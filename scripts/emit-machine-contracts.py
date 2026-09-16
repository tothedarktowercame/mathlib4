#!/usr/bin/env python3
"""Emit/verify the machine contract bundle; never regenerate Holes.

Manifest pins contract bytes separately (no circular self-digest). Git revisions
pin ownership; SHA-256 pins exact bytes. Run from the canonical mathlib checkout.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'DarkTower.WarMachine.'
NAMES = dict(zip(
    ['Observation', 'BeliefState', 'BeliefUpdate', 'Precision', 'Depth',
     'Temperature', 'Action', 'PredictionError'],
    ['machineObservation', 'machineBeliefState', 'machineBeliefUpdate',
     'machinePrecision', 'machineDepth', 'machineTemperature', 'machineAction',
     'machineChannelPredictionError']))
EXPECTED = {PREFIX + 'Machine' + k: [PREFIX + 'Machine' + k + '.' + v]
            for k, v in NAMES.items()}
# Aligned modules (ALIGNMENT.md): runtime-correspondence entries, possibly several per module.
EXPECTED[PREFIX + 'TokenState'] = [PREFIX + 'TokenState.' + n
                                   for n in ['observedBelief', 'independentBelief', 'coverage']]
EXPECTED[PREFIX + 'CascadeTransition'] = [PREFIX + 'CascadeTransition.' + n
                                          for n in ['patternKernel', 'firstEnabled', 'cascadeKernel', 'interpret']]
EXPECTED[PREFIX + 'PolicyRollout'] = [PREFIX + 'PolicyRollout.rolloutState',
                                      PREFIX + 'PolicyRollout.predictedOutcome']
EXPECTED[PREFIX + 'TokenObservation'] = [PREFIX + 'TokenObservation.tokenLikelihood',
                                         PREFIX + 'TokenObservation.observationKernelOK']
EXPECTED[PREFIX + 'TokenPreference'] = [PREFIX + 'TokenPreference.PreferenceSpec',
                                        PREFIX + 'TokenPreference.PreferenceSpec.utility',
                                        PREFIX + 'TokenPreference.PreferenceSpec.preference']
EXPECTED[PREFIX + 'PolicyHorizon'] = [PREFIX + 'PolicyHorizon.' + n
                                      for n in ['stepRisk', 'stepAmbiguity', 'horizonEFE']]
HOLDERS = {'model-transcription-only', 'runtime-correspondence-not-live-path'}
# Runtime-correspondence entries must point at the named forms, not merely at an
# existing line: pointer -> (form head, name) expected at that line. A locus that
# drifts onto another defn/deftest/theorem refuses (ALIGNMENT.md item 5).
RUNTIME_FORMS = {
    PREFIX + 'TokenState.observedBelief': {
        'clojure-locus': ('defn', 'observed-belief'),
        'fixture': ('deftest', 'token-state-lean-fixture-correspondence'),
        'evidence': ('theorem', 'observedBelief_sum')},
    PREFIX + 'TokenState.independentBelief': {
        'clojure-locus': ('defn', 'independent-belief'),
        'fixture': ('deftest', 'token-state-lean-theorem-properties'),
        'evidence': ('theorem', 'independentBelief_sum')},
    PREFIX + 'TokenState.coverage': {
        'clojure-locus': ('defn', 'coverage'),
        'fixture': ('deftest', 'token-state-lean-theorem-properties'),
        'evidence': ('theorem', 'coverage_nonneg')},
    PREFIX + 'CascadeTransition.patternKernel': {
        'clojure-locus': ('defn', 'pattern-kernel'),
        'fixture': ('deftest', 'cascade-transition-lean-fixture-correspondence'),
        'evidence': ('theorem', 'patternKernel_of_achieved')},
    PREFIX + 'CascadeTransition.firstEnabled': {
        'clojure-locus': ('defn', 'first-enabled'),
        'fixture': ('deftest', 'cascade-transition-lean-theorem-properties'),
        'evidence': ('theorem', 'firstEnabled_skips_forbidden')},
    PREFIX + 'CascadeTransition.cascadeKernel': {
        'clojure-locus': ('defn', 'cascade-kernel'),
        'fixture': ('deftest', 'cascade-transition-lean-theorem-properties'),
        'evidence': ('theorem', 'cascadeKernel_rowsum')},
    PREFIX + 'CascadeTransition.interpret': {
        'clojure-locus': ('defn', 'missing-interpretation'),
        'fixture': ('deftest', 'cascade-transition-lean-falsifiers'),
        'evidence': ('theorem', 'interpret_eq_none_iff')},
    PREFIX + 'PolicyRollout.rolloutState': {
        'clojure-locus': ('defn', 'rollout'),
        'fixture': ('deftest', 'cascade-transition-lean-fixture-correspondence'),
        'evidence': ('theorem', 'fixture_rollout_two')},
    PREFIX + 'PolicyRollout.predictedOutcome': {
        'clojure-locus': ('defn', 'predict-observations'),
        'fixture': ('deftest', 'token-observation-lean-theorem-properties'),
        'evidence': ('theorem', 'predictedOutcome_eq_rolloutState')},
    PREFIX + 'TokenObservation.tokenLikelihood': {
        'clojure-locus': ('defn', 'token-likelihood'),
        'fixture': ('deftest', 'token-observation-lean-fixture-correspondence'),
        'evidence': ('theorem', 'tokenLikelihood_checkable')},
    PREFIX + 'TokenObservation.observationKernelOK': {
        'clojure-locus': ('defn', 'observation-distribution'),
        'fixture': ('deftest', 'token-observation-lean-theorem-properties'),
        'evidence': ('theorem', 'tokenLikelihood_colsum')},
    PREFIX + 'TokenPreference.PreferenceSpec': {
        'clojure-locus': ('defn', 'preference-spec'),
        'fixture': ('deftest', 'token-preference-lean-falsifiers'),
        'evidence': ('theorem', 'Z_pos')},
    PREFIX + 'TokenPreference.PreferenceSpec.utility': {
        'clojure-locus': ('defn', 'token-utility'),
        'fixture': ('deftest', 'token-preference-lean-fixture-correspondence'),
        'evidence': ('theorem', 'preference_lt_of_want_lt')},
    PREFIX + 'TokenPreference.PreferenceSpec.preference': {
        'clojure-locus': ('defn', 'preference-distribution'),
        'fixture': ('deftest', 'token-preference-lean-theorem-properties'),
        'evidence': ('theorem', 'preference_sum')},
    PREFIX + 'PolicyHorizon.stepRisk': {
        'clojure-locus': ('defn', 'outcome-risk'),
        'fixture': ('deftest', 'outcome-risk-properties'),
        'evidence': ('theorem', 'stepRisk_nonneg')},
    PREFIX + 'PolicyHorizon.stepAmbiguity': {
        'clojure-locus': ('defn', 'step-ambiguity'),
        'fixture': ('deftest', 'horizon-g-lean-fixture-correspondence'),
        'evidence': ('theorem', 'stepAmbiguity_nonneg')},
    PREFIX + 'PolicyHorizon.horizonEFE': {
        'clojure-locus': ('defn', 'horizon-g'),
        'fixture': ('deftest', 'horizon-g-infinite-risk'),
        'evidence': ('theorem', 'horizonEFE_eq_top_iff')},
}


def form_at(line):
    """(head, name) of a Clojure `(defn name` / `(deftest name` or Lean `theorem name` line."""
    t = line.strip()
    if t.startswith('('):
        parts = t[1:].split()
        head = parts[0] if parts else ''
        if head == 'defn-':
            head = 'defn'
        return head, (parts[1] if len(parts) > 1 else '')
    parts = t.split()
    return (parts[0] if parts else ''), (parts[1] if len(parts) > 1 else '')
SCOPE = 'per-entry-holder'
SCHEMA = 'wm-machine-contract-manifest-v2'
EMITTER = 'DarkTower/WarMachine/MachineContracts.lean'
HOLES = 'DarkTower/WarMachine/holes-contract.json'
TEN = {'name', 'kind', 'signature', 'owner', 'holder', 'decided',
       'clojure-locus', 'fixture', 'evidence', 'falsifier'}


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def run(*args):
    return subprocess.check_output(args, cwd=ROOT)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def strict_json(data):
    def pairs(items):
        d = {}
        for k, v in items:
            require(k not in d, 'duplicate JSON key: ' + k)
            d[k] = v
        return d
    return json.loads(data, object_pairs_hook=pairs)


def local(path):
    p = ROOT / path
    require(not Path(path).is_absolute() and '..' not in Path(path).parts,
            'foreign source path')
    require(p.resolve().is_relative_to(ROOT) and p.is_file(), 'missing/foreign source')
    return p


def pin(path):
    data = local(path).read_bytes()
    commit = run('git', 'log', '-1', '--format=%H', '--', path).decode().strip()
    require(bool(commit), 'uncommitted source: ' + path)
    require(data == run('git', 'show', commit + ':' + path), 'dirty source: ' + path)
    require(data == run('git', 'show', 'HEAD:' + path), 'stale ownership: ' + path)
    return {'path': path, 'commit': commit, 'sha256': digest(data)}


def check_pin(p):
    require(set(p) == {'path', 'commit', 'sha256'}, 'malformed source pin')
    require(pin(p['path']) == p, 'stale source pin: ' + p['path'])


def encode(value):
    return (json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True) + '\n').encode()


def verify(manifest_path):
    m = strict_json(manifest_path.read_bytes())
    require(m['schema'] == SCHEMA, 'manifest schema')
    require(m['expected-modules'] == sorted([PREFIX + 'Holes', *EXPECTED]), 'population')
    require(m['scope'] == SCOPE, 'scope')
    expected_paths = {EMITTER, 'scripts/emit-machine-contracts.py',
                      'scripts/emit_machine_contracts.lean', 'DarkTower/Contract/Emit.lean', 'lean-toolchain',
                      *[k.replace('.', '/') + '.lean' for k in EXPECTED],
                      'DarkTower/WarMachine/Holes.lean'}
    require(len(m['sources']) == len(expected_paths) and
            {p['path'] for p in m['sources']} == expected_paths, 'source population')
    for p in m['sources']:
        check_pin(p)
    sources = {p['path']: p for p in m['sources']}
    h = m['holes-component']
    require(h['path'] == HOLES, 'Holes component path')
    require(digest(local(HOLES).read_bytes()) == h['sha256'], 'Holes bytes changed')
    require(local(HOLES).read_bytes() == run('git', 'show', 'HEAD:' + HOLES), 'dirty Holes contract')
    hc = strict_json(local(HOLES).read_bytes())
    require(hc['source']['module'] == PREFIX + 'Holes' and
            hc['source']['git-sha'] == sources['DarkTower/WarMachine/Holes.lean']['commit'],
            'stale Holes ownership')
    b = m['bundle']
    require(b['file'] == 'machine-contracts.json', 'bundle filename')
    raw = (manifest_path.parent / b['file']).read_bytes()
    require(digest(raw) == b['sha256'], 'contract byte mismatch')
    bundle = strict_json(raw)
    require(bundle['schema'] == 'wm-machine-contract-bundle-v1' and
            bundle['scope'] == m['scope'], 'bundle schema/scope')
    contracts = bundle['contracts']
    require(len(contracts) == len(EXPECTED) and
            {c['source']['module'] for c in contracts} == set(EXPECTED), 'module population')
    require(len({c['contract-id'] for c in contracts}) == len(EXPECTED), 'duplicate contract id')
    for c in contracts:
        mod = c['source']['module']
        p = sources[mod.replace('.', '/') + '.lean']
        require(c['schema-version'] == 1 and c['source'] ==
                {'module': mod, 'git-sha': p['commit'], 'sha256': p['sha256']}, 'module ownership')
        require([d['name'] for d in c['declarations']] == EXPECTED[mod], 'declaration population')
        for d in c['declarations']:
            require(set(d) == TEN | {'source'}, 'declaration fields')
            require(all(isinstance(d[k], str) and d[k].strip() for k in TEN), 'missing entry metadata')
            require(d['source'] == c['source'], 'entry identity')
            require(d['signature'] == 'checked-reference:' + d['name'], 'checked reference')
            require(d['kind'] == 'closed' and d['holder'] in HOLDERS, 'disposition')
            runtime = d['holder'] != 'model-transcription-only'
            require(not runtime or d['name'] in RUNTIME_FORMS, 'runtime entry without named forms: ' + d['name'])
            for key in ['fixture', 'evidence', 'clojure-locus']:
                path, line = d[key].rsplit(':', 1)
                target = ROOT.parent / path
                require(target.resolve().is_relative_to(ROOT.parent) and target.is_file(), 'unresolved ' + key)
                lines = target.read_text().splitlines()
                require(1 <= int(line) <= len(lines), 'bad pointer ' + key)
                if runtime:
                    require(form_at(lines[int(line) - 1]) == RUNTIME_FORMS[d['name']][key],
                            'pointer does not name the expected form: %s %s -> %r'
                            % (d['name'], key, lines[int(line) - 1].strip()))
    return m


def emit(destination):
    paths = [EMITTER, 'scripts/emit-machine-contracts.py', 'scripts/emit_machine_contracts.lean', 'DarkTower/Contract/Emit.lean',
             'lean-toolchain', 'DarkTower/WarMachine/Holes.lean',
             *[m.replace('.', '/') + '.lean' for m in sorted(EXPECTED)]]
    pins = [pin(p) for p in paths]
    holes_bytes = local(HOLES).read_bytes()
    run('lake', 'build', 'DarkTower.WarMachine.MachineContracts')
    bundle = strict_json(run('lake', 'env', 'lean', 'scripts/emit_machine_contracts.lean'))
    by_path = {p['path']: p for p in pins}
    for c in bundle['contracts']:
        p = by_path[c['source']['module'].replace('.', '/') + '.lean']
        require(c['source']['git-sha'] == p['commit'], 'emitter source mismatch')
        c['source']['sha256'] = p['sha256']
        for d in c['declarations']:
            d['source'] = dict(c['source'])
    raw = encode(bundle)
    manifest = {'schema': SCHEMA, 'scope': SCOPE,
                'expected-modules': sorted([PREFIX + 'Holes', *EXPECTED]),
                'sources': pins, 'holes-component': {'path': HOLES, 'sha256': digest(holes_bytes)},
                'bundle': {'file': 'machine-contracts.json', 'sha256': digest(raw)}}
    with tempfile.TemporaryDirectory(prefix='wm-contracts-') as tmp:
        stage = Path(tmp)
        (stage / 'machine-contracts.json').write_bytes(raw)
        (stage / 'manifest.json').write_bytes(encode(manifest))
        verify(stage / 'manifest.json')  # includes fresh post-build source verification
        require(local(HOLES).read_bytes() == holes_bytes, 'Holes changed during emission')
        destination.mkdir(parents=True, exist_ok=True)
        for name in ['machine-contracts.json', 'manifest.json']:
            target = destination / name
            data = (stage / name).read_bytes()
            if target.exists():
                require(target.read_bytes() == data, 'refusing artifact overwrite: ' + str(target))
            else:
                with target.open('xb') as stream:
                    stream.write(data)
    verify(destination / 'manifest.json')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    sub.add_parser('emit').add_argument('directory', type=Path)
    sub.add_parser('verify').add_argument('manifest', type=Path)
    args = parser.parse_args()
    try:
        if args.command == 'emit':
            emit(args.directory)
        else:
            verify(args.manifest)
        print('PASS: %d machine contracts plus unchanged Holes; source and contract pins verified'
              % len(EXPECTED))
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as exc:
        parser.exit(1, 'REFUSED: ' + str(exc) + '\n')
