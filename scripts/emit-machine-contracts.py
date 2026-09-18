#!/usr/bin/env python3
"""Emit/verify the machine contract bundle; never regenerate Holes.

Manifest pins contract bytes separately (no circular self-digest). Git revisions
pin ownership; SHA-256 pins exact bytes. Run from the canonical mathlib checkout.

emit builds MachineContracts through the futon3c Test Registry and pins the build
warrant in the manifest (--author <agent>; --no-warrant records none). verify
checks that warrant without rebuilding. Needs sibling ../futon3c and Agency :7070.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'DarkTower.WarMachine.'
# 'Action'/'machineAction' RETIRED 2026-09-18 (claude-12): its transcribed code
# (the flat selection block, policy.clj:672-862) was deleted by Joe's H6b ruling
# (futon2 0d29c706); the surviving action law is carried by ActionMarginal and
# PolicySelection below. See the retirement record in MachineContracts.lean.
NAMES = dict(zip(
    ['Observation', 'BeliefState', 'BeliefUpdate', 'Precision', 'Depth',
     'Temperature', 'PredictionError'],
    ['machineObservation', 'machineBeliefState', 'machineBeliefUpdate',
     'machinePrecision', 'machineDepth', 'machineTemperature',
     'machineChannelPredictionError']))
EXPECTED = {PREFIX + 'Machine' + k: [PREFIX + 'Machine' + k + '.' + v]
            for k, v in NAMES.items()}
# Aligned modules (ALIGNMENT.md): runtime-correspondence entries, possibly several per module.
EXPECTED[PREFIX + 'TokenState'] = [PREFIX + 'TokenState.' + n
                                   for n in ['observedBelief', 'independentBelief', 'coverage']]
EXPECTED[PREFIX + 'CascadeTransition'] = [PREFIX + 'CascadeTransition.' + n
                                          for n in ['patternKernel', 'firstEnabled', 'cascadeKernel', 'interpret',
                                                    'guard', 'firstEnabled', 'cascadeKernel', 'cascadeKernel']]
EXPECTED[PREFIX + 'PolicyRollout'] = [PREFIX + 'PolicyRollout.rolloutState',
                                      PREFIX + 'PolicyRollout.predictedOutcome']
EXPECTED[PREFIX + 'TokenObservation'] = [PREFIX + 'TokenObservation.tokenLikelihood',
                                         PREFIX + 'TokenObservation.observationKernelOK']
EXPECTED[PREFIX + 'TokenPreference'] = [PREFIX + 'TokenPreference.PreferenceSpec',
                                        PREFIX + 'TokenPreference.PreferenceSpec.utility',
                                        PREFIX + 'TokenPreference.PreferenceSpec.preference',
                                        PREFIX + 'TokenPreference.PreferenceSpec.preference',
                                        PREFIX + 'TokenPreference.PreferenceSpec.preference']
EXPECTED[PREFIX + 'PolicyHorizon'] = [PREFIX + 'PolicyHorizon.' + n
                                      for n in ['stepRisk', 'stepAmbiguity', 'horizonEFE', 'horizonEFE', 'horizonEFE']]
EXPECTED[PREFIX + 'ExactBeliefTrajectory'] = [PREFIX + 'ExactBeliefTrajectory.exactUpdate',
                                              PREFIX + 'ExactBeliefTrajectory.tokenBeliefAt']
EXPECTED[PREFIX + 'PolicySelection'] = [PREFIX + 'PolicySelection.selectionPosterior']
EXPECTED[PREFIX + 'ActionMarginal'] = [PREFIX + 'ActionMarginal.IsBayesAction']
HOLDERS = {'model-transcription-only', 'runtime-correspondence-not-live-path',
           'runtime-correspondence-live-shadow', 'runtime-correspondence-live-enactment',
           'runtime-correspondence-lagging'}
# 'runtime-correspondence-live-selection' is reserved for P11 step 3 and is refused
# until Joe's word adds it here.
# Modules whose policy carrier is non-conformant (MachinePolicySet.nonConformantAgainst):
# they may be transcribed, never certified as runtime correspondence.
NON_CONFORMANT_MODULES = {'DarkTower.WarMachine.MachinePolicySet'}
LIVE_HOLDERS = {'runtime-correspondence-live-shadow', 'runtime-correspondence-live-enactment'}
LIVE_SITE_RE = __import__('re').compile(r'live-call-site=(\S+):(\d+)')
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
    PREFIX + 'CascadeTransition.firstEnabled': [
        {'clojure-locus': ('defn', 'first-enabled'),
         'fixture': ('deftest', 'cascade-transition-lean-theorem-properties'),
         'evidence': ('theorem', 'firstEnabled_skips_forbidden')},
        {'clojure-locus': ('defn', 'first-enabled'),
         'fixture': ('deftest', 'cascade-transition-p10-same-precedence-chain'),
         'evidence': ('theorem', 'fixture_same_precedence_chain')}],
    PREFIX + 'CascadeTransition.cascadeKernel': [
        {'clojure-locus': ('defn', 'cascade-kernel'),
         'fixture': ('deftest', 'cascade-transition-lean-theorem-properties'),
         'evidence': ('theorem', 'cascadeKernel_rowsum')},
        {'clojure-locus': ('defn', 'cascade-kernel'),
         'fixture': ('deftest', 'cascade-transition-p10-five-situations'),
         'evidence': ('theorem', 'fixture_situation_v_renewal')},
        {'clojure-locus': ('defn', 'acting-order'),
         'fixture': ('deftest', 'acting-order-rechecks-guards-and-completes-by-achievement'),
         'evidence': ('theorem', 'fixture_situation_v_renewal')}],
    PREFIX + 'PolicySelection.selectionPosterior': {
        'clojure-locus': ('defn', 'selection-posterior'),
        'fixture': ('deftest', 'selection-posterior-lean-correspondence'),
        'evidence': ('theorem', 'selectionPosterior_finite')},
    PREFIX + 'ActionMarginal.IsBayesAction': {
        'clojure-locus': ('defn', 'bayes-choice'),
        'fixture': ('deftest', 'bayes-choice-aggregates'),
        'evidence': ('theorem', 'fixture_bayes_a')},
    PREFIX + 'CascadeTransition.guard': {
        'clojure-locus': ('defn', 'guard-holds?'),
        'fixture': ('deftest', 'cascade-transition-p10-achieved-first-is-skipped'),
        'evidence': ('theorem', 'firstEnabled_skips_achieved')},
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
    PREFIX + 'TokenPreference.PreferenceSpec.preference': [
        {'clojure-locus': ('defn', 'preference-distribution'),
         'fixture': ('deftest', 'token-preference-lean-theorem-properties'),
         'evidence': ('theorem', 'preference_sum')},
        {'clojure-locus': ('defn', 'preference-fn'),
         'fixture': ('deftest', 'preference-fn-equals-distribution'),
         'evidence': ('theorem', 'preference_sum')},
        {'clojure-locus': ('defn', 'log-preference-fn'),
         'fixture': ('deftest', 'log-preference-fn-scales-and-zeroed-check-safe'),
         'evidence': ('theorem', 'preference_eq_zero_iff')}],
    PREFIX + 'PolicyHorizon.stepRisk': {
        'clojure-locus': ('defn', 'outcome-risk'),
        'fixture': ('deftest', 'outcome-risk-properties'),
        'evidence': ('theorem', 'stepRisk_nonneg')},
    PREFIX + 'PolicyHorizon.stepAmbiguity': {
        'clojure-locus': ('defn', 'step-ambiguity'),
        'fixture': ('deftest', 'horizon-g-lean-fixture-correspondence'),
        'evidence': ('theorem', 'stepAmbiguity_nonneg')},
    PREFIX + 'PolicyHorizon.horizonEFE': [
        {'clojure-locus': ('defn', 'horizon-g'),
         'fixture': ('deftest', 'horizon-g-infinite-risk'),
         'evidence': ('theorem', 'horizonEFE_eq_top_iff')},
        {'clojure-locus': ('defn', 'horizon-g-sparse'),
         'fixture': ('deftest', 'sparse-g-equals-enumerating-g'),
         'evidence': ('theorem', 'horizonEFE_eq_top_iff')},
        {'clojure-locus': ('defn', 'shadow-cascade-g'),
         'fixture': ('deftest', 'shadow-g-computed-on-fixture'),
         'evidence': ('theorem', 'horizonEFE_eq_top_iff')}],
    PREFIX + 'ExactBeliefTrajectory.exactUpdate': {
        'clojure-locus': ('defn', 'exact-update'),
        'fixture': ('deftest', 'exact-belief-lean-fixture-correspondence'),
        'evidence': ('theorem', 'exactUpdate_vfe_le')},
    PREFIX + 'ExactBeliefTrajectory.tokenBeliefAt': {
        'clojure-locus': ('defn', 'token-belief-at'),
        'fixture': ('deftest', 'exact-belief-properties'),
        'evidence': ('theorem', 'tokenBeliefAt_dist')},
}


def committed_lines(path):
    """Lines of a cross-repo pointer target at its repository's HEAD, not the working tree.

    Contract pointers name committed code: an owner's uncommitted edit elsewhere in the
    same file must neither break nor satisfy verification. `path` is `<repo>/<rest>`
    relative to the parent of this checkout (e.g. futon2/src/...)."""
    repo, rest = path.split('/', 1)
    target = ROOT.parent / path
    require(target.resolve().is_relative_to(ROOT.parent), 'foreign pointer: ' + path)
    out = subprocess.run(['git', '-C', str(ROOT.parent / repo), 'show', 'HEAD:' + rest],
                         capture_output=True)
    require(out.returncode == 0, 'pointer not committed at HEAD: ' + path)
    return out.stdout.decode().splitlines()


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
# Build warrant: the MachineContracts build registered in the futon3c Test
# Registry (futon3c.test-registry), pinned in the manifest. It is evidence that
# this exact source closure built clean and sorry-free under a pinned toolchain;
# it never licenses skipping a build. Manifests without one (or emitted with
# --no-warrant) verify as before and say so.
BUILD_MODULE = PREFIX + 'MachineContracts'
BUILD_COMMAND = ['lake', 'build', BUILD_MODULE]
REGISTRY_ROOT = ROOT.parent / 'futon3c'
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


def edn_str(s):
    return '"' + s.replace('\\', '\\\\').replace('"', '\\"') + '"'


def registry(operation, fields):
    """Run a futon3c.test-registry operation; return its JSON result. FIELDS
    maps EDN keyword names to strings, lists of strings, or pre-rendered EDN."""
    def render(v):
        if isinstance(v, list):
            return '[' + ' '.join(edn_str(x) for x in v) + ']'
        return edn_str(v) if isinstance(v, str) else v.edn
    with tempfile.NamedTemporaryFile('w', suffix='.edn', prefix='wm-warrant-') as cfg:
        cfg.write('{' + ' '.join(':%s %s' % (k, render(v)) for k, v in fields.items()) + ' :output :json}')
        cfg.flush()
        out = subprocess.run(['clojure', '-M', '-m', 'futon3c.test-registry', operation, cfg.name],
                             cwd=REGISTRY_ROOT, capture_output=True, text=True)
    lines = out.stdout.strip().splitlines()
    require(bool(lines), 'test registry produced no result: ' + out.stderr[-400:])
    return strict_json(lines[-1].encode())


def register_build_warrant(author, source_paths, artifact_dir):
    """Build MachineContracts THROUGH the registry (this is the emission build)."""
    row = registry('run', {'agency-url': 'http://localhost:7070', 'repo-root': str(ROOT),
                           'command': BUILD_COMMAND, 'author': author,
                           'code-paths': sorted(p for p in source_paths if p.endswith('.lean')),
                           'test-paths': ['scripts/emit_machine_contracts.lean'],
                           'artifact-dir': str(artifact_dir)})
    require(row.get('evidence/id', '').startswith('test-registry-') and row['payload']['warrant?'] is True,
            'build warrant refused: %s' % json.dumps(row.get('payload', row).get('results', row))[:600])
    return {'entry-id': row['evidence/id'], 'command': BUILD_COMMAND,
            'registry': 'futon3c.test-registry'}


def check_build_warrant(w, sources):
    """Registry check (no rebuild), then bind the warrant to THIS manifest: same
    command, clean results, and every pinned Lean source in its import closure at
    the pinned bytes."""
    require(set(w) == {'entry-id', 'command', 'registry'} and w['command'] == BUILD_COMMAND and
            w['registry'] == 'futon3c.test-registry', 'malformed build warrant')
    check = registry('check', {'agency-url': 'http://localhost:7070', 'entry-id': w['entry-id'],
                               'repo-root': str(ROOT), 'changed-paths': []})
    require(check.get('warrant?') is True,
            'build warrant does not check: %s %s' % (check.get('reason'), json.dumps(check.get('details'))[:600]))
    record = check['record']
    require(record['command'] == BUILD_COMMAND, 'build warrant is for another command')
    r = record['results']
    # Sorries are allowed only in the frozen Holes component, whose declared
    # holes MachineContracts imports; any other sorry in the closure refuses.
    require(r['exit'] == 0 and r['error-count'] == 0, 'build warrant results not clean')
    stray = sorted(set(r['sorry-files']) - {'DarkTower/WarMachine/Holes.lean'})
    require(not stray, 'build warrant closure has sorries outside Holes: ' + ', '.join(stray))
    closure = {e['path']: e['sha256'] for e in record['load-closure']}
    for path, p in sources.items():
        if path.endswith('.lean') and path != 'scripts/emit_machine_contracts.lean':
            require(closure.get(path) == p['sha256'], 'build warrant does not cover pinned source: ' + path)
    return w['entry-id']


VERIFIED_WARRANT = {}


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
    warrant = m.get('build-warrant')
    if warrant is None or warrant.get('status') == 'none':
        warrant_note = 'no build warrant (%s)' % ('predates build warrants' if warrant is None else warrant['reason'])
    else:
        warrant_note = 'build warrant ' + check_build_warrant(warrant, sources)
    VERIFIED_WARRANT[manifest_path.resolve()] = warrant_note
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
                lines = committed_lines(path)
                require(1 <= int(line) <= len(lines), 'bad pointer ' + key)
                if runtime:
                    options = RUNTIME_FORMS[d['name']]
                    options = options if isinstance(options, list) else [options]
                    require(any(form_at(lines[int(line) - 1]) == o[key] for o in options),
                            'pointer does not name an expected form: %s %s -> %r'
                            % (d['name'], key, lines[int(line) - 1].strip()))
            if d['holder'] != 'model-transcription-only':
                require(not any(d['name'].startswith(m + '.') for m in NON_CONFORMANT_MODULES),
                        'runtime correspondence refused for a non-conformant policy grain: ' + d['name'])
            if d['holder'] == 'runtime-correspondence-lagging':
                require(d['falsifier'].startswith('LAGGING'),
                        'lagging entry must name the lag first in its falsifier: ' + d['name'])
            if d['holder'] in LIVE_HOLDERS:
                # A live claim must name the live call site (in the owner string as
                # live-call-site=path:line) and that line must call the runtime function.
                m = LIVE_SITE_RE.search(d['owner'])
                require(m is not None, 'live entry without live-call-site: ' + d['name'])
                site_lines = committed_lines(m.group(1))
                require(1 <= int(m.group(2)) <= len(site_lines), 'bad live-call-site line: ' + d['name'])
                path, line = d['clojure-locus'].rsplit(':', 1)
                fn = form_at(committed_lines(path)[int(line) - 1])[1]
                call = site_lines[int(m.group(2)) - 1]
                require(__import__('re').search(r'(^|[\s(/])' + __import__('re').escape(fn) + r'([\s)]|$)', call)
                        is not None,
                        'live-call-site does not call %s: %r' % (fn, call.strip()))
            if runtime:
                options = RUNTIME_FORMS[d['name']]
                options = options if isinstance(options, list) else [options]
                def at(key):
                    path, line = d[key].rsplit(':', 1)
                    return form_at(committed_lines(path)[int(line) - 1])
                require(any(all(at(k) == o[k] for k in o) for o in options),
                        'pointers do not form one declared (locus, fixture, evidence) triple: ' + d['name'])
    return m


def emit(destination, author=None, warrant=True):
    paths = [EMITTER, 'scripts/emit-machine-contracts.py', 'scripts/emit_machine_contracts.lean', 'DarkTower/Contract/Emit.lean',
             'lean-toolchain', 'DarkTower/WarMachine/Holes.lean',
             *[m.replace('.', '/') + '.lean' for m in sorted(EXPECTED)]]
    pins = [pin(p) for p in paths]
    holes_bytes = local(HOLES).read_bytes()
    if warrant:
        require(bool(author), 'a build warrant needs --author (or pass --no-warrant)')
        build_warrant = register_build_warrant(author, paths, destination.resolve() / 'build-warrant')
    else:
        run(*BUILD_COMMAND)
        build_warrant = {'status': 'none', 'reason': 'emitted with --no-warrant'}
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
                'bundle': {'file': 'machine-contracts.json', 'sha256': digest(raw)},
                'build-warrant': build_warrant}
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
    emit_parser = sub.add_parser('emit')
    emit_parser.add_argument('directory', type=Path)
    emit_parser.add_argument('--author', help='agent id registering the build warrant')
    emit_parser.add_argument('--no-warrant', action='store_true',
                             help='build without the test registry; the manifest records no warrant')
    sub.add_parser('verify').add_argument('manifest', type=Path)
    args = parser.parse_args()
    try:
        if args.command == 'emit':
            emit(args.directory, author=args.author, warrant=not args.no_warrant)
            manifest = args.directory / 'manifest.json'
        else:
            verify(args.manifest)
            manifest = args.manifest
        print('PASS: %d machine contracts plus unchanged Holes; source and contract pins verified; %s'
              % (len(EXPECTED), VERIFIED_WARRANT[manifest.resolve()]))
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as exc:
        parser.exit(1, 'REFUSED: ' + str(exc) + '\n')
