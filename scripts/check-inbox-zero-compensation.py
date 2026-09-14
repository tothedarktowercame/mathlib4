#!/usr/bin/env python3
"""Check the model and six deliberately false compensating-safety claims; no runtime calls."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MODEL = 'DarkTower/WarMachine/InboxZeroCompensationWitness.lean'
BASE = ROOT / 'DarkTower/WarMachine/inbox-zero-compensation'


def check():
    rows = []
    commands = [('build', ['lake', 'build', 'DarkTower.WarMachine.InboxZeroCompensationWitness'], 0),
                ('model', ['lake', 'env', 'lean', MODEL], 0)]
    # Fixed population: a missing negative must not silently reduce the gate.
    for name in ['MissedEdit', 'SurvivesDeadline', 'DetectionOnlyBound', 'FailedUndo', 'LostEditorChange', 'ZeroCommits']:
        commands.append((name, ['lake', 'env', 'lean', str(BASE / 'negative' / (name + '.lean'))], 1))
    before = hashlib.sha256((ROOT / MODEL).read_bytes()).hexdigest()
    for name, argv, expected in commands:
        p = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=120)
        output = p.stdout + p.stderr
        rows.append({'case': name, 'argv': argv, 'exit': p.returncode,
                     'expected-exit': expected, 'stdout': p.stdout, 'stderr': p.stderr})
        if p.returncode != expected or 'sorryAx' in output:
            raise RuntimeError(json.dumps(rows, indent=2))
        if expected == 0 and ('error:' in output or 'warning:' in output):
            raise RuntimeError(output)
        if expected == 1 and not ('unsolved goals' in output or "Tactic `decide` proved that the proposition" in output):
            raise RuntimeError('Not a logical refusal: ' + output)
    assert before == hashlib.sha256((ROOT / MODEL).read_bytes()).hexdigest()
    return {'scope': 'model-only; runtime-correspondence not-proven',
            'model-sha256': before, 'checks': rows}


if __name__ == '__main__':
    try:
        print(json.dumps(check(), indent=2))
    except (RuntimeError, subprocess.TimeoutExpired) as error:
        sys.exit(str(error))
