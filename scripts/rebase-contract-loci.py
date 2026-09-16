#!/usr/bin/env python3
"""Rebase MachineContracts.lean runtime-entry pointers to the lines where their named
forms (RUNTIME_FORMS in emit-machine-contracts.py) now sit at each repository's HEAD.

Only line numbers change, and only when the named form is found exactly once in the
committed file; ambiguity or absence is reported and left for a person. Prints a diff
summary; writes the file in place."""
import importlib.util, re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('emit', ROOT / 'scripts/emit-machine-contracts.py')
emit = importlib.util.module_from_spec(spec); spec.loader.exec_module(emit)
MC = ROOT / 'DarkTower/WarMachine/MachineContracts.lean'
text = MC.read_text()
lines = text.split('\n')
KEYS = ['clojure-locus', 'fixture', 'evidence']
problems, changes = [], []
i = 0
while i < len(lines):
    m = re.search(r'runtimeEntry ``(\S+) (\w+) ', lines[i])
    if not m:
        i += 1; continue
    name = m.group(1)
    ptr_idx = [i + 2, i + 3, i + 4]
    ptrs = [re.search(r'"([^"]+):(\d+)"', lines[j]) for j in ptr_idx]
    options = emit.RUNTIME_FORMS.get(name)
    if options is None or not all(ptrs):
        problems.append(f'{name}: no named forms or unparsable pointers'); i += 1; continue
    options = options if isinstance(options, list) else [options]
    best = None
    for opt in options:
        new, dist, ok = [], 0, True
        for k, p in zip(KEYS, ptrs):
            path, old = p.group(1), int(p.group(2))
            try:
                src = emit.committed_lines(path)
            except ValueError as e:
                ok = False; break
            hits = [n + 1 for n, l in enumerate(src) if emit.form_at(l) == opt[k]]
            if len(hits) != 1:
                ok = False; break
            new.append(hits[0]); dist += abs(hits[0] - old)
        if ok and (best is None or dist < best[0]):
            best = (dist, new, opt)
    if best is None:
        problems.append(f'{name} at MachineContracts line {i+1}: no option resolves uniquely'); i += 1; continue
    for j, p, n in zip(ptr_idx, ptrs, best[1]):
        if int(p.group(2)) != n:
            changes.append(f'{name}: {p.group(1)} {p.group(2)} -> {n}')
            lines[j] = lines[j].replace(f'{p.group(1)}:{p.group(2)}"', f'{p.group(1)}:{n}"', 1)
    i += 1
MC.write_text('\n'.join(lines))
print('\n'.join(changes) or 'no changes')
if problems:
    print('PROBLEMS:\n' + '\n'.join(problems)); sys.exit(1)
