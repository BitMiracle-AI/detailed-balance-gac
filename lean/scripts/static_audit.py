#!/usr/bin/env python3
"""Check source completeness and placeholders; this does not replace Lean."""
from pathlib import Path
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[1]


def code_only(text):
    """Strip nested block comments, line comments, and string literals."""
    out = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1
                i += 2
            elif text.startswith('-/', i):
                depth -= 1
                i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' ')
                i += 1
        elif text.startswith('/-', i):
            depth = 1
            out.append(' ')
            i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            out.append(' ')
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    out.append('\n' if text[i] == '\n' else ' ')
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unterminated block comment')
    return ''.join(out)


files = sorted([ROOT / 'GAC.lean', ROOT / 'Audit.lean',
                *ROOT.glob('GAC/**/*.lean')])
issues = []
for path in files:
    code = code_only(path.read_text())
    for match in re.finditer(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code):
        line = code.count('\n', 0, match.start()) + 1
        issues.append(f'{path.relative_to(ROOT)}:{line}: {match.group()}')
    for module in re.findall(r'^import\s+([\w.]+)', code, re.M):
        if module.startswith('GAC.') or module == 'GAC':
            target = ROOT / (module.replace('.', '/') + '.lean')
            if not target.is_file():
                issues.append(f'{path.relative_to(ROOT)}: missing import {module}')

# Every derived persistence module must be recorded in the source map and
# keep its modification notice; the Apache-2.0 license must stay alongside.
source_map = json.loads((ROOT / 'docs/source-map.json').read_text())
recorded = {r['path'] for r in source_map['files']}
derived = {str(p.relative_to(ROOT)) for p in ROOT.glob('GAC/Persistence/**/*.lean')}
if recorded != derived:
    issues.append(f'source map mismatch: {sorted(recorded ^ derived)}')
for path in sorted(derived):
    if not (ROOT / path).read_text().startswith('-- Derived from upstream '):
        issues.append(f'{path}: missing modification notice')
if not (ROOT / 'GAC/Persistence/LICENSE').is_file():
    issues.append('GAC/Persistence/LICENSE missing')

if issues:
    print('\n'.join(issues))
    sys.exit(1)
print(f'PASS: {len(files)} Lean source files; local imports resolve; no placeholder or extra-axiom tokens.')
print(f'PASS: {len(derived)} derived persistence modules recorded in docs/source-map.json with notices and license.')
print('Static inspection only. Run the build and Audit.lean for kernel checks.')
