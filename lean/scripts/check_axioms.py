#!/usr/bin/env python3
"""Validate the actual #print axioms output, including every expected theorem."""
from pathlib import Path
import re
import sys

expected = {
    'GAC.Persistence.bounded_persistent_of_weaklyReversible',
    'GAC.Paper.uniform_affine_approximation',
    'GAC.Paper.wr_trajectory_compact_interior',
    'GAC.exists_compact_class_container',
    'GAC.Paper.entropyRate_eq_zero_iff',
    'GAC.detailed_balanced_global_convergence',
    'GAC.Paper.db_unique_equilibrium_attracts',
    'GAC.Example.convergence',
    'GAC.PaperExample.net_detailed_balanced',
    'GAC.PaperExample.convergence',
    'GAC.PaperExample.tends_to_equilibrium',
    'GAC.PaperExample.tends_to_equilibrium_of_total_eq_three',
    'GAC.PaperExample.figure_initial_states_converge',
    'GAC.PaperExample.total_conserved',
}
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
text = Path(sys.argv[1]).read_text()
found = {}
for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
    found[name] = {a.strip() for a in axioms.split(',') if a.strip()}
for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
    found[name] = set()
missing = expected - found.keys()
extra = {n: sorted(found[n] - allowed) for n in expected & found.keys()
         if found[n] - allowed}
if missing or extra:
    print(f'FAIL: missing={sorted(missing)}, unexpected_axioms={extra}')
    sys.exit(1)
print(f'PASS: {len(expected)} declarations; every reported axiom is in {sorted(allowed)}.')
