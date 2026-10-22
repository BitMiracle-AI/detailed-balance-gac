# detailed-balance-gac

Lean 4 formalization accompanying the paper
*Global Convergence of Detailed Balanced Mass Action Systems* (BitMiracle AI Lab, 2026).

Main theorem: for a finite detailed balanced mass-action system with positive rate
constants, each positive stoichiometric compatibility class contains exactly one
positive equilibrium, and every positive trajectory converges to it
(`GAC.Paper.db_unique_equilibrium_attracts`, underlying
`GAC.detailed_balanced_global_convergence`).

## Build and check

Requires [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.34.1) and
Mathlib (`d13f23b723b8a846827a245b89c10fc7d3f11612`) are pinned; do not run `lake update`.

```sh
cd lean
lake exe cache get
lake build GAC
lake env lean Audit.lean > axioms-main.log
lake env lean GAC/Reformulated/Audit.lean
python3 scripts/check_axioms.py axioms-main.log
python3 scripts/static_audit.py
```

The two audit entries check 14 + 21 declarations; all depend only on
`propext`, `Classical.choice` and `Quot.sound`.

## Layout

| Path | Content |
| --- | --- |
| `lean/GAC/Persistence/` | 71 modules: boundedness and persistence of weakly reversible systems (Theorem 3.1), adapted from openai/math |
| `lean/GAC/DetailedBalance.lean`, `CompactClass.lean` | Horn–Jackson argument and global convergence |
| `lean/GAC/Paper.lean` | Paper-facing statements |
| `lean/GAC/Example.lean`, `PaperExample.lean` | `A ⇌ B` and the three-species example of Section 5.1 |
| `lean/GAC/Reformulated/` | Logarithmic bounds, feasible directions, equilibrium parameterization |
| `lean/docs/PAPER_MAPPING.md` | Paper numbering ↔ Lean declarations, with coverage limits |
| `lean/docs/SOURCE_MAP.md` | Upstream provenance of the adapted modules |

Not formalized: the handwritten Lipschitz/Dini route of Lemmas 3.9–3.10 (the same
confinement conclusion is proved through finite-minimum monotonicity), a single
declaration for the three-set identity of Lemma 3.18, Corollary 3.23, the
complex-balanced extension, and the numerical integration of Section 5.1.

## License

Apache License 2.0; see `LICENSE` and `NOTICE`.
