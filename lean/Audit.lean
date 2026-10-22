import GAC

/-! Run with `lake env lean Audit.lean` after `lake build GAC`.
This file is intentionally outside the GAC root to avoid a cyclic import. -/

#check GAC.Paper.DBCondition
#check GAC.Paper.wr_trajectory_compact_interior
#check GAC.Paper.uniform_affine_approximation
#check GAC.exists_compact_class_container
#check GAC.Paper.entropyRate_eq_zero_iff
#check GAC.Paper.db_unique_equilibrium_attracts
#check GAC.PaperExample.convergence
#check GAC.PaperExample.tends_to_equilibrium
#check GAC.PaperExample.tends_to_equilibrium_of_total_eq_three
#check GAC.PaperExample.figure_initial_states_converge
#check GAC.PaperExample.total_conserved

#print axioms GAC.Persistence.bounded_persistent_of_weaklyReversible
#print axioms GAC.Paper.uniform_affine_approximation
#print axioms GAC.Paper.wr_trajectory_compact_interior
#print axioms GAC.exists_compact_class_container
#print axioms GAC.Paper.entropyRate_eq_zero_iff
#print axioms GAC.detailed_balanced_global_convergence
#print axioms GAC.Paper.db_unique_equilibrium_attracts
#print axioms GAC.Example.convergence
#print axioms GAC.PaperExample.net_detailed_balanced
#print axioms GAC.PaperExample.convergence
#print axioms GAC.PaperExample.tends_to_equilibrium
#print axioms GAC.PaperExample.tends_to_equilibrium_of_total_eq_three
#print axioms GAC.PaperExample.figure_initial_states_converge
#print axioms GAC.PaperExample.total_conserved
