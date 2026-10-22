import GAC.DetailedBalance

/-!
# Corollary 3.15: a compact set containing every trajectory from one initial state

This is a containing set for solutions from `x0`. No claim is made that the
coordinate box is forward invariant for every initial state in that box.
-/

open GAC.Persistence

noncomputable section

namespace GAC

variable {d : ℕ}

/-- The closed coordinate box intersected with the stoichiometric class. -/
def classContainer (N : ReactionNetwork d) (x0 : Fin d → ℝ) (ε : ℝ) :
    Set (Fin d → ℝ) :=
  (Set.univ.pi fun _ => Set.Icc ε ε⁻¹) ∩ {z | z - x0 ∈ stoichSubspace N}

/-- Corollary 3.15. The same compact set and speed bound work for every solution
with the specified positive initial state. The bounds may depend on `x0`. -/
theorem exists_compact_class_container
    (N : ReactionNetwork d) (κ : Reaction N → ℝ) (hd : 0 < d)
    (hκ : ∀ e, 0 < κ e) {xs : Fin d → ℝ} (hdb : IsDetailedBalanced N κ xs)
    (x0 : Fin d → ℝ) (hx0 : PositiveState x0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      IsCompact (classContainer N x0 ε) ∧
      (∀ z ∈ classContainer N x0 ε, PositiveState z) ∧
      (∃ x, IsGlobalForwardSolution N κ x0 x) ∧
      (∀ x, IsGlobalForwardSolution N κ x0 x →
        ∀ t : ℝ, 0 ≤ t → x t ∈ classContainer N x0 ε) ∧
      ∃ B : ℝ, 0 < B ∧ ∀ z ∈ classContainer N x0 ε, ‖massAction N κ z‖ ≤ B := by
  obtain ⟨ε, hε, hεone, hex, hbd⟩ := bounded_persistent_of_weaklyReversible d N κ hd
    (weaklyReversible_of_reversible hdb.reversible) hκ x0 hx0
  have hK : IsCompact (classContainer N x0 ε) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      (((stoichSubspace N).closed_of_finiteDimensional).preimage
        (continuous_id.sub continuous_const))
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (continuous_massAction N κ).continuousOn
  refine ⟨ε, hε, hεone, hK, ?_, hex, ?_, |M| + 1, by positivity, ?_⟩
  · intro z hz i
    exact hε.trans_le (hz.1 i (Set.mem_univ i)).1
  · intro x hx t ht
    exact ⟨fun i _ => hbd x hx t ht i, sol_mem_class hx ht⟩
  · intro z hz
    exact (hM z hz).trans (by linarith [le_abs_self M])

end GAC
