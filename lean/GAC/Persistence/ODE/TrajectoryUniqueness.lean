-- Derived from upstream lean/OAI/Analysis/MassAction/SolutionUniqueness.lean (revision 1581d4c), Apache-2.0.
-- Modified: module path, namespaces and cited declaration names changed; see docs/SOURCE_MAP.md.
import GAC.Persistence.Model.Network
import GAC.Persistence.ODE.Uniqueness

namespace GAC

noncomputable section
namespace Persistence

variable {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
  {z : Fin d → ℝ} {T : ℝ} {x y : ℝ → (Fin d → ℝ)}

/-- Uniqueness for finite forward solutions, including both endpoints. -/
theorem IsForwardSolutionOn.eqOn
    (hv : LocallyLipschitz (massAction N κ)) (hT : 0 ≤ T)
    (hx : IsForwardSolutionOn N κ z T x)
    (hy : IsForwardSolutionOn N κ z T y) :
    Set.EqOn x y (Set.Icc (0 : ℝ) T) :=
  eqOn_Icc_of_locallyLipschitz_ode hv hT hx.2.1 hx.2.2 hy.2.1 hy.2.2
    (hx.1.trans hy.1.symm)

/-- One invariant global trajectory from each initial point suffices for the
full finite-segment and extension definition of forward invariance. -/
theorem isForwardInvariant_of_global_trajectories
    (hv : LocallyLipschitz (massAction N κ)) {K : Set (Fin d → ℝ)}
    (hK : ∀ z ∈ K, ∃ x : ℝ → (Fin d → ℝ),
      IsGlobalForwardSolution N κ z x ∧ ∀ t : ℝ, 0 ≤ t → x t ∈ K) :
    IsForwardInvariant N κ K := by
  intro z hz
  obtain ⟨xg, hxg, hmem⟩ := hK z hz
  refine ⟨⟨xg, hxg⟩, ?_⟩
  intro T x hT hx
  have hg : IsForwardSolutionOn N κ z T xg := by
    refine ⟨hxg.1, ?_, ?_⟩
    · intro t ht
      exact (hxg.2 t ht.1).continuousAt.continuousWithinAt
    · intro t ht
      exact hxg.2 t ht.1.le
  have heq : Set.EqOn xg x (Set.Icc (0 : ℝ) T) := hg.eqOn hv hT hx
  refine ⟨?_, ⟨xg, hxg, heq⟩⟩
  intro t ht
  rw [← heq ht]
  exact hmem t ht.1

end Persistence

end

end GAC
