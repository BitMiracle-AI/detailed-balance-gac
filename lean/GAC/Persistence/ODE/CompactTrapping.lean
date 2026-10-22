-- Derived from upstream lean/OAI/Analysis/MassAction/CompactContinuation.lean (revision 1581d4c), Apache-2.0.
-- Modified: module path, namespaces and cited declaration names changed; see docs/SOURCE_MAP.md.
import GAC.Persistence.Model.Network
import GAC.Persistence.ODE.GlobalExtension
import GAC.Persistence.ODE.TrajectoryUniqueness

namespace GAC

noncomputable section

open Set

namespace Persistence

theorem global_massAction_of_compact_trap
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    (hreg : ContDiff ℝ 1 (massAction N κ))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (htrap : ∀ z ∈ K, ∀ (T : ℝ) (x : ℝ → (Fin d → ℝ)),
      0 ≤ T → IsForwardSolutionOn N κ z T x →
      ∀ t ∈ Icc (0 : ℝ) T, x t ∈ K)
    {z : Fin d → ℝ} (hz : z ∈ K) :
    ∃ g : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ z g ∧
      ∀ t : ℝ, 0 ≤ t → g t ∈ K := by
  obtain ⟨g, hg0, hgd, hgK⟩ := global_solution_of_compact_trap hreg hK
    (fun q hq T hT x hx hd => htrap q hq T x hT
      ⟨hx, fun t ht => (hd t ht).continuousAt.continuousWithinAt,
        fun t ht => hd t (Ioo_subset_Icc_self ht)⟩) hz
  exact ⟨g, ⟨hg0, hgd⟩, hgK⟩

theorem isForwardInvariant_of_compact_trapping
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    (hreg : ContDiff ℝ 1 (massAction N κ))
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (htrap : ∀ z ∈ K, ∀ (T : ℝ) (x : ℝ → (Fin d → ℝ)),
      0 ≤ T → IsForwardSolutionOn N κ z T x →
      ∀ t ∈ Icc (0 : ℝ) T, x t ∈ K) :
    IsForwardInvariant N κ K := by
  apply isForwardInvariant_of_global_trajectories hreg.locallyLipschitz
  intro z hz
  exact global_massAction_of_compact_trap hreg hK htrap hz

/-- No extra regularity hypothesis is necessary for the polynomial mass-action
field: compact trapping of finite solutions implies full forward invariance. -/
theorem massAction_isForwardInvariant_of_compact_trapping
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (htrap : ∀ z ∈ K, ∀ (T : ℝ) (x : ℝ → (Fin d → ℝ)),
      0 ≤ T → IsForwardSolutionOn N κ z T x →
      ∀ t ∈ Icc (0 : ℝ) T, x t ∈ K) :
    IsForwardInvariant N κ K :=
  isForwardInvariant_of_compact_trapping (by
    unfold massAction monomial
    fun_prop) hK htrap

end Persistence

end

end GAC
