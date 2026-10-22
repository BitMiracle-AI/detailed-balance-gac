-- Derived from upstream lean/OAI/Analysis/MassAction/Main.lean (revision 1581d4c), Apache-2.0.
-- Modified: module path, namespaces and cited declaration names changed; see docs/SOURCE_MAP.md.
import GAC.Persistence.Confinement.ActiveBranches
import GAC.Persistence.Approximation.Uniform.ActivityCompactness
import GAC.Persistence.Approximation.Layers.LocalFromLabels
import GAC.Persistence.Approximation.Layers.Certificates
import GAC.Persistence.Approximation.Gluing.FullExistence
import GAC.Persistence.Approximation.Gluing.GlobalGluing
import GAC.Persistence.Approximation.Gluing.CutComparison
import GAC.Persistence.Approximation.Layers.LayerCertificates
import GAC.Persistence.Approximation.Local.PositiveLimitSets
import GAC.Persistence.Approximation.Local.CubeNeighborhood
import GAC.Persistence.Barrier.LabelPolytope
import GAC.Persistence.Asymptotics.DotSignGap
import GAC.Persistence.Confinement.MinimumAlongCurves
import GAC.Persistence.Confinement.ForwardInvariance
import GAC.Persistence.ODE.LipschitzExtension
import GAC.Persistence.ODE.PositiveBounds
import GAC.Persistence.ODE.CompactTrapping
import GAC.Persistence.ODE.InvariantBounds
import GAC.Persistence.Approximation.Gluing.FullExistenceAlternative
import GAC.Persistence.Flux.LevelIntegral
import GAC.Persistence.Flux.DirectedCuts
import GAC.Persistence.Confinement.MinimumMonotonicity
import GAC.Persistence.ODE.FirstBoundaryTime
import GAC.Persistence.Approximation.Layers.Labels
import GAC.Persistence.Approximation.Layers.ConstantLabels
import GAC.Persistence.Approximation.Layers.RelativeEstimates
import GAC.Persistence.ODE.PiecewiseDerivative
import GAC.Persistence.Approximation.Gluing.IntervalChains
import GAC.Persistence.Approximation.Gluing.OrderedCovers
import GAC.Persistence.Confinement.LabelTrapping
import GAC.Persistence.Approximation.Layers.LayerChain
import GAC.Persistence.ODE.LocalSolutions
import GAC.Persistence.Flux.InwardDirections
import GAC.Persistence.Model.Smoothness
import GAC.Persistence.Model.Network
import GAC.Persistence.Asymptotics.MonomialComparison
import GAC.Persistence.Barrier.FiniteLabelData
import GAC.Persistence.Barrier.Construction
import GAC.Persistence.ODE.Concatenation
import GAC.Persistence.ODE.GlobalExtension
import GAC.Persistence.ODE.Uniqueness
import GAC.Persistence.Barrier.ConstantBranch
import GAC.Persistence.Barrier.PlateauTopology
import GAC.Persistence.Barrier.Polyhedra
import GAC.Persistence.Asymptotics.PowerRatios
import GAC.Persistence.Asymptotics.SignMargins
import GAC.Persistence.Asymptotics.ParameterChoice
import GAC.Persistence.ODE.TrajectoryUniqueness
import GAC.Persistence.Approximation.Uniform.SequentialBounds
import GAC.Persistence.Approximation.Uniform.UniformData
import GAC.Persistence.Approximation.Local.OffsetDecay

namespace GAC

noncomputable section

namespace Persistence

theorem compact_convex_invariant_polytope :
    ∀ (d : ℕ) (N : ReactionNetwork d) (κ : Reaction N → ℝ),
      0 < d → WeaklyReversible N → (∀ e, 0 < κ e) →
      ∀ x0 : Fin d → ℝ, PositiveState x0 →
      ∃ K : Set (Fin d → ℝ),
        IsCompact K ∧ Convex ℝ K ∧ IsFinitePolyhedron K ∧
        x0 ∈ K ∧ K ⊆ {x | PositiveState x} ∧ IsForwardInvariant N κ K := by
  intro d N κ _ hweak hκ x0 hx0
  apply Barrier.compact_convex_invariant_polytope_of_uniform ?_
    N κ hweak hκ x0 hx0
  exact Affine.uniform_data_of_full_certificates
    (fun E hE => Affine.exists_full_certificate d (-1) 1 E (by norm_num)
      (fun r _ => hE r))

theorem bounded_persistent_of_weaklyReversible :
    ∀ (d : ℕ) (N : ReactionNetwork d) (κ : Reaction N → ℝ),
      0 < d → WeaklyReversible N → (∀ e, 0 < κ e) →
      ∀ x0 : Fin d → ℝ, PositiveState x0 →
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
        (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
        ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹ := by
  intro d N κ hd hweak hκ x0 hx0
  obtain ⟨K, hK, _, _, hxK, hpos, hinv⟩ :=
    compact_convex_invariant_polytope d N κ hd hweak hκ x0 hx0
  exact global_bounds_of_compact_invariant N κ x0 hK hxK hpos hinv

end Persistence

end

end GAC
