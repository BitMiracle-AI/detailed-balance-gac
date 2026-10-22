-- Derived from upstream lean/OAI/Analysis/MassAction/LocalCertificateRadius.lean (revision 1581d4c), Apache-2.0.
-- Modified: module path, namespaces and cited declaration names changed; see docs/SOURCE_MAP.md.
import GAC.Persistence.Approximation.Layers.Certificates
import GAC.Persistence.Approximation.Local.MinimumBand
import GAC.Persistence.Approximation.Local.OffsetDecay

namespace GAC

noncomputable section

open Filter
open scoped Topology

namespace Persistence.Affine

/-- A fixed-minimum certificate supplies a common neighborhood radius with
both approximation throughout the band and the stronger offset decay used
by the interval-gluing construction. -/
theorem LocalCertificate.exists_radius
    {d : ℕ} (hd : 0 < d) {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (C : LocalCertificate d a b t E) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ L ∈ C.labels,
        L.offset =o[𝓝[>] (0 : ℝ)] (fun h => h ^ (t + ρ))) ∧
      ∀ s : ℝ, |s - t| < ρ → ApproximatesAtMinimum C.labels a b s E := by
  classical
  obtain ⟨ρ₀, hρ₀, hnear⟩ := approximatesAtMinimum_nearby
    hd C.labels a b t E C.approximation
  let : Nonempty C.labels := ⟨⟨_, C.baseline⟩⟩
  have hdecay (L : C.labels) : ∃ β : ℝ, t < β ∧
      L.val.offset =O[𝓝[>] (0 : ℝ)] (fun h => h ^ β) :=
    ⟨C.decayExponent, C.decay_gt, (C.offsets L.val L.property).isBigO⟩
  obtain ⟨ρ, hρ, hρsmall, hoffsets⟩ := exists_radius_with_offset_decay
    (fun L : C.labels => L.val.offset) t ρ₀ hρ₀ hdecay
  refine ⟨ρ, hρ, (fun L hL => hoffsets ⟨L, hL⟩), ?_⟩
  intro s hs
  apply hnear s
  have h := abs_lt.mp (hs.trans hρsmall)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end Persistence.Affine

end

end GAC
