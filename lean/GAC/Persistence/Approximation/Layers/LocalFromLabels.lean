-- Derived from upstream lean/OAI/Analysis/MassAction/AffineCertificateBridge.lean (revision 1581d4c), Apache-2.0.
-- Modified: module path, namespaces and cited declaration names changed; see docs/SOURCE_MAP.md.
import GAC.Persistence.Approximation.Layers.Certificates
import GAC.Persistence.Approximation.Layers.ConstantLabels

namespace GAC

noncomputable section
open Filter Topology

namespace Persistence.Affine

theorem localCertificate_of_label_certificates {d : ℕ}
    {Λ : Finset (Label d)} {a b t : ℝ} {E : (Fin d → ℝ) → ℝ}
    (hbaseline : constantLabel d t ∈ Λ)
    (hslopes : ∀ L ∈ Λ, Cube t b L.slope)
    (hminima : ∀ L ∈ Λ, HasMinimum L.slope t)
    (hcert : ∀ L ∈ Λ, FixedMinimumLabelCertificate Λ a b t E L) :
    Nonempty (LocalCertificate d a b t E) := by
  obtain ⟨η, hη, hoff⟩ := exists_common_offset_decay hcert
  exact ⟨{
    labels := Λ
    baseline := hbaseline
    slopes := hslopes
    minima := hminima
    decayExponent := η
    decay_gt := hη
    offsets := hoff
    approximation := approximatesAtMinimum_of_certificates hbaseline hcert
  }⟩

end Persistence.Affine

end

end GAC
