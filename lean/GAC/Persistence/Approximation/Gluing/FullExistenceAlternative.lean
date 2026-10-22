-- Derived from upstream lean/OAI/Analysis/MassAction/CompleteAffine.lean (revision 1581d4c), Apache-2.0.
-- Modified: module path, namespaces and cited declaration names changed; see docs/SOURCE_MAP.md.
import GAC.Persistence.Approximation.Layers.LocalFromLowerDimension
import GAC.Persistence.Approximation.Gluing.FullFromLocal

namespace GAC

noncomputable section

namespace Persistence.Affine

/-- Full arbitrary-tolerance affine approximation, with both the dimension
induction and the finite interval gluing discharged. -/
theorem fullCertificate_exists :
    ∀ d : ℕ, ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) →
      Nonempty (FullCertificate d a b E) :=
  fullCertificate_of_local_constructor localCertificate_of_lower_fullCertificates

end Persistence.Affine

end

end GAC
