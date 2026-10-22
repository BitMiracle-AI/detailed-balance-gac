-- Derived from upstream lean/OAI/Analysis/MassAction/AffineExistence.lean (revision 1581d4c), Apache-2.0.
-- Modified: module path, namespaces and cited declaration names changed; see docs/SOURCE_MAP.md.
import GAC.Persistence.Approximation.Layers.TypeLayers
import GAC.Persistence.Approximation.Layers.LocalFromLayers
import GAC.Persistence.Approximation.Gluing.LocalToGlobal

namespace GAC

noncomputable section

namespace Persistence.Affine

/-- The full affine approximation certificate, obtained by dimension induction
and finite interval gluing. The tolerance need not be continuous. -/
theorem exists_full_certificate :
    ∀ d : ℕ, ∀ a b : ℝ, ∀ E : (Fin d → ℝ) → ℝ,
      a < b → (∀ r, Cube a b r → 0 < E r) →
      Nonempty (FullCertificate d a b E) := by
  apply fullCertificate_of_local_and_glue
  · intro d hd ih a b E hab hE t hat htb
    by_cases heq : t = b
    · subst t
      exact ⟨localCertificate_upper hd a b E (hE _ (fun _ => ⟨hab.le, le_rfl⟩))⟩
    · apply localCertificate_of_layers hd (lt_of_le_of_ne htb heq) E
        (hE _ (fun _ => ⟨hat, htb⟩))
      intro k hk hkd β htβ hβb
      obtain ⟨F, _, hF⟩ := exists_typeFamily_layerCertificate hk hkd htβ hβb E
        (fun r hr => hE r (fun i => ⟨hat.trans (hr i).1, (hr i).2⟩))
        (fun E' hE' => ih k hkd β b E' hβb hE')
      exact ⟨F, hF⟩
  · intro d hd a b E hab _ hlocal
    exact glue_localCertificates hd hab.le E hlocal

end Persistence.Affine

end

end GAC
