import GAC.Persistence.Model.Network

/-! Direct log/exp compact-confinement criterion; no persistence theorem used. -/

open GAC.Persistence

noncomputable section

namespace GAC.Reformulated

variable {d : ℕ}

/-- Common-bound criterion, forward direction: bound continuous logarithms on the compact set. -/
theorem log_bound_of_compact_positive {K : Set (Fin d → ℝ)} (hK : IsCompact K)
    (hpos : ∀ x ∈ K, PositiveState x) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ K, ∀ i, |Real.log (x i)| ≤ L := by
  classical
  have hb : ∀ i : Fin d, ∃ M : ℝ, ∀ x ∈ K, ‖Real.log (x i)‖ ≤ M := by
    intro i
    apply hK.exists_bound_of_continuousOn
    intro x hx
    have hlog : ContinuousAt (fun y : Fin d → ℝ => Real.log (y i)) x :=
      ((continuous_apply i).continuousAt).log (hpos x hx i).ne'
    exact hlog.continuousWithinAt
  choose M hM using hb
  refine ⟨∑ i, |M i|, Finset.sum_nonneg (fun i _ => abs_nonneg _), ?_⟩
  intro x hx i
  calc
    |Real.log (x i)| ≤ M i := by simpa only [Real.norm_eq_abs] using hM i x hx
    _ ≤ |M i| := le_abs_self _
    _ ≤ ∑ j, |M j| := Finset.single_le_sum (fun j _ => abs_nonneg (M j)) (Finset.mem_univ i)

/-- Common-bound criterion, reverse direction: exponentiate into an explicit compact positive box. -/
theorem compact_positive_of_log_bound {A : Set (Fin d → ℝ)}
    (hpos : ∀ x ∈ A, PositiveState x) {L : ℝ}
    (hb : ∀ x ∈ A, ∀ i, |Real.log (x i)| ≤ L) :
    ∃ K : Set (Fin d → ℝ), IsCompact K ∧ A ⊆ K ∧ ∀ x ∈ K, PositiveState x := by
  refine ⟨Set.univ.pi (fun _ => Set.Icc (Real.exp (-L)) (Real.exp L)),
    isCompact_univ_pi (fun _ => isCompact_Icc), ?_, ?_⟩
  · intro x hx i _
    have hi := abs_le.mp (hb x hx i)
    constructor
    · simpa only [Real.exp_log (hpos x hx i)] using Real.exp_le_exp.mpr hi.1
    · simpa only [Real.exp_log (hpos x hx i)] using Real.exp_le_exp.mpr hi.2
  · intro x hx i
    exact (Real.exp_pos (-L)).trans_le (hx i (Set.mem_univ i)).1

theorem compact_positive_iff_log_bound {A : Set (Fin d → ℝ)}
    (hpos : ∀ x ∈ A, PositiveState x) :
    (∃ K : Set (Fin d → ℝ), IsCompact K ∧ A ⊆ K ∧ ∀ x ∈ K, PositiveState x) ↔
      ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ A, ∀ i, |Real.log (x i)| ≤ L := by
  constructor
  · rintro ⟨K, hK, hAK, hKpos⟩
    obtain ⟨L, hL, hb⟩ := log_bound_of_compact_positive hK hKpos
    exact ⟨L, hL, fun x hx => hb x (hAK hx)⟩
  · rintro ⟨L, _, hb⟩
    exact compact_positive_of_log_bound hpos hb

/-- Uniform over a whole family; existence is retained on both sides.
Specialize P to IsGlobalForwardSolution for the mass-action application. -/
theorem solution_family_log_confinement (P : (ℝ → Fin d → ℝ) → Prop)
    (hpos : ∀ x, P x → ∀ t : ℝ, 0 ≤ t → PositiveState (x t)) :
    ((∃ x, P x) ∧ ∃ K : Set (Fin d → ℝ), IsCompact K ∧
      (∀ z ∈ K, PositiveState z) ∧ ∀ x, P x → ∀ t : ℝ, 0 ≤ t → x t ∈ K) ↔
    ((∃ x, P x) ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ x, P x → ∀ t : ℝ, 0 ≤ t → ∀ i, |Real.log (x t i)| ≤ L) := by
  let A : Set (Fin d → ℝ) := {z | ∃ x, P x ∧ ∃ t : ℝ, 0 ≤ t ∧ z = x t}
  have hA : ∀ z ∈ A, PositiveState z := by
    rintro z ⟨x, hx, t, ht, rfl⟩
    exact hpos x hx t ht
  constructor
  · rintro ⟨hex, K, hK, hKpos, hmem⟩
    have hAK : A ⊆ K := by
      rintro z ⟨x, hx, t, ht, rfl⟩
      exact hmem x hx t ht
    obtain ⟨L, hL, hb⟩ := (compact_positive_iff_log_bound hA).mp ⟨K, hK, hAK, hKpos⟩
    exact ⟨hex, L, hL, fun x hx t ht => hb (x t) ⟨x, hx, t, ht, rfl⟩⟩
  · rintro ⟨hex, L, hL, hb⟩
    have hbA : ∀ z ∈ A, ∀ i, |Real.log (z i)| ≤ L := by
      rintro z ⟨x, hx, t, ht, rfl⟩
      exact hb x hx t ht
    obtain ⟨K, hK, hAK, hKpos⟩ := (compact_positive_iff_log_bound hA).mpr ⟨L, hL, hbA⟩
    exact ⟨hex, K, hK, hKpos, fun x hx t ht => hAK ⟨x, hx, t, ht, rfl⟩⟩

end GAC.Reformulated
