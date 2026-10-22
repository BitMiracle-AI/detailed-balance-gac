import Mathlib

/-! Lemma 3.8: finite affine inequalities, tight constraints, and short feasible rays.
The finite-slack proof is independent of the original barrier theorem.
-/

noncomputable section

namespace GAC.Reformulated

/-- A single slack/slope pair admits a positive step unless a tight constraint
has negative slope. The absolute-value denominator also covers zero slope. -/
lemma slack_step {a b : ℝ} (ha : 0 ≤ a) (htight : a = 0 → 0 ≤ b) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Icc 0 ε, 0 ≤ a + t * b := by
  by_cases hz : a = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    simpa [hz] using mul_nonneg ht.1 (htight hz)
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have hden : 0 < |b| + 1 := by positivity
    refine ⟨a / (|b| + 1), div_pos hap hden, ?_⟩
    intro t ht
    have hprod : t * (|b| + 1) ≤ a := (le_div_iff₀ hden).mp ht.2
    have hlo := mul_le_mul_of_nonneg_left (neg_abs_le b) ht.1
    nlinarith [ht.1]

/-- Uniform positive step for finitely many constraints, including an empty family. -/
lemma finite_slack_step {J : Type*} [Fintype J] (a b : J → ℝ)
    (ha : ∀ j, 0 ≤ a j) (htight : ∀ j, a j = 0 → 0 ≤ b j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Icc 0 ε, ∀ j, 0 ≤ a j + t * b j := by
  classical
  have hsteps : ∀ j, ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ Set.Icc 0 ε, 0 ≤ a j + t * b j :=
    fun j => slack_step (ha j) (htight j)
  choose δ hδ hbound using hsteps
  haveI : Nonempty {x : ℝ // 0 < x} := ⟨⟨1, zero_lt_one⟩⟩
  obtain ⟨r, hrδ⟩ :=
    Finite.exists_ge (fun j : J => (⟨δ j, hδ j⟩ : {x : ℝ // 0 < x}))
  exact ⟨r.val, r.property, fun t ht j => hbound j t ⟨ht.1, ht.2.trans (hrδ j)⟩⟩

/-- Lemma 3.8. Linear functionals represent the normals r_j; c_j are affine offsets. -/
theorem feasible_direction_iff_tight {J E : Type*} [Fintype J]
    [AddCommGroup E] [Module ℝ E] (r : J → E →ₗ[ℝ] ℝ) (c : J → ℝ)
    (M : ℝ) (z v : E) (hz : ∀ j, M ≤ r j z + c j) :
    (∀ j, r j z + c j = M → 0 ≤ r j v) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Icc 0 ε, ∀ j, M ≤ r j (z + t • v) + c j := by
  constructor
  · intro htight
    obtain ⟨ε, hε, hb⟩ := finite_slack_step
      (fun j => r j z + c j - M) (fun j => r j v)
      (fun j => sub_nonneg.mpr (hz j))
      (fun j hj => htight j (sub_eq_zero.mp hj))
    refine ⟨ε, hε, ?_⟩
    intro t ht j
    have := hb t ht j
    simp only [map_add, map_smul, smul_eq_mul]
    linarith
  · rintro ⟨ε, hε, hb⟩ j hj
    have h := hb ε ⟨hε.le, le_rfl⟩ j
    simp only [map_add, map_smul, smul_eq_mul] at h
    have hmul : 0 ≤ ε * r j v := by linarith
    exact (mul_nonneg_iff_of_pos_left hε).mp hmul

end GAC.Reformulated
