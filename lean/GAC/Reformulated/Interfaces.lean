import GAC.Reformulated.Equilibria
import GAC.Reformulated.Compactness
import GAC.Reformulated.FeasibleDirections

/-!
The restated forms of Section 3 used in the paper, connected to the main development:
the common logarithmic bound of Theorem 3.1, the feasible-direction form of
condition (B3) on a barrier plateau (Lemma 3.8), and Lemma 3.19 via the
exponential parameterization of Lemma 3.18.
-/

open GAC.Persistence

noncomputable section

namespace GAC.Reformulated

variable {d : ℕ}

/-- Theorem 3.1 in logarithmic form: existence together with one
logarithmic bound for every global forward solution from `x0`.
The bound is obtained through `Compactness.lean` from the reciprocal box of the
persistence theorem. Positivity is not implied, since `Real.log 0 = 0`. -/
theorem wr_trajectory_log_bound (N : ReactionNetwork d) (κ : Reaction N → ℝ)
    (hd : 0 < d) (hWR : WeaklyReversible N) (hκ : ∀ e, 0 < κ e)
    (x0 : Fin d → ℝ) (hx0 : PositiveState x0) :
    (∃ x, IsGlobalForwardSolution N κ x0 x) ∧ ∃ L : ℝ, 0 ≤ L ∧
      ∀ x, IsGlobalForwardSolution N κ x0 x → ∀ t : ℝ, 0 ≤ t →
        ∀ i, |Real.log (x t i)| ≤ L := by
  obtain ⟨ε, hε, -, hex, hbd⟩ :=
    bounded_persistent_of_weaklyReversible d N κ hd hWR hκ x0 hx0
  have hpos : ∀ x, IsGlobalForwardSolution N κ x0 x → ∀ t : ℝ, 0 ≤ t →
      PositiveState (x t) :=
    fun x hx t ht i => hε.trans_le (hbd x hx t ht i).1
  refine (solution_family_log_confinement (IsGlobalForwardSolution N κ x0) hpos).mp
    ⟨hex, Set.univ.pi fun _ => Set.Icc ε ε⁻¹, isCompact_univ_pi fun _ => isCompact_Icc,
      ?_, ?_⟩
  · intro z hz i
    exact hε.trans_le (hz i (Set.mem_univ i)).1
  · intro x hx t ht i _
    exact hbd x hx t ht i

section Plateau

variable {N : ReactionNetwork d} {κ : Reaction N → ℝ} {x₀ : Fin d → ℝ}

private lemma dotL_eq_dot (a w : Fin d → ℝ) : dotL a w = dot a w := rfl

/-- On the plateau the active branches are exactly the tight constraints,
because the constant branch fixes the minimum value. -/
lemma plateau_active_iff_tight (A : Barrier.BarrierData N κ x₀) {z : Fin d → ℝ}
    (hz : z ∈ A.plateau) (j : Fin A.n) :
    AffineActive A.slope A.offset z j ↔
      dot (A.slope j) z + A.offset j = A.offset A.constant_branch := by
  have hcb : dot (A.slope A.constant_branch) z + A.offset A.constant_branch =
      A.offset A.constant_branch := by
    simp [A.slope_constant, dot]
  constructor
  · intro h
    exact le_antisymm ((h A.constant_branch).trans_eq hcb) (hz j)
  · intro h k
    rw [h]
    exact hz k

/-- Lemma 3.8 on the plateau of a constructed barrier:
nonnegative slopes on all active branches are equivalent to short-segment
feasibility. The proof applies `feasible_direction_iff_tight` to the plateau
inequalities. -/
theorem plateau_feasible_direction_iff_active (A : Barrier.BarrierData N κ x₀)
    {z : Fin d → ℝ} (hz : z ∈ A.plateau) (v : Fin d → ℝ) :
    (∀ j, AffineActive A.slope A.offset z j → 0 ≤ dot (A.slope j) v) ↔
      ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Icc (0 : ℝ) ε, z + t • v ∈ A.plateau := by
  have key := feasible_direction_iff_tight (fun j => dotL (A.slope j)) A.offset
    (A.offset A.constant_branch) z v (fun j => by simpa only [dotL_eq_dot] using hz j)
  constructor
  · intro h
    obtain ⟨ε, hε, hb⟩ := key.mp fun j hj => by
      simpa only [dotL_eq_dot] using
        h j ((plateau_active_iff_tight A hz j).mpr (by simpa only [dotL_eq_dot] using hj))
    exact ⟨ε, hε, fun t ht j => by simpa only [dotL_eq_dot] using hb t ht j⟩
  · rintro ⟨ε, hε, hb⟩ j hj
    have h := key.mpr ⟨ε, hε, fun t ht j => by simpa only [dotL_eq_dot] using hb t ht j⟩ j
      (by simpa only [dotL_eq_dot] using (plateau_active_iff_tight A hz j).mp hj)
    simpa only [dotL_eq_dot] using h

/-- Condition (B3) in feasible-direction form: at every plateau point the
mass-action vector is a feasible direction of the plateau. -/
theorem plateau_massAction_feasible (A : Barrier.BarrierData N κ x₀)
    {z : Fin d → ℝ} (hz : z ∈ A.plateau) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Set.Icc (0 : ℝ) ε,
      z + t • massAction N κ z ∈ A.plateau :=
  (plateau_feasible_direction_iff_active A hz _).mp fun _ hj =>
    A.inward_on_box (interior_subset (A.plateau_subset_interior_box hz)) hj

end Plateau

section Uniqueness

variable {N : ReactionNetwork d} {κ : Reaction N → ℝ} {c : Fin d → ℝ}

/-- Lemma 3.19 derived from Lemma 3.18: the exponential parameter of each
positive equilibrium lies in `S⊥`, which forces equal equilibria in one class. -/
theorem equilibria_unique_of_exp_parameterization (hκ : ∀ e, 0 < κ e)
    (hdb : IsDetailedBalanced N κ c) {a b : Fin d → ℝ}
    (ha : PositiveState a) (hb : PositiveState b)
    (hfa : massAction N κ a = 0) (hfb : massAction N κ b = 0)
    (hab : a - b ∈ stoichSubspace N) : a = b := by
  have hnormal : ∀ x, PositiveState x → massAction N κ x = 0 →
      Normal N (logShift c x) := by
    intro x hx hf
    have hmem : x ∈ expShift c '' {w | Normal N w} := by
      rw [← positive_equilibria_eq_exp_normal hκ hdb]
      exact ⟨hx, hf⟩
    obtain ⟨w, hw, hwx⟩ := hmem
    rw [← exponential_parameter_unique hdb.pos hwx]
    exact hw
  exact eq_of_gap_zero ha hb (normal_iff_gaps.mp (hnormal a ha hfa))
    (normal_iff_gaps.mp (hnormal b hb hfb)) hab

end Uniqueness

end GAC.Reformulated
