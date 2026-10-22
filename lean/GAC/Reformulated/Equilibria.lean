import GAC.DetailedBalance

/-!
Direct proof of the exponential parametrization of positive equilibria.
Reuses the flux and dissipation identities from GAC.DetailedBalance, not its
convergence theorem or a pre-existing equilibrium equivalence. Attribution and
licenses are recorded in `docs/SOURCE_MAP.md`.
-/

open GAC.Persistence

noncomputable section

namespace GAC.Reformulated

variable {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
  {c x : Fin d → ℝ}

/-- The ordinary coordinate-dot-product orthogonal complement of S. -/
def Normal (N : ReactionNetwork d) (w : Fin d → ℝ) : Prop :=
  ∀ v ∈ stoichSubspace N, dotL w v = 0

def logShift (c x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => Real.log (x i) - Real.log (c i)

def expShift (c w : Fin d → ℝ) : Fin d → ℝ :=
  fun i => c i * Real.exp (w i)

lemma dot_logShift_reaction (e : Reaction N) :
    dotL (logShift c x) (reactionVector e) =
      logRatio c x e.val.2 - logRatio c x e.val.1 := by
  change (∑ i, (Real.log (x i) - Real.log (c i)) * reactionVector e i) = _
  simp only [reactionVector, logRatio, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma normal_iff_gaps : Normal N (logShift c x) ↔
    ∀ e : Reaction N, logRatio c x e.val.1 = logRatio c x e.val.2 := by
  constructor
  · intro h e
    have he := h (reactionVector e) (Submodule.subset_span ⟨e, rfl⟩)
    rw [dot_logShift_reaction] at he
    linarith
  · intro hg
    have hS : stoichSubspace N ≤ LinearMap.ker (dotL (logShift c x)) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨e, rfl⟩
      change dotL (logShift c x) (reactionVector e) = 0
      rw [dot_logShift_reaction, hg e, sub_self]
    exact fun v hv => hS hv

/-- Pair the reversed summands; balanced fluxes cancel coordinate by coordinate. -/
lemma field_zero_of_balanced_flux (hr : IsReversible N)
    (hf : ∀ e : Reaction N,
      κ e * monomial x e.val.1 = κ (revR hr e) * monomial x e.val.2) :
    massAction N κ x = 0 := by
  funext i
  have h2 : 2 * ∑ e : Reaction N,
      κ e * monomial x e.val.1 * ((e.val.2 i : ℝ) - (e.val.1 i : ℝ)) = 0 := by
    rw [two_mul_sum_revR hr]
    refine Finset.sum_eq_zero fun e _ => ?_
    simp only [revR_fst, revR_snd]
    rw [← hf e]
    ring
  change (∑ e : Reaction N,
    κ e * monomial x e.val.1 * ((e.val.2 i : ℝ) - (e.val.1 i : ℝ))) = 0
  linarith

lemma field_zero_of_normal (hdb : IsDetailedBalanced N κ c) (hx : PositiveState x)
    (hw : Normal N (logShift c x)) : massAction N κ x = 0 := by
  apply field_zero_of_balanced_flux hdb.reversible
  intro e
  rw [flux_bwd hdb hx, flux_fwd hdb hx, (normal_iff_gaps.mp hw) e]

/-- Zero field forces every nonpositive term of the entropy identity to vanish. -/
lemma normal_of_field_zero (hκ : ∀ e, 0 < κ e) (hdb : IsDetailedBalanced N κ c)
    (hx : PositiveState x) (hf : massAction N κ x = 0) :
    Normal N (logShift c x) := by
  apply normal_iff_gaps.mpr
  have hD : dissip N κ c x = 0 := by simp [dissip, hf]
  have hsum := two_dissip hdb hx
  rw [hD, mul_zero] at hsum
  have hnp : ∀ e ∈ (Finset.univ : Finset (Reaction N)),
      (κ e * monomial c e.val.1) *
        ((logRatio c x e.val.2 - logRatio c x e.val.1) *
          (Real.exp (logRatio c x e.val.1) - Real.exp (logRatio c x e.val.2))) ≤ 0 :=
    fun e _ => mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (hκ e) (monomial_pos hdb.pos _)).le (gap_mul_exp_nonpos _ _)
  intro e
  have hz := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hsum.symm e (Finset.mem_univ e)
  by_contra hne
  have hn := mul_neg_of_pos_of_neg
    (mul_pos (hκ e) (monomial_pos hdb.pos e.val.1)) (gap_mul_exp_neg hne)
  linarith

lemma logShift_expShift (hc : PositiveState c) (w : Fin d → ℝ) :
    logShift c (expShift c w) = w := by
  funext i
  simp [logShift, expShift, Real.log_mul (hc i).ne' (Real.exp_pos _).ne']

lemma expShift_logShift (hc : PositiveState c) (hx : PositiveState x) :
    expShift c (logShift c x) = x := by
  funext i
  simp only [expShift, logShift, Real.exp_sub, Real.exp_log (hx i), Real.exp_log (hc i)]
  field_simp [(hc i).ne']

/-- Lemma 3.18: the entire positive equilibrium set, not one compatibility class. -/
theorem positive_equilibria_eq_exp_normal (hκ : ∀ e, 0 < κ e)
    (hdb : IsDetailedBalanced N κ c) :
    {x : Fin d → ℝ | PositiveState x ∧ massAction N κ x = 0} =
      expShift c '' {w | Normal N w} := by
  ext x
  constructor
  · rintro ⟨hx, hf⟩
    exact ⟨logShift c x, normal_of_field_zero hκ hdb hx hf,
      expShift_logShift hdb.pos hx⟩
  · rintro ⟨w, hw, rfl⟩
    have hx : PositiveState (expShift c w) :=
      fun i => mul_pos (hdb.pos i) (Real.exp_pos _)
    refine ⟨hx, field_zero_of_normal hdb hx ?_⟩
    rwa [logShift_expShift hdb.pos]

theorem exponential_parameter_unique (hc : PositiveState c)
    {w : Fin d → ℝ} (h : expShift c w = x) : w = logShift c x := by
  rw [← h, logShift_expShift hc]

end GAC.Reformulated
