import GAC.Persistence.BoundedPersistence

/-!
# Global convergence of detailed balanced mass-action systems

This file takes `GAC.Persistence.bounded_persistent_of_weaklyReversible`
(positive trajectories of finite weakly reversible mass-action systems are bounded and persistent) as its only external input
and formalizes the classical argument of Steps 2–5 of the paper:

* Step 2: the derivative of the Horn–Jackson function `lyap` along trajectories is `dissip`, and `dissip ≤ 0`;
* Step 3: at positive states, `dissip = 0` iff `logRatio` agrees at both ends of every reaction, and then `massAction = 0`;
* Step 4: each stoichiometric compatibility class contains at most one positive equilibrium;
* Step 5: a LaSalle-type argument. Instead of invariance of ω-limit sets it uses a descent argument
  (bounded speed + a non-increasing Lyapunov function bounded below) to show `dissip = 0` at every cluster point.

The main theorem is `GAC.detailed_balanced_global_convergence`.
-/

open Filter Topology GAC.Persistence

noncomputable section

namespace GAC

variable {d : ℕ} {N : ReactionNetwork d}

/-! ### Definitions -/

/-- Reversible network: the reverse of every reaction is also a reaction. -/
def IsReversible (N : ReactionNetwork d) : Prop :=
  ∀ e ∈ N.reactions, (e.2, e.1) ∈ N.reactions

/-- The reverse reaction. -/
def revR (h : IsReversible N) (e : Reaction N) : Reaction N :=
  ⟨(e.val.2, e.val.1), h e.val e.property⟩

@[simp] lemma revR_fst (h : IsReversible N) (e : Reaction N) : (revR h e).val.1 = e.val.2 := rfl

@[simp] lemma revR_snd (h : IsReversible N) (e : Reaction N) : (revR h e).val.2 = e.val.1 := rfl

lemma revR_revR (h : IsReversible N) (e : Reaction N) : revR h (revR h e) = e := Subtype.ext rfl

/-- Detailed balance: the network is reversible and a positive state `xs` balances every forward/reverse pair. -/
structure IsDetailedBalanced (N : ReactionNetwork d) (κ : Reaction N → ℝ) (xs : Fin d → ℝ) :
    Prop where
  reversible : IsReversible N
  pos : PositiveState xs
  balance : ∀ e : Reaction N,
    κ e * monomial xs e.val.1 = κ (revR reversible e) * monomial xs e.val.2

/-- The reaction vector `y' - y`. -/
def reactionVector (e : Reaction N) : Fin d → ℝ :=
  fun i => (e.val.2 i : ℝ) - (e.val.1 i : ℝ)

/-- The stoichiometric subspace `S = span {y' - y}`. -/
def stoichSubspace (N : ReactionNetwork d) : Submodule ℝ (Fin d → ℝ) :=
  Submodule.span ℝ (Set.range (reactionVector (N := N)))

/-- `logRatio xs x y = ∑ yᵢ (log xᵢ - log xsᵢ)`, that is, `log (x^y / xs^y)`. -/
def logRatio (xs x : Fin d → ℝ) (y : Fin d → ℕ) : ℝ :=
  ∑ i, (y i : ℝ) * (Real.log (x i) - Real.log (xs i))

/-- The Horn–Jackson Lyapunov function. -/
def lyap (xs x : Fin d → ℝ) : ℝ :=
  ∑ i, (x i * (Real.log (x i) - Real.log (xs i)) - x i + xs i)

/-- `∇V · f`: the derivative of the Lyapunov function along the vector field. -/
def dissip (N : ReactionNetwork d) (κ : Reaction N → ℝ) (xs x : Fin d → ℝ) : ℝ :=
  ∑ i, (Real.log (x i) - Real.log (xs i)) * massAction N κ x i

/-- The linear functional given by the inner product with `c`. -/
def dotL (c : Fin d → ℝ) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun w := ∑ i, c i * w i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.mul_sum, mul_left_comm]

/-! ### Basic lemmas -/

lemma weaklyReversible_of_reversible (h : IsReversible N) : WeaklyReversible N :=
  fun e => Relation.TransGen.single (h e.val e.property)

lemma sum_revR (h : IsReversible N) (F : Reaction N → ℝ) :
    ∑ e, F (revR h e) = ∑ e, F e :=
  Equiv.sum_comp (Function.Involutive.toPerm (revR h) (revR_revR h)) F

lemma two_mul_sum_revR (h : IsReversible N) (F : Reaction N → ℝ) :
    2 * ∑ e, F e = ∑ e, (F e + F (revR h e)) := by
  rw [Finset.sum_add_distrib, sum_revR h, two_mul]

lemma monomial_pos {x : Fin d → ℝ} (hx : PositiveState x) (y : Fin d → ℕ) :
    0 < monomial x y :=
  Finset.prod_pos fun i _ => pow_pos (hx i) _

lemma monomial_eq_exp {x : Fin d → ℝ} (hx : PositiveState x) (y : Fin d → ℕ) :
    monomial x y = Real.exp (∑ i, (y i : ℝ) * Real.log (x i)) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Real.exp_nat_mul, Real.exp_log (hx i)]

lemma monomial_ratio {xs x : Fin d → ℝ} (hxs : PositiveState xs) (hx : PositiveState x)
    (y : Fin d → ℕ) : monomial x y = monomial xs y * Real.exp (logRatio xs x y) := by
  rw [monomial_eq_exp hx, monomial_eq_exp hxs, ← Real.exp_add]
  congr 1
  unfold logRatio
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma continuous_massAction (N : ReactionNetwork d) (κ : Reaction N → ℝ) :
    Continuous (massAction N κ) := by
  unfold massAction monomial
  fun_prop

lemma massAction_eq_sum_smul (κ : Reaction N → ℝ) (x : Fin d → ℝ) :
    massAction N κ x = ∑ e, (κ e * monomial x e.val.1) • reactionVector e := by
  funext i
  simp [massAction, reactionVector, Finset.sum_apply, smul_eq_mul]

lemma massAction_mem_stoich (κ : Reaction N → ℝ) (x : Fin d → ℝ) :
    massAction N κ x ∈ stoichSubspace N := by
  rw [massAction_eq_sum_smul]
  exact Submodule.sum_mem _ fun e _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨e, rfl⟩)

/-! ### Supplement to Step 1: trajectories stay in their compatibility class -/

/-- A difference-quotient estimate from the mean value theorem. -/
lemma sub_le_of_hasDerivAt_le {g g' : ℝ → ℝ} {a b C : ℝ} (hab : a < b)
    (hg : ∀ s ∈ Set.Icc a b, HasDerivAt g (g' s) s) (hC : ∀ s ∈ Set.Ioo a b, g' s ≤ C) :
    g b - g a ≤ C * (b - a) := by
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope g g' hab
    (fun s hs => (hg s hs).continuousAt.continuousWithinAt)
    (fun s hs => hg s (Set.Ioo_subset_Icc_self hs))
  have hba : 0 < b - a := sub_pos.mpr hab
  have : g b - g a = g' c * (b - a) := by rw [hc']; field_simp
  rw [this]
  exact mul_le_mul_of_nonneg_right (hC c hc) hba.le

lemma sol_mem_class {κ : Reaction N → ℝ} {x0 : Fin d → ℝ} {x : ℝ → Fin d → ℝ}
    (hx : IsGlobalForwardSolution N κ x0 x) {t : ℝ} (ht : 0 ≤ t) :
    x t - x0 ∈ stoichSubspace N := by
  -- Show that every functional `φ` in the annihilator of `S` vanishes on `x t - x0`.
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  -- Write `φ` in coordinates as `φ w = ∑ wᵢ cᵢ`.
  set c : Fin d → ℝ := fun i => φ (fun j => if i = j then 1 else 0) with hc
  have hrep : ∀ w, φ w = ∑ i, w i * c i := fun w => by
    rw [LinearMap.pi_apply_eq_sum_univ φ w]
    simp [hc, smul_eq_mul]
  have hder : ∀ s, 0 ≤ s → HasDerivAt (fun s => ∑ i, x s i * c i) 0 s := by
    intro s hs
    have h := HasDerivAt.fun_sum (u := Finset.univ) (A := fun i s => x s i * c i)
      (A' := fun i => massAction N κ (x s) i * c i)
      (fun i _ => ((hasDerivAt_pi.mp (hx.2 s hs)) i).mul_const (c i))
    have h0 : ∑ i, massAction N κ (x s) i * c i = 0 := by
      rw [← hrep]; exact hφ _ (massAction_mem_stoich κ (x s))
    rwa [h0] at h
  rw [map_sub, hrep (x t), hrep x0]
  rcases ht.eq_or_lt with h | h
  · subst h; rw [hx.1, sub_self]
  · -- Mean value theorem: the derivative vanishes, so the values at `t` and `0` agree.
    obtain ⟨s, hs, hslope⟩ := exists_hasDerivAt_eq_slope
      (fun s => ∑ i, x s i * c i) (fun _ => (0 : ℝ)) h
      (fun s hs => (hder s hs.1).continuousAt.continuousWithinAt)
      (fun s hs => hder s hs.1.le)
    have hne : t - 0 ≠ 0 := by linarith
    have heq : (∑ i, x t i * c i) - ∑ i, x 0 i * c i = 0 := by
      field_simp at hslope
      linarith
    rw [hx.1] at heq
    exact heq

/-! ### Step 2: the Lyapunov function -/

lemma lyap_term_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ a * (Real.log a - Real.log b) - a + b := by
  have h1 : Real.log b - Real.log a ≤ b / a - 1 := by
    rw [← Real.log_div hb.ne' ha.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hb ha)
  have h2 : a * (b / a - 1) = b - a := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h1 ha.le]

lemma lyap_nonneg {xs x : Fin d → ℝ} (hxs : PositiveState xs) (hx : PositiveState x) :
    0 ≤ lyap xs x :=
  Finset.sum_nonneg fun i _ => lyap_term_nonneg (hx i) (hxs i)

lemma hasDerivAt_lyap {κ : Reaction N → ℝ} {xs : Fin d → ℝ} {x : ℝ → Fin d → ℝ} {t : ℝ}
    (hxd : HasDerivAt x (massAction N κ (x t)) t) (hpos : PositiveState (x t)) :
    HasDerivAt (fun s => lyap xs (x s)) (dissip N κ xs (x t)) t := by
  unfold lyap dissip
  refine HasDerivAt.fun_sum (u := Finset.univ)
    (A := fun i s => x s i * (Real.log (x s i) - Real.log (xs i)) - x s i + xs i)
    (A' := fun i => (Real.log (x t i) - Real.log (xs i)) * massAction N κ (x t) i) ?_
  intro i _
  have hi : HasDerivAt (fun s => x s i) (massAction N κ (x t) i) t := hasDerivAt_pi.mp hxd i
  have h := ((hi.mul ((hi.log (hpos i).ne').sub_const (Real.log (xs i)))).sub hi).add_const (xs i)
  convert h using 1
  have := (hpos i).ne'
  field_simp
  ring

lemma continuousAt_dissip (κ : Reaction N → ℝ) (xs : Fin d → ℝ) {z : Fin d → ℝ}
    (hz : PositiveState z) : ContinuousAt (dissip N κ xs) z := by
  unfold dissip
  have hcomp : ∀ i, ContinuousAt
      (fun x : Fin d → ℝ => (Real.log (x i) - Real.log (xs i)) * massAction N κ x i) z := by
    intro i
    have h1 : ContinuousAt (fun x : Fin d → ℝ => Real.log (x i)) z :=
      ((continuous_apply i).continuousAt).log (hz i).ne'
    have h2 : ContinuousAt (fun x : Fin d → ℝ => massAction N κ x i) z :=
      ((continuous_apply i).comp (continuous_massAction N κ)).continuousAt
    exact (h1.sub continuousAt_const).mul h2
  exact tendsto_finsetSum _ fun i _ => hcomp i

lemma dissip_eq_sum (κ : Reaction N → ℝ) (xs x : Fin d → ℝ) :
    dissip N κ xs x = ∑ e : Reaction N,
      κ e * monomial x e.val.1 * (logRatio xs x e.val.2 - logRatio xs x e.val.1) := by
  unfold dissip massAction logRatio
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun i _ => by ring

section Balanced

variable {κ : Reaction N → ℝ} {xs : Fin d → ℝ}

lemma flux_fwd (hdb : IsDetailedBalanced N κ xs) {x : Fin d → ℝ} (hx : PositiveState x)
    (e : Reaction N) :
    κ e * monomial x e.val.1 =
      (κ e * monomial xs e.val.1) * Real.exp (logRatio xs x e.val.1) := by
  rw [monomial_ratio hdb.pos hx]; ring

lemma flux_bwd (hdb : IsDetailedBalanced N κ xs) {x : Fin d → ℝ} (hx : PositiveState x)
    (e : Reaction N) :
    κ (revR hdb.reversible e) * monomial x e.val.2 =
      (κ e * monomial xs e.val.1) * Real.exp (logRatio xs x e.val.2) := by
  rw [monomial_ratio hdb.pos hx, hdb.balance e]; ring

/-- The dissipation identity after pairing forward and reverse reactions. -/
lemma two_dissip (hdb : IsDetailedBalanced N κ xs) {x : Fin d → ℝ} (hx : PositiveState x) :
    2 * dissip N κ xs x = ∑ e : Reaction N, (κ e * monomial xs e.val.1) *
      ((logRatio xs x e.val.2 - logRatio xs x e.val.1) *
        (Real.exp (logRatio xs x e.val.1) - Real.exp (logRatio xs x e.val.2))) := by
  rw [dissip_eq_sum, two_mul_sum_revR hdb.reversible]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [revR_fst, revR_snd]
  rw [flux_fwd hdb hx, flux_bwd hdb hx]
  ring

lemma gap_mul_exp_neg {a b : ℝ} (h : a ≠ b) : (b - a) * (Real.exp a - Real.exp b) < 0 := by
  rcases h.lt_or_gt with h | h
  · exact mul_neg_of_pos_of_neg (by linarith) (by linarith [Real.exp_lt_exp.mpr h])
  · exact mul_neg_of_neg_of_pos (by linarith) (by linarith [Real.exp_lt_exp.mpr h])

lemma gap_mul_exp_nonpos (a b : ℝ) : (b - a) * (Real.exp a - Real.exp b) ≤ 0 := by
  by_cases h : a = b
  · simp [h]
  · exact (gap_mul_exp_neg h).le

/-- Step 2: `dV/dt ≤ 0`. -/
lemma dissip_nonpos (hκ : ∀ e, 0 < κ e) (hdb : IsDetailedBalanced N κ xs)
    {x : Fin d → ℝ} (hx : PositiveState x) : dissip N κ xs x ≤ 0 := by
  have h := two_dissip hdb hx
  have : ∑ e : Reaction N, (κ e * monomial xs e.val.1) *
      ((logRatio xs x e.val.2 - logRatio xs x e.val.1) *
        (Real.exp (logRatio xs x e.val.1) - Real.exp (logRatio xs x e.val.2))) ≤ 0 :=
    Finset.sum_nonpos fun e _ => mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (hκ e) (monomial_pos hdb.pos _)).le (gap_mul_exp_nonpos _ _)
  linarith

/-! ### Step 3: positive states with `dV/dt = 0` are exactly the positive equilibria -/

lemma gap_zero_of_dissip_eq_zero (hκ : ∀ e, 0 < κ e) (hdb : IsDetailedBalanced N κ xs)
    {x : Fin d → ℝ} (hx : PositiveState x) (h0 : dissip N κ xs x = 0) :
    ∀ e : Reaction N, logRatio xs x e.val.1 = logRatio xs x e.val.2 := by
  intro e
  have hnp : ∀ e ∈ (Finset.univ : Finset (Reaction N)), (κ e * monomial xs e.val.1) *
      ((logRatio xs x e.val.2 - logRatio xs x e.val.1) *
        (Real.exp (logRatio xs x e.val.1) - Real.exp (logRatio xs x e.val.2))) ≤ 0 :=
    fun e _ => mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (hκ e) (monomial_pos hdb.pos _)).le (gap_mul_exp_nonpos _ _)
  have hsum : ∑ e : Reaction N, (κ e * monomial xs e.val.1) *
      ((logRatio xs x e.val.2 - logRatio xs x e.val.1) *
        (Real.exp (logRatio xs x e.val.1) - Real.exp (logRatio xs x e.val.2))) = 0 := by
    rw [← two_dissip hdb hx, h0, mul_zero]
  have hall := (Finset.sum_eq_zero_iff_of_nonpos hnp).mp hsum e (Finset.mem_univ e)
  by_contra hne
  have := mul_neg_of_pos_of_neg (mul_pos (hκ e) (monomial_pos hdb.pos e.val.1))
    (gap_mul_exp_neg hne)
  linarith

lemma massAction_eq_zero_of_gap (hdb : IsDetailedBalanced N κ xs) {x : Fin d → ℝ}
    (hx : PositiveState x)
    (hg : ∀ e : Reaction N, logRatio xs x e.val.1 = logRatio xs x e.val.2) :
    massAction N κ x = 0 := by
  funext i
  have h2 : 2 * ∑ e : Reaction N,
      κ e * monomial x e.val.1 * ((e.val.2 i : ℝ) - (e.val.1 i : ℝ)) = 0 := by
    rw [two_mul_sum_revR hdb.reversible]
    refine Finset.sum_eq_zero fun e _ => ?_
    simp only [revR_fst, revR_snd]
    have : κ (revR hdb.reversible e) * monomial x e.val.2 = κ e * monomial x e.val.1 := by
      rw [flux_bwd hdb hx, flux_fwd hdb hx, hg e]
    rw [this]; ring
  have : massAction N κ x i = 0 := by
    simp only [massAction]; linarith
  simpa using this

lemma dissip_eq_zero_of_massAction_eq_zero {x : Fin d → ℝ} (h : massAction N κ x = 0) :
    dissip N κ xs x = 0 := by
  simp [dissip, h]

/-! ### Step 4: at most one positive equilibrium in each compatibility class -/

lemma log_sub_mul_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hne : a ≠ b) :
    0 < (Real.log a - Real.log b) * (a - b) := by
  rcases hne.lt_or_gt with h | h
  · exact mul_pos_of_neg_of_neg (by linarith [Real.log_lt_log ha h]) (by linarith)
  · exact mul_pos (by linarith [Real.log_lt_log hb h]) (by linarith)

lemma log_sub_mul_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ (Real.log a - Real.log b) * (a - b) := by
  by_cases h : a = b
  · simp [h]
  · exact (log_sub_mul_pos ha hb h).le

lemma dot_reactionVector (xs a b : Fin d → ℝ) (e : Reaction N) :
    ∑ i, (Real.log (a i) - Real.log (b i)) * reactionVector e i =
      (logRatio xs a e.val.2 - logRatio xs a e.val.1) -
        (logRatio xs b e.val.2 - logRatio xs b e.val.1) := by
  simp only [logRatio, reactionVector, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma eq_of_gap_zero {a b : Fin d → ℝ} (ha : PositiveState a) (hb : PositiveState b)
    (hga : ∀ e : Reaction N, logRatio xs a e.val.1 = logRatio xs a e.val.2)
    (hgb : ∀ e : Reaction N, logRatio xs b e.val.1 = logRatio xs b e.val.2)
    (hab : a - b ∈ stoichSubspace N) : a = b := by
  set c : Fin d → ℝ := fun i => Real.log (a i) - Real.log (b i) with hc
  have hS : stoichSubspace N ≤ LinearMap.ker (dotL c) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨e, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, dotL, LinearMap.coe_mk, AddHom.coe_mk, hc]
    rw [dot_reactionVector xs a b e, hga e, hgb e]
    ring
  have h0 : ∑ i, c i * (a i - b i) = 0 := by
    have := hS hab
    simpa [dotL] using this
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin d)), 0 ≤ c i * (a i - b i) :=
    fun i _ => log_sub_mul_nonneg (ha i) (hb i)
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0
  funext i
  by_contra hne
  exact (log_sub_mul_pos (ha i) (hb i) hne).ne' (hz i (Finset.mem_univ _))

/-- Step 4: two positive equilibria in the same compatibility class are equal. -/
lemma eq_of_equilibria (hκ : ∀ e, 0 < κ e) (hdb : IsDetailedBalanced N κ xs)
    {a b : Fin d → ℝ} (ha : PositiveState a) (hb : PositiveState b)
    (hfa : massAction N κ a = 0) (hfb : massAction N κ b = 0)
    (hab : a - b ∈ stoichSubspace N) : a = b :=
  eq_of_gap_zero ha hb
    (gap_zero_of_dissip_eq_zero hκ hdb ha (dissip_eq_zero_of_massAction_eq_zero hfa))
    (gap_zero_of_dissip_eq_zero hκ hdb hb (dissip_eq_zero_of_massAction_eq_zero hfb)) hab

/-! ### Step 5: cluster points satisfy `dV/dt = 0` (LaSalle-type argument) -/

/-- If a trajectory stays uniformly away from the boundary with bounded speed, `dissip = 0` at every positive cluster point.
As in Lemma 3.20 of the paper: first choose `V(T) < inf V + η δ`, then `t ≥ T` with the trajectory
near the cluster point. The speed bound keeps it there for time `δ`, so one descent gives `V(t + δ) < inf V`, a contradiction.
The proof uses neither LaSalle's invariance principle, uniqueness of solutions, nor continuous dependence on initial data. -/
lemma dissip_eq_zero_of_mapClusterPt (hκ : ∀ e, 0 < κ e) (hdb : IsDetailedBalanced N κ xs)
    {x0 : Fin d → ℝ} {ε : ℝ} (hε : 0 < ε) {x : ℝ → Fin d → ℝ}
    (hx : IsGlobalForwardSolution N κ x0 x)
    (hbd : ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹)
    {B : ℝ} (hB : 0 < B) (hspeed : ∀ t : ℝ, 0 ≤ t → ‖massAction N κ (x t)‖ ≤ B)
    {z : Fin d → ℝ} (hzpos : PositiveState z) (hz : MapClusterPt z atTop x) :
    dissip N κ xs z = 0 := by
  have hpos : ∀ t : ℝ, 0 ≤ t → PositiveState (x t) :=
    fun t ht i => hε.trans_le (hbd t ht i).1
  set W : ℝ → ℝ := fun s => lyap xs (x s) with hWdef
  have hW : ∀ s : ℝ, 0 ≤ s → HasDerivAt W (dissip N κ xs (x s)) s :=
    fun s hs => hasDerivAt_lyap (hx.2 s hs) (hpos s hs)
  have hanti : ∀ a b : ℝ, 0 ≤ a → a ≤ b → W b ≤ W a := by
    intro a b ha hab
    rcases hab.eq_or_lt with h | hlt
    · rw [h]
    · have := sub_le_of_hasDerivAt_le hlt (fun s hs => hW s (ha.trans hs.1))
        (fun s hs => dissip_nonpos hκ hdb (hpos s (ha.trans hs.1.le)))
      linarith
  by_contra hne
  have hneg : dissip N κ xs z < 0 := lt_of_le_of_ne (dissip_nonpos hκ hdb hzpos) hne
  set η : ℝ := -dissip N κ xs z / 2 with hη
  have hηpos : 0 < η := by linarith
  have hev : ∀ᶠ w in 𝓝 z, dissip N κ xs w < -η :=
    (continuousAt_dissip κ xs hzpos).eventually (Iio_mem_nhds (by linarith))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := r / (2 * B) with hδdef
  have hδ : 0 < δ := by positivity
  have hne' : (W '' Set.Ici 0).Nonempty := ⟨W 0, 0, le_refl (0 : ℝ), rfl⟩
  have hbdd : BddBelow (W '' Set.Ici 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact lyap_nonneg hdb.pos (hpos s hs)
  set c : ℝ := sInf (W '' Set.Ici 0) with hcdef
  have hlt : c < c + η * δ := by nlinarith
  obtain ⟨_, ⟨T, hT, rfl⟩, hTlt⟩ := exists_lt_of_csInf_lt hne' hlt
  have hT0 : (0 : ℝ) ≤ T := hT
  have hfreq := (mapClusterPt_iff_frequently.mp hz) (Metric.ball z (r / 2))
    (Metric.ball_mem_nhds z (by positivity))
  obtain ⟨t, htT, htz⟩ := frequently_atTop.mp hfreq T
  have ht0 : 0 ≤ t := hT0.trans htT
  have hmove : ∀ s ∈ Set.Icc t (t + δ), ‖x s - x t‖ ≤ B * (s - t) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := x)
      (f' := fun s => massAction N κ (x s))
      (fun s hs => (hx.2 s (ht0.trans hs.1)).hasDerivWithinAt)
      (fun s hs => hspeed s (ht0.trans hs.1))
  have hBδ : B * δ = r / 2 := by rw [hδdef]; field_simp
  have hnear : ∀ s ∈ Set.Icc t (t + δ), dist (x s) z < r := by
    intro s hs
    have h1 := hmove s hs
    have h2 : B * (s - t) ≤ B * δ :=
      mul_le_mul_of_nonneg_left (by linarith [hs.2]) hB.le
    have h3 : dist (x t) z < r / 2 := htz
    calc dist (x s) z ≤ dist (x s) (x t) + dist (x t) z := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by rw [dist_eq_norm]; linarith
      _ = r := by ring
  have hdrop := sub_le_of_hasDerivAt_le (show t < t + δ by linarith)
    (fun s hs => hW s (ht0.trans hs.1))
    (fun s hs => (hball (hnear s ⟨hs.1.le, hs.2.le⟩)).le)
  have hWt : W t ≤ W T := hanti T t hT0 htT
  have hWc : c ≤ W (t + δ) := csInf_le hbdd ⟨t + δ, by simp only [Set.mem_Ici]; linarith, rfl⟩
  have : -η * (t + δ - t) = -(η * δ) := by ring
  linarith

end Balanced

/-! ### Main theorem -/

/-- **Global convergence of detailed balanced mass-action systems** (using the imported, proved boundedness and persistence theorem).

Assume the network is reversible, the rates are positive, and detailed balance holds at a positive state `xs`. For every positive `x0`:
there is a unique positive equilibrium `xbar` in the compatibility class `x0 + S` of `x0`; a global solution exists;
and every global forward solution converges to `xbar`. -/
theorem detailed_balanced_global_convergence
    (N : ReactionNetwork d) (κ : Reaction N → ℝ) (hκ : ∀ e, 0 < κ e)
    {xs : Fin d → ℝ} (hdb : IsDetailedBalanced N κ xs)
    (x0 : Fin d → ℝ) (hx0 : PositiveState x0) :
    ∃ xbar : Fin d → ℝ,
      PositiveState xbar ∧ massAction N κ xbar = 0 ∧ xbar - x0 ∈ stoichSubspace N ∧
      (∀ z : Fin d → ℝ, PositiveState z → massAction N κ z = 0 →
        z - x0 ∈ stoichSubspace N → z = xbar) ∧
      (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
      ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        Tendsto x atTop (𝓝 xbar) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- The zero-dimensional case is trivial.
    refine ⟨x0, fun i => i.elim0, Subsingleton.elim _ _,
      by rw [sub_self]; exact Submodule.zero_mem _,
      fun z _ _ _ => Subsingleton.elim _ _, ⟨fun _ => x0, rfl, fun t _ => ?_⟩, fun x _ => ?_⟩
    · convert hasDerivAt_const t x0
    · have : x = fun _ => x0 := funext fun _ => Subsingleton.elim _ _
      rw [this]
      exact tendsto_const_nhds
  -- Step 1: apply the boundedness and persistence theorem.
  obtain ⟨ε, hε, -, ⟨x₁, hx₁⟩, hbd⟩ :=
    bounded_persistent_of_weaklyReversible d N κ hd
      (weaklyReversible_of_reversible hdb.reversible) hκ x0 hx0
  set S := stoichSubspace N with hSdef
  set K : Set (Fin d → ℝ) := (Set.univ.pi fun _ => Set.Icc ε ε⁻¹) ∩ {z | z - x0 ∈ S} with hKdef
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      ((S.closed_of_finiteDimensional).preimage (continuous_id.sub continuous_const))
  have hmemK : ∀ x, IsGlobalForwardSolution N κ x0 x → ∀ t : ℝ, 0 ≤ t → x t ∈ K :=
    fun x hx t ht => ⟨fun i _ => hbd x hx t ht i, sol_mem_class hx ht⟩
  have hKpos : ∀ z ∈ K, PositiveState z := fun z hz i => hε.trans_le (hz.1 i (Set.mem_univ i)).1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuous_massAction N κ).continuousOn
  have hspeed : ∀ x, IsGlobalForwardSolution N κ x0 x → ∀ t : ℝ, 0 ≤ t →
      ‖massAction N κ (x t)‖ ≤ |M| + 1 :=
    fun x hx t ht => (hM _ (hmemK x hx t ht)).trans (by linarith [le_abs_self M])
  -- Step 5: cluster points are equilibria.
  have hcl : ∀ x, IsGlobalForwardSolution N κ x0 x → ∀ z ∈ K, MapClusterPt z atTop x →
      massAction N κ z = 0 := by
    intro x hx z hzK hz
    have hD := dissip_eq_zero_of_mapClusterPt hκ hdb hε hx (hbd x hx) (by positivity)
      (hspeed x hx) (hKpos z hzK) hz
    exact massAction_eq_zero_of_gap hdb (hKpos z hzK)
      (gap_zero_of_dissip_eq_zero hκ hdb (hKpos z hzK) hD)
  have hev : ∀ x, IsGlobalForwardSolution N κ x0 x → ∀ᶠ t in atTop, x t ∈ K :=
    fun x hx => eventually_atTop.mpr ⟨0, fun t ht => hmemK x hx t ht⟩
  obtain ⟨xbar, hbarK, hbar⟩ :=
    hK.exists_mapClusterPt (f := atTop) (u := x₁) (le_principal_iff.mpr (hev x₁ hx₁))
  have hbar_eq := hcl x₁ hx₁ xbar hbarK hbar
  -- Step 4: uniqueness.
  have huniq : ∀ z : Fin d → ℝ, PositiveState z → massAction N κ z = 0 → z - x0 ∈ S →
      z = xbar := fun z hz hfz hzS =>
    eq_of_equilibria hκ hdb hz (hKpos _ hbarK) hfz hbar_eq
      (by simpa using S.sub_mem hzS hbarK.2)
  refine ⟨xbar, hKpos _ hbarK, hbar_eq, hbarK.2, huniq, ⟨x₁, hx₁⟩, fun x hx => ?_⟩
  exact hK.tendsto_nhds_of_unique_mapClusterPt (hev x hx) fun z hzK hz =>
    huniq z (hKpos z hzK) (hcl x hx z hzK hz) hzK.2

end GAC
