import GAC.CompactClass

/-!
# Paper interface

The names in this module follow the statements in the paper.
They are transparent abbreviations or proved wrappers over the rest of the project.
In particular, the weakly reversible theorem is proved in `GAC.Persistence`;
it is not a new axiom or an original result of this module.
Corollary 3.23 and the complex-balanced extension are outside this interface.
-/

open Filter Topology GAC.Persistence

noncomputable section

namespace GAC.Paper

variable {d : ℕ}

abbrev CRN (d : ℕ) := ReactionNetwork d
abbrev RxnIdx (N : CRN d) := Reaction N
abbrev HasReverses (N : CRN d) := GAC.IsReversible N
abbrev InOpenOrthant (x : Fin d → ℝ) := PositiveState x
abbrev xPow (x : Fin d → ℝ) (y : Fin d → ℕ) := monomial x y
abbrev rateField (N : CRN d) (κ : RxnIdx N → ℝ) := massAction N κ
abbrev reactionSpan (N : CRN d) := GAC.stoichSubspace N
abbrev SolvesForward (N : CRN d) (κ : RxnIdx N → ℝ)
    (x0 : Fin d → ℝ) (x : ℝ → Fin d → ℝ) := IsGlobalForwardSolution N κ x0 x
abbrev oppRxn {N : CRN d} (h : HasReverses N) (e : RxnIdx N) := GAC.revR h e
abbrev logQuot (c x : Fin d → ℝ) (y : Fin d → ℕ) := GAC.logRatio c x y
abbrev entropyFn (c x : Fin d → ℝ) := GAC.lyap c x
abbrev entropyRate (N : CRN d) (κ : RxnIdx N → ℝ) (c x : Fin d → ℝ) :=
  GAC.dissip N κ c x

/-- The exact fields displayed in Section 4.2 of the paper. -/
structure DBCondition (N : CRN d) (κ : RxnIdx N → ℝ) (c : Fin d → ℝ) : Prop where
  hRev : HasReverses N
  hPos : InOpenOrthant c
  hEq : ∀ e : RxnIdx N,
    κ e * xPow c e.val.1 = κ (oppRxn hRev e) * xPow c e.val.2

theorem DBCondition.toDetailedBalanced {N : CRN d} {κ : RxnIdx N → ℝ} {c : Fin d → ℝ}
    (h : DBCondition N κ c) : GAC.IsDetailedBalanced N κ c :=
  ⟨h.hRev, h.hPos, h.hEq⟩

theorem DBCondition.ofDetailedBalanced {N : CRN d} {κ : RxnIdx N → ℝ} {c : Fin d → ℝ}
    (h : GAC.IsDetailedBalanced N κ c) : DBCondition N κ c :=
  ⟨h.reversible, h.pos, h.balance⟩

theorem dbCondition_iff {N : CRN d} {κ : RxnIdx N → ℝ} {c : Fin d → ℝ} :
    DBCondition N κ c ↔ GAC.IsDetailedBalanced N κ c :=
  ⟨DBCondition.toDetailedBalanced, DBCondition.ofDetailedBalanced⟩

/-- Lemma 2.3. -/
theorem strongConn_of_hasReverses {N : CRN d} (h : HasReverses N) : WeaklyReversible N :=
  GAC.weaklyReversible_of_reversible h

/-- Theorem 3.1, with existence and one bound for all solutions from `x0`. -/
theorem wr_trajectory_compact_interior
    (N : CRN d) (κ : RxnIdx N → ℝ) (hd : 0 < d)
    (hWR : WeaklyReversible N) (hκ : ∀ e, 0 < κ e)
    (x0 : Fin d → ℝ) (hx0 : InOpenOrthant x0) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (∃ x : ℝ → Fin d → ℝ, SolvesForward N κ x0 x) ∧
      ∀ x : ℝ → Fin d → ℝ, SolvesForward N κ x0 x →
        ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹ :=
  bounded_persistent_of_weaklyReversible d N κ hd hWR hκ x0 hx0

/-- Proposition 3.5, including arbitrary positive tolerances and every tie. -/
theorem uniform_affine_approximation : Barrier.UniformAffineApproximation d :=
  Affine.uniform_data_of_full_certificates
    (fun E hE => Affine.exists_full_certificate d (-1) 1 E (by norm_num)
      (fun r _ => hE r))

/-- Proposition 3.6. The approximation premise is discharged here. -/
theorem exists_minBarrierSpec (N : CRN d) (κ : RxnIdx N → ℝ)
    (hWR : WeaklyReversible N) (hκ : ∀ e, 0 < κ e)
    (x0 : Fin d → ℝ) (hx0 : InOpenOrthant x0) :
    Nonempty (Barrier.BarrierData N κ x0) :=
  Barrier.exists_barrier_data uniform_affine_approximation
    N κ hWR hκ x0 hx0

/-- Lemma 3.14. -/
theorem trajectory_in_coset {N : CRN d} {κ : RxnIdx N → ℝ}
    {x0 : Fin d → ℝ} {x : ℝ → Fin d → ℝ} (hx : SolvesForward N κ x0 x)
    {t : ℝ} (ht : 0 ≤ t) : x t - x0 ∈ reactionSpan N :=
  GAC.sol_mem_class hx ht

/-- Lemma 3.16(a). -/
theorem entropyFn_ge_zero {c x : Fin d → ℝ}
    (hc : InOpenOrthant c) (hx : InOpenOrthant x) : 0 ≤ entropyFn c x :=
  GAC.lyap_nonneg hc hx

/-- Lemma 3.16(b). -/
theorem entropyFn_deriv {N : CRN d} {κ : RxnIdx N → ℝ} {c : Fin d → ℝ}
    {x : ℝ → Fin d → ℝ} {t : ℝ}
    (hx : HasDerivAt x (rateField N κ (x t)) t) (hp : InOpenOrthant (x t)) :
    HasDerivAt (fun s => entropyFn c (x s)) (entropyRate N κ c (x t)) t :=
  GAC.hasDerivAt_lyap hx hp

/-- Lemma 3.16(c), as continuity on the positive orthant. -/
theorem entropyRate_continuous (N : CRN d) (κ : RxnIdx N → ℝ) (c : Fin d → ℝ) :
    ContinuousOn (entropyRate N κ c) {x | InOpenOrthant x} :=
  fun _ hx => (GAC.continuousAt_dissip κ c hx).continuousWithinAt

/-- Lemma 3.17, the paired dissipation identity. -/
theorem entropyRate_double {N : CRN d} {κ : RxnIdx N → ℝ} {c x : Fin d → ℝ}
    (hDB : DBCondition N κ c) (hx : InOpenOrthant x) :
    2 * entropyRate N κ c x = ∑ e : RxnIdx N, (κ e * xPow c e.val.1) *
      ((logQuot c x e.val.2 - logQuot c x e.val.1) *
        (Real.exp (logQuot c x e.val.1) - Real.exp (logQuot c x e.val.2))) :=
  GAC.two_dissip hDB.toDetailedBalanced hx

theorem entropyRate_le_zero {N : CRN d} {κ : RxnIdx N → ℝ} {c x : Fin d → ℝ}
    (hκ : ∀ e, 0 < κ e) (hDB : DBCondition N κ c) (hx : InOpenOrthant x) :
    entropyRate N κ c x ≤ 0 :=
  GAC.dissip_nonpos hκ hDB.toDetailedBalanced hx

/-- Lemma 3.18, zero dissipation forces all logarithmic gaps to vanish. -/
theorem logGap_vanish_of_rate_zero {N : CRN d} {κ : RxnIdx N → ℝ} {c x : Fin d → ℝ}
    (hκ : ∀ e, 0 < κ e) (hDB : DBCondition N κ c) (hx : InOpenOrthant x)
    (h0 : entropyRate N κ c x = 0) :
    ∀ e : RxnIdx N, logQuot c x e.val.1 = logQuot c x e.val.2 :=
  GAC.gap_zero_of_dissip_eq_zero hκ hDB.toDetailedBalanced hx h0

theorem rateField_zero_of_logGap {N : CRN d} {κ : RxnIdx N → ℝ} {c x : Fin d → ℝ}
    (hDB : DBCondition N κ c) (hx : InOpenOrthant x)
    (hg : ∀ e : RxnIdx N, logQuot c x e.val.1 = logQuot c x e.val.2) :
    rateField N κ x = 0 :=
  GAC.massAction_eq_zero_of_gap hDB.toDetailedBalanced hx hg

/-- Lemma 3.18 in its explicit equivalence form. -/
theorem entropyRate_eq_zero_iff {N : CRN d} {κ : RxnIdx N → ℝ} {c x : Fin d → ℝ}
    (hκ : ∀ e, 0 < κ e) (hDB : DBCondition N κ c) (hx : InOpenOrthant x) :
    entropyRate N κ c x = 0 ↔ rateField N κ x = 0 := by
  constructor
  · intro h0
    exact rateField_zero_of_logGap hDB hx (logGap_vanish_of_rate_zero hκ hDB hx h0)
  · exact GAC.dissip_eq_zero_of_massAction_eq_zero

/-- Lemma 3.19. -/
theorem unique_of_logGap {N : CRN d} {c a b : Fin d → ℝ}
    (ha : InOpenOrthant a) (hb : InOpenOrthant b)
    (hga : ∀ e : RxnIdx N, logQuot c a e.val.1 = logQuot c a e.val.2)
    (hgb : ∀ e : RxnIdx N, logQuot c b e.val.1 = logQuot c b e.val.2)
    (hab : a - b ∈ reactionSpan N) : a = b :=
  GAC.eq_of_gap_zero ha hb hga hgb hab

theorem equilibria_coincide {N : CRN d} {κ : RxnIdx N → ℝ} {c a b : Fin d → ℝ}
    (hκ : ∀ e, 0 < κ e) (hDB : DBCondition N κ c)
    (ha : InOpenOrthant a) (hb : InOpenOrthant b)
    (hfa : rateField N κ a = 0) (hfb : rateField N κ b = 0)
    (hab : a - b ∈ reactionSpan N) : a = b :=
  GAC.eq_of_equilibria hκ hDB.toDetailedBalanced ha hb hfa hfb hab

/-- Lemma 3.20. -/
theorem entropyRate_zero_at_accumulation
    {N : CRN d} {κ : RxnIdx N → ℝ} {c : Fin d → ℝ}
    (hκ : ∀ e, 0 < κ e) (hDB : DBCondition N κ c)
    {x0 : Fin d → ℝ} {ε : ℝ} (hε : 0 < ε) {x : ℝ → Fin d → ℝ}
    (hx : SolvesForward N κ x0 x)
    (hbd : ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹)
    {B : ℝ} (hB : 0 < B) (hspeed : ∀ t : ℝ, 0 ≤ t → ‖rateField N κ (x t)‖ ≤ B)
    {z : Fin d → ℝ} (hzpos : InOpenOrthant z) (hz : MapClusterPt z atTop x) :
    entropyRate N κ c z = 0 :=
  GAC.dissip_eq_zero_of_mapClusterPt hκ hDB.toDetailedBalanced hε hx hbd hB hspeed hzpos hz

/-- Theorem 3.21 / Theorem 1.1, with the statement displayed in Section 4.2. -/
theorem db_unique_equilibrium_attracts
    (N : CRN d) (κ : RxnIdx N → ℝ) (hκ : ∀ e, 0 < κ e)
    {c : Fin d → ℝ} (hDB : DBCondition N κ c)
    (x0 : Fin d → ℝ) (hx0 : InOpenOrthant x0) :
    ∃ cstar : Fin d → ℝ,
      InOpenOrthant cstar ∧ rateField N κ cstar = 0 ∧
      cstar - x0 ∈ reactionSpan N ∧
      (∀ z, InOpenOrthant z → rateField N κ z = 0 →
        z - x0 ∈ reactionSpan N → z = cstar) ∧
      (∃ x, SolvesForward N κ x0 x) ∧
      ∀ x, SolvesForward N κ x0 x → Tendsto x atTop (𝓝 cstar) :=
  GAC.detailed_balanced_global_convergence N κ hκ hDB.toDetailedBalanced x0 hx0

end GAC.Paper
