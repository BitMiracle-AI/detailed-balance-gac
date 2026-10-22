import GAC.Paper

/-!
# Section 5.1: A + B ⇌ C and 2A ⇌ B

The rate constants are 2, 1, 1, 1/2 in the directions displayed in the paper.
The state (1/2, 1/2, 1/2) is detailed balanced and has conserved total 3.
These exact statements and the application of the convergence theorem are
formalized here. Numerical integration and the plotted curves are not proofs.
-/

open Filter Topology GAC.Persistence

noncomputable section

namespace GAC.PaperExample

def cAB : Fin 3 → ℕ := ![1, 1, 0]
def cC : Fin 3 → ℕ := ![0, 0, 1]
def c2A : Fin 3 → ℕ := ![2, 0, 0]
def cB : Fin 3 → ℕ := ![0, 1, 0]

def net : ReactionNetwork 3 where
  complexes := {cAB, cC, c2A, cB}
  reactions := {(cAB, cC), (cC, cAB), (c2A, cB), (cB, c2A)}
  source_mem := by decide
  target_mem := by decide
  source_ne_target := by decide

noncomputable def rate (e : Reaction net) : ℝ :=
  if e.val = (cAB, cC) then 2 else if e.val = (cB, c2A) then 1 / 2 else 1

def equilibrium : Fin 3 → ℝ := ![1 / 2, 1 / 2, 1 / 2]

theorem rate_pos (e : Reaction net) : 0 < rate e := by
  unfold rate
  split_ifs <;> norm_num

theorem equilibrium_pos : PositiveState equilibrium := by
  intro i
  fin_cases i <;> norm_num [equilibrium]

theorem net_reversible : IsReversible net := by
  intro e he
  simp only [net, Finset.mem_insert, Finset.mem_singleton] at he ⊢
  rcases he with h | h | h | h <;> simp [h]

theorem net_detailed_balanced : IsDetailedBalanced net rate equilibrium where
  reversible := net_reversible
  pos := equilibrium_pos
  balance := by
    intro e
    have he := e.property
    simp only [net, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h | h <;>
      norm_num [rate, revR, h, monomial, equilibrium, cAB, cC, c2A, cB,
        Fin.prod_univ_succ]

theorem equilibrium_is_equilibrium : massAction net rate equilibrium = 0 := by
  apply massAction_eq_zero_of_gap net_detailed_balanced equilibrium_pos
  intro e
  simp [logRatio]

def total (x : Fin 3 → ℝ) : ℝ := x 0 + 2 * x 1 + 3 * x 2

theorem equilibrium_total : total equilibrium = 3 := by
  norm_num [total, equilibrium]

def totalMap : (Fin 3 → ℝ) →ₗ[ℝ] ℝ where
  toFun := total
  map_add' x y := by simp only [total, Pi.add_apply]; ring
  map_smul' a x := by simp only [total, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem total_reactionVector (e : Reaction net) : total (reactionVector e) = 0 := by
  have he := e.property
  simp only [net, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with h | h | h | h <;>
    norm_num [total, reactionVector, h, cAB, cC, c2A, cB]

theorem stoich_total_zero {v : Fin 3 → ℝ} (hv : v ∈ stoichSubspace net) : total v = 0 := by
  have hS : stoichSubspace net ≤ LinearMap.ker totalMap := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨e, rfl⟩
    exact total_reactionVector e
  exact hS hv

theorem total_conserved (x0 : Fin 3 → ℝ) (x : ℝ → Fin 3 → ℝ)
    (hx : IsGlobalForwardSolution net rate x0 x) {t : ℝ} (ht : 0 ≤ t) :
    total (x t) = total x0 := by
  have hz := stoich_total_zero (sol_mem_class hx ht)
  change totalMap (x t - x0) = 0 at hz
  rw [map_sub] at hz
  exact sub_eq_zero.mp hz

def reaction1 : Reaction net := ⟨(cAB, cC), by simp [net]⟩
def reaction2 : Reaction net := ⟨(c2A, cB), by simp [net]⟩

/-- The total-3 condition used in Figure 1 implies membership in the same
stoichiometric class as the displayed equilibrium. -/
theorem equilibrium_mem_class_of_total_eq_three (x0 : Fin 3 → ℝ)
    (htotal : total x0 = 3) : equilibrium - x0 ∈ stoichSubspace net := by
  have h1 : reactionVector reaction1 ∈ stoichSubspace net :=
    Submodule.subset_span ⟨reaction1, rfl⟩
  have h2 : reactionVector reaction2 ∈ stoichSubspace net :=
    Submodule.subset_span ⟨reaction2, rfl⟩
  have hlin : equilibrium - x0 =
      (equilibrium 2 - x0 2) • reactionVector reaction1 +
      ((equilibrium 1 - x0 1) + (equilibrium 2 - x0 2)) • reactionVector reaction2 := by
    unfold total at htotal
    funext i
    fin_cases i <;>
      norm_num [reactionVector, reaction1, reaction2, cAB, cC, c2A, cB, equilibrium] <;>
      linarith
  rw [hlin]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h1) (Submodule.smul_mem _ _ h2)

/-- Every positive initial state has a unique attracting equilibrium in its class. -/
theorem convergence (x0 : Fin 3 → ℝ) (hx0 : PositiveState x0) :
    ∃ xbar : Fin 3 → ℝ,
      PositiveState xbar ∧ massAction net rate xbar = 0 ∧
      xbar - x0 ∈ stoichSubspace net ∧
      (∀ z : Fin 3 → ℝ, PositiveState z → massAction net rate z = 0 →
        z - x0 ∈ stoichSubspace net → z = xbar) ∧
      (∃ x, IsGlobalForwardSolution net rate x0 x) ∧
      ∀ x, IsGlobalForwardSolution net rate x0 x → Tendsto x atTop (𝓝 xbar) :=
  detailed_balanced_global_convergence net rate rate_pos net_detailed_balanced x0 hx0

/-- If the stated equilibrium is in the initial state's class, every solution
converges to that explicit equilibrium. -/
theorem tends_to_equilibrium (x0 : Fin 3 → ℝ) (hx0 : PositiveState x0)
    (hclass : equilibrium - x0 ∈ stoichSubspace net)
    (x : ℝ → Fin 3 → ℝ) (hx : IsGlobalForwardSolution net rate x0 x) :
    Tendsto x atTop (𝓝 equilibrium) := by
  obtain ⟨xbar, _, _, _, huniq, _, hall⟩ := convergence x0 hx0
  have heq := huniq equilibrium equilibrium_pos equilibrium_is_equilibrium hclass
  simpa only [← heq] using hall x hx

/-- The precise class and equilibrium displayed in Section 5.1. -/
theorem tends_to_equilibrium_of_total_eq_three (x0 : Fin 3 → ℝ)
    (hx0 : PositiveState x0) (htotal : total x0 = 3)
    (x : ℝ → Fin 3 → ℝ) (hx : IsGlobalForwardSolution net rate x0 x) :
    Tendsto x atTop (𝓝 equilibrium) :=
  tends_to_equilibrium x0 hx0 (equilibrium_mem_class_of_total_eq_three x0 htotal) x hx

/-- The five initial states in Figure 1, represented by exact rational numbers. -/
def figureInitialState : Fin 5 → Fin 3 → ℝ :=
  ![![2997 / 1000, 1 / 1000, 1 / 3000],
    ![1 / 1000, 1499 / 1000, 1 / 3000],
    ![1 / 1000, 11 / 50, 853 / 1000],
    ![1, 1 / 2, 1 / 3],
    ![3 / 10, 3 / 10, 7 / 10]]

theorem figure_initial_states_positive (k : Fin 5) : PositiveState (figureInitialState k) := by
  intro i
  fin_cases k <;> fin_cases i <;> norm_num [figureInitialState]

theorem figure_initial_states_total (k : Fin 5) : total (figureInitialState k) = 3 := by
  fin_cases k <;> norm_num [total, figureInitialState]

theorem figure_initial_states_converge (k : Fin 5) (x : ℝ → Fin 3 → ℝ)
    (hx : IsGlobalForwardSolution net rate (figureInitialState k) x) :
    Tendsto x atTop (𝓝 equilibrium) :=
  tends_to_equilibrium_of_total_eq_three (figureInitialState k)
    (figure_initial_states_positive k) (figure_initial_states_total k) x hx

end GAC.PaperExample
