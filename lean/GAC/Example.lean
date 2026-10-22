import GAC.DetailedBalance

/-!
# Non-vacuity check: `A ⇌ B`

A concrete detailed balanced network, confirming that the hypotheses of `IsDetailedBalanced` can be met
and that the main theorem can be instantiated.
-/

open GAC.Persistence

namespace GAC.Example

/-- The complexes `A = (1,0)` and `B = (0,1)`. -/
def cA : Fin 2 → ℕ := ![1, 0]
def cB : Fin 2 → ℕ := ![0, 1]

/-- The network `A ⇌ B`. -/
def net : ReactionNetwork 2 where
  complexes := {cA, cB}
  reactions := {(cA, cB), (cB, cA)}
  source_mem := by decide
  target_mem := by decide
  source_ne_target := by decide

/-- Both rate constants equal 1. -/
def rate : Reaction net → ℝ := fun _ => 1

lemma monomial_one (y : Fin 2 → ℕ) : monomial (fun _ => (1 : ℝ)) y = 1 := by
  simp [monomial]

theorem net_detailed_balanced : IsDetailedBalanced net rate (fun _ => 1) where
  reversible := by
    show ∀ e ∈ net.reactions, (e.2, e.1) ∈ net.reactions
    decide
  pos := fun _ => one_pos
  balance := fun e => by simp [rate, monomial_one]

/-- The main theorem for `A ⇌ B`: every positive trajectory converges to the unique positive equilibrium of its class. -/
theorem convergence (x0 : Fin 2 → ℝ) (hx0 : PositiveState x0) :
    ∃ xbar : Fin 2 → ℝ,
      PositiveState xbar ∧ massAction net rate xbar = 0 ∧ xbar - x0 ∈ stoichSubspace net ∧
      (∀ z : Fin 2 → ℝ, PositiveState z → massAction net rate z = 0 →
        z - x0 ∈ stoichSubspace net → z = xbar) ∧
      (∃ x : ℝ → (Fin 2 → ℝ), IsGlobalForwardSolution net rate x0 x) ∧
      ∀ x : ℝ → (Fin 2 → ℝ), IsGlobalForwardSolution net rate x0 x →
        Filter.Tendsto x Filter.atTop (nhds xbar) :=
  detailed_balanced_global_convergence net rate (fun _ => one_pos) net_detailed_balanced x0 hx0

end GAC.Example
