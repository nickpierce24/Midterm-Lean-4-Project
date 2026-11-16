/-
# Finite probability spaces: expectation, variance, independence

We work on a finite sample space `Ω` carrying a probability mass function.
A random variable is any function `X : Ω → ℝ`; its expectation is the
weighted sum `E[X] = ∑ ω, p ω * X ω`.

Independence of two sources of randomness (training data and noise) is
modelled by the product distribution on `Ω₁ × Ω₂`, with mass
`p (ω₁, ω₂) = p₁ ω₁ * p₂ ω₂`.

No axioms are introduced in this development.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset

namespace BiasVariance

/-- A probability mass function on a finite sample space. -/
structure FinProb (Ω : Type*) [Fintype Ω] where
  /-- probability mass of each outcome -/
  p : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ p ω
  sum_one : ∑ ω, p ω = 1

namespace FinProb

variable {Ω : Type*} [Fintype Ω] (P : FinProb Ω)

/-- Expectation `E[X] = ∑ ω, p(ω) X(ω)`. -/
def E (X : Ω → ℝ) : ℝ := ∑ ω, P.p ω * X ω

/-- Variance `Var[X] = E[(X - E[X])²]`. -/
def Var (X : Ω → ℝ) : ℝ := P.E (fun ω => (X ω - P.E X) ^ 2)

/-- Expectation of a constant. -/
lemma E_const (c : ℝ) : P.E (fun _ => c) = c := by
  unfold E
  rw [← sum_mul, P.sum_one, one_mul]

/-- **Linearity of expectation** for quadratic polynomials in two random
variables `X, Y` with constant coefficients. -/
lemma E_quad (X Y : Ω → ℝ) (a b c d e g : ℝ) :
    P.E (fun ω => a + b * X ω + c * Y ω + d * X ω ^ 2 + e * Y ω ^ 2 + g * (X ω * Y ω))
      = a + b * P.E X + c * P.E Y + d * P.E (fun ω => X ω ^ 2)
          + e * P.E (fun ω => Y ω ^ 2) + g * P.E (fun ω => X ω * Y ω) := by
  unfold E
  have h : ∀ ω, P.p ω * (a + b * X ω + c * Y ω + d * X ω ^ 2 + e * Y ω ^ 2 + g * (X ω * Y ω))
      = a * P.p ω + b * (P.p ω * X ω) + c * (P.p ω * Y ω) + d * (P.p ω * X ω ^ 2)
          + e * (P.p ω * Y ω ^ 2) + g * (P.p ω * (X ω * Y ω)) := fun ω => by ring
  simp only [h, sum_add_distrib, ← mul_sum, P.sum_one]
  ring

/-- `Var[X] = E[X²] - E[X]²`. -/
lemma var_eq (X : Ω → ℝ) : P.Var X = P.E (fun ω => X ω ^ 2) - (P.E X) ^ 2 := by
  unfold Var
  have h : (fun ω => (X ω - P.E X) ^ 2)
      = fun ω => (P.E X) ^ 2 + (-2 * P.E X) * X ω + 0 * X ω + 1 * X ω ^ 2
          + 0 * X ω ^ 2 + 0 * (X ω * X ω) := by
    funext ω; ring
  rw [h, E_quad]
  ring

/-! ### Product (independent) distributions -/

variable {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]

/-- The product distribution `P₁ ⊗ P₂` on `Ω₁ × Ω₂`: the two coordinates are
independent with marginals `P₁` and `P₂`. -/
def prod (P₁ : FinProb Ω₁) (P₂ : FinProb Ω₂) : FinProb (Ω₁ × Ω₂) where
  p x := P₁.p x.1 * P₂.p x.2
  nonneg x := mul_nonneg (P₁.nonneg x.1) (P₂.nonneg x.2)
  sum_one := by
    rw [Fintype.sum_prod_type, ← Fintype.sum_mul_sum, P₁.sum_one, P₂.sum_one, one_mul]

variable (P₁ : FinProb Ω₁) (P₂ : FinProb Ω₂)

/-- Expectation under the product distribution factorises as a double sum. -/
lemma E_prod (F : Ω₁ × Ω₂ → ℝ) :
    (P₁.prod P₂).E F = ∑ ω₁, ∑ ω₂, P₁.p ω₁ * P₂.p ω₂ * F (ω₁, ω₂) := by
  unfold E prod
  rw [Fintype.sum_prod_type]

/-- A random variable depending only on the first coordinate has the same
expectation under `P₁ ⊗ P₂` as under `P₁` (marginalisation). -/
lemma E_prod_fst (g : Ω₁ → ℝ) : (P₁.prod P₂).E (fun x => g x.1) = P₁.E g := by
  rw [E_prod]
  unfold E
  refine sum_congr rfl fun ω₁ _ => ?_
  calc ∑ ω₂, P₁.p ω₁ * P₂.p ω₂ * g ω₁ = ∑ ω₂, (P₁.p ω₁ * g ω₁) * P₂.p ω₂ :=
        sum_congr rfl fun ω₂ _ => by ring
    _ = P₁.p ω₁ * g ω₁ := by rw [← mul_sum, P₂.sum_one, mul_one]

/-- Marginalisation for a random variable depending only on the second coordinate. -/
lemma E_prod_snd (h : Ω₂ → ℝ) : (P₁.prod P₂).E (fun x => h x.2) = P₂.E h := by
  rw [E_prod]
  unfold E
  calc ∑ ω₁, ∑ ω₂, P₁.p ω₁ * P₂.p ω₂ * h ω₂
      = ∑ ω₁, P₁.p ω₁ * ∑ ω₂, P₂.p ω₂ * h ω₂ :=
        sum_congr rfl fun ω₁ _ => by rw [mul_sum]; exact sum_congr rfl fun ω₂ _ => by ring
    _ = ∑ ω₂, P₂.p ω₂ * h ω₂ := by rw [← sum_mul, P₁.sum_one, one_mul]

/-- **Independence ⇒ uncorrelatedness**: under `P₁ ⊗ P₂`,
`E[g(ω₁) h(ω₂)] = E[g] E[h]`. -/
lemma E_prod_mul (g : Ω₁ → ℝ) (h : Ω₂ → ℝ) :
    (P₁.prod P₂).E (fun x => g x.1 * h x.2) = P₁.E g * P₂.E h := by
  rw [E_prod]
  unfold E
  rw [Fintype.sum_mul_sum]
  exact sum_congr rfl fun ω₁ _ => sum_congr rfl fun ω₂ _ => by ring

lemma Var_prod_fst (g : Ω₁ → ℝ) : (P₁.prod P₂).Var (fun x => g x.1) = P₁.Var g := by
  unfold Var
  rw [E_prod_fst]
  exact E_prod_fst P₁ P₂ (fun ω₁ => (g ω₁ - P₁.E g) ^ 2)

lemma Var_prod_snd (h : Ω₂ → ℝ) : (P₁.prod P₂).Var (fun x => h x.2) = P₂.Var h := by
  unfold Var
  rw [E_prod_snd]
  exact E_prod_snd P₁ P₂ (fun ω₂ => (h ω₂ - P₂.E h) ^ 2)

end FinProb

end BiasVariance
