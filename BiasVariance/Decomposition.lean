/-
# The bias–variance decomposition

Setting (at a fixed test input `x₀`):

* `f₀ = f(x₀)` is the true regression value (a constant);
* the observed response is `Y = f₀ + ε`, where `ε` is noise with `E[ε] = 0`
  and `Var[ε] = σ²`;
* `f̂(x₀)` is the prediction of a model fitted on a random training set, so it
  is itself a random variable.

Main results:

* `bias_variance_of_uncorrelated` : on any finite probability space, if
  `E[ε] = 0` and `E[f̂ ε] = E[f̂] E[ε]`, then
  `E[(Y - f̂)²] = (E[f̂] - f₀)² + Var[f̂] + Var[ε]`.
* `mse_eq_bias_sq_add_var` : `E[(f̂ - f₀)²] = Bias[f̂]² + Var[f̂]`.
* `bias_variance_decomposition` : the textbook theorem, with the training data
  `T ∼ P_T` and the noise `ε ∼ P_ε` independent (product distribution):
  `E_{T,ε}[(f₀ + ε - f̂_T(x₀))²] = Bias² + Var_T[f̂_T(x₀)] + σ²`.

No axioms are introduced; only standard Lean/mathlib foundations are used.
-/
import BiasVariance.FinProb

namespace BiasVariance

open FinProb

variable {Ω : Type*} [Fintype Ω]

/-- Bias of a (random) prediction `f̂` for the target value `f₀`. -/
def bias (P : FinProb Ω) (fhat : Ω → ℝ) (f₀ : ℝ) : ℝ := P.E fhat - f₀

/-- **Bias–variance decomposition of the estimation error**:
`E[(f̂ - f₀)²] = Bias[f̂]² + Var[f̂]`. -/
theorem mse_eq_bias_sq_add_var (P : FinProb Ω) (fhat : Ω → ℝ) (f₀ : ℝ) :
    P.E (fun ω => (fhat ω - f₀) ^ 2) = (bias P fhat f₀) ^ 2 + P.Var fhat := by
  have h : (fun ω => (fhat ω - f₀) ^ 2)
      = fun ω => f₀ ^ 2 + (-2 * f₀) * fhat ω + 0 * fhat ω + 1 * fhat ω ^ 2
          + 0 * fhat ω ^ 2 + 0 * (fhat ω * fhat ω) := by
    funext ω; ring
  rw [h, E_quad, var_eq, bias]
  ring

/-- **Bias–variance decomposition of the expected prediction error**
(general form). On a finite probability space, let `f̂` be the prediction and
`ε` the noise, with `E[ε] = 0` and `f̂`, `ε` uncorrelated. Then for
`Y = f₀ + ε`,
`E[(Y - f̂)²] = (E[f̂] - f₀)² + Var[f̂] + Var[ε]`. -/
theorem bias_variance_of_uncorrelated (P : FinProb Ω) (f₀ : ℝ) (fhat ε : Ω → ℝ)
    (hε : P.E ε = 0)
    (hunc : P.E (fun ω => fhat ω * ε ω) = P.E fhat * P.E ε) :
    P.E (fun ω => (f₀ + ε ω - fhat ω) ^ 2)
      = (bias P fhat f₀) ^ 2 + P.Var fhat + P.Var ε := by
  have h : (fun ω => (f₀ + ε ω - fhat ω) ^ 2)
      = fun ω => f₀ ^ 2 + (-2 * f₀) * fhat ω + (2 * f₀) * ε ω + 1 * fhat ω ^ 2
          + 1 * ε ω ^ 2 + (-2) * (fhat ω * ε ω) := by
    funext ω; ring
  rw [h, E_quad, var_eq P fhat, var_eq P ε, hunc, hε, bias]
  ring

/-- **Bias–variance decomposition (independent training data and noise).**
Let `P_T` be the distribution of the training set on a finite space `𝒯`, and
`P_ε` the distribution of the noise on a finite space `𝒩`, drawn
independently (product distribution `P_T ⊗ P_ε`). Let `fhat : 𝒯 → ℝ` give the
prediction `f̂_T(x₀)` of the model trained on `T`, and `ε : 𝒩 → ℝ` the noise,
with `E[ε] = 0`. Then for `Y = f₀ + ε`,

`E_{T,ε}[(Y - f̂_T(x₀))²] = (E_T[f̂_T(x₀)] - f₀)² + Var_T[f̂_T(x₀)] + Var[ε]`,

i.e. expected squared error = bias² + variance + irreducible noise σ². -/
theorem bias_variance_decomposition {𝒯 𝒩 : Type*} [Fintype 𝒯] [Fintype 𝒩]
    (P_T : FinProb 𝒯) (P_ε : FinProb 𝒩) (f₀ : ℝ) (fhat : 𝒯 → ℝ) (ε : 𝒩 → ℝ)
    (hε : P_ε.E ε = 0) :
    (P_T.prod P_ε).E (fun x => (f₀ + ε x.2 - fhat x.1) ^ 2)
      = (bias P_T fhat f₀) ^ 2 + P_T.Var fhat + P_ε.Var ε := by
  have hε' : (P_T.prod P_ε).E (fun x => ε x.2) = 0 := by
    rw [E_prod_snd]; exact hε
  have hunc : (P_T.prod P_ε).E (fun x => fhat x.1 * ε x.2)
      = (P_T.prod P_ε).E (fun x => fhat x.1) * (P_T.prod P_ε).E (fun x => ε x.2) := by
    rw [E_prod_mul, E_prod_fst, E_prod_snd]
  have key := bias_variance_of_uncorrelated (P_T.prod P_ε) f₀
    (fun x => fhat x.1) (fun x => ε x.2) hε' hunc
  rw [key, Var_prod_fst, Var_prod_snd]
  simp only [bias, E_prod_fst]

end BiasVariance
