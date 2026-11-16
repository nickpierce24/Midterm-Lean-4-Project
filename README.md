# Bias–Variance Decomposition in Lean 4

STAT 4052 (Fall 2026) midterm Lean 4 project.
**Authors:** Arielle Aceves, Milena Yared, Henry O'Conor, Nick Pierce.

## Goal

Formally verify the **bias–variance decomposition** of the expected squared
prediction error: at a fixed test input `x₀`, with true value `f₀ = f(x₀)`,
response `Y = f₀ + ε` and a prediction `f̂_T(x₀)` from a model trained on a
random training set `T` drawn independently of the noise `ε` (with `E[ε] = 0`),

```
E_{T,ε}[(Y − f̂_T(x₀))²] = (E_T[f̂_T(x₀)] − f₀)²  +  Var_T[f̂_T(x₀)]  +  Var[ε]
                           \_______ bias² ______/    \___ variance ___/   \_ σ² _/
```

The formalization works on **finite probability spaces** (probability mass
functions on finite types), where expectations are finite weighted sums.
Independence of training data and noise is modelled by the product
distribution `P_T ⊗ P_ε`.

## Main results

| Lean name | Statement |
|---|---|
| `BiasVariance.bias_variance_decomposition` | Main theorem above, with `T ∼ P_T` and `ε ∼ P_ε` independent (product distribution) and `E[ε] = 0`. |
| `BiasVariance.bias_variance_of_uncorrelated` | Same identity on any finite probability space, assuming only `E[ε] = 0` and `E[f̂ ε] = E[f̂] E[ε]`. |
| `BiasVariance.mse_eq_bias_sq_add_var` | `E[(f̂ − f₀)²] = Bias[f̂]² + Var[f̂]`. |
| `BiasVariance.FinProb.E_prod_mul` | Independence ⇒ uncorrelated: `E[g(T) h(ε)] = E[g] E[h]` under `P_T ⊗ P_ε`. |

## External inputs

**None.** No additional external axioms are used beyond the stated theorem
hypotheses and the standard Lean/mathlib foundations. The development contains
no `axiom`, `sorry` or `admit`. You can confirm this with
`#print axioms BiasVariance.bias_variance_decomposition`, which reports only
Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Files

- `BiasVariance/FinProb.lean`: finite probability spaces (`FinProb`), expectation `E`,
  variance `Var`, linearity of expectation, `Var X = E[X²] − E[X]²`, product
  (independent) distributions and marginalisation lemmas.
- `BiasVariance/Decomposition.lean`: `bias` and the three decomposition theorems.
- `BiasVariance.lean`: root module.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: Lean version
  (`leanprover/lean4:v4.36.0`) and pinned dependencies (mathlib `v4.36.0`).

## Build instructions

1. Install Lean via [elan](https://github.com/leanprover/elan) (the toolchain in
   `lean-toolchain` is downloaded automatically).
2. Clone and build:

   ```bash
   git clone https://github.com/nickpierce24/Midterm-Lean-4-Project.git
   cd Midterm-Lean-4-Project
   lake exe cache get   # download precompiled mathlib (recommended, saves hours)
   lake build
   ```

A successful build ends with `Build completed successfully` and no errors.
`lake exe cache get` is optional; without it, `lake build` compiles the needed
part of mathlib from source (about 1,400 files).

## AI disclosure

Claude (Anthropic) was used to suggest the project idea, write the Lean
formalization and draft this README and the report. The authors reviewed the
theorem statements, assumptions and conclusions.
