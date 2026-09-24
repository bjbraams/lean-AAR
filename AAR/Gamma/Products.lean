/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Infinite products (DLMF §5.8)

The Weierstrass product 5.8.2 is `one_div_Gamma_eq_tprod` in `Basic.lean`.
Gauss's limit 5.8.1 is Mathlib `GammaSeq_tendsto_Gamma`. The remaining
identities are the modulus product and the general balanced Gamma product.
-/

@[expose] public section

open Complex Filter
open scoped Topology Real

noncomputable section

namespace AAR.Gamma

@[dlmf 5.8.E3]
theorem Gamma_div_Gamma_add_mul_I_sq {x y : ℝ} (hx : ∀ k : ℕ, (x : ℂ) ≠ -k) :
    ‖(Real.Gamma x : ℂ) / Complex.Gamma (x + I * y)‖ ^ 2 =
      ∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2) := by
  sorry

@[dlmf 5.8.E5]
theorem Gamma_balanced_product {m : ℕ} (hm : 0 < m) (a b : Fin m → ℂ)
    (hsum : ∑ k : Fin m, a k = ∑ k : Fin m, b k)
    (hb : ∀ k : Fin m, ∀ n : ℕ, b k ≠ -n) :
    ∏' n : ℕ, (∏ k : Fin m, (a k + n)) / (∏ k : Fin m, (b k + n)) =
      (∏ k : Fin m, Complex.Gamma (b k)) / (∏ k : Fin m, Complex.Gamma (a k)) := by
  sorry

end AAR.Gamma
