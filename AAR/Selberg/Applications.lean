/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Classical
public import AAR.Selberg.Basic
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.NumberTheory.GaussSum
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Trace.Defs

/-!
# Applications of the Selberg integral (AAR §§8.5–8.11)

Stieltjes electrostatics, Siegel's inequality, Dyson's constant-term identity, the
Hasse–Davenport relation for Gauss sums (Mathlib already defines `gaussSum`), and the
finite-field analogue of Selberg.
-/

@[expose] public section

open Complex
open scoped Real Nat

noncomputable section

/-- The product of squared differences of the Jacobi roots, AAR Theorem 8.5.3,
p. 418. This is the discriminant of the monic normalization of `P_n^{(α,β)}`. -/
theorem jacobiP_discriminant {α β : ℝ} {n : ℕ} (hn : n ≠ 0)
    (hα : -1 < α) (hβ : -1 < β) (x : Fin n → ℝ)
    (hroot : ∀ i, jacobiP α β n (x i) = 0) (hinj : Function.Injective x) :
    (Finset.univ.prod fun i : Fin n => Finset.univ.prod fun j : Fin n =>
      if i.val < j.val then ((x i - x j : ℝ) : ℂ) ^ (2 : ℕ) else (1 : ℂ)) =
      (2 : ℂ) ^ (n * (n - 1)) *
        Finset.univ.prod fun j : Fin n =>
          ((j : ℂ) + 1) ^ (j.val + 1) *
            ((j : ℂ) + 1 + α) ^ j.val *
            ((j : ℂ) + 1 + β) ^ j.val /
            ((n : ℂ) + j + 1 + α + β) ^ (n + j.val - 1) := by
  sorry

/-- The polynomial `P_n(t)` in AAR (8.6.2), p. 420. -/
def siegelP (n : ℕ) (t : ℝ) : ℝ :=
  1 / (n.factorial : ℝ) *
    ∏ k ∈ Finset.range (n - 1), ((t + k) / ((n : ℝ) - k)) ^ (n - k - 1)

/-- The rational function `Q_n(t)` in AAR (8.6.3), p. 420. -/
def siegelQ (n : ℕ) (t : ℝ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 (n - 1), (1 + ((n : ℝ) - k) / (t + k - 1))

/-- The squared Vandermonde product `Δ` used in AAR §8.6, p. 420. -/
def siegelDiscriminant {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i.val < j.val then (x i - x j) ^ 2 else 1

/-- Siegel's refinement of the arithmetic–geometric mean inequality, AAR Theorem 8.6.2,
p. 420. The positive parameter `μ` satisfies (8.6.4). -/
theorem siegel_inequality {n : ℕ} (hn : 2 ≤ n) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) (hΔ : siegelDiscriminant x ≠ 0)
    {μ : ℝ} (hμ : 0 < μ)
    (hroot : siegelP n μ = (∏ i, x i) ^ (n - 1) / siegelDiscriminant x) :
    (∏ i, x i) * siegelQ n μ ≤ ((∑ i, x i) / (n : ℝ)) ^ n := by
  sorry

/-- For two distinct positive numbers, Siegel's bound is an equality. In fact only
the nonzero discriminant, nonzero parameter, and defining equation are needed. -/
theorem siegel_inequality_two {x : Fin 2 → ℝ} {μ : ℝ}
    (hΔ : siegelDiscriminant x ≠ 0) (hμ : μ ≠ 0)
    (hroot : siegelP 2 μ = (∏ i, x i) / siegelDiscriminant x) :
    (∏ i, x i) * siegelQ 2 μ = ((∑ i, x i) / 2) ^ 2 := by
  have hd : (x 0 - x 1) ^ 2 ≠ 0 := by
    simpa [siegelDiscriminant, Fin.prod_univ_two] using hΔ
  norm_num [siegelP, siegelDiscriminant, Fin.prod_univ_two] at hroot
  norm_num [siegelQ, Fin.prod_univ_two, Fin.sum_univ_two]
  field_simp [hd] at hroot
  rw [eq_div_iff hd] at hroot
  field_simp [hμ]
  nlinarith [hroot]

/-- The complex factorial quotient equals the corresponding multinomial coefficient.
This is an algebraic ingredient for Dyson's identity; it does not compute a Laurent
polynomial constant term. -/
theorem factorial_sum_div_prod_factorial {n : ℕ} (a : Fin n → ℕ) :
    ((∑ i, a i).factorial : ℂ) / ∏ i, (a i).factorial = Nat.multinomial Finset.univ a := by
  -- Already known in Mathlib as `Nat.multinomial_spec`.
  have hden : (∏ i, ((a i).factorial : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Nat.cast_ne_zero.mpr (a i).factorial_ne_zero
  rw [Nat.cast_prod]
  apply (div_eq_iff hden).mpr
  have h := congrArg (fun k : ℕ => (k : ℂ)) (Nat.multinomial_spec Finset.univ a)
  simpa [Nat.cast_mul, Nat.cast_prod, mul_comm] using h.symm

/-- A terminating nearly poised `₃F₂(1)` evaluation, AAR Theorem 8.9.1(a), p. 429.
Positive real parts suffice to keep all denominators in the finite sum nonzero.

The supplied AAR printing has an error: the last denominator factor is printed
as `(α)_{2k}`, but must be `(α + 1)_{2k}`. For `k = 1`, `α = 1/2`, `β = 1`,
the finite sum is `8/15`, whereas the printed right-hand side is `8/3`.
The corrected formula also appears as equation (20) in Nagar, Naranjo-Ríos and
Gupta, "Generalized Selberg Integral and Nearly Poised 3F2 Series" (2015). -/
theorem nearly_poised_3F2 {α β : ℂ} (k : ℕ)
    (hα : 0 < α.re) (hβ : 0 < β.re) :
    (∑ r ∈ Finset.range (2 * k + 1),
      poch (-(2 * k : ℂ)) r * poch α r * poch (-α - β - 2 * k) r /
        (poch (-α - 2 * k) r * poch (α + β) r * (r.factorial : ℂ))) =
      poch (α + 1) k * poch β k * poch 1 (2 * k) /
        (poch (α + β) k * poch 1 k * poch (α + 1) (2 * k)) := by
  sorry

/-- The Hasse–Davenport lifting relation, AAR Theorem 8.10.4, p. 432.
The sum on `E` uses the norm lift of `χ` and the trace lift of `ψ`, as in
(8.10.5)–(8.10.6). The extension degree `Module.finrank F E` is positive.
Over a finite field, nontriviality of the additive character is sufficient;
the identity also allows the trivial multiplicative character. -/
theorem hasse_davenport {F E : Type*} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] [FiniteDimensional F E]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) :
    (∑ x : E, χ (Algebra.norm F x) * ψ (Algebra.trace F E x)) =
      (-1 : ℂ) ^ (Module.finrank F E - 1) * gaussSum χ ψ ^ Module.finrank F E := by
  sorry

/-- The monic polynomial with a specified vector of lower coefficients. -/
def selbergMonicPolynomial {F : Type*} [Field F] {n : ℕ} (v : Fin n → F) : Polynomial F :=
  Polynomial.X ^ n + ∑ i, Polynomial.C (v i) * Polynomial.X ^ (i : ℕ)

/-- Finite-field Selberg evaluation, AAR Theorem 8.11.2, with the sum (8.11.7).
AAR §8.10 specifies only a nontrivial multiplicative character, but §8.11 uses
`χ^((q-1)/2)` as the quadratic character and tests exponents modulo `q-1`.
Here `χ` is required to have order `q-1`, as needed for those uses. -/
theorem selberg_finite_field {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : orderOf χ = Fintype.card F - 1) (hψ : ψ.IsPrimitive)
    (hodd : Odd (Fintype.card F)) {n a b c : ℕ}
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hparams : ∀ j : Fin n,
      ¬(Fintype.card F - 1) ∣ (a + (j : ℕ) * c) ∧
      ¬(Fintype.card F - 1) ∣ (b + (j : ℕ) * c) ∧
      ¬(Fintype.card F - 1) ∣ (((j : ℕ) + 1) * c)) :
    (∑ v : Fin n → F,
      let f := selbergMonicPolynomial v
      χ ((-1 : F) ^ (n * a) * f.eval 0 ^ a * f.eval 1 ^ b * f.discr ^ c) *
        (χ ^ ((Fintype.card F - 1) / 2)) f.discr) =
      let gstar := fun m : ℕ => (Fintype.card F : ℂ) / gaussSum ((χ ^ m)⁻¹) ψ
      ∏ j : Fin n,
        gstar (a + (j : ℕ) * c) * gstar (b + (j : ℕ) * c) * gstar (((j : ℕ) + 1) * c) /
          (gstar (a + b + (n - 1 + j : ℕ) * c) * gstar c) := by
  sorry
