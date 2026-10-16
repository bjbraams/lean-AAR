/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.OrthogonalPolynomials.Explicit
public import AAR.OrthogonalPolynomials.Differential
public import AAR.OrthogonalPolynomials.Series
public import AAR.OrthogonalPolynomials.Associated
public import AAR.Bessel.Basic
public import AAR.Gamma.IntegralRepresentations
public import AAR.Gamma.BetaFunction
public import AAR.Confluent.IntegralRepresentations
public import AAR.Hypergeometric.IntegralRepresentations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality
public import TauCeti.RingTheory.Polynomial.Hermite.Derivative
public import TauCeti.Analysis.SpecialFunctions.Hermite.Function.Fourier.Basic
public import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp
/-!
# Classical orthogonality, Rodrigues formulas, and integral identities

Integral identities from NIST DLMF Chapter 18. The Hermite and weighted Jacobi antiderivatives
are proved by the fundamental theorem of calculus. The Laguerre squared norm
is obtained from the already proved monomial moments;
other declarations below still include admitted results.
Probabilists’ Hermite orthogonality and polynomial Gaussian integrability use
the corresponding results of the Tau Ceti contributors. The two Hermite Fourier
eigenfunction identities adapt their normalized Hermite Fourier theorem to the
positive phase and scales used in DLMF.
The Hermite cosine and sine transforms 18.17.23 and 18.17.27 integrate by parts
against `He_n(x) e^{-x²/2}`; they use the Tau Ceti contributors' Gaussian
integrability `integrable_aeval_mul_gaussian` and Hermite parity `hermite_aeval_neg`.
The product cosine and sine transforms use finite Hermite linearization followed
by the single-polynomial transforms. The Gaussian convolution transfers derivatives
by integration by parts and evaluates its base case with Hermite addition.
The Laguerre fractional integrals reuse the regularized Kummer parameter integral
and the Laguerre addition and moment formulas. Gamma normalization uses Mathlib's
Gamma/Pochhammer identity; the tail substitution uses its measure-preserving translation API.
The Jacobi fractional integral reuses the regularized Gauss fractional integral.
Both Rodrigues formulas iterate the proved weighted derivative identities, with
Mathlib's iterated-derivative and real-scalar APIs handling the real restrictions.
Jacobi norms reduce by weighted integration by parts to shifted parameters and
terminate at the Beta integral, using Mathlib's endpoint-continuity and FTC APIs.
Gegenbauer orthogonality reuses symmetric Jacobi orthogonality and these norms;
Mathlib's Gamma duplication formula fixes its normalization, including degree zero.
Legendre norms follow from the three-term recurrence and proved Jacobi orthogonality.
The unweighted Laguerre convolution uses Mathlib's interval integration by parts
and the project's Laguerre derivative recurrence, and retains arbitrary real endpoints.
The weighted Laguerre convolution expands the normalized polynomials into finite
Gamma-normalized sums and scales Mathlib's Beta integral. Its Vandermonde step
uses an additive functional on Mathlib polynomials and their binomial coefficients.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology

noncomputable section

set_option autoImplicit false

namespace AAR.OrthogonalPolynomials

/-- `x^k e^{-x²}` is integrable. -/
lemma integrable_pow_mul_exp_neg_sq (k : ℕ) :
    Integrable fun x : ℝ => x ^ k * Real.exp (-(x ^ 2)) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
    (s := (k : ℝ)) (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp [Real.rpow_natCast]

/-- A polynomial times the Gaussian is integrable. -/
lemma integrable_eval_mul_exp_neg_sq (q : ℝ[X]) :
    Integrable fun x : ℝ => q.eval x * Real.exp (-(x ^ 2)) := by
  exact TauCeti.integrable_eval_mul_exp_neg_sq q

/-- Physicists' Hermite polynomials as real polynomials. -/
abbrev hermitePhysR (n : ℕ) : ℝ[X] := (hermitePhys n).map (Int.castRingHom ℝ)

lemma aeval_hermitePhys_eq_eval (n : ℕ) (x : ℝ) :
    (aeval x (hermitePhys n) : ℝ) = (hermitePhysR n).eval x := by
  rw [aeval_def, hermitePhysR, eval_map]
  congr 1

lemma hermitePhysR_succ (n : ℕ) :
    hermitePhysR (n + 1) = 2 * X * hermitePhysR n - derivative (hermitePhysR n) := by
  simp [hermitePhysR, Polynomial.map_sub, Polynomial.map_mul, derivative_map]

lemma hasDerivAt_hermite_gauss (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (hermitePhysR n).eval y * Real.exp (-(y ^ 2)))
      (-((hermitePhysR (n + 1)).eval x * Real.exp (-(x ^ 2)))) x := by
  have hg : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2))) (Real.exp (-(x ^ 2)) * (-(2 * x))) x := by
    have := ((hasDerivAt_pow 2 x).neg).exp
    simpa using this
  have h := ((hermitePhysR n).hasDerivAt x).mul hg
  convert h using 1
  rw [hermitePhysR_succ, eval_sub, eval_mul, eval_mul, eval_X]
  simp
  ring

/-- Repeated integration by parts against the Hermite–Gaussian. -/
lemma integral_eval_mul_hermite_gauss (n : ℕ) :
    ∀ q : ℝ[X], ∫ x : ℝ, q.eval x * ((hermitePhysR n).eval x * Real.exp (-(x ^ 2))) =
      ∫ x : ℝ, (derivative^[n] q).eval x * Real.exp (-(x ^ 2)) := by
  induction n with
  | zero => intro q; simp [hermitePhysR]
  | succ n ih =>
    intro q
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := fun x => q.eval x) (u' := fun x => (derivative q).eval x)
      (v := fun x => (hermitePhysR n).eval x * Real.exp (-(x ^ 2)))
      (v' := fun x => -((hermitePhysR (n + 1)).eval x * Real.exp (-(x ^ 2))))
      (fun x _ => q.hasDerivAt x) (fun x _ => hasDerivAt_hermite_gauss n x)
      (by
        have := (integrable_eval_mul_exp_neg_sq (q * hermitePhysR (n + 1))).neg
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only [Pi.mul_apply, eval_mul, Pi.neg_apply]; ring)
      (by
        have := integrable_eval_mul_exp_neg_sq (derivative q * hermitePhysR n)
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only [Pi.mul_apply, eval_mul]; ring)
      (by
        have := integrable_eval_mul_exp_neg_sq (q * hermitePhysR n)
        refine this.congr (Eventually.of_forall fun x => ?_)
        simp only [Pi.mul_apply, eval_mul]; ring)
    have h1 : ∫ x : ℝ, q.eval x * ((hermitePhysR (n + 1)).eval x * Real.exp (-(x ^ 2))) =
        -∫ x : ℝ, q.eval x * -((hermitePhysR (n + 1)).eval x * Real.exp (-(x ^ 2))) := by
      rw [← integral_neg]; congr 1; funext x; ring
    rw [h1, hibp, neg_neg, ih, Function.iterate_succ_apply]

lemma hermitePhysR_natDegree_coeff (n : ℕ) :
    (hermitePhysR n).natDegree ≤ n ∧ (hermitePhysR n).coeff n = 2 ^ n := by
  induction n with
  | zero => simp [hermitePhysR]
  | succ n ih =>
    obtain ⟨hd, hc⟩ := ih
    rw [hermitePhysR_succ]
    constructor
    · refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        have : (2 * X : ℝ[X]).natDegree ≤ 1 := by
          rw [show (2 * X : ℝ[X]) = C 2 * X by rw [← map_ofNat C 2]]
          exact (natDegree_C_mul_le 2 X).trans natDegree_X_le
        omega
      · exact (natDegree_derivative_le _).trans (by omega)
    · rw [coeff_sub, show (2 * X : ℝ[X]) = C 2 * X by rw [← map_ofNat C 2], mul_assoc, coeff_C_mul, coeff_X_mul,
        hc, coeff_derivative, coeff_eq_zero_of_natDegree_lt (by omega)]
      ring

/-- Scaling Mathlib's Beta integral gives the power moments used in Laguerre
convolutions, including singular but integrable endpoints. -/
lemma integral_cpow_mul_sub_cpow {a b : ℂ} {x : ℝ}
    (ha : -1 < a.re) (hb : -1 < b.re) (hx : 0 < x) :
    (∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^ a * ((x : ℂ) - t) ^ b) =
      (x : ℂ) ^ (a + b + 1) * (Gamma (a + 1) * Gamma (b + 1) / Gamma (a + b + 2)) := by
  let f : ℝ → ℂ := fun t => (t : ℂ) ^ a * ((x : ℂ) - t) ^ b
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hs := intervalIntegral.smul_integral_comp_mul_left f x (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one, Complex.real_smul] at hs
  have hpow : (x : ℂ) * (x : ℂ) ^ a * (x : ℂ) ^ b = (x : ℂ) ^ (a + b + 1) := by
    calc
      _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ a * (x : ℂ) ^ b := by rw [cpow_one]
      _ = _ := by
        rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]
        congr 1
        ring
  have hi : (∫ t : ℝ in (0 : ℝ)..x, f t) =
      (x : ℂ) ^ (a + b + 1) * betaIntegral (a + 1) (b + 1) := by
    rw [← hs, betaIntegral, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have hp : ((x : ℂ) * (1 - (t : ℂ))) ^ b = (x : ℂ) ^ b * (1 - (t : ℂ)) ^ b := by
      simpa only [ofReal_sub, ofReal_one] using
        mul_cpow_ofReal_nonneg hx.le (sub_nonneg.mpr ht.2.le) b
    dsimp [f]
    simp only [ofReal_mul, add_sub_cancel_right]
    rw [show (x : ℂ) - (x : ℂ) * t = (x : ℂ) * (1 - (t : ℂ)) by ring,
      mul_cpow_ofReal_nonneg hx.le ht.1.le, hp]
    linear_combination (t : ℂ) ^ a * (1 - (t : ℂ)) ^ b * hpow
  rw [betaIntegral_eq_Gamma_mul_div (a + 1) (b + 1) (by simp; linarith) (by simp; linarith)] at hi
  simpa only [show a + 1 + (b + 1) = a + b + 2 by ring] using hi

/-- Integrability of scaled Beta kernels, including integrable endpoint singularities. -/
lemma intervalIntegrable_cpow_mul_sub_cpow {a b : ℂ} {x : ℝ}
    (ha : -1 < a.re) (hb : -1 < b.re) (hx : 0 < x) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ a * ((x : ℂ) - t) ^ b) volume 0 x := by
  have hi := (betaIntegral_convergent (u := a + 1) (v := b + 1)
    (by simp; linarith) (by simp; linarith)).comp_mul_left (c := x⁻¹)
  simp only [add_sub_cancel_right, zero_div, one_div, inv_inv] at hi
  apply (hi.const_mul ((x : ℂ) ^ a * (x : ℂ) ^ b)).congr_ae
  apply (ae_restrict_mem measurableSet_Ioc).mono
  intro t ht
  simp only [min_eq_left hx.le, max_eq_right hx.le, Set.mem_Ioc] at ht
  dsimp only
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : 0 ≤ 1 - x⁻¹ * t := by
    rw [inv_mul_eq_div]; exact sub_nonneg.mpr ((div_le_one hx).mpr ht.2)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have he : (x : ℂ) * ((x⁻¹ * t : ℝ) : ℂ) = t := by
    push_cast; field_simp
  have he' : (x : ℂ) * ((1 - x⁻¹ * t : ℝ) : ℂ) = (x : ℂ) - t := by
    push_cast; field_simp
  have hp := mul_cpow_ofReal_nonneg hx.le
    (mul_nonneg (inv_nonneg.mpr hx.le) ht0) a
  have hp' := mul_cpow_ofReal_nonneg hx.le ht1 b
  rw [he] at hp
  rw [he'] at hp'
  simp only [ofReal_sub, ofReal_one] at hp'
  rw [hp, hp']
  ring

/-- Integrability of the Jacobi weight on its orthogonality interval. -/
lemma intervalIntegrable_jacobi_weight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    IntervalIntegrable (fun t : ℝ => (1 - (t : ℂ)) ^ (α : ℂ) *
      (1 + (t : ℂ)) ^ (β : ℂ)) volume (-1) 1 := by
  have hi := (intervalIntegrable_cpow_mul_sub_cpow (a := (β : ℂ)) (b := (α : ℂ))
    hβ hα (show (0 : ℝ) < 2 by norm_num)).comp_add_right 1
  norm_num only [zero_sub, sub_self, sub_add_cancel] at hi
  convert hi using 1
  · ext t
    push_cast
    rw [show (2 : ℂ) - ((t : ℂ) + 1) = 1 - t by ring]
    rw [add_comm (t : ℂ) 1]
    ring

/-- Integrability of Jacobi polynomial products against their weight. -/
lemma intervalIntegrable_jacobi_product {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (m n : ℕ) :
    IntervalIntegrable (fun t : ℝ => jacobiP α β m t * jacobiP α β n t *
      (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ)) volume (-1) 1 := by
  have hP (k : ℕ) : Continuous (fun t : ℝ => jacobiP α β k t) :=
    (continuous_iff_continuousAt.mpr fun z => (analyticAt_jacobiP α β k z).continuousAt).comp
      continuous_ofReal
  convert (intervalIntegrable_jacobi_weight hα hβ).continuousOn_mul
    ((hP m).mul (hP n)).continuousOn using 1
  ext t
  simp only [Pi.mul_apply]
  ring

/-- Integration by parts reduces a Jacobi squared norm to a shifted norm. -/
lemma jacobi_norm_shift {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    4 * (n + 1 : ℂ) * (∫ t : ℝ in (-1 : ℝ)..1, jacobiP α β (n + 1) t ^ 2 *
      (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ)) =
    (n + α + β + 2 : ℂ) * (∫ t : ℝ in (-1 : ℝ)..1, jacobiP (α + 1) (β + 1) n t ^ 2 *
      (1 - (t : ℂ)) ^ (α + 1 : ℂ) * (1 + (t : ℂ)) ^ (β + 1 : ℂ)) := by
  let w (a b : ℝ) (t : ℝ) : ℂ := (1 - (t : ℂ)) ^ (a : ℂ) * (1 + (t : ℂ)) ^ (b : ℂ)
  let g (t : ℝ) : ℂ := w (α + 1) (β + 1) t * jacobiP (α + 1) (β + 1) n t
  let H (t : ℝ) : ℂ := g t * jacobiP α β (n + 1) t
  let f (a b : ℝ) (k : ℕ) (t : ℝ) : ℂ := jacobiP a b k t ^ 2 * w a b t
  have hP (a b : ℝ) (k : ℕ) : Continuous (fun t : ℝ => jacobiP a b k t) :=
    (continuous_iff_continuousAt.mpr fun z => (analyticAt_jacobiP a b k z).continuousAt).comp
      continuous_ofReal
  have hw : ContinuousOn (w (α + 1) (β + 1)) (Set.Icc (-1) 1) := by
    intro t ht
    dsimp only [w]
    apply ContinuousWithinAt.mul
    · exact ((continuousAt_cpow_const_of_re_pos (z := 1 - (t : ℂ))
        (Or.inl (by simp; linarith [ht.2]))
        (show 0 < ((α + 1 : ℝ) : ℂ).re by simp; linarith)).comp (x := t)
        (show ContinuousAt (fun u : ℝ => 1 - (u : ℂ)) t by fun_prop)).continuousWithinAt
    · exact ((continuousAt_cpow_const_of_re_pos (z := 1 + (t : ℂ))
        (Or.inl (by simp; linarith [ht.1]))
        (show 0 < ((β + 1 : ℝ) : ℂ).re by simp; linarith)).comp (x := t)
        (show ContinuousAt (fun u : ℝ => 1 + (u : ℂ)) t by fun_prop)).continuousWithinAt
  have hHcont : ContinuousOn H (Set.Icc (-1) 1) := by
    simpa only [H, g, ofReal_add, ofReal_one, Pi.mul_def] using
      (hw.mul (hP (α + 1) (β + 1) n).continuousOn).mul (hP α β (n + 1)).continuousOn
  have hd (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) : HasDerivAt H
      (-2 * (n + 1 : ℂ) * f α β (n + 1) t +
        (n + α + β + 2 : ℂ) / 2 * f (α + 1) (β + 1) n t) t := by
    have h1 : 1 - (t : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [ht.2])
    have h2 : 1 + (t : ℂ) ∈ slitPlane := Or.inl (by simp; linarith [ht.1])
    have hA := ((((hasDerivAt_id' (t : ℂ)).const_sub 1).cpow_const
      (c := ((α + 1 : ℝ) : ℂ)) h1).comp_ofReal)
    have hB := ((((hasDerivAt_id' (t : ℂ)).const_add 1).cpow_const
      (c := ((β + 1 : ℝ) : ℂ)) h2).comp_ofReal)
    have hJ := (analyticAt_jacobiP ((α + 1 : ℝ) : ℂ) ((β + 1 : ℝ) : ℂ) n (t : ℂ)).differentiableAt.hasDerivAt.comp_ofReal
    have hg : DifferentiableAt ℝ g t := by
      simpa only [g, w, ofReal_add, ofReal_one, Function.comp_apply, Pi.mul_def] using
        ((hA.mul hB).mul hJ).differentiableAt
    have he := jacobi_weighted_derivative (α := α + 1) (β := β + 1)
      (by linarith) (by linarith) n ht
    simp only [ofReal_add, ofReal_one, add_sub_cancel_right, add_sub_cancel_right] at he
    have he' : deriv g t = -2 * (n + 1 : ℂ) * w α β t * jacobiP α β (n + 1) t := by
      simpa only [g, w, ofReal_add, ofReal_one, mul_assoc] using he
    have hJ' := (analyticAt_jacobiP (α : ℂ) β (n + 1) (t : ℂ)).differentiableAt.hasDerivAt.comp_ofReal
    rw [jacobi_derivative hα] at hJ'
    have h := hg.hasDerivAt.mul hJ'
    rw [he'] at h
    convert h using 1
    dsimp [H, g, f, w]
    push_cast
    ring
  have hf (a b : ℝ) (ha : -1 < a) (hb : -1 < b) (k : ℕ) :
      IntervalIntegrable (f a b k) volume (-1) 1 := by
    simpa only [f, w, pow_two, mul_assoc] using intervalIntegrable_jacobi_product ha hb k k
  have hi := ((hf α β hα hβ (n + 1)).const_mul (-2 * (n + 1 : ℂ))).add
    ((hf (α + 1) (β + 1) (by linarith) (by linarith) n).const_mul ((n + α + β + 2 : ℂ) / 2))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (-1 : ℝ) ≤ 1)
    hHcont hd hi
  have ha0 : ((α + 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hb0 : ((β + 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  simp only [H, g, w, ofReal_one, ofReal_neg, sub_self, add_neg_cancel,
    zero_cpow ha0, zero_cpow hb0, zero_mul, mul_zero] at he
  rw [intervalIntegral.integral_add (f := fun t => -2 * (n + 1 : ℂ) * f α β (n + 1) t)
    (g := fun t => (n + α + β + 2 : ℂ) / 2 * f (α + 1) (β + 1) n t)
    ((hf α β hα hβ (n + 1)).const_mul _) ((hf (α + 1) (β + 1) (by linarith) (by linarith) n).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  dsimp [f, w] at he
  push_cast at he ⊢
  simp only [mul_assoc] at he ⊢
  linear_combination -2 * he

/-- The Jacobi weight integral in a form regular throughout the orthogonality range. -/
lemma integral_jacobi_weight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) :
    (∫ t : ℝ in (-1 : ℝ)..1, (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ)) =
      (2 : ℂ) ^ ((α : ℂ) + β + 1) * (Gamma ((α : ℂ) + 1) * Gamma ((β : ℂ) + 1) /
        Gamma ((α : ℂ) + β + 2)) := by
  have he := intervalIntegral.integral_comp_add_right
    (fun t : ℝ => (t : ℂ) ^ (β : ℂ) * ((2 : ℂ) - t) ^ (α : ℂ)) 1
    (a := (-1 : ℝ)) (b := 1)
  norm_num only [neg_add_cancel, one_add_one_eq_two] at he
  have hm := integral_cpow_mul_sub_cpow (a := (β : ℂ)) (b := (α : ℂ)) hβ hα
    (by norm_num : (0 : ℝ) < 2)
  norm_num only [ofReal_ofNat] at hm
  rw [hm] at he
  calc
    _ = ∫ t : ℝ in (-1 : ℝ)..1, ((t + 1 : ℝ) : ℂ) ^ (β : ℂ) *
        ((2 : ℂ) - ((t + 1 : ℝ) : ℂ)) ^ (α : ℂ) := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      push_cast
      rw [show (2 : ℂ) - ((t : ℂ) + 1) = 1 - t by ring, add_comm (t : ℂ) 1]
      ring
    _ = _ := by rw [he, add_comm (β : ℂ) α, mul_comm (Gamma ((β : ℂ) + 1))]

/-- Jacobi squared norms at all degrees, with a denominator regular at degree zero. -/
lemma jacobi_norm_all {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    (∫ t : ℝ in (-1 : ℝ)..1, jacobiP α β n t ^ 2 *
      (1 - (t : ℂ)) ^ (α : ℂ) * (1 + (t : ℂ)) ^ (β : ℂ)) =
      (2 : ℂ) ^ ((α : ℂ) + β + 1) * Gamma ((α : ℂ) + n + 1) * Gamma ((β : ℂ) + n + 1) *
        poch ((α : ℂ) + β + n + 1) n /
          (n.factorial * Gamma ((α : ℂ) + β + 2 * n + 2)) := by
  induction n generalizing α β with
  | zero => simpa only [jacobiP_zero, one_pow, one_mul, Nat.cast_zero, add_zero, mul_zero,
      poch_zero, mul_one, Nat.factorial_zero, Nat.cast_one, mul_div_assoc, mul_assoc] using integral_jacobi_weight hα hβ
  | succ n ih =>
    have h := jacobi_norm_shift hα hβ n
    have hih := ih (by linarith : -1 < α + 1) (by linarith : -1 < β + 1)
    push_cast at hih
    rw [hih] at h
    have hn : (4 : ℂ) * (n + 1 : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (by exact_mod_cast Nat.succ_ne_zero n)
    apply mul_left_cancel₀ hn
    rw [h]
    push_cast
    rw [poch_succ_left, Nat.factorial_succ]
    push_cast
    have hp : (2 : ℂ) ^ (((α : ℂ) + 1) + ((β : ℂ) + 1) + 1) =
        4 * (2 : ℂ) ^ ((α : ℂ) + β + 1) := by
      rw [show ((α : ℂ) + 1) + ((β : ℂ) + 1) + 1 = ((α : ℂ) + β + 1) + 2 by ring,
        cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      norm_num
      ring
    rw [hp]
    have hG : Gamma ((α : ℂ) + β + 2 * n + 4) ≠ 0 := Gamma_ne_zero_of_re_pos (by
      simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
    have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    rw [show ((α : ℂ) + 1) + n + 1 = (α : ℂ) + (n + 1) + 1 by ring,
      show ((β : ℂ) + 1) + n + 1 = (β : ℂ) + (n + 1) + 1 by ring,
      show ((α : ℂ) + 1) + ((β : ℂ) + 1) + n + 1 = ((α : ℂ) + β + (n + 1) + 1) + 1 by ring,
      show ((α : ℂ) + 1) + ((β : ℂ) + 1) + 2 * n + 2 = (α : ℂ) + β + 2 * n + 4 by ring,
      show (α : ℂ) + β + 2 * (n + 1) + 2 = (α : ℂ) + β + 2 * n + 4 by ring]
    field_simp
    ring

@[dlmf 18.3.T1]
theorem jacobi_norm {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, jacobiP α β (n + 1) x ^ 2 *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) =
      (2 : ℂ) ^ ((α : ℂ) + β + 1) * Gamma (n + (α : ℂ) + 2) * Gamma (n + (β : ℂ) + 2) /
      ((2 * n + α + β + 3) * (n + 1).factorial * Gamma (n + (α : ℂ) + β + 2)) := by
  rw [jacobi_norm_all hα hβ]
  have hz : 0 < ((α : ℂ) + β + n + 2).re := by
    simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  have hg := Gamma_add_nat_div_Gamma_eq (n := n + 1) ((α : ℂ) + β + n + 2)
    (not_neg_nat_of_re_pos hz)
  change _ = poch ((α : ℂ) + β + n + 2) (n + 1) at hg
  push_cast at hg ⊢
  rw [show (α : ℂ) + β + (n + 1) + 1 = (α : ℂ) + β + n + 2 by ring, ← hg,
    show (α : ℂ) + β + n + 2 + (n + 1) = (α : ℂ) + β + 2 * n + 3 by ring,
    show (α : ℂ) + β + 2 * (n + 1) + 2 = ((α : ℂ) + β + 2 * n + 3) + 1 by ring,
    Gamma_add_one ((α : ℂ) + β + 2 * n + 3) (by
      have hp : 0 < ((α : ℂ) + β + 2 * n + 3).re := by
        simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
      intro he; rw [he] at hp; simp at hp)]
  have hG : Gamma ((α : ℂ) + β + 2 * n + 3) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  rw [show (α : ℂ) + (n + 1) + 1 = n + (α : ℂ) + 2 by ring,
    show (β : ℂ) + (n + 1) + 1 = n + (β : ℂ) + 2 by ring,
    show (α : ℂ) + β + n + 2 = n + (α : ℂ) + β + 2 by ring,
    show (α : ℂ) + β + 2 * n + 3 = 2 * n + (α : ℂ) + β + 3 by ring] at *
  have hG' : Gamma ((n : ℂ) * 2 + α + β + 3) ≠ 0 := by
    convert hG using 1
    congr 1
    ring
  field_simp [hG']

/-- The squared Laguerre norm for the weight `x^α exp (-x)` on the positive ray. -/
@[dlmf 18.3.T1]
theorem laguerre_norm {α : ℝ} (hα : -1 < α) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, laguerre α n x ^ 2 * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (n + (α : ℂ) + 1) / n.factorial := by
  have heq : (fun x : ℝ => laguerre α n x ^ 2 * exp (-x) * (x : ℂ) ^ (α : ℂ)) =
      fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (poch ((α : ℂ) + 1) n / n.factorial * confluentHGCoeff (-(n : ℂ)) (α + 1) k) *
          (laguerre α n x * (x : ℂ) ^ k * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) := by
    funext x
    rw [pow_two]
    conv_lhs => arg 1; arg 1; arg 1; rw [laguerre_eq_sum_coeff (α : ℂ) n]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq, integral_finsetSum _ (fun k _ =>
    (integrable_laguerre_mul_monomial hα n k).const_mul _)]
  simp_rw [MeasureTheory.integral_const_mul, integral_laguerre_mul_monomial hα]
  rw [Finset.sum_eq_single n]
  · have hc : ∀ j : ℕ, (α : ℂ) + 1 ≠ -j := not_neg_nat_of_re_pos (by
      simp only [add_re, ofReal_re, one_re]; linarith)
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hp := poch_ne_zero_of_not_neg_nat hc n
    change (poch ((α : ℂ) + 1) n / n.factorial *
      (poch (-(n : ℂ)) n / (poch ((α : ℂ) + 1) n * n.factorial))) *
      (Gamma ((α : ℂ) + n + 1) * poch (-(n : ℂ)) n / n.factorial) = _
    rw [poch_neg_coe_nat, Nat.descFactorial_self]
    have hs : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    rw [show (α : ℂ) + n + 1 = n + (α : ℂ) + 1 by ring]
    field_simp [hn, hp]
    linear_combination (Gamma (n + (α : ℂ) + 1)) * hs
  · intro k hk hkn
    have hlt : k < n := by have := Finset.mem_range.mp hk; omega
    rw [poch_neg_nat_eq_zero hlt]
    simp
  · simp

@[dlmf 18.3.T1]
theorem hermitePhys_orthogonality (m n : ℕ) :
    ∫ x : ℝ, (aeval x (hermitePhys m) : ℝ) * aeval x (hermitePhys n) * Real.exp (-(x ^ 2)) =
      if m = n then Real.sqrt Real.pi * 2 ^ n * n.factorial else 0 := by
  have key : ∀ a b : ℕ, ∫ x : ℝ, (aeval x (hermitePhys a) : ℝ) * aeval x (hermitePhys b) *
      Real.exp (-(x ^ 2)) = ∫ x : ℝ, (derivative^[b] (hermitePhysR a)).eval x *
        Real.exp (-(x ^ 2)) := fun a b => by
    rw [← integral_eval_mul_hermite_gauss b]
    congr 1; funext x
    rw [aeval_hermitePhys_eq_eval, aeval_hermitePhys_eq_eval]; ring
  have hzero : ∀ a b : ℕ, a < b → ∫ x : ℝ, (aeval x (hermitePhys a) : ℝ) * aeval x (hermitePhys b) *
      Real.exp (-(x ^ 2)) = 0 := fun a b hab => by
    rw [key, iterate_derivative_eq_zero ((hermitePhysR_natDegree_coeff a).1.trans_lt hab)]
    simp
  split_ifs with hmn
  · subst hmn
    rw [key]
    obtain ⟨hd, hc⟩ := hermitePhysR_natDegree_coeff m
    have hconst : derivative^[m] (hermitePhysR m) = C ((m ! : ℝ) * 2 ^ m) := by
      rw [eq_C_of_natDegree_le_zero ((natDegree_iterate_derivative _ _).trans (by omega)),
        coeff_iterate_derivative, zero_add, Nat.descFactorial_self, hc, nsmul_eq_mul]
    simp only [hconst, eval_C]
    rw [integral_const_mul, show (fun x : ℝ => Real.exp (-(x ^ 2))) =
      fun x => Real.exp (-1 * x ^ 2) by funext x; ring_nf, integral_gaussian, div_one]
    ring
  · rcases Nat.lt_or_gt_of_ne hmn with h | h
    · exact hzero m n h
    · rw [← hzero n m h]
      congr 1; funext x; ring

@[dlmf 18.3.T1]
theorem hermite_orthogonality (m n : ℕ) :
    ∫ x : ℝ, (aeval x (hermite m) : ℝ) * aeval x (hermite n) * Real.exp (-(x ^ 2) / 2) =
      if m = n then Real.sqrt (2 * Real.pi) * n.factorial else 0 := by
  simpa only [neg_div, mul_comm] using
    TauCeti.integral_hermite_mul_hermite_mul_gaussian m n

@[dlmf 18.3.T1]
theorem legendre_orthogonality (m n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, legendreP m x * legendreP n x =
      if m = n then 2 / (2 * (n : ℂ) + 1) else 0 := by
  let K : ℕ → ℕ → ℂ := fun i j => ∫ x : ℝ in (-1 : ℝ)..1, legendreP i x * legendreP j x
  let J : ℕ → ℕ → ℂ := fun i j => ∫ x : ℝ in (-1 : ℝ)..1,
    (x : ℂ) * legendreP i x * legendreP j x
  have hL (i : ℕ) : Continuous (fun x : ℝ => legendreP i x) :=
    (continuous_iff_continuousAt.mpr fun z =>
      ((analyticOnNhd_jacobiP 0 0 i) z (Set.mem_univ z)).continuousAt).comp continuous_ofReal
  have hK (i j : ℕ) : IntervalIntegrable
      (fun x : ℝ => legendreP i x * legendreP j x) volume (-1) 1 :=
    ((hL i).mul (hL j)).intervalIntegrable _ _
  have hJ (i j : ℕ) : IntervalIntegrable
      (fun x : ℝ => (x : ℂ) * legendreP i x * legendreP j x) volume (-1) 1 :=
    ((continuous_ofReal.mul (hL i)).mul (hL j)).intervalIntegrable _ _
  have hzero (i j : ℕ) (hij : i ≠ j) : K i j = 0 := by
    simpa only [K, legendreP, ofReal_zero, cpow_zero, mul_one] using
      jacobiP_orthogonal (α := 0) (β := 0) (by norm_num) (by norm_num) hij
  have hR (i j : ℕ) : (i + 2 : ℂ) * K (i + 2) j =
      (2 * i + 3 : ℂ) * J (i + 1) j - (i + 1 : ℂ) * K i j := by
    dsimp [K, J]
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub ((hJ (i + 1) j).const_mul _) ((hK i j).const_mul _)]
    apply intervalIntegral.integral_congr
    intro x _
    linear_combination legendreP j x * legendreP_recurrence i x
  have hJsym (i j : ℕ) : J i j = J j i :=
    intervalIntegral.integral_congr fun x _ => by ring
  have hnorm : ∀ i : ℕ, K i i = 2 / (2 * (i : ℂ) + 1) := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero => norm_num [K, legendreP_zero]
    | one =>
      have h := hR 0 0
      rw [hzero 2 0 (by omega)] at h
      have h00 : K 0 0 = 2 := by norm_num [K, legendreP_zero]
      have h10 : J 1 0 = K 1 1 := by simp [J, K, legendreP_zero]
      rw [h00, h10] at h
      norm_num at h ⊢
      linear_combination -h / 3
    | more i _hi hi1 =>
      have h₁ := hR i (i + 2)
      have h₂ := hR (i + 1) (i + 1)
      rw [hzero i (i + 2) (by omega), mul_zero, sub_zero] at h₁
      rw [hzero (i + 1 + 2) (i + 1) (by omega), mul_zero, hi1] at h₂
      have hsym : J (i + 1 + 1) (i + 1) = J (i + 1) (i + 2) := by
        simpa only [Nat.add_assoc] using hJsym (i + 2) (i + 1)
      rw [hsym] at h₂
      have hd : (2 * (i + 2 : ℂ) + 1) ≠ 0 := by
        have hp : 0 < (2 * (i + 2 : ℂ) + 1).re := by simp; positivity
        intro h; rw [h] at hp; simpa using hp
      have hd1 : (2 * (i + 1 : ℂ) + 1) ≠ 0 := by
        have hp : 0 < (2 * (i + 1 : ℂ) + 1).re := by simp; positivity
        intro h; rw [h] at hp; simpa using hp
      have hn : (i + 2 : ℂ) ≠ 0 := by
        have hp : 0 < (i + 2 : ℂ).re := by simp; positivity
        intro h; rw [h] at hp; simpa using hp
      push_cast at h₁ h₂ ⊢
      apply (eq_div_iff hd).mpr
      have h₂' : (2 * (i : ℂ) + 5) * J (i + 1) (i + 2) *
          (2 * (i : ℂ) + 3) = 2 * ((i : ℂ) + 2) := by
        have he : (2 * (i : ℂ) + 5) * J (i + 1) (i + 2) =
            (2 * ((i : ℂ) + 2)) / (2 * (i : ℂ) + 3) := by
          linear_combination -h₂
        exact (eq_div_iff (by convert hd1 using 1 <;> ring)).mp he
      apply mul_left_cancel₀ hn
      linear_combination (2 * (i : ℂ) + 5) * h₁ + h₂'
  split_ifs with hmn
  · subst m
    exact hnorm n
  · exact hzero m n hmn

/-- Duplication converts the symmetric Jacobi normalization to the Gegenbauer one. -/
private lemma gegenbauer_norm_constant {lam : ℝ} (hlam : 0 < lam) :
    (2 : ℂ) ^ (2 * (lam : ℂ)) * Gamma ((lam : ℂ) + 1 / 2) ^ 2 / Gamma (2 * (lam : ℂ)) ^ 2 =
      2 * (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.pi / Gamma (lam : ℂ) ^ 2 := by
  have hG : Gamma (lam : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos hlam
  have hG2 : Gamma (2 * (lam : ℂ)) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hd := Gamma_mul_Gamma_add_half (lam : ℂ)
  have hh : Gamma ((lam : ℂ) + 1 / 2) =
      Gamma (2 * (lam : ℂ)) * (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.sqrt Real.pi / Gamma (lam : ℂ) := by
    apply (eq_div_iff hG).mpr
    linear_combination hd
  have hs : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hp' : (2 : ℂ) ^ (2 * (lam : ℂ)) * (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) = 2 := by
    rw [← cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0),
      show 2 * (lam : ℂ) + (1 - 2 * (lam : ℂ)) = 1 by ring, cpow_one]
  rw [hh, div_pow, mul_pow, mul_pow, hs]
  field_simp
  exact hp'

/-- Gegenbauer squared norms, including degree zero. -/
lemma gegenbauer_norm {lam : ℝ} (hlam : 0 < lam) (n : ℕ) :
    (∫ t : ℝ in (-1 : ℝ)..1, gegenbauer lam n t ^ 2 *
      (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2)) =
      (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.pi * Gamma (n + 2 * (lam : ℂ)) /
        ((n + lam) * Gamma (lam : ℂ) ^ 2 * n.factorial) := by
  have ha : -1 < lam - 1 / 2 := by linarith
  have hpoch (k : ℕ) : poch ((lam : ℂ) + 1 / 2) k ≠ 0 :=
    poch_ne_zero_of_re_pos (by simp; linarith) k
  have he : (∫ t : ℝ in (-1 : ℝ)..1, gegenbauer lam n t ^ 2 *
      (1 - (t : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2)) =
      (poch (2 * (lam : ℂ)) n / poch ((lam : ℂ) + 1 / 2) n) ^ 2 *
        (∫ t : ℝ in (-1 : ℝ)..1, jacobiP ((lam - 1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) n t ^ 2 *
          (1 - (t : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) * (1 + (t : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    dsimp only
    rw [gegenbauer_eq_jacobiP n _ (hpoch n), mul_pow]
    have hp := mul_cpow_ofReal_nonneg (show 0 ≤ 1 - t by linarith [ht.2])
      (show 0 ≤ 1 + t by linarith [ht.1]) ((lam : ℂ) - 1 / 2)
    push_cast at hp ⊢
    rw [show (1 - (t : ℂ)) * (1 + t) = 1 - (t : ℂ) ^ 2 by ring] at hp
    rw [hp]
    ring
  rw [he, jacobi_norm_all ha ha]
  push_cast
  have h1 := Gamma_add_nat_div_Gamma_eq (n := n) ((lam : ℂ) + 1 / 2)
    (not_neg_nat_of_re_pos (by simp; linarith))
  change _ = poch ((lam : ℂ) + 1 / 2) n at h1
  have h2 := Gamma_add_nat_div_Gamma_eq (n := n) (2 * (lam : ℂ))
    (not_neg_nat_of_re_pos (by simp; linarith))
  change _ = poch (2 * (lam : ℂ)) n at h2
  have h3 := Gamma_add_nat_div_Gamma_eq (n := n) (2 * (lam : ℂ) + n)
    (not_neg_nat_of_re_pos (by simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith))
  change _ = poch (2 * (lam : ℂ) + n) n at h3
  have hG (k : ℕ) : Gamma (2 * (lam : ℂ) + k) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
  have hGh : Gamma ((lam : ℂ) + 1 / 2 + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by
    simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  have hGh0 : Gamma ((lam : ℂ) + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hG0 : Gamma (2 * (lam : ℂ)) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [show ((lam : ℂ) - 1 / 2) + ((lam : ℂ) - 1 / 2) + 1 = 2 * (lam : ℂ) by ring,
    show ((lam : ℂ) - 1 / 2) + n + 1 = (lam : ℂ) + 1 / 2 + n by ring,
    show ((lam : ℂ) - 1 / 2) + ((lam : ℂ) - 1 / 2) + n + 1 = 2 * (lam : ℂ) + n by ring,
    show ((lam : ℂ) - 1 / 2) + ((lam : ℂ) - 1 / 2) + 2 * n + 2 =
      (2 * (lam : ℂ) + (2 * n : ℕ)) + 1 by push_cast; ring,
    ← h1, ← h2, ← h3,
    show 2 * (lam : ℂ) + n + n = 2 * (lam : ℂ) + (2 * n : ℕ) by push_cast; ring,
    Gamma_add_one (2 * (lam : ℂ) + (2 * n : ℕ)) (by
      have hp : 0 < (2 * (lam : ℂ) + (2 * n : ℕ)).re := by
        simp; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
      intro h; rw [h] at hp; simp at hp)]
  have hconst := gegenbauer_norm_constant hlam
  have halgebra : (Gamma (2 * (lam : ℂ) + n) / Gamma (2 * (lam : ℂ)) /
      (Gamma ((lam : ℂ) + 1 / 2 + n) / Gamma ((lam : ℂ) + 1 / 2))) ^ 2 *
        ((2 : ℂ) ^ (2 * (lam : ℂ)) * Gamma ((lam : ℂ) + 1 / 2 + n) *
          Gamma ((lam : ℂ) + 1 / 2 + n) *
          (Gamma (2 * (lam : ℂ) + (2 * n : ℕ)) / Gamma (2 * (lam : ℂ) + n)) /
          (n.factorial * ((2 * (lam : ℂ) + (2 * n : ℕ)) * Gamma (2 * (lam : ℂ) + (2 * n : ℕ))))) =
      ((2 : ℂ) ^ (2 * (lam : ℂ)) * Gamma ((lam : ℂ) + 1 / 2) ^ 2 / Gamma (2 * (lam : ℂ)) ^ 2) *
        Gamma (2 * (lam : ℂ) + n) / ((2 * (lam : ℂ) + (2 * n : ℕ)) * n.factorial) := by
    have hfield (A B C D E P q r : ℂ) (hA : A ≠ 0) (hB : B ≠ 0)
        (hC : C ≠ 0) (hD : D ≠ 0) (hE : E ≠ 0) :
        (A / B / (C / D)) ^ 2 * (P * C * C * (E / A) / (r * (q * E))) =
          (P * D ^ 2 / B ^ 2) * A / (q * r) := by
      field_simp
    exact hfield _ _ _ _ _ _ _ _ (hG n) hG0 hGh hGh0 (hG (2 * n))
  rw [halgebra, hconst]
  rw [show (2 * (lam : ℂ) + (2 * n : ℕ)) = 2 * ((n : ℂ) + lam) by push_cast; ring,
    add_comm (2 * (lam : ℂ)) (n : ℂ)]
  field_simp

@[dlmf 18.3.T1]
theorem gegenbauer_orthogonality {lam : ℝ} (hlam : 0 < lam) (m n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, gegenbauer lam m x * gegenbauer lam n x *
      (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) =
      if m = n then (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.pi * Gamma (n + 2 * (lam : ℂ)) /
        ((n + lam) * Gamma (lam : ℂ) ^ 2 * n.factorial) else 0 := by
  split_ifs with hmn
  · subst m
    simpa only [pow_two] using gegenbauer_norm hlam n
  · have ha : -1 < lam - 1 / 2 := by linarith
    have hpoch (k : ℕ) : poch ((lam : ℂ) + 1 / 2) k ≠ 0 :=
      poch_ne_zero_of_re_pos (by simp; linarith) k
    have he : (∫ x : ℝ in (-1 : ℝ)..1, gegenbauer lam m x * gegenbauer lam n x *
        (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2)) =
        (poch (2 * (lam : ℂ)) m / poch ((lam : ℂ) + 1 / 2) m *
          (poch (2 * (lam : ℂ)) n / poch ((lam : ℂ) + 1 / 2) n)) *
          (∫ t : ℝ in (-1 : ℝ)..1, jacobiP ((lam - 1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) m t *
            jacobiP ((lam - 1 / 2 : ℝ) : ℂ) ((lam - 1 / 2 : ℝ) : ℂ) n t *
            (1 - (t : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ) * (1 + (t : ℂ)) ^ ((lam - 1 / 2 : ℝ) : ℂ)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      dsimp only
      rw [gegenbauer_eq_jacobiP m _ (hpoch m), gegenbauer_eq_jacobiP n _ (hpoch n)]
      have hp := mul_cpow_ofReal_nonneg (show 0 ≤ 1 - t by linarith [ht.2])
        (show 0 ≤ 1 + t by linarith [ht.1]) ((lam : ℂ) - 1 / 2)
      push_cast at hp ⊢
      rw [show (1 - (t : ℂ)) * (1 + t) = 1 - (t : ℂ) ^ 2 by ring] at hp
      rw [hp]
      ring
    rw [he, jacobiP_orthogonal ha ha hmn, mul_zero]

/-- Repeated differentiation of the Jacobi weight, using the proved weighted
derivative identity on the open interval. -/
lemma iteratedDeriv_jacobi_weight {α β : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    iteratedDeriv n (fun t : ℝ => (1 - (t : ℂ)) ^ (α + n : ℂ) *
      (1 + (t : ℂ)) ^ (β + n : ℂ)) x =
        (-2 : ℂ) ^ n * n.factorial * (1 - (x : ℂ)) ^ (α : ℂ) *
          (1 + (x : ℂ)) ^ (β : ℂ) * jacobiP α β n x := by
  induction n generalizing α β x with
  | zero => simp
  | succ n ih =>
    have heq : iteratedDeriv n (fun t : ℝ => (1 - (t : ℂ)) ^ ((α : ℂ) + ((n + 1 : ℕ) : ℂ)) *
        (1 + (t : ℂ)) ^ ((β : ℂ) + ((n + 1 : ℕ) : ℂ))) =ᶠ[𝓝 x]
        (fun t : ℝ => ((-2 : ℂ) ^ n * n.factorial) *
          ((1 - (t : ℂ)) ^ (α + 1 : ℂ) * (1 + (t : ℂ)) ^ (β + 1 : ℂ) *
            jacobiP (α + 1) (β + 1) n t)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
      have h := ih (α := α + 1) (β := β + 1) (by linarith) (by linarith) ht
      push_cast at h
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (α : ℂ) + ((n : ℂ) + 1) = (α : ℂ) + 1 + n by ring,
        show (β : ℂ) + ((n : ℂ) + 1) = (β : ℂ) + 1 + n by ring]
      simpa only [mul_assoc] using h
    rw [iteratedDeriv_succ, heq.deriv_eq, deriv_const_mul_field]
    have hD := jacobi_weighted_derivative (by linarith : 0 < α + 1)
      (by linarith : 0 < β + 1) n hx
    push_cast at hD
    rw [hD]
    simp only [Nat.factorial_succ, pow_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      ofReal_add, ofReal_one, add_sub_cancel_right]
    ring

/-- Repeated differentiation of the Laguerre weight on the positive half-line. -/
lemma iteratedDeriv_laguerre_weight {α : ℝ} (hα : -1 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (α + n : ℂ)) x =
      (n.factorial : ℂ) * exp (-(x : ℂ)) * (x : ℂ) ^ (α : ℂ) * laguerre α n x := by
  induction n generalizing α x with
  | zero => simp
  | succ n ih =>
    have heq : iteratedDeriv n (fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ ((α : ℂ) + ((n + 1 : ℕ) : ℂ)))
        =ᶠ[𝓝 x] (fun t : ℝ => (n.factorial : ℂ) *
          (exp (-(t : ℂ)) * (t : ℂ) ^ (α + 1 : ℂ) * laguerre (α + 1) n t)) := by
      filter_upwards [Ioi_mem_nhds hx] with t ht
      have h := ih (α := α + 1) (by linarith) ht
      push_cast at h
      simp only [Nat.cast_add, Nat.cast_one]
      rw [show (α : ℂ) + ((n : ℂ) + 1) = (α : ℂ) + 1 + n by ring]
      simpa only [mul_assoc] using h
    rw [iteratedDeriv_succ, heq.deriv_eq, deriv_const_mul_field]
    have hD := laguerre_weighted_derivative (by linarith : 0 < α + 1) n hx
    push_cast at hD
    rw [hD]
    simp only [Nat.factorial_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      ofReal_add, ofReal_one, add_sub_cancel_right]
    ring

@[dlmf 18.5.E5]
theorem jacobi_rodrigues {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    jacobiP α β n x = (deriv^[n] (fun t : ℝ => (1 - t) ^ (α + n) * (1 + t) ^ (β + n)) x : ℝ) /
      ((-2 : ℂ) ^ n * n.factorial * (1 - x : ℂ) ^ (α : ℂ) * (1 + x : ℂ) ^ (β : ℂ)) := by
  let f : ℝ → ℝ := fun t => (1 - t) ^ (α + n) * (1 + t) ^ (β + n)
  have hf : ContDiffAt ℝ n f x := by
    exact ((contDiffAt_const.sub contDiffAt_id).rpow_const_of_ne (by dsimp; linarith [hx.2])).mul
      ((contDiffAt_const.add contDiffAt_id).rpow_const_of_ne (by dsimp; linarith [hx.1]))
  have heq : (fun t : ℝ => f t • (1 : ℂ)) =ᶠ[𝓝 x]
      (fun t : ℝ => (1 - (t : ℂ)) ^ (α + n : ℂ) * (1 + (t : ℂ)) ^ (β + n : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    simp only [f, Complex.real_smul, mul_one, ofReal_mul]
    rw [ofReal_cpow (by linarith [ht.2]), ofReal_cpow (by linarith [ht.1])]
    push_cast
    rfl
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_smul_const hf, iteratedDeriv_jacobi_weight hα hβ n hx,
    Complex.real_smul, mul_one, iteratedDeriv_eq_iterate] at hd
  rw [hd]
  have h1 : 1 - (x : ℂ) ≠ 0 := by exact_mod_cast (show 1 - x ≠ 0 by linarith [hx.2])
  have h2 : 1 + (x : ℂ) ≠ 0 := by exact_mod_cast (show 1 + x ≠ 0 by linarith [hx.1])
  field_simp [cpow_ne_zero_iff.mpr (Or.inl h1), cpow_ne_zero_iff.mpr (Or.inl h2),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]


@[dlmf 18.5.E5]
theorem laguerre_rodrigues {α : ℝ} (hα : -1 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerre α n x = (Real.exp x * x ^ (-α) *
      deriv^[n] (fun t : ℝ => Real.exp (-t) * t ^ (n + α)) x / n.factorial : ℝ) := by
  let f : ℝ → ℝ := fun t => Real.exp (-t) * t ^ (n + α)
  have hf : ContDiffAt ℝ n f x :=
    (by fun_prop : ContDiffAt ℝ n (fun t : ℝ => Real.exp (-t)) x).mul
      (Real.contDiffAt_rpow_const_of_ne hx.ne')
  have heq : (fun t : ℝ => f t • (1 : ℂ)) =ᶠ[𝓝 x]
      (fun t : ℝ => exp (-(t : ℂ)) * (t : ℂ) ^ (α + n : ℂ)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    simp only [f, Complex.real_smul, mul_one, ofReal_mul, ofReal_exp, ofReal_neg]
    rw [ofReal_cpow ht.le]
    push_cast
    congr 2
    ring
  have hd := heq.iteratedDeriv_eq n
  rw [iteratedDeriv_smul_const hf, iteratedDeriv_laguerre_weight hα n hx,
    Complex.real_smul, mul_one, iteratedDeriv_eq_iterate] at hd
  push_cast
  rw [hd, ofReal_cpow hx.le, ofReal_neg, exp_neg, cpow_neg]
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  field_simp [cpow_ne_zero_iff.mpr (Or.inl hx0), Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]


/-- **Rodrigues' formula for Gegenbauer polynomials** (DLMF 18.5.5, Temme §6.3): for `λ > -1/2`
and `-1 < x < 1`,
`C_n^λ(x) = (2λ)_n / ((-2)ⁿ n! (λ+1/2)_n) · (1-x²)^{1/2-λ} dⁿ/dxⁿ (1-x²)^{n+λ-1/2}`. -/
theorem gegenbauer_rodrigues {lam : ℝ} (hlam : -1 / 2 < lam) (n : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo (-1) 1) :
    gegenbauer lam n x = poch (2 * lam) n / ((-2 : ℂ) ^ n * n.factorial * poch (lam + 1 / 2) n) *
      ((1 - x ^ 2) ^ (1 / 2 - lam) *
        deriv^[n] (fun t : ℝ => (1 - t ^ 2) ^ (n + lam - 1 / 2)) x : ℝ) := by
  have hα : -1 < lam - 1 / 2 := by linarith
  have hp : poch ((lam : ℂ) + 1 / 2) n ≠ 0 := poch_ne_zero_of_not_neg_nat
    (not_neg_nat_of_re_pos (by simp; linarith)) n
  have hJ := jacobi_rodrigues hα hα n hx
  rw [gegenbauer_eq_jacobiP n x hp]
  push_cast at hJ ⊢
  rw [hJ]
  -- the two weights agree near `x`
  have hev : (fun t : ℝ => (1 - t) ^ (lam - 1 / 2 + n) * (1 + t) ^ (lam - 1 / 2 + n)) =ᶠ[𝓝 x]
      fun t : ℝ => (1 - t ^ 2) ^ (n + lam - 1 / 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with t ht
    rw [← Real.mul_rpow (by linarith [ht.2]) (by linarith [ht.1])]
    congr 1 <;> ring
  rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate, hev.iteratedDeriv_eq n]
  have h1 : 0 < 1 - x := by linarith [hx.2]
  have h2 : 0 < 1 + x := by linarith [hx.1]
  have hw : ((1 - x : ℂ) ^ ((lam : ℂ) - 1 / 2)) * ((1 + x : ℂ) ^ ((lam : ℂ) - 1 / 2)) =
      (((1 - x ^ 2) ^ (lam - 1 / 2) : ℝ) : ℂ) := by
    rw [show (1 - x ^ 2) = (1 - x) * (1 + x) by ring, Real.mul_rpow h1.le h2.le]
    push_cast
    rw [Complex.ofReal_cpow h1.le, Complex.ofReal_cpow h2.le]
    push_cast; ring
  have hw' : ((1 - x ^ 2) ^ (1 / 2 - lam) : ℝ) * (1 - x ^ 2) ^ (lam - 1 / 2) = 1 := by
    rw [← Real.rpow_add (by nlinarith)]; norm_num
  have hw0 : (((1 - x ^ 2) ^ (lam - 1 / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by nlinarith) _).ne'
  have hwC : (((1 - x ^ 2) ^ (1 / 2 - lam) : ℝ) : ℂ) = ((((1 - x ^ 2) ^ (lam - 1 / 2) : ℝ) : ℂ))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← Complex.ofReal_mul, hw']; simp
  rw [mul_assoc ((-2 : ℂ) ^ n * n.factorial), hw, hwC]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

/-- **Rodrigues' formula for Legendre polynomials** (DLMF 18.5.5, Temme (6.20)):
`P_n(x) = (2ⁿ n!)⁻¹ dⁿ/dxⁿ (x² - 1)ⁿ` for `-1 < x < 1`. -/
theorem legendre_rodrigues (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    legendreP n x = ((2 ^ n * n.factorial : ℝ)⁻¹ *
      deriv^[n] (fun t : ℝ => (t ^ 2 - 1) ^ n) x : ℝ) := by
  have h := gegenbauer_rodrigues (lam := 1 / 2) (by norm_num) n hx
  rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by norm_num, ← legendre_eq_gegenbauer] at h
  rw [h]
  have hfun : (fun t : ℝ => (1 - t ^ 2) ^ ((n : ℝ) + 1 / 2 - 1 / 2)) =
      fun t : ℝ => (-1) ^ n * (t ^ 2 - 1) ^ n := by
    funext t
    rw [show (n : ℝ) + 1 / 2 - 1 / 2 = (n : ℕ) by ring, Real.rpow_natCast, ← mul_pow]
    ring_nf
  rw [hfun, ← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate,
    iteratedDeriv_const_mul_field]
  simp only [show (1 / 2 : ℝ) - 1 / 2 = 0 by norm_num, Real.rpow_zero, one_mul]
  have hp1 : poch (2 * (1 / 2 : ℂ)) n = n.factorial := by
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, poch_nat_one]
  have hp2 : poch ((1 / 2 : ℂ) + 1 / 2) n = n.factorial := by
    rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, poch_nat_one]
  rw [hp1, hp2]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  push_cast
  rw [show (-2 : ℂ) ^ n = (-1) ^ n * 2 ^ n by rw [← mul_pow]; norm_num]
  have h1 : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  field_simp

@[dlmf 18.10.E2]
theorem legendre_dirichlet_mehler (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    legendreP n (Real.cos θ) = (Real.sqrt 2 / Real.pi *
      ∫ phi : ℝ in (0 : ℝ)..θ, Real.cos ((n + 1 / 2) * phi) / Real.sqrt (Real.cos phi - Real.cos θ) : ℝ) := by
  sorry

section GegenbauerLaplace

open Set

/-- `∫₀^π sin^{2λ-1} = √π Γ(λ)/Γ(λ+1/2)` for `λ > 0`, from the trigonometric Beta integral,
together with the integrability of `sin^{2λ-1}` on `[0, π]`. -/
lemma integral_sin_rpow_aux {lam : ℝ} (hlam : 0 < lam) :
    IntervalIntegrable (fun t : ℝ => Real.sin t ^ (2 * lam - 1)) volume 0 π ∧
    ∫ t in (0 : ℝ)..π, Real.sin t ^ (2 * lam - 1) =
      Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) := by
  have hB := AAR.Gamma.beta_sin_cos (a := lam) (b := 1 / 2) hlam (by norm_num)
  simp only [show 2 * (1 / 2 : ℝ) - 1 = 0 by norm_num, Real.rpow_zero, mul_one,
    Real.Gamma_one_half_eq] at hB
  set f : ℝ → ℝ := fun t => Real.sin t ^ (2 * lam - 1) with hf
  have hpos : 0 < (1 / 2) * (Real.Gamma lam * Real.sqrt π / Real.Gamma (lam + 1 / 2)) := by
    have := Real.Gamma_pos_of_pos hlam
    have := Real.Gamma_pos_of_pos (show 0 < lam + 1 / 2 by linarith)
    have := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  have hI1 : IntervalIntegrable f volume 0 (π / 2) := by
    by_contra h
    rw [intervalIntegral.integral_undef h] at hB
    linarith
  have hsymm : ∀ t, f (π - t) = f t := fun t => by simp [hf, Real.sin_pi_sub]
  have hI2 : IntervalIntegrable f volume (π / 2) π := by
    have := hI1.comp_sub_left π
    simp only [hsymm, sub_zero, show π - π / 2 = π / 2 by ring] at this
    exact this.symm
  refine ⟨hI1.trans hI2, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  have h2 := intervalIntegral.integral_comp_sub_left f (a := 0) (b := π / 2) π
  rw [show π - π / 2 = π / 2 by ring, sub_zero] at h2
  simp only [hsymm] at h2
  rw [← h2, hB]
  ring

/-- The weighted Laplace integral `∫₀^π (cos θ + i sin θ cos φ)ⁿ sin^{2λ-1} φ dφ`. -/
def gegenbauerLaplace (lam θ : ℝ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n *
    ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)

/-- The weighted Laplace integrals satisfy the normalized Gegenbauer recurrence. -/
lemma gegenbauerLaplace_recurrence {lam : ℝ} (hlam : 0 < lam) (θ : ℝ) (n : ℕ) :
    (n + 1 + 2 * lam : ℂ) * gegenbauerLaplace lam θ (n + 2) =
      2 * (n + 1 + lam) * Real.cos θ * gegenbauerLaplace lam θ (n + 1) -
        (n + 1) * gegenbauerLaplace lam θ n := by
  set c : ℂ := (Real.cos θ : ℂ) with hc
  set s : ℂ := (Real.sin θ : ℂ) with hs
  set w : ℝ → ℂ := fun t => c + I * s * Real.cos t with hw
  set ρ : ℝ → ℂ := fun t => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) with hρ
  have hρi : IntervalIntegrable ρ volume 0 π := by
    have := (integral_sin_rpow_aux hlam).1
    exact ⟨this.1.ofReal, this.2.ofReal⟩
  have hU : uIcc (0 : ℝ) π = Icc 0 π := uIcc_of_le Real.pi_pos.le
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq]; simp
  have hsplit : ∀ x : ℝ, 0 ≤ x → x ^ (2 * lam) = x * x ^ (2 * lam - 1) := by
    intro x hx
    rcases hx.eq_or_lt with h | h
    · subst h; rw [Real.zero_rpow (by positivity), zero_mul]
    · rw [← Real.rpow_one_add' h.le (by linarith)]; ring_nf
  -- `F' = ρ g` is the derivative of `F = w^{n+1} sin^{2λ}` on `(0, π)`
  set g : ℝ → ℂ := fun t => (n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) * Real.sin t +
    w t ^ (n + 1) * (2 * lam * Real.cos t) with hg
  have hgc : Continuous g := by fun_prop
  have hD : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivAt (fun t : ℝ => w t ^ (n + 1) *
      ((Real.sin t ^ (2 * lam) : ℝ) : ℂ)) (ρ t * g t) t := by
    intro t ht
    have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have hwd : HasDerivAt w (-(I * s) * Real.sin t) t := by
      have := ((Real.hasDerivAt_cos t).ofReal_comp).const_mul (I * s)
      exact (this.const_add c).congr_deriv (by push_cast; ring)
    have hr := ((Real.hasDerivAt_sin t).rpow_const (p := 2 * lam) (Or.inl hst.ne')).ofReal_comp
    have := (hwd.pow (n + 1)).mul hr
    refine this.congr_deriv ?_
    simp only [hρ, hg, Nat.add_sub_cancel, Pi.pow_apply]
    rw [hsplit _ hst.le]
    push_cast
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
    ((by fun_prop : Continuous fun t : ℝ => w t ^ (n + 1)).continuousOn.mul
      (Complex.continuous_ofReal.comp ((Real.continuous_rpow_const (by positivity)).comp
        Real.continuous_sin)).continuousOn) hD (hρi.mul_continuousOn (hU ▸ hgc.continuousOn))
  simp only [Pi.mul_apply, Function.comp_apply, Real.sin_pi, Real.sin_zero,
    Real.zero_rpow (by positivity : 2 * lam ≠ 0), Complex.ofReal_zero, mul_zero, sub_zero] at hFTC
  -- multiply by `i s`
  have hpt : ∀ t : ℝ, I * s * (ρ t * g t) = ρ t * ((n + 1) * w t ^ n -
      2 * (n + 1 + lam) * c * w t ^ (n + 1) + (n + 1 + 2 * lam) * w t ^ (n + 2)) := by
    intro t
    have htrig : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Real.sin_sq_add_cos_sq]; simp
    simp only [hg, hw]
    linear_combination (ρ t * (n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * (-I ^ 2 * s ^ 2)) *
      htrig - (ρ t * (n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * s ^ 2) * Complex.I_sq +
      (ρ t * (n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n) * hcs
  have h0 : ∫ t : ℝ in (0 : ℝ)..π, I * s * (ρ t * g t) = 0 := by
    rw [intervalIntegral.integral_const_mul, hFTC]; simp
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)] at h0
  have hk : ∀ k : ℕ, IntervalIntegrable (fun t => w t ^ k * ρ t) volume 0 π :=
    fun k => hρi.continuousOn_mul (hU ▸ (by fun_prop : Continuous fun t : ℝ => w t ^ k).continuousOn)
  have hsplit3 : ∀ t : ℝ, ρ t * ((n + 1) * w t ^ n - 2 * (n + 1 + lam) * c * w t ^ (n + 1) +
      (n + 1 + 2 * lam) * w t ^ (n + 2)) = (n + 1) * (w t ^ n * ρ t) -
      2 * (n + 1 + lam) * c * (w t ^ (n + 1) * ρ t) + (n + 1 + 2 * lam) * (w t ^ (n + 2) * ρ t) :=
    fun t => by ring
  rw [intervalIntegral.integral_congr (fun t _ => hsplit3 t),
    intervalIntegral.integral_add (((hk n).const_mul _).sub ((hk (n + 1)).const_mul _))
      ((hk (n + 2)).const_mul _),
    intervalIntegral.integral_sub ((hk n).const_mul _) ((hk (n + 1)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h0
  simp only [gegenbauerLaplace]
  linear_combination h0

@[dlmf 18.10.E4]
theorem gegenbauer_laplace_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (θ : ℝ) :
    gegenbauer lam n (Real.cos θ) / gegenbauer lam n 1 =
      Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) *
        ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ) := by
  obtain ⟨hρi', hρint⟩ := integral_sin_rpow_aux hlam
  set K : ℂ := ((Real.sqrt π * Real.Gamma lam / Real.Gamma (lam + 1 / 2) : ℝ) : ℂ) with hK
  have hG1 : 0 < Real.Gamma (lam + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG2 : 0 < Real.Gamma lam := Real.Gamma_pos_of_pos hlam
  have hsq : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hK0 : K ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hlamC : 0 < (lam : ℂ).re := by simpa using hlam
  -- the normalized polynomials
  set R : ℕ → ℂ := fun n => gegenbauer lam n (Real.cos θ) / gegenbauer lam n 1 with hR
  have hbase0 : gegenbauerLaplace lam θ 0 = K := by
    simp only [gegenbauerLaplace, pow_zero, one_mul, hK]
    rw [intervalIntegral.integral_ofReal, hρint]
  have hcos0 : ∫ t : ℝ in (0 : ℝ)..π, (Real.cos t * Real.sin t ^ (2 * lam - 1) : ℝ) = 0 := by
    have hD : ∀ t ∈ Ioo (0 : ℝ) π, HasDerivAt (fun t : ℝ => Real.sin t ^ (2 * lam) / (2 * lam))
        (Real.cos t * Real.sin t ^ (2 * lam - 1)) t := by
      intro t ht
      have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
      have := ((Real.hasDerivAt_sin t).rpow_const (p := 2 * lam) (Or.inl hst.ne')).div_const
        (2 * lam)
      refine this.congr_deriv ?_
      field_simp
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le Real.pi_pos.le
      (((Real.continuous_rpow_const (by positivity)).comp Real.continuous_sin).div_const
        (2 * lam)).continuousOn hD (hρi'.continuousOn_mul Real.continuous_cos.continuousOn)
    rw [h]
    simp [Real.zero_rpow (by positivity : 2 * lam ≠ 0)]
  have hbase1 : gegenbauerLaplace lam θ 1 = Real.cos θ * K := by
    simp only [gegenbauerLaplace, pow_one]
    have hsplit : ∀ t : ℝ, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) *
        ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) = Real.cos θ * ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) +
          I * Real.sin θ * ((Real.cos t * Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ) := by
      intro t; push_cast; ring
    have hρC : IntervalIntegrable (fun t : ℝ => ((Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ)) volume 0 π :=
      ⟨hρi'.1.ofReal, hρi'.2.ofReal⟩
    have hψ := hρi'.continuousOn_mul Real.continuous_cos.continuousOn
    have hψC : IntervalIntegrable (fun t : ℝ => ((Real.cos t * Real.sin t ^ (2 * lam - 1) : ℝ) : ℂ))
        volume 0 π := ⟨hψ.1.ofReal, hψ.2.ofReal⟩
    rw [intervalIntegral.integral_congr (fun t _ => hsplit t),
      intervalIntegral.integral_add (hρC.const_mul _) (hψC.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, hρint, hcos0, hK]
    simp
  -- induction
  have hind : ∀ n : ℕ, gegenbauerLaplace lam θ n = K * R n ∧
      gegenbauerLaplace lam θ (n + 1) = K * R (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [hbase0]; simp [hR, gegenbauer_zero]
      · rw [hbase1]; simp only [hR, zero_add, gegenbauer_normalized_one hlamC]; ring
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have hr := gegenbauerLaplace_recurrence hlam θ n
      have hP := gegenbauer_normalized_recurrence hlamC n (Real.cos θ)
      rw [ih.1, ih.2] at hr
      have hn : (n + 1 + 2 * lam : ℂ) ≠ 0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith
      apply mul_left_cancel₀ hn
      rw [show n + 1 + 1 = n + 2 by ring, hr]
      simp only [hR]
      linear_combination (-K) * hP
  have hmain := (hind n).1
  have hGam : Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) = K⁻¹ := by
    rw [hK, show (lam + 1 / 2 : ℂ) = ((lam + 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal, Complex.Gamma_ofReal]
    push_cast
    field_simp
  rw [hGam, show (∫ phi : ℝ in (0 : ℝ)..Real.pi, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos phi) ^ n *
      (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ)) = gegenbauerLaplace lam θ n from rfl, hmain]
  field_simp
  rfl

end GegenbauerLaplace

/-- The Laplace integral `∫₀^π (cos θ + i sin θ cos t)^n dt`. -/
def legendreLaplace (θ : ℝ) (n : ℕ) : ℂ :=
  ∫ t : ℝ in (0 : ℝ)..π, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n

/-- The Laplace integrals satisfy the Legendre recurrence. -/
lemma legendreLaplace_recurrence (θ : ℝ) (n : ℕ) :
    (n + 2 : ℂ) * legendreLaplace θ (n + 2) =
      (2 * n + 3) * Real.cos θ * legendreLaplace θ (n + 1) - (n + 1) * legendreLaplace θ n := by
  set c : ℂ := (Real.cos θ : ℂ) with hc
  set s : ℂ := (Real.sin θ : ℂ) with hs
  set w : ℝ → ℂ := fun t => c + I * s * Real.cos t with hw
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    rw [hc, hs, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq]; simp
  -- the exact derivative `d/dt [w^{n+1} sin t]`
  have hD : ∀ t : ℝ, HasDerivAt (fun t : ℝ => w t ^ (n + 1) * (Real.sin t : ℂ))
      ((n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) * Real.sin t +
        w t ^ (n + 1) * Real.cos t) t := by
    intro t
    have hwd : HasDerivAt w (-(I * s) * Real.sin t) t := by
      have := ((Real.hasDerivAt_cos t).ofReal_comp).const_mul (I * s)
      exact (this.const_add c).congr_deriv (by push_cast; ring)
    have := (hwd.pow (n + 1)).mul (Real.hasDerivAt_sin t).ofReal_comp
    exact this.congr_deriv (by simp only [Pi.pow_apply, Nat.add_sub_cancel]; push_cast; ring)
  have hcont : Continuous fun t : ℝ => (n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) *
      Real.sin t + w t ^ (n + 1) * Real.cos t := by fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t)
    (hcont.intervalIntegrable 0 π)
  simp only [Real.sin_pi, Real.sin_zero, Complex.ofReal_zero, mul_zero, sub_zero] at hint
  -- multiply by `i s` and use the pointwise identity
  have hpt : ∀ t : ℝ, I * s * ((n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) * Real.sin t +
      w t ^ (n + 1) * Real.cos t) = (n + 1) * w t ^ n - (2 * n + 3) * c * w t ^ (n + 1) +
        (n + 2) * w t ^ (n + 2) := by
    intro t
    have htrig : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        Real.sin_sq_add_cos_sq]; simp
    simp only [hw]
    linear_combination ((n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * (-I ^ 2 * s ^ 2)) * htrig -
      ((n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n * s ^ 2) * Complex.I_sq +
      ((n + 1 : ℂ) * (c + I * s * Real.cos t) ^ n) * hcs
  have h0 : ∫ t : ℝ in (0 : ℝ)..π, I * s * ((n + 1 : ℂ) * w t ^ n * (-(I * s) * Real.sin t) *
      Real.sin t + w t ^ (n + 1) * Real.cos t) = 0 := by
    rw [intervalIntegral.integral_const_mul, hint]; simp
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)] at h0
  have hc' : ∀ k : ℕ, IntervalIntegrable (fun t : ℝ => w t ^ k) volume 0 π :=
    fun k => (by fun_prop : Continuous fun t : ℝ => w t ^ k).intervalIntegrable 0 π
  rw [intervalIntegral.integral_add (((hc' n).const_mul _).sub ((hc' (n + 1)).const_mul _))
    ((hc' (n + 2)).const_mul _), intervalIntegral.integral_sub ((hc' n).const_mul _)
    ((hc' (n + 1)).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h0
  simp only [legendreLaplace]
  linear_combination h0

@[dlmf 18.10.E5]
theorem legendre_laplace_integral (n : ℕ) (θ : ℝ) :
    legendreP n (Real.cos θ) = (Real.pi : ℂ)⁻¹ *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n := by
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  suffices h : ∀ n : ℕ, legendreLaplace θ n = π * legendreP n (Real.cos θ) ∧
      legendreLaplace θ (n + 1) = π * legendreP (n + 1) (Real.cos θ) by
    rw [show (∫ t : ℝ in (0 : ℝ)..Real.pi, ((Real.cos θ : ℂ) + I * Real.sin θ * Real.cos t) ^ n)
      = legendreLaplace θ n from rfl, (h n).1]
    field_simp
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp [legendreLaplace, legendreP_zero]
    · simp only [legendreLaplace, zero_add, pow_one, legendreP_one]
      rw [intervalIntegral.integral_add intervalIntegrable_const
        ((by fun_prop : Continuous fun t : ℝ => I * (Real.sin θ : ℂ) * Real.cos t
          ).intervalIntegrable 0 π), intervalIntegral.integral_const_mul,
        show ∫ x in (0 : ℝ)..π, ((Real.cos x : ℝ) : ℂ) = ((∫ x in (0 : ℝ)..π, Real.cos x : ℝ) : ℂ)
          from intervalIntegral.integral_ofReal, integral_cos]
      simp
  | succ n ih =>
    refine ⟨ih.2, ?_⟩
    have hr := legendreLaplace_recurrence θ n
    have hP := legendreP_recurrence n (Real.cos θ)
    rw [ih.1, ih.2] at hr
    have hn : (n + 2 : ℂ) ≠ 0 := by norm_cast
    apply mul_left_cancel₀ hn
    rw [hr]
    linear_combination (-(π : ℂ)) * hP

/-- `x^k e^{-xz} e^{-x²}` is integrable for every complex `z`. -/
lemma integrable_pow_mul_cexp_gauss (k : ℕ) (z : ℂ) :
    Integrable fun x : ℝ => (x : ℂ) ^ k * (cexp (-x * z) * cexp (-(x : ℂ) ^ 2)) := by
  have hreal : Integrable fun x : ℝ => x ^ k * Real.exp (-(1 / 2) * x ^ 2) := by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
      (s := (k : ℝ)) (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith)
    refine h.congr (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.rpow_natCast]
  have hg : Integrable fun x : ℝ => (x : ℂ) ^ k * cexp (-(x : ℂ) ^ 2 / 2) := by
    refine hreal.norm.mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp, norm_pow,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    apply le_of_eq
    congr 2
    simp [sq]; ring
  set a := z.re
  have hbd : ∀ x : ℝ, ‖cexp (-x * z - (x : ℂ) ^ 2 / 2)‖ ≤ Real.exp (a ^ 2 / 2) := by
    intro x
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have : (-x * z - (x : ℂ) ^ 2 / 2).re = -x * a - x ^ 2 / 2 := by
      simp [a, sq]
    rw [this]
    nlinarith [sq_nonneg (x + a)]
  have hm : AEStronglyMeasurable (fun x : ℝ => cexp (-x * z - (x : ℂ) ^ 2 / 2)) volume :=
    (by fun_prop : Continuous fun x : ℝ => cexp (-x * z - (x : ℂ) ^ 2 / 2)).aestronglyMeasurable
  refine (hg.bdd_mul hm (Eventually.of_forall hbd)).congr (Eventually.of_forall fun x => ?_)
  beta_reduce
  have e : cexp (-↑x * z - (x : ℂ) ^ 2 / 2) * cexp (-(x : ℂ) ^ 2 / 2) =
      cexp (-↑x * z) * cexp (-(x : ℂ) ^ 2) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  linear_combination (x : ℂ) ^ k * e

/-- A polynomial times `e^{-xz} e^{-x²}` is integrable. -/
lemma integrable_eval_mul_cexp_gauss (q : ℝ[X]) (z : ℂ) :
    Integrable fun x : ℝ => cexp (-x * z) * ((q.eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) := by
  have hq : ∀ x : ℝ, cexp (-x * z) * ((q.eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      ∑ i ∈ Finset.range (q.natDegree + 1),
        (q.coeff i : ℂ) * ((x : ℂ) ^ i * (cexp (-x * z) * cexp (-(x : ℂ) ^ 2))) := fun x => by
    rw [eval_eq_sum_range, Finset.sum_mul]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  simp_rw [hq]
  exact integrable_finsetSum _ fun i _ => (integrable_pow_mul_cexp_gauss i z).const_mul _

/-- Repeated integration by parts against `e^{-xz}`. -/
lemma integral_cexp_mul_hermite_gauss (z : ℂ) (n : ℕ) :
    ∫ x : ℝ, cexp (-x * z) * (((hermitePhysR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      (-z) ^ n * ∫ x : ℝ, cexp (-x * z) * ((Real.exp (-(x ^ 2)) : ℝ) : ℂ) := by
  induction n with
  | zero => simp [hermitePhysR]
  | succ n ih =>
    have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => cexp (-y * z)) (cexp (-x * z) * (-z)) x := by
      intro x
      have := ((hasDerivAt_id (x : ℂ)).neg.mul_const z).cexp.comp_ofReal (z := x)
      simpa using this
    have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (((hermitePhysR n).eval y * Real.exp (-(y ^ 2)) : ℝ) : ℂ))
        (-((((hermitePhysR (n + 1)).eval x * Real.exp (-(x ^ 2))) : ℝ) : ℂ)) x := by
      intro x
      have := (hasDerivAt_hermite_gauss n x).ofReal_comp
      simpa using this
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hu x) (fun x _ => hv x)
      ((integrable_eval_mul_cexp_gauss (hermitePhysR (n + 1)) z).neg.congr
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply, Pi.neg_apply]; ring))
      (((integrable_eval_mul_cexp_gauss (hermitePhysR n) z).const_mul (-z)).congr
        (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring))
      (integrable_eval_mul_cexp_gauss (hermitePhysR n) z)
    have h1 : ∫ x : ℝ, cexp (-x * z) * (((hermitePhysR (n + 1)).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
        -∫ x : ℝ, cexp (-x * z) * -((((hermitePhysR (n + 1)).eval x * Real.exp (-(x ^ 2))) : ℝ) : ℂ) := by
      rw [← integral_neg]; congr 1; funext x; ring
    rw [h1, hibp, neg_neg]
    have h2 : ∫ x : ℝ, cexp (-x * z) * (-z) * (((hermitePhysR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
        -z * ∫ x : ℝ, cexp (-x * z) * (((hermitePhysR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    rw [h2, ih, pow_succ]
    ring

/-- `∫ e^{-xz} e^{-x²} dx = √π e^{z²/4}`. -/
lemma integral_cexp_gauss (z : ℂ) :
    ∫ x : ℝ, cexp (-x * z) * ((Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      (Real.sqrt Real.pi : ℂ) * cexp (z ^ 2 / 4) := by
  have h := integral_cexp_quadratic (b := -1) (by simp) (-z) 0
  have heq : ∀ x : ℝ, cexp (-x * z) * ((Real.exp (-(x ^ 2)) : ℝ) : ℂ) =
      cexp (-1 * (x : ℂ) ^ 2 + -z * x + 0) := fun x => by
    rw [ofReal_exp, ← Complex.exp_add]; push_cast; ring_nf
  simp_rw [heq, h]
  rw [neg_neg, div_one, show (0 : ℂ) - (-z) ^ 2 / (4 * -1) = z ^ 2 / 4 by ring]
  congr 1
  rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]
  norm_num

/-- The Laplace transform of `Hₙ e^{-x²}`. -/
lemma hermite_laplace_aux (n : ℕ) (z : ℂ) :
    ∫ x : ℝ, exp (-x * z) * (aeval (x : ℂ) (hermitePhys n) : ℂ) * exp (-(x : ℂ) ^ 2) =
      Real.sqrt Real.pi * (-z) ^ n * exp (z ^ 2 / 4) := by
  have heq : ∀ x : ℝ, exp (-x * z) * (aeval (x : ℂ) (hermitePhys n) : ℂ) * exp (-(x : ℂ) ^ 2) =
      cexp (-x * z) * (((hermitePhysR n).eval x * Real.exp (-(x ^ 2)) : ℝ) : ℂ) := fun x => by
    have : (aeval (x : ℂ) (hermitePhys n) : ℂ) = (((hermitePhysR n).eval x : ℝ) : ℂ) := by
      rw [← aeval_hermitePhys_eq_eval]
      exact aeval_algebraMap_apply ℂ x (hermitePhys n)
    rw [this, ofReal_mul, ofReal_exp]; push_cast; ring
  simp_rw [heq]
  rw [integral_cexp_mul_hermite_gauss, integral_cexp_gauss]
  ring

/-- `(x+it)^n t^j e^{-t²}` is integrable. -/
lemma integrable_add_I_pow_mul_pow_gauss (x : ℂ) (n j : ℕ) :
    Integrable fun t : ℝ => (x + I * t) ^ n * ((t : ℂ) ^ j * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) := by
  have hq : ∀ t : ℝ, (x + I * t) ^ n * ((t : ℂ) ^ j * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) =
      ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℂ) * x ^ (n - k) * I ^ k) *
        ((t : ℂ) ^ (k + j) * (cexp (-t * 0) * cexp (-(t : ℂ) ^ 2))) := fun t => by
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ofReal_exp]; push_cast; simp; ring
  simp_rw [hq]
  exact integrable_finsetSum _ fun k _ => (integrable_pow_mul_cexp_gauss (k + j) 0).const_mul _

/-- `(x+it)^n e^{-t²}` is integrable. -/
lemma integrable_add_I_pow_gauss (x : ℂ) (n : ℕ) :
    Integrable fun t : ℝ => (x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
  simpa using integrable_add_I_pow_mul_pow_gauss x n 0

/-- One integration by parts: `∫ t (x+it)^n e^{-t²} = (i n / 2) ∫ (x+it)^{n-1} e^{-t²}`. -/
lemma integral_t_mul_add_I_pow (x : ℂ) (n : ℕ) :
    ∫ t : ℝ, (x + I * t) ^ (n + 1) * ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) =
      I * (n + 1) / 2 * ∫ t : ℝ, (x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
  have hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (x + I * s) ^ (n + 1))
      ((n + 1 : ℂ) * (x + I * t) ^ n * I) t := by
    intro t
    have := (((hasDerivAt_id (t : ℂ)).const_mul I).const_add x).pow (n + 1) |>.comp_ofReal (z := t)
    simpa using this
  have hv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((-(Real.exp (-(s ^ 2))) / 2 : ℝ) : ℂ))
      (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(Real.exp (-(s ^ 2))) / 2) (t * Real.exp (-(t ^ 2))) t := by
      have := (((hasDerivAt_pow 2 t).neg).exp.neg).div_const 2
      convert this using 1; simp; ring
    exact h1.ofReal_comp
  have hI := integrable_add_I_pow_gauss x n
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hu t) (fun t _ => hv t)
    ?_ ?_ ?_
  · rw [hibp]
    rw [show (fun t : ℝ => (n + 1 : ℂ) * (x + I * t) ^ n * I * ((-(Real.exp (-(t ^ 2))) / 2 : ℝ) : ℂ))
      = fun t => -(I * (n + 1) / 2) * ((x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) by
        funext t; push_cast; ring, integral_const_mul]
    ring
  · refine (integrable_add_I_pow_mul_pow_gauss x (n + 1) 1).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; push_cast; ring
  · refine ((integrable_add_I_pow_gauss x n).const_mul (-(I * (n + 1) / 2))).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; push_cast; ring
  · refine ((integrable_add_I_pow_gauss x (n + 1)).const_mul (-(1 / 2))).congr
      (Eventually.of_forall fun t => ?_)
    simp only [Pi.mul_apply]; push_cast; ring

@[dlmf 18.10.E7]
theorem hermitePhys_laplace_integral (n : ℕ) (x : ℂ) :
    aeval x (hermitePhys n) = (2 : ℂ) ^ n / Real.sqrt Real.pi *
      ∫ t : ℝ, (x + I * t) ^ n * Real.exp (-(t ^ 2)) := by
  set F : ℕ → ℂ := fun n => ∫ t : ℝ, (x + I * t) ^ n * ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) with hF
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hF0 : F 0 = Real.sqrt Real.pi := by
    simp only [hF, pow_zero, one_mul]
    rw [integral_complex_ofReal, show (fun t : ℝ => Real.exp (-(t ^ 2))) =
      fun t => Real.exp (-1 * t ^ 2) by funext t; ring_nf, integral_gaussian, div_one]
  have hodd : ∫ t : ℝ, ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) = 0 := by
    have h := integral_neg_eq_self (fun t : ℝ => ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ)) volume
    simp only [neg_mul, neg_sq, ofReal_neg, integral_neg] at h
    linear_combination (-1 / 2 : ℂ) * h
  have hF1 : F 1 = x * Real.sqrt Real.pi := by
    have : F 1 = x * F 0 + I * ∫ t : ℝ, ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
      simp only [hF, pow_one, pow_zero, one_mul]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
      · congr 1; funext t; push_cast; try ring
      · exact (integrable_add_I_pow_gauss x 0).const_mul x |>.congr
          (Eventually.of_forall fun t => by simp)
      · exact ((integrable_add_I_pow_mul_pow_gauss 0 0 1).const_mul I).congr
          (Eventually.of_forall fun t => by simp)
    rw [this, hodd, hF0]; ring
  have hrec : ∀ n : ℕ, F (n + 2) = x * F (n + 1) - (n + 1) / 2 * F n := by
    intro n
    have hsplit : F (n + 2) = x * F (n + 1) +
        I * ∫ t : ℝ, (x + I * t) ^ (n + 1) * ((t * Real.exp (-(t ^ 2)) : ℝ) : ℂ) := by
      simp only [hF]
      rw [← integral_const_mul, ← integral_const_mul, ← integral_add
        ((integrable_add_I_pow_gauss x (n + 1)).const_mul x)
        (((integrable_add_I_pow_mul_pow_gauss x (n + 1) 1).const_mul I).congr
          (Eventually.of_forall fun t => by simp only; push_cast; ring))]
      congr 1; funext t; push_cast; ring
    rw [hsplit, integral_t_mul_add_I_pow]
    simp only [hF]
    rw [show I * (I * ((n : ℂ) + 1) / 2 * ∫ t : ℝ, (x + I * t) ^ n *
      ((Real.exp (-(t ^ 2)) : ℝ) : ℂ)) = I ^ 2 * (((n : ℂ) + 1) / 2) * ∫ t : ℝ, (x + I * t) ^ n *
      ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) by ring, I_sq]
    ring
  have key : ∀ n : ℕ, (2 : ℂ) ^ n * F n = Real.sqrt Real.pi * aeval x (hermitePhys n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [hF0]
    | one => rw [hF1, hermitePhys_one, map_mul, aeval_X, map_ofNat]; ring
    | more n ih0 ih1 =>
      rw [hrec, aeval_hermitePhys_succ_succ]
      linear_combination 2 * x * ih1 - 2 * ((n : ℂ) + 1) * ih0
  have hn := key n
  simp only [hF] at hn
  field_simp
  linear_combination -hn

/-- `e^{-t²} tⁿ e^{2ixt}` is integrable. -/
lemma integrable_gauss_pow_cexp (x : ℝ) (n : ℕ) :
    Integrable fun t : ℝ => ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n * cexp (2 * I * x * t) := by
  refine (integrable_pow_mul_cexp_gauss n (-2 * I * x)).congr (Eventually.of_forall fun t => ?_)
  simp only [ofReal_exp]
  push_cast
  rw [show -(t : ℂ) * (-2 * I * x) = 2 * I * x * t by ring]
  ring

/-- The moment recurrence for `∫ e^{-t²} tⁿ e^{2ixt} dt`. -/
lemma integral_K_succ_succ (x : ℝ) (n : ℕ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 2) * cexp (2 * I * x * t) =
      I * x * (∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 1) * cexp (2 * I * x * t)) +
      (n + 1) / 2 * ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n * cexp (2 * I * x * t) := by
  have hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (s : ℂ) ^ (n + 1) * cexp (2 * I * x * s))
      (((n + 1 : ℂ) * (t : ℂ) ^ n) * cexp (2 * I * x * t) +
        (t : ℂ) ^ (n + 1) * (cexp (2 * I * x * t) * (2 * I * x))) t := by
    intro t
    have h1 := (hasDerivAt_pow (n + 1) (t : ℂ)).comp_ofReal
    have h2 := ((hasDerivAt_id (t : ℂ)).const_mul (2 * I * x)).cexp.comp_ofReal (z := t)
    simp only [id, mul_one] at h2
    refine (h1.mul h2).congr_deriv ?_
    push_cast; ring
  have hv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((-(Real.exp (-(s ^ 2))) / 2 : ℝ) : ℂ))
      (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(Real.exp (-(s ^ 2))) / 2) (t * Real.exp (-(t ^ 2))) t := by
      have := (((hasDerivAt_pow 2 t).neg).exp.neg).div_const 2
      convert this using 1; simp; ring
    exact h1.ofReal_comp
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hu t) (fun t _ => hv t)
    ((integrable_gauss_pow_cexp x (n + 2)).congr (Eventually.of_forall fun t => by
      simp only [Pi.mul_apply]; push_cast; ring))
    ((((integrable_gauss_pow_cexp x n).const_mul (-((n : ℂ) + 1) / 2)).add
      ((integrable_gauss_pow_cexp x (n + 1)).const_mul (-(I * x)))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply, Pi.add_apply]; push_cast; ring))
    (((integrable_gauss_pow_cexp x (n + 1)).const_mul (-(1 / 2))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
  have e1 : ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 2) * cexp (2 * I * x * t) =
      ∫ t : ℝ, (t : ℂ) ^ (n + 1) * cexp (2 * I * x * t) * (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) := by
    congr 1; funext t; push_cast; ring
  rw [e1, hibp]
  rw [show (fun t : ℝ => (((n + 1 : ℂ) * (t : ℂ) ^ n) * cexp (2 * I * x * t) +
      (t : ℂ) ^ (n + 1) * (cexp (2 * I * x * t) * (2 * I * x))) * ((-(Real.exp (-(t ^ 2))) / 2 : ℝ) : ℂ))
      = fun t => (-((n : ℂ) + 1) / 2) * (((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n *
          cexp (2 * I * x * t)) + (-(I * x)) * (((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 1) *
          cexp (2 * I * x * t)) by funext t; push_cast; ring]
  rw [integral_add ((integrable_gauss_pow_cexp x n).const_mul _)
    ((integrable_gauss_pow_cexp x (n + 1)).const_mul _), integral_const_mul, integral_const_mul]
  ring

/-- The Fourier transform of the Gaussian. -/
lemma integral_K_zero (x : ℝ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 0 * cexp (2 * I * x * t) =
      Real.sqrt Real.pi * cexp (-(x : ℂ) ^ 2) := by
  have h := integral_cexp_gauss (-2 * I * x)
  rw [show (-2 * I * (x : ℂ)) ^ 2 / 4 = -(x : ℂ) ^ 2 by ring_nf; rw [I_sq]; ring] at h
  rw [← h]
  congr 1; funext t
  rw [show -(t : ℂ) * (-2 * I * x) = 2 * I * x * t by ring]
  ring

/-- The first moment of the Gaussian Fourier kernel. -/
lemma integral_K_one (x : ℝ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 1 * cexp (2 * I * x * t) =
      I * x * ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 0 * cexp (2 * I * x * t) := by
  have hu : ∀ t : ℝ, HasDerivAt (fun s : ℝ => cexp (2 * I * x * s))
      (cexp (2 * I * x * t) * (2 * I * x)) t := by
    intro t
    have h2 := ((hasDerivAt_id (t : ℂ)).const_mul (2 * I * x)).cexp.comp_ofReal (z := t)
    simpa using h2
  have hv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((-(Real.exp (-(s ^ 2))) / 2 : ℝ) : ℂ))
      (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(Real.exp (-(s ^ 2))) / 2) (t * Real.exp (-(t ^ 2))) t := by
      have := (((hasDerivAt_pow 2 t).neg).exp.neg).div_const 2
      convert this using 1; simp; ring
    exact h1.ofReal_comp
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun t _ => hu t) (fun t _ => hv t)
    ((integrable_gauss_pow_cexp x 1).congr (Eventually.of_forall fun t => by
      simp only [Pi.mul_apply]; push_cast; ring))
    (((integrable_gauss_pow_cexp x 0).const_mul (-(I * x))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
    (((integrable_gauss_pow_cexp x 0).const_mul (-(1 / 2))).congr
      (Eventually.of_forall fun t => by simp only [Pi.mul_apply]; push_cast; ring))
  have e1 : ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 1 * cexp (2 * I * x * t) =
      ∫ t : ℝ, cexp (2 * I * x * t) * (((t * Real.exp (-(t ^ 2))) : ℝ) : ℂ) := by
    congr 1; funext t; push_cast; ring
  rw [e1, hibp, show (fun t : ℝ => cexp (2 * I * x * t) * (2 * I * x) *
      ((-(Real.exp (-(t ^ 2))) / 2 : ℝ) : ℂ)) = fun t => (-(I * x)) *
      (((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ 0 * cexp (2 * I * x * t)) by
      funext t; push_cast; ring, integral_const_mul]
  ring

@[dlmf 18.10.E10]
theorem hermitePhys_fourier_integral (n : ℕ) (x : ℝ) :
    (aeval (x : ℂ) (hermitePhys n) : ℂ) = (-2 * I) ^ n * exp ((x : ℂ) ^ 2) / Real.sqrt Real.pi *
      ∫ t : ℝ, Real.exp (-(t ^ 2)) * (t : ℂ) ^ n * exp (2 * I * x * t) := by
  set K : ℕ → ℂ := fun n => ∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n *
    cexp (2 * I * x * t) with hK
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hE : cexp ((x : ℂ) ^ 2) * cexp (-(x : ℂ) ^ 2) = 1 := by rw [← Complex.exp_add]; simp
  have key : ∀ n : ℕ, (-2 * I) ^ n * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi * K n =
      aeval (x : ℂ) (hermitePhys n) := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero =>
      simp only [hK]
      rw [integral_K_zero]
      field_simp
      simp [hE]
    | one =>
      simp only [hK]
      rw [integral_K_one, integral_K_zero, hermitePhys_one, map_mul, aeval_X, map_ofNat]
      generalize (Real.sqrt Real.pi : ℂ) = sp at hπ ⊢
      field_simp
      linear_combination (-(x : ℂ) * I ^ 2) * hE + (-(x : ℂ)) * I_sq
    | more n ih0 ih1 =>
      simp only [hK] at ih0 ih1 ⊢
      rw [integral_K_succ_succ, aeval_hermitePhys_succ_succ, ← ih0, ← ih1]
      generalize (∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ (n + 1) *
        cexp (2 * I * x * t)) = A
      generalize (∫ t : ℝ, ((Real.exp (-(t ^ 2)) : ℝ) : ℂ) * (t : ℂ) ^ n *
        cexp (2 * I * x * t)) = B
      set P := (-2 * I) ^ n * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi
      rw [show (-2 * I) ^ (n + 2) * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi = P * (-2 * I) ^ 2 by
        simp only [P]; ring,
        show (-2 * I) ^ (n + 1) * cexp ((x : ℂ) ^ 2) / Real.sqrt Real.pi = P * (-2 * I) by
        simp only [P]; ring]
      linear_combination (4 * P * I * x * A + 2 * P * ((n : ℂ) + 1) * B) * I_sq
  rw [← key n]

/-- An interval antiderivative of the physicists’ Hermite polynomial. -/
@[dlmf 18.17.E3]
theorem hermitePhys_integral (n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, (aeval y (hermitePhys n) : ℝ) =
      (aeval x (hermitePhys (n + 1)) - aeval (0 : ℝ) (hermitePhys (n + 1))) / (2 * (n + 1)) := by
  have hd (t : ℝ) : HasDerivAt (fun y : ℝ => aeval y (hermitePhys (n + 1)))
      (2 * (n + 1) * aeval t (hermitePhys n)) t := by
    have h := (hermitePhys (n + 1)).hasDerivAt_aeval t
    rw [hermitePhys_derivative] at h
    simpa only [map_mul, aeval_C, map_ofNat, map_add, map_natCast, map_one] using h
  have hi : IntervalIntegrable (fun t : ℝ => 2 * (n + 1) * aeval t (hermitePhys n))
      volume 0 x := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at h
  apply (eq_div_iff (by positivity : (2 * (n + 1) : ℝ) ≠ 0)).mpr
  nlinarith [h]

/-- An interval antiderivative of a Gaussian-weighted physicists’ Hermite polynomial. -/
@[dlmf 18.17.E4]
theorem hermitePhys_weighted_integral (n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, Real.exp (-(y ^ 2)) * (aeval y (hermitePhys (n + 1)) : ℝ) =
      aeval (0 : ℝ) (hermitePhys n) - Real.exp (-(x ^ 2)) * aeval x (hermitePhys n) := by
  let g : ℝ → ℝ := fun t => Real.exp (-(t ^ 2)) * aeval t (hermitePhys n)
  have hd (t : ℝ) : HasDerivAt (fun y => -g y)
      (Real.exp (-(t ^ 2)) * aeval t (hermitePhys (n + 1))) t := by
    have hg : DifferentiableAt ℝ g t :=
      (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => Real.exp (-(t ^ 2))) t).mul
        ((hermitePhys n).hasDerivAt_aeval t).differentiableAt
    have ht := hg.hasDerivAt.neg
    change HasDerivAt (fun y => -g y) (-deriv g t) t at ht
    simpa only [g, AAR.OrthogonalPolynomials.hermitePhys_weighted_derivative, neg_mul, neg_neg]
      using ht
  have hi : IntervalIntegrable
      (fun y : ℝ => Real.exp (-(y ^ 2)) * (aeval y (hermitePhys (n + 1)) : ℝ)) volume 0 x :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa only [g, zero_pow (by decide : 2 ≠ 0), neg_zero, Real.exp_zero, one_mul,
    neg_sub_neg] using h

@[dlmf 18.17.E6]
theorem legendre_product_integral (n : ℕ) (θ ψ : ℝ) :
    legendreP n (Real.cos θ) * legendreP n (Real.cos ψ) = (Real.pi : ℂ)⁻¹ *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, legendreP n
        (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) := by
  sorry

/-- Gamma normalization converts Laguerre polynomials into the regularized Kummer
function. This uses Mathlib's Gamma/Pochhammer relation at regular parameters. -/
lemma laguerre_div_Gamma_eq_regularized {α : ℝ} (hα : -1 < α) (n : ℕ) (y : ℂ) :
    laguerre α n y / Gamma ((α : ℂ) + n + 1) =
      regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} y / (n.factorial : ℂ) := by
  have hp : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp; linarith)
  have hG : Gamma ((α : ℂ) + n + 1) = poch ((α : ℂ) + 1) n * Gamma ((α : ℂ) + 1) := by
    have h := Gamma_add_nat_div_Gamma_eq (n := n) ((α : ℂ) + 1) hp
    rw [show (α : ℂ) + n + 1 = (α : ℂ) + 1 + n by ring]
    exact (div_eq_iff (Gamma_ne_zero hp)).mp h
  rw [laguerre, confluentM_eq_mul_regularizedHGFun hp, hG]
  field [Gamma_ne_zero hp, poch_ne_zero_of_not_neg_nat hp n]

@[dlmf 18.17.E14]
theorem laguerre_fractional_integral {α μ x : ℝ} (hα : -1 < α) (hμ : 0 < μ) (hx : 0 < x) (n : ℕ) :
    (x : ℂ) ^ ((α : ℂ) + μ) * laguerre (α + μ) n x / Gamma (α + μ + n + 1 : ℂ) =
      ∫ y : ℝ in (0 : ℝ)..x, (y : ℂ) ^ (α : ℂ) * laguerre α n y / Gamma (α + n + 1 : ℂ) *
        (x - y : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ) := by
  let f : ℝ → ℂ := fun y => (y : ℂ) ^ (α : ℂ) *
    regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} y *
      ((x : ℂ) - y) ^ ((μ : ℂ) - 1)
  let g : ℝ → ℂ := fun t =>
    regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} ((x : ℂ) * t) *
      (t : ℂ) ^ (α : ℂ) * (1 - (t : ℂ)) ^ ((μ : ℂ) - 1)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hscale : (∫ y : ℝ in (0 : ℝ)..x, f y) =
      (x : ℂ) ^ ((α : ℂ) + μ) * ∫ t : ℝ in (0 : ℝ)..1, g t := by
    have hs := intervalIntegral.smul_integral_comp_mul_left f x (a := (0 : ℝ)) (b := 1)
    simp only [mul_zero, mul_one, Complex.real_smul] at hs
    rw [← hs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have hxp : (x : ℂ) * (x : ℂ) ^ (α : ℂ) * (x : ℂ) ^ ((μ : ℂ) - 1) =
        (x : ℂ) ^ ((α : ℂ) + μ) := by
      calc
        _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (α : ℂ) *
            (x : ℂ) ^ ((μ : ℂ) - 1) := by rw [cpow_one]
        _ = _ := by
          rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]
          congr 1
          ring
    have hptail : ((x : ℂ) * (1 - (t : ℂ))) ^ ((μ : ℂ) - 1) =
        (x : ℂ) ^ ((μ : ℂ) - 1) * (1 - (t : ℂ)) ^ ((μ : ℂ) - 1) := by
      simpa only [ofReal_sub, ofReal_one] using
        mul_cpow_ofReal_nonneg hx.le (sub_nonneg.mpr ht.2.le) ((μ : ℂ) - 1)
    dsimp [f, g]
    simp only [ofReal_mul]
    rw [show (x : ℂ) - (x : ℂ) * t = (x : ℂ) * (1 - (t : ℂ)) by ring,
      mul_cpow_ofReal_nonneg hx.le ht.1.le, hptail]
    linear_combination (t : ℂ) ^ (α : ℂ) *
      regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + 1} ((x : ℂ) * t) *
      (1 - (t : ℂ)) ^ ((μ : ℂ) - 1) * hxp
  have hR := AAR.Confluent.regularized_parameter_integral (a := -(n : ℂ))
    (b := (α : ℂ) + μ + 1) (c := (α : ℂ) + 1) (z := x)
    (by simp; linarith) (by simp; linarith)
  rw [show (α : ℂ) + 1 - 1 = (α : ℂ) by ring,
    show (α : ℂ) + μ + 1 - ((α : ℂ) + 1) = (μ : ℂ) by ring] at hR
  change regularizedHGFun {(-(n : ℂ))} {(α : ℂ) + μ + 1} x =
    1 / Gamma (μ : ℂ) * ∫ t : ℝ in (0 : ℝ)..1, g t at hR
  have hrhs : (∫ y : ℝ in (0 : ℝ)..x,
      (y : ℂ) ^ (α : ℂ) * laguerre α n y / Gamma (α + n + 1 : ℂ) *
        (x - y : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ)) =
      (∫ y : ℝ in (0 : ℝ)..x, f y) / ((n.factorial : ℂ) * Gamma (μ : ℂ)) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [show (y : ℂ) ^ (α : ℂ) * laguerre α n y / Gamma (α + n + 1 : ℂ) =
      (y : ℂ) ^ (α : ℂ) * (laguerre α n y / Gamma (α + n + 1 : ℂ)) by ring,
      laguerre_div_Gamma_eq_regularized hα]
    dsimp [f]
    push_cast
    ring
  have hL := laguerre_div_Gamma_eq_regularized (by linarith : -1 < α + μ) n (x : ℂ)
  push_cast at hL
  rw [hrhs, hscale, show (x : ℂ) ^ ((α : ℂ) + μ) * laguerre (α + μ) n x /
      Gamma (α + μ + n + 1 : ℂ) = (x : ℂ) ^ ((α : ℂ) + μ) *
      (laguerre (α + μ) n x / Gamma (α + μ + n + 1 : ℂ)) by ring,
    hL]
  push_cast
  rw [hR]
  ring

@[dlmf 18.17.E15]
theorem laguerre_fractional_tail_integral {α μ x : ℝ} (hα : -1 < α) (hμ : 0 < μ) (hx : 0 ≤ x) (n : ℕ) :
    exp (-x) * laguerre α n x = ∫ y : ℝ in Set.Ioi x,
      exp (-y) * laguerre (α + μ) n y * (y - x : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ) := by
  have hβ : -1 < μ - 1 := by linarith
  have hp (a : ℝ) (ha : -1 < a) : ∀ k : ℕ, (a : ℂ) + 1 ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp; linarith)
  have hΓ : Gamma (μ : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hμ)
  have hadd (y : ℝ) : laguerre (α + μ) n ((x : ℂ) + y) =
      ∑ k ∈ Finset.range (n + 1), laguerre α k x * laguerre (μ - 1) (n - k) y := by
    have h := laguerre_addition (α : ℂ) ((μ - 1 : ℝ) : ℂ) x y n
    have hparam : (α : ℂ) + ((μ - 1 : ℝ) : ℂ) + 1 = ((α + μ : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hparam, laguerreExtended_eq (hp (α + μ) (by linarith))] at h
    simp only [laguerreExtended_eq (hp α hα), laguerreExtended_eq (hp (μ - 1) hβ)] at h
    simpa only [ofReal_add, ofReal_sub, ofReal_one] using h
  let f : ℕ → ℝ → ℂ := fun k y => laguerre (μ - 1) k y *
    (y : ℂ) ^ ((μ : ℂ) - 1) * exp (-(y : ℂ))
  have hint (k : ℕ) : IntegrableOn (f k) (Set.Ioi 0) := by
    have h := integrable_laguerre_mul_monomial hβ k 0
    simpa only [IntegrableOn, f, pow_zero, mul_one, ofReal_sub, ofReal_one] using h
  have hmoment (k : ℕ) : (∫ y : ℝ in Set.Ioi 0, f k y) =
      if k = 0 then Gamma (μ : ℂ) else 0 := by
    have h := integral_laguerre_mul_monomial hβ k 0
    simp only [pow_zero, mul_one, ofReal_sub, ofReal_one, Nat.cast_zero, neg_zero,
      add_zero, sub_add_cancel] at h
    change (∫ y : ℝ in Set.Ioi 0, f k y) = _ at h
    rw [h]
    cases k with
    | zero => simp [poch_zero]
    | succ k => simp [poch_succ, poch_zero]
  let F : ℝ → ℂ := fun y => exp (-(y : ℂ)) * laguerre (α + μ) n y *
    ((y : ℂ) - x) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ)
  have hshift := (measurePreserving_add_left (volume : Measure ℝ) x).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft x).measurableEmbedding F (Set.Ioi x)
  have hpre : (fun y : ℝ => x + y) ⁻¹' Set.Ioi x = Set.Ioi 0 := by
    ext y
    simp
  rw [hpre] at hshift
  change exp (-x) * laguerre α n x = ∫ y : ℝ in Set.Ioi x, F y
  rw [← hshift]
  have heq (y : ℝ) : F (x + y) = exp (-x) / Gamma (μ : ℂ) *
      ∑ k ∈ Finset.range (n + 1), laguerre α k x * f (n - k) y := by
    dsimp [F, f]
    rw [ofReal_add, add_sub_cancel_left, neg_add, exp_add, hadd]
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y _ => heq y), integral_const_mul,
    integral_finsetSum _ (fun k _ => (hint (n - k)).const_mul (laguerre α k x))]
  simp only [integral_const_mul, hmoment]
  rw [Finset.sum_eq_single n]
  · simp only [Nat.sub_self, ↓reduceIte]
    field [hΓ]
  · intro k hk hkn
    have hk' : k < n := by have := Finset.mem_range.mp hk; omega
    simp [Nat.sub_ne_zero_of_lt hk']
  · simp

@[dlmf 18.17.E21_2]
theorem hermitePhys_fourier_transform (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2) * (aeval (x : ℂ) (hermitePhys n) : ℂ) * exp (I * x * y)) /
      Real.sqrt Real.pi = I ^ n * exp (-(y : ℂ) ^ 2 / 4) * (y : ℂ) ^ n := by
  have h := hermite_laplace_aux n (-I * y)
  have heq : ∀ x : ℝ, exp (-(x : ℂ) ^ 2) * (aeval (x : ℂ) (hermitePhys n) : ℂ) * exp (I * x * y) =
      exp (-x * (-I * y)) * (aeval (x : ℂ) (hermitePhys n) : ℂ) * exp (-(x : ℂ) ^ 2) := fun x => by
    rw [show -(x : ℂ) * (-I * y) = I * x * y by ring]; ring
  simp_rw [heq]
  rw [h]
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [show -(-I * (y : ℂ)) = I * y by ring, mul_pow,
    show (-I * (y : ℂ)) ^ 2 / 4 = -(y : ℂ) ^ 2 / 4 by ring_nf; rw [I_sq]; ring]
  field_simp

/-- TauCeti's Hermite functions with the positive, unit-frequency Fourier convention. -/
lemma hermiteFunction_integral (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, Complex.exp (I * x * y) * (TauCeti.hermiteFunction n x : ℂ)) =
      (Real.sqrt (2 * Real.pi) : ℂ) * I ^ n * (TauCeti.hermiteFunction n y : ℂ) := by
  let s := Real.sqrt (2 * Real.pi)
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)
  have hs0 : s ≠ 0 := hs.ne'
  have hs2 : s ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have ha : (Real.sqrt s : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'
  have he := congrFun (TauCeti.fourier_twoPiHermiteFunction n) (-y / s)
  rw [Real.fourier_real_eq_integral_exp_smul] at he
  have hphase (x : ℝ) : (↑(-2 * Real.pi * x * (-y / s)) : ℂ) * I = I * (s * x) * y := by
    rw [show -2 * Real.pi * x * (-y / s) = s * x * y by
      calc
        _ = (2 * Real.pi) * x * y / s := by ring
        _ = _ := by rw [← hs2]; field_simp]
    push_cast
    ring
  simp_rw [hphase, smul_eq_mul, TauCeti.twoPiHermiteFunction_def, ofReal_mul] at he
  have harg : s * (-y / s) = -y := by field_simp
  change (∫ x : ℝ, exp (I * (s * x) * y) * ((Real.sqrt s : ℂ) * ↑(TauCeti.hermiteFunction n (s * x)))) =
    (-I) ^ n * ((Real.sqrt s : ℂ) * ↑(TauCeti.hermiteFunction n (s * (-y / s)))) at he
  rw [harg, TauCeti.hermiteFunction_neg, ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one] at he
  have hmul : (-I) ^ n * ((Real.sqrt s : ℂ) * ((-1) ^ n * ↑(TauCeti.hermiteFunction n y))) =
      (Real.sqrt s : ℂ) * (I ^ n * ↑(TauCeti.hermiteFunction n y)) := by
    rw [show (-I) ^ n = (-1 : ℂ) ^ n * I ^ n by rw [← mul_pow]; congr 1; ring]
    have hn : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    calc
      _ = (Real.sqrt s : ℂ) * (I ^ n * ↑(TauCeti.hermiteFunction n y)) * ((-1) ^ n * (-1) ^ n) := by ring
      _ = _ := by rw [hn, mul_one]
  rw [hmul] at he
  have hleft : (∫ x : ℝ, exp (I * (s * x) * y) * ((Real.sqrt s : ℂ) * ↑(TauCeti.hermiteFunction n (s * x)))) =
      (Real.sqrt s : ℂ) * (s : ℂ)⁻¹ * ∫ x : ℝ, exp (I * x * y) * ↑(TauCeti.hermiteFunction n x) := by
    simp_rw [mul_left_comm (exp _)]
    simp_rw [← ofReal_mul s]
    rw [integral_const_mul, Measure.integral_comp_mul_left
      (fun x : ℝ => exp (I * x * y) * ↑(TauCeti.hermiteFunction n x)) s]
    simp [abs_of_pos (inv_pos.mpr hs), Complex.real_smul, mul_assoc]
  rw [hleft] at he
  have hsc0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs0
  field_simp [hsc0] at he
  exact he
/-- Evaluation of integer polynomials commutes with the real-to-complex inclusion. -/
private lemma ofReal_aeval_int (p : ℤ[X]) (x : ℝ) :
    ((aeval x p : ℝ) : ℂ) = aeval (x : ℂ) p := by
  exact (aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x p).symm

/-- The physicists' Hermite envelope differs from TauCeti's function by a constant. -/
lemma hermitePhys_envelope (n : ℕ) (x : ℝ) :
    exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermitePhys n) : ℂ) =
      ((2 : ℝ) ^ (n / 2 : ℝ) * Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) : ℝ) *
        (TauCeti.hermiteFunction n x : ℂ) := by
  rw [← ofReal_aeval_int, aeval_hermitePhys_eq_hermite, TauCeti.hermiteFunction_def]
  have hc : Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) ≠ 0 :=
    TauCeti.sqrt_factorial_mul_sqrt_pi_ne_zero n
  have he : exp (-(x : ℂ) ^ 2 / 2) = (Real.exp (-(x ^ 2 / 2)) : ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; ring
  rw [he]
  push_cast
  rw [mul_comm x (Real.sqrt 2)]
  field_simp [ofReal_ne_zero.mpr hc]
  rw [mul_div_cancel_right₀ _ (ofReal_ne_zero.mpr hc)]

/-- The probabilists' Hermite envelope is a dilation of TauCeti's Hermite function. -/
lemma hermite_envelope (n : ℕ) (x : ℝ) :
    exp (-(x : ℂ) ^ 2 / 4) * (aeval (x : ℂ) (hermite n) : ℂ) =
      (Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) : ℂ) *
        (TauCeti.hermiteFunction n (x / Real.sqrt 2) : ℂ) := by
  rw [← ofReal_aeval_int, TauCeti.hermiteFunction_def]
  have hc := TauCeti.sqrt_factorial_mul_sqrt_pi_ne_zero n
  have hr : Real.sqrt 2 ≠ 0 := by positivity
  rw [div_mul_cancel₀ x hr]
  rw [show -((x / Real.sqrt 2) ^ 2 / 2) = -(x ^ 2 / 4) by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; ring]
  have he : exp (-(x : ℂ) ^ 2 / 4) = (Real.exp (-(x ^ 2 / 4)) : ℂ) := by
    rw [ofReal_exp]; congr 1; push_cast; ring
  rw [he]
  push_cast
  field_simp [ofReal_ne_zero.mpr hc]
  rw [mul_div_cancel_right₀ _ (ofReal_ne_zero.mpr hc)]

@[dlmf 18.17.E21_3]
theorem hermitePhys_fourier_eigenfunction (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermitePhys n) : ℂ) * exp (I * x * y)) /
      Real.sqrt (2 * Real.pi) = I ^ n * exp (-(y : ℂ) ^ 2 / 2) * aeval (y : ℂ) (hermitePhys n) := by
  have hs : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [show I ^ n * exp (-(y : ℂ) ^ 2 / 2) * aeval (y : ℂ) (hermitePhys n) =
    I ^ n * (exp (-(y : ℂ) ^ 2 / 2) * aeval (y : ℂ) (hermitePhys n)) by ring]
  simp_rw [hermitePhys_envelope]
  simp_rw [mul_assoc, mul_comm (↑(TauCeti.hermiteFunction n _) : ℂ) (exp _)]
  rw [integral_const_mul]
  simp_rw [← mul_assoc I]
  rw [hermiteFunction_integral]
  field_simp

/-- `u^{s-1} e^{-wu}` is integrable on `(0,∞)` for `Re s, Re w > 0`. -/
lemma integrableOn_cpow_mul_cexp_neg {s w : ℂ} (hs : 0 < s.re) (hw : 0 < w.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-(w * u))) (Set.Ioi 0) := by
  have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1) (b := w.re)
    (by linarith) one_pos hw
  refine Integrable.mono' hb (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : 0 < u := hu
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu', Complex.norm_exp, Real.rpow_one]
  simp

/-- Termwise Mellin–Laplace integration of a finite polynomial sum. -/
lemma integral_finite_sum_mellin_laplace {a : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : 0 < z.re) (s : Finset ℕ) (c : ℕ → ℂ) (d : ℕ → ℕ) :
    (∫ x : ℝ in Set.Ioi 0, exp (-a * x) *
      (∑ k ∈ s, c k * (x : ℂ) ^ d k) * (x : ℂ) ^ (z - 1)) =
      ∑ k ∈ s, c k * Gamma (z + d k) / (a : ℂ) ^ (z + d k) := by
  have hs (k : ℕ) : 0 < (z + d k).re := by
    simp only [add_re, natCast_re]; positivity
  have hterm (x : ℝ) (hx : 0 < x) :
      exp (-a * x) * (∑ k ∈ s, c k * (x : ℂ) ^ d k) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ s, c k * ((x : ℂ) ^ (z + d k - 1) * exp (-((a : ℂ) * x))) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    rw [show z + (d k : ℂ) - 1 = (z - 1) + d k by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), cpow_natCast]
    rw [neg_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hterm x hx),
    integral_finsetSum _ (fun k _ =>
      (integrableOn_cpow_mul_cexp_neg (hs k) (by simpa using ha)).const_mul _)]
  simp_rw [integral_const_mul,
    AAR.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (z := (a : ℂ)) (hs _) (by simpa using ha), cpow_neg,
    div_eq_mul_inv, mul_assoc]

/-- `Γ(a + m) = (a)_m Γ(a)` for `Re a > 0`. -/
lemma Gamma_add_nat_eq_poch_mul {a : ℂ} (ha : 0 < a.re) (m : ℕ) :
    Gamma (a + m) = poch a m * Gamma a := by
  induction m with
  | zero => simp [poch_zero]
  | succ m ih =>
    have hne : a + m ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [show a + ((m + 1 : ℕ) : ℂ) = (a + m) + 1 by push_cast; ring, Gamma_add_one _ hne, ih,
      poch_succ]
    ring

/-- The Laplace transform of `e^{-x} x^α L_n^{(α)}(x)`. -/
lemma laguerre_laplace_aux {α : ℝ} (hα : -1 < α) (n : ℕ) {z : ℂ} (hz : -1 < z.re) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x * z) * laguerre α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (α + n + 1 : ℂ) * z ^ n / (n.factorial * (z + 1) ^ (α + n + 1 : ℂ)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hw : 0 < (z + 1).re := by simp; linarith
  have hw0 : z + 1 ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have hs : ∀ k : ℕ, 0 < ((α : ℂ) + k + 1).re := fun k => by
    simp; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  -- termwise form of the integrand
  have hterm : ∀ x : ℝ, 0 < x → exp (-x * z) * laguerre α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      ∑ k ∈ Finset.range (n + 1), poch (α + 1 + k) (n - k) / ((n - k).factorial * k.factorial : ℂ) *
        (-1) ^ k * ((x : ℂ) ^ (((α : ℂ) + k + 1) - 1) * cexp (-((z + 1) * x))) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
    rw [laguerre_eq_sum hα', Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hc : (x : ℂ) ^ (((α : ℂ) + k + 1) - 1) = (x : ℂ) ^ (α : ℂ) * (x : ℂ) ^ k := by
      rw [show ((α : ℂ) + k + 1) - 1 = (α : ℂ) + k by ring, cpow_add _ _ hx0, cpow_natCast]
    have he : cexp (-((z + 1) * x)) = cexp (-x * z) * cexp (-x) := by
      rw [← Complex.exp_add]; ring_nf
    rw [hc, he, neg_pow]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => hterm x hx)]
  rw [integral_finsetSum _ fun k _ =>
    ((integrableOn_cpow_mul_cexp_neg (hs k) hw).const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_congr rfl fun k _ => by rw [AAR.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (hs k) hw]]
  -- resum with the binomial theorem
  have hz1 : z = (z + 1) - 1 := by ring
  have hpowz : z ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (-1) ^ k * (z + 1) ^ (n - k) := by
    conv_lhs => rw [hz1]
    rw [sub_eq_add_neg, add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hS : ∀ k ∈ Finset.range (n + 1), poch (α + 1 + k) (n - k) / ((n - k).factorial * k.factorial : ℂ) *
      (-1) ^ k * (Gamma ((α : ℂ) + k + 1) * (z + 1) ^ (-((α : ℂ) + k + 1))) =
      Gamma ((α : ℂ) + n + 1) / (n ! * (z + 1) ^ ((α : ℂ) + n + 1)) *
        ((n.choose k : ℂ) * (-1) ^ k * (z + 1) ^ (n - k)) := by
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hG := Gamma_add_nat_eq_poch_mul (hs k) (n - k)
    rw [show (α : ℂ) + k + 1 + ((n - k : ℕ) : ℂ) = α + n + 1 by push_cast [Nat.cast_sub hkn]; ring,
      show (α : ℂ) + k + 1 = α + 1 + k by ring] at hG
    rw [show (α : ℂ) + k + 1 = α + 1 + k by ring, hG,
      show (α : ℂ) + n + 1 = α + 1 + k + (n - k : ℕ) by push_cast [Nat.cast_sub hkn]; ring,
      cpow_add _ _ hw0, cpow_neg, cpow_natCast, Nat.cast_choose ℂ hkn]
    have hf1 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hf2 : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
    have hp1 : (z + 1) ^ ((α : ℂ) + 1 + k) ≠ 0 := by
      rw [cpow_def_of_ne_zero hw0]; exact exp_ne_zero _
    have hp2 : (z + 1) ^ (n - k) ≠ 0 := pow_ne_zero _ hw0
    have hfn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    field_simp
  rw [Finset.sum_congr rfl hS, ← Finset.mul_sum, ← hpowz]
  ring

@[dlmf 18.17.E28_5]
theorem laguerre_fourier_transform {α : ℝ} (hα : -1 < α) (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x) * (x : ℂ) ^ (α : ℂ) * laguerre α n x * exp (I * x * y) =
      Gamma (α + n + 1 : ℂ) * (-I * y) ^ n / (n.factorial * (1 - I * y) ^ (α + n + 1 : ℂ)) := by
  have h := laguerre_laplace_aux hα n (z := -I * y) (by simp)
  rw [show -I * (y : ℂ) + 1 = 1 - I * y by ring] at h
  rw [← h]
  congr 1; funext x
  rw [show -(x : ℂ) * (-I * y) = I * x * y by ring]
  ring

@[dlmf 18.17.E35]
theorem hermitePhys_laplace_transform (n : ℕ) (z : ℂ) :
    ∫ x : ℝ, exp (-x * z) * (aeval (x : ℂ) (hermitePhys n) : ℂ) * exp (-(x : ℂ) ^ 2) =
      Real.sqrt Real.pi * (-z) ^ n * exp (z ^ 2 / 4) := by
  exact hermite_laplace_aux n z

@[dlmf 18.17.E36]
theorem jacobi_mellin_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ (z - 1) * (1 + (x : ℂ)) ^ (β : ℂ) * jacobiP α β n x =
      (2 : ℂ) ^ ((β : ℂ) + z) * Gamma z * Gamma (1 + (β : ℂ) + n) * poch (1 + α - z) n /
      (n.factorial * Gamma (1 + β + z + n)) := by
  sorry

@[dlmf 18.17.E38]
theorem legendre_even_mellin_transform {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendreP (2 * n) x * (x : ℂ) ^ (z - 1) =
      (-1 : ℂ) ^ n * poch (1 / 2 - z / 2) n / (2 * poch (z / 2) (n + 1)) := by
  sorry

@[dlmf 18.17.E39]
theorem legendre_odd_mellin_transform {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendreP (2 * n + 1) x * (x : ℂ) ^ (z - 1) =
      (-1 : ℂ) ^ n * poch (1 - z / 2) n / (2 * poch (1 / 2 + z / 2) (n + 1)) := by
  sorry

@[dlmf 18.17.E44]
theorem legendre_singular_integral (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    ∫ t : ℝ in (-1 : ℝ)..1, (legendreP n x - legendreP n t) / (|x - t| : ℝ) =
      2 * (∑ k ∈ Finset.range n, ((k + 1 : ℂ)⁻¹)) * legendreP n x := by
  sorry

/-- Vandermonde convolution applied to an arbitrary finite coefficient sequence. -/
private lemma binomial_double_sum (m n : ℕ) (f : ℕ → ℂ) :
    (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
      (m.choose i : ℂ) * (n.choose j : ℂ) * f (i + j)) =
    ∑ k ∈ Finset.range (m + n + 1), ((m + n).choose k : ℂ) * f k := by
  let ell : ℂ[X] →+ ℂ := {
    toFun := fun p => p.sum (fun k c => c * f k)
    map_zero' := sum_zero_index _
    map_add' := fun p q => sum_add_index p q _ (by simp) (by intros; ring) }
  have hs (k : ℕ) : (X + 1 : ℂ[X]) ^ k =
      ∑ i ∈ Finset.range (k + 1), monomial i (k.choose i : ℂ) := by
    have h := as_sum_range' ((X + 1 : ℂ[X]) ^ k) (k + 1)
      (by simpa only [← C_1, natDegree_pow_X_add_C] using Nat.lt_succ_self k)
    simpa only [coeff_X_add_one_pow] using h
  have h := congrArg ell (pow_add (X + 1 : ℂ[X]) m n).symm
  rw [hs m, hs n, hs (m + n), Finset.sum_mul] at h
  simp only [Finset.mul_sum, map_sum, monomial_mul_monomial] at h
  change (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1),
    (monomial (i + j) ((m.choose i : ℂ) * (n.choose j : ℂ))).sum (fun k c => c * f k)) =
    (∑ k ∈ Finset.range (m + n + 1),
      (monomial k ((m + n).choose k : ℂ)).sum (fun k c => c * f k)) at h
  simpa only [sum_monomial_index, zero_mul] using h

/-- Finite Gamma-normalized expansion of the Laguerre polynomial divided by its value at zero. -/
lemma laguerre_normalized_sum {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    laguerre α n x / laguerre α n 0 =
      Gamma (α + 1) * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * (-x) ^ i / Gamma (α + 1 + i) := by
  have ha : 0 < (α + 1).re := by simp; linarith
  have hc := not_neg_nat_of_re_pos ha
  have hp : poch (α + 1) n / (n.factorial : ℂ) ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hc n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  rw [laguerre_at_zero, laguerre, mul_div_cancel_left₀ _ hp,
    confluentM_eq_sum_neg_nat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpi := poch_ne_zero_of_not_neg_nat hc i
  have hgi := Gamma_ne_zero_of_re_pos (show 0 < (α + 1 + i).re by
    simp; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith)
  have hga := Gamma_ne_zero_of_re_pos ha
  have hg := Gamma_add_nat_div_Gamma_eq (n := i) (α + 1) hc
  change Gamma (α + 1 + i) / Gamma (α + 1) = poch (α + 1) i at hg
  have hfi : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  rw [← hg, neg_pow]
  field_simp
  ring

/-- Power expansion of a normalized Laguerre polynomial with its endpoint weight. -/
lemma laguerre_normalized_weight_sum {α : ℂ} (hα : -1 < α.re)
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ α * laguerre α n t / laguerre α n 0 =
      Gamma (α + 1) * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * (-1) ^ i / Gamma (α + 1 + i) * (t : ℂ) ^ (α + i) := by
  rw [mul_div_assoc, laguerre_normalized_sum hα, ← mul_assoc, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast, neg_pow]
  ring

@[dlmf 18.17.E47]
theorem laguerre_convolution {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β) (hx : 0 < x) (m n : ℕ) :
    ∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^ (α : ℂ) * laguerre α m t / laguerre α m 0 *
      (x - t : ℂ) ^ (β : ℂ) * laguerre β n (x - t) / laguerre β n 0 =
      Gamma (α + 1 : ℂ) * Gamma (β + 1 : ℂ) / Gamma (α + β + 2 : ℂ) *
      (x : ℂ) ^ (α + β + 1 : ℂ) * laguerre (α + β + 1) (m + n) x / laguerre (α + β + 1) (m + n) 0 := by
  have ha : -1 < (α : ℂ).re := hα
  have hb : -1 < (β : ℂ).re := hβ
  have hc : -1 < ((α + β + 1 : ℝ) : ℂ).re := by simp; linarith
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  let F (i j : ℕ) (t : ℝ) : ℂ :=
    (m.choose i : ℂ) * (n.choose j : ℂ) * (-1) ^ (i + j) /
      (Gamma ((α : ℂ) + 1 + i) * Gamma ((β : ℂ) + 1 + j)) *
      ((t : ℂ) ^ ((α : ℂ) + i) * ((x : ℂ) - t) ^ ((β : ℂ) + j))
  have hai (i : ℕ) : -1 < ((α : ℂ) + i).re := by
    simp; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith
  have hbj (j : ℕ) : -1 < ((β : ℂ) + j).re := by
    simp; have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
  have hi (i j : ℕ) : IntervalIntegrable (F i j) volume 0 x :=
    (intervalIntegrable_cpow_mul_sub_cpow (hai i) (hbj j) hx).const_mul _
  have hmoment (i j : ℕ) : (∫ t : ℝ in (0 : ℝ)..x, F i j t) =
      (x : ℂ) ^ ((α : ℂ) + β + 1) *
        ((m.choose i : ℂ) * (n.choose j : ℂ) * (- (x : ℂ)) ^ (i + j) /
          Gamma ((α : ℂ) + β + 2 + (i + j : ℕ))) := by
    dsimp only [F]
    rw [intervalIntegral.integral_const_mul, integral_cpow_mul_sub_cpow (hai i) (hbj j) hx]
    have hga : Gamma ((α : ℂ) + 1 + i) ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by simp; have := (Nat.cast_nonneg i : (0 : ℝ) ≤ i); linarith)
    have hgb : Gamma ((β : ℂ) + 1 + j) ≠ 0 :=
      Gamma_ne_zero_of_re_pos (by simp; have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith)
    rw [show (α : ℂ) + i + ((β : ℂ) + j) + 1 =
        ((α : ℂ) + β + 1) + (i + j : ℕ) by push_cast; ring,
      cpow_add _ _ hx0, cpow_natCast,
      show (α : ℂ) + i + 1 = (α : ℂ) + 1 + i by ring,
      show (β : ℂ) + j + 1 = (β : ℂ) + 1 + j by ring,
      show (α : ℂ) + i + ((β : ℂ) + j) + 2 =
        (α : ℂ) + β + 2 + (i + j : ℕ) by push_cast; ring]
    rw [neg_pow (x : ℂ)]
    field_simp
  have he : (∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^ (α : ℂ) * laguerre α m t / laguerre α m 0 *
      (x - t : ℂ) ^ (β : ℂ) * laguerre β n (x - t) / laguerre β n 0) =
      Gamma ((α : ℂ) + 1) * Gamma ((β : ℂ) + 1) *
        ∫ t : ℝ in (0 : ℝ)..x, ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), F i j t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hx.le
    intro t ht
    dsimp only
    rw [← ofReal_sub x t]
    have ht' : 0 < x - t := sub_pos.mpr ht.2
    rw [show (t : ℂ) ^ (α : ℂ) * laguerre α m t / laguerre α m 0 *
        ((x - t : ℝ) : ℂ) ^ (β : ℂ) * laguerre β n ((x - t : ℝ) : ℂ) / laguerre β n 0 =
        ((t : ℂ) ^ (α : ℂ) * laguerre α m t / laguerre α m 0) *
        (((x - t : ℝ) : ℂ) ^ (β : ℂ) * laguerre β n ((x - t : ℝ) : ℂ) / laguerre β n 0) by ring,
      laguerre_normalized_weight_sum ha m ht.1, laguerre_normalized_weight_sum hb n ht']
    simp only [Finset.mul_sum, Finset.sum_mul, F, ofReal_sub, pow_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, intervalIntegral.integral_finsetSum
    (f := fun i t => ∑ j ∈ Finset.range (n + 1), F i j t)
    (fun i _ => by
      convert IntervalIntegrable.sum (Finset.range (n + 1)) (fun j _ => hi i j) using 1
      ext t
      simp)]
  have hs (i : ℕ) : (∫ t : ℝ in (0 : ℝ)..x, ∑ j ∈ Finset.range (n + 1), F i j t) =
      ∑ j ∈ Finset.range (n + 1), ∫ t : ℝ in (0 : ℝ)..x, F i j t :=
    intervalIntegral.integral_finsetSum (fun j _ => hi i j)
  simp_rw [hs, hmoment]
  simp only [← Finset.mul_sum, div_eq_mul_inv, mul_assoc]
  have hbin := binomial_double_sum m n (fun k => (- (x : ℂ)) ^ k *
    (Gamma ((α : ℂ) + β + 2 + k))⁻¹)
  simp only [mul_assoc, ← Finset.mul_sum] at hbin
  rw [hbin]
  have hgc : Gamma ((α : ℂ) + β + 2) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hn := laguerre_normalized_sum hc (m + n) (x : ℂ)
  push_cast at hn
  rw [show (α : ℂ) + β + 1 + 1 = (α : ℂ) + β + 2 by ring] at hn
  simp only [div_eq_mul_inv, mul_assoc] at hn
  rw [hn]
  field_simp

@[dlmf 18.17.E48]
theorem hermitePhys_convolution (m n : ℕ) (x : ℝ) :
    ∫ y : ℝ, (aeval y (hermitePhys m) : ℝ) * Real.exp (-(y ^ 2)) *
      aeval (x - y) (hermitePhys n) * Real.exp (-((x - y) ^ 2)) =
      Real.sqrt Real.pi * (2 : ℝ) ^ (-((m : ℝ) + n + 1) / 2) *
      aeval (x / Real.sqrt 2) (hermitePhys (m + n)) * Real.exp (-(x ^ 2) / 2) := by
  let g (j : ℕ) (t : ℝ) := (aeval t (hermitePhys j) : ℝ) * Real.exp (-(t ^ 2))
  have hg (j : ℕ) (t : ℝ) : HasDerivAt (g j) (-g (j + 1) t) t := by
    simpa only [g, aeval_hermitePhys_eq_eval] using hasDerivAt_hermite_gauss j t
  have hi (j k : ℕ) : Integrable (fun t => g j t * g k (x - t)) := by
    let q := hermitePhysR j * (hermitePhysR k).comp (C x - X)
    have he := (integrable_eval_mul_exp_neg_sq q).mul_bdd
      (by fun_prop : Continuous (fun t : ℝ => Real.exp (-((x - t) ^ 2)))).aestronglyMeasurable
      (Eventually.of_forall fun t => show ‖Real.exp (-((x - t) ^ 2))‖ ≤ (1 : ℝ) by
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
        exact neg_nonpos.mpr (sq_nonneg _))
    apply he.congr
    filter_upwards [] with t
    simp only [q, g, eval_mul, eval_comp, eval_sub, eval_C, eval_X,
      aeval_hermitePhys_eq_eval]
    ring
  have htransfer (j k : ℕ) : (∫ t, g (j + 1) t * g k (x - t)) =
      ∫ t, g j t * g (k + 1) (x - t) := by
    have hv (t : ℝ) : HasDerivAt (fun t => g k (x - t)) (g (k + 1) (x - t)) t := by
      convert (hg k (x - t)).comp t ((hasDerivAt_id t).const_sub x) using 1 <;> first | rfl | ring
    have he := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun t _ => hg j t) (fun t _ => hv t) (hi j (k + 1))
      ((hi (j + 1) k).neg.congr (Eventually.of_forall fun t => by simp)) (hi j k)
    rw [← integral_neg] at he
    simpa only [neg_mul, neg_neg] using he.symm
  have hreduce (j k : ℕ) : (∫ t, g j t * g k (x - t)) = ∫ t, g 0 t * g (j + k) (x - t) := by
    induction j generalizing k with
    | zero => simp
    | succ j ih => rw [htransfer, ih]; congr 1; funext t; congr 2; omega
  let s := Real.sqrt 2
  let r := s⁻¹
  let v := x / s
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 2 := by simp [s]
  have hr : 0 < r := inv_pos.mpr hs
  have hab : r ^ 2 + (-r) ^ 2 = 1 := by dsimp [r]; field_simp; nlinarith
  have hmoment (k : ℕ) : (∫ u : ℝ, (aeval (r * v - r * u) (hermitePhys k) : ℝ) *
      Real.exp (-(u ^ 2))) = r ^ k * aeval v (hermitePhys k) * Real.sqrt π := by
    have hfun (u : ℝ) : (aeval (r * v - r * u) (hermitePhys k) : ℝ) * Real.exp (-(u ^ 2)) =
        ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * r ^ i * (-r) ^ (k - i) *
          aeval v (hermitePhys i) * (aeval u (hermitePhys (k - i)) * Real.exp (-(u ^ 2))) := by
      rw [show r * v - r * u = r * v + (-r) * u by ring,
        hermitePhys_addition r (-r) v u hab, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hfun]
    rw [integral_finsetSum _ (fun i _ => by
      simpa only [aeval_hermitePhys_eq_eval] using
        ((integrable_eval_mul_exp_neg_sq (hermitePhysR (k - i))).const_mul
          ((k.choose i : ℝ) * r ^ i * (-r) ^ (k - i) * aeval v (hermitePhys i))))]
    simp_rw [integral_const_mul]
    have hm (i : ℕ) : (∫ u : ℝ, (aeval u (hermitePhys i) : ℝ) * Real.exp (-(u ^ 2))) =
        if i = 0 then Real.sqrt π else 0 := by
      by_cases hi : i = 0
      · subst i; simpa using hermitePhys_orthogonality 0 0
      · simpa [hi, Ne.symm hi] using hermitePhys_orthogonality 0 i
    simp_rw [hm]
    rw [Finset.sum_eq_single k]
    · simp
    · intro i hi hik
      have hiz : k - i ≠ 0 := by have := Finset.mem_range.mp hi; omega
      simp [hiz]
    · simp
  have hbase (k : ℕ) : (∫ t, g 0 t * g k (x - t)) =
      Real.sqrt π * (2 : ℝ) ^ (-((k : ℝ) + 1) / 2) *
        aeval v (hermitePhys k) * Real.exp (-(x ^ 2) / 2) := by
    let F : ℝ → ℝ := fun t => g 0 t * g k (x - t)
    have hchange : (∫ u : ℝ, F (r * u + x / 2)) = s * ∫ t : ℝ, F t := by
      have he := Measure.integral_comp_mul_left (fun t => F (t + x / 2)) r
      simpa only [integral_add_right_eq_self, r, inv_inv, abs_of_pos hs, smul_eq_mul] using he
    have hfun (u : ℝ) : F (r * u + x / 2) = Real.exp (-(x ^ 2) / 2) *
        ((aeval (r * v - r * u) (hermitePhys k) : ℝ) * Real.exp (-(u ^ 2))) := by
      have hx : x - (r * u + x / 2) = r * v - r * u := by
        dsimp [r, v]
        field_simp [hs.ne']
        ring_nf
        simp [hs2]
        ring
      dsimp only [F, g]
      simp only [hermitePhys_zero, map_one, one_mul]
      rw [hx]
      have he : Real.exp (-((r * u + x / 2) ^ 2)) * Real.exp (-((r * v - r * u) ^ 2)) =
          Real.exp (-(x ^ 2) / 2) * Real.exp (-(u ^ 2)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [r, v]
        field_simp [hs.ne']
        ring_nf
        simp [hs2, show s ^ 3 = 2 * s by rw [pow_succ, hs2],
          show s ^ 4 = 4 by rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; norm_num]
        ring
      linear_combination (aeval (r * v - r * u) (hermitePhys k) : ℝ) * he
    simp_rw [hfun] at hchange
    rw [integral_const_mul, hmoment] at hchange
    have hpow : r ^ k / s = (2 : ℝ) ^ (-((k : ℝ) + 1) / 2) := by
      dsimp [r, s]
      rw [inv_pow, div_eq_mul_inv, ← mul_inv, ← pow_succ, Real.sqrt_eq_rpow,
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      push_cast
      ring
    apply (mul_left_cancel₀ hs.ne')
    change (s * ∫ t, F t) = _
    rw [← hchange, ← hpow]
    field_simp
  have he := (hreduce m n).trans (hbase (m + n))
  simpa only [g, v, s, Nat.cast_add, mul_assoc] using he

@[dlmf 18.17.E49]
theorem hermitePhys_triple_integral (a b c : ℕ) :
    ∫ x : ℝ, (aeval x (hermitePhys (a + b)) : ℝ) * aeval x (hermitePhys (b + c)) *
      aeval x (hermitePhys (c + a)) * Real.exp (-(x ^ 2)) =
      2 ^ (a + b + c) * (a + b).factorial * (b + c).factorial * (c + a).factorial *
      Real.sqrt Real.pi / ((a.factorial : ℝ) * b.factorial * c.factorial) := by
  have hl (m n : ℕ) (x : ℝ) :
      (aeval x (hermitePhys m) : ℝ) * aeval x (hermitePhys n) =
        ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℝ) * n.choose k * 2 ^ k * k.factorial *
          aeval x (hermitePhys (m + n - 2 * k)) := by
    have h := hermitePhys_linearization m n (x : ℂ)
    have castH (j : ℕ) : (aeval (x : ℂ) (hermitePhys j) : ℂ) =
        ((aeval x (hermitePhys j) : ℝ) : ℂ) :=
      aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x (hermitePhys j)
    simp_rw [castH] at h
    exact_mod_cast h
  have hi (k : ℕ) : Integrable (fun x : ℝ =>
      (aeval x (hermitePhys (a + b + (b + c) - 2 * k)) : ℝ) *
        aeval x (hermitePhys (c + a)) * Real.exp (-(x ^ 2))) := by
    simp_rw [aeval_hermitePhys_eq_eval, ← eval_mul]
    exact integrable_eval_mul_exp_neg_sq _
  have heq : (fun x : ℝ => (aeval x (hermitePhys (a + b)) : ℝ) *
      aeval x (hermitePhys (b + c)) * aeval x (hermitePhys (c + a)) * Real.exp (-(x ^ 2))) =
      fun x => ∑ k ∈ Finset.range (min (a + b) (b + c) + 1),
        ((a + b).choose k : ℝ) * (b + c).choose k * 2 ^ k * k.factorial *
          ((aeval x (hermitePhys (a + b + (b + c) - 2 * k)) : ℝ) *
            aeval x (hermitePhys (c + a)) * Real.exp (-(x ^ 2))) := by
    funext x
    rw [hl, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _; ring
  rw [heq, integral_finsetSum _ (fun k _ => (hi k).const_mul _)]
  simp_rw [integral_const_mul, hermitePhys_orthogonality]
  rw [Finset.sum_eq_single b]
  · rw [if_pos (by omega : a + b + (b + c) - 2 * b = c + a),
      Nat.cast_choose ℝ (by omega : b ≤ a + b), Nat.cast_choose ℝ (by omega : b ≤ b + c)]
    rw [show a + b - b = a by omega, show b + c - b = c by omega]
    have hp : (2 : ℝ) ^ b * 2 ^ (c + a) = 2 ^ (a + b + c) := by
      rw [← pow_add]; congr 1; omega
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b),
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero c)]
    linear_combination ((a + b).factorial : ℝ) * (b + c).factorial * (c + a).factorial *
      Real.sqrt Real.pi * hp
  · intro k hk hkb
    have hneq : a + b + (b + c) - 2 * k ≠ c + a := by
      have := Finset.mem_range.mp hk; omega
    simp [hneq]
  · simp only [Finset.mem_range]
    omega


/-- The weighted Jacobi antiderivative on an interval contained in `(-1,1)`. -/
@[dlmf 18.17.E1]
theorem jacobi_weighted_integral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    2 * (n + 1 : ℂ) * (∫ y : ℝ in (0 : ℝ)..x, (1 - (y : ℂ)) ^ (α : ℂ) *
      (1 + (y : ℂ)) ^ (β : ℂ) * jacobiP α β (n + 1) y) =
      jacobiP (α + 1) (β + 1) n 0 - (1 - (x : ℂ)) ^ (α + 1 : ℂ) *
        (1 + (x : ℂ)) ^ (β + 1 : ℂ) * jacobiP (α + 1) (β + 1) n x := by
  have hreg (a b : ℝ) (m : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) :
      DifferentiableAt ℝ (fun y : ℝ => (1 - (y : ℂ)) ^ (a : ℂ) *
        (1 + (y : ℂ)) ^ (b : ℂ) * jacobiP a b m y) t := by
    have h1 : (1 - (t : ℂ)) ∈ slitPlane := by
      rw [show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.2])
    have h2 : (1 + (t : ℂ)) ∈ slitPlane := by
      rw [show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.1])
    exact (((((hasDerivAt_id' (t : ℂ)).const_sub 1).cpow_const h1).comp_ofReal).mul
      ((((hasDerivAt_id' (t : ℂ)).const_add 1).cpow_const h2).comp_ofReal)).differentiableAt.mul
      (((analyticOnNhd_jacobiP a b m) t (Set.mem_univ _)).differentiableAt.hasDerivAt.comp_ofReal).differentiableAt
  have hmem (t : ℝ) (ht : t ∈ Set.uIcc 0 x) : t ∈ Set.Ioo (-1) 1 := by
    rcases Set.mem_uIcc.mp ht with ht | ht <;> constructor <;>
      linarith [ht.1, ht.2, hx.1, hx.2]
  let g : ℝ → ℂ := fun y => (1 - (y : ℂ)) ^ (α + 1 : ℂ) *
    (1 + (y : ℂ)) ^ (β + 1 : ℂ) * jacobiP (α + 1) (β + 1) n y
  have hd (t : ℝ) (ht : t ∈ Set.uIcc 0 x) : HasDerivAt (fun y => -g y)
      (2 * (n + 1 : ℂ) * ((1 - (t : ℂ)) ^ (α : ℂ) *
        (1 + (t : ℂ)) ^ (β : ℂ) * jacobiP α β (n + 1) t)) t := by
    have hg : DifferentiableAt ℝ g t := by
      simpa only [g, ofReal_add, ofReal_one] using hreg (α + 1) (β + 1) n t (hmem t ht)
    have hh := hg.hasDerivAt.neg
    have he := jacobi_weighted_derivative (α := α + 1) (β := β + 1)
      (by linarith) (by linarith) n (hmem t ht)
    simp only [ofReal_add, ofReal_one, add_sub_cancel_right] at he
    change deriv g t = _ at he
    rw [he] at hh
    convert hh using 1; ring
  have hi : IntervalIntegrable (fun y : ℝ => 2 * (n + 1 : ℂ) *
      ((1 - (y : ℂ)) ^ (α : ℂ) * (1 + (y : ℂ)) ^ (β : ℂ) *
        jacobiP α β (n + 1) y)) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (continuousAt_const.mul (hreg α β (n + 1) t (hmem t ht)).continuousAt).continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul] at hh
  simpa [g, sub_eq_add_neg, add_comm] using hh

@[dlmf 18.17.E2]
theorem laguerre_unweighted_convolution (m n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, laguerre 0 m y * laguerre 0 n (x - y) =
      laguerre 0 (m + n) x - laguerre 0 (m + n + 1) x := by
  let A : ℕ → ℝ → ℂ := fun j y => laguerre 0 j y - laguerre 0 (j + 1) y
  let D : ℕ → ℝ → ℂ := fun j y => -deriv (laguerre 0 j) ((x : ℂ) - y)
  let C : ℕ → ℕ → ℂ := fun i j => ∫ y : ℝ in (0 : ℝ)..x,
    laguerre 0 i y * laguerre 0 j ((x : ℂ) - y)
  have hL (a : ℂ) (ha : -1 < a.re) (j : ℕ) : Continuous (laguerre a j) :=
    continuous_iff_continuousAt.mpr fun y => (analyticAt_laguerre ha j y).continuousAt
  have hdL (j : ℕ) (y : ℝ) : HasDerivAt (fun t : ℝ => laguerre 0 j t)
      (deriv (laguerre 0 j) y) y :=
    ((analyticAt_laguerre (by norm_num) j (y : ℂ)).differentiableAt.hasDerivAt).comp_ofReal
  have hA (j : ℕ) (y : ℝ) : HasDerivAt (A j) (laguerre 0 j y) y := by
    have h := (hdL j y).sub (hdL (j + 1) y)
    convert h using 1
    linear_combination (laguerre_deriv_succ_sub (α := 0) (by norm_num) j y)
  have hAcont (j : ℕ) : Continuous (A j) :=
    ((hL 0 (by norm_num) j).comp continuous_ofReal).sub
      ((hL 0 (by norm_num) (j + 1)).comp continuous_ofReal)
  have hDcont (j : ℕ) : Continuous (D j) := by
    cases j with
    | zero =>
      have h0 : laguerre 0 0 = fun _ => 1 := funext fun y => laguerre_zero 0 y
      simp only [D, h0, deriv_const, neg_zero]
      exact continuous_const
    | succ j =>
      have hder : deriv (laguerre 0 (j + 1)) = fun y => -laguerre 1 j y :=
        funext fun y => by simpa using laguerre_derivative (α := 0) (by norm_num) j y
      simp only [D, hder, neg_neg]
      exact (hL 1 (by norm_num) j).comp (continuous_const.sub continuous_ofReal)
  have hzero (j : ℕ) : laguerre 0 j 0 = 1 := by
    simp [laguerre_at_zero, poch, ascPochhammer_eval_one, Nat.factorial_ne_zero]
  have hIBP (i j : ℕ) : C i j = A i x - ∫ y : ℝ in (0 : ℝ)..x, D j y * A i y := by
    have hu (y : ℝ) : HasDerivAt (fun t : ℝ => laguerre 0 j ((x : ℂ) - t)) (D j y) y := by
      have h := (analyticAt_laguerre (α := 0) (by norm_num) j ((x : ℂ) - y)).differentiableAt.hasDerivAt
      have hc := (h.comp (y : ℂ) ((hasDerivAt_id (y : ℂ)).const_sub (x : ℂ))).comp_ofReal
      simpa only [D, Function.comp_apply, mul_neg, mul_one] using hc
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : ℝ)) (b := x) (fun y _ => hu y) (fun y _ => hA i y)
      ((hDcont j).intervalIntegrable _ _)
      (((hL 0 (by norm_num) i).comp continuous_ofReal).intervalIntegrable _ _)
    have hleft : (∫ y : ℝ in (0 : ℝ)..x, laguerre 0 j ((x : ℂ) - y) * laguerre 0 i y) = C i j := by
      apply intervalIntegral.integral_congr
      intro y _
      dsimp [C]
      ring
    rw [hleft] at h
    simpa [A, hzero] using h
  have hstep (i j : ℕ) : C i (j + 1) = C (i + 1) j := by
    have hD (y : ℝ) : D (j + 1) y = D j y + laguerre 0 j ((x : ℂ) - y) := by
      dsimp [D]
      linear_combination -(laguerre_deriv_succ_sub (α := 0) (by norm_num) j ((x : ℂ) - y))
    have hsplit : (∫ y : ℝ in (0 : ℝ)..x, D (j + 1) y * A i y) =
        (∫ y : ℝ in (0 : ℝ)..x, D j y * A i y) + C i j - C (i + 1) j := by
      have heq : (fun y => D (j + 1) y * A i y) = fun y => D j y * A i y +
          laguerre 0 i y * laguerre 0 j ((x : ℂ) - y) -
          laguerre 0 (i + 1) y * laguerre 0 j ((x : ℂ) - y) := by
        funext y
        rw [hD]
        dsimp [A]
        ring
      have hprod (k : ℕ) : Continuous (fun y : ℝ =>
          laguerre 0 k y * laguerre 0 j ((x : ℂ) - y)) :=
        ((hL 0 (by norm_num) k).comp continuous_ofReal).mul
          ((hL 0 (by norm_num) j).comp (continuous_const.sub continuous_ofReal))
      have hDA : Continuous (fun y => D j y * A i y) := (hDcont j).mul (hAcont i)
      rw [heq, intervalIntegral.integral_sub
        (f := fun y => D j y * A i y + laguerre 0 i y * laguerre 0 j ((x : ℂ) - y))
        (g := fun y => laguerre 0 (i + 1) y * laguerre 0 j ((x : ℂ) - y))
        ((hDA.add (hprod i)).intervalIntegrable _ _)
        ((hprod (i + 1)).intervalIntegrable _ _),
        intervalIntegral.integral_add
          (f := fun y => D j y * A i y)
          (g := fun y => laguerre 0 i y * laguerre 0 j ((x : ℂ) - y))
          (hDA.intervalIntegrable _ _)
          ((hprod i).intervalIntegrable _ _)]
    rw [hIBP, hsplit, hIBP i j]
    ring
  have hbase (i : ℕ) : C i 0 = A i x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := x)
      (fun y _ => hA i y) (((hL 0 (by norm_num) i).comp continuous_ofReal).intervalIntegrable _ _)
    simpa [C, A, hzero] using h
  have hconv : ∀ i j : ℕ, C i j = A (i + j) x := by
    intro i j
    induction j generalizing i with
    | zero => simpa using hbase i
    | succ j ih => rw [hstep, ih]; congr 1; omega
  exact hconv m n

@[dlmf 18.17.E5]
theorem gegenbauer_product_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (θ ψ : ℝ) :
    gegenbauer lam n (Real.cos θ) / gegenbauer lam n 1 *
      (gegenbauer lam n (Real.cos ψ) / gegenbauer lam n 1) =
      Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, gegenbauer lam n
        (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) / gegenbauer lam n 1 *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ) := by
  sorry

@[dlmf 18.17.E9]
theorem jacobi_fractional_integral {α β μ : ℝ} (hα : -1 < α) (hβ : -1 < β) (hμ : 0 < μ)
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    (1 - (x : ℂ)) ^ (α + μ : ℂ) * jacobiP (α + μ) (β - μ) n x / Gamma (α + μ + n + 1 : ℂ) =
      ∫ y : ℝ in x..1, (1 - (y : ℂ)) ^ (α : ℂ) * jacobiP α β n y / Gamma (α + n + 1 : ℂ) *
        ((y - x : ℂ) ^ (μ - 1 : ℂ) / Gamma (μ : ℂ)) := by
  have hnorm (a b : ℝ) (ha : -1 < a) (y : ℂ) :
      jacobiP a b n y / Gamma ((a : ℂ) + n + 1) =
        regularizedGaussHGFun (-(n : ℂ))
          (n + (a : ℂ) + b + 1) ((a : ℂ) + 1) ((1 - y) / 2) / n.factorial := by
    have hp : ∀ k : ℕ, (a : ℂ) + 1 ≠ -(k : ℂ) :=
      not_neg_nat_of_re_pos (by simp; linarith)
    have hG : Gamma ((a : ℂ) + n + 1) = poch ((a : ℂ) + 1) n * Gamma ((a : ℂ) + 1) := by
      rw [show (a : ℂ) + n + 1 = (a : ℂ) + 1 + n by ring]
      exact (div_eq_iff (Gamma_ne_zero hp)).mp
        (Gamma_add_nat_div_Gamma_eq (n := n) ((a : ℂ) + 1) hp)
    rw [jacobiP, AAR.Hypergeometric.regularizedGaussHGFun_eq_div_Gamma hp, hG]
    field [Gamma_ne_zero hp, poch_ne_zero_of_not_neg_nat hp n]
  let R : ℂ → ℂ := regularizedGaussHGFun (-(n : ℂ))
    (n + (α : ℂ) + β + 1) ((α : ℂ) + 1)
  let f : ℝ → ℂ := fun y => (1 - (y : ℂ)) ^ (α : ℂ) * R ((1 - y) / 2) *
    ((y : ℂ) - x) ^ ((μ : ℂ) - 1)
  let g : ℝ → ℂ := fun t => R (((1 - (x : ℂ)) / 2) * t) *
    (t : ℂ) ^ (α : ℂ) * (1 - (t : ℂ)) ^ ((μ : ℂ) - 1)
  have hxpos : 0 < 1 - x := by linarith [hx.2]
  have hx0 : 1 - (x : ℂ) ≠ 0 := by
    exact_mod_cast hxpos.ne'
  have hscale : (∫ y : ℝ in x..1, f y) =
      (1 - (x : ℂ)) ^ ((α : ℂ) + μ) * ∫ t : ℝ in (0 : ℝ)..1, g t := by
    have hs := intervalIntegral.smul_integral_comp_sub_mul f (1 - x) 1
      (a := (0 : ℝ)) (b := 1)
    simp only [mul_one, sub_sub_cancel, mul_zero, sub_zero, Complex.real_smul,
      ofReal_sub, ofReal_one] at hs
    rw [← hs, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    have hxp : (1 - (x : ℂ)) * (1 - (x : ℂ)) ^ (α : ℂ) *
        (1 - (x : ℂ)) ^ ((μ : ℂ) - 1) = (1 - (x : ℂ)) ^ ((α : ℂ) + μ) := by
      calc
        _ = (1 - (x : ℂ)) ^ (1 : ℂ) * (1 - (x : ℂ)) ^ (α : ℂ) *
            (1 - (x : ℂ)) ^ ((μ : ℂ) - 1) := by rw [cpow_one]
        _ = _ := by rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; congr 1; ring
    have hp (s : ℝ) (hs : 0 ≤ s) (a : ℂ) :
        ((1 - (x : ℂ)) * s) ^ a = (1 - (x : ℂ)) ^ a * (s : ℂ) ^ a := by
      simpa only [ofReal_sub, ofReal_one] using mul_cpow_ofReal_nonneg hxpos.le hs a
    dsimp [f, g]
    push_cast
    rw [show 1 - (1 - (1 - (x : ℂ)) * t) = (1 - (x : ℂ)) * t by ring,
      show 1 - (1 - (x : ℂ)) * t - x = (1 - (x : ℂ)) * (1 - t) by ring,
      hp t ht.1.le, show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; rfl,
      hp (1 - t) (by linarith [ht.2])]
    push_cast
    rw [show (1 - (x : ℂ)) * t / 2 = ((1 - (x : ℂ)) / 2) * t by ring]
    linear_combination (t : ℂ) ^ (α : ℂ) * R (((1 - (x : ℂ)) / 2) * t) *
      (1 - (t : ℂ)) ^ ((μ : ℂ) - 1) * hxp
  have hz : ‖(1 - (x : ℂ)) / 2‖ < 1 := by
    rw [show (1 - (x : ℂ)) / 2 = (((1 - x) / 2 : ℝ) : ℂ) by push_cast; rfl,
      norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith [hx.1]
  have hR := AAR.Hypergeometric.fractional_integral (a := -(n : ℂ))
    (b := n + (α : ℂ) + β + 1) (c := (α : ℂ) + μ + 1) (d := (α : ℂ) + 1)
    (by simp; linarith) (by simp; linarith) hz
  rw [show (α : ℂ) + 1 - 1 = (α : ℂ) by ring,
    show (α : ℂ) + μ + 1 - ((α : ℂ) + 1) = (μ : ℂ) by ring] at hR
  change regularizedGaussHGFun (-(n : ℂ))
    (n + (α : ℂ) + β + 1) ((α : ℂ) + μ + 1) ((1 - x) / 2) =
      1 / Gamma (μ : ℂ) * ∫ t : ℝ in (0 : ℝ)..1, g t at hR
  have hrhs : (∫ y : ℝ in x..1, (1 - (y : ℂ)) ^ (α : ℂ) * jacobiP α β n y /
      Gamma (α + n + 1 : ℂ) * ((y - x : ℂ) ^ (μ - 1 : ℂ) / Gamma (μ : ℂ))) =
      (∫ y : ℝ in x..1, f y) / ((n.factorial : ℂ) * Gamma (μ : ℂ)) := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp only
    rw [show (1 - (y : ℂ)) ^ (α : ℂ) * jacobiP α β n y / Gamma (α + n + 1 : ℂ) =
      (1 - (y : ℂ)) ^ (α : ℂ) * (jacobiP α β n y / Gamma (α + n + 1 : ℂ)) by ring,
      hnorm α β hα]
    dsimp [f, R]
    push_cast
    ring
  have hL := hnorm (α + μ) (β - μ) (by linarith) x
  push_cast at hL
  rw [show (n : ℂ) + ((α : ℂ) + μ) + ((β : ℂ) - μ) + 1 = n + (α : ℂ) + β + 1 by ring] at hL
  rw [hrhs, hscale, show (1 - (x : ℂ)) ^ (α + μ : ℂ) * jacobiP (α + μ) (β - μ) n x /
      Gamma (α + μ + n + 1 : ℂ) = (1 - (x : ℂ)) ^ (α + μ : ℂ) *
      (jacobiP (α + μ) (β - μ) n x / Gamma (α + μ + n + 1 : ℂ)) by ring, hL, hR]
  push_cast
  ring

@[dlmf 18.17.E16_5]
theorem gegenbauer_fourier_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      gegenbauer lam n x * exp (I * x * y) =
      2 * Real.pi * I ^ n * Gamma (n + 2 * (lam : ℂ)) * besselJ (n + (lam : ℂ)) y /
        (n.factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  sorry

@[dlmf 18.17.E21]
theorem legendre_bessel_square_integral (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendreP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y) =
      Real.pi / 2 * besselJ (n + 1 / 2 : ℂ) ((y : ℂ) / 2) ^ 2 := by
  sorry

@[dlmf 18.17.E22]
theorem hermite_fourier_eigenfunction (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2 / 4) * (aeval (x : ℂ) (hermite n) : ℂ) * exp (I * x * y / 2)) /
      (2 * Real.sqrt Real.pi) = I ^ n * exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n) := by
  let r := Real.sqrt 2
  have hr : 0 < r := Real.sqrt_pos.mpr two_pos
  have hr0 : r ≠ 0 := hr.ne'
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let c := Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi)
  let F : ℝ → ℂ := fun x => exp (-(x : ℂ) ^ 2 / 4) * aeval (x : ℂ) (hermite n) * exp (I * x * y / 2)
  have hscale := Measure.integral_comp_mul_left F r
  have hx (x : ℝ) : F (r * x) = (c : ℂ) *
      (exp (I * x * ↑(y / r)) * (TauCeti.hermiteFunction n x : ℂ)) := by
    dsimp [F]
    rw [hermite_envelope]
    change (c : ℂ) * (TauCeti.hermiteFunction n (r * x / r) : ℂ) * exp (I * ↑(r * x) * y / 2) = _
    rw [mul_div_cancel_left₀ x hr0]
    have he : I * ↑(r * x) * y / 2 = I * x * ↑(y / r) := by
      push_cast
      have hrc : (r : ℂ) ^ 2 = 2 := by exact_mod_cast hr2
      have hr0c : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0
      field_simp
      linear_combination (x : ℂ) * y * hrc
    rw [he]
    ring
  simp_rw [hx] at hscale
  rw [integral_const_mul, hermiteFunction_integral, abs_of_pos (inv_pos.mpr hr), Complex.real_smul] at hscale
  have hrs : (r : ℂ) * (Real.sqrt (2 * Real.pi) : ℂ) = 2 * (Real.sqrt Real.pi : ℂ) := by
    norm_cast
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    change r * (r * Real.sqrt Real.pi) = _
    rw [← mul_assoc, ← pow_two, hr2]
  rw [show I ^ n * exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n) =
    I ^ n * (exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n)) by ring, hermite_envelope]
  change (∫ x, F x) / (2 * ↑(Real.sqrt Real.pi)) = I ^ n * ((c : ℂ) * ↑(TauCeti.hermiteFunction n (y / r)))
  have hr0c : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr0
  have hp0 : (Real.sqrt Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  rw [ofReal_inv] at hscale
  field_simp [hr0c] at hscale
  apply (div_eq_iff (mul_ne_zero two_ne_zero hp0)).mpr
  calc
    _ = (c : ℂ) * (r * ↑(Real.sqrt (2 * Real.pi))) * I ^ n * ↑(TauCeti.hermiteFunction n (y / r)) := by
      linear_combination -hscale
    _ = _ := by rw [hrs]; ring

/-! ### Fourier transforms of `He_n(x) e^{-x²/2}` -/

/-- The Hermite–Gaussian function `He_n(x) e^{-x²/2}`. -/
def hermiteGauss (n : ℕ) (x : ℝ) : ℝ := aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))

/-- `He_n(x) e^{-x²/2} = (-1)^n dⁿ/dxⁿ e^{-x²/2}`. -/
lemma hermiteGauss_eq_iterate (n : ℕ) (x : ℝ) :
    hermiteGauss n x = (-1) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x := by
  rw [deriv_gaussian_eq_hermite_mul_gaussian, hermiteGauss, ← mul_assoc, ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- `(He_n e^{-x²/2})' = -He_{n+1} e^{-x²/2}`. -/
lemma hasDerivAt_hermiteGauss (n : ℕ) (x : ℝ) :
    HasDerivAt (hermiteGauss n) (-hermiteGauss (n + 1) x) x := by
  have hg : ContDiff ℝ ⊤ fun y : ℝ => Real.exp (-(y ^ 2 / 2)) := by fun_prop
  have hd : Differentiable ℝ (deriv^[n] fun y : ℝ => Real.exp (-(y ^ 2 / 2))) := by
    rw [← iteratedDeriv_eq_iterate]
    exact hg.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)
  have hfun : hermiteGauss n = fun x =>
      (-1) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x :=
    funext (hermiteGauss_eq_iterate n)
  rw [hfun, hermiteGauss_eq_iterate, Function.iterate_succ_apply', pow_succ]
  convert ((hd x).hasDerivAt.const_mul ((-1 : ℝ) ^ n)) using 1
  ring

/-- `He_n(x) e^{-x²/2}` is integrable (Tau Ceti `integrable_aeval_mul_gaussian`). -/
lemma integrable_hermiteGauss (n : ℕ) : Integrable (hermiteGauss n) :=
  TauCeti.integrable_aeval_mul_gaussian (hermite n)

/-- The positive-phase Fourier transform of `He_n(x) e^{-x²/2}`. -/
lemma integral_exp_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    ∫ x : ℝ, cexp (I * y * x) * (hermiteGauss n x : ℂ) =
      (I * y) ^ n * (Real.sqrt (2 * π) * Real.exp (-(y ^ 2 / 2)) : ℝ) := by
  induction n with
  | zero =>
    have h := fourierIntegral_gaussian (b := 1 / 2) (by norm_num) (y : ℂ)
    simp only [hermiteGauss, hermite_zero, map_one, one_mul, pow_zero]
    convert h using 1
    · congr 1; funext x; congr 1; push_cast; congr 1; ring
    · rw [show (π : ℂ) / (1 / 2) = 2 * π by ring, Complex.ofReal_mul, Real.sqrt_eq_rpow,
        Complex.ofReal_cpow (by positivity), Complex.ofReal_exp]
      push_cast
      congr 2
      ring
  | succ n ih =>
    have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => cexp (I * y * x)) (I * y * cexp (I * y * x)) x :=
      fun x => by
        have := ((hasDerivAt_id (x : ℂ)).const_mul (I * y)).cexp.comp_ofReal
        simpa [mul_comm] using this
    have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (hermiteGauss n x : ℂ))
        ((-hermiteGauss (n + 1) x : ℝ) : ℂ) x :=
      fun x => (hasDerivAt_hermiteGauss n x).ofReal_comp
    have hint : ∀ m, Integrable fun x : ℝ => cexp (I * y * x) * (hermiteGauss m x : ℂ) := by
      intro m
      refine (integrable_hermiteGauss m).ofReal.bdd_mul (c := 1) ?_ ?_
      · exact (by fun_prop : Continuous fun x : ℝ => cexp (I * y * x)).aestronglyMeasurable
      · refine Eventually.of_forall fun x => le_of_eq ?_
        rw [Complex.norm_exp]
        simp
    have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x)
      (fun x _ => hv x)
      ((hint (n + 1)).neg.congr (Eventually.of_forall fun x => by simp))
      (((hint n).const_mul (I * y)).congr (Eventually.of_forall fun x => by simp; ring))
      (hint n)
    simp only [ofReal_neg, mul_neg, integral_neg, neg_inj] at hibp
    rw [hibp, show (fun x : ℝ => I * y * cexp (I * y * x) * (hermiteGauss n x : ℂ)) =
      fun x : ℝ => I * y * (cexp (I * y * x) * (hermiteGauss n x : ℂ)) by funext x; ring,
      integral_const_mul, ih, pow_succ]
    ring


/-- `e^{iyx} He_n(x) e^{-x²/2}` is integrable. -/
lemma integrable_exp_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    Integrable fun x : ℝ => cexp (I * y * x) * (hermiteGauss n x : ℂ) := by
  refine (integrable_hermiteGauss n).ofReal.bdd_mul (c := 1) ?_ ?_
  · exact (by fun_prop : Continuous fun x : ℝ => cexp (I * y * x)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => le_of_eq ?_
    rw [Complex.norm_exp]
    simp

/-- Rewriting `e^{iyx}` as `e^{(yx) i}`. -/
lemma exp_I_mul_eq (y x : ℝ) : cexp (I * y * x) = cexp (((y * x : ℝ) : ℂ) * I) := by
  push_cast; ring_nf

/-- The cosine transform of `He_n(x) e^{-x²/2}` over `ℝ`. -/
lemma integral_cos_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    ∫ x : ℝ, Real.cos (y * x) * hermiteGauss n x =
      ((I * y) ^ n).re * (Real.sqrt (2 * π) * Real.exp (-(y ^ 2 / 2))) := by
  have h := congrArg Complex.re (integral_exp_mul_hermiteGauss n y)
  have hr := integral_re (integrable_exp_mul_hermiteGauss n y)
  simp only [RCLike.re_to_complex] at hr
  rw [← hr, Complex.re_mul_ofReal] at h
  rw [← h]
  congr 1; funext x
  rw [exp_I_mul_eq, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re]

/-- The sine transform of `He_n(x) e^{-x²/2}` over `ℝ`. -/
lemma integral_sin_mul_hermiteGauss (n : ℕ) (y : ℝ) :
    ∫ x : ℝ, Real.sin (y * x) * hermiteGauss n x =
      ((I * y) ^ n).im * (Real.sqrt (2 * π) * Real.exp (-(y ^ 2 / 2))) := by
  have h := congrArg Complex.im (integral_exp_mul_hermiteGauss n y)
  have hi := integral_im (integrable_exp_mul_hermiteGauss n y)
  simp only [RCLike.im_to_complex] at hi
  rw [← hi, Complex.im_mul_ofReal] at h
  rw [← h]
  congr 1; funext x
  rw [exp_I_mul_eq, Complex.im_mul_ofReal, Complex.exp_ofReal_mul_I_im]

/-- `√(2π)/2 = √(π/2)`. -/
lemma sqrt_two_pi_div_two : Real.sqrt (2 * π) / 2 = Real.sqrt (π / 2) := by
  rw [show π / 2 = (2 * π) / 2 ^ 2 by ring, Real.sqrt_div' _ (by positivity),
    Real.sqrt_sq (by norm_num)]

@[dlmf 18.17.E23]
theorem hermite_even_cosine_transform (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n)) : ℝ) * Real.cos (x * y) =
      (-1 : ℝ) ^ n * Real.sqrt (Real.pi / 2) * y ^ (2 * n) * Real.exp (-(y ^ 2) / 2) := by
  set f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n)) : ℝ) *
    Real.cos (x * y) with hf
  have heven : ∀ x, f |x| = f x := by
    intro x
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hf]
      simp only [hermite_aeval_neg, pow_mul, one_pow, one_mul, neg_mul, Real.cos_neg,
        even_two, Even.neg_pow]
  have habs := integral_comp_abs (f := f)
  simp_rw [heven] at habs
  have hfull : ∫ x, f x = ∫ x : ℝ, Real.cos (y * x) * hermiteGauss (2 * n) x := by
    congr 1; funext x
    simp only [hf, hermiteGauss, neg_div, mul_comm x y]
    ring
  rw [hfull, integral_cos_mul_hermiteGauss, mul_pow, pow_mul, I_sq] at habs
  have hre : (((-1 : ℂ) ^ n) * (y : ℂ) ^ (2 * n)).re = (-1 : ℝ) ^ n * y ^ (2 * n) := by
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
    norm_cast
  rw [hre] at habs
  rw [← sqrt_two_pi_div_two, neg_div]
  linarith

@[dlmf 18.17.E27]
theorem hermite_odd_sine_transform (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n + 1)) : ℝ) * Real.sin (x * y) =
      (-1 : ℝ) ^ n * Real.sqrt (Real.pi / 2) * y ^ (2 * n + 1) * Real.exp (-(y ^ 2) / 2) := by
  set f : ℝ → ℝ := fun x => Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n + 1)) : ℝ) *
    Real.sin (x * y) with hf
  have heven : ∀ x, f |x| = f x := by
    intro x
    rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hf]
      simp only [hermite_aeval_neg, neg_mul, Real.sin_neg, neg_sq]
      rw [pow_succ (-1 : ℝ), pow_mul (-1 : ℝ), neg_one_sq, one_pow]
      ring
  have habs := integral_comp_abs (f := f)
  simp_rw [heven] at habs
  have hfull : ∫ x, f x = ∫ x : ℝ, Real.sin (y * x) * hermiteGauss (2 * n + 1) x := by
    congr 1; funext x
    simp only [hf, hermiteGauss, neg_div, mul_comm x y]
    ring
  rw [hfull, integral_sin_mul_hermiteGauss, mul_pow, pow_succ, pow_mul, I_sq] at habs
  have him : ((-1 : ℂ) ^ n * I * (y : ℂ) ^ (2 * n + 1)).im =
      (-1 : ℝ) ^ n * y ^ (2 * n + 1) := by
    rw [show (-1 : ℂ) ^ n * I * (y : ℂ) ^ (2 * n + 1) =
      (((-1 : ℝ) ^ n * y ^ (2 * n + 1) : ℝ) : ℂ) * I by push_cast; ring, Complex.mul_I_im,
      Complex.ofReal_re]
  rw [him] at habs
  rw [← sqrt_two_pi_div_two, neg_div]
  linarith

/-- The product formula for Mathlib's probabilists' Hermite normalization. -/
lemma hermite_linearization (m n : ℕ) (x : ℝ) :
    (aeval x (hermite m) : ℝ) * aeval x (hermite n) =
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℝ) * n.choose k * k.factorial *
        aeval x (hermite (m + n - 2 * k)) := by
  let s := Real.sqrt 2
  have hs : 0 < s := by dsimp [s]; positivity
  have hs2 : s ^ 2 = 2 := by simp [s]
  have hscale (j : ℕ) : (aeval (x / s) (hermitePhys j) : ℝ) =
      s ^ j * aeval x (hermite j) := by
    rw [aeval_hermitePhys_eq_hermite]
    have hpow : (2 : ℝ) ^ (j / 2 : ℝ) = s ^ j := by
      rw [show s = (2 : ℝ) ^ (1 / 2 : ℝ) by dsimp [s]; rw [Real.sqrt_eq_rpow],
        ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hpow, show Real.sqrt 2 * (x / s) = x by dsimp [s]; field_simp]
  have hcast (j : ℕ) : (aeval ((x / s : ℝ) : ℂ) (hermitePhys j) : ℂ) =
      ((aeval (x / s) (hermitePhys j) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) (x / s) (hermitePhys j)
  have hc := hermitePhys_linearization m n ((x / s : ℝ) : ℂ)
  simp_rw [hcast] at hc
  have hr : (aeval (x / s) (hermitePhys m) : ℝ) * aeval (x / s) (hermitePhys n) =
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℝ) * n.choose k * 2 ^ k * k.factorial *
        aeval (x / s) (hermitePhys (m + n - 2 * k)) := by exact_mod_cast hc
  simp_rw [hscale] at hr
  have hpow (k : ℕ) (hk : k ∈ Finset.range (min m n + 1)) :
      (2 : ℝ) ^ k * s ^ (m + n - 2 * k) = s ^ (m + n) := by
    have hle : 2 * k ≤ m + n := by have := Finset.mem_range.mp hk; omega
    rw [← hs2, ← pow_mul, ← pow_add, Nat.add_sub_of_le hle]
  apply mul_left_cancel₀ (pow_ne_zero (m + n) hs.ne')
  calc
    _ = (s ^ m * (aeval x (hermite m) : ℝ)) * (s ^ n * aeval x (hermite n)) := by
      rw [pow_add]; ring
    _ = _ := hr
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have := hpow k hk
      linear_combination (m.choose k : ℝ) * n.choose k * k.factorial *
        (aeval x (hermite (m + n - 2 * k)) : ℝ) * this

/-- The finite contraction sum in a Hermite transform is a Laguerre polynomial. -/
lemma hermite_laguerre_sum (n l : ℕ) (u : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + l).choose k * k.factorial *
      (-1 : ℂ) ^ (n - k) * u ^ (2 * (n - k) + l) =
      n.factorial * u ^ l * laguerre l n (u ^ 2) := by
  have hl : ∀ k : ℕ, (l : ℂ) + 1 ≠ -k :=
    not_neg_nat_of_re_pos (by simp; positivity)
  rw [laguerre_eq_sum hl, Finset.mul_sum, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
  rw [show n + 1 - 1 - j = n - j by omega, Nat.sub_sub_self hjn]
  have hN : (n.choose (n - j) : ℂ) * (n - j).factorial * j.factorial = n.factorial := by
    exact_mod_cast (by simpa [Nat.sub_sub_self hjn] using
      Nat.choose_mul_factorial_mul_factorial (Nat.sub_le n j))
  have hL : ((n + l).choose (n - j) : ℂ) * (n - j).factorial * (l + j).factorial =
      (n + l).factorial := by
    exact_mod_cast (by simpa [show n + l - (n - j) = l + j by omega] using
      Nat.choose_mul_factorial_mul_factorial (show n - j ≤ n + l by omega))
  have hP : ((l + j).factorial : ℂ) * poch ((l : ℂ) + 1 + j) (n - j) = (n + l).factorial := by
    have he := factorial_mul_ascPochhammer ℂ (l + j) (n - j)
    simpa only [poch, Nat.add_sub_of_le (show j ≤ n + l by omega),
      show l + j + (n - j) = n + l by omega, Nat.cast_add,
      show (l : ℂ) + j + 1 = l + 1 + j by ring] using he
  have hcoeff : (n.choose (n - j) : ℂ) * (n + l).choose (n - j) * (n - j).factorial =
      n.factorial * (poch ((l : ℂ) + 1 + j) (n - j) /
        ((n - j).factorial * j.factorial : ℂ)) := by
    rw [← mul_div_assoc]
    apply (eq_div_iff (mul_ne_zero (Nat.cast_ne_zero.mpr (n - j).factorial_ne_zero)
      (Nat.cast_ne_zero.mpr j.factorial_ne_zero))).mpr
    calc
      _ = ((n.choose (n - j) : ℂ) * (n - j).factorial * j.factorial) *
          (((n + l).choose (n - j) : ℂ) * (n - j).factorial) := by ring
      _ = n.factorial * poch ((l : ℂ) + 1 + j) (n - j) := by
        rw [hN]
        congr 1
        apply mul_right_cancel₀ (Nat.cast_ne_zero.mpr (l + j).factorial_ne_zero)
        rw [hL]
        simpa [mul_comm] using hP.symm
  rw [hcoeff, neg_pow (u ^ 2), pow_add, pow_mul]
  ring

@[dlmf 18.17.E25]
theorem hermite_product_cosine_transform (m n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m)) * Real.cos (x * y) =
      (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m) *
        exp (-(y : ℂ) ^ 2 / 2) * laguerre (2 * m) n ((y : ℂ) ^ 2) := by
  have hcast (j : ℕ) (x : ℝ) : (aeval (x : ℂ) (hermite j) : ℂ) =
      ((aeval x (hermite j) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x (hermite j)
  have hexp (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) = (Real.exp (-(x ^ 2) / 2) : ℂ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  let G (j : ℕ) (x : ℝ) : ℂ := exp (-(x : ℂ) ^ 2 / 2) *
    aeval (x : ℂ) (hermite j) * Real.cos (x * y)
  have hi (j : ℕ) : Integrable (G j) := by
    have ht := (integrable_hermiteGauss j).mul_bdd
      (by fun_prop : Continuous (fun x : ℝ => Real.cos (x * y))).aestronglyMeasurable
      (Eventually.of_forall fun x => show ‖Real.cos (x * y)‖ ≤ (1 : ℝ) by
        simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (x * y))
    apply ht.ofReal.congr
    filter_upwards [] with x
    dsimp only [G]
    rw [hexp, hcast]
    simp only [hermiteGauss, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, neg_div]
    ring_nf
  have hlin (x : ℝ) : (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m)) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
          aeval (x : ℂ) (hermite (n + (n + 2 * m) - 2 * k)) := by
    simp_rw [hcast]
    have hr := hermite_linearization n (n + 2 * m) x
    rw [min_eq_left (by omega)] at hr
    exact_mod_cast hr
  have he : (∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) *
      (aeval (x : ℂ) (hermite n) : ℂ) * aeval (x : ℂ) (hermite (n + 2 * m)) *
        Real.cos (x * y)) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
        ∫ x : ℝ in Set.Ioi 0, G (n + (n + 2 * m) - 2 * k) x := by
    have he (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
        aeval (x : ℂ) (hermite (n + 2 * m)) * Real.cos (x * y) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
          G (n + (n + 2 * m) - 2 * k) x := by
      rw [mul_assoc (exp _) _ _, hlin]
      simp only [Finset.mul_sum, Finset.sum_mul, G]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun k _ => (hi _).integrableOn.const_mul _)]
    simp_rw [integral_const_mul]
  have htrans (j : ℕ) : (∫ x : ℝ in Set.Ioi 0, G (2 * j) x) =
      (-1 : ℂ) ^ j * Real.sqrt (Real.pi / 2) * (y : ℂ) ^ (2 * j) *
        exp (-(y : ℂ) ^ 2 / 2) := by
    simp only [G, hexp, hcast, ← ofReal_mul, _root_.integral_complex_ofReal]
    rw [hermite_even_cosine_transform j y]
    push_cast
    ring
  rw [he]
  have hsum := hermite_laguerre_sum n (2 * m) (y : ℂ)
  calc
    _ = ((-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * exp (-(y : ℂ) ^ 2 / 2)) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m).choose k * k.factorial *
          (-1 : ℂ) ^ (n - k) * (y : ℂ) ^ (2 * (n - k) + 2 * m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [show n + (n + 2 * m) - 2 * k = 2 * (n - k + m) by omega,
        htrans, pow_add, show 2 * (n - k + m) = 2 * (n - k) + 2 * m by omega]
      ring
    _ = _ := by
      try simp only [← Nat.add_assoc] at hsum
      rw [hsum]
      push_cast
      ring

@[dlmf 18.17.E26]
theorem hermite_product_sine_transform (m n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m + 1)) * Real.sin (x * y) =
      (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m + 1) *
        exp (-(y : ℂ) ^ 2 / 2) * laguerre (2 * m + 1) n ((y : ℂ) ^ 2) := by
  have hcast (j : ℕ) (x : ℝ) : (aeval (x : ℂ) (hermite j) : ℂ) =
      ((aeval x (hermite j) : ℝ) : ℂ) :=
    aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) x (hermite j)
  have hexp (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) = (Real.exp (-(x ^ 2) / 2) : ℂ) := by
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  let G (j : ℕ) (x : ℝ) : ℂ := exp (-(x : ℂ) ^ 2 / 2) *
    aeval (x : ℂ) (hermite j) * Real.sin (x * y)
  have hi (j : ℕ) : Integrable (G j) := by
    have ht := (integrable_hermiteGauss j).mul_bdd
      (by fun_prop : Continuous (fun x : ℝ => Real.sin (x * y))).aestronglyMeasurable
      (Eventually.of_forall fun x => show ‖Real.sin (x * y)‖ ≤ (1 : ℝ) by
        simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (x * y))
    apply ht.ofReal.congr
    filter_upwards [] with x
    dsimp only [G]
    rw [hexp, hcast]
    simp only [hermiteGauss, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_mul, neg_div]
    ring_nf
  have hlin (x : ℝ) : (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m + 1)) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
          aeval (x : ℂ) (hermite (n + (n + 2 * m + 1) - 2 * k)) := by
    simp_rw [hcast]
    have hr := hermite_linearization n (n + 2 * m + 1) x
    rw [min_eq_left (by omega)] at hr
    exact_mod_cast hr
  have he : (∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) *
      (aeval (x : ℂ) (hermite n) : ℂ) * aeval (x : ℂ) (hermite (n + 2 * m + 1)) *
        Real.sin (x * y)) = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
        ∫ x : ℝ in Set.Ioi 0, G (n + (n + 2 * m + 1) - 2 * k) x := by
    have he (x : ℝ) : exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
        aeval (x : ℂ) (hermite (n + 2 * m + 1)) * Real.sin (x * y) =
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
          G (n + (n + 2 * m + 1) - 2 * k) x := by
      rw [mul_assoc (exp _) _ _, hlin]
      simp only [Finset.mul_sum, Finset.sum_mul, G]
      apply Finset.sum_congr rfl
      intro k _
      ring
    simp_rw [he]
    rw [integral_finsetSum _ (fun k _ => (hi _).integrableOn.const_mul _)]
    simp_rw [integral_const_mul]
  have htrans (j : ℕ) : (∫ x : ℝ in Set.Ioi 0, G (2 * j + 1) x) =
      (-1 : ℂ) ^ j * Real.sqrt (Real.pi / 2) * (y : ℂ) ^ (2 * j + 1) *
        exp (-(y : ℂ) ^ 2 / 2) := by
    simp only [G, hexp, hcast, ← ofReal_mul, _root_.integral_complex_ofReal]
    rw [hermite_odd_sine_transform j y]
    push_cast
    ring
  rw [he]
  have hsum := hermite_laguerre_sum n (2 * m + 1) (y : ℂ)
  calc
    _ = ((-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * exp (-(y : ℂ) ^ 2 / 2)) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (n + 2 * m + 1).choose k * k.factorial *
          (-1 : ℂ) ^ (n - k) * (y : ℂ) ^ (2 * (n - k) + 2 * m + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
      rw [show n + (n + 2 * m + 1) - 2 * k = 2 * (n - k + m) + 1 by omega,
        htrans, pow_add, show 2 * (n - k + m) + 1 = 2 * (n - k) + 2 * m + 1 by omega]
      ring
    _ = _ := by
      try simp only [← Nat.add_assoc] at hsum
      rw [hsum]
      push_cast
      ring

@[dlmf 18.17.E33]
theorem jacobi_laplace_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (z : ℂ) :
    ∫ x : ℝ in (-1 : ℝ)..1, exp (-((x : ℂ) + 1) * z) * jacobiP α β n x *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) =
      (-1 : ℂ) ^ n * (2 : ℂ) ^ (α + β + n + 1 : ℂ) * Gamma (α + n + 1 : ℂ) *
      Gamma (β + n + 1 : ℂ) / (Gamma (α + β + 2 * n + 2 : ℂ) * n.factorial) *
      z ^ n * confluentM (β + n + 1 : ℂ) (α + β + 2 * n + 2 : ℂ) (-2 * z) := by
  sorry

@[dlmf 18.17.E34_5]
theorem laguerre_product_laplace_transform {α : ℝ} (hα : -1 < α) (m n : ℕ) {z : ℂ}
    (hz : -1 < z.re) (hz0 : z ≠ 0) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x * z) * laguerre α m x * laguerre α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (α + m + 1 : ℂ) * Gamma (α + n + 1 : ℂ) /
      (Gamma (α + 1 : ℂ) * m.factorial * n.factorial) * z ^ (m + n) /
      (z + 1) ^ (α + m + n + 1 : ℂ) * ₂F₁ (-(m : ℂ)) (-(n : ℂ)) (α + 1 : ℂ) (z⁻¹ ^ 2) := by
  sorry

/-- Corrected finite-sum form of DLMF 18.17.41 (checked 2026-09-16).
The displayed DLMF formula is incorrect: at `n = 0` its power `a^(-n-2)`
would give `Γ(z)/a²`, whereas the integral is `Γ(z)/a^z`.
The terminating ₂F₂ denominator parameters also require a shift: they should be
`(1-z-n)/2` and `(2-z-n)/2`. This sum avoids their removable singularities. -/
@[dlmf 18.17.E41]
theorem hermite_mellin_laplace_transform {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-a * x) * (aeval (x : ℂ) (hermite n) : ℂ) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ Finset.range (n / 2 + 1), (-1 : ℂ) ^ k * n.factorial /
        (2 ^ k * (k.factorial : ℂ) * (n - 2 * k).factorial) *
        Gamma (z + (n - 2 * k : ℕ)) / (a : ℂ) ^ (z + (n - 2 * k : ℕ)) := by
  simp_rw [hermite_finite_sum]
  exact integral_finite_sum_mellin_laplace ha hz _ _ (fun k => n - 2 * k)



@[dlmf 18.10.E1]
theorem gegenbauer_dirichlet_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ)
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    gegenbauer lam n (Real.cos θ) / gegenbauer lam n 1 =
      (2 : ℂ) ^ (lam : ℂ) * Gamma (lam + 1 / 2 : ℂ) /
        (Real.sqrt Real.pi * Gamma (lam : ℂ)) * (Real.sin θ : ℂ) ^ (1 - 2 * lam : ℂ) *
      ∫ phi : ℝ in (0 : ℝ)..θ, (Real.cos ((n + lam) * phi) : ℂ) *
        (Real.cos phi - Real.cos θ : ℂ) ^ (lam - 1 : ℂ) := by
  sorry

@[dlmf 18.10.E3]
theorem jacobi_double_laplace_integral {α β : ℝ} (hαβ : β < α) (hβ : -1 / 2 < β)
    (n : ℕ) (θ : ℝ) :
    jacobiP α β n (Real.cos θ) / jacobiP α β n 1 =
      2 * Gamma (α + 1 : ℂ) / (Real.sqrt Real.pi * Gamma (α - β : ℂ) * Gamma (β + 1 / 2 : ℂ)) *
      ∫ r : ℝ in (0 : ℝ)..1, ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((Real.cos (θ / 2) : ℂ) ^ 2 - r ^ 2 * (Real.sin (θ / 2) : ℂ) ^ 2 +
          I * r * Real.sin θ * Real.cos phi) ^ n *
        (1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ) := by
  sorry

@[dlmf 18.10.E6]
theorem laguerre_double_laplace_integral {α : ℝ} (hα : -1 / 2 < α) (n : ℕ) (x : ℝ) :
    laguerre α n ((x : ℂ) ^ 2) =
      2 * (-1 : ℂ) ^ n / (Real.sqrt Real.pi * Gamma (α + 1 / 2 : ℂ) * n.factorial) *
      ∫ r : ℝ in Set.Ioi 0, ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi) ^ n * exp (-(r : ℂ) ^ 2) *
        (r : ℂ) ^ (2 * α + 1 : ℂ) * (Real.sin phi : ℂ) ^ (2 * α : ℂ) := by
  sorry

@[dlmf 18.10.E9]
theorem laguerre_bessel_integral {α : ℝ} (hα : -1 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerre α n x = exp (x : ℂ) * (x : ℂ) ^ (-α / 2 : ℂ) / n.factorial *
      ∫ t : ℝ in Set.Ioi 0, exp (-t : ℂ) * (t : ℂ) ^ (n + α / 2 : ℂ) *
        besselJ α (2 * Real.sqrt (x * t)) := by
  sorry

@[dlmf 18.17.E16]
theorem jacobi_fourier_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) *
      jacobiP α β n x * exp (I * x * y) =
      (I * y) ^ n * exp (I * y) / n.factorial * (2 : ℂ) ^ (n + α + β + 1 : ℂ) *
        Gamma (n + α + 1 : ℂ) * Gamma (n + β + 1 : ℂ) / Gamma (2 * n + α + β + 2 : ℂ) *
        confluentM (n + α + 1) (2 * n + α + β + 2) (-2 * I * y) := by
  sorry

@[dlmf 18.17.E17]
theorem gegenbauer_even_cosine_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      gegenbauer lam (2 * n) x * Real.cos (x * y) =
      (-1 : ℂ) ^ n * Real.pi * Gamma (2 * n + 2 * lam : ℂ) * besselJ (lam + 2 * n) y /
        ((2 * n).factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  sorry

@[dlmf 18.17.E18]
theorem gegenbauer_odd_sine_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      gegenbauer lam (2 * n + 1) x * Real.sin (x * y) =
      (-1 : ℂ) ^ n * Real.pi * Gamma (2 * n + 2 * lam + 1 : ℂ) * besselJ (2 * n + lam + 1) y /
        ((2 * n + 1).factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  sorry

@[dlmf 18.17.E19]
theorem legendre_fourier_transform (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (-1 : ℝ)..1, legendreP n x * exp (I * x * y) =
      I ^ n * Real.sqrt (2 * Real.pi / y) * besselJ (n + 1 / 2 : ℂ) y := by
  sorry

@[dlmf 18.17.E34]
theorem laguerre_laplace_transform {α : ℝ} (hα : -1 < α) (n : ℕ) {z : ℂ} (hz : -1 < z.re) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x * z) * laguerre α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (α + n + 1 : ℂ) * z ^ n / (n.factorial * (z + 1) ^ (α + n + 1 : ℂ)) := by
  exact laguerre_laplace_aux hα n hz

@[dlmf 18.17.E37]
theorem gegenbauer_mellin_transform {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      gegenbauer lam n x * (x : ℂ) ^ (z - 1) =
      Real.pi * (2 : ℂ) ^ (1 - 2 * lam - z) * Gamma (n + 2 * lam : ℂ) * Gamma z /
        (n.factorial * Gamma (lam : ℂ) * Gamma (1 / 2 + n / 2 + lam + z / 2) *
          Gamma (1 / 2 + z / 2 - n / 2)) := by
  sorry

/-- Finite-sum version, including parameters where the displayed hypergeometric quotient
has removable singularities. -/
@[dlmf 18.17.E40]
theorem laguerre_mellin_laplace_transform {a : ℝ} (ha : 0 < a) {α : ℂ} (hα : -1 < α.re)
    (b : ℂ) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-a * x) * laguerre α n (b * x) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ Finset.range (n + 1), poch (α + k + 1) (n - k) * (-b) ^ k /
        ((n - k).factorial * (k.factorial : ℂ)) * Gamma (z + k) / (a : ℂ) ^ (z + k) := by
  have hα' : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simp only [add_re, one_re]; linarith)
  have heq (x : ℝ) : laguerre α n (b * x) =
      ∑ k ∈ Finset.range (n + 1),
        (poch (α + k + 1) (n - k) * (-b) ^ k / ((n - k).factorial * (k.factorial : ℂ))) *
          (x : ℂ) ^ k := by
    rw [laguerre_eq_sum hα']
    apply Finset.sum_congr rfl
    intro k _
    rw [show -(b * (x : ℂ)) = -b * x by ring, mul_pow]
    rw [show α + 1 + (k : ℂ) = α + k + 1 by ring]
    ring
  simp_rw [heq]
  exact integral_finite_sum_mellin_laplace ha hz _ _ id

end AAR.OrthogonalPolynomials
