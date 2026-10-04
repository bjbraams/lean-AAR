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
public import AAR.Bessel.Basic
public import AAR.Gamma.IntegralRepresentations
public import TauCeti.Analysis.SpecialFunctions.Hermite.Orthogonality
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

@[dlmf 18.3.T1]
theorem jacobi_norm {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, jacobiP α β (n + 1) x ^ 2 *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) =
      (2 : ℂ) ^ ((α : ℂ) + β + 1) * Gamma (n + (α : ℂ) + 2) * Gamma (n + (β : ℂ) + 2) /
      ((2 * n + α + β + 3) * (n + 1).factorial * Gamma (n + (α : ℂ) + β + 2)) := by
  sorry

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
  sorry

@[dlmf 18.3.T1]
theorem gegenbauer_orthogonality {lam : ℝ} (hlam : 0 < lam) (m n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, gegenbauer lam m x * gegenbauer lam n x *
      (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) =
      if m = n then (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.pi * Gamma (n + 2 * (lam : ℂ)) /
        ((n + lam) * Gamma (lam : ℂ) ^ 2 * n.factorial) else 0 := by
  sorry

@[dlmf 18.5.E5]
theorem jacobi_rodrigues {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    jacobiP α β n x = (deriv^[n] (fun t : ℝ => (1 - t) ^ (α + n) * (1 + t) ^ (β + n)) x : ℝ) /
      ((-2 : ℂ) ^ n * n.factorial * (1 - x : ℂ) ^ (α : ℂ) * (1 + x : ℂ) ^ (β : ℂ)) := by
  sorry

@[dlmf 18.5.E5]
theorem laguerre_rodrigues {α : ℝ} (hα : -1 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerre α n x = (Real.exp x * x ^ (-α) *
      deriv^[n] (fun t : ℝ => Real.exp (-t) * t ^ (n + α)) x / n.factorial : ℝ) := by
  sorry

@[dlmf 18.10.E2]
theorem legendre_dirichlet_mehler (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    legendreP n (Real.cos θ) = (Real.sqrt 2 / Real.pi *
      ∫ phi : ℝ in (0 : ℝ)..θ, Real.cos ((n + 1 / 2) * phi) / Real.sqrt (Real.cos phi - Real.cos θ) : ℝ) := by
  sorry

@[dlmf 18.10.E4]
theorem gegenbauer_laplace_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (θ : ℝ) :
    gegenbauer lam n (Real.cos θ) / gegenbauer lam n 1 =
      Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) *
        ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ) := by
  sorry

@[dlmf 18.10.E5]
theorem legendre_laplace_integral (n : ℕ) (θ : ℝ) :
    legendreP n (Real.cos θ) = (Real.pi : ℂ)⁻¹ *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n := by
  sorry

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

/-- The Hermite recurrence in evaluated form. -/
lemma aeval_hermitePhys_succ_succ (x : ℂ) (n : ℕ) :
    (aeval x (hermitePhys (n + 2)) : ℂ) =
      2 * x * aeval x (hermitePhys (n + 1)) - 2 * (n + 1) * aeval x (hermitePhys n) := by
  rw [hermitePhys_succ (n + 1), hermitePhys_derivative]
  simp only [map_sub, map_mul, aeval_X, aeval_C, map_ofNat]
  push_cast
  ring

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

@[dlmf 18.17.E14]
theorem laguerre_fractional_integral {α μ x : ℝ} (hα : -1 < α) (hμ : 0 < μ) (hx : 0 < x) (n : ℕ) :
    (x : ℂ) ^ ((α : ℂ) + μ) * laguerre (α + μ) n x / Gamma (α + μ + n + 1 : ℂ) =
      ∫ y : ℝ in (0 : ℝ)..x, (y : ℂ) ^ (α : ℂ) * laguerre α n y / Gamma (α + n + 1 : ℂ) *
        (x - y : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ) := by
  sorry

@[dlmf 18.17.E15]
theorem laguerre_fractional_tail_integral {α μ x : ℝ} (hα : -1 < α) (hμ : 0 < μ) (hx : 0 ≤ x) (n : ℕ) :
    exp (-x) * laguerre α n x = ∫ y : ℝ in Set.Ioi x,
      exp (-y) * laguerre (α + μ) n y * (y - x : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ) := by
  sorry

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

@[dlmf 18.17.E47]
theorem laguerre_convolution {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β) (hx : 0 < x) (m n : ℕ) :
    ∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^ (α : ℂ) * laguerre α m t / laguerre α m 0 *
      (x - t : ℂ) ^ (β : ℂ) * laguerre β n (x - t) / laguerre β n 0 =
      Gamma (α + 1 : ℂ) * Gamma (β + 1 : ℂ) / Gamma (α + β + 2 : ℂ) *
      (x : ℂ) ^ (α + β + 1 : ℂ) * laguerre (α + β + 1) (m + n) x / laguerre (α + β + 1) (m + n) 0 := by
  sorry

@[dlmf 18.17.E48]
theorem hermitePhys_convolution (m n : ℕ) (x : ℝ) :
    ∫ y : ℝ, (aeval y (hermitePhys m) : ℝ) * Real.exp (-(y ^ 2)) *
      aeval (x - y) (hermitePhys n) * Real.exp (-((x - y) ^ 2)) =
      Real.sqrt Real.pi * (2 : ℝ) ^ (-((m : ℝ) + n + 1) / 2) *
      aeval (x / Real.sqrt 2) (hermitePhys (m + n)) * Real.exp (-(x ^ 2) / 2) := by
  sorry

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
  sorry

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
  sorry

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

@[dlmf 18.17.E23]
theorem hermite_even_cosine_transform (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n)) : ℝ) * Real.cos (x * y) =
      (-1 : ℝ) ^ n * Real.sqrt (Real.pi / 2) * y ^ (2 * n) * Real.exp (-(y ^ 2) / 2) := by
  sorry

@[dlmf 18.17.E27]
theorem hermite_odd_sine_transform (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n + 1)) : ℝ) * Real.sin (x * y) =
      (-1 : ℝ) ^ n * Real.sqrt (Real.pi / 2) * y ^ (2 * n + 1) * Real.exp (-(y ^ 2) / 2) := by
  sorry

@[dlmf 18.17.E25]
theorem hermite_product_cosine_transform (m n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m)) * Real.cos (x * y) =
      (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m) *
        exp (-(y : ℂ) ^ 2 / 2) * laguerre (2 * m) n ((y : ℂ) ^ 2) := by
  sorry

@[dlmf 18.17.E26]
theorem hermite_product_sine_transform (m n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m + 1)) * Real.sin (x * y) =
      (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m + 1) *
        exp (-(y : ℂ) ^ 2 / 2) * laguerre (2 * m + 1) n ((y : ℂ) ^ 2) := by
  sorry

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
