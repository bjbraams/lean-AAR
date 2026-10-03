/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.OrthogonalPolynomials.Hahn
public import AAR.OrthogonalPolynomials.Explicit
public import AAR.OrthogonalPolynomials.Differential
/-!
# Associated, Bessel, Pollaczek, Freud, and exceptional polynomials

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology

noncomputable section

set_option autoImplicit false

namespace AAR.OrthogonalPolynomials

/-- General associated family. The shift may be real, as in DLMF §18.30.
The `n = 0` step is written separately to avoid a negative natural index. -/
@[dlmf 18.30.E3]
def associated (A B C : ℝ → ℂ) (c : ℝ) : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, x => A c * x + B c
  | n + 2, x => (A (n + 1 + c) * x + B (n + 1 + c)) * associated A B C c (n + 1) x -
      C (n + 1 + c) * associated A B C c n x

@[dlmf 18.30.E9]
def associatedLaguerre (lam : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => -(t + 1 : ℂ)⁻¹)
    (fun t => (2 * t + lam + 1) / (t + 1)) (fun t => (t + lam) / (t + 1)) c

@[dlmf 18.30.E13]
def associatedHermite (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun _ => 2) (fun _ => 0) (fun t => 2 * t) c

@[dlmf 18.30.E16]
def associatedMeixnerPollaczek (lam phi : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => 2 * sin phi / (t + 1))
    (fun t => 2 * (t + lam) * cos phi / (t + 1))
    (fun t => (t + 2 * lam - 1) / (t + 1)) c

@[dlmf 18.35.E2]
def pollaczek (lam a b : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => 2 * (t + lam + a) / (t + 1))
    (fun t => 2 * b / (t + 1)) (fun t => (t + 2 * lam - 1) / (t + 1)) c

@[dlmf 18.34.E1]
def besselPolynomial (a : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), n + a - 1] [] (-x / 2)

/-- Polynomial form of the reversal, valid also at zero. -/
@[dlmf 18.34.E2]
def reverseBesselPolynomial (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch (n + 1) k *
    (-1 / 2 : ℂ) ^ k * x ^ (n - k) / k.factorial

@[dlmf 18.32.E2]
def freudWeight (α : ℝ) (Q : ℝ → ℝ) (x : ℝ) : ℝ :=
  |x| ^ α * Real.exp (-Q x)

/-- Degree `n + 1`: exceptional Laguerre has no degree-zero member. -/
@[dlmf 18.36.E5]
def exceptionalLaguerre (k : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  -(x + k + 1) * laguerre k n x + if n = 0 then 0 else laguerre k (n - 1) x

@[dlmf 18.36.E3]
def exceptionalLaguerreWeight (k x : ℝ) : ℝ := x ^ k * Real.exp (-x) / (x + k) ^ 2

/-- The exceptional Hermite degrees are 0, 3, 4, …; the index type omits 1 and 2. -/
@[dlmf 18.36.E9]
def exceptionalHermite : Option ℕ → ℝ → ℝ
  | none, _ => (2 : ℝ) ^ (3 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ)
  | some n, x => ((4 * x ^ 2 + 2) * aeval x (hermitePhys (n + 1)) +
      8 * x * aeval x (hermitePhys n)) /
      (Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ (n + 1) * (n + 3) * n.factorial))

@[dlmf 18.30.E2]
theorem associated_zero (A B C : ℝ → ℂ) (c : ℝ) (x : ℂ) : associated A B C c 0 x = 1 := by
  rfl

@[dlmf 18.30.E19]
theorem associatedPollaczek_limit_laguerre (lam : ℂ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : ℂ) :
    Tendsto (fun phi : ℝ => associatedMeixnerPollaczek ((lam + 1) / 2) phi c n (-x / (2 * sin (phi : ℂ))))
      (𝓝[>] 0) (𝓝 (associatedLaguerre lam c n x)) := by
  have hcos : Tendsto (fun phi : ℝ => cos (phi : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto (fun phi : ℝ => cos (phi : ℂ)) (𝓝 0) (𝓝 (cos ((0 : ℝ) : ℂ))) :=
      Continuous.tendsto (by fun_prop) 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hsin : ∀ᶠ phi : ℝ in 𝓝[>] 0, sin (phi : ℂ) ≠ 0 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.pi by positivity)] with phi hphi
    rw [← ofReal_sin]
    exact ofReal_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hphi.1 hphi.2).ne'
  have ht : ∀ n : ℕ, ((n : ℝ) + 1 + c : ℂ) + 1 ≠ 0 := fun n => by
    have : (0 : ℝ) < n + 1 + c + 1 := by positivity
    exact_mod_cast this.ne'
  refine tendsto_of_three_term
    (f := fun n (phi : ℝ) => associatedMeixnerPollaczek ((lam + 1) / 2) phi c n
      (-x / (2 * sin (phi : ℂ))))
    (g := fun n => associatedLaguerre lam c n x)
    (A := fun n (phi : ℝ) => -x / (((n + 1 + c : ℝ) : ℂ) + 1) +
      2 * (((n + 1 + c : ℝ) : ℂ) + (lam + 1) / 2) * cos (phi : ℂ) / (((n + 1 + c : ℝ) : ℂ) + 1))
    (B := fun n (_ : ℝ) => -((((n + 1 + c : ℝ) : ℂ) + 2 * ((lam + 1) / 2) - 1) /
      (((n + 1 + c : ℝ) : ℂ) + 1)))
    (A' := fun n => -x / (((n + 1 + c : ℝ) : ℂ) + 1) +
      2 * (((n + 1 + c : ℝ) : ℂ) + (lam + 1) / 2) * 1 / (((n + 1 + c : ℝ) : ℂ) + 1))
    (B' := fun n => -((((n + 1 + c : ℝ) : ℂ) + 2 * ((lam + 1) / 2) - 1) /
      (((n + 1 + c : ℝ) : ℂ) + 1))) ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp [associatedMeixnerPollaczek, associatedLaguerre, associated]
  · have hc1 : (c : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < c + 1 := by positivity
      exact_mod_cast this.ne'
    have h := (tendsto_const_nhds (x := -x / ((c : ℂ) + 1))).add
      ((hcos.const_mul (2 * ((c : ℂ) + (lam + 1) / 2))).div_const ((c : ℂ) + 1))
    have hv : -x / ((c : ℂ) + 1) + 2 * ((c : ℂ) + (lam + 1) / 2) * 1 / ((c : ℂ) + 1) =
        associatedLaguerre lam c 1 x := by
      simp only [associatedLaguerre, associated]
      field_simp
      ring
    rw [hv] at h
    refine h.congr' ?_
    filter_upwards [hsin] with phi hphi
    simp only [associatedMeixnerPollaczek, associated]
    field_simp
  · intro n
    exact tendsto_const_nhds.add (((hcos.const_mul _).div_const _))
  · intro n; exact tendsto_const_nhds
  · intro n
    filter_upwards [hsin] with phi hphi
    simp only [associatedMeixnerPollaczek, associated]
    push_cast
    field_simp
    ring
  · intro n
    simp only [associatedLaguerre, associated]
    push_cast
    field_simp
    ring

@[dlmf 18.30.E20]
theorem associatedPollaczek_limit_hermite {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : ℂ) :
    Tendsto (fun lam : ℝ => poch (c + 1) n * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      associatedMeixnerPollaczek lam (Real.pi / 2) c n (x * Real.sqrt lam)) atTop
      (𝓝 (associatedHermite c n x)) := by
  have hsc : sin ((Real.pi : ℂ) / 2) = 1 := Complex.sin_pi_div_two
  have hcc : cos ((Real.pi : ℂ) / 2) = 0 := Complex.cos_pi_div_two
  refine tendsto_of_three_term (f := fun n (lam : ℝ) => poch (c + 1) n * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      associatedMeixnerPollaczek lam (Real.pi / 2) c n (x * Real.sqrt lam))
    (g := fun n => associatedHermite c n x)
    (A := fun _ _ => 2 * x)
    (B := fun n (lam : ℝ) => -(((n : ℂ) + c + 1) * (2 + (n + c) / (lam : ℂ))))
    (A' := fun _ => 2 * x) (B' := fun n => -(((n : ℂ) + c + 1) * 2)) ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp [associatedMeixnerPollaczek, associatedHermite, associated, poch_zero]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with lam hl
    have hs : (Real.sqrt lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
    have hc1 : (c : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < c + 1 := by positivity
      exact_mod_cast this.ne'
    simp only [associatedMeixnerPollaczek, associatedHermite, associated, hsc, hcc, poch_one]
    field_simp
    ring
  · intro n; exact tendsto_const_nhds
  · intro n
    simpa only [add_zero] using
      (((tendsto_const_div_ofReal_atTop ((n : ℂ) + c)).const_add 2).const_mul
        ((n : ℂ) + c + 1)).neg
  · intro n
    filter_upwards [eventually_gt_atTop 0] with lam hl
    have hs : (Real.sqrt lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
    have hs2 : (lam : ℂ) = (Real.sqrt lam : ℂ) ^ 2 := by
      rw [← ofReal_pow, Real.sq_sqrt hl.le]
    have ht : ((n + 1 + c : ℝ) : ℂ) + 1 ≠ 0 := by
      have : (0 : ℝ) < n + 1 + c + 1 := by positivity
      exact_mod_cast this.ne'
    simp only [associatedMeixnerPollaczek, associated, hsc, hcc, poch_succ, inv_pow]
    rw [hs2]
    push_cast at ht ⊢
    field_simp
    ring
  · intro n
    simp only [associatedHermite, associated]
    push_cast
    ring

/-- `(a+1)_b = (a+b)!/a!` for natural `a`, in factorial form. -/
lemma poch_nat_succ_mul_factorial (a b : ℕ) :
    (a ! : ℂ) * poch ((a : ℂ) + 1) b = ((a + b) ! : ℂ) := by
  rw [poch_nat_succ_eq_choose_mul_factorial]
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right a b)
  rw [Nat.add_sub_cancel_left] at h
  have h' : ((a + b).choose a : ℂ) * a ! * b ! = (a + b)! := by exact_mod_cast h
  linear_combination h'

/-- Reflection of a Pochhammer symbol: `(1 - r - k)_k = (-1)^k (r)_k`. -/
lemma poch_reflect (r : ℂ) (k : ℕ) : poch (1 - r - k) k = (-1) ^ k * poch r k := by
  rw [poch, show (1 - r - k : ℂ) = -(r + k - 1) by ring, ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_ascPochhammer]
  congr 2
  ring

@[dlmf 18.34.E1]
theorem besselPolynomial_eq_laguerre (a : ℂ) (n : ℕ) {x : ℂ} (hx : x ≠ 0) :
    besselPolynomial a n x = (n.factorial : ℂ) * (-x / 2) ^ n * laguerreExtended (1 - a - 2 * n) n (2 / x) := by
  unfold besselPolynomial terminatingHG laguerreExtended
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  rw [Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show n + 1 - 1 - k = n - k by omega, Nat.sub_sub_self hkn]
  have e : (1 - a - 2 * n + ((n - k : ℕ) : ℂ) + 1) = 1 - (n + a - 1) - k := by
    push_cast [Nat.cast_sub hkn]; ring
  rw [e, poch_reflect]
  have p1 := poch_neg_nat_mul_factorial hkn
  have f1 : ((n - k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f2 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpow : (-x / 2) ^ n * (-(2 / x)) ^ (n - k) = (-x / 2) ^ k := by
    rw [show n = k + (n - k) by omega, pow_add, show k + (n - k) - k = n - k by omega, mul_assoc,
      ← mul_pow]
    rw [show -x / 2 * -(2 / x) = 1 by field_simp, one_pow, mul_one]
  have q1 : poch (-(n : ℂ)) k = (-1) ^ k * (n ! : ℂ) / (n - k) ! := by
    field_simp; linear_combination p1
  rw [q1]
  linear_combination (-(n ! : ℂ) * ((-1) ^ k * poch (n + a - 1) k / ((k ! : ℂ) * (n - k) !))) * hpow

@[dlmf 18.34.E2]
theorem reverseBesselPolynomial_eq (n : ℕ) {x : ℂ} (hx : x ≠ 0) :
    reverseBesselPolynomial n x = x ^ n * besselPolynomial 2 n x⁻¹ := by
  unfold reverseBesselPolynomial besselPolynomial terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hp : x ^ n = x ^ (n - k) * x ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  rw [show (n : ℂ) + 2 - 1 = n + 1 by ring, hp]
  rw [show -x⁻¹ / 2 = (-1 / 2 : ℂ) * x⁻¹ by ring, mul_pow, inv_pow]
  field_simp

@[dlmf 18.34.E4]
theorem besselPolynomial_recurrence (a : ℂ) (n : ℕ) (x : ℂ) :
    2 * (n + a) * (2 * n + a) * besselPolynomial a (n + 2) x =
      ((2 * n + a + 2) * (2 * n + a + 1) * (2 * n + a) * x +
        2 * (a - 2) * (2 * n + a + 1)) * besselPolynomial a (n + 1) x +
      2 * (n + 1) * (2 * n + a + 2) * besselPolynomial a n x := by
  sorry

@[dlmf 18.34.E7]
theorem besselPolynomial_differential_equation (a : ℂ) (n : ℕ) (x : ℂ) :
    x ^ 2 * deriv (deriv (besselPolynomial a n)) x + (a * x + 2) * deriv (besselPolynomial a n) x -
      n * (n + a - 1) * besselPolynomial a n x = 0 := by
  set c : ℕ → ℂ := fun k =>
    poch (-(n : ℂ)) k * poch (n + a - 1) k * (-1 / 2) ^ k / (k.factorial : ℂ)
  set p : ℂ[X] := ∑ k ∈ Finset.range (n + 1), C (c k) * X ^ k
  have hp : besselPolynomial a n = fun x => p.eval x := by
    funext x
    unfold besselPolynomial terminatingHG
    simp only [p, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, c, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show -x / 2 = (-1 / 2) * x by ring, mul_pow]; ring
  have hcoeff : ∀ j, p.coeff j = c j := by
    intro j
    simp only [p, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · simp only [Finset.mem_range, not_lt] at h
      simp [c, poch_neg_nat_eq_zero (by omega : n < j)]
  have hc : ∀ k, 2 * (k + 1) * c (k + 1) = -((k - n) * (k + n + a - 1)) * c k := by
    intro k
    simp only [c, poch_succ, pow_succ, Nat.factorial_succ]
    have : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    push_cast
    field_simp
    ring
  have hQ : X ^ 2 * derivative (derivative p) + (C a * X + 2) * derivative p -
      C ((n : ℂ) * (n + a - 1)) * p = 0 := by
    ext k
    have e2 : (2 : ℂ[X]) = C 2 := rfl
    rw [coeff_zero, e2, show (C a * X + C 2) * derivative p =
      C a * (X ^ 1 * derivative p) + C 2 * derivative p by ring]
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow_mul', coeff_derivative,
      hcoeff]
    rcases k with _ | _ | k
    · have := hc 0
      simp only [zero_add, Nat.reduceLeDiff, ↓reduceIte]
      push_cast at this ⊢
      linear_combination this
    · have := hc 1
      simp only [zero_add, Nat.reduceLeDiff, ↓reduceIte, Nat.sub_self]
      push_cast at this ⊢
      linear_combination this
    · have := hc (k + 2)
      simp only [show 2 ≤ k + 1 + 1 by omega, show 1 ≤ k + 1 + 1 by omega, ↓reduceIte,
        show k + 1 + 1 - 2 = k by omega, show k + 1 + 1 - 1 = k + 1 by omega]
      push_cast at this ⊢
      linear_combination this
  have hd : deriv (besselPolynomial a n) = fun x => (derivative p).eval x := by
    rw [hp]; funext x; exact Polynomial.deriv p
  rw [hd, hp]
  simp only [Polynomial.deriv]
  have := congrArg (eval x) hQ
  simpa [eval_add, eval_sub, eval_mul] using this

@[dlmf 18.34.E5_5]
theorem besselPolynomial_finite_orthogonality {a : ℝ} (m n : ℕ) (ha : a < 1 - 2 * max m n) :
    (2 : ℂ) ^ (1 - (a : ℂ)) / Gamma (1 - (a : ℂ)) *
      (∫ x : ℝ in Set.Ioi 0, besselPolynomial a m x * besselPolynomial a n x *
        (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)) =
      if m = n then (1 - a) / (1 - a - 2 * (n : ℂ)) * n.factorial / poch (2 - a - n) n else 0 := by
  sorry

@[dlmf 18.34.E8]
theorem jacobi_limit_besselPolynomial (a : ℂ) (n : ℕ) (x : ℂ) :
    Tendsto (fun α : ℝ => jacobiP α (a - α - 2) n (1 + α * x) / jacobiP α (a - α - 2) n 1) atTop
      (𝓝 (besselPolynomial a n x)) := by
  unfold besselPolynomial terminatingHG
  have hlim : Tendsto (fun α : ℝ => ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k * poch (n + a - 1) k * (-x / 2) ^ k / k ! *
        (poch (1 + (α : ℂ)) k / (α : ℂ) ^ k)⁻¹) atTop
      (𝓝 (∑ k ∈ Finset.range (n + 1),
        poch (-(n : ℂ)) k * poch (n + a - 1) k * (-x / 2) ^ k / k ! * 1⁻¹)) := by
    apply tendsto_finsetSum
    intro k _
    exact ((tendsto_poch_add_div_pow 1 k).inv₀ one_ne_zero).const_mul _
  simp only [inv_one, mul_one] at hlim
  refine (hlim.congr' ?_).trans ?_
  · filter_upwards [eventually_gt_atTop 0] with α hα
    have hα' : (α : ℂ) ≠ 0 := ofReal_ne_zero.mpr hα.ne'
    have hc : ∀ k : ℕ, (α : ℂ) + 1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
    have hp : poch ((α : ℂ) + 1) n / n ! ≠ 0 :=
      div_ne_zero (poch_ne_zero_of_not_neg_nat hc n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
    have h0 : ₂F₁ (-(n : ℂ)) (n + α + (a - α - 2) + 1) (α + 1) (0 : ℂ) = 1 := by
      rw [ordinaryHypergeometric_eq_sum_neg_nat, Finset.sum_range_succ']
      simp [gaussHGCoeff, poch_zero]
    unfold jacobiP
    rw [show ((1 : ℂ) - 1) / 2 = 0 by ring, h0, mul_one, mul_div_cancel_left₀ _ hp,
      ordinaryHypergeometric_eq_sum_neg_nat]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hpk : poch ((α : ℂ) + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hc k
    unfold gaussHGCoeff
    rw [show (n : ℂ) + α + (a - α - 2) + 1 = n + a - 1 by ring,
      show (1 - (1 + (α : ℂ) * x)) / 2 = α * (-x / 2) by ring, mul_pow, add_comm (1 : ℂ)]
    field_simp
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
    rfl

@[dlmf 18.35.E2_5]
theorem pollaczek_reflection (lam a b : ℂ) (c : ℝ) (n : ℕ) (x : ℂ) :
    pollaczek lam a b c n (-x) = (-1 : ℂ) ^ n * pollaczek lam a (-b) c n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pollaczek, associated]
  | one => simp [pollaczek, associated]; ring
  | more n ih0 ih1 =>
    change (2 * ((n + 1 + c : ℝ) + lam + a) / ((n + 1 + c : ℝ) + 1) * (-x) +
      2 * b / ((n + 1 + c : ℝ) + 1)) * pollaczek lam a b c (n + 1) (-x) -
      (((n + 1 + c : ℝ) + 2 * lam - 1) / ((n + 1 + c : ℝ) + 1)) * pollaczek lam a b c n (-x) = _
    rw [ih0, ih1]
    simp only [pollaczek, associated, pow_succ]
    ring

@[dlmf 18.35.E4]
theorem pollaczek_finite_sum (lam a b : ℂ) (n : ℕ) {θ : ℂ} (hθ : sin θ ≠ 0) :
    pollaczek lam a b 0 n (cos θ) = ∑ k ∈ Finset.range (n + 1),
      poch (lam + I * (a * cos θ + b) / sin θ) k / k.factorial *
      (poch (lam - I * (a * cos θ + b) / sin θ) (n - k) / (n - k).factorial) *
      exp (I * ((n : ℂ) - 2 * k) * θ) := by
  sorry

@[dlmf 18.35.E7]
theorem pollaczek_generating_function (lam a b : ℂ) (θ : ℝ) (hθ : Real.sin θ ≠ 0) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => pollaczek lam a b 0 n (Real.cos θ) * z ^ n)
      ((1 - z * exp (I * θ)) ^ (-lam + I * (a * Real.cos θ + b) / Real.sin θ) *
       (1 - z * exp (-I * θ)) ^ (-lam - I * (a * Real.cos θ + b) / Real.sin θ)) := by
  sorry

@[dlmf 18.35.E8]
theorem pollaczek_eq_gegenbauer {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    pollaczek lam 0 0 0 n x = gegenbauer lam n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pollaczek, associated]
  | one => simp [pollaczek, associated, gegenbauer_one_eq hlam]
  | more n ih0 ih1 =>
    have hr := gegenbauer_recurrence hlam n x
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    simp only [pollaczek, associated] at ih0 ih1 ⊢
    rw [ih0, ih1]
    push_cast
    simp only [add_zero, mul_zero, zero_div]
    rw [show (n : ℂ) + 1 + 1 = n + 2 by ring]
    field_simp
    linear_combination -hr


@[dlmf 18.35.E9]
theorem pollaczek_eq_meixnerPollaczek {lam : ℂ} (hlam : 0 < lam.re) (phi x : ℂ) (n : ℕ) :
    pollaczek lam 0 (x * sin phi) 0 n (cos phi) = meixnerPollaczek lam phi n x := by
  have hl : lam ≠ 0 := fun h => by simp [h] at hlam
  induction n using Nat.twoStepInduction with
  | zero => simp [pollaczek, associated, meixnerPollaczek, terminatingHG, poch_zero]
  | one =>
    simp [pollaczek, associated, meixnerPollaczek_one hl]
    ring
  | more n ih0 ih1 =>
    have hr := meixnerPollaczek_recurrence hlam phi n x
    have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    simp only [pollaczek, associated] at ih0 ih1 ⊢
    rw [ih0, ih1]
    push_cast
    simp only [add_zero]
    rw [show (n : ℂ) + 1 + 1 = n + 2 by ring]
    field_simp
    linear_combination -hr

@[dlmf 18.35.E10]
theorem pollaczek_eq_associatedMeixnerPollaczek (lam phi x : ℂ) (c : ℝ) (n : ℕ) :
    pollaczek lam 0 (x * sin phi) c n (cos phi) = associatedMeixnerPollaczek lam phi c n x := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [pollaczek, associatedMeixnerPollaczek, associated]; ring
  | more n ih0 ih1 =>
    change (2 * ((n + 1 + c : ℝ) + lam + 0) / ((n + 1 + c : ℝ) + 1) * cos phi +
      2 * (x * sin phi) / ((n + 1 + c : ℝ) + 1)) * pollaczek lam 0 (x * sin phi) c (n + 1) (cos phi) -
      (((n + 1 + c : ℝ) + 2 * lam - 1) / ((n + 1 + c : ℝ) + 1)) * pollaczek lam 0 (x * sin phi) c n (cos phi) = _
    rw [ih0, ih1]
    simp only [associatedMeixnerPollaczek, associated]
    ring

@[dlmf 18.36.E2]
theorem laguerre_negative_integer_parameter {n k : ℕ} (hk : k ≤ n) (x : ℂ) :
    laguerreExtended (-(k : ℂ)) n x = (-1 : ℂ) ^ k * (n - k).factorial / n.factorial * x ^ k * laguerre k (n - k) x := by
  have hα : ∀ j : ℕ, (k : ℂ) + 1 ≠ -(j : ℂ) := by
    intro j h
    have : ((k + 1 + j : ℕ) : ℂ) = 0 := by push_cast; linear_combination h
    exact absurd (by exact_mod_cast this : k + 1 + j = 0) (by omega)
  rw [laguerre_eq_sum hα]
  unfold laguerreExtended
  obtain ⟨N, rfl⟩ : ∃ N, n = k + N := ⟨n - k, by omega⟩
  rw [show k + N + 1 = k + (N + 1) by ring, Finset.sum_range_add, Nat.add_sub_cancel_left]
  have hzero : ∑ j ∈ Finset.range k, poch (-(k : ℂ) + j + 1) (k + N - j) /
      ((j.factorial : ℂ) * (k + N - j).factorial) * (-x) ^ j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hjk := Finset.mem_range.mp hj
    have : poch (-(k : ℂ) + j + 1) (k + N - j) = 0 := by
      rw [poch, ascPochhammer_eval_eq_zero_iff]
      refine ⟨k - 1 - j, by omega, ?_⟩
      push_cast [show 1 + j ≤ k by omega, Nat.sub_sub]
      ring
    simp [this]
  rw [hzero, zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have e1 : k + N - (k + m) = N - m := by omega
  have e2 : -(k : ℂ) + ((k + m : ℕ) : ℂ) + 1 = (m : ℂ) + 1 := by push_cast; ring
  have e3 : (k : ℂ) + 1 + (m : ℂ) = ((k + m : ℕ) : ℂ) + 1 := by push_cast; ring
  rw [e1, e2, e3]
  have p1 := poch_nat_succ_mul_factorial m (N - m)
  have p2 := poch_nat_succ_mul_factorial (k + m) (N - m)
  rw [show m + (N - m) = N by omega] at p1
  rw [show k + m + (N - m) = k + N by omega] at p2
  have f1 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f2 : ((k + m) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f3 : ((N - m) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have f4 : ((k + N) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have q1 : poch ((m : ℂ) + 1) (N - m) = (N ! : ℂ) / m ! := by
    field_simp; linear_combination p1
  have q2 : poch (((k + m : ℕ) : ℂ) + 1) (N - m) = ((k + N) ! : ℂ) / (k + m) ! := by
    field_simp; linear_combination p2
  rw [q1, q2, pow_add, show (-x) ^ k = (-1) ^ k * x ^ k by ring]
  field_simp

lemma analyticAt_laguerre {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    AnalyticAt ℂ (laguerre α n) x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]; linarith)
  have he : laguerre α n = fun z => poch (α + 1) n / (n.factorial : ℂ) *
      confluentM (-(n : ℂ)) (α + 1) z := rfl
  rw [he]
  exact analyticAt_const.mul ((hasFPowerSeriesOnBall_confluentM (a := -(n : ℂ)) hc).analyticAt_of_mem
    (by simp))

/-- `L'_{m+1} - L'_m + L_m = 0`. -/
lemma laguerre_deriv_succ_sub {α : ℂ} (hα : -1 < α.re) (m : ℕ) (x : ℂ) :
    deriv (laguerre α (m + 1)) x - deriv (laguerre α m) x + laguerre α m x = 0 := by
  rcases m with _ | j
  · have h0 : laguerre α 0 = fun _ => 1 := funext fun x => laguerre_zero α x
    rw [laguerre_derivative hα 0, h0, deriv_const, laguerre_zero]
    simp [laguerre_zero]
  · have hα1 : -1 < (α + 1).re := by simp; linarith
    rw [laguerre_derivative hα (j + 1), laguerre_derivative hα j, laguerre_raise_parameter hα j]
    ring

@[dlmf 18.36.E6]
theorem exceptionalLaguerre_orthogonality {k : ℝ} (hk : 0 < k) (m n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exceptionalLaguerre k m x * exceptionalLaguerre k n x * exceptionalLaguerreWeight k x =
      if m = n then (n + 1 + (k : ℂ)) * Gamma (n + (k : ℂ)) / n.factorial else 0 := by
  sorry

@[dlmf 18.36.E7]
theorem exceptionalLaguerre_differential_equation {k : ℝ} (hk : 0 < k) (n : ℕ) {x : ℂ} (hx : x + k ≠ 0) :
    -x * deriv (deriv (exceptionalLaguerre k n)) x + (x - k) / (x + k) *
      ((x + k + 1) * deriv (exceptionalLaguerre k n) x - exceptionalLaguerre k n x) =
      n * exceptionalLaguerre k n x := by
  have hα : -1 < (k : ℂ).re := by simp; linarith
  have hL : ∀ j y, HasDerivAt (laguerre (k : ℂ) j) (deriv (laguerre (k : ℂ) j) y) y := fun j y =>
    (analyticAt_laguerre hα j y).differentiableAt.hasDerivAt
  have hL' : ∀ j y, HasDerivAt (deriv (laguerre (k : ℂ) j)) (deriv (deriv (laguerre (k : ℂ) j)) y) y :=
    fun j y => (analyticAt_laguerre hα j y).deriv.differentiableAt.hasDerivAt
  rcases n with _ | m
  · have he : exceptionalLaguerre k 0 = fun y : ℂ => -(y + (k : ℂ) + 1) := by
      funext y; simp [exceptionalLaguerre, laguerre_zero]
    have hd : deriv (exceptionalLaguerre k 0) = fun _ => -1 := by
      rw [he]; funext y
      have := ((hasDerivAt_id y).add_const ((k : ℂ) + 1)).neg
      simpa [add_assoc] using this.deriv
    rw [hd, he, deriv_const]
    push_cast; ring
  · have he : exceptionalLaguerre k (m + 1) = fun y => -(y + k + 1) * laguerre (k : ℂ) (m + 1) y +
        laguerre (k : ℂ) m y := by
      funext y; simp [exceptionalLaguerre]
    have hd1 : ∀ y, HasDerivAt (exceptionalLaguerre k (m + 1))
        (-laguerre (k : ℂ) (m + 1) y - (y + k + 1) * deriv (laguerre (k : ℂ) (m + 1)) y +
          deriv (laguerre (k : ℂ) m) y) y := by
      intro y
      rw [he]
      have := ((((hasDerivAt_id y).add_const ((k : ℂ) + 1)).neg).mul (hL (m + 1) y)).add (hL m y)
      convert this using 1
      · funext z; simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, id]; ring
      · simp; ring
    have hd : deriv (exceptionalLaguerre k (m + 1)) = fun y =>
        -laguerre (k : ℂ) (m + 1) y - (y + k + 1) * deriv (laguerre (k : ℂ) (m + 1)) y +
          deriv (laguerre (k : ℂ) m) y := funext fun y => (hd1 y).deriv
    have hd2 : deriv (deriv (exceptionalLaguerre k (m + 1))) x =
        -2 * deriv (laguerre (k : ℂ) (m + 1)) x -
          (x + k + 1) * deriv (deriv (laguerre (k : ℂ) (m + 1))) x +
          deriv (deriv (laguerre (k : ℂ) m)) x := by
      rw [hd]
      have h2 : HasDerivAt (fun y => -laguerre (k : ℂ) (m + 1) y -
          (y + k + 1) * deriv (laguerre (k : ℂ) (m + 1)) y + deriv (laguerre (k : ℂ) m) y)
          (-2 * deriv (laguerre (k : ℂ) (m + 1)) x -
          (x + k + 1) * deriv (deriv (laguerre (k : ℂ) (m + 1))) x +
          deriv (deriv (laguerre (k : ℂ) m)) x) x := by
        have := (((hL (m + 1) x).neg.sub (((hasDerivAt_id x).add_const ((k : ℂ) + 1)).mul
          (hL' (m + 1) x))).add (hL' m x))
        convert this using 1
        · funext y; simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply, id]; ring
        · simp; ring
      exact h2.deriv
    rw [hd2, (hd1 x).deriv, he]
    have E1 := laguerre_differential_equation hα (m + 1) x
    have E2 := laguerre_differential_equation hα m x
    have R2 := laguerre_deriv_succ_sub hα m x
    field_simp
    push_cast at E1 E2 ⊢
    linear_combination (x + k) * (x + k + 1) * E1 - (x + k) * E2 - 2 * x * R2

@[dlmf 18.36.E10]
theorem exceptionalHermite_orthonormal (m n : Option ℕ) :
    ∫ x : ℝ, exceptionalHermite m x * exceptionalHermite n x *
      (Real.exp (-(x ^ 2)) / (4 * x ^ 2 + 2) ^ 2) = if m = n then 1 else 0 := by
  sorry


@[dlmf 18.35.E3]
def pollaczekTau (a b θ : ℝ) : ℝ := (a * Real.cos θ + b) / Real.sin θ

/-- Angular density, including the Jacobian `sin θ` for `x = cos θ`. -/
@[dlmf 18.35.E6]
def pollaczekAngularWeight (lam a b θ : ℝ) : ℝ :=
  Real.pi⁻¹ * Real.exp ((2 * θ - Real.pi) * pollaczekTau a b θ) *
    (2 * Real.sin θ) ^ (2 * lam - 1) * ‖Gamma (lam + I * pollaczekTau a b θ)‖ ^ 2 * Real.sin θ

@[dlmf 18.35.E5]
theorem pollaczek_orthogonality {lam a b : ℝ} (hlam : 0 < lam) (hab : |b| ≤ a) (m n : ℕ) :
    ∫ θ : ℝ in (0 : ℝ)..Real.pi, pollaczek lam a b 0 m (Real.cos θ) *
      pollaczek lam a b 0 n (Real.cos θ) * pollaczekAngularWeight lam a b θ =
      if m = n then Gamma (2 * (lam : ℂ) + n) / (n.factorial * (lam + a + n)) else 0 := by
  sorry

/-- The finite family related to the Morse differential equation. -/
@[dlmf 18.34.E7_1]
def morsePolynomialFunction (lam : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  Real.exp (-lam * Real.exp (-x)) * (2 * lam * Real.exp (-x) : ℂ) ^ (lam - 1 / 2 : ℂ) *
    besselPolynomial (2 - 2 * lam) n (lam⁻¹ * Real.exp x) / n.factorial

@[dlmf 18.34.E7_2]
theorem morsePolynomialFunction_ode {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (x : ℝ) :
    deriv (deriv (morsePolynomialFunction lam n)) x -
      (lam ^ 2 * (Real.exp (-2 * x) - 2 * Real.exp (-x)) + (lam - (n + 1 / 2)) ^ 2 : ℝ) *
        morsePolynomialFunction lam n x = 0 := by
  sorry

@[dlmf 18.34.E7_3]
theorem morsePolynomialFunction_orthogonality {lam : ℝ} (m n : ℕ) (hm : (m : ℝ) < lam - 1 / 2) (hn : (n : ℝ) < lam - 1 / 2) :
    ∫ x : ℝ, morsePolynomialFunction lam m x * morsePolynomialFunction lam n x =
      if m = n then Gamma (2 * (lam : ℂ) - n) / ((2 * lam - 2 * n - 1) * n.factorial) else 0 := by
  sorry


end AAR.OrthogonalPolynomials
