/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
/-!
# Kernels, moments, recurrence coefficients, and zeros

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
The compact-support expansion uses the Tau Ceti contributors' polynomial
completeness and weighted Hilbert-basis construction, as in `General`.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology

noncomputable section

set_option autoImplicit false

namespace AAR.OrthogonalPolynomials

@[dlmf 18.2.E5]
def squaredNorm (μ : Measure ℝ) (p : ℕ → ℝ[X]) (n : ℕ) : ℝ :=
  ∫ x, (p n).eval x ^ 2 ∂μ

@[dlmf 18.2.E12]
def christoffelDarbouxKernel (μ : Measure ℝ) (p : ℕ → ℝ[X]) (n : ℕ) (x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (p k).eval x * (p k).eval y / squaredNorm μ p k

@[dlmf 18.2.E26]
def moment (μ : Measure ℝ) (n : ℕ) : ℝ := ∫ x, x ^ n ∂μ

@[dlmf 18.2.E27]
def hankelDeterminant (μ : Measure ℝ) (n : ℕ) : ℝ :=
  Matrix.det (fun i j : Fin n => moment μ (i.val + j.val))

/-- The coefficient of degree `n` in `X p_n`, expanded in the OP basis. -/
@[dlmf 18.2.E11]
def recurrenceDiagonal {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) (n : ℕ) : ℝ :=
  h.basis.repr (X * p n) n

@[dlmf 18.2.E5_5]
theorem integral_product {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p) (m n : ℕ) :
    ∫ x, (p m).eval x * (p n).eval x ∂μ = if m = n then squaredNorm μ p n else 0 := by
  by_cases hmn : m = n
  · subst m
    simp [squaredNorm, pow_two]
  · simp [hmn, h.2.2.2 m n hmn]

@[dlmf 18.2.E11]
theorem recurrenceDiagonal_eq_integral {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p) (n : ℕ) :
    recurrenceDiagonal h n = (∫ x, x * (p n).eval x ^ 2 ∂μ) / squaredNorm μ p n := by
  apply (eq_div_iff (ne_of_gt (h.2.2.1 n))).mpr
  calc
    _ = ∫ x, (X * p n).eval x * (p n).eval x ∂μ := (h.integral_mul (X * p n) n).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Polynomial.eval_mul, Polynomial.eval_X]
      ring)

/-- DLMF 18.2.11₁ has a sign error (checked 2026-09-16). The telescoping
sum of 18.2.11 is the *negative* coefficient ratio, as stated here. -/
@[dlmf 18.2.E11_1]
theorem sum_recurrenceDiagonal {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), recurrenceDiagonal h j = -(p (n + 1)).coeff n / (p (n + 1)).leadingCoeff := by
  have hc (j : ℕ) : (X * p j).coeff j / (p j).leadingCoeff =
      recurrenceDiagonal h j + (p (j + 1)).coeff j / (p (j + 1)).leadingCoeff := by
    have he := congrArg (fun q : ℝ[X] => q.coeff j)
      (h.expansion (q := X * p j) (N := j + 2) (by
        rw [h.degree_X_mul]
        exact_mod_cast Nat.lt_succ_self (j + 1)))
    simp only [finsetSum_coeff, coeff_smul, smul_eq_mul] at he
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at he
    have hz : ∑ k ∈ Finset.range j, h.basis.repr (X * p j) k * (p k).coeff j = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [coeff_eq_zero_of_natDegree_lt (by rw [h.1]; exact Finset.mem_range.mp hk), mul_zero]
    have hj : (p j).coeff j = (p j).leadingCoeff := by
      simpa only [h.1] using (p j).coeff_natDegree
    rw [hz, zero_add, hj, h.repr_X_mul_top] at he
    dsimp [recurrenceDiagonal]
    have h0 := leadingCoeff_ne_zero.mpr (h.ne_zero j)
    have h1 := leadingCoeff_ne_zero.mpr (h.ne_zero (j + 1))
    rw [he]
    field_simp
  induction n with
  | zero =>
    have he := hc 0
    simp only [coeff_X_mul_zero, zero_div] at he
    simpa [neg_div] using (eq_neg_of_add_eq_zero_left he.symm)
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have he := hc (n + 1)
    rw [coeff_X_mul] at he
    simp only [neg_div]
    linarith

/-- Integration against the kernel is a finite sum of orthogonal coordinates. -/
lemma integral_mul_kernel {μ : Measure ℝ} {p : ℕ → ℝ[X]}
    (h : IsOrthogonalPolynomials μ p) {f : ℝ → ℝ} (hf : MemLp f 2 μ) (n : ℕ) (x : ℝ) :
    ∫ y, f y * christoffelDarbouxKernel μ p n x y ∂μ =
      ∑ k ∈ Finset.range (n + 1), (p k).eval x / squaredNorm μ p k *
        ∫ y, f y * (p k).eval y ∂μ := by
  have he (y : ℝ) : f y * christoffelDarbouxKernel μ p n x y =
      ∑ k ∈ Finset.range (n + 1), (p k).eval x / squaredNorm μ p k *
        (f y * (p k).eval y) := by
    unfold christoffelDarbouxKernel
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [he]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
  · intro k _
    exact (hf.integrable_mul (h.memLp_eval (p k))).const_mul _

@[dlmf 18.2.E12_5]
theorem kernel_reproduces {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    (n : ℕ) (f : ℝ[X]) (hf : f.degree ≤ n) (x : ℝ) :
    ∫ y, f.eval y * christoffelDarbouxKernel μ p n x y ∂μ = f.eval x := by
  rw [integral_mul_kernel h (h.memLp_eval f)]
  simp_rw [h.integral_mul]
  have he := congrArg (fun q : ℝ[X] => q.eval x)
    (h.expansion (q := f) (N := n + 1) (hf.trans_lt (by exact_mod_cast Nat.lt_succ_self n)))
  simp only [eval_finsetSum, smul_eq_C_mul, eval_mul, eval_C] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [squaredNorm]
  field_simp [ne_of_gt (h.2.2.1 k)]

@[dlmf 18.2.E13]
theorem christoffel_darboux_diagonal {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p) (n : ℕ) (x : ℝ) :
    christoffelDarbouxKernel μ p n x x = (p n).leadingCoeff /
      (squaredNorm μ p n * (p (n + 1)).leadingCoeff) *
      ((derivative (p (n + 1))).eval x * (p n).eval x - (derivative (p n)).eval x * (p (n + 1)).eval x) := by
  let K : ℝ[X] := ∑ k ∈ Finset.range (n + 1), C ((p k).eval x / squaredNorm μ p k) * p k
  let A : ℝ := (p n).leadingCoeff / ((p (n + 1)).leadingCoeff * squaredNorm μ p n)
  have hK (t : ℝ) : K.eval t = christoffelDarbouxKernel μ p n t x := by
    simp only [K, eval_finsetSum, Polynomial.eval_mul, eval_C, christoffelDarbouxKernel]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hp : (X - C x) * K = C A *
      (C ((p n).eval x) * p (n + 1) - C ((p (n + 1)).eval x) * p n) := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, eval_C, hK]
    by_cases ht : t = x
    · subst t
      ring
    · have hc := christoffel_darboux h (n := n + 1) (by omega) ht
      simp only [Nat.add_sub_cancel] at hc
      dsimp [A]
      unfold christoffelDarbouxKernel squaredNorm
      rw [hc]
      field_simp [sub_ne_zero.mpr ht]
  have hd := congrArg (fun q : ℝ[X] => q.derivative.eval x) hp
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    eval_C, sub_self, zero_mul, zero_add, add_zero, one_mul] at hd
  rw [hK] at hd
  simpa [A, mul_comm, mul_left_comm, mul_assoc] using hd

@[dlmf 18.2.E16]
theorem kernel_difference (μ : Measure ℝ) (p : ℕ → ℝ[X]) (n : ℕ) (x y : ℝ) :
    christoffelDarbouxKernel μ p (n + 1) x y - christoffelDarbouxKernel μ p n x y =
      (p (n + 1)).eval x * (p (n + 1)).eval y / squaredNorm μ p (n + 1) := by
  simp only [christoffelDarbouxKernel, Finset.sum_range_succ]
  ring

@[dlmf 18.2.E27]
theorem hankelDeterminant_pos {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p) (n : ℕ) :
    0 < hankelDeterminant μ n := by
  unfold hankelDeterminant
  change 0 < (Matrix.of fun i j : Fin n => moment μ (i + j)).det
  apply Matrix.PosDef.det_pos
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun v hv => ?_⟩
  · ext i j
    simp [Matrix.conjTranspose_apply, add_comm]
  -- the quadratic form is the integral of the square of `∑ v i X^i`
  set q : ℝ[X] := ∑ i : Fin n, C (v i) * X ^ (i : ℕ) with hq_def
  have hint (i j : ℕ) : Integrable (fun x : ℝ => x ^ (i + j)) μ := by
    simpa [pow_add] using h.integrable_mul (X ^ i) (X ^ j)
  have hquad : dotProduct (star v) ((Matrix.of fun i j : Fin n => moment μ (i + j)).mulVec v) =
      ∫ x, q.eval x ^ 2 ∂μ := by
    have hsq (x : ℝ) : q.eval x ^ 2 = ∑ i : Fin n, ∑ j : Fin n, v i * v j * x ^ ((i : ℕ) + j) := by
      simp only [hq_def, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, sq,
        Finset.sum_mul, Finset.mul_sum, pow_add]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have hij (i j : Fin n) : Integrable (fun x : ℝ => v i * v j * x ^ ((i : ℕ) + j)) μ :=
      (hint i j).const_mul _
    simp_rw [hsq]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hij i j]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => hij i j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, moment]
    ring
  rw [hquad]
  have hdeg : q.degree < n := degree_sum_fin_lt v
  have hq0 : q ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    intro hq
    apply hi
    have := congrArg (fun r : ℝ[X] => r.coeff i) hq
    simp only [hq_def, finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at this
    rw [Finset.sum_eq_single i (fun j _ hj => by
      simp [Fin.val_eq_val, Ne.symm hj]) (by simp)] at this
    simpa using this
  exact h.integral_eval_sq_pos hq0 hdeg

@[dlmf 18.2.E11_4]
theorem monic_squaredNorm_ratio {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    (hmonic : ∀ n, (p n).Monic) (n : ℕ) :
    h.basis.repr (X * p (n + 1)) n = squaredNorm μ p (n + 1) / squaredNorm μ p n := by
  have ht := h.repr_X_mul_top n
  rw [(hmonic n).leadingCoeff, (hmonic (n + 1)).leadingCoeff, div_self one_ne_zero] at ht
  have hs := h.repr_X_mul_symm n (n + 1)
  rw [ht] at hs
  apply (eq_div_iff (ne_of_gt (h.2.2.1 n))).mpr
  have he := (div_eq_div_iff (ne_of_gt (h.2.2.1 n)) (ne_of_gt (h.2.2.1 (n + 1)))).mp hs
  simpa [squaredNorm] using he.symm

@[dlmf 18.2.vi]
theorem zeros_interlace {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p) (n : ℕ) :
    ∃ x : Fin n → ℝ, ∃ y : Fin (n + 1) → ℝ, StrictMono x ∧ StrictMono y ∧
      (∀ i, (p n).eval (x i) = 0) ∧ (∀ i, (p (n + 1)).eval (y i) = 0) ∧
      ∀ i : Fin n, y i.castSucc < x i ∧ x i < y i.succ := by
  sorry

@[dlmf 18.2.E21]
theorem symmetric_measure_parity {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    (hμ : Measure.map (fun x : ℝ => -x) μ = μ) (n : ℕ) (x : ℝ) :
    (p n).eval (-x) = (-1 : ℝ) ^ n * (p n).eval x := by
  set r : ℝ[X] := (p n).comp (-X) - C ((-1 : ℝ) ^ n) * p n with hr_def
  have hpn : (p n).natDegree = n := h.1 n
  -- the leading terms cancel
  have hdeg : r.degree < n := by
    rcases eq_or_ne r 0 with hr0 | hr0
    · rw [hr0, degree_zero]; exact WithBot.bot_lt_coe n
    have hf : ((p n).comp (-X)).degree = n := by
      rw [degree_comp_neg_X, degree_eq_natDegree (h.ne_zero n), hpn]
    have hg : (C ((-1 : ℝ) ^ n) * p n).degree = n := by
      rw [degree_C_mul (pow_ne_zero _ (by norm_num)), degree_eq_natDegree (h.ne_zero n), hpn]
    have hlc : ((p n).comp (-X)).leadingCoeff = (C ((-1 : ℝ) ^ n) * p n).leadingCoeff := by
      rw [comp_neg_X_leadingCoeff_eq, leadingCoeff_C_mul_of_isUnit (by simp), hpn]
    have := degree_sub_lt_left (hf.trans hg.symm)
      (by rw [Ne, ← degree_eq_bot, hf]; exact WithBot.coe_ne_bot) hlc
    rwa [hf] at this
  -- reflection moves onto the lower-degree polynomial
  have hrefl (k : ℕ) (hk : k < n) : ∫ t, ((p n).comp (-X)).eval t * (p k).eval t ∂μ = 0 := by
    have hmap : ∫ t, (p n).eval t * ((p k).comp (-X)).eval t ∂(Measure.map (fun x : ℝ => -x) μ) =
        ∫ t, (p n).eval (-t) * ((p k).comp (-X)).eval (-t) ∂μ :=
      integral_map (by fun_prop) (by fun_prop : Continuous _).aestronglyMeasurable
    rw [hμ] at hmap
    have hdk : ((p k).comp (-X)).degree < n := by
      rw [degree_comp_neg_X, degree_eq_natDegree (h.ne_zero k), h.1 k]; exact_mod_cast hk
    have h0 := h.integral_mul_eq_zero_of_degree_lt hdk
    simp only [eval_comp, eval_neg, eval_X, neg_neg] at hmap
    rw [show (∫ t, ((p n).comp (-X)).eval t * (p k).eval t ∂μ) =
        ∫ t, (p n).eval (-t) * (p k).eval t ∂μ by simp [eval_comp]]
    rw [← hmap]
    rw [← h0]
    congr 1; ext t; simp only [eval_comp, eval_neg, eval_X]; ring
  have hcoord (k : ℕ) (hk : k < n) : h.basis.repr r k = 0 := by
    have hint := h.integral_mul r k
    have hsplit : ∫ t, r.eval t * (p k).eval t ∂μ =
        ∫ t, ((p n).comp (-X)).eval t * (p k).eval t ∂μ -
          (-1 : ℝ) ^ n * ∫ t, (p n).eval t * (p k).eval t ∂μ := by
      rw [← integral_const_mul, ← integral_sub (h.integrable_mul _ _)
        ((h.integrable_mul _ _).const_mul _)]
      congr 1; ext t; simp only [hr_def, eval_sub, eval_mul, eval_C]; ring
    rw [hsplit, hrefl k hk, h.2.2.2 n k (by omega), mul_zero, sub_zero] at hint
    exact (mul_eq_zero.mp hint.symm).resolve_right (ne_of_gt (h.2.2.1 k))
  have hr0 : r = 0 := by
    rw [h.expansion hdeg]
    exact Finset.sum_eq_zero fun k hk => by rw [hcoord k (Finset.mem_range.mp hk), zero_smul]
  have := congrArg (fun q : ℝ[X] => q.eval x) hr0
  simp only [hr_def, eval_sub, eval_comp, eval_neg, eval_X, eval_mul, eval_C, eval_zero] at this
  linarith


@[dlmf 18.2.E6]
def firstWeightedSquaredNorm (μ : Measure ℝ) (p : ℕ → ℝ[X]) (n : ℕ) : ℝ :=
  ∫ x, x * (p n).eval x ^ 2 ∂μ

@[dlmf 18.2.E28]
def shiftedHankelDeterminant (μ : Measure ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    Matrix.det (fun i j : Fin n => moment μ (i.val + if j.val + 1 = n then n else j.val))

@[dlmf 18.2.E41]
def poissonKernel (μ : Measure ℝ) (p : ℕ → ℝ[X]) (z x y : ℝ) : ℝ :=
  ∑' n : ℕ, (p n).eval x * (p n).eval y / squaredNorm μ p n * z ^ n

/-- The Szegő integrability condition on `(-1,1)`, with positivity stated
explicitly so that totalized `Real.log 0` cannot mask a zero weight. -/
@[dlmf 18.2.E39]
def IsSzegoWeight (w : ℝ → ℝ) : Prop :=
  (∀ᵐ x ∂(volume.restrict (Set.Ioo (-1 : ℝ) 1)), 0 < w x) ∧
  Integrable (fun x => |Real.log (w x)| / Real.sqrt (1 - x ^ 2))
    (volume.restrict (Set.Ioo (-1 : ℝ) 1))

@[dlmf 18.2.E40]
def IsNevaiClass (a b : ℝ) (α β : ℕ → ℝ) : Prop :=
  Tendsto (fun n => Real.sqrt (β n)) atTop (𝓝 (a / 2)) ∧ Tendsto α atTop (𝓝 b)

@[dlmf 18.2.E12_5]
theorem kernel_annihilates {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    {f : ℝ → ℝ} (hf : MemLp f 2 μ) (n : ℕ) (horth : ∀ k ≤ n, ∫ y, f y * (p k).eval y ∂μ = 0) (x : ℝ) :
    ∫ y, f y * christoffelDarbouxKernel μ p n x y ∂μ = 0 := by
  rw [integral_mul_kernel h hf]
  apply Finset.sum_eq_zero
  intro k hk
  rw [horth k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)), mul_zero]

@[dlmf 18.2.E15]
theorem kernel_polynomials_orthogonal {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    {a b y : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) (hy : y < a ∨ b < y) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x, christoffelDarbouxKernel μ p n x y * christoffelDarbouxKernel μ p m x y * |y - x| ∂μ = 0 := by
  classical
  let K (j : ℕ) : ℝ[X] := ∑ k ∈ Finset.range (j + 1),
    C ((p k).eval y / squaredNorm μ p k) * p k
  have hK (j : ℕ) (x : ℝ) : (K j).eval x = christoffelDarbouxKernel μ p j x y := by
    simp only [K, eval_finsetSum, Polynomial.eval_mul, eval_C, christoffelDarbouxKernel]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hsigned (i j : ℕ) (hij : i < j) :
      ∫ x, christoffelDarbouxKernel μ p j x y *
        christoffelDarbouxKernel μ p i x y * (y - x) ∂μ = 0 := by
    let A : ℝ := (p j).leadingCoeff / ((p (j + 1)).leadingCoeff * squaredNorm μ p j)
    have hp : (X - C y) * K j = C A *
        (C ((p j).eval y) * p (j + 1) - C ((p (j + 1)).eval y) * p j) := by
      apply Polynomial.funext
      intro x
      simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, eval_C, hK]
      by_cases hxy : x = y
      · subst x; ring
      · have hc := christoffel_darboux h (n := j + 1) (by omega) hxy
        simp only [Nat.add_sub_cancel] at hc
        dsimp [A]
        unfold christoffelDarbouxKernel squaredNorm
        rw [hc]
        field_simp [sub_ne_zero.mpr hxy]
    have horth (k : ℕ) (hk : k ≤ i) :
        ∫ x, (((X - C y) * K j).eval x) * (p k).eval x ∂μ = 0 := by
      rw [hp]
      simp only [Polynomial.eval_mul, eval_sub, eval_C, sub_mul, mul_assoc]
      rw [integral_const_mul, integral_sub
        ((h.integrable_mul (p (j + 1)) (p k)).const_mul _)
        ((h.integrable_mul (p j) (p k)).const_mul _),
        integral_const_mul, integral_const_mul,
        h.2.2.2 (j + 1) k (by omega), h.2.2.2 j k (by omega)]
      ring
    have he := kernel_annihilates h (h.memLp_eval ((X - C y) * K j)) i horth y
    have hswap (x : ℝ) : christoffelDarbouxKernel μ p i y x =
        christoffelDarbouxKernel μ p i x y := by
      simp only [christoffelDarbouxKernel, mul_comm]
    simp_rw [eval_mul, eval_sub, eval_X, eval_C, hK, hswap] at he
    calc
      _ = -(∫ x, (x - y) * christoffelDarbouxKernel μ p j x y *
          christoffelDarbouxKernel μ p i x y ∂μ) := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = 0 := by rw [he, neg_zero]
  have hs : ∫ x, christoffelDarbouxKernel μ p n x y *
      christoffelDarbouxKernel μ p m x y * (y - x) ∂μ = 0 := by
    rcases lt_or_gt_of_ne hmn with hlt | hgt
    · exact hsigned m n hlt
    · convert hsigned n m hgt using 1
      congr 1
      funext x
      ring
  rcases hy with hy | hy
  · calc
      _ = -(∫ x, christoffelDarbouxKernel μ p n x y *
          christoffelDarbouxKernel μ p m x y * (y - x) ∂μ) := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards [ae_iff.mpr hsupp] with x hx
        rw [abs_of_neg (by linarith [hx.1])]
        ring
      _ = 0 := by rw [hs, neg_zero]
  · calc
      _ = ∫ x, christoffelDarbouxKernel μ p n x y *
          christoffelDarbouxKernel μ p m x y * (y - x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_iff.mpr hsupp] with x hx
        rw [abs_of_pos (by linarith [hx.2])]
      _ = 0 := hs

@[dlmf 18.2.E29]
theorem monic_moment_determinant {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    (hmonic : ∀ n, (p n).Monic) (n : ℕ) (x : ℝ) :
    (p n).eval x = Matrix.det (fun i j : Fin (n + 1) =>
      if i.val = n then x ^ j.val else moment μ (i.val + j.val)) / hankelDeterminant μ n := by
  sorry

@[dlmf 18.2.E30]
theorem monic_diagonal_moment_determinant {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    (hmonic : ∀ n, (p n).Monic) (n : ℕ) :
    recurrenceDiagonal h n = shiftedHankelDeterminant μ (n + 1) / hankelDeterminant μ (n + 1) -
      shiftedHankelDeterminant μ n / hankelDeterminant μ n := by
  sorry

@[dlmf 18.2.E30]
theorem monic_offdiagonal_moment_determinant {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    (hmonic : ∀ n, (p n).Monic) (n : ℕ) :
    h.basis.repr (X * p (n + 1)) n =
      hankelDeterminant μ (n + 2) * hankelDeterminant μ n / hankelDeterminant μ (n + 1) ^ 2 := by
  sorry

@[dlmf 18.2.E25]
theorem compact_support_L2_expansion {μ : Measure ℝ} {p : ℕ → ℝ[X]} (h : IsOrthogonalPolynomials μ p)
    {a b : ℝ} (hsupp : μ (Set.Icc a b)ᶜ = 0) {f : ℝ → ℝ} (hf : MemLp f 2 μ) :
    Tendsto (fun N : ℕ => ∫ x, (f x - ∑ n ∈ Finset.range N,
      ((∫ t, f t * (p n).eval t ∂μ) / squaredNorm μ p n) * (p n).eval x) ^ 2 ∂μ) atTop (𝓝 0) := by
  classical
  have hfinite : IsFiniteMeasure μ := by
    have hi := h.integrable_mul (1 : ℝ[X]) 1
    exact (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
      (by simpa using hi)
  let := hfinite
  have hexp : ∃ r : ℝ, 0 < r ∧ Integrable (fun x : ℝ => Real.exp (r * |x|)) μ := by
    refine ⟨1, one_pos, ?_⟩
    have hi := (show Continuous (fun x : ℝ => Real.exp (1 * |x|)) by fun_prop).continuousOn.integrableOn_compact
      (μ := μ) (isCompact_Icc (a := a) (b := b))
    simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hsupp)] using hi
  let c : ℕ → ℝ := fun n => ∫ x, (p n).eval x ^ 2 ∂μ
  have hc : ∀ n, 0 < c n := h.2.2.1
  have hmem : ∀ n, MemLp (fun x => (algebraMap ℝ ℝ) ((p n).eval x / Real.sqrt (c n))) 2
      (μ.withDensity (fun _ => ENNReal.ofReal (1 : ℝ))) := by
    intro n
    simpa [div_eq_mul_inv] using (h.memLp_eval (p n)).mul_const (Real.sqrt (c n))⁻¹
  -- Reuse the Tau Ceti contributors' polynomial completeness and basis APIs.
  have hcomplete := TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot (𝕜 := ℝ)
    p (fun _ => 1) c (fun n => (degree_eq_natDegree (h.ne_zero n)).trans (by rw [h.1 n]))
    hc (by simpa using hexp) hmem
  have horth : ∀ m n, (∫ x, (p m).eval x * (p n).eval x * 1 ∂μ) =
      if m = n then c n else 0 := by
    intro m n
    by_cases hmn : m = n
    · subst m; simp [c, pow_two]
    · simpa [hmn] using h.2.2.2 m n hmn
  let B := TauCeti.hilbertBasisOfOrthogonalSystem (𝕜 := ℝ) (fun n x => (p n).eval x)
    (fun _ => 1) c (Filter.Eventually.of_forall fun _ => one_pos)
    aemeasurable_const hc horth hmem hcomplete
  have hB (n : ℕ) : ⇑(B n) =ᵐ[μ] fun x => (p n).eval x / Real.sqrt (c n) := by
    simpa [B] using TauCeti.coeFn_hilbertBasisOfOrthogonalSystem (𝕜 := ℝ)
      (fun n x => (p n).eval x) (fun _ => 1) c
      (Filter.Eventually.of_forall fun _ => one_pos) aemeasurable_const hc horth hmem hcomplete n
  have hinner (n : ℕ) : inner ℝ (hf.toLp f) (B n) =
      (∫ x, f x * (p n).eval x ∂μ) / Real.sqrt (c n) := by
    rw [L2.inner_def, ← MeasureTheory.integral_div]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hB n] with x hx hb
    simp [hx, hb, mul_div_assoc, mul_comm]
  let v := hf.toLp f
  let S (N : ℕ) := ∑ n ∈ Finset.range N, B.repr v n • B n
  have hrepr (n : ℕ) : B.repr v n =
      (∫ x, f x * (p n).eval x ∂μ) / Real.sqrt (c n) := by
    rw [B.repr_apply_apply, real_inner_comm]
    exact hinner n
  have hS (N : ℕ) : ⇑(S N) =ᵐ[μ] fun x => ∑ n ∈ Finset.range N,
      ((∫ t, f t * (p n).eval t ∂μ) / c n) * (p n).eval x := by
    have hsmul (n : ℕ) : ⇑(B.repr v n • B n) =ᵐ[μ] fun x =>
        ((∫ t, f t * (p n).eval t ∂μ) / c n) * (p n).eval x := by
      filter_upwards [Lp.coeFn_smul (B.repr v n) (B n), hB n] with x hx hb
      rw [hx, Pi.smul_apply, smul_eq_mul, hb, hrepr]
      field_simp [ne_of_gt (Real.sqrt_pos.mpr (hc n)), ne_of_gt (hc n)]
      rw [Real.sq_sqrt (hc n).le]
      ring
    filter_upwards [Lp.coeFn_finsetSum (Finset.range N) (fun n => B.repr v n • B n),
      ae_all_iff.mpr hsmul] with x hx hn
    rw [hx]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun n _ => hn n)
  have he (N : ℕ) : ∫ x, (f x - ∑ n ∈ Finset.range N,
      ((∫ t, f t * (p n).eval t ∂μ) / squaredNorm μ p n) * (p n).eval x) ^ 2 ∂μ =
        ‖v - S N‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub v (S N), hf.coeFn_toLp, hS N] with x hx hv hs
    change (f x - ∑ n ∈ Finset.range N,
      ((∫ t, f t * (p n).eval t ∂μ) / c n) * (p n).eval x) ^ 2 =
      (v - S N) x * (v - S N) x
    rw [hx]
    simp only [Pi.sub_apply]
    rw [show v x = f x from hv, hs, pow_two]
  simp_rw [he]
  have ht := ((tendsto_const_nhds (x := v)).sub (B.hasSum_repr v).tendsto_sum_nat).norm.pow 2
  simpa [S] using ht


end AAR.OrthogonalPolynomials
