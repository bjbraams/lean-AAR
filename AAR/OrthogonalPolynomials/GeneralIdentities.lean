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

Statements from NIST DLMF Chapter 18. See `DLMFCoverage.md` for the source inventory.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
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
  sorry

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
  sorry


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
  sorry

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
  sorry


end AAR.OrthogonalPolynomials
