/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Airy.Framework
public import DLMF.Airy.Equation
public import DLMF.Airy.Relations
public import ToMathlib.Analysis.Asymptotics.WatsonRotated
public import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Airy asymptotic expansions and error bounds, DLMF §9.7

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF.Confluent
open scoped Real Topology Interval
namespace DLMF.Airy

/-- Airy expansion coefficient u_k, including u_0=1. -/
def airyU (k : ℕ) : ℝ :=
  (ascPochhammer ℝ k).eval (1 / 6) * (ascPochhammer ℝ k).eval (5 / 6) /
    (2 ^ k * k.factorial)
/-- Airy derivative expansion coefficient v_k, including v_0=1. -/
def airyV (k : ℕ) : ℝ := (6 * (k : ℝ) + 1) / (1 - 6 * (k : ℝ)) * airyU k
/-- The Gamma-ratio error multiplier χ. -/
@[dlmf 9.7.E3]
def airyChi (x : ℝ) : ℝ := Real.sqrt π * Real.Gamma (x / 2 + 1) / Real.Gamma (x / 2 + 1 / 2)
/-- Which of the four Airy functions is expanded. -/
inductive AiryKind where
  | ai | aiDeriv | bi | biDeriv
  deriving DecidableEq
/-- The function selected by an Airy expansion index. -/
def airyFunction : AiryKind → ℂ → ℂ
  | .ai => airyAi | .aiDeriv => airyAiDeriv | .bi => airyBi | .biDeriv => airyBiDeriv
/-- The exponential prefactor in DLMF 9.7.5–9.7.8. -/
def airyPrefactor (kind : AiryKind) (z : ℂ) : ℂ :=
  match kind with
  | .ai => exp (-airyZetaComplex z) / (2 * Real.sqrt π * z ^ (1 / 4 : ℂ))
  | .aiDeriv => -z ^ (1 / 4 : ℂ) * exp (-airyZetaComplex z) / (2 * Real.sqrt π)
  | .bi => exp (airyZetaComplex z) / (Real.sqrt π * z ^ (1 / 4 : ℂ))
  | .biDeriv => z ^ (1 / 4 : ℂ) * exp (airyZetaComplex z) / Real.sqrt π
/-- Signed coefficients in the exponential Airy expansions. -/
def airyExpansionCoeff (kind : AiryKind) (k : ℕ) : ℂ :=
  match kind with
  | .ai => (-1 : ℂ) ^ k * airyU k
  | .aiDeriv => (-1 : ℂ) ^ k * airyV k
  | .bi => airyU k
  | .biDeriv => airyV k
/-- A finite, normalized exponential Airy expansion. -/
def airyExponentialSum (kind : AiryKind) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, airyExpansionCoeff kind k / airyZetaComplex z ^ k
/-- The exact normalized remainder, not an arbitrarily chosen error function. -/
def airyRemainder (kind : AiryKind) (N : ℕ) (z : ℂ) : ℂ :=
  airyFunction kind z / airyPrefactor kind z - airyExponentialSum kind N z
/-- Even or odd subseries in an oscillatory expansion. -/
def airyOscSum (derivative : Bool) (parity N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k *
    (if derivative then airyV (2 * k + parity) else airyU (2 * k + parity)) /
      airyZetaComplex z ^ (2 * k + parity)
/-- The algebraic prefactor of a negative-axis expansion. -/
def airyOscPrefactor (kind : AiryKind) (z : ℂ) : ℂ :=
  match kind with
  | .ai | .bi => 1 / (Real.sqrt π * z ^ (1 / 4 : ℂ))
  | .aiDeriv | .biDeriv => z ^ (1 / 4 : ℂ) / Real.sqrt π
/-- The two separately truncated oscillatory series, with the stated sine/cosine signs. -/
def airyOscApprox (kind : AiryKind) (N M : ℕ) (z : ℂ) : ℂ :=
  let θ := airyZetaComplex z - π / 4
  airyOscPrefactor kind z * match kind with
    | .ai => cos θ * airyOscSum false 0 N z + sin θ * airyOscSum false 1 M z
    | .aiDeriv => sin θ * airyOscSum true 0 N z - cos θ * airyOscSum true 1 M z
    | .bi => -sin θ * airyOscSum false 0 N z + cos θ * airyOscSum false 1 M z
    | .biDeriv => cos θ * airyOscSum true 0 N z + sin θ * airyOscSum true 1 M z
/-- A positive error envelope; it does not divide by an oscillatory leading term. -/
def airyOscError (kind : AiryKind) (N M : ℕ) (z : ℂ) : ℝ :=
  ‖airyOscPrefactor kind z‖ * Real.exp |(airyZetaComplex z).im| *
    (‖airyZetaComplex z‖ ^ (-(2 * N : ℤ)) + ‖airyZetaComplex z‖ ^ (-(2 * M + 1 : ℤ)))
/-- Rotated Bi approximations on their two Stokes rays. -/
def airyRotatedBiApprox (derivative : Bool) (ε : ℝ) (N M : ℕ) (z : ℂ) : ℂ :=
  let θ := airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2
  if derivative then
    (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ) *
      (-sin θ * airyOscSum true 0 N z + cos θ * airyOscSum true 1 M z)
  else
    (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ) *
      (cos θ * airyOscSum false 0 N z + sin θ * airyOscSum false 1 M z)
/-- The piecewise complex error multiplier in 9.7.17; the phase of ζ is inherited from z. -/
@[dlmf 9.7.E17]
def airyErrorMultiplier (n : ℕ) (σ : ℝ) (z : ℂ) : ℝ :=
  if |arg z| ≤ π / 3 then 1 else
  if |arg z| ≤ 2 * π / 3 then min |(Real.sin (3 * arg z / 2))⁻¹| (airyChi (n + σ) + 1) else
    Real.sqrt (2 * π * (n + σ)) / |Real.cos (3 * arg z / 2)| ^ ((n : ℝ) + σ) + airyChi (n + σ) + 1
/-- The terminant, with an explicit logarithmic argument to retain the Gamma branch. -/
@[dlmf 9.7.E22]
def airyTerminator (p w : ℂ) : ℂ := exp (exp w) / (2 * π) * Gamma p * airyUpperGammaOnLog (1 - p) w
/-- The near-optimal exponential truncation index. -/
def airyOptimalIndex (z : ℂ) : ℕ := ⌊2 * ‖airyZetaComplex z‖⌋₊
/-- Exact second-level remainder after re-expanding the normalized Ai remainder. -/
def airyHyperRemainder (derivative : Bool) (m n : ℕ) (z : ℂ) : ℂ :=
  airyRemainder (if derivative then .aiDeriv else .ai) n z -
    (-1 : ℂ) ^ (if derivative then n - 1 else n) *
      ∑ k ∈ Finset.range m, (-1 : ℂ) ^ k * (if derivative then airyV k else airyU k) *
        airyTerminator ((n : ℂ) - k) (log 2 + airyLogZeta z) / airyZetaComplex z ^ k

/-- The recurrence for `u_k`, cleared of denominators and cast to `ℂ`. -/
lemma airyU_succ_mul (k : ℕ) :
    (airyU (k + 1) : ℂ) * ((2 * k + 1) * 216 * (k + 1)) =
      (6 * k + 1) * (6 * k + 3) * (6 * k + 5) * airyU k := by
  have h' : airyU (k + 1) * ((2 * k + 1) * 216 * (k + 1)) =
      (6 * k + 1) * (6 * k + 3) * (6 * k + 5) * airyU k := by
    simp only [airyU, ascPochhammer_succ_eval, pow_succ, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hp : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  exact_mod_cast h'

/-- `u_k · 216^k k! · ∏_{j<k}(2j+1) = ∏_{j<3k}(2j+1)`. -/
lemma airyU_mul_oddProd (k : ℕ) :
    (airyU k : ℂ) * ((216 : ℂ) ^ k * k.factorial) * ∏ j ∈ Finset.range k, (2 * (j : ℂ) + 1) =
      ∏ j ∈ Finset.range (3 * k), (2 * (j : ℂ) + 1) := by
  induction k with
  | zero => simp [airyU]
  | succ k ih =>
    rw [show 3 * (k + 1) = 3 * k + 1 + 1 + 1 by ring, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, ← ih,
      Nat.factorial_succ]
    push_cast
    linear_combination (216 ^ k * (k.factorial : ℂ) * ∏ j ∈ Finset.range k, (2 * (j : ℂ) + 1)) *
      airyU_succ_mul k

/-- airyU product (DLMF 9.7.2). -/
@[dlmf 9.7.E2]
theorem airyU_product (k : ℕ) :
    (airyU k : ℂ) = (∏ j ∈ Finset.range (2 * k), (2 * (k : ℂ) + 1 + 2 * j)) /
      ((216 : ℂ) ^ k * k.factorial) := by
  have h := airyU_mul_oddProd k
  rw [show 3 * k = k + 2 * k by ring, Finset.prod_range_add] at h
  have hQ : ∏ j ∈ Finset.range k, (2 * (j : ℂ) + 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => by norm_cast
  have hD : (216 : ℂ) ^ k * k.factorial ≠ 0 := by
    have : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) this
  rw [eq_div_iff hD]
  apply mul_right_cancel₀ hQ
  rw [h, mul_comm (∏ j ∈ Finset.range k, _)]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  push_cast; ring

/-- airyU recurrence (DLMF 9.7.2). -/
@[dlmf 9.7.E2]
theorem airyU_recurrence (k : ℕ) :
    airyU (k + 1) = ((6 * (k : ℝ) + 1) * (6 * k + 3) * (6 * k + 5)) /
      ((2 * k + 1) * 216 * (k + 1)) * airyU k := by
  simp only [airyU, ascPochhammer_succ_eval, pow_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hp : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have h2k : 2 * (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- airyChi isEquivalent (DLMF 9.7.4). -/
@[dlmf 9.7.E4]
theorem airyChi_isEquivalent  :
    (fun x : ℝ => airyChi x) ~[atTop] (fun x => Real.sqrt (π * x / 2)) := by
  have h := (DLMF.Gamma.Gamma_ratio_power (a := 1) (b := 1 / 2)).comp
    (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have h' := (Complex.continuous_re.tendsto _).comp h
  simp only [Complex.one_re] at h'
  refine isEquivalent_of_tendsto_one ?_
  apply h'.congr'
  filter_upwards [eventually_gt_atTop 0] with x hx
  have hx2 : (0 : ℝ) ≤ x / 2 := by positivity
  simp only [Function.comp_apply, id]
  have e1 : ((x / 2 : ℝ) : ℂ) + 1 = ((x / 2 + 1 : ℝ) : ℂ) := by push_cast; ring
  have e2 : ((x / 2 : ℝ) : ℂ) + 1 / 2 = ((x / 2 + 1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have e3 : ((x / 2 : ℝ) : ℂ) ^ ((1 : ℂ) - 1 / 2) = ((Real.sqrt (x / 2) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hx2]; norm_num
  rw [e1, e2, e3, Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div,
    ← Complex.ofReal_div, Complex.ofReal_re]
  simp only [Pi.div_apply]
  rw [airyChi,
    show π * x / 2 = π * (x / 2) by ring, Real.sqrt_mul Real.pi_pos.le]
  have hs : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

/-! ### Rotated Laplace integrals and the exponential expansions (DLMF 9.7.5–9.7.14)

The principal-branch Kummer `U` representation gives the expansion of `Ai` only for
`|arg z| < 2π/3`. To reach the full sector `|arg z| ≤ π - δ` we use the Laplace integrals of
`t^{a-1}(1+t)^β` along rotated rays `arg t = θ`, `θ ∈ (-π, π)`, identify them with `Ai` by the
identity theorem, and glue finitely many sectors. The expansions of `Bi`, `Bi'` and the
oscillatory and Stokes-ray expansions then follow from the connection formulas.
-/

/-- The kernel `t^{a-1} (1+t)^β` of the rotated Laplace integrals for the Airy functions. -/
def airyRot_kernel (a β : ℝ) (t : ℂ) : ℂ := t ^ ((a : ℂ) - 1) * (1 + t) ^ (β : ℂ)

/-- The Laplace transform of the kernel along the ray `arg t = θ`, in the rotated variable. -/
def airyRot_lap (a β θ : ℝ) (W : ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), Complex.exp (-(W * r)) • airyRot_kernel a β (r * exp (θ * I))

lemma airyRot_norm_ofReal_mul_exp {r : ℝ} (hr : 0 ≤ r) (u : ℝ) :
    ‖(r : ℂ) * exp (u * I)‖ = r := by
  rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

lemma airyRot_ofReal_mul_exp_ne_zero {r : ℝ} (hr : 0 < r) (u : ℝ) :
    (r : ℂ) * exp (u * I) ≠ 0 :=
  mul_ne_zero (ofReal_ne_zero.mpr hr.ne') (exp_ne_zero _)

/-- `arg (r e^{iu}) = u` for `r > 0`, `u ∈ (-π, π]`. -/
lemma airyRot_arg {r : ℝ} (hr : 0 < r) {u : ℝ} (h1 : -π < u) (h2 : u ≤ π) :
    arg ((r : ℂ) * exp (u * I)) = u := by
  rw [exp_mul_I]
  exact arg_mul_cos_add_sin_mul_I hr ⟨h1, h2⟩

/-- `r e^{iu}` lies in the slit plane for `r > 0`, `|u| < π`. -/
lemma airyRot_mem_slitPlane {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : |u| < π) :
    (r : ℂ) * exp (u * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff_arg]
  refine ⟨?_, airyRot_ofReal_mul_exp_ne_zero hr u⟩
  rw [airyRot_arg hr (by linarith [neg_abs_le u]) (by linarith [le_abs_self u])]
  exact (by linarith [le_abs_self u] : u < π).ne

/-- `1 + r e^{iu}` lies in the slit plane for `r ≥ 0`, `|u| < π`. -/
lemma airyRot_one_add_mem_slitPlane {r : ℝ} (hr : 0 ≤ r) {u : ℝ} (hu : |u| < π) :
    1 + (r : ℂ) * exp (u * I) ∈ slitPlane := by
  rcases eq_or_lt_of_le hr with h | h
  · subst h; simp
  by_cases hs : Real.sin u = 0
  · have hu0 : u = 0 := by
      rcases Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le u]) (by linarith [le_abs_self u]) |>.mp hs with h'
      exact h'
    subst hu0
    left
    simp; linarith
  · right
    simp [exp_ofReal_mul_I_im] at *
    exact ⟨h.ne', hs⟩

/-- The kernel is holomorphic at `r e^{iu}`, `r > 0`, `|u| < π`. -/
lemma airyRot_differentiableAt_kernel (a β : ℝ) {r : ℝ} (hr : 0 < r) {u : ℝ} (hu : |u| < π) :
    DifferentiableAt ℂ (airyRot_kernel a β) ((r : ℂ) * exp (u * I)) := by
  unfold airyRot_kernel
  exact (differentiableAt_id.cpow (differentiableAt_const _) (airyRot_mem_slitPlane hr hu)).mul
    ((differentiableAt_const _ |>.add differentiableAt_id).cpow (differentiableAt_const _)
      (airyRot_one_add_mem_slitPlane hr.le hu))

/-- The kernel along a ray is continuous on `(0, ∞)`. -/
lemma airyRot_continuousOn_kernel (a β : ℝ) {θ : ℝ} (hθ : |θ| < π) :
    ContinuousOn (fun r : ℝ => airyRot_kernel a β ((r : ℂ) * exp (θ * I))) (Ioi 0) :=
  fun r hr => (ContinuousAt.comp (g := airyRot_kernel a β) (f := fun r : ℝ => (r : ℂ) * exp (θ * I))
    (airyRot_differentiableAt_kernel a β hr hθ).continuousAt
    (by fun_prop : Continuous fun r : ℝ => (r : ℂ) * exp (θ * I)).continuousAt).continuousWithinAt

/-- Uniform bound for the kernel on a closed sector `|u| ≤ Φ < π`. -/
lemma airyRot_kernel_bound (a β : ℝ) {Φ : ℝ} (hΦ : Φ < π) :
    ∃ C > 0, ∀ r : ℝ, 0 < r → ∀ u : ℝ, |u| ≤ Φ →
      ‖airyRot_kernel a β (r * exp (u * I))‖ ≤ C * (r ^ (a - 1) * (1 + r) ^ |β|) := by
  obtain ⟨c, hc, hcle⟩ := Complex.exists_pos_le_norm_one_add_ofReal_mul_exp hΦ
  have hc' : 0 < min c 1 := lt_min hc one_pos
  refine ⟨(min c 1) ^ (-|β|), by positivity, fun r hr u hu => ?_⟩
  have hc'1 : min c 1 ≤ 1 := min_le_right _ _
  have h1 : min c 1 ≤ ‖1 + (r : ℂ) * exp (u * I)‖ := (min_le_left _ _).trans (hcle r hr.le u hu)
  have h2 : ‖1 + (r : ℂ) * exp (u * I)‖ ≤ 1 + r := by
    refine (norm_add_le _ _).trans ?_; rw [norm_one, airyRot_norm_ofReal_mul_exp hr.le]
  rw [airyRot_kernel, norm_mul, show ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) by push_cast; ring,
    norm_cpow_real, norm_cpow_real, airyRot_norm_ofReal_mul_exp hr.le]
  have hr1 : 1 ≤ 1 + r := by linarith
  have hb : ‖1 + (r : ℂ) * exp (u * I)‖ ^ β ≤ (min c 1) ^ (-|β|) * (1 + r) ^ |β| := by
    rcases le_total 0 β with hβ | hβ
    · rw [abs_of_nonneg hβ]
      calc ‖1 + (r : ℂ) * exp (u * I)‖ ^ β ≤ (1 + r) ^ β :=
            Real.rpow_le_rpow (norm_nonneg _) h2 hβ
        _ ≤ (min c 1) ^ (-β) * (1 + r) ^ β := by
            refine le_mul_of_one_le_left (by positivity) ?_
            exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hc' hc'1 (by linarith)
    · rw [abs_of_nonpos hβ, neg_neg]
      calc ‖1 + (r : ℂ) * exp (u * I)‖ ^ β ≤ (min c 1) ^ β :=
            Real.rpow_le_rpow_of_nonpos hc' h1 hβ
        _ ≤ (min c 1) ^ β * (1 + r) ^ (-β) := by
            refine le_mul_of_one_le_right (by positivity) ?_
            exact Real.one_le_rpow hr1 (by linarith)
  have hra := Real.rpow_nonneg hr.le (a - 1)
  calc r ^ (a - 1) * ‖1 + (r : ℂ) * exp (u * I)‖ ^ β
      ≤ r ^ (a - 1) * ((min c 1) ^ (-|β|) * (1 + r) ^ |β|) := by gcongr
    _ = _ := by ring

/-- The damped kernel along a ray is integrable on `(0, ∞)`. -/
lemma airyRot_integrableOn (a β : ℝ) (ha : 0 < a) {θ : ℝ} (hθ : |θ| < π) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) • airyRot_kernel a β ((r : ℂ) * exp (θ * I)))
      (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := airyRot_kernel_bound a β (Φ := |θ|) hθ
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |β| ≤ N := ⟨⌈|β|⌉₊, Nat.le_ceil _⟩
  refine Integrable.mono' ((integrableOn_exp_mul_rpow_mul_one_add_pow (s := a - 1) (by linarith)
    hc N).const_mul C) ?_ ?_
  · exact (((by fun_prop : Continuous fun r : ℝ => Real.exp (-c * r)).continuousOn).smul
      (airyRot_continuousOn_kernel a β hθ)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr : (0 : ℝ) < r := hr
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp]
    have h1 := hb r hr θ le_rfl
    have h2 : (1 + r) ^ |β| ≤ (1 + r) ^ (N : ℕ) := by
      rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hN
    have hra := Real.rpow_nonneg hr.le (a - 1)
    calc Real.exp (-c * r) * ‖airyRot_kernel a β ((r : ℂ) * exp (θ * I))‖
        ≤ Real.exp (-c * r) * (C * (r ^ (a - 1) * (1 + r) ^ |β|)) := by gcongr
      _ ≤ Real.exp (-c * r) * (C * (r ^ (a - 1) * (1 + r) ^ N)) := by gcongr
      _ = C * (Real.exp (-c * r) * r ^ (a - 1) * (1 + r) ^ N) := by ring

/-- The rotated Laplace transform is holomorphic on the right half-plane. -/
lemma airyRot_differentiableOn_lap (a β : ℝ) (ha : 0 < a) {θ : ℝ} (hθ : |θ| < π) :
    DifferentiableOn ℂ (airyRot_lap a β θ) {W : ℂ | 0 < W.re} := by
  intro W hW
  have hW : 0 < W.re := hW
  have h := differentiableOn_integral_cexp_neg_mul_smul
    (airyRot_integrableOn a β ha hθ (half_pos hW))
  exact (h.differentiableAt ((isOpen_lt continuous_const continuous_re).mem_nhds
    (show W.re / 2 < W.re by linarith))).differentiableWithinAt

/-- Rotation of the ray of integration from `0` to `θ`, `|θ| < π`. -/
lemma airyRot_lap_rotate (a β : ℝ) (ha : 0 < a) {θ : ℝ} (hθ : |θ| < π) {w : ℂ}
    (hw : ∀ y ∈ [[0, θ]], 0 < (w * exp (y * I)).re) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(w * t)) * airyRot_kernel a β t =
      exp (θ * I) * airyRot_lap a β θ (w * exp (θ * I)) := by
  obtain ⟨C, hC, hb⟩ := airyRot_kernel_bound a β (Φ := |θ|) hθ
  have hy : ∀ y ∈ [[0, θ]], |y| ≤ |θ| := fun y hy => abs_le_abs_of_mem_uIcc_zero hy
  have h := integral_cexp_neg_mul_mul_eq_rotate (F := airyRot_kernel a β) (θ := θ) (σ := a)
    (C := C * 2 ^ |β|) (k := a - 1 + |β|) (z := w) ha ?_ ?_ ?_ hw
  · rw [h, airyRot_lap]
    rfl
  · intro r hr y hy'
    exact airyRot_differentiableAt_kernel a β hr ((hy y hy').trans_lt hθ)
  · intro r hr hr1 y hy'
    refine (hb r hr y (hy y hy')).trans ?_
    have : (1 + r) ^ |β| ≤ 2 ^ |β| :=
      Real.rpow_le_rpow (by linarith) (by linarith) (abs_nonneg _)
    have hra := Real.rpow_nonneg hr.le (a - 1)
    calc C * (r ^ (a - 1) * (1 + r) ^ |β|) ≤ C * (r ^ (a - 1) * 2 ^ |β|) := by gcongr
      _ = C * 2 ^ |β| * r ^ (a - 1) := by ring
  · intro r hr y hy'
    have hr0 : 0 < r := by linarith
    refine (hb r hr0 y (hy y hy')).trans ?_
    have h2 : (1 + r) ^ |β| ≤ (2 * r) ^ |β| :=
      Real.rpow_le_rpow (by linarith) (by linarith) (abs_nonneg _)
    rw [Real.mul_rpow (by norm_num) hr0.le] at h2
    have hra := Real.rpow_nonneg hr0.le (a - 1)
    calc C * (r ^ (a - 1) * (1 + r) ^ |β|) ≤ C * (r ^ (a - 1) * (2 ^ |β| * r ^ |β|)) := by
          gcongr
      _ = C * 2 ^ |β| * r ^ (a - 1 + |β|) := by rw [Real.rpow_add hr0]; ring

/-- **Watson's lemma** for the rotated Airy kernel, in the rotated variable. -/
lemma airyRot_hasAsymptoticExpansion (a β : ℝ) (ha : 0 < a) {θ : ℝ} (hθ : |θ| < π) {δ : ℝ}
    (hδ : 0 < δ) :
    HasAsymptoticExpansion (sectorAtTop δ) (fun (n : ℕ) (W : ℂ) => W ^ (-((n : ℂ) + a)))
      (fun n => Complex.Gamma ((n : ℂ) + a) • exp (θ * I * ((n : ℂ) + a)) •
        Ring.choose (β : ℂ) n)
      (fun W => exp (θ * I) • airyRot_lap a β θ W) := by
  have hθ1 : -π < θ := by linarith [neg_abs_le θ]
  have hθ2 : θ ≤ π := by linarith [le_abs_self θ]
  refine hasAsymptoticExpansion_integral_cexp_smul_rotate (c := 1) (μ := (a : ℂ)) hθ1 hθ2
    (by simpa using ha) hδ (airyRot_integrableOn a β ha hθ one_pos) fun N => ?_
  have hbin := one_add_mul_cpow_sub_sum_isBigO (exp (θ * I)) (β : ℂ) N
  have hpow : (fun r : ℝ => ((r : ℂ) * exp (θ * I)) ^ ((a : ℂ) - 1)) =O[𝓝[>] 0]
      fun r : ℝ => r ^ (a - 1) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    rw [show ((a : ℂ) - 1) = ((a - 1 : ℝ) : ℂ) by push_cast; ring, norm_cpow_real,
      airyRot_norm_ofReal_mul_exp hr.le, one_mul,
      Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
  refine (hpow.mul hbin).congr' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    have ht := airyRot_ofReal_mul_exp_ne_zero hr θ
    simp only [airyRot_kernel, smul_eq_mul, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show ((n : ℂ) + (a : ℂ) - 1) = ((a : ℂ) - 1) + n by ring, cpow_add _ _ ht, cpow_natCast]
    ring
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : (0 : ℝ) < r := hr
    simp only [ofReal_re]
    rw [show (N : ℝ) + a - 1 = (a - 1) + N by ring, Real.rpow_add hr, Real.rpow_natCast]

/-! ### Continuation of the Airy–Tricomi representation to rotated sectors -/

/-- `re (e^w) = e^{re w} cos (im w)`. -/
lemma airyRot_re_exp (w : ℂ) : (exp w).re = Real.exp w.re * Real.cos w.im := Complex.exp_re w

/-- `airyLogZeta` is holomorphic on the slit plane. -/
lemma airyRot_differentiableAt_logZeta {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ airyLogZeta z := by
  unfold airyLogZeta
  exact (differentiableAt_const _).add ((differentiableAt_const _).mul (differentiableAt_log hz))

/-- `ζ` is holomorphic on the slit plane. -/
lemma airyRot_differentiableAt_zeta {z : ℂ} (hz : z ∈ slitPlane) :
    DifferentiableAt ℂ airyZetaComplex z := by
  unfold airyZetaComplex
  exact (differentiableAt_const _).mul (differentiableAt_id.cpow (differentiableAt_const _) hz)

/-- `2ζ e^{iy} = exp (log 2 + L + iy)`. -/
lemma airyRot_two_zeta_mul_exp {z : ℂ} (hz : z ≠ 0) (y : ℝ) :
    2 * airyZetaComplex z * exp (y * I) = exp (log 2 + airyLogZeta z + y * I) := by
  rw [exp_add, exp_log_two_add_airyLogZeta hz]

/-- The real part of `exp (log 2 + L + iy)`. -/
lemma airyRot_re_W (z : ℂ) (y : ℝ) :
    (exp (log 2 + airyLogZeta z + y * I)).re =
      Real.exp (log 2 + airyLogZeta z).re * Real.cos (3 / 2 * arg z + y) := by
  rw [airyRot_re_exp]
  congr 2
  · simp
  · rw [add_im, im_log_two_add_airyLogZeta]
    simp

lemma airyRot_re_W_pos (z : ℂ) {y : ℝ} (hy : |3 / 2 * arg z + y| < π / 2) :
    0 < (exp (log 2 + airyLogZeta z + y * I)).re := by
  rw [airyRot_re_W]
  refine mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩) <;>
    linarith [abs_lt.mp hy]

/-- **The Airy–Tricomi representation in a rotated sector.** If an entire function `f` equals
`A e^{pL - ζ} Γ(a)⁻¹ ∫₀^∞ e^{-2ζt} t^{a-1}(1+t)^β dt` for `|arg z| < π/3`, then, for every
`|θ| < π`, it equals the rotated integral on the whole open sector `|(3/2) arg z + θ| < π/2`. -/
lemma airyRot_eq_of_anchor {f : ℂ → ℂ} (hf : Differentiable ℂ f) (A p : ℂ) (a β : ℝ)
    (ha : 0 < a)
    (hanchor : ∀ z : ℂ, z ≠ 0 → |arg z| < π / 3 → f z =
      A * exp (p * airyLogZeta z - airyZetaComplex z) * (1 / Gamma a *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(2 * airyZetaComplex z * t)) * airyRot_kernel a β t))
    {θ : ℝ} (hθ : |θ| < π) {z : ℂ} (hz : z ≠ 0) (hzθ : |3 / 2 * arg z + θ| < π / 2) :
    f z = A * exp (p * airyLogZeta z - airyZetaComplex z) *
      (1 / Gamma a * (exp (θ * I) * airyRot_lap a β θ (exp (log 2 + airyLogZeta z + θ * I)))) := by
  have hπ := Real.pi_pos
  have hθ' := abs_lt.mp hθ
  set g : ℂ → ℂ := fun z => A * exp (p * airyLogZeta z - airyZetaComplex z) *
      (1 / Gamma a * (exp (θ * I) * airyRot_lap a β θ (exp (log 2 + airyLogZeta z + θ * I))))
    with hg
  set α1 : ℝ := 2 / 3 * (-(π / 2) - θ)
  set α2 : ℝ := 2 / 3 * (π / 2 - θ)
  set U : Set ℂ := (fun q : ℝ × ℝ => (q.1 : ℂ) * exp (q.2 * I)) '' (Ioi 0 ×ˢ Ioo α1 α2) with hU
  have hUc : IsPreconnected U :=
    (isPreconnected_Ioi.prod isPreconnected_Ioo).image _ (by fun_prop : Continuous
      fun q : ℝ × ℝ => (q.1 : ℂ) * exp (q.2 * I)).continuousOn
  have hmemU : ∀ w : ℂ, w ≠ 0 → |3 / 2 * arg w + θ| < π / 2 → w ∈ U := by
    intro w hw hwθ
    refine ⟨(‖w‖, arg w), ⟨norm_pos_iff.mpr hw, ?_, ?_⟩, norm_mul_exp_arg_mul_I w⟩ <;>
      simp only [α1, α2] <;> linarith [abs_lt.mp hwθ]
  have hUsub : ∀ w ∈ U, w ∈ slitPlane ∧ |3 / 2 * arg w + θ| < π / 2 := by
    rintro w ⟨⟨r, u⟩, ⟨hr, hu1, hu2⟩, rfl⟩
    simp only [α1, α2] at hu1 hu2
    have hr' : (0 : ℝ) < r := hr
    have hu : |u| < π := abs_lt.mpr ⟨by linarith, by linarith⟩
    refine ⟨airyRot_mem_slitPlane hr' hu, ?_⟩
    simp only
    rw [airyRot_arg hr' (by linarith) (by linarith)]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  -- the open set where `g` is holomorphic
  set O : Set ℂ := slitPlane ∩ (fun w => exp (log 2 + airyLogZeta w + θ * I)) ⁻¹'
    {W : ℂ | 0 < W.re} with hO
  have hWc : ContinuousOn (fun w => exp (log 2 + airyLogZeta w + θ * I)) slitPlane := fun w hw =>
    ((((differentiableAt_const _).add (airyRot_differentiableAt_logZeta hw)).add
      (differentiableAt_const _)).cexp).continuousAt.continuousWithinAt
  have hOo : IsOpen O := hWc.isOpen_inter_preimage isOpen_slitPlane
    (isOpen_lt continuous_const continuous_re)
  have hgd : DifferentiableOn ℂ g O := by
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    have hW : DifferentiableAt ℂ (fun w => exp (log 2 + airyLogZeta w + θ * I)) w :=
      (((differentiableAt_const _).add (airyRot_differentiableAt_logZeta hw.1)).add
        (differentiableAt_const _)).cexp
    have hL := ((airyRot_differentiableOn_lap a β ha hθ).differentiableAt
      ((isOpen_lt continuous_const continuous_re).mem_nhds hw.2)).comp w hW
    exact ((differentiableAt_const _).mul (((differentiableAt_const _).mul
      (airyRot_differentiableAt_logZeta hw.1)).sub (airyRot_differentiableAt_zeta hw.1)).cexp).mul
      ((differentiableAt_const _).mul ((differentiableAt_const _).mul hL))
  have hUO : U ⊆ O := fun w hw => ⟨(hUsub w hw).1, airyRot_re_W_pos w (hUsub w hw).2⟩
  have hfa : AnalyticOnNhd ℂ f U := fun w _ => hf.analyticAt w
  have hga : AnalyticOnNhd ℂ g U := fun w hw => hgd.analyticOnNhd hOo w (hUO hw)
  -- the base point and the eventual equality
  set z0 : ℂ := ((1 : ℝ) : ℂ) * exp ((-(θ / 3) : ℝ) * I) with hz0
  have hz0U : z0 ∈ U := ⟨(1, -(θ / 3)), ⟨(one_pos : (0:ℝ) < 1), by simp only [α1]; linarith,
    by simp only [α2]; linarith⟩, rfl⟩
  have harg0 : arg z0 = -(θ / 3) := airyRot_arg one_pos (by linarith) (by linarith)
  set V : Set ℂ := slitPlane ∩ arg ⁻¹' {u : ℝ | |u| < π / 3 ∧ |3 / 2 * u + θ| < π / 2} with hV
  have hargc : ContinuousOn arg slitPlane := fun w hw => (continuousAt_arg hw).continuousWithinAt
  have hVo : IsOpen V := hargc.isOpen_inter_preimage isOpen_slitPlane
    ((isOpen_lt (continuous_abs) continuous_const).inter
      (isOpen_lt (by fun_prop : Continuous fun u : ℝ => |3 / 2 * u + θ|) continuous_const))
  have hz0V : z0 ∈ V := by
    refine ⟨(hUsub z0 hz0U).1, ?_, ?_⟩ <;> simp only [harg0] <;>
      rw [abs_lt] <;> constructor <;> linarith
  have hev : f =ᶠ[𝓝 z0] g := by
    filter_upwards [hVo.mem_nhds hz0V] with w hw
    obtain ⟨hws, hw1, hw2⟩ := hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hws
    rw [hanchor w hw0 hw1]
    simp only [hg]
    congr 2
    rw [← airyRot_two_zeta_mul_exp hw0 θ]
    refine airyRot_lap_rotate a β ha hθ fun y hy => ?_
    rw [airyRot_two_zeta_mul_exp hw0 y]
    refine airyRot_re_W_pos w ?_
    have h1 := abs_lt.mp hw1
    have h2 := abs_lt.mp hw2
    rcases le_total 0 θ with h | h
    · rw [uIcc_of_le h] at hy
      exact abs_lt.mpr ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
    · rw [uIcc_of_ge h] at hy
      exact abs_lt.mpr ⟨by linarith [hy.1, hy.2], by linarith [hy.1, hy.2]⟩
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga hUc hz0U hev (hmemU z hz hzθ)

/-- `re (2ζ) > 0` for `|arg z| < π/3`. -/
lemma airyRot_re_two_zeta_pos {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < π / 3) :
    0 < (2 * airyZetaComplex z).re := by
  have h := airyRot_re_W_pos z (y := 0) (by rw [add_zero, abs_mul]; norm_num; linarith)
  rwa [← airyRot_two_zeta_mul_exp hz 0, ofReal_zero, zero_mul, exp_zero, mul_one] at h

/-- The anchor for `Ai`: Tricomi's Laplace integral on `|arg z| < π/3`. -/
lemma airyRot_airyAi_anchor {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < π / 3) :
    airyAi z = ((3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π) *
      exp ((2 / 3) * airyLogZeta z - airyZetaComplex z) * (1 / Gamma ((5 / 6 : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(2 * airyZetaComplex z * t)) *
          airyRot_kernel (5 / 6) (-1 / 6) t) := by
  rw [airyAi_eq_kummerU hz (harg.trans (by linarith [Real.pi_pos])),
    kummerU_laplace (by norm_num) (airyRot_re_two_zeta_pos hz harg)]
  have hG : Gamma ((5 / 6 : ℝ) : ℂ) = Gamma (5 / 6) := by push_cast; ring_nf
  have hI : ∀ t : ℝ, Complex.exp (-(2 * airyZetaComplex z) * t) * (t : ℂ) ^ ((5 : ℂ) / 6 - 1) *
      (1 + (t : ℂ)) ^ ((5 : ℂ) / 3 - 5 / 6 - 1) = Complex.exp (-(2 * airyZetaComplex z * t)) *
        airyRot_kernel (5 / 6) (-1 / 6) t := by
    intro t
    simp only [airyRot_kernel]
    rw [show (((5 / 6 : ℝ) : ℂ) - 1) = 5 / 6 - 1 by push_cast; ring,
      show (((-1 / 6 : ℝ)) : ℂ) = 5 / 3 - 5 / 6 - 1 by push_cast; ring]
    ring_nf
  simp_rw [hI, hG]

/-- The anchor for `Ai'`: Tricomi's Laplace integral on `|arg z| < π/3`. -/
lemma airyRot_airyAiDeriv_anchor {z : ℂ} (hz : z ≠ 0) (harg : |arg z| < π / 3) :
    airyAiDeriv z = (-((3 : ℂ) ^ (1 / 6 : ℂ) / Real.sqrt π)) *
      exp ((4 / 3) * airyLogZeta z - airyZetaComplex z) * (1 / Gamma ((7 / 6 : ℝ) : ℂ) *
        ∫ t in Ioi (0 : ℝ), Complex.exp (-(2 * airyZetaComplex z * t)) *
          airyRot_kernel (7 / 6) (1 / 6) t) := by
  rw [airyAiDeriv_eq_kummerU hz (harg.trans (by linarith [Real.pi_pos])),
    kummerU_laplace (by norm_num) (airyRot_re_two_zeta_pos hz harg)]
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) = Gamma (7 / 6) := by push_cast; ring_nf
  have hI : ∀ t : ℝ, Complex.exp (-(2 * airyZetaComplex z) * t) * (t : ℂ) ^ ((7 : ℂ) / 6 - 1) *
      (1 + (t : ℂ)) ^ ((7 : ℂ) / 3 - 7 / 6 - 1) = Complex.exp (-(2 * airyZetaComplex z * t)) *
        airyRot_kernel (7 / 6) (1 / 6) t := by
    intro t
    simp only [airyRot_kernel]
    rw [show (((7 / 6 : ℝ) : ℂ) - 1) = 7 / 6 - 1 by push_cast; ring,
      show (((1 / 6 : ℝ)) : ℂ) = 7 / 3 - 7 / 6 - 1 by push_cast; ring]
    ring_nf
  simp_rw [hI, hG]

/-! ### Expansions on closed rotated sectors -/

/-- `z → ∞` with `|(3/2) arg z + θ| ≤ γ`. -/
def airyRot_filter (θ γ : ℝ) : Filter ℂ :=
  comap (fun z : ℂ => ‖z‖) atTop ⊓ 𝓟 {z : ℂ | z ≠ 0 ∧ |3 / 2 * arg z + θ| ≤ γ}

lemma airyRot_eventually_mem (θ γ : ℝ) :
    ∀ᶠ z in airyRot_filter θ γ, z ≠ 0 ∧ |3 / 2 * arg z + θ| ≤ γ :=
  mem_inf_of_right (mem_principal_self _)

/-- `‖2ζ‖ = (4/3) ‖z‖^{3/2}`. -/
lemma airyRot_norm_two_zeta (z : ℂ) : ‖2 * airyZetaComplex z‖ = 4 / 3 * ‖z‖ ^ (3 / 2 : ℝ) := by
  rw [airyZetaComplex, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring, norm_mul, norm_mul,
    norm_cpow_real]
  norm_num
  ring

/-- The rotated variable `W = 2ζ e^{iθ}` tends to infinity in the sector `cos γ |W| ≤ re W`. -/
lemma airyRot_tendsto_W (θ : ℝ) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ : γ < π / 2) :
    Tendsto (fun z => exp (log 2 + airyLogZeta z + θ * I)) (airyRot_filter θ γ)
      (sectorAtTop (Real.cos γ)) := by
  have hnorm : ∀ z : ℂ, z ≠ 0 →
      ‖exp (log 2 + airyLogZeta z + θ * I)‖ = 4 / 3 * ‖z‖ ^ (3 / 2 : ℝ) := by
    intro z hz
    rw [← airyRot_two_zeta_mul_exp hz θ, norm_mul, norm_exp_ofReal_mul_I, mul_one,
      airyRot_norm_two_zeta]
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · have h : Tendsto (fun z : ℂ => 4 / 3 * ‖z‖ ^ (3 / 2 : ℝ)) (airyRot_filter θ γ) atTop :=
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).comp
        (tendsto_comap.mono_left inf_le_left)).const_mul_atTop (by norm_num)
    refine h.congr' ?_
    filter_upwards [airyRot_eventually_mem θ γ] with z hz
    simp only [Function.comp_apply]
    rw [hnorm z hz.1]
  · filter_upwards [airyRot_eventually_mem θ γ] with z hz
    show Real.cos γ * ‖exp (log 2 + airyLogZeta z + θ * I)‖ ≤ (exp (log 2 + airyLogZeta z + θ * I)).re
    rw [airyRot_re_W, Complex.norm_exp]
    have : Real.cos γ ≤ Real.cos (3 / 2 * arg z + θ) := by
      rw [← Real.cos_abs (3 / 2 * arg z + θ)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hz.2
    have he : (log 2 + airyLogZeta z + θ * I).re = (log 2 + airyLogZeta z).re := by simp
    rw [he, mul_comm]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le

/-- `W^{-s} = exp (-s (log 2 + L + iθ))` on the closed rotated sector. -/
lemma airyRot_W_cpow {z : ℂ} {θ γ : ℝ} (hγ : γ < π / 2) (hz : |3 / 2 * arg z + θ| ≤ γ) (s : ℂ) :
    exp (log 2 + airyLogZeta z + θ * I) ^ s = exp (s * (log 2 + airyLogZeta z + θ * I)) := by
  have him : (log 2 + airyLogZeta z + θ * I).im = 3 / 2 * arg z + θ := by
    rw [add_im, im_log_two_add_airyLogZeta]; simp
  rw [cpow_def_of_ne_zero (exp_ne_zero _), log_exp (by rw [him]; linarith [abs_le.mp hz, Real.pi_pos])
    (by rw [him]; linarith [abs_le.mp hz, Real.pi_pos]), mul_comm]

/-- **The generic Airy expansion on a closed rotated sector.** -/
lemma airyRot_expansion (a β : ℝ) (ha : 0 < a) {θ : ℝ} (hθ : |θ| < π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ < π / 2) {f ε : ℂ → ℂ} (κ : ℂ)
    (hf : ∀ᶠ z in airyRot_filter θ γ, f z = ε z * (exp (θ * I) *
      airyRot_lap a β θ (exp (log 2 + airyLogZeta z + θ * I))))
    (hε : ∀ᶠ z in airyRot_filter θ γ, ε z * exp (-(a * (log 2 + airyLogZeta z))) = κ) :
    HasAsymptoticExpansion (airyRot_filter θ γ) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (fun n => κ * (Gamma ((n : ℂ) + a) * Ring.choose (β : ℂ) n) / 2 ^ n) f := by
  have hW := (airyRot_hasAsymptoticExpansion a β ha hθ (Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos], hγ⟩)).comp_tendsto (airyRot_tendsto_W θ hγ0 hγ)
  have h1 := hW.mul_left ε
  have h2 := h1.smul_scale (κ := fun n : ℕ => κ * exp (-(θ * I * ((n : ℂ) + a))) / 2 ^ n)
    (ψ := fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) fun n => by
      filter_upwards [airyRot_eventually_mem θ γ, hε] with z hz hεz
      rw [airyRot_W_cpow hγ hz.2, ← hεz]
      have h2z : exp (log 2 + airyLogZeta z) = 2 * airyZetaComplex z :=
        exp_log_two_add_airyLogZeta hz.1
      have hsplit : exp (-((n : ℂ) + a) * (log 2 + airyLogZeta z + θ * I)) =
          exp (-(a * (log 2 + airyLogZeta z))) * exp (-(θ * I * ((n : ℂ) + a))) *
            (exp (log 2 + airyLogZeta z) ^ n)⁻¹ := by
        rw [← exp_nat_mul, ← exp_neg, ← exp_add, ← exp_add]
        congr 1; ring
      rw [hsplit, h2z, mul_pow]
      ring
  refine (h2.congr_coeff ?_).congr' ?_
  · funext n
    simp only [smul_eq_mul]
    have : exp (-(θ * I * ((n : ℂ) + a))) * exp (θ * I * ((n : ℂ) + a)) = 1 := by
      rw [← exp_add]; simp
    field_simp
    linear_combination (κ * Gamma ((n : ℂ) + a) * Ring.choose (β : ℂ) n) * this
  · filter_upwards [hf] with z hz
    rw [hz]
    simp only [Function.comp_apply, smul_eq_mul]

/-! ### The Airy coefficients -/

lemma airyRot_ascPochhammer_ofReal (n : ℕ) (x : ℝ) :
    (ascPochhammer ℂ n).eval (x : ℂ) = (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]; push_cast; ring

lemma airyRot_gamma_ratio (n : ℕ) {x : ℝ} (hx : 0 < x) :
    Gamma ((n : ℂ) + x) / Gamma x = (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) := by
  rw [add_comm, Gamma_add_nat_div_Gamma_eq, airyRot_ascPochhammer_ofReal]
  intro k h
  have := congrArg Complex.re h
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma airyRot_choose_ofReal_neg (n : ℕ) (x : ℝ) :
    Ring.choose ((-x : ℝ) : ℂ) n =
      (-1) ^ n * (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) / n.factorial := by
  rw [ofReal_neg, ring_choose_neg_eq_poch, poch, airyRot_ascPochhammer_ofReal]

/-- The Ai coefficients: `Γ(n+5/6)/Γ(5/6) · binom(-1/6, n) / 2^n = (-1)^n u_n`. -/
lemma airyRot_coeff_ai (n : ℕ) :
    1 / Gamma ((5 / 6 : ℝ) : ℂ) * (Gamma ((n : ℂ) + ((5 / 6 : ℝ) : ℂ)) *
      Ring.choose (((-1 / 6 : ℝ)) : ℂ) n) / 2 ^ n = airyExpansionCoeff .ai n := by
  have hG : Gamma ((5 / 6 : ℝ) : ℂ) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp)
  have h1 := airyRot_gamma_ratio n (x := 5 / 6) (by norm_num)
  have h2 := airyRot_choose_ofReal_neg n (1 / 6)
  rw [show ((-1 / 6 : ℝ)) = -(1 / 6 : ℝ) by ring, h2]
  rw [div_eq_iff hG] at h1
  simp only [airyExpansionCoeff, airyU]
  rw [h1]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  generalize Gamma ((5 / 6 : ℝ) : ℂ) = G at hG ⊢
  push_cast
  field_simp

lemma airyRot_poch_seven_sixths (n : ℕ) :
    (ascPochhammer ℝ n).eval (7 / 6) = (6 * n + 1) * (ascPochhammer ℝ n).eval (1 / 6) := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ih]; push_cast; ring

lemma airyRot_poch_neg_sixth (n : ℕ) :
    (ascPochhammer ℝ n).eval (-1 / 6) * (1 - 6 * n) = (ascPochhammer ℝ n).eval (5 / 6) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, ← ih]; push_cast; ring

/-- The Ai' coefficients: `Γ(n+7/6)/Γ(7/6) · binom(1/6, n) / 2^n = (-1)^n v_n`. -/
lemma airyRot_coeff_aiDeriv (n : ℕ) :
    1 / Gamma ((7 / 6 : ℝ) : ℂ) * (Gamma ((n : ℂ) + ((7 / 6 : ℝ) : ℂ)) *
      Ring.choose (((1 / 6 : ℝ)) : ℂ) n) / 2 ^ n = airyExpansionCoeff .aiDeriv n := by
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp)
  have h1 := airyRot_gamma_ratio n (x := 7 / 6) (by norm_num)
  have h2 := airyRot_choose_ofReal_neg n (-1 / 6)
  rw [show ((1 / 6 : ℝ)) = -(-1 / 6 : ℝ) by ring, h2]
  rw [div_eq_iff hG] at h1
  simp only [airyExpansionCoeff, airyV, airyU]
  rw [h1, airyRot_poch_seven_sixths, ← airyRot_poch_neg_sixth]
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have h6 : (1 - 6 * (n : ℂ)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    have h' : (6 * n : ℝ) = 1 := by linarith
    have : (6 * n : ℕ) = 1 := by exact_mod_cast h'
    omega
  generalize Gamma ((7 / 6 : ℝ) : ℂ) = G at hG ⊢
  push_cast
  field_simp

/-! ### The normalized Ai, Ai' on closed rotated sectors -/

lemma airyRot_exp_combine {z : ℂ} (hz : z ≠ 0) (c3 p q a : ℂ)
    (hkey : log 2 + c3 * log 3 + p * (log 2 - log 3 + 3 / 2 * log z) + q * log z -
      a * (log 2 + (log 2 - log 3 + 3 / 2 * log z)) = 0) :
    2 * (3 : ℂ) ^ c3 * exp (p * airyLogZeta z) * z ^ q * exp (-(a * (log 2 + airyLogZeta z))) =
      1 := by
  rw [cpow_def_of_ne_zero hz, cpow_def_of_ne_zero (by norm_num : (3 : ℂ) ≠ 0), airyLogZeta,
    log_two_thirds]
  calc 2 * exp (log 3 * c3) * exp (p * (log 2 - log 3 + 3 / 2 * log z)) * exp (log z * q) *
        exp (-(a * (log 2 + (log 2 - log 3 + 3 / 2 * log z))))
      = exp (log 2) * exp (log 3 * c3) * exp (p * (log 2 - log 3 + 3 / 2 * log z)) *
          exp (log z * q) * exp (-(a * (log 2 + (log 2 - log 3 + 3 / 2 * log z)))) := by
        rw [exp_log two_ne_zero]
    _ = exp (log 2 + c3 * log 3 + p * (log 2 - log 3 + 3 / 2 * log z) + q * log z -
          a * (log 2 + (log 2 - log 3 + 3 / 2 * log z))) := by
        simp only [← exp_add]; congr 1; ring
    _ = 1 := by rw [hkey, exp_zero]

/-- The normalized `Ai` on a closed rotated sector. -/
lemma airyRot_airyAi_expansion_piece {θ : ℝ} (hθ : |θ| < π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ < π / 2) :
    HasAsymptoticExpansion (airyRot_filter θ γ) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .ai) (fun z => airyAi z / airyPrefactor .ai z) := by
  have hG : Gamma ((5 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h := airyRot_expansion (5 / 6) (-1 / 6) (by norm_num) hθ hγ0 hγ
    (f := fun z => airyAi z / airyPrefactor .ai z)
    (ε := fun z => 2 * (3 : ℂ) ^ (-1 / 6 : ℂ) * exp (2 / 3 * airyLogZeta z) * z ^ (1 / 4 : ℂ) /
      Gamma ((5 / 6 : ℝ) : ℂ)) (1 / Gamma ((5 / 6 : ℝ) : ℂ)) ?_ ?_
  · exact h.congr_coeff (funext airyRot_coeff_ai)
  · filter_upwards [airyRot_eventually_mem θ γ] with z hz
    have hz0 := hz.1
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    rw [airyRot_eq_of_anchor differentiable_airyAi _ _ (5 / 6) (-1 / 6) (by norm_num)
      (fun w hw harg => airyRot_airyAi_anchor hw harg) hθ hz0
      (lt_of_le_of_lt hz.2 hγ)]
    simp only [airyPrefactor]
    rw [exp_sub]
    have hE : exp (airyZetaComplex z) * exp (-airyZetaComplex z) = 1 := by
      rw [← exp_add]; simp
    field_simp
    linear_combination (-airyRot_lap (5 / 6) (-(1 / 6)) θ
      (exp (log 2 + airyLogZeta z + θ * I))) * hE
  · filter_upwards [airyRot_eventually_mem θ γ] with z hz
    rw [div_mul_eq_mul_div, airyRot_exp_combine hz.1 _ _ _ _ (by push_cast; ring)]

/-- The normalized `Ai'` on a closed rotated sector. -/
lemma airyRot_airyAiDeriv_expansion_piece {θ : ℝ} (hθ : |θ| < π) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ : γ < π / 2) :
    HasAsymptoticExpansion (airyRot_filter θ γ) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .aiDeriv) (fun z => airyAiDeriv z / airyPrefactor .aiDeriv z) := by
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h := airyRot_expansion (7 / 6) (1 / 6) (by norm_num) hθ hγ0 hγ
    (f := fun z => airyAiDeriv z / airyPrefactor .aiDeriv z)
    (ε := fun z => 2 * (3 : ℂ) ^ (1 / 6 : ℂ) * exp (4 / 3 * airyLogZeta z) * z ^ (-1 / 4 : ℂ) /
      Gamma ((7 / 6 : ℝ) : ℂ)) (1 / Gamma ((7 / 6 : ℝ) : ℂ)) ?_ ?_
  · exact h.congr_coeff (funext airyRot_coeff_aiDeriv)
  · filter_upwards [airyRot_eventually_mem θ γ] with z hz
    have hz0 := hz.1
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hqq : z ^ (-(1 / 4) : ℂ) * z ^ (1 / 4 : ℂ) = 1 := by
      rw [← cpow_add _ _ hz0]; norm_num
    have hE : exp (airyZetaComplex z) * exp (-airyZetaComplex z) = 1 := by
      rw [← exp_add]; simp
    rw [airyRot_eq_of_anchor (hf := fun w => (hasDerivAt_airyAiDeriv w).differentiableAt) _ _
      (7 / 6) (1 / 6) (by norm_num) (fun w hw harg => airyRot_airyAiDeriv_anchor hw harg) hθ hz0
      (lt_of_le_of_lt hz.2 hγ)]
    simp only [airyPrefactor]
    rw [exp_sub]
    field_simp
    linear_combination (-airyRot_lap (7 / 6) (1 / 6) θ (exp (log 2 + airyLogZeta z + θ * I)) *
      z ^ (1 / 4 : ℂ) * z ^ (-(1 / 4) : ℂ)) * hE +
      (-airyRot_lap (7 / 6) (1 / 6) θ (exp (log 2 + airyLogZeta z + θ * I))) * hqq
  · filter_upwards [airyRot_eventually_mem θ γ] with z hz
    rw [div_mul_eq_mul_div, airyRot_exp_combine hz.1 _ _ _ _ (by push_cast; ring)]

/-! ### Gluing the rotated sectors -/

/-- Five closed rotated sectors cover the sector `|arg z| ≤ π - δ`. -/
lemma airyRot_sector_le {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    airySector (π - δ) ≤ airyRot_filter 0 (π / 2 - δ / 4) ⊔
      airyRot_filter (-(π / 2)) (π / 2 - δ / 4) ⊔ airyRot_filter (π / 2) (π / 2 - δ / 4) ⊔
      airyRot_filter (-(π - δ / 4)) (π / 2 - δ / 4) ⊔
      airyRot_filter (π - δ / 4) (π / 2 - δ / 4) := by
  simp only [airyRot_filter, airySector, ← inf_sup_left, sup_principal]
  refine inf_le_inf_left _ (principal_mono.mpr ?_)
  rintro z ⟨hz, harg⟩
  have ha := abs_le.mp harg
  simp only [mem_union, mem_ofPred_eq]
  set φ := 3 / 2 * arg z with hφ
  have hφ1 : -(3 / 2 * (π - δ)) ≤ φ := by rw [hφ]; linarith
  have hφ2 : φ ≤ 3 / 2 * (π - δ) := by rw [hφ]; linarith
  rcases le_or_gt φ (π / 2 - δ / 4) with h1 | h1
  · rcases le_or_gt (-(π / 2 - δ / 4)) φ with h2 | h2
    · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩)))
    · rcases le_or_gt (-(π - δ / 4)) φ with h3 | h3
      · exact Or.inl (Or.inl (Or.inr ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩))
      · exact Or.inr ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  · rcases le_or_gt φ (π - δ / 4) with h3 | h3
    · exact Or.inl (Or.inl (Or.inl (Or.inr ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩)))
    · exact Or.inl (Or.inr ⟨hz, abs_le.mpr ⟨by linarith, by linarith⟩⟩)

/-- Expansions valid on every closed rotated sector glue to `|arg z| ≤ π - δ`. -/
lemma airyRot_glue {φ : ℕ → ℂ → ℂ} {c : ℕ → ℂ} {f : ℂ → ℂ}
    (h : ∀ θ : ℝ, |θ| < π → ∀ γ : ℝ, 0 ≤ γ → γ < π / 2 →
      HasAsymptoticExpansion (airyRot_filter θ γ) φ c f)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    HasAsymptoticExpansion (airySector (π - δ)) φ c f := by
  have hπ := Real.pi_pos
  have hγ0 : 0 ≤ π / 2 - δ / 4 := by linarith
  have hγ : π / 2 - δ / 4 < π / 2 := by linarith
  refine (((((h 0 (by simpa using hπ) _ hγ0 hγ).sup
    (h (-(π / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith) _ hγ0 hγ)).sup
    (h (π / 2) (by rw [abs_of_pos (by linarith)]; linarith) _ hγ0 hγ)).sup
    (h (-(π - δ / 4)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith) _ hγ0 hγ)).sup
    (h (π - δ / 4) (by rw [abs_of_pos (by linarith)]; linarith) _ hγ0 hγ)).mono
    (airyRot_sector_le hδ hδ')

/-- **Poincaré expansion of the normalized `Ai`** in `|arg z| ≤ π - δ` (DLMF 9.7.5). -/
theorem airyRot_airyAi_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    HasAsymptoticExpansion (airySector (π - δ)) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .ai) (fun z => airyAi z / airyPrefactor .ai z) :=
  airyRot_glue (fun _ hθ _ hγ0 hγ => airyRot_airyAi_expansion_piece hθ hγ0 hγ) hδ hδ'

/-- **Poincaré expansion of the normalized `Ai'`** in `|arg z| ≤ π - δ` (DLMF 9.7.6). -/
theorem airyRot_airyAiDeriv_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) :
    HasAsymptoticExpansion (airySector (π - δ)) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .aiDeriv) (fun z => airyAiDeriv z / airyPrefactor .aiDeriv z) :=
  airyRot_glue (fun _ hθ _ hγ0 hγ => airyRot_airyAiDeriv_expansion_piece hθ hγ0 hγ) hδ hδ'

/-! ### From normalized expansions to the Poincaré statements -/

lemma airyRot_eventually_ne_zero (α : ℝ) : ∀ᶠ z in airySector α, z ≠ 0 :=
  mem_inf_of_right (mem_principal.mpr fun _ hz => hz.1)

lemma airyRot_eventually_arg (α : ℝ) : ∀ᶠ z in airySector α, z ≠ 0 ∧ |arg z| ≤ α :=
  mem_inf_of_right (mem_principal_self _)

lemma airyRot_prefactor_ne_zero (kind : AiryKind) {z : ℂ} (hz : z ≠ 0) :
    airyPrefactor kind z ≠ 0 := by
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
  cases kind <;> simp only [airyPrefactor] <;> field_simp <;> simp [hπ, hz, exp_ne_zero]

/-- A normalized expansion gives the Poincaré `O`-statement. -/
lemma airyRot_isBigO_of_expansion {l : Filter ℂ} {f p : ℂ → ℂ} {c : ℕ → ℂ}
    (h : HasAsymptoticExpansion l (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c
      (fun z => f z / p z)) (hp : ∀ᶠ z in l, p z ≠ 0) (N : ℕ) :
    IsBigO l (fun z => f z - p z * ∑ k ∈ Finset.range N, c k / airyZetaComplex z ^ k)
      (fun z => p z / airyZetaComplex z ^ N) := by
  refine ((isBigO_refl p l).mul (h N)).congr' ?_ (Eventually.of_forall fun z => ?_)
  · filter_upwards [hp] with z hz
    simp only [smul_eq_mul]
    rw [mul_sub, mul_div_cancel₀ _ hz]
    congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [div_eq_mul_inv, mul_comm]
  · simp only [div_eq_mul_inv]

/-! ### Rotations of the variable -/

lemma airyRot_arg_mul_exp {z : ℂ} (hz : z ≠ 0) {α : ℝ} (h1 : -π < arg z + α)
    (h2 : arg z + α ≤ π) : arg (z * exp (α * I)) = arg z + α := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [mul_assoc, ← exp_add, show (arg z : ℂ) * I + α * I = ((arg z + α : ℝ) : ℂ) * I by
    push_cast; ring]
  exact airyRot_arg (norm_pos_iff.mpr hz) h1 h2

lemma airyRot_zeta_mul_exp {z : ℂ} (hz : z ≠ 0) {α : ℝ} (h1 : -π < arg z + α)
    (h2 : arg z + α ≤ π) :
    airyZetaComplex (z * exp (α * I)) = airyZetaComplex z * exp (α * I * (3 / 2)) := by
  unfold airyZetaComplex
  rw [Complex.cpow_mul_exp_ofReal_mul_I hz h1 h2]
  ring

/-- Rotation by `c` maps the sector `|arg z| ≤ α` into `|arg z| ≤ β` when `|c| + α ≤ β < π`. -/
lemma airyRot_tendsto_rotate {α β c : ℝ} (hc : |c| + α ≤ β) (hβ : β < π) :
    Tendsto (fun z : ℂ => z * exp (c * I)) (airySector α) (airySector β) := by
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · refine (tendsto_comap.mono_left inf_le_left).congr fun z => ?_
    simp only [Function.comp_apply, norm_mul, norm_exp_ofReal_mul_I, mul_one]
  · filter_upwards [airyRot_eventually_arg α] with z hz
    refine ⟨mul_ne_zero hz.1 (exp_ne_zero _), ?_⟩
    have h1 := abs_le.mp hz.2
    have h2 := le_abs_self c
    have h3 := neg_abs_le c
    rw [airyRot_arg_mul_exp hz.1 (by linarith) (by linarith)]
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The exponents `e^{±2πi/3}` in the form `e^{iα}`. -/
lemma airyRot_exp_two_pi_div_three :
    exp (2 * π * I / 3) = exp (((2 * π / 3 : ℝ) : ℂ) * I) ∧
      exp (-(2 * π * I / 3)) = exp (((-(2 * π / 3)) : ℝ) * I) := by
  constructor <;> congr 1 <;> push_cast <;> ring

/-- An expansion on `|arg z| ≤ π - δ` gives, at the two rotated points `z e^{±2πi/3}`,
expansions on `|arg z| ≤ π/3 - δ` with alternating coefficients. -/
lemma airyRot_rotated_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    HasAsymptoticExpansion (airySector (π / 3 - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) (fun n => (-1) ^ n * c n)
      (fun z => F (z * exp (((ε * (2 * π / 3)) : ℝ) * I))) := by
  have hπ := Real.pi_pos
  have habs : |ε * (2 * π / 3)| = 2 * π / 3 := by
    rcases hε with h | h <;> subst h <;> simp [abs_of_pos (by positivity : (0:ℝ) < 2 * π / 3)]
  have h := hF.comp_tendsto (airyRot_tendsto_rotate (α := π / 3 - δ) (β := π - δ)
    (c := ε * (2 * π / 3)) (by rw [habs]; linarith) (by linarith))
  refine (h.smul_scale (κ := fun n => (-1 : ℂ) ^ n)
    (ψ := fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) fun n => ?_).congr_coeff ?_
  · filter_upwards [airyRot_eventually_arg (π / 3 - δ)] with z hz
    have h1 := abs_le.mp hz.2
    have h2 : -π < arg z + ε * (2 * π / 3) ∧ arg z + ε * (2 * π / 3) ≤ π := by
      rcases hε with h | h <;> subst h <;> constructor <;> linarith
    rw [airyRot_zeta_mul_exp hz.1 h2.1 h2.2]
    have he : exp (((ε * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -1 := by
      rcases hε with h | h <;> subst h
      · rw [show (((1 * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = π * I by push_cast; ring,
          exp_pi_mul_I]
      · rw [show ((((-1) * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -(π * I) by push_cast; ring,
          exp_neg, exp_pi_mul_I]; norm_num
    rw [he, mul_neg_one, neg_pow, mul_inv, ← inv_pow, inv_neg, inv_one]
  · funext n
    simp only [smul_eq_mul]

lemma airyRot_exp_rot_three_halves {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    exp (((ε * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -1 := by
  rcases hε with h | h <;> subst h
  · rw [show (((1 * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = π * I by push_cast; ring,
      exp_pi_mul_I]
  · rw [show ((((-1) * (2 * π / 3) : ℝ) : ℂ) * I * (3 / 2)) = -(π * I) by push_cast; ring,
      exp_neg, exp_pi_mul_I]; norm_num

lemma airyRot_arg_rot_bounds {z : ℂ} (hz : |arg z| < π / 3) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    -π < arg z + ε * (2 * π / 3) ∧ arg z + ε * (2 * π / 3) ≤ π := by
  have h1 := abs_lt.mp hz
  have hπ := Real.pi_pos
  rcases hε with h | h <;> subst h <;> constructor <;> linarith

/-- `ζ(z e^{±2πi/3}) = -ζ(z)` for `|arg z| ≤ π/3`. -/
lemma airyRot_zeta_rot {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    airyZetaComplex (z * exp (((ε * (2 * π / 3)) : ℝ) * I)) = -airyZetaComplex z := by
  obtain ⟨h1, h2⟩ := airyRot_arg_rot_bounds hz hε
  rw [airyRot_zeta_mul_exp hz0 h1 h2, airyRot_exp_rot_three_halves hε, mul_neg_one]

/-- `(z e^{±2πi/3})^{1/4} = z^{1/4} e^{±πi/6}`. -/
lemma airyRot_quarter_rot {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) :
    (z * exp (((ε * (2 * π / 3)) : ℝ) * I)) ^ (1 / 4 : ℂ) =
      z ^ (1 / 4 : ℂ) * exp (((ε * (π / 6)) : ℝ) * I) := by
  obtain ⟨h1, h2⟩ := airyRot_arg_rot_bounds hz hε
  rw [Complex.cpow_mul_exp_ofReal_mul_I hz0 h1 h2]
  congr 2
  push_cast; ring

lemma airyRot_exp_mul_exp_neg (w : ℂ) : exp w * exp (-w) = 1 := by
  rw [← exp_add]; simp

/-- **Poincaré expansion of the normalized `Bi`** in `|arg z| ≤ π/3 - δ` (DLMF 9.7.7). -/
theorem airyRot_airyBi_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) :
    HasAsymptoticExpansion (airySector (π / 3 - δ)) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .bi) (fun z => airyBi z / airyPrefactor .bi z) := by
  have hπ := Real.pi_pos
  have hA := airyRot_airyAi_expansion hδ (by linarith)
  have hp := airyRot_rotated_expansion hδ hA (Or.inl rfl)
  have hm := airyRot_rotated_expansion hδ hA (Or.inr rfl)
  refine ((hp.const_smul (1 / 2 : ℂ)).add (hm.const_smul (1 / 2 : ℂ))).congr_coeff ?_ |>.congr' ?_
  · funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, airyExpansionCoeff]
    have h1 : ((-1 : ℂ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (airyU n : ℂ) * h1
  · filter_upwards [airyRot_eventually_arg (π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < π / 3 := hz.2.trans_lt (by linarith)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    rw [airyBi_eq_airyAi_omega z, airyRot_exp_two_pi_div_three.1, airyRot_exp_two_pi_div_three.2]
    simp only [airyPrefactor]
    rw [airyRot_zeta_rot hz0 hz3 (Or.inl rfl), airyRot_zeta_rot hz0 hz3 (Or.inr rfl),
      airyRot_quarter_rot hz0 hz3 (Or.inl rfl), airyRot_quarter_rot hz0 hz3 (Or.inr rfl)]
    rw [show (((1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((2 * π / 3 : ℝ) : ℂ) by push_cast; ring,
      show (((-1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((-(2 * π / 3) : ℝ) : ℂ) by push_cast; ring]
    have e1 : exp ((((1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = exp (π * I / 6) := by
      congr 1; push_cast; ring
    have e2 : exp ((((-1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = exp (-(π * I / 6)) := by
      congr 1; push_cast; ring
    rw [e1, e2]
    have h6 := airyRot_exp_mul_exp_neg (π * I / 6)
    have hz2 := airyRot_exp_mul_exp_neg (airyZetaComplex z)
    rw [neg_neg]
    field_simp
    ring_nf

/-- Differentiating an identity `f(z) = c₁ g(z w₁) + c₂ g(z w₂)`. -/
lemma airyRot_deriv_of_eq {f g f' g' : ℂ → ℂ} (hf : ∀ z, HasDerivAt f (f' z) z)
    (hg : ∀ z, HasDerivAt g (g' z) z) (c₁ c₂ w₁ w₂ : ℂ)
    (h : ∀ z, f z = c₁ * g (z * w₁) + c₂ * g (z * w₂)) (z : ℂ) :
    f' z = c₁ * w₁ * g' (z * w₁) + c₂ * w₂ * g' (z * w₂) := by
  have h1 : HasDerivAt (fun z => c₁ * g (z * w₁) + c₂ * g (z * w₂))
      (c₁ * (g' (z * w₁) * w₁) + c₂ * (g' (z * w₂) * w₂)) z :=
    (((hg (z * w₁)).comp z ((hasDerivAt_id z).mul_const w₁)).const_mul c₁).add
      (((hg (z * w₂)).comp z ((hasDerivAt_id z).mul_const w₂)).const_mul c₂) |>.congr_deriv
      (by simp)
  rw [← funext h] at h1
  rw [(hf z).unique h1]
  ring

/-- `Bi'(z) = e^{-5πi/6} Ai'(z e^{-2πi/3}) + e^{5πi/6} Ai'(z e^{2πi/3})`. -/
lemma airyRot_airyBiDeriv_eq (z : ℂ) :
    airyBiDeriv z = exp (-(π * I / 6)) * exp (-(2 * π * I / 3)) *
        airyAiDeriv (z * exp (-(2 * π * I / 3))) +
      exp (π * I / 6) * exp (2 * π * I / 3) * airyAiDeriv (z * exp (2 * π * I / 3)) :=
  airyRot_deriv_of_eq hasDerivAt_airyBi hasDerivAt_airyAi _ _ _ _ airyBi_eq_airyAi_omega z

/-- **Poincaré expansion of the normalized `Bi'`** in `|arg z| ≤ π/3 - δ` (DLMF 9.7.8). -/
theorem airyRot_airyBiDeriv_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) :
    HasAsymptoticExpansion (airySector (π / 3 - δ)) (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (airyExpansionCoeff .biDeriv) (fun z => airyBiDeriv z / airyPrefactor .biDeriv z) := by
  have hπ := Real.pi_pos
  have hA := airyRot_airyAiDeriv_expansion hδ (by linarith)
  have hp := airyRot_rotated_expansion hδ hA (Or.inl rfl)
  have hm := airyRot_rotated_expansion hδ hA (Or.inr rfl)
  refine ((hp.const_smul (1 / 2 : ℂ)).add (hm.const_smul (1 / 2 : ℂ))).congr_coeff ?_ |>.congr' ?_
  · funext n
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, airyExpansionCoeff]
    have h1 : ((-1 : ℂ) ^ n) * ((-1) ^ n) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (airyV n : ℂ) * h1
  · filter_upwards [airyRot_eventually_arg (π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < π / 3 := hz.2.trans_lt (by linarith)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    rw [airyRot_airyBiDeriv_eq z, airyRot_exp_two_pi_div_three.1,
      airyRot_exp_two_pi_div_three.2]
    simp only [airyPrefactor]
    rw [airyRot_zeta_rot hz0 hz3 (Or.inl rfl), airyRot_zeta_rot hz0 hz3 (Or.inr rfl),
      airyRot_quarter_rot hz0 hz3 (Or.inl rfl), airyRot_quarter_rot hz0 hz3 (Or.inr rfl)]
    rw [show (((1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((2 * π / 3 : ℝ) : ℂ) by push_cast; ring,
      show (((-1 : ℝ) * (2 * π / 3) : ℝ) : ℂ) = ((-(2 * π / 3)) : ℝ) by push_cast; ring]
    set u := exp (π * I / 6) with hu
    have e1 : exp ((((1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = u := by
      rw [hu]; congr 1; push_cast; ring
    have e2 : exp ((((-1 : ℝ) * (π / 6) : ℝ) : ℂ) * I) = u⁻¹ := by
      rw [hu, ← exp_neg]; congr 1; push_cast; ring
    have e3 : exp (((2 * π / 3 : ℝ) : ℂ) * I) = u ^ 4 := by
      rw [hu, ← exp_nat_mul]; congr 1; push_cast; ring
    have e4 : exp (((-(2 * π / 3) : ℝ) : ℂ) * I) = (u ^ 4)⁻¹ := by
      rw [hu, ← exp_nat_mul, ← exp_neg]; congr 1; push_cast; ring
    have e5 : exp (-(π * I / 6)) = u⁻¹ := by rw [hu, exp_neg]
    have hu6 : u ^ 6 = -1 := by
      rw [hu, ← exp_nat_mul, show ((6 : ℕ) : ℂ) * (π * I / 6) = π * I by push_cast; ring,
        exp_pi_mul_I]
    have hu0 : u ≠ 0 := exp_ne_zero _
    rw [e1, e2, e3, e4, e5]
    have hz2 := airyRot_exp_mul_exp_neg (airyZetaComplex z)
    rw [neg_neg]
    field_simp
    linear_combination (-(airyAiDeriv (z / u ^ 4) + u ^ 4 * airyAiDeriv (z * u ^ 4))) * hu6

/-! ### Even and odd parts on the negative axis -/

/-- An expansion on `|arg z| ≤ π - δ` restricts along the rotation `z ↦ z e^{iα}` to the sector
`|arg z| ≤ β`, for `|α| + β ≤ π - δ`. -/
lemma airyRot_rot_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) {α β : ℝ} (hαβ : |α| + β ≤ π - δ) :
    HasAsymptoticExpansion (airySector β)
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹)
      (fun n => ((exp (α * I * (3 / 2))) ^ n)⁻¹ * c n)
      (fun z => F (z * exp (α * I))) := by
  have hπ := Real.pi_pos
  have h := hF.comp_tendsto (airyRot_tendsto_rotate (α := β) (β := π - δ) (c := α) hαβ
    (by linarith))
  refine (h.smul_scale (κ := fun n => ((exp (α * I * (3 / 2))) ^ n)⁻¹)
    (ψ := fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) fun n => ?_).congr_coeff ?_
  · filter_upwards [airyRot_eventually_arg β] with z hz
    have h1 := abs_le.mp hz.2
    have h2 := le_abs_self α
    have h3 := neg_abs_le α
    rw [airyRot_zeta_mul_exp hz.1 (by linarith) (by linarith), mul_pow, mul_inv, mul_comm]
  · funext n
    simp only [smul_eq_mul]

/-- The even part `(F(z e^{iπ/3}) + F(z e^{-iπ/3}))/2`. -/
def airyRot_even (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F (z * exp ((π / 3 : ℝ) * I)) + F (z * exp ((-(π / 3) : ℝ) * I))) / 2

/-- The odd part `(F(z e^{iπ/3}) - F(z e^{-iπ/3}))/(2i)`. -/
def airyRot_odd (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  (F (z * exp ((π / 3 : ℝ) * I)) - F (z * exp ((-(π / 3) : ℝ) * I))) / (2 * I)

lemma airyRot_exp_third_three_halves :
    exp (((π / 3 : ℝ) : ℂ) * I * (3 / 2)) = I ∧ exp (((-(π / 3)) : ℝ) * I * (3 / 2)) = -I := by
  constructor
  · rw [show (((π / 3 : ℝ) : ℂ) * I * (3 / 2)) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring,
      exp_mul_I]
    simp
  · rw [show ((((-(π / 3)) : ℝ) : ℂ) * I * (3 / 2)) = ((-(π / 2)) : ℝ) * I by push_cast; ring,
      exp_mul_I]
    simp

lemma airyRot_I_pow_inv_even (j : ℕ) :
    ((I ^ (2 * j))⁻¹ + ((-I) ^ (2 * j))⁻¹) / 2 = (-1) ^ j ∧
      ((I ^ (2 * j))⁻¹ - ((-I) ^ (2 * j))⁻¹) / (2 * I) = 0 := by
  have h1 : I ^ (2 * j) = (-1) ^ j := by rw [pow_mul, I_sq]
  have h2 : (-I) ^ (2 * j) = (-1) ^ j := by rw [pow_mul, neg_sq, I_sq]
  rw [h1, h2]
  constructor
  · rw [← inv_pow, inv_neg, inv_one]; ring
  · simp

lemma airyRot_I_pow_inv_odd (j : ℕ) :
    ((I ^ (2 * j + 1))⁻¹ + ((-I) ^ (2 * j + 1))⁻¹) / 2 = 0 ∧
      ((I ^ (2 * j + 1))⁻¹ - ((-I) ^ (2 * j + 1))⁻¹) / (2 * I) = -(-1) ^ j := by
  have h1 : I ^ (2 * j + 1) = (-1) ^ j * I := by rw [pow_succ, pow_mul, I_sq]
  have h2 : (-I) ^ (2 * j + 1) = -((-1) ^ j * I) := by rw [pow_succ, pow_mul, neg_sq, I_sq]; ring
  rw [h1, h2]
  have hI : I ≠ 0 := I_ne_zero
  have hm : ((-1 : ℂ) ^ j) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm2 : ((-1 : ℂ) ^ j) * (-1) ^ j = 1 := by rw [← mul_pow]; norm_num
  constructor
  · rw [inv_neg]; ring
  · field_simp
    linear_combination (2 : ℂ) * I_sq + (2 * I ^ 2) * hm2

lemma airyRot_pm_expansions {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) :
    HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
        (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) (fun n => (I ^ n)⁻¹ * c n)
        (fun z => F (z * exp ((π / 3 : ℝ) * I))) ∧
      HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
        (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) (fun n => ((-I) ^ n)⁻¹ * c n)
        (fun z => F (z * exp ((-(π / 3) : ℝ) * I))) := by
  have hπ := Real.pi_pos
  constructor
  · have h := airyRot_rot_expansion hδ hF (α := π / 3) (β := 2 * π / 3 - δ)
      (by rw [abs_of_pos (by positivity)]; linarith)
    rwa [airyRot_exp_third_three_halves.1] at h
  · have h := airyRot_rot_expansion hδ hF (α := -(π / 3)) (β := 2 * π / 3 - δ)
      (by rw [abs_neg, abs_of_pos (by positivity)]; linarith)
    rwa [airyRot_exp_third_three_halves.2] at h

/-- The even part has the even subseries `∑ (-1)^j c_{2j} ζ^{-2j}`. -/
lemma airyRot_even_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) :
    HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
      (fun (j : ℕ) z => ((airyZetaComplex z) ^ (2 * j))⁻¹) (fun j => (-1) ^ j * c (2 * j))
      (airyRot_even F) := by
  obtain ⟨hp, hm⟩ := airyRot_pm_expansions hδ hF
  have h := ((hp.add hm).const_smul (1 / 2 : ℂ)).congr' (g := airyRot_even F)
    (Eventually.of_forall fun z => by
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, airyRot_even]; ring)
  have h' := h.even (fun j => by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have := (airyRot_I_pow_inv_odd j).1
    linear_combination (c (2 * j + 1)) * this)
  refine h'.congr_coeff (funext fun j => ?_)
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have := (airyRot_I_pow_inv_even j).1
  linear_combination (c (2 * j)) * this

/-- The odd part has the odd subseries `-∑ (-1)^j c_{2j+1} ζ^{-2j-1}`. -/
lemma airyRot_odd_expansion {F : ℂ → ℂ} {c : ℕ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hF : HasAsymptoticExpansion (airySector (π - δ))
      (fun (n : ℕ) z => ((airyZetaComplex z) ^ n)⁻¹) c F) :
    HasAsymptoticExpansion (airySector (2 * π / 3 - δ))
      (fun (j : ℕ) z => ((airyZetaComplex z) ^ (2 * j + 1))⁻¹)
      (fun j => -((-1) ^ j * c (2 * j + 1))) (airyRot_odd F) := by
  obtain ⟨hp, hm⟩ := airyRot_pm_expansions hδ hF
  have h := ((hp.sub hm).const_smul (1 / (2 * I) : ℂ)).congr' (g := airyRot_odd F)
    (Eventually.of_forall fun z => by
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, airyRot_odd]; ring)
  have h' := h.odd (fun j => by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    have := (airyRot_I_pow_inv_even j).2
    linear_combination (c (2 * j)) * this)
  refine h'.congr_coeff (funext fun j => ?_)
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have := (airyRot_I_pow_inv_odd j).2
  linear_combination (c (2 * j + 1)) * this

/-! ### The oscillatory error envelope -/

lemma airyRot_norm_exp_mul_I_le (w : ℂ) :
    ‖exp (-(w * I))‖ ≤ Real.exp |w.im| ∧ ‖exp (w * I)‖ ≤ Real.exp |w.im| := by
  constructor <;> rw [Complex.norm_exp] <;> apply Real.exp_le_exp.mpr <;> simp <;>
    [exact le_abs_self _; exact neg_le_abs _]

lemma airyRot_norm_inv_pow (w : ℂ) (k : ℕ) : ‖(w ^ k)⁻¹‖ = ‖w‖ ^ (-(k : ℤ)) := by
  rw [norm_inv, norm_pow, zpow_neg, zpow_natCast]

/-- **The oscillatory envelope.** If `X = pref (a E + b O)` and `Y = pref (a P + b Q)` with
`a, b` combinations of `e^{∓iζ}`, then `X - Y` is bounded by the envelope
`|pref| e^{|im ζ|} (|ζ|^{-2N} + |ζ|^{-2M-1})`. -/
lemma airyRot_osc_bound {l : Filter ℂ} {E O P Q pref X Y : ℂ → ℂ} {N M : ℕ} (κp κm : ℂ)
    (hE : (fun z => E z - P z) =O[l] (fun z => ((airyZetaComplex z) ^ (2 * N))⁻¹))
    (hO : (fun z => O z - Q z) =O[l] (fun z => ((airyZetaComplex z) ^ (2 * M + 1))⁻¹))
    (hX : ∀ᶠ z in l, X z = pref z *
      ((κp * exp (-(airyZetaComplex z * I)) + κm * exp (airyZetaComplex z * I)) * E z +
        I * (κp * exp (-(airyZetaComplex z * I)) - κm * exp (airyZetaComplex z * I)) * O z))
    (hY : ∀ᶠ z in l, Y z = pref z *
      ((κp * exp (-(airyZetaComplex z * I)) + κm * exp (airyZetaComplex z * I)) * P z +
        I * (κp * exp (-(airyZetaComplex z * I)) - κm * exp (airyZetaComplex z * I)) * Q z)) :
    IsBigO l (fun z => X z - Y z) (fun z => ‖pref z‖ * Real.exp |(airyZetaComplex z).im| *
      (‖airyZetaComplex z‖ ^ (-(2 * N : ℤ)) + ‖airyZetaComplex z‖ ^ (-(2 * M + 1 : ℤ)))) := by
  obtain ⟨C1, hC1, h1⟩ := hE.exists_pos
  obtain ⟨C2, hC2, h2⟩ := hO.exists_pos
  set K := ‖κp‖ + ‖κm‖
  refine IsBigO.of_bound (K * (C1 + C2)) ?_
  filter_upwards [h1.bound, h2.bound, hX, hY] with z hz1 hz2 hzX hzY
  rw [hzX, hzY]
  set ζ := airyZetaComplex z
  obtain ⟨he1, he2⟩ := airyRot_norm_exp_mul_I_le ζ
  set A := κp * exp (-(ζ * I)) + κm * exp (ζ * I)
  set B := I * (κp * exp (-(ζ * I)) - κm * exp (ζ * I))
  have hA : ‖A‖ ≤ K * Real.exp |ζ.im| := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := norm_nonneg κp; have := norm_nonneg κm
    nlinarith
  have hB : ‖B‖ ≤ K * Real.exp |ζ.im| := by
    rw [norm_mul, norm_I, one_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have := norm_nonneg κp; have := norm_nonneg κm
    nlinarith
  have heq : pref z * (A * E z + B * O z) - pref z * (A * P z + B * Q z) =
      pref z * (A * (E z - P z) + B * (O z - Q z)) := by ring
  rw [heq]
  rw [airyRot_norm_inv_pow] at hz1 hz2
  have hr1 : (0 : ℝ) ≤ ‖ζ‖ ^ (-(2 * N : ℤ)) := by positivity
  have hr2 : (0 : ℝ) ≤ ‖ζ‖ ^ (-(2 * M + 1 : ℤ)) := by positivity
  have hex := Real.exp_pos |ζ.im|
  have hK : 0 ≤ K := by positivity
  rw [Real.norm_of_nonneg (by positivity)]
  rw [norm_mul]
  push_cast at hz1 hz2 ⊢
  calc ‖pref z‖ * ‖A * (E z - P z) + B * (O z - Q z)‖
      ≤ ‖pref z‖ * (‖A‖ * ‖E z - P z‖ + ‖B‖ * ‖O z - Q z‖) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul]
    _ ≤ ‖pref z‖ * (K * Real.exp |ζ.im| * (C1 * ‖ζ‖ ^ (-(2 * (N : ℤ)))) +
          K * Real.exp |ζ.im| * (C2 * ‖ζ‖ ^ (-(2 * (M : ℤ) + 1)))) := by
        gcongr
    _ ≤ K * (C1 + C2) * (‖pref z‖ * Real.exp |ζ.im| *
          (‖ζ‖ ^ (-(2 * (N : ℤ))) + ‖ζ‖ ^ (-(2 * (M : ℤ) + 1)))) := by
        have := norm_nonneg (pref z)
        have hp1 : 0 ≤ ‖pref z‖ * Real.exp |ζ.im| := by positivity
        nlinarith [mul_nonneg hp1 hr1, mul_nonneg hp1 hr2, mul_nonneg hK hC1.le,
          mul_nonneg hK hC2.le, mul_nonneg (mul_nonneg hp1 hr1) (mul_nonneg hK hC2.le),
          mul_nonneg (mul_nonneg hp1 hr2) (mul_nonneg hK hC1.le)]

/-! ### The oscillatory expansions on the negative axis -/

/-- Rewriting `α₊ F(z e^{iπ/3}) + α₋ F(z e^{-iπ/3})` through the even and odd parts. -/
lemma airyRot_decomp (F : ℂ → ℂ) (z αp αm : ℂ) :
    αp * F (z * exp ((π / 3 : ℝ) * I)) + αm * F (z * exp ((-(π / 3) : ℝ) * I)) =
      (αp + αm) * airyRot_even F z + I * (αp - αm) * airyRot_odd F z := by
  simp only [airyRot_even, airyRot_odd]
  field_simp
  ring

lemma airyRot_arg_third_bounds {z : ℂ} (hz : |arg z| < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) : -π < arg z + ε * (π / 3) ∧ arg z + ε * (π / 3) ≤ π := by
  have h1 := abs_lt.mp hz
  have hπ := Real.pi_pos
  rcases hε with h | h <;> subst h <;> constructor <;> linarith

/-- The data of `ζ` and `z^{1/4}` at the points `z e^{±iπ/3}`. -/
lemma airyRot_third_data {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyZetaComplex (z * exp ((π / 3 : ℝ) * I)) = airyZetaComplex z * I ∧
    airyZetaComplex (z * exp ((-(π / 3) : ℝ) * I)) = -(airyZetaComplex z * I) ∧
    (z * exp ((π / 3 : ℝ) * I)) ^ (1 / 4 : ℂ) = z ^ (1 / 4 : ℂ) * exp (π * I / 12) ∧
    (z * exp ((-(π / 3) : ℝ) * I)) ^ (1 / 4 : ℂ) = z ^ (1 / 4 : ℂ) * (exp (π * I / 12))⁻¹ := by
  obtain ⟨a1, a2⟩ := airyRot_arg_third_bounds hz (Or.inl rfl)
  obtain ⟨b1, b2⟩ := airyRot_arg_third_bounds hz (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at a1 a2 b1 b2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [airyRot_zeta_mul_exp hz0 a1 a2, airyRot_exp_third_three_halves.1]
  · rw [airyRot_zeta_mul_exp hz0 b1 b2, airyRot_exp_third_three_halves.2]; ring
  · rw [Complex.cpow_mul_exp_ofReal_mul_I hz0 a1 a2]; congr 2; push_cast; ring
  · rw [Complex.cpow_mul_exp_ofReal_mul_I hz0 b1 b2, ← exp_neg]; congr 2; push_cast; ring

/-- The connection formula for `Ai(-z)` with the rotations written as `e^{iα}`. -/
lemma airyRot_airyAi_neg (z : ℂ) :
    airyAi (-z) = exp (π * I / 3) * airyAi (z * exp ((π / 3 : ℝ) * I)) +
      exp (-π * I / 3) * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyAi_neg_connection z]
  congr 4 <;> push_cast <;> ring_nf

/-- `Bi(-z)` with the rotations written as `e^{iα}`. -/
lemma airyRot_airyBi_neg (z : ℂ) :
    airyBi (-z) = exp (-π * I / 6) * airyAi (z * exp ((π / 3 : ℝ) * I)) +
      exp (π * I / 6) * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyBi_neg_connection z]
  congr 4 <;> push_cast <;> ring_nf

/-- The twelfth root of `-1`, `u = e^{iπ/12}`, and the exponentials used below. -/
lemma airyRot_u_powers :
    exp (π * I / 3) = exp (π * I / 12) ^ 4 ∧ exp (-π * I / 3) = (exp (π * I / 12) ^ 4)⁻¹ ∧
    exp (π * I / 4) = exp (π * I / 12) ^ 3 ∧ exp (-(π * I / 4)) = (exp (π * I / 12) ^ 3)⁻¹ ∧
    exp (π * I / 6) = exp (π * I / 12) ^ 2 ∧ exp (-π * I / 6) = (exp (π * I / 12) ^ 2)⁻¹ ∧
    exp (π * I / 12) ^ 12 = -1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [← exp_nat_mul, ← exp_neg]
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring
  · rw [show ((12 : ℕ) : ℂ) * (π * I / 12) = π * I by push_cast; ring, exp_pi_mul_I]

/-- The sum identity behind the even subseries. -/
lemma airyRot_sum_even {d : ℕ → ℂ} (c : ℕ → ℂ) (hc : ∀ j, c (2 * j) = d (2 * j)) (N : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.range N, ((airyZetaComplex z) ^ (2 * j))⁻¹ • ((-1) ^ j * c (2 * j)) =
      ∑ k ∈ Finset.range N, (-1 : ℂ) ^ k * d (2 * k) / airyZetaComplex z ^ (2 * k) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, smul_eq_mul]; ring

lemma airyRot_sum_odd {d : ℕ → ℂ} (c : ℕ → ℂ) (hc : ∀ j, c (2 * j + 1) = -d (2 * j + 1)) (M : ℕ) (z : ℂ) :
    ∑ j ∈ Finset.range M, ((airyZetaComplex z) ^ (2 * j + 1))⁻¹ • (-((-1) ^ j * c (2 * j + 1))) =
      ∑ k ∈ Finset.range M, (-1 : ℂ) ^ k * d (2 * k + 1) / airyZetaComplex z ^ (2 * k + 1) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc, smul_eq_mul]; ring

lemma airyRot_coeff_parity (kind : AiryKind) (hk : kind = .ai ∨ kind = .aiDeriv) (j : ℕ) :
    airyExpansionCoeff kind (2 * j) =
      ((if kind = .aiDeriv then airyV (2 * j) else airyU (2 * j) : ℝ) : ℂ) ∧
    airyExpansionCoeff kind (2 * j + 1) =
      -((if kind = .aiDeriv then airyV (2 * j + 1) else airyU (2 * j + 1) : ℝ) : ℂ) := by
  have h1 : (-1 : ℂ) ^ (2 * j) = 1 := by rw [pow_mul]; norm_num
  have h2 : (-1 : ℂ) ^ (2 * j + 1) = -1 := by rw [pow_succ, h1]; norm_num
  rcases hk with h | h <;> subst h <;> simp [airyExpansionCoeff, h1, h2]

/-- airy ai oscillatory expansion (DLMF 9.7.9). -/
@[dlmf 9.7.E9]
theorem airy_ai_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .ai (-z) - airyOscApprox .ai N M z)
      (airyOscError .ai N M) := by
  have hπ := Real.pi_pos
  have hF := airyRot_airyAi_expansion hδ (by linarith)
  have hE := (airyRot_even_expansion hδ hF) N
  have hO := (airyRot_odd_expansion hδ hF) M
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAi w / airyPrefactor .ai w)
    (O := airyRot_odd fun w => airyAi w / airyPrefactor .ai w)
    (P := airyOscSum false 0 N) (Q := airyOscSum false 1 M)
    (exp (π * I / 4) / 2) (exp (-(π * I / 4)) / 2) ?_ ?_ ?_ ?_
  · refine hE.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_even (d := fun k => ((airyU k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .ai (Or.inl rfl) j).1) N z]
    simp [airyOscSum]
  · refine hO.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_odd (d := fun k => ((airyU k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .ai (Or.inl rfl) j).2) M z]
    simp [airyOscSum]
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .ai (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .ai
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyAi_neg z]
    rw [show airyAi (z * exp ((π / 3 : ℝ) * I)) = airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
        (airyAi (z * exp ((π / 3 : ℝ) * I)) / airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) by
        field_simp,
      show airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
    have ep : exp (π * I / 3) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .ai z * (exp (π * I / 4) / 2 * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, u4, u3]
      field_simp
      rw [hu]; ring_nf
    have em : exp (-π * I / 3) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .ai z * (exp (-(π * I / 4)) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, um4, um3, neg_neg]
      field_simp
      rw [hu]; ring_nf
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox, Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4) * I) =
        exp (-(π * I / 4)) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4) * I) =
        exp (π * I / 4) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

lemma airyRot_exp_third_ofReal :
    exp ((π / 3 : ℝ) * I) = exp (π * I / 3) ∧ exp ((-(π / 3) : ℝ) * I) = exp (-π * I / 3) := by
  constructor <;> (congr 1; push_cast; ring)

/-- `Ai'(-z) = e^{-iπ/3} Ai'(z e^{iπ/3}) + e^{iπ/3} Ai'(z e^{-iπ/3})`. -/
lemma airyRot_airyAiDeriv_neg (z : ℂ) :
    airyAiDeriv (-z) = exp (-π * I / 3) * airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) +
      exp (π * I / 3) * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have h := airyRot_deriv_of_eq (f := fun z => airyAi (-z)) (f' := fun z => -airyAiDeriv (-z))
    (fun z => by simpa [Function.comp_def] using
      (hasDerivAt_airyAi (-z)).comp z (hasDerivAt_id z).neg)
    hasDerivAt_airyAi _ _ _ _ airyRot_airyAi_neg z
  obtain ⟨u4, um4, -, -, -, -, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  rw [k1, k2] at h ⊢
  rw [u4, um4] at h ⊢
  have hu0 : exp (π * I / 12) ≠ 0 := exp_ne_zero _
  have h' : airyAiDeriv (-z) = (-(exp (π * I / 12) ^ 4 * exp (π * I / 12) ^ 4)) *
      airyAiDeriv (z * exp (π * I / 12) ^ 4) + (-((exp (π * I / 12) ^ 4)⁻¹ *
      (exp (π * I / 12) ^ 4)⁻¹)) * airyAiDeriv (z * (exp (π * I / 12) ^ 4)⁻¹) := by
    linear_combination -h
  have e1 : -(exp (π * I / 12) ^ 4 * exp (π * I / 12) ^ 4) = (exp (π * I / 12) ^ 4)⁻¹ := by
    field_simp; linear_combination -u12
  have e2 : -((exp (π * I / 12) ^ 4)⁻¹ * (exp (π * I / 12) ^ 4)⁻¹) = exp (π * I / 12) ^ 4 := by
    field_simp; linear_combination -u12
  rw [h', e1, e2]

/-- `Bi'(-z) = -e^{iπ/6} Ai'(z e^{iπ/3}) - e^{-iπ/6} Ai'(z e^{-iπ/3})`. -/
lemma airyRot_airyBiDeriv_neg (z : ℂ) :
    airyBiDeriv (-z) = -exp (π * I / 6) * airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) +
      -exp (-π * I / 6) * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have h := airyRot_deriv_of_eq (f := fun z => airyBi (-z)) (f' := fun z => -airyBiDeriv (-z))
    (fun z => by simpa [Function.comp_def] using
      (hasDerivAt_airyBi (-z)).comp z (hasDerivAt_id z).neg)
    hasDerivAt_airyAi _ _ _ _ airyRot_airyBi_neg z
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  rw [k1, k2] at h ⊢
  rw [u4, um4, u2, um2] at h ⊢
  have hu0 : exp (π * I / 12) ≠ 0 := exp_ne_zero _
  have e1 : (exp (π * I / 12) ^ 2)⁻¹ * exp (π * I / 12) ^ 4 = exp (π * I / 12) ^ 2 := by
    field_simp
  have e2 : exp (π * I / 12) ^ 2 * (exp (π * I / 12) ^ 4)⁻¹ = (exp (π * I / 12) ^ 2)⁻¹ := by
    field_simp
  rw [e1, e2] at h
  linear_combination -h

/-- airy aiDeriv oscillatory expansion (DLMF 9.7.10). -/
@[dlmf 9.7.E10]
theorem airy_aiDeriv_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .aiDeriv (-z) - airyOscApprox .aiDeriv N M z)
      (airyOscError .aiDeriv N M) := by
  have hπ := Real.pi_pos
  have hF := airyRot_airyAiDeriv_expansion hδ (by linarith)
  have hE := (airyRot_even_expansion hδ hF) N
  have hO := (airyRot_odd_expansion hδ hF) M
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (O := airyRot_odd fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (P := airyOscSum true 0 N) (Q := airyOscSum true 1 M)
    (-(exp (-(π * I / 4)) / 2)) (-(exp (π * I / 4) / 2)) ?_ ?_ ?_ ?_
  · refine hE.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_even (d := fun k => ((airyV k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .aiDeriv (Or.inr rfl) j).1) N z]
    simp [airyOscSum]
  · refine hO.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_odd (d := fun k => ((airyV k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .aiDeriv (Or.inr rfl) j).2) M z]
    simp [airyOscSum]
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyAiDeriv_neg z]
    rw [show airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
        (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) by field_simp,
      show airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
    have ep : exp (-π * I / 3) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .aiDeriv z *
          (-(exp (-(π * I / 4)) / 2) * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, ← hu, um4, um3]
      field_simp
    have em : exp (π * I / 3) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .aiDeriv z * (-(exp (π * I / 4) / 2) * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, ← hu, u4, u3, neg_neg]
      field_simp
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox]
    rw [show cos (airyZetaComplex z - π / 4) = sin (airyZetaComplex z - π / 4 + π / 2) from
        (Complex.sin_add_pi_div_two _).symm,
      show sin (airyZetaComplex z - π / 4) = -cos (airyZetaComplex z - π / 4 + π / 2) by
        rw [Complex.cos_add_pi_div_two]; ring]
    simp only [Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (π * I / 4) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (-(π * I / 4)) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

/-- airy bi oscillatory expansion (DLMF 9.7.11). -/
@[dlmf 9.7.E11]
theorem airy_bi_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .bi (-z) - airyOscApprox .bi N M z)
      (airyOscError .bi N M) := by
  have hπ := Real.pi_pos
  have hF := airyRot_airyAi_expansion hδ (by linarith)
  have hE := (airyRot_even_expansion hδ hF) N
  have hO := (airyRot_odd_expansion hδ hF) M
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAi w / airyPrefactor .ai w)
    (O := airyRot_odd fun w => airyAi w / airyPrefactor .ai w)
    (P := airyOscSum false 0 N) (Q := airyOscSum false 1 M)
    (exp (-(π * I / 4)) / 2) (exp (π * I / 4) / 2) ?_ ?_ ?_ ?_
  · refine hE.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_even (d := fun k => ((airyU k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .ai (Or.inl rfl) j).1) N z]
    simp [airyOscSum]
  · refine hO.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_odd (d := fun k => ((airyU k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .ai (Or.inl rfl) j).2) M z]
    simp [airyOscSum]
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .ai
      (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .ai
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyBi_neg z]
    rw [show airyAi (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
        (airyAi (z * exp ((π / 3 : ℝ) * I)) /
          airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) by field_simp,
      show airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
    have ep : exp (-π * I / 6) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .bi z *
          (exp (-(π * I / 4)) / 2 * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, ← hu, um2, um3]
      field_simp
    have em : exp (π * I / 6) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .bi z * (exp (π * I / 4) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, ← hu, u2, u3, neg_neg]
      field_simp
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox]
    rw [show cos (airyZetaComplex z - π / 4) = sin (airyZetaComplex z - π / 4 + π / 2) from
        (Complex.sin_add_pi_div_two _).symm,
      show sin (airyZetaComplex z - π / 4) = -cos (airyZetaComplex z - π / 4 + π / 2) by
        rw [Complex.cos_add_pi_div_two]; ring]
    simp only [Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (π * I / 4) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4 + π / 2) * I) =
        exp (-(π * I / 4)) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

/-- airy biDeriv oscillatory expansion (DLMF 9.7.12). -/
@[dlmf 9.7.E12]
theorem airy_biDeriv_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .biDeriv (-z) - airyOscApprox .biDeriv N M z)
      (airyOscError .biDeriv N M) := by
  have hπ := Real.pi_pos
  have hF := airyRot_airyAiDeriv_expansion hδ (by linarith)
  have hE := (airyRot_even_expansion hδ hF) N
  have hO := (airyRot_odd_expansion hδ hF) M
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  set u := exp (π * I / 12) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  refine airyRot_osc_bound (E := airyRot_even fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (O := airyRot_odd fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)
    (P := airyOscSum true 0 N) (Q := airyOscSum true 1 M)
    (exp (π * I / 4) / 2) (exp (-(π * I / 4)) / 2) ?_ ?_ ?_ ?_
  · refine hE.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_even (d := fun k => ((airyV k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .aiDeriv (Or.inr rfl) j).1) N z]
    simp [airyOscSum]
  · refine hO.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_odd (d := fun k => ((airyV k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .aiDeriv (Or.inr rfl) j).2) M z]
    simp [airyOscSum]
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    simp only [airyFunction]
    rw [airyRot_airyBiDeriv_neg z]
    rw [show airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
        (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) by field_simp,
      show airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) by field_simp]
    rw [← mul_assoc, ← mul_assoc]
    rw [airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
    have ep : -exp (π * I / 6) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyOscPrefactor .biDeriv z *
          (exp (π * I / 4) / 2 * exp (-(airyZetaComplex z * I))) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d1, d3, ← hu, u2, u3]
      field_simp
    have em : -exp (-π * I / 6) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyOscPrefactor .biDeriv z * (exp (-(π * I / 4)) / 2 * exp (airyZetaComplex z * I)) := by
      simp only [airyPrefactor, airyOscPrefactor]
      rw [d2, d4, ← hu, um2, um3, neg_neg]
      field_simp
    rw [ep, em]
    ring
  · filter_upwards with z
    simp only [airyOscApprox, Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4) * I) =
        exp (-(π * I / 4)) * exp (airyZetaComplex z * I) := by
      rw [← exp_add]; congr 1; ring
    have e2 : exp (-(airyZetaComplex z - π / 4) * I) =
        exp (π * I / 4) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add]; congr 1; ring
    rw [e1, e2]
    ring

lemma airyRot_u_six : exp (π * I / 12) ^ 6 = I := by
  rw [← exp_nat_mul, show ((6 : ℕ) : ℂ) * (π * I / 12) = (π / 2 : ℂ) * I by push_cast; ring,
    exp_pi_div_two_mul_I]

/-- `Bi(z e^{iπ/3}) = i Ai(z e^{iπ/3}) + 2 e^{-iπ/6} Ai(z e^{-iπ/3})`. -/
lemma airyRot_airyBi_rot_pos (z : ℂ) :
    airyBi (z * exp (π * I / 3)) = I * airyAi (z * exp ((π / 3 : ℝ) * I)) +
      2 * exp (-π * I / 6) * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyBi_eq_airyAi_omega,
    show z * exp (π * I / 3) * exp (-(2 * π * I / 3)) = z * exp ((-(π / 3) : ℝ) * I) by
      rw [mul_assoc, ← exp_add]; congr 2; push_cast; ring,
    show z * exp (π * I / 3) * exp (2 * π * I / 3) = -z by
      rw [mul_assoc, ← exp_add, show π * I / 3 + 2 * π * I / 3 = π * I by ring, exp_pi_mul_I]
      ring,
    airyRot_airyAi_neg z]
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  have k : exp (-(π * I / 6)) = exp (-π * I / 6) := by congr 1; ring
  have hu6 := airyRot_u_six
  rw [k, u4, um4, u2, um2]
  set u := exp (π * I / 12)
  set A := airyAi (z * exp ((π / 3 : ℝ) * I))
  set B := airyAi (z * exp ((-(π / 3) : ℝ) * I))
  have hu0 : u ≠ 0 := exp_ne_zero _
  rw [← hu6]
  field_simp
  ring

/-- `Bi(z e^{-iπ/3}) = 2 e^{iπ/6} Ai(z e^{iπ/3}) - i Ai(z e^{-iπ/3})`. -/
lemma airyRot_airyBi_rot_neg (z : ℂ) :
    airyBi (z * exp (-(π * I / 3))) = 2 * exp (π * I / 6) * airyAi (z * exp ((π / 3 : ℝ) * I)) -
      I * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := by
  rw [airyBi_eq_airyAi_omega,
    show z * exp (-(π * I / 3)) * exp (2 * π * I / 3) = z * exp ((π / 3 : ℝ) * I) by
      rw [mul_assoc, ← exp_add]; congr 2; push_cast; ring,
    show z * exp (-(π * I / 3)) * exp (-(2 * π * I / 3)) = -z by
      rw [mul_assoc, ← exp_add, show -(π * I / 3) + -(2 * π * I / 3) = -(π * I) by ring,
        exp_neg, exp_pi_mul_I]
      ring,
    airyRot_airyAi_neg z]
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  have k : exp (-(π * I / 6)) = exp (-π * I / 6) := by congr 1; ring
  have hu6 := airyRot_u_six
  rw [k, u4, um4, u2, um2]
  set u := exp (π * I / 12)
  set A := airyAi (z * exp ((π / 3 : ℝ) * I))
  set B := airyAi (z * exp ((-(π / 3) : ℝ) * I))
  have hu0 : u ≠ 0 := exp_ne_zero _
  rw [← hu6]
  field_simp
  linear_combination B * u12

lemma airyRot_exp_half_log_two : exp ((Real.log 2 : ℂ) / 2) = (Real.sqrt 2 : ℂ) := by
  rw [show (Real.log 2 : ℂ) / 2 = ((Real.log 2 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_exp]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos two_pos]; ring_nf

lemma airyRot_two_div_pi_cpow :
    (2 / π : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) / (Real.sqrt π : ℂ) := by
  rw [show (2 / π : ℂ) = ((2 / π : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_div' _ Real.pi_pos.le]
  push_cast; ring

lemma airyRot_norm_exp_real_mul (ε : ℝ) (c : ℝ) : ‖exp (ε * (c * I))‖ = 1 := by
  rw [show (ε : ℂ) * (c * I) = ((ε * c : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I]

lemma airyRot_norm_two_div_pi_cpow :
    ‖(2 / π : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt 2 / Real.sqrt π := by
  rw [airyRot_two_div_pi_cpow, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- The prefactor of 9.7.13 is `√2` times that of 9.7.11 in norm. -/
lemma airyRot_norm_rot_pref (ε : ℝ) (z : ℂ) :
    ‖(2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ)‖ =
      Real.sqrt 2 * ‖airyOscPrefactor .bi z‖ := by
  rw [show (ε : ℂ) * (π * I / 6) = ε * (((π / 6 : ℝ) : ℂ) * I) by push_cast; ring,
    norm_mul, norm_mul, airyRot_norm_exp_real_mul, airyRot_norm_two_div_pi_cpow,
    show (-1 / 4 : ℂ) = -(1 / 4) by ring, cpow_neg, airyOscPrefactor, norm_div, norm_mul,
    norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  simp only [norm_one]
  ring

/-- The prefactor of 9.7.14 is `√2` times that of 9.7.12 in norm. -/
lemma airyRot_norm_rot_pref' (ε : ℝ) (z : ℂ) :
    ‖(2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ)‖ =
      Real.sqrt 2 * ‖airyOscPrefactor .biDeriv z‖ := by
  rw [show (-ε : ℂ) * (π * I / 6) = ((-ε : ℝ) : ℂ) * (((π / 6 : ℝ) : ℂ) * I) by push_cast; ring,
    norm_mul, norm_mul, airyRot_norm_exp_real_mul, airyRot_norm_two_div_pi_cpow,
    airyOscPrefactor, norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Passing from the `√2`-scaled envelope to `airyOscError`. -/
lemma airyRot_envelope {l : Filter ℂ} (kind : AiryKind) (pref : ℂ → ℂ) (N M : ℕ)
    (h : ∀ z, ‖pref z‖ = Real.sqrt 2 * ‖airyOscPrefactor kind z‖) :
    (fun z => ‖pref z‖ * Real.exp |(airyZetaComplex z).im| *
      (‖airyZetaComplex z‖ ^ (-(2 * N : ℤ)) + ‖airyZetaComplex z‖ ^ (-(2 * M + 1 : ℤ))))
      =O[l] airyOscError kind N M := by
  refine ((isBigO_refl (airyOscError kind N M) l).const_mul_left (Real.sqrt 2)).congr_left
    fun z => ?_
  rw [h, airyOscError]; ring

/-- airyBi rotated expansion (DLMF 9.7.13). -/
@[dlmf 9.7.E13]
theorem airyBi_rotated_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyBi (z * exp (ε * (π * I / 3))) -
        airyRotatedBiApprox false ε N M z) (airyOscError .bi N M) := by
  have hπ := Real.pi_pos
  have hF := airyRot_airyAi_expansion hδ (by linarith)
  have hE := (airyRot_even_expansion hδ hF) N
  have hO := (airyRot_odd_expansion hδ hF) M
  have hE' : (fun z => airyRot_even (fun w => airyAi w / airyPrefactor .ai w) z -
      airyOscSum false 0 N z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * N))⁻¹) := by
    refine hE.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_even (d := fun k => ((airyU k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .ai (Or.inl rfl) j).1) N z]
    simp [airyOscSum]
  have hO' : (fun z => airyRot_odd (fun w => airyAi w / airyPrefactor .ai w) z -
      airyOscSum false 1 M z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * M + 1))⁻¹) := by
    refine hO.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_odd (d := fun k => ((airyU k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .ai (Or.inl rfl) j).2) M z]
    simp [airyOscSum]
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  have hu6 := airyRot_u_six
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hl : exp (-((Real.log 2 : ℂ) / 2)) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [exp_neg, airyRot_exp_half_log_two]
  refine (airyRot_osc_bound (X := fun z => airyBi (z * exp (ε * (π * I / 3))))
    (Y := airyRotatedBiApprox false ε N M)
    (pref := fun z => (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (ε * (π * I / 6)) * z ^ (-1 / 4 : ℂ))
    (exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2)
    (exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) hE' hO' ?_ ?_).trans
    (airyRot_envelope .bi _ N M (airyRot_norm_rot_pref ε))
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .ai (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .ai
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    have split1 : airyAi (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) *
        (airyAi (z * exp ((π / 3 : ℝ) * I)) / airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I))) := by
      field_simp
    have split2 : airyAi (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAi (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I))) := by field_simp
    have hneg : z ^ (-1 / 4 : ℂ) = (z ^ (1 / 4 : ℂ))⁻¹ := by
      rw [show (-1 / 4 : ℂ) = -(1 / 4) by ring, cpow_neg]
    rcases hε with rfl | rfl
    · simp only [ofReal_one, one_mul]
      rw [airyRot_airyBi_rot_pos z, split1, split2, ← mul_assoc, ← mul_assoc,
        airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
      have ep : I * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
          (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (-1 / 4 : ℂ) *
            (exp (π * I / 4) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
              exp (-(airyZetaComplex z * I))) := by
        simp only [airyPrefactor]
        rw [d1, d3, airyRot_two_div_pi_cpow, hl, hneg, u2, u3]
        set u := exp (π * I / 12)
        have hu0 : u ≠ 0 := exp_ne_zero _
        rw [← hu6]
        field_simp
      have em : 2 * exp (-π * I / 6) * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
          (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (-1 / 4 : ℂ) *
            (exp (-(π * I / 4)) * exp ((Real.log 2 : ℂ) / 2) / 2 * exp (airyZetaComplex z * I)) := by
        simp only [airyPrefactor]
        rw [d2, d4, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two, hneg, u2, um2, um3, neg_neg]
        set u := exp (π * I / 12)
        have hu0 : u ≠ 0 := exp_ne_zero _
        field_simp
        linear_combination -hs
      rw [ep, em]
      ring_nf
    · simp only [ofReal_neg, ofReal_one, neg_one_mul]
      rw [airyRot_airyBi_rot_neg z, split1, split2, sub_eq_add_neg, ← neg_mul, ← mul_assoc,
        ← mul_assoc, airyRot_decomp (fun w => airyAi w / airyPrefactor .ai w)]
      have ep : 2 * exp (π * I / 6) * airyPrefactor .ai (z * exp ((π / 3 : ℝ) * I)) =
          (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (-1 / 4 : ℂ) *
            (exp (π * I / 4) * exp ((Real.log 2 : ℂ) / 2) / 2 *
              exp (-(airyZetaComplex z * I))) := by
        simp only [airyPrefactor]
        rw [d1, d3, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two, hneg, u2, u3,
          show -(π * I / 6) = -π * I / 6 by ring, um2]
        set u := exp (π * I / 12)
        have hu0 : u ≠ 0 := exp_ne_zero _
        field_simp
        linear_combination -hs
      have em : -I * airyPrefactor .ai (z * exp ((-(π / 3) : ℝ) * I)) =
          (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (-1 / 4 : ℂ) *
            (exp (-(π * I / 4)) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
              exp (airyZetaComplex z * I)) := by
        simp only [airyPrefactor]
        rw [d2, d4, airyRot_two_div_pi_cpow, hl, hneg, um3,
          show -(π * I / 6) = -π * I / 6 by ring, um2, neg_neg]
        set u := exp (π * I / 12)
        have hu0 : u ≠ 0 := exp_ne_zero _
        rw [← hu6]
        field_simp
        linear_combination -u12
      rw [ep, em]
      ring_nf
  · filter_upwards with z
    simp only [airyRotatedBiApprox, Bool.false_eq_true, ite_false, Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) * I) =
        exp (-(π * I / 4)) * exp ((ε : ℂ) * Real.log 2 / 2) * exp (airyZetaComplex z * I) := by
      rw [← exp_add, ← exp_add]; congr 1
      linear_combination (-(ε : ℂ) * Real.log 2 / 2) * I_sq
    have e2 : exp (-(airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) * I) =
        exp (π * I / 4) * exp (-((ε : ℂ) * Real.log 2 / 2)) * exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add, ← exp_add]; congr 1
      linear_combination ((ε : ℂ) * Real.log 2 / 2) * I_sq
    rw [e1, e2]
    ring

lemma airyRot_hasDerivAt_comp_mul {f f' : ℂ → ℂ} (hf : ∀ z, HasDerivAt f (f' z) z) (c z : ℂ) :
    HasDerivAt (fun z => f (z * c)) (c * f' (z * c)) z := by
  have := (hf (z * c)).comp z ((hasDerivAt_id' z).mul_const c)
  rw [show c * f' (z * c) = f' (z * c) * (1 * c) by ring]
  exact this

/-- `Bi'(z e^{iπ/3}) = i Ai'(z e^{iπ/3}) - 2 e^{iπ/6} Ai'(z e^{-iπ/3})`. -/
lemma airyRot_airyBiDeriv_rot_pos (z : ℂ) :
    airyBiDeriv (z * exp (π * I / 3)) = I * airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) +
      -2 * exp (π * I / 6) * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have h := airyRot_deriv_of_eq (airyRot_hasDerivAt_comp_mul hasDerivAt_airyBi (exp (π * I / 3)))
    hasDerivAt_airyAi _ _ _ _ airyRot_airyBi_rot_pos z
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  have hu6 := airyRot_u_six
  rw [k1, k2] at h ⊢
  simp only [u4, um4, u2, um2] at h ⊢
  set u := exp (π * I / 12)
  set A := airyAiDeriv (z * u ^ 4)
  set B := airyAiDeriv (z * (u ^ 4)⁻¹)
  set X := airyBiDeriv (z * u ^ 4)
  have hu0 : u ≠ 0 := exp_ne_zero _
  apply mul_left_cancel₀ (pow_ne_zero 4 hu0)
  rw [h, ← hu6]
  field_simp
  linear_combination 2 * B * u12

/-- `Bi'(z e^{-iπ/3}) = -2 e^{-iπ/6} Ai'(z e^{iπ/3}) - i Ai'(z e^{-iπ/3})`. -/
lemma airyRot_airyBiDeriv_rot_neg (z : ℂ) :
    airyBiDeriv (z * exp (-(π * I / 3))) = -2 * exp (-π * I / 6) *
      airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) + -I * airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) := by
  have hc : ∀ z, airyBi (z * exp (-(π * I / 3))) = 2 * exp (π * I / 6) *
      airyAi (z * exp ((π / 3 : ℝ) * I)) + -I * airyAi (z * exp ((-(π / 3) : ℝ) * I)) := fun z => by
    rw [airyRot_airyBi_rot_neg]; ring
  have h := airyRot_deriv_of_eq
    (airyRot_hasDerivAt_comp_mul hasDerivAt_airyBi (exp (-(π * I / 3))))
    hasDerivAt_airyAi _ _ _ _ hc z
  obtain ⟨u4, um4, -, -, u2, um2, u12⟩ := airyRot_u_powers
  obtain ⟨k1, k2⟩ := airyRot_exp_third_ofReal
  have hu6 := airyRot_u_six
  have k3 : exp (-(π * I / 3)) = exp (-π * I / 3) := by congr 1; ring
  rw [k1, k2, k3] at h ⊢
  simp only [u4, um4, u2, um2] at h ⊢
  set u := exp (π * I / 12)
  set A := airyAiDeriv (z * u ^ 4)
  set B := airyAiDeriv (z * (u ^ 4)⁻¹)
  set X := airyBiDeriv (z * (u ^ 4)⁻¹)
  have hu0 : u ≠ 0 := exp_ne_zero _
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 4 hu0))
  rw [h, ← hu6]
  field_simp
  linear_combination 2 * A * u12

/-- airyBiDeriv rotated expansion (DLMF 9.7.14). -/
@[dlmf 9.7.E14]
theorem airyBiDeriv_rotated_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) {ε : ℝ}
    (hε : ε = 1 ∨ ε = -1) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyBiDeriv (z * exp (ε * (π * I / 3))) -
        airyRotatedBiApprox true ε N M z) (airyOscError .biDeriv N M) := by
  have hπ := Real.pi_pos
  have hF := airyRot_airyAiDeriv_expansion hδ (by linarith)
  have hE := (airyRot_even_expansion hδ hF) N
  have hO := (airyRot_odd_expansion hδ hF) M
  have hE' : (fun z => airyRot_even (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z -
      airyOscSum true 0 N z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * N))⁻¹) := by
    refine hE.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_even (d := fun k => ((airyV k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .aiDeriv (Or.inr rfl) j).1) N z]
    simp [airyOscSum]
  have hO' : (fun z => airyRot_odd (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w) z -
      airyOscSum true 1 M z) =O[airySector (2 * π / 3 - δ)]
      (fun z => ((airyZetaComplex z) ^ (2 * M + 1))⁻¹) := by
    refine hO.congr_left fun z => ?_
    dsimp only
    rw [airyRot_sum_odd (d := fun k => ((airyV k : ℝ) : ℂ)) _
      (fun j => by simpa using (airyRot_coeff_parity .aiDeriv (Or.inr rfl) j).2) M z]
    simp [airyOscSum]
  obtain ⟨u4, um4, u3, um3, u2, um2, u12⟩ := airyRot_u_powers
  have hu6 := airyRot_u_six
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hs0 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
  have hπs : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hl : exp (-((Real.log 2 : ℂ) / 2)) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
    rw [exp_neg, airyRot_exp_half_log_two]
  refine (airyRot_osc_bound (X := fun z => airyBiDeriv (z * exp (ε * (π * I / 3))))
    (Y := airyRotatedBiApprox true ε N M)
    (pref := fun z => (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-ε * (π * I / 6)) * z ^ (1 / 4 : ℂ))
    (exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) / 2)
    (exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) / 2) hE' hO' ?_ ?_).trans
    (airyRot_envelope .biDeriv _ N M (airyRot_norm_rot_pref' ε))
  · filter_upwards [airyRot_eventually_arg (2 * π / 3 - δ)] with z hz
    have hz0 := hz.1
    have hz3 : |arg z| < 2 * π / 3 := hz.2.trans_lt (by linarith)
    obtain ⟨d1, d2, d3, d4⟩ := airyRot_third_data hz0 hz3
    have hq : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz0)
    have hp1 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((π / 3 : ℝ) * I)))
    have hp2 := airyRot_prefactor_ne_zero .aiDeriv
      (mul_ne_zero hz0 (exp_ne_zero ((-(π / 3) : ℝ) * I)))
    have split1 : airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) *
        (airyAiDeriv (z * exp ((π / 3 : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I))) := by
      field_simp
    have split2 : airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
        airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) *
        (airyAiDeriv (z * exp ((-(π / 3) : ℝ) * I)) /
          airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I))) := by field_simp
    rcases hε with rfl | rfl
    · simp only [ofReal_one, one_mul, neg_one_mul]
      rw [airyRot_airyBiDeriv_rot_pos z, split1, split2, ← mul_assoc, ← mul_assoc,
        airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
      have ep : I * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
          (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (1 / 4 : ℂ) *
            (exp (-(π * I / 4)) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
              exp (-(airyZetaComplex z * I))) := by
        simp only [airyPrefactor]
        rw [d1, d3, airyRot_two_div_pi_cpow, hl, show -(π * I / 6) = -π * I / 6 by ring,
          um2, um3]
        set u := exp (π * I / 12)
        have hu0 : u ≠ 0 := exp_ne_zero _
        rw [← hu6]
        field_simp
        linear_combination -u12
      have em : -2 * exp (π * I / 6) * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
          (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (-(π * I / 6)) * z ^ (1 / 4 : ℂ) *
            (exp (π * I / 4) * exp ((Real.log 2 : ℂ) / 2) / 2 * exp (airyZetaComplex z * I)) := by
        simp only [airyPrefactor]
        rw [d2, d4, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two,
          show -(π * I / 6) = -π * I / 6 by ring, u2, um2, u3, neg_neg]
        set u := exp (π * I / 12)
        have hu0 : u ≠ 0 := exp_ne_zero _
        field_simp
        linear_combination -hs
      rw [ep, em]
      ring_nf
    · simp only [ofReal_neg, ofReal_one, neg_one_mul, neg_neg, one_mul]
      rw [airyRot_airyBiDeriv_rot_neg z, split1, split2, ← mul_assoc,
        ← mul_assoc, airyRot_decomp (fun w => airyAiDeriv w / airyPrefactor .aiDeriv w)]
      have ep : -2 * exp (-π * I / 6) * airyPrefactor .aiDeriv (z * exp ((π / 3 : ℝ) * I)) =
          (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (1 / 4 : ℂ) *
            (exp (-(π * I / 4)) * exp ((Real.log 2 : ℂ) / 2) / 2 *
              exp (-(airyZetaComplex z * I))) := by
        simp only [airyPrefactor]
        rw [d1, d3, airyRot_two_div_pi_cpow, airyRot_exp_half_log_two, u2, um2, um3]
        set u := exp (π * I / 12)
        have hu0 : u ≠ 0 := exp_ne_zero _
        field_simp
        linear_combination -hs
      have em : -I * airyPrefactor .aiDeriv (z * exp ((-(π / 3) : ℝ) * I)) =
          (2 / π : ℂ) ^ (1 / 2 : ℂ) * exp (π * I / 6) * z ^ (1 / 4 : ℂ) *
            (exp (π * I / 4) * exp (-((Real.log 2 : ℂ) / 2)) / 2 *
              exp (airyZetaComplex z * I)) := by
        simp only [airyPrefactor]
        rw [d2, d4, airyRot_two_div_pi_cpow, hl, u3, u2, neg_neg]
        set u := exp (π * I / 12)
        have hu0 : u ≠ 0 := exp_ne_zero _
        rw [← hu6]
        field_simp
      rw [ep, em]
      ring_nf
  · filter_upwards with z
    simp only [airyRotatedBiApprox, ↓reduceIte]
    rw [show cos (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) =
          sin (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) from
        (Complex.sin_add_pi_div_two _).symm,
      show sin (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2) =
          -cos (airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) by
        rw [Complex.cos_add_pi_div_two]; ring]
    simp only [Complex.cos, Complex.sin]
    have e1 : exp ((airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) * I) =
        exp (π * I / 4) * exp ((ε : ℂ) * Real.log 2 / 2) * exp (airyZetaComplex z * I) := by
      rw [← exp_add, ← exp_add]; congr 1
      linear_combination (-(ε : ℂ) * Real.log 2 / 2) * I_sq
    have e2 : exp (-(airyZetaComplex z - π / 4 - ε * I * Real.log 2 / 2 + π / 2) * I) =
        exp (-(π * I / 4)) * exp (-((ε : ℂ) * Real.log 2 / 2)) *
          exp (-(airyZetaComplex z * I)) := by
      rw [← exp_add, ← exp_add]; congr 1
      linear_combination ((ε : ℂ) * Real.log 2 / 2) * I_sq
    rw [e1, e2]
    ring

lemma airyRot_eventually_prefactor_ne_zero (kind : AiryKind) (α : ℝ) :
    ∀ᶠ z in airySector α, airyPrefactor kind z ≠ 0 :=
  (airyRot_eventually_ne_zero α).mono fun _ hz => airyRot_prefactor_ne_zero kind hz

/-- airy ai poincare (DLMF 9.7.5). -/
@[dlmf 9.7.E5]
theorem airy_ai_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (N : ℕ) :
    IsBigO (airySector (π - δ)) (fun z => airyFunction .ai z -
      airyPrefactor .ai z * airyExponentialSum .ai N z)
      (fun z => airyPrefactor .ai z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyAi_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .ai _) N

/-- airy aiDeriv poincare (DLMF 9.7.6). -/
@[dlmf 9.7.E6]
theorem airy_aiDeriv_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (N : ℕ) :
    IsBigO (airySector (π - δ)) (fun z => airyFunction .aiDeriv z -
      airyPrefactor .aiDeriv z * airyExponentialSum .aiDeriv N z)
      (fun z => airyPrefactor .aiDeriv z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyAiDeriv_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .aiDeriv _) N

/-- airy bi poincare (DLMF 9.7.7). -/
@[dlmf 9.7.E7]
theorem airy_bi_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (airySector (π / 3 - δ)) (fun z => airyFunction .bi z -
      airyPrefactor .bi z * airyExponentialSum .bi N z)
      (fun z => airyPrefactor .bi z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyBi_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .bi _) N

/-- airy biDeriv poincare (DLMF 9.7.8). -/
@[dlmf 9.7.E8]
theorem airy_biDeriv_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (airySector (π / 3 - δ)) (fun z => airyFunction .biDeriv z -
      airyPrefactor .biDeriv z * airyExponentialSum .biDeriv N z)
      (fun z => airyPrefactor .biDeriv z / airyZetaComplex z ^ N) :=
  airyRot_isBigO_of_expansion (airyRot_airyBiDeriv_expansion hδ hδ')
    (airyRot_eventually_prefactor_ne_zero .biDeriv _) N

/-! ### Real-axis error bounds (DLMF §9.7(iii), 9.7.15)

On the positive axis the normalized `Ai` and `Ai'` are Laplace integrals
`(2ζ)^a Γ(a)⁻¹ ∫₀^∞ e^{-2ζr} r^{a-1} (1+r)^β dr` with `(a, β) = (5/6, -1/6)`, `(7/6, 1/6)`.
The binomial remainder of `(1+r)^β` after `N ≥ β` terms lies between `0` and the first
neglected term, which gives the classical enveloping property of the expansions.
-/

/-! ### Binomial remainders -/

/-- The remainder of the binomial series of `(1 + t)^β` after `N` terms. -/
def airyReal_rho (β : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  (1 + t) ^ β - ∑ n ∈ Finset.range N, Ring.choose β n * t ^ n

lemma airyReal_choose_succ (β : ℝ) (m : ℕ) :
    ((m : ℝ) + 1) * Ring.choose β (m + 1) = β * Ring.choose (β - 1) m := by
  have h := Ring.choose_smul_choose β (n := m + 1) (k := 1) (by omega)
  simp only [Nat.choose_one_right, Ring.choose_one_right, Nat.cast_one, Nat.add_sub_cancel,
    nsmul_eq_mul] at h
  rw [← h]; push_cast; ring

lemma airyReal_hasDerivAt_rho (β : ℝ) (N : ℕ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (airyReal_rho β (N + 1)) (β * airyReal_rho (β - 1) N t) t := by
  have hfun : airyReal_rho β (N + 1) = fun t => (1 + t) ^ β -
      (∑ m ∈ Finset.range N, Ring.choose β (m + 1) * t ^ (m + 1) + Ring.choose β 0) := by
    funext t; rw [airyReal_rho, Finset.sum_range_succ', pow_zero, mul_one]
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => (1 + t) ^ β) (1 * β * (1 + t) ^ (β - 1)) t :=
    ((hasDerivAt_id t).const_add 1).rpow_const (Or.inl (by simp; linarith))
  have h2 : HasDerivAt (fun t : ℝ => ∑ m ∈ Finset.range N, Ring.choose β (m + 1) * t ^ (m + 1))
      (∑ m ∈ Finset.range N, Ring.choose β (m + 1) * (((m + 1 : ℕ) : ℝ) * t ^ m)) t := by
    have := HasDerivAt.fun_sum (u := Finset.range N)
      (A := fun m (t : ℝ) => Ring.choose β (m + 1) * t ^ (m + 1))
      (A' := fun m => Ring.choose β (m + 1) * (((m + 1 : ℕ) : ℝ) * t ^ m)) (x := t)
      (fun m _ => by
        have := (hasDerivAt_pow (m + 1) t).const_mul (Ring.choose β (m + 1))
        simpa using this)
    simpa using this
  refine (h1.fun_sub (h2.add_const _)).congr_deriv ?_
  rw [airyReal_rho, mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun m _ => ?_
    have := airyReal_choose_succ β m
    push_cast
    linear_combination t ^ m * this

/-- A function vanishing at `0` with nonnegative derivative on `[0, ∞)` is nonnegative there. -/
lemma airyReal_nonneg_of_deriv {φ g : ℝ → ℝ} (hφ : ∀ t, 0 ≤ t → HasDerivAt φ (g t) t)
    (h0 : φ 0 = 0) (hg : ∀ t, 0 ≤ t → 0 ≤ g t) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ φ t := by
  have hmono : MonotoneOn φ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x hx => (hφ x hx).continuousAt.continuousWithinAt)
      (fun x hx => by
        rw [interior_Ici] at hx
        exact (hφ x (le_of_lt hx)).differentiableAt.differentiableWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    rw [(hφ x (le_of_lt hx)).deriv]
    exact hg x (le_of_lt hx)
  have := hmono (mem_Ici.mpr (le_refl (0 : ℝ))) (mem_Ici.mpr ht) ht
  rwa [h0] at this

/-- **Binomial remainder bound**: for `β ≤ N` and `t ≥ 0` the remainder lies between `0` and
the first neglected term `binom(β, N) t^N`. -/
lemma airyReal_rho_btw (N : ℕ) : ∀ β : ℝ, β ≤ N → ∀ t : ℝ, 0 ≤ t →
    0 ≤ airyReal_rho β N t * (Ring.choose β N * t ^ N - airyReal_rho β N t) := by
  induction N with
  | zero =>
    intro β hβ t ht
    simp only [airyReal_rho, Finset.range_zero, Finset.sum_empty, sub_zero, Ring.choose_zero_right,
      pow_zero, one_mul]
    have h1 : 0 ≤ (1 + t) ^ β := Real.rpow_nonneg (by linarith) _
    have h2 : (1 + t) ^ β ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simpa using hβ)
    nlinarith
  | succ N ih =>
    intro β hβ t ht
    have hih : ∀ s, 0 ≤ s → 0 ≤ (β * airyReal_rho (β - 1) N s) *
        (β * Ring.choose (β - 1) N * s ^ N - β * airyReal_rho (β - 1) N s) := by
      intro s hs
      have := ih (β - 1) (by push_cast at hβ; linarith) s hs
      nlinarith [sq_nonneg β]
    have hd : ∀ s, 0 ≤ s → HasDerivAt (airyReal_rho β (N + 1)) (β * airyReal_rho (β - 1) N s) s :=
      fun s hs => airyReal_hasDerivAt_rho β N (by linarith)
    have hB : ∀ s : ℝ, HasDerivAt (fun s => Ring.choose β (N + 1) * s ^ (N + 1))
        (β * Ring.choose (β - 1) N * s ^ N) s := fun s => by
      have := (hasDerivAt_pow (N + 1) s).const_mul (Ring.choose β (N + 1))
      refine this.congr_deriv ?_
      have := airyReal_choose_succ β N
      push_cast
      linear_combination s ^ N * this
    have h00 : airyReal_rho β (N + 1) 0 = 0 := by
      simp [airyReal_rho, Finset.sum_range_succ']
    set c := Ring.choose β (N + 1)
    rcases le_total 0 c with hc | hc
    · have hcN : ∀ s, 0 ≤ s → 0 ≤ β * Ring.choose (β - 1) N * s ^ N := fun s hs => by
        rw [← airyReal_choose_succ]; positivity
      have hg : ∀ s, 0 ≤ s → 0 ≤ β * airyReal_rho (β - 1) N s ∧
          β * airyReal_rho (β - 1) N s ≤ β * Ring.choose (β - 1) N * s ^ N := fun s hs => by
        have h1 := hih s hs; have h2 := hcN s hs
        constructor <;> nlinarith
      have p1 := airyReal_nonneg_of_deriv hd h00 (fun s hs => (hg s hs).1) ht
      have p2 := airyReal_nonneg_of_deriv (φ := fun s => c * s ^ (N + 1) - airyReal_rho β (N + 1) s)
        (fun s hs => (hB s).sub (hd s hs)) (by simp [h00]) (fun s hs => by
          have := (hg s hs).2; linarith) ht
      exact mul_nonneg p1 p2
    · have hcN : ∀ s, 0 ≤ s → β * Ring.choose (β - 1) N * s ^ N ≤ 0 := fun s hs => by
        rw [← airyReal_choose_succ, mul_assoc]
        exact mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (mul_nonpos_of_nonpos_of_nonneg hc (by positivity))
      have hg : ∀ s, 0 ≤ s → β * airyReal_rho (β - 1) N s ≤ 0 ∧
          β * Ring.choose (β - 1) N * s ^ N ≤ β * airyReal_rho (β - 1) N s := fun s hs => by
        have h1 := hih s hs; have h2 := hcN s hs
        constructor <;> nlinarith
      have p1 := airyReal_nonneg_of_deriv (φ := fun s => -airyReal_rho β (N + 1) s)
        (fun s hs => (hd s hs).neg) (by simp [h00]) (fun s hs => by
          have := (hg s hs).1; linarith) ht
      have p2 := airyReal_nonneg_of_deriv (φ := fun s => airyReal_rho β (N + 1) s - c * s ^ (N + 1))
        (fun s hs => (hd s hs).sub (hB s)) (by simp [h00]) (fun s hs => by
          have := (hg s hs).2; linarith) ht
      have := mul_nonneg p1 p2
      linarith

/-- The moments `∫₀^∞ e^{-sr} r^{a-1} r^n dr = Γ(a+n) s^{-(a+n)}`. -/
lemma airyReal_moment {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (n : ℕ) :
    IntegrableOn (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * r ^ n) (Ioi 0) ∧
    ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * r ^ n =
      Real.Gamma (a + n) * s ^ (-(a + n)) := by
  have heq : EqOn (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * r ^ n)
      (fun r : ℝ => r ^ (a - 1 + n) * Real.exp (-s * r ^ (1 : ℝ))) (Ioi 0) := by
    intro r hr
    simp only [Real.rpow_one]
    rw [Real.rpow_add hr, Real.rpow_natCast]; ring_nf
  have hq : -1 < a - 1 + n := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  refine ⟨(integrableOn_rpow_mul_exp_neg_mul_rpow hq one_pos hs).congr_fun heq.symm
    measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    _root_.integral_rpow_mul_exp_neg_mul_rpow one_pos hq hs]
  rw [show (a - 1 + n + 1) / 1 = a + n by ring, show -(a - 1 + n + 1) / 1 = -(a + n) by ring]
  ring

lemma airyReal_sq_le_of_btw {p q : ℝ} (h : 0 ≤ p * (q - p)) : |p| ≤ |q| :=
  sq_le_sq.mp (by nlinarith [sq_nonneg (q - p)])

/-- **Integrated binomial remainder**: the Laplace transform of the remainder lies between `0`
and that of the first neglected term. -/
lemma airyReal_integral_btw {a s β : ℝ} (ha : 0 < a) (hs : 0 < s) {N : ℕ} (hβ : β ≤ N) :
    IntegrableOn (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r) (Ioi 0) ∧
    0 ≤ (∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r) *
      (Ring.choose β N * (Real.Gamma (a + N) * s ^ (-(a + N))) -
        ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r) := by
  obtain ⟨hmi, hmv⟩ := airyReal_moment ha hs N
  set c := Ring.choose β N
  have hw : ∀ r : ℝ, 0 < r → 0 ≤ Real.exp (-(s * r)) * r ^ (a - 1) := fun r hr =>
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hr.le _)
  have hb : ∀ r : ℝ, 0 < r → 0 ≤ airyReal_rho β N r * (c * r ^ N - airyReal_rho β N r) :=
    fun r hr => airyReal_rho_btw N β hβ r hr.le
  have hmeas : AEStronglyMeasurable
      (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r)
      (volume.restrict (Ioi 0)) := by
    refine Measurable.aestronglyMeasurable ?_
    unfold airyReal_rho
    fun_prop
  have hint : IntegrableOn (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r)
      (Ioi 0) := by
    refine Integrable.mono' (hmi.const_mul |c|) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have h1 := airyReal_sq_le_of_btw (hb r hr)
    have h2 := hw r hr
    rw [abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt (mem_Ioi.mp hr)) N)] at h1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h2]
    calc Real.exp (-(s * r)) * r ^ (a - 1) * |airyReal_rho β N r|
        ≤ Real.exp (-(s * r)) * r ^ (a - 1) * (|c| * r ^ N) := by
          gcongr
      _ = |c| * (Real.exp (-(s * r)) * r ^ (a - 1) * r ^ N) := by ring
  refine ⟨hint, ?_⟩
  have hM : ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * (c * r ^ N) =
      c * (Real.Gamma (a + N) * s ^ (-(a + N))) := by
    rw [← hmv, ← integral_const_mul]
    congr 1; funext r; ring
  rw [← hM]
  have hMi : IntegrableOn (fun r : ℝ => Real.exp (-(s * r)) * r ^ (a - 1) * (c * r ^ N)) (Ioi 0) :=
    IntegrableOn.congr_fun (hmi.const_mul c) (fun r _ => by ring) measurableSet_Ioi
  rcases le_total 0 c with hc | hc
  · have hlo : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r :=
      fun r hr => by
        have := hb r hr; have := hw r hr
        have hcr : 0 ≤ c * r ^ N := mul_nonneg hc (pow_nonneg (le_of_lt (mem_Ioi.mp hr)) N)
        have : 0 ≤ airyReal_rho β N r := by nlinarith
        positivity
    have hhi : ∀ r ∈ Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r ≤
        Real.exp (-(s * r)) * r ^ (a - 1) * (c * r ^ N) := fun r hr => by
      have := hb r hr; have h2 := hw r hr
      have hcr : 0 ≤ c * r ^ N := mul_nonneg hc (pow_nonneg (le_of_lt (mem_Ioi.mp hr)) N)
      have : airyReal_rho β N r ≤ c * r ^ N := by nlinarith
      exact mul_le_mul_of_nonneg_left this h2
    have h1 := setIntegral_nonneg (μ := volume) measurableSet_Ioi hlo
    have h2 := setIntegral_mono_on hint hMi measurableSet_Ioi hhi
    exact mul_nonneg h1 (by linarith)
  · have hlo : ∀ r ∈ Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r ≤ 0 :=
      fun r hr => by
        have := hb r hr; have h2 := hw r hr
        have hcr : c * r ^ N ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg (le_of_lt (mem_Ioi.mp hr)) N)
        have : airyReal_rho β N r ≤ 0 := by nlinarith
        exact mul_nonpos_of_nonneg_of_nonpos h2 this
    have hhi : ∀ r ∈ Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * (c * r ^ N) ≤
        Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r := fun r hr => by
      have := hb r hr; have h2 := hw r hr
      have hcr : c * r ^ N ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg (le_of_lt (mem_Ioi.mp hr)) N)
      have : c * r ^ N ≤ airyReal_rho β N r := by nlinarith
      exact mul_le_mul_of_nonneg_left this h2
    have h1 := setIntegral_nonpos (μ := volume) measurableSet_Ioi hlo
    have h2 := setIntegral_mono_on hMi hint measurableSet_Ioi hhi
    exact mul_nonneg_of_nonpos_of_nonpos h1 (by linarith)

/-- The Laplace integral of the full kernel splits into the remainder and the moments. -/
lemma airyReal_split {a s β : ℝ} (ha : 0 < a) (hs : 0 < s) (N : ℕ) (hβ : β ≤ N) :
    ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * (r ^ (a - 1) * (1 + r) ^ β) =
      (∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r) +
      ∑ n ∈ Finset.range N, Ring.choose β n * (Real.Gamma (a + n) * s ^ (-(a + n))) := by
  have hint := (airyReal_integral_btw ha hs hβ).1
  have heq : ∀ r : ℝ, Real.exp (-(s * r)) * (r ^ (a - 1) * (1 + r) ^ β) =
      Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r +
        ∑ n ∈ Finset.range N, Ring.choose β n * (Real.exp (-(s * r)) * r ^ (a - 1) * r ^ n) := by
    intro r
    simp only [airyReal_rho]
    rw [mul_sub, Finset.mul_sum]
    have : ∀ n ∈ Finset.range N, Real.exp (-(s * r)) * r ^ (a - 1) * (Ring.choose β n * r ^ n) =
        Ring.choose β n * (Real.exp (-(s * r)) * r ^ (a - 1) * r ^ n) := fun n _ => by ring
    rw [Finset.sum_congr rfl this]
    ring
  simp_rw [heq]
  rw [integral_add hint, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, (airyReal_moment ha hs n).2]
  · intro n _
    exact ((airyReal_moment ha hs n).1.const_mul (Ring.choose β n))
  · exact integrable_finsetSum _ fun n _ => (airyReal_moment ha hs n).1.const_mul _

/-- One term of the expansion as a real number. -/
lemma airyReal_term {a s β : ℝ} (ha : 0 < a) (hs : 0 < s) (n : ℕ) (Z : ℂ) (hZ : 2 * Z = s) :
    1 / Gamma ((a : ℝ) : ℂ) * (Gamma ((n : ℂ) + ((a : ℝ) : ℂ)) * Ring.choose ((β : ℝ) : ℂ) n) /
      2 ^ n / Z ^ n =
    ((s ^ a / Real.Gamma a * (Ring.choose β n * (Real.Gamma (a + n) * s ^ (-(a + n)))) : ℝ) :
      ℂ) := by
  have hZ' : Z = ((s / 2 : ℝ) : ℂ) := by push_cast; linear_combination hZ / 2
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hs0 : s ≠ 0 := hs.ne'
  rw [hZ', show (n : ℂ) + ((a : ℝ) : ℂ) = ((n + a : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofRealHom_eq_coe β,
    ← Ring.map_choose, Complex.ofRealHom_eq_coe]
  have hpow : s ^ a * s ^ (-(a + n)) = (s ^ n)⁻¹ := by
    rw [← Real.rpow_add hs, show a + -(a + n) = -(n : ℝ) by ring, Real.rpow_neg hs.le,
      Real.rpow_natCast]
  rw [show (1 : ℂ) / (Real.Gamma a : ℂ) * (((Real.Gamma (n + a) : ℝ) : ℂ) *
      ((Ring.choose β n : ℝ) : ℂ)) / 2 ^ n / ((s / 2 : ℝ) : ℂ) ^ n =
      ((1 / Real.Gamma a * (Real.Gamma (n + a) * Ring.choose β n) / 2 ^ n / (s / 2) ^ n : ℝ) : ℂ)
      by push_cast; ring]
  congr 1
  rw [show s ^ a / Real.Gamma a * (Ring.choose β n * (Real.Gamma (a + n) * s ^ (-(a + n)))) =
      Ring.choose β n * Real.Gamma (a + n) * (s ^ a * s ^ (-(a + n))) / Real.Gamma a by ring,
    hpow, add_comm (n : ℝ) a, div_pow]
  field_simp

/-- The exact normalized remainder as a real Laplace integral of the binomial remainder. -/
lemma airyReal_remainder {a s β : ℝ} (ha : 0 < a) (hs : 0 < s) (N : ℕ) (hβ : β ≤ N) (Z : ℂ)
    (hZ : 2 * Z = s) :
    (((s ^ a / Real.Gamma a *
        ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * (r ^ (a - 1) * (1 + r) ^ β) : ℝ)) : ℂ) -
      ∑ n ∈ Finset.range N, 1 / Gamma ((a : ℝ) : ℂ) *
        (Gamma ((n : ℂ) + ((a : ℝ) : ℂ)) * Ring.choose ((β : ℝ) : ℂ) n) / 2 ^ n / Z ^ n =
    ((s ^ a / Real.Gamma a *
      ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r : ℝ) : ℂ) := by
  rw [airyReal_split ha hs N hβ, mul_add, ofReal_add, add_sub_assoc, add_eq_left, sub_eq_zero,
    Finset.mul_sum, ofReal_sum]
  exact Finset.sum_congr rfl fun n _ => (airyReal_term ha hs n Z hZ).symm

/-! ### The real axis -/

lemma airyReal_zeta_ofReal {x : ℝ} (hx : 0 < x) :
    airyZetaComplex (x : ℂ) = ((airyZeta x : ℝ) : ℂ) := by
  rw [airyZetaComplex, airyZeta, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← ofReal_cpow hx.le]
  push_cast; ring

lemma airyReal_log_two_add {x : ℝ} (hx : 0 < x) :
    log 2 + airyLogZeta x = ((Real.log (2 * airyZeta x) : ℝ) : ℂ) := by
  have h2 : log (2 : ℂ) = ((Real.log 2 : ℝ) : ℂ) := by
    rw [ofReal_log (by norm_num)]; norm_num
  have h23 : log (2 / 3 : ℂ) = ((Real.log (2 / 3) : ℝ) : ℂ) := by
    rw [ofReal_log (by norm_num)]; push_cast; ring_nf
  have hxl : log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := (ofReal_log hx.le).symm
  rw [airyLogZeta, h2, h23, hxl, airyZeta, Real.log_mul (by norm_num) (by positivity),
    Real.log_mul (by norm_num) (by positivity), Real.log_rpow hx]
  push_cast; ring

lemma airyReal_exp_mul {x : ℝ} (hx : 0 < x) (a : ℝ) :
    exp ((a : ℂ) * (log 2 + airyLogZeta x)) = (((2 * airyZeta x) ^ a : ℝ) : ℂ) := by
  have hs : 0 < 2 * airyZeta x := by have := airyZeta_pos hx; linarith
  rw [airyReal_log_two_add hx, ← ofReal_mul, ← ofReal_exp, Real.rpow_def_of_pos hs, mul_comm]

lemma airyReal_integral_ofReal {x : ℝ} (hx : 0 < x) (a β : ℝ) :
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(2 * airyZetaComplex x * t)) * airyRot_kernel a β t =
      ((∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) * (r ^ (a - 1) * (1 + r) ^ β) : ℝ)
        : ℂ) := by
  rw [← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr0 : 0 ≤ r := le_of_lt hr
  simp only [airyRot_kernel, airyReal_zeta_ofReal hx]
  rw [ofReal_mul, ofReal_mul, ofReal_exp, ofReal_cpow hr0, ofReal_cpow (by linarith : 0 ≤ 1 + r)]
  push_cast; ring_nf

/-- The real Laplace representation of the normalized `Ai` on the positive axis. -/
lemma airyReal_ai_repr {x : ℝ} (hx : 0 < x) :
    airyAi x / airyPrefactor .ai x =
      ((((2 * airyZeta x) ^ (5 / 6 : ℝ) / Real.Gamma (5 / 6) *
        ∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) *
          (r ^ ((5 / 6 : ℝ) - 1) * (1 + r) ^ (-1 / 6 : ℝ))) : ℝ) : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hG : Gamma ((5 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hE : exp (airyZetaComplex x) * exp (-airyZetaComplex x) = 1 := by
    rw [← exp_add]; simp
  have hc := airyRot_exp_combine hx0 (-1 / 6) (2 / 3) (1 / 4) (5 / 6) (by ring)
  have hc' : 2 * (3 : ℂ) ^ (-1 / 6 : ℂ) * exp (2 / 3 * airyLogZeta x) * (x : ℂ) ^ (1 / 4 : ℂ) =
      exp (((5 / 6 : ℝ) : ℂ) * (log 2 + airyLogZeta x)) := by
    have h1 : exp (-((5 / 6 : ℂ) * (log 2 + airyLogZeta x))) *
        exp ((5 / 6 : ℂ) * (log 2 + airyLogZeta x)) = 1 := by rw [← exp_add]; simp
    push_cast
    linear_combination exp ((5 / 6 : ℂ) * (log 2 + airyLogZeta x)) * hc -
      (2 * (3 : ℂ) ^ (-1 / 6 : ℂ) * exp (2 / 3 * airyLogZeta x) * (x : ℂ) ^ (1 / 4 : ℂ)) * h1
  rw [airyRot_airyAi_anchor hx0 harg, airyReal_integral_ofReal hx, ofReal_mul,
    ofReal_div ((2 * airyZeta x) ^ (5 / 6 : ℝ)) (Real.Gamma (5 / 6)),
    ← airyReal_exp_mul hx, ← hc', ← Complex.Gamma_ofReal]
  simp only [airyPrefactor]
  rw [exp_sub]
  generalize ((∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) *
    (r ^ ((5 / 6 : ℝ) - 1) * (1 + r) ^ (-1 / 6 : ℝ)) : ℝ) : ℂ) = K
  field_simp
  linear_combination (-K) * hE

/-- The real Laplace representation of the normalized `Ai'` on the positive axis. -/
lemma airyReal_aiDeriv_repr {x : ℝ} (hx : 0 < x) :
    airyAiDeriv x / airyPrefactor .aiDeriv x =
      ((((2 * airyZeta x) ^ (7 / 6 : ℝ) / Real.Gamma (7 / 6) *
        ∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) *
          (r ^ ((7 / 6 : ℝ) - 1) * (1 + r) ^ (1 / 6 : ℝ))) : ℝ) : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x : ℂ)| < π / 3 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  have hG : Gamma ((7 / 6 : ℝ) : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp)
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hq : (x : ℂ) ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hqq : (x : ℂ) ^ (-1 / 4 : ℂ) * (x : ℂ) ^ (1 / 4 : ℂ) = 1 := by
    rw [← cpow_add _ _ hx0]; norm_num
  have hE : exp (airyZetaComplex x) * exp (-airyZetaComplex x) = 1 := by
    rw [← exp_add]; simp
  have hc := airyRot_exp_combine hx0 (1 / 6) (4 / 3) (-1 / 4) (7 / 6) (by ring)
  have hc' : 2 * (3 : ℂ) ^ (1 / 6 : ℂ) * exp (4 / 3 * airyLogZeta x) * (x : ℂ) ^ (-1 / 4 : ℂ) =
      exp (((7 / 6 : ℝ) : ℂ) * (log 2 + airyLogZeta x)) := by
    have h1 : exp (-((7 / 6 : ℂ) * (log 2 + airyLogZeta x))) *
        exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta x)) = 1 := by rw [← exp_add]; simp
    push_cast
    linear_combination exp ((7 / 6 : ℂ) * (log 2 + airyLogZeta x)) * hc -
      (2 * (3 : ℂ) ^ (1 / 6 : ℂ) * exp (4 / 3 * airyLogZeta x) * (x : ℂ) ^ (-1 / 4 : ℂ)) * h1
  rw [airyRot_airyAiDeriv_anchor hx0 harg, airyReal_integral_ofReal hx, ofReal_mul,
    ofReal_div ((2 * airyZeta x) ^ (7 / 6 : ℝ)) (Real.Gamma (7 / 6)),
    ← airyReal_exp_mul hx, ← hc', ← Complex.Gamma_ofReal]
  simp only [airyPrefactor]
  rw [exp_sub]
  generalize ((∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) *
    (r ^ ((7 / 6 : ℝ) - 1) * (1 + r) ^ (1 / 6 : ℝ)) : ℝ) : ℂ) = K
  field_simp
  have hqq' : (x : ℂ) ^ (-(1 / 4) : ℂ) * (x : ℂ) ^ (1 / 4 : ℂ) = 1 := by
    rw [← cpow_add _ _ hx0]; norm_num
  linear_combination (-K * (x : ℂ) ^ (1 / 4 : ℂ) * (x : ℂ) ^ (-(1 / 4) : ℂ)) * hE + (-K) * hqq'

/-- Packaged form: remainder and first neglected term on the positive axis. -/
lemma airyReal_pack {a β : ℝ} (ha : 0 < a) {N : ℕ} (hβ : β ≤ N) {x : ℝ} (hx : 0 < x)
    {f : ℂ → ℂ} (hf : f x = ((((2 * airyZeta x) ^ a / Real.Gamma a *
        ∫ r in Ioi (0 : ℝ), Real.exp (-(2 * airyZeta x * r)) * (r ^ (a - 1) * (1 + r) ^ β)) : ℝ)
          : ℂ))
    {c : ℕ → ℂ} (hc : ∀ n : ℕ, 1 / Gamma ((a : ℝ) : ℂ) *
      (Gamma ((n : ℂ) + ((a : ℝ) : ℂ)) * Ring.choose ((β : ℝ) : ℂ) n) / 2 ^ n = c n) :
    ‖f x - ∑ k ∈ Finset.range N, c k / airyZetaComplex x ^ k‖ ≤ ‖c N / airyZetaComplex x ^ N‖ ∧
      0 ≤ (f x - ∑ k ∈ Finset.range N, c k / airyZetaComplex x ^ k).re * (c N).re := by
  have hs : 0 < 2 * airyZeta x := by have := airyZeta_pos hx; linarith
  have hZ : 2 * airyZetaComplex x = ((2 * airyZeta x : ℝ) : ℂ) := by
    rw [airyReal_zeta_ofReal hx]; push_cast; ring
  set s := 2 * airyZeta x
  have hR := airyReal_remainder ha hs N hβ _ hZ
  simp only [hc] at hR
  have hT := airyReal_term (β := β) ha hs N _ hZ
  rw [hc] at hT
  rw [hf, hR, hT]
  obtain ⟨-, hb⟩ := airyReal_integral_btw (β := β) ha hs hβ
  set J := ∫ r in Ioi (0 : ℝ), Real.exp (-(s * r)) * r ^ (a - 1) * airyReal_rho β N r
  set M := Ring.choose β N * (Real.Gamma (a + N) * s ^ (-(a + N)))
  have hC : 0 < s ^ a / Real.Gamma a := div_pos (Real.rpow_pos_of_pos hs _) (Real.Gamma_pos_of_pos ha)
  set C := s ^ a / Real.Gamma a
  have hb' : 0 ≤ (C * J) * (C * M - C * J) := by
    have : (C * J) * (C * M - C * J) = C ^ 2 * (J * (M - J)) := by ring
    rw [this]; positivity
  refine ⟨?_, ?_⟩
  · rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    exact airyReal_sq_le_of_btw hb'
  · have hcN : c N = ((C * M * airyZeta x ^ N : ℝ) : ℂ) := by
      have hz0 : airyZetaComplex x ^ N ≠ 0 := by
        rw [airyReal_zeta_ofReal hx]; exact pow_ne_zero _ (ofReal_ne_zero.mpr (airyZeta_pos hx).ne')
      have : c N = c N / airyZetaComplex x ^ N * airyZetaComplex x ^ N := by field_simp
      rw [this, hT, airyReal_zeta_ofReal hx]; push_cast; ring
    rw [hcN, ofReal_re, ofReal_re]
    have hz := pow_pos (airyZeta_pos hx) N
    have : C * J * (C * M * airyZeta x ^ N) = (C * J * (C * M - C * J) + (C * J) ^ 2) *
      airyZeta x ^ N := by ring
    rw [this]; positivity

lemma airyReal_norm_prefactor_ai {x : ℝ} (hx : 0 < x) :
    ‖airyPrefactor .ai x‖ = Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)) := by
  have hq : ‖(x : ℂ) ^ (1 / 4 : ℂ)‖ = x ^ (1 / 4 : ℝ) := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx.le,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [airyPrefactor, norm_div, norm_mul, norm_mul, hq, Complex.norm_exp, neg_re,
    airyReal_zeta_ofReal hx, ofReal_re, Complex.norm_real, Complex.norm_two,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

lemma airyReal_norm_prefactor_aiDeriv {x : ℝ} (hx : 0 < x) :
    ‖airyPrefactor .aiDeriv x‖ = x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) / (2 * Real.sqrt π) := by
  have hq : ‖(x : ℂ) ^ (1 / 4 : ℂ)‖ = x ^ (1 / 4 : ℝ) := by
    rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by push_cast; ring, ← ofReal_cpow hx.le,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [airyPrefactor, norm_div, norm_mul, norm_neg, norm_mul, hq, Complex.norm_exp, neg_re,
    airyReal_zeta_ofReal hx, ofReal_re, Complex.norm_real, Complex.norm_two,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]

lemma airyReal_airyU_zero : airyU 0 = 1 := by simp [airyU]
lemma airyReal_airyU_one : airyU 1 = 5 / 72 := by
  simp [airyU, ascPochhammer_one]; norm_num
lemma airyReal_airyV_zero : airyV 0 = 1 := by simp [airyV, airyReal_airyU_zero]
lemma airyReal_airyV_one : airyV 1 = -7 / 72 := by
  rw [airyV, airyReal_airyU_one]; norm_num

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_ai_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 0 ≤ N) :
    ‖airyRemainder .ai N x‖ ≤ 
      ‖airyExpansionCoeff .ai N / airyZetaComplex x ^ N‖ ∧
      0 ≤ (airyRemainder .ai N x).re * (airyExpansionCoeff .ai N).re :=
  airyReal_pack (a := 5 / 6) (β := -1 / 6) (by norm_num)
    (by have := (Nat.cast_nonneg N : (0 : ℝ) ≤ N); linarith) hx
    (f := fun z => airyAi z / airyPrefactor .ai z) (airyReal_ai_repr hx) airyRot_coeff_ai

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_aiDeriv_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N x‖ ≤ 
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex x ^ N‖ ∧
      0 ≤ (airyRemainder .aiDeriv N x).re * (airyExpansionCoeff .aiDeriv N).re :=
  airyReal_pack (a := 7 / 6) (β := 1 / 6) (by norm_num)
    (by have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith) hx
    (f := fun z => airyAiDeriv z / airyPrefactor .aiDeriv z) (airyReal_aiDeriv_repr hx)
    airyRot_coeff_aiDeriv

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_bi_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 0 ≤ N) :
    ‖airyRemainder .bi N x‖ ≤ (airyChi (N + 1 / 6) + 1) * 
      ‖airyExpansionCoeff .bi N / airyZetaComplex x ^ N‖ := by
  sorry

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_biDeriv_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .biDeriv N x‖ ≤ (airyChi (N + 0) + 1) * 
      ‖airyExpansionCoeff .biDeriv N / airyZetaComplex x ^ N‖ := by
  sorry

/-- airy ai bound (DLMF 9.7.15). -/
@[dlmf 9.7.E15]
theorem airy_ai_bound {x : ℝ} (hx : 0 < x) :
    airyAiReal x ≤ Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)) := by
  have h := (airyReal_pack (a := 5 / 6) (β := -1 / 6) (N := 0) (by norm_num) (by norm_num) hx
    (f := fun z => airyAi z / airyPrefactor .ai z) (airyReal_ai_repr hx) airyRot_coeff_ai).1
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one,
    airyExpansionCoeff, airyReal_airyU_zero, ofReal_one, mul_one, norm_one] at h
  have hp : airyPrefactor .ai x ≠ 0 :=
    airyRot_prefactor_ne_zero .ai (ofReal_ne_zero.mpr hx.ne')
  calc airyAiReal x ≤ ‖airyAi x‖ := Complex.re_le_norm _
    _ = ‖airyPrefactor .ai x‖ * ‖airyAi x / airyPrefactor .ai x‖ := by
      rw [← norm_mul, mul_div_cancel₀ _ hp]
    _ ≤ ‖airyPrefactor .ai x‖ * 1 := by gcongr
    _ = _ := by rw [mul_one, airyReal_norm_prefactor_ai hx]

/-- airy aiDeriv bound (DLMF 9.7.15). -/
@[dlmf 9.7.E15]
theorem airy_aiDeriv_bound {x : ℝ} (hx : 0 < x) :
    |airyAiDerivReal x| ≤ x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) / (2 * Real.sqrt π) * (1 + 7 / (72 * airyZeta x)) := by
  have h := (airyReal_pack (a := 7 / 6) (β := 1 / 6) (N := 1) (by norm_num) (by norm_num) hx
    (f := fun z => airyAiDeriv z / airyPrefactor .aiDeriv z) (airyReal_aiDeriv_repr hx)
    airyRot_coeff_aiDeriv).1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, div_one, pow_one,
    airyExpansionCoeff, airyReal_airyV_zero, airyReal_airyV_one, ofReal_one, mul_one] at h
  have hp : airyPrefactor .aiDeriv x ≠ 0 :=
    airyRot_prefactor_ne_zero .aiDeriv (ofReal_ne_zero.mpr hx.ne')
  have hz := airyZeta_pos hx
  have h1 : ‖airyAiDeriv x / airyPrefactor .aiDeriv x‖ ≤ 1 + 7 / (72 * airyZeta x) := by
    have h2 : ‖(-1 : ℂ) * ((-7 / 72 : ℝ) : ℂ) / airyZetaComplex x‖ = 7 / (72 * airyZeta x) := by
      have hz0 : (airyZeta x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz.ne'
      rw [airyReal_zeta_ofReal hx, show (-1 : ℂ) * ((-7 / 72 : ℝ) : ℂ) / ((airyZeta x : ℝ) : ℂ) =
        ((7 / (72 * airyZeta x) : ℝ) : ℂ) by push_cast; field_simp,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h2] at h
    calc ‖airyAiDeriv x / airyPrefactor .aiDeriv x‖
        = ‖(airyAiDeriv x / airyPrefactor .aiDeriv x - 1) + 1‖ := by ring_nf
      _ ≤ ‖airyAiDeriv x / airyPrefactor .aiDeriv x - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 7 / (72 * airyZeta x) + 1 := by rw [norm_one]; gcongr
      _ = _ := by ring
  calc |airyAiDerivReal x| ≤ ‖airyAiDeriv x‖ := Complex.abs_re_le_norm _
    _ = ‖airyPrefactor .aiDeriv x‖ * ‖airyAiDeriv x / airyPrefactor .aiDeriv x‖ := by
      rw [← norm_mul, mul_div_cancel₀ _ hp]
    _ ≤ ‖airyPrefactor .aiDeriv x‖ * (1 + 7 / (72 * airyZeta x)) := by gcongr
    _ = _ := by rw [airyReal_norm_prefactor_aiDeriv hx]

/-- airy bi bound (DLMF 9.7.16). -/
@[dlmf 9.7.E16]
theorem airy_bi_bound {x : ℝ} (hx : 0 < x) :
    airyBiReal x ≤ Real.exp (airyZeta x) / (Real.sqrt π * x ^ (1 / 4 : ℝ)) * (1 + (airyChi (7 / 6) + 1) * 5 / (72 * airyZeta x)) := by
  sorry

/-- airy biDeriv bound (DLMF 9.7.16). -/
@[dlmf 9.7.E16]
theorem airy_biDeriv_bound {x : ℝ} (hx : 0 < x) :
    airyBiDerivReal x ≤ x ^ (1 / 4 : ℝ) * Real.exp (airyZeta x) / Real.sqrt π * (1 + (π / 2 + 1) * 7 / (72 * airyZeta x)) := by
  sorry

/-- airy ai complex error (DLMF 9.7.17). -/
@[dlmf 9.7.E17]
theorem airy_ai_complex_error {z : ℂ} (hz : z ∈ slitPlane) {N : ℕ} (hN : 0 ≤ N) :
    ‖airyRemainder .ai N z‖ ≤ airyErrorMultiplier N (1 / 6) z *
      ‖airyExpansionCoeff .ai N / airyZetaComplex z ^ N‖ := by
  sorry

/-- airy aiDeriv complex error (DLMF 9.7.17). -/
@[dlmf 9.7.E17]
theorem airy_aiDeriv_complex_error {z : ℂ} (hz : z ∈ slitPlane) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N z‖ ≤ airyErrorMultiplier N (0) z *
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex z ^ N‖ := by
  sorry

/-- airy ai exact remainder (DLMF 9.7.18). -/
@[dlmf 9.7.E18]
theorem airy_ai_exact_remainder {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    airyFunction .ai z = airyPrefactor .ai z *
      (airyExponentialSum .ai N z + airyRemainder .ai N z) := by
  have hp : airyPrefactor .ai z ≠ 0 := by
    dsimp only [airyPrefactor]
    have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hz' : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
    exact div_ne_zero (exp_ne_zero _) (mul_ne_zero (mul_ne_zero two_ne_zero hπ) hz')
  unfold airyRemainder
  field_simp
  ring

/-- airy aiDeriv exact remainder (DLMF 9.7.19). -/
@[dlmf 9.7.E19]
theorem airy_aiDeriv_exact_remainder {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    airyFunction .aiDeriv z = airyPrefactor .aiDeriv z *
      (airyExponentialSum .aiDeriv N z + airyRemainder .aiDeriv N z) := by
  have hp : airyPrefactor .aiDeriv z ≠ 0 := by
    dsimp only [airyPrefactor]
    have hπ : (Real.sqrt π : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hz' : z ^ (1 / 4 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hz)
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hz') (exp_ne_zero _)) (mul_ne_zero two_ne_zero hπ)
  unfold airyRemainder
  field_simp
  ring

/-- airy R hyper reexpansion (DLMF 9.7.20). -/
@[dlmf 9.7.E20]
theorem airy_R_hyper_reexpansion (m n : ℕ) (z : ℂ) :
    airyRemainder .ai n z =
      (-1 : ℂ) ^ (n) *
        (∑ k ∈ Finset.range m, (-1 : ℂ) ^ k * (airyU k : ℂ) *
          airyTerminator ((n : ℂ) - k) (log 2 + airyLogZeta z) / airyZetaComplex z ^ k) +
      airyHyperRemainder false m n z := by
  norm_num [airyHyperRemainder] <;> ring

/-- airy S hyper reexpansion (DLMF 9.7.21). -/
@[dlmf 9.7.E21]
theorem airy_S_hyper_reexpansion (m n : ℕ) (z : ℂ) :
    airyRemainder .aiDeriv n z =
      (-1 : ℂ) ^ (n - 1) *
        (∑ k ∈ Finset.range m, (-1 : ℂ) ^ k * (airyV k : ℂ) *
          airyTerminator ((n : ℂ) - k) (log 2 + airyLogZeta z) / airyZetaComplex z ^ k) +
      airyHyperRemainder true m n z := by
  norm_num [airyHyperRemainder] <;> ring

/-- airy R hyper error (DLMF 9.7.23). -/
@[dlmf 9.7.E23]
theorem airy_R_hyper_error (m : ℕ) :
    IsBigO (airySector (2 * π / 3)) (fun z => airyHyperRemainder false m (airyOptimalIndex z) z)
      (fun z => Real.exp (-2 * ‖airyZetaComplex z‖) * ‖airyZetaComplex z‖ ^ (-(m : ℤ))) := by
  sorry

/-- airy S hyper error (DLMF 9.7.23). -/
@[dlmf 9.7.E23]
theorem airy_S_hyper_error (m : ℕ) :
    IsBigO (airySector (2 * π / 3)) (fun z => airyHyperRemainder true m (airyOptimalIndex z) z)
      (fun z => Real.exp (-2 * ‖airyZetaComplex z‖) * ‖airyZetaComplex z‖ ^ (-(m : ℤ))) := by
  sorry

/-- The exact even/odd coefficients obtained by inverting the real sine/cosine system. -/
def airyOscComponent (derivative : Bool) (parity : Fin 2) (x : ℝ) : ℂ :=
  let θ : ℂ := airyZeta x - π / 4
  let pref := airyOscPrefactor (if derivative then .aiDeriv else .ai) x
  if derivative then
    if parity.val = 0 then (sin θ * airyAiDeriv (-x) + cos θ * airyBiDeriv (-x)) / pref
    else (-cos θ * airyAiDeriv (-x) + sin θ * airyBiDeriv (-x)) / pref
  else
    if parity.val = 0 then (cos θ * airyAi (-x) - sin θ * airyBi (-x)) / pref
    else (sin θ * airyAi (-x) + cos θ * airyBi (-x)) / pref

/-- The signed first-neglected-term bound for each real oscillatory subseries, 9.7(iii).
The hypothesis explicitly retains the source's condition on the following term. -/
theorem airy_oscillatory_real_error (derivative : Bool) (parity : Fin 2)
    {x : ℝ} (hx : 0 < x) (N : ℕ)
    (hopposite : ((-1 : ℝ) ^ N * (if derivative then airyV (2 * N + parity.val) else airyU (2 * N + parity.val))) *
      ((-1 : ℝ) ^ (N + 1) * (if derivative then airyV (2 * (N + 1) + parity.val) else airyU (2 * (N + 1) + parity.val))) < 0) :
    ‖airyOscComponent derivative parity x - airyOscSum derivative parity.val N x‖ ≤
      ‖(-1 : ℂ) ^ N * (if derivative then airyV (2 * N + parity.val) else airyU (2 * N + parity.val)) /
        airyZetaComplex x ^ (2 * N + parity.val)‖ ∧
    0 ≤ (airyOscComponent derivative parity x - airyOscSum derivative parity.val N x).re *
      ((-1 : ℝ) ^ N * (if derivative then airyV (2 * N + parity.val) else airyU (2 * N + parity.val))) := by
  sorry

/-! ### Exact values of χ at integers -/

/-- The two-step recurrence `χ(x+2) = χ(x) (x+2)/(x+1)` for `x ≥ 0`. -/
lemma airyChi_add_two {x : ℝ} (hx : 0 ≤ x) :
    airyChi (x + 2) = airyChi x * ((x + 2) / (x + 1)) := by
  have h1 : (x + 2) / 2 + 1 = (x / 2 + 1) + 1 := by ring
  have h2 : (x + 2) / 2 + 1 / 2 = (x / 2 + 1 / 2) + 1 := by ring
  have hp1 : 0 < x / 2 + 1 := by positivity
  have hp2 : 0 < x / 2 + 1 / 2 := by positivity
  have hG := (Real.Gamma_pos_of_pos hp2).ne'
  rw [airyChi, airyChi, h1, h2, Real.Gamma_add_one hp1.ne', Real.Gamma_add_one hp2.ne']
  have : x + 1 ≠ 0 := by positivity
  field_simp

/-- `χ(0) = 1`. -/
lemma airyChi_zero : airyChi 0 = 1 := by
  rw [airyChi]; norm_num [Real.Gamma_one_half_eq]
  exact (Real.sqrt_pos.mpr Real.pi_pos).ne'

/-- `χ(1) = π/2`. -/
lemma airyChi_one : airyChi 1 = π / 2 := by
  rw [airyChi, show (1 : ℝ) / 2 + 1 = 1 / 2 + 1 by ring, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq, show (1 : ℝ) / 2 + 1 / 2 = 1 by ring, Real.Gamma_one]
  rw [show Real.sqrt π * (1 / 2 * Real.sqrt π) = (Real.sqrt π) ^ 2 / 2 by ring,
    Real.sq_sqrt Real.pi_pos.le]
  ring

/-- `χ(2m) = ∏_{j<m} (2j+2)/(2j+1)`. -/
lemma airyChi_two_mul (m : ℕ) :
    airyChi (2 * m) = ∏ j ∈ Finset.range m, ((2 * j + 2 : ℝ) / (2 * j + 1)) := by
  induction m with
  | zero => simpa using airyChi_zero
  | succ m ih =>
    rw [Finset.prod_range_succ, ← ih, show (2 * ((m + 1 : ℕ) : ℝ)) = 2 * m + 2 by push_cast; ring,
      airyChi_add_two (by positivity)]

/-- `χ(2m+1) = (π/2) ∏_{j<m} (2j+3)/(2j+2)`. -/
lemma airyChi_two_mul_add_one (m : ℕ) :
    airyChi (2 * m + 1) = π / 2 * ∏ j ∈ Finset.range m, ((2 * j + 3 : ℝ) / (2 * j + 2)) := by
  induction m with
  | zero => simpa using airyChi_one
  | succ m ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ← ih,
      show (2 * ((m + 1 : ℕ) : ℝ)) + 1 = (2 * m + 1) + 2 by push_cast; ring,
      airyChi_add_two (by positivity)]
    congr 1; ring_nf

end DLMF.Airy
