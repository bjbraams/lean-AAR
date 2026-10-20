/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Framework

/-!
# Airy asymptotic expansions and error bounds, DLMF §9.7

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

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
  have h := (AAR.Gamma.Gamma_ratio_power (a := 1) (b := 1 / 2)).comp
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

/-- airy ai poincare (DLMF 9.7.5). -/
@[dlmf 9.7.E5]
theorem airy_ai_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (N : ℕ) :
    IsBigO (airySector (π - δ)) (fun z => airyFunction .ai z -
      airyPrefactor .ai z * airyExponentialSum .ai N z)
      (fun z => airyPrefactor .ai z / airyZetaComplex z ^ N) := by
  sorry

/-- airy aiDeriv poincare (DLMF 9.7.6). -/
@[dlmf 9.7.E6]
theorem airy_aiDeriv_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (N : ℕ) :
    IsBigO (airySector (π - δ)) (fun z => airyFunction .aiDeriv z -
      airyPrefactor .aiDeriv z * airyExponentialSum .aiDeriv N z)
      (fun z => airyPrefactor .aiDeriv z / airyZetaComplex z ^ N) := by
  sorry

/-- airy bi poincare (DLMF 9.7.7). -/
@[dlmf 9.7.E7]
theorem airy_bi_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (airySector (π / 3 - δ)) (fun z => airyFunction .bi z -
      airyPrefactor .bi z * airyExponentialSum .bi N z)
      (fun z => airyPrefactor .bi z / airyZetaComplex z ^ N) := by
  sorry

/-- airy biDeriv poincare (DLMF 9.7.8). -/
@[dlmf 9.7.E8]
theorem airy_biDeriv_poincare {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (airySector (π / 3 - δ)) (fun z => airyFunction .biDeriv z -
      airyPrefactor .biDeriv z * airyExponentialSum .biDeriv N z)
      (fun z => airyPrefactor .biDeriv z / airyZetaComplex z ^ N) := by
  sorry

/-- airy ai oscillatory expansion (DLMF 9.7.9). -/
@[dlmf 9.7.E9]
theorem airy_ai_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .ai (-z) - airyOscApprox .ai N M z)
      (airyOscError .ai N M) := by
  sorry

/-- airy aiDeriv oscillatory expansion (DLMF 9.7.10). -/
@[dlmf 9.7.E10]
theorem airy_aiDeriv_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .aiDeriv (-z) - airyOscApprox .aiDeriv N M z)
      (airyOscError .aiDeriv N M) := by
  sorry

/-- airy bi oscillatory expansion (DLMF 9.7.11). -/
@[dlmf 9.7.E11]
theorem airy_bi_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .bi (-z) - airyOscApprox .bi N M z)
      (airyOscError .bi N M) := by
  sorry

/-- airy biDeriv oscillatory expansion (DLMF 9.7.12). -/
@[dlmf 9.7.E12]
theorem airy_biDeriv_oscillatory_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyFunction .biDeriv (-z) - airyOscApprox .biDeriv N M z)
      (airyOscError .biDeriv N M) := by
  sorry

/-- airyBi rotated expansion (DLMF 9.7.13). -/
@[dlmf 9.7.E13]
theorem airyBi_rotated_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyBi (z * exp (ε * (π * I / 3))) -
        airyRotatedBiApprox false ε N M z) (airyOscError .bi N M) := by
  sorry

/-- airyBiDeriv rotated expansion (DLMF 9.7.14). -/
@[dlmf 9.7.E14]
theorem airyBiDeriv_rotated_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (N M : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => airyBiDeriv (z * exp (ε * (π * I / 3))) -
        airyRotatedBiApprox true ε N M z) (airyOscError .biDeriv N M) := by
  sorry

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_ai_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 0 ≤ N) :
    ‖airyRemainder .ai N x‖ ≤ 
      ‖airyExpansionCoeff .ai N / airyZetaComplex x ^ N‖ ∧
      0 ≤ (airyRemainder .ai N x).re * (airyExpansionCoeff .ai N).re := by
  sorry

/-- First-neglected-term remainder bound and its sign, DLMF §9.7(iii). -/
theorem airy_aiDeriv_real_error {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : 1 ≤ N) :
    ‖airyRemainder .aiDeriv N x‖ ≤ 
      ‖airyExpansionCoeff .aiDeriv N / airyZetaComplex x ^ N‖ ∧
      0 ≤ (airyRemainder .aiDeriv N x).re * (airyExpansionCoeff .aiDeriv N).re := by
  sorry

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
  sorry

/-- airy aiDeriv bound (DLMF 9.7.15). -/
@[dlmf 9.7.E15]
theorem airy_aiDeriv_bound {x : ℝ} (hx : 0 < x) :
    |airyAiDerivReal x| ≤ x ^ (1 / 4 : ℝ) * Real.exp (-airyZeta x) / (2 * Real.sqrt π) * (1 + 7 / (72 * airyZeta x)) := by
  sorry

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

end AAR.Airy
