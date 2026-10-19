/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.ModulusPhase

/-!
# Airy zeros and their common asymptotic coefficients, DLMF §9.9

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- The k-th negative real zero, ordered from zero towards negative infinity (k≥1). -/
def airyRealZero (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x < 0 ∧ f x = 0 ∧
    ({y : ℝ | x < y ∧ y < 0 ∧ f y = 0} : Set ℝ).ncard = k - 1)
/-- Negative zeros of Ai. -/
def airyAiZero : ℕ → ℝ := airyRealZero airyAiReal
/-- Negative zeros of Ai'. -/
def airyAiDerivZero : ℕ → ℝ := airyRealZero airyAiDerivReal
/-- Negative zeros of Bi. -/
def airyBiZero : ℕ → ℝ := airyRealZero airyBiReal
/-- Negative zeros of Bi'. -/
def airyBiDerivZero : ℕ → ℝ := airyRealZero airyBiDerivReal
/-- Zeros in the upper complex-zero sector of Bi or Bi'. -/
def airyUpperZeroSet (f : ℂ → ℂ) : Set ℂ := {z | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}
/-- Complex zeros ordered by increasing modulus; the specification theorem establishes existence. -/
def airyComplexZero (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon (fun z : ℂ => z ∈ airyUpperZeroSet f ∧
    ({w : ℂ | w ∈ airyUpperZeroSet f ∧ ‖w‖ < ‖z‖} : Set ℂ).ncard = k - 1)
/-- Upper-half-plane complex zeros of Bi. -/
def airyBiComplexZero : ℕ → ℂ := airyComplexZero airyBi
/-- Upper-half-plane complex zeros of Bi'. -/
def airyBiDerivComplexZero : ℕ → ℂ := airyComplexZero airyBiDeriv
/-- The continuous extension of the Ai zero index, via the unwrapped phase. -/
def airyAiZeroContinuous (k : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x ≤ 0 ∧ airyPhase x = k * π)
/-- The continuous extension of the Ai' zero index. -/
def airyAiDerivZeroContinuous (k : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x ≤ 0 ∧ airyDerivPhase x = (k - 1) * π)
/-- An all-order expansion in the common inverse even-power scale used in 9.9.18–9.9.21. -/
def HasAiryZeroExpansion (q : ℝ) (f t : ℕ → ℂ) (c : ℕ → ℂ) : Prop :=
  HasAsymptoticExpansion atTop (fun n k => t k ^ (-2 * (n : ℂ))) c
    (fun k => f k / t k ^ (q : ℂ))
/-- The real argument of the T,V pair at the (k+1)-st Ai zero. -/
def airyZeroArgument (offset : ℝ) (k : ℕ) : ℂ := (3 * π / 8 * (4 * (k + 1 : ℝ) - offset) : ℝ)
/-- The complex argument of the T,V and U,W pairs for Bi's upper-sector zeros. -/
def airyComplexZeroArgument (offset : ℝ) (k : ℕ) : ℂ := airyZeroArgument offset k + 3 * I * Real.log 2 / 4

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyAi_real_zeros_negative {x : ℝ} (hx : airyAiReal x = 0) :
    x < 0 := by
  by_contra hn
  obtain ⟨r, hr, he⟩ := airyAi_ofReal_pos (not_lt.mp hn)
  have hx' : (airyAi x).re = 0 := hx
  rw [he] at hx'
  simp only [ofReal_re] at hx'
  linarith

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyAi_infinite_real_zeros  :
    Set.Infinite {x : ℝ | airyAiReal x = 0} := by
  sorry

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyAiZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyAiZero k < 0 ∧ airyAiReal (airyAiZero k) = 0 ∧
      ({y : ℝ | airyAiZero k < y ∧ y < 0 ∧ airyAiReal y = 0} : Set ℝ).ncard = k - 1 := by
  sorry

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyAiZero_enumeration  :
    StrictAntiOn airyAiZero (Ici 1) ∧ ∀ x : ℝ, airyAiReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyAiZero k = x := by
  sorry

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyAiDeriv_real_zeros_negative {x : ℝ} (hx : airyAiDerivReal x = 0) :
    x < 0 := by
  sorry

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyAiDeriv_infinite_real_zeros  :
    Set.Infinite {x : ℝ | airyAiDerivReal x = 0} := by
  sorry

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyAiDerivZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyAiDerivZero k < 0 ∧ airyAiDerivReal (airyAiDerivZero k) = 0 ∧
      ({y : ℝ | airyAiDerivZero k < y ∧ y < 0 ∧ airyAiDerivReal y = 0} : Set ℝ).ncard = k - 1 := by
  sorry

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyAiDerivZero_enumeration  :
    StrictAntiOn airyAiDerivZero (Ici 1) ∧ ∀ x : ℝ, airyAiDerivReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyAiDerivZero k = x := by
  sorry

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyBi_real_zeros_negative {x : ℝ} (hx : airyBiReal x = 0) :
    x < 0 := by
  by_contra hn
  obtain ⟨r, hr, he⟩ := airyBi_ofReal_pos (not_lt.mp hn)
  have hx' : (airyBi x).re = 0 := hx
  rw [he] at hx'
  simp only [ofReal_re] at hx'
  linarith

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyBi_infinite_real_zeros  :
    Set.Infinite {x : ℝ | airyBiReal x = 0} := by
  sorry

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyBiZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiZero k < 0 ∧ airyBiReal (airyBiZero k) = 0 ∧
      ({y : ℝ | airyBiZero k < y ∧ y < 0 ∧ airyBiReal y = 0} : Set ℝ).ncard = k - 1 := by
  sorry

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyBiZero_enumeration  :
    StrictAntiOn airyBiZero (Ici 1) ∧ ∀ x : ℝ, airyBiReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyBiZero k = x := by
  sorry

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyBiDeriv_real_zeros_negative {x : ℝ} (hx : airyBiDerivReal x = 0) :
    x < 0 := by
  sorry

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyBiDeriv_infinite_real_zeros  :
    Set.Infinite {x : ℝ | airyBiDerivReal x = 0} := by
  sorry

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyBiDerivZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiDerivZero k < 0 ∧ airyBiDerivReal (airyBiDerivZero k) = 0 ∧
      ({y : ℝ | airyBiDerivZero k < y ∧ y < 0 ∧ airyBiDerivReal y = 0} : Set ℝ).ncard = k - 1 := by
  sorry

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyBiDerivZero_enumeration  :
    StrictAntiOn airyBiDerivZero (Ici 1) ∧ ∀ x : ℝ, airyBiDerivReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyBiDerivZero k = x := by
  sorry

/-- Ai and Ai' have no nonreal zeros, DLMF §9.9(i). -/
theorem airyAi_complex_zeros_real {z : ℂ} (hz : airyAi z = 0) :
    z.im = 0 ∧ z.re < 0 := by
  sorry

/-- Ai and Ai' have no nonreal zeros, DLMF §9.9(i). -/
theorem airyAiDeriv_complex_zeros_real {z : ℂ} (hz : airyAiDeriv z = 0) :
    z.im = 0 ∧ z.re < 0 := by
  sorry

/-- The nonreal-zero sectors of Bi and Bi', DLMF §9.9(i). -/
theorem airyBi_complex_zeros_sector {z : ℂ} (hz : airyBi z = 0) (him : z.im ≠ 0) :
    π / 3 < |arg z| ∧ |arg z| < π / 2 := by
  sorry

/-- Infinitely many zeros in the upper sector, DLMF §9.9(i). -/
theorem airyBi_infinite_complex_zeros  :
    Set.Infinite (airyUpperZeroSet airyBi) := by
  sorry

/-- The upper-sector complex-zero specification, DLMF §9.9(i). -/
theorem airyBiComplexZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiComplexZero k ∈ airyUpperZeroSet airyBi := by
  sorry

/-- Complex-zero enumeration in increasing modulus, DLMF §9.9(i). -/
theorem airyBiComplexZero_enumeration  :
    StrictMonoOn (fun k => ‖airyBiComplexZero k‖) (Ici 1) ∧
      ∀ z ∈ airyUpperZeroSet airyBi, ∃ k : ℕ, 1 ≤ k ∧ airyBiComplexZero k = z := by
  sorry

/-- The nonreal-zero sectors of Bi and Bi', DLMF §9.9(i). -/
theorem airyBiDeriv_complex_zeros_sector {z : ℂ} (hz : airyBiDeriv z = 0) (him : z.im ≠ 0) :
    π / 3 < |arg z| ∧ |arg z| < π / 2 := by
  sorry

/-- Infinitely many zeros in the upper sector, DLMF §9.9(i). -/
theorem airyBiDeriv_infinite_complex_zeros  :
    Set.Infinite (airyUpperZeroSet airyBiDeriv) := by
  sorry

/-- The upper-sector complex-zero specification, DLMF §9.9(i). -/
theorem airyBiDerivComplexZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiDerivComplexZero k ∈ airyUpperZeroSet airyBiDeriv := by
  sorry

/-- Complex-zero enumeration in increasing modulus, DLMF §9.9(i). -/
theorem airyBiDerivComplexZero_enumeration  :
    StrictMonoOn (fun k => ‖airyBiDerivComplexZero k‖) (Ici 1) ∧
      ∀ z ∈ airyUpperZeroSet airyBiDeriv, ∃ k : ℕ, 1 ≤ k ∧ airyBiDerivComplexZero k = z := by
  sorry

/-- airyAiZero phase (DLMF 9.9.1). -/
@[dlmf 9.9.E1]
theorem airyAiZero_phase {k : ℕ} (hk : 1 ≤ k) :
    airyPhase (airyAiZero k) = k * π ∧ airyDerivPhase (airyAiDerivZero (k + 1)) = k * π := by
  sorry

/-- airyBiZero phase (DLMF 9.9.2). -/
@[dlmf 9.9.E2]
theorem airyBiZero_phase {k : ℕ} (hk : 1 ≤ k) :
    airyPhase (airyBiZero k) = ((k : ℝ) - 1 / 2) * π ∧
      airyDerivPhase (airyBiDerivZero k) = ((k : ℝ) - 1 / 2) * π := by
  sorry

/-- airyAiZero value (DLMF 9.9.3). -/
@[dlmf 9.9.E3]
theorem airyAiZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyAiDeriv (airyAiZero k) = (-1 : ℂ) ^ (k - 1) / (π * airyModulus (airyAiZero k)) := by
  sorry

/-- airyBiZero value (DLMF 9.9.3). -/
@[dlmf 9.9.E3]
theorem airyBiZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyBiDeriv (airyBiZero k) = (-1 : ℂ) ^ (k - 1) / (π * airyModulus (airyBiZero k)) := by
  sorry

/-- airyAiDerivZero value (DLMF 9.9.4). -/
@[dlmf 9.9.E4]
theorem airyAiDerivZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyAi (airyAiDerivZero k) = (-1 : ℂ) ^ (k - 1) / (π * airyDerivModulus (airyAiDerivZero k)) := by
  sorry

/-- airyBiDerivZero value (DLMF 9.9.4). -/
@[dlmf 9.9.E4]
theorem airyBiDerivZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyBi (airyBiDerivZero k) = (-1 : ℂ) ^ (k) / (π * airyDerivModulus (airyBiDerivZero k)) := by
  sorry

/-- Continuous-index interpolation used in DLMF §9.9(iii). -/
theorem airyAiZeroContinuous_natCast {k : ℕ} (hk : 1 ≤ k) :
    airyAiZeroContinuous k = airyAiZero k := by
  sorry

/-- airyAiZeroContinuous derivative value (DLMF 9.9.5). -/
@[dlmf 9.9.E5]
theorem airyAiZeroContinuous_derivative_value {k : ℕ} (hk : 1 ≤ k) :
    airyAiDeriv (airyAiZero k) = (-1 : ℂ) ^ (k - 1) *
      ((-deriv airyAiZeroContinuous k : ℝ) : ℂ) ^ (-1 / 2 : ℂ) := by
  sorry

/-- Continuous-index interpolation used in DLMF §9.9(iii). -/
theorem airyAiDerivZeroContinuous_natCast {k : ℕ} (hk : 1 ≤ k) :
    airyAiDerivZeroContinuous k = airyAiDerivZero k := by
  sorry

/-- airyAiDerivZeroContinuous derivative value (DLMF 9.9.5). -/
@[dlmf 9.9.E5]
theorem airyAiDerivZeroContinuous_derivative_value {k : ℕ} (hk : 1 ≤ k) :
    airyAi (airyAiDerivZero k) = (-1 : ℂ) ^ (k - 1) *
      ((airyAiDerivZero k * deriv airyAiDerivZeroContinuous k : ℝ) : ℂ) ^ (-1 / 2 : ℂ) := by
  sorry

/-- The common all-order T,U,V,W expansions, including every printed coefficient and real/complex zero family in DLMF 9.9.6–9.9.21 (DLMF 9.9.18). -/
@[dlmf 9.9.E6, dlmf 9.9.E7, dlmf 9.9.E8, dlmf 9.9.E9, dlmf 9.9.E10, dlmf 9.9.E11, dlmf 9.9.E12, dlmf 9.9.E13, dlmf 9.9.E14, dlmf 9.9.E15, dlmf 9.9.E16, dlmf 9.9.E17, dlmf 9.9.E18, dlmf 9.9.E19, dlmf 9.9.E20, dlmf 9.9.E21]
theorem airy_zero_common_asymptotic_coefficients  :
    ∃ cT cU cV cW : ℕ → ℂ,
      (∀ n < 6, cT n = ([1, 5/48, -5/36, 77125/82944, -108056875/6967296, 162375596875/334430208] : List ℂ)[n]! ∧
      ∀ n < 6, cU n = ([1, -7/48, 35/288, -181223/207360, 18683371/1244160, -91145884361/191102976] : List ℂ)[n]! ∧
      ∀ n < 6, cV n = ([1, 5/48, -1525/4608, 2397875/663552, -74898940625/891813888, 144198303734375/42807066624] : List ℂ)[n]! ∧
      ∀ n < 6, cW n = ([1, -7/96, 1673/6144, -84394709/26542080, 780277135421/10192158720, -204449051051945/65229815808] : List ℂ)[n]!) ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyAiZero (k + 1) : ℂ)) (airyZeroArgument 1) cT ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyAiDerivZero (k + 1) : ℂ)) (airyZeroArgument 3) cU ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyBiZero (k + 1) : ℂ)) (airyZeroArgument 3) cT ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyBiDerivZero (k + 1) : ℂ)) (airyZeroArgument 1) cU ∧
      HasAiryZeroExpansion (1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k) * airyAiDeriv (airyAiZero (k + 1))) (airyZeroArgument 1) cV ∧
      HasAiryZeroExpansion (-1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k) * airyAi (airyAiDerivZero (k + 1))) (airyZeroArgument 3) cW ∧
      HasAiryZeroExpansion (1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k) * airyBiDeriv (airyBiZero (k + 1))) (airyZeroArgument 3) cV ∧
      HasAiryZeroExpansion (-1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k + 1) * airyBi (airyBiDerivZero (k + 1))) (airyZeroArgument 1) cW ∧
      HasAiryZeroExpansion (2 / 3)
        (fun k => exp (-π * I / 3) * airyBiComplexZero (k + 1)) (airyComplexZeroArgument 1) cT ∧
      HasAiryZeroExpansion (2 / 3)
        (fun k => exp (-π * I / 3) * airyBiDerivComplexZero (k + 1)) (airyComplexZeroArgument 3) cU ∧
      HasAiryZeroExpansion (1 / 6)
        (fun k => Real.sqrt π / Real.sqrt 2 * (-1 : ℂ) ^ (k + 1) * exp (π * I / 6) *
          airyBiDeriv (airyBiComplexZero (k + 1))) (airyComplexZeroArgument 1) cV ∧
      HasAiryZeroExpansion (-1 / 6)
        (fun k => Real.sqrt π / Real.sqrt 2 * (-1 : ℂ) ^ (k) * exp (-π * I / 6) *
          airyBi (airyBiDerivComplexZero (k + 1))) (airyComplexZeroArgument 3) cW := by
  sorry

/-- Exact common T,U,V,W parametrizations in DLMF 9.9.6–9.9.17.
Their all-order asymptotics, with the auxiliary functions eliminated, are given by
`airy_zero_common_asymptotic_coefficients`. No analytic continuation is asserted here. -/
@[dlmf 9.9.E6, dlmf 9.9.E7, dlmf 9.9.E8, dlmf 9.9.E9, dlmf 9.9.E10, dlmf 9.9.E11,
  dlmf 9.9.E12, dlmf 9.9.E13, dlmf 9.9.E14, dlmf 9.9.E15, dlmf 9.9.E16, dlmf 9.9.E17]
theorem exists_airy_zero_parametrizations :
    ∃ T U V W : ℂ → ℂ, ∀ k : ℕ,
      (airyAiZero (k + 1) : ℂ) = -T (airyZeroArgument 1 k) ∧
      airyAiDeriv (airyAiZero (k + 1)) = (-1 : ℂ) ^ k * V (airyZeroArgument 1 k) ∧
      (airyAiDerivZero (k + 1) : ℂ) = -U (airyZeroArgument 3 k) ∧
      airyAi (airyAiDerivZero (k + 1)) = (-1 : ℂ) ^ k * W (airyZeroArgument 3 k) ∧
      (airyBiZero (k + 1) : ℂ) = -T (airyZeroArgument 3 k) ∧
      airyBiDeriv (airyBiZero (k + 1)) = (-1 : ℂ) ^ k * V (airyZeroArgument 3 k) ∧
      (airyBiDerivZero (k + 1) : ℂ) = -U (airyZeroArgument 1 k) ∧
      airyBi (airyBiDerivZero (k + 1)) = (-1 : ℂ) ^ (k + 1) * W (airyZeroArgument 1 k) ∧
      airyBiComplexZero (k + 1) = exp (π * I / 3) * T (airyComplexZeroArgument 1 k) ∧
      airyBiDeriv (airyBiComplexZero (k + 1)) =
        (-1 : ℂ) ^ (k + 1) * Real.sqrt 2 * exp (-π * I / 6) * V (airyComplexZeroArgument 1 k) ∧
      airyBiDerivComplexZero (k + 1) = exp (π * I / 3) * U (airyComplexZeroArgument 3 k) ∧
      airyBi (airyBiDerivComplexZero (k + 1)) =
        (-1 : ℂ) ^ k * Real.sqrt 2 * exp (π * I / 6) * W (airyComplexZeroArgument 3 k) := by
  sorry

end AAR.Airy
