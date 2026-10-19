/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Struve.Basic

/-!
# Struve half-integer orders, recurrences and Bessel expansions

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Struve

open AAR.Bessel

/-- struveK nat add half. -/
@[dlmf 11.4.E1]
theorem struveK_nat_add_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveK (n+1/2) z = (2/(π*z))^(1/2:ℂ) * ∑ m ∈ Finset.range (n+1), ((2*m).factorial : ℂ)*2^(-(2*m:ℤ))/((m.factorial:ℂ)*(n-m).factorial)*(z/2)^((n:ℤ)-2*m) := by
  sorry

/-- struveL nat add half. -/
@[dlmf 11.4.E2]
theorem struveL_nat_add_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (n+1/2) z = besselI (-n-1/2) z - (2/(π*z))^(1/2:ℂ) * ∑ m ∈ Finset.range (n+1), (-1)^m*((2*m).factorial : ℂ)*2^(-(2*m:ℤ))/((m.factorial:ℂ)*(n-m).factorial)*(z/2)^((n:ℤ)-2*m) := by
  sorry

/-- struveH neg nat sub half. -/
@[dlmf 11.4.E3]
theorem struveH_neg_nat_sub_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (-n-1/2) z = (-1)^n*besselJ (n+1/2) z := by
  sorry

/-- struveL neg nat sub half. -/
@[dlmf 11.4.E4]
theorem struveL_neg_nat_sub_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (-n-1/2) z = besselI (n+1/2) z := by
  sorry

/-- struve special 5. -/
@[dlmf 11.4.E5]
theorem struve_special_5 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (1/2) z = (2/(π*z))^(1/2:ℂ)*(1-cos z) := by
  sorry

/-- struve special 6. -/
@[dlmf 11.4.E6]
theorem struve_special_6 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (-1/2) z = (2/(π*z))^(1/2:ℂ)*sin z := by
  sorry

/-- struve special 7. -/
@[dlmf 11.4.E7]
theorem struve_special_7 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (1/2) z = (2/(π*z))^(1/2:ℂ)*(cosh z-1) := by
  sorry

/-- struve special 8. -/
@[dlmf 11.4.E8]
theorem struve_special_8 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (-1/2) z = (2/(π*z))^(1/2:ℂ)*sinh z := by
  sorry

/-- struve special 9. -/
@[dlmf 11.4.E9]
theorem struve_special_9 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (3/2) z = (z/(2*π))^(1/2:ℂ)*(1+2/z^2)-(2/(π*z))^(1/2:ℂ)*(sin z+cos z/z) := by
  sorry

/-- struve special 10. -/
@[dlmf 11.4.E10]
theorem struve_special_10 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (-3/2) z = (2/(π*z))^(1/2:ℂ)*(cos z-sin z/z) := by
  sorry

/-- struve special 11. -/
@[dlmf 11.4.E11]
theorem struve_special_11 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (3/2) z = -(z/(2*π))^(1/2:ℂ)*(1-2/z^2)+(2/(π*z))^(1/2:ℂ)*(sinh z-cosh z/z) := by
  sorry

/-- struve special 12. -/
@[dlmf 11.4.E12]
theorem struve_special_12 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (-3/2) z = (2/(π*z))^(1/2:ℂ)*(cosh z-sinh z/z) := by
  sorry

/-- struveH nonneg. -/
@[dlmf 11.4.E13]
theorem struveH_nonneg {ν x : ℝ} (hν : 1/2 ≤ ν) (hx : 0 < x) :
    0 ≤ (struveH ν x).re ∧ (struveH ν x).im = 0 := by
  sorry

/-- DLMF relative-error bound, with minimum distance to reciprocal-gamma zeros explicit. -/
@[dlmf 11.4.E14, dlmf 11.4.E15]
theorem struveH_relative_bound {ν z : ℂ} (hν : ∀ n : ℕ, ν+3/2 ≠ -n) (hz : z ≠ 0) (d : ℝ) (hd : 0 < d) (hmin : ∀ n : ℕ, d ≤ ‖ν+3/2+n‖) (hatt : ∃ n : ℕ, d = ‖ν+3/2+n‖) :
    ∃ θ : ℂ, struveH ν z = 2*(z/2)^(ν+1)/(Real.sqrt π*Gamma (ν+3/2))*(1+θ) ∧ ‖θ‖ < 2/3*Real.exp (‖z‖^2/(4*d)-1) := by
  sorry

/-- struveH bessel series 18. -/
@[dlmf 11.4.E18]
theorem struveH_bessel_series_18 (ν : ℂ) (hν : ∀ n : ℕ, ν ≠ -(n+1)) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (4/(Real.sqrt π*Gamma (ν+1/2))) * ((2*k+ν+1)*Gamma (k+ν+1)/((k.factorial:ℂ)*(2*k+1)*(2*k+2*ν+1))*besselJ (2*k+ν+1) z)) (struveH ν z) := by
  sorry

/-- struveH bessel series 19. -/
@[dlmf 11.4.E19]
theorem struveH_bessel_series_19 (ν : ℂ)  {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (z/(2*π))^(1/2:ℂ) * ((z/2)^k/((k.factorial:ℂ)*(k+1/2))*besselJ (k+ν+1/2) z)) (struveH ν z) := by
  sorry

/-- struveH bessel series 20. -/
@[dlmf 11.4.E20]
theorem struveH_bessel_series_20 (ν : ℂ) (hν : ∀ n : ℕ, ν+1/2 ≠ -n) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (z/2)^(ν+1/2)/Gamma (ν+1/2) * ((z/2)^k/((k.factorial:ℂ)*(k+ν+1/2))*besselJ (k+1/2) z)) (struveH ν z) := by
  sorry

/-- struveH zero odd. -/
@[dlmf 11.4.E21]
theorem struveH_zero_odd {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 4/π*besselJ (2*k+1) z/(2*k+1)) (struveH 0 z) := by
  sorry

/-- struveH zero products. -/
@[dlmf 11.4.E21]
theorem struveH_zero_products {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 2*(-1)^k*(besselJ (k+1/2) (z/2))^2) (struveH 0 z) := by
  sorry

/-- struveH one even. -/
@[dlmf 11.4.E22]
theorem struveH_one_even {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 4/π*besselJ (2*(k+1)) z/(4*(k+1:ℂ)^2-1)) (struveH 1 z-2/π*(1-besselJ 0 z)) := by
  sorry

/-- struveH one products. -/
@[dlmf 11.4.E22]
theorem struveH_one_products {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 4*besselJ (2*k+1/2) (z/2)*besselJ (2*k+3/2) (z/2)) (struveH 1 z) := by
  sorry

/-- struveH recurrence. -/
@[dlmf 11.4.E23]
theorem struveH_recurrence (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (ν-1) z + struveH (ν+1) z = 2*ν/z*struveH ν z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)) := by
  sorry

/-- struveH derivative. -/
@[dlmf 11.4.E24]
theorem struveH_derivative (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (struveH ν) ((struveH (ν-1) z - struveH (ν+1) z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)))/2) z := by
  sorry

/-- struveH weighted deriv 27. -/
@[dlmf 11.4.E27, dlmf 11.7.E1]
theorem struveH_weighted_deriv_27 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(1*ν)*struveH ν z) (z^ν*struveH (ν-1) z) z := by
  sorry

/-- struveH weighted deriv 28. -/
@[dlmf 11.4.E28, dlmf 11.7.E2]
theorem struveH_weighted_deriv_28 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(-1*ν)*struveH ν z) (2^(-ν)/(Real.sqrt π*Gamma (ν+3/2)) - z^(-ν)*struveH (ν+1) z) z := by
  sorry

/-- struveH iterated weighted deriv. -/
@[dlmf 11.4.E31]
theorem struveH_iterated_weighted_deriv (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ((fun f : ℂ → ℂ => fun z => deriv f z/z)^[m]) (fun z => z^ν*struveH ν z) z = z^(ν-m)*struveH (ν-m) z := by
  sorry

/-- struveH zero deriv. -/
@[dlmf 11.4.E32]
theorem struveH_zero_deriv (z : ℂ) :
    HasDerivAt (struveH 0) (2/π - struveH 1 z) z := by
  sorry

/-- struveH one weighted deriv. -/
@[dlmf 11.4.E32]
theorem struveH_one_weighted_deriv (z : ℂ) :
    HasDerivAt (fun z => z*struveH 1 z) (z*struveH 0 z) z := by
  sorry

/-- struveL recurrence. -/
@[dlmf 11.4.E25]
theorem struveL_recurrence (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (ν-1) z - struveL (ν+1) z = 2*ν/z*struveL ν z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)) := by
  sorry

/-- struveL derivative. -/
@[dlmf 11.4.E26]
theorem struveL_derivative (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (struveL ν) ((struveL (ν-1) z + struveL (ν+1) z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)))/2) z := by
  sorry

/-- struveL weighted deriv 29. -/
@[dlmf 11.4.E29, dlmf 11.7.E3]
theorem struveL_weighted_deriv_29 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(1*ν)*struveL ν z) (z^ν*struveL (ν-1) z) z := by
  sorry

/-- struveL weighted deriv 30. -/
@[dlmf 11.4.E30, dlmf 11.7.E4]
theorem struveL_weighted_deriv_30 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(-1*ν)*struveL ν z) (2^(-ν)/(Real.sqrt π*Gamma (ν+3/2)) + z^(-ν)*struveL (ν+1) z) z := by
  sorry

/-- struveL iterated weighted deriv. -/
@[dlmf 11.4.E31]
theorem struveL_iterated_weighted_deriv (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ((fun f : ℂ → ℂ => fun z => deriv f z/z)^[m]) (fun z => z^ν*struveL ν z) z = z^(ν-m)*struveL (ν-m) z := by
  sorry

/-- struveL zero deriv. -/
@[dlmf 11.4.E33]
theorem struveL_zero_deriv (z : ℂ) :
    HasDerivAt (struveL 0) (2/π + struveL 1 z) z := by
  sorry

/-- struveL one weighted deriv. -/
@[dlmf 11.4.E33]
theorem struveL_one_weighted_deriv (z : ℂ) :
    HasDerivAt (fun z => z*struveL 1 z) (z*struveL 0 z) z := by
  sorry

end AAR.Struve
