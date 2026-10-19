/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Hypergeometric

/-!
# Associated Legendre behavior at singularities

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- legendre singular 1. -/
@[dlmf 14.8.E1]
theorem legendre_singular_1 (ν μ : ℂ) (hμ : ∀ n : ℕ, μ ≠ n+1) :
    (fun x : ℝ => ferrersP ν μ x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => 1/Gamma (1-μ)*(2/(1-x):ℂ)^(μ/2)) := by
  sorry

/-- legendre singular 2. -/
@[dlmf 14.8.E2]
theorem legendre_singular_2 (ν : ℂ) (m : ℕ) (hm : 0 < m) (hν : poch (ν-m+1) (2*m) ≠ 0) :
    (fun x : ℝ => ferrersP ν m x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => (-1)^m*poch (ν-m+1) (2*m)/(m.factorial:ℂ)*((1-x)/2:ℂ)^((m:ℂ)/2)) := by
  sorry

/-- legendre singular 4. -/
@[dlmf 14.8.E4]
theorem legendre_singular_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) (hμ : 0 < μ.re) (hh : ∀ n : ℕ, μ ≠ n+1/2) :
    (fun x : ℝ => ferrersQ ν μ x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => 1/2*cos (μ*π)*Gamma μ*(2/(1-x):ℂ)^(μ/2)) := by
  sorry

/-- legendre singular 5. -/
@[dlmf 14.8.E5]
theorem legendre_singular_5 (ν : ℂ) (n : ℕ) (hp : LegendreQRegular ν (n+1/2)) (hm : LegendreQRegular ν (-n-1/2)) :
    (fun x : ℝ => ferrersQ ν (n+1/2) x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => (-1)^(n+1)*π*Gamma (ν+n+3/2)/(2*Gamma (n+3/2)*Gamma (ν-n+1/2))*((1-x)/2:ℂ)^((n+1/2:ℂ)/2)) := by
  sorry

/-- legendre singular 6. -/
@[dlmf 14.8.E6]
theorem legendre_singular_6 (ν μ : ℂ) (hμ : 0 < μ.re) (hp : LegendreQRegular ν μ) (hm : LegendreQRegular ν (-μ)) :
    (fun x : ℝ => ferrersQ ν (-μ) x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => Gamma μ*Gamma (ν-μ+1)/(2*Gamma (ν+μ+1))*(2/(1-x):ℂ)^(μ/2)) := by
  sorry

/-- legendre singular 7. -/
@[dlmf 14.8.E7]
theorem legendre_singular_7 (ν μ : ℂ) (hμ : ∀ n : ℕ, μ ≠ n+1) :
    (fun x : ℝ => associatedP ν μ x) ~[𝓝[>] (1:ℝ)] (fun x : ℝ => 1/Gamma (1-μ)*(2/(x-1):ℂ)^(μ/2)) := by
  sorry

/-- legendre singular 8. -/
@[dlmf 14.8.E8]
theorem legendre_singular_8 (ν : ℂ) (m : ℕ) (hm : 0 < m) (hp : LegendreQRegular ν m) (hn : LegendreQRegular ν (-m)) :
    (fun x : ℝ => associatedP ν m x) ~[𝓝[>] (1:ℝ)] (fun x : ℝ => Gamma (ν+m+1)/((m.factorial:ℂ)*Gamma (ν-m+1))*((x-1)/2:ℂ)^((m:ℂ)/2)) := by
  sorry

/-- legendre singular 11. -/
@[dlmf 14.8.E11]
theorem legendre_singular_11 (ν μ : ℂ) (hμ : 0 < μ.re) (hp : LegendreQRegular ν μ) :
    (fun x : ℝ => olverQ ν μ x) ~[𝓝[>] (1:ℝ)] (fun x : ℝ => Gamma μ/(2*Gamma (ν+μ+1))*(2/(x-1):ℂ)^(μ/2)) := by
  sorry

/-- legendre singular 12. -/
@[dlmf 14.8.E12]
theorem legendre_singular_12 (ν μ : ℂ) (hν : -1/2 < ν.re) (hμ : ∀ n : ℕ, μ-ν ≠ n+1) :
    (fun x : ℝ => associatedP ν μ x) ~[atTop] (fun x : ℝ => Gamma (ν+1/2)/(Real.sqrt π*Gamma (ν-μ+1))*(2*x:ℂ)^ν) := by
  sorry

/-- legendre singular 13. -/
@[dlmf 14.8.E13]
theorem legendre_singular_13 (ν μ : ℂ) (hν : ν.re < -1/2) (hμ : ∀ n : ℕ, ν+μ ≠ n) :
    (fun x : ℝ => associatedP ν μ x) ~[atTop] (fun x : ℝ => Gamma (-ν-1/2)/(Real.sqrt π*Gamma (-μ-ν)*(2*x:ℂ)^(ν+1))) := by
  sorry

/-- legendre singular 14. -/
@[dlmf 14.8.E14]
theorem legendre_singular_14 (μ : ℂ) (hμ : ∀ n : ℕ, μ ≠ n+1/2) :
    (fun x : ℝ => associatedP (-1/2) μ x) ~[atTop] (fun x : ℝ => 1/Gamma (1/2-μ)*(2/(π*x):ℂ)^(1/2:ℂ)*Real.log x) := by
  sorry

/-- legendre singular 15. -/
@[dlmf 14.8.E15]
theorem legendre_singular_15 (ν μ : ℂ) (hν : ∀ n : ℕ, ν ≠ -n-3/2) :
    (fun x : ℝ => olverQ ν μ x) ~[atTop] (fun x : ℝ => Real.sqrt π/(Gamma (ν+3/2)*(2*x:ℂ)^(ν+1))) := by
  sorry

/-- legendre singular 16. -/
@[dlmf 14.8.E16]
theorem legendre_singular_16 (μ : ℂ) (n : ℕ) (hn : 0 < n) (hμ : ∀ k : ℕ, μ-n+1/2 ≠ -k) :
    (fun x : ℝ => olverQ (-n-1/2) μ x) ~[atTop] (fun x : ℝ => Real.sqrt π*Gamma (μ+n+1/2)/((n.factorial:ℂ)*Gamma (μ-n+1/2)*(2*x:ℂ)^(n+1/2:ℂ))) := by
  sorry

/-- ferrersQ log singular. -/
@[dlmf 14.8.E3]
theorem ferrersQ_log_singular {ν : ℂ} (hν : LegendreQRegular ν 0) :
    (fun x : ℝ => ferrersQ ν 0 x-1/2*log (2/(1-x):ℂ)+Real.eulerMascheroniConstant+digamma (ν+1)) =O[𝓝[<] (1:ℝ)] (fun x : ℝ => (1-x)*Real.log (1-x)) := by
  sorry

/-- olverQ log singular. -/
@[dlmf 14.8.E9]
theorem olverQ_log_singular {ν : ℂ} (hν : LegendreQRegular ν 0) :
    (fun x : ℝ => olverQ ν 0 x+log (x-1:ℂ)/(2*Gamma (ν+1))-(log 2/2-Real.eulerMascheroniConstant-digamma (ν+1))/Gamma (ν+1)) =O[𝓝[>] (1:ℝ)] (fun x : ℝ => (x-1)*Real.log (x-1)) := by
  sorry

/-- olverQ negative degree singular. -/
@[dlmf 14.8.E10]
theorem olverQ_negative_degree_singular (n : ℕ) (hn : 0 < n) :
    Tendsto (fun x : ℝ => olverQ (-n) 0 x) (𝓝[>] (1:ℝ)) (𝓝 ((-1)^(n+1)*((n-1).factorial:ℂ))) := by
  sorry

end AAR.Legendre
