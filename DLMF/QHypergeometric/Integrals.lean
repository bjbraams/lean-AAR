/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Calculus
public import DLMF.Gamma.QGamma

/-!
# q-beta integrals (DLMF §17.13)

Finite and bilateral Jackson integrals reuse `QSeries.jacksonIntegral` through
the adapters in `Calculus`. Every evaluated integral asserts convergence of its
defining series. The ordinary Mellin integral asserts Bochner integrability.
The Gamma quotient of 17.13.3 is filled by its complex-parameter limit at
removable positive-integer alpha values; the literal totalized `0/0` would be false.
-/

@[expose] public noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology
open DLMF.QSeries
namespace DLMF.QHypergeometric

/-- The two-ended Jackson q-beta kernel. -/
def jacksonBetaKernel (a b c d q x : ℂ) : ℂ :=
  qPochhammerInf (-q*x/c) q * qPochhammerInf (q*x/d) q /
    (qPochhammerInf (-a*x/c) q * qPochhammerInf (b*x/d) q)

/-- The complex two-ended q-beta integral, with endpoint-series convergence. -/
@[dlmf 17.13.E1]
theorem jacksonBeta_integral (a b c d q : ℂ) (hq : ‖q‖<1)
    (hc : c≠0) (hd : d≠0) (hcd : c+d≠0)
    (hden : qDenominatorRegular [a,b,-b*c/d,-a*d/c] q) :
    Summable (fun n : ℕ => jacksonBetaKernel a b c d q (d*q^n)*q^n) ∧
    Summable (fun n : ℕ => jacksonBetaKernel a b c d q (-c*q^n)*q^n) ∧
    jacksonBetween q (-c) d (jacksonBetaKernel a b c d q) =
      (1-q) * qPochhammerInf q q * qPochhammerInf (a*b) q * c*d *
        qPochhammerInf (-c/d) q * qPochhammerInf (-d/c) q /
        (qPochhammerInf a q * qPochhammerInf b q * (c+d) *
          qPochhammerInf (-b*c/d) q * qPochhammerInf (-a*d/c) q) := by
  sorry

/-- The q-Gamma normalization of the two-ended Jackson integral. -/
@[dlmf 17.13.E2]
theorem jacksonBeta_integral_qGamma (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (α β c d : ℂ) (hα : 0<α.re) (hβ : 0<β.re)
    (hc : c≠0) (hd : d≠0) (hcd : c+d≠0)
    (hden : qDenominatorRegular [-((q:ℂ)^β)*c/d,-((q:ℂ)^α)*d/c] q) :
    Summable (fun n : ℕ => jacksonBetaKernel ((q:ℂ)^α) ((q:ℂ)^β) c d q (d*q^n)*q^n) ∧
    Summable (fun n : ℕ => jacksonBetaKernel ((q:ℂ)^α) ((q:ℂ)^β) c d q (-c*q^n)*q^n) ∧
    jacksonBetween q (-c) d (jacksonBetaKernel ((q:ℂ)^α) ((q:ℂ)^β) c d q) =
      DLMF.Gamma.qBeta q α β * (c*d/(c+d)) *
        qPochhammerInf (-c/d) q * qPochhammerInf (-d/c) q /
        (qPochhammerInf (-((q:ℂ)^β)*c/d) q * qPochhammerInf (-((q:ℂ)^α)*d/c) q) := by
  sorry

/-- The meromorphically interpreted Gamma quotient in the ordinary q-beta integral. -/
def mellinQBetaValue (q : ℝ) (α β : ℂ) : ℂ :=
  limUnder (𝓝[≠] α) (fun a : ℂ =>
    Complex.Gamma a * Complex.Gamma (1-a) * DLMF.QSeries.qGamma q β /
      (DLMF.QSeries.qGamma q (1-a) * DLMF.QSeries.qGamma q (a+β)))

/-- On its initial regular strip the filled value is the printed Gamma quotient. -/
@[dlmf 17.13.E3]
theorem mellinQBetaValue_eq (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (α β : ℂ) (hα0 : 0<α.re) (hα1 : α.re<1) (hβ : 0<β.re) :
    mellinQBetaValue q α β =
      Complex.Gamma α * Complex.Gamma (1-α) * DLMF.QSeries.qGamma q β /
        (DLMF.QSeries.qGamma q (1-α) * DLMF.QSeries.qGamma q (α+β)) := by
  sorry

/-- The ordinary Mellin q-beta integral, including the removable integer-alpha cases. -/
@[dlmf 17.13.E3]
theorem mellinQBeta_integral (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (α β : ℂ) (hα : 0<α.re) (hβ : 0<β.re) :
    let f := fun t : ℝ => (t:ℂ)^(α-1) *
      qPochhammerInf (-(t:ℂ)*(q:ℂ)^(α+β)) q / qPochhammerInf (-(t:ℂ)) q
    IntegrableOn f (Ioi 0) ∧ (∫ t in Ioi (0:ℝ), f t) = mellinQBetaValue q α β := by
  sorry

/-- The bilateral Jackson q-beta integral with a general nonzero scale. -/
@[dlmf 17.13.E4]
theorem bilateralJacksonBeta_integral (q : ℝ) (hq0 : 0<q) (hq1 : q<1)
    (α β c : ℂ) (hα : 0<α.re) (hβ : 0<β.re) (hc : c≠0)
    (hden : ∀ k : ℤ, c≠ -((q:ℂ)^k)) :
    let f := fun t : ℂ => t^(α-1) *
      qPochhammerInf (-c*t*(q:ℂ)^(α+β)) q / qPochhammerInf (-c*t) q
    Summable (fun n : ℤ => (q:ℂ)^n * f ((q:ℂ)^n)) ∧
    jacksonBilateral q f =
      DLMF.Gamma.qBeta q α β * qPochhammerInf (-c*(q:ℂ)^α) q *
        qPochhammerInf (-(q:ℂ)^(1-α)/c) q /
        (qPochhammerInf (-c) q * qPochhammerInf (-(q:ℂ)/c) q) := by
  sorry

/-- The Gamma quotient has a genuine removable limit, including positive integer alpha. -/
@[dlmf 17.13.E3]
theorem tendsto_mellinQBetaValue (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (α β : ℂ) (hα : 0 < α.re) (hβ : 0 < β.re) :
    Tendsto (fun a : ℂ =>
      Complex.Gamma a * Complex.Gamma (1-a) * DLMF.QSeries.qGamma q β /
        (DLMF.QSeries.qGamma q (1-a) * DLMF.QSeries.qGamma q (a+β)))
      (𝓝[≠] α) (𝓝 (mellinQBetaValue q α β)) := by
  sorry


end DLMF.QHypergeometric
