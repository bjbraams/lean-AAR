/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.ExpIntegral
public import AAR.Confluent.ErrorFunctions
public import AAR.Confluent.FresnelAsymptotics
public import AAR.Statistical.IncompleteGamma
public import AAR.Statistical.IncompleteBeta
public import AAR.Bessel.SecondKind
public import AAR.OrthogonalPolynomials.Classical
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Algebra.ContinuedFractions.Basic

/-!
# Convergence and branch conventions for the DLMF Chapters 6–8 acquisition

Improper integrals assert limits of finite integrals. Logarithmic coordinates
retain continuation across cuts. Continued fractions assert convergence of
finite truncations, rather than an equality to a totalized infinite expression.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory
open scoped Real Topology
namespace AAR.DLMF

/-- Improper integral on a right half-line, including convergence. -/
def HasIntegralAtTop (f : ℝ → ℂ) (a : ℝ) (v : ℂ) : Prop :=
  Tendsto (fun R => ∫ t in a..R, f t) atTop (𝓝 v)
/-- Improper integral on a left half-line, including convergence. -/
def HasIntegralAtBot (f : ℝ → ℂ) (a : ℝ) (v : ℂ) : Prop :=
  Tendsto (fun R => ∫ t in R..a, f t) atBot (𝓝 v)
/-- Convergence of both tails separately. -/
def HasIntegralWholeLine (f : ℝ → ℂ) (v : ℂ) : Prop :=
  ∃ u w, HasIntegralAtBot f 0 u ∧ HasIntegralAtTop f 0 w ∧ u + w = v
/-- Value of a convergent tail, with convergence always asserted separately. -/
def improperAtTop (f : ℝ → ℂ) (a : ℝ) : ℂ :=
  limUnder atTop (fun R => ∫ t in a..R, f t)
/-- Symmetric principal value at the interior point of a right half-line. -/
def HasPrincipalValueIoi (f : ℝ → ℂ) (a c : ℝ) (v : ℂ) : Prop :=
  a < c ∧
  (∀ ε > 0, HasIntegralAtTop f (c + ε) (improperAtTop f (c + ε))) ∧
  Tendsto (fun ε : ℝ => (∫ t in a..c-ε, f t) + improperAtTop f (c+ε))
    (𝓝[>] (0 : ℝ)) (𝓝 v)
/-- Straight complex segment with its Jacobian. -/
def segmentIntegral (f : ℂ → ℂ) (a b : ℂ) : ℂ :=
  (b-a) * ∫ t : ℝ in 0..1, f (a + t * (b-a))
/-- Primitive based at zero of an entire integrand. -/
def primitive (f : ℂ → ℂ) (z : ℂ) : ℂ := segmentIntegral f 0 z
/-- Uniform approach to infinity in a closed principal sector. -/
def sector (α : ℝ) : Filter ℂ :=
  comap norm atTop ⊓ 𝓟 {z : ℂ | z ≠ 0 ∧ |arg z| ≤ α}
/-- Uniform approach to infinity in a closed sector on the logarithmic plane. -/
def logSector (α : ℝ) : Filter ℂ :=
  comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | |w.im| ≤ α}
/-- Numerator, denominator and termination flag of a finite continued fraction.
Mathlib’s `GenContFract.nextConts` supplies the recurrence. Continuants avoid
nested division by an intermediate zero. A zero numerator
at a positive index terminates the fraction and freezes subsequent convergents. -/
def cfContinuants (a b : ℕ → ℂ) (k : ℕ) : ℕ → ℂ × ℂ × Bool
  | 0 => (0, 1, false)
  | 1 => (a k, b k, false)
  | n+2 =>
    let u := cfContinuants a b k (n+1)
    let v := cfContinuants a b k n
    if u.2.2 = true ∨ a (k+n+1) = 0 then (u.1, u.2.1, true)
    else
      let p := GenContFract.nextConts (a (k+n+1)) (b (k+n+1))
        ⟨v.1, v.2.1⟩ ⟨u.1, u.2.1⟩
      (p.a, p.b, false)
/-- Finite continued fraction as a ratio of continuants, with exact termination. -/
def cfTail (a b : ℕ → ℂ) (k N : ℕ) : ℂ :=
  let p := cfContinuants a b k N
  p.1/p.2.1
/-- Convergence of the specified finite continued fractions. -/
def HasContinuedFraction (a b : ℕ → ℂ) (v : ℂ) : Prop :=
  Tendsto (cfTail a b 0) atTop (𝓝 v)
/-- The odd product 1·3···(2n+1). -/
def oddProduct (n : ℕ) : ℂ := ∏ j ∈ Finset.range (n+1), (2*j+1 : ℂ)
/-- Spherical j_n, with the removable value at zero supplied explicitly. -/
def sphericalJ (n : ℕ) (z : ℂ) : ℂ :=
  Real.sqrt π * z ^ n / (2 : ℂ) ^ (n+1) *
    regularizedHGFun ∅ {(n : ℂ)+3/2} (-z^2/4)
/-- Modified spherical i_n, including its removable value at zero. -/
def sphericalI (n : ℕ) (z : ℂ) : ℂ :=
  Real.sqrt π * z ^ n / (2 : ℂ) ^ (n+1) *
    regularizedHGFun ∅ {(n : ℂ)+3/2} (z^2/4)
/-- A zero chosen by the count of strictly closer zeros; existence is a theorem. -/
def orderedZero (f : ℂ → ℂ) (S : Set ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon (fun z => z ∈ S ∧ f z = 0 ∧
    ({w : ℂ | w ∈ S ∧ f w = 0 ∧ ‖w‖ < ‖z‖} : Set ℂ).ncard = k-1)

/-- Coefficients extracted successively by limits at positive infinity.
Theorems asserting expansions must separately establish that these limits exist. -/
def asymptoticCoeff (f : ℝ → ℂ) : ℕ → ℂ
  | 0 => limUnder atTop f
  | n+1 => limUnder atTop (fun t : ℝ => (t : ℂ)^(n+1) *
      (f t-∑ j ∈ Finset.range (n+1), asymptoticCoeff f (n-j)*(t : ℂ)^(-((n-j : ℕ) : ℤ))))
termination_by n => n

end AAR.DLMF
