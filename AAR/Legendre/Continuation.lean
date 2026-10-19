/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Conical
public import AAR.Legendre.Hypergeometric

/-!
# Legendre boundary values and continuation by ODE transport

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- Boundary value with convergence asserted separately. -/
def legendreBoundary (F : ℂ → ℂ) (s x : ℝ) : ℂ :=
  limUnder (𝓝[>] (0:ℝ)) (fun ε : ℝ => F (x+s*I*ε))

/-- associatedP boundary upper. -/
@[dlmf 14.23.E1]
theorem associatedP_boundary_upper (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => associatedP ν μ (x+(1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(1:ℂ)*μ*π*I/2)*ferrersP ν μ x)) := by
  sorry

/-- olverQ boundary upper. -/
@[dlmf 14.23.E2]
theorem olverQ_boundary_upper (ν μ : ℂ) (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp ((1:ℂ)*μ*π*I/2)/Gamma (ν+μ+1)*(ferrersQ ν μ x-(1:ℂ)*π*I/2*ferrersP ν μ x))) := by
  sorry

/-- ferrersP boundary inverse upper. -/
@[dlmf 14.23.E4]
theorem ferrersP_boundary_inverse_upper (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x=exp ((1:ℂ)*μ*π*I/2)*legendreBoundary (associatedP ν μ) 1 x := by
  sorry

/-- ferrersQ boundary inverse upper. -/
@[dlmf 14.23.E6]
theorem ferrersQ_boundary_inverse_upper {ν μ : ℂ} (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν μ x=exp (-(1:ℂ)*μ*π*I/2)*Gamma (ν+μ+1)*legendreBoundary (olverQ ν μ) 1 x+(1:ℂ)*π*I/2*exp ((1:ℂ)*μ*π*I/2)*legendreBoundary (associatedP ν μ) 1 x := by
  sorry

/-- olverQ boundary hypergeometric upper. -/
@[dlmf 14.23.E3]
theorem olverQ_boundary_hypergeometric_upper (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(1:ℂ)*ν*π*I/2)*(π:ℂ)^(3/2:ℂ)*(1-x^2:ℂ)^(μ/2)/2^(ν+1)*(x*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (x^2)/(Gamma ((ν-μ+1)/2)*Gamma ((ν+μ+1)/2))-(1:ℂ)*I*regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (x^2)/(Gamma ((ν-μ+2)/2)*Gamma ((ν+μ+2)/2))))) := by
  sorry

/-- associatedP boundary lower. -/
@[dlmf 14.23.E1]
theorem associatedP_boundary_lower (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => associatedP ν μ (x+(-1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(-1:ℂ)*μ*π*I/2)*ferrersP ν μ x)) := by
  sorry

/-- olverQ boundary lower. -/
@[dlmf 14.23.E2]
theorem olverQ_boundary_lower (ν μ : ℂ) (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(-1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp ((-1:ℂ)*μ*π*I/2)/Gamma (ν+μ+1)*(ferrersQ ν μ x-(-1:ℂ)*π*I/2*ferrersP ν μ x))) := by
  sorry

/-- ferrersP boundary inverse lower. -/
@[dlmf 14.23.E4]
theorem ferrersP_boundary_inverse_lower (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x=exp ((-1:ℂ)*μ*π*I/2)*legendreBoundary (associatedP ν μ) (-1) x := by
  sorry

/-- ferrersQ boundary inverse lower. -/
@[dlmf 14.23.E6]
theorem ferrersQ_boundary_inverse_lower {ν μ : ℂ} (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν μ x=exp (-(-1:ℂ)*μ*π*I/2)*Gamma (ν+μ+1)*legendreBoundary (olverQ ν μ) (-1) x+(-1:ℂ)*π*I/2*exp ((-1:ℂ)*μ*π*I/2)*legendreBoundary (associatedP ν μ) (-1) x := by
  sorry

/-- olverQ boundary hypergeometric lower. -/
@[dlmf 14.23.E3]
theorem olverQ_boundary_hypergeometric_lower (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun ε : ℝ => olverQ ν μ (x+(-1:ℂ)*I*ε)) (𝓝[>] (0:ℝ)) (𝓝 (exp (-(-1:ℂ)*ν*π*I/2)*(π:ℂ)^(3/2:ℂ)*(1-x^2:ℂ)^(μ/2)/2^(ν+1)*(x*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) (x^2)/(Gamma ((ν-μ+1)/2)*Gamma ((ν+μ+1)/2))-(-1:ℂ)*I*regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) (x^2)/(Gamma ((ν-μ+2)/2)*Gamma ((ν+μ+2)/2))))) := by
  sorry

/-- ferrersQ boundary average. -/
@[dlmf 14.23.E5]
theorem ferrersQ_boundary_average {ν μ : ℂ} (hr : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν μ x=Gamma (ν+μ+1)/2*(exp (-μ*π*I/2)*legendreBoundary (olverQ ν μ) 1 x+exp (μ*π*I/2)*legendreBoundary (olverQ ν μ) (-1) x) := by
  sorry

/-- conicalQHat boundary. -/
@[dlmf 14.23.E7]
theorem conicalQHat_boundary {τ μ : ℝ} (hτ : 0 ≤ τ) (hμ : 0 ≤ μ) (hex : τ ≠ 0 ∨ ∀ n : ℕ, μ ≠ n+1/2) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    conicalQHat τ μ x=1/2*exp (3*μ*π*I/2)*legendreBoundary (associatedQ (-1/2+I*τ) (-μ)) (-1) x+1/2*exp (-3*μ*π*I/2)*legendreBoundary (associatedQ (-1/2-I*τ) (-μ)) 1 x := by
  sorry

/-- Continuation of the value and complex derivative along a path, by its first-order differential system. -/
def IsLegendreTransport (ν μ : ℂ) (γ : ℝ → ℂ) (a b : ℂ) (u v : ℝ → ℂ) : Prop :=
  u 0=a ∧ v 0=b ∧ ContinuousOn u (Icc 0 1) ∧ ContinuousOn v (Icc 0 1) ∧ ∀ t ∈ Icc (0:ℝ) 1, HasDerivWithinAt u (deriv γ t*v t) (Icc 0 1) t ∧ HasDerivWithinAt v (deriv γ t*(2*γ t*v t-(ν*(ν+1)-μ^2/(1-(γ t)^2))*u t)/(1-(γ t)^2)) (Icc 0 1) t

/-- Endpoint value of the continued solution; existence and endpoint uniqueness are not consequences of choice. -/
def legendreTransport (ν μ : ℂ) (γ : ℝ → ℂ) (a b : ℂ) : ℂ :=
  let uv:=Classical.epsilon (fun p : (ℝ → ℂ) × (ℝ → ℂ) => IsLegendreTransport ν μ γ a b p.1 p.2); uv.1 1

/-- Existence on a compact path avoiding both regular singular points. -/
theorem legendreTransport_exists (ν μ a b : ℂ) (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hreg : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 1 ∧ γ t ≠ -1) :
    ∃ u v : ℝ → ℂ, IsLegendreTransport ν μ γ a b u v := by
  sorry

/-- Uniqueness identifies the actual analytic continuation, independently of the chosen solution. -/
theorem legendreTransport_unique (ν μ a b : ℂ) (γ : ℝ → ℂ) (hγ : ContDiff ℝ 1 γ) (hreg : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ 1 ∧ γ t ≠ -1) {u v : ℝ → ℂ} (huv : IsLegendreTransport ν μ γ a b u v) :
    legendreTransport ν μ γ a b=u 1 := by
  sorry

/-- Half-circuits of the confocal ellipse, with inherited path orientation. -/
def legendreEllipsePath (z : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  let q:=z+exp ((log (z-1)+log (z+1))/2); (q*exp (s*π*I*t)+q⁻¹*exp (-s*π*I*t))/2

/-- legendreEllipseContinued. -/
def legendreEllipseContinued (F : ℂ → ℂ) (ν μ z : ℂ) (s : ℤ) : ℂ :=
  legendreTransport ν μ (legendreEllipsePath z s) (F z) (deriv F z)

/-- The parameter limit retains odd half-integral degrees. -/
@[dlmf 14.24.E1]
theorem associatedP_ellipse_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    Tendsto (fun v : ℂ => exp (s*v*π*I)*associatedP v (-μ) z+2*I*sin ((v+1/2)*s*π)*exp (-s*π*I/2)/(cos (v*π)*Gamma (μ-v))*olverQ v μ z) (𝓝[≠] ν) (𝓝 (legendreEllipseContinued (associatedP ν (-μ)) ν μ z s)) := by
  sorry

/-- olverQ ellipse continuation. -/
@[dlmf 14.24.E2]
theorem olverQ_ellipse_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    legendreEllipseContinued (olverQ ν μ) ν μ z s=(-1:ℂ)^s*exp (-s*ν*π*I)*olverQ ν μ z := by
  sorry

/-- Smooth joining parameter with zero derivatives at both endpoints. -/
def legendreSmoothStep (t : ℝ) : ℝ :=
  3*t^2-2*t^3

/-- A joined path from z to 3/2, s circuits about one of radius 1/2, and back; minus one is not enclosed. -/
def legendreOneLoop (z : ℂ) (s : ℤ) (t : ℝ) : ℂ :=
  if t ≤ 1/3 then z+legendreSmoothStep (3*t)*(3/2-z) else if t ≤ 2/3 then 1+1/2*exp (2*π*I*s*legendreSmoothStep (3*t-1)) else 3/2+legendreSmoothStep (3*t-2)*(z-3/2)

/-- legendreOneContinued. -/
def legendreOneContinued (F : ℂ → ℂ) (ν μ z : ℂ) (s : ℤ) : ℂ :=
  legendreTransport ν μ (legendreOneLoop z s) (F z) (deriv F z)

/-- associatedP one continuation. -/
@[dlmf 14.24.E3]
theorem associatedP_one_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    legendreOneContinued (associatedP ν (-μ)) ν μ z s=exp (s*μ*π*I)*associatedP ν (-μ) z := by
  sorry

/-- Integer orders use the removable parameter limit of the complete expression. -/
@[dlmf 14.24.E4]
theorem olverQ_one_continuation (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (s : ℤ) :
    Tendsto (fun m : ℂ => exp (-s*m*π*I)*olverQ ν m z-π*I*sin (s*m*π)/(sin (m*π)*Gamma (ν-m+1))*associatedP ν (-m) z) (𝓝[≠] μ) (𝓝 (legendreOneContinued (olverQ ν μ) ν μ z s)) := by
  sorry

end AAR.Legendre
