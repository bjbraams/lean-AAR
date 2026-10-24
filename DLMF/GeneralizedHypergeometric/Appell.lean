/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.AppellF4
public import DLMF.Hypergeometric.GeneralizedIntegral
public import DLMF.Core.Framework
public import ToMathlib.Analysis.Complex.ParametricHolomorphy
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic

/-!
# Appell functions and Horn's double series (DLMF §§16.13–16.16)

Acquired 2026-10-24. The ordinary double series are totalized outside convergence and at
exceptional denominator parameters. Convergence, differentiation and integral representations
therefore state their exact domains. Euler integrals provide analytic branches beyond the
series domains. Transformation formulas are identities of germs at the origin, transported
along compatible analytic continuations; no divergent totalized series is silently identified
with a continued function. The infinity connection formula explicitly specifies continuation.

The existing `appF4` and Bailey product theorem are reused. One-variable continuation uses the
pinned TauCeti continuation API; the two-variable definition below is its direct domain extension.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Polynomial
open scoped Real Topology Nat
namespace DLMF.Hypergeometric

/-- A bivariate power series at zero has only its constant term. -/
lemma appell_tsum_zero (c : ℕ × ℕ→ℂ) :
    (∑' p : ℕ × ℕ,c p*0^p.1*0^p.2)=c (0,0) := by
  rw [tsum_eq_single (0,0)]
  · simp
  · rintro ⟨m,n⟩ hp
    by_cases hm : m=0
    · subst m
      have hn : n≠0 := fun hn => hp (by simp [hn])
      simp [hn]
    · simp [hm]

/-- Appell denominator parameters avoid every nonpositive integer. -/
def AppellRegular (c : ℂ) : Prop := ∀ n : ℕ,c≠ -(n:ℂ)

/-- Bidisc of absolute convergence for F1 and F3. -/
def appellBidisc : Set (ℂ × ℂ) := {p | ‖p.1‖<1 ∧ ‖p.2‖<1}

/-- Diamond of absolute convergence for F2. -/
def appellDiamond : Set (ℂ × ℂ) := {p | ‖p.1‖+‖p.2‖<1}

/-- Exact open convergence region of F4. -/
def appellF4Domain : Set (ℂ × ℂ) := {p | Real.sqrt ‖p.1‖+Real.sqrt ‖p.2‖<1}

/-- The first-variable derivative of a bivariate complex function. -/
def appellDx (f : ℂ→ℂ→ℂ) (x y : ℂ) : ℂ := deriv (fun t => f t y) x

/-- The second-variable derivative of a bivariate complex function. -/
def appellDy (f : ℂ→ℂ→ℂ) (x y : ℂ) : ℂ := deriv (f x) y

/-- The first Euler operator in two variables. -/
def appellThetaX (f : ℂ→ℂ→ℂ) : ℂ→ℂ→ℂ := fun x y => x*appellDx f x y

/-- The second Euler operator in two variables. -/
def appellThetaY (f : ℂ→ℂ→ℂ) : ℂ→ℂ→ℂ := fun x y => y*appellDy f x y

/-- Analytic continuation of a two-variable germ along a continuous parameterized path.
This is the two-variable domain analogue of TauCeti.IsAnalyticContinuationAlong. -/
structure IsAppellContinuation (F : ℝ→(ℂ × ℂ→ℂ)) (γ : ℝ→ℂ × ℂ) : Prop where
  continuousOn : ContinuousOn γ (Icc 0 1)
  analyticAt : ∀ t∈Icc 0 1,AnalyticAt ℂ (F t) (γ t)
  locallyEq : ∀ t∈Icc 0 1,∀ᶠ u in 𝓝[Icc 0 1] t,F u=ᶠ[𝓝 (γ u)] F t

/-- A chosen branch is reached from a seed germ by a specified analytic continuation. -/
def IsAppellBranchAt (seed : ℂ × ℂ→ℂ) (p : ℂ × ℂ) (f : ℂ × ℂ→ℂ) : Prop :=
  ∃ γ : ℝ→ℂ × ℂ,∃ F : ℝ→(ℂ × ℂ→ℂ),IsAppellContinuation F γ ∧ γ 0=(0,0) ∧ γ 1=p ∧
    F 0=ᶠ[𝓝 (0,0)] seed ∧ F 1=ᶠ[𝓝 p] f

/-- Appell F1 double-series coefficient. -/
@[dlmf 16.13.E1]
def appF1Coeff (a b b' c : ℂ) (m n : ℕ) : ℂ :=
  poch a (m+n)*poch b m*poch b' n/(poch c (m+n)*(m !*n !))

/-- Appell F2 double-series coefficient. -/
@[dlmf 16.13.E2]
def appF2Coeff (a b b' c c' : ℂ) (m n : ℕ) : ℂ :=
  poch a (m+n)*poch b m*poch b' n/(poch c m*poch c' n*(m !*n !))

/-- Appell F3 double-series coefficient. -/
@[dlmf 16.13.E3]
def appF3Coeff (a a' b b' c : ℂ) (m n : ℕ) : ℂ :=
  poch a m*poch a' n*poch b m*poch b' n/(poch c (m+n)*(m !*n !))

/-- The totalized double series; continuations are represented by analytic germs. -/
@[dlmf 16.13.E1]
def appF1 (a b b' c x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF1Coeff a b b' c p.1 p.2*x^p.1*y^p.2

/-- The totalized double series; continuations are represented by analytic germs. -/
@[dlmf 16.13.E2]
def appF2 (a b b' c c' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF2Coeff a b b' c c' p.1 p.2*x^p.1*y^p.2

/-- The totalized double series; continuations are represented by analytic germs. -/
@[dlmf 16.13.E3]
def appF3 (a a' b b' c x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,appF3Coeff a a' b b' c p.1 p.2*x^p.1*y^p.2

/-- 16.13.E1: hasSum appF1. -/
@[dlmf 16.13.E1]
theorem hasSum_appF1 (a b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ} (hxy : (x,y)∈appellBidisc) :
    HasSum (fun p : ℕ × ℕ => appF1Coeff a b b' c p.1 p.2*x^p.1*y^p.2) (appF1 a b b' c x y) := by
  sorry

/-- 16.13: analytic appF1. -/
@[dlmf 16.13]
theorem analytic_appF1 (a b b' c : ℂ) (hc : AppellRegular c) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF1 a b b' c p.1 p.2) appellBidisc := by
  sorry

/-- 16.13.E2: hasSum appF2. -/
@[dlmf 16.13.E2]
theorem hasSum_appF2 (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') {x y : ℂ} (hxy : (x,y)∈appellDiamond) :
    HasSum (fun p : ℕ × ℕ => appF2Coeff a b b' c c' p.1 p.2*x^p.1*y^p.2) (appF2 a b b' c c' x y) := by
  sorry

/-- 16.13: analytic appF2. -/
@[dlmf 16.13]
theorem analytic_appF2 (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF2 a b b' c c' p.1 p.2) appellDiamond := by
  sorry

/-- 16.13.E3: hasSum appF3. -/
@[dlmf 16.13.E3]
theorem hasSum_appF3 (a a' b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ} (hxy : (x,y)∈appellBidisc) :
    HasSum (fun p : ℕ × ℕ => appF3Coeff a a' b b' c p.1 p.2*x^p.1*y^p.2) (appF3 a a' b b' c x y) := by
  sorry

/-- 16.13: analytic appF3. -/
@[dlmf 16.13]
theorem analytic_appF3 (a a' b b' c : ℂ) (hc : AppellRegular c) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF3 a a' b b' c p.1 p.2) appellBidisc := by
  sorry

/-- 16.13.E4: hasSum appF4. -/
@[dlmf 16.13.E4]
theorem hasSum_appF4 (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') {x y : ℂ} (hxy : (x,y)∈appellF4Domain) :
    HasSum (fun p : ℕ × ℕ => appF4Coeff a b c c' p.1 p.2*x^p.1*y^p.2) (appF4 a b c c' x y) := by
  sorry

/-- 16.13: analytic appF4. -/
@[dlmf 16.13]
theorem analytic_appF4 (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF4 a b c c' p.1 p.2) appellF4Domain := by
  sorry

/-- 16.13.E1: appF1 zero. -/
@[dlmf 16.13.E1]
theorem appF1_zero (a b b' c : ℂ) : appF1 a b b' c 0 0=1 := by
  rw [appF1,appell_tsum_zero]; simp [appF1Coeff,poch_zero]

/-- 16.13.E2: appF2 zero. -/
@[dlmf 16.13.E2]
theorem appF2_zero (a b b' c c' : ℂ) : appF2 a b b' c c' 0 0=1 := by
  rw [appF2,appell_tsum_zero]; simp [appF2Coeff,poch_zero]

/-- 16.13.E3: appF3 zero. -/
@[dlmf 16.13.E3]
theorem appF3_zero (a a' b b' c : ℂ) : appF3 a a' b b' c 0 0=1 := by
  rw [appF3,appell_tsum_zero]; simp [appF3Coeff,poch_zero]

/-- Concrete parameter witnesses make the prose non-product claim mathematically precise. -/
@[dlmf 16.13]
theorem appell_generic_nonseparable :
    (¬∃ f g : ℂ→ℂ,AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      (fun p : ℂ × ℂ => appF1 1 1 1 2 p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => f p.1*g p.2)) ∧
    (¬∃ f g : ℂ→ℂ,AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      (fun p : ℂ × ℂ => appF2 1 1 1 1 1 p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => f p.1*g p.2)) ∧
    (¬∃ f g : ℂ→ℂ,AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      (fun p : ℂ × ℂ => appF3 1 1 1 1 2 p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => f p.1*g p.2)) ∧
    (¬∃ f g : ℂ→ℂ,AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      (fun p : ℂ × ℂ => appF4 1 1 1 1 p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => f p.1*g p.2)) := by
  sorry

/-- 16.14.E1: appF1 pde. -/
@[dlmf 16.14.E1]
theorem appF1_pde (a b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ} (hxy : (x,y)∈appellBidisc) :
    let f := appF1 a b b' c
    x*(1-x)*appellDx (appellDx f) x y+y*(1-x)*appellDx (appellDy f) x y+(c-(a+b+1)*x)*appellDx f x y-b*y*appellDy f x y-a*b*f x y=0 ∧
    y*(1-y)*appellDy (appellDy f) x y+x*(1-y)*appellDx (appellDy f) x y+(c-(a+b'+1)*y)*appellDy f x y-b'*x*appellDx f x y-a*b'*f x y=0 := by
  sorry

/-- 16.14.E2: appF2 pde. -/
@[dlmf 16.14.E2]
theorem appF2_pde (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') {x y : ℂ} (hxy : (x,y)∈appellDiamond) :
    let f := appF2 a b b' c c'
    x*(1-x)*appellDx (appellDx f) x y-x*y*appellDx (appellDy f) x y+(c-(a+b+1)*x)*appellDx f x y-b*y*appellDy f x y-a*b*f x y=0 ∧
    y*(1-y)*appellDy (appellDy f) x y-x*y*appellDx (appellDy f) x y+(c'-(a+b'+1)*y)*appellDy f x y-b'*x*appellDx f x y-a*b'*f x y=0 := by
  sorry

/-- 16.14.E3: appF3 pde. -/
@[dlmf 16.14.E3]
theorem appF3_pde (a a' b b' c : ℂ) (hc : AppellRegular c) {x y : ℂ} (hxy : (x,y)∈appellBidisc) :
    let f := appF3 a a' b b' c
    x*(1-x)*appellDx (appellDx f) x y+y*appellDx (appellDy f) x y+(c-(a+b+1)*x)*appellDx f x y-a*b*f x y=0 ∧
    y*(1-y)*appellDy (appellDy f) x y+x*appellDx (appellDy f) x y+(c-(a'+b'+1)*y)*appellDy f x y-a'*b'*f x y=0 := by
  sorry

/-- 16.14.E4: appF4 pde. -/
@[dlmf 16.14.E4]
theorem appF4_pde (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') {x y : ℂ} (hxy : (x,y)∈appellF4Domain) :
    let f := appF4 a b c c'
    x*(1-x)*appellDx (appellDx f) x y-2*x*y*appellDx (appellDy f) x y-y^2*appellDy (appellDy f) x y+(c-(a+b+1)*x)*appellDx f x y-(a+b+1)*y*appellDy f x y-a*b*f x y=0 ∧
    y*(1-y)*appellDy (appellDy f) x y-2*x*y*appellDx (appellDy f) x y-x^2*appellDx (appellDx f) x y+(c'-(a+b+1)*y)*appellDy f x y-(a+b+1)*x*appellDx f x y-a*b*f x y=0 := by
  sorry

/-- Horn G2 in the gamma-ratio normalization. -/
@[dlmf 16.14.E5]
def hornG2 (a a' b b' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,Gamma (a+p.1)*Gamma (a'+p.2)*Gamma (b+p.2-p.1)*Gamma (b'+p.1-p.2)/
    (Gamma a*Gamma a'*Gamma b*Gamma b'*(p.1 !*p.2 !))*x^p.1*y^p.2

/-- Horn G3 in the gamma-ratio normalization. -/
@[dlmf 16.14.E6]
def hornG3 (a a' x y : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ,Gamma (a+2*p.2-p.1)*Gamma (a'+2*p.1-p.2)/
    (Gamma a*Gamma a'*(p.1 !*p.2 !))*x^p.1*y^p.2

/-- 16.14.E5: hornG2 summable. -/
@[dlmf 16.14.E5]
theorem hornG2_summable (a a' b b' : ℂ) (ha : AppellRegular a) (ha' : AppellRegular a')
    (hb : ∀ k : ℤ,b≠k) (hb' : ∀ k : ℤ,b'≠k) {x y : ℂ} (hxy : (x,y)∈appellBidisc) :
    Summable (fun p : ℕ × ℕ => Gamma (a+p.1)*Gamma (a'+p.2)*Gamma (b+p.2-p.1)*Gamma (b'+p.1-p.2)/
      (Gamma a*Gamma a'*Gamma b*Gamma b'*(p.1 !*p.2 !))*x^p.1*y^p.2) := by
  sorry

/-- 16.14.E6: hornG3 summable. -/
@[dlmf 16.14.E6]
theorem hornG3_summable (a a' : ℂ) (ha : ∀ k : ℤ,a≠k) (ha' : ∀ k : ℤ,a'≠k)
    {x y : ℂ} (hxy : ‖x‖+‖y‖<(1/4:ℝ)) :
    Summable (fun p : ℕ × ℕ => Gamma (a+2*p.2-p.1)*Gamma (a'+2*p.1-p.2)/
      (Gamma a*Gamma a'*(p.1 !*p.2 !))*x^p.1*y^p.2) := by
  sorry

/-- 16.14.ii: hornG2 G3 second order pde. -/
@[dlmf 16.14.ii]
theorem hornG2_G3_second_order_pde (a a' b b' : ℂ) (ha : ∀ k : ℤ,a≠k) (ha' : ∀ k : ℤ,a'≠k)
    (hb : ∀ k : ℤ,b≠k) (hb' : ∀ k : ℤ,b'≠k) {x y : ℂ}
    (hxy : ‖x‖+‖y‖<(1/4:ℝ)) :
    let f := hornG2 a a' b b'
    let g := hornG3 a a'
    appellThetaX (fun x y => b*f x y+appellThetaY f x y-appellThetaX f x y) x y=
      x*(a*b'*f x y+(a+b')*appellThetaX f x y-a*appellThetaY f x y+
        appellThetaX (appellThetaX f) x y-appellThetaX (appellThetaY f) x y) ∧
    appellThetaY (fun x y => b'*f x y+appellThetaX f x y-appellThetaY f x y) x y=
      y*(a'*b*f x y+(a'+b)*appellThetaY f x y-a'*appellThetaX f x y+
        appellThetaY (appellThetaY f) x y-appellThetaX (appellThetaY f) x y) ∧
    appellThetaX (fun x y => a*g x y+2*appellThetaY g x y-appellThetaX g x y) x y=
      x*((a'*(a'+1))*g x y+(4*a'+2)*appellThetaX g x y-(2*a'+1)*appellThetaY g x y+
        4*appellThetaX (appellThetaX g) x y-4*appellThetaX (appellThetaY g) x y+
        appellThetaY (appellThetaY g) x y) ∧
    appellThetaY (fun x y => a'*g x y+2*appellThetaX g x y-appellThetaY g x y) x y=
      y*(a*(a+1)*g x y+(4*a+2)*appellThetaY g x y-(2*a+1)*appellThetaX g x y+
        4*appellThetaY (appellThetaY g) x y-4*appellThetaX (appellThetaY g) x y+
        appellThetaX (appellThetaX g) x y) := by
  sorry

/-- 16.14.ii: hornG3 nonmaximal region. -/
@[dlmf 16.14.ii]
theorem hornG3_nonmaximal_region (a a' : ℂ) (ha : ∀ k : ℤ,a≠k) (ha' : ∀ k : ℤ,a'≠k) :
    ∃ x y : ℂ,(1/4:ℝ)≤‖x‖+‖y‖ ∧
      Summable (fun p : ℕ × ℕ => Gamma (a+2*p.2-p.1)*Gamma (a'+2*p.1-p.2)/
        (Gamma a*Gamma a'*(p.1 !*p.2 !))*x^p.1*y^p.2) := by
  sorry

/-- 16.16: appell continuation unique. -/
@[dlmf 16.16]
theorem appell_continuation_unique {F G : ℝ→(ℂ × ℂ→ℂ)} {γ : ℝ→ℂ × ℂ}
    (hF : IsAppellContinuation F γ) (hG : IsAppellContinuation G γ)
    (h0 : F 0=ᶠ[𝓝 (γ 0)] G 0) : F 1=ᶠ[𝓝 (γ 1)] G 1 := by
  sorry


/-! ## Euler integral branches with actual integrability -/

/-- Natural principal cut plane for the two separate Euler denominator factors. -/
def appellEulerDomain : Set (ℂ × ℂ) := {p | 1-p.1∈slitPlane ∧ 1-p.2∈slitPlane}

/-- The square-integral denominator stays on its principal branch at every integration point. -/
def appellSquareSlit (p : ℂ × ℂ) : Prop :=
  ∀ u∈Icc (0:ℝ) 1,∀ v∈Icc (0:ℝ) 1,1-(u:ℂ)*p.1-(v:ℂ)*p.2∈slitPlane

/-- Euler's integration triangle, including its measure-zero boundary. -/
def appellTriangle : Set (ℝ × ℝ) := {p | 0≤p.1 ∧ 0≤p.2 ∧ p.1+p.2≤1}

/-- The Euler kernel for F1, with all powers principal on their stated domain. -/
def appF1EulerKernel (a b b' c x y : ℂ) (u : ℝ) : ℂ :=
  (u:ℂ)^(a-1)*((1-u:ℝ):ℂ)^(c-a-1)/(1-u*x)^b/(1-u*y)^b'

/-- The Euler kernel for F2. -/
def appF2EulerKernel (a b b' c c' x y : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1:ℂ)^(b-1)*(p.2:ℂ)^(b'-1)*((1-p.1:ℝ):ℂ)^(c-b-1)*
    ((1-p.2:ℝ):ℂ)^(c'-b'-1)/(1-p.1*x-p.2*y)^a

/-- The simplex Euler kernel for F3. -/
def appF3EulerKernel (a a' b b' c x y : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1:ℂ)^(b-1)*(p.2:ℂ)^(b'-1)*((1-p.1-p.2:ℝ):ℂ)^(c-b-b'-1)/
    (1-p.1*x)^a/(1-p.2*y)^a'

/-- The transformed Euler kernel for F4. -/
def appF4EulerKernel (a b c c' x y : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1:ℂ)^(a-1)*(p.2:ℂ)^(b-1)*((1-p.1:ℝ):ℂ)^(c-a-1)*
    ((1-p.2:ℝ):ℂ)^(c'-b-1)/(1-p.1*x)^(c+c'-a-1)/(1-p.2*y)^(c+c'-b-1)/
    (1-p.1*x-p.2*y)^(a+b-c-c'+1)

/-- The Euler integral branch of F1, distinct from its totalized double series. -/
@[dlmf 16.15.E1]
def appF1Euler (a b b' c x y : ℂ) : ℂ :=
  Gamma c/(Gamma a*Gamma (c-a))*∫ u in (0:ℝ)..1,appF1EulerKernel a b b' c x y u

/-- The Euler square-integral branch of F2. -/
@[dlmf 16.15.E2]
def appF2Euler (a b b' c c' x y : ℂ) : ℂ :=
  Gamma c*Gamma c'/(Gamma b*Gamma b'*Gamma (c-b)*Gamma (c'-b'))*
    ∫ p in Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1,appF2EulerKernel a b b' c c' x y p

/-- The Euler simplex-integral branch of F3. -/
@[dlmf 16.15.E3]
def appF3Euler (a a' b b' c x y : ℂ) : ℂ :=
  Gamma c/(Gamma b*Gamma b'*Gamma (c-b-b'))*
    ∫ p in appellTriangle,appF3EulerKernel a a' b b' c x y p

/-- The Euler branch at the transformed arguments x(1-y),y(1-x). -/
@[dlmf 16.15.E4]
def appF4Euler (a b c c' x y : ℂ) : ℂ :=
  Gamma c*Gamma c'/(Gamma a*Gamma b*Gamma (c-a)*Gamma (c'-b))*
    ∫ p in Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1,appF4EulerKernel a b c c' x y p

/-- 16.15.E1: appF1 euler integrable. -/
@[dlmf 16.15.E1]
theorem appF1_euler_integrable (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) {x y : ℂ} (hxy : (x,y)∈appellEulerDomain) :
    IntegrableOn (appF1EulerKernel a b b' c x y) (Icc (0:ℝ) 1) := by
  sorry

/-- 16.15.E1: appF1 euler analytic. -/
@[dlmf 16.15.E1]
theorem appF1_euler_analytic (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF1Euler a b b' c p.1 p.2) appellEulerDomain := by
  sorry

/-- 16.15.E1: appF1 euler germ. -/
@[dlmf 16.15.E1]
theorem appF1_euler_germ (a b b' c : ℂ) (ha : 0<a.re) (hca : 0<(c-a).re) :
    (fun p : ℂ × ℂ => appF1 a b b' c p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => appF1Euler a b b' c p.1 p.2) := by
  sorry

/-- 16.15.E2: appF2 euler integrable. -/
@[dlmf 16.15.E2]
theorem appF2_euler_integrable (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re) (hcb' : b'.re<c'.re) {x y : ℂ} (hxy : (x,y)∈{p | appellSquareSlit p}) :
    IntegrableOn (appF2EulerKernel a b b' c c' x y) (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) := by
  sorry

/-- 16.15.E2: appF2 euler analytic. -/
@[dlmf 16.15.E2]
theorem appF2_euler_analytic (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re) (hcb' : b'.re<c'.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF2Euler a b b' c c' p.1 p.2) {p | appellSquareSlit p} := by
  sorry

/-- 16.15.E2: appF2 euler germ. -/
@[dlmf 16.15.E2]
theorem appF2_euler_germ (a b b' c c' : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hcb : b.re<c.re) (hcb' : b'.re<c'.re) :
    (fun p : ℂ × ℂ => appF2 a b b' c c' p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => appF2Euler a b b' c c' p.1 p.2) := by
  sorry

/-- 16.15.E3: appF3 euler integrable. -/
@[dlmf 16.15.E3]
theorem appF3_euler_integrable (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hrest : 0<(c-b-b').re) {x y : ℂ} (hxy : (x,y)∈appellEulerDomain) :
    IntegrableOn (appF3EulerKernel a a' b b' c x y) appellTriangle := by
  sorry

/-- 16.15.E3: appF3 euler analytic. -/
@[dlmf 16.15.E3]
theorem appF3_euler_analytic (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hrest : 0<(c-b-b').re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF3Euler a a' b b' c p.1 p.2) appellEulerDomain := by
  sorry

/-- 16.15.E3: appF3 euler germ. -/
@[dlmf 16.15.E3]
theorem appF3_euler_germ (a a' b b' c : ℂ) (hb : 0<b.re) (hb' : 0<b'.re) (hrest : 0<(c-b-b').re) :
    (fun p : ℂ × ℂ => appF3 a a' b b' c p.1 p.2)=ᶠ[𝓝 (0,0)] (fun p => appF3Euler a a' b b' c p.1 p.2) := by
  sorry

/-- 16.15.E4: appF4 euler integrable. -/
@[dlmf 16.15.E4]
theorem appF4_euler_integrable (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re) (hcb : b.re<c'.re) {x y : ℂ} (hxy : (x,y)∈{p | appellSquareSlit p}) :
    IntegrableOn (appF4EulerKernel a b c c' x y) (Icc (0:ℝ) 1×ˢIcc (0:ℝ) 1) := by
  sorry

/-- 16.15.E4: appF4 euler analytic. -/
@[dlmf 16.15.E4]
theorem appF4_euler_analytic (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re) (hcb : b.re<c'.re) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => appF4Euler a b c c' p.1 p.2) {p | appellSquareSlit p} := by
  sorry

/-- 16.15.E4: appF4 euler germ. -/
@[dlmf 16.15.E4]
theorem appF4_euler_germ (a b c c' : ℂ) (ha : 0<a.re) (hb : 0<b.re) (hca : a.re<c.re) (hcb : b.re<c'.re) :
    (fun p : ℂ × ℂ => appF4 a b c c' (p.1*(1-p.2)) (p.2*(1-p.1)))=ᶠ[𝓝 (0,0)] (fun p => appF4Euler a b c c' p.1 p.2) := by
  sorry

/-- 16.16.E1: appF1 reduction gauss. -/
@[dlmf 16.16.E1]
theorem appF1_reduction_gauss (a b b' : ℂ) (hc : AppellRegular (b+b')) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF1 a b b' (b+b') x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-a)*₂F₁ a b (b+b') ((x-y)/(1-y))) := by
  sorry

/-- 16.16.E2: appF2 reduction gauss. -/
@[dlmf 16.16.E2]
theorem appF2_reduction_gauss (a b b' c : ℂ) (hc : AppellRegular c) (hb' : AppellRegular b') :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF2 a b b' c b' x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-a)*₂F₁ a b c (x/(1-y))) := by
  sorry

/-- 16.16.E3: appF2 reduction appF1. -/
@[dlmf 16.16.E3]
theorem appF2_reduction_appF1 (a b b' c : ℂ) (hc : AppellRegular c) (ha : AppellRegular a) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF2 a b b' c a x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-b')*appF1 b (a-b') b' c x (x/(1-y))) := by
  sorry

/-- 16.16.E4: appF3 reduction appF1. -/
@[dlmf 16.16.E4]
theorem appF3_reduction_appF1 (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF3 a (c-a) b b' c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(-b')*appF1 a b b' c x (y/(y-1))) := by
  sorry

/-- 16.16.E5: appF3 reduction gauss. -/
@[dlmf 16.16.E5]
theorem appF3_reduction_gauss (a b c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF3 a (c-a) b (c-b) c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-y)^(a+b-c)*₂F₁ a b c (x+y-x*y)) := by
  sorry

/-- 16.16.E5_5: appF4 reduction appF1. -/
@[dlmf 16.16.E5_5]
theorem appF4_reduction_appF1 (a b c : ℂ) (hc : AppellRegular c) (hb : AppellRegular b) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF4 a b c b (x*(1-y)) (y*(1-x)))=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-a)*(1-y)^(-a)*appF1 a (c-b) (a-c+1) c (x/(x-1)) (x*y/((1-x)*(1-y)))) := by
  sorry

/-- 16.16.E6: appF4 product germ. -/
@[dlmf 16.16.E6]
theorem appF4_product_germ (a b c : ℂ) (hc : AppellRegular c) (hc' : AppellRegular (a+b-c+1)) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF4 a b c (a+b-c+1) (x*(1-y)) (y*(1-x)))=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; ₂F₁ a b c x*₂F₁ a b (a+b-c+1) y) := by
  sorry

/-- 16.16.E8: appF1 pfaff first. -/
@[dlmf 16.16.E8]
theorem appF1_pfaff_first (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF1 a b b' c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-b)*(1-y)^(-b')*appF1 (c-a) b b' c (x/(x-1)) (y/(y-1))) := by
  sorry

/-- 16.16.E8: appF1 pfaff second. -/
@[dlmf 16.16.E8]
theorem appF1_pfaff_second (a b b' c : ℂ) (hc : AppellRegular c) :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF1 a b b' c x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-a)*appF1 a (c-b-b') b' c (x/(x-1)) ((y-x)/(1-x))) := by
  sorry

/-- 16.16.E9: appF2 pfaff. -/
@[dlmf 16.16.E9]
theorem appF2_pfaff (a b b' c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    (fun p : ℂ × ℂ => let x:=p.1; let y:=p.2; appF2 a b b' c c' x y)=ᶠ[𝓝 (0,0)]
      (fun p => let x:=p.1; let y:=p.2; (1-x)^(-a)*appF2 a (c-b) b' c c' (x/(x-1)) (y/(1-x))) := by
  sorry

/-- 16.16.E7: appF4 burchnall chaundy. -/
@[dlmf 16.16.E7]
theorem appF4_burchnall_chaundy (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c') :
    ∃ δ>0,∀ x y : ℂ,‖x‖<δ→‖y‖<δ→
      HasSum (fun k : ℕ => poch a k*poch b k*poch (a+b-c-c'+1) k/
        (poch c k*poch c' k*k !)*x^k*y^k*₂F₁ (a+k) (b+k) (c+k) x*
          ₂F₁ (a+k) (b+k) (c'+k) y) (appF4 a b c c' (x*(1-y)) (y*(1-x))) := by
  sorry

/-- The large-variable formula is a branch reached by analytic continuation, not a divergent-series identity. -/
@[dlmf 16.16.E10]
theorem appF4_infinity_connection (a b c c' : ℂ) (hc : AppellRegular c) (hc' : AppellRegular c')
    (hab : ∀ k : ℤ,a-b≠k) {x y : ℂ}
    (hconv : (x/y,1/y)∈appellF4Domain) (hy : -y∈slitPlane) :
    IsAppellBranchAt (fun p : ℂ × ℂ => appF4 a b c c' p.1 p.2) (x,y)
      (fun p => Gamma c'*Gamma (b-a)/(Gamma (c'-a)*Gamma b)*(-p.2)^(-a)*
        appF4 a (a-c'+1) c (a-b+1) (p.1/p.2) (1/p.2)+
        Gamma c'*Gamma (a-b)/(Gamma (c'-b)*Gamma a)*(-p.2)^(-b)*
        appF4 b (b-c'+1) c (b-a+1) (p.1/p.2) (1/p.2)) := by
  sorry

/-- Coalescing exponent parameters require the combined connection expression limit. -/
@[dlmf 16.16.E10]
theorem appF4_infinity_resonance_limits {a b c c' : ℂ} (hc : AppellRegular c) (hc' : AppellRegular c')
    (k : ℤ) (hab : a-b=k) {x y : ℂ} (hconv : (x/y,1/y)∈appellF4Domain) (hy : -y∈slitPlane) :
    ∃ L : ℂ,Tendsto (fun a' : ℂ =>
      Gamma c'*Gamma (b-a')/(Gamma (c'-a')*Gamma b)*(-y)^(-a')*
        appF4 a' (a'-c'+1) c (a'-b+1) (x/y) (1/y)+
      Gamma c'*Gamma (a'-b)/(Gamma (c'-b)*Gamma a')*(-y)^(-b)*
        appF4 b (b-c'+1) c (b-a'+1) (x/y) (1/y)) (𝓝[≠] a) (𝓝 L) := by
  sorry


end DLMF.Hypergeometric
