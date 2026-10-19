/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import AAR.Legendre.Conical
public import AAR.ParabolicCylinder.WeberUniform

/-!
# Coordinate changes and envelopes for Legendre uniform approximations

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

open AAR.Bessel AAR.Confluent

/-- legendreOrderAlpha. -/
@[dlmf 14.15.E5]
def legendreOrderAlpha (ν μ : ℝ) : ℝ :=
  (ν+1/2)/μ

/-- legendreOrderP. -/
@[dlmf 14.15.E6]
def legendreOrderP (α x : ℝ) : ℝ :=
  x/Real.sqrt (α^2*x^2+1-α^2)

/-- legendreOrderRho. -/
@[dlmf 14.15.E7]
def legendreOrderRho (α x : ℝ) : ℝ :=
  let p:=legendreOrderP α x; Real.log ((1+p)/(1-p))/2+α/2*Real.log ((1-α*p)/(1+α*p))

/-- LegendreEtaRelation. -/
@[dlmf 14.15.E10]
def LegendreEtaRelation (α x η : ℝ) : Prop :=
  α*Real.log (Real.sqrt (α^2+η^2)+α)-α*Real.log η-Real.sqrt (α^2+η^2) = Real.log (((1+α^2)*x^2+1-α^2-2*x*Real.sqrt (α^2*x^2-α^2+1))/((x^2-1)*(1-α^2)))/2+α/2*Real.log ((α^2*(2*x^2-1)+1+2*α*x*Real.sqrt (α^2*x^2-α^2+1))/(1-α^2))

/-- legendreOrderEta. -/
@[dlmf 14.15.E10]
def legendreOrderEta (α x : ℝ) : ℝ :=
  Classical.epsilon (fun η : ℝ => 0 < η ∧ LegendreEtaRelation α x η)

/-- legendreOrderEta spec. -/
@[dlmf 14.15.E10]
theorem legendreOrderEta_spec {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 1 < x) :
    0 < legendreOrderEta α x ∧ LegendreEtaRelation α x (legendreOrderEta α x) ∧ ∀ η : ℝ, 0 < η → LegendreEtaRelation α x η → η=legendreOrderEta α x := by
  sorry

/-- One-to-one correspondence and endpoint behavior in DLMF 14.15(ii). -/
theorem legendreOrderEta_bijective {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    Set.BijOn (legendreOrderEta α) (Ioi 1) (Ioi 0) ∧ StrictAntiOn (legendreOrderEta α) (Ioi 1) ∧ Tendsto (legendreOrderEta α) (𝓝[>] 1) atTop ∧ Tendsto (legendreOrderEta α) atTop (𝓝 0) := by
  sorry

/-- legendreDegreeAlpha. -/
@[dlmf 14.15.E19]
def legendreDegreeAlpha (ν μ : ℝ) : ℝ :=
  μ/(ν+1/2)

/-- legendreDegreeBeta. -/
@[dlmf 14.15.E20]
def legendreDegreeBeta (ν μ : ℝ) : ℝ :=
  Real.exp μ*((ν-μ+1/2)/(ν+μ+1/2))^(ν/2+1/4)*((ν+1/2)^2-μ^2)^(-μ/2)

/-- LegendreYRelation. -/
@[dlmf 14.15.E21, dlmf 14.15.E22]
def LegendreYRelation (α x y : ℝ) : Prop :=
  if x=1 then y=0 else if x ≤ Real.sqrt (1-α^2) then α^2 ≤ y ∧ Real.sqrt (y-α^2)-α*Real.arctan (Real.sqrt (y-α^2)/α)=Real.arccos (x/Real.sqrt (1-α^2))-α/2*Real.arccos (((1+α^2)*x^2-1+α^2)/((1-α^2)*(1-x^2))) else y ≤ α^2 ∧ Real.sqrt (α^2-y)+α/2*Real.log |y|-α*Real.log (Real.sqrt (α^2-y)+α)=Real.log ((x+Real.sqrt (x^2-1+α^2))/Real.sqrt (1-α^2))+α/2*Real.log ((1-α^2)*|1-x^2|/((1+α^2)*x^2-1+α^2+2*α*x*Real.sqrt (x^2-1+α^2)))

/-- legendreDegreeY. -/
def legendreDegreeY (α x : ℝ) : ℝ :=
  Classical.epsilon (LegendreYRelation α x)

/-- legendreDegreeY spec. -/
@[dlmf 14.15.E21, dlmf 14.15.E22]
theorem legendreDegreeY_spec {α x : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) (hx : 0 ≤ x) :
    LegendreYRelation α x (legendreDegreeY α x) ∧ ∀ y : ℝ, LegendreYRelation α x y → y=legendreDegreeY α x := by
  sorry

/-- Mapping and endpoint properties in DLMF 14.15(iv). -/
theorem legendreDegreeY_monotone {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1) :
    StrictAntiOn (legendreDegreeY α) (Ici 0) ∧ legendreDegreeY α (Real.sqrt (1-α^2))=α^2 ∧ legendreDegreeY α 1=0 ∧ Tendsto (legendreDegreeY α) atTop atBot := by
  sorry

/-- Removable turning-point amplitude, including x=sqrt(1-alpha squared). -/
def legendreDegreeAmplitude (α x : ℝ) : ℝ :=
  limUnder (𝓝[≠] x) (fun t : ℝ => ((legendreDegreeY α t-α^2)/(1-α^2-t^2))^(1/4:ℝ))

/-- First positive crossing used in DLMF 2.8(iv). -/
def besselEnvelopeCross (ν : ℝ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ besselJ ν x+besselY ν x=0}

/-- Exact Bessel envelopes from DLMF 2.8.33–34, used in 14.15. -/
def legendreBesselEnvelope (second : Bool) (ν x : ℝ) : ℝ :=
  if x ≤ besselEnvelopeCross ν then Real.sqrt 2*(if second then ‖besselY ν x‖ else (besselJ ν x).re) else Real.sqrt (‖besselJ ν x‖^2+‖besselY ν x‖^2)

/-- cylinderEnvelopeCross. -/
@[dlmf 14.15.E23]
def cylinderEnvelopeCross (c : ℝ) : ℝ :=
  sSup {x : ℝ | 0 < x ∧ pcfU (-c) x=pcfUBar (-c) x}

/-- legendreCylinderEnvelope. -/
@[dlmf 14.15.E23]
def legendreCylinderEnvelope (barred : Bool) (c x : ℝ) : ℝ :=
  if x ≤ cylinderEnvelopeCross c then Real.sqrt (‖pcfU (-c) x‖^2+‖pcfUBar (-c) x‖^2) else Real.sqrt 2*(if barred then (pcfUBar (-c) x).re else (pcfU (-c) x).re)

/-- legendreCylinderA. -/
@[dlmf 14.15.E26]
def legendreCylinderA (ν μ : ℝ) : ℝ :=
  Real.sqrt ((ν+μ+1/2)*|ν-μ+1/2|)/(ν+1/2)

/-- legendreCylinderAlpha. -/
@[dlmf 14.15.E26]
def legendreCylinderAlpha (ν μ : ℝ) : ℝ :=
  Real.sqrt (2*|ν-μ+1/2|/(ν+1/2))

/-- LegendreCylinderRelation. -/
@[dlmf 14.15.E27, dlmf 14.15.E28, dlmf 14.15.E29, dlmf 14.15.E31]
def LegendreCylinderRelation (ν μ x ζ : ℝ) : Prop :=
  let a:=legendreCylinderA ν μ; let α:=legendreCylinderAlpha ν μ; if a=0 then ζ^2=-Real.log (1-x^2) ∧ 0 ≤ x*ζ else if μ ≤ ν+1/2 then if x = -a then ζ = -α else if a ≤ x then α ≤ ζ ∧ ζ*Real.sqrt (ζ^2-α^2)/2-α^2/2*Real.arcosh (ζ/α)=Real.sqrt (1-a^2)*Real.artanh (Real.sqrt ((x^2-a^2)/(1-a^2))/x)-Real.arcosh (x/a) else |ζ| ≤ α ∧ α^2/2*Real.arcsin (ζ/α)+ζ/2*Real.sqrt (α^2-ζ^2)=Real.arcsin (x/a)-Real.sqrt (1-a^2)*Real.arctan (x*Real.sqrt ((1-a^2)/(a^2-x^2))) else ζ*Real.sqrt (ζ^2+α^2)/2+α^2/2*Real.arsinh (ζ/α)=Real.sqrt (1+a^2)*Real.artanh (x*Real.sqrt ((1+a^2)/(x^2+a^2)))-Real.arsinh (x/a)

/-- legendreCylinderZeta. -/
def legendreCylinderZeta (ν μ x : ℝ) : ℝ :=
  Classical.epsilon (LegendreCylinderRelation ν μ x)

/-- legendreCylinderZeta spec. -/
@[dlmf 14.15.E27, dlmf 14.15.E28, dlmf 14.15.E29, dlmf 14.15.E31]
theorem legendreCylinderZeta_spec {ν μ x : ℝ} (hν : -1/2 < ν) (hμ : 0 < μ) (hx : x ∈ Ioo (-1:ℝ) 1) (hdom : μ ≤ ν+1/2 → -legendreCylinderA ν μ ≤ x) :
    LegendreCylinderRelation ν μ x (legendreCylinderZeta ν μ x) ∧ ∀ ζ : ℝ, LegendreCylinderRelation ν μ x ζ → ζ=legendreCylinderZeta ν μ x := by
  sorry

/-- legendreCylinderAmplitude. -/
def legendreCylinderAmplitude (ν μ x : ℝ) : ℝ :=
  limUnder (𝓝[≠] x) (fun t : ℝ => let a:=legendreCylinderA ν μ; let α:=legendreCylinderAlpha ν μ; let ζ:=legendreCylinderZeta ν μ t; if μ ≤ ν+1/2 then ((ζ^2-α^2)/(t^2-a^2))^(1/4:ℝ) else ((ζ^2+α^2)/(t^2+a^2))^(1/4:ℝ))

/-- Uniform approach in the large first parameter, with both other parameters varying. -/
def legendreUniformFilter (S : Set (ℝ × ℝ × ℝ)) : Filter (ℝ × ℝ × ℝ) :=
  comap Prod.fst atTop ⊓ 𝓟 S

/-- Existence of the first positive Bessel crossing used by the envelopes. -/
theorem besselEnvelopeCross_spec {ν : ℝ} (hν : 0 ≤ ν) :
    0 < besselEnvelopeCross ν ∧
      besselJ ν (besselEnvelopeCross ν)+AAR.Bessel.besselY ν (besselEnvelopeCross ν)=0 ∧
      ∀ x : ℝ, 0 < x → x < besselEnvelopeCross ν → besselJ ν x+AAR.Bessel.besselY ν x ≠ 0 := by
  sorry

/-- DLMF 14.15(v): the last positive crossing defining the cylinder envelopes exists. -/
@[dlmf 14.15.E23]
theorem cylinderEnvelopeCross_spec {c : ℝ} (hc : 0 ≤ c) :
    0 < cylinderEnvelopeCross c ∧
      AAR.Confluent.pcfU (-c) (cylinderEnvelopeCross c)=AAR.Confluent.pcfUBar (-c) (cylinderEnvelopeCross c) ∧
      ∀ x : ℝ, cylinderEnvelopeCross c < x → AAR.Confluent.pcfU (-c) x ≠ AAR.Confluent.pcfUBar (-c) x := by
  sorry

end AAR.Legendre
