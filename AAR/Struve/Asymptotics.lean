/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Struve.AngerWeber
public import AAR.Airy.Scorer

/-!
# Struve and Anger–Weber asymptotics

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Struve

open AAR.Bessel AAR.Airy

/-- struveAsymptoticTerm. -/
def struveAsymptoticTerm (ν z : ℂ) (k : ℕ) : ℂ :=
  Gamma (k+1/2)/Gamma (ν+1/2-k)*(z/2)^(ν-2*k-1)/π

/-- struveK asymptotic. -/
@[dlmf 11.6.E1]
theorem struveK_asymptotic (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => struveK ν z-∑ k ∈ Finset.range N, struveAsymptoticTerm ν z k) =O[sector (π-δ)] (fun z : ℂ => z^(ν-2*N-1)) := by
  sorry

/-- struveM asymptotic. -/
@[dlmf 11.6.E2]
theorem struveM_asymptotic (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun z : ℂ => struveM ν z-∑ k ∈ Finset.range N, (-1)^(k+1)*struveAsymptoticTerm ν z k) =O[sector (π/2-δ)] (fun z : ℂ => z^(ν-2*N-1)) := by
  sorry

/-- struveK primitive asymptotic. -/
@[dlmf 11.6.E3]
theorem struveK_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => AAR.DLMF.primitive (struveK 0) z - 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; (-1)^(k+1)*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ))) := by
  sorry

/-- struveM primitive asymptotic. -/
@[dlmf 11.6.E4]
theorem struveM_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun z : ℂ => AAR.DLMF.primitive (struveM 0) z + 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; 1*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector (π/2-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ))) := by
  sorry

/-- struveH large order. -/
@[dlmf 11.6.E5]
theorem struveH_large_order {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => struveH ν z) ~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν))) := by
  sorry

/-- struveL large order. -/
@[dlmf 11.6.E5]
theorem struveL_large_order {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => struveL ν z) ~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν))) := by
  sorry

/-- Finite polynomial formula for the saddle-endpoint coefficients. -/
def struveScaledCoeff (lam : ℂ) (k : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (k+1), if k ≤ 2*j then
    ((2*j).factorial:ℂ)/(j.factorial:ℂ) *
      (∏ r ∈ Finset.range j, (Polynomial.X-Polynomial.C (1/2+r:ℂ))).coeff (2*j-k) /
      lam^(2*j) else 0) / (k.factorial:ℂ)

/-- struveK scaled asymptotic. -/
@[dlmf 11.6.E6]
theorem struveK_scaled_asymptotic {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => Real.sqrt π*Gamma (ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveK ν (lam*ν)-∑ k ∈ Finset.range N, (k.factorial:ℂ)*struveScaledCoeff (lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- struveM scaled asymptotic. -/
@[dlmf 11.6.E7]
theorem struveM_scaled_asymptotic {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => -Real.sqrt π*Gamma (ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveM ν (lam*ν)-∑ k ∈ Finset.range N, (k.factorial:ℂ)*struveScaledCoeff (I*lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- struveScaledCoeff initial. -/
@[dlmf 11.6.E8]
theorem struveScaledCoeff_initial (lam : ℂ) (hlam : lam ≠ 0) :
    struveScaledCoeff lam 0=1 ∧ struveScaledCoeff lam 1=2/(lam:ℂ)^2 ∧ struveScaledCoeff lam 2=6/(lam:ℂ)^4-1/(2*(lam:ℂ)^2) ∧ struveScaledCoeff lam 3=20/(lam:ℂ)^6-4/(lam:ℂ)^4 ∧ struveScaledCoeff lam 4=70/(lam:ℂ)^8-45/(2*(lam:ℂ)^6)+3/(8*(lam:ℂ)^4) := by
  sorry

/-- struveL scaled equiv. -/
@[dlmf 11.6.E9]
theorem struveL_scaled_equiv {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) :
    (fun ν : ℂ => struveL ν (lam*ν)) ~[sector (π/2-δ)] (fun ν => besselI ν (lam*ν)) := by
  sorry

/-- First omitted term bounds the real positive-argument remainder. -/
theorem struveK_remainder_sign {ν x : ℝ} (hx : 0 < x) (m : ℕ) (hm : ν ≤ m+1/2) :
    let R := struveK ν x-∑ k ∈ Finset.range m, struveAsymptoticTerm ν x k; R.im=0 ∧ R.re*(struveAsymptoticTerm ν x m).re ≥ 0 ∧ ‖R‖ ≤ ‖struveAsymptoticTerm ν x m‖ := by
  sorry

/-- angerF. -/
@[dlmf 11.11.E1]
def angerF (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (ν^2-(2*j+1)^2)

/-- angerG. -/
@[dlmf 11.11.E1]
def angerG (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (ν^2-(2*j+2)^2)

/-- angerFG poch. -/
@[dlmf 11.11.E1]
theorem angerFG_poch (ν : ℂ) (k : ℕ) :
    angerF ν k = (-4)^k*poch (1/2-ν/2) k*poch (1/2+ν/2) k ∧ angerG ν k = (-4)^k*poch (1-ν/2) k*poch (1+ν/2) k := by
  induction k with
  | zero => simp [angerF, angerG, poch_zero]
  | succ k ih =>
    rcases ih with ⟨ihF, ihG⟩
    have hF : angerF ν (k+1)=angerF ν k*(ν^2-(2*k+1)^2) := by
      simp [angerF, Finset.prod_range_succ]
    have hG : angerG ν (k+1)=angerG ν k*(ν^2-(2*k+2)^2) := by
      simp [angerG, Finset.prod_range_succ]
    rw [hF,hG,ihF,ihG,poch_succ,poch_succ,poch_succ,poch_succ,pow_succ]
    push_cast
    constructor <;> ring

/-- angerJ large argument. -/
@[dlmf 11.11.E2]
theorem angerJ_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerJ ν z-besselJ ν z-(∑ k ∈ Finset.range N, sin (π*ν)/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  sorry

/-- weberE large argument. -/
@[dlmf 11.11.E3]
theorem weberE_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => weberE ν z+besselY ν z-(∑ k ∈ Finset.range N, -(1+cos (π*ν))/π*angerF ν k/z^(2*k+1)-ν*(1-cos (π*ν))/π*angerG ν k/z^(2*k+2))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  sorry

/-- angerA large argument. -/
@[dlmf 11.11.E4]
theorem angerA_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerA ν z-(∑ k ∈ Finset.range N, 1/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  sorry

/-- Large orders separated from all integers. -/
def nonintegerOrderSector (ε : ℝ) : Filter ℂ :=
  sector π ⊓ 𝓟 {ν : ℂ | ∀ n : ℤ, ε ≤ ‖ν-n‖}

/-- angerJ large order. -/
@[dlmf 11.11.E5]
theorem angerJ_large_order (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun ν : ℂ => π*ν/sin (π*ν)*angerJ ν z-1+ν*z/(ν^2-1)) =O[nonintegerOrderSector ε] (fun ν : ℂ => ν^(-2:ℤ)) := by
  sorry

/-- weberE large order. -/
@[dlmf 11.11.E6]
theorem weberE_large_order (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun ν : ℂ => π*ν/2*weberE ν z-(sin (π*ν/2))^2-ν*z/(ν^2-1)*(cos (π*ν/2))^2) =O[nonintegerOrderSector ε] (fun ν : ℂ => ν^(-2:ℤ)) := by
  sorry

/-- weberE large integer 0. -/
@[dlmf 11.11.E7]
theorem weberE_large_integer_0 (z : ℂ) :
    (fun n : ℤ => weberE (2*n+0) z) ~[comap (fun n : ℤ => |n|) atTop] (fun n => 2*z/((4*(n:ℂ)^2-1)*π)) := by
  sorry

/-- weberE large integer 1. -/
@[dlmf 11.11.E7]
theorem weberE_large_integer_1 (z : ℂ) :
    (fun n : ℤ => weberE (2*n+1) z) ~[comap (fun n : ℤ => |n|) atTop] (fun n => 2/((2*n+1:ℂ)*π)) := by
  sorry

/-- Coefficients in the scaled Anger–Weber expansion. -/
def angerScaledA : ℕ → ℂ → ℂ
  | 0 => fun lam => 1/(1+lam)
  | k+1 => fun lam => limUnder (𝓝[≠] lam) (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/((2*k+1:ℂ)*(2*k+2)))

/-- angerScaledA initial. -/
@[dlmf 11.11.E9]
theorem angerScaledA_initial (lam : ℂ) (h : lam ≠ -1) :
    angerScaledA 1 lam = -lam/(2*(1+lam)^4) ∧ angerScaledA 2 lam = (9*lam^2-lam)/(24*(1+lam)^7) ∧ angerScaledA 3 lam = -(225*lam^3-54*lam^2+lam)/(720*(1+lam)^10) := by
  sorry

/-- angerA scaled 8. -/
@[dlmf 11.11.E8]
theorem angerA_scaled_8 {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => angerA (1*ν) (lam*ν)-(1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (1*lam)/ν^(2*k+1)) =O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ))) := by
  sorry

/-- angerA scaled 10. -/
@[dlmf 11.11.E10]
theorem angerA_scaled_10 {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => angerA (-1*ν) (lam*ν)-(-1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (-1*lam)/ν^(2*k+1)) =O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ))) := by
  sorry

/-- angerMu. -/
@[dlmf 11.11.E12]
def angerMu (lam : ℂ) : ℂ :=
  (1-lam^2)^(1/2:ℂ)-log ((1+(1-lam^2)^(1/2:ℂ))/lam)

/-- Coefficients of the saddle expansion, with existence provided by the expansion theorem. -/
def angerScaledB (lam : ℝ) (k : ℕ) : ℂ :=
  asymptoticCoeff (fun v : ℝ => ((π*v/2:ℂ)^(1/2:ℂ))*exp (v*angerMu lam)*angerA (-v) (lam*v)) k / poch (1/2) k

/-- angerA scaled saddle. -/
@[dlmf 11.11.E11]
theorem angerA_scaled_saddle {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => (π*ν/2)^(1/2:ℂ)*exp (ν*angerMu lam)*angerA (-ν) (lam*ν)-∑ k ∈ Finset.range N, poch (1/2) k*angerScaledB lam k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- angerScaledB initial. -/
@[dlmf 11.11.E13]
theorem angerScaledB_initial {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    angerScaledB lam 0 = (1-lam^2:ℂ)^(-1/4:ℂ) ∧ angerScaledB lam 1 = (2+3*lam^2:ℂ)/(12*(1-lam^2:ℂ)^(7/4:ℂ)) ∧ angerScaledB lam 2 = (4+300*lam^2+81*lam^4:ℂ)/(864*(1-lam^2:ℂ)^(13/4:ℂ)) := by
  sorry

/-- angerA scaled outer equiv. -/
@[dlmf 11.11.E14]
theorem angerA_scaled_outer_equiv {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerA (-ν) (lam*ν)) ~[sector (π-δ)] (fun ν => 1/(π*ν*(lam-1))) := by
  sorry

/-- angerA scaled inner equiv. -/
@[dlmf 11.11.E15]
theorem angerA_scaled_inner_equiv {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) :
    (fun ν : ℂ => angerA (-ν) (lam*ν)) ~[sector (π/2-δ)] (fun ν => (2/(π*ν))^(1/2:ℂ)*exp (-ν*angerMu lam)/(1-lam^2:ℂ)^(1/4:ℂ)) := by
  sorry

/-- angerA turning equiv. -/
@[dlmf 11.11.E16]
theorem angerA_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerA (-ν) ν) ~[sector (π-δ)] (fun ν => 2^(4/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  sorry

/-- angerJ turning equiv. -/
@[dlmf 11.11.E18]
theorem angerJ_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerJ ν ν) ~[sector (π-δ)] (fun ν => 2^(1/3:ℂ)/(3^(2/3:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  sorry

/-- weberE turning equiv. -/
@[dlmf 11.11.E19]
theorem weberE_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => weberE ν ν) ~[sector (π-δ)] (fun ν => 2^(1/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  sorry

/-- Turning-point approximation uniform on bounded complex transition parameters; positive real order. -/
@[dlmf 11.11.E17]
theorem angerA_turning_uniform (M : ℝ) (hM : 0 < M) :
    (fun p : ℝ × ℂ => angerA (-p.1) (p.1+p.2*(p.1:ℂ)^(1/3:ℂ))-2^(1/3:ℂ)*(p.1:ℂ)^(-1/3:ℂ)*scorerHi (-2^(1/3:ℂ)*p.2)) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℂ | ‖p.2‖ ≤ M}] (fun p : ℝ × ℂ => (p.1:ℂ)^(-1:ℤ)) := by
  sorry

/-- The recurrence in DLMF 11.11(iii) has a removable singularity at lambda=1. -/
theorem angerScaledA_removable (k : ℕ) {lam : ℂ} (hlam : lam ≠ -1) :
    Tendsto (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/((2*k+1:ℂ)*(2*k+2)))
      (𝓝[≠] lam) (𝓝 (angerScaledA (k+1) lam)) := by
  sorry

/-- The convergent defining H series is also a generalized large-order expansion, DLMF 11.6(ii). -/
theorem struveH_large_order_expansion {z : ℂ} (hz : z ∈ slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => struveH ν z-(z/2)^(ν+1)*∑ n ∈ Finset.range N,
      (-1)^n*(z/2)^(2*n)*struveCoeff ν n) =O[sector (π-δ)]
      (fun ν : ℂ => (z/2)^(ν+1)/Gamma (ν+N+3/2)) := by
  sorry

/-- The corresponding generalized L expansion in DLMF 11.6(ii). -/
theorem struveL_large_order_expansion {z : ℂ} (hz : z ∈ slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => struveL ν z-(z/2)^(ν+1)*∑ n ∈ Finset.range N,
      (z/2)^(2*n)*struveCoeff ν n) =O[sector (π-δ)]
      (fun ν : ℂ => (z/2)^(ν+1)/Gamma (ν+N+3/2)) := by
  sorry

end AAR.Struve
