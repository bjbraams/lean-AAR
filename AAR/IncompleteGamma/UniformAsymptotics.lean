/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.Asymptotics
public import AAR.Gamma.Asymptotics

/-!
# Uniform incomplete-Gamma expansions and inversion, DLMF §8.12

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat ENNReal
namespace AAR.Confluent

open AAR.Statistical

/-- Scaled Gamma Γ*, as in DLMF 5.11.3; the retired 8.18.13 points there. -/
def gammaScaled (z : ℂ) : ℂ :=
  Gamma z/((2*π : ℂ)^(1/2 : ℂ)*exp ((z-1/2)*log z-z))

/-- The Stirling coefficients g_k from the actual scaled Gamma expansion. -/
def gammaStirlingCoeff (k : ℕ) : ℂ :=
  asymptoticCoeff (fun t : ℝ => gammaScaled t) k

/-- Nonvanishing analytic factor used to choose the continuous square root. -/
def gammaEtaFactor (w : ℂ) : ℂ :=
  if w=0 then 1 else 2*(exp w-1-w)/w^2

/-- η on the logarithmic λ-plane, normalized by η~log λ~λ-1 at λ=1. -/
@[dlmf 8.12.E1]
def gammaUniformEtaOnLog (w : ℂ) : ℂ :=
  w*exp (primitive (fun t => deriv gammaEtaFactor t/gammaEtaFactor t) w/2)

/-- gammaUniformEta equation. -/
@[dlmf 8.12.E2]
theorem gammaUniformEta_equation {w : ℂ} (hw : |w.im| < 2*π) :
    gammaUniformEtaOnLog w^2/2=exp w-1-w := by
  sorry

/-- gammaUniformEta derivative. -/
@[dlmf 8.12.E2]
theorem gammaUniformEta_derivative {w : ℂ} (hw : |w.im| < 2*π) (hw0 : w ≠ 0) :
    HasDerivAt gammaUniformEtaOnLog ((exp w-1)/gammaUniformEtaOnLog w) w := by
  sorry

/-- gammaUniformEta normalization. -/
@[dlmf 8.12.E1]
theorem gammaUniformEta_normalization  :
    HasDerivAt gammaUniformEtaOnLog 1 0 ∧ gammaUniformEtaOnLog 0=0 := by
  sorry

/-- The exact S remainder, with w the logarithm of λ. -/
@[dlmf 8.12.E4]
def gammaUniformS (a w : ℂ) : ℂ :=
  normIncGammaQOnLog a (log a+w)-erfc (gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))/2

/-- The exact T remainder with the removable integer-parameter quotient cancelled. -/
def gammaUniformT (a w : ℂ) : ℂ :=
  I*(-exp (π*I*a)*Gamma (a+1)/(2*π*I)*upperIncGammaOnLog (-a) (log a+w+π*I)-erfc (I*gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))/2)

/-- gammaUniformP identity. -/
@[dlmf 8.12.E3]
theorem gammaUniformP_identity (a w : ℂ) :
    normIncGammaPOnLog a (log a+w)=erfc (-gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))/2-gammaUniformS a w := by
  have h : ∀ u : ℂ, erfc (-u) + erfc u = 2 := by
    intro u; simp only [erfc, erf, neg_sq]; ring
  have := h (gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))
  rw [gammaUniformS, normIncGammaQOnLog, neg_mul]
  linear_combination -this/2

/-- Points of the slit plane are not poles of `Γ(a+1)`. -/
lemma slitPlane_add_one_ne_neg_nat {a : ℂ} (ha : a ∈ slitPlane) : ∀ n : ℕ, a+1 ≠ -n := by
  intro n h
  have : a = ((-((n:ℝ)+1) : ℝ) : ℂ) := by push_cast; linear_combination h
  rw [this, ofReal_mem_slitPlane] at ha
  linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]

/-- The reflection formula cancels the source quotient by sin(πa), including integral a. -/
@[dlmf 8.12.E5]
theorem gammaUniformQ_negative_identity {a : ℂ} (ha : a ∈ slitPlane) {w : ℂ} (hw : |w.im| < 2*π) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    -exp (ε*π*I*a)*Gamma (a+1)/(2*π*I)*upperIncGammaOnLog (-a) (log a+w+ε*π*I)=ε/2*erfc (ε*I*gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))-I*gammaUniformT a w := by
  have hG := Gamma_ne_zero (slitPlane_add_one_ne_neg_nat ha)
  rcases hε with rfl | rfl
  · simp only [gammaUniformT]
    push_cast
    ring_nf; rw [I_sq]; ring
  · have hj := upperIncGammaOnLog_jump (-a) (log a+w)
    rw [show 1-(-a)=a+1 by ring] at hj
    have he : ∀ u : ℂ, erfc (-u) + erfc u = 2 := by
      intro u; simp only [erfc, erf, neg_sq]; ring
    have h2 := he (I*gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))
    simp only [gammaUniformT]
    push_cast
    rw [show log a+w+-1*π*I=log a+w-π*I by ring]
    have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp at hj
    field_simp
    ring_nf
    ring_nf at hj h2
    have hI3 : I^3 = -I := by rw [pow_succ, I_sq]; ring
    rw [hI3]
    linear_combination hj + π*I*h2
      - Gamma (1+a)*exp (π*I*a)*upperIncGammaOnLog (-a) (π*I+log a+w)*I_sq

/-- gammaUniform scIncGamma identity. -/
@[dlmf 8.12.E6]
theorem gammaUniform_scIncGamma_identity {a : ℂ} (ha : a ∈ slitPlane) {w : ℂ} (hw : |w.im| < 2*π) :
    exp (-a*(log a+w))*scIncGamma (-a) (-a*exp w)=cos (π*a)-2*sin (π*a)*(exp (a*gammaUniformEtaOnLog w^2/2)/Real.sqrt π*dawsonF (gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ))+gammaUniformT a w) := by
  have ha0 : a ≠ 0 := slitPlane_ne_zero ha
  have hev : exp (log a+w)=a*exp w := by rw [Complex.exp_add, Complex.exp_log ha0]
  by_cases hint : ∃ n : ℕ, a = n
  · obtain ⟨n, rfl⟩ := hint
    have hs : Complex.sin (π*n)=0 := by
      rw [Complex.sin_eq_zero_iff]; exact ⟨n, by push_cast; ring⟩
    have hc : Complex.cos (π*n)=(-1)^n := by
      rw [show (π:ℂ)*n=((n*π:ℝ):ℂ) by push_cast; ring, ← ofReal_cos, Real.cos_nat_mul_pi]; push_cast; rfl
    rw [hs, hc, scIncGamma_neg_nat, mul_pow, neg_pow, show -(n:ℂ)*(log n+w)=-(n*(log n+w)) by ring,
      Complex.exp_neg, show (n:ℂ)*(log n+w)=(n:ℕ)*(log n+w) by rfl, Complex.exp_nat_mul, hev]
    have : (n:ℂ)*exp w ≠ 0 := mul_ne_zero ha0 (Complex.exp_ne_zero w)
    field_simp
    ring
  push Not at hint
  have hreg : ∀ n : ℕ, -a ≠ -n := fun n h => hint n (neg_inj.mp h)
  have hreg1 := slitPlane_add_one_ne_neg_nat ha
  have hs : Complex.sin (π*a) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    have hk' : a = k := mul_left_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) (by rw [hk]; ring)
    rcases Int.eq_nat_or_neg k with ⟨j, rfl | rfl⟩
    · exact hint j (by simpa using hk')
    · have : a = ((-(j:ℝ)) : ℝ) := by rw [hk']; push_cast; ring
      rw [this, ofReal_mem_slitPlane] at ha
      linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hU := upperIncGammaOnLog_halfTurn (log a+w) hreg (ε := 1) (Or.inl rfl)
  rw [hev] at hU
  have hr := Complex.Gamma_mul_Gamma_one_sub (-a)
  rw [show 1-(-a)=a+1 by ring, show (π:ℂ)*(-a)=-(π*a) by ring, Complex.sin_neg] at hr
  have herf : erf (I*(gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)))
      =2/Real.sqrt π*I*exp (a*gammaUniformEtaOnLog w^2/2)*dawsonF (gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)) := by
    set u := gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)
    have hu2 : u^2=a*gammaUniformEtaOnLog w^2/2 := by
      simp only [u, mul_pow]
      rw [show (1/2:ℂ)=(2:ℂ)⁻¹ by norm_num]
      have := Complex.cpow_ofNat_inv_pow (a/2) 2
      rw [this]; ring
    have he : erf (I*u)=2/Real.sqrt π*I*primitive (fun t => exp (t^2)) u := by
      rw [erf_complex_segment_integral]
      simp only [primitive, segmentIntegral, sub_zero, zero_add]
      have harg (t : ℝ) : -((t:ℂ)*(I*u))^2=((t:ℂ)*u)^2 := by simp [mul_pow, I_sq]
      simp_rw [harg]
      ring
    have hx : exp (u^2)*exp (-u^2)=1 := by rw [← Complex.exp_add]; simp
    rw [he, dawsonF, ← hu2]
    linear_combination (-(2/Real.sqrt π*I*primitive (fun t => exp (t^2)) u))*hx
  simp only [gammaUniformT, erfc]
  rw [show I*gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)=I*(gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)) by ring,
    herf, show log a+w+π*I=log a+w+((1:ℝ):ℂ)*π*I by push_cast; ring, hU]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hcs : Complex.cos (π*a)+I*Complex.sin (π*a)=exp (π*I*a) := by
    rw [show (π:ℂ)*I*a=(π*a)*I by ring, Complex.exp_mul_I]; ring
  have hee : exp (-a*(log a+w)+(1:ℝ)*π*I*(-a))=exp (-a*(log a+w))*exp (-(π*I*a)) := by
    rw [← Complex.exp_add]; push_cast; ring_nf
  have hpm : exp (π*I*a)*exp (-(π*I*a))=1 := by rw [← Complex.exp_add]; simp
  have hG1 := Gamma_ne_zero hreg1
  have hGm : Gamma (-a)=-π/(Complex.sin (π*a)*Gamma (a+1)) := by
    rw [eq_div_iff (mul_ne_zero hs hG1)]; rw [eq_div_iff (neg_ne_zero.mpr hs)] at hr
    linear_combination -hr
  rw [hee, hGm, neg_mul a (exp w), ← hcs]
  rw [← hcs] at hpm
  have hs' : Complex.sin (a*π) ≠ 0 := by rwa [mul_comm]
  have hpm' : (Complex.cos (a*π)+Complex.sin (a*π)*I)*exp (-(a*π*I))=1 := by
    rw [← hpm]; ring_nf
  field_simp
  linear_combination (-(Real.sqrt π:ℂ)*exp (-(a*(log a+w)))*scIncGamma (-a) (-(a*exp w)))*hpm'
    + Complex.sin (a*π)*(2*exp (a*gammaUniformEtaOnLog w^2/2)*dawsonF (gammaUniformEtaOnLog w*(a/2)^(1/2 : ℂ)))*I_sq

/-- Uniform coefficients, with removable singularities filled by limits at w=0. -/
@[dlmf 8.12.E9, dlmf 8.12.E10]
def gammaUniformC : ℕ → ℂ → ℂ
  | 0, w => if w=0 then -1/3 else 1/(exp w-1)-1/gammaUniformEtaOnLog w
  | k+1, w => if w=0 then limUnder (𝓝[≠] (0 : ℂ))
      (fun t => deriv (gammaUniformC k) t/(exp t-1)+(-1 : ℂ)^(k+1)*gammaStirlingCoeff (k+1)/(exp t-1))
    else deriv (gammaUniformC k) w/(exp w-1)+(-1 : ℂ)^(k+1)*gammaStirlingCoeff (k+1)/(exp w-1)

/-- gammaUniformC first. -/
@[dlmf 8.12.E9]
theorem gammaUniformC_first {w : ℂ} (hw : |w.im| < 2*π) (hw0 : w ≠ 0) :
    gammaUniformC 0 w=1/(exp w-1)-1/gammaUniformEtaOnLog w ∧ gammaUniformC 1 w=1/gammaUniformEtaOnLog w^3-1/(exp w-1)^3-1/(exp w-1)^2-1/(12*(exp w-1)) := by
  sorry

/-- Uniform large-a filter with independently bounded log arguments of a and λ. -/
def gammaUniformFilter (α β : ℝ) : Filter (ℂ × ℂ) :=
  comap (fun p : ℂ × ℂ => Real.exp p.1.re) atTop ⊓ 𝓟 {p : ℂ × ℂ | |p.1.im| ≤ α ∧ |p.2.im| ≤ β}

/-- gammaUniformS uniform expansion. -/
@[dlmf 8.12.E7]
theorem gammaUniformS_uniform_expansion {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) (hε : 0 < ε) (hε1 : ε < 2*π) (N : ℕ) :
    IsBigO (gammaUniformFilter (π-δ) (2*π-ε)) (fun p => Real.sqrt (2*π)*exp (p.1/2)*exp (exp p.1*gammaUniformEtaOnLog p.2^2/2)*gammaUniformS (exp p.1) p.2-∑ k ∈ Finset.range N, gammaUniformC k p.2*exp (-(k : ℂ)*p.1)) (fun p => exp (-(N : ℂ)*p.1)) := by
  sorry

/-- gammaUniformT uniform expansion. -/
@[dlmf 8.12.E8]
theorem gammaUniformT_uniform_expansion {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) (hε : 0 < ε) (hε1 : ε < 2*π) (N : ℕ) :
    IsBigO (gammaUniformFilter (π-δ) (2*π-ε)) (fun p => Real.sqrt (2*π)*exp (p.1/2)*exp (-exp p.1*gammaUniformEtaOnLog p.2^2/2)*gammaUniformT (exp p.1) p.2-∑ k ∈ Finset.range N, (-1 : ℂ)^k*gammaUniformC k p.2*exp (-(k : ℂ)*p.1)) (fun p => exp (-(N : ℂ)*p.1)) := by
  sorry

/-- The normalized analytic inverse of η on its Maclaurin disk. -/
def gammaUniformInverseLog  : ℂ → ℂ :=
  Classical.epsilon (fun f : ℂ → ℂ => f 0=0 ∧ deriv f 0=1 ∧ ∀ η : ℂ, ‖η‖ < 2*Real.sqrt π → DifferentiableAt ℂ f η ∧ |(f η).im| < 2*π ∧ gammaUniformEtaOnLog (f η)=η)

/-- Inverse λ-series coefficients α_n. -/
def gammaUniformAlpha (n : ℕ) : ℂ :=
  iteratedDeriv n (fun η => exp (gammaUniformInverseLog η)) 0/(n.factorial : ℂ)

/-- Maclaurin coefficients d_{k,n}. -/
def gammaUniformD (k n : ℕ) : ℂ :=
  iteratedDeriv n (fun η => gammaUniformC k (gammaUniformInverseLog η)) 0/(n.factorial : ℂ)

/-- gammaUniformInverseLog spec. -/
@[dlmf 8.12.E13]
theorem gammaUniformInverseLog_spec  :
    gammaUniformInverseLog 0=0 ∧ deriv gammaUniformInverseLog 0=1 ∧ ∀ η : ℂ, ‖η‖ < 2*Real.sqrt π → DifferentiableAt ℂ gammaUniformInverseLog η ∧ |(gammaUniformInverseLog η).im| < 2*π ∧ gammaUniformEtaOnLog (gammaUniformInverseLog η)=η := by
  sorry

/-- gammaUniformC maclaurin. -/
@[dlmf 8.12.E11]
theorem gammaUniformC_maclaurin (k : ℕ) {η : ℂ} (hη : ‖η‖ < 2*Real.sqrt π) :
    HasSum (fun n : ℕ => gammaUniformD k n*η^n) (gammaUniformC k (gammaUniformInverseLog η)) := by
  sorry

/-- gammaUniformD recurrence. -/
@[dlmf 8.12.E12]
theorem gammaUniformD_recurrence (k n : ℕ) :
    gammaUniformD 0 0 = -1/3 ∧ (1 ≤ n → gammaUniformD 0 n=(n+2)*gammaUniformAlpha (n+2)) ∧ gammaUniformD (k+1) n=(-1 : ℂ)^(k+1)*gammaStirlingCoeff (k+1)*gammaUniformD 0 n+(n+2)*gammaUniformD k (n+2) := by
  sorry

/-- gammaUniformAlpha hasSum. -/
@[dlmf 8.12.E13]
theorem gammaUniformAlpha_hasSum {η : ℂ} (hη : ‖η‖ < 2*Real.sqrt π) :
    HasSum (fun n : ℕ => gammaUniformAlpha n*η^n) (exp (gammaUniformInverseLog η)) := by
  sorry

/-- gammaUniformAlpha printed. -/
@[dlmf 8.12.E14]
theorem gammaUniformAlpha_printed  :
    ∀ n < 6, gammaUniformAlpha (n+3)=([1/36,-1/270,1/4320,1/17010,-139/5443200,1/204120] : List ℂ)[n]! := by
  sorry

/-- gammaUniformC at zero printed. -/
@[dlmf 8.12.E17]
theorem gammaUniformC_at_zero_printed  :
    ∀ n < 6, gammaUniformC n 0=([-1/3,-1/540,25/6048,101/155520,-3184811/3695155200,-2745493/8151736320] : List ℂ)[n]! := by
  sorry

/-- normIncGammaQ diagonal uniform asymptotic. -/
@[dlmf 8.12.E15]
theorem normIncGammaQ_diagonal_uniform_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (logSector (π-δ)) (fun k w => exp (-((k : ℂ)+1/2)*w)/Real.sqrt (2*π)) (fun k => gammaUniformC k 0) (fun w => normIncGammaQOnLog (exp w) w-1/2) := by
  sorry

/-- normIncGammaQ negative diagonal asymptotic. -/
@[dlmf 8.12.E16]
theorem normIncGammaQ_negative_diagonal_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    HasAsymptoticExpansion (logSector (π-δ)) (fun k w => exp (-((k : ℂ)+1/2)*w)/Real.sqrt (2*π)) (fun k => -I*(-1 : ℂ)^k*gammaUniformC k 0) (fun w => -exp (ε*π*I*exp w)*Gamma (exp w+1)/(2*π*I)*upperIncGammaOnLog (-exp w) (w+ε*π*I)-ε/2) := by
  sorry

/-- The parabolic transition function d(χ). -/
@[dlmf 8.12.E19]
def gammaParisD (χ : ℂ) : ℂ :=
  Real.sqrt (π/2)*exp (χ^2/2)*erfc (χ/Real.sqrt 2)

/-- Transition coefficients extracted in the positive square-root variable. -/
def gammaParisRawCoeff (upper : Bool) (χ : ℂ) (k : ℕ) : ℂ :=
  asymptoticCoeff (fun t : ℝ => let z : ℂ := t^2; let a := z-χ*t; Gamma a*z^(1/2-a)*exp z*(if upper then normIncGammaQContinued a z else normIncGammaPContinued a z)) k

/-- The coefficients A_k(χ) fixed by the two complementary transitions. -/
def gammaParisA (k : ℕ) (χ : ℂ) : ℂ :=
  (gammaParisRawCoeff true χ k+gammaParisRawCoeff false χ k)/(gammaParisD χ+gammaParisD (-χ))

/-- The coefficients B_k(χ). -/
def gammaParisB (k : ℕ) (χ : ℂ) : ℂ :=
  gammaParisD χ*gammaParisA k χ-gammaParisRawCoeff true χ k

/-- gammaParis printed. -/
@[dlmf 8.12.E20]
theorem gammaParis_printed (χ : ℂ) :
    gammaParisA 0 χ=1 ∧ gammaParisB 0 χ=0 ∧ gammaParisA 1 χ=χ/2+χ^3/6 ∧ gammaParisB 1 χ=1/3+χ^2/6 := by
  sorry

/-- Uniformity is specified for bounded transition variable χ and closed right-half-plane sectors. -/
@[dlmf 8.12.E18]
theorem gammaParis_uniform_expansion (upper : Bool) {δ B : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/2) (hB : 0 < B) (N : ℕ) :
    IsBigO (comap (fun p : ℂ × ℂ => Real.exp p.1.re) atTop ⊓ 𝓟 {p : ℂ × ℂ | |p.1.im| ≤ π/2-δ ∧ ‖p.2‖ ≤ B ∧ (if upper then 0 ≤ (p.2*exp (p.1/2)).re else (p.2*exp (p.1/2)).re ≤ 0)}) (fun p => let a := exp p.1-p.2*exp (p.1/2); let ε : ℂ := if upper then 1 else -1; Gamma a*exp ((1/2-a)*p.1+exp p.1)*(if upper then normIncGammaQContinued a (exp p.1) else normIncGammaPContinued a (exp p.1))-gammaParisD (ε*p.2)*(∑ k ∈ Finset.range N, gammaParisA k p.2*exp (-(k : ℂ)*p.1/2))+ε*(∑ k ∈ Finset.range N, gammaParisB k p.2*exp (-(k : ℂ)*p.1/2))) (fun p => exp (-(N : ℂ)*p.1/2)) := by
  sorry

/-- The inverse Q, including x=∞ at q=0. -/
@[dlmf 8.12.E21]
def gammaQInverse (a q : ℝ) : ℝ≥0∞ :=
  if q=0 then ∞ else if q=1 then 0 else ENNReal.ofReal (Classical.epsilon (fun x : ℝ => 0 ≤ x ∧ (normIncGammaQContinued a x).re=q))

/-- gammaQInverse spec. -/
@[dlmf 8.12.E21]
theorem gammaQInverse_spec {a q : ℝ} (ha : 0 < a) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    (if gammaQInverse a q=∞ then 0 else (normIncGammaQContinued a (gammaQInverse a q).toReal).re)=q ∧ (q ≠ 0 → gammaQInverse a q ≠ ∞) := by
  sorry

/-- gammaQInverse median asymptotic. -/
@[dlmf 8.12.E22]
theorem gammaQInverse_median_asymptotic  :
    ∃ c : ℕ → ℝ, (∀ n < 5, c n=([1,-1/3,8/405,184/25515,2248/3444525] : List ℝ)[n]!) ∧ HasAsymptoticExpansion atTop (fun n (a : ℝ) => a^((1 : ℤ)-n)) c (fun a => (gammaQInverse a (1/2)).toReal) := by
  sorry

end AAR.Confluent
