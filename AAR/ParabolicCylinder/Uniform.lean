/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ParabolicCylinder.AsymptoticsZeros
public import AAR.Airy.Basic

/-!
# Olver and Temme uniform cylinder expansions and coefficient systems

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open Polynomial

/-- pcfXi. -/
@[dlmf 12.10.E7]
def pcfXi (t : ℝ) : ℝ :=
  (t*Real.sqrt (t^2-1)-Real.log (t+Real.sqrt (t^2-1)))/2

/-- pcfEta. -/
@[dlmf 12.10.E23]
def pcfEta (t : ℝ) : ℝ :=
  (Real.arccos t-t*Real.sqrt (1-t^2))/2

/-- pcfXiBar. -/
@[dlmf 12.10.E26]
def pcfXiBar (t : ℝ) : ℝ :=
  (t*Real.sqrt (t^2+1)+Real.log (t+Real.sqrt (t^2+1)))/2

/-- pcfH. -/
@[dlmf 12.10.E15]
def pcfH (μ : ℂ) : ℂ :=
  2^(-μ^2/4-1/4)*exp (-μ^2/4)*μ^(μ^2/2-1/2)

/-- pcfGammaCoeff. -/
@[dlmf 12.10.E16]
def pcfGammaCoeff (s : ℕ) : ℂ :=
  asymptoticCoeff (fun z : ℝ => Gamma (1/2+z)/((Real.sqrt (2*π):ℂ)*exp (-z)*(z:ℂ)^(z:ℂ))) s

/-- pcfGammaCoeff expansion. -/
@[dlmf 12.10.E16]
theorem pcfGammaCoeff_expansion (N : ℕ) :
    (fun z : ℝ => Gamma (1/2+z)/((Real.sqrt (2*π):ℂ)*exp (-z)*(z:ℂ)^(z:ℂ))-∑ s ∈ Finset.range N, pcfGammaCoeff s/(z:ℂ)^s) =O[atTop] (fun z : ℝ => (z:ℂ)^(-(N:ℤ))) := by
  sorry

/-- pcfGammaCoeff initial. -/
@[dlmf 12.10.E17]
theorem pcfGammaCoeff_initial  :
    pcfGammaCoeff 0=1 ∧ pcfGammaCoeff 1=-1/24 ∧ pcfGammaCoeff 2=1/1152 ∧ pcfGammaCoeff 3=1003/414720 ∧ pcfGammaCoeff 4=-4027/39813120 := by
  sorry

/-- Polynomial pairs `(u_s,r_{s-1})`; the polynomial degree condition fixes the integration constant.
Existence of the chosen polynomial is asserted separately, not inferred from choice.
The `u`-equation coefficient is `3(s+1)` as in DLMF 12.10.11 (corrected 2026-10-20 from
`3/2(s+1)`, for which no polynomial solution exists at `s = 0`). -/
def pcfOlverPair : ℕ → Polynomial ℝ × Polynomial ℝ
  | 0 => (1,0)
  | s+1 =>
    let q := pcfOlverPair s
    let r := C (1/8:ℝ)*(C 3*X^2+C 2)*q.1 - C (3/2*(s+1:ℝ))*X*q.2 + C (1/2:ℝ)*(X^2-1)*derivative q.2
    (Classical.epsilon (fun p : Polynomial ℝ =>
      (X^2-1)*derivative p-C (3*(s+1:ℝ))*X*p=r ∧
      p.natDegree ≤ if Even (s+1) then 3*(s+1)-2 else 3*(s+1)),r)

/-- pcfOlverU. -/
@[dlmf 12.10.E11]
def pcfOlverU (s : ℕ) : Polynomial ℝ :=
  (pcfOlverPair s).1

/-- pcfOlverR. -/
@[dlmf 12.10.E12]
def pcfOlverR (s : ℕ) : Polynomial ℝ :=
  (pcfOlverPair (s+1)).2

/-- pcfOlverV. -/
@[dlmf 12.10.E13]
def pcfOlverV (s : ℕ) : Polynomial ℝ :=
  if s=0 then 1 else pcfOlverU s+C (1/2:ℝ)*X*pcfOlverU (s-1)-(pcfOlverPair (s-1)).2

/-- pcfOlverU spec. -/
@[dlmf 12.10.E11]
theorem pcfOlverU_spec (s : ℕ) :
    (X^2-1)*derivative (pcfOlverU (s+1))-C (3*(s+1:ℝ))*X*pcfOlverU (s+1)=pcfOlverR s ∧ (pcfOlverU (s+1)).natDegree ≤ if Even (s+1) then 3*(s+1)-2 else 3*(s+1) := by
  sorry

/-- Coefficient recursion of `(X²-1)p' - kXp`. -/
lemma olver_homog_coeff (k : ℝ) (p : Polynomial ℝ) (n : ℕ) :
    ((X^2-1)*derivative p-C k*X*p).coeff (n+1) = (n-k) * p.coeff n - (n+2) * p.coeff (n+2) := by
  have : (X^2-1)*derivative p-C k*X*p = X^2*derivative p - derivative p - C k*(X*p) := by ring
  rw [this, coeff_sub, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_derivative]
  rcases n with _ | n
  · simp [coeff_X_pow_mul']; ring
  · rw [show n+1+1 = n+2 by ring, coeff_X_pow_mul']
    simp [coeff_derivative]; ring

/-- Constant coefficient of `(X²-1)p' - kXp`. -/
lemma olver_homog_coeff_zero (k : ℝ) (p : Polynomial ℝ) :
    ((X^2-1)*derivative p-C k*X*p).coeff 0 = - p.coeff 1 := by
  have : (X^2-1)*derivative p-C k*X*p = X^2*derivative p - derivative p - C k*(X*p) := by ring
  rw [this]; simp [coeff_derivative]

/-- Polynomial solutions of `(X²-1)p' - 3Xp = 0` of degree `≤ 3` vanish. -/
lemma olver_homog_three {p : Polynomial ℝ} (hp : (X^2-1)*derivative p-C 3*X*p=0)
    (hd : p.natDegree ≤ 3) : p = 0 := by
  have h4 : p.coeff 4 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have e0 := olver_homog_coeff_zero 3 p
  have e1 := olver_homog_coeff 3 p 0
  have e2 := olver_homog_coeff 3 p 1
  have e3 := olver_homog_coeff 3 p 2
  rw [hp, coeff_zero] at e0 e1 e2 e3
  push_cast at e1 e2 e3
  have h1 : p.coeff 1 = 0 := by linarith
  have h3 : p.coeff 3 = 0 := by linarith
  have h2 : p.coeff 2 = 0 := by linarith
  have h0 : p.coeff 0 = 0 := by linarith
  ext n
  rcases (show n ≤ 3 ∨ 3 < n by omega) with hn | hn
  · interval_cases n <;> simp [h0, h1, h2, h3]
  · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hn)]

/-- Polynomial solutions of `(X²-1)p' - 6Xp = 0` of degree `≤ 4` vanish. -/
lemma olver_homog_six {p : Polynomial ℝ} (hp : (X^2-1)*derivative p-C 6*X*p=0)
    (hd : p.natDegree ≤ 4) : p = 0 := by
  have h5 : p.coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have h6 : p.coeff 6 = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have e0 := olver_homog_coeff_zero 6 p
  have e1 := olver_homog_coeff 6 p 0
  have e2 := olver_homog_coeff 6 p 1
  have e3 := olver_homog_coeff 6 p 2
  have e4 := olver_homog_coeff 6 p 3
  have e5 := olver_homog_coeff 6 p 4
  rw [hp, coeff_zero] at e0 e1 e2 e3 e4 e5
  push_cast at e1 e2 e3 e4 e5
  have h4 : p.coeff 4 = 0 := by linarith
  have h1 : p.coeff 1 = 0 := by linarith
  have h3 : p.coeff 3 = 0 := by linarith
  have h2 : p.coeff 2 = 0 := by linarith
  have h0 : p.coeff 0 = 0 := by linarith
  ext n
  rcases (show n ≤ 4 ∨ 4 < n by omega) with hn | hn
  · interval_cases n <;> simp [h0, h1, h2, h3, h4]
  · simp [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hn)]

/-- A choice value is pinned down by a witness and uniqueness. -/
lemma olver_epsilon_eq {Q : Polynomial ℝ → Prop} {w : Polynomial ℝ} (hw : Q w)
    (hu : ∀ p, Q p → p = w) : Classical.epsilon Q = w :=
  hu _ (Classical.epsilon_spec ⟨w, hw⟩)

/-- Difference of two solutions of the `u`-equation. -/
lemma olver_sub_eq {k : ℝ} {r p w : Polynomial ℝ} (hp : (X^2-1)*derivative p-C k*X*p=r)
    (hw : (X^2-1)*derivative w-C k*X*w=r) : (X^2-1)*derivative (p-w)-C k*X*(p-w)=0 := by
  rw [derivative_sub]; linear_combination hp - hw

/-- The first Olver pair `(u₁, r₀)`. -/
lemma pcfOlverPair_one :
    pcfOlverPair 1 = (X*(X^2-C 6)*C (1/24:ℝ), C (1/8:ℝ)*(C 3*X^2+C 2)) := by
  simp only [pcfOlverPair]
  have hw : (X^2-1)*derivative (X*(X^2-C 6)*C (1/24:ℝ))-C (3*((0:ℕ)+1:ℝ))*X*(X*(X^2-C 6)*C (1/24:ℝ)) =
      C (1/8:ℝ)*(C 3*X^2+C 2)*1 - C (3/2*((0:ℕ)+1:ℝ))*X*0 + C (1/2:ℝ)*(X^2-1)*derivative 0 := by
    apply Polynomial.funext; intro x
    simp [derivative_mul]; ring
  rw [olver_epsilon_eq (w := X*(X^2-C 6)*C (1/24:ℝ)) ⟨hw, by norm_num; compute_degree⟩]
  · simp
  · rintro _p ⟨hp, hd⟩
    have h := olver_sub_eq hp hw
    rw [show (3*((0:ℕ)+1:ℝ)) = 3 by norm_num] at h
    norm_num at hd
    refine sub_eq_zero.mp (olver_homog_three h ?_)
    refine (natDegree_sub_le _ _).trans (max_le hd ?_)
    compute_degree

/-- The chosen Olver polynomial equals any witness, given uniqueness of homogeneous solutions. -/
lemma olver_epsilon_of {k : ℝ} {N : ℕ} {r w : Polynomial ℝ}
    (hw : (X^2-1)*derivative w-C k*X*w=r) (hwd : w.natDegree ≤ N)
    (hu : ∀ q : Polynomial ℝ, (X^2-1)*derivative q-C k*X*q=0 → q.natDegree ≤ N → q = 0) :
    Classical.epsilon (fun p : Polynomial ℝ => (X^2-1)*derivative p-C k*X*p=r ∧ p.natDegree ≤ N) = w :=
  olver_epsilon_eq ⟨hw, hwd⟩ fun _ hp => sub_eq_zero.mp
    (hu _ (olver_sub_eq hp.1 hw) ((natDegree_sub_le _ _).trans (max_le hp.2 hwd)))

/-- The second Olver pair `(u₂, r₁)`. -/
lemma pcfOlverU_two : pcfOlverU 2 = (-C 9*X^4+C 249*X^2+C 145)*C (1/1152:ℝ) := by
  rw [pcfOlverU, pcfOlverPair.eq_2 1, pcfOlverPair_one]
  dsimp only
  rw [olver_epsilon_of (w := (-C 9*X^4+C 249*X^2+C 145)*C (1/1152:ℝ))]
  · apply Polynomial.funext; intro x
    simp [derivative_mul]; ring
  · norm_num; compute_degree
  · intro q hq hd
    rw [show (3*((1:ℕ)+1:ℝ)) = 6 by norm_num] at hq
    norm_num at hd
    exact olver_homog_six hq hd

/-- pcfOlverUV initial. -/
@[dlmf 12.10.E9, dlmf 12.10.E10]
theorem pcfOlverUV_initial  :
    pcfOlverU 0=1 ∧ pcfOlverU 1=X*(X^2-C 6)*C (1/24:ℝ) ∧ pcfOlverU 2=(-C 9*X^4+C 249*X^2+C 145)*C (1/1152:ℝ) ∧ pcfOlverV 0=1 ∧ pcfOlverV 1=X*(X^2+C 6)*C (1/24:ℝ) ∧ pcfOlverV 2=(C 15*X^4-C 327*X^2-C 143)*C (1/1152:ℝ) := by
  have hU1 : pcfOlverU 1 = X*(X^2-C 6)*C (1/24:ℝ) := by rw [pcfOlverU, pcfOlverPair_one]
  refine ⟨by simp [pcfOlverU, pcfOlverPair], hU1, pcfOlverU_two, by simp [pcfOlverV], ?_, ?_⟩
  · rw [show pcfOlverV 1 = pcfOlverU 1 + C (1/2:ℝ)*X*pcfOlverU 0 - (pcfOlverPair 0).2 from rfl, hU1]
    simp only [pcfOlverU, pcfOlverPair]
    apply Polynomial.funext; intro x
    simp; ring
  · rw [show pcfOlverV 2 = pcfOlverU 2 + C (1/2:ℝ)*X*pcfOlverU 1 - (pcfOlverPair 1).2 from rfl, hU1, pcfOlverU_two, pcfOlverPair_one]
    apply Polynomial.funext; intro x
    simp; ring

/-- pcfOlverA. -/
@[dlmf 12.10.E8]
def pcfOlverA (s : ℕ) (t : ℝ) : ℂ :=
  (((pcfOlverU s).eval t:ℝ):ℂ)/(t^2-1:ℂ)^(3*(s:ℂ)/2)

/-- pcfOlverATilde. -/
@[dlmf 12.10.E24]
def pcfOlverATilde (s : ℕ) (t : ℝ) : ℂ :=
  (((pcfOlverU s).eval t:ℝ):ℂ)/(1-t^2:ℂ)^(3*(s:ℂ)/2)

/-- pcfOlverUBar. -/
@[dlmf 12.10.E27]
def pcfOlverUBar (s : ℕ) (t : ℝ) : ℂ :=
  I^s*aeval (-I*t) (pcfOlverU s)

/-- pcfOlverB. -/
@[dlmf 12.10.E8]
def pcfOlverB (s : ℕ) (t : ℝ) : ℂ :=
  (((pcfOlverV s).eval t:ℝ):ℂ)/(t^2-1:ℂ)^(3*(s:ℂ)/2)

/-- pcfOlverBTilde. -/
@[dlmf 12.10.E24]
def pcfOlverBTilde (s : ℕ) (t : ℝ) : ℂ :=
  (((pcfOlverV s).eval t:ℝ):ℂ)/(1-t^2:ℂ)^(3*(s:ℂ)/2)

/-- pcfOlverVBar. -/
@[dlmf 12.10.E30]
def pcfOlverVBar (s : ℕ) (t : ℝ) : ℂ :=
  I^s*aeval (-I*t) (pcfOlverV s)

/-- pcfUniformFilter. -/
def pcfUniformFilter (S : Set ℝ) : Filter (ℝ × ℝ) :=
  comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | p.2 ∈ S}

/-- HasCylinderUniformExpansion. -/
def HasCylinderUniformExpansion (F : ℝ → ℝ → ℂ) (C : ℕ → ℝ → ℂ) (S : Set ℝ) : Prop :=
  ∀ N : ℕ, (fun p : ℝ × ℝ => F p.1 p.2-∑ s ∈ Finset.range N, C s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter S] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ)))

/-- IsCylinderGNormalizer. -/
@[dlmf 12.10.E14]
def IsCylinderGNormalizer (g : ℝ → ℂ) : Prop :=
  ∀ N : ℕ, (fun μ : ℝ => g μ/pcfH μ-1-1/2*∑ j ∈ Finset.range N, pcfGammaCoeff (j+1)/(μ^2/2:ℂ)^(j+1)) =O[atTop] (fun μ : ℝ => (μ:ℂ)^(-(2*(N+1):ℤ)))

/-- pcf negative parameter uniform. -/
@[dlmf 12.10.E3, dlmf 12.10.E4, dlmf 12.10.E5, dlmf 12.10.E6, dlmf 12.10.E14]
theorem pcf_negative_parameter_uniform  :
    ∃ g : ℝ → ℂ, IsCylinderGNormalizer g ∧ ∀ δ : ℝ, 0 < δ → HasCylinderUniformExpansion (fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2)/(g μ*exp (-μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ))) (fun s t => pcfOlverA s t) (Ici (1+δ)) ∧ HasCylinderUniformExpansion (fun μ t => pcfUDeriv (-μ^2/2) (μ*t*Real.sqrt 2)/(-(μ:ℂ)/Real.sqrt 2*g μ*(t^2-1:ℂ)^(1/4:ℂ)*exp (-μ^2*pcfXi t))) (fun s t => pcfOlverB s t) (Ici (1+δ)) ∧ HasCylinderUniformExpansion (fun μ t => pcfV (-μ^2/2) (μ*t*Real.sqrt 2)/(2*g μ/Gamma (1/2+μ^2/2)*exp (μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ))) (fun s t => (-1)^s*pcfOlverA s t) (Ici (1+δ)) ∧ HasCylinderUniformExpansion (fun μ t => pcfVDeriv (-μ^2/2) (μ*t*Real.sqrt 2)/(Real.sqrt 2*μ*g μ/Gamma (1/2+μ^2/2)*(t^2-1:ℂ)^(1/4:ℂ)*exp (μ^2*pcfXi t))) (fun s t => (-1)^s*pcfOlverB s t) (Ici (1+δ)) := by
  sorry

/-- pcfKappa. -/
@[dlmf 12.10.E22]
def pcfKappa (μ t : ℝ) : ℝ :=
  μ^2*pcfEta t-π/4

/-- pcfChi. -/
@[dlmf 12.10.E22]
def pcfChi (μ t : ℝ) : ℝ :=
  μ^2*pcfEta t+π/4

/-- pcf oscillatory parameter uniform. -/
@[dlmf 12.10.E18, dlmf 12.10.E19, dlmf 12.10.E20, dlmf 12.10.E21]
theorem pcf_oscillatory_parameter_uniform  :
    ∃ g : ℝ → ℂ, IsCylinderGNormalizer g ∧ ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ N : ℕ, (fun p : ℝ × ℝ => pcfU (-p.1^2/2) (p.1*p.2*Real.sqrt 2)/(2*g p.1/(1-p.2^2:ℂ)^(1/4:ℂ))-∑ s ∈ Finset.range N, Real.cos (pcfKappa p.1 p.2+s*π/2)*pcfOlverATilde s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter (Icc (-1+δ) (1-δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ))) ∧ (fun p : ℝ × ℝ => pcfUDeriv (-p.1^2/2) (p.1*p.2*Real.sqrt 2)/(p.1*Real.sqrt 2*g p.1*(1-p.2^2:ℂ)^(1/4:ℂ))-∑ s ∈ Finset.range N, Real.sin (pcfKappa p.1 p.2+s*π/2)*pcfOlverBTilde s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter (Icc (-1+δ) (1-δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ))) ∧ (fun p : ℝ × ℝ => pcfV (-p.1^2/2) (p.1*p.2*Real.sqrt 2)/(2*g p.1/(Gamma (1/2+p.1^2/2)*(1-p.2^2:ℂ)^(1/4:ℂ)))-∑ s ∈ Finset.range N, Real.cos (pcfChi p.1 p.2+s*π/2)*pcfOlverATilde s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter (Icc (-1+δ) (1-δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ))) ∧ (fun p : ℝ × ℝ => pcfVDeriv (-p.1^2/2) (p.1*p.2*Real.sqrt 2)/(p.1*Real.sqrt 2*g p.1*(1-p.2^2:ℂ)^(1/4:ℂ)/Gamma (1/2+p.1^2/2))-∑ s ∈ Finset.range N, Real.sin (pcfChi p.1 p.2+s*π/2)*pcfOlverBTilde s p.2/(p.1:ℂ)^(2*s)) =O[pcfUniformFilter (Icc (-1+δ) (1-δ))] (fun p : ℝ × ℝ => (p.1:ℂ)^(-(2*N:ℤ))) := by
  sorry

/-- IsCylinderGBarNormalizer. -/
@[dlmf 12.10.E28]
def IsCylinderGBarNormalizer (g : ℝ → ℂ) : Prop :=
  ∀ N : ℕ, (fun μ : ℝ => g μ*μ*Real.sqrt 2*pcfH μ-1-1/2*∑ j ∈ Finset.range N, (-1)^(j+1)*pcfGammaCoeff (j+1)/(μ^2/2:ℂ)^(j+1)) =O[atTop] (fun μ : ℝ => (μ:ℂ)^(-(2*(N+1):ℤ)))

/-- pcf positive parameter uniform. -/
@[dlmf 12.10.E25, dlmf 12.10.E29]
theorem pcf_positive_parameter_uniform  :
    ∃ g : ℝ → ℂ, IsCylinderGBarNormalizer g ∧ HasCylinderUniformExpansion (fun μ t => pcfU (μ^2/2) (μ*t*Real.sqrt 2)/(g μ*exp (-μ^2*pcfXiBar t)/(t^2+1:ℂ)^(1/4:ℂ))) (fun s t => pcfOlverUBar s t/(t^2+1:ℂ)^(3*(s:ℂ)/2)) univ ∧ HasCylinderUniformExpansion (fun μ t => pcfUDeriv (μ^2/2) (μ*t*Real.sqrt 2)/(-(μ:ℂ)/Real.sqrt 2*g μ*(t^2+1:ℂ)^(1/4:ℂ)*exp (-μ^2*pcfXiBar t))) (fun s t => pcfOlverVBar s t/(t^2+1:ℂ)^(3*(s:ℂ)/2)) univ := by
  sorry

/-- pcfTau. -/
@[dlmf 12.10.E32]
def pcfTau (t : ℝ) : ℝ :=
  (t/Real.sqrt (t^2-1)-1)/2

/-- Polynomial primitive based at zero. -/
def pcfPolyPrimitive (p : Polynomial ℝ) : Polynomial ℝ :=
  p.sum (fun n c => C (c/(n+1))*X^(n+1))

/-- Temme polynomials, with an explicit derivative-integral recursion. -/
def pcfTemmePoly : ℕ → Polynomial ℝ
  | 0 => 1
  | s+1 => -C 4*X^2*(X+1)^2*derivative (pcfTemmePoly s)-C (1/4:ℝ)*pcfPolyPrimitive ((C 20*X^2+C 20*X+C 3)*pcfTemmePoly s)

/-- Real polynomials with equal derivatives and equal values at `0` are equal. -/
lemma pcfPoly_eq_of_derivative_eq {P Q : Polynomial ℝ} (hd : derivative P = derivative Q)
    (h0 : P.eval 0 = Q.eval 0) : P = Q := by
  have hc : ∀ x : ℝ, HasDerivAt (fun x => (P - Q).eval x) 0 x := fun x => by
    have := (P - Q).hasDerivAt x
    rwa [derivative_sub, hd, sub_self, eval_zero] at this
  have := fun x => is_const_of_deriv_eq_zero (fun x => (hc x).differentiableAt) (fun x => (hc x).deriv) x 0
  refine sub_eq_zero.mp (Polynomial.funext fun x => ?_)
  rw [this x, eval_sub, h0, sub_self, eval_zero]

/-- The primitive is additive. -/
lemma pcfPolyPrimitive_add (p q : Polynomial ℝ) :
    pcfPolyPrimitive (p + q) = pcfPolyPrimitive p + pcfPolyPrimitive q := by
  unfold pcfPolyPrimitive
  exact Polynomial.sum_add_index _ _ _ (fun n => by simp) (fun n a b => by rw [add_div, C_add, add_mul])

/-- The primitive of a monomial. -/
lemma pcfPolyPrimitive_monomial (n : ℕ) (c : ℝ) :
    pcfPolyPrimitive (monomial n c) = C (c/(n+1)) * X^(n+1) := by
  unfold pcfPolyPrimitive
  exact Polynomial.sum_monomial_index _ _ (by simp)

/-- The primitive has derivative `p`. -/
lemma derivative_pcfPolyPrimitive (p : Polynomial ℝ) : derivative (pcfPolyPrimitive p) = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [pcfPolyPrimitive_add, derivative_add, hp, hq]
  | monomial n c =>
    rw [pcfPolyPrimitive_monomial, derivative_C_mul_X_pow, ← C_mul_X_pow_eq_monomial]
    congr 1
    · congr 1; push_cast; field_simp

/-- The primitive vanishes at `0`. -/
lemma eval_zero_pcfPolyPrimitive (p : Polynomial ℝ) : (pcfPolyPrimitive p).eval 0 = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [pcfPolyPrimitive_add, eval_add, hp, hq, add_zero]
  | monomial n c => simp [pcfPolyPrimitive_monomial]

/-- Characterization of the primitive. -/
lemma pcfPolyPrimitive_eq {p P : Polynomial ℝ} (hd : derivative P = p) (h0 : P.eval 0 = 0) :
    pcfPolyPrimitive p = P :=
  pcfPoly_eq_of_derivative_eq (by rw [derivative_pcfPolyPrimitive, hd]) (by rw [eval_zero_pcfPolyPrimitive, h0])

/-- pcfTemmePoly initial. -/
@[dlmf 12.10.E34]
theorem pcfTemmePoly_initial  :
    pcfTemmePoly 1=-C (1/12:ℝ)*X*(C 20*X^2+C 30*X+C 9) ∧ pcfTemmePoly 2=C (1/288:ℝ)*X^2*(C 6160*X^4+C 18480*X^3+C 19404*X^2+C 8028*X+C 945) := by
  have h1 : pcfTemmePoly 1 = -C (1/12:ℝ)*X*(C 20*X^2+C 30*X+C 9) := by
    rw [pcfTemmePoly, pcfTemmePoly, pcfPolyPrimitive_eq (P := C (20/3:ℝ)*X^3 + C 10*X^2 + C 3*X)]
    · apply Polynomial.funext; intro r; simp; ring
    · apply Polynomial.funext; intro r; simp; ring
    · simp
  refine ⟨h1, ?_⟩
  rw [show (2:ℕ) = 1 + 1 from rfl, pcfTemmePoly, h1,
    pcfPolyPrimitive_eq (P := -C (1/12:ℝ) * (C (400/6:ℝ)*X^6 + C 200*X^5 + C 210*X^4 + C 90*X^3 + C (27/2:ℝ)*X^2))]
  · apply Polynomial.funext; intro r; simp; ring
  · apply Polynomial.funext; intro r; simp; ring
  · simp

/-- pcfTemmePoly recurrence. -/
@[dlmf 12.10.E33]
theorem pcfTemmePoly_recurrence (s : ℕ) (τ : ℝ) :
    (pcfTemmePoly (s+1)).eval τ=-4*τ^2*(τ+1)^2*(derivative (pcfTemmePoly s)).eval τ-1/4*∫ u : ℝ in 0..τ, (20*u^2+20*u+3)*(pcfTemmePoly s).eval u := by
  set q := (C 20*X^2+C 20*X+C 3)*pcfTemmePoly s
  have hint : ∫ u : ℝ in 0..τ, (20*u^2+20*u+3)*(pcfTemmePoly s).eval u = (pcfPolyPrimitive q).eval τ := by
    have : ∀ u : ℝ, (20*u^2+20*u+3)*(pcfTemmePoly s).eval u = q.eval u := fun u => by simp [q]
    simp_rw [this]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun u => (pcfPolyPrimitive q).eval u)
      (fun u _ => by simpa [derivative_pcfPolyPrimitive] using (pcfPolyPrimitive q).hasDerivAt u)
      (q.continuous.intervalIntegrable _ _), eval_zero_pcfPolyPrimitive, sub_zero]
  rw [hint, pcfTemmePoly]
  simp [q]

/-- pcfU temme uniform. -/
@[dlmf 12.10.E31]
theorem pcfU_temme_uniform {δ : ℝ} (hδ : 0 < δ) :
    HasCylinderUniformExpansion (fun μ t => pcfU (-μ^2/2) (μ*t*Real.sqrt 2)/(pcfH μ*exp (-μ^2*pcfXi t)/(t^2-1:ℂ)^(1/4:ℂ))) (fun s t => (((pcfTemmePoly s).eval (pcfTau t):ℝ):ℂ)) (Ici (1+δ)) := by
  sorry

/-- pcfZeta. -/
@[dlmf 12.10.E39]
def pcfZeta (t : ℝ) : ℝ :=
  if 1 ≤ t then (3/2*pcfXi t)^(2/3:ℝ) else -(3/2*pcfEta t)^(2/3:ℝ)

/-- Inverse turning-point coordinate; its domain and uniqueness are asserted separately. -/
def pcfInverseZeta (ζ : ℝ) : ℝ :=
  Classical.epsilon (fun t : ℝ => -1 < t ∧ pcfZeta t=ζ)

/-- pcfInverseZeta spec. -/
@[dlmf 12.10.E39]
theorem pcfInverseZeta_spec {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    -1 < pcfInverseZeta ζ ∧ pcfZeta (pcfInverseZeta ζ)=ζ ∧ ∀ t : ℝ, -1 < t → pcfZeta t=ζ → t=pcfInverseZeta ζ := by
  sorry

/-- pcfPhi. -/
@[dlmf 12.10.E40]
def pcfPhi (ζ : ℝ) : ℝ :=
  if ζ=0 then 2^(-1/6:ℝ) else (ζ/((pcfInverseZeta ζ)^2-1))^(1/4:ℝ)

/-- The turning-point coordinate is analytic at the turning point. -/
theorem pcfZeta_analytic_at_one  :
    AnalyticAt ℝ pcfZeta 1 := by
  sorry

/-- pcfInverseZeta taylor. -/
@[dlmf 12.10.E41]
theorem pcfInverseZeta_taylor  :
    (fun ζ : ℝ => let w:=2^(-1/3:ℝ)*ζ; pcfInverseZeta ζ-(1+w-w^2/10+11*w^3/350-823*w^4/63000+150653*w^5/24255000)) =O[𝓝 0] (fun ζ : ℝ => ζ^6) := by
  sorry

/-- pcfAiryAlpha. -/
@[dlmf 12.10.E43]
def pcfAiryAlpha (m : ℕ) : ℝ :=
  (∏ j ∈ Finset.range (2*m), (2*m+1+2*j:ℝ))/((m.factorial:ℝ)*144^m)

/-- pcfAiryBeta. -/
@[dlmf 12.10.E43]
def pcfAiryBeta (m : ℕ) : ℝ :=
  -(6*m+1:ℝ)/(6*m-1:ℝ)*pcfAiryAlpha m

/-- Continuous coefficient at zero is supplied by a removable limit. -/
@[dlmf 12.10.E42]
def pcfAiryA (s : ℕ) (ζ : ℝ) : ℝ :=
  limUnder (𝓝[≠] ζ) (fun u : ℝ => (∑ m ∈ Finset.range (2*s+1), pcfAiryBeta m*(pcfPhi u)^(6*(2*s-m))*(pcfOlverU (2*s-m)).eval (pcfInverseZeta u))/u^(3*s+0))

/-- pcfAiryA limit. -/
@[dlmf 12.10.E42]
theorem pcfAiryA_limit (s : ℕ) {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    Tendsto (fun u : ℝ => (∑ m ∈ Finset.range (2*s+1), pcfAiryBeta m*(pcfPhi u)^(6*(2*s-m))*(pcfOlverU (2*s-m)).eval (pcfInverseZeta u))/u^(3*s+0)) (𝓝[≠] ζ) (𝓝 (pcfAiryA s ζ)) := by
  sorry

/-- Continuous coefficient at zero is supplied by a removable limit. -/
@[dlmf 12.10.E42]
def pcfAiryB (s : ℕ) (ζ : ℝ) : ℝ :=
  limUnder (𝓝[≠] ζ) (fun u : ℝ => -(∑ m ∈ Finset.range (2*s+1+1), pcfAiryAlpha m*(pcfPhi u)^(6*(2*s+1-m))*(pcfOlverU (2*s+1-m)).eval (pcfInverseZeta u))/u^(3*s+2))

/-- pcfAiryB limit. -/
@[dlmf 12.10.E42]
theorem pcfAiryB_limit (s : ℕ) {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    Tendsto (fun u : ℝ => -(∑ m ∈ Finset.range (2*s+1+1), pcfAiryAlpha m*(pcfPhi u)^(6*(2*s+1-m))*(pcfOlverU (2*s+1-m)).eval (pcfInverseZeta u))/u^(3*s+2)) (𝓝[≠] ζ) (𝓝 (pcfAiryB s ζ)) := by
  sorry

/-- Continuous coefficient at zero is supplied by a removable limit. -/
@[dlmf 12.10.E46]
def pcfAiryC (s : ℕ) (ζ : ℝ) : ℝ :=
  limUnder (𝓝[≠] ζ) (fun u : ℝ => -(∑ m ∈ Finset.range (2*s+1+1), pcfAiryBeta m*(pcfPhi u)^(6*(2*s+1-m))*(pcfOlverV (2*s+1-m)).eval (pcfInverseZeta u))/u^(3*s+1))

/-- pcfAiryC limit. -/
@[dlmf 12.10.E46]
theorem pcfAiryC_limit (s : ℕ) {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    Tendsto (fun u : ℝ => -(∑ m ∈ Finset.range (2*s+1+1), pcfAiryBeta m*(pcfPhi u)^(6*(2*s+1-m))*(pcfOlverV (2*s+1-m)).eval (pcfInverseZeta u))/u^(3*s+1)) (𝓝[≠] ζ) (𝓝 (pcfAiryC s ζ)) := by
  sorry

/-- Continuous coefficient at zero is supplied by a removable limit. -/
@[dlmf 12.10.E46]
def pcfAiryD (s : ℕ) (ζ : ℝ) : ℝ :=
  limUnder (𝓝[≠] ζ) (fun u : ℝ => (∑ m ∈ Finset.range (2*s+1), pcfAiryAlpha m*(pcfPhi u)^(6*(2*s-m))*(pcfOlverV (2*s-m)).eval (pcfInverseZeta u))/u^(3*s+0))

/-- pcfAiryD limit. -/
@[dlmf 12.10.E46]
theorem pcfAiryD_limit (s : ℕ) {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    Tendsto (fun u : ℝ => (∑ m ∈ Finset.range (2*s+1), pcfAiryAlpha m*(pcfPhi u)^(6*(2*s-m))*(pcfOlverV (2*s-m)).eval (pcfInverseZeta u))/u^(3*s+0)) (𝓝[≠] ζ) (𝓝 (pcfAiryD s ζ)) := by
  sorry

/-- pcfAiryChi. -/
@[dlmf 12.10.E45]
def pcfAiryChi (ζ : ℝ) : ℝ :=
  deriv pcfPhi ζ/pcfPhi ζ

/-- pcfAiryChi formula. -/
@[dlmf 12.10.E45]
theorem pcfAiryChi_formula {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) (hz : ζ ≠ 0) :
    pcfAiryChi ζ=(1-2*pcfInverseZeta ζ*(pcfPhi ζ)^6)/(4*ζ) := by
  sorry

/-- pcfAiryCD derivative. -/
@[dlmf 12.10.E44]
theorem pcfAiryCD_derivative (s : ℕ) {ζ : ℝ} (hζ : -(3*π/4)^(2/3:ℝ) < ζ) :
    pcfAiryC s ζ=pcfAiryChi ζ*pcfAiryA s ζ+deriv (pcfAiryA s) ζ+ζ*pcfAiryB s ζ ∧ pcfAiryD (s+1) ζ=pcfAiryA (s+1) ζ+pcfAiryChi ζ*pcfAiryB s ζ+deriv (pcfAiryB s) ζ := by
  sorry

end AAR.Confluent
