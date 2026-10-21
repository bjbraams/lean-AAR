/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Weber

/-!
# Cylinder asymptotic sectors and real and complex zeros

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- pcfUTerm. -/
def pcfUTerm (a z : ℂ) (s : ℕ) : ℂ :=
  (-1)^s*poch (1/2+a) (2*s)/((s.factorial:ℂ)*(2*z^2)^s)

/-- pcfVTerm. -/
def pcfVTerm (a z : ℂ) (s : ℕ) : ℂ :=
  poch (1/2-a) (2*s)/((s.factorial:ℂ)*(2*z^2)^s)

/-- pcfU sector asymptotic. -/
@[dlmf 12.9.E1]
theorem pcfU_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < 3*π/4) (N : ℕ) :
    (fun z : ℂ => exp (z^2/4)*z^(a+1/2)*pcfU a z-∑ s ∈ Finset.range N, pcfUTerm a z s) =O[sector (3*π/4-δ)] (fun z : ℂ => z^(-(2*N:ℤ))) := by
  exact pcfSect_U_sector a hδ N

/-- pcfV sector asymptotic. -/
@[dlmf 12.9.E2]
theorem pcfV_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/4) (N : ℕ) :
    (fun z : ℂ => (Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2)*pcfV a z-∑ s ∈ Finset.range N, pcfVTerm a z s) =O[sector (π/4-δ)] (fun z : ℂ => z^(-(2*N:ℤ))) := by
  exact pcfSect_V_sector a hδ hδπ N

/-- pcfLogWedge. -/
def pcfLogWedge (lo hi : ℝ) : Filter ℂ :=
  comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | lo ≤ w.im ∧ w.im ≤ hi}

/-- Two-exponential expansion with an absolute sum-of-envelopes remainder and inherited powers. -/
@[dlmf 12.9.E3]
theorem pcfU_adjacent_asymptotic_pos (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun w : ℂ => pcfU a (exp w)-(exp (-exp (2*w)/4-(a+1/2)*w)*(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j)+(1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(1:ℂ)*I*π*a)*exp (exp (2*w)/4+(a-1/2)*w)*(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j))) =O[pcfLogWedge (π/4+δ) (5*π/4-δ)] (fun w : ℂ => ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ)) := by
  have h1 := pcfSect_U_logWedge a hδ (-π) (lo := π/4+δ) (hi := 5*π/4-δ) (by linarith) (by linarith) N
  have h2 := pcfSect_U_logWedge (-a) hδ (-(π/2)) (lo := π/4+δ) (hi := 5*π/4-δ) (by linarith) (by linarith) N
  set C1 : ℂ := (-1:ℂ)*I*exp ((-1:ℂ)*I*π*a)
  set C2 : ℂ := (Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp ((-1:ℂ)*I*π*(a/2-1/4))
  have e2a : ∀ w : ℂ, exp (2 * (w + ((-π : ℝ) : ℂ) * I)) = exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * -π : ℝ)) : ℂ) * I = ((-1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have e2b : ∀ w : ℂ, exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) = -exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * -(π/2) : ℝ)) : ℂ) * I = -(π * I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]; ring
  have hIexp : I = exp (π / 2 * I) := Complex.exp_pi_div_two_mul_I.symm
  have hm1 : (-1 : ℂ) = exp (π * I) := Complex.exp_pi_mul_I.symm
  have hA : ∀ w, C1 * exp (-exp (2 * (w + ((-π : ℝ) : ℂ) * I)) / 4 -
      (a + 1 / 2) * (w + ((-π : ℝ) : ℂ) * I)) = exp (-exp (2*w)/4-(a+1/2)*w) := fun w => by
    have hC1 : C1 = exp (π * I + π / 2 * I + (-1:ℂ) * I * π * a) := by
      rw [Complex.exp_add, Complex.exp_add, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
    rw [hC1, e2a, ← Complex.exp_add]
    exact pcfSect_exp_eq_of_eq_add 1 (by push_cast; ring)
  have hB : ∀ w, C2 * exp (-exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) / 4 -
      (-a + 1 / 2) * (w + ((-(π/2) : ℝ) : ℂ) * I)) = (1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(1:ℂ)*I*π*a) * exp (exp (2*w)/4+(a-1/2)*w) := fun w => by
    have h1 : C2 * exp (-exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) / 4 -
        (-a + 1 / 2) * (w + ((-(π/2) : ℝ) : ℂ) * I)) = (Real.sqrt (2*π):ℂ)/Gamma (1/2+a) *
        exp ((-1:ℂ)*I*π*(a/2-1/4) + (-exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) / 4 -
        (-a + 1 / 2) * (w + ((-(π/2) : ℝ) : ℂ) * I))) := by
      simp only [C2]; rw [Complex.exp_add]; ring
    have h2 : (1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(1:ℂ)*I*π*a) * exp (exp (2*w)/4+(a-1/2)*w) = (Real.sqrt (2*π):ℂ)/Gamma (1/2+a) *
        exp (π / 2 * I + (-(1:ℂ)*I*π*a) + (exp (2*w)/4+(a-1/2)*w)) := by
      rw [Complex.exp_add (π / 2 * I + (-(1:ℂ)*I*π*a)), Complex.exp_add (π / 2 * I),
        Complex.exp_pi_div_two_mul_I]; ring
    rw [h1, h2, e2b]
    congr 1
    exact pcfSect_exp_eq_of_eq_add 0 (by push_cast; ring)
  have he : ∀ w : ℂ, 0 ≤ Real.exp (-2 * N * w.re) := fun w => (Real.exp_pos _).le
  have g1 := pcfSect_isBigO_const_mul_envelope C1 zero_le_one h1 he (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by rw [hA w]; nlinarith [norm_nonneg (exp (exp (2*w)/4+(a-1/2)*w)), he w])
  have g2 := pcfSect_isBigO_const_mul_envelope C2
    (norm_nonneg ((1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(1:ℂ)*I*π*a))) h2 he
    (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hB w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (-exp (2*w)/4-(a+1/2)*w)), he w])
  refine (g1.add g2).congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
  have z1 : exp (w + ((-π:ℝ):ℂ)*I) = -exp w := by
    rw [Complex.exp_add, show ((-π:ℝ):ℂ)*I = -(π*I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]; ring
  have z2 : exp (w + ((-(π/2):ℝ):ℂ)*I) = (-1:ℂ)*I*exp w := by
    rw [Complex.exp_add, show ((-(π/2):ℝ):ℂ)*I = -(π/2*I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_div_two_mul_I, Complex.inv_I]; ring
  have s1 : ∑ s ∈ Finset.range N, pcfSect_uTerm a (exp (w + ((-π:ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfUTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by rw [z1]; exact pcfSect_uTerm_congr_sq a (by ring) s
  have s2 : ∑ s ∈ Finset.range N, pcfSect_uTerm (-a) (exp (w + ((-(π/2):ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfVTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by
      rw [z2]; exact pcfSect_uTerm_neg_eq_vTerm a (by ring_nf; rw [I_sq]; ring) s
  dsimp only
  rw [s1, s2, pcfU_rotated_connection_entire_neg a (exp w), ← z1, ← z2]
  linear_combination (-(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j)) * hA w -
    (∑ j ∈ Finset.range N, pcfVTerm a (exp w) j) * hB w

/-- Two-exponential expansion with an absolute sum-of-envelopes remainder and inherited powers. -/
@[dlmf 12.9.E3]
theorem pcfU_adjacent_asymptotic_neg (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun w : ℂ => pcfU a (exp w)-(exp (-exp (2*w)/4-(a+1/2)*w)*(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j)+(-1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(-1:ℂ)*I*π*a)*exp (exp (2*w)/4+(a-1/2)*w)*(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j))) =O[pcfLogWedge (-(5*π/4-δ)) (-(π/4+δ))] (fun w : ℂ => ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ)) := by
  have h1 := pcfSect_U_logWedge a hδ π (lo := -(5*π/4-δ)) (hi := -(π/4+δ)) (by linarith) (by linarith) N
  have h2 := pcfSect_U_logWedge (-a) hδ (π/2) (lo := -(5*π/4-δ)) (hi := -(π/4+δ)) (by linarith) (by linarith) N
  set C1 : ℂ := (1:ℂ)*I*exp ((1:ℂ)*I*π*a)
  set C2 : ℂ := (Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp ((1:ℂ)*I*π*(a/2-1/4))
  have e2a : ∀ w : ℂ, exp (2 * (w + ((π : ℝ) : ℂ) * I)) = exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * π : ℝ)) : ℂ) * I = ((1 : ℤ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have e2b : ∀ w : ℂ, exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) = -exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * (π/2) : ℝ)) : ℂ) * I = π * I by push_cast; ring,
      Complex.exp_pi_mul_I]; ring
  have hIexp : I = exp (π / 2 * I) := Complex.exp_pi_div_two_mul_I.symm
  have hm1 : (-1 : ℂ) = exp (π * I) := Complex.exp_pi_mul_I.symm
  have hA : ∀ w, C1 * exp (-exp (2 * (w + ((π : ℝ) : ℂ) * I)) / 4 -
      (a + 1 / 2) * (w + ((π : ℝ) : ℂ) * I)) = exp (-exp (2*w)/4-(a+1/2)*w) := fun w => by
    have hC1 : C1 = exp (π / 2 * I + (1:ℂ) * I * π * a) := by
      rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I]; simp only [C1]; ring
    rw [hC1, e2a, ← Complex.exp_add]
    exact pcfSect_exp_eq_of_eq_add 0 (by push_cast; ring)
  have hB : ∀ w, C2 * exp (-exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) / 4 -
      (-a + 1 / 2) * (w + ((π/2 : ℝ) : ℂ) * I)) = (-1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(-1:ℂ)*I*π*a) * exp (exp (2*w)/4+(a-1/2)*w) := fun w => by
    have h1 : C2 * exp (-exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) / 4 -
        (-a + 1 / 2) * (w + ((π/2 : ℝ) : ℂ) * I)) = (Real.sqrt (2*π):ℂ)/Gamma (1/2+a) *
        exp ((1:ℂ)*I*π*(a/2-1/4) + (-exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) / 4 -
        (-a + 1 / 2) * (w + ((π/2 : ℝ) : ℂ) * I))) := by
      simp only [C2]; rw [Complex.exp_add]; ring
    have h2 : (-1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(-1:ℂ)*I*π*a) * exp (exp (2*w)/4+(a-1/2)*w) = (Real.sqrt (2*π):ℂ)/Gamma (1/2+a) *
        exp (-(π / 2 * I) + (-(-1:ℂ)*I*π*a) + (exp (2*w)/4+(a-1/2)*w)) := by
      rw [Complex.exp_add (-(π / 2 * I) + (-(-1:ℂ)*I*π*a)), Complex.exp_add (-(π / 2 * I)),
        Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]; ring
    rw [h1, h2, e2b]
    congr 1
    exact pcfSect_exp_eq_of_eq_add 0 (by push_cast; ring)
  have he : ∀ w : ℂ, 0 ≤ Real.exp (-2 * N * w.re) := fun w => (Real.exp_pos _).le
  have g1 := pcfSect_isBigO_const_mul_envelope C1 zero_le_one h1 he (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by rw [hA w]; nlinarith [norm_nonneg (exp (exp (2*w)/4+(a-1/2)*w)), he w])
  have g2 := pcfSect_isBigO_const_mul_envelope C2
    (norm_nonneg ((-1:ℂ)*I*Real.sqrt (2*π)/Gamma (1/2+a)*exp (-(-1:ℂ)*I*π*a))) h2 he
    (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hB w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (-exp (2*w)/4-(a+1/2)*w)), he w])
  refine (g1.add g2).congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
  have z1 : exp (w + ((π:ℝ):ℂ)*I) = -exp w := by
    rw [Complex.exp_add, show ((π:ℝ):ℂ)*I = π*I by push_cast; ring,
      Complex.exp_pi_mul_I]; ring
  have z2 : exp (w + ((π/2:ℝ):ℂ)*I) = (1:ℂ)*I*exp w := by
    rw [Complex.exp_add, show ((π/2:ℝ):ℂ)*I = π/2*I by push_cast; ring,
      Complex.exp_pi_div_two_mul_I]; ring
  have s1 : ∑ s ∈ Finset.range N, pcfSect_uTerm a (exp (w + ((π:ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfUTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by rw [z1]; exact pcfSect_uTerm_congr_sq a (by ring) s
  have s2 : ∑ s ∈ Finset.range N, pcfSect_uTerm (-a) (exp (w + ((π/2:ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfVTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by
      rw [z2]; exact pcfSect_uTerm_neg_eq_vTerm a (by ring_nf; rw [I_sq]; ring) s
  dsimp only
  rw [s1, s2, pcfU_rotated_connection_entire_pos a (exp w), ← z1, ← z2]
  linear_combination (-(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j)) * hA w -
    (∑ j ∈ Finset.range N, pcfVTerm a (exp w) j) * hB w

/-- Two-exponential expansion with an absolute sum-of-envelopes remainder and inherited powers. -/
@[dlmf 12.9.E4]
theorem pcfV_adjacent_asymptotic_pos (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun w : ℂ => pcfV a (exp w)-((Real.sqrt (2/π):ℂ)*exp (exp (2*w)/4+(a-1/2)*w)*(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j)+(1:ℂ)*I/Gamma (1/2-a)*exp (-exp (2*w)/4-(a+1/2)*w)*(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j))) =O[pcfLogWedge (-π/4+δ) (3*π/4-δ)] (fun w : ℂ => ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ)) := by
  have h1 := pcfSect_U_logWedge a hδ 0 (lo := -π/4+δ) (hi := 3*π/4-δ) (by linarith) (by linarith) N
  have h2 := pcfSect_U_logWedge (-a) hδ (-(π/2)) (lo := -π/4+δ) (hi := 3*π/4-δ) (by linarith) (by linarith) N
  set C1 : ℂ := (1:ℂ)*I/Gamma (1/2-a)
  set C2 : ℂ := (Real.sqrt (2/π):ℂ)*exp (I*π*(a/2-1/4))
  have z1 : ∀ w : ℂ, w + ((0:ℝ):ℂ)*I = w := fun w => by simp
  have e2b : ∀ w : ℂ, exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) = -exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * -(π/2) : ℝ)) : ℂ) * I = -(π * I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_mul_I]; ring
  have hA : ∀ w, C1 * exp (-exp (2 * (w + ((0 : ℝ) : ℂ) * I)) / 4 -
      (a + 1 / 2) * (w + ((0 : ℝ) : ℂ) * I)) = C1 * exp (-exp (2*w)/4-(a+1/2)*w) := fun w => by
    rw [z1]
  have hB : ∀ w, C2 * exp (-exp (2 * (w + ((-(π/2) : ℝ) : ℂ) * I)) / 4 -
      (-a + 1 / 2) * (w + ((-(π/2) : ℝ) : ℂ) * I)) =
      (Real.sqrt (2/π):ℂ) * exp (exp (2*w)/4+(a-1/2)*w) := fun w => by
    simp only [C2]
    rw [e2b, mul_assoc, ← Complex.exp_add]
    congr 1
    exact pcfSect_exp_eq_of_eq_add 0 (by push_cast; ring)
  have he : ∀ w : ℂ, 0 ≤ Real.exp (-2 * N * w.re) := fun w => (Real.exp_pos _).le
  have g1 := pcfSect_isBigO_const_mul_envelope C1 (norm_nonneg C1) h1 he (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hA w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (exp (2*w)/4+(a-1/2)*w)), he w])
  have g2 := pcfSect_isBigO_const_mul_envelope C2
    (norm_nonneg (Real.sqrt (2/π):ℂ)) h2 he
    (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hB w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (-exp (2*w)/4-(a+1/2)*w)), he w])
  refine (g1.add g2).congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
  have z2 : exp (w + ((-(π/2):ℝ):ℂ)*I) = -I*exp w := by
    rw [Complex.exp_add, show ((-(π/2):ℝ):ℂ)*I = -(π/2*I) by push_cast; ring, Complex.exp_neg,
      Complex.exp_pi_div_two_mul_I, Complex.inv_I]; ring
  have s2 : ∑ s ∈ Finset.range N, pcfSect_uTerm (-a) (exp (w + ((-(π/2):ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfVTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by
      rw [z2]; exact pcfSect_uTerm_neg_eq_vTerm a (by ring_nf; rw [I_sq]; ring) s
  dsimp only
  rw [z1, s2, pcfV_eq_mul_neg_I a (exp w), ← z2]
  simp only [C1, C2]
  have hu : ∑ s ∈ Finset.range N, pcfSect_uTerm a (exp w) s =
      ∑ j ∈ Finset.range N, pcfUTerm a (exp w) j := rfl
  rw [hu]
  linear_combination (-(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j)) * hB w

/-- Two-exponential expansion with an absolute sum-of-envelopes remainder and inherited powers. -/
@[dlmf 12.9.E4]
theorem pcfV_adjacent_asymptotic_neg (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun w : ℂ => pcfV a (exp w)-((Real.sqrt (2/π):ℂ)*exp (exp (2*w)/4+(a-1/2)*w)*(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j)+(-1:ℂ)*I/Gamma (1/2-a)*exp (-exp (2*w)/4-(a+1/2)*w)*(∑ j ∈ Finset.range N, pcfUTerm a (exp w) j))) =O[pcfLogWedge (-(3*π/4-δ)) (-(-π/4+δ))] (fun w : ℂ => ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ)) := by
  have h1 := pcfSect_U_logWedge a hδ 0 (lo := -(3*π/4-δ)) (hi := -(-π/4+δ)) (by linarith) (by linarith) N
  have h2 := pcfSect_U_logWedge (-a) hδ (π/2) (lo := -(3*π/4-δ)) (hi := -(-π/4+δ)) (by linarith) (by linarith) N
  set C1 : ℂ := (-1:ℂ)*I/Gamma (1/2-a)
  set C2 : ℂ := (Real.sqrt (2/π):ℂ)*exp (-I*π*(a/2-1/4))
  have z1 : ∀ w : ℂ, w + ((0:ℝ):ℂ)*I = w := fun w => by simp
  have e2b : ∀ w : ℂ, exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) = -exp (2 * w) := fun w => by
    rw [pcfSect_exp_two_mul_add]
    rw [show (((2 * (π/2) : ℝ)) : ℂ) * I = π * I by push_cast; ring,
      Complex.exp_pi_mul_I]; ring
  have hA : ∀ w, C1 * exp (-exp (2 * (w + ((0 : ℝ) : ℂ) * I)) / 4 -
      (a + 1 / 2) * (w + ((0 : ℝ) : ℂ) * I)) = C1 * exp (-exp (2*w)/4-(a+1/2)*w) := fun w => by
    rw [z1]
  have hB : ∀ w, C2 * exp (-exp (2 * (w + ((π/2 : ℝ) : ℂ) * I)) / 4 -
      (-a + 1 / 2) * (w + ((π/2 : ℝ) : ℂ) * I)) =
      (Real.sqrt (2/π):ℂ) * exp (exp (2*w)/4+(a-1/2)*w) := fun w => by
    simp only [C2]
    rw [e2b, mul_assoc, ← Complex.exp_add]
    congr 1
    exact pcfSect_exp_eq_of_eq_add 0 (by push_cast; ring)
  have he : ∀ w : ℂ, 0 ≤ Real.exp (-2 * N * w.re) := fun w => (Real.exp_pos _).le
  have g1 := pcfSect_isBigO_const_mul_envelope C1 (norm_nonneg C1) h1 he (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hA w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (exp (2*w)/4+(a-1/2)*w)), he w])
  have g2 := pcfSect_isBigO_const_mul_envelope C2
    (norm_nonneg (Real.sqrt (2/π):ℂ)) h2 he
    (T := fun w : ℂ =>
    ((‖exp (-exp (2*w)/4-(a+1/2)*w)‖+‖exp (exp (2*w)/4+(a-1/2)*w)‖)*Real.exp (-2*N*w.re):ℝ))
    (fun w => by
      rw [hB w, norm_mul, mul_assoc]
      gcongr
      nlinarith [norm_nonneg (exp (-exp (2*w)/4-(a+1/2)*w)), he w])
  refine (g1.add g2).congr' (Eventually.of_forall fun w => ?_) EventuallyEq.rfl
  have z2 : exp (w + ((π/2:ℝ):ℂ)*I) = I*exp w := by
    rw [Complex.exp_add, show ((π/2:ℝ):ℂ)*I = π/2*I by push_cast; ring,
      Complex.exp_pi_div_two_mul_I]; ring
  have s2 : ∑ s ∈ Finset.range N, pcfSect_uTerm (-a) (exp (w + ((π/2:ℝ):ℂ)*I)) s =
      ∑ j ∈ Finset.range N, pcfVTerm a (exp w) j :=
    Finset.sum_congr rfl fun s _ => by
      rw [z2]; exact pcfSect_uTerm_neg_eq_vTerm a (by ring_nf; rw [I_sq]; ring) s
  dsimp only
  rw [z1, s2, pcfV_eq_mul_I a (exp w), ← z2]
  simp only [C1, C2]
  have hu : ∑ s ∈ Finset.range N, pcfSect_uTerm a (exp w) s =
      ∑ j ∈ Finset.range N, pcfUTerm a (exp w) j := rfl
  rw [hu]
  linear_combination (-(∑ j ∈ Finset.range N, pcfVTerm a (exp w) j)) * hB w

/-- The integral over `(0,∞)` of a positive real function, viewed in `ℂ`, is nonzero. -/
lemma integral_Ioi_ofReal_ne_zero {g : ℝ → ℝ} (hpos : ∀ t ∈ Ioi (0:ℝ), 0 < g t)
    (hint : IntegrableOn (fun t => (g t : ℂ)) (Ioi 0)) : (∫ t in Ioi (0:ℝ), (g t : ℂ)) ≠ 0 := by
  have hg : IntegrableOn g (Ioi 0) := by simpa using hint.re
  rw [integral_complex_ofReal, Complex.ofReal_ne_zero]
  refine (ne_of_gt ((setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hpos t ht).le) hg).2 ?_))
  refine lt_of_lt_of_le (by simp [Real.volume_Ioi]) (measure_mono (s := Ioi (0:ℝ)) fun t ht => ⟨(hpos t ht).ne', ht⟩)

/-- DLMF 12.11(i): absence of real zeros. -/
theorem pcfU_no_real_zero {a : ℝ} (ha : -1/2 ≤ a) (x : ℝ) :
    pcfU a x ≠ 0 := by
  rcases ha.eq_or_lt with h | h
  · rw [← h, show ((-1/2:ℝ):ℂ) = -1/2 by push_cast; ring, pcfU_neg_half]; exact Complex.exp_ne_zero _
  · rw [pcfU_eq_integral (by simpa using h)]
    refine mul_ne_zero (div_ne_zero (Complex.exp_ne_zero _)
      (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))) ?_
    have hc : -1 < ((a:ℂ) - 1/2).re := by simp; linarith
    have heq : ∀ t ∈ Ioi (0:ℝ), (t:ℂ)^((a:ℂ) - 1/2) * exp (-(t:ℂ)^2/2 - x*t) =
        ((t^(a-1/2) * Real.exp (-t^2/2 - x*t) : ℝ) : ℂ) := fun t ht => by
      rw [Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht), Complex.ofReal_exp]; push_cast; ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi heq]
    refine integral_Ioi_ofReal_ne_zero (fun t ht => mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)) ?_
    exact (integrableOn_pcfIntegrand hc x).congr_fun heq measurableSet_Ioi

/-- DLMF 12.11(i): the first real zero lies on the negative axis. -/
theorem pcfU_no_positive_zero {a : ℝ} (h0 : -3/2 < a) (h1 : a < -1/2) {x : ℝ} (hx : 0 < x) :
    pcfU a x ≠ 0 := by
  have hz : 0 < ((x:ℂ)^2/2).re := by
    rw [show (x:ℂ)^2/2 = ((x^2/2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]; positivity
  have hα : 0 < ((a:ℂ)/2+3/4).re := by simp; linarith
  rw [pcfU_kummerU_odd (a:ℂ) (by simpa using hx), kummerU_laplace hα hz]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (by exact_mod_cast hx.ne'))
    (Complex.exp_ne_zero _)) (mul_ne_zero (one_div_ne_zero (Complex.Gamma_ne_zero_of_re_pos hα)) ?_)
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  · have heq : ∀ t ∈ Ioi (0:ℝ), exp (-((x:ℂ)^2/2) * t) * (t:ℂ)^((a:ℂ)/2+3/4-1) *
        (1+(t:ℂ))^((3/2:ℂ)-((a:ℂ)/2+3/4)-1) =
        ((Real.exp (-(x^2/2)*t) * t^((a/2+3/4)-1) * (1+t)^(3/2-(a/2+3/4)-1) : ℝ) : ℂ) := fun t ht => by
      have ht0 : (0:ℝ) ≤ 1 + t := by linarith [show (0:ℝ) < t from ht]
      rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_cpow (le_of_lt ht),
        Complex.ofReal_cpow ht0, Complex.ofReal_exp]
      push_cast; ring_nf
    rw [setIntegral_congr_fun measurableSet_Ioi heq]
    refine integral_Ioi_ofReal_ne_zero (fun t ht => mul_pos (mul_pos (Real.exp_pos _)
      (Real.rpow_pos_of_pos ht _)) (Real.rpow_pos_of_pos (by linarith [show (0:ℝ) < t from ht]) _)) ?_
    exact (kummerU_laplace_integrable (b := 3/2) hα hz).congr_fun heq measurableSet_Ioi

/-- Exact positive real zero count in DLMF 12.11(i). -/
theorem pcfU_positive_zero_count {a : ℝ} (n : ℕ) (hn : 0 < n) (h0 : -2*n-3/2 < a) (h1 : a < -2*n+1/2) :
    Set.Finite {x : ℝ | 0 < x ∧ pcfU a x=0} ∧ ({x : ℝ | 0 < x ∧ pcfU a x=0}:Set ℝ).ncard=n := by
  sorry

/-- Hermite specialization and enclosure of all real zeros. -/
theorem pcfU_hermite_zero_count (n : ℕ) :
    Set.Finite {x : ℝ | pcfU (-n-1/2) x=0} ∧ ({x : ℝ | pcfU (-n-1/2) x=0}:Set ℝ).ncard=n ∧ ∀ x : ℝ, pcfU (-n-1/2) x=0 → |x| ≤ 2*Real.sqrt (n+1/2) := by
  sorry

/-- DLMF 12.11(i): absence of positive real zeros of V. -/
theorem pcfV_no_positive_zero {a : ℝ} (ha : -1/2 < a) {x : ℝ} (hx : 0 < x) :
    pcfV a x ≠ 0 := by
  sorry

/-- DLMF 12.11(i): zeros of V at the origin. -/
theorem pcfV_integer_zero (n : ℤ) :
    pcfV (3/2-2*n) 0=0 := by
  rw [pcfV_zero', pcfVZero]
  rcases le_or_gt 1 n with hn | hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨(n-1).toNat, by omega⟩
    rw [show (1/4:ℂ) + (3/2 - 2*((m+1:ℤ):ℂ))/2 = -(m:ℂ) by push_cast; ring, Complex.Gamma_neg_nat_eq_zero]
    simp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -m := ⟨(-n).toNat, by omega⟩
    rw [show (3/4:ℂ) - (3/2 - 2*((-(m:ℤ):ℤ):ℂ))/2 = -(m:ℂ) by push_cast; ring, Complex.Gamma_neg_nat_eq_zero]
    simp

/-- pcfZeroTau. -/
@[dlmf 12.11.E2]
def pcfZeroTau (a : ℝ) (s : ℕ) : ℂ :=
  (2*s+1/2-a:ℂ)*π+I*log ((π:ℂ)^(-1/2:ℂ)*2^(-a-1/2:ℂ)*Gamma (1/2+a))

/-- pcfZeroLambda. -/
@[dlmf 12.11.E3]
def pcfZeroLambda (a : ℝ) (s : ℕ) : ℂ :=
  log (pcfZeroTau a s)-π*I/2

/-- pcfU complex zero strings. -/
@[dlmf 12.11.E1]
theorem pcfU_complex_zero_strings {a : ℝ} (ha : -1/2 < a) :
    ∃ Z : ℕ → ℂ, (∀ᶠ s in atTop, pcfU a (Z s)=0 ∧ pcfU a (star (Z s))=0 ∧ 0 < (Z s).im) ∧ (fun s => Z s/(exp (3*π*I/4)*(2*pcfZeroTau a s)^(1/2:ℂ))-1+I*a*pcfZeroLambda a s/(2*pcfZeroTau a s)-(2*a^2*(pcfZeroLambda a s)^2-8*a^2*pcfZeroLambda a s+4*a^2+3)/(16*(pcfZeroTau a s)^2)) =O[atTop] (fun s => (pcfZeroLambda a s)^3/(pcfZeroTau a s)^3) := by
  sorry

end DLMF.Confluent
