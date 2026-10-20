/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.SpecialValues
public import AAR.IncompleteGamma.SeriesRecurrences
public import AAR.Confluent.Integrals
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Generalized exponential integral, DLMF §8.19

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- Generalized exponential integral on the logarithmic plane. -/
def genExpIntEOnLog (p w : ℂ) : ℂ :=
  exp ((p-1)*w)*upperIncGammaOnLog (1-p) w

/-- Extension at zero in Re p>1; the old plain function keeps its totalized value. -/
def genExpIntEExtended (p z : ℂ) : ℂ :=
  if z=0 then 1/(p-1) else genExpIntE p z

/-- genExpIntE horizontal integral. -/
@[dlmf 8.19.E2]
theorem genExpIntE_horizontal_integral (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(-p)*exp (-(z+t))) 0 (z^(1-p)*genExpIntE p z) := by
  have h := (upperIncGamma_horizontal_integral (1-p) hz).congr
    (g := fun t : ℝ => (z+t)^(-p)*exp (-(z+t))) fun t _ => by rw [show 1-p-1 = -p by ring]
  convert h using 1
  rw [genExpIntE, ← mul_assoc, ← cpow_add _ _ (slitPlane_ne_zero hz)]
  simp

/-- genExpIntE laplace complex. -/
@[dlmf 8.19.E3]
theorem genExpIntE_laplace_complex (p : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genExpIntE p z=∫ t : ℝ in Ioi 1, exp (-z*t)*(t : ℂ)^(-p) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  have hU := kummerU_laplace (a:=1) (b:=2-p) (z:=z) (by norm_num) hz
  simp only [Gamma_one, div_one, one_div_one, one_mul, sub_self, cpow_zero, mul_one,
    show (2-p:ℂ)-1-1 = -p by ring] at hU
  rw [genExpIntE_eq_exp_mul_kummerU p hz0, hU, ← integral_const_mul]
  have ht := setIntegral_Ioi_comp_add_right
    (fun s : ℝ => exp (-z*s)*(s:ℂ)^(-p)) 0 1
  simp only [zero_add] at ht
  rw [← ht]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  push_cast
  rw [show -z*((t:ℂ)+1) = -z + -z*t by ring, Complex.exp_add]
  rw [add_comm (1:ℂ) t]
  ring

/-- genExpIntE stieltjes. -/
@[dlmf 8.19.E4]
theorem genExpIntE_stieltjes {p z : ℂ} (hp : 0 < p.re) (hz : 0 < z.re) :
    genExpIntE p z=z^(p-1)*exp (-z)/Gamma p*(∫ t : ℝ in Ioi 0, (t : ℂ)^(p-1)*exp (-z*t)/(1+t)) := by
  rw [genExpIntE_eq_cpow_mul_kummerU, kummerU_laplace hp hz]
  have hI : (∫ t : ℝ in Ioi 0, exp (-z*t)*(t : ℂ)^(p-1)*(1+(t:ℂ))^(p-p-1)) =
      ∫ t : ℝ in Ioi 0, (t : ℂ)^(p-1)*exp (-z*t)/(1+t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [sub_self, zero_sub, cpow_neg_one]
    rw [div_eq_mul_inv]
    ring
  rw [hI]
  ring

/-- `z log z → 0` as `z → 0`, `z ≠ 0`, in `ℂ`. -/
lemma tendsto_mul_log_nhdsNE_zero :
    Tendsto (fun z : ℂ => z * log z) (𝓝[≠] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hc : Tendsto (fun z : ℂ => |‖z‖ * Real.log ‖z‖| + π * ‖z‖) (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Continuous (fun z : ℂ => |‖z‖ * Real.log ‖z‖| + π * ‖z‖) :=
      ((Real.continuous_mul_log.comp continuous_norm).abs).add (continuous_const.mul continuous_norm)
    simpa using (h1.tendsto 0).mono_left nhdsWithin_le_nhds
  refine squeeze_zero (fun _ => norm_nonneg _) (fun z => ?_) hc
  rw [norm_mul]
  calc ‖z‖ * ‖log z‖ ≤ ‖z‖ * (|Real.log ‖z‖| + π) := by
        gcongr
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [log_re, log_im]
        gcongr
        exact abs_arg_le_pi z
    _ = _ := by rw [abs_mul, abs_norm]; ring

/-- genExpIntEExtended zero. -/
@[dlmf 8.19.E6]
theorem genExpIntEExtended_zero {p : ℂ} (hp : 1 < p.re) :
    genExpIntEExtended p 0=1/(p-1) ∧ ContinuousAt (genExpIntEExtended p) 0 := by
  have hval : genExpIntEExtended p 0 = 1/(p-1) := by simp [genExpIntEExtended]
  refine ⟨hval, ?_⟩
  have hp1 : p - 1 ≠ 0 := fun h => by
    have := congrArg re h; simp at this; linarith
  have hG : Gamma (1 - (2 - p)) / Gamma (1 - (2 - p) + 1) = 1/(p-1) := by
    have hG0 : Gamma (p - 1) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    rw [show (1:ℂ) - (2 - p) = p - 1 by ring, Gamma_add_one _ hp1]
    field_simp
  have hU : Tendsto (fun z => kummerU 1 (2 - p) z) (𝓝[≠] 0) (𝓝 (1/(p-1))) := by
    rw [← hG, ← tendsto_sub_nhds_zero_iff]
    rw [show (1:ℂ) - (2 - p) + 1 = 1 - (2 - p) + 1 by ring]
    by_cases hb : (2 - p).re ≤ 0
    · by_cases hb0 : 2 - p = 0
      · have h := (isBigO_kummerU_at_zero_b_zero 1).trans_tendsto tendsto_mul_log_nhdsNE_zero
        rw [hb0]
        simpa using h
      · exact ((isBigO_kummerU_at_zero_re_nonpos 1 (2 - p) hb hb0).mono nhdsWithin_le_nhds).trans_tendsto
          ((continuous_id.tendsto' 0 0 rfl).mono_left nhdsWithin_le_nhds)
    · push Not at hb
      refine (isBigO_kummerU_at_zero_re_zero_to_one 1 (2 - p) hb (by simp; linarith)).trans_tendsto ?_
      have hr : 0 < ((1 - (2 - p).re : ℝ) : ℂ).re := by simp; linarith
      have hc := (continuousAt_cpow_zero_of_re_pos hr).tendsto.comp
        ((continuous_id.prodMk continuous_const).tendsto (0 : ℂ))
      have h0 : (0 : ℂ) ^ (((1 - (2 - p).re : ℝ) : ℂ)) = 0 :=
        zero_cpow (fun h => by rw [h] at hr; simp at hr)
      simp only [Function.comp_def, id] at hc
      rw [h0] at hc
      exact_mod_cast hc.mono_left nhdsWithin_le_nhds
  have hE : Tendsto (genExpIntEExtended p) (𝓝[≠] 0) (𝓝 (1/(p-1))) := by
    have he : Tendsto (fun z : ℂ => exp (-z)) (𝓝[≠] 0) (𝓝 1) := by
      simpa using (continuous_neg.cexp.tendsto 0).mono_left nhdsWithin_le_nhds
    refine ((he.mul hU).congr' ?_).trans (by rw [one_mul])
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 0 := hz
    simp only [genExpIntEExtended, hz', ↓reduceIte, genExpIntE_eq_exp_mul_kummerU p hz']
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hval]
  exact hE

/-- genExpIntE nat finite. -/
@[dlmf 8.19.E7]
theorem genExpIntE_nat_finite {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    genExpIntE n z=(-z)^(n-1)/(n-1).factorial*genExpIntE 1 z+exp (-z)/(n-1).factorial*(∑ k ∈ Finset.range (n-1), ((n-k-2).factorial : ℂ)*(-z)^k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n-2, by omega⟩
  have h := upperIncGamma_neg_nat_finite (m+1) hz
  rw [show m+2-1 = m+1 by omega, genExpIntE]
  push_cast
  rw [show (1:ℂ)-(m+2) = -((m:ℂ)+1) by ring, show (m:ℂ)+2-1 = ((m+1:ℕ):ℂ) by push_cast; ring,
    cpow_natCast]
  push_cast at h
  rw [h]
  have hsum : (∑ k ∈ Finset.range (m+1), ((m+2-k-2).factorial : ℂ)*(-z)^k) =
      ∑ k ∈ Finset.range (m+1), (-1:ℂ)^(m+k)*(k.factorial : ℂ)*z^(m-k) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m-k, by omega⟩
    rw [show k+j+1-1-k = j by omega, show k+j+2-j-2 = k by omega, show k+j-k = j by omega,
      neg_pow, pow_add]
    have hk2 : ((-1:ℂ)^k)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    linear_combination -(-1:ℂ)^j*(k.factorial:ℂ)*z^j*hk2
  have hterm : ∀ k ∈ Finset.range (m+1), z^(m+1)*((-1:ℂ)^(m+1)/((m+1).factorial : ℂ)*(exp (-z)*
      ((-1:ℂ)^k*(k.factorial:ℂ)/z^(k+1)))) =
      -(exp (-z)/((m+1).factorial : ℂ)*((-1:ℂ)^(m+k)*(k.factorial : ℂ)*z^(m-k))) := by
    intro k hk
    rw [Finset.mem_range] at hk
    obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m-k, by omega⟩
    rw [show k+j-k = j by omega]
    have hzk : z^(k+1) ≠ 0 := pow_ne_zero _ hz
    rw [show k+j+1 = j+(k+1) by ring, pow_add z, pow_add (-1:ℂ) j (k+1),
      show k+j+k = j+2*k by ring, pow_add (-1:ℂ) j (2*k), pow_mul, neg_one_sq, one_pow]
    have hk2 : ((-1:ℂ)^k)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    field_simp
    rw [pow_succ]
    linear_combination (-(k.factorial : ℂ) / ((j + (k + 1)).factorial : ℂ)) * hk2
  have hS : z^(m+1)*((-1:ℂ)^(m+1)/((m+1).factorial : ℂ)*(exp (-z)*
      ∑ k ∈ Finset.range (m+1), (-1:ℂ)^k*(k.factorial:ℂ)/z^(k+1))) =
      -(exp (-z)/((m+1).factorial : ℂ)*
        ∑ k ∈ Finset.range (m+1), (-1:ℂ)^(m+k)*(k.factorial : ℂ)*z^(m-k)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hterm
  rw [hsum, neg_pow z]
  linear_combination -hS

/-- genExpIntE nat hasSum. -/
@[dlmf 8.19.E8]
theorem genExpIntE_nat_hasSum {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => if k=n-1 then 0 else (-z)^k/((k.factorial : ℂ)*(1-(n : ℂ)+k))) ((-z)^(n-1)/(n-1).factorial*(digamma n-log z)-genExpIntE n z) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have h := upperIncGamma_neg_nat_hasSum m hz
  simp only [Nat.add_sub_cancel]
  convert h using 1
  · funext k
    push_cast
    rw [show 1-((m:ℂ)+1)+k = k - m by ring]
  · rw [genExpIntE, zpow_natCast, neg_pow]
    push_cast
    rw [show (m:ℂ)+1-1 = m by ring, show 1-((m:ℂ)+1) = -m by ring, cpow_natCast]
    ring

/-- genExpIntE nat digamma series. -/
@[dlmf 8.19.E9]
theorem genExpIntE_nat_digamma_series {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    genExpIntE n z=(-1 : ℂ)^n*z^(n-1)/(n-1).factorial*log z+exp (-z)/(n-1).factorial*(∑ k ∈ Finset.range (n-1), (-z)^k*Gamma (n-(k+1)))+exp (-z)*(-z)^(n-1)/(n-1).factorial*(∑' k : ℕ, z^k/(k.factorial : ℂ)*digamma (k+1)) := by
  sorry

/-- Excluding positive integral `p` excludes nonpositive integral `1-p`. -/
lemma one_sub_ne_neg_nat {p : ℂ} (hp : ∀ n : ℕ, p ≠ n+1) : ∀ n : ℕ, 1-p ≠ -n :=
  fun n h => hp n (by linear_combination -h)

/-- genExpIntE hasSum noninteger. -/
@[dlmf 8.19.E10]
theorem genExpIntE_hasSum_noninteger {p : ℂ} (hp : ∀ n : ℕ, p ≠ n+1) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (-z)^k/((k.factorial : ℂ)*(1-p+k))) (z^(p-1)*Gamma (1-p)-genExpIntE p z) := by
  have h := (upperIncGamma_hasSum_alternating (one_sub_ne_neg_nat hp) hz).mul_left (z^(p-1))
  rw [genExpIntE, ← mul_sub]
  refine h.congr_fun fun k => ?_
  rw [cpow_add _ _ hz, cpow_natCast, neg_pow]
  have hp1 : z^(p-1)*z^(1-p) = 1 := by rw [← cpow_add _ _ hz]; simp
  linear_combination -(-1:ℂ)^k*z^k/((k.factorial : ℂ)*(1-p+k)) * hp1

/-- genExpIntE hasSum exponential. -/
@[dlmf 8.19.E11]
theorem genExpIntE_hasSum_exponential {p : ℂ} (hp : ∀ n : ℕ, p ≠ n+1) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => exp (-z)*z^k/Gamma (2-p+k)) (z^(p-1)-genExpIntE p z/Gamma (1-p)) := by
  have ha := one_sub_ne_neg_nat hp
  have h := scIncGamma_hasSum_exponential (1-p) z
  rw [scIncGamma_eq ha hz] at h
  convert h using 1
  · funext k; congr 2; ring
  · have hc := lowerIncGamma_add_upperIncGamma ha hz
    rw [genExpIntE, show -(1-p) = p-1 by ring]
    field_simp [Gamma_ne_zero ha]
    linear_combination -z^(p-1)*hc

/-- The required limiting interpretation at positive integral p. -/
@[dlmf 8.19.E10, dlmf 8.19.E11]
theorem genExpIntE_series_integer_limits {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun p : ℂ => z^(p-1)*Gamma (1-p)-∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(1-p+k))) (𝓝[≠] (n : ℂ)) (𝓝 (genExpIntE n z)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n-1, by omega⟩
  have hcont : Continuous fun p : ℂ => genExpIntE p z :=
    ((continuous_const_cpow' hz).comp (continuous_id.sub continuous_const)).mul
      ((upperIncGamma_parameter_entire hz).continuous.comp (continuous_const.sub continuous_id))
  have hmap : Tendsto (fun p : ℂ => 1-p) (𝓝[≠] ((m+1:ℕ) : ℂ)) (𝓝[≠] (-(m:ℂ))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun p : ℂ => 1-p) (𝓝 ((m+1:ℕ) : ℂ)) (𝓝 (1-((m+1:ℕ) : ℂ))) :=
        (continuous_const.sub continuous_id).tendsto _
      convert h.mono_left nhdsWithin_le_nhds using 2; push_cast; ring
    · filter_upwards [self_mem_nhdsWithin] with p hp
      simp only [mem_compl_iff, mem_singleton_iff] at hp ⊢
      intro h
      apply hp
      push_cast
      linear_combination -h
  have hev := hmap.eventually (eventually_nhdsNE_neg_nat_ne m)
  refine ((hcont.tendsto _).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [hev] with p hp
  have hp' : ∀ k : ℕ, p ≠ k+1 := fun k h => hp k (by rw [h]; ring)
  rw [(genExpIntE_hasSum_noninteger hp' hz).tsum_eq]
  ring

/-- genExpIntE scaled derivative. -/
@[dlmf 8.19.E14]
theorem genExpIntE_scaled_derivative (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun t => exp t*genExpIntE p t) (exp z*genExpIntE p z*(1+(p-1)/z)-1/z) z := by
  have hz0 := slitPlane_ne_zero hz
  have h := ((hasDerivAt_id z).cexp).mul (hasDerivAt_genExpIntE p hz)
  have hr := genExpIntE_add_one (p-1) hz0
  rw [sub_add_cancel] at hr
  simp only [id_eq] at h
  refine h.congr_deriv ?_
  have he := Complex.exp_add z (-z)
  simp only [add_neg_cancel, Complex.exp_zero] at he
  field_simp
  linear_combination -exp z * hr + he

/-- genExpIntE parameter derivatives. -/
@[dlmf 8.19.E15]
theorem genExpIntE_parameter_derivatives (j : ℕ) (p : ℂ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv j (fun q => genExpIntE q z) p=(-1 : ℂ)^j*(∫ t : ℝ in Ioi 1, (Real.log t : ℂ)^j*(t : ℂ)^(-p)*exp (-z*t)) := by
  sorry

/-- genExpIntE continuedFraction. -/
@[dlmf 8.19.E17]
theorem genExpIntE_continuedFraction (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasContinuedFraction (fun k => if k=0 then exp (-z) else if Odd k then p+((k-1)/2 : ℕ) else ((k/2 : ℕ) : ℂ)) (fun k => if Even k then z else 1) (genExpIntE p z) := by
  sorry

/-- genExpIntEOnLog monodromy. -/
@[dlmf 8.19.E18]
theorem genExpIntEOnLog_monodromy {p : ℂ} (hp : ∀ n : ℤ, p ≠ n) (w : ℂ) (m : ℤ) :
    genExpIntEOnLog p (w+2*m*π*I)=2*π*I*exp (m*p*π*I)/Gamma p*sin (m*p*π)/sin (p*π)*exp ((p-1)*w)+genExpIntEOnLog p w := by
  have ha : ∀ n : ℕ, 1-p ≠ -n := fun n h => hp (n+1) (by push_cast; linear_combination -h)
  have hp0 : ∀ n : ℕ, p ≠ -n := fun n h => hp (-n) (by rw [h]; push_cast; ring)
  have hs : Complex.sin (p*π) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    exact hp k (mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) hk)
  have hG := Gamma_ne_zero hp0
  have hr := Complex.Gamma_mul_Gamma_one_sub p
  rw [mul_comm (π:ℂ) p] at hr
  unfold genExpIntEOnLog
  rw [show w+2*m*π*I=w+2*π*m*I by ring, upperIncGammaOnLog_monodromy w m ha]
  have e1 : exp ((p-1)*(w+2*π*m*I))*exp (2*π*m*I*(1-p))=exp ((p-1)*w) := by
    rw [← Complex.exp_add, show (p-1)*(w+2*π*m*I)+2*π*m*I*(1-p)=(p-1)*w by ring]
  have e2 : exp ((p-1)*(w+2*π*m*I))=exp (m*p*π*I)*exp (m*p*π*I)*exp ((p-1)*w) := by
    have := exp_add_two_pi_int_mul_I ((p-1)*w+2*m*p*π*I) (-m)
    rw [← Complex.exp_add, ← Complex.exp_add,
      show m*p*π*I+m*p*π*I+(p-1)*w=(p-1)*w+2*m*p*π*I by ring, ← this]; congr 1; push_cast; ring
  have e3 : exp (m*p*π*I)*exp (2*π*m*I*(1-p))=exp (-(m*p*π*I)) := by
    rw [← Complex.exp_add]
    have := exp_add_two_pi_int_mul_I (-(m*p*π*I)) m
    rw [← this]; congr 1; ring
  have hsin : Complex.sin (m*p*π)*(2*I)=exp (m*p*π*I)-exp (-(m*p*π*I)) := by
    rw [Complex.sin]; ring_nf; rw [I_sq]; ring
  rw [mul_add, ← mul_assoc, e1]
  have hG1 : Gamma (1-p)=π/(Complex.sin (p*π)*Gamma p) := by
    rw [eq_div_iff (mul_ne_zero hs hG)]; rw [eq_div_iff hs] at hr; linear_combination hr
  rw [hG1]
  rw [e2]
  linear_combination exp (m*p*π*I)*exp ((p-1)*w)*π*(Complex.sin (p*π)*Gamma p)⁻¹*(-e3-hsin)

/-- genExpIntEOnLog nat monodromy. -/
@[dlmf 8.19.E18]
theorem genExpIntEOnLog_nat_monodromy {n : ℕ} (hn : 1 ≤ n) (w : ℂ) (m : ℤ) :
    genExpIntEOnLog n (w+2*m*π*I)=genExpIntEOnLog n w+2*π*I*m*(-1 : ℂ)^n/(n-1).factorial*exp (((n : ℂ)-1)*w) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  unfold genExpIntEOnLog
  have h1 : (1:ℂ)-((k+1:ℕ):ℂ) = -(k:ℂ) := by push_cast; ring
  have he : exp ((((k+1:ℕ):ℂ)-1)*(w+2*m*π*I))=exp ((((k+1:ℕ):ℂ)-1)*w) := by
    have := exp_add_two_pi_int_mul_I ((((k+1:ℕ):ℂ)-1)*w) (k*m)
    rw [← this]; congr 1; push_cast; ring
  rw [h1, he, show w+2*m*π*I=w+2*π*m*I by ring, upperIncGammaOnLog_neg_nat_monodromy,
    show k+1-1=k by omega, pow_succ]
  ring

/-- genExpIntEOnLog nonpos nat monodromy. -/
@[dlmf 8.19.E18]
theorem genExpIntEOnLog_nonpos_nat_monodromy (n : ℕ) (w : ℂ) (m : ℤ) :
    genExpIntEOnLog (-n) (w+2*m*π*I)=genExpIntEOnLog (-n) w := by
  unfold genExpIntEOnLog
  have ha : ∀ k : ℕ, 1-(-(n:ℂ)) ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have he : exp ((-(n:ℂ)-1)*(w+2*m*π*I))=exp ((-(n:ℂ)-1)*w) := by
    have := exp_add_two_pi_int_mul_I ((-(n:ℂ)-1)*w) (-(n+1)*m)
    rw [← this]; congr 1; push_cast; ring
  have he2 : exp (2*π*m*I*(1-(-(n:ℂ))))=1 := by
    have := exp_add_two_pi_int_mul_I 0 ((n+1)*m)
    rw [Complex.exp_zero] at this
    rw [show 2*π*m*I*(1-(-(n:ℂ)))=0+2*π*(((n+1)*m : ℤ):ℂ)*I by push_cast; ring]; exact this
  rw [he, show w+2*m*π*I=w+2*π*m*I by ring, upperIncGammaOnLog_monodromy w m ha, he2]
  ring

/-- Each nonzero-argument branch is entire in p. -/
theorem genExpIntEOnLog_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun p => genExpIntEOnLog p w) := by
  unfold genExpIntEOnLog
  have h := (upperIncGammaOnLog_parameter_entire w).comp (differentiable_const (1:ℂ) |>.sub differentiable_id)
  exact (by fun_prop : Differentiable ℂ fun p : ℂ => exp ((p-1)*w)).mul (by simpa [Function.comp_def] using h)

/-- Nontrivial monodromy except at nonpositive integral order. -/
theorem genExpIntEOnLog_branch_point {p : ℂ} (hp : ∀ n : ℕ, p ≠ -n) (w : ℂ) :
    genExpIntEOnLog p (w+2*π*I) ≠ genExpIntEOnLog p w := by
  by_cases hz : ∀ n : ℤ, p ≠ n
  · have h := genExpIntEOnLog_monodromy hz w 1
    have hs : Complex.sin (p*π) ≠ 0 := by
      rw [Complex.sin_ne_zero_iff]
      intro k hk
      exact hz k (mul_right_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero) hk)
    push_cast at h
    simp only [one_mul, mul_one] at h
    rw [h]
    intro h'
    have h0 := add_eq_right.mp h'
    rw [mul_div_assoc, div_self hs, mul_one] at h0
    simp [Gamma_ne_zero hp, Real.pi_ne_zero, I_ne_zero, Complex.exp_ne_zero] at h0
  · push Not at hz
    obtain ⟨n, rfl⟩ := hz
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k+1 := by
      rcases Int.eq_nat_or_neg n with ⟨j, rfl | rfl⟩
      · rcases j with _ | j
        · exact absurd (by simp) (hp 0)
        · exact ⟨j, by push_cast; ring⟩
      · exact absurd (by push_cast; ring) (hp j)
    subst hk
    have h := genExpIntEOnLog_nat_monodromy (n := k+1) (by omega) w 1
    push_cast at h ⊢
    simp only [mul_one] at h
    rw [h]
    intro h'
    have h0 := add_eq_left.mp h'
    simp [Real.pi_ne_zero, I_ne_zero, Complex.exp_ne_zero, Nat.factorial_ne_zero] at h0

/-- genExpIntE nat order bounds. -/
@[dlmf 8.19.E19]
theorem genExpIntE_nat_order_bounds {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ((n : ℝ)-1)/n*(genExpIntE n x).re < (genExpIntE (n+1) x).re ∧ (genExpIntE (n+1) x).re < (genExpIntE n x).re := by
  sorry

/-- genExpIntE nat logconvex. -/
@[dlmf 8.19.E20]
theorem genExpIntE_nat_logconvex {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (genExpIntE n x).re^2 < (genExpIntE (n-1 : ℕ) x).re*(genExpIntE (n+1) x).re := by
  sorry

/-- genExpIntE nat rational bounds. -/
@[dlmf 8.19.E21]
theorem genExpIntE_nat_rational_bounds {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    1/(x+n) < Real.exp x*(genExpIntE n x).re ∧ Real.exp x*(genExpIntE n x).re ≤ 1/(x+n-1) := by
  sorry

/-- genExpIntE nat ratio derivative. -/
@[dlmf 8.19.E22]
theorem genExpIntE_nat_ratio_derivative {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    0 < deriv (fun y : ℝ => (genExpIntE n y).re/(genExpIntE (n-1 : ℕ) y).re) x := by
  sorry

/-- genExpIntE tail integral. -/
@[dlmf 8.19.E23]
theorem genExpIntE_tail_integral (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => genExpIntE (p-1) (z+t)) 0 (genExpIntE p z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -genExpIntE p (z+t)) (genExpIntE (p-1) (z+t)) t := by
    intro t ht
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -genExpIntE p w)
      (hasDerivAt_genExpIntE p (add_ofReal_mem_slitPlane hz ht)).neg).congr_deriv ?_
    ring
  have hc : ContinuousOn (fun t : ℝ => genExpIntE (p-1) (z+t)) (Ici 0) := fun t ht =>
    (hasDerivAt_comp_add_ofReal (hasDerivAt_genExpIntE (p-1)
      (add_ofReal_mem_slitPlane hz ht))).continuousAt.continuousWithinAt
  have hl : Tendsto (fun t : ℝ => -genExpIntE p (z+t)) atTop (𝓝 0) := by
    have h := ((tendsto_exp_neg_mul_kummerU_sectorAtTop 1 (2-p) (by norm_num : (0:ℝ) < 1/2)).comp
      (tendsto_add_ofReal_sectorAtTop z)).neg
    rw [neg_zero] at h
    refine h.congr' ?_
    have := (tendsto_norm_sectorAtTop (1/2)).comp (tendsto_add_ofReal_sectorAtTop z)
    filter_upwards [this.eventually_gt_atTop 0] with t ht
    have ht0 : z+t ≠ 0 := by intro h0; simp [h0] at ht
    simp [genExpIntE_eq_exp_mul_kummerU p ht0]
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  simpa using h

/-- genExpIntE nat laplace. -/
@[dlmf 8.19.E24]
theorem genExpIntE_nat_laplace {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : -1 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*genExpIntE n t)=if a=0 then 1/(n : ℂ) else (-1 : ℂ)^(n-1)/a^n*(log (1+a)+∑ k ∈ Finset.range (n-1), (-1 : ℂ)^(k+1)*a^(k+1)/(k+1)) := by
  sorry

/-- The displayed formula also needs Re b>0 for convergence at zero. -/
@[dlmf 8.19.E25]
theorem genExpIntE_mellin_laplace {a b p : ℂ} (ha : -1 < a.re) (hb : 0 < b.re) (hpb : 1 < (p+b).re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*(t : ℂ)^(b-1)*genExpIntE p t)=Gamma b*(1+a)^(-b)/(p+b-1)*Gamma (p+b)*AAR.Hypergeometric.regularizedGaussHG 1 b (p+b) (a/(1+a)) := by
  have hz : 0 < (1+a).re := by simp; linarith
  have hz0 : (1+a) ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  have hL := laplace_kummerU (a := p) (b := b+p-1) (c := p) (z := 1+a)
    (by simp at hpb ⊢; linarith) (by simp; linarith) hz
  have hI : (∫ t : ℝ in Ioi 0, exp (-a*t)*(t : ℂ)^(b-1)*genExpIntE p t) =
      ∫ t : ℝ in Ioi 0, exp (-(1+a)*t)*(t : ℂ)^(b+p-1-1)*kummerU p p t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [genExpIntE_eq_cpow_mul_kummerU, show b+p-1-1 = (b-1)+(p-1) by ring, cpow_add _ _ ht0,
      show -(1+a)*(t:ℂ) = -a*t + -t by ring, Complex.exp_add]
    ring
  rw [hI, hL]
  have hx : 1 - (1+a)⁻¹ = a/(1+a) := by field_simp; ring
  have hcut : a/(1+a) ∈ cutPlane := by
    rw [mem_cutPlane, ← hx, sub_sub_cancel]
    exact Or.inl (by rw [inv_re]; exact div_pos hz (normSq_pos.mpr hz0))
  rw [hx, show p+(b+p-1)-p+1 = p+b by ring, show b+p-1-p+1 = b by ring,
    regularizedGaussHG_euler _ _ _ hcut,
    show p+b-p = b by ring, show p+b-(b+p-1) = 1 by ring, show b-(b+p-1) = 1-p by ring,
    regularizedGaussHG_symm b 1 _ hcut, ← hx, sub_sub_cancel,
    inv_cpow _ _ (by
      intro h
      have := (arg_eq_pi_iff.mp h).1
      linarith)]
  have hpb1 : p+b-1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this hpb; linarith
  have hG : Gamma (p+b) = (p+b-1)*Gamma (p+b-1) := by
    rw [← Complex.Gamma_add_one _ hpb1]; ring_nf
  have hc : (1+a)^(-(b+p-1)) = (1+a)^(-b) * (1+a)^(1-p) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  have hc1 : (1+a)^(1-p) ≠ 0 := by simp [hz0]
  rw [hG, hc, show b+p-1 = p+b-1 by ring]
  field_simp

/-- The auxiliary integral L(p) for positive p. -/
@[dlmf 8.19.E27]
def genExpIntL (p : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, exp (-t : ℂ)*genExpIntE p t

/-- genExpIntL hypergeometric. -/
@[dlmf 8.19.E27]
theorem genExpIntL_hypergeometric {p : ℝ} (hp : 0 < p) :
    genExpIntL p=Gamma (1+(p : ℂ))/(2*p)*AAR.Hypergeometric.regularizedGaussHG 1 1 (1+p) (1/2) := by
  have h := genExpIntE_mellin_laplace (a := 1) (b := 1) (p := p) (by norm_num) (by norm_num)
    (by simp; linarith)
  rw [genExpIntL]
  have hI : (∫ t : ℝ in Ioi 0, exp (-t : ℂ)*genExpIntE p t) =
      ∫ t : ℝ in Ioi 0, exp (-1*t)*(t : ℂ)^((1:ℂ)-1)*genExpIntE p t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp
  rw [hI, h, Gamma_one, show (1:ℂ)+1 = 2 by norm_num, add_comm (p:ℂ) 1, cpow_neg_one]
  have hp0 : (p:ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  rw [show (1:ℂ)+p-1 = p by ring]
  field_simp

/-- genExpIntE product integral. -/
@[dlmf 8.19.E26]
theorem genExpIntE_product_integral {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p+q) :
    (∫ t : ℝ in Ioi 0, genExpIntE p t*genExpIntE q t)=(genExpIntL p+genExpIntL q)/(p+q-1) := by
  sorry

/-- The error-to-exponential-integral relation with its square-argument continuation. -/
@[dlmf 7.11.E3]
theorem erfc_genExpIntEOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erfc z=z/Real.sqrt π*genExpIntEOnLog (1/2) (2*log z) := by
  rw [genExpIntEOnLog, show (1:ℂ)-1/2 = 1/2 by norm_num, upperIncGammaOnLog_half,
    show 2*log z/2=log z by ring, Complex.exp_log hz,
    show ((1:ℂ)/2-1)*(2*log z) = -log z by ring, Complex.exp_neg, Complex.exp_log hz]
  have hp : (Real.sqrt π:ℂ)≠0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp

end AAR.Confluent
