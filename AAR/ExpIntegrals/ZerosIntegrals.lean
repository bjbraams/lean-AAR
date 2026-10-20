/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ExpIntegrals.Asymptotics

/-!
# Zeros, transforms, sums and computational recurrences, DLMF §§6.13–6.18

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- The unique real zero of Ei. -/
@[dlmf 6.13.E1]
def Real.expIntEiZero  : ℝ :=
  Classical.epsilon (fun x : ℝ => x ≠ 0 ∧ Real.expIntEi x=0)

/-- Positive Ci zeros, indexed from zero. -/
def Real.cosIntZero (k : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ Real.cosInt x=0 ∧ ({y : ℝ | 0 < y ∧ y < x ∧ Real.cosInt y=0} : Set ℝ).ncard=k)

/-- Positive si zeros, indexed from zero. -/
def Real.sinIntTailZero (k : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ Real.sinInt x-π/2=0 ∧ ({y : ℝ | 0 < y ∧ y < x ∧ Real.sinInt y-π/2=0} : Set ℝ).ncard=k)

/-- Real.expIntEi unique zero. -/
theorem Real.expIntEi_unique_zero  :
    Real.expIntEiZero ≠ 0 ∧ Real.expIntEi Real.expIntEiZero=0 ∧ ∀ x : ℝ, x ≠ 0 → Real.expIntEi x=0 → x=Real.expIntEiZero := by
  sorry

/-- Real.expIntEiZero decimal. -/
@[dlmf 6.13.E1]
theorem Real.expIntEiZero_decimal  :
    372507410781366634461991866580/10^30 ≤ Real.expIntEiZero ∧ Real.expIntEiZero < 372507410781366634461991866581/10^30 := by
  sorry

/-- Real.cosIntZero spec. -/
theorem Real.cosIntZero_spec (k : ℕ) :
    0 < Real.cosIntZero k ∧ (Real.cosInt) (Real.cosIntZero k)=0 ∧ ({y : ℝ | 0 < y ∧ y < Real.cosIntZero k ∧ (Real.cosInt) y=0} : Set ℝ).ncard=k := by
  sorry

/-- Real.cosIntZero enumeration. -/
theorem Real.cosIntZero_enumeration  :
    StrictMono Real.cosIntZero ∧ ∀ x : ℝ, 0 < x → ((Real.cosInt) x=0 ↔ ∃ k, Real.cosIntZero k=x) := by
  sorry

/-- Real.sinIntTailZero spec. -/
theorem Real.sinIntTailZero_spec (k : ℕ) :
    0 < Real.sinIntTailZero k ∧ (fun x => Real.sinInt x-π/2) (Real.sinIntTailZero k)=0 ∧ ({y : ℝ | 0 < y ∧ y < Real.sinIntTailZero k ∧ (fun x => Real.sinInt x-π/2) y=0} : Set ℝ).ncard=k := by
  sorry

/-- Real.sinIntTailZero enumeration. -/
theorem Real.sinIntTailZero_enumeration  :
    StrictMono Real.sinIntTailZero ∧ ∀ x : ℝ, 0 < x → ((fun x => Real.sinInt x-π/2) x=0 ↔ ∃ k, Real.sinIntTailZero k=x) := by
  sorry

/-- Shared all-order zero expansions and signed next-term bounds. -/
@[dlmf 6.13.E2]
theorem Real.trigonometric_integral_zero_asymptotics  :
    ∃ c : ℕ → ℝ, (∀ n < 5, c n=([1,1,-16/3,1673/15,-507746/105] : List ℝ)[n]!) ∧ (∀ aux : Bool, let α := fun k : ℕ => ((k : ℝ)+(if aux then 1/2 else 0))*π; let zero := if aux then Real.sinIntTailZero else Real.cosIntZero; HasAsymptoticExpansion atTop (fun n k => (α k)^(-(2*n : ℤ)+1)) c zero ∧ ∀ k N : ℕ, 1 ≤ k → 1 ≤ N → |zero k-∑ n ∈ Finset.range N, c n*(α k)^(-(2*n : ℤ)+1)| ≤ |c N*(α k)^(-(2*N : ℤ)+1)| ∧ 0 ≤ (zero k-∑ n ∈ Finset.range N, c n*(α k)^(-(2*n : ℤ)+1))*(c N*(α k)^(-(2*N : ℤ)+1))) := by
  sorry

/-- expIntE1 laplace. -/
@[dlmf 6.14.E1]
theorem expIntE1_laplace {a : ℂ} (ha : -1 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*genExpIntE 1 t) = if a=0 then 1 else log (1+a)/a := by
  sorry

/-- cosInt laplace. -/
@[dlmf 6.14.E2]
theorem cosInt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*cosInt t) = -log (1+a^2)/(2*a) := by
  sorry

/-- sinIntTail laplace. -/
@[dlmf 6.14.E3]
theorem sinIntTail_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*sinIntTail t) = -arctan a/a := by
  sorry

/-- expIntE1 squared integral. -/
@[dlmf 6.14.E4]
theorem expIntE1_squared_integral  :
    (∫ t : ℝ in Ioi 0, genExpIntE 1 t^2) = 2*Real.log 2 := by
  sorry

/-- cosInt fourier integral. -/
@[dlmf 6.14.E5]
theorem cosInt_fourier_integral  :
    HasIntegralAtTop (fun t : ℝ => cos t*cosInt t) 0 (-π/4) ∧ HasIntegralAtTop (fun t : ℝ => sin t*sinIntTail t) 0 (-π/4) := by
  sorry

/-- trigIntegral squared integrals. -/
@[dlmf 6.14.E6]
theorem trigIntegral_squared_integrals  :
    (∫ t : ℝ in Ioi 0, cosInt t^2) = π/2 ∧ (∫ t : ℝ in Ioi 0, sinIntTail t^2) = π/2 := by
  sorry

/-- trigIntegral product integral. -/
@[dlmf 6.14.E7]
theorem trigIntegral_product_integral  :
    (∫ t : ℝ in Ioi 0, cosInt t*sinIntTail t) = Real.log 2 := by
  sorry

/-- trigIntegral hasSum 1. -/
@[dlmf 6.15.E1]
theorem trigIntegral_hasSum_1  :
    HasSum (fun n : ℕ => cosInt (π*(n+1 : ℂ))) ((Real.log 2-Real.eulerMascheroniConstant)/2) := by
  sorry

/-- trigIntegral hasSum 2. -/
@[dlmf 6.15.E2]
theorem trigIntegral_hasSum_2  :
    HasSum (fun n : ℕ => sinIntTail (π*(n+1 : ℂ))/(n+1 : ℂ)) (π/2*(Real.log π-1)) := by
  sorry

/-- trigIntegral hasSum 3. -/
@[dlmf 6.15.E3]
theorem trigIntegral_hasSum_3  :
    HasSum (fun n : ℕ => (-1 : ℂ)^(n+1)*cosInt (2*π*(n+1 : ℂ))) (1-Real.log 2-Real.eulerMascheroniConstant/2) := by
  sorry

/-- trigIntegral hasSum 4. -/
@[dlmf 6.15.E4]
theorem trigIntegral_hasSum_4  :
    HasSum (fun n : ℕ => (-1 : ℂ)^(n+1)*sinIntTail (2*π*(n+1 : ℂ))/(n+1 : ℂ)) (π*(3/2*Real.log 2-1)) := by
  sorry

/-- Acton auxiliary integral. -/
@[dlmf 6.18.E1]
def expIntActonA (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ)^1*exp (-z*t)/((t : ℂ)^2+1) * ((t : ℂ)^2/(1+(t : ℂ)^2))^n

/-- Acton auxiliary integral. -/
@[dlmf 6.18.E1]
def expIntActonB (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ)^0*exp (-z*t)/((t : ℂ)^2+1) * ((t : ℂ)^2/(1+(t : ℂ)^2))^n

/-- Acton auxiliary integral. -/
@[dlmf 6.18.E1]
def expIntActonC (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ)^0*exp (-z*t)/1 * ((t : ℂ)^2/(1+(t : ℂ)^2))^n

/-- Initial normalization in DLMF §6.18(ii). -/
theorem expIntActon_initial {z : ℂ} (hz : 0 < z.re) :
    expIntActonB 0 z=expIntAuxF z ∧ expIntActonA 0 z=expIntAuxG z ∧ expIntActonC 0 z=1/z := by
  obtain ⟨hf, hg⟩ := expIntAux_laplace_Ioi hz
  refine ⟨?_, ?_, ?_⟩
  · rw [expIntActonB, hf]; simp
  · rw [expIntActonA, hg]; simp only [pow_zero, mul_one, pow_one]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  · rw [expIntActonC]
    have := (laplace_nat_pow hz 0).2
    simpa using this

/-- A bounded continuous real weight against `e^{-zt}`, `Re z > 0`, is integrable on `(0,∞)`. -/
theorem integrableOn_cexp_mul_bounded {z : ℂ} (hz : 0 < z.re) {g : ℝ → ℝ} (hg : Continuous g)
    {K : ℝ} (hK : ∀ t, 0 ≤ t → |g t| ≤ K) :
    IntegrableOn (fun t : ℝ => exp (-z*t)*(g t : ℂ)) (Ioi 0) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hz).const_mul K) ?_ ?_
  · exact (Continuous.mul (by fun_prop) (Complex.continuous_ofReal.comp hg)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hre : (-z*(t:ℂ)).re = -z.re*t := by simp
    rw [hre, mul_comm]
    exact mul_le_mul_of_nonneg_right (hK t (le_of_lt ht)) (Real.exp_pos _).le

/-- `e^{-zt}` times a bounded real weight tends to zero, `Re z > 0`. -/
theorem tendsto_cexp_mul_bounded {z : ℂ} (hz : 0 < z.re) {g : ℝ → ℝ}
    {K : ℝ} (hK : ∀ t, 0 ≤ t → |g t| ≤ K) :
    Tendsto (fun t : ℝ => exp (-z*t)*(g t : ℂ)) atTop (𝓝 0) := by
  have hl : Tendsto (fun t : ℝ => K*Real.exp (-(z.re*t))) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hz)).const_mul K
  refine squeeze_zero_norm' ?_ hl
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have hre : (-z*(t:ℂ)).re = -(z.re*t) := by simp
  rw [hre, mul_comm]
  exact mul_le_mul_of_nonneg_right (hK t ht) (Real.exp_pos _).le

/-- Integration by parts on `(0,∞)` against `e^{-zt}` for a real weight vanishing at zero. -/
theorem integral_cexp_mul_deriv {z : ℂ} (hz : 0 < z.re) {u v : ℝ → ℝ}
    (hu : ∀ t, HasDerivAt u (v t) t) (hv : Continuous v) (h0 : u 0 = 0)
    {K : ℝ} (hK : ∀ t, 0 ≤ t → |u t| ≤ K) {K' : ℝ} (hK' : ∀ t, 0 ≤ t → |v t| ≤ K') :
    (∫ t in Ioi (0:ℝ), exp (-z*t)*(v t : ℂ)) = z*∫ t in Ioi (0:ℝ), exp (-z*t)*(u t : ℂ) := by
  have hc : Continuous u := continuous_iff_continuousAt.mpr fun t => (hu t).continuousAt
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => exp (-z*t)*(u t : ℂ))
      (exp (-z*t)*(v t : ℂ) + (-z)*(exp (-z*t)*(u t : ℂ))) t := by
    have he : HasDerivAt (fun t : ℝ => exp (-z*t)) (exp (-z*t)*(-z)) t := by
      have := ((hasDerivAt_id (t:ℂ)).const_mul (-z)).cexp.comp_ofReal
      simpa using this
    convert he.mul (hu t).ofReal_comp using 1
    ring
  have hi1 := integrableOn_cexp_mul_bounded hz hv hK'
  have hi2 := (integrableOn_cexp_mul_bounded hz hc hK).const_mul (-z)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (hd 0).continuousAt.continuousWithinAt
    (fun t _ => hd t) (hi1.add hi2) (tendsto_cexp_mul_bounded hz hK)
  rw [integral_add hi1 hi2, integral_const_mul, h0] at h
  simp only [Complex.ofReal_zero, mul_zero, sub_zero] at h
  linear_combination h

/-- expIntActon recurrence. -/
@[dlmf 6.18.E2]
theorem expIntActon_recurrence {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : 1 ≤ n) :
    expIntActonA (n-1) z=expIntActonA n z+z/(2*n)*expIntActonC n z ∧ expIntActonB (n-1) z=(2*n*expIntActonB n z+z*expIntActonA (n-1) z)/(2*n-1) ∧ expIntActonC (n-1) z=expIntActonC n z+expIntActonB (n-1) z := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m+1 := ⟨n-1, by omega⟩
  simp only [Nat.add_sub_cancel]
  let W : ℝ → ℝ := fun t => t^2/(1+t^2)
  let P : ℝ → ℝ := fun t => 1/(t^2+1)
  let Q : ℝ → ℝ := fun t => t/(t^2+1)
  have hpos (t : ℝ) : 0 < t^2+1 := by positivity
  have hpos' (t : ℝ) : 0 < 1+t^2 := by positivity
  have hW (t : ℝ) : |W t| ≤ 1 := by
    simp only [W]; rw [abs_div, abs_of_nonneg (sq_nonneg t), abs_of_pos (hpos' t),
      div_le_one (hpos' t)]; linarith
  have hP (t : ℝ) : |P t| ≤ 1 := by
    simp only [P]; rw [abs_div, abs_one, abs_of_pos (hpos t), div_le_one (hpos t)]
    nlinarith [sq_nonneg t]
  have hQ (t : ℝ) : |Q t| ≤ 1 := by
    simp only [Q]; rw [abs_div, abs_of_pos (hpos t), div_le_one (hpos t)]
    nlinarith [sq_nonneg (|t|-1), sq_abs t, abs_nonneg t]
  have hWk (k : ℕ) (t : ℝ) : |W t^k| ≤ 1 := by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hW t)
  have hb (f : ℝ → ℝ) (hf : ∀ t, |f t| ≤ 1) (k : ℕ) (t : ℝ) : |f t*W t^k| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg (f t), abs_nonneg (W t^k), hf t, hWk k t]
  have hcW : Continuous W := by
    exact Continuous.div (by fun_prop) (by fun_prop) fun t => (hpos' t).ne'
  have hcP : Continuous P := Continuous.div (by fun_prop) (by fun_prop) fun t => (hpos t).ne'
  have hcQ : Continuous Q := Continuous.div (by fun_prop) (by fun_prop) fun t => (hpos t).ne'
  -- rewrite the three integrals with real weights
  have hA (k : ℕ) : expIntActonA k z = ∫ t in Ioi (0:ℝ), exp (-z*t)*((Q t*W t^k : ℝ) : ℂ) := by
    unfold expIntActonA
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [Q, W]; push_cast; ring
  have hB (k : ℕ) : expIntActonB k z = ∫ t in Ioi (0:ℝ), exp (-z*t)*((P t*W t^k : ℝ) : ℂ) := by
    unfold expIntActonB
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [P, W]; push_cast; ring
  have hC (k : ℕ) : expIntActonC k z = ∫ t in Ioi (0:ℝ), exp (-z*t)*((W t^k : ℝ) : ℂ) := by
    unfold expIntActonC
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [W]; push_cast; ring
  have iA (k : ℕ) : IntegrableOn (fun t : ℝ => exp (-z*t)*((Q t*W t^k : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_cexp_mul_bounded hz (g := fun t => Q t*W t^k) (hcQ.mul (hcW.pow k))
      (fun t _ => hb Q hQ k t)
  have iB (k : ℕ) : IntegrableOn (fun t : ℝ => exp (-z*t)*((P t*W t^k : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_cexp_mul_bounded hz (g := fun t => P t*W t^k) (hcP.mul (hcW.pow k))
      (fun t _ => hb P hP k t)
  have iC (k : ℕ) : IntegrableOn (fun t : ℝ => exp (-z*t)*((W t^k : ℝ) : ℂ)) (Ioi 0) :=
    integrableOn_cexp_mul_bounded hz (g := fun t => W t^k) (hcW.pow k) (fun t _ => hWk k t)
  have hw0 (t : ℝ) : HasDerivAt W (2*t/(1+t^2)^2) t := by
    have h := (hasDerivAt_pow 2 t).div ((hasDerivAt_pow 2 t).const_add 1) (hpos' t).ne'
    refine h.congr_deriv ?_
    field_simp
    push_cast
    ring
  have hq0 (t : ℝ) : HasDerivAt Q ((1-t^2)/(t^2+1)^2) t := by
    have h := (hasDerivAt_id t).div ((hasDerivAt_pow 2 t).add_const 1) (hpos t).ne'
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    push_cast
    ring
  have hm1 : ((m+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  refine ⟨?_, ?_, ?_⟩
  · -- integration by parts against W^(m+1)
    have hd (t : ℝ) : HasDerivAt (fun t => W t^(m+1))
        (2*(m+1)*(Q t*W t^m) - 2*(m+1)*(Q t*W t^(m+1))) t := by
      refine ((hw0 t).pow (m+1)).congr_deriv ?_
      have h1 : 1+t^2 ≠ 0 := (hpos' t).ne'
      have h2 : t^2+1 ≠ 0 := (hpos t).ne'
      simp only [Q, W, Nat.add_sub_cancel, div_pow]
      field_simp
      push_cast
      ring
    have hv : Continuous (fun t => 2*(m+1)*(Q t*W t^m) - 2*(m+1)*(Q t*W t^(m+1))) := by
      have := hcQ; have := hcW; fun_prop
    have h := integral_cexp_mul_deriv hz hd hv (by simp [W]) (fun t _ => hWk (m+1) t)
      (K' := 2*(m+1)+2*(m+1)) (fun t _ => by
        refine le_trans (abs_sub _ _) (add_le_add ?_ ?_) <;>
        · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*(m+1))]
          exact mul_le_of_le_one_right (by positivity) (hb Q hQ _ t))
    have hs : (∫ t in Ioi (0:ℝ), exp (-z*t)*(((2*(m+1)*(Q t*W t^m) - 2*(m+1)*(Q t*W t^(m+1))) : ℝ) : ℂ)) =
        2*(m+1)*expIntActonA m z - 2*(m+1)*expIntActonA (m+1) z := by
      rw [hA, hA, ← integral_const_mul, ← integral_const_mul, ← integral_sub
        ((iA m).const_mul _) ((iA (m+1)).const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      push_cast; ring
    rw [hs, ← hC] at h
    push_cast at hm1 ⊢
    field_simp
    linear_combination h
  · -- integration by parts against Q W^m
    have hd (t : ℝ) : HasDerivAt (fun t => Q t*W t^m)
        ((2*m+1)*(P t*W t^m) - (2*m+2)*(P t*W t^(m+1))) t := by
      refine ((hq0 t).mul ((hw0 t).pow m)).congr_deriv ?_
      have h1 : 1+t^2 ≠ 0 := (hpos' t).ne'
      have h2 : t^2+1 ≠ 0 := (hpos t).ne'
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · subst h0; simp only [P, W, Pi.pow_apply, pow_zero, zero_add, pow_one, div_pow]; field_simp; ring
      · obtain ⟨j, rfl⟩ : ∃ j, m = j+1 := ⟨m-1, by omega⟩
        simp only [P, Q, W, Nat.add_sub_cancel, Pi.pow_apply, div_pow]
        field_simp
        push_cast
        ring
    have hv : Continuous (fun t => (2*m+1)*(P t*W t^m) - (2*m+2)*(P t*W t^(m+1))) := by
      have := hcP; have := hcW; fun_prop
    have h := integral_cexp_mul_deriv hz hd hv (by simp [Q]) (fun t _ => hb Q hQ m t)
      (K' := (2*m+1)+(2*m+2)) (fun t _ => by
        refine le_trans (abs_sub _ _) (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*m+1)]
          exact mul_le_of_le_one_right (by positivity) (hb P hP _ t)
        · rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*m+2)]
          exact mul_le_of_le_one_right (by positivity) (hb P hP _ t))
    have hs : (∫ t in Ioi (0:ℝ), exp (-z*t)*((((2*m+1)*(P t*W t^m) - (2*m+2)*(P t*W t^(m+1))) : ℝ) : ℂ)) =
        (2*m+1)*expIntActonB m z - (2*m+2)*expIntActonB (m+1) z := by
      rw [hB, hB, ← integral_const_mul, ← integral_const_mul, ← integral_sub
        ((iB m).const_mul _) ((iB (m+1)).const_mul _)]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      push_cast; ring
    rw [hs, ← hA] at h
    have h2 : (2*((m+1:ℕ):ℂ)-1) ≠ 0 := by
      push_cast
      intro h0; have := congrArg Complex.re h0; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    rw [eq_div_iff h2]
    push_cast
    linear_combination h
  · rw [hC, hC, hB, ← integral_add (iC (m+1)) (iB m)]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have : W t^m = W t^(m+1) + P t*W t^m := by
      have h1 : 1+t^2 ≠ 0 := (hpos' t).ne'
      have h2 : t^2+1 ≠ 0 := (hpos t).ne'
      simp only [W, P, div_pow]; field_simp; ring
    rw [← mul_add, ← Complex.ofReal_add, ← this]

end AAR.Confluent
