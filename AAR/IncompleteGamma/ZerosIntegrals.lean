/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.SpecialValues
public import AAR.Confluent.Integrals
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.Bernoulli

/-!
# Zeros, transforms and sums, DLMF §§8.13–8.15

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- The negative x-zero when it exists. -/
def Real.scIncGammaNegativeZero (a : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x < 0 ∧ scIncGamma a x=0)

/-- The positive x-zero when it exists. -/
def Real.scIncGammaPositiveZero (a : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ scIncGamma a x=0)

/-- A complex sum of nonnegative real terms with positive leading term is nonzero. -/
lemma ne_zero_of_hasSum_ofReal_nonneg {f : ℕ → ℝ} {S : ℂ} (h : HasSum (fun k => (f k : ℂ)) S)
    (hf : ∀ k, 0 ≤ f k) (h0 : 0 < f 0) : S ≠ 0 := by
  have hr : HasSum f S.re := by
    have := (Complex.reCLM.hasSum h)
    simpa using this
  have hS : S = (S.re : ℂ) := by
    have hi := (Complex.imCLM.hasSum h)
    simp at hi
    apply Complex.ext <;> simp [hi.unique hasSum_zero]
  rw [hS]
  exact ofReal_ne_zero.mpr (lt_of_lt_of_le h0 (le_hasSum hr 0 fun j _ => hf j)).ne'

/-- scIncGamma nonnegative parameter no real zeros. -/
theorem scIncGamma_nonnegative_parameter_no_real_zeros {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    scIncGamma a x ≠ 0 := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have := scIncGamma_neg_nat 0 (x:ℂ)
    simp only [Nat.cast_zero, neg_zero, pow_zero] at this
    rw [ofReal_zero, this]; exact one_ne_zero
  have hG : ∀ k : ℕ, 0 < Real.Gamma (a+k+1) := fun k => Real.Gamma_pos_of_pos (by positivity)
  rcases le_or_gt 0 x with hx | hx
  · have h := scIncGamma_hasSum_exponential (a:ℂ) x
    refine ne_zero_of_hasSum_ofReal_nonneg (f := fun k => Real.exp (-x)*x^k/Real.Gamma (a+k+1))
      ?_ (fun k => by have := hG k; positivity) (by have := hG 0; simp; positivity)
    refine h.congr_fun fun k => ?_
    rw [show (a:ℂ)+k+1 = ((a+k+1 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; rfl
  · have hs := (hasFPowerSeriesOnBall_regularizedConfluent (a:ℂ) (a+1)).hasSum_mul_pow
      (by simp : ((-x:ℝ):ℂ) ∈ Metric.eball (0:ℂ) ⊤)
    rw [ofReal_neg, regularizedConfluent_self_succ_neg] at hs
    refine ne_zero_of_hasSum_ofReal_nonneg
      (f := fun k => (ascPochhammer ℝ k).eval a/(k.factorial*Real.Gamma (a+1+k))*(-x)^k)
      ?_ (fun k => by
        have := ascPochhammer_pos k a hpos
        have : 0 < Real.Gamma (a+1+k) := Real.Gamma_pos_of_pos (by positivity)
        have : 0 ≤ -x := by linarith
        positivity) (by
        have : 0 < Real.Gamma (a+1+0) := Real.Gamma_pos_of_pos (by positivity)
        simp; positivity)
    refine hs.congr_fun fun k => ?_
    rw [regularizedHGFunCoeff_singleton, poch_ofReal,
      show (a:ℂ)+1+k = ((a+1+k : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast
    ring

/-- scIncGamma one negative zero. -/
theorem scIncGamma_one_negative_zero {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 1-2*(n : ℝ) < a) (ha1 : a < 2-2*(n : ℝ)) :
    Real.scIncGammaNegativeZero a < 0 ∧ ∀ x : ℝ, scIncGamma a x=0 ↔ x=Real.scIncGammaNegativeZero a := by
  sorry

/-- scIncGamma two real zeros. -/
theorem scIncGamma_two_real_zeros {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : -2*(n : ℝ) < a) (ha1 : a < 1-2*(n : ℝ)) :
    Real.scIncGammaNegativeZero a < 0 ∧ 0 < Real.scIncGammaPositiveZero a ∧ ∀ x : ℝ, scIncGamma a x=0 ↔ x=Real.scIncGammaNegativeZero a ∨ x=Real.scIncGammaPositiveZero a := by
  sorry

/-- Real.scIncGammaNegativeZero strictAnti. -/
theorem Real.scIncGammaNegativeZero_strictAnti  :
    StrictAntiOn Real.scIncGammaNegativeZero (Ioo (-1) 0) := by
  sorry

/-- Real.scIncGammaNegativeZero bounds. -/
@[dlmf 8.13.E1]
theorem Real.scIncGammaNegativeZero_bounds {a : ℝ} (ha0 : -1 < a) (ha1 : a < 0) :
    1+1/a < Real.scIncGammaNegativeZero a ∧ Real.scIncGammaNegativeZero a < Real.log |a| := by
  sorry

/-- The double parameter-zero pair (a_n*,x_n*). -/
def scIncGammaDoubleZero (n : ℕ) : ℝ × ℝ :=
  Classical.epsilon (fun p : ℝ × ℝ => -2*(n : ℝ) < p.1 ∧ p.1 < 1-2*(n : ℝ) ∧ 0 < p.2 ∧ scIncGamma p.1 p.2=0 ∧ deriv (fun a : ℂ => scIncGamma a p.2) p.1=0)

/-- scIncGamma two parameter zeros negative x. -/
theorem scIncGamma_two_parameter_zeros_negative_x {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x < 0) :
    ({a : ℝ | -2*(n : ℝ) < a ∧ a < 2-2*(n : ℝ) ∧ scIncGamma a x=0} : Set ℝ).ncard=2 := by
  sorry

/-- scIncGamma two parameter zeros positive x. -/
theorem scIncGamma_two_parameter_zeros_positive_x {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) (hx1 : x < (scIncGammaDoubleZero n).2) :
    ({a : ℝ | -2*(n : ℝ) < a ∧ a < 1-2*(n : ℝ) ∧ scIncGamma a x=0} : Set ℝ).ncard=2 := by
  sorry

/-- At coalescence the two zeros are counted with multiplicity, not as distinct points. -/
theorem scIncGamma_double_parameter_zero {n : ℕ} (hn : 1 ≤ n) :
    let p := scIncGammaDoubleZero n; -2*(n : ℝ) < p.1 ∧ p.1 < 1-2*(n : ℝ) ∧ 0 < p.2 ∧ scIncGamma p.1 p.2=0 ∧ deriv (fun a : ℂ => scIncGamma a p.2) p.1=0 ∧ iteratedDeriv 2 (fun a : ℂ => scIncGamma a p.2) p.1 ≠ 0 ∧ ({a : ℝ | -2*(n : ℝ) < a ∧ a < 1-2*(n : ℝ) ∧ scIncGamma a p.2=0} : Set ℝ).ncard=1 := by
  sorry

/-- scIncGamma parameter zeros at x zero. -/
theorem scIncGamma_parameter_zeros_at_x_zero (a : ℝ) :
    scIncGamma a 0=0 ↔ ∃ n : ℕ, 1 ≤ n ∧ a = -(n : ℝ) := by
  have h := scIncGamma_hasSum_exponential (a:ℂ) 0
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.sum_range_one, pow_zero, neg_zero, Complex.exp_zero, one_mul, Nat.cast_zero,
    add_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
    mul_zero, zero_div] at h
  have h0 := (hasSum_zero.unique h)
  rw [show scIncGamma a 0 = 1/Gamma (a+1) by linear_combination -h0, one_div, inv_eq_zero,
    Complex.Gamma_eq_zero_iff]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m+1, by omega, ?_⟩
    have := congrArg Complex.re hm
    simp at this; push_cast; linarith
  · rintro ⟨n, hn, rfl⟩
    refine ⟨n-1, ?_⟩
    rw [Nat.cast_sub hn]; push_cast; ring

/-- scIncGamma conjugate zero trajectories. -/
theorem scIncGamma_conjugate_zero_trajectories {n : ℕ} (hn : 1 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ f : ℝ → ℂ, ContinuousOn f (Icc (scIncGammaDoubleZero n).2 ((scIncGammaDoubleZero n).2+δ)) ∧ f (scIncGammaDoubleZero n).2=(scIncGammaDoubleZero n).1 ∧ ∀ x ∈ Ioo (scIncGammaDoubleZero n).2 ((scIncGammaDoubleZero n).2+δ), 0 < (f x).im ∧ scIncGamma (f x) x=0 ∧ scIncGamma (star (f x)) x=0 := by
  sorry

/-- The lower Gamma in the exponentially weighted regularized Kummer normalization. -/
theorem lowerIncGamma_eq_exp_regularized {b : ℂ} (hb : ∀ k : ℕ, b≠-k) (x : ℂ) :
    lowerIncGamma b x=Gamma b*x^b*exp (-x)*regularizedHGFun {1} {b+1} x := by
  rw [lowerIncGamma_eq_regularized hb,
    regularizedConfluent_kummer_transform b (b+1) (-x)]
  simp only [show b+1-b=1 by ring, neg_neg]
  ring

/-- normIncGammaP laplace. -/
@[dlmf 8.14.E1]
theorem normIncGammaP_laplace {a b : ℂ} (ha : 0 < a.re) (hb : -1 < b.re) :
    (∫ x : ℝ in Ioi 0, exp (-a*x)*normIncGammaPContinued b x)=(1+a)^(-b)/a := by
  have ha0 := ne_zero_of_re_pos ha
  have ha1 : 1+a≠0 := ne_zero_of_re_pos (by simp; linarith)
  have hi : (∫ x : ℝ in Ioi 0, exp (-a*x)*normIncGammaPContinued b x)=
      ∫ x : ℝ in Ioi 0, exp (-(1+a)*x)*(x:ℂ)^((b+1)-1)*regularizedHGFun {1} {b+1} x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [normIncGammaPContinued,scIncGamma, add_sub_cancel_right]
    have he : exp (-a*x)*exp (-(x:ℂ))=exp (-(1+a)*x) := by rw [← Complex.exp_add]; congr 1; ring
    linear_combination (x:ℂ)^b*regularizedHGFun {1} {b+1} x*he
  rw [hi,laplace_regularizedHGFun_self (by simp; linarith) (by simp; linarith),
    show -(b+1)= -b-1 by ring, cpow_sub _ _ ha1, cpow_one, cpow_neg_one]
  field_simp [ha0]
  ring

/-- upperIncGamma laplace. -/
@[dlmf 8.14.E2]
theorem upperIncGamma_laplace {a b : ℂ} (ha : -1 < a.re) (hb : -1 < b.re) :
    (∫ x : ℝ in Ioi 0, exp (-a*x)*upperIncGamma b x)=if a=0 then Gamma (b+1) else if b=0 then log (1+a)/a else Gamma b*(1-(1+a)^(-b))/a := by
  have hm := (laplace_kummerU_gauss (a:=1-b) (b:=1) (c:=1-b) (z:=1+a)
    (by simp) (by simp only [sub_re,one_re]; linarith) (by simp; linarith)).2
  have hi : (∫ x : ℝ in Ioi 0, exp (-a*x)*upperIncGamma b x)=
      ∫ x : ℝ in Ioi 0, tricomiLaplaceKernel (1-b) 1 (1-b) (1+a) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [upperIncGamma,tricomiLaplaceKernel]
    simp only [sub_self,cpow_zero,mul_one]
    rw [← mul_assoc,← Complex.exp_add]
    congr 2
    ring
  rw [hi,hm,show 1-(1-b)+1=b+1 by ring,show (1-b)+1-(1-b)+1=(2:ℂ) by ring,
    show 1-(1+a)= -a by ring,Gamma_one,one_mul]
  have hcut : -a∈cutPlane := by change 1-(-a)∈slitPlane; left; simp; linarith
  rw [regularizedGaussHG_symm 1 (b+1) 2 hcut,
    regularizedGaussHG_eq_regularizedGaussHGIntegral (by norm_num) (by norm_num) hcut]
  simp only [regularizedGaussHGIntegral,eulerKernel,sub_self,cpow_zero,one_mul,
    show (2:ℂ)-1-1=0 by ring,show (2:ℂ)-1=1 by ring,Gamma_one,inv_one]
  simp_rw [show ∀ t : ℝ, 1-(-a)*(t:ℂ)=1+a*t by intro t; ring]
  have hslit (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : 1+a*(t:ℂ)∈slitPlane := by
    left
    simp only [add_re,one_re,mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
    by_cases h : 0≤a.re
    · nlinarith [mul_nonneg h ht.1]
    · have hp := mul_nonneg (show 0≤ -a.re by linarith) (show 0≤1-t by linarith [ht.2])
      nlinarith
  have hcont : ContinuousOn (fun t : ℝ => (1+a*(t:ℂ))^(-(b+1))) (Icc (0:ℝ) 1) :=
    (by fun_prop : Continuous (fun t : ℝ => 1+a*(t:ℂ))).continuousOn.cpow_const hslit
  have hint : IntervalIntegrable (fun t : ℝ => (1+a*(t:ℂ))^(-(b+1))) volume 0 1 := hcont.intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1)
  by_cases ha0 : a=0
  · subst a
    simp
  rw [if_neg ha0]
  by_cases hb0 : b=0
  · subst b
    rw [if_pos rfl]
    norm_num only [zero_add,Gamma_one,one_mul,neg_add_rev,neg_zero,add_zero] at *
    have hd (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) :
        HasDerivAt (fun u : ℝ => log (1+a*(u:ℂ))/a) ((1+a*(t:ℂ))^(-1:ℂ)) t := by
      have ht' : t∈Icc (0:ℝ) 1 := by simpa using ht
      have h := (((hasDerivAt_id (t:ℂ)).const_mul a).const_add 1).clog (hslit t ht')
      have h' := (h.div_const a).comp_ofReal
      refine (h'.congr_of_eventuallyEq (Eventually.of_forall fun u=>rfl)).congr_deriv ?_
      simp only [id_eq,mul_one,cpow_neg_one]
      field_simp
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
    simpa using hh
  rw [if_neg hb0]
  have hd (t : ℝ) (ht : t∈uIcc (0:ℝ) 1) :
      HasDerivAt (fun u : ℝ => (1+a*(u:ℂ))^(-b)/(-a*b)) ((1+a*(t:ℂ))^(-(b+1))) t := by
    have ht' : t∈Icc (0:ℝ) 1 := by simpa using ht
    have h := (((hasDerivAt_id (t:ℂ)).const_mul a).const_add 1).cpow_const (c:= -b) (hslit t ht')
    have h' := (h.div_const (-a*b)).comp_ofReal
    refine (h'.congr_of_eventuallyEq (Eventually.of_forall fun u=>rfl)).congr_deriv ?_
    simp only [id_eq,mul_one]
    rw [show -b-1= -(b+1) by ring]
    field_simp
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  simp only [Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,add_zero,one_cpow] at hh
  rw [hh,Gamma_add_one b hb0]
  field_simp
  ring

/-- lowerIncGamma mellin. -/
@[dlmf 8.14.E3]
theorem lowerIncGamma_mellin {a b : ℂ} (ha : a.re < 0) (hab : 0 < (a+b).re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*lowerIncGamma b x) = -Gamma (a+b)/a := by
  have hbpos : 0<b.re := by simp only [add_re] at hab; linarith
  have hb := not_neg_nat_of_re_pos hbpos
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*lowerIncGamma b x)=Gamma b*
      ∫ x : ℝ in Ioi 0, exp (-(x:ℂ))*(x:ℂ)^((a+b)-1)*regularizedHGFun {1} {b+1} x := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [lowerIncGamma_eq_exp_regularized hb]
    have hp : (x:ℂ)^(a-1)*(x:ℂ)^b=(x:ℂ)^((a+b)-1) := by
      rw [← cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]; congr 1; ring
    linear_combination Gamma b*exp (-(x:ℂ))*regularizedHGFun {1} {b+1} x*hp
  rw [hi,mellin_regularizedHGFun_exp hab (by simp only [add_re,sub_re,one_re]; linarith)]
  rw [show b+1-1-(a+b)= -a by ring, show b+1-1=b by ring,
    show b+1-(a+b)= -a+1 by ring, Gamma_add_one (-a) (by intro h; simp at h; simp [h] at ha)]
  have hg := Gamma_ne_zero_of_re_pos hbpos
  have hga := Gamma_ne_zero_of_re_pos (show 0<(-a).re by simpa)
  field_simp

/-- upperIncGamma mellin. -/
@[dlmf 8.14.E4]
theorem upperIncGamma_mellin {a b : ℂ} (ha : 0 < a.re) (hab : 0 < (a+b).re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*upperIncGamma b x)=Gamma (a+b)/a := by
  have hm := (laplace_kummerU_gauss (a:=1-b) (b:=a) (c:=1-b) (z:=1)
    ha (by simp only [sub_re,one_re]; simp only [add_re] at hab; linarith) (by simp)).2
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*upperIncGamma b x)=
      ∫ x : ℝ in Ioi 0, tricomiLaplaceKernel (1-b) a (1-b) 1 x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    simp only [upperIncGamma,tricomiLaplaceKernel,one_mul]
    ring
  rw [hi,hm]
  rw [show a-(1-b)+1=a+b by ring, show 1-b+a-(1-b)+1=a+1 by ring]
  simp only [sub_self]
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ (by simp)]
  rw [regularizedGaussHGFun_eq_div_Gamma (not_neg_nat_of_re_pos (by simp; linarith))]
  simp only [ordinaryHypergeometric_zero]
  rw [Gamma_add_one a (ne_zero_of_re_pos ha)]
  field_simp [Gamma_ne_zero_of_re_pos ha]

/-- lowerIncGamma mellin laplace. -/
@[dlmf 8.14.E5]
theorem lowerIncGamma_mellin_laplace {a b s : ℂ} (hs : 0 < s.re) (hab : 0 < (a+b).re) (hb : ∀ n : ℕ, b ≠ -n) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*exp (-s*x)*lowerIncGamma b x)=Gamma (a+b)/(b*(1+s)^(a+b))*Gamma (1+b)*AAR.Hypergeometric.regularizedGaussHG 1 (a+b) (1+b) (1/(1+s)) := by
  have hm := laplace_regularizedHGFun (a:=1) (b:=a+b) (c:=b+1) (k:=1) (z:=1+s)
    hab (by simp; linarith) (by simp; linarith)
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*exp (-s*x)*lowerIncGamma b x)=Gamma b*
      ∫ x : ℝ in Ioi 0, exp (-(1+s)*x)*(x:ℂ)^((a+b)-1)*regularizedHGFun {1} {b+1} (1*x) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [lowerIncGamma_eq_exp_regularized hb]
    have hp : (x:ℂ)^(a-1)*(x:ℂ)^b=(x:ℂ)^((a+b)-1) := by
      rw [← cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]; congr 1; ring
    have he : exp (-s*x)*exp (-(x:ℂ))=exp (-(1+s)*x) := by rw [← Complex.exp_add]; congr 1; ring
    simp only [one_mul]
    calc
      _ = Gamma b*((x:ℂ)^(a-1)*(x:ℂ)^b)*(exp (-s*x)*exp (-(x:ℂ)))*regularizedHGFun {1} {b+1} x := by ring
      _ = _ := by rw [hp,he]; ring
  rw [hi,hm,show (1:ℂ)+b=b+1 by ring, Gamma_add_one b (by simpa using hb 0), cpow_neg]
  field_simp [show b≠0 by simpa using hb 0]

/-- upperIncGamma mellin laplace. -/
@[dlmf 8.14.E6]
theorem upperIncGamma_mellin_laplace {a b s : ℂ} (hs : -1 < s.re) (hab : 0 < (a+b).re) (ha : 0 < a.re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*exp (-s*x)*upperIncGamma b x)=Gamma (a+b)/(a*(1+s)^(a+b))*Gamma (1+a)*AAR.Hypergeometric.regularizedGaussHG 1 (a+b) (1+a) (s/(1+s)) := by
  have hm := (laplace_kummerU_gauss (a:=1) (b:=a+b) (c:=b+1) (z:=1+s)
    hab (by simp only [add_re,sub_re,one_re]; linarith) (by simp; linarith)).2
  have hi : (∫ x : ℝ in Ioi 0, (x:ℂ)^(a-1)*exp (-s*x)*upperIncGamma b x)=
      ∫ x : ℝ in Ioi 0, tricomiLaplaceKernel 1 (a+b) (b+1) (1+s) x := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [upperIncGamma_eq_cpow_mul_kummerU _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]
    unfold tricomiLaplaceKernel
    have hp : (x:ℂ)^(a-1)*(x:ℂ)^b=(x:ℂ)^((a+b)-1) := by
      rw [← cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ne_of_gt hx))]; congr 1; ring
    have he : exp (-s*x)*exp (-(x:ℂ))=exp (-(1+s)*x) := by rw [← Complex.exp_add]; congr 1; ring
    calc
      _ = ((x:ℂ)^(a-1)*(x:ℂ)^b)*(exp (-s*x)*exp (-(x:ℂ)))*kummerU 1 (b+1) x := by ring
      _ = _ := by rw [hp,he]; ring
  rw [hi,hm,show a+b-(b+1)+1=a by ring, show 1+(a+b)-(b+1)+1=a+1 by ring,
    show 1-(1+s)= -s by ring]
  have hcut : -s∈cutPlane := by change 1-(-s)∈slitPlane; left; simp; linarith
  rw [regularizedGaussHG_pfaff (a+b) a (a+1) hcut,
    show (a+1)-a=1 by ring, show 1-(-s)=1+s by ring,
    show (-s)/(-s-1)=s/(1+s) by rw [show -s-1= -(1+s) by ring, neg_div_neg_eq]]
  have hmap : s/(1+s)∈cutPlane := by
    convert div_sub_one_mem_cutPlane hcut using 1
    rw [show -s-1= -(1+s) by ring, neg_div_neg_eq]
  rw [regularizedGaussHG_symm (a+b) 1 (a+1) hmap]
  rw [show (1:ℂ)+a=a+1 by ring,Gamma_add_one a (ne_zero_of_re_pos ha),cpow_neg]
  field_simp [ne_zero_of_re_pos ha]

/-- lowerIncGamma multiplication hasSum. -/
@[dlmf 8.15.E1]
theorem lowerIncGamma_multiplication_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (u v : ℂ) :
    HasSum (fun k : ℕ => exp (a*v)*lowerIncGammaOnLog (a+k) u*(1-exp v)^k/(k.factorial : ℂ)) (lowerIncGammaOnLog a (u+v)) := by
  sorry

/-- Complex-argument Hurwitz zeta by Euler–Maclaurin continuation; used only for 8.15.2. -/
def hurwitzZetaComplex (s z : ℂ) : ℂ :=
  let M := ⌈(1-s.re)/2⌉₊+1; limUnder atTop (fun N : ℕ => (∑ n ∈ Finset.range N, (z+n)^(-s))+(z+N)^(1-s)/(s-1)+(z+N)^(-s)/2+∑ k ∈ Finset.range M, (bernoulli (2*k+2) : ℂ)/(2*k+2).factorial*poch s (2*k+1)*(z+N)^(-s-(2*k+1)))

/-- Bridge to Mathlib; its existing Hurwitz zeta is periodic in a real second argument. -/
theorem hurwitzZetaComplex_mathlib {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {s : ℂ} (hs : s ≠ 1) :
    hurwitzZetaComplex s x=HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s := by
  sorry

/-- Inherited logarithms and a right-half-plane convergence domain are explicit. -/
@[dlmf 8.15.E2]
theorem incompleteGamma_hurwitz_fourier_sum {a z : ℂ} (ha : a ≠ -1) (hz : 0 < z.re) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    HasSum (fun k : ℕ => let j : ℂ := k+1; a*(exp (2*π*I*j*(z+h))/(2*π*I*j)^(a+1)*upperIncGammaOnLog a (log z+log (2*π*j)+π*I/2)+exp (-2*π*I*j*(z+h))/(-2*π*I*j)^(a+1)*upperIncGammaOnLog a (log z+log (2*π*j)-π*I/2))) (hurwitzZetaComplex (-a) (z+h)+z^(a+1)/(a+1)+(h-1/2)*z^a) := by
  sorry

/-- The function F(p,x) approximated in DLMF §8.27(i). -/
def Real.gammaDiDonatoF (p x : ℝ) : ℝ :=
  x^(-p)*Real.exp (x^2/2)*(∫ t : ℝ in Ioi x, Real.exp (-t^2/2)*t^p)

/-- The explicit approximation denominator in DLMF §8.27(i). -/
def Real.gammaDiDonatoH (p x : ℝ) : ℝ :=
  3*(x^2-p)+Real.sqrt ((x^2-p)^2+8*(x^2+p))

/-- The change of variable mentioned in DLMF §8.27(i). -/
theorem Real.gammaDiDonato_gamma (p : ℝ) {x : ℝ} (hx : 0 < x) :
    (Real.gammaDiDonatoF p x : ℂ)=(x : ℂ)^(-(p : ℂ))*Real.exp (x^2/2)*(2 : ℂ)^(((p : ℂ)-1)/2)*upperIncGamma ((p+1)/2) (x^2/2) := by
  have hx2 : 0 < x^2/2 := by positivity
  have hU := upperIncGamma_eq_integral (((p:ℂ)+1)/2) hx2
  push_cast at hU
  rw [hU]
  -- real substitution
  have himg : (fun t : ℝ => t^2/2) '' Ioi x = Ioi (x^2/2) := by
    ext u
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have : x^2 < t^2 := by nlinarith
      linarith
    · intro hu
      refine ⟨Real.sqrt (2*u), ?_, ?_⟩
      · rw [show x = Real.sqrt (x^2) from (Real.sqrt_sq hx.le).symm]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
      · rw [Real.sq_sqrt (by nlinarith [sq_nonneg x])]; ring
  have hsub := integral_image_eq_integral_abs_deriv_smul (s := Ioi x) (f := fun t : ℝ => t^2/2)
    (f' := fun t => t) measurableSet_Ioi
    (fun t _ => by
      have := ((hasDerivAt_pow 2 t).div_const 2)
      convert this.hasDerivWithinAt using 1; push_cast; ring)
    (fun s hs t ht hst => by
      simp only at hst
      have h1 : 0 < s := lt_trans hx hs
      have h2 : 0 < t := lt_trans hx ht
      nlinarith [sq_nonneg (s-t), sq_nonneg (s+t)])
    (fun u : ℝ => (u : ℂ)^(((p:ℂ)+1)/2-1)*cexp (-(u:ℂ)))
  rw [himg] at hsub
  have key : (∫ t : ℝ in Ioi x, ((Real.exp (-t^2/2)*t^p : ℝ) : ℂ)) =
      (2:ℂ)^(((p:ℂ)-1)/2) * ∫ u : ℝ in Ioi (x^2/2), (u : ℂ)^(((p:ℂ)+1)/2-1)*cexp (-(u:ℂ)) := by
    rw [hsub, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := lt_trans hx ht
    simp only [Complex.real_smul]
    rw [abs_of_pos ht0]
    have hq : ((t^2/2 : ℝ) : ℂ)^(((p:ℂ)+1)/2-1) = ((t^(p-1)/2^((p-1)/2) : ℝ) : ℂ) := by
      rw [show ((p:ℂ)+1)/2-1 = (((p-1)/2 : ℝ) : ℂ) by push_cast; ring,
        ← ofReal_cpow (by positivity), Real.div_rpow (by positivity) (by norm_num),
        ← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
      congr 3; push_cast; ring
    have h2 : (2:ℂ)^(((p:ℂ)-1)/2) = ((2^((p-1)/2) : ℝ) : ℂ) := by
      rw [ofReal_cpow (by norm_num)]; push_cast; ring_nf
    have htp : t^p = t * t^(p-1) := by
      conv_lhs => rw [show p = 1 + (p-1) by ring]
      rw [Real.rpow_add ht0, Real.rpow_one]
    have h2p : (0:ℝ) < 2^((p-1)/2) := by positivity
    have h2c : ((2^((p-1)/2) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr h2p.ne'
    rw [hq, h2, htp]
    push_cast
    rw [show -(t:ℂ)^2/2 = -((t:ℂ)^2/2) by ring]
    field_simp
  rw [Real.gammaDiDonatoF, ofReal_mul, ofReal_mul, ← integral_complex_ofReal, ofReal_cpow hx.le, key]
  push_cast
  ring

/-- The explicit O(x^-7) approximation theorem in DLMF §8.27(i). -/
theorem Real.gammaDiDonato_approximation (p : ℝ) :
    IsBigO atTop (fun x : ℝ => Real.gammaDiDonatoF p x-4*x/Real.gammaDiDonatoH p x) (fun x => x^(-7 : ℤ)) := by
  sorry

end AAR.Confluent
