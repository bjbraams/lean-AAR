/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.SpecialValues
public import AAR.ExpIntegrals.Basic

/-!
# Series, recurrences and derivatives, DLMF §§8.7–8.8

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

/-- scIncGamma hasSum alternating. -/
@[dlmf 8.7.E1]
theorem scIncGamma_hasSum_alternating {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    HasSum (fun k : ℕ => (-z)^k/(Gamma a*(k.factorial : ℂ)*(a+k))) (scIncGamma a z) := by
  have hs := (hasFPowerSeriesOnBall_regularizedConfluent a (a+1)).hasSum_mul_pow
    (by simp : -z ∈ Metric.eball (0:ℂ) ⊤)
  have he : regularizedHGFun {a} {a+1} (-z)=scIncGamma a z := by
    simpa [add_comm] using (scIncGamma_regularized_pair a z).2.symm
  rw [he] at hs
  refine hs.congr_fun fun k => ?_
  have hk : a+(k:ℂ) ≠ 0 := by intro h; exact ha k (by linear_combination h)
  have hG : Gamma (a+k) ≠ 0 := Gamma_ne_zero (fun n h => ha (k+n) (by push_cast; linear_combination h))
  rw [regularizedHGFunCoeff_singleton, poch, ← Gamma_add_nat_div_Gamma_eq a ha,
    show a+1+k=(a+k)+1 by ring, Gamma_add_one _ hk]
  field_simp [Gamma_ne_zero ha, hG]

/-- incompleteGamma increment series. -/
@[dlmf 8.7.E2]
theorem incompleteGamma_increment_series {a x y : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hx : x ∈ slitPlane) (hxy : x+y ∈ slitPlane) (hy : ‖y‖ < ‖x‖) :
    HasSum (fun n : ℕ => exp (-x)*x^(a-1)*poch (1-a) n/(-x)^n*(1-exp (-y)*expPartialSum n y)) (lowerIncGamma a (x+y)-lowerIncGamma a x) ∧ lowerIncGamma a (x+y)-lowerIncGamma a x=upperIncGamma a x-upperIncGamma a (x+y) := by
  sorry

/-- upperIncGamma hasSum alternating. -/
@[dlmf 8.7.E3]
theorem upperIncGamma_hasSum_alternating {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (-1 : ℂ)^k*z^(a+k)/((k.factorial : ℂ)*(a+k))) (Gamma a-upperIncGamma a z) := by
  have hs := (scIncGamma_hasSum_alternating ha z).mul_left (Gamma a*z^a)
  have he : Gamma a*z^a*scIncGamma a z=Gamma a-upperIncGamma a z := by
    rw [scIncGamma_eq ha hz]
    have hp : z^a*z^(-a)=1 := by rw [← cpow_add _ _ hz]; simp
    have hc := lowerIncGamma_add_upperIncGamma ha hz
    calc
      Gamma a*z^a*(z^(-a)*lowerIncGamma a z/Gamma a) =
          (z^a*z^(-a))*lowerIncGamma a z := by field_simp [Gamma_ne_zero ha]
      _ = lowerIncGamma a z := by rw [hp, one_mul]
      _ = Gamma a-upperIncGamma a z := by linear_combination hc
  rw [he] at hs
  refine hs.congr_fun fun k => ?_
  rw [neg_pow, show a+(k:ℂ)=a+(k:ℂ) by rfl, cpow_add _ _ hz, cpow_natCast]
  field_simp [Gamma_ne_zero ha]
  ring

/-- upperIncGamma hasSum exponential. -/
@[dlmf 8.7.E3]
theorem upperIncGamma_hasSum_exponential {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => Gamma a*z^a*exp (-z)*z^k/Gamma (a+k+1)) (Gamma a-upperIncGamma a z) := by
  have hs := (scIncGamma_hasSum_exponential a z).mul_left (Gamma a*z^a)
  have he : Gamma a*z^a*scIncGamma a z=Gamma a-upperIncGamma a z := by
    rw [scIncGamma_eq ha hz]
    have hp : z^a*z^(-a)=1 := by rw [← cpow_add _ _ hz]; simp
    have hc := lowerIncGamma_add_upperIncGamma ha hz
    calc
      Gamma a*z^a*(z^(-a)*lowerIncGamma a z/Gamma a) =
          (z^a*z^(-a))*lowerIncGamma a z := by field_simp [Gamma_ne_zero ha]
      _ = lowerIncGamma a z := by rw [hp, one_mul]
      _ = Gamma a-upperIncGamma a z := by linear_combination hc
  rw [he] at hs
  exact hs.congr_fun fun k => by ring

/-- lowerIncGamma besselI series. -/
@[dlmf 8.7.E4]
theorem lowerIncGamma_besselI_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => Gamma a*(x : ℂ)^(a/2)*exp (-x : ℂ)*expPartialSum n (-1)*(x : ℂ)^((n : ℂ)/2)*AAR.Bessel.besselI (n+a) (2*Real.sqrt x)) (lowerIncGamma a x) := by
  sorry

/-- scIncGamma sphericalI series. -/
@[dlmf 8.7.E5]
theorem scIncGamma_sphericalI_series (a z : ℂ) :
    HasSum (fun n : ℕ => exp (-z/2)*poch (1-a) n/Gamma (n+a+1)*(2*n+1)*sphericalI n (z/2)) (scIncGamma a z) := by
  sorry

/-- upperIncGamma laguerre series. -/
@[dlmf 8.7.E6]
theorem upperIncGamma_laguerre_series {a : ℂ} (ha : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (x : ℂ)^a*exp (-x : ℂ)*AAR.OrthogonalPolynomials.laguerrePolyL a n x/(n+1)) (upperIncGamma a x) := by
  sorry

/-- incompleteGamma threeTerm. -/
@[dlmf 8.8.E3]
theorem incompleteGamma_threeTerm {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    ∀ f ∈ ({lowerIncGamma,upperIncGamma} : Set (ℂ → ℂ → ℂ)), f (a+2) z-(a+1+z)*f (a+1) z+a*z*f a z=0 := by
  intro f hf
  rcases hf with rfl | rfl
  · have h0 := lowerIncGamma_add_one ha hz
    have h1 := lowerIncGamma_add_one (add_one_ne_neg_nat ha) hz
    rw [show a+1+1=a+2 by ring, cpow_add _ _ hz, cpow_one] at h1
    linear_combination h1 - z*h0
  · have h0 := upperIncGamma_add_one a hz
    have h1 := upperIncGamma_add_one (a+1) hz
    rw [show a+1+1=a+2 by ring, cpow_add _ _ hz, cpow_one] at h1
    linear_combination h1 - z*h0

/-- lowerIncGamma shift up. -/
@[dlmf 8.8.E7]
theorem lowerIncGamma_shift_up (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma (a+n) z=poch a n*lowerIncGamma a z - z^a*exp (-z)*(∑ k ∈ Finset.range n, Gamma (a+n)/Gamma (a+k+1)*z^k) := by
  have han := not_neg_nat_add_nat ha n
  have hGa := Gamma_ne_zero ha
  have hGan := Gamma_ne_zero han
  have hs := normIncGammaPContinued_shift_up n a hz
  rw [normIncGammaPContinued_eq han, normIncGammaPContinued_eq ha,
    normIncGammaP, normIncGammaP] at hs
  have hg := Gamma_add_nat_div_Gamma_eq (n := n) a ha
  rw [← poch] at hg
  rw [← hg]
  have hsum : ∑ k ∈ Finset.range n, Gamma (a+n)/Gamma (a+k+1)*z^k =
      Gamma (a+n)*∑ k ∈ Finset.range n, z^k/Gamma (a+k+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum]
  calc
    lowerIncGamma (a+n) z = Gamma (a+n)*(lowerIncGamma a z/Gamma a-
        z^a*exp (-z)*∑ k ∈ Finset.range n, z^k/Gamma (a+k+1)) := by
      rw [← hs]
      field_simp
    _ = _ := by ring

/-- Reversing the finite upward-shift correction gives the downward-shift indexing. -/
theorem incompleteGamma_shift_sum_reverse (n : ℕ) (a : ℂ) {z : ℂ} (hz : z≠0) :
    z^(a-n)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-n+k+1)*z^k)=
      z^(a-1)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-k)*z^(-(k:ℤ))) := by
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_range_reflect (fun k => z^(a-n)*(Gamma a/Gamma (a-n+k+1)*z^k)) n]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k<n := Finset.mem_range.mp hk
  have hcast : ((n-1-k:ℕ):ℂ)=(n:ℂ)-1-k := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  rw [show a-n+(n-1-k:ℕ)+1=a-k by rw [hcast]; ring]
  have he : z^(a-n)*z^(n-1-k)=z^(a-1)*z^(-(k:ℤ)) := by
    rw [← cpow_natCast, ← cpow_intCast, ← cpow_add _ _ hz, ← cpow_add _ _ hz, hcast]
    congr 1
    push_cast
    ring
  linear_combination (Gamma a/Gamma (a-k))*he

/-- lowerIncGamma shift down. -/
@[dlmf 8.8.E8]
theorem lowerIncGamma_shift_down (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z=Gamma a/Gamma (a-n)*lowerIncGamma (a-n) z - z^(a-1)*exp (-z)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-k)*z^(-(k : ℤ))) := by
  have hs := lowerIncGamma_shift_up n ha hz
  have hg := Gamma_add_nat_div_Gamma_eq (n:=n) (a-n) ha
  rw [show a-(n:ℂ)+n=a by ring] at hs hg
  rw [← poch] at hg
  rw [← hg] at hs
  have he := incompleteGamma_shift_sum_reverse n a hz
  linear_combination hs-exp (-z)*he

/-- upperIncGamma shift up. -/
@[dlmf 8.8.E9]
theorem upperIncGamma_shift_up (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma (a+n) z=poch a n*upperIncGamma a z + z^a*exp (-z)*(∑ k ∈ Finset.range n, Gamma (a+n)/Gamma (a+k+1)*z^k) := by
  have h0 := lowerIncGamma_add_upperIncGamma ha hz
  have hn := lowerIncGamma_add_upperIncGamma (not_neg_nat_add_nat ha n) hz
  have hs := lowerIncGamma_shift_up n ha hz
  have hg := Gamma_add_nat_div_Gamma_eq (n := n) a ha
  rw [← poch, div_eq_iff (Gamma_ne_zero ha)] at hg
  linear_combination hn-hs-poch a n*h0+hg

/-- upperIncGamma shift down. -/
@[dlmf 8.8.E10]
theorem upperIncGamma_shift_down (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma a z=Gamma a/Gamma (a-n)*upperIncGamma (a-n) z + z^(a-1)*exp (-z)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-k)*z^(-(k : ℤ))) := by
  have hs := upperIncGamma_shift_up n ha hz
  have hg := Gamma_add_nat_div_Gamma_eq (n:=n) (a-n) ha
  rw [show a-(n:ℂ)+n=a by ring] at hs hg
  rw [← poch] at hg
  rw [← hg] at hs
  have he := incompleteGamma_shift_sum_reverse n a hz
  linear_combination hs+exp (-z)*he

/-- scIncGamma deriv parameter zero. -/
@[dlmf 8.8.E14]
theorem scIncGamma_deriv_parameter_zero {z : ℂ} (hz : z ≠ 0) :
    deriv (fun a => scIncGamma a z) 0 = -genExpIntE 1 z-log z := by
  have he : (fun a : ℂ => scIncGamma a z)=
      (fun a => regularizedHGFun {a} {a+1} (-z)) := by
    funext a
    rw [regularizedConfluent_kummer_transform a (a+1) (-z)]
    simp only [show a+1-a=1 by ring, neg_neg, scIncGamma]
  rw [he, (hasDerivAt_regularizedConfluent_Ein z).deriv, expIntE1_eq_Ein_complex hz]
  ring

/-- lowerIncGamma iteratedDeriv scaled power. -/
@[dlmf 8.8.E15]
theorem lowerIncGamma_iteratedDeriv_scaled_power (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t^(-a)*lowerIncGamma a t) z=(-1 : ℂ)^n*z^(-a-n)*lowerIncGamma (a+n) z := by
  have hz0 := slitPlane_ne_zero hz
  have ha0 : a≠0 := by simpa using ha 0
  have ha1 := add_one_ne_neg_nat ha
  have han0 : a+(n:ℂ)≠0 := by intro h; exact ha n (by linear_combination h)
  have he : (fun t => t^(-a)*lowerIncGamma a t)=ᶠ[𝓝 z]
      (fun t => (1/a)*kummerM a (a+1) (-t)) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
    rw [lowerIncGamma]
    have hp : t^(-a)*t^a=1 := by rw [← cpow_add _ _ (slitPlane_ne_zero ht)]; simp
    linear_combination kummerM a (a+1) (-t)/a*hp
  rw [he.iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
    iteratedDeriv_comp_neg, iteratedDeriv_kummerM n ha1, lowerIncGamma]
  simp only [smul_eq_mul]
  rw [show a+1+(n:ℂ)=a+n+1 by ring]
  have hp : z^(-a-n)*z^(a+n)=1 := by rw [← cpow_add _ _ hz0]; ring_nf; simp
  have hpoch : a*poch (a+1) n=(a+n)*poch a n := by
    rw [← poch_succ_left, poch_succ]
    ring
  have hpc := poch_ne_zero_of_not_neg_nat ha1 n
  rw [show (-1:ℂ)^n*z^(-a-n)*(z^(a+n)/(a+n)*kummerM (a+n) (a+n+1) (-z))=
      (-1:ℂ)^n/(a+n)*kummerM (a+n) (a+n+1) (-z) by
    linear_combination (-1:ℂ)^n/(a+n)*kummerM (a+n) (a+n+1) (-z)*hp]
  field_simp [ha0,han0,hpc]
  linear_combination -kummerM (a+n) (a+n+1) (-z)*hpoch

/-- upperIncGamma iteratedDeriv scaled power. -/
@[dlmf 8.8.E16]
theorem upperIncGamma_iteratedDeriv_scaled_power (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t^(-a)*upperIncGamma a t) z=(-1 : ℂ)^n*z^(-a-n)*upperIncGamma (a+n) z := by
  have he : (fun t => t^(-a)*upperIncGamma a t)=ᶠ[𝓝 z]
      (fun t => exp (-t)*kummerU 1 (1+a) t) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
    have ht0 := slitPlane_ne_zero ht
    rw [upperIncGamma_eq_cpow_mul_kummerU _ ht0, add_comm a 1]
    have hp : t^(-a)*t^a=1 := by rw [← cpow_add _ _ ht0]; simp
    linear_combination exp (-t)*kummerU 1 (1+a) t*hp
  rw [he.iteratedDeriv_eq n, iteratedDeriv_exp_neg_kummerU _ _ _ hz,
    upperIncGamma_eq_cpow_mul_kummerU _ (slitPlane_ne_zero hz)]
  have hp : z^(-a-n)*z^(a+n)=1 := by rw [← cpow_add _ _ (slitPlane_ne_zero hz)]; ring_nf; simp
  rw [show a+(n:ℂ)+1=1+a+n by ring]
  linear_combination -(-1:ℂ)^n*exp (-z)*kummerU 1 (1+a+n) z*hp

/-- Exponentially weighted upper-Gamma differentiation holds at every parameter. -/
theorem hasDerivAt_exp_mul_upperIncGamma (a : ℂ) {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (fun t => exp t*upperIncGamma a t)
      ((a-1)*exp z*upperIncGamma (a-1) z) z := by
  have hd := (Complex.hasDerivAt_exp z).mul (hasDerivAt_upperIncGamma_complex a hz)
  refine hd.congr_deriv ?_
  have hr := upperIncGamma_add_one (a-1) (slitPlane_ne_zero hz)
  rw [sub_add_cancel] at hr
  have he : exp z*exp (-z)=1 := by rw [← Complex.exp_add]; simp
  linear_combination exp z*hr

/-- Exponentially weighted lower-Gamma differentiation away from the shifted poles. -/
theorem hasDerivAt_exp_mul_lowerIncGamma (a : ℂ)
    (ha : ∀ k : ℕ, a-1≠-k) {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (fun t => exp t*lowerIncGamma a t)
      ((a-1)*exp z*lowerIncGamma (a-1) z) z := by
  have ha0 : ∀ k : ℕ, a≠-k := by simpa using add_one_ne_neg_nat ha
  have hd := (Complex.hasDerivAt_exp z).mul (hasDerivAt_incompleteGamma ha0 hz).1
  refine hd.congr_deriv ?_
  have hr := lowerIncGamma_add_one ha (slitPlane_ne_zero hz)
  rw [sub_add_cancel] at hr
  have he : exp z*exp (-z)=1 := by rw [← Complex.exp_add]; simp
  linear_combination exp z*hr

/-- lowerIncGamma iteratedDeriv scaled exp. -/
@[dlmf 8.8.E17]
theorem lowerIncGamma_iteratedDeriv_scaled_exp (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => exp t*lowerIncGamma a t) z=(-1 : ℂ)^n*poch (1-a) n*exp z*lowerIncGamma (a-n) z := by
  induction n generalizing a with
  | zero => simp [poch_zero]
  | succ n ih =>
    have ha1 : ∀ k : ℕ, a-1≠-k := by
      intro k hk
      apply ha (k+n)
      push_cast
      linear_combination hk
    have has : ∀ k : ℕ, (a-1)-n≠-k := by
      intro k hk
      apply ha k
      push_cast
      linear_combination hk
    have he : deriv (fun t => exp t*lowerIncGamma a t)=ᶠ[𝓝 z]
        (fun t => (a-1)*(exp t*lowerIncGamma (a-1) t)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
      simpa only [mul_assoc] using (hasDerivAt_exp_mul_lowerIncGamma a ha1 ht).deriv
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih has,
      poch_succ_left, pow_succ]
    rw [show (1:ℂ)-(a-1)=1-a+1 by ring,
      show a-1-(n:ℂ)=a-(n+1:ℕ) by push_cast; ring]
    ring

/-- upperIncGamma iteratedDeriv scaled exp. -/
@[dlmf 8.8.E19]
theorem upperIncGamma_iteratedDeriv_scaled_exp (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => exp t*upperIncGamma a t) z=(-1 : ℂ)^n*poch (1-a) n*exp z*upperIncGamma (a-n) z := by
  induction n generalizing a with
  | zero => simp [poch_zero]
  | succ n ih =>
    have ha1 : ∀ k : ℕ, a-1≠-k := by
      intro k hk
      apply ha (k+n)
      push_cast
      linear_combination hk
    have has : ∀ k : ℕ, (a-1)-n≠-k := by
      intro k hk
      apply ha k
      push_cast
      linear_combination hk
    have he : deriv (fun t => exp t*upperIncGamma a t)=ᶠ[𝓝 z]
        (fun t => (a-1)*(exp t*upperIncGamma (a-1) t)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
      simpa only [mul_assoc] using (hasDerivAt_exp_mul_upperIncGamma a ht).deriv
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih has,
      poch_succ_left, pow_succ]
    rw [show (1:ℂ)-(a-1)=1-a+1 by ring,
      show a-1-(n:ℂ)=a-(n+1:ℕ) by push_cast; ring]
    ring

/-- A weighted regularized Kummer derivative, valid at every denominator parameter. -/
theorem hasDerivAt_cpow_mul_regularized_one (a : ℂ) {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (fun t => t^a*regularizedHGFun {1} {a+1} t)
      (z^(a-1)*regularizedHGFun {1} {a} z) z := by
  have hm := (differentiableAt_regularizedConfluent 1 (a+1) z).hasDerivAt
  rw [deriv_regularizedConfluent] at hm
  have hd := ((hasDerivAt_id z).cpow_const (c:=a) hz).mul hm
  refine (hd.congr_of_eventuallyEq (Eventually.of_forall fun t => rfl)).congr_deriv ?_
  have hc := regularizedConfluent_contiguous_mixed_b_pred 1 (a+1) z
  simp only [add_sub_cancel_right, show (1:ℂ)+1=2 by norm_num, one_mul] at hc
  have hp : z^a=z*z^(a-1) := by
    calc
      z^a=z^((1:ℂ)+(a-1)) := by congr 1; ring
      _ = _ := by rw [cpow_add _ _ (slitPlane_ne_zero hz), cpow_one]
  simp only [id_eq, mul_one, show (1:ℂ)+1=2 by norm_num]
  rw [hp]
  linear_combination z^(a-1)*hc

/-- Iterating the all-parameter weighted regularized derivative. -/
theorem iteratedDeriv_cpow_mul_regularized_one (n : ℕ) (a : ℂ) {z : ℂ} (hz : z∈slitPlane) :
    iteratedDeriv n (fun t => t^a*regularizedHGFun {1} {a+1} t) z=
      z^(a-n)*regularizedHGFun {1} {a-n+1} z := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
    have he : deriv (fun t => t^a*regularizedHGFun {1} {a+1} t)=ᶠ[𝓝 z]
        (fun t => t^(a-1)*regularizedHGFun {1} {a} t) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with t ht
      exact (hasDerivAt_cpow_mul_regularized_one a ht).deriv
    rw [iteratedDeriv_succ',he.iteratedDeriv_eq n]
    have hf : (fun t : ℂ => t^(a-1)*regularizedHGFun {1} {a} t)=
        (fun t : ℂ => t^(a-1)*regularizedHGFun {1} {(a-1)+1} t) := by simp
    rw [hf,ih (a-1)]
    congr 1 <;> push_cast <;> ring

/-- scIncGamma iteratedDeriv scaled. -/
@[dlmf 8.8.E18]
theorem scIncGamma_iteratedDeriv_scaled (n : ℕ) (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t^a*exp t*scIncGamma a t) z=z^(a-n)*exp z*scIncGamma (a-n) z := by
  have he (a t : ℂ) : t^a*exp t*scIncGamma a t=t^a*regularizedHGFun {1} {a+1} t := by
    rw [scIncGamma]
    have hE : exp t*exp (-t)=1 := by rw [← Complex.exp_add]; simp
    linear_combination t^a*regularizedHGFun {1} {a+1} t*hE
  simp_rw [he]
  exact iteratedDeriv_cpow_mul_regularized_one n a hz

/-- At parameter zero the logarithmic-plane upper Gamma function is `Ein(e^w)-w-γ`. -/
theorem upperIncGammaOnLog_zero (w : ℂ) :
    upperIncGammaOnLog 0 w=expIntEin (exp w)-w-Real.eulerMascheroniConstant := by
  have hz : exp w ≠ 0 := Complex.exp_ne_zero w
  have hd (u : ℂ) : HasDerivAt (fun v => -(expIntEin (exp v)-v)) (exp (0*u-exp u)) u := by
    have h := ((hasDerivAt_expIntEin_complex (Complex.exp_ne_zero u)).comp u
      (Complex.hasDerivAt_exp u)).sub (hasDerivAt_id u)
    refine h.neg.congr_deriv ?_
    have he : exp u ≠ 0 := Complex.exp_ne_zero u
    simp only [zero_mul, zero_sub]
    field_simp
    ring
  have hi := segmentIntegral_eq_sub (by fun_prop : Continuous (fun u : ℂ => exp (0*u-exp u)))
    hd (log (exp w)) w
  rw [upperIncGammaOnLog, hi, upperIncGamma_zero_E1 hz, expIntE1_eq_Ein_complex hz,
    Complex.exp_log hz]
  ring

/-- A full turn of the logarithmic variable does not change `exp`. -/
lemma exp_add_two_pi_int_mul_I (w : ℂ) (m : ℤ) : exp (w+2*π*m*I)=exp w := by
  rw [Complex.exp_add, show (2:ℂ)*π*m*I=m*(2*π*I) by ring, exp_int_mul_two_pi_mul_I, mul_one]

/-- At nonpositive integral parameters the logarithmic-plane upper Gamma function changes by an
additive constant under a full turn. -/
theorem upperIncGammaOnLog_neg_nat_monodromy (k : ℕ) (w : ℂ) (m : ℤ) :
    upperIncGammaOnLog (-k) (w+2*π*m*I)=upperIncGammaOnLog (-k) w-2*π*m*I*(-1 : ℂ)^k/k.factorial := by
  induction k with
  | zero =>
    simp only [CharP.cast_eq_zero, neg_zero, upperIncGammaOnLog_zero, exp_add_two_pi_int_mul_I,
      pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
    ring
  | succ k ih =>
    have hk : (-((k+1:ℕ):ℂ)) ≠ 0 := by push_cast; exact neg_ne_zero.mpr (by exact_mod_cast k.succ_ne_zero)
    have hr (v : ℂ) := upperIncGammaOnLog_add_one (-((k+1:ℕ):ℂ)) v
    rw [show -((k+1:ℕ):ℂ)+1=-(k:ℂ) by push_cast; ring] at hr
    have he : exp (-((k+1:ℕ):ℂ)*(w+2*π*m*I))=exp (-((k+1:ℕ):ℂ)*w) := by
      have := exp_add_two_pi_int_mul_I (-((k+1:ℕ):ℂ)*w) (-((k+1:ℕ):ℤ)*m)
      rw [← this]; congr 1; push_cast; ring
    have h1 := hr (w+2*π*m*I)
    have h0 := hr w
    rw [ih, exp_add_two_pi_int_mul_I, show -((k+1:ℕ):ℂ)*(w+2*π*m*I)-exp w
      =-((k+1:ℕ):ℂ)*(w+2*π*m*I)+(-exp w) by ring, Complex.exp_add, he] at h1
    rw [show -((k+1:ℕ):ℂ)*w-exp w=-((k+1:ℕ):ℂ)*w+(-exp w) by ring, Complex.exp_add] at h0
    have hf : ((k+1).factorial : ℂ)=(k+1)*k.factorial := by push_cast [Nat.factorial_succ]; ring
    rw [hf]
    have hk' : (k:ℂ)+1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have hkf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
    have hinv : ((k:ℂ)+1)⁻¹*((k:ℂ)+1)=1 := inv_mul_cancel₀ hk'
    push_cast at h1 h0 ⊢
    rw [pow_succ, div_eq_mul_inv, mul_inv]
    linear_combination ((k:ℂ)+1)⁻¹*(h1-h0)-(upperIncGammaOnLog (-(k+1)) (w+2*π*m*I)-upperIncGammaOnLog (-(k+1)) w)*hinv

/-- On the principal strip the logarithmic-plane upper Gamma function is the principal one. -/
theorem upperIncGammaOnLog_eq_upperIncGamma (a : ℂ) {w : ℂ} (h1 : -π < w.im) (h2 : w.im ≤ π) :
    upperIncGammaOnLog a w=upperIncGamma a (exp w) := by
  rw [upperIncGammaOnLog, Complex.log_exp h1 h2]
  simp [segmentIntegral]

/-- The logarithmic-plane upper Gamma function has derivative `-exp (a w - e^w)` at every
parameter. -/
theorem hasDerivAt_upperIncGammaOnLog (a w : ℂ) :
    HasDerivAt (upperIncGammaOnLog a) (-exp (a*w-exp w)) w := by
  by_cases ha : ∀ n : ℕ, a ≠ -n
  · have h := (hasDerivAt_lowerIncGammaOnLog ha w).const_sub (Gamma a)
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun v => upperIncGammaOnLog_eq_Gamma_sub ha v)
  push Not at ha
  obtain ⟨n, rfl⟩ := ha
  induction n generalizing w with
  | zero =>
    have h := (((hasDerivAt_expIntEin_complex (Complex.exp_ne_zero w)).comp w
      (Complex.hasDerivAt_exp w)).sub (hasDerivAt_id w)).sub_const (Real.eulerMascheroniConstant:ℂ)
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)).congr_deriv ?_
    · simp [upperIncGammaOnLog_zero]
    · have he : exp w ≠ 0 := Complex.exp_ne_zero w
      simp only [CharP.cast_eq_zero, neg_zero, zero_mul, zero_sub, id, Function.comp_apply]
      field_simp
      ring
  | succ n ih =>
    have hk : (-((n+1:ℕ):ℂ)) ≠ 0 := by
      push_cast; exact neg_ne_zero.mpr (by exact_mod_cast n.succ_ne_zero)
    set a : ℂ := -((n+1:ℕ):ℂ) with ha
    have hr (v : ℂ) : upperIncGammaOnLog a v = (upperIncGammaOnLog (-(n:ℂ)) v - exp (a*v-exp v))/a := by
      have := upperIncGammaOnLog_add_one a v
      rw [show a+1 = -(n:ℂ) by rw [ha]; push_cast; ring] at this
      rw [this]; field_simp; ring
    have he : HasDerivAt (fun v => exp (a*v-exp v)) (exp (a*w-exp w)*(a-exp w)) w := by
      have := (((hasDerivAt_id w).const_mul a).sub (Complex.hasDerivAt_exp w)).cexp
      simpa using this
    have h := ((ih w).sub he).div_const a
    refine (h.congr_of_eventuallyEq (Eventually.of_forall fun v => hr v)).congr_deriv ?_
    rw [show -(n:ℂ) = a+1 by rw [ha]; push_cast; ring,
      show (a+1)*w-exp w = (a*w-exp w)+w by ring, Complex.exp_add (a*w-exp w)]
    field_simp
    ring

end AAR.Confluent
