/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Regularized
public import AAR.Hypergeometric.ConnectionFormulas

/-!
# Parameter derivatives of the regularized Kummer series

Termwise parameter differentiation and the logarithmic series at integer second parameters.
The domination argument adapts `hasSum_deriv_regularizedGaussHGFun_comp` from
`AAR.Hypergeometric.ConnectionFormulas`, using the entire confluent majorant.
-/

@[expose] public section

open Complex Filter Set FormalMultilinearSeries AAR.Hypergeometric
open scoped Real Nat Topology ENNReal

noncomputable section
set_option autoImplicit false

namespace AAR.Confluent

/-- Termwise differentiation of the regularized Kummer series along entire parameter curves. -/
theorem hasSum_deriv_regularizedConfluent_comp {A B : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (z : ℂ) (w₀ : ℂ) :
    HasSum (fun n : ℕ => deriv (fun w => poch (A w) n * z ^ n / n.factorial *
        (Gamma (B w + n))⁻¹) w₀)
      (deriv (fun w => regularizedHGFun {A w} {B w} z) w₀) := by
  set T : ℕ → ℂ → ℂ := fun n w => poch (A w) n * z ^ n / n.factorial *
    (Gamma (B w + n))⁻¹ with hT
  have hTd : ∀ n, Differentiable ℂ (T n) := by
    intro n
    have h1 : Differentiable ℂ fun w => (ascPochhammer ℂ n).eval (A w) :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hA
    exact ((h1.mul_const _).div_const _).mul
      (differentiable_one_div_Gamma.comp (hB.add_const _))
  have hfun : (fun w => regularizedHGFun {A w} {B w} z) = fun w => ∑' n, T n w := by
    funext w; rw [regularizedConfluent_eq_tsum]
  rw [hfun]
  -- domination near `w₀`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 - (B w₀).re ≤ N := exists_nat_ge _
  have hre0 : 2 ≤ (B w₀ + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  obtain ⟨V, hVopen, hc₀V, hV⟩ := exists_open_norm_Gamma_add_nat_gt hre0
  have hevA : ∀ᶠ w in 𝓝 w₀, ‖A w‖ < ‖A w₀‖ + 1 :=
    hA.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  have hevC : ∀ᶠ w in 𝓝 w₀, (B w₀).re - 1 < (B w).re :=
    (Complex.continuous_re.comp hB.continuous).continuousAt.eventually
      (lt_mem_nhds (by show (B w₀).re - 1 < (B w₀).re; linarith))
  have hevV : ∀ᶠ w in 𝓝 w₀, B w ∈ V := hB.continuous.continuousAt (hVopen.mem_nhds hc₀V)
  have hevF : ∀ᶠ w in 𝓝 w₀, ∀ n ∈ Finset.range N, ‖T n w‖ < ‖T n w₀‖ + 1 := by
    rw [Finset.eventually_all]
    intro n _
    exact (hTd n).continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨U, hU, hUopen, hw₀U⟩ :=
    eventually_nhds_iff.mp (hevA.and (hevC.and (hevV.and hevF)))
  set p := regularizedHGFunSeries {((‖A w₀‖ + 1 : ℝ) : ℂ)} {1 - (N : ℂ)} with hp
  have hz' : (‖z‖₊ : ENNReal) < p.radius := by
    rw [hp, radius_regularizedConfluentSeries]
    exact ENNReal.coe_lt_top
  have hm : 0 < ‖Gamma (B w₀ + N)‖ / 2 := by
    have hpole : ∀ k : ℕ, B w₀ + N ≠ -k := fun k h => by
      have := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have := norm_pos_iff.mpr (Gamma_ne_zero hpole)
    positivity
  set u : ℕ → ℝ := fun n => if n < N then ‖T n w₀‖ + 1 else
    (‖Gamma (B w₀ + N)‖ / 2)⁻¹ * (‖p n‖ * (‖z‖₊ : ℝ) ^ n) with hu
  have hus : Summable u := by
    refine (summable_nat_add_iff N).mp ?_
    have := ((p.summable_norm_mul_pow hz').mul_left ((‖Gamma (B w₀ + N)‖ / 2)⁻¹))
    refine ((summable_nat_add_iff N).mpr this).congr fun n => ?_
    simp only [hu, show ¬ n + N < N by omega, ite_false]
  refine hasSum_deriv_of_summable_norm hus (fun n => (hTd n).differentiableOn) hUopen
    (fun n w hw => ?_) hw₀U
  obtain ⟨hAw, hCw, hVw, hFw⟩ := hU w hw
  by_cases hn : n < N
  · simp only [hu, hn, ite_true]
    exact (hFw n (Finset.mem_range.mpr hn)).le
  · simp only [hu, hn, ite_false]
    have hre : 1 ≤ (B w + N).re := by
      simp only [Complex.add_re, Complex.natCast_re] at hre0 ⊢
      linarith
    simpa only [coe_nnnorm] using
      norm_confluent_term_le_majorant hAw.le hre hm (hV _ hVw).le (not_lt.mp hn)

/-- Derivative of the regularized connection numerator at a positive integer parameter.
The finite sum is the singular part; the infinite sum supplies the logarithmic part. -/
theorem tricomi_numerator_nat_series (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    Summable (fun k : ℕ =>
      (poch a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
        (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k))) ∧
    deriv (fun c : ℂ =>
      regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
        z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹)
      ((n : ℂ) + 1) =
      (Gamma (a - n))⁻¹ * ∑' k : ℕ,
        (poch a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
          (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) +
      z ^ (-(n : ℂ)) * (Gamma a)⁻¹ * ∑ j ∈ Finset.range n,
        poch (a - n) j * z ^ j / j.factorial *
          ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) := by
  set c₀ : ℂ := n + 1 with hc₀
  set β : ℂ := a - n with hβ
  set Q : ℂ → ℂ := fun c => regularizedHGFun {a} {c} z with hQ
  set S : ℂ → ℂ := fun c => regularizedHGFun {a - c + 1} {2 - c} z with hS
  set q : ℕ → ℂ := fun k => poch a k * z ^ k / k.factorial *
    (Gamma ((n : ℂ) + 1 + k))⁻¹ with hq
  set P : ℂ := poch β n with hP
  have hβnp : ∀ k : ℕ, β ≠ -(k : ℂ) := ha
  have hanp : ∀ k : ℕ, a ≠ -(k : ℂ) := by
    simpa [hβ] using not_neg_nat_add_nat hβnp n
  have eβ : a - c₀ + 1 = β := by rw [hc₀, hβ]; ring
  have eC : 2 - c₀ = 1 - (n : ℂ) := by rw [hc₀]; ring
  have hQd : Differentiable ℂ Q :=
    differentiable_regularizedConfluent_comp (differentiable_const _) differentiable_id z
  have hSd : Differentiable ℂ S :=
    differentiable_regularizedConfluent_comp (by fun_prop) (by fun_prop) z
  have hQ0 : HasSum q (Q c₀) := by
    simpa [hq, hQ, hc₀, regularizedConfluent_eq_tsum] using
      (summable_regularizedConfluent_term a ((n : ℂ) + 1) z).hasSum
  have hQsum := hasSum_deriv_regularizedConfluent_comp (A := fun _ => a)
    (B := fun c => c) (differentiable_const _) differentiable_id z c₀
  have hSsum := hasSum_deriv_regularizedConfluent_comp (A := fun c => a - c + 1)
    (B := fun c => 2 - c) (by fun_prop) (by fun_prop) z c₀
  have hmn : ∀ k : ℕ, ∀ j : ℕ, (n : ℂ) + 1 + k ≠ -(j : ℂ) := by
    intro k j hj
    have := congrArg re hj
    simp at this
    linarith [Nat.cast_nonneg n (α := ℝ), Nat.cast_nonneg k (α := ℝ),
      Nat.cast_nonneg j (α := ℝ)]
  have hqd : ∀ k : ℕ, deriv (fun c : ℂ => poch a k * z ^ k / k.factorial *
      (Gamma (c + k))⁻¹) c₀ = -q k * digamma ((n : ℂ) + 1 + k) := by
    intro k
    have hg := ((hasDerivAt_inv_Gamma (hmn k)).comp c₀ ((hasDerivAt_id c₀).add_const (k : ℂ))).const_mul
      (poch a k * z ^ k / k.factorial)
    change HasDerivAt (fun c : ℂ => poch a k * z ^ k / k.factorial *
      (Gamma (c + k))⁻¹) _ c₀ at hg
    rw [hg.deriv]
    simp only [hq]
    ring
  set dt : ℕ → ℂ := fun j => deriv (fun c : ℂ => poch (a - c + 1) j * z ^ j / j.factorial *
    (Gamma (2 - c + j))⁻¹) c₀ with hdt
  have htd : ∀ j : ℕ, dt j = z ^ j / j.factorial *
      (-(poch β j * (digamma (β + j) - digamma β)) * (Gamma (1 - (n : ℂ) + j))⁻¹ -
        poch β j * deriv (fun y : ℂ => (Gamma y)⁻¹) (1 - (n : ℂ) + j)) := by
    intro j
    have hp : HasDerivAt (fun y => poch y j)
        (poch β j * (digamma (β + j) - digamma β)) (a - c₀ + 1) := by
      rw [eβ]; exact hasDerivAt_poch hβnp j
    have hl1 : HasDerivAt (fun c : ℂ => a - c + 1) (-1) c₀ := by
      simpa using ((hasDerivAt_id c₀).const_sub a).add_const (1 : ℂ)
    have hl2 : HasDerivAt (fun c : ℂ => 2 - c + j) (-1) c₀ := by
      simpa using ((hasDerivAt_id c₀).const_sub (2 : ℂ)).add_const (j : ℂ)
    have hg := (hasDerivAt_inv_Gamma_any (2 - c₀ + j)).comp c₀ hl2
    have h := (((hp.comp c₀ hl1).mul_const (z ^ j)).div_const (j.factorial : ℂ)).mul hg
    change HasDerivAt (fun c : ℂ => poch (a - c + 1) j * z ^ j / j.factorial *
      (Gamma (2 - c + j))⁻¹) _ c₀ at h
    change deriv (fun c : ℂ => poch (a - c + 1) j * z ^ j / j.factorial *
      (Gamma (2 - c + j))⁻¹) c₀ = _
    rw [h.deriv]
    simp only [Function.comp_apply, eβ, eC]
    ring
  have hGk : ∀ k : ℕ, Gamma ((n : ℂ) + 1 + k) = ((k + n).factorial : ℂ) := by
    intro k
    rw [show (n : ℂ) + 1 + k = ((k + n : ℕ) : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial]
  have hG1k : ∀ k : ℕ, Gamma (1 - (n : ℂ) + ((k + n : ℕ) : ℂ)) = (k.factorial : ℂ) := by
    intro k
    rw [show 1 - (n : ℂ) + ((k + n : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial]
  set s : ℕ → ℂ := fun j => poch β j * z ^ j / j.factorial *
    (Gamma (1 - (n : ℂ) + j))⁻¹ with hs
  have hS0 : HasSum s (S c₀) := by
    simpa [hs, hS, eβ, eC, regularizedConfluent_eq_tsum] using
      (summable_regularizedConfluent_term β (1 - (n : ℂ)) z).hasSum
  have hs_shift : ∀ k : ℕ, s (k + n) = P * z ^ n * q k := by
    intro k
    simp only [hs, hq, hP, hGk, hG1k]
    rw [add_comm k n, poch_add β n k, show β + (n : ℂ) = a by rw [hβ]; ring,
      pow_add, add_comm n k]
    have hk : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hkn : ((k + n).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
  have hpole : ∀ j : ℕ, j < n → 1 - (n : ℂ) + j = -((n - 1 - j : ℕ) : ℂ) := by
    intro j hj
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hS0eq : S c₀ = P * z ^ n * Q c₀ := by
    have h := (hasSum_nat_add_iff' n).mpr hS0
    have hlow : ∑ j ∈ Finset.range n, s j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      simp only [hs, hpole j (Finset.mem_range.mp hj), Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
    rw [hlow, sub_zero] at h
    exact h.unique ((hQ0.mul_left (P * z ^ n)).congr_fun fun k => (hs_shift k).symm ▸ rfl)
  have hdt_shift : ∀ k : ℕ, dt (k + n) = P * z ^ n * q k *
      (-digamma (a + k) + digamma β + digamma (k + 1)) := by
    intro k
    have hk1 : ∀ j : ℕ, (k : ℂ) + 1 ≠ -(j : ℂ) := by
      intro j hj
      have := congrArg re hj
      simp at this
      linarith [Nat.cast_nonneg k (α := ℝ), Nat.cast_nonneg j (α := ℝ)]
    rw [htd, show 1 - (n : ℂ) + ((k + n : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring,
      deriv_inv_Gamma_eq hk1, ← hs_shift k]
    simp only [hs, show 1 - (n : ℂ) + ((k + n : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring,
      show β + ((k + n : ℕ) : ℂ) = a + k by rw [hβ]; push_cast; ring]
    ring
  have hdt_low : ∀ j ∈ Finset.range n, dt j =
      -(poch β j * z ^ j / j.factorial *
        ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ))) := by
    intro j hj
    rw [htd, hpole j (Finset.mem_range.mp hj), deriv_inv_Gamma_neg_nat,
      Gamma_neg_nat_eq_zero, inv_zero]
    ring
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero hanp
  have hGβ : Gamma β ≠ 0 := Gamma_ne_zero hβnp
  have hGam : Gamma a = P * Gamma β := by
    have h := Gamma_add_nat_div_Gamma_eq (n := n) β hβnp
    rw [div_eq_iff hGβ, show β + (n : ℂ) = a by rw [hβ]; ring] at h
    exact h
  have hP0 : P ≠ 0 := poch_ne_zero_of_not_neg_nat hβnp n
  have hJP : (Gamma a)⁻¹ * P = (Gamma β)⁻¹ := by rw [hGam]; field_simp [hP0]
  have hZ : z ^ (-(n : ℂ)) * z ^ n = 1 := by
    rw [cpow_neg, cpow_natCast]; exact inv_mul_cancel₀ (pow_ne_zero _ hz)
  have hG : HasDerivAt (fun c : ℂ => (Gamma (a - c + 1))⁻¹)
      (digamma β * (Gamma β)⁻¹) c₀ := by
    have hg : HasDerivAt (fun y : ℂ => (Gamma y)⁻¹) (-digamma β * (Gamma β)⁻¹)
        (a - c₀ + 1) := by rw [eβ]; exact hasDerivAt_inv_Gamma hβnp
    have hh := hg.comp c₀ (((hasDerivAt_id c₀).const_sub a).add_const (1 : ℂ))
    change HasDerivAt (fun c : ℂ => (Gamma (a - c + 1))⁻¹) _ c₀ at hh
    convert hh using 1; ring
  have hpow : HasDerivAt (fun c : ℂ => z ^ (1 - c))
      (-(z ^ (-(n : ℂ)) * log z)) c₀ := by
    have h := ((hasDerivAt_id c₀).const_sub (1 : ℂ)).const_cpow (c := z) (Or.inl hz)
    simpa only [_root_.id, hc₀, show 1 - ((n : ℂ) + 1) = -(n : ℂ) by ring,
      neg_mul, mul_neg, mul_one] using h
  have hR := ((hQd c₀).hasDerivAt.mul hG).sub
    ((hpow.mul (hSd c₀).hasDerivAt).mul_const (Gamma a)⁻¹)
  have hRderiv := hR.deriv
  change deriv (fun c : ℂ => regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
      z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹) c₀ = _ at hRderiv
  simp only [eβ, show 1 - c₀ = -(n : ℂ) by rw [hc₀]; ring] at hRderiv
  rw [hS0eq] at hRderiv
  have hRsimple : deriv (fun c : ℂ => regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
      z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹) c₀ =
      (Gamma β)⁻¹ * (deriv Q c₀ + (digamma β + log z) * Q c₀) -
        z ^ (-(n : ℂ)) * (Gamma a)⁻¹ * deriv S c₀ := by
    rw [hRderiv]
    linear_combination (log z * Q c₀ * (Gamma a)⁻¹ * P) * hZ +
      log z * Q c₀ * hJP
  have hTail : HasSum (fun k => q k *
      (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)))
      (deriv Q c₀ + (digamma β + log z) * Q c₀ -
        z ^ (-(n : ℂ)) / P * (deriv S c₀ - ∑ j ∈ Finset.range n, dt j)) := by
    have h := (hQsum.add (hQ0.mul_left (digamma β + log z))).sub
      (((hasSum_nat_add_iff' n).mpr hSsum).mul_left (z ^ (-(n : ℂ)) / P))
    convert h using 1
    funext k
    rw [hqd, hdt_shift]
    have hP0 : P ≠ 0 := poch_ne_zero_of_not_neg_nat hβnp n
    field_simp
    linear_combination -(q k * (digamma (a + k) - digamma β - digamma (k + 1))) * hZ
  refine ⟨hTail.summable, ?_⟩
  change _ = (Gamma β)⁻¹ * (∑' k : ℕ, q k *
      (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k))) + _
  rw [hTail.tsum_eq]
  have hFin : ∑ j ∈ Finset.range n, dt j = -(∑ j ∈ Finset.range n,
      poch β j * z ^ j / j.factorial *
        ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ))) := by
    simp_rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl hdt_low
  rw [hFin, hRsimple]
  have hK : (Gamma β)⁻¹ / P = (Gamma a)⁻¹ := by rw [← hJP]; field_simp
  linear_combination (z ^ (-(n : ℂ)) * (deriv S c₀ + ∑ j ∈ Finset.range n,
    poch β j * z ^ j / j.factorial *
      ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)))) * hK

/-- Derivative of the regularized connection numerator at a positive integer parameter.
The finite sum is the singular part; the infinite sum supplies the logarithmic part. -/
theorem deriv_tricomi_numerator_nat (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    deriv (fun c : ℂ =>
      regularizedHGFun {a} {c} z * (Gamma (a - c + 1))⁻¹ -
        z ^ (1 - c) * regularizedHGFun {a - c + 1} {2 - c} z * (Gamma a)⁻¹)
      ((n : ℂ) + 1) =
      (Gamma (a - n))⁻¹ * ∑' k : ℕ,
        (poch a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
          (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k)) +
      z ^ (-(n : ℂ)) * (Gamma a)⁻¹ * ∑ j ∈ Finset.range n,
        poch (a - n) j * z ^ j / j.factorial *
          ((-1 : ℂ) ^ (n - 1 - j) * ((n - 1 - j).factorial : ℂ)) :=
  (tricomi_numerator_nat_series a n hz ha).2

end AAR.Confluent
