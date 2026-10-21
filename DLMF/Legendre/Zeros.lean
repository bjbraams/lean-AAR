/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Conical
public import DLMF.Legendre.SpecialValues

/-!
# Real Legendre zero counts and interlacing

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

attribute [local instance] Classical.propDecidable

/-- legendreIntegerPart. -/
@[dlmf 14.16.E1]
def legendreIntegerPart (μ : ℝ) : ℤ :=
  ⌊μ⌋

/-- legendreFractionalPart. -/
@[dlmf 14.16.E1]
def legendreFractionalPart (μ : ℝ) : ℝ :=
  μ-⌊μ⌋

/-- ferrersZeroSet. -/
def ferrersZeroSet (second : Bool) (ν μ : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Ioo (-1:ℝ) 1 ∧ (if second then ferrersQ ν μ x else ferrersP ν μ x)=0}

/-- Extra-zero cases in DLMF 14.16(ii), away from integer parameters. -/
def ferrersPExtraZero (ν μ : ℝ) : Bool :=
  decide (0 < μ ∧ ((⌊μ⌋ < ⌊ν⌋ ∧ legendreFractionalPart ν ≤ legendreFractionalPart μ) ∨ (⌊ν⌋ < ⌊μ⌋ ∧ Even (⌊μ⌋-⌊ν⌋))))

/-- Nonintegral parameter zero count from DLMF 14.16(ii). -/
theorem ferrersP_zero_count {ν μ : ℝ} (hν : -1/2 ≤ ν) (hνn : ∀ n : ℤ, ν ≠ n) (hμn : ∀ n : ℤ, μ ≠ n) (hnondeg : ∃ x ∈ Ioo (-1:ℝ) 1, ferrersP ν μ x ≠ 0) :
    Set.Finite (ferrersZeroSet false ν μ) ∧ (ferrersZeroSet false ν μ).ncard=(max (⌈ν-|μ|⌉:ℤ) 0).toNat+(if ferrersPExtraZero ν μ then 1 else 0) := by
  sorry

/-- The nonpositive-order case, including integral parameters. -/
theorem ferrersP_nonpositive_order_zero_count {ν μ : ℝ} (hν : -1/2 ≤ ν) (hμ : μ ≤ 0) :
    Set.Finite (ferrersZeroSet false ν μ) ∧ (ferrersZeroSet false ν μ).ncard=(max (⌈ν-|μ|⌉:ℤ) 0).toNat := by
  sorry

/-- Integer-degree case excludes the identically zero solution when integral order exceeds degree. -/
theorem ferrersP_nat_degree_zero_count (n : ℕ) (μ : ℝ) (hnondeg : ∃ x ∈ Ioo (-1:ℝ) 1, ferrersP n μ x ≠ 0) :
    Set.Finite (ferrersZeroSet false n μ) ∧ (ferrersZeroSet false n μ).ncard=(max (⌈(n:ℝ)-|μ|⌉:ℤ) 0).toNat := by
  sorry

/-- DLMF 14.16(ii): the n+1 zeros of Q_n. -/
theorem ferrersQ_nat_zero_count (n : ℕ) :
    Set.Finite (ferrersZeroSet true n 0) ∧ (ferrersZeroSet true n 0).ncard=n+1 := by
  sorry

/-- Separation of successive distinct zeros in both directions. -/
def InterlacesZeros (S T : Set ℝ) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a < b → (¬∃ c ∈ S, a < c ∧ c < b) → ∃! c : ℝ, c ∈ T ∧ a < c ∧ c < b) ∧ (∀ a ∈ T, ∀ b ∈ T, a < b → (¬∃ c ∈ T, a < c ∧ c < b) → ∃! c : ℝ, c ∈ S ∧ a < c ∧ c < b)

/-- The Wronskian must be nonzero; degenerate proportional solutions do not interlace. -/
theorem ferrersPQ_interlace {ν μ : ℝ} (hν : -1/2 ≤ ν) (hr : LegendreQRegular ν μ) (hind : Gamma (ν+μ+1)/Gamma (ν-μ+1) ≠ 0) :
    InterlacesZeros (ferrersZeroSet false ν μ) (ferrersZeroSet true ν μ) := by
  sorry

/-- Count range and parity in DLMF 14.16(ii), on the nondegenerate domain. -/
theorem ferrersQ_zero_count_range {ν μ : ℝ} (hν : -1/2 ≤ ν) (hr : LegendreQRegular ν μ) (hind : Gamma (ν+μ+1)/Gamma (ν-μ+1) ≠ 0) :
    Set.Finite (ferrersZeroSet true ν μ) ∧ ∃ k : ℤ, k ∈ Finset.Icc (-1) 2 ∧ ((ferrersZeroSet true ν μ).ncard:ℤ)=max (⌈ν-|μ|⌉:ℤ) 0+k ∧ (Real.cos (ν*π)*Real.cos (μ*π) < 0 → Even ((ferrersZeroSet true ν μ).ncard:ℤ)) ∧ (0 < Real.cos (ν*π)*Real.cos (μ*π) → Odd ((ferrersZeroSet true ν μ).ncard:ℤ)) := by
  sorry

/-- associatedPOneZero. -/
def associatedPOneZero (ν μ : ℝ) : Prop :=
  (0 < μ ∧ ν < μ ∧ (∀ n : ℤ, μ ≠ n) ∧ Real.sin ((μ-ν)*π)*Real.sin (μ*π) < 0) ∨ (μ ≤ ν ∧ (∀ n : ℤ, μ ≠ n) ∧ Odd (⌊μ⌋:ℤ))

/-- Exactly one or no exterior zeros, excluding an identically zero solution. -/
theorem associatedP_zero_count {ν μ : ℝ} (hν : -1/2 ≤ ν) (hnondeg : ∃ x : ℝ, 1 < x ∧ associatedP ν μ x ≠ 0) :
    Set.Finite {x : ℝ | 1 < x ∧ associatedP ν μ x=0} ∧ ({x : ℝ | 1 < x ∧ associatedP ν μ x=0}:Set ℝ).ncard=if associatedPOneZero ν μ then 1 else 0 := by
  sorry

/-- A complex sum of nonnegative real terms with positive leading term is nonzero. -/
lemma lzero_ne_zero_of_hasSum {f : ℕ → ℝ} {S : ℂ} (h : HasSum (fun k => (f k : ℂ)) S)
    (hf : ∀ k, 0 ≤ f k) (h0 : 0 < f 0) : S ≠ 0 := by
  have hr : HasSum f S.re := by simpa using Complex.reCLM.hasSum h
  intro hS
  rw [hS, zero_re] at hr
  have := le_hasSum hr 0 fun j _ => hf j
  linarith

/-- The regularized Gauss series is positive for positive parameters on `(0, 1)`. -/
lemma lzero_regularizedGaussHG_ne_zero {a b c w : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hw0 : 0 ≤ w) (hw1 : w < 1) : regularizedGaussHG a b c w ≠ 0 := by
  have hw : ‖(w : ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]; exact hw1
  rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw]
  have hG : ∀ n : ℕ, 0 < Real.Gamma (c + n) := fun n => Real.Gamma_pos_of_pos (by positivity)
  refine lzero_ne_zero_of_hasSum (f := fun n => (ascPochhammer ℝ n).eval a *
    (ascPochhammer ℝ n).eval b * w ^ n / n.factorial * (Real.Gamma (c + n))⁻¹)
    ((hasSum_regularizedGaussHGFun _ _ _ hw).congr_fun fun n => ?_) (fun n => ?_) ?_
  · rw [ascPochhammer_eval_ofReal, ascPochhammer_eval_ofReal,
      show (c : ℂ) + n = ((c + n : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  · have := ascPochhammer_pos n a ha
    have := ascPochhammer_pos n b hb
    have := hG n
    positivity
  · have := hG 0
    simp only [ascPochhammer_zero, Polynomial.eval_one, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul, Nat.cast_zero, add_zero]
    positivity

lemma lzero_olverQ_ne_zero_of_nonneg {ν μ : ℝ} (hν : -1 < ν) (hμ : 0 ≤ μ) {x : ℝ} (hx : 1 < x) :
    olverQ ν μ x ≠ 0 := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith)
  unfold olverQ legendreBranchPower
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 : (2 : ℂ) ^ ((ν : ℂ) + 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hxp : (x : ℂ) ^ ((ν : ℂ) + μ + 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
  have hw : (1 : ℂ) / (x : ℂ) ^ 2 = ((1 / x ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have hF := lzero_regularizedGaussHG_ne_zero (a := (ν + μ + 2) / 2) (b := (ν + μ + 1) / 2)
    (c := ν + 3 / 2) (w := 1 / x ^ 2) (by linarith) (by linarith) (by linarith) (by positivity)
    (by rw [div_lt_one (by positivity)]; nlinarith)
  push_cast at hF
  rw [hw]
  push_cast
  exact mul_ne_zero (div_ne_zero (mul_ne_zero hπ (exp_ne_zero _)) (mul_ne_zero h2 hxp)) hF

/-- DLMF 14.16(iii): no exterior zeros for degree greater than minus one. -/
theorem olverQ_no_exterior_zero {ν μ : ℝ} (hν : -1 < ν) {x : ℝ} (hx : 1 < x) :
    olverQ ν μ x ≠ 0 := by
  rcases le_or_gt 0 μ with hμ | hμ
  · exact lzero_olverQ_ne_zero_of_nonneg hν hμ hx
  · have hs : (x : ℂ) - 1 ∈ slitPlane := by
      rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.mpr (by linarith)
    have h := associated_connection_14 ν (-μ : ℝ) hs
    rw [show -((-μ : ℝ) : ℂ) = (μ : ℂ) by push_cast; ring] at h
    rw [h]
    exact lzero_olverQ_ne_zero_of_nonneg hν (by linarith) hx

/-- A `C²` function on `[a, b]` vanishing at both ends, whose second derivative is positive at
any positive critical point, is nonpositive on `[a, b]`. -/
lemma lzero_nonpos_of_ode {g g' g'' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hg : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (hg' : ∀ x ∈ Icc a b, HasDerivAt g' (g'' x) x)
    (hode : ∀ x ∈ Icc a b, 0 < g x → g' x = 0 → 0 < g'' x) (ha : g a = 0) (hb : g b = 0) :
    ∀ x ∈ Icc a b, g x ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, hgy⟩ := hcon
  have hc : ContinuousOn g (Icc a b) := fun x hx => (hg x hx).continuousAt.continuousWithinAt
  obtain ⟨x0, hx0, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab.le) hc
  have hpos : 0 < g x0 := hgy.trans_le (hmax hy)
  have hxa : a < x0 := lt_of_le_of_ne hx0.1 (fun h => by rw [← h, ha] at hpos; exact lt_irrefl _ hpos)
  have hxb : x0 < b := lt_of_le_of_ne hx0.2 (fun h => by rw [h, hb] at hpos; exact lt_irrefl _ hpos)
  have hloc : IsLocalMax g x0 := hmax.isLocalMax (Icc_mem_nhds hxa hxb)
  have hd0 : g' x0 = 0 := hloc.hasDerivAt_eq_zero (hg x0 hx0)
  have hdd := hode x0 hx0 hpos hd0
  -- `g'` is positive just to the right of `x0`
  have hsl := hasDerivAt_iff_tendsto_slope.mp (hg' x0 hx0)
  have hev : ∀ᶠ x in 𝓝[>] x0, 0 < g' x := by
    have h1 : ∀ᶠ x in 𝓝[≠] x0, 0 < slope g' x0 x := hsl.eventually (lt_mem_nhds hdd)
    filter_upwards [nhdsWithin_mono _ (fun x (hx : x ∈ Ioi x0) => ne_of_gt hx) h1,
      self_mem_nhdsWithin] with x hx hx'
    rw [slope_def_field, hd0, sub_zero] at hx
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hx')).mp hx
  obtain ⟨c, hc0, hcsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  set x := min ((x0 + c) / 2) ((x0 + b) / 2)
  have hx1 : x0 < x := lt_min (by linarith [hc0.out]) (by linarith)
  have hx2 : x < c := (min_le_left _ _).trans_lt (by linarith [hc0.out])
  have hx3 : x < b := (min_le_right _ _).trans_lt (by linarith)
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' hx1
    (fun t ht => (hg t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt.continuousWithinAt)
    (fun t ht => hg t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hgξ : 0 < g' ξ := hcsub ⟨hξ.1, hξ.2.trans hx2⟩
  rw [hξeq] at hgξ
  have : g x0 < g x := by
    have := (div_pos_iff_of_pos_right (sub_pos.mpr hx1)).mp hgξ; linarith
  exact absurd (hmax ⟨by linarith, hx3.le⟩) (not_le.mpr this)

lemma lzero_mem {x : ℝ} (hx : 1 < x) : (x : ℂ) ∈ {z : ℂ | z - 1 ∈ slitPlane} := by
  show (x : ℂ) - 1 ∈ slitPlane
  rw [show (x : ℂ) - 1 = ((x - 1 : ℝ) : ℂ) by push_cast; ring]
  exact ofReal_mem_slitPlane.mpr (by linarith)

/-- The real ODE of `x ↦ Re 𝑸(x)` on `(1, ∞)`. -/
lemma lzero_real_ode (ν μ : ℝ) {x : ℝ} (hx : 1 < x) :
    let Q := olverQ ν μ
    HasDerivAt (fun t : ℝ => (Q t).re) (deriv Q x).re x ∧
      HasDerivAt (fun t : ℝ => (deriv Q t).re) (deriv (deriv Q) x).re x ∧
      (1 - x ^ 2) * (deriv (deriv Q) x).re - 2 * x * (deriv Q x).re +
        (ν * (ν + 1) - μ ^ 2 / (1 - x ^ 2)) * (Q x).re = 0 := by
  intro Q
  have hA := olverQ_analytic ν μ (x : ℂ) (lzero_mem hx)
  refine ⟨hA.differentiableAt.hasDerivAt.real_of_complex,
    hA.deriv.differentiableAt.hasDerivAt.real_of_complex, ?_⟩
  have h := olverQ_ode ν μ (z := (x : ℂ)) (lzero_mem hx)
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  have h' := congrArg re h
  rw [show (1 - (x : ℂ) ^ 2) = ((1 - x ^ 2 : ℝ) : ℂ) by push_cast; ring,
    show 2 * (x : ℂ) = ((2 * x : ℝ) : ℂ) by push_cast; ring,
    show ((ν : ℂ) * (ν + 1) - (μ : ℂ) ^ 2 / ((1 - x ^ 2 : ℝ) : ℂ)) =
      ((ν * (ν + 1) - μ ^ 2 / (1 - x ^ 2) : ℝ) : ℂ) by push_cast; ring] at h'
  simpa only [add_re, sub_re, re_ofReal_mul, zero_re] using h'

/-- At most one exterior zero; the identically zero regularized solution is excluded. -/
theorem olverQ_at_most_one_exterior_zero {ν μ : ℝ} (hν : ν < -1) (hnondeg : ∃ x : ℝ, 1 < x ∧ olverQ ν μ x ≠ 0) :
    ∀ x y : ℝ, 1 < x → 1 < y → olverQ ν μ x=0 → olverQ ν μ y=0 → x=y := by
  set Q := olverQ ν μ
  have hνν : 0 < ν * (ν + 1) := by nlinarith
  -- two zeros `a < b` force `Q = 0` on `[a, b]`
  have key : ∀ a b : ℝ, 1 < a → a < b → Q a = 0 → Q b = 0 → ∀ t ∈ Icc a b, Q t = 0 := by
    intro a b ha hab hQa hQb t ht
    have hI : ∀ s ∈ Icc a b, 1 < s := fun s hs => ha.trans_le hs.1
    have hode : ∀ (σ : ℝ), σ = 1 ∨ σ = -1 → ∀ s ∈ Icc a b, 0 < σ * (Q s).re →
        σ * (deriv Q s).re = 0 → 0 < σ * (deriv (deriv Q) s).re := by
      intro σ hσ s hs hpos hd
      obtain ⟨-, -, he⟩ := lzero_real_ode ν μ (hI s hs)
      have hs1 : 1 - s ^ 2 < 0 := by nlinarith [hI s hs]
      have hq : 0 < ν * (ν + 1) - μ ^ 2 / (1 - s ^ 2) := by
        have : μ ^ 2 / (1 - s ^ 2) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hs1.le
        linarith
      have he' : (1 - s ^ 2) * (σ * (deriv (deriv Q) s).re) =
          2 * s * (σ * (deriv Q s).re) - (ν * (ν + 1) - μ ^ 2 / (1 - s ^ 2)) * (σ * (Q s).re) := by
        linear_combination σ * he
      rw [hd, mul_zero, zero_sub] at he'
      have : (1 - s ^ 2) * (σ * (deriv (deriv Q) s).re) < 0 := by
        rw [he']; exact neg_neg_of_pos (mul_pos hq hpos)
      by_contra hle
      push Not at hle
      nlinarith
    have hσ : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → σ * (Q t).re ≤ 0 := by
      intro σ hσs
      refine lzero_nonpos_of_ode (g := fun s => σ * (Q s).re) (g' := fun s => σ * (deriv Q s).re)
        (g'' := fun s => σ * (deriv (deriv Q) s).re) hab
        (fun s hs => (lzero_real_ode ν μ (hI s hs)).1.const_mul σ)
        (fun s hs => (lzero_real_ode ν μ (hI s hs)).2.1.const_mul σ)
        (hode σ hσs) (by simp [hQa]) (by simp [hQb]) t ht
    have h1 := hσ 1 (Or.inl rfl)
    have h2 := hσ (-1) (Or.inr rfl)
    have hre : (Q t).re = 0 := by linarith
    have him : (Q t).im = 0 := olverQ_real ν μ (hI t ht)
    exact Complex.ext hre him
  intro x y hx hy hQx hQy
  by_contra hxy
  wlog hlt : x < y generalizing x y
  · exact this y x hy hx hQy hQx (Ne.symm hxy) (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hxy))
  obtain ⟨w, hw, hQw⟩ := hnondeg
  -- identity theorem on the slit domain
  set U := {z : ℂ | z - 1 ∈ slitPlane}
  have hU : IsPreconnected U := isPreconnected_sub_one_mem_slitPlane
  have hfreq : ∃ᶠ z in 𝓝[≠] (x : ℂ), Q z = 0 := by
    have ht : Tendsto (fun n : ℕ => ((x + (y - x) / (n + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have : Tendsto (fun n : ℕ => x + (y - x) / ((n : ℝ) + 2)) atTop (𝓝 (x + 0)) :=
          tendsto_const_nhds.add (tendsto_const_nhds.div_atTop
            (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
        rw [add_zero] at this
        exact (continuous_ofReal.tendsto _).comp this
      · simp only [mem_compl_iff, mem_singleton_iff, ofReal_inj]
        have : 0 < (y - x) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
        linarith
    refine ht.frequently (Frequently.of_forall fun n => ?_)
    have hn : (y - x) / ((n : ℝ) + 2) ≤ y - x := div_le_self (by linarith) (by linarith)
    have hn0 : 0 < (y - x) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
    exact key x y hx hlt hQx hQy _ ⟨by linarith, by linarith⟩
  have hzero := (olverQ_analytic ν μ).eqOn_zero_of_preconnected_of_frequently_eq_zero hU
    (lzero_mem hx) hfreq
  exact hQw (hzero (lzero_mem hw))

end DLMF.Legendre
