/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import AAR.Confluent.Basic
public import AAR.Confluent.BasicProperties
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Whittaker functions (AAR §4.3)

Whittaker's functions are the standard pair of solutions of the Whittaker equation,
written in terms of Kummer's `M` and the continued Tricomi `U`.
The `OnLog` definitions retain the logarithmic argument for monodromy;
ordinary multiplication of the complex argument by `exp (2πi)` would lose that information.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

/-- Whittaker's `M_{κ,μ}(z)`. -/
@[dlmf 13.14.E2]
def whittakerM (κ μ z : ℂ) : ℂ :=
  exp (-z / 2) * z ^ (μ + 1 / 2) * confluentM (μ - κ + 1 / 2) (1 + 2 * μ) z

/-- Whittaker's principal-branch W, defined through the continued Tricomi function. -/
@[dlmf 13.14.E3]
def whittakerW (κ μ z : ℂ) : ℂ :=
  exp (-z / 2) * z ^ (1 / 2 + μ) * confluentU (1 / 2 + μ - κ) (1 + 2 * μ) z

/-- A half-integer Whittaker specialization whose former raw Gamma formula vanished. -/
lemma whittakerW_half_zero (z : ℂ) :
    whittakerW (1 / 2) 0 z = exp (-z / 2) * z ^ (1 / 2 : ℂ) := by
  norm_num [whittakerW, confluentU_zero]

/-- Whittaker's M on the logarithmic argument plane, which records full turns around zero. -/
def whittakerMOnLog (κ μ w : ℂ) : ℂ :=
  exp (-exp w / 2) * exp ((μ + 1 / 2) * w) *
    confluentM (μ - κ + 1 / 2) (1 + 2 * μ) (exp w)

/-- Whittaker's W connection formula on the logarithmic argument plane.
It represents W when `2 * μ` is not an integer. -/
def whittakerWOnLog (κ μ w : ℂ) : ℂ :=
  Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * whittakerMOnLog κ μ w +
    Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * whittakerMOnLog κ (-μ) w

/-- Logarithmic derivative of the prefactor in Whittaker's `M`. -/
lemma hasDerivAt_whittakerPrefactor (r : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => exp (-w / 2) * w ^ r)
      (exp (-z / 2) * z ^ r * (r / z - 1 / 2)) z := by
  have hd := (((hasDerivAt_id z).neg.div_const 2).cexp).mul
    ((hasDerivAt_id z).cpow_const (c := r) hz)
  convert! hd using 1
  simp only [id_eq, Pi.neg_apply, mul_one]
  rw [cpow_sub _ _ (slitPlane_ne_zero hz), cpow_one]
  field_simp
  ring

/-- Whittaker's equation (AAR §4.3). -/
@[dlmf 13.14.E1]
theorem whittakerM_ode {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    iteratedDeriv 2 (whittakerM κ μ) z +
      (-1 / 4 + κ / z + (1 / 4 - μ ^ 2) / z ^ 2) * whittakerM κ μ z = 0 := by
  let r := μ + 1 / 2
  let y := confluentM (μ - κ + 1 / 2) (1 + 2 * μ)
  let g := fun w : ℂ => exp (-w / 2) * w ^ r
  let q := fun w : ℂ => r / w - 1 / 2
  have hf := hasFPowerSeriesOnBall_confluentM (a := μ - κ + 1 / 2) hμ
  have hy (w : ℂ) : HasDerivAt y (deriv y w) w :=
    (hf.analyticAt_of_mem (y := w) (by simp)).differentiableAt.hasDerivAt
  have hy' : HasDerivAt (deriv y) (iteratedDeriv 2 y z) z := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      (hf.deriv_ofScalars.analyticAt_of_mem (y := z) (by simp)).differentiableAt.hasDerivAt
  have hg (w : ℂ) (hw : w ∈ slitPlane) : HasDerivAt g (g w * q w) w :=
    hasDerivAt_whittakerPrefactor r hw
  have hq : HasDerivAt q (-r / z ^ 2) z := by
    convert! ((hasDerivAt_const z r).div (hasDerivAt_id z) (slitPlane_ne_zero hz)).sub_const
      (1 / 2) using 1
    simp
  have hfirst (w : ℂ) (hw : w ∈ slitPlane) :
      deriv (whittakerM κ μ) w = g w * (deriv y w + q w * y w) := by
    have hd := (hg w hw).mul (hy w)
    change deriv (g * y) w = _
    rw [hd.deriv]
    ring
  have heq : deriv (whittakerM κ μ) =ᶠ[𝓝 z]
      (g * (deriv y + q * y)) :=
    Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) hfirst
  have hsecond := (hg z hz).mul (hy'.add (hq.mul (hy z)))
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero,
    heq.deriv_eq, hsecond.deriv]
  have hode := confluentM_ode (a := μ - κ + 1 / 2) hμ (slitPlane_ne_zero hz)
  change z * iteratedDeriv 2 y z + (1 + 2 * μ - z) * deriv y z -
    (μ - κ + 1 / 2) * y z = 0 at hode
  change _ + _ * (g z * y z) = 0
  dsimp [q, r]
  field_simp [slitPlane_ne_zero hz]
  linear_combination (16 * z * g z) * hode

/-- Whittaker's `M` is analytic away from the principal power's branch cut. -/
lemma analyticAt_whittakerM {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) : AnalyticAt ℂ (whittakerM κ μ) z := by
  unfold whittakerM
  apply AnalyticAt.mul
  · apply AnalyticAt.mul
    · fun_prop
    · exact analyticAt_id.cpow analyticAt_const hz
  · exact (hasFPowerSeriesOnBall_confluentM (a := μ - κ + 1 / 2) hμ).analyticAt_of_mem
      (by simp)

/-- The generic connection formula for W; the integer case uses continuation. -/
@[dlmf 13.14.E33]
lemma whittakerW_eq_connection {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℤ, 2 * μ ≠ k) :
    whittakerW κ μ z =
      Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * whittakerM κ μ z +
        Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * whittakerM κ (-μ) z := by
  have hb : ∀ k : ℤ, (1 : ℂ) + 2 * μ ≠ k := by
    intro k hk
    apply hμ (k - 1)
    push_cast
    linear_combination hk
  unfold whittakerW
  rw [confluentU_eq_connection _ _ _ hb]
  unfold confluentUConnection whittakerM
  symm
  have hz0 := slitPlane_ne_zero hz
  have h1b : (1 : ℂ) - (1 + 2 * μ) = -2 * μ := by ring
  have hb1 : (1 + 2 * μ : ℂ) - 1 = 2 * μ := by ring
  have hab : (1 / 2 + μ - κ : ℂ) - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ := by ring
  have h2b : (2 : ℂ) - (1 + 2 * μ) = 1 - 2 * μ := by ring
  have hMμ : (μ : ℂ) - κ + 1 / 2 = 1 / 2 + μ - κ := by ring
  have hMμ' : (-μ : ℂ) - κ + 1 / 2 = 1 / 2 - μ - κ := by ring
  have hden : (1 : ℂ) + 2 * (-μ) = 1 - 2 * μ := by ring
  have hpow : z ^ (1 / 2 + μ) * z ^ (-2 * μ) = z ^ (1 / 2 - μ) := by
    rw [← cpow_add _ _ hz0]
    ring_nf
  simp only [h1b, hb1, hab, h2b, hMμ, hMμ', hden]
  rw [mul_add]
  have hswap :
      exp (-z / 2) * z ^ (1 / 2 + μ) *
          (Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * z ^ (-2 * μ) *
            confluentM (1 / 2 - μ - κ) (1 - 2 * μ) z) =
        Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) *
          (exp (-z / 2) * z ^ (1 / 2 - μ) * confluentM (1 / 2 - μ - κ) (1 - 2 * μ) z) := by
    calc
      _ = Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * exp (-z / 2) *
            (z ^ (1 / 2 + μ) * z ^ (-2 * μ)) *
            confluentM (1 / 2 - μ - κ) (1 - 2 * μ) z := by ring
      _ = _ := by rw [hpow]; ring
  rw [hswap]
  ring_nf

/-- Whittaker's `W` satisfies the same equation. -/
@[dlmf 13.14.E1]
theorem whittakerW_ode {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℤ, 2 * μ ≠ k) :
    iteratedDeriv 2 (whittakerW κ μ) z +
      (-1 / 4 + κ / z + (1 / 4 - μ ^ 2) / z ^ 2) * whittakerW κ μ z = 0 := by
  have hpos : ∀ k : ℕ, 1 + 2 * μ ≠ -k := by
    intro k hk
    apply hμ (-(k : ℤ) - 1)
    push_cast
    linear_combination hk
  have hneg : ∀ k : ℕ, 1 + 2 * (-μ) ≠ -k := by
    intro k hk
    apply hμ ((k : ℤ) + 1)
    push_cast
    linear_combination -hk
  have hp := whittakerM_ode (κ := κ) hz hpos
  have hn := whittakerM_ode (κ := κ) hz hneg
  have hap := (analyticAt_whittakerM (κ := κ) hz hpos).contDiffAt (n := 2)
  have han := (analyticAt_whittakerM (κ := κ) hz hneg).contDiffAt (n := 2)
  have heq : whittakerW κ μ =ᶠ[𝓝 z] (fun w =>
      Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * whittakerM κ μ w +
        Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * whittakerM κ (-μ) w) :=
    Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun w hw =>
      whittakerW_eq_connection hw hμ
  rw [heq.iteratedDeriv_eq 2, whittakerW_eq_connection hz hμ]
  rw [iteratedDeriv_fun_add (contDiffAt_const.mul hap) (contDiffAt_const.mul han),
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
  linear_combination
    Gamma (-2 * μ) / Gamma (1 / 2 - μ - κ) * hp +
      Gamma (2 * μ) / Gamma (1 / 2 + μ - κ) * hn

namespace AAR.Confluent

/-- The definition of W through the continued Tricomi function. -/
@[dlmf 13.14.E3]
theorem whittakerW_eq_confluentU {κ μ z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (1 / 2 + μ) * confluentU (1 / 2 + μ - κ) (1 + 2 * μ) z := by
  rfl

@[dlmf 13.14.E4]
theorem confluentM_eq_whittakerM {a b z : ℂ} (hz : z ∈ slitPlane)
    (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b z =
      exp (z / 2) * z ^ (-b / 2) * whittakerM (b / 2 - a) (b / 2 - 1 / 2) z := by
  unfold whittakerM
  have hz0 := slitPlane_ne_zero hz
  have hr : (b / 2 - 1 / 2 : ℂ) + 1 / 2 = b / 2 := by ring
  have ha : (b / 2 - 1 / 2 : ℂ) - (b / 2 - a) + 1 / 2 = a := by ring
  have hb' : (1 : ℂ) + 2 * (b / 2 - 1 / 2) = b := by ring
  rw [hr, ha, hb']
  have hpow : z ^ (-b / 2) * z ^ (b / 2) = 1 := by
    rw [← cpow_add _ _ hz0]
    ring_nf
    simp
  have hexp : exp (z / 2) * exp (-z / 2) = 1 := by
    rw [← exp_add]
    convert exp_zero using 2
    ring
  calc
    confluentM a b z
        = (exp (z / 2) * exp (-z / 2)) * (z ^ (-b / 2) * z ^ (b / 2)) * confluentM a b z := by
          rw [hexp, hpow]; ring
    _ = exp (z / 2) * z ^ (-b / 2) *
          (exp (-z / 2) * z ^ (b / 2) * confluentM a b z) := by ring

@[dlmf 13.14.E5]
theorem confluentU_eq_whittakerW {a b z : ℂ} (hz : z ∈ slitPlane) :
    confluentU a b z =
      exp (z / 2) * z ^ (-b / 2) * whittakerW (b / 2 - a) (b / 2 - 1 / 2) z := by
  have hz0 := slitPlane_ne_zero hz
  have hW := whittakerW_eq_confluentU (κ := b / 2 - a) (μ := b / 2 - 1 / 2) hz
  have hμ : (1 / 2 + (b / 2 - 1 / 2) - (b / 2 - a) : ℂ) = a := by ring
  have hb' : (1 + 2 * (b / 2 - 1 / 2) : ℂ) = b := by ring
  have hr : (1 / 2 + (b / 2 - 1 / 2) : ℂ) = b / 2 := by ring
  rw [hμ, hb', hr] at hW
  have hpow : z ^ (-b / 2) * z ^ (b / 2) = 1 := by
    rw [← cpow_add _ _ hz0]
    ring_nf
    simp
  have hexp : exp (z / 2) * exp (-z / 2) = 1 := by
    rw [← exp_add]
    convert exp_zero using 2
    ring
  calc
    confluentU a b z
        = (exp (z / 2) * exp (-z / 2)) * (z ^ (-b / 2) * z ^ (b / 2)) * confluentU a b z := by
          rw [hexp, hpow]; ring
    _ = exp (z / 2) * z ^ (-b / 2) *
          (exp (-z / 2) * z ^ (b / 2) * confluentU a b z) := by ring
    _ = exp (z / 2) * z ^ (-b / 2) * whittakerW (b / 2 - a) (b / 2 - 1 / 2) z := by
          rw [hW]

/-- The punctured parameter limit of normalized Whittaker M at a denominator pole. -/
@[dlmf 13.14.E7]
theorem tendsto_whittakerM_div_Gamma (κ : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun μ : ℂ => whittakerM κ μ z / Gamma (2 * μ + 1)) (𝓝[≠] (-(n + 1 : ℂ) / 2))
      (𝓝 (poch (-(n : ℂ) / 2 - κ) (n + 1) / (n + 1).factorial *
        whittakerM κ ((n + 1 : ℂ) / 2) z)) := by
  sorry

/-- Half-turn continuation of Whittaker M on the logarithmic argument plane. -/
@[dlmf 13.14.E10]
theorem whittakerM_neg_argument {κ μ z : ℂ} (hz : z ∈ slitPlane) (sign : Bool)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerMOnLog κ μ (log z + (if sign then 1 else -1) * π * I) =
      (if sign then 1 else -1) * I * exp ((if sign then 1 else -1) * μ * π * I) *
        whittakerM (-κ) μ z := by
  sorry

/-- Full-turn continuation of Whittaker M, retaining the logarithmic argument. -/
@[dlmf 13.14.E11]
theorem whittakerM_continuation {κ μ z : ℂ} (m : ℤ) (hz : z ∈ slitPlane) :
    whittakerMOnLog κ μ (log z + 2 * m * π * I) =
      (-1 : ℂ) ^ m * exp (2 * m * μ * π * I) * whittakerM κ μ z := by
  have hz0 := slitPlane_ne_zero hz
  have ht : exp (2 * (m : ℂ) * π * I) = 1 := by
    rw [show 2 * (m : ℂ) * π * I = (m : ℂ) * (2 * π * I) by ring,
      exp_int_mul_two_pi_mul_I]
  have he : exp (log z + 2 * m * π * I) = z := by rw [exp_add, ht, exp_log hz0, mul_one]
  have hm : exp ((m : ℂ) * (π * I)) = (-1 : ℂ) ^ m := by
    rw [exp_int_mul, exp_pi_mul_I]
  have hp : exp ((μ + 1 / 2) * (log z + 2 * m * π * I)) =
      (-1 : ℂ) ^ m * exp (2 * m * μ * π * I) * z ^ (μ + 1 / 2) := by
    rw [show (μ + 1 / 2) * (log z + 2 * m * π * I) =
      (m * (π * I) + 2 * m * μ * π * I) + log z * (μ + 1 / 2) by ring,
      exp_add, exp_add, hm, cpow_def_of_ne_zero hz0]
  simp only [whittakerMOnLog, whittakerM, he, hp]
  ring

/-- Full-turn continuation of Whittaker W at noninteger twice-order. -/
@[dlmf 13.14.E12]
theorem whittakerW_continuation {κ μ z : ℂ} (m : ℤ) (hz : z ∈ slitPlane)
    (hμ : ∀ n : ℤ, 2 * μ ≠ n) :
    whittakerWOnLog κ μ (log z + 2 * m * π * I) =
      (-1 : ℂ) ^ (m + 1) * 2 * π * I * sin (2 * π * μ * m) /
          (Gamma (1 / 2 - μ - κ) * Gamma (1 + 2 * μ) * sin (2 * π * μ)) *
        whittakerM κ μ z +
        (-1 : ℂ) ^ m * exp (-2 * m * μ * π * I) * whittakerW κ μ z := by
  sorry

@[dlmf 13.14.E14]
theorem isBigO_whittakerM_at_zero {κ μ : ℂ} (hμ : ∀ k : ℕ, 2 * μ ≠ -k - 1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => whittakerM κ μ z - z ^ (μ + 1 / 2))
      (fun z => z ^ (μ + 3 / 2)) := by
  sorry

@[dlmf 13.14.E20]
theorem tendsto_whittakerM_atTop {κ μ : ℂ} (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k)
    (hκ : ∀ k : ℕ, 1 / 2 + μ - κ ≠ -k) :
    Tendsto (fun x : ℝ => whittakerM κ μ x * Gamma (1 / 2 + μ - κ) /
      (Gamma (1 + 2 * μ) * exp (x / 2) * (x : ℂ) ^ (-κ))) atTop (𝓝 1) := by
  sorry

@[dlmf 13.14.E21]
theorem tendsto_whittakerW_atTop (κ μ : ℂ) :
    Tendsto (fun x : ℝ => whittakerW κ μ x / (exp (-x / 2) * (x : ℂ) ^ κ)) atTop (𝓝 1) := by
  sorry

@[dlmf 13.14.E25]
theorem wronskian_whittakerM {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hμ' : ∀ k : ℕ, 1 - 2 * μ ≠ -k) :
    wronskian (whittakerM κ μ) (whittakerM κ (-μ)) z = -2 * μ := by
  sorry

@[dlmf 13.14.E26]
theorem wronskian_whittakerM_W {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    wronskian (whittakerM κ μ) (whittakerW κ μ) z =
      -Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ - κ) := by
  sorry

/-- DLMF's `W_{-κ,μ}(z e^{±πi})` is represented by the principal value at `-z`, which is the
`e^{+πi}` continuation for `ph z < 0` and the `e^{-πi}` continuation for `ph z > 0`. -/
@[dlmf 13.14.E27]
theorem wronskian_whittakerM_W_neg {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (sign : Bool)
    (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    wronskian (whittakerM κ μ)
      (fun w => whittakerW (-κ) μ (exp ((if sign then 1 else -1) * π * I) * w)) z =
      Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ + κ) *
        exp (-(if sign then 1 else -1) * (1 / 2 + μ) * π * I) := by
  sorry

@[dlmf 13.14.E28]
theorem wronskian_whittakerM_neg_W {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 - 2 * μ ≠ -k) :
    wronskian (whittakerM κ (-μ)) (whittakerW κ μ) z =
      -Gamma (1 - 2 * μ) / Gamma (1 / 2 - μ - κ) := by
  sorry

/-- DLMF's `W_{-κ,μ}(z e^{±πi})` is represented by the principal value at `-z`, which is the
`e^{+πi}` continuation for `ph z < 0` and the `e^{-πi}` continuation for `ph z > 0`. -/
@[dlmf 13.14.E30]
theorem wronskian_whittakerW_pair {κ μ z : ℂ} (hz : z ∈ slitPlane) (sign : Bool)
    (hsign : if sign then z.arg < 0 else 0 < z.arg) :
    wronskian (whittakerW κ μ)
      (fun w => whittakerW (-κ) μ (exp ((if sign then 1 else -1) * π * I) * w)) z =
      exp (-(if sign then 1 else -1) * κ * π * I) := by
  sorry

/-- Symmetry in the order for the generic W connection formula on the slit plane.
Extension to half-integer orders requires the Tricomi parameter-limit API. -/
@[dlmf 13.14.E31]
theorem whittakerW_even_mu (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℤ, 2 * μ ≠ k) :
    whittakerW κ μ z = whittakerW κ (-μ) z := by
  have hneg : ∀ k : ℤ, 2 * (-μ) ≠ k := by
    intro k hk
    apply hμ (-k)
    push_cast
    linear_combination -hk
  rw [whittakerW_eq_connection hz hμ, whittakerW_eq_connection hz hneg]
  simp only [neg_neg]
  rw [add_comm]
  refine congrArg₂ (· + ·) ?_ ?_ <;> congr 1 <;> ring

/-- DLMF's `W_{-κ,μ}(z e^{±πi})` is represented by the principal value at `-z`, which is the
`e^{+πi}` continuation for `ph z ≤ 0` and the `e^{-πi}` continuation for `ph z > 0`. -/
@[dlmf 13.14.E32]
theorem whittakerM_eq_whittakerW_connection {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (sign : Bool)
    (hsign : if sign then z.arg ≤ 0 else 0 < z.arg) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      exp ((if sign then 1 else -1) * (κ - μ - 1 / 2) * π * I) /
          Gamma (1 / 2 + μ + κ) * whittakerW κ μ z +
        exp ((if sign then 1 else -1) * κ * π * I) / Gamma (1 / 2 + μ - κ) *
          whittakerW (-κ) μ (exp ((if sign then 1 else -1) * π * I) * z) := by
  sorry

/-- The jump of `W` across the negative axis, with both continuations `z e^{±πi}` taken on
the logarithmic argument plane. `whittakerWOnLog` represents `W` there for noninteger `2μ`. -/
@[dlmf 13.14.E34]
theorem whittakerM_jump {κ μ z : ℂ} (hz : z ∈ slitPlane) (hμi : ∀ n : ℤ, 2 * μ ≠ n)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hκ : ∀ k : ℕ, 1 / 2 - μ - κ ≠ -k) :
    2 * π / (Gamma (1 + 2 * μ) * Gamma (1 / 2 - μ - κ)) * whittakerM (-κ) μ z =
      exp (μ * π * I) * whittakerWOnLog κ μ (log z + π * I) +
        exp (-μ * π * I) * whittakerWOnLog κ μ (log z - π * I) := by
  sorry

/-- The jump of `W` across the negative axis, with both continuations `z e^{±πi}` taken on
the logarithmic argument plane. `whittakerWOnLog` represents `W` there for noninteger `2μ`. -/
@[dlmf 13.14.E35]
theorem whittakerW_jump {κ μ z : ℂ} (hz : z ∈ slitPlane) (hμi : ∀ n : ℤ, 2 * μ ≠ n) :
    2 * π * I / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) * whittakerW (-κ) μ z =
      exp (-κ * π * I) * whittakerWOnLog κ μ (log z + π * I) -
        exp (κ * π * I) * whittakerWOnLog κ μ (log z - π * I) := by
  sorry

end AAR.Confluent

