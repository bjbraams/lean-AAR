/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Generalized

/-!
# Calculus of the generalized hypergeometric function (Duverney §§3.4–3.6)

For Mathlib's regularized `𝐅(a; b; z) = ∑ ∏(aᵢ)ₙ zⁿ / (n! ∏ Γ(bⱼ+n))`, for all parameters:
* `deriv_regularizedHGFun`: `𝐅'(a; b; z) = (∏ a) 𝐅(a+1; b+1; z)` inside the disc of convergence
  (Duverney Thm 3.11);
* `regularizedHGFun_contiguous`: `θ𝐅(i, a'; b) = i (𝐅(i+1, a'; b) - 𝐅(i, a'; b))`
  (Duverney (3.40));
* `coeff_eq_of_generalized_ode`: a power series solving the generalized hypergeometric equation
  is a multiple of `𝐅` when no `bⱼ` is a nonpositive integer (Duverney Thm 3.8).
-/

@[expose] public section

open Complex Filter FormalMultilinearSeries Polynomial
open scoped Topology Nat

noncomputable section

namespace AAR.Hypergeometric

/-- Raising every parameter by one. -/
abbrev shiftParams (a : Multiset ℂ) : Multiset ℂ := a.map (· + 1)

/-- `(n+1) c_{n+1}(a;b) = (∏ a) c_n(a+1; b+1)` for the regularized coefficients. -/
lemma regularizedHGFunCoeff_succ_deriv (a b : Multiset ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * regularizedHGFunCoeff a b (n + 1) =
      a.prod * regularizedHGFunCoeff (shiftParams a) (shiftParams b) n := by
  unfold regularizedHGFunCoeff
  have ha : (a.map (ascPochhammer ℂ (n + 1)).eval).prod =
      a.prod * ((shiftParams a).map (ascPochhammer ℂ n).eval).prod := by
    rw [Multiset.map_map]
    conv_rhs => rw [show a.prod = (a.map fun x => x).prod by rw [Multiset.map_id']]
    rw [← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun i _ => ?_
    simp [ascPochhammer_succ_left, Polynomial.eval_comp]
  have hb : (b.map (Gamma <| · + ((n + 1 : ℕ) : ℂ))).prod =
      ((shiftParams b).map (Gamma <| · + (n : ℂ))).prod := by
    rw [Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun j _ => ?_
    simp only [Function.comp]; push_cast; ring_nf
  rw [ha, hb, Nat.factorial_succ]
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

/-- The regularized function as a `tsum` of its coefficients. -/
lemma regularizedHGFun_eq_tsum' (a b : Multiset ℂ) (z : ℂ) :
    regularizedHGFun a b z = ∑' n : ℕ, regularizedHGFunCoeff a b n * z ^ n := by
  simp only [regularizedHGFun, FormalMultilinearSeries.sum, regularizedHGFunSeries,
    ofScalars_apply_eq, smul_eq_mul]

/-- **Derivative of the generalized hypergeometric function** (Duverney Thm 3.11; DLMF 16.3.1):
`𝐅'(a; b; z) = (∏ a) 𝐅(a+1; b+1; z)` inside the disc of convergence, for all parameters. -/
@[dlmf 16.3.E1]
theorem deriv_regularizedHGFun {a b : Multiset ℂ}
    (hr : 0 < (regularizedHGFunSeries a b).radius) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries a b).radius) :
    deriv (regularizedHGFun a b) z =
      a.prod * regularizedHGFun (shiftParams a) (shiftParams b) z := by
  have h : HasFPowerSeriesOnBall (regularizedHGFun a b)
      (ofScalars ℂ (regularizedHGFunCoeff a b)) 0 (regularizedHGFunSeries a b).radius :=
    (regularizedHGFunSeries a b).hasFPowerSeriesOnBall hr
  have hd := h.deriv_ofScalars.hasSum_mul_pow hz
  simp_rw [regularizedHGFunCoeff_succ_deriv] at hd
  rw [regularizedHGFun_eq_tsum']
  by_cases h0 : a.prod = 0
  · simp only [h0, zero_mul] at hd ⊢
    exact hd.tsum_eq.symm.trans tsum_zero
  · have hd' := hd.div_const a.prod
    simp_rw [mul_assoc, mul_div_cancel_left₀ _ h0] at hd'
    rw [hd'.tsum_eq]
    field_simp

/-- `n cₙ(i :: a'; b) = i (cₙ(i+1 :: a'; b) - cₙ(i :: a'; b))`. -/
lemma regularizedHGFunCoeff_contiguous (i : ℂ) (a b : Multiset ℂ) (n : ℕ) :
    (n : ℂ) * regularizedHGFunCoeff (i ::ₘ a) b n =
      i * (regularizedHGFunCoeff ((i + 1) ::ₘ a) b n - regularizedHGFunCoeff (i ::ₘ a) b n) := by
  unfold regularizedHGFunCoeff
  simp only [Multiset.map_cons, Multiset.prod_cons]
  have h := ascPochhammer_succ_eval (S := ℂ) n i
  rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one] at h
  linear_combination (-(a.map (ascPochhammer ℂ n).eval).prod *
    (↑n ! * (b.map (Gamma <| · + n)).prod)⁻¹) * h

/-- **Contiguous relation of the generalized hypergeometric function** (Duverney (3.40);
DLMF 16.3.4 form): `θ 𝐅(i, a'; b; z) = i (𝐅(i+1, a'; b; z) - 𝐅(i, a'; b; z))` inside both discs of
convergence. -/
theorem regularizedHGFun_contiguous (i : ℂ) (a b : Multiset ℂ) {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries (i ::ₘ a) b).radius)
    (hz' : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries ((i + 1) ::ₘ a) b).radius) :
    z * deriv (regularizedHGFun (i ::ₘ a) b) z =
      i * (regularizedHGFun ((i + 1) ::ₘ a) b z - regularizedHGFun (i ::ₘ a) b z) := by
  have hr : 0 < (regularizedHGFunSeries (i ::ₘ a) b).radius := by
    rw [Metric.mem_eball] at hz; exact lt_of_le_of_lt zero_le hz
  have hr' : 0 < (regularizedHGFunSeries ((i + 1) ::ₘ a) b).radius := by
    rw [Metric.mem_eball] at hz'; exact lt_of_le_of_lt zero_le hz'
  have h : HasFPowerSeriesOnBall (regularizedHGFun (i ::ₘ a) b)
      (ofScalars ℂ (regularizedHGFunCoeff (i ::ₘ a) b)) 0
        (regularizedHGFunSeries (i ::ₘ a) b).radius :=
    (regularizedHGFunSeries (i ::ₘ a) b).hasFPowerSeriesOnBall hr
  have h' : HasFPowerSeriesOnBall (regularizedHGFun ((i + 1) ::ₘ a) b)
      (ofScalars ℂ (regularizedHGFunCoeff ((i + 1) ::ₘ a) b)) 0
        (regularizedHGFunSeries ((i + 1) ::ₘ a) b).radius :=
    (regularizedHGFunSeries ((i + 1) ::ₘ a) b).hasFPowerSeriesOnBall hr'
  have hd := (h.deriv_ofScalars.hasSum_mul_pow hz).mul_left z
  have hs := h.hasSum_mul_pow hz
  have hs' := h'.hasSum_mul_pow hz'
  have hrhs := (hs'.sub hs).mul_left i
  -- shift the derivative series by one
  have hshift : HasSum (fun n : ℕ => (n : ℂ) * regularizedHGFunCoeff (i ::ₘ a) b n * z ^ n)
      (z * deriv (regularizedHGFun (i ::ₘ a) b) z) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    refine hd.congr_fun fun n => ?_
    push_cast; ring
  refine hshift.unique (hrhs.congr_fun fun n => ?_)
  rw [regularizedHGFunCoeff_contiguous]
  ring

/-- Coefficients of a power series are determined by its sums on a small disk. -/
lemma scalarSeries_unique_ball {c d : ℕ → ℂ} {g : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hc : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => c n * z ^ n) (g z))
    (hd : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => d n * z ^ n) (g z)) : c = d := by
  set ρ' : NNReal := ⟨ρ / 2, by positivity⟩
  have series {e : ℕ → ℂ}
      (he : ∀ z : ℂ, ‖z‖ < ρ → HasSum (fun n => e n * z ^ n) (g z)) :
      HasFPowerSeriesOnBall g (FormalMultilinearSeries.ofScalars ℂ e) 0 (ρ' : ENNReal) := by
    refine ⟨?_, ?_, ?_⟩
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      have hz0 : ‖((ρ / 2 : ℝ) : ℂ)‖ < ρ := by
        rw [norm_real, Real.norm_of_nonneg (by positivity)]; linarith
      have := (he _ hz0).summable.norm
      simp only [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg
        (by positivity : (0 : ℝ) ≤ ρ / 2)] at this
      simp only [FormalMultilinearSeries.ofScalars_norm]
      exact this
    · exact ENNReal.coe_pos.mpr (by rw [← NNReal.coe_pos]; show (0 : ℝ) < ρ / 2; positivity)
    · intro z hz
      have hzNN : ‖z‖₊ < ρ' := by
        simpa only [Metric.mem_eball, edist_zero_right, enorm_lt_coe] using hz
      have hz' : ‖z‖ < ρ / 2 := by exact_mod_cast hzNN
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
        he z (by linarith)
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    ((series hc).hasFPowerSeriesAt.eq_formalMultilinearSeries (series hd).hasFPowerSeriesAt)

/-- **Power-series solutions of the generalized hypergeometric equation** (Duverney Thm 3.8):
if `f = ∑ cₙ zⁿ` near `0` satisfies `θ ∏ⱼ(θ+bⱼ-1) f = z ∏ᵢ(θ+aᵢ) f` and no `bⱼ` is a nonpositive
integer, then `cₙ = c₀ / 𝐅₀ · 𝐅ₙ`, i.e. `f = (f(0)/𝐅(a;b;0)) 𝐅(a;b;·)`. -/
theorem coeff_eq_of_generalized_ode {a b : Multiset ℂ} (hb : ∀ j ∈ b, ∀ k : ℕ, j ≠ -k)
    {f : ℂ → ℂ} {c : ℕ → ℂ} {r : ENNReal} (hr : 0 < r)
    (h : HasFPowerSeriesOnBall f (ofScalars ℂ c) 0 r)
    (hode : ∀ z ∈ Metric.eball (0 : ℂ) r,
      thetaPoly (X * (b.map fun j => X + C (j - 1)).prod) f z =
        z * thetaPoly (a.map fun i => X + C i).prod f z) (n : ℕ) :
    c n = c 0 / regularizedHGFunCoeff a b 0 * regularizedHGFunCoeff a b n := by
  obtain ⟨ρ, hρ0, hρr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  have hball : ∀ z : ℂ, ‖z‖ < ρ → z ∈ Metric.eball (0 : ℂ) r := fun z hz => by
    rw [Metric.mem_eball, edist_zero_right]
    exact lt_trans (by exact_mod_cast hz) hρr
  set Pb : ℂ[X] := X * (b.map fun j => X + C (j - 1)).prod
  set Pa : ℂ[X] := (a.map fun i => X + C i).prod
  set e : ℕ → ℂ := fun n => if n = 0 then 0 else Pa.eval ((n - 1 : ℕ) : ℂ) * c (n - 1)
  have hcoef := scalarSeries_unique_ball (g := thetaPoly Pb f) (c := fun n => Pb.eval (n : ℂ) * c n)
    (d := e) (ρ := ρ) (by exact_mod_cast hρ0)
    (fun z hz => by simpa [mul_assoc] using hasSum_thetaPoly h Pb (hball z hz))
    (fun z hz => by
      rw [hode z (hball z hz)]
      have hs := (hasSum_thetaPoly h Pa (hball z hz)).mul_left z
      rw [← hasSum_nat_add_iff' 1]
      convert hs using 1
      · funext n; simp [e, pow_succ]; ring
      · simp [e])
  have hrec (n : ℕ) : ((n : ℂ) + 1) * (b.map fun j : ℂ => j + n).prod * c (n + 1) =
      (a.map fun i => (n : ℂ) + i).prod * c n := by
    have := congrFun hcoef (n + 1)
    simp only [e, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, Pb, Pa, eval_mul, eval_X,
      eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_add, eval_C] at this
    push_cast at this
    rw [show (b.map fun j : ℂ => (n : ℂ) + 1 + (j - 1)) = b.map fun j : ℂ => j + n by
      congr 1; funext j; ring] at this
    rw [show (a.map fun i : ℂ => (n : ℂ) + i) = a.map fun i : ℂ => (n : ℂ) + i from rfl]
    linear_combination this
  have hκ0 : regularizedHGFunCoeff a b 0 ≠ 0 := by
    rw [Ne, regularizedHGFunCoeff_eq_zero_iff]
    push Not
    refine ⟨fun j _ k hk => absurd hk (Nat.not_lt_zero k), fun j hj m => ?_⟩
    simpa using hb j hj m
  have hden (n : ℕ) : ((n : ℂ) + 1) * (b.map fun j : ℂ => j + n).prod ≠ 0 := by
    refine mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n) ?_
    apply Multiset.prod_ne_zero
    intro h0
    obtain ⟨j, hj, hj0⟩ := Multiset.mem_map.mp h0
    exact hb j hj n (by linear_combination hj0)
  induction n with
  | zero => field_simp
  | succ n ih =>
    have hk := regularizedHGFunCoeff_succ_mul a b n
    refine mul_left_cancel₀ (hden n) ?_
    rw [hrec n, ih]
    linear_combination (-(c 0 / regularizedHGFunCoeff a b 0)) * hk

end AAR.Hypergeometric

end
