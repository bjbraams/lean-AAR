/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Integrals
public import AAR.Legendre.Connections

/-!
# Removable parameter values in source formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- Sine-weighted digamma with its removable values at negative integral degree. -/
def legendreSinDigamma (ν : ℂ) : ℂ :=
  limUnder (𝓝[≠] ν) (fun v => sin (π*v)*digamma (v+1))

/-- Sine-squared-weighted trigamma with removable values. -/
def legendreSinSqTrigamma (ν : ℂ) : ℂ :=
  limUnder (𝓝[≠] ν) (fun v => (sin (π*v))^2*deriv digamma (v+1))

/-- legendreSinDigamma limit. -/
theorem legendreSinDigamma_limit (ν : ℂ) :
    Tendsto (fun v => sin (π*v)*digamma (v+1)) (𝓝[≠] ν) (𝓝 (legendreSinDigamma ν)) := by
  sorry

/-- legendreSinSqTrigamma limit. -/
theorem legendreSinSqTrigamma_limit (ν : ℂ) :
    Tendsto (fun v => (sin (π*v))^2*deriv digamma (v+1)) (𝓝[≠] ν) (𝓝 (legendreSinSqTrigamma ν)) := by
  sorry

/-- ferrersPP integral all degrees. -/
@[dlmf 14.17.E10]
theorem ferrersPP_integral_all_degrees (ν lam : ℂ) (h0 : lam ≠ ν) (h1 : lam ≠ -ν-1) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersP lam 0 x)=2*(2*(sin (π*lam)*legendreSinDigamma ν-sin (π*ν)*legendreSinDigamma lam)+π*sin ((lam-ν)*π))/(π^2*(lam-ν)*(lam+ν+1)) := by
  sorry

/-- ferrersP sq integral all degrees. -/
@[dlmf 14.17.E11]
theorem ferrersP_sq_integral_all_degrees {ν : ℂ} (hν : ν ≠ -1/2) :
    (∫ x : ℝ in -1..1, (ferrersP ν 0 x)^2)=(π^2-2*legendreSinSqTrigamma ν)/(π^2*(ν+1/2)) := by
  sorry

/-- ferrersP negative order parameter limit. -/
@[dlmf 14.9.E3]
theorem ferrersP_negative_order_parameter_limit (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun v : ℂ => (-1)^m*Gamma (v-m+1)/Gamma (v+m+1)*ferrersP v m x) (𝓝[≠] ν) (𝓝 (ferrersP ν (-m) x)) := by
  have ht : ((1:ℂ)-x)/2 ∈ cutPlane := by
    rw [mem_cutPlane, show (1:ℂ) - (1-(x:ℂ))/2 = (((1+x)/2 : ℝ) : ℂ) by push_cast; ring]
    exact Or.inl (by simp only [ofReal_re]; linarith [hx.1])
  have hc : Continuous fun v : ℂ => ferrersP v (-m) x := by
    unfold ferrersP
    exact continuous_const.mul (differentiable_regularizedGaussHG_comp (A := fun v => v+1) (B := fun v => -v)
      (C := fun _ => 1-(-(m:ℂ))) (by fun_prop) (by fun_prop) (by fun_prop) ht).continuous
  refine ((hc.tendsto ν).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_affine_ne_neg_nat one_ne_zero (-(m:ℂ)+1) ν] with v hv
  exact ferrersP_negative_integer_order v m (fun n hn => hv n (by linear_combination hn)) hx

/-- associatedP negative order parameter limit. -/
@[dlmf 14.9.E13]
theorem associatedP_negative_order_parameter_limit (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Tendsto (fun v : ℂ => Gamma (v-m+1)/Gamma (v+m+1)*associatedP v m z) (𝓝[≠] ν) (𝓝 (associatedP ν (-m) z)) := by
  have ht := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have hc : Continuous fun v : ℂ => associatedP v (-m) z := by
    unfold associatedP
    exact continuous_const.mul (differentiable_regularizedGaussHG_comp (A := fun v => v+1) (B := fun v => -v)
      (C := fun _ => 1-(-(m:ℂ))) (by fun_prop) (by fun_prop) (by fun_prop) ht).continuous
  refine ((hc.tendsto ν).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_affine_ne_neg_nat one_ne_zero (-(m:ℂ)+1) ν] with v hv
  exact associatedP_negative_integer_order v m (fun n hn => hv n (by linear_combination hn)) hz

end AAR.Legendre
