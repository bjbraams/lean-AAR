/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Scorer
public import AAR.Airy.Asymptotics

/-!
# Scorer exponential and integrated asymptotics, DLMF §9.12

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- scorerHi two scale expansion (DLMF 9.12.29). -/
@[dlmf 9.12.E29]
theorem scorerHi_two_scale_expansion {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π) (N M : ℕ) :
    IsBigO (airySector (π - δ))
      (fun z => scorerHi z + (1 / (π * z) *
        ∑ k ∈ Finset.range N, ((3 * k).factorial : ℂ) / (k.factorial * (3 * z ^ 3) ^ k)) -
          airyPrefactor .bi z * airyExponentialSum .bi M z)
      (fun z => ‖z‖ ^ (-(3 * N + 1 : ℤ)) + ‖airyPrefactor .bi z / airyZetaComplex z ^ M‖) := by
  sorry

/-- scorerGi primitive asymptotic (DLMF 9.12.30). -/
@[dlmf 9.12.E30]
theorem scorerGi_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (airySector (π / 3 - δ))
      (fun z => primitive (fun t => scorerGi t) z - log z / π -
        (2 * (Real.eulerMascheroniConstant : ℂ) + log 3) / (3 * π) -
        (∑ k ∈ Finset.range N, -(1 : ℂ) *
          ((3 * (k + 1) - 1).factorial : ℂ) / ((k + 1).factorial * (3 * z ^ 3) ^ (k + 1))) / π)
      (fun z => z ^ (-3 * ((N : ℂ) + 1))) := by
  sorry

/-- scorerHi primitive asymptotic (DLMF 9.12.31). -/
@[dlmf 9.12.E31]
theorem scorerHi_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N : ℕ) :
    IsBigO (airySector (2 * π / 3 - δ))
      (fun z => primitive (fun t => scorerHi (-t)) z - log z / π -
        (2 * (Real.eulerMascheroniConstant : ℂ) + log 3) / (3 * π) -
        (∑ k ∈ Finset.range N, (-1 : ℂ) ^ k *
          ((3 * (k + 1) - 1).factorial : ℂ) / ((k + 1).factorial * (3 * z ^ 3) ^ (k + 1))) / π)
      (fun z => z ^ (-3 * ((N : ℂ) + 1))) := by
  sorry

end AAR.Airy
