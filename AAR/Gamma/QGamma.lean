/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.QSeries.Pochhammer
public import AAR.QSeries.Identities

/-!
# q-gamma and q-beta (DLMF §5.18)

The q-Pochhammer symbols 5.18.1 and 5.18.3, the q-gamma function 5.18.4–5.18.7,
and Jackson's q-beta integral 5.18.12 are already in `AAR.QSeries`. The remaining
identities are recorded here without duplicating those definitions.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

/-- q-factorial, DLMF 5.18.2. -/
@[dlmf 5.18.E2]
def qFactorial (q : ℂ) (n : ℕ) : ℂ :=
  qPochhammer q q n * (1 - q) ^ (-(n : ℂ))

@[dlmf 5.18.E6]
theorem qFactorial_eq_qGamma (q : ℂ) (n : ℕ) (hq : ‖q‖ < 1) (hq0 : q ≠ 1) :
    qFactorial q n = qGamma q (n + 1) := by
  have hb : 1 - q ≠ 0 := sub_ne_zero.mpr fun h => hq0 h.symm
  have hcast : (n + 1 : ℂ) = ↑(n + 1) := by
    rw [Nat.cast_add, Nat.cast_one]
  have hpow : q * q ^ n = q ^ (n + 1 : ℂ) := by
    rw [hcast, cpow_natCast, pow_succ']
  have hsplit := qPochhammerInf_mul_qPochhammer (a := q) hq n
  have hexp : (1 - q) ^ (1 - (n + 1 : ℂ)) = (1 - q) ^ (-(n : ℂ)) := by
    congr 1
    ring
  have hinf : qPochhammerInf (q ^ (n + 1 : ℂ)) q ≠ 0 := by
    refine qPochhammerInf_ne_zero hq fun k hk => ?_
    have hpow' : q ^ (n + 1 : ℂ) = q ^ (n + 1) := by
      rw [hcast, cpow_natCast]
    have hpos : 0 < n + 1 + k := Nat.add_pos_left (Nat.succ_pos n) k
    have hlt : ‖q ^ (n + 1 + k)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq hpos.ne'
    have : q ^ (n + 1) * q ^ k = q ^ (n + 1 + k) := (pow_add _ _ _).symm
    rw [hpow', this, sub_eq_zero] at hk
    rw [← hk, norm_one] at hlt
    exact (lt_irrefl (1 : ℝ)) hlt
  unfold qFactorial qGamma
  rw [hsplit, hpow, hexp]
  field [hinf, hb]

@[dlmf 5.18.E5]
theorem qGamma_two {q : ℂ} (hq : ‖q‖ < 1) : qGamma q 2 = 1 := by
  by_cases hq0 : q = 0
  · subst hq0
    have h0 : (0 : ℂ) ^ (2 : ℂ) = 0 := zero_cpow (by norm_num)
    have hone : qPochhammerInf (0 : ℂ) 0 = 1 := by
      simp [qPochhammerInf, tprod_one]
    simp [qGamma, h0, hone]
  · have hx : ∀ n : ℕ, q ^ ((1 : ℂ) + n) ≠ 1 := by
      intro n h
      have hpow : q ^ ((1 : ℂ) + n) = q ^ (n + 1) := by
        rw [add_comm, ← Nat.cast_one, ← Nat.cast_add, cpow_natCast]
      have hlt : ‖q ^ (n + 1)‖ < 1 := by
        rw [norm_pow]
        exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero n)
      rw [hpow] at h
      rw [h, norm_one] at hlt
      exact (lt_irrefl (1 : ℝ)) hlt
    have hrec := qGamma_add_one hq hq0 hx (x := 1)
    have hq1 : q ≠ 1 := by
      intro h
      rw [h, norm_one] at hq
      exact (lt_irrefl (1 : ℝ)) hq
    have hb : 1 - q ≠ 0 := sub_ne_zero.mpr fun h => hq1 h.symm
    have hsimp : (1 - q ^ (1 : ℂ)) / (1 - q) * qGamma q 1 = 1 := by
      simp [qGamma_one hq, cpow_one, hb]
    have : qGamma q ((1 : ℂ) + 1) = 1 := hrec.trans hsimp
    simpa [show (1 : ℂ) + 1 = 2 by ring] using this

/-- q-beta function, DLMF 5.18.11. -/
@[dlmf 5.18.E11]
def qBeta (q a b : ℂ) : ℂ :=
  qGamma q a * qGamma q b / qGamma q (a + b)

@[dlmf 5.18.E8]
theorem qGamma_mono_left {q r x : ℝ} (hq0 : 0 < q) (hqr : q < r) (hr1 : r < 1)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (qGamma q x).re < (qGamma r x).re := by
  sorry

/-- Strict decrease of the q-Gamma function in its base when `1 < x < 2`.
At `x = 2` the function is constant, so the upper restriction is essential. -/
@[dlmf 5.18.E9]
theorem qGamma_mono_right {q r x : ℝ} (hq0 : 0 < q) (hqr : q < r) (hr1 : r < 1)
    (hx : 1 < x) (hx2 : x < 2) :
    (qGamma r x).re < (qGamma q x).re := by
  sorry

@[dlmf 5.18.E10]
theorem tendsto_qGamma_one {x : ℝ} (hx : 0 < x) :
    Tendsto (fun q : ℝ => qGamma q x) (𝓝[<] (1 : ℝ)) (𝓝 (Real.Gamma x : ℂ)) := by
  sorry

end AAR.Gamma
