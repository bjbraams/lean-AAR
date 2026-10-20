/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.ModulusPhase

/-!
# Airy zeros and their common asymptotic coefficients, DLMF §9.9

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- The k-th negative real zero, ordered from zero towards negative infinity (k≥1). -/
def airyRealZero (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x < 0 ∧ f x = 0 ∧
    ({y : ℝ | x < y ∧ y < 0 ∧ f y = 0} : Set ℝ).ncard = k - 1)
/-- Negative zeros of Ai. -/
def airyAiZero : ℕ → ℝ := airyRealZero airyAiReal
/-- Negative zeros of Ai'. -/
def airyAiDerivZero : ℕ → ℝ := airyRealZero airyAiDerivReal
/-- Negative zeros of Bi. -/
def airyBiZero : ℕ → ℝ := airyRealZero airyBiReal
/-- Negative zeros of Bi'. -/
def airyBiDerivZero : ℕ → ℝ := airyRealZero airyBiDerivReal
/-- Zeros in the upper complex-zero sector of Bi or Bi'. -/
def airyUpperZeroSet (f : ℂ → ℂ) : Set ℂ := {z | π / 3 < arg z ∧ arg z < π / 2 ∧ f z = 0}
/-- Complex zeros ordered by increasing modulus; the specification theorem establishes existence. -/
def airyComplexZero (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  Classical.epsilon (fun z : ℂ => z ∈ airyUpperZeroSet f ∧
    ({w : ℂ | w ∈ airyUpperZeroSet f ∧ ‖w‖ < ‖z‖} : Set ℂ).ncard = k - 1)
/-- Upper-half-plane complex zeros of Bi. -/
def airyBiComplexZero : ℕ → ℂ := airyComplexZero airyBi
/-- Upper-half-plane complex zeros of Bi'. -/
def airyBiDerivComplexZero : ℕ → ℂ := airyComplexZero airyBiDeriv
/-- The continuous extension of the Ai zero index, via the unwrapped phase. -/
def airyAiZeroContinuous (k : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x ≤ 0 ∧ airyPhase x = k * π)
/-- The continuous extension of the Ai' zero index. -/
def airyAiDerivZeroContinuous (k : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x ≤ 0 ∧ airyDerivPhase x = (k - 1) * π)
/-- An all-order expansion in the common inverse even-power scale used in 9.9.18–9.9.21. -/
def HasAiryZeroExpansion (q : ℝ) (f t : ℕ → ℂ) (c : ℕ → ℂ) : Prop :=
  HasAsymptoticExpansion atTop (fun n k => t k ^ (-2 * (n : ℂ))) c
    (fun k => f k / t k ^ (q : ℂ))
/-- The real argument of the T,V pair at the (k+1)-st Ai zero. -/
def airyZeroArgument (offset : ℝ) (k : ℕ) : ℂ := (3 * π / 8 * (4 * (k + 1 : ℝ) - offset) : ℝ)
/-- The complex argument of the T,V and U,W pairs for Bi's upper-sector zeros. -/
def airyComplexZeroArgument (offset : ℝ) (k : ℕ) : ℂ := airyZeroArgument offset k + 3 * I * Real.log 2 / 4

/-- `Ai(x) → 0` as `x → +∞` on the real axis. -/
lemma tendsto_airyAiReal_atTop : Tendsto airyAiReal atTop (𝓝 0) := by
  have hv : Tendsto (fun x : ℝ => Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (1 / 4 : ℝ)))
      atTop (𝓝 0) :=
    (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_airyZeta).div_atTop
      ((tendsto_rpow_atTop (by norm_num)).const_mul_atTop
        (by have := Real.sqrt_pos.mpr Real.pi_pos; positivity))
  have hv' := (continuous_ofReal.tendsto 0).comp hv
  rw [ofReal_zero] at hv'
  have h := airyAi_isEquivalent.symm.tendsto_nhds hv'
  have h' := (continuous_re.tendsto 0).comp h
  rw [zero_re] at h'
  exact h'

/-- `Bi(x) > 0` for `x ≥ 0`. -/
lemma airyBiReal_pos {x : ℝ} (hx : 0 ≤ x) : 0 < airyBiReal x := by
  obtain ⟨r, hr, he⟩ := airyBi_ofReal_pos hx
  simp [airyBiReal, he, hr]

/-- `Ai(x) > 0` for `x ≥ 0`. -/
lemma airyAiReal_pos {x : ℝ} (hx : 0 ≤ x) : 0 < airyAiReal x := by
  obtain ⟨r, hr, he⟩ := airyAi_ofReal_pos hx
  simp [airyAiReal, he, hr]

/-- `Bi'(0) > 0`. -/
lemma airyBiDerivReal_zero_pos : 0 < airyBiDerivReal 0 := by
  have h := airyBiDeriv_zero
  rw [show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    ← Complex.ofReal_div] at h
  simp only [airyBiDerivReal, ofReal_zero, h, ofReal_re]
  have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
  positivity

/-- `Ai'(0) < 0`. -/
lemma airyAiDerivReal_zero_neg : airyAiDerivReal 0 < 0 := by
  have h := airyAiDeriv_zero
  rw [show (1 / 3 : ℂ) = ((1 / 3 : ℝ) : ℂ) by push_cast; ring, Complex.Gamma_ofReal,
    ← Complex.ofReal_mul, show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by simp, ← Complex.ofReal_div] at h
  simp only [airyAiDerivReal, ofReal_zero, h, ofReal_re]
  have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)
  have : 0 < (3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  apply div_neg_of_neg_of_pos (by norm_num) (by positivity)

/-- `((-1)^n)^2 = 1`. -/
lemma neg_one_pow_sq_real (n : ℕ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul]; simp

/-! ### Real zeros through a monotone phase -/

section PhaseZeros

variable {f g : ℝ → ℝ} {c : ℝ}

/-- Hypotheses describing the zeros of `f` as the level crossings `g = c + jπ` of a phase `g`
that decreases on `(-∞, 0]` from `g 0 ∈ (c, c + π)` to `+∞`. -/
structure PhaseZeroData (f g : ℝ → ℝ) (c : ℝ) : Prop where
  cont : Continuous g
  anti : StrictAntiOn g (Iic 0)
  tendsto : Tendsto g atBot atTop
  lt_zero : c < g 0
  zero_lt : g 0 < c + π
  zero_iff : ∀ x < 0, f x = 0 ↔ ∃ j : ℤ, g x = c + j * π
  neg : ∀ x, f x = 0 → x < 0

namespace PhaseZeroData

/-- Every level above `g 0` is attained on `(-∞, 0]`. -/
lemma exists_level (h : PhaseZeroData f g c) {L : ℝ} (hL : g 0 ≤ L) : ∃ x ≤ 0, g x = L := by
  obtain ⟨x0, hx0⟩ := (h.tendsto.eventually (eventually_ge_atTop L)).exists_forall_of_atBot
  set x1 := min x0 0
  have h1 : L ≤ g x1 := hx0 x1 (min_le_left _ _)
  obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc' (min_le_right x0 0) h.cont.continuousOn
    (mem_Icc.mpr ⟨hL, h1⟩)
  exact ⟨x, hx.2, hgx⟩

/-- A zero of `f` is negative and lies on a level `c + jπ` with `j ≥ 1`. -/
lemma level_of_zero (h : PhaseZeroData f g c) {x : ℝ} (hx : f x = 0) :
    x < 0 ∧ ∃ j : ℕ, 1 ≤ j ∧ g x = c + j * π := by
  have hneg := h.neg x hx
  obtain ⟨j, hj⟩ := (h.zero_iff x hneg).1 hx
  have hg0 : g 0 < g x := h.anti (mem_Iic.mpr hneg.le) (mem_Iic.mpr le_rfl) hneg
  have hπ := Real.pi_pos
  have hjpos : (0 : ℝ) < j := by
    by_contra hn; push Not at hn
    have := mul_nonpos_of_nonpos_of_nonneg hn hπ.le
    linarith [h.lt_zero]
  have hj1 : 1 ≤ j := by exact_mod_cast hjpos
  refine ⟨hneg, j.toNat, by omega, ?_⟩
  rw [hj]; congr 2
  have : ((j.toNat : ℤ) : ℝ) = (j : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
  exact_mod_cast this.symm

/-- A point of `(-∞, 0]` on a level `c + jπ`, `j ≥ 1`, is a negative zero of `f`. -/
lemma zero_of_level (h : PhaseZeroData f g c) {x : ℝ} (hx : x ≤ 0) {j : ℕ} (hj : 1 ≤ j)
    (hg : g x = c + j * π) : x < 0 ∧ f x = 0 := by
  have hπ := Real.pi_pos
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hx0 : x ≠ 0 := by
    rintro rfl
    have := h.zero_lt
    nlinarith
  have hlt : x < 0 := lt_of_le_of_ne hx hx0
  exact ⟨hlt, (h.zero_iff x hlt).2 ⟨j, by rw [hg]; norm_cast⟩⟩

/-- The level-`j` point. -/
noncomputable def pt (h : PhaseZeroData f g c) (j : ℕ) : ℝ :=
  Classical.choose (h.exists_level (le_max_right (c + j * π) (g 0)))

/-- The level-`j` point lies in `(-∞, 0]` on the level `c + jπ`. -/
lemma pt_spec (h : PhaseZeroData f g c) {j : ℕ} (hj : 1 ≤ j) :
    h.pt j ≤ 0 ∧ g (h.pt j) = c + j * π := by
  have hs := Classical.choose_spec (h.exists_level (le_max_right (c + j * π) (g 0)))
  refine ⟨hs.1, ?_⟩
  rw [pt, hs.2, max_eq_left]
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have := h.zero_lt; have := Real.pi_pos; nlinarith

/-- Uniqueness of the level-`j` point. -/
lemma eq_pt (h : PhaseZeroData f g c) {x : ℝ} (hx : x ≤ 0) {j : ℕ} (hj : 1 ≤ j)
    (hg : g x = c + j * π) : x = h.pt j :=
  h.anti.injOn (mem_Iic.mpr hx) (mem_Iic.mpr (h.pt_spec hj).1) (by rw [hg, (h.pt_spec hj).2])

/-- The level points decrease with the level. -/
lemma pt_lt_pt (h : PhaseZeroData f g c) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) :
    h.pt j < h.pt i := by
  have hj : 1 ≤ j := by omega
  by_contra hn; push Not at hn
  have h1 := h.anti.antitoneOn (mem_Iic.mpr (h.pt_spec hi).1) (mem_Iic.mpr (h.pt_spec hj).1) hn
  rw [(h.pt_spec hi).2, (h.pt_spec hj).2] at h1
  have : (i : ℝ) < j := by exact_mod_cast hij
  have := Real.pi_pos
  nlinarith

/-- Exactly `k - 1` zeros lie strictly between the level-`k` point and `0`. -/
lemma ncard_eq (h : PhaseZeroData f g c) {k : ℕ} (hk : 1 ≤ k) :
    ({y : ℝ | h.pt k < y ∧ y < 0 ∧ f y = 0} : Set ℝ).ncard = k - 1 := by
  have hS : ({y : ℝ | h.pt k < y ∧ y < 0 ∧ f y = 0} : Set ℝ) =
      h.pt '' (↑(Finset.Ico 1 k) : Set ℕ) := by
    ext y
    simp only [mem_ofPred_eq, mem_image, Finset.coe_Ico, mem_Ico]
    constructor
    · rintro ⟨h1, h2, h3⟩
      obtain ⟨-, j, hj, hgj⟩ := h.level_of_zero h3
      refine ⟨j, ⟨hj, ?_⟩, (h.eq_pt h2.le hj hgj).symm⟩
      by_contra hn; push Not at hn
      have := h.anti.antitoneOn (mem_Iic.mpr (h.pt_spec hk).1) (mem_Iic.mpr h2.le) h1.le
      rw [(h.pt_spec hk).2, hgj] at this
      have hkj : (k : ℝ) ≤ j := by exact_mod_cast hn
      have := h.anti (mem_Iic.mpr (h.pt_spec hk).1) (mem_Iic.mpr h2.le) h1
      rw [(h.pt_spec hk).2, hgj] at this
      have := Real.pi_pos
      nlinarith
    · rintro ⟨j, ⟨hj, hjk⟩, rfl⟩
      exact ⟨h.pt_lt_pt hj hjk, (h.zero_of_level (h.pt_spec hj).1 hj (h.pt_spec hj).2)⟩
  have hinj : Set.InjOn h.pt (↑(Finset.Ico 1 k) : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_Ico, mem_Ico] at hi hj
    rcases lt_trichotomy i j with hl | rfl | hl
    · exact absurd hij (h.pt_lt_pt hi.1 hl).ne'
    · rfl
    · exact absurd hij (h.pt_lt_pt hj.1 hl).ne
  rw [hS, hinj.ncard_image, Set.ncard_coe_finset, Nat.card_Ico]

/-- The `k`-th ordered zero is the level-`k` point. -/
lemma airyRealZero_eq (h : PhaseZeroData f g c) {k : ℕ} (hk : 1 ≤ k) :
    airyRealZero f k = h.pt k := by
  set P : ℝ → Prop := fun x => x < 0 ∧ f x = 0 ∧
      ({y : ℝ | x < y ∧ y < 0 ∧ f y = 0} : Set ℝ).ncard = k - 1 with hPdef
  have hP : P (h.pt k) := by
    have := h.zero_of_level (h.pt_spec hk).1 hk (h.pt_spec hk).2
    exact ⟨this.1, this.2, h.ncard_eq hk⟩
  have hε : P (Classical.epsilon P) := Classical.epsilon_spec ⟨_, hP⟩
  change Classical.epsilon P = _
  set x := Classical.epsilon P
  obtain ⟨hx0, hfx, hcard⟩ := hε
  obtain ⟨-, j, hj, hgj⟩ := h.level_of_zero hfx
  have hxj := h.eq_pt hx0.le hj hgj
  rw [hxj, h.ncard_eq hj] at hcard
  have : j = k := by omega
  rw [hxj, this]

/-- The ordered-zero specification, with the phase value at the zero. -/
lemma spec (h : PhaseZeroData f g c) {k : ℕ} (hk : 1 ≤ k) :
    airyRealZero f k < 0 ∧ f (airyRealZero f k) = 0 ∧
      ({y : ℝ | airyRealZero f k < y ∧ y < 0 ∧ f y = 0} : Set ℝ).ncard = k - 1 ∧
      g (airyRealZero f k) = c + k * π := by
  rw [h.airyRealZero_eq hk]
  have := h.zero_of_level (h.pt_spec hk).1 hk (h.pt_spec hk).2
  exact ⟨this.1, this.2, h.ncard_eq hk, (h.pt_spec hk).2⟩

/-- The ordered zeros decrease and exhaust the zeros of `f`. -/
lemma enumeration (h : PhaseZeroData f g c) :
    StrictAntiOn (airyRealZero f) (Ici 1) ∧
      ∀ x : ℝ, f x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyRealZero f k = x := by
  refine ⟨fun i hi j hj hij => ?_, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · rw [h.airyRealZero_eq hi, h.airyRealZero_eq hj]; exact h.pt_lt_pt hi hij
  · obtain ⟨hx0, j, hj, hgj⟩ := h.level_of_zero hx
    exact ⟨j, hj, by rw [h.airyRealZero_eq hj, h.eq_pt hx0.le hj hgj]⟩
  · rintro ⟨k, hk, rfl⟩; exact (h.spec hk).2.1

/-- The zero set of `f` is infinite. -/
lemma infinite (h : PhaseZeroData f g c) : Set.Infinite {x : ℝ | f x = 0} := by
  have hinj : Set.InjOn (airyRealZero f) (Ici 1) := (h.enumeration).1.injOn
  have : airyRealZero f '' (Ici 1) ⊆ {x : ℝ | f x = 0} := by
    rintro _ ⟨k, hk, rfl⟩; exact (h.spec hk).2.1
  exact Set.Infinite.mono this ((Set.Ici_infinite 1).image hinj)

end PhaseZeroData

end PhaseZeros

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyAi_real_zeros_negative {x : ℝ} (hx : airyAiReal x = 0) :
    x < 0 := by
  by_contra hn
  obtain ⟨r, hr, he⟩ := airyAi_ofReal_pos (not_lt.mp hn)
  have hx' : (airyAi x).re = 0 := hx
  rw [he] at hx'
  simp only [ofReal_re] at hx'
  linarith


/-- The zeros of `Ai` are the crossings `θ = jπ`. -/
lemma phaseZeroData_airyAi : PhaseZeroData airyAiReal airyPhase 0 := by
  have hπ := Real.pi_pos
  have h0 : airyPhase 0 = π / 6 := by simp [airyPhase]
  refine ⟨airyPhase_continuous, airy_phase_monotone, tendsto_airyPhase_atBot, ?_, ?_, ?_,
    fun x hx => airyAi_real_zeros_negative hx⟩
  · rw [h0]; positivity
  · rw [h0]; linarith
  · intro x _
    rw [airyAiReal_eq_modulus_sin, mul_eq_zero, or_iff_right (airyModulus_pos x).ne',
      Real.sin_eq_zero_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n, by rw [← hn]; ring⟩, fun ⟨n, hn⟩ => ⟨n, by rw [hn]; ring⟩⟩

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyAi_infinite_real_zeros  :
    Set.Infinite {x : ℝ | airyAiReal x = 0} := by
  exact phaseZeroData_airyAi.infinite

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyAiZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyAiZero k < 0 ∧ airyAiReal (airyAiZero k) = 0 ∧
      ({y : ℝ | airyAiZero k < y ∧ y < 0 ∧ airyAiReal y = 0} : Set ℝ).ncard = k - 1 := by
  obtain ⟨h1, h2, h3, -⟩ := phaseZeroData_airyAi.spec hk
  exact ⟨h1, h2, h3⟩

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyAiZero_enumeration  :
    StrictAntiOn airyAiZero (Ici 1) ∧ ∀ x : ℝ, airyAiReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyAiZero k = x := by
  exact phaseZeroData_airyAi.enumeration

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyAiDeriv_real_zeros_negative {x : ℝ} (hx : airyAiDerivReal x = 0) :
    x < 0 := by
  by_contra hn
  replace hn := not_lt.mp hn
  have hcont : Continuous airyAiDerivReal := continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_airyAiDerivReal t).continuousAt
  have hmono : StrictMonoOn airyAiDerivReal (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) hcont.continuousOn fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hasDerivAt_airyAiDerivReal t).deriv]
    exact mul_pos ht (airyAiReal_pos ht.le)
  have hpos : ∀ t, x < t → 0 < airyAiDerivReal t := fun t ht => by
    have := hmono (mem_Ici.mpr hn) (mem_Ici.mpr (hn.trans ht.le)) ht
    linarith
  have hAi : MonotoneOn airyAiReal (Ici x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici x)
      (continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_airyAiReal t).continuousAt).continuousOn
      (fun t _ => (hasDerivAt_airyAiReal t).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hasDerivAt_airyAiReal t).deriv]
    exact (hpos t ht).le
  have h0 := airyAiReal_pos hn
  obtain ⟨t, ht1, ht2⟩ := ((tendsto_order.1 tendsto_airyAiReal_atTop).2 _ h0).and
    (eventually_ge_atTop x) |>.exists
  have := hAi (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht2) ht2
  linarith


/-- The zeros of `Ai'` are the crossings `φ = (j - 1)π`. -/
lemma phaseZeroData_airyAiDeriv : PhaseZeroData airyAiDerivReal airyDerivPhase (-π) := by
  have hπ := Real.pi_pos
  have h0 : airyDerivPhase 0 = -π / 6 := by simp [airyDerivPhase]
  refine ⟨airyDerivPhase_continuous, airy_derivPhase_monotone, tendsto_airyDerivPhase_atBot,
    ?_, ?_, ?_, fun x hx => airyAiDeriv_real_zeros_negative hx⟩
  · rw [h0]; linarith
  · rw [h0]; linarith
  · intro x _
    rw [airyAiDerivReal_eq_modulus_sin, mul_eq_zero, or_iff_right (airyDerivModulus_pos x).ne',
      Real.sin_eq_zero_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n + 1, by rw [← hn]; push_cast; ring⟩,
      fun ⟨n, hn⟩ => ⟨n - 1, by rw [hn]; push_cast; ring⟩⟩

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyAiDeriv_infinite_real_zeros  :
    Set.Infinite {x : ℝ | airyAiDerivReal x = 0} := by
  exact phaseZeroData_airyAiDeriv.infinite

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyAiDerivZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyAiDerivZero k < 0 ∧ airyAiDerivReal (airyAiDerivZero k) = 0 ∧
      ({y : ℝ | airyAiDerivZero k < y ∧ y < 0 ∧ airyAiDerivReal y = 0} : Set ℝ).ncard = k - 1 := by
  obtain ⟨h1, h2, h3, -⟩ := phaseZeroData_airyAiDeriv.spec hk
  exact ⟨h1, h2, h3⟩

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyAiDerivZero_enumeration  :
    StrictAntiOn airyAiDerivZero (Ici 1) ∧ ∀ x : ℝ, airyAiDerivReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyAiDerivZero k = x := by
  exact phaseZeroData_airyAiDeriv.enumeration

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyBi_real_zeros_negative {x : ℝ} (hx : airyBiReal x = 0) :
    x < 0 := by
  by_contra hn
  obtain ⟨r, hr, he⟩ := airyBi_ofReal_pos (not_lt.mp hn)
  have hx' : (airyBi x).re = 0 := hx
  rw [he] at hx'
  simp only [ofReal_re] at hx'
  linarith


/-- The zeros of `Bi` are the crossings `θ = (j - 1/2)π`. -/
lemma phaseZeroData_airyBi : PhaseZeroData airyBiReal airyPhase (-(π / 2)) := by
  have hπ := Real.pi_pos
  have h0 : airyPhase 0 = π / 6 := by simp [airyPhase]
  refine ⟨airyPhase_continuous, airy_phase_monotone, tendsto_airyPhase_atBot, ?_, ?_, ?_,
    fun x hx => airyBi_real_zeros_negative hx⟩
  · rw [h0]; linarith
  · rw [h0]; linarith
  · intro x _
    rw [airyBiReal_eq_modulus_cos, mul_eq_zero, or_iff_right (airyModulus_pos x).ne',
      Real.cos_eq_zero_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n + 1, by rw [hn]; push_cast; ring⟩,
      fun ⟨n, hn⟩ => ⟨n - 1, by rw [hn]; push_cast; ring⟩⟩

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyBi_infinite_real_zeros  :
    Set.Infinite {x : ℝ | airyBiReal x = 0} := by
  exact phaseZeroData_airyBi.infinite

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyBiZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiZero k < 0 ∧ airyBiReal (airyBiZero k) = 0 ∧
      ({y : ℝ | airyBiZero k < y ∧ y < 0 ∧ airyBiReal y = 0} : Set ℝ).ncard = k - 1 := by
  obtain ⟨h1, h2, h3, -⟩ := phaseZeroData_airyBi.spec hk
  exact ⟨h1, h2, h3⟩

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyBiZero_enumeration  :
    StrictAntiOn airyBiZero (Ici 1) ∧ ∀ x : ℝ, airyBiReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyBiZero k = x := by
  exact phaseZeroData_airyBi.enumeration

/-- All real zeros are negative, DLMF §9.9(i). -/
theorem airyBiDeriv_real_zeros_negative {x : ℝ} (hx : airyBiDerivReal x = 0) :
    x < 0 := by
  by_contra hn
  replace hn := not_lt.mp hn
  have hmono : MonotoneOn airyBiDerivReal (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_airyBiDerivReal t).continuousAt).continuousOn
      (fun t _ => (hasDerivAt_airyBiDerivReal t).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hasDerivAt_airyBiDerivReal t).deriv]
    exact mul_nonneg ht.le (airyBiReal_pos ht.le).le
  have := hmono ((mem_Ici.mpr le_rfl)) hn hn
  linarith [airyBiDerivReal_zero_pos]


/-- The zeros of `Bi'` are the crossings `φ = (j - 1/2)π`. -/
lemma phaseZeroData_airyBiDeriv : PhaseZeroData airyBiDerivReal airyDerivPhase (-(π / 2)) := by
  have hπ := Real.pi_pos
  have h0 : airyDerivPhase 0 = -π / 6 := by simp [airyDerivPhase]
  refine ⟨airyDerivPhase_continuous, airy_derivPhase_monotone, tendsto_airyDerivPhase_atBot,
    ?_, ?_, ?_, fun x hx => airyBiDeriv_real_zeros_negative hx⟩
  · rw [h0]; linarith
  · rw [h0]; linarith
  · intro x _
    rw [airyBiDerivReal_eq_modulus_cos, mul_eq_zero, or_iff_right (airyDerivModulus_pos x).ne',
      Real.cos_eq_zero_iff]
    exact ⟨fun ⟨n, hn⟩ => ⟨n + 1, by rw [hn]; push_cast; ring⟩,
      fun ⟨n, hn⟩ => ⟨n - 1, by rw [hn]; push_cast; ring⟩⟩

/-- Infinitely many real zeros, DLMF §9.9(i). -/
theorem airyBiDeriv_infinite_real_zeros  :
    Set.Infinite {x : ℝ | airyBiDerivReal x = 0} := by
  exact phaseZeroData_airyBiDeriv.infinite

/-- The ordered real-zero specification in DLMF §9.9(i). -/
theorem airyBiDerivZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiDerivZero k < 0 ∧ airyBiDerivReal (airyBiDerivZero k) = 0 ∧
      ({y : ℝ | airyBiDerivZero k < y ∧ y < 0 ∧ airyBiDerivReal y = 0} : Set ℝ).ncard = k - 1 := by
  obtain ⟨h1, h2, h3, -⟩ := phaseZeroData_airyBiDeriv.spec hk
  exact ⟨h1, h2, h3⟩

/-- The real zeros are exhausted in their stated order, DLMF §9.9(i). -/
theorem airyBiDerivZero_enumeration  :
    StrictAntiOn airyBiDerivZero (Ici 1) ∧ ∀ x : ℝ, airyBiDerivReal x = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ airyBiDerivZero k = x := by
  exact phaseZeroData_airyBiDeriv.enumeration

/-- Ai and Ai' have no nonreal zeros, DLMF §9.9(i). -/
theorem airyAi_complex_zeros_real {z : ℂ} (hz : airyAi z = 0) :
    z.im = 0 ∧ z.re < 0 := by
  sorry

/-- Ai and Ai' have no nonreal zeros, DLMF §9.9(i). -/
theorem airyAiDeriv_complex_zeros_real {z : ℂ} (hz : airyAiDeriv z = 0) :
    z.im = 0 ∧ z.re < 0 := by
  sorry

/-- The nonreal-zero sectors of Bi and Bi', DLMF §9.9(i). -/
theorem airyBi_complex_zeros_sector {z : ℂ} (hz : airyBi z = 0) (him : z.im ≠ 0) :
    π / 3 < |arg z| ∧ |arg z| < π / 2 := by
  sorry

/-- Infinitely many zeros in the upper sector, DLMF §9.9(i). -/
theorem airyBi_infinite_complex_zeros  :
    Set.Infinite (airyUpperZeroSet airyBi) := by
  sorry

/-- The upper-sector complex-zero specification, DLMF §9.9(i). -/
theorem airyBiComplexZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiComplexZero k ∈ airyUpperZeroSet airyBi := by
  sorry

/-- Complex-zero enumeration in increasing modulus, DLMF §9.9(i). -/
theorem airyBiComplexZero_enumeration  :
    StrictMonoOn (fun k => ‖airyBiComplexZero k‖) (Ici 1) ∧
      ∀ z ∈ airyUpperZeroSet airyBi, ∃ k : ℕ, 1 ≤ k ∧ airyBiComplexZero k = z := by
  sorry

/-- The nonreal-zero sectors of Bi and Bi', DLMF §9.9(i). -/
theorem airyBiDeriv_complex_zeros_sector {z : ℂ} (hz : airyBiDeriv z = 0) (him : z.im ≠ 0) :
    π / 3 < |arg z| ∧ |arg z| < π / 2 := by
  sorry

/-- Infinitely many zeros in the upper sector, DLMF §9.9(i). -/
theorem airyBiDeriv_infinite_complex_zeros  :
    Set.Infinite (airyUpperZeroSet airyBiDeriv) := by
  sorry

/-- The upper-sector complex-zero specification, DLMF §9.9(i). -/
theorem airyBiDerivComplexZero_spec {k : ℕ} (hk : 1 ≤ k) :
    airyBiDerivComplexZero k ∈ airyUpperZeroSet airyBiDeriv := by
  sorry

/-- Complex-zero enumeration in increasing modulus, DLMF §9.9(i). -/
theorem airyBiDerivComplexZero_enumeration  :
    StrictMonoOn (fun k => ‖airyBiDerivComplexZero k‖) (Ici 1) ∧
      ∀ z ∈ airyUpperZeroSet airyBiDeriv, ∃ k : ℕ, 1 ≤ k ∧ airyBiDerivComplexZero k = z := by
  sorry

/-- airyAiZero phase (DLMF 9.9.1). -/
@[dlmf 9.9.E1]
theorem airyAiZero_phase {k : ℕ} (hk : 1 ≤ k) :
    airyPhase (airyAiZero k) = k * π ∧ airyDerivPhase (airyAiDerivZero (k + 1)) = k * π := by
  refine ⟨?_, ?_⟩
  · rw [airyAiZero, (phaseZeroData_airyAi.spec hk).2.2.2, zero_add]
  · rw [airyAiDerivZero, (phaseZeroData_airyAiDeriv.spec (by omega : 1 ≤ k + 1)).2.2.2]
    push_cast; ring

/-- airyBiZero phase (DLMF 9.9.2). -/
@[dlmf 9.9.E2]
theorem airyBiZero_phase {k : ℕ} (hk : 1 ≤ k) :
    airyPhase (airyBiZero k) = ((k : ℝ) - 1 / 2) * π ∧
      airyDerivPhase (airyBiDerivZero k) = ((k : ℝ) - 1 / 2) * π := by
  refine ⟨?_, ?_⟩
  · rw [airyBiZero, (phaseZeroData_airyBi.spec hk).2.2.2]; ring
  · rw [airyBiDerivZero, (phaseZeroData_airyBiDeriv.spec hk).2.2.2]; ring

/-- airyAiZero value (DLMF 9.9.3). -/
@[dlmf 9.9.E3]
theorem airyAiZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyAiDeriv (airyAiZero k) = (-1 : ℂ) ^ (k - 1) / (π * airyModulus (airyAiZero k)) := by
  obtain ⟨-, h0, -, hθ⟩ := phaseZeroData_airyAi.spec hk
  set x := airyRealZero airyAiReal k
  change airyAiDeriv x = _
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hW := wronskian_airyReal x
  have hb := airyBiReal_eq_modulus_cos x
  rw [hθ, zero_add, Real.cos_nat_mul_pi] at hb
  rw [h0, hb] at hW
  have hM := (airyModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hr : airyAiDerivReal x = (-1) ^ n / (π * airyModulus x) := by
    rw [eq_div_iff hπ] at hW
    rw [eq_div_iff (mul_ne_zero hπ hM)]
    linear_combination (-1 : ℝ) ^ n * hW - (airyAiDerivReal x * airyModulus x * π) *
      neg_one_pow_sq_real n
  rw [airyAiDeriv_ofReal_eq, hr, Nat.add_sub_cancel]
  push_cast; rfl

/-- airyBiZero value (DLMF 9.9.3). -/
@[dlmf 9.9.E3]
theorem airyBiZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyBiDeriv (airyBiZero k) = (-1 : ℂ) ^ (k - 1) / (π * airyModulus (airyBiZero k)) := by
  obtain ⟨-, h0, -, hθ⟩ := phaseZeroData_airyBi.spec hk
  set x := airyRealZero airyBiReal k
  change airyBiDeriv x = _
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hW := wronskian_airyReal x
  have ha := airyAiReal_eq_modulus_sin x
  rw [hθ, show -(π / 2) + ((n + 1 : ℕ) : ℝ) * π = n * π + π / 2 by push_cast; ring,
    Real.sin_add_pi_div_two, Real.cos_nat_mul_pi] at ha
  rw [h0, ha] at hW
  have hM := (airyModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hr : airyBiDerivReal x = (-1) ^ n / (π * airyModulus x) := by
    rw [eq_div_iff hπ] at hW
    rw [eq_div_iff (mul_ne_zero hπ hM)]
    linear_combination (-1 : ℝ) ^ n * hW - (airyBiDerivReal x * airyModulus x * π) *
      neg_one_pow_sq_real n
  rw [airyBiDeriv_ofReal_eq, hr, Nat.add_sub_cancel]
  push_cast; rfl

/-- airyAiDerivZero value (DLMF 9.9.4). -/
@[dlmf 9.9.E4]
theorem airyAiDerivZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyAi (airyAiDerivZero k) = (-1 : ℂ) ^ (k - 1) / (π * airyDerivModulus (airyAiDerivZero k)) := by
  obtain ⟨-, h0, -, hθ⟩ := phaseZeroData_airyAiDeriv.spec hk
  set x := airyRealZero airyAiDerivReal k
  change airyAi x = _
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hW := wronskian_airyReal x
  have hb := airyBiDerivReal_eq_modulus_cos x
  rw [hθ, show -π + ((n + 1 : ℕ) : ℝ) * π = n * π by push_cast; ring, Real.cos_nat_mul_pi] at hb
  rw [h0, hb] at hW
  have hM := (airyDerivModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hr : airyAiReal x = (-1) ^ n / (π * airyDerivModulus x) := by
    rw [eq_div_iff hπ] at hW
    rw [eq_div_iff (mul_ne_zero hπ hM)]
    linear_combination (-1 : ℝ) ^ n * hW - (airyAiReal x * airyDerivModulus x * π) *
      neg_one_pow_sq_real n
  rw [airyAi_ofReal_eq, hr, Nat.add_sub_cancel]
  push_cast; rfl

/-- airyBiDerivZero value (DLMF 9.9.4). -/
@[dlmf 9.9.E4]
theorem airyBiDerivZero_value {k : ℕ} (hk : 1 ≤ k) :
    airyBi (airyBiDerivZero k) = (-1 : ℂ) ^ (k) / (π * airyDerivModulus (airyBiDerivZero k)) := by
  obtain ⟨-, h0, -, hθ⟩ := phaseZeroData_airyBiDeriv.spec hk
  set x := airyRealZero airyBiDerivReal k
  change airyBi x = _
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hW := wronskian_airyReal x
  have ha := airyAiDerivReal_eq_modulus_sin x
  rw [hθ, show -(π / 2) + ((n + 1 : ℕ) : ℝ) * π = n * π + π / 2 by push_cast; ring,
    Real.sin_add_pi_div_two, Real.cos_nat_mul_pi] at ha
  rw [h0, ha] at hW
  have hM := (airyDerivModulus_pos x).ne'
  have hπ := Real.pi_ne_zero
  have hr : airyBiReal x = (-1) ^ (n + 1) / (π * airyDerivModulus x) := by
    rw [eq_div_iff hπ] at hW
    rw [eq_div_iff (mul_ne_zero hπ hM)]
    linear_combination (-(-1 : ℝ) ^ n) * hW - (airyBiReal x * airyDerivModulus x * π) *
      neg_one_pow_sq_real n
  rw [airyBi_ofReal_eq, hr]
  push_cast; rfl

/-- Differentiability of the continuous-index level function `t ↦ g⁻¹((t + d)π)` of a
decreasing phase `g` on `(-∞, 0]`. -/
lemma hasDerivAt_phaseLevel {g : ℝ → ℝ} {g' d t₀ : ℝ} (hgc : Continuous g)
    (hanti : StrictAntiOn g (Iic 0)) (htend : Tendsto g atBot atTop)
    (ht₀ : g 0 < (t₀ + d) * π)
    (hd : HasDerivAt g g' (Classical.epsilon fun x : ℝ => x ≤ 0 ∧ g x = (t₀ + d) * π))
    (hg' : g' ≠ 0) :
    HasDerivAt (fun t : ℝ => Classical.epsilon fun x : ℝ => x ≤ 0 ∧ g x = (t + d) * π)
      (π / g') t₀ := by
  have hπ := Real.pi_pos
  set α : ℝ → ℝ := fun t => Classical.epsilon fun x : ℝ => x ≤ 0 ∧ g x = (t + d) * π with hα
  set U : Set ℝ := {t | g 0 < (t + d) * π} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const ((continuous_id.add continuous_const).mul
    continuous_const)
  have hex : ∀ t ∈ U, ∃ x ≤ 0, g x = (t + d) * π := by
    intro t ht
    obtain ⟨x0, hx0⟩ := (htend.eventually (eventually_ge_atTop ((t + d) * π))).exists_forall_of_atBot
    obtain ⟨x, hx, hgx⟩ := intermediate_value_Icc' (min_le_right x0 0) hgc.continuousOn
      (mem_Icc.mpr ⟨(ht : g 0 < _).le, hx0 _ (min_le_left _ _)⟩)
    exact ⟨x, hx.2, hgx⟩
  have hspec : ∀ t ∈ U, α t ≤ 0 ∧ g (α t) = (t + d) * π := fun t ht =>
    Classical.epsilon_spec (hex t ht)
  have hneg : ∀ t ∈ U, α t < 0 := fun t ht => by
    refine lt_of_le_of_ne (hspec t ht).1 fun h0 => ?_
    have := (hspec t ht).2; rw [h0] at this; exact absurd this (ht : g 0 < _).ne
  have hmono : MonotoneOn (fun t => -α t) U := by
    intro t₁ h₁ t₂ h₂ h12
    simp only [neg_le_neg_iff]
    by_contra hn; push Not at hn
    have := hanti (mem_Iic.mpr (hspec t₁ h₁).1) (mem_Iic.mpr (hspec t₂ h₂).1) hn
    rw [(hspec t₁ h₁).2, (hspec t₂ h₂).2] at this
    nlinarith
  have himage : (fun t => -α t) '' U = Ioi 0 := by
    ext y
    simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨t, ht, rfl⟩; linarith [hneg t ht]
    · intro hy
      have hgy : g 0 < g (-y) := hanti (mem_Iic.mpr (by linarith)) (mem_Iic.mpr le_rfl)
        (by linarith)
      set t := g (-y) / π - d
      have htU : t ∈ U := by
        show g 0 < (t + d) * π
        simp only [t]; field_simp; simpa using hgy
      refine ⟨t, htU, ?_⟩
      have h1 := hspec t htU
      have h2 : g (-y) = (t + d) * π := by simp only [t]; field_simp; ring
      have := hanti.injOn (mem_Iic.mpr h1.1) (mem_Iic.mpr (by linarith : -y ≤ 0))
        (h1.2.trans h2.symm)
      linarith
  have hcont : ContinuousAt α t₀ := by
    have h := continuousAt_of_monotoneOn_of_image_mem_nhds hmono (hUo.mem_nhds ht₀)
      (by rw [himage]; exact Ioi_mem_nhds (by linarith [hneg t₀ ht₀]))
    simpa using h.neg
  have hf : HasDerivAt (fun x => g x / π - d) (g' / π) (α t₀) := (hd.div_const π).sub_const d
  have := HasDerivAt.of_local_left_inverse hcont hf (div_ne_zero hg' hπ.ne')
    (Filter.mem_of_superset (hUo.mem_nhds ht₀) fun t ht => by
      simp only [mem_ofPred_eq, (hspec t ht).2]; field_simp; ring)
  simpa [inv_div] using this

/-- `(r²)^{-1/2} = r⁻¹` as a complex power, for `r > 0`. -/
lemma ofReal_sq_cpow_neg_half {r : ℝ} (hr : 0 < r) :
    ((r ^ 2 : ℝ) : ℂ) ^ (-1 / 2 : ℂ) = ((r⁻¹ : ℝ) : ℂ) := by
  rw [show (-1 / 2 : ℂ) = ((-1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity)]
  congr 1
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hr.le]

/-- Continuous-index interpolation used in DLMF §9.9(iii). -/
theorem airyAiZeroContinuous_natCast {k : ℕ} (hk : 1 ≤ k) :
    airyAiZeroContinuous k = airyAiZero k := by
  obtain ⟨h1, -, -, hθ⟩ := phaseZeroData_airyAi.spec hk
  have hP : airyAiZero k ≤ 0 ∧ airyPhase (airyAiZero k) = k * π := ⟨h1.le, by
    rw [airyAiZero, hθ, zero_add]⟩
  have hε := Classical.epsilon_spec (p := fun x : ℝ => x ≤ 0 ∧ airyPhase x = k * π) ⟨_, hP⟩
  exact airy_phase_monotone.injOn hε.1 hP.1 (hε.2.trans hP.2.symm)

/-- airyAiZeroContinuous derivative value (DLMF 9.9.5). -/
@[dlmf 9.9.E5]
theorem airyAiZeroContinuous_derivative_value {k : ℕ} (hk : 1 ≤ k) :
    airyAiDeriv (airyAiZero k) = (-1 : ℂ) ^ (k - 1) *
      ((-deriv airyAiZeroContinuous k : ℝ) : ℂ) ^ (-1 / 2 : ℂ) := by
  have hπ := Real.pi_pos
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfun : airyAiZeroContinuous =
      fun t : ℝ => Classical.epsilon fun x : ℝ => x ≤ 0 ∧ airyPhase x = (t + 0) * π := by
    funext t; simp only [add_zero]; rfl
  have hnat := airyAiZeroContinuous_natCast hk
  have hd := hasDerivAt_phaseLevel (d := 0) (t₀ := k) airyPhase_continuous airy_phase_monotone
    tendsto_airyPhase_atBot (by simp [airyPhase]; nlinarith)
    (hasDerivAt_airyPhase _)
    (neg_ne_zero.mpr (one_div_pos.mpr (mul_pos hπ (pow_pos (airyModulus_pos _) 2))).ne')
  have hε : (Classical.epsilon fun x : ℝ => x ≤ 0 ∧ airyPhase x = ((k : ℝ) + 0) * π) =
      airyAiZero k := by rw [← hnat, hfun]
  rw [← hfun, hε] at hd
  rw [hd.deriv, airyAiZero_value hk]
  have hM := airyModulus_pos (airyAiZero k)
  rw [show -(π / -(1 / (π * airyModulus (airyAiZero k) ^ 2))) =
      (π * airyModulus (airyAiZero k)) ^ 2 by field_simp,
    ofReal_sq_cpow_neg_half (by positivity)]
  push_cast
  ring

/-- Continuous-index interpolation used in DLMF §9.9(iii). -/
theorem airyAiDerivZeroContinuous_natCast {k : ℕ} (hk : 1 ≤ k) :
    airyAiDerivZeroContinuous k = airyAiDerivZero k := by
  obtain ⟨h1, -, -, hθ⟩ := phaseZeroData_airyAiDeriv.spec hk
  have hP : airyAiDerivZero k ≤ 0 ∧ airyDerivPhase (airyAiDerivZero k) = (k - 1) * π := ⟨h1.le, by
    rw [airyAiDerivZero, hθ]; ring⟩
  have hε := Classical.epsilon_spec
    (p := fun x : ℝ => x ≤ 0 ∧ airyDerivPhase x = ((k : ℝ) - 1) * π) ⟨_, hP⟩
  exact airy_derivPhase_monotone.injOn hε.1 hP.1 (hε.2.trans hP.2.symm)

/-- airyAiDerivZeroContinuous derivative value (DLMF 9.9.5). -/
@[dlmf 9.9.E5]
theorem airyAiDerivZeroContinuous_derivative_value {k : ℕ} (hk : 1 ≤ k) :
    airyAi (airyAiDerivZero k) = (-1 : ℂ) ^ (k - 1) *
      ((airyAiDerivZero k * deriv airyAiDerivZeroContinuous k : ℝ) : ℂ) ^ (-1 / 2 : ℂ) := by
  have hπ := Real.pi_pos
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hfun : airyAiDerivZeroContinuous =
      fun t : ℝ => Classical.epsilon fun x : ℝ => x ≤ 0 ∧ airyDerivPhase x = (t + -1) * π := by
    funext t; simp only [← sub_eq_add_neg]; rfl
  have hnat := airyAiDerivZeroContinuous_natCast hk
  have hneg := (airyAiDerivZero_spec hk).1
  have hε : (Classical.epsilon fun x : ℝ => x ≤ 0 ∧ airyDerivPhase x = ((k : ℝ) + -1) * π) =
      airyAiDerivZero k := by rw [← hnat, hfun]
  have hd := hasDerivAt_phaseLevel (d := -1) (t₀ := k) airyDerivPhase_continuous
    airy_derivPhase_monotone tendsto_airyDerivPhase_atBot
    (by simp [airyDerivPhase]; nlinarith) (hasDerivAt_airyDerivPhase _)
    (by
      rw [hε]
      have := airyDerivModulus_pos (airyAiDerivZero k)
      exact div_ne_zero hneg.ne (by positivity))
  rw [← hfun, hε] at hd
  rw [hd.deriv, airyAiDerivZero_value hk]
  have hM := airyDerivModulus_pos (airyAiDerivZero k)
  rw [show airyAiDerivZero k * (π / (airyAiDerivZero k / (π * airyDerivModulus (airyAiDerivZero k) ^ 2))) =
      (π * airyDerivModulus (airyAiDerivZero k)) ^ 2 by
        have := hneg.ne; field_simp,
    ofReal_sq_cpow_neg_half (by positivity)]
  push_cast
  ring

/-- The common all-order T,U,V,W expansions, including every printed coefficient and real/complex zero family in DLMF 9.9.6–9.9.21 (DLMF 9.9.18). -/
@[dlmf 9.9.E6, dlmf 9.9.E7, dlmf 9.9.E8, dlmf 9.9.E9, dlmf 9.9.E10, dlmf 9.9.E11, dlmf 9.9.E12, dlmf 9.9.E13, dlmf 9.9.E14, dlmf 9.9.E15, dlmf 9.9.E16, dlmf 9.9.E17, dlmf 9.9.E18, dlmf 9.9.E19, dlmf 9.9.E20, dlmf 9.9.E21]
theorem airy_zero_common_asymptotic_coefficients  :
    ∃ cT cU cV cW : ℕ → ℂ,
      (∀ n < 6, cT n = ([1, 5/48, -5/36, 77125/82944, -108056875/6967296, 162375596875/334430208] : List ℂ)[n]! ∧
      ∀ n < 6, cU n = ([1, -7/48, 35/288, -181223/207360, 18683371/1244160, -91145884361/191102976] : List ℂ)[n]! ∧
      ∀ n < 6, cV n = ([1, 5/48, -1525/4608, 2397875/663552, -74898940625/891813888, 144198303734375/42807066624] : List ℂ)[n]! ∧
      ∀ n < 6, cW n = ([1, -7/96, 1673/6144, -84394709/26542080, 780277135421/10192158720, -204449051051945/65229815808] : List ℂ)[n]!) ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyAiZero (k + 1) : ℂ)) (airyZeroArgument 1) cT ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyAiDerivZero (k + 1) : ℂ)) (airyZeroArgument 3) cU ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyBiZero (k + 1) : ℂ)) (airyZeroArgument 3) cT ∧
      HasAiryZeroExpansion (2 / 3) (fun k => -(airyBiDerivZero (k + 1) : ℂ)) (airyZeroArgument 1) cU ∧
      HasAiryZeroExpansion (1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k) * airyAiDeriv (airyAiZero (k + 1))) (airyZeroArgument 1) cV ∧
      HasAiryZeroExpansion (-1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k) * airyAi (airyAiDerivZero (k + 1))) (airyZeroArgument 3) cW ∧
      HasAiryZeroExpansion (1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k) * airyBiDeriv (airyBiZero (k + 1))) (airyZeroArgument 3) cV ∧
      HasAiryZeroExpansion (-1 / 6)
        (fun k => Real.sqrt π * (-1 : ℂ) ^ (k + 1) * airyBi (airyBiDerivZero (k + 1))) (airyZeroArgument 1) cW ∧
      HasAiryZeroExpansion (2 / 3)
        (fun k => exp (-π * I / 3) * airyBiComplexZero (k + 1)) (airyComplexZeroArgument 1) cT ∧
      HasAiryZeroExpansion (2 / 3)
        (fun k => exp (-π * I / 3) * airyBiDerivComplexZero (k + 1)) (airyComplexZeroArgument 3) cU ∧
      HasAiryZeroExpansion (1 / 6)
        (fun k => Real.sqrt π / Real.sqrt 2 * (-1 : ℂ) ^ (k + 1) * exp (π * I / 6) *
          airyBiDeriv (airyBiComplexZero (k + 1))) (airyComplexZeroArgument 1) cV ∧
      HasAiryZeroExpansion (-1 / 6)
        (fun k => Real.sqrt π / Real.sqrt 2 * (-1 : ℂ) ^ (k) * exp (-π * I / 6) *
          airyBi (airyBiDerivComplexZero (k + 1))) (airyComplexZeroArgument 3) cW := by
  sorry

/-- Exact common T,U,V,W parametrizations in DLMF 9.9.6–9.9.17.
Their all-order asymptotics, with the auxiliary functions eliminated, are given by
`airy_zero_common_asymptotic_coefficients`. No analytic continuation is asserted here. -/
@[dlmf 9.9.E6, dlmf 9.9.E7, dlmf 9.9.E8, dlmf 9.9.E9, dlmf 9.9.E10, dlmf 9.9.E11,
  dlmf 9.9.E12, dlmf 9.9.E13, dlmf 9.9.E14, dlmf 9.9.E15, dlmf 9.9.E16, dlmf 9.9.E17]
theorem exists_airy_zero_parametrizations :
    ∃ T U V W : ℂ → ℂ, ∀ k : ℕ,
      (airyAiZero (k + 1) : ℂ) = -T (airyZeroArgument 1 k) ∧
      airyAiDeriv (airyAiZero (k + 1)) = (-1 : ℂ) ^ k * V (airyZeroArgument 1 k) ∧
      (airyAiDerivZero (k + 1) : ℂ) = -U (airyZeroArgument 3 k) ∧
      airyAi (airyAiDerivZero (k + 1)) = (-1 : ℂ) ^ k * W (airyZeroArgument 3 k) ∧
      (airyBiZero (k + 1) : ℂ) = -T (airyZeroArgument 3 k) ∧
      airyBiDeriv (airyBiZero (k + 1)) = (-1 : ℂ) ^ k * V (airyZeroArgument 3 k) ∧
      (airyBiDerivZero (k + 1) : ℂ) = -U (airyZeroArgument 1 k) ∧
      airyBi (airyBiDerivZero (k + 1)) = (-1 : ℂ) ^ (k + 1) * W (airyZeroArgument 1 k) ∧
      airyBiComplexZero (k + 1) = exp (π * I / 3) * T (airyComplexZeroArgument 1 k) ∧
      airyBiDeriv (airyBiComplexZero (k + 1)) =
        (-1 : ℂ) ^ (k + 1) * Real.sqrt 2 * exp (-π * I / 6) * V (airyComplexZeroArgument 1 k) ∧
      airyBiDerivComplexZero (k + 1) = exp (π * I / 3) * U (airyComplexZeroArgument 3 k) ∧
      airyBi (airyBiDerivComplexZero (k + 1)) =
        (-1 : ℂ) ^ k * Real.sqrt 2 * exp (π * I / 6) * W (airyComplexZeroArgument 3 k) := by
  sorry

end AAR.Airy
