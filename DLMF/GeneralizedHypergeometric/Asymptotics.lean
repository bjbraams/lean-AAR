/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.DifferentialEquations
public import DLMF.GeneralizedHypergeometric.Integrals
public import TauCeti.Analysis.Contour.Residue.Basic

/-!
# Generalized hypergeometric asymptotics: DLMF §16.11

All powers are evaluated on a specified logarithm sheet. Thus the two formal
exponential series at phases w±πi are not collapsed by principal argument reduction.
Algebraic terms are Barnes residues, deduplicated at resonant poles; multiple poles
automatically retain the logarithmic terms mentioned in the source. The printed
coefficient recurrence is continued through repeated lower parameters by a specified
limit. Formal E/H series are coefficient families, never asserted convergent except
where DLMF explicitly claims convergence (p=q+1, |z|>1).

Residues are the proved pinned TauCeti API (authors and origin retained upstream).
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- The positive exponential index kappa, for p<q+1 (16.11.3). -/
@[dlmf 16.11.E3]
def genAsymptoticKappa (p q : ℕ) : ℕ := q + 1 - p

/-- The full complex exponent nu (16.11.3). -/
@[dlmf 16.11.E3]
def genAsymptoticNu {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) : ℂ :=
  (∑ j, a j) - (∑ j, b j) + ((q : ℂ) - p) / 2

/-- Append the fixed lower parameter b_(q+1)=1 used by the coefficient recurrence. -/
def genAsymptoticAugment {q : ℕ} (b : Fin q → ℂ) (j : Fin (q + 1)) : ℂ :=
  if hj : j.val < q then b ⟨j.val, hj⟩ else 1

/-- The raw e_(k,m) coefficient, where the augmented lower parameters are distinct. -/
@[dlmf 16.11.E5]
def genAsymptoticEkm {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (k m : ℕ) : ℂ :=
  ∑ j : Fin (q + 1),
    poch (1 - genAsymptoticNu a b - genAsymptoticKappa p q * genAsymptoticAugment b j + m)
      (genAsymptoticKappa p q + k - m) *
    (∏ i, a i - genAsymptoticAugment b j) /
      (∏ i ∈ univ.erase j, genAsymptoticAugment b i - genAsymptoticAugment b j)

/-- Raw c coefficients from the complete finite recurrence (16.11.4). -/
@[dlmf 16.11.E4]
def genAsymptoticCRaw {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) : ℕ → ℂ
  | 0 => 1
  | k + 1 => -(∑ m : Fin (k + 1), genAsymptoticCRaw a b m.val *
      genAsymptoticEkm a b (k + 1) m.val) /
      ((k + 1 : ℂ) * (genAsymptoticKappa p q : ℂ) ^ genAsymptoticKappa p q)
termination_by k => k

/-- Distinct generic perturbation of the lower parameters, keeping the appended one fixed. -/
def genAsymptoticPerturb {q : ℕ} (b : Fin q → ℂ) (ε : ℂ) (j : Fin q) : ℂ :=
  b j + (j.val + 1) * ε

/-- The coefficient c_k with removable repeated-parameter cases retained by continuation. -/
def genAsymptoticC {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (k : ℕ) : ℂ :=
  limUnder (𝓝[≠] (0 : ℂ)) (fun ε => genAsymptoticCRaw a (genAsymptoticPerturb b ε) k)

/-- The kth formal exponential term E_(p,q) on the logarithm sheet w (16.11.1). -/
@[dlmf 16.11.E1]
def genETermLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (w : ℂ) (k : ℕ) : ℂ :=
  let κ := (genAsymptoticKappa p q : ℂ)
  let ν := genAsymptoticNu a b
  (2 * Real.pi : ℂ) ^ (((p : ℂ) - q) / 2) * κ ^ (-ν - 1 / 2) *
    Complex.exp (κ * Complex.exp (w / κ)) * genAsymptoticC a b k *
    Complex.exp ((ν - k) * (Complex.log κ + w / κ))

/-- The formal algebraic simple-pole term H_(p,q) on logarithm sheet w (16.11.2). -/
@[dlmf 16.11.E2]
def genHTermLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (w : ℂ) (jk : Fin p × ℕ) : ℂ :=
  (-1 : ℂ) ^ jk.2 / jk.2.factorial * Gamma (a jk.1 + jk.2) *
    (∏ i ∈ univ.erase jk.1, Gamma (a i - a jk.1 - jk.2)) /
    genGamma (genShift (genParams b) (-a jk.1 - jk.2)) *
    Complex.exp ((-a jk.1 - jk.2) * w)

/-- The distinct upper-pole set, which does not count resonant coincidences twice. -/
def genHPoleSet {p : ℕ} (a : Fin p → ℂ) : Set ℂ :=
  {s | ∃ j : Fin p, ∃ k : ℕ, s = -a j - k}

/-- The algebraic formal term at any pole, including logarithmic multiple-pole terms. -/
def genHResidueLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (w s : ℂ) : ℂ :=
  TauCeti.Contour.residue (genBarnesKernelLog (genParams a) (genParams b) w) s

/-- A finite set of distinct algebraic poles through order N. -/
def genHPoleTrunc {p : ℕ} (a : Fin p → ℂ) (N : ℕ) : Finset ℂ := by
  classical
  exact ((Finset.univ : Finset (Fin p)).product (Finset.range N)).image (fun jk : Fin p × ℕ => -a jk.1 - jk.2)

/-- The finite algebraic expansion, retaining full residues at resonant poles. -/
def genHTruncLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (w : ℂ) (N : ℕ) : ℂ :=
  ∑ s ∈ genHPoleTrunc a N, genHResidueLog a b w s

/-- The exponential remainder scale, with its branch fixed by w. -/
def genEScaleLog {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (w : ℂ) (N : ℕ) : ℂ :=
  let κ := (genAsymptoticKappa p q : ℂ)
  Complex.exp (κ * Complex.exp (w / κ)) *
    Complex.exp ((genAsymptoticNu a b - N) * (Complex.log κ + w / κ))

/-- An algebraic remainder bound, with sufficient logarithmic degree for repeated poles. -/
def genHScaleLog {p : ℕ} (a : Fin p → ℂ) (w : ℂ) (N : ℕ) : ℝ :=
  (1 + ‖w‖) ^ (p - 1) * ∑ j, ‖Complex.exp ((-a j - N) * w)‖

/-- Approach to infinity in a closed half of the full principal logarithm sector. -/
def genInfinityLogHalf (ε : ℝ) : Filter ℂ :=
  comap Complex.re atTop ⊓ 𝓟 {w : ℂ | |w.im| ≤ Real.pi ∧ 0 ≤ ε * w.im}

/-- The selected large-parameter shift for16.11.10. -/
def genPartialShift {n : ℕ} (a : Fin n → ℂ) (k : ℕ) (r : ℝ) (j : Fin n) : ℂ :=
  if j.val < k then a j + r else a j

/-- All repeated lower-parameter cases have the finite limiting coefficient. -/
@[dlmf 16.11.E4, dlmf 16.11.E5]
theorem genAsymptoticC_limit {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p < q + 1) (k : ℕ) :
    Tendsto (fun ε : ℂ => genAsymptoticCRaw a (genAsymptoticPerturb b ε) k)
      (𝓝[≠] 0) (𝓝 (genAsymptoticC a b k)) := by
  sorry

/-- The complete printed recurrence on its nonsingular augmented-parameter domain. -/
@[dlmf 16.11.E4]
theorem genAsymptoticC_recurrence {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p < q + 1)
    (hb : Function.Injective (genAsymptoticAugment b)) :
    genAsymptoticC a b 0 = 1 ∧ ∀ k : ℕ, genAsymptoticC a b (k + 1) =
      -(∑ m ∈ range (k + 1), genAsymptoticC a b m * genAsymptoticEkm a b (k + 1) m) /
        ((k + 1 : ℂ) * (genAsymptoticKappa p q : ℂ) ^ genAsymptoticKappa p q) := by
  sorry

/-- The algebraic coefficients equal the corresponding simple Barnes residues. -/
@[dlmf 16.11.E2]
theorem genH_simple_residue {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (ha : genDenRegular (genParams a))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n)
    (w : ℂ) (j : Fin p) (k : ℕ) :
    genHResidueLog a b w (-a j - k) = genHTermLog a b w (j, k) := by
  sorry

/-- A repeated pole contributes an exponential times a polynomial in the logarithm. -/
theorem genH_resonant_log_polynomial {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (ha : genDenRegular (genParams a)) {s : ℂ} (hs : s ∈ genHPoleSet a) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ p - 1 ∧
      ∀ w : ℂ, genHResidueLog a b w s = Complex.exp (s * w) * P.eval w := by
  sorry

/-- The full H residue series converges to the continued function at |z|>1, including resonances and both closed cut sides. -/
@[dlmf 16.11.E6]
theorem genH_balanced_converges {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (ha : genDenRegular (genParams a)) (hb : genDenRegular (genParams b))
    {w : ℂ} (hr : 0 < w.re) (hi : |w.im| ≤ Real.pi) :
    HasSum (fun s : genHPoleSet a => genHResidueLog a b w s)
      (genGamma (genParams a) / genGamma (genParams b) *
        genHGNegativeLog (genParams a) (genParams b) w) := by
  sorry

/-- All orders of the equal-order expansion, with the full phase convention and resonant residues. -/
@[dlmf 16.11.E7]
theorem genHG_equal_order_asymptotic {q : ℕ} (a b : Fin q → ℂ)
    (ha : genDenRegular (genParams a)) (hb : genDenRegular (genParams b))
    (N : ℕ) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Asymptotics.IsBigO (genInfinityLogHalf ε)
      (fun w => genGamma (genParams a) / genGamma (genParams b) *
        genHG (genParams a) (genParams b) (Complex.exp w) -
        genHTruncLog a b (w - ε * Real.pi * I) N - ∑ k ∈ range N, genETermLog a b w k)
      (fun w => genHScaleLog a (w - ε * Real.pi * I) N + ‖genEScaleLog a b w N‖) := by
  sorry

/-- All orders with p=q−1, both shifted E branches, and the full algebraic residue series. -/
@[dlmf 16.11.E8]
theorem genHG_one_lower_asymptotic {p : ℕ} (a : Fin p → ℂ) (b : Fin (p + 1) → ℂ)
    (ha : genDenRegular (genParams a)) (hb : genDenRegular (genParams b)) (N : ℕ) :
    Asymptotics.IsBigO (DLMF.logSector Real.pi)
      (fun w => genGamma (genParams a) / genGamma (genParams b) *
        genHG (genParams a) (genParams b) (-Complex.exp w) - genHTruncLog a b w N -
        ∑ k ∈ range N, (genETermLog a b (w - Real.pi * I) k + genETermLog a b (w + Real.pi * I) k))
      (fun w => genHScaleLog a w N + ‖genEScaleLog a b (w - Real.pi * I) N‖ +
        ‖genEScaleLog a b (w + Real.pi * I) N‖) := by
  sorry

/-- All orders with p≤q−2 on the full principal sector, with both E branch contributions. -/
@[dlmf 16.11.E9]
theorem genHG_fewer_upper_asymptotic {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p + 2 ≤ q)
    (ha : genDenRegular (genParams a)) (hb : genDenRegular (genParams b)) (N : ℕ) :
    Asymptotics.IsBigO (DLMF.logSector Real.pi)
      (fun w => genGamma (genParams a) / genGamma (genParams b) *
        genHG (genParams a) (genParams b) (-Complex.exp w) -
        ∑ k ∈ range N, (genETermLog a b (w - Real.pi * I) k + genETermLog a b (w + Real.pi * I) k))
      (fun w => ‖genEScaleLog a b (w - Real.pi * I) N‖ +
        ‖genEScaleLog a b (w + Real.pi * I) N‖) := by
  sorry

/-- Every printed partial large-parameter shift, with unrestricted shifted bottoms and the full principal z domain. -/
@[dlmf 16.11.E10]
theorem genHG_partial_large_parameter_asymptotic {p : ℕ} (a : Fin (p + 1) → ℂ) (b : Fin p → ℂ)
    {k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p)
    (hb : ∀ j : Fin p, k ≤ j.val → ∀ n : ℕ, b j ≠ -n)
    {z : ℂ} (hz : z ∈ cutPlane) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun r : ℝ => genHG (genParams (genPartialShift a (k - 1) r))
        (genParams (genPartialShift b k r)) z -
        ∑ n ∈ range m, genCoeff (genParams (genPartialShift a (k - 1) r))
          (genParams (genPartialShift b k r)) n * z ^ n)
      (fun r : ℝ => 1 / r ^ m) := by
  sorry

/-- Every full large-parameter shift for p<q, without unnecessary exclusions on the unshifted constants. -/
@[dlmf 16.11.E11]
theorem genHG_all_large_parameter_asymptotic {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p < q) (z : ℂ) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun r : ℝ => genHG (genShift (genParams a) r) (genShift (genParams b) r) z -
        ∑ n ∈ range m, genCoeff (genShift (genParams a) r) (genShift (genParams b) r) n * z ^ n)
      (fun r : ℝ => 1 / r ^ ((q - p) * m)) := by
  sorry

end DLMF.Hypergeometric
