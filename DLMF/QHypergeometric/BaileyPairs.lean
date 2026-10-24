/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Bailey
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Bailey transforms and pairs (DLMF §17.12)

The finite Bailey-pair definition, Bailey lemma and Watson transformation are
already proved in `DLMF.Bailey`. This module adds the general double-series
transform and the remaining infinite identity and explicit pair.
The general transform uses absolute summability, the hypothesis permitting
the interchange of its two infinite sums.
-/

@[expose] public noncomputable section
open Complex Finset Filter
open scoped Topology
namespace DLMF.QHypergeometric

/-- The finite row of a general Bailey transform. -/
@[dlmf 17.12.E2]
def generalBaileyBeta (u v α : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ range (n + 1), α j * u (n - j) * v (n + j)

/-- The infinite column of a general Bailey transform. -/
@[dlmf 17.12.E2]
def generalBaileyGamma (u v δ : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑' n : ℕ, if j ≤ n then δ n * u (n - j) * v (n + j) else 0

/-- General Bailey transform, with the double-sum convergence needed by Fubini. -/
@[dlmf 17.12.E1]
theorem generalBaileyTransform (u v α δ : ℕ → ℂ)
    (hF : Summable (fun p : ℕ × ℕ =>
      if p.2 ≤ p.1 then α p.2 * δ p.1 * u (p.1 - p.2) * v (p.1 + p.2) else 0)) :
    (∑' j : ℕ, α j * generalBaileyGamma u v δ j) =
      ∑' n : ℕ, generalBaileyBeta u v α n * δ n := by
  let F : ℕ → ℕ → ℂ := fun n j =>
    if j ≤ n then α j * δ n * u (n - j) * v (n + j) else 0
  have hrow (n : ℕ) : (∑' j, F n j) = generalBaileyBeta u v α n * δ n := by
    have hs : HasSum (F n) (∑ j ∈ range (n + 1), F n j) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by
        have hj' : ¬j ≤ n := by simpa using hj
        simp [F, hj']
    rw [hs.tsum_eq, generalBaileyBeta, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j ≤ n := by simpa using hj
    simp [F, hj']
    ring
  have hcol (j : ℕ) : (∑' n, F n j) = α j * generalBaileyGamma u v δ j := by
    rw [generalBaileyGamma, ← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : j ≤ n <;> simp [F, hn]
    ring
  have hcomm := (show Summable (Function.uncurry F) from hF).tsum_comm
  calc (∑' j : ℕ, α j * generalBaileyGamma u v δ j)
      = ∑' j, ∑' n, F n j := tsum_congr fun j => (hcol j).symm
    _ = ∑' n, ∑' j, F n j := hcomm
    _ = ∑' n, generalBaileyBeta u v α n * δ n := tsum_congr hrow

/-- DLMF17.12: an infinite chain is obtained by successive applications of17.12.5.
The transform parameters may vary at each step. Every displayed quotient denominator,
including the denominators in the Bailey-pair relation, is required to be nonzero. -/
@[dlmf 17.12]
def IsBaileyChain (a q : ℂ) (α β : ℕ → ℕ → ℂ) : Prop :=
  (∀ k : ℕ, DLMF.Bailey.IsBaileyPair a q (α k) (β k)) ∧
  (∀ n : ℕ, DLMF.QSeries.qPochhammer q q n ≠ 0) ∧
  (∀ n : ℕ, DLMF.QSeries.qPochhammer (a*q) q n ≠ 0) ∧
  ∃ ρ1 ρ2 : ℕ → ℂ, ∀ k : ℕ,
    ρ1 k ≠ 0 ∧ ρ2 k ≠ 0 ∧
    (∀ n : ℕ, DLMF.QSeries.qPochhammer (a*q/ρ1 k) q n ≠ 0) ∧
    (∀ n : ℕ, DLMF.QSeries.qPochhammer (a*q/ρ2 k) q n ≠ 0) ∧
    (∀ n : ℕ,
      DLMF.QSeries.qPochhammer (a*q/ρ1 k) q n *
        DLMF.QSeries.qPochhammer (a*q/ρ2 k) q n * α (k+1) n =
      DLMF.QSeries.qPochhammer (ρ1 k) q n *
        DLMF.QSeries.qPochhammer (ρ2 k) q n *
        (a*q/(ρ1 k*ρ2 k))^n * α k n) ∧
    (∀ n : ℕ,
      DLMF.QSeries.qPochhammer (a*q/ρ1 k) q n *
        DLMF.QSeries.qPochhammer (a*q/ρ2 k) q n * β (k+1) n =
      ∑ j ∈ Finset.range (n+1),
        DLMF.QSeries.qPochhammer (ρ1 k) q j *
          DLMF.QSeries.qPochhammer (ρ2 k) q j *
          DLMF.QSeries.qPochhammer (a*q/(ρ1 k*ρ2 k)) q (n-j) *
          (a*q/(ρ1 k*ρ2 k))^j * β k j /
            DLMF.QSeries.qPochhammer q q (n-j))

/-- The infinite limiting form of Bailey's lemma. -/
@[dlmf 17.12.E4]
theorem limitingBaileyTransform {a q : ℂ} {α β : ℕ → ℂ}
    (hq : ‖q‖ < 1) (hpair : DLMF.Bailey.IsBaileyPair a q α β)
    (hden : ∀ n : ℕ, DLMF.QSeries.qPochhammer (a * q) q n ≠ 0)
    (hα : Summable (fun n : ℕ => q ^ (n * n) * a ^ n * α n))
    (hβ : Summable (fun n : ℕ => q ^ (n * n) * a ^ n * β n)) :
    (∑' n : ℕ, q ^ (n * n) * a ^ n * β n) =
      (∑' n : ℕ, q ^ (n * n) * a ^ n * α n) /
        DLMF.QSeries.qPochhammerInf (a * q) q := by
  sorry

/-- The explicit numerator sequence of the Rogers–Ramanujan Bailey pair. -/
@[dlmf 17.12.E6]
def rogersBaileyAlpha (a q : ℂ) (n : ℕ) : ℂ :=
  DLMF.QSeries.qPochhammer a q n * (1 - a * q ^ (2 * n)) * (-1) ^ n *
    q ^ (n * n + n.choose 2) * a ^ n /
      (DLMF.QSeries.qPochhammer q q n * (1 - a))

/-- The explicit denominator sequence of the Rogers–Ramanujan Bailey pair. -/
@[dlmf 17.12.E6]
def rogersBaileyBeta (q : ℂ) (n : ℕ) : ℂ :=
  (DLMF.QSeries.qPochhammer q q n)⁻¹

/-- The displayed sequences form a Bailey pair wherever their quotients are finite.
The removable specialization `a=1` is deliberately not identified with `0/0`. -/
@[dlmf 17.12.E6]
theorem rogersBaileyPair {a q : ℂ} (ha : a ≠ 1)
    (hqq : ∀ n : ℕ, DLMF.QSeries.qPochhammer q q n ≠ 0)
    (haq : ∀ n : ℕ, DLMF.QSeries.qPochhammer (a * q) q n ≠ 0) :
    DLMF.Bailey.IsBaileyPair a q (rogersBaileyAlpha a q) (rogersBaileyBeta q) := by
  sorry

end DLMF.QHypergeometric
