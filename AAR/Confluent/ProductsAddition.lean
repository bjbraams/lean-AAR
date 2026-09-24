/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.Whittaker

/-!
# Products and addition theorems (DLMF §§13.12, 13.13, 13.25, 13.26)

Addition formulas are stated for positive real `x` with `x+y` in the slit
plane, so that principal powers are unambiguous.
-/

@[expose] public section

open Complex
open scoped Real Topology

noncomputable section

namespace AAR.Confluent

@[dlmf 13.12.E1]
theorem confluentM_product {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (hb1 : ∀ k : ℕ, 1 - b ≠ -k)
    (hb0 : b ≠ 0) (hb2 : b ≠ 1) (hb3 : b ≠ -1) :
    confluentM a b z * confluentM (-a) (-b) (-z) +
      a * (a - b) * z ^ 2 / (b ^ 2 * (1 - b ^ 2)) *
        confluentM (1 + a) (2 + b) z * confluentM (1 - a) (2 - b) (-z) = 1 := by
  sorry

@[dlmf 13.13.E1]
theorem confluentM_addition {a b x y : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b (x + y) =
      ∑' n : ℕ, poch a n * y ^ n / (poch b n * n.factorial) * confluentM (a + n) (b + n) x := by
  sorry

@[dlmf 13.13.E2]
theorem confluentM_addition_shift_b {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b (x + y) =
      ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, poch (1 - b) n * (-y / x) ^ n / n.factorial * confluentM a (b - n) x := by
  sorry

@[dlmf 13.13.E3]
theorem confluentM_addition_shift_a {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b (x + y) =
      (x / (x + y)) ^ a *
        ∑' n : ℕ, poch a n * y ^ n / (n.factorial * (x + y) ^ n) * confluentM (a + n) b x := by
  sorry

@[dlmf 13.13.E4]
theorem confluentM_addition_exp {a b x y : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b (x + y) =
      exp y * ∑' n : ℕ, poch (b - a) n * (-y) ^ n / (poch b n * n.factorial) *
        confluentM a (b + n) x := by
  sorry

@[dlmf 13.13.E5]
theorem confluentM_addition_exp_shift_a {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : 1 / 2 < ((y + x) / x).re) (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b (x + y) =
      exp y * (x / (x + y)) ^ (b - a) *
        ∑' n : ℕ, poch (b - a) n * y ^ n / (n.factorial * (x + y) ^ n) *
          confluentM (a - n) b x := by
  sorry

@[dlmf 13.13.E6]
theorem confluentM_addition_exp_shift_both {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b (x + y) =
      exp y * ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, poch (1 - b) n * (-y) ^ n / (n.factorial * x ^ n) *
          confluentM (a - n) (b - n) x := by
  sorry

@[dlmf 13.13.E7]
theorem confluentU_addition (a b x y : ℂ) :
    confluentU a b (x + y) =
      ∑' n : ℕ, poch a n * (-y) ^ n / n.factorial * confluentU (a + n) (b + n) x := by
  sorry

@[dlmf 13.13.E8]
theorem confluentU_addition_shift_b {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) :
    confluentU a b (x + y) =
      ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, poch (1 + a - b) n * (-y / x) ^ n / n.factorial * confluentU a (b - n) x := by
  sorry

@[dlmf 13.13.E9]
theorem confluentU_addition_shift_a {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    confluentU a b (x + y) =
      (x / (x + y)) ^ a *
        ∑' n : ℕ, poch a n * poch (1 + a - b) n * y ^ n / (n.factorial * (x + y) ^ n) *
          confluentU (a + n) b x := by
  sorry

@[dlmf 13.13.E10]
theorem confluentU_addition_exp (a b x y : ℂ) :
    confluentU a b (x + y) =
      exp y * ∑' n : ℕ, (-y) ^ n / n.factorial * confluentU a (b + n) x := by
  sorry

@[dlmf 13.13.E11]
theorem confluentU_addition_exp_shift_a {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    confluentU a b (x + y) =
      exp y * (x / (x + y)) ^ (b - a) *
        ∑' n : ℕ, (-y) ^ n / (n.factorial * (x + y) ^ n) * confluentU (a - n) b x := by
  sorry

@[dlmf 13.13.E12]
theorem confluentU_addition_exp_shift_both {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) :
    confluentU a b (x + y) =
      exp y * ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, (-y) ^ n / (n.factorial * x ^ n) * confluentU (a - n) (b - n) x := by
  sorry

@[dlmf 13.25.E1]
theorem whittakerM_product {κ μ z : ℂ} (hμ : ∀ k : ℕ, 2 * μ ≠ -k)
    (hμ1 : μ ≠ 0) (hμ2 : μ ≠ -1) (hμ3 : 1 + 2 * μ ≠ 0) (hz : z ∈ slitPlane) :
    whittakerM κ μ z * whittakerM κ (-μ - 1) z +
      (1 / 2 + μ + κ) * (1 / 2 + μ - κ) / (4 * μ * (1 + μ) * (1 + 2 * μ) ^ 2) *
        whittakerM κ (μ + 1) z * whittakerM κ (-μ) z = 1 := by
  sorry

@[dlmf 13.26.E1]
theorem whittakerM_addition {κ μ x y : ℂ} (hx : x ∈ slitPlane) (hxy : x + y ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (-y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, poch (-2 * μ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerM (κ - n / 2) (μ - n / 2) x := by
  sorry

@[dlmf 13.26.E2]
theorem whittakerM_addition_shift_mu {κ μ x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n / (poch (1 + 2 * μ) n * n.factorial) *
          (y / x ^ (1 / 2 : ℂ)) ^ n * whittakerM (κ - n / 2) (μ + n / 2) x := by
  sorry

@[dlmf 13.26.E3]
theorem whittakerM_addition_shift_kappa {κ μ x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ κ *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n * y ^ n / (n.factorial * (x + y) ^ n) *
          whittakerM (κ - n) μ x := by
  sorry

@[dlmf 13.26.E4]
theorem whittakerM_addition_exp {κ μ x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, poch (-2 * μ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerM (κ + n / 2) (μ - n / 2) x := by
  sorry

@[dlmf 13.26.E5]
theorem whittakerM_addition_exp_shift_mu {κ μ x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 + μ + κ) n / (poch (1 + 2 * μ) n * n.factorial) *
          (-y / x ^ (1 / 2 : ℂ)) ^ n * whittakerM (κ + n / 2) (μ + n / 2) x := by
  sorry

@[dlmf 13.26.E6]
theorem whittakerM_addition_exp_shift_kappa {κ μ x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : 1 / 2 < ((y + x) / x).re)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ κ *
        ∑' n : ℕ, poch (1 / 2 + μ + κ) n * y ^ n / (n.factorial * (x + y) ^ n) *
          whittakerM (κ + n) μ x := by
  sorry

@[dlmf 13.26.E7]
theorem whittakerW_addition {κ μ x y : ℂ} (hx : x ∈ slitPlane) (hxy : x + y ∈ slitPlane) :
    whittakerW κ μ (x + y) =
      exp (-y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 - μ - κ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ - n / 2) (μ - n / 2) x := by
  sorry

@[dlmf 13.26.E8]
theorem whittakerW_addition_shift_mu {κ μ x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) :
    whittakerW κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ - n / 2) (μ + n / 2) x := by
  sorry

@[dlmf 13.26.E9]
theorem whittakerW_addition_shift_kappa {κ μ x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    whittakerW κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ κ *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n / n.factorial *
          (y / (x + y)) ^ n * whittakerW (κ - n) μ x := by
  sorry

@[dlmf 13.26.E10]
theorem whittakerW_addition_exp {κ μ x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) :
    whittakerW κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, (1 / n.factorial) * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ + n / 2) (μ - n / 2) x := by
  sorry

@[dlmf 13.26.E11]
theorem whittakerW_addition_exp_shift_mu {κ μ x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) :
    whittakerW κ μ (x + y) =
      exp (y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, (1 / n.factorial) * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ + n / 2) (μ + n / 2) x := by
  sorry

@[dlmf 13.26.E12]
theorem whittakerW_addition_exp_shift_kappa {κ μ x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    whittakerW κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ κ *
        ∑' n : ℕ, (1 / n.factorial) * (-y / (x + y)) ^ n * whittakerW (κ + n) μ x := by
  sorry

end AAR.Confluent
