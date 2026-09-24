/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Solutions

/-!
# Riemann's differential equation (DLMF §15.11)

P-symbols are interpreted as solution spaces. The source's E5 is the Möbius map
appearing explicitly in `riemann_mobius_covariance`; no separate general-purpose
Möbius transformation definition is introduced. The covariance statement treats
finite triples whose images remain finite. The normalized operator and reduction
handle the usual triple containing infinity. A classification of all Fuchsian
equations is deferred until regular singularities on the Riemann sphere are defined.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Hypergeometric

/-- Riemann's differential operator with three finite singular points. -/
@[dlmf 15.11.E1]
def riemannOperator (α β γ a₁ a₂ b₁ b₂ c₁ c₂ : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  iteratedDeriv 2 f z +
    ((1 - a₁ - a₂) / (z - α) + (1 - b₁ - b₂) / (z - β) + (1 - c₁ - c₂) / (z - γ)) * deriv f z +
    ((α - β) * (α - γ) * a₁ * a₂ / (z - α) + (β - α) * (β - γ) * b₁ * b₂ / (z - β)+
      (γ - α) * (γ - β) * c₁ * c₂ / (z - γ)) * f z / ((z - α) * (z - β) * (z - γ))

/-- The P-symbol denotes a set of solutions, not a distinguished scalar function.
The domain is explicit; differentiability is required there. -/
@[dlmf 15.11.E3]
def riemannSolutions (α β γ a₁ a₂ b₁ b₂ c₁ c₂ : ℂ) (U : Set ℂ) : Set (ℂ → ℂ) :=
  {f | ContDiffOn ℂ 2 f U ∧ ∀ z ∈ U, riemannOperator α β γ a₁ a₂ b₁ b₂ c₁ c₂ f z = 0}

/-- Riemann's operator with singularities at `0,1,∞`. -/
def riemannNormalOperator (a₁ a₂ b₁ b₂ c₁ c₂ : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  iteratedDeriv 2 f z + ((1 - a₁ - a₂) / z + (1 - b₁ - b₂) / (z - 1)) * deriv f z +
    (a₁ * a₂ / z + b₁ * b₂ / (1 - z) - c₁ * c₂) * f z / (z * (1 - z))

/-- The exponent pairs of the Gauss equation satisfy Fuchs's relation. -/
@[dlmf 15.11.E2]
theorem gauss_fuchs_relation (a b c : ℂ) :
    0 + (1 - c) + 0 + (c - a - b) + a + b = 1 := by ring

/-- The Gauss equation is the normalized Riemann equation with these exponent pairs. -/
@[dlmf 15.11.E4]
theorem riemannNormalOperator_gauss (a b c : ℂ) (f : ℂ → ℂ) {z : ℂ}
    (hz : z ≠ 0) (hz1 : z ≠ 1) :
    z * (1 - z) * riemannNormalOperator 0 (1 - c) 0 (c - a - b) a b f z =
      gaussOperator a b c f z := by
  unfold riemannNormalOperator gaussOperator
  field_simp
  ring

@[dlmf 15.11.E7]
theorem riemann_hypergeometric_solution {α β γ a₁ a₂ b₁ b₂ c₁ c₂ z : ℂ}
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ) (hzγ : z ≠ γ)
    (hfuchs : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1)
    (hc : ∀ k : ℕ, 1 + a₁ - a₂ ≠ -(k : ℂ))
    (hα : (z - α) / (z - γ) ∈ slitPlane) (hβ : (z - β) / (z - γ) ∈ slitPlane)
    (hz : ‖(z - α) * (β - γ) / ((z - γ) * (β - α))‖ < 1) :
    riemannOperator α β γ a₁ a₂ b₁ b₂ c₁ c₂
      (fun w => ((w - α) / (w - γ)) ^ a₁ * ((w - β) / (w - γ)) ^ b₁ *
        ₂F₁ (a₁ + b₁ + c₁) (a₁ + b₁ + c₂) (1 + a₁ - a₂) ((w - α) * (β - γ) / ((w - γ) * (β - α)))) z = 0 := by
  sorry

@[dlmf 15.11.E8]
theorem riemann_gauge_shift {a₁ a₂ b₁ b₂ c₁ c₂ l m z : ℂ} {f : ℂ → ℂ}
    (hfuchs : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1) (hf : ContDiffAt ℂ 2 f z)
    (hz : z ∈ slitPlane) (hz1 : 1 - z ∈ slitPlane)
    (heq : riemannNormalOperator a₁ a₂ b₁ b₂ c₁ c₂ f z = 0) :
    riemannNormalOperator (a₁ + l) (a₂ + l) (b₁ + m) (b₂ + m) (c₁ - l - m) (c₂ - l - m)
      (fun w => w ^ l * (1 - w) ^ m * f w) z = 0 := by
  sorry

@[dlmf 15.11.E5, dlmf 15.11.E6]
theorem riemann_mobius_covariance {α β γ a₁ a₂ b₁ b₂ c₁ c₂ κ l μ ν z : ℂ} {f : ℂ → ℂ}
    (hdet : κ * ν - l * μ = 1) (hfuchs : a₁ + a₂ + b₁ + b₂ + c₁ + c₂ = 1)
    (hαβ : α ≠ β) (hαγ : α ≠ γ) (hβγ : β ≠ γ)
    (hα : μ * α + ν ≠ 0) (hβ : μ * β + ν ≠ 0) (hγ : μ * γ + ν ≠ 0)
    (hz : μ * z + ν ≠ 0) (hzα : z ≠ α) (hzβ : z ≠ β) (hzγ : z ≠ γ)
    (hf : ContDiffAt ℂ 2 f ((κ * z + l) / (μ * z + ν)))
    (heq : riemannOperator ((κ * α + l) / (μ * α + ν)) ((κ * β + l) / (μ * β + ν))
      ((κ * γ + l) / (μ * γ + ν)) a₁ a₂ b₁ b₂ c₁ c₂ f ((κ * z + l) / (μ * z + ν)) = 0) :
    riemannOperator α β γ a₁ a₂ b₁ b₂ c₁ c₂
      (fun w => f ((κ * w + l) / (μ * w + ν))) z = 0 := by
  sorry

end AAR.Hypergeometric
