/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.MatrixC0Alpha

/-!
# Flat one-dimensional standard Ricci--DeTurck coordinate algebra

This module records the exact scalar calculation for a flat one-dimensional
background. It is deliberately independent of the intrinsic DeTurck API:
`m`, `d`, and `h` stand for the coordinate metric entry and its first and
second spatial jets. The result exhibits the nonlinear reaction term that is
absent from the legacy schematic matrix.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace RicciFlow
namespace AnalyticPDE

/-- The sole Christoffel coefficient of `g = m dx ⊗ dx` in a flat coordinate
background, with `d = ∂ₓm`. -/
def standardDeTurckFlatOneDimensionalChristoffel (m d : ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * m⁻¹ * d

/-- The standard DeTurck vector coefficient
`V¹ = g¹¹ (Γ(g)¹₁₁ - Γ(background)¹₁₁)` in a flat one-dimensional background. -/
def standardDeTurckFlatOneDimensionalVector (m d : ℝ) : ℝ :=
  m⁻¹ * standardDeTurckFlatOneDimensionalChristoffel m d

/-- The formal first spatial jet of the standard DeTurck vector coefficient,
where `d = ∂ₓm` and `h = ∂ₓ²m`. -/
def standardDeTurckFlatOneDimensionalVectorJetDerivative (m d h : ℝ) : ℝ :=
  -(m⁻¹ ^ 3 * d ^ 2) + (2 : ℝ)⁻¹ * m⁻¹ ^ 2 * h

/-- The flat one-dimensional standard Ricci--DeTurck scalar RHS. Ricci is zero
in dimension one, so this is the `11` component of `ℒ_V g = V ∂ₓm + 2m ∂ₓV`. -/
def standardDeTurckFlatOneDimensionalRHS (m d h : ℝ) : ℝ :=
  standardDeTurckFlatOneDimensionalVector m d * d +
    (2 : ℝ) * m * standardDeTurckFlatOneDimensionalVectorJetDerivative m d h

/-- The flat one-dimensional standard Ricci--DeTurck RHS has the heat term and
its unavoidable quadratic first-jet reaction term. -/
theorem standardDeTurckFlatOneDimensionalRHS_eq
    {m : ℝ} (hm : 0 < m) (d h : ℝ) :
    standardDeTurckFlatOneDimensionalRHS m d h =
      m⁻¹ * h - (3 / 2 : ℝ) * m⁻¹ ^ 2 * d ^ 2 := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  simp only [standardDeTurckFlatOneDimensionalRHS,
    standardDeTurckFlatOneDimensionalVector,
    standardDeTurckFlatOneDimensionalChristoffel,
    standardDeTurckFlatOneDimensionalVectorJetDerivative]
  field_simp [hm0]
  ring

/-- The `1 × 1` metric matrix with entry `m`. -/
def standardDeTurckFlatOneDimensionalMetricMatrix (m : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => m

/-- The first spatial coordinate jet array of the one-dimensional metric entry. -/
def standardDeTurckFlatOneDimensionalFirstJet (d : ℝ) :
    Fin 1 → Fin 1 → Fin 1 → ℝ :=
  fun _ _ _ => d

/-- The second spatial coordinate jet array of the one-dimensional metric entry. -/
def standardDeTurckFlatOneDimensionalSecondJet (h : ℝ) :
    Fin 1 → Fin 1 → Fin 1 → Fin 1 → ℝ :=
  fun _ _ _ _ => h

/-- In the flat one-dimensional specialization, the existing schematic matrix
contains only the scalar heat term. -/
theorem ricciDeTurckSchematicMatrix_flatOneDimensional_apply
    (m d h : ℝ) :
    ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
      (standardDeTurckFlatOneDimensionalMetricMatrix m)
      (standardDeTurckFlatOneDimensionalFirstJet d)
      (standardDeTurckFlatOneDimensionalSecondJet h)
      0 0 = m⁻¹ * h := by
  simp [ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix,
    standardDeTurckFlatOneDimensionalMetricMatrix,
    standardDeTurckFlatOneDimensionalFirstJet,
    standardDeTurckFlatOneDimensionalSecondJet]

/-- The corrected flat one-dimensional standard Ricci--DeTurck RHS differs from
the legacy schematic matrix by its explicit nonlinear first-jet reaction term. -/
theorem standardDeTurckFlatOneDimensionalRHS_sub_schematic_eq
    {m : ℝ} (hm : 0 < m) (d h : ℝ) :
    standardDeTurckFlatOneDimensionalRHS m d h -
      ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (standardDeTurckFlatOneDimensionalMetricMatrix m)
        (standardDeTurckFlatOneDimensionalFirstJet d)
        (standardDeTurckFlatOneDimensionalSecondJet h)
        0 0 =
      -(3 / 2 : ℝ) * m⁻¹ ^ 2 * d ^ 2 := by
  rw [standardDeTurckFlatOneDimensionalRHS_eq hm,
    ricciDeTurckSchematicMatrix_flatOneDimensional_apply]
  ring

/-- For a positive one-dimensional metric whose first jet is nonzero, the
corrected standard Ricci--DeTurck RHS cannot equal the legacy schematic matrix. -/
theorem standardDeTurckFlatOneDimensionalRHS_ne_schematic_of_firstJet_ne_zero
    {m d h : ℝ} (hm : 0 < m) (hd : d ≠ 0) :
    standardDeTurckFlatOneDimensionalRHS m d h ≠
      ParabolicC0AlphaOn.ricciDeTurckSchematicMatrix
        (standardDeTurckFlatOneDimensionalMetricMatrix m)
        (standardDeTurckFlatOneDimensionalFirstJet d)
        (standardDeTurckFlatOneDimensionalSecondJet h)
        0 0 := by
  intro heq
  have hdisc := standardDeTurckFlatOneDimensionalRHS_sub_schematic_eq hm d h
  rw [heq] at hdisc
  have hinv : m⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hm)
  have hreaction : -(3 / 2 : ℝ) * m⁻¹ ^ 2 * d ^ 2 ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact pow_ne_zero 2 hinv
    · exact pow_ne_zero 2 hd
  apply hreaction
  simpa using hdisc.symm

end AnalyticPDE
end RicciFlow
