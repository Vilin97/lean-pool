/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ClassicalBridge
public import LeanPool.NavierStokesAndEuler.Euler.InitialDataBridge
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothField

@[expose] public section

/-!
# Interface to the current Euler development

The divergence operators agree definitionally. Compact smooth initial data
satisfy the Comparator's initial-data conditions. To package a Comparator
solution as the development's `SmoothL2Field`, however, one must establish
square integrability of every spatial derivative. The exact equivalence below
exposes that obligation without adding it to the reference statement.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Euler.ComparatorBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem divergence_eq_development (v : ℝ³ → ℝ³) (x : ℝ³) :
    Euler.divergence v x = EulerSmoothLimit.divergence v x := rfl

theorem admissible_initial_data
    (A : EulerLpTranslation.SmoothL2Field ℝ³) (hc : HasCompactSupport A.field)
    (hd : ∀ x, EulerSmoothLimit.divergence A.field x = 0) :
    InitialVelocityConditionDecay A.field :=
  initialVelocityConditionDecay_of_compact A.field A.smooth hc hd

theorem exists_smoothL2Field_iff
    {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p) (t : ℝ) (ht : 0 ≤ t) :
    (∃ A : EulerLpTranslation.SmoothL2Field ℝ³, A.field = (v · t)) ↔
      ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m (v · t)) 2 volume := by
  constructor
  · rintro ⟨A, hA⟩ m
    rw [← hA]
    exact A.integrable m
  · intro hjets
    exact ⟨⟨(v · t), h.velocity_contDiff t ht, hjets⟩, rfl⟩

/-- A conversion once the required all-order spatial integrability is proved.
This hypothesis is deliberately explicit; the Comparator does not provide it. -/
def velocityField
    {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}
    (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (hjets : ∀ t ≥ 0, ∀ m : ℕ, MemLp (iteratedFDeriv ℝ m (v · t)) 2 volume)
    (t : ℝ) (ht : 0 ≤ t) : EulerLpTranslation.SmoothL2Field ℝ³ where
  field := (v · t)
  smooth := h.velocity_contDiff t ht
  integrable := hjets t ht

end Euler.ComparatorBridge
