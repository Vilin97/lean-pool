/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.ChangeMeasureLeSmul
public import LeanPool.RellichKondrachov.MeasureTheory.Function.LpSpace.Restrict

/-!
# `RellichKondrachov.MeasureTheory.Function.LpSpace.ExtendByZeroRangeEquiv`

Transport `Lp` **extend-by-zero ranges** across comparable measures on a measurable set.

For a measurable set `s`, the extend-by-zero map
`Lp E p (μ.restrict s) →ₗᵢ[ℝ] Lp E p μ` is a linear isometry. Hence its range is canonically
isomorphic to `Lp E p (μ.restrict s)`. If two measures `μ, ν` are mutually comparable on `s`,
`Lp.changeMeasureEquiv` provides an equivalence between the restricted `Lp` spaces, and therefore
an equivalence between the corresponding extend-by-zero ranges.

This is used in the manifold Rellich glue to transport compactness on `volume` to chart measures on
fixed compact supports.
-/

@[expose] public section

namespace MeasureTheory

open scoped ENNReal

namespace Lp

noncomputable section

variable {α : Type*} [MeasurableSpace α]
variable {μ ν : Measure α}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {s : Set α} (hs : MeasurableSet s)

/-- If `μ.restrict s` and `ν.restrict s` are mutually comparable (with finite constants), then the
extend-by-zero ranges in `Lp` are continuously linearly equivalent. -/
noncomputable def extendByZeroRangeEquivOfRestrictChangeMeasureEquiv {c₁ c₂ : ℝ≥0∞}
    (hc₁ : c₁ ≠ ∞) (hc₂ : c₂ ≠ ∞)
    (hν : ν.restrict s ≤ c₁ • μ.restrict s) (hμ : μ.restrict s ≤ c₂ • ν.restrict s)
    (hp : p ≠ ∞) :
    ↥(LinearMap.range
          ((Lp.extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs).toLinearMap)) ≃L[ℝ]
        ↥(LinearMap.range
          ((Lp.extendByZeroₗᵢ (μ := ν) (E := E) (p := p) (s := s) hs).toLinearMap)) := by
  classical
  let eμ := Lp.extendByZeroₗᵢ (μ := μ) (E := E) (p := p) (s := s) hs
  let eν := Lp.extendByZeroₗᵢ (μ := ν) (E := E) (p := p) (s := s) hs
  -- Identify each range with the restricted `Lp` space, transport across measures, then re-embed.
  refine
    ((LinearIsometry.equivRange eμ).symm.toContinuousLinearEquiv.trans
        ((Lp.changeMeasureEquiv (μ := μ.restrict s) (ν := ν.restrict s) (E := E) (p := p)
          hc₁ hc₂ hν hμ hp).trans
          (LinearIsometry.equivRange eν).toContinuousLinearEquiv))

end

end Lp

end MeasureTheory
