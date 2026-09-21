/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateL2
public import Mathlib.Topology.Order.OrderClosed

/-! # Translation Estimate H1 -/

@[expose] public section

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.TranslationEstimateH1`

Extend Euclidean `L²` translation estimates from `C¹_c` to the closure-based Euclidean `H¹` space.

## Main results

- `norm_translateL2_sub_h1ToL2_le`: for `u ∈ H¹`, `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`, where `∇u` is the
  `L²(E)` component in our `H¹ ⊆ L² × L²(E)` model.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local instance instMeasurableSpaceE_SobolevEuclideanTranslationEstimateH1 :
    MeasurableSpace E := borel E
local instance instBorelSpaceE_SobolevEuclideanTranslationEstimateH1 :
    BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceE_SobolevEuclideanTranslationEstimateH1 :
    OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddE_SobolevEuclideanTranslationEstimateH1 : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]

/-- `H¹` translation estimate via closure: `‖τ_a u - u‖₂ ≤ ‖a‖ · ‖∇u‖₂`. -/
theorem norm_translateL2_sub_h1ToL2_le (a : E) (u : ↥(h1 (μ := μ) (E := E))) :
    ‖translateL2 (μ := μ) (F := ℝ) a (h1ToL2 (μ := μ) (E := E) u) -
        h1ToL2 (μ := μ) (E := E) u‖ ≤
      ‖a‖ * ‖h1ToL2Grad (μ := μ) (E := E) u‖ := by
  classical
  -- Work in the ambient space `L² × L²(E)`.
  let V : Type _ := (E →₂[μ] ℝ) × (E →₂[μ] E)
  let S : Set V :=
    {v |
      ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ ≤
        ‖a‖ * ‖v.2‖}
  have hS_closed : IsClosed S := by
    -- Closedness follows from continuity of both sides.
    have hf :
        Continuous fun v : V =>
          ‖translateL2 (μ := μ) (F := ℝ) a v.1 - v.1‖ := by
      -- `v ↦ v.1` is continuous, translation is continuous,
      -- subtraction is continuous, and norm is continuous.
      have hfst : Continuous fun v : V => v.1 := continuous_fst
      have htr :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 := by
        -- `translateL2` is a continuous linear isometry.
        exact (translateL2 (μ := μ) (F := ℝ) a).toContinuousLinearMap.continuous.comp hfst
      have hsub :
          Continuous fun v : V =>
            translateL2 (μ := μ) (F := ℝ) a v.1 - v.1 := by
        simpa [sub_eq_add_neg] using! htr.sub hfst
      simpa using! (continuous_norm.comp hsub)
    have hg :
        Continuous fun v : V =>
          ‖a‖ * ‖v.2‖ := by
      have hsnd : Continuous fun v : V => v.2 := continuous_snd
      have hnorm : Continuous fun v : V => ‖v.2‖ := continuous_norm.comp hsnd
      simpa [mul_assoc] using! (continuous_const.mul hnorm)
    exact isClosed_le hf hg
  have hRange : (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S := by
    rintro v ⟨f, rfl⟩
    -- Reduce to the `C¹_c` estimate.
    simpa [S, graph, toL2Linear, toL2GradLinear] using!
      norm_translateL2_sub_toL2_le (μ := μ) (E := E) a f
  have hClosure :
      closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) ⊆ S :=
    closure_minimal hRange hS_closed
  have hu :
      (u : V) ∈ closure (LinearMap.range (graph (μ := μ) (E := E)) : Set V) := by
    -- `u ∈ H¹` means `u` is in the topological closure of the range of `graph`.
    have hu0 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := by
      have hu0 : (u : V) ∈ h1 (μ := μ) (E := E) := u.2
      dsimp [h1] at hu0
      exact hu0
    have hu1 :
        (u : V) ∈
          ((LinearMap.range (graph (μ := μ) (E := E))).topologicalClosure :
            Set V) := hu0
    rw [Submodule.topologicalClosure_coe] at hu1
    exact hu1
  have huS : (u : V) ∈ S := hClosure hu
  -- Unpack membership in `S` and rewrite in terms of the bundled maps `h1ToL2` and `h1ToL2Grad`.
  simpa [S, V, h1ToL2, h1ToL2Grad] using! huS

end

end

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
