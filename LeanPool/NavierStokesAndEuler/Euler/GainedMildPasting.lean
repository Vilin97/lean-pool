/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatKernel
public import LeanPool.NavierStokesAndEuler.Euler.TimePathGluing
import LeanPool.NavierStokesAndEuler.Euler.DuhamelPasting
import LeanPool.NavierStokesAndEuler.Euler.GainedMildFormula

/-! Pasting actual high-order viscous mild solutions preserves the derivative-gaining Duhamel
formula. -/

@[expose] public section


noncomputable section

namespace EulerGainedMildPasting

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerSobolevHeatGenerator
  EulerVolterraConvolution EulerDuhamelDifferentiation EulerTimePathGluing EulerDuhamelPasting
      EulerGainedMildFormula
open scoped Topology

/-- Applying an actual bounded spatial map commutes with matching-endpoint time pasting. -/
theorem gluePath_map_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (A : E →L[ℝ] F)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) (t : Icc (0 : ℝ) (a + b)) :
    A (gluePath a b ha hb u v hmatch t) =
      gluePath a b ha hb (A.compLeftContinuous ℝ (Icc (0 : ℝ) a) u)
        (A.compLeftContinuous ℝ (Icc (0 : ℝ) b) v) (congrArg A hmatch) t := by
  change A (if t.val ≤ a then extendPath a ha u t.val else extendPath b hb v (t.val-a)) =
    if t.val ≤ a then A (extendPath a ha u t.val) else A (extendPath b hb v (t.val-a))
  split <;> rfl

variable (period : ℝ) [Fact (0 < period)]

/-- Matching actual solutions on adjacent intervals give a genuine gained-derivative mild solution
on the union. -/
theorem glue_gained_mild {q : ℕ} (ν : ℝ) (hν : 0 < ν) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, SobolevSpace period (q + 1)))
    (v : C(Icc (0 : ℝ) b, SobolevSpace period (q + 1)))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩)
    (f : C(Icc (0 : ℝ) (a + b), SobolevSpace period q))
    (f1 : C(Icc (0 : ℝ) a, SobolevSpace period q))
    (f2 : C(Icc (0 : ℝ) b, SobolevSpace period q)) (u₀ : SobolevSpace period (q + 1))
    (hF1 : ∀ r ∈ Icc 0 a, extendPath (a + b) (add_nonneg ha hb) f r = extendPath a ha f1 r)
    (hF2 : ∀ r ∈ Icc 0 b, extendPath (a + b) (add_nonneg ha hb) f (a + r) = extendPath b hb f2 r)
    (hsolu : ∀ t : Icc (0 : ℝ) a, u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
      ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath a ha f1 (t.val-r)))
    (hsolv : ∀ t : Icc (0 : ℝ) b, v t = heatOperator period (q+1) (2*ν*t.val).toNNReal (u
        ⟨a,ha,le_rfl⟩) +
      ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath b hb f2 (t.val-r))) :
    ∀ t : Icc (0 : ℝ) (a+b), gluePath a b ha hb u v hmatch t =
      heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath (a+b) (add_nonneg ha hb) f
            (t.val-r)) := by
  let ul := (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) a) u
  let vl := (truncateOperator period q).compLeftContinuous ℝ (Icc (0 : ℝ) b) v
  have hml : ul ⟨a,ha,le_rfl⟩ = vl ⟨0,le_rfl,hb⟩ := congrArg (truncateOperator period q) hmatch
  have hul := (gained_mild_iff period q ν hν a ha u₀ f1 u).mp hsolu
  have hvl := (gained_mild_iff period q ν hν b hb (u ⟨a,ha,le_rfl⟩) f2 v).mp hsolv
  have h := glue_ordinary_mild period ν hν.le a b ha hb ul vl hml f f1 f2
    (truncateOperator period q u₀) hF1 hF2 hul hvl
  apply (gained_mild_iff period q ν hν (a+b) (add_nonneg ha hb) u₀ f
    (gluePath a b ha hb u v hmatch)).mpr
  intro t
  exact (gluePath_map_apply (truncateOperator period q) a b ha hb u v hmatch t).trans (h t)

end EulerGainedMildPasting
