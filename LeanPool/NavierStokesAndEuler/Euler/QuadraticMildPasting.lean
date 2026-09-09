/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.WindowSource

@[expose] public section

/-! Exact continuation-by-pasting for the actual projected quadratic viscous equation. -/

noncomputable section

namespace EulerQuadraticMildPasting

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerVolterraConvolution
  EulerUniformHeatLocal EulerQuadraticSource EulerTimePathGluing EulerGainedMildPasting
    EulerWindowSource
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The local solver's actual quadratic Duhamel formula is exactly the literal zero-offset nonlinear source formula. -/
theorem quadratic_mild_window_iff {q : ℕ} (ν : ℝ) (hν : 0 < ν) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q+1)) (SobolevSpace period q))
    (u₀ : SobolevSpace period (q+1)) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1))) :
    (∀ t, u t = quadraticDuhamel period ν hν hT hTS C u₀ u t) ↔
    (∀ t : Icc (0 : ℝ) T, u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀+
      ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
        (extendPath T hT (windowSource C 0 T le_rfl (by simpa using hTS) u) (t.val-r))) := by
  have he (t : Icc (0 : ℝ) T) : quadraticDuhamel period ν hν hT hTS C u₀ u t =
      heatOperator period (q+1) (2*ν*t.val).toNNReal u₀+
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
          (extendPath T hT (windowSource C 0 T le_rfl (by simpa using hTS) u) (t.val-r)) := by
    unfold quadraticDuhamel
    apply congrArg (fun x => heatOperator period (q+1) (2*ν*t.val).toNNReal u₀+x)
    apply intervalIntegral.integral_congr
    intro r _
    exact congrArg (heatKernel period q ν hν r) (windowSource_zero C hT hTS u (t.val-r)).symm
  constructor
  · intro h t
    exact (h t).trans (he t)
  · intro h t
    exact (h t).trans (he t).symm

/-- The actual projected quadratic mild equation is preserved when a genuine local restart is appended. -/
theorem glue_quadratic_mild {q : ℕ} (ν : ℝ) (hν : 0 < ν) {S : ℝ}
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q+1)) (SobolevSpace period q))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (haS : a ≤ S) (habS : a+b ≤ S)
    (u : C(Icc (0 : ℝ) a, SobolevSpace period (q+1)))
    (v : C(Icc (0 : ℝ) b, SobolevSpace period (q+1)))
    (hmatch : u ⟨a,ha,le_rfl⟩ = v ⟨0,le_rfl,hb⟩) (u₀ : SobolevSpace period (q+1))
    (hsolu : ∀ t, u t = quadraticDuhamel period ν hν ha haS C u₀ u t)
    (hsolv : ∀ t : Icc (0 : ℝ) b, v t = heatOperator period (q+1) (2*ν*t.val).toNNReal (u
      ⟨a,ha,le_rfl⟩)+
      ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
        (C.apply (timeWindow a b ha habS (projIcc 0 b hb (t.val-r))) (v (projIcc 0 b hb
          (t.val-r))))) :
    ∀ t, gluePath a b ha hb u v hmatch t = quadraticDuhamel period ν hν (add_nonneg ha hb) habS C u₀
      (gluePath a b ha hb u v hmatch) t := by
  apply (quadratic_mild_window_iff period ν hν (add_nonneg ha hb) habS C u₀
    (gluePath a b ha hb u v hmatch)).mpr
  exact glue_gained_mild period ν hν a b ha hb u v hmatch
    (windowSource C 0 (a+b) le_rfl (by simpa using habS) (gluePath a b ha hb u v hmatch))
    (windowSource C 0 a le_rfl (by simpa using haS) u) (windowSource C a b ha habS v) u₀
    (windowSource_glue_left C a b ha hb habS u v hmatch)
    (windowSource_glue_right C a b ha hb habS u v hmatch)
    ((quadratic_mild_window_iff period ν hν ha haS C u₀ u).mp hsolu) hsolv

end EulerQuadraticMildPasting
