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
public import LeanPool.NavierStokesAndEuler.Euler.QuadraticHeatLocal
public import LeanPool.NavierStokesAndEuler.Euler.QuadraticCoefficients
import LeanPool.NavierStokesAndEuler.Euler.SobolevHeatVolterra
import LeanPool.NavierStokesAndEuler.Euler.VolterraUniqueness
import Mathlib.Algebra.Order.Star.Real

/-! Exact continuation-by-pasting for the actual projected quadratic viscous equation. -/

section

/-! Actual nonlinear source paths commute with restriction and adjacent-interval solution pasting.
-/

section

/-! A uniform positive restart time for bounded data in the actual viscous Sobolev equation. -/

@[expose] public section

noncomputable section

namespace EulerUniformHeatLocal

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerQuadraticSource
open scoped Topology

/-- A translated compact time window inside the prescribed coefficient interval. -/
def timeWindow {S : ℝ} (a T : ℝ) (ha : 0 ≤ a) (haT : a + T ≤ S) :
    C(Icc (0 : ℝ) T, Icc (0 : ℝ) S) where
  toFun t := ⟨a+t.val, by linarith [t.property.1], by linarith [t.property.2]⟩
  continuous_toFun := (continuous_const.add continuous_subtype_val).subtype_mk _

/-- The mass of the actual parabolic kernel bound is monotone in nonnegative time. -/
theorem parabolic_mass_mono (ν s t : ℝ) (hst : s ≤ t) :
    s + 2 * parabolicConstant ν * Real.sqrt s ≤ t + 2 * parabolicConstant ν * Real.sqrt t := by
  have hC := parabolicConstant_nonneg ν
  have hroot := Real.sqrt_le_sqrt hst
  nlinarith

variable (period : ℝ) [Fact (0 < period)]

/-- Uniformly bounded initial Sobolev data have genuine local solutions on every time window of one
fixed positive length.
The length depends only on the compact coefficient bounds and the data bound, not on the restart
time or state. -/
theorem exists_uniform_restart_time (q : ℕ) (ν : ℝ) (hν : 0 < ν) (S : ℝ) (hS : 0 < S)
    (R : ℝ) (hR : 0 ≤ R)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q + 1)) (SobolevSpace period q)) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ S ∧
      ∀ (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (haT : a+T ≤ S), T ≤ δ →
        ∀ u₀ : SobolevSpace period (q+1), ‖u₀‖ ≤ R →
          ∃ u : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)),
            ‖u‖ ≤ R+1 ∧ u ⟨0, le_rfl, hT⟩ = u₀ ∧
            ∀ t : Icc (0 : ℝ) T, u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
              ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
                (C.apply (timeWindow a T ha haT (projIcc 0 T hT (t.val-r)))
                  (u (projIcc 0 T hT (t.val-r)))) := by
  have hR1 : 0 ≤ R+1 := by linarith
  obtain ⟨δ, hδ, hδS, hb, hl⟩ := exists_positive_time_budget ν
    (C.ballBound (R+1)) (C.ballLipschitz (R+1)) 1 S (by norm_num) hS
  refine ⟨δ, hδ, hδS, ?_⟩
  intro a T ha hT haT hTδ u₀ hu₀
  let D := C.comp (timeWindow a T ha haT)
  have hmass := parabolic_mass_mono ν T δ hTδ
  have hM := C.ballBound_nonneg (R+1) hR1
  have hL := C.ballLipschitz_nonneg (R+1) hR1
  have hbudget : ‖u₀‖ + (T+2*parabolicConstant ν*Real.sqrt T)*C.ballBound (R+1) ≤ R+1 := by
    have hh := mul_le_mul_of_nonneg_right hmass hM
    linarith
  have hsmall : (T+2*parabolicConstant ν*Real.sqrt T)*C.ballLipschitz (R+1) < 1 :=
    (mul_le_mul_of_nonneg_right hmass hL).trans_lt hl
  obtain ⟨u, hu, hsol⟩ := exists_viscous_mild_solution period q ν hν T hT u₀ D.apply D.continuous
    (R+1) (C.ballBound (R+1)) (C.ballLipschitz (R+1)) hR1 hM hL
    (fun t x hx => C.apply_bound (R+1) hR1 (timeWindow a T ha haT t) x hx)
    (fun t x y hx hy => C.apply_sub_bound (R+1) hR1 (timeWindow a T ha haT t) x y hx hy)
    hbudget hsmall
  refine ⟨u, hu, ?_, hsol⟩
  have hzero := hsol ⟨0, le_rfl, hT⟩
  simpa only [mul_zero, Real.toNNReal_zero, heatOperator_zero, intervalIntegral.integral_same,
      add_zero] using hzero

end EulerUniformHeatLocal

end
end

end

@[expose] public section

noncomputable section

namespace EulerWindowSource

open MeasureTheory Set EulerVolterraConvolution EulerUniformHeatLocal EulerQuadraticSource
  EulerTimePathGluing
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The actual nonlinear forcing evaluated along a solution on a translated compact time window. -/
def windowSource {S : ℝ} (C : Coefficients (Icc (0 : ℝ) S) X Y)
    (a T : ℝ) (ha : 0 ≤ a) (haT : a + T ≤ S) (u : C(Icc (0 : ℝ) T, X)) : C(Icc (0 : ℝ) T, Y) :=
  ⟨fun t => C.apply (timeWindow a T ha haT t) (u t),
    C.continuous.comp ((timeWindow a T ha haT).continuous.prodMk u.continuous)⟩

/-- The clamped source has its literal nonlinear value at every time inside its actual window. -/
theorem windowSource_extend {S : ℝ} (C : Coefficients (Icc (0 : ℝ) S) X Y)
    (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (haT : a + T ≤ S)
    (u : C(Icc (0 : ℝ) T, X)) (r : ℝ) (hr : r ∈ Icc 0 T) :
    extendPath T hT (windowSource C a T ha haT u) r =
      C.apply (timeWindow a T ha haT ⟨r,hr⟩) (extendPath T hT u r) :=
  congrArg (fun t => C.apply (timeWindow a T ha haT t) (extendPath T hT u r)) (projIcc_of_mem hT hr)

/-- At zero offset the actual source path is exactly the initial-interval source used by the local
solver. -/
theorem windowSource_zero {S T : ℝ} (C : Coefficients (Icc (0 : ℝ) S) X Y)
    (hT : 0 ≤ T) (hTS : T ≤ S) (u : C(Icc (0 : ℝ) T, X)) (r : ℝ) :
    extendPath T hT (windowSource C 0 T le_rfl (by simpa using hTS) u) r =
      C.apply (timeInclusion hTS (projIcc 0 T hT r)) (extendPath T hT u r) := by
  apply congrArg (fun t => C.apply t (extendPath T hT u r))
  apply Subtype.ext
  exact zero_add _

/-- Before the restart, the literal nonlinear source of the pasted solution is the old source. -/
theorem windowSource_glue_left {S : ℝ} (C : Coefficients (Icc (0 : ℝ) S) X Y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (habS : a + b ≤ S)
    (u : C(Icc (0 : ℝ) a, X)) (v : C(Icc (0 : ℝ) b, X))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) (r : ℝ) (hr : r ∈ Icc 0 a) :
    extendPath (a+b) (add_nonneg ha hb)
      (windowSource C 0 (a+b) le_rfl (by simpa using habS) (gluePath a b ha hb u v hmatch)) r =
      extendPath a ha (windowSource C 0 a le_rfl (by linarith) u) r := by
  have hru : r ∈ Icc 0 (a+b) := ⟨hr.1,by linarith [hr.2]⟩
  have h1 := windowSource_extend C 0 (a+b) le_rfl (add_nonneg ha hb) (by simpa using habS)
    (gluePath a b ha hb u v hmatch) r hru
  have h2 := windowSource_extend C 0 a le_rfl ha (by linarith) u r hr
  have ht : timeWindow 0 (a+b) le_rfl (by simpa using habS) ⟨r,hru⟩ =
      timeWindow 0 a le_rfl (by linarith) ⟨r,hr⟩ := by apply Subtype.ext; rfl
  exact h1.trans ((congrArg₂ C.apply ht (gluePath_left a b ha hb u v hmatch r hr)).trans h2.symm)

/-- After the restart, the literal nonlinear source of the pasted solution is the translated new
source. -/
theorem windowSource_glue_right {S : ℝ} (C : Coefficients (Icc (0 : ℝ) S) X Y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (habS : a + b ≤ S)
    (u : C(Icc (0 : ℝ) a, X)) (v : C(Icc (0 : ℝ) b, X))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) (r : ℝ) (hr : r ∈ Icc 0 b) :
    extendPath (a+b) (add_nonneg ha hb)
      (windowSource C 0 (a+b) le_rfl (by simpa using habS) (gluePath a b ha hb u v hmatch)) (a+r) =
      extendPath b hb (windowSource C a b ha habS v) r := by
  have hru : a+r ∈ Icc 0 (a+b) := ⟨by linarith [hr.1],by linarith [hr.2]⟩
  have h1 := windowSource_extend C 0 (a+b) le_rfl (add_nonneg ha hb) (by simpa using habS)
    (gluePath a b ha hb u v hmatch) (a+r) hru
  have h2 := windowSource_extend C a b ha hb habS v r hr
  have ht : timeWindow 0 (a+b) le_rfl (by simpa using habS) ⟨a+r,hru⟩ =
      timeWindow a b ha habS ⟨r,hr⟩ := by apply Subtype.ext; exact zero_add _
  exact h1.trans ((congrArg₂ C.apply ht (gluePath_right a b ha hb u v hmatch r hr)).trans h2.symm)

end EulerWindowSource

end
end

end

section

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

end
end

end

@[expose] public section

noncomputable section

namespace EulerQuadraticMildPasting

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerVolterraConvolution
  EulerUniformHeatLocal EulerQuadraticSource EulerTimePathGluing EulerGainedMildPasting
      EulerWindowSource
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The local solver's actual quadratic Duhamel formula is exactly the literal zero-offset nonlinear
source formula. -/
theorem quadratic_mild_window_iff {q : ℕ} (ν : ℝ) (hν : 0 < ν) {S T : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q + 1)) (SobolevSpace period q))
    (u₀ : SobolevSpace period (q + 1)) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) :
    (∀ t, u t = quadraticDuhamel period ν hν hT hTS C u₀ u t) ↔
    (∀ t : Icc (0 : ℝ) T, u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
      ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
        (extendPath T hT (windowSource C 0 T le_rfl (by simpa using hTS) u) (t.val-r))) := by
  have he (t : Icc (0 : ℝ) T) : quadraticDuhamel period ν hν hT hTS C u₀ u t =
      heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
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

/-- The actual projected quadratic mild equation is preserved when a genuine local restart is
appended. -/
theorem glue_quadratic_mild {q : ℕ} (ν : ℝ) (hν : 0 < ν) {S : ℝ}
    (C : Coefficients (Icc (0 : ℝ) S) (SobolevSpace period (q + 1)) (SobolevSpace period q))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (haS : a ≤ S) (habS : a + b ≤ S)
    (u : C(Icc (0 : ℝ) a, SobolevSpace period (q + 1)))
    (v : C(Icc (0 : ℝ) b, SobolevSpace period (q + 1)))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) (u₀ : SobolevSpace period (q + 1))
    (hsolu : ∀ t, u t = quadraticDuhamel period ν hν ha haS C u₀ u t)
    (hsolv : ∀ t : Icc (0 : ℝ) b, v t = heatOperator period (q+1) (2*ν*t.val).toNNReal (u
        ⟨a,ha,le_rfl⟩) +
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
