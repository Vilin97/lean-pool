/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GainedMildPasting

@[expose] public section

/-! Actual nonlinear source paths commute with restriction and adjacent-interval solution pasting.
  -/

noncomputable section

namespace EulerWindowSource

open MeasureTheory Set EulerVolterraConvolution EulerUniformHeatLocal EulerQuadraticSource
  EulerTimePathGluing EulerGainedMildPasting
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The actual nonlinear forcing evaluated along a solution on a translated compact time window. -/
def windowSource {S : ℝ} (C : Coefficients (Icc (0 : ℝ) S) X Y)
    (a T : ℝ) (ha : 0 ≤ a) (haT : a+T ≤ S) (u : C(Icc (0 : ℝ) T, X)) : C(Icc (0 : ℝ) T, Y) :=
  ⟨fun t => C.apply (timeWindow a T ha haT t) (u t),
    C.continuous.comp ((timeWindow a T ha haT).continuous.prodMk u.continuous)⟩

/-- The clamped source has its literal nonlinear value at every time inside its actual window. -/
theorem windowSource_extend {S : ℝ} (C : Coefficients (Icc (0 : ℝ) S) X Y)
    (a T : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (haT : a+T ≤ S)
    (u : C(Icc (0 : ℝ) T, X)) (r : ℝ) (hr : r ∈ Icc 0 T) :
    extendPath T hT (windowSource C a T ha haT u) r =
      C.apply (timeWindow a T ha haT ⟨r,hr⟩) (extendPath T hT u r) :=
  congrArg (fun t => C.apply (timeWindow a T ha haT t) (extendPath T hT u r)) (projIcc_of_mem hT hr)

/-- At zero offset the actual source path is exactly the initial-interval source used by the local solver. -/
theorem windowSource_zero {S T : ℝ} (C : Coefficients (Icc (0 : ℝ) S) X Y)
    (hT : 0 ≤ T) (hTS : T ≤ S) (u : C(Icc (0 : ℝ) T, X)) (r : ℝ) :
    extendPath T hT (windowSource C 0 T le_rfl (by simpa using hTS) u) r =
      C.apply (timeInclusion hTS (projIcc 0 T hT r)) (extendPath T hT u r) := by
  apply congrArg (fun t => C.apply t (extendPath T hT u r))
  apply Subtype.ext
  exact zero_add _

/-- Before the restart, the literal nonlinear source of the pasted solution is the old source. -/
theorem windowSource_glue_left {S : ℝ} (C : Coefficients (Icc (0 : ℝ) S) X Y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (habS : a+b ≤ S)
    (u : C(Icc (0 : ℝ) a, X)) (v : C(Icc (0 : ℝ) b, X))
    (hmatch : u ⟨a,ha,le_rfl⟩ = v ⟨0,le_rfl,hb⟩) (r : ℝ) (hr : r ∈ Icc 0 a) :
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

/-- After the restart, the literal nonlinear source of the pasted solution is the translated new source. -/
theorem windowSource_glue_right {S : ℝ} (C : Coefficients (Icc (0 : ℝ) S) X Y)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (habS : a+b ≤ S)
    (u : C(Icc (0 : ℝ) a, X)) (v : C(Icc (0 : ℝ) b, X))
    (hmatch : u ⟨a,ha,le_rfl⟩ = v ⟨0,le_rfl,hb⟩) (r : ℝ) (hr : r ∈ Icc 0 b) :
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
