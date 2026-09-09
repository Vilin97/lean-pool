/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldJoint
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeSuperposition
public import LeanPool.NavierStokesAndEuler.Euler.SmoothPathTimeJets
public import LeanPool.NavierStokesAndEuler.Euler.BoundedFieldTimeDerivative

@[expose] public section

/-! A literal time derivative of smooth bounded fields differentiates
every actual spatial jet, both pointwise and in the uniform field norm. -/

noncomputable section


open scoped ContDiff BoundedContinuousFunction

namespace SmoothTimeField

open Set EulerVolterraConvolution EulerSmoothPathTimeJets

variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (T : ℝ) (hT : 0 ≤ T) (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E V)

private local instance (n : ℕ) : NormedAddCommGroup (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E [×n]→L[ℝ] V) := inferInstance
private local instance (n : ℕ) : NormedAddCommGroup (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance
private local instance (n : ℕ) : NormedSpace ℝ (E →ᵇ (E [×n]→L[ℝ] V)) := inferInstance

def sliceFamily (x : E) : C(Icc (0 : ℝ) T,V) :=
  A.superposition ((ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)) x)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
@[simp] theorem sliceFamily_apply (x : E) (t : Icc (0 : ℝ) T) :
    sliceFamily T A x t = A.field t x := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
theorem sliceFamily_contDiff : ContDiff ℝ ∞ (sliceFamily T A) :=
  A.superposition_contDiff.comp
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) (E := E)
      (F := C(Icc (0 : ℝ) T,E)) (ContinuousLinearMap.const ℝ (Icc (0 : ℝ) T)))

theorem sliceFamily_jet (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    jetFamily T (sliceFamily T A) n x t = A.jet n t x := by
  rw [jetFamily_apply T _ (sliceFamily_contDiff T A)]
  exact (A.jet_eq n t x).symm

theorem TimeDerivative.jet_pointwise (htime : TimeDerivative T hT A A₁)
    (n : ℕ) (x : E) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => extendPath T hT (A.jet n) s x)
      (A₁.jet n t x) (Icc (0 : ℝ) T) t := by
  have hd : ∀ y (s : Icc (0 : ℝ) T),
      HasDerivWithinAt (extendPath T hT (sliceFamily T A y))
        (sliceFamily T A₁ y s) (Icc (0 : ℝ) T) s := fun y s => htime s y
  have h := jetFamily_hasDerivWithinAt T hT (sliceFamily T A) (sliceFamily T A₁)
    (sliceFamily_contDiff T A) (sliceFamily_contDiff T A₁) hd n x t
  have he : extendPath T hT (jetFamily T (sliceFamily T A) n x) =
      fun s => extendPath T hT (A.jet n) s x := by
    funext s
    exact sliceFamily_jet T A n x (projIcc 0 T hT s)
  rw [he, sliceFamily_jet] at h
  exact h

theorem TimeDerivative.derivative (htime : TimeDerivative T hT A A₁) :
    TimeDerivative T hT A.derivative A₁.derivative := by
  intro t x
  let L := (continuousMultilinearCurryFin1 ℝ E V).toContinuousLinearEquiv.toContinuousLinearMap
  have h := L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ)
    (TimeDerivative.jet_pointwise T hT A A₁ htime 1 x t)
  exact h

theorem TimeDerivative.jet_uniform (htime : TimeDerivative T hT A A₁)
    (n : ℕ) (t : Icc (0 : ℝ) T) :
    HasDerivWithinAt (extendPath T hT (A.jet n))
      (A₁.jet n t) (Icc (0 : ℝ) T) t := by
  have h := EulerBoundedFieldTimeDerivative.hasDerivWithinAt T hT (A.jet n) (A₁.jet n)
    (fun s hs x => by
      simpa only [extendPath, projIcc_of_mem hT hs] using
        TimeDerivative.jet_pointwise T hT A A₁ htime n x ⟨s,hs⟩) t t.property
  simpa only [extendPath, projIcc_of_mem hT t.property] using h

end SmoothTimeField
