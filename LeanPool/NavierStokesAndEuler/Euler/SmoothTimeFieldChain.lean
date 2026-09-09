/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldComposition
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldBilinear
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldAlgebra
public import LeanPool.NavierStokesAndEuler.Euler.SmoothTimeFieldTimeJets
public import LeanPool.NavierStokesAndEuler.Euler.SeparatingTimeDerivative

@[expose] public section

/-! Genuine time product and chain rules for the constructed smooth
bounded coefficient paths. The closed-interval statements include both
one-sided endpoints, obtained from the actual Bochner integral identity. -/

noncomputable section

open scoped ContDiff BoundedContinuousFunction

namespace SmoothTimeField

open Set EulerVolterraConvolution

section Application

variable {K E V W : Type} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

def applyField (A : SmoothTimeField K E (V →L[ℝ] W)) (B : SmoothTimeField K E V) :
    SmoothTimeField K E W :=
  bilinear (ContinuousLinearMap.id ℝ (V →L[ℝ] W)) A B

@[simp] theorem applyField_apply (A : SmoothTimeField K E (V →L[ℝ] W))
    (B : SmoothTimeField K E V) (t : K) (x : E) :
    (applyField A B).field t x = A.field t x (B.field t x) := rfl

end Application

variable {E V W Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {T : ℝ} {hT : 0 ≤ T}

theorem TimeDerivative.congr_fields
    {A A₁ B B₁ : SmoothTimeField (Icc (0 : ℝ) T) E V}
    (hA : TimeDerivative T hT A A₁)
    (he : ∀ t x, A.field t x=B.field t x)
    (he₁ : ∀ t x, A₁.field t x=B₁.field t x) :
    TimeDerivative T hT B B₁ := by
  intro t x
  have hf : (fun s => B.realField T hT s x) = (fun s => A.realField T hT s x) := by
    funext s
    exact (he (projIcc 0 T hT s) x).symm
  rw [hf,← he₁]
  exact hA t x

theorem TimeDerivative.bilinear (L : V →L[ℝ] W →L[ℝ] Z)
    {A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E V}
    {B B₁ : SmoothTimeField (Icc (0 : ℝ) T) E W}
    (hA : TimeDerivative T hT A A₁) (hB : TimeDerivative T hT B B₁) :
    TimeDerivative T hT (bilinear L A B) ((bilinear L A₁ B).add (bilinear L A B₁)) := by
  intro t x
  have hL := L.hasFDerivAt.comp_hasDerivWithinAt (t : ℝ) (hA t x)
  have h := hL.clm_apply (hB t x)
  change HasDerivWithinAt (fun s => L (A.realField T hT s x) (B.realField T hT s x))
    (L (A₁.field t x) (B.field t x)+L (A.field t x) (B₁.field t x)) (Icc (0 : ℝ) T) t
  simpa only [Function.comp_def,realField_apply] using h

theorem TimeDerivative.applyField
    {A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E (V →L[ℝ] W)}
    {B B₁ : SmoothTimeField (Icc (0 : ℝ) T) E V}
    (hA : TimeDerivative T hT A A₁) (hB : TimeDerivative T hT B B₁) :
    TimeDerivative T hT (applyField A B) ((applyField A₁ B).add (applyField A B₁)) :=
  hA.bilinear (ContinuousLinearMap.id ℝ (V →L[ℝ] W)) hB

theorem compDisplacement_time_interior
    (A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E V)
    (D D₁ : SmoothTimeField (Icc (0 : ℝ) T) E E)
    (hA : TimeDerivative T hT A A₁) (hD : TimeDerivative T hT D D₁)
    (t : Icc (0 : ℝ) T) (ht : (t : ℝ) ∈ Ioo 0 T) (x : E) :
    HasDerivAt (fun s => (A.compDisplacement D).realField T hT s x)
      (A₁.field t (x+D.field t x)+A.derivative.field t (x+D.field t x) (D₁.field t x)) t := by
  have hi := (hasDerivAt_id (t : ℝ)).prodMk
    (((hD t x).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).const_add x)
  have ho := realField_hasFDerivAt T hT A A₁ hA (t : ℝ) ht (x+D.realField T hT t x)
  have h := ho.comp_hasDerivAt (t : ℝ) hi
  change HasDerivAt (fun s => A.realField T hT s (x+D.realField T hT s x)) _ _
  simpa only [Function.comp_def,Function.uncurry_def,id_eq,jointDerivative,ContinuousLinearMap.coprod_apply,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul,realField_apply] using h

variable [CompleteSpace V]

theorem TimeDerivative.compDisplacement
    {A A₁ : SmoothTimeField (Icc (0 : ℝ) T) E V}
    {D D₁ : SmoothTimeField (Icc (0 : ℝ) T) E E}
    (hA : TimeDerivative T hT A A₁) (hD : TimeDerivative T hT D D₁) :
    TimeDerivative T hT (A.compDisplacement D)
      ((A₁.compDisplacement D).add (SmoothTimeField.applyField (A.derivative.compDisplacement D)
        D₁)) := by
  intro t x
  let C := A.compDisplacement D
  let C₁ := (A₁.compDisplacement D).add (SmoothTimeField.applyField (A.derivative.compDisplacement
    D) D₁)
  have hh := EulerSeparatingTimeDerivative.hasDerivWithinAt T hT
    (sliceFamily T C x) (sliceFamily T C₁ x)
    (fun _ : Unit => ContinuousLinearMap.id ℝ V)
    (by intro u v huv; exact congrFun huv ())
    (by
      intro _ s hs
      exact compDisplacement_time_interior A A₁ D D₁ hA hD ⟨s,hs.1.le,hs.2.le⟩ hs x)
    t
  exact hh

end SmoothTimeField
