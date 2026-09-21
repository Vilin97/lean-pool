/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.InteriorLocalInputs
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.LocalComparisonBridges
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectionHessianRowWeightedTail
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.TestSubmodule

/-!
# Tail transfer from an interior gradient to a reflected Hessian row

This file is a purely measure-theoretic bridge.  It consumes restricted
almost-everywhere identities supplied by the reflected interior construction;
it does not assert either identity or any PDE property.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-- Restricted almost-everywhere equality transports both the square weight
and its norm-threshold set. -/
private theorem sqWeightedMeasure_tail_inter_eq_of_ae_eq_restrict
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {B : Set α} {F G : α → E} {a : ℝ}
    (hB : MeasurableSet B) (hFG : F =ᵐ[μ.restrict B] G) :
    sqWeightedMeasure F μ ({x | a < ‖F x‖} ∩ B) =
      sqWeightedMeasure G μ ({x | a < ‖G x‖} ∩ B) := by
  have hreplace :
      sqWeightedMeasure F μ ({x | a < ‖F x‖} ∩ B) =
        sqWeightedMeasure G μ ({x | a < ‖F x‖} ∩ B) :=
    sqWeightedMeasure_apply_inter_eq_of_ae_eq_restrict hB hFG
  have hFG_base : ∀ᵐ x ∂μ, x ∈ B → F x = G x :=
    (ae_restrict_iff' hB).mp hFG
  have hFG_weighted :
      ∀ᵐ x ∂sqWeightedMeasure G μ, x ∈ B → F x = G x :=
    (withDensity_absolutelyContinuous μ _).ae_le hFG_base
  have htail :
      sqWeightedMeasure G μ ({x | a < ‖F x‖} ∩ B) =
        sqWeightedMeasure G μ ({x | a < ‖G x‖} ∩ B) := by
    apply measure_congr
    filter_upwards [hFG_weighted] with x hx
    apply propext
    change (a < ‖F x‖ ∧ x ∈ B) ↔ (a < ‖G x‖ ∧ x ∈ B)
    by_cases hxB : x ∈ B
    · rw [hx hxB]
    · constructor
      · intro h
        exact False.elim (hxB h.2)
      · intro h
        exact False.elim (hxB h.2)
  exact hreplace.trans htail

/-- Transfer square-weighted tails from the zero-extended gradient on the
half parent to a reflected Hessian row and then to its source row.

The two restricted a.e. identities are explicit inputs: one identifies the
interior gradient with the reflected row on the half parent, and the other
identifies its zero extension with the source row on the source cube. -/
theorem openParentGradientExtension_reflectedHessianRow_tail_transfer
    {d : ℕ} {m : ℤ} (i : Fin d) (R : Vec d → Vec d)
    (hR : AEStronglyMeasurable (fun x => HilbertVec.ofVec (R x))
      (volume.restrict (openCubeSet (originCube d m))))
    (uU : H1Function
      (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)))
    (hUrow :
      hilbertifyVecField uU.grad =ᵐ[volume.restrict
        (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ))]
        fun x => HilbertVec.ofVec
          (cubeDirichletOddReflectionHessianRowVectorField
            (originCube d m) i R x))
    (hQsource :
      openParentGradientExtension
          (scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)) uU =ᵐ[
        volume.restrict (openCubeSet (originCube d m))]
        fun x => HilbertVec.ofVec (R x)) :
    ∀ a : ℝ,
      (sqWeightedMeasure
          (openParentGradientExtension
            (scaledOpenCubeSet
              (originCube d (m + 1)) (1 / 2 : ℝ)) uU) volume
          ({x | a < ‖openParentGradientExtension
            (scaledOpenCubeSet
              (originCube d (m + 1)) (1 / 2 : ℝ)) uU x‖} ∩
            openCubeSet (originCube d m)) =
        sqWeightedMeasure (fun x => HilbertVec.ofVec (R x)) volume
          ({x | a < ‖HilbertVec.ofVec (R x)‖} ∩
            openCubeSet (originCube d m))) ∧
      (sqWeightedMeasure
          (openParentGradientExtension
            (scaledOpenCubeSet
              (originCube d (m + 1)) (1 / 2 : ℝ)) uU) volume
          ({x | a < ‖openParentGradientExtension
            (scaledOpenCubeSet
              (originCube d (m + 1)) (1 / 2 : ℝ)) uU x‖} ∩
            scaledOpenCubeSet
              (originCube d (m + 1)) (1 / 2 : ℝ)) ≤
        ((3 : ℝ≥0∞) ^ d) *
          sqWeightedMeasure (fun x => HilbertVec.ofVec (R x)) volume
            ({x | a < ‖HilbertVec.ofVec (R x)‖} ∩
              openCubeSet (originCube d m))) := by
  let U : Set (Vec d) :=
    scaledOpenCubeSet (originCube d (m + 1)) (1 / 2 : ℝ)
  let Q : Set (Vec d) := openCubeSet (originCube d m)
  let Fext : Vec d → HilbertVec d := openParentGradientExtension U uU
  let Fgrad : Vec d → HilbertVec d := hilbertifyVecField uU.grad
  let Frow : Vec d → HilbertVec d := fun x => HilbertVec.ofVec
    (cubeDirichletOddReflectionHessianRowVectorField
      (originCube d m) i R x)
  let Fsource : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (R x)
  have hUmeas : MeasurableSet U :=
    (isOpen_scaledOpenCubeSet
      (originCube d (m + 1)) (1 / 2 : ℝ)).measurableSet
  have hQmeas : MeasurableSet Q :=
    measurableSet_openCubeSet (originCube d m)
  have hUrow' : Fgrad =ᵐ[volume.restrict U] Frow := by
    simpa only [Fgrad, Frow, U] using hUrow
  have hQsource' : Fext =ᵐ[volume.restrict Q] Fsource := by
    simpa only [Fext, Fsource, U, Q] using hQsource
  intro a
  constructor
  · exact sqWeightedMeasure_tail_inter_eq_of_ae_eq_restrict
      hQmeas hQsource'
  · have hindicator :
        sqWeightedMeasure Fext volume ({x | a < ‖Fext x‖} ∩ U) =
          sqWeightedMeasure Fgrad volume ({x | a < ‖Fgrad x‖} ∩ U) := by
      simpa only [Fext, Fgrad, openParentGradientExtension] using
        sqWeightedMeasure_indicator_tail_inter_eq_of_subset
          (μ := volume) (U := U) (B := U) (f := Fgrad) (a := a)
          hUmeas hUmeas (fun _ hx => hx)
    have hrow_tail :
        sqWeightedMeasure Fgrad volume ({x | a < ‖Fgrad x‖} ∩ U) =
          sqWeightedMeasure Frow volume ({x | a < ‖Frow x‖} ∩ U) :=
      sqWeightedMeasure_tail_inter_eq_of_ae_eq_restrict hUmeas hUrow'
    calc
      sqWeightedMeasure Fext volume ({x | a < ‖Fext x‖} ∩ U) =
          sqWeightedMeasure Fgrad volume ({x | a < ‖Fgrad x‖} ∩ U) :=
        hindicator
      _ = sqWeightedMeasure Frow volume ({x | a < ‖Frow x‖} ∩ U) :=
        hrow_tail
      _ ≤ ((3 : ℝ≥0∞) ^ d) *
          sqWeightedMeasure Fsource volume
            ({x | a < ‖Fsource x‖} ∩ Q) := by
        simpa only [Frow, Fsource, U, Q] using
          reflectedHessianRow_sqWeightedMeasure_innerHalf_tail_le
            i R hR

end CubeCalderonZygmund

end

end Homogenization
