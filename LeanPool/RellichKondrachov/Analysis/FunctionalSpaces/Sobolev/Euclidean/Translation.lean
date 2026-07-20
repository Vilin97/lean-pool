/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import LeanPool.RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.H1
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic

/-!
# `RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.Translation`

Translation utilities for the Euclidean Sobolev model spaces.

This file is intentionally “pre-Rellich”: it provides the algebraic/measure-theoretic translation
operators and their interaction with the `C¹_c` graph embedding used to define `H¹`.

## Main results

- `translateC1c`: translation as a linear endomorphism of `C¹_c`.
- `translateL2`: translation as a linear isometry of `L²` (under an invariant measure).
- `translateL2_toL2` / `translateL2_toL2Grad`: translation commutes with `toL2` / `toL2Grad`.
- `grad_translate`: the Euclidean gradient commutes with translation.
-/

namespace RellichKondrachov
namespace Analysis
namespace FunctionalSpaces
namespace Sobolev
namespace Euclidean

open scoped ENNReal MeasureTheory Topology
open MeasureTheory

section Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Translate a function by `a` (right translation): `x ↦ f (x + a)`. -/
def translate {F : Type*} (a : E) (f : E → F) : E → F :=
  fun x => f (x + a)

omit [CompleteSpace E] in
lemma contDiff_translate {f : E → ℝ} (hf : ContDiff ℝ 1 f) (a : E) :
    ContDiff ℝ 1 (translate (E := E) a f) := by
  -- `x ↦ x + a` is `C^∞`; compose.
  exact hf.comp (contDiff_id.add contDiff_const)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma hasCompactSupport_translate {F : Type*} [Zero F] {f : E → F}
    (hf : HasCompactSupport f) (a : E) : HasCompactSupport (translate (E := E) a f) := by
  exact hf.comp_homeomorph (Homeomorph.addRight a)

lemma grad_translate (a : E) (f : E → ℝ) (x : E) :
    grad (E := E) (translate (E := E) a f) x = grad (E := E) f (x + a) := by
  classical
  -- `fderiv` commutes with translation, hence so does `grad`.
  -- Reduce to the standard `fderiv` translation lemma, applied under the Riesz dual map.
  have hfderiv : fderiv ℝ (translate (E := E) a f) x = fderiv ℝ f (x + a) :=
    fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) a
  simp only [grad, hfderiv]

omit [CompleteSpace E] in
lemma mem_C1c_translate {f : E → ℝ} (hf : f ∈ C1c (E := E)) (a : E) :
    translate (E := E) a f ∈ C1c (E := E) :=
  ⟨contDiff_translate (E := E) hf.1 a, hasCompactSupport_translate (E := E) hf.2 a⟩

/-- Translation as a linear endomorphism of `C¹_c`. -/
noncomputable def translateC1c (a : E) : ↥(C1c (E := E)) →ₗ[ℝ] ↥(C1c (E := E)) where
  toFun f := ⟨translate (E := E) a f.1, mem_C1c_translate (E := E) (f := f.1) f.2 a⟩
  map_add' f g := by
    ext x
    simp [translate]
  map_smul' c f := by
    ext x
    simp [translate]

end Topology

section Measure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Borel σ-algebra on the model space `E`. -/
local instance instMeasurableSpaceTranslation : MeasurableSpace E := borel E
local instance instBorelSpaceTranslation : BorelSpace E := ⟨rfl⟩
local instance instOpensMeasurableSpaceTranslation : OpensMeasurableSpace E := by
  infer_instance
local instance instMeasurableAddTranslation : MeasurableAdd E := by
  infer_instance

variable (μ : Measure E) [μ.IsAddRightInvariant]

/-- Translation on `L²` as a linear isometry, under an additive right-invariant measure. -/
noncomputable def translateL2 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E) :
    (E →₂[μ] F) →ₗᵢ[ℝ] (E →₂[μ] F) := by
  classical
  simpa using
    (MeasureTheory.Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := F) (p := (2 : ENNReal))
      (μ := μ) (μb := μ) (f := fun x : E => x + a) (MeasureTheory.measurePreserving_add_right μ a))

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
lemma translateL2_ae_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : E)
    (g : E →₂[μ] F) :
    (translateL2 (μ := μ) (F := F) a g : E → F) =ᵐ[μ] fun x => (g : E → F) (x + a) := by
  classical
  -- Reduce to `Lp.coeFn_compMeasurePreserving`.
  exact
    (MeasureTheory.Lp.coeFn_compMeasurePreserving (g := (g : MeasureTheory.Lp F (2 : ENNReal) μ))
      (hf := MeasureTheory.measurePreserving_add_right μ a))

variable [IsFiniteMeasureOnCompacts μ]

omit [CompleteSpace E] in
lemma translateL2_toL2 (a : E) (f : ↥(C1c (E := E))) :
    translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) =
      toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) := by
  apply Lp.ext
  have h₁ :
      (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
        fun x => f.1 (x + a) := by
    have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hf' :
        (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
      -- Move the a.e. equality through a measure-preserving map.
      exact
        (Measure.QuasiMeasurePreserving.ae_eq_comp
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
    exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
  have h₂ :
      (toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) : E → ℝ) =ᵐ[μ]
        fun x => f.1 (x + a) := by
    -- `toL2` agrees a.e. with the underlying translated function.
    exact
      (memLp_of_mem_C1c (μ := μ) (E := E) (translateC1c (E := E) a f).2).coeFn_toLp
  exact h₁.trans h₂.symm

lemma translateL2_toL2Grad (a : E) (f : ↥(C1c (E := E))) :
    translateL2 (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f) =
      toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) := by
  apply Lp.ext
  have h₁ :
      (translateL2 (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f) : E → E) =ᵐ[μ]
        fun x => grad (E := E) f.1 (x + a) := by
    have hf :
        (toL2Grad (μ := μ) (E := E) f : E → E) =ᵐ[μ] grad (E := E) f.1 :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hf' :
        (fun x => (toL2Grad (μ := μ) (E := E) f : E → E) (x + a)) =ᵐ[μ]
          fun x => grad (E := E) f.1 (x + a) := by
      exact
        (Measure.QuasiMeasurePreserving.ae_eq_comp
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
    exact
      (translateL2_ae_eq (μ := μ) (F := E) a (toL2Grad (μ := μ) (E := E) f)).trans hf'
  have h₂ :
      (toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) : E → E) =ᵐ[μ]
        fun x => grad (E := E) f.1 (x + a) := by
    have hTo :
        (toL2Grad (μ := μ) (E := E) (translateC1c (E := E) a f) : E → E) =ᵐ[μ]
          grad (E := E) (translate (E := E) a f.1) :=
      (memLp_grad_of_mem_C1c (μ := μ) (E := E) (translateC1c (E := E) a f).2).coeFn_toLp
    have hGrad :
        grad (E := E) (translate (E := E) a f.1) = fun x => grad (E := E) f.1 (x + a) := by
      funext x
      simpa [translate] using grad_translate (E := E) a f.1 x
    exact hTo.trans (by simp [hGrad])
  exact h₁.trans h₂.symm

end Measure

end Euclidean
end Sobolev
end FunctionalSpaces
end Analysis
end RellichKondrachov
