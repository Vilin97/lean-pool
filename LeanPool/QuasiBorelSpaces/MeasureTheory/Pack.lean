/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# LeanPool.QuasiBorelSpaces.MeasureTheory.Pack

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.MeasureTheory.Pack`.
-/


namespace MeasureTheory

variable {A : Type*} [MeasurableSpace A] [StandardBorelSpace A]

/-- Packs a natural number and a real number into a single real number. -/
noncomputable def pack : A → ℝ :=
  open Classical in
  if h : Countable A
  then MeasureTheory.embeddingReal _
  else PolishSpace.measurableEquivOfNotCountable h not_countable

/-- Unpacks a natural number and a real number from a single real number. -/
noncomputable def unpack [Nonempty A] : ℝ → A :=
  open Classical in
  if h : Countable A
  then (MeasureTheory.measurableEmbedding_embeddingReal _).invFun
  else (PolishSpace.measurableEquivOfNotCountable h not_countable).symm

@[simp]
lemma unpack_pack [Nonempty A] (x : A) : unpack (pack x) = x := by
  simp only [unpack, pack]
  by_cases h : Countable A
  · simp only [h, ↓reduceDIte]
    apply MeasurableEmbedding.leftInverse_invFun
  · simp only [h, ↓reduceDIte, MeasurableEquiv.symm_apply_apply]

@[simp]
lemma pack_unpack [Nonempty A] (h : ¬Countable A) (x : ℝ) : pack (unpack (A := A) x) = x :=by
  simp only [pack, h, ↓reduceDIte, unpack, MeasurableEquiv.apply_symm_apply]

@[simp, fun_prop]
lemma measurable_pack : Measurable (pack (A := A)) := by
  unfold pack
  by_cases h : Countable A
  · simp only [h, ↓reduceDIte]
    fun_prop
  · simp only [h, ↓reduceDIte]
    fun_prop

@[simp, fun_prop]
lemma measurable_unpack [Nonempty A] : Measurable (unpack (A := A)) := by
  unfold unpack
  by_cases h : Countable A
  · simp only [h, ↓reduceDIte]
    fun_prop
  · simp only [h, ↓reduceDIte]
    fun_prop

end MeasureTheory
