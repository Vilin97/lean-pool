/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Order.OmegaCompletePartialOrder
import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Const
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic


/-!
# Basic properties of ω-complete partial orders

This file is a placeholder for lemmas about `OmegaCompletePartialOrder`.
As the library grows, compatibility helpers specific to this project can
be added here.
-/

namespace OmegaCompletePartialOrder

variable {A B C : Type*}
  [OmegaCompletePartialOrder A]
  [OmegaCompletePartialOrder B]
  [OmegaCompletePartialOrder C]

attribute [fun_prop]
  ωScottContinuous
  ωScottContinuous.id
  ωScottContinuous.comp
  ωScottContinuous.const

@[fun_prop]
lemma ωScottContinuous_const (x : B) : ωScottContinuous (fun _ : A ↦ x) := ωScottContinuous.const

@[fun_prop]
lemma ωScottContinuous_mk
    {f : A → B} {g : A → C} (hf : ωScottContinuous f) (hg : ωScottContinuous g)
    : ωScottContinuous (fun x ↦ (f x, g x)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨?_, fun c ↦ ?_⟩
  · simp only [monotone_prodMk_iff, hf.monotone, hg.monotone, and_self]
  · ext : 1
    · simp only [Prod.ωSup_fst]
      rw [hf.map_ωSup]
      rfl
    · simp only [Prod.ωSup_snd]
      rw [hg.map_ωSup]
      rfl

@[fun_prop]
lemma ωScottContinuous_fst
    {f : A → B × C} (hf : ωScottContinuous f)
    : ωScottContinuous (fun x ↦ (f x).1) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨monotone_fst.comp hf.monotone, fun c ↦ ?_⟩
  rw [hf.map_ωSup]
  rfl

@[fun_prop]
lemma ωScottContinuous_snd
    {f : A → B × C} (hf : ωScottContinuous f)
    : ωScottContinuous (fun x ↦ (f x).2) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨monotone_snd.comp hf.monotone, fun c ↦ ?_⟩
  rw [hf.map_ωSup]
  rfl

@[simp]
lemma ωSup_const (x : A) : ωSup (Chain.const x) = x := by
  apply antisymm (r := (· ≤ ·))
  · simp only [ωSup_le_iff, Chain.const_apply, le_refl, implies_true]
  · apply le_ωSup_of_le 0
    simp only [Chain.const_apply, le_refl]

namespace Measure

@[fun_prop]
lemma ωScottContinuous_lintegral
    [MeasurableSpace B]
    {f : A → B → ENNReal}
    (hf₁ : ωScottContinuous fun x : _ × _ ↦ f x.1 x.2)
    (hf₂ : ∀a, Measurable (f a))
    (μ : MeasureTheory.Measure B)
    : ωScottContinuous fun x ↦ ∫⁻ y, f x y ∂μ := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun a b h ↦ ?_, fun c ↦ ?_⟩
  · apply MeasureTheory.lintegral_mono
    intro c
    apply hf₁.monotone (⟨h, le_rfl⟩ : (a, c) ≤ (b, c))
  · change ∫⁻ y, f (ωSup c) y ∂μ = ⨆ n, ∫⁻ y, f (c n) y ∂μ
    rw [← MeasureTheory.lintegral_iSup]
    · apply MeasureTheory.lintegral_congr fun b ↦ ?_
      rw [(by simp : f (ωSup c) b = f (ωSup c) (ωSup (Chain.const b)))]
      apply Eq.trans (hf₁.map_ωSup (Chain.zip c (Chain.const b)))
      rfl
    · fun_prop
    · intro i j h a
      apply hf₁.monotone
        (⟨(OrderHomClass.mono c) h, le_rfl⟩ : (c i, a) ≤ (c j, a))

end Measure

lemma ωScottContinuous_ite
    {f : A → Prop} (hf : ∀ {x y}, x ≤ y → f x = f y) [DecidablePred f]
    {g : A → B} (hg : ωScottContinuous g)
    {h : A → B} (hh : ωScottContinuous h)
    : ωScottContinuous fun x ↦ if f x then g x else h x := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y hxy ↦ ?_, fun c ↦ ?_⟩
  · grind [hh.monotone hxy, hg.monotone hxy]
  · rw [hg.map_ωSup, hh.map_ωSup, ← apply_ite]
    congr 1
    ext i
    simp only [Chain.coe_map, OrderHom.coe_mk, Function.comp_apply, hf (le_ωSup c i)]
    split_ifs <;> simp only [Chain.coe_map, OrderHom.coe_mk, Function.comp_apply]

end OmegaCompletePartialOrder
