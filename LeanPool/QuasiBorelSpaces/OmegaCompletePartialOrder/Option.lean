/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/

import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Basic
import LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Option

/-!
# LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Option

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Option`.
-/


/-
Faithful ωCPO structure on `Option A` (bottom element `none`, supremum of a
chain given by the first defined element and the ω-supremum of the tail).
-/

variable {A : Type*}

namespace OmegaCompletePartialOrder.Option

variable [OmegaCompletePartialOrder A]

noncomputable instance instOptionLeanPool : OmegaCompletePartialOrder (Option A) where
  ωSup c := Option.map ωSup (Chain.Option.distrib c)
  le_ωSup c i := by
    cases c using Chain.Option.distrib_cases with
    | none => simp only [Chain.Option.none_coe, Chain.Option.distrib_none, Option.map_none, le_refl]
    | some j c =>
      simp only [Chain.Option.some_coe, Chain.Option.distrib_some, Option.map_some]
      by_cases h : i < j
      · simp only [h, ↓reduceIte, Option.none_le]
      · simp only [h, ↓reduceIte, Option.some_le_some]
        apply le_ωSup
  ωSup_le c x h := by
    cases c using Chain.Option.distrib_cases with
    | none => simp only [Chain.Option.distrib_none, Option.map_none, Option.none_le]
    | some i c =>
      simp only [Chain.Option.distrib_some, Option.map_some]
      cases x with
      | none =>
        specialize h i
        simp only [
          Chain.Option.some_coe, lt_self_iff_false, ↓reduceIte,
          Nat.sub_self, Option.le_none, reduceCtorEq] at h
      | some x =>
        simp only [Option.some_le_some, ωSup_le_iff]
        intro j
        specialize h (j + i)
        have : ¬j + i < i := by grind
        simp only [
          Chain.Option.some_coe, this, ↓reduceIte,
          Nat.add_sub_cancel, Option.some_le_some] at h
        exact h

variable {B C : Type*} [OmegaCompletePartialOrder B] [OmegaCompletePartialOrder C]

@[fun_prop]
lemma ωScottContinuous_some
    {f : A → B} (hf : ωScottContinuous f)
    : ωScottContinuous fun x ↦ some (f x) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y hxy ↦ ?_, fun c ↦ ?_⟩
  · simp only [Option.some_le_some]
    apply hf.monotone hxy
  · simp only [hf.map_ωSup, ωSup]
    let c' := c.map {
        toFun := fun x ↦ some (f x)
        monotone' i j hij := by apply hf.monotone hij
    }
    change _ = Option.map ωSup (Chain.Option.distrib c')
    have : c' = Chain.Option.some 0 (c.map ⟨f, hf.monotone⟩) := by
      ext n
      simp only [
        Chain.coe_map, OrderHom.coe_mk, Function.comp_apply, Option.some.injEq,
        Chain.Option.some_coe, Nat.not_lt_zero, ↓reduceIte, Nat.sub_zero, c']
    simp only [this, Chain.Option.distrib_some, Option.map_some]

@[fun_prop]
lemma ωScottContinuous_elim
    [OrderBot C]
    {f : A → Option B} (hf : ωScottContinuous f)
    {g : C} (hg : g = ⊥ := by rfl)
    {h : A → B → C} (hh : ωScottContinuous fun x : A × B ↦ h x.1 x.2)
    : ωScottContinuous fun x ↦ Option.elim (f x) g (h x) := by
  subst hg
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y hxy ↦ ?_, fun c ↦ ?_⟩
  · cases hfx : f x with
    | none => simp only [hfx, Option.elim_none, bot_le]
    | some z =>
      have := hf.monotone hxy
      cases hgx : f y with
      | none =>
        simp only [hfx, hgx, Option.le_none, reduceCtorEq] at this
      | some w =>
        simp only [hfx, Option.elim_some, hgx]
        refine hh.monotone (⟨?_, ?_⟩ : (x, z) ≤ (y, w))
        · simp only [hxy]
        · simp only [hfx, hgx, Option.some_le_some] at this
          simp only [this]
  · simp only [hf.map_ωSup, ωSup]
    let c' := c.map ⟨f, hf.monotone⟩
    change (Option.map ωSup (Chain.Option.distrib c')).elim ⊥ (h (ωSup c)) = _
    cases hc' : c' using Chain.Option.distrib_cases with
    | none =>
      simp only [
        Chain.ext_iff, Chain.coe_map, OrderHom.coe_mk, funext_iff,
        Function.comp_apply, Chain.Option.none_coe, c'] at hc'
      symm
      simp only [Chain.Option.distrib_none, Option.map_none, Option.elim_none]
      rw [eq_bot_iff, ωSup_le_iff]
      intro i
      simp only [
        Chain.coe_map, OrderHom.coe_mk, Function.comp_apply,
        hc', Option.elim_none, le_refl]
    | some i c'' =>
      simp only [
        Chain.ext_iff, Chain.coe_map, OrderHom.coe_mk, funext_iff,
        Function.comp_apply, Chain.Option.some_coe, c'] at hc'
      simp only [Chain.Option.distrib_some, Option.map_some, Option.elim_some]
      apply Eq.trans (hh.map_ωSup (c.zip c''))
      apply le_antisymm
      · simp only [
          ωSup_le_iff, Chain.coe_map, OrderHom.coe_mk, Function.comp_apply, Chain.zip_apply]
        intro j
        apply le_ωSup_of_le (i + j)
        specialize hc' (i + j)
        simp only [add_lt_iff_neg_left, not_lt_zero, ↓reduceIte, add_tsub_cancel_left] at hc'
        simp only [Chain.coe_map, OrderHom.coe_mk, Function.comp_apply, hc', Option.elim_some]
        apply hh.monotone (_ : (_, _) ≤ (_, _))
        simp only [ge_iff_le, Prod.mk_le_mk, le_refl, and_true]
        apply c.monotone
        simp only [le_add_iff_nonneg_left, zero_le]
      · simp only [ωSup_le_iff, Chain.coe_map, OrderHom.coe_mk, Function.comp_apply]
        intro j
        apply le_ωSup_of_le j
        specialize hc' j
        by_cases hji : j < i
        · simp only [hji, ↓reduceIte] at hc'
          simp only [
            hc', Option.elim_none, Chain.coe_map, OrderHom.coe_mk,
            Function.comp_apply, Chain.zip_apply, bot_le]
        · simp only [hji, ↓reduceIte] at hc'
          simp only [
            hc', Option.elim_some, Chain.coe_map, OrderHom.coe_mk,
            Function.comp_apply, Chain.zip_apply]
          apply hh.monotone (_ : (_, _) ≤ (_, _))
          simp only [ge_iff_le, Prod.mk_le_mk, le_refl, true_and]
          apply c''.monotone
          simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]

@[fun_prop]
lemma ωScottContinuous_map
    {f : A → B → C} (hf : ωScottContinuous fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : ωScottContinuous g)
    : ωScottContinuous (fun x ↦ Option.map (f x) (g x)) := by
  have {x} : Option.map (f x) (g x) = Option.elim (g x) .none (.some ∘ f x) := by
    cases g x <;> rfl
  simp only [this]
  exact ωScottContinuous_elim hg rfl (by fun_prop)

@[fun_prop]
lemma ωScottContinuous_bind
    {f : A → B → Option C} (hf : ωScottContinuous fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : ωScottContinuous g)
    : ωScottContinuous (fun x ↦ Option.bind (g x) (f x)) := by
  have {x} : Option.bind (g x) (f x) = Option.elim (g x) .none (f x) := by
    cases g x <;> rfl
  simp only [this]
  exact ωScottContinuous_elim hg rfl (by fun_prop)

@[fun_prop]
lemma ωScottContinuous_bind'
    {C : Type _} [OmegaCompletePartialOrder C]
    {f : A → B → Option C} (hf : ωScottContinuous fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : ωScottContinuous g)
    : ωScottContinuous (fun x ↦ g x >>= f x) := by
  simp only [Option.bind_eq_bind]
  fun_prop

end OmegaCompletePartialOrder.Option
