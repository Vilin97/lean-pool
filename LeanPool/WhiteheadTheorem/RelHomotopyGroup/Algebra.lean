/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Bound
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Abel


/-!
TODO: Use `Pointed` (the category of pointed types) in Mathlib.
-/


/- A pointed map from `(X, x₀)` to `(Y, y₀)` is a function `f : X → Y` such that `f x₀ = y₀`. -/
/-- `IsPointedMap` -/
class IsPointedMap {X Y : Type*} [Inhabited X] [Inhabited Y] (f : X → Y) : Prop where
  map_default : f default = default

namespace IsPointedMap

variable {X Y : Type*} [Inhabited X] [Inhabited Y] (f : X → Y) [IsPointedMap f]

lemma default_mem_image_of_default_mem {A : Set X} : default ∈ A → default ∈ f '' A :=
  fun h ↦ (Set.mem_image _ _ _).mpr ⟨default, ⟨h, IsPointedMap.map_default⟩⟩

lemma default_mem_preimage_default : default ∈ f ⁻¹' {default} := by
  apply Set.mem_preimage.mpr
  rw [(IsPointedMap.map_default : f _ = _)]
  exact Set.mem_singleton _

lemma default_subset_preimage_default : {default} ⊆ f ⁻¹' {default} :=
  Set.singleton_subset_iff.mpr (default_mem_preimage_default _)

lemma default_eq_image_preimage_default : {default} = f '' (f ⁻¹' {default}) := by
  refine Set.Subset.antisymm ?_ (Set.image_preimage_subset f {default})
  apply Set.singleton_subset_iff.mpr
  apply default_mem_image_of_default_mem
  exact default_mem_preimage_default f

end IsPointedMap


namespace ExactSeq

/- The sequence `X --f-> Y --g-> Z` of pointed sets is said to be exact at `Y`
if `Ker g = Im f`. -/
/-- `IsExactAt` -/
def IsExactAt {X Y Z : Type*} [Inhabited Z]
    (f : X → Y) (g : Y → Z) : Prop :=
  g ⁻¹' {default} = Set.range f

lemma isExactAt_of_ker_supset_im_of_ker_subset_im
    {X Y Z : Type*} [Inhabited X] [Inhabited Y] [Inhabited Z]
    {f : X → Y} {g : Y → Z} [IsPointedMap f] [IsPointedMap g]
    (hsup : ∀ y, (∃ x, f x = y) → g y = default)
    (hsub : ∀ y, (g y = default) → ∃ x, f x = y) :
    IsExactAt f g := by
  apply Set.eq_of_subset_of_subset
  · intro y hy
    exact Set.mem_range.mpr <| hsub y <| Set.mem_preimage.mp hy
  · intro y hy
    exact Set.mem_preimage.mpr <| Set.mem_singleton_iff.mpr <| hsup y <| Set.mem_range.mp hy

/-!
Given an exact sequence
`A --a-> B --b-> C --c-> D --d-> E`
of five pointed sets, if `a` is surjective and `d` is injective, then `C = 0`.
*proof.*
- `Ker b = Im a = B` (since `a` is surjective)
- Hence `Im b = 0`
- `0 = Ker d = Im c` (since `d` is injective)
- Hence `Ker c = C`
- Use `Ker c = Im b` to conclude `C = 0`.
-/

variable {A B C D E : Type*}
variable [Inhabited A] [Inhabited B] [Inhabited C] [Inhabited D] [Inhabited E]

private lemma im_B_eq_zero (a : A → B) (b : B → C) (a_surj : Function.Surjective a)
    [IsPointedMap a] [IsPointedMap b] (exb : IsExactAt a b) :
    Set.range b = {default} := by
  rw [IsExactAt, Set.range_eq_univ.mpr a_surj] at exb
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x ∈ b ⁻¹' ({default} : Set C) := by
      rw [exb]
      exact Set.mem_univ x
    simpa using hx
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact ⟨default, IsPointedMap.map_default⟩

private lemma ker_c_eq_C (c : C → D) (d : D → E) (d_inj : Function.Injective d)
    [IsPointedMap c] [IsPointedMap d] (exd : IsExactAt c d) :
    c ⁻¹' {default} = Set.univ := by
  rw [IsExactAt] at exd
  have : d ⁻¹' {default} = {default} := by
    refine Set.Subset.antisymm ?_ (IsPointedMap.default_subset_preimage_default _)
    apply Set.subset_singleton_iff.mpr
    intro x hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    apply @d_inj x default
    rw [hx]
    exact Eq.symm IsPointedMap.map_default
  have : {default} = Set.range c := this.symm.trans exd
  apply Set.eq_univ_of_forall
  intro x
  have hx : c x ∈ Set.range c := ⟨x, rfl⟩
  rw [← this] at hx
  exact hx

/-- `C = {0}` if there is an exact sequence `A --a-> B --b-> C --c-> D --d-> E`
of five pointed sets such that `a` is surjective and `d` is injective. -/
theorem unique_mid_of_five (a : A → B) (b : B → C) (c : C → D) (d : D → E)
    [IsPointedMap a] [IsPointedMap b] [IsPointedMap c] [IsPointedMap d]
    (a_surj : Function.Surjective a) (d_inj : Function.Injective d)
    (exb : IsExactAt a b) (exc : IsExactAt b c) (exd : IsExactAt c d) :
    Nonempty (Unique C) :=
  Nonempty.intro <|
    { uniq := fun x ↦ by
        have h1 := im_B_eq_zero a b a_surj exb
        have h2 := ker_c_eq_C c d d_inj exd
        have h : @Set.univ C = {default} := h2.symm.trans exc |>.trans h1
        apply Set.eq_singleton_iff_unique_mem.mp h |>.right
        simp only [Set.mem_univ] }

end ExactSeq
