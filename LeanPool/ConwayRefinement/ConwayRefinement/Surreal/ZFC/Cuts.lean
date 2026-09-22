/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.ZFC.Basic
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Basic
public import Mathlib.Logic.Small.Set

import LeanPool.ConwayRefinement.CombinatorialGames.Game.Basic
import Mathlib.Data.Set.Image

/-!
# Small Conway cuts of class-coded surreal values

A small left set and a small right set of numeric ZFC game codes form a numeric code when every
left value is strictly below every right value. Its quotient value is the Conway cut of the option
values. Choosing numeric representatives therefore constructs cuts on arbitrary small sets of
class-coded surreal values, independently of the representative choices at the level of values.
-/

universe u

public noncomputable section

open Set

namespace ZFSet.GameCode

/-- Small separated sets of numeric codes form a numeric Conway cut. -/
theorem isNumeric_ofSets (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t]
    (hs : ∀ x ∈ s, IsNumeric x) (ht : ∀ x ∈ t, IsNumeric x)
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) : IsNumeric (ofSets s t) := by
  rw [isNumeric_iff_options]
  constructor
  · simpa only [moves_ofSets_left, moves_ofSets_right] using h
  · intro p x hx
    cases p with
    | left => exact hs x (by simpa only [moves_ofSets_left] using hx)
    | right => exact ht x (by simpa only [moves_ofSets_right] using hx)

end ZFSet.GameCode

namespace ZFSet.Surreal

/-- Quotienting numeric codes preserves their strict Conway comparison. -/
@[simp]
theorem mk_lt_mk (x y : GameCode.{u}) (hx : x.IsNumeric) (hy : y.IsNumeric) :
    mk x hx < mk y hy ↔ x < y := by
  let : IGame.Numeric x.toIGame := (GameCode.isNumeric_iff x).1 hx
  let : IGame.Numeric y.toIGame := (GameCode.isNumeric_iff y).1 hy
  rw [← toSurreal_lt_toSurreal, toSurreal_mk, toSurreal_mk,
    _root_.Surreal.mk_lt_mk, GameCode.toIGame_lt_toIGame]

/-- Quotienting numeric codes preserves their non-strict Conway comparison. -/
@[simp]
theorem mk_le_mk (x y : GameCode.{u}) (hx : x.IsNumeric) (hy : y.IsNumeric) :
    mk x hx ≤ mk y hy ↔ x ≤ y := by
  let : IGame.Numeric x.toIGame := (GameCode.isNumeric_iff x).1 hx
  let : IGame.Numeric y.toIGame := (GameCode.isNumeric_iff y).1 hy
  rw [← toSurreal_le_toSurreal, toSurreal_mk, toSurreal_mk,
    _root_.Surreal.mk_le_mk, GameCode.toIGame_le_toIGame]

/-- The class values represented by a set of numeric game codes. -/
def codeValues (s : Set GameCode.{u}) (hs : ∀ x ∈ s, x.IsNumeric) : Set Surreal.{u} :=
  Set.range fun x : s ↦ mk x.1 (hs x.1 x.2)

instance (s : Set GameCode.{u}) (hs : ∀ x ∈ s, x.IsNumeric) [Small.{u} s] :
    Small.{u} (codeValues s hs) :=
  inferInstanceAs (Small.{u} (Set.range fun x : s ↦ mk x.1 (hs x.1 x.2)))

@[simp]
theorem mem_codeValues {s : Set GameCode.{u}} {hs : ∀ x ∈ s, x.IsNumeric}
    {x : Surreal.{u}} : x ∈ codeValues s hs ↔ ∃ y, ∃ hy : y ∈ s, mk y (hs y hy) = x := by
  simp [codeValues]

/-- Strict separation of numeric code sets descends to their class values. -/
theorem codeValues_separated (s t : Set GameCode.{u})
    (hs : ∀ x ∈ s, x.IsNumeric) (ht : ∀ x ∈ t, x.IsNumeric)
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∀ x ∈ codeValues s hs, ∀ y ∈ codeValues t ht, x < y := by
  rintro _ ⟨⟨x, hx⟩, rfl⟩ _ ⟨⟨y, hy⟩, rfl⟩
  exact (mk_lt_mk x y (hs x hx) (ht y hy)).2 (h x hx y hy)

/-- Evaluation preserves separation of left and right sets of class values. -/
theorem toSurreal_separated (s t : Set Surreal.{u})
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∀ x ∈ toSurreal '' s, ∀ y ∈ toSurreal '' t, x < y := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (toSurreal_lt_toSurreal x y).2 (h x hx y hy)

/-- The quotient value of the raw Conway cut on separated numeric option codes. -/
def ofCodeSets (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t]
    (hs : ∀ x ∈ s, x.IsNumeric) (ht : ∀ x ∈ t, x.IsNumeric)
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) : Surreal.{u} :=
  mk (GameCode.ofSets s t) (GameCode.isNumeric_ofSets s t hs ht h)

/-- The class code cut is represented by the literal ZFC cut on its option codes. -/
theorem ofCodeSets_eq_mk (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t]
    (hs : ∀ x ∈ s, x.IsNumeric) (ht : ∀ x ∈ t, x.IsNumeric)
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ofCodeSets s t hs ht h =
      mk (GameCode.ofSets s t) (GameCode.isNumeric_ofSets s t hs ht h) := (rfl)

/-- Evaluating a raw numeric code cut gives the Conway cut of its evaluated option values. -/
theorem toSurreal_ofCodeSets (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t]
    (hs : ∀ x ∈ s, x.IsNumeric) (ht : ∀ x ∈ t, x.IsNumeric)
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    toSurreal (ofCodeSets s t hs ht h) =
      !{toSurreal '' codeValues s hs | toSurreal '' codeValues t ht}'
        (toSurreal_separated _ _ (codeValues_separated s t hs ht h)) := by
  apply _root_.Surreal.toGame_inj.1
  rw [ofCodeSets_eq_mk, toSurreal_mk, _root_.Surreal.toGame_mk,
    GameCode.toIGame_ofSets, Game.mk_ofSets, _root_.Surreal.toGame_ofSets]
  congr 1
  simp only [codeValues, Set.image_image, ← Set.range_comp, Function.comp_def,
    toSurreal_mk, _root_.Surreal.toGame_mk]
  simp only [Set.image_eq_range]

/-- Choose a numeric ZFC game code representing a class value. -/
def out (x : Surreal.{u}) : GameCode.{u} := Classical.choose (exists_mk x)

/-- The chosen representative of a class value is numeric. -/
theorem isNumeric_out (x : Surreal.{u}) : x.out.IsNumeric :=
  Classical.choose (Classical.choose_spec (exists_mk x))

@[simp]
theorem out_eq (x : Surreal.{u}) : mk x.out (isNumeric_out x) = x :=
  Classical.choose_spec (Classical.choose_spec (exists_mk x))

@[simp]
theorem out_lt_out (x y : Surreal.{u}) : x.out < y.out ↔ x < y := by
  rw [← mk_lt_mk x.out y.out (isNumeric_out x) (isNumeric_out y), out_eq, out_eq]

/-- Every code in the image of a set under the representative selection is numeric. -/
theorem out_image_numeric (s : Set Surreal.{u}) : ∀ x ∈ out '' s, x.IsNumeric := by
  rintro _ ⟨x, _, rfl⟩
  exact isNumeric_out x

/-- Selecting representatives preserves strict separation of two sets. -/
theorem out_image_separated (s t : Set Surreal.{u})
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ∀ x ∈ out '' s, ∀ y ∈ out '' t, x < y := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (out_lt_out x y).2 (h x hx y hy)

@[simp]
theorem codeValues_out_image (s : Set Surreal.{u}) :
    codeValues (out '' s) (out_image_numeric s) = s := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, hc, hcx⟩ := mem_codeValues.1 hx
    obtain ⟨y, hy, rfl⟩ := hc
    exact ((out_eq y).symm.trans hcx) ▸ hy
  · intro hx
    exact mem_codeValues.2 ⟨x.out, Set.mem_image_of_mem out hx, out_eq x⟩

/-- Construct a class-coded Conway cut using the raw cuts of chosen numeric representatives. -/
instance : OfSets Surreal.{u} (fun st ↦ ∀ x ∈ st Player.left,
    ∀ y ∈ st Player.right, x < y) where
  ofSets st h _ _ := ofCodeSets (out '' st Player.left) (out '' st Player.right)
    (out_image_numeric _) (out_image_numeric _)
    (out_image_separated _ _ h)

/-- The class cut is the quotient of the raw cut on chosen representative codes. -/
theorem ofSets_eq_ofCodeSets (s t : Set Surreal.{u}) [Small.{u} s] [Small.{u} t]
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    (!{s | t}'h : Surreal.{u}) = ofCodeSets (out '' s) (out '' t)
      (out_image_numeric s) (out_image_numeric t) (out_image_separated s t h) := (rfl)

/-- Evaluating an arbitrary small class cut gives the Conway cut of the evaluation images. -/
@[simp]
theorem toSurreal_ofSets (s t : Set Surreal.{u}) [Small.{u} s] [Small.{u} t]
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    toSurreal (!{s | t}'h) =
      !{toSurreal '' s | toSurreal '' t}'(toSurreal_separated s t h) := by
  rw [ofSets_eq_ofCodeSets, toSurreal_ofCodeSets]
  simp only [codeValues_out_image]

/-- A raw numeric code cut agrees with the class cut of its option values. -/
theorem ofCodeSets_eq_ofSets (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t]
    (hs : ∀ x ∈ s, x.IsNumeric) (ht : ∀ x ∈ t, x.IsNumeric)
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    ofCodeSets s t hs ht h =
      !{codeValues s hs | codeValues t ht}'(codeValues_separated s t hs ht h) := by
  apply toSurreal_injective
  rw [toSurreal_ofCodeSets, toSurreal_ofSets]

/-- Quotienting the literal ZFC cut is the same as cutting its quotient option values. -/
theorem mk_ofSets (s t : Set GameCode.{u}) [Small.{u} s] [Small.{u} t]
    (hs : ∀ x ∈ s, x.IsNumeric) (ht : ∀ x ∈ t, x.IsNumeric)
    (h : ∀ x ∈ s, ∀ y ∈ t, x < y) :
    mk (GameCode.ofSets s t) (GameCode.isNumeric_ofSets s t hs ht h) =
      !{codeValues s hs | codeValues t ht}'(codeValues_separated s t hs ht h) := by
  exact (ofCodeSets_eq_mk s t hs ht h).symm.trans (ofCodeSets_eq_ofSets s t hs ht h)

/-- Every left option value is strictly below the class cut. -/
theorem lt_ofSets_of_mem_left {s t : Set Surreal.{u}} [Small.{u} s] [Small.{u} t]
    {h : ∀ x ∈ s, ∀ y ∈ t, x < y} {x : Surreal.{u}} (hx : x ∈ s) :
    x < !{s | t}'h := by
  rw [← toSurreal_lt_toSurreal, toSurreal_ofSets]
  exact _root_.Surreal.lt_ofSets_of_mem_left (Set.mem_image_of_mem _ hx)

/-- The class cut is strictly below every right option value. -/
theorem ofSets_lt_of_mem_right {s t : Set Surreal.{u}} [Small.{u} s] [Small.{u} t]
    {h : ∀ x ∈ s, ∀ y ∈ t, x < y} {x : Surreal.{u}} (hx : x ∈ t) :
    !{s | t}'h < x := by
  rw [← toSurreal_lt_toSurreal, toSurreal_ofSets]
  exact _root_.Surreal.ofSets_lt_of_mem_right (Set.mem_image_of_mem _ hx)

end ZFSet.Surreal
