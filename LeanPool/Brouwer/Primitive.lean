/-
Copyright (c) 2026 Math_XMUM. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math_XMUM
-/
import LeanPool.Brouwer.Brouwer

/-!
# Primitive sets and the slack-vector form of Scarf's lemma

This file reformulates rooms and doors of an `IndexedLOrder` in terms of primitive
sets over the enlarged good set `T ⊕ I`, the "slack-vector" language of Scarf's
algorithm. It relates the room/door combinatorics developed in `Scarf` to this
primitive-set picture used by the path-following termination argument.
-/

attribute [local instance] Classical.propDecidable
open Finset


noncomputable section

namespace IndexedLOrder

variable {T I : Type*} [Inhabited T] [Fintype T] [Fintype I]
variable [DecidableEq T] [DecidableEq I] [IST : IndexedLOrder I T]

/-- The abstract enlargement `T ∪ I` used for Scarf's slack-vector language. -/
abbrev ExtendedGoods (T I : Type*) := Sum T I

/-- Turn a room `(σ, C)` into the corresponding primitive set `σ ∪ (I \ C)`. -/
def toPrimitiveSet (σ : Finset T) (C : Finset I) : Finset (ExtendedGoods T I) :=
  (σ.image Sum.inl) ∪ ((Finset.univ \ C).image Sum.inr)

/-- Turn a door `(τ, D)` into the corresponding almost primitive set `τ ∪ (I \ D)`. -/
def toAlmostPrimitive (τ : Finset T) (D : Finset I) : Finset (ExtendedGoods T I) :=
  toPrimitiveSet (I := I) τ D

/-- The goods part of a subset of `T ∪ I`. -/
def fromGoods (X : Finset (ExtendedGoods T I)) : Finset T :=
  Finset.univ.filter (fun t : T => Sum.inl t ∈ X)

/-- The indices whose slack vectors are missing from a subset of `T ∪ I`. -/
def fromMissing (X : Finset (ExtendedGoods T I)) : Finset I :=
  Finset.univ.filter (fun i : I => Sum.inr i ∉ X)

/-- The room/door cell associated to a subset of `T ∪ I`. -/
def associatedCell (X : Finset (ExtendedGoods T I)) : GiCell T I :=
  (fromGoods (T := T) (I := I) X, fromMissing (T := T) (I := I) X)

omit [Inhabited T] IST in
@[simp] lemma associatedCell_fst (X : Finset (ExtendedGoods T I)) :
    (associatedCell (T := T) (I := I) X).1 = fromGoods (T := T) (I := I) X := rfl

omit [Inhabited T] IST in
@[simp] lemma associatedCell_snd (X : Finset (ExtendedGoods T I)) :
    (associatedCell (T := T) (I := I) X).2 = fromMissing (T := T) (I := I) X := rfl

omit [Inhabited T] [Fintype T] IST in
@[simp] lemma mem_toPrimitiveSet_inl {σ : Finset T} {C : Finset I} {t : T} :
    Sum.inl t ∈ toPrimitiveSet (I := I) σ C ↔ t ∈ σ := by
  simp [toPrimitiveSet]

omit [Fintype T] IST in
@[simp] lemma mem_toPrimitiveSet_inr {σ : Finset T} {C : Finset I} {i : I} :
    Sum.inr i ∈ toPrimitiveSet (T := T) σ C ↔ i ∉ C := by
  simp [toPrimitiveSet]

omit [Inhabited T] [Fintype T] IST in
@[simp] lemma mem_toAlmostPrimitive_inl {τ : Finset T} {D : Finset I} {t : T} :
    Sum.inl t ∈ toAlmostPrimitive (I := I) τ D ↔ t ∈ τ := by
  simp [toAlmostPrimitive]

omit [Fintype T] IST in
@[simp] lemma mem_toAlmostPrimitive_inr {τ : Finset T} {D : Finset I} {i : I} :
    Sum.inr i ∈ toAlmostPrimitive (T := T) τ D ↔ i ∉ D := by
  simp [toAlmostPrimitive]

omit [Inhabited T] [Fintype I] IST in
@[simp] lemma mem_fromGoods {X : Finset (ExtendedGoods T I)} {t : T} :
    t ∈ fromGoods (T := T) (I := I) X ↔ Sum.inl t ∈ X := by
  simp [fromGoods]

omit [Inhabited T] [Fintype T] IST in
@[simp] lemma mem_fromMissing {X : Finset (ExtendedGoods T I)} {i : I} :
    i ∈ fromMissing (T := T) (I := I) X ↔ Sum.inr i ∉ X := by
  simp [fromMissing]

omit [Inhabited T] IST in
@[simp] lemma fromGoods_toPrimitiveSet (σ : Finset T) (C : Finset I) :
    fromGoods (T := T) (I := I) (toPrimitiveSet (I := I) σ C) = σ := by
  ext t
  simp

omit [Fintype T] IST in
@[simp] lemma fromMissing_toPrimitiveSet (σ : Finset T) (C : Finset I) :
    fromMissing (T := T) (I := I) (toPrimitiveSet (I := I) σ C) = C := by
  ext i
  simp

omit [Inhabited T] IST in
@[simp] lemma fromGoods_toAlmostPrimitive (τ : Finset T) (D : Finset I) :
    fromGoods (T := T) (I := I) (toAlmostPrimitive (I := I) τ D) = τ := by
  simp [toAlmostPrimitive]

omit [Fintype T] IST in
@[simp] lemma fromMissing_toAlmostPrimitive (τ : Finset T) (D : Finset I) :
    fromMissing (T := T) (I := I) (toAlmostPrimitive (I := I) τ D) = D := by
  simp [toAlmostPrimitive]

omit [Inhabited T] [Fintype T] IST in
lemma goods_slacks_disjoint (σ : Finset T) (C : Finset I) :
    Disjoint (σ.image Sum.inl) ((Finset.univ \ C).image Sum.inr) := by
  rw [Finset.disjoint_left]
  intro x hxGoods hxSlack
  rcases Finset.mem_image.mp hxGoods with ⟨t, _, rfl⟩
  rcases Finset.mem_image.mp hxSlack with ⟨i, _, h⟩
  cases h

omit [Inhabited T] [Fintype T] IST in
lemma card_toPrimitiveSet (σ : Finset T) (C : Finset I) :
    (toPrimitiveSet (I := I) σ C).card = σ.card + (Finset.univ \ C).card := by
  rw [toPrimitiveSet, Finset.card_union_of_disjoint (goods_slacks_disjoint σ C)]
  have hGoods : (σ.image (Sum.inl : T → ExtendedGoods T I)).card = σ.card := by
    apply Finset.card_image_of_injOn
    intro a _ b _ h
    exact Sum.inl.inj h
  have hSlacks :
      (((Finset.univ \ C).image (Sum.inr : I → ExtendedGoods T I)).card =
        (Finset.univ \ C).card) := by
    apply Finset.card_image_of_injOn
    intro a _ b _ h
    exact Sum.inr.inj h
  rw [hGoods, hSlacks]

omit [Inhabited T] IST in
lemma eq_toPrimitive_from_parts (X : Finset (ExtendedGoods T I)) :
    X = toPrimitiveSet (I := I)
      (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  ext x
  cases x with
  | inl t => simp
  | inr i => simp [toPrimitiveSet, fromMissing]

omit [Inhabited T] IST in
lemma eq_toAlmost_from_parts (X : Finset (ExtendedGoods T I)) :
    X = toAlmostPrimitive (I := I)
      (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  simpa [toAlmostPrimitive] using
    (eq_toPrimitive_from_parts (T := T) (I := I) X)

omit [Inhabited T] [Fintype T] in
lemma card_toPrimitiveSet_of_room {σ : Finset T} {C : Finset I} (hRoom : IST.isRoom σ C) :
    (toPrimitiveSet (I := I) σ C).card = Fintype.card I := by
  rw [card_toPrimitiveSet, ← hRoom.2, Finset.card_sdiff_of_subset (Finset.subset_univ C),
    Finset.card_univ]
  have hCle : C.card ≤ Fintype.card I := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ C)
  omega

omit [Inhabited T] [Fintype T] in
lemma card_toAlmostPrimitive_of_door {τ : Finset T} {D : Finset I} (hDoor : IST.isDoor τ D) :
    (toAlmostPrimitive (I := I) τ D).card + 1 = Fintype.card I := by
  rw [toAlmostPrimitive, card_toPrimitiveSet,
    Finset.card_sdiff_of_subset (Finset.subset_univ D), Finset.card_univ]
  have hDle : D.card ≤ Fintype.card I := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ D)
  omega

omit [Inhabited T] [Fintype T] IST in
lemma exists_insert_eq_of_subset_card_eq_succ {α : Type*} [DecidableEq α]
    {s t : Finset α} (hsub : s ⊆ t) (hcard : t.card = s.card + 1) :
    ∃ x, x ∉ s ∧ insert x s = t := by
  have hdiff_card : (t \ s).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, hcard]
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdiff_card
  have hxmem : x ∈ t \ s := by
    rw [hx]
    simp
  refine ⟨x, (Finset.mem_sdiff.mp hxmem).2, ?_⟩
  calc
    insert x s = {x} ∪ s := rfl
    _ = (t \ s) ∪ s := by rw [hx]
    _ = t := Finset.sdiff_union_of_subset hsub

/-- Primitive sets stated through the equivalent room language. -/
def isRoomPrimitive (X : Finset (ExtendedGoods T I)) : Prop :=
  ∃ σ C, IST.isRoom σ C ∧ X = toPrimitiveSet (I := I) σ C

/--
Scarf primitive sets in the paper's native dominance form, using the characterization
`X` primitive iff `X ∩ T` is dominant with respect to the missing slack indices.
-/
def isPrimitive (X : Finset (ExtendedGoods T I)) : Prop :=
  X.card = Fintype.card I ∧
    IST.isDominant (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X)

/-- Backwards-compatible name for the paper's native primitive definition. -/
abbrev isPrimitiveNative (X : Finset (ExtendedGoods T I)) : Prop :=
  isPrimitive (IST := IST) X

/-- Almost primitive sets, stated through the equivalent door language. -/
def isAlmostPrimitive (Y : Finset (ExtendedGoods T I)) : Prop :=
  ∃ τ D σ C,
    IST.isDoorof τ D σ C ∧
      Y = toAlmostPrimitive (I := I) τ D

/-- Almost primitive sets in the paper's native form: an `(n-1)`-face contained in a
primitive set. -/
def isAlmostPrimitiveNative (Y : Finset (ExtendedGoods T I)) : Prop :=
  Y.card + 1 = Fintype.card I ∧ ∃ X, isPrimitiveNative (IST := IST) X ∧ Y ⊆ X

omit [Inhabited T] [Fintype T] in
/-- A room gives the equivalent room-language primitive set. -/
lemma room_to_roomPrimitive {σ : Finset T} {C : Finset I} (h : IST.isRoom σ C) :
    isRoomPrimitive (IST := IST) (toPrimitiveSet (I := I) σ C) := by
  exact ⟨σ, C, h, rfl⟩

omit [Inhabited T] in
/-- Extract the room corresponding to a primitive set. -/
lemma primitive_to_room {X : Finset (ExtendedGoods T I)} (h : isPrimitive (IST := IST) X) :
    IST.isRoom (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  rcases h with ⟨hCard, hDom⟩
  let σ := fromGoods (T := T) (I := I) X
  let C := fromMissing (T := T) (I := I) X
  have hXcard : X.card = σ.card + (Finset.univ \ C).card := by
    rw [eq_toPrimitive_from_parts (T := T) (I := I) X, card_toPrimitiveSet]
  have hCcard : C.card = σ.card := by
    rw [hXcard, Finset.card_sdiff_of_subset (Finset.subset_univ C),
      Finset.card_univ] at hCard
    have hCle : C.card ≤ Fintype.card I := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ C)
    omega
  exact ⟨hDom, hCcard⟩

/-- A room gives a primitive set in the paper's native sense. -/
lemma room_to_primitive {σ : Finset T} {C : Finset I} (h : IST.isRoom σ C) :
    isPrimitive (IST := IST) (toPrimitiveSet (I := I) σ C) := by
  constructor
  · exact card_toPrimitiveSet_of_room h
  · simpa using h.1

/--
For sets written in room coordinates, being primitive is exactly being a room.
This is the cardinality condition implicit in the paper's comparison between
dominant sets and primitive sets.
-/
theorem isPrimitive_toPrimitiveSet_iff_room {σ : Finset T} {C : Finset I} :
    isPrimitive (IST := IST) (toPrimitiveSet (I := I) σ C) ↔ IST.isRoom σ C := by
  constructor
  · intro h
    simpa using primitive_to_room (IST := IST) h
  · exact room_to_primitive

omit [Inhabited T] in
lemma primitive_eq_toPrimitive_from_parts {X : Finset (ExtendedGoods T I)}
    (_h : isPrimitive (IST := IST) X) :
    X = toPrimitiveSet (I := I)
      (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  exact eq_toPrimitive_from_parts X

/-- A room recovered from a primitive set is again primitive. -/
lemma primitive_from_parts {X : Finset (ExtendedGoods T I)}
    (h : isPrimitive (IST := IST) X) :
    isPrimitive (IST := IST)
      (toPrimitiveSet (I := I)
        (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X)) := by
  exact room_to_primitive (primitive_to_room h)

lemma primitive_to_nativePrimitive {X : Finset (ExtendedGoods T I)}
    (h : isRoomPrimitive (IST := IST) X) :
    isPrimitiveNative (IST := IST) X := by
  constructor
  · rcases h with ⟨σ, C, hRoom, rfl⟩
    exact card_toPrimitiveSet_of_room hRoom
  · rcases h with ⟨σ, C, hRoom, rfl⟩
    simpa using hRoom.1

omit [Inhabited T] in
lemma nativePrimitive_to_primitive {X : Finset (ExtendedGoods T I)}
    (h : isPrimitiveNative (IST := IST) X) :
    isRoomPrimitive (IST := IST) X := by
  rcases h with ⟨hCard, hDom⟩
  let σ := fromGoods (T := T) (I := I) X
  let C := fromMissing (T := T) (I := I) X
  have hXcard : X.card = σ.card + (Finset.univ \ C).card := by
    rw [eq_toPrimitive_from_parts (T := T) (I := I) X, card_toPrimitiveSet]
  have hCcard : C.card = σ.card := by
    rw [hXcard, Finset.card_sdiff_of_subset (Finset.subset_univ C),
      Finset.card_univ] at hCard
    have hCle : C.card ≤ Fintype.card I := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.subset_univ C)
    omega
  have hRoom : IST.isRoom σ C := ⟨hDom, hCcard⟩
  rw [eq_toPrimitive_from_parts (T := T) (I := I) X]
  exact room_to_roomPrimitive hRoom

theorem isPrimitive_iff_native {X : Finset (ExtendedGoods T I)} :
    isRoomPrimitive (IST := IST) X ↔ isPrimitiveNative (IST := IST) X :=
  ⟨primitive_to_nativePrimitive, nativePrimitive_to_primitive⟩

omit [Inhabited T] [Fintype T] in
/-- A door of a room gives an almost primitive set. -/
lemma door_to_almostPrimitive {τ σ : Finset T} {D C : Finset I}
    (h : IST.isDoorof τ D σ C) :
    isAlmostPrimitive (IST := IST) (toAlmostPrimitive (I := I) τ D) := by
  exact ⟨τ, D, σ, C, h, rfl⟩

/-- Recover the door represented by an almost primitive set. -/
lemma almostPrimitive_to_door {Y : Finset (ExtendedGoods T I)}
    (h : isAlmostPrimitive (IST := IST) Y) :
    IST.isDoor (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y) := by
  rcases h with ⟨τ, D, σ, C, hDoor, rfl⟩
  cases hDoor with
  | idoor _ hD _ _ _ _ => simpa using hD
  | odoor _ hD _ _ _ _ => simpa using hD

/-- Recover a room incident to an almost primitive set. -/
lemma almostPrimitive_incident_room {Y : Finset (ExtendedGoods T I)}
    (h : isAlmostPrimitive (IST := IST) Y) :
    ∃ σ C,
      IST.isDoorof (fromGoods (T := T) (I := I) Y)
        (fromMissing (T := T) (I := I) Y) σ C := by
  rcases h with ⟨τ, D, σ, C, hDoor, rfl⟩
  exact ⟨σ, C, by simpa using hDoor⟩

omit [Fintype T] in
/-- Incidence of doors and rooms becomes subset inclusion of the corresponding sets. -/
lemma doorof_toAlmost_subset_toPrimitive {τ σ : Finset T} {D C : Finset I}
    (h : IST.isDoorof τ D σ C) :
    toAlmostPrimitive (I := I) τ D ⊆ toPrimitiveSet (I := I) σ C := by
  intro z hz
  cases z with
  | inl t =>
      cases h with
      | idoor _ _ _ _ hInsert hD =>
          rw [mem_toAlmostPrimitive_inl] at hz
          rw [mem_toPrimitiveSet_inl]
          rw [← hInsert]
          exact Finset.mem_insert_of_mem hz
      | odoor _ _ _ hNot hτ hD =>
          rw [mem_toAlmostPrimitive_inl] at hz
          rw [mem_toPrimitiveSet_inl]
          rwa [← hτ]
  | inr i =>
      cases h with
      | idoor _ _ _ _ hInsert hD =>
          rw [mem_toAlmostPrimitive_inr] at hz
          rw [mem_toPrimitiveSet_inr]
          rwa [hD] at hz
      | odoor _ _ j hNot hτ hD =>
          rw [mem_toAlmostPrimitive_inr] at hz
          rw [mem_toPrimitiveSet_inr]
          rw [hD] at hz
          exact fun hiC => hz (Finset.mem_insert_of_mem hiC)

/-- A useful packaged form of the door/primitive-set incidence correspondence. -/
lemma doorof_iff_subset_primitive {τ σ : Finset T} {D C : Finset I} :
    IST.isDoorof τ D σ C →
      IST.isRoom σ C ∧
        isAlmostPrimitive (IST := IST) (toAlmostPrimitive (I := I) τ D) ∧
          isPrimitive (IST := IST) (toPrimitiveSet (I := I) σ C) ∧
            toAlmostPrimitive (I := I) τ D ⊆ toPrimitiveSet (I := I) σ C := by
  intro h
  have hRoom : IST.isRoom σ C := IST.isRoom_of_Door h
  exact ⟨hRoom, door_to_almostPrimitive h, room_to_primitive hRoom,
    doorof_toAlmost_subset_toPrimitive h⟩

omit [Inhabited T] in
lemma almostPrimitive_eq_toAlmost_from_parts {Y : Finset (ExtendedGoods T I)}
    (_h : isAlmostPrimitive (IST := IST) Y) :
    Y = toAlmostPrimitive (I := I)
      (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y) := by
  exact eq_toAlmost_from_parts Y

omit [Fintype T] in
lemma subset_toPrimitive_toAlmost_doorof {τ σ : Finset T} {D C : Finset I}
    (hDoor : IST.isDoor τ D) (hRoom : IST.isRoom σ C)
    (hsub : toAlmostPrimitive (I := I) τ D ⊆ toPrimitiveSet (I := I) σ C) :
    IST.isDoorof τ D σ C := by
  have hτsub : τ ⊆ σ := by
    intro t ht
    have hmem : Sum.inl t ∈ toPrimitiveSet (I := I) σ C :=
      hsub (by simpa using ht)
    simpa using hmem
  have hCsubD : C ⊆ D := by
    intro i hiC
    by_contra hiD
    have hmem : Sum.inr i ∈ toPrimitiveSet (T := T) σ C :=
      hsub (by simpa using hiD)
    have hiNotC : i ∉ C := by simpa using hmem
    exact hiNotC hiC
  have hτleσ : τ.card ≤ σ.card := Finset.card_le_card hτsub
  have hσleτsucc : σ.card ≤ τ.card + 1 := by
    calc
      σ.card = C.card := hRoom.2.symm
      _ ≤ D.card := Finset.card_le_card hCsubD
      _ = τ.card + 1 := hDoor.2
  have hCases : σ.card = τ.card ∨ σ.card = τ.card + 1 := by
    omega
  cases hCases with
  | inl hEq =>
      have hτσ : τ = σ := Finset.eq_of_subset_of_card_le hτsub (by omega)
      have hDcard : D.card = C.card + 1 := by
        omega
      obtain ⟨j, hjC, hjInsert⟩ := exists_insert_eq_of_subset_card_eq_succ hCsubD hDcard
      apply isDoorof.odoor hRoom.1 hDoor j hjC
      · exact hτσ
      · exact hjInsert.symm
  | inr hSucc =>
      have hCD : C = D := by
        apply Finset.eq_of_subset_of_card_le hCsubD
        omega
      obtain ⟨x, hxτ, hxInsert⟩ := exists_insert_eq_of_subset_card_eq_succ hτsub hSucc
      apply isDoorof.idoor hRoom.1 hDoor x hxτ
      · exact hxInsert
      · exact hCD.symm

lemma nativeAlmostPrimitive_to_almostPrimitive {Y : Finset (ExtendedGoods T I)}
    (h : isAlmostPrimitiveNative (IST := IST) Y) :
    isAlmostPrimitive (IST := IST) Y := by
  rcases h with ⟨hcard, X, hPrim, hsub⟩
  rcases nativePrimitive_to_primitive hPrim with ⟨σ, C, hRoom, rfl⟩
  let τ := fromGoods (T := T) (I := I) Y
  let D := fromMissing (T := T) (I := I) Y
  have hYeq : Y = toAlmostPrimitive (I := I) τ D := eq_toAlmost_from_parts Y
  have hτsub : τ ⊆ σ := by
    intro t ht
    have hy : Sum.inl t ∈ Y := by simpa [τ] using ht
    have hx : Sum.inl t ∈ toPrimitiveSet (I := I) σ C := hsub hy
    simpa using hx
  have hCsubD : C ⊆ D := by
    intro i hiC
    rw [mem_fromMissing]
    intro hy
    have hx : Sum.inr i ∈ toPrimitiveSet (T := T) σ C := hsub hy
    have hiNotC : i ∉ C := by simpa using hx
    exact hiNotC hiC
  have hCell : IST.isCell τ D := by
    exact IST.Dominant_of_supset τ C D hCsubD
      (IST.Dominant_of_subset σ τ C hτsub hRoom.1)
  have hDoor : IST.isDoor τ D := by
    constructor
    · exact hCell
    · have hYcard :
          Y.card = τ.card + (Finset.univ \ D).card := by
        rw [hYeq, toAlmostPrimitive, card_toPrimitiveSet]
      rw [hYcard, Finset.card_sdiff_of_subset (Finset.subset_univ D),
        Finset.card_univ] at hcard
      have hDle : D.card ≤ Fintype.card I := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.subset_univ D)
      omega
  have hsubParts : toAlmostPrimitive (I := I) τ D ⊆ toPrimitiveSet (I := I) σ C := by
    rw [← hYeq]
    exact hsub
  exact ⟨τ, D, σ, C, subset_toPrimitive_toAlmost_doorof hDoor hRoom hsubParts, hYeq⟩

lemma almostPrimitive_to_nativeAlmostPrimitive {Y : Finset (ExtendedGoods T I)}
    (h : isAlmostPrimitive (IST := IST) Y) :
    isAlmostPrimitiveNative (IST := IST) Y := by
  rcases h with ⟨τ, D, σ, C, hDoorof, rfl⟩
  have hDoor : IST.isDoor τ D := by
    cases hDoorof with
    | idoor _ hD _ _ _ _ => exact hD
    | odoor _ hD _ _ _ _ => exact hD
  have hRoom : IST.isRoom σ C := IST.isRoom_of_Door hDoorof
  constructor
  · exact card_toAlmostPrimitive_of_door hDoor
  · exact ⟨toPrimitiveSet (I := I) σ C, room_to_primitive hRoom,
      doorof_toAlmost_subset_toPrimitive hDoorof⟩

theorem isAlmostPrimitive_iff_native {Y : Finset (ExtendedGoods T I)} :
    isAlmostPrimitive (IST := IST) Y ↔ isAlmostPrimitiveNative (IST := IST) Y :=
  ⟨almostPrimitive_to_nativeAlmostPrimitive, nativeAlmostPrimitive_to_almostPrimitive⟩

/--
Scarf's main lemma for internal almost primitive sets, in the room/door
language: an internal almost primitive face is contained in two distinct
primitive sets.
-/
theorem internal_almostPrimitive_two_incident_primitives {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y)
    (hInternal : (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃ X₁ X₂ : Finset (ExtendedGoods T I),
      X₁ ≠ X₂ ∧
        isPrimitive (IST := IST) X₁ ∧
        isPrimitive (IST := IST) X₂ ∧
        Y ⊆ X₁ ∧
        Y ⊆ X₂ := by
  let τ := fromGoods (T := T) (I := I) Y
  let D := fromMissing (T := T) (I := I) Y
  have hDoor : IST.isDoor τ D := almostPrimitive_to_door hY
  obtain ⟨σ₁, σ₂, C₁, C₂, hNe, hRoom₁, hRoom₂, hDoor₁, hDoor₂, _hUnique⟩ :=
    IST.internal_door_two_rooms τ D ⟨hDoor, hInternal⟩
  let X₁ := toPrimitiveSet (I := I) σ₁ C₁
  let X₂ := toPrimitiveSet (I := I) σ₂ C₂
  refine ⟨X₁, X₂, ?_, room_to_primitive hRoom₁, room_to_primitive hRoom₂, ?_, ?_⟩
  · intro hEq
    have hσ : σ₁ = σ₂ := by
      have := congrArg (fromGoods (T := T) (I := I)) hEq
      simpa [X₁, X₂] using this
    have hC : C₁ = C₂ := by
      have := congrArg (fromMissing (T := T) (I := I)) hEq
      simpa [X₁, X₂] using this
    exact hNe (by simp [hσ, hC])
  · rw [almostPrimitive_eq_toAlmost_from_parts hY]
    exact doorof_toAlmost_subset_toPrimitive hDoor₁
  · rw [almostPrimitive_eq_toAlmost_from_parts hY]
    exact doorof_toAlmost_subset_toPrimitive hDoor₂

theorem internal_almostPrimitive_exactly_two_incident_primitives
    {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y)
    (hInternal : (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃ X₁ X₂ : Finset (ExtendedGoods T I),
      X₁ ≠ X₂ ∧
        isPrimitive (IST := IST) X₁ ∧
        isPrimitive (IST := IST) X₂ ∧
        Y ⊆ X₁ ∧
        Y ⊆ X₂ ∧
        ∀ X, isPrimitive (IST := IST) X → Y ⊆ X → X = X₁ ∨ X = X₂ := by
  let τ := fromGoods (T := T) (I := I) Y
  let D := fromMissing (T := T) (I := I) Y
  have hDoor : IST.isDoor τ D := almostPrimitive_to_door hY
  obtain ⟨σ₁, σ₂, C₁, C₂, hNe, hRoom₁, hRoom₂, hDoor₁, hDoor₂, hUnique⟩ :=
    IST.internal_door_two_rooms τ D ⟨hDoor, hInternal⟩
  let X₁ := toPrimitiveSet (I := I) σ₁ C₁
  let X₂ := toPrimitiveSet (I := I) σ₂ C₂
  refine ⟨X₁, X₂, ?_, room_to_primitive hRoom₁, room_to_primitive hRoom₂, ?_, ?_, ?_⟩
  · intro hEq
    have hσ : σ₁ = σ₂ := by
      have := congrArg (fromGoods (T := T) (I := I)) hEq
      simpa [X₁, X₂] using this
    have hC : C₁ = C₂ := by
      have := congrArg (fromMissing (T := T) (I := I)) hEq
      simpa [X₁, X₂] using this
    exact hNe (by simp [hσ, hC])
  · rw [almostPrimitive_eq_toAlmost_from_parts hY]
    exact doorof_toAlmost_subset_toPrimitive hDoor₁
  · rw [almostPrimitive_eq_toAlmost_from_parts hY]
    exact doorof_toAlmost_subset_toPrimitive hDoor₂
  · intro X hX hSub
    have hDoorX :
        IST.isDoorof τ D (fromGoods (T := T) (I := I) X)
          (fromMissing (T := T) (I := I) X) := by
      have hRoomX : IST.isRoom (fromGoods (T := T) (I := I) X)
          (fromMissing (T := T) (I := I) X) := primitive_to_room hX
      apply subset_toPrimitive_toAlmost_doorof hDoor hRoomX
      rw [← almostPrimitive_eq_toAlmost_from_parts hY, ← primitive_eq_toPrimitive_from_parts hX]
      exact hSub
    have hRoomX : IST.isRoom (fromGoods (T := T) (I := I) X)
        (fromMissing (T := T) (I := I) X) := primitive_to_room hX
    obtain hLeft | hRight := hUnique
      (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) hRoomX hDoorX
    · left
      rw [primitive_eq_toPrimitive_from_parts hX, hLeft.1, hLeft.2]
    · right
      rw [primitive_eq_toPrimitive_from_parts hX, hRight.1, hRight.2]

theorem native_internal_almostPrimitive_exactly_two_incident_primitives
    {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitiveNative (IST := IST) Y)
    (hInternal : (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃ X₁ X₂ : Finset (ExtendedGoods T I),
      X₁ ≠ X₂ ∧
        isPrimitiveNative (IST := IST) X₁ ∧
        isPrimitiveNative (IST := IST) X₂ ∧
        Y ⊆ X₁ ∧
        Y ⊆ X₂ ∧
        ∀ X, isPrimitiveNative (IST := IST) X → Y ⊆ X → X = X₁ ∨ X = X₂ := by
  have hY' : isAlmostPrimitive (IST := IST) Y :=
    nativeAlmostPrimitive_to_almostPrimitive hY
  obtain ⟨X₁, X₂, hNe, hPrim₁, hPrim₂, hSub₁, hSub₂, hUnique⟩ :=
    internal_almostPrimitive_exactly_two_incident_primitives hY' hInternal
  exact ⟨X₁, X₂, hNe, hPrim₁, hPrim₂, hSub₁, hSub₂, fun X hX hSub =>
    hUnique X hX hSub⟩
/--
Native Scarf main lemma in the "remove one point" form: after removing a
point from a primitive set, either the resulting face lies in the slack
boundary, or there is a unique other primitive set containing that face.
-/
theorem native_primitive_erase_mainLemma
    {X : Finset (ExtendedGoods T I)} (hX : isPrimitiveNative (IST := IST) X)
    {x : ExtendedGoods T I} (hx : x ∈ X) :
    ¬ (fromGoods (T := T) (I := I) (X.erase x)).Nonempty ∨
      ∃! X' : Finset (ExtendedGoods T I),
        isPrimitiveNative (IST := IST) X' ∧
          X.erase x ⊆ X' ∧ X' ≠ X := by
  let Y := X.erase x
  have hYnative : isAlmostPrimitiveNative (IST := IST) Y := by
    constructor
    · have hcardErase : Y.card + 1 = X.card := by
        change (X.erase x).card + 1 = X.card
        rw [Finset.card_erase_of_mem hx]
        have hpos : 0 < X.card := Finset.card_pos.mpr ⟨x, hx⟩
        omega
      exact hcardErase.trans hX.1
    · exact ⟨X, hX, Finset.erase_subset x X⟩
  by_cases hInternal : (fromGoods (T := T) (I := I) Y).Nonempty
  · right
    obtain ⟨X₁, X₂, hNe, hPrim₁, hPrim₂, hSub₁, hSub₂, hUnique⟩ :=
      native_internal_almostPrimitive_exactly_two_incident_primitives hYnative hInternal
    have hXmem := hUnique X hX (Finset.erase_subset x X)
    rcases hXmem with hXX₁ | hXX₂
    · refine ⟨X₂, ⟨hPrim₂, hSub₂, ?_⟩, ?_⟩
      · intro hX₂
        exact hNe (hXX₁.symm.trans hX₂.symm)
      · intro Z hZ
        rcases hZ with ⟨hPrimZ, hSubZ, hZneX⟩
        rcases hUnique Z hPrimZ hSubZ with hZ₁ | hZ₂
        · exfalso
          exact hZneX (hZ₁.trans hXX₁.symm)
        · exact hZ₂
    · refine ⟨X₁, ⟨hPrim₁, hSub₁, ?_⟩, ?_⟩
      · intro hX₁
        exact hNe (hX₁.trans hXX₂)
      · intro Z hZ
        rcases hZ with ⟨hPrimZ, hSubZ, hZneX⟩
        rcases hUnique Z hPrimZ hSubZ with hZ₁ | hZ₂
        · exact hZ₁
        · exfalso
          exact hZneX (hZ₂.trans hXX₂.symm)
  · left
    exact hInternal

/--
Scarf's main lemma in the paper's replacement form: after removing `x` from
a primitive set `X`, either only slack vectors remain, or there is a unique
new element `y ∉ X` such that `X - x + y` is primitive.
-/
theorem native_primitive_erase_replacement_mainLemma
    {X : Finset (ExtendedGoods T I)} (hX : isPrimitiveNative (IST := IST) X)
    {x : ExtendedGoods T I} (hx : x ∈ X) :
    ¬ (fromGoods (T := T) (I := I) (X.erase x)).Nonempty ∨
      ∃! y : ExtendedGoods T I,
        y ∉ X ∧ isPrimitiveNative (IST := IST) (insert y (X.erase x)) := by
  let Y := X.erase x
  have hYcard : Y.card + 1 = Fintype.card I := by
    change (X.erase x).card + 1 = Fintype.card I
    rw [Finset.card_erase_of_mem hx]
    have hpos : 0 < X.card := Finset.card_pos.mpr ⟨x, hx⟩
    have hle : 1 ≤ X.card := Nat.succ_le_iff.mpr hpos
    rw [Nat.sub_add_cancel hle, hX.1]
  obtain hBoundary | hOther := native_primitive_erase_mainLemma (IST := IST) hX hx
  · exact Or.inl hBoundary
  · right
    rcases hOther with ⟨X', ⟨hPrimX', hSub, hNe⟩, hUniqueX⟩
    have hX'card : X'.card = Y.card + 1 := by
      rw [hPrimX'.1, hYcard]
    obtain ⟨y, hyNotY, hyInsert⟩ := exists_insert_eq_of_subset_card_eq_succ hSub hX'card
    have hyNotX : y ∉ X := by
      intro hyX
      have hyx : y = x := by
        by_contra hyNe
        exact hyNotY (Finset.mem_erase.mpr ⟨hyNe, hyX⟩)
      subst hyx
      have hX'eqX : X' = X := by
        rw [← hyInsert]
        simp [hx]
      exact hNe hX'eqX
    refine ⟨y, ⟨hyNotX, ?_⟩, ?_⟩
    · rw [hyInsert]
      exact hPrimX'
    · intro z hz
      rcases hz with ⟨hzNotX, hzPrim⟩
      have hNez : insert z Y ≠ X := by
        intro hEq
        have hzX : z ∈ X := by
          rw [← hEq]
          exact Finset.mem_insert_self z Y
        exact hzNotX hzX
      have hEqToX' : insert z Y = X' :=
        hUniqueX (insert z Y) ⟨hzPrim, Finset.subset_insert z Y, hNez⟩
      have hEqInsert : insert z Y = insert y Y := hEqToX'.trans hyInsert.symm
      have hzNotY : z ∉ Y := fun hzY => hzNotX (Finset.erase_subset x X hzY)
      have hzMem : z ∈ insert y Y := by
        rw [← hEqInsert]
        exact Finset.mem_insert_self z Y
      rw [Finset.mem_insert] at hzMem
      rcases hzMem with hzy | hzY
      · exact hzy
      · exact False.elim (hzNotY hzY)

/-- The boundary almost primitive set made only of slacks, missing `i`. -/
def slackBoundary (i : I) : Finset (ExtendedGoods T I) :=
  toAlmostPrimitive (T := T) (Finset.empty : Finset T) ({i} : Finset I)

omit [Inhabited T] IST in
@[simp] lemma fromGoods_slackBoundary (i : I) :
    fromGoods (T := T) (I := I) (slackBoundary (T := T) (I := I) i) =
      (Finset.empty : Finset T) := by
  simp [slackBoundary]

omit [Fintype T] IST in
@[simp] lemma fromMissing_slackBoundary (i : I) :
    fromMissing (T := T) (I := I) (slackBoundary (T := T) (I := I) i) =
      ({i} : Finset I) := by
  simp [slackBoundary]

omit IST in
@[simp] lemma associatedCell_slackBoundary (i : I) :
    associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i) =
      ((Finset.empty : Finset T), ({i} : Finset I)) := by
  ext <;> simp

omit [Fintype T] in
/-- Each slack boundary is an almost primitive set. -/
lemma slackBoundary_isAlmostPrimitive [Finite T] (i : I) :
    isAlmostPrimitive (IST := IST) (slackBoundary (T := T) (I := I) i) := by
  have : Fintype T := Fintype.ofFinite T
  have hOutside : IST.isOutsideDoor (Finset.empty : Finset T) ({i} : Finset I) :=
    IST.outsidedoor_singleton i
  let xMax : T := @Finset.max' T (IST i) Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨(default : T)⟩)
  have hCell : IST.isCell ({xMax} : Finset T) ({i} : Finset I) := by
    intro y
    refine ⟨i, by simp, ?_⟩
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
  have hDoorof : IST.isDoorof (Finset.empty : Finset T) ({i} : Finset I)
      ({xMax} : Finset T) ({i} : Finset I) := by
    apply isDoorof.idoor hCell hOutside.1 xMax
    · exact Finset.notMem_empty xMax
    · rfl
    · rfl
  exact door_to_almostPrimitive hDoorof

lemma slackBoundary_isAlmostPrimitiveNative (i : I) :
    isAlmostPrimitiveNative (IST := IST) (slackBoundary (T := T) (I := I) i) :=
  almostPrimitive_to_nativeAlmostPrimitive (slackBoundary_isAlmostPrimitive (IST := IST) i)

lemma slackBoundary_unique_incident_primitive (i : I) :
    ∃! X : Finset (ExtendedGoods T I),
      isPrimitive (IST := IST) X ∧ slackBoundary (T := T) (I := I) i ⊆ X := by
  let xMax : T := @Finset.max' T (IST i) Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨(default : T)⟩)
  let X₀ := toPrimitiveSet (I := I) ({xMax} : Finset T) ({i} : Finset I)
  have hOutside : IST.isOutsideDoor (Finset.empty : Finset T) ({i} : Finset I) :=
    IST.outsidedoor_singleton i
  have hCell : IST.isCell ({xMax} : Finset T) ({i} : Finset I) := by
    intro y
    refine ⟨i, by simp, ?_⟩
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
  have hDoorof₀ : IST.isDoorof (Finset.empty : Finset T) ({i} : Finset I)
      ({xMax} : Finset T) ({i} : Finset I) := by
    apply isDoorof.idoor hCell hOutside.1 xMax
    · exact Finset.notMem_empty xMax
    · rfl
    · rfl
  have hRoom₀ : IST.isRoom ({xMax} : Finset T) ({i} : Finset I) := IST.isRoom_of_Door hDoorof₀
  refine ⟨X₀, ⟨room_to_primitive hRoom₀, ?_⟩, ?_⟩
  · exact doorof_toAlmost_subset_toPrimitive hDoorof₀
  · intro X hX
    rcases hX with ⟨hPrim, hSub⟩
    rcases nativePrimitive_to_primitive hPrim with ⟨σ, C, hRoom, rfl⟩
    have hDoorof : IST.isDoorof (Finset.empty : Finset T) ({i} : Finset I) σ C :=
      subset_toPrimitive_toAlmost_doorof hOutside.1 hRoom hSub
    cases hDoorof with
    | idoor hCellσC _ x _ hInsert hD_eq =>
        have hσ : σ = ({x} : Finset T) := by
          rw [← hInsert]
          rfl
        have hC : C = ({i} : Finset I) := hD_eq.symm
        have hx_eq : x = xMax := by
          have hAbove : ∀ y : T, (IST i).le y x := by
            intro y
            obtain ⟨j, hj, hle⟩ := hCellσC y
            have hji : j = i := by
              rw [hC] at hj
              exact Finset.mem_singleton.mp hj
            subst hji
            apply hle
            rw [hσ]
            simp
          have hx_le_max : (IST i).le x xMax :=
            @Finset.le_max' T (IST i) Finset.univ x (Finset.mem_univ x)
          have hmax_le_x : (IST i).le xMax x := hAbove xMax
          exact @le_antisymm T (IST i).toPartialOrder x xMax hx_le_max hmax_le_x
        rw [hσ, hC, hx_eq]
    | odoor _ _ j _ hτ_eq _ =>
        exfalso
        have hσNonempty : σ.Nonempty := IST.sigma_nonempty_of_room hRoom
        rw [← hτ_eq] at hσNonempty
        exact Finset.not_nonempty_empty hσNonempty

lemma slackBoundary_unique_incident_nativePrimitive (i : I) :
    ∃! X : Finset (ExtendedGoods T I),
      isPrimitiveNative (IST := IST) X ∧ slackBoundary (T := T) (I := I) i ⊆ X := by
  rcases slackBoundary_unique_incident_primitive (IST := IST) i with ⟨X, hX, hUnique⟩
  refine ⟨X, hX, ?_⟩
  intro Y hY
  exact hUnique Y hY

/--
Every almost primitive face made only of slack vectors is one of the boundary
faces `I - i`.
-/
lemma boundary_almostPrimitive_eq_slackBoundary {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y)
    (hBoundary : ¬ (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃ i : I, Y = slackBoundary (T := T) (I := I) i := by
  have hGoods : fromGoods (T := T) (I := I) Y = Finset.empty :=
    Finset.not_nonempty_iff_eq_empty.mp hBoundary
  have hDoor : IST.isDoor (fromGoods (T := T) (I := I) Y)
      (fromMissing (T := T) (I := I) Y) :=
    almostPrimitive_to_door hY
  have hDcard : (fromMissing (T := T) (I := I) Y).card = 1 := by
    have hDoorCard := hDoor.2
    rw [hGoods] at hDoorCard
    have hEmpty : (Finset.empty : Finset T).card = 0 := rfl
    rw [hEmpty] at hDoorCard
    simpa using hDoorCard
  obtain ⟨i, hD⟩ := Finset.card_eq_one.mp hDcard
  refine ⟨i, ?_⟩
  rw [almostPrimitive_eq_toAlmost_from_parts hY, hGoods, hD]
  rfl

/--
Boundary almost primitive faces are incident to exactly one primitive set.
-/
theorem boundary_almostPrimitive_unique_incident_primitive
    {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y)
    (hBoundary : ¬ (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃! X : Finset (ExtendedGoods T I), isPrimitive (IST := IST) X ∧ Y ⊆ X := by
  obtain ⟨i, hYeq⟩ := boundary_almostPrimitive_eq_slackBoundary (IST := IST) hY hBoundary
  rw [hYeq]
  exact slackBoundary_unique_incident_primitive (IST := IST) i

theorem native_boundary_almostPrimitive_unique_incident_primitive
    {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitiveNative (IST := IST) Y)
    (hBoundary : ¬ (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃! X : Finset (ExtendedGoods T I), isPrimitiveNative (IST := IST) X ∧ Y ⊆ X :=
  boundary_almostPrimitive_unique_incident_primitive
    (IST := IST) (nativeAlmostPrimitive_to_almostPrimitive hY) hBoundary

/--
The full Scarf incidence dichotomy for almost primitive faces: a boundary face
is incident to one primitive set, while an internal face is incident to exactly
two primitive sets.
-/
theorem almostPrimitive_incident_primitives_boundary_or_internal
    {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y) :
    (¬ (fromGoods (T := T) (I := I) Y).Nonempty ∧
      ∃! X : Finset (ExtendedGoods T I), isPrimitive (IST := IST) X ∧ Y ⊆ X) ∨
    ((fromGoods (T := T) (I := I) Y).Nonempty ∧
      ∃ X₁ X₂ : Finset (ExtendedGoods T I),
        X₁ ≠ X₂ ∧
          isPrimitive (IST := IST) X₁ ∧
          isPrimitive (IST := IST) X₂ ∧
          Y ⊆ X₁ ∧
          Y ⊆ X₂ ∧
          ∀ X, isPrimitive (IST := IST) X → Y ⊆ X → X = X₁ ∨ X = X₂) := by
  by_cases hInternal : (fromGoods (T := T) (I := I) Y).Nonempty
  · right
    exact ⟨hInternal, internal_almostPrimitive_exactly_two_incident_primitives hY hInternal⟩
  · left
    exact ⟨hInternal, boundary_almostPrimitive_unique_incident_primitive hY hInternal⟩

theorem native_almostPrimitive_incident_primitives_boundary_or_internal
    {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitiveNative (IST := IST) Y) :
    (¬ (fromGoods (T := T) (I := I) Y).Nonempty ∧
      ∃! X : Finset (ExtendedGoods T I), isPrimitiveNative (IST := IST) X ∧ Y ⊆ X) ∨
    ((fromGoods (T := T) (I := I) Y).Nonempty ∧
      ∃ X₁ X₂ : Finset (ExtendedGoods T I),
        X₁ ≠ X₂ ∧
          isPrimitiveNative (IST := IST) X₁ ∧
          isPrimitiveNative (IST := IST) X₂ ∧
          Y ⊆ X₁ ∧
          Y ⊆ X₂ ∧
          ∀ X, isPrimitiveNative (IST := IST) X → Y ⊆ X → X = X₁ ∨ X = X₂) := by
  by_cases hInternal : (fromGoods (T := T) (I := I) Y).Nonempty
  · right
    exact ⟨hInternal, native_internal_almostPrimitive_exactly_two_incident_primitives hY hInternal⟩
  · left
    exact ⟨hInternal, native_boundary_almostPrimitive_unique_incident_primitive hY hInternal⟩

/--
Incidence between an almost primitive face and a primitive set is exactly
the old room-door incidence after translating both sides back to `(goods, indices)`.
-/
lemma almostPrimitive_subset_primitive_iff_doorof
    {Y X : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y) (hX : isPrimitive (IST := IST) X) :
    Y ⊆ X ↔
      IST.isDoorof (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y)
        (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  constructor
  · intro hSub
    have hDoor : IST.isDoor (fromGoods (T := T) (I := I) Y)
        (fromMissing (T := T) (I := I) Y) := almostPrimitive_to_door hY
    have hRoom : IST.isRoom (fromGoods (T := T) (I := I) X)
        (fromMissing (T := T) (I := I) X) := primitive_to_room hX
    apply subset_toPrimitive_toAlmost_doorof hDoor hRoom
    rw [← almostPrimitive_eq_toAlmost_from_parts hY, ← primitive_eq_toPrimitive_from_parts hX]
    exact hSub
  · intro hDoorof
    rw [almostPrimitive_eq_toAlmost_from_parts hY, primitive_eq_toPrimitive_from_parts hX]
    exact doorof_toAlmost_subset_toPrimitive hDoorof

/--
A Scarf replacement step: two primitive sets are adjacent if they share an
almost primitive face. This is the primitive-set version of walking through a
door from one room to another.
-/
def primitiveReplacementStep (X X' : Finset (ExtendedGoods T I)) : Prop :=
  isPrimitive (IST := IST) X ∧
    isPrimitive (IST := IST) X' ∧
      X ≠ X' ∧
        ∃ Y, isAlmostPrimitive (IST := IST) Y ∧ Y ⊆ X ∧ Y ⊆ X'

omit [Inhabited T] in
lemma primitiveReplacementStep.symm {X X' : Finset (ExtendedGoods T I)}
    (h : primitiveReplacementStep (IST := IST) X X') :
    primitiveReplacementStep (IST := IST) X' X := by
  rcases h with ⟨hX, hX', hne, Y, hY, hYX, hYX'⟩
  exact ⟨hX', hX, hne.symm, Y, hY, hYX', hYX⟩

lemma replacementStep_has_common_door {X X' : Finset (ExtendedGoods T I)}
    (h : primitiveReplacementStep (IST := IST) X X') :
    ∃ Y,
      isAlmostPrimitive (IST := IST) Y ∧
      Y ⊆ X ∧ Y ⊆ X' ∧
      IST.isDoorof (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y)
        (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) ∧
      IST.isDoorof (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y)
        (fromGoods (T := T) (I := I) X') (fromMissing (T := T) (I := I) X') := by
  rcases h with ⟨hX, hX', _hne, Y, hY, hYX, hYX'⟩
  exact ⟨Y, hY, hYX, hYX',
    (almostPrimitive_subset_primitive_iff_doorof hY hX).mp hYX,
    (almostPrimitive_subset_primitive_iff_doorof hY hX').mp hYX'⟩

lemma common_door_gives_replacementStep
    {τ : Finset T} {D : Finset I} {σ₁ σ₂ : Finset T} {C₁ C₂ : Finset I}
    (hDoor₁ : IST.isDoorof τ D σ₁ C₁)
    (hDoor₂ : IST.isDoorof τ D σ₂ C₂)
    (hNe : (σ₁, C₁) ≠ (σ₂, C₂)) :
    primitiveReplacementStep (IST := IST)
      (toPrimitiveSet (I := I) σ₁ C₁) (toPrimitiveSet (I := I) σ₂ C₂) := by
  have hRoom₁ : IST.isRoom σ₁ C₁ := IST.isRoom_of_Door hDoor₁
  have hRoom₂ : IST.isRoom σ₂ C₂ := IST.isRoom_of_Door hDoor₂
  refine ⟨room_to_primitive hRoom₁, room_to_primitive hRoom₂, ?_,
    toAlmostPrimitive (I := I) τ D, door_to_almostPrimitive hDoor₁, ?_, ?_⟩
  · intro hEq
    have hσ : σ₁ = σ₂ := by
      have := congrArg (fromGoods (T := T) (I := I)) hEq
      simpa using this
    have hC : C₁ = C₂ := by
      have := congrArg (fromMissing (T := T) (I := I)) hEq
      simpa using this
    exact hNe (by simp [hσ, hC])
  · exact doorof_toAlmost_subset_toPrimitive hDoor₁
  · exact doorof_toAlmost_subset_toPrimitive hDoor₂

theorem internal_almostPrimitive_replacementStep {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y)
    (hInternal : (fromGoods (T := T) (I := I) Y).Nonempty) :
    ∃ X₁ X₂,
      primitiveReplacementStep (IST := IST) X₁ X₂ ∧ Y ⊆ X₁ ∧ Y ⊆ X₂ := by
  obtain ⟨X₁, X₂, hNe, hPrim₁, hPrim₂, hSub₁, hSub₂⟩ :=
    internal_almostPrimitive_two_incident_primitives hY hInternal
  exact ⟨X₁, X₂, ⟨hPrim₁, hPrim₂, hNe, Y, hY, hSub₁, hSub₂⟩, hSub₁, hSub₂⟩

/-- Extend a coloring of goods by coloring each slack vector by its own index. -/
def extendedColoring (c : T → I) : ExtendedGoods T I → I
  | Sum.inl t => c t
  | Sum.inr i => i

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] IST in
@[simp] lemma extendedColoring_inl (c : T → I) (t : T) :
    extendedColoring (T := T) (I := I) c (Sum.inl t) = c t := rfl

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] IST in
@[simp] lemma extendedColoring_inr (c : T → I) (i : I) :
    extendedColoring (T := T) (I := I) c (Sum.inr i) = i := rfl

omit [Fintype T] IST in
lemma image_extendedColoring_toPrimitiveSet (c : T → I) (σ : Finset T) (C : Finset I) :
    (toPrimitiveSet (I := I) σ C).image (extendedColoring (T := T) (I := I) c) =
      (σ.image c) ∪ (Finset.univ \ C) := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨x, hx, rfl⟩
    cases x with
    | inl t =>
        rw [mem_toPrimitiveSet_inl] at hx
        exact Finset.mem_union_left _ (Finset.mem_image_of_mem c hx)
    | inr j =>
        rw [mem_toPrimitiveSet_inr] at hx
        exact Finset.mem_union_right _ (by simpa [extendedColoring] using hx)
  · intro hi
    rcases Finset.mem_union.mp hi with hImage | hSlack
    · rcases Finset.mem_image.mp hImage with ⟨t, ht, rfl⟩
      exact Finset.mem_image_of_mem (extendedColoring (T := T) (I := I) c)
        (show Sum.inl t ∈ toPrimitiveSet (I := I) σ C by
          rw [mem_toPrimitiveSet_inl]
          exact ht)
    · exact Finset.mem_image_of_mem (extendedColoring (T := T) (I := I) c)
        (show Sum.inr i ∈ toPrimitiveSet (T := T) σ C by
          rw [mem_toPrimitiveSet_inr]
          exact (Finset.mem_sdiff.mp hSlack).2)

omit [Fintype T] in
/--
For a room, Scarf's statement that a primitive set has all colors is exactly
the Section 1 statement that the corresponding room is colorful.
-/
lemma full_color_primitive_iff_colorful_room (c : T → I) {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) :
    (toPrimitiveSet (I := I) σ C).image (extendedColoring (T := T) (I := I) c) =
        (Finset.univ : Finset I) ↔
      IST.isColorful c σ C := by
  constructor
  · intro hFull
    have hUnion : (σ.image c) ∪ (Finset.univ \ C) = (Finset.univ : Finset I) := by
      simpa [image_extendedColoring_toPrimitiveSet] using hFull
    have hC_subset_image : C ⊆ σ.image c := by
      intro i hiC
      have hiUnion : i ∈ (σ.image c) ∪ (Finset.univ \ C) := by
        rw [hUnion]
        exact Finset.mem_univ i
      rcases Finset.mem_union.mp hiUnion with hiImage | hiCompl
      · exact hiImage
      · exact False.elim ((Finset.mem_sdiff.mp hiCompl).2 hiC)
    have hImage_card_le_C : (σ.image c).card ≤ C.card := by
      calc
        (σ.image c).card ≤ σ.card := Finset.card_image_le
        _ = C.card := hRoom.2.symm
    exact ⟨hRoom.1, (Finset.eq_of_subset_of_card_le hC_subset_image hImage_card_le_C).symm⟩
  · intro hColorful
    rw [image_extendedColoring_toPrimitiveSet, hColorful.2]
    exact Finset.union_sdiff_self_eq_union.symm.trans (by simp)

/-- Scarf's primitive-set coloring condition `c(X) = I`. -/
def isFullyColoredPrimitive (c : T → I) (X : Finset (ExtendedGoods T I)) : Prop :=
  isPrimitive (IST := IST) X ∧
    X.image (extendedColoring (T := T) (I := I) c) = (Finset.univ : Finset I)

/--
For an arbitrary primitive set, Scarf's condition `c(X) = I` is exactly the
colorful-room condition for the associated room `(X ∩ T, I \ X)`.
-/
lemma full_color_primitive_iff_colorful_associated_room
    (c : T → I) {X : Finset (ExtendedGoods T I)} (hX : isPrimitive (IST := IST) X) :
    X.image (extendedColoring (T := T) (I := I) c) = (Finset.univ : Finset I) ↔
      IST.isColorful c (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) := by
  constructor
  · intro hFull
    have hFull' :
        (toPrimitiveSet (I := I) (fromGoods (T := T) (I := I) X)
            (fromMissing (T := T) (I := I) X)).image
            (extendedColoring (T := T) (I := I) c) = (Finset.univ : Finset I) := by
      rw [← primitive_eq_toPrimitive_from_parts hX]
      exact hFull
    exact (full_color_primitive_iff_colorful_room c (primitive_to_room hX)).1 hFull'
  · intro hColorful
    rw [primitive_eq_toPrimitive_from_parts hX]
    exact (full_color_primitive_iff_colorful_room c (primitive_to_room hX)).2 hColorful

omit [Fintype T] IST in
lemma image_extendedColoring_toAlmostPrimitive (c : T → I) (τ : Finset T) (D : Finset I) :
    (toAlmostPrimitive (I := I) τ D).image (extendedColoring (T := T) (I := I) c) =
      (τ.image c) ∪ (Finset.univ \ D) := by
  simpa [toAlmostPrimitive] using
    (image_extendedColoring_toPrimitiveSet (T := T) (I := I) c τ D)

omit [Fintype T] IST in
lemma diff_image_eq_singleton_iff_allButColor_toPrimitiveSet
    (c : T → I) (i : I) (σ : Finset T) (C : Finset I) :
    C \ σ.image c = {i} ↔
      (toPrimitiveSet (I := I) σ C).image (extendedColoring (T := T) (I := I) c) =
        (Finset.univ.erase i : Finset I) := by
  rw [image_extendedColoring_toPrimitiveSet]
  constructor
  · intro hDiff
    ext j
    constructor
    · intro hj
      rcases Finset.mem_union.mp hj with hjImage | hjCompl
      · have hji : j ≠ i := by
          intro hji
          subst j
          have hiDiff : i ∈ C \ σ.image c := by
            rw [hDiff]
            simp
          exact (Finset.mem_sdiff.mp hiDiff).2 hjImage
        exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
      · have hji : j ≠ i := by
          intro hji
          subst j
          have hiDiff : i ∈ C \ σ.image c := by
            rw [hDiff]
            simp
          exact (Finset.mem_sdiff.mp hjCompl).2 (Finset.mem_sdiff.mp hiDiff).1
        exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
    · intro hj
      by_cases hjImage : j ∈ σ.image c
      · exact Finset.mem_union_left _ hjImage
      · have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hjNotC : j ∉ C := by
          intro hjC
          have hjDiff : j ∈ C \ σ.image c := Finset.mem_sdiff.mpr ⟨hjC, hjImage⟩
          have : j = i := by
            rw [hDiff] at hjDiff
            exact Finset.mem_singleton.mp hjDiff
          exact hji this
        exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hjNotC⟩)
  · intro hAllBut
    ext j
    constructor
    · intro hj
      have hjNotUnion : j ∉ σ.image c ∪ (Finset.univ \ C) := by
        intro hUnion
        rcases Finset.mem_union.mp hUnion with hjImage | hjCompl
        · exact (Finset.mem_sdiff.mp hj).2 hjImage
        · exact (Finset.mem_sdiff.mp hjCompl).2 (Finset.mem_sdiff.mp hj).1
      have hjNotErase : j ∉ Finset.univ.erase i := by
        rw [← hAllBut]
        exact hjNotUnion
      have hji : j = i := by
        by_contra hne
        exact hjNotErase (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩)
      rw [hji]
      simp
    · intro hj
      have hji : j = i := Finset.mem_singleton.mp hj
      subst j
      have hiNotErase : i ∉ (Finset.univ.erase i : Finset I) := by simp
      have hiNotUnion : i ∉ σ.image c ∪ (Finset.univ \ C) := by
        rw [hAllBut]
        exact hiNotErase
      have hiC : i ∈ C := by
        by_contra hiNotC
        exact hiNotUnion (Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiNotC⟩))
      have hiNotImage : i ∉ σ.image c := by
        intro hiImage
        exact hiNotUnion (Finset.mem_union_left _ hiImage)
      exact Finset.mem_sdiff.mpr ⟨hiC, hiNotImage⟩

omit [Fintype T] IST in
lemma diff_image_eq_singleton_iff_allButColor_toAlmostPrimitive
    (c : T → I) (i : I) (τ : Finset T) (D : Finset I) :
    D \ τ.image c = {i} ↔
      (toAlmostPrimitive (I := I) τ D).image (extendedColoring (T := T) (I := I) c) =
        (Finset.univ.erase i : Finset I) := by
  simpa [toAlmostPrimitive] using
    (diff_image_eq_singleton_iff_allButColor_toPrimitiveSet
      (T := T) (I := I) c i τ D)

lemma allButColor_primitive_iff_typed_associated_room
    (c : T → I) (i : I) {X : Finset (ExtendedGoods T I)}
    (hX : isPrimitive (IST := IST) X) :
    X.image (extendedColoring (T := T) (I := I) c) =
        (Finset.univ.erase i : Finset I) ↔
      IST.isTypedNC c i (fromGoods (T := T) (I := I) X)
        (fromMissing (T := T) (I := I) X) := by
  constructor
  · intro hAllBut
    exact ⟨(primitive_to_room hX).1,
      (diff_image_eq_singleton_iff_allButColor_toPrimitiveSet
        (T := T) (I := I) c i
        (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X)).2
          (by rwa [← primitive_eq_toPrimitive_from_parts hX])⟩
  · intro hTyped
    rw [primitive_eq_toPrimitive_from_parts hX]
    exact (diff_image_eq_singleton_iff_allButColor_toPrimitiveSet
      (T := T) (I := I) c i
      (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X)).1 hTyped.2

lemma allButColor_almostPrimitive_iff_typed_associated_door
    (c : T → I) (i : I) {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y) :
    Y.image (extendedColoring (T := T) (I := I) c) =
        (Finset.univ.erase i : Finset I) ↔
      IST.isTypedNC c i (fromGoods (T := T) (I := I) Y)
        (fromMissing (T := T) (I := I) Y) := by
  constructor
  · intro hAllBut
    exact ⟨(almostPrimitive_to_door hY).1,
      (diff_image_eq_singleton_iff_allButColor_toAlmostPrimitive
        (T := T) (I := I) c i
        (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y)).2
          (by rwa [← almostPrimitive_eq_toAlmost_from_parts hY])⟩
  · intro hTyped
    rw [almostPrimitive_eq_toAlmost_from_parts hY]
    exact (diff_image_eq_singleton_iff_allButColor_toAlmostPrimitive
      (T := T) (I := I) c i
      (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y)).1 hTyped.2

omit [Fintype T] IST in
@[simp] lemma image_extendedColoring_slackBoundary (c : T → I) (i : I) :
    (slackBoundary (T := T) (I := I) i).image (extendedColoring (T := T) (I := I) c) =
      (Finset.univ.erase i : Finset I) := by
  rw [slackBoundary, image_extendedColoring_toAlmostPrimitive]
  ext j
  constructor
  · intro hj
    rw [Finset.mem_union] at hj
    rcases hj with hjEmpty | hjCompl
    · rcases Finset.mem_image.mp hjEmpty with ⟨x, hx, _⟩
      exact False.elim (Finset.notMem_empty x hx)
    · exact Finset.mem_erase.mpr
        ⟨fun hji => (Finset.mem_sdiff.mp hjCompl).2 (by simp [hji]), Finset.mem_univ j⟩
  · intro hj
    exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ j, fun hji => (Finset.mem_erase.mp hj).1 (Finset.mem_singleton.mp hji)⟩)

lemma slackBoundary_GiDoorVertex (c : T → I) (i : I) :
    GiDoorVertex (IST := IST) c i
      (associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i)) := by
  have hY : isAlmostPrimitive (IST := IST) (slackBoundary (T := T) (I := I) i) :=
    slackBoundary_isAlmostPrimitive (IST := IST) i
  have hTyped := (allButColor_almostPrimitive_iff_typed_associated_door
    (IST := IST) c i hY).1 (image_extendedColoring_slackBoundary (T := T) (I := I) c i)
  exact ⟨almostPrimitive_to_door hY, hTyped⟩

lemma fullyColoredPrimitive_GiRoomVertex
    {c : T → I} {i : I} {X : Finset (ExtendedGoods T I)}
    (hX : isFullyColoredPrimitive (IST := IST) c X) :
    GiRoomVertex (IST := IST) c i (associatedCell (T := T) (I := I) X) := by
  exact Or.inl ((full_color_primitive_iff_colorful_associated_room c hX.1).1 hX.2)

lemma allButColorPrimitive_GiRoomVertex
    {c : T → I} {i : I} {X : Finset (ExtendedGoods T I)}
    (hPrim : isPrimitive (IST := IST) X)
    (hColor : X.image (extendedColoring (T := T) (I := I) c) =
      (Finset.univ.erase i : Finset I)) :
    GiRoomVertex (IST := IST) c i (associatedCell (T := T) (I := I) X) := by
  exact Or.inr ⟨primitive_to_room hPrim,
    (allButColor_primitive_iff_typed_associated_room c i hPrim).1 hColor⟩

lemma allButColorAlmostPrimitive_GiDoorVertex
    {c : T → I} {i : I} {Y : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y)
    (hColor : Y.image (extendedColoring (T := T) (I := I) c) =
      (Finset.univ.erase i : Finset I)) :
    GiDoorVertex (IST := IST) c i (associatedCell (T := T) (I := I) Y) := by
  exact ⟨almostPrimitive_to_door hY,
    (allButColor_almostPrimitive_iff_typed_associated_door c i hY).1 hColor⟩

lemma algorithm_incidence_to_GiEdge
    {c : T → I} {i : I}
    {Y X : Finset (ExtendedGoods T I)}
    (hY : isAlmostPrimitive (IST := IST) Y)
    (hYColor : Y.image (extendedColoring (T := T) (I := I) c) =
      (Finset.univ.erase i : Finset I))
    (hX : isPrimitive (IST := IST) X)
    (hXColor :
      X.image (extendedColoring (T := T) (I := I) c) =
        (Finset.univ.erase i : Finset I) ∨
      X.image (extendedColoring (T := T) (I := I) c) =
        (Finset.univ : Finset I))
    (hSub : Y ⊆ X) :
    GiEdge (IST := IST) c i
      (associatedCell (T := T) (I := I) X) (associatedCell (T := T) (I := I) Y) := by
  have hRoomVertex : GiRoomVertex (IST := IST) c i (associatedCell (T := T) (I := I) X) := by
    rcases hXColor with hAllBut | hFull
    · exact allButColorPrimitive_GiRoomVertex (IST := IST) hX hAllBut
    · exact fullyColoredPrimitive_GiRoomVertex (IST := IST) ⟨hX, hFull⟩
  have hDoorVertex : GiDoorVertex (IST := IST) c i (associatedCell (T := T) (I := I) Y) :=
    allButColorAlmostPrimitive_GiDoorVertex (IST := IST) hY hYColor
  have hDoorof :
      IST.isDoorof (fromGoods (T := T) (I := I) Y) (fromMissing (T := T) (I := I) Y)
        (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) :=
    (almostPrimitive_subset_primitive_iff_doorof hY hX).mp hSub
  exact Or.inl ⟨hRoomVertex, hDoorVertex, hDoorof⟩

/--
A split Scarf replacement step, matching §3: an all-but-`i` primitive set moves
through an all-but-`i` almost primitive face to another primitive set, which is
either still all-but-`i` or already fully colored.
-/
def scarfSplitReplacementStep (c : T → I) (i : I)
    (X Y X' : Finset (ExtendedGoods T I)) : Prop :=
  isPrimitive (IST := IST) X ∧
    X.image (extendedColoring (T := T) (I := I) c) =
      (Finset.univ.erase i : Finset I) ∧
    isAlmostPrimitive (IST := IST) Y ∧
    Y.image (extendedColoring (T := T) (I := I) c) =
      (Finset.univ.erase i : Finset I) ∧
    Y ⊆ X ∧
    isPrimitive (IST := IST) X' ∧
    Y ⊆ X' ∧
    (X'.image (extendedColoring (T := T) (I := I) c) =
        (Finset.univ.erase i : Finset I) ∨
      X'.image (extendedColoring (T := T) (I := I) c) =
        (Finset.univ : Finset I)) ∧
    X ≠ X'

omit [Inhabited T] in
lemma scarfSplitReplacementStep_replacementStep
    {c : T → I} {i : I} {X Y X' : Finset (ExtendedGoods T I)}
    (h : scarfSplitReplacementStep (IST := IST) c i X Y X') :
    primitiveReplacementStep (IST := IST) X X' := by
  rcases h with ⟨hX, _hXColor, hY, _hYColor, hYX, hX', hYX', _hX'Color, hNe⟩
  exact ⟨hX, hX', hNe, Y, hY, hYX, hYX'⟩

lemma scarfSplitReplacementStep_GiEdges
    {c : T → I} {i : I} {X Y X' : Finset (ExtendedGoods T I)}
    (h : scarfSplitReplacementStep (IST := IST) c i X Y X') :
    GiEdge (IST := IST) c i
        (associatedCell (T := T) (I := I) X) (associatedCell (T := T) (I := I) Y) ∧
      GiEdge (IST := IST) c i
        (associatedCell (T := T) (I := I) X') (associatedCell (T := T) (I := I) Y) := by
  rcases h with ⟨hX, hXColor, hY, hYColor, hYX, hX', hYX', hX'Color, _hNe⟩
  exact ⟨
    algorithm_incidence_to_GiEdge (IST := IST) hY hYColor hX (Or.inl hXColor) hYX,
    algorithm_incidence_to_GiEdge (IST := IST) hY hYColor hX' hX'Color hYX'⟩

/--
The graph-walk segment represented by one split Scarf replacement step:
`X → Y → X'`.
-/
def scarfSplitReplacementStepWalk
    {c : T → I} {i : I} {X Y X' : Finset (ExtendedGoods T I)}
    (h : scarfSplitReplacementStep (IST := IST) c i X Y X') :
    (GiGraph (IST := IST) c i).Walk
      (associatedCell (T := T) (I := I) X)
      (associatedCell (T := T) (I := I) X') :=
  let hEdges := scarfSplitReplacementStep_GiEdges (IST := IST) h
  SimpleGraph.Walk.cons hEdges.1
    (SimpleGraph.Walk.cons (GiEdge.symm hEdges.2) SimpleGraph.Walk.nil)

lemma initial_scarf_step_to_GiEdge (c : T → I) (i : I) :
    ∃ X : Finset (ExtendedGoods T I),
      isPrimitive (IST := IST) X ∧
        slackBoundary (T := T) (I := I) i ⊆ X ∧
        GiEdge (IST := IST) c i
          (associatedCell (T := T) (I := I) X)
          (associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i)) := by
  rcases slackBoundary_unique_incident_primitive (IST := IST) i with ⟨X, hX, _hUnique⟩
  rcases hX with ⟨hPrim, hSub⟩
  have hDoorVertex := slackBoundary_GiDoorVertex (IST := IST) c i
  have hDoorof :
      IST.isDoorof
        (fromGoods (T := T) (I := I) (slackBoundary (T := T) (I := I) i))
        (fromMissing (T := T) (I := I) (slackBoundary (T := T) (I := I) i))
        (fromGoods (T := T) (I := I) X) (fromMissing (T := T) (I := I) X) :=
    (almostPrimitive_subset_primitive_iff_doorof
      (slackBoundary_isAlmostPrimitive (IST := IST) i) hPrim).mp hSub
  have hRoomVertex :
      GiRoomVertex (IST := IST) c i (associatedCell (T := T) (I := I) X) :=
    GiRoomVertex_of_incident_typed_door hDoorVertex.2 hDoorof
  exact ⟨X, hPrim, hSub, Or.inl ⟨hRoomVertex, hDoorVertex, hDoorof⟩⟩

/-- The first graph-walk segment of Scarf's algorithm, from `I - i` into the building. -/
lemma initial_scarf_step_walk (c : T → I) (i : I) :
    ∃ X : Finset (ExtendedGoods T I),
      ∃ _p : (GiGraph (IST := IST) c i).Walk
          (associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i))
          (associatedCell (T := T) (I := I) X),
        isPrimitive (IST := IST) X ∧
        slackBoundary (T := T) (I := I) i ⊆ X := by
  rcases initial_scarf_step_to_GiEdge (IST := IST) c i with ⟨X, hPrim, hSub, hEdge⟩
  refine ⟨X, ?_, hPrim, hSub⟩
  exact SimpleGraph.Walk.cons
    (show (GiGraph (IST := IST) c i).Adj
      (associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i))
      (associatedCell (T := T) (I := I) X) from GiEdge.symm hEdge)
    SimpleGraph.Walk.nil

/--
A complete primitive-language Scarf algorithm trace of type `i`.  It starts at
the boundary face `I - i`, follows `G_i`, and terminates at a fully colored
primitive set.  The local lemmas above build such walks from initial and split
replacement segments.
-/
structure ScarfAlgorithmTrace (c : T → I) (i : I) where
  /-- The terminal room of a Scarf-algorithm trace. -/
  terminal : Finset (ExtendedGoods T I)
  terminal_fullyColored : isFullyColoredPrimitive (IST := IST) c terminal
  /-- The graph walk recorded by a Scarf-algorithm trace. -/
  walk : (GiGraph (IST := IST) c i).Walk
    (associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i))
    (associatedCell (T := T) (I := I) terminal)

lemma ScarfAlgorithmTrace.terminal_colorful_room
    {c : T → I} {i : I} (trace : ScarfAlgorithmTrace (IST := IST) c i) :
    IST.isColorful c
      (fromGoods (T := T) (I := I) trace.terminal)
      (fromMissing (T := T) (I := I) trace.terminal) :=
  (full_color_primitive_iff_colorful_associated_room c trace.terminal_fullyColored.1).1
    trace.terminal_fullyColored.2

omit [Inhabited T] in
/-- A reachable fully colored primitive set gives a complete Scarf trace. -/
lemma scarfAlgorithmTrace_of_reachable_fullyColoredPrimitive
    {c : T → I} {i : I} {X : Finset (ExtendedGoods T I)}
    (hX : isFullyColoredPrimitive (IST := IST) c X)
    (hReach : (GiGraph (IST := IST) c i).Reachable
      (associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i))
      (associatedCell (T := T) (I := I) X)) :
    Nonempty (ScarfAlgorithmTrace (IST := IST) c i) := by
  rcases hReach with ⟨p⟩
  exact ⟨⟨X, hX, p⟩⟩

omit [Inhabited T] in
/--
It is enough to find a fully colored primitive set in the connected component
of the outside door. This is the component-level form of the path-following
argument in §3.
-/
lemma scarfAlgorithmTrace_of_component_fullyColoredPrimitive
    {c : T → I} {i : I} {X : Finset (ExtendedGoods T I)}
    (hX : isFullyColoredPrimitive (IST := IST) c X)
    (hComponent :
      (GiGraph (IST := IST) c i).connectedComponentMk
        (associatedCell (T := T) (I := I) X) =
      (GiGraph (IST := IST) c i).connectedComponentMk
        (associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i))) :
    Nonempty (ScarfAlgorithmTrace (IST := IST) c i) := by
  apply scarfAlgorithmTrace_of_reachable_fullyColoredPrimitive (IST := IST) hX
  exact SimpleGraph.ConnectedComponent.exact hComponent.symm

omit [Inhabited T] in
/--
Existence of a complete Scarf trace is equivalent to finding a fully colored
primitive set in the connected component of the outside door.  This isolates
the remaining graph-theoretic endpoint argument from the primitive-set
translation.
-/
theorem scarfAlgorithmTrace_nonempty_iff_component_fullyColoredPrimitive
    (c : T → I) (i : I) :
    Nonempty (ScarfAlgorithmTrace (IST := IST) c i) ↔
      ∃ X : Finset (ExtendedGoods T I),
        isFullyColoredPrimitive (IST := IST) c X ∧
          (GiGraph (IST := IST) c i).connectedComponentMk
            (associatedCell (T := T) (I := I) X) =
          (GiGraph (IST := IST) c i).connectedComponentMk
            (associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i)) := by
  constructor
  · rintro ⟨trace⟩
    refine ⟨trace.terminal, trace.terminal_fullyColored, ?_⟩
    exact SimpleGraph.ConnectedComponent.sound trace.walk.reachable |>.symm
  · rintro ⟨X, hX, hComponent⟩
    exact scarfAlgorithmTrace_of_component_fullyColoredPrimitive (IST := IST) hX hComponent

lemma outsideDoor_endpoint_cell_eq_slackBoundary
    {c : T → I} {i : I} {v : GiCell T I}
    (hDoor : GiDoorVertex (IST := IST) c i v) (hOutside : IST.isOutsideDoor v.1 v.2) :
    v = associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i) := by
  have hτ : v.1 = Finset.empty := hOutside.2
  have hD : v.2 = ({i} : Finset I) := by
    have hTyped := hDoor.2.2
    rw [hτ] at hTyped
    have hImg : Finset.image c (Finset.empty : Finset T) = Finset.empty := Finset.image_empty c
    rw [hImg] at hTyped
    have hsdiff : v.2 \ (Finset.empty : Finset I) = v.2 :=
      Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_empty_right v.2)
    rwa [hsdiff] at hTyped
  rw [associatedCell_slackBoundary]
  exact Prod.ext hτ hD

omit [Inhabited T] in
lemma giVertex_of_GiDegree_eq_one {c : T → I} {i : I} {v : GiCell T I}
    (hdeg : GiDegree (IST := IST) c i v = 1) :
    GiVertex (IST := IST) c i v := by
  have hNonempty : (GiNeighbors (IST := IST) c i v).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < GiDegree (IST := IST) c i v
    rw [hdeg]
    norm_num
  rcases hNonempty with ⟨w, hw⟩
  exact GiEdge.left_vertex ((mem_GiNeighbors (IST := IST)).1 hw)

omit [Inhabited T] in
/-- The induced subgraph on the vertices reachable from a fixed base vertex. -/
def reachableComponentGraph {α : Type*} (G : SimpleGraph α) (v₀ : α) :
    SimpleGraph {v : α // G.Reachable v₀ v} where
  Adj a b := G.Adj a.1 b.1
  symm := by intro a b h; exact G.symm h
  loopless := ⟨fun a h => G.loopless.1 a.1 h⟩

omit [Inhabited T] in
lemma reachableComponentGraph_degree_eq
    {α : Type*} [Fintype α] (G : SimpleGraph α) (v₀ : α)
    (x : {v : α // G.Reachable v₀ v}) :
    (reachableComponentGraph G v₀).degree x = G.degree x.1 := by
  classical
  let H : SimpleGraph {v : α // G.Reachable v₀ v} := reachableComponentGraph G v₀
  change H.degree x = G.degree x.1
  have hImage :
      (H.neighborFinset x).image (fun y : {v : α // G.Reachable v₀ v} => y.1) =
        G.neighborFinset x.1 := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_image.mp hy with ⟨z, hz, rfl⟩
      exact (SimpleGraph.mem_neighborFinset G x.1 z.1).2
        ((SimpleGraph.mem_neighborFinset H x z).1 hz)
    · intro hy
      have hAdj : G.Adj x.1 y := (SimpleGraph.mem_neighborFinset G x.1 y).1 hy
      have hReachY : G.Reachable v₀ y := by
        rcases x.2 with ⟨p⟩
        exact ⟨p.concat hAdj⟩
      exact Finset.mem_image.mpr
        ⟨⟨y, hReachY⟩, (SimpleGraph.mem_neighborFinset H x ⟨y, hReachY⟩).2 hAdj, rfl⟩
  calc
    H.degree x = (H.neighborFinset x).card := rfl
    _ = ((H.neighborFinset x).image (fun y : {v : α // G.Reachable v₀ v} => y.1)).card := by
      rw [Finset.card_image_of_injOn]
      intro a _ b _ h
      exact Subtype.ext h
    _ = (G.neighborFinset x.1).card := by rw [hImage]
    _ = G.degree x.1 := rfl

theorem scarfAlgorithmTrace_exists [Inhabited I] (c : T → I) (i : I) :
    Nonempty (ScarfAlgorithmTrace (IST := IST) c i) := by
  classical
  let outside : GiCell T I :=
    associatedCell (T := T) (I := I) (slackBoundary (T := T) (I := I) i)
  let G := GiGraph (IST := IST) c i
  let H : SimpleGraph {v : GiCell T I // G.Reachable outside v} :=
    reachableComponentGraph G outside
  let outsideSub : {v : GiCell T I // G.Reachable outside v} := ⟨outside, ⟨SimpleGraph.Walk.nil⟩⟩
  have hOutsideDoor : IST.isOutsideDoor outside.1 outside.2 := by
    simp only [associatedCell_slackBoundary, outside]
    exact IST.outsidedoor_singleton i
  have hOutsideTyped : IST.isTypedNC c i outside.1 outside.2 := by
    have hDoorVertex := slackBoundary_GiDoorVertex (IST := IST) c i
    simpa [outside] using hDoorVertex.2
  have hOutsideDegree : G.degree outside = 1 := by
    change GiDegree (IST := IST) c i outside = 1
    exact GiDegree_outsideDoor (IST := IST) hOutsideDoor hOutsideTyped
  have hOutsideSubDegree : H.degree outsideSub = 1 := by
    rw [reachableComponentGraph_degree_eq G outside outsideSub, hOutsideDegree]
  have hOddOutside : Odd (H.degree outsideSub) := by rw [hOutsideSubDegree]; exact odd_one
  obtain ⟨w, hwNe, hwOdd⟩ :=
    SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree H outsideSub hOddOutside
  have hwOddG : Odd (G.degree w.1) := by
    rw [← reachableComponentGraph_degree_eq G outside w]
    exact hwOdd
  have hwLe : G.degree w.1 ≤ 2 := by
    exact (GiPathStructure_of_degreeCharacterization
      (IST := IST) (GiDegreeCharacterization_holds (IST := IST) c i)).2 w.1
  have hwDegreeOne : G.degree w.1 = 1 := by
    rcases hwOddG with ⟨k, hk⟩
    omega
  have hwGiDegreeOne : GiDegree (IST := IST) c i w.1 = 1 := by
    rw [← hwDegreeOne]
    rfl
  have hwEndpoint : GiEndpoint (IST := IST) c i w.1 :=
    ⟨giVertex_of_GiDegree_eq_one (IST := IST) hwGiDegreeOne, hwGiDegreeOne⟩
  have hwEndpointKind := (GiDegreeCharacterization_holds (IST := IST) c i).2 w.1 |>.mp hwEndpoint
  have hwColorful : IST.isColorful c w.1.1 w.1.2 := by
    rcases hwEndpointKind with hOutside | hColorful
    · have hwEqOutside := outsideDoor_endpoint_cell_eq_slackBoundary
        (IST := IST) hOutside.1 hOutside.2
      have hwEq : w = outsideSub := by
        apply Subtype.ext
        change w.1 = outside
        simpa [outside] using hwEqOutside
      exact False.elim (hwNe hwEq)
    · exact hColorful
  let X : Finset (ExtendedGoods T I) := toPrimitiveSet (I := I) w.1.1 w.1.2
  have hRoom : IST.isRoom w.1.1 w.1.2 := IST.room_of_colorful hwColorful
  have hPrim : isPrimitive (IST := IST) X := room_to_primitive hRoom
  have hFull :
      X.image (extendedColoring (T := T) (I := I) c) = (Finset.univ : Finset I) :=
    (full_color_primitive_iff_colorful_room c hRoom).2 hwColorful
  apply scarfAlgorithmTrace_of_reachable_fullyColoredPrimitive (IST := IST) ⟨hPrim, hFull⟩
  have hReach : G.Reachable outside w.1 := w.2
  rcases hReach with ⟨p⟩
  change (GiGraph (IST := IST) c i).Reachable outside (associatedCell (T := T) (I := I) X)
  have hAssoc : associatedCell (T := T) (I := I) X = w.1 := by
    simp [X, associatedCell]
  rw [hAssoc]
  exact ⟨p⟩

/--
Scarf's combinatorial theorem in the primitive-set language from §3: after
extending a coloring by the identity on slack vectors, some primitive set has
all colors, obtained by following the Scarf trace from the boundary door.
-/
theorem scarf_fullyColoredPrimitive_exists_via_trace [Inhabited I] (c : T → I) :
    ∃ X : Finset (ExtendedGoods T I), isFullyColoredPrimitive (IST := IST) c X := by
  obtain ⟨trace⟩ := scarfAlgorithmTrace_exists (IST := IST) c default
  exact ⟨trace.terminal, trace.terminal_fullyColored⟩

/--
Scarf's combinatorial theorem in the primitive-set language from §3.  The proof
is routed through the path-following trace, matching the narrative of the paper.
-/
theorem scarf_fullyColoredPrimitive_exists [Inhabited I] (c : T → I) :
    ∃ X : Finset (ExtendedGoods T I), isFullyColoredPrimitive (IST := IST) c X :=
  scarf_fullyColoredPrimitive_exists_via_trace (IST := IST) c

/--
The unique primitive set incident to the boundary face `I - i`, in the same
language used to start Scarf's replacement path.
-/
lemma initial_scarf_primitive_from_boundary (i : I) :
    ∃! X : Finset (ExtendedGoods T I),
      isPrimitive (IST := IST) X ∧ slackBoundary (T := T) (I := I) i ⊆ X :=
  slackBoundary_unique_incident_nativePrimitive (IST := IST) i

omit [Inhabited T] in
/--
Splitting a replacement step gives exactly the alternating primitive /
almost-primitive pattern described in §3.
-/
lemma replacementStep_splits_through_almostPrimitive
    {X X' : Finset (ExtendedGoods T I)}
    (h : primitiveReplacementStep (IST := IST) X X') :
    ∃ Y,
      isAlmostPrimitive (IST := IST) Y ∧
      Y ⊆ X ∧ Y ⊆ X' ∧
      X ≠ X' :=
  let ⟨_, _, hNe, Y, hY, hYX, hYX'⟩ := h
  ⟨Y, hY, hYX, hYX', hNe⟩

/--
Utility functions realize the abstract preference orders when they preserve
and reflect each indexed strict order.
-/
structure UtilityRealization (u : I → T → ℝ) : Prop where
  order_iff : ∀ i x y, (IST i).lt x y ↔ u i x < u i y

/-- Positive utility functions, matching the economic convention in §3. -/
structure PositiveUtilityRealization (u : I → T → ℝ) : Prop extends
    UtilityRealization (IST := IST) u where
  positive : ∀ i x, 0 < u i x

/-- The lower contour set of `x` in the order indexed by `i`. -/
def orderLowerSet (i : I) (x : T) : Finset T :=
  letI : LinearOrder T := IST i
  Finset.univ.filter (fun y : T => y ≤ x)

/--
The finite rank utility associated to an indexed order. Adding `1` makes it
positive, matching the economic convention in the paper.
-/
def orderUtility (i : I) (x : T) : ℝ :=
  ((orderLowerSet (IST := IST) i x).card : ℝ) + 1

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma orderUtility_positive (i : I) (x : T) :
    0 < orderUtility (IST := IST) i x := by
  unfold orderUtility
  positivity

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma orderUtility_order_iff (i : I) (x y : T) :
    (IST i).lt x y ↔
      orderUtility (IST := IST) i x < orderUtility (IST := IST) i y := by
  letI : LinearOrder T := IST i
  constructor
  · intro hxy
    unfold orderUtility orderLowerSet
    have hSubset : Finset.univ.filter (fun z : T => z ≤ x) ⊂
        Finset.univ.filter (fun z : T => z ≤ y) := by
      constructor
      · intro z hz
        rw [Finset.mem_filter] at hz ⊢
        exact ⟨hz.1, le_trans hz.2 (le_of_lt hxy)⟩
      · intro hEq
        have hy_mem_y : y ∈ Finset.univ.filter (fun z : T => z ≤ y) := by
          simp
        have hy_mem_x : y ∈ Finset.univ.filter (fun z : T => z ≤ x) := by
          exact hEq hy_mem_y
        rw [Finset.mem_filter] at hy_mem_x
        exact not_le_of_gt hxy hy_mem_x.2
    have hCard : (Finset.univ.filter (fun z : T => z ≤ x)).card <
        (Finset.univ.filter (fun z : T => z ≤ y)).card :=
      Finset.card_lt_card hSubset
    exact_mod_cast (Nat.succ_lt_succ hCard)
  · intro hlt
    by_contra hnot
    have hyx : y ≤ x := le_of_not_gt hnot
    unfold orderUtility orderLowerSet at hlt
    have hSubset : Finset.univ.filter (fun z : T => z ≤ y) ⊆
        Finset.univ.filter (fun z : T => z ≤ x) := by
      intro z hz
      rw [Finset.mem_filter] at hz ⊢
      exact ⟨hz.1, le_trans hz.2 hyx⟩
    have hCard : (Finset.univ.filter (fun z : T => z ≤ y)).card ≤
        (Finset.univ.filter (fun z : T => z ≤ x)).card :=
      Finset.card_le_card hSubset
    have hNot : ¬
        (((Finset.univ.filter (fun z : T => z ≤ x)).card : ℝ) + 1 <
          ((Finset.univ.filter (fun z : T => z ≤ y)).card : ℝ) + 1) := by
      apply not_lt.mpr
      exact_mod_cast Nat.succ_le_succ hCard
    exact hNot hlt

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma orderUtility_realization :
    UtilityRealization (IST := IST) (fun i x => orderUtility (IST := IST) i x) where
  order_iff := orderUtility_order_iff

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma positiveOrderUtility_realization :
    PositiveUtilityRealization (IST := IST) (fun i x => orderUtility (IST := IST) i x) where
  order_iff := orderUtility_order_iff
  positive := orderUtility_positive

/-- A utility vector embeds a good into `ℝ^I`. -/
def utilityVector (u : I → T → ℝ) (x : T) : I → ℝ :=
  fun i => u i x

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma utilityVector_injective_of_realization [Inhabited I] {u : I → T → ℝ}
    (hu : UtilityRealization (IST := IST) u) :
    Function.Injective (utilityVector (I := I) u) := by
  intro x y hxy
  by_contra hne
  let i : I := default
  letI : LinearOrder T := IST i
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hcoord := congrFun hxy i
    have hltCoord : u i x < u i y := (hu.order_iff i x y).mp hlt
    exact (ne_of_lt hltCoord) (by simpa [utilityVector] using hcoord)
  · have hcoord := congrFun hxy i
    have hltCoord : u i y < u i x := (hu.order_iff i y x).mp hgt
    exact (ne_of_lt hltCoord) (by simpa [utilityVector] using hcoord.symm)

/-- The finite coordinate image `u(T)` used when identifying goods with utility vectors. -/
def utilityImage (u : I → T → ℝ) : Finset (I → ℝ) :=
  Finset.univ.image (utilityVector (I := I) u)

/--
The paper's "identify `T` with its image `u(T)`" step, formalized as an
equivalence once the utility realization separates points.
-/
noncomputable def utilityImageEquiv [Inhabited I] (u : I → T → ℝ)
    (hu : UtilityRealization (IST := IST) u) :
    T ≃ {v : I → ℝ // v ∈ utilityImage (T := T) (I := I) u} where
  toFun x := ⟨utilityVector (I := I) u x, by simp [utilityImage]⟩
  invFun v := Classical.choose (Finset.mem_image.mp v.2)
  left_inv x := by
    have hmem : (utilityVector (I := I) u x) ∈ utilityImage (T := T) (I := I) u := by
      simp [utilityImage]
    have hchosen := Classical.choose_spec (Finset.mem_image.mp hmem)
    exact utilityVector_injective_of_realization (IST := IST) hu hchosen.2
  right_inv v := by
    rcases v with ⟨v, hv⟩
    have hchosen := Classical.choose_spec (Finset.mem_image.mp hv)
    ext i
    exact congrFun hchosen.2 i

/--
The coordinate model of Scarf's slack vector for face `i`: the `i`th
coordinate is zero and all other coordinates are the chosen large value `M i`.
-/
def slackVector (M : I → ℝ) (i : I) : I → ℝ :=
  fun j => if j = i then 0 else M i

/-- Interpret the enlarged set `T ∪ I` as points in `ℝ^I`. -/
def extendedCoordinatePoint (u : I → T → ℝ) (M : I → ℝ) :
    ExtendedGoods T I → I → ℝ
  | Sum.inl x => utilityVector (I := I) u x
  | Sum.inr i => slackVector (I := I) M i

/-- A uniform choice of slack heights for a finite utility realization. -/
def uniformSlackHeight : I → ℝ :=
  Function.const I ((Fintype.card T : ℝ) + 2)

omit [Fintype I] in
@[simp] lemma slackVector_self (M : I → ℝ) (i : I) :
    slackVector (I := I) M i i = 0 := by
  simp [slackVector]

omit [Fintype I] in
@[simp] lemma slackVector_of_ne (M : I → ℝ) {i j : I} (h : j ≠ i) :
    slackVector (I := I) M i j = M i := by
  simp [slackVector, h]

omit [Fintype I] in
lemma slackVector_other_coordinate_gt {M : I → ℝ} {i j : I} (hji : j ≠ i)
    {r : ℝ} (hr : r < M i) :
    r < slackVector (I := I) M i j := by
  simpa [slackVector, hji] using hr

/--
Slack-height condition for Scarf's slack vectors: the nonzero coordinate
`coord` of the slack vector `s(slack)` is above the corresponding coordinate
of every good. Since `s(slack) coord = M slack` when `coord ≠ slack`, this is
the condition needed for the coordinate model to match the abstract
room/primitive-set model.
-/
def SlackHeightsDominateGoodsCoordinates (u : I → T → ℝ) (M : I → ℝ) : Prop :=
  ∀ slack coord x, coord ≠ slack → u coord x < M slack

/-- Backwards-compatible short name for the slack-height condition. -/
abbrev SlackBounds (u : I → T → ℝ) (M : I → ℝ) : Prop :=
  SlackHeightsDominateGoodsCoordinates (T := T) (I := I) u M

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] IST in
lemma slackBounds_iff_heights_gt_coordinates {u : I → T → ℝ} {M : I → ℝ} :
    SlackBounds (T := T) (I := I) u M ↔ ∀ i j x, j ≠ i → u j x < M i := by
  rfl

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] IST in
lemma slackBounds_of_global_coordinate_bound {u : I → T → ℝ} {M : I → ℝ} {B : ℝ}
    (hGoods : ∀ coord x, u coord x < B) (hHeights : ∀ slack, B ≤ M slack) :
    SlackBounds (T := T) (I := I) u M := by
  intro slack coord x _hcoord
  exact lt_of_lt_of_le (hGoods coord x) (hHeights slack)

/-- The finite set of Scarf slack vectors. -/
def slackImage (M : I → ℝ) : Finset (I → ℝ) :=
  Finset.univ.image (slackVector (I := I) M)

/-- The actual coordinate enlarged set `u(T) ∪ {s(i) | i ∈ I}` from §3. -/
def coordinateEnlargedSet (u : I → T → ℝ) (M : I → ℝ) : Finset (I → ℝ) :=
  utilityImage (T := T) (I := I) u ∪ slackImage (I := I) M

omit [Inhabited T] [DecidableEq T] IST in
lemma extendedCoordinatePoint_mem_coordinateEnlargedSet
    (u : I → T → ℝ) (M : I → ℝ) (z : ExtendedGoods T I) :
    extendedCoordinatePoint (T := T) (I := I) u M z ∈
      coordinateEnlargedSet (T := T) (I := I) u M := by
  cases z with
  | inl x =>
      exact Finset.mem_union_left _
        (Finset.mem_image_of_mem (utilityVector (I := I) u) (Finset.mem_univ x))
  | inr i =>
      exact Finset.mem_union_right _
        (Finset.mem_image_of_mem (slackVector (I := I) M) (Finset.mem_univ i))

omit [Fintype T] [Fintype I] [DecidableEq T] in
lemma slackVector_injective_of_bounds
    {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M) :
    Function.Injective (slackVector (I := I) M) := by
  intro i k hEq
  by_contra hik
  have hcoord := congrFun hEq i
  have hki : i ≠ k := hik
  have hkpos : 0 < M k := by
    have hlt := hM k i default hki
    exact lt_trans (hu.positive i default) (by simpa [slackVector, hki] using hlt)
  exact (ne_of_gt hkpos) (by simpa [slackVector, hki] using hcoord.symm)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma utilityVector_ne_slackVector_of_positive
    {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u) (x : T) (i : I) :
    utilityVector (I := I) u x ≠ slackVector (I := I) M i := by
  intro hEq
  have hcoord := congrFun hEq i
  exact (ne_of_gt (hu.positive i x)) (by simpa [utilityVector, slackVector] using hcoord)

omit [Fintype T] [Fintype I] [DecidableEq T] in
lemma extendedCoordinatePoint_injective_of_realization
    [Inhabited I] {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M) :
    Function.Injective (extendedCoordinatePoint (T := T) (I := I) u M) := by
  intro a b hEq
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          exact congrArg Sum.inl
            (utilityVector_injective_of_realization (IST := IST) hu.toUtilityRealization hEq)
      | inr i =>
          exact False.elim (utilityVector_ne_slackVector_of_positive (IST := IST) hu x i hEq)
  | inr i =>
      cases b with
      | inl y =>
          exact False.elim (utilityVector_ne_slackVector_of_positive (IST := IST) hu y i hEq.symm)
      | inr k =>
          exact congrArg Sum.inr (slackVector_injective_of_bounds (IST := IST) hu hM hEq)

omit [Inhabited T] [DecidableEq T] IST in
lemma coordinateEnlargedSet_exists_preimage
    (u : I → T → ℝ) (M : I → ℝ) {v : I → ℝ}
    (hv : v ∈ coordinateEnlargedSet (T := T) (I := I) u M) :
    ∃ z : ExtendedGoods T I, extendedCoordinatePoint (T := T) (I := I) u M z = v := by
  rcases Finset.mem_union.mp hv with hvGood | hvSlack
  · rcases Finset.mem_image.mp hvGood with ⟨x, _hx, rfl⟩
    exact ⟨Sum.inl x, rfl⟩
  · rcases Finset.mem_image.mp hvSlack with ⟨i, _hi, rfl⟩
    exact ⟨Sum.inr i, rfl⟩

/--
The abstract `T ∪ I` representation is equivalent to the actual coordinate
enlarged set `u(T) ∪ {s(i)}` under the paper's positivity/slack hypotheses.
-/
noncomputable def extendedCoordinateEquivCoordinateEnlargedSet
    [Inhabited I] {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M) :
    ExtendedGoods T I ≃
      {v : I → ℝ // v ∈ coordinateEnlargedSet (T := T) (I := I) u M} where
  toFun z := ⟨extendedCoordinatePoint (T := T) (I := I) u M z,
    extendedCoordinatePoint_mem_coordinateEnlargedSet u M z⟩
  invFun v := Classical.choose
    (coordinateEnlargedSet_exists_preimage (T := T) (I := I) u M v.2)
  left_inv z := by
    apply extendedCoordinatePoint_injective_of_realization (IST := IST) hu hM
    exact Classical.choose_spec
      (coordinateEnlargedSet_exists_preimage (T := T) (I := I) u M
        (extendedCoordinatePoint_mem_coordinateEnlargedSet u M z))
  right_inv v := by
    ext j
    exact congrFun
      (Classical.choose_spec
        (coordinateEnlargedSet_exists_preimage (T := T) (I := I) u M v.2)) j

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] IST in
@[simp] lemma extendedCoordinatePoint_good (u : I → T → ℝ) (M : I → ℝ) (x : T) :
    extendedCoordinatePoint (T := T) (I := I) u M (Sum.inl x) = utilityVector (I := I) u x := rfl

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] IST in
@[simp] lemma extendedCoordinatePoint_slack (u : I → T → ℝ) (M : I → ℝ) (i : I) :
    extendedCoordinatePoint (T := T) (I := I) u M (Sum.inr i) = slackVector (I := I) M i := rfl

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] IST in
lemma slackBounds_lt_slack_coordinate {u : I → T → ℝ} {M : I → ℝ}
    (hM : SlackBounds (T := T) (I := I) u M) {i j : I} (hji : j ≠ i) (x : T) :
    extendedCoordinatePoint (T := T) (I := I) u M (Sum.inl x) j <
      extendedCoordinatePoint (T := T) (I := I) u M (Sum.inr i) j := by
  simpa [extendedCoordinatePoint, utilityVector, slackVector, hji] using hM i j x hji

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma orderUtility_lt_uniformSlackHeight (i : I) (x : T) :
    orderUtility (IST := IST) i x < uniformSlackHeight (T := T) (I := I) i := by
  unfold orderUtility uniformSlackHeight orderLowerSet
  simp only [Function.const_apply]
  have hCard : (Finset.univ.filter (fun y : T => (IST i).le y x)).card ≤ Fintype.card T := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hNat :
      (Finset.univ.filter (fun y : T => (IST i).le y x)).card + 1 <
        Fintype.card T + 2 := by
    omega
  exact_mod_cast hNat

omit [Inhabited T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma orderUtility_slackBounds :
    SlackBounds (T := T) (I := I)
      (fun i x => orderUtility (IST := IST) i x) (uniformSlackHeight (T := T) (I := I)) := by
  intro i j x hji
  simpa [uniformSlackHeight, slackVector, hji] using orderUtility_lt_uniformSlackHeight j x

/--
The coordinate-induced strict relation on `T ∪ I`: one point is smaller
exactly when its `i`th coordinate is smaller. To match the paper, linearity is
kept as an explicit hypothesis below rather than enforced by a tie-breaker.
-/
def extendedCoordinateLt (u : I → T → ℝ) (M : I → ℝ) (i : I)
    (x y : ExtendedGoods T I) : Prop :=
  extendedCoordinatePoint (T := T) (I := I) u M x i <
    extendedCoordinatePoint (T := T) (I := I) u M y i

/--
The paper assumes, after perturbing if necessary, that coordinate values define
linear orders on the enlarged set.
-/
def CoordinateValuesDefineLinearOrders (u : I → T → ℝ) (M : I → ℝ) : Prop :=
  ∀ i, IsStrictTotalOrder (ExtendedGoods T I) (extendedCoordinateLt (T := T) (I := I) u M i)

/-- The paper's "the `M_i` are pairwise different" assumption. -/
def SlackHeightsPairwiseDistinct (M : I → ℝ) : Prop :=
  Function.Injective M

omit [Inhabited T] IST in
/-- All utility coordinates, as a finite set of real numbers. -/
noncomputable def utilityCoordinateValues (u : I → T → ℝ) : Finset ℝ :=
  (Finset.univ.product Finset.univ).image (fun p : I × T => u p.1 p.2)

omit [DecidableEq T] [DecidableEq I] IST in
lemma utilityCoordinateValues_nonempty [Inhabited I] (u : I → T → ℝ) :
    (utilityCoordinateValues (T := T) (I := I) u).Nonempty := by
  refine ⟨u default default, ?_⟩
  unfold utilityCoordinateValues
  rw [Finset.mem_image]
  exact ⟨((default : I), (default : T)), by simp, rfl⟩

omit IST in
/--
A strict upper bound for all utility coordinates.  This packages the finite
maximum used to make the slack heights dominate the goods coordinates.
-/
noncomputable def utilityCoordinateBound [Inhabited I] (u : I → T → ℝ) : ℝ :=
  (utilityCoordinateValues (T := T) (I := I) u).max'
    (utilityCoordinateValues_nonempty (T := T) (I := I) u) + 1

omit [DecidableEq T] [DecidableEq I] IST in
lemma utility_lt_utilityCoordinateBound [Inhabited I] (u : I → T → ℝ) (j : I) (x : T) :
    u j x < utilityCoordinateBound (T := T) (I := I) u := by
  unfold utilityCoordinateBound
  have hmem : u j x ∈ utilityCoordinateValues (T := T) (I := I) u := by
    unfold utilityCoordinateValues
    rw [Finset.mem_image]
    exact ⟨(j, x), by simp, rfl⟩
  have hle :
      u j x ≤ (utilityCoordinateValues (T := T) (I := I) u).max'
        (utilityCoordinateValues_nonempty (T := T) (I := I) u) :=
    Finset.le_max' _ _ hmem
  linarith

/--
An explicit version of the paper's "perturb the slack heights" step: start
above every utility coordinate and then add the finite index of each trader.
-/
noncomputable def perturbedSlackHeight [Inhabited I] (u : I → T → ℝ) : I → ℝ :=
  fun i => utilityCoordinateBound (T := T) (I := I) u + ((Fintype.equivFin I i).val : ℝ)

omit [DecidableEq T] [DecidableEq I] IST in
lemma perturbedSlackHeight_slackBounds [Inhabited I] (u : I → T → ℝ) :
    SlackBounds (T := T) (I := I) u (perturbedSlackHeight (T := T) (I := I) u) := by
  rw [slackBounds_iff_heights_gt_coordinates]
  intro i j x _hji
  have hlt := utility_lt_utilityCoordinateBound (T := T) (I := I) u j x
  have hnonneg : 0 ≤ ((Fintype.equivFin I i).val : ℝ) := by positivity
  unfold perturbedSlackHeight
  linarith

omit [DecidableEq T] [DecidableEq I] IST in
lemma perturbedSlackHeight_pairwiseDistinct [Inhabited I] (u : I → T → ℝ) :
    SlackHeightsPairwiseDistinct (I := I) (perturbedSlackHeight (T := T) (I := I) u) := by
  intro i j hij
  apply (Fintype.equivFin I).injective
  apply Fin.ext
  have hvalReal :
      ((Fintype.equivFin I i).val : ℝ) = ((Fintype.equivFin I j).val : ℝ) := by
    unfold perturbedSlackHeight at hij
    linarith
  exact_mod_cast hvalReal

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma utility_coordinate_injective {u : I → T → ℝ}
    (hu : UtilityRealization (IST := IST) u) (i : I) :
    Function.Injective (fun x : T => u i x) := by
  intro x y hxy
  by_contra hne
  letI : LinearOrder T := IST i
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hltCoord : u i x < u i y := (hu.order_iff i x y).mp hlt
    exact (ne_of_lt hltCoord) hxy
  · have hltCoord : u i y < u i x := (hu.order_iff i y x).mp hgt
    exact (ne_of_lt hltCoord) hxy.symm

omit [Fintype T] [Fintype I] [DecidableEq T] in
lemma extendedCoordinatePoint_coordinate_injective
    {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M)
    (hM_inj : SlackHeightsPairwiseDistinct (I := I) M) (i : I) :
    Function.Injective (fun z : ExtendedGoods T I =>
      extendedCoordinatePoint (T := T) (I := I) u M z i) := by
  intro a b hEq
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          exact congrArg Sum.inl
            (utility_coordinate_injective (IST := IST) hu.toUtilityRealization i
              (by simpa [extendedCoordinatePoint, utilityVector] using hEq))
      | inr k =>
          exfalso
          by_cases hki : k = i
          · have hpos : 0 < u i x := hu.positive i x
            exact (ne_of_gt hpos)
              (by simpa [extendedCoordinatePoint, utilityVector, slackVector, hki.symm] using hEq)
          · have hik : i ≠ k := fun hik => hki hik.symm
            have hlt : u i x < slackVector (I := I) M k i := by
              simpa [slackVector, hik] using hM k i x hik
            exact (ne_of_lt hlt) (by simpa [extendedCoordinatePoint, utilityVector] using hEq)
  | inr k =>
      cases b with
      | inl y =>
          exfalso
          by_cases hki : k = i
          · have hpos : 0 < u i y := hu.positive i y
            exact (ne_of_gt hpos)
              (by simpa [extendedCoordinatePoint, utilityVector, slackVector, hki.symm]
                  using hEq.symm)
          · have hik : i ≠ k := fun hik => hki hik.symm
            have hlt : u i y < slackVector (I := I) M k i := by
              simpa [slackVector, hik] using hM k i y hik
            exact (ne_of_lt hlt) (by simpa [extendedCoordinatePoint, utilityVector] using hEq.symm)
      | inr l =>
          by_cases hki : k = i
          · by_cases hli : l = i
            · exact congrArg Sum.inr (hki.trans hli.symm)
            · exfalso
              have hil : i ≠ l := fun hil => hli hil.symm
              have hlt : u i default < slackVector (I := I) M l i := by
                simpa [slackVector, hil] using hM l i default hil
              have hpos : 0 < slackVector (I := I) M l i :=
                lt_trans (hu.positive i default) hlt
              exact (ne_of_lt hpos)
                (by simpa [extendedCoordinatePoint, slackVector, hki.symm, hil] using hEq)
          · by_cases hli : l = i
            · exfalso
              have hik : i ≠ k := fun hik => hki hik.symm
              have hlt : u i default < slackVector (I := I) M k i := by
                simpa [slackVector, hik] using hM k i default hik
              have hpos : 0 < slackVector (I := I) M k i :=
                lt_trans (hu.positive i default) hlt
              exact (ne_of_lt hpos)
                (by simpa [extendedCoordinatePoint, slackVector, hik, hli.symm] using hEq.symm)
            · have hik : i ≠ k := fun hik => hki hik.symm
              have hil : i ≠ l := fun hil => hli hil.symm
              have hMkMl : M k = M l := by
                simpa [extendedCoordinatePoint, slackVector, hik, hil] using hEq
              exact congrArg Sum.inr (hM_inj hMkMl)

omit [Fintype T] [Fintype I] [DecidableEq T] in
/--
Under the hypotheses stated in §3 (positive utilities realizing the
preferences, slack bounds, and pairwise different slack heights), coordinate
values themselves define linear orders on `T ∪ I`.
-/
theorem coordinateValuesDefineLinearOrders_of_realization
    {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M)
    (hM_inj : SlackHeightsPairwiseDistinct (I := I) M) :
    CoordinateValuesDefineLinearOrders (T := T) (I := I) u M := by
  intro i
  let f : ExtendedGoods T I → ℝ :=
    fun z => extendedCoordinatePoint (T := T) (I := I) u M z i
  have hf : Function.Injective f :=
    extendedCoordinatePoint_coordinate_injective (IST := IST) hu hM hM_inj i
  exact
    { trichotomous := by
        intro a b hab hba
        apply hf
        exact le_antisymm (le_of_not_gt hba) (le_of_not_gt hab)
      irrefl := by
        intro a
        exact lt_irrefl (f a)
      trans := by
        intro a b c hab hbc
        exact lt_trans hab hbc }

omit [DecidableEq T] [Fintype T] [Fintype I] in
/--
The fully formalized perturbation step from §3: for every positive utility
realization on a finite, nonempty index set, there are slack heights that
dominate all goods coordinates, are pairwise distinct, and therefore make
coordinate comparison into linear orders on `T ∪ I`.
-/
theorem exists_perturbedSlackHeights_for_coordinate_orders [Inhabited I] [Finite T] [Finite I]
    {u : I → T → ℝ} (hu : PositiveUtilityRealization (IST := IST) u) :
    ∃ M : I → ℝ,
      SlackBounds (T := T) (I := I) u M ∧
      SlackHeightsPairwiseDistinct (I := I) M ∧
      CoordinateValuesDefineLinearOrders (T := T) (I := I) u M := by
  have : Fintype T := Fintype.ofFinite T
  have : Fintype I := Fintype.ofFinite I
  let M := perturbedSlackHeight (T := T) (I := I) u
  have hBounds : SlackBounds (T := T) (I := I) u M :=
    perturbedSlackHeight_slackBounds (T := T) (I := I) u
  have hDistinct : SlackHeightsPairwiseDistinct (I := I) M :=
    perturbedSlackHeight_pairwiseDistinct (T := T) (I := I) u
  exact ⟨M, hBounds, hDistinct,
    coordinateValuesDefineLinearOrders_of_realization (IST := IST) hu hBounds hDistinct⟩

omit [DecidableEq T] [Fintype T] [Fintype I] in
/--
The §3 utility-and-perturbation passage as a single existence statement:
starting only from the abstract indexed linear orders, choose positive utility
functions realizing the orders and pairwise distinct slack heights large enough
to make coordinate comparison linear on the enlarged set.
-/
theorem exists_coordinateUtilityModel [Inhabited I] [Finite T] [Finite I] :
    ∃ (u : I → T → ℝ) (M : I → ℝ),
      PositiveUtilityRealization (IST := IST) u ∧
      SlackBounds (T := T) (I := I) u M ∧
      SlackHeightsPairwiseDistinct (I := I) M ∧
      CoordinateValuesDefineLinearOrders (T := T) (I := I) u M := by
  have : Fintype T := Fintype.ofFinite T
  have : Fintype I := Fintype.ofFinite I
  let u : I → T → ℝ := fun i x => orderUtility (IST := IST) i x
  have hu : PositiveUtilityRealization (IST := IST) u :=
    positiveOrderUtility_realization (IST := IST)
  obtain ⟨M, hBounds, hDistinct, hCoord⟩ :=
    exists_perturbedSlackHeights_for_coordinate_orders (IST := IST) hu
  exact ⟨u, M, hu, hBounds, hDistinct, hCoord⟩

/-- The indexed family of coordinate-induced orders on the enlarged set. -/
@[reducible]
def coordinateIndexedLOrder (u : I → T → ℝ) (M : I → ℝ)
    (hCoord : CoordinateValuesDefineLinearOrders (T := T) (I := I) u M) :
    IndexedLOrder I (ExtendedGoods T I) where
  IST := fun i =>
    letI : IsStrictTotalOrder (ExtendedGoods T I)
      (extendedCoordinateLt (T := T) (I := I) u M i) := hCoord i
    linearOrderOfSTO (extendedCoordinateLt (T := T) (I := I) u M i)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] IST in
lemma extendedCoordinateLt_of_coord_lt {u : I → T → ℝ} {M : I → ℝ}
    {i : I} {x y : ExtendedGoods T I}
    (h : extendedCoordinatePoint (T := T) (I := I) u M x i <
      extendedCoordinatePoint (T := T) (I := I) u M y i) :
    extendedCoordinateLt (T := T) (I := I) u M i x y := by
  exact h

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma extendedCoordinateLt_goods_of_original_lt {u : I → T → ℝ} {M : I → ℝ}
    (hu : UtilityRealization (IST := IST) u) {i : I} {x y : T}
    (hxy : (IST i).lt x y) :
    extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl x) (Sum.inl y) := by
  apply extendedCoordinateLt_of_coord_lt
  simpa [extendedCoordinatePoint, utilityVector] using (hu.order_iff i x y).mp hxy

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma original_lt_of_extendedCoordinateLt_goods {u : I → T → ℝ} {M : I → ℝ}
    (hu : UtilityRealization (IST := IST) u) {i : I} {x y : T}
    (hxy : extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl x) (Sum.inl y)) :
    (IST i).lt x y := by
  exact (hu.order_iff i x y).mpr (by simpa [extendedCoordinateLt, extendedCoordinatePoint,
    utilityVector] using hxy)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma extendedCoordinateLt_goods_iff {u : I → T → ℝ} {M : I → ℝ}
    (hu : UtilityRealization (IST := IST) u) (i : I) (x y : T) :
    extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl x) (Sum.inl y) ↔
      (IST i).lt x y :=
  ⟨original_lt_of_extendedCoordinateLt_goods hu, extendedCoordinateLt_goods_of_original_lt hu⟩

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma coordinateGoods_le_of_original_le {u : I → T → ℝ} {M : I → ℝ}
    (hCoord : CoordinateValuesDefineLinearOrders (T := T) (I := I) u M)
    (hu : UtilityRealization (IST := IST) u) {i : I} {x y : T}
    (hxy : (IST i).le x y) :
    ((coordinateIndexedLOrder (T := T) (I := I) u M hCoord) i).le (Sum.inl x) (Sum.inl y) := by
  letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I) u M hCoord) i
  letI : LinearOrder T := IST i
  by_cases hEq : x = y
  · subst hEq
    exact le_rfl
  · exact le_of_lt (show ((coordinateIndexedLOrder (T := T) (I := I) u M hCoord) i).lt
      (Sum.inl x) (Sum.inl y) from
        extendedCoordinateLt_goods_of_original_lt hu (lt_of_le_of_ne hxy hEq))

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma original_le_of_coordinateGoods_le {u : I → T → ℝ} {M : I → ℝ}
    (hCoord : CoordinateValuesDefineLinearOrders (T := T) (I := I) u M)
    (hu : UtilityRealization (IST := IST) u) {i : I} {x y : T}
    (hxy : ((coordinateIndexedLOrder (T := T) (I := I) u M hCoord) i).le (Sum.inl x) (Sum.inl y)) :
    (IST i).le x y := by
  letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I) u M hCoord) i
  letI : LinearOrder T := IST i
  by_contra hnot
  have hyx : (IST i).lt y x := lt_of_not_ge hnot
  have hCoordLt : extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl y) (Sum.inl x) :=
    extendedCoordinateLt_goods_of_original_lt hu hyx
  exact not_lt_of_ge hxy (show ((coordinateIndexedLOrder (T := T) (I := I) u M hCoord) i).lt
    (Sum.inl y) (Sum.inl x) from hCoordLt)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] IST in
lemma coordinateGood_lt_slack_of_ne {u : I → T → ℝ} {M : I → ℝ}
    (hM : SlackBounds (T := T) (I := I) u M) {i k : I} (hik : i ≠ k) (x : T) :
    extendedCoordinateLt (T := T) (I := I) u M i (Sum.inl x) (Sum.inr k) := by
  apply extendedCoordinateLt_of_coord_lt
  simpa [extendedCoordinatePoint, utilityVector, slackVector, hik] using hM k i x hik

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma coordinateSlack_lt_good {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u) (i : I) (x : T) :
    extendedCoordinateLt (T := T) (I := I) u M i (Sum.inr i) (Sum.inl x) := by
  apply extendedCoordinateLt_of_coord_lt
  simpa [extendedCoordinatePoint, utilityVector, slackVector] using hu.positive i x

omit [Fintype T] [Fintype I] [DecidableEq T] in
lemma coordinateSlack_lt_slack_of_ne {u : I → T → ℝ} {M : I → ℝ}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M) {i k : I} (hik : i ≠ k) :
    extendedCoordinateLt (T := T) (I := I) u M i (Sum.inr i) (Sum.inr k) := by
  apply extendedCoordinateLt_of_coord_lt
  have hposM : 0 < slackVector (I := I) M k i :=
    lt_trans (hu.positive i (default : T)) (by
      simpa [slackVector, hik] using hM k i default hik)
  simpa [extendedCoordinatePoint, slackVector, hik] using hposM

/-- The literal coordinate-dominance primitive definition on the enlarged ordered set. -/
def isCoordinatePrimitive (u : I → T → ℝ) (M : I → ℝ)
    (hCoord : CoordinateValuesDefineLinearOrders (T := T) (I := I) u M)
    (X : Finset (ExtendedGoods T I)) : Prop :=
  X.card = Fintype.card I ∧
    (coordinateIndexedLOrder (T := T) (I := I) u M hCoord).isDominant X Finset.univ

theorem nativePrimitive_to_coordinatePrimitive {u : I → T → ℝ} {M : I → ℝ}
    {hCoord : CoordinateValuesDefineLinearOrders (T := T) (I := I) u M}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M)
    {X : Finset (ExtendedGoods T I)} (hX : isPrimitiveNative (IST := IST) X) :
    isCoordinatePrimitive (T := T) (I := I) u M hCoord X := by
  constructor
  · exact hX.1
  · intro y
    let σ := fromGoods (T := T) (I := I) X
    let C := fromMissing (T := T) (I := I) X
    cases y with
    | inl t =>
        obtain ⟨i, hiC, hleGoods⟩ := hX.2 t
        refine ⟨i, Finset.mem_univ i, ?_⟩
        intro z hz
        cases z with
        | inl x =>
            have hxσ : x ∈ σ := by simpa [σ] using hz
            exact coordinateGoods_le_of_original_le hCoord hu.toUtilityRealization (hleGoods x hxσ)
        | inr k =>
            have hkNotC : k ∉ C := by simpa [C] using hz
            have hik : i ≠ k := by
              intro hEq
              exact hkNotC (hEq ▸ hiC)
            letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I)
                u M hCoord) i
            exact le_of_lt (show ((coordinateIndexedLOrder (T := T) (I := I) u M hCoord) i).lt
              (Sum.inl t) (Sum.inr k) from coordinateGood_lt_slack_of_ne hM hik t)
    | inr j =>
        refine ⟨j, Finset.mem_univ j, ?_⟩
        intro z hz
        cases z with
        | inl x =>
            letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I)
                u M hCoord) j
            exact le_of_lt (show ((coordinateIndexedLOrder (T := T) (I := I) u M hCoord) j).lt
              (Sum.inr j) (Sum.inl x) from coordinateSlack_lt_good (M := M) hu j x)
        | inr k =>
            by_cases hkj : k = j
            · subst hkj
              letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I)
                  u M hCoord) k
              exact le_rfl
            · letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I)
                u M hCoord) j
              exact le_of_lt (show ((coordinateIndexedLOrder (T := T) (I := I) u M hCoord) j).lt
                (Sum.inr j) (Sum.inr k) from coordinateSlack_lt_slack_of_ne hu hM (Ne.symm hkj))

omit [Inhabited T] in
theorem coordinatePrimitive_to_nativePrimitive {u : I → T → ℝ} {M : I → ℝ}
    {hCoord : CoordinateValuesDefineLinearOrders (T := T) (I := I) u M}
    (hu : PositiveUtilityRealization (IST := IST) u)
    {X : Finset (ExtendedGoods T I)}
    (hX : isCoordinatePrimitive (T := T) (I := I) u M hCoord X) :
    isPrimitiveNative (IST := IST) X := by
  constructor
  · exact hX.1
  · intro y
    obtain ⟨i, _hi, hleX⟩ := hX.2 (Sum.inl y)
    have hiMissing : i ∈ fromMissing (T := T) (I := I) X := by
      rw [mem_fromMissing]
      intro hiSlack
      have hleSlack := hleX (Sum.inr i) hiSlack
      have hSlackLtGood := coordinateSlack_lt_good (M := M) hu i y
      letI : LinearOrder (ExtendedGoods T I) := (coordinateIndexedLOrder (T := T) (I := I)
          u M hCoord) i
      exact not_lt_of_ge hleSlack (show ((coordinateIndexedLOrder (T := T) (I := I) u M hCoord)
          i).lt
        (Sum.inr i) (Sum.inl y) from hSlackLtGood)
    refine ⟨i, hiMissing, ?_⟩
    intro x hx
    have hleGood := hleX (Sum.inl x) (by simpa using hx)
    exact original_le_of_coordinateGoods_le hCoord hu.toUtilityRealization hleGood

theorem coordinatePrimitive_iff_native {u : I → T → ℝ} {M : I → ℝ}
    {hCoord : CoordinateValuesDefineLinearOrders (T := T) (I := I) u M}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M)
    {X : Finset (ExtendedGoods T I)} :
    isCoordinatePrimitive (T := T) (I := I) u M hCoord X ↔ isPrimitiveNative (IST := IST) X :=
  ⟨coordinatePrimitive_to_nativePrimitive hu, nativePrimitive_to_coordinatePrimitive hu hM⟩

/--
Scarf's main lemma for the literal coordinate-dominance definition of
primitive sets on `T ∪ I`.
-/
theorem coordinatePrimitive_erase_replacement_mainLemma
    {u : I → T → ℝ} {M : I → ℝ}
    {hCoord : CoordinateValuesDefineLinearOrders (T := T) (I := I) u M}
    (hu : PositiveUtilityRealization (IST := IST) u)
    (hM : SlackBounds (T := T) (I := I) u M)
    {X : Finset (ExtendedGoods T I)}
    (hX : isCoordinatePrimitive (T := T) (I := I) u M hCoord X)
    {x : ExtendedGoods T I} (hx : x ∈ X) :
    ¬ (fromGoods (T := T) (I := I) (X.erase x)).Nonempty ∨
      ∃! y : ExtendedGoods T I,
        y ∉ X ∧ isCoordinatePrimitive (T := T) (I := I) u M hCoord (insert y (X.erase x)) := by
  obtain hBoundary | hReplace :=
    native_primitive_erase_replacement_mainLemma
      (IST := IST) (coordinatePrimitive_to_nativePrimitive hu hX) hx
  · exact Or.inl hBoundary
  · right
    rcases hReplace with ⟨y, ⟨hyNotX, hyPrim⟩, hUnique⟩
    refine ⟨y, ⟨hyNotX, (coordinatePrimitive_iff_native hu hM).2 hyPrim⟩, ?_⟩
    intro z hz
    exact hUnique z ⟨hz.1, (coordinatePrimitive_iff_native hu hM).1 hz.2⟩

end IndexedLOrder

end
