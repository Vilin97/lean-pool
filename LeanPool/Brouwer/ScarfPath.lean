/-
Copyright (c) 2026 Math_XMUM. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Math_XMUM
-/
import LeanPool.Brouwer.Scarf
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# The Scarf path graph

This file builds the graph `G_i` whose vertices are the colorful and typed
nearly-colorful rooms and doors of a fixed type `i`, and whose edges are
room-door incidences. Following a path in this graph between odd-degree vertices
is the combinatorial heart of the path-following proof of Scarf's lemma.
-/

attribute [local instance] Classical.propDecidable
open Finset

noncomputable section

namespace IndexedLOrder

variable {T I : Type*} [Inhabited T] [Fintype T] [Fintype I]
variable [DecidableEq T] [DecidableEq I] [IST : IndexedLOrder I T]

/-- A room/door cell, represented as the pair `(σ, C)`. -/
abbrev GiCell (T I : Type*) := Finset T × Finset I

/-- The room-type vertices of the graph `G_i`: colorful rooms and typed nearly-colorful rooms. -/
def GiRoomVertex (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  IST.isColorful c v.1 v.2 ∨
    (IST.isRoom v.1 v.2 ∧ IST.isTypedNC c i v.1 v.2)

/-- The door-type vertices of the graph `G_i`: typed nearly-colorful doors. -/
def GiDoorVertex (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  IST.isDoor v.1 v.2 ∧ IST.isTypedNC c i v.1 v.2

/-- Vertices of `G_i`: the relevant rooms and doors of fixed type `i`. -/
def GiVertex (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  GiRoomVertex (IST := IST) c i v ∨ GiDoorVertex (IST := IST) c i v

/-- Edges of `G_i`: room-door incidence, made symmetric. -/
def GiEdge (c : T → I) (i : I) (v w : GiCell T I) : Prop :=
  (GiRoomVertex (IST := IST) c i v ∧
    GiDoorVertex (IST := IST) c i w ∧
      IST.isDoorof w.1 w.2 v.1 v.2) ∨
  (GiRoomVertex (IST := IST) c i w ∧
    GiDoorVertex (IST := IST) c i v ∧
      IST.isDoorof v.1 v.2 w.1 w.2)

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma GiEdge.symm {c : T → I} {i : I} {v w : GiCell T I}
    (h : GiEdge (IST := IST) c i v w) :
    GiEdge (IST := IST) c i w v :=
  h.elim Or.inr Or.inl

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma GiEdge.left_vertex {c : T → I} {i : I} {v w : GiCell T I}
    (h : GiEdge (IST := IST) c i v w) :
    GiVertex (IST := IST) c i v :=
  h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2.1)

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma GiEdge.right_vertex {c : T → I} {i : I} {v w : GiCell T I}
    (h : GiEdge (IST := IST) c i v w) :
    GiVertex (IST := IST) c i w :=
  (GiEdge.symm h).left_vertex

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma GiRoomVertex.room {c : T → I} {i : I} {v : GiCell T I}
    (h : GiRoomVertex (IST := IST) c i v) :
    IST.isRoom v.1 v.2 :=
  h.elim IST.room_of_colorful (·.1)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma GiDoorVertex.door {c : T → I} {i : I} {v : GiCell T I}
    (h : GiDoorVertex (IST := IST) c i v) :
    IST.isDoor v.1 v.2 := h.1

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma GiEdge.irrefl {c : T → I} {i : I} (v : GiCell T I) :
    ¬ GiEdge (IST := IST) c i v v := by
  intro h
  rcases h with h | h <;>
    exact absurd h.2.1.door.2 (by have := h.1.room.2; omega)

/-- The Mathlib `SimpleGraph` whose vertices and edges are the graph `G_i`. -/
def GiGraph (c : T → I) (i : I) : SimpleGraph (GiCell T I) where
  Adj := GiEdge (IST := IST) c i
  symm := ⟨fun _ _ h => GiEdge.symm h⟩
  loopless := ⟨fun v => GiEdge.irrefl (IST := IST) (c := c) (i := i) v⟩

/-- The finite neighbor set of a vertex in `G_i`. -/
def GiNeighbors (c : T → I) (i : I) (v : GiCell T I) : Finset (GiCell T I) :=
  (GiGraph (IST := IST) c i).neighborFinset v

omit [Inhabited T] in
lemma mem_GiNeighbors {c : T → I} {i : I} {v w : GiCell T I} :
    w ∈ GiNeighbors (IST := IST) c i v ↔ GiEdge (IST := IST) c i v w := by
  exact SimpleGraph.mem_neighborFinset (GiGraph (IST := IST) c i) v w

/-- Degree in `G_i`. -/
def GiDegree (c : T → I) (i : I) (v : GiCell T I) : Nat :=
  (GiNeighbors (IST := IST) c i v).card

/-- Endpoint vertices of `G_i`. -/
def GiEndpoint (c : T → I) (i : I) (v : GiCell T I) : Prop :=
  GiVertex (IST := IST) c i v ∧ GiDegree (IST := IST) c i v = 1

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma not_room_of_door {τ : Finset T} {D : Finset I}
    (hDoor : IST.isDoor τ D) :
    ¬ IST.isRoom τ D := by
  intro hRoom
  have := hDoor.2; have := hRoom.2; omega

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma not_colorful_of_door {c : T → I} {τ : Finset T} {D : Finset I}
    (hDoor : IST.isDoor τ D) :
    ¬ IST.isColorful c τ D :=
  fun hColorful => not_room_of_door hDoor (IST.room_of_colorful hColorful)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma not_GiRoomVertex_of_door {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hDoor : IST.isDoor τ D) :
    ¬ GiRoomVertex (IST := IST) c i (τ, D) :=
  fun hRoomVertex => hRoomVertex.elim (not_colorful_of_door hDoor)
    (fun hTypedRoom => not_room_of_door hDoor hTypedRoom.1)

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] [DecidableEq I] in
lemma not_door_of_room {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) :
    ¬ IST.isDoor σ C :=
  fun hDoor => not_room_of_door hDoor hRoom

omit [Inhabited T] [Fintype T] [Fintype I] [DecidableEq T] in
lemma not_GiDoorVertex_of_room {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) :
    ¬ GiDoorVertex (IST := IST) c i (σ, C) :=
  fun hDoorVertex => not_door_of_room hRoom hDoorVertex.1

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma isDoor_of_Doorof {τ σ : Finset T} {D C : Finset I}
    (hDoorof : IST.isDoorof τ D σ C) :
    IST.isDoor τ D := by
  cases hDoorof with
  | idoor _ hDoor _ _ _ _ => exact hDoor
  | odoor _ hDoor _ _ _ _ => exact hDoor

omit [Inhabited T] [Fintype T] [Fintype I] in
lemma GiRoomVertex_of_incident_typed_door {c : T → I} {i : I}
    {τ σ : Finset T} {D C : Finset I}
    (hTypedDoor : IST.isTypedNC c i τ D)
    (hDoorof : IST.isDoorof τ D σ C) :
    GiRoomVertex (IST := IST) c i (σ, C) := by
  exact (IST.NC_or_C_of_door hTypedDoor hDoorof).elim
    (fun hTypedRoom => Or.inr ⟨IST.isRoom_of_Door hDoorof, hTypedRoom⟩) Or.inl

omit [Inhabited T] in
theorem GiDegree_internalDoor {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hInternal : IST.isInternalDoor τ D) (hTyped : IST.isTypedNC c i τ D) :
    GiDegree (IST := IST) c i (τ, D) = 2 := by
  obtain ⟨σ₁, σ₂, C₁, C₂, hNe, hRoom₁, hRoom₂, hDoor₁, hDoor₂, hUnique⟩ :=
    IST.internal_door_two_rooms τ D hInternal
  have hNeighbors :
      GiNeighbors (IST := IST) c i (τ, D) = ({(σ₁, C₁), (σ₂, C₂)} : Finset (GiCell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : GiEdge (IST := IST) c i (τ, D) w := (mem_GiNeighbors).1 hw
      rcases hEdge with hBad | hGood
      · exact False.elim (not_GiRoomVertex_of_door hInternal.1 hBad.1)
      · obtain hCases := hUnique w.1 w.2 (IST.isRoom_of_Door hGood.2.2) hGood.2.2
        rw [Finset.mem_insert, Finset.mem_singleton]
        rcases hCases with hLeft | hRight
        · exact Or.inl (Prod.ext hLeft.1 hLeft.2)
        · exact Or.inr (Prod.ext hRight.1 hRight.2)
    · intro hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      apply (mem_GiNeighbors).2
      rcases hw with hEq | hEq
      · exact hEq ▸ Or.inr ⟨GiRoomVertex_of_incident_typed_door hTyped hDoor₁,
          ⟨hInternal.1, hTyped⟩, hDoor₁⟩
      · exact hEq ▸ Or.inr ⟨GiRoomVertex_of_incident_typed_door hTyped hDoor₂,
          ⟨hInternal.1, hTyped⟩, hDoor₂⟩
  rw [GiDegree, hNeighbors]
  exact Finset.card_pair hNe

omit [Inhabited T] in
theorem GiDegree_typedNCRoom {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hRoom : IST.isRoom σ C) (hTyped : IST.isTypedNC c i σ C) :
    GiDegree (IST := IST) c i (σ, C) = 2 := by
  obtain ⟨door₁, door₂, hNe, hDoors⟩ :=
    IST.doors_of_NCroom (c := c) hRoom (IST.NC_of_TNC hTyped)
  have hNeighbors :
      GiNeighbors (IST := IST) c i (σ, C) = ({door₁, door₂} : Finset (GiCell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : GiEdge (IST := IST) c i (σ, C) w := (mem_GiNeighbors).1 hw
      rcases hEdge with hGood | hBad
      · have hwDoor : w ∈ IST.NCdoors c σ C := by
          change IST.isNearlyColorful c w.1 w.2 ∧ IST.isDoorof w.1 w.2 σ C
          exact ⟨IST.NC_of_TNC hGood.2.1.2, hGood.2.2⟩
        rw [hDoors] at hwDoor
        simpa using hwDoor
      · exact False.elim (not_GiDoorVertex_of_room hRoom hBad.2.1)
    · intro hw
      have hwDoor : w ∈ IST.NCdoors c σ C := by
        rw [hDoors]
        simpa using hw
      change IST.isNearlyColorful c w.1 w.2 ∧ IST.isDoorof w.1 w.2 σ C at hwDoor
      let hTypedDoor := IST.isTypedNC_of_isNearlyColorful_of_isDoorof_isTypedNC
        hwDoor.1 hwDoor.2 hTyped
      apply (mem_GiNeighbors).2
      exact Or.inl ⟨Or.inr ⟨hRoom, hTyped⟩,
        ⟨isDoor_of_Doorof hwDoor.2, hTypedDoor⟩,
        hwDoor.2⟩
  rw [GiDegree, hNeighbors]
  exact Finset.card_pair hNe

theorem GiDegree_outsideDoor {c : T → I} {i : I} {τ : Finset T} {D : Finset I}
    (hOutside : IST.isOutsideDoor τ D) (hTyped : IST.isTypedNC c i τ D) :
    GiDegree (IST := IST) c i (τ, D) = 1 := by
  have hτ : τ = Finset.empty := hOutside.2
  have hD : D = ({i} : Finset I) := by
    have h := hTyped.2
    rw [hτ] at h
    have hImg : Finset.image c (Finset.empty : Finset T) = Finset.empty := Finset.image_empty c
    rw [hImg] at h
    have hsdiff : D \ (Finset.empty : Finset I) = D :=
      Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_empty_right D)
    rwa [hsdiff] at h
  let xMax : T := @Finset.max' T (IST i) Finset.univ
    (Finset.univ_nonempty_iff.mpr ⟨(default : T)⟩)
  let room : GiCell T I := ({xMax}, ({i} : Finset I))
  have hCellRoom : IST.isCell ({xMax} : Finset T) ({i} : Finset I) := by
    intro y
    refine ⟨i, by simp, ?_⟩
    intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact @Finset.le_max' T (IST i) Finset.univ y (Finset.mem_univ y)
  have hDoorofRoom : IST.isDoorof τ D ({xMax} : Finset T) ({i} : Finset I) := by
    rw [hτ, hD]
    apply isDoorof.idoor hCellRoom (IST.outsidedoor_singleton i).1 xMax
    · exact Finset.notMem_empty xMax
    · rfl
    · rfl
  have hNeighbors :
      GiNeighbors (IST := IST) c i (τ, D) = ({room} : Finset (GiCell T I)) := by
    ext w
    constructor
    · intro hw
      have hEdge : GiEdge (IST := IST) c i (τ, D) w := (mem_GiNeighbors).1 hw
      rcases hEdge with hBad | hGood
      · exact False.elim (not_GiRoomVertex_of_door hOutside.1 hBad.1)
      · have hDoorof : IST.isDoorof τ D w.1 w.2 := hGood.2.2
        have hRoomW : IST.isRoom w.1 w.2 := IST.isRoom_of_Door hDoorof
        rw [hτ, hD] at hDoorof
        cases hDoorof with
        | idoor hCell _ x _ hInsert hDEq =>
            rw [Finset.mem_singleton]
            apply Prod.ext
            · have hwσ : w.1 = ({x} : Finset T) := by
                rw [← hInsert]
                rfl
              have hxMax : x = xMax := by
                have hAbove : ∀ y : T, (IST i).le y x := by
                  intro y
                  obtain ⟨j, hj, hle⟩ := hCell y
                  have hji : j = i := by
                    rw [← hDEq] at hj
                    exact Finset.mem_singleton.mp hj
                  subst hji
                  apply hle
                  rw [hwσ]
                  simp
                have hx_le_max : (IST i).le x xMax :=
                  @Finset.le_max' T (IST i) Finset.univ x (Finset.mem_univ x)
                have hmax_le_x : (IST i).le xMax x := hAbove xMax
                exact @le_antisymm T (IST i).toPartialOrder x xMax hx_le_max hmax_le_x
              rw [hwσ, hxMax]
            · exact hDEq.symm
        | odoor _ _ _ _ hτEq _ =>
            exfalso
            have hσEmpty : w.1 = Finset.empty := by
              simpa using hτEq.symm
            have hNonempty := IST.sigma_nonempty_of_room hRoomW
            rw [hσEmpty] at hNonempty
            exact Finset.not_nonempty_empty hNonempty
    · intro hw
      rw [Finset.mem_singleton] at hw
      rw [hw]
      apply (mem_GiNeighbors).2
      exact Or.inr ⟨GiRoomVertex_of_incident_typed_door hTyped hDoorofRoom,
        ⟨hOutside.1, hTyped⟩, hDoorofRoom⟩
  rw [GiDegree, hNeighbors]
  simp

omit [Inhabited T] in
theorem GiDegree_colorfulRoom {c : T → I} {i : I} {σ : Finset T} {C : Finset I}
    (hColorful : IST.isColorful c σ C) :
    GiDegree (IST := IST) c i (σ, C) = 1 := by
  have hRoom : IST.isRoom σ C := IST.room_of_colorful hColorful
  have hInj : Set.InjOn c (↑σ : Set T) := by
    apply (Finset.card_image_iff).mp
    rw [hColorful.2, hRoom.2]
  by_cases hiC : i ∈ C
  · have hiImage : i ∈ σ.image c := by
      rwa [hColorful.2]
    obtain ⟨x, hxσ, hcx⟩ := Finset.mem_image.mp hiImage
    let door : GiCell T I := (σ.erase x, C)
    have hxUnique : ∀ ⦃y⦄, y ∈ σ → c y = c x → y = x := by
      intro y hy hcy
      exact hInj hy hxσ hcy
    have hDoorof : IST.isDoorof (σ.erase x) C σ C :=
      IST.collision_door_valid σ C c x hColorful.1 hxσ hRoom.2
    have hTypedDoor : IST.isTypedNC c i (σ.erase x) C := by
      constructor
      · exact IST.Dominant_of_subset σ (σ.erase x) C (Finset.erase_subset x σ) hColorful.1
      · have hImgErase :
            (σ.erase x).image c = (σ.image c).erase (c x) :=
          image_erase_eq_erase_image_of_unique σ c hxσ hxUnique
        rw [hImgErase, ← hColorful.2, hcx]
        ext j
        constructor
        · intro hj
          rcases Finset.mem_sdiff.mp hj with ⟨hjC, hjNotErase⟩
          by_cases hji : j = i
          · simp [hji]
          · have hjErase : j ∈ (σ.image c).erase i := Finset.mem_erase.mpr ⟨hji, hjC⟩
            exact False.elim (hjNotErase hjErase)
        · intro hj
          have hji : j = i := Finset.mem_singleton.mp hj
          subst hji
          exact Finset.mem_sdiff.mpr ⟨hiImage, by simp⟩
    have hNeighbors :
        GiNeighbors (IST := IST) c i (σ, C) = ({door} : Finset (GiCell T I)) := by
      ext w
      constructor
      · intro hw
        have hEdge : GiEdge (IST := IST) c i (σ, C) w := (mem_GiNeighbors).1 hw
        rcases hEdge with hGood | hBad
        · have hDoorofW : IST.isDoorof w.1 w.2 σ C := hGood.2.2
          have hTypedW : IST.isTypedNC c i w.1 w.2 := hGood.2.1.2
          cases hDoorofW with
          | idoor _ _ y hyNot hInsert hDEq =>
              have hyσ : y ∈ σ := by
                rw [← hInsert]
                exact Finset.mem_insert_self y w.1
              have hwσ : w.1 = σ.erase y := by
                rw [← Finset.erase_insert hyNot, hInsert]
              have hcyNotErase : c y ∉ (σ.erase y).image c := by
                intro hmem
                rcases Finset.mem_image.mp hmem with ⟨z, hzErase, hcz⟩
                have hzσ : z ∈ σ := Finset.erase_subset y σ hzErase
                have hzEq : z = y := hInj hzσ hyσ hcz
                exact (Finset.mem_erase.mp hzErase).1 hzEq
              have hcyDiff : c y ∈ w.2 \ w.1.image c := by
                rw [hDEq, hwσ]
                exact Finset.mem_sdiff.mpr
                  ⟨by rw [← hColorful.2]; exact Finset.mem_image_of_mem c hyσ, hcyNotErase⟩
              have hcyi : c y = i := by
                rw [hTypedW.2] at hcyDiff
                exact Finset.mem_singleton.mp hcyDiff
              have hyx : y = x := hInj hyσ hxσ (hcyi.trans hcx.symm)
              rw [Finset.mem_singleton]
              apply Prod.ext
              · rw [hwσ, hyx]
              · exact hDEq
          | odoor _ _ j _ hτEq _ =>
              exfalso
              have hiDiff : i ∈ w.2 \ w.1.image c := by
                rw [hTypedW.2]
                simp
              have hiNotImage : i ∉ w.1.image c := (Finset.mem_sdiff.mp hiDiff).2
              rw [hτEq] at hiNotImage
              exact hiNotImage hiImage
        · exact False.elim (not_GiDoorVertex_of_room hRoom hBad.2.1)
      · intro hw
        rw [Finset.mem_singleton] at hw
        rw [hw]
        apply (mem_GiNeighbors).2
        exact Or.inl ⟨Or.inl hColorful, ⟨isDoor_of_Doorof hDoorof, hTypedDoor⟩, hDoorof⟩
    rw [GiDegree, hNeighbors]
    simp
  · let door : GiCell T I := (σ, insert i C)
    have hDoor : IST.isDoor σ (insert i C) := by
      constructor
      · exact IST.Dominant_of_supset σ C (insert i C) (Finset.subset_insert i C) hColorful.1
      · rw [Finset.card_insert_of_notMem hiC, hRoom.2]
    have hDoorof : IST.isDoorof σ (insert i C) σ C :=
      isDoorof.odoor hColorful.1 hDoor i hiC rfl rfl
    have hTypedDoor : IST.isTypedNC c i σ (insert i C) := by
      constructor
      · exact hDoor.1
      · rw [← hColorful.2]
        ext j
        constructor
        · intro hj
          rcases Finset.mem_sdiff.mp hj with ⟨hjInsert, hjNotImage⟩
          rcases Finset.mem_insert.mp hjInsert with hji | hjImage
          · simp [hji]
          · exact False.elim (hjNotImage hjImage)
        · intro hj
          have hji : j = i := Finset.mem_singleton.mp hj
          rw [hji]
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_insert_self i (σ.image c), by
              rwa [hColorful.2]⟩
    have hNeighbors :
        GiNeighbors (IST := IST) c i (σ, C) = ({door} : Finset (GiCell T I)) := by
      ext w
      constructor
      · intro hw
        have hEdge : GiEdge (IST := IST) c i (σ, C) w := (mem_GiNeighbors).1 hw
        rcases hEdge with hGood | hBad
        · have hDoorofW : IST.isDoorof w.1 w.2 σ C := hGood.2.2
          have hTypedW : IST.isTypedNC c i w.1 w.2 := hGood.2.1.2
          cases hDoorofW with
          | idoor _ _ y _ _ hDEq =>
              exfalso
              have hiDiff : i ∈ w.2 \ w.1.image c := by
                rw [hTypedW.2]
                simp
              have hiC' : i ∈ C := by
                rw [hDEq] at hiDiff
                exact (Finset.mem_sdiff.mp hiDiff).1
              exact hiC hiC'
          | odoor _ _ j hjNotC hτEq hDEq =>
              have hjDiff : j ∈ w.2 \ w.1.image c := by
                rw [hDEq, hτEq]
                exact Finset.mem_sdiff.mpr
                  ⟨Finset.mem_insert_self j C, by
                    rw [hColorful.2]
                    exact hjNotC⟩
              have hji : j = i := by
                rw [hTypedW.2] at hjDiff
                exact Finset.mem_singleton.mp hjDiff
              rw [Finset.mem_singleton]
              apply Prod.ext
              · exact hτEq
              · rw [hDEq, hji]
        · exact False.elim (not_GiDoorVertex_of_room hRoom hBad.2.1)
      · intro hw
        rw [Finset.mem_singleton] at hw
        rw [hw]
        apply (mem_GiNeighbors).2
        exact Or.inl ⟨Or.inl hColorful, ⟨hDoor, hTypedDoor⟩, hDoorof⟩
    rw [GiDegree, hNeighbors]
    simp

/-- A graph has degree at most two at each vertex. -/
def simpleGraphDegreeAtMostTwo {α : Type*} [Fintype α] (G : SimpleGraph α) : Prop :=
  ∀ v, G.degree v ≤ 2

/-- A connected component is represented by a Mathlib graph path. -/
def simpleGraphPathComponent {α : Type*}
    (G : SimpleGraph α) (component : G.ConnectedComponent) : Prop :=
  ∃ (u v : α) (p : G.Walk u v),
    p.IsPath ∧ {x : α | x ∈ p.support} = component.supp

/-- A connected component is represented by a Mathlib graph cycle. -/
def simpleGraphCycleComponent {α : Type*}
    (G : SimpleGraph α) (component : G.ConnectedComponent) : Prop :=
  ∃ (u : α) (p : G.Walk u u),
    p.IsCycle ∧ {x : α | x ∈ p.support} = component.supp

/-- The literal "disjoint paths and cycles" component statement for a finite `SimpleGraph`. -/
def simpleGraphComponentsArePathsOrCycles {α : Type*}
    (G : SimpleGraph α) : Prop :=
  ∀ component : G.ConnectedComponent,
    simpleGraphPathComponent G component ∨ simpleGraphCycleComponent G component

/--
The degree characterization of `G_i`: every vertex has degree one or two, and
the degree-one vertices are exactly the unique outside door of type `i` and
the colorful rooms.
-/
def GiDegreeCharacterization (c : T → I) (i : I) : Prop :=
  (∀ v, GiVertex (IST := IST) c i v →
    GiDegree (IST := IST) c i v = 1 ∨ GiDegree (IST := IST) c i v = 2) ∧
  (∀ v, GiEndpoint (IST := IST) c i v ↔
    (GiDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
      IST.isColorful c v.1 v.2)

theorem GiDegreeCharacterization_holds (c : T → I) (i : I) :
    GiDegreeCharacterization (IST := IST) c i := by
  constructor
  · intro v hv
    rcases hv with hRoomVertex | hDoorVertex
    · rcases hRoomVertex with hColorful | hTypedRoom
      · exact Or.inl (GiDegree_colorfulRoom (IST := IST) (i := i) hColorful)
      · exact Or.inr (GiDegree_typedNCRoom (IST := IST) hTypedRoom.1 hTypedRoom.2)
    · by_cases hNonempty : v.1.Nonempty
      · exact Or.inr (GiDegree_internalDoor (IST := IST) ⟨hDoorVertex.1, hNonempty⟩ hDoorVertex.2)
      · have hOutside : IST.isOutsideDoor v.1 v.2 :=
          ⟨hDoorVertex.1, Finset.not_nonempty_iff_eq_empty.mp hNonempty⟩
        exact Or.inl (GiDegree_outsideDoor (IST := IST) hOutside hDoorVertex.2)
  · intro v
    constructor
    · intro hend
      rcases hend with ⟨hv, hDegreeOne⟩
      rcases hv with hRoomVertex | hDoorVertex
      · rcases hRoomVertex with hColorful | hTypedRoom
        · exact Or.inr hColorful
        · have hDegreeTwo := GiDegree_typedNCRoom (IST := IST) hTypedRoom.1 hTypedRoom.2
          rw [hDegreeOne] at hDegreeTwo; norm_num at hDegreeTwo
      · by_cases hNonempty : v.1.Nonempty
        · have hDegreeTwo := GiDegree_internalDoor (IST := IST) ⟨hDoorVertex.1,
          hNonempty⟩ hDoorVertex.2
          rw [hDegreeOne] at hDegreeTwo; norm_num at hDegreeTwo
        · have hOutside : IST.isOutsideDoor v.1 v.2 :=
            ⟨hDoorVertex.1, Finset.not_nonempty_iff_eq_empty.mp hNonempty⟩
          exact Or.inl ⟨hDoorVertex, hOutside⟩
    · intro hEndpointKind
      rcases hEndpointKind with hOutsideDoor | hColorful
      · exact ⟨Or.inr hOutsideDoor.1,
          GiDegree_outsideDoor (IST := IST) hOutsideDoor.2 hOutsideDoor.1.2⟩
      · exact ⟨Or.inl (Or.inl hColorful),
          GiDegree_colorfulRoom (IST := IST) (i := i) hColorful⟩

/--
The path-structure target for `G_i`: degree characterization plus the local
degree-at-most-two property used by path-following.
-/
def GiPathStructure (c : T → I) (i : I) : Prop :=
  GiDegreeCharacterization (IST := IST) c i ∧
    simpleGraphDegreeAtMostTwo (GiGraph (IST := IST) c i)

/--
The faithful component-level target for `G_i`: its connected components are
paths or cycles, and the endpoints of path components are exactly colorful
rooms except for the unique outside door of type `i`.
-/
def GiComponentStructure (c : T → I) (i : I) : Prop :=
  simpleGraphComponentsArePathsOrCycles (GiGraph (IST := IST) c i) ∧
    (∀ v, GiEndpoint (IST := IST) c i v ↔
      (GiDoorVertex (IST := IST) c i v ∧ IST.isOutsideDoor v.1 v.2) ∨
        IST.isColorful c v.1 v.2)

omit [Inhabited T] in
theorem GiPathStructure_of_degreeCharacterization {c : T → I} {i : I}
    (hdegStmt : GiDegreeCharacterization (IST := IST) c i) :
    GiPathStructure (IST := IST) c i := by
  refine ⟨hdegStmt, ?_⟩
  intro v
  rw [SimpleGraph.degree]
  change GiDegree (IST := IST) c i v ≤ 2
  by_cases hv : GiVertex (IST := IST) c i v
  · rcases hdegStmt.1 v hv with hOne | hTwo <;> omega
  · have hNoNeighbors : GiNeighbors (IST := IST) c i v = ∅ := by
      ext w
      simpa only [Finset.notMem_empty, iff_false]
        using fun hw => hv (GiEdge.left_vertex ((mem_GiNeighbors).1 hw))
    rw [GiDegree, hNoNeighbors]
    simp

omit [Inhabited T] in
theorem GiComponentStructure_of_components_are_paths_or_cycles {c : T → I} {i : I}
    (hdegStmt : GiDegreeCharacterization (IST := IST) c i)
    (hcomponents :
      simpleGraphComponentsArePathsOrCycles (GiGraph (IST := IST) c i)) :
    GiComponentStructure (IST := IST) c i :=
  ⟨hcomponents, hdegStmt.2⟩

/--
Generic graph-theoretic step 1: in a finite connected component of a graph of
degree at most two, choose a path whose support is maximal inside that
component.
-/
theorem exists_maximal_component_path_of_degree_le_two
    {α : Type*} [Fintype α] (G : SimpleGraph α)
    (_hdeg : simpleGraphDegreeAtMostTwo G) (component : G.ConnectedComponent) :
    ∃ (u v : α) (p : G.Walk u v),
      p.IsPath ∧
        {x : α | x ∈ p.support} ⊆ component.supp ∧
        ∀ (u' v' : α) (p' : G.Walk u' v'),
          p'.IsPath →
            {x : α | x ∈ p'.support} ⊆ component.supp →
              p'.length ≤ p.length := by
  classical
  let lengths : Set ℕ :=
    {n | ∃ (u v : α) (p : G.Walk u v),
      p.IsPath ∧ {x : α | x ∈ p.support} ⊆ component.supp ∧ p.length = n}
  have hfinite : lengths.Finite := by
    apply Set.Finite.subset (Set.finite_le_nat (Fintype.card α))
    intro n hn
    rcases hn with ⟨u, v, p, hp, _hsub, rfl⟩
    exact Nat.le_of_lt (SimpleGraph.Walk.IsPath.length_lt hp)
  obtain ⟨x, hxcomp⟩ := component.nonempty_supp
  have hnonempty : (0 : ℕ) ∈ lengths := by
    refine ⟨x, x, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, ?_, rfl⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_nil, List.mem_cons, List.not_mem_nil, or_false,
      Set.setOf_eq_eq_singleton, Set.mem_singleton_iff] at hy
    rw [hy]
    exact hxcomp
  obtain ⟨n, ⟨hn_mem, hn_max⟩⟩ := hfinite.exists_maximal ⟨0, hnonempty⟩
  rcases hn_mem with ⟨u, v, p, hp, hp_sub, hp_len⟩
  refine ⟨u, v, p, hp, hp_sub, ?_⟩
  intro u' v' p' hp' hp'_sub
  have hp'_len_mem : p'.length ∈ lengths :=
    ⟨u', v', p', hp', hp'_sub, rfl⟩
  have := hn_max hp'_len_mem
  omega

/--
Generic graph-theoretic step 2a: in a graph of degree at most two, a maximal
component path has no neighbor outside its support.  This is the point that
rules out T-shaped components.
-/
theorem maximal_component_path_no_escape_of_degree_le_two
    {α : Type*} [Fintype α] (G : SimpleGraph α)
    (hdeg : simpleGraphDegreeAtMostTwo G)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath)
    (hp_sub : {x : α | x ∈ p.support} ⊆ component.supp)
    (hmax :
      ∀ (u' v' : α) (p' : G.Walk u' v'),
        p'.IsPath →
          {x : α | x ∈ p'.support} ⊆ component.supp →
            p'.length ≤ p.length)
    {x y : α}
    (hx : x ∈ p.support)
    (hxy : G.Adj x y)
    (hycomp : y ∈ component.supp) :
    y ∈ p.support := by
  by_contra hyNot
  by_cases hxu : x = u
  · subst hxu
    let p' : G.Walk y v := SimpleGraph.Walk.cons hxy.symm p
    have hp' : p'.IsPath := (SimpleGraph.Walk.cons_isPath_iff hxy.symm p).2 ⟨hp, hyNot⟩
    have hp'_sub : {z : α | z ∈ p'.support} ⊆ component.supp := by
      intro z hz
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, Set.mem_setOf_eq, p'] at hz
      rcases hz with rfl | hz
      · exact hycomp
      · exact hp_sub hz
    have hle := hmax y v p' hp' hp'_sub
    simp [p'] at hle
  by_cases hxv : x = v
  · subst hxv
    let p' : G.Walk u y := p.concat hxy
    have hp' : p'.IsPath := (SimpleGraph.Walk.concat_isPath_iff hxy).2 ⟨hp, hyNot⟩
    have hp'_sub : {z : α | z ∈ p'.support} ⊆ component.supp := by
      intro z hz
      simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false, Set.mem_setOf_eq, p'] at hz
      rcases hz with hz | rfl
      · exact hp_sub hz
      · exact hycomp
    have hle := hmax u y p' hp' hp'_sub
    simp [p'] at hle
  obtain ⟨q, r, hqPath, hrPath,
    hqr⟩ := (SimpleGraph.Walk.IsPath.mem_support_iff_exists_append hp).1 hx
  have hqNonNil : ¬ q.Nil :=
    SimpleGraph.Walk.not_nil_of_ne (fun hux => hxu hux.symm)
  have hrNonNil : ¬ r.Nil := SimpleGraph.Walk.not_nil_of_ne hxv
  let a : α := q.penultimate
  let b : α := r.snd
  have haAdj : G.Adj x a := (q.adj_penultimate hqNonNil).symm
  have hbAdj : G.Adj x b := r.adj_snd hrNonNil
  have haQ : a ∈ q.support := q.getVert_mem_support (q.length - 1)
  have hbR : b ∈ r.support := r.getVert_mem_support 1
  have hpqr : (q.append r).IsPath := by rwa [← hqr]
  have hb_ne_x : b ≠ x := hbAdj.ne.symm
  have hab : a ≠ b :=
    SimpleGraph.Walk.IsPath.ne_of_mem_support_of_append hpqr hb_ne_x haQ hbR
  have haP : a ∈ p.support := by
    rw [hqr, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl haQ
  have hbP : b ∈ p.support := by
    rw [hqr, SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hbR
  have hay : a ≠ y := fun h => hyNot (h ▸ haP)
  have hby : b ≠ y := fun h => hyNot (h ▸ hbP)
  have hTripleSubset : ({a, b, y} : Finset α) ⊆ (G.neighborFinset x) := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl | rfl
    · exact haAdj
    · exact hbAdj
    · exact hxy
  have hTripleCard : ({a, b, y} : Finset α).card = 3 :=
    Finset.card_eq_three.2 ⟨a, b, y, hab, hay, hby, rfl⟩
  have hThreeLe : 3 ≤ G.degree x := by
    rw [SimpleGraph.degree, ← hTripleCard]
    exact Finset.card_le_card hTripleSubset
  have hTwo := hdeg x
  omega

/--
Generic graph-theoretic step 2b: if a component path has no edge escaping its
support inside the component, then its support is the whole component.
-/
theorem component_path_support_eq_component_of_no_escape
    {α : Type*} (G : SimpleGraph α)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp_sub : {x : α | x ∈ p.support} ⊆ component.supp)
    (hend :
      ∀ ⦃x y : α⦄,
        x ∈ p.support →
          G.Adj x y →
            y ∈ component.supp →
              y ∈ p.support) :
    {x : α | x ∈ p.support} = component.supp := by
  ext z
  constructor
  · intro hz
    exact hp_sub hz
  · intro hzcomp
    by_contra hzNot
    have huSupport : u ∈ p.support := p.start_mem_support
    have hucomp : u ∈ component.supp := hp_sub huSupport
    have hReach : G.Reachable u z := by
      apply SimpleGraph.ConnectedComponent.exact
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hucomp hzcomp
      exact hucomp.trans hzcomp.symm
    rcases hReach with ⟨q⟩
    obtain ⟨d, hdq, hdfst, hdsnd⟩ :=
      q.exists_boundary_dart {x : α | x ∈ p.support} huSupport hzNot
    have hdfstComp : d.fst ∈ component.supp := hp_sub hdfst
    have hdsndComp : d.snd ∈ component.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_congr_adj component d.adj).1 hdfstComp
    exact hdsnd (hend hdfst d.adj hdsndComp)

/- Generic graph-theoretic step 3: if a maximal component path in a degree-at-most
two graph has a closing edge not already used by the path, then the component
is a cycle.  The extra edge condition excludes the two-vertex path case. -/
theorem component_cycle_of_maximal_path_closes
    {α : Type*} (G : SimpleGraph α)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath)
    (hsupp : {x : α | x ∈ p.support} = component.supp)
    (hclose : G.Adj v u)
    (hnew : s(v, u) ∉ p.edges) :
    simpleGraphCycleComponent G component := by
  refine ⟨v, SimpleGraph.Walk.cons hclose p, ?_, ?_⟩
  · exact (SimpleGraph.Walk.cons_isCycle_iff p hclose).2 ⟨hp, hnew⟩
  · rw [← hsupp]
    ext x
    constructor
    · intro hx
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, Set.mem_setOf_eq] at hx
      rcases hx with rfl | hx
      · exact p.end_mem_support
      · exact hx
    · intro hx
      simpa only [SimpleGraph.Walk.support_cons, List.mem_cons, Set.mem_setOf_eq] using Or.inr hx

/-- A path whose support is exactly a component represents that component as a path. -/
theorem component_path_of_support_eq_component
    {α : Type*} (G : SimpleGraph α)
    {component : G.ConnectedComponent} {u v : α} {p : G.Walk u v}
    (hp : p.IsPath)
    (hsupp : {x : α | x ∈ p.support} = component.supp) :
    simpleGraphPathComponent G component :=
  ⟨u, v, p, hp, hsupp⟩

/--
Generic graph-theoretic theorem: every connected component of a finite graph
whose vertices all have degree at most two is represented by either a path or
a cycle.
-/
theorem simpleGraph_components_path_or_cycle_of_degree_le_two
    {α : Type*} [Fintype α] (G : SimpleGraph α)
    (hdeg : simpleGraphDegreeAtMostTwo G) :
    simpleGraphComponentsArePathsOrCycles G := by
  intro component
  obtain ⟨u, v, p, hp, hp_sub, hmax⟩ :=
    exists_maximal_component_path_of_degree_le_two G hdeg component
  have hNoEscape :
      ∀ ⦃x y : α⦄, x ∈ p.support → G.Adj x y → y ∈ component.supp → y ∈ p.support :=
    fun x y hx hxy hycomp =>
      maximal_component_path_no_escape_of_degree_le_two G hdeg hp hp_sub hmax hx hxy hycomp
  have hsupp : {x : α | x ∈ p.support} = component.supp :=
    component_path_support_eq_component_of_no_escape G hp_sub hNoEscape
  by_cases hcycle : G.Adj v u ∧ s(v, u) ∉ p.edges
  · exact Or.inr (component_cycle_of_maximal_path_closes G hp hsupp hcycle.1 hcycle.2)
  · exact Or.inl (component_path_of_support_eq_component G hp hsupp)

/--
Final graph structure statement for `G_i`: its components are paths or cycles,
and its endpoints are exactly the outside door of type `i` and the colorful
rooms.
-/
theorem GiComponentStructure_holds (c : T → I) (i : I) :
    GiComponentStructure (IST := IST) c i :=
  GiComponentStructure_of_components_are_paths_or_cycles
    (IST := IST)
    (GiDegreeCharacterization_holds (IST := IST) c i)
    (simpleGraph_components_path_or_cycle_of_degree_le_two
      (GiGraph (IST := IST) c i)
      (GiPathStructure_of_degreeCharacterization
        (IST := IST) (GiDegreeCharacterization_holds (IST := IST) c i)).2)

end IndexedLOrder

end
