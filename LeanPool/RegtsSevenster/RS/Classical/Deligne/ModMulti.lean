/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModTensor

/-!
# The multi-tensor of internal modules over a monoid object

The replacement for associativity of the binary module tensor
product of `ModTensor.lean`: for a list `Xs` of left modules over a
monoid object `A` in a braided monoidal category, the multi-tensor
`X₁ ⊗_A ⋯ ⊗_A Xₙ` is presented in one step, as the coequalizer of a
single wide relation pair

    `⊕ₛ mid s ⇉ X₁ ⊗ (X₂ ⊗ (⋯ ⊗ Xₙ))`

whose source is the finite biproduct, over the adjacent slots `s` of
the list, of the relation objects obtained by inserting `A` between
the two factors of the slot, and whose legs act on the slot through
the braided right action and the left action respectively — the two
legs of `ModTensor.lean` at the slot's window, in every adjacent
slot at once.

* `modList A Xs`: the plain tensor fold of the underlying objects,
  with the monoidal unit as seed; `modListCast` transports it along
  equalities of lists.
* `ModSlot Xs`: an adjacent slot, recorded as a decomposition
  `Xs = pre ++ M :: N :: post`; `modSlots Xs` enumerates the slots
  and `mem_modSlots` shows the enumeration is complete.
* `modMulti A Xs`, `modMultiπ`, `modMulti_rel`, `modMultiDesc`,
  `modMultiπ_desc`, `modMulti_hom_ext`: the multi-tensor and its
  universal property, with the slot relations quantified over
  decompositions.
* `modMultiNil`/`modMultiSingle`: with this presentation the empty
  multi-tensor is the monoidal unit of the ambient category (not
  the regular module `A`, which is the unit of `Mod A` — consumers
  wanting that convention should treat the empty list separately),
  and the singleton multi-tensor is the module itself.
* `modMultiPair`: the two-element multi-tensor agrees with the
  binary `modTensor`, compatibly with the projections.
* `modMultiWhiskerRDesc`/`modMultiWhiskerLDesc`: descent along the
  whiskered projections, with the whiskered relation condition
  reduced to the slots through the biproduct distributors.
* `modMultiConcatFst`, `modMultiConcat`: the concatenation map
  `modMulti A Xs ⊗ modMulti A Ys ⟶ modMulti A (Xs ++ Ys)`, by a
  two-stage descent through the whiskered coequalizers, with the
  defining equation `tensorHom_modMultiπ_concat` against the
  projections and the fold concatenation `modListConcat`.
* `modMultiHeadAct`, `modMultiMod`: for a commutative monoid the
  action on the head factor descends, making the multi-tensor of a
  non-empty list a module; the empty multi-tensor is the monoidal
  unit and carries no canonical `A`-action.

The further descent of `modMultiConcat` through the middle
`A`-action — the comparison with `modTensor` of two multi-tensors —
is outside this module's scope; its substrate (the head modules,
the concatenation map, and the slot relations) is complete.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The underlying tensor fold -/

section ModList

/-- The tensor fold of the underlying objects of a list of modules,
folded to the right with the monoidal unit as seed. -/
def modList [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] :
    List (Mod D A) → D
  | [] => 𝟙_ D
  | M :: l => M.X ⊗ modList A l

@[simp] lemma modList_nil
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] :
    modList A ([] : List (Mod D A)) = 𝟙_ D :=
  rfl

@[simp] lemma modList_cons
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M : Mod D A) (l : List (Mod D A)) :
    modList A (M :: l) = M.X ⊗ modList A l :=
  rfl

/-- Transport of the tensor fold along an equality of lists.  It is
an `eqToHom`, so it composes and cancels by `eqToHom` simp lemmas. -/
def modListCast [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {l₁ l₂ : List (Mod D A)} (h : l₁ = l₂) :
    modList A l₁ ⟶ modList A l₂ :=
  eqToHom (congrArg (modList A) h)

@[simp] lemma modListCast_rfl
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (l : List (Mod D A)) :
    modListCast A (rfl : l = l) = 𝟙 _ :=
  rfl

@[reassoc (attr := simp)]
lemma modListCast_comp [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {l₁ l₂ l₃ : List (Mod D A)} (h : l₁ = l₂)
    (h' : l₂ = l₃) :
    modListCast A h ≫ modListCast A h' = modListCast A (h.trans h') := by
  simp [modListCast]

/-- Whiskering a list transport is a list transport. -/
lemma modListCast_whiskerLeft
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M : Mod D A) {l₁ l₂ : List (Mod D A)}
    (h : l₁ = l₂) :
    M.X ◁ modListCast A h =
      modListCast A (congrArg (M :: ·) h) := by
  subst h
  simp only [modListCast_rfl, MonoidalCategory.whiskerLeft_id]
  rfl

end ModList

/-! ## The slot relations

A slot of the list is a decomposition `Xs = pre ++ M :: N :: post`.
Its relation object inserts `A` between the two factors of the
slot, nested exactly as the ambient fold, so that the legs below
are typed at the fold on the nose, with no transport. -/

section Slots

/-- The relation object of a slot: the ambient fold with the monoid
inserted between the two factors of the slot. -/
def modMultiMid [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] :
    List (Mod D A) → Mod D A → Mod D A →
    List (Mod D A) → D
  | [], M, N, post => ((M.X ⊗ A) ⊗ N.X) ⊗ modList A post
  | P :: rest, M, N, post => P.X ⊗ modMultiMid A rest M N post

@[simp] lemma modMultiMid_nil
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M N : Mod D A) (post : List (Mod D A)) :
    modMultiMid A [] M N post = ((M.X ⊗ A) ⊗ N.X) ⊗ modList A post :=
  rfl

@[simp] lemma modMultiMid_cons
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (P : Mod D A) (pre : List (Mod D A))
    (M N : Mod D A) (post : List (Mod D A)) :
    modMultiMid A (P :: pre) M N post =
      P.X ⊗ modMultiMid A pre M N post :=
  rfl

/-- Assemble a window morphism on `(M.X ⊗ A) ⊗ N.X` into a relation
leg over a prefix: resolve the window, reassociate the second factor
onto the suffix, and whisker through the prefix. -/
def modMultiLegOf [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M N : Mod D A) (post : List (Mod D A))
    (w : (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X) :
    (pre : List (Mod D A)) →
      modMultiMid A pre M N post ⟶ modList A (pre ++ M :: N :: post)
  | [] => (w ▷ modList A post) ≫ (α_ M.X N.X (modList A post)).hom
  | P :: rest => P.X ◁ modMultiLegOf A M N post w rest

@[simp] lemma modMultiLegOf_nil
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M N : Mod D A) (post : List (Mod D A))
    (w : (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X) :
    modMultiLegOf A M N post w [] =
      (w ▷ modList A post) ≫ (α_ M.X N.X (modList A post)).hom :=
  rfl

@[simp] lemma modMultiLegOf_cons
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M N : Mod D A)
    (post : List (Mod D A)) (w : (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X)
    (P : Mod D A) (pre : List (Mod D A)) :
    modMultiLegOf A M N post w (P :: pre) =
      P.X ◁ modMultiLegOf A M N post w pre :=
  rfl

/-- The first relation leg at a slot: act on the left factor of the
window through the braided right action. -/
def modMultiLegM [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D]
    (pre : List (Mod D A)) (M N : Mod D A)
    (post : List (Mod D A)) :
    modMultiMid A pre M N post ⟶ modList A (pre ++ M :: N :: post) :=
  modMultiLegOf A M N post (modTensorLegM A M N) pre

/-- The second relation leg at a slot: associate and act on the
right factor of the window. -/
def modMultiLegN [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (pre : List (Mod D A)) (M N : Mod D A)
    (post : List (Mod D A)) :
    modMultiMid A pre M N post ⟶ modList A (pre ++ M :: N :: post) :=
  modMultiLegOf A M N post (modTensorLegN A M N) pre

end Slots

/-! ## Enumeration of the slots -/

section SlotList

/-- An adjacent slot of a list of modules: a decomposition into a
prefix, two adjacent factors, and a suffix. -/
structure ModSlot
    [Category.{v} D] [MonoidalCategory D]
    {A : D} [MonObj A] (Xs : List (Mod D A)) where
  /-- The factors below the slot. -/
  pre : List (Mod D A)
  /-- The first factor of the slot. -/
  fst : Mod D A
  /-- The second factor of the slot. -/
  snd : Mod D A
  /-- The factors above the slot. -/
  post : List (Mod D A)
  /-- The decomposition of the ambient list. -/
  eq : Xs = pre ++ fst :: snd :: post

variable {A} in
/-- Extend a slot by one factor below. -/
def ModSlot.consSlot [Category.{v} D] [MonoidalCategory D] {A : D} [MonObj A]
    (P : Mod D A) {Xs : List (Mod D A)}
    (s : ModSlot Xs) : ModSlot (P :: Xs) :=
  ⟨P :: s.pre, s.fst, s.snd, s.post, congrArg (List.cons P) s.eq⟩

/-- The list of all adjacent slots of a list of modules. -/
def modSlots [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] :
    (Xs : List (Mod D A)) → List (ModSlot Xs)
  | [] => []
  | [_] => []
  | M :: N :: post =>
    ⟨[], M, N, post, rfl⟩ ::
      (modSlots A (N :: post)).map (ModSlot.consSlot M)

@[simp] lemma modSlots_nil
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] :
    modSlots A ([] : List (Mod D A)) = [] :=
  rfl

@[simp] lemma modSlots_singleton
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M : Mod D A) :
    modSlots A [M] = [] :=
  rfl

variable {A} in
/-- Extension by a factor preserves membership in the slot list. -/
lemma ModSlot.consSlot_mem
    [Category.{v} D] [MonoidalCategory D] {A : D} [MonObj A]
    (P : Mod D A) :
    ∀ {Ys : List (Mod D A)} (s : ModSlot Ys),
      s ∈ modSlots A Ys → s.consSlot P ∈ modSlots A (P :: Ys)
  | [], s, _ => absurd s.eq (by simp)
  | _ :: _, _, hs =>
    List.mem_cons_of_mem _ (List.mem_map_of_mem hs)

variable {A} in
/-- **The slot enumeration is complete**: every decomposition of the
list occurs among its slots. -/
lemma mem_modSlots [Category.{v} D] [MonoidalCategory D] {A : D} [MonObj A]
    {Xs : List (Mod D A)} (s : ModSlot Xs) :
    s ∈ modSlots A Xs := by
  obtain ⟨pre, M, N, post, rfl⟩ := s
  induction pre with
  | nil => exact List.mem_cons_self
  | cons P pre ih => exact ModSlot.consSlot_mem P _ ih

end SlotList

/-! ## The relation pair of the multi-tensor -/

section ModMultiDefs

variable {A} in
/-- The relation object of a slot, in slot form. -/
abbrev ModSlot.mid [Category.{v} D] [MonoidalCategory D] {A : D} [MonObj A]
    {Xs : List (Mod D A)} (s : ModSlot Xs) : D :=
  modMultiMid A s.pre s.fst s.snd s.post

variable {A} in
/-- The first relation leg of a slot, transported to the ambient
list. -/
def ModSlot.legM [Category.{v} D] [MonoidalCategory D] {A : D} [MonObj A]
    [BraidedCategory D]
    {Xs : List (Mod D A)} (s : ModSlot Xs) :
    s.mid ⟶ modList A Xs :=
  modMultiLegM A s.pre s.fst s.snd s.post ≫ modListCast A s.eq.symm

variable {A} in
/-- The second relation leg of a slot, transported to the ambient
list. -/
def ModSlot.legN [Category.{v} D] [MonoidalCategory D] {A : D} [MonObj A]
    {Xs : List (Mod D A)} (s : ModSlot Xs) :
    s.mid ⟶ modList A Xs :=
  modMultiLegN A s.pre s.fst s.snd s.post ≫ modListCast A s.eq.symm

/-- The source of the relation pair: the biproduct of the relation
objects over all adjacent slots.  An abbreviation, so that the
biproduct API applies to the legs without unfolding. -/
noncomputable abbrev modMultiSrc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] [Preadditive D]
    [HasFiniteBiproducts D]
    (Xs : List (Mod D A)) : D :=
  ⨁ fun i : Fin (modSlots A Xs).length => (modSlots A Xs)[i.1].mid

/-- The first leg of the relation pair, assembled over all slots. -/
noncomputable def modMultiLegFst
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    (Xs : List (Mod D A)) :
    modMultiSrc A Xs ⟶ modList A Xs :=
  biproduct.desc fun i => (modSlots A Xs)[i.1].legM

/-- The second leg of the relation pair, assembled over all slots. -/
noncomputable def modMultiLegSnd
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] [Preadditive D]
    [HasFiniteBiproducts D]
    (Xs : List (Mod D A)) :
    modMultiSrc A Xs ⟶ modList A Xs :=
  biproduct.desc fun i => (modSlots A Xs)[i.1].legN

end ModMultiDefs

/-! ## The multi-tensor and its universal property -/

section ModMulti

/-- **The multi-tensor of a list of modules** over `A`: the
coequalizer of the wide relation pair, identifying
`(x·c) ⊗ y ~ x ⊗ (c·y)` in every adjacent slot simultaneously.  No
binary module tensor product and no associativity enter. -/
noncomputable def modMulti
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (Xs : List (Mod D A)) : D :=
  coequalizer (modMultiLegFst A Xs) (modMultiLegSnd A Xs)

/-- The projection of the ambient fold onto the multi-tensor. -/
noncomputable def modMultiπ
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (Xs : List (Mod D A)) :
    modList A Xs ⟶ modMulti A Xs :=
  coequalizer.π _ _

instance [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (Xs : List (Mod D A)) : Epi (modMultiπ A Xs) :=
  inferInstanceAs (Epi (coequalizer.π _ _))

/-- The two assembled legs agree after the projection. -/
@[reassoc]
lemma modMulti_condition
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (Xs : List (Mod D A)) :
    modMultiLegFst A Xs ≫ modMultiπ A Xs =
      modMultiLegSnd A Xs ≫ modMultiπ A Xs :=
  coequalizer.condition _ _

/-- **The slot relation in the multi-tensor**: at every
decomposition `Xs = pre ++ M :: N :: post` the two slot legs agree
after the projection. -/
@[reassoc]
lemma modMulti_rel [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {Xs : List (Mod D A)} (pre : List (Mod D A))
    (M N : Mod D A) (post : List (Mod D A))
    (h : Xs = pre ++ M :: N :: post) :
    modMultiLegM A pre M N post ≫ modListCast A h.symm ≫
        modMultiπ A Xs =
      modMultiLegN A pre M N post ≫ modListCast A h.symm ≫
        modMultiπ A Xs := by
  have hmem : (⟨pre, M, N, post, h⟩ : ModSlot Xs) ∈ modSlots A Xs :=
    mem_modSlots _
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hmem
  have h2 : biproduct.ι
        (fun j : Fin (modSlots A Xs).length => (modSlots A Xs)[j.1].mid)
        ⟨i, hi⟩ ≫ modMultiLegFst A Xs ≫ modMultiπ A Xs =
      biproduct.ι
        (fun j : Fin (modSlots A Xs).length => (modSlots A Xs)[j.1].mid)
        ⟨i, hi⟩ ≫ modMultiLegSnd A Xs ≫ modMultiπ A Xs := by
    rw [modMulti_condition]
  simp only [modMultiLegFst, modMultiLegSnd, biproduct.ι_desc_assoc]
    at h2
  rw [hget] at h2
  simpa [ModSlot.legM, ModSlot.legN] using h2

/-- Morphisms out of the multi-tensor are determined by their
composite with the projection. -/
lemma modMulti_hom_ext [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {Xs : List (Mod D A)} {W : D}
    {k l : modMulti A Xs ⟶ W}
    (h : modMultiπ A Xs ≫ k = modMultiπ A Xs ≫ l) : k = l :=
  coequalizer.hom_ext h

/-- Descend a morphism that coequalizes every slot relation to the
multi-tensor. -/
noncomputable def modMultiDesc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {Xs : List (Mod D A)} {W : D}
    (k : modList A Xs ⟶ W)
    (h : ∀ (pre : List (Mod D A)) (M N : Mod D A)
      (post : List (Mod D A)) (hd : Xs = pre ++ M :: N :: post),
      modMultiLegM A pre M N post ≫ modListCast A hd.symm ≫ k =
        modMultiLegN A pre M N post ≫ modListCast A hd.symm ≫ k) :
    modMulti A Xs ⟶ W :=
  coequalizer.desc k (by
    apply biproduct.hom_ext'
    intro i
    simp only [modMultiLegFst, modMultiLegSnd, biproduct.ι_desc_assoc]
    have hs := h (modSlots A Xs)[i.1].pre (modSlots A Xs)[i.1].fst
      (modSlots A Xs)[i.1].snd (modSlots A Xs)[i.1].post
      (modSlots A Xs)[i.1].eq
    simpa [ModSlot.legM, ModSlot.legN] using hs)

/-- The descent factors the given morphism through the
projection. -/
@[reassoc (attr := simp)]
lemma modMultiπ_desc [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {Xs : List (Mod D A)} {W : D}
    (k : modList A Xs ⟶ W)
    (h : ∀ (pre : List (Mod D A)) (M N : Mod D A)
      (post : List (Mod D A)) (hd : Xs = pre ++ M :: N :: post),
      modMultiLegM A pre M N post ≫ modListCast A hd.symm ≫ k =
        modMultiLegN A pre M N post ≫ modListCast A hd.symm ≫ k) :
    modMultiπ A Xs ≫ modMultiDesc A k h = k :=
  coequalizer.π_desc _ _

/-! ### The empty and singleton multi-tensors

Below two factors there are no adjacent slots: the relation source
is the empty biproduct, the legs agree, and the projection is an
isomorphism. -/

/-- On a slot-free list the projection is an isomorphism. -/
noncomputable def modMultiTriv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    {Xs : List (Mod D A)}
    (h : modSlots A Xs = []) : modMulti A Xs ≅ modList A Xs where
  hom := modMultiDesc A (𝟙 _) (fun pre M N post hd =>
    absurd (mem_modSlots ⟨pre, M, N, post, hd⟩) (by simp [h]))
  inv := modMultiπ A Xs
  hom_inv_id := modMulti_hom_ext A (by
    rw [modMultiπ_desc_assoc, Category.id_comp, Category.comp_id])
  inv_hom_id := modMultiπ_desc A _ _

/-- **The empty multi-tensor is the monoidal unit** of the ambient
category.  With this presentation the empty fold is `𝟙_ D`, not the
regular module: consumers wanting `A` as the empty product — the
unit of the module category — should treat the empty list as a
separate case. -/
noncomputable def modMultiNil
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] : modMulti A ([] : List (Mod D A)) ≅ 𝟙_ D :=
  modMultiTriv A (modSlots_nil A)

/-- **The singleton multi-tensor is the module.** -/
noncomputable def modMultiSingle
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    (X : Mod D A) :
    modMulti A [X] ≅ X.X :=
  modMultiTriv A (modSlots_singleton A X) ≪≫ ρ_ X.X

end ModMulti

/-! ## Comparison with the binary module tensor product

For a two-element list the wide relation pair has a single slot,
whose window legs are exactly the parallel pair of `ModTensor.lean`;
the two coequalizer presentations agree, up to the right unitor
absorbing the unit seed of the fold. -/

section Pair

/-- The only slot of a two-element list is the full decomposition. -/
lemma pair_decomp [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    {X Y M N : Mod D A} {pre post : List (Mod D A)}
    (h : [X, Y] = pre ++ M :: N :: post) :
    pre = [] ∧ X = M ∧ Y = N ∧ post = [] := by
  rcases pre with _ | ⟨P, pre⟩
  · injection h with h1 h
    injection h with h2 h3
    exact ⟨rfl, h1, h2, h3.symm⟩
  · rcases pre with _ | ⟨Q, pre⟩ <;> simp at h

/-- The resolution of the two-element fold onto the plain tensor
product: absorb the unit seed.  A bridge morphism with a
`modList`-typed source, so that statements through it stay
type-correct at low transparency. -/
def pairResolve
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) : modList A [X, Y] ⟶ X.X ⊗ Y.X :=
  X.X ◁ (ρ_ Y.X).hom

/-- The inverse resolution: reinstate the unit seed. -/
def pairResolveInv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) : X.X ⊗ Y.X ⟶ modList A [X, Y] :=
  X.X ◁ (ρ_ Y.X).inv

@[reassoc (attr := simp)]
lemma pairResolve_inv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) :
    pairResolve A X Y ≫ pairResolveInv A X Y = 𝟙 _ := by
  show (X.X ◁ (ρ_ Y.X).hom) ≫ (X.X ◁ (ρ_ Y.X).inv) =
    𝟙 (X.X ⊗ (Y.X ⊗ 𝟙_ D))
  rw [← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
    MonoidalCategory.whiskerLeft_id]

@[reassoc (attr := simp)]
lemma pairResolveInv_resolve
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) :
    pairResolveInv A X Y ≫ pairResolve A X Y = 𝟙 _ := by
  show (X.X ◁ (ρ_ Y.X).inv) ≫ (X.X ◁ (ρ_ Y.X).hom) =
    𝟙 (X.X ⊗ Y.X)
  rw [← MonoidalCategory.whiskerLeft_comp, Iso.inv_hom_id,
    MonoidalCategory.whiskerLeft_id]

/-- The window seed of the pair: the right unitor of the single
relation object, retyped at `modMultiMid`. -/
def pairSeed
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) : modMultiMid A [] X Y [] ⟶ (X.X ⊗ A) ⊗ Y.X :=
  (ρ_ ((X.X ⊗ A) ⊗ Y.X)).hom

/-- The inverse window seed of the pair. -/
def pairSeedInv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A) : (X.X ⊗ A) ⊗ Y.X ⟶ modMultiMid A [] X Y [] :=
  (ρ_ ((X.X ⊗ A) ⊗ Y.X)).inv

/-- The single relation leg of the pair against the resolution: the
unit seed is absorbed and the window morphism remains. -/
@[reassoc]
lemma modMultiLeg_pair_resolve
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A)
    (w : (X.X ⊗ A) ⊗ Y.X ⟶ X.X ⊗ Y.X)
    (h : ([] ++ X :: Y :: [] : List (Mod D A)) = [X, Y]) :
    modMultiLegOf A X Y [] w [] ≫ modListCast A h ≫
        pairResolve A X Y =
      pairSeed A X Y ≫ w := by
  have hcoh : (α_ X.X Y.X (𝟙_ D)).hom ≫ (X.X ◁ (ρ_ Y.X).hom) =
      (ρ_ (X.X ⊗ Y.X)).hom := by monoidal
  show ((w ▷ 𝟙_ D) ≫ (α_ X.X Y.X (𝟙_ D)).hom) ≫
      𝟙 (X.X ⊗ (Y.X ⊗ 𝟙_ D)) ≫ (X.X ◁ (ρ_ Y.X).hom) =
    (ρ_ ((X.X ⊗ A) ⊗ Y.X)).hom ≫ w
  rw [Category.id_comp, Category.assoc, hcoh, rightUnitor_naturality]

/-- A window morphism against the inverse resolution, in leg
form. -/
@[reassoc]
lemma modMultiLeg_pair_resolveInv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] (X : Mod D A)
    (Y : Mod D A)
    (w : (X.X ⊗ A) ⊗ Y.X ⟶ X.X ⊗ Y.X)
    (h : ([] ++ X :: Y :: [] : List (Mod D A)) = [X, Y]) :
    w ≫ pairResolveInv A X Y =
      pairSeedInv A X Y ≫ modMultiLegOf A X Y [] w [] ≫
        modListCast A h := by
  have hcoh : (ρ_ (X.X ⊗ Y.X)).inv ≫ (α_ X.X Y.X (𝟙_ D)).hom =
      X.X ◁ (ρ_ Y.X).inv := by monoidal
  show w ≫ (X.X ◁ (ρ_ Y.X).inv) =
    (ρ_ ((X.X ⊗ A) ⊗ Y.X)).inv ≫
      ((w ▷ 𝟙_ D) ≫ (α_ X.X Y.X (𝟙_ D)).hom) ≫
        𝟙 (X.X ⊗ (Y.X ⊗ 𝟙_ D))
  rw [Category.comp_id, ← rightUnitor_inv_naturality_assoc, hcoh]

end Pair

section PairIso

/-- Comparison with the binary tensor product: the forward
direction, descending the binary projection. -/
noncomputable def modMultiPairHom
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] (X : Mod D A) (Y : Mod D A) :
    modMulti A [X, Y] ⟶ modTensor A X Y :=
  modMultiDesc A (pairResolve A X Y ≫ modTensorπ A X Y)
    (by
      intro pre M N post hd
      obtain ⟨rfl, h2, h3, rfl⟩ := pair_decomp A hd
      subst h2
      subst h3
      rw [modMultiLegM, modMultiLegN,
        modMultiLeg_pair_resolve_assoc A X Y _ hd.symm,
        modMultiLeg_pair_resolve_assoc A X Y _ hd.symm,
        modTensor_condition])

/-- Defining equation of the forward comparison. -/
@[reassoc (attr := simp)]
lemma modMultiπ_pairMod [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] (X : Mod D A) (Y : Mod D A) :
    modMultiπ A [X, Y] ≫ modMultiPairHom A X Y =
      pairResolve A X Y ≫ modTensorπ A X Y :=
  modMultiπ_desc A _ _

/-- Comparison with the binary tensor product: the backward
direction, descending the wide projection. -/
noncomputable def modMultiPairInv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] (X : Mod D A) (Y : Mod D A) :
    modTensor A X Y ⟶ modMulti A [X, Y] :=
  modTensorDesc A X Y (pairResolveInv A X Y ≫ modMultiπ A [X, Y])
    (by
      have hrel := modMulti_rel A [] X Y []
        (rfl : [X, Y] = [] ++ X :: Y :: [])
      rw [modMultiLegM, modMultiLegN] at hrel
      rw [modMultiLeg_pair_resolveInv_assoc A X Y _
          (Eq.symm (rfl : [X, Y] = [] ++ X :: Y :: [])),
        modMultiLeg_pair_resolveInv_assoc A X Y _
          (Eq.symm (rfl : [X, Y] = [] ++ X :: Y :: [])),
        hrel])

/-- Defining equation of the backward comparison. -/
@[reassoc (attr := simp)]
lemma modTensorπ_pairInv
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] (X : Mod D A) (Y : Mod D A) :
    modTensorπ A X Y ≫ modMultiPairInv A X Y =
      pairResolveInv A X Y ≫ modMultiπ A [X, Y] :=
  modTensorπ_desc A X Y _ _

/-- **The two-element multi-tensor is the binary module tensor
product**: the one-slot wide presentation and the parallel-pair
presentation coequalize the same relations. -/
noncomputable def modMultiPair
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D] (X : Mod D A) (Y : Mod D A) :
    modMulti A [X, Y] ≅ modTensor A X Y where
  hom := modMultiPairHom A X Y
  inv := modMultiPairInv A X Y
  hom_inv_id := by
    apply modMulti_hom_ext
    rw [modMultiπ_pairMod_assoc, modTensorπ_pairInv,
      pairResolve_inv_assoc, Category.comp_id]
  inv_hom_id := by
    apply modTensor_hom_ext
    rw [modTensorπ_pairInv_assoc, modMultiπ_pairMod,
      pairResolveInv_resolve_assoc, Category.comp_id]

end PairIso

/-! ## Concatenation of folds

The fold of a concatenated list against the tensor product of the
two folds, with the bridges that carry a relation slot of one block
into the concatenated list.  Casts are quantified, as in the slot
relations, so consumers never meet a transported proof they cannot
name. -/

section Concat

/-- Concatenation of tensor folds: the two-block fold reassociates
onto the fold of the concatenated list. -/
def modListConcat [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A] :
    (Xs Ys : List (Mod D A)) →
    (modList A Xs ⊗ modList A Ys ≅ modList A (Xs ++ Ys))
  | [], Ys => λ_ (modList A Ys)
  | P :: Xs, Ys =>
    α_ P.X (modList A Xs) (modList A Ys) ≪≫
      whiskerLeftIso P.X (modListConcat A Xs Ys)

/-- A morphism whiskered under a cons prefix passes the
concatenation: the step case of every prefix induction below. -/
lemma modListConcat_cons_whisker
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (P : Mod D A) {S : D}
    {T Ys : List (Mod D A)} (u : S ⟶ modList A T) :
    ((P.X ◁ u) ▷ modList A Ys) ≫ (modListConcat A (P :: T) Ys).hom =
      (α_ P.X S (modList A Ys)).hom ≫
        (P.X ◁ ((u ▷ modList A Ys) ≫ (modListConcat A T Ys).hom)) := by
  show ((P.X ◁ u) ▷ modList A Ys) ≫
      ((α_ P.X (modList A T) (modList A Ys)).hom ≫
        (P.X ◁ (modListConcat A T Ys).hom)) =
    (α_ P.X S (modList A Ys)).hom ≫
      (P.X ◁ ((u ▷ modList A Ys) ≫ (modListConcat A T Ys).hom))
  rw [MonoidalCategory.whiskerLeft_comp,
    associator_naturality_middle_assoc]

/-- A morphism whiskered on the right of a cons prefix passes the
concatenation. -/
lemma modListConcat_whiskerLeft_cons
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (P : Mod D A)
    (Xs : List (Mod D A)) {S : D} {T : List (Mod D A)}
    (u : S ⟶ modList A T) :
    (modList A (P :: Xs) ◁ u) ≫ (modListConcat A (P :: Xs) T).hom =
      (α_ P.X (modList A Xs) S).hom ≫
        (P.X ◁ ((modList A Xs ◁ u) ≫
          (modListConcat A Xs T).hom)) := by
  show ((P.X ⊗ modList A Xs) ◁ u) ≫
      ((α_ P.X (modList A Xs) (modList A T)).hom ≫
        (P.X ◁ (modListConcat A Xs T).hom)) =
    (α_ P.X (modList A Xs) S).hom ≫
      (P.X ◁ ((modList A Xs ◁ u) ≫ (modListConcat A Xs T).hom))
  rw [MonoidalCategory.whiskerLeft_comp,
    associator_naturality_right_assoc]

/-- A transport in the second block passes the concatenation. -/
@[reassoc]
lemma modListConcat_cast_right
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (Xs : List (Mod D A))
    {l₁ l₂ : List (Mod D A)} (h : l₁ = l₂) :
    (modList A Xs ◁ modListCast A h) ≫
        (modListConcat A Xs l₂).hom =
      (modListConcat A Xs l₁).hom ≫
        modListCast A (congrArg (Xs ++ ·) h) := by
  subst h
  simp

/-- The relation object of a slot, concatenated on the right: the
suffix grows by the second block. -/
def modMultiMidConcat [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M N : Mod D A) (post Ys : List (Mod D A)) :
    (pre : List (Mod D A)) →
      (modMultiMid A pre M N post ⊗ modList A Ys ⟶
        modMultiMid A pre M N (post ++ Ys))
  | [] =>
    (α_ ((M.X ⊗ A) ⊗ N.X) (modList A post) (modList A Ys)).hom ≫
      (((M.X ⊗ A) ⊗ N.X) ◁ (modListConcat A post Ys).hom)
  | P :: rest =>
    (α_ P.X (modMultiMid A rest M N post) (modList A Ys)).hom ≫
      (P.X ◁ modMultiMidConcat A M N post Ys rest)

/-- The base of the right leg-concatenation: the window against the
concatenation, by the pentagon. -/
lemma modMultiLegOf_concat_nil
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M N : Mod D A)
    (post Ys : List (Mod D A))
    (w : (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X) :
    (modMultiLegOf A M N post w [] ▷ modList A Ys) ≫
        (modListConcat A (M :: N :: post) Ys).hom =
      modMultiMidConcat A M N post Ys [] ≫
        modMultiLegOf A M N (post ++ Ys) w [] := by
  show (((w ▷ modList A post) ≫
        (α_ M.X N.X (modList A post)).hom) ▷ modList A Ys) ≫
      ((α_ M.X (N.X ⊗ modList A post) (modList A Ys)).hom ≫
        (M.X ◁ ((α_ N.X (modList A post) (modList A Ys)).hom ≫
          (N.X ◁ (modListConcat A post Ys).hom)))) =
    ((α_ ((M.X ⊗ A) ⊗ N.X) (modList A post) (modList A Ys)).hom ≫
        (((M.X ⊗ A) ⊗ N.X) ◁ (modListConcat A post Ys).hom)) ≫
      ((w ▷ modList A (post ++ Ys)) ≫
        (α_ M.X N.X (modList A (post ++ Ys))).hom)
  simp only [MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [whisker_exchange_assoc,
    ← associator_naturality_left_assoc, associator_naturality_right]
  rw [pentagon_assoc]

/-- **The right leg-concatenation**: a slot leg of the first block,
whiskered by the second block, is the slot leg of the concatenated
list at the widened suffix. -/
@[reassoc]
lemma modMultiLegOf_concat
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M N : Mod D A) (post Ys : List (Mod D A))
    (w : (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X) :
    ∀ (pre : List (Mod D A))
      (h : pre ++ M :: N :: (post ++ Ys) =
        (pre ++ M :: N :: post) ++ Ys),
    (modMultiLegOf A M N post w pre ▷ modList A Ys) ≫
        (modListConcat A (pre ++ M :: N :: post) Ys).hom =
      modMultiMidConcat A M N post Ys pre ≫
        modMultiLegOf A M N (post ++ Ys) w pre ≫ modListCast A h
  | [], h => by
    simp only [List.nil_append, List.cons_append, modListCast_rfl,
      Category.comp_id]
    exact modMultiLegOf_concat_nil A M N post Ys w
  | P :: rest, h => by
    show ((P.X ◁ modMultiLegOf A M N post w rest) ▷ modList A Ys) ≫
        (modListConcat A (P :: (rest ++ M :: N :: post)) Ys).hom =
      ((α_ P.X (modMultiMid A rest M N post) (modList A Ys)).hom ≫
          (P.X ◁ modMultiMidConcat A M N post Ys rest)) ≫
        (P.X ◁ modMultiLegOf A M N (post ++ Ys) w rest) ≫
          modListCast A h
    rw [modListConcat_cons_whisker A P,
      modMultiLegOf_concat A M N post Ys w rest (by simp)]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [modListCast_whiskerLeft]
    rfl

/-- The relation object of a slot, concatenated on the left: the
prefix grows by the first block. -/
def modMultiMidConcatL [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (pre : List (Mod D A)) (M N : Mod D A)
    (post : List (Mod D A)) :
    (Xs : List (Mod D A)) →
      (modList A Xs ⊗ modMultiMid A pre M N post ⟶
        modMultiMid A (Xs ++ pre) M N post)
  | [] => (λ_ (modMultiMid A pre M N post)).hom
  | P :: rest =>
    (α_ P.X (modList A rest) (modMultiMid A pre M N post)).hom ≫
      (P.X ◁ modMultiMidConcatL A pre M N post rest)

/-- **The left leg-concatenation**: a slot leg of the second block,
whiskered by the first block, is the slot leg of the concatenated
list at the widened prefix. -/
@[reassoc]
lemma modMultiLegOf_concatL
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (pre : List (Mod D A)) (M N : Mod D A)
    (post : List (Mod D A)) (w : (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X) :
    ∀ (Xs : List (Mod D A))
      (h : (Xs ++ pre) ++ M :: N :: post =
        Xs ++ (pre ++ M :: N :: post)),
    (modList A Xs ◁ modMultiLegOf A M N post w pre) ≫
        (modListConcat A Xs (pre ++ M :: N :: post)).hom =
      modMultiMidConcatL A pre M N post Xs ≫
        modMultiLegOf A M N post w (Xs ++ pre) ≫ modListCast A h
  | [], h => by
    show ((𝟙_ D) ◁ modMultiLegOf A M N post w pre) ≫
        (λ_ (modList A (pre ++ M :: N :: post))).hom =
      (λ_ (modMultiMid A pre M N post)).hom ≫
        modMultiLegOf A M N post w pre ≫
          𝟙 (modList A (pre ++ M :: N :: post))
    rw [Category.comp_id, leftUnitor_naturality]
  | P :: rest, h => by
    rw [modListConcat_whiskerLeft_cons A P rest,
      modMultiLegOf_concatL A pre M N post w rest (by simp)]
    show (α_ P.X (modList A rest) (modMultiMid A pre M N post)).hom ≫
        (P.X ◁ (modMultiMidConcatL A pre M N post rest ≫
          modMultiLegOf A M N post w (rest ++ pre) ≫
            modListCast A (show (rest ++ pre) ++ M :: N :: post =
              rest ++ (pre ++ M :: N :: post) by simp))) =
      ((α_ P.X (modList A rest) (modMultiMid A pre M N post)).hom ≫
          (P.X ◁ modMultiMidConcatL A pre M N post rest)) ≫
        ((P.X ◁ modMultiLegOf A M N post w (rest ++ pre)) ≫
          modListCast A h)
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      modListCast_whiskerLeft]
    rfl

end Concat

/-! ## Whiskered descent

Morphisms out of a whiskered multi-tensor, by descent along the
whiskered projection.  The relation source is a biproduct, so the
whiskered relation condition reduces to the slots through the
distributors of the monoidal preadditive structure. -/

section Whisker

/-- Maps out of a right-whiskered biproduct are determined by the
whiskered injections. -/
lemma biproduct_whiskerRight_hom_ext
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D]
    {J : Type} [Fintype J]
    (f : J → D) (P : D) {W : D} {u v : (⨁ f) ⊗ P ⟶ W}
    (h : ∀ j, (biproduct.ι f j ▷ P) ≫ u =
      (biproduct.ι f j ▷ P) ≫ v) :
    u = v := by
  apply (cancel_epi (rightDistributor f P).inv).mp
  apply biproduct.hom_ext'
  intro j
  rw [← Category.assoc, ← Category.assoc,
    biproduct_ι_comp_rightDistributor_inv]
  exact h j

/-- Maps out of a left-whiskered biproduct are determined by the
whiskered injections. -/
lemma biproduct_whiskerLeft_hom_ext
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D]
    {J : Type} [Fintype J]
    (f : J → D) (P : D) {W : D} {u v : P ⊗ (⨁ f) ⟶ W}
    (h : ∀ j, (P ◁ biproduct.ι f j) ≫ u =
      (P ◁ biproduct.ι f j) ≫ v) :
    u = v := by
  apply (cancel_epi (leftDistributor P f).inv).mp
  apply biproduct.hom_ext'
  intro j
  rw [← Category.assoc, ← Category.assoc,
    biproduct_ι_comp_leftDistributor_inv]
  exact h j

section WhiskerRight

/-- Whiskering the multi-tensor coequalizer by `tensorRight P`
yields a colimit cofork. -/
noncomputable def modMultiWhiskerRIsColimit
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    (Xs : List (Mod D A))
    (P : D) :
    IsColimit (Cofork.ofπ (modMultiπ A Xs ▷ P)
      (by rw [← MonoidalCategory.comp_whiskerRight,
        modMulti_condition, MonoidalCategory.comp_whiskerRight]) :
      Cofork (modMultiLegFst A Xs ▷ P) (modMultiLegSnd A Xs ▷ P)) :=
  isColimitOfHasCoequalizerOfPreservesColimit
    (MonoidalCategory.tensorRight P) _ _

/-- Morphisms out of a right-whiskered multi-tensor are determined
by their composite with the whiskered projection. -/
lemma modMulti_whiskerR_hom_ext
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    (Xs : List (Mod D A)) (P : D)
    {W : D} {k l : modMulti A Xs ⊗ P ⟶ W}
    (h : (modMultiπ A Xs ▷ P) ≫ k = (modMultiπ A Xs ▷ P) ≫ l) :
    k = l :=
  Cofork.IsColimit.hom_ext (modMultiWhiskerRIsColimit A Xs P) h

/-- Descend a morphism coequalizing every right-whiskered slot
relation along the right-whiskered projection. -/
noncomputable def modMultiWhiskerRDesc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    (Xs : List (Mod D A)) (P : D)
    {W : D} (k : modList A Xs ⊗ P ⟶ W)
    (h : ∀ (pre : List (Mod D A)) (M N : Mod D A)
      (post : List (Mod D A)) (hd : Xs = pre ++ M :: N :: post),
      ((modMultiLegM A pre M N post ≫ modListCast A hd.symm) ▷ P) ≫
          k =
        ((modMultiLegN A pre M N post ≫ modListCast A hd.symm) ▷ P) ≫
          k) :
    modMulti A Xs ⊗ P ⟶ W :=
  Cofork.IsColimit.desc (modMultiWhiskerRIsColimit A Xs P) k
    (by
      apply biproduct_whiskerRight_hom_ext
      intro j
      rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
        ← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
      simp only [modMultiLegFst, modMultiLegSnd, biproduct.ι_desc]
      have hs := h (modSlots A Xs)[j.1].pre (modSlots A Xs)[j.1].fst
        (modSlots A Xs)[j.1].snd (modSlots A Xs)[j.1].post
        (modSlots A Xs)[j.1].eq
      simpa [ModSlot.legM, ModSlot.legN] using hs)

/-- The right-whiskered descent factors the given morphism through
the whiskered projection. -/
@[reassoc (attr := simp)]
lemma whiskerRight_modMultiπ_whiskerRDesc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    (Xs : List (Mod D A))
    (P : D) {W : D} (k : modList A Xs ⊗ P ⟶ W)
    (h : ∀ (pre : List (Mod D A)) (M N : Mod D A)
      (post : List (Mod D A)) (hd : Xs = pre ++ M :: N :: post),
      ((modMultiLegM A pre M N post ≫ modListCast A hd.symm) ▷ P) ≫
          k =
        ((modMultiLegN A pre M N post ≫ modListCast A hd.symm) ▷ P) ≫
          k) :
    (modMultiπ A Xs ▷ P) ≫ modMultiWhiskerRDesc A Xs P k h = k :=
  Cofork.IsColimit.π_desc' (modMultiWhiskerRIsColimit A Xs P) k _

end WhiskerRight

section WhiskerLeft

/-- Whiskering the multi-tensor coequalizer by `tensorLeft P`
yields a colimit cofork. -/
noncomputable def modMultiWhiskerLIsColimit
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (Xs : List (Mod D A))
    (P : D) :
    IsColimit (Cofork.ofπ (P ◁ modMultiπ A Xs)
      (by rw [← MonoidalCategory.whiskerLeft_comp,
        modMulti_condition, MonoidalCategory.whiskerLeft_comp]) :
      Cofork (P ◁ modMultiLegFst A Xs) (P ◁ modMultiLegSnd A Xs)) :=
  isColimitOfHasCoequalizerOfPreservesColimit
    (MonoidalCategory.tensorLeft P) _ _

/-- Morphisms out of a left-whiskered multi-tensor are determined
by their composite with the whiskered projection. -/
lemma modMulti_whiskerL_hom_ext
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (Xs : List (Mod D A)) (P : D)
    {W : D} {k l : P ⊗ modMulti A Xs ⟶ W}
    (h : (P ◁ modMultiπ A Xs) ≫ k = (P ◁ modMultiπ A Xs) ≫ l) :
    k = l :=
  Cofork.IsColimit.hom_ext (modMultiWhiskerLIsColimit A Xs P) h

/-- Descend a morphism coequalizing every left-whiskered slot
relation along the left-whiskered projection. -/
noncomputable def modMultiWhiskerLDesc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (Xs : List (Mod D A)) (P : D)
    {W : D} (k : P ⊗ modList A Xs ⟶ W)
    (h : ∀ (pre : List (Mod D A)) (M N : Mod D A)
      (post : List (Mod D A)) (hd : Xs = pre ++ M :: N :: post),
      (P ◁ (modMultiLegM A pre M N post ≫ modListCast A hd.symm)) ≫
          k =
        (P ◁ (modMultiLegN A pre M N post ≫ modListCast A hd.symm)) ≫
          k) :
    P ⊗ modMulti A Xs ⟶ W :=
  Cofork.IsColimit.desc (modMultiWhiskerLIsColimit A Xs P) k
    (by
      apply biproduct_whiskerLeft_hom_ext
      intro j
      rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp,
        ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
      simp only [modMultiLegFst, modMultiLegSnd, biproduct.ι_desc]
      have hs := h (modSlots A Xs)[j.1].pre (modSlots A Xs)[j.1].fst
        (modSlots A Xs)[j.1].snd (modSlots A Xs)[j.1].post
        (modSlots A Xs)[j.1].eq
      simpa [ModSlot.legM, ModSlot.legN] using hs)

/-- The left-whiskered descent factors the given morphism through
the whiskered projection. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_modMultiπ_whiskerLDesc
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (Xs : List (Mod D A))
    (P : D) {W : D} (k : P ⊗ modList A Xs ⟶ W)
    (h : ∀ (pre : List (Mod D A)) (M N : Mod D A)
      (post : List (Mod D A)) (hd : Xs = pre ++ M :: N :: post),
      (P ◁ (modMultiLegM A pre M N post ≫ modListCast A hd.symm)) ≫
          k =
        (P ◁ (modMultiLegN A pre M N post ≫ modListCast A hd.symm)) ≫
          k) :
    (P ◁ modMultiπ A Xs) ≫ modMultiWhiskerLDesc A Xs P k h = k :=
  Cofork.IsColimit.π_desc' (modMultiWhiskerLIsColimit A Xs P) k _

end WhiskerLeft

end Whisker

/-! ## The concatenation map

The projection of the concatenated list descends through the tensor
product of the two multi-tensors, one block at a time: first the
relations of the first block through the right-whiskered
coequalizer, then those of the second block through the
left-whiskered coequalizer. -/

section ConcatMap

/-- First stage of the concatenation: the relations of the first
block descend, the second block still at the fold. -/
noncomputable def modMultiConcatFst
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    (Xs Ys : List (Mod D A)) :
    modMulti A Xs ⊗ modList A Ys ⟶ modMulti A (Xs ++ Ys) :=
  modMultiWhiskerRDesc A Xs (modList A Ys)
    ((modListConcat A Xs Ys).hom ≫ modMultiπ A (Xs ++ Ys))
    (by
      intro pre M N post hd
      subst hd
      simp only [modListCast_rfl, Category.comp_id]
      rw [modMultiLegM, modMultiLegN,
        modMultiLegOf_concat_assoc A M N post Ys _ pre (by simp),
        modMultiLegOf_concat_assoc A M N post Ys _ pre (by simp)]
      have hrel := modMulti_rel A pre M N (post ++ Ys)
        (show (pre ++ M :: N :: post) ++ Ys =
          pre ++ M :: N :: (post ++ Ys) by simp)
      rw [modMultiLegM, modMultiLegN] at hrel
      exact congrArg (modMultiMidConcat A M N post Ys pre ≫ ·) hrel)

/-- Defining equation of the first stage. -/
@[reassoc (attr := simp)]
lemma whiskerRight_modMultiπ_concatFst
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    (Xs Ys : List (Mod D A)) :
    (modMultiπ A Xs ▷ modList A Ys) ≫ modMultiConcatFst A Xs Ys =
      (modListConcat A Xs Ys).hom ≫ modMultiπ A (Xs ++ Ys) :=
  whiskerRight_modMultiπ_whiskerRDesc A Xs _ _ _

/-- **The concatenation map**: the multi-tensor of a concatenated
list receives the tensor product of the two multi-tensors. -/
noncomputable def modMultiConcat
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (Xs Ys : List (Mod D A)) :
    modMulti A Xs ⊗ modMulti A Ys ⟶ modMulti A (Xs ++ Ys) :=
  modMultiWhiskerLDesc A Ys (modMulti A Xs)
    (modMultiConcatFst A Xs Ys)
    (by
      intro pre M N post hd
      subst hd
      simp only [modListCast_rfl, Category.comp_id]
      apply modMulti_whiskerR_hom_ext A Xs
      rw [← whisker_exchange_assoc, ← whisker_exchange_assoc,
        whiskerRight_modMultiπ_concatFst]
      rw [modMultiLegM, modMultiLegN,
        modMultiLegOf_concatL_assoc A pre M N post _ Xs (by simp),
        modMultiLegOf_concatL_assoc A pre M N post _ Xs (by simp)]
      have hrel := modMulti_rel A (Xs ++ pre) M N post
        (show Xs ++ (pre ++ M :: N :: post) =
          (Xs ++ pre) ++ M :: N :: post by simp)
      rw [modMultiLegM, modMultiLegN] at hrel
      exact congrArg
        (modMultiMidConcatL A pre M N post Xs ≫ ·) hrel)

/-- Defining equation of the concatenation against the projection
of the second block. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_modMultiπ_concat
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (Xs Ys : List (Mod D A)) :
    (modMulti A Xs ◁ modMultiπ A Ys) ≫ modMultiConcat A Xs Ys =
      modMultiConcatFst A Xs Ys :=
  whiskerLeft_modMultiπ_whiskerLDesc A Ys _ _ _

/-- **Defining equation of the concatenation**: on the two
projections it is the fold concatenation followed by the projection
of the concatenated list. -/
@[reassoc]
lemma tensorHom_modMultiπ_concat
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [Preadditive D] [MonoidalPreadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorRight Y)]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (Xs Ys : List (Mod D A)) :
    (modMultiπ A Xs ⊗ₘ modMultiπ A Ys) ≫ modMultiConcat A Xs Ys =
      (modListConcat A Xs Ys).hom ≫ modMultiπ A (Xs ++ Ys) := by
  rw [tensorHom_def, Category.assoc, whiskerLeft_modMultiπ_concat,
    whiskerRight_modMultiπ_concatFst]

end ConcatMap

/-! ## The head action

On a non-empty list the monoid acts through the head factor; the
action descends to the multi-tensor, making it a module.  The slot
compatibilities are the two cases: the slot at the head, through
the binary window compatibilities of `ModTensor.lean`, and a slot
in the tail, disjoint from the action. -/

section HeadAction

/-- The head action on the fold of a non-empty list: act on the
head factor. -/
def modListHeadAct [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : Mod D A) (l : List (Mod D A)) :
    A ⊗ modList A (X :: l) ⟶ modList A (X :: l) :=
  (α_ A X.X (modList A l)).inv ≫ (actLeft A X.X ▷ modList A l)

/-- Unitality of the head action. -/
lemma modListHeadAct_one
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : Mod D A) (l : List (Mod D A)) :
    η[A] ▷ modList A (X :: l) ≫ modListHeadAct A X l =
      (λ_ (modList A (X :: l))).hom :=
  one_act_tensorRight A X.X (actLeft A X.X) (one_actLeft A X.X)
    (modList A l)

/-- Associativity of the head action. -/
lemma modListHeadAct_mul
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : Mod D A) (l : List (Mod D A)) :
    μ[A] ▷ modList A (X :: l) ≫ modListHeadAct A X l =
      (α_ A A (modList A (X :: l))).hom ≫
        (A ◁ modListHeadAct A X l) ≫ modListHeadAct A X l :=
  mul_act_tensorRight A X.X (actLeft A X.X) (mul_actLeft A X.X)
    (modList A l)

/-- The shuffle of the head slot: the monoid moves inside the
window and acts on the left module factor there. -/
def modMultiHeadShuffle [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M N : Mod D A) (post : List (Mod D A)) :
    A ⊗ modMultiMid A [] M N post ⟶ modMultiMid A [] M N post :=
  (α_ A ((M.X ⊗ A) ⊗ N.X) (modList A post)).inv ≫
    (((α_ A (M.X ⊗ A) N.X).inv ≫
      ((α_ A M.X A).inv ≫ actLeft A M.X ▷ A) ▷ N.X) ▷
        modList A post)

/-- **The head-slot compatibility**: a window morphism compatible
with the binary action commutes the head action past the head
slot's leg. -/
@[reassoc]
lemma modListHeadAct_window
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (M N : Mod D A) (post : List (Mod D A))
    (w : (M.X ⊗ A) ⊗ N.X ⟶ M.X ⊗ N.X)
    (hw : A ◁ w ≫ ((α_ A M.X N.X).inv ≫ actLeft A M.X ▷ N.X) =
      ((α_ A (M.X ⊗ A) N.X).inv ≫
        ((α_ A M.X A).inv ≫ actLeft A M.X ▷ A) ▷ N.X) ≫ w) :
    (A ◁ modMultiLegOf A M N post w []) ≫
        modListHeadAct A M (N :: post) =
      modMultiHeadShuffle A M N post ≫
        modMultiLegOf A M N post w [] := by
  have hcoh : (A ◁ (α_ M.X N.X (modList A post)).hom) ≫
      (α_ A M.X (N.X ⊗ modList A post)).inv =
    (α_ A (M.X ⊗ N.X) (modList A post)).inv ≫
      ((α_ A M.X N.X).inv ▷ modList A post) ≫
        (α_ (A ⊗ M.X) N.X (modList A post)).hom := by
    monoidal
  show (A ◁ ((w ▷ modList A post) ≫
        (α_ M.X N.X (modList A post)).hom)) ≫
      ((α_ A M.X (N.X ⊗ modList A post)).inv ≫
        (actLeft A M.X ▷ (N.X ⊗ modList A post))) =
    ((α_ A ((M.X ⊗ A) ⊗ N.X) (modList A post)).inv ≫
        (((α_ A (M.X ⊗ A) N.X).inv ≫
          ((α_ A M.X A).inv ≫ actLeft A M.X ▷ A) ▷ N.X) ▷
            modList A post)) ≫
      ((w ▷ modList A post) ≫ (α_ M.X N.X (modList A post)).hom)
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  conv_rhs => rw [← MonoidalCategory.comp_whiskerRight_assoc, ← hw]
  simp only [MonoidalCategory.comp_whiskerRight, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc,
    associator_naturality_left, reassoc_of% hcoh]

/-- **The tail-slot compatibility**: the head action is disjoint
from any morphism whiskered under the head factor. -/
@[reassoc]
lemma modListHeadAct_tail
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    (X : Mod D A) {S : D}
    {T : List (Mod D A)} (u : S ⟶ modList A T) :
    (A ◁ (X.X ◁ u)) ≫ modListHeadAct A X T =
      ((α_ A X.X S).inv ≫ (actLeft A X.X ▷ S)) ≫ (X.X ◁ u) := by
  show (A ◁ (X.X ◁ u)) ≫
      ((α_ A X.X (modList A T)).inv ≫
        (actLeft A X.X ▷ modList A T)) =
    ((α_ A X.X S).inv ≫ (actLeft A X.X ▷ S)) ≫ (X.X ◁ u)
  rw [associator_inv_naturality_right_assoc, Category.assoc,
    whisker_exchange]

end HeadAction

/-! ## Descent of the head action -/

section HeadDescent

/-- The head action carries every slot relation into the kernel of
the projection. -/
lemma modListHeadAct_slotwise
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [HasFiniteBiproducts D] [HasCoequalizers D]
    (X : Mod D A) (l : List (Mod D A))
    (pre : List (Mod D A)) (M N : Mod D A) (post : List (Mod D A))
    (hd : X :: l = pre ++ M :: N :: post) :
    (A ◁ (modMultiLegM A pre M N post ≫ modListCast A hd.symm)) ≫
        (modListHeadAct A X l ≫ modMultiπ A (X :: l)) =
      (A ◁ (modMultiLegN A pre M N post ≫ modListCast A hd.symm)) ≫
        (modListHeadAct A X l ≫ modMultiπ A (X :: l)) := by
  rcases pre with _ | ⟨P, pre'⟩
  · rw [List.nil_append] at hd
    injection hd with h1 h2
    subst h1
    subst h2
    rw [modMultiLegM, modMultiLegN]
    show (A ◁ (modMultiLegOf A X N post (modTensorLegM A X N) [] ≫
          𝟙 (modList A ([] ++ X :: N :: post)))) ≫
        (modListHeadAct A X (N :: post) ≫
          modMultiπ A (X :: N :: post)) =
      (A ◁ (modMultiLegOf A X N post (modTensorLegN A X N) [] ≫
          𝟙 (modList A ([] ++ X :: N :: post)))) ≫
        (modListHeadAct A X (N :: post) ≫
          modMultiπ A (X :: N :: post))
    rw [Category.comp_id, Category.comp_id,
      modListHeadAct_window_assoc A X N post _
        (whiskerLeft_modTensorLegM_act A X N A (actLeft A X.X)
          (actLeft_actRight A X.X)),
      modListHeadAct_window_assoc A X N post _
        (whiskerLeft_modTensorLegN_act A X N A (actLeft A X.X))]
    have hrel := modMulti_rel A [] X N post
      (rfl : X :: N :: post = [] ++ X :: N :: post)
    simp only [List.nil_append, modListCast_rfl, Category.id_comp]
      at hrel
    rw [modMultiLegM, modMultiLegN] at hrel
    exact (Category.assoc _ _ _).trans
      ((congrArg (modMultiHeadShuffle A X N post ≫ ·) hrel).trans
        (Category.assoc _ _ _).symm)
  · rw [List.cons_append] at hd
    injection hd with h1 h2
    subst h1
    subst h2
    rw [modMultiLegM, modMultiLegN]
    show (A ◁ ((X.X ◁ modMultiLegOf A M N post
            (modTensorLegM A M N) pre') ≫
          𝟙 (X.X ⊗ modList A (pre' ++ M :: N :: post)))) ≫
        (modListHeadAct A X (pre' ++ M :: N :: post) ≫
          modMultiπ A (X :: (pre' ++ M :: N :: post))) =
      (A ◁ ((X.X ◁ modMultiLegOf A M N post
            (modTensorLegN A M N) pre') ≫
          𝟙 (X.X ⊗ modList A (pre' ++ M :: N :: post)))) ≫
        (modListHeadAct A X (pre' ++ M :: N :: post) ≫
          modMultiπ A (X :: (pre' ++ M :: N :: post)))
    rw [Category.comp_id, Category.comp_id,
      modListHeadAct_tail_assoc A X _, modListHeadAct_tail_assoc A X _]
    have hrel := modMulti_rel A (X :: pre') M N post
      (show X :: (pre' ++ M :: N :: post) =
        (X :: pre') ++ M :: N :: post by simp)
    simp only [List.cons_append, modListCast_rfl, Category.id_comp]
      at hrel
    rw [modMultiLegM, modMultiLegN, modMultiLegOf_cons,
      modMultiLegOf_cons] at hrel
    have h4 : (actLeft A X.X ▷ modMultiMid A pre' M N post ≫
        X.X ◁ modMultiLegOf A M N post (modTensorLegM A M N) pre') ≫
          modMultiπ A (X :: (pre' ++ M :: N :: post)) =
      (actLeft A X.X ▷ modMultiMid A pre' M N post ≫
        X.X ◁ modMultiLegOf A M N post (modTensorLegN A M N) pre') ≫
          modMultiπ A (X :: (pre' ++ M :: N :: post)) :=
      (Category.assoc _ _ _).trans
        ((congrArg
          (actLeft A X.X ▷ modMultiMid A pre' M N post ≫ ·)
          hrel).trans (Category.assoc _ _ _).symm)
    exact (Category.assoc _ _ _).trans
      ((congrArg
        ((α_ A X.X (modMultiMid A pre' M N post)).inv ≫ ·)
        h4).trans (Category.assoc _ _ _).symm)

/-- **The head action on the multi-tensor**, by descent. -/
noncomputable def modMultiHeadAct
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X : Mod D A) (l : List (Mod D A)) :
    A ⊗ modMulti A (X :: l) ⟶ modMulti A (X :: l) :=
  modMultiWhiskerLDesc A (X :: l) A
    (modListHeadAct A X l ≫ modMultiπ A (X :: l))
    (fun pre M N post hd =>
      modListHeadAct_slotwise A X l pre M N post hd)

/-- Defining equation of the descended head action. -/
@[reassoc (attr := simp)]
lemma whiskerLeft_modMultiπ_headAct
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X : Mod D A)
    (l : List (Mod D A)) :
    (A ◁ modMultiπ A (X :: l)) ≫ modMultiHeadAct A X l =
      modListHeadAct A X l ≫ modMultiπ A (X :: l) :=
  whiskerLeft_modMultiπ_whiskerLDesc A (X :: l) A _ _

/-- Unitality of the descended head action. -/
lemma modMultiHeadAct_one
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X : Mod D A) (l : List (Mod D A)) :
    η[A] ▷ modMulti A (X :: l) ≫ modMultiHeadAct A X l =
      (λ_ (modMulti A (X :: l))).hom := by
  apply modMulti_whiskerL_hom_ext A (X :: l) (𝟙_ D)
  rw [whisker_exchange_assoc, whiskerLeft_modMultiπ_headAct,
    reassoc_of% (modListHeadAct_one A X l)]
  conv_rhs => rw [leftUnitor_naturality]

/-- Associativity of the descended head action. -/
lemma modMultiHeadAct_mul
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X : Mod D A) (l : List (Mod D A)) :
    μ[A] ▷ modMulti A (X :: l) ≫ modMultiHeadAct A X l =
      (α_ A A (modMulti A (X :: l))).hom ≫
        (A ◁ modMultiHeadAct A X l) ≫ modMultiHeadAct A X l := by
  apply modMulti_whiskerL_hom_ext A (X :: l) (A ⊗ A)
  conv_lhs => rw [whisker_exchange_assoc,
    whiskerLeft_modMultiπ_headAct]
  conv_rhs => rw [associator_naturality_right_assoc,
    ← MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_modMultiπ_headAct,
    MonoidalCategory.whiskerLeft_comp_assoc,
    whiskerLeft_modMultiπ_headAct]
  rw [reassoc_of% (modListHeadAct_mul A X l)]

/-- The multi-tensor of a non-empty list is a module over `A`. -/
@[implicit_reducible]
noncomputable def modMultiModObj
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X : Mod D A) (l : List (Mod D A)) :
    ModObj A (modMulti A (X :: l)) where
  smul := modMultiHeadAct A X l
  one_smul := modMultiHeadAct_one A X l
  mul_smul := modMultiHeadAct_mul A X l

/-- The multi-tensor of a non-empty list, bundled as a module. -/
noncomputable def modMultiMod
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X : Mod D A) (l : List (Mod D A)) :
    Mod D A :=
  letI := modMultiModObj A X l
  ⟨modMulti A (X :: l)⟩

@[simp] lemma modMultiMod_X
    [Category.{v} D] [MonoidalCategory D] (A : D) [MonObj A]
    [BraidedCategory D] [IsCommMonObj A] [Preadditive D]
    [MonoidalPreadditive D] [HasFiniteBiproducts D] [HasCoequalizers D]
    [∀ Y : D, PreservesColimitsOfShape WalkingParallelPair
      (MonoidalCategory.tensorLeft Y)]
    (X : Mod D A) (l : List (Mod D A)) :
    (modMultiMod A X l).X = modMulti A (X :: l) :=
  rfl

end HeadDescent

end RS
