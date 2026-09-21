/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.WordMap

/-!
# The kernel of a tensor power of an epimorphism

The exactness half of the mixed filtration for Deligne 1.19's
extension argument (Catégories tensorielles): if `ι : U ⟶ Z` covers
the kernel of an epimorphism `π : Z ⟶ W`, then the kernel of
`π ^ ⊗ m` is covered by the images of the word maps of `ι` and
`𝟙 Z` with exactly one `ι`-slot (`kernelSubobject_tensorPowMap_le`).

**The exactness hypothesis.**  The kernel condition is stated as
`hker : kernelSubobject π ≤ imageSubobject ι` — only the covering
half of exactness is consumed, so neither `Mono ι` nor `ι ≫ π = 0`
is assumed.  For a genuinely exact pair, with `Mono ι` and
`hexact : imageSubobject ι = kernelSubobject π`, apply the theorems
at `hker := hexact.ge`.

Three layers:

* **Word concatenation** (pure monoidal coherence): appended words
  `wordAppend` concatenate word powers (`wordPowConcatIso`) and word
  maps (`wordMap_append`), mirroring `wordMap_standard`; letter
  counts add (`popCount_wordAppend`).  At the level of images this
  is `imageSubobject_wordMap_concat`.
* **The two-factor kernel** (the abelian heart): in a rigid abelian
  monoidal category the kernel of `p₁ ⊗ₘ p₂`, for `p₁` epi, is the
  join of the images of the two one-slot kernel insertions
  (`kernelSubobject_tensorHom_le`, an equality by
  `kernelSubobject_tensorHom`).  The chase runs through the
  factorisation `p₁ ⊗ₘ p₂ = (p₁ ▷ Z₂) ≫ (W₁ ◁ p₂)`, the
  identification of whiskered kernels
  (`kernelSubobject_whiskerRight_le`), and a pullback of the
  covering epimorphism (`kernelSubobject_comp_le_of_cover`).
* **The iterated kernel**: induction along
  `tensorPowMap π (m + 1) = tensorPowMap π m ⊗ₘ π`, transporting
  the inductive cover through the tensor structure.  The cover is
  a single morphism from a biproduct of one-slot word powers
  (`oneSlotCover`), and the final statement is phrased as a
  `Finset.sup` of image subobjects: the ambient category is not
  assumed well-powered, so the subobject lattice carries finite
  joins but no indexed supremum.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable {A : Type u}

/-! ## Appended words

`wordAppend` is `Fin.append`: the first word occupies the low
block.  This matches the orientation of `tensorPowConcat` and
`standardWord`, whose first factor is also the low block
(`wordAppend_const_true_false`).
-/

/-- **The appended word**: `wa` on the low block, `wb` on the high
block. -/
def wordAppend {a b : ℕ} (wa : Fin a → Bool) (wb : Fin b → Bool) :
    Fin (a + b) → Bool :=
  Fin.append wa wb

/-- Appending the empty word is the identity. -/
theorem wordAppend_zero {a : ℕ} (wa : Fin a → Bool)
    (wb : Fin 0 → Bool) : wordAppend wa wb = wa := by
  funext i
  induction i using Fin.addCases with
  | left j => exact Fin.append_left wa wb j
  | right j => exact j.elim0

/-- Restricting an appended word restricts the second word. -/
theorem wordAppend_castSucc {a b : ℕ} (wa : Fin a → Bool)
    (wb : Fin (b + 1) → Bool) :
    wordAppend wa wb ∘ Fin.castSucc =
      wordAppend wa (wb ∘ Fin.castSucc) := by
  funext i
  induction i using Fin.addCases with
  | left j =>
    exact (Fin.append_left wa wb j).trans
      (Fin.append_left wa (wb ∘ Fin.castSucc) j).symm
  | right j =>
    exact (Fin.append_right wa wb (Fin.castSucc j)).trans
      (Fin.append_right wa (wb ∘ Fin.castSucc) j).symm

/-- The last letter of an appended word is the second word's last
letter. -/
theorem wordAppend_last {a b : ℕ} (wa : Fin a → Bool)
    (wb : Fin (b + 1) → Bool) :
    wordAppend wa wb (Fin.last (a + b)) = wb (Fin.last b) :=
  Fin.append_right wa wb (Fin.last b)

/-- Letter counts add across an appended word. -/
theorem popCount_wordAppend {a b : ℕ} (wa : Fin a → Bool)
    (wb : Fin b → Bool) :
    popCount (wordAppend wa wb) = popCount wa + popCount wb := by
  have key : ∀ (m : ℕ) (v : Fin m → Bool),
      popCount v = ∑ i, if v i = true then 1 else 0 := by
    intro m v
    simp [popCount]
  rw [key, key, key, Fin.sum_univ_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by
      rw [wordAppend, Fin.append_left]
  · exact Finset.sum_congr rfl fun i _ => by
      rw [wordAppend, Fin.append_right]

/-- The sorted word is the all-`true` word appended to the
all-`false` word: `wordAppend`'s low block matches
`standardWord`'s. -/
theorem wordAppend_const_true_false (p q : ℕ) :
    wordAppend (fun _ : Fin p => true) (fun _ : Fin q => false) =
      standardWord p q := by
  funext i
  induction i using Fin.addCases with
  | left j =>
    rw [wordAppend, Fin.append_left]
    exact (decide_eq_true j.isLt).symm
  | right j =>
    rw [wordAppend, Fin.append_right]
    simp [standardWord]

/-! ## Word powers of appended words -/

/-- Appending the empty word does not change the word power. -/
theorem wordPow_append_zero [Category.{v} A] [MonoidalCategory A]
    (U V : A) {a : ℕ} (wa : Fin a → Bool)
    (wb : Fin 0 → Bool) :
    wordPow U V (a + 0) (wordAppend wa wb) = wordPow U V a wa :=
  congrArg (wordPow U V a) (wordAppend_zero wa wb)

/-- One more letter of the second word tensors the selected
object. -/
theorem wordPow_append_succ [Category.{v} A] [MonoidalCategory A]
    (U V : A) {a b : ℕ} (wa : Fin a → Bool)
    (wb : Fin (b + 1) → Bool) :
    wordPow U V (a + (b + 1)) (wordAppend wa wb) =
      wordPow U V (a + b) (wordAppend wa (wb ∘ Fin.castSucc)) ⊗
        (bif wb (Fin.last b) then U else V) := by
  show wordPow U V (a + b) (wordAppend wa wb ∘ Fin.castSucc) ⊗
      (bif wordAppend wa wb (Fin.last (a + b)) then U else V) = _
  rw [wordAppend_castSucc, wordAppend_last]

/-- **The word powers of an appended word concatenate**: the word
power of `wordAppend wa wb` is the tensor of the two word powers,
by the recursion of the second word.  Built stage by stage, mirror
to `standardMixedIso`, so that consumers can compose with it. -/
noncomputable def wordPowConcatIso [Category.{v} A] [MonoidalCategory A]
    (U V : A) {a : ℕ}
    (wa : Fin a → Bool) : (b : ℕ) → (wb : Fin b → Bool) →
      (wordPow U V (a + b) (wordAppend wa wb) ≅
        wordPow U V a wa ⊗ wordPow U V b wb)
  | 0, wb =>
      eqToIso (wordPow_append_zero U V wa wb) ≪≫
        (ρ_ (wordPow U V a wa)).symm
  | b + 1, wb =>
      eqToIso (wordPow_append_succ U V wa wb) ≪≫
        whiskerRightIso
          (wordPowConcatIso U V wa b (wb ∘ Fin.castSucc)) _ ≪≫
        α_ (wordPow U V a wa)
          (wordPow U V b (wb ∘ Fin.castSucc))
          (bif wb (Fin.last b) then U else V)

/-! ## The concatenation square

The word map of an appended word is the tensor of the two word
maps, followed by the concatenation of the target powers, under
`wordPowConcatIso`.  The gluing helpers replicate the private
steps of `wordMap_standard` at general objects, applied by
`exact`, so that no tensor-power arity enters the rewriting.
-/

/-- Tensoring with the unit's identity is unitor conjugation.
Stated at general objects. -/
private theorem unit_tensor_unitor [Category.{v} A] [MonoidalCategory A]
    {P Q : A} (k : P ⟶ Q) :
    (k ⊗ₘ 𝟙 (𝟙_ A)) ≫ (ρ_ Q).hom = (ρ_ P).hom ≫ k := by
  rw [MonoidalCategory.tensorHom_id]
  exact MonoidalCategory.rightUnitor_naturality k

/-- One stage of the concatenation glued onto an intertwining of
the previous stage.  Stated at general objects. -/
private theorem concat_step_glue [Category.{v} A] [MonoidalCategory A]
    {P Q W R P' Q' S T : A}
    (u : P ⊗ Q ⟶ W) (M : W ⟶ R) (v₁ : P ⟶ P') (v₂ : Q ⟶ Q')
    (c : P' ⊗ Q' ⟶ R) (e : S ⟶ T)
    (hih : u ≫ M = (v₁ ⊗ₘ v₂) ≫ c) :
    (α_ P Q S).inv ≫ ((u ▷ S) ≫ (M ⊗ₘ e)) =
      (v₁ ⊗ₘ (v₂ ⊗ₘ e)) ≫ (α_ P' Q' T).inv ≫ (c ▷ T) := by
  have h1 : (u ▷ S) ≫ (M ⊗ₘ e) = (u ≫ M) ⊗ₘ e := by
    rw [← MonoidalCategory.tensorHom_id u S,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  have h2 : ((v₁ ⊗ₘ v₂) ⊗ₘ e) ≫ (c ▷ T) = ((v₁ ⊗ₘ v₂) ≫ c) ⊗ₘ e := by
    rw [← MonoidalCategory.tensorHom_id c T,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  have h3 : (α_ P Q S).inv ≫ ((v₁ ⊗ₘ v₂) ⊗ₘ e) =
      (v₁ ⊗ₘ (v₂ ⊗ₘ e)) ≫ (α_ P' Q' T).inv :=
    (MonoidalCategory.associator_inv_naturality v₁ v₂ e).symm
  calc (α_ P Q S).inv ≫ ((u ▷ S) ≫ (M ⊗ₘ e))
      = (α_ P Q S).inv ≫ (((v₁ ⊗ₘ v₂) ≫ c) ⊗ₘ e) := by rw [h1, hih]
    _ = (α_ P Q S).inv ≫ ((v₁ ⊗ₘ v₂) ⊗ₘ e) ≫ (c ▷ T) := by rw [h2]
    _ = ((v₁ ⊗ₘ (v₂ ⊗ₘ e)) ≫ (α_ P' Q' T).inv) ≫ (c ▷ T) := by
        rw [← Category.assoc, h3]
    _ = (v₁ ⊗ₘ (v₂ ⊗ₘ e)) ≫ (α_ P' Q' T).inv ≫ (c ▷ T) :=
        Category.assoc _ _ _

/-- A transport and its inverse cancel across a decomposition of
the middle morphism.  Stated at general objects and applied by
`exact`, so the defeq-mismatched arities never enter a rewrite. -/
private theorem cast_cancel_glue [Category.{v} A]
    {M N W R : A} (h : N = W)
    (h' : W = N) (a : M ⟶ N) (D : W ⟶ R) (T : N ⟶ R)
    (hD : D = eqToHom h' ≫ T) :
    (a ≫ eqToHom h) ≫ D = a ≫ T := by
  subst h
  rw [hD, show h' = rfl from rfl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

/-- Transport along the `a + 0` arity cast composes away against
the word map of the first word. -/
private theorem word_map_cast
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) {a : ℕ}
    (wa : Fin a → Bool)
    (H : wordPow U V a wa = wordPow U V (a + 0) wa) :
    eqToHom H ≫ wordMap f g (a + 0) wa = wordMap f g a wa := by
  rw [show H = rfl from rfl, eqToHom_refl, Category.id_comp]
  rfl

/-- **The concatenation square**: the word map of an appended word
is the tensor of the two word maps followed by the concatenation
of the pure target powers, under `wordPowConcatIso` at the
source. -/
theorem wordMap_append
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) {a : ℕ}
    (wa : Fin a → Bool) :
    ∀ (b : ℕ) (wb : Fin b → Bool),
      (wordPowConcatIso U V wa b wb).inv ≫
          wordMap f g (a + b) (wordAppend wa wb) =
        (wordMap f g a wa ⊗ₘ wordMap f g b wb) ≫
          (tensorPowConcat Z a b).hom := by
  intro b
  induction b with
  | zero =>
    intro wb
    have hkey : eqToHom (wordPow_append_zero U V wa wb).symm ≫
        wordMap f g (a + 0) (wordAppend wa wb) =
        wordMap f g a wa := by
      rw [wordMap_congr f g (wordAppend_zero wa wb),
        eqToHom_trans_assoc]
      exact word_map_cast f g wa _
    show ((ρ_ (wordPow U V a wa)).hom ≫
          eqToHom (wordPow_append_zero U V wa wb).symm) ≫
        wordMap f g (a + 0) (wordAppend wa wb) =
      (wordMap f g a wa ⊗ₘ 𝟙 (𝟙_ A)) ≫
        (ρ_ (tensorPow A Z a)).hom
    rw [Category.assoc, hkey]
    exact (unit_tensor_unitor (wordMap f g a wa)).symm
  | succ b ih =>
    intro wb
    have hstep : wordPow U V (a + (b + 1)) (wordAppend wa wb) =
        wordPow U V (a + b) (wordAppend wa (wb ∘ Fin.castSucc)) ⊗
          (bif wb (Fin.last b) then U else V) :=
      wordPow_append_succ U V wa wb
    have hsplit := wordMap_split f g (a + b)
      (wordAppend (a := a) (b := b + 1) wa wb)
      (wordAppend wa (wb ∘ Fin.castSucc)) (wb (Fin.last b))
      (wordAppend_castSucc wa wb) (wordAppend_last wa wb) hstep
    refine (cast_cancel_glue hstep.symm hstep
      ((α_ (wordPow U V a wa)
          (wordPow U V b (wb ∘ Fin.castSucc))
          (bif wb (Fin.last b) then U else V)).inv ≫
        ((wordPowConcatIso U V wa b (wb ∘ Fin.castSucc)).inv ▷ _))
      (wordMap f g (a + (b + 1)) (wordAppend wa wb))
      (wordMap f g (a + b) (wordAppend wa (wb ∘ Fin.castSucc)) ⊗ₘ
        letterMap f g (wb (Fin.last b)))
      hsplit).trans ?_
    erw [Category.assoc]
    exact concat_step_glue
      (wordPowConcatIso U V wa b (wb ∘ Fin.castSucc)).inv
      (wordMap f g (a + b) (wordAppend wa (wb ∘ Fin.castSucc)))
      (wordMap f g a wa) (wordMap f g b (wb ∘ Fin.castSucc))
      (tensorPowConcat Z a b).hom
      (letterMap f g (wb (Fin.last b)))
      (ih (wb ∘ Fin.castSucc))

/-! ## Extended and all-`false` words

The one-slot insertions of the filtration are words extended by
`Fin.snoc`, and the base insertion is an all-`false` word with one
`true` slot on top.  The lemmas mirror the all-`true` cases of
`WordMap.lean`.
-/

/-- The letter count of an extended word. -/
theorem popCount_snoc {n : ℕ} (w : Fin n → Bool) (y : Bool) :
    popCount (Fin.snoc w y) = popCount w + (bif y then 1 else 0) := by
  rw [popCount_succ,
    show (Fin.snoc w y : Fin (n + 1) → Bool) ∘ Fin.castSucc = w from
      Fin.snoc_comp_castSucc,
    Fin.snoc_last]

/-- The all-`false` word has no `true` letters. -/
theorem popCount_const_false (n : ℕ) :
    popCount (fun _ : Fin n => false) = 0 := by
  simp [popCount]

/-- The word power of a `false`-extended word tensors a `Y`. -/
theorem wordPow_snoc_false [Category.{v} A] [MonoidalCategory A]
    (X Y : A) (n : ℕ) (w : Fin n → Bool) :
    wordPow X Y (n + 1) (Fin.snoc w false) = wordPow X Y n w ⊗ Y := by
  rw [wordPow_succ,
    show (Fin.snoc w false : Fin (n + 1) → Bool) ∘ Fin.castSucc = w
      from Fin.snoc_comp_castSucc,
    Fin.snoc_last]
  rfl

/-- The word power of a `true`-extended word tensors an `X`. -/
theorem wordPow_snoc_true [Category.{v} A] [MonoidalCategory A]
    (X Y : A) (n : ℕ) (w : Fin n → Bool) :
    wordPow X Y (n + 1) (Fin.snoc w true) = wordPow X Y n w ⊗ X := by
  rw [wordPow_succ,
    show (Fin.snoc w true : Fin (n + 1) → Bool) ∘ Fin.castSucc = w
      from Fin.snoc_comp_castSucc,
    Fin.snoc_last]
  rfl

/-- The word map of a `false`-extended word tensors a `g`. -/
theorem wordMap_snoc_false
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) (n : ℕ)
    (w : Fin n → Bool) :
    wordMap f g (n + 1) (Fin.snoc w false) =
      eqToHom (wordPow_snoc_false U V n w) ≫
        (wordMap f g n w ⊗ₘ g) :=
  wordMap_split_false f g n (Fin.snoc w false) w
    Fin.snoc_comp_castSucc (Fin.snoc_last ..)
    (wordPow_snoc_false U V n w)

/-- The word map of a `true`-extended word tensors an `f`. -/
theorem wordMap_snoc_true
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) (n : ℕ)
    (w : Fin n → Bool) :
    wordMap f g (n + 1) (Fin.snoc w true) =
      eqToHom (wordPow_snoc_true U V n w) ≫
        (wordMap f g n w ⊗ₘ f) :=
  wordMap_split_true f g n (Fin.snoc w true) w
    Fin.snoc_comp_castSucc (Fin.snoc_last ..)
    (wordPow_snoc_true U V n w)

/-- An all-`false` word power is a pure power of `Y`. -/
theorem wordPow_const_false [Category.{v} A] [MonoidalCategory A]
    (X Y : A) :
    ∀ n : ℕ, wordPow X Y n (fun _ => false) = tensorPow A Y n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show wordPow X Y n (fun _ => false) ⊗ Y = tensorPow A Y n ⊗ Y
    rw [ih]

/-- An `eqToHom` pulls out of the first factor of a tensor.  Stated
at general objects. -/
private theorem eqToHom_tensor_pull [Category.{v} A] [MonoidalCategory A]
    {P P' Q R S : A} (h : P = P')
    (k : P' ⟶ Q) (l : R ⟶ S) :
    (eqToHom h ≫ k) ⊗ₘ l =
      eqToHom (congrArg (· ⊗ R) h) ≫ (k ⊗ₘ l) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.id_comp]

/-- On an all-`false` word the word map is the pure power of `g`. -/
theorem wordMap_const_false
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) :
    ∀ n : ℕ,
      wordMap f g n (fun _ => false) =
        eqToHom (wordPow_const_false U V n) ≫ tensorPowMap g n := by
  intro n
  induction n with
  | zero =>
    exact (Category.id_comp _).symm
  | succ n ih =>
    show wordMap f g n (fun _ => false) ⊗ₘ g = _
    rw [ih]
    exact eqToHom_tensor_pull (wordPow_const_false U V n) _ _

/-- A tensor with a cast first factor is a left whiskering.  Stated
at general objects and applied by `exact`, so the defeq-mismatched
arities never enter a rewrite. -/
private theorem cast_tensor_to_whiskerLeft [Category.{v} A] [MonoidalCategory A]
    {P Q R S : A} (h : P = Q)
    (H : Q ⊗ R = P ⊗ R) (l : R ⟶ S) :
    eqToHom H ≫ (eqToHom h ⊗ₘ l) = Q ◁ l := by
  subst h
  rw [show H = rfl from rfl, eqToHom_refl, eqToHom_refl,
    Category.id_comp, MonoidalCategory.id_tensorHom]

/-! ## Concatenation at the level of images -/

section Image

/-- Rewriting the morphism inside an image subobject.  Stated as a
congruence, so the image's instance argument transports with the
equality. -/
private theorem imageSubobject_congr [Category.{v} A] [HasImages A]
    {X B : A} {f g : X ⟶ B}
    (h : f = g) : imageSubobject f = imageSubobject g := by
  subst h
  rfl

/-- **Concatenation of word-map images**: the tensor of two word
maps followed by the target concatenation has the same image as
the word map of the appended word — the concatenation square
`wordMap_append` up to the isomorphism `wordPowConcatIso` of the
sources. -/
theorem imageSubobject_wordMap_concat
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    [HasEqualizers A] [HasImages A]
    (f : U ⟶ Z) (g : V ⟶ Z)
    {a b : ℕ} (wa : Fin a → Bool) (wb : Fin b → Bool) :
    imageSubobject ((wordMap f g a wa ⊗ₘ wordMap f g b wb) ≫
        (tensorPowConcat Z a b).hom) =
      imageSubobject (wordMap f g (a + b) (wordAppend wa wb)) :=
  ((imageSubobject_congr (wordMap_append f g wa b wb)).symm).trans
    (imageSubobject_iso_comp _ _)

end Image

/-! ## The subobject toolkit

Factoring through subobjects in an abelian category: epi descent
(`factors_of_epi_comp`, the monomorphism half of the
kernel–cokernel duality), the kernel and image conversions, and
the composite-kernel chase `kernelSubobject_comp_le_of_cover` — the
kernel of `u ≫ v` is covered by the kernel of `u` together with
any `b` whose image under `u` covers the kernel of `v`.  This is
the extension `0 ⟶ ker u ⟶ ker (u ≫ v) ⟶ ker v` of the mixed
filtration, phrased through a pullback of the covering
epimorphism.
-/

section Toolkit

/-- **Epi descent for factorisations**: a morphism factors through
a subobject as soon as its composite with an epimorphism does.
The subobject's arrow is the kernel of its cokernel, so the
factorisation is `Abelian.monoLift`. -/
theorem factors_of_epi_comp [Category.{v} A] [Abelian A]
    {P K B : A} (S : Subobject B)
    (e : P ⟶ K) [Epi e] (k : K ⟶ B) (h : S.Factors (e ≫ k)) :
    S.Factors k := by
  have hz : k ≫ cokernel.π S.arrow = 0 := by
    rw [← cancel_epi e, comp_zero, ← Category.assoc,
      ← Subobject.factorThru_arrow S (e ≫ k) h, Category.assoc,
      cokernel.condition, comp_zero]
  exact (Subobject.factors_iff S k).mpr
    ⟨Abelian.monoLift S.arrow k hz, Abelian.monoLift_comp S.arrow k hz⟩

/-- A subobject containing a kernel factors the kernel's arrow. -/
theorem factors_kernel_ι_of_le [Category.{v} A] [Abelian A]
    {X Y : A} {p : X ⟶ Y}
    {S : Subobject X} (h : kernelSubobject p ≤ S) :
    S.Factors (kernel.ι p) :=
  Subobject.factors_of_le _ h
    (kernelSubobject_factors p _ (kernel.condition p))

/-- A subobject factoring a kernel's arrow contains the kernel. -/
theorem kernelSubobject_le_of_factors [Category.{v} A] [Abelian A]
    {X Y : A} {p : X ⟶ Y}
    {S : Subobject X} (h : S.Factors (kernel.ι p)) :
    kernelSubobject p ≤ S := by
  refine Subobject.le_of_comm
    ((kernelSubobjectIso p).hom ≫ S.factorThru (kernel.ι p) h) ?_
  rw [Category.assoc, Subobject.factorThru_arrow,
    kernelSubobject_arrow]

/-- A subobject factoring a morphism contains its image. -/
theorem imageSubobject_le_of_factors [Category.{v} A] [Abelian A]
    {X B : A} {f : X ⟶ B}
    {S : Subobject B} (h : S.Factors f) :
    imageSubobject f ≤ S :=
  imageSubobject_le f (S.factorThru f h)
    (Subobject.factorThru_arrow S f h)

/-- The image of a morphism factors it. -/
theorem factors_self_imageSubobject [Category.{v} A] [Abelian A]
    {X B : A} (f : X ⟶ B) :
    (imageSubobject f).Factors f :=
  (Subobject.factors_iff _ _).mpr
    ⟨factorThruImageSubobject f, imageSubobject_arrow_comp f⟩

/-- Rewriting the morphism inside a kernel subobject.  Stated as a
congruence, so the kernel's instance argument transports with the
equality. -/
private theorem kernelSubobject_congr [Category.{v} A] [Abelian A]
    {X Y : A} {f g : X ⟶ Y}
    (h : f = g) : kernelSubobject f = kernelSubobject g := by
  subst h
  rfl

/-- **The composite-kernel chase**: if the image of `b ≫ u` covers
the kernel of `v`, then the kernel of `u ≫ v` is covered by the
kernel of `u` together with the image of `b`.  The kernel arrow of
`u ≫ v`, pushed into `Y`, factors through the cover; pulling the
covering epimorphism back splits the kernel arrow, up to an
epimorphism, into a summand through `ker u` and a summand through
`b`. -/
theorem kernelSubobject_comp_le_of_cover [Category.{v} A] [Abelian A]
    {X Y T B : A}
    (u : X ⟶ Y) (v : Y ⟶ T) (b : B ⟶ X)
    (hv : kernelSubobject v ≤ imageSubobject (b ≫ u)) :
    kernelSubobject (u ≫ v) ≤
      kernelSubobject u ⊔ imageSubobject b := by
  have hku : (kernel.ι (u ≫ v) ≫ u) ≫ v = 0 := by
    rw [Category.assoc, kernel.condition]
  have hfac : (imageSubobject (b ≫ u)).Factors
      (kernel.ι (u ≫ v) ≫ u) :=
    Subobject.factors_of_le _ hv (kernelSubobject_factors v _ hku)
  obtain ⟨t, htw⟩ : ∃ t' : kernel (u ≫ v) ⟶
        (imageSubobject (b ≫ u) : A),
      t' ≫ (imageSubobject (b ≫ u)).arrow = kernel.ι (u ≫ v) ≫ u :=
    ⟨_, Subobject.factorThru_arrow _ _ hfac⟩
  obtain ⟨q, hq_epi, hqw⟩ : ∃ q' : B ⟶ (imageSubobject (b ≫ u) : A),
      Epi q' ∧ q' ≫ (imageSubobject (b ≫ u)).arrow = b ≫ u :=
    ⟨factorThruImageSubobject (b ≫ u), inferInstance,
      imageSubobject_arrow_comp (b ≫ u)⟩
  haveI := hq_epi
  refine kernelSubobject_le_of_factors
    (factors_of_epi_comp _ (pullback.fst t q)
      (kernel.ι (u ≫ v)) ?_)
  have hd : (pullback.fst t q ≫ kernel.ι (u ≫ v) -
      pullback.snd t q ≫ b) ≫ u = 0 := by
    calc (pullback.fst t q ≫ kernel.ι (u ≫ v) -
          pullback.snd t q ≫ b) ≫ u
        = pullback.fst t q ≫ (kernel.ι (u ≫ v) ≫ u) -
            pullback.snd t q ≫ (b ≫ u) := by
          rw [Preadditive.sub_comp, Category.assoc, Category.assoc]
      _ = pullback.fst t q ≫
            (t ≫ (imageSubobject (b ≫ u)).arrow) -
            pullback.snd t q ≫
              (q ≫ (imageSubobject (b ≫ u)).arrow) := by
          rw [htw, hqw]
      _ = (pullback.fst t q ≫ t - pullback.snd t q ≫ q) ≫
            (imageSubobject (b ≫ u)).arrow := by
          rw [Preadditive.sub_comp, Category.assoc, Category.assoc]
      _ = 0 := by rw [pullback.condition, sub_self, zero_comp]
  have hsum : pullback.fst t q ≫ kernel.ι (u ≫ v) =
      (pullback.fst t q ≫ kernel.ι (u ≫ v) -
        pullback.snd t q ≫ b) + pullback.snd t q ≫ b :=
    (sub_add_cancel _ _).symm
  rw [hsum]
  exact Subobject.factors_add _ _
    (Subobject.sup_factors_of_factors_left
      (kernelSubobject_factors u _ hd))
    (Subobject.sup_factors_of_factors_right
      (Subobject.factors_of_factors_right _
        (factors_self_imageSubobject b)))

end Toolkit

/-! ## Whiskered epimorphisms and kernels

Whiskering preserves epimorphisms and kernels because tensoring is
exact in a rigid category (`TensorExact.lean`).
-/

section Rigid

/-- Right whiskering preserves epimorphisms. -/
theorem epi_whiskerRight_of_epi
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    {X Y : A} (p : X ⟶ Y) [Epi p]
    (W : A) : Epi (p ▷ W) := by
  haveI : PreservesColimitsOfSize.{0, 0} (tensorRight W) :=
    preservesSmallestColimits_of_preservesColimits _
  exact (tensorRight W).map_epi p

/-- Left whiskering preserves epimorphisms. -/
theorem epi_whiskerLeft_of_epi
    [Category.{v} A] [MonoidalCategory A] [RigidCategory A]
    (W : A) {X Y : A} (p : X ⟶ Y)
    [Epi p] : Epi (W ◁ p) := by
  haveI : PreservesColimitsOfSize.{0, 0} (tensorLeft W) :=
    preservesSmallestColimits_of_preservesColimits _
  exact (tensorLeft W).map_epi p

end Rigid

section WhiskerKernel

/-- The kernel arrow of a right-whiskered morphism factors through
the whiskered kernel arrow, because right tensoring preserves
kernels. -/
private theorem exists_kernel_ι_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [RigidCategory A]
    {X Y : A} (p : X ⟶ Y)
    (W : A) :
    ∃ e : kernel (p ▷ W) ⟶ kernel p ⊗ W,
      kernel.ι (p ▷ W) = e ≫ (kernel.ι p ▷ W) := by
  haveI : PreservesLimitsOfSize.{0, 0} (tensorRight W) :=
    preservesSmallestLimits_of_preservesLimits _
  exact ⟨(PreservesKernel.iso (tensorRight W) p).inv,
    (PreservesKernel.iso_inv_ι (tensorRight W) p).symm⟩

/-- The kernel arrow of a left-whiskered morphism factors through
the whiskered kernel arrow, because left tensoring preserves
kernels. -/
private theorem exists_kernel_ι_whiskerLeft
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [RigidCategory A]
    (W : A) {X Y : A}
    (p : X ⟶ Y) :
    ∃ e : kernel (W ◁ p) ⟶ W ⊗ kernel p,
      kernel.ι (W ◁ p) = e ≫ (W ◁ kernel.ι p) := by
  haveI : PreservesLimitsOfSize.{0, 0} (tensorLeft W) :=
    preservesSmallestLimits_of_preservesLimits _
  exact ⟨(PreservesKernel.iso (tensorLeft W) p).inv,
    (PreservesKernel.iso_inv_ι (tensorLeft W) p).symm⟩

/-- A subobject factoring the whiskered kernel arrow factors the
kernel arrow of the right-whiskered morphism. -/
theorem factors_kernel_ι_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [RigidCategory A]
    {X Y : A} (p : X ⟶ Y) {W : A}
    {S : Subobject (X ⊗ W)} (h : S.Factors (kernel.ι p ▷ W)) :
    S.Factors (kernel.ι (p ▷ W)) := by
  obtain ⟨e, he⟩ := exists_kernel_ι_whiskerRight p W
  rw [he]
  exact Subobject.factors_of_factors_right e h

/-- A subobject factoring the whiskered kernel arrow factors the
kernel arrow of the left-whiskered morphism. -/
theorem factors_kernel_ι_whiskerLeft
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [RigidCategory A]
    {W X Y : A} (p : X ⟶ Y)
    {S : Subobject (W ⊗ X)} (h : S.Factors (W ◁ kernel.ι p)) :
    S.Factors (kernel.ι (W ◁ p)) := by
  obtain ⟨e, he⟩ := exists_kernel_ι_whiskerLeft W p
  rw [he]
  exact Subobject.factors_of_factors_right e h

/-- **The kernel of a right-whiskered morphism** is covered by the
image of the whiskered kernel arrow. -/
theorem kernelSubobject_whiskerRight_le
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [RigidCategory A]
    {X Y : A} (p : X ⟶ Y)
    (W : A) :
    kernelSubobject (p ▷ W) ≤ imageSubobject (kernel.ι p ▷ W) :=
  kernelSubobject_le_of_factors
    (factors_kernel_ι_whiskerRight p
      (factors_self_imageSubobject _))

/-- Factoring through an image is stable under right whiskering. -/
theorem factors_imageSubobject_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [Abelian A] [RigidCategory A]
    {X B C' : A}
    {f : X ⟶ B} {c : C' ⟶ B}
    (h : (imageSubobject c).Factors f) (W : A) :
    (imageSubobject (c ▷ W)).Factors (f ▷ W) := by
  haveI : Epi (factorThruImageSubobject c ▷ W) :=
    epi_whiskerRight_of_epi (factorThruImageSubobject c) W
  have harrow : (imageSubobject (c ▷ W)).Factors
      ((imageSubobject c).arrow ▷ W) := by
    refine factors_of_epi_comp _
      (factorThruImageSubobject c ▷ W) _ ?_
    have hc : (factorThruImageSubobject c ▷ W) ≫
        ((imageSubobject c).arrow ▷ W) = c ▷ W := by
      rw [← MonoidalCategory.comp_whiskerRight,
        imageSubobject_arrow_comp]
    rw [hc]
    exact factors_self_imageSubobject _
  have hf : f ▷ W =
      ((imageSubobject c).factorThru f h ▷ W) ≫
        ((imageSubobject c).arrow ▷ W) := by
    rw [← MonoidalCategory.comp_whiskerRight,
      Subobject.factorThru_arrow]
  rw [hf]
  exact Subobject.factors_of_factors_right _ harrow

/-- Factoring through an image is stable under left whiskering. -/
theorem factors_imageSubobject_whiskerLeft
    [Category.{v} A] [MonoidalCategory A] [Abelian A] [RigidCategory A]
    {X B C' : A}
    {f : X ⟶ B} {c : C' ⟶ B}
    (h : (imageSubobject c).Factors f) (W : A) :
    (imageSubobject (W ◁ c)).Factors (W ◁ f) := by
  haveI : Epi (W ◁ factorThruImageSubobject c) :=
    epi_whiskerLeft_of_epi W (factorThruImageSubobject c)
  have harrow : (imageSubobject (W ◁ c)).Factors
      (W ◁ (imageSubobject c).arrow) := by
    refine factors_of_epi_comp _
      (W ◁ factorThruImageSubobject c) _ ?_
    have hc : (W ◁ factorThruImageSubobject c) ≫
        (W ◁ (imageSubobject c).arrow) = W ◁ c := by
      rw [← MonoidalCategory.whiskerLeft_comp,
        imageSubobject_arrow_comp]
    rw [hc]
    exact factors_self_imageSubobject _
  have hf : W ◁ f =
      (W ◁ (imageSubobject c).factorThru f h) ≫
        (W ◁ (imageSubobject c).arrow) := by
    rw [← MonoidalCategory.whiskerLeft_comp,
      Subobject.factorThru_arrow]
  rw [hf]
  exact Subobject.factors_of_factors_right _ harrow

/-! ## The two-factor kernel -/

/-- **The kernel of a tensor product of an epimorphism and a
morphism** is covered by the two one-slot kernel insertions: the
whiskered kernels of the factors.  The route is the factorisation
`p₁ ⊗ₘ p₂ = (p₁ ▷ Z₂) ≫ (W₁ ◁ p₂)`: the kernel of the second
factor is covered by the image of `Z₁ ◁ kernel.ι p₂` under the
first — the whisker exchange against the epimorphism
`p₁ ▷ kernel p₂` — and the composite-kernel chase concludes. -/
theorem kernelSubobject_tensorHom_le
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [RigidCategory A]
    {Z₁ W₁ Z₂ W₂ : A}
    (p₁ : Z₁ ⟶ W₁) (p₂ : Z₂ ⟶ W₂) [Epi p₁] :
    kernelSubobject (p₁ ⊗ₘ p₂) ≤
      imageSubobject (kernel.ι p₁ ▷ Z₂) ⊔
        imageSubobject (Z₁ ◁ kernel.ι p₂) := by
  have hv : kernelSubobject (W₁ ◁ p₂) ≤
      imageSubobject ((Z₁ ◁ kernel.ι p₂) ≫ (p₁ ▷ Z₂)) := by
    haveI : Epi (p₁ ▷ kernel p₂) := epi_whiskerRight_of_epi p₁ _
    refine kernelSubobject_le_of_factors
      (factors_kernel_ι_whiskerLeft p₂
        (factors_of_epi_comp _ (p₁ ▷ kernel p₂) _ ?_))
    rw [← whisker_exchange p₁ (kernel.ι p₂)]
    exact factors_self_imageSubobject _
  calc kernelSubobject (p₁ ⊗ₘ p₂)
      = kernelSubobject ((p₁ ▷ Z₂) ≫ (W₁ ◁ p₂)) :=
        kernelSubobject_congr (MonoidalCategory.tensorHom_def p₁ p₂)
    _ ≤ kernelSubobject (p₁ ▷ Z₂) ⊔
          imageSubobject (Z₁ ◁ kernel.ι p₂) :=
        kernelSubobject_comp_le_of_cover (p₁ ▷ Z₂) (W₁ ◁ p₂)
          (Z₁ ◁ kernel.ι p₂) hv
    _ ≤ imageSubobject (kernel.ι p₁ ▷ Z₂) ⊔
          imageSubobject (Z₁ ◁ kernel.ι p₂) :=
        sup_le_sup_right (kernelSubobject_whiskerRight_le p₁ Z₂) _

/-- The two one-slot kernel insertions land in the kernel of the
tensor product; no epimorphism hypothesis is needed. -/
theorem sup_le_kernelSubobject_tensorHom
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A]
    {Z₁ W₁ Z₂ W₂ : A}
    (p₁ : Z₁ ⟶ W₁) (p₂ : Z₂ ⟶ W₂) :
    imageSubobject (kernel.ι p₁ ▷ Z₂) ⊔
        imageSubobject (Z₁ ◁ kernel.ι p₂) ≤
      kernelSubobject (p₁ ⊗ₘ p₂) := by
  refine sup_le
    (imageSubobject_le_of_factors
      (kernelSubobject_factors _ _ ?_))
    (imageSubobject_le_of_factors
      (kernelSubobject_factors _ _ ?_))
  · rw [MonoidalCategory.tensorHom_def, ← Category.assoc,
      ← MonoidalCategory.comp_whiskerRight, kernel.condition,
      MonoidalPreadditive.zero_whiskerRight, zero_comp]
  · rw [MonoidalCategory.tensorHom_def', ← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp, kernel.condition,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp]

/-- **The kernel of a tensor product of an epimorphism and a
morphism**, exactly: it is the join of the images of the two
one-slot kernel insertions. -/
theorem kernelSubobject_tensorHom
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [RigidCategory A]
    {Z₁ W₁ Z₂ W₂ : A}
    (p₁ : Z₁ ⟶ W₁) (p₂ : Z₂ ⟶ W₂) [Epi p₁] :
    kernelSubobject (p₁ ⊗ₘ p₂) =
      imageSubobject (kernel.ι p₁ ▷ Z₂) ⊔
        imageSubobject (Z₁ ◁ kernel.ι p₂) :=
  le_antisymm (kernelSubobject_tensorHom_le p₁ p₂)
    (sup_le_kernelSubobject_tensorHom p₁ p₂)

/-! ## The iterated kernel

The kernel of `π ^ ⊗ m` is covered by the one-slot insertions: the
word maps of `ι` and `𝟙 Z` at words with exactly one `true`
letter.  The induction along
`tensorPowMap π (m + 1) = tensorPowMap π m ⊗ₘ π` transports the
inductive cover through the tensor structure, so the cover is kept
as a single morphism out of the biproduct of the one-slot word
powers (`oneSlotCover`); the `Finset.sup` phrasing is recovered at
the end.
-/

attribute [local instance] Abelian.hasFiniteBiproducts

/-- **The one-slot cover**: the fold of all word maps of `ι` and
`𝟙 Z` with exactly one `ι`-slot, out of the biproduct of their
word powers. -/
noncomputable def oneSlotCover [Category.{v} A] [MonoidalCategory A] [Abelian A]
    {U Z : A} (ι : U ⟶ Z) (m : ℕ) :
    (⨁ fun w : {w : Fin m → Bool // popCount w = 1} =>
        wordPow U Z m w.1) ⟶ tensorPow A Z m :=
  biproduct.desc fun w => wordMap ι (𝟙 Z) m w.1

/-- Each one-slot word map factors through the cover's image. -/
private theorem factors_oneSlotCover
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    {U Z : A} (ι : U ⟶ Z) (m : ℕ)
    (w : Fin m → Bool) (hw : popCount w = 1) :
    (imageSubobject (oneSlotCover ι m)).Factors
      (wordMap ι (𝟙 Z) m w) := by
  have h : wordMap ι (𝟙 Z) m w =
      biproduct.ι
        (fun w' : {w' : Fin m → Bool // popCount w' = 1} =>
          wordPow U Z m w'.1) ⟨w, hw⟩ ≫ oneSlotCover ι m := by
    unfold oneSlotCover
    rw [biproduct.ι_desc]
  rw [h]
  exact Subobject.factors_of_factors_right _
    (factors_self_imageSubobject _)

/-- The cover, decomposed as the sum of its word-map summands. -/
private theorem oneSlotCover_eq_sum
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    {U Z : A} (ι : U ⟶ Z) (m : ℕ) :
    oneSlotCover ι m =
      ∑ w : {w : Fin m → Bool // popCount w = 1},
        biproduct.π
          (fun w' : {w' : Fin m → Bool // popCount w' = 1} =>
            wordPow U Z m w'.1) w ≫ wordMap ι (𝟙 Z) m w.1 := by
  calc oneSlotCover ι m
      = 𝟙 _ ≫ oneSlotCover ι m := (Category.id_comp _).symm
    _ = (∑ w : {w : Fin m → Bool // popCount w = 1},
          biproduct.π _ w ≫ biproduct.ι _ w) ≫ oneSlotCover ι m := by
        rw [biproduct.total]
    _ = ∑ w : {w : Fin m → Bool // popCount w = 1},
          (biproduct.π _ w ≫ biproduct.ι _ w) ≫ oneSlotCover ι m :=
        Preadditive.sum_comp _ _ _
    _ = ∑ w : {w : Fin m → Bool // popCount w = 1},
          biproduct.π _ w ≫ wordMap ι (𝟙 Z) m w.1 :=
        Finset.sum_congr rfl fun w _ => by
          rw [Category.assoc]
          exact congrArg (biproduct.π _ w ≫ ·) (biproduct.ι_desc _ _)

/-- Factoring through a subobject is closed under finite sums. -/
private theorem factors_sum [Category.{v} A] [Abelian A]
    {X B : A} {S : Subobject B}
    {J : Type*} [Fintype J] (g : J → (X ⟶ B))
    (h : ∀ j, S.Factors (g j)) : S.Factors (∑ j, g j) :=
  Finset.sum_induction g S.Factors
    (fun a b ha hb => Subobject.factors_add a b ha hb)
    Subobject.factors_zero (fun j _ => h j)

/-- A morphism equal to a cast composed with a decomposition of a
given morphism.  Stated at general objects and applied by `exact`,
so the defeq-mismatched arities never enter a rewrite. -/
private theorem eq_cast_comp_of [Category.{v} A]
    {N W R : A} (h : N = W)
    (h' : W = N) (D : N ⟶ R) (E : W ⟶ R)
    (hD : D = eqToHom h ≫ E) : E = eqToHom h' ≫ D := by
  subst h
  rw [hD, show h' = rfl from rfl, eqToHom_refl, Category.id_comp,
    Category.id_comp]

/-- The right-whiskered cover factors through the next cover: a
`false` letter joins each word on top, preserving its letter
count. -/
private theorem factors_oneSlotCover_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A]
    {U Z : A}
    (ι : U ⟶ Z) (m : ℕ) :
    (imageSubobject (oneSlotCover ι (m + 1))).Factors
      (oneSlotCover ι m ▷ Z) := by
  rw [oneSlotCover_eq_sum ι m, sum_whiskerRight]
  refine factors_sum _ fun w => ?_
  rw [MonoidalCategory.comp_whiskerRight]
  refine Subobject.factors_of_factors_right _ ?_
  have hbase : (imageSubobject (oneSlotCover ι (m + 1))).Factors
      (wordMap ι (𝟙 Z) (m + 1) (Fin.snoc w.1 false)) := by
    refine factors_oneSlotCover ι (m + 1) _ ?_
    rw [popCount_snoc, w.2]
    rfl
  have hE : (wordMap ι (𝟙 Z) m w.1 ⊗ₘ 𝟙 Z) =
      eqToHom (wordPow_snoc_false U Z m w.1).symm ≫
        wordMap ι (𝟙 Z) (m + 1) (Fin.snoc w.1 false) :=
    eq_cast_comp_of (wordPow_snoc_false U Z m w.1)
      (wordPow_snoc_false U Z m w.1).symm _ _
      (wordMap_snoc_false ι (𝟙 Z) m w.1)
  rw [← MonoidalCategory.tensorHom_id, hE]
  exact Subobject.factors_of_factors_right _ hbase

/-- The base insertion `Z ^ ⊗ m ◁ ι` factors through the next
cover: it is the word map of the all-`false` word with one `true`
letter on top. -/
private theorem factors_whiskerLeft_iota
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    {U Z : A} (ι : U ⟶ Z)
    (m : ℕ) :
    (imageSubobject (oneSlotCover ι (m + 1))).Factors
      (tensorPow A Z m ◁ ι) := by
  have hbase : (imageSubobject (oneSlotCover ι (m + 1))).Factors
      (wordMap ι (𝟙 Z) (m + 1)
        (Fin.snoc (fun _ : Fin m => false) true)) := by
    refine factors_oneSlotCover ι (m + 1) _ ?_
    rw [popCount_snoc, popCount_const_false]
    rfl
  have hM : wordMap ι (𝟙 Z) m (fun _ => false) =
      eqToHom (wordPow_const_false U Z m) := by
    rw [wordMap_const_false, tensorPowMap_id, Category.comp_id]
  have hE : (wordMap ι (𝟙 Z) m (fun _ => false) ⊗ₘ ι) =
      eqToHom (wordPow_snoc_true U Z m (fun _ => false)).symm ≫
        wordMap ι (𝟙 Z) (m + 1)
          (Fin.snoc (fun _ : Fin m => false) true) :=
    eq_cast_comp_of (wordPow_snoc_true U Z m (fun _ => false))
      (wordPow_snoc_true U Z m (fun _ => false)).symm _ _
      (wordMap_snoc_true ι (𝟙 Z) m (fun _ => false))
  have hwhisk : tensorPow A Z m ◁ ι =
      eqToHom (congrArg (· ⊗ U) (wordPow_const_false U Z m).symm) ≫
        (wordMap ι (𝟙 Z) m (fun _ => false) ⊗ₘ ι) := by
    rw [hM]
    exact
      (cast_tensor_to_whiskerLeft (wordPow_const_false U Z m) _ ι).symm
  rw [hwhisk, hE]
  exact Subobject.factors_of_factors_right _
    (Subobject.factors_of_factors_right _ hbase)

/-- **The kernel of a tensor power of an epimorphism, cover
form**: if `ι` covers the kernel of the epimorphism `π`, then the
kernel of `π ^ ⊗ m` is covered by the image of the one-slot
cover. -/
theorem kernelSubobject_tensorPowMap_le_cover
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [RigidCategory A]
    {U Z W : A}
    (ι : U ⟶ Z) (π : Z ⟶ W) [Epi π]
    (hker : kernelSubobject π ≤ imageSubobject ι) :
    ∀ m : ℕ, kernelSubobject (tensorPowMap π m) ≤
      imageSubobject (oneSlotCover ι m) := by
  intro m
  induction m with
  | zero =>
    refine kernelSubobject_le_of_factors ?_
    have h : kernel.ι (tensorPowMap π 0) = 0 := by
      rw [← Category.comp_id (kernel.ι (tensorPowMap π 0))]
      exact kernel.condition (tensorPowMap π 0)
    rw [h]
    exact Subobject.factors_zero
  | succ m ih =>
    haveI : Epi (tensorPowMap π m) := tensorPowMap_epi π m
    refine le_trans
      (kernelSubobject_tensorHom_le (tensorPowMap π m) π)
      (sup_le ?_ ?_)
    · exact imageSubobject_le_of_factors
        (Subobject.factors_of_le _
          (imageSubobject_le_of_factors
            (factors_oneSlotCover_whiskerRight ι m))
          (factors_imageSubobject_whiskerRight
            (factors_kernel_ι_of_le ih) Z))
    · exact imageSubobject_le_of_factors
        (Subobject.factors_of_le _
          (imageSubobject_le_of_factors (factors_whiskerLeft_iota ι m))
          (factors_imageSubobject_whiskerLeft
            (factors_kernel_ι_of_le hker) (tensorPow A Z m)))

/-- **The kernel of a tensor power of an epimorphism**: if `ι`
covers the kernel of the epimorphism `π : Z ⟶ W`, the kernel of
`π ^ ⊗ m` is covered by the join of the images of the word maps of
`ι` and `𝟙 Z` over the words with exactly one `ι`-slot.  The join
is a `Finset.sup`: without well-poweredness the subobject lattice
carries finite joins, and the index is the finite set of one-slot
words. -/
theorem kernelSubobject_tensorPowMap_le
    [Category.{v} A] [MonoidalCategory A] [Abelian A]
    [MonoidalPreadditive A] [RigidCategory A]
    {U Z W : A}
    (ι : U ⟶ Z) (π : Z ⟶ W) [Epi π]
    (hker : kernelSubobject π ≤ imageSubobject ι) (m : ℕ) :
    kernelSubobject (tensorPowMap π m) ≤
      ((Finset.univ.filter
          fun w : Fin m → Bool => popCount w = 1).sup
        fun w => imageSubobject (wordMap ι (𝟙 Z) m w)) := by
  refine le_trans (kernelSubobject_tensorPowMap_le_cover ι π hker m)
    (imageSubobject_le_of_factors ?_)
  rw [oneSlotCover_eq_sum]
  refine factors_sum _ fun w => ?_
  refine Subobject.factors_of_factors_right _ ?_
  refine Subobject.finset_sup_factors ⟨w.1, ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w.2⟩
  · exact factors_self_imageSubobject _

end WhiskerKernel

end RS
