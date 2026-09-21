/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.BiprodPow

/-!
# Word maps of an arbitrary pair of morphisms

`BiprodPow` folds the letterwise biproduct inclusions of `X ⊞ Y`
into the mixed inclusions `mixedInto` and sorts them under the
symmetric-group action.  Its sorting arguments never use that the
letters are biproduct inclusions — only monoidal coherence and
naturality.  This file replays that machinery at two arbitrary
morphisms with a common target, `f : U ⟶ Z` and `g : V ⟶ Z`, in a
monoidal category.

The letterwise fold of `f` and `g` over a word is the word map
`wordMap`.  It is natural in the letters: composing with a
letterwise fold `wordCongrMap` of morphisms of the sources composes
the letters (`wordMap_natural`).  On a sorted word the word map is
the concatenation of the pure powers of `f` and `g`
(`wordMap_standard`), and in a symmetric category every word map,
followed by the action of its sorting permutation, is that sorted
concatenation — up to the isomorphism `wordSortIso` of the source
and an arity transport at the target (`wordMap_sorted`).

The word powers `wordPow`, the letter counts `popCount`, the sorted
words `standardWord`, their structural isomorphism
`standardMixedIso` and the sorting permutations `sortPerm` are
reused from `BiprodPow` unchanged: they depend only on the two
source objects, never on the letter maps.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {A : Type u}

/-! ## Letter maps and the word map -/

/-- The morphism selected by one letter: `f` on a `true` letter and
`g` on a `false` one. -/
def letterMap [Category.{v} A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) :
    (b : Bool) → ((bif b then U else V) ⟶ Z)
  | true => f
  | false => g

/-- **The word map**: the fold of the letter maps of `f` and `g`
over a word, by the recursion of `wordPow`. -/
noncomputable def wordMap
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) :
    (n : ℕ) → (w : Fin n → Bool) →
      (wordPow U V n w ⟶ tensorPow A Z n)
  | 0, _ => 𝟙 (𝟙_ A)
  | n + 1, w =>
      wordMap f g n (w ∘ Fin.castSucc) ⊗ₘ
        letterMap f g (w (Fin.last n))

/-! ## Naturality in the letters -/

/-- The source morphism selected by one letter: `α` on a `true`
letter and `β` on a `false` one. -/
def letterCongr [Category.{v} A] {U : A} {V : A} {U' : A} {V' : A}
    (α : U' ⟶ U) (β : V' ⟶ V) :
    (b : Bool) → ((bif b then U' else V') ⟶ (bif b then U else V))
  | true => α
  | false => β

/-- A letter's congruence map composed with its letter map is the
letter map of the composites. -/
theorem letterCongr_letterMap
    [Category.{v} A] {U : A} {V : A} {Z : A} {U' : A} {V' : A}
    (α : U' ⟶ U) (β : V' ⟶ V)
    (f : U ⟶ Z) (g : V ⟶ Z) (b : Bool) :
    letterCongr α β b ≫ letterMap f g b =
      letterMap (α ≫ f) (β ≫ g) b := by
  cases b <;> rfl

/-- **The letterwise congruence map** between word powers on the
same word: the fold of `α` on the `true` letters and `β` on the
`false` ones, by the recursion of `wordPow`. -/
noncomputable def wordCongrMap
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {U' : A} {V' : A}
    (α : U' ⟶ U) (β : V' ⟶ V) :
    (n : ℕ) → (w : Fin n → Bool) →
      (wordPow U' V' n w ⟶ wordPow U V n w)
  | 0, _ => 𝟙 (𝟙_ A)
  | n + 1, w =>
      wordCongrMap α β n (w ∘ Fin.castSucc) ⊗ₘ
        letterCongr α β (w (Fin.last n))

/-- **Naturality of the word map in the letters**: the letterwise
congruence map composed with the word map of `f` and `g` is the
word map of the composed letters. -/
theorem wordMap_natural
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A} {U' : A}
    {V' : A}
    (α : U' ⟶ U) (β : V' ⟶ V)
    (f : U ⟶ Z) (g : V ⟶ Z) :
    ∀ (n : ℕ) (w : Fin n → Bool),
      wordCongrMap α β n w ≫ wordMap f g n w =
        wordMap (α ≫ f) (β ≫ g) n w := by
  intro n
  induction n with
  | zero => intro w; exact Category.id_comp _
  | succ n ih =>
    intro w
    show (wordCongrMap α β n (w ∘ Fin.castSucc) ⊗ₘ
          letterCongr α β (w (Fin.last n))) ≫
        (wordMap f g n (w ∘ Fin.castSucc) ⊗ₘ
          letterMap f g (w (Fin.last n))) =
      wordMap (α ≫ f) (β ≫ g) n (w ∘ Fin.castSucc) ⊗ₘ
        letterMap (α ≫ f) (β ≫ g) (w (Fin.last n))
    rw [MonoidalCategory.tensorHom_comp_tensorHom,
      ih (w ∘ Fin.castSucc), letterCongr_letterMap]

/-! ## Transport and splitting -/

/-- Transport of `wordMap` along an equality of words. -/
theorem wordMap_congr
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) {n : ℕ}
    {w w' : Fin n → Bool} (h : w = w') :
    wordMap f g n w =
      eqToHom (congrArg (wordPow U V n) h) ≫ wordMap f g n w' := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

/-- Splitting `wordMap` at the last letter, with the recursion's
word and letter replaced by given values. -/
theorem wordMap_split
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) (n : ℕ)
    (w : Fin (n + 1) → Bool) (w' : Fin n → Bool) (b : Bool)
    (hw : w ∘ Fin.castSucc = w') (hb : w (Fin.last n) = b)
    (h : wordPow U V (n + 1) w =
      wordPow U V n w' ⊗ (bif b then U else V)) :
    wordMap f g (n + 1) w =
      eqToHom h ≫ (wordMap f g n w' ⊗ₘ letterMap f g b) := by
  subst hw
  subst hb
  exact (Category.id_comp _).symm

/-- The last-letter split of `wordMap` at a `false` letter, with
the selected object and morphism spelled as `V` and `g`. -/
theorem wordMap_split_false
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) (n : ℕ)
    (w : Fin (n + 1) → Bool) (w' : Fin n → Bool)
    (hw : w ∘ Fin.castSucc = w') (hb : w (Fin.last n) = false)
    (h : wordPow U V (n + 1) w = wordPow U V n w' ⊗ V) :
    wordMap f g (n + 1) w =
      eqToHom h ≫ (wordMap f g n w' ⊗ₘ g) :=
  wordMap_split f g n w w' false hw hb h

/-- The last-letter split of `wordMap` at a `true` letter, with
the selected object and morphism spelled as `U` and `f`. -/
theorem wordMap_split_true
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) (n : ℕ)
    (w : Fin (n + 1) → Bool) (w' : Fin n → Bool)
    (hw : w ∘ Fin.castSucc = w') (hb : w (Fin.last n) = true)
    (h : wordPow U V (n + 1) w = wordPow U V n w' ⊗ U) :
    wordMap f g (n + 1) w =
      eqToHom h ≫ (wordMap f g n w' ⊗ₘ f) :=
  wordMap_split f g n w w' true hw hb h

/-! ## The base-point map

On a sorted word, `wordMap` is the concatenation of the two pure
powers.  The gluing helpers are stated at general objects and
applied by `exact`, so that no tensor-power arity enters the
rewriting.
-/

/-- An `eqToHom` pulls out of the first factor of a tensor.  Stated
at general objects. -/
private theorem eqToHom_tensor_pull [Category.{v} A] [MonoidalCategory A]
    {P P' Q R S : A} (h : P = P')
    (k : P' ⟶ Q) (l : R ⟶ S) :
    (eqToHom h ≫ k) ⊗ₘ l =
      eqToHom (congrArg (· ⊗ R) h) ≫ (k ⊗ₘ l) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.id_comp]

/-- On an all-`true` word the word map is the pure power of `f`. -/
theorem wordMap_const_true
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) :
    ∀ n : ℕ,
      wordMap f g n (fun _ => true) =
        eqToHom (wordPow_const_true U V n) ≫ tensorPowMap f n := by
  intro n
  induction n with
  | zero =>
    exact (Category.id_comp _).symm
  | succ n ih =>
    show wordMap f g n (fun _ => true) ⊗ₘ f = _
    rw [ih]
    exact eqToHom_tensor_pull (wordPow_const_true U V n) _ _

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

/-- Transport along the `p + 0` arity cast composes away against
the pure power of the first letter. -/
private theorem map_pow_cast
    [Category.{v} A] [MonoidalCategory A] {U : A} {Z : A}
    (f : U ⟶ Z) (m : ℕ)
    (H : tensorPow A U m = tensorPow A U (m + 0)) :
    eqToHom H ≫ tensorPowMap f (m + 0) = tensorPowMap f m := by
  rw [show H = rfl from rfl, eqToHom_refl, Category.id_comp]
  rfl

/-- **The base-point map**: on a sorted word, `wordMap` is the
concatenation of the pure powers of the two letter maps. -/
theorem wordMap_standard
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) (p : ℕ) :
    ∀ q : ℕ,
      (standardMixedIso U V p q).inv ≫
          wordMap f g (p + q) (standardWord p q) =
        (tensorPowMap f p ⊗ₘ tensorPowMap g q) ≫
          (tensorPowConcat Z p q).hom := by
  intro q
  induction q with
  | zero =>
    have hkey : eqToHom (wordPow_standard_zero U V p).symm ≫
        wordMap f g (p + 0) (standardWord p 0) =
        tensorPowMap f p := by
      rw [wordMap_congr f g (standardWord_zero p),
        wordMap_const_true f g, eqToHom_trans_assoc,
        eqToHom_trans_assoc]
      exact map_pow_cast f p _
    show ((ρ_ (tensorPow A U p)).hom ≫
          eqToHom (wordPow_standard_zero U V p).symm) ≫
        wordMap f g (p + 0) (standardWord p 0) =
      (tensorPowMap f p ⊗ₘ 𝟙 (𝟙_ A)) ≫
        (ρ_ (tensorPow A Z p)).hom
    rw [Category.assoc, hkey]
    exact (unit_tensor_unitor (tensorPowMap f p)).symm
  | succ q ih =>
    have hstep : wordPow U V (p + q + 1) (standardWord p (q + 1)) =
        wordPow U V (p + q) (standardWord p q) ⊗ V :=
      wordPow_standard_succ U V p q
    have hsplit := wordMap_split_false f g (p + q)
      (standardWord p (q + 1)) (standardWord p q)
      (standardWord_castSucc p q) (standardWord_last p q) hstep
    refine (cast_cancel_glue hstep.symm hstep
      ((α_ (tensorPow A U p) (tensorPow A V q) V).inv ≫
        ((standardMixedIso U V p q).inv ▷ V))
      (wordMap f g (p + q + 1) (standardWord p (q + 1)))
      (wordMap f g (p + q) (standardWord p q) ⊗ₘ g)
      hsplit).trans ?_
    erw [Category.assoc]
    exact concat_step_glue (standardMixedIso U V p q).inv
      (wordMap f g (p + q) (standardWord p q))
      (tensorPowMap f p) (tensorPowMap g q)
      (tensorPowConcat Z p q).hom g ih

/-! ## Sorting

Every word map is the base-point map of its sorted form, up to the
symmetric-group action.  The bubbling infrastructure —
`permMor_ofSplit`, `putBelow`, `insertTop_full` and
`putBelow_concat` — is reused from `BiprodPow`; the gluing helpers
below replicate its private steps at general letters.
-/

section Symmetric

/-- A whiskered arity transport is the transport one arity up.
Stated with both transports explicit, so it applies by `exact`
wherever the endpoints agree definitionally. -/
private theorem cast_whiskerRight_eq [Category.{v} A] [MonoidalCategory A]
    (W : A) {P Q : A} (h : P = Q)
    (h' : P ⊗ W = Q ⊗ W) :
    eqToHom h ▷ W = eqToHom h' := by
  subst h
  rw [show h' = rfl from rfl, eqToHom_refl, eqToHom_refl,
    MonoidalCategory.id_whiskerRight]

/-- Splitting the first factor off a composite tensored against a
morphism.  Stated at general objects. -/
private theorem tensor_split_first [Category.{v} A] [MonoidalCategory A]
    {P Q R S T : A} (a : P ⟶ Q)
    (v : Q ⟶ R) (k : S ⟶ T) :
    (a ≫ v) ⊗ₘ k = (a ▷ S) ≫ (v ⊗ₘ k) := by
  calc (a ≫ v) ⊗ₘ k = (a ≫ v) ⊗ₘ (𝟙 S ≫ k) := by
        rw [Category.id_comp]
    _ = (a ⊗ₘ 𝟙 S) ≫ (v ⊗ₘ k) :=
        (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm
    _ = (a ▷ S) ≫ (v ⊗ₘ k) := by
        rw [MonoidalCategory.tensorHom_id]

/-- Splitting the last factor off a composite tensored against a
morphism.  Stated at general objects. -/
private theorem tensor_split_last [Category.{v} A] [MonoidalCategory A]
    {P Q R S T : A} (v : P ⟶ Q)
    (E : Q ⟶ R) (k : S ⟶ T) :
    (v ≫ E) ⊗ₘ k = (v ⊗ₘ k) ≫ (E ▷ T) := by
  calc (v ≫ E) ⊗ₘ k = (v ≫ E) ⊗ₘ (k ≫ 𝟙 T) := by
        rw [Category.comp_id]
    _ = (v ⊗ₘ k) ≫ (E ⊗ₘ 𝟙 T) :=
        (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm
    _ = (v ⊗ₘ k) ≫ (E ▷ T) := by
        rw [MonoidalCategory.tensorHom_id]

/-- A tensor absorbed into the second factor through a left
whiskering.  Stated at general objects. -/
private theorem tensor_then_whiskerLeft [Category.{v} A] [MonoidalCategory A]
    {P Q S T W : A} (a : P ⟶ Q)
    (h : S ⟶ T) (k : T ⟶ W) :
    (a ⊗ₘ h) ≫ (Q ◁ k) = a ⊗ₘ (h ≫ k) := by
  rw [← MonoidalCategory.id_tensorHom Q k,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- A left whiskering absorbed into the second factor of a tensor.
Stated at general objects. -/
private theorem whiskerLeft_then_tensor [Category.{v} A] [MonoidalCategory A]
    {P Q S T W : A} (a : P ⟶ Q)
    (h : S ⟶ T) (k : T ⟶ W) :
    (P ◁ h) ≫ (a ⊗ₘ k) = a ⊗ₘ (h ≫ k) := by
  rw [← MonoidalCategory.id_tensorHom P h,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- `tensor_then_whiskerLeft` against a tail. -/
private theorem tensor_then_whiskerLeft_assoc
    [Category.{v} A] [MonoidalCategory A]
    {P Q S T W R : A}
    (a : P ⟶ Q) (h : S ⟶ T) (k : T ⟶ W) (rest : Q ⊗ W ⟶ R) :
    (a ⊗ₘ h) ≫ (Q ◁ k) ≫ rest = (a ⊗ₘ (h ≫ k)) ≫ rest := by
  rw [← Category.assoc, tensor_then_whiskerLeft]

/-- `whiskerLeft_then_tensor` against a tail. -/
private theorem whiskerLeft_then_tensor_assoc
    [Category.{v} A] [MonoidalCategory A]
    {P Q S T W R : A}
    (a : P ⟶ Q) (h : S ⟶ T) (k : T ⟶ W) (rest : Q ⊗ W ⟶ R) :
    (P ◁ h) ≫ (a ⊗ₘ k) ≫ rest = (a ⊗ₘ (h ≫ k)) ≫ rest := by
  rw [← Category.assoc, whiskerLeft_then_tensor]

/-- One whiskered concatenation stage: reassociate and take the
next stage. -/
private theorem concat_whisker_step [Category.{v} A] [MonoidalCategory A]
    (T : A) (p m : ℕ) :
    ((tensorPowConcat T p m).hom ▷ T) =
      (α_ (tensorPow A T p) (tensorPow A T m) T).hom ≫
        (tensorPowConcat T p (m + 1)).hom :=
  (Iso.hom_inv_id_assoc
    (α_ (tensorPow A T p) (tensorPow A T m) T) _).symm

/-- One whiskered concatenation stage against the insertion cycle:
reassociate, insert within the second block, and concatenate. -/
private theorem concat_whisker_insert
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (T : A) (p m : ℕ) :
    ((tensorPowConcat T p m).hom ▷ T) ≫ insertTop T (p + m) m =
      (α_ (tensorPow A T p) (tensorPow A T m) T).hom ≫
        ((tensorPow A T p ◁ insertTop T m m) ≫
          (tensorPowConcat T p (m + 1)).hom) := by
  have h1 := tensorPowConcat_insertTop T p m m le_rfl
  calc ((tensorPowConcat T p m).hom ▷ T) ≫ insertTop T (p + m) m
      = ((α_ (tensorPow A T p) (tensorPow A T m) T).hom ≫
          (tensorPowConcat T p (m + 1)).hom) ≫
          insertTop T (p + m) m := by
            rw [concat_whisker_step]
            exact rfl
    _ = (α_ (tensorPow A T p) (tensorPow A T m) T).hom ≫
          ((tensorPowConcat T p (m + 1)).hom ≫
            insertTop T (p + m) m) := Category.assoc _ _ _
    _ = (α_ (tensorPow A T p) (tensorPow A T m) T).hom ≫
          ((tensorPow A T p ◁ insertTop T m m) ≫
            (tensorPowConcat T p (m + 1)).hom) :=
        congrArg
          (fun t => (α_ (tensorPow A T p) (tensorPow A T m) T).hom ≫ t)
          h1

/-- A tensor absorbed through a right whiskering.  Stated at
general objects. -/
private theorem tensor_then_whiskerRight [Category.{v} A] [MonoidalCategory A]
    {P Q R S T : A}
    (a : P ⟶ Q) (u : Q ⟶ R) (k : S ⟶ T) :
    (a ⊗ₘ k) ≫ (u ▷ T) = (a ≫ u) ⊗ₘ k := by
  rw [← MonoidalCategory.tensorHom_id u T,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- Reassociating a parenthesised three-chain against a tail. -/
private theorem assoc₃ [Category.{v} A]
    {P Q R S T : A} (a : P ⟶ Q) (b : Q ⟶ R)
    (c : R ⟶ S) (d : S ⟶ T) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

/-- The false-branch gluing at general objects: tensoring a
four-chain with a letter splits it around the reassociation. -/
private theorem sorted_false_glue [Category.{v} A] [MonoidalCategory A]
    {W P Q P' Q' N N' S T : A}
    (a : W ⟶ P ⊗ Q) (v₁ : P ⟶ P') (v₂ : Q ⟶ Q')
    (c : P' ⊗ Q' ⟶ N) (E : N ⟶ N') (k : S ⟶ T) :
    (a ≫ (v₁ ⊗ₘ v₂) ≫ c ≫ E) ⊗ₘ k =
      (a ▷ S) ≫ (α_ P Q S).hom ≫ (v₁ ⊗ₘ (v₂ ⊗ₘ k)) ≫
        (α_ P' Q' T).inv ≫ (c ▷ T) ≫ (E ▷ T) := by
  rw [tensor_split_first, tensor_split_last,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.associator_conjugation]
  simp only [Category.assoc]

/-- Arity transport commutes with the insertion cycle. -/
private theorem insertTop_cast
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (T : A) (a b k : ℕ) (hab : a = b)
    (H : tensorPow A T a = tensorPow A T b) :
    (eqToHom H ▷ T) ≫ insertTop T b k =
      insertTop T a k ≫ (eqToHom H ▷ T) := by
  subst hab
  erw [show H = rfl from rfl, eqToHom_refl,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  exact (Category.comp_id _).symm

/-- An arity transport composed with a whiskered one is the joint
transport. -/
private theorem cast_then_cast_whisker [Category.{v} A] [MonoidalCategory A]
    (T : A) {a b n : ℕ}
    (hab : a = b + 1) (hbn : b = n)
    (H₁ : tensorPow A T a = tensorPow A T (b + 1))
    (H₂ : tensorPow A T b = tensorPow A T n)
    (H₃ : tensorPow A T a = tensorPow A T (n + 1)) :
    eqToHom H₁ ≫ (eqToHom H₂ ▷ T) = eqToHom H₃ := by
  subst hbn
  subst hab
  erw [show H₁ = rfl from rfl, show H₂ = rfl from rfl,
    show H₃ = rfl from rfl, eqToHom_refl, eqToHom_refl,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  rfl

/-- **Sorting one appended `true` letter**: the base-point map with
one more `f` in the last slot, bubbled down past the whole `g`
block, is the base-point map of the grown `f` block — up to
braiding the appended factor past the `V` power on the mixed side
and the arity transport `(p + 1) + m = p + (m + 1)` at the
target. -/
private theorem letter_insert_true
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    [SymmetricCategory A]
    (f : U ⟶ Z) (g : V ⟶ Z)
    (p m : ℕ) :
    (((tensorPowMap f p ⊗ₘ tensorPowMap g m) ≫
        (tensorPowConcat Z p m).hom) ⊗ₘ f) ≫
      insertTop Z (p + m) m =
    (α_ (tensorPow A U p) (tensorPow A V m) U).hom ≫
      (tensorPow A U p ◁ (β_ (tensorPow A V m) U).hom) ≫
      (α_ (tensorPow A U p) U (tensorPow A V m)).inv ≫
      (tensorPowMap f (p + 1) ⊗ₘ tensorPowMap g m) ≫
      (tensorPowConcat Z (p + 1) m).hom ≫
      eqToHom (congrArg (tensorPow A Z)
        (Nat.succ_add_eq_add_succ p m)) := by
  rw [tensor_split_last]
  repeat' erw [Category.assoc]
  rw [concat_whisker_insert, insertTop_full,
    MonoidalCategory.associator_naturality_assoc,
    tensor_then_whiskerLeft_assoc,
    BraidedCategory.braiding_naturality_assoc,
    ← whiskerLeft_then_tensor_assoc, ← tensor_then_whiskerLeft_assoc,
    putBelow_concat, MonoidalCategory.associator_inv_naturality_assoc]
  exact rfl

/-- Regrouping a flat seven-chain into the packaged form.  Stated
at general objects. -/
private theorem false_final_shape [Category.{v} A]
    {W₀ W₁ P R₁ R₂ R₃ R₄ R₅ : A}
    (a : W₀ ⟶ W₁) (b : W₁ ⟶ P) (c : P ⟶ R₁) (t : R₁ ⟶ R₂)
    (ai : R₂ ⟶ R₃) (cw : R₃ ⟶ R₄) (e : R₄ ⟶ R₅) :
    a ≫ b ≫ c ≫ t ≫ ai ≫ cw ≫ e =
      (a ≫ b ≫ c) ≫ t ≫ (ai ≫ cw) ≫ e := by
  simp only [Category.assoc]

/-- **The sorting square grows by a `false` letter**: the appended
`V` slot joins the top of the `g` block and nothing is bubbled. -/
private theorem sorted_step_false
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    [SymmetricCategory A]
    (f : U ⟶ Z) (g : V ⟶ Z) {n : ℕ}
    (w : Fin (n + 1) → Bool) (p m : ℕ)
    (hpm : p + m = n) (hq1 : p + (m + 1) = n + 1)
    (e' : wordPow U V n (w ∘ Fin.castSucc) ≅
      tensorPow A U p ⊗ tensorPow A V m)
    (hobj : wordPow U V (n + 1) w =
      wordPow U V n (w ∘ Fin.castSucc) ⊗ V)
    (hb : w (Fin.last n) = false)
    (hperm : permMor Z (n + 1) (sortPerm w) =
      permMor Z n (sortPerm (w ∘ Fin.castSucc)) ▷ Z)
    (hsq' : wordMap f g n (w ∘ Fin.castSucc) ≫
        permMor Z n (sortPerm (w ∘ Fin.castSucc)) =
      e'.hom ≫
        (tensorPowMap f p ⊗ₘ tensorPowMap g m) ≫
        (tensorPowConcat Z p m).hom ≫
        eqToHom (congrArg (tensorPow A Z) hpm)) :
    wordMap f g (n + 1) w ≫ permMor Z (n + 1) (sortPerm w) =
      (eqToIso hobj ≪≫ whiskerRightIso e' V ≪≫
          α_ (tensorPow A U p) (tensorPow A V m) V).hom ≫
        (tensorPowMap f p ⊗ₘ tensorPowMap g (m + 1)) ≫
        (tensorPowConcat Z p (m + 1)).hom ≫
        eqToHom (congrArg (tensorPow A Z) hq1) := by
  have hsplit := wordMap_split_false f g n w (w ∘ Fin.castSucc)
    rfl hb hobj
  have hcast := cast_whiskerRight_eq Z
    (congrArg (tensorPow A Z) hpm)
    (congrArg (tensorPow A Z) hq1)
  have h1 : wordMap f g (n + 1) w ≫
        permMor Z (n + 1) (sortPerm w)
      = (eqToHom hobj ≫
          (wordMap f g n (w ∘ Fin.castSucc) ⊗ₘ g)) ≫
          (permMor Z n (sortPerm (w ∘ Fin.castSucc)) ▷ Z) := by
        rw [hsplit, hperm]
        exact rfl
  have h2 : (eqToHom hobj ≫
          (wordMap f g n (w ∘ Fin.castSucc) ⊗ₘ g)) ≫
          (permMor Z n (sortPerm (w ∘ Fin.castSucc)) ▷ Z)
      = eqToHom hobj ≫
          ((wordMap f g n (w ∘ Fin.castSucc) ⊗ₘ g) ≫
          (permMor Z n (sortPerm (w ∘ Fin.castSucc)) ▷ Z)) :=
    Category.assoc _ _ _
  have h3 : eqToHom hobj ≫
          ((wordMap f g n (w ∘ Fin.castSucc) ⊗ₘ g) ≫
          (permMor Z n (sortPerm (w ∘ Fin.castSucc)) ▷ Z))
      = eqToHom hobj ≫
          ((wordMap f g n (w ∘ Fin.castSucc) ≫
            permMor Z n (sortPerm (w ∘ Fin.castSucc))) ⊗ₘ g) :=
    congrArg (fun t => eqToHom hobj ≫ t)
      (tensor_then_whiskerRight _ _ _)
  have h4 : eqToHom hobj ≫
          ((wordMap f g n (w ∘ Fin.castSucc) ≫
            permMor Z n (sortPerm (w ∘ Fin.castSucc))) ⊗ₘ g)
      = eqToHom hobj ≫
          ((e'.hom ≫
            (tensorPowMap f p ⊗ₘ tensorPowMap g m) ≫
            (tensorPowConcat Z p m).hom ≫
            eqToHom (congrArg (tensorPow A Z) hpm)) ⊗ₘ g) := by
    rw [hsq']
  have h5 : eqToHom hobj ≫
          ((e'.hom ≫
            (tensorPowMap f p ⊗ₘ tensorPowMap g m) ≫
            (tensorPowConcat Z p m).hom ≫
            eqToHom (congrArg (tensorPow A Z) hpm)) ⊗ₘ g)
      = eqToHom hobj ≫
          ((e'.hom ▷ V) ≫
            (α_ (tensorPow A U p) (tensorPow A V m) V).hom ≫
            (tensorPowMap f p ⊗ₘ (tensorPowMap g m ⊗ₘ g)) ≫
            (α_ (tensorPow A Z p) (tensorPow A Z m) Z).inv ≫
            ((tensorPowConcat Z p m).hom ▷ Z) ≫
            (eqToHom (congrArg (tensorPow A Z) hpm) ▷ Z)) :=
    congrArg (fun t => eqToHom hobj ≫ t)
      (sorted_false_glue e'.hom _ _ _ _ _)
  have h6 : eqToHom hobj ≫
          ((e'.hom ▷ V) ≫
            (α_ (tensorPow A U p) (tensorPow A V m) V).hom ≫
            (tensorPowMap f p ⊗ₘ (tensorPowMap g m ⊗ₘ g)) ≫
            (α_ (tensorPow A Z p) (tensorPow A Z m) Z).inv ≫
            ((tensorPowConcat Z p m).hom ▷ Z) ≫
            (eqToHom (congrArg (tensorPow A Z) hpm) ▷ Z))
      = eqToHom hobj ≫
          ((e'.hom ▷ V) ≫
            (α_ (tensorPow A U p) (tensorPow A V m) V).hom ≫
            (tensorPowMap f p ⊗ₘ (tensorPowMap g m ⊗ₘ g)) ≫
            (α_ (tensorPow A Z p) (tensorPow A Z m) Z).inv ≫
            ((tensorPowConcat Z p m).hom ▷ Z) ≫
            eqToHom (congrArg (tensorPow A Z) hq1)) := by
    rw [hcast]
    exact rfl
  have h7 : eqToHom hobj ≫
          ((e'.hom ▷ V) ≫
            (α_ (tensorPow A U p) (tensorPow A V m) V).hom ≫
            (tensorPowMap f p ⊗ₘ (tensorPowMap g m ⊗ₘ g)) ≫
            (α_ (tensorPow A Z p) (tensorPow A Z m) Z).inv ≫
            ((tensorPowConcat Z p m).hom ▷ Z) ≫
            eqToHom (congrArg (tensorPow A Z) hq1))
      = (eqToIso hobj ≪≫ whiskerRightIso e' V ≪≫
          α_ (tensorPow A U p) (tensorPow A V m) V).hom ≫
        (tensorPowMap f p ⊗ₘ tensorPowMap g (m + 1)) ≫
        (tensorPowConcat Z p (m + 1)).hom ≫
        eqToHom (congrArg (tensorPow A Z) hq1) :=
      false_final_shape _ _ _ _ _ _ _
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans
    (h6.trans h7)))))

/-- Regrouping the true-branch chain into the packaged form.
Stated at general objects. -/
private theorem true_final_shape [Category.{v} A]
    {W₀ W₁ P R₀ R₁ R₂ R₃ R₄ R₅ R₆ : A}
    (a : W₀ ⟶ W₁) (b : W₁ ⟶ P) (c : P ⟶ R₀) (d : R₀ ⟶ R₁)
    (e : R₁ ⟶ R₂) (t : R₂ ⟶ R₃) (cw : R₃ ⟶ R₄) (e₁ : R₄ ⟶ R₅)
    (e₂ : R₅ ⟶ R₆) :
    a ≫ ((b ≫ (c ≫ d ≫ e ≫ t ≫ cw ≫ e₁)) ≫ e₂) =
      (a ≫ b ≫ c ≫ d ≫ e) ≫ t ≫ cw ≫ e₁ ≫ e₂ := by
  simp only [Category.assoc]

/-- **The sorting square grows by a `true` letter**: the appended
`U` slot is bubbled down past the whole `g` block onto the top of
the `f` block. -/
private theorem sorted_step_true
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    [SymmetricCategory A]
    (f : U ⟶ Z) (g : V ⟶ Z) {n : ℕ}
    (w : Fin (n + 1) → Bool) (p m : ℕ)
    (hpm : p + m = n) (hm : n - p = m)
    (hq1 : p + 1 + m = n + 1)
    (e' : wordPow U V n (w ∘ Fin.castSucc) ≅
      tensorPow A U p ⊗ tensorPow A V m)
    (hobj : wordPow U V (n + 1) w =
      wordPow U V n (w ∘ Fin.castSucc) ⊗ U)
    (hb : w (Fin.last n) = true)
    (hperm : permMor Z (n + 1) (sortPerm w) =
      (permMor Z n (sortPerm (w ∘ Fin.castSucc)) ▷ Z) ≫
        insertTop Z n (n - p))
    (hsq' : wordMap f g n (w ∘ Fin.castSucc) ≫
        permMor Z n (sortPerm (w ∘ Fin.castSucc)) =
      e'.hom ≫
        (tensorPowMap f p ⊗ₘ tensorPowMap g m) ≫
        (tensorPowConcat Z p m).hom ≫
        eqToHom (congrArg (tensorPow A Z) hpm)) :
    wordMap f g (n + 1) w ≫ permMor Z (n + 1) (sortPerm w) =
      (eqToIso hobj ≪≫ whiskerRightIso e' U ≪≫
          α_ (tensorPow A U p) (tensorPow A V m) U ≪≫
          whiskerLeftIso (tensorPow A U p)
            (β_ (tensorPow A V m) U) ≪≫
          (α_ (tensorPow A U p) U (tensorPow A V m)).symm).hom ≫
        (tensorPowMap f (p + 1) ⊗ₘ tensorPowMap g m) ≫
        (tensorPowConcat Z (p + 1) m).hom ≫
        eqToHom (congrArg (tensorPow A Z) hq1) := by
  have hsplit := wordMap_split_true f g n w (w ∘ Fin.castSucc)
    rfl hb hobj
  have hmerge := cast_then_cast_whisker Z
    (a := p + 1 + m) (b := p + m) (n := n)
    (by omega) hpm
    (congrArg (tensorPow A Z) (Nat.succ_add_eq_add_succ p m))
    (congrArg (tensorPow A Z) hpm)
    (congrArg (tensorPow A Z) hq1)
  have h1 : wordMap f g (n + 1) w ≫
        permMor Z (n + 1) (sortPerm w)
      = (eqToHom hobj ≫
          (wordMap f g n (w ∘ Fin.castSucc) ⊗ₘ f)) ≫
          ((permMor Z n (sortPerm (w ∘ Fin.castSucc)) ▷ Z) ≫
            insertTop Z n (n - p)) := by
    rw [hsplit, hperm]
    exact rfl
  refine (h1.trans ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => eqToHom hobj ≫ t)
    (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      (t ≫ insertTop Z n (n - p)))
    (tensor_then_whiskerRight _ _ _)).trans ?_
  refine (?_ :
    eqToHom hobj ≫
      (((wordMap f g n (w ∘ Fin.castSucc) ≫
        permMor Z n (sortPerm (w ∘ Fin.castSucc))) ⊗ₘ f) ≫
        insertTop Z n (n - p)) = _)
  rw [hsq']
  refine (congrArg
    (fun v => eqToHom hobj ≫
      ((v ⊗ₘ f) ≫ insertTop Z n (n - p)))
    (assoc₃ e'.hom _ _ _).symm).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      (t ≫ insertTop Z n (n - p)))
    (tensor_split_last _ _ _)).trans ?_
  refine (congrArg (fun t => eqToHom hobj ≫ t)
    (Category.assoc _ _ _)).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      (((e'.hom ≫
        (tensorPowMap f p ⊗ₘ tensorPowMap g m) ≫
        (tensorPowConcat Z p m).hom) ⊗ₘ f) ≫ t))
    (insertTop_cast Z (p + m) n (n - p) hpm
      (congrArg (tensorPow A Z) hpm))).trans ?_
  refine (congrArg
    (fun k => eqToHom hobj ≫
      (((e'.hom ≫
        (tensorPowMap f p ⊗ₘ tensorPowMap g m) ≫
        (tensorPowConcat Z p m).hom) ⊗ₘ f) ≫
        (insertTop Z (p + m) k ≫
          (eqToHom (congrArg (tensorPow A Z) hpm) ▷ Z))))
    hm).trans ?_
  refine (congrArg (fun t => eqToHom hobj ≫ t)
    (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      ((t ≫ insertTop Z (p + m) m) ≫
        (eqToHom (congrArg (tensorPow A Z) hpm) ▷ Z)))
    (tensor_split_first e'.hom _ _)).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      (t ≫ (eqToHom (congrArg (tensorPow A Z) hpm) ▷ Z)))
    (Category.assoc _ _ _)).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      (((e'.hom ▷ U) ≫ t) ≫
        (eqToHom (congrArg (tensorPow A Z) hpm) ▷ Z)))
    (letter_insert_true f g p m)).trans ?_
  refine (true_final_shape (eqToHom hobj) (e'.hom ▷ U)
    (α_ (tensorPow A U p) (tensorPow A V m) U).hom
    (tensorPow A U p ◁ (β_ (tensorPow A V m) U).hom)
    (α_ (tensorPow A U p) U (tensorPow A V m)).inv
    (tensorPowMap f (p + 1) ⊗ₘ tensorPowMap g m)
    (tensorPowConcat Z (p + 1) m).hom
    (eqToHom (congrArg (tensorPow A Z)
      (Nat.succ_add_eq_add_succ p m)))
    (eqToHom (congrArg (tensorPow A Z) hpm) ▷ Z)).trans ?_
  exact congrArg
    (fun s => (eqToHom hobj ≫ (e'.hom ▷ U) ≫
        (α_ (tensorPow A U p) (tensorPow A V m) U).hom ≫
        (tensorPow A U p ◁ (β_ (tensorPow A V m) U).hom) ≫
        (α_ (tensorPow A U p) U (tensorPow A V m)).inv) ≫
      (tensorPowMap f (p + 1) ⊗ₘ tensorPowMap g m) ≫
      (tensorPowConcat Z (p + 1) m).hom ≫ s)
    hmerge

/-- Append a definitionally trivial transport to a three-step
factorisation. -/
private theorem comp_cast_end₃ [Category.{v} A]
    {P Q R S : A} {k : P ⟶ S}
    {g₁ : P ⟶ Q} {g₂ : Q ⟶ R} {g₃ : R ⟶ S} (H : S = S)
    (hkg : k = g₁ ≫ g₂ ≫ g₃) :
    k = g₁ ≫ g₂ ≫ g₃ ≫ eqToHom H := by
  rw [show H = rfl from rfl, eqToHom_refl, Category.comp_id, hkg]

/-- Renaming the block sizes of a sorting square: the data and the
square transport along equalities of the two sizes. -/
private theorem sorted_pack
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    (f : U ⟶ Z) (g : V ⟶ Z) {n : ℕ}
    {W : A} (mi : W ⟶ tensorPow A Z n) (p q pc qc : ℕ)
    (hp : p = pc) (hq : q = qc) (hpq : p + q = n)
    (hpcqc : pc + qc = n)
    (e : W ≅ tensorPow A U p ⊗ tensorPow A V q)
    (hsq : mi = e.hom ≫
      (tensorPowMap f p ⊗ₘ tensorPowMap g q) ≫
      (tensorPowConcat Z p q).hom ≫
      eqToHom (congrArg (tensorPow A Z) hpq)) :
    ∃ e' : W ≅ tensorPow A U pc ⊗ tensorPow A V qc,
      mi = e'.hom ≫
        (tensorPowMap f pc ⊗ₘ tensorPowMap g qc) ≫
        (tensorPowConcat Z pc qc).hom ≫
        eqToHom (congrArg (tensorPow A Z) hpcqc) := by
  subst hp
  subst hq
  exact ⟨e, hsq⟩

/-- **The sorting lemma**: every word map is a permuted base-point
map.  For each word `w` there is an isomorphism of the word power
with `U ^ ⊗ popCount w ⊗ V ^ ⊗ (n − popCount w)` under which
`wordMap f g`, followed by the action of `sortPerm w`, is the
concatenation of the pure powers of `f` and `g`, transported along
`popCount w + (n − popCount w) = n` at the target. -/
theorem wordMap_sorted_exists
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    [SymmetricCategory A]
    (f : U ⟶ Z) (g : V ⟶ Z) :
    ∀ (n : ℕ) (w : Fin n → Bool),
      ∃ e : wordPow U V n w ≅
          tensorPow A U (popCount w) ⊗
            tensorPow A V (n - popCount w),
        wordMap f g n w ≫ permMor Z n (sortPerm w) =
          e.hom ≫
            (tensorPowMap f (popCount w) ⊗ₘ
              tensorPowMap g (n - popCount w)) ≫
            (tensorPowConcat Z (popCount w) (n - popCount w)).hom ≫
            eqToHom (congrArg (tensorPow A Z)
              (Nat.add_sub_cancel' (popCount_le w))) := by
  intro n
  induction n with
  | zero =>
    intro w
    refine sorted_pack f g
      (wordMap f g 0 w ≫ permMor Z 0 (sortPerm w))
      0 0 (popCount w) (0 - popCount w) (popCount_nil w).symm
      (by rw [popCount_nil]) rfl
      (Nat.add_sub_cancel' (popCount_le w))
      (ρ_ (𝟙_ A)).symm ?_
    have hz : (𝟙 (𝟙_ A) ≫ 𝟙 (𝟙_ A) : 𝟙_ A ⟶ 𝟙_ A) =
        (ρ_ (𝟙_ A)).inv ≫ (𝟙 (𝟙_ A) ⊗ₘ 𝟙 (𝟙_ A)) ≫
          (ρ_ (𝟙_ A)).hom := by
      rw [MonoidalCategory.id_tensorHom_id, Category.id_comp,
        Category.id_comp, Iso.inv_hom_id]
    refine comp_cast_end₃ _ ?_
    exact hz
  | succ n ih =>
    intro w
    obtain ⟨e', hsq'⟩ := ih (w ∘ Fin.castSucc)
    have hple := popCount_le (w ∘ Fin.castSucc)
    cases hb : w (Fin.last n) with
    | false =>
      have hpw : popCount w = popCount (w ∘ Fin.castSucc) := by
        rw [popCount_succ, hb]
        rfl
      have hobj : wordPow U V (n + 1) w =
          wordPow U V n (w ∘ Fin.castSucc) ⊗ V := by
        rw [wordPow_succ, hb]
        rfl
      have hperm : permMor Z (n + 1) (sortPerm w) =
          permMor Z n (sortPerm (w ∘ Fin.castSucc)) ▷ Z := by
        rw [sortPerm_succ, hb, Bool.cond_false, permMor_ofSplit,
          show ((Fin.last n : Fin (n + 1)) : ℕ) = n from rfl,
          Nat.sub_self, insertTop_zero]
        exact Category.comp_id _
      have hq1 : popCount (w ∘ Fin.castSucc) +
          (n - popCount (w ∘ Fin.castSucc) + 1) = n + 1 := by
        omega
      refine sorted_pack f g
        (wordMap f g (n + 1) w ≫
          permMor Z (n + 1) (sortPerm w))
        (popCount (w ∘ Fin.castSucc))
        (n - popCount (w ∘ Fin.castSucc) + 1)
        (popCount w) (n + 1 - popCount w) hpw.symm (by omega) hq1
        (Nat.add_sub_cancel' (popCount_le w)) _
        (sorted_step_false f g w (popCount (w ∘ Fin.castSucc))
          (n - popCount (w ∘ Fin.castSucc))
          (Nat.add_sub_cancel' hple) hq1 e' hobj hb hperm hsq')
    | true =>
      have hpw : popCount w = popCount (w ∘ Fin.castSucc) + 1 := by
        rw [popCount_succ, hb]
        rfl
      have hobj : wordPow U V (n + 1) w =
          wordPow U V n (w ∘ Fin.castSucc) ⊗ U := by
        rw [wordPow_succ, hb]
        rfl
      have hperm : permMor Z (n + 1) (sortPerm w) =
          (permMor Z n (sortPerm (w ∘ Fin.castSucc)) ▷ Z) ≫
            insertTop Z n
              (n - popCount (w ∘ Fin.castSucc)) := by
        rw [sortPerm_succ, hb, Bool.cond_true, permMor_ofSplit]
      have hq1 : popCount (w ∘ Fin.castSucc) + 1 +
          (n - popCount (w ∘ Fin.castSucc)) = n + 1 := by
        omega
      refine sorted_pack f g
        (wordMap f g (n + 1) w ≫
          permMor Z (n + 1) (sortPerm w))
        (popCount (w ∘ Fin.castSucc) + 1)
        (n - popCount (w ∘ Fin.castSucc))
        (popCount w) (n + 1 - popCount w) hpw.symm (by omega) hq1
        (Nat.add_sub_cancel' (popCount_le w)) _
        (sorted_step_true f g w (popCount (w ∘ Fin.castSucc))
          (n - popCount (w ∘ Fin.castSucc))
          (Nat.add_sub_cancel' hple) rfl hq1 e' hobj hb hperm hsq')

/-- **The sorting isomorphism**, chosen once and for all from the
sorting lemma: `wordPow U V n w` against the sorted concatenation
of pure powers. -/
noncomputable def wordSortIso
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    [SymmetricCategory A]
    (f : U ⟶ Z) (g : V ⟶ Z) (n : ℕ)
    (w : Fin n → Bool) :
    wordPow U V n w ≅
      tensorPow A U (popCount w) ⊗ tensorPow A V (n - popCount w) :=
  (wordMap_sorted_exists f g n w).choose

/-- **The sorting square**, for the chosen isomorphism
`wordSortIso`: the word map of `f` and `g`, followed by the action
of the sorting permutation, is the concatenation of the pure powers
of `f` and `g`, up to `wordSortIso` at the source and the arity
transport at the target. -/
theorem wordMap_sorted
    [Category.{v} A] [MonoidalCategory A] {U : A} {V : A} {Z : A}
    [SymmetricCategory A]
    (f : U ⟶ Z) (g : V ⟶ Z) (n : ℕ)
    (w : Fin n → Bool) :
    wordMap f g n w ≫ permMor Z n (sortPerm w) =
      (wordSortIso f g n w).hom ≫
        (tensorPowMap f (popCount w) ⊗ₘ
          tensorPowMap g (n - popCount w)) ≫
        (tensorPowConcat Z (popCount w) (n - popCount w)).hom ≫
        eqToHom (congrArg (tensorPow A Z)
          (Nat.add_sub_cancel' (popCount_le w))) :=
  (wordMap_sorted_exists f g n w).choose_spec

end Symmetric

end RS
