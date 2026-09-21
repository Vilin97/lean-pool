/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.MixedConc
import LeanPool.RegtsSevenster.RS.Classical.Deligne.PermNat

/-!
# Binomial expansion of a tensor power of a biproduct

`(X ⊞ Y) ^ ⊗ n` decomposes into `2 ^ n` mixed words: for each
`w : Fin n → Bool` the word power `wordPow X Y n w` tensors an `X`
for each `true` letter and a `Y` for each `false` one, in slot
order.  The letterwise biproduct inclusions and projections fold to
`mixedInto` and `mixedFrom`, which exhibit the word powers as a
biproduct decomposition of the full power: same-word round trips
are identities, different-word round trips vanish, and the sum of
all `mixedFrom ≫ mixedInto` is the identity of `(X ⊞ Y) ^ ⊗ n`.

The sorted words are the `standardWord`s — all `X`s below all
`Y`s — whose word power is `X ^ ⊗ p ⊗ Y ^ ⊗ q` up to the
structural isomorphism `standardMixedIso`, and on which `mixedInto`
is the concatenation of the two pure-power inclusions.  The sorting
lemma closes the file: every word is a sorted word up to the
symmetric-group action — `mixedInto` for `w`, followed by the
action of `sortPerm w`, is the base-point inclusion at
`(popCount w, n − popCount w)`, up to an isomorphism of the source
and an arity transport `eqToHom` at the target.

`mixedPow` in `RS/Definitions.lean` already names the dual-mixed
power of a rigid object, so the word-indexed power here is called
`wordPow` instead.
-/

namespace RS

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u

variable {A : Type u}

/-! ## Word powers -/

/-- **The word power**: tensor an `X` for each `true` letter of `w`
and a `Y` for each `false` one, by the recursion of `tensorPow`. -/
def wordPow [Category.{v} A] [MonoidalCategory A]
    (X Y : A) : (n : ℕ) → (Fin n → Bool) → A
  | 0, _ => 𝟙_ A
  | n + 1, w =>
      wordPow X Y n (w ∘ Fin.castSucc) ⊗
        (bif w (Fin.last n) then X else Y)

/-- The defining recursion of `wordPow`: one more letter tensors
the selected object on the right. -/
theorem wordPow_succ [Category.{v} A] [MonoidalCategory A]
    (X Y : A) (n : ℕ) (w : Fin (n + 1) → Bool) :
    wordPow X Y (n + 1) w =
      wordPow X Y n (w ∘ Fin.castSucc) ⊗
        (bif w (Fin.last n) then X else Y) := rfl

/-! ## Letterwise inclusions and projections -/

section Biprod

/-- The biproduct inclusion selected by one letter. -/
noncomputable def letterInto
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X Y : A) :
    (b : Bool) → ((bif b then X else Y) ⟶ X ⊞ Y)
  | true => biprod.inl
  | false => biprod.inr

/-- The biproduct projection selected by one letter. -/
noncomputable def letterFrom
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X Y : A) :
    (b : Bool) → (X ⊞ Y ⟶ (bif b then X else Y))
  | true => biprod.fst
  | false => biprod.snd

/-- A letter's round trip through the biproduct is the identity. -/
theorem letterInto_letterFrom
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X Y : A) (b : Bool) :
    letterInto X Y b ≫ letterFrom X Y b = 𝟙 _ := by
  cases b
  · exact biprod.inr_snd
  · exact biprod.inl_fst

/-- Different letters' round trips vanish. -/
theorem letterInto_letterFrom_ne
    [Category.{v} A] [Preadditive A] [HasBinaryBiproducts A]
    (X Y : A) {b b' : Bool}
    (hbb' : b ≠ b') :
    letterInto X Y b ≫ letterFrom X Y b' = 0 := by
  cases b <;> cases b'
  · exact absurd rfl hbb'
  · exact biprod.inr_fst
  · exact biprod.inl_snd
  · exact absurd rfl hbb'

/-- **The inclusion of a word power** into the tensor power of the
biproduct: the fold of the letterwise inclusions, by the recursion
of `wordPow`. -/
noncomputable def mixedInto
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : A) : (n : ℕ) → (w : Fin n → Bool) →
    (wordPow X Y n w ⟶ tensorPow A (X ⊞ Y) n)
  | 0, _ => 𝟙 (𝟙_ A)
  | n + 1, w =>
      mixedInto X Y n (w ∘ Fin.castSucc) ⊗ₘ
        letterInto X Y (w (Fin.last n))

/-- **The projection onto a word power** from the tensor power of
the biproduct: the fold of the letterwise projections. -/
noncomputable def mixedFrom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : A) : (n : ℕ) → (w : Fin n → Bool) →
    (tensorPow A (X ⊞ Y) n ⟶ wordPow X Y n w)
  | 0, _ => 𝟙 (𝟙_ A)
  | n + 1, w =>
      mixedFrom X Y n (w ∘ Fin.castSucc) ⊗ₘ
        letterFrom X Y (w (Fin.last n))

/-! ## Round trips

Each round-trip computation happens factorwise.  The helpers are
stated at general objects and applied by `exact`, so that no
tensor-power arity enters the rewriting.
-/

/-- Sections tensor to a section.  Stated at general objects. -/
private theorem tensor_split_id [Category.{v} A] [MonoidalCategory A]
    {P Q R S : A} (f : P ⟶ Q) (g : Q ⟶ P)
    (h : R ⟶ S) (k : S ⟶ R) (hfg : f ≫ g = 𝟙 P) (hhk : h ≫ k = 𝟙 R) :
    (f ⊗ₘ h) ≫ (g ⊗ₘ k) = 𝟙 (P ⊗ R) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, hfg, hhk,
    MonoidalCategory.id_tensorHom_id]

/-- Two words of positive length differ in the last letter or in
the rest. -/
private theorem word_ne_cases {n : ℕ} {w w' : Fin (n + 1) → Bool}
    (hww' : w ≠ w') :
    w ∘ Fin.castSucc ≠ w' ∘ Fin.castSucc ∨
      w (Fin.last n) ≠ w' (Fin.last n) := by
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  refine hww' (funext fun i => ?_)
  induction i using Fin.lastCases with
  | last => exact h2
  | cast j => exact congrFun h1 j

section MonPre

/-- A vanishing first factor kills the tensor.  Stated at general
objects. -/
private theorem tensor_split_zero_fst
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A]
    {P Q R S T U : A}
    (f : P ⟶ Q) (g : Q ⟶ R) (h : S ⟶ T) (k : T ⟶ U)
    (hfg : f ≫ g = 0) : (f ⊗ₘ h) ≫ (g ⊗ₘ k) = 0 := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, hfg,
    MonoidalPreadditive.zero_tensor]

/-- A vanishing second factor kills the tensor.  Stated at general
objects. -/
private theorem tensor_split_zero_snd
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A]
    {P Q R S T U : A}
    (f : P ⟶ Q) (g : Q ⟶ R) (h : S ⟶ T) (k : T ⟶ U)
    (hhk : h ≫ k = 0) : (f ⊗ₘ h) ≫ (g ⊗ₘ k) = 0 := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, hhk,
    MonoidalPreadditive.tensor_zero]

/-! ### Completeness

Summed over all words, the round trips through the word powers
decompose the identity of `(X ⊞ Y) ^ ⊗ n`.  The words of length
`n + 1` are reindexed by `Fin.snocEquiv` as pairs of a last letter
and a shorter word; the letter sum is `biprod.total` and the word
sum is the inductive hypothesis.
-/

/-- One word's round trip through the full power, split into the
shorter word's round trip and the last letter's. -/
private theorem fromInto_snoc
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : A) (n : ℕ) (w' : Fin n → Bool)
    (b : Bool) :
    mixedFrom X Y (n + 1) (Fin.snoc w' b) ≫
        mixedInto X Y (n + 1) (Fin.snoc w' b) =
      (mixedFrom X Y n w' ≫ mixedInto X Y n w') ⊗ₘ
        (letterFrom X Y b ≫ letterInto X Y b) := by
  have hw : (Fin.snoc w' b : Fin (n + 1) → Bool) ∘ Fin.castSucc = w' :=
    Fin.snoc_comp_castSucc
  have hb : (Fin.snoc w' b : Fin (n + 1) → Bool) (Fin.last n) = b :=
    Fin.snoc_last ..
  have hww : mixedFrom X Y n (Fin.snoc w' b ∘ Fin.castSucc) ≫
      mixedInto X Y n (Fin.snoc w' b ∘ Fin.castSucc) =
    mixedFrom X Y n w' ≫ mixedInto X Y n w' := by rw [hw]
  have hbb : letterFrom X Y
        ((Fin.snoc w' b : Fin (n + 1) → Bool) (Fin.last n)) ≫
      letterInto X Y
        ((Fin.snoc w' b : Fin (n + 1) → Bool) (Fin.last n)) =
    letterFrom X Y b ≫ letterInto X Y b := by rw [hb]
  rw [← hww, ← hbb]
  exact MonoidalCategory.tensorHom_comp_tensorHom (C := A) _ _ _ _

/-- **Completeness of the word decomposition**: the round trips
through the word powers sum to the identity of the full power. -/
theorem sum_mixedFrom_mixedInto
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A] [MonoidalPreadditive A]
    (X Y : A) :
    ∀ n : ℕ,
      ∑ w : Fin n → Bool, mixedFrom X Y n w ≫ mixedInto X Y n w =
        𝟙 (tensorPow A (X ⊞ Y) n) := by
  intro n
  induction n with
  | zero =>
    rw [Fintype.sum_unique]
    exact Category.id_comp _
  | succ n ih =>
    have e1 : (∑ w : Fin (n + 1) → Bool,
          mixedFrom X Y (n + 1) w ≫ mixedInto X Y (n + 1) w) =
        ∑ p : Bool × (Fin n → Bool),
          mixedFrom X Y (n + 1) (Fin.snoc p.2 p.1) ≫
            mixedInto X Y (n + 1) (Fin.snoc p.2 p.1) :=
      (Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (n + 1) => Bool)
        (fun w => mixedFrom X Y (n + 1) w ≫
          mixedInto X Y (n + 1) w)).symm
    have e2 : (∑ p : Bool × (Fin n → Bool),
          mixedFrom X Y (n + 1) (Fin.snoc p.2 p.1) ≫
            mixedInto X Y (n + 1) (Fin.snoc p.2 p.1)) =
        ∑ p : Bool × (Fin n → Bool),
          ((mixedFrom X Y n p.2 ≫ mixedInto X Y n p.2) ⊗ₘ
              (letterFrom X Y p.1 ≫ letterInto X Y p.1) :
            tensorPow A (X ⊞ Y) (n + 1) ⟶
              tensorPow A (X ⊞ Y) (n + 1)) :=
      Finset.sum_congr rfl fun p _ => fromInto_snoc X Y n p.2 p.1
    have e3 : (∑ p : Bool × (Fin n → Bool),
          ((mixedFrom X Y n p.2 ≫ mixedInto X Y n p.2) ⊗ₘ
              (letterFrom X Y p.1 ≫ letterInto X Y p.1) :
            tensorPow A (X ⊞ Y) (n + 1) ⟶
              tensorPow A (X ⊞ Y) (n + 1))) =
        ∑ b : Bool, ∑ w' : Fin n → Bool,
          ((mixedFrom X Y n w' ≫ mixedInto X Y n w') ⊗ₘ
              (letterFrom X Y b ≫ letterInto X Y b) :
            tensorPow A (X ⊞ Y) (n + 1) ⟶
              tensorPow A (X ⊞ Y) (n + 1)) :=
      Fintype.sum_prod_type _
    have e4 : ∀ b : Bool,
        (∑ w' : Fin n → Bool,
          ((mixedFrom X Y n w' ≫ mixedInto X Y n w') ⊗ₘ
              (letterFrom X Y b ≫ letterInto X Y b) :
            tensorPow A (X ⊞ Y) (n + 1) ⟶
              tensorPow A (X ⊞ Y) (n + 1))) =
        𝟙 (tensorPow A (X ⊞ Y) n) ⊗ₘ
          (letterFrom X Y b ≫ letterInto X Y b) := by
      intro b
      rw [← ih]
      exact (sum_tensor _ _ _).symm
    have e5 : (∑ b : Bool, ∑ w' : Fin n → Bool,
          ((mixedFrom X Y n w' ≫ mixedInto X Y n w') ⊗ₘ
              (letterFrom X Y b ≫ letterInto X Y b) :
            tensorPow A (X ⊞ Y) (n + 1) ⟶
              tensorPow A (X ⊞ Y) (n + 1))) =
        ∑ b : Bool, 𝟙 (tensorPow A (X ⊞ Y) n) ⊗ₘ
          (letterFrom X Y b ≫ letterInto X Y b) :=
      Finset.sum_congr rfl fun b _ => e4 b
    have e6 : (∑ b : Bool, 𝟙 (tensorPow A (X ⊞ Y) n) ⊗ₘ
          (letterFrom X Y b ≫ letterInto X Y b)) =
        𝟙 (tensorPow A (X ⊞ Y) (n + 1)) := by
      rw [← tensor_sum, Fintype.sum_bool]
      show 𝟙 (tensorPow A (X ⊞ Y) n) ⊗ₘ
          (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) = 𝟙 _
      rw [biprod.total, MonoidalCategory.id_tensorHom_id]
    exact e1.trans (e2.trans (e3.trans (e5.trans e6)))

end MonPre

end Biprod

/-! ## Counting letters and the sorted words -/

/-- The number of `true` letters of a word. -/
def popCount {n : ℕ} (w : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => w i = true).card

/-- At most every letter is `true`. -/
theorem popCount_le {n : ℕ} (w : Fin n → Bool) : popCount w ≤ n := by
  have h := Finset.card_filter_le Finset.univ fun i => w i = true
  rwa [Finset.card_univ, Fintype.card_fin] at h

/-- The empty word has no `true` letters. -/
theorem popCount_nil (w : Fin 0 → Bool) : popCount w = 0 := by
  simp [popCount]

/-- The letter count splits off the last letter. -/
theorem popCount_succ {n : ℕ} (w : Fin (n + 1) → Bool) :
    popCount w =
      popCount (w ∘ Fin.castSucc) +
        (bif w (Fin.last n) then 1 else 0) := by
  have key : ∀ (m : ℕ) (v : Fin m → Bool),
      popCount v = ∑ i, if v i = true then 1 else 0 := by
    intro m v
    simp [popCount]
  have hsum : (∑ i : Fin n, if w (Fin.castSucc i) = true
        then 1 else 0) =
      ∑ i : Fin n, if (w ∘ Fin.castSucc) i = true then 1 else 0 :=
    Finset.sum_congr rfl fun i _ => rfl
  rw [key, key, Fin.sum_univ_castSucc, hsum]
  cases hw : w (Fin.last n) <;> rfl

/-- **The sorting permutation** of a word: the last slot is routed
below the tail — to the top of the `X` block when its letter is
`true`, and kept in place when it is `false` — and the rest is
sorted recursively.  This is the `ofSplit` decomposition the
tensor-power action recurses on. -/
noncomputable def sortPerm :
    {n : ℕ} → (Fin n → Bool) → Equiv.Perm (Fin n)
  | 0, _ => 1
  | n + 1, w =>
      ofSplit
        (bif w (Fin.last n)
          then ⟨popCount (w ∘ Fin.castSucc),
            Nat.lt_succ_of_le (popCount_le _)⟩
          else Fin.last n)
        (sortPerm (w ∘ Fin.castSucc))

/-- The defining recursion of `sortPerm`. -/
theorem sortPerm_succ {n : ℕ} (w : Fin (n + 1) → Bool) :
    sortPerm w =
      ofSplit
        (bif w (Fin.last n)
          then ⟨popCount (w ∘ Fin.castSucc),
            Nat.lt_succ_of_le (popCount_le _)⟩
          else Fin.last n)
        (sortPerm (w ∘ Fin.castSucc)) := rfl

/-- **The sorted word**: `true` on the first block of `p` slots and
`false` on the last `q`. -/
def standardWord (p q : ℕ) : Fin (p + q) → Bool :=
  fun i => decide ((i : ℕ) < p)

/-- With an empty second block the sorted word is all `true`. -/
theorem standardWord_zero (p : ℕ) :
    standardWord p 0 = fun _ => true := by
  funext i
  exact decide_eq_true i.isLt

/-- Restricting a sorted word drops one `false` letter. -/
theorem standardWord_castSucc (p q : ℕ) :
    standardWord p (q + 1) ∘ Fin.castSucc = standardWord p q := rfl

/-- The last letter of a sorted word with `false` letters is
`false`. -/
theorem standardWord_last (p q : ℕ) :
    standardWord p (q + 1) (Fin.last (p + q)) = false := by
  have h : ¬ (p + q < p) := by omega
  simp [standardWord, h]

/-! ## The sorted word power -/

/-- An all-`true` word power is a pure power of `X`. -/
theorem wordPow_const_true [Category.{v} A] [MonoidalCategory A]
    (X Y : A) :
    ∀ n : ℕ, wordPow X Y n (fun _ => true) = tensorPow A X n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show wordPow X Y n (fun _ => true) ⊗ X = tensorPow A X n ⊗ X
    rw [ih]

/-- The sorted word power with empty second block is the pure
power of `X`. -/
theorem wordPow_standard_zero [Category.{v} A] [MonoidalCategory A]
    (X Y : A) (p : ℕ) :
    wordPow X Y (p + 0) (standardWord p 0) = tensorPow A X p := by
  rw [standardWord_zero]
  exact wordPow_const_true X Y p

/-- One more `false` letter of a sorted word tensors a `Y`. -/
theorem wordPow_standard_succ [Category.{v} A] [MonoidalCategory A]
    (X Y : A) (p q : ℕ) :
    wordPow X Y (p + (q + 1)) (standardWord p (q + 1)) =
      wordPow X Y (p + q) (standardWord p q) ⊗ Y := by
  show wordPow X Y (p + q)
        (standardWord p (q + 1) ∘ Fin.castSucc) ⊗
      (bif standardWord p (q + 1) (Fin.last (p + q)) then X else Y) =
    wordPow X Y (p + q) (standardWord p q) ⊗ Y
  rw [standardWord_castSucc, standardWord_last]
  rfl

/-- **The sorted word power is a concatenation of pure powers**:
with all `X`s below all `Y`s, the word power reassociates to
`X ^ ⊗ p ⊗ Y ^ ⊗ q`.  Built by the recursion of the word, so that
consumers can compose with it stage by stage. -/
noncomputable def standardMixedIso [Category.{v} A] [MonoidalCategory A]
    (X Y : A) (p : ℕ) : (q : ℕ) →
    (wordPow X Y (p + q) (standardWord p q) ≅
      tensorPow A X p ⊗ tensorPow A Y q)
  | 0 =>
      eqToIso (wordPow_standard_zero X Y p) ≪≫
        (ρ_ (tensorPow A X p)).symm
  | q + 1 =>
      eqToIso (wordPow_standard_succ X Y p q) ≪≫
        whiskerRightIso (standardMixedIso X Y p q) Y ≪≫
        α_ (tensorPow A X p) (tensorPow A Y q) Y

/-! ## The base-point inclusion

On a sorted word, `mixedInto` is the concatenation of the two
pure-power inclusions.  The gluing helpers are stated at general
objects and applied by `exact`, so that no tensor-power arity
enters the rewriting.
-/

/-- Tensoring with the unit's identity is unitor conjugation.
Stated at general objects. -/
private theorem unit_tensor_unitor [Category.{v} A] [MonoidalCategory A]
    {P Q : A} (f : P ⟶ Q) :
    (f ⊗ₘ 𝟙 (𝟙_ A)) ≫ (ρ_ Q).hom = (ρ_ P).hom ≫ f := by
  rw [MonoidalCategory.tensorHom_id]
  exact MonoidalCategory.rightUnitor_naturality f

/-- One stage of the concatenation glued onto an intertwining of
the previous stage.  Stated at general objects. -/
private theorem concat_step_glue [Category.{v} A] [MonoidalCategory A]
    {P Q W R P' Q' Y Z : A}
    (u : P ⊗ Q ⟶ W) (M : W ⟶ R) (f : P ⟶ P') (g : Q ⟶ Q')
    (c : P' ⊗ Q' ⟶ R) (e : Y ⟶ Z)
    (hih : u ≫ M = (f ⊗ₘ g) ≫ c) :
    (α_ P Q Y).inv ≫ ((u ▷ Y) ≫ (M ⊗ₘ e)) =
      (f ⊗ₘ (g ⊗ₘ e)) ≫ (α_ P' Q' Z).inv ≫ (c ▷ Z) := by
  have h1 : (u ▷ Y) ≫ (M ⊗ₘ e) = (u ≫ M) ⊗ₘ e := by
    rw [← MonoidalCategory.tensorHom_id u Y,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  have h2 : ((f ⊗ₘ g) ⊗ₘ e) ≫ (c ▷ Z) = ((f ⊗ₘ g) ≫ c) ⊗ₘ e := by
    rw [← MonoidalCategory.tensorHom_id c Z,
      MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]
  have h3 : (α_ P Q Y).inv ≫ ((f ⊗ₘ g) ⊗ₘ e) =
      (f ⊗ₘ (g ⊗ₘ e)) ≫ (α_ P' Q' Z).inv :=
    (MonoidalCategory.associator_inv_naturality f g e).symm
  calc (α_ P Q Y).inv ≫ ((u ▷ Y) ≫ (M ⊗ₘ e))
      = (α_ P Q Y).inv ≫ (((f ⊗ₘ g) ≫ c) ⊗ₘ e) := by rw [h1, hih]
    _ = (α_ P Q Y).inv ≫ ((f ⊗ₘ g) ⊗ₘ e) ≫ (c ▷ Z) := by rw [h2]
    _ = ((f ⊗ₘ (g ⊗ₘ e)) ≫ (α_ P' Q' Z).inv) ≫ (c ▷ Z) := by
        rw [← Category.assoc, h3]
    _ = (f ⊗ₘ (g ⊗ₘ e)) ≫ (α_ P' Q' Z).inv ≫ (c ▷ Z) :=
        Category.assoc _ _ _

/-- An `eqToHom` pulls out of the first factor of a tensor.  Stated
at general objects. -/
private theorem eqToHom_tensor_pull [Category.{v} A] [MonoidalCategory A]
    {P P' Q R S : A} (h : P = P')
    (f : P' ⟶ Q) (g : R ⟶ S) :
    (eqToHom h ≫ f) ⊗ₘ g =
      eqToHom (congrArg (· ⊗ R) h) ≫ (f ⊗ₘ g) := by
  subst h
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.id_comp]

/-- Append a definitionally trivial transport to a two-step
factorisation.  The transport's endpoints coincide, so `exact`
applies it wherever they agree definitionally. -/
private theorem comp_cast_end₂ [Category.{v} A]
    {P Q R : A} {f : P ⟶ R} {g₁ : P ⟶ Q}
    {g₂ : Q ⟶ R} (H : R = R) (hfg : f = g₁ ≫ g₂) :
    f = g₁ ≫ g₂ ≫ eqToHom H := by
  rw [show H = rfl from rfl, eqToHom_refl, Category.comp_id, hfg]

/-- A transport and its inverse cancel across a decomposition of
the middle morphism.  Stated at general objects and applied by
`exact`, so the defeq-mismatched arities never enter a rewrite. -/
private theorem cast_cancel_glue [Category.{v} A]
    {U V W R : A} (h : V = W)
    (h' : W = V) (a : U ⟶ V) (D : W ⟶ R) (T : V ⟶ R)
    (hD : D = eqToHom h' ≫ T) :
    (a ≫ eqToHom h) ≫ D = a ≫ T := by
  subst h
  rw [hD, show h' = rfl from rfl, eqToHom_refl,
    Category.id_comp, Category.comp_id]

section Base

/-- Transport of `mixedInto` along an equality of words. -/
theorem mixedInto_congr [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : A) {n : ℕ} {w w' : Fin n → Bool}
    (h : w = w') :
    mixedInto X Y n w =
      eqToHom (congrArg (wordPow X Y n) h) ≫ mixedInto X Y n w' := by
  subst h
  rw [eqToHom_refl, Category.id_comp]

/-- Splitting `mixedInto` at the last letter, with the recursion's
word and letter replaced by given values. -/
theorem mixedInto_split [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : A) (n : ℕ) (w : Fin (n + 1) → Bool)
    (w' : Fin n → Bool) (b : Bool) (hw : w ∘ Fin.castSucc = w')
    (hb : w (Fin.last n) = b)
    (h : wordPow X Y (n + 1) w =
      wordPow X Y n w' ⊗ (bif b then X else Y)) :
    mixedInto X Y (n + 1) w =
      eqToHom h ≫ (mixedInto X Y n w' ⊗ₘ letterInto X Y b) := by
  subst hw
  subst hb
  exact (Category.id_comp _).symm

/-- On an all-`true` word the inclusion is the pure power of
`biprod.inl`. -/
theorem mixedInto_const_true
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : A) :
    ∀ n : ℕ,
      mixedInto X Y n (fun _ => true) =
        eqToHom (wordPow_const_true X Y n) ≫
          tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) n := by
  intro n
  induction n with
  | zero =>
    exact (Category.id_comp _).symm
  | succ n ih =>
    show mixedInto X Y n (fun _ => true) ⊗ₘ
        (biprod.inl : X ⟶ X ⊞ Y) = _
    rw [ih]
    exact eqToHom_tensor_pull (wordPow_const_true X Y n) _ _

/-- The last-letter split of `mixedInto` at a `false` letter, with
the selected object and inclusion spelled as `Y` and `biprod.inr`. -/
theorem mixedInto_split_false
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : A) (n : ℕ)
    (w : Fin (n + 1) → Bool) (w' : Fin n → Bool)
    (hw : w ∘ Fin.castSucc = w') (hb : w (Fin.last n) = false)
    (h : wordPow X Y (n + 1) w = wordPow X Y n w' ⊗ Y) :
    mixedInto X Y (n + 1) w =
      eqToHom h ≫
        (mixedInto X Y n w' ⊗ₘ (biprod.inr : Y ⟶ X ⊞ Y)) :=
  mixedInto_split X Y n w w' false hw hb h

/-- The last-letter split of `mixedInto` at a `true` letter, with
the selected object and inclusion spelled as `X` and `biprod.inl`. -/
theorem mixedInto_split_true
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : A) (n : ℕ)
    (w : Fin (n + 1) → Bool) (w' : Fin n → Bool)
    (hw : w ∘ Fin.castSucc = w') (hb : w (Fin.last n) = true)
    (h : wordPow X Y (n + 1) w = wordPow X Y n w' ⊗ X) :
    mixedInto X Y (n + 1) w =
      eqToHom h ≫
        (mixedInto X Y n w' ⊗ₘ (biprod.inl : X ⟶ X ⊞ Y)) :=
  mixedInto_split X Y n w w' true hw hb h

/-- Transport along the `p + 0` arity cast composes away against
the pure power of the first inclusion. -/
private theorem inl_pow_cast
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : A) (m : ℕ)
    (H : tensorPow A X m = tensorPow A X (m + 0)) :
    eqToHom H ≫ tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) (m + 0) =
      tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) m := by
  rw [show H = rfl from rfl, eqToHom_refl, Category.id_comp]
  rfl

end Base

/-! ## Sorting

Every word's inclusion is the base-point inclusion of its sorted
form, up to the symmetric-group action.  The categorical content is
a single full rotation: bubbling the top factor all the way down is
the braiding against the whole tail, followed by a merge of the new
bottom factor into the concatenation — `insertTop_full` and
`putBelow_concat` below.
-/

section Symmetric

/-- The recursion of the action, at a split permutation. -/
theorem permMor_ofSplit
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (Z : A) (n : ℕ) (q : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) :
    permMor Z (n + 1) (ofSplit q τ) =
      (permMor Z n τ ▷ Z) ≫ insertTop Z n (n - (q : ℕ)) := by
  rw [permMor_succ, restPerm_ofSplit, topImage_ofSplit]

/-- The hexagon, arranged for one bubbling step: braiding the top
two slots and then the lower pair against the top is braiding the
joint pair.  Stated at a general object. -/
private theorem swap_hexagon
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (P Z : A) :
    ((α_ P Z Z).hom ≫ (P ◁ (β_ Z Z).hom) ≫ (α_ P Z Z).inv) ≫
        ((β_ P Z).hom ▷ Z) =
      (β_ (P ⊗ Z) Z).hom ≫ (α_ Z P Z).inv := by
  have h := BraidedCategory.hexagon_reverse P Z Z
  calc ((α_ P Z Z).hom ≫ (P ◁ (β_ Z Z).hom) ≫ (α_ P Z Z).inv) ≫
        ((β_ P Z).hom ▷ Z)
      = (α_ P Z Z).hom ≫ ((P ◁ (β_ Z Z).hom) ≫ (α_ P Z Z).inv ≫
          ((β_ P Z).hom ▷ Z)) := by simp only [Category.assoc]
    _ = (α_ P Z Z).hom ≫ (α_ P Z Z).inv ≫ (β_ (P ⊗ Z) Z).hom ≫
          (α_ Z P Z).inv := by rw [← h]
    _ = (β_ (P ⊗ Z) Z).hom ≫ (α_ Z P Z).inv := by
        rw [Iso.hom_inv_id_assoc]

/-- One rotation step, at a general base object: a braid-and-merge
of the lower slots, whiskered and preceded by the top braiding, is
the joint braid-and-merge one slot higher. -/
private theorem rotate_step
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    {P V : A} (Z : A) (i : P ⊗ Z ⟶ V)
    (u : Z ⊗ P ⟶ V) (hi : i = (β_ P Z).hom ≫ u) :
    ((α_ P Z Z).hom ≫ (P ◁ (β_ Z Z).hom) ≫ (α_ P Z Z).inv) ≫
        (i ▷ Z) =
      (β_ (P ⊗ Z) Z).hom ≫ (α_ Z P Z).inv ≫ (u ▷ Z) := by
  rw [hi, MonoidalCategory.comp_whiskerRight, ← Category.assoc,
    swap_hexagon, Category.assoc]

/-- **Merging a factor at the bottom**: the structural morphism
`Z ⊗ Z ^ ⊗ m ⟶ Z ^ ⊗ (m + 1)`, by the recursion of the power. -/
noncomputable def putBelow [Category.{v} A] [MonoidalCategory A]
    (Z : A) : (m : ℕ) →
    (Z ⊗ tensorPow A Z m ⟶ tensorPow A Z (m + 1))
  | 0 => (ρ_ Z).hom ≫ (λ_ Z).inv
  | m + 1 =>
      (α_ Z (tensorPow A Z m) Z).inv ≫ (putBelow Z m ▷ Z)

/-- **The full rotation is a braiding**: bubbling the top factor of
`Z ^ ⊗ (m + 1)` all the way to the bottom is the braiding of the
factor against the whole tail, followed by the bottom merge. -/
theorem insertTop_full
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (Z : A) :
    ∀ m : ℕ, insertTop Z m m =
      (β_ (tensorPow A Z m) Z).hom ≫ putBelow Z m := by
  intro m
  induction m with
  | zero =>
    rw [insertTop_zero]
    have h : (β_ (𝟙_ A) Z).hom ≫ (ρ_ Z).hom ≫ (λ_ Z).inv =
        𝟙 (𝟙_ A ⊗ Z) := by
      rw [← Category.assoc, braiding_rightUnitor, Iso.hom_inv_id]
    exact h.symm
  | succ m ih =>
    rw [insertTop_succ]
    exact rotate_step Z (insertTop Z m m) (putBelow Z m) ih

/-- A whiskered arity transport is the transport one arity up.
Stated with both transports explicit, so it applies by `exact`
wherever the endpoints agree definitionally. -/
private theorem cast_whiskerRight_eq [Category.{v} A] [MonoidalCategory A]
    (Z : A) {P Q : A} (h : P = Q)
    (h' : P ⊗ Z = Q ⊗ Z) :
    eqToHom h ▷ Z = eqToHom h' := by
  subst h
  rw [show h' = rfl from rfl, eqToHom_refl, eqToHom_refl,
    MonoidalCategory.id_whiskerRight]

/-- The bottom merge against one concatenation stage, at the empty
tail: pure unitor coherence, at general objects. -/
private theorem putBelow_concat_zero_coh [Category.{v} A] [MonoidalCategory A]
    (P Z : A) :
    (P ◁ ((ρ_ Z).hom ≫ (λ_ Z).inv)) ≫
        ((α_ P (𝟙_ A) Z).inv ≫ ((ρ_ P).hom ▷ Z)) =
      (α_ P Z (𝟙_ A)).inv ≫ (ρ_ (P ⊗ Z)).hom := by
  monoidal

/-- The inductive step of the bottom merge against the
concatenation, at general objects: the pentagon and naturality. -/
private theorem merge_step_glue [Category.{v} A] [MonoidalCategory A]
    {P U M W B' N N' : A}
    (u : U ⊗ M ⟶ B') (c : P ⊗ B' ⟶ N)
    (c' : (P ⊗ U) ⊗ M ⟶ N') (E : N' ⟶ N)
    (hih : (P ◁ u) ≫ c = (α_ P U M).inv ≫ c' ≫ E) :
    (P ◁ ((α_ U M W).inv ≫ (u ▷ W))) ≫
        ((α_ P B' W).inv ≫ (c ▷ W)) =
      (α_ P U (M ⊗ W)).inv ≫ (α_ (P ⊗ U) M W).inv ≫
        (c' ▷ W) ≫ (E ▷ W) := by
  have hpent : (P ◁ (α_ U M W).inv) ≫ (α_ P (U ⊗ M) W).inv ≫
      ((α_ P U M).inv ▷ W) =
      (α_ P U (M ⊗ W)).inv ≫ (α_ (P ⊗ U) M W).inv := by
    monoidal
  calc (P ◁ ((α_ U M W).inv ≫ (u ▷ W))) ≫
        ((α_ P B' W).inv ≫ (c ▷ W))
      = (P ◁ (α_ U M W).inv) ≫ ((P ◁ (u ▷ W)) ≫
          (α_ P B' W).inv) ≫ (c ▷ W) := by
        rw [MonoidalCategory.whiskerLeft_comp]
        try simp only [Category.assoc]
    _ = (P ◁ (α_ U M W).inv) ≫ ((α_ P (U ⊗ M) W).inv ≫
          ((P ◁ u) ▷ W)) ≫ (c ▷ W) := by
        rw [MonoidalCategory.associator_inv_naturality_middle]
    _ = (P ◁ (α_ U M W).inv) ≫ (α_ P (U ⊗ M) W).inv ≫
          ((P ◁ u) ≫ c) ▷ W := by
        rw [MonoidalCategory.comp_whiskerRight]
        try simp only [Category.assoc]
    _ = (P ◁ (α_ U M W).inv) ≫ (α_ P (U ⊗ M) W).inv ≫
          ((α_ P U M).inv ▷ W) ≫ (c' ▷ W) ≫ (E ▷ W) := by
        rw [hih, MonoidalCategory.comp_whiskerRight,
          MonoidalCategory.comp_whiskerRight]
        try simp only [Category.assoc]
    _ = ((P ◁ (α_ U M W).inv) ≫ (α_ P (U ⊗ M) W).inv ≫
          ((α_ P U M).inv ▷ W)) ≫ (c' ▷ W) ≫ (E ▷ W) := by
        simp only [Category.assoc]
    _ = (α_ P U (M ⊗ W)).inv ≫ (α_ (P ⊗ U) M W).inv ≫
          (c' ▷ W) ≫ (E ▷ W) := by
        rw [hpent]
        try simp only [Category.assoc]

/-- **The bottom merge concatenates**: merging a factor below the
second block and concatenating is reassociating it onto the first
block, up to the arity transport. -/
theorem putBelow_concat [Category.{v} A] [MonoidalCategory A]
    (Z : A) (p : ℕ) :
    ∀ m : ℕ,
      (tensorPow A Z p ◁ putBelow Z m) ≫
          (tensorPowConcat Z p (m + 1)).hom =
        (α_ (tensorPow A Z p) Z (tensorPow A Z m)).inv ≫
          (tensorPowConcat Z (p + 1) m).hom ≫
          eqToHom (congrArg (tensorPow A Z)
            (Nat.succ_add_eq_add_succ p m)) := by
  intro m
  induction m with
  | zero =>
    exact comp_cast_end₂ _
      (putBelow_concat_zero_coh (tensorPow A Z p) Z)
  | succ m ih =>
    have step := merge_step_glue (P := tensorPow A Z p) (W := Z)
      (putBelow Z m) (tensorPowConcat Z p (m + 1)).hom
      (tensorPowConcat Z (p + 1) m).hom
      (eqToHom (congrArg (tensorPow A Z)
        (Nat.succ_add_eq_add_succ p m))) ih
    refine step.trans ?_
    rw [cast_whiskerRight_eq Z
      (congrArg (tensorPow A Z) (Nat.succ_add_eq_add_succ p m))
      (congrArg (tensorPow A Z)
        (Nat.succ_add_eq_add_succ p (m + 1)))]
    exact congrArg
      (fun t => (α_ (tensorPow A Z p) Z
        (tensorPow A Z m ⊗ Z)).inv ≫ t)
      (Category.assoc _ _ _).symm

/-- Splitting the first factor off a composite tensored against a
morphism.  Stated at general objects. -/
private theorem tensor_split_first [Category.{v} A] [MonoidalCategory A]
    {P Q R S T : A} (a : P ⟶ Q)
    (v : Q ⟶ R) (g : S ⟶ T) :
    (a ≫ v) ⊗ₘ g = (a ▷ S) ≫ (v ⊗ₘ g) := by
  calc (a ≫ v) ⊗ₘ g = (a ≫ v) ⊗ₘ (𝟙 S ≫ g) := by
        rw [Category.id_comp]
    _ = (a ⊗ₘ 𝟙 S) ≫ (v ⊗ₘ g) :=
        (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm
    _ = (a ▷ S) ≫ (v ⊗ₘ g) := by
        rw [MonoidalCategory.tensorHom_id]

/-- Splitting the last factor off a composite tensored against a
morphism.  Stated at general objects. -/
private theorem tensor_split_last [Category.{v} A] [MonoidalCategory A]
    {P Q R S T : A} (v : P ⟶ Q)
    (E : Q ⟶ R) (g : S ⟶ T) :
    (v ≫ E) ⊗ₘ g = (v ⊗ₘ g) ≫ (E ▷ T) := by
  calc (v ≫ E) ⊗ₘ g = (v ≫ E) ⊗ₘ (g ≫ 𝟙 T) := by
        rw [Category.comp_id]
    _ = (v ⊗ₘ g) ≫ (E ⊗ₘ 𝟙 T) :=
        (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm
    _ = (v ⊗ₘ g) ≫ (E ▷ T) := by
        rw [MonoidalCategory.tensorHom_id]

/-- A tensor absorbed into the second factor through a left
whiskering.  Stated at general objects. -/
private theorem tensor_then_whiskerLeft [Category.{v} A] [MonoidalCategory A]
    {P Q S T U : A} (g : P ⟶ Q)
    (h : S ⟶ T) (k : T ⟶ U) :
    (g ⊗ₘ h) ≫ (Q ◁ k) = g ⊗ₘ (h ≫ k) := by
  rw [← MonoidalCategory.id_tensorHom Q k,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- A left whiskering absorbed into the second factor of a tensor.
Stated at general objects. -/
private theorem whiskerLeft_then_tensor [Category.{v} A] [MonoidalCategory A]
    {P Q S T U : A} (g : P ⟶ Q)
    (h : S ⟶ T) (k : T ⟶ U) :
    (P ◁ h) ≫ (g ⊗ₘ k) = g ⊗ₘ (h ≫ k) := by
  rw [← MonoidalCategory.id_tensorHom P h,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- One concatenation stage, whiskered: reassociate and take the
next stage. -/
private theorem concat_whisker_step [Category.{v} A] [MonoidalCategory A]
    (Z : A) (p m : ℕ) :
    ((tensorPowConcat Z p m).hom ▷ Z) =
      (α_ (tensorPow A Z p) (tensorPow A Z m) Z).hom ≫
        (tensorPowConcat Z p (m + 1)).hom :=
  (Iso.hom_inv_id_assoc
    (α_ (tensorPow A Z p) (tensorPow A Z m) Z) _).symm

/-- Arity transport commutes with the insertion cycle. -/
private theorem insertTop_cast
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (Z : A) (a b k : ℕ) (hab : a = b)
    (H : tensorPow A Z a = tensorPow A Z b) :
    (eqToHom H ▷ Z) ≫ insertTop Z b k =
      insertTop Z a k ≫ (eqToHom H ▷ Z) := by
  subst hab
  rw [show H = rfl from rfl, eqToHom_refl,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  exact (Category.comp_id _).symm

/-- An arity transport composed with a whiskered one is the joint
transport. -/
private theorem cast_then_cast_whisker [Category.{v} A] [MonoidalCategory A]
    (Z : A) {a b n : ℕ}
    (hab : a = b + 1) (hbn : b = n)
    (H₁ : tensorPow A Z a = tensorPow A Z (b + 1))
    (H₂ : tensorPow A Z b = tensorPow A Z n)
    (H₃ : tensorPow A Z a = tensorPow A Z (n + 1)) :
    eqToHom H₁ ≫ (eqToHom H₂ ▷ Z) = eqToHom H₃ := by
  subst hbn
  subst hab
  rw [show H₁ = rfl from rfl, show H₂ = rfl from rfl,
    show H₃ = rfl from rfl, eqToHom_refl, eqToHom_refl,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  rfl

/-- `tensor_then_whiskerLeft` against a tail. -/
private theorem tensor_then_whiskerLeft_assoc
    [Category.{v} A] [MonoidalCategory A]
    {P Q S T U V : A}
    (g : P ⟶ Q) (h : S ⟶ T) (k : T ⟶ U) (rest : Q ⊗ U ⟶ V) :
    (g ⊗ₘ h) ≫ (Q ◁ k) ≫ rest = (g ⊗ₘ (h ≫ k)) ≫ rest := by
  rw [← Category.assoc, tensor_then_whiskerLeft]

/-- `whiskerLeft_then_tensor` against a tail. -/
private theorem whiskerLeft_then_tensor_assoc
    [Category.{v} A] [MonoidalCategory A]
    {P Q S T U V : A}
    (g : P ⟶ Q) (h : S ⟶ T) (k : T ⟶ U) (rest : Q ⊗ U ⟶ V) :
    (P ◁ h) ≫ (g ⊗ₘ k) ≫ rest = (g ⊗ₘ (h ≫ k)) ≫ rest := by
  rw [← Category.assoc, whiskerLeft_then_tensor]

/-- One whiskered concatenation stage against the insertion cycle:
reassociate, insert within the second block, and concatenate. -/
private theorem concat_whisker_insert
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (Z : A) (p m : ℕ) :
    ((tensorPowConcat Z p m).hom ▷ Z) ≫ insertTop Z (p + m) m =
      (α_ (tensorPow A Z p) (tensorPow A Z m) Z).hom ≫
        ((tensorPow A Z p ◁ insertTop Z m m) ≫
          (tensorPowConcat Z p (m + 1)).hom) := by
  have h1 := tensorPowConcat_insertTop Z p m m le_rfl
  calc ((tensorPowConcat Z p m).hom ▷ Z) ≫ insertTop Z (p + m) m
      = ((α_ (tensorPow A Z p) (tensorPow A Z m) Z).hom ≫
          (tensorPowConcat Z p (m + 1)).hom) ≫
          insertTop Z (p + m) m := by
            rw [concat_whisker_step]
            exact rfl
    _ = (α_ (tensorPow A Z p) (tensorPow A Z m) Z).hom ≫
          ((tensorPowConcat Z p (m + 1)).hom ≫
            insertTop Z (p + m) m) := Category.assoc _ _ _
    _ = (α_ (tensorPow A Z p) (tensorPow A Z m) Z).hom ≫
          ((tensorPow A Z p ◁ insertTop Z m m) ≫
            (tensorPowConcat Z p (m + 1)).hom) :=
        congrArg
          (fun t => (α_ (tensorPow A Z p) (tensorPow A Z m) Z).hom ≫ t)
          h1

/-- A tensor absorbed through a right whiskering.  Stated at
general objects. -/
private theorem tensor_then_whiskerRight [Category.{v} A] [MonoidalCategory A]
    {P Q R S T : A}
    (f : P ⟶ Q) (u : Q ⟶ R) (g : S ⟶ T) :
    (f ⊗ₘ g) ≫ (u ▷ T) = (f ≫ u) ⊗ₘ g := by
  rw [← MonoidalCategory.tensorHom_id u T,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- The concatenation's successor stage, unfolded. -/
private theorem tensorPowConcat_succ_hom [Category.{v} A] [MonoidalCategory A]
    (Z : A) (a b : ℕ) :
    (tensorPowConcat Z a (b + 1)).hom =
      (α_ (tensorPow A Z a) (tensorPow A Z b) Z).inv ≫
        ((tensorPowConcat Z a b).hom ▷ Z) := rfl

/-- Reassociating a parenthesised three-chain against a tail. -/
private theorem assoc₃ [Category.{v} A]
    {P Q R S T : A} (a : P ⟶ Q) (b : Q ⟶ R)
    (c : R ⟶ S) (d : S ⟶ T) :
    (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

/-- The false-branch gluing at general objects: tensoring a
four-chain with a letter splits it around the reassociation. -/
private theorem sorted_false_glue [Category.{v} A] [MonoidalCategory A]
    {W P Q P' Q' N N' Y Z : A}
    (a : W ⟶ P ⊗ Q) (f₁ : P ⟶ P') (f₂ : Q ⟶ Q')
    (c : P' ⊗ Q' ⟶ N) (E : N ⟶ N') (g : Y ⟶ Z) :
    (a ≫ (f₁ ⊗ₘ f₂) ≫ c ≫ E) ⊗ₘ g =
      (a ▷ Y) ≫ (α_ P Q Y).hom ≫ (f₁ ⊗ₘ (f₂ ⊗ₘ g)) ≫
        (α_ P' Q' Z).inv ≫ (c ▷ Z) ≫ (E ▷ Z) := by
  rw [tensor_split_first, tensor_split_last,
    MonoidalCategory.comp_whiskerRight,
    MonoidalCategory.associator_conjugation]
  simp only [Category.assoc]

section SortedBiprod

/-- **Sorting one appended `X`**: the base-point inclusion with one
more `X` in the last slot, bubbled down past the whole `Y` block,
is the base-point inclusion of the grown `X` block — up to braiding
the appended factor past the `Y` power on the mixed side and the
arity transport `(p + 1) + m = p + (m + 1)` at the target. -/
theorem base_insert_true
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [HasBinaryBiproducts A]
    (X Y : A) (p m : ℕ) :
    (((tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
          tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m) ≫
        (tensorPowConcat (X ⊞ Y) p m).hom) ⊗ₘ
        (biprod.inl : X ⟶ X ⊞ Y)) ≫
      insertTop (X ⊞ Y) (p + m) m =
    (α_ (tensorPow A X p) (tensorPow A Y m) X).hom ≫
      (tensorPow A X p ◁ (β_ (tensorPow A Y m) X).hom) ≫
      (α_ (tensorPow A X p) X (tensorPow A Y m)).inv ≫
      (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) (p + 1) ⊗ₘ
        tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m) ≫
      (tensorPowConcat (X ⊞ Y) (p + 1) m).hom ≫
      eqToHom (congrArg (tensorPow A (X ⊞ Y))
        (Nat.succ_add_eq_add_succ p m)) := by
  rw [tensor_split_last]
  simp only [Category.assoc]
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
`Y` joins the top of the `Y` block and nothing is bubbled. -/
private theorem sorted_step_false
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [HasBinaryBiproducts A]
    (X Y : A) {n : ℕ}
    (w : Fin (n + 1) → Bool) (p m : ℕ)
    (hpm : p + m = n) (hq1 : p + (m + 1) = n + 1)
    (e' : wordPow X Y n (w ∘ Fin.castSucc) ≅
      tensorPow A X p ⊗ tensorPow A Y m)
    (hobj : wordPow X Y (n + 1) w =
      wordPow X Y n (w ∘ Fin.castSucc) ⊗ Y)
    (hb : w (Fin.last n) = false)
    (hperm : permMor (X ⊞ Y) (n + 1) (sortPerm w) =
      permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) ▷ (X ⊞ Y))
    (hsq' : mixedInto X Y n (w ∘ Fin.castSucc) ≫
        permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) =
      e'.hom ≫
        (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
          tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m) ≫
        (tensorPowConcat (X ⊞ Y) p m).hom ≫
        eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm)) :
    mixedInto X Y (n + 1) w ≫
        permMor (X ⊞ Y) (n + 1) (sortPerm w) =
      (eqToIso hobj ≪≫ whiskerRightIso e' Y ≪≫
          α_ (tensorPow A X p) (tensorPow A Y m) Y).hom ≫
        (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
          tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) (m + 1)) ≫
        (tensorPowConcat (X ⊞ Y) p (m + 1)).hom ≫
        eqToHom (congrArg (tensorPow A (X ⊞ Y)) hq1) := by
  have hsplit := mixedInto_split_false X Y n w (w ∘ Fin.castSucc)
    rfl hb hobj
  have hcast := cast_whiskerRight_eq (X ⊞ Y)
    (congrArg (tensorPow A (X ⊞ Y)) hpm)
    (congrArg (tensorPow A (X ⊞ Y)) hq1)
  have h1 : mixedInto X Y (n + 1) w ≫
        permMor (X ⊞ Y) (n + 1) (sortPerm w)
      = (eqToHom hobj ≫
          (mixedInto X Y n (w ∘ Fin.castSucc) ⊗ₘ
            (biprod.inr : Y ⟶ X ⊞ Y))) ≫
          (permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) ▷
            (X ⊞ Y)) := by
        rw [hsplit, hperm]
        exact rfl
  have h2 : (eqToHom hobj ≫
          (mixedInto X Y n (w ∘ Fin.castSucc) ⊗ₘ
            (biprod.inr : Y ⟶ X ⊞ Y))) ≫
          (permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) ▷
            (X ⊞ Y))
      = eqToHom hobj ≫
          ((mixedInto X Y n (w ∘ Fin.castSucc) ⊗ₘ
            (biprod.inr : Y ⟶ X ⊞ Y)) ≫
          (permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) ▷
            (X ⊞ Y))) := Category.assoc _ _ _
  have h3 : eqToHom hobj ≫
          ((mixedInto X Y n (w ∘ Fin.castSucc) ⊗ₘ
            (biprod.inr : Y ⟶ X ⊞ Y)) ≫
          (permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) ▷
            (X ⊞ Y)))
      = eqToHom hobj ≫
          ((mixedInto X Y n (w ∘ Fin.castSucc) ≫
            permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc))) ⊗ₘ
            (biprod.inr : Y ⟶ X ⊞ Y)) :=
        congrArg (fun t => eqToHom hobj ≫ t)
          (tensor_then_whiskerRight _ _ _)
  have h4 : eqToHom hobj ≫
          ((mixedInto X Y n (w ∘ Fin.castSucc) ≫
            permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc))) ⊗ₘ
            (biprod.inr : Y ⟶ X ⊞ Y))
      = eqToHom hobj ≫
          ((e'.hom ≫
            (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
              tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m) ≫
            (tensorPowConcat (X ⊞ Y) p m).hom ≫
            eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm)) ⊗ₘ
            (biprod.inr : Y ⟶ X ⊞ Y)) := by rw [hsq']
  have h5 : eqToHom hobj ≫
          ((e'.hom ≫
            (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
              tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m) ≫
            (tensorPowConcat (X ⊞ Y) p m).hom ≫
            eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm)) ⊗ₘ
            (biprod.inr : Y ⟶ X ⊞ Y))
      = eqToHom hobj ≫
          ((e'.hom ▷ Y) ≫
            (α_ (tensorPow A X p) (tensorPow A Y m) Y).hom ≫
            (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
              (tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m ⊗ₘ
                (biprod.inr : Y ⟶ X ⊞ Y))) ≫
            (α_ (tensorPow A (X ⊞ Y) p) (tensorPow A (X ⊞ Y) m)
              (X ⊞ Y)).inv ≫
            ((tensorPowConcat (X ⊞ Y) p m).hom ▷ (X ⊞ Y)) ≫
            (eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm) ▷
              (X ⊞ Y))) :=
        congrArg (fun t => eqToHom hobj ≫ t)
          (sorted_false_glue e'.hom _ _ _ _ _)
  have h6 : eqToHom hobj ≫
          ((e'.hom ▷ Y) ≫
            (α_ (tensorPow A X p) (tensorPow A Y m) Y).hom ≫
            (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
              (tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m ⊗ₘ
                (biprod.inr : Y ⟶ X ⊞ Y))) ≫
            (α_ (tensorPow A (X ⊞ Y) p) (tensorPow A (X ⊞ Y) m)
              (X ⊞ Y)).inv ≫
            ((tensorPowConcat (X ⊞ Y) p m).hom ▷ (X ⊞ Y)) ≫
            (eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm) ▷
              (X ⊞ Y)))
      = eqToHom hobj ≫
          ((e'.hom ▷ Y) ≫
            (α_ (tensorPow A X p) (tensorPow A Y m) Y).hom ≫
            (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
              (tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m ⊗ₘ
                (biprod.inr : Y ⟶ X ⊞ Y))) ≫
            (α_ (tensorPow A (X ⊞ Y) p) (tensorPow A (X ⊞ Y) m)
              (X ⊞ Y)).inv ≫
            ((tensorPowConcat (X ⊞ Y) p m).hom ▷ (X ⊞ Y)) ≫
            eqToHom (congrArg (tensorPow A (X ⊞ Y)) hq1)) := by
        rw [hcast]
        exact rfl
  have h7 : eqToHom hobj ≫
          ((e'.hom ▷ Y) ≫
            (α_ (tensorPow A X p) (tensorPow A Y m) Y).hom ≫
            (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
              (tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m ⊗ₘ
                (biprod.inr : Y ⟶ X ⊞ Y))) ≫
            (α_ (tensorPow A (X ⊞ Y) p) (tensorPow A (X ⊞ Y) m)
              (X ⊞ Y)).inv ≫
            ((tensorPowConcat (X ⊞ Y) p m).hom ▷ (X ⊞ Y)) ≫
            eqToHom (congrArg (tensorPow A (X ⊞ Y)) hq1))
      = (eqToIso hobj ≪≫ whiskerRightIso e' Y ≪≫
          α_ (tensorPow A X p) (tensorPow A Y m) Y).hom ≫
        (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
          tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) (m + 1)) ≫
        (tensorPowConcat (X ⊞ Y) p (m + 1)).hom ≫
        eqToHom (congrArg (tensorPow A (X ⊞ Y)) hq1) :=
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
`X` is bubbled down past the whole `Y` block onto the top of the
`X` block. -/
private theorem sorted_step_true
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [HasBinaryBiproducts A]
    (X Y : A) {n : ℕ}
    (w : Fin (n + 1) → Bool) (p m : ℕ)
    (hpm : p + m = n) (hm : n - p = m)
    (hq1 : p + 1 + m = n + 1)
    (e' : wordPow X Y n (w ∘ Fin.castSucc) ≅
      tensorPow A X p ⊗ tensorPow A Y m)
    (hobj : wordPow X Y (n + 1) w =
      wordPow X Y n (w ∘ Fin.castSucc) ⊗ X)
    (hb : w (Fin.last n) = true)
    (hperm : permMor (X ⊞ Y) (n + 1) (sortPerm w) =
      (permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) ▷
        (X ⊞ Y)) ≫ insertTop (X ⊞ Y) n (n - p))
    (hsq' : mixedInto X Y n (w ∘ Fin.castSucc) ≫
        permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) =
      e'.hom ≫
        (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
          tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m) ≫
        (tensorPowConcat (X ⊞ Y) p m).hom ≫
        eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm)) :
    mixedInto X Y (n + 1) w ≫
        permMor (X ⊞ Y) (n + 1) (sortPerm w) =
      (eqToIso hobj ≪≫ whiskerRightIso e' X ≪≫
          α_ (tensorPow A X p) (tensorPow A Y m) X ≪≫
          whiskerLeftIso (tensorPow A X p)
            (β_ (tensorPow A Y m) X) ≪≫
          (α_ (tensorPow A X p) X (tensorPow A Y m)).symm).hom ≫
        (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) (p + 1) ⊗ₘ
          tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m) ≫
        (tensorPowConcat (X ⊞ Y) (p + 1) m).hom ≫
        eqToHom (congrArg (tensorPow A (X ⊞ Y)) hq1) := by
  have hsplit := mixedInto_split_true X Y n w (w ∘ Fin.castSucc)
    rfl hb hobj
  have hmerge := cast_then_cast_whisker (X ⊞ Y)
    (a := p + 1 + m) (b := p + m) (n := n)
    (by omega) hpm
    (congrArg (tensorPow A (X ⊞ Y)) (Nat.succ_add_eq_add_succ p m))
    (congrArg (tensorPow A (X ⊞ Y)) hpm)
    (congrArg (tensorPow A (X ⊞ Y)) hq1)
  have h1 : mixedInto X Y (n + 1) w ≫
        permMor (X ⊞ Y) (n + 1) (sortPerm w)
      = (eqToHom hobj ≫
          (mixedInto X Y n (w ∘ Fin.castSucc) ⊗ₘ
            (biprod.inl : X ⟶ X ⊞ Y))) ≫
          ((permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) ▷
            (X ⊞ Y)) ≫ insertTop (X ⊞ Y) n (n - p)) := by
    rw [hsplit, hperm]
    exact rfl
  refine (h1.trans ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => eqToHom hobj ≫ t)
    (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      (t ≫ insertTop (X ⊞ Y) n (n - p)))
    (tensor_then_whiskerRight _ _ _)).trans ?_
  refine (?_ :
    eqToHom hobj ≫
      (((mixedInto X Y n (w ∘ Fin.castSucc) ≫
        permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc))) ⊗ₘ
        (biprod.inl : X ⟶ X ⊞ Y)) ≫
        insertTop (X ⊞ Y) n (n - p)) = _)
  rw [hsq']
  refine (congrArg
    (fun v => eqToHom hobj ≫
      ((v ⊗ₘ (biprod.inl : X ⟶ X ⊞ Y)) ≫
        insertTop (X ⊞ Y) n (n - p)))
    (assoc₃ e'.hom _ _ _).symm).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      (t ≫ insertTop (X ⊞ Y) n (n - p)))
    (tensor_split_last _ _ _)).trans ?_
  refine (congrArg (fun t => eqToHom hobj ≫ t)
    (Category.assoc _ _ _)).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      (((e'.hom ≫
        (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
          tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m) ≫
        (tensorPowConcat (X ⊞ Y) p m).hom) ⊗ₘ
        (biprod.inl : X ⟶ X ⊞ Y)) ≫ t))
    (insertTop_cast (X ⊞ Y) (p + m) n (n - p) hpm
      (congrArg (tensorPow A (X ⊞ Y)) hpm))).trans ?_
  refine (congrArg
    (fun k => eqToHom hobj ≫
      (((e'.hom ≫
        (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
          tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m) ≫
        (tensorPowConcat (X ⊞ Y) p m).hom) ⊗ₘ
        (biprod.inl : X ⟶ X ⊞ Y)) ≫
        (insertTop (X ⊞ Y) (p + m) k ≫
          (eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm) ▷
            (X ⊞ Y)))))
    hm).trans ?_
  refine (congrArg (fun t => eqToHom hobj ≫ t)
    (Category.assoc _ _ _).symm).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      ((t ≫ insertTop (X ⊞ Y) (p + m) m) ≫
        (eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm) ▷
          (X ⊞ Y))))
    (tensor_split_first e'.hom _ _)).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      (t ≫ (eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm) ▷
        (X ⊞ Y))))
    (Category.assoc _ _ _)).trans ?_
  refine (congrArg
    (fun t => eqToHom hobj ≫
      (((e'.hom ▷ X) ≫ t) ≫
        (eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm) ▷
          (X ⊞ Y))))
    (base_insert_true X Y p m)).trans ?_
  refine (true_final_shape (eqToHom hobj) (e'.hom ▷ X)
    (α_ (tensorPow A X p) (tensorPow A Y m) X).hom
    (tensorPow A X p ◁ (β_ (tensorPow A Y m) X).hom)
    (α_ (tensorPow A X p) X (tensorPow A Y m)).inv
    (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) (p + 1) ⊗ₘ
      tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m)
    (tensorPowConcat (X ⊞ Y) (p + 1) m).hom
    (eqToHom (congrArg (tensorPow A (X ⊞ Y))
      (Nat.succ_add_eq_add_succ p m)))
    (eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpm) ▷
      (X ⊞ Y))).trans ?_
  exact congrArg
    (fun s => (eqToHom hobj ≫ (e'.hom ▷ X) ≫
        (α_ (tensorPow A X p) (tensorPow A Y m) X).hom ≫
        (tensorPow A X p ◁ (β_ (tensorPow A Y m) X).hom) ≫
        (α_ (tensorPow A X p) X (tensorPow A Y m)).inv) ≫
      (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) (p + 1) ⊗ₘ
        tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) m) ≫
      (tensorPowConcat (X ⊞ Y) (p + 1) m).hom ≫ s)
    hmerge

/-- Append a definitionally trivial transport to a three-step
factorisation. -/
private theorem comp_cast_end₃ [Category.{v} A]
    {P Q R S : A} {f : P ⟶ S}
    {g₁ : P ⟶ Q} {g₂ : Q ⟶ R} {g₃ : R ⟶ S} (H : S = S)
    (hfg : f = g₁ ≫ g₂ ≫ g₃) :
    f = g₁ ≫ g₂ ≫ g₃ ≫ eqToHom H := by
  rw [show H = rfl from rfl, eqToHom_refl, Category.comp_id, hfg]

/-- Renaming the block sizes of a sorting square: the data and the
square transport along equalities of the two sizes. -/
private theorem sorted_pack
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [HasBinaryBiproducts A]
    (X Y : A) {n : ℕ} {W : A}
    (mi : W ⟶ tensorPow A (X ⊞ Y) n) (p q pc qc : ℕ)
    (hp : p = pc) (hq : q = qc) (hpq : p + q = n)
    (hpcqc : pc + qc = n)
    (e : W ≅ tensorPow A X p ⊗ tensorPow A Y q)
    (hsq : mi = e.hom ≫
      (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) p ⊗ₘ
        tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) q) ≫
      (tensorPowConcat (X ⊞ Y) p q).hom ≫
      eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpq)) :
    ∃ e' : W ≅ tensorPow A X pc ⊗ tensorPow A Y qc,
      mi = e'.hom ≫
        (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) pc ⊗ₘ
          tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y) qc) ≫
        (tensorPowConcat (X ⊞ Y) pc qc).hom ≫
        eqToHom (congrArg (tensorPow A (X ⊞ Y)) hpcqc) := by
  subst hp
  subst hq
  exact ⟨e, hsq⟩

/-- **The sorting lemma**: every mixed inclusion is a permuted
base-point inclusion.  For each word `w` there is an isomorphism of
the word power with `X ^ ⊗ popCount w ⊗ Y ^ ⊗ (n − popCount w)`
under which `mixedInto`, followed by the action of `sortPerm w`, is
the concatenation of the two pure-power inclusions, transported
along `popCount w + (n − popCount w) = n` at the target. -/
theorem mixedInto_sorted
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [HasBinaryBiproducts A]
    (X Y : A) :
    ∀ (n : ℕ) (w : Fin n → Bool),
      ∃ e : wordPow X Y n w ≅
          tensorPow A X (popCount w) ⊗
            tensorPow A Y (n - popCount w),
        mixedInto X Y n w ≫ permMor (X ⊞ Y) n (sortPerm w) =
          e.hom ≫
            (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) (popCount w) ⊗ₘ
              tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y)
                (n - popCount w)) ≫
            (tensorPowConcat (X ⊞ Y) (popCount w)
              (n - popCount w)).hom ≫
            eqToHom (congrArg (tensorPow A (X ⊞ Y))
              (Nat.add_sub_cancel' (popCount_le w))) := by
  intro n
  induction n with
  | zero =>
    intro w
    refine sorted_pack X Y
      (mixedInto X Y 0 w ≫ permMor (X ⊞ Y) 0 (sortPerm w))
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
      have hobj : wordPow X Y (n + 1) w =
          wordPow X Y n (w ∘ Fin.castSucc) ⊗ Y := by
        rw [wordPow_succ, hb]
        rfl
      have hperm : permMor (X ⊞ Y) (n + 1) (sortPerm w) =
          permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) ▷
            (X ⊞ Y) := by
        rw [sortPerm_succ, hb, Bool.cond_false, permMor_ofSplit,
          show ((Fin.last n : Fin (n + 1)) : ℕ) = n from rfl,
          Nat.sub_self, insertTop_zero]
        exact Category.comp_id _
      have hq1 : popCount (w ∘ Fin.castSucc) +
          (n - popCount (w ∘ Fin.castSucc) + 1) = n + 1 := by
        omega
      refine sorted_pack X Y
        (mixedInto X Y (n + 1) w ≫
          permMor (X ⊞ Y) (n + 1) (sortPerm w))
        (popCount (w ∘ Fin.castSucc))
        (n - popCount (w ∘ Fin.castSucc) + 1)
        (popCount w) (n + 1 - popCount w) hpw.symm (by omega) hq1
        (Nat.add_sub_cancel' (popCount_le w)) _
        (sorted_step_false X Y w (popCount (w ∘ Fin.castSucc))
          (n - popCount (w ∘ Fin.castSucc))
          (Nat.add_sub_cancel' hple) hq1 e' hobj hb hperm hsq')
    | true =>
      have hpw : popCount w = popCount (w ∘ Fin.castSucc) + 1 := by
        rw [popCount_succ, hb]
        rfl
      have hobj : wordPow X Y (n + 1) w =
          wordPow X Y n (w ∘ Fin.castSucc) ⊗ X := by
        rw [wordPow_succ, hb]
        rfl
      have hperm : permMor (X ⊞ Y) (n + 1) (sortPerm w) =
          (permMor (X ⊞ Y) n (sortPerm (w ∘ Fin.castSucc)) ▷
            (X ⊞ Y)) ≫
            insertTop (X ⊞ Y) n
              (n - popCount (w ∘ Fin.castSucc)) := by
        rw [sortPerm_succ, hb, Bool.cond_true, permMor_ofSplit]
      have hq1 : popCount (w ∘ Fin.castSucc) + 1 +
          (n - popCount (w ∘ Fin.castSucc)) = n + 1 := by
        omega
      refine sorted_pack X Y
        (mixedInto X Y (n + 1) w ≫
          permMor (X ⊞ Y) (n + 1) (sortPerm w))
        (popCount (w ∘ Fin.castSucc) + 1)
        (n - popCount (w ∘ Fin.castSucc))
        (popCount w) (n + 1 - popCount w) hpw.symm (by omega) hq1
        (Nat.add_sub_cancel' (popCount_le w)) _
        (sorted_step_true X Y w (popCount (w ∘ Fin.castSucc))
          (n - popCount (w ∘ Fin.castSucc))
          (Nat.add_sub_cancel' hple) rfl hq1 e' hobj hb hperm hsq')

/-- **The sorting isomorphism**, chosen once and for all from the
sorting lemma: `wordPow X Y n w` against the sorted concatenation
of pure powers. -/
noncomputable def sortIso
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [HasBinaryBiproducts A]
    (X Y : A) (n : ℕ) (w : Fin n → Bool) :
    wordPow X Y n w ≅
      tensorPow A X (popCount w) ⊗ tensorPow A Y (n - popCount w) :=
  (mixedInto_sorted X Y n w).choose

/-- The sorting square, for the chosen isomorphism `sortIso`. -/
theorem sortIso_spec [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [HasBinaryBiproducts A]
    (X Y : A) (n : ℕ) (w : Fin n → Bool) :
    mixedInto X Y n w ≫ permMor (X ⊞ Y) n (sortPerm w) =
      (sortIso X Y n w).hom ≫
        (tensorPowMap (biprod.inl : X ⟶ X ⊞ Y) (popCount w) ⊗ₘ
          tensorPowMap (biprod.inr : Y ⟶ X ⊞ Y)
            (n - popCount w)) ≫
        (tensorPowConcat (X ⊞ Y) (popCount w)
          (n - popCount w)).hom ≫
        eqToHom (congrArg (tensorPow A (X ⊞ Y))
          (Nat.add_sub_cancel' (popCount_le w))) :=
  (mixedInto_sorted X Y n w).choose_spec

end SortedBiprod

end Symmetric

end RS
