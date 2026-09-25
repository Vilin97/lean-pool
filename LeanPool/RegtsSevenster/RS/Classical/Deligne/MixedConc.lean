/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.SymPerm

/-!
# Concatenation of tensor powers and the block embedding

`X ^ ⊗ a ⊗ X ^ ⊗ b` reassociates to `X ^ ⊗ (a + b)`, and the
reassociation intertwines the permutation actions: a pair of
permutations acting on the two factors separately corresponds to
their block embedding into `S_{a + b}`.

The block embedding is conjugation by `finSumFinEquiv`, which sends
the `Fin a` summand to the first block `{0, …, a − 1}` by
`Fin.castAdd` and the `Fin b` summand to the last block by
`Fin.natAdd`; so `σ` permutes the first `a` slots and `τ` the last
`b`, matching the order of the tensor factors.

Both the embedding and the intertwiners are multiplicative, so the
intertwining reduces to the generator families `(σ, 1)` and `(1, τ)`.
The first extends by `extPerm` one slot at a time, following the
recursion of the concatenation isomorphism; the second follows the
recursion of `permMor` itself, shifted into the last block — its top
cycle bubbles inside the last block only, which is the content of
the insertion lemma.  The `ℂ`-bilinear extension to the group
algebras then holds on basis permutations and extends linearly.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

universe v u

/-! ## The block embedding of symmetric groups -/

section BlockEmbed

variable {a b : ℕ}

/-- **The block embedding** of `S_a × S_b` into `S_{a + b}`:
`σ` permutes the first `a` slots and `τ` the last `b`.  The
convention is that of `finSumFinEquiv`, which carries the `Fin a`
summand onto `{0, …, a − 1}` by `Fin.castAdd` and the `Fin b`
summand onto `{a, …, a + b − 1}` by `Fin.natAdd`. -/
noncomputable def blockEmbed (σ : Equiv.Perm (Fin a))
    (τ : Equiv.Perm (Fin b)) : Equiv.Perm (Fin (a + b)) :=
  finSumFinEquiv.permCongr (σ.sumCongr τ)

/-- On the first block the embedding acts by `σ`. -/
@[simp]
theorem blockEmbed_castAdd (σ : Equiv.Perm (Fin a))
    (τ : Equiv.Perm (Fin b)) (i : Fin a) :
    blockEmbed σ τ (Fin.castAdd b i) = Fin.castAdd b (σ i) := by
  simp [blockEmbed]

/-- On the last block the embedding acts by `τ`. -/
@[simp]
theorem blockEmbed_natAdd (σ : Equiv.Perm (Fin a))
    (τ : Equiv.Perm (Fin b)) (j : Fin b) :
    blockEmbed σ τ (Fin.natAdd a j) = Fin.natAdd a (τ j) := by
  simp [blockEmbed]

/-- The block embedding of the identities is the identity. -/
@[simp]
theorem blockEmbed_one :
    blockEmbed (1 : Equiv.Perm (Fin a)) (1 : Equiv.Perm (Fin b)) = 1 := by
  refine Equiv.ext fun x => ?_
  induction x using Fin.addCases with
  | left i => simp
  | right j => simp

/-- **The block embedding is multiplicative**: it is a homomorphism
from the product group. -/
theorem blockEmbed_mul (σ σ' : Equiv.Perm (Fin a))
    (τ τ' : Equiv.Perm (Fin b)) :
    blockEmbed (σ * σ') (τ * τ') = blockEmbed σ τ * blockEmbed σ' τ' := by
  refine Equiv.ext fun x => ?_
  induction x using Fin.addCases with
  | left i => simp [Equiv.Perm.mul_apply]
  | right j => simp [Equiv.Perm.mul_apply]

/-- A block embedding splits into its two one-sided factors. -/
theorem blockEmbed_decompose (σ : Equiv.Perm (Fin a))
    (τ : Equiv.Perm (Fin b)) :
    blockEmbed σ τ = blockEmbed σ 1 * blockEmbed 1 τ := by
  rw [← blockEmbed_mul, mul_one, one_mul]

/-- With an empty second block the embedding is the identity
re-indexing. -/
theorem blockEmbed_one_zero (σ : Equiv.Perm (Fin a)) :
    blockEmbed σ (1 : Equiv.Perm (Fin 0)) = σ := by
  refine Equiv.ext fun x => ?_
  induction x using Fin.addCases with
  | left i =>
    rw [blockEmbed_castAdd]
    rfl
  | right j => exact j.elim0

/-- Growing the second block by an unused slot extends the embedding
by fixing the new top slot. -/
theorem blockEmbed_one_succ (σ : Equiv.Perm (Fin a)) :
    blockEmbed σ (1 : Equiv.Perm (Fin (b + 1))) =
      extPerm (blockEmbed σ (1 : Equiv.Perm (Fin b))) := by
  refine Equiv.ext fun x => ?_
  induction x using Fin.addCases with
  | left i =>
    change blockEmbed σ 1 (Fin.castAdd (b + 1) i) =
      extPerm (blockEmbed σ 1) (Fin.castSucc (Fin.castAdd b i))
    rw [blockEmbed_castAdd, extPerm_castSucc, blockEmbed_castAdd]
    rfl
  | right j =>
    induction j using Fin.lastCases with
    | last =>
      change blockEmbed σ 1 (Fin.natAdd a (Fin.last b)) =
        extPerm (blockEmbed σ 1) (Fin.last (a + b))
      rw [blockEmbed_natAdd, extPerm_last]
      rfl
    | cast j =>
      change blockEmbed σ 1 (Fin.natAdd a (Fin.castSucc j)) =
        extPerm (blockEmbed σ 1) (Fin.castSucc (Fin.natAdd a j))
      rw [blockEmbed_natAdd, extPerm_castSucc, blockEmbed_natAdd]
      rfl

/-- The block embedding of `(1, τ)` sends the top slot where `τ`
does, shifted into the last block. -/
theorem topImage_blockEmbed (τ : Equiv.Perm (Fin (b + 1))) :
    topImage (n := a + b) (blockEmbed (a := a) (b := b + 1) 1 τ) =
      Fin.natAdd a (topImage τ) := by
  change blockEmbed (a := a) (b := b + 1) 1 τ
      (Fin.natAdd a (Fin.last b)) =
    Fin.natAdd a (topImage τ)
  rw [blockEmbed_natAdd]
  rfl

/-- Reinsertion above a point of the last block stays inside the
last block. -/
private theorem natAdd_succAbove (q : Fin (b + 1)) (j : Fin b) :
    (Fin.natAdd a q).succAbove (Fin.natAdd a j) =
      Fin.natAdd a (q.succAbove j) := by
  rcases Fin.lt_or_le (Fin.castSucc j) q with h | h
  · have hv : (j : ℕ) < (q : ℕ) := Fin.lt_def.mp h
    have h' : Fin.castSucc (Fin.natAdd a j) < Fin.natAdd a q :=
      Fin.lt_def.mpr (show a + (j : ℕ) < a + (q : ℕ) by omega)
    rw [Fin.succAbove_of_castSucc_lt _ _ h,
      Fin.succAbove_of_castSucc_lt _ _ h']
    rfl
  · have hv : (q : ℕ) ≤ (j : ℕ) := Fin.le_def.mp h
    have h' : Fin.natAdd a q ≤ Fin.castSucc (Fin.natAdd a j) :=
      Fin.le_def.mpr (show a + (q : ℕ) ≤ a + (j : ℕ) by omega)
    rw [Fin.succAbove_of_le_castSucc _ _ h,
      Fin.succAbove_of_le_castSucc _ _ h']
    rfl

/-- The block embedding of `(1, τ)` induces the block embedding of
`(1, restPerm τ)` on the lower slots: the top split of the ambient
permutation happens entirely inside the last block. -/
theorem restPerm_blockEmbed (τ : Equiv.Perm (Fin (b + 1))) :
    restPerm (n := a + b) (blockEmbed (a := a) (b := b + 1) 1 τ) =
      blockEmbed 1 (restPerm τ) := by
  refine Equiv.ext fun j => ?_
  have key : (topImage (n := a + b)
        (blockEmbed (a := a) (b := b + 1) 1 τ)).succAbove
        (blockEmbed (1 : Equiv.Perm (Fin a)) (restPerm τ) j) =
      blockEmbed (1 : Equiv.Perm (Fin a)) τ (Fin.castSucc j) := by
    rw [topImage_blockEmbed]
    induction j using Fin.addCases with
    | left i =>
      have hlt : Fin.castSucc (Fin.castAdd b i) <
          Fin.natAdd a (topImage τ) :=
        Fin.lt_def.mpr (show (i : ℕ) < a + ((topImage τ) : ℕ) by
          have := i.isLt
          omega)
      change (Fin.natAdd a (topImage τ)).succAbove
          (blockEmbed (1 : Equiv.Perm (Fin a)) (restPerm τ)
            (Fin.castAdd b i)) =
        blockEmbed (1 : Equiv.Perm (Fin a)) τ (Fin.castAdd (b + 1) i)
      rw [blockEmbed_castAdd, blockEmbed_castAdd, Equiv.Perm.one_apply,
        Fin.succAbove_of_castSucc_lt _ _ hlt]
      rfl
    | right i =>
      change (Fin.natAdd a (topImage τ)).succAbove
          (blockEmbed (1 : Equiv.Perm (Fin a)) (restPerm τ)
            (Fin.natAdd a i)) =
        blockEmbed (1 : Equiv.Perm (Fin a)) τ
          (Fin.natAdd a (Fin.castSucc i))
      rw [blockEmbed_natAdd, blockEmbed_natAdd, natAdd_succAbove,
        succAbove_restPerm]
  exact Fin.succAbove_right_injective
    ((succAbove_restPerm (blockEmbed (a := a) (b := b + 1) 1 τ)
      j).trans key.symm)

end BlockEmbed

/-! ## The concatenation isomorphism -/

variable {A : Type u}

/-- **The concatenation isomorphism**
`X ^ ⊗ a ⊗ X ^ ⊗ b ≅ X ^ ⊗ (a + b)`, by the recursion of
`tensorPow` itself: the empty second power is absorbed by the right
unitor, and one further factor reassociates off the second power and
whiskers the previous stage. -/
noncomputable def tensorPowConcat [Category.{v} A] [MonoidalCategory A]
    (X : A) (a : ℕ) :
    (b : ℕ) → (tensorPow A X a ⊗ tensorPow A X b ≅ tensorPow A X (a + b))
  | 0 => ρ_ (tensorPow A X a)
  | b + 1 =>
      (α_ (tensorPow A X a) (tensorPow A X b) X).symm ≪≫
        whiskerRightIso (tensorPowConcat X a b) X

/-- Concatenating with the empty power is the right unitor. -/
theorem tensorPowConcat_zero [Category.{v} A] [MonoidalCategory A]
    (X : A) (a : ℕ) :
    tensorPowConcat X a 0 = ρ_ (tensorPow A X a) := rfl

/-- The defining recursion of `tensorPowConcat`. -/
theorem tensorPowConcat_succ [Category.{v} A] [MonoidalCategory A]
    (X : A) (a b : ℕ) :
    tensorPowConcat X a (b + 1) =
      (α_ (tensorPow A X a) (tensorPow A X b) X).symm ≪≫
        whiskerRightIso (tensorPowConcat X a b) X := rfl

/-! ## Passing endomorphisms across one stage

The successor stage of the concatenation is an associator followed
by a whiskering of the previous stage.  Each helper is stated at
general objects and applied by `exact`, so that no tensor-power
arity enters the rewriting.
-/

/-- Two morphisms passed one at a time across `T`. -/
private theorem pull_pair [Category.{v} A]
    {P Q : A} {T : P ⟶ Q} {u v : Q ⟶ Q}
    {u' v' : P ⟶ P} (hu : T ≫ u = u' ≫ T) (hv : T ≫ v = v' ≫ T) :
    T ≫ (u ≫ v) = (u' ≫ v') ≫ T := by
  rw [← Category.assoc, hu, Category.assoc, hv, ← Category.assoc]

/-- Identities pass across `T`. -/
private theorem id_pass [Category.{v} A]
    {P Q : A} (T : P ⟶ Q) :
    T ≫ 𝟙 Q = 𝟙 P ≫ T := by
  rw [Category.comp_id, Category.id_comp]

/-- A morphism of the second tensorand passed across one stage of
the concatenation. -/
private theorem concat_left_glue [Category.{v} A] [MonoidalCategory A]
    {P Q R Y : A} (c : P ⊗ Q ⟶ R)
    (u : R ⟶ R) (g : Q ⟶ Q) (h : c ≫ u = (P ◁ g) ≫ c) :
    ((α_ P Q Y).inv ≫ (c ▷ Y)) ≫ (u ▷ Y) =
      (P ◁ (g ▷ Y)) ≫ (α_ P Q Y).inv ≫ (c ▷ Y) := by
  rw [Category.assoc, ← MonoidalCategory.comp_whiskerRight, h,
    MonoidalCategory.comp_whiskerRight,
    ← MonoidalCategory.associator_inv_naturality_middle_assoc]

/-- A morphism of the first tensorand passed across one stage of
the concatenation. -/
private theorem concat_right_glue [Category.{v} A] [MonoidalCategory A]
    {P Q R Y : A} (c : P ⊗ Q ⟶ R)
    (u : R ⟶ R) (f : P ⟶ P) (h : c ≫ u = (f ▷ Q) ≫ c) :
    ((α_ P Q Y).inv ≫ (c ▷ Y)) ≫ (u ▷ Y) =
      (f ▷ (Q ⊗ Y)) ≫ (α_ P Q Y).inv ≫ (c ▷ Y) := by
  rw [Category.assoc, ← MonoidalCategory.comp_whiskerRight, h,
    MonoidalCategory.comp_whiskerRight,
    ← MonoidalCategory.associator_inv_naturality_left_assoc]

section Symmetric

/-- The braiding conjugate defining `swapTop` commutes with a doubly
whiskered morphism of the base, at general objects. -/
private theorem swap_conj_whisker
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    {P R : A} (Y : A) (g : P ⟶ R) :
    ((g ▷ Y) ▷ Y) ≫
        ((α_ R Y Y).hom ≫ (R ◁ (β_ Y Y).hom) ≫ (α_ R Y Y).inv) =
      ((α_ P Y Y).hom ≫ (P ◁ (β_ Y Y).hom) ≫ (α_ P Y Y).inv) ≫
        ((g ▷ Y) ▷ Y) := by
  rw [MonoidalCategory.associator_naturality_left_assoc,
    ← MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.associator_inv_naturality_left]
  simp only [Category.assoc]

/-- The structural half of the swap intertwining: conjugating the
braiding at the joint base against conjugating it inside the second
tensorand.  Pure coherence and naturality, discharged by
`monoidal`. -/
private theorem concat_swap_structural
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (P Q Y : A) :
    (α_ P (Q ⊗ Y) Y).inv ≫ ((α_ P Q Y).inv ▷ Y) ≫
        (α_ (P ⊗ Q) Y Y).hom ≫ ((P ⊗ Q) ◁ (β_ Y Y).hom) ≫
        (α_ (P ⊗ Q) Y Y).inv =
      (P ◁ ((α_ Q Y Y).hom ≫ (Q ◁ (β_ Y Y).hom) ≫ (α_ Q Y Y).inv)) ≫
        (α_ P (Q ⊗ Y) Y).inv ≫ ((α_ P Q Y).inv ▷ Y) := by
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
  monoidal

/-- The swap intertwining at general objects: the top braiding after
two stages of concatenation is the whiskered top braiding of the
second tensorand. -/
private theorem concat_swap_aux
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    {P Q R : A} (Y : A) (c : P ⊗ Q ⟶ R) :
    ((α_ P (Q ⊗ Y) Y).inv ≫ (((α_ P Q Y).inv ≫ (c ▷ Y)) ▷ Y)) ≫
        ((α_ R Y Y).hom ≫ (R ◁ (β_ Y Y).hom) ≫ (α_ R Y Y).inv) =
      (P ◁ ((α_ Q Y Y).hom ≫ (Q ◁ (β_ Y Y).hom) ≫ (α_ Q Y Y).inv)) ≫
        (α_ P (Q ⊗ Y) Y).inv ≫ (((α_ P Q Y).inv ≫ (c ▷ Y)) ▷ Y) := by
  rw [MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [swap_conj_whisker Y c]
  simp only [Category.assoc]
  rw [reassoc_of% (concat_swap_structural P Q Y)]

/-- **The concatenation isomorphism intertwines the top braiding**
of the last block: braiding the top two slots of `X ^ ⊗ (a + b + 2)`
corresponds to braiding the top two slots of the second factor. -/
theorem tensorPowConcat_swapTop
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (a b : ℕ) :
    (tensorPowConcat X a (b + 2)).hom ≫ swapTop X (a + b) =
      (tensorPow A X a ◁ swapTop X b) ≫ (tensorPowConcat X a (b + 2)).hom :=
  concat_swap_aux X ((tensorPowConcat X a b).hom)

/-- **The concatenation isomorphism intertwines bubbling** inside
the last block: as long as the insertion distance stays within the
second factor, inserting the top slot commutes with concatenation. -/
theorem tensorPowConcat_insertTop
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (a : ℕ) :
    ∀ b k : ℕ, k ≤ b →
      (tensorPowConcat X a (b + 1)).hom ≫ insertTop X (a + b) k =
        (tensorPow A X a ◁ insertTop X b k) ≫
          (tensorPowConcat X a (b + 1)).hom := by
  intro b
  induction b with
  | zero =>
    intro k hk
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    rw [insertTop_zero, insertTop_zero, MonoidalCategory.whiskerLeft_id]
    exact id_pass _
  | succ b ihb =>
    intro k hk
    cases k with
    | zero =>
      rw [insertTop_zero, insertTop_zero,
        MonoidalCategory.whiskerLeft_id]
      exact id_pass _
    | succ k =>
      have hin : insertTop (A := A) X (a + (b + 1)) (k + 1) =
          swapTop X (a + b) ≫ (insertTop X (a + b) k ▷ X) :=
        insertTop_succ X (a + b) k
      have hwl : tensorPow A X a ◁ insertTop (A := A) X (b + 1) (k + 1) =
          (tensorPow A X a ◁ swapTop X b) ≫
            (tensorPow A X a ◁ (insertTop X b k ▷ X)) := by
        rw [insertTop_succ X b k]
        exact MonoidalCategory.whiskerLeft_comp _ _ _
      have hswap := tensorPowConcat_swapTop X a b
      have hstep : (tensorPowConcat X a (b + 1 + 1)).hom ≫
            (insertTop X (a + b) k ▷ X) =
          (tensorPow A X a ◁ (insertTop X b k ▷ X)) ≫
            (tensorPowConcat X a (b + 1 + 1)).hom :=
        concat_left_glue ((tensorPowConcat X a (b + 1)).hom)
          (insertTop X (a + b) k) (insertTop X b k)
          (ihb k (Nat.le_of_succ_le_succ hk))
      rw [hin, hwl]
      exact pull_pair hswap hstep

/-- **The intertwining on the first generator family**: a
permutation of the first block acts on the first tensor factor
alone. -/
theorem tensorPowConcat_permMor_fst
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (a : ℕ)
    (σ : Equiv.Perm (Fin a)) :
    ∀ b : ℕ,
      (tensorPowConcat X a b).hom ≫ permMor X (a + b) (blockEmbed σ 1) =
        (permMor X a σ ▷ tensorPow A X b) ≫ (tensorPowConcat X a b).hom := by
  intro b
  induction b with
  | zero =>
    rw [blockEmbed_one_zero]
    exact (MonoidalCategory.rightUnitor_naturality (permMor X a σ)).symm
  | succ b ih =>
    rw [blockEmbed_one_succ]
    have hpm : permMor X (a + (b + 1))
          (extPerm (blockEmbed σ (1 : Equiv.Perm (Fin b)))) =
        permMor X (a + b) (blockEmbed σ 1) ▷ X :=
      permMor_extPerm X (a + b) (blockEmbed σ 1)
    rw [hpm]
    exact concat_right_glue ((tensorPowConcat X a b).hom)
      (permMor X (a + b) (blockEmbed σ 1)) (permMor X a σ) ih

/-- **The intertwining on the second generator family**: a
permutation of the last block acts on the second tensor factor
alone.  The proof mirrors the recursion of `permMor`, shifted into
the last block by `restPerm_blockEmbed` and `topImage_blockEmbed`. -/
theorem tensorPowConcat_permMor_snd
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (a : ℕ) :
    ∀ (b : ℕ) (τ : Equiv.Perm (Fin b)),
      (tensorPowConcat X a b).hom ≫ permMor X (a + b) (blockEmbed 1 τ) =
        (tensorPow A X a ◁ permMor X b τ) ≫ (tensorPowConcat X a b).hom := by
  intro b
  induction b with
  | zero =>
    intro τ
    have hτ : τ = 1 := Equiv.ext fun x => x.elim0
    rw [hτ, blockEmbed_one, permMor_one, permMor_one,
      MonoidalCategory.whiskerLeft_id, Category.comp_id, Category.id_comp]
  | succ b ih =>
    intro τ
    have hs := permMor_succ X (a + b)
      (blockEmbed (a := a) (b := b + 1) 1 τ)
    rw [restPerm_blockEmbed, topImage_blockEmbed] at hs
    have harith : a + b - ((Fin.natAdd a (topImage τ) :
          Fin (a + b + 1)) : ℕ) =
        b - ((topImage τ : Fin (b + 1)) : ℕ) := by
      change a + b - (a + ((topImage τ : Fin (b + 1)) : ℕ)) = _
      omega
    rw [harith] at hs
    have hs' : permMor X (a + (b + 1))
          (blockEmbed (a := a) (b := b + 1) 1 τ) =
        (permMor X (a + b) (blockEmbed 1 (restPerm τ)) ▷ X) ≫
          insertTop X (a + b) (b - ((topImage τ : Fin (b + 1)) : ℕ)) := hs
    have h2 : (tensorPowConcat X a (b + 1)).hom ≫
          (permMor X (a + b) (blockEmbed 1 (restPerm τ)) ▷ X) =
        (tensorPow A X a ◁ (permMor X b (restPerm τ) ▷ X)) ≫
          (tensorPowConcat X a (b + 1)).hom :=
      concat_left_glue ((tensorPowConcat X a b).hom)
        (permMor X (a + b) (blockEmbed 1 (restPerm τ)))
        (permMor X b (restPerm τ)) (ih (restPerm τ))
    have h3 : (tensorPowConcat X a (b + 1)).hom ≫
          insertTop X (a + b) (b - ((topImage τ : Fin (b + 1)) : ℕ)) =
        (tensorPow A X a ◁
            insertTop X b (b - ((topImage τ : Fin (b + 1)) : ℕ))) ≫
          (tensorPowConcat X a (b + 1)).hom :=
      tensorPowConcat_insertTop X a b _ (Nat.sub_le _ _)
    have hwl : tensorPow A X a ◁ permMor X (b + 1) τ =
        (tensorPow A X a ◁ (permMor X b (restPerm τ) ▷ X)) ≫
          (tensorPow A X a ◁
            insertTop X b (b - ((topImage τ : Fin (b + 1)) : ℕ))) := by
      rw [permMor_succ X b τ]
      exact MonoidalCategory.whiskerLeft_comp _ _ _
    rw [hs', hwl]
    exact pull_pair h2 h3

/-- **The concatenation isomorphism intertwines the block
embedding**: under `tensorPowConcat`, the action of
`blockEmbed σ τ` on `X ^ ⊗ (a + b)` is the tensor product of the
actions of `σ` and `τ` on the two factors. -/
theorem tensorPowConcat_permMor
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) {a b : ℕ}
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    (tensorPowConcat X a b).hom ≫ permMor X (a + b) (blockEmbed σ τ) =
      (permMor X a σ ⊗ₘ permMor X b τ) ≫ (tensorPowConcat X a b).hom := by
  rw [blockEmbed_decompose, permMor_mul, MonoidalCategory.tensorHom_def']
  exact pull_pair (tensorPowConcat_permMor_snd X a b τ)
    (tensorPowConcat_permMor_fst X a σ b)

end Symmetric

/-! ## The linear extension -/

section Linear

/-- The first-block embedding as a monoid homomorphism. -/
noncomputable def blockEmbedFstHom (a b : ℕ) :
    Equiv.Perm (Fin a) →* Equiv.Perm (Fin (a + b)) where
  toFun σ := blockEmbed σ 1
  map_one' := blockEmbed_one
  map_mul' σ σ' := by rw [← blockEmbed_mul, one_mul]

/-- The second-block embedding as a monoid homomorphism. -/
noncomputable def blockEmbedSndHom (a b : ℕ) :
    Equiv.Perm (Fin b) →* Equiv.Perm (Fin (a + b)) where
  toFun τ := blockEmbed 1 τ
  map_one' := blockEmbed_one
  map_mul' τ τ' := by rw [← blockEmbed_mul, one_mul]

/-- **The block embedding of group algebras**: the `ℂ`-bilinear
extension of `blockEmbed`, carrying a pair of group-algebra elements
to the product of their one-sided embeddings. -/
noncomputable def blockAlgEmbed {a b : ℕ} (x : SymGroupAlgebra a)
    (y : SymGroupAlgebra b) : SymGroupAlgebra (a + b) :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b) x *
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b) y

/-- On basis permutations the algebra embedding is the block
embedding. -/
theorem blockAlgEmbed_single {a b : ℕ} (σ : Equiv.Perm (Fin a))
    (τ : Equiv.Perm (Fin b)) (c d : ℂ) :
    blockAlgEmbed (MonoidAlgebra.single σ c)
        (MonoidAlgebra.single τ d) =
      MonoidAlgebra.single (blockEmbed σ τ) (c * d) := by
  have hL : MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b)
      (MonoidAlgebra.single σ c) =
      MonoidAlgebra.single (blockEmbed σ 1) c := by
    change MonoidAlgebra.mapDomain _ (MonoidAlgebra.single σ c) = _
    exact MonoidAlgebra.mapDomain_single
  have hR : MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b)
      (MonoidAlgebra.single τ d) =
      MonoidAlgebra.single (blockEmbed 1 τ) d := by
    change MonoidAlgebra.mapDomain _ (MonoidAlgebra.single τ d) = _
    exact MonoidAlgebra.mapDomain_single
  unfold blockAlgEmbed
  rw [hL, hR, MonoidAlgebra.single_mul_single, ← blockEmbed_decompose]

/-- The algebra embedding is additive in the first argument. -/
theorem blockAlgEmbed_add_fst {a b : ℕ} (x x' : SymGroupAlgebra a)
    (y : SymGroupAlgebra b) :
    blockAlgEmbed (x + x') y = blockAlgEmbed x y + blockAlgEmbed x' y := by
  unfold blockAlgEmbed
  rw [map_add, add_mul]

/-- The algebra embedding is homogeneous in the first argument. -/
theorem blockAlgEmbed_smul_fst {a b : ℕ} (r : ℂ) (x : SymGroupAlgebra a)
    (y : SymGroupAlgebra b) :
    blockAlgEmbed (r • x) y = r • blockAlgEmbed x y := by
  unfold blockAlgEmbed
  rw [map_smul, smul_mul_assoc]

/-- The algebra embedding is additive in the second argument. -/
theorem blockAlgEmbed_add_snd {a b : ℕ} (x : SymGroupAlgebra a)
    (y y' : SymGroupAlgebra b) :
    blockAlgEmbed x (y + y') = blockAlgEmbed x y + blockAlgEmbed x y' := by
  unfold blockAlgEmbed
  rw [map_add, mul_add]

/-- The algebra embedding is homogeneous in the second argument. -/
theorem blockAlgEmbed_smul_snd {a b : ℕ} (r : ℂ) (x : SymGroupAlgebra a)
    (y : SymGroupAlgebra b) :
    blockAlgEmbed x (r • y) = r • blockAlgEmbed x y := by
  unfold blockAlgEmbed
  rw [map_smul, mul_smul_comm]

/-- The tensor product of morphisms is homogeneous in the second
factor. -/
private theorem tensorHom_smul
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    {P Q R S : A} (f : P ⟶ Q) (r : ℂ)
    (g : R ⟶ S) : f ⊗ₘ (r • g) = r • (f ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def,
    MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]

/-- The tensor product of morphisms is homogeneous in the first
factor. -/
private theorem smul_tensorHom
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    {P Q R S : A} (r : ℂ) (f : P ⟶ Q)
    (g : R ⟶ S) : (r • f) ⊗ₘ g = r • (f ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_def, MonoidalCategory.tensorHom_def,
    MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

/-- Intertwining a tensor product across `T` is closed under sums in
the second factor.  Stated at general objects and applied by
`exact`, so that the endomorphism-ring structure never enters the
rewriting. -/
private theorem tensor_add_glue
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A]
    {P Q R : A} {T : P ⊗ Q ⟶ R}
    {u v : R ⟶ R} {f : P ⟶ P} {g h : Q ⟶ Q}
    (hu : T ≫ u = (f ⊗ₘ g) ≫ T) (hv : T ≫ v = (f ⊗ₘ h) ≫ T) :
    T ≫ (u + v) = (f ⊗ₘ (g + h)) ≫ T := by
  rw [MonoidalPreadditive.tensor_add, Preadditive.comp_add,
    Preadditive.add_comp, hu, hv]

/-- Intertwining a tensor product across `T` is closed under sums in
the first factor.  Stated at general objects and applied by
`exact`. -/
private theorem add_tensor_glue
    [Category.{v} A] [MonoidalCategory A] [Preadditive A]
    [MonoidalPreadditive A]
    {P Q R : A} {T : P ⊗ Q ⟶ R}
    {u v : R ⟶ R} {f g : P ⟶ P} {h : Q ⟶ Q}
    (hu : T ≫ u = (f ⊗ₘ h) ≫ T) (hv : T ≫ v = (g ⊗ₘ h) ≫ T) :
    T ≫ (u + v) = ((f + g) ⊗ₘ h) ≫ T := by
  rw [MonoidalPreadditive.add_tensor, Preadditive.comp_add,
    Preadditive.add_comp, hu, hv]

/-- Intertwining a tensor product across `T` is closed under scalars
in the second factor.  Stated at general objects and applied by
`exact`. -/
private theorem tensor_smul_glue
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    {P Q R : A} {T : P ⊗ Q ⟶ R}
    {u : R ⟶ R} {f : P ⟶ P} {g : Q ⟶ Q} (r : ℂ)
    (h : T ≫ u = (f ⊗ₘ g) ≫ T) :
    T ≫ (r • u) = (f ⊗ₘ (r • g)) ≫ T := by
  rw [tensorHom_smul, Linear.comp_smul, Linear.smul_comp, h]

/-- Intertwining a tensor product across `T` is closed under scalars
in the first factor.  Stated at general objects and applied by
`exact`. -/
private theorem smul_tensor_glue
    [Category.{v} A] [MonoidalCategory A] [Preadditive A] [Linear ℂ A]
    [MonoidalPreadditive A] [MonoidalLinear ℂ A]
    {P Q R : A} {T : P ⊗ Q ⟶ R}
    {u : R ⟶ R} {f : P ⟶ P} {g : Q ⟶ Q} (r : ℂ)
    (h : T ≫ u = (f ⊗ₘ g) ≫ T) :
    T ≫ (r • u) = ((r • f) ⊗ₘ g) ≫ T := by
  rw [smul_tensorHom, Linear.comp_smul, Linear.smul_comp, h]

/-- **The concatenation isomorphism intertwines the block embedding
of group algebras**: the `ℂ`-bilinear extension of the intertwining
on basis permutations.  Both sides are bilinear in `(x, y)`, so the
statement reduces to `tensorPowConcat_permMor`. -/
theorem tensorPowConcat_permAlg
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A] [MonoidalPreadditive A]
    [MonoidalLinear ℂ A]
    (X : A) {a b : ℕ}
    (x : SymGroupAlgebra a) (y : SymGroupAlgebra b) :
    (tensorPowConcat X a b).hom ≫ permAlg X (a + b) (blockAlgEmbed x y) =
      (permAlg X a x ⊗ₘ permAlg X b y) ≫ (tensorPowConcat X a b).hom := by
  induction x using MonoidAlgebra.induction_on with
  | of σ =>
    induction y using MonoidAlgebra.induction_on with
    | of τ =>
      rw [show (MonoidAlgebra.of ℂ (Equiv.Perm (Fin a))) σ =
          MonoidAlgebra.single σ (1 : ℂ) from rfl,
        show (MonoidAlgebra.of ℂ (Equiv.Perm (Fin b))) τ =
          MonoidAlgebra.single τ (1 : ℂ) from rfl,
        blockAlgEmbed_single, one_mul, permAlg_single, permAlg_single,
        permAlg_single]
      exact tensorPowConcat_permMor X σ τ
    | add y₁ y₂ hy₁ hy₂ =>
      rw [blockAlgEmbed_add_snd, map_add, map_add]
      exact tensor_add_glue hy₁ hy₂
    | smul r y' hy =>
      rw [blockAlgEmbed_smul_snd, map_smul, map_smul]
      exact tensor_smul_glue r hy
  | add x₁ x₂ hx₁ hx₂ =>
    rw [blockAlgEmbed_add_fst, map_add, map_add]
    exact add_tensor_glue hx₁ hx₂
  | smul r x' hx =>
    rw [blockAlgEmbed_smul_fst, map_smul, map_smul]
    exact smul_tensor_glue r hx

end Linear

end RS
