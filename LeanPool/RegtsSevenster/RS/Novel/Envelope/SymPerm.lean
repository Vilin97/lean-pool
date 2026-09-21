/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.TensorPow
import LeanPool.RegtsSevenster.RS.Common.PermTopSplit
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.SchurPackage

/-!
# The symmetric-group action on a tensor power

In a symmetric monoidal category, the tensor power `X ^ ⊗ n` carries
an action of `S_n` permuting its factors.  Mathlib has the monoidal
coherence theorem but not the symmetric one, and no presentation of
`S_n`, so the action is built here by an explicit recursion that
makes no choice of word: the factor in the top slot is bubbled down
to its destination by adjacent braidings (`insertTop`), and the rest
is handled by the recursion at one lower arity (`permMor`).

The two primitives are the adjacent braiding on the top two slots
(`swapTop`) and the insertion cycle (`insertTop`).  Functoriality of
the recursion follows from mere generation of `S_n` by the adjacent
transpositions — no presentation is needed — and the linear
structure then turns the action into the algebra map `permAlg` that
a tower's representation field asks for.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {A : Type u}

/-! ## The adjacent braiding on the top two slots -/

/-- **The top transposition**: braid the last two factors of
`X ^ ⊗ (n + 2)`.  Reassociating exposes the last two tensorands, the
braiding exchanges them, and the associator is undone. -/
noncomputable def swapTop
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) :
    tensorPow A X (n + 2) ⟶ tensorPow A X (n + 2) :=
  (α_ (tensorPow A X n) X X).hom ≫
    (tensorPow A X n ◁ (β_ X X).hom) ≫
    (α_ (tensorPow A X n) X X).inv

/-- The top transposition is an involution: the braiding of a
symmetric category squares to the identity. -/
@[simp]
theorem swapTop_swapTop
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) :
    swapTop X n ≫ swapTop X n = 𝟙 (tensorPow A X (n + 2)) := by
  unfold swapTop
  slice_lhs 3 4 => rw [Iso.inv_hom_id]
  rw [Category.id_comp]
  slice_lhs 2 3 => rw [← MonoidalCategory.whiskerLeft_comp,
    SymmetricCategory.symmetry, MonoidalCategory.whiskerLeft_id]
  rw [Category.id_comp, Iso.hom_inv_id]

/-! ## Bubbling the top factor down -/

/-- **The insertion cycle**: move the factor in the top slot of
`X ^ ⊗ (n + 1)` down to slot `p`, shifting slots `p, …, n − 1` up by
one.  It is defined by bubbling one slot at a time, so no word is
chosen: `insertTop X n n` is the identity, and each further step
composes one more top transposition, whiskered by the factors above
it.  The recursion is on the gap `n - p`. -/
noncomputable def insertTop
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) : (n : ℕ) → (k : ℕ) →
    (tensorPow A X (n + 1) ⟶ tensorPow A X (n + 1))
  | _, 0 => 𝟙 _
  | 0, _ + 1 => 𝟙 _
  | n + 1, k + 1 =>
      swapTop X n ≫ (insertTop X n k ▷ X)

/-- Bubbling by no steps is the identity. -/
@[simp]
theorem insertTop_zero
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) :
    insertTop (A := A) X n 0 = 𝟙 _ := by
  cases n <;> rfl

/-- At arity one there is nothing to bubble. -/
@[simp]
theorem insertTop_of_zero
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (k : ℕ) :
    insertTop (A := A) X 0 k = 𝟙 _ := by
  cases k <;> rfl

/-- One bubbling step: braid the top factor past the one below it,
then continue bubbling the result inside the lower part. -/
theorem insertTop_succ
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n k : ℕ) :
    insertTop (A := A) X (n + 1) (k + 1) =
      swapTop X n ≫ (insertTop X n k ▷ X) := rfl

/-- Bubbling down by one step is the top swap. -/
@[simp]
theorem insertTop_one
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) :
    insertTop (A := A) X (n + 1) 1 = swapTop X n := by
  rw [insertTop_succ, insertTop_zero, MonoidalCategory.id_whiskerRight]
  exact Category.comp_id _

/-! ## Disjoint slots commute

The top braiding touches only the top two slots, so it commutes with
anything acting on the factors below them.  This is what lets the
recursion be reorganised when a transposition and a permutation act
on disjoint parts of a tensor power.
-/

/-- **The top braiding commutes with morphisms below it.**  The
braiding touches only the top two slots, so a morphism of the factors
below them passes through.  The computation is done at a general
object, which keeps the tensor power's arity out of the rewrites. -/
theorem swapTop_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ)
    (f : tensorPow A X n ⟶ tensorPow A X n) :
    ((f ▷ X) ▷ X) ≫ swapTop X n = swapTop X n ≫ ((f ▷ X) ▷ X) := by
  have key : ∀ (P : A) (g : P ⟶ P),
      ((g ▷ X) ▷ X) ≫
          ((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) =
        ((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) ≫
          ((g ▷ X) ▷ X) := by
    intro P g
    rw [MonoidalCategory.associator_naturality_left_assoc,
      ← MonoidalCategory.whisker_exchange_assoc,
      MonoidalCategory.associator_inv_naturality_left]
    simp only [Category.assoc]
  exact key (tensorPow A X n) f

/-! ### The braid relation

Two adjacent top braidings satisfy the braid relation.  Reassociating
all three tensorands off the base turns both sides into the base
whiskered onto a morphism of `X ⊗ (X ⊗ X)`, where the relation is
Mathlib's `yang_baxter` at three copies of `X`; the reassociation
itself is structural and is discharged by `monoidal`.
-/

/-- The full reassociation of three tensorands off a base. -/
private noncomputable def assoc3 [Category.{v} A] [MonoidalCategory A]
    (P X : A) :
    ((P ⊗ X) ⊗ X) ⊗ X ≅ P ⊗ (X ⊗ (X ⊗ X)) :=
  (α_ (P ⊗ X) X X) ≪≫ (α_ P X (X ⊗ X))

/-- Braiding the top two tensorands, reassociated off the base. -/
private theorem braid_upper
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (P X : A) :
    ((α_ (P ⊗ X) X X).hom ≫ ((P ⊗ X) ◁ (β_ X X).hom) ≫
        (α_ (P ⊗ X) X X).inv)
      = (assoc3 P X).hom ≫ (P ◁ (X ◁ (β_ X X).hom)) ≫
        (assoc3 P X).inv := by
  simp only [assoc3, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  monoidal

/-- Braiding the middle two tensorands, reassociated off the base. -/
private theorem braid_lower
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (P X : A) :
    (((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) ▷ X)
      = (assoc3 P X).hom ≫ (P ◁ ((α_ X X X).inv ≫
          ((β_ X X).hom ▷ X) ≫ (α_ X X X).hom)) ≫ (assoc3 P X).inv := by
  simp only [assoc3, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  monoidal

/-- **The braid relation** for two adjacent top braidings. -/
theorem swapTop_braid
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) :
    swapTop X (n + 1) ≫ (swapTop X n ▷ X) ≫ swapTop X (n + 1) =
      (swapTop X n ▷ X) ≫ swapTop X (n + 1) ≫ (swapTop X n ▷ X) := by
  have key : ∀ P : A,
      ((α_ (P ⊗ X) X X).hom ≫ ((P ⊗ X) ◁ (β_ X X).hom) ≫
          (α_ (P ⊗ X) X X).inv) ≫
        (((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) ▷ X) ≫
        ((α_ (P ⊗ X) X X).hom ≫ ((P ⊗ X) ◁ (β_ X X).hom) ≫
          (α_ (P ⊗ X) X X).inv) =
      (((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) ▷ X) ≫
        ((α_ (P ⊗ X) X X).hom ≫ ((P ⊗ X) ◁ (β_ X X).hom) ≫
          (α_ (P ⊗ X) X X).inv) ≫
        (((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫
          (α_ P X X).inv) ▷ X) := by
    intro P
    have hbr : (X ◁ (β_ X X).hom) ≫ (α_ X X X).inv ≫
          ((β_ X X).hom ▷ X) ≫ (α_ X X X).hom ≫ (X ◁ (β_ X X).hom) =
        (α_ X X X).inv ≫ ((β_ X X).hom ▷ X) ≫ (α_ X X X).hom ≫
          (X ◁ (β_ X X).hom) ≫ (α_ X X X).inv ≫
          ((β_ X X).hom ▷ X) ≫ (α_ X X X).hom :=
      (BraidedCategory.yang_baxter X X X).symm
    rw [braid_upper P X, braid_lower P X]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    congr 1
    rw [← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc]
    simp only [Category.assoc, hbr, MonoidalCategory.whiskerLeft_comp]
  exact key (tensorPow A X n)

/-! ### The two bubblings and the braiding

The identity the action's functoriality rests on: precomposing a pair
of bubblings with the top braiding exchanges them.  The first case is
an induction on the arity, whose step is the braid relation together
with the fact that the braiding commutes with what lies below it; the
second case follows from the first because the braiding is an
involution.
-/

private theorem id_sandwich [Category.{v} A]
    {P Q : A} (f : P ⟶ Q) :
    f ≫ 𝟙 Q ≫ 𝟙 Q = 𝟙 P ≫ f := by simp

private theorem comp_id_id_comp [Category.{v} A]
    {P Q R : A} (f : P ⟶ Q) (g : Q ⟶ R) :
    f ≫ g ≫ 𝟙 R = 𝟙 P ≫ f ≫ g := by simp

private theorem whisker_comp₂ [Category.{v} A] [MonoidalCategory A]
    {P Q R : A} (f : P ⟶ Q) (g : Q ⟶ R) (Y : A) :
    (f ≫ g) ▷ Y = (f ▷ Y) ≫ (g ▷ Y) :=
  MonoidalCategory.comp_whiskerRight f g Y

private theorem whisker_comp₃ [Category.{v} A] [MonoidalCategory A]
    {P Q R S : A} (f : P ⟶ Q) (g : Q ⟶ R)
    (h : R ⟶ S) (Y : A) :
    (f ≫ g ≫ h) ▷ Y = (f ▷ Y) ≫ (g ▷ Y) ≫ (h ▷ Y) := by
  rw [whisker_comp₂, whisker_comp₂]

private theorem braid_shuffle [Category.{v} A]
    {P : A} {s t F G U : P ⟶ P}
    (hbr : s ≫ t ≫ s = t ≫ s ≫ t)
    (hF : F ≫ s = s ≫ F) (hG : G ≫ s = s ≫ G)
    (hih : t ≫ F ≫ U = G ≫ t ≫ F) :
    s ≫ (t ≫ F) ≫ (s ≫ U) = (t ≫ G) ≫ (s ≫ t ≫ F) := by
  calc s ≫ (t ≫ F) ≫ (s ≫ U)
      = s ≫ t ≫ (F ≫ s) ≫ U := by simp only [Category.assoc]
    _ = s ≫ t ≫ (s ≫ F) ≫ U := by rw [hF]
    _ = (s ≫ t ≫ s) ≫ F ≫ U := by simp only [Category.assoc]
    _ = (t ≫ s ≫ t) ≫ F ≫ U := by rw [hbr]
    _ = t ≫ s ≫ t ≫ F ≫ U := by simp only [Category.assoc]
    _ = t ≫ s ≫ G ≫ t ≫ F := by rw [hih]
    _ = t ≫ (s ≫ G) ≫ t ≫ F := by simp only [Category.assoc]
    _ = t ≫ (G ≫ s) ≫ t ≫ F := by rw [hG]
    _ = (t ≫ G) ≫ (s ≫ t ≫ F) := by simp only [Category.assoc]

/-- **The braid identity, first case**: when the top factor is
bubbled at least as far as the one below it, the two bubblings and
the braiding rearrange with the destinations shifted by one. -/
theorem insertTop_braid_le
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) :
    ∀ (n a b : ℕ), b ≤ a → a ≤ n →
      swapTop X n ≫ (insertTop X n a ▷ X) ≫ insertTop X (n + 1) b =
        (insertTop X n b ▷ X) ≫ insertTop X (n + 1) (a + 1) := by
  intro n
  induction n with
  | zero =>
    intro a b hba han
    obtain rfl : a = 0 := Nat.le_zero.mp han
    obtain rfl : b = 0 := Nat.le_zero.mp hba
    simp only [Nat.zero_add, insertTop_zero, insertTop_one,
      MonoidalCategory.id_whiskerRight]
    exact id_sandwich (swapTop X 0)
  | succ n' ih =>
    intro a b hba han
    match b, a, hba with
    | 0, a, _ =>
      simp only [insertTop_zero, MonoidalCategory.id_whiskerRight,
        insertTop_succ]
      exact comp_id_id_comp _ _
    | Nat.succ b₀, Nat.succ a', hba =>
      have hb : b₀ ≤ a' := by omega
      have ha : a' ≤ n' := by omega
      have e3 : (insertTop X (n' + 1) (a' + 1) ▷ X)
          = (swapTop X n' ▷ X) ≫ ((insertTop X n' a' ▷ X) ▷ X) :=
        whisker_comp₂ _ _ X
      have e4 : (insertTop X (n' + 1) (b₀ + 1) ▷ X)
          = (swapTop X n' ▷ X) ≫ ((insertTop X n' b₀ ▷ X) ▷ X) :=
        whisker_comp₂ _ _ X
      have hih : (swapTop X n' ▷ X) ≫
            ((insertTop X n' a' ▷ X) ▷ X) ≫
              (insertTop X (n' + 1) b₀ ▷ X) =
          ((insertTop X n' b₀ ▷ X) ▷ X) ≫
            ((swapTop X n' ▷ X) ≫ ((insertTop X n' a' ▷ X) ▷ X)) := by
        refine (whisker_comp₃ (swapTop X n') (insertTop X n' a' ▷ X)
          (insertTop X (n' + 1) b₀) X).symm.trans ?_
        refine (congrArg (fun m => m ▷ X) (ih a' b₀ hb ha)).trans ?_
        refine (whisker_comp₂ (insertTop X n' b₀ ▷ X)
          (insertTop X (n' + 1) (a' + 1)) X).trans ?_
        exact congrArg (fun m => ((insertTop X n' b₀ ▷ X) ▷ X) ≫ m) e3
      show swapTop X (n' + 1) ≫ (insertTop X (n' + 1) (a' + 1) ▷ X) ≫
          (swapTop X (n' + 1) ≫ (insertTop X (n' + 1) b₀ ▷ X))
        = (insertTop X (n' + 1) (b₀ + 1) ▷ X) ≫
          (swapTop X (n' + 1) ≫ (insertTop X (n' + 1) (a' + 1) ▷ X))
      rw [e3, e4]
      exact braid_shuffle (swapTop_braid X n')
        (swapTop_whiskerRight X (n' + 1) (insertTop X n' a'))
        (swapTop_whiskerRight X (n' + 1) (insertTop X n' b₀)) hih

private theorem cancel_invol [Category.{v} A]
    {P : A} {s : P ⟶ P} (hs : s ≫ s = 𝟙 P)
    {Q : A} (f : P ⟶ Q) : s ≫ s ≫ f = f := by
  rw [← Category.assoc, hs, Category.id_comp]

/-- **The braid identity, second case**: when the top factor is
inserted above the one below it, the two bubblings exchange with the
braiding the other way round.  It follows from the first case and the
involutivity of the braiding. -/
theorem insertTop_braid_lt
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n a b₀ : ℕ) (hab : a ≤ b₀)
    (hb : b₀ ≤ n) :
    swapTop X n ≫ (insertTop X n a ▷ X) ≫ insertTop X (n + 1) (b₀ + 1) =
      (insertTop X n b₀ ▷ X) ≫ insertTop X (n + 1) a := by
  have hA := insertTop_braid_le X n b₀ a hab hb
  exact (congrArg (fun m => swapTop X n ≫ m) hA.symm).trans
    (cancel_invol (swapTop_swapTop X n) _)

/-! ## The action

A permutation acts by routing the factor in each slot to the slot it
names.  The recursion splits off the top slot: the lower `n` factors
are permuted by `restPerm σ`, which places them in their compressed
target slots, and the top factor is then bubbled down into slot
`topImage σ`, which shifts the compressed slots at or above it up by
one — exactly recovering the true targets.

No word in the adjacent transpositions is chosen, so no
word-independence is needed; functoriality instead follows from mere
generation.
-/

/-- **The permutation action on a tensor power**: `permMor X σ`
routes the factor in slot `i` to slot `σ i`. -/
noncomputable def permMor
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) :
    (n : ℕ) → Equiv.Perm (Fin n) → (tensorPow A X n ⟶ tensorPow A X n)
  | 0, _ => 𝟙 _
  | n + 1, σ =>
      (permMor X n (restPerm σ) ▷ X) ≫
        insertTop X n (n - (topImage σ : ℕ))

/-- The recursion equation. -/
theorem permMor_succ [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    permMor X (n + 1) σ =
      (permMor X n (restPerm σ) ▷ X) ≫
        insertTop X n (n - (topImage σ : ℕ)) := rfl

/-- The identity permutation acts as the identity. -/
@[simp]
theorem permMor_one [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) :
    permMor X n 1 = 𝟙 (tensorPow A X n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [permMor_succ, restPerm_one, ih, topImage_one]
    simp [Fin.last]

/-- **A top-fixing permutation acts on the lower factors alone.** -/
@[simp]
theorem permMor_extPerm
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) (τ : Equiv.Perm (Fin n)) :
    permMor X (n + 1) (extPerm τ) = permMor X n τ ▷ X := by
  rw [permMor_succ, restPerm_extPerm, topImage_extPerm,
    show (Fin.last n : Fin (n + 1)).val = n from rfl, Nat.sub_self,
    insertTop_zero]
  exact Category.comp_id _

/-- **Functoriality against a top-fixing permutation**, granted
functoriality one arity down. -/
theorem permMor_mul_extPerm
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ)
    (ih : ∀ ρ τ : Equiv.Perm (Fin n),
      permMor X n (ρ * τ) = permMor X n τ ≫ permMor X n ρ)
    (σ : Equiv.Perm (Fin (n + 1))) (τ : Equiv.Perm (Fin n)) :
    permMor X (n + 1) (σ * extPerm τ) =
      permMor X (n + 1) (extPerm τ) ≫ permMor X (n + 1) σ := by
  rw [permMor_succ, restPerm_mul_extPerm, topImage_mul_extPerm,
    ih (restPerm σ) τ, MonoidalCategory.comp_whiskerRight,
    permMor_extPerm, permMor_succ, Category.assoc]
  rfl

/-! ## The cycles

`topCycle q` is the permutation with trivial induced permutation, so
the recursion evaluates it to a single bubbling — which is what
`insertTop` was defined to be.  The top transposition is the cycle at
the second-highest slot, so it acts by the top braiding.
-/

/-- **A cycle acts by bubbling.** -/
@[simp]
theorem permMor_topCycle
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) (q : Fin (n + 1)) :
    permMor X (n + 1) (topCycle q) = insertTop X n (n - (q : ℕ)) := by
  rw [permMor_succ, restPerm_topCycle, topImage_topCycle, permMor_one,
    MonoidalCategory.id_whiskerRight, Category.id_comp]

/-- **The top transposition acts by the top braiding.**  It is the
cycle at the second-highest slot, one bubbling step. -/
theorem permMor_topSwap
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) :
    permMor X (n + 2) (topCycle (Fin.castSucc (Fin.last n))) =
      swapTop X n := by
  rw [permMor_topCycle,
    show ((Fin.castSucc (Fin.last n) : Fin (n + 2)) : ℕ) = n from rfl,
    show n + 1 - n = 1 from by omega, insertTop_one]

/-- **The top transposition acts by the top braiding**, in the form
the generating set uses. -/
@[simp]
theorem permMor_topSwap_eq
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) :
    permMor X (n + 2) (topSwap : Equiv.Perm (Fin (n + 2))) =
      swapTop X n := by
  rw [topSwap_eq_topCycle]
  exact permMor_topSwap X n

/-- Whiskering the recursion equation by one more factor. -/
theorem permMor_whiskerRight_succ
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ)
    (τ : Equiv.Perm (Fin (n + 1))) :
    (permMor X (n + 1) τ ▷ X) =
      ((permMor X n (restPerm τ) ▷ X) ▷ X) ≫
        (insertTop X n (n - (topImage τ : ℕ)) ▷ X) := by
  rw [permMor_succ]
  exact MonoidalCategory.comp_whiskerRight _ _ _

/-- Commuting morphisms may be exchanged in front of a third.  Stated
at general objects, so that no tensor-power arity enters the
rewriting. -/
private theorem comm_assoc [Category.{v} A]
    {P R : A} {a b : P ⟶ P} (h : a ≫ b = b ≫ a)
    (c : P ⟶ R) : a ≫ b ≫ c = b ≫ a ≫ c := by
  rw [← Category.assoc, h, Category.assoc]

/-- **The top braiding passes the lower-lower permutation.**  Only
the bubbling of the lower part can interact with the braiding of the
top two slots; the permutation beneath it commutes through. -/
theorem swapTop_comp_permMor_whiskerRight
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ)
    (τ : Equiv.Perm (Fin (n + 1))) :
    swapTop X n ≫ (permMor X (n + 1) τ ▷ X) =
      ((permMor X n (restPerm τ) ▷ X) ▷ X) ≫
        swapTop X n ≫ (insertTop X n (n - (topImage τ : ℕ)) ▷ X) := by
  rw [permMor_whiskerRight_succ]
  exact comm_assoc (swapTop_whiskerRight X n
    (permMor X n (restPerm τ))).symm _

/-! ## The top transposition

Both sides of the generator identity for the top transposition carry
the same permutation of the factors below the top two: the braiding
commutes past it, and precomposing with the top transposition leaves
the twice-restricted permutation alone.  What is left is a relation
between two bubblings and the braiding, with no permutation in it.
-/

/-- Congruence on the second factor of a composite.  Stated at
general objects, so that no tensor-power arity enters. -/
private theorem comp_congr_right [Category.{v} A]
    {P Q R : A} (a : P ⟶ Q) {b b' : Q ⟶ R}
    (h : b = b') : a ≫ b = a ≫ b' := by rw [h]

/-- Rearranging a commutation in front of a common tail.  Stated at a
general object, so that no tensor-power arity enters the rewriting. -/
private theorem shuffle [Category.{v} A]
    {P : A} {s v z v' w : P ⟶ P}
    (h : s ≫ v = z ≫ (s ≫ v')) :
    s ≫ v ≫ w = z ≫ (s ≫ v' ≫ w) := by
  rw [← Category.assoc, h, Category.assoc, Category.assoc]

/-- **The generator identity for the top transposition, reduced.**
Granted the braid relation between the two bubblings, the action is
functorial against the top transposition. -/
theorem permMor_mul_topSwap_of_braid
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2)))
    (hbraid :
      swapTop X n ≫
          ((insertTop X n (n - (topImage (restPerm σ) : ℕ)) ▷ X) ≫
            insertTop X (n + 1) (n + 1 - (topImage σ : ℕ))) =
        (insertTop X n
            (n - (topImage (restPerm (σ * topSwap)) : ℕ)) ▷ X) ≫
          insertTop X (n + 1)
            (n + 1 - (topImage (σ * topSwap) : ℕ))) :
    permMor X (n + 2) (σ * topSwap) =
      swapTop X n ≫ permMor X (n + 2) σ := by
  have h1 : permMor X (n + 2) (σ * topSwap) =
      ((permMor X n (restPerm (restPerm σ)) ▷ X) ▷ X) ≫
        ((insertTop X n
            (n - (topImage (restPerm (σ * topSwap)) : ℕ)) ▷ X) ≫
          insertTop X (n + 1)
            (n + 1 - (topImage (σ * topSwap) : ℕ))) := by
    rw [permMor_succ, permMor_whiskerRight_succ,
      restPerm_restPerm_mul_topSwap]
    exact Category.assoc _ _ _
  have h3 : ((permMor X n (restPerm (restPerm σ)) ▷ X) ▷ X) ≫
        (swapTop X n ≫
          ((insertTop X n (n - (topImage (restPerm σ) : ℕ)) ▷ X) ≫
            insertTop X (n + 1) (n + 1 - (topImage σ : ℕ)))) =
      swapTop X n ≫ permMor X (n + 2) σ := by
    rw [permMor_succ (σ := σ)]
    exact (shuffle (swapTop_comp_permMor_whiskerRight X n
      (restPerm σ))).symm
  exact h1.trans ((comp_congr_right _ hbraid.symm).trans h3)

/-- **Functoriality against the top transposition.**  The two cases
are whether the top slot's image lies above or below the image of the
slot beneath it; each feeds the corresponding braid identity. -/
theorem permMor_mul_topSwap
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ)
    (σ : Equiv.Perm (Fin (n + 2))) :
    permMor X (n + 2) (σ * topSwap) =
      swapTop X n ≫ permMor X (n + 2) σ := by
  refine permMor_mul_topSwap_of_braid X n σ ?_
  have hm : ((topImage (restPerm σ) : Fin (n + 1)) : ℕ) ≤ n :=
    Nat.lt_succ_iff.mp (topImage (restPerm σ)).isLt
  have hp : ((topImage σ : Fin (n + 2)) : ℕ) ≤ n + 1 :=
    Nat.lt_succ_iff.mp (topImage σ).isLt
  rcases Fin.lt_or_le ((topImage (restPerm σ)).castSucc) (topImage σ) with h | h
  · have hlt : ((topImage (restPerm σ) : Fin (n + 1)) : ℕ)
        < ((topImage σ : Fin (n + 2)) : ℕ) := by
      simpa [Fin.lt_def] using h
    rw [topImage_mul_topSwap_val_of_lt σ h,
      topImage_restPerm_mul_topSwap_val_of_lt σ h,
      show n - (((topImage σ : Fin (n + 2)) : ℕ) - 1)
        = n + 1 - ((topImage σ : Fin (n + 2)) : ℕ) from by omega,
      show n + 1 - ((topImage (restPerm σ) : Fin (n + 1)) : ℕ)
        = (n - ((topImage (restPerm σ) : Fin (n + 1)) : ℕ)) + 1 from by
          omega]
    exact insertTop_braid_le X n _ _ (by omega) (by omega)
  · have hle : ((topImage σ : Fin (n + 2)) : ℕ)
        ≤ ((topImage (restPerm σ) : Fin (n + 1)) : ℕ) := by
      simpa [Fin.le_def] using h
    rw [topImage_mul_topSwap_val_of_le σ h,
      topImage_restPerm_mul_topSwap_val_of_le σ h,
      show n + 1 - (((topImage (restPerm σ) : Fin (n + 1)) : ℕ) + 1)
        = n - ((topImage (restPerm σ) : Fin (n + 1)) : ℕ) from by omega,
      show n + 1 - ((topImage σ : Fin (n + 2)) : ℕ)
        = (n - ((topImage σ : Fin (n + 2)) : ℕ)) + 1 from by omega]
    exact insertTop_braid_lt X n _ _ (by omega) (by omega)

/-! ## Functoriality

Every permutation is a product of adjacent transpositions, and each of
those is either top-fixing or the top transposition — both already
handled.  Since the action was defined canonically rather than through
a chosen word, generation is all that is needed: no presentation of
the symmetric group, and no coherence theorem.
-/

/-- **The action is functorial.**  Composition of permutations goes to
composition of morphisms, in the order `End` multiplies. -/
theorem permMor_mul [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) : ∀ (n : ℕ) (σ τ : Equiv.Perm (Fin n)),
    permMor X n (σ * τ) = permMor X n τ ≫ permMor X n σ := by
  intro n
  induction n with
  | zero =>
    intro σ τ
    show 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    exact (Category.comp_id _).symm
  | succ n' ih =>
    match n' with
    | 0 =>
      intro σ τ
      have h1 : ∀ ρ : Equiv.Perm (Fin (0 + 1)), ρ = 1 := fun ρ =>
        Equiv.ext fun x => Fin.ext (by omega)
      rw [h1 σ, h1 τ, one_mul, permMor_one]
      exact (Category.id_comp _).symm
    | n'' + 1 =>
      have hgen : ∀ (i : Fin (n'' + 1)) (ρ : Equiv.Perm (Fin (n'' + 2))),
          permMor X (n'' + 2) (ρ * Equiv.swap i.castSucc i.succ)
            = permMor X (n'' + 2) (Equiv.swap i.castSucc i.succ)
              ≫ permMor X (n'' + 2) ρ := by
        intro i
        refine Fin.lastCases ?_ (fun j ρ => ?_) i
        · intro ρ
          rw [show Equiv.swap (Fin.castSucc (Fin.last n''))
              (Fin.last n'').succ = (topSwap : Equiv.Perm (Fin (n'' + 2)))
            from by rw [topSwap, Fin.succ_last]]
          rw [permMor_topSwap_eq]
          exact permMor_mul_topSwap X n'' ρ
        · rw [swap_castSucc_succ_castSucc j]
          exact permMor_mul_extPerm X (n'' + 1) ih ρ _
      have key : ∀ τ : Equiv.Perm (Fin (n'' + 2)),
          τ ∈ Submonoid.closure (Set.range fun i : Fin (n'' + 1) =>
            Equiv.swap i.castSucc i.succ) →
          ∀ σ : Equiv.Perm (Fin (n'' + 2)),
            permMor X (n'' + 2) (σ * τ)
              = permMor X (n'' + 2) τ ≫ permMor X (n'' + 2) σ := by
        intro τ hτ
        induction hτ using Submonoid.closure_induction_left with
        | one =>
          intro σ
          rw [mul_one, permMor_one]
          exact (Category.id_comp _).symm
        | mul_left g hg τ' hτ' ihτ' =>
          obtain ⟨i, rfl⟩ := hg
          intro σ
          rw [← mul_assoc, ihτ' (σ * _), hgen i σ, ihτ' _, Category.assoc]
      intro σ τ
      exact key τ (by
        rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial) σ

/-! ## The algebra map

With functoriality in hand the action is a monoid homomorphism into
the endomorphism monoid, and the universal property of the group
algebra turns it into the algebra map a tower's representation field
asks for.  Only this last step needs the linear structure.
-/

/-- **The action as a monoid homomorphism.** -/
@[simps]
noncomputable def permHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X : A) (n : ℕ) :
    Equiv.Perm (Fin n) →* End (tensorPow A X n) where
  toFun := permMor X n
  map_one' := permMor_one X n
  map_mul' := permMor_mul X n

section Linear

/-- **The symmetric-group algebra acting on a tensor power.** -/
noncomputable def permAlg
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (X : A) (n : ℕ) :
    SymGroupAlgebra n →ₐ[ℂ] End (tensorPow A X n) :=
  MonoidAlgebra.lift ℂ (End (tensorPow A X n)) (Equiv.Perm (Fin n))
    (permHom X n)

/-- The algebra map sends a group element to its action. -/
@[simp]
theorem permAlg_single
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (X : A) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    permAlg X n (MonoidAlgebra.single σ (1 : ℂ)) = permMor X n σ := by
  rw [permAlg, MonoidAlgebra.lift_single, one_smul]
  rfl

end Linear

end RS
