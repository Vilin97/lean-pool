/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.Intertwine
import LeanPool.RegtsSevenster.RS.Novel.Envelope.SymPerm

/-!
# Distribution of the permutation action over a tensor product

The distribution isomorphism `(X ⊗ Y) ^ ⊗ n ≅ X ^ ⊗ n ⊗ Y ^ ⊗ n`
re-sorts the factors of a tensor power of a tensor product: stage by
stage, the middle-four interchange (`tensorμ`) moves the newest pair
of factors past the ones already sorted.  The diagonal permutation
action on the left matches the simultaneous action of the same
permutation on the two sides.

The intertwining is proved for the top braiding first: braiding two
compound factors distributes into the two plain braidings, which is
the symmetric-category compatibility `tensorμ_braid_swap` conjugated
through Mathlib's `tensor_associativity`.  It then propagates along
the recursions of `insertTop` and `permMor` exactly as the naturality
lemmas of `Deligne/PermNat.lean` do, and linearises to the group
algebra, whose diagonal double action is packaged as `diagAlg`.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe v u

variable {A : Type u}

/-! ## The distribution isomorphism -/

/-- **The middle-four interchange as an isomorphism**: `tensorμ` and
`tensorδ` are mutually inverse. -/
noncomputable def tensorμIso
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (P Q X Y : A) :
    (P ⊗ Q) ⊗ (X ⊗ Y) ≅ (P ⊗ X) ⊗ (Q ⊗ Y) where
  hom := tensorμ P Q X Y
  inv := tensorδ P Q X Y
  hom_inv_id := tensorμ_tensorδ P Q X Y
  inv_hom_id := tensorδ_tensorμ P Q X Y

/-- **The distribution isomorphism**
`(X ⊗ Y) ^ ⊗ n ≅ X ^ ⊗ n ⊗ Y ^ ⊗ n`: at each stage the previous
stage sorts all but the newest pair of factors, and the middle-four
interchange routes that pair to its two destinations. -/
noncomputable def tensorPowDistrib
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X Y : A) : (n : ℕ) →
    (tensorPow A (X ⊗ Y) n ≅ tensorPow A X n ⊗ tensorPow A Y n)
  | 0 => (λ_ (𝟙_ A)).symm
  | n + 1 =>
      whiskerRightIso (tensorPowDistrib X Y n) (X ⊗ Y) ≪≫
        tensorμIso (tensorPow A X n) (tensorPow A Y n) X Y

/-- The distribution at arity zero is the inverse unitor. -/
@[simp]
theorem tensorPowDistrib_zero
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X Y : A) :
    tensorPowDistrib X Y 0 = (λ_ (𝟙_ A)).symm := rfl

/-! ## The top braiding distributes

Braiding the top two compound factors of `((P ⊗ Q) ⊗ (X ⊗ Y)) ⊗
(X ⊗ Y)` corresponds, through the two-stage interchange, to braiding
the two top factors on each side at once.  The computation is done at
general objects, so that no tensor-power arity enters the rewriting:
the two-stage interchange is re-associated into a single interchange
against the paired factors (`tensor_associativity`), where the
braiding of a tensor square distributes by the symmetric-category
compatibility `tensorμ_braid_swap`.
-/

/-- In a symmetric category the interchange with the two middle
factors swapped is the inverse interchange: the single braiding they
contain differs by `braiding_swap_eq_inv_braiding`. -/
private theorem tensorμ_swap_eq_tensorδ
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X₁ X₂ Y₁ Y₂ : A) :
    tensorμ X₁ Y₁ X₂ Y₂ = tensorδ X₁ X₂ Y₁ Y₂ := by
  simp only [tensorμ, tensorδ,
    SymmetricCategory.braiding_swap_eq_inv_braiding]

/-- **The braiding of a tensor square distributes**: braiding the two
compound factors corresponds, through the interchange, to braiding
the two plain pairs.  This reads `tensorμ_braid_swap` through the
inverse interchange. -/
private theorem braiding_tensorμ
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X Y : A) :
    (β_ (X ⊗ Y) (X ⊗ Y)).hom ≫ tensorμ X Y X Y =
      tensorμ X Y X Y ≫ ((β_ X X).hom ⊗ₘ (β_ Y Y).hom) := by
  have h := SymmetricCategory.tensorμ_braid_swap (C := A) X Y
  rw [tensorμ_swap_eq_tensorδ X X Y Y]
  calc (β_ (X ⊗ Y) (X ⊗ Y)).hom ≫ tensorδ X X Y Y
      = tensorδ X X Y Y ≫ tensorμ X X Y Y ≫
          (β_ (X ⊗ Y) (X ⊗ Y)).hom ≫ tensorδ X X Y Y := by
        rw [tensorδ_tensorμ_assoc]
    _ = tensorδ X X Y Y ≫ ((β_ X X).hom ⊗ₘ (β_ Y Y).hom) ≫
          tensorμ X X Y Y ≫ tensorδ X X Y Y := by
        rw [← reassoc_of% h]
    _ = tensorδ X X Y Y ≫ ((β_ X X).hom ⊗ₘ (β_ Y Y).hom) := by
        rw [tensorμ_tensorδ, Category.comp_id]

/-- The two-stage interchange, re-associated: distributing twice is a
single interchange against the paired factors, conjugated by
associators.  This is `tensor_associativity` with the final
associators moved across. -/
private theorem interchange_assoc
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (P Q X Y : A) :
    (tensorμ P Q X Y ▷ (X ⊗ Y)) ≫ tensorμ (P ⊗ X) (Q ⊗ Y) X Y =
      (α_ (P ⊗ Q) (X ⊗ Y) (X ⊗ Y)).hom ≫
        ((P ⊗ Q) ◁ tensorμ X Y X Y) ≫
        tensorμ P Q (X ⊗ X) (Y ⊗ Y) ≫
        ((α_ P X X).inv ⊗ₘ (α_ Q Y Y).inv) := by
  rw [← tensor_associativity_assoc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id, Iso.hom_inv_id, id_tensorHom_id, Category.comp_id]

/-- **The top braiding distributes through the interchange**, at
general objects standing for the two sorted lower parts. -/
private theorem swap_distrib_core
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (P Q X Y : A) :
    ((α_ (P ⊗ Q) (X ⊗ Y) (X ⊗ Y)).hom ≫
        ((P ⊗ Q) ◁ (β_ (X ⊗ Y) (X ⊗ Y)).hom) ≫
        (α_ (P ⊗ Q) (X ⊗ Y) (X ⊗ Y)).inv) ≫
      (tensorμ P Q X Y ▷ (X ⊗ Y)) ≫ tensorμ (P ⊗ X) (Q ⊗ Y) X Y =
    ((tensorμ P Q X Y ▷ (X ⊗ Y)) ≫ tensorμ (P ⊗ X) (Q ⊗ Y) X Y) ≫
      (((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) ⊗ₘ
        ((α_ Q Y Y).hom ≫ (Q ◁ (β_ Y Y).hom) ≫ (α_ Q Y Y).inv)) := by
  rw [interchange_assoc P Q X Y]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc, braiding_tensorμ,
    MonoidalCategory.whiskerLeft_comp_assoc,
    tensorμ_natural_right_assoc, tensorHom_comp_tensorHom,
    tensorHom_comp_tensorHom, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_assoc]

/-- The braiding conjugate that defines `swapTop` is natural in the
base object.  Stated at general objects. -/
private theorem swap_conj_base
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    {B B' : A} (Z : A) (g : B ⟶ B') :
    ((g ▷ Z) ▷ Z) ≫
        ((α_ B' Z Z).hom ≫ (B' ◁ (β_ Z Z).hom) ≫ (α_ B' Z Z).inv) =
      ((α_ B Z Z).hom ≫ (B ◁ (β_ Z Z).hom) ≫ (α_ B Z Z).inv) ≫
        ((g ▷ Z) ▷ Z) := by
  rw [MonoidalCategory.associator_naturality_left_assoc,
    ← MonoidalCategory.whisker_exchange_assoc,
    MonoidalCategory.associator_inv_naturality_left]
  simp only [Category.assoc]

/-- A conjugation step at general objects: what commutes with `s`
across `W` and intertwines across `T` intertwines across the
composite. -/
private theorem conj_step [Category.{v} A]
    {P₁ P₂ P₃ : A} {W : P₁ ⟶ P₂} {s : P₁ ⟶ P₁}
    {s' : P₂ ⟶ P₂} {T : P₂ ⟶ P₃} {u : P₃ ⟶ P₃}
    (h1 : W ≫ s' = s ≫ W) (h2 : s' ≫ T = T ≫ u) :
    s ≫ W ≫ T = (W ≫ T) ≫ u := by
  calc s ≫ W ≫ T
      = (W ≫ s') ≫ T := by rw [h1, Category.assoc]
    _ = (W ≫ T) ≫ u := by rw [Category.assoc, Category.assoc, h2]

/-- **The distribution intertwines the top braiding**: braiding the
top two factors of `(X ⊗ Y) ^ ⊗ (n + 2)` corresponds to braiding the
top two factors on each side simultaneously. -/
theorem tensorPowDistrib_swapTop
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X Y : A) (n : ℕ) :
    swapTop (X ⊗ Y) n ≫ (tensorPowDistrib X Y (n + 2)).hom =
      (tensorPowDistrib X Y (n + 2)).hom ≫
        (swapTop X n ⊗ₘ swapTop Y n) := by
  have hD : (tensorPowDistrib X Y (n + 2)).hom =
      (((tensorPowDistrib X Y n).hom ▷ (X ⊗ Y)) ▷ (X ⊗ Y)) ≫
        ((tensorμ (tensorPow A X n) (tensorPow A Y n) X Y ▷
            (X ⊗ Y)) ≫
          tensorμ (tensorPow A X n ⊗ X) (tensorPow A Y n ⊗ Y)
            X Y) := by
    have h := MonoidalCategory.comp_whiskerRight
      ((tensorPowDistrib X Y n).hom ▷ (X ⊗ Y))
      (tensorμ (tensorPow A X n) (tensorPow A Y n) X Y) (X ⊗ Y)
    change ((((tensorPowDistrib X Y n).hom ▷ (X ⊗ Y)) ≫
      tensorμ (tensorPow A X n) (tensorPow A Y n) X Y) ▷ (X ⊗ Y)) ≫
      tensorμ (tensorPow A X n ⊗ X) (tensorPow A Y n ⊗ Y) X Y = _
    erw [h, Category.assoc]
  rw [hD]
  exact conj_step
    (swap_conj_base (X ⊗ Y) (tensorPowDistrib X Y n).hom)
    (swap_distrib_core (tensorPow A X n) (tensorPow A Y n) X Y)

/-! ## The insertion cycle and the full action

The intertwining propagates along the recursions of `insertTop` and
`permMor` exactly as the naturality lemmas of `PermNat.lean`: each
whiskered step passes through the distribution by naturality of the
interchange, and each top braiding by the coherence above.
-/

/-- A morphism intertwining the distribution one arity down still
intertwines after whiskering by the newest pair, by naturality of the
interchange.  Stated at general objects. -/
private theorem whisker_pass_distrib
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    {P Q R : A} (X Y : A)
    {u : P ⟶ P} {v : Q ⟶ Q} {w : R ⟶ R} {T : P ⟶ Q ⊗ R}
    (h : u ≫ T = T ≫ (v ⊗ₘ w)) :
    (u ▷ (X ⊗ Y)) ≫ ((T ▷ (X ⊗ Y)) ≫ tensorμ Q R X Y) =
      ((T ▷ (X ⊗ Y)) ≫ tensorμ Q R X Y) ≫
        ((v ▷ X) ⊗ₘ (w ▷ Y)) := by
  calc (u ▷ (X ⊗ Y)) ≫ ((T ▷ (X ⊗ Y)) ≫ tensorμ Q R X Y)
      = ((u ≫ T) ▷ (X ⊗ Y)) ≫ tensorμ Q R X Y := by
        rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight]
    _ = ((T ≫ (v ⊗ₘ w)) ▷ (X ⊗ Y)) ≫ tensorμ Q R X Y := by
        rw [h]
    _ = (T ▷ (X ⊗ Y)) ≫ ((v ⊗ₘ w) ▷ (X ⊗ Y)) ≫ tensorμ Q R X Y := by
        rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
    _ = (T ▷ (X ⊗ Y)) ≫ tensorμ Q R X Y ≫
          ((v ▷ X) ⊗ₘ (w ▷ Y)) := by
        rw [tensorμ_natural_left]
    _ = ((T ▷ (X ⊗ Y)) ≫ tensorμ Q R X Y) ≫
          ((v ▷ X) ⊗ₘ (w ▷ Y)) := by
        rw [Category.assoc]

/-- Two morphisms that each intertwine `T` compose to a morphism
intertwining `T`.  Stated at general objects, so that no tensor-power
arity enters the rewriting. -/
private theorem step_shuffle [Category.{v} A]
    {P Q : A} {s u : P ⟶ P} {T : P ⟶ Q}
    {s' u' : Q ⟶ Q} (hs : s ≫ T = T ≫ s') (hu : u ≫ T = T ≫ u') :
    (s ≫ u) ≫ T = T ≫ (s' ≫ u') := by
  rw [Category.assoc, hu, ← Category.assoc, hs, Category.assoc]

/-- The identity intertwines any morphism into a tensor product with
the tensor product of identities.  Stated at general objects. -/
private theorem id_pass [Category.{v} A] [MonoidalCategory A]
    {P Q R : A} (T : P ⟶ Q ⊗ R) :
    𝟙 P ≫ T = T ≫ (𝟙 Q ⊗ₘ 𝟙 R) := by
  rw [MonoidalCategory.id_tensorHom_id, Category.id_comp,
    Category.comp_id]

/-- **The distribution intertwines the insertion cycle**: bubbling
the top compound factor down corresponds to bubbling the top factor
on each side simultaneously.  The proof follows the recursion of
`insertTop`. -/
theorem tensorPowDistrib_insertTop
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X Y : A) :
    ∀ n k : ℕ,
      insertTop (X ⊗ Y) n k ≫ (tensorPowDistrib X Y (n + 1)).hom =
        (tensorPowDistrib X Y (n + 1)).hom ≫
          (insertTop X n k ⊗ₘ insertTop Y n k) := by
  intro n
  induction n with
  | zero =>
    intro k
    simp only [insertTop_of_zero, MonoidalCategory.id_tensorHom_id,
      Category.id_comp, Category.comp_id]
  | succ n ih =>
    intro k
    cases k with
    | zero =>
      simp only [insertTop_zero, MonoidalCategory.id_tensorHom_id,
        Category.id_comp, Category.comp_id]
    | succ k =>
      have hs := tensorPowDistrib_swapTop X Y n
      have hw : (insertTop (X ⊗ Y) n k ▷ (X ⊗ Y)) ≫
            (tensorPowDistrib X Y (n + 2)).hom =
          (tensorPowDistrib X Y (n + 2)).hom ≫
            ((insertTop X n k ▷ X) ⊗ₘ (insertTop Y n k ▷ Y)) :=
        whisker_pass_distrib X Y (ih k)
      have hcomp := MonoidalCategory.tensorHom_comp_tensorHom
        (swapTop X n) (swapTop Y n)
        (insertTop X n k ▷ X) (insertTop Y n k ▷ Y)
      rw [insertTop_succ, insertTop_succ, insertTop_succ]
      exact (step_shuffle hs hw).trans
        (congrArg (fun m => (tensorPowDistrib X Y (n + 2)).hom ≫ m)
          hcomp)

/-- **The distribution intertwines the permutation action**: the
diagonal action of `σ` on `(X ⊗ Y) ^ ⊗ n` corresponds to the
simultaneous action of `σ` on the two sides.  The proof is the
recursion of `permMor` itself. -/
theorem tensorPowDistrib_permMor
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X Y : A) :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      permMor (X ⊗ Y) n σ ≫ (tensorPowDistrib X Y n).hom =
        (tensorPowDistrib X Y n).hom ≫
          (permMor X n σ ⊗ₘ permMor Y n σ) := by
  intro n
  induction n with
  | zero =>
    intro σ
    exact id_pass (tensorPowDistrib X Y 0).hom
  | succ n ih =>
    intro σ
    have hw : (permMor (X ⊗ Y) n (restPerm σ) ▷ (X ⊗ Y)) ≫
          (tensorPowDistrib X Y (n + 1)).hom =
        (tensorPowDistrib X Y (n + 1)).hom ≫
          ((permMor X n (restPerm σ) ▷ X) ⊗ₘ
            (permMor Y n (restPerm σ) ▷ Y)) :=
      whisker_pass_distrib X Y (ih (restPerm σ))
    have hi := tensorPowDistrib_insertTop X Y n
      (n - (topImage σ : ℕ))
    have hcomp := MonoidalCategory.tensorHom_comp_tensorHom
      (permMor X n (restPerm σ) ▷ X) (permMor Y n (restPerm σ) ▷ Y)
      (insertTop X n (n - (topImage σ : ℕ)))
      (insertTop Y n (n - (topImage σ : ℕ)))
    rw [permMor_succ, permMor_succ, permMor_succ]
    exact (step_shuffle hw hi).trans
      (congrArg (fun m => (tensorPowDistrib X Y (n + 1)).hom ≫ m)
        hcomp)

/-! ## The diagonal double action -/

/-- **The diagonal double action of a permutation** on
`X ^ ⊗ n ⊗ Y ^ ⊗ n`, as a monoid homomorphism: `σ` acts by its two
actions tensored together. -/
@[simps]
noncomputable def diagPermHom
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    (X Y : A) (n : ℕ) :
    Equiv.Perm (Fin n) →* End (tensorPow A X n ⊗ tensorPow A Y n)
    where
  toFun σ := permMor X n σ ⊗ₘ permMor Y n σ
  map_one' := by
    show permMor X n 1 ⊗ₘ permMor Y n 1 =
      𝟙 (tensorPow A X n ⊗ tensorPow A Y n)
    rw [permMor_one, permMor_one, MonoidalCategory.id_tensorHom_id]
  map_mul' σ τ := by
    show permMor X n (σ * τ) ⊗ₘ permMor Y n (σ * τ) =
      (permMor X n τ ⊗ₘ permMor Y n τ) ≫
        (permMor X n σ ⊗ₘ permMor Y n σ)
    rw [permMor_mul, permMor_mul,
      MonoidalCategory.tensorHom_comp_tensorHom]

section Linear

/-- **The diagonal double action of the symmetric-group algebra** on
`X ^ ⊗ n ⊗ Y ^ ⊗ n`: the linear extension of
`σ ↦ permMor X n σ ⊗ₘ permMor Y n σ`. -/
noncomputable def diagAlg
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (X Y : A) (n : ℕ) :
    SymGroupAlgebra n →ₐ[ℂ] End (tensorPow A X n ⊗ tensorPow A Y n) :=
  MonoidAlgebra.lift ℂ (End (tensorPow A X n ⊗ tensorPow A Y n))
    (Equiv.Perm (Fin n)) (diagPermHom X Y n)

/-- The diagonal algebra map sends a group element to the tensor
product of its two actions. -/
@[simp]
theorem diagAlg_single
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (X Y : A) (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    diagAlg X Y n (MonoidAlgebra.single σ (1 : ℂ)) =
      permMor X n σ ⊗ₘ permMor Y n σ := by
  rw [diagAlg, MonoidAlgebra.lift_single, one_smul]
  rfl

/-- The diagonal algebra map written out as a sum over the support:
`x` acts by `Σ_σ x_σ • (permMor X n σ ⊗ₘ permMor Y n σ)`. -/
theorem diagAlg_apply
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (X Y : A) (n : ℕ) (x : SymGroupAlgebra n) :
    diagAlg X Y n x =
      Finsupp.sum x.coeff fun σ c =>
        c • (permMor X n σ ⊗ₘ permMor Y n σ) := by
  rw [diagAlg, MonoidAlgebra.lift_apply]
  rfl

/-- **The distribution intertwines the group-algebra action**: the
diagonal action of any group-algebra element on `(X ⊗ Y) ^ ⊗ n`
corresponds, through the distribution isomorphism, to its diagonal
double action on
`X ^ ⊗ n ⊗ Y ^ ⊗ n`.  Both sides are `ℂ`-linear in the element, so
the statement reduces to basis permutations, where it is
`tensorPowDistrib_permMor`. -/
theorem tensorPowDistrib_permAlg
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (X Y : A) {n : ℕ}
    (x : SymGroupAlgebra n) :
    permAlg (X ⊗ Y) n x ≫ (tensorPowDistrib X Y n).hom =
      (tensorPowDistrib X Y n).hom ≫ diagAlg X Y n x := by
  induction x using MonoidAlgebra.induction_on with
  | of σ =>
    rw [show (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))) σ =
        MonoidAlgebra.single σ (1 : ℂ) from rfl,
      permAlg_single, diagAlg_single]
    exact tensorPowDistrib_permMor X Y n σ
  | add x y hx hy =>
    rw [map_add, map_add]
    exact intertwine_add hx hy
  | smul r x hx =>
    rw [map_smul, map_smul]
    exact intertwine_smul r hx

end Linear

end RS
