/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.CatTheory.Intertwine
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SchurVanishing
import LeanPool.RegtsSevenster.RS.Classical.Deligne.TensorExact

/-!
# Naturality of the symmetric-group action

A morphism `f : X ⟶ Y` induces `f ^ ⊗ n` between the tensor powers,
and the permutation action of `Envelope/SymPerm.lean` is natural in
it: every braiding used there is a component of a natural
transformation, so the action of any group-algebra element commutes
with `f ^ ⊗ n`.  The naturality lemmas follow the recursion that
defines the action — one lemma per auxiliary definition.

Two consequences are recorded.  Tensor powers of monomorphisms are
monomorphisms (and dually for epimorphisms), because tensoring is
exact in a rigid category (`TensorExact.lean`); and Schur vanishing
passes to subobjects, quotients and isomorphs (the idempotent-level
form of Deligne's 1.19, Catégories tensorielles): a mono `Y ⟶ X`
intertwines the two actions, so if the block idempotent kills
`X ^ ⊗ n` it kills `Y ^ ⊗ n` as well.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {A : Type u}

/-! ## Tensor powers of a morphism -/

/-- **The tensor power of a morphism**: `f ^ ⊗ n` acts as `f` on
every factor, by the same recursion that defines `tensorPow`. -/
noncomputable def tensorPowMap [Category.{v} A] [MonoidalCategory A]
    {X Y : A} (f : X ⟶ Y) :
    (n : ℕ) → (tensorPow A X n ⟶ tensorPow A Y n)
  | 0 => 𝟙 (𝟙_ A)
  | n + 1 => tensorPowMap f n ⊗ₘ f

/-- The empty power of a morphism is the identity of the unit. -/
@[simp]
theorem tensorPowMap_zero [Category.{v} A] [MonoidalCategory A]
    {X Y : A} (f : X ⟶ Y) :
    tensorPowMap f 0 = 𝟙 (𝟙_ A) := rfl

/-- The defining recursion of `tensorPowMap`. -/
theorem tensorPowMap_succ [Category.{v} A] [MonoidalCategory A]
    {X Y : A} (f : X ⟶ Y) (n : ℕ) :
    tensorPowMap f (n + 1) = tensorPowMap f n ⊗ₘ f := rfl

/-- Tensor powers of the identity are the identity. -/
@[simp]
theorem tensorPowMap_id [Category.{v} A] [MonoidalCategory A]
    (X : A) (n : ℕ) :
    tensorPowMap (𝟙 X) n = 𝟙 (tensorPow A X n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tensorPowMap_succ, ih, MonoidalCategory.id_tensorHom_id]
    rfl

/-- Tensor powers are functorial in the morphism. -/
theorem tensorPowMap_comp [Category.{v} A] [MonoidalCategory A]
    {X Y Z : A} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) :
    tensorPowMap (f ≫ g) n = tensorPowMap f n ≫ tensorPowMap g n := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n ih =>
    rw [tensorPowMap_succ, tensorPowMap_succ, tensorPowMap_succ, ih,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
    rfl

/-! ## Mono and epi transport

In a rigid category tensoring is exact (`TensorExact.lean`), so both
whiskerings preserve monomorphisms and epimorphisms, and hence so
does the tensor power of a morphism.
-/

/-- **Tensor powers preserve monomorphisms** in a rigid category:
each factor of `f ⊗ₘ f`'s whiskering factorisation preserves
monomorphisms, because tensoring preserves limits. -/
theorem tensorPowMap_mono [Category.{v} A] [MonoidalCategory A]
    [RigidCategory A] {X Y : A} (f : X ⟶ Y)
    [Mono f] (n : ℕ) : Mono (tensorPowMap f n) := by
  induction n with
  | zero =>
    exact inferInstanceAs (Mono (𝟙 (𝟙_ A)))
  | succ n ih =>
    haveI : PreservesLimitsOfSize.{0, 0} (tensorRight X) :=
      preservesSmallestLimits_of_preservesLimits _
    haveI : PreservesLimitsOfSize.{0, 0}
        (tensorLeft (tensorPow A Y n)) :=
      preservesSmallestLimits_of_preservesLimits _
    haveI := ih
    haveI : Mono (tensorPowMap f n ▷ X) :=
      (tensorRight X).map_mono (tensorPowMap f n)
    haveI : Mono (tensorPow A Y n ◁ f) :=
      (tensorLeft (tensorPow A Y n)).map_mono f
    rw [tensorPowMap_succ, MonoidalCategory.tensorHom_def]
    show Mono ((tensorPowMap f n ▷ X) ≫ (tensorPow A Y n ◁ f))
    exact mono_comp _ _

/-- **Tensor powers preserve monomorphisms**, from mono
preservation of the tensor factors alone — the form consumed over
an ind-completion, where tensoring is exact without rigidity. -/
theorem tensorPowMap_mono' [Category.{v} A] [MonoidalCategory A]
    [∀ Z : A, (tensorLeft Z).PreservesMonomorphisms]
    [∀ Z : A, (tensorRight Z).PreservesMonomorphisms]
    {X Y : A} (f : X ⟶ Y) [Mono f] (n : ℕ) :
    Mono (tensorPowMap f n) := by
  induction n with
  | zero =>
    exact inferInstanceAs (Mono (𝟙 (𝟙_ A)))
  | succ n ih =>
    haveI := ih
    haveI : Mono (tensorPowMap f n ▷ X) :=
      (tensorRight X).map_mono (tensorPowMap f n)
    haveI : Mono (tensorPow A Y n ◁ f) :=
      (tensorLeft (tensorPow A Y n)).map_mono f
    rw [tensorPowMap_succ, MonoidalCategory.tensorHom_def]
    show Mono ((tensorPowMap f n ▷ X) ≫
      (tensorPow A Y n ◁ f))
    exact mono_comp _ _

/-- **Tensor powers preserve epimorphisms** in a rigid category:
each factor of `f ⊗ₘ f`'s whiskering factorisation preserves
epimorphisms, because tensoring preserves colimits. -/
theorem tensorPowMap_epi [Category.{v} A] [MonoidalCategory A]
    [RigidCategory A] {X Y : A} (f : X ⟶ Y)
    [Epi f] (n : ℕ) : Epi (tensorPowMap f n) := by
  induction n with
  | zero =>
    exact inferInstanceAs (Epi (𝟙 (𝟙_ A)))
  | succ n ih =>
    haveI : PreservesColimitsOfSize.{0, 0} (tensorRight X) :=
      preservesSmallestColimits_of_preservesColimits _
    haveI : PreservesColimitsOfSize.{0, 0}
        (tensorLeft (tensorPow A Y n)) :=
      preservesSmallestColimits_of_preservesColimits _
    haveI := ih
    haveI : Epi (tensorPowMap f n ▷ X) :=
      (tensorRight X).map_epi (tensorPowMap f n)
    haveI : Epi (tensorPow A Y n ◁ f) :=
      (tensorLeft (tensorPow A Y n)).map_epi f
    rw [tensorPowMap_succ, MonoidalCategory.tensorHom_def]
    show Epi ((tensorPowMap f n ▷ X) ≫ (tensorPow A Y n ◁ f))
    exact epi_comp _ _

/-! ## Naturality of the action

Each auxiliary morphism of `Envelope/SymPerm.lean` is built from
braidings and associators, which are components of natural
transformations, so each commutes with a tensor power of `f`.  The
lemmas follow the definitions' recursions exactly.
-/

/-- A morphism intertwining `v` and `w` still intertwines after
whiskering, against `v ⊗ₘ f`.  Stated at general objects, so that no
tensor-power arity enters the rewriting. -/
private theorem whisker_pass [Category.{v} A] [MonoidalCategory A]
    {P Q X Y : A} {u : P ⟶ P} {v : P ⟶ Q}
    {w : Q ⟶ Q} (f : X ⟶ Y) (h : u ≫ v = v ≫ w) :
    (u ▷ X) ≫ (v ⊗ₘ f) = (v ⊗ₘ f) ≫ (w ▷ Y) := by
  rw [← MonoidalCategory.tensorHom_id u X,
    ← MonoidalCategory.tensorHom_id w Y,
    MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, h,
    Category.id_comp, Category.comp_id]

/-- A commutation in the second tensorand passes a tensored morphism
through a left whiskering.  Stated at general objects. -/
private theorem tensor_middle [Category.{v} A] [MonoidalCategory A]
    {P Q S T U V : A} (g : P ⟶ Q)
    (h : S ⟶ T) (k : T ⟶ U) (h' : S ⟶ V) (k' : V ⟶ U)
    (w : h ≫ k = h' ≫ k') :
    (g ⊗ₘ h) ≫ (Q ◁ k) = (P ◁ h') ≫ (g ⊗ₘ k') := by
  rw [← MonoidalCategory.id_tensorHom Q k,
    ← MonoidalCategory.id_tensorHom P h',
    MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, w,
    Category.comp_id, Category.id_comp]

/-- Two morphisms that each intertwine `T` compose to a morphism
intertwining `T`.  Stated at general objects, so that no tensor-power
arity enters the rewriting. -/
private theorem step_shuffle [Category.{v} A]
    {P Q : A} {s u : P ⟶ P} {T : P ⟶ Q}
    {s' u' : Q ⟶ Q} (hs : s ≫ T = T ≫ s') (hu : u ≫ T = T ≫ u') :
    (s ≫ u) ≫ T = T ≫ (s' ≫ u') := by
  rw [Category.assoc, hu, ← Category.assoc, hs, Category.assoc]

section Symmetric

/-- The braiding conjugate that defines `swapTop` is natural, at a
general base object. -/
private theorem swap_conj_natural
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    {P Q X Y : A} (g : P ⟶ Q)
    (f : X ⟶ Y) :
    ((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv) ≫
        ((g ⊗ₘ f) ⊗ₘ f) =
      ((g ⊗ₘ f) ⊗ₘ f) ≫
        ((α_ Q Y Y).hom ≫ (Q ◁ (β_ Y Y).hom) ≫ (α_ Q Y Y).inv) := by
  have hmid : (g ⊗ₘ (f ⊗ₘ f)) ≫ (Q ◁ (β_ Y Y).hom) =
      (P ◁ (β_ X X).hom) ≫ (g ⊗ₘ (f ⊗ₘ f)) :=
    tensor_middle _ _ _ _ _ (BraidedCategory.braiding_naturality f f)
  simp only [Category.assoc]
  rw [← MonoidalCategory.associator_inv_naturality,
    ← reassoc_of% hmid,
    ← MonoidalCategory.associator_naturality_assoc]

/-- **Naturality of the top braiding**: `swapTop` commutes with a
tensor power of `f`, by naturality of the associator and of the
braiding. -/
theorem swapTop_natural
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    {X Y : A} (f : X ⟶ Y) (n : ℕ) :
    swapTop X n ≫ tensorPowMap f (n + 2) =
      tensorPowMap f (n + 2) ≫ swapTop Y n :=
  swap_conj_natural (tensorPowMap f n) f

/-- **Naturality of the insertion cycle**, by the recursion that
defines it: each bubbling step is a top braiding, natural by
`swapTop_natural`, whiskered by factors `f` passes through by
`whisker_pass`. -/
theorem insertTop_natural
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    {X Y : A} (f : X ⟶ Y) :
    ∀ n k : ℕ,
      insertTop X n k ≫ tensorPowMap f (n + 1) =
        tensorPowMap f (n + 1) ≫ insertTop Y n k := by
  intro n
  induction n with
  | zero =>
    intro k
    rw [insertTop_of_zero, insertTop_of_zero, Category.id_comp,
      Category.comp_id]
  | succ n ih =>
    intro k
    cases k with
    | zero =>
      rw [insertTop_zero, insertTop_zero, Category.id_comp,
        Category.comp_id]
    | succ k =>
      have hw : (insertTop X n k ▷ X) ≫ tensorPowMap f (n + 1 + 1) =
          tensorPowMap f (n + 1 + 1) ≫ (insertTop Y n k ▷ Y) :=
        whisker_pass f (ih k)
      have hs : swapTop X n ≫ tensorPowMap f (n + 1 + 1) =
          tensorPowMap f (n + 1 + 1) ≫ swapTop Y n :=
        swapTop_natural f n
      rw [insertTop_succ, insertTop_succ]
      exact step_shuffle hs hw

/-- **Naturality of the permutation action**: the action of any
permutation commutes with a tensor power of `f`.  The proof is the
recursion of `permMor` itself. -/
theorem permMor_natural
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    {X Y : A} (f : X ⟶ Y) :
    ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)),
      permMor X n σ ≫ tensorPowMap f n =
        tensorPowMap f n ≫ permMor Y n σ := by
  intro n
  induction n with
  | zero =>
    intro σ
    show 𝟙 (𝟙_ A) ≫ 𝟙 (𝟙_ A) = 𝟙 (𝟙_ A) ≫ 𝟙 (𝟙_ A)
    rfl
  | succ n ih =>
    intro σ
    have hw : (permMor X n (restPerm σ) ▷ X) ≫ tensorPowMap f (n + 1) =
        tensorPowMap f (n + 1) ≫ (permMor Y n (restPerm σ) ▷ Y) :=
      whisker_pass f (ih (restPerm σ))
    rw [permMor_succ, permMor_succ]
    exact step_shuffle hw (insertTop_natural f n (n - (topImage σ : ℕ)))

end Symmetric

section Linear

/-- **Naturality of the symmetric-group action**: the action of any
group-algebra element commutes with a tensor power of `f`.  Both
sides are `ℂ`-linear in the element, so the statement reduces to
basis permutations, where it is `permMor_natural`. -/
theorem permAlg_natural
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    {X Y : A} (f : X ⟶ Y) (n : ℕ)
    (x : SymGroupAlgebra n) :
    permAlg X n x ≫ tensorPowMap f n =
      tensorPowMap f n ≫ permAlg Y n x := by
  induction x using MonoidAlgebra.induction_on with
  | hM σ =>
    rw [show (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n))) σ =
        MonoidAlgebra.single σ (1 : ℂ) from rfl,
      permAlg_single, permAlg_single]
    exact permMor_natural f n σ
  | hadd x y hx hy =>
    rw [map_add, map_add]
    exact intertwine_add hx hy
  | hsmul r x hx =>
    rw [map_smul, map_smul]
    exact intertwine_smul r hx

/-! ## Stability of Schur vanishing

The idempotent-level form of Deligne's 1.19 (Catégories
tensorielles): Schur vanishing passes along monomorphisms,
epimorphisms and isomorphisms, by cancelling the tensor power of the
morphism against the naturality square.
-/

/-- A morphism intertwined with zero across a monomorphism is zero.
Stated at general objects. -/
private theorem zero_of_intertwine_mono [Category.{v} A] [Preadditive A]
    {P Q : A} {a : P ⟶ P}
    {b : Q ⟶ Q} {T : P ⟶ Q} [Mono T] (hnat : a ≫ T = T ≫ b)
    (hb : b = 0) : a = 0 :=
  zero_of_comp_mono T (by rw [hnat, hb, comp_zero])

/-- A morphism intertwined with zero across an epimorphism is zero.
Stated at general objects. -/
private theorem zero_of_intertwine_epi [Category.{v} A] [Preadditive A]
    {P Q : A} {a : P ⟶ P}
    {b : Q ⟶ Q} {T : P ⟶ Q} [Epi T] (hnat : a ≫ T = T ≫ b)
    (ha : a = 0) : b = 0 :=
  zero_of_epi_comp T (by rw [← hnat, ha, zero_comp])

/-- A morphism intertwined with zero across a split epimorphism is
zero.  Stated at general objects. -/
private theorem zero_of_intertwine_split [Category.{v} A] [Preadditive A]
    {P Q : A} {a : P ⟶ P}
    {b : Q ⟶ Q} {T : P ⟶ Q} {S : Q ⟶ P} (hST : S ≫ T = 𝟙 Q)
    (hnat : a ≫ T = T ≫ b) (ha : a = 0) : b = 0 := by
  calc b = (S ≫ T) ≫ b := by rw [hST, Category.id_comp]
    _ = S ≫ a ≫ T := by rw [Category.assoc, ← hnat]
    _ = 0 := by rw [ha, zero_comp, comp_zero]

/-- **Schur vanishing descends along monomorphisms** (the
subobject half of Deligne's 1.19, at the idempotent level): if the
block idempotent of `μ` kills `X ^ ⊗ μ.card` and `Y ⟶ X` is a
monomorphism, it kills `Y ^ ⊗ μ.card` as well. -/
theorem SchurKilled.of_mono
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    [RigidCategory A] (P : SchurPackage.{v})
    {X Y : A} (f : Y ⟶ X) [Mono f] {μ : YoungDiagram}
    (h : SchurKilled P X μ) : SchurKilled P Y μ := by
  haveI := tensorPowMap_mono f μ.card
  exact zero_of_intertwine_mono (permAlg_natural f μ.card (P.e μ)) h

/-- **Schur vanishing descends along epimorphisms** (the quotient
half of Deligne's 1.19, at the idempotent level). -/
theorem SchurKilled.of_epi
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    [RigidCategory A] (P : SchurPackage.{v})
    {X Y : A} (f : X ⟶ Y) [Epi f] {μ : YoungDiagram}
    (h : SchurKilled P X μ) : SchurKilled P Y μ := by
  haveI := tensorPowMap_epi f μ.card
  exact zero_of_intertwine_epi (permAlg_natural f μ.card (P.e μ)) h

/-- **Schur vanishing is invariant under isomorphism.**  No rigidity
is needed: the tensor power of `e.inv` splits the tensor power of
`e.hom`, and the naturality square does the rest. -/
theorem SchurKilled.of_iso
    [Category.{v} A] [MonoidalCategory A] [SymmetricCategory A]
    [Preadditive A] [Linear ℂ A]
    (P : SchurPackage.{v}) {X Y : A}
    (e : X ≅ Y) {μ : YoungDiagram} (h : SchurKilled P X μ) :
    SchurKilled P Y μ := by
  have hST : tensorPowMap e.inv μ.card ≫ tensorPowMap e.hom μ.card =
      𝟙 (tensorPow A Y μ.card) := by
    rw [← tensorPowMap_comp, e.inv_hom_id, tensorPowMap_id]
  exact zero_of_intertwine_split hST
    (permAlg_natural e.hom μ.card (P.e μ)) h

end Linear

end RS
