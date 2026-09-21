/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

universe u

noncomputable section

open Monoid.Coprod

namespace MarshallHall

/-!
## Binary free products and the Grushko rank calculation

The binary coproduct of two free groups is identified explicitly with the free
group on the disjoint union of their bases.  The lower bound in the rank
calculation is obtained from abelianization, so the result is not merely a
cardinality calculation transported through an unproved presentation.
-/

abbrev BinaryFreeProduct (α β : Type u) := FreeGroup α ∗ FreeGroup β

def factorInclusionLeft {α β : Type u} : FreeGroup α →* BinaryFreeProduct α β :=
  Monoid.Coprod.inl

def factorInclusionRight {α β : Type u} : FreeGroup β →* BinaryFreeProduct α β :=
  Monoid.Coprod.inr

def binaryFreeProductToFree {α β : Type u} :
    BinaryFreeProduct α β →* FreeGroup (α ⊕ β) :=
  Monoid.Coprod.lift (FreeGroup.map Sum.inl) (FreeGroup.map Sum.inr)

def freeToBinaryFreeProduct {α β : Type u} :
    FreeGroup (α ⊕ β) →* BinaryFreeProduct α β :=
  FreeGroup.lift (fun x => match x with
    | Sum.inl a => factorInclusionLeft (FreeGroup.of a)
    | Sum.inr b => factorInclusionRight (FreeGroup.of b))

@[simp]
theorem binaryFreeProductToFree_left {α β : Type u} (a : α) :
    binaryFreeProductToFree (α := α) (β := β)
      (factorInclusionLeft (FreeGroup.of a)) = FreeGroup.of (Sum.inl a) := by
  simp [binaryFreeProductToFree, factorInclusionLeft]

@[simp]
theorem binaryFreeProductToFree_right {α β : Type u} (b : β) :
    binaryFreeProductToFree (α := α) (β := β)
      (factorInclusionRight (FreeGroup.of b)) = FreeGroup.of (Sum.inr b) := by
  simp [binaryFreeProductToFree, factorInclusionRight]

@[simp]
theorem freeToBinaryFreeProduct_left {α β : Type u} (a : α) :
    freeToBinaryFreeProduct (α := α) (β := β) (FreeGroup.of (Sum.inl a)) =
      factorInclusionLeft (FreeGroup.of a) := by
  simp [freeToBinaryFreeProduct]

@[simp]
theorem freeToBinaryFreeProduct_right {α β : Type u} (b : β) :
    freeToBinaryFreeProduct (α := α) (β := β) (FreeGroup.of (Sum.inr b)) =
      factorInclusionRight (FreeGroup.of b) := by
  simp [freeToBinaryFreeProduct]

theorem binaryFreeProduct_comp_left {α β : Type u} :
    (freeToBinaryFreeProduct (α := α) (β := β)).comp
        (binaryFreeProductToFree (α := α) (β := β)) = MonoidHom.id _ := by
  apply Monoid.Coprod.hom_ext
  · have hmap : (freeToBinaryFreeProduct (α := α) (β := β)).comp
        (FreeGroup.map Sum.inl) = factorInclusionLeft := by
      apply FreeGroup.ext_hom
      intro a
      simp [freeToBinaryFreeProduct]
    simpa only [MonoidHom.comp_assoc, binaryFreeProductToFree,
      Monoid.Coprod.lift_comp_inl, MonoidHom.id_comp, factorInclusionLeft] using hmap
  · have hmap : (freeToBinaryFreeProduct (α := α) (β := β)).comp
        (FreeGroup.map Sum.inr) = factorInclusionRight := by
      apply FreeGroup.ext_hom
      intro b
      simp [freeToBinaryFreeProduct]
    simpa only [MonoidHom.comp_assoc, binaryFreeProductToFree,
      Monoid.Coprod.lift_comp_inr, MonoidHom.id_comp, factorInclusionRight] using hmap

theorem binaryFreeProduct_comp_right {α β : Type u} :
    (binaryFreeProductToFree (α := α) (β := β)).comp
        (freeToBinaryFreeProduct (α := α) (β := β)) = MonoidHom.id _ := by
  apply FreeGroup.ext_hom
  intro x
  cases x with
  | inl a =>
      rw [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [freeToBinaryFreeProduct_left, binaryFreeProductToFree_left]
  | inr b =>
      rw [MonoidHom.comp_apply, MonoidHom.id_apply]
      rw [freeToBinaryFreeProduct_right, binaryFreeProductToFree_right]

def binaryFreeProductEquiv {α β : Type u} :
    BinaryFreeProduct α β ≃* FreeGroup (α ⊕ β) :=
  MulEquiv.ofBijective (binaryFreeProductToFree (α := α) (β := β)) ⟨
    (fun x y h => by
      have h' := congrArg (fun z => freeToBinaryFreeProduct (α := α) (β := β) z) h
      have hcomp := binaryFreeProduct_comp_left (α := α) (β := β)
      calc
        x = freeToBinaryFreeProduct (α := α) (β := β)
              (binaryFreeProductToFree (α := α) (β := β) x) := by
          have hx := congrArg (fun f : BinaryFreeProduct α β →* BinaryFreeProduct α β => f x) hcomp
          exact hx.symm
        _ = freeToBinaryFreeProduct (α := α) (β := β)
              (binaryFreeProductToFree (α := α) (β := β) y) := h'
        _ = y := by
          have hy := congrArg (fun f : BinaryFreeProduct α β →* BinaryFreeProduct α β => f y) hcomp
          exact hy),
    (fun y => ⟨freeToBinaryFreeProduct (α := α) (β := β) y, by
      have hy := congrArg (fun f : FreeGroup (α ⊕ β) →* FreeGroup (α ⊕ β) => f y)
        (binaryFreeProduct_comp_right (α := α) (β := β))
      exact hy⟩)⟩

@[simp]
theorem binaryFreeProductEquiv_inl {α β : Type u} (x : FreeGroup α) :
    binaryFreeProductEquiv (α := α) (β := β) (Monoid.Coprod.inl x) =
      FreeGroup.map Sum.inl x := by
  have hmap :
      (binaryFreeProductToFree (α := α) (β := β)).comp
          (factorInclusionLeft (α := α) (β := β)) = FreeGroup.map Sum.inl := by
    apply FreeGroup.ext_hom
    intro a
    simp [binaryFreeProductToFree, factorInclusionLeft]
  change binaryFreeProductToFree (factorInclusionLeft x) = FreeGroup.map Sum.inl x
  exact congrArg (fun f : FreeGroup α →* FreeGroup (α ⊕ β) => f x) hmap

def abelianizedValue {α : Type u} (x : FreeGroup α) : FreeAbelianGroup α :=
  Additive.ofMul (Abelianization.of x)

@[simp]
theorem abelianizedValue_one {α : Type u} :
    abelianizedValue (1 : FreeGroup α) = 0 := by
  simp [abelianizedValue]
  rfl

@[simp]
theorem abelianizedValue_mul {α : Type u} (x y : FreeGroup α) :
    abelianizedValue (x * y) = abelianizedValue x + abelianizedValue y := by
  change Additive.ofMul (Abelianization.of (x * y)) = _
  rw [map_mul]
  rfl

@[simp]
theorem abelianizedValue_inv {α : Type u} (x : FreeGroup α) :
    abelianizedValue x⁻¹ = -abelianizedValue x := by
  change Additive.ofMul (Abelianization.of x⁻¹) = _
  rw [map_inv]
  rfl

@[simp]
theorem abelianizedValue_of {α : Type u} (a : α) :
    abelianizedValue (FreeGroup.of a) = FreeAbelianGroup.of a := rfl

theorem rank_freeGroup_finite (α : Type u) [Fintype α] :
    Group.rank (FreeGroup α) = Fintype.card α := by
  classical
  let S₀ : Finset (FreeGroup α) := Finset.univ.image FreeGroup.of
  have hS₀ : Subgroup.closure (S₀ : Set (FreeGroup α)) = ⊤ := by
    rw [Finset.coe_image]
    simpa using (FreeGroup.closure_range_of α)
  have hup : Group.rank (FreeGroup α) ≤ Fintype.card α := by
    apply (Group.rank_le hS₀).trans_eq
    rw [show S₀.card = (Finset.univ : Finset α).card by
      simp [S₀, Finset.card_image_of_injective _ FreeGroup.of_injective]]
    simp
  obtain ⟨S, hcard, hS⟩ := Group.rank_spec (FreeGroup α)
  let T : Finset (FreeAbelianGroup α) := S.image abelianizedValue
  have hspan : Submodule.span ℤ (T : Set (FreeAbelianGroup α)) = ⊤ := by
    apply top_unique
    intro x hx
    clear hx
    induction x using FreeAbelianGroup.induction_on with
    | zero =>
        rw [← abelianizedValue_one]
        exact (Submodule.span ℤ (T : Set (FreeAbelianGroup α))).zero_mem
    | of a =>
        have ha : FreeGroup.of a ∈ Subgroup.closure (S : Set (FreeGroup α)) := by
          rw [hS]
          trivial
        have hp : abelianizedValue (FreeGroup.of a) ∈
            Submodule.span ℤ (T : Set (FreeAbelianGroup α)) := by
          refine Subgroup.closure_induction (p := fun y _ =>
            abelianizedValue y ∈ Submodule.span ℤ (T : Set (FreeAbelianGroup α))) ?_ ?_ ?_ ?_ ha
          · intro y hy
            exact Submodule.subset_span (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
          · rw [abelianizedValue_one]
            exact (Submodule.span ℤ (T : Set (FreeAbelianGroup α))).zero_mem
          · intro y z _ _ hy hz
            rw [abelianizedValue_mul]
            exact (Submodule.span ℤ (T : Set (FreeAbelianGroup α))).add_mem hy hz
          · intro y _ hy
            rw [abelianizedValue_inv]
            exact (Submodule.span ℤ (T : Set (FreeAbelianGroup α))).neg_mem hy
        simpa only [abelianizedValue_of] using hp
    | neg x ih =>
        exact (Submodule.span ℤ (T : Set (FreeAbelianGroup α))).neg_mem ih
    | add x y ihx ihy =>
        exact (Submodule.span ℤ (T : Set (FreeAbelianGroup α))).add_mem ihx ihy
  have hlow : Fintype.card α ≤ S.card := by
    have hfin := finrank_span_finset_le_card (R := ℤ)
      (M := FreeAbelianGroup α) T
    have hfin' : Module.finrank ℤ (FreeAbelianGroup α) ≤ T.card := by
      change Module.finrank ℤ (Submodule.span ℤ (T : Set (FreeAbelianGroup α))) ≤ T.card at hfin
      rw [hspan] at hfin
      simpa only [finrank_top] using hfin
    rw [Module.finrank_eq_card_basis (FreeAbelianGroup.basis α)] at hfin'
    have hT : T.card ≤ S.card := by
      simpa only [T] using
        (Finset.card_image_le : (S.image abelianizedValue).card ≤ S.card)
    exact hfin'.trans hT
  exact le_antisymm hup (by simpa [hcard] using hlow)

instance binaryFreeProduct_fg {α β : Type u} [Fintype α] [Fintype β] :
    Group.FG (BinaryFreeProduct α β) :=
  Group.fg_iff_monoid_fg.mpr
    (Monoid.fg_of_surjective (binaryFreeProductEquiv (α := α) (β := β)).symm.toMonoidHom
      (binaryFreeProductEquiv (α := α) (β := β)).symm.surjective)

/-- Binary Grushko--Neumann for finite-rank free groups. -/
theorem rank_binaryFreeProduct {α β : Type u} [Fintype α] [Fintype β] :
    Group.rank (BinaryFreeProduct α β) = Fintype.card α + Fintype.card β := by
  classical
  rw [Group.rank_congr binaryFreeProductEquiv]
  rw [rank_freeGroup_finite]
  simp [Fintype.card_sum]

end MarshallHall
