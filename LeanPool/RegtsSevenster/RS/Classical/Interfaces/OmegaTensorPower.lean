/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Interfaces.OmegaPerm
public import LeanPool.RegtsSevenster.RS.Classical.Super.ColourPower

/-!
# Tensor-power decomposition of the fibre-functor image

The fibre functor `ω` of a Deligne package sends the skein object
`SkeinObj.mk n` to a super vector space that is canonically
isomorphic to the `n`-th monoidal power of `V := ω.obj (SkeinObj.mk 1)`.
This file builds the chain:

## Part A — Iterated tensorator

* `omegaPow n : superPow V n ≅ ω.obj (SkeinObj.mk n)` —
  by induction on `n` using the unit comparison `ε`/`η` and
  the tensorator `μ`/`δ`.

## Part B — Conjugated action

* `superPermAction n` — the algebra homomorphism
  `SymGroupAlgebra n →ₐ[ℂ] End (superPow V n)` obtained by
  conjugating `omegaSkeinRep` through `omegaPow`.
* `superPermAction_eq_zero_iff` — conjugation by an iso preserves
  zero: `superPermAction x = 0 ↔ omegaSkeinRep x = 0`.

## Part C — The permutation-level formula

* `superPermAction_perm` — on a single permutation `σ`,
  `superPermAction σ` equals the conjugation of `ω.map (permClass σ)`
  by `omegaPow`.
-/

@[expose] public section

noncomputable section

namespace RS

open CategoryTheory MonoidalCategory Category
open Functor.LaxMonoidal Functor.OplaxMonoidal

variable {R : ℕ} (f : EdgeRankParameter R)
  (P : DelignePackage (SkeinObj f))

/-! ### Part A: The iterated tensorator -/

/-- Abbreviation for the strand image. -/
abbrev strandImage : SuperVect :=
  P.ω.obj (SkeinObj.mk 1)

/-- The forward map of the iterated tensorator:
`superPow V n ⟶ ω.obj (SkeinObj.mk n)`, built left-nested
using the unit comparison and the tensorator. -/
noncomputable def omegaPowHom :
    (n : ℕ) → (superPow (strandImage f P) n ⟶
      P.ω.obj (SkeinObj.mk n))
  | 0 =>
      letI := P.braided
      ε P.ω
  | n + 1 =>
      letI := P.braided
      ((omegaPowHom n ⊗ₘ (𝟙 (P.ω.obj (SkeinObj.mk 1)))) ≫
        μ P.ω (SkeinObj.mk n) (SkeinObj.mk 1))

/-- The backward map of the iterated tensorator:
`ω.obj (SkeinObj.mk n) ⟶ superPow V n`, built by inverting
the tensorator at each step. -/
noncomputable def omegaPowInv :
    (n : ℕ) → (P.ω.obj (SkeinObj.mk n) ⟶
      superPow (strandImage f P) n)
  | 0 =>
      letI := P.braided
      η P.ω
  | n + 1 =>
      letI := P.braided
      (δ P.ω (SkeinObj.mk n) (SkeinObj.mk 1) ≫
        (omegaPowInv n ⊗ₘ (𝟙 (P.ω.obj (SkeinObj.mk 1)))))

/-- The backward-then-forward composite is the identity
(the fibre side). -/
theorem omegaPow_inv_hom :
    ∀ n : ℕ,
      (omegaPowInv f P n ≫ omegaPowHom f P n :
        P.ω.obj (SkeinObj.mk n) ⟶
          P.ω.obj (SkeinObj.mk n)) =
        𝟙 (P.ω.obj (SkeinObj.mk n))
  | 0 => by
    let := P.braided
    change (η P.ω ≫ ε P.ω : P.ω.obj (SkeinObj.mk 0) ⟶ _) = 𝟙 _
    exact Functor.Monoidal.η_ε P.ω
  | n + 1 => by
    let := P.braided
    change (δ P.ω (SkeinObj.mk n) (SkeinObj.mk 1) ≫
        (omegaPowInv f P n ⊗ₘ 𝟙 (P.ω.obj (SkeinObj.mk 1)))) ≫
      ((omegaPowHom f P n ⊗ₘ 𝟙 (P.ω.obj (SkeinObj.mk 1))) ≫
        μ P.ω (SkeinObj.mk n) (SkeinObj.mk 1)) = 𝟙 _
    simp only [assoc]
    rw [← assoc (omegaPowInv f P n ⊗ₘ _)]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [omegaPow_inv_hom n, comp_id]
    rw [MonoidalCategory.id_tensorHom_id]
    rw [id_comp]
    exact Functor.Monoidal.δ_μ P.ω (SkeinObj.mk n) (SkeinObj.mk 1)

/-- The forward-then-backward composite is the identity
(the model side). -/
theorem omegaPow_hom_inv :
    ∀ n : ℕ,
      (omegaPowHom f P n ≫ omegaPowInv f P n :
        superPow (strandImage f P) n ⟶
          superPow (strandImage f P) n) =
        𝟙 (superPow (strandImage f P) n)
  | 0 => by
    let := P.braided
    change (ε P.ω ≫ η P.ω : SuperVect.tensorUnit ⟶ _) = 𝟙 _
    exact Functor.Monoidal.ε_η P.ω
  | n + 1 => by
    let := P.braided
    change ((omegaPowHom f P n ⊗ₘ 𝟙 (P.ω.obj (SkeinObj.mk 1))) ≫
        μ P.ω (SkeinObj.mk n) (SkeinObj.mk 1)) ≫
      (δ P.ω (SkeinObj.mk n) (SkeinObj.mk 1) ≫
        (omegaPowInv f P n ⊗ₘ 𝟙 (P.ω.obj (SkeinObj.mk 1)))) = 𝟙 _
    simp only [assoc]
    rw [← assoc (μ P.ω (SkeinObj.mk n) (SkeinObj.mk 1))]
    rw [show (μ P.ω (SkeinObj.mk n) (SkeinObj.mk 1) :
          P.ω.obj (SkeinObj.mk n) ⊗ P.ω.obj (SkeinObj.mk 1) ⟶
            P.ω.obj (SkeinObj.mk (n + 1))) ≫
        δ P.ω (SkeinObj.mk n) (SkeinObj.mk 1) = 𝟙 _ from
      Functor.Monoidal.μ_δ P.ω (SkeinObj.mk n) (SkeinObj.mk 1)]
    rw [id_comp]
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    rw [omegaPow_hom_inv n, comp_id]
    exact MonoidalCategory.id_tensorHom_id _ _

/-- **The iterated tensorator**: the `n`-th monoidal power of the
strand image is isomorphic to `ω.obj (SkeinObj.mk n)`, built by
iterating the tensorator `μ`/`δ`. -/
noncomputable def omegaPow (n : ℕ) :
    superPow (strandImage f P) n ≅ P.ω.obj (SkeinObj.mk n) where
  hom := omegaPowHom f P n
  inv := omegaPowInv f P n
  hom_inv_id := omegaPow_hom_inv f P n
  inv_hom_id := omegaPow_inv_hom f P n

/-! ### Part B: The conjugated action -/

/-- Conjugation of an endomorphism by an isomorphism:
`e.hom ≫ f ≫ e.inv`, transporting `f : End Y` to `End X`
via `e : X ≅ Y`. -/
def isoConj {C : Type*} [Category C] {X Y : C} (e : X ≅ Y)
    (f : End Y) : End X :=
  e.hom ≫ f ≫ e.inv

/-- Conjugation by an isomorphism, unfolded. -/
@[simp]
theorem isoConj_unfold {C : Type*} [Category C] {X Y : C}
    (e : X ≅ Y) (f : End Y) :
    isoConj e f = e.hom ≫ f ≫ e.inv := rfl

/-- It preserves the identity. -/
theorem isoConj_one {C : Type*} [Category C] {X Y : C}
    (e : X ≅ Y) :
    isoConj e (𝟙 Y) = 𝟙 X := by
  simp only [isoConj, id_comp, e.hom_inv_id]

/-- And composition. -/
theorem isoConj_mul {C : Type*} [Category C]
    {X Y : C} (e : X ≅ Y) (f g : End Y) :
    isoConj e (f ≫ g) =
      isoConj e f ≫ isoConj e g := by
  simp only [isoConj, assoc]
  rw [← assoc e.inv e.hom, e.inv_hom_id, id_comp]

/-- It sends zero to zero. -/
theorem isoConj_zero {C : Type*} [Category C] [Preadditive C]
    {X Y : C} (e : X ≅ Y) :
    isoConj e (0 : End Y) = 0 := by
  change e.hom ≫ (0 : Y ⟶ Y) ≫ e.inv = 0
  simp

/-- And is additive — so it is an algebra map on endomorphisms. -/
theorem isoConj_add {C : Type*} [Category C] [Preadditive C]
    {X Y : C} (e : X ≅ Y) (f g : End Y) :
    isoConj e (f + g) = isoConj e f + isoConj e g := by
  change e.hom ≫ (f + g) ≫ e.inv =
    e.hom ≫ f ≫ e.inv + e.hom ≫ g ≫ e.inv
  have h1 : (f + g) ≫ e.inv = f ≫ e.inv + g ≫ e.inv :=
    map_add (Preadditive.rightComp Y e.inv) f g
  rw [h1]
  exact map_add (Preadditive.leftComp X e.hom) (f ≫ e.inv) (g ≫ e.inv)

/-- Conjugation by an iso preserves scalar multiplication. -/
theorem isoConj_smul {C : Type*} [Category C] [Preadditive C]
    [Linear ℂ C] {X Y : C} (e : X ≅ Y)
    (r : ℂ) (f : End Y) :
    isoConj e (r • f) = r • isoConj e f := by
  change e.hom ≫ (r • f) ≫ e.inv = r • (e.hom ≫ f ≫ e.inv)
  have h1 : (r • f) ≫ e.inv = r • (f ≫ e.inv) :=
    Linear.smul_comp _ _ _ r f e.inv
  rw [h1]
  exact Linear.comp_smul _ _ _ e.hom r (f ≫ e.inv)

/-- Conjugation by an iso is injective. -/
theorem isoConj_injective {C : Type*} [Category C]
    {X Y : C}
    (e : X ≅ Y) : Function.Injective (isoConj e) := by
  intro f g (h : e.hom ≫ f ≫ e.inv = e.hom ≫ g ≫ e.inv)
  have h2 : e.inv ≫ (e.hom ≫ f ≫ e.inv) ≫ e.hom =
      e.inv ≫ (e.hom ≫ g ≫ e.inv) ≫ e.hom := by rw [h]
  simp only [Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] at h2
  exact h2

/-- Conjugation by an iso preserves zero iff:
`isoConj e f = 0 ↔ f = 0`. -/
theorem isoConj_eq_zero_iff {C : Type*} [Category C]
    [Preadditive C] {X Y : C} (e : X ≅ Y) (f : End Y) :
    isoConj e f = 0 ↔ f = 0 := by
  constructor
  · intro h
    exact isoConj_injective e (h.trans (isoConj_zero e).symm)
  · intro h
    rw [h, isoConj_zero]

/-- **The transported symmetric-group action on the tensor power**:
the algebra homomorphism obtained by conjugating `omegaSkeinRep`
through the iterated tensorator `omegaPow`. -/
noncomputable def superPermAction (n : ℕ) :
    SymGroupAlgebra n →ₐ[ℂ]
      End (superPow (strandImage f P) n) := by
  letI := P.additive
  letI := P.linear
  exact {
    toFun := fun x => isoConj (omegaPow f P n)
      (omegaSkeinRep f P n x)
    map_one' := by rw [map_one]; exact isoConj_one _
    map_mul' := fun x y => by
      rw [map_mul]; exact isoConj_mul _ _ _
    map_zero' := by rw [map_zero]; exact isoConj_zero _
    map_add' := fun x y => by
      rw [map_add]; exact isoConj_add _ _ _
    commutes' := fun r => by
      simp only [Algebra.algebraMap_eq_smul_one, map_smul,
        map_one]
      -- Goal: isoConj e (r • 1) = r • 1
      -- where 1 : End Y = 𝟙 Y
      have h1 : (1 : End (P.ω.obj (SkeinObj.mk n))) =
        𝟙 (P.ω.obj (SkeinObj.mk n)) := rfl
      have h2 : (1 : End (superPow (strandImage f P) n)) =
        𝟙 (superPow (strandImage f P) n) := rfl
      rw [h1, isoConj_smul, isoConj_one, h2]
  }

/-- **Zero equivalence**: the transported action kills an element
if and only if the original fibre-functor action does. -/
theorem superPermAction_eq_zero_iff (n : ℕ)
    (x : SymGroupAlgebra n) :
    letI := P.additive
    letI := P.linear
    superPermAction f P n x = 0 ↔
      omegaSkeinRep f P n x = 0 := by
  let := P.additive
  let := P.linear
  exact isoConj_eq_zero_iff (omegaPow f P n)
    (omegaSkeinRep f P n x)

/-! ### Part C: Permutation-level formula -/

/-- On a single permutation, `superPermAction` is the conjugation
of `ω.map (permClass σ)` by `omegaPow`. -/
theorem superPermAction_perm (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    letI := P.additive
    letI := P.linear
    superPermAction f P n
      (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ) =
      isoConj (omegaPow f P n)
        (P.ω.map (permClass f n σ)) := by
  let := P.additive
  let := P.linear
  change isoConj (omegaPow f P n)
    (omegaSkeinRep f P n
      (MonoidAlgebra.of ℂ (Equiv.Perm (Fin n)) σ)) = _
  rw [omegaSkeinRep_of]

end RS

end
