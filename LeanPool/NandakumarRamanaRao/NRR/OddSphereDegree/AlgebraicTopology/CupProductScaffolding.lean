/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularCohomology
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# Cochain tensor-product infrastructure for the cup product

Registers the additive and sign instances needed to tensor chain and cochain
complexes over `ModuleCat`, and packages the singular cochain tensor square with
its functoriality laws. This is the algebraic substrate consumed by the
Alexander–Whitney and cup-product modules; the diagonal itself is constructed
in those later modules rather than in this file.
-/

@[expose] public section
open CategoryTheory MonoidalCategory Limits

namespace SphereOddDegree

/-! ## 1. Coefficient-category wiring (gap `U6`)

The chain/cochain monoidal structure on `HomologicalComplex C c` requires the
additivity of `curriedTensor C` both in its argument object and as a functor.
Both follow from `MonoidalPreadditive C` but are not registered upstream. -/

section CoeffWiring

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]

/-- For a preadditive monoidal category with `MonoidalPreadditive`, tensoring on
the left by a fixed object is an additive functor. This is the
`((curriedTensor C).obj X).Additive` side condition required by
`HomologicalComplex.monoidalCategory`; it holds because
`(curriedTensor C).obj X` is definitionally `tensorLeft X`. -/
instance curriedTensorObj_additive (X : C) : ((curriedTensor C).obj X).Additive :=
  inferInstanceAs (tensorLeft X).Additive

/-- For a preadditive monoidal category with `MonoidalPreadditive`, the currying
functor `curriedTensor C : C ⥤ C ⥤ C` is itself additive. This is the
`(curriedTensor C).Additive` side condition required by
`HomologicalComplex.monoidalCategory`; additivity in the first variable is
`MonoidalPreadditive.add_tensor` componentwise. -/
instance curriedTensor_additive : (curriedTensor C).Additive := by
  refine ⟨?_⟩
  intro X Y f g
  ext Z
  simp [curriedTensor]

end CoeffWiring

/-! ## 2. Tensor signs for the cochain shape `ComplexShape.up ℕ`

Mathlib registers `TensorSigns` for `down ℕ` and `up ℤ`, but not for `up ℕ`, the
shape of the singular cochain complex. We supply it with the same `(-1)^•`
convention as the chain case. -/

/-- The `ComplexShape.TensorSigns` instance for the cochain shape
`ComplexShape.up ℕ`, using the sign `ε n = (-1)^n`. This instance makes
`HomologicalComplex.monoidalCategory` apply to
`CochainComplex (ModuleCat R) ℕ`. -/
instance tensorSignsUpNat : (ComplexShape.up ℕ).TensorSigns where
  ε' := {
    toFun := fun (i : Multiplicative ℕ) => (-1 : ℤˣ) ^ (Multiplicative.toAdd i)
    map_one' := rfl
    map_mul' := fun x y => by
      change (-1 : ℤˣ) ^ (Multiplicative.toAdd x + Multiplicative.toAdd y) = _
      rw [pow_add]
  }
  rel_add p q r hpq := by
    change p + r + 1 = q + r
    have : p + 1 = q := hpq
    omega
  add_rel p q r hpq := by
    change r + p + 1 = r + q
    have : p + 1 = q := hpq
    omega
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ) ^ (p + 1) = -(-1 : ℤˣ) ^ p
    rw [pow_add, pow_one, mul_neg, mul_one]

/-- The Koszul sign of `ComplexShape.up ℕ` at index `n` is `(-1)^n`. -/
@[simp]
theorem ε_up_nat (n : ℕ) : (ComplexShape.up ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

/-! ## 3. The singular cochain tensor square `C^•(X) ⊗ C^•(X)`

With the wiring of §1–§2 in place, the tensor product of the singular cochain
complex with itself is a genuine cochain complex, functorial in `X`. This is the
domain of a cup product (a map `C^•(X) ⊗ C^•(X) → C^•(X)`), and its
functorial pullback is the naturality substrate for `f^*(a ⌣ b) = f^* a ⌣ f^* b`. -/

/-- The **tensor square of the singular cochain complex** with coefficients in
`M : ModuleCat R`, i.e. `C^•(X; M) ⊗ C^•(X; M)` as a `CochainComplex (ModuleCat R) ℕ`.
This is the cochain-level domain of a cup product `⌣ : C^•(X) ⊗ C^•(X) → C^•(X)`. -/
noncomputable def singularCochainTensorSquare (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (X : TopCat.{0}ᵒᵖ) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  MonoidalCategory.tensorObj ((singularCochainComplexFunctor R M).obj X)
    ((singularCochainComplexFunctor R M).obj X)

/-- The functorial pullback on the cochain tensor square: a continuous map
(packaged as `f : X ⟶ Y` in `TopCatᵒᵖ`) induces `f^* ⊗ f^*` on the tensor
squares. This is `MonoidalCategory.tensorHom` applied to the cochain pullback
`(singularCochainComplexFunctor R M).map f` with itself. -/
noncomputable def singularCochainTensorSquareMap (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) {X Y : TopCat.{0}ᵒᵖ} (f : X ⟶ Y) :
    singularCochainTensorSquare R M X ⟶ singularCochainTensorSquare R M Y :=
  MonoidalCategory.tensorHom ((singularCochainComplexFunctor R M).map f)
    ((singularCochainComplexFunctor R M).map f)

/-- Functoriality: the cochain tensor-square pullback preserves identities. -/
@[simp]
theorem singularCochainTensorSquareMap_id (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) (X : TopCat.{0}ᵒᵖ) :
    singularCochainTensorSquareMap R M (𝟙 X) = 𝟙 _ := by
  rw [singularCochainTensorSquareMap, (singularCochainComplexFunctor R M).map_id]
  exact MonoidalCategory.id_tensorHom_id _ _

/-- Functoriality: the cochain tensor-square pullback preserves composition. -/
theorem singularCochainTensorSquareMap_comp (R : Type) [CommRing R]
    (M : ModuleCat.{0} R) {X Y Z : TopCat.{0}ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z) :
    singularCochainTensorSquareMap R M (f ≫ g)
      = singularCochainTensorSquareMap R M f ≫ singularCochainTensorSquareMap R M g := by
  dsimp [singularCochainTensorSquareMap]
  rw [Functor.map_comp]
  exact (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).symm

/-! ## 4. `ZMod 2` specializations

The downstream `RPⁿ` work uses `ZMod 2` coefficients, where the Koszul sign is
trivial (`-1 = 1`). These are thin abbreviations of the general definitions. -/

/-- The tensor square of the singular `F₂`-cochain complex,
`C^•(X; F₂) ⊗ C^•(X; F₂)`. -/
noncomputable abbrev singularCochainTensorSquareZMod2 (X : TopCat.{0}ᵒᵖ) :
    CochainComplex (ModuleCat.{0} (ZMod 2)) ℕ :=
  singularCochainTensorSquare (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) X

/-- The functorial pullback on the `F₂`-cochain tensor square. -/
noncomputable abbrev singularCochainTensorSquareZMod2Map {X Y : TopCat.{0}ᵒᵖ}
    (f : X ⟶ Y) :
    singularCochainTensorSquareZMod2 X ⟶ singularCochainTensorSquareZMod2 Y :=
  singularCochainTensorSquareMap (ZMod 2) (ModuleCat.of (ZMod 2) (ZMod 2)) f

end SphereOddDegree
