/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Product
public import LeanPool.ClassFieldTheory.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
public import Mathlib.Algebra.GroupWithZero.Action.Prod
/-!
# Low-degree Tate cohomology of binary products

This specializes the dependent-product calculation to two possibly
different coefficient groups.  It is used to join the unrestricted and
integral parts of a supported idele group.
-/

@[expose] public section

noncomputable
section

namespace CyclicCohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand

universe uG uA

variable {G : Type uG} [Group G] [Fintype G]
variable (A B : Type uA)
variable [CommGroup A] [CommGroup B]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]

/-- The two-element dependent family associated with `A × B`. -/
abbrev BinaryCoefficientFamily : Bool → Type uA
  | false => A
  | true => B

/-- Each member of the binary coefficient family inherits its commutative group structure. -/
instance binaryCoefficientFamilyCommGroup :
    ∀ i, CommGroup (BinaryCoefficientFamily A B i)
  | false => inferInstance
  | true => inferInstance

/-- The componentwise `G`-action on the binary coefficient family. -/
@[reducible]
noncomputable def binaryCoefficientFamilyAction :
    ∀ i, MulDistribMulAction G
      (BinaryCoefficientFamily A B i)
  | false => inferInstance
  | true => inferInstance

/-- The binary coefficient family carries the given action on each component. -/
noncomputable instance binaryCoefficientFamilyMulDistribMulAction
    (i : Bool) :
    MulDistribMulAction G
      (BinaryCoefficientFamily A B i) :=
  binaryCoefficientFamilyAction A B i

/-- Reindex a binary product as a dependent family over `Bool`. -/
noncomputable def prodEquivBinaryCoefficientFamily :
    A × B ≃* ∀ i, BinaryCoefficientFamily A B i where
  toFun x
    | false => x.1
    | true => x.2
  invFun x := ⟨x false, x true⟩
  left_inv _ := rfl
  right_inv x := by
    funext i
    cases i <;> rfl
  map_mul' _ _ := by
    funext i
    cases i <;> rfl

omit [Fintype G] in
/-- The binary reindexing is equivariant for the componentwise
actions. -/
theorem prodEquivBinaryCoefficientFamily_smul
    (g : G) (x : A × B) :
    letI : ∀ i, MulDistribMulAction G
        (BinaryCoefficientFamily A B i) :=
      binaryCoefficientFamilyAction A B
    letI : MulDistribMulAction G
        (∀ i, BinaryCoefficientFamily A B i) :=
      piMulDistribMulAction G
        (BinaryCoefficientFamily A B)
    prodEquivBinaryCoefficientFamily A B (g • x) =
      g • prodEquivBinaryCoefficientFamily A B x := by
  funext i
  cases i <;> rfl

/-- Identify the degree-zero cohomology family over `Bool` with its two factors. -/
noncomputable def piHerbrandH0EquivProd :
    (∀ i, HerbrandH0 G
      (BinaryCoefficientFamily A B i)) ≃*
        HerbrandH0 G A × HerbrandH0 G B where
  toFun x := ⟨x false, x true⟩
  invFun x
    | false => x.1
    | true => x.2
  left_inv x := by
    funext i
    cases i <;> rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Identify the degree-minus-one cohomology family over `Bool` with its two factors. -/
noncomputable def piHerbrandHMinusOneEquivProd
    (σ : G) :
    (∀ i, HerbrandHMinusOne G
      (BinaryCoefficientFamily A B i) σ) ≃*
        HerbrandHMinusOne G A σ ×
          HerbrandHMinusOne G B σ where
  toFun x := ⟨x false, x true⟩
  invFun x
    | false => x.1
    | true => x.2
  left_inv x := by
    funext i
    cases i <;> rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Degree-zero Tate cohomology commutes with a binary product. -/
noncomputable def herbrandH0ProdEquiv :
    HerbrandH0 G (A × B) ≃*
      HerbrandH0 G A × HerbrandH0 G B := by
  letI familyAction : ∀ i, MulDistribMulAction G
      (BinaryCoefficientFamily A B i) :=
    binaryCoefficientFamilyAction A B
  letI piAction : MulDistribMulAction G
      (∀ i, BinaryCoefficientFamily A B i) :=
    piMulDistribMulAction G
      (BinaryCoefficientFamily A B)
  exact
    (herbrandH0EquivariantMulEquiv
      (prodEquivBinaryCoefficientFamily A B)
      (prodEquivBinaryCoefficientFamily_smul A B)).trans
      ((herbrandH0PiEquiv
        (G := G) (BinaryCoefficientFamily A B)).trans
        (piHerbrandH0EquivProd A B))

/-- Degree-minus-one Tate cohomology commutes with a binary product. -/
noncomputable def herbrandHMinusOneProdEquiv
    (σ : G) :
    HerbrandHMinusOne G (A × B) σ ≃*
      HerbrandHMinusOne G A σ ×
        HerbrandHMinusOne G B σ := by
  letI familyAction : ∀ i, MulDistribMulAction G
      (BinaryCoefficientFamily A B i) :=
    binaryCoefficientFamilyAction A B
  letI piAction : MulDistribMulAction G
      (∀ i, BinaryCoefficientFamily A B i) :=
    piMulDistribMulAction G
      (BinaryCoefficientFamily A B)
  exact
    (herbrandHMinusOneEquivariantMulEquiv
      (prodEquivBinaryCoefficientFamily A B)
      (prodEquivBinaryCoefficientFamily_smul A B) σ).trans
      ((herbrandHMinusOnePiEquiv
        (G := G) (BinaryCoefficientFamily A B) σ).trans
        (piHerbrandHMinusOneEquivProd A B σ))

/-- Finiteness of degree zero is preserved by a binary product. -/
theorem herbrandH0ProdFinite
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandH0 G B)] :
    Finite (HerbrandH0 G (A × B)) :=
  Finite.of_equiv
    (HerbrandH0 G A × HerbrandH0 G B)
    (herbrandH0ProdEquiv A B).symm.toEquiv

/-- Finiteness of degree minus one is preserved by a binary product. -/
theorem herbrandHMinusOneProdFinite
    (σ : G)
    [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandHMinusOne G B σ)] :
    Finite (HerbrandHMinusOne G (A × B) σ) :=
  Finite.of_equiv
    (HerbrandHMinusOne G A σ ×
      HerbrandHMinusOne G B σ)
    (herbrandHMinusOneProdEquiv A B σ).symm.toEquiv

/-- Cardinality of degree-zero Tate cohomology for a binary product. -/
theorem herbrandH0Prod_card
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandH0 G B)] :
    letI : Finite (HerbrandH0 G (A × B)) :=
      herbrandH0ProdFinite A B
    Nat.card (HerbrandH0 G (A × B)) =
      Nat.card (HerbrandH0 G A) *
        Nat.card (HerbrandH0 G B) := by
  rw [Nat.card_congr (herbrandH0ProdEquiv A B).toEquiv,
    Nat.card_prod]

/-- Cardinality of degree-minus-one Tate cohomology for a binary
product. -/
theorem herbrandHMinusOneProd_card
    (σ : G)
    [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandHMinusOne G B σ)] :
    letI : Finite (HerbrandHMinusOne G (A × B) σ) :=
      herbrandHMinusOneProdFinite A B σ
    Nat.card (HerbrandHMinusOne G (A × B) σ) =
      Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (HerbrandHMinusOne G B σ) := by
  rw [Nat.card_congr
      (herbrandHMinusOneProdEquiv A B σ).toEquiv,
    Nat.card_prod]

/-- The Herbrand quotient of a binary product is the product of the
two Herbrand quotients. -/
theorem herbrandQuotient_prod
    (σ : G)
    [Finite (HerbrandH0 G A)]
    [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)]
    [Finite (HerbrandHMinusOne G B σ)] :
    letI : Finite (HerbrandH0 G (A × B)) :=
      herbrandH0ProdFinite A B
    letI : Finite (HerbrandHMinusOne G (A × B) σ) :=
      herbrandHMinusOneProdFinite A B σ
    herbrandQuotient (G := G) (A := A × B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := B) σ := by
  let : Finite (HerbrandH0 G (A × B)) :=
    herbrandH0ProdFinite A B
  let : Finite (HerbrandHMinusOne G (A × B) σ) :=
    herbrandHMinusOneProdFinite A B σ
  rw [herbrandQuotient_eq_card_ratio,
    herbrandQuotient_eq_card_ratio,
    herbrandQuotient_eq_card_ratio,
    herbrandH0Prod_card A B,
    herbrandHMinusOneProd_card A B σ]
  simp only [Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

end CyclicCohomology
