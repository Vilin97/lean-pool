/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.PointFibre

/-!
# The residue algebra of a complex point

The residue module of a ℂ-point of a super-commutative algebra `S`
has a copy of ℂ for its even part and a vanishing odd part, and the
point makes `S` act through its value.  Multiplication of complex
numbers therefore descends to a morphism `k ⊗ k ⟶ k` of super
modules, and the point itself to a morphism from the unit module,
so the residue module is a commutative monoid object.  Super
modules over `S` are symmetric monoidal, so the middle-four
interchange followed by that multiplication is a comparison
`(M ⊗ k) ⊗ (N ⊗ k) ⟶ (M ⊗ N) ⊗ k`, natural in both variables, and
the monoid laws are exactly what makes it lax monoidal and braided.
The comparison is carried down to super vector spaces in
[Comparison.lean](Comparison.lean).

## Contents

* `RS.pointMulHom`, `RS.pointUnitHom`: the residue module as a
  commutative algebra over the base, with its associativity
  `RS.pointMulHom_assoc`, its two unit laws and its commutativity
  `RS.pointMulHom_comm`.
* `RS.pointBaseMu`, `RS.pointBaseEps`: the comparison morphisms
  over the algebra, with `RS.pointBaseMu_naturality` and the four
  generator formulas `RS.pointBaseMu_evenMap_ee` and companions.
* `RS.pointBaseMu_associativity`, `RS.pointBaseMu_left_unitality`,
  `RS.pointBaseMu_right_unitality`: the three coherence laws of the
  comparison over the algebra — base change over the algebra is lax
  monoidal, and the multiplication of the residue module is what
  makes it so.
* `RS.pointBaseMu_braiding`: the comparison over the algebra
  intertwines the braidings, the residue factor contributing
  nothing because its multiplication is commutative.
* `RS.modAssociator_hom` and its companions: the structural
  morphisms of the category of super modules, in the form the
  generator computations consume.
-/

namespace RS

open CategoryTheory MonoidalCategory
open SuperCommAlgebra (pointMod)
open SuperCommAlgebra.Mod

universe u

/-! ## The residue module is a commutative algebra -/

section ResidueAlgebra

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)

/-- The odd part of the residue module has one element. -/
instance pointMod_odd_subsingleton :
    Subsingleton (pointMod P : S.Mod.{u, u, u, u}).odd :=
  (inferInstance : Subsingleton (ULift.{u} PUnit.{1}))

/-- An element of the odd part of the residue module vanishes. -/
theorem pointMod_odd_eq_zero
    (v : (pointMod P : S.Mod.{u, u, u, u}).odd) : v = 0 :=
  Subsingleton.elim _ _

/-- The even action on the residue module is multiplication by the
value of the point. -/
theorem pointMod_actEE (x : S.even)
    (c : (pointMod P : S.Mod.{u, u, u, u}).even) :
    (pointMod P).actEE x c = ULift.up (P.chi x * c.down) := rfl

/-- The odd action on the even part of the residue module
vanishes. -/
theorem pointMod_actOE (u : S.odd)
    (c : (pointMod P : S.Mod.{u, u, u, u}).even) :
    (pointMod P).actOE u c = 0 := rfl

/-- The odd action on the odd part of the residue module
vanishes. -/
theorem pointMod_actOO (u : S.odd)
    (v : (pointMod P : S.Mod.{u, u, u, u}).odd) :
    (pointMod P).actOO u v = 0 := rfl

/-- **The multiplication of the residue module**, on even parts:
the residue module is a copy of ℂ in even degree, and this is the
multiplication of ℂ. -/
noncomputable def pointMulLin :
    (pointMod P : S.Mod.{u, u, u, u}).even →ₗ[ℂ]
      (pointMod P : S.Mod.{u, u, u, u}).even →ₗ[ℂ]
        (pointMod P : S.Mod.{u, u, u, u}).even :=
  LinearMap.mk₂ ℂ (fun a b => ULift.up (a.down * b.down))
    (fun a b c => ULift.ext _ _ (by
      show (a.down + b.down) * c.down = _
      exact add_mul _ _ _))
    (fun r a b => ULift.ext _ _ (by
      show (r * a.down) * b.down = r * (a.down * b.down)
      exact mul_assoc _ _ _))
    (fun a b c => ULift.ext _ _ (by
      show a.down * (b.down + c.down) = _
      exact mul_add _ _ _))
    (fun r a b => ULift.ext _ _ (by
      show a.down * (r * b.down) = r * (a.down * b.down)
      ring))

/-- The multiplication of the residue module, evaluated. -/
@[simp] theorem pointMulLin_apply
    (a b : (pointMod P : S.Mod.{u, u, u, u}).even) :
    pointMulLin P a b = ULift.up (a.down * b.down) := rfl

/-- **The data of the multiplication** of the residue module as a
morphism out of the tensor square: the even-even block is the
multiplication of ℂ and the three remaining blocks vanish, the odd
part of the residue module being zero. -/
noncomputable def pointMulData :
    TensorData (pointMod P : S.Mod.{u, u, u, u}) (pointMod P)
      (pointMod P) where
  fee := pointMulLin P
  foo := 0
  feo := 0
  foe := 0
  hee b m n := ULift.ext _ _ (by
    show P.chi b * m.down * n.down = m.down * (P.chi b * n.down)
    ring)
  hoo _ _ _ := rfl
  hoeo c m n := by
    rw [pointMod_actOO]
    show (0 : (pointMod P).even) = pointMulLin P m 0
    rw [map_zero]
  hooe c m n := by
    rw [pointMod_actOO]
    show pointMulLin P 0 n = -(0 : (pointMod P).even)
    rw [map_zero, LinearMap.zero_apply, neg_zero]
  heeo _ _ _ := Subsingleton.elim _ _
  heoe _ _ _ := Subsingleton.elim _ _
  hoee _ _ _ := Subsingleton.elim _ _
  hooo _ _ _ := Subsingleton.elim _ _
  aee a m n := ULift.ext _ _ (by
    show P.chi a * m.down * n.down = P.chi a * (m.down * n.down)
    ring)
  aoo a m n := by
    show (0 : (pointMod P).even) = (pointMod P).actEE a 0
    rw [map_zero]
  aeo _ _ _ := Subsingleton.elim _ _
  aoe _ _ _ := Subsingleton.elim _ _
  cee _ _ _ := Subsingleton.elim _ _
  coo _ _ _ := Subsingleton.elim _ _
  ceo c m n := by
    rw [pointMod_actOO]
    rfl
  coe c m n := by
    rw [pointMod_actOO, pointMod_actOO]
    show pointMulLin P 0 n = 0
    rw [map_zero, LinearMap.zero_apply]

/-- **The multiplication of the residue module**, as a morphism of
super modules out of its tensor square. -/
noncomputable def pointMulHom :
    ((pointMod P : S.Mod.{u, u, u, u}).tensor (pointMod P)) ⟶
      pointMod P :=
  mkHom (pointMulData P)

/-- The multiplication on even-even products. -/
@[simp] theorem pointMulHom_evenMap_tmulEE
    (a b : (pointMod P : S.Mod.{u, u, u, u}).even) :
    (pointMulHom P).evenMap (tmulEE (pointMod P) (pointMod P) a b) =
      ULift.up (a.down * b.down) :=
  mkHom_evenMap_tmulEE (pointMulData P) a b

/-- **The unit of the residue module**: the point itself, read as a
morphism from the algebra. -/
noncomputable def pointUnitHom :
    (S.unitMod : S.Mod.{u, u, u, u}) ⟶ pointMod P where
  evenMap := (ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm.toLinearMap ∘ₗ
    (P.chi.toLinearMap : S.even →ₗ[ℂ] ℂ)
  oddMap := 0
  map_actEE x m := ULift.ext _ _ (by
    show P.chi (S.mulEE x m) = P.chi x * P.chi m
    exact map_mul P.chi x m)
  map_actEO _ _ := Subsingleton.elim _ _
  map_actOE _ _ := Subsingleton.elim _ _
  map_actOO u m := ULift.ext _ _ (by
    show P.chi (S.mulOO u m) = (0 : ULift.{u} ℂ).down
    rw [P.vanishing]
    rfl)

/-- The unit of the residue module, evaluated. -/
@[simp] theorem pointUnitHom_evenMap (x : S.even) :
    (pointUnitHom P).evenMap x = ULift.up (P.chi x) := rfl

/-- **The base change of the unit module is finite dimensional** in
even degree: the left unitor identifies it with the residue
module. -/
instance finiteDimensional_unitMod_tensor_point_even :
    FiniteDimensional ℂ
      ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod P)).even :=
  (evenEquiv (unitTensorPoint P)).symm.finiteDimensional

/-- **The base change of the unit module is finite dimensional** in
odd degree. -/
instance finiteDimensional_unitMod_tensor_point_odd :
    FiniteDimensional ℂ
      ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod P)).odd :=
  (oddEquiv (unitTensorPoint P)).symm.finiteDimensional

end ResidueAlgebra

/-! ## The comparison over the algebra

Base change is the functor `M ↦ M ⊗ k` for `k` the residue module
of the point.  The residue module is a commutative algebra, so the
usual middle-four interchange followed by its multiplication is a
comparison morphism
`(M ⊗ k) ⊗ (N ⊗ k) ⟶ (M ⊗ N) ⊗ k`. -/

section BaseChangeComparison

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)

/-- **The comparison morphism of base change**, over the algebra:
interchange the middle two factors and multiply the two copies of
the residue module. -/
noncomputable def pointBaseMu (M N : S.Mod.{u, u, u, u}) :
    ((M.tensor (pointMod P)).tensor (N.tensor (pointMod P)) :
        S.Mod.{u, u, u, u}) ⟶ (M.tensor N).tensor (pointMod P) :=
  tensorμ M (pointMod P) N (pointMod P) ≫
    ((M.tensor N : S.Mod.{u, u, u, u}) ◁ pointMulHom P)

/-- **The unit of base change**, over the algebra: the point read
as a morphism from the unit, followed by the inverse left unitor. -/
noncomputable def pointBaseEps :
    (S.unitMod : S.Mod.{u, u, u, u}) ⟶
      (S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod P) :=
  (ρ_ (S.unitMod : S.Mod.{u, u, u, u})).inv ≫
    ((S.unitMod : S.Mod.{u, u, u, u}) ◁ pointUnitHom P)

/-- **The comparison over the algebra is natural** in both
variables: this is naturality of the middle-four interchange. -/
theorem pointBaseMu_naturality {M M' N N' : S.Mod.{u, u, u, u}}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((f ⊗ₘ 𝟙 (pointMod P)) ⊗ₘ (g ⊗ₘ 𝟙 (pointMod P))) ≫
        pointBaseMu P M' N' =
      pointBaseMu P M N ≫ ((f ⊗ₘ g) ⊗ₘ 𝟙 (pointMod P)) := by
  simp only [pointBaseMu, Category.assoc]
  rw [← Category.assoc, tensorμ_natural, Category.assoc]
  congr 1
  simp only [← id_tensorHom, tensorHom_comp_tensorHom,
    Category.comp_id, Category.id_comp, id_tensorHom_id]
  exact congrArg (fun h => h ⊗ₘ pointMulHom P)
    (Category.comp_id (f ⊗ₘ g))

end BaseChangeComparison

/-! ## The comparison over the algebra, on generators -/

section BaseMuFormulas

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)
  (M N : S.Mod.{u, u, u, u})

/-- The monoidal associator of the super modules is the explicit
associator. -/
theorem modAssociator_hom (X Y Z : S.Mod.{u, u, u, u}) :
    (α_ X Y Z).hom = assocHom X Y Z := rfl

/-- The inverse associator of the super modules is explicit. -/
theorem modAssociator_inv (X Y Z : S.Mod.{u, u, u, u}) :
    (α_ X Y Z).inv = assocInv X Y Z := rfl

/-- The braiding of the super modules is the Koszul swap. -/
theorem modBraiding_hom (X Y : S.Mod.{u, u, u, u}) :
    (β_ X Y).hom = braidingHom X Y := rfl

/-- Left whiskering of super modules is a tensor product of
morphisms. -/
theorem modWhiskerLeft (X : S.Mod.{u, u, u, u})
    {Y Z : S.Mod.{u, u, u, u}} (f : Y ⟶ Z) :
    X ◁ f = SuperCommAlgebra.Mod.tensorHom (𝟙 X) f := rfl

/-- Right whiskering of super modules is a tensor product of
morphisms. -/
theorem modWhiskerRight {Y Z : S.Mod.{u, u, u, u}} (f : Y ⟶ Z)
    (X : S.Mod.{u, u, u, u}) :
    f ▷ X = SuperCommAlgebra.Mod.tensorHom f (𝟙 X) := rfl

/-- The monoidal tensor product of super modules is the balanced
tensor product. -/
theorem modTensorObj (X Y : S.Mod.{u, u, u, u}) :
    X ⊗ Y = X.tensor Y := rfl

/-- The left unitor of the super modules is explicit. -/
theorem modLeftUnitor_hom (X : S.Mod.{u, u, u, u}) :
    (λ_ X).hom = leftUnitorHom X := rfl

/-- The right unitor of the super modules is explicit. -/
theorem modRightUnitor_hom (X : S.Mod.{u, u, u, u}) :
    (ρ_ X).hom = rightUnitorHom X := rfl

/-- The monoidal unit of the super modules is the algebra. -/
theorem modTensorUnit : (𝟙_ (S.Mod.{u, u, u, u})) = S.unitMod := rfl

/-- **The comparison over the algebra on even-even generators.** -/
theorem pointBaseMu_evenMap_ee (m : M.even)
    (a : (pointMod P : S.Mod.{u, u, u, u}).even) (n : N.even)
    (b : (pointMod P : S.Mod.{u, u, u, u}).even) :
    (pointBaseMu P M N).evenMap
        (tmulEE (M.tensor (pointMod P)) (N.tensor (pointMod P))
          (tmulEE M (pointMod P) m a)
          (tmulEE N (pointMod P) n b)) =
      tmulEE (M.tensor N) (pointMod P) (tmulEE M N m n)
        (ULift.up (a.down * b.down)) := by
  simp [pointBaseMu, tensorμ, modTensorObj, modAssociator_hom,
    modAssociator_inv, modBraiding_hom, modWhiskerLeft,
    modWhiskerRight]

/-- **The comparison over the algebra on odd-odd generators.** -/
theorem pointBaseMu_evenMap_oo (m : M.odd)
    (a : (pointMod P : S.Mod.{u, u, u, u}).even) (n : N.odd)
    (b : (pointMod P : S.Mod.{u, u, u, u}).even) :
    (pointBaseMu P M N).evenMap
        (tmulOO (M.tensor (pointMod P)) (N.tensor (pointMod P))
          (tmulOE M (pointMod P) m a)
          (tmulOE N (pointMod P) n b)) =
      tmulEE (M.tensor N) (pointMod P) (tmulOO M N m n)
        (ULift.up (a.down * b.down)) := by
  simp [pointBaseMu, tensorμ, modTensorObj, modAssociator_hom,
    modAssociator_inv, modBraiding_hom, modWhiskerLeft,
    modWhiskerRight]

/-- **The comparison over the algebra on even-odd generators.** -/
theorem pointBaseMu_oddMap_eo (m : M.even)
    (a : (pointMod P : S.Mod.{u, u, u, u}).even) (n : N.odd)
    (b : (pointMod P : S.Mod.{u, u, u, u}).even) :
    (pointBaseMu P M N).oddMap
        (tmulEO (M.tensor (pointMod P)) (N.tensor (pointMod P))
          (tmulEE M (pointMod P) m a)
          (tmulOE N (pointMod P) n b)) =
      tmulOE (M.tensor N) (pointMod P) (tmulEO M N m n)
        (ULift.up (a.down * b.down)) := by
  simp [pointBaseMu, tensorμ, modTensorObj, modAssociator_hom,
    modAssociator_inv, modBraiding_hom, modWhiskerLeft,
    modWhiskerRight]

/-- **The comparison over the algebra on odd-even generators.** -/
theorem pointBaseMu_oddMap_oe (m : M.odd)
    (a : (pointMod P : S.Mod.{u, u, u, u}).even) (n : N.even)
    (b : (pointMod P : S.Mod.{u, u, u, u}).even) :
    (pointBaseMu P M N).oddMap
        (tmulOE (M.tensor (pointMod P)) (N.tensor (pointMod P))
          (tmulOE M (pointMod P) m a)
          (tmulEE N (pointMod P) n b)) =
      tmulOE (M.tensor N) (pointMod P) (tmulOE M N m n)
        (ULift.up (a.down * b.down)) := by
  simp [pointBaseMu, tensorμ, modTensorObj, modAssociator_hom,
    modAssociator_inv, modBraiding_hom, modWhiskerLeft,
    modWhiskerRight]

end BaseMuFormulas

/-! ## The residue module is a commutative monoid object

The three monoid laws and commutativity, in the form the lax
structure of base change consumes.  Every law is an identity of
complex numbers in the even-even-even block, and every other block
lands in the odd part of the residue module, which vanishes. -/

section MonoidLaws

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)

/-- Associativity of the multiplication of the residue module, on
the one family of generators that does not vanish. -/
private theorem point_triple_ee
    (a b c : (pointMod P : S.Mod.{u, u, u, u}).even) :
    ((pointMulHom P ▷ pointMod P) ≫ pointMulHom P).evenMap
        (tmulEE ((pointMod P).tensor (pointMod P)) (pointMod P)
          (tmulEE (pointMod P) (pointMod P) a b) c) =
      ((α_ (pointMod P) (pointMod P)
              (pointMod P : S.Mod.{u, u, u, u})).hom ≫
          ((pointMod P : S.Mod.{u, u, u, u}) ◁ pointMulHom P) ≫
            pointMulHom P).evenMap
        (tmulEE ((pointMod P).tensor (pointMod P)) (pointMod P)
          (tmulEE (pointMod P) (pointMod P) a b) c) := by
  have e1 : (SuperCommAlgebra.Mod.tensorHom (pointMulHom P)
        (𝟙 (pointMod P))).evenMap
      (tmulEE ((pointMod P).tensor (pointMod P)) (pointMod P)
        (tmulEE (pointMod P) (pointMod P) a b) c) =
      tmulEE (pointMod P) (pointMod P)
        (ULift.up (a.down * b.down)) c := by
    rw [tensorHom_evenMap_tmulEE, pointMulHom_evenMap_tmulEE]
    rfl
  have e2 : (assocHom (pointMod P) (pointMod P)
        (pointMod P : S.Mod.{u, u, u, u})).evenMap
      (tmulEE ((pointMod P).tensor (pointMod P)) (pointMod P)
        (tmulEE (pointMod P) (pointMod P) a b) c) =
      tmulEE (pointMod P) ((pointMod P).tensor (pointMod P)) a
        (tmulEE (pointMod P) (pointMod P) b c) := by
    rw [assocHom_evenMap_tmulEE, assocFee_tmulEE]
  have e3 : (SuperCommAlgebra.Mod.tensorHom (𝟙 (pointMod P))
        (pointMulHom P)).evenMap
      (tmulEE (pointMod P) ((pointMod P).tensor (pointMod P)) a
        (tmulEE (pointMod P) (pointMod P) b c)) =
      tmulEE (pointMod P) (pointMod P) a
        (ULift.up (b.down * c.down)) := by
    rw [tensorHom_evenMap_tmulEE, pointMulHom_evenMap_tmulEE]
    rfl
  show (pointMulHom P).evenMap
      ((SuperCommAlgebra.Mod.tensorHom (pointMulHom P)
        (𝟙 (pointMod P))).evenMap
        (tmulEE ((pointMod P).tensor (pointMod P)) (pointMod P)
          (tmulEE (pointMod P) (pointMod P) a b) c)) =
    (pointMulHom P).evenMap
      ((SuperCommAlgebra.Mod.tensorHom (𝟙 (pointMod P))
        (pointMulHom P)).evenMap
        ((assocHom (pointMod P) (pointMod P)
          (pointMod P : S.Mod.{u, u, u, u})).evenMap
          (tmulEE ((pointMod P).tensor (pointMod P)) (pointMod P)
            (tmulEE (pointMod P) (pointMod P) a b) c)))
  erw [e1, e2, e3, pointMulHom_evenMap_tmulEE,
    pointMulHom_evenMap_tmulEE]
  refine ULift.ext _ _ ?_
  show a.down * b.down * c.down = a.down * (b.down * c.down)
  exact mul_assoc _ _ _

/-- **The multiplication of the residue module is associative.** -/
theorem pointMulHom_assoc :
    ((pointMulHom P ▷ pointMod P) ≫ pointMulHom P :
        ((pointMod P).tensor (pointMod P)).tensor (pointMod P) ⟶
          pointMod P) =
      (α_ (pointMod P) (pointMod P)
          (pointMod P : S.Mod.{u, u, u, u})).hom ≫
        ((pointMod P : S.Mod.{u, u, u, u}) ◁ pointMulHom P) ≫
          pointMulHom P := by
  refine hom_ext₃ (fun a b c => point_triple_ee P a b c)
    (fun a b c => ?_) (fun a b c => ?_) (fun a b c => ?_)
    (fun a b c => Subsingleton.elim _ _)
    (fun a b c => Subsingleton.elim _ _)
    (fun a b c => Subsingleton.elim _ _)
    (fun a b c => Subsingleton.elim _ _)
  · have h : tmulEE ((pointMod P).tensor (pointMod P))
        (pointMod P : S.Mod.{u, u, u, u})
        (tmulOO (pointMod P) (pointMod P) a b) c = 0 := by
      rw [pointMod_odd_eq_zero P a, map_zero, LinearMap.zero_apply,
        map_zero, LinearMap.zero_apply]
    rw [h, map_zero, map_zero]
  · have h : tmulOO ((pointMod P).tensor (pointMod P))
        (pointMod P : S.Mod.{u, u, u, u})
        (tmulEO (pointMod P) (pointMod P) a b) c = 0 := by
      rw [pointMod_odd_eq_zero P c, map_zero]
    rw [h, map_zero, map_zero]
  · have h : tmulOO ((pointMod P).tensor (pointMod P))
        (pointMod P : S.Mod.{u, u, u, u})
        (tmulOE (pointMod P) (pointMod P) a b) c = 0 := by
      rw [pointMod_odd_eq_zero P c, map_zero]
    rw [h, map_zero, map_zero]

/-- **The point is a left unit for the multiplication of the
residue module.** -/
theorem pointMulHom_left_unit :
    ((pointUnitHom P ▷ pointMod P) ≫ pointMulHom P :
        (S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod P) ⟶
          pointMod P) =
      (λ_ (pointMod P : S.Mod.{u, u, u, u})).hom := by
  refine hom_ext (fun x a => ?_) (fun u v => ?_)
    (fun x v => Subsingleton.elim _ _)
    (fun u a => Subsingleton.elim _ _)
  · conv_lhs => erw [modWhiskerRight, comp_evenMap,
      LinearMap.comp_apply, tensorHom_evenMap_tmulEE,
      pointUnitHom_evenMap, id_evenMap, LinearMap.id_coe, id_eq,
      pointMulHom_evenMap_tmulEE]
    conv_rhs => rw [modLeftUnitor_hom,
      leftUnitorHom_evenMap_tmulEE, pointMod_actEE]
  · rw [pointMod_odd_eq_zero P v, map_zero, map_zero, map_zero]

/-- **The point is a right unit for the multiplication of the
residue module.** -/
theorem pointMulHom_right_unit :
    (((pointMod P : S.Mod.{u, u, u, u}) ◁ pointUnitHom P) ≫
        pointMulHom P :
        (pointMod P : S.Mod.{u, u, u, u}).tensor S.unitMod ⟶
          pointMod P) =
      (ρ_ (pointMod P : S.Mod.{u, u, u, u})).hom := by
  refine hom_ext (fun a x => ?_) (fun v u => ?_)
    (fun a u => Subsingleton.elim _ _)
    (fun v x => Subsingleton.elim _ _)
  · conv_lhs => erw [modWhiskerLeft, comp_evenMap,
      LinearMap.comp_apply, tensorHom_evenMap_tmulEE,
      pointUnitHom_evenMap, id_evenMap, LinearMap.id_coe, id_eq,
      pointMulHom_evenMap_tmulEE]
    conv_rhs => rw [modRightUnitor_hom,
      rightUnitorHom_evenMap_tmulEE, pointMod_actEE]
    exact ULift.ext _ _ (mul_comm _ _)
  · rw [pointMod_odd_eq_zero P v, map_zero, LinearMap.zero_apply,
      map_zero, map_zero]

/-- **The multiplication of the residue module is commutative.** -/
theorem pointMulHom_comm :
    ((β_ (pointMod P) (pointMod P : S.Mod.{u, u, u, u})).hom ≫
        pointMulHom P) = pointMulHom P := by
  refine hom_ext (fun a b => ?_) (fun a b => ?_)
    (fun a b => Subsingleton.elim _ _)
    (fun a b => Subsingleton.elim _ _)
  · conv_lhs => rw [modBraiding_hom, comp_evenMap,
      LinearMap.comp_apply, braidingHom_evenMap_tmulEE,
      pointMulHom_evenMap_tmulEE]
    conv_rhs => rw [pointMulHom_evenMap_tmulEE]
    exact ULift.ext _ _ (mul_comm _ _)
  · rw [pointMod_odd_eq_zero P a, map_zero, LinearMap.zero_apply,
      map_zero, map_zero]

end MonoidLaws

/-! ## Base change over the algebra is lax monoidal -/

section AlgebraCoherence

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)

/-- **Associativity of the comparison over the algebra.** -/
theorem pointBaseMu_associativity (M N Q : S.Mod.{u, u, u, u}) :
    (pointBaseMu P M N ▷ (Q.tensor (pointMod P))) ≫
        pointBaseMu P (M.tensor N) Q ≫
        ((α_ M N Q).hom ▷ pointMod P) =
      (α_ (M.tensor (pointMod P)) (N.tensor (pointMod P))
          (Q.tensor (pointMod P))).hom ≫
        ((M.tensor (pointMod P) : S.Mod.{u, u, u, u}) ◁
          pointBaseMu P N Q) ≫ pointBaseMu P M (N.tensor Q) := by
  simp only [pointBaseMu, ← modTensorObj, comp_whiskerRight,
    whiskerLeft_comp, Category.assoc]
  rw [← id_tensorHom (M ⊗ N) (pointMulHom P),
    tensorμ_natural_left_assoc, id_whiskerRight, id_tensorHom,
    ← whiskerLeft_comp_assoc, pointMulHom_assoc,
    whiskerLeft_comp_assoc, whisker_exchange,
    ← tensorHom_def'_assoc]
  show tensorμ M (pointMod P) N (pointMod P) ▷ (Q ⊗ pointMod P) ≫
      tensorμ (M ⊗ N) (pointMod P ⊗ pointMod P) Q (pointMod P) ≫
        ((α_ M N Q).hom ⊗ₘ
          (α_ (pointMod P) (pointMod P) (pointMod P)).hom) ≫
        ((M ⊗ N ⊗ Q) ◁ ((pointMod P ◁ pointMulHom P) ≫
          pointMulHom P)) = _
  rw [tensor_associativity_assoc,
    ← id_tensorHom (N ⊗ Q) (pointMulHom P),
    tensorμ_natural_right_assoc, whiskerLeft_id, id_tensorHom,
    ← whiskerLeft_comp]
  rfl

/-- **Left unitality of the comparison over the algebra.** -/
theorem pointBaseMu_left_unitality (M : S.Mod.{u, u, u, u}) :
    (λ_ (M.tensor (pointMod P))).hom =
      (pointBaseEps P ▷ (M.tensor (pointMod P))) ≫
        pointBaseMu P S.unitMod M ≫ ((λ_ M).hom ▷ pointMod P) := by
  simp only [pointBaseMu, pointBaseEps, ← modTensorObj,
    ← modTensorUnit, comp_whiskerRight, Category.assoc]
  rw [← unitors_inv_equal, ← id_tensorHom (𝟙_ (S.Mod.{u, u, u, u}))
      (pointUnitHom P), tensorμ_natural_left_assoc, id_whiskerRight,
    id_tensorHom, ← whiskerLeft_comp_assoc, pointMulHom_left_unit,
    ← tensorHom_def']
  exact tensor_left_unitality M (pointMod P)

/-- **Right unitality of the comparison over the algebra.** -/
theorem pointBaseMu_right_unitality (M : S.Mod.{u, u, u, u}) :
    (ρ_ (M.tensor (pointMod P))).hom =
      ((M.tensor (pointMod P) : S.Mod.{u, u, u, u}) ◁
          pointBaseEps P) ≫
        pointBaseMu P M S.unitMod ≫ ((ρ_ M).hom ▷ pointMod P) := by
  simp only [pointBaseMu, pointBaseEps, ← modTensorObj,
    ← modTensorUnit, whiskerLeft_comp, Category.assoc]
  rw [← unitors_inv_equal, ← id_tensorHom (𝟙_ (S.Mod.{u, u, u, u}))
      (pointUnitHom P), tensorμ_natural_right_assoc, whiskerLeft_id,
    id_tensorHom, ← whiskerLeft_comp_assoc, pointMulHom_right_unit,
    ← tensorHom_def']
  exact tensor_right_unitality M (pointMod P)

/-- **The comparison over the algebra intertwines the braidings.**
The interchange does so by `RS.tensorμ_braiding`, and the residue
factor by commutativity of its multiplication. -/
theorem pointBaseMu_braiding (M N : S.Mod.{u, u, u, u}) :
    pointBaseMu P M N ≫ ((β_ M N).hom ▷ pointMod P) =
      (β_ (M ⊗ pointMod P) (N ⊗ pointMod P)).hom ≫
        pointBaseMu P N M := by
  simp only [pointBaseMu, ← modTensorObj, Category.assoc]
  rw [tensorμ_braiding_assoc]
  congr 1
  rw [← MonoidalCategory.id_tensorHom (M ⊗ N) (pointMulHom P),
    ← MonoidalCategory.tensorHom_id (β_ M N).hom (pointMod P),
    ← MonoidalCategory.id_tensorHom (N ⊗ M) (pointMulHom P),
    MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id,
    pointMulHom_comm, Category.id_comp, Category.comp_id]

end AlgebraCoherence

end RS
