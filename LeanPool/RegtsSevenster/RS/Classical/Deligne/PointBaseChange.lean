/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairAdd
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModShiftUnit
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperPointMod

/-!
# Base change of a free super module to a complex point

Tensoring a super module with the residue module of a complex point
(`RS.SuperCommAlgebra.pointMod`) is base change along that point.
This file computes the base change of a free super module of rank
`(p | q)` and records that the answer is a finite-dimensional super
vector space of the same rank.

The computation is pure additivity.  Tensoring on the right by a
fixed module is an additive functor, so it carries a finite
biproduct to a finite biproduct; the two summands of a free module
are the unit and its parity shift, and tensoring either of them
with the residue module is already known — the unit case is the
left unitor and the shifted case is
`RS.SuperCommAlgebra.Mod.shiftUnitTensor`.  What is left is a
biproduct of `p` copies of the residue module and `q` copies of its
parity shift, whose even part has dimension `p` and whose odd part
has dimension `q`.

Finite-dimensionality is read off through the two component
functors to complex vector spaces.  Taking the even part, or the
odd part, of a super module is an additive functor to `ModuleCat ℂ`,
so it turns the abstract biproduct of super modules into the
concrete product of the component spaces, and a finite product of
finite-dimensional spaces is finite-dimensional.

## Contents

* `RS.SuperCommAlgebra.Mod.evenModFunctor`, `oddModFunctor`: the two
  component functors, and their additivity.
* `RS.SuperCommAlgebra.Mod.evenBiproductEquiv`, `oddBiproductEquiv`:
  the component of a finite biproduct is the product of the
  components.
* `RS.SuperCommAlgebra.Mod.tensorRightFunctor`: tensoring on the
  right by a fixed module, as an additive functor.
* `RS.unitTensorPoint`, `RS.shiftTensorPoint`: base change of the
  unit and of its parity shift.
* `RS.freeTensorPoint`: base change of a free module of rank
  `(p | q)`.
* `RS.finiteDimensional_even_of_free`,
  `RS.finiteDimensional_odd_of_free`: finite-dimensionality of the
  base change of a free module.
* `RS.finrank_even_of_free`, `RS.finrank_odd_of_free`: the two
  dimensions are `p` and `q`.
* `RS.toSuperVect`: the base change packaged as a super vector
  space, with `RS.toSuperVectEvenEquiv`, `toSuperVectOddEquiv` and
  the two explicit coordinate equivalences
  `RS.freeEvenEquivFin`, `freeOddEquivFin`.
-/

namespace RS

open CategoryTheory Limits

universe u

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u}}

/-! ## The two component functors -/

/-- **The even component as a functor** to complex vector spaces. -/
noncomputable def evenModFunctor (S : SuperCommAlgebra.{u, u}) :
    S.Mod.{u, u, u, u} ⥤ ModuleCat.{u} ℂ where
  obj M := ModuleCat.of ℂ M.even
  map f := ModuleCat.ofHom f.evenMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- **The odd component as a functor** to complex vector spaces. -/
noncomputable def oddModFunctor (S : SuperCommAlgebra.{u, u}) :
    S.Mod.{u, u, u, u} ⥤ ModuleCat.{u} ℂ where
  obj M := ModuleCat.of ℂ M.odd
  map f := ModuleCat.ofHom f.oddMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The even component functor is additive. -/
instance evenModFunctor_additive (S : SuperCommAlgebra.{u, u}) :
    (evenModFunctor S).Additive where
  map_add := rfl

/-- The odd component functor is additive. -/
instance oddModFunctor_additive (S : SuperCommAlgebra.{u, u}) :
    (oddModFunctor S).Additive where
  map_add := rfl

/-- An isomorphism of super modules is a linear equivalence on even
components. -/
noncomputable def evenEquiv {M N : S.Mod.{u, u, u, u}} (e : M ≅ N) :
    M.even ≃ₗ[ℂ] N.even :=
  ((evenModFunctor S).mapIso e).toLinearEquiv

/-- An isomorphism of super modules is a linear equivalence on odd
components. -/
noncomputable def oddEquiv {M N : S.Mod.{u, u, u, u}} (e : M ≅ N) :
    M.odd ≃ₗ[ℂ] N.odd :=
  ((oddModFunctor S).mapIso e).toLinearEquiv

/-! ## Components of a finite biproduct -/

/-- **The even component of a finite biproduct** is the product of
the even components. -/
noncomputable def evenBiproductEquiv {J : Type} [Fintype J]
    (g : J → S.Mod.{u, u, u, u}) :
    (⨁ g).even ≃ₗ[ℂ] ∀ j, (g j).even :=
  (((evenModFunctor S).mapBiproduct g).trans
    (ModuleCat.biproductIsoPi _)).toLinearEquiv

/-- **The odd component of a finite biproduct** is the product of
the odd components. -/
noncomputable def oddBiproductEquiv {J : Type} [Fintype J]
    (g : J → S.Mod.{u, u, u, u}) :
    (⨁ g).odd ≃ₗ[ℂ] ∀ j, (g j).odd :=
  (((oddModFunctor S).mapBiproduct g).trans
    (ModuleCat.biproductIsoPi _)).toLinearEquiv

/-! ## Tensoring on the right -/

/-- **Tensoring on the right by a fixed module**, as a functor. -/
noncomputable def tensorRightFunctor (N : S.Mod.{u, u, u, u}) :
    S.Mod.{u, u, u, u} ⥤ S.Mod.{u, u, u, u} where
  obj M := M.tensor N
  map f := tensorHom f (𝟙 N)
  map_id M := tensorHom_id M N
  map_comp f g := by
    rw [← tensorHom_comp f g (𝟙 N) (𝟙 N), Category.comp_id]

@[simp] theorem tensorRightFunctor_obj (N M : S.Mod.{u, u, u, u}) :
    (tensorRightFunctor N).obj M = M.tensor N := rfl

/-- Tensoring on the right by a fixed module is additive: this is
additivity of the tensor product in the left variable. -/
instance tensorRightFunctor_additive (N : S.Mod.{u, u, u, u}) :
    (tensorRightFunctor N).Additive where
  map_add {_ _ f g} := tensorHom_add_left f g (𝟙 N)

end SuperCommAlgebra.Mod

open SuperCommAlgebra SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u}}

/-! ## Base change of the two free generators -/

/-- **Base change of the unit module**: tensoring the unit with the
residue module of a point returns the residue module.  This is the
left unitor. -/
noncomputable def unitTensorPoint (P : SuperPoint S) :
    (S.unitMod.tensor (pointMod P) : S.Mod.{u, u, u, u}) ≅
      pointMod P :=
  leftUnitor (pointMod P)

/-- **Base change of the shifted unit module**: tensoring the parity
shift of the unit with the residue module of a point returns the
parity shift of the residue module. -/
noncomputable def shiftTensorPoint (P : SuperPoint S) :
    ((shift S.unitMod).tensor (pointMod P) : S.Mod.{u, u, u, u}) ≅
      shift (pointMod P) :=
  shiftUnitTensor (pointMod P)

/-! ## Base change of a free module -/

/-- **Base change of a free super module of rank `(p | q)`**: the
result is the biproduct of `p` copies of the residue module and `q`
copies of its parity shift.  Tensoring on the right is additive, so
it carries the defining biproduct across, and the two summands are
handled by `RS.unitTensorPoint` and `RS.shiftTensorPoint`. -/
noncomputable def freeTensorPoint (P : SuperPoint S) (p q : ℕ) :
    ((⨁ fun i : Fin p ⊕ Fin q =>
        Sum.elim (fun _ => S.unitMod)
          (fun _ => shift S.unitMod) i).tensor
        (pointMod P) : S.Mod.{u, u, u, u}) ≅
      ⨁ fun i : Fin p ⊕ Fin q =>
        Sum.elim (fun _ => pointMod P)
          (fun _ => shift (pointMod P)) i :=
  (tensorRightFunctor (pointMod P)).mapBiproduct
      (fun i : Fin p ⊕ Fin q =>
        Sum.elim (fun _ => S.unitMod)
          (fun _ => shift S.unitMod) i) ≪≫
    biproduct.mapIso fun i =>
      match i with
      | Sum.inl _ => unitTensorPoint P
      | Sum.inr _ => shiftTensorPoint P

/-! ## The residue module is one-dimensional in even degree -/

/-- The even part of the residue module of a point is
finite-dimensional: it is a copy of the complex numbers. -/
instance finiteDimensional_pointMod_even (P : SuperPoint S) :
    FiniteDimensional ℂ (pointMod P : S.Mod.{u, u, u, u}).even :=
  (inferInstance : FiniteDimensional ℂ (ULift.{u} ℂ))

/-- The odd part of the residue module of a point is
finite-dimensional: it is zero. -/
instance finiteDimensional_pointMod_odd (P : SuperPoint S) :
    FiniteDimensional ℂ (pointMod P : S.Mod.{u, u, u, u}).odd :=
  (inferInstance : FiniteDimensional ℂ (ULift.{u} PUnit.{1}))

/-- The even part of the residue module of a point is
one-dimensional. -/
theorem finrank_pointMod_even (P : SuperPoint S) :
    Module.finrank ℂ (pointMod P : S.Mod.{u, u, u, u}).even = 1 := by
  change Module.finrank ℂ (ULift.{u} ℂ) = 1
  rw [LinearEquiv.finrank_eq (ULift.moduleEquiv (R := ℂ) (M := ℂ)),
    Module.finrank_self]

/-- The odd part of the residue module of a point is zero. -/
theorem finrank_pointMod_odd (P : SuperPoint S) :
    Module.finrank ℂ (pointMod P : S.Mod.{u, u, u, u}).odd = 0 :=
  Module.finrank_eq_zero_of_subsingleton ℂ (ULift.{u} PUnit.{1})

/-! ## The biproduct of residue modules -/

/-- The family of summands of the base change of a free module of
rank `(p | q)`: `p` copies of the residue module of the point and
`q` copies of its parity shift. -/
noncomputable def residueShape (P : SuperPoint S) (p q : ℕ) :
    Fin p ⊕ Fin q → S.Mod.{u, u, u, u} := fun i =>
  Sum.elim (fun _ => pointMod P) (fun _ => shift (pointMod P)) i

/-- Every summand has finite-dimensional even part. -/
instance finiteDimensional_residueShape_even (P : SuperPoint S)
    (p q : ℕ) (i : Fin p ⊕ Fin q) :
    FiniteDimensional ℂ (residueShape P p q i).even := by
  cases i with
  | inl _ => exact finiteDimensional_pointMod_even P
  | inr _ => exact finiteDimensional_pointMod_odd P

/-- Every summand has finite-dimensional odd part. -/
instance finiteDimensional_residueShape_odd (P : SuperPoint S)
    (p q : ℕ) (i : Fin p ⊕ Fin q) :
    FiniteDimensional ℂ (residueShape P p q i).odd := by
  cases i with
  | inl _ => exact finiteDimensional_pointMod_odd P
  | inr _ => exact finiteDimensional_pointMod_even P

/-- The even part of the biproduct of residue modules is
finite-dimensional. -/
instance finiteDimensional_biproduct_even (P : SuperPoint S)
    (p q : ℕ) :
    FiniteDimensional ℂ (⨁ residueShape P p q).even :=
  (evenBiproductEquiv (residueShape P p q)).symm.finiteDimensional

/-- The odd part of the biproduct of residue modules is
finite-dimensional. -/
instance finiteDimensional_biproduct_odd (P : SuperPoint S)
    (p q : ℕ) :
    FiniteDimensional ℂ (⨁ residueShape P p q).odd :=
  (oddBiproductEquiv (residueShape P p q)).symm.finiteDimensional

/-- The even part of the biproduct of residue modules has
dimension `p`. -/
theorem finrank_biproduct_even (P : SuperPoint S) (p q : ℕ) :
    Module.finrank ℂ (⨁ residueShape P p q).even = p := by
  rw [LinearEquiv.finrank_eq (evenBiproductEquiv (residueShape P p q)),
    Module.finrank_pi_fintype ℂ, Fintype.sum_sum_type]
  have h₁ : ∀ a : Fin p,
      Module.finrank ℂ (residueShape P p q (Sum.inl a)).even = 1 :=
    fun _ => finrank_pointMod_even P
  have h₂ : ∀ b : Fin q,
      Module.finrank ℂ (residueShape P p q (Sum.inr b)).even = 0 :=
    fun _ => finrank_pointMod_odd P
  rw [Finset.sum_congr rfl fun a _ => h₁ a,
    Finset.sum_congr rfl fun b _ => h₂ b]
  simp

/-- The odd part of the biproduct of residue modules has
dimension `q`. -/
theorem finrank_biproduct_odd (P : SuperPoint S) (p q : ℕ) :
    Module.finrank ℂ (⨁ residueShape P p q).odd = q := by
  rw [LinearEquiv.finrank_eq (oddBiproductEquiv (residueShape P p q)),
    Module.finrank_pi_fintype ℂ, Fintype.sum_sum_type]
  have h₁ : ∀ a : Fin p,
      Module.finrank ℂ (residueShape P p q (Sum.inl a)).odd = 0 :=
    fun _ => finrank_pointMod_odd P
  have h₂ : ∀ b : Fin q,
      Module.finrank ℂ (residueShape P p q (Sum.inr b)).odd = 1 :=
    fun _ => finrank_pointMod_even P
  rw [Finset.sum_congr rfl fun a _ => h₁ a,
    Finset.sum_congr rfl fun b _ => h₂ b]
  simp

/-! ## Base change of a module known to be free -/

/-- **The base change of a free module of rank `(p | q)`**, in the
form used below: a module isomorphic to a free module of rank
`(p | q)` has base change the biproduct of residue modules. -/
noncomputable def tensorPointIso (P : SuperPoint S) (p q : ℕ)
    (M : S.Mod.{u, u, u, u})
    (e : M ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod)
        (fun _ => shift S.unitMod) i) :
    M.tensor (pointMod P) ≅ ⨁ residueShape P p q :=
  (tensorRightFunctor (pointMod P)).mapIso e ≪≫ freeTensorPoint P p q

/-- **The base change of a free module of rank `(p | q)` has
finite-dimensional even part.** -/
theorem finiteDimensional_even_of_free (P : SuperPoint S) (p q : ℕ)
    (M : S.Mod.{u, u, u, u})
    (e : M ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod)
        (fun _ => shift S.unitMod) i) :
    FiniteDimensional ℂ (M.tensor (pointMod P)).even :=
  (evenEquiv (tensorPointIso P p q M e)).symm.finiteDimensional

/-- **The base change of a free module of rank `(p | q)` has
finite-dimensional odd part.** -/
theorem finiteDimensional_odd_of_free (P : SuperPoint S) (p q : ℕ)
    (M : S.Mod.{u, u, u, u})
    (e : M ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod)
        (fun _ => shift S.unitMod) i) :
    FiniteDimensional ℂ (M.tensor (pointMod P)).odd :=
  (oddEquiv (tensorPointIso P p q M e)).symm.finiteDimensional

/-- **The even dimension of the base change of a free module of
rank `(p | q)` is `p`.** -/
theorem finrank_even_of_free (P : SuperPoint S) (p q : ℕ)
    (M : S.Mod.{u, u, u, u})
    (e : M ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod)
        (fun _ => shift S.unitMod) i) :
    Module.finrank ℂ (M.tensor (pointMod P)).even = p := by
  rw [LinearEquiv.finrank_eq (evenEquiv (tensorPointIso P p q M e)),
    finrank_biproduct_even]

/-- **The odd dimension of the base change of a free module of
rank `(p | q)` is `q`.** -/
theorem finrank_odd_of_free (P : SuperPoint S) (p q : ℕ)
    (M : S.Mod.{u, u, u, u})
    (e : M ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod)
        (fun _ => shift S.unitMod) i) :
    Module.finrank ℂ (M.tensor (pointMod P)).odd = q := by
  rw [LinearEquiv.finrank_eq (oddEquiv (tensorPointIso P p q M e)),
    finrank_biproduct_odd]

/-! ## The super vector space of a base change -/

-- The finite-dimensionality instances pin the intended value, and
-- are the signature the two coordinate equivalences are stated at.
/-- **The base change of a super module along a point, packaged as a
super vector space.**  The components of a super module live in an
arbitrary universe, while `RS.SuperVect` asks for types in `Type`,
so the packaging is by coordinates: each component is replaced by
the space of coordinate vectors of its dimension.  The two
equivalences `RS.toSuperVectEvenEquiv` and `RS.toSuperVectOddEquiv`
identify the components of the base change with the components of
this super vector space. -/
noncomputable def toSuperVect (P : SuperPoint S)
    (M : S.Mod.{u, u, u, u})
    :
    SuperVect where
  even := Fin (Module.finrank ℂ (M.tensor (pointMod P)).even) → ℂ
  odd := Fin (Module.finrank ℂ (M.tensor (pointMod P)).odd) → ℂ

@[simp] theorem toSuperVect_even (P : SuperPoint S)
    (M : S.Mod.{u, u, u, u})
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd] :
    (toSuperVect P M).even =
      (Fin (Module.finrank ℂ (M.tensor (pointMod P)).even) → ℂ) :=
  rfl

@[simp] theorem toSuperVect_odd (P : SuperPoint S)
    (M : S.Mod.{u, u, u, u})
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd] :
    (toSuperVect P M).odd =
      (Fin (Module.finrank ℂ (M.tensor (pointMod P)).odd) → ℂ) :=
  rfl

/-- The even part of the base change is the even part of the super
vector space attached to it. -/
noncomputable def toSuperVectEvenEquiv (P : SuperPoint S)
    (M : S.Mod.{u, u, u, u})
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd] :
    (M.tensor (pointMod P)).even ≃ₗ[ℂ] (toSuperVect P M).even :=
  (Module.finBasis ℂ (M.tensor (pointMod P)).even).equivFun

/-- The odd part of the base change is the odd part of the super
vector space attached to it. -/
noncomputable def toSuperVectOddEquiv (P : SuperPoint S)
    (M : S.Mod.{u, u, u, u})
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd] :
    (M.tensor (pointMod P)).odd ≃ₗ[ℂ] (toSuperVect P M).odd :=
  (Module.finBasis ℂ (M.tensor (pointMod P)).odd).equivFun

/-! ## Explicit coordinates in the free case -/

/-- **Coordinates on the even part**: the base change of a free
module of rank `(p | q)` has even part the space of `p`-tuples of
complex numbers. -/
noncomputable def freeEvenEquivFin (P : SuperPoint S) (p q : ℕ)
    (M : S.Mod.{u, u, u, u})
    (e : M ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod)
        (fun _ => shift S.unitMod) i) :
    (M.tensor (pointMod P)).even ≃ₗ[ℂ] (Fin p → ℂ) :=
  haveI := finiteDimensional_even_of_free P p q M e
  (Module.finBasisOfFinrankEq ℂ (M.tensor (pointMod P)).even
    (finrank_even_of_free P p q M e)).equivFun

/-- **Coordinates on the odd part**: the base change of a free
module of rank `(p | q)` has odd part the space of `q`-tuples of
complex numbers. -/
noncomputable def freeOddEquivFin (P : SuperPoint S) (p q : ℕ)
    (M : S.Mod.{u, u, u, u})
    (e : M ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod)
        (fun _ => shift S.unitMod) i) :
    (M.tensor (pointMod P)).odd ≃ₗ[ℂ] (Fin q → ℂ) :=
  haveI := finiteDimensional_odd_of_free P p q M e
  (Module.finBasisOfFinrankEq ℂ (M.tensor (pointMod P)).odd
    (finrank_odd_of_free P p q M e)).equivFun

/-- **The super vector space of the base change of a free module of
rank `(p | q)`** has even part of dimension `p`. -/
theorem finrank_toSuperVect_even_of_free (P : SuperPoint S)
    (p q : ℕ) (M : S.Mod.{u, u, u, u})
    (e : M ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod)
        (fun _ => shift S.unitMod) i)
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd] :
    Module.finrank ℂ (toSuperVect P M).even = p := by
  rw [← finrank_even_of_free P p q M e]
  change Module.finrank ℂ
    (Fin (Module.finrank ℂ (M.tensor (pointMod P)).even) → ℂ) = _
  rw [Module.finrank_fin_fun ℂ]

/-- **The super vector space of the base change of a free module of
rank `(p | q)`** has odd part of dimension `q`. -/
theorem finrank_toSuperVect_odd_of_free (P : SuperPoint S)
    (p q : ℕ) (M : S.Mod.{u, u, u, u})
    (e : M ≅ ⨁ fun i : Fin p ⊕ Fin q =>
      Sum.elim (fun _ => S.unitMod)
        (fun _ => shift S.unitMod) i)
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd] :
    Module.finrank ℂ (toSuperVect P M).odd = q := by
  rw [← finrank_odd_of_free P p q M e]
  change Module.finrank ℂ
    (Fin (Module.finrank ℂ (M.tensor (pointMod P)).odd) → ℂ) = _
  rw [Module.finrank_fin_fun ℂ]


/-! ## Sealing the coordinates

The two coordinate equivalences are chosen bases, and nothing below
should depend on how they were chosen.  Sealing them keeps `simp`
from unfolding a base change into a composite of `Module.finBasis`
coordinates, which is what makes the coherence laws of the base
change unmanageable downstream. -/

attribute [irreducible] toSuperVectEvenEquiv toSuperVectOddEquiv

end RS
