/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModMonoidal
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModShift

/-!
# Tensoring with the shifted unit is the parity shift

For a super-commutative ℂ-algebra `S` and a module `M` over it,
the parity shift of the unit module is invertible for the tensor
product of `RS.Classical.Deligne.SuperModTensor`:

  `(shift S.unitMod) ⊗ M ≅ shift M`.

The construction is the exact analogue of the left unitor of
`RS.Classical.Deligne.SuperModMonoidal`, with the parity of the
algebra factor reversed.  Reversing that parity forces two of the
four blocks to carry a sign: the shifted unit relabels the four
multiplication blocks of `S`, and the eight balancing laws of the
tensor product then hold only for the block pattern

  `fee = M.actOE`, `foo = -M.actEO`,
  `feo = -M.actOO`, `foe = M.actEE`,

whose relative signs are pinned by the odd-odd relators (where the
Koszul sign lives) and by the odd action laws; the overall sign is
the one free choice, normalised here by taking the even-even block
unsigned.  The inverse carries the matching sign, `−1` in even
degree and `+1` in odd degree.

## Contents

* `RS.SuperCommAlgebra.Mod.shiftUnitMod_actOO_one`,
  `shiftUnitMod_actEO_one`: acting on the algebra unit inside the
  shifted unit module returns the scalar.
* `RS.SuperCommAlgebra.Mod.shiftUnitData`: the four blocks with
  their eight balancing laws and eight action laws.
* `RS.SuperCommAlgebra.Mod.shiftUnitHom`, `shiftUnitInv`: the two
  structure maps, with their computation rules.
* `RS.SuperCommAlgebra.Mod.shiftUnitTensor`: the isomorphism.
-/

namespace RS

open CategoryTheory MonoidalCategory

universe u

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u}}

/-! ## The shifted unit module -/

/-- Acting by an odd scalar on the algebra unit, viewed inside the
shifted unit module, returns the scalar.  In the shifted module
the algebra unit is odd, so the relevant block is `actOO`. -/
theorem shiftUnitMod_actOO_one (v : S.odd) :
    (shift S.unitMod).actOO v S.one = v :=
  unitMod_actOE_one v

/-- Acting by an even scalar on the algebra unit, viewed inside
the shifted unit module, returns the scalar. -/
theorem shiftUnitMod_actEO_one (x : S.even) :
    (shift S.unitMod).actEO x S.one = x :=
  unitMod_actEE_one x

/-! ## The four blocks -/

section ShiftUnit

variable (M : S.Mod.{u, u, u, u})

/-- The data of the shift-unit isomorphism: the shifted unit
factor acts on the module, with the parities of the algebra
relabelled.  The odd-odd and even-odd blocks carry a sign, forced
by the four mixed balancing laws and by the four odd action
laws. -/
def shiftUnitData : TensorData (shift S.unitMod) M (shift M) where
  fee := M.actOE
  foo := -M.actEO
  feo := -M.actOO
  foe := M.actEE
  hee := fun b m n => by
    change M.actOE (S.mulEO b m) n = M.actOE m (M.actEE b n)
    erw [← M.assoc_oee, ← S.comm_eo]
  hoo := fun b m n => by
    change -M.actEO (S.mulEE b m) n = -M.actEO m (M.actEO b n)
    erw [M.assoc_eeo, M.actEO_actEO_comm]
  hoeo := fun c m n => by
    change -M.actEO (S.mulOO c m) n = M.actOE m (M.actOO c n)
    erw [M.assoc_ooo, M.actOE_actOO_neg, neg_neg]
  hooe := fun c m n => by
    change M.actOE (S.mulOE c m) n
      = -(-(M.actEO m (M.actOE c n)))
    erw [neg_neg, M.assoc_oee, M.actEO_actOE]
  heeo := fun b m n => by
    change -M.actOO (S.mulEO b m) n = -M.actOO m (M.actEO b n)
    erw [M.assoc_eoo, M.actEE_actOO]
  heoe := fun b m n => by
    change M.actEE (S.mulEE b m) n = M.actEE m (M.actEE b n)
    erw [M.assoc_eee, M.actEE_actEE_comm]
  hoee := fun c m n => by
    change M.actEE (S.mulOO c m) n = -(M.actOO m (M.actOE c n))
    erw [M.assoc_ooe, M.actOO_actOE_neg]
  hooo := fun c m n => by
    change -M.actOO (S.mulOE c m) n = -(M.actEE m (M.actOO c n))
    erw [M.assoc_oeo, M.actEE_actOO]
  aee := fun a m n => M.assoc_eoe a m n
  aoo := fun a m n => by
    change -M.actEO (S.mulEE a m) n = M.actEO a (-(M.actEO m n))
    erw [M.assoc_eeo, map_neg]
  aeo := fun a m n => by
    change -M.actOO (S.mulEO a m) n = M.actEE a (-(M.actOO m n))
    erw [M.assoc_eoo, map_neg]
  aoe := fun a m n => M.assoc_eee a m n
  cee := fun c m n => M.assoc_ooe c m n
  coo := fun c m n => by
    change -M.actOO (S.mulOE c m) n = M.actOO c (-(M.actEO m n))
    erw [M.assoc_oeo, map_neg]
  ceo := fun c m n => by
    change -M.actEO (S.mulOO c m) n = M.actOE c (-(M.actOO m n))
    erw [M.assoc_ooo, map_neg]
  coe := fun c m n => M.assoc_oee c m n

/-! ## The structure maps -/

/-- The structure map of the shift-unit isomorphism. -/
noncomputable def shiftUnitHom :
    (shift S.unitMod).tensor M ⟶ shift M :=
  mkHom (shiftUnitData M)

/-- The structure map on an even-even generator. -/
@[simp] theorem shiftUnitHom_evenMap_tmulEE (v : S.odd) (m : M.even) :
    (shiftUnitHom M).evenMap (tmulEE (shift S.unitMod) M v m)
      = M.actOE v m :=
  mkHom_evenMap_tmulEE (shiftUnitData M) v m

/-- The structure map on an odd-odd generator. -/
@[simp] theorem shiftUnitHom_evenMap_tmulOO (x : S.even) (m : M.odd) :
    (shiftUnitHom M).evenMap (tmulOO (shift S.unitMod) M x m)
      = -M.actEO x m :=
  mkHom_evenMap_tmulOO (shiftUnitData M) x m

/-- The structure map on an even-odd generator. -/
@[simp] theorem shiftUnitHom_oddMap_tmulEO (v : S.odd) (m : M.odd) :
    (shiftUnitHom M).oddMap (tmulEO (shift S.unitMod) M v m)
      = -M.actOO v m :=
  mkHom_oddMap_tmulEO (shiftUnitData M) v m

/-- The structure map on an odd-even generator. -/
@[simp] theorem shiftUnitHom_oddMap_tmulOE (x : S.even) (m : M.even) :
    (shiftUnitHom M).oddMap (tmulOE (shift S.unitMod) M x m)
      = M.actEE x m :=
  mkHom_oddMap_tmulOE (shiftUnitData M) x m

/-- The inverse of the shift-unit isomorphism: tensor with the
algebra unit, which is odd in the shifted unit module.  The even
component carries a sign, forced by the odd-odd Koszul relator. -/
noncomputable def shiftUnitInv :
    shift M ⟶ (shift S.unitMod).tensor M where
  evenMap := -tmulOO (shift S.unitMod) M S.one
  oddMap := tmulOE (shift S.unitMod) M S.one
  map_actEE x m := by
    change -(tmulOO (shift S.unitMod) M S.one (M.actEO x m))
      = ((shift S.unitMod).tensor M).actEE x
        (-(tmulOO (shift S.unitMod) M S.one m))
    erw [map_neg, actEE_tmulOO, tmulOO_balanced_eoo]
  map_actEO x m := by
    change tmulOE (shift S.unitMod) M S.one (M.actEE x m)
      = ((shift S.unitMod).tensor M).actEO x
        (tmulOE (shift S.unitMod) M S.one m)
    exact ((actEO_tmulOE (shift S.unitMod) M x S.one m).trans
      (tmulOE_balanced_eoe (shift S.unitMod) M x S.one m)).symm
  map_actOE v m := by
    change tmulOE (shift S.unitMod) M S.one (M.actOO v m)
      = ((shift S.unitMod).tensor M).actOE v
        (-(tmulOO (shift S.unitMod) M S.one m))
    rw [map_neg]
    erw [actOE_tmulOO (shift S.unitMod) M v S.one m]
    simpa only [neg_neg] using
      (congrArg Neg.neg (tmulEO_balanced_ooo (shift S.unitMod) M v S.one m)).symm
  map_actOO v m := by
    change -(tmulOO (shift S.unitMod) M S.one (M.actOE v m))
      = ((shift S.unitMod).tensor M).actOO v
        (tmulOE (shift S.unitMod) M S.one m)
    erw [actOO_tmulOE, tmulEE_balanced_ooe]

/-- The inverse in even degree. -/
@[simp] theorem shiftUnitInv_evenMap (m : M.odd) :
    (shiftUnitInv M).evenMap m
      = -tmulOO (shift S.unitMod) M S.one m := rfl

/-- The inverse in odd degree. -/
@[simp] theorem shiftUnitInv_oddMap (m : M.even) :
    (shiftUnitInv M).oddMap m
      = tmulOE (shift S.unitMod) M S.one m := rfl

/-! ## The isomorphism -/

/-- **The parity shift of the unit is invertible**: tensoring with
the shifted unit module shifts the parity. -/
noncomputable def shiftUnitTensor :
    (shift S.unitMod).tensor M ≅ shift M where
  hom := shiftUnitHom M
  inv := shiftUnitInv M
  hom_inv_id := by
    refine hom_ext (fun (v : S.odd) m => ?_)
      (fun (x : S.even) m => ?_) (fun (v : S.odd) m => ?_)
      (fun (x : S.even) m => ?_)
    · erw [comp_evenMap, LinearMap.comp_apply,
        shiftUnitHom_evenMap_tmulEE, shiftUnitInv_evenMap,
        id_evenMap, LinearMap.id_coe, id_eq,
        ← tmulEE_balanced_ooe, shiftUnitMod_actOO_one]
    · erw [comp_evenMap, LinearMap.comp_apply,
        shiftUnitHom_evenMap_tmulOO, shiftUnitInv_evenMap, map_neg,
        neg_neg, id_evenMap, LinearMap.id_coe, id_eq,
        ← tmulOO_balanced_eoo, shiftUnitMod_actEO_one]
    · erw [comp_oddMap, LinearMap.comp_apply,
        shiftUnitHom_oddMap_tmulEO, shiftUnitInv_oddMap, map_neg,
        id_oddMap, LinearMap.id_coe, id_eq,
        ← tmulEO_balanced_ooo, shiftUnitMod_actOO_one]
    · erw [comp_oddMap, LinearMap.comp_apply,
        shiftUnitHom_oddMap_tmulOE, shiftUnitInv_oddMap,
        id_oddMap, LinearMap.id_coe, id_eq,
        ← tmulOE_balanced_eoe, shiftUnitMod_actEO_one]
  inv_hom_id := by
    refine Hom.ext (LinearMap.ext fun m => ?_)
      (LinearMap.ext fun m => ?_)
    · change (shiftUnitHom M).evenMap
        (-(tmulOO (shift S.unitMod) M S.one m)) = m
      refine Eq.trans (map_neg _ _) ?_
      refine Eq.trans (congrArg Neg.neg
        (shiftUnitHom_evenMap_tmulOO M S.one m)) ?_
      exact Eq.trans (neg_neg _) (M.one_act_o m)
    · exact Eq.trans (shiftUnitHom_oddMap_tmulOE M S.one m)
        (M.one_act_e m)

end ShiftUnit

end SuperCommAlgebra.Mod

end RS
