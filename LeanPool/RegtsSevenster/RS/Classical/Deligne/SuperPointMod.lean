/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperEvenRing
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaModule

/-!
# The residue module of a complex point

A complex point of a super-commutative algebra makes the complex
numbers, concentrated in even degree, a module over that algebra:
the even part acts through the point and the odd part acts by zero,
which is consistent exactly because a point kills the products of
two odd elements.
-/

@[expose] public section

namespace RS

open CategoryTheory

universe u u' w

namespace SuperCommAlgebra

variable {S : SuperCommAlgebra.{u, u'}}

/-- **The residue module of a complex point**: the complex numbers
in even degree and zero in odd degree, with the even part of the
algebra acting through the point. -/
noncomputable def pointMod (P : SuperPoint S) :
    S.Mod.{u, u', w, w} where
  even := ULift.{w} ℂ
  odd := ULift.{w} PUnit.{1}
  actEE := LinearMap.mk₂ ℂ
    (fun x c => ULift.up (P.chi x * c.down))
    (fun x y c => ULift.ext _ _ (by
      simp only [map_add, ULift.add_down]
      ring))
    (fun r x c => ULift.ext _ _ (by
      simp only [map_smul, smul_eq_mul, ULift.smul_down]
      ring))
    (fun x c d => ULift.ext _ _ (by
      simp only [ULift.add_down]
      ring))
    (fun r x c => ULift.ext _ _ (by
      simp only [ULift.smul_down, smul_eq_mul]
      ring))
  actEO := 0
  actOE := 0
  actOO := 0
  one_act_e m := by
    refine ULift.ext _ _ ?_
    change P.chi 1 * m.down = m.down
    rw [map_one, one_mul]
  one_act_o m := Subsingleton.elim _ _
  assoc_eee x y m := by
    refine ULift.ext _ _ ?_
    change P.chi (S.mulEE x y) * m.down = P.chi x * (P.chi y * m.down)
    rw [show S.mulEE x y = x * y from rfl, map_mul, mul_assoc]
  assoc_eeo _ _ _ := Subsingleton.elim _ _
  assoc_eoe _ _ _ := Subsingleton.elim _ _
  assoc_eoo x u m := by
    refine ULift.ext _ _ ?_
    change (0 : ℂ) = P.chi x * (0 : ULift.{w} ℂ).down
    simp
  assoc_oee _ _ _ := Subsingleton.elim _ _
  assoc_oeo x u m := by
    refine ULift.ext _ _ ?_
    change (0 : ℂ) = (0 : ULift.{w} ℂ).down
    rfl
  assoc_ooe u v m := by
    refine ULift.ext _ _ ?_
    change P.chi (S.mulOO u v) * m.down = (0 : ULift.{w} ℂ).down
    rw [P.vanishing, zero_mul]; rfl
  assoc_ooo _ _ _ := Subsingleton.elim _ _

end SuperCommAlgebra

end RS
