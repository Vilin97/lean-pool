/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.SquareZeroLocalizedRing


/-!
# Localized specialization respects the localized action

The Ore localization of the opposite deformation ring acts on the localized
deformation module.  This file proves directly on displayed left-Ore
fractions that module specialization intertwines this action with the
commutative special-fibre localization action.

The use of the opposite ring is load-bearing: an Ore equation in `Bᵐᵒᵖ` is
sent through `oppositeSpecializationRingHom`, whose multiplicativity is
exactly the reversal from written right multiplication to the left action.
No Artinian descent, characteristic-variety, or involutivity statement is
made here.
-/

@[expose] public section

namespace Stafford38.Characteristic.LocalizedSpecializationActionCompatibility

open Stafford38.Characteristic.SquareZeroLocalizedExactness
open Stafford38.Characteristic.SquareZeroLocalizedRing
open Stafford38.Characteristic.SquareZeroTraceData

noncomputable section

universe u_k u_R u_B u_N u_G

variable {k : Type u_k} {R : Type u_R} {B : Type u_B}
variable {N : Type u_N} {G : Type u_G}
variable [Field k] [CommRing R] [Algebra k R]
variable [Ring B] [Algebra k B]
variable [AddCommGroup N] [Module k N] [Module Bᵐᵒᵖ N]
variable [SMulCommClass k Bᵐᵒᵖ N]
variable [AddCommGroup G] [Module k G] [Module R G]

variable (D : RightSquareZeroTraceData k R B N G)
variable (S : Submonoid R)
variable [OreLocalization.OreSet (OppositeDenominators D S)]

/-- Specialization of the concrete localized deformation module intertwines
the full localized opposite-ring action with specialization of the scalar.
The multiplication displayed on the source is the left action corresponding
to written right multiplication before passage to the opposite ring. -/
theorem localizedSpecialization_smul
    (a : OreLocalization (OppositeDenominators D S) (Bᵐᵒᵖ))
    (z : LocalizedDeformationModule D S) :
    localizedSpecialization D S (a • z) =
      localizedOppositeSpecialization D S a •
        localizedSpecialization D S z := by
  induction a using OreLocalization.ind with
  | _ b s =>
    induction z using OreLocalization.ind with
    | _ m t =>
      obtain ⟨r, u, hur, haction⟩ :=
        OreLocalization.oreDivSMulChar' b m s t
      rw [haction, localizedSpecialization_apply,
        localizedSpecializationFun_oreDiv,
        localizedOppositeSpecialization_oreDiv,
        localizedSpecialization_apply,
        localizedSpecializationFun_oreDiv]
      have hscalar :
          ((localizedDenominatorUnits D S s)⁻¹ :
              Units (Localization S)) *
              algebraMap R (Localization S) (D.pi b.unop) =
            Localization.mk (D.pi b.unop) (denominatorMap D S s) := by
        change
          ((1 : R) /ₒ denominatorMap D S s) *
              (D.pi b.unop /ₒ (1 : S)) =
            D.pi b.unop /ₒ denominatorMap D S s
        simpa only [one_mul] using
          (OreLocalization.one_div_mul
            (S := S) (r := D.pi b.unop) (s := (1 : S))
            (t := denominatorMap D S s))
      rw [hscalar, LocalizedModule.mk_smul_mk]
      have hore := congrArg (oppositeSpecializationRingHom D) hur
      simp only [map_mul, oppositeSpecializationRingHom_apply] at hore
      apply LocalizedModule.mk_eq.mpr
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul]
      have hrho : D.rho (r • m) = D.pi r.unop • D.rho m := by
        simpa using D.rho_action r.unop m
      have hcoeff :
          (D.pi s.val.unop * D.pi t.val.unop) * D.pi r.unop =
            (D.pi u.val.unop * D.pi s.val.unop) * D.pi b.unop := by
        calc
          (D.pi s.val.unop * D.pi t.val.unop) * D.pi r.unop =
            D.pi s.val.unop * (D.pi r.unop * D.pi t.val.unop) := by
              ring
          _ = D.pi s.val.unop * (D.pi u.val.unop * D.pi b.unop) := by
              rw [hore]
          _ = (D.pi u.val.unop * D.pi s.val.unop) * D.pi b.unop := by
              ring
      rw [hrho, ← mul_smul, ← mul_smul]
      have hcoeff' :
          ((denominatorMap D S s : R) *
              (denominatorMap D S t : R)) * D.pi r.unop =
            (denominatorMap D S (u * s) : R) * D.pi b.unop := by
        rw [map_mul]
        exact hcoeff
      exact congrArg (fun q : R => q • D.rho m) hcoeff'


end

end Stafford38.Characteristic.LocalizedSpecializationActionCompatibility
