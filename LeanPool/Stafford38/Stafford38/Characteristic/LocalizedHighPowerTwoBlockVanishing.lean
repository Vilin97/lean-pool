/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.LocalizedSpecializationActionCompatibility
import LeanPool.Stafford38.Stafford38.Characteristic.RightReesArtinianAdapter

/-!
# Localized high-power two-block vanishing

This file discharges the elementwise two-block condition in the concrete
right-Rees Artinian adapter.  A localized scalar whose specialization lies in
an annihilating ideal sends every deformation vector into the parameter
image.  Two such scalar actions therefore produce two parameter factors and
vanish by square-zero.

The opposite localization acts on the left in the order corresponding to
written right multiplication.  The finite sum below consequently retains the
displayed product order.  No residue-field action is placed on the deformation
module.
-/

namespace Stafford38.Characteristic.LocalizedHighPowerTwoBlockVanishing

open Stafford38.Characteristic.LocalizedSpecializationActionCompatibility
open Stafford38.Characteristic.RightReesArtinianAdapter
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

/-- The central deformation parameter remains central after Ore localization.
The multiplication is in the opposite ring, hence represents written right
multiplication in the original deformation ring. -/
theorem localizedParameter_comm
    (a : OreLocalization (OppositeDenominators D S) (Bᵐᵒᵖ)) :
    OreLocalization.numeratorRingHom (MulOpposite.op D.c) * a =
      a * OreLocalization.numeratorRingHom (MulOpposite.op D.c) := by
  induction a using OreLocalization.ind with
  | _ b s =>
      rw [OreLocalization.numeratorRingHom_apply]
      rw [OreLocalization.oreDiv_mul_char
        (MulOpposite.op D.c) b 1 s (MulOpposite.op D.c) s]
      · rw [OreLocalization.mul_div_one]
        congr 1
        · apply MulOpposite.unop_injective
          exact (D.c_center.comm b.unop).symm
        · simp
      · apply MulOpposite.unop_injective
        exact D.c_center.comm s.val.unop

/-- A localized scalar action commutes with the concrete parameter action.
This is the bridge that permits the two high-power blocks to contribute two
successive parameter factors. -/
theorem smul_localizedCAct
    (a : OreLocalization (OppositeDenominators D S) (Bᵐᵒᵖ))
    (z : LocalizedDeformationModule D S) :
    a • localizedCAct D S z = localizedCAct D S (a • z) := by
  rw [localizedCAct_apply, localizedCAct_apply]
  rw [← OreLocalization.oreDiv_one_smul]
  rw [← mul_smul]
  rw [← OreLocalization.numeratorRingHom_apply (MulOpposite.op D.c)]
  rw [← localizedParameter_comm D S a, mul_smul]
  exact OreLocalization.oreDiv_one_smul _ _

/-- If the specialization of a localized scalar lies in an ideal annihilating
the special fibre, then its action on every deformation vector is a localized
parameter multiple. -/
theorem smul_mem_parameterRange_of_specialization_mem_annihilator
    (a : OreLocalization (OppositeDenominators D S) (Bᵐᵒᵖ))
    (ha : localizedOppositeSpecialization D S a ∈
      Module.annihilator (Localization S) (LocalizedModule S G))
    (z : LocalizedDeformationModule D S) :
    a • z ∈ AddMonoidHom.range (localizedCAct D S) := by
  rw [← localizedSpecialization_ker_eq_range D S]
  rw [AddMonoidHom.mem_ker, localizedSpecialization_smul D S]
  exact Module.mem_annihilator.mp ha (localizedSpecialization D S z)

/-- Two localized factors whose specializations lie in one annihilating ideal
act successively by zero. -/
theorem product_smul_eq_zero_of_specializations_mem_annihilator
    (a b : OreLocalization (OppositeDenominators D S) (Bᵐᵒᵖ))
    (ha : localizedOppositeSpecialization D S a ∈
      Module.annihilator (Localization S) (LocalizedModule S G))
    (hb : localizedOppositeSpecialization D S b ∈
      Module.annihilator (Localization S) (LocalizedModule S G))
    (z : LocalizedDeformationModule D S) :
    (a * b) • z = 0 := by
  obtain ⟨w, hw⟩ :=
    smul_mem_parameterRange_of_specialization_mem_annihilator D S b hb z
  obtain ⟨v, hv⟩ :=
    smul_mem_parameterRange_of_specialization_mem_annihilator D S a ha w
  rw [mul_smul, ← hw, smul_localizedCAct D S, ← hv]
  exact localizedCAct_sq_eq_zero D S v

/-- An annihilating maximal-ideal power supplies the exact two-block
vanishing proposition required by `RightReesArtinianAdapter`. -/
theorem localizedHighPowerTwoBlockVanishing_of_annihilatingPower
    [IsLocalRing (Localization S)]
    (q : ℕ)
    (hpow : IsLocalRing.maximalIdeal (Localization S) ^ q ≤
      Module.annihilator (Localization S) (LocalizedModule S G)) :
    LocalizedHighPowerTwoBlockVanishing D S q := by
  intro iota s a b ha hb z
  rw [Finset.sum_smul]
  apply Finset.sum_eq_zero
  intro i hi
  exact product_smul_eq_zero_of_specializations_mem_annihilator D S
    (a i) (b i) (hpow (ha i hi)) (hpow (hb i hi)) z


end

end Stafford38.Characteristic.LocalizedHighPowerTwoBlockVanishing
