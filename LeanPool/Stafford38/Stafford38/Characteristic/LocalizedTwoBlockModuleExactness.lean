/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.LocalizedTwoBlockQuotient


/-!
# Module exactness after the localized two-block ring quotient

The two-block ideal annihilates the localized deformation module, so passage
to the quotient changes only its scalar ring.  This file names the action of
the quotient parameter and identifies it exactly with the already constructed
localized parameter action.  Parameter exactness and the additive
special-fibre equivalence therefore transfer without quotienting the module.

No identification of the quotient ring modulo its parameter with the
commutative doubled-power quotient is asserted.
-/

@[expose] public section

namespace Stafford38.Characteristic.LocalizedTwoBlockModuleExactness

open Stafford38.Characteristic.LocalizedTwoBlockQuotient
open Stafford38.Characteristic.RightReesArtinianAdapter
open Stafford38.Characteristic.SquareZeroLocalizedExactness
open Stafford38.Characteristic.SquareZeroTraceData

noncomputable section

universe u_R u_k u_B u_N u_G

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
variable [IsLocalRing (Localization S)]

local notation "Wₗ" => LocalizedDeformationModule D S
local notation "A₀" => Localization S
local notation "𝔪" => IsLocalRing.maximalIdeal A₀

/-- The additive endomorphism induced by the parameter class in the localized
two-block quotient ring. -/
def localizedTwoBlockParameterAct
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤
      Module.annihilator A₀ (LocalizedModule S G)) :
    Wₗ →+ Wₗ where
  toFun w :=
    localizedTwoBlockAction D S q hpow
      ((localizedTwoBlockIdeal D S q).ringCon.mk'
        (OreLocalization.numeratorRingHom (MulOpposite.op D.c))) w
  map_zero' := by
    calc
      localizedTwoBlockAction D S q hpow
          ((localizedTwoBlockIdeal D S q).ringCon.mk'
            (OreLocalization.numeratorRingHom (MulOpposite.op D.c))) 0 =
        localizedCAct D S 0 :=
          localizedTwoBlock_parameter_smul D S q hpow 0
      _ = 0 := (localizedCAct D S).map_zero
  map_add' x y := by
    calc
      localizedTwoBlockAction D S q hpow
          ((localizedTwoBlockIdeal D S q).ringCon.mk'
            (OreLocalization.numeratorRingHom (MulOpposite.op D.c))) (x + y) =
        localizedCAct D S (x + y) :=
          localizedTwoBlock_parameter_smul D S q hpow (x + y)
      _ = localizedCAct D S x + localizedCAct D S y :=
        (localizedCAct D S).map_add x y
      _ = localizedTwoBlockAction D S q hpow
            ((localizedTwoBlockIdeal D S q).ringCon.mk'
              (OreLocalization.numeratorRingHom (MulOpposite.op D.c))) x +
          localizedTwoBlockAction D S q hpow
            ((localizedTwoBlockIdeal D S q).ringCon.mk'
              (OreLocalization.numeratorRingHom (MulOpposite.op D.c))) y := by
        rw [localizedTwoBlock_parameter_smul,
          localizedTwoBlock_parameter_smul]

/-- Quotienting the scalar ring does not change the parameter endomorphism of
the localized deformation module. -/
theorem localizedTwoBlockParameterAct_eq_localizedCAct
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤
      Module.annihilator A₀ (LocalizedModule S G)) :
    localizedTwoBlockParameterAct D S q hpow =
      localizedCAct D S := by
  ext w
  exact localizedTwoBlock_parameter_smul D S q hpow w

/-- The square-zero parameter sequence remains exact after descent of the
scalar action to the localized two-block quotient ring. -/
theorem localizedTwoBlockParameterAct_ker_eq_range
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤
      Module.annihilator A₀ (LocalizedModule S G)) :
    AddMonoidHom.ker (localizedTwoBlockParameterAct D S q hpow) =
      AddMonoidHom.range (localizedTwoBlockParameterAct D S q hpow) := by
  rw [localizedTwoBlockParameterAct_eq_localizedCAct]
  exact localizedCAct_ker_eq_range D S

/-- The additive special fibre of the unchanged quotient-ring module is the
ordinary localized special fibre. -/
noncomputable def localizedTwoBlockSpecialFibreAddEquiv
    (q : ℕ)
    (hpow : 𝔪 ^ q ≤
      Module.annihilator A₀ (LocalizedModule S G)) :
    (Wₗ ⧸ AddMonoidHom.range
        (localizedTwoBlockParameterAct D S q hpow)) ≃+
      LocalizedModule S G := by
  rw [localizedTwoBlockParameterAct_eq_localizedCAct]
  exact localizedSpecialFibreAddEquiv D S


end

end Stafford38.Characteristic.LocalizedTwoBlockModuleExactness
