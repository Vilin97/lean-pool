/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RelativePieceKeystone
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RestrictionFlatness

/-!
# Leaf-A chain assembly (Wedhorn Prop 8.30, whole-space residual)

The downstream fold that assembles the Remark 7.55 flatness chain for the whole-space
image piece `𝒪_B(im E)` over `B = 𝒪_X(D)`. This is the join point of two otherwise parallel
branches:

* the **per-step machinery** (`RelativePieceKeystone`): `flat_chainStep_domUnit` (the
  `CompatiblePlusSubring`-free domUnit step, span⊤ from the dominating unit),
  `flat_presheafValue_coUnitDatum_at_base` (the `X₀` coUnit base step),
  `remark755_dominating_unit_over_presheafValue` (the dominating unit `u`, `|u| ≤ |s|`);
* the **chain fold** (`RestrictionFlatness`): `restrictionMap_flat_chain`.

The chain invariant `h_pb : u·s⁻¹ ∈ B⁺` is **structural** — `u` is a *generator* of the step
piece `{tᵢ, u}` over the denominator `s`, so `u·s⁻¹ = divByS u s ∈ locPlusSubring ⊆ B⁺`
(`RationalLocData.divByS_mem_locPlusSubring`, upstream in `Presheaf`); no power-bounded keystone
or Spa pullback is needed (so `WedhornCechAcyclicity` is NOT imported).

Wedhorn Remark 7.55 (wedhorn.txt:3504-3517): `Spa B ⊇ X₀ ⊇ ⋯ ⊇ Xₙ = im E`, `X₀` the
dominating-unit piece (where `s` becomes a unit), each `Xᵢ = Xᵢ₋₁ ∩ {x(tᵢ) ≤ x(s)}`.
Every piece is a rational subset of `Spa B` (two-level `presheafValue`), so the whole fold
stays two-level — the `𝒪(X₀)`-relative chain would be three-level and exceed the elaborator.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Remark 7.55, Prop 8.30 (wedhorn.txt:3504-3517)
-/

namespace ValuationSpectrum

open Pointwise
open Classical

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]
-- The completion IRIE instance (`presheafValuePlus_isRingOfIntegralElements`) requires the base
-- affinoid interface; threaded explicitly (Wedhorn Def 7.14 / 7.19). All-`Prop` class, diamond-free.
variable [IsRingOfIntegralElements (A⁺)]

/-- **Prop 8.30 (assembled): restriction-map flatness for a rational pair.** For `D' ⊆ D` rational
subsets, `𝒪_X(D) → 𝒪_X(D')` is flat. This is the *usable* form (what the structure-sheaf/OMT proof
consumes): Wedhorn's first reduction "we may assume `X = V`" (`relativePiece_equiv`, the 8.16 keystone)
identifies `𝒪_X(D') ≅ 𝒪_B(im D')` over `B = 𝒪_X(D)`, intertwining the restriction with the whole-space
canonical map, so flatness transports (`Module.Flat.of_linearEquiv`) from the now-complete whole-space
chain `prop_8_30_imagePiece_assembled`. The downstream, sorry-free-assembly counterpart of
`prop_8_30_remark755_chain` (which routes through the RPK stub). -/
theorem prop_8_30_remark755_chain_assembled
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [HasLocLiftPowerBounded A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hD : D.IsRational) (hD' : D'.IsRational) :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      (restrictionMapHom D D' h).toModule := by
  haveI hTateB : IsTateRing (presheafValue D) := presheafValue_isTateRing_concrete D
  haveI : IsNoetherianRing (presheafValue D) := presheafValue_isNoetherianRing_faithful D
  haveI : IsHuberRing (presheafValue D) := hTateB.toIsHuberRing
  haveI : IsStronglyNoetherian (presheafValue D) := presheafValue_isStronglyNoetherian_faithful D
  set W := imagePieceDatum D D'.T D'.s hD'.span_eq_top with hW
  set e := relativePiece_equiv D D' h hD'.span_eq_top with he
  have hflatW : @Module.Flat (presheafValue D) (presheafValue W) _ _
      (W.canonicalMap).toModule :=
    prop_8_30_imagePiece_assembled D D' hD'.span_eq_top
  letI : Module (presheafValue D) (presheafValue D') := (restrictionMapHom D D' h).toModule
  letI : Module (presheafValue D) (presheafValue W) := W.canonicalMap.toModule
  have he_smul : ∀ (a : presheafValue D) (x : presheafValue D'), e (a • x) = a • e x := by
    intro a x
    change e (restrictionMapHom D D' h a * x) = W.canonicalMap a * e x
    rw [e.map_mul]; congr 1
    exact relativePiece_equiv_restrictionMap D D' h hD'.span_eq_top a
  exact @Module.Flat.of_linearEquiv (presheafValue D) (presheafValue W) (presheafValue D')
    _ _ _ _ _ hflatW
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

end ValuationSpectrum
