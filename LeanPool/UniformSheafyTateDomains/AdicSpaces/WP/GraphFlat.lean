/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.GraphFibreL1
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Reduced

/-!
# Flatness of the graph model over the head

([hrw-decomposition] L1 input (α).)  Wedhorn 8.30 — the restriction map to a
rational subset is flat — transported to the head's graph model along the two
project bridges: the completion model `A ≃ 𝒪_X(X)` and the graph bridge
`𝒪_X(U) ≅ Q`.
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver FiniteJet.GraphKoszul

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {w : ℕ → ℕ} {N : ℕ}

/-- **The W16 law**: the graph bridge takes the canonical map to the constants
of the graph model. -/
theorem headLocEquiv_canonicalMap (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (x : WPHead K w N) :
    headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap x) = headToQ DH x := by
  haveI : HasLocLiftPowerBounded (WPHead K w N) := hasLocLiftPowerBounded_faithful
  rw [show headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap x) =
      headLocFwd ϖ DH hDH (DH.canonicalMap x) from rfl,
    show DH.canonicalMap x = DH.coeRingHom
      (algebraMap (WPHead K w N) (Localization.Away DH.s) x) from rfl,
    headLocFwd_coe, headLocFwdAlg_algebraMap]
  rfl

/-- The global datum's rational open contains every other one. -/
theorem rationalOpen_globalLocData_superset
    (DH : RationalLocData (WPHead K w N)) :
    rationalOpen DH.T DH.s ⊆
      rationalOpen (globalLocData DH.P).T (globalLocData DH.P).s := by
  rw [show (globalLocData DH.P).T = {1} from rfl,
    show (globalLocData DH.P).s = 1 from rfl, rationalOpen_singleton_one]
  exact rationalOpen_subset_spa

/-- **L1 input (α)**: the graph model is flat over the head (Wedhorn 8.30,
transported through the completion model and the graph bridge). -/
theorem flat_headToQ (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    letI : Algebra (WPHead K w N) (QHead DH) := (headToQ DH).toAlgebra
    Module.Flat (WPHead K w N) (QHead DH) := by
  letI : Algebra (WPHead K w N) (QHead DH) := (headToQ DH).toAlgebra
  haveI hNoeth : IsNoetherianRing (WPHead K w N) :=
    isNoetherianRing_WPHead w N ϖ hK₀
  haveI hSN : IsStronglyNoetherian (WPHead K w N) :=
    isStronglyNoetherian_WPHead w N ϖ hK₀
  haveI : HasLocLiftPowerBounded (WPHead K w N) := hasLocLiftPowerBounded_faithful
  have hsub := rationalOpen_globalLocData_superset DH
  -- Wedhorn 8.30 for the restriction from the global datum
  letI algres : Algebra (presheafValue (globalLocData DH.P)) (presheafValue DH) :=
    (restrictionMapHom (globalLocData DH.P) DH hsub).toAlgebra
  haveI hflat : Module.Flat (presheafValue (globalLocData DH.P))
      (presheafValue DH) :=
    prop_8_30_flat_clean_proof (globalLocData DH.P) DH hsub
  -- the head sits under both through the canonical maps
  letI algA₁ : Algebra (WPHead K w N) (presheafValue (globalLocData DH.P)) :=
    ((globalLocData DH.P).canonicalMap).toAlgebra
  letI algB₁ : Algebra (WPHead K w N) (presheafValue DH) :=
    (DH.canonicalMap).toAlgebra
  haveI htower : IsScalarTower (WPHead K w N)
      (presheafValue (globalLocData DH.P)) (presheafValue DH) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (restrictionMapHom_canonicalMap_generic (globalLocData DH.P) DH hsub x).symm
  -- the completion model is the head itself, hence flat over it
  haveI hflat1 : Module.Flat (WPHead K w N)
      (presheafValue (globalLocData DH.P)) := by
    set α : (WPHead K w N) ≃+* presheafValue (globalLocData DH.P) :=
      completeRingEquivCompletionModel (A := WPHead K w N) DH.P with hα
    have hαapp : ∀ r : WPHead K w N,
        α r = (globalLocData DH.P).canonicalMap r := fun r => by rw [hα]; rfl
    refine Module.Flat.of_linearEquiv (R := WPHead K w N)
      (M := WPHead K w N) (N := presheafValue (globalLocData DH.P))
      { toFun := fun z => α.symm z
        map_add' := map_add _
        map_smul' := fun r z => by
          show α.symm ((globalLocData DH.P).canonicalMap r * z) =
            r * α.symm z
          have hr : α.symm ((globalLocData DH.P).canonicalMap r) = r := by
            rw [← hαapp r]
            exact α.symm_apply_apply r
          rw [map_mul α.symm, hr]
        invFun := fun x => (globalLocData DH.P).canonicalMap x
        left_inv := fun z => by
          show (globalLocData DH.P).canonicalMap (α.symm z) = z
          rw [← hαapp]
          exact α.apply_symm_apply z
        right_inv := fun x => by
          show α.symm ((globalLocData DH.P).canonicalMap x) = x
          rw [← hαapp x]
          exact α.symm_apply_apply x }
  haveI hflatB₁ : Module.Flat (WPHead K w N) (presheafValue DH) :=
    Module.Flat.trans (WPHead K w N) (presheafValue (globalLocData DH.P))
      (presheafValue DH)
  -- transport along the graph bridge
  set β := headLocEquiv ϖ hK₀ DH hDH with hβ
  refine Module.Flat.of_linearEquiv (R := WPHead K w N)
    (M := presheafValue DH) (N := QHead DH)
    { toFun := fun z => β.symm z
      map_add' := map_add _
      map_smul' := fun r z => by
        show β.symm (headToQ DH r * z) = DH.canonicalMap r * β.symm z
        have hr : β.symm (headToQ DH r) = DH.canonicalMap r := by
          rw [← headLocEquiv_canonicalMap ϖ hK₀ DH hDH r, hβ]
          exact β.symm_apply_apply _
        rw [map_mul β.symm, hr]
      invFun := fun y => β y
      left_inv := fun z => β.apply_symm_apply z
      right_inv := fun y => β.symm_apply_apply y }

end WeightedParity
