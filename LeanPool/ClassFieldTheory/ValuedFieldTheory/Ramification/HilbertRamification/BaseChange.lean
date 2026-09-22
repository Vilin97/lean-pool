/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ResidueField
/-!
# Conjugation and base change

This file proves functoriality of the decomposition, inertia, and
ramification groups under a commutative square of field embeddings.  Only
normality of the lower extension is needed to restrict conjugation to its
Galois group.  The decomposition statement for absolute values includes
the archimedean case; the valuation-subring statements give the three
nonarchimedean homomorphisms.
-/

noncomputable section

universe u v u' v'

namespace HilbertRamification

open AlgebraicNumberTheory.Valuations
open scoped Pointwise

variable {K : Type u} {L : Type v} {K' : Type u'} {L' : Type v'}
variable [Field K] [Field L] [Field K'] [Field L']
variable [Algebra K L] [Algebra K' L']

section GaloisPullback

variable (tauK : K →+* K') (tauL : L →+* L')
variable (hsquare : tauL.comp (algebraMap K L) =
  (algebraMap K' L').comp tauK)
variable [Normal K L]

include hsquare in
private def galoisPullbackElement (sigma : L' ≃ₐ[K'] L') : L ≃ₐ[K] L := by
  letI : Algebra K K' := tauK.toAlgebra
  letI : Algebra K L' := ((algebraMap K' L').comp tauK).toAlgebra
  letI : Algebra L L' := tauL.toAlgebra
  letI : IsScalarTower K K' L' :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K L L' :=
    IsScalarTower.of_algebraMap_eq' (by
      simpa only [RingHom.algebraMap_toAlgebra] using hsquare.symm)
  let tauLK : L →ₐ[K] L' :=
    { tauL with
      commutes' := fun x => by
        exact (congrFun (RingHom.coe_coe tauL) _).trans
          (DFunLike.congr_fun hsquare x) }
  exact
    Normal.algHomEquivAut K L' L
      ((sigma.restrictScalars K).toAlgHom.comp
        tauLK)

private theorem galoisPullbackElement_commutes
    (sigma : L' ≃ₐ[K'] L') (x : L) :
    tauL (galoisPullbackElement tauK tauL hsquare sigma x) =
      sigma (tauL x) := by
  let : Algebra K K' := tauK.toAlgebra
  let : Algebra K L' := ((algebraMap K' L').comp tauK).toAlgebra
  let : Algebra L L' := tauL.toAlgebra
  let : IsScalarTower K K' L' :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K L L' :=
    IsScalarTower.of_algebraMap_eq' (by
      simpa only [RingHom.algebraMap_toAlgebra] using hsquare.symm)
  let tauLK : L →ₐ[K] L' :=
    { tauL with
      commutes' := fun y => by
        exact (congrFun (RingHom.coe_coe tauL) _).trans
          (DFunLike.congr_fun hsquare y) }
  change algebraMap L L'
      (galoisPullbackElement tauK tauL hsquare sigma x) = _
  change algebraMap L L'
      ((((sigma.restrictScalars K).toAlgHom.comp tauLK).restrictNormal' L) x) = _
  rw [show
      (((sigma.restrictScalars K).toAlgHom.comp tauLK).restrictNormal' L) x =
        (((sigma.restrictScalars K).toAlgHom.comp tauLK).restrictNormal L) x by
      apply congrFun
      exact AlgEquiv.coe_ofBijective _ _]
  rw [AlgHom.restrictNormal_commutes]
  rfl

include hsquare in
/-- The conjugation and base-change law: conjugation along a commutative
square restricts to a homomorphism on Galois groups. -/
def galoisPullbackGaloisPullback : (L' ≃ₐ[K'] L') →* (L ≃ₐ[K] L) where
  toFun := galoisPullbackElement tauK tauL hsquare
  map_one' := by
    ext x
    apply tauL.injective
    rw [galoisPullbackElement_commutes]
    simp
  map_mul' sigma rho := by
    ext x
    apply tauL.injective
    rw [galoisPullbackElement_commutes]
    change sigma (rho (tauL x)) =
      tauL (galoisPullbackElement tauK tauL hsquare sigma
        (galoisPullbackElement tauK tauL hsquare rho x))
    rw [galoisPullbackElement_commutes, galoisPullbackElement_commutes]

/-- The defining equation `tauL (tau^* sigma x) = sigma (tauL x)`. -/
@[simp] theorem galoisPullback_galoisPullback_commutes
    (sigma : L' ≃ₐ[K'] L') (x : L) :
    tauL (galoisPullbackGaloisPullback tauK tauL hsquare sigma x) =
      sigma (tauL x) :=
  galoisPullbackElement_commutes tauK tauL hsquare sigma x

include hsquare in
/-- The conjugation and base-change law, including the archimedean case: the pullback on Galois
groups sends the decomposition group of `w'` to the decomposition group of
the pulled-back absolute value. -/
def galoisPullbackAbsoluteValueDecompositionGroupMap (w' : AbsoluteValue L' ℝ) :
    absoluteValueDecompositionGroup K' w' →*
      absoluteValueDecompositionGroup K (w'.comp (f := tauL) tauL.injective) where
  toFun sigma :=
    ⟨galoisPullbackGaloisPullback tauK tauL hsquare (sigma : L' ≃ₐ[K'] L'), by
      intro x
      change w' (tauL
          (galoisPullbackGaloisPullback tauK tauL hsquare
            (sigma : L' ≃ₐ[K'] L') x)) < 1 ↔
        w' (tauL x) < 1
      rw [galoisPullback_galoisPullback_commutes]
      exact sigma.property (tauL x)⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (galoisPullbackGaloisPullback tauK tauL hsquare)
  map_mul' sigma rho := by
    apply Subtype.ext
    exact map_mul (galoisPullbackGaloisPullback tauK tauL hsquare)
      (sigma : L' ≃ₐ[K'] L') (rho : L' ≃ₐ[K'] L')

namespace ValuationSubring

open RamificationTheory.HilbertRamification.ValuationSubring

variable (A' : _root_.ValuationSubring L')

private abbrev pulledValuationSubring : _root_.ValuationSubring L :=
  A'.comap tauL

private theorem mem_nonunits_pulled_iff (x : L) :
    x ∈ (pulledValuationSubring tauL A').nonunits ↔
      tauL x ∈ A'.nonunits := by
  rw [_root_.ValuationSubring.mem_nonunits_iff_or,
    _root_.ValuationSubring.mem_nonunits_iff_or]
  constructor
  · rintro (rfl | hx)
    · exact Or.inl (map_zero tauL)
    · exact Or.inr (by
        simpa only [map_inv₀, _root_.ValuationSubring.mem_comap] using hx)
  · rintro (hx | hx)
    · exact Or.inl (tauL.injective (by simpa using hx))
    · exact Or.inr (by
        simpa only [map_inv₀, _root_.ValuationSubring.mem_comap] using hx)

private theorem units_map_mem_principalUnitGroup_iff (x : Lˣ) :
    Units.map tauL x ∈ A'.principalUnitGroup ↔
      x ∈ (pulledValuationSubring tauL A').principalUnitGroup := by
  rw [_root_.ValuationSubring.mem_principalUnitGroup_iff,
    _root_.ValuationSubring.mem_principalUnitGroup_iff]
  have h := (mem_nonunits_pulled_iff tauL A' ((x : L) - 1)).symm
  have hcoe :
      (↑(Units.map (tauL : L →* L') x) : L') = tauL (x : L) :=
    (Units.coe_map (tauL : L →* L') x).trans
      (congrFun (RingHom.coe_coe tauL) _)
  rw [hcoe]
  simpa only [_root_.ValuationSubring.mem_nonunits_iff, map_sub, map_one] using h

private theorem mem_inertiaGroup_iff_sub_mem_nonunits
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : _root_.ValuationSubring E) (sigma : decompositionGroup F A) :
    sigma ∈ inertiaGroup F A ↔
      ∀ x : A,
        ((sigma : E ≃ₐ[F] E) (x : E) - (x : E)) ∈ A.nonunits := by
  change residueAction F A sigma = 1 ↔ _
  constructor
  · intro hsigma x
    have happ := congrArg
      (fun e : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A =>
        e (IsLocalRing.residue A x)) hsigma
    change sigma • (IsLocalRing.residue A x) =
      IsLocalRing.residue A x at happ
    rw [← IsLocalRing.ResidueField.residue_smul,
      ValuationTheory.DiscreteValuationField.ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal]
      at happ
    exact A.coe_mem_nonunits_iff.mpr happ
  · intro hsigma
    apply RingEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    change sigma • (IsLocalRing.residue A x) =
      IsLocalRing.residue A x
    rw [← IsLocalRing.ResidueField.residue_smul,
      ValuationTheory.DiscreteValuationField.ResidueField.residue_eq_residue_iff_sub_mem_maximalIdeal]
    exact A.coe_mem_nonunits_iff.mp (hsigma x)

include hsquare in
/-- The conjugation and base-change law in the valuation-subring model: decomposition groups map
under pullback along the commutative square. -/
def galoisPullbackDecompositionGroupMap :
    decompositionGroup K' A' →*
      decompositionGroup K (pulledValuationSubring tauL A') where
  toFun sigma :=
    ⟨galoisPullbackGaloisPullback tauK tauL hsquare (sigma : L' ≃ₐ[K'] L'), by
      ext x
      rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      change tauL
          ((galoisPullbackGaloisPullback tauK tauL hsquare
            (sigma : L' ≃ₐ[K'] L'))⁻¹ x) ∈ A' ↔
        tauL x ∈ A'
      have hinv := galoisPullback_galoisPullback_commutes
        tauK tauL hsquare ((sigma : L' ≃ₐ[K'] L')⁻¹) x
      rw [← map_inv, hinv]
      have hsigma : (sigma : L' ≃ₐ[K'] L') • A' = A' := sigma.property
      have hmem :=
        congrArg (fun B : _root_.ValuationSubring L' => tauL x ∈ B) hsigma
      simp only [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
        AlgEquiv.smul_def] at hmem
      exact ⟨fun h => hmem.mp h, fun h => hmem.symm.mp h⟩⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (galoisPullbackGaloisPullback tauK tauL hsquare)
  map_mul' sigma rho := by
    apply Subtype.ext
    exact map_mul (galoisPullbackGaloisPullback tauK tauL hsquare)
      (sigma : L' ≃ₐ[K'] L') (rho : L' ≃ₐ[K'] L')

private theorem decompositionGroupMap_commutes
    (sigma : decompositionGroup K' A') (x : L) :
    tauL ((((galoisPullbackDecompositionGroupMap tauK tauL hsquare A' sigma :
      decompositionGroup K (pulledValuationSubring tauL A')) :
        L ≃ₐ[K] L) x)) =
      (sigma : L' ≃ₐ[K'] L') (tauL x) :=
  galoisPullback_galoisPullback_commutes tauK tauL hsquare
    (sigma : L' ≃ₐ[K'] L') x

include hsquare in
/-- The conjugation and base-change law in the valuation-subring model: inertia groups map under
pullback along the commutative square. -/
def galoisPullbackInertiaGroupMap :
    inertiaGroup K' A' →*
      inertiaGroup K (pulledValuationSubring tauL A') where
  toFun sigma := by
    let delta := galoisPullbackDecompositionGroupMap tauK tauL hsquare A'
      (sigma : decompositionGroup K' A')
    refine ⟨delta, ?_⟩
    rw [mem_inertiaGroup_iff_sub_mem_nonunits]
    intro x
    rw [mem_nonunits_pulled_iff]
    rw [map_sub, decompositionGroupMap_commutes]
    exact (mem_inertiaGroup_iff_sub_mem_nonunits A'
      (sigma : decompositionGroup K' A')).mp sigma.property
      ⟨tauL (x : L), x.property⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (galoisPullbackDecompositionGroupMap tauK tauL hsquare A')
  map_mul' sigma rho := by
    apply Subtype.ext
    exact map_mul (galoisPullbackDecompositionGroupMap tauK tauL hsquare A')
      (sigma : decompositionGroup K' A') (rho : decompositionGroup K' A')

private theorem inertiaGroupMap_commutes
    (sigma : inertiaGroup K' A') (x : L) :
    tauL (((((galoisPullbackInertiaGroupMap tauK tauL hsquare A' sigma :
      inertiaGroup K (pulledValuationSubring tauL A')) :
        decompositionGroup K (pulledValuationSubring tauL A')) :
          L ≃ₐ[K] L) x)) =
      (((sigma : inertiaGroup K' A') : decompositionGroup K' A') :
        L' ≃ₐ[K'] L') (tauL x) := by
  simpa [galoisPullbackInertiaGroupMap] using
    decompositionGroupMap_commutes tauK tauL hsquare A'
      (sigma : decompositionGroup K' A') x

private theorem automorphismUnitQuotient_map
    (sigma : inertiaGroup K' A') (x : Lˣ) :
    Units.map tauL
        (automorphismUnitQuotient K (pulledValuationSubring tauL A')
          ((galoisPullbackInertiaGroupMap tauK tauL hsquare A' sigma :
            inertiaGroup K (pulledValuationSubring tauL A')) :
              decompositionGroup K (pulledValuationSubring tauL A')) x) =
      automorphismUnitQuotient K' A'
        (sigma : decompositionGroup K' A') (Units.map tauL x) := by
  ext
  simp [automorphismUnitQuotient, inertiaGroupMap_commutes]

private theorem ramificationPredicate_map
    (sigma : inertiaGroup K' A')
    (hsigma : ∀ y : L'ˣ,
      automorphismUnitQuotient K' A' (sigma : decompositionGroup K' A') y ∈
        A'.principalUnitGroup) :
    ∀ x : Lˣ,
    automorphismUnitQuotient K (pulledValuationSubring tauL A')
        ((galoisPullbackInertiaGroupMap tauK tauL hsquare A' sigma :
          inertiaGroup K (pulledValuationSubring tauL A')) :
            decompositionGroup K (pulledValuationSubring tauL A')) x ∈
      (pulledValuationSubring tauL A').principalUnitGroup := by
  intro x
  specialize hsigma (Units.map tauL x)
  rw [← units_map_mem_principalUnitGroup_iff tauL A']
  rw [automorphismUnitQuotient_map]
  exact hsigma

include hsquare in
/-- The conjugation and base-change law in the valuation-subring model: ramification groups map
under pullback along the commutative square. -/
def galoisPullbackRamificationGroupMap :
    ramificationGroup K' A' →*
      ramificationGroup K (pulledValuationSubring tauL A') :=
  ((galoisPullbackInertiaGroupMap tauK tauL hsquare A').domRestrict
      (ramificationGroup K' A')).codRestrict
    (ramificationGroup K (pulledValuationSubring tauL A'))
    (fun sigma => by
      change ∀ x : Lˣ,
        automorphismUnitQuotient K (pulledValuationSubring tauL A')
            ((galoisPullbackInertiaGroupMap tauK tauL hsquare A'
              (sigma : inertiaGroup K' A') :
                inertiaGroup K (pulledValuationSubring tauL A')) :
                  decompositionGroup K (pulledValuationSubring tauL A')) x ∈
          (pulledValuationSubring tauL A').principalUnitGroup
      apply ramificationPredicate_map tauK tauL hsquare A'
      have hsigma := sigma.property
      change ∀ y : L'ˣ,
        automorphismUnitQuotient K' A'
            ((sigma : inertiaGroup K' A') : decompositionGroup K' A') y ∈
          A'.principalUnitGroup at hsigma
      exact hsigma)

end ValuationSubring

end GaloisPullback

end HilbertRamification

end
