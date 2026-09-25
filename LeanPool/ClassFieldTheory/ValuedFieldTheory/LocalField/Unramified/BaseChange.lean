/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.BaseChangeCore
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.Compositum
/-!
# A base-change polynomial model for unramified extensions

Let `L` and `K'` be intermediate fields of a common algebraic ambient field
`Ω`.  Starting from the primitive integral model of a finite unramified
extension `L/K`, this file maps its generator and polynomial to the actual
compositum `L ⊔ K'`.  The resulting data are exactly the inputs of the
primitive-separable integral-model criterion: generation over `K'`, a monic
polynomial vanishing at the mapped generator, and separable reduction.

No finite-dimensionality of `K'/K` is used.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations

open DiscreteValuationField.FieldCompositum

section RestrictedValuationMaps

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

/-- Inclusion of restricted valuation rings along an inclusion of ambient
intermediate fields. -/
def restrictedValuationRingMapOfLE
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    {E F : IntermediateField K Ω} (hEF : E ≤ F) :
    LubinTate.Valuations.exponentialValuationSubring
        (exponentialValuationRestrict w E) →+*
      LubinTate.Valuations.exponentialValuationSubring
        (exponentialValuationRestrict w F) :=
  (IntermediateField.inclusion hEF).toRingHom.restrict _ _ fun x hx ↦ by
    change (0 : WithTop ℝ) ≤ w (x : Ω)
    exact hx

@[simp]
theorem restrictedValuationRingMapOfLE_apply
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    {E F : IntermediateField K Ω} (hEF : E ≤ F)
    (x : LubinTate.Valuations.exponentialValuationSubring
      (exponentialValuationRestrict w E)) :
    ((restrictedValuationRingMapOfLE w hEF x :
      LubinTate.Valuations.exponentialValuationSubring
        (exponentialValuationRestrict w F)) : F) =
      IntermediateField.inclusion hEF (x : E) :=
  rfl

end RestrictedValuationMaps

section BaseChangeModel

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

/-! The private common-top core retains the source generator together with
its canonical image.  Public projections below expose both the original
primitive integral model and the residue-generator endpoint without
duplicating the base-change proof. -/
private theorem primitive_separable_integral_model_on_commonTop_core
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L]
    [Algebra.IsAlgebraic K K']
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    (hExt : ∀ a : K, w (algebraMap K Ω a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hUnramified : FiniteUnramifiedExtension v
      (exponentialValuationRestrict w L)
      (exponentialValuationRestrict_extends v w hExt L)) :
    let wLeft := exponentialValuationRestrict w L
    let wRight := exponentialValuationRestrict w K'
    let wTop := exponentialValuationRestrict w (L ⊔ K')
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight).valuation ∧
      (∀ a : K',
        wTop (algebraMap K' (L ⊔ K' : IntermediateField K Ω) a) =
          wRight a) ∧
        ∃ aLeft : LubinTate.Valuations.exponentialValuationSubring wLeft,
          ∃ aTop : LubinTate.Valuations.exponentialValuationSubring wTop,
            ∃ FRight : Polynomial (LubinTate.Valuations.exponentialValuationSubring wRight),
              aTop = restrictedValuationRingMapOfLE w
                  (show L ≤ (L ⊔ K' : IntermediateField K Ω) from le_sup_left)
                  aLeft ∧
                Algebra.adjoin K'
                ({(aTop : (L ⊔ K' : IntermediateField K Ω))} :
                  Set (L ⊔ K' : IntermediateField K Ω)) = ⊤ ∧
              FRight.Monic ∧
                (FRight.map
                  ((algebraMap K'
                    (L ⊔ K' : IntermediateField K Ω)).comp
                    (LubinTate.Valuations.exponentialValuationSubring wRight).subtype)).eval
                    (aTop : (L ⊔ K' : IntermediateField K Ω)) = 0 ∧
                  (FRight.map (IsLocalRing.residue
                    (LubinTate.Valuations.exponentialValuationSubring wRight))).Separable := by
  classical
  let wLeft := exponentialValuationRestrict w L
  let wRight := exponentialValuationRestrict w K'
  let wTop := exponentialValuationRestrict w (L ⊔ K')
  let hLeft : ∀ a : K, wLeft (algebraMap K L a) = v a :=
    exponentialValuationRestrict_extends v w hExt L
  let hRight : ∀ a : K, wRight (algebraMap K K' a) = v a :=
    exponentialValuationRestrict_extends v w hExt K'
  let hRightTop : ∀ a : K',
      wTop (algebraMap K' (L ⊔ K' : IntermediateField K Ω) a) =
        wRight a := by
    intro a
    rfl
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let WRight := LubinTate.Valuations.exponentialValuationSubring wRight
  let WTop := LubinTate.Valuations.exponentialValuationSubring wTop
  let iRight := unramifiedValuationRingValuationRingMap v wRight hRight
  let : IsLocalHom iRight :=
    unramifiedValuationRingValuationRingMap_isLocalHom v wRight hRight
  let k := IsLocalRing.ResidueField V
  let kRight := IsLocalRing.ResidueField WRight
  let : Algebra k kRight :=
    (IsLocalRing.ResidueField.map iRight).toAlgebra
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  have hhensRight :
      ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight).valuation :=
    henselianValuation_of_algebraic_extension
      v wRight hRight hhens
  obtain ⟨a, F, haGen, hFfield, _hFresidueMinpoly,
      hFreduction, _haSeparable⟩ :=
    exists_primitive_lift_minpoly_of_finiteUnramifiedExtension
      v wLeft hLeft hhens hUnramified
  let aTop : WTop :=
    restrictedValuationRingMapOfLE w
      (show L ≤ (L ⊔ K' : IntermediateField K Ω) from le_sup_left) a
  let FRight : Polynomial WRight := F.map iRight
  have haGenAlg :
      Algebra.adjoin K ({(a : L)} : Set L) =
        (⊤ : Subalgebra K L) := by
    exact Algebra.adjoin_eq_top_of_intermediateField
      (by intro x hx; exact Algebra.IsAlgebraic.isAlgebraic x) haGen
  have haTopGen :
      Algebra.adjoin K'
          ({(aTop : (L ⊔ K' : IntermediateField K Ω))} :
            Set (L ⊔ K' : IntermediateField K Ω)) = ⊤ := by
    simpa [aTop] using
      (sup_right_adjoin_left_singleton_eq_top_of_adjoin_eq_top
        (K := K) (Ω := Ω) L K' (a : L) haGenAlg)
  have hFRightMonic : FRight.Monic := by
    have hFmapMonic : (F.map V.subtype).Monic := by
      rw [hFfield]
      exact minpoly.monic (Algebra.IsIntegral.isIntegral (a : L))
    have hFMonic : F.Monic :=
      (V.subtype_injective.monic_map_iff (p := F)).2 hFmapMonic
    exact hFMonic.map iRight
  have hFrootLeft :
      (F.map ((algebraMap K L).comp V.subtype)).eval (a : L) = 0 := by
    have hmin : Polynomial.aeval (a : L) (minpoly K (a : L)) = 0 :=
      minpoly.aeval K (a : L)
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hmin
    have hpoly :
        F.map ((algebraMap K L).comp V.subtype) =
          (F.map V.subtype).map (algebraMap K L) := by
      rw [Polynomial.map_map]
    rw [hpoly, hFfield]
    exact hmin
  let iLeftTop : L →+* (L ⊔ K' : IntermediateField K Ω) :=
    (IntermediateField.inclusion
      (show L ≤ (L ⊔ K' : IntermediateField K Ω) from le_sup_left)).toRingHom
  have hFrootTopFromLeft :
      ((F.map ((algebraMap K L).comp V.subtype)).map iLeftTop).eval
          (aTop : (L ⊔ K' : IntermediateField K Ω)) = 0 := by
    change ((F.map ((algebraMap K L).comp V.subtype)).map iLeftTop).eval
      (iLeftTop (a : L)) = 0
    rw [Polynomial.eval_map_apply, hFrootLeft, map_zero]
  have hFmapTop :
      FRight.map
          ((algebraMap K' (L ⊔ K' : IntermediateField K Ω)).comp
            WRight.subtype) =
        (F.map ((algebraMap K L).comp V.subtype)).map iLeftTop := by
    apply Polynomial.ext
    intro n
    apply Subtype.ext
    simp only [Polynomial.coeff_map, RingHom.coe_comp, Subring.coe_subtype, Function.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, SubalgebraClass.coe_algebraMap,
      FRight, iRight, iLeftTop]
    rw [unramifiedValuationRingValuationRingMap_apply]
    change (((algebraMap K' (L ⊔ K' : IntermediateField K Ω))
        (algebraMap K K' (F.coeff n : K)) :
          (L ⊔ K' : IntermediateField K Ω)) : Ω) =
      algebraMap K Ω (F.coeff n : K)
    rw [← IsScalarTower.algebraMap_apply K K'
      (L ⊔ K' : IntermediateField K Ω)]
    rfl
  have hFRightRoot :
      (FRight.map
        ((algebraMap K' (L ⊔ K' : IntermediateField K Ω)).comp
          WRight.subtype)).eval
          (aTop : (L ⊔ K' : IntermediateField K Ω)) = 0 := by
    rw [hFmapTop]
    exact hFrootTopFromLeft
  have hFRightReduction :
      (FRight.map (IsLocalRing.residue WRight)).Separable := by
    have hReductionMap :=
      unramifiedValuationRing_polynomial_target_reduction_eq
        v wRight hRight F
    change (F.map iRight).map (IsLocalRing.residue WRight) =
        (F.map (IsLocalRing.residue V)).map (algebraMap k kRight)
      at hReductionMap
    rw [hReductionMap]
    exact hFreduction.map
  exact ⟨hhensRight, hRightTop, a, aTop, FRight, rfl, haTopGen,
    hFRightMonic, hFRightRoot, hFRightReduction⟩

/-- the unramified base-change theorem, concrete base-change model.

The original extension `L/K` is finite, but `K'/K` is only algebraic.  The
ambient valuation is restricted to `L`, `K'`, and `L ⊔ K'`.  The returned
generator and polynomial have the exact four properties required by the
primitive-separable integral-model criterion on the upper branch. -/
theorem exists_primitive_separable_integral_model_on_commonTop
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L]
    [Algebra.IsAlgebraic K K']
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    (hExt : ∀ a : K, w (algebraMap K Ω a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hUnramified : FiniteUnramifiedExtension v
      (exponentialValuationRestrict w L)
      (exponentialValuationRestrict_extends v w hExt L)) :
    let wRight := exponentialValuationRestrict w K'
    let wTop := exponentialValuationRestrict w (L ⊔ K')
    ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring wRight).valuation ∧
      (∀ a : K',
        wTop (algebraMap K' (L ⊔ K' : IntermediateField K Ω) a) =
          wRight a) ∧
        ∃ aTop : LubinTate.Valuations.exponentialValuationSubring wTop,
          ∃ FRight : Polynomial (LubinTate.Valuations.exponentialValuationSubring wRight),
            Algebra.adjoin K'
                ({(aTop : (L ⊔ K' : IntermediateField K Ω))} :
                  Set (L ⊔ K' : IntermediateField K Ω)) = ⊤ ∧
              FRight.Monic ∧
                (FRight.map
                  ((algebraMap K'
                    (L ⊔ K' : IntermediateField K Ω)).comp
                    (LubinTate.Valuations.exponentialValuationSubring wRight).subtype)).eval
                    (aTop : (L ⊔ K' : IntermediateField K Ω)) = 0 ∧
                  (FRight.map (IsLocalRing.residue
                    (LubinTate.Valuations.exponentialValuationSubring wRight))).Separable := by
  rcases primitive_separable_integral_model_on_commonTop_core
      L K' v w hExt hhens hUnramified with
    ⟨hhensRight, hRightTop, _aLeft, aTop, FRight, _haTop,
      haGen, hFmonic, hFroot, hFreduction⟩
  exact ⟨hhensRight, hRightTop, aTop, FRight, haGen,
    hFmonic, hFroot, hFreduction⟩

/-- the unramified base-change theorem, residue generator on the actual common top.

The primitive generator may be kept on the original unramified factor: its
canonical image in `L ⊔ K'` has residue generating the whole common-top
residue field over the residue field of `K'`. -/
theorem unramifiedBaseChange_exists_commonTop_residue_generator_from_left
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L]
    [Algebra.IsAlgebraic K K']
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    (hExt : ∀ a : K, w (algebraMap K Ω a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hUnramified : FiniteUnramifiedExtension v
      (exponentialValuationRestrict w L)
      (exponentialValuationRestrict_extends v w hExt L)) :
    let wLeft := exponentialValuationRestrict w L
    let wRight := exponentialValuationRestrict w K'
    let wTop := exponentialValuationRestrict w (L ⊔ K')
    let hRightTop : ∀ a : K',
        wTop (algebraMap K' (L ⊔ K' : IntermediateField K Ω) a) =
          wRight a := by intro a; rfl
    ∃ aLeft : LubinTate.Valuations.exponentialValuationSubring wLeft,
      ∃ aTop : LubinTate.Valuations.exponentialValuationSubring wTop,
        aTop = restrictedValuationRingMapOfLE w
            (show L ≤ (L ⊔ K' : IntermediateField K Ω) from le_sup_left)
            aLeft ∧
          (let i := unramifiedValuationRingValuationRingMap wRight wTop hRightTop
           letI : IsLocalHom i :=
             unramifiedValuationRingValuationRingMap_isLocalHom
               wRight wTop hRightTop
           letI : Algebra (LubinTate.Valuations.exponentialValuationSubring wRight)
               (LubinTate.Valuations.exponentialValuationSubring wTop) := i.toAlgebra
           letI : Algebra
               (IsLocalRing.ResidueField
                 (LubinTate.Valuations.exponentialValuationSubring wRight))
               (IsLocalRing.ResidueField
                 (LubinTate.Valuations.exponentialValuationSubring wTop)) :=
             (IsLocalRing.ResidueField.map i).toAlgebra
           IntermediateField.adjoin
               (IsLocalRing.ResidueField
                 (LubinTate.Valuations.exponentialValuationSubring wRight))
               ({IsLocalRing.residue
                   (LubinTate.Valuations.exponentialValuationSubring wTop) aTop} :
                 Set (IsLocalRing.ResidueField
                   (LubinTate.Valuations.exponentialValuationSubring wTop))) = ⊤) := by
  let wLeft := exponentialValuationRestrict w L
  let wRight := exponentialValuationRestrict w K'
  let wTop := exponentialValuationRestrict w (L ⊔ K')
  let hRightTop : ∀ a : K',
      wTop (algebraMap K' (L ⊔ K' : IntermediateField K Ω) a) =
        wRight a := by
    intro a
    rfl
  rcases primitive_separable_integral_model_on_commonTop_core
      L K' v w hExt hhens hUnramified with
    ⟨hhensRight, hRightTop', aLeft, aTop, FRight, haTop,
      haGen, hFmonic, hFroot, hFreduction⟩
  have hRightTopEq : hRightTop' = hRightTop := by
    funext a
    rfl
  subst hRightTop'
  refine ⟨aLeft, aTop, haTop, ?_⟩
  let : FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω) :=
    finiteDimensional_sup_over_right_of_left L K'
  exact
    unramifiedBaseChange_residue_adjoin_eq_top_of_primitive_separable_integral_model
      wRight wTop hRightTop hhensRight aTop FRight hFmonic hFroot
        hFreduction haGen

/-- Finite base-change endpoint for unramified extensions.

If `L/K` is finite unramified and `K'/K` is an arbitrary algebraic
intermediate extension in the common ambient field, then the actual
compositum `L ⊔ K'` is finite unramified over `K'` for the restricted ambient
valuation.  In particular, no finite-dimensionality hypothesis on `K'/K`
appears at the theorem boundary. -/
theorem finiteUnramifiedExtension_commonTop_of_baseChange
    (L K' : IntermediateField K Ω)
    [FiniteDimensional K L]
    [Algebra.IsAlgebraic K K']
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation Ω)
    (hExt : ∀ a : K, w (algebraMap K Ω a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hUnramified : FiniteUnramifiedExtension v
      (exponentialValuationRestrict w L)
      (exponentialValuationRestrict_extends v w hExt L)) :
    let wRight := exponentialValuationRestrict w K'
    let wTop := exponentialValuationRestrict w (L ⊔ K')
    let hRightTop : ∀ a : K',
        wTop (algebraMap K' (L ⊔ K' : IntermediateField K Ω) a) =
          wRight a := by intro a; rfl
    letI : FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω) :=
      finiteDimensional_sup_over_right_of_left L K'
    FiniteUnramifiedExtension wRight wTop hRightTop := by
  let wRight := exponentialValuationRestrict w K'
  let wTop := exponentialValuationRestrict w (L ⊔ K')
  let hRightTop : ∀ a : K',
      wTop (algebraMap K' (L ⊔ K' : IntermediateField K Ω) a) =
        wRight a := by
    intro a
    rfl
  let : FiniteDimensional K' (L ⊔ K' : IntermediateField K Ω) :=
    finiteDimensional_sup_over_right_of_left L K'
  rcases exists_primitive_separable_integral_model_on_commonTop
      L K' v w hExt hhens hUnramified with
    ⟨hhensRight, hRightTop', aTop, FRight, haGen,
      hFmonic, hFroot, hFreduction⟩
  have hRightTopEq : hRightTop' = hRightTop := by
    funext a
    rfl
  subst hRightTop'
  exact finiteUnramifiedExtension_of_primitive_separable_integral_model
    wRight wTop hRightTop hhensRight aTop FRight hFmonic hFroot
      hFreduction haGen

end BaseChangeModel

end Valuations
end AlgebraicNumberTheory

end
