/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.HenselReduction
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.Separable
/-!
# the unramified base-change theorem: primitive Hensel base-change core

This file proves the polynomial core of the unramified base-change argument.  A
primitive integral generator whose monic model has separable reduction gives
a finite unramified extension.  The proof takes the actual integral minimal
polynomial, proves its reduction irreducible by Hensel's lemma, and compares
the resulting residue subfield degree with the fundamental inequality.
-/

@[expose] public section

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-! The private core retains both conclusions produced by the same degree
comparison: finite unramifiedness and generation of the target residue field
by the supplied generator's residue. -/
private theorem primitive_separable_integral_model_core
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (a : LubinTate.Valuations.exponentialValuationSubring w)
    (F : (LubinTate.Valuations.exponentialValuationSubring v)[X])
    (hFmonic : F.Monic)
    (hFroot :
      (F.map ((algebraMap K L).comp
        (LubinTate.Valuations.exponentialValuationSubring v).subtype)).eval (a : L) = 0)
    (hFreduction :
      (F.map (IsLocalRing.residue
        (LubinTate.Valuations.exponentialValuationSubring v))).Separable)
    (haGen : Algebra.adjoin K ({(a : L)} : Set L) = ⊤) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    letI : Algebra V W := i.toAlgebra
    letI : Algebra (IsLocalRing.ResidueField V)
        (IsLocalRing.ResidueField W) :=
      (IsLocalRing.ResidueField.map i).toAlgebra
    FiniteUnramifiedExtension v w hExt ∧
      IntermediateField.adjoin (IsLocalRing.ResidueField V)
          ({IsLocalRing.residue W a} :
            Set (IsLocalRing.ResidueField W)) = ⊤ := by
  classical
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let algVW : Algebra V W := i.toAlgebra
  let : Algebra V W := algVW
  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : SMul V L := algVL.toSMul
  let : SMul V W := algVW.toSMul
  let : Module V L := algVL.toModule
  let : Module V W := algVW.toModule
  let : IsScalarTower V K L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := K) (A := L) (by intro; rfl)
  let : IsScalarTower V W L := IsScalarTower.of_algebraMap_eq
    (R := V) (S := W) (A := L) (by intro; rfl)
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
  let : IsFractionRing V K := by
    change IsFractionRing Vv K
    have hfr : IsFractionRing Vv.valuation.valuationSubring K :=
      (Valuation.valuationSubring.integers
        (v := Vv.valuation)).isFractionRing
    rw [Vv.valuationSubring_valuation] at hfr
    exact hfr
  let : IsIntegrallyClosed V := by
    change IsIntegrallyClosed Vv
    infer_instance
  let : Module.IsTorsionFree V L :=
    Module.IsTorsionFree.trans_faithfulSMul V K L
  have haIntegralV : IsIntegral V (a : L) := by
    refine ⟨F, hFmonic, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map]
    change
      (F.map ((algebraMap K L).comp V.subtype)).eval (a : L) = 0
    exact hFroot
  have haIntegralK : IsIntegral K (a : L) :=
    Algebra.IsIntegral.isIntegral (R := K) (a : L)
  let G : V[X] := minpoly V (a : L)
  let qbar : k[X] := G.map (IsLocalRing.residue V)
  have hGmonic : G.Monic := minpoly.monic haIntegralV
  have hGfield : G.map (algebraMap V K) = minpoly K (a : L) := by
    exact (minpoly.isIntegrallyClosed_eq_field_fractions' K haIntegralV).symm
  have hGirreducible : Irreducible (G.map (algebraMap V K)) := by
    rw [hGfield]
    exact minpoly.irreducible haIntegralK
  have hGdvdF : G ∣ F := by
    apply minpoly.isIntegrallyClosed_dvd haIntegralV
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    change
      (F.map ((algebraMap K L).comp V.subtype)).eval (a : L) = 0
    exact hFroot
  have hqSep : qbar.Separable :=
    hFreduction.of_dvd (Polynomial.map_dvd (IsLocalRing.residue V) hGdvdF)
  have hhensV : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty Vv := by
    change ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      Vv.valuation.valuationSubring at hhens
    rw [Vv.valuationSubring_valuation] at hhens
    exact hhens
  have hqIrreducible : Irreducible qbar := by
    exact irreducible_residue_of_irreducible_of_separable_of_henselian
      Vv hhensV hGmonic hGirreducible hqSep
  have hGaW : Polynomial.aeval a G = 0 := by
    have hcompat :
        (algebraMap V L).comp (RingHom.id V) =
          W.subtype.comp (algebraMap V W) := by
      ext x
      rfl
    have hmap := Polynomial.map_aeval_eq_aeval_map
      hcompat G a
    have hmin : Polynomial.aeval (a : L) G = 0 :=
      minpoly.aeval V (a : L)
    apply W.subtype_injective
    change W.subtype (Polynomial.aeval a G) = W.subtype 0
    rw [hmap]
    simpa using hmin
  let alpha : ell := IsLocalRing.residue W a
  have hqRoot : Polynomial.aeval alpha qbar = 0 := by
    have hres := unramifiedValuationRing_polynomial_aeval_residue_eq v w hExt G a
    dsimp only at hres
    rw [hGaW, map_zero] at hres
    simpa [alpha, qbar, Polynomial.aeval_def] using hres.symm
  have hqMinpoly : qbar = minpoly k alpha :=
    minpoly.eq_of_irreducible_of_monic
      hqIrreducible hqRoot (hGmonic.map (IsLocalRing.residue V))
  have halphaSep : IsSeparable k alpha := by
    rw [IsSeparable, ← hqMinpoly]
    exact hqSep
  have halphaIntegral : IsIntegral k alpha := halphaSep.isIntegral
  have hfieldDegree :
      Module.finrank K L = (minpoly K (a : L)).natDegree := by
    have hAdjoin :
        IntermediateField.adjoin K ({(a : L)} : Set L) =
          (⊤ : IntermediateField K L) :=
      (IntermediateField.adjoin_eq_top_iff).2 haGen
    calc
      Module.finrank K L = Module.finrank K
          (IntermediateField.adjoin K ({(a : L)} : Set L)) := by
        rw [hAdjoin]
        simp
      _ = (minpoly K (a : L)).natDegree :=
        IntermediateField.adjoin.finrank haIntegralK
  have hqDegree : qbar.natDegree = Module.finrank K L := by
    calc
      qbar.natDegree = G.natDegree :=
        hGmonic.natDegree_map (IsLocalRing.residue V)
      _ = (G.map (algebraMap V K)).natDegree := by
        rw [Polynomial.natDegree_map_eq_of_injective
          (show Function.Injective (algebraMap V K) from
            IsFractionRing.injective V K)]
      _ = (minpoly K (a : L)).natDegree := by rw [hGfield]
      _ = Module.finrank K L := hfieldDegree.symm
  have hresfin : FiniteDimensional k ell :=
    residueExtension_finiteDimensional_of_finiteDimensional v w hExt
  let : FiniteDimensional k ell := hresfin
  let residueModule : Module k ell := inferInstance
  let algebraModule : Module k ell :=
    (inferInstance : Algebra k ell).toModule
  have hresidueModule : residueModule = algebraModule := by
    apply Module.ext
    funext r x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  have hresfinAlgebra :
      @FiniteDimensional k ell _ _ algebraModule := by
    rw [← hresidueModule]
    exact hresfin
  have hfinTopAlgebra :
      FiniteDimensional k (⊤ : IntermediateField k ell) :=
    @IntermediateField.finiteDimensional_left
      k ell _ _ _ (⊤ : IntermediateField k ell) hresfinAlgebra
  have hresidueSubDegree :
      Module.finrank k
          (IntermediateField.adjoin k ({alpha} : Set ell)) =
        Module.finrank K L := by
    rw [IntermediateField.adjoin.finrank halphaIntegral, ← hqMinpoly]
    exact hqDegree
  have hsuble :
      Module.finrank K L ≤ @Module.finrank k ell _ _ residueModule := by
    rw [← hresidueSubDegree, hresidueModule]
    simpa using (@IntermediateField.finrank_le_of_le_right k ell _ _ _
      (IntermediateField.adjoin k ({alpha} : Set ell))
      (⊤ : IntermediateField k ell) hfinTopAlgebra le_top)
  let : Finite (ExponentialValueGroupQuotient v w) :=
    exponentialValueGroupQuotient_finite_of_finiteDimensional v w hExt
  have hepos : 0 < exponentialRamificationIndex v w := by
    let : Nonempty (ExponentialValueGroupQuotient v w) :=
      ⟨QuotientAddGroup.mk (0 : exponentialValueSubgroup w)⟩
    rw [exponentialRamificationIndex]
    exact Nat.card_pos
  have hfundamental := ramificationInvariants_fundamental_inequality v w hExt
  have hresle :
      @Module.finrank k ell _ _ residueModule ≤ Module.finrank K L := by
    change exponentialResidueDegree v w hExt ≤ Module.finrank K L
    nlinarith
  have hdegreeEq :
      Module.finrank K L =
        @Module.finrank k ell _ _ residueModule :=
    Nat.le_antisymm hsuble hresle
  have hdegreeEqAlgebra :
      Module.finrank K L = @Module.finrank k ell _ _ algebraModule := by
    rwa [hresidueModule] at hdegreeEq
  have hAdjoinResidue :
      IntermediateField.adjoin k ({alpha} : Set ell) = ⊤ := by
    apply (@Field.primitive_element_iff_minpoly_natDegree_eq
      k ell _ _ _ hresfinAlgebra alpha).2
    rw [← hqMinpoly, hqDegree]
    exact hdegreeEqAlgebra
  have hsepEll : Algebra.IsSeparable k ell := by
    rw [← IntermediateField.isSeparable_top, ← hAdjoinResidue,
      IntermediateField.isSeparable_adjoin_iff_isSeparable]
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact halphaSep
  refine ⟨⟨?_, ?_⟩, hAdjoinResidue⟩
  · exact hsepEll
  · change Module.finrank K L =
      @Module.finrank k ell _ _ residueModule
    exact hdegreeEq

/-- Primitive-generator form of the finite base-change argument in
the unramified base-change theorem.

The data `a` and `F` are concrete outputs of the primitive residue lift for
the original unramified extension: `a` generates the field, `F` is a monic
integral polynomial vanishing at `a`, and its actual reduction is separable.
No unramified conclusion or degree comparison is assumed. -/
theorem finiteUnramifiedExtension_of_primitive_separable_integral_model
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (a : LubinTate.Valuations.exponentialValuationSubring w)
    (F : (LubinTate.Valuations.exponentialValuationSubring v)[X])
    (hFmonic : F.Monic)
    (hFroot :
      (F.map ((algebraMap K L).comp
        (LubinTate.Valuations.exponentialValuationSubring v).subtype)).eval (a : L) = 0)
    (hFreduction :
      (F.map (IsLocalRing.residue
        (LubinTate.Valuations.exponentialValuationSubring v))).Separable)
    (haGen : Algebra.adjoin K ({(a : L)} : Set L) = ⊤) :
    FiniteUnramifiedExtension v w hExt := by
  exact (primitive_separable_integral_model_core
    v w hExt hhens a F hFmonic hFroot hFreduction haGen).1

/-- the unramified base-change theorem, residue-generator endpoint for the primitive integral
model.

Under the same source hypotheses as the finite base-change criterion, the
residue of the supplied primitive generator generates the entire target
residue field over the base residue field. -/
theorem unramifiedBaseChange_residue_adjoin_eq_top_of_primitive_separable_integral_model
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (a : LubinTate.Valuations.exponentialValuationSubring w)
    (F : (LubinTate.Valuations.exponentialValuationSubring v)[X])
    (hFmonic : F.Monic)
    (hFroot :
      (F.map ((algebraMap K L).comp
        (LubinTate.Valuations.exponentialValuationSubring v).subtype)).eval (a : L) = 0)
    (hFreduction :
      (F.map (IsLocalRing.residue
        (LubinTate.Valuations.exponentialValuationSubring v))).Separable)
    (haGen : Algebra.adjoin K ({(a : L)} : Set L) = ⊤) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    letI : Algebra V W := i.toAlgebra
    letI : Algebra (IsLocalRing.ResidueField V)
        (IsLocalRing.ResidueField W) :=
      (IsLocalRing.ResidueField.map i).toAlgebra
    IntermediateField.adjoin (IsLocalRing.ResidueField V)
        ({IsLocalRing.residue W a} :
          Set (IsLocalRing.ResidueField W)) = ⊤ := by
  exact (primitive_separable_integral_model_core
    v w hExt hhens a F hFmonic hFroot hFreduction haGen).2

end Valuations
end AlgebraicNumberTheory

end
