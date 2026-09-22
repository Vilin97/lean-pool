/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.MaximalResidue
/-!
# Lifting separable residue elements to unramified extensions

The reverse residue-field inclusion in the maximal-residue theorem is the Hensel step
from the residue-lifting argument: lift the minimal polynomial of a separable ambient residue
element, then lift its simple linear factor over the ambient valuation ring.
-/

noncomputable section

universe u

namespace AlgebraicNumberTheory
namespace Valuations

section SeparableResidueLift

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
variable [Algebra.IsAlgebraic K L]

/-- A separable ambient residue element is the residue of an actual root of
a monic lift of its base minimal polynomial. -/
theorem exists_integral_root_lifting_separable_residue_element
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    let k := IsLocalRing.ResidueField V
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
    ∀ alpha : ell, IsSeparable k alpha →
    ∃ F : Polynomial V,
      ∃ beta : W,
        F.Monic ∧
          F.map (IsLocalRing.residue V) = minpoly k alpha ∧
          (F.map ((algebraMap K L).comp
            V.subtype)).eval (beta : L) = 0 ∧
          IsLocalRing.residue W beta = alpha := by
  classical
  simp only
  intro alpha halpha
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
  let fbar : Polynomial k := minpoly k alpha
  have hfbarMonic : fbar.Monic := minpoly.monic halpha.isIntegral
  have hfbarSep : fbar.Separable := halpha
  have hlifts : fbar ∈ Polynomial.lifts (IsLocalRing.residue V) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact IsLocalRing.residue_surjective (fbar.coeff n)
  obtain ⟨F, hFmap, _hFdegree, hFmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts hfbarMonic
  let FW : Polynomial W := F.map i
  let pbar : Polynomial ell := fbar.map (algebraMap k ell)
  have hFWmonic : FW.Monic := hFmonic.map i
  have hFWmap : FW.map (IsLocalRing.residue W) = pbar := by
    have hred := unramifiedValuationRing_polynomial_target_reduction_eq
      v w hExt F
    change (F.map i).map (IsLocalRing.residue W) =
      (F.map (IsLocalRing.residue V)).map (algebraMap k ell) at hred
    rw [hred, hFmap]
  have hpbarMonic : pbar.Monic := hfbarMonic.map (algebraMap k ell)
  have hpbarSep : pbar.Separable := hfbarSep.map
  have hpbarRoot : pbar.eval alpha = 0 := by
    have hroot := minpoly.aeval k alpha
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hroot
    exact hroot
  have hpbarDerivative : pbar.derivative.eval alpha ≠ 0 := by
    exact hpbarSep.eval₂_derivative_ne_zero (RingHom.id ell) (by
      simpa using hpbarRoot)
  let gbar : Polynomial ell := Polynomial.X - Polynomial.C alpha
  let hbar : Polynomial ell := pbar /ₘ gbar
  have hgbarMonic : gbar.Monic := Polynomial.monic_X_sub_C alpha
  have hfactor : pbar = gbar * hbar := by
    have hdivision :=
      Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic pbar alpha
    have hmod : pbar %ₘ (Polynomial.X - Polynomial.C alpha) = 0 := by
      rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, hpbarRoot,
        Polynomial.C_0]
    rw [hmod, sub_zero] at hdivision
    simpa [gbar, hbar] using hdivision.symm
  have hhbarMonic : hbar.Monic := by
    exact hgbarMonic.of_mul_monic_left (hfactor ▸ hpbarMonic)
  have hcoprime : IsCoprime gbar hbar := by
    exact Polynomial.isCoprime_of_is_root_of_eval_derivative_ne_zero
      pbar alpha hpbarDerivative

  have hHenselianW : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w).valuation :=
    henselianValuation_of_algebraic_extension v w hExt hhens
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  have hfactorization : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty Wv := by
    change ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      Wv.valuation.valuationSubring at hHenselianW
    rw [ValuationSubring.valuationSubring_valuation] at hHenselianW
    exact hHenselianW
  have hlift : DiscreteValuationField.MonicResidualCoprimeFactorLifting Wv :=
    DiscreteValuationField.monicResidualCoprimeFactorLifting_of_henselFactorization
      hfactorization
  have hFWfactor : FW.map (IsLocalRing.residue W) = gbar * hbar :=
    hFWmap.trans hfactor
  rcases hlift hFWmonic hgbarMonic hhbarMonic hFWfactor hcoprime with
    ⟨G, H, hGmonic, _hHmonic, hGH, hGmap, _hHmap⟩
  have hGdegree : G.natDegree = 1 := by
    calc
      G.natDegree = (G.map (IsLocalRing.residue W)).natDegree :=
        (hGmonic.natDegree_map (IsLocalRing.residue W)).symm
      _ = gbar.natDegree := congrArg Polynomial.natDegree hGmap
      _ = 1 := Polynomial.natDegree_X_sub_C alpha
  let betaV : Wv := -G.coeff 0
  let beta : W := ⟨betaV.1, betaV.2⟩
  have hGform : G = Polynomial.X - Polynomial.C betaV := by
    simpa [betaV, sub_eq_add_neg] using hGmonic.eq_X_add_C hGdegree
  have hbetaResidue : IsLocalRing.residue W beta = alpha := by
    have hcoeff := congrArg (fun P ↦ P.coeff 0) hGmap
    rw [Polynomial.coeff_map] at hcoeff
    have hC : (Polynomial.C alpha : Polynomial ell).coeff 0 = alpha :=
      Polynomial.coeff_C_zero
    have hg0 : gbar.coeff 0 = -alpha := by
      rw [show gbar = Polynomial.X - Polynomial.C alpha from rfl,
        Polynomial.coeff_sub, Polynomial.coeff_X_zero, hC, zero_sub]
    have hcoeffNeg := hcoeff.trans hg0
    let coeffW : W := ⟨G.coeff 0, (G.coeff 0).property⟩
    have hresCoeff :
        IsLocalRing.residue W coeffW =
          IsLocalRing.residue Wv (G.coeff 0) := by
      rfl
    have hcoeffWNeg :
        IsLocalRing.residue W coeffW = -alpha :=
      hresCoeff.trans hcoeffNeg
    calc
      IsLocalRing.residue W beta =
          -(IsLocalRing.residue W coeffW) := by rfl
      _ = -(-alpha) := congrArg Neg.neg hcoeffWNeg
      _ = alpha := neg_neg alpha
  have hbetaRootV : (G * H).IsRoot betaV := by
    apply Polynomial.dvd_iff_isRoot.mp
    refine ⟨H, ?_⟩
    rw [hGform]
  have hbetaRootL :
      (F.map ((algebraMap K L).comp V.subtype)).eval (beta : L) = 0 := by
    change (F.map ((algebraMap K L).comp V.subtype)).eval (betaV : L) = 0
    have hpoly :
        F.map ((algebraMap K L).comp V.subtype) =
          (G * H).map Wv.subtype := by
      apply Polynomial.ext
      intro n
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      calc
        (algebraMap K L) ↑(F.coeff n) =
            Wv.subtype (show Wv from FW.coeff n) := by
          rw [show FW.coeff n = i (F.coeff n) by
            simp [FW]]
          exact (unramifiedValuationRingValuationRingMap_apply
            v w hExt (F.coeff n)).symm
        _ = Wv.subtype ((G * H).coeff n) := by
          exact congrArg Wv.subtype
            (congrArg (fun P : Polynomial Wv => P.coeff n) hGH)
    rw [hpoly]
    calc
      _ = Wv.subtype ((G * H).eval betaV) :=
        Polynomial.eval_map_apply Wv.subtype betaV
      _ = Wv.subtype 0 := congrArg Wv.subtype hbetaRootV
      _ = 0 := map_zero Wv.subtype
  exact ⟨F, beta, hFmonic, hFmap, hbetaRootL, hbetaResidue⟩

/-- The lifted root generates a concrete finite unramified subextension whose
residue image is the prescribed separable ambient residue element. -/
theorem exists_finiteUnramifiedSubextension_residue_image_eq
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    let k := IsLocalRing.ResidueField V
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
    ∀ alpha : ell, IsSeparable k alpha →
      ∃ E : IntermediateField K L,
        ∃ z : IsLocalRing.ResidueField
          (LubinTate.Valuations.exponentialValuationSubring
            (exponentialValuationRestrict w E)),
          FiniteUnramifiedSubextension v w hExt E ∧
            restrictedResidueAlgHomToAmbient v w hExt E z = alpha := by
  classical
  simp only
  intro alpha halpha
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
  obtain ⟨F, beta, hFmonic, hFmap, hFroot, hbetaResidue⟩ :=
    exists_integral_root_lifting_separable_residue_element
      v w hExt hhens alpha halpha

  let pK : Polynomial K := F.map V.subtype
  have hpKmonic : pK.Monic := hFmonic.map V.subtype
  have hpKroot : Polynomial.aeval (beta : L) pK = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    have hpoly : pK.map (algebraMap K L) =
        F.map ((algebraMap K L).comp V.subtype) := by
      rw [Polynomial.map_map]
    rw [hpoly]
    exact hFroot
  have hbetaIntegral : IsIntegral K (beta : L) :=
    ⟨pK, hpKmonic, hpKroot⟩
  let E : IntermediateField K L :=
    IntermediateField.adjoin K ({(beta : L)} : Set L)
  let hfinE : FiniteDimensional K E := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    have hx' : x = (beta : L) := by simpa using hx
    subst x
    exact hbetaIntegral
  let : FiniteDimensional K E := hfinE
  let wE := exponentialValuationRestrict w E
  let hKE := exponentialValuationRestrict_extends v w hExt E
  let betaE : LubinTate.Valuations.exponentialValuationSubring wE :=
    ⟨⟨(beta : L), IntermediateField.subset_adjoin K
      ({(beta : L)} : Set L) (Set.mem_singleton (beta : L))⟩,
      beta.property⟩
  have hFrootE :
      (F.map ((algebraMap K E).comp V.subtype)).eval (betaE : E) = 0 := by
    apply E.val.injective
    rw [← Polynomial.eval_map_apply]
    have hpoly :
        (F.map ((algebraMap K E).comp V.subtype)).map E.val.toRingHom =
          F.map ((algebraMap K L).comp V.subtype) := by
      rw [Polynomial.map_map]
      apply Polynomial.ext
      intro n
      rfl
    rw [hpoly]
    simp only [map_zero]
    exact hFroot
  have hFreduction :
      (F.map (IsLocalRing.residue V)).Separable := by
    rw [hFmap]
    exact halpha
  have hGenIF :
      IntermediateField.adjoin K ({(betaE : E)} : Set E) = ⊤ := by
    have hmapTop : IntermediateField.map E.val ⊤ = E := by
      ext x
      constructor
      · rintro ⟨y, _hy, rfl⟩
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, by trivial, rfl⟩
    apply IntermediateField.map_injective E.val
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    change IntermediateField.adjoin K ({(beta : L)} : Set L) =
      IntermediateField.map E.val ⊤
    change E = IntermediateField.map E.val ⊤
    exact hmapTop.symm
  have hGen : Algebra.adjoin K ({(betaE : E)} : Set E) = ⊤ := by
    apply Algebra.adjoin_eq_top_of_intermediateField
      (fun x _hx ↦ Algebra.IsAlgebraic.isAlgebraic x)
    exact hGenIF
  have hEfinite : FiniteUnramifiedExtension v wE hKE :=
    finiteUnramifiedExtension_of_primitive_separable_integral_model
      v wE hKE hhens betaE F hFmonic hFrootE hFreduction hGen
  let VE := LubinTate.Valuations.exponentialValuationSubring wE
  let z := IsLocalRing.residue VE betaE
  refine ⟨E, z, ⟨hfinE, hEfinite⟩, ?_⟩
  change IsLocalRing.residue W beta = alpha
  exact hbetaResidue

/-- the maximal-residue theorem, reverse residue-field inclusion: every ambient residue
element separable over the base occurs already in the residue field of the
maximal unramified subextension. -/
theorem separableClosure_le_maximalUnramifiedSubextension_residue_fieldRange
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    let T := maximalUnramifiedSubextension v w hExt
    let wT := exponentialValuationRestrict w T
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let VT := LubinTate.Valuations.exponentialValuationSubring wT
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v wT
      (exponentialValuationRestrict_extends v w hExt T)
    let b := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v wT
        (exponentialValuationRestrict_extends v w hExt T)
    letI : IsLocalHom b :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    let k := IsLocalRing.ResidueField V
    let kT := IsLocalRing.ResidueField VT
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k kT := (IsLocalRing.ResidueField.map i).toAlgebra
    letI : Algebra k ell := (IsLocalRing.ResidueField.map b).toAlgebra
    separableClosure k ell ≤
      (restrictedResidueAlgHomToAmbient v w hExt T).fieldRange := by
  classical
  simp only
  intro alpha halpha
  let T := maximalUnramifiedSubextension v w hExt
  let wT := exponentialValuationRestrict w T
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let VT := LubinTate.Valuations.exponentialValuationSubring wT
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let b := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom b :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map b).toAlgebra
  have hsep : IsSeparable k alpha :=
    mem_separableClosure_iff.mp halpha
  obtain ⟨E, z, hEunramified, hz⟩ :=
    exists_finiteUnramifiedSubextension_residue_image_eq
      v w hExt hhens alpha hsep
  have hET : E ≤ T :=
    finiteUnramifiedSubextension_le_maximal v w hExt hEunramified
  let wE := exponentialValuationRestrict w E
  let VE := LubinTate.Valuations.exponentialValuationSubring wE
  obtain ⟨e, rfl⟩ := IsLocalRing.residue_surjective z
  let eT : VT := restrictedValuationRingMapOfLE w hET e
  let zT := IsLocalRing.residue VT eT
  refine ⟨zT, ?_⟩
  calc
    restrictedResidueAlgHomToAmbient v w hExt T zT =
        restrictedResidueAlgHomToAmbient v w hExt E
          (IsLocalRing.residue VE e) := by rfl
    _ = alpha := hz

/-- Exact residue-field identity for the lifted unramified extension. -/
theorem maximalUnramifiedSubextension_residue_fieldRange_eq_separableClosure
    (v : LubinTate.Valuations.ExponentialValuation K) (w :
      LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation) :
    let T := maximalUnramifiedSubextension v w hExt
    let wT := exponentialValuationRestrict w T
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let VT := LubinTate.Valuations.exponentialValuationSubring wT
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v wT
      (exponentialValuationRestrict_extends v w hExt T)
    let b := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v wT
        (exponentialValuationRestrict_extends v w hExt T)
    letI : IsLocalHom b :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    let k := IsLocalRing.ResidueField V
    let kT := IsLocalRing.ResidueField VT
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k kT := (IsLocalRing.ResidueField.map i).toAlgebra
    letI : Algebra k ell := (IsLocalRing.ResidueField.map b).toAlgebra
    (restrictedResidueAlgHomToAmbient v w hExt T).fieldRange =
      separableClosure k ell := by
  apply le_antisymm
  · exact
      maximalUnramifiedSubextension_residue_fieldRange_le_separableClosure
        v w hExt hhens
  · exact
      separableClosure_le_maximalUnramifiedSubextension_residue_fieldRange
        v w hExt hhens

end SeparableResidueLift

end Valuations
end AlgebraicNumberTheory

end
