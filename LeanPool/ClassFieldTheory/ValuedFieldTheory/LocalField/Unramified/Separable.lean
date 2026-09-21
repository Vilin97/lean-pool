/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.HenselianAlgebraicExtension
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.Unramified.BasicInvariants
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Adjoin.PowerBasis
/-!
# Separability sources for finite unramified extensions

A finite unramified extension of a Henselian valued field is separable.  The
proof follows the primitive-residue-element argument on p. 153: lift a
primitive generator of the separable residue extension, use the fundamental inequality
to show that its powers are a basis of the field extension, and compare its
minimal polynomial with its separable reduction.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

section ResiduePolynomial

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]

/-- Reducing a base valuation-ring polynomial after mapping it to the target
valuation ring agrees with first reducing it over the base residue field. -/
theorem unramifiedValuationRing_polynomial_target_reduction_eq
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (P : Polynomial (LubinTate.Valuations.exponentialValuationSubring v)) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    let k := IsLocalRing.ResidueField V
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
    (P.map i).map (IsLocalRing.residue W) =
      (P.map (IsLocalRing.residue V)).map (algebraMap k ell) := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
  ext n
  simp only [Polynomial.coeff_map]
  change IsLocalRing.residue W (i (P.coeff n)) =
    IsLocalRing.ResidueField.map i
      (IsLocalRing.residue V (P.coeff n))
  rfl

/-- Evaluation of a valuation-ring polynomial commutes with passage to the
actual residue fields. -/
theorem unramifiedValuationRing_polynomial_aeval_residue_eq
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (P : Polynomial (LubinTate.Valuations.exponentialValuationSubring v))
    (x : LubinTate.Valuations.exponentialValuationSubring w) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    letI : Algebra V W := i.toAlgebra
    let k := IsLocalRing.ResidueField V
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
    IsLocalRing.residue W (Polynomial.aeval x P) =
      ((P.map (IsLocalRing.residue V)).map (algebraMap k ell)).eval
        (IsLocalRing.residue W x) := by
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
  calc
    IsLocalRing.residue W (Polynomial.aeval x P) =
        ((P.map i).map (IsLocalRing.residue W)).eval
          (IsLocalRing.residue W x) := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact
        (Polynomial.eval_map_apply
          (f := IsLocalRing.residue W) (p := P.map i) x).symm
    _ = ((P.map (IsLocalRing.residue V)).map
          (algebraMap k ell)).eval (IsLocalRing.residue W x) := by
      rw [unramifiedValuationRing_polynomial_target_reduction_eq v w hExt P]

end ResiduePolynomial

section FiniteUnramifiedExtensionSeparability

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]

/-- Primitive-lift source for a finite unramified extension.

For a finite unramified extension, this constructs the lifted primitive
residue element used on p. 153 and its integral minimal polynomial.  The
element generates `L/K`; the polynomial becomes its field minimal polynomial
over `K`, and its residue is the separable minimal polynomial of the residue
class. -/
theorem exists_primitive_lift_minpoly_of_finiteUnramifiedExtension
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hUnramified : FiniteUnramifiedExtension v w hExt) :
    let V := LubinTate.Valuations.exponentialValuationSubring v
    let W := LubinTate.Valuations.exponentialValuationSubring w
    let i := unramifiedValuationRingValuationRingMap v w hExt
    letI : IsLocalHom i :=
      unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
    let k := IsLocalRing.ResidueField V
    let ell := IsLocalRing.ResidueField W
    letI : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
    ∃ a : W, ∃ F : Polynomial V,
      IntermediateField.adjoin K ({(a : L)} : Set L) = ⊤ ∧
        F.map V.subtype = minpoly K (a : L) ∧
          F.map (IsLocalRing.residue V) =
            minpoly k (IsLocalRing.residue W a) ∧
          (F.map (IsLocalRing.residue V)).Separable ∧
            IsSeparable K (a : L) := by
  classical
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let Vv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v
  let Wv := LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  let V := LubinTate.Valuations.exponentialValuationSubring v
  let W := LubinTate.Valuations.exponentialValuationSubring w
  let i := unramifiedValuationRingValuationRingMap v w hExt
  let : IsLocalHom i :=
    unramifiedValuationRingValuationRingMap_isLocalHom v w hExt
  let : Algebra V W := i.toAlgebra
  let k := IsLocalRing.ResidueField V
  let ell := IsLocalRing.ResidueField W
  let : Algebra k ell := (IsLocalRing.ResidueField.map i).toAlgebra
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
      @FiniteDimensional k ell _ _
        algebraModule := by
    rw [← hresidueModule]
    exact hresfin
  have hressep : Algebra.IsSeparable k ell :=
    finiteUnramifiedExtension_residue_isSeparable
      v w hExt hUnramified
  let : Algebra.IsSeparable k ell := hressep

  obtain ⟨abar, habarPrimitive⟩ :=
    @Field.exists_primitive_element k ell _ _ _ hresfinAlgebra hressep
  have habarIntegral : IsIntegral k abar :=
    Algebra.IsIntegral.isIntegral abar
  have habarAlgebraAdjoin :
      Algebra.adjoin k ({abar} : Set ell) = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element
      habarIntegral.isAlgebraic habarPrimitive
  let pb : PowerBasis k ell :=
    PowerBasis.ofAdjoinEqTop habarIntegral habarAlgebraAdjoin
  let betaFamily : Fin pb.dim → ell := fun j => pb.basis j
  have hbetaLinearIndependent :
      @LinearIndependent (Fin pb.dim) k ell betaFamily _ _
        residueModule := by
    rw [hresidueModule]
    exact pb.basis.linearIndependent
  have hbetaSpan :
      (⊤ : @Submodule k ell _ _ residueModule) ≤
        @Submodule.span k ell _ _ residueModule
          (Set.range betaFamily) := by
    rw [hresidueModule]
    exact le_of_eq pb.basis.span_eq.symm
  let beta :
      @Module.Basis (Fin pb.dim) k ell _ _ residueModule :=
    @Module.Basis.mk (Fin pb.dim) k ell _ _ residueModule
      betaFamily hbetaLinearIndependent hbetaSpan
  have hbeta_apply (j : Fin pb.dim) : beta j = pb.basis j := by
    calc
      beta j = betaFamily j :=
        @Module.Basis.mk_apply (Fin pb.dim) k ell _ _ residueModule
          betaFamily hbetaLinearIndependent hbetaSpan j
      _ = pb.basis j := rfl
  obtain ⟨a, hares⟩ := IsLocalRing.residue_surjective abar
  have homega : ∀ j : Fin pb.dim,
      IsLocalRing.residue W (a ^ (j : ℕ)) = beta j := by
    intro j
    calc
      IsLocalRing.residue W (a ^ (j : ℕ)) =
          abar ^ (j : ℕ) := by rw [map_pow, hares]
      _ = pb.gen ^ (j : ℕ) := by
        rw [PowerBasis.ofAdjoinEqTop_gen]
      _ = pb.basis j := (pb.basis_eq_pow j).symm
      _ = beta j := (hbeta_apply j).symm
  obtain ⟨bL, hbL⟩ :=
    exists_basis_eq_residueBasisLifts_of_finiteUnramifiedExtension
      v w hExt hUnramified beta
        (fun j : Fin pb.dim ↦ a ^ (j : ℕ)) homega
  let pbL : PowerBasis K L :=
    { gen := (a : L)
      dim := pb.dim
      basis := bL
      basis_eq_pow := by
        intro j
        rw [hbL j]
        rfl }

  let algVL : Algebra V L :=
    ((algebraMap K L).comp V.subtype).toAlgebra
  let : Algebra V L := algVL
  let : SMul V L := algVL.toSMul
  let : SMul V K := (inferInstance : Algebra V K).toSMul
  let : IsScalarTower V K L :=
    IsScalarTower.of_algebraMap_eq
      (R := V) (S := K) (A := L) (by intro x; rfl)
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
  have hclosureVv :
      Wv.toSubring = (integralClosure Vv L).toSubring :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      v w hExt hhens
  let eV : V ≃+* Vv :=
    { toFun := fun x => ⟨x, x.property⟩
      invFun := fun x => ⟨x, x.property⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_mul' := fun _ _ => Subtype.ext rfl
      map_add' := fun _ _ => Subtype.ext rfl }
  have heV :
      (algebraMap Vv L).comp eV.toRingHom = algebraMap V L := by
    ext x
    rfl
  have haIntegralVv : IsIntegral Vv (a : L) := by
    change (a : L) ∈ (integralClosure Vv L).toSubring
    rw [← hclosureVv]
    exact a.property
  have haIntegralV : IsIntegral V (a : L) :=
    (eV.isIntegral_iff heV (a : L)).mpr haIntegralVv

  let pV : Polynomial V := minpoly V (a : L)
  let pK : Polynomial K := minpoly K (a : L)
  let pbar : Polynomial k := pV.map (IsLocalRing.residue V)
  let q : Polynomial k := minpoly k abar
  have hpW : Polynomial.aeval a pV = 0 := by
    change pV.eval₂ i a = 0
    apply W.subtype_injective
    rw [map_zero, Polynomial.hom_eval₂]
    change pV.eval₂ (algebraMap V L) (a : L) = 0
    exact minpoly.aeval V (a : L)
  have hpbarRoot : Polynomial.aeval abar pbar = 0 := by
    have hred :=
      unramifiedValuationRing_polynomial_aeval_residue_eq v w hExt pV a
    simp only at hred
    rw [hpW, map_zero] at hred
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    rw [← hares]
    exact hred.symm
  have hqdvd : q ∣ pbar := by
    exact minpoly.dvd k abar hpbarRoot
  have hpVmonic : pV.Monic := minpoly.monic haIntegralV
  have hpbarMonic : pbar.Monic := hpVmonic.map _
  have hqMonic : q.Monic := minpoly.monic habarIntegral
  have hpKmap : pK = pV.map (algebraMap V K) := by
    exact minpoly.isIntegrallyClosed_eq_field_fractions' K haIntegralV
  have hdegree : pbar.natDegree ≤ q.natDegree := by
    apply le_of_eq
    calc
      pbar.natDegree = pV.natDegree := hpVmonic.natDegree_map _
      _ = pK.natDegree := by
        rw [hpKmap, hpVmonic.natDegree_map]
      _ = pbL.dim := pbL.natDegree_minpoly
      _ = pb.dim := rfl
      _ = q.natDegree := pb.natDegree_minpoly.symm
  have hpbarEq : pbar = q := by
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      hqMonic hpbarMonic hqdvd hdegree
  have hqSeparable : q.Separable :=
    Algebra.IsSeparable.isSeparable k abar
  have hqDerivative : q.derivative ≠ 0 :=
    (Polynomial.separable_iff_derivative_ne_zero
      (minpoly.irreducible habarIntegral)).1 hqSeparable
  have hpKDerivative : pK.derivative ≠ 0 := by
    intro hpKzero
    have hpVmapDerivative :
        pV.derivative.map (algebraMap V K) = 0 := by
      rw [← Polynomial.derivative_map, ← hpKmap, hpKzero]
    have hVKinj : Function.Injective (algebraMap V K) := by
      exact V.subtype_injective
    have hpVDerivative : pV.derivative = 0 :=
      (Polynomial.map_eq_zero_iff hVKinj).1 hpVmapDerivative
    have hpbarDerivative : pbar.derivative = 0 := by
      simp [pbar, Polynomial.derivative_map, hpVDerivative]
    apply hqDerivative
    rw [← hpbarEq]
    exact hpbarDerivative
  have haSeparable : IsSeparable K (a : L) := by
    change pK.Separable
    exact (Polynomial.separable_iff_derivative_ne_zero
      (minpoly.irreducible (Algebra.IsIntegral.isIntegral (a : L)))).2
        hpKDerivative
  have hprimitiveK :
      IntermediateField.adjoin K ({(a : L)} : Set L) = ⊤ := by
    apply IntermediateField.adjoin_eq_top_iff.2
    exact pbL.adjoin_gen_eq_top
  have hresidueMinpoly :
      pV.map (IsLocalRing.residue V) =
        minpoly k (IsLocalRing.residue W a) := by
    change pbar = minpoly k (IsLocalRing.residue W a)
    rw [hares]
    exact hpbarEq
  have hpbarSeparable :
      (pV.map (IsLocalRing.residue V)).Separable := by
    change pbar.Separable
    rw [hpbarEq]
    exact hqSeparable
  refine ⟨a, pV, hprimitiveK, ?_, hresidueMinpoly,
    hpbarSeparable, haSeparable⟩
  change pV.map V.subtype = pK
  rw [hpKmap]
  ext n
  rfl

/-- Finite separability source for an unramified extension.

A finite extension satisfying the literal unramified condition is separable
when the base valuation is Henselian.  No separability of
`L/K` is assumed. -/
theorem finiteUnramifiedExtension_isSeparable_of_henselian
    (v : LubinTate.Valuations.ExponentialValuation K) (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a)
    (hhens : ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring v).valuation)
    (hUnramified : FiniteUnramifiedExtension v w hExt) :
    Algebra.IsSeparable K L := by
  obtain ⟨a, _F, hprimitiveK, _hfieldMinpoly, _hresidueMinpoly,
    _hresidueSeparable, haSeparable⟩ :=
    exists_primitive_lift_minpoly_of_finiteUnramifiedExtension
      v w hExt hhens hUnramified
  apply (separableClosure.eq_top_iff (F := K) (E := L)).1
  apply top_unique
  rw [← hprimitiveK]
  apply IntermediateField.adjoin_le_iff.2
  intro x hx
  have hxEq : x = (a : L) := by simpa using hx
  rw [hxEq]
  exact mem_separableClosure_iff.2 haSeparable

end FiniteUnramifiedExtensionSeparability

end Valuations
end AlgebraicNumberTheory

end
