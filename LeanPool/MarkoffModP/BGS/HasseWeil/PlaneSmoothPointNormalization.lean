/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.SquareExtensionAffinePlaces
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveAuxiliaryFinitePlaceCases
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.Tactic

/-!
# Smooth affine centres and normalization residue fields

For a closed affine centre coming from the quadratic constant-field
extension, its residue field embeds into that quadratic extension.  Hence
every residue satisfies the square-Frobenius identity required by the
Stepanov vanishing argument.

At a smooth centre, the local Jacobian criterion identifies the affine local
ring as a discrete valuation ring.  Its valuation subring inside the function
field is therefore the selected dominating normalization valuation.  Thus the
affine centre and its selected normalization prime have canonically equivalent
residue fields; in particular, the selected place has degree at most two and
satisfies square Frobenius.

The file also records that nonvanishing of the second partial derivative at
a quadratic-extension point is exactly non-membership of that derivative in
the corresponding affine maximal ideal.
-/

@[expose] public section

namespace BGS.HasseWeil

open BGS.CorvajaZannier
open IsDedekindDomain
open Module
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-! ## The smooth partial-`Y` chart -/

/-- The singleton relation family presenting the affine plane curve. -/
def planeCurveRelationFamily (f : MvPolynomial (Fin 2) K) (_ : Unit) := f

/-- The singleton-relation presentation is the usual plane-curve coordinate
ring. -/
def planeCurvePresentationEquiv (f : MvPolynomial (Fin 2) K) :
    (MvPolynomial (Fin 2) K ⧸
      Ideal.span (Set.range (planeCurveRelationFamily f))) ≃ₐ[K]
      PlaneCurveCoordinateRing f :=
  Ideal.quotientEquivAlgOfEq K (by
    congr 1
    ext g
    simp [planeCurveRelationFamily, eq_comm])

/-- The plane curve as a one-equation pre-submersive presentation, with the
second coordinate chosen as the Jacobian direction. -/
def planeCurveYPreSubmersivePresentation (f : MvPolynomial (Fin 2) K) :
    Algebra.PreSubmersivePresentation K (PlaneCurveCoordinateRing f) (Fin 2) Unit :=
  (Algebra.PreSubmersivePresentation.naive
      (v := planeCurveRelationFamily f)
      (fun _ => 1) (fun _ _ _ => Subsingleton.elim _ _)).ofAlgEquiv
    (planeCurvePresentationEquiv f)

noncomputable instance planeCurveFinitePresentation (f : MvPolynomial (Fin 2) K) :
    Algebra.FinitePresentation K (PlaneCurveCoordinateRing f) :=
  Algebra.Presentation.finitePresentation_of_isFinite
    (planeCurveYPreSubmersivePresentation f).toPresentation

/-- The class of the second partial derivative in the plane-curve coordinate
ring. -/
def planeCurvePartialY (f : MvPolynomial (Fin 2) K) :
    PlaneCurveCoordinateRing f :=
  planeCurveQuotientMap f (MvPolynomial.pderiv 1 f)

/-- The Jacobian of the chosen one-equation presentation is the second
partial derivative. -/
theorem planeCurveYPreSubmersivePresentation_jacobian
    (f : MvPolynomial (Fin 2) K) :
    (planeCurveYPreSubmersivePresentation f).jacobian = planeCurvePartialY f := by
  let P := Algebra.PreSubmersivePresentation.naive
    (v := planeCurveRelationFamily f)
    (fun _ => 1) (fun _ _ _ => Subsingleton.elim _ _)
  let E := planeCurvePresentationEquiv f
  change (P.ofAlgEquiv E).jacobian = planeCurvePartialY f
  rw [Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique]
  erw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
  change E (Ideal.Quotient.mk _ (MvPolynomial.pderiv 1 f)) =
    Ideal.Quotient.mk _ (MvPolynomial.pderiv 1 f)
  exact Ideal.quotientEquivAlgOfEq_mk K _ _

/-- The principal smooth chart on which the second partial derivative is
inverted. -/
abbrev PlaneCurvePartialYLocalization (f : MvPolynomial (Fin 2) K) :=
  Localization.Away (planeCurvePartialY f)

def planeCurvePartialYLocalizationPreSubmersivePresentation
    (f : MvPolynomial (Fin 2) K) :
    Algebra.PreSubmersivePresentation
      (PlaneCurveCoordinateRing f) (PlaneCurvePartialYLocalization f) Unit Unit :=
  Algebra.PreSubmersivePresentation.localizationAway
    (PlaneCurvePartialYLocalization f) (planeCurvePartialY f)

def planeCurvePartialYCompositePresentation (f : MvPolynomial (Fin 2) K) :
    Algebra.PreSubmersivePresentation K (PlaneCurvePartialYLocalization f)
      (Unit ⊕ Fin 2) (Unit ⊕ Unit) :=
  (planeCurvePartialYLocalizationPreSubmersivePresentation f).comp
    (planeCurveYPreSubmersivePresentation f)

theorem planeCurvePartialYCompositePresentation_jacobian_isUnit
    (f : MvPolynomial (Fin 2) K) :
    IsUnit (planeCurvePartialYCompositePresentation f).jacobian := by
  let A := PlaneCurveCoordinateRing f
  let Ad := PlaneCurvePartialYLocalization f
  let P₀ := planeCurveYPreSubmersivePresentation f
  let Q := planeCurvePartialYLocalizationPreSubmersivePresentation f
  have hP₀ : IsUnit (algebraMap A Ad P₀.jacobian) := by
    rw [show P₀.jacobian = planeCurvePartialY f by
      exact planeCurveYPreSubmersivePresentation_jacobian f]
    exact IsLocalization.Away.algebraMap_isUnit
      (S := Ad) (planeCurvePartialY f)
  have hQ : IsUnit Q.jacobian := by
    rw [show Q.jacobian = algebraMap A Ad (planeCurvePartialY f) by
      exact Algebra.PreSubmersivePresentation.localizationAway_jacobian _]
    exact IsLocalization.Away.algebraMap_isUnit
      (S := Ad) (planeCurvePartialY f)
  change IsUnit (Q.comp P₀).jacobian
  rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.smul_def]
  exact hP₀.mul hQ

/-- A submersive presentation of the partial-`Y` smooth chart. -/
def planeCurvePartialYSubmersivePresentation (f : MvPolynomial (Fin 2) K) :
    Algebra.SubmersivePresentation K (PlaneCurvePartialYLocalization f)
      (Unit ⊕ Fin 2) (Unit ⊕ Unit) where
  toPreSubmersivePresentation := planeCurvePartialYCompositePresentation f
  jacobian_isUnit := planeCurvePartialYCompositePresentation_jacobian_isUnit f

theorem planeCurvePartialYLocalization_isStandardSmooth
    (f : MvPolynomial (Fin 2) K) :
    Algebra.IsStandardSmooth K (PlaneCurvePartialYLocalization f) :=
  (planeCurvePartialYSubmersivePresentation f).isStandardSmooth

theorem planeCurvePartialYSubmersivePresentation_dimension
    (f : MvPolynomial (Fin 2) K) :
    (planeCurvePartialYSubmersivePresentation f).dimension = 1 := by
  simp [Algebra.Presentation.dimension]

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

omit [DecidableEq K] in
/-- The residue field of every closed affine centre obtained from the
quadratic constant-field extension satisfies square Frobenius. -/
theorem squareExtensionClosedPoint_residue_squareFrobenius
    (f : MvPolynomial (Fin 2) K)
    (m : SquareExtensionClosedPoint K p f) :
    ∀ z : m.1.asIdeal.ResidueField,
      z ^ (Fintype.card K) ^ 2 = z := by
  obtain ⟨w, hw⟩ := m.2
  let wf : SquareExtensionClosedPointFiber K p f m :=
    ⟨w, Subtype.ext hw⟩
  let ι := squareExtensionFiberResidueAlgHom K p f m wf
  let : Fintype (SquareExtension K p) := Fintype.ofFinite _
  have hcard : Fintype.card (SquareExtension K p) =
      (Fintype.card K) ^ 2 := by
    rw [Fintype.card_eq_nat_card, FiniteField.natCard_extension K p 2,
      Nat.card_eq_fintype_card]
  intro z
  apply ι.injective
  rw [map_pow, ← hcard, FiniteField.pow_card]

omit [DecidableEq K] in
/-- The second partial derivative is nonzero at a quadratic-extension point
exactly in the direction needed for the local Jacobian criterion: its class
does not belong to the point's affine maximal ideal. -/
theorem squareExtensionPoint_pderiv_not_mem_maximalIdeal
    (f : MvPolynomial (Fin 2) K)
    (z : SquareExtensionAffinePoint K p f)
    (hregular : MvPolynomial.eval ![z.1.1, z.1.2]
      (MvPolynomial.map (algebraMap K (SquareExtension K p))
        (MvPolynomial.pderiv 1 f)) ≠ 0) :
    planeCurveQuotientMap f (MvPolynomial.pderiv 1 f) ∉
      (squareExtensionPointMaximalIdeal K p f z).asIdeal := by
  rw [squareExtensionPointMaximalIdeal_asIdeal, RingHom.mem_ker]
  change MvPolynomial.eval₂ (algebraMap K (SquareExtension K p))
      ![z.1.1, z.1.2] (MvPolynomial.pderiv 1 f) ≠ 0
  rw [MvPolynomial.eval₂_eq_eval_map]
  exact hregular

/-! ## Smooth closed points are discrete valuation rings -/

omit [DecidableEq K] in
/-- A closed point on the partial-`Y` smooth locus is not the generic point. -/
theorem squareExtensionClosedPoint_asIdeal_ne_bot_of_partialY
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (m : SquareExtensionClosedPoint K p f)
    (hsmooth : planeCurvePartialY f ∉ m.1.asIdeal) :
    letI := planeCurveCoordinateRing_isDomain hf
    m.1.asIdeal ≠ ⊥ := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let A := PlaneCurveCoordinateRing f
  obtain ⟨z, hz⟩ := m.2
  let r : A := planeCurveCoordinate f 0 ^ (Nat.card K) ^ 2 -
    planeCurveCoordinate f 0
  have hr : r ∈ m.1.asIdeal := by
    rw [← hz]
    change planeCurveCoordinate f 0 ^ (Nat.card K) ^ 2 -
      planeCurveCoordinate f 0 ∈
        (squareExtensionPointMaximalIdeal K p f z).asIdeal
    exact squareExtensionFrobeniusElement_mem_pointMaximalIdeal K p f z
  intro hm
  have hrzero : r = 0 := by simpa [hm] using hr
  have hpartial : MvPolynomial.pderiv 1 f ≠ 0 := by
    intro hzero
    apply hsmooth
    simp [planeCurvePartialY, hzero]
  have hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartial)
  let g : Polynomial K :=
    Polynomial.X ^ (Nat.card K) ^ 2 - Polynomial.X
  have hg0 : g ≠ 0 := by
    exact FiniteField.X_pow_card_pow_sub_X_ne_zero K (by omega)
      Finite.one_lt_card
  apply hg0
  apply (transcendental_iff.mp hx) g
  simpa [g, r, planeCurveFunction] using congrArg
    (algebraMap A (PlaneCurveFunctionField f)) hrzero

omit [DecidableEq K] in
/-- A finite-residue closed point on the partial-`Y` smooth locus has a
discrete valuation local ring. -/
theorem planeCurveClosedPoint_localization_isDiscreteValuationRing
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (m : MaximalSpectrum (PlaneCurveCoordinateRing f))
    [Finite m.asIdeal.ResidueField]
    (hm0 : m.asIdeal ≠ ⊥)
    (hsmooth : planeCurvePartialY f ∉ m.asIdeal) :
    letI := planeCurveCoordinateRing_isDomain hf
    IsDiscreteValuationRing (Localization.AtPrime m.asIdeal) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let A := PlaneCurveCoordinateRing f
  let d : A := planeCurvePartialY f
  let Ad := PlaneCurvePartialYLocalization f
  have hd0 : d ≠ 0 := by
    intro hd
    apply hsmooth
    change d ∈ m.asIdeal
    rw [hd]
    exact m.asIdeal.zero_mem
  let : IsDomain Ad := IsLocalization.Away.isDomain Ad hd0
  have hdisj : Disjoint ((Submonoid.powers d : Submonoid A) : Set A)
      (m.asIdeal : Set A) := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact hsmooth
  let q : Ideal Ad := Ideal.map (algebraMap A Ad) m.asIdeal
  let hqPrime : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers d) Ad m.asIdeal m.isMaximal.isPrime hdisj
  have hunder : q.comap (algebraMap A Ad) = m.asIdeal := by
    exact IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers d) Ad m.isMaximal.isPrime hdisj
  let hunderMax : (q.comap (algebraMap A Ad)).IsMaximal := by
    rw [hunder]
    exact m.isMaximal
  let hqMax : q.IsMaximal := by
    exact IsLocalization.isMaximal_of_isMaximal_under (Submonoid.powers d) Ad q
  let S := Localization.AtPrime q
  let : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S q
  let : IsDomain S := IsLocalization.isDomain_of_atPrime S q
  let : Algebra A S := inferInstance
  let : IsScalarTower A Ad S := inferInstance
  let hSatPrime : IsLocalization.AtPrime S m.asIdeal := by
    have hlocal : IsLocalization.AtPrime S
        (q.comap (algebraMap A Ad)) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers d) S q
    refine ⟨?_⟩
    simpa only [hunder] using hlocal.toIsLocalizationMap
  let : Algebra K S := inferInstance
  let : IsScalarTower K A S := inferInstance
  let : IsScalarTower K Ad S := inferInstance
  let : Algebra.IsStandardSmooth K Ad :=
    planeCurvePartialYLocalization_isStandardSmooth f
  let : Algebra.FormallySmooth K Ad := inferInstance
  let : Algebra.FormallySmooth Ad S :=
    Algebra.FormallySmooth.of_isLocalization q.primeCompl
  let : Algebra.FormallySmooth K S :=
    Algebra.FormallySmooth.comp K Ad S

  let P := planeCurvePartialYSubmersivePresentation f
  let I := ((Set.range P.map)ᶜ : Set (Unit ⊕ Fin 2))
  let bAd : Basis I Ad Ω[Ad⁄K] := P.basisKaehler
  let bS : Basis I S Ω[S⁄K] :=
    bAd.ofIsLocalizedModule S q.primeCompl
      (KaehlerDifferential.map K K Ad S)
  let k := IsLocalRing.ResidueField S
  let bk : Basis I k (TensorProduct S k (KaehlerDifferential K S)) :=
    bS.baseChange k
  have hcardI : Fintype.card I = P.dimension := by
    simp only [I, Fintype.card_compl_set, Algebra.Presentation.dimension,
      Nat.card_eq_fintype_card, Set.card_range_of_injective P.map_inj]
  have htarget : Module.finrank k
      (TensorProduct S k (KaehlerDifferential K S)) = 1 := by
    rw [Module.finrank_eq_card_basis bk, hcardI]
    exact planeCurvePartialYSubmersivePresentation_dimension f

  let eResidue := atPrimeResidueAlgEquiv K A S m.asIdeal
  let : Finite k := Finite.of_injective eResidue.symm eResidue.symm.injective
  let : Algebra.IsSeparable K k := inferInstance
  let : Algebra.FormallyEtale K k :=
    Algebra.FormallyEtale.of_isSeparable K k
  have hraw : Function.Injective
      (KaehlerDifferential.kerCotangentToTensor K S k) := by
    exact (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
      (R := K) (P := S) (A := k) IsLocalRing.residue_surjective).2 inferInstance
  have hker : RingHom.ker (algebraMap S k) =
      IsLocalRing.maximalIdeal S := by
    simpa [k, IsLocalRing.ResidueField.algebraMap_eq] using
      (IsLocalRing.ker_residue (R := S))
  let cotangentEquiv : IsLocalRing.CotangentSpace S ≃ₗ[S]
      (RingHom.ker (algebraMap S k)).Cotangent :=
    Ideal.Cotangent.equivOfEq _ _ hker.symm
  let cotangentMapS : IsLocalRing.CotangentSpace S →ₗ[S]
      (TensorProduct S k (KaehlerDifferential K S)) :=
    (KaehlerDifferential.kerCotangentToTensor K S k).comp
      cotangentEquiv.toLinearMap
  let cotangentMap : IsLocalRing.CotangentSpace S →ₗ[k]
      (TensorProduct S k (KaehlerDifferential K S)) :=
    cotangentMapS.extendScalarsOfSurjective IsLocalRing.residue_surjective
  have hcotangentMap : Function.Injective cotangentMap := by
    intro x y hxy
    apply cotangentEquiv.injective
    apply hraw
    exact hxy
  have hcotangent : Module.finrank k (IsLocalRing.CotangentSpace S) ≤ 1 := by
    rw [← htarget]
    exact cotangentMap.finrank_le_finrank_of_injective hcotangentMap

  have hnotField : ¬ IsField S :=
    IsLocalization.AtPrime.not_isField A hm0 S
  have hprincipal : (IsLocalRing.maximalIdeal S).IsPrincipal :=
    IsLocalRing.finrank_cotangentSpace_le_one_iff.mp hcotangent
  have hSDvr : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnotField).out 5 1).mp hprincipal
  let : IsDiscreteValuationRing S := hSDvr
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsLocalization.algEquiv m.asIdeal.primeCompl S
      (Localization.AtPrime m.asIdeal)).toRingEquiv

omit [DecidableEq K] in
/-- The local ring at a closed point where the second partial derivative does
not vanish is a discrete valuation ring.  This is the local Jacobian boundary
needed to compare the affine curve with its normalization. -/
theorem squareExtensionClosedPoint_localization_isDiscreteValuationRing
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (m : SquareExtensionClosedPoint K p f)
    (hsmooth : planeCurvePartialY f ∉ m.1.asIdeal) :
    letI := planeCurveCoordinateRing_isDomain hf
    IsDiscreteValuationRing (Localization.AtPrime m.1.asIdeal) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let A := PlaneCurveCoordinateRing f
  let d : A := planeCurvePartialY f
  let Ad := PlaneCurvePartialYLocalization f
  have hd0 : d ≠ 0 := by
    intro hd
    apply hsmooth
    change d ∈ m.1.asIdeal
    rw [hd]
    exact m.1.asIdeal.zero_mem
  let : IsDomain Ad := IsLocalization.Away.isDomain Ad hd0
  have hdisj : Disjoint ((Submonoid.powers d : Submonoid A) : Set A)
      (m.1.asIdeal : Set A) := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact hsmooth
  let q : Ideal Ad := Ideal.map (algebraMap A Ad) m.1.asIdeal
  let hqPrime : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers d) Ad m.1.asIdeal m.1.isMaximal.isPrime hdisj
  have hunder : q.comap (algebraMap A Ad) = m.1.asIdeal := by
    exact IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers d) Ad m.1.isMaximal.isPrime hdisj
  let hunderMax : (q.comap (algebraMap A Ad)).IsMaximal := by
    rw [hunder]
    exact m.1.isMaximal
  let hqMax : q.IsMaximal := by
    exact IsLocalization.isMaximal_of_isMaximal_under (Submonoid.powers d) Ad q
  let S := Localization.AtPrime q
  let : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S q
  let : IsDomain S := IsLocalization.isDomain_of_atPrime S q
  let : Algebra A S := inferInstance
  let : IsScalarTower A Ad S := inferInstance
  let hSatPrime : IsLocalization.AtPrime S m.1.asIdeal := by
    have hlocal : IsLocalization.AtPrime S
        (q.comap (algebraMap A Ad)) :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers d) S q
    refine ⟨?_⟩
    simpa only [hunder] using hlocal.toIsLocalizationMap
  let : Algebra K S := inferInstance
  let : IsScalarTower K A S := inferInstance
  let : IsScalarTower K Ad S := inferInstance
  let : Algebra.IsStandardSmooth K Ad :=
    planeCurvePartialYLocalization_isStandardSmooth f
  let : Algebra.FormallySmooth K Ad := inferInstance
  let : Algebra.FormallySmooth Ad S :=
    Algebra.FormallySmooth.of_isLocalization q.primeCompl
  let : Algebra.FormallySmooth K S :=
    Algebra.FormallySmooth.comp K Ad S

  let P := planeCurvePartialYSubmersivePresentation f
  let I := ((Set.range P.map)ᶜ : Set (Unit ⊕ Fin 2))
  let bAd : Basis I Ad Ω[Ad⁄K] := P.basisKaehler
  let bS : Basis I S Ω[S⁄K] :=
    bAd.ofIsLocalizedModule S q.primeCompl
      (KaehlerDifferential.map K K Ad S)
  let k := IsLocalRing.ResidueField S
  let bk : Basis I k (TensorProduct S k (KaehlerDifferential K S)) :=
    bS.baseChange k
  have hcardI : Fintype.card I = P.dimension := by
    simp only [I, Fintype.card_compl_set, Algebra.Presentation.dimension,
      Nat.card_eq_fintype_card, Set.card_range_of_injective P.map_inj]
  have htarget : Module.finrank k
      (TensorProduct S k (KaehlerDifferential K S)) = 1 := by
    rw [Module.finrank_eq_card_basis bk, hcardI]
    exact planeCurvePartialYSubmersivePresentation_dimension f

  obtain ⟨z, hz⟩ := m.2
  let zf : SquareExtensionClosedPointFiber K p f m :=
    ⟨z, Subtype.ext hz⟩
  let ι := squareExtensionFiberResidueAlgHom K p f m zf
  let : Finite m.1.asIdeal.ResidueField := Finite.of_injective ι ι.injective
  let eResidue := atPrimeResidueAlgEquiv K A S m.1.asIdeal
  let : Finite k := Finite.of_injective eResidue.symm eResidue.symm.injective
  let : Algebra.IsSeparable K k := inferInstance
  let : Algebra.FormallyEtale K k :=
    Algebra.FormallyEtale.of_isSeparable K k
  have hraw : Function.Injective
      (KaehlerDifferential.kerCotangentToTensor K S k) := by
    exact (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
      (R := K) (P := S) (A := k) IsLocalRing.residue_surjective).2 inferInstance
  have hker : RingHom.ker (algebraMap S k) =
      IsLocalRing.maximalIdeal S := by
    simpa [k, IsLocalRing.ResidueField.algebraMap_eq] using
      (IsLocalRing.ker_residue (R := S))
  let cotangentEquiv : IsLocalRing.CotangentSpace S ≃ₗ[S]
      (RingHom.ker (algebraMap S k)).Cotangent :=
    Ideal.Cotangent.equivOfEq _ _ hker.symm
  let cotangentMapS : IsLocalRing.CotangentSpace S →ₗ[S]
      (TensorProduct S k (KaehlerDifferential K S)) :=
    (KaehlerDifferential.kerCotangentToTensor K S k).comp
      cotangentEquiv.toLinearMap
  let cotangentMap : IsLocalRing.CotangentSpace S →ₗ[k]
      (TensorProduct S k (KaehlerDifferential K S)) :=
    cotangentMapS.extendScalarsOfSurjective IsLocalRing.residue_surjective
  have hcotangentMap : Function.Injective cotangentMap := by
    intro x y hxy
    apply cotangentEquiv.injective
    apply hraw
    exact hxy
  have hcotangent : Module.finrank k (IsLocalRing.CotangentSpace S) ≤ 1 := by
    rw [← htarget]
    exact cotangentMap.finrank_le_finrank_of_injective hcotangentMap

  have hm0 : m.1.asIdeal ≠ ⊥ :=
    squareExtensionClosedPoint_asIdeal_ne_bot_of_partialY
      K p hf m hsmooth
  have hnotField : ¬ IsField S :=
    IsLocalization.AtPrime.not_isField A hm0 S
  have hprincipal : (IsLocalRing.maximalIdeal S).IsPrincipal :=
    IsLocalRing.finrank_cotangentSpace_le_one_iff.mp hcotangent
  have hSDvr : IsDiscreteValuationRing S :=
    ((IsDiscreteValuationRing.TFAE S hnotField).out 5 1).mp hprincipal
  let : IsDiscreteValuationRing S := hSDvr
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (IsLocalization.algEquiv m.1.asIdeal.primeCompl S
      (Localization.AtPrime m.1.asIdeal)).toRingEquiv

section CommonLocalization

variable {C A B R : Type*}
  [Field C] [CommRing A] [CommRing B] [CommRing R]
  [Algebra C A] [Algebra C B] [Algebra A R] [Algebra B R] [Algebra C R]
  [IsScalarTower C A R] [IsScalarTower C B R] [IsLocalRing R]
  (m : Ideal A) [m.IsMaximal] (q : Ideal B) [q.IsMaximal]
  [IsLocalization.AtPrime R m] [IsLocalization.AtPrime R q]

/-- If two maximal ideals have the same local ring, their residue fields are
canonically equivalent over the common coefficient field. -/
noncomputable def atPrimeResidueAlgEquivOfCommonLocalization :
    m.ResidueField ≃ₐ[C] q.ResidueField :=
  (atPrimeResidueAlgEquiv C A R m).trans
    (atPrimeResidueAlgEquiv C B R q).symm

include R in
/-- Residue-field degree is preserved across a common localization. -/
theorem finrank_residueField_eq_of_commonLocalization :
    Module.finrank C m.ResidueField = Module.finrank C q.ResidueField :=
  (atPrimeResidueAlgEquivOfCommonLocalization
    (C := C) (A := A) (B := B) (R := R) m q).toLinearEquiv.finrank_eq

end CommonLocalization

private theorem residue_finrank_eq_of_regular_dominating_valuation
    (C A B E : Type*) [Field C] [CommRing A] [IsDomain A] [CommRing B] [Field E]
    [Algebra C A] [Algebra C B] [Algebra A E] [IsFractionRing A E]
    [Algebra C E] [IsScalarTower C A E]
    (m : MaximalSpectrum A) (q : Ideal B) [q.IsMaximal]
    (R : ValuationSubring E) [Algebra B R] [Algebra C R]
    [IsScalarTower C B R] [IsLocalization.AtPrime R q]
    [IsDiscreteValuationRing (Localization.AtPrime m.asIdeal)]
    (hm0 : m.asIdeal ≠ ⊥)
    (hspec : R = dominatingValuationSubring (A := A) (L := E) m)
    (hscalar : ∀ c : C, ((algebraMap C R c : R) : E) = algebraMap C E c) :
    Module.finrank C m.asIdeal.ResidueField = Module.finrank C q.ResidueField := by
  let Wsub : Subalgebra A E :=
    Localization.subalgebra.ofField E m.asIdeal.primeCompl
      m.asIdeal.primeCompl_le_nonZeroDivisors
  let : IsDiscreteValuationRing Wsub :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsLocalization.algEquiv m.asIdeal.primeCompl
        (Localization.AtPrime m.asIdeal) Wsub).toRingEquiv
  let W : ValuationSubring E :=
    ValuationSubring.ofSubring Wsub.toSubring fun x => by
      simpa [IsLocalization.IsInteger] using
        ValuationRing.isInteger_or_isInteger Wsub x
  let : Algebra A W := Wsub.algebra'
  let : IsLocalization m.asIdeal.primeCompl W :=
    Localization.subalgebra.isLocalization_ofField E
      m.asIdeal.primeCompl m.asIdeal.primeCompl_le_nonZeroDivisors
  let eW : Wsub ≃+* W :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let : IsDiscreteValuationRing W :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eW
  let V := dominatingValuationSubring (A := A) (L := E) m
  have hWV : W ≤ V := by
    intro x hx
    change x ∈ Wsub at hx
    rcases hx with ⟨a, s, hs, rfl⟩
    have haV : algebraMap A E a ∈ V :=
      range_le_dominatingValuationSubring m ⟨a, rfl⟩
    have hsV : algebraMap A E s ∈ V :=
      range_le_dominatingValuationSubring m ⟨s, rfl⟩
    let sv : V := ⟨algebraMap A E s, hsV⟩
    have hsvNot : sv ∉ IsLocalRing.maximalIdeal V := by
      intro hsv
      apply hs
      rw [pointIdeal_eq_comap_dominatingValuationSubring_maximalIdeal
        (A := A) (L := E)]
      exact hsv
    have hsvUnit : IsUnit sv := by
      by_contra hunit
      apply hsvNot
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hunit
    have hinvV : (algebraMap A E s)⁻¹ ∈ V :=
      Submonoid.inv_mem_of_isUnit (S := V) hsvUnit
    exact V.toSubring.mul_mem haV hinvV
  rw [Submodule.ne_bot_iff] at hm0
  obtain ⟨r, hr, hr0⟩ := hm0
  have hrMap0 : algebraMap A E r ≠ 0 := by
    intro hzero
    apply hr0
    apply IsFractionRing.injective A E
    simpa using hzero
  have hrNonunits : algebraMap A E r ∈ V.nonunits :=
    algebraMap_mem_dominatingValuationSubring_nonunits_of_mem
      (A := A) (L := E) m r hr
  have hV : V ≠ ⊤ := by
    intro htop
    have hnontrivial : V.valuation.IsNontrivial :=
      (Valuation.isNontrivial_iff_exists_lt_one V.valuation).2
        ⟨algebraMap A E r, hrMap0, hrNonunits⟩
    exact ((ValuationSubring.eq_top_iff V).mp htop) hnontrivial
  have hWVeq : W = V :=
    ValuationSubring.eq_of_le_of_ne_top W hWV hV
  have hWR : W = R := hWVeq.trans hspec.symm
  let eWR : W ≃+* R :=
    { toFun := fun x => ⟨x.1, by rw [← hWR]; exact x.2⟩
      invFun := fun x => ⟨x.1, by rw [hWR]; exact x.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => Subtype.ext rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let : Algebra A R :=
    RingHom.toAlgebra (eWR.toRingHom.comp (algebraMap A W))
  let eWRAlg : W ≃ₐ[A] R :=
    { eWR with commutes' := fun _ => rfl }
  let : IsLocalization m.asIdeal.primeCompl R :=
    IsLocalization.isLocalization_of_algEquiv
      m.asIdeal.primeCompl eWRAlg
  let : IsScalarTower C A R :=
    IsScalarTower.of_algebraMap_eq (R := C) (S := A) (A := R) (fun c => by
      apply Subtype.ext
      change ((algebraMap C R c : R) : E) = algebraMap A E (algebraMap C A c)
      rw [hscalar, ← IsScalarTower.algebraMap_apply C A E])
  exact finrank_residueField_eq_of_commonLocalization (C := C) (R := R) m.asIdeal q

section SquareExtensionCommonLocalization

variable {f : MvPolynomial (Fin 2) K}
variable {B R : Type*} [CommRing B] [CommRing R]
  [Algebra K B]
  [Algebra (PlaneCurveCoordinateRing f) R] [Algebra B R] [Algebra K R]
  [IsScalarTower K (PlaneCurveCoordinateRing f) R]
  [IsScalarTower K B R] [IsLocalRing R]
  (m : SquareExtensionClosedPoint K p f)
  (q : Ideal B) [q.IsMaximal]
  [IsLocalization.AtPrime R m.1.asIdeal]
  [IsLocalization.AtPrime R q]

omit [DecidableEq K] in
include f R m in
/-- A normalization prime sharing its local ring with a
quadratic-extension affine centre has residue degree at most two. -/
theorem squareExtensionClosedPoint_commonLocalization_residue_finrank_le_two :
    Module.finrank K q.ResidueField ≤ 2 := by
  rw [← finrank_residueField_eq_of_commonLocalization
    (C := K) (A := PlaneCurveCoordinateRing f) (B := B) (R := R)
      m.1.asIdeal q]
  exact squareExtensionClosedPoint_residueDegree_le_two K p f m

omit [DecidableEq K] in
include f R m in
/-- A normalization local ring that is also the affine local ring at a
quadratic-extension centre has the square-Frobenius residue identity needed
by Stepanov's method. -/
theorem squareExtensionClosedPoint_commonLocalization_residue_squareFrobenius :
    ∀ z : q.ResidueField, z ^ (Fintype.card K) ^ 2 = z := by
  let e := atPrimeResidueAlgEquivOfCommonLocalization
    (C := K) (A := PlaneCurveCoordinateRing f) (B := B) (R := R)
      m.1.asIdeal q
  intro z
  apply e.symm.injective
  simpa using
    (squareExtensionClosedPoint_residue_squareFrobenius K p f m (e.symm z))

end SquareExtensionCommonLocalization

/-! ## The selected normalization place at a smooth centre -/

/-- At a partial-`Y` smooth centre, normalization preserves the residue field:
the degree of the selected normalization place is exactly the residue degree
of its affine centre. -/
theorem squareExtensionClosedPointExhaustiveFinitePlace_placeDegree_eq_residueDegree_of_partialY
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : SquareExtensionClosedPoint K p f)
    (hsmooth : planeCurvePartialY f ∉ m.1.asIdeal) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : DecidableEq (RatFunc K) := Classical.decEq _
    finiteExtensionPlaceDegree K (PlaneCurveFunctionField f)
        (.inl (squareExtensionClosedPointExhaustiveFinitePlace
          K p hf hpartialSecond m)) =
      Module.finrank K m.1.asIdeal.ResidueField := by
  intro domainModel hx ratFuncModel polynomialModel towerModel finiteModel separableModel
    decidableModel
  let A := PlaneCurveCoordinateRing f
  let E := PlaneCurveFunctionField f
  let q : FiniteExtensionFinitePlace K E :=
    squareExtensionClosedPointExhaustiveFinitePlace
      K p hf hpartialSecond m
  let B := RatFuncFiniteIntegralClosure K E
  let : Algebra K B :=
    RingHom.toAlgebra
      ((algebraMap (Polynomial K) B).comp (algebraMap K (Polynomial K)))
  let : IsScalarTower K (Polynomial K) B :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      have h := congrArg
        (fun g : Polynomial K →+* E => g (Polynomial.C c))
        (ratFuncSpecialization_comp_polynomial_algebraMap
          (planeCurveFunction f 0) hx)
      simpa [E, planeCurveFirstCoordinateRatFuncAlgebra] using h.symm)
  let : IsScalarTower K (Polynomial K) E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) E,
        IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
      rfl)
  let : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) E]
    rfl)
  let R := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E q
  let : Algebra K R :=
    RingHom.toAlgebra ((algebraMap B R).comp (algebraMap K B))
  let : IsScalarTower K B R := IsScalarTower.of_algebraMap_eq' rfl

  let : IsDiscreteValuationRing (Localization.AtPrime m.1.asIdeal) :=
    squareExtensionClosedPoint_localization_isDiscreteValuationRing K p hf m hsmooth
  have hresidue := residue_finrank_eq_of_regular_dominating_valuation K A B E
    m.1 q.asIdeal R
    (squareExtensionClosedPoint_asIdeal_ne_bot_of_partialY K p hf m hsmooth)
    (squareExtensionClosedPointExhaustiveFinitePlace_spec K p hf hpartialSecond m)
    (fun c => by
      change algebraMap B E (algebraMap K B c) = algebraMap K E c
      exact (IsScalarTower.algebraMap_apply K B E c).symm)
  rw [finiteExtensionFinitePlace_degree_eq_finrank_residueField K E q]
  exact hresidue.symm

section FinitePlaceDegree

variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
variable [DecidableEq (RatFunc K)]

local instance (priority := 10) planeSmoothPolynomialAlgebra : Algebra K[X] L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K[X] (RatFunc K)))

local instance planeSmoothPolynomialScalarTower :
    IsScalarTower K[X] (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance planeSmoothFiniteConstantAlgebra :
    Algebra K (RatFuncFiniteIntegralClosure K L) :=
  RingHom.toAlgebra ((algebraMap K[X]
    (RatFuncFiniteIntegralClosure K L)).comp (algebraMap K K[X]))

local instance planeSmoothFiniteConstantTower :
    IsScalarTower K K[X] (RatFuncFiniteIntegralClosure K L) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Any finite function-field place of constant-field degree at most two has
the square-Frobenius residue identity consumed by the Stepanov restriction
map. -/
theorem finiteExtensionFinitePlace_residue_squareFrobenius_of_degree_le_two
    (q : FiniteExtensionFinitePlace K L)
    (hdegree : finiteExtensionPlaceDegree K L (.inl q) ≤ 2) :
    ∀ z : q.asIdeal.ResidueField,
      z ^ (Fintype.card K) ^ 2 = z := by
  have hdegree' : Module.finrank K q.asIdeal.ResidueField ≤ 2 := by
    rw [finiteExtensionFinitePlace_degree_eq_finrank_residueField K L q] at hdegree
    exact hdegree
  let : Finite q.asIdeal.ResidueField :=
    finiteExtensionFinitePlace_residueField_finite (K := K) (L := L) q
  let : Fintype q.asIdeal.ResidueField := Fintype.ofFinite _
  let : Module.Finite K q.asIdeal.ResidueField := by
    rw [Module.finite_def]
    exact ⟨Finset.univ, by simp⟩
  have hpositive : 0 < Module.finrank K q.asIdeal.ResidueField := Module.finrank_pos
  have hcard : Fintype.card q.asIdeal.ResidueField =
      (Fintype.card K) ^ Module.finrank K q.asIdeal.ResidueField := by
    exact Module.card_eq_pow_finrank
  intro z
  have hdegreeCases : Module.finrank K q.asIdeal.ResidueField = 1 ∨
      Module.finrank K q.asIdeal.ResidueField = 2 := by omega
  rcases hdegreeCases with hdegreeOne | hdegreeTwo
  · have hz := FiniteField.pow_card_pow 2 z
    simpa [hcard, hdegreeOne] using hz
  · simpa [hcard, hdegreeTwo] using FiniteField.pow_card z

end FinitePlaceDegree

/-- A selected normalization place above a partial-`Y` smooth quadratic
closed point has constant-field degree at most two. -/
theorem squareExtensionClosedPointExhaustiveFinitePlace_placeDegree_le_two_of_partialY
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : SquareExtensionClosedPoint K p f)
    (hsmooth : planeCurvePartialY f ∉ m.1.asIdeal) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    finiteExtensionPlaceDegree K (PlaneCurveFunctionField f)
        (.inl (squareExtensionClosedPointExhaustiveFinitePlace
          K p hf hpartialSecond m)) ≤ 2 := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  rw [squareExtensionClosedPointExhaustiveFinitePlace_placeDegree_eq_residueDegree_of_partialY
    K p hf hpartialSecond m hsmooth]
  exact squareExtensionClosedPoint_residueDegree_le_two K p f m

/-- The residue field of the selected normalization place above a
partial-`Y` smooth quadratic closed point satisfies square Frobenius. -/
theorem squareExtensionClosedPointExhaustiveFinitePlace_residue_squareFrobenius_of_partialY
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (m : SquareExtensionClosedPoint K p f)
    (hsmooth : planeCurvePartialY f ∉ m.1.asIdeal) :
    letI := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    letI := planeCurveFirstCoordinateRatFuncAlgebra f hx
    letI : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    letI : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    letI : DecidableEq (RatFunc K) := Classical.decEq _
    ∀ z : (squareExtensionClosedPointExhaustiveFinitePlace
        K p hf hpartialSecond m).asIdeal.ResidueField,
      z ^ (Fintype.card K) ^ 2 = z := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let hx := firstCoordinate_transcendental hf
    (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
  let : Algebra (RatFunc K) (PlaneCurveFunctionField f) :=
    planeCurveFirstCoordinateRatFuncAlgebra f hx
  let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
    RingHom.toAlgebra
      ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
        (algebraMap (Polynomial K) (RatFunc K)))
  let : IsScalarTower (Polynomial K) (RatFunc K)
      (PlaneCurveFunctionField f) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
    finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
    separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
  let : DecidableEq (RatFunc K) := Classical.decEq _
  let q := squareExtensionClosedPointExhaustiveFinitePlace
    K p hf hpartialSecond m
  apply finiteExtensionFinitePlace_residue_squareFrobenius_of_degree_le_two
    K (PlaneCurveFunctionField f) q
  exact squareExtensionClosedPointExhaustiveFinitePlace_placeDegree_le_two_of_partialY
    K p hf hpartialSecond m hsmooth

/-- Evaluation identifies the residue field at a rational affine point with
the ground field. -/
noncomputable def affinePlaneCurvePoint_residueAlgEquiv
    {f : MvPolynomial (Fin 2) K} (z : AffinePlaneCurvePoint f) :
    (affinePlaneCurvePointMaximalIdeal f z).asIdeal.ResidueField ≃ₐ[K] K := by
  let A := PlaneCurveCoordinateRing f
  let m := affinePlaneCurvePointMaximalIdeal f z
  let ev : A →ₐ[K] K :=
    { planeCurvePointEval f z with
      commutes' := planeCurvePointEval_algebraMap f z }
  let eQuot : (A ⧸ m.asIdeal) ≃ₐ[K] K := by
    change (A ⧸ RingHom.ker ev.toRingHom) ≃ₐ[K] K
    exact Ideal.quotientKerAlgEquivOfSurjective
      (planeCurvePointEval_surjective f z)
  let eResidue : (A ⧸ m.asIdeal) ≃ₐ[K] m.asIdeal.ResidueField :=
    AlgEquiv.ofBijective
      (IsScalarTower.toAlgHom K (A ⧸ m.asIdeal) m.asIdeal.ResidueField)
      m.asIdeal.bijective_algebraMap_quotient_residueField
  exact eResidue.symm.trans eQuot

/-- The normalization place selected above a rational affine point that is
regular in the second-coordinate direction has degree one over the full
constant field. -/
theorem affinePointExhaustiveFinitePlace_degree_eq_one_of_partialY
    {f : MvPolynomial (Fin 2) K}
    (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0)
    (z : AffinePlaneCurvePoint f)
    (hregular : MvPolynomial.eval ![z.1.1, z.1.2]
      (MvPolynomial.pderiv 1 f) ≠ 0) :
    let := planeCurveCoordinateRing_isDomain hf
    let hx := firstCoordinate_transcendental hf
      (degreeOf_second_pos_of_pderiv_ne_zero hpartialSecond)
    let := planeCurveFirstCoordinateRatFuncAlgebra f hx
    let : Algebra (Polynomial K) (PlaneCurveFunctionField f) :=
      RingHom.toAlgebra
        ((algebraMap (RatFunc K) (PlaneCurveFunctionField f)).comp
          (algebraMap (Polynomial K) (RatFunc K)))
    let : IsScalarTower (Polynomial K) (RatFunc K)
        (PlaneCurveFunctionField f) :=
      IsScalarTower.of_algebraMap_eq' rfl
    let : FiniteDimensional (RatFunc K) (PlaneCurveFunctionField f) :=
      finiteDimensional_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : Algebra.IsSeparable (RatFunc K) (PlaneCurveFunctionField f) :=
      separable_planeCurveFunctionField_over_ratFunc hf hpartialSecond
    let : DecidableEq (RatFunc K) := Classical.decEq _
    finiteExtensionPlaceDegree K (PlaneCurveFunctionField f)
      (.inl (affinePointExhaustiveFinitePlace
        hf hpartialFirst hpartialSecond z)) = 1 := by
  intro domainModel hx ratFuncModel polynomialModel towerModel finiteModel separableModel
    decidableModel
  let A := PlaneCurveCoordinateRing f
  let E := PlaneCurveFunctionField f
  let m := affinePlaneCurvePointMaximalIdeal f z
  let q : FiniteExtensionFinitePlace K E :=
    affinePointExhaustiveFinitePlace hf hpartialFirst hpartialSecond z
  let B := RatFuncFiniteIntegralClosure K E
  let : Algebra K B :=
    RingHom.toAlgebra
      ((algebraMap (Polynomial K) B).comp (algebraMap K (Polynomial K)))
  let : IsScalarTower K (Polynomial K) B :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower K (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      have h := congrArg
        (fun g : Polynomial K →+* E => g (Polynomial.C c))
        (ratFuncSpecialization_comp_polynomial_algebraMap
          (planeCurveFunction f 0) hx)
      simpa [E, planeCurveFirstCoordinateRatFuncAlgebra] using h.symm)
  let : IsScalarTower K (Polynomial K) E :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      rw [IsScalarTower.algebraMap_apply K (RatFunc K) E,
        IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K)]
      rfl)
  let : IsScalarTower K B E := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) E]
    rfl)
  let R := IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E q
  let : Algebra K R :=
    RingHom.toAlgebra ((algebraMap B R).comp (algebraMap K B))
  let : IsScalarTower K B R := IsScalarTower.of_algebraMap_eq' rfl

  let eCenter := affinePlaneCurvePoint_residueAlgEquiv K z
  let : Finite m.asIdeal.ResidueField :=
    Finite.of_injective eCenter eCenter.injective
  let r0 : A := planeCurveCoordinate f 0 - algebraMap K A z.1.1
  have hr0mem : r0 ∈ m.asIdeal :=
    firstCoordinate_sub_mem_affinePlaneCurvePointMaximalIdeal z
  have hr0mapEq : algebraMap A E r0 =
      planeCurveFunction f 0 - algebraMap K E z.1.1 := by
    simp only [r0, map_sub]
    rfl
  have hr0map : algebraMap A E r0 ≠ 0 := by
    rw [hr0mapEq]
    exact firstCoordinate_sub_affinePoint_ne_zero hf hpartialSecond z
  have hr0 : r0 ≠ 0 := by
    intro hzero
    apply hr0map
    rw [hzero, map_zero]
  have hm0 : m.asIdeal ≠ ⊥ := by
    intro hm
    apply hr0
    simpa [hm] using hr0mem
  have hsmooth : planeCurvePartialY f ∉ m.asIdeal := by
    change planeCurvePointEval f z (planeCurvePartialY f) ≠ 0
    change MvPolynomial.eval ![z.1.1, z.1.2]
      (MvPolynomial.pderiv 1 f) ≠ 0
    exact hregular
  let : IsDiscreteValuationRing (Localization.AtPrime m.asIdeal) :=
    planeCurveClosedPoint_localization_isDiscreteValuationRing
      K hf m hm0 hsmooth

  have hresidue := residue_finrank_eq_of_regular_dominating_valuation K A B E
    m q.asIdeal R hm0
    (affinePointExhaustiveFinitePlace_spec hf hpartialFirst hpartialSecond z).1
    (fun c => by
      change algebraMap B E (algebraMap K B c) = algebraMap K E c
      exact (IsScalarTower.algebraMap_apply K B E c).symm)
  rw [finiteExtensionFinitePlace_degree_eq_finrank_residueField K E q, ← hresidue]
  simpa using eCenter.toLinearEquiv.finrank_eq

end
end BGS.HasseWeil
