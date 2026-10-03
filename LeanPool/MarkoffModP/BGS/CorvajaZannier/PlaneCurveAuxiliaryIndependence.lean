/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.BivariateGauss
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.AbsoluteIrreducibilityBaseChange
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PerfectConstants
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveSeparability
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.SeparatingCoordinateNotFrobenius

/-!
# The plane-curve auxiliary family over the Frobenius subfield

This file specializes the algebraic resultant argument in
`BivariateGauss.lean` to the function field of an irreducible affine plane
curve over a perfect field of prime characteristic.  Constants are embedded
in the Frobenius subfield `L^p`, and separability over a coordinate rational
subfield is promoted to separability over `L^p` adjoined with that coordinate.

The only irreducibility hypothesis retained at the final boundary is the
literal base change of the defining equation from the constant field to
`L^p`.  This is the precise consequence of absolute irreducibility used in
Corvaja--Zannier's Proposition 1; it is not replaced by an unrelated
typeclass or by an axiom.

Source provenance: published pages 1933--1934; checked semantic reconstruction
`Papers/CorvajaZannier2013/CorvajaZannier2013.tex`, lines 486--571.  The
specialization with Frobenius exponent `p` and no auxiliary twists is the
linear-independence input cited on published page 1940.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

/-- View a polynomial in affine coordinates `0,1` as a polynomial in
coordinate `0` whose coefficients are ordinary polynomials in coordinate
`1`. -/
def planeCurveToBivariate (K : Type*) [Field K] :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  (MvPolynomial.finSuccEquiv K 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)))

@[simp]
theorem planeCurveToBivariate_X_zero
    (K : Type*) [Field K] :
    planeCurveToBivariate K (MvPolynomial.X 0) = Polynomial.X := by
  have hinner :
      MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 0) =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 1) K)) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  rw [planeCurveToBivariate]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 0)) = Polynomial.X
  rw [hinner]
  simp

@[simp]
theorem planeCurveToBivariate_X_one
    (K : Type*) [Field K] :
    planeCurveToBivariate K (MvPolynomial.X 1) =
      Polynomial.C Polynomial.X := by
  have hinner :
      MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1) =
        Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by decide]
    rfl
  rw [planeCurveToBivariate]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1)) =
      Polynomial.C Polynomial.X
  rw [hinner]
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp]
theorem planeCurveToBivariate_C
    (K : Type*) [Field K] (c : K) :
    planeCurveToBivariate K (MvPolynomial.C c) =
      Polynomial.C (Polynomial.C c) := by
  have hinner :
      MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C c) =
        Polynomial.C (MvPolynomial.C c) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  rw [planeCurveToBivariate]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C c)) =
      Polynomial.C (Polynomial.C c)
  rw [hinner]
  simp [MvPolynomial.uniqueAlgEquiv]

/-- The outer degree of the source-oriented iterated presentation is exactly
the degree in coordinate `0`. -/
theorem planeCurveToBivariate_natDegree_eq_degreeOf_zero
    (K : Type*) [Field K] (f : MvPolynomial (Fin 2) K) :
    (planeCurveToBivariate K f).natDegree =
      MvPolynomial.degreeOf 0 f := by
  rw [planeCurveToBivariate]
  change
    ((MvPolynomial.finSuccEquiv K 1 f).map
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom).natDegree = _
  rw [Polynomial.natDegree_map_eq_of_injective
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).injective]
  exact MvPolynomial.natDegree_finSuccEquiv f

/-- Transposing the source-oriented iterated presentation gives the standard
bivariate-polynomial presentation. -/
theorem transposeBivariate_planeCurveToBivariate
    (K : Type*) [Field K] (f : MvPolynomial (Fin 2) K) :
    transposeBivariate (planeCurveToBivariate K f) =
      (Polynomial.Bivariate.equivMvPolynomial K).symm f := by
  let lhs : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K) :=
    transposeBivariate.comp
      (planeCurveToBivariate K).toRingEquiv.toRingHom
  let rhs : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K) :=
    (Polynomial.Bivariate.equivMvPolynomial K).symm.toRingEquiv.toRingHom
  change lhs f = rhs f
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [lhs, rhs]
  · intro i
    fin_cases i <;> simp [lhs, rhs]

/-- The outer degree in the standard bivariate presentation is exactly the
degree in coordinate `1`. -/
theorem bivariateEquiv_symm_natDegree_eq_degreeOf_one
    (K : Type*) [Field K] (f : MvPolynomial (Fin 2) K) :
    ((Polynomial.Bivariate.equivMvPolynomial K).symm f).natDegree =
      MvPolynomial.degreeOf 1 f := by
  let remaining := {i : Fin 2 // i ≠ 1}
  let i0 : remaining := ⟨0, by decide⟩
  let : Unique remaining :=
    { default := i0
      uniq := by
        intro i
        apply Subtype.ext
        omega }
  let q : MvPolynomial (Fin 2) K →+*
      Polynomial (MvPolynomial remaining K) :=
    (MvPolynomial.optionEquivLeft K remaining).toRingEquiv.toRingHom.comp
      (MvPolynomial.rename
        (Equiv.optionSubtypeNe (1 : Fin 2)).symm).toRingHom
  let e : MvPolynomial remaining K ≃ₐ[K] Polynomial K :=
    MvPolynomial.uniqueAlgEquiv K remaining
  let lhs : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K) :=
    (Polynomial.Bivariate.equivMvPolynomial K).symm.toRingEquiv.toRingHom
  let rhs : MvPolynomial (Fin 2) K →+* Polynomial (Polynomial K) :=
    (Polynomial.mapRingHom e.toRingHom).comp q
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs, q, e]
    · intro i
      fin_cases i <;> simp [lhs, rhs, q, e, remaining]
  change (lhs f).natDegree = _
  rw [hhom]
  change ((q f).map e.toRingHom).natDegree = _
  rw [Polynomial.natDegree_map_eq_of_injective e.injective]
  exact (MvPolynomial.degreeOf_eq_natDegree (1 : Fin 2) f).symm

/-- An injective change of coefficients preserves every coordinate degree. -/
theorem degreeOf_map_eq_of_injective
    {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (ι : R →+* S) (hι : Function.Injective ι) (i : σ)
    (f : MvPolynomial σ R) :
    MvPolynomial.degreeOf i (MvPolynomial.map ι f) =
      MvPolynomial.degreeOf i f := by
  rw [MvPolynomial.degreeOf_eq_sup, MvPolynomial.degreeOf_eq_sup,
    MvPolynomial.support_map_of_injective f hι]

variable {K L : Type*} [Field K] [Field L] {p : ℕ}
  [Fact p.Prime] [CharP K p] [CharP L p] [PerfectField K] [Algebra K L]

/-- The defining plane equation after extension of constants from `K` to the
Frobenius subfield `L^p`, in the iterated-polynomial orientation used by the
resultant proof. -/
def planeCurveFrobeniusRelation (f : MvPolynomial (Fin 2) K) :
    Polynomial (Polynomial (frobeniusSubfield L p)) :=
  planeCurveToBivariate (frobeniusSubfield L p)
    (MvPolynomial.map
      (perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)) f)

/-- The first exact bidegree of the Frobenius-base-changed relation. -/
theorem planeCurveFrobeniusRelation_natDegree
    (f : MvPolynomial (Fin 2) K) :
    (planeCurveFrobeniusRelation (L := L) (p := p) f).natDegree =
      MvPolynomial.degreeOf 0 f := by
  rw [planeCurveFrobeniusRelation,
    planeCurveToBivariate_natDegree_eq_degreeOf_zero,
    degreeOf_map_eq_of_injective]
  exact (perfectConstantsToFrobeniusSubfield
    (K := K) (L := L) (p := p)).injective

/-- The second exact bidegree of the Frobenius-base-changed relation. -/
theorem transposeBivariate_planeCurveFrobeniusRelation_natDegree
    (f : MvPolynomial (Fin 2) K) :
    (transposeBivariate
      (planeCurveFrobeniusRelation (L := L) (p := p) f)).natDegree =
      MvPolynomial.degreeOf 1 f := by
  rw [planeCurveFrobeniusRelation,
    transposeBivariate_planeCurveToBivariate,
    bivariateEquiv_symm_natDegree_eq_degreeOf_one,
    degreeOf_map_eq_of_injective]
  exact (perfectConstantsToFrobeniusSubfield
    (K := K) (L := L) (p := p)).injective

/-- Evaluation of the Frobenius-base-changed relation agrees with direct
evaluation of the original plane equation. -/
theorem evalBivariate_planeCurveFrobeniusRelation
    (f : MvPolynomial (Fin 2) K) (x y : L) :
    evalBivariate y x
        (planeCurveFrobeniusRelation (L := L) (p := p) f) =
      MvPolynomial.eval₂ (algebraMap K L) ![x, y] f := by
  let F := frobeniusSubfield L p
  let ι : K →+* F :=
    perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p)
  let evalIterated : Polynomial (Polynomial F) →+* L :=
    Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom (algebraMap F L) y) x
  let lhs : MvPolynomial (Fin 2) K →+* L :=
    evalIterated.comp
      ((planeCurveToBivariate F).toRingEquiv.toRingHom.comp
        (MvPolynomial.map ι))
  let rhs : MvPolynomial (Fin 2) K →+* L :=
    MvPolynomial.eval₂Hom (algebraMap K L) ![x, y]
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      dsimp only [lhs, RingHom.comp_apply]
      rw [MvPolynomial.map_C]
      change evalIterated
          (planeCurveToBivariate F (MvPolynomial.C (ι c))) =
        rhs (MvPolynomial.C c)
      rw [planeCurveToBivariate_C]
      simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, MvPolynomial.eval₂Hom_C, F,
        evalIterated, ι, rhs]
      change
        (((perfectConstantsToFrobeniusSubfield
          (K := K) (L := L) (p := p) c : frobeniusSubfield L p) : L)) =
            algebraMap K L c
      exact coe_perfectConstantsToFrobeniusSubfield
        (K := K) (L := L) (p := p) c
    · intro i
      fin_cases i <;>
        simp [lhs, rhs, evalIterated, ι, RingHom.comp_apply]
  change lhs f = rhs f
  rw [hhom]

/-- Irreducibility after the precise constant-field extension to `L^p`
implies irreducibility in the iterated-polynomial presentation. -/
theorem planeCurveFrobeniusRelation_irreducible
    {f : MvPolynomial (Fin 2) K}
    (hbaseChange : Irreducible
      (MvPolynomial.map
        (perfectConstantsToFrobeniusSubfield
          (K := K) (L := L) (p := p)) f)) :
    Irreducible (planeCurveFrobeniusRelation (L := L) (p := p) f) := by
  exact hbaseChange.map
    (planeCurveToBivariate (frobeniusSubfield L p)).toMulEquiv

/-- Extending the base from the perfect constant field to the Frobenius
subfield preserves separability of the remaining top extension. -/
theorem isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin
    (z : L)
    [Algebra.IsSeparable (IntermediateField.adjoin K {z}) L] :
    Algebra.IsSeparable
      (IntermediateField.adjoin (frobeniusSubfield L p) {z}) L := by
  let F := frobeniusSubfield L p
  let : Algebra K F :=
    (perfectConstantsToFrobeniusSubfield
      (K := K) (L := L) (p := p)).toAlgebra
  let : IsScalarTower K F L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    exact (coe_perfectConstantsToFrobeniusSubfield
      (K := K) (L := L) (p := p) c).symm
  let A : IntermediateField K L := IntermediateField.adjoin K {z}
  let E : IntermediateField F L := IntermediateField.adjoin F {z}
  have hAE : A ≤ E.restrictScalars K := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact IntermediateField.subset_adjoin F {z} (Set.mem_singleton z)
  let : Algebra A E := (IntermediateField.inclusion hAE).toAlgebra
  let : IsScalarTower A E L := IsScalarTower.of_algebraMap_eq' rfl
  exact Algebra.isSeparable_tower_top_of_isSeparable A E L

/-- A separating element has minimal polynomial of exact degree `p` over the
Frobenius subfield. -/
theorem minpoly_natDegree_over_frobeniusSubfield_eq_char
    (z : L) (hz : z ∉ frobeniusSubfield L p)
    [Algebra.IsSeparable
      (IntermediateField.adjoin (frobeniusSubfield L p) {z}) L] :
    (minpoly (frobeniusSubfield L p) z).natDegree = p := by
  let F := frobeniusSubfield L p
  let : IsPurelyInseparable F L := frobeniusSubfield_isPurelyInseparable p
  have hzIntegral : IsIntegral F z := IsPurelyInseparable.isIntegral' F z
  calc
    (minpoly F z).natDegree =
        Module.finrank F (IntermediateField.adjoin F {z}) :=
      (IntermediateField.adjoin.finrank hzIntegral).symm
    _ = Module.finrank F L := by
      rw [adjoin_frobeniusSubfield_eq_top (p := p) z,
        IntermediateField.finrank_top']
    _ = p := finrank_frobeniusSubfield_eq_char (p := p) z hz

/-- **Plane-curve form of the Corvaja--Zannier auxiliary-family
linear-independence proposition (the `q = p`, `z = w = 1` specialization).**

The two nonzero partial derivatives are the source's two separating-coordinate
hypotheses.  For the displayed orientation, separability over the field
generated by coordinate `1` is the one used to prove that this coordinate has
minimal-polynomial degree `p` over `L^p`; the symmetric partial is retained
because the source proposition assumes both coordinates separating.

Two hypotheses mark exact geometric boundaries rather than hiding them:

* `hbaseChange` is irreducibility after the literal extension of constants
  `K → L^p`, the consequence of absolute irreducibility needed by Gauss
  descent;
* `hsecondNotFrobenius` says that the separating second coordinate is not a
  `p`-th power in `L`.  Equivalently, it is the missing differential/basis
  compatibility needed to turn separability into degree exactly `p`.

All remaining assumptions are the printed positivity, exact bidegree,
size, and excluded-degree-alternative hypotheses. -/
theorem planeCurve_auxiliaryFamily_linearIndependent
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (_hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    ∀ (a b h k : ℕ),
      0 < a → 0 < h → 0 < k →
      Irreducible
        (MvPolynomial.map
          (perfectConstantsToFrobeniusSubfield
            (K := K) (L := PlaneCurveFunctionField f) (p := p)) f) →
      (planeCurveFrobeniusRelation
          (K := K) (L := PlaneCurveFunctionField f) (p := p) f).natDegree = a →
      (transposeBivariate
          (planeCurveFrobeniusRelation
            (K := K) (L := PlaneCurveFunctionField f) (p := p) f)).natDegree = b →
      planeCurveFunction f 1 ∉
        frobeniusSubfield (PlaneCurveFunctionField f) p →
      a * h + b * k < p →
      ¬ (a ≤ k ∧ b ≤ h) →
      LinearIndependent (frobeniusSubfield (PlaneCurveFunctionField f) p)
        (auxiliaryFamily
          (planeCurveFunction f 0) (planeCurveFunction f 1) h k) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : CharP (PlaneCurveFunctionField f) p :=
    charP_of_injective_algebraMap
      (algebraMap K (PlaneCurveFunctionField f)).injective p
  intro a b h k ha hh hk hbaseChange hdegreeFirst hdegreeSecond
    hsecondNotFrobenius hsize hdegreeAlternativeExcluded
  let L := PlaneCurveFunctionField f
  let F := frobeniusSubfield L p
  let x : L := planeCurveFunction f 0
  let y : L := planeCurveFunction f 1
  let g : Polynomial (Polynomial F) :=
    planeCurveFrobeniusRelation (K := K) (L := L) (p := p) f
  have hseparableOverSecond :=
    finiteSeparable_over_secondCoordinate_of_irreducible hf hpartialFirst
  let : Algebra.IsSeparable (SecondCoordinateSubfield f) L :=
    hseparableOverSecond.2
  let : Algebra.IsSeparable (IntermediateField.adjoin F {y}) L := by
    exact isSeparable_over_frobeniusAdjoin_of_isSeparable_over_constantAdjoin
      (K := K) (L := L) (p := p) y
  have hminpoly : (minpoly F y).natDegree = p :=
    minpoly_natDegree_over_frobeniusSubfield_eq_char
      (p := p) y hsecondNotFrobenius
  have hyTranscendental : Transcendental K y := by
    exact secondCoordinate_transcendental hf
      (degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst)
  have hyOne : y ≠ 1 := by
    intro hy
    apply hyTranscendental
    rw [hy]
    exact isAlgebraic_one
  have hgIrreducible : Irreducible g := by
    exact planeCurveFrobeniusRelation_irreducible hbaseChange
  have hgCoefficientDegree : ∀ i, (g.coeff i).natDegree ≤ b := by
    intro i
    have hbound := transposeBivariate_coeff_natDegree_le
      (transposeBivariate g) b hdegreeSecond.le i
    simpa only [transposeBivariate_transposeBivariate] using hbound
  have hgZero : evalBivariate y x g = 0 := by
    rw [evalBivariate_planeCurveFrobeniusRelation]
    have hcoordinates : ![x, y] = planeCurveFunction f := by
      funext i
      fin_cases i <;> rfl
    rw [hcoordinates]
    exact eval₂_planeCurveFunction_eq_zero f
  exact auxiliaryFamily_linearIndependent_of_irreducible_bidegree
    g a b h k p ha hh hk hgIrreducible hdegreeFirst hdegreeSecond
      hgCoefficientDegree x y hyOne hminpoly hgZero hsize
      hdegreeAlternativeExcluded

/-- Plane-curve auxiliary-family linear independence with the Frobenius
exclusion discharged from the separating-coordinate hypothesis. -/
theorem planeCurve_auxiliaryFamily_linearIndependent_of_nonzero_partials
    {f : MvPolynomial (Fin 2) K} (hf : Irreducible f)
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    ∀ (a b h k : ℕ),
      0 < a → 0 < h → 0 < k →
      Irreducible
        (MvPolynomial.map
          (perfectConstantsToFrobeniusSubfield
            (K := K) (L := PlaneCurveFunctionField f) (p := p)) f) →
      (planeCurveFrobeniusRelation
          (K := K) (L := PlaneCurveFunctionField f) (p := p) f).natDegree = a →
      (transposeBivariate
          (planeCurveFrobeniusRelation
            (K := K) (L := PlaneCurveFunctionField f) (p := p) f)).natDegree = b →
      a * h + b * k < p →
      ¬ (a ≤ k ∧ b ≤ h) →
      LinearIndependent (frobeniusSubfield (PlaneCurveFunctionField f) p)
        (auxiliaryFamily
          (planeCurveFunction f 0) (planeCurveFunction f 1) h k) := by
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : CharP (PlaneCurveFunctionField f) p :=
    charP_of_injective_algebraMap
      (algebraMap K (PlaneCurveFunctionField f)).injective p
  intro a b h k ha hh hk hbaseChange hdegreeFirst hdegreeSecond
    hsize hdegreeAlternativeExcluded
  exact planeCurve_auxiliaryFamily_linearIndependent
    (p := p) hf hpartialFirst hpartialSecond a b h k ha hh hk
      hbaseChange hdegreeFirst hdegreeSecond
      (secondCoordinate_not_mem_frobeniusSubfield
        (p := p) hf hpartialFirst)
      hsize hdegreeAlternativeExcluded

/-- Plane-curve auxiliary-family linear independence from absolute
irreducibility and the two separating-coordinate hypotheses.  Absolute
irreducibility supplies both irreducibility over the constant field and the
literal base change to the Frobenius subfield used by the resultant proof. -/
theorem planeCurve_auxiliaryFamily_linearIndependent_of_absoluteIrreducible
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let hf : Irreducible f := by
      simpa only [MvPolynomial.map_id] using
        irreducible_map_of_irreducible_map_algebraicClosure
        (RingHom.id K) f habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    ∀ (a b h k : ℕ),
      0 < a → 0 < h → 0 < k →
      (planeCurveFrobeniusRelation
          (K := K) (L := PlaneCurveFunctionField f) (p := p) f).natDegree = a →
      (transposeBivariate
          (planeCurveFrobeniusRelation
            (K := K) (L := PlaneCurveFunctionField f) (p := p) f)).natDegree = b →
      a * h + b * k < p →
      ¬ (a ≤ k ∧ b ≤ h) →
      LinearIndependent (frobeniusSubfield (PlaneCurveFunctionField f) p)
        (auxiliaryFamily
          (planeCurveFunction f 0) (planeCurveFunction f 1) h k) := by
  let hf : Irreducible f := by
    simpa only [MvPolynomial.map_id] using
      irreducible_map_of_irreducible_map_algebraicClosure
      (RingHom.id K) f habsolute
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : CharP (PlaneCurveFunctionField f) p :=
    charP_of_injective_algebraMap
      (algebraMap K (PlaneCurveFunctionField f)).injective p
  dsimp only
  intro a b h k ha hh hk hdegreeFirst hdegreeSecond hsize
    hdegreeAlternativeExcluded
  apply planeCurve_auxiliaryFamily_linearIndependent_of_nonzero_partials
    (p := p) hf hpartialFirst hpartialSecond a b h k ha hh hk
  · exact irreducible_map_perfectConstantsToFrobeniusSubfield
      (K := K) (L := PlaneCurveFunctionField f) (p := p) f habsolute
  · exact hdegreeFirst
  · exact hdegreeSecond
  · exact hsize
  · exact hdegreeAlternativeExcluded

/-- The strongest plane-curve auxiliary-family theorem at the present
algebraic boundary: the bidegrees are the actual coordinate degrees of the
defining equation, so no degree-identification hypotheses remain. -/
theorem planeCurve_auxiliaryFamily_linearIndependent_of_absoluteIrreducible_coordinateDegrees
    {f : MvPolynomial (Fin 2) K}
    (habsolute : Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f))
    (hpartialFirst : MvPolynomial.pderiv 0 f ≠ 0)
    (hpartialSecond : MvPolynomial.pderiv 1 f ≠ 0) :
    let hf : Irreducible f := by
      simpa only [MvPolynomial.map_id] using
        irreducible_map_of_irreducible_map_algebraicClosure
        (RingHom.id K) f habsolute
    letI := planeCurveCoordinateRing_isDomain hf
    letI : CharP (PlaneCurveFunctionField f) p :=
      charP_of_injective_algebraMap
        (algebraMap K (PlaneCurveFunctionField f)).injective p
    ∀ (h k : ℕ),
      0 < h → 0 < k →
      MvPolynomial.degreeOf 0 f * h +
          MvPolynomial.degreeOf 1 f * k < p →
      ¬ (MvPolynomial.degreeOf 0 f ≤ k ∧
          MvPolynomial.degreeOf 1 f ≤ h) →
      LinearIndependent
        (frobeniusSubfield (PlaneCurveFunctionField f) p)
        (auxiliaryFamily
          (planeCurveFunction f 0) (planeCurveFunction f 1) h k) := by
  let hf : Irreducible f := by
    simpa only [MvPolynomial.map_id] using
      irreducible_map_of_irreducible_map_algebraicClosure
      (RingHom.id K) f habsolute
  let : IsDomain (PlaneCurveCoordinateRing f) :=
    planeCurveCoordinateRing_isDomain hf
  let : CharP (PlaneCurveFunctionField f) p :=
    charP_of_injective_algebraMap
      (algebraMap K (PlaneCurveFunctionField f)).injective p
  dsimp only
  intro h k hh hk hsize hdegreeAlternativeExcluded
  apply planeCurve_auxiliaryFamily_linearIndependent_of_absoluteIrreducible
    (p := p) habsolute hpartialFirst hpartialSecond
      (MvPolynomial.degreeOf 0 f) (MvPolynomial.degreeOf 1 f) h k
  · exact degreeOf_first_pos_of_pderiv_ne_zero hpartialFirst
  · exact hh
  · exact hk
  · exact planeCurveFrobeniusRelation_natDegree
      (K := K) (L := PlaneCurveFunctionField f) (p := p) f
  · exact transposeBivariate_planeCurveFrobeniusRelation_natDegree
      (K := K) (L := PlaneCurveFunctionField f) (p := p) f
  · exact hsize
  · exact hdegreeAlternativeExcluded

end

end BGS.CorvajaZannier
