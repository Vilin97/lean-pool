/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.LaurentJacobian
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Smoothness of the Laurent trace cover

This module converts the Jacobian unit-ideal calculation into an actual `Algebra.Smooth` theorem.
It constructs submersive presentations on the two principal opens where the formal partial
derivatives are inverted, proves those localizations standard smooth, and covers the prime
spectrum using `weightedSplitTraceLaurentPartials_span_top`.

The construction is explicit: no smoothness or normality assumption is stored in a structure or
passed as an opaque typeclass premise.
-/

namespace BGS.Markoff

noncomputable section

variable {K : Type*} [Field K]

/-! ### Finite presentations and the first-partial smooth chart -/

/-- The singleton family of equations presenting the affine trace cover. -/
def weightedSplitTraceRelationFamily (alpha beta : K) (d e : ℕ) (_ : Unit) :
    MvPolynomial (Fin 2) K := splitTraceCoverPolynomial alpha beta d e

def weightedSplitTraceAffinePresentationEquiv (alpha beta : K) (d e : ℕ) :
    (MvPolynomial (Fin 2) K ⧸ Ideal.span (Set.range
      (weightedSplitTraceRelationFamily alpha beta d e))) ≃ₐ[K]
      WeightedSplitTraceAffineCoordinateRing alpha beta d e :=
  Ideal.quotientEquivAlgOfEq K (by
    congr 1
    ext p
    simp [weightedSplitTraceRelationFamily, eq_comm])

def weightedSplitTraceAffineXPreSubmersivePresentation (alpha beta : K) (d e : ℕ) :
    Algebra.PreSubmersivePresentation K
      (WeightedSplitTraceAffineCoordinateRing alpha beta d e) (Fin 2) Unit :=
  (Algebra.PreSubmersivePresentation.naive
      (v := weightedSplitTraceRelationFamily alpha beta d e)
      (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _)).ofAlgEquiv
    (weightedSplitTraceAffinePresentationEquiv alpha beta d e)

noncomputable instance weightedSplitTraceAffineFinitePresentation (alpha beta : K) (d e : ℕ) :
    Algebra.FinitePresentation K
      (WeightedSplitTraceAffineCoordinateRing alpha beta d e) :=
  Algebra.Presentation.finitePresentation_of_isFinite
    (weightedSplitTraceAffineXPreSubmersivePresentation alpha beta d e).toPresentation

noncomputable instance weightedSplitTraceLaurentFinitePresentation (alpha beta : K) (d e : ℕ) :
    Algebra.FinitePresentation K
      (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) :=
  Algebra.FinitePresentation.trans K
    (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
    (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)

def weightedSplitTraceAffinePartialX (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceAffineCoordinateRing alpha beta d e :=
  Ideal.Quotient.mk _
    (MvPolynomial.pderiv 0 (splitTraceCoverPolynomial alpha beta d e))

theorem weightedSplitTraceAffineXPreSubmersivePresentation_jacobian
    (alpha beta : K) (d e : ℕ) :
    (weightedSplitTraceAffineXPreSubmersivePresentation alpha beta d e).jacobian =
      weightedSplitTraceAffinePartialX alpha beta d e := by
  let P := Algebra.PreSubmersivePresentation.naive
    (v := weightedSplitTraceRelationFamily alpha beta d e)
    (fun _ => 0) (fun _ _ _ => Subsingleton.elim _ _)
  let E := weightedSplitTraceAffinePresentationEquiv alpha beta d e
  change (P.ofAlgEquiv E).jacobian = weightedSplitTraceAffinePartialX alpha beta d e
  erw [Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique, Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
  change E (Ideal.Quotient.mk _
      (MvPolynomial.pderiv 0 (splitTraceCoverPolynomial alpha beta d e))) =
    Ideal.Quotient.mk _
      (MvPolynomial.pderiv 0 (splitTraceCoverPolynomial alpha beta d e))
  exact Ideal.quotientEquivAlgOfEq_mk K _ _

theorem weightedSplitTraceLaurentEval_eq_algebraMap_mk
    (alpha beta : K) (d e : ℕ) (p : MvPolynomial (Fin 2) K) :
    MvPolynomial.aeval
        ![weightedSplitTraceLaurentX alpha beta d e,
          weightedSplitTraceLaurentY alpha beta d e] p =
      algebraMap (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
        (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
        (Ideal.Quotient.mk _ p) := by
  let ev : MvPolynomial (Fin 2) K →ₐ[K]
      WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
    MvPolynomial.aeval
      ![weightedSplitTraceLaurentX alpha beta d e,
        weightedSplitTraceLaurentY alpha beta d e]
  let q : MvPolynomial (Fin 2) K →ₐ[K]
      WeightedSplitTraceAffineCoordinateRing alpha beta d e :=
    Ideal.Quotient.mkₐ K _
  let inclusion : WeightedSplitTraceAffineCoordinateRing alpha beta d e →ₐ[K]
      WeightedSplitTraceLaurentCoordinateRing alpha beta d e :=
    { toRingHom := algebraMap _ _
      commutes' := fun k => IsScalarTower.algebraMap_apply K
        (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
        (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) k }
  have h : ev =
      inclusion.comp q := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;>
      simp [ev, q, inclusion, AlgHom.comp_apply, weightedSplitTraceLaurentX,
        weightedSplitTraceLaurentY, weightedSplitTraceAffineX,
        weightedSplitTraceAffineY]
  change ev p = _
  rw [h]
  rfl

theorem weightedSplitTraceAffinePartialX_mapsToLaurent
    (alpha beta : K) (d e : ℕ) :
    algebraMap (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
        (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
        (weightedSplitTraceAffinePartialX alpha beta d e) =
      weightedSplitTraceLaurentPartialX alpha beta d e := by
  symm
  exact weightedSplitTraceLaurentEval_eq_algebraMap_mk alpha beta d e _

abbrev WeightedSplitTracePartialXLocalization (alpha beta : K) (d e : ℕ) :=
  Localization.Away (weightedSplitTraceLaurentPartialX alpha beta d e)

def weightedSplitTraceCoordinateProductPreSubmersivePresentation
    (alpha beta : K) (d e : ℕ) :
    Algebra.PreSubmersivePresentation
      (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
      (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) Unit Unit :=
  Algebra.PreSubmersivePresentation.localizationAway
    (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
    (weightedSplitTraceAffineCoordinateProduct alpha beta d e)

def weightedSplitTraceLaurentXPreSubmersivePresentation (alpha beta : K) (d e : ℕ) :
    Algebra.PreSubmersivePresentation K
      (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
      (Unit ⊕ Fin 2) (Unit ⊕ Unit) :=
  (weightedSplitTraceCoordinateProductPreSubmersivePresentation alpha beta d e).comp
    (weightedSplitTraceAffineXPreSubmersivePresentation alpha beta d e)

def weightedSplitTracePartialXLocalizationPreSubmersivePresentation
    (alpha beta : K) (d e : ℕ) :
    Algebra.PreSubmersivePresentation
      (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
      (WeightedSplitTracePartialXLocalization alpha beta d e) Unit Unit :=
  Algebra.PreSubmersivePresentation.localizationAway
    (WeightedSplitTracePartialXLocalization alpha beta d e)
    (weightedSplitTraceLaurentPartialX alpha beta d e)

def weightedSplitTracePartialXCompositePresentation
    (alpha beta : K) (d e : ℕ) :
    Algebra.PreSubmersivePresentation K
      (WeightedSplitTracePartialXLocalization alpha beta d e)
      (Unit ⊕ (Unit ⊕ Fin 2)) (Unit ⊕ (Unit ⊕ Unit)) :=
  (weightedSplitTracePartialXLocalizationPreSubmersivePresentation alpha beta d e).comp
    (weightedSplitTraceLaurentXPreSubmersivePresentation alpha beta d e)

theorem weightedSplitTracePartialXCompositePresentation_jacobian_isUnit
    (alpha beta : K) (d e : ℕ) :
    IsUnit (weightedSplitTracePartialXCompositePresentation alpha beta d e).jacobian := by
  let A := WeightedSplitTraceAffineCoordinateRing alpha beta d e
  let L := WeightedSplitTraceLaurentCoordinateRing alpha beta d e
  let Lx := WeightedSplitTracePartialXLocalization alpha beta d e
  let P₀ := weightedSplitTraceAffineXPreSubmersivePresentation alpha beta d e
  let Qxy := weightedSplitTraceCoordinateProductPreSubmersivePresentation alpha beta d e
  let P₁ := weightedSplitTraceLaurentXPreSubmersivePresentation alpha beta d e
  let Qx := weightedSplitTracePartialXLocalizationPreSubmersivePresentation alpha beta d e
  have hP₀ : IsUnit (algebraMap L Lx (algebraMap A L P₀.jacobian)) := by
    rw [show P₀.jacobian = weightedSplitTraceAffinePartialX alpha beta d e by
      exact weightedSplitTraceAffineXPreSubmersivePresentation_jacobian alpha beta d e]
    rw [weightedSplitTraceAffinePartialX_mapsToLaurent]
    exact IsLocalization.Away.algebraMap_isUnit
      (S := Lx) (weightedSplitTraceLaurentPartialX alpha beta d e)
  have hQxy : IsUnit (algebraMap L Lx Qxy.jacobian) := by
    rw [show Qxy.jacobian = algebraMap A L
        (weightedSplitTraceAffineCoordinateProduct alpha beta d e) by
      exact Algebra.PreSubmersivePresentation.localizationAway_jacobian _]
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := L) (weightedSplitTraceAffineCoordinateProduct alpha beta d e)).map
        (algebraMap L Lx)
  have hQx : IsUnit Qx.jacobian := by
    rw [show Qx.jacobian = algebraMap L Lx
        (weightedSplitTraceLaurentPartialX alpha beta d e) by
      exact Algebra.PreSubmersivePresentation.localizationAway_jacobian _]
    exact IsLocalization.Away.algebraMap_isUnit
      (S := Lx) (weightedSplitTraceLaurentPartialX alpha beta d e)
  change IsUnit (Qx.comp P₁).jacobian
  rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.smul_def]
  have hP₁ : IsUnit (algebraMap L Lx P₁.jacobian) := by
    change IsUnit (algebraMap L Lx (Qxy.comp P₀).jacobian)
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def, map_mul]
    exact hP₀.mul hQxy
  exact hP₁.mul hQx

def weightedSplitTracePartialXSubmersivePresentation
    (alpha beta : K) (d e : ℕ) :
    Algebra.SubmersivePresentation K
      (WeightedSplitTracePartialXLocalization alpha beta d e)
      (Unit ⊕ (Unit ⊕ Fin 2)) (Unit ⊕ (Unit ⊕ Unit)) where
  toPreSubmersivePresentation :=
    weightedSplitTracePartialXCompositePresentation alpha beta d e
  jacobian_isUnit :=
    weightedSplitTracePartialXCompositePresentation_jacobian_isUnit alpha beta d e

theorem weightedSplitTracePartialXLocalization_isStandardSmooth
    (alpha beta : K) (d e : ℕ) :
    Algebra.IsStandardSmooth K
      (WeightedSplitTracePartialXLocalization alpha beta d e) :=
  (weightedSplitTracePartialXSubmersivePresentation alpha beta d e).isStandardSmooth

theorem weightedSplitTracePartialXLocalization_smooth
    (alpha beta : K) (d e : ℕ) :
    Algebra.Smooth K (WeightedSplitTracePartialXLocalization alpha beta d e) := by
  let : Algebra.IsStandardSmooth K
      (WeightedSplitTracePartialXLocalization alpha beta d e) :=
    weightedSplitTracePartialXLocalization_isStandardSmooth alpha beta d e
  infer_instance

/-! ### The second-partial smooth chart -/

/-- The affine second partial derivative, before localization at the coordinate product. -/
def weightedSplitTraceAffinePartialY (alpha beta : K) (d e : ℕ) :
    WeightedSplitTraceAffineCoordinateRing alpha beta d e :=
  Ideal.Quotient.mk _
    (MvPolynomial.pderiv 1 (splitTraceCoverPolynomial alpha beta d e))

/-- The hypersurface presentation selecting the `y` column of its Jacobian matrix. -/
def weightedSplitTraceAffineYPreSubmersivePresentation
    (alpha beta : K) (d e : ℕ) :
    Algebra.PreSubmersivePresentation K
      (WeightedSplitTraceAffineCoordinateRing alpha beta d e) (Fin 2) Unit :=
  (Algebra.PreSubmersivePresentation.naive
      (v := weightedSplitTraceRelationFamily alpha beta d e)
      (fun _ => 1) (fun _ _ _ => Subsingleton.elim _ _)).ofAlgEquiv
    (weightedSplitTraceAffinePresentationEquiv alpha beta d e)

theorem weightedSplitTraceAffineYPreSubmersivePresentation_jacobian
    (alpha beta : K) (d e : ℕ) :
    (weightedSplitTraceAffineYPreSubmersivePresentation alpha beta d e).jacobian =
      weightedSplitTraceAffinePartialY alpha beta d e := by
  let P := Algebra.PreSubmersivePresentation.naive
    (v := weightedSplitTraceRelationFamily alpha beta d e)
    (fun _ => 1) (fun _ _ _ => Subsingleton.elim _ _)
  let E := weightedSplitTraceAffinePresentationEquiv alpha beta d e
  change (P.ofAlgEquiv E).jacobian = weightedSplitTraceAffinePartialY alpha beta d e
  erw [Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique, Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
  change E (Ideal.Quotient.mk _
      (MvPolynomial.pderiv 1 (splitTraceCoverPolynomial alpha beta d e))) =
    Ideal.Quotient.mk _
      (MvPolynomial.pderiv 1 (splitTraceCoverPolynomial alpha beta d e))
  exact Ideal.quotientEquivAlgOfEq_mk K _ _

theorem weightedSplitTraceAffinePartialY_mapsToLaurent
    (alpha beta : K) (d e : ℕ) :
    algebraMap (WeightedSplitTraceAffineCoordinateRing alpha beta d e)
        (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
        (weightedSplitTraceAffinePartialY alpha beta d e) =
      weightedSplitTraceLaurentPartialY alpha beta d e := by
  symm
  exact weightedSplitTraceLaurentEval_eq_algebraMap_mk alpha beta d e _

/-- The principal open on which the second partial derivative is invertible. -/
abbrev WeightedSplitTracePartialYLocalization (alpha beta : K) (d e : ℕ) :=
  Localization.Away (weightedSplitTraceLaurentPartialY alpha beta d e)

/-- Laurent presentation whose hypersurface Jacobian is the second partial derivative. -/
def weightedSplitTraceLaurentYPreSubmersivePresentation
    (alpha beta : K) (d e : ℕ) :
    Algebra.PreSubmersivePresentation K
      (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
      (Unit ⊕ Fin 2) (Unit ⊕ Unit) :=
  (weightedSplitTraceCoordinateProductPreSubmersivePresentation alpha beta d e).comp
    (weightedSplitTraceAffineYPreSubmersivePresentation alpha beta d e)

def weightedSplitTracePartialYLocalizationPreSubmersivePresentation
    (alpha beta : K) (d e : ℕ) :
    Algebra.PreSubmersivePresentation
      (WeightedSplitTraceLaurentCoordinateRing alpha beta d e)
      (WeightedSplitTracePartialYLocalization alpha beta d e) Unit Unit :=
  Algebra.PreSubmersivePresentation.localizationAway
    (WeightedSplitTracePartialYLocalization alpha beta d e)
    (weightedSplitTraceLaurentPartialY alpha beta d e)

def weightedSplitTracePartialYCompositePresentation
    (alpha beta : K) (d e : ℕ) :
    Algebra.PreSubmersivePresentation K
      (WeightedSplitTracePartialYLocalization alpha beta d e)
      (Unit ⊕ (Unit ⊕ Fin 2)) (Unit ⊕ (Unit ⊕ Unit)) :=
  (weightedSplitTracePartialYLocalizationPreSubmersivePresentation alpha beta d e).comp
    (weightedSplitTraceLaurentYPreSubmersivePresentation alpha beta d e)

theorem weightedSplitTracePartialYCompositePresentation_jacobian_isUnit
    (alpha beta : K) (d e : ℕ) :
    IsUnit (weightedSplitTracePartialYCompositePresentation alpha beta d e).jacobian := by
  let A := WeightedSplitTraceAffineCoordinateRing alpha beta d e
  let L := WeightedSplitTraceLaurentCoordinateRing alpha beta d e
  let Ly := WeightedSplitTracePartialYLocalization alpha beta d e
  let P₀ := weightedSplitTraceAffineYPreSubmersivePresentation alpha beta d e
  let Qxy := weightedSplitTraceCoordinateProductPreSubmersivePresentation alpha beta d e
  let P₁ := weightedSplitTraceLaurentYPreSubmersivePresentation alpha beta d e
  let Qy := weightedSplitTracePartialYLocalizationPreSubmersivePresentation alpha beta d e
  have hP₀ : IsUnit (algebraMap L Ly (algebraMap A L P₀.jacobian)) := by
    rw [show P₀.jacobian = weightedSplitTraceAffinePartialY alpha beta d e by
      exact weightedSplitTraceAffineYPreSubmersivePresentation_jacobian alpha beta d e]
    rw [weightedSplitTraceAffinePartialY_mapsToLaurent]
    exact IsLocalization.Away.algebraMap_isUnit
      (S := Ly) (weightedSplitTraceLaurentPartialY alpha beta d e)
  have hQxy : IsUnit (algebraMap L Ly Qxy.jacobian) := by
    rw [show Qxy.jacobian = algebraMap A L
        (weightedSplitTraceAffineCoordinateProduct alpha beta d e) by
      exact Algebra.PreSubmersivePresentation.localizationAway_jacobian _]
    exact (IsLocalization.Away.algebraMap_isUnit
      (S := L) (weightedSplitTraceAffineCoordinateProduct alpha beta d e)).map
        (algebraMap L Ly)
  have hQy : IsUnit Qy.jacobian := by
    rw [show Qy.jacobian = algebraMap L Ly
        (weightedSplitTraceLaurentPartialY alpha beta d e) by
      exact Algebra.PreSubmersivePresentation.localizationAway_jacobian _]
    exact IsLocalization.Away.algebraMap_isUnit
      (S := Ly) (weightedSplitTraceLaurentPartialY alpha beta d e)
  change IsUnit (Qy.comp P₁).jacobian
  rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    Algebra.smul_def]
  have hP₁ : IsUnit (algebraMap L Ly P₁.jacobian) := by
    change IsUnit (algebraMap L Ly (Qxy.comp P₀).jacobian)
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.smul_def, map_mul]
    exact hP₀.mul hQxy
  exact hP₁.mul hQy

def weightedSplitTracePartialYSubmersivePresentation
    (alpha beta : K) (d e : ℕ) :
    Algebra.SubmersivePresentation K
      (WeightedSplitTracePartialYLocalization alpha beta d e)
      (Unit ⊕ (Unit ⊕ Fin 2)) (Unit ⊕ (Unit ⊕ Unit)) where
  toPreSubmersivePresentation :=
    weightedSplitTracePartialYCompositePresentation alpha beta d e
  jacobian_isUnit :=
    weightedSplitTracePartialYCompositePresentation_jacobian_isUnit alpha beta d e

theorem weightedSplitTracePartialYLocalization_isStandardSmooth
    (alpha beta : K) (d e : ℕ) :
    Algebra.IsStandardSmooth K
      (WeightedSplitTracePartialYLocalization alpha beta d e) :=
  (weightedSplitTracePartialYSubmersivePresentation alpha beta d e).isStandardSmooth

theorem weightedSplitTracePartialYLocalization_smooth
    (alpha beta : K) (d e : ℕ) :
    Algebra.Smooth K (WeightedSplitTracePartialYLocalization alpha beta d e) := by
  let : Algebra.IsStandardSmooth K
      (WeightedSplitTracePartialYLocalization alpha beta d e) :=
    weightedSplitTracePartialYLocalization_isStandardSmooth alpha beta d e
  infer_instance

theorem weightedSplitTraceLaurent_smooth_of_partialLocalizations
    (alpha beta : K) (d e : ℕ)
    (hspan : Ideal.span {weightedSplitTraceLaurentPartialX alpha beta d e,
        weightedSplitTraceLaurentPartialY alpha beta d e} = ⊤)
    (hX : Algebra.Smooth K
      (Localization.Away (weightedSplitTraceLaurentPartialX alpha beta d e)))
    (hY : Algebra.Smooth K
      (Localization.Away (weightedSplitTraceLaurentPartialY alpha beta d e))) :
    Algebra.Smooth K (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) := by
  let L := WeightedSplitTraceLaurentCoordinateRing alpha beta d e
  let fx : L := weightedSplitTraceLaurentPartialX alpha beta d e
  let fy : L := weightedSplitTraceLaurentPartialY alpha beta d e
  have hXOpen : (PrimeSpectrum.basicOpen fx : Set (PrimeSpectrum L)) ⊆
      Algebra.smoothLocus K L :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hX
  have hYOpen : (PrimeSpectrum.basicOpen fy : Set (PrimeSpectrum L)) ⊆
      Algebra.smoothLocus K L :=
    Algebra.basicOpen_subset_smoothLocus_iff_smooth.mpr hY
  have hLocus : Algebra.smoothLocus K L = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases hpx : p ∈ PrimeSpectrum.basicOpen fx
    · exact hXOpen hpx
    by_cases hpy : p ∈ PrimeSpectrum.basicOpen fy
    · exact hYOpen hpy
    have hfx : fx ∈ p.asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using hpx
    have hfy : fy ∈ p.asIdeal := by
      simpa [PrimeSpectrum.mem_basicOpen] using hpy
    exfalso
    have hle : Ideal.span {fx, fy} ≤ p.asIdeal := by
      rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hfx
      · exact hfy
    have hpTop : p.asIdeal = ⊤ := top_unique (hspan ▸ hle)
    exact p.isPrime.ne_top hpTop
  exact ⟨(Algebra.smoothLocus_eq_univ_iff.mp hLocus), inferInstance⟩

/-- The Laurent trace-cover algebra is smooth over the ground field in the paper's
nondegenerate, characteristic-compatible range. -/
theorem weightedSplitTraceLaurent_smooth
    (alpha beta : K) (hnondegenerate : alpha * beta ≠ 1)
    (htwo : (2 : K) ≠ 0) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hdChar : (d : K) ≠ 0) (heChar : (e : K) ≠ 0) :
    Algebra.Smooth K
      (WeightedSplitTraceLaurentCoordinateRing alpha beta d e) :=
  weightedSplitTraceLaurent_smooth_of_partialLocalizations alpha beta d e
    (weightedSplitTraceLaurentPartials_span_top alpha beta hnondegenerate
      htwo d e hd he hdChar heChar)
    (weightedSplitTracePartialXLocalization_smooth alpha beta d e)
    (weightedSplitTracePartialYLocalization_smooth alpha beta d e)

end

end BGS.Markoff
