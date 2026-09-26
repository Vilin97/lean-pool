/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.ScalarizationDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Finite.Properties
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MultiscaleEllipticity.Public
public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Theorems.CoarseObservables
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Widetilde Theta -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

/-!
# Moment roots and `widetildeTheta`

Clean Ch4 definitions of the scalar moment roots used to compare the primitive
contrast `Theta_n` to the moment-enhanced quantity `widetildeTheta_n`.
-/

open MeasureTheory
open scoped Matrix.Norms.L2Operator BigOperators

noncomputable section

/-- The annealed `L^ξ` moment root of a nonnegative scalar observable. -/
noncomputable def annealedMomentRoot {d : ℕ}
    (P : RestrictionCoeffLaw d) (ξ : ℕ) (X : RegCoeffField d → ℝ) : ℝ :=
  (∫ a, X a ^ ξ ∂P) ^ (1 / (ξ : ℝ))

/-- The upper multiscale ellipticity observable on ambient coefficient fields.
On the a.e.-elliptic support it uses the canonical dependent Ch2 coefficient
family; off support it is totalized by `0`. -/
noncomputable def LambdaSqCoeffField {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (a : RegCoeffField d) : ℝ := by
  classical
  exact
    if h : AELocallyUniformlyEllipticField a then
      Ch02.LambdaSq Q s q (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h)
    else
      0

/-- The lower multiscale ellipticity observable on ambient coefficient fields.
On the a.e.-elliptic support it uses the canonical dependent Ch2 coefficient
family; off support it is totalized by `0`. -/
noncomputable def lambdaSqCoeffField {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s : ℝ) (q : Ch02.MultiscaleExponent)
    (a : RegCoeffField d) : ℝ := by
  classical
  exact
    if h : AELocallyUniformlyEllipticField a then
      Ch02.lambdaSq Q s q (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h)
    else
      0

private theorem cubeSet_translateCube_descendantTranslationShift_eq_translateSet_int
    {d : ℕ} (z : Fin d → ℤ) (n : ℕ) {R : TriadicCube d}
    (hRscale : R.scale = -((n : ℕ) : ℤ)) :
    cubeSet (translateCube (descendantTranslationShift n z) R) =
      translateSet (intVecToRealVec z) (cubeSet R) := by
  ext x
  rw [mem_cubeSet_translateCube_iff, mem_translateSet_iff_sub_mem]
  have hvec :
      (fun i => ((descendantTranslationShift n z i : ℤ) : ℝ) * cubeScaleFactor R) =
        intVecToRealVec z := by
    ext i
    simp [descendantTranslationShift, cubeScaleFactor, hRscale, intVecToRealVec]
    field_simp [pow_ne_zero n (by norm_num : (3 : ℝ) ≠ 0)]
  simp [hvec]

private theorem scale_eq_neg_natCast_of_mem_descendantsAtScale_originCube_zero
    {d : ℕ} {n : ℕ} {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ))) :
    R.scale = -((n : ℕ) : ℤ) := by
  have hk : (originCube d 0).scale - (n : ℤ) ≤ (originCube d 0).scale := by
    exact sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  have hscale := scale_eq_sub_of_mem_descendantsAtScale (Q := originCube d 0) hk hR
  simpa [originCube] using hscale

private theorem coarseBlockMatrix_translateCube_descendant_eq_translateByInt
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (z : Fin d → ℤ)
    (htranslate : AELocallyUniformlyEllipticField (translateReg (intVecToRealVec z) a))
    (n : ℕ) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ))) :
    Ch02.coarseBlockMatrix (Ch02.cubeDomain (translateCube (descendantTranslationShift n z) R))
        ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn
          (translateCube (descendantTranslationShift n z) R)) =
      Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
        ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (translateReg (intVecToRealVec z) a) htranslate).coeffOn R) := by
  let T : TriadicCube d := translateCube (descendantTranslationShift n z) R
  have hleft :
      Ch02.coarseBlockMatrix (Ch02.cubeDomain T)
          ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn T) =
        coarseBlockMatrix (cubeSet T) a.toFun := by
    simpa [T] using
      (RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha T).symm
  have hset : cubeSet T = translateSet (intVecToRealVec z) (cubeSet R) := by
    have hRscale := scale_eq_neg_natCast_of_mem_descendantsAtScale_originCube_zero hR
    simpa [T] using
      cubeSet_translateCube_descendantTranslationShift_eq_translateSet_int z n hRscale
  have hright :
      coarseBlockMatrix (cubeSet R) (translateReg (intVecToRealVec z) a).toFun =
        Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
          ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField
            (translateReg (intVecToRealVec z) a) htranslate).coeffOn R) := by
    simpa using
      RestrictionLawCarrier.coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        htranslate R
  calc
    Ch02.coarseBlockMatrix (Ch02.cubeDomain T)
        ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha).coeffOn T)
        = coarseBlockMatrix (cubeSet T) a.toFun := hleft
    _ = coarseBlockMatrix (translateSet (intVecToRealVec z) (cubeSet R)) a.toFun := by
          rw [hset]
    _ = coarseBlockMatrix (cubeSet R) (translateReg (intVecToRealVec z) a).toFun := by
          simpa [translateByInt] using!
            coarseBlockMatrix_translateSet_eq_translateCoeffField
              (intVecToRealVec z) (cubeSet R) a.toFun
    _ = Ch02.coarseBlockMatrix (Ch02.cubeDomain R)
        ((triadicCoeffFamilyOfAELocallyUniformlyEllipticField
          (translateReg (intVecToRealVec z) a) htranslate).coeffOn R) := hright

private theorem LambdaSqCoeffField_originCube_zero_translateByInt_pointwise
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (z : Fin d → ℤ)
    (htranslate : AELocallyUniformlyEllipticField (translateReg (intVecToRealVec z) a))
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    LambdaSqCoeffField (translateCube z (originCube d 0)) s q a =
      LambdaSqCoeffField (originCube d 0) s q (translateReg (intVecToRealVec z) a) := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField (translateReg (intVecToRealVec z) a) htranslate
  have hB : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)) →
        Ch02.coarseBMatrixNorm (translateCube (descendantTranslationShift n z) R) F =
          Ch02.coarseBMatrixNorm R G := by
    intro n R hR
    have hmat :
        Ch02.coarseBlockMatrix
            (Ch02.cubeDomain (translateCube (descendantTranslationShift n z) R))
            (F.coeffOn (translateCube (descendantTranslationShift n z) R)) =
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (G.coeffOn R) := by
      simpa [F, G] using
        coarseBlockMatrix_translateCube_descendant_eq_translateByInt
          (ha := ha) z (htranslate := htranslate) n hR
    have hupper := congrArg (fun A : BlockMat d => Ch02.matrixNorm A.upperLeft) hmat
    simpa [Ch02.coarseBMatrixNorm] using hupper
  have h := Ch02.LambdaSq_translateCube_of_coarseBMatrixNorm
    F G z (originCube d 0) s q hB
  simpa [LambdaSqCoeffField, ha, htranslate, F, G] using h

private theorem lambdaSqCoeffField_originCube_zero_translateByInt_pointwise
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (z : Fin d → ℤ)
    (htranslate : AELocallyUniformlyEllipticField (translateReg (intVecToRealVec z) a))
    (s : ℝ) (q : Ch02.MultiscaleExponent) :
    lambdaSqCoeffField (translateCube z (originCube d 0)) s q a =
      lambdaSqCoeffField (originCube d 0) s q (translateReg (intVecToRealVec z) a) := by
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  let G : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField (translateReg (intVecToRealVec z) a) htranslate
  have hSigma : ∀ (n : ℕ) (R : TriadicCube d),
      R ∈ descendantsAtScale (originCube d 0) ((originCube d 0).scale - (n : ℤ)) →
        Ch02.coarseSigmaStarInvMatrixNorm
            (translateCube (descendantTranslationShift n z) R) F =
          Ch02.coarseSigmaStarInvMatrixNorm R G := by
    intro n R hR
    have hmat :
        Ch02.coarseBlockMatrix
            (Ch02.cubeDomain (translateCube (descendantTranslationShift n z) R))
            (F.coeffOn (translateCube (descendantTranslationShift n z) R)) =
          Ch02.coarseBlockMatrix (Ch02.cubeDomain R) (G.coeffOn R) := by
      simpa [F, G] using
        coarseBlockMatrix_translateCube_descendant_eq_translateByInt
          (ha := ha) z (htranslate := htranslate) n hR
    have hlower := congrArg (fun A : BlockMat d => Ch02.matrixNorm A.lowerRight) hmat
    simpa [Ch02.coarseSigmaStarInvMatrixNorm] using hlower
  have h := Ch02.lambdaSq_translateCube_of_coarseSigmaStarInvMatrixNorm
    F G z (originCube d 0) s q hSigma
  simpa [lambdaSqCoeffField, ha, htranslate, F, G] using h

private theorem ae_locallyUniformlyEllipticField_translateByInt
    {d : ℕ} {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) (z : Fin d → ℤ) :
    ∀ᵐ a ∂P, AELocallyUniformlyEllipticField (translateReg (intVecToRealVec z) a) := by
  have hmapSupport :
      ∀ᵐ b ∂Measure.map (translateReg (intVecToRealVec z)) P, AELocallyUniformlyEllipticField b := by
    simpa [hstat z] using hP.ae_locallyUniformlyEllipticField
  exact MeasureTheory.ae_of_ae_map (measurable_translateReg (intVecToRealVec z)).aemeasurable hmapSupport

/-- Upper multiscale ellipticity on the scale-zero origin cube is covariant
under integer translations, almost surely under a stationary law carrier. -/
theorem LambdaSqCoeffField_originCube_zero_translateByInt_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) (z : Fin d → ℤ) (s : ℝ) (q : Ch02.MultiscaleExponent) :
    (fun a => LambdaSqCoeffField (translateCube z (originCube d 0)) s q a) =ᵐ[P]
      fun a => LambdaSqCoeffField (originCube d 0) s q (translateReg (intVecToRealVec z) a) := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField,
    ae_locallyUniformlyEllipticField_translateByInt hP hstat z] with a ha htranslate
  exact LambdaSqCoeffField_originCube_zero_translateByInt_pointwise ha z htranslate s q

/-- Lower multiscale ellipticity on the scale-zero origin cube is covariant
under integer translations, almost surely under a stationary law carrier. -/
theorem lambdaSqCoeffField_originCube_zero_translateByInt_ae
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (hstat : RestrictionStationaryLaw P) (z : Fin d → ℤ) (s : ℝ) (q : Ch02.MultiscaleExponent) :
    (fun a => lambdaSqCoeffField (translateCube z (originCube d 0)) s q a) =ᵐ[P]
      fun a => lambdaSqCoeffField (originCube d 0) s q (translateReg (intVecToRealVec z) a) := by
  filter_upwards [hP.ae_locallyUniformlyEllipticField,
    ae_locallyUniformlyEllipticField_translateByInt hP hstat z] with a ha htranslate
  exact lambdaSqCoeffField_originCube_zero_translateByInt_pointwise ha z htranslate s q

theorem LambdaSqCoeffField_finite_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {s q : ℝ} (a : RegCoeffField d)
    (hs : 0 < s) (hq : 1 ≤ q) :
    0 ≤ LambdaSqCoeffField Q s (.finite q) a := by
  classical
  by_cases h : AELocallyUniformlyEllipticField a
  · have hnonneg :
        0 ≤ Ch02.LambdaSq Q s (.finite q)
          (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h) :=
      Ch02.LambdaSq_finite_nonneg Q
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h) hs hq
    simpa [LambdaSqCoeffField, h] using hnonneg
  · simp [LambdaSqCoeffField, h]

theorem lambdaSqCoeffField_finite_nonneg {d : ℕ} [NeZero d]
    (Q : TriadicCube d) {s q : ℝ} (a : RegCoeffField d)
    (hs : 0 < s) (hq : 1 ≤ q) :
    0 ≤ lambdaSqCoeffField Q s (.finite q) a := by
  classical
  by_cases h : AELocallyUniformlyEllipticField a
  · have hnonneg :
        0 ≤ Ch02.lambdaSq Q s (.finite q)
          (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h) :=
      Ch02.lambdaSq_finite_nonneg Q
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h) hs hq
    simpa [lambdaSqCoeffField, h] using hnonneg
  · simp [lambdaSqCoeffField, h]

/-- Ambient coefficient-field lift of the Ch2 descendant upper-left operator
norm maximum.  It uses the canonical dependent Ch2 coefficient family on the
a.e.-locally elliptic support and is zero off that support. -/
noncomputable def maxDescendantBMatrixNormCoeffFieldAtScale {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (k : ℤ) (a : RegCoeffField d) : ℝ := by
  classical
  exact
    if h : AELocallyUniformlyEllipticField a then
      Ch02.maxDescendantBMatrixNormAtScale Q k
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h)
    else
      0

/-- Ambient coefficient-field lift of the Ch2 descendant lower-right inverse
operator-norm maximum. -/
noncomputable def maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (k : ℤ)
    (a : RegCoeffField d) : ℝ := by
  classical
  exact
    if h : AELocallyUniformlyEllipticField a then
      Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h)
    else
      0

namespace RestrictionLawCarrier

theorem finsetSupReal_eq_sup' {α : Type*}
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    Ch02.finsetSupReal s f = s.sup' hs f := by
  apply le_antisymm
  · exact Ch02.finsetSupReal_le s hs (fun x hx => Finset.le_sup' f hx)
  · refine Finset.sup'_le hs f ?_
    intro x hx
    unfold Ch02.finsetSupReal
    have hbdd : BddAbove (f '' (↑s : Set α)) :=
      ((Set.toFinite _).image f).bddAbove
    exact le_csSup hbdd ⟨x, hx, rfl⟩

/-- Finite nonempty suprema of almost-everywhere measurable real observables
remain almost-everywhere measurable. -/
theorem aemeasurable_finset_sup'
    {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Finset ι} (hs : s.Nonempty)
    {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (s.sup' hs f) μ :=
  Finset.sup'_induction (s := s) (H := hs) (f := f)
    (p := fun g => AEMeasurable g μ)
    (fun _f hf' _g hg' => hf'.sup hg')
    (fun i hi => hf i hi)

theorem maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (k : ℤ) :
    maxDescendantBMatrixNormCoeffFieldAtScale Q k a =
      Ch02.finsetSupReal (descendantsAtScale Q k)
        (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft) := by
  classical
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hnorm : ∀ R ∈ descendantsAtScale Q k,
      Ch02.coarseBMatrixNorm R F =
        Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft := by
    intro R _hR
    have hmat :=
      coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha R
    have hupper :=
      congrArg (fun A : BlockMat d => Ch02.matrixNorm A.upperLeft) hmat
    simpa [Ch02.coarseBMatrixNorm, F] using hupper.symm
  simpa [maxDescendantBMatrixNormCoeffFieldAtScale,
    Ch02.maxDescendantBMatrixNormAtScale, ha, F] using
    Ch02.finsetSupReal_congr (descendantsAtScale Q k) hnorm

theorem maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
    {d : ℕ} [NeZero d] {a : RegCoeffField d}
    (ha : AELocallyUniformlyEllipticField a) (Q : TriadicCube d) (k : ℤ) :
    maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q k a =
      Ch02.finsetSupReal (descendantsAtScale Q k)
        (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight) := by
  classical
  let F : Ch02.TriadicCoeffFamily d :=
    triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
  have hnorm : ∀ R ∈ descendantsAtScale Q k,
      Ch02.coarseSigmaStarInvMatrixNorm R F =
        Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight := by
    intro R _hR
    have hmat :=
      coarseBlockMatrix_cubeSet_eq_ch02_coarseBlockMatrix_of_aelocallyUniformlyEllipticField
        ha R
    have hlower :=
      congrArg (fun A : BlockMat d => Ch02.matrixNorm A.lowerRight) hmat
    simpa [Ch02.coarseSigmaStarInvMatrixNorm, F] using hlower.symm
  simpa [maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale,
    Ch02.maxDescendantSigmaStarInvMatrixNormAtScale, ha, F] using
    Ch02.finsetSupReal_congr (descendantsAtScale Q k) hnorm

private theorem aemeasurable_maxDescendantBMatrixNormCoeffFieldAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (n : ℕ) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a) P := by
  classical
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  let sDesc := descendantsAtScale Q (Q.scale - (n : ℤ))
  have hsDesc : sDesc.Nonempty :=
    descendantsAtScale_nonempty Q (sub_le_self Q.scale hn)
  have hsup :
      AEMeasurable
        (sDesc.sup' hsDesc
          (fun R (a : RegCoeffField d) =>
            Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft)) P := by
    refine aemeasurable_finset_sup' hsDesc ?_
    intro R _hR
    simpa [Ch02.matrixNorm, Matrix.l2_opNorm_toEuclideanCLM] using
      (hP.aemeasurable_coarseB_cubeSet R).norm
  have hfin :
      AEMeasurable
        (fun a : RegCoeffField d =>
          Ch02.finsetSupReal sDesc
            (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft)) P := by
    convert hsup using 1
    ext a
    rw [Finset.sup'_apply]
    exact finsetSupReal_eq_sup' sDesc hsDesc
      (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).upperLeft)
  refine hfin.congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  simpa [sDesc] using
    (maxDescendantBMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      (a := a) ha Q (Q.scale - (n : ℤ))).symm

private theorem aemeasurable_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) (n : ℕ) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
          Q (Q.scale - (n : ℤ)) a) P := by
  classical
  have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
  let sDesc := descendantsAtScale Q (Q.scale - (n : ℤ))
  have hsDesc : sDesc.Nonempty :=
    descendantsAtScale_nonempty Q (sub_le_self Q.scale hn)
  have hsup :
      AEMeasurable
        (sDesc.sup' hsDesc
          (fun R (a : RegCoeffField d) =>
            Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight)) P := by
    refine aemeasurable_finset_sup' hsDesc ?_
    intro R _hR
    simpa [Ch02.matrixNorm, Matrix.l2_opNorm_toEuclideanCLM] using
      (hP.aemeasurable_coarseSigmaStarInv_cubeSet R).norm
  have hfin :
      AEMeasurable
        (fun a : RegCoeffField d =>
          Ch02.finsetSupReal sDesc
            (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight)) P := by
    convert hsup using 1
    ext a
    rw [Finset.sup'_apply]
    exact finsetSupReal_eq_sup' sDesc hsDesc
      (fun R => Ch02.matrixNorm (coarseBlockMatrix (cubeSet R) a.toFun).lowerRight)
  refine hfin.congr ?_
  filter_upwards [hP.ae_locallyUniformlyEllipticField] with a ha
  simpa [sDesc] using
    (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale_eq_finsetSupReal_ae
      (a := a) ha Q (Q.scale - (n : ℤ))).symm

theorem summable_weighted_maxDescendantBMatrixNormCoeffFieldAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ =>
      Ch02.geometricWeight s 1 n *
        Real.rpow
          (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  classical
  by_cases ha : AELocallyUniformlyEllipticField a
  · simpa [maxDescendantBMatrixNormCoeffFieldAtScale, ha] using
      Ch02.summable_B_series_pointwiseCoeffField Q
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) hs
        (by norm_num : (0 : ℝ) < 1)
  · simp [maxDescendantBMatrixNormCoeffFieldAtScale, ha]

theorem summable_weighted_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ =>
      Ch02.geometricWeight s 1 n *
        Real.rpow
          (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
            Q (Q.scale - (n : ℤ)) a)
          (1 / 2 : ℝ)) := by
  classical
  by_cases ha : AELocallyUniformlyEllipticField a
  · simpa [maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha] using
      Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q
        (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha) hs
        (by norm_num : (0 : ℝ) < 1)
  · simp [maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha]

private theorem aemeasurable_tsum_weighted_maxDescendantBMatrixNormCoeffFieldAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        ∑' n : ℕ,
          Ch02.geometricWeight s 1 n *
            Real.rpow
              (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) P := by
  refine
    aemeasurable_of_tendsto_metrizable_ae (Filter.atTop : Filter ℕ)
      (f := fun N a =>
        ∑ n ∈ Finset.range N,
          Ch02.geometricWeight s 1 n *
            Real.rpow
              (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ))
      (g := fun a =>
        ∑' n : ℕ,
          Ch02.geometricWeight s 1 n *
            Real.rpow
              (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) ?_ ?_
  · intro N
    refine Finset.aemeasurable_fun_sum (μ := P)
      (f := fun n (a : RegCoeffField d) =>
        Ch02.geometricWeight s 1 n *
          Real.rpow
            (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) (Finset.range N) ?_
    intro n _hn
    have hpow :
        AEMeasurable
          (fun a : RegCoeffField d =>
            Real.rpow
              (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) P :=
      by
        have hrpow : Measurable (fun x : ℝ => Real.rpow x (1 / 2 : ℝ)) :=
          (Real.continuous_rpow_const (by positivity : 0 ≤ (1 / 2 : ℝ))).measurable
        exact hrpow.comp_aemeasurable
          (aemeasurable_maxDescendantBMatrixNormCoeffFieldAtScale hP Q n)
    exact hpow.const_mul (Ch02.geometricWeight s 1 n)
  · exact Filter.Eventually.of_forall fun a =>
      HasSum.tendsto_sum_nat
        ((summable_weighted_maxDescendantBMatrixNormCoeffFieldAtScale Q a hs).hasSum)

private theorem aemeasurable_tsum_weighted_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    AEMeasurable
      (fun a : RegCoeffField d =>
        ∑' n : ℕ,
          Ch02.geometricWeight s 1 n *
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) P := by
  refine
    aemeasurable_of_tendsto_metrizable_ae (Filter.atTop : Filter ℕ)
      (f := fun N a =>
        ∑ n ∈ Finset.range N,
          Ch02.geometricWeight s 1 n *
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ))
      (g := fun a =>
        ∑' n : ℕ,
          Ch02.geometricWeight s 1 n *
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) ?_ ?_
  · intro N
    refine Finset.aemeasurable_fun_sum (μ := P)
      (f := fun n (a : RegCoeffField d) =>
        Ch02.geometricWeight s 1 n *
          Real.rpow
            (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) (Finset.range N) ?_
    intro n _hn
    have hpow :
        AEMeasurable
          (fun a : RegCoeffField d =>
            Real.rpow
              (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                Q (Q.scale - (n : ℤ)) a)
              (1 / 2 : ℝ)) P :=
      by
        have hrpow : Measurable (fun x : ℝ => Real.rpow x (1 / 2 : ℝ)) :=
          (Real.continuous_rpow_const (by positivity : 0 ≤ (1 / 2 : ℝ))).measurable
        exact hrpow.comp_aemeasurable
          (aemeasurable_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale hP Q n)
    exact hpow.const_mul (Ch02.geometricWeight s 1 n)
  · exact Filter.Eventually.of_forall fun a =>
      HasSum.tendsto_sum_nat
        ((summable_weighted_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale Q a hs).hasSum)

theorem LambdaSqCoeffField_finite_one_eq_tsum_sq
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d) (s : ℝ) :
    LambdaSqCoeffField Q s (.finite 1) a =
      (∑' n : ℕ,
        Ch02.geometricWeight s 1 n *
          Real.rpow
            (maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) ^ 2 := by
  classical
  by_cases ha : AELocallyUniformlyEllipticField a
  · simp [LambdaSqCoeffField, Ch02.LambdaSqFinite,
      maxDescendantBMatrixNormCoeffFieldAtScale, ha]
  · simp [LambdaSqCoeffField, maxDescendantBMatrixNormCoeffFieldAtScale, ha]

theorem lambdaSqCoeffField_finite_one_eq_tsum_sq_inv
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {s : ℝ} (hs : 0 < s) :
    lambdaSqCoeffField Q s (.finite 1) a =
      ((∑' n : ℕ,
        Ch02.geometricWeight s 1 n *
          Real.rpow
            (maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
              Q (Q.scale - (n : ℤ)) a)
            (1 / 2 : ℝ)) ^ 2)⁻¹ := by
  classical
  by_cases ha : AELocallyUniformlyEllipticField a
  · let F : Ch02.TriadicCoeffFamily d :=
      triadicCoeffFamilyOfAELocallyUniformlyEllipticField a ha
    let S : ℝ :=
      ∑' n : ℕ,
        Ch02.geometricWeight s 1 n *
          Real.rpow
            (Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (n : ℤ)) F)
            (1 / 2 : ℝ)
    have hS_nonneg : 0 ≤ S := by
      simpa [S] using
        Ch02.lambdaSqFinite_series_nonneg Q s 1 F
          (by norm_num : (0 : ℝ) ≤ 1) (by simpa using hs.le)
    have hneg : Real.rpow S (-(2 : ℝ)) = (Real.rpow S (2 : ℝ))⁻¹ :=
      Real.rpow_neg hS_nonneg 2
    simp [lambdaSqCoeffField, Ch02.lambdaSqFinite,
      maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha]
  · simp [lambdaSqCoeffField, maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, ha]

/-- The upper all-scale coefficient observable at a deterministic triadic cube
is a.e.-measurable under a Chapter 4 law carrier. -/
theorem aemeasurable_LambdaSqCoeffField_finite_one
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    AEMeasurable
      (fun a : RegCoeffField d => LambdaSqCoeffField Q s (.finite 1) a) P := by
  have hS :=
    aemeasurable_tsum_weighted_maxDescendantBMatrixNormCoeffFieldAtScale hP Q hs
  refine (hS.mul hS).congr ?_
  filter_upwards with a
  simpa [pow_two] using (LambdaSqCoeffField_finite_one_eq_tsum_sq Q a s).symm

/-- The lower all-scale coefficient observable at a deterministic triadic cube
is a.e.-measurable under a Chapter 4 law carrier. -/
theorem aemeasurable_lambdaSqCoeffField_finite_one
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    AEMeasurable
      (fun a : RegCoeffField d => lambdaSqCoeffField Q s (.finite 1) a) P := by
  have hS :=
    aemeasurable_tsum_weighted_maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale hP Q hs
  refine (hS.mul hS).inv.congr ?_
  filter_upwards with a
  simpa [pow_two] using (lambdaSqCoeffField_finite_one_eq_tsum_sq_inv Q a hs).symm

/-- The inverse lower all-scale coefficient observable at a deterministic
triadic cube is a.e.-measurable under a Chapter 4 law carrier. -/
theorem aemeasurable_lambdaSqCoeffField_finite_one_inv
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier P)
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) :
    AEMeasurable
      (fun a : RegCoeffField d => (lambdaSqCoeffField Q s (.finite 1) a)⁻¹) P :=
  (hP.aemeasurable_lambdaSqCoeffField_finite_one Q hs).inv

end RestrictionLawCarrier

/-- The q=1 deterministic Jensen split for the ambient upper multiscale
ellipticity observable.  This is the Ch4-facing form of the Ch2 theorem, with
no probability or measurability assumptions. -/
theorem LambdaSqCoeffField_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {s : ℝ} (hs : 0 < s) :
    LambdaSqCoeffField Q s (.finite 1) a ≤
      ∑' n : ℕ,
        Ch02.geometricWeight s 1 n *
          maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a := by
  classical
  by_cases h : AELocallyUniformlyEllipticField a
  · simpa [LambdaSqCoeffField, maxDescendantBMatrixNormCoeffFieldAtScale, h] using
      Ch02.LambdaSq_finite_one_le_tsum_weighted_maxDescendantBMatrixNormAtScale
        Q (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h) hs
  · have htsum_nonneg :
        0 ≤
          ∑' n : ℕ,
            Ch02.geometricWeight s 1 n *
              maxDescendantBMatrixNormCoeffFieldAtScale Q (Q.scale - (n : ℤ)) a := by
      refine tsum_nonneg fun n => ?_
      simp [maxDescendantBMatrixNormCoeffFieldAtScale, h]
    simpa [LambdaSqCoeffField, h] using htsum_nonneg

/-- The q=1 deterministic Jensen split for the ambient lower inverse
multiscale ellipticity observable. -/
theorem lambdaSqCoeffField_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : RegCoeffField d)
    {s : ℝ} (hs : 0 < s) :
    (lambdaSqCoeffField Q s (.finite 1) a)⁻¹ ≤
      ∑' n : ℕ,
        Ch02.geometricWeight s 1 n *
          maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
            Q (Q.scale - (n : ℤ)) a := by
  classical
  by_cases h : AELocallyUniformlyEllipticField a
  · simpa [lambdaSqCoeffField,
      maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, h] using
      Ch02.lambdaSq_finite_one_inv_le_tsum_weighted_maxDescendantSigmaStarInvMatrixNormAtScale
        Q (triadicCoeffFamilyOfAELocallyUniformlyEllipticField a h) hs
  · have htsum_nonneg :
        0 ≤
          ∑' n : ℕ,
            Ch02.geometricWeight s 1 n *
              maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale
                Q (Q.scale - (n : ℤ)) a := by
      refine tsum_nonneg fun n => ?_
      simp [maxDescendantSigmaStarInvMatrixNormCoeffFieldAtScale, h]
    simpa [lambdaSqCoeffField, h] using htsum_nonneg

/-- Upper multiscale ellipticity moment at scale `n`. -/
noncomputable def LambdaMomentAtScale {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ) (s : ℝ) (ξ : ℕ) : ℝ :=
  annealedMomentRoot P ξ
    (fun a => LambdaSqCoeffField (originCube d n) s (.finite 1) a)

/-- Lower inverse multiscale ellipticity moment at scale `n`. -/
noncomputable def lambdaInvMomentAtScale {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ) (s : ℝ) (ξ : ℕ) : ℝ :=
  annealedMomentRoot P ξ
    (fun a => (lambdaSqCoeffField (originCube d n) s (.finite 1) a)⁻¹)

/-- The moment-enhanced contrast `\widetilde\Theta_n`. -/
noncomputable def widetildeThetaAtScale {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ) (sUpper sLower : ℝ) (ξ : ℕ) : ℝ :=
  LambdaMomentAtScale P n sUpper ξ * lambdaInvMomentAtScale P n sLower ξ

theorem annealedMomentRoot_nonneg_of_nonneg {d : ℕ}
    (P : RestrictionCoeffLaw d) (ξ : ℕ) {X : RegCoeffField d → ℝ}
    (hX : ∀ a, 0 ≤ X a) :
    0 ≤ annealedMomentRoot P ξ X := by
  rw [annealedMomentRoot]
  exact Real.rpow_nonneg
    (MeasureTheory.integral_nonneg fun a => pow_nonneg (hX a) ξ) _

/-- Monotonicity of the annealed moment root under a.e. domination of
nonnegative observables. -/
theorem annealedMomentRoot_le_of_ae_nonneg_le {d : ℕ} {P : RestrictionCoeffLaw d}
    {ξ : ℕ} {X Y : RegCoeffField d → ℝ}
    (hξ : 1 ≤ ξ)
    (hX_nonneg : ∀ a, 0 ≤ X a)
    (hX_int : Integrable (fun a => X a ^ ξ) P)
    (hY_int : Integrable (fun a => Y a ^ ξ) P)
    (hXY : X ≤ᵐ[P] Y) :
    annealedMomentRoot P ξ X ≤ annealedMomentRoot P ξ Y := by
  have hpow :
      (fun a => X a ^ ξ) ≤ᵐ[P] fun a => Y a ^ ξ := by
    filter_upwards [hXY] with a hle
    exact pow_le_pow_left₀ (hX_nonneg a) hle ξ
  have hInt_le :
      ∫ a, X a ^ ξ ∂P ≤ ∫ a, Y a ^ ξ ∂P :=
    integral_mono_ae hX_int hY_int hpow
  have hIntX_nonneg : 0 ≤ ∫ a, X a ^ ξ ∂P := by
    exact integral_nonneg fun a => pow_nonneg (hX_nonneg a) ξ
  have hExp_nonneg : 0 ≤ 1 / (ξ : ℝ) := by
    positivity
  simpa [annealedMomentRoot] using
    Real.rpow_le_rpow hIntX_nonneg hInt_le hExp_nonneg

theorem LambdaMomentAtScale_nonneg {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ) {s : ℝ} (ξ : ℕ)
    (hs : 0 < s) :
    0 ≤ LambdaMomentAtScale P n s ξ :=
  annealedMomentRoot_nonneg_of_nonneg P ξ fun a =>
    LambdaSqCoeffField_finite_nonneg (originCube d n) a hs (by norm_num : (1 : ℝ) ≤ 1)

theorem lambdaInvMomentAtScale_nonneg {d : ℕ} [NeZero d]
    (P : RestrictionCoeffLaw d) (n : ℤ) {s : ℝ} (ξ : ℕ)
    (hs : 0 < s) :
    0 ≤ lambdaInvMomentAtScale P n s ξ :=
  annealedMomentRoot_nonneg_of_nonneg P ξ fun a =>
    inv_nonneg.mpr
      (lambdaSqCoeffField_finite_nonneg (originCube d n) a hs (by norm_num : (1 : ℝ) ≤ 1))

private theorem toReal_eLpNorm_eq_integral_abs_pow_rpow_inv
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} {p : ℕ}
    (hp : 1 ≤ p) (hf : AEStronglyMeasurable f μ)
    (hLp_int : Integrable (fun ω => |f ω| ^ p) μ) :
    ENNReal.toReal (eLpNorm f (p : ENNReal) μ) =
      (∫ ω, |f ω| ^ p ∂μ) ^ (1 / (p : ℝ)) := by
  have hp_nat_ne_zero : p ≠ 0 := by omega
  have h_memLp : MemLp f (p : ENNReal) μ := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hf
      (by exact_mod_cast hp_nat_ne_zero) (by simp)]
    simpa [Real.norm_eq_abs] using hLp_int
  have hnonneg :
      0 ≤ (∫ a, ‖f a‖ ^ (p : ENNReal).toReal ∂μ) ^
        (p : ENNReal).toReal⁻¹ := by
    positivity
  rw [h_memLp.eLpNorm_eq_integral_rpow_norm
      (by exact_mod_cast hp_nat_ne_zero) (by simp),
    ENNReal.toReal_ofReal hnonneg]
  simp [Real.norm_eq_abs, one_div]

/-- Root decomposition for a nonnegative observable controlled by a
deterministic base plus a nonnegative error:
`||X||_ξ <= A + ||E||_ξ` when `X <= A + E`.

This is the Ch4-owned scalar Minkowski step used in the Section 5.2 moment
lemma. -/
theorem annealedMomentRoot_le_const_add_of_nonneg_le
    {d : ℕ} {P : RestrictionCoeffLaw d} [IsProbabilityMeasure P]
    {ξ : ℕ} {X E : RegCoeffField d → ℝ} {A : ℝ}
    (hξ : 1 ≤ ξ) (hA_nonneg : 0 ≤ A)
    (hX_nonneg : ∀ a, 0 ≤ X a)
    (hE_nonneg : ∀ a, 0 ≤ E a)
    (hX_le : ∀ a, X a ≤ A + E a)
    (hX_meas : AEMeasurable X P)
    (hE_meas : AEMeasurable E P)
    (hX_int : Integrable (fun a => |X a| ^ ξ) P)
    (hE_int : Integrable (fun a => |E a| ^ ξ) P) :
    annealedMomentRoot P ξ X ≤ A + annealedMomentRoot P ξ E := by
  have hξ_enn : (1 : ENNReal) ≤ (ξ : ENNReal) := by exact_mod_cast hξ
  have hξ_ne : ξ ≠ 0 := by omega
  have hE_memLp : MemLp E (ξ : ENNReal) P := by
    rw [← MeasureTheory.integrable_norm_rpow_iff hE_meas.aestronglyMeasurable
      (by exact_mod_cast hξ_ne) (by simp)]
    simpa [Real.norm_eq_abs] using hE_int
  have hP_ne_zero : (P : Measure (RegCoeffField d)) ≠ 0 := by
    exact IsProbabilityMeasure.ne_zero P
  have hConst_toReal :
      ENNReal.toReal (eLpNorm (fun _ : RegCoeffField d => A) (ξ : ENNReal) P) = A := by
    have hξ_enn_ne_zero : (ξ : ENNReal) ≠ 0 := by exact_mod_cast hξ_ne
    rw [MeasureTheory.eLpNorm_const (μ := P) (c := A) (p := (ξ : ENNReal))
      hξ_enn_ne_zero hP_ne_zero]
    simp [IsProbabilityMeasure.measure_univ, Real.norm_eq_abs, abs_of_nonneg hA_nonneg]
  have hConst_ne_top :
      eLpNorm (fun _ : RegCoeffField d => A) (ξ : ENNReal) P ≠ ⊤ := by
    have hξ_enn_ne_zero : (ξ : ENNReal) ≠ 0 := by exact_mod_cast hξ_ne
    rw [MeasureTheory.eLpNorm_const (μ := P) (c := A) (p := (ξ : ENNReal))
      hξ_enn_ne_zero hP_ne_zero]
    simp
  have hX_toReal :
      ENNReal.toReal (eLpNorm X (ξ : ENNReal) P) =
        annealedMomentRoot P ξ X := by
    calc
      ENNReal.toReal (eLpNorm X (ξ : ENNReal) P)
          = (∫ a, |X a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) :=
              toReal_eLpNorm_eq_integral_abs_pow_rpow_inv hξ
                hX_meas.aestronglyMeasurable hX_int
      _ = (∫ a, X a ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            congr 1
            exact integral_congr_ae
              (Filter.Eventually.of_forall fun a => by
                simp [abs_of_nonneg (hX_nonneg a)])
      _ = annealedMomentRoot P ξ X := rfl
  have hE_toReal :
      ENNReal.toReal (eLpNorm E (ξ : ENNReal) P) =
        annealedMomentRoot P ξ E := by
    calc
      ENNReal.toReal (eLpNorm E (ξ : ENNReal) P)
          = (∫ a, |E a| ^ ξ ∂P) ^ (1 / (ξ : ℝ)) :=
              toReal_eLpNorm_eq_integral_abs_pow_rpow_inv hξ
                hE_meas.aestronglyMeasurable hE_int
      _ = (∫ a, E a ^ ξ ∂P) ^ (1 / (ξ : ℝ)) := by
            congr 1
            exact integral_congr_ae
              (Filter.Eventually.of_forall fun a => by
                simp [abs_of_nonneg (hE_nonneg a)])
      _ = annealedMomentRoot P ξ E := rfl
  have hmono :
      eLpNorm X (ξ : ENNReal) P ≤
        eLpNorm (fun a : RegCoeffField d => A + E a) (ξ : ENNReal) P :=
    MeasureTheory.eLpNorm_mono fun a => by
      have hX_abs : |X a| = X a := abs_of_nonneg (hX_nonneg a)
      have hAE_nonneg : 0 ≤ A + E a := add_nonneg hA_nonneg (hE_nonneg a)
      have hAE_abs : |A + E a| = A + E a := abs_of_nonneg hAE_nonneg
      simpa [Real.norm_eq_abs, hX_abs, hAE_abs] using hX_le a
  have hadd :
      eLpNorm (fun a : RegCoeffField d => A + E a) (ξ : ENNReal) P ≤
        eLpNorm (fun _ : RegCoeffField d => A) (ξ : ENNReal) P +
          eLpNorm E (ξ : ENNReal) P := by
    simpa [Pi.add_apply] using!
      (MeasureTheory.eLpNorm_add_le
        (aestronglyMeasurable_const (μ := P) (b := A))
        hE_meas.aestronglyMeasurable hξ_enn)
  have hsum_ne_top :
      eLpNorm (fun _ : RegCoeffField d => A) (ξ : ENNReal) P +
          eLpNorm E (ξ : ENNReal) P ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hConst_ne_top, hE_memLp.2.ne⟩
  calc
    annealedMomentRoot P ξ X =
        ENNReal.toReal (eLpNorm X (ξ : ENNReal) P) := hX_toReal.symm
    _ ≤ ENNReal.toReal
        (eLpNorm (fun _ : RegCoeffField d => A) (ξ : ENNReal) P +
          eLpNorm E (ξ : ENNReal) P) :=
        ENNReal.toReal_mono hsum_ne_top (le_trans hmono hadd)
    _ = A + annealedMomentRoot P ξ E := by
        rw [ENNReal.toReal_add hConst_ne_top hE_memLp.2.ne, hConst_toReal, hE_toReal]

/-- Internal primitive factor bounds imply `Theta_n <= widetildeTheta_n`. -/
theorem Internal.annealedThetaAtScaleOfPrimitive_le_widetildeThetaAtScale_of_factor_bounds
    {d : ℕ} [NeZero d] {P : RestrictionCoeffLaw d} {n : ℤ}
    {sUpper sLower : ℝ} {ξ : ℕ}
    (primitive : Internal.AnnealedPrimitiveScalarizationData (d := d) P n)
    (hsUpper : 0 < sUpper)
    (hUpper : Internal.barBAtScaleOfPrimitive primitive ≤
      LambdaMomentAtScale P n sUpper ξ)
    (hStarInv_nonneg : 0 ≤ Internal.barSigmaStarInvAtScaleOfPrimitive primitive)
    (hLower : Internal.barSigmaStarInvAtScaleOfPrimitive primitive ≤
      lambdaInvMomentAtScale P n sLower ξ) :
    Internal.annealedThetaAtScaleOfPrimitive primitive ≤
      widetildeThetaAtScale P n sUpper sLower ξ := by
  exact mul_le_mul hUpper hLower hStarInv_nonneg
    (LambdaMomentAtScale_nonneg P n ξ hsUpper)

end

end Ch04
end Book
end Homogenization
