/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Examples.Periodic.PeriodicConcreteComparison
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.FaceVanishCollar
public import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CubeVectorH1

/-!
# Classical flux periodic comparison corollary

**Proves.** `periodicSmooth_comparison` — the periodic comparison estimate stated
entirely in *classical* terms over the explicit field `a(x) = m(x) • I`.  The
solutions `u`, `v` are smooth (`ContDiff ℝ ⊤`) scalar fields solving the
divergence-form equations `∇·(a∇u) = ∇·g` and `∇·(ā∇v) = ∇·g` pointwise, with
`u − v` vanishing on the cube faces; the defect and data are written with the
classical gradient.  The weak `H¹` comparison datum required by the public theorem
is *constructed* from this classical data (`classicalFluxComparisonPair`) by
genuine integration by parts (`integral_vecDot_grad_eq_neg_integral_euclideanDivergence`),
so no weak-solution hypothesis is assumed.

**Comparator.** `Audit/PeriodicSmooth` checks a Mathlib-only restatement of this
theorem against the proof below.  See `Audit/README.md` for the comparator map.

**Progression.** abstract theorem (`Audit/QuenchedComparison`) → general periodic
(`PeriodicGeneralComparison`, `Audit/PeriodicGeneral`) → explicit field
(`PeriodicConcreteComparison`, `Audit/PeriodicConcrete`) → *classical data (this
file)*.
-/

@[expose] public section

namespace Homogenization
namespace Examples
namespace Periodic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Package a smooth scalar field as an `H¹` function on the public origin
cube. -/
noncomputable def classicalH1OnOriginCube {d : ℕ} [NeZero d] (m : ℕ)
    (u : Vec d → ℝ) (hu : ContDiff ℝ 1 u) :
    H1Function (Book.Ch02.cubeDomain (Book.MainResults.originCube d m) : Set (Vec d)) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain
    (by
      simpa [Book.Ch02.cubeDomain_coe] using
        isOpenBoundedConvexDomain_openCubeSet (Book.MainResults.originCube d m))
    hu

@[simp] theorem classicalH1OnOriginCube_toFun {d : ℕ} [NeZero d] (m : ℕ)
    (u : Vec d → ℝ) (hu : ContDiff ℝ 1 u) :
    (classicalH1OnOriginCube (d := d) m u hu).toFun = u := by
  simp [classicalH1OnOriginCube, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain]

@[simp] theorem classicalH1OnOriginCube_grad {d : ℕ} [NeZero d] (m : ℕ)
    (u : Vec d → ℝ) (hu : ContDiff ℝ 1 u) :
    (classicalH1OnOriginCube (d := d) m u hu).grad = euclideanGradient u := by
  funext x i
  simp [classicalH1OnOriginCube, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
    H1Function.ofContDiffOnIsSobolevRegularDomain, euclideanGradient, euclideanCoordDeriv]

/-- Classical pointwise divergence of a smooth vector field,
`(∇·F)(x) = ∑ᵢ ∂ᵢ Fᵢ(x)`. -/
def euclideanDivergence {d : ℕ} (F : Vec d → Vec d) : Vec d → ℝ :=
  fun x => ∑ i : Fin d, euclideanCoordDeriv i (fun y => F y i) x

/-- Package a `C¹` vector field as a coordinatewise `H¹` competitor on the
public origin cube. -/
noncomputable def classicalCubeVectorH1 {d : ℕ} [NeZero d] (m : ℕ)
    (F : Vec d → Vec d) (hF : ContDiff ℝ 1 F) :
    CubeVectorH1Function (Book.MainResults.originCube d m) where
  coord i := classicalH1OnOriginCube (d := d) m (fun x => F x i) (contDiff_pi.mp hF i)

@[simp] theorem classicalCubeVectorH1_toField {d : ℕ} [NeZero d] (m : ℕ)
    (F : Vec d → Vec d) (hF : ContDiff ℝ 1 F) :
    (classicalCubeVectorH1 (d := d) m F hF).toField = F := by
  funext x i
  simp [classicalCubeVectorH1, CubeVectorH1Function.toField]

@[simp] theorem classicalCubeVectorH1_divergence {d : ℕ} [NeZero d] (m : ℕ)
    (F : Vec d → Vec d) (hF : ContDiff ℝ 1 F) :
    (classicalCubeVectorH1 (d := d) m F hF).divergence = euclideanDivergence F := by
  funext x
  simp only [CubeVectorH1Function.divergence, classicalCubeVectorH1,
    euclideanDivergence]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [classicalH1OnOriginCube_grad]
  rfl

/-- Integration by parts against a zero-trace test function: for a `C¹` vector
field `F` and `φ ∈ H¹₀`, `∫ F·∇φ = − ∫ (∇·F) φ` on the public origin cube. -/
theorem integral_vecDot_grad_eq_neg_integral_euclideanDivergence
    {d : ℕ} [NeZero d] (m : ℕ) (F : Vec d → Vec d) (hF : ContDiff ℝ 1 F)
    (φ : H10Function (openCubeSet (Book.MainResults.originCube d m))) :
    ∫ x in openCubeSet (Book.MainResults.originCube d m),
        vecDot (F x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
      -∫ x in openCubeSet (Book.MainResults.originCube d m),
        euclideanDivergence F x * φ.toH1Function x ∂MeasureTheory.volume := by
  have h :=
    (classicalCubeVectorH1 (d := d) m F hF).integral_divergence_mul_zeroTrace_eq_neg_integral_vecDot φ
  rw [classicalCubeVectorH1_divergence, classicalCubeVectorH1_toField] at h
  linarith [h]

/-- Classical pointwise divergence data packaged as the weak comparison pair used
by the homogenization comparison theorem.  The two scalar solutions are smooth and
satisfy the divergence-form equations `∇·(a∇u) = ∇·g` and `∇·(ā∇v) = ∇·g`
pointwise; the weak `H¹` datum is obtained by integration by parts. -/
noncomputable def classicalFluxComparisonPair {d : ℕ} [NeZero d]
    (S : Book.MainResults.Setup d)
    (aω : RegCoeffField d) (ha : Book.Ch04.AELocallyUniformlyEllipticField aω)
    (m : ℕ) (u v : Vec d → ℝ) (g : Vec d → Vec d)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (hg : ContDiff ℝ 1 g)
    (haflux : ContDiff ℝ 1 (fun x => matVecMul (aω x) (euclideanGradient u x)))
    (hvflux : ContDiff ℝ 1
      (fun x => matVecMul S.homogenizedMatrix.matrix (euclideanGradient v x)))
    (hlower_zero : ∀ i : Fin d, ∀ x : Vec d,
      (u - v) (cubeLowerFaceProjection (Book.MainResults.originCube d m) i x) = 0)
    (hupper_zero : ∀ i : Fin d, ∀ x : Vec d,
      (u - v) (cubeUpperFaceProjection (Book.MainResults.originCube d m) i x) = 0)
    (hu_div : ∀ x : Vec d,
      euclideanDivergence (fun y => matVecMul (aω y) (euclideanGradient u y)) x =
        euclideanDivergence g x)
    (hv_div : ∀ x : Vec d,
      euclideanDivergence
          (fun y => matVecMul S.homogenizedMatrix.matrix (euclideanGradient v y)) x =
        euclideanDivergence g x) :
    S.ComparisonPair aω ha m g := by
  let Q := Book.MainResults.originCube d m
  let uH1 :
      H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)) :=
    classicalH1OnOriginCube (d := d) m u (hu.of_le (by simp))
  let vH1 :
      H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)) :=
    classicalH1OnOriginCube (d := d) m v (hv.of_le (by simp))
  refine
    { u := uH1
      v := vH1
      uWeakSolution := ?_
      vWeakSolution := ?_
      zeroTraceDifference := ?_ }
  · intro φ
    simp only [Book.Ch02.cubeDomain_coe]
    have key1 := integral_vecDot_grad_eq_neg_integral_euclideanDivergence (d := d) m
      (fun x => matVecMul (aω x) (euclideanGradient u x)) haflux φ
    have keyg := integral_vecDot_grad_eq_neg_integral_euclideanDivergence (d := d) m g hg φ
    have hdiv :
        (∫ x in openCubeSet Q,
            euclideanDivergence (fun y => matVecMul (aω y) (euclideanGradient u y)) x *
              φ.toH1Function x ∂MeasureTheory.volume)
          = ∫ x in openCubeSet Q,
              euclideanDivergence g x * φ.toH1Function x ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      rw [hu_div x]
    trans (∫ x in openCubeSet Q,
        vecDot (matVecMul (aω x) (euclideanGradient u x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume)
    · refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      simp [uH1, Book.Ch05.Section57.assemblyCoeffFamily]
    · rw [key1, hdiv, ← keyg]
  · intro φ
    simp only [Book.Ch02.cubeDomain_coe]
    have key1 := integral_vecDot_grad_eq_neg_integral_euclideanDivergence (d := d) m
      (fun x => matVecMul S.homogenizedMatrix.matrix (euclideanGradient v x)) hvflux φ
    have keyg := integral_vecDot_grad_eq_neg_integral_euclideanDivergence (d := d) m g hg φ
    have hdiv :
        (∫ x in openCubeSet Q,
            euclideanDivergence
                (fun y => matVecMul S.homogenizedMatrix.matrix (euclideanGradient v y)) x *
              φ.toH1Function x ∂MeasureTheory.volume)
          = ∫ x in openCubeSet Q,
              euclideanDivergence g x * φ.toH1Function x ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      rw [hv_div x]
    trans (∫ x in openCubeSet Q,
        vecDot (matVecMul S.homogenizedMatrix.matrix (euclideanGradient v x))
          (φ.toH1Function.grad x) ∂MeasureTheory.volume)
    · refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with x
      simp [vH1, Book.MainResults.Setup.homogenizedMatrix,
        Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
        Book.Ch05.Section57.scalarConstantCoeffMatrix_matrix]
    · rw [key1, hdiv, ← keyg]
  · let w : H10Function (Book.Ch02.cubeDomain Q : Set (Vec d)) := by
      simpa [Book.Ch02.cubeDomain_coe, Q] using
        H10Function.ofContDiffFaceZeroOnOpenCubeSetNoCompact Q
          (hu.sub hv) hlower_zero hupper_zero
    refine ⟨w, ?_⟩
    simpa [w, uH1, vH1, Q, sub_eq_add_neg, Book.Ch02.cubeDomain_coe] using
      H10Function.ofContDiffFaceZeroOnOpenCubeSetNoCompact_toFun_ae
        Q (hu.sub hv) hlower_zero hupper_zero

/-- The constant-coefficient part of the classical comparison defect. -/
noncomputable def classicalComparisonConstantGradientField {d : ℕ}
    (abar : Mat d) (u v : Vec d → ℝ) : Vec d → Vec d :=
  fun x => matVecMul abar (euclideanGradient u x - euclideanGradient v x)

/-- The flux part of the classical comparison defect. -/
noncomputable def classicalComparisonFluxField {d : ℕ}
    (a : CoeffField d) (abar : Mat d) (u v : Vec d → ℝ) : Vec d → Vec d :=
  fun x => matVecMul (a x) (euclideanGradient u x) -
    matVecMul abar (euclideanGradient v x)

/-- The legacy dual-Besov classical compatibility defect appearing in the smooth
periodic corollary. -/
noncomputable def classicalComparisonDefect {d : ℕ} [NeZero d]
    (abar : Mat d) (s : ℝ) (a : CoeffField d) (m : ℕ)
    (u v : Vec d → ℝ) : ℝ :=
  Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
      (Book.MainResults.originCube d m) s
      (classicalComparisonConstantGradientField abar u v) +
    Book.Ch03.Legacy.scaleNormalizedNegativeSobolevVectorNormTwo
      (Book.MainResults.originCube d m) s
      (classicalComparisonFluxField a abar u v)

/-- The energy norm of a smooth classical field on a cube. -/
noncomputable def classicalH1EnergyNormOnCube {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → ℝ) : ℝ :=
  Real.sqrt <|
    volumeAverage (openCubeSet Q) fun x =>
      vecDot (euclideanGradient u x)
        (matVecMul (symmPart (a x)) (euclideanGradient u x))

/-- The classical data norm controlling the smooth periodic compatibility
defect; its force term is legacy fractional-Sobolev. -/
noncomputable def classicalComparisonData {d : ℕ} [NeZero d]
    (sigmaBar : ℝ) (s : ℝ) (a : CoeffField d) (m : ℕ)
    (g : Vec d → Vec d) (u : Vec d → ℝ) : ℝ :=
  Real.sqrt sigmaBar *
      classicalH1EnergyNormOnCube (Book.MainResults.originCube d m) a u +
    Book.Ch03.Legacy.scaleNormalizedPositiveSobolevVectorSeminormTwo
      (Book.MainResults.originCube d m) s g

/--
Fixed-exponent quenched homogenization comparison for smooth classical flux
data over the explicit periodic coefficient field.
-/
theorem periodicSmooth_comparison {d : ℕ} [NeZero d] :
    ∃ C alpha Cscale : ℝ,
      0 < C ∧ 0 < alpha ∧ 0 < Cscale ∧
      ∀ (two_le_dim : 2 ≤ d),
        let Lam : ℝ := 2 * (d : ℝ) + 2
        let S : Book.MainResults.Setup d :=
          periodicSetup two_le_dim (mFieldReg (d := d)) 2 Lam
            mFieldCoeff_periodic mFieldCoeff_isotropic mFieldCoeff_adjointInvariant
            (by norm_num)
            (by
              nlinarith [show 0 ≤ (d : ℝ) by exact_mod_cast Nat.zero_le d])
            (fun Q => mFieldReg_aeeEllipticOn (measurableSet_openCubeSet Q))
        ∃ sigmaBar : ℝ,
          0 < sigmaBar ∧
          ∃ X : RegCoeffField d → ℝ,
            S.IsMinimalScale X Cscale ∧
            ∀ᵐ aω ∂S.P,
              ∀ (_ha : Book.Ch04.AELocallyUniformlyEllipticField aω)
                {m : ℕ} {u v : Vec d → ℝ} {g : Vec d → Vec d}
                (_hu : ContDiff ℝ (⊤ : ℕ∞) u)
                (_hv : ContDiff ℝ (⊤ : ℕ∞) v)
                (_hg : ContDiff ℝ 1 g)
                (_haflux : ContDiff ℝ 1
                  (fun x => matVecMul (aω x) (euclideanGradient u x)))
                (_hvflux : ContDiff ℝ 1
                  (fun x => matVecMul (scalarMatrix (d := d) sigmaBar) (euclideanGradient v x)))
                (_hlower_zero : ∀ i : Fin d, ∀ x : Vec d,
                  (u - v) (cubeLowerFaceProjection (Book.MainResults.originCube d m) i x) = 0)
                (_hupper_zero : ∀ i : Fin d, ∀ x : Vec d,
                  (u - v) (cubeUpperFaceProjection (Book.MainResults.originCube d m) i x) = 0)
                (_hu_div : ∀ x : Vec d,
                  euclideanDivergence (fun y => matVecMul (aω y) (euclideanGradient u y)) x =
                    euclideanDivergence g x)
                (_hv_div : ∀ x : Vec d,
                  euclideanDivergence
                      (fun y =>
                        matVecMul (scalarMatrix (d := d) sigmaBar) (euclideanGradient v y)) x =
                    euclideanDivergence g x),
                X aω ≤ (3 : ℝ) ^ m →
                Book.Ch03.Legacy.ForceSobolevRegularity
                  (Book.MainResults.originCube d m) Book.MainResults.fixedComparisonS g →
                classicalComparisonDefect (scalarMatrix (d := d) sigmaBar)
                    Book.MainResults.fixedComparisonS aω.toFun m u v ≤
                  C * ((3 : ℝ) ^ m / X aω) ^ (-alpha) *
                    classicalComparisonData sigmaBar
                      Book.MainResults.fixedComparisonS aω.toFun m g u := by
  obtain ⟨C, alpha, Cscale, hC, halpha, hCscale, hmain⟩ :=
    periodicConcrete_comparison (d := d)
  refine ⟨C, alpha, Cscale, hC, halpha, hCscale, ?_⟩
  intro two_le_dim
  let Lam : ℝ := 2 * (d : ℝ) + 2
  let S : Book.MainResults.Setup d :=
    periodicSetup two_le_dim (mFieldReg (d := d)) 2 Lam
      mFieldCoeff_periodic mFieldCoeff_isotropic mFieldCoeff_adjointInvariant
      (by norm_num)
      (by
        nlinarith [show 0 ≤ (d : ℝ) by exact_mod_cast Nat.zero_le d])
      (fun Q => mFieldReg_aeeEllipticOn (measurableSet_openCubeSet Q))
  let sigmaBar : ℝ := Book.Ch05.Section57.barSigmaLimit S.hP S.hStruct
  have hsigma : 0 < sigmaBar := by
    dsimp [sigmaBar]
    exact S.barSigmaLimit_pos
  obtain ⟨_sigmaBar, _hsigma, X, hX, hmainS⟩ := hmain two_le_dim
  refine ⟨sigmaBar, hsigma, X, hX, ?_⟩
  filter_upwards [hmainS] with aω hmain_aω
  intro ha m u v g hu hv hg haflux hvflux hlower_zero hupper_zero hu_div hv_div hXm hgsob
  have hMat : S.homogenizedMatrix.matrix = scalarMatrix (d := d) sigmaBar := by
    simp [sigmaBar, Book.MainResults.Setup.homogenizedMatrix,
      Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
      Book.Ch05.Section57.scalarConstantCoeffMatrix_matrix]
  let pair : S.ComparisonPair aω ha m g :=
    classicalFluxComparisonPair S aω ha m u v g hu hv hg haflux
      (by rw [hMat]; exact hvflux)
      hlower_zero hupper_zero hu_div
      (by intro x; rw [hMat]; exact hv_div x)
  have hstep := hmain_aω ha pair hXm hgsob
  simpa [pair, Book.MainResults.Setup.comparisonDefect,
    Book.MainResults.Setup.comparisonData, Book.MainResults.Setup.homogenizedMatrix,
    Book.Ch03.Legacy.homogenizationComparisonNegativeSobolevLHS,
    Book.Ch03.homogenizationComparisonConstantGradientField,
    Book.Ch03.homogenizationComparisonFluxField,
    Book.Ch03.h1EnergyNormOnCube, Book.Ch03.localizedCoeffEnergyValue,
    Book.Ch03.normalizedSetAverage,
    Book.Ch05.Section57.assemblyCoeffFamily,
    Book.Ch05.Section57.assemblyConstantCoeffMatrixOfScalar,
    Book.Ch05.Section57.scalarConstantCoeffMatrix_matrix,
    Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField,
    Book.Ch04.coeffOnOfAEEllipticOn,
    Book.Ch02.cubeDomain_coe,
    classicalComparisonDefect, classicalComparisonData,
    classicalComparisonConstantGradientField, classicalComparisonFluxField,
    classicalH1EnergyNormOnCube, classicalFluxComparisonPair,
    classicalH1OnOriginCube, volumeAverage] using! hstep

end

end Periodic
end Examples
end Homogenization
