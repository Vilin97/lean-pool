/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectionWeightedTail
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLp
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentL2

/-!
# Finite-p transport under Neumann even reflection

The all-face Neumann reflection acts on vector fields by the coordinate-fold
linear isometries.  Its Euclidean norm therefore agrees pointwise with the
already-developed Dirichlet odd reflection, whose additional scalar sign has
unit modulus.  This file transfers the exact finite-`p` norm and weighted-tail
identities to the even reflection used by the Neumann good-`lambda` argument.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

open MeasureTheory
open CubeCalderonZygmund

/-- The stored normalized Euclidean `L²` witness gives the raw vector `L²`
datum required by the Neumann weak equation on the source open cube. -/
theorem CubeEuclideanL2LpField.memVectorL2_openCubeSet
    {d : ℕ} {Q : TriadicCube d} {p : FiniteLpExponent}
    (G : CubeEuclideanL2LpField Q p) :
    MemVectorL2 (openCubeSet Q) G.toField := by
  have hnormalized : MemLp (fun x ↦ HilbertVec.ofVec (G.toField x)) 2
      (cubeBoundedMeasurableDomain Q).normalizedVolume := by
    simpa only
      [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
      using G.euclideanMemL2
  have hrestricted : MemLp (fun x ↦ HilbertVec.ofVec (G.toField x)) 2
      (cubeBoundedMeasurableDomain Q).restrictedVolume :=
    ((cubeBoundedMeasurableDomain Q).memLp_normalizedVolume_iff 2 _).mp
      hnormalized
  have hopen : MemLp (fun x ↦ HilbertVec.ofVec (G.toField x)) 2
      (volume.restrict (openCubeSet Q)) := by
    simpa only
      [cubeBoundedMeasurableDomain_restrictedVolume_eq_restrict_openCubeSet]
      using hrestricted
  let T : HilbertVec d →L[ℝ] Vec d :=
    (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap
  simpa only [MemVectorL2, volumeMeasureOn, Function.comp_def,
    HilbertVec.toVec_ofVec, T] using! T.comp_memLp' hopen

/-- The Neumann even reflection and Dirichlet odd reflection have the same
pointwise Euclidean norm. -/
theorem norm_hilbertVec_ofVec_cubeCoordinateFoldReflectedVectorField_eq_oddReflection
    {d : ℕ} (Q : TriadicCube d) (G : Vec d → Vec d) (x : Vec d) :
    ‖HilbertVec.ofVec (cubeCoordinateFoldReflectedVectorField Q G x)‖ =
      ‖HilbertVec.ofVec (cubeDirichletOddReflectionVectorField Q G x)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [HilbertVec.norm_sq_ofVec, HilbertVec.norm_sq_ofVec]
  exact (cubeDirichletOddReflectionVectorField_self_pairing Q G x).symm

/-- Every `L^p` seminorm of the Neumann even reflection agrees with the
corresponding Dirichlet odd-reflection seminorm. -/
theorem eLpNorm_cubeCoordinateFoldReflectedVectorField_eq_oddReflection
    {d : ℕ} (Q : TriadicCube d) (G : Vec d → Vec d) (p : ℝ≥0∞)
    (mu : Measure (Vec d)) :
    eLpNorm
        (fun x ↦ HilbertVec.ofVec
          (cubeCoordinateFoldReflectedVectorField Q G x)) p mu =
      eLpNorm
        (fun x ↦ HilbertVec.ofVec
          (cubeDirichletOddReflectionVectorField Q G x)) p mu := by
  apply eLpNorm_congr_norm_ae
  filter_upwards with x
  exact
    norm_hilbertVec_ofVec_cubeCoordinateFoldReflectedVectorField_eq_oddReflection
      Q G x

/-- Exact finite-`p` scaling from a centered cube to its parent under Neumann
even reflection. -/
theorem eLpNorm_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
    {d : ℕ} {m : ℤ} (G : Vec d → Vec d) (p : FiniteLpExponent) :
    eLpNorm
        (fun x ↦ HilbertVec.ofVec
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x))
        p.exponent
        (volume.restrict (openCubeSet (originCube d (m + 1)))) =
      ((3 : ℝ≥0∞) ^ d) ^ (1 / p.exponent.toReal) *
        eLpNorm (fun x ↦ HilbertVec.ofVec (G x)) p.exponent
          (volume.restrict (openCubeSet (originCube d m))) := by
  rw [eLpNorm_cubeCoordinateFoldReflectedVectorField_eq_oddReflection]
  exact
    eLpNorm_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField
      G p

private theorem aestronglyMeasurable_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
    {d : ℕ} {m : ℤ} {G : Vec d → Vec d}
    (hG : AEStronglyMeasurable (fun x ↦ HilbertVec.ofVec (G x))
      (volume.restrict (openCubeSet (originCube d m)))) :
    AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec
        (cubeCoordinateFoldReflectedVectorField (originCube d m) G x))
      (volume.restrict (openCubeSet (originCube d (m + 1)))) := by
  classical
  have hmeasure :
      volume.restrict (openCubeSet (originCube d (m + 1))) =
        volume.restrict (cubeFaceReflectionBlockSet (originCube d m)) := by
    simpa using Measure.restrict_congr_set
      (cubeFaceReflectionBlockSet_originCube_ae_eq_openCubeSet_succ d m).symm
  rw [hmeasure, cubeFaceReflectionBlockSet_eq_iUnion_cellCube]
  apply AEStronglyMeasurable.iUnion
  intro choice
  let T : Vec d → Vec d :=
    cubeFaceReflectionCellFoldMap (originCube d m) choice
  have hmp : MeasurePreserving T
      (volume.restrict
        (openCubeSet
          (cubeFaceReflectionCellCube (originCube d m) choice)))
      (volume.restrict (openCubeSet (originCube d m))) := by
    simpa [T, preimage_cubeFaceReflectionCellFoldMap_openCubeSet] using
      (measurePreserving_cubeFaceReflectionCellFoldMap
        (originCube d m) choice).restrict_preimage_emb
          (measurableEmbedding_cubeFaceReflectionCellFoldMap
            (originCube d m) choice)
          (openCubeSet (originCube d m))
  have hcomp : AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec (G (T x)))
      (volume.restrict
        (openCubeSet
          (cubeFaceReflectionCellCube (originCube d m) choice))) := by
    have hGmap : AEStronglyMeasurable
        (fun x ↦ HilbertVec.ofVec (G x))
        (Measure.map T
          (volume.restrict
            (openCubeSet
              (cubeFaceReflectionCellCube (originCube d m) choice)))) := by
      rw [hmp.map_eq]
      exact hG
    simpa [Function.comp_def] using hGmap.comp_aemeasurable hmp.aemeasurable
  have hvec : AEStronglyMeasurable (fun x ↦ G (T x))
      (volume.restrict
        (openCubeSet
          (cubeFaceReflectionCellCube (originCube d m) choice))) := by
    simpa using
      (HilbertVec.continuousLinearEquivVec d).continuous.comp_aestronglyMeasurable
        hcomp
  have hlinear : AEStronglyMeasurable
      (fun x ↦ cubeFaceReflectionCellFoldLinear choice (G (T x)))
      (volume.restrict
        (openCubeSet
          (cubeFaceReflectionCellCube (originCube d m) choice))) :=
    (cubeFaceReflectionCellFoldLinear choice).continuous.comp_aestronglyMeasurable
      hvec
  have hhilbert : AEStronglyMeasurable
      (fun x ↦ HilbertVec.ofVec
        (cubeFaceReflectionCellFoldLinear choice (G (T x))))
      (volume.restrict
        (openCubeSet
          (cubeFaceReflectionCellCube (originCube d m) choice))) :=
    (HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable hlinear
  refine hhilbert.congr ?_
  filter_upwards
      [ae_restrict_mem
        (measurableSet_openCubeSet
          (cubeFaceReflectionCellCube (originCube d m) choice))] with x hx
  exact congrArg HilbertVec.ofVec
    (cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
      (originCube d m) choice G hx).symm

/-- Finite-`p` membership transports from a centered cube to its parent under
Neumann even reflection. -/
theorem memLp_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
    {d : ℕ} {m : ℤ} {G : Vec d → Vec d} (p : FiniteLpExponent)
    (hG : MemLp (fun x ↦ HilbertVec.ofVec (G x)) p.exponent
      (volume.restrict (openCubeSet (originCube d m)))) :
    MemLp
      (fun x ↦ HilbertVec.ofVec
        (cubeCoordinateFoldReflectedVectorField (originCube d m) G x))
      p.exponent
      (volume.restrict (openCubeSet (originCube d (m + 1)))) := by
  refine ⟨aestronglyMeasurable_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
      hG.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField]
  refine ENNReal.mul_lt_top ?_ hG.eLpNorm_lt_top
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (by simp)

private theorem normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet
    {d : ℕ} (m : ℤ) :
    normalizedCubeMeasure (originCube d m) =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
  rw [normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube]

private theorem restrict_openCubeSet_originCube_eq_smul_normalizedCubeMeasure
    {d : ℕ} (m : ℤ) :
    volume.restrict (openCubeSet (originCube d m)) =
      ENNReal.ofReal (cubeVolume (originCube d m)) •
        normalizedCubeMeasure (originCube d m) := by
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  rw [ENNReal.ofReal_inv_of_pos (cubeVolume_pos _), smul_smul]
  have hnonzero : ENNReal.ofReal (cubeVolume (originCube d m)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (cubeVolume_pos _)
  have hone : ENNReal.ofReal (cubeVolume (originCube d m)) *
      (ENNReal.ofReal (cubeVolume (originCube d m)))⁻¹ = 1 := by
    simpa [mul_comm] using
      ENNReal.inv_mul_cancel hnonzero ENNReal.ofReal_ne_top
  rw [hone, one_smul]

/-- Normalized finite-`p` norms are exactly preserved from a centered cube to
its parent under Neumann even reflection. -/
theorem eLpNorm_normalizedCubeMeasure_succ_originCube_cubeCoordinateFoldReflectedVectorField
    {d : ℕ} {m : ℤ} (G : Vec d → Vec d) (p : FiniteLpExponent) :
    eLpNorm
        (fun x ↦ HilbertVec.ofVec
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x))
        p.exponent (normalizedCubeMeasure (originCube d (m + 1))) =
      eLpNorm (fun x ↦ HilbertVec.ofVec (G x)) p.exponent
        (normalizedCubeMeasure (originCube d m)) := by
  rw [eLpNorm_cubeCoordinateFoldReflectedVectorField_eq_oddReflection]
  exact
    eLpNorm_normalizedCubeMeasure_succ_originCube_cubeDirichletOddReflectionVectorField
      G p

/-- Normalized finite-`p` membership is preserved by Neumann even reflection. -/
theorem memLp_normalizedCubeMeasure_succ_originCube_cubeCoordinateFoldReflectedVectorField
    {d : ℕ} {m : ℤ} {G : Vec d → Vec d} (p : FiniteLpExponent)
    (hG : MemLp (fun x ↦ HilbertVec.ofVec (G x)) p.exponent
      (normalizedCubeMeasure (originCube d m))) :
    MemLp
      (fun x ↦ HilbertVec.ofVec
        (cubeCoordinateFoldReflectedVectorField (originCube d m) G x))
      p.exponent (normalizedCubeMeasure (originCube d (m + 1))) := by
  have hGopen : MemLp (fun x ↦ HilbertVec.ofVec (G x)) p.exponent
      (volume.restrict (openCubeSet (originCube d m))) := by
    rw [restrict_openCubeSet_originCube_eq_smul_normalizedCubeMeasure]
    exact hG.smul_measure ENNReal.ofReal_ne_top
  have hreflect :=
    memLp_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField
      p hGopen
  rw [normalizedCubeMeasure_originCube_eq_smul_restrict_openCubeSet]
  exact hreflect.smul_measure ENNReal.ofReal_ne_top

/-- Radial nonnegative integrals on the reflected parent consist of exactly
`3^d` copies of the source-cube integral. -/
theorem lintegral_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_comp_norm
    {d : ℕ} {m : ℤ} (G : Vec d → Vec d) (Phi : ℝ → ℝ≥0∞) :
    ∫⁻ x in openCubeSet (originCube d (m + 1)),
        Phi ‖HilbertVec.ofVec
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)‖
          ∂volume =
      ((3 : ℝ≥0∞) ^ d) *
        ∫⁻ y in openCubeSet (originCube d m),
          Phi ‖HilbertVec.ofVec (G y)‖ ∂volume := by
  calc
    ∫⁻ x in openCubeSet (originCube d (m + 1)),
        Phi ‖HilbertVec.ofVec
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)‖
          ∂volume =
      ∫⁻ x in openCubeSet (originCube d (m + 1)),
        Phi ‖HilbertVec.ofVec
          (cubeDirichletOddReflectionVectorField (originCube d m) G x)‖
          ∂volume := by
            apply lintegral_congr
            intro x
            rw [norm_hilbertVec_ofVec_cubeCoordinateFoldReflectedVectorField_eq_oddReflection]
    _ = _ :=
      lintegral_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_comp_norm
        G Phi

/-- Square-weighted level tails have the exact `3^d` reflection factor under
Neumann even reflection. -/
theorem sqWeightedMeasure_openCubeSet_succ_originCube_cubeCoordinateFoldReflectedVectorField_tail
    {d : ℕ} {m : ℤ} (G : Vec d → Vec d) {a : ℝ}
    (hG : AEStronglyMeasurable (fun x ↦ HilbertVec.ofVec (G x))
      (volume.restrict (openCubeSet (originCube d m)))) :
    sqWeightedMeasure
        (fun x ↦ HilbertVec.ofVec
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)) volume
        ({x | a < ‖HilbertVec.ofVec
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)‖} ∩
          openCubeSet (originCube d (m + 1))) =
      ((3 : ℝ≥0∞) ^ d) *
        sqWeightedMeasure (fun x ↦ HilbertVec.ofVec (G x)) volume
          ({x | a < ‖HilbertVec.ofVec (G x)‖} ∩
            openCubeSet (originCube d m)) := by
  let E : Vec d → HilbertVec d := fun x ↦ HilbertVec.ofVec
    (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)
  let O : Vec d → HilbertVec d := fun x ↦ HilbertVec.ofVec
    (cubeDirichletOddReflectionVectorField (originCube d m) G x)
  have hnorm : ∀ x, ‖E x‖ = ‖O x‖ := fun x ↦
    norm_hilbertVec_ofVec_cubeCoordinateFoldReflectedVectorField_eq_oddReflection
      (originCube d m) G x
  have hmeasure : sqWeightedMeasure E volume = sqWeightedMeasure O volume := by
    apply MeasureTheory.withDensity_congr_ae
    filter_upwards with x
    rw [hnorm x]
  have htail : {x | a < ‖E x‖} = {x | a < ‖O x‖} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [hnorm x]
  change sqWeightedMeasure E volume
      ({x | a < ‖E x‖} ∩ openCubeSet (originCube d (m + 1))) = _
  rw [hmeasure, htail]
  exact
    sqWeightedMeasure_openCubeSet_succ_originCube_cubeDirichletOddReflectionVectorField_tail
      G hG

/-- Reflect an `L² ∩ L^p` datum to the centered parent cube, preserving both
stored normalized memberships exactly. -/
noncomputable def CubeEuclideanL2LpField.neumannEvenReflectionToParent
    {d : ℕ} {m : ℤ} {p : FiniteLpExponent}
    (G : CubeEuclideanL2LpField (originCube d m) p) :
    CubeEuclideanL2LpField (originCube d (m + 1)) p where
  toField := cubeCoordinateFoldReflectedVectorField (originCube d m) G.toField
  euclideanMemLp :=
    memLp_normalizedCubeMeasure_succ_originCube_cubeCoordinateFoldReflectedVectorField
      p G.euclideanMemLp
  euclideanMemL2 := by
    simpa only [FiniteLpExponent.two_exponent] using
      memLp_normalizedCubeMeasure_succ_originCube_cubeCoordinateFoldReflectedVectorField
        FiniteLpExponent.two G.euclideanMemL2

@[simp] theorem CubeEuclideanL2LpField.neumannEvenReflectionToParent_toField
    {d : ℕ} {m : ℤ} {p : FiniteLpExponent}
    (G : CubeEuclideanL2LpField (originCube d m) p) :
    G.neumannEvenReflectionToParent.toField =
      cubeCoordinateFoldReflectedVectorField (originCube d m) G.toField :=
  rfl

end

end Homogenization
