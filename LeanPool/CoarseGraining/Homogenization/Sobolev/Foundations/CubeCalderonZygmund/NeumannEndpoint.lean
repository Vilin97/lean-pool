/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.CubeTranslationFiniteP
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.Neumann.FiniteLpBelowTwo

/-!
# Arbitrary-cube Neumann Calderón--Zygmund endpoint

This file translates the centered finite-exponent Neumann estimate to an
arbitrary triadic cube and exposes it on the project's raw `Vec` norm.  The
datum needs only the stated finite-`Lᵖ` membership.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

private theorem memLp_hilbertify_of_memLp_vec_neumannEndpoint
    {d : ℕ} {p : ℝ≥0∞} {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp F p (normalizedCubeMeasure Q)) :
    MemLp (fun x ↦ HilbertVec.ofVec (F x)) p (normalizedCubeMeasure Q) := by
  simpa only [Function.comp_apply, HilbertVec.ofVecL_apply] using!
    (HilbertVec.ofVecL d).comp_memLp' hF

private theorem memLp_vec_of_memLp_hilbertify_neumannEndpoint
    {d : ℕ} {p : ℝ≥0∞} {Q : TriadicCube d} {F : Vec d → Vec d}
    (hF : MemLp (fun x ↦ HilbertVec.ofVec (F x)) p
      (normalizedCubeMeasure Q)) :
    MemLp F p (normalizedCubeMeasure Q) := by
  simpa only [Function.comp_apply, HilbertVec.continuousLinearEquivVec_apply,
    HilbertVec.toVec_ofVec] using!
    (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap.comp_memLp' hF

private theorem eLpNorm_vec_le_hilbertify_neumannEndpoint
    {d : ℕ} {p : ℝ≥0∞} {Q : TriadicCube d} (F : Vec d → Vec d) :
    eLpNorm F p (normalizedCubeMeasure Q) ≤
      eLpNorm (fun x ↦ HilbertVec.ofVec (F x)) p (normalizedCubeMeasure Q) := by
  apply eLpNorm_mono_ae
  filter_upwards [] with x
  exact HilbertVec.norm_le_norm_ofVec (F x)

private theorem eLpNorm_hilbertify_le_dimension_mul_vec_neumannEndpoint
    {d : ℕ} {p : ℝ≥0∞} {Q : TriadicCube d} (F : Vec d → Vec d) :
    eLpNorm (fun x ↦ HilbertVec.ofVec (F x)) p (normalizedCubeMeasure Q) ≤
      ENNReal.ofReal (d : ℝ) * eLpNorm F p (normalizedCubeMeasure Q) := by
  calc
    eLpNorm (fun x ↦ HilbertVec.ofVec (F x)) p (normalizedCubeMeasure Q) ≤
        eLpNorm (fun x ↦ (d : ℝ) • F x) p (normalizedCubeMeasure Q) := by
      apply eLpNorm_mono_ae
      filter_upwards [] with x
      simpa only [norm_smul, Real.norm_natCast] using
        HilbertVec.norm_ofVec_le_mul_norm (F x)
    _ = ENNReal.ofReal (d : ℝ) * eLpNorm F p (normalizedCubeMeasure Q) := by
      rw [show (fun x ↦ (d : ℝ) • F x) = (d : ℝ) • F by rfl,
        eLpNorm_const_smul]
      rw [Real.enorm_eq_ofReal]
      norm_num

private theorem centeredCubeNeumannDivergence_eLpNorm_le
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (f : Vec d → Vec d),
      MemLp f q.exponent (normalizedCubeMeasure (originCube d m)) →
      ∀ u : H1MeanZeroFunction (openCubeSet (originCube d m)),
        IsMeanZeroNeumannRhsWeakSolution
          (fun _ : Vec d ↦ (1 : Mat d)) (openCubeSet (originCube d m)) u
          (fun x ↦ -f x) →
        MemLp u.toH1Function.grad q.exponent
            (normalizedCubeMeasure (originCube d m)) ∧
          eLpNorm u.toH1Function.grad q.exponent
              (normalizedCubeMeasure (originCube d m)) ≤
            (C * ENNReal.ofReal (d : ℝ)) * eLpNorm f q.exponent
              (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH1MeanZeroNeumannDivergence_cz_lpData d q
  refine ⟨C, hCtop, ?_⟩
  intro m f hf u hu
  let h : CubeEuclideanLpField (originCube d m) q :=
    { toField := f
      euclideanMemLp := memLp_hilbertify_of_memLp_vec_neumannEndpoint hf }
  have huScalar : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ scalarMatrix (d := d) (1 : ℝ))
      (openCubeSet (originCube d m)) u (fun x ↦ -h.toField x) := by
    simpa only [h, scalarMatrix, one_smul] using hu
  have hEuclidean := hC m 1 h u (by norm_num) huScalar
  have hHilbert :
      eLpNorm (fun x ↦ HilbertVec.ofVec (u.toH1Function.grad x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) ≤
        C * eLpNorm (fun x ↦ HilbertVec.ofVec (f x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      euclideanNorm_eq_norm_ofVec, eLpNorm_norm, h, ENNReal.ofReal_one,
      inv_one, mul_one] using hEuclidean
  have hGradHilbert :
      MemLp (fun x ↦ HilbertVec.ofVec (u.toH1Function.grad x)) q.exponent
        (normalizedCubeMeasure (originCube d m)) := by
    refine ⟨?_, ?_⟩
    · have hrawTwo : MemLp u.toH1Function.grad 2
          (normalizedCubeMeasure (originCube d m)) := by
        unfold normalizedCubeMeasure cubeMeasure
        rw [volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
        exact u.toH1Function.grad_memVectorL2.smul_measure ENNReal.ofReal_ne_top
      exact (HilbertVec.ofVecL d).continuous.comp_aestronglyMeasurable
        hrawTwo.aestronglyMeasurable
    · apply lt_of_le_of_lt hHilbert
      exact ENNReal.mul_lt_top hCtop
        (memLp_hilbertify_of_memLp_vec_neumannEndpoint hf).eLpNorm_lt_top
  refine ⟨memLp_vec_of_memLp_hilbertify_neumannEndpoint hGradHilbert, ?_⟩
  calc
    eLpNorm u.toH1Function.grad q.exponent
        (normalizedCubeMeasure (originCube d m)) ≤
      eLpNorm (fun x ↦ HilbertVec.ofVec (u.toH1Function.grad x)) q.exponent
        (normalizedCubeMeasure (originCube d m)) :=
          eLpNorm_vec_le_hilbertify_neumannEndpoint _
    _ ≤ C * eLpNorm (fun x ↦ HilbertVec.ofVec (f x)) q.exponent
        (normalizedCubeMeasure (originCube d m)) := hHilbert
    _ ≤ (C * ENNReal.ofReal (d : ℝ)) *
        eLpNorm f q.exponent (normalizedCubeMeasure (originCube d m)) := by
      calc
        C * eLpNorm (fun x ↦ HilbertVec.ofVec (f x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) ≤
          C * (ENNReal.ofReal (d : ℝ) *
            eLpNorm f q.exponent
              (normalizedCubeMeasure (originCube d m))) := by
                gcongr
                exact eLpNorm_hilbertify_le_dimension_mul_vec_neumannEndpoint f
        _ = _ := by ac_rfl

/-- The raw-vector mean-zero Neumann Calderón--Zygmund estimate on arbitrary
triadic cubes.  The real constant depends only on dimension and exponent. -/
theorem exists_cubeH1MeanZeroNeumannDivergence_cz
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : TriadicCube d) (f : Vec d → Vec d),
      MemLp f q.exponent (normalizedCubeMeasure Q) →
      ∀ u : H1MeanZeroFunction (openCubeSet Q),
        IsMeanZeroNeumannRhsWeakSolution
          (fun _ : Vec d ↦ (1 : Mat d)) (openCubeSet Q) u (fun x ↦ -f x) →
        MemLp u.toH1Function.grad q.exponent (normalizedCubeMeasure Q) ∧
          cubeLpNorm Q q.exponent u.toH1Function.grad ≤
            C * cubeLpNorm Q q.exponent f := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeNeumannDivergence_eLpNorm_le d q
  let Cₙ : ℝ := max 1 ((C * ENNReal.ofReal (d : ℝ)).toReal)
  refine ⟨Cₙ, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro Q f hf u hu
  let f₀ : Vec d → Vec d := pullbackToOrigin Q f
  let u₀ : H1MeanZeroFunction (openCubeSet (originCube d Q.scale)) :=
    untranslateH1MeanZeroToOrigin Q u
  have hf₀ : MemLp f₀ q.exponent
      (normalizedCubeMeasure (originCube d Q.scale)) :=
    memLp_pullbackToOrigin Q hf
  have hu₀ : IsMeanZeroNeumannRhsWeakSolution
      (fun _ : Vec d ↦ (1 : Mat d)) (openCubeSet (originCube d Q.scale)) u₀
      (fun x ↦ -f₀ x) := by
    simpa only [u₀, f₀] using
      isMeanZeroNeumannRhsWeakSolution_untranslateH1MeanZeroToOrigin
        Q (1 : Mat d) hu
  obtain ⟨hgrad₀, hbound₀⟩ := hC Q.scale f₀ hf₀ u₀ hu₀
  have hgrad : MemLp u.toH1Function.grad q.exponent
      (normalizedCubeMeasure Q) := by
    rw [← pushforwardFromOrigin_untranslateH1MeanZeroToOrigin_grad Q u]
    exact memLp_pushforwardFromOrigin Q hgrad₀
  refine ⟨hgrad, ?_⟩
  have hgradNorm : cubeLpNorm Q q.exponent u.toH1Function.grad =
      (eLpNorm u₀.toH1Function.grad q.exponent
        (normalizedCubeMeasure (originCube d Q.scale))).toReal := by
    rw [← pushforwardFromOrigin_untranslateH1MeanZeroToOrigin_grad Q u,
      cubeLpNorm_pushforwardFromOrigin_eq Q q.exponent hgrad₀.aestronglyMeasurable]
    rfl
  have hfNorm : cubeLpNorm Q q.exponent f =
      (eLpNorm f₀ q.exponent
        (normalizedCubeMeasure (originCube d Q.scale))).toReal := by
    rw [← cubeLpNorm_pullbackToOrigin_eq Q q.exponent hf.aestronglyMeasurable]
    rfl
  rw [hgradNorm, hfNorm]
  calc
    (eLpNorm u₀.toH1Function.grad q.exponent
        (normalizedCubeMeasure (originCube d Q.scale))).toReal ≤
      ((C * ENNReal.ofReal (d : ℝ)) *
        eLpNorm f₀ q.exponent
          (normalizedCubeMeasure (originCube d Q.scale))).toReal :=
            ENNReal.toReal_mono
              (ENNReal.mul_ne_top
                (ENNReal.mul_ne_top hCtop.ne ENNReal.ofReal_ne_top)
                hf₀.eLpNorm_ne_top) hbound₀
    _ = (C * ENNReal.ofReal (d : ℝ)).toReal *
        (eLpNorm f₀ q.exponent
          (normalizedCubeMeasure (originCube d Q.scale))).toReal := by
      rw [ENNReal.toReal_mul]
    _ ≤ Cₙ * (eLpNorm f₀ q.exponent
          (normalizedCubeMeasure (originCube d Q.scale))).toReal := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg

end CubeCalderonZygmund

end

end Homogenization
