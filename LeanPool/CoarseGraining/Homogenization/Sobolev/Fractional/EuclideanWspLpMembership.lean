/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspCongruence

/-!
# Finite-seminorm membership for Euclidean fractional Sobolev fields

This file packages the product-measure measurability needed to turn a
normalized-cube `L^p` field with finite Euclidean fractional seminorm into a
literal `MemCubeEuclideanWsp` witness.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem gagliardoCubeMeasure_diagonal_eq_zero {d : ℕ} [NeZero d]
    (Q : TriadicCube d) :
    Gagliardo.gagliardoCubeMeasure Q (Set.diagonal (Vec d)) = 0 := by
  let : IsFiniteMeasure (cubeMeasure Q) :=
    ⟨lt_top_iff_ne_top.mpr (cubeMeasure_apply_univ_ne_top Q)⟩
  rw [Gagliardo.gagliardoCubeMeasure]
  apply Measure.measure_prod_null isClosed_diagonal.measurableSet |>.mpr
  filter_upwards with x
  have hpre : Prod.mk x ⁻¹' Set.diagonal (Vec d) = {x} := by
    ext y
    simp [Set.mem_diagonal_iff, eq_comm]
  rw [hpre]
  simp [cubeMeasure]

private theorem aestronglyMeasurable_cubeEuclideanWspKernel_of_memLp
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} {F : Vec d → Vec d}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (normalizedCubeMeasure Q)) :
    AEStronglyMeasurable (cubeEuclideanWspKernel s p F)
      (Gagliardo.gagliardoCubeMeasure Q) := by
  let μ := Gagliardo.gagliardoCubeMeasure Q
  let D : Set (Vec d × Vec d) := (Set.diagonal (Vec d))ᶜ
  have hFcube : AEStronglyMeasurable (fun x => HilbertVec.ofVec (F x))
      (cubeMeasure Q) := by
    refine ⟨hF.aestronglyMeasurable.mk _,
      hF.aestronglyMeasurable.stronglyMeasurable_mk, ?_⟩
    exact Gagliardo.ae_normalizedCubeMeasure_iff.mp
      hF.aestronglyMeasurable.ae_eq_mk
  have hfst : AEStronglyMeasurable (fun z : Vec d × Vec d =>
      HilbertVec.ofVec (F z.1)) μ := by
    dsimp only [μ, Gagliardo.gagliardoCubeMeasure]
    exact hF.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst
  have hsnd : AEStronglyMeasurable (fun z : Vec d × Vec d =>
      HilbertVec.ofVec (F z.2)) μ := by
    dsimp only [μ, Gagliardo.gagliardoCubeMeasure]
    exact hFcube.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hpair : AEStronglyMeasurable (fun z : Vec d × Vec d =>
      HilbertVec.ofVec (F z.1 - F z.2)) μ := by
    simpa only [map_sub] using! hfst.sub hsnd
  have hdist : Continuous (fun z : Vec d × Vec d => euclideanDist z.1 z.2) := by
    have hh : Continuous (fun z : Vec d × Vec d => HilbertVec.ofVec (z.1 - z.2)) :=
      (HilbertVec.ofVecL d).continuous.comp (continuous_fst.sub continuous_snd)
    simpa only [euclideanDist, euclideanNorm_eq_norm_ofVec] using hh.norm
  have hDmeas : MeasurableSet D := isClosed_diagonal.measurableSet.compl
  have hscalar : AEStronglyMeasurable (fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal)))
      (μ.restrict D) := by
    exact (hdist.continuousOn.rpow_const fun z hz => Or.inl (by
      intro hzero
      apply hz
      exact Set.mem_diagonal_iff.mpr (euclideanDist_eq_zero_iff.mp hzero))).aestronglyMeasurable hDmeas
  have hrestrictPair : AEStronglyMeasurable (fun z : Vec d × Vec d =>
      HilbertVec.ofVec (F z.1 - F z.2)) (μ.restrict D) := hpair.restrict
  have hkernel : AEStronglyMeasurable (cubeEuclideanWspKernel s p F)
      (μ.restrict D) := by
    simpa only [cubeEuclideanWspKernel_apply] using! hscalar.smul hrestrictPair
  have hdiag : μ (Set.diagonal (Vec d)) = 0 := by
    dsimp only [μ]
    exact gagliardoCubeMeasure_diagonal_eq_zero Q
  have hDae : ∀ᵐ z ∂μ, z ∈ D := by
    rw [ae_iff]
    simpa [D] using! hdiag
  have hrestrict : μ.restrict D = μ := Measure.restrict_eq_self_of_ae_mem hDae
  simpa only [hrestrict] using hkernel

/-- A normalized-cube Euclidean `L^p` field with finite fractional seminorm
belongs to the literal Euclidean fractional Sobolev membership predicate. -/
theorem memCubeEuclideanWsp_of_memLp_of_eSeminorm_lt_top
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} {F : Vec d → Vec d}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (normalizedCubeMeasure Q))
    (hsemi : cubeEuclideanWspESeminorm Q s p F < ∞) :
    MemCubeEuclideanWsp Q s p F := by
  classical
  by_cases hd : d = 0
  · subst d
    have hkernel : cubeEuclideanWspKernel s p F = 0 := by
      funext z
      have hsub : F z.1 - F z.2 = 0 := Subsingleton.elim _ _
      simp [cubeEuclideanWspKernel_apply, hsub]
    unfold MemCubeEuclideanWsp
    rw [hkernel]
    exact MemLp.zero
  · let : NeZero d := ⟨hd⟩
    exact ⟨aestronglyMeasurable_cubeEuclideanWspKernel_of_memLp hF, hsemi⟩

end

end Homogenization
