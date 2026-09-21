/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLp
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Bounded `L² ∩ Lᵖ` approximation of cube data

Every finite-exponent cube datum admits bounded continuous approximants on the
same normalized cube measure.  Boundedness supplies the additional `L²`
membership required by the supplied-solution Calderón--Zygmund theorem.
-/

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

private noncomputable def boundedApproximation
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (h : CubeEuclideanLpField Q q) (n : ℕ) :
    BoundedContinuousFunction (Vec d) (HilbertVec d) :=
  Classical.choose (h.euclideanMemLp.exists_boundedContinuous_eLpNorm_sub_le
    q.lt_top.ne (ε := ((n : ℝ≥0∞) + 1)⁻¹) (by simp))

private theorem boundedApproximation_memLp
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (h : CubeEuclideanLpField Q q) (n : ℕ) :
    MemLp (boundedApproximation h n) q.exponent (normalizedCubeMeasure Q) :=
  (Classical.choose_spec (h.euclideanMemLp.exists_boundedContinuous_eLpNorm_sub_le
    q.lt_top.ne (ε := ((n : ℝ≥0∞) + 1)⁻¹) (by simp))).2

private theorem eLpNorm_sub_boundedApproximation_le
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (h : CubeEuclideanLpField Q q) (n : ℕ) :
    eLpNorm (fun x => HilbertVec.ofVec (h.toField x) - boundedApproximation h n x)
      q.exponent (normalizedCubeMeasure Q) ≤ ((n : ℝ≥0∞) + 1)⁻¹ :=
  (Classical.choose_spec (h.euclideanMemLp.exists_boundedContinuous_eLpNorm_sub_le
    q.lt_top.ne (ε := ((n : ℝ≥0∞) + 1)⁻¹) (by simp))).1

private theorem boundedApproximation_memLp_two
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (h : CubeEuclideanLpField Q q) (n : ℕ) :
    MemLp (boundedApproximation h n) 2 (normalizedCubeMeasure Q) := by
  let : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  rcases (boundedApproximation h n).bounded with ⟨C, hC⟩
  have hbound : ∀ x : Vec d,
      ‖boundedApproximation h n x‖ ≤ C + ‖boundedApproximation h n 0‖ := by
    intro x
    calc
      ‖boundedApproximation h n x‖ = dist (boundedApproximation h n x) 0 := by
        rw [dist_zero_right]
      _ ≤ dist (boundedApproximation h n x) (boundedApproximation h n 0) +
          dist (boundedApproximation h n 0) 0 :=
        dist_triangle _ _ _
      _ ≤ C + ‖boundedApproximation h n 0‖ := by
        rw [dist_zero_right]
        gcongr
        exact hC x 0
  exact MemLp.of_bound (boundedApproximation h n).continuous.aestronglyMeasurable
    (C + ‖boundedApproximation h n 0‖) (Eventually.of_forall hbound)

/-- A bounded continuous approximation of an arbitrary finite-exponent cube
datum, bundled with the internally derived `L²` membership. -/
noncomputable def finiteLpDataApproximation
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (h : CubeEuclideanLpField Q q) (n : ℕ) : CubeEuclideanL2LpField Q q where
  toField := fun x => (boundedApproximation h n x).toVec
  euclideanMemLp := by
    simpa only [HilbertVec.ofVec_toVec] using boundedApproximation_memLp h n
  euclideanMemL2 := by
    simpa only [HilbertVec.ofVec_toVec] using boundedApproximation_memLp_two h n

@[simp] private theorem finiteLpDataApproximation_toField
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (h : CubeEuclideanLpField Q q) (n : ℕ) :
    (finiteLpDataApproximation h n).toField = fun x => (boundedApproximation h n x).toVec :=
  rfl

/-- The bounded `L² ∩ Lᵖ` cube-data approximants converge in the exact
normalized Euclidean `L^p` extended norm. -/
theorem tendsto_eLpNorm_sub_finiteLpDataApproximation
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    (h : CubeEuclideanLpField Q q) :
    Tendsto (fun n => eLpNorm
      (fun x => HilbertVec.ofVec (h.toField x - (finiteLpDataApproximation h n).toField x))
      q.exponent (normalizedCubeMeasure Q)) atTop (nhds 0) := by
  have hbound : ∀ n,
      eLpNorm (fun x => HilbertVec.ofVec
        (h.toField x - (finiteLpDataApproximation h n).toField x))
        q.exponent (normalizedCubeMeasure Q) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    calc
      eLpNorm (fun x => HilbertVec.ofVec
          (h.toField x - (finiteLpDataApproximation h n).toField x))
          q.exponent (normalizedCubeMeasure Q) =
        eLpNorm (fun x => HilbertVec.ofVec (h.toField x) - boundedApproximation h n x)
          q.exponent (normalizedCubeMeasure Q) := by
          apply eLpNorm_congr_ae
          filter_upwards with x
          rw [finiteLpDataApproximation_toField]
          change (HilbertVec.ofVecL d) (h.toField x - (boundedApproximation h n x).toVec) = _
          simpa only [HilbertVec.ofVecL_apply] using
            (HilbertVec.ofVecL d).map_sub (h.toField x) (boundedApproximation h n x).toVec
      _ ≤ _ := eLpNorm_sub_boundedApproximation_le h n
  have hzero : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (nhds 0) := by
    have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [eventually_ge_atTop b] with n hn
      omega
    have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0∞)⁻¹)) atTop (nhds 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp hshift
    simpa only [Nat.cast_add, Nat.cast_one] using hinv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hzero
    (fun _ => bot_le) hbound

end CubeCalderonZygmund

end
end Homogenization
