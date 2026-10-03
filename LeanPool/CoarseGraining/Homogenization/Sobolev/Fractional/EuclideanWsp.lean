/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.Definitions

/-!
# Euclidean fractional Sobolev core

The exact Chapter 3 Euclidean `W^(s,p)` kernel and full power norm on a
triadic cube.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

noncomputable def cubeEuclideanWspKernel {d : ℕ} (s : FractionalOrder)
    (p : FiniteLpExponent) (F : Vec d → Vec d) :
    Vec d × Vec d → HilbertVec d :=
  fun z =>
    (euclideanDist z.1 z.2 ^
      (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
        HilbertVec.ofVec (F z.1 - F z.2)

@[simp] theorem cubeEuclideanWspKernel_apply {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (z : Vec d × Vec d) :
    cubeEuclideanWspKernel s p F z =
      (euclideanDist z.1 z.2 ^
        (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
          HilbertVec.ofVec (F z.1 - F z.2) := rfl

theorem norm_cubeEuclideanWspKernel {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (z : Vec d × Vec d) :
    ‖cubeEuclideanWspKernel s p F z‖ =
      (euclideanDist z.1 z.2 ^
        (-(s.1 + (d : ℝ) / p.exponent.toReal))) *
          euclideanNorm (F z.1 - F z.2) := by
  rw [cubeEuclideanWspKernel_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (euclideanDist_nonneg _ _) _),
    ← euclideanNorm_eq_norm_ofVec]

def MemCubeEuclideanWsp {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) : Prop :=
  MemLp (cubeEuclideanWspKernel s p F) p.exponent
    (Gagliardo.gagliardoCubeMeasure Q)

noncomputable def cubeEuclideanWspESeminorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  eLpNorm' (cubeEuclideanWspKernel s p F) p.exponent.toReal
    (Gagliardo.gagliardoCubeMeasure Q)

/-- For measurable kernels, the integral seminorm is Mathlib's `eLpNorm`. -/
theorem cubeEuclideanWspESeminorm_eq_eLpNorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d)
    (hF : AEStronglyMeasurable (cubeEuclideanWspKernel s p F)
      (Gagliardo.gagliardoCubeMeasure Q)) :
    cubeEuclideanWspESeminorm Q s p F = eLpNorm (cubeEuclideanWspKernel s p F)
      p.exponent (Gagliardo.gagliardoCubeMeasure Q) :=
  (eLpNorm_eq_eLpNorm' (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne hF).symm

theorem cubeEuclideanWspESeminorm_eq_lintegral {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    cubeEuclideanWspESeminorm Q s p F =
      (∫⁻ z, ‖cubeEuclideanWspKernel s p F z‖ₑ ^ p.exponent.toReal
        ∂Gagliardo.gagliardoCubeMeasure Q) ^
          (1 / p.exponent.toReal) := by
  unfold cubeEuclideanWspESeminorm
  exact eLpNorm'_eq_lintegral_enorm _ _ _

theorem memCubeEuclideanWsp_iff {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} {F : Vec d → Vec d} :
    MemCubeEuclideanWsp Q s p F ↔
      AEStronglyMeasurable (cubeEuclideanWspKernel s p F)
          (Gagliardo.gagliardoCubeMeasure Q) ∧
        cubeEuclideanWspESeminorm Q s p F < ∞ := by
  constructor
  · intro hF
    refine ⟨MemLp.aestronglyMeasurable hF, ?_⟩
    rw [cubeEuclideanWspESeminorm_eq_eLpNorm _ _ _ _ (MemLp.aestronglyMeasurable hF)]
    exact MemLp.eLpNorm_lt_top hF
  · rintro ⟨hmeas, hfinite⟩
    rw [cubeEuclideanWspESeminorm_eq_eLpNorm _ _ _ _ hmeas] at hfinite
    exact hfinite

theorem MemCubeEuclideanWsp.aestronglyMeasurable {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    {F : Vec d → Vec d} (hF : MemCubeEuclideanWsp Q s p F) :
    AEStronglyMeasurable (cubeEuclideanWspKernel s p F)
      (Gagliardo.gagliardoCubeMeasure Q) :=
  MemLp.aestronglyMeasurable hF

theorem MemCubeEuclideanWsp.eSeminorm_lt_top {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    {F : Vec d → Vec d} (hF : MemCubeEuclideanWsp Q s p F) :
    cubeEuclideanWspESeminorm Q s p F < ∞ :=
  (memCubeEuclideanWsp_iff.1 hF).2

structure CubeEuclideanWspField {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent)
    extends CubeEuclideanLpField Q p where
  euclideanMemWsp : MemCubeEuclideanWsp Q s p toField

namespace CubeEuclideanWspField

instance {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} :
    CoeFun (CubeEuclideanWspField Q s p) (fun _ => Vec d → Vec d) where
  coe F := F.toField

theorem kernel_aestronglyMeasurable {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) :
    AEStronglyMeasurable
      (cubeEuclideanWspKernel s p F.toField)
      (Gagliardo.gagliardoCubeMeasure Q) :=
  F.euclideanMemWsp.aestronglyMeasurable

theorem eSeminorm_lt_top {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) :
    cubeEuclideanWspESeminorm Q s p F.toField < ∞ :=
  F.euclideanMemWsp.eSeminorm_lt_top

end CubeEuclideanWspField

noncomputable def cubeEuclideanWspScalePowerWeight {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) : ℝ≥0∞ :=
  (ENNReal.ofReal (cubeScaleFactor Q)) ^
    (-s.1 * p.exponent.toReal)

theorem cubeEuclideanWspScalePowerWeight_lt_top {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) :
    cubeEuclideanWspScalePowerWeight Q s p < ∞ := by
  unfold cubeEuclideanWspScalePowerWeight
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  exact lt_top_iff_ne_top.mpr
    (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_ne_zero_iff.mpr hscale)
      ENNReal.ofReal_ne_top)

noncomputable def cubeEuclideanWspFullENorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  (cubeEuclideanWspScalePowerWeight Q s p *
        ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
          p.exponent F) ^ p.exponent.toReal +
      (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal) ^
    (p.exponent.toReal)⁻¹

theorem CubeEuclideanWspField.normalizedEuclideanLpENorm_lt_top
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} (F : CubeEuclideanWspField Q s p) :
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
        p.exponent F.toField < ∞ := by
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
  have hmeas : AEStronglyMeasurable (fun x => euclideanNorm (F.toField x))
      (cubeBoundedMeasurableDomain Q).normalizedVolume := by
    rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    simpa only [euclideanNorm_eq_norm_ofVec] using F.euclideanMemLp.norm.aestronglyMeasurable
  rw [BoundedMeasurableDomain.normalizedLpENorm_eq_eLpNorm _ _ _ hmeas,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  simpa only [euclideanNorm_eq_norm_ofVec] using
      F.euclideanMemLp.norm.eLpNorm_lt_top

theorem CubeEuclideanWspField.fullENorm_lt_top {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) :
    cubeEuclideanWspFullENorm Q s p F.toField < ∞ := by
  unfold cubeEuclideanWspFullENorm
  apply ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
  exact (ENNReal.add_lt_top.mpr ⟨
    ENNReal.mul_lt_top
      (cubeEuclideanWspScalePowerWeight_lt_top Q s p)
      (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
        F.normalizedEuclideanLpENorm_lt_top.ne),
    ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg
      F.eSeminorm_lt_top.ne⟩).ne

end

end Homogenization
