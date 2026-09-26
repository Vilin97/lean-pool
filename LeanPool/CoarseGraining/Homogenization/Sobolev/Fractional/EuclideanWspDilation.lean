/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Dilation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWsp

/-!
# Triadic dilation covariance for finite-p Euclidean fractional norms

The pullback from `dilateCube k Q` to `Q` is composition with the literal
map `x ↦ 3^k • x`.  Normalized volume is invariant, while the fractional
seminorm and the full power norm acquire the physical factor `3^(-k s)`.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

private noncomputable def euclideanWspDilationEquiv {d : ℕ}
    (k : ℤ) : Vec d ≃ᵐ Vec d :=
  MeasurableEquiv.smul₀ (Book.Ch02.triadicDilationFactor k)
    (Book.Ch02.triadicDilationFactor_ne_zero k)

private theorem cubeVolume_dilateCube {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    cubeVolume (Book.Ch02.dilateCube k Q) =
      (Book.Ch02.triadicDilationFactor k) ^ d * cubeVolume Q := by
  rw [cubeVolume_eq_scaleFactor_pow, Book.Ch02.cubeScaleFactor_dilateCube,
    mul_pow, cubeVolume_eq_scaleFactor_pow]

private theorem euclideanWspDilation_measurePreserving {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) :
    MeasurePreserving (euclideanWspDilationEquiv (d := d) k)
      (normalizedCubeMeasure Q)
      (normalizedCubeMeasure (Book.Ch02.dilateCube k Q)) := by
  let r : ℝ := Book.Ch02.triadicDilationFactor k
  let T := euclideanWspDilationEquiv (d := d) k
  have hr : 0 < r := Book.Ch02.triadicDilationFactor_pos k
  have hT : (T : Vec d → Vec d) = fun x => r • x := rfl
  have hres : Measure.map T (cubeMeasure Q) =
      ENNReal.ofReal ((r ^ d)⁻¹) • cubeMeasure (Book.Ch02.dilateCube k Q) := by
    rw [cubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
      hT, map_smul_volume_restrict hr,
      Book.Ch02.openCubeSet_dilateCube]
  have hvol : cubeVolume (Book.Ch02.dilateCube k Q) = r ^ d * cubeVolume Q := by
    simpa only [r] using cubeVolume_dilateCube k Q
  refine ⟨T.measurable, ?_⟩
  rw [normalizedCubeMeasure, normalizedCubeMeasure,
    Measure.map_smul _ T.measurable.aemeasurable, hres]
  rw [smul_smul]
  congr 1
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (cubeVolume_nonneg Q))]
  have hrpow : 0 < r ^ d := pow_pos hr d
  rw [show (cubeVolume Q)⁻¹ * (r ^ d)⁻¹ =
      (r ^ d * cubeVolume Q)⁻¹ by field_simp [hrpow.ne'], hvol]

private theorem euclideanWspDilation_cubeMeasure_map {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) :
    Measure.map (euclideanWspDilationEquiv (d := d) k) (cubeMeasure Q) =
      ENNReal.ofReal ((Book.Ch02.triadicDilationFactor k ^ d)⁻¹) •
        cubeMeasure (Book.Ch02.dilateCube k Q) := by
  let r : ℝ := Book.Ch02.triadicDilationFactor k
  let T := euclideanWspDilationEquiv (d := d) k
  have hr : 0 < r := Book.Ch02.triadicDilationFactor_pos k
  have hT : (T : Vec d → Vec d) = fun x => r • x := rfl
  rw [cubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
    hT, map_smul_volume_restrict hr,
    Book.Ch02.openCubeSet_dilateCube]

private theorem euclideanWspDilation_pair_measure_map {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) :
    Measure.map
        ((euclideanWspDilationEquiv (d := d) k).prodCongr
          (euclideanWspDilationEquiv (d := d) k))
        (Gagliardo.gagliardoCubeMeasure Q) =
      ENNReal.ofReal ((Book.Ch02.triadicDilationFactor k ^ d)⁻¹) •
        Gagliardo.gagliardoCubeMeasure (Book.Ch02.dilateCube k Q) := by
  let T := euclideanWspDilationEquiv (d := d) k
  have hnorm := euclideanWspDilation_measurePreserving k Q
  have hcube := euclideanWspDilation_cubeMeasure_map k Q
  have : SFinite (cubeMeasure Q) := by
    unfold cubeMeasure
    infer_instance
  have : SFinite (cubeMeasure (Book.Ch02.dilateCube k Q)) := by
    unfold cubeMeasure
    infer_instance
  change Measure.map (Prod.map T T)
      ((normalizedCubeMeasure Q).prod (cubeMeasure Q)) = _
  rw [← Measure.map_prod_map _ _ T.measurable T.measurable,
    hnorm.map_eq, hcube, Measure.prod_smul_right]
  rfl

private theorem euclideanWspDilation_pair_measure_target_eq_smul_map {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) :
    Gagliardo.gagliardoCubeMeasure (Book.Ch02.dilateCube k Q) =
      (ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) ^ d •
        Measure.map
          ((euclideanWspDilationEquiv (d := d) k).prodCongr
            (euclideanWspDilationEquiv (d := d) k))
          (Gagliardo.gagliardoCubeMeasure Q) := by
  let r : ℝ := Book.Ch02.triadicDilationFactor k
  have hr : 0 < r := Book.Ch02.triadicDilationFactor_pos k
  rw [euclideanWspDilation_pair_measure_map, smul_smul]
  have hrpow : 0 ≤ r ^ d := (pow_pos hr d).le
  rw [← ENNReal.ofReal_pow hr.le,
    ← ENNReal.ofReal_mul hrpow,
    mul_inv_cancel₀ (pow_pos hr d).ne', ENNReal.ofReal_one, one_smul]

/-- Pointwise covariance of the Euclidean fractional kernel under the
source-to-target triadic dilation. -/
theorem cubeEuclideanWspKernel_dilate {d : ℕ}
    (k : ℤ) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : Vec d → Vec d) (z : Vec d × Vec d) :
    cubeEuclideanWspKernel s p F
        (Book.Ch02.dilateVec k z.1, Book.Ch02.dilateVec k z.2) =
      (Book.Ch02.triadicDilationFactor k) ^
        (-(s.1 + (d : ℝ) / p.exponent.toReal)) •
        cubeEuclideanWspKernel s p
          (fun x => F (Book.Ch02.dilateVec k x)) z := by
  let r : ℝ := Book.Ch02.triadicDilationFactor k
  have hr : 0 < r := Book.Ch02.triadicDilationFactor_pos k
  change cubeEuclideanWspKernel s p F (r • z.1, r • z.2) = _
  rw [cubeEuclideanWspKernel_apply, cubeEuclideanWspKernel_apply,
    euclideanDist_smul, abs_of_pos hr]
  rw [Real.mul_rpow hr.le (euclideanDist_nonneg _ _), smul_smul]
  simp only [Book.Ch02.dilateVec, r]

/-- Normalized Euclidean `L^p` is invariant under the source pullback of a
triadic dilation. -/
theorem cubeEuclideanNormalizedLpENorm_dilate {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    (cubeBoundedMeasurableDomain (Book.Ch02.dilateCube k Q)).normalizedEuclideanLpENorm
        p.exponent F =
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent
        (fun x => F (Book.Ch02.dilateVec k x)) := by
  let T := euclideanWspDilationEquiv (d := d) k
  have hMP := euclideanWspDilation_measurePreserving k Q
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
  unfold BoundedMeasurableDomain.normalizedLpENorm
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
  simp only [if_neg (ne_of_gt (lt_trans zero_lt_one p.one_lt)),
    if_neg p.lt_top.ne, eLpNorm'_eq_lintegral_enorm]
  congr 1
  rw [MeasurePreserving.lintegral_map_equiv _ T hMP]
  rfl

/-- The Euclidean fractional seminorm acquires exactly the physical factor
`3^(-k s)` under source pullback by a triadic dilation. -/
theorem cubeEuclideanWspESeminorm_dilate {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : Vec d → Vec d) :
    cubeEuclideanWspESeminorm (Book.Ch02.dilateCube k Q) s p F =
      (ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) ^ (-s.1) *
        cubeEuclideanWspESeminorm Q s p
          (fun x => F (Book.Ch02.dilateVec k x)) := by
  let r : ℝ := Book.Ch02.triadicDilationFactor k
  let T := euclideanWspDilationEquiv (d := d) k
  let TP := T.prodCongr T
  let a : ℝ := -(s.1 + (d : ℝ) / p.exponent.toReal)
  have hr : 0 < r := Book.Ch02.triadicDilationFactor_pos k
  have hR0 : ENNReal.ofReal r ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hr
  have hRtop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hT : (TP : Vec d × Vec d → Vec d × Vec d) =
      (euclideanWspDilationEquiv (d := d) k).prodCongr
        (euclideanWspDilationEquiv (d := d) k) := rfl
  have hker : cubeEuclideanWspKernel s p F ∘ TP =
      fun z => r ^ a • cubeEuclideanWspKernel s p
        (fun x => F (Book.Ch02.dilateVec k x)) z := by
    funext z
    simpa only [Function.comp_apply, r, a] using! cubeEuclideanWspKernel_dilate k s p F z
  rw [cubeEuclideanWspESeminorm,
    euclideanWspDilation_pair_measure_target_eq_smul_map]
  rw [eLpNorm'_smul_measure ENNReal.toReal_nonneg]
  have hmap : eLpNorm' (cubeEuclideanWspKernel s p F) p.exponent.toReal
      (Measure.map TP (Gagliardo.gagliardoCubeMeasure Q)) =
      eLpNorm' (cubeEuclideanWspKernel s p F ∘ TP) p.exponent.toReal
        (Gagliardo.gagliardoCubeMeasure Q) := by
    simp only [eLpNorm'_eq_lintegral_enorm]
    rw [TP.measurableEmbedding.lintegral_map]
    rfl
  rw [hmap]
  rw [hker]
  change (ENNReal.ofReal r ^ d) ^ (1 / p.exponent.toReal) *
      eLpNorm' (r ^ a • cubeEuclideanWspKernel s p
        (fun x => F (Book.Ch02.dilateVec k x))) p.exponent.toReal
        (Gagliardo.gagliardoCubeMeasure Q) = _
  rw [eLpNorm'_const_smul _
    (ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne)]
  rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hr.le a)]
  rw [← ENNReal.ofReal_rpow_of_pos hr]
  rw [← ENNReal.rpow_natCast (ENNReal.ofReal r) d]
  rw [← ENNReal.rpow_mul]
  rw [← mul_assoc, ← ENNReal.rpow_add _ _ hR0 hRtop]
  change (ENNReal.ofReal r) ^ ((d : ℝ) * (1 / p.exponent.toReal) + a) *
      eLpNorm' (cubeEuclideanWspKernel s p
        (fun x => F (Book.Ch02.dilateVec k x))) p.exponent.toReal
        (Gagliardo.gagliardoCubeMeasure Q) =
      (ENNReal.ofReal r) ^ (-s.1) *
        eLpNorm' (cubeEuclideanWspKernel s p
          (fun x => F (Book.Ch02.dilateVec k x))) p.exponent.toReal
          (Gagliardo.gagliardoCubeMeasure Q)
  congr 1
  congr 1
  simp only [one_div, ENNReal.toReal_inv]
  dsimp only [a]
  ring

/-- Fractional Sobolev membership is transported exactly by a triadic
dilation and source pullback. -/
theorem memCubeEuclideanWsp_dilate_iff {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : Vec d → Vec d) :
    MemCubeEuclideanWsp (Book.Ch02.dilateCube k Q) s p F ↔
      MemCubeEuclideanWsp Q s p
        (fun x => F (Book.Ch02.dilateVec k x)) := by
  let r : ℝ := Book.Ch02.triadicDilationFactor k
  let T := euclideanWspDilationEquiv (d := d) k
  let TP := T.prodCongr T
  let c : ℝ≥0∞ := (ENNReal.ofReal r) ^ d
  have hr : 0 < r := Book.Ch02.triadicDilationFactor_pos k
  have hc0 : c ≠ 0 := by
    dsimp only [c]
    exact pow_ne_zero d (ENNReal.ofReal_ne_zero_iff.mpr hr)
  have hctop : c ≠ ∞ := by
    dsimp only [c]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have ha : r ^ (-(s.1 + (d : ℝ) / p.exponent.toReal)) ≠ 0 :=
    (Real.rpow_pos_of_pos hr _).ne'
  have hmeasure := euclideanWspDilation_pair_measure_target_eq_smul_map k Q
  have hker : cubeEuclideanWspKernel s p F ∘ TP =
      r ^ (-(s.1 + (d : ℝ) / p.exponent.toReal)) •
        cubeEuclideanWspKernel s p
          (fun x => F (Book.Ch02.dilateVec k x)) := by
    funext z
    simpa only [Function.comp_apply] using! cubeEuclideanWspKernel_dilate k s p F z
  change MemLp (cubeEuclideanWspKernel s p F) p.exponent
      (Gagliardo.gagliardoCubeMeasure (Book.Ch02.dilateCube k Q)) ↔
    MemLp (cubeEuclideanWspKernel s p
      (fun x => F (Book.Ch02.dilateVec k x))) p.exponent
      (Gagliardo.gagliardoCubeMeasure Q)
  rw [hmeasure]
  change MemLp (cubeEuclideanWspKernel s p F) p.exponent
      (c • Measure.map TP (Gagliardo.gagliardoCubeMeasure Q)) ↔ _
  constructor
  · intro htarget
    have hmap : MemLp (cubeEuclideanWspKernel s p F) p.exponent
        (Measure.map TP (Gagliardo.gagliardoCubeMeasure Q)) := by
      have hinv := htarget.smul_measure (ENNReal.inv_ne_top.2 hc0)
      simpa only [smul_smul, ENNReal.inv_mul_cancel hc0 hctop, one_smul] using hinv
    have hpull : MemLp (cubeEuclideanWspKernel s p F ∘ TP) p.exponent
        (Gagliardo.gagliardoCubeMeasure Q) :=
      (TP.memLp_map_measure_iff).mp hmap
    rw [hker] at hpull
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using
      hpull.const_smul (r ^ (-(s.1 + (d : ℝ) / p.exponent.toReal)))⁻¹
  · intro hpull
    have hcomp : MemLp (cubeEuclideanWspKernel s p F ∘ TP) p.exponent
        (Gagliardo.gagliardoCubeMeasure Q) := by
      rw [hker]
      exact hpull.const_smul _
    have hmap : MemLp (cubeEuclideanWspKernel s p F) p.exponent
        (Measure.map TP (Gagliardo.gagliardoCubeMeasure Q)) :=
      (TP.memLp_map_measure_iff).mpr hcomp
    exact hmap.smul_measure hctop

private theorem cubeEuclideanWspScalePowerWeight_dilate {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) :
    cubeEuclideanWspScalePowerWeight (Book.Ch02.dilateCube k Q) s p =
      ((ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) ^
        (-s.1)) ^ p.exponent.toReal *
        cubeEuclideanWspScalePowerWeight Q s p := by
  let r : ℝ := Book.Ch02.triadicDilationFactor k
  let a : ℝ := cubeScaleFactor Q
  let t : ℝ := p.exponent.toReal
  have hr : 0 < r := Book.Ch02.triadicDilationFactor_pos k
  have ha : 0 < a := by
    simpa [a, cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  unfold cubeEuclideanWspScalePowerWeight
  rw [Book.Ch02.cubeScaleFactor_dilateCube]
  change (ENNReal.ofReal (r * a)) ^ (-s.1 * t) =
    ((ENNReal.ofReal r) ^ (-s.1)) ^ t *
      (ENNReal.ofReal a) ^ (-s.1 * t)
  rw [ENNReal.ofReal_rpow_of_pos (mul_pos hr ha),
    Real.mul_rpow hr.le ha.le,
    ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
  rw [Real.rpow_mul hr.le]
  rw [← ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _),
    ENNReal.ofReal_rpow_of_pos hr,
    ← ENNReal.ofReal_rpow_of_pos ha]

/-- The full normalized Euclidean fractional power norm acquires exactly the
physical factor `3^(-k s)` under source pullback by a triadic dilation. -/
theorem cubeEuclideanWspFullENorm_dilate {d : ℕ}
    (k : ℤ) (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : Vec d → Vec d) :
    cubeEuclideanWspFullENorm (Book.Ch02.dilateCube k Q) s p F =
      (ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)) ^ (-s.1) *
        cubeEuclideanWspFullENorm Q s p
          (fun x => F (Book.Ch02.dilateVec k x)) := by
  let R : ℝ≥0∞ := ENNReal.ofReal (Book.Ch02.triadicDilationFactor k)
  let A : ℝ≥0∞ := R ^ (-s.1)
  let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
    p.exponent (fun x => F (Book.Ch02.dilateVec k x))
  let S := cubeEuclideanWspESeminorm Q s p
    (fun x => F (Book.Ch02.dilateVec k x))
  let W := cubeEuclideanWspScalePowerWeight Q s p
  let t := p.exponent.toReal
  have ht : 0 < t :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have htinv : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  rw [cubeEuclideanWspFullENorm,
    cubeEuclideanWspScalePowerWeight_dilate,
    cubeEuclideanNormalizedLpENorm_dilate,
    cubeEuclideanWspESeminorm_dilate]
  change ((A ^ t * W) * L ^ t + (A * S) ^ t) ^ t⁻¹ =
    A * (W * L ^ t + S ^ t) ^ t⁻¹
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le]
  calc
    ((A ^ t * W) * L ^ t + A ^ t * S ^ t) ^ t⁻¹ =
        (A ^ t * (W * L ^ t + S ^ t)) ^ t⁻¹ := by
      congr 1
      rw [mul_add]
      ac_rfl
    _ = (A ^ t) ^ t⁻¹ * (W * L ^ t + S ^ t) ^ t⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ htinv]
    _ = A * (W * L ^ t + S ^ t) ^ t⁻¹ := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]

end

end Homogenization
