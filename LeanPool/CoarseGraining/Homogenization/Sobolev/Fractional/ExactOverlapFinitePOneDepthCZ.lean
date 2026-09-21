/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePAveraging
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePDepthTriangle
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePGlobalBound
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePPDESplitting
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePPoincareDepth
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.OverlapCubeVectorNormalized

/-!
# One-depth finite-`p` Calderon--Zygmund overlap estimate

This is the one-depth analytic closure: the exact overlap energy of the
gradient of a cube Dirichlet divergence solution is controlled by that of its
datum, uniformly in the root scale and overlap depth.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/- The supplied-solution CZ theorem is stated on the normalized centered
cube.  The overlap API is stated on the equivalent normalized cube measure,
so keep this transport private to the one-depth assembly. -/
private theorem cubeDirichletDivergenceProblem_to_centered_normalized
    {d : ℕ} [NeZero d] (m : ℤ) {u : H10Function (openCubeSet (originCube d m))}
    {h : Vec d → Vec d}
    (hh : MemLp (fun x => HilbertVec.ofVec (h x)) 2
      (normalizedCubeMeasure (originCube d m)))
    (hu : CubeDirichletDivergenceProblem (originCube d m) u h) :
    IsCenteredCubeH10ScalarDivergenceSolution m 1 u ⟨h, hh⟩ := by
  intro phi
  have hmeasure : (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) := by
    simp only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure, cubeMeasure,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  rw [hmeasure, MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_smul_measure, smul_eq_mul, smul_eq_mul, one_mul,
    hu phi]
  ring

/- Although an `H10Function` begins only in `L²`, the supplied-solution
finite-`q` estimate makes the particular gradient used below a genuine
`L^q` field.  This is solely a private membership bridge required by the
depth-triangle API, not an extra theorem hypothesis. -/
private theorem cubeDirichletDivergenceProblem_grad_memLp
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) (h : Vec d → Vec d)
    (hh2 : MemLp (fun x => HilbertVec.ofVec (h x)) 2
      (normalizedCubeMeasure (originCube d m)))
    (hhq : MemLp (fun x => HilbertVec.ofVec (h x)) q.exponent
      (normalizedCubeMeasure (originCube d m)))
    (w : H10Function (openCubeSet (originCube d m)))
    (hw : CubeDirichletDivergenceProblem (originCube d m) w h) :
    MemLp (fun x => HilbertVec.ofVec (w.toH1Function.grad x)) q.exponent
      (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨C, hCtop, hC⟩ := CubeCalderonZygmund.centeredCubeH10ScalarDivergence_cz d q
  let hField : CubeEuclideanL2LpField (originCube d m) q :=
    { toField := h
      euclideanMemLp := hhq
      euclideanMemL2 := hh2 }
  have hbound :
      eLpNorm (fun x => HilbertVec.ofVec (w.toH1Function.grad x)) q.exponent
          (normalizedCubeMeasure (originCube d m)) ≤
        C * (ENNReal.ofReal (1 : ℝ))⁻¹ *
          eLpNorm (fun x => HilbertVec.ofVec (h x)) q.exponent
            (normalizedCubeMeasure (originCube d m)) := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      euclideanNorm_eq_norm_ofVec, MeasureTheory.eLpNorm_norm, hField] using
      hC m 1 hField w (by norm_num)
        (cubeDirichletDivergenceProblem_to_centered_normalized m hh2 hw)
  have hgrad_l2 : MemLp (fun x => HilbertVec.ofVec (w.toH1Function.grad x)) 2
      (normalizedCubeMeasure (originCube d m)) := by
    rw [MeasureTheory.memLp_piLp_iff]
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      w.toH1Function.grad_memL2_normalizedCubeMeasure i
  refine ⟨hgrad_l2.aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt hbound (by
    simpa only [ENNReal.ofReal_one, inv_one, mul_one] using
      ENNReal.mul_lt_top hCtop hhq.eLpNorm_lt_top)

private theorem eLpNorm_rpow_eq_lintegral_enorm {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E]
    (q : FiniteLpExponent) (μ : Measure α) (f : α → E) :
    (eLpNorm f q.exponent μ) ^ q.exponent.toReal =
      ∫⁻ x, ‖f x‖ₑ ^ q.exponent.toReal ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (zero_lt_one.trans q.one_lt).ne' q.lt_top.ne, ← ENNReal.rpow_mul]
  have hq : q.exponent.toReal ≠ 0 :=
    ENNReal.toReal_pos (zero_lt_one.trans q.one_lt).ne' q.lt_top.ne |>.ne'
  rw [one_div, inv_mul_cancel₀ hq, ENNReal.rpow_one]

/- This is the scale cancellation at the heart of the smooth component.  It
is separated from the PDE proof so the `Real.rpow` algebra remains entirely
transparent: a first derivative costs one inverse overlap scale, while the
Poincaré estimate supplies precisely one positive scale. -/
private theorem overlap_scale_rpow_cancellation {a D ell r : ℝ}
    (ha : 0 ≤ a) (hell : 0 < ell) (hr : 0 ≤ r) :
    (ENNReal.ofReal ell)^r * (ENNReal.ofReal (a * (D / ell)^2))^(r/2) =
      (ENNReal.ofReal (a * D^2))^(r/2) := by
  rw [ENNReal.ofReal_rpow_of_nonneg hell.le hr,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg ha (sq_nonneg (D / ell))) (by positivity),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hell.le r),
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg ha (sq_nonneg D)) (by positivity)]
  congr 1
  have hinv : (ell⁻¹ ^ 2) ^ (r / 2) = (ell ^ r)⁻¹ := by
    rw [← Real.rpow_two]
    rw [← Real.rpow_mul (inv_nonneg.mpr hell.le)]
    rw [show (2 : ℝ) * (r / 2) = r by ring]
    exact Real.inv_rpow hell.le r
  rw [show a * (D / ell)^2 = (a * D^2) * ell⁻¹^2 by field_simp [hell.ne'],
    Real.mul_rpow (mul_nonneg ha (sq_nonneg D)) (sq_nonneg ell⁻¹), hinv]
  field_simp [Real.rpow_pos_of_pos hell r]

/- The residual part of the splitting closes without any scale factor: global
overlap control, the finite-`q` solution-stability estimate, and the smooth
averaging residual estimate are all parent-normalized. -/
private theorem exactOverlapFiniteP_residual_rpow_le
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) {m : ℤ} {j : ℕ}
    (P : SmoothOverlapPartition (originCube d m) j) (h : Vec d → Vec d)
    (hh2 : MemLp (fun x => HilbertVec.ofVec (h x)) 2
      (normalizedCubeMeasure (originCube d m)))
    (hhq : MemLp (fun x => HilbertVec.ofVec (h x)) q.exponent
      (normalizedCubeMeasure (originCube d m)))
    (w v : H10Function (openCubeSet (originCube d m)))
    (hw : CubeDirichletDivergenceProblem (originCube d m) w h)
    (hv : CubeDirichletDivergenceProblem (originCube d m) v (P.averagingField h))
    (C : ℝ≥0∞)
    (hcomparison : eLpNorm (fun x => HilbertVec.ofVec
        (w.toH1Function.grad x - v.toH1Function.grad x)) q.exponent
        (normalizedCubeMeasure (originCube d m)) ≤
      C * eLpNorm (fun x => HilbertVec.ofVec
        (h x - P.averagingField h x)) q.exponent
        (normalizedCubeMeasure (originCube d m))) :
      (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q
        (fun x => w.toH1Function.grad x - v.toH1Function.grad x) j) ^
          q.exponent.toReal ≤
        C ^ q.exponent.toReal * exactOverlapDepthGlobalBoundConstant d ^
          q.exponent.toReal * (3 ^ d : ℝ≥0∞) *
          (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^
            q.exponent.toReal := by
  have hwq := cubeDirichletDivergenceProblem_grad_memLp q m h hh2 hhq w hw
  have hGq : MemLp (fun x => HilbertVec.ofVec (P.averagingField h x)) q.exponent
      (normalizedCubeMeasure (originCube d m)) := by
    obtain ⟨_, Gq, _, hGq, _⟩ :=
      P.exists_synchronized_averagingCompetitors h q hh2 hhq
    simpa only [hGq] using Gq.euclideanMemLp
  have hvq := cubeDirichletDivergenceProblem_grad_memLp q m (P.averagingField h)
    (by
      obtain ⟨G2, _, hG2, _, _⟩ :=
        P.exists_synchronized_averagingCompetitors h q hh2 hhq
      have hG2hilbert : MemLp (fun x => HilbertVec.ofVec (G2.toField x)) 2
          (normalizedCubeMeasure (originCube d m)) := by
        rw [MeasureTheory.memLp_piLp_iff]
        intro i
        simpa only [CubeVectorH1Function.toField, HilbertVec.ofVec, PiLp.toLp_apply] using
          H1Function.memL2_normalizedCubeMeasure (G2.coord i)
      simpa only [hG2] using hG2hilbert)
    hGq v hv
  have hdiff : MemLp (fun x => HilbertVec.ofVec
      (w.toH1Function.grad x - v.toH1Function.grad x)) q.exponent
      (normalizedCubeMeasure (originCube d m)) := by
    simpa only [map_sub] using! hwq.sub hvq
  have hglobal := cubeEuclideanPositiveBesovOverlapDepthENorm_le_global
    (originCube d m) q (fun x => w.toH1Function.grad x - v.toH1Function.grad x) j hdiff
  have hglobal_pow := ENNReal.rpow_le_rpow hglobal
    (show 0 ≤ q.exponent.toReal from ENNReal.toReal_nonneg)
  rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg] at hglobal_pow
  have hcomparison_pow := ENNReal.rpow_le_rpow hcomparison
    (show 0 ≤ q.exponent.toReal from ENNReal.toReal_nonneg)
  rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg] at hcomparison_pow
  have hresidual :=
    lintegral_enorm_rpow_sub_averagingField_le_overlapDepthENorm_rpow P h q hhq
  rw [← eLpNorm_rpow_eq_lintegral_enorm q
    (normalizedCubeMeasure (originCube d m))
    (fun x => HilbertVec.ofVec (h x - P.averagingField h x))] at hresidual
  calc
    (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q
        (fun x => w.toH1Function.grad x - v.toH1Function.grad x) j) ^
          q.exponent.toReal ≤
        exactOverlapDepthGlobalBoundConstant d ^ q.exponent.toReal *
          (eLpNorm (fun x => HilbertVec.ofVec
            (w.toH1Function.grad x - v.toH1Function.grad x)) q.exponent
            (normalizedCubeMeasure (originCube d m))) ^ q.exponent.toReal := hglobal_pow
    _ ≤ exactOverlapDepthGlobalBoundConstant d ^ q.exponent.toReal *
          (C ^ q.exponent.toReal *
            (eLpNorm (fun x => HilbertVec.ofVec
              (h x - P.averagingField h x)) q.exponent
              (normalizedCubeMeasure (originCube d m))) ^ q.exponent.toReal) := by
          gcongr
    _ = C ^ q.exponent.toReal * exactOverlapDepthGlobalBoundConstant d ^
          q.exponent.toReal *
          (eLpNorm (fun x => HilbertVec.ofVec
            (h x - P.averagingField h x)) q.exponent
            (normalizedCubeMeasure (originCube d m))) ^ q.exponent.toReal := by ring
    _ ≤ C ^ q.exponent.toReal * exactOverlapDepthGlobalBoundConstant d ^
          q.exponent.toReal * ((3 ^ d : ℝ≥0∞) *
          (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^
            q.exponent.toReal) :=
      mul_le_mul_right hresidual _
    _ = _ := by ring

private theorem exactOverlapFiniteP_smooth_rpow_le
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) {m : ℤ} {j : ℕ}
    (h : Vec d → Vec d)
    (hhq : MemLp (fun x => HilbertVec.ofVec (h x)) q.exponent
      (normalizedCubeMeasure (originCube d m)))
    (V : CubeVectorW1pFunction (originCube d m) q)
    (Csplit Cpoin : ℝ≥0∞)
    (hpoin : (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q V.toField j) ^
        q.exponent.toReal ≤ Cpoin *
          (ENNReal.ofReal (cubeScaleFactor (originCube d m) / (3 : ℝ) ^ j)) ^
            q.exponent.toReal *
          (eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
            (normalizedCubeMeasure (originCube d m))) ^ q.exponent.toReal)
    (hcomparison : eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
        (normalizedCubeMeasure (originCube d m)) ≤ Csplit *
          eLpNorm (fun x => HilbertMat.ofMat
            (((concreteSmoothOverlapPartition (originCube d m) j).averagingCompetitorW1p h q).jacobian x))
            q.exponent
            (normalizedCubeMeasure (originCube d m))) :
    (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q V.toField j) ^
        q.exponent.toReal ≤
      Cpoin * Csplit ^ q.exponent.toReal *
      ((if q.exponent.toReal ≤ 2 then 1 else
        (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (q.exponent.toReal / 2 - 1)) *
      (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
      (ENNReal.ofReal ((3 ^ d : ℝ) *
        (smoothOverlapPartitionDerivativeConstant d) ^ 2)) ^
          (q.exponent.toReal / 2) *
      (if q.exponent.toReal ≤ 2 then 1 else
        (3 ^ d : ℝ≥0∞) ^ (q.exponent.toReal / 2 - 1)) *
      (3 ^ d : ℝ≥0∞)) *
      (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^
        q.exponent.toReal := by
  let P := concreteSmoothOverlapPartition (originCube d m) j
  let ell : ℝ := cubeScaleFactor (originCube d m) / (3 : ℝ) ^ j
  let r : ℝ := q.exponent.toReal
  let A : ℝ≥0∞ :=
    (if r ≤ 2 then 1 else
      (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (r / 2 - 1)) *
    (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
    (ENNReal.ofReal ((3 ^ d : ℝ) *
      (smoothOverlapPartitionDerivativeConstant d) ^ 2)) ^ (r / 2) *
    (if r ≤ 2 then 1 else (3 ^ d : ℝ≥0∞) ^ (r / 2 - 1)) * (3 ^ d : ℝ≥0∞)
  have hell : 0 < ell := by
    exact div_pos (cubeScaleFactor_pos' (originCube d m))
      (pow_pos (by norm_num : (0 : ℝ) < 3) j)
  have hjacobian := SmoothOverlapPartition.lintegral_enorm_rpow_averagingCompetitorW1p_jacobian_le_depthENorm
    P h q hhq
  have hjacobian' :
      (eLpNorm (fun x => HilbertMat.ofMat ((P.averagingCompetitorW1p h q).jacobian x))
        q.exponent (normalizedCubeMeasure (originCube d m))) ^ r ≤
        ((if r ≤ 2 then 1 else
          (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (r / 2 - 1)) *
        (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
        (ENNReal.ofReal ((3 ^ d : ℝ) *
          (P.coordDerivConstant / ell) ^ 2)) ^ (r / 2) *
        (if r ≤ 2 then 1 else (3 ^ d : ℝ≥0∞) ^ (r / 2 - 1)) *
        (3 ^ d : ℝ≥0∞)) *
        (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^ r := by
    rw [eLpNorm_rpow_eq_lintegral_enorm]
    simpa only [P, ell, r] using hjacobian
  have hcomparison_pow := ENNReal.rpow_le_rpow hcomparison
    (show 0 ≤ r from ENNReal.toReal_nonneg)
  rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg] at hcomparison_pow
  have hscale :
      (ENNReal.ofReal ell) ^ r *
        (ENNReal.ofReal ((3 ^ d : ℝ) *
          (P.coordDerivConstant / ell) ^ 2)) ^ (r / 2) =
        (ENNReal.ofReal ((3 ^ d : ℝ) *
          (smoothOverlapPartitionDerivativeConstant d) ^ 2)) ^ (r / 2) := by
    simpa only [P] using! overlap_scale_rpow_cancellation
      (a := (3 ^ d : ℝ)) (D := smoothOverlapPartitionDerivativeConstant d)
      (ell := ell) (r := r) (by positivity) hell ENNReal.toReal_nonneg
  calc
    (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q V.toField j) ^ r ≤
        Cpoin * (ENNReal.ofReal ell) ^ r *
          (eLpNorm (fun x => HilbertMat.ofMat (V.jacobian x)) q.exponent
            (normalizedCubeMeasure (originCube d m))) ^ r := by
      simpa only [ell, r] using hpoin
    _ ≤ Cpoin * (ENNReal.ofReal ell) ^ r *
          (Csplit ^ r * (eLpNorm (fun x => HilbertMat.ofMat
            ((P.averagingCompetitorW1p h q).jacobian x)) q.exponent
            (normalizedCubeMeasure (originCube d m))) ^ r) := by gcongr
    _ ≤ Cpoin * (ENNReal.ofReal ell) ^ r *
          (Csplit ^ r *
          (((if r ≤ 2 then 1 else
            (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (r / 2 - 1)) *
          (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
          (ENNReal.ofReal ((3 ^ d : ℝ) *
            (P.coordDerivConstant / ell) ^ 2)) ^ (r / 2) *
          (if r ≤ 2 then 1 else (3 ^ d : ℝ≥0∞) ^ (r / 2 - 1)) *
          (3 ^ d : ℝ≥0∞)) *
          (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^ r)) := by
      gcongr
    _ = Cpoin * Csplit ^ r * A *
      (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^ r := by
      rw [show Cpoin * (ENNReal.ofReal ell) ^ r *
          (Csplit ^ r *
          (((if r ≤ 2 then 1 else
            (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (r / 2 - 1)) *
          (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
          (ENNReal.ofReal ((3 ^ d : ℝ) *
            (P.coordDerivConstant / ell) ^ 2)) ^ (r / 2) *
          (if r ≤ 2 then 1 else (3 ^ d : ℝ≥0∞) ^ (r / 2 - 1)) *
          (3 ^ d : ℝ≥0∞)) *
          (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^ r)) =
          Cpoin * Csplit ^ r *
          ((if r ≤ 2 then 1 else
            (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (r / 2 - 1)) *
          (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
          ((ENNReal.ofReal ell) ^ r *
            (ENNReal.ofReal ((3 ^ d : ℝ) *
              (P.coordDerivConstant / ell) ^ 2)) ^ (r / 2)) *
          (if r ≤ 2 then 1 else (3 ^ d : ℝ≥0∞) ^ (r / 2 - 1)) *
          (3 ^ d : ℝ≥0∞)) *
          (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^ r by ring]
      rw [hscale]
    _ = _ := by rfl

/-- One exact-overlap depth of the finite-`p` gradient energy of a cube
Dirichlet divergence solution is controlled by the corresponding depth of its
datum, uniformly in both the root scale and the depth. -/
theorem exists_exactOverlapFiniteP_oneDepth_cz
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (j : ℕ) (h : Vec d → Vec d),
      MemLp (fun x => HilbertVec.ofVec (h x)) 2
        (normalizedCubeMeasure (originCube d m)) →
      MemLp (fun x => HilbertVec.ofVec (h x)) q.exponent
        (normalizedCubeMeasure (originCube d m)) →
      ∀ w : H10Function (openCubeSet (originCube d m)),
      CubeDirichletDivergenceProblem (originCube d m) w h →
        (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q
          w.toH1Function.grad j) ^ q.exponent.toReal ≤
          C * (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^
            q.exponent.toReal := by
  obtain ⟨Csplit, hCsplit_top, hsplit⟩ := exists_exactOverlapFiniteP_pdeSplitting d q
  obtain ⟨Cpoin, hCpoin_top, hpoin⟩ :=
    exists_cubeEuclideanPositiveBesovOverlapDepthENorm_rpow_le (d := d) q
  let A : ℝ≥0∞ :=
    ((if q.exponent.toReal ≤ 2 then 1 else
      (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^ (q.exponent.toReal / 2 - 1)) *
    (Fintype.card (Fin d × Fin d) : ℝ≥0∞) *
    (ENNReal.ofReal ((3 ^ d : ℝ) *
      (smoothOverlapPartitionDerivativeConstant d) ^ 2)) ^
        (q.exponent.toReal / 2) *
    (if q.exponent.toReal ≤ 2 then 1 else
      (3 ^ d : ℝ≥0∞) ^ (q.exponent.toReal / 2 - 1)) *
    (3 ^ d : ℝ≥0∞))
  let Cres : ℝ≥0∞ := Csplit ^ q.exponent.toReal *
    exactOverlapDepthGlobalBoundConstant d ^ q.exponent.toReal * (3 ^ d : ℝ≥0∞)
  let Csmooth : ℝ≥0∞ := Cpoin * Csplit ^ q.exponent.toReal * A
  have hA_top : A < ∞ := by
    dsimp [A]
    have hder : (ENNReal.ofReal ((3 ^ d : ℝ) *
        smoothOverlapPartitionDerivativeConstant d ^ 2)) ^
        (q.exponent.toReal / 2) < ∞ :=
      ENNReal.rpow_lt_top_of_nonneg
        (div_nonneg ENNReal.toReal_nonneg (by norm_num)) ENNReal.ofReal_ne_top
    have hthree : (3 ^ d : ℝ≥0∞) < ∞ :=
      (ENNReal.pow_ne_top ENNReal.ofNat_ne_top).lt_top
    by_cases hq : q.exponent.toReal ≤ 2
    · simp only [if_pos hq, one_mul, mul_one]
      exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top (ENNReal.natCast_ne_top (Fintype.card (Fin d × Fin d))).lt_top hder) hthree
    · simp only [if_neg hq]
      have hr : 0 ≤ q.exponent.toReal / 2 - 1 := by
        have htwo : 2 < q.exponent.toReal := lt_of_not_ge hq
        linarith
      have hdim : (Fintype.card (Fin d × Fin d) : ℝ≥0∞) ^
          (q.exponent.toReal / 2 - 1) < ∞ :=
        ENNReal.rpow_lt_top_of_nonneg hr
          (ENNReal.natCast_ne_top (Fintype.card (Fin d × Fin d)))
      have hoverlap : (3 ^ d : ℝ≥0∞) ^ (q.exponent.toReal / 2 - 1) < ∞ :=
        ENNReal.rpow_lt_top_of_nonneg hr (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
      exact ENNReal.mul_lt_top
        (ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (ENNReal.mul_lt_top hdim
            (ENNReal.natCast_ne_top _).lt_top) hder)
          hoverlap)
        hthree
  have hthree : (3 ^ d : ℝ≥0∞) < ∞ :=
    (ENNReal.pow_ne_top ENNReal.ofNat_ne_top).lt_top
  have htri_top : exactOverlapDepthTriangleConstant q < ∞ := by
    dsimp [exactOverlapDepthTriangleConstant]
    exact (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)).lt_top
  have hglobal_top : exactOverlapDepthGlobalBoundConstant d ≠ ∞ := by
    unfold exactOverlapDepthGlobalBoundConstant
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.pow_ne_top (by norm_num))
  have hCres_top : Cres < ∞ := by
    dsimp [Cres]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hCsplit_top.ne)
        (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hglobal_top))
      hthree
  have hCsmooth_top : Csmooth < ∞ := by
    dsimp [Csmooth]
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hCpoin_top.lt_top
        (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hCsplit_top.ne))
      hA_top
  refine ⟨exactOverlapDepthTriangleConstant q * (Cres + Csmooth),
    ENNReal.mul_lt_top htri_top ((ENNReal.add_lt_top).2 ⟨hCres_top, hCsmooth_top⟩), ?_⟩
  intro m j h hh2 hhq w hw
  let P : SmoothOverlapPartition (originCube d m) j :=
    concreteSmoothOverlapPartition (originCube d m) j
  obtain ⟨v, V, hv, hVfield, hcomparison, hHessiancomparison⟩ :=
    hsplit m j P h hh2 hhq w hw
  have hwq := cubeDirichletDivergenceProblem_grad_memLp q m h hh2 hhq w hw
  have hvq : MemLp (fun x => HilbertVec.ofVec (v.toH1Function.grad x)) q.exponent
      (normalizedCubeMeasure (originCube d m)) := by
    rw [← hVfield]
    exact V.euclideanMemLp
  have htriangle := cubeEuclideanPositiveBesovOverlapDepthENorm_sub_add_rpow_le
    (originCube d m) q w.toH1Function.grad v.toH1Function.grad j hwq hvq
  have hresidual := exactOverlapFiniteP_residual_rpow_le q P h hh2 hhq w v hw hv
    Csplit hcomparison
  have hsmooth := exactOverlapFiniteP_smooth_rpow_le q h hhq V Csplit Cpoin
    (hpoin (originCube d m) j V) (by simpa only [P] using hHessiancomparison)
  calc
    (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q
        w.toH1Function.grad j) ^ q.exponent.toReal ≤
        exactOverlapDepthTriangleConstant q *
          ((cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q
            (fun x => w.toH1Function.grad x - v.toH1Function.grad x) j) ^
              q.exponent.toReal +
          (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q
            v.toH1Function.grad j) ^ q.exponent.toReal) := htriangle
    _ ≤ exactOverlapDepthTriangleConstant q *
          ((Csplit ^ q.exponent.toReal * exactOverlapDepthGlobalBoundConstant d ^
            q.exponent.toReal * (3 ^ d : ℝ≥0∞) +
            Cpoin * Csplit ^ q.exponent.toReal * A) *
          (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^
            q.exponent.toReal) := by
      apply mul_le_mul_right
      calc
        (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q
            (fun x => w.toH1Function.grad x - v.toH1Function.grad x) j) ^
              q.exponent.toReal +
          (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q
            v.toH1Function.grad j) ^ q.exponent.toReal ≤
          (Csplit ^ q.exponent.toReal * exactOverlapDepthGlobalBoundConstant d ^
            q.exponent.toReal * (3 ^ d : ℝ≥0∞)) *
          (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^
            q.exponent.toReal +
          (Cpoin * Csplit ^ q.exponent.toReal * A) *
          (cubeEuclideanPositiveBesovOverlapDepthENorm (originCube d m) q h j) ^
            q.exponent.toReal := by
              apply add_le_add hresidual
              simpa only [hVfield] using hsmooth
        _ = _ := by ring
    _ = _ := by
      simp only [Cres, Csmooth]
      ring

end

end Homogenization
