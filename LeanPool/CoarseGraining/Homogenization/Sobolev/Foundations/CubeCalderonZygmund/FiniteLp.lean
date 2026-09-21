/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectedOneLevelTail
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaIntegration
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaParameters
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CenteredCubeEuclideanL2
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWsp
import LeanPool.CoarseGraining.Homogenization.Sobolev.SmoothCompactSupport

/-!
# Finite-exponent cube Calderón--Zygmund interface

The source-facing finite-`L^p` carriers and weak solution predicates for the
constant-coefficient cube Calderón--Zygmund argument.  The one-level
good-`λ` input remains internal to this module while the source-facing
declarations below keep the manuscript's supplied-solution interfaces exact.
-/

namespace Homogenization

open scoped ENNReal

noncomputable section

structure CubeEuclideanL2LpField {d : ℕ} (Q : TriadicCube d)
    (p : FiniteLpExponent) extends CubeEuclideanLpField Q p where
  euclideanMemL2 :
    MeasureTheory.MemLp (fun x => HilbertVec.ofVec (toField x)) 2
      (normalizedCubeMeasure Q)

structure CubeEuclideanWspL2Field {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent)
    extends CubeEuclideanWspField Q s p where
  euclideanMemL2 :
    MeasureTheory.MemLp (fun x => HilbertVec.ofVec (toField x)) 2
      (normalizedCubeMeasure Q)

noncomputable def CubeEuclideanL2LpField.toLpTwo {d : ℕ}
    {Q : TriadicCube d} {p : FiniteLpExponent}
    (F : CubeEuclideanL2LpField Q p) :
    CubeEuclideanLpField Q FiniteLpExponent.two :=
  ⟨F.toField, F.euclideanMemL2⟩

noncomputable def CubeEuclideanWspL2Field.toLpTwo {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspL2Field Q s p) :
    CubeEuclideanLpField Q FiniteLpExponent.two :=
  ⟨F.toField, F.euclideanMemL2⟩

def IsCenteredCubeW10pScalarDivergenceSolution {d : ℕ}
    {q : FiniteLpExponent} (m : ℤ) (sigma0 : ℝ)
    (w : W10pFunction (openCubeSet (originCube d m)) q.exponent)
    (h : CubeEuclideanLpField (originCube d m) q) : Prop :=
  ∀ phi : SmoothCompactSupportFunction
      ⟨openCubeSet (originCube d m), isOpen_openCubeSet (originCube d m)⟩,
    sigma0 * ∫ x, vecDot (w.grad x) (phi.gradient x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      -∫ x, vecDot (h.toField x) (phi.gradient x)
        ∂(centeredCubeDomain d m).normalizedVolume

def IsCenteredCubeH10ScalarDivergenceSolution {d : ℕ}
    (m : ℤ) (sigma0 : ℝ)
    (w : H10Function (openCubeSet (originCube d m)))
    (h : CubeEuclideanLpField (originCube d m)
      FiniteLpExponent.two) : Prop :=
  ∀ phi : H10Function (openCubeSet (originCube d m)),
    sigma0 * ∫ x,
        vecDot (w.toH1Function.grad x) (phi.toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume =
      -∫ x, vecDot (h.toField x) (phi.toH1Function.grad x)
        ∂(centeredCubeDomain d m).normalizedVolume

namespace CubeCalderonZygmund

open MeasureTheory Set

private noncomputable def finiteLpExponentSucc (p : FiniteLpExponent) :
    FiniteLpExponent where
  exponent := p.exponent + 1
  one_lt := lt_of_lt_of_le p.one_lt (le_add_of_nonneg_right bot_le)
  lt_top := ENNReal.add_lt_top.mpr ⟨p.lt_top, by norm_num⟩

private theorem finiteLpExponentSucc_toReal (p : FiniteLpExponent) :
    (finiteLpExponentSucc p).exponent.toReal = p.exponent.toReal + 1 := by
  simp only [finiteLpExponentSucc]
  rw [ENNReal.toReal_add p.lt_top.ne ENNReal.one_ne_top]
  norm_num

private theorem finiteLpExponent_lt_succ (p : FiniteLpExponent) :
    p.exponent.toReal < (finiteLpExponentSucc p).exponent.toReal := by
  rw [finiteLpExponentSucc_toReal]
  linarith

private theorem sqWeightedMeasure_univ_ne_top_of_memLp_two
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} {f : α → E}
    (hf : MeasureTheory.MemLp f 2 μ) :
    sqWeightedMeasure f μ Set.univ ≠ ∞ := by
  rw [sqWeightedMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  simpa only [MeasureTheory.Measure.restrict_univ, ← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) zero_le_two,
    ENNReal.toReal_ofNat, Real.rpow_two] using
    (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
      hf.eLpNorm_lt_top).ne

private theorem sqWeightedMeasure_univ_eq_eLpNorm_two_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} (f : α → E) :
    sqWeightedMeasure f μ Set.univ = (eLpNorm f 2 μ) ^ (2 : ℕ) := by
  rw [sqWeightedMeasure, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  change (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ (2 : ℕ)) ∂μ) = _
  simp_rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [← ENNReal.rpow_natCast,
    MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    ← ENNReal.rpow_mul]
  norm_num

private theorem lintegral_ofReal_norm_rpow_ne_top_of_memLp
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} {p : FiniteLpExponent} {f : α → E}
    (hf : MeasureTheory.MemLp f p.exponent μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) ∂μ) ≠ ∞ := by
  simpa only [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg] using
    (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne hf.eLpNorm_lt_top).ne

private theorem lintegral_ofReal_norm_rpow_div_ne_top_of_memLp
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} {p : FiniteLpExponent} {a : ℝ} {f : α → E}
    (ha : 0 < a) (hf : MeasureTheory.MemLp f p.exponent μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal /
      a ^ (p.exponent.toReal - 2)) ∂μ) ≠ ∞ := by
  let b : ℝ := a ^ (p.exponent.toReal - 2)
  have hb : 0 < b := by
    exact Real.rpow_pos_of_pos ha _
  have hpoint (x : α) :
      ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal / b) =
        (ENNReal.ofReal b)⁻¹ * ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) := by
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul
      (inv_nonneg.mpr hb.le), ENNReal.ofReal_inv_of_pos hb]
  have hmeas : AEMeasurable
      (fun x => ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal)) μ :=
    (hf.aestronglyMeasurable.norm.aemeasurable.pow aemeasurable_const).ennreal_ofReal
  simp_rw [show a ^ (p.exponent.toReal - 2) = b by rfl, hpoint]
  rw [MeasureTheory.lintegral_const_mul'' _ hmeas]
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_ne_zero_iff.mpr hb))
    (lintegral_ofReal_norm_rpow_ne_top_of_memLp hf)

private theorem toReal_eLpNorm_two_sq_eq_integral_norm_sq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] {μ : MeasureTheory.Measure α} {f : α → E}
    (hf : MeasureTheory.MemLp f 2 μ) :
    (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ (2 : ℕ) =
      ∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ := by
  have hpow : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  have hnorm := hf.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hsq : (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ (2 : ℕ) =
      ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := by
    rw [hnorm, hpow]
    have hnonneg : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ :=
      MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)
    rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hnonneg _)]
    rw [show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt hnonneg
  calc
    (ENNReal.toReal (MeasureTheory.eLpNorm f 2 μ)) ^ (2 : ℕ) =
        ∫ x, ‖f x‖ ^ (2 : ℝ) ∂μ := hsq
    _ = _ := by
      congr 1 with x
      rw [Real.rpow_two]

private theorem centeredCube_normalizedVolume_eq_smul_openCubeVolume
    {d : ℕ} (m : ℤ) :
    (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        MeasureTheory.volume.restrict (openCubeSet (originCube d m)) := by
  change (cubeBoundedMeasurableDomain (originCube d m)).normalizedVolume = _
  rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
    normalizedCubeMeasure, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

private theorem rawWeak_of_isCenteredCubeH10ScalarDivergenceSolution
    {d : ℕ} {m : ℤ} {sigma0 : ℝ}
    {u : H10Function (openCubeSet (originCube d m))}
    {h : CubeEuclideanLpField (originCube d m) FiniteLpExponent.two}
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h) :
    ∀ psi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet (originCube d m),
          vecDot (h.toField x) (psi.toH1Function.grad x) ∂volume := by
  intro psi
  have hnormalized := hsolution psi
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume,
    MeasureTheory.integral_smul_measure,
    MeasureTheory.integral_smul_measure] at hnormalized
  have hfactor_pos :
      0 < (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal := by
    rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (cubeVolume_nonneg _))]
    exact inv_pos.mpr (cubeVolume_pos _)
  apply (mul_left_cancel₀ hfactor_pos.ne')
  calc
    (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
        (sigma0 * ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume) =
      sigma0 *
        ((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          ∫ x in openCubeSet (originCube d m),
            vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume) := by
          ring
    _ = -((ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
          ∫ x in openCubeSet (originCube d m),
            vecDot (h.toField x) (psi.toH1Function.grad x) ∂volume) := hnormalized
    _ = (ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)).toReal *
        (-∫ x in openCubeSet (originCube d m),
          vecDot (h.toField x) (psi.toH1Function.grad x) ∂volume) := by
          ring

private theorem memVectorL2_openCubeSet_of_euclideanMemLpTwo
    {d : ℕ} (Q : TriadicCube d) {F : Vec d → Vec d}
    (hF : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F x)) 2
      (normalizedCubeMeasure Q)) :
    MemVectorL2 (openCubeSet Q) F := by
  have hvec : MeasureTheory.MemLp F 2 (normalizedCubeMeasure Q) := by
    apply MeasureTheory.MemLp.of_eval
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF.eval_piLp i
  have hle :
      cubeMeasure Q ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    have hvol_nonneg : 0 ≤ cubeVolume Q := cubeVolume_nonneg Q
    have hmul :
        ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hvol_nonneg]
      have hreal : cubeVolume Q * (cubeVolume Q)⁻¹ = 1 := by
        field_simp [(cubeVolume_pos Q).ne']
      rw [hreal]
      norm_num
    have heq : ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q = cubeMeasure Q := by
      rw [normalizedCubeMeasure]
      ext s
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply]
      change ENNReal.ofReal (cubeVolume Q) *
          (ENNReal.ofReal ((cubeVolume Q)⁻¹) * (cubeMeasure Q) s) =
        (cubeMeasure Q) s
      rw [← mul_assoc, hmul, one_mul]
    exact le_of_eq heq.symm
  have hcube : MeasureTheory.MemLp F 2 (cubeMeasure Q) :=
    hvec.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q))
      ENNReal.ofReal_ne_top hle
  simpa only [MemVectorL2, volumeMeasureOn, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using hcube

private theorem memLp_openCubeSet_of_euclideanMemLp
    {d : ℕ} (Q : TriadicCube d) {p : FiniteLpExponent} {F : Vec d → Vec d}
    (hF : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (normalizedCubeMeasure Q)) :
    MeasureTheory.MemLp (hilbertifyVecField F) p.exponent
      (volume.restrict (openCubeSet Q)) := by
  have hle :
      cubeMeasure Q ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    have hvol_nonneg : 0 ≤ cubeVolume Q := cubeVolume_nonneg Q
    have hmul :
        ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal ((cubeVolume Q)⁻¹) = 1 := by
      rw [← ENNReal.ofReal_mul hvol_nonneg]
      have hreal : cubeVolume Q * (cubeVolume Q)⁻¹ = 1 := by
        field_simp [(cubeVolume_pos Q).ne']
      rw [hreal]
      norm_num
    have heq : ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q = cubeMeasure Q := by
      rw [normalizedCubeMeasure]
      ext s
      rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.smul_apply]
      change ENNReal.ofReal (cubeVolume Q) *
          (ENNReal.ofReal ((cubeVolume Q)⁻¹) * (cubeMeasure Q) s) =
        (cubeMeasure Q) s
      rw [← mul_assoc, hmul, one_mul]
    exact le_of_eq heq.symm
  have hcube : MeasureTheory.MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (cubeMeasure Q) :=
    hF.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q))
      ENNReal.ofReal_ne_top hle
  simpa only [hilbertifyVecField, cubeMeasure,
    volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using! hcube

private theorem sqWeightedMeasure_restrict_apply_eq_inter
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} {B T : Set α} {f : α → E}
    (hB : MeasurableSet B) :
    sqWeightedMeasure f (μ.restrict B) T = sqWeightedMeasure f μ (T ∩ B) := by
  change ((μ.restrict B).withDensity fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) T =
    (μ.withDensity fun x => ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) (T ∩ B)
  rw [← MeasureTheory.restrict_withDensity hB]
  exact Measure.restrict_apply' hB

private theorem sqWeightedMeasure_smul_measure
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} {c : ℝ≥0∞} {T : Set α} {f : α → E} :
    sqWeightedMeasure f (c • μ) T = c * sqWeightedMeasure f μ T := by
  unfold sqWeightedMeasure
  rw [MeasureTheory.withDensity_smul_measure]
  rfl

private theorem norm_gradToHilbertVectorL2_le_sigmaInv_datum
    {d : ℕ} {m : ℤ} {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (u : H10Function (openCubeSet (originCube d m)))
    {H : Vec d → Vec d} (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hweak : ∀ psi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet (originCube d m),
          vecDot (H x) (psi.toH1Function.grad x) ∂volume) :
    ‖u.toH1Function.gradToHilbertVectorL2‖ ≤
      sigma0⁻¹ * ‖toHilbertVectorL2OfVecField hH‖ := by
  let G : HilbertVectorL2 (openCubeSet (originCube d m)) :=
    u.toH1Function.gradToHilbertVectorL2
  let K : HilbertVectorL2 (openCubeSet (originCube d m)) :=
    toHilbertVectorL2OfVecField hH
  have hgrad_integral :
      ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (u.toH1Function.grad x) ∂volume =
        ‖G‖ ^ 2 := by
    calc
      ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (u.toH1Function.grad x) ∂volume =
        inner ℝ G G := by
          simpa [G, H1Function.gradToHilbertVectorL2] using
            (inner_toHilbertVectorL2OfVecField_eq_integral
              (U := openCubeSet (originCube d m))
              u.toH1Function.grad_memVectorL2
              u.toH1Function.grad_memVectorL2).symm
      _ = ‖G‖ ^ 2 := real_inner_self_eq_norm_sq G
  have hpair_integral :
      ∫ x in openCubeSet (originCube d m),
          vecDot (H x) (u.toH1Function.grad x) ∂volume =
        inner ℝ K G := by
    simpa [K, G, H1Function.gradToHilbertVectorL2] using
      (inner_toHilbertVectorL2OfVecField_eq_integral
        (U := openCubeSet (originCube d m)) hH
        u.toH1Function.grad_memVectorL2).symm
  have henergy := hweak u
  rw [hgrad_integral, hpair_integral] at henergy
  have henergy_le : sigma0 * ‖G‖ ^ 2 ≤ ‖K‖ * ‖G‖ := by
    calc
      sigma0 * ‖G‖ ^ 2 = -inner ℝ K G := henergy
      _ ≤ |inner ℝ K G| := neg_le_abs _
      _ ≤ ‖K‖ * ‖G‖ := abs_real_inner_le_norm K G
  by_cases hGzero : ‖G‖ = 0
  · rw [hGzero]
    exact mul_nonneg (inv_nonneg.mpr hsigma0.le) (norm_nonneg K)
  · have hGpos : 0 < ‖G‖ := lt_of_le_of_ne (norm_nonneg G) (Ne.symm hGzero)
    have hsigmaG : sigma0 * ‖G‖ ≤ ‖K‖ := by
      apply le_of_mul_le_mul_right _ hGpos
      simpa [pow_two, mul_assoc] using henergy_le
    have hdiv : ‖G‖ ≤ ‖K‖ / sigma0 := by
      apply (le_div_iff₀ hsigma0).2
      simpa [mul_comm] using hsigmaG
    simpa [G, K, div_eq_mul_inv, mul_comm] using hdiv

private theorem centeredCubeNormalized_eLpNorm_grad_le_scaledDatum
    {d : ℕ} {m : ℤ} {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0)
    (u : H10Function (openCubeSet (originCube d m)))
    {H : Vec d → Vec d} (hH : MemVectorL2 (openCubeSet (originCube d m)) H)
    (hweak : ∀ psi : H10Function (openCubeSet (originCube d m)),
      sigma0 * ∫ x in openCubeSet (originCube d m),
          vecDot (u.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume =
        -∫ x in openCubeSet (originCube d m),
          vecDot (H x) (psi.toH1Function.grad x) ∂volume) :
    eLpNorm (hilbertifyVecField u.toH1Function.grad) 2
        (centeredCubeDomain d m).normalizedVolume ≤
      eLpNorm (sigma0⁻¹ • hilbertifyVecField H) 2
        (centeredCubeDomain d m).normalizedVolume := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)
  have hc : c ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (inv_pos.mpr (cubeVolume_pos (originCube d m))))
  have henergy := norm_gradToHilbertVectorL2_le_sigmaInv_datum hsigma0 u hH hweak
  have hraw :
      eLpNorm (hilbertifyVecField u.toH1Function.grad) 2
          (volume.restrict (openCubeSet (originCube d m))) ≤
        eLpNorm (sigma0⁻¹ • hilbertifyVecField H) 2
          (volume.restrict (openCubeSet (originCube d m))) := by
    rw [MeasureTheory.eLpNorm_const_smul,
      eLpNorm_hilbertify_grad_two_eq_ofReal_norm_gradToHilbertVectorL2,
      eLpNorm_hilbertifyVecField_two_eq_ofReal_norm_toHilbertVectorL2 hH]
    rw [← ofReal_norm,
      Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hsigma0.le)]
    exact ENNReal.ofReal_le_ofReal henergy
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume]
  change eLpNorm (hilbertifyVecField u.toH1Function.grad) 2
      (c • volume.restrict (openCubeSet (originCube d m))) ≤
    eLpNorm (sigma0⁻¹ • hilbertifyVecField H) 2
      (c • volume.restrict (openCubeSet (originCube d m)))
  rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero hc,
    MeasureTheory.eLpNorm_smul_measure_of_ne_zero hc]
  exact mul_le_mul_right hraw _

/-- The energy (`q = 2`) endpoint for the supplied-solution cube
Calderón--Zygmund interface; this is the base case used by the all-exponent
assembly. -/
theorem centeredCubeH10ScalarDivergence_cz_two
    {d : ℕ} [NeZero d] (m : ℤ) (sigma0 : ℝ)
    (h : CubeEuclideanL2LpField (originCube d m) FiniteLpExponent.two)
    (u : H10Function (openCubeSet (originCube d m)))
    (hsigma0 : 0 < sigma0)
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo) :
    (centeredCubeDomain d m).normalizedEuclideanLpENorm
        FiniteLpExponent.two.exponent u.toH1Function.grad ≤
      (ENNReal.ofReal sigma0)⁻¹ *
        (centeredCubeDomain d m).normalizedEuclideanLpENorm
          FiniteLpExponent.two.exponent h.toField := by
  have hH : MemVectorL2 (openCubeSet (originCube d m)) h.toField :=
    memVectorL2_openCubeSet_of_euclideanMemLpTwo (originCube d m)
      h.euclideanMemL2
  have hnormalized := centeredCubeNormalized_eLpNorm_grad_le_scaledDatum
    hsigma0 u hH
    (rawWeak_of_isCenteredCubeH10ScalarDivergenceSolution hsolution)
  rw [MeasureTheory.eLpNorm_const_smul] at hnormalized
  rw [← ofReal_norm,
    Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le),
    ENNReal.ofReal_inv_of_pos hsigma0] at hnormalized
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm,
    FiniteLpExponent.two_exponent, euclideanNorm_eq_norm_ofVec,
    MeasureTheory.eLpNorm_norm, hilbertifyVecField] using! hnormalized

private theorem reflectedGoodLambdaCutoff_sq_eq_normalized_energy
    {d : ℕ} {m : ℤ} (depth : ℕ) (eps sigma0 : ℝ)
    (u : H10Function (openCubeSet (originCube d m))) (H : Vec d → Vec d) :
    reflectedGoodLambdaCutoff m depth eps sigma0 u H ^ (2 : ℕ) =
      (3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d *
        ((∫ x, ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ)
            ∂(centeredCubeDomain d m).normalizedVolume) +
          (eps⁻¹) ^ (2 : ℕ) *
            ∫ x, ‖sigma0⁻¹ • hilbertifyVecField H x‖ ^ (2 : ℕ)
              ∂(centeredCubeDomain d m).normalizedVolume) := by
  let s : ℝ := cubeScaleFactor (originCube d m)
  let L : ℝ := 10 * (3 : ℝ) ^ depth
  let V : ℝ := cubeVolume (originCube d m)
  have hs : 0 < s := by
    dsimp only [s]
    simpa [cubeScaleFactor] using!
      zpow_pos (by norm_num : (0 : ℝ) < 3) m
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hV : V = s ^ d := by
    simp only [V, s, cubeVolume_eq_scaleFactor_pow]
  have hnormal : (ENNReal.ofReal (V⁻¹)).toReal = V⁻¹ := by
    rw [ENNReal.toReal_ofReal]
    exact inv_nonneg.mpr (by rw [hV]; positivity)
  have hmeasure : (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal (V⁻¹) • volume.restrict (openCubeSet (originCube d m)) := by
    simpa only [V] using centeredCube_normalizedVolume_eq_smul_openCubeVolume m
  have hIu :
      (∫ x, ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ)
          ∂(centeredCubeDomain d m).normalizedVolume) =
        V⁻¹ * ∫ x in openCubeSet (originCube d m),
          ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume := by
    rw [hmeasure, MeasureTheory.integral_smul_measure, hnormal]
    exact smul_eq_mul _ _
  have hIH :
      (∫ x, ‖sigma0⁻¹ • hilbertifyVecField H x‖ ^ (2 : ℕ)
          ∂(centeredCubeDomain d m).normalizedVolume) =
        V⁻¹ * ∫ x in openCubeSet (originCube d m),
          ‖sigma0⁻¹ • hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume := by
    rw [hmeasure, MeasureTheory.integral_smul_measure, hnormal]
    exact smul_eq_mul _ _
  have hscaled :
      (∫ x in openCubeSet (originCube d m),
          ‖sigma0⁻¹ • hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume) =
        (sigma0⁻¹) ^ (2 : ℕ) *
          ∫ x in openCubeSet (originCube d m),
            ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1
    funext x
    rw [norm_smul, Real.norm_eq_abs]
    calc
      (|sigma0⁻¹| * ‖hilbertifyVecField H x‖) ^ (2 : ℕ) =
          |sigma0⁻¹| ^ (2 : ℕ) * ‖hilbertifyVecField H x‖ ^ (2 : ℕ) := by ring
      _ = _ := by rw [sq_abs]
  have hcoef :
      ((2 * ((s / 2) / L)) ^ d)⁻¹ * (3 : ℝ) ^ d =
        (3 : ℝ) ^ d * L ^ d * V⁻¹ := by
    rw [hV]
    rw [← inv_pow]
    field_simp [hs.ne', hL.ne']
    rw [div_pow]
    exact div_mul_cancel₀ _ (pow_pos hs _).ne'
  rw [reflectedGoodLambdaCutoff, reflectedSourceSquaredEnergy, Real.sq_sqrt]
  · dsimp only [reflectedStoppingRadius]
    rw [show cubeRadius (originCube d m) = s / 2 by
      dsimp only [s, cubeRadius]
      ring]
    rw [show 10 * (3 : ℝ) ^ depth = L by rfl, hIu, hIH, hscaled]
    calc
      ((2 * (s / 2 / L)) ^ d)⁻¹ *
          ((3 : ℝ) ^ d *
            ((∫ x in openCubeSet (originCube d m),
              ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) +
              (eps⁻¹) ^ (2 : ℕ) * (sigma0⁻¹) ^ (2 : ℕ) *
                ∫ x in openCubeSet (originCube d m),
                  ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume)) =
          (((2 * (s / 2 / L)) ^ d)⁻¹ * (3 : ℝ) ^ d) *
            ((∫ x in openCubeSet (originCube d m),
              ‖hilbertifyVecField u.toH1Function.grad x‖ ^ (2 : ℕ) ∂volume) +
              (eps⁻¹) ^ (2 : ℕ) * (sigma0⁻¹) ^ (2 : ℕ) *
                ∫ x in openCubeSet (originCube d m),
                  ‖hilbertifyVecField H x‖ ^ (2 : ℕ) ∂volume) := by ring
      _ = _ := by rw [hcoef]; ring
  · apply mul_nonneg
    · exact inv_nonneg.mpr (pow_nonneg
        (mul_nonneg (by norm_num) (reflectedStoppingRadius_pos m depth).le) _)
    · apply mul_nonneg (pow_nonneg (by norm_num) _)
      apply add_nonneg
      · exact MeasureTheory.integral_nonneg fun _ => sq_nonneg _
      · exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (MeasureTheory.integral_nonneg fun _ => sq_nonneg _)

private theorem reflectedGoodLambdaCutoff_le_normalized_datum_energy
    {d : ℕ} [NeZero d] {m : ℤ} {q : FiniteLpExponent}
    (depth : ℕ) {eps sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (u : H10Function (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo) :
    reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField ≤
      Real.sqrt (((3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d) *
        (1 + (eps⁻¹) ^ (2 : ℕ))) *
        Real.sqrt (∫ x, ‖sigma0⁻¹ • hilbertifyVecField h.toField x‖ ^ (2 : ℕ)
          ∂(centeredCubeDomain d m).normalizedVolume) := by
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let f : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField h.toField
  let K : ℝ := (3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d
  let E : ℝ := ∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ
  let A : ℝ := ∫ x, ‖f x‖ ^ (2 : ℕ) ∂μ
  let C : ℝ := Real.sqrt (K * (1 + (eps⁻¹) ^ (2 : ℕ)))
  have hfraw : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [f, hilbertifyVecField] using
      memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2
  have hf : MemLp f 2 μ := by
    rw [show μ = ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
      simpa only [μ] using centeredCube_normalizedVolume_eq_smul_openCubeVolume m]
    exact hfraw.smul_measure ENNReal.ofReal_ne_top
  have hgbase : MemLp (hilbertifyVecField h.toField) 2 μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemL2
  have hg : MemLp g 2 μ := by
    simpa only [g] using hgbase.const_smul sigma0⁻¹
  have hnorm := centeredCubeNormalized_eLpNorm_grad_le_scaledDatum hsigma0 u
    (memVectorL2_openCubeSet_of_euclideanMemLpTwo (originCube d m) h.euclideanMemL2)
    (rawWeak_of_isCenteredCubeH10ScalarDivergenceSolution hsolution)
  have hnormR := (ENNReal.toReal_le_toReal hf.eLpNorm_lt_top.ne
      hg.eLpNorm_lt_top.ne).mpr hnorm
  have hsq := (sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hnormR
  rw [toReal_eLpNorm_two_sq_eq_integral_norm_sq hf,
    toReal_eLpNorm_two_sq_eq_integral_norm_sq hg] at hsq
  have hAE : A ≤ E := by simpa only [A, E, f, g] using hsq
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  have hE0 : 0 ≤ E := MeasureTheory.integral_nonneg fun _ => sq_nonneg _
  have hsum : A + (eps⁻¹) ^ (2 : ℕ) * E ≤
      (1 + (eps⁻¹) ^ (2 : ℕ)) * E := by
    have he : 0 ≤ (eps⁻¹) ^ (2 : ℕ) := sq_nonneg _
    nlinarith [hAE]
  calc
    reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField =
        Real.sqrt (reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField ^ (2 : ℕ)) := by
      symm
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
        (reflectedGoodLambdaCutoff_nonneg m depth eps sigma0 u h.toField)]
    _ = Real.sqrt (K * (A + (eps⁻¹) ^ (2 : ℕ) * E)) := by
      rw [reflectedGoodLambdaCutoff_sq_eq_normalized_energy]
      rfl
    _ ≤ Real.sqrt (K * ((1 + (eps⁻¹) ^ (2 : ℕ)) * E)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsum hK.le)
    _ = C * Real.sqrt E := by
      dsimp only [C]
      rw [← mul_assoc, Real.sqrt_mul]
      positivity
    _ = _ := rfl

/-- Internal finite-`q` specialization of the reflected one-level estimate. -/
private theorem sqWeightedMeasure_reflected_oneLevel_tail_originCube_finiteLp
    {d : ℕ} [NeZero d] {q r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (hr : 2 < r.exponent.toReal) {m : ℤ} {sigma0 eps M level : ℝ}
    (hsigma0 : 0 < sigma0) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hM : 1 ≤ M) (u : H10Function (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo)
    (hlevel : reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField < level) :
    sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad) volume
        ({x | M * level < ‖hilbertifyVecField u.toH1Function.grad x‖} ∩
          openCubeSet (originCube d m)) ≤
      ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad) volume
            ({x | level / 2 < ‖hilbertifyVecField u.toH1Function.grad x‖} ∩
              openCubeSet (originCube d m)) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField h.toField) volume
              ({x | eps * level / 2 <
                ‖(sigma0⁻¹ • hilbertifyVecField h.toField) x‖} ∩
                openCubeSet (originCube d m))) := by
  exact sqWeightedMeasure_reflected_oneLevel_tail_originCube G hr hsigma0 heps
    heps_one hM u h.toField
    (memVectorL2_openCubeSet_of_euclideanMemLpTwo (originCube d m)
      h.euclideanMemL2)
    (rawWeak_of_isCenteredCubeH10ScalarDivergenceSolution hsolution) hlevel

private theorem finiteLp_oneLevel_tail_restrict
    {d : ℕ} [NeZero d] {q r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (hr : 2 < r.exponent.toReal) {m : ℤ} {sigma0 eps M lambda : ℝ}
    (hsigma0 : 0 < sigma0) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hM : 1 ≤ M) (u : H10Function (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo)
    (hlambda : reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField < lambda) :
    ∀ level, lambda ≤ level →
      sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
          (volume.restrict (openCubeSet (originCube d m)))
          {x | M * level < ‖hilbertifyVecField u.toH1Function.grad x‖} ≤
        (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
            (volume.restrict (openCubeSet (originCube d m)))
            {x | level / 2 < ‖hilbertifyVecField u.toH1Function.grad x‖} +
        ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))) *
          sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField h.toField)
            (volume.restrict (openCubeSet (originCube d m)))
            {x | eps * level / 2 <
              ‖(sigma0⁻¹ • hilbertifyVecField h.toField) x‖} := by
  intro level hlevel
  have htail := sqWeightedMeasure_reflected_oneLevel_tail_originCube_finiteLp
    G hr hsigma0 heps heps_one hM u h hsolution (hlambda.trans_le hlevel)
  rw [sqWeightedMeasure_restrict_apply_eq_inter
      (measurableSet_openCubeSet (originCube d m)),
    sqWeightedMeasure_restrict_apply_eq_inter
      (measurableSet_openCubeSet (originCube d m)),
    sqWeightedMeasure_restrict_apply_eq_inter
      (measurableSet_openCubeSet (originCube d m))]
  simpa only [mul_add, mul_assoc] using htail

private theorem finiteLp_oneLevel_tail_normalized
    {d : ℕ} [NeZero d] {q r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (hr : 2 < r.exponent.toReal) {m : ℤ} {sigma0 eps M lambda : ℝ}
    (hsigma0 : 0 < sigma0) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hM : 1 ≤ M) (u : H10Function (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo)
    (hlambda : reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField < lambda) :
    ∀ level, lambda ≤ level →
      sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
          (centeredCubeDomain d m).normalizedVolume
          {x | M * level < ‖hilbertifyVecField u.toH1Function.grad x‖} ≤
        (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
            (centeredCubeDomain d m).normalizedVolume
            {x | level / 2 < ‖hilbertifyVecField u.toH1Function.grad x‖} +
        ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))) *
          sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField h.toField)
            (centeredCubeDomain d m).normalizedVolume
            {x | eps * level / 2 <
              ‖(sigma0⁻¹ • hilbertifyVecField h.toField) x‖} := by
  intro level hlevel
  let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹)
  have hraw := finiteLp_oneLevel_tail_restrict G hr hsigma0 heps heps_one hM
    u h hsolution hlambda level hlevel
  rw [centeredCube_normalizedVolume_eq_smul_openCubeVolume,
    sqWeightedMeasure_smul_measure, sqWeightedMeasure_smul_measure,
    sqWeightedMeasure_smul_measure]
  calc
    c * sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
        (volume.restrict (openCubeSet (originCube d m)))
        {x | M * level < ‖hilbertifyVecField u.toH1Function.grad x‖} ≤
      c *
        ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
            (volume.restrict (openCubeSet (originCube d m)))
            {x | level / 2 < ‖hilbertifyVecField u.toH1Function.grad x‖} +
          ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
            (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
              ENNReal.ofReal (eps ^ (2 : ℕ)))) *
            ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))) *
            sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField h.toField)
              (volume.restrict (openCubeSet (originCube d m)))
              {x | eps * level / 2 <
                ‖(sigma0⁻¹ • hilbertifyVecField h.toField) x‖}) :=
        by simpa only [mul_comm] using mul_le_mul_right hraw c
    _ = _ := by ring

/-- The layer-cake integration step, with its contraction hypothesis kept
private because the outer finite-`L^p` argument chooses the parameters. -/
private theorem finiteLp_integrated_tail_of_parameters
    {d : ℕ} [NeZero d] {q r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (hr : 2 < r.exponent.toReal) (hq : 2 < q.exponent.toReal)
    {m : ℤ} {sigma0 M eps lambda0 : ℝ}
    (hsigma0 : 0 < sigma0) (hM : 1 < M) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hlambda0 : 0 < lambda0)
    (u : H10Function (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo)
    (hcutoff : reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField < lambda0)
    (hsmall :
      (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ)))) *
        ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2)) < 1) :
    ∫⁻ x, ENNReal.ofReal
        (‖hilbertifyVecField u.toH1Function.grad x‖ ^ q.exponent.toReal /
          M ^ (q.exponent.toReal - 2))
        ∂(centeredCubeDomain d m).normalizedVolume ≤
      (sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
          (centeredCubeDomain d m).normalizedVolume Set.univ *
          ENNReal.ofReal (lambda0 ^ (q.exponent.toReal - 2)) +
        ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))) *
          ∫⁻ x, ENNReal.ofReal
            (‖(sigma0⁻¹ • hilbertifyVecField h.toField) x‖ ^ q.exponent.toReal /
              (eps / 2) ^ (q.exponent.toReal - 2))
            ∂(centeredCubeDomain d m).normalizedVolume) /
        (1 -
          (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
            (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
              ENNReal.ofReal (eps ^ (2 : ℕ)))) *
            ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2))) := by
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let f : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField h.toField
  let C : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G
  let theta : ℝ≥0∞ := C *
    (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
      ENNReal.ofReal (eps ^ (2 : ℕ)))
  let B : ℝ≥0∞ := theta * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))
  have hfraw : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [f, hilbertifyVecField] using
      memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2
  have hf : MemLp f 2 μ := by
    rw [show μ = ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        volume.restrict (openCubeSet (originCube d m)) by
      simpa only [μ] using centeredCube_normalizedVolume_eq_smul_openCubeVolume m]
    exact hfraw.smul_measure ENNReal.ofReal_ne_top
  have hg_base : MemLp (hilbertifyVecField h.toField) q.exponent μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hg : MemLp g q.exponent μ := by
    simpa only [g] using hg_base.const_smul sigma0⁻¹
  have hC : C ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
      (oneStoppingBallCoefficient_ne_top G)
  have htheta : theta ≠ ∞ := by
    exact ENNReal.mul_ne_top hC (ENNReal.add_ne_top.mpr
      ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  have hB : B ≠ ∞ :=
    ENNReal.mul_ne_top htheta ENNReal.ofReal_ne_top
  have heps_half : 0 < eps / 2 := by linarith
  have htail : ∀ level, lambda0 ≤ level →
      sqWeightedMeasure f μ {x | M * level < ‖f x‖} ≤
        theta * sqWeightedMeasure f μ {x | level / 2 < ‖f x‖} +
          B * sqWeightedMeasure g μ
            {x | eps * level / 2 < ‖g x‖} := by
    simpa only [μ, f, g, theta, B, C, mul_assoc] using
      finiteLp_oneLevel_tail_normalized G hr hsigma0 heps heps_one hM.le u h
        hsolution hcutoff
  simpa only [μ, f, g, theta, B, C] using
    (lp_le_of_oneLevel_weighted_tail hf.aestronglyMeasurable hg.aestronglyMeasurable
      hq (by linarith) (by linarith) heps hlambda0
      (sqWeightedMeasure_univ_ne_top_of_memLp_two hf) hB
      (lintegral_ofReal_norm_rpow_div_ne_top_of_memLp heps_half hg)
      hsmall htail)

private theorem exists_finiteLp_goodLambda_data
    {d : ℕ} [NeZero d] (q : FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) :
    ∃ (depth : ℕ) (G : INTERNAL.HarmonicEuclideanGradientGain d
        (finiteLpExponentSucc q) depth) (M eps : ℝ),
      1 < M ∧ 0 < eps ∧ eps ≤ 1 ∧
        (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^
            (2 - (finiteLpExponentSucc q).exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2)) < 1 := by
  obtain ⟨⟨depth, G⟩⟩ :=
    INTERNAL.nonempty_harmonicEuclideanGradientGain_finiteTarget_of_pos d
      (Nat.pos_of_ne_zero (NeZero.ne d)) (finiteLpExponentSucc q)
  let C : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G
  have hC : C ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (by norm_num)) (oneStoppingBallCoefficient_ne_top G)
  obtain ⟨M, eps, hM, heps, heps_one, hsmall⟩ :=
    INTERNAL.exists_strict_goodLambda_parameters hC hq
      (finiteLpExponent_lt_succ q)
  exact ⟨depth, G, M, eps, hM, heps, heps_one, hsmall⟩

private theorem ennreal_le_root_mul_of_rpow_le {p : ℝ} {R X Y : ℝ≥0∞}
    (hp : 0 < p) (h : X ^ p ≤ R * Y ^ p) :
    X ≤ R ^ p⁻¹ * Y := by
  have hp0 : p ≠ 0 := hp.ne'
  have hpnonneg : 0 ≤ p := hp.le
  calc
    X = X ^ (p * p⁻¹) := by rw [mul_inv_cancel₀ hp0, ENNReal.rpow_one]
    _ = (X ^ p) ^ p⁻¹ := ENNReal.rpow_mul _ _ _
    _ ≤ (R * Y ^ p) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow h (inv_nonneg.mpr hpnonneg)
    _ = R ^ p⁻¹ * Y := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hpnonneg),
        ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0, ENNReal.rpow_one]

private theorem eLpNorm_rpow_finiteLpExponent_eq_lintegral_ofReal_norm_rpow
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} (p : FiniteLpExponent) (f : α → E) :
    (eLpNorm f p.exponent μ) ^ p.exponent.toReal =
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) ∂μ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne,
    ← ENNReal.rpow_mul]
  have hp : p.exponent.toReal ≠ 0 :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans p.one_lt)) p.lt_top.ne |>.ne'
  rw [one_div, inv_mul_cancel₀ hp, ENNReal.rpow_one]
  apply MeasureTheory.lintegral_congr
  intro x
  rw [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]

private theorem lintegral_ofReal_norm_rpow_eq_ofReal_mul_div
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} {p : FiniteLpExponent} {a : ℝ} {f : α → E}
    (ha : 0 < a) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) ∂μ) =
      ENNReal.ofReal (a ^ (p.exponent.toReal - 2)) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal /
          a ^ (p.exponent.toReal - 2)) ∂μ := by
  let b : ℝ := a ^ (p.exponent.toReal - 2)
  have hb : 0 < b := Real.rpow_pos_of_pos ha _
  have hpoint (x : α) :
      ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) =
        ENNReal.ofReal b * ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal / b) := by
    calc
      ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) =
          ENNReal.ofReal ((‖f x‖ ^ p.exponent.toReal / b) * b) := by
        congr 1
        exact (div_mul_cancel₀ _ hb.ne').symm
      _ = ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal / b) * ENNReal.ofReal b :=
        ENNReal.ofReal_mul (div_nonneg
          (Real.rpow_nonneg (norm_nonneg _) _) hb.le)
      _ = _ := mul_comm _ _
  simp_rw [show a ^ (p.exponent.toReal - 2) = b by rfl, hpoint]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem divided_moment_eq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : MeasureTheory.Measure α} {p : FiniteLpExponent} {a : ℝ} {f : α → E}
    (ha : 0 < a) (hf : MemLp f p.exponent μ) :
    ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal /
      a ^ (p.exponent.toReal - 2)) ∂μ =
      (ENNReal.ofReal (a ^ (p.exponent.toReal - 2)))⁻¹ *
        (eLpNorm f p.exponent μ) ^ p.exponent.toReal := by
  let b : ℝ := a ^ (p.exponent.toReal - 2)
  have hb : 0 < b := Real.rpow_pos_of_pos ha _
  have hpoint (x : α) :
      ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal / b) =
        (ENNReal.ofReal b)⁻¹ * ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal) := by
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul
      (inv_nonneg.mpr hb.le), ENNReal.ofReal_inv_of_pos hb]
  have hmeas : AEMeasurable
      (fun x => ENNReal.ofReal (‖f x‖ ^ p.exponent.toReal)) μ :=
    (hf.aestronglyMeasurable.norm.aemeasurable.pow aemeasurable_const).ennreal_ofReal
  simp_rw [show a ^ (p.exponent.toReal - 2) = b by rfl, hpoint]
  rw [MeasureTheory.lintegral_const_mul'' _ hmeas,
    ← eLpNorm_rpow_finiteLpExponent_eq_lintegral_ofReal_norm_rpow p f]

private theorem tail_powered_package
    {cM D L B cdata X Y : ℝ≥0∞} (hcM : cM ≠ 0) (hcMtop : cM ≠ ∞)
    (htail : cM⁻¹ * X ≤ (L * Y + B * (cdata⁻¹ * Y)) / D) :
    X ≤ (cM * D⁻¹ * (L + B * cdata⁻¹)) * Y := by
  calc
    X = cM * (cM⁻¹ * X) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel hcM hcMtop, one_mul]
    _ = (cM⁻¹ * X) * cM := mul_comm _ _
    _ ≤ ((L * Y + B * (cdata⁻¹ * Y)) / D) * cM :=
      mul_le_mul_left htail _
    _ = cM * ((L * Y + B * (cdata⁻¹ * Y)) / D) := mul_comm _ _
    _ = (cM * D⁻¹ * (L + B * cdata⁻¹)) * Y := by
      rw [ENNReal.div_eq_inv_mul]
      ring

private theorem tail_norm_package
    {p : ℝ} {cM D L B cdata X Y : ℝ≥0∞} (hp : 0 < p) (hcM : cM ≠ 0)
    (hcMtop : cM ≠ ∞)
    (htail : cM⁻¹ * X ^ p ≤ (L * Y ^ p + B * (cdata⁻¹ * Y ^ p)) / D) :
    X ≤ (cM * D⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ * Y := by
  have hpow : X ^ p ≤ (cM * D⁻¹ * (L + B * cdata⁻¹)) * Y ^ p :=
    tail_powered_package hcM hcMtop htail
  have hp0 : p ≠ 0 := hp.ne'
  have hpnonneg : 0 ≤ p := hp.le
  calc
    X = X ^ (p * p⁻¹) := by rw [mul_inv_cancel₀ hp0, ENNReal.rpow_one]
    _ = (X ^ p) ^ p⁻¹ := ENNReal.rpow_mul _ _ _
    _ ≤ ((cM * D⁻¹ * (L + B * cdata⁻¹)) * Y ^ p) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow hpow (inv_nonneg.mpr hpnonneg)
    _ = (cM * D⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ * Y := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hpnonneg),
        ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0, ENNReal.rpow_one]

/-- Algebraic finalization of the integrated good-`λ` inequality.  The
solution moment is deliberately supplied through the raw moment identity, so
this lemma does not assume the conclusion `MemLp f q` while proving it. -/
private theorem finiteLp_norm_bound_of_moment_tail
    {p : ℝ} {cM D L B cdata X Y Jf Jg low : ℝ≥0∞}
    (hp : 0 < p) (hcM : cM ≠ 0) (hcMtop : cM ≠ ∞)
    (hJf : X ^ p = cM * Jf)
    (hJg : Jg = cdata⁻¹ * Y ^ p)
    (htail : Jf ≤ (low + B * Jg) / D)
    (hlow : low ≤ L * Y ^ p) :
    X ≤ (cM * D⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ * Y := by
  apply tail_norm_package hp hcM hcMtop
  rw [hJf, ← mul_assoc, ENNReal.inv_mul_cancel hcM hcMtop, one_mul]
  calc
    Jf ≤ (low + B * Jg) / D := htail
    _ ≤ (L * Y ^ p + B * (cdata⁻¹ * Y ^ p)) / D := by
      apply ENNReal.div_le_div_right
      calc
        low + B * Jg ≤ L * Y ^ p + B * Jg := by
          simpa [add_comm] using add_le_add_right hlow (B * Jg)
        _ = _ := by rw [hJg]

private theorem finiteLp_low_term_package
    {p : ℝ} {S lam c N₂ Nq : ℝ≥0∞}
    (hp : 2 < p) (hS : S ≤ N₂ ^ (2 : ℕ))
    (hlam : lam ≤ c * N₂) (hN : N₂ ≤ Nq) :
    S * lam ^ (p - 2) ≤ c ^ (p - 2) * Nq ^ p := by
  have he : 0 ≤ p - 2 := by linarith
  calc
    S * lam ^ (p - 2) ≤ N₂ ^ (2 : ℕ) * (c * N₂) ^ (p - 2) :=
      mul_le_mul hS (ENNReal.rpow_le_rpow hlam he) bot_le bot_le
    _ = c ^ (p - 2) * N₂ ^ p := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ he]
      rw [← ENNReal.rpow_natCast]
      calc
        N₂ ^ (2 : ℝ) * (c ^ (p - 2) * N₂ ^ (p - 2)) =
            c ^ (p - 2) * (N₂ ^ (2 : ℝ) * N₂ ^ (p - 2)) := by
              ac_rfl
        _ = c ^ (p - 2) * N₂ ^ (2 + (p - 2)) := by
              rw [ENNReal.rpow_add_of_nonneg _ _ (by norm_num) he]
        _ = c ^ (p - 2) * N₂ ^ p := by
              congr 2
              ring
    _ ≤ c ^ (p - 2) * Nq ^ p := by
      gcongr

private theorem finiteLp_low_term_of_l2_control
    {d : ℕ} {m : ℤ} {q : FiniteLpExponent}
    {f g : Vec d → HilbertVec d} {lambda c : ℝ}
    (hgq : MemLp g q.exponent (centeredCubeDomain d m).normalizedVolume)
    (hq : 2 < q.exponent.toReal)
    (henergy : eLpNorm f 2 (centeredCubeDomain d m).normalizedVolume ≤
      eLpNorm g 2 (centeredCubeDomain d m).normalizedVolume)
    (hc : 0 ≤ c) (hlambda : 0 ≤ lambda)
    (hlambda_bound : lambda ≤ c *
      (eLpNorm g q.exponent (centeredCubeDomain d m).normalizedVolume).toReal) :
    sqWeightedMeasure f (centeredCubeDomain d m).normalizedVolume Set.univ *
        ENNReal.ofReal (lambda ^ (q.exponent.toReal - 2)) ≤
      (ENNReal.ofReal c) ^ (q.exponent.toReal - 2) *
        (eLpNorm g q.exponent (centeredCubeDomain d m).normalizedVolume) ^
          q.exponent.toReal := by
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  have hprob : IsProbabilityMeasure μ := ⟨by
    dsimp only [μ]
    exact (centeredCubeDomain d m).normalizedVolume_apply_univ⟩
  let : IsProbabilityMeasure μ := hprob
  have htwoq : (2 : ℝ≥0∞) ≤ q.exponent := by
    apply le_of_lt
    apply (ENNReal.toReal_lt_toReal (a := (2 : ℝ≥0∞)) (b := q.exponent)
      (by norm_num) q.lt_top.ne).mp
    simpa using hq
  have htwoqnorm : eLpNorm g 2 μ ≤ eLpNorm g q.exponent μ :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le htwoq hgq.aestronglyMeasurable
  have hS : sqWeightedMeasure f μ Set.univ ≤ (eLpNorm g 2 μ) ^ (2 : ℕ) := by
    rw [sqWeightedMeasure_univ_eq_eLpNorm_two_sq]
    exact pow_le_pow_left₀ bot_le henergy 2
  have hSq : sqWeightedMeasure f μ Set.univ ≤ (eLpNorm g q.exponent μ) ^ (2 : ℕ) :=
    hS.trans (pow_le_pow_left₀ bot_le htwoqnorm 2)
  have hlamENN : ENNReal.ofReal lambda ≤ ENNReal.ofReal c * eLpNorm g q.exponent μ := by
    calc
      ENNReal.ofReal lambda ≤ ENNReal.ofReal
          (c * (eLpNorm g q.exponent μ).toReal) := ENNReal.ofReal_le_ofReal hlambda_bound
      _ = ENNReal.ofReal c * eLpNorm g q.exponent μ := by
        rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_toReal hgq.eLpNorm_lt_top.ne]
  rw [show (ENNReal.ofReal (lambda ^ (q.exponent.toReal - 2))) =
      (ENNReal.ofReal lambda) ^ (q.exponent.toReal - 2) by
    exact (ENNReal.ofReal_rpow_of_nonneg (p := q.exponent.toReal - 2)
      hlambda (by linarith)).symm]
  exact finiteLp_low_term_package hq hSq hlamENN le_rfl

private theorem reflectedGoodLambdaCutoff_le_q_datum_norm
    {d : ℕ} [NeZero d] {m : ℤ} {q : FiniteLpExponent} (depth : ℕ)
    {eps sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (u : H10Function (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo)
    (hq : 2 < q.exponent.toReal) :
    reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField ≤
      Real.sqrt (((3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d) *
        (1 + (eps⁻¹) ^ (2 : ℕ))) *
      (eLpNorm (sigma0⁻¹ • hilbertifyVecField h.toField) q.exponent
        (centeredCubeDomain d m).normalizedVolume).toReal := by
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField h.toField
  let C : ℝ := Real.sqrt (((3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d) *
    (1 + (eps⁻¹) ^ (2 : ℕ)))
  have hgbase : MemLp (hilbertifyVecField h.toField) 2 μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemL2
  have hg2 : MemLp g 2 μ := by simpa only [g] using hgbase.const_smul sigma0⁻¹
  have hgqbase : MemLp (hilbertifyVecField h.toField) q.exponent μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hgq : MemLp g q.exponent μ := by simpa only [g] using hgqbase.const_smul sigma0⁻¹
  let : IsProbabilityMeasure μ := ⟨by
    dsimp only [μ]
    exact (centeredCubeDomain d m).normalizedVolume_apply_univ⟩
  have htwoq : (2 : ℝ≥0∞) ≤ q.exponent := by
    apply le_of_lt
    apply (ENNReal.toReal_lt_toReal (a := (2 : ℝ≥0∞)) (b := q.exponent)
      (by norm_num) q.lt_top.ne).mp
    simpa using hq
  have hnorm : eLpNorm g 2 μ ≤ eLpNorm g q.exponent μ :=
    MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le htwoq hgq.aestronglyMeasurable
  have hnormR : (eLpNorm g 2 μ).toReal ≤ (eLpNorm g q.exponent μ).toReal :=
    (ENNReal.toReal_le_toReal hg2.eLpNorm_lt_top.ne hgq.eLpNorm_lt_top.ne).mpr hnorm
  have hmoment : (eLpNorm g 2 μ).toReal ^ (2 : ℕ) =
      ∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ :=
    toReal_eLpNorm_two_sq_eq_integral_norm_sq hg2
  have hsqrt : Real.sqrt (∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ) =
      (eLpNorm g 2 μ).toReal := by
    rw [← hmoment, Real.sqrt_sq_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hcut := reflectedGoodLambdaCutoff_le_normalized_datum_energy
    (eps := eps) depth hsigma0 u h hsolution
  calc
    reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField ≤
        C * Real.sqrt (∫ x, ‖g x‖ ^ (2 : ℕ) ∂μ) := by
          simpa only [μ, g, C] using! hcut
    _ = C * (eLpNorm g 2 μ).toReal := by rw [hsqrt]
    _ ≤ C * (eLpNorm g q.exponent μ).toReal := by
      apply mul_le_mul_of_nonneg_left hnormR
      dsimp only [C]
      positivity

/-- The finite-exponent conclusion from an integrated reflected tail estimate.
The only analytic input not intrinsic to layer-cake is the low-level term;
the outer argument bounds it using the energy estimate and its cutoff choice. -/
private theorem finiteLp_norm_bound_of_parameters
    {d : ℕ} [NeZero d] {q r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (hr : 2 < r.exponent.toReal) (hq : 2 < q.exponent.toReal)
    {m : ℤ} {sigma0 M eps lambda0 : ℝ}
    (hsigma0 : 0 < sigma0) (hM : 1 < M) (heps : 0 < eps) (heps_one : eps ≤ 1)
    (hlambda0 : 0 < lambda0)
    (u : H10Function (openCubeSet (originCube d m)))
    (h : CubeEuclideanL2LpField (originCube d m) q)
    (hsolution : IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo)
    (hcutoff : reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField < lambda0)
    (hsmall :
      (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ)))) *
        ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2)) < 1)
    {L : ℝ≥0∞}
    (hlow :
      sqWeightedMeasure (hilbertifyVecField u.toH1Function.grad)
          (centeredCubeDomain d m).normalizedVolume Set.univ *
          ENNReal.ofReal (lambda0 ^ (q.exponent.toReal - 2)) ≤
        L * (eLpNorm (sigma0⁻¹ • hilbertifyVecField h.toField) q.exponent
          (centeredCubeDomain d m).normalizedVolume) ^ q.exponent.toReal) :
    eLpNorm (hilbertifyVecField u.toH1Function.grad) q.exponent
        (centeredCubeDomain d m).normalizedVolume ≤
      (ENNReal.ofReal (M ^ (q.exponent.toReal - 2)) *
        (1 -
          (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
            (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
              ENNReal.ofReal (eps ^ (2 : ℕ)))) *
            ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2)))⁻¹ *
        (L +
          ((((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
            (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
              ENNReal.ofReal (eps ^ (2 : ℕ)))) *
            ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))) *
            (ENNReal.ofReal ((eps / 2) ^ (q.exponent.toReal - 2)))⁻¹)) ^
          (q.exponent.toReal)⁻¹ *
        eLpNorm (sigma0⁻¹ • hilbertifyVecField h.toField) q.exponent
          (centeredCubeDomain d m).normalizedVolume := by
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let f : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField h.toField
  let theta : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
    (ENNReal.ofReal ((M / 2) ^ (2 - r.exponent.toReal)) +
      ENNReal.ofReal (eps ^ (2 : ℕ)))
  let B : ℝ≥0∞ := theta * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))
  let cM : ℝ≥0∞ := ENNReal.ofReal (M ^ (q.exponent.toReal - 2))
  let cdata : ℝ≥0∞ := ENNReal.ofReal ((eps / 2) ^ (q.exponent.toReal - 2))
  let D : ℝ≥0∞ := 1 - theta * ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2))
  have hepshalf : 0 < eps / 2 := by linarith
  have hcM : cM ≠ 0 := by
    dsimp only [cM]
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hcMtop : cM ≠ ∞ := ENNReal.ofReal_ne_top
  have htail := finiteLp_integrated_tail_of_parameters G hr hq hsigma0 hM
    heps heps_one hlambda0 u h hsolution hcutoff hsmall
  have hJf : (eLpNorm f q.exponent μ) ^ q.exponent.toReal =
      cM * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal /
        M ^ (q.exponent.toReal - 2)) ∂μ := by
    rw [eLpNorm_rpow_finiteLpExponent_eq_lintegral_ofReal_norm_rpow,
      lintegral_ofReal_norm_rpow_eq_ofReal_mul_div (p := q) (a := M)
        (f := f) (by linarith)]
  have hgbase : MemLp (hilbertifyVecField h.toField) q.exponent μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hg : MemLp g q.exponent μ := by
    simpa only [g] using hgbase.const_smul sigma0⁻¹
  have hJg : (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q.exponent.toReal /
      (eps / 2) ^ (q.exponent.toReal - 2)) ∂μ) =
      cdata⁻¹ * (eLpNorm g q.exponent μ) ^ q.exponent.toReal := by
    simpa only [cdata] using divided_moment_eq hepshalf hg
  have htail' :
      (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal /
        M ^ (q.exponent.toReal - 2)) ∂μ) ≤
        (sqWeightedMeasure f μ Set.univ *
            ENNReal.ofReal (lambda0 ^ (q.exponent.toReal - 2)) +
          B * ∫⁻ x, ENNReal.ofReal (‖g x‖ ^ q.exponent.toReal /
            (eps / 2) ^ (q.exponent.toReal - 2)) ∂μ) / D := by
    simpa only [μ, f, g, theta, B, D] using htail
  have hlow' : sqWeightedMeasure f μ Set.univ *
      ENNReal.ofReal (lambda0 ^ (q.exponent.toReal - 2)) ≤
        L * (eLpNorm g q.exponent μ) ^ q.exponent.toReal := by
    simpa only [μ, f, g] using hlow
  have hp : 0 < q.exponent.toReal := by linarith
  simpa only [μ, f, g, theta, B, cM, cdata, D] using
    (finiteLp_norm_bound_of_moment_tail
      (p := q.exponent.toReal) (L := L) (B := B) hp
      hcM hcMtop hJf hJg htail' hlow')

private theorem finiteLp_final_coefficient_ne_top
    {p : ℝ} {cM rho L B cdata : ℝ≥0∞}
    (hp : 0 < p) (hcMtop : cM ≠ ∞) (hrho : rho < 1)
    (hLtop : L ≠ ∞) (hBtop : B ≠ ∞) (hcdata : cdata ≠ 0) :
    (cM * (1 - rho)⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ ≠ ∞ := by
  apply ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le)
  apply ENNReal.mul_ne_top
  · apply ENNReal.mul_ne_top hcMtop
    exact ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hrho))
  · apply ENNReal.add_ne_top.mpr
    exact ⟨hLtop, ENNReal.mul_ne_top hBtop (ENNReal.inv_ne_top.mpr hcdata)⟩

/-- Cube Calderón--Zygmund estimate above the energy exponent. -/
theorem centeredCubeH10ScalarDivergence_cz_of_two_lt
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (sigma0 : ℝ)
      (h : CubeEuclideanL2LpField (originCube d m) q)
      (u : H10Function (openCubeSet (originCube d m))), 0 < sigma0 →
      IsCenteredCubeH10ScalarDivergenceSolution m sigma0 u h.toLpTwo →
      (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad ≤ C * (ENNReal.ofReal sigma0)⁻¹ *
          (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
            h.toField := by
  obtain ⟨depth, G, M, eps, hM, heps, heps_one, hsmall⟩ :=
    exists_finiteLp_goodLambda_data (d := d) q hq
  let theta : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
    (ENNReal.ofReal ((M / 2) ^ (2 - (finiteLpExponentSucc q).exponent.toReal)) +
      ENNReal.ofReal (eps ^ (2 : ℕ)))
  let B : ℝ≥0∞ := theta * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))
  let cM : ℝ≥0∞ := ENNReal.ofReal (M ^ (q.exponent.toReal - 2))
  let cdata : ℝ≥0∞ := ENNReal.ofReal ((eps / 2) ^ (q.exponent.toReal - 2))
  let rho : ℝ≥0∞ := theta * ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2))
  let Ccut : ℝ := Real.sqrt (((3 : ℝ) ^ d * (10 * (3 : ℝ) ^ depth) ^ d) *
    (1 + (eps⁻¹) ^ (2 : ℕ)))
  let L : ℝ≥0∞ := (ENNReal.ofReal (2 * Ccut)) ^ (q.exponent.toReal - 2)
  let C : ℝ≥0∞ :=
    (cM * (1 - rho)⁻¹ * (L + B * cdata⁻¹)) ^ (q.exponent.toReal)⁻¹
  have hp : 0 < q.exponent.toReal := by linarith
  have hCtop : C ≠ ∞ := by
    apply finiteLp_final_coefficient_ne_top hp ENNReal.ofReal_ne_top
    · simpa only [rho, theta] using hsmall
    · dsimp only [L]
      exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
    · dsimp only [B, theta]
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
            (oneStoppingBallCoefficient_ne_top G))
          (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩))
        ENNReal.ofReal_ne_top
    · dsimp only [cdata]
      exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  refine ⟨C, lt_top_iff_ne_top.mpr hCtop, ?_⟩
  intro m sigma0 h u hsigma0 hsolution
  let μ : Measure (Vec d) := (centeredCubeDomain d m).normalizedVolume
  let f : Vec d → HilbertVec d := hilbertifyVecField u.toH1Function.grad
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField h.toField
  have henergy : eLpNorm f 2 μ ≤ eLpNorm g 2 μ := by
    simpa only [μ, f, g] using
      (centeredCubeNormalized_eLpNorm_grad_le_scaledDatum hsigma0 u
        (memVectorL2_openCubeSet_of_euclideanMemLpTwo (originCube d m)
          h.euclideanMemL2)
        (rawWeak_of_isCenteredCubeH10ScalarDivergenceSolution hsolution))
  have hgbase : MemLp (hilbertifyVecField h.toField) q.exponent μ := by
    simpa only [μ, centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      hilbertifyVecField] using! h.euclideanMemLp
  have hg : MemLp g q.exponent μ := by simpa only [g] using hgbase.const_smul sigma0⁻¹
  by_cases hYzero : eLpNorm g q.exponent μ = 0
  · let : IsProbabilityMeasure μ := ⟨by
      dsimp only [μ]
      exact (centeredCubeDomain d m).normalizedVolume_apply_univ⟩
    have htwoq : (2 : ℝ≥0∞) ≤ q.exponent := by
      apply le_of_lt
      apply (ENNReal.toReal_lt_toReal (a := (2 : ℝ≥0∞)) (b := q.exponent)
        (by norm_num) q.lt_top.ne).mp
      simpa using hq
    have hg2zero : eLpNorm g 2 μ = 0 :=
      le_zero_iff.mp ((MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
        htwoq hg.aestronglyMeasurable).trans_eq hYzero)
    have hf2zero : eLpNorm f 2 μ = 0 := le_zero_iff.mp (henergy.trans_eq hg2zero)
    have hfraw : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))) := by
      simpa only [f, hilbertifyVecField] using
        memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2
    have hf2 : MemLp f 2 μ := by
      rw [show μ = ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
          volume.restrict (openCubeSet (originCube d m)) by
        simpa only [μ] using centeredCube_normalizedVolume_eq_smul_openCubeVolume m]
      exact hfraw.smul_measure ENNReal.ofReal_ne_top
    have hfae : f =ᵐ[μ] 0 :=
      (MeasureTheory.eLpNorm_eq_zero_iff hf2.aestronglyMeasurable (by norm_num)).mp hf2zero
    have hfqzero : eLpNorm f q.exponent μ = 0 :=
      MeasureTheory.eLpNorm_eq_zero_of_ae_zero hfae
    have htargetzero : (centeredCubeDomain d m).normalizedEuclideanLpENorm
        q.exponent u.toH1Function.grad = 0 := by
      simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        MeasureTheory.eLpNorm_norm, f, μ, hilbertifyVecField] using! hfqzero
    rw [htargetzero]
    exact bot_le
  · let lambda0 : ℝ := reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField +
      Ccut * (eLpNorm g q.exponent μ).toReal
    have hYpos : 0 < (eLpNorm g q.exponent μ).toReal :=
      ENNReal.toReal_pos hYzero hg.eLpNorm_lt_top.ne
    have hCcut : 0 < Ccut := by
      dsimp only [Ccut]
      positivity
    have hcut := reflectedGoodLambdaCutoff_le_q_datum_norm (eps := eps)
      depth hsigma0 u h hsolution hq
    have hcut' : reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField ≤
        Ccut * (eLpNorm g q.exponent μ).toReal := by
      simpa only [μ, g, Ccut] using hcut
    have hlambda0 : 0 < lambda0 := by
      dsimp only [lambda0]
      exact add_pos_of_nonneg_of_pos
        (reflectedGoodLambdaCutoff_nonneg m depth eps sigma0 u h.toField)
        (mul_pos hCcut hYpos)
    have hcutoff : reflectedGoodLambdaCutoff m depth eps sigma0 u h.toField < lambda0 := by
      dsimp only [lambda0]
      nlinarith [hcut']
    have hlambdaBound : lambda0 ≤ 2 * Ccut * (eLpNorm g q.exponent μ).toReal := by
      dsimp only [lambda0]
      nlinarith [hcut']
    have hlow := finiteLp_low_term_of_l2_control (q := q) (f := f) (g := g)
      hg hq henergy (by nlinarith [hCcut]) hlambda0.le hlambdaBound
    have hbound := finiteLp_norm_bound_of_parameters G
      (hq.trans (finiteLpExponent_lt_succ q)) hq hsigma0 hM heps heps_one
      hlambda0 u h hsolution hcutoff (by
        simpa only [finiteLpExponentSucc_toReal] using hsmall) (L := L) (by
          simpa only [μ, f, g, lambda0, L, Ccut] using hlow)
    have hleft : (centeredCubeDomain d m).normalizedEuclideanLpENorm q.exponent
        u.toH1Function.grad = eLpNorm f q.exponent μ := by
      simp only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
        BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
        MeasureTheory.eLpNorm_norm, f, μ]
      rfl
    rw [hleft]
    rw [MeasureTheory.eLpNorm_const_smul] at hbound
    rw [← ofReal_norm,
      Real.norm_of_nonneg (inv_nonneg.mpr hsigma0.le),
      ENNReal.ofReal_inv_of_pos hsigma0] at hbound
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
      MeasureTheory.eLpNorm_norm, μ, f, g, C, theta, B, cM, cdata, rho, L,
      mul_assoc] using! hbound

end CubeCalderonZygmund

end

end Homogenization
