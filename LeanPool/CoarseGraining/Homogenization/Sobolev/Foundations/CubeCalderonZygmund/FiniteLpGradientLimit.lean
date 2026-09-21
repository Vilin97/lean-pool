/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpSolutionSequence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Internal gradient limits for finite-`L^p` cube data

This module only completes the canonical finite-data gradients.  In
particular, it deliberately contains neither a limiting scalar solution nor a
zero-trace assertion.
-/

namespace Homogenization

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

namespace INTERNAL

private theorem centeredCube_rawVolume_le_smul_normalizedVolume
    {d : ℕ} (m : ℤ) :
    volume.restrict (openCubeSet (originCube d m)) ≤
      ENNReal.ofReal (cubeVolume (originCube d m)) •
        (centeredCubeDomain d m).normalizedVolume := by
  rw [show (centeredCubeDomain d m).normalizedVolume =
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) •
        cubeMeasure (originCube d m) by
    simp only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      normalizedCubeMeasure]]
  have hvol_nonneg : 0 ≤ cubeVolume (originCube d m) :=
    cubeVolume_nonneg _
  have hmul : ENNReal.ofReal (cubeVolume (originCube d m)) *
      ENNReal.ofReal ((cubeVolume (originCube d m))⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul hvol_nonneg]
    have hreal : cubeVolume (originCube d m) *
        (cubeVolume (originCube d m))⁻¹ = 1 := by
      field_simp [(cubeVolume_pos _).ne']
    rw [hreal]
    norm_num
  rw [smul_smul, hmul, one_smul]
  rw [cubeMeasure, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]

private theorem raw_eLpNorm_le_cubeFactor_mul_normalized
    {d : ℕ} (m : ℤ) (q : FiniteLpExponent)
    (F : Vec d → HilbertVec d) :
    eLpNorm F q.exponent (volume.restrict (openCubeSet (originCube d m))) ≤
      (ENNReal.ofReal (cubeVolume (originCube d m)) ^
        (1 / q.exponent).toReal) *
        eLpNorm F q.exponent (centeredCubeDomain d m).normalizedVolume := by
  calc
    eLpNorm F q.exponent (volume.restrict (openCubeSet (originCube d m))) ≤
        eLpNorm F q.exponent
          (ENNReal.ofReal (cubeVolume (originCube d m)) •
            (centeredCubeDomain d m).normalizedVolume) :=
      eLpNorm_mono_measure F (centeredCube_rawVolume_le_smul_normalizedVolume m)
    _ = _ := by
      exact eLpNorm_smul_measure_of_ne_zero
        (ENNReal.ofReal_ne_zero_iff.2 (cubeVolume_pos _)) F q.exponent _

private theorem tendsto_rawEuclideanLpENorm_finiteLpSolutionApproximation_grad_sub
    (d : ℕ) [NeZero d] (q : FiniteLpExponent) (m : ℤ) (sigma0 : ℝ)
    (h : CubeEuclideanLpField (originCube d m) q) (hsigma0 : 0 < sigma0) :
    Tendsto (fun nk : ℕ × ℕ =>
      eLpNorm (fun x => HilbertVec.ofVec
        ((finiteLpSolutionApproximation m hsigma0 h nk.1).toH1Function.grad x -
          (finiteLpSolutionApproximation m hsigma0 h nk.2).toH1Function.grad x))
        q.exponent (volume.restrict (openCubeSet (originCube d m))))
      atTop (nhds 0) := by
  obtain ⟨C, hCtop, hC⟩ :=
    exists_tendsto_normalizedEuclideanLpENorm_finiteLpSolutionApproximation_grad_sub d q
  have hnormalized := hC m sigma0 h hsigma0
  have hnormalized' : Tendsto (fun nk : ℕ × ℕ =>
      eLpNorm (fun x => HilbertVec.ofVec
        ((finiteLpSolutionApproximation m hsigma0 h nk.1).toH1Function.grad x -
          (finiteLpSolutionApproximation m hsigma0 h nk.2).toH1Function.grad x))
        q.exponent (centeredCubeDomain d m).normalizedVolume)
      atTop (nhds 0) := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
      eLpNorm_norm] using hnormalized
  let A : ℝ≥0∞ := ENNReal.ofReal (cubeVolume (originCube d m)) ^
    (1 / q.exponent).toReal
  have hAtop : A ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hright : Tendsto (fun nk : ℕ × ℕ =>
      A * eLpNorm (fun x => HilbertVec.ofVec
        ((finiteLpSolutionApproximation m hsigma0 h nk.1).toH1Function.grad x -
          (finiteLpSolutionApproximation m hsigma0 h nk.2).toH1Function.grad x))
        q.exponent (centeredCubeDomain d m).normalizedVolume)
      atTop (nhds 0) := by
    simpa only [A, mul_zero] using
      ENNReal.Tendsto.const_mul (a := A) hnormalized' (Or.inr hAtop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hright
    (fun _ => zero_le) (fun nk => ?_)
  exact raw_eLpNorm_le_cubeFactor_mul_normalized m q _

private theorem finiteLpSolutionApproximation_grad_memLp
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (n : ℕ) :
    MemLp (fun x => HilbertVec.ofVec
      ((finiteLpSolutionApproximation m hsigma0 h n).toH1Function.grad x))
      q.exponent (volume.restrict (openCubeSet (originCube d m))) := by
  obtain ⟨C, hCtop, hC⟩ := centeredCubeH10ScalarDivergence_cz d q
  let u := finiteLpSolutionApproximation m hsigma0 h n
  let hn := finiteLpDataApproximation h n
  have hnormalized :
      eLpNorm (fun x => HilbertVec.ofVec (u.toH1Function.grad x))
        q.exponent (centeredCubeDomain d m).normalizedVolume ≤
      C * (ENNReal.ofReal sigma0)⁻¹ *
        eLpNorm (fun x => HilbertVec.ofVec (hn.toField x))
          q.exponent (centeredCubeDomain d m).normalizedVolume := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm, euclideanNorm_eq_norm_ofVec,
      eLpNorm_norm, u, hn] using
      hC m sigma0 hn u hsigma0
        (finiteLpSolutionApproximation_normalized_weak m hsigma0 h n)
  have hdata : MemLp (fun x => HilbertVec.ofVec (hn.toField x)) q.exponent
      (centeredCubeDomain d m).normalizedVolume := by
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
      hn.euclideanMemLp
  have hfactor_top : C * (ENNReal.ofReal sigma0)⁻¹ ≠ ∞ :=
    ENNReal.mul_ne_top hCtop.ne
      (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hsigma0)))
  have hright_top : C * (ENNReal.ofReal sigma0)⁻¹ *
      eLpNorm (fun x => HilbertVec.ofVec (hn.toField x)) q.exponent
        (centeredCubeDomain d m).normalizedVolume < ∞ :=
    ENNReal.mul_lt_top hfactor_top.lt_top hdata.eLpNorm_lt_top
  refine ⟨?_, ?_⟩
  · simpa only [u, hilbertifyVecField] using!
      (memHilbertVectorL2_hilbertifyVecField u.toH1Function.grad_memVectorL2).aestronglyMeasurable
  · refine lt_of_le_of_lt (raw_eLpNorm_le_cubeFactor_mul_normalized m q _) ?_
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top).lt_top
      (lt_of_le_of_lt hnormalized hright_top)

/-- The canonical finite-data approximants have `L^q` gradient coordinates on
the unnormalized open cube.  This is deliberately exposed within the internal
CZ namespace so that the later zero-trace bridge need not repeat the measure
transport. -/
theorem finiteLpSolutionApproximation_gradMemLp
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (n : ℕ) :
    GradMemLpOn (openCubeSet (originCube d m)) q.exponent
      (finiteLpSolutionApproximation m hsigma0 h n).toH1Function.grad := by
  intro i
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
    (finiteLpSolutionApproximation_grad_memLp m hsigma0 h n).eval_piLp i

private noncomputable def finiteLpSolutionApproximation_gradientLp
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (n : ℕ) :
    Lp (HilbertVec d) q.exponent (volume.restrict (openCubeSet (originCube d m))) :=
  (finiteLpSolutionApproximation_grad_memLp m hsigma0 h n).toLp _

private theorem cauchySeq_finiteLpSolutionApproximation_gradientLp
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) [Fact (1 ≤ q.exponent)] (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    CauchySeq (finiteLpSolutionApproximation_gradientLp m hsigma0 h) := by
  rw [Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
  have htend :=
    tendsto_rawEuclideanLpENorm_finiteLpSolutionApproximation_grad_sub d q m sigma0 h hsigma0
  refine htend.congr' ?_
  filter_upwards [] with nk
  apply eLpNorm_congr_ae
  filter_upwards [MemLp.coeFn_toLp
    (finiteLpSolutionApproximation_grad_memLp m hsigma0 h nk.1),
    MemLp.coeFn_toLp
      (finiteLpSolutionApproximation_grad_memLp m hsigma0 h nk.2)] with x hx hy
  simp only [finiteLpSolutionApproximation_gradientLp]
  change HilbertVec.ofVec
      ((finiteLpSolutionApproximation m hsigma0 h nk.1).toH1Function.grad x -
        (finiteLpSolutionApproximation m hsigma0 h nk.2).toH1Function.grad x) =
    _ - _
  rw [hx, hy]
  exact (HilbertVec.ofVecL d).map_sub _ _

private theorem exists_finiteLpGradientSubsequence
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) [Fact (1 ≤ q.exponent)]
    (m : ℤ) {sigma0 : ℝ} (hsigma0 : 0 < sigma0)
    (h : CubeEuclideanLpField (originCube d m) q) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∀ N, ∀ n ≥ r N,
      dist (finiteLpSolutionApproximation_gradientLp m hsigma0 h n)
        (finiteLpSolutionApproximation_gradientLp m hsigma0 h (r N)) <
        ((1 : ℝ) / 2) ^ (N + 2) := by
  exact Metric.exists_subseq_bounded_of_cauchySeq
    (finiteLpSolutionApproximation_gradientLp m hsigma0 h)
    (cauchySeq_finiteLpSolutionApproximation_gradientLp q m hsigma0 h)
    (fun N => ((1 : ℝ) / 2) ^ (N + 2)) (fun N => by positivity)

private noncomputable def finiteLpGradientSubsequence
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    ℕ → ℕ := by
  letI : Fact (1 ≤ q.exponent) := ⟨q.one_lt.le⟩
  exact Classical.choose (exists_finiteLpGradientSubsequence q m hsigma0 h)

private theorem finiteLpGradientSubsequence_strictMono
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    StrictMono (finiteLpGradientSubsequence q m hsigma0 h) := by
  let : Fact (1 ≤ q.exponent) := ⟨q.one_lt.le⟩
  exact (Classical.choose_spec (exists_finiteLpGradientSubsequence q m hsigma0 h)).1

private theorem finiteLpGradientSubsequence_dist_lt
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (N n : ℕ) (hn : finiteLpGradientSubsequence q m hsigma0 h N ≤ n) :
    dist (finiteLpSolutionApproximation_gradientLp m hsigma0 h n)
      (finiteLpSolutionApproximation_gradientLp m hsigma0 h
        (finiteLpGradientSubsequence q m hsigma0 h N)) <
      ((1 : ℝ) / 2) ^ (N + 2) := by
  let : Fact (1 ≤ q.exponent) := ⟨q.one_lt.le⟩
  exact (Classical.choose_spec (exists_finiteLpGradientSubsequence q m hsigma0 h)).2 N n hn

private theorem eLpNorm_finiteLpSolutionApproximation_gradient_sub_eq_edist
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (n k : ℕ) :
    eLpNorm (fun x => HilbertVec.ofVec
      ((finiteLpSolutionApproximation m hsigma0 h n).toH1Function.grad x -
        (finiteLpSolutionApproximation m hsigma0 h k).toH1Function.grad x))
      q.exponent (volume.restrict (openCubeSet (originCube d m))) =
      edist (finiteLpSolutionApproximation_gradientLp m hsigma0 h n)
        (finiteLpSolutionApproximation_gradientLp m hsigma0 h k) := by
  let : Fact (1 ≤ q.exponent) := ⟨q.one_lt.le⟩
  symm
  simpa only [finiteLpSolutionApproximation_gradientLp,
    HilbertVec.ofVecL_apply] using!
    Lp.edist_toLp_toLp _ _
      (finiteLpSolutionApproximation_grad_memLp m hsigma0 h n)
      (finiteLpSolutionApproximation_grad_memLp m hsigma0 h k)

private theorem finiteLpGradientSubsequence_vector_eLpNorm_sub_lt
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (N n k : ℕ) (hNn : N ≤ n) (hNk : N ≤ k) :
    eLpNorm (fun x => HilbertVec.ofVec
      ((finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientSubsequence q m hsigma0 h n)).toH1Function.grad x -
        (finiteLpSolutionApproximation m hsigma0 h
          (finiteLpGradientSubsequence q m hsigma0 h k)).toH1Function.grad x))
      q.exponent (volume.restrict (openCubeSet (originCube d m))) <
      ENNReal.ofReal (((1 : ℝ) / 2) ^ N) := by
  let : Fact (1 ≤ q.exponent) := ⟨q.one_lt.le⟩
  let r := finiteLpGradientSubsequence q m hsigma0 h
  let u := finiteLpSolutionApproximation_gradientLp m hsigma0 h
  have hrn : r N ≤ r n := (finiteLpGradientSubsequence_strictMono q m hsigma0 h).monotone hNn
  have hrk : r N ≤ r k := (finiteLpGradientSubsequence_strictMono q m hsigma0 h).monotone hNk
  have hdn : dist (u (r n)) (u (r N)) < ((1 : ℝ) / 2) ^ (N + 2) :=
    finiteLpGradientSubsequence_dist_lt q m hsigma0 h N (r n) hrn
  have hdk : dist (u (r k)) (u (r N)) < ((1 : ℝ) / 2) ^ (N + 2) :=
    finiteLpGradientSubsequence_dist_lt q m hsigma0 h N (r k) hrk
  have hpow : 0 < ((1 : ℝ) / 2) ^ (N + 2) := by positivity
  have hsum : edist (u (r n)) (u (r k)) <
      ENNReal.ofReal (((1 : ℝ) / 2) ^ (N + 2)) +
        ENNReal.ofReal (((1 : ℝ) / 2) ^ (N + 2)) := by
    calc
      edist (u (r n)) (u (r k)) ≤ edist (u (r n)) (u (r N)) +
          edist (u (r k)) (u (r N)) := edist_triangle_right _ _ _
      _ = ENNReal.ofReal (dist (u (r n)) (u (r N))) +
          ENNReal.ofReal (dist (u (r k)) (u (r N))) := by
        rw [Lp.edist_dist, Lp.edist_dist]
      _ < _ := ENNReal.add_lt_add
        ((ENNReal.ofReal_lt_ofReal_iff hpow).2 hdn)
        ((ENNReal.ofReal_lt_ofReal_iff hpow).2 hdk)
  have hreal : 2 * ((1 : ℝ) / 2) ^ (N + 2) < ((1 : ℝ) / 2) ^ N := by
    calc
      2 * ((1 : ℝ) / 2) ^ (N + 2) =
          ((1 : ℝ) / 2) ^ N * (2 * ((1 : ℝ) / 2) ^ 2) := by
        rw [show N + 2 = N + 2 by rfl, pow_add]
        ring_nf
      _ = ((1 : ℝ) / 2) ^ N * ((1 : ℝ) / 2) := by norm_num
      _ < ((1 : ℝ) / 2) ^ N * 1 := by
        gcongr
        norm_num
      _ = ((1 : ℝ) / 2) ^ N := by ring_nf
  rw [eLpNorm_finiteLpSolutionApproximation_gradient_sub_eq_edist q m hsigma0 h]
  calc
    edist (u (r n)) (u (r k)) <
        ENNReal.ofReal (((1 : ℝ) / 2) ^ (N + 2)) +
          ENNReal.ofReal (((1 : ℝ) / 2) ^ (N + 2)) := hsum
    _ = ENNReal.ofReal (2 * ((1 : ℝ) / 2) ^ (N + 2)) := by
      rw [← ENNReal.ofReal_add (le_of_lt hpow) (le_of_lt hpow)]
      ring_nf
    _ < ENNReal.ofReal (((1 : ℝ) / 2) ^ N) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hreal

theorem exists_finiteLpGradientLimit
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ Du : Vec d → Vec d,
      GradMemLpOn (openCubeSet (originCube d m)) q.exponent Du ∧
        ∀ i : Fin d,
          Tendsto (fun N => eLpNorm (fun x =>
            (finiteLpSolutionApproximation m hsigma0 h (r N)).toH1Function.grad x i -
              Du x i) q.exponent
            (volume.restrict (openCubeSet (originCube d m)))) atTop (nhds 0) := by
  let r := finiteLpGradientSubsequence q m hsigma0 h
  refine ⟨r, finiteLpGradientSubsequence_strictMono q m hsigma0 h, ?_⟩
  have hmem : ∀ i : Fin d, ∀ N,
      MemLp (fun x =>
        (finiteLpSolutionApproximation m hsigma0 h (r N)).toH1Function.grad x i)
        q.exponent (volume.restrict (openCubeSet (originCube d m))) := by
    intro i N
    exact finiteLpSolutionApproximation_gradMemLp m hsigma0 h (r N) i
  have hsum : ∑' N : ℕ, ENNReal.ofReal (((1 : ℝ) / 2) ^ N) ≠ ∞ :=
    summable_geometric_two.tsum_ofReal_ne_top
  have hcau : ∀ (i : Fin d) (N n k : ℕ), N ≤ n → N ≤ k →
      eLpNorm (fun x =>
        (finiteLpSolutionApproximation m hsigma0 h (r n)).toH1Function.grad x i -
          (finiteLpSolutionApproximation m hsigma0 h (r k)).toH1Function.grad x i)
        q.exponent (volume.restrict (openCubeSet (originCube d m))) <
        ENNReal.ofReal (((1 : ℝ) / 2) ^ N) := by
    intro i N n k hNn hNk
    calc
      eLpNorm (fun x =>
          (finiteLpSolutionApproximation m hsigma0 h (r n)).toH1Function.grad x i -
            (finiteLpSolutionApproximation m hsigma0 h (r k)).toH1Function.grad x i)
          q.exponent (volume.restrict (openCubeSet (originCube d m))) ≤
        eLpNorm (fun x => HilbertVec.ofVec
          ((finiteLpSolutionApproximation m hsigma0 h (r n)).toH1Function.grad x -
            (finiteLpSolutionApproximation m hsigma0 h (r k)).toH1Function.grad x))
          q.exponent (volume.restrict (openCubeSet (originCube d m))) := by
          simpa only [Pi.sub_apply] using coordinate_eLpNorm_le_euclidean
            (volume.restrict (openCubeSet (originCube d m))) q
            (fun x =>
              (finiteLpSolutionApproximation m hsigma0 h (r n)).toH1Function.grad x -
                (finiteLpSolutionApproximation m hsigma0 h (r k)).toH1Function.grad x) i
      _ < ENNReal.ofReal (((1 : ℝ) / 2) ^ N) :=
        finiteLpGradientSubsequence_vector_eLpNorm_sub_lt q m hsigma0 h N n k hNn hNk
  choose D hDmem hDtend using fun i =>
    Lp.cauchy_complete_eLpNorm q.one_lt.le (hmem i) hsum (hcau i)
  refine ⟨fun x i => D i x, ?_, ?_⟩
  · intro i
    exact hDmem i
  · intro i
    simpa only [r] using! hDtend i

/-- The subsequence selected together with the canonical limiting gradient. -/
noncomputable def finiteLpGradientLimitSubsequence
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    ℕ → ℕ :=
  Classical.choose (exists_finiteLpGradientLimit q m hsigma0 h)

/-- The canonical `L^q` gradient representative selected from the controlled
finite-data approximation sequence. -/
noncomputable def finiteLpGradientLimit
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Vec d → Vec d :=
  Classical.choose (Classical.choose_spec (exists_finiteLpGradientLimit q m hsigma0 h)).2

theorem finiteLpGradientLimitSubsequence_strictMono
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    StrictMono (finiteLpGradientLimitSubsequence q m hsigma0 h) :=
  (Classical.choose_spec (exists_finiteLpGradientLimit q m hsigma0 h)).1

theorem finiteLpGradientLimit_gradMemLp
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    GradMemLpOn (openCubeSet (originCube d m)) q.exponent
      (finiteLpGradientLimit q m hsigma0 h) :=
  (Classical.choose_spec
    (Classical.choose_spec (exists_finiteLpGradientLimit q m hsigma0 h)).2).1

theorem tendsto_eLpNorm_finiteLpSolutionApproximation_gradCoord_sub_finiteLpGradientLimit
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q)
    (i : Fin d) :
    Tendsto (fun N => eLpNorm (fun x =>
      (finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad x i -
        (finiteLpGradientLimit q m hsigma0 h) x i) q.exponent
      (volume.restrict (openCubeSet (originCube d m)))) atTop (nhds 0) :=
  (Classical.choose_spec
    (Classical.choose_spec (exists_finiteLpGradientLimit q m hsigma0 h)).2).2 i

theorem tendsto_eLpNorm_finiteLpSolutionApproximation_grad_sub_finiteLpGradientLimit
    {d : ℕ} [NeZero d] (q : FiniteLpExponent) (m : ℤ) {sigma0 : ℝ}
    (hsigma0 : 0 < sigma0) (h : CubeEuclideanLpField (originCube d m) q) :
    Tendsto (fun N => eLpNorm (fun x => HilbertVec.ofVec
      ((finiteLpSolutionApproximation m hsigma0 h
        (finiteLpGradientLimitSubsequence q m hsigma0 h N)).toH1Function.grad x -
        (finiteLpGradientLimit q m hsigma0 h) x)) q.exponent
      (volume.restrict (openCubeSet (originCube d m)))) atTop (nhds 0) := by
  let r := finiteLpGradientLimitSubsequence q m hsigma0 h
  let Du := finiteLpGradientLimit q m hsigma0 h
  have hcoord : ∀ i : Fin d,
      Tendsto (fun N => eLpNorm (fun x =>
        (finiteLpSolutionApproximation m hsigma0 h (r N)).toH1Function.grad x i -
          Du x i) q.exponent
        (volume.restrict (openCubeSet (originCube d m)))) atTop (nhds 0) := by
    intro i
    simpa only [r, Du] using
      tendsto_eLpNorm_finiteLpSolutionApproximation_gradCoord_sub_finiteLpGradientLimit
        q m hsigma0 h i
  have hsum : Tendsto (fun N => ∑ i : Fin d,
      eLpNorm (fun x =>
        (finiteLpSolutionApproximation m hsigma0 h (r N)).toH1Function.grad x i -
          Du x i) q.exponent
        (volume.restrict (openCubeSet (originCube d m)))) atTop (nhds 0) := by
    simpa using (tendsto_finsetSum Finset.univ fun i _ => hcoord i)
  have hright : Tendsto (fun N => ‖(d : ℝ)‖ₑ * ∑ i : Fin d,
      eLpNorm (fun x =>
        (finiteLpSolutionApproximation m hsigma0 h (r N)).toH1Function.grad x i -
          Du x i) q.exponent
        (volume.restrict (openCubeSet (originCube d m)))) atTop (nhds 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul (a := ‖(d : ℝ)‖ₑ)
      hsum (Or.inr ENNReal.coe_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hright
    (fun _ => zero_le) (fun N => ?_)
  apply euclidean_eLpNorm_le_dimension_mul_sum_coordinates
    (volume.restrict (openCubeSet (originCube d m))) q
    (fun x =>
      (finiteLpSolutionApproximation m hsigma0 h (r N)).toH1Function.grad x - Du x)
  intro i
  exact ((finiteLpSolutionApproximation_gradMemLp m hsigma0 h (r N) i).sub
    (finiteLpGradientLimit_gradMemLp q m hsigma0 h i)).aestronglyMeasurable

end INTERNAL

end CubeCalderonZygmund

end
end Homogenization
