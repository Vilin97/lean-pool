/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianRepresentation
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.NewtonianKernelIntegrability

/-!
# Interior Basic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic


/-!
# Harmonic interior estimates from the Newtonian representation

Kernel and integration-by-parts infrastructure for the representation route.
-/
noncomputable section

namespace CKN.Foundation.Heat

def q (z : Vec3) : ℝ := ∑ i : Fin 3, z i ^ 2

lemma q_pos {z : Vec3} (hz : z ≠ 0) : 0 < q z := by
  have hsum : q z = vec3EuclideanNorm z ^ 2 := by
    unfold q vec3EuclideanNorm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg (fun i _ => sq_nonneg (z i))
  rw [hsum]
  have : 0 < vec3EuclideanNorm z := by
    rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
    intro hzero
    apply hz
    exact (WithLp.toLp_eq_zero 2).mp hzero
  positivity

lemma q_eq_vec3Norm_sq (z : Vec3) :
    q z = vec3EuclideanNorm z ^ 2 := by
  unfold q vec3EuclideanNorm
  rw [Real.sq_sqrt]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg (z i))

private lemma hasFDerivAt_q (z : Vec3) :
    HasFDerivAt q
      (∑ i : Fin 3, (2 * z i) •
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z := by
  have hfun : q = ∑ i : Fin 3, (fun y : Vec3 => y i * y i) := by
    funext y
    simp [q, pow_two]
  have hsum : HasFDerivAt
      (∑ i : Fin 3, (fun y : Vec3 => y i * y i))
      (∑ i : Fin 3, (2 * z i) •
        (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z := by
    apply HasFDerivAt.sum
    intro i _hi
    have hprod := (hasFDerivAt_apply (𝕜 := ℝ) i z).mul
      (hasFDerivAt_apply (𝕜 := ℝ) i z)
    convert hprod using 1
    ext v
    simp [smul_eq_mul]
    ring_nf
  rw [hfun]
  exact hsum

lemma hasFDerivAt_newtonianKernel {z : Vec3} (hz : z ≠ 0) :
    HasFDerivAt newtonianKernel
      ((4 * Real.pi)⁻¹ •
        ((-(1 : ℝ) / 2 * q z ^ (-(1 : ℝ) / 2 - 1)) •
          ∑ i : Fin 3, (2 * z i) •
            (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ))) z := by
  have hq : HasFDerivAt (fun y : Vec3 => q y ^ (-(1 : ℝ) / 2))
      ((-(1 : ℝ) / 2 * q z ^ (-(1 : ℝ) / 2 - 1)) •
        ∑ i : Fin 3, (2 * z i) •
          (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) z := by
    exact (hasFDerivAt_q z).rpow_const (p := -(1 : ℝ) / 2)
      (Or.inl (q_pos hz).ne')
  have hkernel : (fun y : Vec3 => newtonianKernel y) =
      (fun y : Vec3 => (4 * Real.pi)⁻¹ * q y ^ (-(1 : ℝ) / 2)) := by
    funext y
    by_cases hy : y = 0
    · subst y
      simp [newtonianKernel, q, vec3EuclideanNorm]
    · rw [newtonianKernel, q_eq_vec3Norm_sq]
      rw [one_div]
      rw [show (4 * Real.pi * vec3EuclideanNorm y)⁻¹ =
          (4 * Real.pi)⁻¹ * (vec3EuclideanNorm y)⁻¹ by ring]
      rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg (sq_nonneg (vec3EuclideanNorm y))]
      have hsqrt : (vec3EuclideanNorm y ^ 2) ^ (1 / 2 : ℝ) =
          vec3EuclideanNorm y := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      rw [hsqrt]
  change HasFDerivAt (fun y : Vec3 => newtonianKernel y) _ z
  rw [hkernel]
  exact hq.const_mul (4 * Real.pi)⁻¹

lemma spatialDeriv_newtonianKernel_shift {x y : Vec3} (hxy : x - y ≠ 0)
    (i : Fin 3) :
    CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (x - z)) i y =
      (4 * Real.pi)⁻¹ * (x - y) i * q (x - y) ^ (-(3 : ℝ) / 2) := by
  have hsub : HasFDerivAt (fun z : Vec3 => x - z)
      (-ContinuousLinearMap.id ℝ Vec3) y := by
    simpa using (hasFDerivAt_const (𝕜 := ℝ) x y).sub
      (hasFDerivAt_id (𝕜 := ℝ) y)
  have hcomp := (hasFDerivAt_newtonianKernel hxy).comp y hsub
  have hi := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i)) hcomp.fderiv
  change (fderiv ℝ (newtonianKernel ∘ (fun z : Vec3 => x - z)) y)
      (CKN.basisVec i) = _
  rw [hi]
  simp only [ContinuousLinearMap.comp_apply]
  simp [smul_eq_mul, CKN.basisVec_apply]
  ring_nf

private lemma contDiff_q : ContDiff ℝ (⊤ : ℕ∞) q := by
  unfold q
  apply ContDiff.sum
  intro i hi
  exact (contDiff_apply ℝ ℝ i).pow 2

private lemma contDiffAt_newtonianKernel {z : Vec3} (hz : z ≠ 0) :
    ContDiffAt ℝ (2 : ℕ) newtonianKernel z := by
  have hqpos : q z ≠ 0 := (q_pos hz).ne'
  have hpow := (Real.contDiffAt_rpow_const (n := 2)
    (x := q z) (p := -(1 : ℝ) / 2) (Or.inl hqpos)).comp z
    (contDiff_q.contDiffAt.of_le (by norm_num))
  have hconst : ContDiffAt ℝ (2 : ℕ)
      (fun _ : Vec3 => (4 * Real.pi)⁻¹) z :=
    (contDiff_const : ContDiff ℝ (2 : ℕ) (fun _ : Vec3 => (4 * Real.pi)⁻¹)).contDiffAt
  have hmul := hconst.mul hpow
  have hkernel : (fun y : Vec3 => newtonianKernel y) =
      (fun y : Vec3 => (4 * Real.pi)⁻¹ * q y ^ (-(1 : ℝ) / 2)) := by
    funext y
    by_cases hy : y = 0
    · subst y
      simp [newtonianKernel, q, vec3EuclideanNorm]
    · rw [newtonianKernel, q_eq_vec3Norm_sq]
      rw [one_div]
      rw [show (4 * Real.pi * vec3EuclideanNorm y)⁻¹ =
          (4 * Real.pi)⁻¹ * (vec3EuclideanNorm y)⁻¹ by ring]
      rw [show -(1 : ℝ) / 2 = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg (sq_nonneg (vec3EuclideanNorm y))]
      have hsqrt : (vec3EuclideanNorm y ^ 2) ^ (1 / 2 : ℝ) =
          vec3EuclideanNorm y := by
        rw [← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
          abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
      rw [hsqrt]
  change ContDiffAt ℝ (2 : ℕ) (fun y : Vec3 => newtonianKernel y) z
  rw [hkernel]
  simpa only [Function.comp_apply] using hmul

def kernelDerivative (i : Fin 3) (z : Vec3) : ℝ :=
  if z = 0 then 0 else
    (4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2)

private lemma kernelDerivative_locallyIntegrable (i : Fin 3) :
    LocallyIntegrable (kernelDerivative i) volume := by
  have hnorm : Continuous (fun z : Vec3 => vec3EuclideanNorm z) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hmeas : AEStronglyMeasurable (kernelDerivative i) volume := by
    unfold kernelDerivative
    have hset : MeasurableSet {z : Vec3 | z = 0} := by
      simpa only [Set.ofPred_eq_eq_singleton] using (measurableSet_singleton (0 : Vec3))
    have hqcont : Continuous q := by
      unfold q
      fun_prop
    have hqzero : MeasurableSet {z : Vec3 | q z = 0} := by
      exact measurableSet_eq.preimage hqcont.measurable
    have hqnonneg : ∀ z : Vec3, 0 ≤ q z := by
      intro z
      unfold q
      positivity
    have hpowm : Measurable (fun z : Vec3 => q z ^ (-(3 : ℝ) / 2)) := by
      have hexp : Measurable (fun z : Vec3 =>
          Real.exp (Real.log (q z) * (-(3 : ℝ) / 2))) := by
        exact ((hqcont.measurable.log).mul measurable_const).exp
      have hm : Measurable (fun z : Vec3 =>
          if q z = 0 then (0 : ℝ) else
            Real.exp (Real.log (q z) * (-(3 : ℝ) / 2))) :=
        Measurable.ite hqzero
          (measurable_const : Measurable (fun _ : Vec3 => (0 : ℝ))) hexp
      have hEq : (fun z : Vec3 => q z ^ (-(3 : ℝ) / 2)) =
          (fun z : Vec3 => if q z = 0 then 0 else
            Real.exp (Real.log (q z) * (-(3 : ℝ) / 2))) := by
        funext z
        rw [Real.rpow_def_of_nonneg (hqnonneg z)]
        norm_num
      rw [hEq]
      exact hm
    have hformula : Measurable (fun z : Vec3 =>
        (4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2)) := by
      exact (measurable_const.mul (measurable_pi_apply i)).mul hpowm
    exact (Measurable.ite hset measurable_const hformula).aestronglyMeasurable
  refine locallyIntegrable_of_norm_le_rpow (E := Vec3) (F := ℝ)
    (C := (4 * Real.pi)⁻¹) (α := (2 : ℝ)) ?_ (by norm_num) ?_ hmeas
  · change 1 ≤ Module.finrank ℝ (Fin 3 → ℝ)
    rw [Module.finrank_fin_fun]
    norm_num
  · filter_upwards [] with z
    by_cases hz : z = 0
    · subst z
      simp [kernelDerivative]
    · have hr : 0 < vec3EuclideanNorm z := by
        rw [vec3EuclideanNorm_eq_l2, norm_pos_iff]
        intro hzero
        exact hz ((WithLp.toLp_eq_zero 2).mp hzero)
      have hq : q z = vec3EuclideanNorm z ^ 2 := q_eq_vec3Norm_sq z
      have hqi : q z ^ (-(3 : ℝ) / 2) =
          (vec3EuclideanNorm z) ^ (-(3 : ℝ)) := by
        rw [hq, show (-(3 : ℝ) / 2) = -(3 / 2 : ℝ) by ring,
          show vec3EuclideanNorm z ^ 2 = vec3EuclideanNorm z ^ (2 : ℝ) by norm_num,
          ← Real.rpow_mul (vec3EuclideanNorm_nonneg z)]
        congr 1
        ring
      have hcoord : |z i| ≤ vec3EuclideanNorm z := by
        simpa [CKN.vecEuclideanNorm, CKN.vecNormSq, CKN.vecDot,
          vec3EuclideanNorm, pow_two] using CKN.abs_apply_le_vecEuclideanNorm z i
      rw [kernelDerivative, ite_eq_right hz, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (by positivity),
        abs_of_nonneg (Real.rpow_nonneg (q_pos hz).le _)]
      rw [hqi]
      have hpow : vec3EuclideanNorm z *
          vec3EuclideanNorm z ^ (-(3 : ℝ)) =
          vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
        calc
          vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ)) =
              vec3EuclideanNorm z ^ (1 : ℝ) *
                vec3EuclideanNorm z ^ (-(3 : ℝ)) := by
            rw [Real.rpow_one]
          _ = vec3EuclideanNorm z ^ ((1 : ℝ) + (-(3 : ℝ))) := by
            rw [← Real.rpow_add hr]
          _ = vec3EuclideanNorm z ^ (-(2 : ℝ)) := by norm_num
      calc
        (4 * Real.pi)⁻¹ * |z i| * vec3EuclideanNorm z ^ (-(3 : ℝ)) ≤
            (4 * Real.pi)⁻¹ * vec3EuclideanNorm z *
              vec3EuclideanNorm z ^ (-(3 : ℝ)) := by
          gcongr
        _ = (4 * Real.pi)⁻¹ * vec3EuclideanNorm z ^ (-(2 : ℝ)) := by
          rw [show (4 * Real.pi)⁻¹ * vec3EuclideanNorm z *
              vec3EuclideanNorm z ^ (-(3 : ℝ)) =
              (4 * Real.pi)⁻¹ *
                (vec3EuclideanNorm z * vec3EuclideanNorm z ^ (-(3 : ℝ))) by ring,
            hpow]
        _ ≤ (4 * Real.pi)⁻¹ * ‖z‖ ^ (-(2 : ℝ)) := by
          have hspace : ‖z‖ ≤ vec3EuclideanNorm z := CKN.space_norm_le_euclideanNorm z
          have hinv : (vec3EuclideanNorm z) ^ (-(2 : ℝ)) ≤ ‖z‖ ^ (-(2 : ℝ)) := by
            rw [show (-(2 : ℝ)) = -(2 : ℝ) by norm_num,
              Real.rpow_neg (vec3EuclideanNorm_nonneg _),
              show (-(2 : ℝ)) = -(2 : ℝ) by norm_num,
              Real.rpow_neg (norm_nonneg _)]
            apply (inv_le_inv₀ (by positivity) (by positivity)).2
            have hsquare : ‖z‖ ^ (2 : ℝ) ≤
                (vec3EuclideanNorm z) ^ (2 : ℝ) := by
              rw [Real.rpow_two, Real.rpow_two]
              exact (sq_le_sq₀ (norm_nonneg _) (vec3EuclideanNorm_nonneg _)).2 hspace
            exact hsquare
          exact mul_le_mul_of_nonneg_left hinv (by positivity)

private lemma kernelDerivative_shift_locallyIntegrable (x : Vec3) (i : Fin 3) :
    LocallyIntegrable (fun y : Vec3 => kernelDerivative i (x - y)) volume := by
  have hmp := Measure.measurePreserving_sub_left (volume : Measure Vec3) x
  have hmap : Measure.map (fun y : Vec3 => x - y) volume = volume := hmp.map_eq
  have hbase : LocallyIntegrable (kernelDerivative i)
      (Measure.map (Homeomorph.subLeft x) volume) := by
    change LocallyIntegrable (kernelDerivative i)
      (Measure.map (fun y : Vec3 => x - y) volume)
    rw [hmap]
    exact kernelDerivative_locallyIntegrable i
  have hcomp := (locallyIntegrable_map_homeomorph (Homeomorph.subLeft x)
    (f := kernelDerivative i)).1 hbase
  change LocallyIntegrable (fun y : Vec3 => kernelDerivative i (x - y)) volume at hcomp
  exact hcomp

private lemma spatialDeriv_kernel_eq_kernelDerivative {x y : Vec3} (hxy : x - y ≠ 0)
    (i : Fin 3) :
    CKN.spatialDeriv (fun z : Vec3 => newtonianKernel (x - z)) i y =
      kernelDerivative i (x - y) := by
  rw [kernelDerivative, ite_eq_right hxy]
  exact spatialDeriv_newtonianKernel_shift hxy i

/-- The smooth cutoff used in the annular harmonic representation. -/
def eta (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) : Vec3 → ℝ :=
  mollifiedBallCutoff x₀ hρ

/-- The Newtonian kernel times one cutoff derivative. -/
def kernelCutoffDerivative (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (i : Fin 3) (y : Vec3) : ℝ :=
  newtonianKernel (x - y) * spatialDeriv (eta x₀ hρ) i y

private lemma spatialDeriv_eta_eq_zero_on_closed_inner (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) {y : Vec3} (hy : y ∈ euclideanClosedBall x₀ (13 * ρ / 20))
    (i : Fin 3) : spatialDeriv (eta x₀ hρ) i y = 0 := by
  have hgrad := mollifiedBallCutoff_derivatives_vanish_outside_annulus x₀ hρ
    (hx := fun h => h.2 hy)
  change (fderiv ℝ (eta x₀ hρ) y) (basisVec i) = 0
  have hi := congrFun hgrad.1 i
  simpa [eta, classicalGradient, classicalGradient_apply, CKN.basisVec_apply] using hi

lemma contDiff_spatialDeriv_two {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (i : Fin 3) :
    ContDiff ℝ (2 : ℕ) (spatialDeriv f i) := by
  have hfd := hf.contDiff_fderiv_apply (m := (2 : ℕ))
    (n := (↑(⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  have hc : ContDiff ℝ (2 : ℕ)
      (fun x : Vec3 => (x, basisVec i)) := by
    fun_prop
  have hcomp := hfd.comp hc
  change ContDiff ℝ (2 : ℕ)
    (fun x : Vec3 => (fderiv ℝ f x) (basisVec i))
  exact hcomp

lemma spatialDeriv_eta_eventually_zero (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    ∀ᶠ y in 𝓝 x, spatialDeriv (eta x₀ hρ) i y = 0 := by
  have hopen : IsOpen (euclideanBall x₀ (13 * ρ / 20)) := by
    change IsOpen {y : Vec3 | euclideanSqDist y x₀ < (13 * ρ / 20) ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  obtain ⟨δ, hδ, hball⟩ := (Metric.isOpen_iff.mp hopen) x hx
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  apply spatialDeriv_eta_eq_zero_on_closed_inner x₀ hρ _ i
  apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
    (x₀ := x₀) (x := y) (by positivity)).2
  exact le_of_lt ((mem_euclideanBall_iff_vecEuclideanNorm_lt
    (x₀ := x₀) (x := y) (by positivity)).1 (hball hy))

private lemma kernelCutoffDerivative_contDiffAt (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) (y : Vec3) :
    ContDiffAt ℝ (1 : ℕ) (kernelCutoffDerivative x x₀ hρ i) y := by
  by_cases hxy : x - y = 0
  · have heq : (kernelCutoffDerivative x x₀ hρ i) =ᶠ[𝓝 y]
        (fun _ : Vec3 => (0 : ℝ)) := by
      have hxy' : x = y := sub_eq_zero.mp hxy
      subst y
      filter_upwards [spatialDeriv_eta_eventually_zero x x₀ hρ hx i] with z hz
      simp [kernelCutoffDerivative, hz]
    have hzero : ContDiffAt ℝ (1 : ℕ) (fun _ : Vec3 => (0 : ℝ)) y :=
      (contDiff_const : ContDiff ℝ (1 : ℕ) (fun _ : Vec3 => (0 : ℝ))).contDiffAt
    exact hzero.congr_of_eventuallyEq heq
  · have hsub : ContDiffAt ℝ (2 : ℕ) (fun z : Vec3 => x - z) y := by
      fun_prop
    have hkernel : ContDiffAt ℝ (2 : ℕ)
        (fun z : Vec3 => newtonianKernel (x - z)) y := by
      simpa only [Function.comp_def] using
        (contDiffAt_newtonianKernel hxy).comp y hsub
    have heta0 : ContDiff ℝ (↑(⊤ : ℕ∞)) (eta x₀ hρ) := by
      simpa only [eta] using mollifiedBallCutoff_smooth x₀ hρ
    have heta : ContDiffAt ℝ (2 : ℕ)
        (spatialDeriv (eta x₀ hρ) i) y :=
      (contDiff_spatialDeriv_two heta0 i).contDiffAt
    have hprod := hkernel.mul heta
    change ContDiffAt ℝ (1 : ℕ)
      (fun z : Vec3 => newtonianKernel (x - z) *
        spatialDeriv (eta x₀ hρ) i z) y
    exact hprod.of_le (by norm_num)

lemma kernelCutoffDerivative_contDiff (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    ContDiff ℝ (1 : ℕ) (kernelCutoffDerivative x x₀ hρ i) :=
  contDiff_iff_contDiffAt.mpr (kernelCutoffDerivative_contDiffAt x x₀ hρ hx i)

lemma kernelCutoffDerivative_hasCompactSupport (x x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) (i : Fin 3) :
    HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) := by
  have hd : HasCompactSupport (spatialDeriv (eta x₀ hρ) i) :=
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  change HasCompactSupport (fun y : Vec3 => newtonianKernel (x - y) *
    spatialDeriv (eta x₀ hρ) i y)
  exact hd.mul_left

lemma kernelCutoffDerivative_integrable_mul_left {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    Integrable (fun y : Vec3 =>
      spatialDeriv h i y * kernelCutoffDerivative x x₀ hρ i y) volume := by
  have hk : HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) :=
    kernelCutoffDerivative_hasCompactSupport x x₀ hρ i
  have hkc : Continuous (kernelCutoffDerivative x x₀ hρ i) :=
    (kernelCutoffDerivative_contDiff x x₀ hρ hx i).continuous
  have hhc : Continuous (spatialDeriv h i) := by
    exact (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  exact (hhc.mul hkc).integrable_of_hasCompactSupport hk.mul_left

lemma kernelCutoffDerivative_integrable_mul_right {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    Integrable (fun y : Vec3 =>
      h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y) volume := by
  have hk : HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) :=
    kernelCutoffDerivative_hasCompactSupport x x₀ hρ i
  have hkc : ContDiff ℝ (1 : ℕ) (kernelCutoffDerivative x x₀ hρ i) :=
    kernelCutoffDerivative_contDiff x x₀ hρ hx i
  have hkd : Continuous (CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i) := by
    exact (hkc.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hhc : Continuous h := hh.continuous
  have hkdSupport : HasCompactSupport
      (CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i) :=
    hk.fderiv_apply (𝕜 := ℝ) (basisVec i)
  exact (hhc.mul hkd).integrable_of_hasCompactSupport hkdSupport.mul_left

private lemma kernelCutoffDerivative_integrable_mul_h {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    Integrable (fun y : Vec3 =>
      h y * kernelCutoffDerivative x x₀ hρ i y) volume := by
  have hk : HasCompactSupport (kernelCutoffDerivative x x₀ hρ i) :=
    kernelCutoffDerivative_hasCompactSupport x x₀ hρ i
  have hkc : Continuous (kernelCutoffDerivative x x₀ hρ i) :=
    (kernelCutoffDerivative_contDiff x x₀ hρ hx i).continuous
  exact (hh.continuous.mul hkc).integrable_of_hasCompactSupport hk.mul_left

lemma integral_h_mul_kernelCutoffDerivative_spatialDeriv {h : Vec3 → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (x x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) (i : Fin 3) :
    ∫ y : Vec3, h y * CKN.spatialDeriv (kernelCutoffDerivative x x₀ hρ i) i y =
      -∫ y : Vec3, spatialDeriv h i y * kernelCutoffDerivative x x₀ hρ i y := by
  have hleft := kernelCutoffDerivative_integrable_mul_left hh x x₀ hρ hx i
  have hright := kernelCutoffDerivative_integrable_mul_right hh x x₀ hρ hx i
  have hprod := kernelCutoffDerivative_integrable_mul_h hh x x₀ hρ hx i
  have hfdiff : ∀ y ∈ tsupport (kernelCutoffDerivative x x₀ hρ i),
      DifferentiableAt ℝ h y := by
    intro y hy
    exact hh.differentiable (by simp) y
  have hgdiff : ∀ y ∈ tsupport h,
      DifferentiableAt ℝ (kernelCutoffDerivative x x₀ hρ i) y := by
    intro y hy
    exact (kernelCutoffDerivative_contDiff x x₀ hρ hx i).differentiable
      (by norm_num) y
  simpa only [spatialDeriv] using
    (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := basisVec i) hleft hright hprod hfdiff hgdiff)

lemma newtonianKernel_mul_compact_integrable {f : Vec3 → ℝ}
    (hf : Continuous f) (hfSupport : HasCompactSupport f) (x : Vec3) :
    Integrable (fun y : Vec3 => newtonianKernel (x - y) * f y) volume := by
  exact (locallyIntegrable_newtonianKernel_sub x).integrable_smul_right_of_hasCompactSupport
    hf hfSupport

theorem newtonianKernel_mul_compact_integrable_global {f : Vec3 → ℝ}
    (hf : Continuous f) (hfSupport : HasCompactSupport f) (x : Vec3) :
    Integrable (fun y : Vec3 => newtonianKernel (x - y) * f y) volume :=
  newtonianKernel_mul_compact_integrable hf hfSupport x

lemma laplacian_compact_support {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (CKN.spatialLaplacian f) := by
  have hgi (i : Fin 3) : HasCompactSupport
      (CKN.spatialDeriv (CKN.spatialDeriv f i) i) :=
    (hf.fderiv_apply (𝕜 := ℝ) (CKN.basisVec i)).fderiv_apply
      (𝕜 := ℝ) (CKN.basisVec i)
  have h01 : HasCompactSupport (fun y : Vec3 =>
      CKN.spatialDeriv (CKN.spatialDeriv f (0 : Fin 3)) 0 y +
        CKN.spatialDeriv (CKN.spatialDeriv f (1 : Fin 3)) 1 y) := by
    convert (hgi (0 : Fin 3)).add (hgi (1 : Fin 3)) using 1
  have hsum : HasCompactSupport (fun y : Vec3 =>
      CKN.spatialDeriv (CKN.spatialDeriv f (0 : Fin 3)) 0 y +
        CKN.spatialDeriv (CKN.spatialDeriv f (1 : Fin 3)) 1 y +
          CKN.spatialDeriv (CKN.spatialDeriv f (2 : Fin 3)) 2 y) := by
    convert h01.add (hgi (2 : Fin 3)) using 1
  change HasCompactSupport (fun y : Vec3 =>
    ∑ i : Fin 3, CKN.spatialDeriv (CKN.spatialDeriv f i) i y)
  simpa only [Fin.sum_univ_three] using hsum

theorem laplacian_compact_support_global {f : Vec3 → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (CKN.spatialLaplacian f) :=
  laplacian_compact_support hf

theorem newtonianKernel_size_bound {z : Vec3} (hz : z ≠ 0) :
    |newtonianKernel z| ≤ (4 * Real.pi)⁻¹ * ‖z‖⁻¹ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrn : 0 < vec3EuclideanNorm z :=
    lt_of_lt_of_le hzn (CKN.space_norm_le_euclideanNorm z)
  have hinv : (vec3EuclideanNorm z)⁻¹ ≤ ‖z‖⁻¹ := by
    exact (inv_le_inv₀ hrn hzn).2 (CKN.space_norm_le_euclideanNorm z)
  rw [newtonianKernel, abs_of_nonneg (by positivity)]
  rw [show 1 / (4 * Real.pi * vec3EuclideanNorm z) =
      (4 * Real.pi)⁻¹ * (vec3EuclideanNorm z)⁻¹ by field_simp]
  exact mul_le_mul_of_nonneg_left hinv (by positivity)

theorem newtonianKernel_continuousAt {z : Vec3} (hz : z ≠ 0) :
    ContinuousAt newtonianKernel z :=
  (contDiffAt_newtonianKernel hz).continuousAt

theorem newtonianKernel_hasFDerivAt {z : Vec3} (hz : z ≠ 0) :
    HasFDerivAt newtonianKernel (fderiv ℝ newtonianKernel z) z :=
  (contDiffAt_newtonianKernel hz).differentiableAt (by norm_num) |>.hasFDerivAt

theorem newtonianKernel_spatialDeriv_formula {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) :
    CKN.spatialDeriv newtonianKernel i z =
      -(4 * Real.pi)⁻¹ * z i * q z ^ (-(3 : ℝ) / 2) := by
  have hdirect := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec i))
    (hasFDerivAt_newtonianKernel hz).fderiv
  change CKN.spatialDeriv newtonianKernel i z = _ at hdirect
  convert hdirect using 1
  simp [smul_eq_mul, CKN.basisVec_apply]
  ring_nf

theorem newtonianKernel_spatialDeriv_second_formula {z : Vec3} (hz : z ≠ 0)
    (i j : Fin 3) :
    CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j z =
      -(4 * Real.pi)⁻¹ *
        ((if i = j then 1 else 0) * q z ^ (-(3 : ℝ) / 2) +
          z i * (-(3 : ℝ) / 2 * q z ^ (-(3 : ℝ) / 2 - 1) * (2 * z j))) := by
  have hpow := (hasFDerivAt_q z).rpow_const (p := -(3 : ℝ) / 2)
    (Or.inl (q_pos hz).ne')
  have hi := (hasFDerivAt_apply (𝕜 := ℝ) i z).mul hpow
  have hc := hi.const_mul (-(4 * Real.pi)⁻¹)
  have hformula : HasFDerivAt (fun y : Vec3 =>
      -(4 * Real.pi)⁻¹ * y i * q y ^ (-(3 : ℝ) / 2))
      ((-(4 * Real.pi)⁻¹) •
        ((z i) • ((-(3 : ℝ) / 2 * q z ^ (-(3 : ℝ) / 2 - 1)) •
          (∑ k : Fin 3, (2 * z k) •
            (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ))) +
          q z ^ (-(3 : ℝ) / 2) •
            (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ))) z := by
    convert hc using 1
    · ext y
      simp
      ring
  have hnonzero : ∀ᶠ w in 𝓝 z, w ≠ 0 :=
    isOpen_compl_singleton.mem_nhds hz
  have hfun : CKN.spatialDeriv newtonianKernel i =ᶠ[𝓝 z]
      (fun y : Vec3 =>
        -(4 * Real.pi)⁻¹ * y i * q y ^ (-(3 : ℝ) / 2)) := by
    filter_upwards [hnonzero] with w hw
    rw [newtonianKernel_spatialDeriv_formula hw i]
  have hfd := hformula.congr_of_eventuallyEq hfun
  have hfd' := hfd.fderiv
  have happly := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (CKN.basisVec j)) hfd'
  change (fderiv ℝ (CKN.spatialDeriv newtonianKernel i) z)
      (CKN.basisVec j) = _
  rw [happly]
  simp [smul_eq_mul, CKN.basisVec_apply]
  by_cases hij : i = j
  · subst j
    simp
    ring
  · simp [hij]

theorem hasFDerivAt_newtonianKernel_spatialDeriv_formula
    {z : Vec3} (hz : z ≠ 0) (i : Fin 3) :
    HasFDerivAt (CKN.spatialDeriv newtonianKernel i)
      ((-(4 * Real.pi)⁻¹) •
        ((z i) • ((-(3 : ℝ) / 2 * q z ^ (-(3 : ℝ) / 2 - 1)) •
          (∑ k : Fin 3, (2 * z k) •
            (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ))) +
          q z ^ (-(3 : ℝ) / 2) •
            (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ))) z := by
  have hpow := (hasFDerivAt_q z).rpow_const (p := -(3 : ℝ) / 2)
    (Or.inl (q_pos hz).ne')
  have hi := (hasFDerivAt_apply (𝕜 := ℝ) i z).mul hpow
  have hc := hi.const_mul (-(4 * Real.pi)⁻¹)
  have hformula : HasFDerivAt (fun y : Vec3 =>
      -(4 * Real.pi)⁻¹ * y i * q y ^ (-(3 : ℝ) / 2))
      ((-(4 * Real.pi)⁻¹) •
        ((z i) • ((-(3 : ℝ) / 2 * q z ^ (-(3 : ℝ) / 2 - 1)) •
          (∑ k : Fin 3, (2 * z k) •
            (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ))) +
          q z ^ (-(3 : ℝ) / 2) •
            (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ))) z := by
    convert hc using 1
    · ext y
      simp
      ring
  have hnonzero : ∀ᶠ w in 𝓝 z, w ≠ 0 :=
    isOpen_compl_singleton.mem_nhds hz
  have hfun : CKN.spatialDeriv newtonianKernel i =ᶠ[𝓝 z]
      (fun y : Vec3 =>
        -(4 * Real.pi)⁻¹ * y i * q y ^ (-(3 : ℝ) / 2)) := by
    filter_upwards [hnonzero] with w hw
    rw [newtonianKernel_spatialDeriv_formula hw i]
  exact hformula.congr_of_eventuallyEq hfun

theorem newtonianKernel_spatialDeriv_continuousAt {z : Vec3} (hz : z ≠ 0)
    (i : Fin 3) : ContinuousAt (CKN.spatialDeriv newtonianKernel i) z := by
  have hfd := (contDiffAt_newtonianKernel hz).continuousAt_fderiv (by norm_num)
  change ContinuousAt (fun w : Vec3 => (fderiv ℝ newtonianKernel w)
    (CKN.basisVec i)) z
  exact hfd.clm_apply continuousAt_const

theorem newtonianKernel_spatialDeriv_second_continuousAt
    {z : Vec3} (hz : z ≠ 0) (i j : Fin 3) :
    ContinuousAt (CKN.spatialDeriv (CKN.spatialDeriv newtonianKernel i) j) z := by
  have hfd : ContDiffAt ℝ (1 : ℕ)
      (fderiv ℝ newtonianKernel) z :=
    (contDiffAt_newtonianKernel hz).fderiv_right (m := (1 : ℕ))
      (by norm_num)
  have hi : ContDiffAt ℝ (1 : ℕ)
      (CKN.spatialDeriv newtonianKernel i) z := by
    change ContDiffAt ℝ (1 : ℕ)
      (fun w : Vec3 => (fderiv ℝ newtonianKernel w)
        (CKN.basisVec i)) z
    exact hfd.clm_apply contDiffAt_const
  have hj := hi.continuousAt_fderiv (by norm_num)
  change ContinuousAt (fun w : Vec3 =>
    (fderiv ℝ (CKN.spatialDeriv newtonianKernel i) w)
      (CKN.basisVec j)) z
  exact hj.clm_apply continuousAt_const

end CKN.Foundation.Heat
