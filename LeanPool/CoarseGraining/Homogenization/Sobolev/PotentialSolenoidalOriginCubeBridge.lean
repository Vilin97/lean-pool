/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidal
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.OriginCubeBridge
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # Potential Solenoidal Origin Cube Bridge -/

namespace Homogenization

private theorem volume_openCubeSet_originCube_lt_top_bridge {d : ℕ} (n : ℤ) :
    MeasureTheory.volume (openCubeSet (originCube d n)) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hzero : (MeasureTheory.volume (openCubeSet (originCube d n))).toReal = 0 := by
    simp [htop]
  rw [volume_openCubeSet_toReal] at hzero
  exact (ne_of_gt (cubeVolume_pos (originCube d n))) hzero

theorem isPotentialOn_cubeSet_originCube_of_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {f : Vec d → Vec d}
    (hf : IsPotentialOn (openCubeSet (originCube d n)) f) :
    IsPotentialOn (cubeSet (originCube d n)) f := by
  rcases hf with ⟨u, rfl⟩
  exact (u.toCubeSetOriginCube).isPotentialOn

theorem isPotentialOn_openCubeSet_originCube_of_cubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {f : Vec d → Vec d}
    (hf : IsPotentialOn (cubeSet (originCube d n)) f) :
    IsPotentialOn (openCubeSet (originCube d n)) f := by
  rcases hf with ⟨u, rfl⟩
  exact (u.restrict (isOpen_openCubeSet (originCube d n)) (openCubeSet_subset_cubeSet _)).isPotentialOn

theorem isPotentialOn_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {f : Vec d → Vec d} :
    IsPotentialOn (cubeSet (originCube d n)) f ↔
      IsPotentialOn (openCubeSet (originCube d n)) f := by
  constructor
  · exact isPotentialOn_openCubeSet_originCube_of_cubeSet
  · exact isPotentialOn_cubeSet_originCube_of_openCubeSet

theorem isPotentialZeroTraceOn_cubeSet_originCube_of_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn (openCubeSet (originCube d n)) f) :
    IsPotentialZeroTraceOn (cubeSet (originCube d n)) f := by
  rcases hf with ⟨u, rfl⟩
  exact (u.toCubeSetOriginCube).isPotentialZeroTraceOn

theorem isPotentialZeroTraceOn_openCubeSet_originCube_of_cubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn (cubeSet (originCube d n)) f) :
    IsPotentialZeroTraceOn (openCubeSet (originCube d n)) f := by
  rcases hf with ⟨u, rfl⟩
  exact (u.toOpenCubeSetOriginCube).isPotentialZeroTraceOn

theorem isPotentialZeroTraceOn_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {f : Vec d → Vec d} :
    IsPotentialZeroTraceOn (cubeSet (originCube d n)) f ↔
      IsPotentialZeroTraceOn (openCubeSet (originCube d n)) f := by
  constructor
  · exact isPotentialZeroTraceOn_openCubeSet_originCube_of_cubeSet
  · exact isPotentialZeroTraceOn_cubeSet_originCube_of_openCubeSet

theorem isSolenoidalOn_cubeSet_originCube_of_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {g : Vec d → Vec d}
    (hg : IsSolenoidalOn (openCubeSet (originCube d n)) g) :
    IsSolenoidalOn (cubeSet (originCube d n)) g := by
  intro φ
  have hopen := hg (φ.toOpenCubeSetOriginCube)
  have hset :
      ∫ x in cubeSet (originCube d n),
          vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet (originCube d n),
          vecDot (g x) ((φ.toOpenCubeSetOriginCube.toH1Function.grad) x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube
        (d := d) (n := n)
        (f := fun x => vecDot (g x) (φ.toH1Function.grad x)))
  rw [hset]
  simpa using hopen

theorem isSolenoidalOn_openCubeSet_originCube_of_cubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {g : Vec d → Vec d}
    (hg : IsSolenoidalOn (cubeSet (originCube d n)) g) :
    IsSolenoidalOn (openCubeSet (originCube d n)) g := by
  intro φ
  have hcube := hg (φ.toCubeSetOriginCube)
  have hset :
      ∫ x in cubeSet (originCube d n),
          vecDot (g x) ((φ.toCubeSetOriginCube.toH1Function.grad) x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet (originCube d n),
          vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
    simpa using
      (setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube
        (d := d) (n := n)
        (f := fun x => vecDot (g x) ((φ.toCubeSetOriginCube.toH1Function.grad) x)))
  rw [hset] at hcube
  simpa using hcube

theorem isSolenoidalOn_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {g : Vec d → Vec d} :
    IsSolenoidalOn (cubeSet (originCube d n)) g ↔
      IsSolenoidalOn (openCubeSet (originCube d n)) g := by
  constructor
  · exact isSolenoidalOn_openCubeSet_originCube_of_cubeSet
  · exact isSolenoidalOn_cubeSet_originCube_of_openCubeSet

theorem isSolenoidalZeroNormalTraceOn_cubeSet_originCube_of_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {g : Vec d → Vec d}
    (hg : IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d n)) g) :
    IsSolenoidalZeroNormalTraceOn (cubeSet (originCube d n)) g := by
  intro φ
  let φopen : H1Function (openCubeSet (originCube d n)) :=
    φ.restrict (isOpen_openCubeSet (originCube d n)) (openCubeSet_subset_cubeSet _)
  have hopen := hg φopen
  have hset :
      ∫ x in cubeSet (originCube d n), vecDot (g x) (φ.grad x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet (originCube d n), vecDot (g x) (φopen.grad x) ∂MeasureTheory.volume := by
    simpa [φopen, H1Function.restrict] using
      (setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube
        (d := d) (n := n)
        (f := fun x => vecDot (g x) (φ.grad x)))
  rw [hset]
  simpa using hopen

theorem isSolenoidalZeroNormalTraceOn_openCubeSet_originCube_of_cubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {g : Vec d → Vec d}
    (hg : IsSolenoidalZeroNormalTraceOn (cubeSet (originCube d n)) g) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d n)) g := by
  intro φ
  have hcube := hg (φ.toCubeSetOriginCube)
  have hset :
      ∫ x in cubeSet (originCube d n),
          vecDot (g x) ((φ.toCubeSetOriginCube.grad) x) ∂MeasureTheory.volume =
        ∫ x in openCubeSet (originCube d n),
          vecDot (g x) (φ.grad x) ∂MeasureTheory.volume := by
    simpa using!
      (setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube
        (d := d) (n := n)
        (f := fun x => vecDot (g x) ((φ.toCubeSetOriginCube.grad) x)))
  rw [hset] at hcube
  simpa using hcube

theorem isSolenoidalZeroNormalTraceOn_cubeSet_originCube_iff_openCubeSet
    {d : ℕ} [NeZero d] {n : ℤ} {g : Vec d → Vec d} :
    IsSolenoidalZeroNormalTraceOn (cubeSet (originCube d n)) g ↔
      IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d n)) g := by
  constructor
  · exact isSolenoidalZeroNormalTraceOn_openCubeSet_originCube_of_cubeSet
  · exact isSolenoidalZeroNormalTraceOn_cubeSet_originCube_of_openCubeSet

theorem IsPotentialZeroTraceOn.integral_eq_zero_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn (openCubeSet (originCube d n)) f) :
    (fun i => ∫ x in openCubeSet (originCube d n), f x i ∂MeasureTheory.volume) = 0 := by
  rcases hf with ⟨u, rfl⟩
  ext i
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let μ := MeasureTheory.volume.restrict U
  have : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_openCubeSet_originCube_lt_top_bridge (d := d) n⟩
  have : MeasureTheory.IsFiniteMeasure μ := inferInstance
  let D : ℕ → Vec d → ℝ := fun m x => (fderiv ℝ (u.approx m) x) (basisVec i)
  have hD_integrable : ∀ m, MeasureTheory.Integrable (D m) MeasureTheory.volume := by
    intro m
    have hcont : Continuous (D m) := by
      simpa [D] using
        ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply continuous_const
    have hcomp : HasCompactSupport (D m) := by
      simpa [D] using (u.approx_hasCompactSupport m).fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact hcont.integrable_of_hasCompactSupport hcomp
  have hD_integrable_restrict :
      ∀ᶠ m in Filter.atTop, MeasureTheory.Integrable (D m) μ := by
    refine Filter.Eventually.of_forall ?_
    intro m
    simpa [MeasureTheory.IntegrableOn, μ] using (hD_integrable m).integrableOn (s := U)
  have hD_zero : ∀ m, ∫ x, D m x ∂μ = 0 := by
    intro m
    have happrox_integrable : MeasureTheory.Integrable (u.approx m) MeasureTheory.volume := by
      exact (u.approx_smooth m).continuous.integrable_of_hasCompactSupport
        (u.approx_hasCompactSupport m)
    have hfull :
        ∫ x, D m x ∂MeasureTheory.volume = 0 := by
      have h :=
        integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
          (μ := MeasureTheory.volume)
          (f := fun _ : Vec d => (1 : ℝ))
          (g := u.approx m)
          (v := basisVec i)
          (by simp)
          (by simpa [D] using hD_integrable m)
          (by simpa using happrox_integrable)
          (fun x _ => differentiableAt_const (c := (1 : ℝ)))
          (fun x _ => ((u.approx_smooth m).differentiable (by simp)).differentiableAt)
      simpa [D] using h
    have hzero_off : ∀ x, x ∉ U → D m x = 0 := by
      intro x hx
      have hnot : x ∉ tsupport (u.approx m) := fun hx' => hx (u.approx_support_subset m hx')
      have hfderiv : fderiv ℝ (u.approx m) x = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot
      simpa [D] using congrArg (fun L => L (basisVec i)) hfderiv
    have hset :
        ∫ x in U, D m x ∂MeasureTheory.volume =
          ∫ x, D m x ∂MeasureTheory.volume :=
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero_off
    simpa [μ] using hset.trans hfull
  have hfi : MeasureTheory.Integrable (fun x => u.toH1Function.grad x i) μ := by
    simpa [μ] using
      (u.toH1Function.gradMemL2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hDiffMeas :
      ∀ m, MeasureTheory.AEStronglyMeasurable (fun x => D m x - u.toH1Function.grad x i) μ := by
    intro m
    have hDm :
        MeasureTheory.AEStronglyMeasurable (D m) μ := by
      have hInt : MeasureTheory.Integrable (D m) μ := by
        simpa [MeasureTheory.IntegrableOn, μ] using (hD_integrable m).integrableOn (s := U)
      exact hInt.aestronglyMeasurable
    exact hDm.sub (u.toH1Function.gradMemL2 i).aestronglyMeasurable
  have hL1_bound :
      ∀ m,
        MeasureTheory.eLpNorm (fun x => D m x - u.toH1Function.grad x i) 1 μ ≤
          MeasureTheory.eLpNorm (fun x => D m x - u.toH1Function.grad x i) 2 μ *
            μ Set.univ ^ ((1 : ℝ) - 1 / 2) := by
    intro m
    simpa using
      (MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ)
        (f := fun x => D m x - u.toH1Function.grad x i)
        (p := (1 : ENNReal))
        (q := (2 : ENNReal))
        (by norm_num)
        (hDiffMeas m))
  have hConst_ne_top : μ Set.univ ^ ((1 : ℝ) - 1 / 2) ≠ ⊤ := by
    refine (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_).ne
    simpa [μ, U] using (MeasureTheory.measure_lt_top μ Set.univ).ne
  have hL1 :
      Filter.Tendsto
        (fun m => MeasureTheory.eLpNorm (fun x => D m x - u.toH1Function.grad x i) 1 μ)
        Filter.atTop (nhds 0) := by
    have hscaled :
        Filter.Tendsto
          (fun m =>
            MeasureTheory.eLpNorm (fun x => D m x - u.toH1Function.grad x i) 2 μ *
              μ Set.univ ^ ((1 : ℝ) - 1 / 2))
          Filter.atTop
          (nhds (0 * (μ Set.univ ^ ((1 : ℝ) - 1 / 2)))) := by
      exact ENNReal.Tendsto.mul_const (u.tendsto_approx_grad i) (Or.inr hConst_ne_top)
    have hscaled0 :
        Filter.Tendsto
          (fun m =>
            MeasureTheory.eLpNorm (fun x => D m x - u.toH1Function.grad x i) 2 μ *
              μ Set.univ ^ ((1 : ℝ) - 1 / 2))
          Filter.atTop (nhds 0) := by
      simpa [zero_mul] using hscaled
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hscaled0
      (fun _ => zero_le)
      hL1_bound
  have hconv :
      Filter.Tendsto
        (fun m => ∫ x, D m x ∂μ)
        Filter.atTop
        (nhds (∫ x, u.toH1Function.grad x i ∂μ)) :=
    MeasureTheory.tendsto_integral_of_L1'
      (μ := μ)
      (f := fun x => u.toH1Function.grad x i)
      hfi.aestronglyMeasurable
      hD_integrable_restrict
      hL1
  have hEq : (fun m => ∫ x, D m x ∂μ) = fun _ => (0 : ℝ) := by
    funext m
    exact hD_zero m
  have hzero_tendsto :
      Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
        (nhds (∫ x, u.toH1Function.grad x i ∂μ)) := by
    simpa [hEq] using hconv
  have hIntegralZero : ∫ x, u.toH1Function.grad x i ∂μ = 0 :=
    tendsto_nhds_unique hzero_tendsto tendsto_const_nhds
  change ∫ x in U, u.toH1Function.grad x i ∂MeasureTheory.volume = 0
  simpa [μ, U] using hIntegralZero

theorem IsPotentialZeroTraceOn.integral_eq_zero_cubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {f : Vec d → Vec d}
    (hf : IsPotentialZeroTraceOn (cubeSet (originCube d n)) f) :
    (fun i => ∫ x in cubeSet (originCube d n), f x i ∂MeasureTheory.volume) = 0 := by
  have hf_open :
      IsPotentialZeroTraceOn (openCubeSet (originCube d n)) f :=
    (isPotentialZeroTraceOn_cubeSet_originCube_iff_openCubeSet
      (d := d) (n := n) (f := f)).mp hf
  ext i
  calc
    ∫ x in cubeSet (originCube d n), f x i ∂MeasureTheory.volume =
        ∫ x in openCubeSet (originCube d n), f x i ∂MeasureTheory.volume := by
          simpa using
            (setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube
              (d := d) (n := n) (f := fun x => f x i))
    _ = 0 := by
      exact congrFun
        (IsPotentialZeroTraceOn.integral_eq_zero_openCubeSet_originCube
          (d := d) (n := n) (f := f) hf_open) i

theorem IsSolenoidalZeroNormalTraceOn.integral_eq_zero_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {g : Vec d → Vec d}
    (hg : IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d n)) g) :
    (fun i => ∫ x in openCubeSet (originCube d n), g x i ∂MeasureTheory.volume) = 0 := by
  ext i
  have htest :
      ∫ x in openCubeSet (originCube d n), vecDot (g x) (basisVec i) ∂MeasureTheory.volume = 0 := by
    simpa [H1Function.coordOnOpenCubeSetOriginCube] using
      hg (H1Function.coordOnOpenCubeSetOriginCube (d := d) (n := n) i)
  simpa [vecDot, basisVec_apply] using htest

theorem IsSolenoidalZeroNormalTraceOn.integral_eq_zero_cubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {g : Vec d → Vec d}
    (hg : IsSolenoidalZeroNormalTraceOn (cubeSet (originCube d n)) g) :
    (fun i => ∫ x in cubeSet (originCube d n), g x i ∂MeasureTheory.volume) = 0 := by
  have hg_open :
      IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d n)) g :=
    (isSolenoidalZeroNormalTraceOn_cubeSet_originCube_iff_openCubeSet
      (d := d) (n := n) (g := g)).mp hg
  ext i
  calc
    ∫ x in cubeSet (originCube d n), g x i ∂MeasureTheory.volume =
        ∫ x in openCubeSet (originCube d n), g x i ∂MeasureTheory.volume := by
          simpa using
            (setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube
              (d := d) (n := n) (f := fun x => g x i))
    _ = 0 := by
      exact congrFun
        (IsSolenoidalZeroNormalTraceOn.integral_eq_zero_openCubeSet_originCube
          (d := d) (n := n) (g := g) hg_open) i

end Homogenization
