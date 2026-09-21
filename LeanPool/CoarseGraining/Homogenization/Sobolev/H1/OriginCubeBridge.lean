/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.BasicLemmas
import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeBoundaryPush
import LeanPool.CoarseGraining.Homogenization.Geometry.OriginCubeMeasureBridge
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Origin Cube Bridge -/

namespace Homogenization

open scoped Topology

private def diagonalShift {d : ℕ} (ε : ℝ) : Vec d :=
  fun _ => ε

private theorem volume_cubeSet_originCube_lt_top {d : ℕ} (n : ℤ) :
    MeasureTheory.volume (cubeSet (originCube d n)) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hzero : (MeasureTheory.volume (cubeSet (originCube d n))).toReal = 0 := by
    simp [htop]
  rw [volume_cubeSet_toReal] at hzero
  exact (ne_of_gt (cubeVolume_pos (originCube d n))) hzero

private theorem volume_openCubeSet_originCube_lt_top {d : ℕ} (n : ℤ) :
    MeasureTheory.volume (openCubeSet (originCube d n)) < ⊤ := by
  exact lt_of_le_of_lt
    (MeasureTheory.measure_mono (openCubeSet_subset_cubeSet (originCube d n)))
    (volume_cubeSet_originCube_lt_top (d := d) n)

private theorem dist_sub_diagonalShift_le {d : ℕ} (x : Vec d) {ε : ℝ} (hε : 0 ≤ ε) :
    dist (x - diagonalShift (d := d) ε) x ≤ ε := by
  rw [dist_pi_le_iff hε]
  intro i
  have hcoord : ((x - diagonalShift (d := d) ε) i) - x i = -ε := by
    simp [diagonalShift]
  rw [Real.dist_eq, hcoord, abs_neg, abs_of_nonneg hε]

private theorem exists_abs_bound_of_continuous_of_hasCompactSupport {d : ℕ} {f : Vec d → ℝ}
    (hf_cont : Continuous f) (hf_compact : HasCompactSupport f) :
    ∃ C : ℝ, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf_compact.exists_bound_of_continuous hf_cont
  refine ⟨C, ?_⟩
  intro x
  simpa [Real.norm_eq_abs] using hC x

private theorem tendsto_precomp_sub_diagonalShift {d : ℕ} (x : Vec d) (ε₀ : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))
      Filter.atTop (𝓝 x) := by
  have hdenCast : Filter.Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))) Filter.atTop Filter.atTop := by
    exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 2)
  have hden : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 2) Filter.atTop Filter.atTop := by
    convert hdenCast using 1
    ext n
    simp [Nat.cast_add]
  have hε : Filter.Tendsto (fun n : ℕ => ε₀ / ((n : ℝ) + 2)) Filter.atTop (𝓝 0) := by
    have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) Filter.atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    simpa [div_eq_mul_inv, mul_comm] using hinv.const_mul ε₀
  rw [tendsto_pi_nhds]
  intro i
  simpa [diagonalShift] using tendsto_const_nhds.sub hε

private theorem tendsto_setIntegral_mul_precomp_subRight_of_memL2On
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U)]
    {f ψ : Vec d → ℝ} (hfL2 : MemL2On U f) (hψ_cont : Continuous ψ)
    (hψ_compact : HasCompactSupport ψ) (ε₀ : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ x in U, f x * ψ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))
          ∂MeasureTheory.volume)
      Filter.atTop
      (𝓝 (∫ x in U, f x * ψ x ∂MeasureTheory.volume)) := by
  let μ := MeasureTheory.volume.restrict U
  have hf_int : MeasureTheory.Integrable f μ := by
    simpa [MemL2On, μ] using (hfL2.integrable (by norm_num : (1 : ENNReal) ≤ 2))
  obtain ⟨C, hC⟩ := exists_abs_bound_of_continuous_of_hasCompactSupport hψ_cont hψ_compact
  have hbound_int : MeasureTheory.Integrable (fun x : Vec d => C * |f x|) μ := by
    simpa [Real.norm_eq_abs, mul_comm, μ] using (hf_int.norm.mul_const C)
  have hmeas :
      ∀ n : ℕ,
        MeasureTheory.AEStronglyMeasurable
          (fun x : Vec d => f x * ψ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))) μ := by
    intro n
    have hshift_cont :
        Continuous (fun x : Vec d => ψ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))) :=
      hψ_cont.comp (continuous_id.sub continuous_const)
    exact hfL2.aestronglyMeasurable.mul hshift_cont.aestronglyMeasurable
  have hbound :
      ∀ n : ℕ,
        ∀ᵐ x ∂μ,
          ‖f x * ψ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))‖ ≤ C * |f x| := by
    intro n
    filter_upwards with x
    have hψx : |ψ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))| ≤ C :=
      hC (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [abs_nonneg (f x), abs_nonneg (ψ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2))))]
  have hlim :
      ∀ᵐ x ∂μ,
        Filter.Tendsto
          (fun n : ℕ => f x * ψ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2))))
          Filter.atTop (𝓝 (f x * ψ x)) := by
    refine Filter.Eventually.of_forall ?_
    intro x
    have hψ_lim :
        Filter.Tendsto
          (fun n : ℕ => ψ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2))))
          Filter.atTop (𝓝 (ψ x)) :=
      hψ_cont.continuousAt.tendsto.comp (tendsto_precomp_sub_diagonalShift (d := d) x ε₀)
    simpa using hψ_lim.const_mul (f x)
  simpa [μ] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (μ := μ) (bound := fun x : Vec d => C * |f x|) hmeas hbound_int hbound hlim)

namespace H1Function

/--
Promote an `H¹` witness on the open centered cube to an `H¹` witness on the
corresponding half-open centered cube by shifting smooth compactly supported
tests inward and passing to the limit.
-/
noncomputable def toCubeSetOriginCube {d : ℕ} [NeZero d] {n : ℤ}
    (u : H1Function (openCubeSet (originCube d n))) :
    H1Function (cubeSet (originCube d n)) := by
  let Uo : Set (Vec d) := openCubeSet (originCube d n)
  let Uc : Set (Vec d) := cubeSet (originCube d n)
  haveI : Fact (MeasureTheory.volume Uc < ⊤) := ⟨volume_cubeSet_originCube_lt_top (d := d) n⟩
  haveI : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict Uc) := inferInstance
  have hu_memL2 : MemL2On Uc u.toFun := by
    simpa [MemL2On, Uo, Uc,
      volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube (d := d) n]
      using u.memL2
  have hu_gradMemL2 : GradMemL2On Uc u.grad := by
    intro i
    simpa [MemL2On, Uo, Uc,
      volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube (d := d) n]
      using u.gradMemL2 i
  refine
    { toFun := u.toFun
      grad := u.grad
      memL2 := hu_memL2
      gradMemL2 := hu_gradMemL2
      hasWeakGradient := ?_ }
  intro i φ hφ_smooth hφ_compact hφ_sub
  rcases HasCompactSupport.exists_pos_forall_precomp_subRight_tsupport_subset_openCubeSet_originCube
      (d := d) (n := n) (φ := φ) hφ_compact hφ_sub with ⟨ε₀, hε₀pos, hpush⟩
  let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
  let ψn : ℕ → Vec d → ℝ :=
    fun n x => φ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))
  have hφ_cont : Continuous φ := (hφ_smooth.differentiable (by simp)).continuous
  have hdφ_cont : Continuous dφ := by
    simpa [dφ] using
      (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ_compact : HasCompactSupport dφ := by
    simpa [dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hψn_smooth : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) (ψn n) := by
    intro n
    have hshift_smooth :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun x : Vec d => x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2))) := by
      simpa [diagonalShift] using contDiff_id.sub contDiff_const
    exact hφ_smooth.comp hshift_smooth
  have hψn_compact : ∀ n : ℕ, HasCompactSupport (ψn n) := by
    intro n
    simpa [ψn] using!
      hφ_compact.comp_homeomorph
        (Homeomorph.subRight (diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2))))
  have hψn_sub : ∀ n : ℕ, tsupport (ψn n) ⊆ Uo := by
    intro n
    have hεpos : 0 < ε₀ / ((n : ℝ) + 2) := by
      have hden_pos : 0 < ((n : ℝ) + 2) := by positivity
      exact div_pos hε₀pos hden_pos
    have hεlt : ε₀ / ((n : ℝ) + 2) < ε₀ := by
      have hn_nonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
      have hden_pos : 0 < ((n : ℝ) + 2) := by nlinarith
      have hmul : ε₀ < ε₀ * ((n : ℝ) + 2) := by nlinarith [hε₀pos, hn_nonneg]
      exact (div_lt_iff₀ hden_pos).2 hmul
    exact hpush hεpos hεlt
  have hshiftEq :
      ∀ m : ℕ,
        ∫ x in Uc, u.toFun x * dφ (x - diagonalShift (d := d) (ε₀ / ((m : ℝ) + 2)))
            ∂MeasureTheory.volume =
          -∫ x in Uc, u.grad x i * φ (x - diagonalShift (d := d) (ε₀ / ((m : ℝ) + 2)))
            ∂MeasureTheory.volume := by
    intro m
    have hweakOpen := u.hasWeakGradient i (ψn m) (hψn_smooth m) (hψn_compact m) (hψn_sub m)
    have hleftSet :
        ∫ x in Uc, u.toFun x * dφ (x - diagonalShift (d := d) (ε₀ / ((m : ℝ) + 2)))
            ∂MeasureTheory.volume =
          ∫ x in Uo, u.toFun x * dφ (x - diagonalShift (d := d) (ε₀ / ((m : ℝ) + 2)))
            ∂MeasureTheory.volume := by
      simpa [Uo, Uc] using
        (setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube
          (d := d) (n := n)
          (f := fun x =>
            u.toFun x * dφ (x - diagonalShift (d := d) (ε₀ / ((m : ℝ) + 2)))))
    have hrightSet :
        ∫ x in Uc, u.grad x i * φ (x - diagonalShift (d := d) (ε₀ / ((m : ℝ) + 2)))
            ∂MeasureTheory.volume =
          ∫ x in Uo, u.grad x i * φ (x - diagonalShift (d := d) (ε₀ / ((m : ℝ) + 2)))
            ∂MeasureTheory.volume := by
      simpa [Uo, Uc] using
        (setIntegral_cubeSet_originCube_eq_setIntegral_openCubeSet_originCube
          (d := d) (n := n)
          (f := fun x =>
            u.grad x i * φ (x - diagonalShift (d := d) (ε₀ / ((m : ℝ) + 2)))))
    rw [hleftSet, hrightSet]
    simpa [Uo, Uc, dφ, ψn, diagonalShift, fderiv_comp_sub] using hweakOpen
  have hleft :
      Filter.Tendsto
        (fun n : ℕ =>
          ∫ x in Uc, u.toFun x * dφ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))
            ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝 (∫ x in Uc, u.toFun x * dφ x ∂MeasureTheory.volume)) :=
    tendsto_setIntegral_mul_precomp_subRight_of_memL2On
      (U := Uc) (f := u.toFun) (ψ := dφ) hu_memL2 hdφ_cont hdφ_compact ε₀
  have hright :
      Filter.Tendsto
        (fun n : ℕ =>
          ∫ x in Uc, u.grad x i * φ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))
            ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝 (∫ x in Uc, u.grad x i * φ x ∂MeasureTheory.volume)) :=
    tendsto_setIntegral_mul_precomp_subRight_of_memL2On
      (U := Uc) (f := fun x => u.grad x i) (ψ := φ) (hu_gradMemL2 i) hφ_cont hφ_compact ε₀
  have hrightNeg :
      Filter.Tendsto
        (fun n : ℕ =>
          -∫ x in Uc, u.grad x i * φ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))
            ∂MeasureTheory.volume)
        Filter.atTop
        (𝓝 (-∫ x in Uc, u.grad x i * φ x ∂MeasureTheory.volume)) := by
    simpa using hright.neg
  have hsame :
      ∀ n : ℕ,
        -∫ x in Uc, u.grad x i * φ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))
            ∂MeasureTheory.volume =
          (∫ x in Uc, u.toFun x * dφ (x - diagonalShift (d := d) (ε₀ / ((n : ℝ) + 2)))
            ∂MeasureTheory.volume) := by
    intro n
    exact (hshiftEq n).symm
  have hfinal :
      ∫ x in Uc, u.toFun x * dφ x ∂MeasureTheory.volume =
        -∫ x in Uc, u.grad x i * φ x ∂MeasureTheory.volume :=
    tendsto_nhds_unique hleft
      (Filter.Tendsto.congr' (Filter.Eventually.of_forall hsame) hrightNeg)
  simpa [dφ, Uc] using hfinal

theorem exists_toCubeSetOriginCube {d : ℕ} [NeZero d] {n : ℤ}
    (u : H1Function (openCubeSet (originCube d n))) :
    ∃ v : H1Function (cubeSet (originCube d n)), v.toFun = u.toFun ∧ v.grad = u.grad := by
  refine ⟨u.toCubeSetOriginCube, rfl, rfl⟩

/--
The coordinate projection `x ↦ x i` as an `H¹` function on the open centered cube,
with constant gradient `basisVec i`.
-/
noncomputable def coordOnOpenCubeSetOriginCube {d : ℕ} {n : ℤ} (i : Fin d) :
    H1Function (openCubeSet (originCube d n)) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  haveI : Fact (MeasureTheory.volume U < ⊤) := ⟨volume_openCubeSet_originCube_lt_top (d := d) n⟩
  haveI : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict U) := inferInstance
  refine
    { toFun := fun x => x i
      grad := fun _ => basisVec i
      memL2 := ?_
      gradMemL2 := ?_
      hasWeakGradient := ?_ }
  · let C : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ n
    refine MeasureTheory.MemLp.of_bound
      (μ := MeasureTheory.volume.restrict U)
      ((continuous_apply i).aestronglyMeasurable)
      C ?_
    rw [MeasureTheory.ae_restrict_iff' (measurableSet_openCubeSet (originCube d n))]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    rcases (mem_openCubeSet_originCube_iff.mp hx) i with ⟨hlo, hhi⟩
    have hlo' : -C < x i := by
      simpa [C, neg_mul] using hlo
    have habs : |x i| < C := by
      rw [abs_lt]
      exact ⟨hlo', hhi⟩
    exact le_of_lt (by simpa [Real.norm_eq_abs] using habs)
  · intro j
    simpa [U] using
      (MeasureTheory.memLp_const
        (μ := MeasureTheory.volume.restrict U)
        (p := (2 : ENNReal))
        (c := basisVec i j))
  · intro j
    convert
      (HasWeakPartialDerivOn.of_contDiff
        (U := U)
        (i := j)
        (f := fun x : Vec d => x i)
        (hf := contDiff_apply (𝕜 := ℝ) (n := (1 : ℕ∞)) (E := ℝ) i)) using 2
    rename_i x
    let π : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
    have hproj :
        HasFDerivAt (fun y : Vec d => y i) π x := by
      simpa [π] using! π.hasFDerivAt (x := x)
    have hlin : fderiv ℝ (fun y : Vec d => y i) x = π := hproj.fderiv
    simpa [π, basisVec_apply, eq_comm] using
      (congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec j)) hlin).symm

end H1Function

namespace H10Function

/--
Promote an `H¹₀` witness on the open centered cube to an `H¹₀` witness on the
corresponding half-open centered cube.
-/
noncomputable def toCubeSetOriginCube {d : ℕ} [NeZero d] {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) :
    H10Function (cubeSet (originCube d n)) where
  toH1Function := u.toH1Function.toCubeSetOriginCube
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_support_subset := by
    intro m
    exact (u.approx_support_subset m).trans (openCubeSet_subset_cubeSet (originCube d n))
  tendsto_approx := by
    simpa
      [volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube (d := d) n]
      using! u.tendsto_approx
  tendsto_approx_grad := by
    intro i
    simpa
      [volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube (d := d) n]
      using! u.tendsto_approx_grad i

@[simp] theorem toCubeSetOriginCube_toH1Function_toFun {d : ℕ} [NeZero d] {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) :
    (u.toCubeSetOriginCube.toH1Function.toFun) = u.toH1Function.toFun :=
  rfl

@[simp] theorem toCubeSetOriginCube_toH1Function_grad {d : ℕ} [NeZero d] {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) :
    (u.toCubeSetOriginCube.toH1Function.grad) = u.toH1Function.grad :=
  rfl

/--
Restrict an `H¹₀` witness on the half-open centered cube to the corresponding
open centered cube by pushing each smooth approximant slightly inward while
keeping the shift small enough that the `L²` error still vanishes.
-/
noncomputable def toOpenCubeSetOriginCube {d : ℕ} [NeZero d] {n : ℤ}
    (u : H10Function (cubeSet (originCube d n))) :
    H10Function (openCubeSet (originCube d n)) := by
  let Uc : Set (Vec d) := cubeSet (originCube d n)
  let Uo : Set (Vec d) := openCubeSet (originCube d n)
  have hUo_open : IsOpen Uo := isOpen_openCubeSet (originCube d n)
  let v : H1Function Uo := u.toH1Function.restrict hUo_open (openCubeSet_subset_cubeSet _)
  let μo := MeasureTheory.volume.restrict Uo
  haveI : Fact (MeasureTheory.volume Uo < ⊤) := ⟨volume_openCubeSet_originCube_lt_top (d := d) n⟩
  haveI : MeasureTheory.IsFiniteMeasure μo := inferInstance
  have hshiftData :
      ∀ m : ℕ,
        ∃ ε : ℝ, 0 < ε ∧
          tsupport (fun x : Vec d => u.approx m (x - diagonalShift (d := d) ε)) ⊆ Uo ∧
          (∀ x : Vec d,
            dist (u.approx m (x - diagonalShift (d := d) ε)) (u.approx m x) ≤
              1 / ((m : ℝ) + 1)) ∧
          (∀ i : Fin d, ∀ x : Vec d,
            dist ((fderiv ℝ (u.approx m) (x - diagonalShift (d := d) ε)) (basisVec i))
              ((fderiv ℝ (u.approx m) x) (basisVec i)) ≤ 1 / ((m : ℝ) + 1)) := by
    intro m
    let η : ℝ := 1 / ((m : ℝ) + 1)
    have hη : 0 < η := by
      dsimp [η]
      positivity
    have happrox_cont : Continuous (u.approx m) :=
      (u.approx_smooth m).differentiable (by simp) |>.continuous
    have happrox_uc : UniformContinuous (u.approx m) :=
      (u.approx_hasCompactSupport m).uniformContinuous_of_continuous happrox_cont
    have hgrad_uc :
        ∀ i : Fin d,
          UniformContinuous (fun x : Vec d => (fderiv ℝ (u.approx m) x) (basisVec i)) := by
      intro i
      have hcont :
          Continuous (fun x : Vec d => (fderiv ℝ (u.approx m) x) (basisVec i)) := by
        simpa using
          ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply continuous_const
      have hcompact :
          HasCompactSupport (fun x : Vec d => (fderiv ℝ (u.approx m) x) (basisVec i)) := by
        simpa using (u.approx_hasCompactSupport m).fderiv_apply (𝕜 := ℝ) (basisVec i)
      exact hcompact.uniformContinuous_of_continuous hcont
    obtain ⟨εpush, hεpush_pos, hpush⟩ :=
      HasCompactSupport.exists_pos_forall_precomp_subRight_tsupport_subset_openCubeSet_originCube
        (d := d) (n := n) (φ := u.approx m) (u.approx_hasCompactSupport m) (u.approx_support_subset m)
    obtain ⟨δfun, hδfun_pos, hδfun⟩ :=
      (Metric.uniformContinuous_iff_le.mp happrox_uc) η hη
    let δgrad : Fin d → ℝ := fun i =>
      Classical.choose ((Metric.uniformContinuous_iff_le.mp (hgrad_uc i)) η hη)
    have hδgrad_pos : ∀ i : Fin d, 0 < δgrad i := by
      intro i
      exact (Classical.choose_spec ((Metric.uniformContinuous_iff_le.mp (hgrad_uc i)) η hη)).1
    have hδgrad :
        ∀ i : Fin d, ∀ {x y : Vec d}, dist x y ≤ δgrad i →
          dist ((fderiv ℝ (u.approx m) x) (basisVec i))
            ((fderiv ℝ (u.approx m) y) (basisVec i)) ≤ η := by
      intro i x y hxy
      exact (Classical.choose_spec ((Metric.uniformContinuous_iff_le.mp (hgrad_uc i)) η hη)).2 hxy
    let gradValues : Finset ℝ := Finset.univ.image δgrad
    have hgradValues_nonempty : gradValues.Nonempty := by
      exact Finset.univ_nonempty.image δgrad
    let δgradMin : ℝ := gradValues.min' hgradValues_nonempty
    have hδgradMin_pos : 0 < δgradMin := by
      rcases Finset.mem_image.mp (Finset.min'_mem gradValues hgradValues_nonempty) with
        ⟨i, -, hi⟩
      calc
        0 < δgrad i := hδgrad_pos i
        _ = δgradMin := by simpa [δgradMin, gradValues] using hi
    have hδgradMin_le : ∀ i : Fin d, δgradMin ≤ δgrad i := by
      intro i
      exact Finset.min'_le gradValues (δgrad i)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    let ε : ℝ := min (εpush / 2) (min δfun δgradMin)
    have hε_pos : 0 < ε := by
      dsimp [ε]
      refine lt_min ?_ (lt_min hδfun_pos hδgradMin_pos)
      linarith
    have hε_lt_push : ε < εpush := by
      have hle : ε ≤ εpush / 2 := by
        dsimp [ε]
        exact min_le_left _ _
      have hhalf_lt : εpush / 2 < εpush := by
        linarith
      exact lt_of_le_of_lt hle hhalf_lt
    refine ⟨ε, hε_pos, hpush hε_pos hε_lt_push, ?_, ?_⟩
    · intro x
      have hdist :
          dist (x - diagonalShift (d := d) ε) x ≤ δfun := by
        calc
          dist (x - diagonalShift (d := d) ε) x ≤ ε :=
            dist_sub_diagonalShift_le (d := d) x (le_of_lt hε_pos)
          _ ≤ min δfun δgradMin := by
            dsimp [ε]
            exact min_le_right _ _
          _ ≤ δfun := min_le_left _ _
      exact hδfun hdist
    · intro i x
      have hdist :
          dist (x - diagonalShift (d := d) ε) x ≤ δgrad i := by
        calc
          dist (x - diagonalShift (d := d) ε) x ≤ ε :=
            dist_sub_diagonalShift_le (d := d) x (le_of_lt hε_pos)
          _ ≤ min δfun δgradMin := by
            dsimp [ε]
            exact min_le_right _ _
          _ ≤ δgradMin := min_le_right _ _
          _ ≤ δgrad i := hδgradMin_le i
      exact hδgrad i hdist
  let εShift : ℕ → ℝ := fun m => Classical.choose (hshiftData m)
  let approx' : ℕ → Vec d → ℝ := fun m x => u.approx m (x - diagonalShift (d := d) (εShift m))
  have hεShift :
      ∀ m : ℕ,
        0 < εShift m ∧
          tsupport (approx' m) ⊆ Uo ∧
          (∀ x : Vec d, dist (approx' m x) (u.approx m x) ≤ 1 / ((m : ℝ) + 1)) ∧
          (∀ i : Fin d, ∀ x : Vec d,
            dist ((fderiv ℝ (u.approx m) (x - diagonalShift (d := d) (εShift m))) (basisVec i))
              ((fderiv ℝ (u.approx m) x) (basisVec i)) ≤ 1 / ((m : ℝ) + 1)) := by
    intro m
    simpa [εShift, approx'] using Classical.choose_spec (hshiftData m)
  have happrox'_smooth : ∀ m : ℕ, ContDiff ℝ (⊤ : ℕ∞) (approx' m) := by
    intro m
    have hshift_smooth :
        ContDiff ℝ (⊤ : ℕ∞)
          (fun x : Vec d => x - diagonalShift (d := d) (εShift m)) := by
      simpa [diagonalShift] using contDiff_id.sub contDiff_const
    simpa [approx'] using! (u.approx_smooth m).comp hshift_smooth
  have happrox'_compact : ∀ m : ℕ, HasCompactSupport (approx' m) := by
    intro m
    simpa [approx'] using!
      (u.approx_hasCompactSupport m).comp_homeomorph
        (Homeomorph.subRight (diagonalShift (d := d) (εShift m)))
  have horigRestrict :
      Filter.Tendsto
        (fun m : ℕ =>
          MeasureTheory.eLpNorm (fun x => u.approx m x - v.toFun x) 2 μo)
        Filter.atTop (𝓝 0) := by
    have hcube :
        Filter.Tendsto
          (fun m : ℕ =>
            MeasureTheory.eLpNorm (fun x => u.approx m x - u.toH1Function.toFun x) 2
              (MeasureTheory.volume.restrict Uc))
          Filter.atTop (𝓝 0) := by
      simpa [Uc] using u.tendsto_approx
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcube (fun _ => bot_le) ?_
    intro m
    simpa [v, H1Function.restrict, μo, Uo, Uc] using
      (MeasureTheory.eLpNorm_mono_measure
        (fun x => u.approx m x - u.toH1Function.toFun x)
        (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume (openCubeSet_subset_cubeSet _)))
  have horigGradRestrict :
      ∀ i : Fin d,
        Filter.Tendsto
          (fun m : ℕ =>
            MeasureTheory.eLpNorm
              (fun x => (fderiv ℝ (u.approx m) x) (basisVec i) - v.grad x i) 2 μo)
          Filter.atTop (𝓝 0) := by
    intro i
    have hcube :
        Filter.Tendsto
          (fun m : ℕ =>
            MeasureTheory.eLpNorm
              (fun x => (fderiv ℝ (u.approx m) x) (basisVec i) - u.toH1Function.grad x i) 2
                (MeasureTheory.volume.restrict Uc))
          Filter.atTop (𝓝 0) := by
      simpa [Uc] using u.tendsto_approx_grad i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hcube (fun _ => bot_le) ?_
    intro m
    simpa [v, H1Function.restrict, μo, Uo, Uc] using
      (MeasureTheory.eLpNorm_mono_measure
        (fun x => (fderiv ℝ (u.approx m) x) (basisVec i) - u.toH1Function.grad x i)
        (MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume (openCubeSet_subset_cubeSet _)))
  have hμo_univ_lt_top : μo Set.univ < ⊤ := by
    simpa [μo] using volume_openCubeSet_originCube_lt_top (d := d) n
  have hshiftApprox :
      Filter.Tendsto
        (fun m : ℕ =>
          MeasureTheory.eLpNorm (fun x => approx' m x - u.approx m x) 2 μo)
        Filter.atTop (𝓝 0) := by
    let cμ : ℝ := (μo Set.univ).toReal ^ (1 / ((2 : ENNReal).toReal))
    have hpow_eq :
        μo Set.univ ^ (1 / ((2 : ENNReal).toReal)) = ENNReal.ofReal cμ := by
      have hpow_lt_top :
          μo Set.univ ^ (1 / ((2 : ENNReal).toReal)) < ⊤ :=
        ENNReal.rpow_lt_top_of_nonneg (by positivity) hμo_univ_lt_top.ne
      calc
        μo Set.univ ^ (1 / ((2 : ENNReal).toReal)) =
            ENNReal.ofReal ((μo Set.univ ^ (1 / ((2 : ENNReal).toReal))).toReal) := by
              exact (ENNReal.ofReal_toReal hpow_lt_top.ne).symm
        _ = ENNReal.ofReal cμ := by
              congr 1
              simpa [cμ] using
                (ENNReal.toReal_rpow (μo Set.univ) (1 / ((2 : ENNReal).toReal))).symm
    have hbound :
        ∀ m : ℕ,
          MeasureTheory.eLpNorm (fun x => approx' m x - u.approx m x) 2 μo ≤
            ENNReal.ofReal ((1 / ((m : ℝ) + 1)) * cμ) := by
      intro m
      calc
        MeasureTheory.eLpNorm (fun x => approx' m x - u.approx m x) 2 μo
            ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * μo Set.univ ^ (1 / ((2 : ENNReal).toReal)) :=
              MeasureTheory.eLpNorm_sub_le_of_dist_bdd
                (μ := μo) (p := (2 : ENNReal)) (s := Set.univ)
                (by simp) MeasurableSet.univ (by positivity) (hεShift m).2.2.1
                (by simp) (by simp)
        _ = ENNReal.ofReal ((1 / ((m : ℝ) + 1)) * cμ) := by
              rw [hpow_eq, ← ENNReal.ofReal_mul]
              positivity
    have hbase : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) Filter.atTop (𝓝 0) := by
      have hdenCast : Filter.Tendsto (fun m : ℕ => (((m + 1 : ℕ) : ℝ))) Filter.atTop Filter.atTop := by
        exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
      have hden : Filter.Tendsto (fun m : ℕ => (m : ℝ) + 1) Filter.atTop Filter.atTop := by
        convert hdenCast using 1
        ext m
        simp [Nat.cast_add]
      simpa [one_div] using! tendsto_inv_atTop_zero.comp hden
    have hbound_tendsto :
        Filter.Tendsto
          (fun m : ℕ => ENNReal.ofReal ((1 / ((m : ℝ) + 1)) * cμ))
          Filter.atTop (𝓝 0) := by
      simpa [zero_mul, mul_comm] using ENNReal.tendsto_ofReal (hbase.mul_const cμ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound_tendsto
      (fun _ => bot_le) hbound
  have hshiftGrad :
      ∀ i : Fin d,
        Filter.Tendsto
          (fun m : ℕ =>
            MeasureTheory.eLpNorm
              (fun x =>
                (fderiv ℝ (u.approx m) (x - diagonalShift (d := d) (εShift m))) (basisVec i)
                  - (fderiv ℝ (u.approx m) x) (basisVec i)) 2 μo)
          Filter.atTop (𝓝 0) := by
    intro i
    let cμ : ℝ := (μo Set.univ).toReal ^ (1 / ((2 : ENNReal).toReal))
    have hpow_eq :
        μo Set.univ ^ (1 / ((2 : ENNReal).toReal)) = ENNReal.ofReal cμ := by
      have hpow_lt_top :
          μo Set.univ ^ (1 / ((2 : ENNReal).toReal)) < ⊤ :=
        ENNReal.rpow_lt_top_of_nonneg (by positivity) hμo_univ_lt_top.ne
      calc
        μo Set.univ ^ (1 / ((2 : ENNReal).toReal)) =
            ENNReal.ofReal ((μo Set.univ ^ (1 / ((2 : ENNReal).toReal))).toReal) := by
              exact (ENNReal.ofReal_toReal hpow_lt_top.ne).symm
        _ = ENNReal.ofReal cμ := by
              congr 1
              simpa [cμ] using
                (ENNReal.toReal_rpow (μo Set.univ) (1 / ((2 : ENNReal).toReal))).symm
    have hbound :
        ∀ m : ℕ,
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ (u.approx m) (x - diagonalShift (d := d) (εShift m))) (basisVec i)
                - (fderiv ℝ (u.approx m) x) (basisVec i)) 2 μo ≤
              ENNReal.ofReal ((1 / ((m : ℝ) + 1)) * cμ) := by
      intro m
      calc
        MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ (u.approx m) (x - diagonalShift (d := d) (εShift m))) (basisVec i)
                - (fderiv ℝ (u.approx m) x) (basisVec i)) 2 μo
            ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * μo Set.univ ^ (1 / ((2 : ENNReal).toReal)) :=
              MeasureTheory.eLpNorm_sub_le_of_dist_bdd
                (μ := μo) (p := (2 : ENNReal)) (s := Set.univ)
                (by simp) MeasurableSet.univ (by positivity) ((hεShift m).2.2.2 i)
                (by simp) (by simp)
        _ = ENNReal.ofReal ((1 / ((m : ℝ) + 1)) * cμ) := by
              rw [hpow_eq, ← ENNReal.ofReal_mul]
              positivity
    have hbase : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) Filter.atTop (𝓝 0) := by
      have hdenCast : Filter.Tendsto (fun m : ℕ => (((m + 1 : ℕ) : ℝ))) Filter.atTop Filter.atTop := by
        exact (tendsto_natCast_atTop_atTop (R := ℝ)).comp (Filter.tendsto_add_atTop_nat 1)
      have hden : Filter.Tendsto (fun m : ℕ => (m : ℝ) + 1) Filter.atTop Filter.atTop := by
        convert hdenCast using 1
        ext m
        simp [Nat.cast_add]
      simpa [one_div] using! tendsto_inv_atTop_zero.comp hden
    have hbound_tendsto :
        Filter.Tendsto
          (fun m : ℕ => ENNReal.ofReal ((1 / ((m : ℝ) + 1)) * cμ))
          Filter.atTop (𝓝 0) := by
      simpa [zero_mul, mul_comm] using ENNReal.tendsto_ofReal (hbase.mul_const cμ)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound_tendsto
      (fun _ => bot_le) hbound
  refine
    { toH1Function := v
      approx := approx'
      approx_smooth := happrox'_smooth
      approx_hasCompactSupport := happrox'_compact
      approx_support_subset := by
        intro m
        exact (hεShift m).2.1
      tendsto_approx := by
        have hsum :
            Filter.Tendsto
              (fun m : ℕ =>
                MeasureTheory.eLpNorm (fun x => u.approx m x - v.toFun x) 2 μo +
                  MeasureTheory.eLpNorm (fun x => approx' m x - u.approx m x) 2 μo)
              Filter.atTop (𝓝 0) := by
          simpa using horigRestrict.add hshiftApprox
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
          (fun _ => bot_le) ?_
        intro m
        have hmeas₁ :
            MeasureTheory.AEStronglyMeasurable (fun x => u.approx m x - v.toFun x) μo :=
          ((u.approx_smooth m).differentiable (by simp)).continuous.aestronglyMeasurable.sub
            v.memL2.aestronglyMeasurable
        have hmeas₂ :
            MeasureTheory.AEStronglyMeasurable (fun x => approx' m x - u.approx m x) μo :=
          (happrox'_smooth m).continuous.aestronglyMeasurable.sub
            ((u.approx_smooth m).differentiable (by simp)).continuous.aestronglyMeasurable
        have htri :=
          MeasureTheory.eLpNorm_add_le hmeas₁ hmeas₂ (by norm_num : (1 : ENNReal) ≤ 2)
        have hsum_eq :
            ((fun x => u.approx m x - v.toFun x) + fun x => approx' m x - u.approx m x) =
              (fun x => approx' m x - v.toFun x) := by
          funext x
          simp [approx', sub_eq_add_neg]
          ring
        simpa [hsum_eq] using htri
      tendsto_approx_grad := by
        intro i
        have hsum :
            Filter.Tendsto
              (fun m : ℕ =>
                MeasureTheory.eLpNorm
                    (fun x => (fderiv ℝ (u.approx m) x) (basisVec i) - v.grad x i) 2 μo +
                  MeasureTheory.eLpNorm
                    (fun x =>
                      (fderiv ℝ (u.approx m) (x - diagonalShift (d := d) (εShift m)))
                        (basisVec i) - (fderiv ℝ (u.approx m) x) (basisVec i)) 2 μo)
              Filter.atTop (𝓝 0) := by
          simpa using (horigGradRestrict i).add (hshiftGrad i)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
          (fun _ => bot_le) ?_
        intro m
        have hmeas₁ :
            MeasureTheory.AEStronglyMeasurable
              (fun x => (fderiv ℝ (u.approx m) x) (basisVec i) - v.grad x i) μo := by
          have hcont :
              Continuous (fun x : Vec d => (fderiv ℝ (u.approx m) x) (basisVec i)) := by
            simpa using
              ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply continuous_const
          exact hcont.aestronglyMeasurable.sub (v.gradMemL2 i).aestronglyMeasurable
        have hmeas₂ :
            MeasureTheory.AEStronglyMeasurable
              (fun x =>
                (fderiv ℝ (u.approx m) (x - diagonalShift (d := d) (εShift m))) (basisVec i)
                  - (fderiv ℝ (u.approx m) x) (basisVec i)) μo := by
          have hcontShift :
              Continuous
                (fun x : Vec d =>
                  (fderiv ℝ (u.approx m) (x - diagonalShift (d := d) (εShift m))) (basisVec i)) := by
            have hbase :
                Continuous (fun x : Vec d => (fderiv ℝ (u.approx m) x) (basisVec i)) := by
              simpa using
                ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply continuous_const
            exact hbase.comp (continuous_id.sub continuous_const)
          have hcont :
              Continuous (fun x : Vec d => (fderiv ℝ (u.approx m) x) (basisVec i)) := by
            simpa using
              ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply continuous_const
          exact hcontShift.aestronglyMeasurable.sub hcont.aestronglyMeasurable
        have htri :=
          MeasureTheory.eLpNorm_add_le hmeas₁ hmeas₂ (by norm_num : (1 : ENNReal) ≤ 2)
        have hsum_eq :
            ((fun x => (fderiv ℝ (u.approx m) x) (basisVec i) - v.grad x i) +
                fun x =>
                  (fderiv ℝ (u.approx m) (x - diagonalShift (d := d) (εShift m))) (basisVec i) -
                    (fderiv ℝ (u.approx m) x) (basisVec i)) =
              (fun x => (fderiv ℝ (approx' m) x) (basisVec i) - v.grad x i) := by
          funext x
          have hderiv_eq :
              (fderiv ℝ (approx' m) x) (basisVec i) =
                (fderiv ℝ (u.approx m) (x - diagonalShift (d := d) (εShift m))) (basisVec i) := by
            simpa [approx'] using
              congrArg (fun L => L (basisVec i))
                (fderiv_comp_sub (𝕜 := ℝ) (f := u.approx m)
                  (x := x) (a := diagonalShift (d := d) (εShift m)))
          rw [hderiv_eq]
          simp [sub_eq_add_neg]
          ring
        simpa [hsum_eq] using htri }

@[simp] theorem toOpenCubeSetOriginCube_toH1Function_toFun {d : ℕ} [NeZero d] {n : ℤ}
    (u : H10Function (cubeSet (originCube d n))) :
    (u.toOpenCubeSetOriginCube.toH1Function.toFun) = u.toH1Function.toFun :=
  rfl

@[simp] theorem toOpenCubeSetOriginCube_toH1Function_grad {d : ℕ} [NeZero d] {n : ℤ}
    (u : H10Function (cubeSet (originCube d n))) :
    (u.toOpenCubeSetOriginCube.toH1Function.grad) = u.toH1Function.grad :=
  rfl

end H10Function

end Homogenization
