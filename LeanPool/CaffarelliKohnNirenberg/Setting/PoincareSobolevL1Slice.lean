/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Vec
public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1SliceBasic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Mathlib.MeasureTheory.SpecificCodomains.Pi
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.LpApproximation
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Transport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpConvergence

/-!
# Poincare Sobolev L1 Slice

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped BigOperators ENNReal Convolution Pointwise
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

/-- H¹ lift of the vector-valued Poincare–Sobolev inequality on nested balls. -/
theorem poincareSobolevL1_vec3_slice_euclidean
    {U : Set Vec3} (hU : IsOpen U) {x₀ : Vec3} {R r : ℝ}
    (hr : 0 < r) (hrr : r < R)
    (hball : vec3Ball x₀ R ⊆ U)
    (u : Vec3 → Vec3) (g : Vec3 → Fin 3 → Vec3)
    (hu : ∀ i : Fin 3, MemLp (fun x => u x i) (2 : ℝ≥0∞)
      (volume.restrict U))
    (hg : ∀ i : Fin 3, MemLp (fun x => g x i) (2 : ℝ≥0∞)
      (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      HasWeakGradientOn U (fun x => u x i) (fun x => g x i)) :
    (∫ x in vec3Ball x₀ r,
        |(vec3EuclideanNorm (u x)) ^ 2 -
          ⨍ y in vec3Ball x₀ r, (vec3EuclideanNorm (u y)) ^ 2| ^
            (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) ≤
      poincareSobolevL1VectorConstant *
        (∫ x in vec3Ball x₀ r, (vec3EuclideanNorm (u x)) ^ 2 ∂volume) ^
          (1 / 2 : ℝ) *
        (∫ x in vec3Ball x₀ r, ∑ i : Fin 3, ∑ j : Fin 3,
          (g x i j) ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
  rw [vec3Ball_eq_euclideanBall' hr]
  let t : ℝ := (R + r) / 2
  let ε₀ : ℝ := (R - t) / (2 * Real.sqrt 3)
  let ε : ℕ → ℝ := fun n => ε₀ / ((n : ℝ) + 1)
  let K : Set Vec3 := euclideanClosedBall x₀ t
  let D : Set Vec3 := euclideanBall x₀ r
  let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀
  have ht : r < t := by dsimp [t]; linarith only [hrr]
  have htR : t < R := by dsimp [t]; linarith only [hrr]
  have ht_pos : 0 < t := lt_trans hr ht
  have hsqrt : 0 < Real.sqrt 3 := by positivity
  have hε₀_pos : 0 < ε₀ := by
    dsimp [ε₀]
    positivity
  have hε_pos : ∀ n, 0 < ε n := by
    intro n
    dsimp [ε]
    exact div_pos hε₀_pos (by positivity)
  have hε_le : ∀ n, ε n ≤ ε₀ := by
    intro n
    dsimp [ε]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    apply (div_le_iff₀ hden).2
    nlinarith only [hε₀_pos.le, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hε_tendsto : Tendsto ε atTop (nhds 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
      simpa only [add_comm] using
        (tendsto_atTop_add_const_left atTop (1 : ℝ)
          (tendsto_natCast_atTop_atTop :
            Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hden
    simpa [ε, div_eq_mul_inv] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ε₀) atTop (nhds ε₀)).mul hinv)
  have hsqrtε : ∀ n, Real.sqrt 3 * ε n ≤ (R - t) / 2 := by
    intro n
    calc
      Real.sqrt 3 * ε n ≤ Real.sqrt 3 * ε₀ :=
        mul_le_mul_of_nonneg_left (hε_le n) hsqrt.le
      _ = (R - t) / 2 := by
        dsimp [ε₀]
        field_simp [ne_of_gt hsqrt]
  have hK_compact : IsCompact K := by
    simpa [K] using isCompact_euclideanClosedBall x₀ ht_pos.le
  have hD_open : IsOpen D := by
    change IsOpen {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hD_meas : MeasurableSet D := hD_open.measurableSet
  have hvecnorm_eq (z : Vec3) : vec3EuclideanNorm z = vecEuclideanNorm z := by
    simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
  have hnorm_le_euclidean (z : Vec3) : ‖z‖ ≤ vec3EuclideanNorm z := by
    rw [Pi.norm_def]
    have hnn : Finset.univ.sup (fun i => ‖z i‖₊) ≤
        ⟨vecEuclideanNorm z, vecEuclideanNorm_nonneg z⟩ := by
      apply Finset.sup_le
      intro i hi
      exact abs_apply_le_vecEuclideanNorm z i
    rw [hvecnorm_eq]
    exact_mod_cast hnn
  have hK_sub_R : K ⊆ vec3Ball x₀ R := by
    intro x hx
    apply mem_vec3Ball.2
    have hxE : vec3EuclideanNorm (x - x₀) ≤ t := by
      simpa [hvecnorm_eq] using
        (mem_euclideanClosedBall_iff_vecEuclideanNorm_le ht_pos.le).1 hx
    exact hxE.trans_lt htR
  have hD_sub_K : D ⊆ K := by
    intro x hx
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le ht_pos.le).2
    have hxE : vec3EuclideanNorm (x - x₀) < r := by
      rw [hvecnorm_eq]
      exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
    simpa [hvecnorm_eq] using le_of_lt (hxE.trans ht)
  have hclosed_subset : ∀ x ∈ K, Metric.closedBall x ε₀ ⊆ U := by
    intro x hx y hy
    apply hball
    apply mem_vec3Ball.2
    have hxy : dist y x ≤ ε₀ := by
      simpa [Metric.mem_closedBall] using hy
    have hx0' : vecEuclideanNorm (x - x₀) ≤ t :=
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le ht_pos.le).1 hx
    have hx0 : vec3EuclideanNorm (x - x₀) ≤ t := by
      simpa [hvecnorm_eq] using hx0'
    have hyx : vec3EuclideanNorm (y - x) ≤ Real.sqrt 3 * ‖y - x‖ :=
      native_euclidean_norm_le_sqrt_three_norm (y - x)
    have htri : vec3EuclideanNorm (y - x₀) ≤
        Real.sqrt 3 * ‖y - x‖ + vec3EuclideanNorm (x - x₀) := by
      calc
        vec3EuclideanNorm (y - x₀) =
            vec3EuclideanNorm ((y - x) + (x - x₀)) := by
              congr 1
              abel
        _ ≤ vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - x₀) :=
          native_euclidean_norm_add_le _ _
        _ ≤ Real.sqrt 3 * ‖y - x‖ + vec3EuclideanNorm (x - x₀) := by
          exact add_le_add_left hyx _
    calc
      vec3EuclideanNorm (y - x₀) ≤ Real.sqrt 3 * ε₀ + t := by
        exact htri.trans (add_le_add
          (mul_le_mul_of_nonneg_left hxy hsqrt.le) hx0)
      _ = (R + t) / 2 := by
        dsimp [ε₀]
        field_simp [ne_of_gt hsqrt]
        ring
      _ < R := by linarith only [htR]
  have hS_compact : IsCompact S := by
    simpa [S] using hK_compact.add (ProperSpace.isCompact_closedBall (0 : Vec3) ε₀)
  have hS_sub_U : S ⊆ U := by
    rintro y ⟨x, hx, z, hz, rfl⟩
    apply hclosed_subset x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [sub_eq_add_neg, add_comm] using hz
  have huS (i : Fin 3) : MemLp (S.indicator (fun x => u x i)) (2 : ℝ≥0∞) volume := by
    apply (memLp_indicator_iff_restrict hS_compact.measurableSet).2
    exact (hu i).mono_measure (Measure.restrict_mono_set volume hS_sub_U)
  have huExt (i : Fin 3) : MemLp (U.indicator (fun x => u x i)) (2 : ℝ≥0∞) volume := by
    apply (memLp_indicator_iff_restrict hU.measurableSet).2
    exact hu i
  have hgExt (i j : Fin 3) : MemLp (U.indicator (fun x => g x i j)) (2 : ℝ≥0∞) volume := by
    apply (memLp_indicator_iff_restrict hU.measurableSet).2
    exact (MemLp.eval (hg i) j)
  have huExtLoc (i : Fin 3) : LocallyIntegrable (U.indicator (fun x => u x i)) volume :=
    (huExt i).locallyIntegrable (by norm_num)
  have hgExtLoc (i j : Fin 3) :
      LocallyIntegrable (U.indicator (fun x => g x i j)) volume :=
    (hgExt i j).locallyIntegrable (by norm_num)
  have hweakExt (i j : Fin 3) :
      HasWeakPartialDerivOn U j (U.indicator (fun x => u x i))
        (U.indicator (fun x => g x i j)) := by
    intro φ hφ hφCompact hφSupport
    calc
      ∫ x in U, U.indicator (fun y => u y i) x *
          (fderiv ℝ φ x) (basisVec j) ∂volume =
          ∫ x in U, (fun y => u y i) x *
            (fderiv ℝ φ x) (basisVec j) ∂volume := by
              apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
              intro x hx
              simp [Set.indicator_of_mem hx]
      _ = -∫ x in U, (fun y => g y i j) x * φ x ∂volume :=
        hweak i j φ hφ hφCompact hφSupport
      _ = -∫ x in U, U.indicator (fun y => g y i j) x * φ x ∂volume := by
              congr 1
              apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
              intro x hx
              simp [Set.indicator_of_mem hx]
  have huLoc (i : Fin 3) : LocallyIntegrable (S.indicator (fun x => u x i)) volume :=
    (huS i).locallyIntegrable (by norm_num)
  have hgS (i j : Fin 3) : MemLp (S.indicator (fun x => g x i j)) (2 : ℝ≥0∞) volume := by
    apply (memLp_indicator_iff_restrict hS_compact.measurableSet).2
    exact ((MemLp.eval (hg i) j).mono_measure
      (Measure.restrict_mono_set volume hS_sub_U))
  have hgLoc (i j : Fin 3) : LocallyIntegrable (S.indicator (fun x => g x i j)) volume :=
    (hgS i j).locallyIntegrable (by norm_num)
  let v : ℕ → Vec3 → Vec3 := fun n x i =>
    mollify (S.indicator (fun y => u y i)) (ε n) (hε_pos n) x
  let w : ℕ → Vec3 → Fin 3 → Vec3 := fun n x i j =>
    mollify (S.indicator (fun y => g y i j)) (ε n) (hε_pos n) x
  have hvDiff (n : ℕ) : ContDiff ℝ 1 (v n) := by
    apply contDiff_pi.2
    intro i
    exact mollify_contDiff (hε_pos n) (huLoc i) (n := 1)
  have hvCoordCont (n : ℕ) (i : Fin 3) : Continuous (fun x => v n x i) :=
      (contDiff_apply ℝ ℝ i |>.comp (hvDiff n)).continuous
  have hwCont (n : ℕ) (i j : Fin 3) : Continuous (fun x => w n x i j) :=
    (mollify_continuous (hε_pos n) (hgLoc i j))
  have hclosed_subset_ε (n : ℕ) : ∀ y ∈ K,
      Metric.closedBall y (ε n) ⊆ U := by
    intro y hy z hz
    apply hclosed_subset y hy
    rw [Metric.mem_closedBall] at hz ⊢
    exact hz.trans (hε_le n)
  have hvalue_eventually (n : ℕ) (i : Fin 3) {x : Vec3} (hx : x ∈ D) :
      (fun y => v n y i) =ᶠ[𝓝 x]
        mollify (U.indicator (fun y => u y i)) (ε n) (hε_pos n) := by
    have hx' : dist x x₀ < r := by
      rw [dist_eq_norm]
      have hxE : vec3EuclideanNorm (x - x₀) < r := by
        rw [hvecnorm_eq]
        exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
      exact lt_of_le_of_lt (hnorm_le_euclidean (x - x₀)) hxE
    have hxt : dist x x₀ < t := lt_trans hx' ht
    have hxE : vec3EuclideanNorm (x - x₀) < t :=
      lt_trans (by
        rw [hvecnorm_eq]
        exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx) ht
    have hball' : Metric.ball x
        ((t - vec3EuclideanNorm (x - x₀)) / Real.sqrt 3) ∈ 𝓝 x :=
      Metric.ball_mem_nhds x (div_pos (sub_pos.mpr hxE) hsqrt)
    filter_upwards [hball'] with y hy
    have hy' : dist y x <
        (t - vec3EuclideanNorm (x - x₀)) / Real.sqrt 3 := by
      simpa [Metric.mem_ball] using hy
    have hyK : y ∈ K := by
      apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le ht_pos.le).2
      have hyx : vec3EuclideanNorm (y - x) ≤ Real.sqrt 3 * ‖y - x‖ :=
        native_euclidean_norm_le_sqrt_three_norm (y - x)
      have hsum : vec3EuclideanNorm (y - x₀) < t := by
        have hy'' : ‖y - x‖ <
            (t - vec3EuclideanNorm (x - x₀)) / Real.sqrt 3 := by
          simpa [dist_eq_norm] using hy'
        calc
          vec3EuclideanNorm (y - x₀) ≤
              vec3EuclideanNorm (y - x) + vec3EuclideanNorm (x - x₀) := by
            rw [show y - x₀ = (y - x) + (x - x₀) by abel]
            exact native_euclidean_norm_add_le _ _
          _ ≤ Real.sqrt 3 * ‖y - x‖ + vec3EuclideanNorm (x - x₀) :=
            add_le_add_left hyx _
          _ < Real.sqrt 3 *
                ((t - vec3EuclideanNorm (x - x₀)) / Real.sqrt 3) +
                vec3EuclideanNorm (x - x₀) := by
            exact add_lt_add_left
              ((mul_lt_mul_of_pos_left hy'' hsqrt)) _
          _ = t := by
            field_simp [ne_of_gt hsqrt]
            ring
      simpa [hvecnorm_eq] using hsum.le
    change mollify (S.indicator (fun z => u z i)) (ε n) (hε_pos n) y = _
    apply mollify_eq_on_compact_of_eq_on_thickening (hε_pos n) (hε_le n)
      (fun z hz => by
        have hzS : z ∈ S := by simpa [S] using hz
        have hzU : z ∈ U := hS_sub_U hzS
        simp [Set.indicator_of_mem hzS, Set.indicator_of_mem hzU]) hyK
  have hderiv_eq (n : ℕ) (i j : Fin 3) {x : Vec3} (hx : x ∈ D) :
      (fderiv ℝ (fun y => v n y i) x) (basisVec j) = w n x i j := by
    have hxK : x ∈ K := hD_sub_K hx
    have hfd := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ)
      (hvalue_eventually n i hx)
    have htransport := fderiv_mollify_eq_mollify_on_compact
      hU hK_compact (huExtLoc i) (hgExtLoc i j)
      (hweakExt i j) (hε_pos n) (hclosed_subset_ε n) hxK
    calc
      (fderiv ℝ (fun y => v n y i) x) (basisVec j) =
          (fderiv ℝ (mollify (U.indicator (fun y => u y i))
            (ε n) (hε_pos n)) x)
            (basisVec j) := by
              exact congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j)) hfd
      _ = mollify (U.indicator (fun y => g y i j)) (ε n) (hε_pos n) x := htransport
      _ = w n x i j := by
        symm
        apply mollify_eq_on_compact_of_eq_on_thickening (hε_pos n) (hε_le n)
          (fun z hz => by
            have hzS : z ∈ S := by simpa [S] using hz
            have hzU : z ∈ U := hS_sub_U hzS
            simp [Set.indicator_of_mem hzS, Set.indicator_of_mem hzU]) hxK
  have hD_sub_U : D ⊆ U := hD_sub_K.trans hK_sub_R |>.trans hball
  have huD (i : Fin 3) : MemLp (fun x => u x i) (2 : ℝ≥0∞) (volume.restrict D) :=
    (hu i).mono_measure (Measure.restrict_mono_set volume hD_sub_U)
  have hgD (i j : Fin 3) : MemLp (fun x => g x i j) (2 : ℝ≥0∞) (volume.restrict D) :=
    (MemLp.eval (hg i) j).mono_measure (Measure.restrict_mono_set volume hD_sub_U)
  have hS_u_support (i : Fin 3) : HasCompactSupport (S.indicator (fun x => u x i)) := by
    apply HasCompactSupport.intro hS_compact
    intro x hx
    simp [Set.indicator, hx]
  have hvMem (n : ℕ) (i : Fin 3) : MemLp (fun x => v n x i) (2 : ℝ≥0∞) volume := by
    apply (mollify_continuous (hε_pos n) (huLoc i)).memLp_of_hasCompactSupport
    change HasCompactSupport
      (mollify (S.indicator (fun y => u y i)) (ε n) (hε_pos n))
    simpa [mollify] using
      (mollifier_hasCompactSupport (hε_pos n)).convolution
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (hS_u_support i)
  have hS_g_support (i j : Fin 3) : HasCompactSupport (S.indicator (fun x => g x i j)) := by
    apply HasCompactSupport.intro hS_compact
    intro x hx
    simp [Set.indicator, hx]
  have hwMem (n : ℕ) (i j : Fin 3) : MemLp (fun x => w n x i j) (2 : ℝ≥0∞) volume := by
    apply (hwCont n i j).memLp_of_hasCompactSupport
    change HasCompactSupport
      (mollify (S.indicator (fun y => g y i j)) (ε n) (hε_pos n))
    simpa [mollify] using
      (mollifier_hasCompactSupport (hε_pos n)).convolution
        (L := ContinuousLinearMap.lsmul ℝ ℝ) (hS_g_support i j)
  have hval_eK (i : Fin 3) : Tendsto (fun n => eLpNorm
        (fun x => mollify (S.indicator (fun y => u y i))
          (ε n) (hε_pos n) x - u x i)
        (2 : ℝ≥0∞) (volume.restrict K)) atTop (nhds 0) := by
    simpa [S] using
      (tendsto_eLpNorm_restrict_mollify_sub_zero hK_compact hε₀_pos
        hclosed_subset (by norm_num) ENNReal.coe_ne_top (hu i)
        hε_tendsto hε_pos)
  have hval_eD (i : Fin 3) : Tendsto (fun n => eLpNorm (fun x => v n x i - u x i)
      (2 : ℝ≥0∞) (volume.restrict D)) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hval_eK i) (Eventually.of_forall (fun _ => zero_le))
    filter_upwards [] with n
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hD_sub_K)
  have hgrad_eK (i j : Fin 3) : Tendsto (fun n => eLpNorm
        (fun x => mollify (S.indicator (fun y => g y i j))
          (ε n) (hε_pos n) x - g x i j)
        (2 : ℝ≥0∞) (volume.restrict K)) atTop (nhds 0) := by
    simpa [S] using
      (tendsto_eLpNorm_restrict_mollify_sub_zero hK_compact hε₀_pos
        hclosed_subset (by norm_num) ENNReal.coe_ne_top (MemLp.eval (hg i) j)
        hε_tendsto hε_pos)
  have hgrad_eD (i j : Fin 3) : Tendsto (fun n => eLpNorm (fun x => w n x i j - g x i j)
      (2 : ℝ≥0∞) (volume.restrict D)) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hgrad_eK i j) (Eventually.of_forall (fun _ => zero_le))
    filter_upwards [] with n
    exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hD_sub_K)
  have hval_lp (i : Fin 3) : Tendsto (fun n => lpNorm (fun x => v n x i - u x i)
      (2 : ℝ≥0∞) (volume.restrict D)) atTop (nhds 0) :=
    tendsto_lpNorm_zero_of_tendsto_eLpNorm_zero (hval_eD i)
  have hgrad_lp (i j : Fin 3) : Tendsto (fun n => lpNorm (fun x => w n x i j - g x i j)
      (2 : ℝ≥0∞) (volume.restrict D)) atTop (nhds 0) :=
    tendsto_lpNorm_zero_of_tendsto_eLpNorm_zero (hgrad_eD i j)
  have hvD (n : ℕ) (i : Fin 3) : MemLp (fun x => v n x i) (2 : ℝ≥0∞) (volume.restrict D) :=
    (hvMem n i).mono_measure Measure.restrict_le_self
  have hwD (n : ℕ) (i j : Fin 3) : MemLp (fun x => w n x i j) (2 : ℝ≥0∞) (volume.restrict D) :=
    (hwMem n i j).mono_measure Measure.restrict_le_self
  have hv_lp (i : Fin 3) : Tendsto
      (fun n => lpNorm (fun x => v n x i) (2 : ℝ≥0∞)
        (volume.restrict D)) atTop (nhds (lpNorm (fun x => u x i)
          (2 : ℝ≥0∞) (volume.restrict D))) :=
    lpNorm_tendsto_of_diff (by norm_num) (huD i) (fun n => hvD n i) (hval_lp i)
  have hw_lp (i j : Fin 3) : Tendsto
      (fun n => lpNorm (fun x => w n x i j) (2 : ℝ≥0∞)
        (volume.restrict D)) atTop (nhds (lpNorm (fun x => g x i j)
          (2 : ℝ≥0∞) (volume.restrict D))) :=
    lpNorm_tendsto_of_diff (by norm_num) (hgD i j) (fun n => hwD n i j)
      (hgrad_lp i j)
  have hval_sq_int (i : Fin 3) : Tendsto (fun n => ∫ x in D, (v n x i) ^ 2 ∂volume) atTop
      (nhds (∫ x in D, (u x i) ^ 2 ∂volume)) := by
    have h := tendsto_integral_rpow_norm_of_tendsto_lpNorm
      (μ := volume.restrict D) (p := (2 : ℝ≥0∞))
      (by norm_num) ENNReal.coe_ne_top (huD i) (fun n => hvD n i) (hv_lp i)
    simpa [Real.norm_eq_abs, sq_abs] using h
  have hgrad_sq_int (i j : Fin 3) : Tendsto (fun n => ∫ x in D, (w n x i j) ^ 2 ∂volume) atTop
      (nhds (∫ x in D, (g x i j) ^ 2 ∂volume)) := by
    have h := tendsto_integral_rpow_norm_of_tendsto_lpNorm
      (μ := volume.restrict D) (p := (2 : ℝ≥0∞))
      (by norm_num) ENNReal.coe_ne_top (hgD i j) (fun n => hwD n i j) (hw_lp i j)
    simpa [Real.norm_eq_abs, sq_abs] using h
  have hvec_sq (z : Vec3) : (vec3EuclideanNorm z) ^ 2 = ∑ i : Fin 3, z i ^ 2 := by
    rw [vec3EuclideanNorm]
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))
  have hval_int_eq (n : ℕ) : (∫ x in D, (vec3EuclideanNorm (v n x)) ^ 2 ∂volume) =
      ∑ i : Fin 3, ∫ x in D, (v n x i) ^ 2 ∂volume := by
    rw [show (fun x => (vec3EuclideanNorm (v n x)) ^ 2) =
        (fun x => ∑ i : Fin 3, (v n x i) ^ 2) by
          funext x
          exact hvec_sq (v n x)]
    rw [integral_finsetSum]
    intro i hi
    simpa [Real.norm_eq_abs, sq_abs] using
      (hvD n i).integrable_norm_rpow (by norm_num) ENNReal.coe_ne_top
  have hval_int_eq_limit : Tendsto (fun n => ∫ x in D, (vec3EuclideanNorm (v n x)) ^ 2 ∂volume) atTop
      (nhds (∫ x in D, (vec3EuclideanNorm (u x)) ^ 2 ∂volume)) := by
    have hsum : Tendsto
        (fun n => ∑ i : Fin 3, ∫ x in D, (v n x i) ^ 2 ∂volume) atTop
          (nhds (∑ i : Fin 3, ∫ x in D, (u x i) ^ 2 ∂volume)) := by
      simpa using tendsto_finsetSum (s := (Finset.univ : Finset (Fin 3)))
        (fun i _ => hval_sq_int i)
    rw [show (∫ x in D, (vec3EuclideanNorm (u x)) ^ 2 ∂volume) =
        ∑ i : Fin 3, ∫ x in D, (u x i) ^ 2 ∂volume by
          rw [show (fun x => (vec3EuclideanNorm (u x)) ^ 2) =
            (fun x => ∑ i : Fin 3, (u x i) ^ 2) by
              funext x
              exact hvec_sq (u x)]
          rw [integral_finsetSum]
          intro i hi
          simpa [Real.norm_eq_abs, sq_abs] using
            (huD i).integrable_norm_rpow (by norm_num) ENNReal.coe_ne_top]
    simpa [hval_int_eq] using hsum
  have hgrad_int_eq (n : ℕ) :
      (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (w n x i j) ^ 2 ∂volume) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x in D, (w n x i j) ^ 2 ∂volume := by
    calc
      _ = ∑ i : Fin 3, ∫ x in D, ∑ j : Fin 3, (w n x i j) ^ 2 ∂volume := by
        apply integral_finsetSum
        intro i hi
        apply integrable_finsetSum
        intro j hj
        simpa [Real.norm_eq_abs, sq_abs] using
          (hwD n i j).integrable_norm_rpow (by norm_num) ENNReal.coe_ne_top
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        intro j hj
        simpa [Real.norm_eq_abs, sq_abs] using
          (hwD n i j).integrable_norm_rpow (by norm_num) ENNReal.coe_ne_top
  have hgrad_int_limit : Tendsto
      (fun n => ∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (w n x i j) ^ 2 ∂volume) atTop
        (nhds (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (g x i j) ^ 2 ∂volume)) := by
    have hsumj (i : Fin 3) : Tendsto
        (fun n => ∑ j : Fin 3, ∫ x in D, (w n x i j) ^ 2 ∂volume) atTop
          (nhds (∑ j : Fin 3, ∫ x in D, (g x i j) ^ 2 ∂volume)) := by
      simpa using tendsto_finsetSum (s := (Finset.univ : Finset (Fin 3)))
        (fun j _ => hgrad_sq_int i j)
    have hsum : Tendsto
        (fun n => ∑ i : Fin 3, ∑ j : Fin 3, ∫ x in D, (w n x i j) ^ 2 ∂volume) atTop
          (nhds (∑ i : Fin 3, ∑ j : Fin 3, ∫ x in D, (g x i j) ^ 2 ∂volume)) := by
      simpa using tendsto_finsetSum (s := (Finset.univ : Finset (Fin 3)))
        (fun i _ => hsumj i)
    rw [show (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (g x i j) ^ 2 ∂volume) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x in D, (g x i j) ^ 2 ∂volume by
          calc
            _ = ∑ i : Fin 3, ∫ x in D, ∑ j : Fin 3, (g x i j) ^ 2 ∂volume := by
              apply integral_finsetSum
              intro i hi
              apply integrable_finsetSum
              intro j hj
              simpa [Real.norm_eq_abs, sq_abs] using
                (hgD i j).integrable_norm_rpow (by norm_num) ENNReal.coe_ne_top
            _ = _ := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [integral_finsetSum]
              intro j hj
              simpa [Real.norm_eq_abs, sq_abs] using
                (hgD i j).integrable_norm_rpow (by norm_num) ENNReal.coe_ne_top]
    simpa [hgrad_int_eq] using hsum
  have hderiv_int_eq (n : ℕ) : (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3,
        ((fderiv ℝ (fun y => v n y i) x) (basisVec j)) ^ 2 ∂volume) =
        ∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (w n x i j) ^ 2 ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hD_meas] with x hx
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hderiv_eq n i j hx]
  have hsmooth (n : ℕ) :
      (∫ x in D,
          |(vec3EuclideanNorm (v n x)) ^ 2 -
            ⨍ y in D, (vec3EuclideanNorm (v n y)) ^ 2| ^
              (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) ≤
        poincareSobolevL1VectorConstant *
          (∫ x in D, (vec3EuclideanNorm (v n x)) ^ 2 ∂volume) ^
            (1 / 2 : ℝ) *
          (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3,
            (w n x i j) ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
    have h := poincareSobolevL1_vec3_ball x₀ hr (v n) (hvDiff n)
    rw [vec3Ball_eq_euclideanBall' hr] at h
    simpa [D, hderiv_int_eq n] using h
  let q : Vec3 → ℝ := fun x => (vec3EuclideanNorm (u x)) ^ 2
  let qn : ℕ → Vec3 → ℝ := fun n x => (vec3EuclideanNorm (v n x)) ^ 2
  let av : ℕ → ℝ := fun n => ⨍ y in D, qn n y
  let av₀ : ℝ := ⨍ y in D, q y
  let F : Vec3 → ℝ := fun x => |q x - av₀| ^ (3 / 2 : ℝ)
  let Fn : ℕ → Vec3 → ℝ := fun n x => |qn n x - av n| ^ (3 / 2 : ℝ)
  have hqn_cont (n : ℕ) : Continuous (qn n) := by
    exact (continuous_vec3EuclideanNorm.comp (hvDiff n).continuous).pow 2
  have hD_closed : D ⊆ euclideanClosedBall x₀ r := by
    intro x hx
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).le
  have hclosed_compact : IsCompact (euclideanClosedBall x₀ r) :=
    isCompact_euclideanClosedBall x₀ hr.le
  have hq_limit : Tendsto
      (fun n => ∫ x in D, qn n x ∂volume) atTop
        (nhds (∫ x in D, q x ∂volume)) := by
    simpa [q, qn] using hval_int_eq_limit
  have havg_formula (n : ℕ) : av n =
      (volume D).toReal⁻¹ * ∫ x in D, qn n x ∂volume := by
    change (⨍ y in D, qn n y) = _
    rw [MeasureTheory.setAverage_eq]
    rfl
  have havg₀_formula : av₀ =
      (volume D).toReal⁻¹ * ∫ x in D, q x ∂volume := by
    change (⨍ y in D, q y) = _
    rw [MeasureTheory.setAverage_eq]
    rfl
  have havg_limit : Tendsto av atTop (nhds av₀) := by
    rw [show av = fun n => (volume D).toReal⁻¹ * ∫ x in D, qn n x ∂volume by
      funext n
      exact havg_formula n]
    rw [show av₀ = (volume D).toReal⁻¹ * ∫ x in D, q x ∂volume by
      exact havg₀_formula]
    simpa using (tendsto_const_nhds.mul hq_limit)
  have hFn_cont (n : ℕ) : Continuous (Fn n) := by
    exact ((hqn_cont n).sub continuous_const).abs.rpow_const
      (fun _ => Or.inr (by norm_num))
  have hFn_int (n : ℕ) : Integrable (Fn n) (volume.restrict D) := by
    exact (hFn_cont n).continuousOn.integrableOn_compact hclosed_compact |>.mono_set hD_closed
  have huVecD : MemLp u (2 : ℝ≥0∞) (volume.restrict D) :=
    MemLp.of_eval huD
  have hvVecD (n : ℕ) : MemLp (v n) (2 : ℝ≥0∞) (volume.restrict D) :=
    MemLp.of_eval (hvD n)
  have hvec_e : Tendsto
      (fun n => eLpNorm (fun x => v n x - u x) (2 : ℝ≥0∞)
        (volume.restrict D)) atTop (nhds 0) := by
    have hsum : Tendsto
        (fun n => ∑ i : Fin 3, eLpNorm (fun x => v n x i - u x i)
          (2 : ℝ≥0∞) (volume.restrict D)) atTop (nhds 0) := by
      simpa using tendsto_finsetSum (s := (Finset.univ : Finset (Fin 3)))
        (fun i _ => hval_eD i)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall (fun _ => zero_le))
    filter_upwards [] with n
    have hmeas : AEStronglyMeasurable (fun x => v n x - u x)
        (volume.restrict D) := (hvVecD n).sub huVecD |>.aestronglyMeasurable
    calc
      eLpNorm (fun x => v n x - u x) (2 : ℝ≥0∞) (volume.restrict D) ≤
          ∑ i : Fin 3, eLpNorm (fun x => (v n x - u x) i)
            (2 : ℝ≥0∞) (volume.restrict D) := eLpNorm_vec3_le_sum hmeas
      _ = ∑ i : Fin 3, eLpNorm (fun x => v n x i - u x i)
            (2 : ℝ≥0∞) (volume.restrict D) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply eLpNorm_congr_ae
        filter_upwards [] with x
        rfl
  obtain ⟨ns, hns_mono, hns_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (μ := volume.restrict D)
      (p := (2 : ℝ≥0∞)) (by norm_num) hvec_e).exists_seq_tendsto_ae
  have hq_ae : ∀ᵐ x ∂volume.restrict D,
      Tendsto (fun k => qn (ns k) x) atTop (nhds (q x)) := by
    filter_upwards [hns_ae] with x hx
    have hvx : Tendsto (fun k => v (ns k) x) atTop (nhds (u x)) := hx
    have hn := (continuous_vec3EuclideanNorm.tendsto (u x)).comp hvx
    simpa [q, qn] using hn.pow 2
  have havg_seq : Tendsto (fun k => av (ns k)) atTop (nhds av₀) :=
    havg_limit.comp (hns_mono.tendsto_atTop)
  have hFn_ae : ∀ᵐ x ∂volume.restrict D,
      Tendsto (fun k => Fn (ns k) x) atTop (nhds (F x)) := by
    filter_upwards [hq_ae] with x hx
    have hsub := (hx.sub havg_seq)
    have habs := (continuous_abs.tendsto (q x - av₀)).comp hsub
    have habs' : Tendsto (fun k => |qn (ns k) x - av (ns k)|) atTop
        (nhds |q x - av₀|) := by
      simpa [Function.comp_def] using habs
    have hpair : Tendsto
        (fun k => (|qn (ns k) x - av (ns k)|, (3 / 2 : ℝ))) atTop
          (nhds (|q x - av₀|, (3 / 2 : ℝ))) :=
      by simpa only [nhds_prod_eq] using habs'.prodMk (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (3 / 2 : ℝ)) atTop (nhds (3 / 2 : ℝ)))
    have hp := (Real.continuousAt_rpow_of_pos (|q x - av₀|, (3 / 2 : ℝ))
      (by norm_num)).tendsto.comp hpair
    simpa [Function.comp_def, F, Fn] using hp
  have hRhs : Tendsto
      (fun n => poincareSobolevL1VectorConstant *
        (∫ x in D, qn n x ∂volume) ^ (1 / 2 : ℝ) *
        (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (w n x i j) ^ 2 ∂volume) ^
          (1 / 2 : ℝ)) atTop (nhds
        (poincareSobolevL1VectorConstant *
          (∫ x in D, q x ∂volume) ^ (1 / 2 : ℝ) *
          (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (g x i j) ^ 2 ∂volume) ^
            (1 / 2 : ℝ))) := by
    have hqroot := (Real.continuous_sqrt.tendsto _).comp hq_limit
    have hgroot := (Real.continuous_sqrt.tendsto _).comp hgrad_int_limit
    simpa [Real.sqrt_eq_rpow] using (tendsto_const_nhds.mul hqroot).mul hgroot
  have hseq (k : ℕ) :
      ∫ x in D, Fn (ns k) x ∂volume ≤
        (poincareSobolevL1VectorConstant *
          (∫ x in D, qn (ns k) x ∂volume) ^ (1 / 2 : ℝ) *
          (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (w (ns k) x i j) ^ 2 ∂volume) ^
            (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) := by
    have hs := hsmooth (ns k)
    have hnonneg : 0 ≤ ∫ x in D, Fn (ns k) x ∂volume := by
      apply integral_nonneg_of_ae
      exact Filter.Eventually.of_forall (fun x =>
        Real.rpow_nonneg (abs_nonneg _) _)
    have hleft_nonneg : 0 ≤
        (∫ x in D, Fn (ns k) x ∂volume) ^ (2 / 3 : ℝ) :=
      Real.rpow_nonneg hnonneg _
    have hrpow := Real.rpow_le_rpow hleft_nonneg hs
      (by norm_num : 0 ≤ (3 / 2 : ℝ))
    calc
      ∫ x in D, Fn (ns k) x ∂volume =
          ((∫ x in D, Fn (ns k) x ∂volume) ^ (2 / 3 : ℝ)) ^
            (3 / 2 : ℝ) := by
              rw [← Real.rpow_mul hnonneg]
              norm_num
      _ ≤ (poincareSobolevL1VectorConstant *
          (∫ x in D, qn (ns k) x ∂volume) ^ (1 / 2 : ℝ) *
          (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (w (ns k) x i j) ^ 2 ∂volume) ^
            (1 / 2 : ℝ)) ^ (3 / 2 : ℝ) := by
              simpa [Fn, qn, av] using hrpow
  have hRhs_seq : Tendsto
      (fun k => poincareSobolevL1VectorConstant *
        (∫ x in D, qn (ns k) x ∂volume) ^ (1 / 2 : ℝ) *
        (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (w (ns k) x i j) ^ 2 ∂volume) ^
          (1 / 2 : ℝ)) atTop (nhds
        (poincareSobolevL1VectorConstant *
          (∫ x in D, q x ∂volume) ^ (1 / 2 : ℝ) *
          (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (g x i j) ^ 2 ∂volume) ^
            (1 / 2 : ℝ))) :=
    hRhs.comp hns_mono.tendsto_atTop
  by_cases hF : Integrable F (volume.restrict D)
  · have hfatou' := MeasureTheory.lintegral_liminf_le'
      (μ := volume.restrict D) (u := (atTop : Filter ℕ))
      (f := fun k => fun x => ‖Fn (ns k) x‖ₑ)
      (fun k => (hFn_cont (ns k)).aestronglyMeasurable.aemeasurable.enorm)
    have hfatou :
        (∫⁻ x, ‖F x‖ₑ ∂(volume.restrict D)) ≤
          Filter.liminf
            (fun k => ∫⁻ x, ‖Fn (ns k) x‖ₑ ∂(volume.restrict D)) atTop := by
      calc
        (∫⁻ x, ‖F x‖ₑ ∂(volume.restrict D)) =
            ∫⁻ x, Filter.liminf (fun k => ‖Fn (ns k) x‖ₑ) atTop
              ∂(volume.restrict D) := by
                apply MeasureTheory.lintegral_congr_ae
                filter_upwards [hFn_ae] with x hx
                exact hx.enorm.liminf_eq.symm
        _ ≤ _ := hfatou'
    have hF_enorm :
        (∫⁻ x, ‖F x‖ₑ ∂(volume.restrict D)) =
          ENNReal.ofReal (∫ x, F x ∂(volume.restrict D)) := by
      calc
        (∫⁻ x, ‖F x‖ₑ ∂(volume.restrict D)) =
            ENNReal.ofReal (∫ x, ‖F x‖ ∂(volume.restrict D)) := by
              exact (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hF).symm
        _ = ENNReal.ofReal (∫ x, F x ∂(volume.restrict D)) := by
              congr 1
              apply integral_congr_ae
              filter_upwards [] with x
              rw [Real.norm_eq_abs,
                abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    have hFn_enorm (k : ℕ) :
        (∫⁻ x, ‖Fn (ns k) x‖ₑ ∂(volume.restrict D)) =
          ENNReal.ofReal (∫ x, Fn (ns k) x ∂(volume.restrict D)) := by
      calc
        (∫⁻ x, ‖Fn (ns k) x‖ₑ ∂(volume.restrict D)) =
            ENNReal.ofReal (∫ x, ‖Fn (ns k) x‖ ∂(volume.restrict D)) := by
              exact (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm
                (hFn_int (ns k))).symm
        _ = ENNReal.ofReal (∫ x, Fn (ns k) x ∂(volume.restrict D)) := by
              congr 1
              apply integral_congr_ae
              filter_upwards [] with x
              rw [Real.norm_eq_abs,
                abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    rw [hF_enorm] at hfatou
    have hright_eq :
        (fun k => ∫⁻ x, ‖Fn (ns k) x‖ₑ ∂(volume.restrict D)) =
          (fun k => ENNReal.ofReal (∫ x, Fn (ns k) x ∂(volume.restrict D))) := by
      funext k
      exact hFn_enorm k
    rw [hright_eq] at hfatou
    let B : ℝ := poincareSobolevL1VectorConstant *
      (∫ x in D, q x ∂volume) ^ (1 / 2 : ℝ) *
      (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (g x i j) ^ 2 ∂volume) ^
        (1 / 2 : ℝ)
    have hB : 0 ≤ B := by
      dsimp [B]
      rw [poincareSobolevL1VectorConstant]
      positivity
    have hRhsPow : Tendsto
        (fun k =>
          (poincareSobolevL1VectorConstant *
            (∫ x in D, qn (ns k) x ∂volume) ^ (1 / 2 : ℝ) *
            (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3,
              (w (ns k) x i j) ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^
              (3 / 2 : ℝ)) atTop (nhds (B ^ (3 / 2 : ℝ))) := by
      have hpow := (Real.continuous_rpow_const
        (by norm_num : 0 ≤ (3 / 2 : ℝ))).tendsto B |>.comp hRhs_seq
      simpa [B, Function.comp_def] using hpow
    have hRhsPowEnn : Tendsto
        (fun k => ENNReal.ofReal
          ((poincareSobolevL1VectorConstant *
            (∫ x in D, qn (ns k) x ∂volume) ^ (1 / 2 : ℝ) *
            (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3,
              (w (ns k) x i j) ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^
                (3 / 2 : ℝ))) atTop
          (nhds (ENNReal.ofReal (B ^ (3 / 2 : ℝ)))) := by
      have h := (ENNReal.continuous_ofReal.tendsto
        (B ^ (3 / 2 : ℝ))).comp hRhsPow
      simpa only [Function.comp_def] using h
    have hseq_enn (k : ℕ) :
        ENNReal.ofReal (∫ x in D, Fn (ns k) x ∂volume) ≤
          ENNReal.ofReal
            ((poincareSobolevL1VectorConstant *
              (∫ x in D, qn (ns k) x ∂volume) ^ (1 / 2 : ℝ) *
              (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3,
                (w (ns k) x i j) ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^
              (3 / 2 : ℝ)) :=
      ENNReal.ofReal_le_ofReal (hseq k)
    have hliminf := Filter.liminf_le_liminf
      (f := (atTop : Filter ℕ))
      (u := fun k => ENNReal.ofReal
        ((poincareSobolevL1VectorConstant *
          (∫ x in D, qn (ns k) x ∂volume) ^ (1 / 2 : ℝ) *
          (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3,
            (w (ns k) x i j) ^ 2 ∂volume) ^ (1 / 2 : ℝ)) ^ (3 / 2 : ℝ)))
      (v := fun k => ENNReal.ofReal (∫ x in D, Fn (ns k) x ∂volume))
      (Filter.Eventually.of_forall hseq_enn)
    have hEnn : ENNReal.ofReal (∫ x in D, F x ∂volume) ≤
        ENNReal.ofReal (B ^ (3 / 2 : ℝ)) := by
      exact hfatou.trans (hliminf.trans_eq hRhsPowEnn.liminf_eq)
    have hreal : ∫ x in D, F x ∂volume ≤ B ^ (3 / 2 : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff
        (Real.rpow_nonneg hB _)).mp hEnn
    have hInt_nonneg : 0 ≤ ∫ x in D, F x ∂volume := by
      apply integral_nonneg_of_ae
      exact Filter.Eventually.of_forall (fun x =>
        Real.rpow_nonneg (abs_nonneg _) _)
    have hroot := Real.rpow_le_rpow hInt_nonneg hreal
      (by norm_num : 0 ≤ (2 / 3 : ℝ))
    have hgoal :
        (∫ x in D, F x ∂volume) ^ (2 / 3 : ℝ) ≤ B := by
      calc
        (∫ x in D, F x ∂volume) ^ (2 / 3 : ℝ) ≤
            (B ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := hroot
        _ = B := by
          rw [← Real.rpow_mul hB]
          norm_num
    simpa [D, F, q, av₀, B] using hgoal
  · let B : ℝ := poincareSobolevL1VectorConstant *
      (∫ x in D, q x ∂volume) ^ (1 / 2 : ℝ) *
      (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (g x i j) ^ 2 ∂volume) ^
        (1 / 2 : ℝ)
    have hB : 0 ≤ B := by
      dsimp [B]
      rw [poincareSobolevL1VectorConstant]
      positivity
    have hgoal : (∫ x in D, F x ∂volume) ^ (2 / 3 : ℝ) ≤ B := by
      rw [MeasureTheory.integral_undef hF]
      simp only [Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
      exact hB
    simpa [D, F, q, av₀, B] using hgoal

end
end CKN
