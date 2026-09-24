/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondWeakCountable

/-!
# Riesz Second Weak Exterior

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

private lemma star_open_complement (Q : DyadicIndex) :
    IsOpen (rieszSecondCubeStar Q)ᶜ := by
  apply isOpen_compl_iff.mpr
  have hc : Continuous (fun x : Vec3 =>
      vec3EuclideanNorm (x - dyadicCubeCenter Q.scale Q.corner)) := by
    unfold vec3EuclideanNorm
    fun_prop
  exact isClosed_Iic.preimage hc

private lemma cube_bounded_for_exterior (Q : DyadicIndex) :
    Bornology.IsBounded (dyadicCubeSet Q) := by
  obtain ⟨c, hc⟩ := dyadicCube_nonempty Q.scale Q.corner
  exact Metric.isBounded_closedBall.subset (dyadicCube_subset_closedBall hc)

private lemma vec3_euclidean_norm_le_sqrt_three (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hv : vec3EuclideanNorm v ^ 2 = ∑ k : Fin 3, v k ^ 2 := by
    unfold vec3EuclideanNorm
    exact Real.sq_sqrt (Finset.sum_nonneg (fun k _hk => sq_nonneg (v k)))
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    rw [hv, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      ∑ k : Fin 3, v k ^ 2 ≤ ∑ _k : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _hk
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v k) 2
      _ = 3 * ‖v‖ ^ 2 := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm v| ≤ |Real.sqrt 3 * ‖v‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg v),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))] at h2

private lemma cube_radius_for_exterior {Q : DyadicIndex}
    {y : Vec3} (hy : y ∈ dyadicCubeSet Q) :
    vec3EuclideanNorm (y - dyadicCubeCenter Q.scale Q.corner) ≤
      Real.sqrt 3 * (dyadicScale Q.scale / 2) := by
  have hs : 0 < dyadicScale Q.scale := dyadicScale_pos Q.scale
  have hsup : ‖y - dyadicCubeCenter Q.scale Q.corner‖ ≤
      dyadicScale Q.scale / 2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro k
    have hy' := (mem_dyadicCube.mp hy) k
    change |y k - dyadicCubeCenter Q.scale Q.corner k| ≤
      dyadicScale Q.scale / 2
    dsimp [dyadicCubeCenter]
    rw [abs_le]
    constructor <;> nlinarith only [hy'.1, hy'.2, hs]
  exact (vec3_euclidean_norm_le_sqrt_three (y -
    dyadicCubeCenter Q.scale Q.corner)).trans
    (mul_le_mul_of_nonneg_left hsup (by positivity))

private lemma cube_star_sep_for_exterior {Q : DyadicIndex}
    {x : Vec3} (hx : x ∈ (rieszSecondCubeStar Q)ᶜ) :
    ∀ y ∈ dyadicCubeSet Q,
      Real.sqrt 3 * (dyadicScale Q.scale / 2) ≤
        vec3EuclideanNorm (x - y) := by
  let c : Vec3 := dyadicCubeCenter Q.scale Q.corner
  let s : ℝ := dyadicScale Q.scale / 2
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos (dyadicScale_pos _) (by norm_num)
  have htri : ∀ u v : Vec3,
      vec3EuclideanNorm (u + v) ≤ vec3EuclideanNorm u + vec3EuclideanNorm v := by
    intro u v
    simp only [vec3EuclideanNorm_eq_l2, WithLp.toLp_add]
    exact norm_add_le _ _
  have hxstar : 2 * Real.sqrt 3 * s <
      vec3EuclideanNorm (x - c) := by
    exact lt_of_not_ge (by simpa [rieszSecondCubeStar, c, s] using hx)
  intro y hy
  have hyc : vec3EuclideanNorm (y - c) ≤ Real.sqrt 3 * s := by
    simpa [c, s] using cube_radius_for_exterior hy
  have htri' : vec3EuclideanNorm (x - c) ≤
      vec3EuclideanNorm (x - y) + vec3EuclideanNorm (y - c) := by
    have heq : x - c = (x - y) + (y - c) := by abel
    rw [heq]
    exact htri _ _
  dsimp [c, s] at hxstar hyc htri' ⊢
  linarith only [hxstar, hyc, htri']

theorem rieszSecond_exterior_operator_bad_bridge
    {i j : Fin 3} (hL2 : RieszSecondL2Input i j)
    {F : Vec3 → ℝ} {level : ℝ} (D : CZDecomposition F level)
    (hF₂ : MemLp F (2 : ℝ≥0∞) volume) {C_H : ℝ≥0∞}
    (hExterior : ∀ {b : Vec3 → ℝ} (hb₂ : MemLp b (2 : ℝ≥0∞) volume)
      {A U : Set Vec3}, IsOpen U → (∀ y ∉ A, b y = 0)
      → Bornology.IsBounded A → {δ : ℝ} → 0 < δ
      → (∀ x ∈ U, ∀ y ∈ A, δ ≤ vec3EuclideanNorm (x - y))
      → rieszSecondL2MeasurableOperator hL2 (MemLp.toLp b hb₂) =ᵐ[volume.restrict U]
        (fun x => ∫ y, rieszSecondPressureKernel i j (x - y) * b y))
    (hkernelBridge : ∀ Q : {Q // Q ∈ D.cubes},
      (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |∫ y,
          rieszSecondPressureKernel i j (x - y) * dyadicBadPart F Q.1 y|) ≤
        C_H * ∫⁻ y in dyadicCubeSet Q.1,
          ENNReal.ofReal |dyadicBadPart F Q.1 y|) :
    ∀ Q : {Q // Q ∈ D.cubes},
      (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |rieszSecondL2MeasurableOperator hL2
          (MemLp.toLp (dyadicBadPart F Q.1)
            (dyadic_bad_part_memLp_two D hF₂ Q)) x|) ≤
        C_H * ∫⁻ y in dyadicCubeSet Q.1,
          ENNReal.ofReal |dyadicBadPart F Q.1 y| := by
  intro Q
  let b : Vec3 → ℝ := dyadicBadPart F Q.1
  let δ : ℝ := Real.sqrt 3 * (dyadicScale Q.1.scale / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact mul_pos (Real.sqrt_pos.2 (by norm_num))
      (div_pos (dyadicScale_pos _) (by norm_num))
  have hsep : ∀ x ∈ (rieszSecondCubeStar Q.1)ᶜ,
      ∀ y ∈ dyadicCubeSet Q.1,
        δ ≤ vec3EuclideanNorm (x - y) := by
    intro x hx y hy
    simpa [δ] using cube_star_sep_for_exterior hx y hy
  have hrep := hExterior (b := b)
    (dyadic_bad_part_memLp_two D hF₂ Q)
    (star_open_complement Q.1)
    (fun y hy => Set.indicator_of_notMem hy _)
    (cube_bounded_for_exterior Q.1) hδ hsep
  have heq : (∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
      ENNReal.ofReal |rieszSecondL2MeasurableOperator hL2
        (MemLp.toLp b (dyadic_bad_part_memLp_two D hF₂ Q)) x|) =
      ∫⁻ x in (rieszSecondCubeStar Q.1)ᶜ,
        ENNReal.ofReal |∫ y, rieszSecondPressureKernel i j (x - y) * b y| := by
    apply lintegral_congr_ae
    filter_upwards [hrep] with x hx
    rw [hx]
  rw [heq]
  simpa only [b] using hkernelBridge Q

end CKN.Foundation.Euclidean
