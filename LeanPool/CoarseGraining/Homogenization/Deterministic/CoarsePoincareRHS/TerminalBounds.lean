/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.AbsorbedErrors

/-! # Terminal Bounds -/

namespace Homogenization

noncomputable section

theorem memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet {d : ℕ}
    (Q : TriadicCube d) {f : Vec d → Vec d}
    (hf : MemVectorL2 (cubeSet Q) f) :
    MeasureTheory.MemLp f (2 : ENNReal) (normalizedCubeMeasure Q) := by
  have hfCube :
      MeasureTheory.MemLp f (2 : ENNReal) (MeasureTheory.volume.restrict (cubeSet Q)) := by
    simpa [MemVectorL2, volumeMeasureOn] using hf
  exact
    hfCube.of_measure_le_smul (c := ENNReal.ofReal ((cubeVolume Q)⁻¹))
      ENNReal.ofReal_ne_top (by rw [normalizedCubeMeasure, cubeMeasure])

theorem memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure {d : ℕ}
    (Q : TriadicCube d) {f : Vec d → Vec d}
    (hf : MeasureTheory.MemLp f (2 : ENNReal) (normalizedCubeMeasure Q)) :
    MemVectorL2 (cubeSet Q) f := by
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
      change
        ENNReal.ofReal (cubeVolume Q) *
            (ENNReal.ofReal ((cubeVolume Q)⁻¹) * (cubeMeasure Q) s) =
          (cubeMeasure Q) s
      rw [← mul_assoc, hmul, one_mul]
    exact le_of_eq heq.symm
  have hfCube :
      MeasureTheory.MemLp f (2 : ENNReal) (cubeMeasure Q) :=
    hf.of_measure_le_smul (c := ENNReal.ofReal (cubeVolume Q))
      ENNReal.ofReal_ne_top hle
  simpa [MemVectorL2, volumeMeasureOn, cubeMeasure] using hfCube

theorem cubeBesovNegativeVectorDepthAverage_eq_sum_components {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthAverage Q u j =
      ∑ i : Fin d,
        cubeBesovCircDepthAverage Q (2 : ENNReal) (fun x => u x i) j := by
  let D := descendantsAtDepth Q j
  unfold cubeBesovNegativeVectorDepthAverage cubeBesovCircDepthAverage descendantsAverage
  change ((D.card : ℝ)⁻¹) * ∑ R ∈ D, vecNormSq (cubeAverageVec R u) =
    ∑ i : Fin d,
      ((D.card : ℝ)⁻¹) *
        ∑ R ∈ D, ‖cubeAverage R (fun x => u x i)‖ ^ (ENNReal.toReal (2 : ENNReal))
  rw [← Finset.mul_sum]
  congr 1
  calc
    ∑ R ∈ D, vecNormSq (cubeAverageVec R u) =
        ∑ R ∈ D, ∑ i : Fin d, (cubeAverage R (fun x => u x i)) ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro R hR
          simp [cubeAverageVec, vecNormSq, vecDot, pow_two]
    _ = ∑ i : Fin d, ∑ R ∈ D, (cubeAverage R (fun x => u x i)) ^ (2 : ℕ) := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin d,
          ∑ R ∈ D, ‖cubeAverage R (fun x => u x i)‖ ^ (ENNReal.toReal (2 : ENNReal)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro R hR
          simp [Real.norm_eq_abs, pow_two]

theorem cubeBesovNegativeVectorDepthAverage_le_cubeAverage_vecNormSq_of_memLp {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → Vec d) (j : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    cubeBesovNegativeVectorDepthAverage Q u j ≤
      cubeAverage Q (fun x => vecNormSq (u x)) := by
  rw [cubeBesovNegativeVectorDepthAverage_eq_sum_components Q u j]
  have hcomponent :
      ∀ i : Fin d,
        cubeBesovCircDepthAverage Q (2 : ENNReal) (fun x => u x i) j ≤
          cubeAverage Q (fun x => (u x i) ^ (2 : ℕ)) := by
    intro i
    have hui :
        MeasureTheory.MemLp (fun x => u x i) (2 : ENNReal) (normalizedCubeMeasure Q) := by
      simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
    have hle :=
      cubeBesovCircDepthAverage_le_cubeLpNorm_rpow
        (Q := Q) (p := (2 : ENNReal)) (u := fun x => u x i) (j := j)
        (by norm_num) (by norm_num) hui
    have hLp :
        (cubeLpNorm Q (2 : ENNReal) (fun x => u x i)) ^ (ENNReal.toReal (2 : ENNReal)) =
          cubeAverage Q (fun x => ‖u x i‖ ^ (2 : ℝ)) := by
      simpa using
        (cubeLpNorm_rpow_eq_cubeAverage_norm_rpow
          (Q := Q) (p := (2 : ENNReal)) (f := fun x => u x i)
          (by norm_num) (by norm_num) hui)
    rw [hLp] at hle
    simpa [Real.norm_eq_abs, sq_abs, pow_two] using hle
  calc
    ∑ i : Fin d,
        cubeBesovCircDepthAverage Q (2 : ENNReal) (fun x => u x i) j
        ≤ ∑ i : Fin d, cubeAverage Q (fun x => (u x i) ^ (2 : ℕ)) := by
          exact Finset.sum_le_sum fun i hi => hcomponent i
    _ = cubeAverage Q (fun x => vecNormSq (u x)) := by
          have hInt :
              ∀ i : Fin d,
                MeasureTheory.Integrable (fun x => u x i * u x i)
                  (normalizedCubeMeasure Q) := by
            intro i
            have hui :
                MeasureTheory.MemLp (fun x => u x i) (2 : ENNReal)
                  (normalizedCubeMeasure Q) := by
              simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
            have hint :
                MeasureTheory.Integrable (fun x => ‖u x i‖ ^ (2 : ℝ))
                  (normalizedCubeMeasure Q) :=
              hui.integrable_norm_rpow (by norm_num) (by norm_num)
            simpa [Real.norm_eq_abs, sq_abs, pow_two] using hint
          have hsum := cubeAverage_vecDot_eq_sum_cubeBesovPairing Q u u hInt
          symm
          simpa [cubeBesovPairing, vecNormSq, vecDot, pow_two] using hsum

theorem sq_cubeBesovNegativeVectorPartialSeminormTwo_le_l2Average_of_memLp {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤
      (geometricDiscount s 2)⁻¹ * cubeAverage Q (fun x => vecNormSq (u x)) := by
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hdisc_nonneg : 0 ≤ (geometricDiscount s 2)⁻¹ := by
    exact inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2))
  have henergy_nonneg : 0 ≤ cubeAverage Q (fun x => vecNormSq (u x)) := by
    exact cubeAverage_nonneg_of_nonneg_on fun x hx => vecNormSq_nonneg (u x)
  have hweight_nonneg :
      ∀ j : ℕ, 0 ≤ Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) := by
    intro j
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hdepth :
      ∀ j ∈ Finset.range (N + 1),
        (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2 ≤
      Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) *
            cubeAverage Q (fun x => vecNormSq (u x)) := by
    intro j hj
    rw [sq_cubeBesovNegativeVectorDepthSeminorm]
    have havg :=
      cubeBesovNegativeVectorDepthAverage_le_cubeAverage_vecNormSq_of_memLp
        Q u j hu
    have hpow :
        (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
          Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) := by
      have h3 : 0 < (3 : ℝ) := by norm_num
      calc
        (Real.rpow (3 : ℝ) (-s * (j : ℝ))) ^ 2 =
            Real.rpow (3 : ℝ) (-s * (j : ℝ)) *
              Real.rpow (3 : ℝ) (-s * (j : ℝ)) := by
              ring
        _ = Real.rpow (3 : ℝ) ((-s * (j : ℝ)) + (-s * (j : ℝ))) := by
              exact (Real.rpow_add h3 (-s * (j : ℝ)) (-s * (j : ℝ))).symm
        _ = Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) := by
              congr 1
              ring
    rw [hpow]
    exact mul_le_mul_of_nonneg_left havg (hweight_nonneg j)
  rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
  calc
    ∑ j ∈ Finset.range (N + 1),
        (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2
        ≤ ∑ j ∈ Finset.range (N + 1),
            Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) *
              cubeAverage Q (fun x => vecNormSq (u x)) := by
          exact Finset.sum_le_sum hdepth
    _ = (∑ j ∈ Finset.range (N + 1),
            Real.rpow (3 : ℝ) (-2 * s * (j : ℝ))) *
          cubeAverage Q (fun x => vecNormSq (u x)) := by
          rw [Finset.sum_mul]
    _ ≤ (geometricDiscount s 2)⁻¹ *
          cubeAverage Q (fun x => vecNormSq (u x)) := by
          have hfinite_le :
              ∑ j ∈ Finset.range (N + 1), Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) ≤
                (geometricDiscount s 2)⁻¹ := by
            have hcoeff_nonneg :
                ∀ n : ℕ, 0 ≤ geometricWeight s 2 n := by
              intro n
              exact geometricWeight_nonneg n (by nlinarith [hs.le])
            have hsum_le :
                ∑ j ∈ Finset.range (N + 1), geometricWeight s 2 j ≤
                  ∑' n : ℕ, geometricWeight s 2 n := by
              exact (summable_geometricWeight hs2).sum_le_tsum
                (Finset.range (N + 1)) (fun n hn => hcoeff_nonneg n)
            have hrewrite :
                ∑ j ∈ Finset.range (N + 1), Real.rpow (3 : ℝ) (-2 * s * (j : ℝ)) =
                  (geometricDiscount s 2)⁻¹ *
                    ∑ j ∈ Finset.range (N + 1), geometricWeight s 2 j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [rpow_neg_two_mul_s_nat_eq_inv_geometricDiscount_mul_geometricWeight_two hs j]
            rw [hrewrite]
            calc
              (geometricDiscount s 2)⁻¹ *
                  ∑ j ∈ Finset.range (N + 1), geometricWeight s 2 j
                  ≤ (geometricDiscount s 2)⁻¹ *
                      ∑' n : ℕ, geometricWeight s 2 n := by
                    exact mul_le_mul_of_nonneg_left hsum_le hdisc_nonneg
              _ = (geometricDiscount s 2)⁻¹ := by
                    rw [tsum_geometricWeight_eq_one hs2]
                    ring
          exact mul_le_mul_of_nonneg_right hfinite_le henergy_nonneg

theorem sq_cubeBesovNegativeVectorSeminormTwo_le_l2Average_of_memLp {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    (cubeBesovNegativeVectorSeminormTwo Q s u) ^ 2 ≤
      (geometricDiscount s 2)⁻¹ * cubeAverage Q (fun x => vecNormSq (u x)) := by
  have henergy_nonneg : 0 ≤ cubeAverage Q (fun x => vecNormSq (u x)) := by
    exact cubeAverage_nonneg_of_nonneg_on fun x hx => vecNormSq_nonneg (u x)
  have hB_nonneg :
      0 ≤ (geometricDiscount s 2)⁻¹ * cubeAverage Q (fun x => vecNormSq (u x)) := by
    exact mul_nonneg
      (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos (by nlinarith [hs]))))
      henergy_nonneg
  exact
    sq_cubeBesovNegativeVectorSeminormTwo_le_of_partialSqBound
      (Q := Q) (s := s) (u := u) hB_nonneg
      (fun N =>
        sq_cubeBesovNegativeVectorPartialSeminormTwo_le_l2Average_of_memLp
          Q hs u N hu)

theorem cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N u) := by
  let B : ℝ := (geometricDiscount s 2)⁻¹ * cubeAverage Q (fun x => vecNormSq (u x))
  have henergy_nonneg : 0 ≤ cubeAverage Q (fun x => vecNormSq (u x)) := by
    exact cubeAverage_nonneg_of_nonneg_on fun x hx => vecNormSq_nonneg (u x)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos (by nlinarith [hs]))))
      henergy_nonneg
  refine ⟨Real.sqrt B, ?_⟩
  rintro x ⟨N, rfl⟩
  have hpartial_nonneg :
      0 ≤ cubeBesovNegativeVectorPartialSeminormTwo Q s N u :=
    cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s N u
  have hsquare :
      (cubeBesovNegativeVectorPartialSeminormTwo Q s N u) ^ 2 ≤
        (Real.sqrt B) ^ 2 := by
    simpa [B, Real.sq_sqrt hB_nonneg] using
      sq_cubeBesovNegativeVectorPartialSeminormTwo_le_l2Average_of_memLp
        Q hs u N hu
  have habs :
      |cubeBesovNegativeVectorPartialSeminormTwo Q s N u| ≤ |Real.sqrt B| :=
    sq_le_sq.mp hsquare
  simpa [abs_of_nonneg hpartial_nonneg, abs_of_nonneg (Real.sqrt_nonneg B)] using habs

theorem cubeBesovNegativeVectorPartialSeminorm_bddAbove_of_memLp {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminorm Q s N u) := by
  have hs_half : 0 < s / 2 := by linarith
  have hgap : 0 < s - s / 2 := by linarith
  rcases cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp
      Q hs_half u hu with
    ⟨B₂, hB₂⟩
  let K : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (s - s / 2)))⁻¹)
  refine ⟨K * max B₂ 0, ?_⟩
  rintro x ⟨N, rfl⟩
  have hq12 :
      cubeBesovNegativeVectorPartialSeminorm Q s N u ≤
        K * cubeBesovNegativeVectorPartialSeminormTwo Q (s / 2) N u := by
    simpa [K] using
      cubeBesovNegativeVectorPartialSeminorm_le_gap_geometric_mul_partialSeminormTwo
        Q hgap N u
  have htwo_le :
      cubeBesovNegativeVectorPartialSeminormTwo Q (s / 2) N u ≤ max B₂ 0 :=
    (hB₂ ⟨N, rfl⟩).trans (le_max_left B₂ 0)
  exact hq12.trans
    (mul_le_mul_of_nonneg_left htwo_le (Real.sqrt_nonneg _))

theorem cubeBesovNegativeVectorSeminormTwo_nonneg_of_memLp {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    0 ≤ cubeBesovNegativeVectorSeminormTwo Q s u :=
  cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove Q s u <|
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs u hu

theorem cubeBesovNegativeVectorSeminorm_nonneg_of_memLp {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    0 ≤ cubeBesovNegativeVectorSeminorm Q s u :=
  cubeBesovNegativeVectorSeminorm_nonneg_of_bddAbove Q s u <|
    cubeBesovNegativeVectorPartialSeminorm_bddAbove_of_memLp Q hs u hu

theorem cubeBesovNegativeVectorPartialSeminorm_le_seminorm_of_memLp {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d)
    (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    cubeBesovNegativeVectorPartialSeminorm Q s N u ≤
      cubeBesovNegativeVectorSeminorm Q s u :=
  cubeBesovNegativeVectorPartialSeminorm_le_seminorm_of_bddAbove Q s u
    (cubeBesovNegativeVectorPartialSeminorm_bddAbove_of_memLp Q hs u hu) N

theorem cubeBesovScaleWeight_mul_cubeBesovNegativeVectorPartialSeminorm_le_mul_cubeBesovNegativeVectorSeminorm_of_memLp
    {d : ℕ} (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (w : ℝ)
    (u : Vec d → Vec d) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    cubeBesovScaleWeight w Q * cubeBesovNegativeVectorPartialSeminorm Q s N u ≤
      cubeBesovScaleWeight w Q * cubeBesovNegativeVectorSeminorm Q s u :=
  mul_le_mul_of_nonneg_left
    (cubeBesovNegativeVectorPartialSeminorm_le_seminorm_of_memLp Q hs u N hu)
    (cubeBesovScaleWeight_nonneg w Q)

theorem coarsePoincareRHSSn_le_l2Average_of_memLp {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d) (n : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    coarsePoincareRHSSn Q s u n ≤
      (geometricDiscount s 2)⁻¹ * cubeAverage Q (fun x => vecNormSq (u x)) := by
  have hdesc :
      descendantsAverage Q n
          (fun R => (cubeBesovNegativeVectorSeminormTwo R s u) ^ 2) ≤
        descendantsAverage Q n
          (fun R => (geometricDiscount s 2)⁻¹ *
            cubeAverage R (fun x => vecNormSq (u x))) := by
    refine descendantsAverage_le_descendantsAverage Q n ?_
    intro R hR
    have huR :
        MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure R) :=
      memLp_on_descendant_of_memLp_generic (E := Vec d) hR hu
    exact sq_cubeBesovNegativeVectorSeminormTwo_le_l2Average_of_memLp R hs u huR
  have henergy_int :
      MeasureTheory.IntegrableOn (fun x => vecNormSq (u x)) (cubeSet Q)
        MeasureTheory.volume := by
    have hInt :
        ∀ i : Fin d,
          MeasureTheory.Integrable (fun x => u x i * u x i)
            (normalizedCubeMeasure Q) := by
      intro i
      have hui :
          MeasureTheory.MemLp (fun x => u x i) (2 : ENNReal) (normalizedCubeMeasure Q) := by
        simpa using! (ContinuousLinearMap.proj (R := ℝ) i).comp_memLp' hu
      have hint :
          MeasureTheory.Integrable (fun x => ‖u x i‖ ^ (2 : ℝ))
            (normalizedCubeMeasure Q) :=
        hui.integrable_norm_rpow (by norm_num) (by norm_num)
      simpa [Real.norm_eq_abs, sq_abs, pow_two] using hint
    have hvec_int :
        MeasureTheory.Integrable (fun x => vecNormSq (u x)) (normalizedCubeMeasure Q) := by
      have hsum_int :
          MeasureTheory.Integrable (fun x => ∑ i : Fin d, u x i * u x i)
            (normalizedCubeMeasure Q) := by
        exact MeasureTheory.integrable_finsetSum Finset.univ (fun i hi => hInt i)
      simpa [vecNormSq, vecDot] using hsum_int
    exact integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) hvec_int
  have hconst :
      descendantsAverage Q n
          (fun R => (geometricDiscount s 2)⁻¹ *
            cubeAverage R (fun x => vecNormSq (u x))) =
        (geometricDiscount s 2)⁻¹ *
          descendantsAverage Q n (fun R => cubeAverage R (fun x => vecNormSq (u x))) := by
    let D := descendantsAtDepth Q n
    let M := (geometricDiscount s 2)⁻¹
    unfold descendantsAverage
    calc
      ((D.card : ℝ)⁻¹) * ∑ R ∈ D,
          M * cubeAverage R (fun x => vecNormSq (u x)) =
        ∑ R ∈ D,
          (((D.card : ℝ)⁻¹ * M) * cubeAverage R (fun x => vecNormSq (u x))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro R hR
          ring
      _ = ((D.card : ℝ)⁻¹ * M) *
          ∑ R ∈ D, cubeAverage R (fun x => vecNormSq (u x)) := by
          simpa [mul_assoc] using
            (Finset.mul_sum (s := D)
              (f := fun R => cubeAverage R (fun x => vecNormSq (u x)))
              ((D.card : ℝ)⁻¹ * M)).symm
      _ = M * (((D.card : ℝ)⁻¹) *
          ∑ R ∈ D, cubeAverage R (fun x => vecNormSq (u x))) := by
          ring
  have hdesc_energy :
      descendantsAverage Q n (fun R => cubeAverage R (fun x => vecNormSq (u x))) =
        cubeAverage Q (fun x => vecNormSq (u x)) := by
    symm
    exact cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      Q n (fun x => vecNormSq (u x)) henergy_int
  have hRn :
      coarsePoincareRHSRn Q s u n ≤
        (geometricDiscount s 2)⁻¹ *
          cubeAverage Q (fun x => vecNormSq (u x)) := by
    unfold coarsePoincareRHSRn at hdesc ⊢
    simpa [hconst, hdesc_energy] using hdesc
  have hweight_le_one : coarsePoincareRHSDepthWeight s n ≤ 1 := by
    unfold coarsePoincareRHSDepthWeight
    have hbase_one : (1 : ℝ) = Real.rpow (3 : ℝ) 0 := by simp
    rw [hbase_one]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) (by nlinarith [hs.le])
  have hweight_nonneg : 0 ≤ coarsePoincareRHSDepthWeight s n := by
    unfold coarsePoincareRHSDepthWeight
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hRn_nonneg := coarsePoincareRHSRn_nonneg Q s u n
  have hB_nonneg :
      0 ≤ (geometricDiscount s 2)⁻¹ * cubeAverage Q (fun x => vecNormSq (u x)) := by
    have henergy_nonneg : 0 ≤ cubeAverage Q (fun x => vecNormSq (u x)) :=
      cubeAverage_nonneg_of_nonneg_on fun x hx => vecNormSq_nonneg (u x)
    exact mul_nonneg
      (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos (by nlinarith [hs]))))
      henergy_nonneg
  unfold coarsePoincareRHSSn
  calc
    coarsePoincareRHSDepthWeight s n * coarsePoincareRHSRn Q s u n
        ≤ 1 * coarsePoincareRHSRn Q s u n := by
          exact mul_le_mul_of_nonneg_right hweight_le_one hRn_nonneg
    _ ≤ 1 * ((geometricDiscount s 2)⁻¹ *
          cubeAverage Q (fun x => vecNormSq (u x))) := by
          exact mul_le_mul_of_nonneg_left hRn zero_le_one
    _ = (geometricDiscount s 2)⁻¹ * cubeAverage Q (fun x => vecNormSq (u x)) := by
          ring

theorem coarsePoincareRHSSn_bddAbove_of_memLp {d : ℕ}
    (Q : TriadicCube d) {s : ℝ} (hs : 0 < s) (u : Vec d → Vec d)
    (hu : MeasureTheory.MemLp u (2 : ENNReal) (normalizedCubeMeasure Q)) :
    BddAbove (Set.range fun n : ℕ => coarsePoincareRHSSn Q s u n) := by
  refine ⟨(geometricDiscount s 2)⁻¹ * cubeAverage Q (fun x => vecNormSq (u x)), ?_⟩
  rintro _ ⟨n, rfl⟩
  exact coarsePoincareRHSSn_le_l2Average_of_memLp Q hs u n hu


end

end Homogenization
