/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.Fatou

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

private lemma poincareSobolevL1_vec3_slice_euclidean_hclosed_subset_1 :
    ∀ {U : Set Vec3} {x₀ : Vec3} {R r : ℝ},
      vec3Ball x₀ R ⊆ U →
        let t : ℝ := (R + r) / (2 : ℝ);
        let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
        let K : Set Vec3 := euclideanClosedBall x₀ t;
        t < R →
          (0 : ℝ) < t →
            (0 : ℝ) < √(3 : ℝ) →
              (∀ (z : Vec3), vec3EuclideanNorm z = vecEuclideanNorm z) →
                ∀ x ∈ K, Metric.closedBall x ε₀ ⊆ U
    := by
  intro U x₀ R r hball t ε₀ K htR ht_pos hsqrt hvecnorm_eq x hx y hy
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

private lemma poincareSobolevL1_vec3_slice_euclidean_hweakExt_2 :
    ∀ {U : Set Vec3},
      IsOpen U →
        ∀ (u : Vec3 → Vec3) (g : Vec3 → Fin (3 : ℕ) → Vec3),
          (∀ (i : Fin (3 : ℕ)),
              HasWeakGradientOn U (fun (x : Vec (3 : ℕ)) => u x i) fun (x : Vec (3 : ℕ)) => g x i) →
            ∀ (i j : Fin (3 : ℕ)),
              HasWeakPartialDerivOn U j (U.indicator fun (x : Vec3) => u x i)
                (U.indicator fun (x : Vec3) => g x i j)
    := by
  intro U hU u g hweak i j φ hφ hφCompact hφSupport
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

private lemma poincareSobolevL1_vec3_slice_euclidean_hvalue_eventually_3 :
    ∀ {U : Set Vec3} {x₀ : Vec3} {R r : ℝ},
      (0 : ℝ) < r →
        ∀ (u : Vec3 → Vec3),
          let t : ℝ := (R + r) / (2 : ℝ);
          let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
          let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
          let K : Set Vec3 := euclideanClosedBall x₀ t;
          let D : Set Vec3 := euclideanBall x₀ r;
          let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
          r < t →
            (0 : ℝ) < t →
              (0 : ℝ) < √(3 : ℝ) →
                ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
                  (∀ (n : ℕ), ε n ≤ ε₀) →
                    (∀ (z : Vec3), vec3EuclideanNorm z = vecEuclideanNorm z) →
                      (∀ (z : Vec3), ‖z‖ ≤ vec3EuclideanNorm z) →
                        S ⊆ U →
                          let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
                            mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
                          ∀ (n : ℕ) (i : Fin (3 : ℕ)) {x : Vec3},
                            x ∈ D →
                              (fun (y : Vec3) => v n y i) =ᶠ[𝓝 x]
                                mollify (U.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n)
    := by
  intro U x₀ R r hr u t ε₀ ε K D S ht ht_pos hsqrt hε_pos hε_le hvecnorm_eq hnorm_le_euclidean
    hS_sub_U v n i x hx
  have hxE : vec3EuclideanNorm (x - x₀) < t :=
    lt_trans (by
      rw [hvecnorm_eq]
      exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx) ht
  have hball' :=
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

private lemma poincareSobolevL1_vec3_slice_euclidean_hderiv_eq_4 :
    ∀ {U : Set Vec3},
      IsOpen U →
        ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3) (g : Vec3 → Fin (3 : ℕ) → Vec3),
          let t : ℝ := (R + r) / (2 : ℝ);
          let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
          let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
          let K : Set Vec3 := euclideanClosedBall x₀ t;
          let D : Set Vec3 := euclideanBall x₀ r;
          let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
          ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
            (∀ (n : ℕ), ε n ≤ ε₀) →
              IsCompact K →
                D ⊆ K →
                  S ⊆ U →
                    (∀ (i : Fin (3 : ℕ)),
                        LocallyIntegrable (ε := ℝ) (U.indicator fun (x : Vec3) => u x i) volume) →
                      (∀ (i j : Fin (3 : ℕ)),
                          LocallyIntegrable (ε := ℝ) (U.indicator fun (x : Vec3) => g x i j)
                            volume) →
                        (∀ (i j : Fin (3 : ℕ)),
                            HasWeakPartialDerivOn U j (U.indicator fun (x : Vec3) => u x i)
                              (U.indicator fun (x : Vec3) => g x i j)) →
                          let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
                            mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
                          let w : ℕ → Vec3 → Fin (3 : ℕ) → Vec3 :=
                            fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
                            mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x;
                          (∀ (n : ℕ), ∀ y ∈ K, Metric.closedBall y (ε n) ⊆ U) →
                            (∀ (n : ℕ) (i : Fin (3 : ℕ)) {x : Vec3},
                                x ∈ D →
                                  (fun (y : Vec3) => v n y i) =ᶠ[𝓝 x]
                                    mollify (U.indicator fun (y : Vec3) => u y i) (ε n)
                                      (hε_pos n)) →
                              ∀ (n : ℕ) (i j : Fin (3 : ℕ)) {x : Vec3},
                                x ∈ D →
                                  (fderiv ℝ (fun (y : Vec3) => v n y i) x : Vec3 → ℝ) (basisVec j) =
                                    w n x i j
    := by
  intro U hU x₀ R r u g t ε₀ ε K D S hε_pos hε_le hK_compact hD_sub_K hS_sub_U huExtLoc hgExtLoc
    hweakExt v w hclosed_subset_ε hvalue_eventually n i j x hx
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

private lemma poincareSobolevL1_vec3_slice_euclidean_hval_int_eq_limit_5 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
        (∀ (i : Fin (3 : ℕ)),
            MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => u x i)
              (2 : ℝ≥0∞) (Measure.restrict volume D)) →
          (∀ (i : Fin (3 : ℕ)),
              Tendsto (β := ℝ)
                (fun (n : ℕ) =>
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => v n x i ^ (2 : ℕ))
                atTop
                (𝓝
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => u x i ^ (2 : ℕ)))) →
            (∀ (z : Vec3), vec3EuclideanNorm z ^ (2 : ℕ) = ∑ i : Fin (3 : ℕ), z i ^ (2 : ℕ)) →
              (∀ (n : ℕ),
                  Eq (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => vec3EuclideanNorm (v n x) ^ (2 : ℕ))
                    (∑ i : Fin (3 : ℕ),
                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                        fun (x : Vec3) => v n x i ^ (2 : ℕ))) →
                Tendsto (β := ℝ)
                  (fun (n : ℕ) =>
                    @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => vec3EuclideanNorm (v n x) ^ (2 : ℕ))
                  atTop
                  (𝓝
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => vec3EuclideanNorm (u x) ^ (2 : ℕ)))
    := by
  intro x₀ R r u t ε₀ ε K D S hε_pos v huD hval_sq_int hvec_sq hval_int_eq
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

private lemma poincareSobolevL1_vec3_slice_euclidean_hgrad_int_eq_6 :
    ∀ {x₀ : Vec3} {R r : ℝ} (g : Vec3 → Fin (3 : ℕ) → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let w : ℕ → Vec3 → Fin (3 : ℕ) → Vec3 := fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x;
        (∀ (n : ℕ) (i j : Fin (3 : ℕ)),
            MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => w n x i j)
              (2 : ℝ≥0∞) (Measure.restrict volume D)) →
          ∀ (n : ℕ),
            Eq (α := ℝ)
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) => ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), w n x i j ^ (2 : ℕ))
              (∑ i : Fin (3 : ℕ),
                ∑ j : Fin (3 : ℕ),
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => w n x i j ^ (2 : ℕ))
    := by
  intro x₀ R r g t ε₀ ε K D S hε_pos w hwD n
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

private lemma poincareSobolevL1_vec3_slice_euclidean_hgrad_int_limit_7 :
    ∀ {x₀ : Vec3} {R r : ℝ} (g : Vec3 → Fin (3 : ℕ) → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let w : ℕ → Vec3 → Fin (3 : ℕ) → Vec3 := fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x;
        (∀ (i j : Fin (3 : ℕ)),
            MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => g x i j)
              (2 : ℝ≥0∞) (Measure.restrict volume D)) →
          (∀ (i j : Fin (3 : ℕ)),
              Tendsto (β := ℝ)
                (fun (n : ℕ) =>
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => w n x i j ^ (2 : ℕ))
                atTop
                (𝓝
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => g x i j ^ (2 : ℕ)))) →
            (∀ (n : ℕ),
                Eq (α := ℝ)
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), w n x i j ^ (2 : ℕ))
                  (∑ i : Fin (3 : ℕ),
                    ∑ j : Fin (3 : ℕ),
                      @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                        fun (x : Vec3) => w n x i j ^ (2 : ℕ))) →
              Tendsto (β := ℝ)
                (fun (n : ℕ) =>
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), w n x i j ^ (2 : ℕ))
                atTop
                (𝓝
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), g x i j ^ (2 : ℕ)))
    := by
  intro x₀ R r g t ε₀ ε K D S hε_pos w hgD hgrad_sq_int hgrad_int_eq
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

private lemma poincareSobolevL1_vec3_slice_euclidean_hvec_e_8 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
        (∀ (i : Fin (3 : ℕ)),
            Tendsto
              (fun (n : ℕ) =>
                @eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => v n x i - u x i)
                  (2 : ℝ≥0∞) (Measure.restrict volume D))
              atTop (𝓝 (0 : ℝ≥0∞))) →
          MemLp (m0 := MeasureSpace.toMeasurableSpace) u (2 : ℝ≥0∞) (Measure.restrict volume D) →
            (∀ (n : ℕ),
                MemLp (m0 := MeasureSpace.toMeasurableSpace) (v n) (2 : ℝ≥0∞)
                  (Measure.restrict volume D)) →
              Tendsto
                (fun (n : ℕ) =>
                  @eLpNorm _ Vec3 _ _ MeasureSpace.toMeasurableSpace (fun (x : Vec3) => v n x - u x)
                    (2 : ℝ≥0∞) (Measure.restrict volume D))
                atTop (𝓝 (0 : ℝ≥0∞))
    := by
  intro x₀ R r u t ε₀ ε K D S hε_pos v hval_eD huVecD hvVecD
  have hsum : Tendsto
      (fun n => ∑ i : Fin 3, eLpNorm (fun x => v n x i - u x i)
        (2 : ℝ≥0∞) (volume.restrict D)) atTop (nhds 0) := by
    simpa using tendsto_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun i _ => hval_eD i)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [] with n
  have hmeas :=
    (hvVecD n).sub huVecD |>.aestronglyMeasurable
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

private lemma poincareSobolevL1_vec3_slice_euclidean_hFn_ae_9 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
        let q : Vec3 → ℝ := fun (x : Vec3) => vec3EuclideanNorm (u x) ^ (2 : ℕ);
        let qn : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) => vec3EuclideanNorm (v n x) ^ (2 : ℕ);
        let av : ℕ → ℝ := fun (n : ℕ) => ⨍ (y : Vec3) in D, qn n y;
        let av₀ : ℝ := ⨍ (y : Vec3) in D, q y;
        let F : Vec3 → ℝ := fun (x : Vec3) => |q x - av₀| ^ (3 / 2 : ℝ);
        let Fn : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) => |qn n x - av n| ^ (3 / 2 : ℝ);
        ∀ (ns : ℕ → ℕ),
          (∀ᵐ (x : Vec3) ∂Measure.restrict volume D,
              Tendsto (fun (k : ℕ) => qn (ns k) x) atTop (𝓝 (q x))) →
            Tendsto (fun (k : ℕ) => av (ns k)) atTop (𝓝 av₀) →
              ∀ᵐ (x : Vec3) ∂Measure.restrict volume D,
                Tendsto (fun (k : ℕ) => Fn (ns k) x) atTop (𝓝 (F x))
    := by
  intro x₀ R r u t ε₀ ε K D S hε_pos v q qn av av₀ F Fn ns hq_ae havg_seq
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

private lemma poincareSobolevL1_vec3_slice_euclidean_hseq_10 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3) (g : Vec3 → Fin (3 : ℕ) → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
        let w : ℕ → Vec3 → Fin (3 : ℕ) → Vec3 := fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x;
        (∀ (n : ℕ),
            HPow.hPow (α := ℝ)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                  fun (x : Vec3) =>
                  |vec3EuclideanNorm (v n x) ^ (2 : ℕ) -
                        ⨍ (y : Vec3) in D, vec3EuclideanNorm (v n y) ^ (2 : ℕ)| ^
                    (3 / 2 : ℝ))
                (2 / 3 : ℝ) ≤
              poincareSobolevL1VectorConstant *
                  HPow.hPow (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => vec3EuclideanNorm (v n x) ^ (2 : ℕ))
                    (1 / 2 : ℝ) *
                HPow.hPow (α := ℝ)
                  (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), w n x i j ^ (2 : ℕ))
                  (1 / 2 : ℝ)) →
          let qn : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) => vec3EuclideanNorm (v n x) ^ (2 : ℕ);
          let av : ℕ → ℝ := fun (n : ℕ) => ⨍ (y : Vec3) in D, qn n y;
          let Fn : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) => |qn n x - av n| ^ (3 / 2 : ℝ);
          ∀ (ns : ℕ → ℕ) (k : ℕ),
            (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) => Fn (ns k) x) ≤
              (poincareSobolevL1VectorConstant *
                    HPow.hPow (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                        fun (x : Vec3) => qn (ns k) x)
                      (1 / 2 : ℝ) *
                  HPow.hPow (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) =>
                      ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), w (ns k) x i j ^ (2 : ℕ))
                    (1 / 2 : ℝ)) ^
                (3 / 2 : ℝ)
    := by
  intro x₀ R r u g t ε₀ ε K D S hε_pos v w hsmooth qn av Fn ns k
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

private lemma poincareSobolevL1_vec3_slice_euclidean_hε_le_1 :
    ∀ {R r : ℝ},
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      (0 : ℝ) < ε₀ → ∀ (n : ℕ), ε n ≤ ε₀
    := by
  intro R r t ε₀ ε hε₀_pos n
  dsimp [ε]
  have hden : 0 < (n : ℝ) + 1 := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith only [hε₀_pos.le, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

private lemma poincareSobolevL1_vec3_slice_euclidean_hε_tendsto_2 :
    ∀ {R r : ℝ},
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      Tendsto ε atTop (𝓝 (0 : ℝ))
    := by
  intro R r t ε₀ ε
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [add_comm] using
      (tendsto_atTop_add_const_left atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop :
          Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden
  simpa [ε, div_eq_mul_inv] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ε₀) atTop (nhds ε₀)).mul hinv)

private lemma poincareSobolevL1_vec3_slice_euclidean_hsqrtε_3 :
    ∀ {R r : ℝ},
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      (0 : ℝ) < √(3 : ℝ) → (∀ (n : ℕ), ε n ≤ ε₀) → ∀ (n : ℕ), √(3 : ℝ) * ε n ≤ (R - t) / (2 : ℝ)
    := by
  intro R r t ε₀ ε hsqrt hε_le n
  calc
    Real.sqrt 3 * ε n ≤ Real.sqrt 3 * ε₀ :=
      mul_le_mul_of_nonneg_left (hε_le n) hsqrt.le
    _ = (R - t) / 2 := by
      dsimp [ε₀]
      field_simp [ne_of_gt hsqrt]

private lemma poincareSobolevL1_vec3_slice_euclidean_hnorm_le_euclidean_4 :
    (∀ (z : Vec3), vec3EuclideanNorm z = vecEuclideanNorm z) →
      ∀ (z : Vec3), ‖z‖ ≤ vec3EuclideanNorm z
    := by
  intro hvecnorm_eq z
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖z i‖₊) ≤
      ⟨vecEuclideanNorm z, vecEuclideanNorm_nonneg z⟩ := by
    apply Finset.sup_le
    intro i hi
    exact abs_apply_le_vecEuclideanNorm z i
  rw [hvecnorm_eq]
  exact_mod_cast hnn

private lemma poincareSobolevL1_vec3_slice_euclidean_hK_sub_R_5 :
    ∀ {x₀ : Vec3} {R r : ℝ},
      let t : ℝ := (R + r) / (2 : ℝ);
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      t < R →
        (0 : ℝ) < t → (∀ (z : Vec3), vec3EuclideanNorm z = vecEuclideanNorm z) → K ⊆ vec3Ball x₀ R
    := by
  intro x₀ R r t K htR ht_pos hvecnorm_eq x hx
  apply mem_vec3Ball.2
  have hxE : vec3EuclideanNorm (x - x₀) ≤ t := by
    simpa [hvecnorm_eq] using
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le ht_pos.le).1 hx
  exact hxE.trans_lt htR

private lemma poincareSobolevL1_vec3_slice_euclidean_hD_sub_K_6 :
    ∀ {x₀ : Vec3} {R r : ℝ},
      (0 : ℝ) < r →
        let t : ℝ := (R + r) / (2 : ℝ);
        let K : Set Vec3 := euclideanClosedBall x₀ t;
        let D : Set Vec3 := euclideanBall x₀ r;
        r < t → (0 : ℝ) < t → (∀ (z : Vec3), vec3EuclideanNorm z = vecEuclideanNorm z) → D ⊆ K
    := by
  intro x₀ R r hr t K D ht ht_pos hvecnorm_eq x hx
  apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le ht_pos.le).2
  have hxE : vec3EuclideanNorm (x - x₀) < r := by
    rw [hvecnorm_eq]
    exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx
  simpa [hvecnorm_eq] using le_of_lt (hxE.trans ht)

private lemma poincareSobolevL1_vec3_slice_euclidean_hvMem_7 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        (∀ (i : Fin (3 : ℕ)),
            LocallyIntegrable (ε := ℝ) (S.indicator fun (x : Vec3) => u x i) volume) →
          let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
            mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
          (∀ (i : Fin (3 : ℕ)), HasCompactSupport (β := ℝ) (S.indicator fun (x : Vec3) => u x i)) →
            ∀ (n : ℕ) (i : Fin (3 : ℕ)),
              MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => v n x i)
                (2 : ℝ≥0∞) volume
    := by
  intro x₀ R r u t ε₀ ε K S hε_pos huLoc v hS_u_support n i
  apply (mollify_continuous (hε_pos n) (huLoc i)).memLp_of_hasCompactSupport
  change HasCompactSupport
    (mollify (S.indicator (fun y => u y i)) (ε n) (hε_pos n))
  simpa [mollify] using
    (mollifier_hasCompactSupport (hε_pos n)).convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (hS_u_support i)

private lemma poincareSobolevL1_vec3_slice_euclidean_hwMem_8 :
    ∀ {x₀ : Vec3} {R r : ℝ} (g : Vec3 → Fin (3 : ℕ) → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let w : ℕ → Vec3 → Fin (3 : ℕ) → Vec3 := fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x;
        (∀ (n : ℕ) (i j : Fin (3 : ℕ)), Continuous (Y := ℝ) fun (x : Vec3) => w n x i j) →
          (∀ (i j : Fin (3 : ℕ)),
              HasCompactSupport (β := ℝ) (S.indicator fun (x : Vec3) => g x i j)) →
            ∀ (n : ℕ) (i j : Fin (3 : ℕ)),
              MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => w n x i j)
                (2 : ℝ≥0∞) volume
    := by
  intro x₀ R r g t ε₀ ε K S hε_pos w hwCont hS_g_support n i j
  apply (hwCont n i j).memLp_of_hasCompactSupport
  change HasCompactSupport
    (mollify (S.indicator (fun y => g y i j)) (ε n) (hε_pos n))
  simpa [mollify] using
    (mollifier_hasCompactSupport (hε_pos n)).convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (hS_g_support i j)

private lemma poincareSobolevL1_vec3_slice_euclidean_hval_int_eq_9 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
        (∀ (n : ℕ) (i : Fin (3 : ℕ)),
            MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => v n x i)
              (2 : ℝ≥0∞) (Measure.restrict volume D)) →
          (∀ (z : Vec3), vec3EuclideanNorm z ^ (2 : ℕ) = ∑ i : Fin (3 : ℕ), z i ^ (2 : ℕ)) →
            ∀ (n : ℕ),
              Eq (α := ℝ)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                  fun (x : Vec3) => vec3EuclideanNorm (v n x) ^ (2 : ℕ))
                (∑ i : Fin (3 : ℕ),
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => v n x i ^ (2 : ℕ))
    := by
  intro x₀ R r u t ε₀ ε K D S hε_pos v hvD hvec_sq n
  rw [show (fun x => (vec3EuclideanNorm (v n x)) ^ 2) =
      (fun x => ∑ i : Fin 3, (v n x i) ^ 2) by
        funext x
        exact hvec_sq (v n x)]
  rw [integral_finsetSum]
  intro i hi
  simpa [Real.norm_eq_abs, sq_abs] using
    (hvD n i).integrable_norm_rpow (by norm_num) ENNReal.coe_ne_top

private lemma poincareSobolevL1_vec3_slice_euclidean_hderiv_int_eq_10 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3) (g : Vec3 → Fin (3 : ℕ) → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        MeasurableSet D →
          let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
            mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
          let w : ℕ → Vec3 → Fin (3 : ℕ) → Vec3 := fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
            mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x;
          (∀ (n : ℕ) (i j : Fin (3 : ℕ)) {x : Vec3},
              x ∈ D →
                Eq (α := ℝ)
                  ((fderiv ℝ
                          (fun (y : Vec3) =>
                            (fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
                                mollify
                                  ((euclideanClosedBall x₀ ((R + r) / (2 : ℝ)) +
                                        Metric.closedBall (0 : Vec3)
                                          ((R - (R + r) / (2 : ℝ)) /
                                            ((2 : ℝ) * √(3 : ℝ)))).indicator
                                    fun (y : Vec3) => u y i)
                                  ((fun (n : ℕ) =>
                                      (R - (R + r) / (2 : ℝ)) / ((2 : ℝ) * √(3 : ℝ)) /
                                        ((↑n : ℝ) + (1 : ℝ)))
                                    n)
                                  (hε_pos n) x)
                              n y i)
                          x :
                        Vec3 → ℝ)
                      (basisVec j) :
                    ℝ)
                  ((fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
                        mollify
                          ((euclideanClosedBall x₀ ((R + r) / (2 : ℝ)) +
                                Metric.closedBall (0 : Vec3)
                                  ((R - (R + r) / (2 : ℝ)) / ((2 : ℝ) * √(3 : ℝ)))).indicator
                            fun (y : Vec3) => g y i j)
                          ((fun (n : ℕ) =>
                              (R - (R + r) / (2 : ℝ)) / ((2 : ℝ) * √(3 : ℝ)) / ((↑n : ℝ) + (1 : ℝ)))
                            n)
                          (hε_pos n) x)
                      n x i j :
                    ℝ)) →
            ∀ (n : ℕ),
              Eq (α := ℝ)
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                  fun (x : Vec3) =>
                  ∑ i : Fin (3 : ℕ),
                    ∑ j : Fin (3 : ℕ),
                      HPow.hPow (α := ℝ)
                        ((fderiv ℝ (fun (y : Vec3) => v n y i) x : Vec3 → ℝ) (basisVec j) : ℝ)
                        (2 : ℕ))
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                  fun (x : Vec3) => ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), w n x i j ^ (2 : ℕ))
    := by
  intro x₀ R r u g t ε₀ ε K D S hε_pos hD_meas v w hderiv_eq n
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hD_meas] with x hx
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hderiv_eq n i j hx]

private lemma poincareSobolevL1_vec3_slice_euclidean_havg_limit_11 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
        let q : Vec3 → ℝ := fun (x : Vec3) => vec3EuclideanNorm (u x) ^ (2 : ℕ);
        let qn : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) => vec3EuclideanNorm (v n x) ^ (2 : ℕ);
        let av : ℕ → ℝ := fun (n : ℕ) => ⨍ (y : Vec3) in D, qn n y;
        let av₀ : ℝ := ⨍ (y : Vec3) in D, q y;
        Tendsto (β := ℝ)
            (fun (n : ℕ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) => qn n x)
            atTop
            (𝓝
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) => q x)) →
          (∀ (n : ℕ),
              av n =
                (ENNReal.toReal ((volume : Set Vec3 → ℝ≥0∞) D))⁻¹ *
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => qn n x) →
            (av₀ =
                (ENNReal.toReal ((volume : Set Vec3 → ℝ≥0∞) D))⁻¹ *
                  @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                    fun (x : Vec3) => q x) →
              Tendsto av atTop (𝓝 av₀)
    := by
  intro x₀ R r u t ε₀ ε K D S hε_pos v q qn av av₀ hq_limit havg_formula havg₀_formula
  rw [show av = fun n => (volume D).toReal⁻¹ * ∫ x in D, qn n x ∂volume by
    funext n
    exact havg_formula n]
  rw [show av₀ = (volume D).toReal⁻¹ * ∫ x in D, q x ∂volume by
    exact havg₀_formula]
  simpa using (tendsto_const_nhds.mul hq_limit)

private lemma poincareSobolevL1_vec3_slice_euclidean_hε_pos_1 :
    ∀ {R r : ℝ},
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      (0 : ℝ) < ε₀ → ∀ (n : ℕ), (0 : ℝ) < ε n
    := by
  intro R r t ε₀ ε hε₀_pos n
  dsimp [ε]
  exact div_pos hε₀_pos (by positivity)

private lemma poincareSobolevL1_vec3_slice_euclidean_hS_sub_U_2 :
    ∀ {U : Set Vec3} {x₀ : Vec3} {R r : ℝ},
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      (∀ x ∈ K, Metric.closedBall x ε₀ ⊆ U) → S ⊆ U
    := by
  intro U x₀ R r t ε₀ K S hclosed_subset
  rintro y ⟨x, hx, z, hz, rfl⟩
  apply hclosed_subset x hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  simpa [sub_eq_add_neg, add_comm] using hz

private lemma poincareSobolevL1_vec3_slice_euclidean_hgS_3 :
    ∀ {U : Set Vec3} {x₀ : Vec3} {R r : ℝ} (g : Vec3 → Fin (3 : ℕ) → Vec3),
      (∀ (i : Fin (3 : ℕ)),
          MemLp (ε := Vec3) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => g x i)
            (2 : ℝ≥0∞) (Measure.restrict volume U)) →
        let t : ℝ := (R + r) / (2 : ℝ);
        let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
        let K : Set Vec3 := euclideanClosedBall x₀ t;
        let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
        IsCompact S →
          S ⊆ U →
            ∀ (i j : Fin (3 : ℕ)),
              MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace)
                (S.indicator fun (x : Vec3) => g x i j) (2 : ℝ≥0∞) volume
    := by
  intro U x₀ R r g hg t ε₀ K S hS_compact hS_sub_U i j
  apply (memLp_indicator_iff_restrict hS_compact.measurableSet).2
  exact ((MemLp.eval (hg i) j).mono_measure
    (Measure.restrict_mono_set volume hS_sub_U))

private lemma poincareSobolevL1_vec3_slice_euclidean_hvDiff_4 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        (∀ (i : Fin (3 : ℕ)),
            LocallyIntegrable (ε := ℝ) (S.indicator fun (x : Vec3) => u x i) volume) →
          let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
            mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
          ∀ (n : ℕ), ContDiff ℝ (1 : WithTop ℕ∞) (v n)
    := by
  intro x₀ R r u t ε₀ ε K S hε_pos huLoc v n
  apply contDiff_pi.2
  intro i
  exact mollify_contDiff (hε_pos n) (huLoc i) (n := 1)

private lemma poincareSobolevL1_vec3_slice_euclidean_hclosed_subset_ε_5 :
    ∀ {U : Set Vec3} {x₀ : Vec3} {R r : ℝ},
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      (∀ (n : ℕ),
          (fun (n : ℕ) => (R - (R + r) / (2 : ℝ)) / ((2 : ℝ) * √(3 : ℝ)) / ((↑n : ℝ) + (1 : ℝ))) n ≤
            (R - (R + r) / (2 : ℝ)) / ((2 : ℝ) * √(3 : ℝ))) →
        (∀ x ∈ K, Metric.closedBall x ε₀ ⊆ U) → ∀ (n : ℕ), ∀ y ∈ K, Metric.closedBall y (ε n) ⊆ U
    := by
  intro U x₀ R r t ε₀ ε K hε_le hclosed_subset n y hy z hz
  apply hclosed_subset y hy
  rw [Metric.mem_closedBall] at hz ⊢
  exact hz.trans (hε_le n)

private lemma poincareSobolevL1_vec3_slice_euclidean_hS_u_support_6 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      IsCompact S →
        ∀ (i : Fin (3 : ℕ)), HasCompactSupport (β := ℝ) (S.indicator fun (x : Vec3) => u x i)
    := by
  intro x₀ R r u t ε₀ K S hS_compact i
  apply HasCompactSupport.intro hS_compact
  intro x hx
  simp [Set.indicator, hx]

private lemma poincareSobolevL1_vec3_slice_euclidean_hS_g_support_7 :
    ∀ {x₀ : Vec3} {R r : ℝ} (g : Vec3 → Fin (3 : ℕ) → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      IsCompact S →
        ∀ (i j : Fin (3 : ℕ)), HasCompactSupport (β := ℝ) (S.indicator fun (x : Vec3) => g x i j)
    := by
  intro x₀ R r g t ε₀ K S hS_compact i j
  apply HasCompactSupport.intro hS_compact
  intro x hx
  simp [Set.indicator, hx]

private lemma poincareSobolevL1_vec3_slice_euclidean_hval_eK_8 :
    ∀ {U : Set Vec3} {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      (∀ (i : Fin (3 : ℕ)),
          MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => u x i) (2 : ℝ≥0∞)
            (Measure.restrict volume U)) →
        let t : ℝ := (R + r) / (2 : ℝ);
        let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
        let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
        let K : Set Vec3 := euclideanClosedBall x₀ t;
        let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
        (0 : ℝ) < ε₀ →
          ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
            (have t : ℝ := (R + r) / (2 : ℝ);
              have ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
              have ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
              Tendsto ε atTop (𝓝 (0 : ℝ))) →
              IsCompact K →
                (∀ x ∈ K, Metric.closedBall x ε₀ ⊆ U) →
                  ∀ (i : Fin (3 : ℕ)),
                    Tendsto
                      (fun (n : ℕ) =>
                        @eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                          (fun (x : Vec (3 : ℕ)) =>
                            mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x -
                              u x i)
                          (2 : ℝ≥0∞) (Measure.restrict volume K))
                      atTop (𝓝 (0 : ℝ≥0∞))
    := by
  intro U x₀ R r u hu t ε₀ ε K S hε₀_pos hε_pos hε_tendsto hK_compact hclosed_subset i
  simpa [S] using
    (tendsto_eLpNorm_restrict_mollify_sub_zero hK_compact hε₀_pos
      hclosed_subset (by norm_num) ENNReal.coe_ne_top (hu i)
      hε_tendsto hε_pos)

private lemma poincareSobolevL1_vec3_slice_euclidean_hval_eD_9 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        euclideanBall x₀ r ⊆ euclideanClosedBall x₀ ((R + r) / (2 : ℝ)) →
          let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
            mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
          (∀ (i : Fin (3 : ℕ)),
              Tendsto
                (fun (n : ℕ) =>
                  @eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                    (fun (x : Vec (3 : ℕ)) =>
                      mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x - u x i)
                    (2 : ℝ≥0∞) (Measure.restrict volume K))
                atTop (𝓝 (0 : ℝ≥0∞))) →
            ∀ (i : Fin (3 : ℕ)),
              Tendsto
                (fun (n : ℕ) =>
                  @eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                    (fun (x : Vec3) => v n x i - u x i) (2 : ℝ≥0∞) (Measure.restrict volume D))
                atTop (𝓝 (0 : ℝ≥0∞))
    := by
  intro x₀ R r u t ε₀ ε K D S hε_pos hD_sub_K v hval_eK i
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hval_eK i) (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [] with n
  exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hD_sub_K)

private lemma poincareSobolevL1_vec3_slice_euclidean_hgrad_eK_10 :
    ∀ {U : Set Vec3} {x₀ : Vec3} {R r : ℝ} (g : Vec3 → Fin (3 : ℕ) → Vec3),
      (∀ (i : Fin (3 : ℕ)),
          MemLp (ε := Vec3) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => g x i)
            (2 : ℝ≥0∞) (Measure.restrict volume U)) →
        let t : ℝ := (R + r) / (2 : ℝ);
        let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
        let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
        let K : Set Vec3 := euclideanClosedBall x₀ t;
        let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
        (0 : ℝ) < ε₀ →
          ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
            (have t : ℝ := (R + r) / (2 : ℝ);
              have ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
              have ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
              Tendsto ε atTop (𝓝 (0 : ℝ))) →
              IsCompact K →
                (∀ x ∈ K, Metric.closedBall x ε₀ ⊆ U) →
                  ∀ (i j : Fin (3 : ℕ)),
                    Tendsto
                      (fun (n : ℕ) =>
                        @eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                          (fun (x : Vec (3 : ℕ)) =>
                            mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x -
                              g x i j)
                          (2 : ℝ≥0∞) (Measure.restrict volume K))
                      atTop (𝓝 (0 : ℝ≥0∞))
    := by
  intro U x₀ R r g hg t ε₀ ε K S hε₀_pos hε_pos hε_tendsto hK_compact hclosed_subset i j
  simpa [S] using
    (tendsto_eLpNorm_restrict_mollify_sub_zero hK_compact hε₀_pos
      hclosed_subset (by norm_num) ENNReal.coe_ne_top (MemLp.eval (hg i) j)
      hε_tendsto hε_pos)

private lemma poincareSobolevL1_vec3_slice_euclidean_hgrad_eD_11 :
    ∀ {x₀ : Vec3} {R r : ℝ} (g : Vec3 → Fin (3 : ℕ) → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        euclideanBall x₀ r ⊆ euclideanClosedBall x₀ ((R + r) / (2 : ℝ)) →
          let w : ℕ → Vec3 → Fin (3 : ℕ) → Vec3 := fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
            mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x;
          (∀ (i j : Fin (3 : ℕ)),
              Tendsto
                (fun (n : ℕ) =>
                  @eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                    (fun (x : Vec (3 : ℕ)) =>
                      mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x - g x i j)
                    (2 : ℝ≥0∞) (Measure.restrict volume K))
                atTop (𝓝 (0 : ℝ≥0∞))) →
            ∀ (i j : Fin (3 : ℕ)),
              Tendsto
                (fun (n : ℕ) =>
                  @eLpNorm _ ℝ _ _ MeasureSpace.toMeasurableSpace
                    (fun (x : Vec3) => w n x i j - g x i j) (2 : ℝ≥0∞) (Measure.restrict volume D))
                atTop (𝓝 (0 : ℝ≥0∞))
    := by
  intro x₀ R r g t ε₀ ε K D S hε_pos hD_sub_K w hgrad_eK i j
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (hgrad_eK i j) (Eventually.of_forall (fun _ => zero_le))
  filter_upwards [] with n
  exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hD_sub_K)

private lemma poincareSobolevL1_vec3_slice_euclidean_hval_sq_int_12 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
        (∀ (i : Fin (3 : ℕ)),
            MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => u x i)
              (2 : ℝ≥0∞) (Measure.restrict volume D)) →
          (∀ (n : ℕ) (i : Fin (3 : ℕ)),
              MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => v n x i)
                (2 : ℝ≥0∞) (Measure.restrict volume D)) →
            (∀ (i : Fin (3 : ℕ)),
                Tendsto
                  (fun (n : ℕ) =>
                    lpNorm (E := ℝ) (m0 := MeasureSpace.toMeasurableSpace)
                      (fun (x : Vec3) => v n x i) (2 : ℝ≥0∞) (Measure.restrict volume D))
                  atTop
                  (𝓝
                    (lpNorm (E := ℝ) (m0 := MeasureSpace.toMeasurableSpace)
                      (fun (x : Vec3) => u x i) (2 : ℝ≥0∞) (Measure.restrict volume D)))) →
              ∀ (i : Fin (3 : ℕ)),
                Tendsto (β := ℝ)
                  (fun (n : ℕ) =>
                    @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => v n x i ^ (2 : ℕ))
                  atTop
                  (𝓝
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => u x i ^ (2 : ℕ)))
    := by
  intro x₀ R r u t ε₀ ε K D S hε_pos v huD hvD hv_lp i
  have h := tendsto_integral_rpow_norm_of_tendsto_lpNorm
    (μ := volume.restrict D) (p := (2 : ℝ≥0∞))
    (by norm_num) ENNReal.coe_ne_top (huD i) (fun n => hvD n i) (hv_lp i)
  simpa [Real.norm_eq_abs, sq_abs] using h

private lemma poincareSobolevL1_vec3_slice_euclidean_hgrad_sq_int_13 :
    ∀ {x₀ : Vec3} {R r : ℝ} (g : Vec3 → Fin (3 : ℕ) → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let w : ℕ → Vec3 → Fin (3 : ℕ) → Vec3 := fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x;
        (∀ (i j : Fin (3 : ℕ)),
            MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => g x i j)
              (2 : ℝ≥0∞) (Measure.restrict volume D)) →
          (∀ (n : ℕ) (i j : Fin (3 : ℕ)),
              MemLp (ε := ℝ) (m0 := MeasureSpace.toMeasurableSpace) (fun (x : Vec3) => w n x i j)
                (2 : ℝ≥0∞) (Measure.restrict volume D)) →
            (∀ (i j : Fin (3 : ℕ)),
                Tendsto
                  (fun (n : ℕ) =>
                    lpNorm (E := ℝ) (m0 := MeasureSpace.toMeasurableSpace)
                      (fun (x : Vec3) => w n x i j) (2 : ℝ≥0∞) (Measure.restrict volume D))
                  atTop
                  (𝓝
                    (lpNorm (E := ℝ) (m0 := MeasureSpace.toMeasurableSpace)
                      (fun (x : Vec3) => g x i j) (2 : ℝ≥0∞) (Measure.restrict volume D)))) →
              ∀ (i j : Fin (3 : ℕ)),
                Tendsto (β := ℝ)
                  (fun (n : ℕ) =>
                    @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => w n x i j ^ (2 : ℕ))
                  atTop
                  (𝓝
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => g x i j ^ (2 : ℕ)))
    := by
  intro x₀ R r g t ε₀ ε K D S hε_pos w hgD hwD hw_lp i j
  have h := tendsto_integral_rpow_norm_of_tendsto_lpNorm
    (μ := volume.restrict D) (p := (2 : ℝ≥0∞))
    (by norm_num) ENNReal.coe_ne_top (hgD i j) (fun n => hwD n i j) (hw_lp i j)
  simpa [Real.norm_eq_abs, sq_abs] using h

private lemma poincareSobolevL1_vec3_slice_euclidean_hsmooth_14 :
    ∀ {x₀ : Vec3} {R r : ℝ},
      (0 : ℝ) < r →
        ∀ (u : Vec3 → Vec3) (g : Vec3 → Fin (3 : ℕ) → Vec3),
          let t : ℝ := (R + r) / (2 : ℝ);
          let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
          let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
          let K : Set Vec3 := euclideanClosedBall x₀ t;
          let D : Set Vec3 := euclideanBall x₀ r;
          let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
          ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
            let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
              mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
            let w : ℕ → Vec3 → Fin (3 : ℕ) → Vec3 := fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
              mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x;
            (∀ (n : ℕ), ContDiff ℝ (1 : WithTop ℕ∞) (v n)) →
              (∀ (n : ℕ),
                  Eq (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) =>
                      ∑ i : Fin (3 : ℕ),
                        ∑ j : Fin (3 : ℕ),
                          HPow.hPow (α := ℝ)
                            ((fderiv ℝ (fun (y : Vec3) => v n y i) x : Vec3 → ℝ) (basisVec j) : ℝ)
                            (2 : ℕ))
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) =>
                      ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), w n x i j ^ (2 : ℕ))) →
                ∀ (n : ℕ),
                  HPow.hPow (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                        fun (x : Vec3) =>
                        |vec3EuclideanNorm (v n x) ^ (2 : ℕ) -
                              ⨍ (y : Vec3) in D, vec3EuclideanNorm (v n y) ^ (2 : ℕ)| ^
                          (3 / 2 : ℝ))
                      (2 / 3 : ℝ) ≤
                    poincareSobolevL1VectorConstant *
                        HPow.hPow (α := ℝ)
                          (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                            (Measure.restrict volume D) fun (x : Vec3) =>
                            vec3EuclideanNorm (v n x) ^ (2 : ℕ))
                          (1 / 2 : ℝ) *
                      HPow.hPow (α := ℝ)
                        (@integral _ _ _ _ MeasureSpace.toMeasurableSpace
                          (Measure.restrict volume D) fun (x : Vec3) =>
                          ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), w n x i j ^ (2 : ℕ))
                        (1 / 2 : ℝ)
    := by
  intro x₀ R r hr u g t ε₀ ε K D S hε_pos v w hvDiff hderiv_int_eq n
  have h := poincareSobolevL1_vec3_ball x₀ hr (v n) (hvDiff n)
  rw [vec3Ball_eq_euclideanBall' hr] at h
  simpa [D, hderiv_int_eq n] using h

private lemma poincareSobolevL1_vec3_slice_euclidean_hD_closed_15 :
    ∀ {x₀ : Vec3} {r : ℝ},
      (0 : ℝ) < r →
        let D : Set Vec3 := euclideanBall x₀ r;
        D ⊆ euclideanClosedBall x₀ r
    := by
  intro x₀ r hr D x hx
  exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
    ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).le

private lemma poincareSobolevL1_vec3_slice_euclidean_havg_formula_16 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
        let qn : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) => vec3EuclideanNorm (v n x) ^ (2 : ℕ);
        let av : ℕ → ℝ := fun (n : ℕ) => ⨍ (y : Vec3) in D, qn n y;
        ∀ (n : ℕ),
          av n =
            (ENNReal.toReal ((volume : Set Vec3 → ℝ≥0∞) D))⁻¹ *
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) => qn n x
    := by
  intro x₀ R r u t ε₀ ε K D S hε_pos v qn av n
  change (⨍ y in D, qn n y) = _
  rw [MeasureTheory.setAverage_eq]
  rfl

private lemma poincareSobolevL1_vec3_slice_euclidean_havg₀_formula_17 :
    ∀ {x₀ : Vec3} {r : ℝ} (u : Vec3 → Vec3),
      let D : Set Vec3 := euclideanBall x₀ r;
      let q : Vec3 → ℝ := fun (x : Vec3) => vec3EuclideanNorm (u x) ^ (2 : ℕ);
      let av₀ : ℝ := ⨍ (y : Vec3) in D, q y;
      av₀ =
        (ENNReal.toReal ((volume : Set Vec3 → ℝ≥0∞) D))⁻¹ *
          @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
            fun (x : Vec3) => q x
    := by
  intro x₀ r u D q av₀
  change (⨍ y in D, q y) = _
  rw [MeasureTheory.setAverage_eq]
  rfl

private lemma poincareSobolevL1_vec3_slice_euclidean_hq_ae_18 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
        let q : Vec3 → ℝ := fun (x : Vec3) => vec3EuclideanNorm (u x) ^ (2 : ℕ);
        let qn : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) => vec3EuclideanNorm (v n x) ^ (2 : ℕ);
        ∀ (ns : ℕ → ℕ),
          (∀ᵐ (x : Vec3) ∂Measure.restrict volume D,
              Tendsto
                (fun (i : ℕ) (i_1 : Fin (3 : ℕ)) =>
                  mollify
                    ((euclideanClosedBall x₀ ((R + r) / (2 : ℝ)) +
                          Metric.closedBall (0 : Vec3)
                            ((R - (R + r) / (2 : ℝ)) / ((2 : ℝ) * √(3 : ℝ)))).indicator
                      fun (y : Vec3) => u y i_1)
                    ((fun (n : ℕ) =>
                        (R - (R + r) / (2 : ℝ)) / ((2 : ℝ) * √(3 : ℝ)) / ((↑n : ℝ) + (1 : ℝ)))
                      (ns i))
                    (hε_pos (ns i)) x)
                atTop (𝓝 (u x))) →
            ∀ᵐ (x : Vec3) ∂Measure.restrict volume D,
              Tendsto (fun (k : ℕ) => qn (ns k) x) atTop (𝓝 (q x))
    := by
  intro x₀ R r u t ε₀ ε K D S hε_pos v q qn ns hns_ae
  filter_upwards [hns_ae] with x hx
  have hvx : Tendsto (fun k => v (ns k) x) atTop (nhds (u x)) := hx
  have hn := (continuous_vec3EuclideanNorm.tendsto (u x)).comp hvx
  simpa [q, qn] using hn.pow 2

private lemma poincareSobolevL1_vec3_slice_euclidean_hRhs_19 :
    ∀ {x₀ : Vec3} {R r : ℝ} (u : Vec3 → Vec3) (g : Vec3 → Fin (3 : ℕ) → Vec3),
      let t : ℝ := (R + r) / (2 : ℝ);
      let ε₀ : ℝ := (R - t) / ((2 : ℝ) * √(3 : ℝ));
      let ε : ℕ → ℝ := fun (n : ℕ) => ε₀ / ((↑n : ℝ) + (1 : ℝ));
      let K : Set Vec3 := euclideanClosedBall x₀ t;
      let D : Set Vec3 := euclideanBall x₀ r;
      let S : Set Vec3 := K + Metric.closedBall (0 : Vec3) ε₀;
      ∀ (hε_pos : ∀ (n : ℕ), (0 : ℝ) < ε n),
        let v : ℕ → Vec3 → Vec3 := fun (n : ℕ) (x : Vec3) (i : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => u y i) (ε n) (hε_pos n) x;
        let w : ℕ → Vec3 → Fin (3 : ℕ) → Vec3 := fun (n : ℕ) (x : Vec3) (i j : Fin (3 : ℕ)) =>
          mollify (S.indicator fun (y : Vec3) => g y i j) (ε n) (hε_pos n) x;
        Tendsto (β := ℝ)
            (fun (n : ℕ) =>
              @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) => ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), w n x i j ^ (2 : ℕ))
            atTop
            (𝓝
              (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                fun (x : Vec3) => ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), g x i j ^ (2 : ℕ))) →
          let q : Vec3 → ℝ := fun (x : Vec3) => vec3EuclideanNorm (u x) ^ (2 : ℕ);
          let qn : ℕ → Vec3 → ℝ := fun (n : ℕ) (x : Vec3) => vec3EuclideanNorm (v n x) ^ (2 : ℕ);
          Tendsto (β := ℝ)
              (fun (n : ℕ) =>
                @integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                  fun (x : Vec3) => qn n x)
              atTop
              (𝓝
                (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                  fun (x : Vec3) => q x)) →
            Tendsto
              (fun (n : ℕ) =>
                poincareSobolevL1VectorConstant *
                    HPow.hPow (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                        fun (x : Vec3) => qn n x)
                      (1 / 2 : ℝ) *
                  HPow.hPow (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), w n x i j ^ (2 : ℕ))
                    (1 / 2 : ℝ))
              atTop
              (𝓝
                (poincareSobolevL1VectorConstant *
                    HPow.hPow (α := ℝ)
                      (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                        fun (x : Vec3) => q x)
                      (1 / 2 : ℝ) *
                  HPow.hPow (α := ℝ)
                    (@integral _ _ _ _ MeasureSpace.toMeasurableSpace (Measure.restrict volume D)
                      fun (x : Vec3) => ∑ i : Fin (3 : ℕ), ∑ j : Fin (3 : ℕ), g x i j ^ (2 : ℕ))
                    (1 / 2 : ℝ)))
    := by
  intro x₀ R r u g t ε₀ ε K D S hε_pos v w hgrad_int_limit q qn hq_limit
  have hqroot := (Real.continuous_sqrt.tendsto _).comp hq_limit
  have hgroot := (Real.continuous_sqrt.tendsto _).comp hgrad_int_limit
  simpa [Real.sqrt_eq_rpow] using (tendsto_const_nhds.mul hqroot).mul hgroot

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
  have hε_pos := @poincareSobolevL1_vec3_slice_euclidean_hε_pos_1 R r hε₀_pos
  have hε_le := @poincareSobolevL1_vec3_slice_euclidean_hε_le_1 R r hε₀_pos
  have hε_tendsto := @poincareSobolevL1_vec3_slice_euclidean_hε_tendsto_2 R r
  have hK_compact : IsCompact K := by
    simpa [K] using isCompact_euclideanClosedBall x₀ ht_pos.le
  have hD_open : IsOpen D := by
    change IsOpen {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  have hD_meas : MeasurableSet D := hD_open.measurableSet
  have hvecnorm_eq (z : Vec3) : vec3EuclideanNorm z = vecEuclideanNorm z := by
    simp [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
  have hnorm_le_euclidean (z : Vec3) :=
    @poincareSobolevL1_vec3_slice_euclidean_hnorm_le_euclidean_4 hvecnorm_eq z
  have hK_sub_R := @poincareSobolevL1_vec3_slice_euclidean_hK_sub_R_5 x₀ R r htR ht_pos hvecnorm_eq
  have hD_sub_K := @poincareSobolevL1_vec3_slice_euclidean_hD_sub_K_6 x₀ R r hr ht ht_pos
    hvecnorm_eq
  have hclosed_subset := @poincareSobolevL1_vec3_slice_euclidean_hclosed_subset_1 U x₀ R r hball
    htR ht_pos hsqrt hvecnorm_eq
  have hS_compact : IsCompact S := by
    simpa [S] using hK_compact.add (ProperSpace.isCompact_closedBall (0 : Vec3) ε₀)
  have hS_sub_U := @poincareSobolevL1_vec3_slice_euclidean_hS_sub_U_2 U x₀ R r hclosed_subset
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
  have hgExtLoc (i j : Fin 3) :=
    (hgExt i j).locallyIntegrable (by norm_num)
  have hweakExt (i j : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hweakExt_2 U hU u g hweak
    i j
  have huLoc (i : Fin 3) : LocallyIntegrable (S.indicator (fun x => u x i)) volume :=
    (huS i).locallyIntegrable (by norm_num)
  have hgS (i j : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hgS_3 U x₀ R r g hg hS_compact
    hS_sub_U i j
  have hgLoc (i j : Fin 3) : LocallyIntegrable (S.indicator (fun x => g x i j)) volume :=
    (hgS i j).locallyIntegrable (by norm_num)
  let v : ℕ → Vec3 → Vec3 := fun n x i =>
    mollify (S.indicator (fun y => u y i)) (ε n) (hε_pos n) x
  let w : ℕ → Vec3 → Fin 3 → Vec3 := fun n x i j =>
    mollify (S.indicator (fun y => g y i j)) (ε n) (hε_pos n) x
  have hvDiff (n : ℕ) := @poincareSobolevL1_vec3_slice_euclidean_hvDiff_4 x₀ R r u hε_pos huLoc n
  have hwCont (n : ℕ) (i j : Fin 3) : Continuous (fun x => w n x i j) :=
    (mollify_continuous (hε_pos n) (hgLoc i j))
  have hclosed_subset_ε (n : ℕ) := @poincareSobolevL1_vec3_slice_euclidean_hclosed_subset_ε_5 U x₀
    R r hε_le hclosed_subset n
  have hvalue_eventually (n : ℕ) (i : Fin 3) {x : Vec3} (hx : x ∈ D) :=
    @poincareSobolevL1_vec3_slice_euclidean_hvalue_eventually_3 U x₀ R r hr u ht ht_pos hsqrt
    hε_pos hε_le hvecnorm_eq hnorm_le_euclidean hS_sub_U n i x hx
  have hderiv_eq (n : ℕ) (i j : Fin 3) {x : Vec3} (hx : x ∈ D) :=
    @poincareSobolevL1_vec3_slice_euclidean_hderiv_eq_4 U hU x₀ R r u g hε_pos hε_le hK_compact
    hD_sub_K hS_sub_U huExtLoc hgExtLoc hweakExt hclosed_subset_ε hvalue_eventually n i j x hx
  have hD_sub_U : D ⊆ U := hD_sub_K.trans hK_sub_R |>.trans hball
  have huD (i : Fin 3) : MemLp (fun x => u x i) (2 : ℝ≥0∞) (volume.restrict D) :=
    (hu i).mono_measure (Measure.restrict_mono_set volume hD_sub_U)
  have hgD (i j : Fin 3) : MemLp (fun x => g x i j) (2 : ℝ≥0∞) (volume.restrict D) :=
    (MemLp.eval (hg i) j).mono_measure (Measure.restrict_mono_set volume hD_sub_U)
  have hS_u_support (i : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hS_u_support_6 x₀ R r u
    hS_compact i
  have hvMem (n : ℕ) (i : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hvMem_7 x₀ R r u
    hε_pos huLoc hS_u_support n i
  have hS_g_support (i j : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hS_g_support_7 x₀ R r
    g hS_compact i j
  have hwMem (n : ℕ) (i j : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hwMem_8 x₀ R r g
    hε_pos hwCont hS_g_support n i j
  have hval_eK (i : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hval_eK_8 U x₀ R r u hu
    hε₀_pos hε_pos hε_tendsto hK_compact hclosed_subset i
  have hval_eD (i : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hval_eD_9 x₀ R r u hε_pos
    hD_sub_K hval_eK i
  have hgrad_eK (i j : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hgrad_eK_10 U x₀ R r g hg
    hε₀_pos hε_pos hε_tendsto hK_compact hclosed_subset i j
  have hgrad_eD (i j : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hgrad_eD_11 x₀ R r g
    hε_pos hD_sub_K hgrad_eK i j
  have hval_lp (i : Fin 3) :=
    tendsto_lpNorm_zero_of_tendsto_eLpNorm_zero (hval_eD i)
  have hgrad_lp (i j : Fin 3) :=
    tendsto_lpNorm_zero_of_tendsto_eLpNorm_zero (hgrad_eD i j)
  have hvD (n : ℕ) (i : Fin 3) : MemLp (fun x => v n x i) (2 : ℝ≥0∞) (volume.restrict D) :=
    (hvMem n i).mono_measure Measure.restrict_le_self
  have hwD (n : ℕ) (i j : Fin 3) : MemLp (fun x => w n x i j) (2 : ℝ≥0∞) (volume.restrict D) :=
    (hwMem n i j).mono_measure Measure.restrict_le_self
  have hv_lp (i : Fin 3) :=
    lpNorm_tendsto_of_diff (by norm_num) (huD i) (fun n => hvD n i) (hval_lp i)
  have hw_lp (i j : Fin 3) :=
    lpNorm_tendsto_of_diff (by norm_num) (hgD i j) (fun n => hwD n i j)
      (hgrad_lp i j)
  have hval_sq_int (i : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hval_sq_int_12 x₀ R r u
    hε_pos huD hvD hv_lp i
  have hgrad_sq_int (i j : Fin 3) := @poincareSobolevL1_vec3_slice_euclidean_hgrad_sq_int_13 x₀ R
    r g hε_pos hgD hwD hw_lp i j
  have hvec_sq (z : Vec3) : (vec3EuclideanNorm z) ^ 2 = ∑ i : Fin 3, z i ^ 2 := by
    rw [vec3EuclideanNorm]
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (z i)))
  have hval_int_eq (n : ℕ) := @poincareSobolevL1_vec3_slice_euclidean_hval_int_eq_9 x₀ R r u
    hε_pos hvD hvec_sq n
  have hval_int_eq_limit := @poincareSobolevL1_vec3_slice_euclidean_hval_int_eq_limit_5 x₀ R r u
    hε_pos huD hval_sq_int hvec_sq hval_int_eq
  have hgrad_int_eq (n : ℕ) := @poincareSobolevL1_vec3_slice_euclidean_hgrad_int_eq_6 x₀ R r g
    hε_pos hwD n
  have hgrad_int_limit := @poincareSobolevL1_vec3_slice_euclidean_hgrad_int_limit_7 x₀ R r g
    hε_pos hgD hgrad_sq_int hgrad_int_eq
  have hderiv_int_eq (n : ℕ) := @poincareSobolevL1_vec3_slice_euclidean_hderiv_int_eq_10 x₀ R r u
    g hε_pos hD_meas hderiv_eq n
  have hsmooth (n : ℕ) := @poincareSobolevL1_vec3_slice_euclidean_hsmooth_14 x₀ R r hr u g hε_pos
    hvDiff hderiv_int_eq n
  let q : Vec3 → ℝ := fun x => (vec3EuclideanNorm (u x)) ^ 2
  let qn : ℕ → Vec3 → ℝ := fun n x => (vec3EuclideanNorm (v n x)) ^ 2
  let av : ℕ → ℝ := fun n => ⨍ y in D, qn n y
  let av₀ : ℝ := ⨍ y in D, q y
  let Fn : ℕ → Vec3 → ℝ := fun n x => |qn n x - av n| ^ (3 / 2 : ℝ)
  have hqn_cont (n : ℕ) : Continuous (qn n) := by
    exact (continuous_vec3EuclideanNorm.comp (hvDiff n).continuous).pow 2
  have hD_closed := @poincareSobolevL1_vec3_slice_euclidean_hD_closed_15 x₀ r hr
  have hclosed_compact : IsCompact (euclideanClosedBall x₀ r) :=
    isCompact_euclideanClosedBall x₀ hr.le
  have hq_limit : Tendsto
      (fun n => ∫ x in D, qn n x ∂volume) atTop
        (nhds (∫ x in D, q x ∂volume)) := by
    simpa [q, qn] using hval_int_eq_limit
  have havg_formula (n : ℕ) := @poincareSobolevL1_vec3_slice_euclidean_havg_formula_16 x₀ R r u
    hε_pos n
  have havg₀_formula := @poincareSobolevL1_vec3_slice_euclidean_havg₀_formula_17 x₀ r u
  have havg_limit := @poincareSobolevL1_vec3_slice_euclidean_havg_limit_11 x₀ R r u hε_pos
    hq_limit havg_formula havg₀_formula
  have hFn_cont (n : ℕ) : Continuous (Fn n) := by
    exact ((hqn_cont n).sub continuous_const).abs.rpow_const
      (fun _ => Or.inr (by norm_num))
  have hFn_int (n : ℕ) : Integrable (Fn n) (volume.restrict D) := by
    exact (hFn_cont n).continuousOn.integrableOn_compact hclosed_compact |>.mono_set hD_closed
  have huVecD : MemLp u (2 : ℝ≥0∞) (volume.restrict D) :=
    MemLp.of_eval huD
  have hvVecD (n : ℕ) : MemLp (v n) (2 : ℝ≥0∞) (volume.restrict D) :=
    MemLp.of_eval (hvD n)
  have hvec_e := @poincareSobolevL1_vec3_slice_euclidean_hvec_e_8 x₀ R r u hε_pos hval_eD huVecD
    hvVecD
  obtain ⟨ns, hns_mono, hns_ae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (μ := volume.restrict D)
      (p := (2 : ℝ≥0∞)) (by norm_num) hvec_e).exists_seq_tendsto_ae
  have hq_ae := @poincareSobolevL1_vec3_slice_euclidean_hq_ae_18 x₀ R r u hε_pos ns hns_ae
  have havg_seq : Tendsto (fun k => av (ns k)) atTop (nhds av₀) :=
    havg_limit.comp (hns_mono.tendsto_atTop)
  have hFn_ae := @poincareSobolevL1_vec3_slice_euclidean_hFn_ae_9 x₀ R r u hε_pos ns hq_ae havg_seq
  have hRhs := @poincareSobolevL1_vec3_slice_euclidean_hRhs_19 x₀ R r u g hε_pos hgrad_int_limit
    hq_limit
  have hseq (k : ℕ) := @poincareSobolevL1_vec3_slice_euclidean_hseq_10 x₀ R r u g hε_pos hsmooth
    ns k
  have hRhs_seq :=
    hRhs.comp hns_mono.tendsto_atTop
  let B := poincareSobolevL1VectorConstant *
    (∫ x in D, q x ∂volume) ^ (1 / 2 : ℝ) *
    (∫ x in D, ∑ i : Fin 3, ∑ j : Fin 3, (g x i j) ^ 2 ∂volume) ^ (1 / 2 : ℝ)
  have hB : 0 ≤ B := by
    dsimp [B, poincareSobolevL1VectorConstant]
    positivity
  have hpowerLimit := (Real.continuous_rpow_const
    (by norm_num : 0 ≤ (3 / 2 : ℝ))).tendsto B |>.comp hRhs_seq
  have hbound := integral_le_of_ae_tendsto_nonneg
    (fun k => hFn_int (ns k))
    (fun _ => Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (Filter.Eventually.of_forall fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    hFn_ae (Real.rpow_nonneg hB _) hpowerLimit hseq
  have hroot := Real.rpow_le_rpow
    (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg (q x - av₀)) (3 / 2 : ℝ))
    hbound (by norm_num : 0 ≤ (2 / 3 : ℝ))
  rw [← Real.rpow_mul hB] at hroot
  norm_num only [show (3 / 2 : ℝ) * (2 / 3) = 1 by norm_num, Real.rpow_one] at hroot
  exact hroot

end
end CKN
