/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.InterpolationBall
public import LeanPool.CaffarelliKohnNirenberg.Setting.VectorNormAggregation
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Interpolation Cylinder

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

private theorem vec3Ball_eq_euclideanBall_interp {x₀ : Vec3} {r : ℝ}
    (hr : 0 < r) : vec3Ball x₀ r = euclideanBall x₀ r := by
  ext x
  change vec3EuclideanNorm (x - x₀) < r ↔ x ∈ euclideanBall x₀ r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
    using (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).symm

private theorem eLpNorm_cube_eq_lintegral_abs_cube_interp
    {s : Set Vec3} {f : Vec3 → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s)) :
    eLpNorm f (3 : ℝ≥0∞) (volume.restrict s) ^ (3 : ℕ) =
      ∫⁻ x in s, ENNReal.ofReal |f x| ^ (3 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (p := (3 : ℝ≥0∞)) (by norm_num) ENNReal.coe_ne_top hf,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs]

private theorem eLpNorm_component_le_sum_interp {ι : Type*} [Fintype ι]
    {f : ι → ℝ≥0∞} (i : ι) :
    f i ≤ ∑ j, f j := by
  exact Finset.single_le_sum (fun j _ => bot_le) (Finset.mem_univ i)

/-! The spatial estimate is stated with the component `L²` masses.  This is
the form in which the finite-dimensional aggregation is cheapest to reuse in
the time integration below. -/

/-- A same-ball `L³` estimate for a vector slice with a fixed scalar constant. -/
theorem vector_interpolation_ball_l3_fixed
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) {u : Vec3 → Vec3}
    {C₆ : ℝ≥0∞}
    (hC : ∀ {x₀ : Vec3} {r : ℝ}, 0 < r → ∀ v : H1Function (euclideanBall x₀ r),
      lpNormOn 3 (euclideanBall x₀ r) v.toFun ^ (3 : ℕ) ≤
        C₆ * weakGradientLpNormOn 2 (euclideanBall x₀ r) v.grad ^
            (3 / 2 : ℝ) * lpNormOn 2 (euclideanBall x₀ r) v.toFun ^
              (3 / 2 : ℝ) +
          C₆ * (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) *
            lpNormOn 2 (euclideanBall x₀ r) v.toFun ^ (3 : ℕ))
    (hu : ∀ _i : Fin 3, H1Function (euclideanBall x₀ r))
    (hcomp : ∀ i : Fin 3, (hu i).toFun = fun x => u x i) :
    (∫⁻ x in vec3Ball x₀ r,
        ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℝ)) ≤
        3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
            (∑ i : Fin 3,
              weakGradientLpNormOn 2 (euclideanBall x₀ r) (hu i).grad) ^
              (3 / 2 : ℝ) *
            (∑ i : Fin 3, lpNormOn 2 (euclideanBall x₀ r) (hu i).toFun) ^
              (3 / 2 : ℝ) +
          3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
            (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) *
            (∑ i : Fin 3, lpNormOn 2 (euclideanBall x₀ r) (hu i).toFun) ^
              (3 : ℝ) := by
  let B : Set Vec3 := euclideanBall x₀ r
  let L : ℝ≥0∞ := ∑ i : Fin 3, lpNormOn 2 B (hu i).toFun
  let G : ℝ≥0∞ := ∑ i : Fin 3, weakGradientLpNormOn 2 B (hu i).grad
  have hball : vec3Ball x₀ r = B := by
    exact vec3Ball_eq_euclideanBall_interp hr
  have hmeas : ∀ i : Fin 3,
      AEMeasurable (fun x => u x i) (volume.restrict B) := by
    intro i
    rw [← hcomp i]
    exact (hu i).memL2.aestronglyMeasurable.aemeasurable
  have hvec := lintegral_vec3EuclideanNorm_rpow_le_sum
    (s := B) (u := u) (p := (3 : ℝ)) (by norm_num) hmeas
  rw [hball]
  calc
    ∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u x)) ^ (3 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt 3) *
          ∑ i : Fin 3, lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) := by
      have hconst : (3 : ℝ) ^ ((3 : ℝ) / 2 - 1) = Real.sqrt 3 := by
        rw [show (3 : ℝ) / 2 - 1 = (1 / 2 : ℝ) by norm_num,
          ← Real.sqrt_eq_rpow]
      have hvec' : ∫⁻ x in B, ENNReal.ofReal (vec3EuclideanNorm (u x)) ^
          (3 : ℝ) ≤ ENNReal.ofReal (Real.sqrt 3) *
            ∑ i : Fin 3, ∫⁻ x in B, ‖u x i‖ₑ ^ (3 : ℝ) := by
        simpa only [show max 0 ((3 : ℝ) / 2 - 1) = (3 : ℝ) / 2 - 1 by norm_num,
          hconst] using hvec
      apply le_trans hvec'
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro i hi
        have hstrong : AEStronglyMeasurable (fun x => u x i)
            (volume.restrict B) := by
          rw [← hcomp i]
          exact (hu i).memL2.aestronglyMeasurable
        have hEq : (∫⁻ x in B, ‖u x i‖ₑ ^ (3 : ℝ)) =
            lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) := by
          calc
            ∫⁻ x in B, ‖u x i‖ₑ ^ (3 : ℝ) =
                ∫⁻ x in B, ENNReal.ofReal |u x i| ^ (3 : ℝ) := by
              apply lintegral_congr
              intro x
              rw [Real.enorm_eq_ofReal_abs,
                ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
            _ = eLpNorm (fun x => u x i) (3 : ℝ≥0∞)
                  (volume.restrict B) ^ (3 : ℕ) := by
              symm
              exact eLpNorm_cube_eq_lintegral_abs_cube_interp hstrong
            _ = lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) := by
              simpa only [lpNormOn] using
                (congrArg (fun f : Vec3 → ℝ =>
                  eLpNorm f (3 : ℝ≥0∞) (volume.restrict B) ^ (3 : ℕ))
                  (hcomp i)).symm
        exact hEq.le
      · positivity
    _ ≤ 3 * ENNReal.ofReal (Real.sqrt 3) * C₆ * G ^ (3 / 2 : ℝ) *
          L ^ (3 / 2 : ℝ) +
        3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
          (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) * L ^ (3 : ℝ) := by
      have hLi : ∀ i : Fin 3,
          lpNormOn 2 B (hu i).toFun ≤ L := by
        intro i
        simpa only [L] using
          (eLpNorm_component_le_sum_interp
            (f := fun j : Fin 3 => lpNormOn 2 B (hu j).toFun) i)
      have hGi : ∀ i : Fin 3,
          weakGradientLpNormOn 2 B (hu i).grad ≤ G := by
        intro i
        simpa only [G] using
          (eLpNorm_component_le_sum_interp
            (f := fun j : Fin 3 => weakGradientLpNormOn 2 B (hu j).grad) i)
      have hterm : ∀ i : Fin 3,
          lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) ≤
            C₆ * (weakGradientLpNormOn 2 B (hu i).grad) ^
                (3 / 2 : ℝ) * (lpNormOn 2 B (hu i).toFun) ^
                (3 / 2 : ℝ) +
              C₆ * (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) *
                (lpNormOn 2 B (hu i).toFun) ^ (3 : ℝ) := by
        intro i
        have hi := hC hr (hu i)
        simpa [B] using hi
      have hprod : ∀ i : Fin 3,
          (weakGradientLpNormOn 2 B (hu i).grad) ^ (3 / 2 : ℝ) *
              (lpNormOn 2 B (hu i).toFun) ^ (3 / 2 : ℝ) ≤
            G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) := by
        intro i
        exact mul_le_mul
          (ENNReal.rpow_le_rpow (hGi i) (by norm_num))
          (ENNReal.rpow_le_rpow (hLi i) (by norm_num))
          (by positivity) (by positivity)
      have hsum : ∑ i : Fin 3, lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) ≤
          3 * C₆ * G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) +
            3 * C₆ * (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) * L ^ (3 : ℝ) := by
        calc
          ∑ i : Fin 3, lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) ≤
              ∑ i : Fin 3,
                (C₆ * (weakGradientLpNormOn 2 B (hu i).grad) ^
                    (3 / 2 : ℝ) * (lpNormOn 2 B (hu i).toFun) ^
                    (3 / 2 : ℝ) +
                  C₆ * (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) *
                    (lpNormOn 2 B (hu i).toFun) ^ (3 : ℝ)) :=
            Finset.sum_le_sum (fun i _ => hterm i)
          _ ≤ 3 * C₆ * G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) +
              3 * C₆ * (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) * L ^ (3 : ℝ) := by
            have hfirst :
                ∑ i : Fin 3, C₆ *
                    ((weakGradientLpNormOn 2 B (hu i).grad) ^
                      (3 / 2 : ℝ) *
                    (lpNormOn 2 B (hu i).toFun) ^ (3 / 2 : ℝ)) ≤
                  3 * C₆ * G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) := by
              calc
                _ ≤ ∑ i : Fin 3, C₆ *
                    (G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ)) := by
                  apply Finset.sum_le_sum
                  intro i _
                  exact mul_le_mul_of_nonneg_left (hprod i) (by positivity)
                _ = _ := by
                  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                    nsmul_eq_mul]
                  ring
            have hsecond :
                ∑ i : Fin 3, C₆ * (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) *
                    (lpNormOn 2 B (hu i).toFun) ^ (3 : ℝ) ≤
                  3 * C₆ * (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) *
                    L ^ (3 : ℝ) := by
              calc
                _ ≤ ∑ i : Fin 3, C₆ * (ENNReal.ofReal r) ^
                      (-(3 / 2 : ℝ)) * L ^ (3 : ℝ) := by
                  apply Finset.sum_le_sum
                  intro i _
                  exact mul_le_mul_of_nonneg_left
                    (ENNReal.rpow_le_rpow (hLi i) (by norm_num)) (by positivity)
                _ = _ := by
                  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                    nsmul_eq_mul]
                  ring
            rw [Finset.sum_add_distrib]
            exact add_le_add (by simpa only [mul_assoc] using hfirst) hsecond
      have hconst : 0 ≤ 3 * ENNReal.ofReal (Real.sqrt 3) := by positivity
      calc
        ENNReal.ofReal (Real.sqrt 3) *
              ∑ i : Fin 3, lpNormOn 3 B (hu i).toFun ^ (3 : ℕ) ≤
            ENNReal.ofReal (Real.sqrt 3) *
              (3 * C₆ * G ^ (3 / 2 : ℝ) * L ^ (3 / 2 : ℝ) +
                3 * C₆ * (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) * L ^ (3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = 3 * ENNReal.ofReal (Real.sqrt 3) * C₆ * G ^ (3 / 2 : ℝ) *
              L ^ (3 / 2 : ℝ) +
            3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
              (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) * L ^ (3 : ℝ) := by
          dsimp [L, G, B]
          ring
        _ = 3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
              (∑ i : Fin 3,
                weakGradientLpNormOn 2 (euclideanBall x₀ r) (hu i).grad) ^
                (3 / 2 : ℝ) *
              (∑ i : Fin 3, lpNormOn 2 (euclideanBall x₀ r) (hu i).toFun) ^
                (3 / 2 : ℝ) +
            3 * ENNReal.ofReal (Real.sqrt 3) * C₆ *
              (ENNReal.ofReal r) ^ (-(3 / 2 : ℝ)) *
              (∑ i : Fin 3, lpNormOn 2 (euclideanBall x₀ r) (hu i).toFun) ^
                (3 : ℝ) := by
          dsimp [L, G, B]

/-! The next bridge is independent of the origin of the slice functions.  It
packages the time Hölder step, so a consumer only has to provide the spatial
interpolation estimate and the two energy bounds. -/

/-- Time integration of a same-ball cubic interpolation estimate. -/
theorem time_interpolation_ball_l3
    {T : Set ℝ} {A G : ℝ → ℝ≥0∞}
    {K R A₀ G₂ V : ℝ≥0∞}
    (hA : AEMeasurable A (volume.restrict T))
    (hG : AEMeasurable G (volume.restrict T))
    (hKtop : K ≠ ∞)
    (hA₀top : A₀ ≠ ∞)
    (hA₀ : ∀ᵐ s ∂volume.restrict T, A s ≤ A₀)
    (hG₂ : (∫⁻ s in T, G s ^ (2 : ℝ)) ≤ G₂)
    (hV : volume T ≤ V) :
    (∫⁻ s in T,
        K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) +
          K * R * A s ^ (3 : ℝ)) ≤
      K * A₀ ^ (3 / 2 : ℝ) * G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) +
        K * R * V * A₀ ^ (3 : ℝ) := by
  have hGmeas : AEMeasurable (fun s => G s ^ (3 / 2 : ℝ))
      (volume.restrict T) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hG
  have hone : AEMeasurable (fun _ : ℝ => (1 : ℝ≥0∞))
      (volume.restrict T) := aemeasurable_const
  have hpq : (4 / 3 : ℝ).HolderConjugate (4 : ℝ) := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq
    (volume.restrict T) hpq hGmeas hone
  have hGpow : (∫⁻ s in T, G s ^ (3 / 2 : ℝ)) ≤
      G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) := by
    calc
      _ = ∫⁻ s in T, (G s ^ (3 / 2 : ℝ)) * 1 := by
        apply lintegral_congr
        intro s
        rw [mul_one]
      _ ≤ (∫⁻ s in T, (G s ^ (3 / 2 : ℝ)) ^ (4 / 3 : ℝ)) ^
            (1 / (4 / 3 : ℝ)) *
          (∫⁻ s in T, (1 : ℝ≥0∞) ^ (4 : ℝ)) ^ (1 / (4 : ℝ)) := by
        simpa only [Pi.mul_apply, mul_one, ENNReal.one_rpow, one_mul,
          lintegral_const] using hholder
      _ = (∫⁻ s in T, G s ^ (2 : ℝ)) ^ (3 / 4 : ℝ) *
          (volume T) ^ (1 / 4 : ℝ) := by
        rw [show 1 / (4 / 3 : ℝ) = (3 / 4 : ℝ) by norm_num]
        congr 1
        · apply congrArg (fun z : ℝ≥0∞ => z ^ (3 / 4 : ℝ))
          apply lintegral_congr
          intro s
          rw [← ENNReal.rpow_mul]
          norm_num
        · simp
      _ ≤ _ := by gcongr
  have hfirst : (∫⁻ s in T,
      K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ)) ≤
      K * A₀ ^ (3 / 2 : ℝ) * G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ) := by
    have hpoint : ∀ᵐ s ∂volume.restrict T,
        K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) ≤
          K * A₀ ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) := by
      filter_upwards [hA₀] with s hs
      gcongr
    calc
      _ ≤ ∫⁻ s in T, K * A₀ ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ) :=
        lintegral_mono_ae hpoint
      _ = K * A₀ ^ (3 / 2 : ℝ) *
          (∫⁻ s in T, G s ^ (3 / 2 : ℝ)) := by
        have hconst := lintegral_const_mul'
          (μ := volume.restrict T) (K * A₀ ^ (3 / 2 : ℝ))
          (fun s : ℝ => G s ^ (3 / 2 : ℝ))
          (ENNReal.mul_ne_top hKtop
            (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hA₀top))
        simpa only [mul_assoc] using hconst
      _ ≤ _ := by
        calc
          _ ≤ K * A₀ ^ (3 / 2 : ℝ) *
              (G₂ ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ)) :=
            mul_le_mul_of_nonneg_left hGpow (by positivity)
          _ = K * A₀ ^ (3 / 2 : ℝ) * G₂ ^ (3 / 4 : ℝ) *
              V ^ (1 / 4 : ℝ) := by ring
  have hsecond : (∫⁻ s in T, K * R * A s ^ (3 : ℝ)) ≤
      K * R * V * A₀ ^ (3 : ℝ) := by
    have hpoint : ∀ᵐ s ∂volume.restrict T,
        K * R * A s ^ (3 : ℝ) ≤ K * R * A₀ ^ (3 : ℝ) := by
      filter_upwards [hA₀] with s hs
      gcongr
    calc
      _ ≤ ∫⁻ s in T, K * R * A₀ ^ (3 : ℝ) := lintegral_mono_ae hpoint
      _ = K * R * (volume T) * A₀ ^ (3 : ℝ) := by
        rw [lintegral_const]
        simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter]
        ring
      _ ≤ _ := by gcongr
  have hfirstmeas : AEMeasurable
      (fun s => K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ))
      (volume.restrict T) :=
    (aemeasurable_const.mul (hA.pow_const (3 / 2 : ℝ))).mul hGmeas
  calc
    _ = (∫⁻ s in T, K * A s ^ (3 / 2 : ℝ) * G s ^ (3 / 2 : ℝ)) +
        (∫⁻ s in T, K * R * A s ^ (3 : ℝ)) :=
      lintegral_add_left' hfirstmeas _
    _ ≤ _ := add_le_add hfirst hsecond

end CKN
