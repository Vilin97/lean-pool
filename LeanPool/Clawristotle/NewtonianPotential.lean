/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombKernel
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Newtonian Potential Bounds and Inverse-Norm Integrability

Proves `coulomb_landauMatrix_entry_le` (|A(z)_{ij}| <= ||z||^{-1}) and local
integrability of ||z||^{-1} against Schwartz functions, the key estimates for
handling the Coulomb singularity in collision integrals.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- Coulomb Landau matrix entry bound: |A(z)_{ij}| ≤ (eucNorm z)⁻¹ for z ≠ 0,
    and A(0) = 0. This is the key bound enabling integrability of collision
    integrands despite the singular kernel Ψ(r) = r⁻³. -/
lemma coulomb_landauMatrix_entry_le (z : Fin 3 → ℝ) (i j : Fin 3) :
    |landauMatrix coulombKernel z i j| ≤
      if z = 0 then 0 else (eucNorm z)⁻¹ := by
  by_cases hz : z = 0
  · -- z = 0: landauMatrix _ 0 = 0 (inner matrix vanishes)
    simp [hz, landauMatrix, innerLandauMatrix, normSq, dotProduct, vecMulVec, eucNorm]
  · rw [if_neg hz]
    -- |Ψ(|z|) * B(z)_{ij}| ≤ |z|^{-3} * |z|² = |z|^{-1}
    simp only [landauMatrix, smul_apply, smul_eq_mul]
    have henz : 0 < eucNorm z := by
      rw [eucNorm]; exact Real.sqrt_pos_of_pos (normSq_pos hz)
    have h_inner : |innerLandauMatrix z i j| ≤ normSq z := by
      rw [innerLandauMatrix_apply]
      have hns : normSq z = ∑ k : Fin 3, z k * z k := by
        simp [normSq, dotProduct, Fin.sum_univ_three]
      split_ifs with hij
      · subst hij
        rw [hns]
        simp only [Fin.sum_univ_three]
        have hz0 := mul_self_nonneg (z 0)
        have hz1 := mul_self_nonneg (z 1)
        have hz2 := mul_self_nonneg (z 2)
        fin_cases i <;>
          simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, add_sub_cancel_right,
            ge_iff_le] <;>
          rw [abs_of_nonneg (by nlinarith)] <;> nlinarith
      · simp only [zero_sub, abs_neg]
        rw [hns]
        simp only [Fin.sum_univ_three]
        have habs0 := abs_mul_abs_self (z 0)
        have habs1 := abs_mul_abs_self (z 1)
        have habs2 := abs_mul_abs_self (z 2)
        fin_cases i <;> fin_cases j <;> simp_all <;>
          nlinarith [sq_abs (z 0), sq_abs (z 1), sq_abs (z 2),
            sq_nonneg (|z 0| - |z 1|), sq_nonneg (|z 0| - |z 2|),
            sq_nonneg (|z 1| - |z 2|)]
    calc |coulombKernel (eucNorm z) * innerLandauMatrix z i j|
        = |coulombKernel (eucNorm z)| * |innerLandauMatrix z i j| := abs_mul _ _
      _ ≤ |coulombKernel (eucNorm z)| * normSq z :=
          mul_le_mul_of_nonneg_left h_inner (abs_nonneg _)
      _ = eucNorm z ^ (-3 : ℝ) * normSq z := by
          congr 1
          rw [coulombKernel, if_neg (by linarith : ¬eucNorm z ≤ 0)]
          exact abs_of_pos (rpow_pos_of_pos henz _)
      _ = eucNorm z ^ (-3 : ℝ) * eucNorm z ^ (2 : ℕ) := by
          congr 1; exact (eucNorm_sq z).symm
      _ = (eucNorm z)⁻¹ := by
          rw [← rpow_natCast (eucNorm z) 2, ← rpow_add henz]
          change eucNorm z ^ ((-3 : ℝ) + (2 : ℝ)) = (eucNorm z)⁻¹
          norm_num [rpow_neg_one]

/-- Pi norm ≤ Euclidean norm in ℝ³: ‖z‖_∞ ≤ √(z·z). -/
lemma pi_norm_le_eucNorm (z : Fin 3 → ℝ) : ‖z‖ ≤ eucNorm z := by
  rw [pi_norm_le_iff_of_nonneg (eucNorm_nonneg z)]
  intro i; rw [Real.norm_eq_abs, eucNorm, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  unfold normSq dotProduct; simp only [Fin.sum_univ_three]
  fin_cases i <;> simp <;>
    nlinarith [mul_self_nonneg (z 0), mul_self_nonneg (z 1), mul_self_nonneg (z 2)]

/-- Coulomb matrix entry bound in Pi norm: |A(z)_{ij}| ≤ ‖z‖⁻¹ for z ≠ 0. -/
lemma coulomb_landauMatrix_entry_le_pi (z : Fin 3 → ℝ) (i j : Fin 3)
    (hz : z ≠ 0) :
    |landauMatrix coulombKernel z i j| ≤ ‖z‖⁻¹ := by
  have h := coulomb_landauMatrix_entry_le z i j
  rw [if_neg hz] at h
  exact le_trans h (inv_anti₀ (norm_pos_iff.mpr hz) (pi_norm_le_eucNorm z))


lemma inv_norm_summable_series (R : ℝ) (hR : 0 < R) :
    Summable (fun k : ℕ => (2^(-k-1 : ℝ) * R)⁻¹ * (2^(-k : ℝ) * R)^3) := by
  have hRne : R ≠ 0 := hR.ne'
  norm_num [ Real.rpow_sub ]
  ring_nf
  norm_num [ hRne ]
  norm_num [ pow_mul', mul_assoc, hRne ]
  norm_num only [ ← mul_assoc, ← mul_pow ]
  ring_nf
  norm_num [ hRne ]
  exact Summable.mul_right _
    (Summable.mul_left _
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)))

lemma inv_norm_ball_volume (R : ℝ) (hR : 0 < R) (k : ℕ) :
    (MeasureTheory.volume (Metric.closedBall (0 : Fin 3 → ℝ) (2^(-k : ℝ) * R))).toReal =
    (2^(-k : ℝ) * R)^3 * (MeasureTheory.volume (Metric.closedBall (0 : Fin 3 → ℝ) 1)).toReal := by
  rw [ MeasureTheory.Measure.addHaar_closedBall ]
  · norm_num
    ring_nf
    positivity
  · positivity

lemma inv_norm_lintegral_bounded (R : ℝ) (hR : 0 < R) (k : ℕ) :
    ∫⁻ (z : Fin 3 → ℝ) in
      Metric.closedBall 0 (2^(-k : ℝ) * R) \
      Metric.closedBall 0 (2^(-k-1 : ℝ) * R),
      ENNReal.ofReal (‖z‖⁻¹) ≤
    ENNReal.ofReal ((2^(-k-1 : ℝ) * R)⁻¹ *
      (MeasureTheory.volume
        (Metric.closedBall (0 : Fin 3 → ℝ)
          (2^(-k : ℝ) * R))).toReal) := by
  have h_bounded : ∀ z : Fin 3 → ℝ,
      z ∈ Metric.closedBall 0 (2^(-k : ℝ) * R) \
        Metric.closedBall 0 (2^(-k-1 : ℝ) * R) →
      ‖z‖⁻¹ ≤ (2^(-k-1 : ℝ) * R)⁻¹ := by
    simp +zetaDelta only [rpow_neg_natCast, zpow_neg, zpow_natCast, Set.mem_diff,
      Metric.mem_closedBall, dist_zero_right, not_le, _root_.mul_inv_rev, and_imp] at *
    intro z hz₁ hz₂
    rw [ ← mul_inv ]
    gcongr
    norm_num [ Real.rpow_sub ] at *
    linarith
  have h_const_bound :
      ∫⁻ (z : Fin 3 → ℝ) in
        Metric.closedBall 0 (2^(-k : ℝ) * R) \
        Metric.closedBall 0 (2^(-k-1 : ℝ) * R),
        ENNReal.ofReal (‖z‖⁻¹) ≤
      ∫⁻ (_z : Fin 3 → ℝ) in
        Metric.closedBall 0 (2^(-k : ℝ) * R) \
        Metric.closedBall 0 (2^(-k-1 : ℝ) * R),
        ENNReal.ofReal ((2 ^ (-(k : ℝ) - 1) * R)⁻¹) :=
    MeasureTheory.lintegral_mono_ae (by
      filter_upwards [MeasureTheory.ae_restrict_mem <|
        measurableSet_closedBall.diff
          measurableSet_closedBall]
        with z hz using
        ENNReal.ofReal_le_ofReal <|
          h_bounded z hz)
  refine le_trans h_const_bound ?_
  simp +zetaDelta only [rpow_neg_natCast, zpow_neg, zpow_natCast, _root_.mul_inv_rev,
    lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter] at *
  rw [ ENNReal.ofReal_mul (by positivity) ]
  rw [ ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity) ]
  gcongr
  calc volume (Metric.closedBall 0 ((2 ^ k) ⁻¹ * R) \
        Metric.closedBall 0 (2 ^ (-(k : ℝ) - 1) * R))
      ≤ volume (Metric.closedBall (0 : Fin 3 → ℝ) ((2 ^ k) ⁻¹ * R)) :=
        MeasureTheory.measure_mono Set.diff_subset
    _ ≤ ENNReal.ofReal (volume (Metric.closedBall (0 : Fin 3 → ℝ)
        ((2 ^ k) ⁻¹ * R))).toReal := by
        rw [ ENNReal.ofReal_toReal ]
        exact ne_of_lt (isCompact_closedBall _ _ |> IsCompact.measure_lt_top)

-- lintegral_iUnion + ENNReal arithmetic requires extended unification
/-- ‖·‖⁻¹ is locally integrable in ℝ³. Proved by Aristotle (job 3dc1b4dc).
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma inv_norm_local_integrable (R : ℝ) (hR : 0 < R) :
    IntegrableOn (fun z : Fin 3 → ℝ => ‖z‖⁻¹)
      (Metric.closedBall (0 : Fin 3 → ℝ) R) := by
  have h_integrable : MeasureTheory.IntegrableOn
      (fun z : (Fin 3) → ℝ => (‖z‖)⁻¹)
      (Metric.closedBall 0 R \ {0}) := by
    have h_integrable : ∫⁻ (z : (Fin 3) → ℝ) in
        Metric.closedBall 0 R \ {0},
        ENNReal.ofReal (‖z‖⁻¹) < ⊤ := by
      have h_integrable : ∫⁻ (z : Fin 3 → ℝ) in
          Metric.closedBall 0 R \ {0},
          ENNReal.ofReal (‖z‖⁻¹) ≤
        ∑' (k : ℕ), ∫⁻ (z : Fin 3 → ℝ) in
          Metric.closedBall 0 (2^(-k : ℝ) * R) \
          Metric.closedBall 0 (2^(-k-1 : ℝ) * R),
          ENNReal.ofReal (‖z‖⁻¹) := by
        rw [ ← MeasureTheory.lintegral_iUnion ]
        · refine MeasureTheory.lintegral_mono_set ?_
          intro x hx
          obtain ⟨k, hk⟩ : ∃ k : ℕ, 2^(-k-1 : ℝ) * R < ‖x‖ ∧ ‖x‖ ≤ 2^(-k : ℝ) * R := by
            obtain ⟨k, hk⟩ : ∃ k : ℕ,
                -k - 1 < Real.logb 2 (‖x‖ / R) ∧ Real.logb 2 (‖x‖ / R) ≤ -k := by
              use Nat.floor (-Real.logb 2 (‖x‖ / R))
              constructor <;> linarith [
                Nat.floor_le (show 0 ≤ -Real.logb 2 (‖x‖ / R) by
                  exact neg_nonneg_of_nonpos
                    (Real.logb_nonpos (by norm_num)
                      (div_nonneg (norm_nonneg x) hR.le)
                      (div_le_one_of_le₀
                        (by simpa using hx.1.out)
                        hR.le))),
                Nat.lt_floor_add_one
                  (-Real.logb 2 (‖x‖ / R))]
            rw [Real.lt_logb_iff_rpow_lt,
              Real.logb_le_iff_le_rpow] at hk
              <;> norm_num at *
              <;> try positivity
            · exact ⟨k,
                by rw [lt_div_iff₀ hR] at hk; linarith,
                by rw [div_le_iff₀ hR] at hk; linarith⟩
            · exact div_pos (norm_pos_iff.mpr hx.2) hR
            · exact div_pos (norm_pos_iff.mpr hx.2) hR
          exact Set.mem_iUnion.mpr ⟨k, by
            simp only [Set.mem_diff, Metric.mem_closedBall, dist_zero_right]
            constructor
            · convert hk.2 using 2
            · intro h_le
              have : ‖x‖ ≤ 2 ^ (-(↑k : ℝ) - 1) * R := by convert h_le using 2
              linarith [hk.1]⟩
        · exact fun i => MeasurableSet.diff (measurableSet_closedBall) (measurableSet_closedBall)
        · intro k l hkl
          simp_all [ mul_comm, Real.rpow_sub ]
          ring_nf
          norm_num [ hR.ne' ]
          cases lt_or_gt_of_ne hkl <;> norm_num [ Set.disjoint_left ]
          · intro a ha₁ ha₂ ha₃
            nlinarith [show (1 / 2 : ℝ) ^ l ≤
                (1 / 2 : ℝ) ^ k / 2 by
              exact le_trans
                (pow_le_pow_of_le_one
                  (by norm_num) (by norm_num)
                  (show l ≥ k + 1 by linarith))
                (by ring_nf; norm_num)]
          · intro a ha₁ ha₂ ha₃
            nlinarith [show (1 / 2 : ℝ) ^ k ≤
                (1 / 2 : ℝ) ^ l * (1 / 2) by
              rw [← pow_succ]
              exact pow_le_pow_of_le_one
                (by norm_num) (by norm_num)
                (by linarith)]
      have h_bounded := inv_norm_lintegral_bounded R hR
      have h_volume := inv_norm_ball_volume R hR
      have h_series := inv_norm_summable_series R hR
      refine lt_of_le_of_lt h_integrable <| lt_of_le_of_lt (ENNReal.tsum_le_tsum h_bounded) ?_
      rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num [ h_volume ]
      · exact fun k => by positivity
      · convert h_series.mul_right
            ((MeasureTheory.volume (Metric.closedBall (0 : Fin 3 → ℝ) 1)
              |> ENNReal.toReal)) using 2
        norm_num [ Real.rpow_add, Real.rpow_sub ]
        ring_nf
        convert congr_arg (· * R⁻¹ * 2 ^ ‹_› * 2) (h_volume ‹_›) using 1
          <;> norm_num [ Real.rpow_neg, Real.rpow_mul ]
        · ring_nf
          norm_num [ mul_comm ]
        · field_simp
          ring_nf
          norm_num [ ← mul_pow ]
    refine ⟨ ?_, ?_ ⟩
    · exact Measurable.aestronglyMeasurable (by exact Measurable.inv (measurable_norm))
    · rw [MeasureTheory.hasFiniteIntegral_iff_norm]
      convert h_integrable using 2
      ext z
      congr 1
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
  rwa [ MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set ]
  rw [ MeasureTheory.ae_eq_set ]; norm_num
  exact MeasureTheory.measure_mono_null (fun x hx => hx.2) (MeasureTheory.measure_singleton 0)


/-- Convolution of a locally integrable kernel with a Schwartz function is integrable.
    Proved by Aristotle (job 1ba752be).
    Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun> -/
lemma convolution_local_int_schwartz
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ, |g w| * (1 + ‖w‖) ^ N ≤ C)
    (hg_meas : AEStronglyMeasurable g volume)
    (hK_local : IntegrableOn (fun z : Fin 3 → ℝ => ‖z‖⁻¹)
      (Metric.closedBall (0 : Fin 3 → ℝ) 1))
    (v : Fin 3 → ℝ) :
    Integrable (fun w => ‖v - w‖⁻¹ * g w) := by
  have h_near :
      MeasureTheory.IntegrableOn
        (fun w => ‖v - w‖⁻¹ * g w)
        (Metric.closedBall v 1) := by
    obtain ⟨M, hM⟩ : ∃ M > 0, ∀ w ∈ Metric.closedBall v 1, |g w| ≤ M := by
      obtain ⟨ C, hC₀, hC ⟩ := hg_decay 0; exact ⟨ C, hC₀, fun w hw => by simpa using hC w ⟩
    have h_inv_integrable :
        MeasureTheory.IntegrableOn (fun w => ‖v - w‖⁻¹) (Metric.closedBall v 1) := by
      rw [ ← MeasureTheory.integrable_indicator_iff (measurableSet_closedBall) ] at *
      convert hK_local.comp_sub_left v using 1
      ext; simp [Set.indicator]
      simp [ dist_eq_norm' ]
    have h_prod_integrable :
        MeasureTheory.IntegrableOn (fun w => M * ‖v - w‖⁻¹) (Metric.closedBall v 1) :=
      h_inv_integrable.const_mul M
    refine h_prod_integrable.mono' ?_ ?_
    · exact MeasureTheory.AEStronglyMeasurable.mul
        (Measurable.aestronglyMeasurable <| by
          exact Measurable.inv <|
            measurable_norm.comp <|
            measurable_const.sub measurable_id')
        (hg_meas.mono_measure <|
          MeasureTheory.Measure.restrict_le_self)
    · filter_upwards [
        MeasureTheory.ae_restrict_mem
          measurableSet_closedBall]
        with w hw
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (v - w)))]
      calc ‖v - w‖⁻¹ * |g w| ≤ ‖v - w‖⁻¹ * M :=
            mul_le_mul_of_nonneg_left (hM.2 w hw) (inv_nonneg.mpr (norm_nonneg _))
        _ = M * ‖v - w‖⁻¹ := mul_comm _ _
  have h_far :
      MeasureTheory.IntegrableOn
        (fun w => ‖v - w‖⁻¹ * g w)
        (Set.univ \ Metric.closedBall v 1) := by
    have h_integrable_g : MeasureTheory.Integrable g := by
      obtain ⟨ C, hC₀, hC ⟩ := hg_decay 4
      exact (inverse_poly_integrable C).mono' hg_meas
        (Filter.Eventually.of_forall fun w => by
          rw [ le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖w‖) ^ 4) ]
          exact hC w)
    have h_far_abs : MeasureTheory.IntegrableOn
        (fun w => ‖g w‖) (Set.univ \ Metric.closedBall v 1) :=
      h_integrable_g.norm.integrableOn
    exact h_far_abs.mono' (by
        exact MeasureTheory.AEStronglyMeasurable.mul
          (Measurable.aestronglyMeasurable (Measurable.inv
            (measurable_norm.comp (measurable_const.sub measurable_id'))))
          (hg_meas.mono_measure MeasureTheory.Measure.restrict_le_self))
      (by
        filter_upwards [
          MeasureTheory.ae_restrict_mem
            (MeasurableSet.univ.diff measurableSet_closedBall)]
          with w hw
        simp only [Real.norm_eq_abs]
        rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg (v - w)))]
        have hw_far : 1 ≤ ‖v - w‖ := by
          rw [Set.mem_diff] at hw
          by_contra h_lt
          rw [not_le] at h_lt
          exact hw.2 (Metric.mem_closedBall.mpr (by rw [dist_comm, dist_eq_norm]; linarith))
        calc ‖v - w‖⁻¹ * |g w| ≤ 1 * |g w| :=
              mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hw_far) (abs_nonneg _)
          _ = |g w| := one_mul _
          _ = ‖g w‖ := (Real.norm_eq_abs _).symm)
  rw [← MeasureTheory.integrableOn_univ]
  rw [show (Set.univ : Set (Fin 3 → ℝ)) = Metric.closedBall v 1 ∪ (Set.univ \ Metric.closedBall v 1)
    from by simp [Set.union_diff_cancel (Set.subset_univ _)]]
  exact h_near.union h_far

/-- Key integrability fact for Coulomb kernel: ‖·‖⁻¹ × Schwartz is integrable in ℝ³.
    Combines inv_norm_local_integrable and convolution_local_int_schwartz. -/
lemma inv_norm_schwartz_integrable
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ, |g w| * (1 + ‖w‖) ^ N ≤ C)
    (hg_meas : AEStronglyMeasurable g volume)
    (v : Fin 3 → ℝ) :
    Integrable (fun w => ‖v - w‖⁻¹ * g w) :=
  convolution_local_int_schwartz g hg_decay hg_meas (inv_norm_local_integrable 1 one_pos) v

lemma newtonian_near_bound
    (g : (Fin 3 → ℝ) → ℝ)
    (C₀ : ℝ) (hg_sup : ∀ w, |g w| ≤ C₀)
    (v : Fin 3 → ℝ)
    (h_int_translated : Integrable (fun z : Fin 3 → ℝ => ‖z‖⁻¹ * |g (v - z)|))
    (h_inv_loc : IntegrableOn (fun z : Fin 3 → ℝ => ‖z‖⁻¹)
      (Metric.closedBall (0 : Fin 3 → ℝ) 1)) :
    ∫ z in Metric.closedBall (0 : Fin 3 → ℝ) 1, ‖z‖⁻¹ * |g (v - z)| ≤
      C₀ * ∫ z in Metric.closedBall (0 : Fin 3 → ℝ) 1, ‖z‖⁻¹ := by
  have h_pw : ∀ z : Fin 3 → ℝ, ‖z‖⁻¹ * |g (v - z)| ≤ C₀ * ‖z‖⁻¹ := fun z =>
    calc ‖z‖⁻¹ * |g (v - z)| ≤ ‖z‖⁻¹ * C₀ :=
        mul_le_mul_of_nonneg_left (hg_sup _) (inv_nonneg.mpr (norm_nonneg _))
      _ = C₀ * ‖z‖⁻¹ := mul_comm _ _
  calc ∫ z in Metric.closedBall (0 : Fin 3 → ℝ) 1, ‖z‖⁻¹ * |g (v - z)|
      ≤ ∫ z in Metric.closedBall (0 : Fin 3 → ℝ) 1, C₀ * ‖z‖⁻¹ :=
        setIntegral_mono h_int_translated.integrableOn
          (h_inv_loc.const_mul _) h_pw
    _ = C₀ * ∫ z in Metric.closedBall (0 : Fin 3 → ℝ) 1, ‖z‖⁻¹ := integral_const_mul _ _


lemma newtonian_far_bound
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_abs_int : Integrable (fun w => |g w|))
    (v : Fin 3 → ℝ)
    (h_int_translated : Integrable (fun z : Fin 3 → ℝ => ‖z‖⁻¹ * |g (v - z)|)) :
    ∫ z in (Metric.closedBall (0 : Fin 3 → ℝ) 1)ᶜ, ‖z‖⁻¹ * |g (v - z)| ≤
      ∫ w, |g w| := by
  calc ∫ z in (Metric.closedBall (0 : Fin 3 → ℝ) 1)ᶜ, ‖z‖⁻¹ * |g (v - z)|
      ≤ ∫ z in (Metric.closedBall (0 : Fin 3 → ℝ) 1)ᶜ, |g (v - z)| := by
        apply setIntegral_mono_on h_int_translated.integrableOn
        · exact (hg_abs_int.comp_sub_left v).integrableOn
        · exact measurableSet_closedBall.compl
        · intro z hz
          rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
          calc ‖z‖⁻¹ * |g (v - z)| ≤ 1 * |g (v - z)| :=
            mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hz.le) (abs_nonneg _)
          _ = |g (v - z)| := one_mul _
    _ ≤ ∫ z, |g (v - z)| :=
        setIntegral_le_integral (hg_abs_int.comp_sub_left v)
          (Filter.Eventually.of_forall fun z => abs_nonneg _)
    _ = ∫ w, |g w| := integral_sub_left_eq_self (fun w => |g w|) volume v


/-- The Newtonian potential (convolution with ‖·‖⁻¹) of a Schwartz function is
    uniformly bounded in ℝ³. Proof: split into near (B(v,1)) and far parts
    near is bounded by sup|g| × ∫_{B(0,1)} ‖z‖⁻¹, far by ∫|g|. -/
lemma newtonian_schwartz_uniform_bound
    (g : (Fin 3 → ℝ) → ℝ)
    (hg_decay : ∀ N : ℕ, ∃ C > 0, ∀ w : Fin 3 → ℝ, |g w| * (1 + ‖w‖) ^ N ≤ C)
    (hg_meas : AEStronglyMeasurable g volume) :
    ∃ M > 0, ∀ v : Fin 3 → ℝ, ∫ w, ‖v - w‖⁻¹ * |g w| ≤ M := by
  -- Step 1: uniform sup bound on |g|
  obtain ⟨C₀, hC₀, hg_raw⟩ := hg_decay 0
  have hg_sup : ∀ w, |g w| ≤ C₀ := fun w => by simpa using hg_raw w
  -- Step 2: integrability of |g| (from decay with N=4)
  obtain ⟨C₄, hC₄, hg_raw4⟩ := hg_decay 4
  have hg_abs_int : Integrable (fun w => |g w|) := by
    apply (inverse_poly_integrable C₄).mono'
    · exact hg_meas.norm
    · filter_upwards with w
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
      exact (le_div_iff₀ (by positivity : (0 : ℝ) < (1 + ‖w‖) ^ 4)).mpr (hg_raw4 w)
  -- Step 3: each v-integral is finite (via norm congr)
  have h_int : ∀ v, Integrable (fun w => ‖v - w‖⁻¹ * |g w|) := fun v =>
    (inv_norm_schwartz_integrable g hg_decay hg_meas v).norm.congr
      (Filter.Eventually.of_forall fun w => by simp)
  -- Step 4: near/far split
  set I_near := ∫ z in Metric.closedBall (0 : Fin 3 → ℝ) 1, ‖z‖⁻¹
  set I_far := ∫ w, |g w|
  have hI_near_nn : 0 ≤ I_near :=
    setIntegral_nonneg measurableSet_closedBall (fun z _ => inv_nonneg.mpr (norm_nonneg z))
  have hI_far_nn : 0 ≤ I_far := integral_nonneg (fun w => abs_nonneg (g w))
  refine ⟨C₀ * I_near + I_far + 1, by linarith [mul_nonneg hC₀.le hI_near_nn], fun v => ?_⟩
  have h_translate : ∫ w, ‖v - w‖⁻¹ * |g w| = ∫ z, ‖z‖⁻¹ * |g (v - z)| := by
    rw [← integral_sub_left_eq_self (fun w => ‖v - w‖⁻¹ * |g w|) volume v]
    congr 1
    ext z
    simp [sub_sub_cancel]
  have h_int_translated : Integrable (fun z => ‖z‖⁻¹ * |g (v - z)|) :=
    ((h_int v).comp_sub_left v).congr
      (Filter.Eventually.of_forall fun z => by simp [sub_sub_cancel])
  rw [h_translate, (integral_add_compl (s := Metric.closedBall (0 : Fin 3 → ℝ) 1)
    measurableSet_closedBall h_int_translated).symm]
  linarith [newtonian_near_bound g C₀ hg_sup v h_int_translated
              (inv_norm_local_integrable 1 one_pos),
            newtonian_far_bound g hg_abs_int v h_int_translated]

end VML
