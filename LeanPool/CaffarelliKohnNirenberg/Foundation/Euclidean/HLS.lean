/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.Hedberg

/-!
# The order-one Hardy--Littlewood--Sobolev estimate in dimension three

The exponent used by the pressure decomposition is `m = 5/2`, `s = 15`.
The proof is Hedberg's pointwise estimate followed by the strong maximal
estimate.  The a.e. maximal-data hypothesis is exposed so that zero data and
finite truncations can be handled by the consuming pressure lemma.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric Filter


noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- The constant in the three-dimensional order-one HLS estimate. -/
def hlsRieszConstant : ℝ≥0∞ :=
  (hedbergNearConstant + hedbergFarConstant) *
    (maximalStrongConstant (5 / 2 : ℝ)) ^ (1 / 15 : ℝ)

private lemma rieszPotentialOne_power_bound
    {A B M P : ℝ≥0∞}
    (hP : P ≤ A * M ^ (1 / 6 : ℝ) * B ^ (5 / 6 : ℝ)) :
    P ^ (15 : ℝ) ≤ A ^ (15 : ℝ) * M ^ (5 / 2 : ℝ) * B ^ (25 / 2 : ℝ) := by
  have hpow := ENNReal.rpow_le_rpow hP (by norm_num : (0 : ℝ) ≤ 15)
  calc
    P ^ (15 : ℝ) ≤
        (A * M ^ (1 / 6 : ℝ) * B ^ (5 / 6 : ℝ)) ^ (15 : ℝ) := hpow
    _ = A ^ (15 : ℝ) * M ^ (5 / 2 : ℝ) * B ^ (25 / 2 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
      congr 1 <;> norm_num

theorem rieszPotentialOne_hls_of_good
    {f : Vec3 → ℝ} (hf : Measurable f)
    (hfp : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) < ∞)
    (hI0 : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ≠ 0)
    (hgood : ∀ᵐ z ∂volume,
      maximalMajorant f z ≠ 0 ∧ maximalMajorant f z ≠ ∞) :
    (∫⁻ z, rieszPotentialOne f z ^ (15 : ℝ)) ^ (1 / 15 : ℝ) ≤
      hlsRieszConstant *
        (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  let M : Vec3 → ℝ≥0∞ := maximalMajorant f
  let A : ℝ≥0∞ := hedbergNearConstant + hedbergFarConstant
  let I : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)
  let B : ℝ≥0∞ := I ^ (2 / 5 : ℝ)
  have hI0' : I ≠ 0 := by simpa [I] using hI0
  have hB0 : B ≠ 0 := by
    dsimp [B]
    exact (ENNReal.rpow_pos (lt_of_le_of_ne bot_le (Ne.symm hI0'))
      (ne_of_lt hfp)).ne'
  have hBtop : B ≠ ∞ := by
    have hItop : I ≠ ∞ := by simpa [I] using (ne_of_lt hfp)
    dsimp [B]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hItop
  have hMmeas : Measurable M := by
    dsimp [M, maximalMajorant]
    exact measurable_maximalFunction _
  have hI_def : I = ∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ) := rfl
  have hstrong :
      ∫⁻ z, M z ^ (5 / 2 : ℝ) ≤
        maximalStrongConstant (5 / 2 : ℝ) * I := by
    dsimp [M, I]
    exact lintegral_rpow_maximalFunction_le
      (hf.norm.ennreal_ofReal) (by norm_num) hfp
  have hpoint : ∀ᵐ z ∂volume,
      rieszPotentialOne f z ^ (15 : ℝ) ≤
        A ^ (15 : ℝ) * M z ^ (5 / 2 : ℝ) * B ^ (25 / 2 : ℝ) := by
    have hM' : IsMaximalMajorant f M := by
      dsimp [M]
      exact isMaximalMajorant_maximalMajorant f
    filter_upwards [hgood] with z hz
    have hhed := rieszPotentialOne_hedberg (f := f) hf.aemeasurable hM' z
      hz.1 hz.2 hB0 hBtop
    have hBpow : B ^ (5 / 6 : ℝ) = I ^ (1 / 3 : ℝ) := by
      dsimp [B]
      rw [← ENNReal.rpow_mul]
      congr 1
      norm_num
    apply rieszPotentialOne_power_bound (A := A) (B := B)
    rw [hBpow]
    simpa [A] using hhed
  have hpower :
      (∫⁻ z, rieszPotentialOne f z ^ (15 : ℝ)) ≤
        A ^ (15 : ℝ) * B ^ (25 / 2 : ℝ) *
          (maximalStrongConstant (5 / 2 : ℝ) * I) := by
    by_cases hAtop : A = ∞
    · have hBpow0 : B ^ (25 / 2 : ℝ) ≠ 0 := by
        exact (ENNReal.rpow_pos
          (lt_of_le_of_ne bot_le (Ne.symm hB0)) hBtop).ne'
      have hSCpos : 0 < maximalStrongConstant (5 / 2 : ℝ) := by
        unfold maximalStrongConstant
        apply ENNReal.div_pos
        · positivity
        · exact ENNReal.ofReal_ne_top
      have hprod0 : maximalStrongConstant (5 / 2 : ℝ) * I ≠ 0 :=
        mul_ne_zero (ne_of_gt hSCpos) hI0'
      have hA15 : A ^ (15 : ℝ) = ∞ := by
        rw [hAtop, ENNReal.top_rpow_of_pos]
        norm_num
      rw [hA15]
      simp [hBpow0, hprod0]
    ·
      calc
        (∫⁻ z, rieszPotentialOne f z ^ (15 : ℝ)) ≤
            ∫⁻ z, A ^ (15 : ℝ) * M z ^ (5 / 2 : ℝ) * B ^ (25 / 2 : ℝ) :=
          lintegral_mono_ae hpoint
        _ = A ^ (15 : ℝ) * B ^ (25 / 2 : ℝ) *
            (∫⁻ z, M z ^ (5 / 2 : ℝ)) := by
          have heq : (fun z : Vec3 =>
              A ^ (15 : ℝ) * M z ^ (5 / 2 : ℝ) * B ^ (25 / 2 : ℝ)) =
              (fun z : Vec3 =>
                A ^ (15 : ℝ) * B ^ (25 / 2 : ℝ) * M z ^ (5 / 2 : ℝ)) := by
            funext z
            ac_rfl
          rw [heq, lintegral_const_mul']
          exact ENNReal.mul_ne_top
            (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hAtop)
            (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBtop)
        _ ≤ A ^ (15 : ℝ) * B ^ (25 / 2 : ℝ) *
            (maximalStrongConstant (5 / 2 : ℝ) * I) := by
          gcongr
  have hroot := ENNReal.rpow_le_rpow hpower (by norm_num : (0 : ℝ) ≤ 1 / 15)
  calc
    (∫⁻ z, rieszPotentialOne f z ^ (15 : ℝ)) ^ (1 / 15 : ℝ) ≤
        (A ^ (15 : ℝ) * B ^ (25 / 2 : ℝ) *
          (maximalStrongConstant (5 / 2 : ℝ) * I)) ^ (1 / 15 : ℝ) := hroot
    _ = A * (maximalStrongConstant (5 / 2 : ℝ)) ^ (1 / 15 : ℝ) *
        I ^ (2 / 5 : ℝ) := by
      have hA : (A ^ (15 : ℝ)) ^ (1 / 15 : ℝ) = A := by
        rw [← ENNReal.rpow_mul]
        norm_num
      have hB : (B ^ (25 / 2 : ℝ)) ^ (1 / 15 : ℝ) =
          I ^ (1 / 3 : ℝ) := by
        dsimp [B]
        rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        congr 1
        norm_num
      have hC :
          (maximalStrongConstant (5 / 2 : ℝ) * I) ^ (1 / 15 : ℝ) =
            maximalStrongConstant (5 / 2 : ℝ) ^ (1 / 15 : ℝ) *
              I ^ (1 / 15 : ℝ) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
      calc
        (A ^ (15 : ℝ) * B ^ (25 / 2 : ℝ) *
            (maximalStrongConstant (5 / 2 : ℝ) * I)) ^ (1 / 15 : ℝ) =
            (A ^ (15 : ℝ) * B ^ (25 / 2 : ℝ)) ^ (1 / 15 : ℝ) *
              (maximalStrongConstant (5 / 2 : ℝ) * I) ^ (1 / 15 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        _ = ((A ^ (15 : ℝ)) ^ (1 / 15 : ℝ) *
              (B ^ (25 / 2 : ℝ)) ^ (1 / 15 : ℝ)) *
              (maximalStrongConstant (5 / 2 : ℝ) * I) ^ (1 / 15 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        _ = A * I ^ (1 / 3 : ℝ) *
              (maximalStrongConstant (5 / 2 : ℝ) ^ (1 / 15 : ℝ) *
                I ^ (1 / 15 : ℝ)) := by rw [hA, hB, hC]
        _ = A * maximalStrongConstant (5 / 2 : ℝ) ^ (1 / 15 : ℝ) *
              I ^ (2 / 5 : ℝ) := by
          calc
            _ = A * maximalStrongConstant (5 / 2 : ℝ) ^ (1 / 15 : ℝ) *
                (I ^ (1 / 3 : ℝ) * I ^ (1 / 15 : ℝ)) := by ac_rfl
            _ = _ := by
              rw [← ENNReal.rpow_add _ _ hI0' (ne_of_lt hfp)]
              congr 2
              norm_num
    _ = hlsRieszConstant *
        (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
      rfl

theorem maximalMajorant_ne_zero_of_integral_ne_zero
    {f : Vec3 → ℝ} (hf : Measurable f)
    (hI0 : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ≠ 0) (z : Vec3) :
    maximalMajorant f z ≠ 0 := by
  intro hz
  have hM := isMaximalMajorant_maximalMajorant f
  have hball : ∀ n : ℕ,
      (∫⁻ w in Metric.ball z ((n : ℝ) + 1), ENNReal.ofReal |f w|) = 0 := by
    intro n
    have h := hM z ((n : ℝ) + 1) (by positivity)
    rw [hz, zero_mul] at h
    exact bot_unique h
  have hunion : (⋃ n : ℕ, Metric.ball z ((n : ℝ) + 1)) = Set.univ := by
    ext w
    simp only [mem_iUnion, mem_ball, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (dist z w)
    refine ⟨n, ?_⟩
    rw [dist_comm]
    linarith only [hn]
  have hglobal : (∫⁻ w, ENNReal.ofReal |f w|) = 0 := by
    have hglobal' : (∫⁻ w in ⋃ n : ℕ, Metric.ball z ((n : ℝ) + 1),
        ENNReal.ofReal |f w|) = 0 := by
      apply le_antisymm
      · calc
          (∫⁻ w in ⋃ n : ℕ, Metric.ball z ((n : ℝ) + 1),
              ENNReal.ofReal |f w|) ≤
              ∑' n : ℕ, ∫⁻ w in Metric.ball z ((n : ℝ) + 1),
                ENNReal.ofReal |f w| := lintegral_iUnion_le _ _
          _ = 0 := by simp [hball]
      · exact bot_le
    simpa [hunion] using hglobal'
  have hfzero : (fun w : Vec3 => ENNReal.ofReal |f w|) =ᵐ[volume] 0 :=
    (lintegral_eq_zero_iff'
      (by simpa only [Real.norm_eq_abs] using
        (hf.norm.ennreal_ofReal).aemeasurable)).mp hglobal
  have hIzero : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hfzero] with w hw
    simp [hw]
  exact hI0 hIzero

theorem rieszPotentialOne_hls
    {f : Vec3 → ℝ} (hf : Measurable f)
    (hfp : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) < ∞)
    (hI0 : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ≠ 0) :
    (∫⁻ z, rieszPotentialOne f z ^ (15 : ℝ)) ^ (1 / 15 : ℝ) ≤
      hlsRieszConstant *
        (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  have htop := ae_lt_top_maximalFunction
    (f := fun w : Vec3 => ENNReal.ofReal |f w|)
    (hf.norm.ennreal_ofReal) (by norm_num) hfp
  have hgood : ∀ᵐ z ∂volume,
      maximalMajorant f z ≠ 0 ∧ maximalMajorant f z ≠ ∞ := by
    filter_upwards [htop] with z hz
    exact ⟨maximalMajorant_ne_zero_of_integral_ne_zero hf hI0 z,
      ne_of_lt (show maximalMajorant f z < ∞ by simpa [maximalMajorant] using hz)⟩
  exact rieszPotentialOne_hls_of_good hf hfp hI0 hgood

theorem rieszPotentialOne_hls_of_zero_or_good
    {f : Vec3 → ℝ} (hf : Measurable f)
    (hfp : (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) < ∞) :
    (∫⁻ z, rieszPotentialOne f z ^ (15 : ℝ)) ^ (1 / 15 : ℝ) ≤
      hlsRieszConstant *
        (∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)) ^ (2 / 5 : ℝ) := by
  let I : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal |f w| ^ (5 / 2 : ℝ)
  by_cases hI0 : I = 0
  · have hfzero0 : (fun w : Vec3 => ENNReal.ofReal |f w|) =ᵐ[volume] 0 :=
      ENNReal.ae_eq_zero_of_lintegral_rpow_eq_zero (by norm_num)
        (hf.norm.ennreal_ofReal).aemeasurable hI0
    have hfzero : f =ᵐ[volume] 0 := by
      filter_upwards [hfzero0] with w hw
      have habs : |f w| = 0 := by
        apply le_antisymm
        · exact ENNReal.ofReal_eq_zero.mp hw
        · exact abs_nonneg _
      exact abs_eq_zero.mp habs
    have hpot : ∀ z : Vec3, rieszPotentialOne f z = 0 := by
      intro z
      unfold rieszPotentialOne
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hfzero] with w hw
      simp [hw]
    have hfun : (fun z => rieszPotentialOne f z) =ᵐ[volume] 0 :=
      Eventually.of_forall hpot
    have hnorm := eLpNorm'_eq_zero_of_ae_zero (f := fun z => rieszPotentialOne f z)
      (by norm_num : (0 : ℝ) < 15) hfun
    calc
      (∫⁻ z, rieszPotentialOne f z ^ (15 : ℝ)) ^ (1 / 15 : ℝ) =
          eLpNorm' (fun z => rieszPotentialOne f z) (15 : ℝ) volume := by
        rw [eLpNorm'_eq_lintegral_enorm]
        congr 1
      _ = 0 := hnorm
      _ ≤ hlsRieszConstant * I ^ (2 / 5 : ℝ) := by simp [hI0]
  · exact rieszPotentialOne_hls hf hfp hI0

end CKN.Foundation.Euclidean
