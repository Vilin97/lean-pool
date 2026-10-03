/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinConvergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.Energy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Density
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.FourierLimit

/-! Fourier coefficient identities for differences of nested Galerkin cutoffs. -/

@[expose] public section

noncomputable section

open MeasureTheory
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalResidualTailMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalResidualTailMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalResidualTailProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

/-- Integer frequencies retained by the symmetric Galerkin cutoff. -/
def GalerkinResidualTail.classicalResidualFrequencyBox (N : ℕ) : Finset (Fin 2 → ℤ) :=
  (symmetricFrequencyBox N).image pairFrequency

theorem GalerkinResidualTail.pairBox_sum_single (N : ℕ)
    (f : ComplexScalarTorusL2) (k : Fin 2 → ℤ) :
    (∑ p ∈ symmetricFrequencyBox N,
        UnitAddTorus.mFourierCoeff f (pairFrequency p) *
          (if k = pairFrequency p then 1 else 0)) =
      if k ∈ GalerkinResidualTail.classicalResidualFrequencyBox N then
        UnitAddTorus.mFourierCoeff f k else 0 := by
  classical
  by_cases hk : k ∈ GalerkinResidualTail.classicalResidualFrequencyBox N
  · obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hk
    have hpair : pairFrequency p = k := hpk
    calc
      (∑ q ∈ symmetricFrequencyBox N,
          UnitAddTorus.mFourierCoeff f (pairFrequency q) *
            (if k = pairFrequency q then 1 else 0)) =
        UnitAddTorus.mFourierCoeff f (pairFrequency p) *
          (if k = pairFrequency p then 1 else 0) :=
            Finset.sum_eq_single_of_mem p hp (by
              intro q hq hqp
              have hne : k ≠ pairFrequency q := by
                intro h
                have hpq : p = q :=
                  (Equiv.injective pairFrequencyEquiv) (hpair.trans h)
                exact hqp hpq.symm
              simp [hne])
      _ = if k ∈ GalerkinResidualTail.classicalResidualFrequencyBox N then
          UnitAddTorus.mFourierCoeff f k else 0 := by
            rw [hpair]
            simp [hk]
  · have hzero : ∀ p ∈ symmetricFrequencyBox N,
        UnitAddTorus.mFourierCoeff f (pairFrequency p) *
          (if k = pairFrequency p then 1 else 0) = 0 := by
      intro p hp
      by_cases hkp : k = pairFrequency p
      · have : k ∈ GalerkinResidualTail.classicalResidualFrequencyBox N :=
          Finset.mem_image.mpr ⟨p, hp, hkp.symm⟩
        exact (hk this).elim
      · simp [hkp]
    calc
      (∑ p ∈ symmetricFrequencyBox N,
          UnitAddTorus.mFourierCoeff f (pairFrequency p) *
            (if k = pairFrequency p then 1 else 0)) = 0 :=
              Finset.sum_eq_zero hzero
      _ = if k ∈ GalerkinResidualTail.classicalResidualFrequencyBox N then
          UnitAddTorus.mFourierCoeff f k else 0 := by simp [hk]

/-- The Hilbert basis coordinates of a finite complex Fourier partial sum are exactly the
retained Fourier coefficients. -/
theorem mFourierBasis_repr_complexFourierPartialSumLp
    (N : ℕ) (f : ComplexScalarTorusL2) (k : Fin 2 → ℤ) :
    (UnitAddTorus.mFourierBasis.repr (complexFourierPartialSumLp N f)) k =
      if k ∈ GalerkinResidualTail.classicalResidualFrequencyBox N then
        UnitAddTorus.mFourierCoeff f k else 0 := by
  classical
  rw [UnitAddTorus.mFourierBasis.repr_apply_apply]
  unfold complexFourierPartialSumLp
  rw [inner_sum]
  simp_rw [inner_smul_right]
  rw [UnitAddTorus.coe_mFourierBasis]
  simp_rw [orthonormal_iff_ite.mp UnitAddTorus.orthonormal_mFourier]
  exact GalerkinResidualTail.pairBox_sum_single N f k

theorem GalerkinResidualTail.classicalResidualFrequencyBox_subset {M N : ℕ} (hMN : M ≤ N) :
    GalerkinResidualTail.classicalResidualFrequencyBox M ⊆
        GalerkinResidualTail.classicalResidualFrequencyBox N := by
  intro k hk
  obtain ⟨p, hp, hpk⟩ := Finset.mem_image.mp hk
  exact Finset.mem_image.mpr ⟨p, symmetricFrequencyBox_subset hMN hp, hpk⟩

theorem GalerkinResidualTail.frequencySq_ge_of_not_mem_box (N : ℕ) (k : Fin 2 → ℤ)
    (hk : k ∉ GalerkinResidualTail.classicalResidualFrequencyBox N) :
    ((N + 1 : ℕ) : ℝ) ^ 2 ≤ AVenhance.Infra.Heat.frequencySq k := by
  have hlarge : (k 0).natAbs > N ∨ (k 1).natAbs > N := by
    by_contra h
    have hle : (k 0).natAbs ≤ N ∧ (k 1).natAbs ≤ N := by omega
    have hcast0 : ((k 0).natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle.1
    have hcast1 : ((k 1).natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle.2
    have habs0 : |(k 0 : ℤ)| ≤ (N : ℤ) := by
      simpa only [Int.natCast_natAbs] using hcast0
    have habs1 : |(k 1 : ℤ)| ≤ (N : ℤ) := by
      simpa only [Int.natCast_natAbs] using hcast1
    rcases abs_le.mp habs0 with ⟨h00, h01⟩
    rcases abs_le.mp habs1 with ⟨h10, h11⟩
    apply hk
    apply Finset.mem_image.mpr
    refine ⟨frequencyPair k, ?_, pairFrequency_frequencyPair k⟩
    simp only [symmetricFrequencyBox, Finset.mem_product, Finset.mem_Icc,
      frequencyPair]
    exact ⟨⟨by omega, h01⟩, ⟨by omega, h11⟩⟩
  have hlargeReal : ((N + 1 : ℕ) : ℝ) ≤ |(k 0 : ℝ)| ∨
      ((N + 1 : ℕ) : ℝ) ≤ |(k 1 : ℝ)| := by
    rcases hlarge with h | h
    · left
      have hnat : N + 1 ≤ (k 0).natAbs := by omega
      have hcast : ((N + 1 : ℕ) : ℝ) ≤ ((k 0).natAbs : ℝ) := by exact_mod_cast hnat
      have hnorm : ((k 0).natAbs : ℝ) = |(k 0 : ℝ)| := by
        have hi : ((k 0).natAbs : ℤ) = |k 0| := Int.natCast_natAbs (k 0)
        have hreal := congrArg (fun z : ℤ => (z : ℝ)) hi
        simpa only [Int.cast_natCast, Int.cast_abs] using hreal
      rw [hnorm] at hcast
      exact hcast
    · right
      have hnat : N + 1 ≤ (k 1).natAbs := by omega
      have hcast : ((N + 1 : ℕ) : ℝ) ≤ ((k 1).natAbs : ℝ) := by exact_mod_cast hnat
      have hnorm : ((k 1).natAbs : ℝ) = |(k 1 : ℝ)| := by
        have hi : ((k 1).natAbs : ℤ) = |k 1| := Int.natCast_natAbs (k 1)
        have hreal := congrArg (fun z : ℤ => (z : ℝ)) hi
        simpa only [Int.cast_natCast, Int.cast_abs] using hreal
      rw [hnorm] at hcast
      exact hcast
  have hfreq : AVenhance.Infra.Heat.frequencySq k =
      (k 0 : ℝ) ^ 2 + (k 1 : ℝ) ^ 2 := by
    simp [AVenhance.Infra.Heat.frequencySq]
  rw [hfreq]
  rcases hlargeReal with h | h
  · have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ ((N + 1 : ℕ) : ℝ))
      (abs_nonneg (k 0 : ℝ))).2 h
    have hsquare' : ((N + 1 : ℕ) : ℝ) ^ 2 ≤ (k 0 : ℝ) ^ 2 := by
      simpa only [sq_abs] using hsquare
    nlinarith [sq_nonneg (k 1 : ℝ)]
  · have hsquare := (sq_le_sq₀ (by positivity : 0 ≤ ((N + 1 : ℕ) : ℝ))
      (abs_nonneg (k 1 : ℝ))).2 h
    have hsquare' : ((N + 1 : ℕ) : ℝ) ^ 2 ≤ (k 1 : ℝ) ^ 2 := by
      simpa only [sq_abs] using hsquare
    nlinarith [sq_nonneg (k 0 : ℝ)]

theorem GalerkinResidualTail.realPart_compLp_sub (f g : ComplexScalarTorusL2) :
    Complex.reCLM.compLp (f - g) =
      Complex.reCLM.compLp f - Complex.reCLM.compLp g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub f g,
    Lp.coeFn_sub (Complex.reCLM.compLp f) (Complex.reCLM.compLp g),
    Complex.reCLM.coeFn_compLp (f - g), Complex.reCLM.coeFn_compLp f,
    Complex.reCLM.coeFn_compLp g] with x hsub hsubRe hfg hff hgg
  calc
    (Complex.reCLM.compLp (f - g)) x = Complex.reCLM ((f - g) x) := hfg
    _ = Complex.reCLM (f x - g x) := by
          rw [hsub]
          simp only [Pi.sub_apply]
    _ = Complex.reCLM (f x) - Complex.reCLM (g x) := map_sub _ _ _
    _ = (Complex.reCLM.compLp f) x - (Complex.reCLM.compLp g) x := by
          rw [hff, hgg]
    _ = (Complex.reCLM.compLp f - Complex.reCLM.compLp g) x := hsubRe.symm

theorem GalerkinResidualTail.mFourierCoeff_complexFourierPartialSumLp_tail
    (M N : ℕ) (hMN : M ≤ N) (f : ComplexScalarTorusL2) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (complexFourierPartialSumLp N f - complexFourierPartialSumLp M f) k =
      if k ∈ GalerkinResidualTail.classicalResidualFrequencyBox N \
          GalerkinResidualTail.classicalResidualFrequencyBox M then
        UnitAddTorus.mFourierCoeff f k else 0 := by
  calc
    UnitAddTorus.mFourierCoeff
        (complexFourierPartialSumLp N f - complexFourierPartialSumLp M f) k =
      (UnitAddTorus.mFourierBasis.repr
        (complexFourierPartialSumLp N f - complexFourierPartialSumLp M f)) k :=
          (UnitAddTorus.mFourierBasis_repr _ k).symm
    _ = (UnitAddTorus.mFourierBasis.repr (complexFourierPartialSumLp N f)) k -
        (UnitAddTorus.mFourierBasis.repr (complexFourierPartialSumLp M f)) k := by
          simp only [map_sub, lp.coeFn_sub, Pi.sub_apply]
    _ = _ := by
          rw [mFourierBasis_repr_complexFourierPartialSumLp N f k,
            mFourierBasis_repr_complexFourierPartialSumLp M f k]
          by_cases hkN : k ∈ GalerkinResidualTail.classicalResidualFrequencyBox N
          · by_cases hkM : k ∈ GalerkinResidualTail.classicalResidualFrequencyBox M
            · simp [hkN, hkM]
            · simp [hkN, hkM]
          · have hkM : k ∉ GalerkinResidualTail.classicalResidualFrequencyBox M := by
              intro h
              exact hkN (GalerkinResidualTail.classicalResidualFrequencyBox_subset hMN h)
            simp [hkN, hkM]

/-- The `L²` tail of the complex Fourier cutoff is bounded by the high-frequency part of the
Dirichlet energy. -/
theorem complexFourierPartialSumLp_tail_norm_sq_le
    (M N : ℕ) (hMN : M ≤ N) (f : ComplexScalarTorusL2)
    (hE : AVenhance.Infra.Heat.HasFiniteFourierEnergy f) :
    ‖complexFourierPartialSumLp N f - complexFourierPartialSumLp M f‖ ^ 2 ≤
      (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
        AVenhance.Infra.Heat.fourierEnergy f := by
  let g := complexFourierPartialSumLp N f - complexFourierPartialSumLp M f
  let C : ℝ := (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hsumCoeff : Summable fun k : Fin 2 → ℤ =>
      ‖UnitAddTorus.mFourierCoeff g k‖ ^ 2 :=
    (UnitAddTorus.hasSum_sq_mFourierCoeff g).summable
  have hsumEnergy : Summable fun k : Fin 2 → ℤ =>
      C * AVenhance.Infra.Heat.fourierEnergyTerm f k := hE.mul_left C
  have hpoint (k : Fin 2 → ℤ) :
      ‖UnitAddTorus.mFourierCoeff g k‖ ^ 2 ≤
        C * AVenhance.Infra.Heat.fourierEnergyTerm f k := by
    rw [show UnitAddTorus.mFourierCoeff g k =
        UnitAddTorus.mFourierCoeff
          (complexFourierPartialSumLp N f - complexFourierPartialSumLp M f) k by
            rfl]
    rw [GalerkinResidualTail.mFourierCoeff_complexFourierPartialSumLp_tail M N hMN f k]
    by_cases hk : k ∈ GalerkinResidualTail.classicalResidualFrequencyBox N \
        GalerkinResidualTail.classicalResidualFrequencyBox M
    · have hnotM : k ∉ GalerkinResidualTail.classicalResidualFrequencyBox M :=
        (Finset.mem_sdiff.mp hk).2
      have hfreq := GalerkinResidualTail.frequencySq_ge_of_not_mem_box M k hnotM
      have hA : 0 < 4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2 := by positivity
      have hA_le : 4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2 ≤
          4 * Real.pi ^ 2 * AVenhance.Infra.Heat.frequencySq k :=
        mul_le_mul_of_nonneg_left hfreq (by positivity)
      have hratio : 1 ≤ (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
          (4 * Real.pi ^ 2 * AVenhance.Infra.Heat.frequencySq k) := by
        calc
          1 = (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
              (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2) := by
                field_simp [ne_of_gt hA]
          _ ≤ _ := mul_le_mul_of_nonneg_left hA_le (inv_nonneg.mpr hA.le)
      simp only [hk]
      change ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 ≤ _
      unfold AVenhance.Infra.Heat.fourierEnergyTerm C
      calc
        ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 =
            1 * ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 := by ring
        _ ≤ ((4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
              (4 * Real.pi ^ 2 * AVenhance.Infra.Heat.frequencySq k)) *
              ‖UnitAddTorus.mFourierCoeff f k‖ ^ 2 :=
                mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
        _ = _ := by ring
    · have hfreqNonneg : 0 ≤ AVenhance.Infra.Heat.frequencySq k := by
        unfold AVenhance.Infra.Heat.frequencySq
        exact Finset.sum_nonneg fun i hi => sq_nonneg (k i : ℝ)
      have htermNonneg : 0 ≤ AVenhance.Infra.Heat.fourierEnergyTerm f k := by
        unfold AVenhance.Infra.Heat.fourierEnergyTerm
        positivity
      have hC : 0 ≤ C := by positivity
      simp only [hk]
      simp only [↓reduceIte, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          ge_iff_le]
      exact mul_nonneg (by positivity) htermNonneg
  have hsum := Summable.tsum_le_tsum hpoint hsumCoeff hsumEnergy
  calc
    ‖complexFourierPartialSumLp N f - complexFourierPartialSumLp M f‖ ^ 2 =
        ∑' k : Fin 2 → ℤ, ‖UnitAddTorus.mFourierCoeff g k‖ ^ 2 :=
          AVenhance.Infra.Heat.norm_sq_eq_tsum_fourierCoeff g
    _ ≤ ∑' k : Fin 2 → ℤ,
          C * AVenhance.Infra.Heat.fourierEnergyTerm f k := hsum
    _ = C * AVenhance.Infra.Heat.fourierEnergy f := by
          rw [hE.tsum_mul_left C]
          rfl

/-- The nested real Galerkin projection tail is controlled by the Fourier `H¹` energy of its
complexification. -/
theorem realFourierProjectionCoefficients_tail_norm_sq_le
    (M N : ℕ) (hMN : M ≤ N) (v : ScalarTorusL2)
    (hE : AVenhance.Infra.Heat.HasFiniteFourierEnergy
      (Complex.ofRealCLM.compLp v)) :
    ‖realFourierProjectionCoefficients N v -
        realFourierCoefficientsLift hMN (realFourierProjectionCoefficients M v)‖ ^ 2 ≤
      (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
        AVenhance.Infra.Heat.fourierEnergy (Complex.ofRealCLM.compLp v) := by
  let fC : ComplexScalarTorusL2 := Complex.ofRealCLM.compLp v
  let tail := complexFourierPartialSumLp N fC - complexFourierPartialSumLp M fC
  let d := realFourierProjectionCoefficients N v -
    realFourierCoefficientsLift hMN (realFourierProjectionCoefficients M v)
  have hmap : realFourierScalarMap N d = Complex.reCLM.compLp tail := by
    calc
      realFourierScalarMap N d =
          realFourierScalarMap N (realFourierProjectionCoefficients N v) -
            realFourierScalarMap N
              (realFourierCoefficientsLift hMN (realFourierProjectionCoefficients M v)) := by
                simp [d, map_sub]
      _ = realFourierScalarMap N (realFourierProjectionCoefficients N v) -
            realFourierScalarMap M (realFourierProjectionCoefficients M v) := by
              rw [realFourierScalarMap_lift]
      _ = Complex.reCLM.compLp (complexFourierPartialSumLp N fC) -
            Complex.reCLM.compLp (complexFourierPartialSumLp M fC) := by
              rw [realFourierScalarMap_projection_eq_realPartFourierSum N v,
                realFourierScalarMap_projection_eq_realPartFourierSum M v]
      _ = Complex.reCLM.compLp tail := by
            simpa [tail] using
              (GalerkinResidualTail.realPart_compLp_sub (complexFourierPartialSumLp N fC)
                (complexFourierPartialSumLp M fC)).symm
  have hnorm : ‖d‖ = ‖Complex.reCLM.compLp tail‖ := by
    calc
      ‖d‖ = ‖realFourierScalarMap N d‖ := (realFourierScalarMap_norm N d).symm
      _ = ‖Complex.reCLM.compLp tail‖ := by rw [hmap]
  have hReOp : ‖Complex.reCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound Complex.reCLM (by norm_num)
    intro z
    change ‖z.re‖ ≤ 1 * ‖z‖
    simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm z
  have hReTail : ‖Complex.reCLM.compLp tail‖ ≤ ‖tail‖ := by
    calc
      ‖Complex.reCLM.compLp tail‖ ≤ ‖Complex.reCLM‖ * ‖tail‖ :=
        ContinuousLinearMap.norm_compLp_le Complex.reCLM tail
      _ ≤ 1 * ‖tail‖ := mul_le_mul_of_nonneg_right hReOp (norm_nonneg _)
      _ = ‖tail‖ := by ring
  have hcomplex := complexFourierPartialSumLp_tail_norm_sq_le M N hMN fC hE
  change ‖d‖ ^ 2 ≤ _
  calc
    ‖d‖ ^ 2 = ‖Complex.reCLM.compLp tail‖ ^ 2 := by rw [hnorm]
    _ ≤ ‖tail‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hReTail
    _ ≤ (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
        AVenhance.Infra.Heat.fourierEnergy (Complex.ofRealCLM.compLp v) := by
          simpa [tail, fC] using hcomplex

end AVenhance.Infra.Classical

end
