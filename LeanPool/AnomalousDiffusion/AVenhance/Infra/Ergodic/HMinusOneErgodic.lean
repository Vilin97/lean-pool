/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.HMinusOneErgodicCore

/-! # The spectral homogeneous H⁻¹ ergodic estimate -/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open scoped ContDiff
open MeasureTheory
open Homogenization
open AVenhance.Infra.Torus

noncomputable section

variable {d : ℕ}

/-- The dimension-dependent Fourier weight appearing in the source estimate. -/
@[irreducible] noncomputable def ergodicFourierWeight (d : ℕ) : ℝ :=
  ∑' k : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖)

theorem ergodicFourierWeight_eq_tsum (d : ℕ) :
    ergodicFourierWeight d =
      ∑' k : Fin d → ℤ, Real.exp (-(1 / 1024 : ℝ) * ‖k‖) := by
  delta ergodicFourierWeight
  rfl

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraErgodicHMinusOneErgodicMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraErgodicHMinusOneErgodicMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraErgodicHMinusOneErgodicIsProbabilityMeasure3 : IsProbabilityMeasure (volume
    : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
attribute [local instance] Measure.Subtype.measureSpace

theorem HMinusOneErgodic.torusRepresentative_eq_cellRepresentative
    (x : UnitAddTorus (Fin d)) :
    Torus.unitTorusRepresentative d x = unitCellRepresentative x := by
  funext i
  rfl

theorem HMinusOneErgodic.integral_torusFunction_eq_unitCell {v : Vec d → ℂ} :
    ∫ x : UnitAddTorus (Fin d), torusFunction v x =
      ∫ x in Torus.unitCell d, v x := by
  calc
    _ = ∫ x : UnitAddTorus (Fin d), Torus.periodicToTorus v x := by
      apply integral_congr_ae
      filter_upwards with x
      simp [torusFunction, Torus.periodicToTorus,
        HMinusOneErgodic.torusRepresentative_eq_cellRepresentative]
    _ = _ := Torus.integral_periodicToTorus_eq_unitCell v

theorem HMinusOneErgodic.cellAverage_absSq_eq_sq {u : Vec d → ℝ} :
    cellAverage (fun x => |u x| ^ 2) = cellAverage (fun x => u x ^ 2) := by
  rw [cellAverage_eq_torusUnitCellIntegral, cellAverage_eq_torusUnitCellIntegral]
  apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
  intro x hx
  simp [sq_abs]

theorem HMinusOneErgodic.l2norm_cell_eq_average_absSq {u : Vec d → ℝ} :
    (∫ x in Torus.unitCell d, u x ^ 2) ^ (1 / 2 : ℝ) =
      (cellAverage (fun x => |u x| ^ 2)) ^ (1 / 2 : ℝ) := by
  rw [← cellAverage_eq_torusUnitCellIntegral, HMinusOneErgodic.cellAverage_absSq_eq_sq]

theorem HMinusOneErgodic.cellAverage_mul_split {f p q g : Vec d → ℝ}
    (hpg : LocallyIntegrable (fun x => p x * g x) (volume : Measure (Vec d)))
    (hqg : LocallyIntegrable (fun x => q x * g x) (volume : Measure (Vec d)))
    (hpoint : ∀ x, f x * g x = p x * g x + q x * g x) :
    cellAverage (fun x => f x * g x) =
      cellAverage (fun x => p x * g x) + cellAverage (fun x => q x * g x) := by
  have hfun : (fun x => f x * g x) = fun x => p x * g x + q x * g x := by
    funext x
    exact hpoint x
  rw [hfun, cellAverage_add_of_locallyIntegrable hpg hqg]

theorem HMinusOneErgodic.complex_norm_ofReal_square {x : ℝ} :
    ‖(x : ℂ)‖ ^ 2 = x ^ 2 := by
  simp [Complex.norm_real, sq_abs]

theorem HMinusOneErgodic.mFourierCoeff_zero_eq_integral_local
    (H : UnitAddTorus (Fin d) → ℂ) :
    UnitAddTorus.mFourierCoeff H (0 : Fin d → ℤ) = ∫ x, H x := by
  simp [UnitAddTorus.mFourierCoeff, UnitAddTorus.mFourier_zero]

theorem HMinusOneErgodic.lowProjection_fastProduct_mean_gap
    {d N M : ℕ} (hN : 0 < N)
    (hgapPos : 0 < (N : ℝ) - (M : ℝ))
    {f : Vec d → ℝ}
    {g : Vec d → ℝ}
    (hg : LocallyIntegrable g (volume : Measure (Vec d)))
    (hg2 : LocallyIntegrable (fun x => |g x| ^ 2) (volume : Measure (Vec d)))
    (hfast : IsFastPeriodic N g) (hgMean : cellAverage g = 0) :
    cellAverage (fun x => lowProjection f M x * g x) = 0 ∧
      ∀ q : Fin d → ℤ, ‖q‖ < (N : ℝ) - (M : ℝ) →
        UnitAddTorus.mFourierCoeff
          (torusFunction (fun x => (lowProjection f M x * g x : ℂ))) q = 0 := by
  classical
  let a : (Fin d → ℤ) → ℂ := fun k =>
    Torus.smoothFourierCoeff (fun x => (f x : ℂ)) k
  let P : C(UnitAddTorus (Fin d), ℂ) := fourierCutoff M a
  let G : UnitAddTorus (Fin d) → ℂ := fun x =>
    ((torusFunction (α := ℝ) g x : ℝ) : ℂ)
  let H : UnitAddTorus (Fin d) → ℂ := fun x => P x * G x
  have hGmem : MemLp G 2 (volume : Measure (UnitAddTorus (Fin d))) := by
    have hcell := cellMemLp_two_of_localSquare hg.aestronglyMeasurable hg2
    have hcomplexCell : MemLp (fun x => (g x : ℂ))
        (ENNReal.ofReal (2 : ℝ))
        ((volume : Measure (Vec d)).restrict (Torus.unitCell d)) := by
      simpa using hcell.2
    have h := memLp_torusFunction_two_of_cellL2 hcomplexCell
    have hEq : G = torusFunction (fun x => (g x : ℂ)) := by
      funext x
      rfl
    rw [hEq]
    simpa using h
  have hGint : Integrable G (volume : Measure (UnitAddTorus (Fin d))) :=
    hGmem.integrable (by norm_num)
  have hGmean : ∫ x : UnitAddTorus (Fin d), G x = 0 := by
    have hrep := HMinusOneErgodic.torusRepresentative_eq_cellRepresentative (d := d)
    calc
      _ = ∫ x : UnitAddTorus (Fin d),
          Torus.periodicToTorus (fun x => (g x : ℂ)) x := by
            apply integral_congr_ae
            filter_upwards with x
            simp [G, torusFunction, Torus.periodicToTorus, hrep]
      _ = ∫ x in Torus.unitCell d, (g x : ℂ) :=
        Torus.integral_periodicToTorus_eq_unitCell _
      _ = (cellAverage g : ℂ) := by
        rw [integral_complex_ofReal, ← cellAverage_eq_torusUnitCellIntegral]
      _ = 0 := by rw [hgMean]; norm_num
  have hGfast : ∀ i x, G (x + fastTorusShift N i) = G x := by
    intro i x
    rw [show G = fun y =>
      ((torusFunction (α := ℝ) g y : ℝ) : ℂ) by rfl]
    exact congrArg Complex.ofReal (torusFunction_add_fastTorusShift_eq hN hfast i x)
  have hPsum : ∀ x, P x = ∑ k ∈ frequencyBall M,
      a k * UnitAddTorus.mFourier k x := by
    intro x
    rfl
  have hPsupport : ∀ (k : Fin d → ℤ), k ∈ frequencyBall M →
      ‖k‖ ≤ (M : ℝ) := by
    intro k hk
    exact mem_frequencyBall.mp hk
  have hlowTransfer :
      torusFunction (fun x => (lowProjection f M x : ℂ)) = P := by
    funext x
    have hrep := HMinusOneErgodic.torusRepresentative_eq_cellRepresentative (d := d) x
    calc
      _ = Torus.periodicToTorus
          (fun y => (euclideanFourierCutoff M a y : ℂ)) x := by
            simp only [torusFunction, lowProjection]
            change (euclideanFourierCutoff M a (unitCellRepresentative x) : ℂ) =
              (euclideanFourierCutoff M a (Torus.unitTorusRepresentative d x) : ℂ)
            rw [hrep]
      _ = (realFourierCutoff M a x : ℂ) :=
            periodicToTorus_euclideanFourierCutoff M a x
      _ = P x := by
        change (realFourierCutoff M a x : ℂ) = fourierCutoff M a x
        exact congrFun (realFourierCutoff_complexification M a
          (smoothFourierCoeff_real_neg (f := f))) x
  have hHrep : H = torusFunction
      (fun x => (lowProjection f M x * g x : ℂ)) := by
    funext x
    change P x * G x = _
    rw [(congrFun hlowTransfer x).symm]
    simp [G, torusFunction]
  have hgapH : ∀ q : Fin d → ℤ, ‖q‖ < (N : ℝ) - (M : ℝ) →
      UnitAddTorus.mFourierCoeff H q = 0 := by
    intro q hq
    exact mFourierCoeff_mul_eq_zero_of_finiteSupport_fast
      hN (frequencyBall M) a P G hPsum (M : ℝ) hPsupport hGint hGmean hGfast q hq
  have hlowMean : cellAverage (fun x => lowProjection f M x * g x) = 0 := by
    have hHmean : ∫ x : UnitAddTorus (Fin d), H x = 0 := by
      rw [← HMinusOneErgodic.mFourierCoeff_zero_eq_integral_local H]
      exact hgapH 0 (by simpa using hgapPos)
    have hmeanEq : ∫ x : UnitAddTorus (Fin d), H x =
        (cellAverage (fun x => lowProjection f M x * g x) : ℂ) := by
      rw [hHrep]
      calc
        _ = ∫ x in Torus.unitCell d,
            (lowProjection f M x * g x : ℂ) := HMinusOneErgodic.integral_torusFunction_eq_unitCell
        _ = (cellAverage (fun x => lowProjection f M x * g x) : ℂ) := by
              calc
                _ = ∫ x in Torus.unitCell d,
                    ((lowProjection f M x * g x : ℝ) : ℂ) := by
                      apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
                      intro x hx
                      simp
                _ = _ := by
                      rw [integral_complex_ofReal,
                        ← cellAverage_eq_torusUnitCellIntegral]
    have hmeanC : (cellAverage (fun x => lowProjection f M x * g x) : ℂ) = 0 :=
      hmeanEq.symm.trans hHmean
    exact Complex.ofReal_injective hmeanC
  have hgapLow : ∀ q : Fin d → ℤ, ‖q‖ < (N : ℝ) - (M : ℝ) →
      UnitAddTorus.mFourierCoeff
        (torusFunction (fun x => (lowProjection f M x * g x : ℂ))) q = 0 := by
    intro q hq
    have hrep : H = torusFunction
        (fun x => (lowProjection f M x : ℂ) * (g x : ℂ)) := by
      exact hHrep
    rw [← hrep]
    exact hgapH q hq
  exact ⟨hlowMean, hgapLow⟩

theorem HMinusOneErgodic.fastProduct_split_l2_bound
    {d N : ℕ} (hd : 0 < d) (hN : 0 < N)
    {f : Vec d → ℝ} (hf : ContDiff ℝ ∞ f) (hper : IsZPeriodic f)
    (Cf r : ℝ) (hCf : 0 ≤ Cf) (hr : 0 < r)
    (hderiv : HasCoordinateAnalyticL2Bounds (fun x => (f x : ℂ)) Cf r)
    {g : Vec d → ℝ}
    (hg2 : LocallyIntegrable (fun x => |g x| ^ 2) (volume : Measure (Vec d)))
    (hfast : IsFastPeriodic N g) (hNr : 2 ≤ r * (N : ℝ)) :
    (∫ x in Torus.unitCell d,
      (lowProjection f (N / 2) x * g x) ^ 2) ^ (1 / 2 : ℝ) ≤
        ((cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ) +
          32 * (ergodicFourierWeight d) ^ (1 / 2 : ℝ) * Cf *
            Real.exp (-r * (N : ℝ) / 4096)) *
          (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) ∧
    (∫ x in Torus.unitCell d,
      (highRemainder f (N / 2) x * g x) ^ 2) ^ (1 / 2 : ℝ) ≤
        (1024 * ((d : ℝ) + 1) * Cf +
          32 * (ergodicFourierWeight d) ^ (1 / 2 : ℝ) * Cf) *
          Real.exp (-r * (N : ℝ) / 4096) *
          (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ) := by
  classical
  let M : ℕ := N / 2
  let K : ℝ := ergodicFourierWeight d
  let Fnorm : ℝ := (cellAverage (fun x => |f x| ^ 2)) ^ (1 / 2 : ℝ)
  let Gnorm : ℝ := (cellAverage (fun x => |g x| ^ 2)) ^ (1 / 2 : ℝ)
  have hK : 0 ≤ K := by
    dsimp [K]
    rw [ergodicFourierWeight_eq_tsum]
    exact tsum_nonneg fun _ => Real.exp_nonneg _
  have hFnonneg : 0 ≤ Fnorm := by
    dsimp [Fnorm]
    rw [cellAverage_eq_torusUnitCellIntegral]
    exact Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  have hGnonneg : 0 ≤ Gnorm := by
    dsimp [Gnorm]
    rw [cellAverage_eq_torusUnitCellIntegral]
    exact Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _
  have hMlower : (N : ℝ) / 2 ≤ (M : ℝ) + 1 := by
    have hnat : N ≤ 2 * (N / 2) + 1 := by omega
    have hnat' : (N : ℝ) ≤ 2 * ((N / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
    dsimp [M]
    nlinarith
  have hscale : 1 ≤ r * ((M : ℝ) + 1) := by
    have hprod : r * ((N : ℝ) / 2) ≤ r * ((M : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hMlower hr.le
    nlinarith [hNr]
  have hsplitAnalytic := lowHighCoordinateAnalyticL2Bounds
    hd hf hper Cf r hderiv M
  rcases hsplitAnalytic with ⟨hLowDeriv, hHighDeriv⟩
  have htail := fourierTailL2_le_of_coordinateAnalyticL2Bounds
    hd (Complex.ofRealCLM.contDiff.comp (highRemainder_contDiff hf M))
    (by
      intro k x
      exact congrArg Complex.ofReal (highRemainder_periodic hper M x k))
    Cf r hCf hr hHighDeriv M hscale
    (Complex.ofRealCLM.contDiff.comp (highRemainder_contDiff hf M))
    (by
      intro k
      have hcoeff := smoothFourierCoeff_euclideanCutoff M
        (fun q => Torus.smoothFourierCoeff (fun x => (f x : ℂ)) q)
        (smoothFourierCoeff_real_neg (f := f)) k
      change Torus.smoothFourierCoeff
        (fun x => (lowProjection f M x : ℂ)) k = _ at hcoeff
      have hsub := smoothFourierCoeff_sub
        (f := fun x => (f x : ℂ))
        (g := fun x => (lowProjection f M x : ℂ))
        (Complex.continuous_ofReal.comp hf.continuous)
        ((Complex.ofRealCLM.contDiff.comp (lowProjection_contDiff M)).continuous) k
      have hcast : (fun x => (highRemainder f M x : ℂ)) =
          (fun x => (f x : ℂ) - (lowProjection f M x : ℂ)) := by
        funext x
        simp [highRemainder]
      change Torus.smoothFourierCoeff
        (fun x => (highRemainder f M x : ℂ)) k =
          (if ‖k‖ ≤ (M : ℝ) then 0 else
            Torus.smoothFourierCoeff (fun x => (highRemainder f M x : ℂ)) k)
      rw [hcast, hsub, hcoeff]
      by_cases hk : ‖k‖ ≤ (M : ℝ)
      · simp [hk, mem_frequencyBall]
      · simp [hk, mem_frequencyBall])
  have hMnorm :
      (∫ x in Torus.unitCell d, (lowProjection f M x) ^ 2) ^
        (1 / 2 : ℝ) ≤ Fnorm := by
    calc
      _ ≤ (∫ x in Torus.unitCell d, f x ^ 2) ^ (1 / 2 : ℝ) :=
        lowProjectionL2_le hf M
      _ = Fnorm := by
        simpa [Fnorm] using (HMinusOneErgodic.l2norm_cell_eq_average_absSq (u := f))
  have hGNcell :
      (∫ x in Torus.unitCell d, g x ^ 2) ^ (1 / 2 : ℝ) = Gnorm := by
    simpa [Gnorm] using (HMinusOneErgodic.l2norm_cell_eq_average_absSq (u := g))
  have hLowProductBound := productL2_le_of_coordinateAnalyticL2Bounds
    hd ((lowProjection_contDiff M).of_le le_top) (lowProjection_periodic M) Cf r hCf hr
    hLowDeriv hg2 hN hfast hNr
  have hLowBound :
      (∫ x in Torus.unitCell d,
        (lowProjection f M x * g x) ^ 2) ^ (1 / 2 : ℝ) ≤
        (Fnorm + 32 * K ^ (1 / 2 : ℝ) * Cf *
          Real.exp (-r * (N : ℝ) / 4096)) * Gnorm := by
    have hbase := hLowProductBound
    rw [hGNcell] at hbase
    calc
      _ ≤ ((∫ x in Torus.unitCell d, lowProjection f M x ^ 2) ^
          (1 / 2 : ℝ) + 32 * K ^ (1 / 2 : ℝ) * Cf *
          Real.exp (-r * (N : ℝ) / 4096)) * Gnorm := by
            simpa [K, ergodicFourierWeight_eq_tsum] using hbase
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ hGnonneg
        nlinarith [hMnorm]
  have hHighProductBound := productL2_le_of_coordinateAnalyticL2Bounds
    hd (highRemainder_contDiff hf M) (highRemainder_periodic hper M) Cf r
    hCf hr hHighDeriv hg2 hN hfast hNr
  have htailN :
      (∫ x in Torus.unitCell d, (highRemainder f M x) ^ 2) ^
        (1 / 2 : ℝ) ≤
        1024 * ((d : ℝ) + 1) * Cf *
          Real.exp (-r * (N : ℝ) / 1024) := by
    have hMexp : r * (N : ℝ) / 1024 ≤
        r * ((M : ℝ) + 1) / 512 := by
      have hmul := mul_le_mul_of_nonneg_left hMlower hr.le
      nlinarith [hmul]
    have hexp : Real.exp (-r * ((M : ℝ) + 1) / 512) ≤
        Real.exp (-r * (N : ℝ) / 1024) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hMlower, hr.le]
    have htail' := htail
    change (∫ x in Torus.unitCell d,
      ‖(highRemainder f M x : ℂ)‖ ^ 2) ^ (1 / 2 : ℝ) ≤ _ at htail'
    have htailEq :
        (∫ x in Torus.unitCell d,
          ‖(highRemainder f M x : ℂ)‖ ^ 2) =
        ∫ x in Torus.unitCell d, (highRemainder f M x) ^ 2 := by
      apply setIntegral_congr_fun (Torus.measurableSet_unitCell d)
      intro x hx
      simp [Complex.norm_real, sq_abs]
    rw [htailEq] at htail'
    calc
      _ ≤ 1024 * ((d : ℝ) + 1) * Cf *
          Real.exp (-r * ((M : ℝ) + 1) / 512) := htail'
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  have hHighBound :
      (∫ x in Torus.unitCell d,
        (highRemainder f M x * g x) ^ 2) ^ (1 / 2 : ℝ) ≤
        (1024 * ((d : ℝ) + 1) * Cf + 32 * K ^ (1 / 2 : ℝ) * Cf) *
          Real.exp (-r * (N : ℝ) / 4096) * Gnorm := by
    have htail' :
        (∫ x in Torus.unitCell d, (highRemainder f M x) ^ 2) ^
          (1 / 2 : ℝ) ≤
          1024 * ((d : ℝ) + 1) * Cf *
            Real.exp (-r * (N : ℝ) / 4096) := by
      have hexp : Real.exp (-r * (N : ℝ) / 1024) ≤
          Real.exp (-r * (N : ℝ) / 4096) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hr, hN]
      calc
        _ ≤ 1024 * ((d : ℝ) + 1) * Cf *
            Real.exp (-r * (N : ℝ) / 1024) := htailN
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
    have hbase := hHighProductBound
    rw [hGNcell] at hbase
    calc
      _ ≤ ((∫ x in Torus.unitCell d,
          (highRemainder f M x) ^ 2) ^ (1 / 2 : ℝ) +
          32 * K ^ (1 / 2 : ℝ) * Cf *
            Real.exp (-r * (N : ℝ) / 4096)) * Gnorm := by
              simpa [K, ergodicFourierWeight_eq_tsum] using hbase
      _ ≤ (1024 * ((d : ℝ) + 1) * Cf *
            Real.exp (-r * (N : ℝ) / 4096) +
          32 * K ^ (1 / 2 : ℝ) * Cf *
            Real.exp (-r * (N : ℝ) / 4096)) * Gnorm :=
              mul_le_mul_of_nonneg_right (by nlinarith [htail']) hGnonneg
      _ = _ := by ring
  constructor
  · simpa [M, Fnorm, Gnorm, K] using hLowBound
  · simpa [M, Gnorm, K] using hHighBound

end

end AVenhance.Infra.Ergodic
