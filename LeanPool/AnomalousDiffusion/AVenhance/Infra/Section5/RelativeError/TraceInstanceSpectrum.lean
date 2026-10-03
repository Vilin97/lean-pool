/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.AnalyticDerivativeTail
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.TraceProjectionTrace
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge

/-! # derivative control for the finite low-frequency trace mode

The finite Fourier cutoff has no derivative loss beyond its physical
frequency radius.  Parseval compares every nonempty ordered derivative with
the full gradient energy of the same cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Ergodic
open AVenhance.Infra.Torus

/-- Ordered complex coordinate derivatives used in the trace spectrum estimate. -/
def TraceInstanceSpectrum.complexWordDerivative : List (Fin 2) → (Vec 2 → ℂ) → Vec 2 → ℂ
  | [], f => f
  | i :: w, f => coordDeriv i (TraceInstanceSpectrum.complexWordDerivative w f)

theorem TraceInstanceSpectrum.complexWordDerivative_contDiff (w : List (Fin 2))
    {f : Vec 2 → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (TraceInstanceSpectrum.complexWordDerivative w f) := by
  induction w with
  | nil => simpa [TraceInstanceSpectrum.complexWordDerivative] using hf
  | cons i w ih =>
      change ContDiff ℝ ∞ (fun x =>
        fderiv ℝ (TraceInstanceSpectrum.complexWordDerivative w f) x (basisVec i))
      exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem TraceInstanceSpectrum.complexWordDerivative_periodic (w : List (Fin 2))
    {f : Vec 2 → ℂ} (hf : IsZdPeriodic f) :
    IsZdPeriodic (TraceInstanceSpectrum.complexWordDerivative w f) := by
  induction w with
  | nil => simpa [TraceInstanceSpectrum.complexWordDerivative] using hf
  | cons i w ih =>
      intro k x
      have hfun : (fun y : Vec 2 => TraceInstanceSpectrum.complexWordDerivative w f
          (y + intVector k)) = TraceInstanceSpectrum.complexWordDerivative w f := by
        funext y
        exact ih k y
      have hder : fderiv ℝ (TraceInstanceSpectrum.complexWordDerivative w f)
          (x + intVector k) = fderiv ℝ (TraceInstanceSpectrum.complexWordDerivative w f) x := by
        calc
          _ = fderiv ℝ (fun y => TraceInstanceSpectrum.complexWordDerivative w f
              (y + intVector k)) x := by rw [fderiv_comp_add_right]
          _ = _ := by rw [hfun]
      change coordDeriv i (TraceInstanceSpectrum.complexWordDerivative w f) (x + intVector k) = _
      exact congrArg (fun L : Vec 2 →L[ℝ] ℂ => L (basisVec i)) hder

theorem TraceInstanceSpectrum.orderedRealDerivative_contDiff (w : List (Fin 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (orderedRealDerivative w f) := by
  induction w with
  | nil => simpa [orderedRealDerivative] using hf
  | cons i w ih =>
      simpa [orderedRealDerivative] using
        (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem TraceInstanceSpectrum.orderedRealDerivative_periodic (w : List (Fin 2))
    {f : Vec 2 → ℝ} (hf : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (orderedRealDerivative w f) := by
  induction w with
  | nil => simpa [orderedRealDerivative] using hf
  | cons i w ih =>
      intro k x
      have hfun : (fun y : Vec 2 => orderedRealDerivative w f
          (y + latticeShift k)) = orderedRealDerivative w f := by
        funext y
        exact ih k y
      have hder : fderiv ℝ (orderedRealDerivative w f)
          (x + latticeShift k) = fderiv ℝ (orderedRealDerivative w f) x := by
        calc
          _ = fderiv ℝ (fun y => orderedRealDerivative w f
              (y + latticeShift k)) x := by rw [fderiv_comp_add_right]
          _ = _ := by rw [hfun]
      exact congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i)) hder

theorem TraceInstanceSpectrum.complexWordDerivative_realCast (w : List (Fin 2))
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ ∞ f) :
    TraceInstanceSpectrum.complexWordDerivative w (realToComplex f) =
      realToComplex (orderedRealDerivative w f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      have htail : ContDiff ℝ ∞ (orderedRealDerivative w f) :=
        TraceInstanceSpectrum.orderedRealDerivative_contDiff w hf
      rw [TraceInstanceSpectrum.complexWordDerivative, ih]
      funext x
      exact coordDeriv_realToComplex
        (htail.of_le (by norm_num)) i x

/-- Product Fourier multiplier associated with a spatial derivative word. -/
def TraceInstanceSpectrum.wordFourierMultiplier : List (Fin 2) → (Fin 2 → ℤ) → ℂ
  | [], _ => 1
  | i :: w, k => (2 * Real.pi * Complex.I * (k i : ℂ)) *
      TraceInstanceSpectrum.wordFourierMultiplier w k

theorem TraceInstanceSpectrum.complexWordDerivative_fourierCoeff (w : List (Fin 2))
    {f : Vec 2 → ℂ} (hf : ContDiff ℝ ∞ f) (hper : IsZdPeriodic f)
    (k : Fin 2 → ℤ) :
    smoothFourierCoeff (TraceInstanceSpectrum.complexWordDerivative w f) k =
      TraceInstanceSpectrum.wordFourierMultiplier w k * smoothFourierCoeff f k := by
  induction w with
  | nil => simp [TraceInstanceSpectrum.complexWordDerivative,
      TraceInstanceSpectrum.wordFourierMultiplier]
  | cons i w ih =>
      have htailDiff := TraceInstanceSpectrum.complexWordDerivative_contDiff w hf
      have htailPer := TraceInstanceSpectrum.complexWordDerivative_periodic w hper
      rw [TraceInstanceSpectrum.complexWordDerivative, smoothFourierCoeff_coordDeriv i
        (htailDiff.of_le (by norm_num)) htailPer, ih]
      simp [TraceInstanceSpectrum.wordFourierMultiplier, mul_assoc]

theorem TraceInstanceSpectrum.wordFourierMultiplier_norm_le (w : List (Fin 2))
    {k : Fin 2 → ℤ} {M K : ℝ} (hK : 0 ≤ K)
    (hfreq : ‖k‖ ≤ M) (hphys : 2 * Real.pi * M ≤ K) :
    ‖TraceInstanceSpectrum.wordFourierMultiplier w k‖ ≤ K ^ w.length := by
  induction w with
  | nil => simp [TraceInstanceSpectrum.wordFourierMultiplier]
  | cons i w ih =>
      have hcoord : |(k i : ℝ)| ≤ M := by
        calc
          |(k i : ℝ)| = ‖(k i : ℝ)‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖k‖ := norm_le_pi_norm k i
          _ ≤ M := hfreq
      have hmult : ‖2 * Real.pi * Complex.I * (k i : ℂ)‖ ≤ K := by
        have habs : |(k i : ℝ)| ≤ M := hcoord
        have hnorm : ‖2 * Real.pi * Complex.I * (k i : ℂ)‖ =
            2 * Real.pi * |(k i : ℝ)| := by
          rw [norm_mul, norm_mul]
          simp [Complex.norm_I, Complex.norm_intCast]
        rw [hnorm]
        calc
          2 * Real.pi * |(k i : ℝ)| ≤ 2 * Real.pi * M :=
            mul_le_mul_of_nonneg_left habs (by positivity)
          _ ≤ K := hphys
      calc
        ‖TraceInstanceSpectrum.wordFourierMultiplier (i :: w) k‖ ≤
            K * ‖TraceInstanceSpectrum.wordFourierMultiplier w k‖ := by
              rw [TraceInstanceSpectrum.wordFourierMultiplier, norm_mul]
              exact mul_le_mul_of_nonneg_right hmult (norm_nonneg _)
        _ ≤ K * K ^ w.length := mul_le_mul_of_nonneg_left ih hK
        _ = K ^ (i :: w).length := by simp [pow_succ]; ring

theorem TraceInstanceSpectrum.lowProjection_complexFourierCoeff
    {g : Vec 2 → ℝ} (M : ℕ) (k : Fin 2 → ℤ) :
    smoothFourierCoeff (realToComplex (lowProjection g M)) k =
      if k ∈ frequencyBall M then smoothFourierCoeff (realToComplex g) k else 0 := by
  exact smoothFourierCoeff_euclideanCutoff M
    (fun q => smoothFourierCoeff (realToComplex g) q)
    (smoothFourierCoeff_real_neg (f := g)) k

/-- Every positive-order real coordinate derivative of the cutoff is bounded
in cell `L²` by its full gradient energy and the physical cutoff radius. -/
theorem lowProjection_orderedDerivative_l2_le
    {g : Vec 2 → ℝ}
    (w : List (Fin 2)) (hw : 1 ≤ w.length) (M : ℕ) :
    Real.sqrt (∫ x in unitCell 2,
      (orderedRealDerivative w (lowProjection g M) x) ^ 2) ≤
      (2 * Real.pi * Real.sqrt 2 * (M : ℝ)) ^ (w.length - 1) *
        Real.sqrt (gradNormSq (spaceGrad (lowProjection g M))) := by
  let f : Vec 2 → ℝ := lowProjection g M
  let fC : Vec 2 → ℂ := realToComplex f
  let qC : Vec 2 → ℂ := TraceInstanceSpectrum.complexWordDerivative w fC
  let K : ℝ := 2 * Real.pi * Real.sqrt 2 * (M : ℝ)
  have hf : ContDiff ℝ ∞ f := by
    simpa [f] using (lowProjection_contDiff (f := g) M).of_le le_top
  have hfperZ : IsZPeriodic f := by
    simpa [f] using lowProjection_periodic (f := g) M
  have hfper : AVenhance.IsZ2Periodic f :=
    (isZPeriodic_iff_isZ2Periodic f).1 hfperZ
  have hfCdiff : ContDiff ℝ ∞ fC := Complex.ofRealCLM.contDiff.comp hf
  have hfCper : IsZdPeriodic fC := by
    intro k x
    exact congrArg Complex.ofReal ((isZdPeriodic_iff_frozen f).2 hfper k x)
  have hqCdiff : ContDiff ℝ ∞ qC := by
    dsimp [qC]
    exact TraceInstanceSpectrum.complexWordDerivative_contDiff w hfCdiff
  have hqCper : IsZdPeriodic qC := by
    dsimp [qC]
    exact TraceInstanceSpectrum.complexWordDerivative_periodic w hfCper
  have hqParseval := hasSum_sq_smoothFourierCoeff hqCdiff.continuous
  have hfGradParseval := hasSum_sq_realToComplexGradientFourierCoeff
    (f := f) (hf.of_le (by norm_num))
  have hcoeff (k : Fin 2 → ℤ) :
      smoothFourierCoeff qC k =
        TraceInstanceSpectrum.wordFourierMultiplier w k * smoothFourierCoeff fC k := by
    exact TraceInstanceSpectrum.complexWordDerivative_fourierCoeff w hfCdiff hfCper k
  have hgradCoeff (i : Fin 2) (k : Fin 2 → ℤ) :
      smoothFourierCoeff (coordDeriv i fC) k =
        (2 * Real.pi * Complex.I * (k i : ℂ)) * smoothFourierCoeff fC k :=
    smoothFourierCoeff_coordDeriv i (hfCdiff.of_le (by norm_num)) hfCper k
  have hKnonneg : 0 ≤ K := by dsimp [K]; positivity
  have hmode (k : Fin 2 → ℤ) :
      ‖smoothFourierCoeff qC k‖ ^ 2 ≤
        K ^ (2 * (w.length - 1)) *
          (∑ i : Fin 2, ‖smoothFourierCoeff (coordDeriv i fC) k‖ ^ 2) := by
    have hword := hcoeff k
    rw [hword]
    by_cases hk : k ∈ frequencyBall M
    · have hfreq := mem_frequencyBall.mp hk
      have hKpos : 0 ≤ K := hKnonneg
      have hphys : 2 * Real.pi * (M : ℝ) ≤ K := by
        dsimp [K]
        have hsqrt : 1 ≤ Real.sqrt 2 := by
          nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num),
            Real.sqrt_nonneg (2 : ℝ)]
        nlinarith [Real.pi_pos.le, show 0 ≤ (M : ℝ) by positivity]
      have hwdecomp : ∃ i : Fin 2, ∃ w' : List (Fin 2), w = i :: w' := by
        cases w with
        | nil => simp at hw
        | cons i w' => exact ⟨i, w', rfl⟩
      obtain ⟨i, w', rfl⟩ := hwdecomp
      let μ : ℂ := 2 * Real.pi * Complex.I * (k i : ℂ)
      let tail : ℂ := TraceInstanceSpectrum.wordFourierMultiplier w' k
      let a : ℂ := smoothFourierCoeff fC k
      have htailNorm : ‖tail‖ ≤ K ^ w'.length := by
        simpa [tail] using TraceInstanceSpectrum.wordFourierMultiplier_norm_le w'
          hKpos hfreq hphys
      have hfirst : ‖μ * a‖ ^ 2 ≤
          ∑ j : Fin 2, ‖smoothFourierCoeff (coordDeriv j fC) k‖ ^ 2 := by
        have hμ : μ * a = smoothFourierCoeff (coordDeriv i fC) k := by
          simpa [μ, a] using (hgradCoeff i k).symm
        rw [hμ]
        exact Finset.single_le_sum (fun j _ => sq_nonneg
          ‖smoothFourierCoeff (coordDeriv j fC) k‖) (Finset.mem_univ i)
      have hmultbound :
          ‖TraceInstanceSpectrum.wordFourierMultiplier (i :: w') k * a‖ ^ 2 ≤
            K ^ (2 * w'.length) * ‖μ * a‖ ^ 2 := by
        have hfactor : TraceInstanceSpectrum.wordFourierMultiplier (i :: w') k * a =
            (μ * a) * tail := by
          calc
            TraceInstanceSpectrum.wordFourierMultiplier (i :: w') k * a =
                μ * tail * a := by simp [TraceInstanceSpectrum.wordFourierMultiplier, μ, tail]
            _ = (μ * a) * tail := by ring
        rw [hfactor, norm_mul, mul_pow]
        have htailSq : ‖tail‖ ^ 2 ≤ K ^ (2 * w'.length) := by
          calc
            ‖tail‖ ^ 2 ≤ (K ^ w'.length) ^ 2 := by
              exact pow_le_pow_left₀ (norm_nonneg _) htailNorm 2
            _ = K ^ (w'.length * 2) := by rw [← pow_mul]
            _ = K ^ (2 * w'.length) := by congr 1; omega
        calc
          ‖μ * a‖ ^ 2 * ‖tail‖ ^ 2 ≤
              ‖μ * a‖ ^ 2 * K ^ (2 * w'.length) :=
            mul_le_mul_of_nonneg_left htailSq (sq_nonneg _)
          _ = K ^ (2 * w'.length) * ‖μ * a‖ ^ 2 := by ring
      have hpowlen : 2 * w'.length = 2 * ((i :: w').length - 1) := by simp
      rw [hpowlen] at hmultbound
      exact hmultbound.trans (mul_le_mul_of_nonneg_left hfirst (by positivity))
    · have hzero : smoothFourierCoeff fC k = 0 := by
        have hh := TraceInstanceSpectrum.lowProjection_complexFourierCoeff (g := g) M k
        simpa [f, fC, hk] using hh
      rw [hzero]
      simp only [mul_zero, norm_zero]
      norm_num
      exact mul_nonneg (pow_nonneg hKnonneg _)
        (add_nonneg (sq_nonneg _) (sq_nonneg _))
  let Kpow : ℝ := K ^ (2 * (w.length - 1))
  have hscaled := hfGradParseval.mul_left Kpow
  have hsum := Summable.tsum_le_tsum hmode hqParseval.summable
    hscaled.summable
  have henergy :
      (∫ x in unitCell 2, ‖qC x‖ ^ 2) ≤
        K ^ (2 * (w.length - 1)) * gradNormSq (spaceGrad f) := by
    calc
      (∫ x in unitCell 2, ‖qC x‖ ^ 2) = ∑' k, ‖smoothFourierCoeff qC k‖ ^ 2 :=
        hqParseval.tsum_eq.symm
      _ ≤ ∑' k, Kpow *
          (∑ i : Fin 2, ‖smoothFourierCoeff (coordDeriv i fC) k‖ ^ 2) := hsum
      _ = Kpow * gradNormSq (spaceGrad f) := by
        rw [hscaled.tsum_eq]
  have hqReal : ∀ x, ‖qC x‖ ^ 2 =
      (orderedRealDerivative w f x) ^ 2 := by
    intro x
    have hcast := congrFun (TraceInstanceSpectrum.complexWordDerivative_realCast w hf) x
    calc
      ‖qC x‖ ^ 2 = ‖realToComplex (orderedRealDerivative w f) x‖ ^ 2 := by
        change ‖TraceInstanceSpectrum.complexWordDerivative w (realToComplex f) x‖ ^ 2 =
          ‖realToComplex (orderedRealDerivative w f) x‖ ^ 2
        exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hcast
      _ = (orderedRealDerivative w f x) ^ 2 := by simp [realToComplex]
  have henergyReal :
      (∫ x in unitCell 2,
        (orderedRealDerivative w f x) ^ 2) ≤
        K ^ (2 * (w.length - 1)) * gradNormSq (spaceGrad f) := by
    calc
      _ = ∫ x in unitCell 2, ‖qC x‖ ^ 2 := by
        apply setIntegral_congr_fun (measurableSet_unitCell 2)
        intro x hx
        exact (hqReal x).symm
      _ ≤ _ := henergy
  have hgradnonneg : 0 ≤ gradNormSq (spaceGrad f) := by
    unfold gradNormSq
    exact integral_nonneg (fun x => vecNormSq_nonneg _)
  have hKnonneg : 0 ≤ K := by dsimp [K]; positivity
  have hpower : 0 ≤ K ^ (2 * (w.length - 1)) := pow_nonneg hKnonneg _
  have hresult := Real.sqrt_le_sqrt henergyReal
  have hsplit : Real.sqrt
      (K ^ (2 * (w.length - 1)) * gradNormSq (spaceGrad f)) =
      K ^ (w.length - 1) * Real.sqrt (gradNormSq (spaceGrad f)) := by
    have hpowid : K ^ (2 * (w.length - 1)) =
        (K ^ (w.length - 1)) ^ 2 := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hpowid, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (pow_nonneg hKnonneg _)]
  rw [hsplit] at hresult
  simpa [f, K] using hresult

end AVenhance.Infra.Section5.RelativeError

end
