/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmSourcePairing
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Time-integral Cauchy bounds used for the regular and flux pairings in the
transported `H_m` estimate. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization

namespace AVenhance.Infra.Section4

/-- Scalar Cauchy--Schwarz on a finite time interval, with the exact interval
length factor retained. -/
theorem hm_interval_integral_abs_le_sqrt_length_mul_l2
    {a b Q : ℝ} {f : ℝ → ℝ} (hab : a ≤ b) (hQ : 0 ≤ Q)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b)))
    (hfSq : ∫ t in Set.Ioc a b, f t ^ 2 ≤ Q ^ 2) :
    |∫ t in a..b, f t| ≤ Real.sqrt (b - a) * Q := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hconst : MemLp (fun _ : ℝ => (1 : ℝ)) 2 μ := by
    simpa [μ] using (memLp_const (c := (1 : ℝ)))
  have hconst' : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hconst
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hf
  have hHolder := integral_mul_norm_le_Lp_mul_Lq
    ((Real.holderConjugate_iff (p := (2 : ℝ)) (q := (2 : ℝ))).mpr
      ⟨by norm_num, by norm_num⟩)
    hconst' hf'
  have hHolder' : (∫ t, |f t| ∂μ) ≤
      (∫ t, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ t, |f t| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa only [Real.norm_eq_abs, abs_one, one_mul] using hHolder
  have hHolderSqrt : (∫ t, |f t| ∂μ) ≤
      Real.sqrt (∫ t, (1 : ℝ) ^ (2 : ℝ) ∂μ) *
        Real.sqrt (∫ t, |f t| ^ (2 : ℝ) ∂μ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact hHolder'
  have hmass : (∫ t, (1 : ℝ) ^ (2 : ℝ) ∂μ) = b - a := by
    simp [μ, hab]
  have hfsqAbs : ∫ t in Set.Ioc a b, |f t| ^ (2 : ℝ) ≤ Q ^ 2 := by
    have hintegrand : ∀ t : ℝ, |f t| ^ (2 : ℝ) = f t ^ 2 := by
      intro t
      rw [Real.rpow_two, sq_abs]
    rw [show (∫ t in Set.Ioc a b, |f t| ^ (2 : ℝ)) =
        ∫ t in Set.Ioc a b, f t ^ 2 from integral_congr_ae
          (Filter.Eventually.of_forall hintegrand)]
    exact hfSq
  have hfsq : (∫ t, |f t| ^ (2 : ℝ) ∂μ) ≤ Q ^ 2 := by
    change ∫ t in Set.Ioc a b, |f t| ^ (2 : ℝ) ≤ Q ^ 2
    exact hfsqAbs
  have hsqrt : Real.sqrt (∫ t, |f t| ^ (2 : ℝ) ∂μ) ≤ Q :=
    (Real.sqrt_le_iff).2 ⟨hQ, hfsq⟩
  have htime : |∫ t in a..b, f t| ≤ ∫ t, |f t| ∂μ := by
    have hh := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := f) hab
    simpa [μ, intervalIntegral.integral_of_le hab] using hh
  calc
    |∫ t in a..b, f t| ≤ ∫ t, |f t| ∂μ := htime
    _ ≤ Real.sqrt (b - a) * Real.sqrt (∫ t, |f t| ^ (2 : ℝ) ∂μ) := by
      rw [← hmass]
      exact hHolderSqrt
    _ ≤ Real.sqrt (b - a) * Q := by
      exact mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)

/-- Cauchy--Schwarz for a product over an interval, with each L² energy
bounded separately. -/
theorem hm_interval_integral_product_abs_le_l2
    {a b A B : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : MemLp f 2 (volume.restrict (Set.Ioc a b)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a b)))
    (hfSq : ∫ t in Set.Ioc a b, f t ^ 2 ≤ A ^ 2)
    (hgSq : ∫ t in Set.Ioc a b, g t ^ 2 ≤ B ^ 2) :
    |∫ t in a..b, f t * g t| ≤ A * B := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc a b)
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hg
  have hHolder := integral_mul_norm_le_Lp_mul_Lq
    ((Real.holderConjugate_iff (p := (2 : ℝ)) (q := (2 : ℝ))).mpr
      ⟨by norm_num, by norm_num⟩)
    hf' hg'
  have hHolder' :
      (∫ t, |f t| * |g t| ∂μ) ≤
        (∫ t, |f t| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
          (∫ t, |g t| ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa only [Real.norm_eq_abs] using hHolder
  have hHolderSqrt :
      (∫ t, |f t| * |g t| ∂μ) ≤
        Real.sqrt (∫ t, |f t| ^ (2 : ℝ) ∂μ) *
          Real.sqrt (∫ t, |g t| ^ (2 : ℝ) ∂μ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact hHolder'
  have hfAbsSq : ∫ t in Set.Ioc a b, |f t| ^ (2 : ℝ) ≤ A ^ 2 := by
    have heq : (∫ t in Set.Ioc a b, |f t| ^ (2 : ℝ)) =
        ∫ t in Set.Ioc a b, f t ^ 2 := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Real.rpow_two, sq_abs]
    rw [heq]
    exact hfSq
  have hgAbsSq : ∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ≤ B ^ 2 := by
    have heq : (∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ)) =
        ∫ t in Set.Ioc a b, g t ^ 2 := by
      apply integral_congr_ae
      filter_upwards with t
      rw [Real.rpow_two, sq_abs]
    rw [heq]
    exact hgSq
  have hfAbsSq' : (∫ t, |f t| ^ (2 : ℝ) ∂μ) ≤ A ^ 2 := by
    change ∫ t in Set.Ioc a b, |f t| ^ (2 : ℝ) ≤ A ^ 2
    exact hfAbsSq
  have hgAbsSq' : (∫ t, |g t| ^ (2 : ℝ) ∂μ) ≤ B ^ 2 := by
    change ∫ t in Set.Ioc a b, |g t| ^ (2 : ℝ) ≤ B ^ 2
    exact hgAbsSq
  have hsqrtF : Real.sqrt (∫ t, |f t| ^ (2 : ℝ) ∂μ) ≤ A :=
    (Real.sqrt_le_iff).2 ⟨hA, hfAbsSq'⟩
  have hsqrtG : Real.sqrt (∫ t, |g t| ^ (2 : ℝ) ∂μ) ≤ B :=
    (Real.sqrt_le_iff).2 ⟨hB, hgAbsSq'⟩
  have htime : |∫ t in a..b, f t * g t| ≤ ∫ t, |f t| * |g t| ∂μ := by
    have hh := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := fun t => f t * g t) hab
    simpa [μ, intervalIntegral.integral_of_le hab, abs_mul] using hh
  calc
    |∫ t in a..b, f t * g t| ≤ ∫ t, |f t| * |g t| ∂μ := htime
    _ ≤ Real.sqrt (∫ t, |f t| ^ (2 : ℝ) ∂μ) *
        Real.sqrt (∫ t, |g t| ^ (2 : ℝ) ∂μ) := hHolderSqrt
    _ ≤ A * B := by
      calc
        _ ≤ A * Real.sqrt (∫ t, |g t| ^ (2 : ℝ) ∂μ) :=
          mul_le_mul_of_nonneg_right hsqrtF (Real.sqrt_nonneg _)
        _ ≤ A * B := mul_le_mul_of_nonneg_left hsqrtG hA

/-- Spatial Cauchy--Schwarz for the regular source pairing on the torus cell. -/
theorem hm_unitCube_scalar_pairing_abs_le
    {f g : Vec 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    |∫ x in AVenhance.unitCube, f x * g x| ≤
      Real.sqrt (AVenhance.l2NormSq f) * Real.sqrt (AVenhance.l2NormSq g) := by
  have hfSqInt : Integrable (fun x => f x ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous (hf.pow 2)
  have hgSqInt : Integrable (fun x => g x ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous (hg.pow 2)
  have hfMem : MemLp f 2 (volume.restrict AVenhance.unitCube) :=
    (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable)).mpr hfSqInt
  have hgMem : MemLp g 2 (volume.restrict AVenhance.unitCube) :=
    (memLp_two_iff_integrable_sq (hg.aestronglyMeasurable)).mpr hgSqInt
  have hfMem' : MemLp f (ENNReal.ofReal (2 : ℝ))
      (volume.restrict AVenhance.unitCube) := by simpa using hfMem
  have hgMem' : MemLp g (ENNReal.ofReal (2 : ℝ))
      (volume.restrict AVenhance.unitCube) := by simpa using hgMem
  have hHolder := integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two hfMem' hgMem'
  have hnormF : (∫ x, ‖f x‖ ^ (2 : ℝ)
      ∂volume.restrict AVenhance.unitCube) =
      ∫ x, f x ^ 2 ∂volume.restrict AVenhance.unitCube := by
    apply integral_congr_ae
    filter_upwards with x
    simp [Real.norm_eq_abs, sq_abs]
  have hnormG : (∫ x, ‖g x‖ ^ (2 : ℝ)
      ∂volume.restrict AVenhance.unitCube) =
      ∫ x, g x ^ 2 ∂volume.restrict AVenhance.unitCube := by
    apply integral_congr_ae
    filter_upwards with x
    simp [Real.norm_eq_abs, sq_abs]
  rw [hnormF, hnormG] at hHolder
  have hHolder' :
      (∫ x, ‖f x‖ * ‖g x‖ ∂volume.restrict AVenhance.unitCube) ≤
        (∫ x, f x ^ 2 ∂volume.restrict AVenhance.unitCube) ^ (1 / (2 : ℝ)) *
          (∫ x, g x ^ 2 ∂volume.restrict AVenhance.unitCube) ^ (1 / (2 : ℝ)) := hHolder
  have hprod :
      (∫ x, |f x * g x| ∂volume.restrict AVenhance.unitCube) =
        ∫ x, ‖f x‖ * ‖g x‖ ∂volume.restrict AVenhance.unitCube := by
    apply integral_congr_ae
    filter_upwards with x
    simp [Real.norm_eq_abs, abs_mul]
  have hleft :
      |∫ x, f x * g x ∂volume.restrict AVenhance.unitCube| ≤
        ∫ x, |f x * g x| ∂volume.restrict AVenhance.unitCube :=
    abs_integral_le_integral_abs
  have hfEnergy :
      (∫ x, f x ^ 2 ∂volume.restrict AVenhance.unitCube) = AVenhance.l2NormSq f := rfl
  have hgEnergy :
      (∫ x, g x ^ 2 ∂volume.restrict AVenhance.unitCube) = AVenhance.l2NormSq g := rfl
  have hbound :
      (∫ x, ‖f x‖ * ‖g x‖ ∂volume.restrict AVenhance.unitCube) ≤
        Real.sqrt (AVenhance.l2NormSq f) *
          Real.sqrt (AVenhance.l2NormSq g) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← hfEnergy, ← hgEnergy]
    exact hHolder'
  have hconvert : (∫ x in AVenhance.unitCube, f x * g x) =
      ∫ x, f x * g x ∂volume.restrict AVenhance.unitCube := rfl
  rw [hconvert]
  exact (hleft.trans (hprod ▸ hbound))

theorem HmPairingEstimates.hm_vecNormSq_nonneg (u : Vec 2) : 0 ≤ vecNormSq u := by
  unfold vecNormSq vecDot
  exact Finset.sum_nonneg fun i hi => by nlinarith [sq_nonneg (u i)]

theorem HmPairingEstimates.hm_vecDot_abs_le_norm (u v : Vec 2) :
    |vecDot u v| ≤ Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq v) := by
  have hdotSq : (vecDot u v) ^ 2 ≤ vecNormSq u * vecNormSq v := by
    simpa [vecDot, vecNormSq, pow_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 2)) u v)
  calc
    |vecDot u v| = Real.sqrt ((vecDot u v) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (vecNormSq u * vecNormSq v) := Real.sqrt_le_sqrt hdotSq
    _ = Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq v) :=
      Real.sqrt_mul (HmPairingEstimates.hm_vecNormSq_nonneg u) _

/-- Spatial Cauchy--Schwarz for a vector flux pairing on the torus cell. -/
theorem hm_unitCube_vector_pairing_abs_le
    {F V : Vec 2 → Vec 2} (hF : Continuous F) (hV : Continuous V) :
    |∫ x in AVenhance.unitCube, vecDot (F x) (V x)| ≤
      Real.sqrt (AVenhance.gradNormSq F) * Real.sqrt (AVenhance.gradNormSq V) := by
  let f : Vec 2 → ℝ := fun x => Real.sqrt (vecNormSq (F x))
  let g : Vec 2 → ℝ := fun x => Real.sqrt (vecNormSq (V x))
  have hf : Continuous f := by
    dsimp [f]
    exact (AVenhance.Infra.Section5.LeftToShow.continuous_vecNormSq_two.comp hF).sqrt
  have hg : Continuous g := by
    dsimp [g]
    exact (AVenhance.Infra.Section5.LeftToShow.continuous_vecNormSq_two.comp hV).sqrt
  have hfSqInt : Integrable (fun x => f x ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous (hf.pow 2)
  have hgSqInt : Integrable (fun x => g x ^ 2)
      (volume.restrict AVenhance.unitCube) :=
    AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous (hg.pow 2)
  have hfMem : MemLp f 2 (volume.restrict AVenhance.unitCube) :=
    (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable)).mpr hfSqInt
  have hgMem : MemLp g 2 (volume.restrict AVenhance.unitCube) :=
    (memLp_two_iff_integrable_sq (hg.aestronglyMeasurable)).mpr hgSqInt
  have hfMem' : MemLp f (ENNReal.ofReal (2 : ℝ))
      (volume.restrict AVenhance.unitCube) := by simpa using hfMem
  have hgMem' : MemLp g (ENNReal.ofReal (2 : ℝ))
      (volume.restrict AVenhance.unitCube) := by simpa using hgMem
  have hHolder := integral_mul_norm_le_Lp_mul_Lq
    Real.HolderConjugate.two_two hfMem' hgMem'
  have hfSq : (∫ x, f x ^ 2 ∂volume.restrict AVenhance.unitCube) =
      AVenhance.gradNormSq F := by
    have heq : (fun x => f x ^ 2) = fun x => vecNormSq (F x) := by
      funext x
      dsimp [f]
      exact Real.sq_sqrt (HmPairingEstimates.hm_vecNormSq_nonneg (F x))
    rw [heq]
    rfl
  have hgSq : (∫ x, g x ^ 2 ∂volume.restrict AVenhance.unitCube) =
      AVenhance.gradNormSq V := by
    have heq : (fun x => g x ^ 2) = fun x => vecNormSq (V x) := by
      funext x
      dsimp [g]
      exact Real.sq_sqrt (HmPairingEstimates.hm_vecNormSq_nonneg (V x))
    rw [heq]
    rfl
  have hHolderSq :
      (∫ x, ‖f x‖ * ‖g x‖ ∂volume.restrict AVenhance.unitCube) ≤
        (∫ x, f x ^ 2 ∂volume.restrict AVenhance.unitCube) ^ (1 / (2 : ℝ)) *
          (∫ x, g x ^ 2 ∂volume.restrict AVenhance.unitCube) ^ (1 / (2 : ℝ)) := by
    have hnormF : (∫ x, ‖f x‖ ^ (2 : ℝ)
        ∂volume.restrict AVenhance.unitCube) =
        ∫ x, f x ^ 2 ∂volume.restrict AVenhance.unitCube := by
      apply integral_congr_ae
      filter_upwards with x
      simp [Real.norm_eq_abs, sq_abs]
    have hnormG : (∫ x, ‖g x‖ ^ (2 : ℝ)
        ∂volume.restrict AVenhance.unitCube) =
        ∫ x, g x ^ 2 ∂volume.restrict AVenhance.unitCube := by
      apply integral_congr_ae
      filter_upwards with x
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnormF, hnormG] at hHolder
    exact hHolder
  have hHolderBound :
      (∫ x, ‖f x‖ * ‖g x‖ ∂volume.restrict AVenhance.unitCube) ≤
        Real.sqrt (AVenhance.gradNormSq F) * Real.sqrt (AVenhance.gradNormSq V) := by
    calc
      _ ≤ (∫ x, f x ^ 2 ∂volume.restrict AVenhance.unitCube) ^ (1 / (2 : ℝ)) *
          (∫ x, g x ^ 2 ∂volume.restrict AVenhance.unitCube) ^ (1 / (2 : ℝ)) := hHolderSq
      _ = _ := by
        rw [← hfSq, ← hgSq, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hnormProd :
      (∫ x, ‖f x‖ * ‖g x‖ ∂volume.restrict AVenhance.unitCube) =
        ∫ x, f x * g x ∂volume.restrict AVenhance.unitCube := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
  have hpoint : ∀ x, |vecDot (F x) (V x)| ≤ f x * g x := by
    intro x
    simpa [f, g] using HmPairingEstimates.hm_vecDot_abs_le_norm (F x) (V x)
  have hdotCont : Continuous (fun x => vecDot (F x) (V x)) := by
    fun_prop [vecDot]
  have hprodCont : Continuous (fun x => f x * g x) := hf.mul hg
  have hleftInt : Integrable (fun x => |vecDot (F x) (V x)|)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [IntegrableOn] using
      AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous hdotCont.abs
  have hrightInt : Integrable (fun x => f x * g x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [IntegrableOn] using
      AVenhance.Infra.Section5.LeftToShow.integrableOn_unitCube_of_continuous hprodCont
  have hmono := integral_mono hleftInt hrightInt fun x => hpoint x
  have hleft :
      |∫ x, vecDot (F x) (V x) ∂volume.restrict AVenhance.unitCube| ≤
        ∫ x, |vecDot (F x) (V x)| ∂volume.restrict AVenhance.unitCube :=
    abs_integral_le_integral_abs
  have hconvert : (∫ x in AVenhance.unitCube,
      vecDot (F x) (V x)) =
      ∫ x, vecDot (F x) (V x) ∂volume.restrict AVenhance.unitCube := rfl
  rw [hconvert]
  calc
    _ ≤ ∫ x, |vecDot (F x) (V x)| ∂volume.restrict AVenhance.unitCube := hleft
    _ ≤ ∫ x, f x * g x ∂volume.restrict AVenhance.unitCube := hmono
    _ = ∫ x, ‖f x‖ * ‖g x‖ ∂volume.restrict AVenhance.unitCube := hnormProd.symm
    _ ≤ _ := hHolderBound

/-- The integrated regular pairing is bounded using only an envelope for
`F` and the time L² energy of `G`. -/
theorem hm_regular_pairing_interval_bound_of_l2
    {F G : ℝ → Vec 2 → ℝ} {a b H Q : ℝ} (hab : a ≤ b)
    (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (hFbound : ∀ s ∈ Set.Ioc a b,
      Real.sqrt (AVenhance.l2NormSq (F s)) ≤ H)
    (hFcont : ∀ s ∈ Set.Ioc a b, Continuous (F s))
    (hGcont : ∀ s ∈ Set.Ioc a b, Continuous (G s))
    (hGnorm : MemLp (fun s => Real.sqrt (AVenhance.l2NormSq (G s))) 2
      (volume.restrict (Set.Ioc a b)))
    (hGsq : ∫ s in Set.Ioc a b,
      (Real.sqrt (AVenhance.l2NormSq (G s))) ^ 2 ≤ Q ^ 2)
    (hGint : Integrable (fun s => Real.sqrt (AVenhance.l2NormSq (G s)))
      (volume.restrict (Set.Ioc a b)))
    (hPairAbsInt : Integrable
      (fun s => |hmRegularPairing (F := F) (G := G) s|)
      (volume.restrict (Set.Ioc a b))) :
    |∫ s in a..b, hmRegularPairing (F := F) (G := G) s| ≤
      Real.sqrt (b - a) * Q * H := by
  let gnorm : ℝ → ℝ := fun s => Real.sqrt (AVenhance.l2NormSq (G s))
  have hpoint : ∀ s ∈ Set.Ioc a b,
      |hmRegularPairing (F := F) (G := G) s| ≤ H * gnorm s := by
    intro s hs
    have hspace := hm_unitCube_scalar_pairing_abs_le (hFcont s hs) (hGcont s hs)
    have hspace' : |hmRegularPairing (F := F) (G := G) s| ≤
        Real.sqrt (AVenhance.l2NormSq (F s)) * gnorm s := by
      simpa [hmRegularPairing, gnorm] using hspace
    exact hspace'.trans (mul_le_mul_of_nonneg_right (hFbound s hs)
      (Real.sqrt_nonneg _))
  have hmono :
      (∫ s, |hmRegularPairing (F := F) (G := G) s|
        ∂volume.restrict (Set.Ioc a b)) ≤
      ∫ s, H * gnorm s ∂volume.restrict (Set.Ioc a b) := by
    apply integral_mono_ae hPairAbsInt (by simpa [gnorm] using hGint.const_mul H)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hpoint s hs
  have hGbound := hm_interval_integral_abs_le_sqrt_length_mul_l2
    (a := a) (b := b) (Q := Q) hab hQ hGnorm hGsq
  have hGsetEq :
      (∫ s, gnorm s ∂volume.restrict (Set.Ioc a b)) =
        ∫ s in a..b, gnorm s := by
    symm
    rw [intervalIntegral.integral_of_le hab]
  have hGsetBound :
      (∫ s, gnorm s ∂volume.restrict (Set.Ioc a b)) ≤ Real.sqrt (b - a) * Q := by
    rw [hGsetEq]
    exact (le_abs_self _).trans hGbound
  have hregularTime :
      |∫ s in a..b, hmRegularPairing (F := F) (G := G) s| ≤
        ∫ s, |hmRegularPairing (F := F) (G := G) s|
          ∂volume.restrict (Set.Ioc a b) := by
    have hh := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := hmRegularPairing (F := F) (G := G)) hab
    simpa [intervalIntegral.integral_of_le hab] using hh
  have hmono' :
      (∫ s, |hmRegularPairing (F := F) (G := G) s|
        ∂volume.restrict (Set.Ioc a b)) ≤
      H * ∫ s, gnorm s ∂volume.restrict (Set.Ioc a b) := by
    calc
      _ ≤ ∫ s, H * gnorm s ∂volume.restrict (Set.Ioc a b) := hmono
      _ = H * ∫ s, gnorm s ∂volume.restrict (Set.Ioc a b) := integral_const_mul H _
  calc
    _ ≤ ∫ s, |hmRegularPairing (F := F) (G := G) s|
        ∂volume.restrict (Set.Ioc a b) := hregularTime
    _ ≤ H * ∫ s, gnorm s ∂volume.restrict (Set.Ioc a b) := hmono'
    _ ≤ H * (Real.sqrt (b - a) * Q) :=
      mul_le_mul_of_nonneg_left hGsetBound hH
    _ = Real.sqrt (b - a) * Q * H := by ring

/-- The integrated gradient--flux pairing is controlled by the product of
the time L² norms of the two spatial vector fields. -/
theorem hm_flux_pairing_interval_bound_of_l2
    {F : ℝ → Vec 2 → ℝ} {V : ℝ → Vec 2 → Vec 2}
    {a b QF QV : ℝ} (hab : a ≤ b) (hQF : 0 ≤ QF) (hQV : 0 ≤ QV)
    (hGradCont : ∀ s ∈ Set.Ioc a b, Continuous (AVenhance.spaceGrad (F s)))
    (hVcont : ∀ s ∈ Set.Ioc a b, Continuous (V s))
    (hFnorm : MemLp
      (fun s => Real.sqrt (AVenhance.gradNormSq (fun x =>
        AVenhance.spaceGrad (F s) x))) 2
      (volume.restrict (Set.Ioc a b)))
    (hVnorm : MemLp
      (fun s => Real.sqrt (AVenhance.gradNormSq (V s))) 2
      (volume.restrict (Set.Ioc a b)))
    (hFsq : ∫ s in Set.Ioc a b,
      (Real.sqrt (AVenhance.gradNormSq (fun x =>
        AVenhance.spaceGrad (F s) x))) ^ 2 ≤ QF ^ 2)
    (hVsq : ∫ s in Set.Ioc a b,
      (Real.sqrt (AVenhance.gradNormSq (V s))) ^ 2 ≤ QV ^ 2)
    (hPairAbsInt : Integrable
      (fun s => |hmFluxPairing (F := F) (V := V) s|)
      (volume.restrict (Set.Ioc a b))) :
    |∫ s in a..b, hmFluxPairing (F := F) (V := V) s| ≤ QF * QV := by
  let fNorm : ℝ → ℝ := fun s =>
    Real.sqrt (AVenhance.gradNormSq (fun x => AVenhance.spaceGrad (F s) x))
  let vNorm : ℝ → ℝ := fun s => Real.sqrt (AVenhance.gradNormSq (V s))
  have hpairPoint : ∀ s ∈ Set.Ioc a b,
      |hmFluxPairing (F := F) (V := V) s| ≤ fNorm s * vNorm s := by
    intro s hs
    have hvec := hm_unitCube_vector_pairing_abs_le (hGradCont s hs) (hVcont s hs)
    have hcoords :
        (∫ x in AVenhance.unitCube,
          (AVenhance.spaceGrad (F s) x 0 * V s x 0 +
            AVenhance.spaceGrad (F s) x 1 * V s x 1)) =
          ∫ x in AVenhance.unitCube,
            vecDot (AVenhance.spaceGrad (F s) x) (V s x) := by
      apply integral_congr_ae
      filter_upwards with x
      simp [vecDot, Fin.sum_univ_two]
    change |-(∫ x in AVenhance.unitCube,
        (AVenhance.spaceGrad (F s) x 0 * V s x 0 +
          AVenhance.spaceGrad (F s) x 1 * V s x 1))| ≤ _
    rw [hcoords]
    simpa [fNorm, vNorm, abs_neg] using hvec
  have hProductInt : Integrable (fun s => fNorm s * vNorm s)
      (volume.restrict (Set.Ioc a b)) := by
    exact hFnorm.integrable_mul hVnorm
  have hmono :
      (∫ s, |hmFluxPairing (F := F) (V := V) s|
        ∂volume.restrict (Set.Ioc a b)) ≤
      ∫ s, fNorm s * vNorm s ∂volume.restrict (Set.Ioc a b) := by
    apply integral_mono_ae hPairAbsInt (by simpa [fNorm, vNorm] using hProductInt)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hpairPoint s hs
  have hprodBound := hm_interval_integral_product_abs_le_l2
    (a := a) (b := b) hab hQF hQV hFnorm hVnorm hFsq hVsq
  have hprodEq : (∫ s, fNorm s * vNorm s
      ∂volume.restrict (Set.Ioc a b)) =
      ∫ s in a..b, fNorm s * vNorm s := by
    symm
    rw [intervalIntegral.integral_of_le hab]
  have hprodBound' :
      (∫ s, fNorm s * vNorm s ∂volume.restrict (Set.Ioc a b)) ≤ QF * QV := by
    rw [hprodEq]
    exact (le_abs_self _).trans hprodBound
  have htime :
      |∫ s in a..b, hmFluxPairing (F := F) (V := V) s| ≤
        ∫ s, |hmFluxPairing (F := F) (V := V) s|
          ∂volume.restrict (Set.Ioc a b) := by
    have hh := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := hmFluxPairing (F := F) (V := V)) hab
    simpa [intervalIntegral.integral_of_le hab] using hh
  exact htime.trans (hmono.trans hprodBound')

end AVenhance.Infra.Section4

end
