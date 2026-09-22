/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspLocalization
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothDual

/-!
# Descendant localization preliminaries for the smooth negative fractional norm

This module records the exact normalized-pairing partition and the canonical
restriction of a globally smooth test field.  They are the two analytic inputs
needed for negative-norm localization by finite Hoelder duality.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private def CubeEuclideanWspSmoothTest.restrictToSubcube {d : ℕ}
    {Q R : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p)
    (_hRQ : openCubeSet R ⊆ openCubeSet Q) :
    CubeEuclideanWspSmoothTest R s p where
  toField := h.toField
  contDiff := h.contDiff

private theorem cubeEuclideanNormalizedSmoothPairing_restrictToSubcube {d : ℕ}
    {Q R : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (h : CubeEuclideanWspSmoothTest Q s p) :
    cubeEuclideanNormalizedSmoothPairing (F.restrictToSubcube hRQ)
        (h.restrictToSubcube hRQ) =
      ∫ x, vecDot (F.toField x) (h.toField x) ∂normalizedCubeMeasure R := by
  rfl

/-- Exact partition of a normalized real pairing over descendants. -/
private theorem cubeEuclideanNormalizedSmoothPairing_descendants_eq {d : ℕ}
    (Q : TriadicCube d) (j : ℕ)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    cubeEuclideanNormalizedSmoothPairing F h =
      descendantsAverage Q j (fun R =>
        if hR : R ∈ descendantsAtDepth Q j then
          cubeEuclideanNormalizedSmoothPairing
            (F.restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))
            (h.restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))
        else 0) := by
  let g : Vec d → ℝ := fun x => vecDot (F.toField x) (h.toField x)
  have hg : IntegrableOn g (cubeSet Q) volume := by
    have hscale_ne_zero : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 := by
      exact ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (cubeVolume_pos Q))
    change Integrable g (volume.restrict (cubeSet Q))
    have hInt := cubeEuclideanNormalizedSmoothPairing_integrable F h
    rw [normalizedCubeMeasure, cubeMeasure] at hInt
    exact (integrable_smul_measure hscale_ne_zero ENNReal.ofReal_ne_top).1 hInt
  unfold cubeEuclideanNormalizedSmoothPairing
  rw [← cubeAverage_eq_integral_normalizedCubeMeasure Q g]
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j g hg]
  simp only [descendantsAverage]
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  simp only [dif_pos hR]
  rfl

private theorem cubeEuclideanWspFullENorm_descendant_lt_top_of_le_one {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (s : FractionalOrder) (p : FiniteLpExponent)
    (h : CubeEuclideanWspSmoothTest Q s p)
    (hunit : cubeEuclideanWspFullENorm Q s p h.toField ≤ 1)
    {R : TriadicCube d} (hR : R ∈ descendantsAtDepth Q j) :
    cubeEuclideanWspFullENorm R s p h.toField < ∞ := by
  let t : ℝ := p.exponent.toReal
  let A : ℝ≥0∞ := descendantsENNAverage Q j
    (fun S => cubeEuclideanWspFullENorm S s p h.toField ^ t)
  have ht : 0 < t := ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hroot := descendantsENNAverage_cubeEuclideanWspFullENorm_root_le
    Q j s p h.toField
  have hscale : (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg
      (mul_nonneg (Nat.cast_nonneg _) s.2.1.le) ENNReal.ofReal_ne_top
  have hroot_top : A ^ t⁻¹ < ∞ := by
    apply lt_of_le_of_lt hroot
    exact ENNReal.mul_lt_top hscale (lt_of_le_of_lt hunit ENNReal.one_lt_top)
  have hA_top : A < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos (inv_pos.mpr ht)).mp hroot_top
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hD : D.Nonempty := by simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard_ne_zero : ((D.card : ℝ≥0∞)⁻¹) ≠ 0 := by
    rw [ENNReal.inv_ne_zero]
    simp
  have hcard_ne_top : ((D.card : ℝ≥0∞)⁻¹) < ∞ := by
    rw [ENNReal.inv_lt_top]
    simp [hD]
  have hsum_top : (∑ S ∈ D,
      cubeEuclideanWspFullENorm S s p h.toField ^ t) < ∞ := by
    have hmul : ((D.card : ℝ≥0∞)⁻¹) *
        (∑ S ∈ D, cubeEuclideanWspFullENorm S s p h.toField ^ t) < ∞ := by
      simpa only [A, descendantsENNAverage, D] using hA_top
    rcases (ENNReal.mul_lt_top_iff.mp hmul) with hboth | hzero | hsumzero
    · exact hboth.2
    · exact False.elim (hcard_ne_zero hzero)
    · simp [hsumzero]
  have hterm_top : cubeEuclideanWspFullENorm R s p h.toField ^ t < ∞ := by
    apply (ENNReal.sum_lt_top.mp hsum_top) R
    simpa [D] using hR
  exact (ENNReal.rpow_lt_top_iff_of_pos ht).mp hterm_top

private def CubeEuclideanWspSmoothTest.scale {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (c : ℝ) (h : CubeEuclideanWspSmoothTest Q s p) :
    CubeEuclideanWspSmoothTest Q s p where
  toField x := c • h.toField x
  contDiff := h.contDiff.const_smul c

private theorem negativeLocalization_kernel_smul {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (c : ℝ)
    (f : Vec d → Vec d) :
    cubeEuclideanWspKernel s p (fun x => c • f x) =
      c • cubeEuclideanWspKernel s p f := by
  funext z
  simp only [cubeEuclideanWspKernel_apply, Pi.smul_apply]
  rw [← smul_sub]
  change _ • (c • HilbertVec.ofVec (f z.1 - f z.2)) =
    c • (_ • HilbertVec.ofVec (f z.1 - f z.2))
  rw [smul_smul, smul_smul, mul_comm]

private theorem negativeLocalization_normalizedLp_smul {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (c : ℝ)
    (f : Vec d → Vec d) :
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent
        (fun x => c • f x) =
      ‖c‖ₑ *
        (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent f := by
  unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
  unfold BoundedMeasurableDomain.normalizedLpENorm
  simp only [ite_eq_right (ne_of_gt (lt_trans zero_lt_one p.one_lt)),
    ite_eq_right p.lt_top.ne]
  change eLpNorm' (fun x => euclideanNorm (c • f x)) p.exponent.toReal
      (cubeBoundedMeasurableDomain Q).normalizedVolume = _
  simp_rw [euclideanNorm_smul]
  change eLpNorm' ((|c| : ℝ) • fun x => euclideanNorm (f x)) p.exponent.toReal
      (cubeBoundedMeasurableDomain Q).normalizedVolume = _
  rw [eLpNorm'_const_smul _ (ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne)]
  simp

private theorem negativeLocalization_eSeminorm_smul {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (c : ℝ) (f : Vec d → Vec d) :
    cubeEuclideanWspESeminorm Q s p (fun x => c • f x) =
      ‖c‖ₑ * cubeEuclideanWspESeminorm Q s p f := by
  unfold cubeEuclideanWspESeminorm
  rw [negativeLocalization_kernel_smul]
  exact eLpNorm'_const_smul c (ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne)

private theorem negativeLocalization_fullENorm_smul {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (c : ℝ) (f : Vec d → Vec d) :
    cubeEuclideanWspFullENorm Q s p (fun x => c • f x) =
      ‖c‖ₑ * cubeEuclideanWspFullENorm Q s p f := by
  let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
    p.exponent f
  let S := cubeEuclideanWspESeminorm Q s p f
  let W := cubeEuclideanWspScalePowerWeight Q s p
  let t := p.exponent.toReal
  have ht : 0 < t :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have htin : 0 ≤ t⁻¹ := inv_nonneg.mpr ht.le
  rw [cubeEuclideanWspFullENorm,
    negativeLocalization_normalizedLp_smul,
    negativeLocalization_eSeminorm_smul]
  change (W * (‖c‖ₑ * L) ^ t + (‖c‖ₑ * S) ^ t) ^ t⁻¹ =
    ‖c‖ₑ * (W * L ^ t + S ^ t) ^ t⁻¹
  rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le,
    ENNReal.mul_rpow_of_nonneg _ _ ht.le]
  calc
    (W * (‖c‖ₑ ^ t * L ^ t) + ‖c‖ₑ ^ t * S ^ t) ^ t⁻¹ =
        (‖c‖ₑ ^ t * (W * L ^ t + S ^ t)) ^ t⁻¹ := by
      congr 1
      rw [mul_add]
      ac_rfl
    _ = (‖c‖ₑ ^ t) ^ t⁻¹ * (W * L ^ t + S ^ t) ^ t⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ htin]
    _ = ‖c‖ₑ * (W * L ^ t + S ^ t) ^ t⁻¹ := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ ht.ne', ENNReal.rpow_one]

private theorem negativeLocalization_pairing_scale {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p) (c : ℝ) :
    cubeEuclideanNormalizedSmoothPairing F (h.scale c) =
      c * cubeEuclideanNormalizedSmoothPairing F h := by
  unfold cubeEuclideanNormalizedSmoothPairing CubeEuclideanWspSmoothTest.scale
  simp_rw [vecDot_smul_right]
  exact integral_const_mul c _

private theorem negativeLocalization_normalizedLp_eq_zero_of_full_eq_zero {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (f : Vec d → Vec d) (hf : cubeEuclideanWspFullENorm Q s p f = 0) :
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent f = 0 := by
  let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent f
  let S := cubeEuclideanWspESeminorm Q s p f
  let W := cubeEuclideanWspScalePowerWeight Q s p
  let t := p.exponent.toReal
  have ht : 0 < t :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hW : W ≠ 0 := by
    apply ne_of_gt
    unfold W cubeEuclideanWspScalePowerWeight
    exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hscale) ENNReal.ofReal_ne_top
  have hbase : W * L ^ t + S ^ t = 0 := by
    rw [← ENNReal.rpow_eq_zero_iff_of_pos (inv_pos.mpr ht)]
    simpa only [cubeEuclideanWspFullENorm, L, S, W, t] using hf
  have hterm : W * L ^ t = 0 := (add_eq_zero.mp hbase).1
  have hpow : L ^ t = 0 := (mul_eq_zero.mp hterm).resolve_left hW
  exact (ENNReal.rpow_eq_zero_iff_of_pos ht).mp hpow

private theorem negativeLocalization_pairing_eq_zero_of_full_eq_zero {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    {p : FiniteLpExponent} (h : CubeEuclideanWspSmoothTest Q s p)
    (hh : cubeEuclideanWspFullENorm Q s p h.toField = 0) :
    cubeEuclideanNormalizedSmoothPairing F h = 0 := by
  have hLp : (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
      p.exponent h.toField = 0 :=
    negativeLocalization_normalizedLp_eq_zero_of_full_eq_zero Q s p h.toField hh
  have hmeas : AEStronglyMeasurable (fun x => euclideanNorm (h.toField x))
      (normalizedCubeMeasure Q) := by
    simpa only [euclideanNorm_eq_norm_ofVec] using
      (CubeEuclideanWspSmoothTest.euclideanMemLp_of_continuous Q
        p.exponent h.contDiff.continuous).aestronglyMeasurable.norm
  have hLp' : eLpNorm (fun x => euclideanNorm (h.toField x))
      p.exponent (normalizedCubeMeasure Q) = 0 := by
    rw [← cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    rw [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm_eq_eLpNorm _ _ _ (by
        rwa [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure])] at hLp
    exact hLp
  have hp_ne_zero : p.exponent ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one p.one_lt)
  have hnorm_zero : (fun x => euclideanNorm (h.toField x)) =ᵐ[
      normalizedCubeMeasure Q] 0 :=
    (eLpNorm_eq_zero_iff hp_ne_zero).mp hLp'
  have hfield_zero : h.toField =ᵐ[normalizedCubeMeasure Q] 0 := by
    filter_upwards [hnorm_zero] with x hx
    exact euclideanNorm_eq_zero_iff.mp hx
  unfold cubeEuclideanNormalizedSmoothPairing
  apply integral_eq_zero_of_ae
  filter_upwards [hfield_zero] with x hx
  simp [hx, vecDot]

private theorem negativeLocalization_pairing_le_dual_mul_full {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p.conjugate)
    (hNtop : cubeEuclideanWspFullENorm Q s p.conjugate h.toField < ∞) :
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
      cubeEuclideanNegativeWspSmoothDualENorm Q s p F *
        cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
  set N := cubeEuclideanWspFullENorm Q s p.conjugate h.toField
  set D := cubeEuclideanNegativeWspSmoothDualENorm Q s p F
  by_cases hNzero : N = 0
  · have hzero : cubeEuclideanNormalizedSmoothPairing F h = 0 := by
      apply negativeLocalization_pairing_eq_zero_of_full_eq_zero Q s F h
      simpa only [N] using hNzero
    simp [hzero, hNzero]
  · let r : ℝ := N.toReal⁻¹
    have hrpos : 0 < r := by
      dsimp [r]
      exact inv_pos.mpr (ENNReal.toReal_pos hNzero hNtop.ne)
    let hs := h.scale r
    have hhsnorm : cubeEuclideanWspFullENorm Q s p.conjugate hs.toField = 1 := by
      change cubeEuclideanWspFullENorm Q s p.conjugate
        (fun x => r • h.toField x) = 1
      rw [negativeLocalization_fullENorm_smul]
      change ‖r‖ₑ * N = 1
      have hr : ENNReal.ofReal r = N⁻¹ := by
        dsimp [r]
        rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hNzero hNtop.ne),
          ENNReal.ofReal_toReal hNtop.ne]
      rw [Real.enorm_eq_ofReal hrpos.le, hr,
        ENNReal.inv_mul_cancel hNzero hNtop.ne]
    let u : CubeEuclideanWspSmoothUnitTest Q s p.conjugate :=
      ⟨hs, hhsnorm.le⟩
    have hu : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| ≤ D := by
      rw [show D = cubeEuclideanNegativeWspSmoothDualENorm Q s p F by rfl,
        cubeEuclideanNegativeWspSmoothDualENorm]
      exact le_iSup (fun u : CubeEuclideanWspSmoothUnitTest Q s p.conjugate =>
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F u.1|) u
    have hpair : cubeEuclideanNormalizedSmoothPairing F hs =
        r * cubeEuclideanNormalizedSmoothPairing F h := by
      exact negativeLocalization_pairing_scale F h r
    have hscaled : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| =
        N⁻¹ * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| := by
      rw [hpair, abs_mul, abs_of_pos hrpos, ENNReal.ofReal_mul hrpos.le]
      congr 1
      dsimp [r]
      rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hNzero hNtop.ne),
        ENNReal.ofReal_toReal hNtop.ne]
    calc
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| =
          N * (N⁻¹ * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h|) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hNzero hNtop.ne, one_mul]
      _ = N * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| := by
        rw [hscaled]
      _ ≤ N * D := by simpa [mul_comm] using mul_le_mul_left hu N
      _ = D * N := mul_comm _ _

private theorem negativeLocalization_finite_holder_average {ι : Type*}
    (D : Finset ι) (hD : D.Nonempty) (p : FiniteLpExponent) (a b : ι → ℝ≥0∞) :
    ((D.card : ℝ≥0∞)⁻¹ * ∑ i ∈ D, a i * b i) ≤
      (((D.card : ℝ≥0∞)⁻¹ * ∑ i ∈ D, a i ^ p.exponent.toReal) ^
        (p.exponent.toReal)⁻¹) *
      (((D.card : ℝ≥0∞)⁻¹ * ∑ i ∈ D, b i ^ p.conjugate.exponent.toReal) ^
        (p.conjugate.exponent.toReal)⁻¹) := by
  have hp : 1 < p.exponent.toReal := by
    rw [← ENNReal.toReal_one,
      ENNReal.toReal_lt_toReal ENNReal.one_ne_top p.lt_top.ne]
    exact p.one_lt
  have hpq : p.exponent.toReal.HolderConjugate p.conjugate.exponent.toReal := by
    let : ENNReal.HolderConjugate p.exponent p.conjugate.exponent := p.holderConjugate
    exact ENNReal.HolderConjugate.toReal hp
  let c : ℝ≥0∞ := (D.card : ℝ≥0∞)⁻¹
  have hc0 : c ≠ 0 := by
    rw [show c = (D.card : ℝ≥0∞)⁻¹ by rfl, ENNReal.inv_ne_zero]
    simp
  have hctop : c ≠ ∞ := by
    rw [show c = (D.card : ℝ≥0∞)⁻¹ by rfl, ENNReal.inv_ne_top]
    exact_mod_cast Finset.card_ne_zero.mpr hD
  have hcp : 0 ≤ p.exponent.toReal⁻¹ :=
    inv_nonneg.mpr (le_trans zero_le_one hp.le)
  have hq : 0 < p.conjugate.exponent.toReal := hpq.symm.pos
  have hcq : 0 ≤ p.conjugate.exponent.toReal⁻¹ := inv_nonneg.mpr hq.le
  have hcexp : c ^ p.exponent.toReal⁻¹ *
      c ^ p.conjugate.exponent.toReal⁻¹ = c := by
    rw [← ENNReal.rpow_add _ _ hc0 hctop, hpq.inv_add_inv_eq_one,
      ENNReal.rpow_one]
  have hholder := ENNReal.inner_le_Lp_mul_Lq D a b hpq
  calc
    (D.card : ℝ≥0∞)⁻¹ * ∑ i ∈ D, a i * b i =
        c * ∑ i ∈ D, a i * b i := by rfl
    _ ≤ c * ((∑ i ∈ D, a i ^ p.exponent.toReal) ^
        (1 / p.exponent.toReal) *
        (∑ i ∈ D, b i ^ p.conjugate.exponent.toReal) ^
          (1 / p.conjugate.exponent.toReal)) := by
      simpa [mul_comm] using mul_le_mul_left hholder c
    _ = (c * ∑ i ∈ D, a i ^ p.exponent.toReal) ^ p.exponent.toReal⁻¹ *
        (c * ∑ i ∈ D, b i ^ p.conjugate.exponent.toReal) ^
          p.conjugate.exponent.toReal⁻¹ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hcp,
        ENNReal.mul_rpow_of_nonneg _ _ hcq]
      rw [show 1 / p.exponent.toReal = p.exponent.toReal⁻¹ by ring,
        show 1 / p.conjugate.exponent.toReal =
          p.conjugate.exponent.toReal⁻¹ by ring]
      conv_lhs => rw [← hcexp]
      ac_rfl

private theorem negativeLocalization_descendantsAverage_abs_le {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (f : TriadicCube d → ℝ) :
    ENNReal.ofReal |descendantsAverage Q j f| ≤
      descendantsENNAverage Q j (fun R => ENNReal.ofReal |f R|) := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hD : D.Nonempty := by simpa [D] using descendantsAtDepth_nonempty Q j
  have hcard : 0 < (D.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hD
  rw [descendantsAverage, descendantsENNAverage]
  change ENNReal.ofReal |((D.card : ℝ)⁻¹) * ∑ R ∈ D, f R| ≤ _
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hcard.le),
    ENNReal.ofReal_mul (inv_nonneg.mpr hcard.le),
    ENNReal.ofReal_inv_of_pos hcard, ENNReal.ofReal_natCast]
  gcongr
  calc
    ENNReal.ofReal |∑ R ∈ D, f R| ≤
        ENNReal.ofReal (∑ R ∈ D, |f R|) :=
      ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs f D)
    _ = ∑ R ∈ D, ENNReal.ofReal |f R| := by
      rw [ENNReal.ofReal_sum_of_nonneg fun R _ => abs_nonneg _]

/-- The smooth negative full dual norm localizes over triadic descendants with
the exact normalized outer `ℓᵖ` average. -/
theorem cubeEuclideanNegativeWspSmoothDualENorm_le_descendantsENNAverage {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    cubeEuclideanNegativeWspSmoothDualENorm Q s p F ≤
      (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1) *
        (descendantsENNAverage Q j (fun R =>
          if hR : R ∈ descendantsAtDepth Q j then
            cubeEuclideanNegativeWspSmoothDualENorm R s p
              (F.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)) ^
                  p.exponent.toReal
          else 0)) ^ p.exponent.toReal⁻¹ := by
  rw [cubeEuclideanNegativeWspSmoothDualENorm]
  apply iSup_le
  rintro h
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  let a : TriadicCube d → ℝ≥0∞ := fun R =>
    if hR : R ∈ descendantsAtDepth Q j then
      cubeEuclideanNegativeWspSmoothDualENorm R s p
        (F.restrictToSubcube
          (openCubeSet_subset_of_mem_descendantsAtDepth hR))
    else 0
  let b : TriadicCube d → ℝ≥0∞ := fun R =>
    if hR : R ∈ descendantsAtDepth Q j then
      cubeEuclideanWspFullENorm R s p.conjugate h.1.toField
    else 0
  have hD : D.Nonempty := by simpa [D] using descendantsAtDepth_nonempty Q j
  have hpart : cubeEuclideanNormalizedSmoothPairing F h.1 =
      descendantsAverage Q j (fun R =>
        if hR : R ∈ descendantsAtDepth Q j then
          cubeEuclideanNormalizedSmoothPairing
            (F.restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))
            (h.1.restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))
        else 0) :=
    cubeEuclideanNormalizedSmoothPairing_descendants_eq Q j F h.1
  have hlocal : ∀ (R : TriadicCube d) (hR : R ∈ D),
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing
          (F.restrictToSubcube
            (openCubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR)))
          (h.1.restrictToSubcube
            (openCubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR)))| ≤
        a R * b R := by
    intro R hR
    have hR' : R ∈ descendantsAtDepth Q j := by simpa [D] using hR
    have htop : cubeEuclideanWspFullENorm R s p.conjugate h.1.toField < ∞ :=
      cubeEuclideanWspFullENorm_descendant_lt_top_of_le_one
        Q j s p.conjugate h.1 h.2 hR'
    simp only [a, b, dif_pos hR']
    exact negativeLocalization_pairing_le_dual_mul_full R s p
      (F.restrictToSubcube
        (openCubeSet_subset_of_mem_descendantsAtDepth hR'))
      (h.1.restrictToSubcube
        (openCubeSet_subset_of_mem_descendantsAtDepth hR')) htop
  have hab : descendantsENNAverage Q j (fun R =>
      ENNReal.ofReal |if hR : R ∈ descendantsAtDepth Q j then
        cubeEuclideanNormalizedSmoothPairing
          (F.restrictToSubcube
            (openCubeSet_subset_of_mem_descendantsAtDepth hR))
          (h.1.restrictToSubcube
            (openCubeSet_subset_of_mem_descendantsAtDepth hR))
      else 0|) ≤ descendantsENNAverage Q j (fun R => a R * b R) := by
    unfold descendantsENNAverage
    apply mul_le_mul_right
    apply Finset.sum_le_sum
    intro R hR
    have hR' : R ∈ D := by simpa only using hR
    simp only [dif_pos (by simpa [D] using hR')]
    exact hlocal R hR'

  have hbeq : descendantsENNAverage Q j (fun R => b R ^
      p.conjugate.exponent.toReal) =
      descendantsENNAverage Q j (fun R =>
        cubeEuclideanWspFullENorm R s p.conjugate h.1.toField ^
          p.conjugate.exponent.toReal) := by
    unfold descendantsENNAverage
    congr 1
    apply Finset.sum_congr rfl
    intro R hR
    simp only [b, dif_pos hR]
  have hpositive := descendantsENNAverage_cubeEuclideanWspFullENorm_root_le
    Q j s p.conjugate h.1.toField
  have hB : (descendantsENNAverage Q j (fun R => b R ^
      p.conjugate.exponent.toReal)) ^ p.conjugate.exponent.toReal⁻¹ ≤
      (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1) := by
    rw [hbeq]
    calc
      (descendantsENNAverage Q j (fun R =>
          cubeEuclideanWspFullENorm R s p.conjugate h.1.toField ^
            p.conjugate.exponent.toReal)) ^ p.conjugate.exponent.toReal⁻¹ ≤
          (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1) *
            cubeEuclideanWspFullENorm Q s p.conjugate h.1.toField := hpositive
      _ ≤ (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1) := by
        simpa [mul_comm] using
          mul_le_mul_left h.2 ((ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1))
  have hholder := negativeLocalization_finite_holder_average D hD p a b
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1| =
        ENNReal.ofReal |descendantsAverage Q j (fun R =>
          if hR : R ∈ descendantsAtDepth Q j then
            cubeEuclideanNormalizedSmoothPairing
              (F.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtDepth hR))
              (h.1.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtDepth hR))
          else 0)| := by rw [hpart]
    _ ≤ descendantsENNAverage Q j (fun R =>
        ENNReal.ofReal |if hR : R ∈ descendantsAtDepth Q j then
          cubeEuclideanNormalizedSmoothPairing
            (F.restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))
            (h.1.restrictToSubcube
              (openCubeSet_subset_of_mem_descendantsAtDepth hR))
        else 0|) :=
      negativeLocalization_descendantsAverage_abs_le Q j _
    _ ≤ descendantsENNAverage Q j (fun R => a R * b R) := hab
    _ ≤ (descendantsENNAverage Q j (fun R => a R ^ p.exponent.toReal)) ^
          p.exponent.toReal⁻¹ *
        (descendantsENNAverage Q j (fun R => b R ^
          p.conjugate.exponent.toReal)) ^ p.conjugate.exponent.toReal⁻¹ := by
      simpa [D, descendantsENNAverage] using hholder
    _ ≤ (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1) *
        (descendantsENNAverage Q j (fun R => a R ^ p.exponent.toReal)) ^
          p.exponent.toReal⁻¹ := by
      simpa [mul_comm] using mul_le_mul_left hB
        ((descendantsENNAverage Q j (fun R => a R ^ p.exponent.toReal)) ^
          p.exponent.toReal⁻¹)
    _ = (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1) *
        (descendantsENNAverage Q j (fun R =>
          if hR : R ∈ descendantsAtDepth Q j then
            cubeEuclideanNegativeWspSmoothDualENorm R s p
              (F.restrictToSubcube
                (openCubeSet_subset_of_mem_descendantsAtDepth hR)) ^
                  p.exponent.toReal
          else 0)) ^ p.exponent.toReal⁻¹ := by
      congr 3
      unfold a
      funext R
      split_ifs
      · rfl
      · simp [ENNReal.zero_rpow_of_pos
          (ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne)]

end

end Homogenization
