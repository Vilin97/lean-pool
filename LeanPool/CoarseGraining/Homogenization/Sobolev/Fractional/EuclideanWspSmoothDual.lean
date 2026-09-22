/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWsp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth full-dual surface for Euclidean fractional Sobolev fields

The smooth-test supremum is retained as a `SmoothDualENorm`; no completion or
density assertion is made in this module.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- A globally smooth vector field used to test the full normalized fractional
Sobolev norm on a cube. -/
structure CubeEuclideanWspSmoothTest {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) where
  /-- The underlying globally defined vector field. -/
  toField : Vec d → Vec d
  /-- Global `C∞` regularity of the test field. -/
  contDiff : ContDiff ℝ (⊤ : ℕ∞) toField

namespace CubeEuclideanWspSmoothTest

instance {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder}
    {p : FiniteLpExponent} :
    CoeFun (CubeEuclideanWspSmoothTest Q s p) (fun _ => Vec d → Vec d) where
  coe h := h.toField

/-- A globally continuous vector field has finite Euclidean `L^q` norm on a
normalized cube for every exponent. -/
theorem euclideanMemLp_of_continuous {d : ℕ} (Q : TriadicCube d)
    (q : ℝ≥0∞) {f : Vec d → Vec d} (hf : Continuous f) :
    MemLp (fun x => HilbertVec.ofVec (f x)) q
      (normalizedCubeMeasure Q) := by
  have hfield : Continuous (fun x => HilbertVec.ofVec (f x)) :=
    (HilbertVec.ofVecL d).continuous.comp hf
  have hcompact : IsCompact (closure (cubeSet Q)) :=
    (isBounded_cubeSet Q).isCompact_closure
  rcases hcompact.bddAbove_image hfield.norm.continuousOn with ⟨C, hC⟩
  have hcube : ∀ᵐ x ∂normalizedCubeMeasure Q, x ∈ cubeSet Q := by
    have hrestrict :
        ∀ᵐ x ∂volume.restrict (cubeSet Q), x ∈ cubeSet Q :=
      ae_restrict_mem (measurableSet_cubeSet Q)
    simpa [normalizedCubeMeasure, cubeMeasure] using
      Measure.ae_smul_measure hrestrict
        (ENNReal.ofReal ((cubeVolume Q)⁻¹))
  exact MemLp.of_bound hfield.aestronglyMeasurable C <|
    hcube.mono fun x hx => hC ⟨x, subset_closure hx, rfl⟩

/-- A globally smooth test automatically supplies the Euclidean `L²`
certificate needed for pairing with the represented `L²` field. -/
theorem euclideanMemLp_two {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    MemLp (fun x => HilbertVec.ofVec (h.toField x)) 2
      (normalizedCubeMeasure Q) :=
  euclideanMemLp_of_continuous Q 2 h.contDiff.continuous

end CubeEuclideanWspSmoothTest

private theorem cubeEuclideanWspKernel_smul {d : ℕ}
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

private theorem normalizedEuclideanLpENorm_smul {d : ℕ}
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

private theorem cubeEuclideanWspESeminorm_smul {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (c : ℝ) (f : Vec d → Vec d) :
    cubeEuclideanWspESeminorm Q s p (fun x => c • f x) =
      ‖c‖ₑ * cubeEuclideanWspESeminorm Q s p f := by
  unfold cubeEuclideanWspESeminorm
  rw [cubeEuclideanWspKernel_smul]
  exact eLpNorm'_const_smul c (ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne)

private theorem cubeEuclideanWspFullENorm_smul {d : ℕ}
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
    normalizedEuclideanLpENorm_smul,
    cubeEuclideanWspESeminorm_smul]
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

private theorem normalizedEuclideanLpENorm_eq_zero_of_fullENorm_eq_zero
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (f : Vec d → Vec d) (hf : cubeEuclideanWspFullENorm Q s p f = 0) :
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
      p.exponent f = 0 := by
  let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
    p.exponent f
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

/-- A smooth test field in the unit ball of the full normalized fractional
Sobolev power norm. -/
abbrev CubeEuclideanWspSmoothUnitTest {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) :=
  {h : CubeEuclideanWspSmoothTest Q s p //
    cubeEuclideanWspFullENorm Q s p h.toField ≤ 1}

/-- The volume-normalized `L²` pairing of a represented field with a smooth
fractional Sobolev test field. -/
noncomputable def cubeEuclideanNormalizedSmoothPairing {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p) : ℝ :=
  ∫ x, vecDot (F.toField x) (h.toField x) ∂normalizedCubeMeasure Q

private def CubeEuclideanWspSmoothTest.smul {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (c : ℝ) (h : CubeEuclideanWspSmoothTest Q s p) :
    CubeEuclideanWspSmoothTest Q s p where
  toField x := c • h.toField x
  contDiff := h.contDiff.const_smul c

private theorem cubeEuclideanNormalizedSmoothPairing_smul_right {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p) (c : ℝ) :
    cubeEuclideanNormalizedSmoothPairing F (h.smul c) =
      c * cubeEuclideanNormalizedSmoothPairing F h := by
  unfold cubeEuclideanNormalizedSmoothPairing CubeEuclideanWspSmoothTest.smul
  simp_rw [vecDot_smul_right]
  exact MeasureTheory.integral_const_mul c _

theorem cubeEuclideanNormalizedSmoothPairing_integrable {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (h : CubeEuclideanWspSmoothTest Q s p) :
    Integrable (fun x => vecDot (F.toField x) (h.toField x))
      (normalizedCubeMeasure Q) := by
  have hF : ∀ i : Fin d,
      MemLp (fun x => F.toField x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    simpa only [FiniteLpExponent.two_exponent, HilbertVec.ofVec,
      PiLp.toLp_apply] using F.euclideanMemLp.eval_piLp i
  have hh : ∀ i : Fin d,
      MemLp (fun x => h.toField x i) 2 (normalizedCubeMeasure Q) := by
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
      h.euclideanMemLp_two.eval_piLp i
  simpa only [vecDot] using!
    integrable_finsetSum Finset.univ fun i _ => (hF i).integrable_mul (hh i)

private theorem cubeEuclideanNormalizedSmoothPairing_eq_zero_of_fullENorm_eq_zero
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    {p : FiniteLpExponent} (h : CubeEuclideanWspSmoothTest Q s p)
    (hh : cubeEuclideanWspFullENorm Q s p h.toField = 0) :
    cubeEuclideanNormalizedSmoothPairing F h = 0 := by
  have hLp : (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
      p.exponent h.toField = 0 :=
    normalizedEuclideanLpENorm_eq_zero_of_fullENorm_eq_zero
      Q s p h.toField hh
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
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [hfield_zero] with x hx
  simp [hx, vecDot]

/-- The extended norm obtained by taking the supremum of normalized pairings
over the smooth unit ball in the conjugate full fractional Sobolev norm. -/
noncomputable def cubeEuclideanNegativeWspSmoothDualENorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) : ℝ≥0∞ :=
  ⨆ h : CubeEuclideanWspSmoothUnitTest Q s p.conjugate,
    ENNReal.ofReal
      |cubeEuclideanNormalizedSmoothPairing F h.1|

/-- The normalized pairing is bounded by the conjugate full fractional
Sobolev power norm on every globally smooth test field. -/
def CubeEuclideanSmoothPairingIsBounded {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) : Prop :=
  ∃ C : ℝ≥0∞, C < ∞ ∧
    ∀ h : CubeEuclideanWspSmoothTest Q s p.conjugate,
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
        C * cubeEuclideanWspFullENorm Q s p.conjugate h.toField

theorem cubeEuclideanNegativeWspSmoothDualENorm_lt_top_iff {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    cubeEuclideanNegativeWspSmoothDualENorm Q s p F < ∞ ↔
      CubeEuclideanSmoothPairingIsBounded Q s p F := by
  set D := cubeEuclideanNegativeWspSmoothDualENorm Q s p F
  constructor
  · intro hD
    refine ⟨D + 1, ENNReal.add_lt_top.2 ⟨hD, ENNReal.one_lt_top⟩, ?_⟩
    intro h
    set N := cubeEuclideanWspFullENorm Q s p.conjugate h.toField
    by_cases hNtop : N = ∞
    · simp [hNtop]
    by_cases hNzero : N = 0
    · have hzero : cubeEuclideanNormalizedSmoothPairing F h = 0 := by
        apply cubeEuclideanNormalizedSmoothPairing_eq_zero_of_fullENorm_eq_zero
        simpa only [N] using hNzero
      simp [hzero, hNzero]
    · let r : ℝ := N.toReal⁻¹
      have hrpos : 0 < r := by
        dsimp [r]
        exact inv_pos.mpr (ENNReal.toReal_pos hNzero hNtop)
      let hs := h.smul r
      have hhsnorm : cubeEuclideanWspFullENorm Q s p.conjugate hs.toField = 1 := by
        change cubeEuclideanWspFullENorm Q s p.conjugate
          (fun x => r • h.toField x) = 1
        rw [cubeEuclideanWspFullENorm_smul]
        change ‖r‖ₑ * N = 1
        rw [Real.enorm_eq_ofReal hrpos.le, show ENNReal.ofReal r = N⁻¹ by
          dsimp [r]
          rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hNzero hNtop),
            ENNReal.ofReal_toReal hNtop], ENNReal.inv_mul_cancel hNzero hNtop]
      let u : CubeEuclideanWspSmoothUnitTest Q s p.conjugate :=
        ⟨hs, hhsnorm.le⟩
      have hu : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| ≤ D := by
        rw [show D = cubeEuclideanNegativeWspSmoothDualENorm Q s p F by rfl,
          cubeEuclideanNegativeWspSmoothDualENorm]
        exact le_iSup (fun u : CubeEuclideanWspSmoothUnitTest Q s p.conjugate =>
          ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F u.1|) u
      have hpair : cubeEuclideanNormalizedSmoothPairing F hs =
          r * cubeEuclideanNormalizedSmoothPairing F h := by
        exact cubeEuclideanNormalizedSmoothPairing_smul_right F h r
      have hscaled : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| =
          N⁻¹ * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| := by
        rw [hpair, abs_mul, abs_of_pos hrpos, ENNReal.ofReal_mul hrpos.le]
        congr 1
        dsimp [r]
        rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hNzero hNtop),
          ENNReal.ofReal_toReal hNtop]
      calc
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| =
            N * (N⁻¹ * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h|) := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hNzero hNtop, one_mul]
        _ = N * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| := by
          rw [hscaled]
        _ ≤ N * D := mul_le_mul_right hu N
        _ ≤ (D + 1) * N := by
          rw [mul_comm N D]
          exact mul_le_mul_left (self_le_add_right D 1) N
  · rintro ⟨C, hCtop, hC⟩
    change cubeEuclideanNegativeWspSmoothDualENorm Q s p F < ∞
    rw [cubeEuclideanNegativeWspSmoothDualENorm]
    apply lt_of_le_of_lt (iSup_le fun h => ?_) hCtop
    calc
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h.1| ≤
          C * cubeEuclideanWspFullENorm Q s p.conjugate h.1.toField := hC h.1
      _ ≤ C * 1 := mul_le_mul_right h.2 C
      _ = C := mul_one C

end

end Homogenization
