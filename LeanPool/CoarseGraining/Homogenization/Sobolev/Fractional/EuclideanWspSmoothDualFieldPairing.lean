/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothDensity
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspCompletedDualExtension
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.FiniteLpBelowTwo

/-!
# Smooth-dual pairing with actual fractional Sobolev fields

This module closes the smooth-test dual pairing against an actual fractional
Sobolev field which also has the required `L²` representative.
-/

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

private instance instFieldPairingFactOneLe (p : FiniteLpExponent) :
    Fact (1 ≤ p.exponent) :=
  ⟨p.one_lt.le⟩

/-- The ambient full-norm graph point of an actual fractional field. -/
private noncomputable def cubeEuclideanWspGraphPointOfField {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) : CubeEuclideanWspGraphAmbient Q p :=
  WithLp.toLp p.exponent fun b =>
    match b with
    | false =>
      cubeEuclideanWspGraphFieldScale Q s •
        F.euclideanMemLp.toLp (fun x => HilbertVec.ofVec (F.toField x))
    | true =>
      F.euclideanMemWsp.toLp (cubeEuclideanWspKernel s p F.toField)

private theorem enorm_cubeEuclideanWspGraphPointOfField {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanWspField Q s p) :
    ‖cubeEuclideanWspGraphPointOfField F‖ₑ =
      cubeEuclideanWspFullENorm Q s p F.toField := by
  change ‖WithLp.toLp p.exponent (fun b : Bool =>
      match b with
      | false => show CubeEuclideanWspGraphComponent Q p false from
        cubeEuclideanWspGraphFieldScale Q s •
          F.euclideanMemLp.toLp (fun x => HilbertVec.ofVec (F.toField x))
      | true => show CubeEuclideanWspGraphComponent Q p true from
        F.euclideanMemWsp.toLp (cubeEuclideanWspKernel s p F.toField))‖ₑ = _
  rw [enorm_eq_nnnorm, PiLp.nnnorm_eq_sum p.lt_top.ne]
  rw [one_div, ENNReal.coe_rpow_of_nonneg _ (inv_nonneg.mpr ENNReal.toReal_nonneg),
    ENNReal.ofNNReal_finsetSum]
  simp_rw [ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg]
  rw [Fintype.sum_bool]
  change (‖F.euclideanMemWsp.toLp (cubeEuclideanWspKernel s p F.toField)‖ₑ ^
      p.exponent.toReal +
      ‖cubeEuclideanWspGraphFieldScale Q s •
        F.euclideanMemLp.toLp (fun x => HilbertVec.ofVec (F.toField x))‖ₑ ^
          p.exponent.toReal) ^ p.exponent.toReal⁻¹ = _
  rw [enorm_smul, Lp.enorm_toLp F.euclideanMemWsp, Lp.enorm_toLp F.euclideanMemLp]
  have hlp : eLpNorm (fun x => HilbertVec.ofVec (F.toField x)) p.exponent
      (normalizedCubeMeasure Q) =
      (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
        p.exponent F.toField := by
    unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
      BoundedMeasurableDomain.normalizedLpENorm
    rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure]
    simp only [euclideanNorm_eq_norm_ofVec, eLpNorm_norm]
  rw [hlp]
  change (cubeEuclideanWspESeminorm Q s p F.toField ^ p.exponent.toReal +
      (‖cubeEuclideanWspGraphFieldScale Q s‖ₑ *
        (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
          p.exponent F.toField) ^ p.exponent.toReal) ^ p.exponent.toReal⁻¹ = _
  have hscale : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hweight : ‖cubeEuclideanWspGraphFieldScale Q s‖ₑ ^ p.exponent.toReal =
      cubeEuclideanWspScalePowerWeight Q s p := by
    unfold cubeEuclideanWspGraphFieldScale cubeEuclideanWspScalePowerWeight
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg hscale.le _),
      ← ENNReal.ofReal_rpow_of_pos hscale]
    rw [← ENNReal.rpow_mul]
  rw [ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, hweight]
  unfold cubeEuclideanWspFullENorm
  rw [add_comm]

private theorem cubeEuclideanWspKernel_sub {d : ℕ} (s : FractionalOrder)
    (p : FiniteLpExponent) (F G : Vec d → Vec d) :
    cubeEuclideanWspKernel s p (fun x => F x - G x) =
      fun z => cubeEuclideanWspKernel s p F z - cubeEuclideanWspKernel s p G z := by
  funext z
  rw [cubeEuclideanWspKernel_apply, cubeEuclideanWspKernel_apply,
    cubeEuclideanWspKernel_apply]
  change _ • (HilbertVec.ofVecL d)
    ((F z.1 - G z.1) - (F z.2 - G z.2)) = _
  rw [sub_sub_sub_comm, (HilbertVec.ofVecL d).map_sub, smul_sub]
  simp only [HilbertVec.ofVecL_apply]

private noncomputable def cubeEuclideanWspFieldSub {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F G : CubeEuclideanWspField Q s p) : CubeEuclideanWspField Q s p where
  toField := fun x => F.toField x - G.toField x
  euclideanMemLp := by
    simpa only [HilbertVec.ofVecL_apply] using! F.euclideanMemLp.sub G.euclideanMemLp
  euclideanMemWsp := by
    change MemLp (cubeEuclideanWspKernel s p
      (fun x => F.toField x - G.toField x)) p.exponent
      (Gagliardo.gagliardoCubeMeasure Q)
    rw [cubeEuclideanWspKernel_sub]
    simpa only [Pi.sub_apply] using! F.euclideanMemWsp.sub G.euclideanMemWsp

private theorem cubeEuclideanWspGraphPointOfField_sub {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F G : CubeEuclideanWspField Q s p) :
    cubeEuclideanWspGraphPointOfField (cubeEuclideanWspFieldSub F G) =
      cubeEuclideanWspGraphPointOfField F - cubeEuclideanWspGraphPointOfField G := by
  apply PiLp.ext
  intro b
  cases b
  · unfold cubeEuclideanWspGraphPointOfField
    rw [WithLp.ofLp_sub, Pi.sub_apply]
    change cubeEuclideanWspGraphFieldScale Q s •
        (cubeEuclideanWspFieldSub F G).euclideanMemLp.toLp
          (fun x => HilbertVec.ofVec ((cubeEuclideanWspFieldSub F G).toField x)) =
      cubeEuclideanWspGraphFieldScale Q s • F.euclideanMemLp.toLp
          (fun x => HilbertVec.ofVec (F.toField x)) -
        cubeEuclideanWspGraphFieldScale Q s • G.euclideanMemLp.toLp
          (fun x => HilbertVec.ofVec (G.toField x))
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (cubeEuclideanWspFieldSub F G).euclideanMemLp,
      MemLp.coeFn_toLp F.euclideanMemLp, MemLp.coeFn_toLp G.euclideanMemLp,
      Lp.coeFn_sub
        (cubeEuclideanWspGraphFieldScale Q s • F.euclideanMemLp.toLp
          (fun x => HilbertVec.ofVec (F.toField x)))
        (cubeEuclideanWspGraphFieldScale Q s • G.euclideanMemLp.toLp
          (fun x => HilbertVec.ofVec (G.toField x))),
      Lp.coeFn_smul (cubeEuclideanWspGraphFieldScale Q s)
        ((cubeEuclideanWspFieldSub F G).euclideanMemLp.toLp
          (fun x => HilbertVec.ofVec ((cubeEuclideanWspFieldSub F G).toField x))),
      Lp.coeFn_smul (cubeEuclideanWspGraphFieldScale Q s)
        (F.euclideanMemLp.toLp (fun x => HilbertVec.ofVec (F.toField x))),
      Lp.coeFn_smul (cubeEuclideanWspGraphFieldScale Q s)
        (G.euclideanMemLp.toLp (fun x => HilbertVec.ofVec (G.toField x)))] with
        x hFG hF hG hsub hscaleFG hscaleF hscaleG
    rw [hsub]
    rw [Pi.sub_apply, hscaleFG, hscaleF, hscaleG]
    simp only [Pi.smul_apply]
    rw [hFG, hF, hG]
    change cubeEuclideanWspGraphFieldScale Q s • (HilbertVec.ofVecL d)
      (F.toField x - G.toField x) = _
    rw [(HilbertVec.ofVecL d).map_sub, smul_sub]
    rfl
  · unfold cubeEuclideanWspGraphPointOfField
    rw [WithLp.ofLp_sub, Pi.sub_apply]
    change (cubeEuclideanWspFieldSub F G).euclideanMemWsp.toLp
        (cubeEuclideanWspKernel s p (cubeEuclideanWspFieldSub F G).toField) =
      F.euclideanMemWsp.toLp (cubeEuclideanWspKernel s p F.toField) -
        G.euclideanMemWsp.toLp (cubeEuclideanWspKernel s p G.toField)
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (cubeEuclideanWspFieldSub F G).euclideanMemWsp,
      MemLp.coeFn_toLp F.euclideanMemWsp, MemLp.coeFn_toLp G.euclideanMemWsp,
      Lp.coeFn_sub
        (F.euclideanMemWsp.toLp (cubeEuclideanWspKernel s p F.toField))
        (G.euclideanMemWsp.toLp (cubeEuclideanWspKernel s p G.toField))] with z hFG hF hG hsub
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hFG, hF, hG]
    exact congrFun (cubeEuclideanWspKernel_sub s p F.toField G.toField) z

/-- The literal normalized-cube pairing of an `L²` field with an actual
fractional Sobolev field. -/
noncomputable def cubeEuclideanNormalizedFieldPairing {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (G : CubeEuclideanWspL2Field Q s p) : ℝ :=
  ∫ x, vecDot (F.toField x) (G.toField x) ∂normalizedCubeMeasure Q

private theorem cubeEuclideanNormalizedFieldPairing_integrable {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (G : CubeEuclideanWspL2Field Q s p) :
    Integrable (fun x => vecDot (F.toField x) (G.toField x))
      (normalizedCubeMeasure Q) := by
  have hF : ∀ i : Fin d, MemLp (fun x => F.toField x i) 2
      (normalizedCubeMeasure Q) := by
    intro i
    simpa only [FiniteLpExponent.two_exponent, HilbertVec.ofVec,
      PiLp.toLp_apply] using F.euclideanMemLp.eval_piLp i
  have hG : ∀ i : Fin d, MemLp (fun x => G.toField x i) 2
      (normalizedCubeMeasure Q) := by
    intro i
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using G.euclideanMemL2.eval_piLp i
  simpa only [vecDot] using!
    integrable_finsetSum Finset.univ fun i _ => (hF i).integrable_mul (hG i)

private theorem fieldPairing_sub_smoothPairing {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (G : CubeEuclideanWspL2Field Q s p)
    (h : CubeEuclideanWspSmoothTest Q s p) :
    cubeEuclideanNormalizedFieldPairing F G -
        cubeEuclideanNormalizedSmoothPairing F h =
      ∫ x, vecDot (F.toField x) (G.toField x - h.toField x)
        ∂normalizedCubeMeasure Q := by
  unfold cubeEuclideanNormalizedFieldPairing cubeEuclideanNormalizedSmoothPairing
  rw [← MeasureTheory.integral_sub
    (cubeEuclideanNormalizedFieldPairing_integrable F G)
    (cubeEuclideanNormalizedSmoothPairing_integrable F h)]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  simp only [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]

private theorem abs_fieldPairing_sub_smoothPairing_le_l2 {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (G : CubeEuclideanWspL2Field Q s p)
    (h : CubeEuclideanWspSmoothTest Q s p) :
    |cubeEuclideanNormalizedFieldPairing F G -
        cubeEuclideanNormalizedSmoothPairing F h| ≤
      (eLpNorm (fun x => HilbertVec.ofVec (F.toField x)) 2
        (normalizedCubeMeasure Q)).toReal *
      (eLpNorm (fun x => HilbertVec.ofVec (G.toField x - h.toField x)) 2
        (normalizedCubeMeasure Q)).toReal := by
  rw [fieldPairing_sub_smoothPairing]
  apply CubeCalderonZygmund.INTERNAL.abs_integral_vecDot_le_eLpNorm_toReal_mul
  · simpa only [FiniteLpExponent.two_exponent] using F.euclideanMemLp
  · simpa only [HilbertVec.ofVecL_apply, sub_eq_add_neg, add_comm] using!
      G.euclideanMemL2.sub h.euclideanMemLp_two

private theorem ennreal_abs_smoothPairing_le_negativeDual_mul_full {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (hD : cubeEuclideanNegativeWspSmoothDualENorm Q s p F < ∞)
    (h : CubeEuclideanWspSmoothTest Q s p.conjugate) :
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| ≤
      cubeEuclideanNegativeWspSmoothDualENorm Q s p F *
        cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
  let E := CubeEuclideanWspSmoothTest.completedPairingExtension F hD
  calc
    ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| =
        ‖E (CubeEuclideanWspSmoothTest.graphToCompleted h)‖ₑ := by
      rw [show E = CubeEuclideanWspSmoothTest.completedPairingExtension F hD by rfl,
        CubeEuclideanWspSmoothTest.completedPairingExtension_apply_graphToCompleted F hD h]
      exact (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ‖E‖ₑ * ‖CubeEuclideanWspSmoothTest.graphToCompleted h‖ₑ :=
      E.le_opENorm _
    _ = cubeEuclideanNegativeWspSmoothDualENorm Q s p F *
        cubeEuclideanWspFullENorm Q s p.conjugate h.toField := by
      rw [show E = CubeEuclideanWspSmoothTest.completedPairingExtension F hD by rfl,
        CubeEuclideanWspSmoothTest.enorm_completedPairingExtension_eq_negativeWspSmoothDualENorm F hD]
      exact congrArg (fun x : ℝ≥0∞ =>
        cubeEuclideanNegativeWspSmoothDualENorm Q s p F * x)
        (CubeEuclideanWspSmoothTest.graph_enorm_eq_cubeEuclideanWspFullENorm h)

/-- A zero full fractional-Sobolev norm forces the literal pairing with every
`L²` datum to vanish. -/
private theorem cubeEuclideanNormalizedFieldPairing_eq_zero_of_fullENorm_eq_zero
    {d : ℕ} {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (G : CubeEuclideanWspL2Field Q s p)
    (hG : cubeEuclideanWspFullENorm Q s p G.toField = 0) :
    cubeEuclideanNormalizedFieldPairing F G = 0 := by
  have hLp : (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
      p.exponent G.toField = 0 := by
    unfold cubeEuclideanWspFullENorm at hG
    let W := cubeEuclideanWspScalePowerWeight Q s p
    let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
      p.exponent G.toField
    let S := cubeEuclideanWspESeminorm Q s p G.toField
    let t := p.exponent.toReal
    have ht : 0 < t := ENNReal.toReal_pos
      (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
    have hW : W ≠ 0 := by
      dsimp only [W]
      unfold cubeEuclideanWspScalePowerWeight
      have hscale : 0 < cubeScaleFactor Q := by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
      exact ne_of_gt (ENNReal.rpow_pos
        (ENNReal.ofReal_pos.mpr hscale) ENNReal.ofReal_ne_top)
    have hbase : W * L ^ t + S ^ t = 0 := by
      rw [← ENNReal.rpow_eq_zero_iff_of_pos (inv_pos.mpr ht)]
      simpa only [W, L, S, t] using hG
    have hpow : L ^ t = 0 :=
      (mul_eq_zero.mp (add_eq_zero.mp hbase).1).resolve_left hW
    exact (ENNReal.rpow_eq_zero_iff_of_pos ht).mp hpow
  have hLp' : eLpNorm (fun x => HilbertVec.ofVec (G.toField x)) p.exponent
      (normalizedCubeMeasure Q) = 0 := by
    simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
      BoundedMeasurableDomain.normalizedLpENorm,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      euclideanNorm_eq_norm_ofVec, eLpNorm_norm] using hLp
  have hzero : (fun x => HilbertVec.ofVec (G.toField x)) =ᵐ[
      normalizedCubeMeasure Q] 0 :=
    (eLpNorm_eq_zero_iff G.euclideanMemLp.aestronglyMeasurable
      (ne_of_gt (lt_trans zero_lt_one p.one_lt))).mp hLp'
  unfold cubeEuclideanNormalizedFieldPairing
  apply MeasureTheory.integral_eq_zero_of_ae
  filter_upwards [hzero] with x hx
  have hx' : G.toField x = 0 := by
    have h := congrArg (HilbertVec.continuousLinearEquivVec d) hx
    simpa only [HilbertVec.continuousLinearEquivVec_apply] using! h
  rw [hx']
  simpa only [Pi.zero_apply] using (vecDot_zero_right (F.toField x))

private theorem smooth_fullENorm_le_full_add_error {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (G : CubeEuclideanWspL2Field Q s p)
    (h : CubeEuclideanWspSmoothTest Q s p) :
    cubeEuclideanWspFullENorm Q s p h.toField ≤
      cubeEuclideanWspFullENorm Q s p G.toField +
        cubeEuclideanWspFullENorm Q s p (fun x => h.toField x - G.toField x) := by
  let H := h.toCubeEuclideanWspField
  let K := cubeEuclideanWspFieldSub H G.toCubeEuclideanWspField
  have hsplit : cubeEuclideanWspGraphPointOfField H =
      cubeEuclideanWspGraphPointOfField K +
        cubeEuclideanWspGraphPointOfField G.toCubeEuclideanWspField := by
    rw [cubeEuclideanWspGraphPointOfField_sub]
    abel
  change cubeEuclideanWspFullENorm Q s p H.toField ≤
    cubeEuclideanWspFullENorm Q s p G.toField +
      cubeEuclideanWspFullENorm Q s p K.toField
  calc
    cubeEuclideanWspFullENorm Q s p H.toField =
        ‖cubeEuclideanWspGraphPointOfField H‖ₑ :=
      (enorm_cubeEuclideanWspGraphPointOfField H).symm
    _ = ‖cubeEuclideanWspGraphPointOfField K +
        cubeEuclideanWspGraphPointOfField G.toCubeEuclideanWspField‖ₑ := by
      rw [← hsplit]
    _ ≤ ‖cubeEuclideanWspGraphPointOfField K‖ₑ +
        ‖cubeEuclideanWspGraphPointOfField G.toCubeEuclideanWspField‖ₑ :=
      enorm_add_le _ _
    _ = cubeEuclideanWspFullENorm Q s p K.toField +
        cubeEuclideanWspFullENorm Q s p G.toField := by
      rw [enorm_cubeEuclideanWspGraphPointOfField,
        enorm_cubeEuclideanWspGraphPointOfField]
    _ = cubeEuclideanWspFullENorm Q s p G.toField +
        cubeEuclideanWspFullENorm Q s p K.toField := add_comm _ _

/-- The literal normalized-cube pairing is controlled by the smooth negative
fractional-Sobolev dual norm. -/
theorem ennreal_ofReal_abs_cubeEuclideanNormalizedFieldPairing_le {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (G : CubeEuclideanWspL2Field Q s p.conjugate) :
    ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G| ≤
      cubeEuclideanNegativeWspSmoothDualENorm Q s p F *
        cubeEuclideanWspFullENorm Q s p.conjugate G.toField := by
  let D := cubeEuclideanNegativeWspSmoothDualENorm Q s p F
  let N := cubeEuclideanWspFullENorm Q s p.conjugate G.toField
  change ENNReal.ofReal |cubeEuclideanNormalizedFieldPairing F G| ≤ D * N
  by_cases hD : D < ∞
  · have hN : N < ∞ := G.toCubeEuclideanWspField.fullENorm_lt_top
    apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top hD.ne hN.ne)).mp
    rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul]
    let A := (eLpNorm (fun x => HilbertVec.ofVec (F.toField x)) 2
      (normalizedCubeMeasure Q)).toReal
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    let delta := epsilon / (A + D.toReal + 1)
    have hdenom : 0 < A + D.toReal + 1 := by positivity
    have hdelta : 0 < delta := div_pos hepsilon hdenom
    obtain ⟨h, hfull, hl2⟩ :=
      exists_cubeEuclideanWspSmoothTest_fullENorm_and_l2_sub_lt G
        (epsilon := ENNReal.ofReal delta) (ENNReal.ofReal_pos.mpr hdelta)
    have hfull_top : cubeEuclideanWspFullENorm Q s p.conjugate
        (fun x => h.toField x - G.toField x) < ∞ :=
      hfull.trans (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
    have hfull_real :
        (cubeEuclideanWspFullENorm Q s p.conjugate
          (fun x => h.toField x - G.toField x)).toReal < delta := by
      have := (ENNReal.toReal_lt_toReal hfull_top.ne ENNReal.ofReal_ne_top).mpr hfull
      simpa only [ENNReal.toReal_ofReal hdelta.le] using this
    have hl2_real :
        (eLpNorm (fun x => HilbertVec.ofVec (h.toField x - G.toField x)) 2
          (normalizedCubeMeasure Q)).toReal < delta := by
      have hl2_top : eLpNorm (fun x => HilbertVec.ofVec (h.toField x - G.toField x)) 2
          (normalizedCubeMeasure Q) < ∞ :=
        hl2.trans (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top)
      have := (ENNReal.toReal_lt_toReal hl2_top.ne ENNReal.ofReal_ne_top).mpr hl2
      simpa only [ENNReal.toReal_ofReal hdelta.le] using this
    have hnorm : cubeEuclideanWspFullENorm Q s p.conjugate h.toField ≤
        N + cubeEuclideanWspFullENorm Q s p.conjugate
          (fun x => h.toField x - G.toField x) :=
      smooth_fullENorm_le_full_add_error G h
    have hhtop : cubeEuclideanWspFullENorm Q s p.conjugate h.toField < ∞ :=
      h.toCubeEuclideanWspField.fullENorm_lt_top
    have hnorm_real : (cubeEuclideanWspFullENorm Q s p.conjugate h.toField).toReal ≤
        N.toReal + (cubeEuclideanWspFullENorm Q s p.conjugate
          (fun x => h.toField x - G.toField x)).toReal := by
      have := (ENNReal.toReal_le_toReal hhtop.ne
        (ENNReal.add_ne_top.mpr ⟨hN.ne, hfull_top.ne⟩)).mpr hnorm
      simpa only [ENNReal.toReal_add hN.ne hfull_top.ne] using this
    have hsmooth : |cubeEuclideanNormalizedSmoothPairing F h| ≤
        D.toReal * (cubeEuclideanWspFullENorm Q s p.conjugate h.toField).toReal := by
      have hbound := ennreal_abs_smoothPairing_le_negativeDual_mul_full F hD h
      have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
        (ENNReal.mul_ne_top hD.ne hhtop.ne)).mpr hbound
      simpa only [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul] using this
    have hl2_eq :
        eLpNorm (fun x => HilbertVec.ofVec (G.toField x - h.toField x)) 2
          (normalizedCubeMeasure Q) =
        eLpNorm (fun x => HilbertVec.ofVec (h.toField x - G.toField x)) 2
          (normalizedCubeMeasure Q) := by
      have hfun : (fun x => HilbertVec.ofVec (G.toField x - h.toField x)) =
          (fun x => -HilbertVec.ofVec (h.toField x - G.toField x)) := by
        funext x
        rw [show G.toField x - h.toField x = -(h.toField x - G.toField x) by abel,
          ← HilbertVec.ofVecL_apply]
        exact (HilbertVec.ofVecL d).map_neg _
      rw [hfun]
      change eLpNorm (-(fun x => HilbertVec.ofVec (h.toField x - G.toField x))) 2
        (normalizedCubeMeasure Q) = _
      rw [eLpNorm_neg]
    have hdifference : |cubeEuclideanNormalizedFieldPairing F G -
        cubeEuclideanNormalizedSmoothPairing F h| ≤
        A * (eLpNorm (fun x => HilbertVec.ofVec (h.toField x - G.toField x)) 2
          (normalizedCubeMeasure Q)).toReal := by
      simpa only [A, hl2_eq] using abs_fieldPairing_sub_smoothPairing_le_l2 F G h
    calc
      |cubeEuclideanNormalizedFieldPairing F G| ≤
          |cubeEuclideanNormalizedSmoothPairing F h| +
            |cubeEuclideanNormalizedFieldPairing F G -
              cubeEuclideanNormalizedSmoothPairing F h| := by
        calc
          |cubeEuclideanNormalizedFieldPairing F G| =
              |cubeEuclideanNormalizedSmoothPairing F h +
                (cubeEuclideanNormalizedFieldPairing F G -
                  cubeEuclideanNormalizedSmoothPairing F h)| := by
                    congr 1
                    ring
          _ ≤ _ := by
            exact abs_add_le _ _
      _ ≤ D.toReal * (cubeEuclideanWspFullENorm Q s p.conjugate h.toField).toReal +
          A * (eLpNorm (fun x => HilbertVec.ofVec (h.toField x - G.toField x)) 2
            (normalizedCubeMeasure Q)).toReal := add_le_add hsmooth hdifference
      _ ≤ D.toReal * (N.toReal + delta) + A * delta := by
        apply add_le_add
        · gcongr
          exact hnorm_real.trans (add_le_add_right hfull_real.le N.toReal)
        · gcongr
      _ = D.toReal * N.toReal + (D.toReal + A) * delta := by ring
      _ ≤ D.toReal * N.toReal + epsilon := by
        gcongr
        rw [show (D.toReal + A) * delta =
          (epsilon * (D.toReal + A)) / (A + D.toReal + 1) by
            dsimp only [delta]
            ring]
        apply (div_le_iff₀ hdenom).mpr
        apply mul_le_mul_of_nonneg_left
        linarith
        exact hepsilon.le
  · have hDtop : D = ∞ := ((not_lt.mp hD).antisymm le_top).symm
    by_cases hNzero : N = 0
    · rw [hDtop, hNzero]
      rw [cubeEuclideanNormalizedFieldPairing_eq_zero_of_fullENorm_eq_zero F G hNzero]
      simp
    · rw [hDtop, ENNReal.top_mul hNzero]
      exact le_top

end

end Homogenization
