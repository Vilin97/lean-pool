/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspCompletedDualGraph
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWspSmoothDual
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Finite smooth-dual extension to the completed fractional-Sobolev graph

On the finite locus of the smooth negative fractional-Sobolev dual norm, the
normalized pairing extends canonically from smooth tests to the completed
two-component graph.
-/

@[expose] public section

namespace Homogenization

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CubeEuclideanWspSmoothTest

private instance instSeminormedAddCommGroup {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) :
    SeminormedAddCommGroup (CubeEuclideanWspSmoothTest Q s p) :=
  SeminormedAddCommGroup.induced _ _ (graph (Q := Q) (s := s) (p := p))

private instance instNormedSpace {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) :
    NormedSpace ℝ (CubeEuclideanWspSmoothTest Q s p) :=
  NormedSpace.induced ℝ _ _ (graph (Q := Q) (s := s) (p := p))

private instance instCompletedGraphNormedAddCommGroup {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) :
    NormedAddCommGroup (CubeEuclideanWspCompletedDualGraph Q s p) := by
  unfold CubeEuclideanWspCompletedDualGraph completedGraphSubmodule
  infer_instance

private instance instCompletedGraphNormedSpace {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) :
    NormedSpace ℝ (CubeEuclideanWspCompletedDualGraph Q s p) := by
  unfold CubeEuclideanWspCompletedDualGraph completedGraphSubmodule
  infer_instance

private instance instCompletedGraphIsBoundedSMul {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) :
    IsBoundedSMul ℝ (CubeEuclideanWspCompletedDualGraph Q s p) :=
  NormedSpace.toIsBoundedSMul

private instance instCompletedGraphDualNormedAddCommGroup {d : ℕ} (Q : TriadicCube d)
    (s : FractionalOrder) (p : FiniteLpExponent) :
    NormedAddCommGroup (CubeEuclideanWspCompletedDualGraph Q s p →L[ℝ] ℝ) := by
  unfold CubeEuclideanWspCompletedDualGraph completedGraphSubmodule
  infer_instance

/-- The normalized smooth pairing, bundled as a real linear functional. -/
noncomputable def pairingLinearMap {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two) :
    CubeEuclideanWspSmoothTest Q s p.conjugate →ₗ[ℝ] ℝ where
  toFun := cubeEuclideanNormalizedSmoothPairing F
  map_add' h k := by
    unfold cubeEuclideanNormalizedSmoothPairing
    change (∫ x, vecDot (F.toField x) ((h + k).toField x)
      ∂normalizedCubeMeasure Q) =
      (∫ x, vecDot (F.toField x) (h.toField x) ∂normalizedCubeMeasure Q) +
        ∫ x, vecDot (F.toField x) (k.toField x) ∂normalizedCubeMeasure Q
    rw [toField_add]
    simp only [Pi.add_apply, vecDot_add_right]
    exact integral_add (cubeEuclideanNormalizedSmoothPairing_integrable F h)
      (cubeEuclideanNormalizedSmoothPairing_integrable F k)
  map_smul' c h := by
    unfold cubeEuclideanNormalizedSmoothPairing
    change (∫ x, vecDot (F.toField x) ((c • h).toField x)
      ∂normalizedCubeMeasure Q) =
      c • ∫ x, vecDot (F.toField x) (h.toField x) ∂normalizedCubeMeasure Q
    rw [toField_smul]
    simp only [Pi.smul_apply, vecDot_smul_right]
    exact integral_const_mul c _

private theorem fullENorm_smul {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent} (c : ℝ)
    (h : CubeEuclideanWspSmoothTest Q s p) :
    cubeEuclideanWspFullENorm Q s p (c • h).toField =
      ‖c‖ₑ * cubeEuclideanWspFullENorm Q s p h.toField := by
  rw [← graph_enorm_eq_cubeEuclideanWspFullENorm (c • h),
    ← graph_enorm_eq_cubeEuclideanWspFullENorm h, graph.map_smul, enorm_smul]

private theorem normalizedEuclideanLpENorm_eq_zero_of_fullENorm_eq_zero
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (f : Vec d → Vec d) (hf : cubeEuclideanWspFullENorm Q s p f = 0) :
    (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent f = 0 := by
  let L := (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent f
  let S := cubeEuclideanWspESeminorm Q s p f
  let W := cubeEuclideanWspScalePowerWeight Q s p
  let t := p.exponent.toReal
  have ht : 0 < t := ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
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

private theorem pairing_eq_zero_of_fullENorm_eq_zero {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder)
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    {p : FiniteLpExponent} (h : CubeEuclideanWspSmoothTest Q s p)
    (hh : cubeEuclideanWspFullENorm Q s p h.toField = 0) :
    cubeEuclideanNormalizedSmoothPairing F h = 0 := by
  have hLp : (cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm
      p.exponent h.toField = 0 :=
    normalizedEuclideanLpENorm_eq_zero_of_fullENorm_eq_zero Q s p h.toField hh
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
  have hp_ne_zero : p.exponent ≠ 0 := ne_of_gt (lt_trans zero_lt_one p.one_lt)
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

/-- The sharp homogeneous smooth-pairing estimate, obtained by rescaling a
finite-norm smooth test into the defining unit ball. -/
private theorem pairing_le_dual_mul_full {d : ℕ}
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
      apply pairing_eq_zero_of_fullENorm_eq_zero Q s F h
      simpa only [N] using hNzero
    simp [hzero, hNzero]
  · let r : ℝ := N.toReal⁻¹
    have hrpos : 0 < r := by
      dsimp [r]
      exact inv_pos.mpr (ENNReal.toReal_pos hNzero hNtop.ne)
    let hs := r • h
    have hhsnorm : cubeEuclideanWspFullENorm Q s p.conjugate hs.toField = 1 := by
      change cubeEuclideanWspFullENorm Q s p.conjugate (r • h).toField = 1
      rw [fullENorm_smul]
      change ‖r‖ₑ * N = 1
      have hr : ENNReal.ofReal r = N⁻¹ := by
        dsimp [r]
        rw [ENNReal.ofReal_inv_of_pos (ENNReal.toReal_pos hNzero hNtop.ne),
          ENNReal.ofReal_toReal hNtop.ne]
      rw [Real.enorm_eq_ofReal hrpos.le, hr,
        ENNReal.inv_mul_cancel hNzero hNtop.ne]
    let u : CubeEuclideanWspSmoothUnitTest Q s p.conjugate := ⟨hs, hhsnorm.le⟩
    have hu : ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| ≤ D := by
      rw [show D = cubeEuclideanNegativeWspSmoothDualENorm Q s p F by rfl,
        cubeEuclideanNegativeWspSmoothDualENorm]
      exact le_iSup (fun u : CubeEuclideanWspSmoothUnitTest Q s p.conjugate =>
        ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F u.1|) u
    have hpair : cubeEuclideanNormalizedSmoothPairing F hs =
        r * cubeEuclideanNormalizedSmoothPairing F h := by
      change pairingLinearMap F (r • h) = r * pairingLinearMap F h
      simp only [LinearMap.map_smul, smul_eq_mul]
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
      _ = N * ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F hs| := by rw [hscaled]
      _ ≤ N * D := mul_le_mul_right hu N
      _ = D * N := mul_comm _ _

/-- The canonical extension of the smooth normalized pairing to the completed
fractional-Sobolev graph. -/
noncomputable def completedPairingExtension {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (_hD : cubeEuclideanNegativeWspSmoothDualENorm Q s p F < ∞) :
    CubeEuclideanWspCompletedDualGraph Q s p.conjugate →L[ℝ] ℝ :=
  (pairingLinearMap F).extendOfNorm
    (graphToCompleted (Q := Q) (s := s) (p := p.conjugate))

private theorem smooth_fullENorm_lt_top {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    cubeEuclideanWspFullENorm Q s p h.toField < ∞ := by
  rw [← graph_enorm_eq_cubeEuclideanWspFullENorm h]
  exact enorm_lt_top

private theorem norm_graphToCompleted_eq_fullENorm_toReal {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    ‖graphToCompleted (Q := Q) (s := s) (p := p) h‖ =
      (cubeEuclideanWspFullENorm Q s p h.toField).toReal := by
  change ‖graph (Q := Q) (s := s) (p := p) h‖ = _
  rw [← toReal_enorm]
  exact congrArg ENNReal.toReal (graph_enorm_eq_cubeEuclideanWspFullENorm h)

private theorem pairing_norm_bound_of_dual_finite {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (hD : cubeEuclideanNegativeWspSmoothDualENorm Q s p F < ∞)
    (h : CubeEuclideanWspSmoothTest Q s p.conjugate) :
    ‖pairingLinearMap F h‖ ≤
      (cubeEuclideanNegativeWspSmoothDualENorm Q s p F).toReal *
        ‖graphToCompleted (Q := Q) (s := s) (p := p.conjugate) h‖ := by
  let D := cubeEuclideanNegativeWspSmoothDualENorm Q s p F
  let N := cubeEuclideanWspFullENorm Q s p.conjugate h.toField
  have hNtop : N < ∞ := smooth_fullENorm_lt_top h
  have hbound := pairing_le_dual_mul_full Q s p F h hNtop
  have hreal := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top hD.ne hNtop.ne)).mpr hbound
  change |cubeEuclideanNormalizedSmoothPairing F h| ≤ D.toReal *
    ‖graphToCompleted (Q := Q) (s := s) (p := p.conjugate) h‖
  rw [norm_graphToCompleted_eq_fullENorm_toReal]
  rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul] at hreal
  simpa only [D, N] using hreal

/-- On the finite dual-norm locus, the completed pairing agrees exactly with
the normalized smooth pairing on every smooth graph point. -/
theorem completedPairingExtension_apply_graphToCompleted {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (hD : cubeEuclideanNegativeWspSmoothDualENorm Q s p F < ∞)
    (h : CubeEuclideanWspSmoothTest Q s p.conjugate) :
    completedPairingExtension F hD
        (graphToCompleted (Q := Q) (s := s) (p := p.conjugate) h) =
      cubeEuclideanNormalizedSmoothPairing F h := by
  apply LinearMap.extendOfNorm_eq
    (denseRange_graphToCompleted (Q := Q) (s := s) (p := p.conjugate))
  refine ⟨(cubeEuclideanNegativeWspSmoothDualENorm Q s p F).toReal, ?_⟩
  exact pairing_norm_bound_of_dual_finite F hD

/-- The finite-locus extension is unique among continuous linear maps that
agree with the normalized pairing on the dense smooth graph. -/
theorem completedPairingExtension_unique {d : ℕ} {Q : TriadicCube d}
    {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (hD : cubeEuclideanNegativeWspSmoothDualENorm Q s p F < ∞)
    (G : CubeEuclideanWspCompletedDualGraph Q s p.conjugate →L[ℝ] ℝ)
    (hG : ∀ h : CubeEuclideanWspSmoothTest Q s p.conjugate,
      G (graphToCompleted (Q := Q) (s := s) (p := p.conjugate) h) =
        cubeEuclideanNormalizedSmoothPairing F h) :
    completedPairingExtension F hD = G := by
  apply LinearMap.extendOfNorm_unique
    (denseRange_graphToCompleted (Q := Q) (s := s) (p := p.conjugate))
    (cubeEuclideanNegativeWspSmoothDualENorm Q s p F).toReal
    (pairing_norm_bound_of_dual_finite F hD) G
  ext h
  simpa only [LinearMap.comp_apply] using! hG h

private theorem enorm_graphToCompleted_eq_fullENorm {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (h : CubeEuclideanWspSmoothTest Q s p) :
    ‖graphToCompleted (Q := Q) (s := s) (p := p) h‖ₑ =
      cubeEuclideanWspFullENorm Q s p h.toField := by
  change ‖graph (Q := Q) (s := s) (p := p) h‖ₑ = _
  exact graph_enorm_eq_cubeEuclideanWspFullENorm h

/-- On the finite locus, the extension has exactly the smooth negative dual
norm as its extended operator norm. -/
theorem enorm_completedPairingExtension_eq_negativeWspSmoothDualENorm {d : ℕ}
    {Q : TriadicCube d} {s : FractionalOrder} {p : FiniteLpExponent}
    (F : CubeEuclideanLpField Q FiniteLpExponent.two)
    (hD : cubeEuclideanNegativeWspSmoothDualENorm Q s p F < ∞) :
    ‖completedPairingExtension (Q := Q) (s := s) (p := p) F hD‖ₑ =
      cubeEuclideanNegativeWspSmoothDualENorm Q s p F := by
  let D := cubeEuclideanNegativeWspSmoothDualENorm Q s p F
  let E := completedPairingExtension (Q := Q) (s := s) (p := p) F hD
  have hupperReal : ‖E‖ ≤ D.toReal :=
    LinearMap.opNorm_extendOfNorm_le
      (denseRange_graphToCompleted (Q := Q) (s := s) (p := p.conjugate))
      ENNReal.toReal_nonneg (pairing_norm_bound_of_dual_finite F hD)
  have hupper : ‖E‖ₑ ≤ D := by
    rw [← ofReal_norm]
    exact (ENNReal.ofReal_le_iff_le_toReal hD.ne).mpr hupperReal
  have hlower : D ≤ ‖E‖ₑ := by
    rw [show D = cubeEuclideanNegativeWspSmoothDualENorm Q s p F by rfl,
      cubeEuclideanNegativeWspSmoothDualENorm]
    apply iSup_le
    rintro ⟨h, hh⟩
    calc
      ENNReal.ofReal |cubeEuclideanNormalizedSmoothPairing F h| =
          ‖E (graphToCompleted (Q := Q) (s := s) (p := p.conjugate) h)‖ₑ := by
        rw [show E = completedPairingExtension (Q := Q) (s := s) (p := p) F hD by rfl,
          completedPairingExtension_apply_graphToCompleted F hD h]
        exact (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ‖E‖ₑ * ‖graphToCompleted (Q := Q) (s := s) (p := p.conjugate) h‖ₑ :=
        E.le_opENorm _
      _ ≤ ‖E‖ₑ * 1 := by
        calc
          ‖E‖ₑ * ‖graphToCompleted (Q := Q) (s := s) (p := p.conjugate) h‖ₑ =
              ‖graphToCompleted (Q := Q) (s := s) (p := p.conjugate) h‖ₑ * ‖E‖ₑ :=
            mul_comm _ _
          _ ≤ 1 * ‖E‖ₑ := by
            apply mul_le_mul_left
            rw [enorm_graphToCompleted_eq_fullENorm]
            exact hh
          _ = ‖E‖ₑ * 1 := mul_comm _ _
      _ = ‖E‖ₑ := mul_one _
  exact hupper.antisymm hlower

end CubeEuclideanWspSmoothTest

end

end Homogenization
