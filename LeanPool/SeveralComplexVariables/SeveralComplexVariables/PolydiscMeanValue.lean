/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.MeanValue
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CauchyIntegral

/-!
# Torus and volume mean values on polydiscs

The fixed-radius torus average of a holomorphic function equals its value at the center, for
every valid radius. This is the plain Bochner-integral average, with no residual Jacobian
factor: the complex contour normalization in `torusIntegral` cancels exactly at the center.
Averaging common complex rotations and applying Fubini also gives the volume mean-value formula
on equal-radius polydiscs. This formula supports the local `Lp` estimate on holomorphic function
spaces. Arbitrary finite coordinate types, including the empty type, are allowed in the volume
formula.

## Main results

* `torusAverage_eq_center`: At the center of a polydisc, the fixed-radius torus average is a plain
  Bochner-integral average of the function over the angle cube, with no Jacobian residue.
* `integral_closedBall_zero_eq_volume_smul`: Averaging a holomorphic function over an equal-radius
  polydisc centered at zero returns its center value times the volume.
* `integral_closedBall_eq_volume_smul`: The volume mean-value formula on an equal-radius polydisc
  with arbitrary center.
-/

public section

open Complex Filter Function MeasureTheory Metric Set
open scoped ENNReal NNReal Real Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- At the center of a polydisc, the fixed-radius torus average is a plain Bochner-integral average
of the function over the angle cube, with no Jacobian residue. -/
theorem torusAverage_eq_center {d : ℕ} {f : (Fin d → ℂ) → E} {c : Fin d → ℂ} {R : Fin d → ℝ}
    (hR : ∀ i, 0 < R i)
    (hfc : ContinuousOn f (closedPolydisc c R))
    (hfa : ∀ z ∈ closedPolydisc c R, ∀ i,
      AnalyticAt ℂ (fun x => f (update z i x)) (z i)) :
    ∫ θ in Set.Icc (0 : Fin d → ℝ) (fun _ => 2 * π), f (torusMap c R θ) =
      (2 * π : ℂ) ^ d • f c := by
  have hw : ∀ i, ‖c i - c i‖ < R i := fun i => by simpa using hR i
  have hkey := two_pi_I_pow_inv_smul_torusIntegral_prod_sub_inv_smul hR hw hfc hfa
  rw [torusIntegral] at hkey
  have hkernel : Set.EqOn
      (fun θ : Fin d → ℝ => (∏ i, (R i : ℂ) * Complex.exp ((θ i : ℂ) * I) * I) •
        ((∏ i, (torusMap c R θ i - c i)⁻¹) • f (torusMap c R θ)))
      (fun θ : Fin d → ℝ => (I : ℂ) ^ d • f (torusMap c R θ))
      (Set.Icc (0 : Fin d → ℝ) fun _ => 2 * π) := by
    intro θ _
    simp only
    rw [smul_smul]
    congr 1
    rw [← Finset.prod_mul_distrib]
    rw [show (I : ℂ) ^ d = ∏ _i : Fin d, I by simp]
    apply Finset.prod_congr rfl
    intro i _
    have hRi : (R i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hR i).ne'
    have hzc : torusMap c R θ i - c i = R i * Complex.exp ((θ i : ℂ) * I) := by
      simp [torusMap]
    rw [hzc]
    have hexp : Complex.exp ((θ i : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hkernel,
    MeasureTheory.integral_smul] at hkey
  have hI : ((2 * π * I : ℂ) ^ d)⁻¹ • ((I : ℂ) ^ d •
      ∫ θ in Set.Icc (0 : Fin d → ℝ) fun _ => 2 * π, f (torusMap c R θ)) = f c := hkey
  have hIpow : ((2 * π * I : ℂ) ^ d)⁻¹ * (I : ℂ) ^ d = ((2 * π : ℂ) ^ d)⁻¹ := by
    rw [mul_pow]
    field_simp
  rw [smul_smul, hIpow] at hI
  have h2π : ((2 * π : ℂ) ^ d) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have := congrArg (fun x => (2 * π : ℂ) ^ d • x) hI
  simpa [smul_smul, h2π] using this

omit [CompleteSpace E] in
/-- A common unit complex rotation preserves integration over a centered polydisc. -/
private theorem integral_closedBall_smul {ι : Type*} [Fintype ι]
    (f : (ι → ℂ) → E) (r : ℝ) {w : ℂ} (hw : ‖w‖ = 1) :
    ∫ z in closedBall (0 : ι → ℂ) r, f (w • z) =
      ∫ z in closedBall (0 : ι → ℂ) r, f z := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  let e : ℂ ≃ₗᵢ[ℝ] ℂ :=
    { (LinearEquiv.smulOfNeZero ℂ ℂ w hw0).restrictScalars ℝ with
      norm_map' := fun z => by simp [LinearEquiv.smulOfNeZero_apply, hw] }
  let ePi := MeasurableEquiv.piCongrRight (fun _ : ι => e.toMeasurableEquiv)
  have hm : MeasurePreserving (fun z : ι → ℂ => w • z) volume volume :=
    volume_preserving_pi (fun _ : ι => e.measurePreserving)
  have hpre : (fun z : ι → ℂ => w • z) ⁻¹' closedBall 0 r = closedBall 0 r := by
    ext z
    simp [mem_closedBall, dist_zero_right, norm_smul, hw]
  simpa only [hpre] using
    hm.setIntegral_preimage_emb ePi.measurableEmbedding f (closedBall 0 r)

/-- Averaging a holomorphic function over an equal-radius polydisc centered at zero returns its
center value times the volume. The proof averages common complex rotations and uses Fubini; it
also applies when the coordinate type is empty. -/
theorem integral_closedBall_zero_eq_volume_smul {ι : Type*} [Fintype ι]
    {f : (ι → ℂ) → E} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 r)) :
    ∫ z in closedBall (0 : ι → ℂ) r, f z =
      volume.real (closedBall (0 : ι → ℂ) r) • f 0 := by
  let B := closedBall (0 : ι → ℂ) r
  let T := Icc (0 : ℝ) (2 * π)
  let H := fun (z : ι → ℂ) (θ : ℝ) => f (circleMap 0 1 θ • z)
  have hrot (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by simp
  have hmap : MapsTo (fun p : (ι → ℂ) × ℝ => circleMap 0 1 p.2 • p.1) (B ×ˢ T) B := by
    intro p hp
    simpa only [B, mem_closedBall, dist_zero_right, norm_smul, hrot, one_mul] using hp.1
  have hcont : ContinuousOn (Function.uncurry H) (B ×ˢ T) :=
    hf.continuousOn.comp (by fun_prop) hmap
  have hint : Integrable (Function.uncurry H)
      ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hcont.integrableOn_compact ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hmean (z : ι → ℂ) (hz : z ∈ B) :
      ∫ θ in T, H z θ = (2 * π) • f 0 := by
    have hline : DifferentiableOn ℂ (fun w : ℂ => f (w • z)) (closedBall 0 1) := by
      intro w hw
      have hwz : w • z ∈ closedBall (0 : ι → ℂ) r := by
        rw [mem_closedBall, dist_zero_right, norm_smul]
        exact (mul_le_mul_of_nonneg_right (mem_closedBall_zero_iff.mp hw) (norm_nonneg z)).trans
          (by simpa [B] using hz)
      have hmap : AnalyticAt ℂ (fun t : ℂ => t • z) w :=
        analyticAt_id.smul analyticAt_const
      exact ((hf _ hwz).comp_of_eq hmap rfl).differentiableWithinAt
    have hline' : DifferentiableOn ℂ (fun w : ℂ => f (w • z))
        (closure (ball 0 |(1 : ℝ)|)) := by
      simpa only [abs_one, closure_ball _ one_ne_zero] using hline
    have h := hline'.diffContOnCl.circleAverage
    simp only [Real.circleAverage, zero_smul] at h
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_Icc_eq_integral_Ioc] at h
    have he := congrArg (fun v : E => (2 * π) • v) h
    simpa only [smul_smul, mul_inv_cancel₀ Real.two_pi_pos.ne', one_smul] using he
  have hswap := integral_integral_swap hint
  have hleft : (∫ z in B, ∫ θ in T, H z θ) =
      (2 * π) • (volume.real B • f 0) := by
    rw [setIntegral_congr_fun measurableSet_closedBall hmean, integral_const]
    simp only [Measure.real, Measure.restrict_apply_univ]
    exact smul_comm _ _ _
  have hright : (∫ θ in T, ∫ z in B, H z θ) =
      (2 * π) • (∫ z in B, f z) := by
    simp_rw [H, B, integral_closedBall_smul f r (hrot _)]
    simp [T, integral_const, Real.volume_Icc, Measure.real, ENNReal.toReal_ofReal Real.pi_pos.le]
  rw [hleft, hright] at hswap
  exact (smul_right_injective E Real.two_pi_pos.ne' hswap).symm

/-- The volume mean-value formula on an equal-radius polydisc with arbitrary center. The norm on the
finite coordinate space is the supremum norm. -/
theorem integral_closedBall_eq_volume_smul {ι : Type*} [Fintype ι]
    {f : (ι → ℂ) → E} {c : ι → ℂ} {r : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) :
    ∫ z in closedBall c r, f z = volume.real (closedBall c r) • f c := by
  have hpre : (fun z : ι → ℂ => c + z) ⁻¹' closedBall c r = closedBall 0 r := by
    ext z
    simp [mem_closedBall, dist_eq_norm]
  have hvol : volume (closedBall (0 : ι → ℂ) r) = volume (closedBall c r) := by
    rw [← hpre]
    exact measure_preimage_add volume c _
  have hm := (measurePreserving_add_left (volume : Measure (ι → ℂ)) c).setIntegral_preimage_emb
    (Homeomorph.addLeft c).isClosedEmbedding.measurableEmbedding f (closedBall c r)
  rw [hpre] at hm
  have htrans : AnalyticOnNhd ℂ (fun z => f (c + z)) (closedBall (0 : ι → ℂ) r) := by
    intro z hz
    have hcz : c + z ∈ closedBall c r := by simpa [mem_closedBall, dist_eq_norm] using hz
    exact (hf _ hcz).comp (analyticAt_const.add analyticAt_id)
  rw [← hm, integral_closedBall_zero_eq_volume_smul htrans, Measure.real, hvol, add_zero]
  rfl

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
