/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HigherVariation3.Existence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HigherVariation3.Multilinear
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.HigherVariation3.Growth

/-! Taylor control for the second spatial derivative of the field. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

/-- Two spatial directions embedded into time-space for the field Taylor expansion. -/
def ThirdFieldTaylor.thirdTaylorDirections2 (h k : Vec 2) : Fin 2 → ℝ × Vec 2 :=
  fun i => if i = 0 then (0, h) else (0, k)

theorem ThirdFieldTaylor.fderiv_spatialSecondDerivativeEval_apply
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (t : ℝ) (x h k v : Vec 2) :
    fderiv ℝ (fun z => spatialSecondDerivativeEval b t z h k) x v =
      spatialThirdDerivativeEval b t x v h k := by
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  let G : ℝ × Vec 2 → _root_.ContinuousMultilinearMap ℝ
      (fun _ : Fin 2 => ℝ × Vec 2) (Vec 2) :=
    fun p => iteratedFDeriv ℝ 2 F p
  let g : Vec 2 → ℝ × Vec 2 := fun z => (t, z)
  let incl : Vec 2 →L[ℝ] (ℝ × Vec 2) :=
    ContinuousLinearMap.inr ℝ ℝ (Vec 2)
  let H : Vec 2 → _root_.ContinuousMultilinearMap ℝ
      (fun _ : Fin 2 => ℝ × Vec 2) (Vec 2) := G ∘ g
  let dirs := ThirdFieldTaylor.thirdTaylorDirections2 h k
  let E : _root_.ContinuousMultilinearMap ℝ
      (fun _ : Fin 2 => ℝ × Vec 2) (Vec 2) →L[ℝ] Vec 2 :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℝ × Vec 2) (Vec 2) dirs
  let f : Vec 2 → Vec 2 := fun z => spatialSecondDerivativeEval b t z h k
  have htwo : (2 : ℕ∞ω) < ∞ := by
    change (↑(2 : ℕ∞) : ℕ∞ω) < (↑(⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top 2)
  have hGdiff : Differentiable ℝ G := by
    exact hb.smooth.differentiable_iteratedFDeriv htwo
  have hg : ∀ z, HasFDerivAt g incl z := by
    intro z
    exact hasFDerivAt_prodMk_right t z
  have hHdiff : Differentiable ℝ H := by
    intro z
    exact (hGdiff (g z)).comp z (hg z).differentiableAt
  have hspatial (z : Vec 2) : f z = E (H z) := by
    change spatialSecondDerivativeEval b t z h k = _
    rw [spatialSecondDerivativeEval_eq_joint]
    simp [F, H, G, g, E, dirs, ThirdFieldTaylor.thirdTaylorDirections2, iteratedFDeriv_two_apply]
  have hEq : f = E ∘ H := by
    funext z
    exact hspatial z
  have hGderiv (p : ℝ × Vec 2) :
      fderiv ℝ G p =
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin 3 => ℝ × Vec 2) (Vec 2))
            (iteratedFDeriv ℝ 3 F p) := by
    exact congrFun (fderiv_iteratedFDeriv (𝕜 := ℝ) (n := 2) (f := F)) p
  have hHderiv (z : Vec 2) : fderiv ℝ H z =
      ((continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin 3 => ℝ × Vec 2) (Vec 2))
          (iteratedFDeriv ℝ 3 F (g z))).comp incl := by
    have hcomp := ((hGdiff (g z)).hasFDerivAt).comp z (hg z)
    rw [hGderiv] at hcomp
    simpa [H, g, Function.comp_def] using hcomp.fderiv
  have hformula : fderiv ℝ f x = E.comp (fderiv ℝ H x) := by
    rw [hEq]
    exact (HasFDerivAt.comp x E.hasFDerivAt (hHdiff x).hasFDerivAt).fderiv
  rw [hformula, hHderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change ((continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin 3 => ℝ × Vec 2) (Vec 2))
        (iteratedFDeriv ℝ 3 F (g x))) (incl v) dirs = _
  rw [continuousMultilinearCurryLeftEquiv_apply]
  change iteratedFDeriv ℝ 3 F (g x) (Fin.cons (incl v) dirs) = _
  have hdirs : Fin.cons (incl v) dirs =
      (fun i => if i = 0 then (0, v) else if i = 1 then (0, h) else (0, k)) := by
    funext i
    fin_cases i <;> rfl
  rw [hdirs]
  rfl

/-- The field Hessian has a quadratic Taylor remainder whose linear term is
its third spatial derivative. -/
theorem exists_global_spatialSecondDerivativeEval_taylor_remainder
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x y h k,
      ‖spatialSecondDerivativeEval b t y h k -
          spatialSecondDerivativeEval b t x h k -
          spatialThirdDerivativeEval b t x (y - x) h k‖ ≤
        C * ‖h‖ * ‖k‖ * ‖y - x‖ * ‖y - x‖ := by
  obtain ⟨C, hC₀, hC⟩ := exists_global_spatialThirdDerivativeEval_lipschitz hb
  refine ⟨C, hC₀, ?_⟩
  intro t x y h k
  let g : Vec 2 → Vec 2 := fun z => b t z
  let J : Vec 2 → Vec 2 →L[ℝ] Vec 2 := fun z => fderiv ℝ g z
  let EvK : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] Vec 2 :=
    (ContinuousLinearMap.apply ℝ (Vec 2)) k
  let Q : Vec 2 → Vec 2 := fun z => jointSpatialFDeriv b t z k
  let EvH : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] Vec 2 :=
    (ContinuousLinearMap.apply ℝ (Vec 2)) h
  let f : Vec 2 → Vec 2 := fun z => fderiv ℝ Q z h
  have hg : ContDiff ℝ ∞ g := by
    exact hb.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hJ : ContDiff ℝ 3 J := hg.fderiv_right (m := 3) (by norm_num)
  have hQeq : Q = EvK ∘ J := by
    funext z
    change jointSpatialFDeriv b t z k = EvK (J z)
    rw [jointSpatialFDeriv_eq_slice hb]
    rfl
  have hQ : ContDiff ℝ 3 Q := by
    rw [hQeq]
    exact EvK.contDiff.comp hJ
  have hFderiv : ContDiff ℝ 2 (fderiv ℝ Q) :=
    hQ.fderiv_right (m := 2) (by norm_num)
  have hf : ContDiff ℝ 2 f := by
    change ContDiff ℝ 2 (EvH ∘ fderiv ℝ Q)
    exact EvH.contDiff.comp hFderiv
  have hfEq (z : Vec 2) : f z = spatialSecondDerivativeEval b t z h k := by
    dsimp [f, Q]
    exact (spatialSecondDerivativeEval_eq_spatialJacobianFDeriv_apply hb t z h k).symm
  have hfeq : f = fun z => spatialSecondDerivativeEval b t z h k := by
    funext z
    exact hfEq z
  have hdfLip (z : Vec 2) :
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤
        (C * ‖h‖ * ‖k‖) * ‖z - x‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [sub_apply,
      hfeq,
      ThirdFieldTaylor.fderiv_spatialSecondDerivativeEval_apply hb,
      ThirdFieldTaylor.fderiv_spatialSecondDerivativeEval_apply hb]
    have hbase := hC t z x v h k
    calc
      ‖spatialThirdDerivativeEval b t z v h k -
          spatialThirdDerivativeEval b t x v h k‖ ≤
          C * ‖z - x‖ * ‖v‖ * ‖h‖ * ‖k‖ := hbase
      _ = (C * ‖h‖ * ‖k‖) * ‖z - x‖ * ‖v‖ := by ring
  let Cder : ℝ := C * ‖h‖ * ‖k‖
  have hCder₀ : 0 ≤ Cder := by dsimp [Cder]; positivity
  let S : Set (Vec 2) := Metric.closedBall x ‖y - x‖
  have hS : Convex ℝ S := convex_closedBall _ _
  have hxS : x ∈ S := by simp [S, Metric.mem_closedBall]
  have hyS : y ∈ S := by
    simp [S, Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
  have hLipOn : ∀ z ∈ S,
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ Cder * ‖y - x‖ := by
    intro z hz
    have hz' : ‖z - x‖ ≤ ‖y - x‖ := by
      simpa [S, Metric.mem_closedBall, dist_eq_norm] using hz
    dsimp [Cder]
    exact (hdfLip z).trans (mul_le_mul_of_nonneg_left hz' (by positivity))
  have hTaylor := hS.norm_image_sub_le_of_norm_fderiv_le'
    (f := f) (φ := fderiv ℝ f x)
    (fun z _ => hf.differentiable (by norm_num) z)
    hLipOn hxS hyS
  have hderiv : fderiv ℝ f x (y - x) =
      spatialThirdDerivativeEval b t x (y - x) h k := by
    rw [hfeq]
    exact ThirdFieldTaylor.fderiv_spatialSecondDerivativeEval_apply hb t x h k (y - x)
  rw [hfEq y, hfEq x, hderiv] at hTaylor
  simpa [Cder, mul_assoc, mul_left_comm, mul_comm] using hTaylor

end AVenhance.Infra.Flow
