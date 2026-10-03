/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Statements.Aleksandrov.Final
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Theorems.Core

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Adapter from the external Aleksandrov formalization

This module connects the completed convex Aleksandrov theorem in the sibling
`AleksandrovDifferentiability` project to the jet-based statement used by the
comparison proof in this project.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped Topology ENNReal
open Asymptotics

namespace ViscositySolns

variable {n : Nat}

private theorem norm_comp_symm_sq_isBigO
    (x : Point n)
    (S : Point n →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (fun z : Point n => (‖S (z - x)‖ ^ 2 : ℝ)) =O[𝓝 x]
      (fun z : Point n => (‖z - x‖ ^ 2 : ℝ)) := by
  rcases S.bound with ⟨C, hCpos, hC⟩
  rw [Asymptotics.isBigO_iff]
  refine ⟨C ^ 2, Filter.Eventually.of_forall ?_⟩
  intro z
  have hle : ‖S (z - x)‖ ≤ C * ‖z - x‖ := hC (z - x)
  have htarget_nonneg : 0 ≤ ‖z - x‖ ^ 2 := sq_nonneg _
  rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg htarget_nonneg]
  nlinarith [hCpos.le, norm_nonneg (z - x), norm_nonneg (S (z - x))]

private def externalFirstDerivativeCLM
    (p : EuclideanSpace ℝ (Fin n)) :
    Point n →L[ℝ] ℝ := by
  let E := EuclideanSpace ℝ (Fin n)
  let e : E ≃L[ℝ] Point n := EuclideanSpace.equiv (Fin n) ℝ
  let S : Point n →L[ℝ] E := e.symm.toContinuousLinearMap
  exact (innerSL ℝ p).comp S

private def externalSecondDerivativeCLM
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Point n →L[ℝ] Point n →L[ℝ] ℝ := by
  let E := EuclideanSpace ℝ (Fin n)
  let e : E ≃L[ℝ] Point n := EuclideanSpace.equiv (Fin n) ℝ
  let S : Point n →L[ℝ] E := e.symm.toContinuousLinearMap
  let T : Point n →L[ℝ] E := B.comp S
  let L : E →L[ℝ] E →L[ℝ] ℝ := innerSL ℝ
  let L1 : E →L[ℝ] Point n →L[ℝ] ℝ := (L.precompL (Point n)) T
  exact L1.comp S

private theorem externalSecondDerivativeCLM_symm
    {B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hB : AleksandrovDifferentiability.IsSymmetricOperator B) :
    IsSymmetricBilinear (externalSecondDerivativeCLM (n := n) B) := by
  intro v w
  dsimp [externalSecondDerivativeCLM,
    AleksandrovDifferentiability.IsSymmetricOperator] at hB ⊢
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] Point n := EuclideanSpace.equiv (Fin n) ℝ
  calc
    inner ℝ (B (e.symm w)) (e.symm v) =
        inner ℝ (e.symm v) (B (e.symm w)) := real_inner_comm _ _
    _ = inner ℝ (B (e.symm v)) (e.symm w) :=
        (hB (e.symm v) (e.symm w)).symm

private theorem hasSomeSecondOrderJet_of_external_secondOrderDifferentiableAt
    {f : Point n → ℝ} {x : Point n}
    (h :
      AleksandrovDifferentiability.SecondOrderDifferentiableAt
        (fun y : EuclideanSpace ℝ (Fin n) =>
          f ((EuclideanSpace.equiv (Fin n) ℝ) y))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x)) :
    HasSomeSecondOrderJet f x := by
  let E := EuclideanSpace ℝ (Fin n)
  let e : E ≃L[ℝ] Point n := EuclideanSpace.equiv (Fin n) ℝ
  let S : Point n →L[ℝ] E := e.symm.toContinuousLinearMap
  rcases h with ⟨p, B, hBsymm, hTaylorE⟩
  let Dφ : Point n →L[ℝ] ℝ := externalFirstDerivativeCLM (n := n) p
  let D2φ : Point n →L[ℝ] Point n →L[ℝ] ℝ :=
    externalSecondDerivativeCLM (n := n) B
  have hD2symm : IsSymmetricBilinear D2φ :=
    externalSecondDerivativeCLM_symm (n := n) hBsymm
  have hTaylor0 :
      (fun w : Point n =>
        f (x + w) - f x - Dφ w - (1 / 2 : ℝ) * D2φ w w)
        =o[𝓝 0] (fun w : Point n => (‖S w‖ ^ 2 : ℝ)) := by
    have hS0 : Filter.Tendsto S (𝓝 (0 : Point n)) (𝓝 (0 : E)) := by
      simpa using S.continuous.tendsto (0 : Point n)
    have hcomp := hTaylorE.comp_tendsto hS0
    refine hcomp.congr_left ?_
    intro w
    dsimp [AleksandrovDifferentiability.HasSecondOrderExpansionAt,
      Dφ, D2φ, externalFirstDerivativeCLM, externalSecondDerivativeCLM, S, e] at *
    rw [map_add]
    rw [show (EuclideanSpace.equiv (Fin n) ℝ)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x) = x by
      exact (EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply x]
    rw [show (EuclideanSpace.equiv (Fin n) ℝ)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm w) = w by
      exact (EuclideanSpace.equiv (Fin n) ℝ).apply_symm_apply w]
    rw [show ((EuclideanSpace.equiv (Fin n) ℝ).symm w) = WithLp.toLp 2 w by rfl]
    change
      f (x + w) - f x - inner ℝ p (WithLp.toLp 2 w) -
          (1 / 2 : ℝ) * inner ℝ (WithLp.toLp 2 w) (B (WithLp.toLp 2 w)) =
        f (x + w) - f x - inner ℝ p (WithLp.toLp 2 w) -
          (1 / 2 : ℝ) * inner ℝ (B (WithLp.toLp 2 w)) (WithLp.toLp 2 w)
    rw [real_inner_comm (B (WithLp.toLp 2 w)) (WithLp.toLp 2 w)]
  have hTaylorX_raw :
      (fun z : Point n =>
        f (x + (z - x)) - f x - Dφ (z - x) -
          (1 / 2 : ℝ) * D2φ (z - x) (z - x))
        =o[𝓝 x] (fun z : Point n => (‖S (z - x)‖ ^ 2 : ℝ)) := by
    have hsub0 : Filter.Tendsto (fun z : Point n => z - x) (𝓝 x) (𝓝 (0 : Point n)) := by
      have hcont :
          ContinuousAt (fun z : Point n => z - x) x :=
        (continuousAt_id : ContinuousAt (fun z : Point n => z) x).sub
          (continuousAt_const : ContinuousAt (fun _ : Point n => x) x)
      change Filter.Tendsto (fun z : Point n => z - x) (𝓝 x)
        (𝓝 ((fun z : Point n => z - x) x)) at hcont
      simpa using hcont
    simpa [Function.comp_def] using hTaylor0.comp_tendsto hsub0
  have hTaylorX :
      (fun z : Point n =>
        f z - frechetSecondOrderModel x (f x) Dφ D2φ z)
        =o[𝓝 x] (fun z : Point n => ‖z - x‖ ^ 2) := by
    refine (hTaylorX_raw.congr_left ?_).trans_isBigO
      (norm_comp_symm_sq_isBigO (n := n) x S)
    intro z
    simp [frechetSecondOrderModel]
    ring
  exact HasSomeSecondOrderJet.of_frechetLittleO hD2symm hTaylorX

private theorem convex_openBall_badSet_volume_eq_zero_external
    (f : Point n → ℝ) (x0 : Point n) (r : ℝ) (_hr : 0 < r)
    (hconv : ConvexOn ℝ (Metric.closedBall x0 r) f) :
    volume (Metric.ball x0 r ∩ {x : Point n | ¬ HasSomeSecondOrderJet f x}) = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let e : E ≃L[ℝ] Point n := EuclideanSpace.equiv (Fin n) ℝ
  let Ω : Set E := e ⁻¹' Metric.ball x0 r
  let u : E → ℝ := fun y => f (e y)
  have hΩopen : IsOpen Ω := by
    exact Metric.isOpen_ball.preimage e.continuous
  have hconvBall : ConvexOn ℝ (Metric.ball x0 r) f :=
    hconv.subset Metric.ball_subset_closedBall (convex_ball x0 r)
  have hconvE : ConvexOn ℝ Ω u := by
    exact hconvBall.comp_linearMap (e.toContinuousLinearMap.toLinearMap)
  have haeSecond :
      ∀ᵐ y ∂((volume : Measure E).restrict Ω),
        AleksandrovDifferentiability.SecondOrderDifferentiableAt u y :=
    AleksandrovDifferentiability.convexAleksandrovAE
      (E := E) (Ω := Ω) (u := u) hΩopen hconvE
  have haeJet :
      ∀ᵐ y ∂((volume : Measure E).restrict Ω),
        HasSomeSecondOrderJet f (e y) := by
    refine haeSecond.mono ?_
    intro y hy
    have hy' :
        AleksandrovDifferentiability.SecondOrderDifferentiableAt
          (fun z : EuclideanSpace ℝ (Fin n) =>
            f ((EuclideanSpace.equiv (Fin n) ℝ) z))
          ((EuclideanSpace.equiv (Fin n) ℝ).symm (e y)) := by
      simpa [u, e] using hy
    exact hasSomeSecondOrderJet_of_external_secondOrderDifferentiableAt
      (n := n) (f := f) (x := e y) hy'
  have hnullRestrict :
      ((volume : Measure E).restrict Ω)
        {y : E | ¬ HasSomeSecondOrderJet f (e y)} = 0 :=
    ae_iff.mp haeJet
  have hnullE :
      (volume : Measure E)
        (Ω ∩ {y : E | ¬ HasSomeSecondOrderJet f (e y)}) = 0 := by
    simpa [Measure.restrict_apply' hΩopen.measurableSet, Set.inter_comm]
      using hnullRestrict
  have hmp : MeasurePreserving (fun x : Point n => e.symm x) volume (volume : Measure E) := by
    exact PiLp.volume_preserving_toLp (Fin n)
  let badE : Set E := Ω ∩ {y : E | ¬ HasSomeSecondOrderJet f (e y)}
  have hpre :
      (fun x : Point n => e.symm x) ⁻¹' badE =
        Metric.ball x0 r ∩ {x : Point n | ¬ HasSomeSecondOrderJet f x} := by
    ext x
    simp [badE, Ω, e]
  rw [← hpre]
  exact hmp.quasiMeasurePreserving.preimage_null (s := badE) hnullE

/--
The completed sibling Aleksandrov formalization implies the closed-ball
second-order jet differentiability theorem used by the viscosity comparison
proofs in this repository.
-/
theorem AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.proof_external
    (n : Nat) :
    AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n := by
  apply AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem.of_convex_openBall
  intro f x0 r hr hconv
  exact convex_openBall_badSet_volume_eq_zero_external f x0 r hr hconv

end ViscositySolns
