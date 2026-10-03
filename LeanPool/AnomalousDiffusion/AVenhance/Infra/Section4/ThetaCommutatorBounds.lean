/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaScale
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaCommutator
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaDifferentiatedEnergy

/-! Pointwise differentiated-drift bounds from the high-order stream-regularity conclusion. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section4

theorem theta_prev_potential_word_abs_le_of_A3
    {β : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Homogenization.Vec 2 → ℝ)
    (hΦ : AVenhance.IsStreamSeq I Φ) (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) :
    ∀ t : ℝ, ∀ w : List (Fin 2), 2 ≤ w.length →
      ∀ x : Homogenization.Vec 2,
        |classicalWordDerivative w (Φ (m - 1) t) x| ≤
        2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
          AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
          (w.length.factorial : ℝ) *
          (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ w.length := by
  intro t w hw x
  let f : Homogenization.Vec 2 → ℝ := Φ (m - 1) t
  have hfAdm : AVenhance.IsAdmissibleStream (Φ (m - 1)) :=
    theta_prev_stream_admissible I Φ hΦ hm
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Homogenization.Vec 2 => (t, y)) :=
      contDiff_const.prodMk contDiff_id
    simpa [f, Function.uncurry, Function.comp_def] using hfAdm.1.comp hmap
  have hword := thetaWordDerivative_eq_iteratedFDeriv_get w f hf x
  have hpoint := theta_stream_deriv_pointwise_of_A3 I Φ hΦ hm hA3
    w.length hw t (fun j => w.get j) x
  rw [hword]
  exact hpoint

/-- The drift derivatives entering the transport commutator are controlled
by the high-order barNorm clause of the stream-regularity estimates.  The hypothesis is copied
    literally
from that clause; its order-two threshold is used because every commutator
term differentiates the drift at least once. -/
theorem theta_prev_drift_word_abs_le_of_A3
    {β : ℝ} {m : ℕ} (I : AVenhance.Ingredients β)
    (Φ : ℕ → ℝ → Homogenization.Vec 2 → ℝ)
    (hΦ : AVenhance.IsStreamSeq I Φ) (hm : 2 ≤ m)
    (hA3 : ∀ j : ℕ, 1 ≤ j → ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (AVenhance.epsilon β I.Λ j)⁻¹)
        (Φ j t) ≤
      ENNReal.ofReal (2 ^ 5 * AVenhance.a β I.Λ j *
        AVenhance.epsilon β I.Λ j ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) :
    ∀ t : ℝ, ∀ w : List (Fin 2), 1 ≤ w.length →
      ∀ j : Fin 2, ∀ x : Homogenization.Vec 2,
        |classicalWordDerivative w
          (fun y => AVenhance.streamVel
            (fun _ => Φ (m - 1) t) 0 y j) x| ≤
        2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
          AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
          ((w.length + 1).factorial : ℝ) *
          (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ (w.length + 1) := by
  intro t w hw j x
  let f : Homogenization.Vec 2 → ℝ := Φ (m - 1) t
  let n : ℕ := w.length + 1
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hfAdm : AVenhance.IsAdmissibleStream (Φ (m - 1)) :=
    theta_prev_stream_admissible I Φ hΦ hm
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Homogenization.Vec 2 => (t, y)) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := hfAdm.1.comp hmap
    simpa [f, Function.uncurry, Function.comp_def] using hcomp
  have hcoef : ∀ r : ℕ, 2 ≤ r → ∀ i : Fin r → Fin 2,
      ∀ y : Homogenization.Vec 2,
      ‖iteratedFDeriv ℝ r f y
        (fun k => Homogenization.basisVec (i k))‖ ≤
        2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
          AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
          (r.factorial : ℝ) *
          (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ r := by
    intro r hr i y
    simpa [f] using theta_stream_deriv_pointwise_of_A3 I Φ hΦ hm hA3 r hr t i y
  have hword (v : List (Fin 2)) (hlen : 2 ≤ v.length) :
      ∀ y : Homogenization.Vec 2,
      |classicalWordDerivative v f y| ≤
        2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
          AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
          (v.length.factorial : ℝ) *
          (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ v.length := by
    intro y
    exact classicalWordDerivative_abs_le_of_iteratedFDeriv v f _ hf
      (by
        intro i' z
        exact hcoef v.length hlen i' z) y
  have hgrad (k : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => AVenhance.spaceGrad f y k) := by
    change ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative [k] f)
    exact classicalWordDerivative_contDiff [k] f hf
  have hwordGrad (k : Fin 2) : ∀ y : Homogenization.Vec 2,
      |classicalWordDerivative w (fun z => AVenhance.spaceGrad f z k) y| ≤
        2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
          AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
          (n.factorial : ℝ) *
          (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n := by
    intro y
    have hcomm := congrFun (classicalWordDerivative_commute_gradient w f hf k) y
    have h := hword (k :: w) (by simp; omega) y
    calc
      |classicalWordDerivative w (fun z => AVenhance.spaceGrad f z k) y| =
          |classicalWordDerivative (k :: w) f y| := by
            rw [hcomm]
            rfl
      _ ≤ 2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
          AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
          (n.factorial : ℝ) *
          (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n := by
        simpa [n] using h
  have hstream0 :
      (fun y => AVenhance.streamVel (fun _ => f) 0 y 0) =
        (fun y => -AVenhance.spaceGrad f y 1) := by
    funext y
    simp [AVenhance.streamVel, AVenhance.sigmaMat,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  have hstream1 :
      (fun y => AVenhance.streamVel (fun _ => f) 0 y 1) =
        (fun y => AVenhance.spaceGrad f y 0) := by
    funext y
    simp [AVenhance.streamVel, AVenhance.sigmaMat,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
  have hresult : ∀ k : Fin 2,
      ∀ y : Homogenization.Vec 2,
        |classicalWordDerivative w
          (fun z => AVenhance.streamVel (fun _ => f) 0 z k) y| ≤
        2 ^ 5 * AVenhance.a β I.Λ (m - 1) *
          AVenhance.epsilon β I.Λ (m - 1) ^ 2 *
          (n.factorial : ℝ) *
          (2 ^ 8 * (AVenhance.epsilon β I.Λ (m - 1))⁻¹) ^ n := by
    intro k y
    fin_cases k
    · change |classicalWordDerivative w
        (fun z => AVenhance.streamVel (fun _ => f) 0 z 0) y| ≤ _
      rw [show (fun z => AVenhance.streamVel (fun _ => f) 0 z 0) =
          (fun z => -AVenhance.spaceGrad f z 1) by exact hstream0,
        classicalWordDerivative_neg w _ (hgrad 1)]
      simpa [abs_neg] using hwordGrad 1 y
    · change |classicalWordDerivative w
        (fun z => AVenhance.streamVel (fun _ => f) 0 z 1) y| ≤ _
      rw [show (fun z => AVenhance.streamVel (fun _ => f) 0 z 1) =
          (fun z => AVenhance.spaceGrad f z 0) by exact hstream1]
      exact hwordGrad 0 y
  simpa [f, n] using hresult j x

end AVenhance.Infra.Section4
