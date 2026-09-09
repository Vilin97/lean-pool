/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanSmoothRepresentative
public import LeanPool.NavierStokesAndEuler.Euler.SobolevJointEvaluation

@[expose] public section

/-! Genuine Sobolev arrays and bounded spatial evaluation for ordinary L² translation orbits. -/

noncomputable section


namespace EulerMeanSmoothRepresentative

open MeasureTheory EulerSmoothLimit EulerMeanSolenoidal EulerMeanOrdinaryLift
  EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolev
  EulerPressureSpatialRegularity EulerCylinderSobolevSpace EulerSobolevPointEvaluation

open scoped ContDiff

private local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

def coordinateTuple {n : ℕ} (w : Fin n → Fin 4) : Fin n → Space :=
  fun i => (standardDirection (w i)).1

theorem coordinateTuple_norm_le {n : ℕ} (w : Fin n → Fin 4) : ‖coordinateTuple w‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  have hdir (i : Fin 4) : ‖(standardDirection i).1‖ ≤ 1 := by
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [standardDirection_zero, norm_zero, zero_le_one]
    · simp only [standardDirection_succ, PiLp.norm_single, norm_one, le_refl]
  exact hdir (w j)

/-- Iterating an actual strong orbit derivative is the same as evaluating the next full tensor. -/
theorem iteratedFDeriv_orbitDerivative (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u)
    (v : Space) (n : ℕ) (a : Space) (m : Fin n → Space) :
    iteratedFDeriv ℝ n (fun b : Space => EulerMeanSolenoidal.translation b (orbitDerivative u v)) a
      m =
      iteratedFDeriv ℝ (n+1) (fun b : Space => EulerMeanSolenoidal.translation b u) a (Fin.snoc m
        v) := by
  let F : Space → EulerMeanSolenoidal.L2 := fun b => EulerMeanSolenoidal.translation b u
  have H := (ContinuousLinearMap.apply ℝ EulerMeanSolenoidal.L2 v).iteratedFDeriv_comp_left
    (hu.fderiv_right (m := ∞) (by simp)).contDiffAt (x := a) (i := n) (by simp)
  have He := congrArg (fun G => G m) H
  change iteratedFDeriv ℝ n (fun b => fderiv ℝ F b v) a m =
    iteratedFDeriv ℝ n (fderiv ℝ F) a m v at He
  have heq : (fun b : Space => EulerMeanSolenoidal.translation b (orbitDerivative u v)) =
      fun b : Space => fderiv ℝ F b v :=
    funext fun b => orbitDerivative_translation u hu v b
  rw [heq, He, iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_snoc, Fin.snoc_last]
  rfl

/-- The coordinates of the constructed jet are actual ordinary-space derivative tensors. -/
theorem ordinarySpatialJet_word (n q : ℕ) (hn : n ≤ q) (u : EulerMeanSolenoidal.L2)
    (hu : SmoothOrbit u) (w : Fin n → Fin 4) :
    (ordinarySpatialJet q u hu).word w = ordinaryLift
      (iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a u) 0 (coordinateTuple
        w)) := by
  induction n generalizing q u with
  | zero =>
    simp only [SpatialJet.word_zero, iteratedFDeriv_zero_apply,
      EulerMeanSolenoidal.translation_zero]
  | succ n ih =>
    cases q with
    | zero => omega
    | succ q =>
      rw [ordinarySpatialJet, SpatialJet.word_succ]
      rw [ih q (by omega) (orbitDerivative u (standardDirection (w (Fin.last n))).1)
        (orbitDerivative_smooth u hu (standardDirection (w (Fin.last n))).1) (Fin.init w)]
      rw [iteratedFDeriv_orbitDerivative u hu]
      congr 2
      change Fin.snoc (Fin.init (coordinateTuple w)) ((coordinateTuple w) (Fin.last n)) =
        coordinateTuple w
      exact Fin.snoc_init_self _

/-- A concrete element of the previously constructed complete cylinder Sobolev space. -/
def ordinarySobolev (q : ℕ) (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) : SobolevSpace 1 q :=
  ofJet 1 (ordinarySpatialJet q u hu)

@[simp] theorem ordinarySobolev_value (q : ℕ) (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) :
    value 1 (ordinarySobolev q u hu) = ordinaryLift u := value_ofJet 1 _

theorem ordinarySobolev_coordinate (q : ℕ) (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u)
    (w : SobolevWord q) :
    (ordinarySobolev q u hu).val w = ordinaryLift
      (iteratedFDeriv ℝ w.1.val (fun a : Space => EulerMeanSolenoidal.translation a u) 0
        (coordinateTuple w.2)) :=
  ordinarySpatialJet_word w.1.val q (Nat.le_of_lt_succ w.1.isLt) u hu w.2

/-- The finite Sobolev array is bounded directly by actual L² orbit-derivative norms. -/
theorem ordinarySobolev_norm_le (q : ℕ) (u : EulerMeanSolenoidal.L2) (hu : SmoothOrbit u) :
    ‖ordinarySobolev q u hu‖ ≤ ∑ n ∈ Finset.range (q+1),
      ‖iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a u) 0‖ := by
  change ‖(ordinarySobolev q u hu).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro w
  rw [ordinarySobolev_coordinate, LinearIsometry.norm_map]
  have Heval := (iteratedFDeriv ℝ w.1.val
    (fun a : Space => EulerMeanSolenoidal.translation a u) 0).unit_le_opNorm
      (coordinateTuple_norm_le w.2)
  apply Heval.trans
  exact Finset.single_le_sum
    (f := fun n => ‖iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a u) 0‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_range.mpr w.1.isLt)

/-- Continuity of finitely many actual derivative tensors gives continuity in genuine Sobolev norm. -/
theorem ordinarySobolev_continuous {T : Type*} [TopologicalSpace T]
    (q : ℕ) (u : T → EulerMeanSolenoidal.L2) (hu : ∀ t, SmoothOrbit (u t))
    (hjet : ∀ n ≤ q, Continuous
      (fun t => iteratedFDeriv ℝ n (fun a : Space => EulerMeanSolenoidal.translation a (u t)) 0)) :
    Continuous (fun t => ordinarySobolev q (u t) (hu t)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  have heq : (fun t => (ordinarySobolev q (u t) (hu t)).val w) =
      fun t => ordinaryLift
        (iteratedFDeriv ℝ w.1.val (fun a : Space => EulerMeanSolenoidal.translation a (u t)) 0
          (coordinateTuple w.2)) := funext fun t => ordinarySobolev_coordinate q (u t) (hu t) w
  change Continuous (fun t => (ordinarySobolev q (u t) (hu t)).val w)
  rw [heq]
  exact ordinaryLift.continuous.comp
    ((continuous_eval_const (coordinateTuple w.2)).comp
      (hjet w.1.val (Nat.le_of_lt_succ w.1.isLt)))

end EulerMeanSmoothRepresentative
