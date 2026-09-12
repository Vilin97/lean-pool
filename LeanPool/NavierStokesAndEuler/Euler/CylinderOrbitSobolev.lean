/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSmoothOrbit
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder

/-!
# Actual cylinder Sobolev arrays of smooth mixed translation orbits

Every coordinate is the literal L² derivative in its ordered spatial/angular
word. The complete Sobolev norm is bounded by the exact finite word sum, and
uniform-time mixed orbit regularity yields a continuous Sobolev path.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerPressureSpatialRegularity
  EulerLpCylinderTranslation EulerCylinderSobolevSpace EulerParameterWordGevrey
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- Iterating a genuine orbit derivative equals the next actual tensor derivative. -/
theorem iteratedFDeriv_orbitDerivative (u : LiftL2 period) (hu : SmoothOrbit period u)
    (v : LiftTangent) (n : ℕ) (a : LiftTangent) (m : Fin n → LiftTangent) :
    iteratedFDeriv ℝ n (fun b : LiftTangent => translate period b (orbitDerivative period u v)) a m
        =
      iteratedFDeriv ℝ (n+1) (fun b : LiftTangent => translate period b u) a (Fin.snoc m v) := by
  let F : LiftTangent → LiftL2 period := fun b => translate period b u
  have h := (ContinuousLinearMap.apply ℝ (LiftL2 period) v).iteratedFDeriv_comp_left
    (hu.fderiv_right (m := ∞) (by simp)).contDiffAt (x := a) (i := n) (by simp)
  have he := congrArg (fun G => G m) h
  change iteratedFDeriv ℝ n (fun b => fderiv ℝ F b v) a m =
    iteratedFDeriv ℝ n (fderiv ℝ F) a m v at he
  have horbit : (fun b : LiftTangent => translate period b (orbitDerivative period u v)) =
      fun b : LiftTangent => fderiv ℝ F b v := funext (fun b => orbitDerivative_translation period
          u hu v b)
  rw [horbit,he,iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_snoc,Fin.snoc_last]
  rfl

/-- Each actual strong jet word is its ordered mixed derivative in the true L² orbit. -/
theorem spatialJet_word (n q : ℕ) (hn : n ≤ q) (u : LiftL2 period)
    (hu : SmoothOrbit period u) (w : Fin n → Fin 4) :
    (spatialJet period q u hu).word w =
      wordDerivative standardDirection (fun a : LiftTangent => translate period a u) w 0 := by
  induction n generalizing q u with
  | zero => simp only [SpatialJet.word_zero,wordDerivative_zero,translate_zero]
  | succ n ih =>
    cases q with
    | zero => omega
    | succ q =>
      rw [spatialJet,SpatialJet.word_succ]
      rw [ih q (by omega) (orbitDerivative period u (standardDirection (w (Fin.last n))))
        (orbitDerivative_smooth period u hu (standardDirection (w (Fin.last n)))) (Fin.init w)]
      unfold wordDerivative
      rw [iteratedFDeriv_orbitDerivative period u hu]
      congr 1
      change Fin.snoc (Fin.init (fun j => standardDirection (w j)))
        (standardDirection (w (Fin.last n))) = (fun j => standardDirection (w j))
      exact Fin.snoc_init_self (fun j => standardDirection (w j))

/-- The actual coordinates of the complete Sobolev realization. -/
theorem sobolev_coordinate (q : ℕ) (u : LiftL2 period) (hu : SmoothOrbit period u)
    (w : SobolevWord q) :
    (sobolev period q u hu).val w =
      wordDerivative standardDirection (fun a : LiftTangent => translate period a u) w.2 0 :=
  spatialJet_word period w.1.val q (Nat.le_of_lt_succ w.1.isLt) u hu w.2

/-- A complete Sobolev norm is controlled by the genuine fixed-order word sum. -/
theorem sobolev_norm_le_baseSize (q : ℕ) (u : LiftL2 period) (hu : SmoothOrbit period u) :
    ‖sobolev period q u hu‖ ≤ baseSize standardDirection q (fun a : LiftTangent => translate period
        a u) 0 := by
  change ‖(sobolev period q u hu).val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (baseSize_nonneg _ _ _ _)).2
  intro w
  rw [sobolev_coordinate]
  calc
    _ ≤ wordSum standardDirection (fun a : LiftTangent => translate period a u) w.1.val 0 :=
      Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ w.2)
    _ ≤ _ := Finset.single_le_sum (fun n _ => wordSum_nonneg _ _ n _) (Finset.mem_range.mpr
        w.1.isLt)

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Every time slice inherits genuine full mixed orbit smoothness. -/
theorem path_evaluation_smooth (p : C(K, LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p)) (t : K) :
    SmoothOrbit period (p t) := by
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K,LiftL2 period)) (F := LiftL2 period) (ContinuousMap.evalCLM ℝ t)).comp hp

/-- A time-slice word is evaluation of the actual uniform-time derivative word. -/
theorem path_word_evaluation (p : C(K, LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p))
    {n : ℕ} (w : Fin n → Fin 4) (t : K) :
    wordDerivative standardDirection (fun a : LiftTangent => translate period a (p t)) w 0 =
      wordDerivative standardDirection (fun a : LiftTangent => pathTranslate period a p) w 0 t := by
  have h := (ContinuousMap.evalCLM ℝ t : C(K,LiftL2 period) →L[ℝ] LiftL2
      period).iteratedFDeriv_comp_left
    (hp.contDiffAt (x := (0 : LiftTangent))) (i := n) (by simp)
  exact congrArg (fun D => D (fun j => standardDirection (w j))) h

/-- Genuine uniform-time mixed regularity gives continuity in every complete Sobolev norm. -/
theorem path_sobolev_continuous (q : ℕ) (p : C(K, LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p)) :
    Continuous (fun t => sobolev period q (p t) (path_evaluation_smooth period p hp t)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro w
  have he : (fun t => (sobolev period q (p t) (path_evaluation_smooth period p hp t)).val w) =
      fun t => wordDerivative standardDirection (fun a : LiftTangent => pathTranslate period a p)
          w.2 0 t := by
    funext t
    rw [sobolev_coordinate,path_word_evaluation period p hp]
  change Continuous (fun t => (sobolev period q (p t) (path_evaluation_smooth period p hp t)).val w)
  rw [he]
  exact (wordDerivative standardDirection (fun a : LiftTangent => pathTranslate period a p) w.2
      0).continuous

/-- The actual continuous Sobolev path. -/
def sobolevPath (q : ℕ) (p : C(K, LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p)) : C(K,SobolevSpace period
        q) :=
  ⟨fun t => sobolev period q (p t) (path_evaluation_smooth period p hp t),path_sobolev_continuous
      period q p hp⟩

@[simp] theorem sobolevPath_value (q : ℕ) (p : C(K, LiftL2 period))
    (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a p)) (t : K) :
    value period (sobolevPath period q p hp t) = p t := sobolev_value period q _ _


end EulerCylinderSmoothOrbit
