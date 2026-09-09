/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SpatialSobolevInverse
import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Exact differentiated projected-pressure equations for actual translation Sobolev jets. -/

@[expose] public section

noncomputable section

namespace EulerPressureJetIdentities

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerLiftedPressure
  EulerPressureSpatialRegularity EulerLiftedWeakDerivative EulerSpatialSobolevInverse
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Strong derivatives preserve the actual closed lifted gradient subspace. -/
theorem gradientSpace_translation_derivative (κ : ℝ) (m : Vector3) (a : LiftTangent)
    {f f' : LiftL2 period} (hf : f ∈ gradientSpace period κ m)
    (hder : HasDerivAt (fun t => translation period (translationPath period a t) f) f' 0) :
    f' ∈ gradientSpace period κ m := by
  have hlim := hder.tendsto_slope_zero
  simp only [zero_add, translationPath_zero, translation_zero] at hlim
  apply (gradientSpace_closed period κ m).mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun t => (gradientSpace period κ m).smul_mem _
    ((gradientSpace period κ m).sub_mem
      (gradientSpace_translation_mem period κ m (translationPath period a t) hf) hf)

namespace SpatialJet

variable {period} {directions : Fin 4 → LiftTangent}

/-- Actual strong derivative words are independent of the chosen derivative witness tree. -/
theorem word_unique {s t n : ℕ} {f g : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (K : EulerSpatialSobolevInverse.SpatialJet period directions t g)
    (hfg : f = g) (hn : n ≤ s) (hm : n ≤ t) (w : Fin n → Fin 4) : J.word w = K.word w := by
  subst g
  induction n with
  | zero => simp
  | succ n ih =>
    have hbase := ih (by omega) (by omega) (Fin.tail w)
    have hJ := J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0)
    have hK := K.word_hasDerivAt (by omega : n < t) (Fin.tail w) (w 0)
    rw [hbase] at hJ
    simpa only [Fin.cons_self_tail] using hJ.unique hK

/-- Every valid word of a gradient-valued Sobolev jet remains in the gradient subspace. -/
theorem word_mem_gradientSpace {s n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (hf : f ∈ gradientSpace period κ m) (hn : n ≤ s)
    (w : Fin n → Fin 4) : J.word w ∈ gradientSpace period κ m := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have h := gradientSpace_translation_derivative period κ m (directions (w 0))
      (ih (by omega) (Fin.tail w))
      (J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0))
    simpa only [Fin.cons_self_tail] using h

/-- Every valid word of a solenoidal Sobolev jet remains genuinely weakly solenoidal. -/
theorem word_mem_divergenceFreeSpace {s n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (hf : f ∈ divergenceFreeSpace period κ m) (hn : n ≤ s)
    (w : Fin n → Fin 4) : J.word w ∈ divergenceFreeSpace period κ m := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    have h := divergenceFree_translation_derivative period κ m (directions (w 0))
      (ih (by omega) (Fin.tail w))
      (J.word_hasDerivAt (by omega : n < s) (Fin.tail w) (w 0))
    simpa only [Fin.cons_self_tail] using h

/-- A bounded operator commuting with actual translations maps genuine spatial jets. -/
def map (L : LiftL2 period →L[ℝ] LiftL2 period)
    (hL : ∀ a f, translation period a (L f) = L (translation period a f))
    {s : ℕ} {f : LiftL2 period} (J : EulerSpatialSobolevInverse.SpatialJet period directions s f) :
    EulerSpatialSobolevInverse.SpatialJet period directions s (L f) :=
  match J with
  | .zero f => .zero (L f)
  | .succ df lower hd => .succ (fun i => L (df i)) (fun i => map L hL (lower i))
      (fun i => by
        have h := L.hasFDerivAt.comp_hasDerivAt 0 (hd i)
        convert h using 1 <;> first | rfl | (funext t; exact hL _ _))

theorem map_word {s n : ℕ} {f : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (L : LiftL2 period →L[ℝ] LiftL2 period)
    (hL : ∀ a f, translation period a (L f) = L (translation period a f))
    (w : Fin n → Fin 4) : (map L hL J).word w = L (J.word w) := by
  induction J generalizing n with
  | zero f => cases n <;> simp [map, EulerSpatialSobolevInverse.SpatialJet.word]
  | succ df lower hd ih =>
    cases n with
    | zero => simp
    | succ n => simpa only [map, EulerSpatialSobolevInverse.SpatialJet.word_succ] using
        (ih (w (Fin.last n)) (Fin.init w))

/-- At every derivative word, the actual projected equation differentiates exactly. -/
theorem pressure_word_projected_equation {s n : ℕ} {A : SmoothCoefficient period}
    {f : LiftL2 period} (K : CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hn : n ≤ s) (w : Fin n → Fin 4) :
    gradientProjection period κ m
      ((EulerSpatialSobolevInverse.SpatialJet.multiply K (J.solvePressure K κ m c hc hpos)).word w)
          =
      gradientProjection period κ m (J.word w) := by
  let P := J.solvePressure K κ m c hc hpos
  let M := EulerSpatialSobolevInverse.SpatialJet.multiply K P
  have heq : gradientProjection period κ m (A.operator (A.pressure κ m c hc hpos f)) =
      gradientProjection period κ m f :=
    liftedPressure_equation period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f
  have h := word_unique (map (gradientProjection period κ m)
      (gradientProjection_translation period κ m) M)
    (map (gradientProjection period κ m) (gradientProjection_translation period κ m) J) heq hn hn w
  simpa only [map_word] using h

/-- The actual derivative word is the coercive inverse applied to its differentiated source
minus the genuine product commutator. -/
theorem pressure_word_inverse {s n : ℕ} {A : SmoothCoefficient period}
    {f : LiftL2 period} (K : CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hn : n ≤ s) (w : Fin n → Fin 4) :
    (J.solvePressure K κ m c hc hpos).word w = A.pressure κ m c hc hpos
      (J.word w - ((EulerSpatialSobolevInverse.SpatialJet.multiply K
        (J.solvePressure K κ m c hc hpos)).word w -
          A.operator ((J.solvePressure K κ m c hc hpos).word w))) := by
  let P := J.solvePressure K κ m c hc hpos
  let M := EulerSpatialSobolevInverse.SpatialJet.multiply K P
  apply liftedPressure_unique period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos
  · exact word_mem_gradientSpace P κ m
      (liftedPressure_mem period κ m A.coefficient A.measurable A.bound A.norm_bound c hc hpos f)
          hn w
  · have hp := pressure_word_projected_equation K J κ m c hc hpos hn w
    change gradientProjection period κ m (A.operator (P.word w)) =
      gradientProjection period κ m (J.word w - (M.word w - A.operator (P.word w)))
    rw [map_sub, map_sub, hp]
    abel

/-- The rigorous triangular pressure estimate before its product commutator is summed. -/
theorem pressure_word_norm_le {s n : ℕ} {A : SmoothCoefficient period}
    {f : LiftL2 period} (K : CoefficientJet period directions s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period directions s f)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (hn : n ≤ s) (w : Fin n → Fin 4) :
    ‖(J.solvePressure K κ m c hc hpos).word w‖ ≤ c⁻¹ *
      (‖J.word w‖ + ‖(EulerSpatialSobolevInverse.SpatialJet.multiply K
        (J.solvePressure K κ m c hc hpos)).word w -
          A.operator ((J.solvePressure K κ m c hc hpos).word w)‖) := by
  calc
    _ = ‖A.pressure κ m c hc hpos (J.word w -
        ((EulerSpatialSobolevInverse.SpatialJet.multiply K (J.solvePressure K κ m c hc hpos)).word
            w -
          A.operator ((J.solvePressure K κ m c hc hpos).word w)))‖ := by
      congr 1
      exact pressure_word_inverse K J κ m c hc hpos hn w
    _ ≤ _ := (A.pressure_norm κ m c hc hpos _).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hc.le))

end SpatialJet

end EulerPressureJetIdentities
