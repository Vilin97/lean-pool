/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderGraphPath
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData

@[expose] public section

/-! Every smooth representative of a genuine all-order field tower has
continuous spatial L² restrictions, including all cylinder derivative words.
The graph estimate loses one angular derivative, with no frequency factor. -/

noncomputable section

namespace EulerAllOrderCorrectionData.FieldTower

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerStrongSmoothJet EulerMetricTransport
  EulerTransportDerivatives EulerCylinderGraphTrace
open scoped ContDiff

variable {P T : ℝ} [Fact (0 < P)] (A : EulerAllOrderCorrectionData.FieldTower P T)

/-- The prescribed derivative coordinate is a genuine continuous L² path. -/
def derivativeWordPath (s n : ℕ) (w : Fin n → Fin 4) (hn : n ≤ s) :
    C(Icc (0 : ℝ) T,LiftL2 P) :=
  (wordOperator P (⟨⟨n,Nat.lt_succ_of_le hn⟩,w⟩ : SobolevWord s)).compLeftContinuous
    ℝ (Icc (0 : ℝ) T) (A.realization s)

variable (f : Icc (0 : ℝ) T → LiftDomain P → Vector3)
  (hf : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (f t) x))
  (hrep : ∀ t, (A.field t : LiftDomain P → Vector3) =ᵐ[liftMeasure P] f t)

include hf hrep in
theorem derivativeWordPath_ae (s n : ℕ) (w : Fin n → Fin 4) (hn : n ≤ s)
    (t : Icc (0 : ℝ) T) :
    (A.derivativeWordPath s n w hn t : LiftDomain P → Vector3) =ᵐ[liftMeasure P]
      iteratedFieldDerivative P w (f t) := by
  have h := jet_word_ae P hn (value P (A.realization s t))
    (toJet P (A.realization s t)) w (f t)
    (by simpa only [A.value_eq] using hrep t) (hf t)
  rw [toJet_word P (A.realization s t) hn w] at h
  exact h

theorem derivativeWordPath_norm_le (s n : ℕ) (w : Fin n → Fin 4) (hn : n ≤ s)
    (t : Icc (0 : ℝ) T) :
    ‖A.derivativeWordPath s n w hn t‖ ≤ ‖A.realization s t‖ :=
  word_norm_le P (A.realization s t) (⟨⟨n,Nat.lt_succ_of_le hn⟩,w⟩ : SobolevWord s)

variable (θ : Vector3 → AddCircle P) (hθ : Continuous θ)

include hf hrep in
/-- The actual angular derivative used by the graph trace is another
coordinate of the same all-order tower. -/
theorem graphWord_angular_ae (n : ℕ) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    (A.derivativeWordPath (n+1) (n+1) (Fin.cons 0 w) le_rfl t :
      LiftDomain P → Vector3) =ᵐ[liftMeasure P]
      fieldDerivative P (0,1) (iteratedFieldDerivative P w (f t)) := by
  simpa only [iteratedFieldDerivative_succ,Fin.cons_zero,Fin.tail_cons,
    standardDirection_zero] using
    A.derivativeWordPath_ae f hf hrep (n+1) (n+1) (Fin.cons 0 w) le_rfl t

/-- Graph restriction of an arbitrary actual cylinder derivative word,
constructed directly as a continuous spatial L² path. -/
def graphWordPath (n : ℕ) (w : Fin n → Fin 4) :
    C(Icc (0 : ℝ) T,Lp Vector3 2 (volume : Measure Vector3)) :=
  EulerCylinderGraphTrace.graphPath P
    (A.derivativeWordPath (n+1) n w (by omega))
    (A.derivativeWordPath (n+1) (n+1) (Fin.cons 0 w) le_rfl)
    (fun t => iteratedFieldDerivative P w (f t))
    (fun t => iteratedFieldDerivative_smooth P w (f t) (hf t))
    (A.derivativeWordPath_ae f hf hrep (n+1) n w (by omega))
    (A.graphWord_angular_ae f hf hrep n w) θ hθ

theorem graphWordPath_ae (n : ℕ) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    (A.graphWordPath f hf hrep θ hθ n w t : Vector3 → Vector3) =ᵐ[volume]
      fun x => iteratedFieldDerivative P w (f t) (x,θ x) :=
  graphPathValue_ae P _ _ _ _ _ _ θ hθ t

theorem graphWordPath_norm_sq_le (n : ℕ) (w : Fin n → Fin 4) (t : Icc (0 : ℝ) T) :
    ‖A.graphWordPath f hf hrep θ hθ n w t‖^2 ≤
      (2/P+2*P)*‖A.realization (n+1) t‖^2 := by
  have h := graph_norm_sq_le P
    (iteratedFieldDerivative P w (f t))
    (iteratedFieldDerivative_smooth P w (f t) (hf t))
    (A.derivativeWordPath (n+1) n w (by omega) t)
    (A.derivativeWordPath (n+1) (n+1) (Fin.cons 0 w) le_rfl t)
    (A.derivativeWordPath_ae f hf hrep (n+1) n w (by omega) t)
    (A.graphWord_angular_ae f hf hrep n w t) θ hθ _
    (A.graphWordPath_ae f hf hrep θ hθ n w t)
  have h0 := pow_le_pow_left₀ (norm_nonneg _)
    (A.derivativeWordPath_norm_le (n+1) n w (by omega) t) 2
  have h1 := pow_le_pow_left₀ (norm_nonneg _)
    (A.derivativeWordPath_norm_le (n+1) (n+1) (Fin.cons 0 w) le_rfl t) 2
  have hP : 0 < P := Fact.out
  calc
    _ ≤ _ := h
    _ ≤ (2/P)*‖A.realization (n+1) t‖^2+(2*P)*‖A.realization (n+1) t‖^2 :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (by positivity))
        (mul_le_mul_of_nonneg_left h1 (by positivity))
    _ = _ := by ring

end EulerAllOrderCorrectionData.FieldTower
