/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.TemperatureForcedEnergy

/-! Finite actual products in the spatial drift commutator. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4

/-- Indices and derivative words describing one differentiated drift product. -/
structure AmnrDriftTerm where
  /-- Velocity component in the differentiated drift product. -/
  row : Fin 2
  /-- Spatial direction of the scalar derivative in the drift product. -/
  column : Fin 2
  /-- Spatial derivative word applied to the velocity coefficient. -/
  coefficientWord : List (Fin 2)
  /-- Spatial derivative word applied to the scalar factor. -/
  scalarWord : List (Fin 2)

/-- The actual product represented by one differentiated drift term. -/
def amnrDriftTermValue (b : AmnrSpace → Vec 2) (f : AmnrSpace → ℝ)
    (q : AmnrDriftTerm) : AmnrSpace → ℝ :=
  amnrWord b (q.coefficientWord.map some) (amnrVelocityGradient b q.row q.column) *
    amnrWord b (q.scalarWord.map some) f

/-- A coordinate derivative can fall on either actual factor. -/
def amnrDriftDerivativeTerms (i : Fin 2) (q : AmnrDriftTerm) : List AmnrDriftTerm :=
  [⟨q.row, q.column, i :: q.coefficientWord, q.scalarWord⟩,
    ⟨q.row, q.column, q.coefficientWord, i :: q.scalarWord⟩]

theorem amnrDriftTermValue_contDiff {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (q : AmnrDriftTerm) :
    ContDiff ℝ (⊤ : ℕ∞) (amnrDriftTermValue b f q) := by
  exact (contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn
    (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn q.row q.column)
    (q.coefficientWord.map some))).mul
      (contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn hf.contDiffOn
        (q.scalarWord.map some)))

/-- Each step is the product rule for actual derivatives, without an estimate
or an assumed commutator expansion. -/
theorem amnrDriftDerivativeTerms_value {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin 2) (q : AmnrDriftTerm) :
    amnrOp b (some i) (amnrDriftTermValue b f q) =
      ((amnrDriftDerivativeTerms i q).map (amnrDriftTermValue b f)).sum := by
  have hA := contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn
    (amnrVelocityGradient_contDiffOn_infty isOpen_univ hb.contDiffOn q.row q.column)
    (q.coefficientWord.map some))
  have hF := contDiffOn_univ.mp (amnrWord_contDiffOn_infty isOpen_univ hb.contDiffOn hf.contDiffOn
    (q.scalarWord.map some))
  funext z
  unfold amnrDriftTermValue amnrDriftDerivativeTerms amnrOp
  rw [fderiv_mul (hA.differentiable (by simp) z) (hF.differentiable (by simp) z)]
  simp only [List.sum_cons, List.sum_nil, Pi.add_apply,
    add_zero, Pi.mul_apply, List.map, amnrWord, amnrOp,
    add_apply, smul_apply, smul_eq_mul]
  ring

end AVenhance.Infra.Section4
