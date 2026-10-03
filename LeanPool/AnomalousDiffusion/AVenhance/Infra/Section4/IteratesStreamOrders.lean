/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesMatrixContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFirstStreamTimeSum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesFirstStreamFactorials
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesStreamCoefficient

/-! Exact principal, first, and high stream orders in the integrated flux. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Split a finite sum into its zero, first, and high coefficient orders. -/
theorem iterate_three_order_list_sum {α : Type*} (P : List α) (n : α → ℕ) (f : α → ℝ) :
    (P.map f).sum = ((P.filter (fun p => n p == 0)).map f).sum +
      ((P.filter (fun p => n p == 1)).map f).sum +
      ((P.filter (fun p => decide (2 ≤ n p))).map f).sum := by
  induction P with
  | nil => simp
  | cons p P ih =>
    by_cases hz : n p = 0
    · simp [hz, ih]; ring
    · by_cases ho : n p = 1
      · simp [ho, ih]; ring
      · have hh : 2 ≤ n p := by omega
        simp [hz, ho, hh, ih]; ring

end AVenhance.Infra.Section4
