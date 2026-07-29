/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.RectangleSymmetry
public import LeanPool.Odlyzko.ExplicitFormula.TartarPoitouTransform
public import LeanPool.Odlyzko.ExplicitFormula.WeightedRectangleArgumentPrinciple

/-!
# Completed Zeta Pole Contour

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A completed zeta pole factor used in the Odlyzko-bound argument. -/
noncomputable def completedZetaPoleFactor (s : ℂ) : ℂ :=
  s * (s - 1)

/-- A completed zeta pole log deriv used in the Odlyzko-bound argument. -/
noncomputable def completedZetaPoleLogDeriv (s : ℂ) : ℂ :=
  1 / s + 1 / (s - 1)

theorem completedZetaPoleLogDeriv_one_sub (s : ℂ) :
    completedZetaPoleLogDeriv (1 - s) =
      -completedZetaPoleLogDeriv s := by
  unfold completedZetaPoleLogDeriv
  grind

theorem meromorphicOrderAt_completedZetaPoleFactor_zero :
    meromorphicOrderAt completedZetaPoleFactor 0 = 1 := by
  have hg : meromorphicOrderAt (fun s : ℂ ↦ s - 1) 0 = 0 := by
    have ha : AnalyticAt ℂ (fun s : ℂ ↦ s - 1) 0 := by fun_prop
    rw [ha.meromorphicOrderAt_eq,
      ha.analyticOrderAt_eq_zero.mpr (by norm_num)]
    simp
  change meromorphicOrderAt
    ((fun s : ℂ ↦ s) * (fun s : ℂ ↦ s - 1)) 0 = 1
  rw [meromorphicOrderAt_mul (by fun_prop) (by fun_prop), hg]
  rw [add_zero, show (fun s : ℂ ↦ s) = id by grind]
  simp

theorem meromorphicOrderAt_completedZetaPoleFactor_one :
    meromorphicOrderAt completedZetaPoleFactor 1 = 1 := by
  have hf : meromorphicOrderAt (fun s : ℂ ↦ s) 1 = 0 := by
    have ha : AnalyticAt ℂ (fun s : ℂ ↦ s) 1 := by fun_prop
    rw [ha.meromorphicOrderAt_eq,
      ha.analyticOrderAt_eq_zero.mpr (by norm_num)]
    simp
  change meromorphicOrderAt
    ((fun s : ℂ ↦ s) * (fun s : ℂ ↦ s - 1)) 1 = 1
  rw [meromorphicOrderAt_mul (by fun_prop) (by fun_prop), hf]
  simp

theorem logDeriv_completedZetaPoleFactor_eq
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedZetaPoleFactor s =
      completedZetaPoleLogDeriv s := by
  unfold completedZetaPoleFactor completedZetaPoleLogDeriv
  rw [logDeriv_mul]
  · simp only [logDeriv_apply, deriv_sub_const,
      deriv_id'', one_div]
  · simp_all
  · grind
  · simp
  · simp

theorem rectangleIntegral_mul_completedZetaPoleLogDeriv
    {h : ℂ → ℂ} {a b u v : ℝ}
    (ha : a < 0) (hb : 1 < b) (hu : u < 0) (hv : 0 < v)
    (hh : ∀ z ∈ Icc a b ×ℂ Icc u v, AnalyticAt ℂ h z) :
    rectangleIntegral
        (fun s ↦ h s * completedZetaPoleLogDeriv s)
        (a + u * I) (b + v * I) =
      2 * Real.pi * I * (h 0 + h 1) := by
  classical
  have hab : a ≤ b := by linarith
  have huv : u ≤ v := by linarith
  have harg :=
    rectangleIntegral_mul_logDeriv_eq_two_pi_I_mul_sum
      (f := completedZetaPoleFactor) (h := h)
      (S := {0, 1}) (order := fun _ ↦ 1)
      hab huv
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact ⟨ha, by norm_num; linarith, hu, hv⟩
        · exact ⟨by norm_num; linarith, hb, hu, hv⟩)
      (by
        unfold completedZetaPoleFactor
        fun_prop)
      hh
      (by
        intro z _ hz
        rw [completedZetaPoleFactor, mul_eq_zero, sub_eq_zero] at hz
        simp_all)
      (by
        intro p hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact meromorphicOrderAt_completedZetaPoleFactor_zero
        · exact meromorphicOrderAt_completedZetaPoleFactor_one)
  have hboundary :
      rectangleIntegral
          (fun s ↦ h s * logDeriv completedZetaPoleFactor s)
          (a + u * I) (b + v * I) =
        rectangleIntegral
          (fun s ↦ h s * completedZetaPoleLogDeriv s)
          (a + u * I) (b + v * I) := by
    apply rectangleIntegral_congr
    · intro t ht
      congr 1
      apply logDeriv_completedZetaPoleFactor_eq
      · intro hz
        have him := congrArg Complex.im hz
        norm_num at him
        linarith
      · intro hz
        have him := congrArg Complex.im hz
        norm_num at him
        linarith
    · intro t ht
      congr 1
      apply logDeriv_completedZetaPoleFactor_eq
      · intro hz
        have him := congrArg Complex.im hz
        norm_num at him
        linarith
      · intro hz
        have him := congrArg Complex.im hz
        norm_num at him
        linarith
    · intro t ht
      congr 1
      apply logDeriv_completedZetaPoleFactor_eq
      · intro hz
        have hre := congrArg Complex.re hz
        norm_num at hre
        linarith
      · intro hz
        have hre := congrArg Complex.re hz
        norm_num at hre
        linarith
    · intro t ht
      congr 1
      apply logDeriv_completedZetaPoleFactor_eq
      · intro hz
        have hre := congrArg Complex.re hz
        norm_num at hre
        linarith
      · intro hz
        have hre := congrArg Complex.re hz
        norm_num at hre
        linarith
  simp_all

end NumberField.Odlyzko
