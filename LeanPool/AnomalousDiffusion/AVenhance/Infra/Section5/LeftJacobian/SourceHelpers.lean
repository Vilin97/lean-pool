/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SourceErrors
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TEquationRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmSourceTelescope

/-!: calculus helpers for the source material equation (local copies of the
private lemmas of `SourceMaterialEquation`). -/

@[expose] public section

noncomputable section

open Homogenization
open scoped ContDiff

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

theorem vecDiv_add_of_differentiableAt
    {V W : Vec 2 → Vec 2} {x : Vec 2}
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) :
    vecDiv (fun y => V y + W y) x = vecDiv V x + vecDiv W x := by
  unfold vecDiv spaceGrad
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hVi : DifferentiableAt ℝ (fun y => V y i) x := by
    have h := (ContinuousLinearMap.proj i).differentiableAt.comp x hV
    simpa [Function.comp_def] using h
  have hWi : DifferentiableAt ℝ (fun y => W y i) x := by
    have h := (ContinuousLinearMap.proj i).differentiableAt.comp x hW
    simpa [Function.comp_def] using h
  change fderiv ℝ ((fun y => V y i) + (fun y => W y i)) x
      (basisVec i) = _
  rw [fderiv_add hVi hWi]
  rfl

theorem vecDiv_add3_of_differentiableAt
    {U V W : Vec 2 → Vec 2} {x : Vec 2}
    (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    (hW : DifferentiableAt ℝ W x) :
    vecDiv (fun y => U y + V y + W y) x = vecDiv U x + vecDiv V x + vecDiv W x := by
  have h1 := vecDiv_add_of_differentiableAt hU hV
  have h2 := vecDiv_add_of_differentiableAt (hU.add hV) hW
  rw [← h1]
  exact h2

theorem stDiv_eq_vecDiv
    {F : ST → Vec 2} {t : ℝ} {x : Vec 2}
    (hF : DifferentiableAt ℝ F (t, x)) :
    stDiv F (t, x) = vecDiv (fun y => F (t, y)) x := by
  let B : ℝ → Vec 2 → Vec 2 := fun s y => F (s, y)
  have hB : DifferentiableAt ℝ (Function.uncurry B) (t, x) := by
    simpa [B, Function.uncurry] using hF
  have hslice : DifferentiableAt ℝ (B t) x := by
    exact hB.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x) |>.differentiableAt
  have hcoord (i : Fin 2) :
      (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec i)) i =
        fderiv ℝ (fun y => B t y i) x (basisVec i) := by
    have hvec := fderiv_uncurry_vector_spatial
      (B := B) (t := t) (x := x) (v := basisVec i) hB
    have h := congrArg (fun v : Vec 2 => v i) hvec
    rw [h, fderiv_apply hslice i]
    simp [ContinuousLinearMap.comp_apply]
  unfold stDiv vecDiv spaceGrad
  simp only [Fin.sum_univ_two]
  change (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec 0)) 0 +
      (fderiv ℝ (Function.uncurry B) (t, x) (0, basisVec 1)) 1 =
    (fderiv ℝ (fun y => B t y 0) x (basisVec 0)) +
      (fderiv ℝ (fun y => B t y 1) x (basisVec 1))
  rw [hcoord 0, hcoord 1]

/-- The terminal `A_{Jcut} q_{Jcut}` tail of `d`. -/
def terminalTail {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) : Vec 2 → Vec 2 :=
  fun y i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
    I.Amnr hΦ m κ n T (Jcut β) t y i j k *
      I.qMNR κ m n (Jcut β) t j k

end AVenhance.Infra.Section5.LeftJacobian

end
