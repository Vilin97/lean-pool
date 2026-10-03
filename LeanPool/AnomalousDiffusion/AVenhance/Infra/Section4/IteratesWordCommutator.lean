/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesCommutator

/-! Exact all-order drift commutators, before quantitative norm estimates. -/

@[expose] public section

noncomputable section
open Homogenization
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- The one-coordinate drift commutator applied to the actual scalar field. -/
def iterateVelocityCommutator (b : AmnrSpace → Vec 2) (i : Fin 2)
    (f : AmnrSpace → ℝ) (z : AmnrSpace) : ℝ :=
  fderiv ℝ f z (0, fderiv ℝ b z (0, basisVec i))

/-- Ordered commutator expansion. The outer derivative differentiates all
previous errors, and the new error differentiates the actual velocity once. -/
def iterateWordMaterialError (b : AmnrSpace → Vec 2) :
    List (Fin 2) → (AmnrSpace → ℝ) → AmnrSpace → ℝ
  | [], _ => fun _ => 0
  | i :: w, f => fun z =>
      amnrOp b (some i) (iterateWordMaterialError b w f) z +
      iterateVelocityCommutator b i (amnrWord b (w.map some) f) z

/-- Finite words preserve smoothness on an open space-time domain. -/
theorem iterate_amnrWord_smoothOn {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (w : List (Option (Fin 2))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (amnrWord b w f) U := by
  apply contDiffOn_infty.mpr
  intro n
  exact amnrWord_contDiffOn hU (hb.of_le (by simp)) (hf.of_le (by simp)) w
    (N := n + w.length) (by omega)

/-- The velocity commutator is a smooth, explicitly differentiated field. -/
theorem iterateVelocityCommutator_smoothOn {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (i : Fin 2) : ContDiffOn ℝ (⊤ : ℕ∞) (iterateVelocityCommutator b i f) U := by
  have hdb : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ b) U :=
    hb.fderiv_of_isOpen hU (by simp)
  have hdf : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) U :=
    hf.fderiv_of_isOpen hU (by simp)
  exact hdf.clm_apply (contDiffOn_const.prodMk (hdb.clm_apply contDiffOn_const))

/-- Every recursively expanded error is smooth; this justifies differentiating
its sum in the next induction step rather than assuming a commutator equation. -/
theorem iterateWordMaterialError_smoothOn {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (w : List (Fin 2)) : ContDiffOn ℝ (⊤ : ℕ∞) (iterateWordMaterialError b w f) U := by
  induction w with
  | nil => exact contDiffOn_const
  | cons i w ih =>
    have hd := iterate_amnrWord_smoothOn hU hb ih [some i]
    exact hd.add (iterateVelocityCommutator_smoothOn hU hb
      (iterate_amnrWord_smoothOn hU hb hf (w.map some)) i)

/-- Commute the actual material operator past any ordered spatial word.
The entire drift error is the explicit recursive expansion above. -/
theorem iterate_spatial_word_material_expansion {U : Set AmnrSpace} (hU : IsOpen U)
    {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    (hb : ContDiffOn ℝ (⊤ : ℕ∞) b U) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (w : List (Fin 2)) :
    Set.EqOn (amnrWord b (w.map some) (amnrOp b none f))
      (fun z => amnrOp b none (amnrWord b (w.map some) f) z +
        iterateWordMaterialError b w f z) U := by
  induction w with
  | nil => intro z _; simp only [List.map_nil, amnrWord, iterateWordMaterialError, add_zero]
  | cons i w ih =>
    intro z hz
    have hn := Filter.eventuallyEq_of_mem (hU.mem_nhds hz) (fun y hy => ih hy)
    have hw := iterate_amnrWord_smoothOn hU hb hf (w.map some)
    have hm := iterate_amnrWord_smoothOn hU hb hw [none]
    have he := iterateWordMaterialError_smoothOn hU hb hf w
    have hmd := (hm.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    change DifferentiableAt ℝ (amnrOp b none (amnrWord b (w.map some) f)) z at hmd
    have hed := (he.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
    have hc := iterate_spatial_material_commutator
      ((hw.contDiffAt (hU.mem_nhds hz)).of_le (by simp))
      ((hb.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)) i
    simp only [List.map_cons, amnrWord, iterateWordMaterialError]
    change fderiv ℝ (amnrWord b (w.map some) (amnrOp b none f)) z (0, basisVec i) = _
    rw [hn.fderiv_eq, fderiv_fun_add hmd hed]
    change amnrOp b (some i) (amnrOp b none (amnrWord b (w.map some) f)) z +
      amnrOp b (some i) (iterateWordMaterialError b w f) z = _
    rw [hc]
    unfold iterateVelocityCommutator
    ring

end AVenhance.Infra.Section4
