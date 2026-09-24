/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFixedRemainderMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFixedRieszMorrey
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Neg
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Zero

/-! # Morrey membership of a signed measurable pressure decomposition

Finite sums of the completed source fields and the measurable remainder
control the same identified pressure field on its target carrier.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-- A finite sum of measurable scalar fields with finite Morrey seminorm
again has finite Morrey seminorm. -/
theorem finite_sum_morreyNorm_lt_top
    {ι : Type*} {P κ : ℝ} (hP : 1 ≤ P) (s : Finset ι)
    {F : ι → ParabolicPoint → ℝ} (hF : ∀ j ∈ s, Measurable (F j))
    (hN : ∀ j ∈ s, morreyNorm P κ (F j) < ⊤) :
    morreyNorm P κ (fun w => ∑ j ∈ s, F j w) < ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, morreyNorm_zero (zero_lt_one.trans_le hP), ENNReal.zero_lt_top]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hFs (j : ι) (hj : j ∈ s) := hF j (Finset.mem_insert_of_mem hj)
    exact (morrey_norm_add_le hP (hF a (Finset.mem_insert_self _ _)).aemeasurable
      (Finset.measurable_sum s hFs).aemeasurable).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hN a (Finset.mem_insert_self _ _),
        ih hFs (fun j hj => hN j (Finset.mem_insert_of_mem hj))⟩)

/-- Finite source and remainder Morrey seminorms give the Morrey class of the
same pressure field in the signed decomposition on a measurable carrier. -/
theorem morreyVecMem_of_signed_pressure_decomposition
    {κ : ℝ} (hκ : 6 / 5 ≤ κ) {S : Set ParabolicPoint} (hS : MeasurableSet S)
    {Dp : ParabolicPoint → Vec3}
    {T F : Fin 3 → Fin 3 → ParabolicPoint → ℝ} {H : Fin 3 → ParabolicPoint → ℝ}
    (hT : ∀ j i, Measurable (T j i)) (hF : ∀ j i, Measurable (F j i))
    (hH : ∀ i, Measurable (H i))
    (hTN : ∀ j i, morreyNorm (6 / 5 : ℝ) κ (T j i) < ⊤)
    (hFN : ∀ j i, morreyNorm (6 / 5 : ℝ) κ (F j i) < ⊤)
    (hHN : ∀ i, morreyNorm (6 / 5 : ℝ) κ (S.indicator (H i)) < ⊤)
    (hid : ∀ i, (fun w => Dp w i) =ᵐ[volume.restrict S]
      (fun w => -(∑ j, T j i w) + H i w + ∑ j, F j i w)) :
    morreyVecMem (6 / 5 : ℝ) κ S Dp := by
  intro i
  let A : ParabolicPoint → ℝ := S.indicator (fun w => ∑ j, T j i w)
  let B : ParabolicPoint → ℝ := S.indicator (fun w => ∑ j, F j i w)
  let C : ParabolicPoint → ℝ := S.indicator (H i)
  have ha : Measurable A := (Finset.measurable_sum _ (fun j _ => hT j i)).indicator hS
  have hb : Measurable B := (Finset.measurable_sum _ (fun j _ => hF j i)).indicator hS
  have hc : Measurable C := (hH i).indicator hS
  have hAn : morreyNorm (6 / 5 : ℝ) κ A < ⊤ :=
    (morreyNorm_indicator_le (by norm_num) _ _).trans_lt
      (finite_sum_morreyNorm_lt_top (by norm_num) Finset.univ
        (fun j _ => hT j i) (fun j _ => hTN j i))
  have hBn : morreyNorm (6 / 5 : ℝ) κ B < ⊤ :=
    (morreyNorm_indicator_le (by norm_num) _ _).trans_lt
      (finite_sum_morreyNorm_lt_top (by norm_num) Finset.univ
        (fun j _ => hF j i) (fun j _ => hFN j i))
  have hnA : morreyNorm (6 / 5 : ℝ) κ (fun w => -A w) < ⊤ := by
    rw [morreyNorm_neg]
    exact hAn
  have hsum : morreyNorm (6 / 5 : ℝ) κ (fun w => -A w + C w + B w) < ⊤ :=
    (morrey_norm_add_le (by norm_num) (ha.neg.add hc).aemeasurable hb.aemeasurable).trans_lt
      (ENNReal.add_lt_top.mpr ⟨
        (morrey_norm_add_le (by norm_num) ha.neg.aemeasurable hc.aemeasurable).trans_lt
          (ENNReal.add_lt_top.mpr ⟨hnA, hHN i⟩), hBn⟩)
  have hDpN : morreyNorm (6 / 5 : ℝ) κ (S.indicator (fun w => Dp w i)) < ⊤ := by
    apply (routeA_morreyNorm_mono_ae (by norm_num : (0 : ℝ) ≤ 6 / 5) ?_).trans_lt hsum
    filter_upwards [(ae_restrict_iff' hS).mp (hid i)] with w hw
    by_cases hs : w ∈ S
    · simp only [A, B, C, Set.indicator_of_mem hs, hw hs, le_refl]
    · simp only [A, B, C, Set.indicator_of_notMem hs, neg_zero, add_zero, le_refl]
  apply (morreyBallNorm_le_two_rpow_mul_morreyNorm (by norm_num) hκ _).trans_lt
  exact ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num))) hDpN

end CKN.Core.Step4
