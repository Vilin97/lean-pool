/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFixedForceMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsRieszMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTBoundedRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsRemainderGlobal
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Neg
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Zero

/-! # Morrey membership of a signed measurable pressure decomposition

Finite sums of the completed source fields and the measurable remainder
control the same identified pressure field on its target carrier.
-/

@[expose] public section

section

/-! # Morrey control of a windowed Riesz field

A completed-operator representative inherits the finite source Morrey
seminorm once the bounded spatial support and the full-time slice membership
are supplied by the fixed product restriction.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- Product restriction supplies the bounded support and full-time slice
membership needed to transfer a source Morrey bound to its Riesz field. -/
theorem window_riesz_field_morrey_lt_top
    (j i : Fin 3) {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9)
    {F T : ParabolicPoint → ℝ} {x : Vec3} {r : ℝ} (hr : 0 < r)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (hF : AEMeasurable ((vec3Ball x r ×ˢ J).indicator F) volume)
    (hFs : ∀ᵐ s ∂volume.restrict J,
      MemLp (fun y => F (y, s)) (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hT : AEMeasurable T volume)
    (hident : ∀ᵐ s ∂volume, (fun y => T (y, s)) =ᵐ[volume]
      rieszSecondGradientExtensionOperator
        (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
        (fun y => (vec3Ball x r ×ˢ J).indicator F (y, s)))
    (hFnorm : morreyNorm (6 / 5 : ℝ) κ ((vec3Ball x r ×ˢ J).indicator F) < ⊤) :
    morreyNorm (6 / 5 : ℝ) κ T < ⊤ := by
  obtain ⟨L, hL⟩ := (CKN.Foundation.Parabolic.isCompact_closure_vec3Ball
    hr).isBounded.exists_norm_le
  apply pressure_riesz_morreyNorm_lt_top j i hκ hκhi hF
    (memLp_product_indicator_slices (isOpen_vec3Ball _ _).measurableSet hJ hFs)
    (L := L) ?_ hT hident hFnorm
  intro y s hy
  exact Set.indicator_of_notMem (fun h => (not_le.mpr hy) (hL y (subset_closure h.1))) F

end CKN.Core.Step4
end

end

section

/-! # Morrey control from almost-everywhere remainder slice bounds

An almost-everywhere spatial bound is sufficient for the measurable
remainder selected by weak derivative uniqueness. A bounded representative
satisfies the pointwise consumer and preserves the original Morrey class.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- A finite temporal majorant controls the original measurable remainder
in Morrey space even when the spatial bound initially holds only almost
everywhere on each time slice. -/
theorem pressure_remainder_indicator_morrey_lt_top_of_ae_slice_bound
    {κ : ℝ} (hκlo : 3 / 2 ≤ κ) (hκhi : κ ≤ 25 / 9)
    {H : ParabolicPoint → ℝ} (hH : Measurable H)
    {M : ℝ → ℝ≥0∞} (hM : AEMeasurable M volume)
    {A : Set ParabolicPoint} {B : Set Vec3}
    (hA : MeasurableSet A) (hAB : ∀ w ∈ A, w.1 ∈ B)
    (hB : MeasurableSet B) (hBfinite : volume B < ⊤)
    (hbound : ∀ᵐ s ∂volume, ∀ᵐ x ∂volume, (x, s) ∈ A → ‖H (x, s)‖ₑ ≤ M s)
    (hMfinite : (∫⁻ s, M s ^ (3 / 2 : ℝ)) < ⊤) :
    morreyNorm (6 / 5 : ℝ) κ (A.indicator H) < ⊤ := by
  obtain ⟨H', hm, heq, hb⟩ := exists_measurable_spatially_bounded_representative hH hM hA hbound
  have hN := pressure_remainder_indicator_morreyNorm_lt_top hκlo hκhi hA hAB
    hm.aemeasurable hM hB hBfinite
    (hb.mono (fun _ hs x _hx => hs x)) hMfinite
  apply (routeA_morreyNorm_mono_ae (by norm_num : (0 : ℝ) ≤ 6 / 5) ?_).trans_lt hN
  filter_upwards [(ae_restrict_iff' hA).mp heq] with w hw
  by_cases ha : w ∈ A
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, hw ha]
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]

/-- A bound on a measurable product carrier, expressed with restricted
space and time measures, has the full-time implication form needed by the
remainder Morrey estimate. -/
theorem ae_spatial_bound_on_product_of_restricted_slices
    {H : ParabolicPoint → ℝ} {M : ℝ → ℝ≥0∞} {B : Set Vec3} {J : Set ℝ}
    (hB : MeasurableSet B) (hJ : MeasurableSet J)
    (hbound : ∀ᵐ s ∂volume.restrict J, ∀ᵐ x ∂volume.restrict B, ‖H (x, s)‖ₑ ≤ M s) :
    ∀ᵐ s ∂volume, ∀ᵐ x ∂volume, (x, s) ∈ B ×ˢ J → ‖H (x, s)‖ₑ ≤ M s := by
  filter_upwards [(ae_restrict_iff' hJ).mp hbound] with s hs
  by_cases hsJ : s ∈ J
  · filter_upwards [(ae_restrict_iff' hB).mp (hs hsJ)] with x hx
    exact fun h => hx h.1
  · exact Eventually.of_forall fun _ h => (hsJ h.2).elim

end CKN.Core.Step4
end

end

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
