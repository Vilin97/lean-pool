/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCorrectedSWS
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluing
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluingTBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceQuantitative
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.TheoremACarrierTime
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# Fixed-radius pressure slices on the full solution interval

The unit time interval supplies enough room to cover the whole open solution
interval by interior backward windows of any fixed length less than one.
The slice bound of `eq:pressure-gradient-morrey` therefore holds almost
everywhere on the full interval, with its source radius unchanged.
-/

public section

section

/-!
# Identification of cell-selected pressure gradients

On each cell, a locally selected weak pressure gradient and the fixed glued
gradient are weak derivatives of the same pressure. Uniqueness identifies
them almost everywhere, preserving the cell's own quantitative bound.
-/

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean

noncomputable section

namespace CKN.Core.Step4

/-- The selected weak-gradient witness on a doubled cell agrees locally with
the fixed glued field. Its norm bound retains the majorant belonging to that
cell. -/
theorem ae_glued_gradient_cell_selected_slice_identification
    {B : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ}
    {Dp : ParabolicPoint → Vec3} {x : Vec3} {t r : ℝ} (hr : 0 < r)
    {M : ℝ → ℝ≥0∞} (hball : vec3Ball x r ⊆ B)
    (htime : Ioc (t - r ^ 2) t ⊆ I)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) k) B volume ∧
      HasWeakPartialDerivOn B k (fun y => p (y, s)) (fun y => Dp (y, s) k))
    (hslice : ∀ᵐ s ∂volume.restrict (Ioc (t - (2 * r) ^ 2) t),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun y => D y k)
          (euclideanBall x ((2 * r) / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) k
          (fun y => p (y, s)) (fun y => D y k)) ∧
        (∀ k : Fin 3, eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ M s)) :
    ∀ᵐ s ∂volume.restrict (Ioc (t - r ^ 2) t),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun y => D y k)
          (euclideanBall x ((2 * r) / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) k
          (fun y => p (y, s)) (fun y => D y k)) ∧
        (∀ k : Fin 3, eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ M s) ∧
        (∀ k : Fin 3, eLpNorm (fun y => Dp (y, s) k)
          (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall x ((2 * r) / 2))) ≤ M s) ∧
        (∀ k : Fin 3,
          (fun y => Dp (y, s) k) =ᵐ[volume.restrict
            (euclideanBall x ((2 * r) / 2))] (fun y => D y k)) := by
  have hEeq : euclideanBall x ((2 * r) / 2) = vec3Ball x r := by
    rw [mul_div_cancel_left₀ r (by norm_num : (2 : ℝ) ≠ 0)]
    exact euclideanBall_eq_vec3Ball_of_pos hr
  have hEopen : IsOpen (euclideanBall x ((2 * r) / 2)) := by
    rw [hEeq]
    exact isOpen_vec3Ball x r
  have hEball : euclideanBall x ((2 * r) / 2) ⊆ B := by
    rw [hEeq]
    exact hball
  have hwindow : Ioc (t - r ^ 2) t ⊆ Ioc (t - (2 * r) ^ 2) t := by
    intro s hs
    exact ⟨lt_of_le_of_lt (by nlinarith only [sq_nonneg r]) hs.1, hs.2⟩
  filter_upwards
    [ae_restrict_of_ae_restrict_of_subset htime hfield,
      ae_restrict_of_ae_restrict_of_subset hwindow hslice] with s hf hs
  obtain ⟨D, hDloc, hDmem, hDweak, hDbound⟩ := hs
  have hEq : ∀ k : Fin 3,
      (fun y => Dp (y, s) k) =ᵐ[volume.restrict
        (euclideanBall x ((2 * r) / 2))] (fun y => D y k) := by
    intro k
    have hDpLoc : LocallyIntegrableOn (fun y => Dp (y, s) k)
        (euclideanBall x ((2 * r) / 2)) volume :=
      (hf k).1.mono_set hEball
    have hDpWeak : HasWeakPartialDerivOn (euclideanBall x ((2 * r) / 2)) k
        (fun y => p (y, s)) (fun y => Dp (y, s) k) :=
      (hf k).2.restrict hEopen hEball
    have hEq := CKN.hasWeakPartialDerivOn_unique_ae hEopen hDpLoc
      (hDloc k) hDpWeak (hDweak k)
    exact hEq
  refine ⟨D, hDloc, hDmem, hDweak, hDbound, ?_, hEq⟩
  intro k
  calc
    eLpNorm (fun y => Dp (y, s) k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) =
      eLpNorm (fun y => D y k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall x ((2 * r) / 2))) :=
          eLpNorm_congr_ae (hEq k)
    _ ≤ M s := hDbound k

end CKN.Core.Step4
end

end

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

private theorem exists_fixed_window
    {I : Set ℝ} (hIo : IsOpen I) (hIc : I.OrdConnected)
    (hunit : Icc (-1 : ℝ) 0 ⊆ I) {d s : ℝ} (hd : 0 < d) (hd1 : d < 1)
    (hs : s ∈ I) : ∃ t : ℝ, Icc (t - d) t ⊆ I ∧ s ∈ Ioo (t - d) t := by
  obtain ⟨a, b, has, hsb⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hIo.mem_nhds hs)
  obtain ⟨a', haa', ha's⟩ := exists_between has.1
  obtain ⟨b', hsb', hb'b⟩ := exists_between has.2
  have haI : a' ∈ I := hsb ⟨haa', ha's.trans has.2⟩
  have hbI : b' ∈ I := hsb ⟨has.1.trans hsb', hb'b⟩
  let A := min a' (-1)
  let B := max b' 0
  have hAI : A ∈ I := by
    rcases min_choice a' (-1 : ℝ) with h | h
    · rw [show A = a' from h]; exact haI
    · rw [show A = -1 from h]; exact hunit ⟨le_rfl, by norm_num⟩
  have hBI : B ∈ I := by
    rcases max_choice b' (0 : ℝ) with h | h
    · rw [show B = b' from h]; exact hbI
    · rw [show B = 0 from h]; exact hunit ⟨by norm_num, le_rfl⟩
  have hAs : A < s := (min_le_left _ _).trans_lt ha's
  have hsB : s < B := hsb'.trans_le (le_max_left _ _)
  have hAB : A + d < B := by
    have hA : A ≤ -1 := min_le_right _ _
    have hB : 0 ≤ B := le_max_right _ _
    linarith only [hA, hB, hd1]
  have hgap : max s (A + d) < min B (s + d) := by
    exact max_lt (lt_min hsB (by linarith only [hd]))
      (lt_min hAB (by linarith only [hAs]))
  obtain ⟨t, htlo, hthi⟩ := exists_between hgap
  refine ⟨t, ?_, ?_⟩
  · apply Subset.trans _ (hIc.out hAI hBI)
    intro v hv
    have ha := (le_max_right s (A + d)).trans_lt htlo
    have hb := hthi.trans_le (min_le_left B (s + d))
    exact ⟨by linarith only [ha, hv.1], hv.2.trans hb.le⟩
  · have ht := (le_max_left s (A + d)).trans_lt htlo
    have hb := hthi.trans_le (min_le_right B (s + d))
    exact ⟨by linarith only [hb], ht⟩

/-- A statement holding almost everywhere on every interior backward window
of a fixed length less than one holds almost everywhere on the full interval. -/
theorem ae_on_interval_of_fixed_windows
    {I : Set ℝ} (hIo : IsOpen I) (hIc : I.OrdConnected)
    (hunit : Icc (-1 : ℝ) 0 ⊆ I) {d : ℝ} (hd : 0 < d) (hd1 : d < 1)
    {P : ℝ → Prop}
    (hwindow : ∀ t : ℝ, Icc (t - d) t ⊆ I →
      ∀ᵐ s ∂volume.restrict (Ioc (t - d) t), P s) :
    ∀ᵐ s ∂volume.restrict I, P s := by
  let T := {t : ℝ // Icc (t - d) t ⊆ I}
  let U : T → Set ℝ := fun t => Ioo (t.1 - d) t.1
  have hcover : (⋃ t : T, U t) = I := by
    apply Subset.antisymm
    · exact iUnion_subset (fun t => Ioo_subset_Icc_self.trans t.2)
    · intro s hs
      obtain ⟨t, ht, hst⟩ := exists_fixed_window hIo hIc hunit hd hd1 hs
      exact mem_iUnion.mpr ⟨⟨t, ht⟩, hst⟩
  obtain ⟨S, hSc, hS⟩ := TopologicalSpace.isOpen_iUnion_countable U (fun _ => isOpen_Ioo)
  rw [← hcover, ← hS, ae_restrict_biUnion_iff U hSc]
  intro t _ht
  exact ae_restrict_of_ae_restrict_of_subset Ioo_subset_Ioc_self (hwindow t.1 t.2)

/-- The complete fixed-origin slice estimate holds on almost every time of
the entire solution interval; unit-time containment and compact spatial
source containment suffice. -/
theorem origin_slice_bound_on_full_interval
    {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hball : closure (vec3Ball (0 : Vec3) ρ) ⊆ Ω)
    (htime : Icc (-1 : ℝ) 0 ⊆ I) :
    ∀ᵐ s ∂volume.restrict I,
      MemLp (fun y => p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (vec3Ball (0 : Vec3) ρ)) ∧
      ∃ D : Vec3 → Vec3,
        (∀ i, LocallyIntegrableOn (fun y => D y i) (vec3Ball 0 (ρ / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball 0 (ρ / 2))) ∧
        (∀ i, HasWeakPartialDerivOn (vec3Ball 0 (ρ / 2)) i
          (fun y => p (y, s)) (fun y => D y i)) ∧
        (∀ i, eLpNorm (fun y => D y i) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (vec3Ball 0 (ρ / 2))) ≤
            originSliceGradientMajorant u Du p f ((0 : Vec3), 0) hρ s) := by
  apply ae_on_interval_of_fixed_windows hsol.2.1 hsol.2.2.1 htime
    (sq_pos_of_pos hρ) (by nlinarith only [hρ, hρone])
  intro t ht
  have hsub : closure (parabolicCylinder (0 : Vec3) t ρ) ⊆ spaceTimeSet Ω I := by
    rw [closure_parabolicCylinder hρ]
    intro w hw
    exact ⟨hball (by rw [closure_vec3Ball hρ]; exact hw.1), ht hw.2⟩
  have hp := sws_pressure_memLp_slice_ae (z := ((0 : Vec3), t)) hsol hρ hsub
  have hg := origin_local_slice_gradient_bound_ae_of_sws (z := ((0 : Vec3), t)) hsol hρ hsub
  filter_upwards [hp, hg] with s hs hgs
  refine ⟨hs, ?_⟩
  have heq : originSliceGradientMajorant u Du p f ((0 : Vec3), t) hρ s =
      originSliceGradientMajorant u Du p f ((0 : Vec3), 0) hρ s := by rfl
  simpa only [heq, CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
    (show 0 < ρ / 2 by positivity)] using hgs

private theorem translated_ball_measure_preserving (x : Vec3) (r : ℝ) :
    MeasurePreserving (fun y : Vec3 => -x + y)
      (volume.restrict (vec3Ball x r)) (volume.restrict (vec3Ball 0 r)) := by
  have heq : (fun y : Vec3 => -x + y) ⁻¹' vec3Ball 0 r = vec3Ball x r := by
    ext y
    simp only [mem_preimage, mem_vec3Ball, sub_zero]
    rw [neg_add_eq_sub]
  have hm := (measurePreserving_add_left (volume : Measure Vec3) (-x)).restrict_preimage
    (isOpen_vec3Ball (0 : Vec3) r).measurableSet
  rwa [heq] at hm

/-- Translating a fixed source ball gives the complete local slice bound on
almost every time in the full solution interval, with the exact translated
majorant used by the carrier time estimate. -/
theorem translated_slice_bound_on_full_interval
    (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (hρone : ρ < 1)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hball : closure (vec3Ball x ρ) ⊆ Ω) (htime : Icc (-1 : ℝ) 0 ⊆ I) :
    ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3, ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball x (ρ / 2)) volume ∧
      HasWeakPartialDerivOn (vec3Ball x (ρ / 2)) i (fun y => p (y, s)) g ∧
      eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball x (ρ / 2))) ≤
          theoremATranslatedSliceMajorant u Du p f x hρ s := by
  have ht : rescaledTime 1 0 I = I := by
    ext t
    simp only [rescaledTime, scalingTime, one_pow, one_mul, zero_add, mem_preimage]
  have hshift := isSuitableWeakSolutionIntegrable_rescale hsol (x, 0) (by norm_num : (0 : ℝ) < 1)
  rw [ht] at hshift
  have hb : closure (vec3Ball (0 : Vec3) ρ) ⊆ rescaledSpace 1 x Ω := by
    intro y hy
    apply hball
    rw [closure_vec3Ball hρ] at hy ⊢
    simpa only [rescaledSpace, scalingSpace, one_smul, add_sub_cancel_left, sub_zero,
      mem_ofPred_eq] using hy
  have hslices := origin_slice_bound_on_full_interval hρ hρone hshift hb htime
  have hsub : vec3Ball (0 : Vec3) (ρ / 2) ⊆ vec3Ball 0 ρ := by
    intro y hy
    change vec3EuclideanNorm (y - 0) < ρ / 2 at hy
    change vec3EuclideanNorm (y - 0) < ρ
    exact hy.trans_le (by linarith only [hρ])
  have himage : vec3Ball (0 : Vec3) (ρ / 2) =
      scalingSpace 1 (-x) '' vec3Ball x (ρ / 2) := by
    ext y
    constructor
    · intro hy
      refine ⟨x + y, ?_, ?_⟩
      · simpa only [mem_vec3Ball, add_sub_cancel_left, sub_zero] using hy
      · simp only [scalingSpace, one_smul, neg_add_cancel_left]
    · rintro ⟨y, hy, rfl⟩
      simpa only [scalingSpace, one_smul, mem_vec3Ball, sub_zero, neg_add_eq_sub] using hy
  have hm := translated_ball_measure_preserving x (ρ / 2)
  filter_upwards [hslices] with s hs
  obtain ⟨hp, D, _hDl, hDm, hDw, hDb⟩ := hs
  intro i
  let g : Vec3 → ℝ := fun y => D (-x + y) i
  have hgm : MemLp g (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (vec3Ball x (ρ / 2))) := (hDm.eval i).comp_measurePreserving hm
  have hfin : IsFiniteMeasure (volume.restrict (vec3Ball x (ρ / 2))) :=
    isFiniteMeasure_restrict.mpr Integration.volume_vec3Ball_lt_top.ne
  have hgl : LocallyIntegrableOn g (vec3Ball x (ρ / 2)) volume :=
    IntegrableOn.locallyIntegrableOn (hgm.integrable (by norm_num))
  have hw := hasWeakPartialDerivOn_scaling 1 (by norm_num) (-x)
    (isOpen_vec3Ball (0 : Vec3) (ρ / 2)).measurableSet i himage (hDw i)
    (hp.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hsub))
    (hDm.eval i).aestronglyMeasurable
  refine ⟨g, hgl, ?_, ?_⟩
  · simpa [rescalePressure, scalingSpace, parabolicTranslate, parabolicScale, g] using hw
  · have heq := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal (6 / 5 : ℝ))
      (hDm.eval i).aestronglyMeasurable hm
    exact heq.trans_le (hDb i)

private theorem fixed_spatial_cover {R : ℝ} (hR : 0 < R) (hR34 : R < 3 / 4) :
    ∃ (n : ℕ) (x : Fin n → Vec3),
      (∀ j, closure (vec3Ball (x j) (1 / 8)) ⊆ vec3Ball (0 : Vec3) 1) ∧
      vec3Ball (0 : Vec3) R ⊆ ⋃ j, vec3Ball (x j) ((1 / 8 : ℝ) / 2) := by
  classical
  let K := closure (vec3Ball (0 : Vec3) R)
  have hc : IsCompact K := isCompact_closure_vec3Ball hR
  have hcover : K ⊆ ⋃ x : K, vec3Ball x.1 (1 / 16) := by
    intro y hy
    refine mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
    simp only [mem_vec3Ball, sub_self, vec3EuclideanNorm_zero]
    norm_num
  obtain ⟨S, hS⟩ := hc.elim_finite_subcover
    (fun x : K => vec3Ball x.1 (1 / 16)) (fun _ => isOpen_vec3Ball _ _) hcover
  let x : Fin S.card → Vec3 := fun j => (S.equivFin.symm j).1.1
  refine ⟨S.card, x, ?_, ?_⟩
  · intro j y hy
    have hx : x j ∈ closure (vec3Ball (0 : Vec3) R) := (S.equivFin.symm j).1.2
    rw [closure_vec3Ball hR] at hx
    have hx' : vec3EuclideanNorm (x j - 0) ≤ R := hx
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 8)] at hy
    change vec3EuclideanNorm (y - x j) ≤ 1 / 8 at hy
    rw [mem_vec3Ball]
    have ht : vec3EuclideanNorm (y - 0) ≤
        vec3EuclideanNorm (y - x j) + vec3EuclideanNorm (x j - 0) := by
      convert CKN.Foundation.Parabolic.vec3EuclideanNorm_add_le
        (y - x j) (x j - 0) using 1
      congr 1
      abel
    linarith only [ht, hy, hx', hR34]
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp (hS (subset_closure hy))
    refine mem_iUnion.mpr ⟨S.equivFin ⟨z, hz⟩, ?_⟩
    simpa only [x, Equiv.symm_apply_apply, show (1 / 8 : ℝ) / 2 = 1 / 16 by norm_num]
      using hyz

private theorem eLpNorm_le_finite_cover_sum
    {n : ℕ} {B : Set Vec3} (hB : MeasurableSet B)
    (U : Fin n → Set Vec3) (hU : ∀ j, MeasurableSet (U j))
    (hcover : B ⊆ ⋃ j, U j) {g : Vec3 → ℝ} (hg : Measurable g) :
    eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict B) ≤
      ∑ j, eLpNorm g (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (U j ∩ B)) := by
  let F : Fin n → Vec3 → ℝ := fun j => (U j ∩ B).indicator g
  have hm (j : Fin n) : Measurable (F j) := hg.indicator ((hU j).inter hB)
  have hbound : ∀ y, ‖B.indicator g y‖ ≤ ‖∑ j, ‖F j y‖‖ := by
    intro y
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg (F j y)))]
    by_cases hy : y ∈ B
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover hy)
      rw [indicator_of_mem hy]
      have heq : F j y = g y := indicator_of_mem (show y ∈ U j ∩ B from ⟨hj, hy⟩) g
      rw [← heq]
      exact Finset.single_le_sum (fun k _ => norm_nonneg (F k y)) (Finset.mem_univ j)
    · rw [indicator_of_notMem hy, norm_zero]
      exact Finset.sum_nonneg (fun j _ => norm_nonneg (F j y))
  calc
    _ = eLpNorm (B.indicator g) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
      (eLpNorm_indicator_eq_eLpNorm_restrict hB).symm
    _ ≤ eLpNorm (fun y => ∑ j, ‖F j y‖) (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
      eLpNorm_mono_ae (hg.indicator hB).aestronglyMeasurable (Eventually.of_forall hbound)
    _ ≤ ∑ j, eLpNorm (fun y => ‖F j y‖) (ENNReal.ofReal (6 / 5 : ℝ)) volume := by
      simpa only [Finset.sum_fn] using
        (eLpNorm_sum_le (f := fun j y => ‖F j y‖) (s := Finset.univ)
          (μ := (volume : Measure Vec3)) (by norm_num : 1 ≤ ENNReal.ofReal (6 / 5 : ℝ)))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [eLpNorm_norm _ (hm j).aestronglyMeasurable]
      exact eLpNorm_indicator_eq_eLpNorm_restrict ((hU j).inter hB)

/-- The exact finite spatial estimate used by the full-interval carrier
time theorem. All centres and the source radius are chosen before the
suitable solution, and the bound holds on almost every time in all of `I`. -/
theorem origin_carrier_finite_translated_slice_estimate
    (R : ℝ) (hR : 0 < R) (hR34 : R < 3 / 4) :
    ∃ (n : ℕ) (x : Fin n → Vec3) (ρ : ℝ) (hρ : 0 < ρ),
      (∀ j, closure (vec3Ball (x j) ρ) ⊆ vec3Ball (0 : Vec3) 1) ∧
      ∀ {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
        {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
        {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3},
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I →
        ∀ Dp : ParabolicPoint → Vec3, Measurable Dp →
        (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
          LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R) volume ∧
          HasWeakPartialDerivOn (vec3Ball 0 R) i
            (fun y => p (y, s)) (fun y => Dp (y, s) i)) →
        ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict I,
          eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
              (volume.restrict (vec3Ball 0 R)) ≤
            ∑ j, theoremATranslatedSliceMajorant u Du p f (x j) hρ s := by
  obtain ⟨n, x, hballs, hcover⟩ := fixed_spatial_cover hR hR34
  refine ⟨n, x, 1 / 8, by norm_num, hballs, ?_⟩
  intro Ω I q u Du p f hsol hdom Dp hDm hfield i
  obtain ⟨hΩ, hI⟩ := OriginInstance.originUnitBall_subset_of_dom hdom
  have hb (j : Fin n) : closure (vec3Ball (x j) (1 / 8)) ⊆ Ω := by
    intro y hy
    apply hΩ
    exact (show vec3EuclideanNorm (y - 0) < 1 from hballs j hy).le
  have hs (j : Fin n) := translated_slice_bound_on_full_interval (x j)
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1)
    hsol (hb j) hI
  filter_upwards [ae_all_iff.mpr hs, hfield] with s hs hf
  have hgm : Measurable (fun y => Dp (y, s) i) :=
    ((measurable_pi_apply i).comp hDm).comp (measurable_id.prodMk measurable_const)
  apply (eLpNorm_le_finite_cover_sum (isOpen_vec3Ball (0 : Vec3) R).measurableSet
    (fun j => vec3Ball (x j) ((1 / 8 : ℝ) / 2))
    (fun j => (isOpen_vec3Ball _ _).measurableSet) hcover hgm).trans
  apply Finset.sum_le_sum
  intro j _hj
  obtain ⟨g, hgl, hgw, hgb⟩ := hs j i
  have ho := (isOpen_vec3Ball (x j) ((1 / 8 : ℝ) / 2)).inter (isOpen_vec3Ball 0 R)
  have heq := ((hf i).2.restrict ho inter_subset_right).ae_eq ho
    ((hf i).1.mono_set inter_subset_right) (hgl.mono_set inter_subset_left)
    (hgw.restrict ho inter_subset_left)
  exact (eLpNorm_congr_ae heq).trans_le
    ((eLpNorm_mono_measure g (Measure.restrict_mono_set volume inter_subset_left)).trans hgb)

/-- The selected gradient on the whole spatial carrier has finite slice
norm almost everywhere on `I`, and its slice norm is integrable on every
compactly interior time set, with no additional slice estimate hypothesis. -/
theorem origin_carrier_slice_time_obligations_of_sws
    {R : ℝ} (hR : 0 < R) (hR34 : R < 3 / 4)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (Dp : ParabolicPoint → Vec3) (hDp : Measurable Dp)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i)) :
    (∀ i : Fin 3, ∀ᵐ s ∂volume.restrict I,
      eLpNorm (fun y => Dp (y, s) i) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (vec3Ball 0 R)) ≠ ⊤) ∧
    (∀ (i : Fin 3) (T : Set ℝ), IsCompact (closure T) → closure T ⊆ I →
      Integrable (fun s => (eLpNorm (fun y => Dp (y, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) (volume.restrict (vec3Ball 0 R))).toReal)
        (volume.restrict T)) :=
  theoremA_carrier_slice_time_of_finite_cover origin_carrier_finite_translated_slice_estimate
    hsol hdom hR hR34 Dp hDp hfield

end CKN.Core.Step4
