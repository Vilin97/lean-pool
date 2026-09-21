/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStoppingExtraction

/-!
# Exact localized maximal recursion after Krause--Lacey stopping extraction

The operator here is the genuine supremum of localized sums over all
intervals above a length threshold, as in KL18 (3.4), not a maximum of
individual scale outputs. The finite interval sum splits exactly into the
constructed good collection and the collections belonging to the selected
children. This gives the actual pointwise and bilinear recursion without
postulating any local oscillatory or sparse domination estimate.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace KrauseLaceyStoppingRecursion

open KrauseLaceyStoppingExtraction


/-- The length-threshold localized sum appearing inside KL18 (3.4). The
scale label is constrained by the genuine kernel localization when needed. -/
noncomputable def localizedTailAction
    (scale : RealInterval → ℤ) (S : Finset RealInterval) (f : ℝ → ℂ)
    (ell : ℤ) (x : ℝ) : ℂ := by
  classical
  exact ∑ I ∈ S, if (2 : ℝ) ^ ell ≤ I.length then
    krauseLaceyLocalizedPiece 1 (scale I) I f x else 0

/-- The actual maximal partial-sum operator, with the source's lower
length-threshold cutoff retained explicitly. -/
noncomputable def localizedTailMaximal
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    (f : ℝ → ℂ) (x : ℝ) : ℝ≥0∞ :=
  ⨆ ell : {ell : ℤ // ell₀ ≤ ell}, ‖localizedTailAction scale S f ell.1 x‖ₑ

theorem measurable_localizedPiece
    (j : ℤ) (I : RealInterval) {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (krauseLaceyLocalizedPiece 1 j I f) := by
  have ha : Continuous (positiveDyadicAmplitude j) :=
    continuous_iff_continuousAt.mpr fun t ↦ (hasDerivAt_positiveDyadicAmplitude j t).continuousAt
  have hp : Measurable (fun p : ℝ × ℝ ↦ phase (p.2 ^ 2)) := by
    unfold phase
    fun_prop
  have hfI : Measurable (fun p : ℝ × ℝ ↦ I.centralThird.indicator f (p.1 - p.2)) :=
    (hf.indicator I.measurableSet_centralThird).comp (measurable_fst.sub measurable_snd)
  have h := ((ha.measurable.comp measurable_snd).mul hp).mul hfI
  have hi := h.stronglyMeasurable.integral_prod_right' (ν := volume)
  change Measurable (fun x : ℝ ↦ ∫ y : ℝ, positiveDyadicAmplitude j y *
    phase (1 * y ^ 2) * I.centralThird.indicator f (x - y))
  simpa only [one_mul, Function.comp_def, Pi.mul_apply]
    using hi.measurable

theorem measurable_localizedTailAction
    (scale : RealInterval → ℤ) (S : Finset RealInterval) {f : ℝ → ℂ}
    (hf : Measurable f) (ell : ℤ) : Measurable (localizedTailAction scale S f ell) := by
  classical
  apply Finset.measurable_fun_sum S
  intro I hI
  by_cases he : (2 : ℝ) ^ ell ≤ I.length
  · simpa only [ite_eq_left he] using measurable_localizedPiece (scale I) I hf
  · simp only [ite_eq_right he]
    exact measurable_const

theorem measurable_localizedTailMaximal
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (localizedTailMaximal ell₀ scale S f) :=
  Measurable.iSup fun ell ↦ (measurable_localizedTailAction scale S hf ell.1).enorm

/-- Restricting the input to a parent interval does not change any of its
localized descendants. This is an exact integral identity. -/
theorem localizedPiece_indicator_parent
    (j : ℤ) (I K : RealInterval) (f : ℝ → ℂ)
    (hIK : I.carrier ⊆ K.carrier) (x : ℝ) :
    krauseLaceyLocalizedPiece 1 j I (K.carrier.indicator f) x =
      krauseLaceyLocalizedPiece 1 j I f x := by
  unfold krauseLaceyLocalizedPiece
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : x - y ∈ I.centralThird
  · have hyK := hIK (I.centralThird_subset_carrier hy)
    simp only [indicator_of_mem hy, indicator_of_mem hyK]
  · simp only [indicator_of_notMem hy]

theorem localizedTailMaximal_indicator_parent
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    (f : ℝ → ℂ) (K : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ K.carrier) (x : ℝ) :
    localizedTailMaximal ell₀ scale S (K.carrier.indicator f) x =
      localizedTailMaximal ell₀ scale S f x := by
  classical
  apply iSup_congr
  intro ell
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [localizedPiece_indicator_parent (scale I) I K f (hsub I hI)]

/-- The support of every maximal recursive child contribution is genuinely
contained in that child, by the proved annular-kernel localization. -/
theorem localizedTailMaximal_eq_zero_of_notMem
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    (f : ℝ → ℂ) (K : RealInterval)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (hsub : ∀ I ∈ S, I.carrier ⊆ K.carrier)
    {x : ℝ} (hx : x ∉ K.carrier) : localizedTailMaximal ell₀ scale S f x = 0 := by
  classical
  have htail (ell : ℤ) : localizedTailAction scale S f ell x = 0 := by
    apply Finset.sum_eq_zero
    intro I hI
    have hz := krauseLaceyLocalizedPiece_eq_zero_of_notMem 1 (scale I) I f
      (hscale I hI) (fun hxI ↦ hx (hsub I hI hxI))
    simp only [hz, ite_self]
  simp only [localizedTailMaximal, htail, enorm_zero, iSup_const]

/-- The exact complex-valued decomposition at each truncation threshold. -/
theorem localizedTailAction_eq_good_add_children
    (scale : RealInterval → ℤ) {S : Finset RealInterval} (f g : ℝ → ℂ)
    (I : RealInterval)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (ell : ℤ) (x : ℝ) :
    localizedTailAction scale S f ell x =
      localizedTailAction scale (goodCollection S f g I) f ell x +
        ∑ K ∈ stoppingChildren S f g I,
          localizedTailAction scale (childCollection S K) f ell x :=
  sum_eq_good_add_sum_children f g I hlam _

/-- The actual localized maximal partial sums satisfy the stopping
recursion pointwise. No cardinality factor or local analytic estimate is
introduced in passing from the exact sum identity to the supremum. -/
theorem localizedTailMaximal_le_good_add_children
    (ell₀ : ℤ) (scale : RealInterval → ℤ) {S : Finset RealInterval}
    (f g : ℝ → ℂ) (I : RealInterval)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier)
    (x : ℝ) :
    localizedTailMaximal ell₀ scale S f x ≤
      localizedTailMaximal ell₀ scale (goodCollection S f g I) f x +
        ∑ K ∈ stoppingChildren S f g I,
          localizedTailMaximal ell₀ scale (childCollection S K) f x := by
  apply iSup_le
  intro ell
  rw [localizedTailAction_eq_good_add_children scale f g I hlam]
  apply (enorm_add_le _ _).trans
  apply add_le_add (le_iSup (fun ell : {ell : ℤ // ell₀ ≤ ell} ↦
    ‖localizedTailAction scale (goodCollection S f g I) f ell.1 x‖ₑ) ell)
  apply (enorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro K hK
  exact le_iSup (fun ell : {ell : ℤ // ell₀ ≤ ell} ↦
    ‖localizedTailAction scale (childCollection S K) f ell.1 x‖ₑ) ell

/-- The genuine bilinear recursion used immediately after the source's
maximal-child selection. Its first term still requires KL18 Lemma 3.5;
that analytic conclusion is not inserted as an assumption here. -/
theorem localizedTailMaximal_pairing_le_good_add_children
    (ell₀ : ℤ) (scale : RealInterval → ℤ) {S : Finset RealInterval}
    {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g) (I : RealInterval)
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
      (∫⁻ x, localizedTailMaximal ell₀ scale (goodCollection S f g I) f x * ‖g x‖ₑ) +
        ∑ K ∈ stoppingChildren S f g I,
          ∫⁻ x, localizedTailMaximal ell₀ scale (childCollection S K) f x * ‖g x‖ₑ := by
  calc
    _ ≤ ∫⁻ x, (localizedTailMaximal ell₀ scale (goodCollection S f g I) f x +
        ∑ K ∈ stoppingChildren S f g I,
          localizedTailMaximal ell₀ scale (childCollection S K) f x) * ‖g x‖ₑ :=
      lintegral_mono fun x ↦ mul_le_mul'
        (localizedTailMaximal_le_good_add_children ell₀ scale f g I hlam x) le_rfl
    _ = _ := by
      simp_rw [add_mul, Finset.sum_mul]
      have hgood : Measurable (fun x ↦
          localizedTailMaximal ell₀ scale (goodCollection S f g I) f x * ‖g x‖ₑ) :=
        (measurable_localizedTailMaximal ell₀ scale (goodCollection S f g I) hf).mul hg.enorm
      rw [lintegral_add_left hgood]
      congr 1
      apply lintegral_finsetSum
      intro K hK
      exact (measurable_localizedTailMaximal ell₀ scale (childCollection S K) hf).mul hg.enorm

/-- One complete finite stopping step for the actual localized maximal
operator: a constructed sparse root/children family, verified bounded
averages on the good collection, exact child locality, and the genuine
bilinear recursion. The pending KL18 local oscillatory estimate is precisely
the first pairing on the right of the final component. -/
theorem finite_localized_stopping_step
    (ell₀ : ℤ) (scale : RealInterval → ℤ) (S : Finset RealInterval)
    {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g) (I : RealInterval)
    (hsub : ∀ J ∈ S, J.carrier ⊆ I.carrier)
    (hscale : ∀ J ∈ S, J.length = (2 : ℝ) ^ (scale J + 2))
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun J K ↦
      J.carrier ⊆ K.carrier ∨ K.carrier ⊆ J.carrier ∨ Disjoint J.carrier K.carrier) :
    IsSparse (1 / 4) (↑(stoppingStepFamily S f g I) : Set RealInterval) ∧
      (∀ J ∈ goodCollection S f g I,
        intervalL1Average f J ≤ 10 * intervalL1Average f I ∧
          intervalL1Average g J ≤ 10 * intervalL1Average g I) ∧
      (∀ K ∈ stoppingChildren S f g I, ∀ x, x ∉ K.carrier →
        localizedTailMaximal ell₀ scale (childCollection S K) f x = 0) ∧
      (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
        (∫⁻ x, localizedTailMaximal ell₀ scale (goodCollection S f g I) f x * ‖g x‖ₑ) +
          ∑ K ∈ stoppingChildren S f g I,
            ∫⁻ x, localizedTailMaximal ell₀ scale (childCollection S K) f x * ‖g x‖ₑ := by
  classical
  refine ⟨root_insert_stoppingChildren_isSparse f g I hfi hgi hlam,
    fun _ hJ ↦ goodCollection_averages_le hsub hJ, ?_,
    localizedTailMaximal_pairing_le_good_add_children ell₀ scale hf hg I hlam⟩
  intro K hK x hx
  apply localizedTailMaximal_eq_zero_of_notMem ell₀ scale (childCollection S K) f K
    (fun J hJ ↦ hscale J (Finset.mem_filter.mp hJ).1)
    (fun J hJ ↦ (Finset.mem_filter.mp hJ).2) hx


end KrauseLaceyStoppingRecursion
end QuadraticCarleson
