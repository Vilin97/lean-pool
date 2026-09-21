/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceySparseInterface
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticFixedHeightAveragingAmplitude

/-!
# Dyadic localization in the Krause--Lacey sparse recursion

This module formalizes the geometric localization at the start of Section 3
of Krause--Lacey, *Sparse bounds for maximal monomial oscillatory Hilbert
transforms* (arXiv:1609.01564).  In their display (3.2), an interval `I` of
length `2^(k+2)` is assigned a genuine dyadic kernel piece at scale `k`, and
the input is restricted to the central third `I'`.  The resulting piece is
supported in `I`.

The source first concentrates on the positive half-kernel `ρₖ⁺`, saying
explicitly that the complementary negative half is symmetric.  Accordingly,
our main localized piece uses the project's concrete `positiveDyadicAmplitude`;
a separate signed companion below uses the full `dyadicPsi` and connects this
localization to the genuine full dyadic Hilbert kernel.  Both have outer
support radius `2^(j-1)`, exactly one eighth of `2^(j+2)` in the project's
indexing.

The genuinely analytic input called Lemma 3.5 in that source is deliberately
not asserted here: it is the remaining local oscillatory `L¹ → L^q` estimate.
The results below prove its localization and stopping/packing framework, but
do not replace that estimate by an assumption.
-/

open Function MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson


/-- The interval `I'` in Krause--Lacey display (3.2): the central third of
`I`.  We retain the project's canonical half-open representative. -/
def RealInterval.centralThird (I : RealInterval) : Set ℝ :=
  Ioc ((2 * I.left + I.right) / 3) ((I.left + 2 * I.right) / 3)

theorem RealInterval.measurableSet_centralThird (I : RealInterval) :
    MeasurableSet I.centralThird := measurableSet_Ioc

theorem RealInterval.centralThird_subset_carrier (I : RealInterval) :
    I.centralThird ⊆ I.carrier := by
  intro x hx
  change (2 * I.left + I.right) / 3 < x ∧
    x ≤ (I.left + 2 * I.right) / 3 at hx
  change I.left < x ∧ x ≤ I.right
  exact ⟨by linarith [hx.1, I.left_lt_right],
    by linarith [hx.2, I.left_lt_right]⟩

/-- The genuine localized quadratic dyadic piece corresponding to
Krause--Lacey (3.2), with the source input restriction to the central third.
The harmless phase parameter is left explicit. -/
noncomputable def krauseLaceyLocalizedPiece
    (lam : ℝ) (j : ℤ) (I : RealInterval) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, positiveDyadicAmplitude j y * phase (lam * y ^ 2) *
    I.centralThird.indicator f (x - y)

/-- At the source scale relation `|I| = 2^(j+2)`, the outer radius of the
project's one-sided dyadic amplitude is exactly `|I|/8`. -/
theorem krauseLacey_scale_eq_eight_mul_radius (j : ℤ) :
    (2 : ℝ) ^ (j + 2) = 8 * (2 : ℝ) ^ (j - 1) := by
  rw [show j + 2 = (j - 1) + 3 by ring,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring

/-- The exact support/locality assertion following Krause--Lacey (3.2):
localizing the input to the central third makes the scale-`j` piece supported
on `I` whenever `|I| = 2^(j+2)`.

The statement is pointwise and needs no integrability hypothesis: outside
`I` the integrand vanishes identically. -/
theorem krauseLaceyLocalizedPiece_eq_zero_of_notMem
    (lam : ℝ) (j : ℤ) (I : RealInterval) (f : ℝ → ℂ)
    (hscale : I.length = (2 : ℝ) ^ (j + 2))
    {x : ℝ} (hx : x ∉ I.carrier) :
    krauseLaceyLocalizedPiece lam j I f x = 0 := by
  unfold krauseLaceyLocalizedPiece
  calc
    ∫ y, positiveDyadicAmplitude j y * phase (lam * y ^ 2) *
        I.centralThird.indicator f (x - y) = ∫ _y : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases ha : positiveDyadicAmplitude j y = 0
      · simp [ha]
      have hy := positiveDyadicAmplitude_support_subset j ha
      have hradius_pos : 0 < (2 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) _
      have hy_nonneg : 0 ≤ y :=
        le_trans (div_nonneg hradius_pos.le (by norm_num)) hy.1
      have hy_upper : y ≤ I.length / 8 := by
        rw [hscale, krauseLacey_scale_eq_eight_mul_radius]
        norm_num
        exact hy.2
      have hnotmid : x - y ∉ I.centralThird := by
        intro hmid
        change (2 * I.left + I.right) / 3 < x - y ∧
          x - y ≤ (I.left + 2 * I.right) / 3 at hmid
        apply hx
        rw [RealInterval.carrier]
        constructor
        · change I.left < x
          linarith [hmid.1, I.left_lt_right]
        · change x ≤ I.right
          dsimp [RealInterval.length] at hy_upper
          linarith [hmid.2]
      rw [Set.indicator_of_notMem hnotmid]
      simp
    _ = 0 := by simp

/-- Set-theoretic support formulation of the preceding exact pointwise
localization. -/
theorem krauseLaceyLocalizedPiece_support_subset
    (lam : ℝ) (j : ℤ) (I : RealInterval) (f : ℝ → ℂ)
    (hscale : I.length = (2 : ℝ) ^ (j + 2)) :
    Function.support (krauseLaceyLocalizedPiece lam j I f) ⊆ I.carrier := by
  intro x hx
  by_contra hmem
  exact hx (krauseLaceyLocalizedPiece_eq_zero_of_notMem lam j I f hscale hmem)

/-- Full signed-project companion of the source's positive-half localized
piece.  This is the same localization using the genuine `dyadicPsi` piece
which occurs in the project's smooth dyadic quadratic truncations. -/
noncomputable def krauseLaceySignedLocalizedPiece
    (lam : ℝ) (j : ℤ) (I : RealInterval) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y, (dyadicPsi j y : ℂ) * phase (lam * y ^ 2) *
    I.centralThird.indicator f (x - y)

theorem krauseLaceySignedLocalizedPiece_eq_zero_of_notMem
    (lam : ℝ) (j : ℤ) (I : RealInterval) (f : ℝ → ℂ)
    (hscale : I.length = (2 : ℝ) ^ (j + 2))
    {x : ℝ} (hx : x ∉ I.carrier) :
    krauseLaceySignedLocalizedPiece lam j I f x = 0 := by
  unfold krauseLaceySignedLocalizedPiece
  calc
    ∫ y, (dyadicPsi j y : ℂ) * phase (lam * y ^ 2) *
        I.centralThird.indicator f (x - y) = ∫ _y : ℝ, (0 : ℂ) := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases ha : dyadicPsi j y = 0
      · simp [ha]
      have hy := dyadicPsi_support_subset j ha
      change (2 : ℝ) ^ (j - 3) < |y| ∧ |y| < (2 : ℝ) ^ (j - 1) at hy
      have hy_upper : y ≤ I.length / 8 := by
        rw [hscale, krauseLacey_scale_eq_eight_mul_radius]
        norm_num
        exact (le_abs_self y).trans hy.2.le
      have hy_lower : -(I.length / 8) ≤ y := by
        rw [hscale, krauseLacey_scale_eq_eight_mul_radius]
        norm_num
        exact (neg_le_neg hy.2.le).trans (neg_abs_le y)
      have hnotmid : x - y ∉ I.centralThird := by
        intro hmid
        change (2 * I.left + I.right) / 3 < x - y ∧
          x - y ≤ (I.left + 2 * I.right) / 3 at hmid
        apply hx
        rw [RealInterval.carrier]
        constructor
        · change I.left < x
          dsimp [RealInterval.length] at hy_lower
          linarith [hmid.1, I.left_lt_right]
        · change x ≤ I.right
          dsimp [RealInterval.length] at hy_upper
          linarith [hmid.2]
      rw [Set.indicator_of_notMem hnotmid]
      simp
    _ = 0 := by simp

theorem krauseLaceySignedLocalizedPiece_support_subset
    (lam : ℝ) (j : ℤ) (I : RealInterval) (f : ℝ → ℂ)
    (hscale : I.length = (2 : ℝ) ^ (j + 2)) :
    Function.support (krauseLaceySignedLocalizedPiece lam j I f) ⊆ I.carrier := by
  intro x hx
  by_contra hmem
  exact hx (krauseLaceySignedLocalizedPiece_eq_zero_of_notMem lam j I f hscale hmem)

/-- The ordinary local `L¹` average used to select stopping children in the
proof of Krause--Lacey Lemma 3.5. -/
noncomputable def intervalL1Average (f : ℝ → ℂ) (I : RealInterval) : ℝ :=
  I.length⁻¹ * ∫ x in I.carrier, ‖f x‖

theorem intervalL1Average_nonneg (f : ℝ → ℂ) (I : RealInterval) :
    0 ≤ intervalL1Average f I := by
  exact mul_nonneg (inv_nonneg.mpr I.length_pos.le) (integral_nonneg fun _ ↦ norm_nonneg _)

theorem intervalL1Average_mul_length (f : ℝ → ℂ) (I : RealInterval) :
    intervalL1Average f I * I.length = ∫ x in I.carrier, ‖f x‖ := by
  rw [intervalL1Average]
  field_simp [I.length_pos.ne']

/-- The one-function packing estimate behind the source's stopping-time
argument.  Pairwise-disjoint children whose `L¹` average exceeds ten times
the parent's occupy at most one tenth of the parent.

Maximality and dyadic provenance are what supply disjointness in the source;
the estimate itself only uses that disjointness and containment. -/
theorem krauseLacey_stoppingChildren_length_le_tenth
    {ι : Type*} (s : Finset ι) (J : ι → RealInterval) (I : RealInterval)
    (f : ℝ → ℂ)
    (hdisj : Set.Pairwise (↑s) (Disjoint on fun i ↦ (J i).carrier))
    (hsub : ∀ i ∈ s, (J i).carrier ⊆ I.carrier)
    (hf : IntegrableOn f I.carrier)
    (hbad : ∀ i ∈ s,
      10 * intervalL1Average f I < intervalL1Average f (J i)) :
    ∑ i ∈ s, (J i).length ≤ I.length / 10 := by
  classical
  by_cases hs : s.Nonempty
  · have hchild_int : ∀ i ∈ s, IntegrableOn (fun x ↦ ‖f x‖) (J i).carrier := by
      intro i hi
      exact hf.norm.mono_measure
        (Measure.restrict_mono (hsub i hi) (le_refl volume))
    have hsum_lt :
        ∑ i ∈ s, (10 * intervalL1Average f I) * (J i).length <
          ∑ i ∈ s, ∫ x in (J i).carrier, ‖f x‖ := by
      apply Finset.sum_lt_sum_of_nonempty hs
      intro i hi
      calc
        (10 * intervalL1Average f I) * (J i).length <
            intervalL1Average f (J i) * (J i).length :=
          mul_lt_mul_of_pos_right (hbad i hi) (J i).length_pos
        _ = ∫ x in (J i).carrier, ‖f x‖ := intervalL1Average_mul_length f (J i)
    have hunion_sub : (⋃ i ∈ s, (J i).carrier) ⊆ I.carrier := by
      intro x hx
      simp only [mem_iUnion] at hx
      rcases hx with ⟨i, hi⟩
      rcases hi with ⟨his, hxJ⟩
      exact hsub i his hxJ
    have hsum_le :
        ∑ i ∈ s, ∫ x in (J i).carrier, ‖f x‖ ≤
          ∫ x in I.carrier, ‖f x‖ := by
      rw [← integral_biUnion_finset s
        (fun i _ ↦ (J i).measurableSet_carrier) hdisj hchild_int]
      exact setIntegral_mono_set hf.norm
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x)) hunion_sub.eventuallyLE
    have hstrict :
        10 * intervalL1Average f I * (∑ i ∈ s, (J i).length) <
          intervalL1Average f I * I.length := by
      rw [Finset.mul_sum, intervalL1Average_mul_length]
      exact hsum_lt.trans_le hsum_le
    have haverage_pos : 0 < intervalL1Average f I := by
      have haverage_nonneg := intervalL1Average_nonneg f I
      have hlength_sum_pos : 0 < ∑ i ∈ s, (J i).length :=
        Finset.sum_pos (fun i _ ↦ (J i).length_pos) hs
      nlinarith [I.length_pos]
    exact (le_of_lt (by
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 10)).2
      nlinarith [hstrict])).trans_eq (by ring)
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hempty]
    simp only [Finset.sum_empty]
    exact div_nonneg I.length_pos.le (by norm_num)

/-- The exact two-function packing estimate in the stopping recursion for
Krause--Lacey Lemma 3.5.  A child is stopped when either input average is more
than ten times its parent average.  The two exceptional subfamilies each cost
at most `|I|/10`, hence all stopping children cost at most `|I|/5`. -/
theorem krauseLacey_stoppingChildren_length_le_fifth
    {ι : Type*} (s : Finset ι) (J : ι → RealInterval) (I : RealInterval)
    (f g : ℝ → ℂ)
    (hdisj : Set.Pairwise (↑s) (Disjoint on fun i ↦ (J i).carrier))
    (hsub : ∀ i ∈ s, (J i).carrier ⊆ I.carrier)
    (hf : IntegrableOn f I.carrier) (hg : IntegrableOn g I.carrier)
    (hbad : ∀ i ∈ s,
      10 * intervalL1Average f I < intervalL1Average f (J i) ∨
        10 * intervalL1Average g I < intervalL1Average g (J i)) :
    ∑ i ∈ s, (J i).length ≤ I.length / 5 := by
  classical
  let p : ι → Prop := fun i ↦
    10 * intervalL1Average f I < intervalL1Average f (J i)
  have hdisj_f : Set.Pairwise (↑(s.filter p))
      (Disjoint on fun i ↦ (J i).carrier) := by
    apply hdisj.mono
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hdisj_g : Set.Pairwise (↑(s.filter fun i ↦ ¬ p i))
      (Disjoint on fun i ↦ (J i).carrier) := by
    apply hdisj.mono
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hfpack : ∑ i ∈ s.filter p, (J i).length ≤ I.length / 10 := by
    apply krauseLacey_stoppingChildren_length_le_tenth
      (s.filter p) J I f hdisj_f
    · intro i hi
      exact hsub i (Finset.mem_filter.mp hi).1
    · exact hf
    · intro i hi
      exact (Finset.mem_filter.mp hi).2
  have hgpack : ∑ i ∈ s.filter (fun i ↦ ¬ p i), (J i).length ≤ I.length / 10 := by
    apply krauseLacey_stoppingChildren_length_le_tenth
      (s.filter fun i ↦ ¬ p i) J I g hdisj_g
    · intro i hi
      exact hsub i (Finset.mem_filter.mp hi).1
    · exact hg
    · intro i hi
      rcases Finset.mem_filter.mp hi with ⟨his, hn⟩
      exact (hbad i his).resolve_left hn
  rw [← Finset.sum_filter_add_sum_filter_not s p fun i ↦ (J i).length]
  linarith [hfpack, hgpack]

/-- The part of a parent interval left after deleting its stopping children.
These are the major subsets used by the recursive sparse construction. -/
def krauseLaceyStoppingMajorSubset
    {ι : Type*} (s : Finset ι) (J : ι → RealInterval) (I : RealInterval) : Set ℝ :=
  I.carrier \ (⋃ i ∈ s, (J i).carrier)

theorem measurableSet_krauseLaceyStoppingMajorSubset
    {ι : Type*} (s : Finset ι) (J : ι → RealInterval) (I : RealInterval) :
    MeasurableSet (krauseLaceyStoppingMajorSubset s J I) := by
  exact I.measurableSet_carrier.diff
    (Finset.measurableSet_biUnion s fun i _ ↦ (J i).measurableSet_carrier)

/-- The quantitative invariant of the KL18 sparse recursion: the stopping
children consume at most one fifth of their parent, so the retained major
subset has measure at least `4|I|/5`.  This is stronger than the source's
declared `1/4` sparse convention. -/
theorem krauseLacey_stoppingMajorSubset_measure_ge_four_fifths
    {ι : Type*} (s : Finset ι) (J : ι → RealInterval) (I : RealInterval)
    (f g : ℝ → ℂ)
    (hdisj : Set.Pairwise (↑s) (Disjoint on fun i ↦ (J i).carrier))
    (hsub : ∀ i ∈ s, (J i).carrier ⊆ I.carrier)
    (hf : IntegrableOn f I.carrier) (hg : IntegrableOn g I.carrier)
    (hbad : ∀ i ∈ s,
      10 * intervalL1Average f I < intervalL1Average f (J i) ∨
        10 * intervalL1Average g I < intervalL1Average g (J i)) :
    4 / 5 * I.length ≤
      (volume (krauseLaceyStoppingMajorSubset s J I)).toReal := by
  classical
  have hunion_sub : (⋃ i ∈ s, (J i).carrier) ⊆ I.carrier := by
    intro x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨i, hi, hxJ⟩
    exact hsub i hi hxJ
  have hunion_meas : MeasurableSet (⋃ i ∈ s, (J i).carrier) :=
    Finset.measurableSet_biUnion s fun i _ ↦ (J i).measurableSet_carrier
  have hunion_measure :
      (volume (⋃ i ∈ s, (J i).carrier)).toReal =
        ∑ i ∈ s, (J i).length := by
    change volume.real (⋃ i ∈ s, (J i).carrier) = _
    rw [MeasureTheory.measureReal_biUnion_finset (h := fun i _ ↦ by simp)
      hdisj (fun i _ ↦ (J i).measurableSet_carrier)]
    apply Finset.sum_congr rfl
    intro i hi
    exact (J i).volume_carrier_toReal
  have hpack := krauseLacey_stoppingChildren_length_le_fifth
    s J I f g hdisj hsub hf hg hbad
  rw [krauseLaceyStoppingMajorSubset]
  change 4 / 5 * I.length ≤
    volume.real (I.carrier \ (⋃ i ∈ s, (J i).carrier))
  rw [MeasureTheory.measureReal_sdiff hunion_sub hunion_meas (by simp)]
  have hI : volume.real I.carrier = I.length := by
    simpa [Measure.real] using I.volume_carrier_toReal
  have hU : volume.real (⋃ i ∈ s, (J i).carrier) =
      ∑ i ∈ s, (J i).length := by
    simpa [Measure.real] using hunion_measure
  rw [hI, hU]
  linarith

/-- In particular, every step of this recursion meets the approved KL18
`1/4` major-subset density, with considerable slack. -/
theorem krauseLacey_stoppingMajorSubset_measure_ge_quarter
    {ι : Type*} (s : Finset ι) (J : ι → RealInterval) (I : RealInterval)
    (f g : ℝ → ℂ)
    (hdisj : Set.Pairwise (↑s) (Disjoint on fun i ↦ (J i).carrier))
    (hsub : ∀ i ∈ s, (J i).carrier ⊆ I.carrier)
    (hf : IntegrableOn f I.carrier) (hg : IntegrableOn g I.carrier)
    (hbad : ∀ i ∈ s,
      10 * intervalL1Average f I < intervalL1Average f (J i) ∨
        10 * intervalL1Average g I < intervalL1Average g (J i)) :
    1 / 4 * I.length ≤
      (volume (krauseLaceyStoppingMajorSubset s J I)).toReal := by
  have hfour := krauseLacey_stoppingMajorSubset_measure_ge_four_fifths
    s J I f g hdisj hsub hf hg hbad
  have hlen := I.length_pos
  linarith

/-- A finite KL18 stopping recursion produces a sparse family.

The last hypothesis is the source's tree separation invariant: two selected
intervals are either disjoint, or the smaller interval lies inside one of the
larger's stopping children.  For a dyadic grid this follows from nesting and
maximal selection.  Unlike an assumption of sparse domination, it is purely
the structural invariant of the recursive construction.  The quantitative
major-subset estimate is derived above from the actual threshold-ten average
test. -/
theorem krauseLacey_finiteStoppingTree_isSparse
    (S : Finset RealInterval) (children : RealInterval → Finset RealInterval)
    (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (hchild_disj : ∀ I ∈ S,
      Set.Pairwise (↑(children I) : Set RealInterval)
        (Disjoint on fun J : RealInterval ↦ J.carrier))
    (hchild_sub : ∀ I ∈ S, ∀ J ∈ children I, J.carrier ⊆ I.carrier)
    (hbad : ∀ I ∈ S, ∀ J ∈ children I,
      10 * intervalL1Average f I < intervalL1Average f J ∨
        10 * intervalL1Average g I < intervalL1Average g J)
    (htree : Set.Pairwise (↑S) fun I J ↦
      Disjoint I.carrier J.carrier ∨
        (∃ K ∈ children I, J.carrier ⊆ K.carrier) ∨
          ∃ K ∈ children J, I.carrier ⊆ K.carrier) :
    IsSparse (1 / 4) (↑S : Set RealInterval) := by
  classical
  let E : {I : RealInterval // I ∈ (↑S : Set RealInterval)} → Set ℝ :=
    fun I ↦ krauseLaceyStoppingMajorSubset (children I.1) id I.1
  refine ⟨by norm_num, by norm_num, E, ?_, ?_, ?_, ?_⟩
  · intro I
    exact measurableSet_krauseLaceyStoppingMajorSubset (children I.1) id I.1
  · intro I
    exact sdiff_subset
  · intro I J hIJ
    have hval_ne : I.1 ≠ J.1 := by
      intro h
      exact hIJ (Subtype.ext h)
    rcases htree I.2 J.2 hval_ne with hparents | hdesc | hdesc
    · exact hparents.mono sdiff_subset sdiff_subset
    · rcases hdesc with ⟨K, hK, hJK⟩
      apply Set.disjoint_left.2
      intro x hxI hxJ
      exact hxI.2 (by
        simp only [mem_iUnion]
        exact ⟨K, hK, hJK hxJ.1⟩)
    · rcases hdesc with ⟨K, hK, hIK⟩
      apply Set.disjoint_left.2
      intro x hxI hxJ
      exact hxJ.2 (by
        simp only [mem_iUnion]
        exact ⟨K, hK, hIK hxI.1⟩)
  · intro I
    exact krauseLacey_stoppingMajorSubset_measure_ge_quarter
      (children I.1) id I.1 f g (hchild_disj I.1 I.2)
      (fun J hJ ↦ hchild_sub I.1 I.2 J hJ) hf.integrableOn hg.integrableOn
      (fun J hJ ↦ hbad I.1 I.2 J hJ)

end QuadraticCarleson
