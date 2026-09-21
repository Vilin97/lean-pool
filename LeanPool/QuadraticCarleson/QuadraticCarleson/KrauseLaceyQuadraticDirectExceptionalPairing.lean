/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectScaleEnergy
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectThresholdClosure
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectThresholdPairing

/-!
# Exceptional pairing closure for the direct quadratic proof

This file localizes the ambient smallest-selected-region partition to a
maximal exceptional interval.  It is the combinatorial step which lets the
fixed-offset input mass under that interval be bounded by the mass of `f`
on the interval itself, without redefining the ambient partition.
-/

open Function MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace KrauseLaceyQuadraticDirectExceptionalPairing

open KrauseLaceyQuadraticDirectAction
open KrauseLaceyQuadraticDirectPartition
open KrauseLaceyQuadraticDirectScaleEnergy
open KrauseLaceyQuadraticDirectPositivePairing
open KrauseLaceyQuadraticDirectThresholdClosure
open KrauseLaceyBadScale


noncomputable section

local instance : DecidableEq RealInterval := Classical.decEq _

/-- Every bounded compactly supported test function has globally integrable
positive real powers of its norm. -/
theorem L0Infinity.integrable_norm_rpow_direct
    (f : L0Infinity) {p : ℝ} (hp : 0 < p) :
    Integrable (fun x ↦ ‖f x‖ ^ p) := by
  have hcompact : IsCompact (tsupport f) := f.hasCompactSupport_toFun
  have hfinite : volume (tsupport f) < ∞ := hcompact.measure_lt_top
  rcases f.bounded_toFun with ⟨C, hC⟩
  let D : ℝ := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hbound (x : ℝ) : ‖f x‖ ≤ D := (hC x).trans (le_max_left _ _)
  have hmeas : AEStronglyMeasurable (fun x ↦ ‖f x‖ ^ p) :=
    ((Real.continuous_rpow_const hp.le).measurable.comp
      f.measurable_toFun.norm).aestronglyMeasurable
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp
  · exact IntegrableOn.of_bound hfinite hmeas.restrict (D ^ p)
      (Filter.Eventually.of_forall fun x ↦ by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact Real.rpow_le_rpow (norm_nonneg _) (hbound x) hp.le)
  · intro x hx
    apply subset_tsupport f
    intro hzero
    apply hx
    simp [hzero, Real.zero_rpow hp.ne']

/-- The selected intervals spatially contained in `Q`. -/
def selectedInside (S : Finset RealInterval) (Q : RealInterval) :
    Finset RealInterval := by
  classical
  exact S.filter fun J ↦ J.carrier ⊆ Q.carrier

theorem mem_selectedInside_iff
    {S : Finset RealInterval} {Q J : RealInterval} :
    J ∈ selectedInside S Q ↔ J ∈ S ∧ J.carrier ⊆ Q.carrier := by
  simp [selectedInside]

/-- Passing to all selected intervals inside `Q` does not change the
smallest-selected region of an interval already contained in `Q`. -/
theorem smallestSelectedRegion_selectedInside_eq
    (S : Finset RealInterval) (Q J : RealInterval)
    (hJQ : J.carrier ⊆ Q.carrier) :
    smallestSelectedRegion (selectedInside S Q) J =
      smallestSelectedRegion S J := by
  ext x
  rw [mem_smallestSelectedRegion_iff, mem_smallestSelectedRegion_iff]
  constructor
  · rintro ⟨hxJ, hmin⟩
    refine ⟨hxJ, ?_⟩
    intro H hHS hHJ hHJsub
    exact hmin H (mem_selectedInside_iff.mpr ⟨hHS, hHJsub.trans hJQ⟩)
      hHJ hHJsub
  · rintro ⟨hxJ, hmin⟩
    refine ⟨hxJ, ?_⟩
    intro H hHin hHJ hHJsub
    exact hmin H (mem_selectedInside_iff.mp hHin).1 hHJ hHJsub

/-- For an output interval inside `Q`, restricting the ambient selected
family to `Q` leaves the fixed-offset grouped input unchanged. -/
theorem offsetGroupedInput_selectedInside_eq
    (S : Finset RealInterval) (Q I : RealInterval)
    (scale : RealInterval → ℤ) (f : ℝ → ℂ) (s : ℤ)
    (hIQ : I.carrier ⊆ Q.carrier) :
    offsetGroupedInput (selectedInside S Q) scale f I s =
      offsetGroupedInput S scale f I s := by
  classical
  have hselected :
      selectedSubintervals (selectedInside S Q) I =
        selectedSubintervals S I := by
    ext J
    simp only [mem_selectedSubintervals_iff, mem_selectedInside_iff]
    constructor
    · rintro ⟨⟨hJS, hJQ⟩, hJI⟩
      exact ⟨hJS, hJI⟩
    · rintro ⟨hJS, hJI⟩
      exact ⟨⟨hJS, hJI.trans hIQ⟩, hJI⟩
  funext x
  unfold offsetGroupedInput
  rw [hselected]
  apply Finset.sum_congr rfl
  intro J hJ
  have hJI : J.carrier ⊆ I.carrier :=
    (mem_selectedSubintervals_iff.mp (Finset.mem_filter.mp hJ).1).2
  rw [smallestSelectedRegion_selectedInside_eq S Q J (hJI.trans hIQ)]

/-- The fixed-offset masses of any output subcollection contained in `Q`
are bounded by the `f`-mass of `Q`.  The smallest-region partition remains
the one formed by the original ambient family `S`. -/
theorem sum_offsetGroupedInput_mass_le_interval
    {S A : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s)
    (Q : RealInterval) (hA : A ⊆ S)
    (hAQ : ∀ I ∈ A, I.carrier ⊆ Q.carrier) :
    ∑ k ∈ A.image scale, ∑ I ∈ A.filter (fun I ↦ scale I = k),
        ∫ x, ‖offsetGroupedInput S scale f I s x‖ ≤
      ∫ x in Q.carrier, ‖f x‖ := by
  classical
  let SQ := selectedInside S Q
  have hASQ : A ⊆ SQ := by
    intro I hI
    exact mem_selectedInside_iff.mpr ⟨hA hI, hAQ I hI⟩
  have hlamQ : Set.Pairwise (↑SQ : Set RealInterval) (fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier) := by
    intro I hI J hJ hne
    exact hlam (mem_selectedInside_iff.mp hI).1
      (mem_selectedInside_iff.mp hJ).1 hne
  have hscaleQ : ∀ I ∈ SQ, I.length = (2 : ℝ) ^ (scale I + 2) := by
    intro I hI
    exact hscale I (mem_selectedInside_iff.mp hI).1
  have hsubQ : ∀ I ∈ SQ, I.carrier ⊆ Q.carrier := by
    intro I hI
    exact (mem_selectedInside_iff.mp hI).2
  have hmass := sum_integral_norm_offsetGroupedInput_allScales_le_root
    hASQ hlamQ scale hscaleQ f hs Q hsubQ
  calc
    ∑ k ∈ A.image scale, ∑ I ∈ A.filter (fun I ↦ scale I = k),
        ∫ x, ‖offsetGroupedInput S scale f I s x‖ =
      ∑ k ∈ A.image scale, ∑ I ∈ A.filter (fun I ↦ scale I = k),
        ∫ x, ‖offsetGroupedInput SQ scale f I s x‖ := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro I hI
          rw [offsetGroupedInput_selectedInside_eq S Q I scale f s
            (hAQ I (Finset.mem_filter.mp hI).1)]
    _ ≤ ∫ x in Q.carrier, ‖f x‖ := hmass

/-- The same local mass bound with the artificial scale fibers removed. -/
theorem sum_offsetGroupedInput_mass_le_interval_unfibered
    {S A : Finset RealInterval}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s)
    (Q : RealInterval) (hA : A ⊆ S)
    (hAQ : ∀ I ∈ A, I.carrier ⊆ Q.carrier) :
    ∑ I ∈ A, ∫ x, ‖offsetGroupedInput S scale f I s x‖ ≤
      ∫ x in Q.carrier, ‖f x‖ := by
  calc
    ∑ I ∈ A, ∫ x, ‖offsetGroupedInput S scale f I s x‖ =
        ∑ k ∈ A.image scale, ∑ I ∈ A.filter (fun I ↦ scale I = k),
          ∫ x, ‖offsetGroupedInput S scale f I s x‖ := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun I hI ↦ Finset.mem_image.mpr ⟨I, hI, rfl⟩) _
    _ ≤ ∫ x in Q.carrier, ‖f x‖ :=
      sum_offsetGroupedInput_mass_le_interval hlam scale hscale f hs Q hA hAQ

/-- Exceptional output intervals lying below a fixed maximal exceptional
interval. -/
def exceptionalBelow (S : Finset RealInterval) (g : ℝ → ℂ)
    (p Λ : ℝ) (Q : RealInterval) : Finset RealInterval := by
  classical
  exact (directExceptionalIntervals S g p Λ).filter fun I ↦
    I.carrier ⊆ Q.carrier

theorem mem_exceptionalBelow_iff
    {S : Finset RealInterval} {g : ℝ → ℂ} {p Λ : ℝ}
    {Q I : RealInterval} :
    I ∈ exceptionalBelow S g p Λ Q ↔
      I ∈ directExceptionalIntervals S g p Λ ∧
        I.carrier ⊆ Q.carrier := by
  simp [exceptionalBelow]

/-- The exceptional descendants of distinct maximal exceptional intervals
are disjoint as finite index sets. -/
theorem exceptionalBelow_pairwiseDisjoint
    {S : Finset RealInterval} {g : ℝ → ℂ} {p Λ : ℝ}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier) :
    Set.Pairwise
      (↑(directMaximalExceptionalIntervals S g p Λ) : Set RealInterval)
      (Disjoint on exceptionalBelow S g p Λ) := by
  intro Q hQ R hR hQR
  change Disjoint (exceptionalBelow S g p Λ Q)
    (exceptionalBelow S g p Λ R)
  rw [Finset.disjoint_left]
  intro I hIQ hIR
  have hsubQ := (mem_exceptionalBelow_iff.mp hIQ).2
  have hsubR := (mem_exceptionalBelow_iff.mp hIR).2
  have hx : I.right ∈ I.carrier := by
    exact ⟨I.left_lt_right, le_rfl⟩
  exact Set.disjoint_left.mp
    (directMaximalExceptionalIntervals_pairwiseDisjoint hlam hQ hR hQR)
    (hsubQ hx) (hsubR hx)

/-- Every exceptional interval belongs to the descendants of a maximal
exceptional interval, and conversely. -/
theorem biUnion_exceptionalBelow_maximal
    (S : Finset RealInterval) (g : ℝ → ℂ) (p Λ : ℝ) :
    (directMaximalExceptionalIntervals S g p Λ).biUnion
        (exceptionalBelow S g p Λ) =
      directExceptionalIntervals S g p Λ := by
  classical
  apply Finset.Subset.antisymm
  · intro I hI
    obtain ⟨Q, hQ, hIQ⟩ := Finset.mem_biUnion.mp hI
    exact (mem_exceptionalBelow_iff.mp hIQ).1
  · intro I hI
    obtain ⟨Q, hQ, hIQ⟩ := directExceptional_subset_maximal hI
    exact Finset.mem_biUnion.mpr
      ⟨Q, hQ, mem_exceptionalBelow_iff.mpr ⟨hI, hIQ⟩⟩

/-- The fixed-offset input mass of all exceptional outputs is bounded by
the sum of the `f`-masses of their maximal exceptional roots. -/
theorem sum_exceptional_offsetGroupedInput_mass_le_maximal_roots
    {S : Finset RealInterval} {g : ℝ → ℂ} {p Λ : ℝ}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) :
    ∑ I ∈ directExceptionalIntervals S g p Λ,
        ∫ x, ‖offsetGroupedInput S scale f I s x‖ ≤
      ∑ Q ∈ directMaximalExceptionalIntervals S g p Λ,
        ∫ x in Q.carrier, ‖f x‖ := by
  classical
  let E := directExceptionalIntervals S g p Λ
  let Qs := directMaximalExceptionalIntervals S g p Λ
  let mass : RealInterval → ℝ := fun I ↦
    ∫ x, ‖offsetGroupedInput S scale f I s x‖
  have hsplit :
      (∑ I ∈ E, mass I) =
        ∑ Q ∈ Qs, ∑ I ∈ exceptionalBelow S g p Λ Q, mass I := by
    rw [← Finset.sum_biUnion (exceptionalBelow_pairwiseDisjoint hlam)]
    rw [biUnion_exceptionalBelow_maximal]
  rw [hsplit]
  apply Finset.sum_le_sum
  intro Q hQ
  apply sum_offsetGroupedInput_mass_le_interval_unfibered
    hlam scale hscale f hs Q
  · intro I hI
    exact (mem_directExceptionalIntervals_iff.mp
      (mem_exceptionalBelow_iff.mp hI).1).1
  · intro I hI
    exact (mem_exceptionalBelow_iff.mp hI).2

/-- Combining the localized mass estimate with average control on the
maximal exceptional roots converts their packing into fixed-offset input
mass decay. -/
theorem sum_exceptional_offsetGroupedInput_mass_le_of_packing
    {S : Finset RealInterval} {g : ℝ → ℂ} {p Λ F L : ℝ}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) (hF : 0 ≤ F)
    (hfavg : ∀ Q ∈ directMaximalExceptionalIntervals S g p Λ,
      intervalL1Average f Q ≤ F)
    (hpack : ∑ Q ∈ directMaximalExceptionalIntervals S g p Λ,
      Q.length ≤ L) :
    ∑ I ∈ directExceptionalIntervals S g p Λ,
        ∫ x, ‖offsetGroupedInput S scale f I s x‖ ≤ F * L := by
  calc
    ∑ I ∈ directExceptionalIntervals S g p Λ,
        ∫ x, ‖offsetGroupedInput S scale f I s x‖ ≤
      ∑ Q ∈ directMaximalExceptionalIntervals S g p Λ,
        ∫ x in Q.carrier, ‖f x‖ :=
      sum_exceptional_offsetGroupedInput_mass_le_maximal_roots
        hlam scale hscale f hs
    _ = ∑ Q ∈ directMaximalExceptionalIntervals S g p Λ,
        intervalL1Average f Q * Q.length := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact (intervalL1Average_mul_length f Q).symm
    _ ≤ ∑ Q ∈ directMaximalExceptionalIntervals S g p Λ,
        F * Q.length := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact mul_le_mul_of_nonneg_right (hfavg Q hQ) Q.length_pos.le
    _ = F * ∑ Q ∈ directMaximalExceptionalIntervals S g p Λ,
        Q.length := by rw [Finset.mul_sum]
    _ ≤ F * L := mul_le_mul_of_nonneg_left hpack hF

/-- The full positive pairing of the exceptional output family.  Uniform
`L¹` averages of the test function and of `f` on maximal exceptional roots,
together with root packing, give the expected packing-sized contribution. -/
theorem lintegral_exceptional_offsetTailMaximalOn_le_of_packing
    {S : Finset RealInterval} {g : L0Infinity} {p Λ F G L : ℝ}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) (ell₀ : ℤ)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfavg : ∀ Q ∈ directMaximalExceptionalIntervals S g p Λ,
      intervalL1Average f Q ≤ F)
    (hgavg : ∀ I ∈ S, intervalL1Average g I ≤ G)
    (hpack : ∑ Q ∈ directMaximalExceptionalIntervals S g p Λ,
      Q.length ≤ L) :
    (∫⁻ x, offsetTailMaximalOn S
        (directExceptionalIntervals S g p Λ) scale f ell₀ s x * ‖g x‖ₑ) ≤
      ENNReal.ofReal
        (8 * positiveDyadicAmplitudeBound * G * F * L) := by
  let E := directExceptionalIntervals S g p Λ
  let mass : RealInterval → ℝ := fun I ↦
    ∫ x, ‖offsetGroupedInput S scale f I s x‖
  have hstruct :=
    lintegral_offsetTailMaximalOn_pairing_le_sum_local_averages
      S E scale f g g.integrable_finiteSparseProof ell₀ s
      (fun I hI ↦ hscale I
        (mem_directExceptionalIntervals_iff.mp hI).1)
  have hterm :
      (∑ I ∈ E, 8 * positiveDyadicAmplitudeBound * mass I *
          intervalL1Average g I) ≤
        (8 * positiveDyadicAmplitudeBound * G) *
          ∑ I ∈ E, mass I := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro I hI
    have hIS : I ∈ S :=
      (mem_directExceptionalIntervals_iff.mp hI).1
    have hmass0 : 0 ≤ mass I := integral_nonneg fun _ ↦ norm_nonneg _
    calc
      8 * positiveDyadicAmplitudeBound * mass I *
          intervalL1Average g I ≤
        8 * positiveDyadicAmplitudeBound * mass I * G :=
          mul_le_mul_of_nonneg_left (hgavg I hIS)
            (mul_nonneg
              (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
              hmass0)
      _ = (8 * positiveDyadicAmplitudeBound * G) * mass I := by ring
  have hmass : (∑ I ∈ E, mass I) ≤ F * L := by
    exact sum_exceptional_offsetGroupedInput_mass_le_of_packing
      hlam scale hscale f hs hF hfavg hpack
  calc
    (∫⁻ x, offsetTailMaximalOn S E scale f ell₀ s x * ‖g x‖ₑ) ≤
        ENNReal.ofReal (∑ I ∈ E, 8 * positiveDyadicAmplitudeBound *
          mass I * intervalL1Average g I) := hstruct
    _ ≤ ENNReal.ofReal ((8 * positiveDyadicAmplitudeBound * G) *
          ∑ I ∈ E, mass I) := ENNReal.ofReal_le_ofReal hterm
    _ ≤ ENNReal.ofReal ((8 * positiveDyadicAmplitudeBound * G) *
          (F * L)) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hmass
        (mul_nonneg
          (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg) hG)
    _ = ENNReal.ofReal
        (8 * positiveDyadicAmplitudeBound * G * F * L) := by ring

/-- The exceptional contribution at the author's exact threshold
`Λ = δ^{-(p-1)}`.  The global `p`-mass supplies the maximal-root packing,
so the result has the desired `δ^{p-1}` decay. -/
theorem lintegral_exceptional_offsetTailMaximalOn_le_directQuadratic
    {S : Finset RealInterval} {g : L0Infinity} {p F G V : ℝ}
    (n : ℕ) (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) (ell₀ : ℤ)
    (I₀ : RealInterval) (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hglobal : (∫ x in I₀.carrier, ‖g x‖ ^ p) ≤ V)
    (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hfavg : ∀ Q ∈ directMaximalExceptionalIntervals S g p
        (directQuadraticExceptionalThreshold p n),
      intervalL1Average f Q ≤ F)
    (hgavg : ∀ I ∈ S, intervalL1Average g I ≤ G) :
    (∫⁻ x, offsetTailMaximalOn S
        (directExceptionalIntervals S g p
          (directQuadraticExceptionalThreshold p n))
        scale f ell₀ s x * ‖g x‖ₑ) ≤
      ENNReal.ofReal (8 * positiveDyadicAmplitudeBound * G * F *
        (directQuadraticDelta n ^ (p - 1) * V)) := by
  apply lintegral_exceptional_offsetTailMaximalOn_le_of_packing
    hlam scale hscale f hs ell₀ hF hG hfavg hgavg
  exact directMaximalExceptional_length_le_directQuadratic_threshold
    n hgp hlam hsub hglobal

/-- Direct high-truncation pairing on a regular output subcollection.  This
is the `(**)` half of the author's proof, with no standard/nonstandard
classification: the local `p`-mass cutoff supplies `a^(1-p) G`, and the
ambient partition supplies the total `f`-mass. -/
theorem lintegral_offsetTailMaximalOn_interpolationHigh_le
    {S A : Finset RealInterval} {g : L0Infinity} {a p G : ℝ}
    (ha : 0 < a) (hp : 1 < p) (hG : 0 ≤ G)
    (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) {s : ℤ} (hs : 0 ≤ s) (ell₀ : ℤ)
    (I₀ : RealInterval) (hA : A ⊆ S)
    (hsub : ∀ I ∈ A, I.carrier ⊆ I₀.carrier)
    (hgavg : ∀ I ∈ A,
      (∫ x in I.carrier, ‖g x‖ ^ p) ≤ G * I.length) :
    (∫⁻ x, offsetTailMaximalOn S A scale f ell₀ s x *
        ‖interpolationHigh g a x‖ₑ) ≤
      ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
        (a ^ (1 - p) * G) * ∫ x in I₀.carrier, ‖f x‖) := by
  let mass : RealInterval → ℝ := fun I ↦
    ∫ x, ‖offsetGroupedInput S scale f I s x‖
  let H : ℝ := a ^ (1 - p) * G
  have hH : 0 ≤ H := mul_nonneg (Real.rpow_nonneg ha.le _) hG
  have hhigh : Integrable (interpolationHigh g a) :=
    integrable_interpolationHigh_local g.measurable_toFun
      g.integrable_finiteSparseProof a
  have hstruct :=
    lintegral_offsetTailMaximalOn_pairing_le_sum_local_averages
      S A scale f (interpolationHigh g a) hhigh ell₀ s
      (fun I hI ↦ hscale I (hA hI))
  have havg (I : RealInterval) (hI : I ∈ A) :
      intervalL1Average (interpolationHigh g a) I ≤ H := by
    exact intervalL1Average_interpolationHigh_le g.measurable_toFun
      g.integrable_finiteSparseProof ha hp hgp I (hgavg I hI)
  have hterm :
      (∑ I ∈ A, 8 * positiveDyadicAmplitudeBound * mass I *
          intervalL1Average (interpolationHigh g a) I) ≤
        (8 * positiveDyadicAmplitudeBound * H) * ∑ I ∈ A, mass I := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro I hI
    have hmass0 : 0 ≤ mass I := integral_nonneg fun _ ↦ norm_nonneg _
    calc
      8 * positiveDyadicAmplitudeBound * mass I *
          intervalL1Average (interpolationHigh g a) I ≤
        8 * positiveDyadicAmplitudeBound * mass I * H :=
          mul_le_mul_of_nonneg_left (havg I hI)
            (mul_nonneg
              (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg)
              hmass0)
      _ = (8 * positiveDyadicAmplitudeBound * H) * mass I := by ring
  have hmass : (∑ I ∈ A, mass I) ≤ ∫ x in I₀.carrier, ‖f x‖ :=
    sum_offsetGroupedInput_mass_le_interval_unfibered
      hlam scale hscale f hs I₀ hA hsub
  calc
    (∫⁻ x, offsetTailMaximalOn S A scale f ell₀ s x *
        ‖interpolationHigh g a x‖ₑ) ≤
      ENNReal.ofReal (∑ I ∈ A, 8 * positiveDyadicAmplitudeBound *
        mass I * intervalL1Average (interpolationHigh g a) I) := hstruct
    _ ≤ ENNReal.ofReal ((8 * positiveDyadicAmplitudeBound * H) *
        ∑ I ∈ A, mass I) := ENNReal.ofReal_le_ofReal hterm
    _ ≤ ENNReal.ofReal ((8 * positiveDyadicAmplitudeBound * H) *
        ∫ x in I₀.carrier, ‖f x‖) := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hmass
        (mul_nonneg
          (mul_nonneg (by norm_num) positiveDyadicAmplitudeBound_nonneg) hH)
    _ = ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
        (a ^ (1 - p) * G) * ∫ x in I₀.carrier, ‖f x‖) := by
      rfl

/-- The regular high-truncation term at the author's simultaneous choices
`A = δ⁻²` and `Λ = δ^{-(p-1)}`. -/
theorem lintegral_regular_offsetTailMaximalOn_interpolationHigh_le_directQuadratic
    {S : Finset RealInterval} {g : L0Infinity} {p : ℝ}
    (n : ℕ) (hp : 1 < p)
    (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier)
    (scale : RealInterval → ℤ)
    (hscale : ∀ I ∈ S, I.length = (2 : ℝ) ^ (scale I + 2))
    (f : L0Infinity) (ell₀ : ℤ) (I₀ : RealInterval)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier) :
    (∫⁻ x, offsetTailMaximalOn S
        (directRegularIntervals S g p
          (directQuadraticExceptionalThreshold p n))
        scale f ell₀ (n : ℤ) x *
          ‖interpolationHigh g (directQuadraticLowThreshold n) x‖ₑ) ≤
      ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
        directQuadraticDelta n ^ (p - 1) *
          ∫ x in I₀.carrier, ‖f x‖) := by
  let A := directRegularIntervals S g p
    (directQuadraticExceptionalThreshold p n)
  have hA : A ⊆ S := by
    intro I hI
    exact (mem_directRegularIntervals_iff.mp hI).1
  have hAroot : ∀ I ∈ A, I.carrier ⊆ I₀.carrier := by
    intro I hI
    exact hsub I (hA hI)
  have hlocal : ∀ I ∈ A,
      (∫ x in I.carrier, ‖g x‖ ^ p) ≤
        directQuadraticExceptionalThreshold p n * I.length := by
    intro I hI
    exact (mem_directRegularIntervals_iff.mp hI).2
  have hhigh := lintegral_offsetTailMaximalOn_interpolationHigh_le
    (a := directQuadraticLowThreshold n) (p := p)
    (G := directQuadraticExceptionalThreshold p n) (s := (n : ℤ))
    (Real.rpow_pos_of_pos (directQuadraticDelta_pos n) _) hp
    (Real.rpow_nonneg (directQuadraticDelta_pos n).le _) hgp
    hlam scale hscale f (by exact_mod_cast n.zero_le) ell₀ I₀ hA hAroot hlocal
  calc
    (∫⁻ x, offsetTailMaximalOn S A scale f ell₀ (n : ℤ) x *
        ‖interpolationHigh g (directQuadraticLowThreshold n) x‖ₑ) ≤
      ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
        (directQuadraticLowThreshold n ^ (1 - p) *
          directQuadraticExceptionalThreshold p n) *
          ∫ x in I₀.carrier, ‖f x‖) := hhigh
    _ = ENNReal.ofReal (8 * positiveDyadicAmplitudeBound *
        directQuadraticDelta n ^ (p - 1) *
          ∫ x in I₀.carrier, ‖f x‖) := by
      rw [directQuadratic_high_threshold_identity]


end
end KrauseLaceyQuadraticDirectExceptionalPairing
end QuadraticCarleson
