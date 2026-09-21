/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyQuadraticDirectSummation

/-!
# Exceptional-interval packing in the direct quadratic proof

This is the stopping calculation used in the author's direct proof, stated
without any standard/nonstandard classification. The only geometry is a
finite laminar selected family. Intervals whose local `p`-mass exceeds
`Λ |I|` are replaced by their inclusion-maximal members; those members are
disjoint and have total length at most `Λ⁻¹ V`.
-/

open Function MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson


/-- Classical decidable equality for the selected exceptional interval families. -/
noncomputable local instance : DecidableEq RealInterval := Classical.decEq _

noncomputable
section

/-- Selected intervals on which the local `p`-mass of `g` exceeds `Λ`. -/
def directExceptionalIntervals (S : Finset RealInterval) (g : ℝ → ℂ)
    (p Λ : ℝ) : Finset RealInterval := by
  classical
  exact S.filter fun I ↦ Λ * I.length < ∫ x in I.carrier, ‖g x‖ ^ p

/-- Inclusion-maximal members of the exceptional selected intervals. -/
def directMaximalExceptionalIntervals (S : Finset RealInterval) (g : ℝ → ℂ)
    (p Λ : ℝ) : Finset RealInterval := by
  classical
  exact (directExceptionalIntervals S g p Λ).filter fun I ↦
    ∀ J ∈ directExceptionalIntervals S g p Λ, I.carrier ⊆ J.carrier → J = I

/-- The complementary selected collection on which every local `p`-mass is
at most `Λ |I|`. -/
def directRegularIntervals (S : Finset RealInterval) (g : ℝ → ℂ)
    (p Λ : ℝ) : Finset RealInterval := by
  classical
  exact S \ directExceptionalIntervals S g p Λ

theorem mem_directExceptionalIntervals_iff
    {S : Finset RealInterval} {g : ℝ → ℂ} {p Λ : ℝ} {I : RealInterval} :
    I ∈ directExceptionalIntervals S g p Λ ↔
      I ∈ S ∧ Λ * I.length < ∫ x in I.carrier, ‖g x‖ ^ p := by
  simp [directExceptionalIntervals]

theorem mem_directMaximalExceptionalIntervals_iff
    {S : Finset RealInterval} {g : ℝ → ℂ} {p Λ : ℝ} {I : RealInterval} :
    I ∈ directMaximalExceptionalIntervals S g p Λ ↔
      I ∈ directExceptionalIntervals S g p Λ ∧
        ∀ J ∈ directExceptionalIntervals S g p Λ, I.carrier ⊆ J.carrier → J = I := by
  classical
  simp [directMaximalExceptionalIntervals]

theorem mem_directRegularIntervals_iff
    {S : Finset RealInterval} {g : ℝ → ℂ} {p Λ : ℝ} {I : RealInterval} :
    I ∈ directRegularIntervals S g p Λ ↔ I ∈ S ∧
      (∫ x in I.carrier, ‖g x‖ ^ p) ≤ Λ * I.length := by
  classical
  simp only [directRegularIntervals, Finset.mem_sdiff,
    mem_directExceptionalIntervals_iff]
  constructor
  · rintro ⟨hI, hnot⟩
    refine ⟨hI, le_of_not_gt ?_⟩
    exact fun hmass ↦ hnot ⟨hI, hmass⟩
  · rintro ⟨hI, hmass⟩
    exact ⟨hI, fun hE ↦ not_lt.mpr hmass hE.2⟩

/-- The threshold split is an exact disjoint partition of the selected
interval indices. -/
theorem directRegular_union_exceptional
    (S : Finset RealInterval) (g : ℝ → ℂ) (p Λ : ℝ) :
    directRegularIntervals S g p Λ ∪ directExceptionalIntervals S g p Λ = S := by
  classical
  rw [directRegularIntervals]
  have hsub : directExceptionalIntervals S g p Λ ⊆ S := Finset.filter_subset _ _
  have hinter : S ∩ directExceptionalIntervals S g p Λ =
      directExceptionalIntervals S g p Λ := Finset.inter_eq_right.mpr hsub
  calc
    S \ directExceptionalIntervals S g p Λ ∪ directExceptionalIntervals S g p Λ =
        S \ directExceptionalIntervals S g p Λ ∪
          (S ∩ directExceptionalIntervals S g p Λ) := by rw [hinter]
    _ = S := Finset.sdiff_union_inter S (directExceptionalIntervals S g p Λ)

theorem directMaximalExceptionalIntervals_subset
    (S : Finset RealInterval) (g : ℝ → ℂ) (p Λ : ℝ) :
    directMaximalExceptionalIntervals S g p Λ ⊆ S := by
  intro I hI
  exact (mem_directExceptionalIntervals_iff.mp
    (mem_directMaximalExceptionalIntervals_iff.mp hI).1).1

private theorem direct_interval_eq_of_subset_of_length_le {I J : RealInterval}
    (hsub : I.carrier ⊆ J.carrier) (hlen : J.length ≤ I.length) : I = J := by
  have h := (Ioc_subset_Ioc_iff I.left_lt_right).mp hsub
  have hl : I.left = J.left := by
    dsimp [RealInterval.length] at hlen
    linarith
  have hr : I.right = J.right := by
    dsimp [RealInterval.length] at hlen
    linarith
  cases I
  cases J
  simp_all

/-- Every exceptional selected interval lies in a maximal exceptional one. -/
theorem directExceptional_subset_maximal
    {S : Finset RealInterval} {g : ℝ → ℂ} {p Λ : ℝ} {I : RealInterval}
    (hI : I ∈ directExceptionalIntervals S g p Λ) :
    ∃ J ∈ directMaximalExceptionalIntervals S g p Λ, I.carrier ⊆ J.carrier := by
  classical
  let A := (directExceptionalIntervals S g p Λ).filter fun J ↦ I.carrier ⊆ J.carrier
  obtain ⟨J, hJ, hmax⟩ := A.exists_max_image RealInterval.length
    ⟨I, Finset.mem_filter.mpr ⟨hI, Subset.rfl⟩⟩
  have hJ' := Finset.mem_filter.mp hJ
  refine ⟨J, mem_directMaximalExceptionalIntervals_iff.mpr ⟨hJ'.1, ?_⟩, hJ'.2⟩
  intro K hK hJK
  exact (direct_interval_eq_of_subset_of_length_le hJK
    (hmax K (Finset.mem_filter.mpr ⟨hK, hJ'.2.trans hJK⟩))).symm

/-- Maximal exceptional intervals are spatially disjoint in a laminar
selected family. -/
theorem directMaximalExceptionalIntervals_pairwiseDisjoint
    {S : Finset RealInterval} {g : ℝ → ℂ} {p Λ : ℝ}
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier) :
    Set.Pairwise (↑(directMaximalExceptionalIntervals S g p Λ) : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.carrier) := by
  intro I hI J hJ hne
  have hi := mem_directMaximalExceptionalIntervals_iff.mp hI
  have hj := mem_directMaximalExceptionalIntervals_iff.mp hJ
  rcases hlam
    (directMaximalExceptionalIntervals_subset S g p Λ hI)
    (directMaximalExceptionalIntervals_subset S g p Λ hJ) hne with hsub | hsub | hdis
  · exact (hne (hi.2 J hj.1 hsub).symm).elim
  · exact (hne (hj.2 I hi.1 hsub)).elim
  · exact hdis

private theorem sum_integral_rpow_on_disjoint_le
    {Q : Finset RealInterval} {g : ℝ → ℂ} {p : ℝ} {I₀ : RealInterval}
    (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (hdisj : Set.Pairwise (↑Q : Set RealInterval)
      (Disjoint on fun I : RealInterval ↦ I.carrier))
    (hsub : ∀ I ∈ Q, I.carrier ⊆ I₀.carrier) :
    ∑ I ∈ Q, ∫ x in I.carrier, ‖g x‖ ^ p ≤
      ∫ x in I₀.carrier, ‖g x‖ ^ p := by
  have hφ (I : RealInterval) :
      Integrable (I.carrier.indicator (fun x ↦ ‖g x‖ ^ p)) :=
    hgp.indicator I.measurableSet_carrier
  calc
    ∑ I ∈ Q, ∫ x in I.carrier, ‖g x‖ ^ p =
        ∑ I ∈ Q, ∫ x, I.carrier.indicator (fun y ↦ ‖g y‖ ^ p) x := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [integral_indicator I.measurableSet_carrier]
    _ = ∫ x, ∑ I ∈ Q, I.carrier.indicator (fun y ↦ ‖g y‖ ^ p) x := by
      exact (integral_finsetSum Q (fun I _ ↦ hφ I)).symm
    _ ≤ ∫ x, I₀.carrier.indicator (fun y ↦ ‖g y‖ ^ p) x := by
      apply integral_mono
      · exact integrable_finsetSum Q fun I _ ↦ hφ I
      · exact hgp.indicator I₀.measurableSet_carrier
      intro x
      change (∑ I ∈ Q, I.carrier.indicator (fun y ↦ ‖g y‖ ^ p) x) ≤
        I₀.carrier.indicator (fun y ↦ ‖g y‖ ^ p) x
      by_cases hx : ∃ I ∈ Q, x ∈ I.carrier
      · obtain ⟨I, hIQ, hxI⟩ := hx
        have hxroot : x ∈ I₀.carrier := hsub I hIQ hxI
        have hsum : (∑ J ∈ Q,
            J.carrier.indicator (fun y ↦ ‖g y‖ ^ p) x) =
            I.carrier.indicator (fun y ↦ ‖g y‖ ^ p) x := by
          apply Finset.sum_eq_single I
          · intro J hJQ hJI
            have hxJ : x ∉ J.carrier := by
              intro hxJ
              exact Set.disjoint_left.mp (hdisj hJQ hIQ hJI) hxJ hxI
            rw [Set.indicator_of_notMem hxJ]
          · intro hInot
            exact (hInot hIQ).elim
        rw [hsum, Set.indicator_of_mem hxI, Set.indicator_of_mem hxroot]
      · have hzero : ∀ I ∈ Q,
          I.carrier.indicator (fun y ↦ ‖g y‖ ^ p) x = 0 := by
          intro I hIQ
          rw [Set.indicator_of_notMem (fun hxI ↦ hx ⟨I, hIQ, hxI⟩)]
        rw [Finset.sum_eq_zero hzero]
        by_cases hxroot : x ∈ I₀.carrier
        · rw [Set.indicator_of_mem hxroot]
          exact Real.rpow_nonneg (norm_nonneg _) _
        · rw [Set.indicator_of_notMem hxroot]
    _ = ∫ x in I₀.carrier, ‖g x‖ ^ p := by
      rw [integral_indicator I₀.measurableSet_carrier]

/-- The maximal exceptional intervals pack by the global `p`-mass. -/
theorem directMaximalExceptionalIntervals_length_le
    {S : Finset RealInterval} {g : ℝ → ℂ} {p Λ V : ℝ} {I₀ : RealInterval}
    (hΛ : 0 < Λ) (hgp : Integrable (fun x ↦ ‖g x‖ ^ p))
    (hlam : Set.Pairwise (↑S : Set RealInterval) fun I J ↦
      I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨ Disjoint I.carrier J.carrier)
    (hsub : ∀ I ∈ S, I.carrier ⊆ I₀.carrier)
    (hglobal : (∫ x in I₀.carrier, ‖g x‖ ^ p) ≤ V) :
    ∑ I ∈ directMaximalExceptionalIntervals S g p Λ, I.length ≤ Λ⁻¹ * V := by
  let Q := directMaximalExceptionalIntervals S g p Λ
  have hterm (I : RealInterval) (hI : I ∈ Q) :
      Λ * I.length ≤ ∫ x in I.carrier, ‖g x‖ ^ p :=
    (mem_directExceptionalIntervals_iff.mp
      (mem_directMaximalExceptionalIntervals_iff.mp hI).1).2.le
  have hsum : Λ * (∑ I ∈ Q, I.length) ≤
      ∑ I ∈ Q, ∫ x in I.carrier, ‖g x‖ ^ p := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun I hI ↦ hterm I hI
  have hroot : ∑ I ∈ Q, ∫ x in I.carrier, ‖g x‖ ^ p ≤ V :=
    (sum_integral_rpow_on_disjoint_le hgp
      (directMaximalExceptionalIntervals_pairwiseDisjoint hlam)
      (fun I hI ↦ hsub I (directMaximalExceptionalIntervals_subset S g p Λ hI))).trans hglobal
  calc
    ∑ I ∈ Q, I.length = Λ⁻¹ * (Λ * ∑ I ∈ Q, I.length) := by
      field_simp [hΛ.ne']
    _ ≤ Λ⁻¹ * V := mul_le_mul_of_nonneg_left (hsum.trans hroot) (inv_nonneg.mpr hΛ.le)

/-- Abstract direct pairing closure. `P A` is the pairing contribution of a
subcollection `A`; its structural estimate is supplied separately by the
future direct `U_s` construction. The theorem records exactly the final
low/high threshold arithmetic, with no reference to the older split. -/
theorem directQuadratic_pairing_threshold_closure
    {ι : Type*} (P : Finset ι → ℝ) (S L E : Finset ι)
    {C p delta A Λ V : ℝ}
    (hdecomp : P S ≤ P L + P E)
    (hlow : P L ≤ C * (delta * A ^ (1 - p / 2) * V))
    (hhigh : P E ≤ C * (A ^ (1 - p) * Λ * V))
    (hlowid : delta * A ^ (1 - p / 2) = delta ^ (p - 1))
    (hhighid : A ^ (1 - p) * Λ = delta ^ (p - 1)) :
    P S ≤ 2 * C * delta ^ (p - 1) * V := by
  calc
    P S ≤ P L + P E := hdecomp
    _ ≤ C * (delta * A ^ (1 - p / 2) * V) +
        C * (A ^ (1 - p) * Λ * V) := add_le_add hlow hhigh
    _ = 2 * C * delta ^ (p - 1) * V := by
      rw [show delta * A ^ (1 - p / 2) * V =
        (delta * A ^ (1 - p / 2)) * V by ring, hlowid]
      rw [show A ^ (1 - p) * Λ * V = (A ^ (1 - p) * Λ) * V by ring, hhighid]
      ring

/-- The preceding closure at the exact direct choices
`δ=2^{-s/2}`, `A=δ^{-2}`, `Λ=δ^{-(p-1)}`. -/
theorem directQuadratic_pairing_threshold_closure_at_scale
    {ι : Type*} (P : Finset ι → ℝ) (S L E : Finset ι)
    {C p V : ℝ} (s : ℕ)
    (hdecomp : P S ≤ P L + P E)
    (hlow : P L ≤ C * (directQuadraticDelta s *
      directQuadraticLowThreshold s ^ (1 - p / 2) * V))
    (hhigh : P E ≤ C * (directQuadraticLowThreshold s ^ (1 - p) *
      directQuadraticExceptionalThreshold p s * V)) :
    P S ≤ 2 * C * directQuadraticDelta s ^ (p - 1) * V := by
  exact directQuadratic_pairing_threshold_closure P S L E hdecomp hlow hhigh
    (directQuadratic_low_threshold_identity p s)
    (directQuadratic_high_threshold_identity p s)


end
end QuadraticCarleson
