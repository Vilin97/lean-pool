/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Probability.Distributions.Uniform

/-!
# Constant-weight bitmap null

This file starts the finite combinatorial route for the constant-weight bitmap
overlap null. The central object is the uniform space of `K`-subsets of a
`D`-coordinate universe, represented as `Fin D`.

The main counting bijection identifies overlap-constrained bitmaps
with a pair consisting of the `x` coordinates selected inside the query bitmap
and the `K - x` coordinates selected outside it.
-/

open scoped NNReal ENNReal

namespace OrdvecFormalization

/-- The finite coordinate universe for a bitmap with `D` coordinates. -/
abbrev BitmapCoord (D : ℕ) := Fin D

/-- The space of constant-weight bitmaps with exactly `K` active coordinates. -/
def constantWeightBitmapSpace (D K : ℕ) : Finset (Finset (BitmapCoord D)) :=
  Finset.univ.powersetCard K

@[simp]
theorem mem_constantWeightBitmapSpace_iff {D K : ℕ} {s : Finset (BitmapCoord D)} :
    s ∈ constantWeightBitmapSpace D K ↔ s.card = K := by
  simp [constantWeightBitmapSpace]

/-- The number of `K`-active bitmaps over `D` coordinates is `D.choose K`. -/
@[simp]
theorem card_constantWeightBitmapSpace (D K : ℕ) :
    (constantWeightBitmapSpace D K).card = D.choose K := by
  simp [constantWeightBitmapSpace]

/-- The `K`-active bitmap space is nonempty exactly in the feasible case `K <= D`. -/
theorem constantWeightBitmapSpace_nonempty {D K : ℕ} (hK : K ≤ D) :
    (constantWeightBitmapSpace D K).Nonempty := by
  have hKuniv : K ≤ (Finset.univ : Finset (BitmapCoord D)).card := by
    simpa using hK
  simpa [constantWeightBitmapSpace] using
    (Finset.powersetCard_nonempty_of_le (s := (Finset.univ : Finset (BitmapCoord D))) hKuniv)

/-- Bitmap overlap is the cardinality of the bitwise intersection. -/
def bitmapOverlap {D : ℕ} (q d : Finset (BitmapCoord D)) : ℕ :=
  (q ∩ d).card

/-- The event that a `K`-active bitmap has overlap exactly `x` with `q`. -/
def bitmapOverlapFiber (D K x : ℕ) (q : Finset (BitmapCoord D)) :
    Finset (Finset (BitmapCoord D)) :=
  (constantWeightBitmapSpace D K).filter fun d => bitmapOverlap q d = x

@[simp]
theorem mem_bitmapOverlapFiber_iff {D K x : ℕ} {q d : Finset (BitmapCoord D)} :
    d ∈ bitmapOverlapFiber D K x q ↔ d.card = K ∧ bitmapOverlap q d = x := by
  simp [bitmapOverlapFiber]

/-- The event that a `K`-active bitmap clears threshold `t` against `q`. -/
def bitmapOverlapTailEvent (D K t : ℕ) (q : Finset (BitmapCoord D)) :
    Finset (Finset (BitmapCoord D)) :=
  (constantWeightBitmapSpace D K).filter fun d => t ≤ bitmapOverlap q d

@[simp]
theorem mem_bitmapOverlapTailEvent_iff {D K t : ℕ} {q d : Finset (BitmapCoord D)} :
    d ∈ bitmapOverlapTailEvent D K t q ↔ d.card = K ∧ t ≤ bitmapOverlap q d := by
  simp [bitmapOverlapTailEvent]

/-- Coordinates outside a query bitmap. -/
def bitmapComplement {D : ℕ} (q : Finset (BitmapCoord D)) : Finset (BitmapCoord D) :=
  Finset.univ \ q

@[simp]
theorem card_bitmapComplement {D : ℕ} (q : Finset (BitmapCoord D)) :
    (bitmapComplement q).card = D - q.card := by
  simp [bitmapComplement, Finset.card_univ_sdiff, Fintype.card_fin]

/--
Structured choices for an overlap-`x` bitmap:
choose `x` coordinates inside the query bitmap and `K - x` outside it.
-/
def insideOutsideChoices {D : ℕ} (K x : ℕ) (q : Finset (BitmapCoord D)) :
    Finset (Finset (BitmapCoord D) × Finset (BitmapCoord D)) :=
  (q.powersetCard x).product ((bitmapComplement q).powersetCard (K - x))

@[simp]
theorem mem_insideOutsideChoices_iff {D K x : ℕ} {q : Finset (BitmapCoord D)}
    {ab : Finset (BitmapCoord D) × Finset (BitmapCoord D)} :
    ab ∈ insideOutsideChoices K x q ↔
      ab.1 ⊆ q ∧ ab.1.card = x ∧ ab.2 ⊆ bitmapComplement q ∧ ab.2.card = K - x := by
  simp [insideOutsideChoices, and_assoc]

/-- Cardinality of the structured inside/outside choice space. -/
theorem card_insideOutsideChoices {D K x : ℕ} (q : Finset (BitmapCoord D)) :
    (insideOutsideChoices K x q).card =
      q.card.choose x * (D - q.card).choose (K - x) := by
  simp [insideOutsideChoices]

/-- The hypergeometric numerator for the constant-weight bitmap null. -/
def bitmapHypergeomNumerator (D K x : ℕ) : ℕ :=
  K.choose x * (D - K).choose (K - x)

/--
For a `K`-active query bitmap, the structured inside/outside choices have the
hypergeometric numerator cardinality.
-/
theorem card_insideOutsideChoices_of_query_card {D K x : ℕ}
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    (insideOutsideChoices K x q).card = bitmapHypergeomNumerator D K x := by
  rw [card_insideOutsideChoices, hq, bitmapHypergeomNumerator]

private theorem overlapFiber_card_eq_insideOutsideChoices_card_of_query_card {D K x : ℕ}
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    (bitmapOverlapFiber D K x q).card = (insideOutsideChoices K x q).card := by
  classical
  have h_inter : ∀ ab ∈ insideOutsideChoices K x q, q ∩ (ab.1 ∪ ab.2) = ab.1 := by
    intro ab hab
    obtain ⟨haq, _hax, hbq, _hbx⟩ := mem_insideOutsideChoices_iff.mp hab
    ext y
    constructor
    · intro hy
      rcases Finset.mem_inter.mp hy with ⟨hyq, hyu⟩
      rcases Finset.mem_union.mp hyu with hya | hyb
      · exact hya
      · have hynq : y ∉ q := by
          simpa [bitmapComplement] using hbq hyb
        exact False.elim (hynq hyq)
    · intro hya
      exact Finset.mem_inter.mpr ⟨haq hya, Finset.mem_union_left _ hya⟩
  refine Finset.card_bij'
    (fun d _ => (q ∩ d, d \ q))
    (fun ab _ => ab.1 ∪ ab.2)
    ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hdK, hdx⟩ := mem_bitmapOverlapFiber_iff.mp hd
    rw [mem_insideOutsideChoices_iff]
    constructor
    · exact Finset.inter_subset_left
    constructor
    · exact hdx
    constructor
    · intro y hy
      have hynq : y ∉ q := (Finset.mem_sdiff.mp hy).2
      simpa [bitmapComplement] using Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hynq⟩
    · have hsum := Finset.card_sdiff_add_card_inter d q
      have hinter : (d ∩ q).card = x := by
        simpa [bitmapOverlap, Finset.inter_comm] using hdx
      have hxK : x ≤ K := by
        rw [← hdK, ← hinter]
        exact Finset.card_le_card Finset.inter_subset_left
      symm
      rw [tsub_eq_iff_eq_add_of_le hxK]
      change K = (d \ q).card + x
      omega
  · intro ab hab
    obtain ⟨haq, hax, hbq, hbx⟩ := mem_insideOutsideChoices_iff.mp hab
    rw [mem_bitmapOverlapFiber_iff]
    have hdisj : Disjoint ab.1 ab.2 := by
      rw [Finset.disjoint_left]
      intro y hya hyb
      have hyq : y ∈ q := haq hya
      have hynq : y ∉ q := by
        simpa [bitmapComplement] using hbq hyb
      exact hynq hyq
    have hcardUnion : (ab.1 ∪ ab.2).card = ab.1.card + ab.2.card :=
      Finset.card_union_of_disjoint hdisj
    have hxK : x ≤ K := by
      rw [← hq, ← hax]
      exact Finset.card_le_card haq
    have hinter := h_inter ab hab
    constructor
    · omega
    · simp [bitmapOverlap, hinter, hax]
  · intro d hd
    ext y
    by_cases hyq : y ∈ q <;> simp [hyq]
  · intro ab hab
    obtain ⟨haq, _hax, hbq, _hbx⟩ := mem_insideOutsideChoices_iff.mp hab
    apply Prod.ext
    · exact h_inter ab hab
    · ext y
      constructor
      · intro hy
        rcases Finset.mem_sdiff.mp hy with ⟨hyu, hynq⟩
        rcases Finset.mem_union.mp hyu with hya | hyb
        · exact False.elim (hynq (haq hya))
        · exact hyb
      · intro hyb
        have hynq : y ∉ q := by
          simpa [bitmapComplement] using hbq hyb
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hyb, hynq⟩

theorem card_bitmapOverlapFiber_of_query_card {D K x : ℕ}
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    (bitmapOverlapFiber D K x q).card = bitmapHypergeomNumerator D K x := by
  rw [overlapFiber_card_eq_insideOutsideChoices_card_of_query_card hq,
    card_insideOutsideChoices_of_query_card hq]

/-- Closed-form point mass for the bitmap overlap null. -/
noncomputable def bitmapHypergeomMass (D K x : ℕ) : ℝ≥0 :=
  (bitmapHypergeomNumerator D K x : ℝ≥0) / (D.choose K : ℝ≥0)

/-- Closed-form point mass as the structured choice count divided by all `K`-subsets. -/
theorem bitmapHypergeomMass_eq_insideOutsideChoices_card_ratio {D K x : ℕ}
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    bitmapHypergeomMass D K x =
      ((insideOutsideChoices K x q).card : ℝ≥0) / (D.choose K : ℝ≥0) := by
  rw [bitmapHypergeomMass, card_insideOutsideChoices_of_query_card hq]

/-- Closed-form point mass as the overlap-fiber count divided by all `K`-subsets. -/
theorem bitmapHypergeomMass_eq_overlapFiber_card_ratio {D K x : ℕ}
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    bitmapHypergeomMass D K x =
      ((bitmapOverlapFiber D K x q).card : ℝ≥0) / (D.choose K : ℝ≥0) := by
  rw [bitmapHypergeomMass, card_bitmapOverlapFiber_of_query_card hq]

/-- Closed-form upper-tail mass for the bitmap overlap null. -/
noncomputable def bitmapHypergeomTail (D K t : ℕ) : ℝ≥0 :=
  (Finset.range (K + 1)).sum fun x =>
    if t ≤ x then bitmapHypergeomMass D K x else 0

/-- Exact finite mass of a threshold event, as a cardinal ratio. -/
noncomputable def bitmapOverlapTailMass (D K t : ℕ) (q : Finset (BitmapCoord D)) : ℝ≥0 :=
  ((bitmapOverlapTailEvent D K t q).card : ℝ≥0) / (D.choose K : ℝ≥0)

/-- The threshold event partitions into exact-overlap fibers over feasible overlap values. -/
theorem card_bitmapOverlapTailEvent_eq_sum_overlapFiber_card_of_query_card {D K t : ℕ}
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    (bitmapOverlapTailEvent D K t q).card =
      (Finset.range (K + 1)).sum fun x =>
        if t ≤ x then (bitmapOverlapFiber D K x q).card else 0 := by
  classical
  have hmaps :
      (bitmapOverlapTailEvent D K t q : Set (Finset (BitmapCoord D))).MapsTo
        (fun d => bitmapOverlap q d) (Finset.range (K + 1)) := by
    intro d hd
    have hle : bitmapOverlap q d ≤ K := by
      rw [bitmapOverlap, ← hq]
      exact Finset.card_le_card Finset.inter_subset_left
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl ?_
  intro x hx
  by_cases htx : t ≤ x
  · rw [if_pos htx]
    apply congrArg Finset.card
    ext d
    constructor
    · intro hd
      obtain ⟨hdtail, hdx⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdK, _hdt⟩ := mem_bitmapOverlapTailEvent_iff.mp hdtail
      exact mem_bitmapOverlapFiber_iff.mpr ⟨hdK, hdx⟩
    · intro hd
      obtain ⟨hdK, hdx⟩ := mem_bitmapOverlapFiber_iff.mp hd
      exact Finset.mem_filter.mpr
        ⟨mem_bitmapOverlapTailEvent_iff.mpr ⟨hdK, hdx ▸ htx⟩, hdx⟩
  · rw [if_neg htx, Finset.card_eq_zero]
    ext d
    constructor
    · intro hd
      obtain ⟨hdtail, hdx⟩ := Finset.mem_filter.mp hd
      obtain ⟨_hdK, hdt⟩ := mem_bitmapOverlapTailEvent_iff.mp hdtail
      exact False.elim (htx (hdx ▸ hdt))
    · intro hd
      simp at hd

/--
The closed-form hypergeometric upper tail is the exact finite mass of the
constant-weight threshold event.
-/
theorem bitmapOverlapTailMass_eq_bitmapHypergeomTail_of_query_card {D K t : ℕ}
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    bitmapOverlapTailMass D K t q = bitmapHypergeomTail D K t := by
  rw [bitmapOverlapTailMass, bitmapHypergeomTail,
    card_bitmapOverlapTailEvent_eq_sum_overlapFiber_card_of_query_card hq]
  simp_rw [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  simp_rw [bitmapHypergeomMass_eq_overlapFiber_card_ratio hq]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro x hx
  by_cases htx : t ≤ x <;> simp [htx]

/-- Uniform law over all `K`-active bitmaps in dimension `D`. -/
noncomputable def bitmapUniformPMF (D K : ℕ) (hK : K ≤ D) :
    PMF (Finset (BitmapCoord D)) :=
  PMF.uniformOfFinset (constantWeightBitmapSpace D K) (constantWeightBitmapSpace_nonempty hK)

@[simp]
theorem bitmapUniformPMF_apply {D K : ℕ} (hK : K ≤ D) (d : Finset (BitmapCoord D)) :
    bitmapUniformPMF D K hK d =
      if d.card = K then ((D.choose K : ℝ≥0∞)⁻¹) else 0 := by
  rw [bitmapUniformPMF, PMF.uniformOfFinset_apply]
  simp

private theorem ennreal_natCast_div_choose_eq_coe_nnreal_div {D K a : ℕ} (hK : K ≤ D) :
    (a : ℝ≥0∞) / (D.choose K : ℝ≥0∞) =
      (((a : ℝ≥0) / (D.choose K : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
  have hden : (D.choose K : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.choose_ne_zero hK)
  rw [ENNReal.coe_div hden]
  simp

private theorem bitmapUniformPMF_event_prob_eq_card_ratio {D K : ℕ} (hK : K ≤ D)
    {event : Finset (Finset (BitmapCoord D))} (hevent : event ⊆ constantWeightBitmapSpace D K) :
    (bitmapUniformPMF D K hK).toOuterMeasure (event : Set (Finset (BitmapCoord D))) =
      (event.card : ℝ≥0∞) / (D.choose K : ℝ≥0∞) := by
  rw [bitmapUniformPMF, PMF.toOuterMeasure_uniformOfFinset_apply]
  trans ((event.card : ℕ) : ℝ≥0∞) / ((constantWeightBitmapSpace D K).card : ℝ≥0∞)
  · congr 1
    apply congrArg (fun s : Finset (Finset (BitmapCoord D)) => ((s.card : ℕ) : ℝ≥0∞))
    ext d
    simpa [Finset.mem_filter] using
      (show (d ∈ constantWeightBitmapSpace D K ∧ d ∈ event) ↔ d ∈ event from
        ⟨And.right, fun hd => ⟨hevent hd, hd⟩⟩)
  · rw [card_constantWeightBitmapSpace]

/--
Under the uniform law over `K`-active bitmaps, the probability of exact
overlap `x` is the closed-form hypergeometric mass.
-/
theorem bitmapUniformPMF_overlapFiber_prob {D K x : ℕ} (hK : K ≤ D)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    (bitmapUniformPMF D K hK).toOuterMeasure
        (bitmapOverlapFiber D K x q : Set (Finset (BitmapCoord D))) =
      (bitmapHypergeomMass D K x : ℝ≥0∞) := by
  have hsubset : bitmapOverlapFiber D K x q ⊆ constantWeightBitmapSpace D K := by
    intro d hd
    exact mem_constantWeightBitmapSpace_iff.mpr (mem_bitmapOverlapFiber_iff.mp hd).1
  rw [bitmapUniformPMF_event_prob_eq_card_ratio hK
      (event := bitmapOverlapFiber D K x q) hsubset,
    card_bitmapOverlapFiber_of_query_card hq, bitmapHypergeomMass]
  exact ennreal_natCast_div_choose_eq_coe_nnreal_div hK

/--
Under the uniform law over `K`-active bitmaps, the probability of
clearing overlap threshold `t` is the closed-form hypergeometric upper tail.
-/
theorem bitmapUniformPMF_overlapTail_prob {D K t : ℕ} (hK : K ≤ D)
    {q : Finset (BitmapCoord D)} (hq : q.card = K) :
    (bitmapUniformPMF D K hK).toOuterMeasure
        (bitmapOverlapTailEvent D K t q : Set (Finset (BitmapCoord D))) =
      (bitmapHypergeomTail D K t : ℝ≥0∞) := by
  have hsubset : bitmapOverlapTailEvent D K t q ⊆ constantWeightBitmapSpace D K := by
    intro d hd
    exact mem_constantWeightBitmapSpace_iff.mpr (mem_bitmapOverlapTailEvent_iff.mp hd).1
  rw [bitmapUniformPMF_event_prob_eq_card_ratio hK
      (event := bitmapOverlapTailEvent D K t q) hsubset,
    ← bitmapOverlapTailMass_eq_bitmapHypergeomTail_of_query_card hq,
    bitmapOverlapTailMass]
  exact ennreal_natCast_div_choose_eq_coe_nnreal_div hK

end OrdvecFormalization
