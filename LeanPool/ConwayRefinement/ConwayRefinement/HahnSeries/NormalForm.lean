/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SupportSupremum
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.WeakNormalForm

/-!
# Principal series and normal forms of real Hahn series

This module formalizes the principal-series clause of LM24, Definition 3.3.1, and the normal forms
of Definition 3.3.6 and Proposition 3.3.7. A principal series is a weakly principal series in the
nonpositive real Hahn ring whose support supremum is zero.

A normal-form term stores a principal coefficient `b` and a real exponent `x`; its represented
series is the exponent translate `b t^x`. A normal form has nondecreasing exponents, nonincreasing
coefficient support order types, and strictly separated translated supports. The definition
stores pairwise support separation and proves its equivalence to the adjacent chain printed in
LM24. The zero series has the empty normal form.

Repeated exponents are deliberately allowed. In particular, the uniqueness proof never infers a
strict inequality from the exponent ordering. It recovers a term's exponent as the real supremum
of the represented support and then recovers its coefficient by inverse translation. This is
compatible with LM24, Remark 3.3.10 and does not infer strict increase from a nondecreasing
sequence of exponents.

The existence theorem starts with the already-proved weak normal form. Each weak block is still
supported in the nonpositive cone, so translating it by the negative of its support supremum gives
a principal coefficient. The proof is generalized from field coefficients to ring coefficients;
no multiplicative property of the coefficients is used.

The construction reuses `List.pmap`, `List.Pairwise.pmap`, and the weak-normal-form API rather than
introducing a second decomposition algorithm.
-/

universe v

public noncomputable section

namespace HahnSeries

variable {R : Type v} [Ring R]

namespace Nonpositive

/-- An LM24 principal series is weakly principal and has support supremum zero. -/
def IsPrincipal (x : Nonpositive ℝ R) : Prop :=
  IsWeaklyPrincipal (x : R⟦ℝ⟧) ∧ supportSup x = 0

/-- Characterization of an LM24 principal series. -/
theorem isPrincipal_iff {x : Nonpositive ℝ R} :
    IsPrincipal x ↔ IsWeaklyPrincipal (x : R⟦ℝ⟧) ∧ supportSup x = 0 :=
  Iff.rfl

theorem IsPrincipal.isWeaklyPrincipal {x : Nonpositive ℝ R} (hx : IsPrincipal x) :
    IsWeaklyPrincipal (x : R⟦ℝ⟧) :=
  (isPrincipal_iff.mp hx).1

theorem IsPrincipal.supportSup_eq_zero {x : Nonpositive ℝ R} (hx : IsPrincipal x) :
    supportSup x = 0 :=
  (isPrincipal_iff.mp hx).2

/-- A principal series is nonzero. -/
theorem IsPrincipal.ne_zero {x : Nonpositive ℝ R} (hx : IsPrincipal x) : x ≠ 0 := by
  have hx' := hx.isWeaklyPrincipal.ne_zero
  simpa using hx'

/-- Normalizing a weakly principal nonpositive series gives a principal series. -/
theorem isPrincipal_normalize {x : Nonpositive ℝ R}
    (hx : IsWeaklyPrincipal (x : R⟦ℝ⟧)) : IsPrincipal (normalize x) := by
  rw [isPrincipal_iff]
  constructor
  · rw [isWeaklyPrincipal_iff, supportOrderType_normalize]
    exact isWeaklyPrincipal_iff.mp hx
  · apply supportSup_normalize
    simpa using hx.ne_zero

/-- A nonzero constant Hahn series is principal. -/
theorem isPrincipal_C {r : R} (hr : r ≠ 0) :
    IsPrincipal ((C : R →+* Nonpositive ℝ R) r) := by
  have hsupport :
      (((C : R →+* Nonpositive ℝ R) r : Nonpositive ℝ R) :
          R⟦ℝ⟧).support = {0} := by
    rw [coe_C, HahnSeries.C_apply, HahnSeries.support_single_of_ne hr]
  have hne : (C : R →+* Nonpositive ℝ R) r ≠ 0 := by
    intro hzero
    have hcoeff := congrArg
      (fun x : Nonpositive ℝ R ↦ (x : R⟦ℝ⟧).coeff 0) hzero
    apply hr
    simpa [coe_C] using hcoeff
  rw [isPrincipal_iff]
  constructor
  · rw [HahnSeries.isWeaklyPrincipal_iff]
    rw [coe_C, HahnSeries.C_apply, HahnSeries.supportOrderType_single hr]
    simpa using Ordinal.isAdditivelyPrincipal_omega0_opow 0
  · apply supportSup_eq_coe_iff.mpr
    refine ⟨hne, ?_⟩
    rw [hsupport]
    exact isLUB_singleton

/-- The multiplicative identity of a nontrivial nonpositive real Hahn-series ring is principal. -/
theorem isPrincipal_one [Nontrivial R] :
    IsPrincipal (1 : Nonpositive ℝ R) := by
  rw [← map_one (C : R →+* Nonpositive ℝ R)]
  exact isPrincipal_C one_ne_zero

end Nonpositive

namespace NormalForm

/-- A coefficient-exponent pair occurring in a real Hahn-series normal form. Principality of the
coefficient is a clause of `HahnSeries.IsNormalForm`, not data stored in this structure. -/
@[ext]
structure Term (R : Type v) [Ring R] where
  coefficient : Nonpositive ℝ R
  exponent : ℝ

namespace Term

/-- The Hahn series represented by a normal-form term. -/
def series (t : Term R) : R⟦ℝ⟧ :=
  translate t.exponent t.coefficient

/-- A normal-form term represents the translate of its coefficient by its exponent. -/
theorem series_eq_translate (t : Term R) :
    t.series = translate t.exponent t.coefficient :=
  (rfl)

@[simp]
theorem coeff_series (t : Term R) (g : ℝ) :
    t.series.coeff g = (t.coefficient : R⟦ℝ⟧).coeff (g - t.exponent) := by
  rw [series_eq_translate, coeff_translate]

/-- Normalize a nonpositive Hahn series and record its original real support supremum. -/
def ofNonpositive (x : Nonpositive ℝ R) : Term R where
  coefficient := x.normalize
  exponent := sSup (x : R⟦ℝ⟧).support

@[simp]
theorem coefficient_ofNonpositive (x : Nonpositive ℝ R) :
    (ofNonpositive x).coefficient = x.normalize :=
  (rfl)

@[simp]
theorem exponent_ofNonpositive (x : Nonpositive ℝ R) :
    (ofNonpositive x).exponent = sSup (x : R⟦ℝ⟧).support :=
  (rfl)

/-- Normalizing a nonpositive series and translating it back recovers the original series. -/
@[simp]
theorem series_ofNonpositive (x : Nonpositive ℝ R) :
    (ofNonpositive x).series = x :=
  Nonpositive.translate_csSup_normalize x

theorem coefficient_ofNonpositive_isPrincipal {x : Nonpositive ℝ R}
    (hx : IsWeaklyPrincipal (x : R⟦ℝ⟧)) :
    Nonpositive.IsPrincipal (ofNonpositive x).coefficient :=
  Nonpositive.isPrincipal_normalize hx

/-- A term with principal coefficient represents a nonzero series. -/
theorem series_ne_zero {t : Term R} (ht : Nonpositive.IsPrincipal t.coefficient) :
    t.series ≠ 0 := by
  intro hzero
  apply ht.ne_zero
  apply Subtype.ext
  exact (translate t.exponent).injective (hzero.trans (map_zero _).symm)

/-- The support of a normal-form term is bounded above by its exponent. -/
theorem bddAbove_support (t : Term R) : BddAbove t.series.support := by
  refine ⟨t.exponent, ?_⟩
  rw [series, support_translate]
  rintro _ ⟨g, hg, rfl⟩
  simpa using add_le_add_left (Nonpositive.support_subset t.coefficient hg) t.exponent

/-- For a principal coefficient, the exponent is the supremum of the represented support. -/
theorem csSup_support_series (t : Term R) (ht : Nonpositive.IsPrincipal t.coefficient) :
    sSup t.series.support = t.exponent := by
  rw [series, csSup_support_translate]
  · have hsup := ht.supportSup_eq_zero
    rw [Nonpositive.supportSup_of_ne ht.ne_zero] at hsup
    norm_cast at hsup
    simp [hsup]
  · simpa using ht.ne_zero
  · exact Nonpositive.bddAbove_support t.coefficient

/-- Principal normal-form terms representing the same Hahn series are equal. -/
theorem eq_of_series_eq {s t : Term R}
    (hs : Nonpositive.IsPrincipal s.coefficient)
    (ht : Nonpositive.IsPrincipal t.coefficient) (hseries : s.series = t.series) :
    s = t := by
  have hexponent : s.exponent = t.exponent := by
    calc
      s.exponent = sSup s.series.support := (csSup_support_series s hs).symm
      _ = sSup t.series.support := congrArg (fun x : R⟦ℝ⟧ ↦ sSup x.support) hseries
      _ = t.exponent := csSup_support_series t ht
  have hcoefficient : (s.coefficient : R⟦ℝ⟧) = t.coefficient := by
    apply (translate s.exponent).injective
    simpa only [series, hexponent] using hseries
  apply Term.ext
  · exact Subtype.ext hcoefficient
  · exact hexponent

end Term

end NormalForm

/-- Supremum is monotone across two nonzero, strictly separated real supports when the upper
support is bounded above. -/
theorem csSup_support_le_of_supportBelow {x y : R⟦ℝ⟧}
    (hx : x ≠ 0) (hy : y ≠ 0) (hybdd : BddAbove y.support)
    (hxy : SupportBelow x y) :
    sSup x.support ≤ sSup y.support := by
  obtain ⟨j, hj⟩ := support_nonempty_iff.mpr hy
  apply (csSup_le (support_nonempty_iff.mpr hx) fun i hi ↦ (hxy.lt hi hj).le).trans
  exact le_csSup hybdd hj

/-- The five clauses defining an LM24 real Hahn-series normal form. -/
def IsNormalForm (x : R⟦ℝ⟧) (terms : List (NormalForm.Term R)) : Prop :=
  (terms.map NormalForm.Term.series).sum = x ∧
    (terms.map NormalForm.Term.exponent).SortedLE ∧
    (∀ t ∈ terms, Nonpositive.IsPrincipal t.coefficient) ∧
    (terms.map (fun t ↦ (t.coefficient : R⟦ℝ⟧).supportOrderType)).SortedGE ∧
    (terms.map NormalForm.Term.series).Pairwise SupportBelow

/-- Characterization by represented sum, exponents, principal coefficients, order types, and
translated supports. -/
theorem isNormalForm_iff {x : R⟦ℝ⟧} {terms : List (NormalForm.Term R)} :
    IsNormalForm x terms ↔
      (terms.map NormalForm.Term.series).sum = x ∧
        (terms.map NormalForm.Term.exponent).SortedLE ∧
        (∀ t ∈ terms, Nonpositive.IsPrincipal t.coefficient) ∧
        (terms.map (fun t ↦ (t.coefficient : R⟦ℝ⟧).supportOrderType)).SortedGE ∧
        (terms.map NormalForm.Term.series).Pairwise SupportBelow :=
  Iff.rfl

/-- Source-form characterization using the adjacent support chain printed in LM24, Definition
3.3.6. Principality makes every represented term nonzero, so the chain is pairwise separated. -/
theorem isNormalForm_iff_isChain {x : R⟦ℝ⟧} {terms : List (NormalForm.Term R)} :
    IsNormalForm x terms ↔
      (terms.map NormalForm.Term.series).sum = x ∧
        (terms.map NormalForm.Term.exponent).SortedLE ∧
        (∀ t ∈ terms, Nonpositive.IsPrincipal t.coefficient) ∧
        (terms.map (fun t ↦ (t.coefficient : R⟦ℝ⟧).supportOrderType)).SortedGE ∧
        (terms.map NormalForm.Term.series).IsChain SupportBelow := by
  rw [isNormalForm_iff]
  constructor
  · rintro ⟨hsum, hexponents, hprincipal, htypes, hpair⟩
    exact ⟨hsum, hexponents, hprincipal, htypes, hpair.isChain⟩
  · rintro ⟨hsum, hexponents, hprincipal, htypes, hchain⟩
    refine ⟨hsum, hexponents, hprincipal, htypes, ?_⟩
    apply pairwise_supportBelow_of_isChain
    · intro b hb
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
      exact NormalForm.Term.series_ne_zero (hprincipal t ht)
    · exact hchain

/-- Forgetting coefficient normalization turns an LM24 normal form into its weak normal form. -/
theorem IsNormalForm.isWeakNormalForm {x : R⟦ℝ⟧} {terms : List (NormalForm.Term R)}
    (h : IsNormalForm x terms) :
    IsWeakNormalForm x (terms.map NormalForm.Term.series) := by
  obtain ⟨hsum, _, hprincipal, htypes, hpair⟩ := isNormalForm_iff.mp h
  rw [isWeakNormalForm_iff]
  refine ⟨hsum, ?_, ?_, hpair⟩
  · intro b hb
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
    rw [isWeaklyPrincipal_iff, NormalForm.Term.series, supportOrderType_translate]
    exact isWeaklyPrincipal_iff.mp (hprincipal t ht).isWeaklyPrincipal
  · convert htypes using 1
    rw [List.map_map]
    apply List.map_congr_left
    intro t ht
    simp [NormalForm.Term.series]

private theorem bddAbove_support_normalTerm_sum (terms : List (NormalForm.Term R)) :
    BddAbove (terms.map NormalForm.Term.series).sum.support := by
  induction terms with
  | nil => simp
  | cons t terms ih =>
      simp only [List.map_cons, List.sum_cons]
      obtain ⟨a, ha⟩ := NormalForm.Term.bddAbove_support t
      obtain ⟨b, hb⟩ := ih
      refine ⟨max a b, ?_⟩
      intro g hg
      rcases support_add_subset t.series (terms.map NormalForm.Term.series).sum hg with hg | hg
      · exact (ha hg).trans (le_max_left _ _)
      · exact (hb hg).trans (le_max_right _ _)

/-- Every series admitting a finite LM24 normal form has support bounded above. -/
theorem IsNormalForm.bddAbove_support {x : R⟦ℝ⟧} {terms : List (NormalForm.Term R)}
    (h : IsNormalForm x terms) : BddAbove x.support := by
  have hbdd := bddAbove_support_normalTerm_sum terms
  rw [(isNormalForm_iff.mp h).1] at hbdd
  exact hbdd

private theorem normalTerms_eq_of_series_eq {terms other : List (NormalForm.Term R)}
    (hterms : ∀ t ∈ terms, Nonpositive.IsPrincipal t.coefficient)
    (hother : ∀ t ∈ other, Nonpositive.IsPrincipal t.coefficient)
    (hseries : terms.map NormalForm.Term.series = other.map NormalForm.Term.series) :
    terms = other := by
  induction terms generalizing other with
  | nil => simpa using hseries
  | cons t terms ih =>
      cases other with
      | nil => simp at hseries
      | cons s other =>
          simp only [List.map_cons, List.cons.injEq] at hseries
          have hts : t = s := NormalForm.Term.eq_of_series_eq
            (hterms t (by simp)) (hother s (by simp)) hseries.1
          subst s
          rw [List.cons.injEq]
          exact ⟨rfl, ih (fun t ht ↦ hterms t (by simp [ht]))
            (fun s hs ↦ hother s (by simp [hs])) hseries.2⟩

/-- Two LM24 normal forms of the same real Hahn series are equal. -/
theorem IsNormalForm.unique {x : R⟦ℝ⟧} {terms other : List (NormalForm.Term R)}
    (hterms : IsNormalForm x terms) (hother : IsNormalForm x other) :
    terms = other := by
  obtain ⟨_, _, htermsPrincipal, _, _⟩ := isNormalForm_iff.mp hterms
  obtain ⟨_, _, hotherPrincipal, _, _⟩ := isNormalForm_iff.mp hother
  apply normalTerms_eq_of_series_eq htermsPrincipal hotherPrincipal
  exact hterms.isWeakNormalForm.unique hother.isWeakNormalForm

/-- Every nonpositive real Hahn series has an LM24 normal form. This is the existence part of
LM24, Proposition 3.3.7. -/
theorem exists_isNormalForm (x : Nonpositive ℝ R) :
    ∃ terms : List (NormalForm.Term R), IsNormalForm x terms := by
  obtain ⟨blocks, hblocks⟩ := exists_isWeakNormalForm (x : R⟦ℝ⟧)
  obtain ⟨hsum, hprincipal, htypes, hpair⟩ := isWeakNormalForm_iff.mp hblocks
  have hnonpositive : ∀ b ∈ blocks, b.support ⊆ Set.Iic (0 : ℝ) := by
    intro b hb
    have hbsub := support_subset_list_sum_of_mem hpair hb
    rw [hsum] at hbsub
    exact hbsub.trans (Nonpositive.support_subset x)
  have hblockData : ∀ b ∈ blocks, b ∈ blocks ∧ b.support ⊆ Set.Iic (0 : ℝ) :=
    fun b hb ↦ ⟨hb, hnonpositive b hb⟩
  let terms : List (NormalForm.Term R) := blocks.pmap
    (fun b hb ↦ NormalForm.Term.ofNonpositive
      ⟨b, (mem_nonpositiveSubring (x := b)).mpr hb.2⟩) hblockData
  have hseries : terms.map NormalForm.Term.series = blocks := by
    simp [terms, List.map_pmap]
  refine ⟨terms, isNormalForm_iff.mpr ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hseries]
    exact hsum
  · rw [List.sortedLE_iff_pairwise]
    simp only [terms, List.map_pmap]
    apply hpair.pmap hblockData
    intro b hb c hc hbc
    apply csSup_support_le_of_supportBelow
    · exact (hprincipal b hb.1).ne_zero
    · exact (hprincipal c hc.1).ne_zero
    · exact ⟨0, hc.2⟩
    · exact hbc
  · intro t ht
    simp only [terms, List.mem_pmap] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    exact NormalForm.Term.coefficient_ofNonpositive_isPrincipal (hprincipal b hb)
  · convert htypes using 1
    simp only [terms, List.map_pmap, NormalForm.Term.coefficient_ofNonpositive,
      Nonpositive.supportOrderType_normalize]
    apply List.pmap_eq_map
  · rwa [hseries]

/-- Every nonpositive real Hahn series has exactly one LM24 normal form. This is LM24,
Proposition 3.3.7. -/
theorem existsUnique_isNormalForm (x : Nonpositive ℝ R) :
    ∃! terms : List (NormalForm.Term R), IsNormalForm x terms := by
  obtain ⟨terms, hterms⟩ := exists_isNormalForm x
  exact ⟨terms, hterms, fun other hother ↦ (hterms.unique hother).symm⟩

private theorem degree_list_sum_le {l : List R⟦ℝ⟧} {d : WithBot NatOrdinal}
    (h : ∀ x ∈ l, x.degree ≤ d) : l.sum.degree ≤ d := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.sum_cons]
      exact (degree_add_le x xs.sum).trans
        (max_le (h x (by simp)) (ih fun y hy ↦ h y (by simp [hy])))

/-- A nonzero nonpositive real Hahn series has a principal leading term and a remainder supported
weakly above its exponent. The leading coefficient has the degree of the original series, and the
remainder has no larger degree. When that degree is zero, the remainder support is strictly above
the leading exponent.

This is the head decomposition extracted from the normal form in LM24, Proposition 3.3.7. The
last clause uses only the source-valid strictness at degree zero and does not assume that all
normal-form exponents are distinct. -/
theorem exists_principal_head_decomposition
    {b : Nonpositive ℝ R} (hbne : b ≠ 0) :
    ∃ b₁ : Nonpositive ℝ R, ∃ x : ℝ, ∃ b' : Nonpositive ℝ R,
      Nonpositive.IsPrincipal b₁ ∧
        (b : R⟦ℝ⟧) = translate x (b₁ : R⟦ℝ⟧) + (b' : R⟦ℝ⟧) ∧
        (b' : R⟦ℝ⟧).support ⊆ Set.Ici x ∧
        (b₁ : R⟦ℝ⟧).degree = (b : R⟦ℝ⟧).degree ∧
        (b' : R⟦ℝ⟧).degree ≤ (b : R⟦ℝ⟧).degree ∧
        ((b : R⟦ℝ⟧).degree = 0 →
          (b' : R⟦ℝ⟧).support ⊆ Set.Ioi x) := by
  obtain ⟨terms, hterms⟩ := exists_isNormalForm b
  obtain ⟨hsum, _, hprincipal, htypes, hpair⟩ := isNormalForm_iff.mp hterms
  cases terms with
  | nil =>
      simp only [List.map_nil, List.sum_nil] at hsum
      exact (hbne (Subtype.ext hsum.symm)).elim
  | cons t terms =>
      simp only [List.map_cons, List.sum_cons] at hsum
      simp only [List.map_cons] at hpair htypes
      rw [List.pairwise_cons] at hpair
      have htPrincipal : Nonpositive.IsPrincipal t.coefficient :=
        hprincipal t (by simp)
      have htBelow :
          SupportBelow t.series (terms.map NormalForm.Term.series).sum :=
        supportBelow_list_sum hpair.1
      have hsupportSum :
          (t.series + (terms.map NormalForm.Term.series).sum).support =
            t.series.support ∪ (terms.map NormalForm.Term.series).sum.support :=
        support_add_eq_union_of_supportBelow _ _ htBelow
      have htailSubset :
          (terms.map NormalForm.Term.series).sum.support ⊆
            (b : R⟦ℝ⟧).support := by
        rw [← hsum, hsupportSum]
        exact Set.subset_union_right
      let b' : Nonpositive ℝ R :=
        ⟨(terms.map NormalForm.Term.series).sum,
          (mem_nonpositiveSubring
            (x := (terms.map NormalForm.Term.series).sum)).mpr
              (htailSubset.trans (Nonpositive.support_subset b))⟩
      have hb'Support : (b' : R⟦ℝ⟧).support ⊆ Set.Ici t.exponent := by
        intro j hj
        rw [← NormalForm.Term.csSup_support_series t htPrincipal]
        apply csSup_le
          (support_nonempty_iff.mpr (NormalForm.Term.series_ne_zero htPrincipal))
        intro i hi
        exact (htBelow.lt hi hj).le
      have htypesPair := List.sortedGE_iff_pairwise.mp htypes
      rw [List.pairwise_cons] at htypesPair
      have htailTermDegree :
          ∀ s ∈ terms,
            s.series.degree ≤ (t.coefficient : R⟦ℝ⟧).degree := by
        intro s hs
        rw [NormalForm.Term.series, degree_translate]
        rw [degree_eq_cantorDegree, degree_eq_cantorDegree]
        exact Ordinal.cantorDegree_mono (htypesPair.1
          (s.coefficient : R⟦ℝ⟧).supportOrderType
            (List.mem_map.mpr ⟨s, hs, rfl⟩))
      have htailDegree :
          (b' : R⟦ℝ⟧).degree ≤ (t.coefficient : R⟦ℝ⟧).degree := by
        exact degree_list_sum_le (by
          intro y hy
          obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hy
          exact htailTermDegree s hs)
      have hheadSupportSubset :
          t.series.support ⊆ (b : R⟦ℝ⟧).support := by
        rw [← hsum, hsupportSum]
        exact Set.subset_union_left
      have hheadDegree :
          (t.coefficient : R⟦ℝ⟧).degree = (b : R⟦ℝ⟧).degree := by
        apply le_antisymm
        · calc
            (t.coefficient : R⟦ℝ⟧).degree = t.series.degree := by
              rw [NormalForm.Term.series, degree_translate]
            _ ≤ (b : R⟦ℝ⟧).degree := degree_mono_support hheadSupportSubset
        · calc
            (b : R⟦ℝ⟧).degree =
                (t.series + (b' : R⟦ℝ⟧)).degree :=
              congrArg degree hsum.symm
            _ ≤ max t.series.degree (b' : R⟦ℝ⟧).degree :=
              degree_add_le _ _
            _ ≤ (t.coefficient : R⟦ℝ⟧).degree := max_le
              (by rw [NormalForm.Term.series, degree_translate])
              htailDegree
      have hb'Degree :
          (b' : R⟦ℝ⟧).degree ≤ (b : R⟦ℝ⟧).degree :=
        htailDegree.trans hheadDegree.le
      have hb'Strict :
          (b : R⟦ℝ⟧).degree = 0 →
            (b' : R⟦ℝ⟧).support ⊆ Set.Ioi t.exponent := by
        intro hbDegree j hj
        have htDegree : (t.coefficient : R⟦ℝ⟧).degree = 0 :=
          hheadDegree.trans hbDegree
        have htFinite := (degree_eq_zero.mp htDegree).2
        have htNonempty : (t.coefficient : R⟦ℝ⟧).support.Nonempty :=
          support_nonempty_iff.mpr (by simpa using htPrincipal.ne_zero)
        have htSup : sSup (t.coefficient : R⟦ℝ⟧).support = 0 := by
          have hsup := htPrincipal.supportSup_eq_zero
          rw [Nonpositive.supportSup_of_ne htPrincipal.ne_zero] at hsup
          exact WithBot.coe_eq_coe.mp hsup
        have hzero : 0 ∈ (t.coefficient : R⟦ℝ⟧).support := by
          rw [← htSup]
          exact htNonempty.csSup_mem htFinite
        have hexponent : t.exponent ∈ t.series.support := by
          rw [NormalForm.Term.series, support_translate]
          exact ⟨0, hzero, by simp⟩
        exact htBelow.lt hexponent hj
      exact ⟨t.coefficient, t.exponent, b', htPrincipal,
        hsum.symm, hb'Support, hheadDegree, hb'Degree, hb'Strict⟩

end HahnSeries
