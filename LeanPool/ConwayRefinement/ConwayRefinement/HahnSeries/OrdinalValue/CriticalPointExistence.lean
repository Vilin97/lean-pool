/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.CriticalPoint

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NormalForm
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.PrincipalAddition
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.PWOSumset
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.GermDegree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.MainLemma
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponentDegree
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.ResidualPointWellOrdered
import Mathlib.Tactic.Linarith

/-!
# Existence of Berarducci critical points

Berarducci, Lemma 10.1 proves that the ordinal values of all translated truncations of a nonzero
nonpositive real Hahn series have a maximum. Definition 10.2 chooses the least nonpositive cutoff
where that maximum occurs.

The proof realizes the maximum through the LM24 normal form. Its principal head has the same
degree as the full series. Truncating at the head exponent recovers that principal coefficient up
to a constant, so its ordinal-value degree reaches the upper bound for every translated truncation.
The maximizers lie in the closed support, which is partially well ordered, and therefore have a
least element.

## References

* A. Berarducci, *Factorization in generalized power series*, Trans. Amer. Math. Soc. 352
  (2000), 553–577, cited as [Ber00].
-/

universe v

open scoped HahnSeries NatOrdinal

public noncomputable section

namespace Berarducci

open HahnSeries

variable {K : Type v} [Field K]

private theorem translatedTruncation_translate_self
    (p : Series K) (x : ℝ) :
    translatedTruncation (HahnSeries.translate x (p : K⟦ℝ⟧)) x = p := by
  apply Subtype.ext
  rw [coe_translatedTruncation, HahnSeries.truncLE_translate]
  simp only [sub_self]
  rw [HahnSeries.truncLE_eq_self_of_support_subset_Iic
    (HahnSeries.Nonpositive.support_subset p), HahnSeries.translate_add_apply]
  simp

private theorem translatedTruncation_eq_C_of_support_subset_Ici
    (b : Series K) (x : ℝ)
    (hb : (b : K⟦ℝ⟧).support ⊆ Set.Ici x) :
    translatedTruncation (b : K⟦ℝ⟧) x =
      HahnSeries.Nonpositive.C ((b : K⟦ℝ⟧).coeff x) := by
  apply Subtype.ext
  ext δ
  rw [coeff_translatedTruncation, HahnSeries.Nonpositive.coe_C]
  rcases lt_trichotomy δ 0 with hδ | rfl | hδ
  · rw [ite_eq_left hδ.le, HahnSeries.C_apply,
      HahnSeries.coeff_single_of_ne hδ.ne]
    apply not_ne_iff.mp
    rw [← HahnSeries.mem_support]
    intro hmem
    exact (not_le_of_gt (by linarith : x + δ < x)) (hb hmem)
  · simp
  · rw [ite_eq_right (not_le_of_gt hδ), HahnSeries.C_apply,
      HahnSeries.coeff_single_of_ne hδ.ne']

private theorem principalHeadExponent_nonpositive
    {b p r : Series K} {x : ℝ}
    (hb : (b : K⟦ℝ⟧) =
      HahnSeries.translate x (p : K⟦ℝ⟧) + (r : K⟦ℝ⟧))
    (hp : HahnSeries.Nonpositive.IsPrincipal p) : x ≤ 0 := by
  by_contra hx
  have hxpos : 0 < x := lt_of_not_ge hx
  have hheadNe : HahnSeries.translate x (p : K⟦ℝ⟧) ≠ 0 :=
    fun hzero ↦ hp.ne_zero (Subtype.ext
      ((HahnSeries.translate x).injective (by simpa using hzero)))
  have hpSup : sSup (p : K⟦ℝ⟧).support = 0 := by
    have hsup := hp.supportSup_eq_zero
    rw [HahnSeries.Nonpositive.supportSup_of_ne hp.ne_zero] at hsup
    exact WithBot.coe_eq_coe.mp hsup
  have hheadBdd : BddAbove
      (HahnSeries.translate x (p : K⟦ℝ⟧)).support := by
    refine ⟨x, ?_⟩
    rw [HahnSeries.support_translate]
    rintro _ ⟨y, hy, rfl⟩
    have hy0 := HahnSeries.Nonpositive.support_subset p hy
    change y ≤ 0 at hy0
    change x + y ≤ x
    linarith
  have hheadSup : sSup
      (HahnSeries.translate x (p : K⟦ℝ⟧)).support = x := by
    rw [HahnSeries.csSup_support_translate (by simpa using hp.ne_zero)
      (HahnSeries.Nonpositive.bddAbove_support p), hpSup]
    simp
  have hheadLUB : IsLUB
      (HahnSeries.translate x (p : K⟦ℝ⟧)).support x := by
    simpa only [hheadSup] using
      (isLUB_csSup (HahnSeries.support_nonempty_iff.mpr hheadNe) hheadBdd)
  obtain ⟨y, hy, hypos, -⟩ := hheadLUB.exists_between hxpos
  have hrCoeff : (r : K⟦ℝ⟧).coeff y = 0 := by
    apply not_ne_iff.mp
    rw [← HahnSeries.mem_support]
    exact fun hmem ↦ (not_le_of_gt hypos)
      (HahnSeries.Nonpositive.support_subset r hmem)
  have hbCoeff := congrArg (fun q : K⟦ℝ⟧ ↦ q.coeff y) hb
  simp only [HahnSeries.coeff_add, hrCoeff, add_zero] at hbCoeff
  have hyb : y ∈ (b : K⟦ℝ⟧).support := by
    rw [HahnSeries.mem_support, hbCoeff]
    exact (HahnSeries.mem_support _ _).mp hy
  exact (not_le_of_gt hypos) (HahnSeries.Nonpositive.support_subset b hyb)

private theorem ordinalValue_add_eq_left_of_lt [CharZero K]
    {b c : Series K} (h : ordinalValue c < ordinalValue b) :
    ordinalValue (b + c) = ordinalValue b := by
  apply le_antisymm
  · simpa [max_eq_left h.le] using ordinalValue_add_le_max b c
  · have hle := ordinalValue_add_le_max (b + c) (-c)
    rw [add_neg_cancel_right, ordinalValue_neg] at hle
    by_contra hnot
    exact (not_lt_of_ge hle) (max_lt (lt_of_not_ge hnot) h)

private theorem ordinalValue_le_of_ordinalValueDegree_le
    {b c : Series K} (h : ordinalValueDegree b ≤ ordinalValueDegree c) :
    ordinalValue b ≤ ordinalValue c := by
  by_cases hb : ordinalValue b = 0
  · simp [hb]
  have hc : ordinalValue c ≠ 0 := by
    intro hc
    have hcDegree : ordinalValueDegree c = ⊥ :=
      ordinalValueDegree_eq_bot_iff.mpr (ordinalValue_eq_zero_iff.mp hc)
    have hbDegree : ordinalValueDegree b ≠ ⊥ := fun hbot ↦
      hb (ordinalValue_eq_zero_iff.mpr (ordinalValueDegree_eq_bot_iff.mp hbot))
    exact hbDegree (bot_unique (h.trans_eq hcDegree))
  have hbDegreeNe : ordinalValueDegree b ≠ ⊥ := fun hbot ↦
    hb (ordinalValue_eq_zero_iff.mpr (ordinalValueDegree_eq_bot_iff.mp hbot))
  have hcDegreeNe : ordinalValueDegree c ≠ ⊥ := fun hbot ↦
    hc (ordinalValue_eq_zero_iff.mpr (ordinalValueDegree_eq_bot_iff.mp hbot))
  let a := (ordinalValueDegree b).unbot hbDegreeNe
  let d := (ordinalValueDegree c).unbot hcDegreeNe
  have haDegree : ordinalValueDegree b = (a : WithBot NatOrdinal) :=
    (WithBot.coe_unbot _ hbDegreeNe).symm
  have hdDegree : ordinalValueDegree c = (d : WithBot NatOrdinal) :=
    (WithBot.coe_unbot _ hcDegreeNe).symm
  have haValue : ordinalValue b = ω^ a :=
    (ordinalValueDegree_eq_coe_iff b a).mp haDegree
  have hdValue : ordinalValue c = ω^ d :=
    (ordinalValueDegree_eq_coe_iff c d).mp hdDegree
  rw [haValue, hdValue]
  apply NatOrdinal.wpow_le_wpow.mpr
  rw [← WithBot.coe_le_coe]
  exact haDegree.symm.trans_le (h.trans_eq hdDegree)

private theorem exists_maximal_translatedTruncation [CharZero K]
    {b : Series K} (hb : b ≠ 0) :
    ∃ x : ℝ, x ≤ 0 ∧
      ∀ y : ℝ, y ≤ 0 →
        ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) ≤
          ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) := by
  obtain ⟨p, x, r, hp, hbpr, hrSupport, hpDegree, -, hrStrict⟩ :=
    HahnSeries.exists_principal_head_decomposition hb
  have hx : x ≤ 0 := principalHeadExponent_nonpositive hbpr hp
  let k := (r : K⟦ℝ⟧).coeff x
  have hgerm : translatedTruncation (b : K⟦ℝ⟧) x =
      p + HahnSeries.Nonpositive.C k := by
    rw [← translatedTruncation_translate_self p x,
      ← translatedTruncation_eq_C_of_support_subset_Ici r x hrSupport,
      ← translatedTruncation_add, hbpr]
  have hpDegreeNe : (p : K⟦ℝ⟧).degree ≠ ⊥ := by
    intro hbot
    exact hp.ne_zero (Subtype.ext (HahnSeries.degree_eq_bot.mp hbot))
  let a := (p : K⟦ℝ⟧).degree.unbot hpDegreeNe
  have hpDegree' : (p : K⟦ℝ⟧).degree =
      (a : WithBot NatOrdinal) := (WithBot.coe_unbot _ hpDegreeNe).symm
  have hpValue : ordinalValue p = ω^ a :=
    ordinalValue_eq_wpow_of_isPrincipal hp hpDegree'
  have hgermValue : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) = ω^ a := by
    rcases eq_or_ne a 0 with ha | ha
    · have hpDegreeZero : (p : K⟦ℝ⟧).degree = 0 := by simpa [ha] using hpDegree'
      have hrStrict' := hrStrict (hpDegree.symm.trans hpDegreeZero)
      have hk : k = 0 := by
        apply not_ne_iff.mp
        rw [← HahnSeries.mem_support]
        exact fun hmem ↦ (lt_irrefl x) (hrStrict' hmem)
      simpa [ha, hgerm, hk] using hpValue
    · have haPos : 0 < a := bot_lt_iff_ne_bot.mpr ha
      have hconstant : ordinalValue (HahnSeries.Nonpositive.C k : Series K) ≤ 1 := by
        by_cases hk : k = 0
        · simp [hk]
        · rw [ordinalValue_C_of_ne hk]
      rw [hgerm, ordinalValue_add_eq_left_of_lt]
      · exact hpValue
      · rw [hpValue]
        exact hconstant.trans_lt (by
          simpa using NatOrdinal.wpow_lt_wpow.mpr haPos)
  refine ⟨x, hx, fun y _ ↦ ordinalValue_le_of_ordinalValueDegree_le ?_⟩
  calc
    ordinalValueDegree (translatedTruncation (b : K⟦ℝ⟧) y) ≤
        (b : K⟦ℝ⟧).degree :=
      ordinalValueDegree_translatedTruncation_le_degree (b : K⟦ℝ⟧) y
    _ = (p : K⟦ℝ⟧).degree := hpDegree.symm
    _ = ordinalValueDegree (translatedTruncation (b : K⟦ℝ⟧) x) :=
      hpDegree'.trans
        ((ordinalValueDegree_eq_coe_iff _ a).mpr hgermValue).symm

/-- Berarducci, Lemma 10.1 and Definition 10.2: every nonzero nonpositive real Hahn series has
a critical point. -/
theorem exists_isCriticalPoint [CharZero K] {b : Series K} (hb : b ≠ 0) :
    ∃ x : ℝ, IsCriticalPoint b x := by
  obtain ⟨x, hx0, hxMax⟩ := exists_maximal_translatedTruncation hb
  let M : Set ℝ := {y | y ≤ 0 ∧
    ordinalValue (translatedTruncation (b : K⟦ℝ⟧) y) =
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x)}
  have hxM : x ∈ M := ⟨hx0, rfl⟩
  have hxValue : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) x) ≠ 0 := by
    have hsupport : (b : K⟦ℝ⟧).support.Nonempty :=
      HahnSeries.support_nonempty_iff.mpr (by simpa using hb)
    obtain ⟨y, hy⟩ := hsupport
    exact ne_of_gt ((ordinalValue_translatedTruncation_pos_of_mem_support hy).trans_le
      (hxMax y (HahnSeries.Nonpositive.support_subset b hy)))
  have hMsub : M ⊆ closure (b : K⟦ℝ⟧).support := by
    intro y hy
    by_contra hclosure
    have hyJ := translatedTruncation_mem_negativeMonomialIdeal_of_not_mem_closure_support hclosure
    have hyZero := ordinalValue_of_mem_negativeMonomialIdeal hyJ
    exact hxValue (hy.2.symm.trans hyZero)
  let hMPWO : M.IsPWO :=
    (Set.isPWO_closure (b : K⟦ℝ⟧).isPWO_support).mono hMsub
  obtain ⟨z, hzMinimal⟩ := hMPWO.exists_minimal ⟨x, hxM⟩
  have hzM : z ∈ M := hzMinimal.1
  refine ⟨z, isCriticalPoint_iff.mpr ⟨hb, hzM.1, ?_, ?_⟩⟩
  · intro y hy
    exact (hxMax y hy).trans_eq hzM.2.symm
  · intro y hy hvalue
    have hyM : y ∈ M := ⟨hy, hvalue.trans hzM.2⟩
    exact le_of_not_gt fun hyz ↦
      (minimal_iff_forall_lt.mp hzMinimal).2 hyz hyM

end Berarducci
