/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Surreal.HahnSeries.NormalFormBasic
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Leading

/-!
# Recursion on the length of a surreal Hahn series

This module supplies successor decomposition and transfinite length recursion for the Conway
normal-form construction. It follows the corresponding axiom-free infrastructure from
CombinatorialGames PR #263, adapted to the pinned public API.
-/

universe u

public noncomputable section

attribute [grind =] Subtype.mk_le_mk Subtype.mk_lt_mk Order.lt_add_one_iff

open Order Set

namespace SurrealHahnSeries

open Ordinal

@[simp]
theorem truncIdx_eq_self {x : SurrealHahnSeries} {i : Ordinal} :
    x.truncIdx i = x ↔ x.length ≤ i where
  mp h := by
    contrapose! h
    exact truncIdx_ne h
  mpr := truncIdx_of_le

@[simp]
theorem truncIdx_length (x : SurrealHahnSeries) : x.truncIdx x.length = x := by
  simp

theorem self_mem_range_truncIdx (x : SurrealHahnSeries) : x ∈ range x.truncIdx :=
  ⟨_, x.truncIdx_length⟩

theorem self_mem_range_trunc (x : SurrealHahnSeries) : x ∈ range x.trunc := by
  refine ⟨!{∅ | x.support}, trunc_eq_self ?_⟩
  aesop

theorem range_truncIdx_eq_range_trunc (x : SurrealHahnSeries) :
    range x.truncIdx = range x.trunc := by
  ext y
  constructor
  · rintro ⟨i, rfl⟩
    obtain h | h := lt_or_ge i x.length
    · rw [truncIdx_of_lt h]
      exact mem_range_self _
    · rw [truncIdx_of_le h]
      exact self_mem_range_trunc x
  · rintro ⟨i, rfl⟩
    by_cases! hx : ∀ j ∈ x.support, i < j
    · rw [trunc_eq_self_iff.2 hx]
      use x.length
      simp
    · have H : {j : x.support | j.1 ≤ i}.Nonempty := by
        obtain ⟨j, hj, hj'⟩ := hx
        exact ⟨⟨j, hj⟩, hj'⟩
      obtain ⟨j, hj, hj'⟩ := wellFounded_gt.has_min _ H
      use x.exp.symm j
      rw [truncIdx_symm_exp]
      refine trunc_eq_trunc hj fun k hk hk' ↦ ?_
      by_contra hk''
      exact hj' ⟨k, hk''⟩ hk' hk

theorem truncIdx_mem_range_trunc (x : SurrealHahnSeries) (i : Ordinal) :
    x.truncIdx i ∈ range x.trunc := by
  simp [← range_truncIdx_eq_range_trunc]

theorem trunc_mem_range_truncIdx (x : SurrealHahnSeries) (i : Surreal) :
    x.trunc i ∈ range x.truncIdx := by
  simp [range_truncIdx_eq_range_trunc]
@[simp]
theorem leadingTerm_term (x : SurrealHahnSeries) (i : Ordinal) :
    (x.term i).leadingTerm = x.term i := by
  by_cases hi : i < x.length
  · rw [term_of_lt hi]
    simp
  · rw [term_of_le (le_of_not_gt hi)]
    simp

@[simp]
theorem leadingCoeff_term (x : SurrealHahnSeries) (i : Ordinal) :
    (x.term i).leadingCoeff = x.coeffIdx i := by
  by_cases hi : i < x.length
  · rw [term_of_lt hi, coeffIdx_of_lt hi]
    simp
  · rw [term_of_le (le_of_not_gt hi), coeffIdx_of_le (le_of_not_gt hi)]
    simp

theorem wlog_term {x : SurrealHahnSeries} {i : Ordinal} (hi : i ∈ Iio x.length) :
    (x.term i).wlog = x.exp ⟨i, hi⟩ := by
  have hc : x.coeffIdx i ≠ 0 := by
    rw [ne_eq, coeffIdx_eq_zero_iff]
    exact not_le_of_gt hi
  have hc' : (x.coeffIdx i : Surreal) ≠ 0 := by exact_mod_cast hc
  rw [term_of_lt hi, Surreal.wlog_mul hc' (by simp)]
  simp

theorem mk_term {x : SurrealHahnSeries} {i : Ordinal} (hi : i ∈ Iio x.length) :
    ArchimedeanClass.mk (x.term i) = .mk (ω^ (x.exp ⟨i, hi⟩)) := by
  have hc : x.coeffIdx i ≠ 0 := by
    rw [ne_eq, coeffIdx_eq_zero_iff]
    exact not_le_of_gt hi
  rw [term_of_lt hi, ArchimedeanClass.mk_mul, Surreal.mk_realCast hc]
  simp

namespace TermSeq

/-- A `TermSeq` with a single term. -/
@[simps (attr := grind =), expose]
def single (r : ℝ) (e : Surreal) (hr : r ≠ 0) : TermSeq where
  length := 1
  exp _ := e
  coeff _ := r
  exp_strictAnti _ := by simp
  coeff_ne_zero _ := hr

/-- Appends a single term at the end of a `TermSeq`. -/
@[simps (attr := grind =) -isSimp length, expose]
def appendSingle (s : TermSeq) (r : ℝ) (e : Surreal) (hr : r ≠ 0) (he : ∀ i, e < s.exp i) :
    TermSeq where
  length := s.length + 1
  exp i := if h : i = s.length then e else s.exp ⟨i, by grind⟩
  coeff i := if h : i = s.length then r else s.coeff ⟨i, by grind⟩
  exp_strictAnti := by grind [StrictAnti]
  coeff_ne_zero := by grind

attribute [simp] appendSingle_length

@[grind =]
theorem appendSingle_exp (s : TermSeq) (r : ℝ) (e : Surreal) (hr : r ≠ 0)
    (he : ∀ i, e < s.exp i) (i : Iio (s.appendSingle r e hr he).length) :
    (s.appendSingle r e hr he).exp i =
      if h : (i : Ordinal) = s.length then e else s.exp ⟨i, by
        have hi := i.property
        change (i : Ordinal) < s.length + 1 at hi
        exact lt_of_le_of_ne (Order.lt_add_one_iff.mp hi) h⟩ := rfl

@[grind =]
theorem appendSingle_coeff (s : TermSeq) (r : ℝ) (e : Surreal) (hr : r ≠ 0)
    (he : ∀ i, e < s.exp i) (i : Iio (s.appendSingle r e hr he).length) :
    (s.appendSingle r e hr he).coeff i =
      if h : (i : Ordinal) = s.length then r else s.coeff ⟨i, by
        have hi := i.property
        change (i : Ordinal) < s.length + 1 at hi
        exact lt_of_le_of_ne (Order.lt_add_one_iff.mp hi) h⟩ := rfl

theorem exp_eq_exp_appendSingle (s : TermSeq) (i r e hr he) :
    s.exp i = (s.appendSingle r e hr he).exp ⟨i.1, by grind⟩ := by
  rw [appendSingle_exp, dite_eq_right (ne_of_lt i.2)]

theorem coeff_eq_coeff_appendSingle (s : TermSeq) (i r e hr he) :
    s.coeff i = (s.appendSingle r e hr he).coeff ⟨i.1, by grind⟩ := by
  rw [appendSingle_coeff, dite_eq_right (ne_of_lt i.2)]

@[simp, grind =]
theorem exp_appendSingle_same (s : TermSeq) (r e hr he) :
    (s.appendSingle r e hr he).exp ⟨s.length, by grind⟩ = e := by
  rw [appendSingle_exp, dite_eq_left rfl]

@[simp, grind =]
theorem coeff_appendSingle_same (s : TermSeq) (r e hr he) :
    (s.appendSingle r e hr he).coeff ⟨s.length, by grind⟩ = r := by
  rw [appendSingle_coeff, dite_eq_left rfl]

@[simp]
theorem coe_appendSingle {s : TermSeq} {r : ℝ} {e : Surreal} (hr : r ≠ 0) (he : ∀ i, e < s.exp i) :
    appendSingle s r e hr he = s + SurrealHahnSeries.single e r := by
  ext j
  by_cases hj : j ∈ range s.exp
  · obtain ⟨j, rfl⟩ := hj
    rw [coeff_add_apply]
    conv_lhs => rw [exp_eq_exp_appendSingle s j r e hr he]
    rw [coeff_coe, appendSingle_coeff, dite_eq_right (ne_of_lt j.2), coeff_coe,
      coeff_single_of_ne (ne_of_lt (he j)), add_zero]
  · rw [coeff_add_apply, coeff_coe_of_notMem hj, zero_add]
    obtain rfl | he := eq_or_ne e j
    · conv_lhs => right; rw [← exp_appendSingle_same s r e hr he]
      rw [coeff_coe]
      simp
    · rw [coeff_single_of_ne he, coeff_coe_of_notMem]
      rintro ⟨k, hk⟩
      rw [appendSingle_exp] at hk
      split at hk
      · exact he hk
      · apply hj
        refine ⟨⟨k, ?_⟩, hk⟩
        have hk' : ↑k ≤ s.length := by
          rw [← Order.lt_add_one_iff, ← appendSingle_length]
          exact k.2
        exact lt_of_le_of_ne hk' ‹↑k ≠ s.length›

/-- Truncate a `TermSeq` at the i-th term. -/
@[simps (attr := grind =) length, expose]
def trunc (s : TermSeq) (i : Ordinal) : TermSeq where
  length := min i s.length
  exp i := s.exp ⟨i, by grind⟩
  coeff i := s.coeff ⟨i, by grind⟩
  exp_strictAnti _ := by grind
  coeff_ne_zero := by grind

@[simp, grind =]
theorem trunc_exp (s : TermSeq) (j : Ordinal) (i : Iio (s.trunc j).length) :
    (s.trunc j).exp i = s.exp ⟨i, by
      have hi := i.property
      change (i : Ordinal) < min j s.length at hi
      exact hi.trans_le (min_le_right ..)⟩ := rfl

@[simp, grind =]
theorem trunc_coeff (s : TermSeq) (j : Ordinal) (i : Iio (s.trunc j).length) :
    (s.trunc j).coeff i = s.coeff ⟨i, by
      have hi := i.property
      change (i : Ordinal) < min j s.length at hi
      exact hi.trans_le (min_le_right ..)⟩ := rfl

@[simp]
theorem trunc_of_le {s : TermSeq} {i : Ordinal} (h : s.length ≤ i) : s.trunc i = s := by
  ext
  · simpa
  · rfl
  · rfl

@[simp]
theorem trunc_trunc (s : TermSeq) (i j : Ordinal) : (s.trunc i).trunc j = s.trunc (min i j) := by
  ext
  · simp only [trunc_length]
    ac_rfl
  · simp
  · simp

@[simp ←]
theorem coe_trunc (s : TermSeq) (i : Ordinal) : s.trunc i = truncIdx s i := by
  obtain hi | hi := lt_or_ge i s.length
  · rw [truncIdx_of_lt (by simpa), exp_coe]
    ext j
    by_cases hj : j ∈ range s.exp
    · obtain ⟨⟨j, hj⟩, _, rfl⟩ := hj
      obtain hj' | hj' := lt_or_ge j i
      · rw [coeff_trunc_of_lt]
        · have hj'' : j ∈ Iio (s.trunc i).length := by
            simpa only [trunc_length, mem_Iio, lt_inf_iff] using And.intro hj' hj
          change
            coeff (s.trunc i : SurrealHahnSeries)
                ((s.trunc i).exp ⟨j, hj''⟩) =
              coeff (s : SurrealHahnSeries) (s.exp ⟨j, hj⟩)
          rw [coeff_coe, coeff_coe]
          rw [trunc_coeff]
        · simpa
      · rw [coeff_trunc_of_le, coeff_coe_of_notMem]
        · grind
        · simpa
    · rw [coeff_trunc_eq_zero, coeff_coe_of_notMem]
      · grind
      · rwa [← support_coe, mem_support_iff, not_ne_iff] at hj
  · rw [trunc_of_le hi, truncIdx_of_le (by simpa)]

theorem trunc_appendSingle {s : TermSeq} {r e hr he} {i} (hi : i ≤ s.length) :
    trunc (s.appendSingle r e hr he) i = trunc s i := by
  apply TermSeq.ext
  · have hi' : i ≤ s.length + 1 := hi.trans (by simp)
    rw [trunc_length, trunc_length, appendSingle_length, min_eq_left hi, min_eq_left hi']
  · intro k hs ht
    have hk : k < s.length := by
      apply lt_of_lt_of_le ht
      rw [trunc_length]
      exact min_le_right ..
    rw [trunc_exp, trunc_exp, appendSingle_exp, dite_eq_right (ne_of_lt hk)]
  · intro k hs ht
    have hk : k < s.length := by
      apply lt_of_lt_of_le ht
      rw [trunc_length]
      exact min_le_right ..
    rw [trunc_coeff, trunc_coeff, appendSingle_coeff, dite_eq_right (ne_of_lt hk)]

@[simp]
theorem trunc_appendSingle_self (s : TermSeq) {r e} (hr he) :
    trunc (s.appendSingle r e hr he) s.length = s := by
  rw [trunc_appendSingle le_rfl , trunc_of_le le_rfl]

theorem trunc_add_one {s : TermSeq} {i} (hi : i ∈ Iio s.length) :
    s.trunc (i + 1) =
      (s.trunc i).appendSingle (s.coeff ⟨i, hi⟩) (s.exp ⟨i, hi⟩) (by simp) (by grind) := by
  have hi' : i + 1 ≤ s.length := Order.add_one_le_iff.mpr hi
  have hlength : (s.trunc i).length = i := by
    rw [trunc_length, min_eq_left hi.le]
  apply TermSeq.ext
  · rw [trunc_length, appendSingle_length, hlength, min_eq_left hi']
  · intro k hs ht
    have hk : k < i + 1 := by
      apply lt_of_lt_of_le hs
      rw [trunc_length]
      exact min_le_left ..
    rw [appendSingle_exp]
    by_cases hki : k = i
    · rw [dite_eq_left (hki.trans hlength.symm), trunc_exp]
      subst k
      rfl
    · rw [dite_eq_right (by
        intro h
        exact hki (h.trans hlength)), trunc_exp, trunc_exp]
  · intro k hs ht
    have hk : k < i + 1 := by
      apply lt_of_lt_of_le hs
      rw [trunc_length]
      exact min_le_left ..
    rw [appendSingle_coeff]
    by_cases hki : k = i
    · rw [dite_eq_left (hki.trans hlength.symm), trunc_coeff]
      subst k
      rfl
    · rw [dite_eq_right (by
        intro h
        exact hki (h.trans hlength)), trunc_coeff, trunc_coeff]


end TermSeq

/-! ### Recursion principles -/

/-- Build data for a `SurrealHahnSeries` by building it for a `TermSeq`. -/
def termSeqRecOn {motive : SurrealHahnSeries → Sort*} (x : SurrealHahnSeries)
    (mk : ∀ s : TermSeq, motive s) : motive x :=
  cast (congrArg _ (by simp)) (mk (.ofSurrealHahnSeries x))

@[simp]
theorem termSeqRecOn_coe {motive : SurrealHahnSeries → Sort*} {mk} (s : TermSeq) :
    termSeqRecOn (motive := motive) s mk = mk s := by
  rw [termSeqRecOn, cast_eq_iff_heq]
  congr
  simp

theorem length_add_single {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (h : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) : (x + single i r).length = x.length + 1 := by
  induction x using termSeqRecOn with | mk s
  rw [← TermSeq.coe_appendSingle hr fun _ ↦ h _ (by simp)]
  rw [TermSeq.length_coe]
  simp

theorem length_add_single_le {x : SurrealHahnSeries} {i : Surreal} {r : ℝ}
    (h : ∀ j ∈ x.support, i < j) : (x + single i r).length ≤ x.length + 1 := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · rw [length_add_single h hr]

@[simp]
theorem length_single (i : Surreal) {r : ℝ} (hr : r ≠ 0) : length (.single i r) = 1 := by
  rw [← zero_add (single i r), length_add_single _ hr] <;> simp

theorem length_single_le (i : Surreal) (r : ℝ) : length (.single i r) ≤ 1 := by
  obtain rfl | hr := eq_or_ne r 0 <;> simp_all

private theorem isLeast_support_succ {x : SurrealHahnSeries} {o : Ordinal} (h : x.length = o + 1) :
    (x.exp ⟨o, by simp_all⟩).1 ∈ lowerBounds x.support := by
  refine fun j hj ↦ ?_
  change _ ≤ ↑(⟨j, hj⟩ : x.support)
  rw [← symm_exp_le_symm_exp_iff, x.exp.symm_apply_apply, ← Subtype.coe_le_coe, ← lt_add_one_iff]
  exact h ▸ symm_exp_lt _

-- Auxiliary construction for `lengthRecOn`.
private def lengthRecOnAux {motive : SurrealHahnSeries → Sort*} (o : Ordinal)
    (succ : ∀ y i r, (∀ j ∈ y.support, i < j) → r ≠ 0 → motive y → motive (y + single i r))
    (limit : ∀ y, IsSuccPrelimit y.length → (∀ z, length z < length y → motive z) → motive y) :
    ∀ x, x.length = o → motive x :=
  SuccOrder.prelimitRecOn o
    (by
      refine fun a _ IH x hx ↦ cast (congrArg _ <| trunc_add_single (isLeast_support_succ hx))
        (succ (x.trunc <| x.exp ⟨a, ?_⟩) _ _ ?_ ?_ (IH _ ?_))
      all_goals aesop
    )
    (fun a ha IH x hx ↦ limit _ (hx ▸ ha) fun y hy ↦ IH _ (hx ▸ hy) _ rfl)

private theorem lengthRecOnAux_succ {motive : SurrealHahnSeries → Sort*}
    {o a : Ordinal} (ha : a = o + 1) {succ limit} :
    lengthRecOnAux (motive := motive) a succ limit = fun x _ ↦
      cast (congrArg _ <| trunc_add_single (isLeast_support_succ <| by simp_all))
        (succ (x.trunc <| x.exp ⟨o, _⟩) _ _ (by grind) (by simp_all)
          (lengthRecOnAux o succ limit _ (by grind))) := by
  subst ha; exact SuccOrder.prelimitRecOn_succ ..

private theorem lengthRecOnAux_limit {motive : SurrealHahnSeries → Sort*}
    {o : Ordinal} (ho : IsSuccPrelimit o) {succ limit} :
    lengthRecOnAux (motive := motive) o succ limit = fun y hy ↦
      limit y (by simp_all) fun z _ ↦ lengthRecOnAux _ succ limit z rfl :=
  SuccOrder.prelimitRecOn_of_isSuccPrelimit _ _ ho

/-- Recursion on the length of a Hahn series, separating out the case where it's a
succesor ordinal. -/
def lengthRecOn {motive : SurrealHahnSeries → Sort*} (x : SurrealHahnSeries)
    (succ : ∀ y i r, (∀ j ∈ y.support, i < j) → r ≠ 0 → motive y → motive (y + single i r))
    (limit : ∀ y, IsSuccPrelimit y.length → (∀ z, length z < length y → motive z) → motive y) :
    motive x :=
  lengthRecOnAux _ succ limit _ rfl

theorem lengthRecOn_succ {motive : SurrealHahnSeries → Sort*} {succ limit}
    {x : SurrealHahnSeries} {i : Surreal} {r : ℝ} (hi : ∀ j ∈ x.support, i < j) (hr : r ≠ 0) :
    lengthRecOn (motive := motive) (x + single i r) succ limit =
      succ _ _ _ hi hr (lengthRecOn x succ limit) := by
  rw [lengthRecOn, lengthRecOnAux_succ (o := x.length), cast_eq_iff_heq, lengthRecOn]
  · have H : ∀ {hx}, ↑((x + single i r).exp ⟨x.length, hx⟩) = i := by
      induction x using termSeqRecOn with | mk s
      rw [← TermSeq.coe_appendSingle hr fun _ ↦ hi _ (by simp)]
      simp
    congr!
    · rw [H, trunc_add, trunc_single_of_le le_rfl, add_zero, trunc_eq_self hi]
    · exact H
    · rw [H]
      simpa using mt (hi i) (lt_irrefl i)
  · exact length_add_single hi hr

theorem lengthRecOn_limit {motive : SurrealHahnSeries → Sort*}
    {x : SurrealHahnSeries} (hx : IsSuccPrelimit x.length) {succ limit} :
    lengthRecOn (motive := motive) x succ limit =
      limit x hx fun y _ ↦ lengthRecOn y succ limit := by
  rw [lengthRecOn, lengthRecOnAux_limit hx]
  rfl

/-! ### Extra lemmas -/

theorem length_truncIdx_add_single {x : SurrealHahnSeries} (i : Iio x.length) {r : ℝ} (hr : r ≠ 0) :
    (x.truncIdx i + single (x.exp i) r).length = i + 1 := by
  rw [length_add_single _ hr, length_truncIdx]
  · grind
  · rw [truncIdx_of_lt i.2, support_trunc]
    aesop

theorem length_truncIdx_add_single_le {x : SurrealHahnSeries} (i : Iio x.length) (r : ℝ) :
    (x.truncIdx i + single (x.exp i) r).length ≤ i + 1 := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · rw [length_truncIdx_add_single _ hr]

@[simp]
theorem truncIdx_truncIdx (x : SurrealHahnSeries) (i j : Ordinal) :
    (x.truncIdx i).truncIdx j = x.truncIdx (min i j) := by
  induction x using termSeqRecOn with | mk s
  simp

@[aesop simp]
theorem coeffIdx_truncIdx (x : SurrealHahnSeries) (i : Ordinal) :
    (x.truncIdx i).coeffIdx = fun j ↦ if j < i then x.coeffIdx j else 0 := by
  ext j
  induction x using termSeqRecOn with | mk s
  aesop

theorem coeffIdx_truncIdx_of_lt {x : SurrealHahnSeries} {i j : Ordinal} (h : j < i) :
    (x.truncIdx i).coeffIdx j = x.coeffIdx j := by
  rw [coeffIdx_truncIdx]
  exact ite_eq_left h

theorem coeffIdx_truncIdx_of_le {x : SurrealHahnSeries} {i j : Ordinal} (h : i ≤ j) :
    (x.truncIdx i).coeffIdx j = 0 := by
  rw [coeffIdx_truncIdx]
  exact ite_eq_right h.not_gt

theorem truncIdx_add_one {x : SurrealHahnSeries} {i : Ordinal} (hi : i ∈ Iio x.length) :
    x.truncIdx (i + 1) = x.truncIdx i + single (x.exp ⟨i, hi⟩) (x.coeffIdx i) := by
  induction x using termSeqRecOn with | mk s
  have hs : i ∈ Iio s.length := by simpa using hi
  have hseq := congrArg (fun t : TermSeq ↦ (t : SurrealHahnSeries)) (TermSeq.trunc_add_one hs)
  rw [TermSeq.coe_appendSingle] at hseq
  simpa only [TermSeq.coe_trunc, TermSeq.exp_coe, TermSeq.coeffIdx_coe_of_lt hs] using hseq

theorem eq_of_length_eq_add_one {x : SurrealHahnSeries} {i : Ordinal} (hi : x.length = i + 1) :
    x = x.truncIdx i + single (x.exp ⟨i, by simp [hi]⟩) (x.coeffIdx i) := by
  rw [← truncIdx_add_one, truncIdx_of_le hi.le]

theorem support_truncIdx_strictMonoOn {x : SurrealHahnSeries} :
    StrictMonoOn (fun i ↦ (truncIdx x i).support) (Iio x.length) := by
  intro i hi j hj h
  dsimp
  rw [← min_eq_right h.le, ← truncIdx_truncIdx]
  apply support_truncIdx_ssubset
  simp_all

theorem support_truncIdx_mono {x : SurrealHahnSeries} :
    Monotone fun i ↦ (truncIdx x i).support := by
  intro i j h
  dsimp
  rw [← min_eq_right h, ← truncIdx_truncIdx]
  exact support_truncIdx_subset ..

@[simp]
theorem exp_truncIdx {x : SurrealHahnSeries} {i : Ordinal} (j : Iio (x.truncIdx i).length) :
    (x.truncIdx i).exp j = ⟨x.exp ⟨j, by
      exact j.property.trans_le ((length_truncIdx x i).le.trans (min_le_right ..))⟩, by
        rw [support_truncIdx]
        split_ifs with h
        · refine ⟨(x.exp _).property, ?_⟩
          change x.exp _ > x.exp ⟨i, h⟩
          apply x.exp.map_rel_iff.mpr
          change (j : Ordinal) < i
          exact j.property.trans_le ((length_truncIdx x i).le.trans (min_le_left ..))
        · exact (x.exp _).property⟩ := by
  induction x using termSeqRecOn with | mk s
  apply Subtype.val_injective
  rw [exp_congr (TermSeq.coe_trunc s i).symm]
  simp

theorem term_truncIdx_of_lt {x : SurrealHahnSeries} {i j : Ordinal} (h : j < i) :
    (x.truncIdx i).term j = x.term j := by
  obtain h' | h' := le_or_gt x.length j
  · rw [truncIdx_of_le (h'.trans h.le)]
  · rw [term_of_lt, term_of_lt h', coeffIdx_truncIdx_of_lt h]
    · simp
    · simpa [h]

theorem term_truncIdx_of_le {x : SurrealHahnSeries} {i j : Ordinal} (h : i ≤ j) :
    (x.truncIdx i).term j = 0 := by
  rw [term_of_le]
  simp [h]

theorem term_injective : term.Injective := by
  intro x y h
  induction x using termSeqRecOn with | mk s
  induction y using termSeqRecOn with | mk t
  congr
  ext i hs ht
  · refine eq_of_forall_ge_iff fun _ ↦ ?_
    simp_rw [← TermSeq.length_coe, ← term_eq_zero, h]
  · have he := congrArg Surreal.wlog (congrFun h i)
    rw [wlog_term (by simpa using hs), wlog_term (by simpa using ht),
      TermSeq.exp_coe, TermSeq.exp_coe] at he
    exact he
  · have hc := congrArg Surreal.leadingCoeff (congrFun h i)
    rw [leadingCoeff_term, leadingCoeff_term,
      TermSeq.coeffIdx_coe_of_lt hs, TermSeq.coeffIdx_coe_of_lt ht] at hc
    exact hc

@[simp]
theorem term_inj {x y : SurrealHahnSeries} : x.term = y.term ↔ x = y :=
  term_injective.eq_iff

end SurrealHahnSeries
