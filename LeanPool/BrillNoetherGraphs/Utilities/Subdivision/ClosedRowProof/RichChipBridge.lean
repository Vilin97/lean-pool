/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichChipDecoder

/-!
# The W5 endpoint chip bridge

`RichChipDecoder.rawChipMassAt` is the *physical* signed chip mass sitting at
one literal coordinate of a displayed slot: it selects the raw chips of that
slot whose form **evaluates** to the coordinate.  The checker, by contrast,
accounts for chips syntactically: `chipPrefix` sums the chips whose *first
syntactic match* among the named points of the anchor is one of the first `s`
named points.

This module proves that the two agree exactly, at the tail coordinate `0` and
at the head coordinate `eval (coordForm e) x`.  Exactness — rather than a
one-sided bound — is forced: ordinary leaves permit negative chip
coefficients, so a chip landing on an endpoint can make the actual endpoint
contribution *smaller*, and an inequality in the wrong direction would be
useless to W5.

The reason no geometry is needed is that `chipMatches` compares forms with
`formEq`, i.e. syntactically.  `Arith.eval_eq_of_formEq` therefore identifies
a matched chip with its named point *at every parameter point*, so the two
indicators agree chipwise:

* existence of a first match is W3;
* uniqueness of a first match (among nonzero indices) is the `range (i - 1)`
  clause of `chipMatches`;
* a matched chip evaluates to `0` exactly when its match index lies in the
  collapsed prefix.

Finally, W1's slack discipline bounds the realized collapse count by the
declared slack, which is what the `minOver` in `tailContribution` /
`headContribution` needs.
-/

@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open MarkedGraphs.Certificate
open Utilities.Certificate

namespace RichWitness

variable {n p : ℕ}

/-! ## Elementary sum plumbing -/

/-- Exchange a finite index sum with a list sum. -/
private theorem sum_range_list_sum {α : Type} (l : List α) (f : ℕ → α → ℤ)
    (k : ℕ) :
    ∑ i ∈ Finset.range k, (l.map (f i)).sum
      = (l.map fun c => ∑ i ∈ Finset.range k, f i c).sum := by
  induction l with
  | nil => simp
  | cons c l ih =>
      simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

/-- The head-side chip sum used by `headCandidate`, named so that the bridge
can be stated without repeating the fold. -/
def headChipSum (w : RichWitness) (a e s : ℕ) : ℤ :=
  (List.range (s + 1)).foldl (fun z t =>
    if t = 0 then z else z + w.chipAt a e ((w.blockList a e).length - t)) 0

theorem headCandidate_eq_headChipSum_sub (w : RichWitness) (a e s : ℕ) :
    w.headCandidate a e s =
      w.headChipSum a e s -
        (w.block a e ((w.blockList a e).length - 1 - s)).hi := rfl

/-- `chipPrefix` as a single list sum of per-chip first-match indicators. -/
theorem chipPrefix_eq_chipwise (w : RichWitness) (a e s : ℕ) :
    w.chipPrefix a e s =
      (w.chips.map fun c => ∑ i ∈ Finset.range (s + 1),
        (if i = 0 then (0 : ℤ)
          else if w.chipMatches a e i c then c.2.2 else 0)).sum := by
  have hswap := sum_range_list_sum w.chips
    (fun i c => if i = 0 then (0 : ℤ)
      else if w.chipMatches a e i c then c.2.2 else 0) (s + 1)
  rw [w.chipPrefix_eq_indicator_sum a e s,
    foldl_range_eq_finset_sum (fun i => if i = 0 then (0 : ℤ)
      else (w.chips.map fun c =>
        if w.chipMatches a e i c then c.2.2 else 0).sum) (s + 1), ← hswap]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = 0
  · subst hi
    simp
  · simp [hi]

/-- `headChipSum` as a single list sum of per-chip first-match indicators. -/
theorem headChipSum_eq_chipwise (w : RichWitness) (a e s : ℕ) :
    w.headChipSum a e s =
      (w.chips.map fun c => ∑ t ∈ Finset.range (s + 1),
        (if t = 0 then (0 : ℤ)
          else if (w.blockList a e).length - t = 0 then 0
          else if w.chipMatches a e ((w.blockList a e).length - t) c then
            c.2.2 else 0)).sum := by
  have hswap := sum_range_list_sum w.chips
    (fun t c => if t = 0 then (0 : ℤ)
      else if (w.blockList a e).length - t = 0 then 0
      else if w.chipMatches a e ((w.blockList a e).length - t) c then
        c.2.2 else 0) (s + 1)
  have hfold := w.headChipSum_eq_indicator_sum a e s
  rw [← hswap]
  rw [headChipSum, hfold]
  have hfun : (fun (z : ℤ) (t : ℕ) =>
      if t = 0 then z else z +
        (if (w.blockList a e).length - t = 0 then 0 else
          (w.chips.map fun c =>
            if w.chipMatches a e ((w.blockList a e).length - t) c then
              c.2.2 else 0).sum))
      = (fun (z : ℤ) (t : ℕ) => z +
        (if t = 0 then 0 else
          if (w.blockList a e).length - t = 0 then 0 else
            (w.chips.map fun c =>
              if w.chipMatches a e ((w.blockList a e).length - t) c then
                c.2.2 else 0).sum)) := by
    funext z t
    split <;> simp
  rw [hfun, foldl_range_eq_finset_sum (fun t => if t = 0 then (0 : ℤ) else
    if (w.blockList a e).length - t = 0 then 0 else
      (w.chips.map fun c =>
        if w.chipMatches a e ((w.blockList a e).length - t) c then
          c.2.2 else 0).sum) (s + 1)]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases ht : t = 0
  · subst ht
    simp
  · by_cases hk : (w.blockList a e).length - t = 0 <;> simp [ht, hk]

/-! ## The chipwise first match -/

/-- **First-match existence and uniqueness.**  On an accepted rich leaf every
raw chip has exactly one nonzero named index at which `chipMatches` fires, and
that index is a genuine interior index of the anchor's block list.

Index `0` is deliberately excluded from the uniqueness clause: `point a e 0`
is the empty form, so a chip whose form is identically zero also matches
there.  The checker never reads index `0` (`chipAt` returns `0`), so this is
exactly the uniqueness statement the accounting needs. -/
theorem exists_unique_chipMatches (w : RichWitness)
    (core : ExplicitPotential.Core n p) (hW3 : w.w3Checks core = true)
    (a : Fin n) {c : ℕ × Form × ℤ} (hc : c ∈ w.chips) :
    ∃ i, 1 ≤ i ∧ i ≤ (w.blockList a.val c.1).length - 1 ∧
      formEq c.2.1 (w.point a.val c.1 i) = true ∧
      w.chipMatches a.val c.1 i c = true ∧
      ∀ j, 1 ≤ j → w.chipMatches a.val c.1 j c = true → j = i := by
  classical
  obtain ⟨i, hi, hform⟩ := w.chip_named_of_w3Checks core hW3 a hc
  have hex : ∃ j, formEq c.2.1 (w.point a.val c.1 (j + 1)) = true := ⟨i, hform⟩
  have hspec : formEq c.2.1 (w.point a.val c.1 (Nat.find hex + 1)) = true :=
    Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex,
      formEq c.2.1 (w.point a.val c.1 (j + 1)) = false := by
    intro j hj
    simpa using Nat.find_min hex hj
  have hle : Nat.find hex ≤ i := Nat.find_min' hex hform
  refine ⟨Nat.find hex + 1, by omega, by omega, hspec, ?_, ?_⟩
  · simp only [chipMatches, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
      Nat.add_sub_cancel]
    refine ⟨⟨trivial, hspec⟩, ?_⟩
    intro j hj
    simp [hmin j (List.mem_range.mp hj)]
  · intro j hj1 hj
    simp only [chipMatches, Bool.and_eq_true, beq_iff_eq,
      List.all_eq_true] at hj
    obtain ⟨⟨_, hformj⟩, hall⟩ := hj
    have hj' : formEq c.2.1 (w.point a.val c.1 ((j - 1) + 1)) = true := by
      rwa [show j - 1 + 1 = j by omega]
    have hfind : Nat.find hex ≤ j - 1 := Nat.find_min' hex hj'
    by_contra hne
    have hlt : Nat.find hex < j - 1 := by omega
    have hmem : Nat.find hex ∈ List.range (j - 1) := List.mem_range.mpr hlt
    have := hall _ hmem
    simp [hspec] at this

/-! ## The tail bridge -/

/-- **The W5 tail chip bridge.**  The physical signed chip mass at the tail
coordinate of slot `e` is exactly the checker's first-match prefix sum through
the last collapsed named point.

The two hypotheses say precisely that the named points `1, …, s` are the ones
which have fallen into the tail; no other geometric input is used, because
`chipMatches` identifies a chip with its named point syntactically. -/
theorem rawChipMassAt_zero_eq_chipPrefix (w : RichWitness)
    (core : ExplicitPotential.Core n p) (hW3 : w.w3Checks core = true)
    (x : List ℤ) (a : Fin n) (e : Fin p) (s : ℕ)
    (hzero : ∀ i, 1 ≤ i → i ≤ s → w.pointValue x a.val e.val i = 0)
    (hpos : ∀ i, s < i → i ≤ (w.blockList a.val e.val).length - 1 →
      w.pointValue x a.val e.val i ≠ 0) :
    w.rawChipMassAt x e.val 0 = w.chipPrefix a.val e.val s := by
  classical
  rw [w.chipPrefix_eq_chipwise a.val e.val s, rawChipMassAt]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro c hc
  by_cases hslot : c.1 = e.val
  · obtain ⟨i₀, hi₀pos, hi₀le, hi₀form, hi₀match, hi₀uniq⟩ :=
      w.exists_unique_chipMatches core hW3 a hc
    rw [hslot] at hi₀le hi₀form hi₀match hi₀uniq
    have hvalue : eval c.2.1 x = w.pointValue x a.val e.val i₀ :=
      eval_eq_of_formEq hi₀form x
    have hterm : ∀ i ∈ Finset.range (s + 1),
        (if i = 0 then (0 : ℤ)
          else if w.chipMatches a.val e.val i c then c.2.2 else 0)
          = if i = i₀ then c.2.2 else 0 := by
      intro i _
      by_cases hi : i = 0
      · subst hi
        rw [ite_eq_left rfl, ite_eq_right (by omega)]
      · rw [ite_eq_right hi]
        by_cases hm : w.chipMatches a.val e.val i c = true
        · rw [ite_eq_left hm, ite_eq_left (hi₀uniq i (by omega) hm)]
        · rw [ite_eq_right hm, ite_eq_right ?_]
          rintro rfl
          exact hm hi₀match
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (s + 1)) i₀
      (fun _ => c.2.2)]
    by_cases hcase : i₀ ≤ s
    · rw [ite_eq_left (Finset.mem_range.mpr (by omega))]
      rw [ite_eq_left]
      simp only [Bool.and_eq_true, beq_iff_eq, hslot, true_and]
      rw [hvalue]
      exact hzero i₀ hi₀pos hcase
    · have hnotmem : i₀ ∉ Finset.range (s + 1) := by
        simp only [Finset.mem_range]
        omega
      rw [ite_eq_right hnotmem, ite_eq_right]
      simp only [Bool.and_eq_true, beq_iff_eq, hslot, true_and, hvalue]
      exact hpos i₀ (by omega) hi₀le
  · have hfalse : ∀ i, w.chipMatches a.val e.val i c = false := by
      intro i
      simp [chipMatches, hslot]
    simp [hslot, hfalse]

/-! ## The head bridge -/

/-- **The W5 head chip bridge**, the mirror of `rawChipMassAt_zero_eq_chipPrefix`
at the far endpoint of the slot.  Here `s` counts the named points which have
fallen into the head, and `L` is the evaluated slot length. -/
theorem rawChipMassAt_length_eq_headChipSum (w : RichWitness)
    (core : ExplicitPotential.Core n p) (hW3 : w.w3Checks core = true)
    (x : List ℤ) (a : Fin n) (e : Fin p) (s : ℕ) (L : ℤ)
    (hs : s ≤ (w.blockList a.val e.val).length - 1)
    (hhead : ∀ i, (w.blockList a.val e.val).length - s ≤ i →
      i ≤ (w.blockList a.val e.val).length - 1 →
      w.pointValue x a.val e.val i = L)
    (hlow : ∀ i, 1 ≤ i → i < (w.blockList a.val e.val).length - s →
      w.pointValue x a.val e.val i ≠ L) :
    w.rawChipMassAt x e.val L = w.headChipSum a.val e.val s := by
  classical
  set k := (w.blockList a.val e.val).length with hk
  rw [w.headChipSum_eq_chipwise a.val e.val s, rawChipMassAt]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro c hc
  by_cases hslot : c.1 = e.val
  · obtain ⟨i₀, hi₀pos, hi₀le, hi₀form, hi₀match, hi₀uniq⟩ :=
      w.exists_unique_chipMatches core hW3 a hc
    rw [hslot] at hi₀le hi₀form hi₀match hi₀uniq
    rw [← hk] at hi₀le
    have hvalue : eval c.2.1 x = w.pointValue x a.val e.val i₀ :=
      eval_eq_of_formEq hi₀form x
    have hterm : ∀ t ∈ Finset.range (s + 1),
        (if t = 0 then (0 : ℤ)
          else if k - t = 0 then 0
          else if w.chipMatches a.val e.val (k - t) c then c.2.2 else 0)
          = if t = k - i₀ then c.2.2 else 0 := by
      intro t ht
      have hts : t ≤ s := by
        have := Finset.mem_range.mp ht
        omega
      by_cases htz : t = 0
      · subst htz
        rw [ite_eq_left rfl, ite_eq_right (by omega)]
      · rw [ite_eq_right htz, ite_eq_right (by omega)]
        by_cases hm : w.chipMatches a.val e.val (k - t) c = true
        · rw [ite_eq_left hm, ite_eq_left]
          have := hi₀uniq (k - t) (by omega) hm
          omega
        · rw [ite_eq_right hm, ite_eq_right ?_]
          intro hEq
          refine hm ?_
          have : k - t = i₀ := by omega
          rw [this]
          exact hi₀match
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (s + 1))
      (k - i₀) (fun _ => c.2.2)]
    by_cases hcase : k - s ≤ i₀
    · rw [ite_eq_left (Finset.mem_range.mpr (by omega)), ite_eq_left]
      simp only [Bool.and_eq_true, beq_iff_eq, hslot, true_and]
      rw [hvalue]
      exact hhead i₀ hcase hi₀le
    · have hnotmem : k - i₀ ∉ Finset.range (s + 1) := by
        simp only [Finset.mem_range]
        omega
      rw [ite_eq_right hnotmem, ite_eq_right]
      simp only [Bool.and_eq_true, beq_iff_eq, hslot, true_and, hvalue]
      exact hlow i₀ hi₀pos (by omega)
  · have hfalse : ∀ i, w.chipMatches a.val e.val i c = false := by
      intro i
      simp [chipMatches, hslot]
    simp [hslot, hfalse]

/-! ## The interior bridge

W4's residual is stated against `w4ChipSum`, the first-match chip total over a
run of named indices.  At a forward selector change the run is a *maximal*
block of named indices sharing one strictly interior coordinate, so the same
chipwise argument as at the endpoints identifies it with the physical chip
mass there.  Unlike the endpoint bridges no index `0` case arises, because a
W4 run starts at `1`. -/

/-- `w4ChipSum` as a single list sum of per-chip first-match indicators. -/
theorem w4ChipSum_eq_chipwise (w : RichWitness) (a e i j : ℕ) (hI : 1 ≤ i) :
    w4ChipSum (fun t => w.chipAt a e t) i j =
      (w.chips.map fun c => ∑ t ∈ Finset.range (j + 1 - i),
        (if w.chipMatches a e (i + t) c then c.2.2 else 0)).sum := by
  have hswap := sum_range_list_sum w.chips
    (fun t c => if w.chipMatches a e (i + t) c then c.2.2 else 0) (j + 1 - i)
  rw [← hswap, w4ChipSum, foldl_range_eq_finset_sum
    (fun t => w.chipAt a e (i + t)) (j + 1 - i)]
  refine Finset.sum_congr rfl fun t _ => ?_
  exact w.chipAt_eq_indicator_sum a e (i + t) (by omega)

/-- **The W4 interior chip bridge.**  The physical signed chip mass at a
coordinate carried by exactly the named points `i, …, j` of the anchor is the
checker's first-match run total.

The three hypotheses say that `i … j` is the *maximal* run of named interior
indices at the coordinate; that is what a forward selector change supplies. -/
theorem rawChipMassAt_eq_w4ChipSum (w : RichWitness)
    (core : ExplicitPotential.Core n p) (hW3 : w.w3Checks core = true)
    (x : List ℤ) (a : Fin n) (e : Fin p) (i j : ℕ) (q : ℤ)
    (hI : 1 ≤ i) (hIJ : i ≤ j)
    (hrun : ∀ t, i ≤ t → t ≤ j → w.pointValue x a.val e.val t = q)
    (hbelow : ∀ t, 1 ≤ t → t < i → w.pointValue x a.val e.val t ≠ q)
    (habove : ∀ t, j < t → t ≤ (w.blockList a.val e.val).length - 1 →
      w.pointValue x a.val e.val t ≠ q) :
    w.rawChipMassAt x e.val q = w4ChipSum (fun t => w.chipAt a.val e.val t) i j := by
  classical
  rw [w.w4ChipSum_eq_chipwise a.val e.val i j hI, rawChipMassAt]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro c hc
  by_cases hslot : c.1 = e.val
  · obtain ⟨i₀, hi₀pos, hi₀le, hi₀form, hi₀match, hi₀uniq⟩ :=
      w.exists_unique_chipMatches core hW3 a hc
    rw [hslot] at hi₀le hi₀form hi₀match hi₀uniq
    have hvalue : eval c.2.1 x = w.pointValue x a.val e.val i₀ :=
      eval_eq_of_formEq hi₀form x
    by_cases hle : i ≤ i₀
    · have hterm : ∀ t ∈ Finset.range (j + 1 - i),
          (if w.chipMatches a.val e.val (i + t) c then c.2.2 else 0)
            = if t = i₀ - i then c.2.2 else 0 := by
        intro t ht
        by_cases hm : w.chipMatches a.val e.val (i + t) c = true
        · have heq : i + t = i₀ := hi₀uniq (i + t) (by omega) hm
          rw [ite_eq_left hm, ite_eq_left (by omega : t = i₀ - i)]
        · have hne : ¬ (t = i₀ - i) := by
            intro hEq
            exact hm (by rw [show i + t = i₀ by omega]; exact hi₀match)
          rw [ite_eq_right hm, ite_eq_right hne]
      rw [Finset.sum_congr rfl hterm,
        Finset.sum_ite_eq' (Finset.range (j + 1 - i)) (i₀ - i) (fun _ => c.2.2)]
      by_cases hcase : i₀ ≤ j
      · rw [ite_eq_left (Finset.mem_range.mpr (by omega)), ite_eq_left]
        simp only [Bool.and_eq_true, beq_iff_eq, hslot, true_and]
        rw [hvalue]
        exact hrun i₀ hle hcase
      · have hnotmem : i₀ - i ∉ Finset.range (j + 1 - i) := by
          simp only [Finset.mem_range]
          omega
        rw [ite_eq_right hnotmem, ite_eq_right]
        simp only [Bool.and_eq_true, beq_iff_eq, hslot, true_and, hvalue]
        exact habove i₀ (by omega) hi₀le
    · have hzero : ∀ t ∈ Finset.range (j + 1 - i),
          (if w.chipMatches a.val e.val (i + t) c then c.2.2 else 0) = (0 : ℤ) := by
        intro t ht
        have hm : ¬ (w.chipMatches a.val e.val (i + t) c = true) := by
          intro hm
          have heq : i + t = i₀ := hi₀uniq (i + t) (by omega) hm
          omega
        rw [ite_eq_right hm]
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, ite_eq_right]
      simp only [Bool.and_eq_true, beq_iff_eq, hslot, true_and, hvalue]
      exact hbelow i₀ hi₀pos (by omega)
  · have hfalse : ∀ t, w.chipMatches a.val e.val t c = false := by
      intro t
      simp [chipMatches, hslot]
    simp [hslot, hfalse]

/-! ## Realizing the collapse counts, with W1's slack discipline

The bridges above take the realized collapse count as a parameter.  W1
supplies it: the named points are weakly monotone, so the collapsed ones form
a prefix (resp. a suffix), and the `positiveCheck` receipts on
`point a e (α + 1)` and on `coordForm e − point a e (k − 1 − ω)` bound that
prefix (resp. suffix) by the declared slack.  That bound is exactly what
`tailContribution_le_candidate` / `headContribution_le_candidate` need. -/

/-- The realized tail collapse count of an accepted rich leaf, with the tail
bridge and the W1 slack bound.  This is the hypothesis-shaped form consumed by
`RichW5Aggregation.w5ActualResidual_class_nonneg`. -/
theorem exists_tail_collapse (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (a : Fin n) (e : Fin p) :
    ∃ s ≤ (w.plan a.val).headSlack.getD e.val 0,
      s ≤ (w.blockList a.val e.val).length - 1 ∧
      w.pointValue x a.val e.val s = 0 ∧
      (∀ i, s < i → i ≤ (w.blockList a.val e.val).length - 1 →
        w.pointValue x a.val e.val i ≠ 0) ∧
      w.rawChipMassAt x e.val 0 = w.chipPrefix a.val e.val s := by
  classical
  set k := (w.blockList a.val e.val).length with hk
  set α := (w.plan a.val).headSlack.getD e.val 0 with hα
  have hLength : ∀ j < k, 0 ≤ w.blockLengthValue x a.val e.val j := fun j hj =>
    w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e j hj
  -- the largest collapsed named index
  set P : ℕ → Prop := fun i => w.pointValue x a.val e.val i = 0 with hP
  have hP0 : P 0 := by simp [hP]
  set s := Nat.findGreatest P (k - 1) with hs
  have hsle : s ≤ k - 1 := Nat.findGreatest_le _
  have hPs : P s := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hzero : ∀ i, 1 ≤ i → i ≤ s → w.pointValue x a.val e.val i = 0 := by
    intro i _ his
    have hmono := w.pointValue_mono_of_lengths x a.val e.val k hLength his
      (by omega)
    have hnn := w.pointValue_nonneg_of_lengths x a.val e.val k i hLength
      (by omega)
    have : w.pointValue x a.val e.val s = 0 := hPs
    omega
  have hpos : ∀ i, s < i → i ≤ k - 1 → w.pointValue x a.val e.val i ≠ 0 := by
    intro i hsi hik
    exact Nat.findGreatest_is_greatest hsi hik
  -- W1's tail slack receipt bounds the realized prefix by the declared slack
  have hslack : s ≤ α := by
    by_cases hbranch : α + 1 ≤ k - 1
    · have hW1' := hW1
      simp only [w1Checks, ExplicitPotential.allFin_eq_true_iff,
        Bool.and_eq_true] at hW1'
      have hclause := (hW1' a e).1.2
      rw [ite_eq_left (by simpa [hk, hα] using hbranch)] at hclause
      have hstrict : 0 < eval (w.point a.val e.val (α + 1)) x :=
        positiveCheck_sound hclause hx
      by_contra hnot
      have hsα : α + 1 ≤ s := by omega
      have hmono := w.pointValue_mono_of_lengths x a.val e.val k hLength hsα
        (by omega)
      have : w.pointValue x a.val e.val s = 0 := hPs
      have hval : w.pointValue x a.val e.val (α + 1) =
          eval (w.point a.val e.val (α + 1)) x := rfl
      omega
    · omega
  exact ⟨s, hslack, hsle, hPs, hpos,
    w.rawChipMassAt_zero_eq_chipPrefix core hW3 x a e s hzero hpos⟩

/-- The head-side mirror of `exists_tail_collapse`. -/
theorem exists_head_collapse (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (a : Fin n) (e : Fin p) :
    ∃ s ≤ (w.plan a.val).tailSlack.getD e.val 0,
      s ≤ (w.blockList a.val e.val).length - 1 ∧
      w.pointValue x a.val e.val ((w.blockList a.val e.val).length - s) =
        eval (coordForm e.val) x ∧
      (∀ i, 1 ≤ i → i < (w.blockList a.val e.val).length - s →
        w.pointValue x a.val e.val i ≠ eval (coordForm e.val) x) ∧
      w.rawChipMassAt x e.val (eval (coordForm e.val) x) =
        w.headChipSum a.val e.val s := by
  classical
  set k := (w.blockList a.val e.val).length with hk
  set ω := (w.plan a.val).tailSlack.getD e.val 0 with hω
  set L := eval (coordForm e.val) x with hL
  have hLength : ∀ j < k, 0 ≤ w.blockLengthValue x a.val e.val j := fun j hj =>
    w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e j hj
  have hLast : w.pointValue x a.val e.val k = L :=
    w.pointValue_last_eq_coord_of_w1Checks core Γ x hW1 a e
  have hLe : ∀ i ≤ k, w.pointValue x a.val e.val i ≤ L := by
    intro i hi
    have hmono := w.pointValue_mono_of_lengths x a.val e.val k hLength hi le_rfl
    omega
  -- the number of named points which have reached the head
  set Q : ℕ → Prop := fun t => w.pointValue x a.val e.val (k - t) = L with hQ
  have hQ0 : Q 0 := by simpa [hQ] using hLast
  set s := Nat.findGreatest Q (k - 1) with hs
  have hsle : s ≤ k - 1 := Nat.findGreatest_le _
  have hQs : Q s := Nat.findGreatest_spec (Nat.zero_le _) hQ0
  have hhead : ∀ i, k - s ≤ i → i ≤ k - 1 → w.pointValue x a.val e.val i = L := by
    intro i hi hik
    have hmono := w.pointValue_mono_of_lengths x a.val e.val k hLength hi
      (by omega)
    have hks : w.pointValue x a.val e.val (k - s) = L := hQs
    have := hLe i (by omega)
    omega
  have hlow : ∀ i, 1 ≤ i → i < k - s → w.pointValue x a.val e.val i ≠ L := by
    intro i hi1 hiks hEq
    have hQi : Q (k - i) := by
      have : k - (k - i) = i := by omega
      simpa [hQ, this] using hEq
    have := Nat.le_findGreatest (show k - i ≤ k - 1 by omega) hQi
    omega
  -- W1's head slack receipt bounds the realized suffix by the declared slack
  have hslack : s ≤ ω := by
    by_cases hbranch : 1 ≤ k - 1 - ω
    · have hW1' := hW1
      simp only [w1Checks, ExplicitPotential.allFin_eq_true_iff,
        Bool.and_eq_true] at hW1'
      have hclause := (hW1' a e).2
      rw [ite_eq_left (by simpa [hk, hω] using hbranch)] at hclause
      have hstrict : 0 < eval (subForm (coordForm e.val)
          (w.point a.val e.val (k - 1 - ω))) x := positiveCheck_sound hclause hx
      rw [eval_subForm] at hstrict
      have hval : w.pointValue x a.val e.val (k - 1 - ω) < L := by
        simp only [pointValue]
        omega
      by_contra hnot
      have hksω : k - s ≤ k - 1 - ω := by omega
      have hmono := w.pointValue_mono_of_lengths x a.val e.val k hLength hksω
        (by omega)
      have hks : w.pointValue x a.val e.val (k - s) = L := hQs
      omega
    · omega
  exact ⟨s, hslack, hsle, hQs, hlow,
    w.rawChipMassAt_length_eq_headChipSum core hW3 x a e s L hsle hhead hlow⟩

/-- A zero-length displayed slot carries no raw chips *on that slot* in an
accepted rich leaf.  This is the zero-slot half of the W5 endpoint accounting:
its two physical endpoints are the same quotient-core vertex, so the tail and
head mass must not be added.  W1 makes the two maximal collapsed runs exhaust
the named points; its `α + ω + 1 ≤ k` discipline then forces `k = 1`, and W3
has no interior named index at which a chip could occur. -/
theorem no_chip_on_coord_eq_zero (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hn : 0 < n) (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (e : Fin p) (hcoord : eval (coordForm e.val) x = 0) :
    ∀ chip ∈ w.chips, chip.1 ≠ e.val := by
  classical
  let a : Fin n := ⟨0, hn⟩
  let k := (w.blockList a.val e.val).length
  let α := (w.plan a.val).headSlack.getD e.val 0
  let ω := (w.plan a.val).tailSlack.getD e.val 0
  have hLength : ∀ j < k, 0 ≤ w.blockLengthValue x a.val e.val j := fun j hj =>
    w.blockLength_nonneg_of_w1Checks core Γ x hW1 hx a e j (by simpa [k] using hj)
  have hLast : w.pointValue x a.val e.val k = 0 := by
    rw [w.pointValue_last_eq_coord_of_w1Checks core Γ x hW1 a e]
    exact hcoord
  have hAllZero : ∀ i ≤ k, w.pointValue x a.val e.val i = 0 := by
    intro i hi
    have hnonneg := w.pointValue_nonneg_of_lengths x a.val e.val k i hLength hi
    have hle := w.pointValue_le_of_lengths_last x a.val e.val k 0 i hLength hLast hi
    omega
  obtain ⟨sT, hsTα, hsTle, -, hsTmax, -⟩ :=
    w.exists_tail_collapse core Γ x hW1 hW3 hx a e
  have hsT : sT = k - 1 := by
    apply Nat.le_antisymm hsTle
    by_contra hnot
    have hlt : sT < k - 1 := Nat.lt_of_not_ge hnot
    exact hsTmax (k - 1) hlt (le_refl _) (hAllZero _ (by omega))
  obtain ⟨sH, hsHω, hsHle, -, hsHlow, -⟩ :=
    w.exists_head_collapse core Γ x hW1 hW3 hx a e
  have hsH : sH = k - 1 := by
    apply Nat.le_antisymm hsHle
    by_contra hnot
    have hlt : sH < k - 1 := Nat.lt_of_not_ge hnot
    have hk1 : 1 < k - sH := by omega
    exact hsHlow 1 (by omega) hk1 (by simpa [hcoord] using hAllZero 1 (by omega))
  have hW1' := hW1
  simp only [w1Checks, ExplicitPotential.allFin_eq_true_iff,
    Bool.and_eq_true] at hW1'
  have hdiscipline : α + ω + 1 ≤ k := by
    exact decide_eq_true_eq.mp (by simpa [α, ω, k] using (hW1' a e).1.1.1.1.2)
  have hk : k = 1 := by
    have hsTα' : sT ≤ α := by simpa [α] using hsTα
    have hsHω' : sH ≤ ω := by simpa [ω] using hsHω
    rw [hsT] at hsTα'
    rw [hsH] at hsHω'
    omega
  intro chip hchip hslot
  obtain ⟨i, hi, -⟩ := w.chip_named_of_w3Checks core hW3 a hchip
  rw [hslot] at hi
  change i < k - 1 at hi
  rw [hk] at hi
  omega

/-- Consequently each physical endpoint mass of a zero-length displayed slot
is zero.  This is the form used when one endpoint contribution is retained
and the other is omitted in the quotient-core W5 sum. -/
theorem rawChipMassAt_eq_zero_of_coord_eq_zero (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hn : 0 < n) (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (e : Fin p) (hcoord : eval (coordForm e.val) x = 0)
    (coordinate : ℤ) :
    w.rawChipMassAt x e.val coordinate = 0 := by
  have hnone := w.no_chip_on_coord_eq_zero core Γ x hn hW1 hW3 hx e hcoord
  unfold rawChipMassAt
  have hmap :
      w.chips.map (fun chip =>
        if chip.1 == e.val && eval chip.2.1 x == coordinate then chip.2.2 else 0) =
      w.chips.map (fun _ => 0) := by
    apply List.map_congr_left
    intro chip hchip
    have hslot : chip.1 ≠ e.val := hnone chip hchip
    simp [hslot]
  rw [hmap]
  simp

/-! ## The W5 endpoint comparisons

Composing the bridge with `minOver_le_candidate` gives the two inequalities
in the shape `RichW5Aggregation.w5ActualResidual_class_nonneg` consumes, with
the *actual* endpoint contribution still written as the physical chip mass
plus (resp. minus) the declared slope bound of the first surviving (resp. last
surviving) block.  Only the slope comparison — W2's `lo ≤ actual ≤ hi` on that
block — remains between these and the closed-face endpoint contributions. -/

/-- W5's conservative tail contribution is dominated by the physical chip mass
at the tail plus the declared lower slope bound of the first block which
survives the collapse.  The returned index `s` is the last named point that
has fallen into the tail. -/
theorem exists_tailContribution_le (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (a : Fin n) (e : Fin p) :
    ∃ s ≤ (w.blockList a.val e.val).length - 1,
      w.pointValue x a.val e.val s = 0 ∧
      (∀ i, s < i → i ≤ (w.blockList a.val e.val).length - 1 →
        w.pointValue x a.val e.val i ≠ 0) ∧
      w.tailContribution a.val e.val ≤
        w.rawChipMassAt x e.val 0 + (w.block a.val e.val s).lo := by
  obtain ⟨s, hslack, hsle, hzero, hmax, hbridge⟩ :=
    w.exists_tail_collapse core Γ x hW1 hW3 hx a e
  refine ⟨s, hsle, hzero, hmax, ?_⟩
  rw [hbridge]
  exact w.tailContribution_le_candidate a.val e.val s hslack

/-- The head-side mirror of `exists_tailContribution_le`.  Here
`(w.blockList a e).length - s` is the first named point that has reached the
head, and `(w.blockList a e).length - 1 - s` indexes the last surviving
block. -/
theorem exists_headContribution_le (w : RichWitness)
    (core : ExplicitPotential.Core n p) (Γ : Context) (x : List ℤ)
    (hW1 : w.w1Checks core Γ = true) (hW3 : w.w3Checks core = true)
    (hx : Γ.Holds x) (a : Fin n) (e : Fin p) :
    ∃ s ≤ (w.blockList a.val e.val).length - 1,
      w.pointValue x a.val e.val ((w.blockList a.val e.val).length - s) =
        eval (coordForm e.val) x ∧
      (∀ i, 1 ≤ i → i < (w.blockList a.val e.val).length - s →
        w.pointValue x a.val e.val i ≠ eval (coordForm e.val) x) ∧
      w.headContribution a.val e.val ≤
        w.rawChipMassAt x e.val (eval (coordForm e.val) x) -
          (w.block a.val e.val ((w.blockList a.val e.val).length - 1 - s)).hi := by
  obtain ⟨s, hslack, hsle, hhead, hlow, hbridge⟩ :=
    w.exists_head_collapse core Γ x hW1 hW3 hx a e
  refine ⟨s, hsle, hhead, hlow, ?_⟩
  rw [hbridge, ← w.headCandidate_eq_headChipSum_sub a.val e.val s]
  exact w.headContribution_le_candidate a.val e.val s hslack

end RichWitness

end Utilities.Subdivision.ClosedRowProof
