/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.RelTransition

/-!
# The elementary re-pairing move on relative transition systems

For a fixed edge subset `F : EdgeSubset W`, this file introduces the
elementary *2-opt move* on boundary-relative transition systems and
proves that the moves connect any two systems.

## Main definitions

* `EdgeSubset.repairFun` — the raw re-pairing of a matching function
  at four flags: `a ↦ c`, `c ↦ a`, `b ↦ d`, `d ↦ b`.
* `EdgeSubset.RepairSquare` — the admissibility data for a move:
  four pairwise distinct internal flags at a common vertex with
  `a ↔ b` and `c ↔ d` matched.
* `EdgeSubset.RelTransitionSystem.repair` — the elementary move,
  producing a transition system over the *same* `F` (so the edge
  subset, its `internalFlags`, and its `boundaryFlags` are untouched
  by construction).
* `EdgeSubset.RelTransitionSystem.MatchEq` — matching equality on
  internal flags; two systems whose matchings agree on
  `F.internalFlags` are indistinguishable to every field of
  `RelTransitionSystem`, so connectivity is stated up to `MatchEq`.
* `EdgeSubset.IsRepairStep` — one elementary move (up to `MatchEq`).
* `EdgeSubset.disagreeSet` — the internal flags where two systems'
  matchings differ.

## Main results

* `EdgeSubset.repair_connectivity` — **connectivity**: any two
  relative transition systems on `F` are joined by a finite chain of
  elementary moves, with `MatchEq` at the endpoints.  The proof is by
  induction on `(disagreeSet κ κ').card`: a disagreement at `a`
  yields an admissible square (`repairSquare_of_disagree`) whose
  repair strictly shrinks the disagreement set
  (`disagreeSet_repair_subset`).
* `EdgeSubset.IsRepairStep.symm` — the move is reversible, so chains
  can be traversed backwards.
* `EdgeSubset.RelTransitionSystem.Orientation.ofMatchEq` and
  `…Orientation.transportRepair` — orientation transport across
  `MatchEq` and (conditionally) across a move.

## Orientation transport along a matching equality

`Orientation.transportRepair` transports an orientation across a
repair when it already separates `a` from `c`
(`o.isOut c = !o.isOut a`): the directions carry over unchanged.
When instead `o.isOut c = o.isOut a` the transported orientation
must flip `isOut` along the walk-orbit segment through `c`, which
needs the orbit machinery; that construction is
`Orientation.segFlip` in `NonSeparatedStep.lean`, with
`Orientation.flipOrbit` of `PathLedger.lean` for a periodic
segment.
-/

namespace RS



variable {α : Type}

namespace EdgeSubset

variable {W : Fragment α} {F : EdgeSubset W}

/-! ## The raw re-pairing function -/

/-- Re-pair a matching function at four flags: `a ↦ c`, `c ↦ a`,
`b ↦ d`, `d ↦ b`, leaving every other flag to `m`. -/
def repairFun (m : W.Flag → W.Flag) (a b c d : W.Flag) :
    W.Flag → W.Flag := fun f =>
  if f = a then c else if f = c then a else
    if f = b then d else if f = d then b else m f

section RepairFun

variable {m m' : W.Flag → W.Flag} {a b c d f : W.Flag}

/-- The re-pairing sends `a` to `c`. -/
theorem repairFun_a : repairFun m a b c d a = c := by
  simp [repairFun]

/-- And `c` back to `a`. -/
theorem repairFun_c (h : c ≠ a) : repairFun m a b c d c = a := by
  simp [repairFun, h]

/-- It sends `b` to `d`. -/
theorem repairFun_b (h1 : b ≠ a) (h2 : b ≠ c) :
    repairFun m a b c d b = d := by
  simp [repairFun, h1, h2]

/-- And `d` back to `b`. -/
theorem repairFun_d (h1 : d ≠ a) (h2 : d ≠ c) (h3 : d ≠ b) :
    repairFun m a b c d d = b := by
  simp [repairFun, h1, h2, h3]

/-- Away from the four flags the matching is untouched: the move is
local. -/
theorem repairFun_of_ne (h1 : f ≠ a) (h2 : f ≠ b) (h3 : f ≠ c)
    (h4 : f ≠ d) : repairFun m a b c d f = m f := by
  simp [repairFun, h1, h2, h3, h4]

/-- The re-paired function depends on the underlying matching only
through its value at the argument. -/
theorem repairFun_congr (hm : m f = m' f) :
    repairFun m a b c d f = repairFun m' a b c d f := by
  unfold repairFun
  split_ifs <;> first | rfl | exact hm

end RepairFun

/-! ## Admissibility data for a move -/

/-- The data of an admissible 2-opt re-pairing move on
`κ : F.RelTransitionSystem`: four pairwise distinct internal flags
`a, b, c, d` attached to a common vertex `v`, with `a ↔ b` and
`c ↔ d` matched by `κ`.  (The distinctness facts `a ≠ b` and `c ≠ d`
are derivable from `match_ne` and are not recorded.) -/
structure RepairSquare (κ : F.RelTransitionSystem)
    (a b c d : W.Flag) (v : W.Vertex) : Prop where
  ha : a ∈ F.internalFlags
  hc : c ∈ F.internalFlags
  hab : κ.match_ a = b
  hcd : κ.match_ c = d
  hac : a ≠ c
  had : a ≠ d
  hbc : b ≠ c
  hbd : b ≠ d
  hav : W.attach a = Sum.inl v
  hcv : W.attach c = Sum.inl v

namespace RepairSquare

variable {κ : F.RelTransitionSystem} {a b c d : W.Flag} {v : W.Vertex}

/-- `b` is internal. -/
theorem hb (h : RepairSquare κ a b c d v) : b ∈ F.internalFlags := by
  rw [← h.hab]; exact κ.match_mem a h.ha

/-- `d` is internal. -/
theorem hd (h : RepairSquare κ a b c d v) : d ∈ F.internalFlags := by
  rw [← h.hcd]; exact κ.match_mem c h.hc

/-- `b ≠ a`. -/
theorem hba (h : RepairSquare κ a b c d v) : b ≠ a := by
  rw [← h.hab]; exact κ.match_ne a h.ha

/-- `d ≠ c`. -/
theorem hdc (h : RepairSquare κ a b c d v) : d ≠ c := by
  rw [← h.hcd]; exact κ.match_ne c h.hc

/-- `κ` matches `b` back to `a`. -/
theorem hmb (h : RepairSquare κ a b c d v) : κ.match_ b = a := by
  rw [← h.hab]; exact κ.match_invol a h.ha

/-- `κ` matches `d` back to `c`. -/
theorem hmd (h : RepairSquare κ a b c d v) : κ.match_ d = c := by
  rw [← h.hcd]; exact κ.match_invol c h.hc

/-- `b` sits at the common vertex. -/
theorem hbv (h : RepairSquare κ a b c d v) :
    W.attach b = Sum.inl v := by
  rw [← h.hab]; exact κ.match_vertex a h.ha v h.hav

/-- `d` sits at the common vertex. -/
theorem hdv (h : RepairSquare κ a b c d v) :
    W.attach d = Sum.inl v := by
  rw [← h.hcd]; exact κ.match_vertex c h.hc v h.hcv

/-- The `κ`-partner of a flag off the square stays off the square. -/
theorem match_ne_four (h : RepairSquare κ a b c d v) {f : W.Flag}
    (hf : f ∈ F.internalFlags) (h1 : f ≠ a) (h2 : f ≠ b)
    (h3 : f ≠ c) (h4 : f ≠ d) :
    κ.match_ f ≠ a ∧ κ.match_ f ≠ b ∧ κ.match_ f ≠ c ∧
      κ.match_ f ≠ d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he
    apply h2
    calc f = κ.match_ (κ.match_ f) := (κ.match_invol f hf).symm
      _ = κ.match_ a := by rw [he]
      _ = b := h.hab
  · intro he
    apply h1
    calc f = κ.match_ (κ.match_ f) := (κ.match_invol f hf).symm
      _ = κ.match_ b := by rw [he]
      _ = a := h.hmb
  · intro he
    apply h4
    calc f = κ.match_ (κ.match_ f) := (κ.match_invol f hf).symm
      _ = κ.match_ c := by rw [he]
      _ = d := h.hcd
  · intro he
    apply h3
    calc f = κ.match_ (κ.match_ f) := (κ.match_invol f hf).symm
      _ = κ.match_ d := by rw [he]
      _ = c := h.hmd

end RepairSquare

/-! ## The elementary move -/

namespace RelTransitionSystem

/-- **The elementary move (2-opt re-pairing)**: given an admissible
square (`a ↔ b`, `c ↔ d` matched, all four distinct, all at vertex
`v`), the transition system matching `a ↔ c` and `b ↔ d` instead,
keeping every other matched pair.  The result is a system over the
*same* edge subset `F`. -/
def repair (κ : F.RelTransitionSystem) (a b c d : W.Flag)
    (v : W.Vertex) (h : RepairSquare κ a b c d v) :
    F.RelTransitionSystem where
  match_ := repairFun κ.match_ a b c d
  match_invol := by
    intro f hf
    by_cases h1 : f = a
    · subst h1
      rw [repairFun_a, repairFun_c (Ne.symm h.hac)]
    by_cases h3 : f = c
    · subst h3
      rw [repairFun_c (Ne.symm h.hac), repairFun_a]
    by_cases h2 : f = b
    · subst h2
      rw [repairFun_b h.hba h.hbc,
        repairFun_d (Ne.symm h.had) h.hdc (Ne.symm h.hbd)]
    by_cases h4 : f = d
    · subst h4
      rw [repairFun_d (Ne.symm h.had) h.hdc (Ne.symm h.hbd),
        repairFun_b h.hba h.hbc]
    · obtain ⟨n1, n2, n3, n4⟩ := h.match_ne_four hf h1 h2 h3 h4
      rw [repairFun_of_ne h1 h2 h3 h4, repairFun_of_ne n1 n2 n3 n4]
      exact κ.match_invol f hf
  match_ne := by
    intro f hf
    by_cases h1 : f = a
    · subst h1; rw [repairFun_a]; exact Ne.symm h.hac
    by_cases h3 : f = c
    · subst h3; rw [repairFun_c (Ne.symm h.hac)]; exact h.hac
    by_cases h2 : f = b
    · subst h2; rw [repairFun_b h.hba h.hbc]; exact Ne.symm h.hbd
    by_cases h4 : f = d
    · subst h4
      rw [repairFun_d (Ne.symm h.had) h.hdc (Ne.symm h.hbd)]
      exact h.hbd
    · rw [repairFun_of_ne h1 h2 h3 h4]; exact κ.match_ne f hf
  match_mem := by
    intro f hf
    by_cases h1 : f = a
    · subst h1; rw [repairFun_a]; exact h.hc
    by_cases h3 : f = c
    · subst h3; rw [repairFun_c (Ne.symm h.hac)]; exact h.ha
    by_cases h2 : f = b
    · subst h2; rw [repairFun_b h.hba h.hbc]; exact h.hd
    by_cases h4 : f = d
    · subst h4
      rw [repairFun_d (Ne.symm h.had) h.hdc (Ne.symm h.hbd)]
      exact h.hb
    · rw [repairFun_of_ne h1 h2 h3 h4]; exact κ.match_mem f hf
  match_vertex := by
    intro f hf w hw
    by_cases h1 : f = a
    · subst h1
      rw [h.hav] at hw
      rw [repairFun_a, ← Sum.inl.inj hw]
      exact h.hcv
    by_cases h3 : f = c
    · subst h3
      rw [h.hcv] at hw
      rw [repairFun_c (Ne.symm h.hac), ← Sum.inl.inj hw]
      exact h.hav
    by_cases h2 : f = b
    · subst h2
      rw [h.hbv] at hw
      rw [repairFun_b h.hba h.hbc, ← Sum.inl.inj hw]
      exact h.hdv
    by_cases h4 : f = d
    · subst h4
      rw [h.hdv] at hw
      rw [repairFun_d (Ne.symm h.had) h.hdc (Ne.symm h.hbd),
        ← Sum.inl.inj hw]
      exact h.hbv
    · rw [repairFun_of_ne h1 h2 h3 h4]
      exact κ.match_vertex f hf w hw

section RepairEval

variable {κ : F.RelTransitionSystem} {a b c d f : W.Flag} {v : W.Vertex}

/-- The repaired system's matching at `a`. -/
@[simp] theorem repair_match_a (h : RepairSquare κ a b c d v) :
    (κ.repair a b c d v h).match_ a = c := repairFun_a

/-- At `c`. -/
@[simp] theorem repair_match_c (h : RepairSquare κ a b c d v) :
    (κ.repair a b c d v h).match_ c = a := repairFun_c (Ne.symm h.hac)

/-- At `b`. -/
@[simp] theorem repair_match_b (h : RepairSquare κ a b c d v) :
    (κ.repair a b c d v h).match_ b = d := repairFun_b h.hba h.hbc

/-- At `d`. -/
@[simp] theorem repair_match_d (h : RepairSquare κ a b c d v) :
    (κ.repair a b c d v h).match_ d = b :=
  repairFun_d (Ne.symm h.had) h.hdc (Ne.symm h.hbd)

/-- And everywhere else, unchanged. -/
theorem repair_match_of_ne (h : RepairSquare κ a b c d v)
    (h1 : f ≠ a) (h2 : f ≠ b) (h3 : f ≠ c) (h4 : f ≠ d) :
    (κ.repair a b c d v h).match_ f = κ.match_ f :=
  repairFun_of_ne h1 h2 h3 h4

end RepairEval

/-! ## Matching equality -/

/-- Two relative transition systems agree when their matchings agree
on the internal flags.  All fields of `RelTransitionSystem` constrain
only internal flags, so `MatchEq`-related systems are
interchangeable; the matching's values off `F.internalFlags` are
junk. -/
def MatchEq (κ₁ κ₂ : F.RelTransitionSystem) : Prop :=
  ∀ f ∈ F.internalFlags, κ₁.match_ f = κ₂.match_ f

namespace MatchEq

variable {κ₁ κ₂ κ₃ : F.RelTransitionSystem}

/-- Matching equality is reflexive. -/
theorem refl (κ : F.RelTransitionSystem) : κ.MatchEq κ :=
  fun _ _ => rfl

/-- It is symmetric. -/
theorem symm (h : κ₁.MatchEq κ₂) : κ₂.MatchEq κ₁ :=
  fun f hf => (h f hf).symm

/-- It is transitive — an equivalence, so chains compose up to
it. -/
theorem trans (h : κ₁.MatchEq κ₂) (h' : κ₂.MatchEq κ₃) :
    κ₁.MatchEq κ₃ :=
  fun f hf => (h f hf).trans (h' f hf)

end MatchEq

end RelTransitionSystem

/-! ## Transport of squares and moves -/

/-- A repair square transports across matching equality. -/
theorem RepairSquare.of_matchEq {κ κ' : F.RelTransitionSystem}
    {a b c d : W.Flag} {v : W.Vertex}
    (heq : κ.MatchEq κ') (h : RepairSquare κ a b c d v) :
    RepairSquare κ' a b c d v :=
  ⟨h.ha, h.hc, (heq a h.ha).symm.trans h.hab,
    (heq c h.hc).symm.trans h.hcd, h.hac, h.had, h.hbc, h.hbd,
    h.hav, h.hcv⟩

namespace RelTransitionSystem

/-- Repairing `MatchEq`-equal systems along the same square yields
`MatchEq`-equal systems. -/
theorem repair_congr {κ κ' : F.RelTransitionSystem}
    {a b c d : W.Flag} {v : W.Vertex} (heq : κ.MatchEq κ')
    (h : RepairSquare κ a b c d v) (h' : RepairSquare κ' a b c d v) :
    (κ.repair a b c d v h).MatchEq (κ'.repair a b c d v h') :=
  fun f hf => repairFun_congr (heq f hf)

/-- **The move is an involution**: repairing back along the inverse
square recovers the original matching on internal flags. -/
theorem repair_repair {κ : F.RelTransitionSystem}
    {a b c d : W.Flag} {v : W.Vertex} (h : RepairSquare κ a b c d v)
    (h₂ : RepairSquare (κ.repair a b c d v h) a c b d v) :
    ((κ.repair a b c d v h).repair a c b d v h₂).MatchEq κ := by
  intro f hf
  by_cases h1 : f = a
  · subst h1
    rw [repair_match_a h₂, h.hab]
  by_cases h2 : f = b
  · subst h2
    rw [repair_match_c h₂, h.hmb]
  by_cases h3 : f = c
  · subst h3
    rw [repair_match_b h₂, h.hcd]
  by_cases h4 : f = d
  · subst h4
    rw [repair_match_d h₂, h.hmd]
  · rw [repair_match_of_ne h₂ h1 h3 h2 h4,
      repair_match_of_ne h h1 h2 h3 h4]

end RelTransitionSystem

/-- The inverse square: after the move, `(a, c, b, d)` is again
admissible (the move `a ↔ c`, `b ↔ d` back to `a ↔ b`, `c ↔ d`). -/
theorem RepairSquare.symm {κ : F.RelTransitionSystem}
    {a b c d : W.Flag} {v : W.Vertex} (h : RepairSquare κ a b c d v) :
    RepairSquare (κ.repair a b c d v h) a c b d v :=
  ⟨h.ha, h.hb, RelTransitionSystem.repair_match_a h,
    RelTransitionSystem.repair_match_b h,
    Ne.symm h.hba, h.had, Ne.symm h.hbc, Ne.symm h.hdc,
    h.hav, h.hbv⟩

/-! ## The elementary step relation -/

/-- One elementary move joins `κ₁` to `κ₂`: some admissible square of
`κ₁` repairs it to a system matching-equal to `κ₂`. -/
def IsRepairStep (κ₁ κ₂ : F.RelTransitionSystem) : Prop :=
  ∃ (a b c d : W.Flag) (v : W.Vertex)
    (h : RepairSquare κ₁ a b c d v),
    (κ₁.repair a b c d v h).MatchEq κ₂

/-- The step relation respects matching equality on both sides. -/
theorem IsRepairStep.congr {κ₁ κ₁' κ₂ κ₂' : F.RelTransitionSystem}
    (h1 : κ₁.MatchEq κ₁') (h2 : κ₂.MatchEq κ₂')
    (hstep : IsRepairStep κ₁ κ₂) : IsRepairStep κ₁' κ₂' := by
  obtain ⟨a, b, c, d, v, h, heq⟩ := hstep
  exact ⟨a, b, c, d, v, h.of_matchEq h1,
    ((RelTransitionSystem.repair_congr h1.symm (h.of_matchEq h1) h).trans
      heq).trans h2⟩

/-- **The step relation is symmetric**: every move can be undone by a
move, so chains of moves can be reversed. -/
theorem IsRepairStep.symm {κ₁ κ₂ : F.RelTransitionSystem}
    (hstep : IsRepairStep κ₁ κ₂) : IsRepairStep κ₂ κ₁ := by
  obtain ⟨a, b, c, d, v, h, heq⟩ := hstep
  refine ⟨a, c, b, d, v, (RepairSquare.symm h).of_matchEq heq, ?_⟩
  exact (RelTransitionSystem.repair_congr heq.symm _
    (RepairSquare.symm h)).trans
    (RelTransitionSystem.repair_repair h _)

/-! ## The disagreement set -/

/-- The internal flags at which two transition systems' matchings
disagree. -/
noncomputable def disagreeSet (κ κ' : F.RelTransitionSystem) :
    Finset W.Flag :=
  F.internalFlags.filter (fun f => κ.match_ f ≠ κ'.match_ f)

/-- Membership in the disagreement set: an internal flag the two
matchings send to different places. -/
theorem mem_disagreeSet {κ κ' : F.RelTransitionSystem} {f : W.Flag} :
    f ∈ disagreeSet κ κ' ↔
      f ∈ F.internalFlags ∧ κ.match_ f ≠ κ'.match_ f :=
  Finset.mem_filter

/-- The disagreement set is empty exactly for matching-equal
systems. -/
theorem disagreeSet_eq_empty_iff {κ κ' : F.RelTransitionSystem} :
    disagreeSet κ κ' = ∅ ↔ κ.MatchEq κ' := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h f hf
    by_contra hne
    exact h f (mem_disagreeSet.mpr ⟨hf, hne⟩)
  · intro h f hf
    obtain ⟨hfi, hfd⟩ := mem_disagreeSet.mp hf
    exact hfd (h f hfi)

/-- A disagreement at `a` yields an admissible square: with
`b := κ.match_ a`, `c := κ'.match_ a`, `d := κ.match_ c`, the four
flags are pairwise distinct internal flags at `a`'s vertex. -/
theorem repairSquare_of_disagree {κ κ' : F.RelTransitionSystem}
    {a : W.Flag} (ha : a ∈ F.internalFlags)
    (hdis : κ.match_ a ≠ κ'.match_ a) {v : W.Vertex}
    (hav : W.attach a = Sum.inl v) :
    RepairSquare κ a (κ.match_ a) (κ'.match_ a)
      (κ.match_ (κ'.match_ a)) v := by
  have hcmem : κ'.match_ a ∈ F.internalFlags := κ'.match_mem a ha
  refine ⟨ha, hcmem, rfl, rfl, ?_, ?_, hdis, ?_, hav, ?_⟩
  · exact Ne.symm (κ'.match_ne a ha)
  · -- a ≠ κ.match_ (κ'.match_ a)
    intro he
    apply hdis
    calc κ.match_ a = κ.match_ (κ.match_ (κ'.match_ a)) := by
          rw [← he]
      _ = κ'.match_ a := κ.match_invol _ hcmem
  · -- κ.match_ a ≠ κ.match_ (κ'.match_ a)
    intro he
    apply Ne.symm (κ'.match_ne a ha)
    calc a = κ.match_ (κ.match_ a) := (κ.match_invol a ha).symm
      _ = κ.match_ (κ.match_ (κ'.match_ a)) := by rw [he]
      _ = κ'.match_ a := κ.match_invol _ hcmem
  · exact κ'.match_vertex a ha v hav

/-- **Disagreement decrease**: repairing the square of a disagreement
at `a` (with `c = κ'.match_ a`) removes both `a` and `c` from the
disagreement set and adds nothing; in particular the new disagreement
set avoids `a`. -/
theorem disagreeSet_repair_subset {κ κ' : F.RelTransitionSystem}
    {a b c d : W.Flag} {v : W.Vertex} (h : RepairSquare κ a b c d v)
    (hc' : κ'.match_ a = c) :
    disagreeSet (κ.repair a b c d v h) κ' ⊆
      (disagreeSet κ κ').erase a := by
  have hca' : κ'.match_ c = a := by
    rw [← hc']; exact κ'.match_invol a h.ha
  intro f hf
  obtain ⟨hfi, hfd⟩ := mem_disagreeSet.mp hf
  rw [Finset.mem_erase, mem_disagreeSet]
  by_cases h1 : f = a
  · subst h1
    exact absurd ((RelTransitionSystem.repair_match_a h).trans
      hc'.symm) hfd
  by_cases h3 : f = c
  · subst h3
    exact absurd ((RelTransitionSystem.repair_match_c h).trans
      hca'.symm) hfd
  refine ⟨h1, hfi, ?_⟩
  by_cases h2 : f = b
  · subst h2
    rw [h.hmb]
    intro he
    have hb' : κ'.match_ a = f := by
      rw [he]; exact κ'.match_invol f h.hb
    exact h.hbc (hb'.symm.trans hc')
  by_cases h4 : f = d
  · subst h4
    rw [h.hmd]
    intro he
    have hd' : κ'.match_ c = f := by
      rw [he]; exact κ'.match_invol f h.hd
    exact h.had (hca'.symm.trans hd')
  · rw [RelTransitionSystem.repair_match_of_ne h h1 h2 h3 h4] at hfd
    exact hfd

/-! ## Connectivity -/

/-- Connectivity, with an explicit bound on the disagreement count:
strong induction on `(disagreeSet κ κ').card`. -/
theorem repair_connectivity_of_card_le (N : ℕ) :
    ∀ κ κ' : F.RelTransitionSystem, (disagreeSet κ κ').card ≤ N →
    ∃ (n : ℕ) (chain : Fin (n + 1) → F.RelTransitionSystem),
      (chain 0).MatchEq κ ∧ (chain (Fin.last n)).MatchEq κ' ∧
      ∀ r : Fin n, IsRepairStep (chain r.castSucc) (chain r.succ) := by
  induction N with
  | zero =>
    intro κ κ' hcard
    have heq : κ.MatchEq κ' :=
      disagreeSet_eq_empty_iff.mp
        (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
    exact ⟨0, fun _ => κ, RelTransitionSystem.MatchEq.refl κ, heq,
      fun r => r.elim0⟩
  | succ N ih =>
    intro κ κ' hcard
    by_cases hne : (disagreeSet κ κ').Nonempty
    · obtain ⟨a, haS⟩ := hne
      obtain ⟨hai, hdis⟩ := mem_disagreeSet.mp haS
      obtain ⟨v, hav⟩ := F.attach_internal_of_mem hai
      have hsq := repairSquare_of_disagree hai hdis hav
      have hsub := disagreeSet_repair_subset hsq rfl
      have hcard' : (disagreeSet (κ.repair a (κ.match_ a)
          (κ'.match_ a) (κ.match_ (κ'.match_ a)) v hsq) κ').card ≤
          N :=
        Nat.lt_succ_iff.mp
          (lt_of_lt_of_le
            (lt_of_le_of_lt (Finset.card_le_card hsub)
              (Finset.card_erase_lt_of_mem haS)) hcard)
      obtain ⟨n, chain, h0, hlast, hstep⟩ := ih _ κ' hcard'
      refine ⟨n + 1, Fin.cons κ chain, ?_, ?_, ?_⟩
      · rw [Fin.cons_zero]
        exact RelTransitionSystem.MatchEq.refl κ
      · rw [← Fin.succ_last, Fin.cons_succ]
        exact hlast
      · intro r
        refine Fin.cases ?_ (fun i => ?_) r
        · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
          exact ⟨a, κ.match_ a, κ'.match_ a,
            κ.match_ (κ'.match_ a), v, hsq, h0.symm⟩
        · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
          exact hstep i
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      exact ⟨0, fun _ => κ, RelTransitionSystem.MatchEq.refl κ,
        disagreeSet_eq_empty_iff.mp hne, fun r => r.elim0⟩

/-- **Connectivity of the elementary move**: any two boundary-relative
transition systems on the same edge subset are joined by a finite
chain of elementary re-pairing moves, matching-equal to the given
systems at the endpoints. -/
theorem repair_connectivity (κ κ' : F.RelTransitionSystem) :
    ∃ (n : ℕ) (chain : Fin (n + 1) → F.RelTransitionSystem),
      (chain 0).MatchEq κ ∧ (chain (Fin.last n)).MatchEq κ' ∧
      ∀ r : Fin n, IsRepairStep (chain r.castSucc) (chain r.succ) :=
  repair_connectivity_of_card_le (disagreeSet κ κ').card κ κ' le_rfl

/-! ## Orientation transport -/

namespace RelTransitionSystem

/-- Orientations transport across matching equality: an orientation
constrains `isOut` only through the matching's values on internal
flags. -/
def Orientation.ofMatchEq {κ κ' : F.RelTransitionSystem}
    (heq : κ.MatchEq κ') (o : κ.Orientation) : κ'.Orientation where
  isOut := o.isOut
  match_flip := fun f hf => by
    rw [← heq f hf]; exact o.match_flip f hf
  pairing_flip := o.pairing_flip

/-- **Orientation transport along a move (separated case)**: when the
orientation already separates `a` and `c` (`isOut c = !isOut a`), it
transports *unchanged* along the repair.  When instead
`isOut c = isOut a` the transported orientation must flip `isOut`
along a walk segment; that is `Orientation.segFlip`. -/
def Orientation.transportRepair {κ : F.RelTransitionSystem}
    {a b c d : W.Flag} {v : W.Vertex} (h : RepairSquare κ a b c d v)
    (o : κ.Orientation) (hflip : o.isOut c = !o.isOut a) :
    (κ.repair a b c d v h).Orientation where
  isOut := o.isOut
  match_flip := by
    have hb' : o.isOut b = !o.isOut a := by
      rw [← h.hab]; exact o.match_flip a h.ha
    have hd' : o.isOut d = !o.isOut c := by
      rw [← h.hcd]; exact o.match_flip c h.hc
    intro f hf
    change o.isOut (repairFun κ.match_ a b c d f) = !o.isOut f
    by_cases h1 : f = a
    · subst h1
      rw [repairFun_a]; exact hflip
    by_cases h3 : f = c
    · subst h3
      rw [repairFun_c (Ne.symm h.hac), hflip, Bool.not_not]
    by_cases h2 : f = b
    · subst h2
      rw [repairFun_b h.hba h.hbc, hd', hflip, hb', Bool.not_not]
    by_cases h4 : f = d
    · subst h4
      rw [repairFun_d (Ne.symm h.had) h.hdc (Ne.symm h.hbd),
        hb', hd', hflip, Bool.not_not]
    · rw [repairFun_of_ne h1 h2 h3 h4]
      exact o.match_flip f hf
  pairing_flip := o.pairing_flip

end RelTransitionSystem

end EdgeSubset

end RS
