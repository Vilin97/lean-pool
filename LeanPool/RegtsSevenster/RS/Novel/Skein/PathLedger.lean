/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.RepairInvariance
import LeanPool.RegtsSevenster.RS.Novel.Skein.ChainAgreement

/-!
# The path ledger for the repair move

The corrected per-move target for Proposition 3: the
path-sign-weighted constrained summand
`pathSign κ * throughSummand … o κ.openCircuitCount` under one
elementary repair move.  The `RepairInvariance` ledger
handles the summand factor; this file supplies the `pathSign`
factor and the case analysis that controls it.

## Main results

* `third_chord_reparity` — **the third-chord parity lemma** (chord
  combinatorics, self-contained): re-pairing four fixed points of a
  linear order into chords in any two ways changes the number of
  crossings with any third chord by an even amount.
* `chain_meet` — **chain rigidity**: two boundary-terminated chains
  sharing a walk flag have the same starting boundary flag (walks
  are forward- and backward-deterministic).
* `pathMatch_repair_of_avoid` — a chain whose pairing arguments
  avoid the four flags of the square walks identically in the
  repaired system.
* `periodicFlag_pairing` / `periodicFlag_match` — the periodic
  flags are closed under the edge pairing and the matching.
* `pathMatch_repair_of_periodic` — **case 1**: a square on periodic
  (circuit) components leaves every path matching unchanged.
* `pathMatch_repair_of_chainLocal` — **cases 2–3**: a square whose
  four flags are each periodic or on the chain of one boundary flag
  `β` leaves every path matching unchanged — untouched chains avoid
  the square by rigidity, and the two ends of `β`'s chain must
  re-pair with each other because `pathMatch` remains a
  fixed-point-free involution (`pathMatch_ne_self`).
* `pathSign_congr` / `pathSign_matchEq` — the crossing sign only
  depends on the path matching, so it is unchanged in cases 1–3 and
  invariant under `MatchEq`.
* `RelTransitionSystem.Orientation.flipOrbit` and
  `throughSummand_flipOrbit` — reversing one whole circuit, and the
  summand's invariance under doing so.
* `SeparatedCountParity` and `NonSeparatedStep` — the two per-case
  hypotheses the move analysis is stated over, discharged in
  `SeparatedParity.lean` and `NonSeparatedStep.lean` respectively.
-/

namespace RS



/-! ## (i) Chord combinatorics: the third-chord parity lemma -/

section ChordParity

variable {γ : Type*}

/-- Two chords of a linear order, each recorded low-to-high,
interleave (in either relative position). -/
def ChordPairCross [LinearOrder γ]
    (x y u w : γ) : Prop :=
  (x < u ∧ u < y ∧ y < w) ∨ (u < x ∧ x < w ∧ w < y)

/-- A point lies strictly inside a chord. -/
def InsideChord [LinearOrder γ]
    (x y p : γ) : Prop := x < p ∧ p < y

/-- Crossing a chord is interleaving: exactly one endpoint inside. -/
theorem chordPairCross_iff_xor [LinearOrder γ]
    {x y u w : γ}
    (huw : u < w) (hux : u ≠ x) (hwy : w ≠ y) :
    ChordPairCross x y u w ↔
      Xor (InsideChord x y u) (InsideChord x y w) := by
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exact Or.inl ⟨⟨h1, h2⟩, fun hw => absurd h3 (not_lt.mpr (le_of_lt hw.2))⟩
    · exact Or.inr ⟨⟨h2, h3⟩, fun hu => absurd h1 (not_lt.mpr (le_of_lt hu.1))⟩
  · rintro (⟨⟨hu1, hu2⟩, hnw⟩ | ⟨⟨hw1, hw2⟩, hnu⟩)
    · have hxw : x < w := lt_trans hu1 huw
      have hyw : y ≤ w := by
        by_contra hcon
        exact hnw ⟨hxw, not_le.mp hcon⟩
      exact Or.inl ⟨hu1, hu2, lt_of_le_of_ne hyw (Ne.symm hwy)⟩
    · have huy : u < y := lt_trans huw hw2
      have hux' : u ≤ x := by
        by_contra hcon
        exact hnu ⟨not_le.mp hcon, huy⟩
      exact Or.inr ⟨lt_of_le_of_ne hux' hux, hw1, hw2⟩

/-- The crossing indicator of one chord has the parity of the
number of its endpoints inside the third chord. -/
theorem chordPairCross_parity [LinearOrder γ]
    {x y u w : γ}
    (huw : u < w) (hux : u ≠ x) (hwy : w ≠ y) :
    (if ChordPairCross x y u w then 1 else 0) % 2 =
      ((if InsideChord x y u then 1 else 0) +
        (if InsideChord x y w then 1 else 0)) % 2 := by
  by_cases hu : InsideChord x y u <;> by_cases hw : InsideChord x y w
  · have hnX : ¬ ChordPairCross x y u w := by
      rw [chordPairCross_iff_xor huw hux hwy]
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact h hw
      · exact h hu
    rw [ite_eq_right hnX, ite_eq_left hu, ite_eq_left hw]
  · have hX : ChordPairCross x y u w := by
      rw [chordPairCross_iff_xor huw hux hwy]
      exact Or.inl ⟨hu, hw⟩
    rw [ite_eq_left hX, ite_eq_left hu, ite_eq_right hw]
  · have hX : ChordPairCross x y u w := by
      rw [chordPairCross_iff_xor huw hux hwy]
      exact Or.inr ⟨hw, hu⟩
    rw [ite_eq_left hX, ite_eq_right hu, ite_eq_left hw]
  · have hnX : ¬ ChordPairCross x y u w := by
      rw [chordPairCross_iff_xor huw hux hwy]
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hu h
      · exact hw h
    rw [ite_eq_right hnX, ite_eq_right hu, ite_eq_right hw]

private theorem inside_sum_eq [LinearOrder γ]
    (x y u₁ w₁ u₂ w₂ : γ) :
    (({u₁, w₁, u₂, w₂} : Multiset γ).map
        (fun p => if InsideChord x y p then 1 else 0)).sum =
      (if InsideChord x y u₁ then 1 else 0) +
        ((if InsideChord x y w₁ then 1 else 0) +
          ((if InsideChord x y u₂ then 1 else 0) +
            (if InsideChord x y w₂ then 1 else 0))) := by
  simp only [Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton]

/-- **The third-chord parity lemma**: re-pairing the same four
points of a linear order into two chords in any two ways (the same
multiset of endpoints, each chord recorded low-to-high, no endpoint
shared with the third chord) preserves the parity of the number of
crossings with the third chord. -/
theorem third_chord_reparity [LinearOrder γ]
    {x y u₁ w₁ u₂ w₂ p₁ q₁ p₂ q₂ : γ}
    (h₁ : u₁ < w₁) (h₂ : u₂ < w₂)
    (h₁' : p₁ < q₁) (h₂' : p₂ < q₂)
    (hmul : ({u₁, w₁, u₂, w₂} : Multiset γ) = {p₁, q₁, p₂, q₂})
    (hne : ∀ p ∈ ({u₁, w₁, u₂, w₂} : Multiset γ), p ≠ x ∧ p ≠ y) :
    ((if ChordPairCross x y u₁ w₁ then 1 else 0) +
        (if ChordPairCross x y u₂ w₂ then 1 else 0)) % 2 =
      ((if ChordPairCross x y p₁ q₁ then 1 else 0) +
        (if ChordPairCross x y p₂ q₂ then 1 else 0)) % 2 := by
  have hne' : ∀ p ∈ ({p₁, q₁, p₂, q₂} : Multiset γ), p ≠ x ∧ p ≠ y := by
    rw [← hmul]; exact hne
  have e₁ := chordPairCross_parity (x := x) (y := y) h₁
    (hne u₁ (by simp)).1 (hne w₁ (by simp)).2
  have e₂ := chordPairCross_parity (x := x) (y := y) h₂
    (hne u₂ (by simp)).1 (hne w₂ (by simp)).2
  have e₁' := chordPairCross_parity (x := x) (y := y) h₁'
    (hne' p₁ (by simp)).1 (hne' q₁ (by simp)).2
  have e₂' := chordPairCross_parity (x := x) (y := y) h₂'
    (hne' p₂ (by simp)).1 (hne' q₂ (by simp)).2
  have hsum : (({u₁, w₁, u₂, w₂} : Multiset γ).map
        (fun p => if InsideChord x y p then 1 else 0)).sum =
      (({p₁, q₁, p₂, q₂} : Multiset γ).map
        (fun p => if InsideChord x y p then 1 else 0)).sum := by
    rw [hmul]
  rw [inside_sum_eq, inside_sum_eq] at hsum
  omega

end ChordParity

/-! ## (ii) Walk rigidity -/

namespace EdgeSubset

variable {α : Type} {W : Fragment α}

section WalkRigidity

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}

/-- The exit step of a boundary-terminated chain is unique. -/
theorem chain_exit_unique {β : W.Flag} {k k' : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ β j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ β k) ∈ F.boundaryFlags)
    (hcont' : ∀ j, j < k' →
      W.pairing (iterWalk κ β j) ∈ F.internalFlags)
    (hterm' : W.pairing (iterWalk κ β k') ∈ F.boundaryFlags) :
    k = k' := by
  rcases Nat.lt_trichotomy k k' with h | h | h
  · exact absurd hterm
      (Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags (hcont' k h) ·)
  · exact h
  · exact absurd hterm'
      (Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags (hcont k' h) ·)

/-- **Chain rigidity**: the walk is forward- and
backward-deterministic, so two boundary-terminated chains sharing a
walk flag start at the same boundary flag, at the same step. -/
theorem chain_meet {β β' : W.Flag} (hβ : β ∈ F.boundaryFlags)
    (hβ' : β' ∈ F.boundaryFlags) {k k' : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ β j) ∈ F.internalFlags)
    (hcont' : ∀ j, j < k' →
      W.pairing (iterWalk κ β' j) ∈ F.internalFlags) :
    ∀ t s, t ≤ k' → s ≤ k → iterWalk κ β' t = iterWalk κ β s →
      β' = β ∧ t = s := by
  intro t
  induction t with
  | zero =>
    intro s _ hs heq
    cases s with
    | zero =>
      rw [iterWalk_zero, iterWalk_zero] at heq
      exact ⟨heq, rfl⟩
    | succ s =>
      exfalso
      have hint : iterWalk κ β (s + 1) ∈ F.internalFlags :=
        iterWalk_mem_internal κ k (by omega) hs hcont
      rw [← heq, iterWalk_zero] at hint
      exact Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hint hβ'
  | succ t ih =>
    intro s ht hs heq
    cases s with
    | zero =>
      exfalso
      have hint : iterWalk κ β' (t + 1) ∈ F.internalFlags :=
        iterWalk_mem_internal κ k' (by omega) ht hcont'
      rw [heq, iterWalk_zero] at hint
      exact Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hint hβ
    | succ s =>
      have hm : κ.match_ (W.pairing (iterWalk κ β' t)) =
          κ.match_ (W.pairing (iterWalk κ β s)) := by
        rw [← iterWalk_succ, ← iterWalk_succ]
        exact heq
      have hargs : W.pairing (iterWalk κ β' t) =
          W.pairing (iterWalk κ β s) :=
        κ.match_injOn (hcont' t (by omega)) (hcont s (by omega)) hm
      have hEq : iterWalk κ β' t = iterWalk κ β s := by
        have h2 := congrArg W.pairing hargs
        rwa [W.pairing_invol, W.pairing_invol] at h2
      obtain ⟨h1, h2⟩ := ih s (by omega) (by omega) hEq
      exact ⟨h1, by omega⟩

end WalkRigidity

/-! ## Walk transfer under square avoidance -/

section RepairAvoid

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}
  {a b c d : W.Flag} {v : W.Vertex}

/-- A walk whose pairing arguments avoid the four flags of the
square is untouched by the repair. -/
theorem repair_iterWalk_of_avoid (hsq : RepairSquare κ a b c d v)
    {δ : W.Flag} {k : ℕ}
    (havoid : ∀ t, t < k →
      W.pairing (iterWalk κ δ t) ≠ a ∧
      W.pairing (iterWalk κ δ t) ≠ b ∧
      W.pairing (iterWalk κ δ t) ≠ c ∧
      W.pairing (iterWalk κ δ t) ≠ d) :
    ∀ t, t ≤ k →
      iterWalk (κ.repair a b c d v hsq) δ t = iterWalk κ δ t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    obtain ⟨h1, h2, h3, h4⟩ := havoid t (by omega)
    rw [iterWalk_succ, ih (by omega), iterWalk_succ,
      RelTransitionSystem.repair_match_of_ne hsq h1 h2 h3 h4]

/-- The path matching is untouched at a boundary flag whose chain
avoids the square. -/
theorem pathMatch_repair_of_avoid (hsq : RepairSquare κ a b c d v)
    {δ : W.Flag} (hδ : δ ∈ F.boundaryFlags) {k : ℕ}
    (hk : k ≤ F.flags.card)
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ δ j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ δ k) ∈ F.boundaryFlags)
    (havoid : ∀ t, t < k →
      W.pairing (iterWalk κ δ t) ≠ a ∧
      W.pairing (iterWalk κ δ t) ≠ b ∧
      W.pairing (iterWalk κ δ t) ≠ c ∧
      W.pairing (iterWalk κ δ t) ≠ d) :
    (κ.repair a b c d v hsq).pathMatch δ hδ = κ.pathMatch δ hδ := by
  have hwalk := repair_iterWalk_of_avoid hsq havoid
  have hcont' : ∀ j, j < k →
      W.pairing (iterWalk (κ.repair a b c d v hsq) δ j) ∈
        F.internalFlags := by
    intro j hj
    rw [hwalk j (by omega)]
    exact hcont j hj
  have hterm' : W.pairing (iterWalk (κ.repair a b c d v hsq) δ k) ∈
      F.boundaryFlags := by
    rw [hwalk k le_rfl]
    exact hterm
  have h1 : (κ.repair a b c d v hsq).pathMatch δ hδ =
      W.pairing (iterWalk (κ.repair a b c d v hsq) δ k) :=
    (κ.repair a b c d v hsq).pathMatch_eq hδ
      (traceChain_fuel_mono _ (by omega)
        (traceChain_forward _ δ hcont' hterm'))
  have h2 : κ.pathMatch δ hδ = W.pairing (iterWalk κ δ k) :=
    κ.pathMatch_eq hδ
      (traceChain_fuel_mono κ (by omega)
        (traceChain_forward κ δ hcont hterm))
  rw [h1, h2, hwalk k le_rfl]

end RepairAvoid

/-! ## Closure of the periodic flags -/

section PeriodicClosure

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}

/-- The edge pairing of a periodic flag is periodic (the reversed
traversal of its circuit). -/
theorem periodicFlag_pairing {f : W.Flag} (hf : κ.PeriodicFlag f) :
    κ.PeriodicFlag (W.pairing f) := by
  obtain ⟨hint, n, hn1, hcont, hper⟩ := hf
  have hf' : κ.PeriodicFlag f := ⟨hint, n, hn1, hcont, hper⟩
  have hrev : ∀ j, j ≤ n →
      iterWalk κ (W.pairing f) j = W.pairing (iterWalk κ f (n - j)) := by
    intro j hj
    have h := iterWalk_reverse κ hcont j hj
    rwa [hper] at h
  refine ⟨by simpa using hcont 0 (by omega), n, hn1, ?_, ?_⟩
  · intro j hj
    rw [hrev j (by omega), W.pairing_invol]
    exact iterWalk_mem_internal_of_periodic κ hf' (n - j) (by omega)
  · rw [hrev n le_rfl, Nat.sub_self, iterWalk_zero]

/-- The matching image of a periodic flag is periodic. -/
theorem periodicFlag_match {f : W.Flag} (hf : κ.PeriodicFlag f) :
    κ.PeriodicFlag (κ.match_ f) := by
  have hp : κ.PeriodicFlag (W.pairing f) := periodicFlag_pairing hf
  have h1 : iterWalk κ (W.pairing f) 1 = κ.match_ f := by
    rw [iterWalk_succ, iterWalk_zero, W.pairing_invol]
  rw [← h1]
  exact periodicFlag_iterWalk κ hp 1

/-- No boundary chain hits a periodic flag in its pairing-argument
position: chains are non-periodic. -/
theorem chain_arg_ne_of_periodic {δ f : W.Flag}
    (hδ : δ ∈ F.boundaryFlags) {kδ : ℕ}
    (hcontδ : ∀ j, j < kδ →
      W.pairing (iterWalk κ δ j) ∈ F.internalFlags)
    (htermδ : W.pairing (iterWalk κ δ kδ) ∈ F.boundaryFlags)
    (hper : κ.PeriodicFlag f) {s : ℕ} (hs : s < kδ) :
    W.pairing (iterWalk κ δ s) ≠ f := by
  intro heq
  have h2 : iterWalk κ δ s = W.pairing f := by
    have h3 := congrArg W.pairing heq
    rwa [W.pairing_invol] at h3
  have hpp : κ.PeriodicFlag (W.pairing f) := periodicFlag_pairing hper
  cases s with
  | zero =>
    rw [iterWalk_zero] at h2
    refine Finset.disjoint_left.mp
      F.internalFlags_disjoint_boundaryFlags ?_ hδ
    rw [h2]
    exact hpp.mem_internal
  | succ s =>
    have hnp := not_periodic_of_chain_segment κ hcontδ htermδ
      (by omega : 1 ≤ s + 1) (by omega : s + 1 ≤ kδ)
    rw [h2] at hnp
    exact hnp hpp

end PeriodicClosure

/-! ## Avoidance of a foreign chain -/

section ChainAvoid

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}

/-- A chain distinct from `β` and from `β`'s far end never hits a
flag of `β`'s chain in its pairing-argument position. -/
theorem chain_arg_ne_of_onChain {β δ f : W.Flag}
    (hβ : β ∈ F.boundaryFlags) (hδ : δ ∈ F.boundaryFlags) {k : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ β j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ β k) ∈ F.boundaryFlags)
    {kδ : ℕ}
    (hcontδ : ∀ j, j < kδ →
      W.pairing (iterWalk κ δ j) ∈ F.internalFlags)
    (hδβ : δ ≠ β) (hδγ : δ ≠ W.pairing (iterWalk κ β k))
    {t : ℕ} (ht : t ≤ k)
    (hf : f = iterWalk κ β t ∨ f = W.pairing (iterWalk κ β t))
    {s : ℕ} (hs : s < kδ) :
    W.pairing (iterWalk κ δ s) ≠ f := by
  intro heq
  have hcontγ : ∀ j, j < k →
      W.pairing (iterWalk κ (W.pairing (iterWalk κ β k)) j) ∈
        F.internalFlags :=
    fun j hj => reverse_chain_continues κ hβ hcont j hj
  rcases hf with rfl | rfl
  · -- `f` is a walk-side flag of `β`'s chain: land on the reverse
    -- chain from the far end and apply rigidity.
    have h3 : iterWalk κ δ s = W.pairing (iterWalk κ β t) := by
      have h4 := congrArg W.pairing heq
      rwa [W.pairing_invol] at h4
    have h5 : iterWalk κ (W.pairing (iterWalk κ β k)) (k - t) =
        W.pairing (iterWalk κ β t) := by
      rw [iterWalk_reverse κ hcont (k - t) (by omega),
        show k - (k - t) = t from by omega]
    have h6 : iterWalk κ δ s =
        iterWalk κ (W.pairing (iterWalk κ β k)) (k - t) :=
      h3.trans h5.symm
    exact hδγ (chain_meet hterm hδ hcontγ hcontδ s (k - t)
      (by omega) (by omega) h6).1
  · -- `f` is a pairing-side flag of `β`'s chain: rigidity directly.
    have h3 : iterWalk κ δ s = iterWalk κ β t := by
      have h4 := congrArg W.pairing heq
      rwa [W.pairing_invol, W.pairing_invol] at h4
    exact hδβ (chain_meet hβ hδ hcont hcontδ s t
      (by omega) (by omega) h3).1

end ChainAvoid

/-! ## Membership on a boundary chain -/

section OnChain

variable {F : EdgeSubset W}

/-- Membership on the boundary chain of `β`: the flag appears on
the walk from `β` (on either side of an edge) before the chain
exits. -/
def OnBoundaryChain (κ : F.RelTransitionSystem) (β f : W.Flag) :
    Prop :=
  ∃ k t : ℕ, t ≤ k ∧
    (∀ j, j < k → W.pairing (iterWalk κ β j) ∈ F.internalFlags) ∧
    W.pairing (iterWalk κ β k) ∈ F.boundaryFlags ∧
    (f = iterWalk κ β t ∨ f = W.pairing (iterWalk κ β t))

variable {κ : F.RelTransitionSystem}

/-- The chain membership is closed under the matching (on internal
flags). -/
theorem onBoundaryChain_match {β f : W.Flag}
    (hβ : β ∈ F.boundaryFlags) (hf : f ∈ F.internalFlags)
    (h : OnBoundaryChain κ β f) :
    OnBoundaryChain κ β (κ.match_ f) := by
  obtain ⟨k, t, htk, hcont, hterm, hft⟩ := h
  rcases hft with rfl | rfl
  · -- walk-side: `match (iterWalk β t) = pairing (iterWalk β (t-1))`
    cases t with
    | zero =>
      exfalso
      rw [iterWalk_zero] at hf
      exact Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hf hβ
    | succ t =>
      refine ⟨k, t, by omega, hcont, hterm, Or.inr ?_⟩
      have h1 : iterWalk κ β (t + 1) =
          κ.match_ (W.pairing (iterWalk κ β t)) := iterWalk_succ κ β t
      rw [h1, κ.match_invol _ (hcont t (by omega))]
  · -- pairing-side: `match (pairing (iterWalk β t)) = iterWalk β (t+1)`
    have htne : t ≠ k := by
      intro hEq
      subst hEq
      exact Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hf hterm
    refine ⟨k, t + 1, by omega, hcont, hterm, Or.inl ?_⟩
    exact (iterWalk_succ κ β t).symm

end OnChain

/-! ## Case 1: squares on circuits -/

section PeriodicSquare

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}
  {a b c d : W.Flag} {v : W.Vertex}

/-- **Case 1**: a square on periodic (circuit) components leaves
every path matching unchanged. -/
theorem pathMatch_repair_of_periodic (hsq : RepairSquare κ a b c d v)
    (hpa : κ.PeriodicFlag a) (hpc : κ.PeriodicFlag c) :
    ∀ δ (hδ : δ ∈ F.boundaryFlags),
      (κ.repair a b c d v hsq).pathMatch δ hδ = κ.pathMatch δ hδ := by
  have hpb : κ.PeriodicFlag b := hsq.hab ▸ periodicFlag_match hpa
  have hpd : κ.PeriodicFlag d := hsq.hcd ▸ periodicFlag_match hpc
  intro δ hδ
  obtain ⟨kδ, hkδ, hcontδ, htermδ⟩ := chain_terminates_with_data κ hδ
  refine pathMatch_repair_of_avoid hsq hδ hkδ hcontδ htermδ ?_
  intro s hs
  exact ⟨chain_arg_ne_of_periodic hδ hcontδ htermδ hpa hs,
    chain_arg_ne_of_periodic hδ hcontδ htermδ hpb hs,
    chain_arg_ne_of_periodic hδ hcontδ htermδ hpc hs,
    chain_arg_ne_of_periodic hδ hcontδ htermδ hpd hs⟩

end PeriodicSquare

/-! ## Cases 2–3: squares localized to one chain -/

section ChainLocalSquare

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}
  {a b c d : W.Flag} {v : W.Vertex}

/-- **Cases 2–3**: a square whose four flags are each periodic or on
the chain of one boundary flag `β` leaves every path matching
unchanged.  Untouched chains avoid the square by rigidity
(`chain_meet`); the two ends of `β`'s chain must then re-pair with
each other, because the repaired path matching is a fixed-point-free
involution and every other boundary end is already taken. -/
theorem pathMatch_repair_of_chainLocal (hsq : RepairSquare κ a b c d v)
    {β : W.Flag} (hβ : β ∈ F.boundaryFlags)
    (hloc : ∀ f, f = a ∨ f = b ∨ f = c ∨ f = d →
      κ.PeriodicFlag f ∨ OnBoundaryChain κ β f) :
    ∀ δ (hδ : δ ∈ F.boundaryFlags),
      (κ.repair a b c d v hsq).pathMatch δ hδ = κ.pathMatch δ hδ := by
  obtain ⟨k, hkle, hcont, hterm⟩ := chain_terminates_with_data κ hβ
  have hγpm : κ.pathMatch β hβ = W.pairing (iterWalk κ β k) :=
    κ.pathMatch_eq hβ (traceChain_fuel_mono κ (by omega)
      (traceChain_forward κ β hcont hterm))
  -- normalize the chain positions to the canonical exit step
  have hloc' : ∀ f, f = a ∨ f = b ∨ f = c ∨ f = d →
      κ.PeriodicFlag f ∨
        ∃ t ≤ k, f = iterWalk κ β t ∨
          f = W.pairing (iterWalk κ β t) := by
    intro f hf
    rcases hloc f hf with hper | ⟨k', t, htk', hcont', hterm', hft⟩
    · exact Or.inl hper
    · have hkk : k' = k := chain_exit_unique hcont' hterm' hcont hterm
      subst hkk
      exact Or.inr ⟨t, htk', hft⟩
  -- untouched chains: avoidance by rigidity
  have hA : ∀ δ (hδ : δ ∈ F.boundaryFlags), δ ≠ β →
      δ ≠ W.pairing (iterWalk κ β k) →
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ := by
    intro δ hδ hδβ hδγ
    obtain ⟨kδ, hkδ, hcontδ, htermδ⟩ :=
      chain_terminates_with_data κ hδ
    refine pathMatch_repair_of_avoid hsq hδ hkδ hcontδ htermδ ?_
    intro s hs
    have hne : ∀ f, f = a ∨ f = b ∨ f = c ∨ f = d →
        W.pairing (iterWalk κ δ s) ≠ f := by
      intro f hf
      rcases hloc' f hf with hper | ⟨t, htk, hft⟩
      · exact chain_arg_ne_of_periodic hδ hcontδ htermδ hper hs
      · exact chain_arg_ne_of_onChain hβ hδ hcont hterm hcontδ
          hδβ hδγ htk hft hs
    exact ⟨hne a (Or.inl rfl), hne b (Or.inr (Or.inl rfl)),
      hne c (Or.inr (Or.inr (Or.inl rfl))),
      hne d (Or.inr (Or.inr (Or.inr rfl)))⟩
  -- the affected chain: its two ends re-pair with each other
  have hB : (κ.repair a b c d v hsq).pathMatch β hβ =
      W.pairing (iterWalk κ β k) := by
    by_contra hne
    have hδmem : (κ.repair a b c d v hsq).pathMatch β hβ ∈
        F.boundaryFlags := (κ.repair a b c d v hsq).pathMatch_mem hβ
    have hδβ : (κ.repair a b c d v hsq).pathMatch β hβ ≠ β :=
      (κ.repair a b c d v hsq).pathMatch_ne_self hβ
    have h1 := hA _ hδmem hδβ hne
    have h2 : (κ.repair a b c d v hsq).pathMatch
        ((κ.repair a b c d v hsq).pathMatch β hβ) hδmem = β :=
      (κ.repair a b c d v hsq).pathMatch_invol hβ
    have h3 : κ.pathMatch ((κ.repair a b c d v hsq).pathMatch β hβ)
        hδmem = β := h1.symm.trans h2
    have h4 : κ.pathMatch β hβ =
        (κ.repair a b c d v hsq).pathMatch β hβ :=
      calc κ.pathMatch β hβ
          = κ.pathMatch (κ.pathMatch
              ((κ.repair a b c d v hsq).pathMatch β hβ) hδmem)
              (κ.pathMatch_mem hδmem) :=
            κ.pathMatch_congr h3.symm hβ _
        _ = (κ.repair a b c d v hsq).pathMatch β hβ :=
            κ.pathMatch_invol hδmem
    exact hne (h4.symm.trans hγpm)
  -- the reverse end
  have hγmem : W.pairing (iterWalk κ β k) ∈ F.boundaryFlags := hterm
  have hγpm' : κ.pathMatch (W.pairing (iterWalk κ β k)) hγmem = β :=
    calc κ.pathMatch (W.pairing (iterWalk κ β k)) hγmem
        = κ.pathMatch (κ.pathMatch β hβ) (κ.pathMatch_mem hβ) :=
          κ.pathMatch_congr hγpm.symm hγmem _
      _ = β := κ.pathMatch_invol hβ
  have hC : (κ.repair a b c d v hsq).pathMatch
      (W.pairing (iterWalk κ β k)) hγmem = β := by
    have h5 := (κ.repair a b c d v hsq).pathMatch_congr hB.symm hγmem
      ((κ.repair a b c d v hsq).pathMatch_mem hβ)
    exact h5.trans ((κ.repair a b c d v hsq).pathMatch_invol hβ)
  intro δ hδ
  by_cases h1 : δ = β
  · subst h1
    exact hB.trans hγpm.symm
  · by_cases h2 : δ = W.pairing (iterWalk κ β k)
    · subst h2
      exact hC.trans hγpm'.symm
    · exact hA δ hδ h1 h2

end ChainLocalSquare

/-! ## The localized case predicate -/

section Localized

variable {F : EdgeSubset W}

/-- The square is **localized** (cases 1–3 of the path ledger): the
two re-paired edges lie on periodic components, or each of the four
flags is periodic or on the chain of a single boundary flag.  The
complement is the genuine two-path case (case 4). -/
def SquareLocalized (κ : F.RelTransitionSystem)
    (a b c d : W.Flag) : Prop :=
  (κ.PeriodicFlag a ∧ κ.PeriodicFlag c) ∨
    ∃ β, β ∈ F.boundaryFlags ∧
      ∀ f, f = a ∨ f = b ∨ f = c ∨ f = d →
        κ.PeriodicFlag f ∨ OnBoundaryChain κ β f

variable {κ : F.RelTransitionSystem} {a b c d : W.Flag}
  {v : W.Vertex}

/-- **(ii) pathMatch invariance in cases 1–3**: a localized square
leaves every path matching unchanged. -/
theorem pathMatch_repair_of_localized (hsq : RepairSquare κ a b c d v)
    (hloc : SquareLocalized κ a b c d) :
    ∀ δ (hδ : δ ∈ F.boundaryFlags),
      (κ.repair a b c d v hsq).pathMatch δ hδ = κ.pathMatch δ hδ := by
  rcases hloc with ⟨hpa, hpc⟩ | ⟨β, hβ, hlocal⟩
  · exact pathMatch_repair_of_periodic hsq hpa hpc
  · exact pathMatch_repair_of_chainLocal hsq hβ hlocal

end Localized

/-! ## The crossing sign under pathMatch-preserving moves -/

section ChordCongr

/-- The chord-interleaving relation only depends on the path
matching. -/
theorem chordCross_congr [LinearOrder α] {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (hpm : ∀ δ (hδ : δ ∈ F.boundaryFlags),
      κ'.pathMatch δ hδ = κ.pathMatch δ hδ)
    (b b' : {x : W.Flag // x ∈ F.boundaryFlags}) :
    ChordCross κ' b b' ↔ ChordCross κ b b' := by
  unfold ChordCross
  rw [hpm b.val b.prop, hpm b'.val b'.prop]

/-- The chord-crossing count only depends on the path matching. -/
theorem chordCrossingCount_congr [LinearOrder α] {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (hpm : ∀ δ (hδ : δ ∈ F.boundaryFlags),
      κ'.pathMatch δ hδ = κ.pathMatch δ hδ) :
    chordCrossingCount κ' = chordCrossingCount κ := by
  unfold chordCrossingCount
  exact congrArg Finset.card
    (Finset.filter_congr
      (fun bb _ => chordCross_congr hpm bb.1 bb.2))

/-- The path sign only depends on the path matching. -/
theorem pathSign_congr [LinearOrder α] {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    (hpm : ∀ δ (hδ : δ ∈ F.boundaryFlags),
      κ'.pathMatch δ hδ = κ.pathMatch δ hδ) :
    pathSign κ' = pathSign κ := by
  unfold pathSign
  rw [chordCrossingCount_congr hpm]

end ChordCongr

/-! ## The MatchEq layer for the path sign -/

section MatchEqPath

variable {F : EdgeSubset W}

/-- Matching-equal systems have equal path matchings. -/
theorem pathMatch_matchEq {κ₁ κ₂ : F.RelTransitionSystem}
    (heq : κ₁.MatchEq κ₂) {δ : W.Flag}
    (hδ : δ ∈ F.boundaryFlags) :
    κ₂.pathMatch δ hδ = κ₁.pathMatch δ hδ := by
  obtain ⟨k, hk, hcont, hterm⟩ := chain_terminates_with_data κ₁ hδ
  have hwalk : ∀ t, t ≤ k → iterWalk κ₂ δ t = iterWalk κ₁ δ t := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [iterWalk_succ, iterWalk_succ, ih (by omega),
        ← heq _ (hcont t (by omega))]
  have hcont' : ∀ j, j < k →
      W.pairing (iterWalk κ₂ δ j) ∈ F.internalFlags := by
    intro j hj
    rw [hwalk j (by omega)]
    exact hcont j hj
  have hterm' : W.pairing (iterWalk κ₂ δ k) ∈ F.boundaryFlags := by
    rw [hwalk k le_rfl]
    exact hterm
  have h1 : κ₂.pathMatch δ hδ = W.pairing (iterWalk κ₂ δ k) :=
    κ₂.pathMatch_eq hδ
      (traceChain_fuel_mono κ₂ (by omega)
        (traceChain_forward κ₂ δ hcont' hterm'))
  have h2 : κ₁.pathMatch δ hδ = W.pairing (iterWalk κ₁ δ k) :=
    κ₁.pathMatch_eq hδ
      (traceChain_fuel_mono κ₁ (by omega)
        (traceChain_forward κ₁ δ hcont hterm))
  rw [h1, h2, hwalk k le_rfl]

/-- Matching-equal systems have equal chord-crossing counts. -/
theorem chordCrossingCount_matchEq [LinearOrder α]
    {κ₁ κ₂ : F.RelTransitionSystem} (heq : κ₁.MatchEq κ₂) :
    chordCrossingCount κ₂ = chordCrossingCount κ₁ :=
  chordCrossingCount_congr (fun _ hδ => pathMatch_matchEq heq hδ)

/-- Matching-equal systems have equal path signs. -/
theorem pathSign_matchEq [LinearOrder α]
    {κ₁ κ₂ : F.RelTransitionSystem} (heq : κ₁.MatchEq κ₂) :
    pathSign κ₂ = pathSign κ₁ :=
  pathSign_congr (fun _ hδ => pathMatch_matchEq heq hδ)

end MatchEqPath

/-! ## Classification: periodic, one chain, or two chains -/

section Classification

/-- Every internal flag is periodic or lies on the chain of some
boundary flag. -/
theorem periodic_or_onBoundaryChain {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    {f : W.Flag} (hf : f ∈ F.internalFlags) :
    κ.PeriodicFlag f ∨
      ∃ β ∈ F.boundaryFlags, OnBoundaryChain κ β f := by
  rcases internal_periodic_or_terminates κ f hf with hper | hterm
  · exact Or.inl hper
  · right
    obtain ⟨fuel, b0, hchain⟩ := hterm
    obtain ⟨kf, hcontf, hexitf, hb0⟩ :=
      traceChain_some_exit κ fuel f b0 hchain
    have hβ : W.pairing (iterWalk κ f kf) ∈ F.boundaryFlags := by
      rw [hexitf]; exact hb0
    have hcontb : ∀ t, t ≤ kf →
        W.pairing (iterWalk κ (W.pairing (iterWalk κ f kf)) t) ∈
          F.internalFlags := by
      intro t ht
      rw [iterWalk_reverse κ hcontf t ht, W.pairing_invol]
      rcases Nat.lt_or_ge t kf with h | h
      · exact iterWalk_mem_internal κ kf (by omega) (by omega)
          hcontf
      · rw [show kf - t = 0 from by omega, iterWalk_zero]
        exact hf
    obtain ⟨k', hk'le, hcont', hterm'⟩ :=
      chain_terminates_with_data κ hβ
    have hk'gt : kf < k' := by
      by_contra hle
      exact Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags
        (hcontb k' (by omega)) hterm'
    have hfeq :
        W.pairing (iterWalk κ (W.pairing (iterWalk κ f kf)) kf) =
          f := reverse_chain_terminates κ hcontf
    exact ⟨W.pairing (iterWalk κ f kf), hβ,
      k', kf, by omega, hcont', hterm', Or.inr hfeq.symm⟩

/-- Chain membership from the far end of a chain is chain membership
from the near end. -/
theorem onBoundaryChain_of_reverse
    {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {β f : W.Flag}
    (hβ : β ∈ F.boundaryFlags) {k : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ β j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ β k) ∈ F.boundaryFlags)
    (h : OnBoundaryChain κ (W.pairing (iterWalk κ β k)) f) :
    OnBoundaryChain κ β f := by
  obtain ⟨kγ, t, htk, hcontγ, htermγ, hft⟩ := h
  have hcontγ' : ∀ j, j < k →
      W.pairing (iterWalk κ (W.pairing (iterWalk κ β k)) j) ∈
        F.internalFlags :=
    fun j hj => reverse_chain_continues κ hβ hcont j hj
  have htermγ' :
      W.pairing (iterWalk κ (W.pairing (iterWalk κ β k)) k) ∈
        F.boundaryFlags := by
    rw [reverse_chain_terminates κ hcont]
    exact hβ
  have hkk : kγ = k := chain_exit_unique hcontγ htermγ hcontγ' htermγ'
  subst hkk
  have hrev := iterWalk_reverse κ hcont t htk
  refine ⟨kγ, kγ - t, by omega, hcont, hterm, ?_⟩
  rcases hft with rfl | rfl
  · exact Or.inr hrev
  · refine Or.inl ?_
    rw [hrev, W.pairing_invol]

/-- **The two-path classification**: a non-localized square has its
two re-paired edges on two genuinely distinct boundary chains. -/
theorem twoChains_of_not_localized
    {F : EdgeSubset W} {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag}
    {c : W.Flag} {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v)
    (hnl : ¬ SquareLocalized κ a b c d) :
    ∃ (β₁ β₂ : W.Flag) (hβ₁ : β₁ ∈ F.boundaryFlags)
      (_hβ₂ : β₂ ∈ F.boundaryFlags),
      OnBoundaryChain κ β₁ a ∧ OnBoundaryChain κ β₂ c ∧
      β₂ ≠ β₁ ∧ β₂ ≠ κ.pathMatch β₁ hβ₁ := by
  rcases periodic_or_onBoundaryChain κ hsq.ha with
    hpa | ⟨β₁, hβ₁, hca⟩
  · rcases periodic_or_onBoundaryChain κ hsq.hc with
      hpc | ⟨β₂, hβ₂, hcc⟩
    · exact absurd (Or.inl ⟨hpa, hpc⟩) hnl
    · exfalso
      refine hnl (Or.inr ⟨β₂, hβ₂, ?_⟩)
      intro f hf
      rcases hf with rfl | rfl | rfl | rfl
      · exact Or.inl hpa
      · exact Or.inl (hsq.hab ▸ periodicFlag_match hpa)
      · exact Or.inr hcc
      · exact Or.inr
          (hsq.hcd ▸ onBoundaryChain_match hβ₂ hsq.hc hcc)
  · rcases periodic_or_onBoundaryChain κ hsq.hc with
      hpc | ⟨β₂, hβ₂, hcc⟩
    · exfalso
      refine hnl (Or.inr ⟨β₁, hβ₁, ?_⟩)
      intro f hf
      rcases hf with rfl | rfl | rfl | rfl
      · exact Or.inr hca
      · exact Or.inr
          (hsq.hab ▸ onBoundaryChain_match hβ₁ hsq.ha hca)
      · exact Or.inl hpc
      · exact Or.inl (hsq.hcd ▸ periodicFlag_match hpc)
    · by_cases h12 : β₂ = β₁
      · subst h12
        exfalso
        refine hnl (Or.inr ⟨β₂, hβ₂, ?_⟩)
        intro f hf
        rcases hf with rfl | rfl | rfl | rfl
        · exact Or.inr hca
        · exact Or.inr
            (hsq.hab ▸ onBoundaryChain_match hβ₂ hsq.ha hca)
        · exact Or.inr hcc
        · exact Or.inr
            (hsq.hcd ▸ onBoundaryChain_match hβ₂ hsq.hc hcc)
      · by_cases h1γ : β₂ = κ.pathMatch β₁ hβ₁
        · exfalso
          obtain ⟨k, hkle, hcont, hterm⟩ :=
            chain_terminates_with_data κ hβ₁
          have hγ : κ.pathMatch β₁ hβ₁ =
              W.pairing (iterWalk κ β₁ k) :=
            κ.pathMatch_eq hβ₁ (traceChain_fuel_mono κ (by omega)
              (traceChain_forward κ β₁ hcont hterm))
          have hcc' : OnBoundaryChain κ β₁ c := by
            refine onBoundaryChain_of_reverse hβ₁ hcont hterm ?_
            rw [← hγ, ← h1γ]
            exact hcc
          refine hnl (Or.inr ⟨β₁, hβ₁, ?_⟩)
          intro f hf
          rcases hf with rfl | rfl | rfl | rfl
          · exact Or.inr hca
          · exact Or.inr
              (hsq.hab ▸ onBoundaryChain_match hβ₁ hsq.ha hca)
          · exact Or.inr hcc'
          · exact Or.inr
              (hsq.hcd ▸ onBoundaryChain_match hβ₁ hsq.hc hcc')
        · exact ⟨β₁, β₂, hβ₁, hβ₂, hca, hcc, h12, h1γ⟩

end Classification

/-! ## Circuit flips: orbit-supported orientation gauges -/

section OrbitFlip

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}

/-- The flags of the walk orbit through `g`, on both sides of each
visited edge. -/
def OrbitFlag (κ : F.RelTransitionSystem) (g f : W.Flag) : Prop :=
  ∃ m, f = iterWalk κ g m ∨ f = W.pairing (iterWalk κ g m)

/-- A flag lies on its own orbit. -/
theorem orbitFlag_self (κ : F.RelTransitionSystem) (g : W.Flag) :
    OrbitFlag κ g g := ⟨0, Or.inl rfl⟩

/-- Orbits are closed under the edge pairing. -/
theorem orbitFlag_pairing {g f : W.Flag} (hf : OrbitFlag κ g f) :
    OrbitFlag κ g (W.pairing f) := by
  obtain ⟨m, rfl | rfl⟩ := hf
  · exact ⟨m, Or.inr rfl⟩
  · exact ⟨m, Or.inl (W.pairing_invol _)⟩

/-- And under it backwards. -/
theorem orbitFlag_of_pairing {g f : W.Flag}
    (h : OrbitFlag κ g (W.pairing f)) : OrbitFlag κ g f := by
  have h2 := orbitFlag_pairing h
  rwa [W.pairing_invol] at h2

/-- Every flag on a periodic flag's orbit is internal: a closed
circuit never reaches the boundary. -/
theorem orbitFlag_internal {g f : W.Flag} (hg : κ.PeriodicFlag g)
    (hf : OrbitFlag κ g f) : f ∈ F.internalFlags := by
  obtain ⟨m, rfl | rfl⟩ := hf
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [iterWalk_zero]
      exact hg.mem_internal
    · exact iterWalk_mem_internal_of_periodic κ hg m hm
  · exact all_pairings_internal_of_periodic κ hg m

/-- So is each such flag's edge partner. -/
theorem orbitFlag_pairing_internal {g f : W.Flag}
    (hg : κ.PeriodicFlag g) (hf : OrbitFlag κ g f) :
    W.pairing f ∈ F.internalFlags :=
  orbitFlag_internal hg (orbitFlag_pairing hf)

/-- A periodic orbit is closed under the matching. -/
theorem orbitFlag_match {g f : W.Flag} (hg : κ.PeriodicFlag g)
    (hf : OrbitFlag κ g f) : OrbitFlag κ g (κ.match_ f) := by
  obtain ⟨hgint, n, hn1, hcont, hper⟩ := hg
  have hg' : κ.PeriodicFlag g := ⟨hgint, n, hn1, hcont, hper⟩
  obtain ⟨m, rfl | rfl⟩ := hf
  · have hshift : iterWalk κ g (n + m) = iterWalk κ g m :=
      iterWalk_add_period κ g n m hper hcont
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, n + m = m₀ + 1 := ⟨n + m - 1, by omega⟩
    have hmm : κ.match_ (iterWalk κ g m) =
        W.pairing (iterWalk κ g m₀) := by
      rw [← hshift, hm₀, iterWalk_succ]
      exact κ.match_invol _
        (all_pairings_internal_of_periodic κ hg' m₀)
    rw [hmm]
    exact ⟨m₀, Or.inr rfl⟩
  · have hmm : κ.match_ (W.pairing (iterWalk κ g m)) =
        iterWalk κ g (m + 1) := (iterWalk_succ κ g m).symm
    rw [hmm]
    exact ⟨m + 1, Or.inl rfl⟩

/-- And under it backwards. -/
theorem orbitFlag_of_match {g f : W.Flag} (hg : κ.PeriodicFlag g)
    (hf : f ∈ F.internalFlags) (h : OrbitFlag κ g (κ.match_ f)) :
    OrbitFlag κ g f := by
  have h2 := orbitFlag_match hg h
  rwa [κ.match_invol f hf] at h2

open Classical in
/-- Flip an orientation on the walk orbit of a periodic flag: a
circuit-supported orientation gauge. -/
noncomputable def RelTransitionSystem.Orientation.flipOrbit
    (o : κ.Orientation) {g : W.Flag} (hg : κ.PeriodicFlag g) :
    κ.Orientation where
  isOut f := if OrbitFlag κ g f then !o.isOut f else o.isOut f
  match_flip := by
    intro f hf
    show (if OrbitFlag κ g (κ.match_ f) then !o.isOut (κ.match_ f)
        else o.isOut (κ.match_ f)) =
      !(if OrbitFlag κ g f then !o.isOut f else o.isOut f)
    by_cases hfo : OrbitFlag κ g f
    · rw [ite_eq_left (orbitFlag_match hg hfo), ite_eq_left hfo,
        o.match_flip f hf]
    · rw [ite_eq_right (fun hcon => hfo (orbitFlag_of_match hg hf hcon)),
        ite_eq_right hfo]
      exact o.match_flip f hf
  pairing_flip := by
    intro f hf hp
    show (if OrbitFlag κ g (W.pairing f) then !o.isOut (W.pairing f)
        else o.isOut (W.pairing f)) =
      !(if OrbitFlag κ g f then !o.isOut f else o.isOut f)
    by_cases hfo : OrbitFlag κ g f
    · rw [ite_eq_left (orbitFlag_pairing hfo), ite_eq_left hfo,
        o.pairing_flip f hf hp]
    · rw [ite_eq_right (fun hcon => hfo (orbitFlag_of_pairing hcon)),
        ite_eq_right hfo]
      exact o.pairing_flip f hf hp

/-- Flipping an orbit reverses the orientation on it. -/
theorem flipOrbit_isOut_of_mem (o : κ.Orientation) {g : W.Flag}
    (hg : κ.PeriodicFlag g) {f : W.Flag} (hf : OrbitFlag κ g f) :
    (o.flipOrbit hg).isOut f = !o.isOut f := by
  change (if OrbitFlag κ g f then !o.isOut f else o.isOut f) =
    !o.isOut f
  exact ite_eq_left hf

/-- And leaves it alone elsewhere. -/
theorem flipOrbit_isOut_of_notMem (o : κ.Orientation) {g : W.Flag}
    (hg : κ.PeriodicFlag g) {f : W.Flag} (hf : ¬ OrbitFlag κ g f) :
    (o.flipOrbit hg).isOut f = o.isOut f := by
  change (if OrbitFlag κ g f then !o.isOut f else o.isOut f) =
    o.isOut f
  exact ite_eq_right hf

/-- An orbit flip is a circuit-supported gauge, so the constrained
summand is invariant under it: the difference is supported on
closed circuits. -/
theorem throughSummand_flipOrbit [LinearOrder α] {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (o : κ.Orientation) {g : W.Flag} (hg : κ.PeriodicFlag g)
    (c : ℕ) :
    F.throughSummand hM st hbnd (o.flipOrbit hg) c =
      F.throughSummand hM st hbnd o c := by
  refine throughSummand_orientation_invariant F hM st hbnd _ o
    (fun f hf hne => ?_) c
  by_cases hfo : OrbitFlag κ g f
  · exact orbitFlag_pairing_internal hg hfo
  · exact absurd (flipOrbit_isOut_of_notMem o hg hfo) hne

end OrbitFlip

end EdgeSubset

/-! ## The per-move interface and its inputs -/

/-- **The count-parity hypothesis (cases 1–3)**: a separated
square on a localized configuration flips the circuit-count parity
(the splice merges two circuits, Δ = −1, or splits one component,
Δ = +1).  Discharged in `SeparatedParity.lean`. -/
def SeparatedCountParity : Prop :=
  ∀ {α : Type} {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a b c d : W.Flag} {v : W.Vertex}
    (hsq : EdgeSubset.RepairSquare κ a b c d v) (o : κ.Orientation),
    o.isOut c = !o.isOut a →
    EdgeSubset.SquareLocalized κ a b c d →
    Odd (κ.openCircuitCount +
      (κ.repair a b c d v hsq).openCircuitCount)

/-- **The flipped-segment hypothesis (non-separated moves)**: a
non-separated square (`isOut c = isOut a`) admits an
orientation on the repaired system realizing the same
pathSign-weighted summand.  The structure: the repaired walk
reverses a segment (Δ = 0), the transported orientation flips on
the reversed segment, and the vertex transposition (−1) cancels
against the segment-reversal telescope (+1 total).  Discharged in
`NonSeparatedStep.lean`. -/
def NonSeparatedStep : Prop :=
  ∀ {α : Type} [LinearOrder α] {W : Fragment α} (F : EdgeSubset W)
    {k ℓ : ℕ} (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} {a b c d : W.Flag} {v : W.Vertex}
    (hsq : EdgeSubset.RepairSquare κ a b c d v) (o : κ.Orientation),
    o.isOut c = o.isOut a →
    ∃ o' : (κ.repair a b c d v hsq).Orientation,
      EdgeSubset.pathSign (κ.repair a b c d v hsq) *
          F.throughSummand hM st hbnd o'
            ((κ.repair a b c d v hsq).openCircuitCount) =
        EdgeSubset.pathSign κ *
          F.throughSummand hM st hbnd o κ.openCircuitCount

end RS
