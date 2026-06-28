/-
Copyright (c) 2026 consensus-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: consensus-lean contributors
-/
import Batteries

/-!
# Extracted checker — a Mathlib-free, compilable, *proved* consensus gate

`Consensus.Certificate` proves the safety property over Mathlib `Finset`s, but a
Mathlib-dependent executable forces native-compiling all of Mathlib (hours). This module
is the **extracted runtime checker**: the same decision procedure over plain `List`s,
importing only `Batteries`, so it compiles to a small native binary in seconds — and it
carries its **own** agreement proof, so the gate that actually runs *is* proved Lean code,
not a hand-port pinned by tests.

The trusted base shrinks to the (fuzzable, fail-closeable) input parser; the *decision*
is machine-checked here.
-/

namespace Consensus.Checker

/-- A vote record: each acceptor paired with the value it cast. -/
abbrev Votes := List (Nat × String)

/-- The value acceptor `x` voted, if any (first match wins). -/
def lookup : Votes → Nat → Option String
  | [], _ => none
  | (a, v) :: rest, x => if a == x then some v else lookup rest x

/-- A certificate: a claimed value and the acceptors who back it. -/
structure Cert where
  /-- The value claimed by the certificate. -/
  value : String
  /-- The acceptors backing the claimed value. -/
  voters : List Nat
  deriving DecidableEq

instance : Repr Cert where
  reprPrec c _ := "{" ++ repr c.value ++ " by " ++ repr c.voters ++ "}"

/-- The runtime check, as a `Bool` over `List`s. Faithful to `Consensus.Bridge.Valid`:
duplicate-free voters that are members, form a strict majority, and each cast the claimed
value. Total and fail-closed — malformed data simply makes a conjunct false. -/
def validB (members : List Nat) (votes : Votes) (c : Cert) : Bool :=
  decide c.voters.Nodup
    && c.voters.all (fun a => decide (a ∈ members))
    && decide (members.length < 2 * c.voters.length)
    && c.voters.all (fun a => lookup votes a == some c.value)

/-- **Counting lemma.** Two duplicate-free majority sub-lists of `members` share an
element: if they were disjoint, their combined length would exceed `members`. -/
theorem shared (members Q Q' : List Nat)
    (hQnd : Q.Nodup) (hQ'nd : Q'.Nodup)
    (hQsub : Q ⊆ members) (hQ'sub : Q' ⊆ members)
    (hQmaj : members.length < 2 * Q.length) (hQ'maj : members.length < 2 * Q'.length) :
    ∃ a, a ∈ Q ∧ a ∈ Q' := by
  by_contra hno
  have hdisj : ∀ a ∈ Q, ∀ b ∈ Q', a ≠ b := by
    intro a ha b hb hab
    exact hno ⟨a, ha, by rw [hab]; exact hb⟩
  have hnd : (Q ++ Q').Nodup := List.nodup_append.mpr ⟨hQnd, hQ'nd, hdisj⟩
  have hsub : (Q ++ Q') ⊆ members := by
    intro a ha
    rcases List.mem_append.mp ha with h | h
    · exact hQsub h
    · exact hQ'sub h
  have hle : (Q ++ Q').length ≤ members.length :=
    (List.subperm_of_subset hnd hsub).length_le
  rw [List.length_append] at hle
  omega

/-- **Agreement, on the extracted checker.** If the `Bool` checker accepts two
certificates against the same roster and votes, they carry the same value. This is
`Consensus.Bridge.cert_agreement` re-established for the compilable `List` checker, so the
running binary is covered by a proof rather than by conformance tests alone. -/
theorem agreement (members : List Nat) (votes : Votes) (c c' : Cert)
    (h : validB members votes c = true) (h' : validB members votes c' = true) :
    c.value = c'.value := by
  simp only [validB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h h'
  obtain ⟨⟨⟨hnd, hsub⟩, hmaj⟩, hall⟩ := h
  obtain ⟨⟨⟨hnd', hsub'⟩, hmaj'⟩, hall'⟩ := h'
  have hsubL : c.voters ⊆ members := by intro a ha; exact hsub a ha
  have hsubL' : c'.voters ⊆ members := by intro a ha; exact hsub' a ha
  obtain ⟨a, ha, ha'⟩ := shared members c.voters c'.voters hnd hnd' hsubL hsubL' hmaj hmaj'
  have e1 : lookup votes a = some c.value := by
    have := hall a ha; simpa using this
  have e2 : lookup votes a = some c'.value := by
    have := hall' a ha'; simpa using this
  rw [e1] at e2
  exact Option.some.inj e2

end Consensus.Checker
