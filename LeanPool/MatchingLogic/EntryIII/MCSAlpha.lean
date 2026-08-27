/-
Copyright (c) 2026 Aurélien Eveil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Eveil, Anthropic, OpenAI
-/

/-
Maximal-consistent-set closure under the raw-syntax alpha bridge.

`Pattern.AlphaEq` packages derivable implications in both directions.  This
module turns those derivations, and the Nat-specific monotonicity rules used to
construct them, into reusable MCS membership facts.  It is independent of the
later witnessed-MCS construction.
-/
import LeanPool.MatchingLogic.EntryIII.CaptureAvoiding
import LeanPool.MatchingLogic.EntryIII.LocalTheory

/-!
# MatchingLogic.EntryIII.MCSAlpha
-/

namespace MatchingLogic

variable {S : Signature}

namespace IsMCS

/-- Every empty-theory theorem belongs to every MCS. -/
theorem mem_of_provable_empty {Gamma : Set (Pattern S Nat)} {p : Pattern S Nat}
    (hM : IsMCS Gamma) (h : Provable (∅ : Set (Pattern S Nat)) p) : p ∈ Gamma :=
  hM.mem_iff_locProvable.mpr (LocProvable.of_provable h)

/-- MCS membership transports along an empty-theory implication. -/
theorem mem_of_provable_imp {Gamma : Set (Pattern S Nat)} {p q : Pattern S Nat}
    (hM : IsMCS Gamma) (hp : p ∈ Gamma)
    (hpq : Provable (∅ : Set (Pattern S Nat)) (.imp p q)) : q ∈ Gamma :=
  hM.mp_mem hp (hM.mem_of_provable_empty hpq)

/-- Membership transport through implication monotonicity. -/
theorem imp_mem_of_mono {Gamma : Set (Pattern S Nat)}
    {p p' q q' : Pattern S Nat} (hM : IsMCS Gamma)
    (hp : Provable (∅ : Set (Pattern S Nat)) (.imp p' p))
    (hq : Provable (∅ : Set (Pattern S Nat)) (.imp q q'))
    (hmem : Pattern.imp p q ∈ Gamma) : Pattern.imp p' q' ∈ Gamma :=
  hM.mem_of_provable_imp hmem (Provable.imp_mono hp hq)

/-- Membership transport through existential monotonicity. -/
theorem ex_mem_of_mono {Gamma : Set (Pattern S Nat)} {x : Nat}
    {p q : Pattern S Nat} (hM : IsMCS Gamma)
    (hpq : Provable (∅ : Set (Pattern S Nat)) (.imp p q))
    (hmem : Pattern.ex x p ∈ Gamma) : Pattern.ex x q ∈ Gamma :=
  hM.mem_of_provable_imp hmem (Provable.ex_mono hpq)

/-- Membership transport through pointwise application monotonicity. -/
theorem app_mem_of_mono {Gamma : Set (Pattern S Nat)} {sigma : S.Sym}
    {args args' : Fin (S.arity sigma) → Pattern S Nat} (hM : IsMCS Gamma)
    (hargs : ∀ i, Provable (∅ : Set (Pattern S Nat)) (.imp (args i) (args' i)))
    (hmem : Pattern.app sigma args ∈ Gamma) : Pattern.app sigma args' ∈ Gamma :=
  hM.mem_of_provable_imp hmem (Provable.app_mono hargs)

/-- MCS membership is invariant under the kernel-level alpha-equivalence
relation. -/
theorem alphaEq_mem_iff {Gamma : Set (Pattern S Nat)} {p q : Pattern S Nat}
    (hM : IsMCS Gamma) (halpha : Pattern.AlphaEq p q) : p ∈ Gamma ↔ q ∈ Gamma := by
  constructor
  · intro hp
    exact hM.mem_of_provable_imp hp (halpha.forward ∅)
  · intro hq
    exact hM.mem_of_provable_imp hq (halpha.backward ∅)

/-- Alpha-congruent implications have identical MCS membership. -/
theorem imp_alphaEq_mem_iff {Gamma : Set (Pattern S Nat)}
    {p p' q q' : Pattern S Nat} (hM : IsMCS Gamma)
    (hp : Pattern.AlphaEq p p') (hq : Pattern.AlphaEq q q') :
    Pattern.imp p q ∈ Gamma ↔ Pattern.imp p' q' ∈ Gamma :=
  hM.alphaEq_mem_iff (Pattern.AlphaEq.imp hp hq)

/-- Alpha-congruent existential bodies have identical MCS membership. -/
theorem ex_alphaEq_mem_iff {Gamma : Set (Pattern S Nat)} {x : Nat}
    {p q : Pattern S Nat} (hM : IsMCS Gamma) (h : Pattern.AlphaEq p q) :
    Pattern.ex x p ∈ Gamma ↔ Pattern.ex x q ∈ Gamma :=
  hM.alphaEq_mem_iff (Pattern.AlphaEq.ex x h)

/-- Pointwise alpha-congruent application arguments have identical MCS
membership. -/
theorem app_alphaEq_mem_iff {Gamma : Set (Pattern S Nat)} {sigma : S.Sym}
    {args args' : Fin (S.arity sigma) → Pattern S Nat} (hM : IsMCS Gamma)
    (h : ∀ i, Pattern.AlphaEq (args i) (args' i)) :
    Pattern.app sigma args ∈ Gamma ↔ Pattern.app sigma args' ∈ Gamma :=
  hM.alphaEq_mem_iff (Pattern.AlphaEq.app h)

/-- Bottom belongs to no maximal locally consistent set. -/
theorem bot_not_mem {Gamma : Set (Pattern S Nat)} (hM : IsMCS Gamma) :
    (.bot : Pattern S Nat) ∉ Gamma := by
  intro hbot
  exact hM.1 (LocProvable.of_mem hbot)

private theorem not_imp_taut :
    PForm.Taut
      (.imp (.imp (.atom 0) .bot) (.imp (.atom 0) (.atom 1))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

private theorem right_imp_taut :
    PForm.Taut (.imp (.atom 1) (.imp (.atom 0) (.atom 1))) := by
  intro v
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [PForm.eval, h0, h1]

/-- Boolean membership clause for primitive implication. -/
theorem imp_mem_iff {Gamma : Set (Pattern S Nat)} (hM : IsMCS Gamma)
    (p q : Pattern S Nat) :
    Pattern.imp p q ∈ Gamma ↔ p ∉ Gamma ∨ q ∈ Gamma := by
  constructor
  · intro himp
    by_cases hp : p ∈ Gamma
    · exact Or.inr (hM.mp_mem hp himp)
    · exact Or.inl hp
  · rintro (hnp | hq)
    · have hnpMem : Pattern.nt p ∈ Gamma := hM.neg_mem_iff_not_mem.mpr hnp
      have ht : Provable (∅ : Set (Pattern S Nat))
          (.imp (Pattern.nt p) (.imp p q)) := by
        simpa [PForm.subst, Pattern.nt] using
          (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
            (θ := fun n => if n = 0 then p else q) not_imp_taut)
      exact hM.mem_of_provable_imp hnpMem ht
    · have ht : Provable (∅ : Set (Pattern S Nat)) (.imp q (.imp p q)) := by
        simpa [PForm.subst] using
          (Provable.taut (Γ := (∅ : Set (Pattern S Nat)))
            (θ := fun n => if n = 0 then p else q) right_imp_taut)
      exact hM.mem_of_provable_imp hq ht

end IsMCS

end MatchingLogic
