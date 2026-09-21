/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.NP
public import LeanPool.BeyondBethe.Complexitylib.Classes.FNP.Defs

/-!
# NP witness characterization

This file states and (up to a single TM-engineering lemma) proves the
textbook characterization of `NP` via FNP witness relations:

> A language `L` is in `NP` iff there is an FNP relation `R` such that
> `x ∈ L ↔ ∃ y, R x y`.

The forward direction (`NP ⊆ witness form`) is a *computation-path* witness
argument and is left for a later pass.

The reverse direction — **the FNP ⇒ NP bridge** used by SAT ∈ NP — is
captured here by `mem_NP_of_FNP_witness`, parameterized by the single
TM-engineering construction interface `WitnessNTMConstruction`: build the
nondeterministic "guess-and-verify" machine from a deterministic verifier
of `pairLang R`. Everything above that construction — unpacking FNP,
computing polynomial bounds, and packaging the result as membership in
`NP` — is proved here unconditionally.

## Proof strategy for `WitnessNTMConstruction`

Given:
- a DTM `M` deciding `pairLang R` in polynomial time, and
- a polynomial `p` bounding witness length (`PolyBalanced R`),

construct an NTM `N` that, on input `x`:

1. **Guess phase.** Reads `p.eval |x|` nondeterministic bits and writes them
   onto a dedicated work tape as a guessed witness `y`.
2. **Pair construction.** Copies `pair(x, y)` onto another work tape using
   `x` from the input tape and the guessed `y` from the witness tape.
3. **Verification.** Simulates `M` on the constructed pair (reading from
   the work tape that holds `pair(x, y)` instead of the input tape).

The total running time is polynomial: `O(p(n) + n + T(2n + p(n) + 2))`
where `T(n) = n^c` bounds `M`.

The construction is mechanical but substantial — analogous in size to the
existing `unionTM`/`seqTM` combinators — and is deferred to a later pass.
All downstream consequences (including `SAT ∈ NP` conditional on the SAT
verifier being in P) rest only on that single lemma.
-/


public section

namespace Complexity


namespace NP

/-- The witness language of a relation `R` — the set of inputs `x` that
    admit some witness. Isolated as a definition so the statement of
    `mem_NP_of_FNP_witness` reads cleanly. -/
def witnessLang (R : List Bool → List Bool → Prop) : Language :=
  {x | ∃ y, R x y}

/-- Membership in `witnessLang R` unfolds to the existence of a witness:
    `x ∈ witnessLang R ↔ ∃ y, R x y`. -/
@[simp] theorem mem_witnessLang {R : List Bool → List Bool → Prop} {x : List Bool} :
    x ∈ witnessLang R ↔ ∃ y, R x y := Iff.rfl

-- ════════════════════════════════════════════════════════════════════════
-- The core TM-engineering construction interface
-- ════════════════════════════════════════════════════════════════════════

/-- **Guess-and-verify NTM construction interface.** Given a DTM `M` deciding
    `pairLang R` within a time bound `T(n) ≤ O(n^c)` and a polynomial `p`
    bounding witness length, there exists an NTM deciding
    `witnessLang R = {x | ∃ y, R x y}` in polynomial time.

    The construction is the standard Arora-Barak guess-and-verify:
    nondeterministically write a witness of length `≤ p(|x|)` onto a work
    tape, build `pair(x, y)` on another work tape, then simulate `M`.

    This is isolated as a named proposition so results can state precisely
    when they rely on the still-to-be-built machine construction, instead of
    importing an unproved theorem.

    ## Supporting utilities
    When implementing this construction, the following lemmas from
    `Complexitylib.Asymptotics` will be useful for packaging the running-time
    bound of the constructed NTM:
    - `BigO.pow_polynomial_bound` — turn the hypothesis `f =O (·^c)` into
      an explicit `Polynomial ℕ` bound on `f`.
    - `BigO.of_polynomial_bound` — turn the computed polynomial bound on
      the constructed NTM's running time back into `g =O (·^d)`.
    The `pair_length` simp lemma in `Complexitylib.Classes.Pairing` gives
    `|pair x y| = 2·|x| + 2 + |y|`, needed when substituting the simulated
    verifier's input length. -/
def WitnessNTMConstruction : Prop :=
  ∀ {R : List Bool → List Bool → Prop}
    {p : Polynomial ℕ} {c k : ℕ}
    {M : TM k} {f : ℕ → ℕ},
    (∀ x y, R x y → y.length ≤ p.eval x.length) →
    M.DecidesInTime (pairLang R) f →
    f =O (· ^ c) →
    ∃ (k' d : ℕ) (N : NTM k') (g : ℕ → ℕ),
      N.DecidesInTime (witnessLang R) g ∧ g =O (· ^ d)

-- ════════════════════════════════════════════════════════════════════════
-- Main theorem: FNP witness relations put L in NP
-- ════════════════════════════════════════════════════════════════════════

/-- **FNP ⇒ NP via witnesses.** If the generic guess-and-verify construction
    has been implemented, `R ∈ FNP`, and `x ∈ L ↔ ∃ y, R x y`, then
    `L ∈ NP`. Proof: unpack FNP to get a polynomial-time DTM verifier
    `M` for `pairLang R` and a polynomial witness-length bound, apply the
    construction to build the guess-and-verify NTM, and package the result as
    NP membership. -/
theorem mem_NP_of_FNP_witness
    (hwitness : WitnessNTMConstruction)
    {R : List Bool → List Bool → Prop} {L : Language}
    (hR : R ∈ FNP)
    (hchar : ∀ x, x ∈ L ↔ ∃ y, R x y) :
    L ∈ NP := by
  obtain ⟨hPB, hPairP⟩ := hR
  -- Unpack `pairLang R ∈ P` to a DTM and a poly time bound.
  obtain ⟨c, k, M, f, hM, hfO⟩ := Set.mem_iUnion.mp hPairP
  -- Unpack `PolyBalanced R` to a polynomial witness-length bound.
  obtain ⟨p, hp⟩ := hPB
  -- Build the NTM via the core construction.
  obtain ⟨k', d, N, g, hN, hgO⟩ := hwitness hp hM hfO
  -- `L = witnessLang R` up to set extensionality.
  have hLeq : L = witnessLang R := Set.ext fun x => by
    simpa [witnessLang] using hchar x
  -- Conclude.
  rw [hLeq]
  exact Set.mem_iUnion.mpr ⟨d, k', N, g, hN, hgO⟩

-- ════════════════════════════════════════════════════════════════════════
-- Immediate corollary: FNP ⇔ NP-witness (the "reverse direction" only)
-- ════════════════════════════════════════════════════════════════════════

/-- **Restatement in terms of `witnessLang`.** If `R ∈ FNP`, then
    `witnessLang R ∈ NP`. This is the useful form for applying to
    concrete relations like `Witness`. -/
theorem witnessLang_mem_NP_of_FNP
    (hwitness : WitnessNTMConstruction)
    {R : List Bool → List Bool → Prop} (hR : R ∈ FNP) :
    witnessLang R ∈ NP :=
  mem_NP_of_FNP_witness hwitness hR fun _ => Iff.rfl

end NP

end Complexity
