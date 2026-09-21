/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.SAT.Encoding
public import LeanPool.BeyondBethe.Complexitylib.Classes.NP.Witness

/-!
# SAT: Language and Witness Relation

This file defines the formal SAT language `language` and the NP witness
relation `Witness`, and proves the two core bridge theorems:

- `mem_language_iff_witness` — `z ∈ language ↔ ∃ α, Witness z α`
  (a CNF is satisfiable iff it admits a short satisfying assignment)
- `polyBalanced_witness` — witness length is bounded by `|z| + 1`
  (satisfying assignments can always be truncated to length `φ.maxVar + 1`,
  and `φ.maxVar ≤ |φ.encode|` from the unary encoding)

These are the semantic and witness-length ingredients used by both routes to
`SAT ∈ NP`. The executable verifier is specified in `SAT/Verifier.lean`, its
polynomial-time TM implementation is proved in `SAT/VerifierTM.lean`, and the
SAT-specialized guess-and-verify construction is assembled into the
unconditional headline theorem in `SAT/Headline.lean`.
-/


@[expose] public section

namespace Complexity

namespace SAT

/-- **The SAT language.** A bitstring `z` is in `language` iff it encodes
    some satisfiable CNF formula.

    Note: `encode` is injective on well-formed CNFs, but we don't need
    injectivity for any of the downstream theorems — we only need
    "there exists some `φ` …". -/
def language : Language := {z | ∃ φ : CNF, z = φ.encode ∧ φ.Satisfiable}

/-- **The SAT witness relation.** `Witness z α` holds when `z` encodes
    some CNF `φ`, `α` is a bit-string of length at most `|z| + 1`, and
    `α` satisfies `φ`.

    The `|z| + 1` length bound is what gives `PolyBalanced Witness`. It's
    always achievable because any satisfying assignment can be truncated
    to length `φ.maxVar + 1 ≤ |φ.encode| + 1 = |z| + 1`
    (`satisfiable_iff_short_witness` + `CNF.maxVar_le_encode_length`). -/
def Witness (z α : List Bool) : Prop :=
  ∃ φ : CNF, z = φ.encode ∧ α.length ≤ z.length + 1 ∧ CNF.eval α φ = true

-- ════════════════════════════════════════════════════════════════════════
-- Witness characterization: language iff ∃ witness
-- ════════════════════════════════════════════════════════════════════════

/-- **Witness characterization of `language`.** A string `z` is in `language`
    iff there exists a witness `α` with `Witness z α`.

    The forward direction uses `CNF.satisfiable_iff_short_witness` to
    produce a truncated witness, then applies `CNF.maxVar_le_encode_length`
    to bound its length by `|z| + 1`.

    The reverse direction is immediate: any `α` satisfying `φ` proves
    `φ.Satisfiable`. -/
theorem mem_language_iff_witness (z : List Bool) :
    z ∈ language ↔ ∃ α, Witness z α := by
  constructor
  · rintro ⟨φ, hz, hsat⟩
    -- Extract a short witness using truncation lemma.
    rw [CNF.satisfiable_iff_short_witness] at hsat
    obtain ⟨α, hlen, heval⟩ := hsat
    refine ⟨α, φ, hz, ?_, heval⟩
    -- α.length ≤ φ.maxVar + 1 ≤ |φ.encode| + 1 = |z| + 1
    have : α.length ≤ φ.encode.length + 1 :=
      le_trans hlen (by have := CNF.maxVar_le_encode_length φ; omega)
    rw [hz]; exact this
  · rintro ⟨α, φ, hz, _, heval⟩
    exact ⟨φ, hz, α, heval⟩

-- ════════════════════════════════════════════════════════════════════════
-- PolyBalanced: witness length is bounded by a polynomial in |z|
-- ════════════════════════════════════════════════════════════════════════

/-- **Short-witness property for SAT.** The witness relation `Witness` is
    polynomially balanced: every valid witness has length at most
    `|z| + 1`, which is bounded by the degree-1 polynomial `X + 1`.

    This is the key structural fact that makes `SAT` a candidate for NP:
    we never need to guess more than linearly many bits. -/
theorem polyBalanced_witness : PolyBalanced Witness := by
  refine ⟨Polynomial.X + Polynomial.C 1, ?_⟩
  intro z α hR
  obtain ⟨_, _, hlen, _⟩ := hR
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  exact hlen

-- ════════════════════════════════════════════════════════════════════════
-- Route to SAT ∈ NP
-- ════════════════════════════════════════════════════════════════════════
--
-- With `polyBalanced_witness` in hand, one route to SAT ∈ NP asks whether
-- the verifier's pair language `pairLang Witness` is in P. That is, whether
-- there is a poly-time deterministic TM that, given
-- `pair(z, α)`, decides whether `Witness z α` holds — equivalently, that
-- parses `z` as a CNF and evaluates it at `α`.
--
-- `SAT/VerifierTM.lean` now discharges that verifier obligation. The generic
-- theorem below remains parameterized by `WitnessNTMConstruction`; the
-- unconditional SAT headline instead uses the specialized construction from
-- `SAT/Internal/GuessVerify.lean`.

/-- **SAT is in FNP modulo the verifier.** If the verifier's pair language
    is in P, then `Witness` is an FNP relation — and hence a candidate NP
    witness relation for `language`. The only nontrivial content is
    `polyBalanced_witness`. -/
theorem witness_mem_FNP_of_verifier (h : pairLang Witness ∈ P) : Witness ∈ FNP :=
  ⟨polyBalanced_witness, h⟩

/-- **SAT is in NP modulo the verifier and generic guess-and-verify construction.**
    If the verifier's pair language is in P and the generic FNP-witness to NP
    construction has been built, then `language ∈ NP`.

    Combines `witness_mem_FNP_of_verifier` (SAT's FNP witness relation) with
    the generic NP witness theorem `mem_NP_of_FNP_witness`. This theorem
    deliberately retains the generic construction as an explicit hypothesis;
    the SAT-specific unconditional route is provided by `SAT/Headline.lean`. -/
theorem language_mem_NP_of_verifier
    (hwitness : NP.WitnessNTMConstruction) (h : pairLang Witness ∈ P) :
    language ∈ NP :=
  NP.mem_NP_of_FNP_witness hwitness (witness_mem_FNP_of_verifier h) mem_language_iff_witness

-- ════════════════════════════════════════════════════════════════════════
-- Worked examples: end-to-end sanity check of the semantic layer
-- ════════════════════════════════════════════════════════════════════════

/-- `[[x₀]]` is satisfiable. Checked by the `decide` tactic using
    `CNF.decidableSatisfiable`. -/
example : CNF.Satisfiable [[{sign := true, var := 0}]] := by decide

/-- `[[x₀], [¬x₀]]` is unsatisfiable: no assignment can make both clauses true. -/
example : ¬ CNF.Satisfiable [[{sign := true, var := 0}], [{sign := false, var := 0}]] := by
  decide

/-- `[[x₀, ¬x₁], [x₁]]` is satisfiable: `α = [true, true]` works. -/
example : CNF.Satisfiable [[{sign := true, var := 0}, {sign := false, var := 1}],
                           [{sign := true, var := 1}]] := by decide

end SAT

end Complexity
