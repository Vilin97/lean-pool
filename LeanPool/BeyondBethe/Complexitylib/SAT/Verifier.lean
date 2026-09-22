/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.SAT.Language
public import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# SAT verifier specification

This file defines an executable verifier for `pairLang Witness`:

1. split `pair(z, α)` back into `(z, α)` via `unpair?`,
2. decode `z` as a CNF in SAT's concrete bit encoding,
3. check the witness length bound `|α| ≤ |z| + 1`,
4. evaluate the decoded formula under `α`.

The deterministic implementation `verifyPairTM` in `SAT/VerifierTM.lean`
computes this specification and proves `pairLang Witness ∈ P`; this file is
the small executable/semantic audit surface for that machine proof.
-/


@[expose] public section

namespace Complexity

namespace SAT

-- ════════════════════════════════════════════════════════════════════════
-- Tokenization of the SAT bit-level encoding
-- ════════════════════════════════════════════════════════════════════════

/-- The four two-bit tokens used by SAT's concrete encoding. -/
inductive EncToken where
  /-- A doubled data bit: `false` is encoded as `00`, `true` as `11`. -/
  | bit (b : Bool)
  /-- The literal separator `|`, encoded as `01`. -/
  | litSep
  /-- The clause separator `#`, encoded as `10`. -/
  | clauseSep
  deriving DecidableEq, Repr

namespace EncToken

/-- Concrete two-bit representation of one SAT encoding token. -/
def encode : EncToken → List Bool
  | .bit false => [false, false]
  | .bit true => [true, true]
  | .litSep => [false, true]
  | .clauseSep => [true, false]

end EncToken

/-- Flatten a token stream back into concrete bits. -/
def encodeTokens (toks : List EncToken) : List Bool :=
  toks.flatMap EncToken.encode

/-- Split a bitstring into SAT encoding tokens. Odd-length strings are invalid. -/
def tokenize? : List Bool → Option (List EncToken)
  | [] => some []
  | [_] => none
  | false :: false :: rest => Option.map (EncToken.bit false :: ·) (tokenize? rest)
  | true :: true :: rest => Option.map (EncToken.bit true :: ·) (tokenize? rest)
  | false :: true :: rest => Option.map (EncToken.litSep :: ·) (tokenize? rest)
  | true :: false :: rest => Option.map (EncToken.clauseSep :: ·) (tokenize? rest)

/-- The empty token stream encodes to the empty bitstring. -/
@[simp] theorem encodeTokens_nil : encodeTokens [] = [] := rfl

/-- `encodeTokens` unfolds on `cons`: the head token's bits precede the tail's encoding. -/
@[simp] theorem encodeTokens_cons (tok : EncToken) (toks : List EncToken) :
    encodeTokens (tok :: toks) = tok.encode ++ encodeTokens toks := by
  cases tok <;> rfl

/-- `encodeTokens` is a monoid homomorphism: it distributes over list append. -/
@[simp] theorem encodeTokens_append (xs ys : List EncToken) :
    encodeTokens (xs ++ ys) = encodeTokens xs ++ encodeTokens ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [List.append_assoc, ih]

/-- Round trip: tokenizing an encoded token stream recovers the original tokens. -/
@[simp] theorem tokenize?_encodeTokens (toks : List EncToken) :
    tokenize? (encodeTokens toks) = some toks := by
  induction toks with
  | nil => simp [encodeTokens, tokenize?]
  | cons tok toks ih =>
      cases tok with
      | bit b =>
          cases b with
          | false =>
              change tokenize? (false :: false :: encodeTokens toks)
                = some (EncToken.bit false :: toks)
              simp [tokenize?, ih]
          | true =>
              change tokenize? (true :: true :: encodeTokens toks)
                = some (EncToken.bit true :: toks)
              simp [tokenize?, ih]
      | litSep =>
          change tokenize? (false :: true :: encodeTokens toks) = some (EncToken.litSep :: toks)
          simp [tokenize?, ih]
      | clauseSep =>
          change tokenize? (true :: false :: encodeTokens toks) = some (EncToken.clauseSep :: toks)
          simp [tokenize?, ih]

/-- Soundness of `tokenize?`: any successfully tokenized bitstring is the
encoding of the resulting token stream. -/
theorem tokenize?_sound {z : List Bool} {toks : List EncToken}
    (h : tokenize? z = some toks) : z = encodeTokens toks := by
  let rec hsound : ∀ z toks, tokenize? z = some toks → z = encodeTokens toks
    | [], toks, htok => by
        simp [tokenize?] at htok
        cases htok
        rfl
    | [_], _, htok => by
        simp [tokenize?] at htok
    | false :: false :: rest, toks, htok => by
        simp [tokenize?] at htok
        rcases htok with ⟨toks', hrest, rfl⟩
        have henc := hsound rest toks' hrest
        simp [encodeTokens, EncToken.encode, henc]
    | true :: true :: rest, toks, htok => by
        simp [tokenize?] at htok
        rcases htok with ⟨toks', hrest, rfl⟩
        have henc := hsound rest toks' hrest
        simp [encodeTokens, EncToken.encode, henc]
    | false :: true :: rest, toks, htok => by
        simp [tokenize?] at htok
        rcases htok with ⟨toks', hrest, rfl⟩
        have henc := hsound rest toks' hrest
        simp [encodeTokens, EncToken.encode, henc]
    | true :: false :: rest, toks, htok => by
        simp [tokenize?] at htok
        rcases htok with ⟨toks', hrest, rfl⟩
        have henc := hsound rest toks' hrest
        simp [encodeTokens, EncToken.encode, henc]
  exact hsound z toks h

/-- Encoding a stream of `bit` tokens doubles each underlying bit. -/
@[simp] theorem encodeTokens_map_bit (bs : List Bool) :
    encodeTokens (bs.map EncToken.bit) = doubleBits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [encodeTokens_cons, doubleBits_cons, EncToken.encode, ih]

-- ════════════════════════════════════════════════════════════════════════
-- Literal decoding
-- ════════════════════════════════════════════════════════════════════════

namespace Lit

/-- Decode a raw literal bitstring `[sign] ++ replicate var true`. -/
def decodeRaw? : List Bool → Option Lit
  | [] => none
  | sign :: rest =>
      if _h : ∀ b ∈ rest, b = true then
        some { sign := sign, var := rest.length }
      else
        none

/-- Round trip: decoding a literal's raw encoding recovers the literal. -/
@[simp] theorem decodeRaw?_encodeRaw (ℓ : Lit) :
    decodeRaw? ℓ.encodeRaw = some ℓ := by
  cases ℓ with
  | mk sign var =>
      simp [decodeRaw?, encodeRaw, Unary.encode]

/-- Soundness of `decodeRaw?`: any successfully decoded bitstring is the raw
encoding of the resulting literal. -/
theorem decodeRaw?_sound {bs : List Bool} {ℓ : Lit}
    (h : decodeRaw? bs = some ℓ) : bs = ℓ.encodeRaw := by
  cases bs with
  | nil =>
      simp [decodeRaw?] at h
  | cons sign rest =>
      simp only [decodeRaw?] at h
      split at h
      · cases h
        have hrep : rest = List.replicate rest.length true := by
          rw [List.eq_replicate_length]
          intro b hb
          exact ‹∀ b ∈ rest, b = true› b hb
        change sign :: rest = sign :: Unary.encode rest.length
        rw [Unary.encode]
        exact congrArg (List.cons sign) hrep
      · simp at h

/-- Token-level raw literal encoding. -/
def rawTokens (ℓ : Lit) : List EncToken :=
  ℓ.encodeRaw.map EncToken.bit

/-- A literal's token-level encoding flattens to its raw bits, doubled. -/
@[simp] theorem encodeTokens_rawTokens (ℓ : Lit) :
    encodeTokens ℓ.rawTokens = doubleBits ℓ.encodeRaw := by
  simp [rawTokens]

end Lit

-- ════════════════════════════════════════════════════════════════════════
-- Clause/CNF token encodings
-- ════════════════════════════════════════════════════════════════════════

namespace Clause

/-- Token-level clause encoding: doubled raw literal bits, each terminated by `|`. -/
def tokens : Clause → List EncToken
  | [] => []
  | ℓ :: ℓs => ℓ.rawTokens ++ [EncToken.litSep] ++ tokens ℓs

/-- A clause's token-level encoding flattens to its concrete bit encoding. -/
@[simp] theorem encodeTokens_tokens (c : Clause) :
    encodeTokens (tokens c) = c.encode := by
  induction c with
  | nil => rfl
  | cons ℓ ℓs ih =>
      simp [tokens, encode_cons, ih, List.append_assoc, EncToken.encode]

/-- `Clause.tokens` distributes over list append. -/
@[simp] theorem tokens_append (c₁ c₂ : Clause) :
    tokens (c₁ ++ c₂) = tokens c₁ ++ tokens c₂ := by
  induction c₁ with
  | nil => rfl
  | cons ℓ ℓs ih =>
      simp [tokens, ih, List.append_assoc]

end Clause

namespace CNF

/-- Token-level CNF encoding: each clause is terminated by `#`. -/
def tokens : CNF → List EncToken
  | [] => []
  | c :: cs => c.tokens ++ [EncToken.clauseSep] ++ tokens cs

/-- A CNF's token-level encoding flattens to its concrete bit encoding. -/
@[simp] theorem encodeTokens_tokens (φ : CNF) :
    encodeTokens (tokens φ) = φ.encode := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
      simp [tokens, encode_cons, ih, List.append_assoc, EncToken.encode]

/-- `CNF.tokens` distributes over list append. -/
@[simp] theorem tokens_append (φ ψ : CNF) :
    tokens (φ ++ ψ) = tokens φ ++ tokens ψ := by
  induction φ with
  | nil => rfl
  | cons c cs ih =>
      simp [tokens, ih, List.append_assoc]

end CNF

-- ════════════════════════════════════════════════════════════════════════
-- Token parser for CNFs
-- ════════════════════════════════════════════════════════════════════════

/-- Core parser state:
`rawRev` is the reversed current raw literal, `clauseRev` the reversed current
clause, and `cnfRev` the reversed list of completed clauses. -/
def parseTokensAux :
    List EncToken → List Bool → Clause → CNF → Option CNF
  | [], rawRev, clauseRev, cnfRev =>
      if _hraw : rawRev = [] then
        if _hclause : clauseRev = [] then
          some cnfRev.reverse
        else
          none
      else
        none
  | EncToken.bit b :: toks, rawRev, clauseRev, cnfRev =>
      parseTokensAux toks (b :: rawRev) clauseRev cnfRev
  | EncToken.litSep :: toks, rawRev, clauseRev, cnfRev =>
      match Lit.decodeRaw? rawRev.reverse with
      | some ℓ => parseTokensAux toks [] (ℓ :: clauseRev) cnfRev
      | none => none
  | EncToken.clauseSep :: toks, rawRev, clauseRev, cnfRev =>
      if _hraw : rawRev = [] then
        parseTokensAux toks [] [] (clauseRev.reverse :: cnfRev)
      else
        none

private theorem parseTokensAux_map_bit
    (bs : List Bool) (toks : List EncToken)
    (rawRev : List Bool) (clauseRev : Clause) (cnfRev : CNF) :
    parseTokensAux (bs.map EncToken.bit ++ toks) rawRev clauseRev cnfRev =
      parseTokensAux toks (bs.reverse ++ rawRev) clauseRev cnfRev := by
  induction bs generalizing rawRev with
  | nil => simp
  | cons b bs ih =>
      cases b <;> simp [parseTokensAux, ih, List.reverse_cons, List.append_assoc]

private theorem parseTokensAux_clause_tokens
    (c : Clause) (toks : List EncToken) (clauseRev : Clause) (cnfRev : CNF) :
    parseTokensAux (c.tokens ++ EncToken.clauseSep :: toks) [] clauseRev cnfRev =
      parseTokensAux toks [] [] ((clauseRev.reverse ++ c) :: cnfRev) := by
  induction c generalizing clauseRev with
  | nil =>
      simp [Clause.tokens, parseTokensAux]
  | cons ℓ ℓs ih =>
      simp [Clause.tokens, Lit.rawTokens]
      rw [parseTokensAux_map_bit ℓ.encodeRaw]
      simp [parseTokensAux, Lit.decodeRaw?_encodeRaw, List.reverse_reverse, ih,
        List.reverse_cons, List.append_assoc]

private theorem parseTokensAux_cnf_tokens
    (φ : CNF) (toks : List EncToken) (cnfRev : CNF) :
    parseTokensAux (φ.tokens ++ toks) [] [] cnfRev =
      parseTokensAux toks [] [] (φ.reverse ++ cnfRev) := by
  induction φ generalizing cnfRev with
  | nil => simp [CNF.tokens]
  | cons c cs ih =>
      rw [CNF.tokens]
      have hclause := parseTokensAux_clause_tokens c (CNF.tokens cs ++ toks) [] cnfRev
      rw [show c.tokens ++ [EncToken.clauseSep] ++ CNF.tokens cs ++ toks =
        c.tokens ++ EncToken.clauseSep :: (CNF.tokens cs ++ toks) by simp [List.append_assoc]]
      rw [hclause]
      simp [ih, List.reverse_cons, List.append_assoc]

private theorem parseTokensAux_sound
    {toks : List EncToken} {rawRev : List Bool} {clauseRev : Clause}
    {cnfRev φ : CNF}
    (h : parseTokensAux toks rawRev clauseRev cnfRev = some φ) :
    CNF.tokens cnfRev.reverse ++ Clause.tokens clauseRev.reverse ++
        rawRev.reverse.map EncToken.bit ++ toks =
      CNF.tokens φ := by
  induction toks generalizing rawRev clauseRev cnfRev φ with
  | nil =>
      cases rawRev <;> cases clauseRev <;> simp [parseTokensAux, Clause.tokens] at h ⊢
      cases h
      simp
  | cons tok toks ih =>
      cases tok with
      | bit b =>
          simp [parseTokensAux] at h
          have hrec := ih h
          simpa [List.reverse_cons, List.append_assoc] using hrec
      | litSep =>
          simp [parseTokensAux] at h
          rcases hdecode : Lit.decodeRaw? rawRev.reverse with _ | ℓ
          · simp [hdecode] at h
          · simp [hdecode] at h
            have hrec := ih h
            have hraw : rawRev.reverse = ℓ.encodeRaw := Lit.decodeRaw?_sound hdecode
            simpa [hraw, Clause.tokens, Clause.tokens_append, Lit.rawTokens,
              List.reverse_cons, List.append_assoc] using hrec
      | clauseSep =>
          simp [parseTokensAux] at h
          rcases h with ⟨hraw, hrest⟩
          have hrec := ih hrest
          simpa [hraw, CNF.tokens, CNF.tokens_append, Clause.tokens,
            List.reverse_cons, List.append_assoc] using hrec

/-- Decode a concrete SAT-encoded bitstring as a CNF. -/
def CNF.decode? (z : List Bool) : Option CNF := do
  let toks <- tokenize? z
  parseTokensAux toks [] [] []

/-- Round trip: decoding an encoded CNF recovers the formula. -/
@[simp] theorem CNF.decode?_encode (φ : CNF) :
    CNF.decode? φ.encode = some φ := by
  rw [CNF.decode?, ← CNF.encodeTokens_tokens φ, tokenize?_encodeTokens]
  simp
  have hparse := parseTokensAux_cnf_tokens φ [] []
  simpa [parseTokensAux] using hparse

/-- Soundness of `CNF.decode?`: any successfully decoded bitstring is the
encoding of the resulting CNF. -/
theorem CNF.decode?_sound {z : List Bool} {φ : CNF}
    (h : CNF.decode? z = some φ) : z = φ.encode := by
  unfold CNF.decode? at h
  cases htok : tokenize? z with
  | none =>
      simp [htok] at h
  | some toks =>
      simp [htok] at h
      have hz : z = encodeTokens toks := tokenize?_sound htok
      have htoks : toks = CNF.tokens φ := by
        simpa using! (parseTokensAux_sound h)
      calc
        z = encodeTokens toks := hz
        _ = encodeTokens (CNF.tokens φ) := by rw [htoks]
        _ = φ.encode := CNF.encodeTokens_tokens φ

-- ════════════════════════════════════════════════════════════════════════
-- Executable verifier specification
-- ════════════════════════════════════════════════════════════════════════

/-- Boolean verifier for SAT's witness relation on paired inputs. -/
def verifyPair (w : List Bool) : Bool :=
  match unpair? w with
  | none => false
  | some (z, α) =>
      match CNF.decode? z with
      | none => false
      | some φ => decide (α.length ≤ z.length + 1) && CNF.eval α φ

/-- On a well-formed pair `pair(φ.encode, α)`, `verifyPair` reduces to the
witness length check conjoined with evaluating `φ` under `α`. -/
@[simp] theorem verifyPair_pair_encode (φ : CNF) (α : Assignment) :
    verifyPair (pair φ.encode α) = (decide (α.length ≤ φ.encode.length + 1) && CNF.eval α φ) := by
  simp [verifyPair, CNF.decode?_encode]

/-- Completeness: `verifyPair` accepts the pairing of any witnessed instance. -/
theorem verifyPair_true_of_witness {z α : List Bool} (hR : Witness z α) :
    verifyPair (pair z α) = true := by
  obtain ⟨φ, hz, hlen, heval⟩ := hR
  subst hz
  simp [verifyPair_pair_encode, hlen, heval]

/-- Correctness of the verifier: `verifyPair` accepts exactly the members of
`pairLang Witness`. -/
theorem verifyPair_eq_true_iff_mem_pairLang (w : List Bool) :
    verifyPair w = true ↔ w ∈ pairLang Witness := by
  constructor
  · intro h
    unfold verifyPair at h
    cases hunpair : unpair? w with
    | none =>
        simp [hunpair] at h
    | some zw =>
        rcases zw with ⟨z, α⟩
        simp [hunpair] at h
        cases hdecode : CNF.decode? z with
        | none =>
            simp [hdecode] at h
        | some φ =>
            simp [hdecode] at h
            have hz : z = φ.encode := CNF.decode?_sound hdecode
            have hw : w = pair z α := eq_pair_of_unpair?_eq_some hunpair
            have hlen : α.length ≤ z.length + 1 := by
              simpa [decide_eq_true_eq] using h.1
            refine ⟨z, α, hw, ?_⟩
            exact ⟨φ, hz, hlen, h.2⟩
  · rintro ⟨z, α, rfl, hR⟩
    exact verifyPair_true_of_witness hR

/-- `verifyPair_eq_true_iff_mem_pairLang` with the biconditional flipped. -/
theorem mem_pairLang_iff_verifyPair (w : List Bool) :
    w ∈ pairLang Witness ↔ verifyPair w = true := by
  rw [verifyPair_eq_true_iff_mem_pairLang]

/-- `pairLang Witness` equals the language decided by `verifyPair`, as sets. -/
theorem pairLang_witness_eq_verifyPairLang :
    pairLang Witness = {w | verifyPair w = true} := by
  ext w
  exact mem_pairLang_iff_verifyPair w

end SAT

end Complexity
