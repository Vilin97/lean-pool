/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.SAT.ThreeSAT
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators.Internal.Scanner

/-!
# Regular syntax checker for exact 3-CNF encodings

Exact-3 shape is a regular property of the concrete CNF encoding. This module
gives a finite-state left-to-right scanner for it and proves that the scanner
accepts an encoded CNF exactly when every clause has three literals. The syntax
language deliberately need not reject every malformed word: intersecting it
with `CNFSAT.language` supplies well-formedness, which keeps this checker small
and makes the intended 3SAT decomposition explicit.

## Main results

- `ThreeSAT.Syntax.encode_mem_language_iff` -- correctness on encoded CNFs
- `ThreeSAT.Syntax.language_mem_P` -- exact-3 syntax is decidable in linear time
- `ThreeSAT.language_eq_cnfsat_inter_syntax` -- semantic decomposition of 3SAT
-/


@[expose] public section

namespace Complexity

namespace SAT

namespace ThreeSAT

namespace Syntax

/-- Parser state after consuming whole two-bit encoding tokens. `between k`
means that `k` complete literals have been seen in the current clause. -/
inductive TokenState where
  | between (count : Fin 4)
  | inLit (count : Fin 4)
  | invalid
  deriving DecidableEq, Fintype

/-- Initial token parser state: between clauses with no current literals. -/
def tokenStart : TokenState := .between 0

/-- One transition of the exact-3 grammar at token granularity. -/
def tokenStep : TokenState → EncToken → TokenState
  | .invalid, _ => .invalid
  | .between count, .bit _ => .inLit count
  | .between _, .litSep => .invalid
  | .between count, .clauseSep =>
      if count.val = 3 then tokenStart else .invalid
  | .inLit count, .bit true => .inLit count
  | .inLit _, .bit false => .invalid
  | .inLit count, .litSep =>
      if h : count.val < 3 then .between ⟨count.val + 1, by omega⟩ else .invalid
  | .inLit _, .clauseSep => .invalid

/-- Bit-level scanner state. `half state b` remembers the first bit of the
next two-bit encoding token. -/
inductive BitState where
  | ready (state : TokenState)
  | half (state : TokenState) (first : Bool)
  deriving DecidableEq, Fintype

/-- Initial bit-level scanner state. -/
def bitStart : BitState := .ready tokenStart

/-- Decode one of the four two-bit concrete token patterns. -/
def tokenOfBits : Bool → Bool → EncToken
  | false, false => .bit false
  | true, true => .bit true
  | false, true => .litSep
  | true, false => .clauseSep

/-- One input-bit transition of the exact-3 syntax scanner. -/
def bitStep : BitState → Bool → BitState
  | .ready state, b => .half state b
  | .half state first, second => .ready (tokenStep state (tokenOfBits first second))

/-- The scanner accepts precisely at a token boundary between clauses. -/
def accept (state : BitState) : Bool := decide (state = bitStart)

/-- The regular language recognized by the exact-3 syntax scanner. -/
def language : Language :=
  {z | accept (z.foldl bitStep bitStart) = true}

/-- An invalid token state remains invalid under every suffix. -/
@[simp] private theorem foldl_invalid (toks : List EncToken) :
    toks.foldl tokenStep .invalid = .invalid := by
  induction toks with
  | nil => rfl
  | cons tok toks ih =>
      rw [List.foldl_cons]
      exact ih

/-- Scanning one concrete token implements its token-level transition. -/
private theorem foldl_encode_token (state : TokenState) (tok : EncToken) :
    tok.encode.foldl bitStep (.ready state) = .ready (tokenStep state tok) := by
  cases tok with
  | bit b => cases b <;> rfl
  | litSep => rfl
  | clauseSep => rfl

/-- Scanning a flattened token stream agrees with folding the token parser. -/
private theorem foldl_encodeTokens (toks : List EncToken) (state : TokenState) :
    (encodeTokens toks).foldl bitStep (.ready state) =
      .ready (toks.foldl tokenStep state) := by
  induction toks generalizing state with
  | nil => rfl
  | cons tok toks ih =>
      rw [encodeTokens_cons, List.foldl_append, foldl_encode_token, ih]
      rfl

/-- Unary variable bodies leave the parser inside the current literal. -/
@[simp] private theorem foldl_true_tokens (count : Fin 4) (n : ℕ) :
    (List.replicate n (EncToken.bit true)).foldl tokenStep (.inLit count) =
      .inLit count := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.foldl_cons]
      exact ih

/-- A typed literal's raw tokens leave the parser inside that literal with
the clause count unchanged. -/
@[simp] private theorem foldl_rawTokens (count : Fin 4) (lit : Lit) :
    lit.rawTokens.foldl tokenStep (.between count) = .inLit count := by
  rcases lit with ⟨sign, var⟩
  simp only [Lit.rawTokens, Lit.encodeRaw, Unary.encode, List.map_cons,
    List.map_replicate, List.foldl_cons, tokenStep]
  exact foldl_true_tokens count var

/-- Scanning one well-formed source literal increments the current clause
count, or becomes invalid if three literals were already complete. -/
private theorem foldl_literal (count : Fin 4) (lit : Lit) :
    (lit.rawTokens ++ [EncToken.litSep]).foldl tokenStep (.between count) =
      if h : count.val < 3 then .between ⟨count.val + 1, by omega⟩ else .invalid := by
  rw [List.foldl_append, foldl_rawTokens]
  simp only [List.foldl_cons, List.foldl_nil, tokenStep]

/-- One encoded clause followed by its separator returns to the initial state
exactly when the clause has width three. -/
private theorem foldl_clause (clause : Clause) :
    (clause.tokens ++ [EncToken.clauseSep]).foldl tokenStep tokenStart =
      if clause.length = 3 then tokenStart else .invalid := by
  rcases clause with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩
  all_goals
    simp [Clause.tokens, List.foldl_append, tokenStart, tokenStep]

/-- Token-level recognition theorem for typed CNFs. -/
private theorem foldl_cnf_eq_start_iff (formula : CNF) :
    formula.tokens.foldl tokenStep tokenStart = tokenStart ↔ formula.Is3CNF := by
  induction formula with
  | nil => simp [CNF.tokens, CNF.Is3CNF]
  | cons clause rest ih =>
      rw [CNF.tokens, List.foldl_append]
      rw [foldl_clause]
      by_cases hclause : clause.length = 3
      · rw [if_pos hclause, ih]
        simp [CNF.is3CNF_cons, hclause]
      · rw [if_neg hclause, foldl_invalid]
        simp [tokenStart, CNF.is3CNF_cons, hclause]

/-- A typed CNF's bit encoding is accepted exactly when it is exact 3-CNF. -/
@[simp] theorem encode_mem_language_iff (formula : CNF) :
    formula.encode ∈ language ↔ formula.Is3CNF := by
  change accept (formula.encode.foldl bitStep bitStart) = true ↔ formula.Is3CNF
  rw [← CNF.encodeTokens_tokens formula]
  change accept ((encodeTokens formula.tokens).foldl bitStep (.ready tokenStart)) = true ↔ _
  rw [foldl_encodeTokens]
  change decide (.ready (formula.tokens.foldl tokenStep tokenStart) = bitStart) = true ↔ _
  rw [decide_eq_true_iff]
  unfold bitStart
  simp only [BitState.ready.injEq]
  exact foldl_cnf_eq_start_iff formula

/-- Concrete zero-work-tape finite-state checker for exact-3 syntax. -/
def syntaxTM : TM 0 :=
  TM.scannerTM bitStart bitStep (fun state => if accept state then .one else .zero)

/-- The syntax checker decides its regular language in exactly `n + 2` steps. -/
theorem syntaxTM_decidesInTime :
    syntaxTM.DecidesInTime language (fun n => n + 2) := by
  exact TM.scannerTM_decidesInTime bitStart bitStep accept (fun _ => Iff.rfl)

/-- The exact-3 syntax language is decidable in linear time. -/
theorem language_mem_P : language ∈ P := by
  refine Set.mem_iUnion.mpr ⟨1, 0, syntaxTM, fun n => n + 2,
    syntaxTM_decidesInTime, ?_⟩
  refine BigO.add ?_ (BigO.const_le_pow 2 1)
  simpa using BigO.refl (fun n : ℕ => n)

end Syntax

/-- 3SAT is CNF-SAT intersected with the regular exact-3 syntax language. -/
theorem language_eq_cnfsat_inter_syntax :
    language = CNFSAT.language ∩ Syntax.language := by
  ext z
  constructor
  · rintro ⟨formula, rfl, hshape, hsat⟩
    exact ⟨⟨formula, rfl, hsat⟩, (Syntax.encode_mem_language_iff formula).2 hshape⟩
  · rintro ⟨⟨formula, rfl, hsat⟩, hshape⟩
    exact ⟨formula, rfl, (Syntax.encode_mem_language_iff formula).1 hshape, hsat⟩

end ThreeSAT

end SAT

end Complexity
