/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import LeanPool.Lentil.ProofMode.Tactics.Have
import LeanPool.Lentil.ProofMode.Tactics.Clear
import LeanPool.Lentil.ProofMode.Tactics.Rename
import LeanPool.Lentil.ProofMode.Tactics.Revert

namespace TLA.ProofMode

open Lean Meta Elab Tactic
open Lean.Parser.Tactic

-- Not sure if this is generally useful, so just make it as a `private theorem` for now
private theorem exists_put_witness_back {α : Sort v} {p : α → pred σ} {Γ g : pred σ} :
  (∀ x, ((Γ) |-tla- ((p x) → g))) = ((Γ) |-tla- ((∃ x, (p x)) → g)) := by tlaUnfoldSimp; grind

section

variable {σ : Type u} {hyps : List (NamedPred σ)} {goal : pred σ}

section

variable (name1 name2 : String) {a b : pred σ}

theorem Entails_rcases_and_by_idx (idx : Nat)
  (heq : hyps[idx]?.map NamedPred.pred = some (tlaAnd a b)) :
  letI hyps' := hyps.eraseIdx idx
  Entails (hyps' ++ [⟨name1, a⟩, ⟨name2, b⟩]) goal → Entails hyps goal := by
  unfold Entails
  simp only [List.map_append, repeatedAnd_append, ← impl_intro_add_r]
  intro h
  conv at h => enter [2]; dsimp only [repeatedAnd, LentilLib.List.foldrD, List.map]
  apply Entails_revert_by_idx idx
  simp at heq; rcases heq with ⟨r, heq1, heq2⟩
  rw [List.get?Internal_eq_getElem?, heq1]; simp only [Option.elim, heq2]; exact h

theorem Entails_rcases_and_by_name (chosen : String) :
  letI idx := hyps.findIdx fun h => h.name == chosen
  (type_of% (@Entails_rcases_and_by_idx _ hyps goal name1 name2 a b idx)) :=
  Entails_rcases_and_by_idx _ _ _

-- NOTE: This proof is slightly repetitive with `Entails_rcases_and_by_idx`, but
-- here the hypothesis is `tlaOr`, so the destructure splits into two subgoals.
theorem Entails_rcases_or_by_idx (idx : Nat)
  (heq : hyps[idx]?.map NamedPred.pred = some (tlaOr a b)) :
  letI hyps' := hyps.eraseIdx idx
  Entails (hyps' ++ [⟨name1, a⟩]) goal → Entails (hyps' ++ [⟨name2, b⟩]) goal →
  Entails hyps goal := by
  unfold Entails
  simp only [List.map_append, repeatedAnd_append, ← impl_intro_add_r]
  intro h1 h2
  conv at h1 => enter [2]; dsimp only [repeatedAnd, LentilLib.List.foldrD, List.map]
  conv at h2 => enter [2]; dsimp only [repeatedAnd, LentilLib.List.foldrD, List.map]
  apply Entails_revert_by_idx idx
  simp at heq; rcases heq with ⟨r, heq1, heq2⟩
  rw [List.get?Internal_eq_getElem?, heq1]; simp only [Option.elim, heq2]
  intro e hΓ hab; exact TLA.or_elim e hab (h1 e hΓ) (h2 e hΓ)

theorem Entails_rcases_or_by_name (chosen : String) :
  letI idx := hyps.findIdx fun h => h.name == chosen
  (type_of% (@Entails_rcases_or_by_idx _ hyps goal name1 name2 a b idx)) :=
  Entails_rcases_or_by_idx _ _ _

end

section

variable (newName : String) {α : Sort v} {p : α → pred σ}

-- NOTE: This proof is slightly repetitive with the one above
theorem Entails_rcases_exists_by_idx (idx : Nat)
  (heq : hyps[idx]?.map NamedPred.pred = some (tlaExists p)) :
  letI hyps' := hyps.eraseIdx idx
  (∀ x : α, Entails (hyps' ++ [⟨newName, p x⟩]) goal) → Entails hyps goal := by
  unfold Entails
  simp only [List.map_append, repeatedAnd_append, ← impl_intro_add_r]
  intro h
  conv at h => enter [x, 2]; dsimp only [repeatedAnd, LentilLib.List.foldrD, List.map]
  rw [exists_put_witness_back] at h
  apply Entails_revert_by_idx idx
  simp at heq; rcases heq with ⟨r, heq1, heq2⟩
  rw [List.get?Internal_eq_getElem?, heq1]; simp only [Option.elim, heq2]; exact h

theorem Entails_rcases_exists_by_name (chosen : String) :
  letI idx := hyps.findIdx fun h => h.name == chosen
  (type_of% (@Entails_rcases_exists_by_idx _ hyps goal newName _ p idx)) :=
  Entails_rcases_exists_by_idx _ _

end

end

private def rcasesTacDSimps : Array Name :=
  #[``List.findIdx, ``List.findIdx.go, ``List.get?Internal,
  ``List.eraseIdx, ``List.cons_append, ``List.nil_append,
  ``String.reduceBEq, ``String.reduceBNe,
  ``or, ``and, ``not, ``cond_true, ``cond_false]

-- FIXME: The naming issue might be partially resolved by using indices?
/-- Generate a name for the hyp slot consumed by this pattern: idents land their
    own name; `_` and tuples get fresh hygienic names that may be re-targeted on
    the recursive call. -/
private def nameStrForPat (pat : TSyntax `rcasesPat) : TacticM String := do
  match pat with
  | `(rcasesPat| $name:ident) => return toString name.getId
  | _ =>
    let freshName ← mkFreshUserName `h
    -- Use something that cannot be a valid identifier to avoid accidental collision
    return "-" ++ toString freshName

/-- Unwrap a `rcasesPatLo` to a single `rcasesPat`, rejecting `: ty` ascriptions.
    A genuine `|` alternation is re-wrapped as a parenthesized `rcasesPat`, so it
    can be carried uniformly and later recognized by `asAlternationOpt`. -/
private def unwrapPatLo (p : TSyntax ``Lean.Parser.Tactic.rcasesPatLo) : TacticM (TSyntax `rcasesPat) := do
  match p with
  | `(rcasesPatLo| $_:rcasesPatMed : $_:term) =>
    throwError "tla_rcases: type ascription ': ty' is not supported"
  | `(rcasesPatLo| $med:rcasesPatMed) =>
    match med with
    | `(rcasesPatMed| $ps:rcasesPat|*) =>
      let elems := ps.getElems
      if elems.size == 0 then throwError "tla_rcases: empty pattern"
      else if elems.size == 1 then return elems[0]!
      else `(rcasesPat| ( $med:rcasesPatMed ))
    | _ => throwError "tla_rcases: unexpected rcasesPatMed shape"
  | _ => throwError "tla_rcases: unexpected rcasesPatLo shape"

/-- If `pat` is a parenthesized alternation `(p₁ | p₂ | …)` with at least two
    branches, return its branches; otherwise `none`. -/
private def asAlternationOpt (pat : TSyntax `rcasesPat) : Option (Array (TSyntax `rcasesPat)) :=
  match pat with
  | `(rcasesPat| ( $lo:rcasesPatLo )) =>
    match lo with
    | `(rcasesPatLo| $med:rcasesPatMed) =>
      match med with
      | `(rcasesPatMed| $ps:rcasesPat|*) =>
        let elems := ps.getElems
        if elems.size ≥ 2 then some elems else none
      | _ => none
    | _ => none
  | _ => none

-- FIXME: There is some back and forth conversion of `List` and `Array`, and ideally
-- the list of patterns should only be processed once. They should be refactored
-- for a more efficient implementation in the future.
/-- Split tuple sub-patterns into (head, tail) with right-associative wrapping
    for n > 2: `[p₁, p₂, …, pₙ]` becomes `(p₁, ⟨p₂, …, pₙ⟩)`. -/
private def splitBinaryRightAssoc (pats : Array (TSyntax ``Lean.Parser.Tactic.rcasesPatLo))
    : TacticM (TSyntax `rcasesPat × TSyntax `rcasesPat) := do
  match pats.toList with
  | [] => throwError "tla_rcases: empty tuple ⟨⟩ is not supported"
  | [_] => throwError "tla_rcases: unary tuple ⟨..⟩ is not supported; drop the brackets"
  | [p1, p2] => return (← unwrapPatLo p1, ← unwrapPatLo p2)
  | p1 :: rest =>
    let restArr := rest.toArray
    let tup ← `(rcasesPat| ⟨ $[$restArr],* ⟩)
    return (← unwrapPatLo p1, tup)

/-- Split alternation branches into (head, tail) with right-associative wrapping
    for n > 2: `[b₁, b₂, …, bₙ]` becomes `(b₁, (b₂ | … | bₙ))`. -/
private def splitAltRightAssoc (branches : Array (TSyntax `rcasesPat))
    : TacticM (TSyntax `rcasesPat × TSyntax `rcasesPat) := do
  match branches.toList with
  | [] | [_] => throwError "tla_rcases: alternation needs at least two branches"
  | [b1, b2] => return (b1, b2)
  | b1 :: rest =>
    let restArr := rest.toArray
    let tail ← `(rcasesPat| ( $[$restArr]|* ))
    return (b1, tail)

/-- The number of syntax nodes in `stx`; used as a recursion-fuel bound when
    destructuring `rcasesPat` patterns (each sub-pattern is strictly smaller). -/
def syntaxNodeCount : Syntax → Nat
  | .node _ _ args => args.foldl (fun acc s => acc + syntaxNodeCount s) 1
  | _ => 1

/-- Destructure the proof-mode hypothesis at `currentHyp` against `pat`.
    Precondition: the goal list contains exactly one goal — every caller
    enforces this by running through `focus` or `Tactic.run`. `fuel` bounds the
    pattern-nesting depth.

    A tuple `⟨..⟩` destructures `tlaAnd` / `tlaExists`; a parenthesized
    alternation `(.. | ..)` case-splits a `tlaOr`, producing two subgoals. -/
def tlaRcasesCoreFocused (fuel : Nat) (currentHyp : TemporalHypLoc)
    (pat : TSyntax `rcasesPat) : TacticM Unit := do
  match fuel with
  | 0 => throwError "tla_rcases: pattern is nested too deeply"
  | fuel + 1 =>
  -- FIXME: This handling also appears in the implementation of `tla_specialize`,
  -- so maybe reuse it?
  let some (_, hyps) ← recognizeEntailsHypsFromGoal | throwError "tla_rcases: failed to read the hypotheses from the goal"
  let (currentHypStr, pred) ← findByTemporalHypLoc hyps currentHyp "tla_rcases" "the goal's Entails list"
  match pat with
  | `(rcasesPat| $name:ident) =>
    let nameStr := toString name.getId
    -- Essentially renaming
    if nameStr != currentHypStr then
      let currentHypStx ← quoteTemporalHypLoc currentHyp
      evalTactic <| ← `(tactic| tla_rename $currentHypStx:temporalHypLoc => $name:ident)
  | `(rcasesPat| _) =>
    -- FIXME: This is not very good, since the generated names are not readable.
    -- A better design should be to only support `-` at the tail positions.
    pure ()
  | `(rcasesPat| -) =>
    -- Clear the targeted hypothesis. Works at any nesting depth because the
    -- name was already resolved to `currentHypStr` above.
    tlaClearByName [currentHypStr]
  | `(rcasesPat| ⟨ $pats,* ⟩) =>
    let (pat1, pat2) ← splitBinaryRightAssoc pats.getElems
    match_expr pred with
    | TLA.tlaAnd _ _ _ =>
      let n1Str ← nameStrForPat pat1
      let n2Str ← nameStrForPat pat2
      -- Inline `hpred := by rfl` so Lean can pin down the implicit `a, b` at
      -- the time `refine` is elaborated (they don't otherwise appear in the
      -- visible conclusion).
      let thm := if currentHyp matches .byName .. then ``Entails_rcases_and_by_name else ``Entails_rcases_and_by_idx
      evalTactic <| ← `(tactic| refine $(mkIdent thm) ($(quote n1Str)) ($(quote n2Str))
          ($(quoteTemporalHypLocToTerm currentHyp)) (by rfl) ?_)
      postDSimpAfterApplyingReflectionTheorem rcasesTacDSimps
      -- The `refine` left a single goal; `pat1` may case-split it, so `pat2`
      -- must then be applied to every goal `pat1` produced.
      tlaRcasesCoreFocused fuel (.byName n1Str) pat1
      let perGoal ← (← getGoals).mapM fun g =>
        Tactic.run g (tlaRcasesCoreFocused fuel (.byName n2Str) pat2)
      setGoals perGoal.flatten
    | TLA.tlaExists _ _ _ =>
      let nInnerStr ← nameStrForPat pat2
      let thm := if currentHyp matches .byName .. then ``Entails_rcases_exists_by_name else ``Entails_rcases_exists_by_idx
      evalTactic <| ← `(tactic| refine $(mkIdent thm) ($(quote nInnerStr))
          ($(quoteTemporalHypLocToTerm currentHyp)) (by rfl) ?_; rintro $pat1)
      postDSimpAfterApplyingReflectionTheorem rcasesTacDSimps
      let perGoal ← (← getGoals).mapM fun g =>
        Tactic.run g (tlaRcasesCoreFocused fuel (.byName nInnerStr) pat2)
      setGoals perGoal.flatten
    | _ =>
      throwError "tla_rcases: cannot destructure pred {pred} with pattern {pat}"
  | _ =>
    match asAlternationOpt pat with
    | some branches =>
      let (pat1, pat2) ← splitAltRightAssoc branches
      match_expr pred with
      | TLA.tlaOr _ _ _ =>
        let n1Str ← nameStrForPat pat1
        let n2Str ← nameStrForPat pat2
        let thm := if currentHyp matches .byName .. then ``Entails_rcases_or_by_name else ``Entails_rcases_or_by_idx
        evalTactic <| ← `(tactic| refine $(mkIdent thm) ($(quote n1Str)) ($(quote n2Str))
            ($(quoteTemporalHypLocToTerm currentHyp)) (by rfl) ?_ ?_)
        postDSimpAfterApplyingReflectionTheorem rcasesTacDSimps
        -- We started focused on one goal, so `refine ?_ ?_` left exactly two:
        -- the `a`-branch and the `b`-branch. Recurse into each.
        match ← getGoals with
        | [g1, g2] =>
          let g1s ← Tactic.run g1 (tlaRcasesCoreFocused fuel (.byName n1Str) pat1)
          let g2s ← Tactic.run g2 (tlaRcasesCoreFocused fuel (.byName n2Str) pat2)
          setGoals (g1s ++ g2s)
        | _ => throwError "tla_rcases: expected exactly two subgoals after the or-split"
      | _ =>
        throwError "tla_rcases: cannot case-split pred {pred} with alternation {pat}"
    | none =>
      throwError "tla_rcases: unsupported pattern (use ident, '_', ⟨..⟩ tuples, or | alternations)"

/-- Run `tlaRcasesCoreFocused` on every current goal, collecting all resulting
    goals. Needed because an or-split multiplies goals, and sibling or
    subsequent patterns must then be applied to each of them. -/
def tlaRcasesCoreAllGoals (fuel : Nat) (currentHyp : TemporalHypLoc)
    (pat : TSyntax `rcasesPat) : TacticM Unit := do
  let perGoal ← (← getGoals).mapM fun g => Tactic.run g (tlaRcasesCoreFocused fuel currentHyp pat)
  setGoals perGoal.flatten

/-- Destructure the proof-mode hypothesis at `currentHyp` against `pat`, acting
    on the main goal and leaving any other goals untouched. This is the entry
    point; the recursive work happens in `tlaRcasesCoreFocused`. -/
def tlaRcasesCore (currentHyp : TemporalHypLoc) (pat : TSyntax `rcasesPat) : TacticM Unit :=
  -- The pattern's syntax-node count bounds the destructuring recursion depth.
  focus (tlaRcasesCoreFocused (syntaxNodeCount pat.raw + 1) currentHyp pat)

/--
`tla_rcases h with pat` destructures a temporal hypothesis in the proof-mode
context.

If `h : p ∧ q`, then
```lean
tla_rcases h with ⟨hp, hq⟩
```
removes `h` and adds `hp : p` and `hq : q`. If `h : ∃ x, P x`, then
```lean
tla_rcases h with ⟨x, hx⟩
```
introduces a Lean witness `x` and a temporal hypothesis `hx : P x`. If
`h : p ∨ q`, then
```lean
tla_rcases h with (hp | hq)
```
case-splits into two subgoals, with `hp : p` in the first and `hq : q` in the
second. A `-` pattern clears the targeted hypothesis:
```lean
tla_rcases h with -
tla_rcases h with ⟨ha, -⟩  -- destructure and discard the second conjunct
```
A numeric index can be used instead of a name:
```lean
tla_rcases 0 with ⟨hp, hq⟩
```
-/
syntax (name := tlaRcasesTac) "tla_rcases" temporalHypLoc " with " rcasesPat : tactic

elab_rules : tactic
  | `(tactic| tla_rcases $hyp:temporalHypLoc with $pat) => withMainContext do
    let hyp ← parseTemporalHypLoc hyp "tla_rcases: invalid syntax for hypothesis position"
    -- `tlaRcasesCore` already acts only on the main goal.
    tlaRcasesCore hyp pat

/--
`tla_obtain pat := t` adds the temporal fact proved by `t` and immediately
destructures it with `pat`.

For example, if `h : |-tla- (p ∧ q)`, then
```lean
tla_obtain ⟨hp, hq⟩ := h
```
adds `hp : p` and `hq : q` to the proof-mode context. If `t` proves an
existential predicate, the pattern may introduce a Lean witness together with
the temporal hypothesis for its body. A bare proof-mode hypothesis is
destructured in place; other terms are first added as a new temporal hypothesis.
-/
syntax (name := tlaObtainTac) "tla_obtain" rcasesPat " := " term : tactic

elab_rules : tactic
  | `(tactic| tla_obtain $pat:rcasesPat := $tm:term) => withMainContext do
    let some (_, hyps) ← recognizeEntailsHypsFromGoal
      | throwError "tla_obtain: failed to read the hypotheses from the goal"
    match ← temporalHypLocOfBareTermOpt hyps tm with
    | some loc => tlaRcasesCore loc pat
    | none =>
      let idx ← tlaHaveTerm default tm
      tlaRcasesCore (.byIdx idx) pat

/--
`tla_by_cases h : p` splits a proof-mode goal into the cases `h : p` and
`h : ¬ p`.

For example,
```lean
tla_by_cases hp : p
```
creates two goals. The first has the temporal hypothesis `hp : p`; the second
has `hp : ¬ p`.
-/
syntax (name := tlaByCasesTac) "tla_by_cases " ident " : " tlafml : tactic

macro_rules
  | `(tactic| tla_by_cases $h:ident : $p:tlafml) =>
    `(tactic| tla_obtain ($h | $h) := TLA.excluded_middle [tlafml| $p])

/--
`tla_rintro pat₁ pat₂ ...` introduces proof-mode goal binders like
`tla_intro`, but each introduced item may be immediately destructured.

For Lean binders and pure antecedents, the pattern is handled by Lean's
`rintro`. For a temporal implication, the antecedent is introduced as a new
temporal hypothesis and then destructured by `tla_rcases`.

For example, if the goal is `(p ∧ q) → r`, then
```lean
tla_rintro ⟨hp, hq⟩
```
adds `hp : p` and `hq : q` to the proof-mode context and changes the goal to
`r`. If the goal is `∀ x, P x`, then
```lean
tla_rintro x
```
introduces `x` as a Lean local and changes the goal to `P x`. A temporal
antecedent `p ∨ q` can be case-split with a parenthesized alternation:
```lean
tla_rintro (hp | hq)
```
introduces the antecedent and splits into two subgoals.
-/
syntax (name := tlaRintroTac) "tla_rintro" (ppSpace colGt rintroPat)+ : tactic

elab_rules : tactic
  | `(tactic| tla_rintro%$tk $[$pats:rintroPat]*) => do
    let tacNonTemporal (pat : TSyntax `rintroPat) : TacticM (TSyntax `tactic) := `(tactic| rintro $pat:rintroPat)
    let rintroPatIdent? (pat : TSyntax `rintroPat) : TacticM (Option Ident) := do
      match pat with
      | `(rintroPat| $name:ident) => return some name
      | _ => return none
    -- Introduce/destructure a single pattern on the current (single) main goal.
    let stepOne (pat : TSyntax `rintroPat) : TacticM Unit := do
      let isTemporal? ← tlaIntroCoreStep `rintroPat pat rintroPatIdent? "tla_rintro" tacNonTemporal
      if isTemporal? then
        -- FIXME: This "getting the last index" also appears frequently ...
        let some hypCount ← goalHypsLength
          | throwError "tla_rintro: failed to read the hypotheses after temporal introduction"
        match pat with
        | `(rintroPat| $rpat:rcasesPat) => tlaRcasesCore (.byIdx <| hypCount - 1) rpat
        | _ => throwError "tla_rintro: unsupported pattern (only rcasesPat is supported for `tla_rintro` temporal hypotheses)"
    -- Focus the main goal; a case-splitting pattern multiplies goals, and
    -- `focus` merges any resulting subgoals back ahead of the others.
    focus do
      for pat in pats, i in 0...* do
        let ctxRef := if i == 0 then Lean.mkNullNode #[tk, pat] else pat
        withTacticInfoContext ctxRef <| withRef pat do
          -- A previous pattern may have case-split the goal; apply this one to
          -- each of the resulting goals.
          let perGoal ← (← getGoals).mapM fun g => Tactic.run g (stepOne pat)
          setGoals perGoal.flatten

end TLA.ProofMode
