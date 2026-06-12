/-
Copyright (c) 2026 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

import Mathlib.Data.Nat.Prime.Defs
import Qq

/-! # Framework for primality certificates

The `prime_cert%` elaborator processes a sequence of *step groups* (e.g. `small`, `pock`, `pock3`).
A `PrimeDict` threads proof terms for already-certified primes through the ladder so later steps
can reference earlier ones. Each step group is written `key spec` or `key {spec₁; spec₂; ...}`; the
syntax for the individual `key`s is declared alongside the corresponding certification method (see
`smallSpec`, `pockSpec`, `pock3Spec`) and the `prime_cert%` elaborator dispatches on the leading
keyword.
-/

open Lean Meta Elab Command Qq

namespace PrimeCert.Meta

/-- We store the metavariable assigned to each certified prime. -/
abbrev PrimeDict := Std.HashMap Nat Expr

/-- Look up the proof term for the prime `n`, throwing if it has not yet been certified. -/
def PrimeDict.getM (dict : PrimeDict) (n : ℕ) : MetaM Expr := do
  let .some entry := dict.get? n
    | throwError s!"Primality not yet certified for {n}"
  return entry

/-- A method to climb one step in the ladder: given the syntax for a single step and the dictionary
of previously proved primes, it certifies a new prime. -/
abbrev PrimeCertMethod (syntaxName : Name) :=
  TSyntax syntaxName → PrimeDict → MetaM (Nat × (N : Q(Nat)) × Q(($N).Prime))

/-- Syntax category for a group of steps in the certificate ladder, e.g. `small {2; 3}` or
`pock (N, root, F₁)`. -/
declare_syntax_cat stepGroup

/-- Convert a syntax category name to a ``TSyntax `stx`` dynamically. -/
def _root_.Lean.Name.toSyntaxCat (cat : Name) : TSyntax `stx :=
  .mk <| mkNode `Lean.Parser.Syntax.cat #[mkIdent cat, mkNullNode]

/-- Build a `docComment` node carrying the given text, so generated `syntax` commands have a
documentation string (required by mathlib's `docBlame` linter). -/
def mkStepGroupDoc (text : String) : TSyntax `Lean.Parser.Command.docComment :=
  .mk <| mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (text ++ " -/")]

/-- Declare the syntax for a step group keyed by `key`, whose individual steps are parsed by the
syntax category `spec`. This produces both the single-step and the braced multi-step forms:
```lean
syntax "pock" pockSpec : stepGroup
syntax "pock" "{" pockSpec;+ "}" : stepGroup
```
-/
def declareStepGroupSyntax (key : String) (spec : Name) : CommandElabM Unit := do
  have spec := spec.toSyntaxCat
  let doc1 := mkStepGroupDoc s!"A single `{key}` step in a certificate ladder."
  let doc2 := mkStepGroupDoc s!"A braced group of `{key}` steps in a certificate ladder."
  elabCommand =<< `(command| $doc1:docComment syntax $(quote key):str $spec : stepGroup)
  elabCommand =<<
    `(command| $doc2:docComment syntax $(quote key):str "{" sepBy1($spec,"; ") "}" : stepGroup)

/-- Read the leading keyword and the individual step syntaxes from a parsed `stepGroup`.
A braced group parses as `sepBy1(spec, "; ")`, whose children alternate step / separator, so we
keep the even-indexed children. -/
def stepGroupParts (stx : TSyntax `stepGroup) : CoreM (String × Array Syntax) := do
  match stx.raw with
  | .node _ _ #[.atom _ key, step] => return (key, #[step])
  | .node _ _ #[.atom _ key, _, .node _ _ steps, _] =>
    let mut elems : Array Syntax := #[]
    for h : i in [0:steps.size] do
      if i % 2 == 0 then elems := elems.push steps[i]
    return (key, elems)
  | _ => throwUnsupportedSyntax

/-- Run a `PrimeCertMethod` on every step of a group, threading the dictionary and recording each
newly certified prime. Returns the updated dictionary together with the last prime certified. -/
def runMethod {spec : Name} (method : PrimeCertMethod spec) (steps : Array Syntax)
    (dict : PrimeDict) : TermElabM (PrimeDict × Nat) := do
  let mut dict := dict
  let mut goal : ℕ := 0
  for step in steps do
    let ⟨n, nE, pf⟩ ← method ⟨step⟩ dict
    goal := n
    let mVar ← mkFreshExprMVar q(Nat.Prime $nE) default <| .mkSimple s!"prime_{n}"
    dict := dict.insert n mVar
    mVar.mvarId!.assign pf
  return (dict, goal)

end PrimeCert.Meta
