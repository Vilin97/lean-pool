/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean
import LeanPool.Lentil.Basic

/-! Gadgets for lifting a propositional theorem to the level of temporal logic. -/

namespace TLA.Lifting

open Lean Meta Core Elab LentilLib

/-- If `p : Prop`, then lift it to `⌞ p ⌟` of type `TLA.pred σ`; otherwise
    do nothing and return `p` (note that in this case, whether `p` is of type `TLA.pred σ`
    is not checked). -/
def liftPropToPurePred (σ p : Expr) : MetaM Expr := do
  trace[lentil.debug] "p is {p}"
  if ← Meta.isProp p then
    trace[lentil.debug] "lifted"
    -- do some very simple special checking
    if p.isTrue then
      mkAppOptM ``TLA.tla_true #[some σ]
    else if p.isFalse then
      mkAppOptM ``TLA.tla_false #[some σ]
    else
      mkAppOptM ``TLA.pure_pred #[some σ, some p]
  else
    pure p

partial def convertPropToTLAPredAux (alist : AssocList Expr Expr) (σ p : Expr) : MetaM Expr := do
  match_expr p with
  | And a b => do
    trace[lentil.debug] "And case: {a} and {b}"
    let a' ← go a ; let b' ← go b
    mkAppM ``TLA.tla_and #[a', b']
  | Or a b => do
    trace[lentil.debug] "Or case: {a} or {b}"
    let a' ← go a ; let b' ← go b
    mkAppM ``TLA.tla_or #[a', b']
  | Not a => do
    trace[lentil.debug] "Not case: not {a}"
    let a' ← go a
    mkAppM ``TLA.tla_not #[a']
  | Exists _ f => do
    trace[lentil.debug] "Exists case: ∃ {f}"
    -- here, do some simple checking
    let f ← whnfD f
    match f with
    | Expr.lam na a b bi =>
      let a' ← go a
      withLocalDecl na bi a' fun avar => do
        let b_ := b.instantiate1 avar
        let b' ← go b_
        let b'' ← mkLambdaFVars #[avar] b'
        mkAppM ``TLA.tla_exists #[b'']
    | _ =>
      let f' ← go f
      mkAppM ``TLA.tla_exists #[f']
  | _ =>
    -- `p` is not any propositional connective listed above
    match p with
    | Expr.forallE na a b bi =>
      -- `p` can be an implication or `∀`
      if p.isArrow then
        trace[lentil.debug] "Arrow case: {a} → {b}"
        let a' ← go a ; let b' ← go b
        mkAppM ``TLA.tla_implies #[a', b']
      else
        trace[lentil.debug] "Forall case: ∀ {a}, {b}"
        -- HMM slightly repetitive
        let a' ← go a
        withLocalDecl na bi a' fun avar => do
          let b_ := b.instantiate1 avar
          let b' ← go b_
          let b'' ← mkLambdaFVars #[avar] b'
          mkAppM ``TLA.tla_forall #[b'']
    | _ =>
      -- simply do a holistic replacement
      trace[lentil.debug] "Terminal case: {p}"
      pure <| p.replace alist.find?
where go (p : Expr) : MetaM Expr :=
  convertPropToTLAPredAux alist σ p >>= liftPropToPurePred σ

partial def convertPropToTLAPred (alist : AssocList Expr Expr) (σ p : Expr) : MetaM Expr :=
  convertPropToTLAPredAux alist σ p >>= liftPropToPurePred σ

inductive LiftingCase where
  /-- The case where the conclusion is a single `↔`. -/
  | Iff
  /-- The other cases, including those where the conclusion is a series of `→`. -/
  | Other
deriving Inhabited

instance : ToString LiftingCase where
  toString
    | LiftingCase.Iff => "Iff"
    | LiftingCase.Other => "Other"

private def guessWhereToStartAux (es xs : List Expr) : MetaM Nat :=
  match xs with
  | [] => pure 0
  | x :: xs' => if es.any x.occurs then pure xs.length else do
    -- NOTE: we might use `Meta.isProp` here to check, but we need to obtain `ty`, so anyway
    let ty ← inferType x
    if (← getLevel ty).isZero then guessWhereToStartAux (ty :: es) xs' else pure xs.length

/-- Given `thmStmt` being `x₁ → x₂ → ⋯ → xₙ`, find the longest suffix `xₘ → ⋯ → xₙ`
    such that each `xᵢ` is a `Prop` and independent. -/
private def guessWhereToStart (thmStmt : Expr) : MetaM Nat := do
  forallTelescope thmStmt fun xs body =>
    guessWhereToStartAux [body] xs.reverse.toList

/-- Convert a theorem statement to the level of temporal logic. Given the theorem statement
    and the name of the additional universe level (required by `σ` in `TLA.pred σ`),
    return the case for lifting and the converted statement. -/
partial def convertTheoremStatement (thmStmt : Expr) (uName : Name) : MetaM (LiftingCase × Expr) := do
  -- create a fresh state type `σ`
  let u := mkLevelSucc <| mkLevelParam uName
  -- NOTE: couldn't come up with a good way to avoid generating a fresh `σ` with a dagger, so just use `σ` here
  withLocalDecl `σ BinderInfo.implicit (.sort u) fun σ => do
    let pred ← mkAppM ``TLA.pred #[σ]
    let n ← guessWhereToStart thmStmt
    forallBoundedTelescope thmStmt n fun xs body => do
      trace[lentil.debug] "xs := {xs}, body := {body}"
      /- convert the things in `xs` according to need; for example,
         if `x` in `xs` has type `Prop`, then convert it to `TLA.pred σ` -/
      /- at the same time, associate things in `xs` with the converted things
         by returning an association list -/
      let (_, xs') ← xs.foldlM (fun (xspre, xs'_) x => do
        let ty ← inferType x
        -- remove typeclass arguments that are `Decidable` or alike
        if [``Decidable, ``DecidableEq, ``DecidablePred].any ty.getAppFn'.isConstOf then
          pure (xspre.push x, xs'_)
        else
          let fv := x.fvarId!
          let n ← fv.getUserName
          let bi ← fv.getBinderInfo
          let ty' ← do
            if ← Meta.isProp ty then
              pure ty
            else
              -- try replacing `Prop` with `TLA.pred σ` within `ty`
              trace[lentil.debug] "ty := {ty}"
              let res := ty.replace fun e => if e == .sort .zero then some pred else none
              trace[lentil.debug] "ty after replacement := {res}"
              pure res
          let ty' (yspre : Array Expr) := do pure <| ty'.replaceFVars xspre yspre
          pure (xspre.push x, xs'_.push (x, n, bi, ty'))) (#[], #[])
      /- FIXME: here, using such association list is very error-prone
         (may introduce unresolved fvar/mvar easily); any better solution? -/
      withLocalDecls (xs'.map Prod.snd) fun ys => do
        let alist := xs'.zipWith (fun (x, _) y => (x, y)) ys
        let alist := alist.toList.toAssocList'
        match_expr body with
        | Iff a b => do
          trace[lentil.debug] "a := {a}, b := {b}"
          let a' ← convertPropToTLAPred alist σ a
          let b' ← convertPropToTLAPred alist σ b
          trace[lentil.debug] "a' := {a'}, b' := {b'}"
          -- now get the statement to prove
          let thmStmt' ← mkAppM ``Eq #[a', b'] >>= mkForallFVars (Array.append #[σ] ys)
          pure (LiftingCase.Iff, thmStmt')
        | _ =>
          let body' ← convertPropToTLAPred alist σ body
          let thmStmt' ← mkAppM ``TLA.valid #[body'] >>= mkForallFVars (Array.append #[σ] ys)
          pure (LiftingCase.Other, thmStmt')

partial def liftTheorem (thmName : Name) (liftedThmName : Option Name)
  (tactic? : Option (TSyntax `term)) : MetaM Unit := do
  let info ← getConstInfo thmName
  let ty := info.type
  let lvlParams := info.levelParams
  trace[lentil.debug] "to-be-lifted theorem statement : {ty}"
  -- NOTE: `mkFreshUserName` does not seem to work well when generating names for universe levels
  let uName := mkUnusedName lvlParams `u
  let (lcase, ty') ← convertTheoremStatement ty uName
  trace[lentil.debug] "after conversion : {ty'}, case: {lcase}"
  if ty'.hasFVar || ty'.hasExprMVar then
    throwError "internal error: the converted result contains free variables or metavariables"
  -- now prove `ty'` using the theorem
  /- NOTE: it seems that directly manipulating the proof term of `thmName`
     does not work well, so again resort to `simpleProveTheorem` to prove -/
  let newThmName := liftedThmName.getD <| thmName.updatePrefix `TLA
  let noncomputable? := isNoncomputable (← getEnv) thmName
  let e ← mkIdent <$> mkFreshUserName `e
  let finalTac ← `(tactic| open Classical in (try solve
    | apply $(mkIdent <| `_root_ ++ thmName)
    | apply $(mkIdent thmName) ))   -- if not using `_root_.` then this may apply the theorem being proved!
  match lcase with
  | LiftingCase.Iff =>
    let defaultTac ← `(term| by intros ; funext $e ; apply $(mkIdent ``propext) ; $finalTac )
    simpleProveTheorem newThmName (uName :: lvlParams) ty'
      (tactic?.getD defaultTac) noncomputable?
  | LiftingCase.Other =>
    let defaultTac ← `(term| by intros ; (try intro $e:ident) ; $finalTac )
    simpleProveTheorem newThmName (uName :: lvlParams) ty'
      (tactic?.getD defaultTac) noncomputable?

end TLA.Lifting

/-- `#tla_lift thm₁ ... thmₙ` lifts (typically purely first-order) theorems
    `thm₁`, ... ,`thmₙ` to the temporal logic level. Each new theorem will
    have the prefix `TLA.` and the same suffix as before.

    For example, after executing ```#tla_lift Decidable.not_not```,
    there will be a new theorem named `TLA.not_not` in the environment. -/
syntax (name := tlaLiftTac) "#tla_lift" ident+ : command
/-- `#tla_lift thm => newthm` behaves like `#tla_lift`, but only lifts
    one theorem, while naming the new theorem as `newthm`. -/
syntax (name := tlaLiftSingleTac) "#tla_lift" ident ("=>" ident)? ("by" tactic)? : command

open Lean Elab Term in
elab_rules : command
  | `(command| #tla_lift $idts:ident* ) => Command.liftTermElabM do
    for idt in idts do
      -- FIXME: this approach prevents using shorter names after `open`, since it does not use `elabTerm`?
      let nm := idt.getId
      addTermInfo' idt (← Lean.mkConstWithLevelParams nm)
      TLA.Lifting.liftTheorem nm none none
  | `(command| #tla_lift $idt:ident $[=> $nm:ident]? $[by $tac:tactic]?) => Command.liftTermElabM do
    addTermInfo' idt (← Lean.mkConstWithLevelParams idt.getId)
    TLA.Lifting.liftTheorem idt.getId (nm.map (·.getId)) (← tac.mapM fun tac => `(term| by $tac:tactic ))
    if let some nm := nm then
      addTermInfo' nm (← Lean.mkConstWithLevelParams nm.getId)
