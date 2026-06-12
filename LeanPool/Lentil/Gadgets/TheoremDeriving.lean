/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.Expr

/-! Gadgets for providing different variants of a proven theorem. -/

namespace TLA.Deriving

open Lean Meta Core Elab TLA.Expr LentilLib

-- does not assume dependency from `ps` to `q`
/-- Assemble premises and a conclusion under a shared context `Γ`. -/
def assembleUnderCommonContextShape (σ : Expr) (ps : List Expr) (q : Expr) : MetaM Expr := do
  withLocalDeclD `Γ (← mkAppM ``TLA.pred #[σ]) fun Γ => do
    let ps' ← ps.toArray.mapM fun p => mkAppM ``TLA.predImplies #[Γ, p]
    let q' ← mkAppM ``TLA.predImplies #[Γ, q]
    let body ← mkArrowN ps' q'
    mkForallFVars #[Γ] body

/-- Assemble a list of premise predicates and a conclusion into the arrow chain
    of separated `predImplies`/`valid` statements used by `tla_derive`. -/
def assembleSeparatedPredImplications (ps : List Expr) (q : Expr) : MetaM Expr := do
  let build p := do
    let (ps, q) ← simplify [] p
    match List.getLast? ps with
    | none => mkAppM ``TLA.valid #[q]
    | some p =>
      let ps := List.dropLast ps
      let conj ← ps.foldrM (fun pp conj => mkAppM ``TLA.tlaAnd #[pp, conj]) p
      mkAppM ``TLA.predImplies #[conj, q]
  let ps' ← ps.mapM build
  let q' ← build q
  let res ← mkArrowN ps'.toArray q'
  pure res
where
  /-- Simplify a premise list and conclusion before assembling the implication chain. -/
  simplify (ps : List Expr) (q : Expr) : MetaM (List Expr × Expr) := do
    -- currently only do very simple simplification:
    -- if `p` is empty while `q` is `alwaysImplies` then turn it into `tlaImplies`
    -- if `q` is `tlaImplies` then split it into parts
    -- FIXME: might enhance this to allow definitionally equal pattern matching, like the one in `Qq`?
    match_expr q with
    | TLA.alwaysImplies _ a b =>
      if ps.isEmpty then
        -- turn `alwaysImplies a b` into `tlaImplies a b` and split that
        let q' ← mkAppM ``TLA.tlaImplies #[a, b]
        let (ps', q'') ← splitImplicationsIntoParts q'
        pure (ps', q'')
      else
        pure (ps, q)
    | TLA.tlaImplies _ _ _ =>
      let (ps', q') ← splitImplicationsIntoParts q
      pure (ps ++ ps', q')
    | _ => pure (ps, q)

-- inspired by how `to_additive` is implemented in Mathlib
/-- For a TLA theorem whose conclusion is a single `TLA.predImplies` or
    `TLA.valid`, this function automatically derives its several equivalent
    or weakened versions, which might be easier to use elsewhere.

    For example, consider the following statement:
    ```
    |-tla- ((p' ⇒ p) → (q ⇒ q') → (p ↝ q) ⇒ (p' ↝ q'))
    ```

    One useful, but weaker version is:
    ```
    (p') |-tla- (p) → (q) |-tla- (q') → (p ↝ q) |-tla- (p' ↝ q')
    ```
    which is derived by repeatly applying `impl_decouple`, `impl_intro` and `always_intro`.

    Another useful and equivalent version is:
    ```
    ∀ Γ, (Γ) |-tla- (p' ⇒ p) → (Γ) |-tla- (q ⇒ q') → (Γ) |-tla- ((p ↝ q) ⇒ (p' ↝ q'))
    ```
    which can be used in case we want to keep the context `Γ`.
-/
def deriveForPredImpliesOrValid (nm : Name) : CoreM Unit := do
  -- get the type of the statement directly from its `ConstInfo`
  let info ← getConstInfo nm
  let ty := info.type
  let lvlParams := info.levelParams
  let noncomputable? := isNoncomputable (← getEnv) nm
  MetaM.run' do
    let (thmName1, thmStmt1, thmName2, thmStmt2) ←
      forallTelescope ty fun xs body => do
        let (ps, q) ← splitPredImpliesIntoParts body
        let .some σ := peekStateType body | unreachable!
        -- here we list the theorem statements to be automatically derived
        let thmStmt1 ← assembleUnderCommonContextShape σ ps q
        let thmStmt1 ← mkForallFVars xs thmStmt1
        let thmName1 := nm ++ `with_context

        let thmStmt2 ← assembleSeparatedPredImplications ps q
        let thmStmt2 ← mkForallFVars xs thmStmt2
        let thmName2 := nm ++ `weakened
        pure (thmName1, thmStmt1, thmName2, thmStmt2)

    simpleProveTheorem thmName1 lvlParams thmStmt1
      -- HACK: sometimes `aesop` is powerful enough to solve the goal;
      -- in that case, the `have` may introduce something with unresolvable universe levels
      -- since the thing brought by `have` is not used in the proof term.
      -- to avoid this, we add a separate branch where there is no `have`.
      (← `(term| by solve
        | tlaNontemporalSimp; aesop
        | have := @$(mkIdent nm); tlaNontemporalSimp; aesop)) noncomputable?
    simpleProveTheorem thmName2 lvlParams thmStmt2
      (← do
        let htmp ← mkIdent <$> mkFreshUserName `htmp
        let htmp' ← mkIdent <$> mkFreshUserName `htmp'
        let introNames ← ty.getForallBinderNames.toArray.mapM (mkIdent <$> mkFreshUserName ·)
        `(term| by solve
        | tlaNontemporalSimp; aesop
        | intro $introNames*; have $htmp := @$(mkIdent nm) $introNames*
          (try rw [← TLA.impl_intro] at $htmp:ident)
          repeat (first
            | (solve
              | tlaNontemporalSimp; aesop)
            | have $htmp' := @$htmp; clear $htmp; have $htmp := @TLA.impl_decouple _ _ _ $htmp'; clear $htmp'
            | unfold TLA.alwaysImplies at $htmp:ident
            | rw [← TLA.always_intro] at $htmp:ident
            | intro $htmp':ident; specialize $htmp $htmp'; clear $htmp'
            | rw [TLA.and_valid_split, _root_.and_imp] at $htmp:ident
          ))) noncomputable?

end TLA.Deriving

/--
For a TLA theorem with this attribute in the form of a single
`TLA.predImplies` or `TLA.valid`, its different variants will be derived.
See the docstring of `TLA.Deriving.deriveForPredImpliesOrValid` for more details.
-/
syntax (name := tlaDerive) "tla_derive" : attr

open Lean TLA.Deriving in
initialize registerBuiltinAttribute {
  name := `tlaDerive
  descr := ""
  add := fun src _ _ => do _ ← deriveForPredImpliesOrValid src
  applicationTime := .afterTypeChecking
}
