/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
import Lean
import LeanPool.Lentil.Tactics.Basic

open Lean

namespace TLA

/-!
This file implements a finite-window reduction for local TLA obligations.

The older `simp_finite_exec_goal` tactic unfolds a TLA formula on an explicit
trace, then tries to discover and generalize the finitely many trace cells that
remain. That is fragile: the tactic has to rediscover finite dependence from
the unfolded goal shape.

Here the finite dependence is part of the certificate. A `FiniteWindow p n`
contains a curried finite predicate `core` over exactly `n` states, together
with a theorem saying that evaluating `p` on a trace is equivalent to evaluating
`core` on the first `n` states of that trace. The tactic uses instance search to
find a `HasFiniteWindow p n`, applies the certificate theorem, introduces the
`n` state variables, and simplifies the resulting `core`.

For sequents, `tlaFiniteWindow` first changes `p |-tla- q` by definitional
equality into `|-tla- p → q`, so the rest of the pipeline only handles validity
goals.
-/

/-- A curried predicate over `n` consecutive states.

For example, `IteratedHomPred 2 σ` reduces to `σ → σ → ULift Prop`. The `ULift`
in the base case is deliberate: for universe-polymorphic `σ : Type u`, the
successor case lives in `Type u`, so the base proposition also has to be lifted
into `Type u`. The user-facing goals are later simplified through `.down`. -/
def IteratedHomPred : Nat → Type u → Type u
  | 0, _ => ULift.{u} Prop
  | n + 1, σ => σ → IteratedHomPred n σ

namespace IteratedHomPred

/-- Evaluate a curried finite predicate on the first `n` states of a trace. -/
def evalExec {σ : Type u} : (n : Nat) → IteratedHomPred n σ → exec σ → Prop
  | 0, p, _ => p.down
  | n + 1, p, e => evalExec n (p (e 0)) (e.drop 1)

/-- View an `n`-state core as an `m`-state core when `n ≤ m`, ignoring the
additional trailing states. This is used to combine two formulas with different
window sizes into a common `max` window. -/
def weaken {σ : Type u} : (n m : Nat) → n ≤ m → IteratedHomPred n σ → IteratedHomPred m σ
  | 0, 0, _, p => p
  | 0, m + 1, _, p => fun _ => weaken 0 m (Nat.zero_le m) p
  | n + 1, 0, h, _ => False.elim (Nat.not_succ_le_zero n h)
  | n + 1, m + 1, h, p => fun s => weaken n m (Nat.le_of_succ_le_succ h) (p s)

/-- Weakening does not change how a core evaluates on any trace. -/
theorem evalExec_weaken {σ : Type u} :
    ∀ {n m : Nat} (h : n ≤ m) (p : IteratedHomPred n σ) (e : exec σ),
      evalExec m (weaken n m h p) e ↔ evalExec n p e
  | 0, 0, _, _, _ => Iff.rfl
  | 0, m + 1, _, p, e => evalExec_weaken (Nat.zero_le m) p (e.drop 1)
  | n + 1, 0, h, _, _ => False.elim (Nat.not_succ_le_zero n h)
  | _ + 1, _ + 1, h, p, e =>
    evalExec_weaken (Nat.le_of_succ_le_succ h) (p (e 0)) (e.drop 1)

/- Pointwise logical constructors for cores of the same width, with lemmas
describing their behavior under `evalExec`. Binary connectives and binders
share the same recursion shape, so the generic constructors below keep the
named logical constructors small. -/

/-- Negate an iterated finite-window predicate. -/
def mkNot {σ : Type u} : (n : Nat) → IteratedHomPred n σ → IteratedHomPred n σ
  | 0, p => ULift.up (¬ p.down)
  | n + 1, p => fun s => mkNot n (p s)

theorem evalExec_mkNot {σ : Type u} :
    ∀ (n : Nat) (p : IteratedHomPred n σ) (e : exec σ),
      evalExec n (mkNot n p) e ↔ ¬ evalExec n p e
  | 0, _, _ => Iff.rfl
  | n + 1, p, e => evalExec_mkNot n (p (e 0)) (e.drop 1)

/-- Combine two iterated finite-window predicates with a binary connective. -/
def mkBinary {σ : Type u} (op : Prop → Prop → Prop) :
    (n : Nat) → IteratedHomPred n σ → IteratedHomPred n σ →
    IteratedHomPred n σ
  | 0, p, q => ULift.up (op p.down q.down)
  | n + 1, p, q => fun s => mkBinary op n (p s) (q s)

theorem evalExec_mkBinary {σ : Type u} (op : Prop → Prop → Prop) :
    ∀ (n : Nat) (p q : IteratedHomPred n σ) (e : exec σ),
      evalExec n (mkBinary op n p q) e ↔ op (evalExec n p e) (evalExec n q e)
  | 0, _, _, _ => Iff.rfl
  | n + 1, p, q, e => evalExec_mkBinary op n (p (e 0)) (q (e 0)) (e.drop 1)

/-- Conjoin two iterated finite-window predicates. -/
def mkAnd {σ : Type u} : (n : Nat) → IteratedHomPred n σ → IteratedHomPred n σ →
    IteratedHomPred n σ :=
  mkBinary (fun p q => p ∧ q)

theorem evalExec_mkAnd {σ : Type u} :
    ∀ (n : Nat) (p q : IteratedHomPred n σ) (e : exec σ),
      evalExec n (mkAnd n p q) e ↔ evalExec n p e ∧ evalExec n q e :=
  evalExec_mkBinary (fun p q => p ∧ q)

/-- Disjoin two iterated finite-window predicates. -/
def mkOr {σ : Type u} : (n : Nat) → IteratedHomPred n σ → IteratedHomPred n σ →
    IteratedHomPred n σ :=
  mkBinary (fun p q => p ∨ q)

theorem evalExec_mkOr {σ : Type u} :
    ∀ (n : Nat) (p q : IteratedHomPred n σ) (e : exec σ),
      evalExec n (mkOr n p q) e ↔ evalExec n p e ∨ evalExec n q e :=
  evalExec_mkBinary (fun p q => p ∨ q)

/-- Form the implication of two iterated finite-window predicates. -/
def mkImplies {σ : Type u} : (n : Nat) → IteratedHomPred n σ → IteratedHomPred n σ →
    IteratedHomPred n σ :=
  mkBinary (fun p q => p → q)

theorem evalExec_mkImplies {σ : Type u} :
    ∀ (n : Nat) (p q : IteratedHomPred n σ) (e : exec σ),
      evalExec n (mkImplies n p q) e ↔ (evalExec n p e → evalExec n q e) :=
  evalExec_mkBinary (fun p q => p → q)

/-- Bind a quantifier over an iterated finite-window predicate. -/
def mkBinder {σ : Type u} {α : Sort v} (op : (α → Prop) → Prop) :
    (n : Nat) → (α → IteratedHomPred n σ) →
    IteratedHomPred n σ
  | 0, p => ULift.up (op fun x => (p x).down)
  | n + 1, p => fun s => mkBinder op n (fun x => p x s)

theorem evalExec_mkBinder {σ : Type u} {α : Sort v} (op : (α → Prop) → Prop) :
    ∀ (n : Nat) (p : α → IteratedHomPred n σ) (e : exec σ),
      evalExec n (mkBinder op n p) e ↔ op (fun x => evalExec n (p x) e)
  | 0, _, _ => Iff.rfl
  | n + 1, p, e => evalExec_mkBinder op n (fun x => p x (e 0)) (e.drop 1)

/-- Universally quantify an iterated finite-window predicate. -/
def mkForall {σ : Type u} {α : Sort v} : (n : Nat) → (α → IteratedHomPred n σ) →
    IteratedHomPred n σ :=
  mkBinder (fun p => ∀ x, p x)

theorem evalExec_mkForall {σ : Type u} {α : Sort v} :
    ∀ (n : Nat) (p : α → IteratedHomPred n σ) (e : exec σ),
      evalExec n (mkForall n p) e ↔ ∀ x, evalExec n (p x) e :=
  evalExec_mkBinder (fun p => ∀ x, p x)

/-- Existentially quantify an iterated finite-window predicate. -/
def mkExists {σ : Type u} {α : Sort v} : (n : Nat) → (α → IteratedHomPred n σ) →
    IteratedHomPred n σ :=
  mkBinder (fun p => ∃ x, p x)

theorem evalExec_mkExists {σ : Type u} {α : Sort v} :
    ∀ (n : Nat) (p : α → IteratedHomPred n σ) (e : exec σ),
      evalExec n (mkExists n p) e ↔ ∃ x, evalExec n (p x) e :=
  evalExec_mkBinder (fun p => ∃ x, p x)

end IteratedHomPred

/-- Universal closure of a finite core over all its state arguments. -/
def IteratedForall {σ : Type u} : (n : Nat) → IteratedHomPred n σ → Prop
  | 0, p => p.down
  | n + 1, p => ∀ s, IteratedForall n (p s)

/-- A universally closed finite core holds on the first `n` states of every
trace. -/
theorem IteratedForall.evalExec {σ : Type u} :
    ∀ {n : Nat} {p : IteratedHomPred n σ}, IteratedForall n p →
      ∀ e, IteratedHomPred.evalExec n p e
  | 0, _, h, _ => h
  | _ + 1, _, h, e => IteratedForall.evalExec (h (e 0)) (e.drop 1)

/-- `FiniteWindow p n` means that `p` can be represented as a predicate over
the first `n` states of a trace. -/
structure FiniteWindow {σ : Type u} (p : pred σ) (n : Nat) where
  /-- The curried finite core over `n` states. -/
  core : IteratedHomPred n σ
  iff_of_eval : ∀ e, p e ↔ IteratedHomPred.evalExec n core e

/-- A computable finite-window certificate.

The window is an output parameter so that instance synthesis can compute a
canonical bound for `p`. The certificate itself is data, because `tlaFiniteWindow`
uses its `core` field to produce the finite-state goal. -/
class HasFiniteWindow {σ : Type u} (p : pred σ) (n : outParam Nat) where
  /-- The finite-window certificate for the predicate. -/
  finite : FiniteWindow p n

/-- Extract the semantic certificate from the tactic-facing class. Keeping this
as a definition, not an instance for `FiniteWindow`, prevents arbitrary
`FiniteWindow` facts from becoming part of instance search. -/
def finiteWindowOfHasFiniteWindow {σ : Type u} {p : pred σ} {n : Nat}
    [h : HasFiniteWindow p n] : FiniteWindow p n :=
  h.finite

/-- Soundness theorem used by `tlaFiniteWindow`: proving the finite core for
all choices of its state arguments proves validity of the original predicate. -/
theorem FiniteWindow.valid_of_forall {σ : Type u} {p : pred σ} {n : Nat}
    (h : FiniteWindow p n) : IteratedForall n h.core → valid p := by
  intro hcore e
  exact (h.iff_of_eval e).mpr (IteratedForall.evalExec hcore e)

theorem HasFiniteWindow.valid_of_forall {σ : Type u} {p : pred σ} {n : Nat}
    [h : HasFiniteWindow p n] : IteratedForall n h.finite.core → valid p :=
  h.finite.valid_of_forall

/- Base finite-window certificates. -/

/-- Finite-window certificate for a pure predicate. -/
def finiteWindowPure {σ : Type u} (P : Prop) : FiniteWindow (purePred (α := σ) P) 0 where
  core := ULift.up P
  iff_of_eval := by simp [purePred, statePred, IteratedHomPred.evalExec]

instance hasFiniteWindowPure {σ : Type u} (P : Prop) : HasFiniteWindow (purePred (α := σ) P) 0 where
  finite := finiteWindowPure P

/-- Finite-window certificate for `⊤`. -/
def finiteWindowTrue {σ : Type u} : FiniteWindow (tlaTrue (α := σ)) 0 where
  core := ULift.up True
  iff_of_eval := by simp [tlaTrue, purePred, statePred, IteratedHomPred.evalExec]

instance hasFiniteWindowTrue {σ : Type u} : HasFiniteWindow (tlaTrue (α := σ)) 0 where
  finite := finiteWindowTrue

/-- Finite-window certificate for `⊥`. -/
def finiteWindowFalse {σ : Type u} : FiniteWindow (tlaFalse (α := σ)) 0 where
  core := ULift.up False
  iff_of_eval := by simp [tlaFalse, purePred, statePred, IteratedHomPred.evalExec]

instance hasFiniteWindowFalse {σ : Type u} : HasFiniteWindow (tlaFalse (α := σ)) 0 where
  finite := finiteWindowFalse

/-- Finite-window certificate for a state predicate. -/
def finiteWindowState {σ : Type u} (p : σ → Prop) : FiniteWindow (statePred p) 1 where
  core := fun s => ULift.up (p s)
  iff_of_eval := by simp [statePred, IteratedHomPred.evalExec]

instance hasFiniteWindowState {σ : Type u} (p : σ → Prop) : HasFiniteWindow (statePred p) 1 where
  finite := finiteWindowState p

/-- Finite-window certificate for an action predicate. -/
def finiteWindowAction {σ : Type u} (a : action σ) : FiniteWindow (actionPred a) 2 where
  core := fun s s' => ULift.up (a s s')
  iff_of_eval := by simp [actionPred, IteratedHomPred.evalExec, exec.drop]

instance hasFiniteWindowAction {σ : Type u} (a : action σ) : HasFiniteWindow (actionPred a) 2 where
  finite := finiteWindowAction a

/-- Finite-window certificate for an enabledness predicate. -/
def finiteWindowEnabled {σ : Type u} (a : action σ) : FiniteWindow (tlaEnabled a) 1 :=
  finiteWindowState (enabled a)

instance hasFiniteWindowEnabled {σ : Type u} (a : action σ) : HasFiniteWindow (tlaEnabled a) 1 where
  finite := finiteWindowEnabled a

/- Compositional finite-window certificates. Binary connectives first weaken
both cores to the common `max` window, then combine them pointwise. -/

/-- Finite-window certificate for a binary connective of predicates. -/
def finiteWindowBinary {σ : Type u} (op : Prop → Prop → Prop) (p q : pred σ) (n m : Nat)
    (hp : FiniteWindow p n) (hq : FiniteWindow q m) :
    FiniteWindow (fun e => op (p e) (q e)) (max n m) where
  core := IteratedHomPred.mkBinary op (max n m)
    (IteratedHomPred.weaken n (max n m) (Nat.le_max_left n m) hp.core)
    (IteratedHomPred.weaken m (max n m) (Nat.le_max_right n m) hq.core)
  iff_of_eval := by
    intro e
    rw [hp.iff_of_eval e, hq.iff_of_eval e]
    rw [IteratedHomPred.evalExec_mkBinary]
    rw [IteratedHomPred.evalExec_weaken, IteratedHomPred.evalExec_weaken]

/-- Finite-window certificate for a conjunction. -/
def finiteWindowAnd {σ : Type u} (p q : pred σ) (n m : Nat)
    (hp : FiniteWindow p n) (hq : FiniteWindow q m) :
    FiniteWindow (tlaAnd p q) (max n m) :=
  finiteWindowBinary (fun p q => p ∧ q) p q n m hp hq

instance hasFiniteWindowAnd {σ : Type u} (p q : pred σ) (n m : Nat)
    [HasFiniteWindow p n] [HasFiniteWindow q m] :
    HasFiniteWindow (tlaAnd p q) (max n m) where
  finite := finiteWindowAnd p q n m finiteWindowOfHasFiniteWindow finiteWindowOfHasFiniteWindow

/-- Finite-window certificate for a disjunction. -/
def finiteWindowOr {σ : Type u} (p q : pred σ) (n m : Nat)
    (hp : FiniteWindow p n) (hq : FiniteWindow q m) :
    FiniteWindow (tlaOr p q) (max n m) :=
  finiteWindowBinary (fun p q => p ∨ q) p q n m hp hq

instance hasFiniteWindowOr {σ : Type u} (p q : pred σ) (n m : Nat)
    [HasFiniteWindow p n] [HasFiniteWindow q m] :
    HasFiniteWindow (tlaOr p q) (max n m) where
  finite := finiteWindowOr p q n m finiteWindowOfHasFiniteWindow finiteWindowOfHasFiniteWindow

/-- Finite-window certificate for a negation. -/
def finiteWindowNot {σ : Type u} (p : pred σ) (n : Nat) (hp : FiniteWindow p n) :
    FiniteWindow (tlaNot p) n where
  core := IteratedHomPred.mkNot n hp.core
  iff_of_eval := by
    intro e
    simp only [tlaNot]
    rw [hp.iff_of_eval e]
    rw [IteratedHomPred.evalExec_mkNot]

instance hasFiniteWindowNot {σ : Type u} (p : pred σ) (n : Nat) [HasFiniteWindow p n] :
    HasFiniteWindow (tlaNot p) n where
  finite := finiteWindowNot p n finiteWindowOfHasFiniteWindow

/-- Finite-window certificate for an implication. -/
def finiteWindowImplies {σ : Type u} (p q : pred σ) (n m : Nat)
    (hp : FiniteWindow p n) (hq : FiniteWindow q m) :
    FiniteWindow (tlaImplies p q) (max n m) :=
  finiteWindowBinary (fun p q => p → q) p q n m hp hq

instance hasFiniteWindowImplies {σ : Type u} (p q : pred σ) (n m : Nat)
    [HasFiniteWindow p n] [HasFiniteWindow q m] :
    HasFiniteWindow (tlaImplies p q) (max n m) where
  finite := finiteWindowImplies p q n m finiteWindowOfHasFiniteWindow finiteWindowOfHasFiniteWindow

/-- Finite-window certificate for the `◯` modality. -/
def finiteWindowLater {σ : Type u} (p : pred σ) (n : Nat) (hp : FiniteWindow p n) :
    FiniteWindow (later p) (n + 1) where
  core := fun _ => hp.core
  iff_of_eval := by
    intro e
    simpa [later, IteratedHomPred.evalExec] using hp.iff_of_eval (e.drop 1)

instance hasFiniteWindowLater {σ : Type u} (p : pred σ) (n : Nat) [HasFiniteWindow p n] :
    HasFiniteWindow (later p) (n + 1) where
  finite := finiteWindowLater p n finiteWindowOfHasFiniteWindow

/- Quantifiers need a uniform finite window for every quantified value. These
are kept as certificate constructors rather than typeclass instances, since
inferring such a uniform window is a separate problem. -/

/-- Finite-window certificate for a quantifier binder. -/
def finiteWindowBinder {σ : Type u} {α : Sort v} (op : (α → Prop) → Prop)
    (op_congr : ∀ {p q : α → Prop}, (∀ x, p x ↔ q x) → (op p ↔ op q))
    (p : α → pred σ) (n : Nat) (hp : ∀ x, FiniteWindow (p x) n) :
    FiniteWindow (fun e => op (fun x => p x e)) n where
  core := IteratedHomPred.mkBinder op n (fun x => (hp x).core)
  iff_of_eval := by
    intro e
    rw [IteratedHomPred.evalExec_mkBinder]
    exact op_congr fun x => (hp x).iff_of_eval e

/-- Finite-window certificate for a universal quantifier. -/
def finiteWindowForall {σ : Type u} {α : Sort v} (p : α → pred σ) (n : Nat)
    (hp : ∀ x, FiniteWindow (p x) n) :
    FiniteWindow (tlaForall p) n :=
  finiteWindowBinder (fun r => ∀ x, r x) forall_congr' p n hp

/-- Finite-window certificate for an existential quantifier. -/
def finiteWindowExists {σ : Type u} {α : Sort v} (p : α → pred σ) (n : Nat)
    (hp : ∀ x, FiniteWindow (p x) n) :
    FiniteWindow (tlaExists p) n :=
  finiteWindowBinder (fun r => ∃ x, r x) exists_congr p n hp

instance hasFiniteWindowForall {σ : Type u} {α : Sort v} (p : α → pred σ) (n : Nat)
    [hp : ∀ x, HasFiniteWindow (p x) n] :
    HasFiniteWindow (tlaForall p) n where
  finite := finiteWindowForall p n fun _ => finiteWindowOfHasFiniteWindow

instance hasFiniteWindowExists {σ : Type u} {α : Sort v} (p : α → pred σ) (n : Nat)
    [hp : ∀ x, HasFiniteWindow (p x) n] :
    HasFiniteWindow (tlaExists p) n where
  finite := finiteWindowExists p n fun _ => finiteWindowOfHasFiniteWindow

attribute [tla_finite_window_def]
  Nat.max_def Nat.reduceAdd Nat.reduceLeDiff
  IteratedForall
  HasFiniteWindow.finite
  finiteWindowOfHasFiniteWindow
  hasFiniteWindowPure hasFiniteWindowTrue hasFiniteWindowFalse
  hasFiniteWindowState hasFiniteWindowAction hasFiniteWindowEnabled
  hasFiniteWindowAnd hasFiniteWindowOr hasFiniteWindowNot
  hasFiniteWindowImplies hasFiniteWindowLater
  hasFiniteWindowForall hasFiniteWindowExists
  finiteWindowPure finiteWindowTrue finiteWindowFalse
  finiteWindowState finiteWindowAction finiteWindowEnabled
  finiteWindowBinary finiteWindowAnd finiteWindowOr finiteWindowNot
  finiteWindowImplies finiteWindowLater
  finiteWindowBinder finiteWindowForall finiteWindowExists
  IteratedHomPred.weaken IteratedHomPred.mkAnd
  IteratedHomPred.mkOr IteratedHomPred.mkNot
  IteratedHomPred.mkImplies IteratedHomPred.mkBinary
  IteratedHomPred.mkForall IteratedHomPred.mkExists
  IteratedHomPred.mkBinder

attribute [tla_finite_window_def ↓] dreduceIte reduceIte

open Elab Tactic Meta

private def finiteWindowOf (p : Expr) : MetaM (Expr × Nat) := do
  let win ← mkFreshExprMVar (some (mkConst ``Nat))
  let instTy ← mkAppM ``HasFiniteWindow #[p, win]
  let inst ←
    try synthInstance instTy
    catch _ => throwError "tlaFiniteWindow: failed to synthesize a finite-window instance for {p}"
  let win ← instantiateMVars win
  let win ← withTransparency .all <| whnf win
  let some n ← (Lean.Meta.evalNat win).run
    | throwError "tlaFiniteWindow: synthesized finite window did not reduce to a numeral: {win}"
  return (inst, n)

private def introFiniteStates (n : Nat) : TacticM Unit := do
  for idx in 0...n do
    discard <| introFresh (stateName idx)
where
  /-- Introduce one fresh state variable for each argument of the finite core. -/
  introFresh (namePrefix : Name) : TacticM FVarId := do
    let name ← mkFreshUserName namePrefix
    liftMetaTacticAux fun g => do
      let (fvar, g') ← g.intro name
      return (fvar, [g'])
  stateName (idx : Nat) : Name :=
    Name.mkSimple <| "s" ++ String.ofList (List.replicate idx '\'')

/--
`tlaFiniteWindow` reduces a finite-window TLA sequent to an ordinary Lean
goal over finitely many states.

The tactic uses `HasFiniteWindow` instances for every predicate in the sequent.
It supports local formulas built from state predicates, action predicates, pure
predicates, Boolean connectives, implication, negation, and `◯`. It deliberately
does not peel genuinely temporal structure such as `□`; use sequent/modal rules
first to expose a finite local obligation.
-/
elab "tlaFiniteWindow" : tactic => withMainContext do
  -- Work only with validity goals. Sequents are definitional aliases for
  -- validity of temporal implication.
  changePredImpliesToValid
  -- Instance search computes the canonical window size. The certificate itself
  -- will be used by `HasFiniteWindow.valid_of_forall` below.
  let (inst, n) ← withMainContext do
    let target ← getMainTarget
    let target := target.headBeta.cleanupAnnotations
    match_expr target with
    | TLA.valid _ p => finiteWindowOf p
    | _ => throwError "tlaFiniteWindow: goal is not a TLA validity goal, but {target}"
  -- Replace the temporal goal by the finite core obligation, then expose the
  -- core as ordinary state variables.
  -- Apply at the meta level to avoid synthesizing instance twice
  let thm ← mkAppOptM ``HasFiniteWindow.valid_of_forall #[none, none, none, some inst]
  let g ← getMainGoal
  let gs ← g.apply thm
  let [g] := gs | throwError "tlaFiniteWindow: unexpected number of goals after applying finite-window validity theorem (got {gs.length}, expected 1)"
  replaceMainGoal [g]
  introFiniteStates n
  -- The core still contains the instance constructors and computed `max` widths;
  -- reducing them produces the expected first-order state predicate goal.
  withMainContext do evalTactic <| ← `(tactic| dsimp only [$(mkIdent `tla_finite_window_def):ident])

end TLA
