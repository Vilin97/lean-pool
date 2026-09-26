/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.LLexpr
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.Linarith
public import Mathlib.Util.Qq


/-!
# The `llarith` tactic

`llarith` proves lattice-linear identities and non-strict inequalities in vector
lattices by reducing them to the corresponding statement over `ℝ`. It quotes the
goal as an `LLexpr`, proves the real identity by expanding lattice operations to
`max` and `min` and splitting cases, and transfers the result back with
`LLexpr.vanishes_of_vanishes_real`.

The supported expression language consists of vector-valued atoms, `0`, addition,
subtraction, negation, real scalar multiplication, `⊔`, `⊓`, positive parts,
negative parts, and absolute values. A goal `a ≤ b` is handled as the equivalent
lattice-linear identity `a ⊔ b = b`. Local hypotheses of the form `0 ≤ x`,
`x ≤ 0`, `0 < x`, and `x < 0` are used when `x` is one of the quoted atoms.
-/

public meta section

namespace LLexpr

open Lean Meta Elab Tactic Qq

namespace Tactic

/-- A quoted lattice-linear expression whose coefficients are elaborated Lean expressions.

Unsupported vector-valued subterms are represented by `var`; they are treated as
atomic variables in the real identity check. -/
inductive Quoted where
  /-- The constant zero expression. -/
  | zero
  /-- A vector-valued atom, represented by its index in the collected atom list. -/
  | var (idx : Nat)
  /-- Addition of quoted expressions. -/
  | add (lhs rhs : Quoted)
  /-- Real scalar multiplication of a quoted expression. -/
  | smul (coeff : Expr) (arg : Quoted)
  /-- Supremum of quoted expressions. -/
  | sup (lhs rhs : Quoted)
  /-- Infimum of quoted expressions. -/
  | inf (lhs rhs : Quoted)
  deriving BEq

/-- The sign information about a quoted atom that `llarith` can use. -/
inductive AtomSign where
  /-- No usable sign information was found. -/
  | unknown
  /-- The atom is known to be non-negative. -/
  | nonneg
  /-- The atom is known to be non-positive. -/
  | nonpos
  deriving BEq, Inhabited

/-- Sign information for an atom, together with a proof of the corresponding weak inequality. -/
structure AtomSignInfo where
  /-- Whether the atom is known to be non-negative or non-positive. -/
  sign : AtomSign
  /-- A proof of `0 ≤ x` in the non-negative case, or `x ≤ 0` in the non-positive case. -/
  proof : Expr

/-- State threaded through quotation: the distinct vector-valued atoms already found. -/
structure QuoteState where
  /-- The vector-valued atoms, in the order used for the generated `Fin n → X` tuple. -/
  atoms : Array Expr := #[]

/-- The monad used while quoting a goal into an `LLexpr`. -/
abbrev QuoteM := StateT QuoteState TacticM

/-- Report that the current target is outside the goal shapes supported by `llarith`. -/
def throwUnsupportedTarget : TacticM α :=
  throwError "llarith only supports equality and non-strict inequality goals"

/-- Syntactic comparison of vector-valued atoms, ignoring metadata. -/
def sameAtom (x y : Expr) : Bool :=
  x.consumeMData == y.consumeMData

/-- Return the index of an atom, adding it to the quotation state if it is new. -/
def registerAtom (e : Expr) : QuoteM Nat := do
  let e := e.consumeMData
  let atoms := (← get).atoms
  for h : i in [:atoms.size] do
    if sameAtom e atoms[i] then
      return i
  modify fun s => { s with atoms := s.atoms.push e }
  return atoms.size

/-- Return the index of an already collected atom, if any. -/
def findAtom (atoms : Array Expr) (e : Expr) : Option Nat :=
  Id.run do
    let e := e.consumeMData
    for h : i in [:atoms.size] do
      if sameAtom e atoms[i] then
        return some i
    return none

/-- Test whether an expression is definitionally the zero element of the given type. -/
def isZeroOfType (type e : Expr) : TacticM Bool := do
  let z ← mkAppOptM ``OfNat.ofNat #[some type, some (mkNatLit 0), none]
  withReducible <| isDefEq e z

/-- Test whether an elaborated type expression is definitionally `ℝ`. -/
def isRealType (type : Expr) : TacticM Bool := do
  withReducible <| isDefEq type q(ℝ)

/-- Quote a vector-valued expression as a lattice-linear expression.

Recognized syntax is translated to the corresponding `Quoted` constructor. Any
other vector-valued subterm is registered as an atomic variable. -/
def quoteExprWithFuel : Nat → (type : Expr) → (e : Expr) → QuoteM Quoted
  | 0, _, _ => throwError "llarith expression traversal exhausted its structural bound"
  | fuel + 1, type, e => do
      if ← liftM <| isZeroOfType type e then
        return .zero
      let e := e.consumeMData
      let args := e.getAppArgs
      let some declName := e.getAppFn.constName?
        | return .var (← registerAtom e)
      match declName with
      | ``HAdd.hAdd =>
          if h : args.size = 6 then
            return .add (← quoteExprWithFuel fuel type args[4])
              (← quoteExprWithFuel fuel type args[5])
          else
            return .var (← registerAtom e)
      | ``HSub.hSub =>
          if h : args.size = 6 then
            return .add (← quoteExprWithFuel fuel type args[4])
              (.smul q((-1 : ℝ)) (← quoteExprWithFuel fuel type args[5]))
          else
            return .var (← registerAtom e)
      | ``Neg.neg =>
          if h : args.size = 3 then
            return .smul q((-1 : ℝ)) (← quoteExprWithFuel fuel type args[2])
          else
            return .var (← registerAtom e)
      | ``HSMul.hSMul =>
          if h : args.size = 6 then
            if ← liftM <| isRealType args[0] then
              return .smul args[4] (← quoteExprWithFuel fuel type args[5])
            else
              return .var (← registerAtom e)
          else
            return .var (← registerAtom e)
      | ``Max.max =>
          if h : args.size = 4 then
            return .sup (← quoteExprWithFuel fuel type args[2])
              (← quoteExprWithFuel fuel type args[3])
          else
            return .var (← registerAtom e)
      | ``Min.min =>
          if h : args.size = 4 then
            return .inf (← quoteExprWithFuel fuel type args[2])
              (← quoteExprWithFuel fuel type args[3])
          else
            return .var (← registerAtom e)
      | ``PosPart.posPart =>
          if h : args.size = 3 then
            return .sup (← quoteExprWithFuel fuel type args[2]) .zero
          else
            return .var (← registerAtom e)
      | ``NegPart.negPart =>
          if h : args.size = 3 then
            return .sup (.smul q((-1 : ℝ)) (← quoteExprWithFuel fuel type args[2])) .zero
          else
            return .var (← registerAtom e)
      | ``abs =>
          if h : args.size = 4 then
            let arg ← quoteExprWithFuel fuel type args[3]
            return .sup arg (.smul q((-1 : ℝ)) arg)
          else
            return .var (← registerAtom e)
      | _ =>
          return .var (← registerAtom e)

/-- The expression size bounds the number of recursive quotation steps along any branch. -/
def quoteExpr (type e : Expr) : QuoteM Quoted :=
  quoteExprWithFuel (e.sizeWithoutSharing + 1) type e

/-- Replace atoms with sign-parametrized expressions when a sign hypothesis is available.

For a non-negative atom `x`, the real side uses `x⁺`; for a non-positive atom,
it uses `-(-x)⁺`. After transfer, the original sign hypothesis rewrites these
expressions back to `x`. -/
def Quoted.applySigns (signs : Array AtomSign) : Quoted → Quoted
  | .zero => .zero
  | .var idx =>
      match signs[idx]? with
      | some .nonneg => .sup (.var idx) .zero
      | some .nonpos => .smul q((-1 : ℝ)) (.sup (.smul q((-1 : ℝ)) (.var idx)) .zero)
      | _ => .var idx
  | .add lhs rhs => .add (lhs.applySigns signs) (rhs.applySigns signs)
  | .smul coeff arg => .smul coeff (arg.applySigns signs)
  | .sup lhs rhs => .sup (lhs.applySigns signs) (rhs.applySigns signs)
  | .inf lhs rhs => .inf (lhs.applySigns signs) (rhs.applySigns signs)

/-- Test whether an elaborated scalar coefficient is definitionally `-1`. -/
def isNegOneCoeff (coeff : Expr) : TacticM Bool := do
  withReducible <| isDefEq coeff q((-1 : ℝ))

/-- Remove simple redundancies introduced while quoting and applying signs. -/
def Quoted.simplify : Quoted → TacticM Quoted
  | .zero => return .zero
  | .var idx => return .var idx
  | .add lhs rhs => do
      let lhs ← lhs.simplify
      let rhs ← rhs.simplify
      match lhs, rhs with
      | .zero, rhs => return rhs
      | lhs, .zero => return lhs
      | _, _ => return .add lhs rhs
  | .smul coeff arg => do
      let arg ← arg.simplify
      match arg with
      | .zero => return .zero
      | .smul coeff' arg' =>
          if (← isNegOneCoeff coeff) && (← isNegOneCoeff coeff') then
            return arg'
          else
            return .smul coeff arg
      | _ => return .smul coeff arg
  | .sup lhs rhs => do
      let lhs ← lhs.simplify
      let rhs ← rhs.simplify
      if lhs == rhs then
        return lhs
      else
        match lhs, rhs with
        | .sup a b, rhs =>
            if a == rhs || b == rhs then return lhs else return .sup lhs rhs
        | lhs, .sup a b =>
            if a == lhs || b == lhs then return rhs else return .sup lhs rhs
        | _, _ => return .sup lhs rhs
  | .inf lhs rhs => do
      let lhs ← lhs.simplify
      let rhs ← rhs.simplify
      if lhs == rhs then
        return lhs
      else
        match lhs, rhs with
        | .inf a b, rhs =>
            if a == rhs || b == rhs then return lhs else return .inf lhs rhs
        | lhs, .inf a b =>
            if a == lhs || b == lhs then return rhs else return .inf lhs rhs
        | _, _ => return .inf lhs rhs

/-- Convert an array of optional sign information to the sign array used by quotation. -/
def AtomSignInfo.toSigns (infos : Array (Option AtomSignInfo)) : Array AtomSign :=
  infos.map fun info => info.map (·.sign) |>.getD .unknown

/-- If a proposition gives sign information about a collected atom, return that information. -/
def signFromHyp (type : Expr) (atoms : Array Expr) (proof prop : Expr) :
    TacticM (Option (Nat × AtomSignInfo)) := do
  let prop ← instantiateMVars prop
  let propWhnf ← whnf prop
  let parseRel (strict : Bool) (relType lhs rhs : Expr) :
      TacticM (Option (Nat × AtomSignInfo)) := do
      unless ← withReducible (isDefEq relType type) do
        return none
      let weakProof ← if strict then mkAppM ``le_of_lt #[proof] else pure proof
      if ← isZeroOfType type lhs then
        return (findAtom atoms rhs).map fun idx =>
          (idx, { sign := .nonneg, proof := weakProof })
      else if ← isZeroOfType type rhs then
        return (findAtom atoms lhs).map fun idx =>
          (idx, { sign := .nonpos, proof := weakProof })
      else
        return none
  match propWhnf.le? <|> prop.le? with
  | some (relType, lhs, rhs) => parseRel false relType lhs rhs
  | none =>
      match propWhnf.lt? <|> prop.lt? with
      | some (relType, lhs, rhs) => parseRel true relType lhs rhs
      | none => return none

/-- Collect atom-level sign information from the local context. -/
def collectAtomSigns (type : Expr) (atoms : Array Expr) :
    TacticM (Array (Option AtomSignInfo)) := do
  let mut signs : Array (Option AtomSignInfo) := Array.replicate atoms.size none
  for localDecl in ← getLCtx do
    unless localDecl.isImplementationDetail do
      let hyp := mkFVar localDecl.fvarId
      if let some (idx, info) ← signFromHyp type atoms hyp localDecl.type then
        if (signs[idx]?).join.isNone then
          signs := signs.set! idx (some info)
  return signs

/-- Add the weak inequalities extracted from sign hypotheses to the local context. -/
def assertAtomSignFacts (infos : Array (Option AtomSignInfo)) : TacticM Unit := do
  for h : i in [:infos.size] do
    if let some info := infos[i] then
      let proof ← instantiateMVars info.proof
      let proofType ← inferType proof
      let signName := (`llarith_sign).appendIndexAfter i
      let (_, goal) ← (← (← getMainGoal).assert signName proofType proof).intro1P
      setGoals [goal]

/-- Build a closed expression for the `idx`th element of `Fin arity`. -/
def mkFinExpr (idx arity : Nat) : Expr :=
  have idxExpr : Q(ℕ) := mkNatLitQ idx
  have arityExpr : Q(ℕ) := mkNatLitQ arity
  have hdec : decide ($idxExpr < $arityExpr) =Q true := ⟨⟩
  (q(⟨$idxExpr, of_decide_eq_true $hdec⟩) : Q(Fin $arityExpr))

/-- Convert quoted syntax into the corresponding formal `LLexpr`. -/
def Quoted.toLLexpr (arity : Nat) : Quoted → TacticM Expr
  | .zero =>
      mkAppOptM ``LLexpr.zero #[some (mkNatLit arity)]
  | .var idx =>
      if idx < arity then
        mkAppM ``LLexpr.var #[mkFinExpr idx arity]
      else
        throwError "llarith internal error: variable index out of bounds"
  | .add lhs rhs => do
      mkAppM ``LLexpr.add #[← lhs.toLLexpr arity, ← rhs.toLLexpr arity]
  | .smul coeff arg => do
      mkAppM ``LLexpr.smul #[coeff, ← arg.toLLexpr arity]
  | .sup lhs rhs => do
      mkAppM ``LLexpr.sup #[← lhs.toLLexpr arity, ← rhs.toLLexpr arity]
  | .inf lhs rhs => do
      mkAppM ``LLexpr.inf #[← lhs.toLLexpr arity, ← rhs.toLLexpr arity]

/-- Build the finite tuple of vector-valued atoms used to evaluate the quoted `LLexpr`s.

The tuple is emitted as a `PiFin` literal so that the final simplification step
can unfold each variable lookup. -/
def mkFinFun (type : Expr) (atoms : Array Expr) : MetaM Expr := do
  let .sort u ← whnf (← inferType type)
    | throwError "llarith internal error: expected a type{indentExpr type}"
  let some v := u.dec
    | throwError "llarith only supports targets in Type"
  have α : Q(Type v) := type
  let atoms : Array Q($α) := atoms.map fun atom => atom
  if h : atoms.isEmpty then
    return q(Fin.elim0 : Fin 0 → $α)
  else
    return PiFin.mkLiteralQ (α := α) (n := atoms.size) fun i => atoms[i]

/-- Prove the generated real vanishing statement.

After introducing the real variables, this unfolds `LLexpr.eval` and first tries
`grind` on the real lattice expression. If that does not close the goal, it
falls back to expanding `max` and `min`, splitting cases, and closing the
resulting arithmetic goals with `linarith` or `nlinarith`. -/
def proveRealVanishes (hreal : MVarId) : TacticM Unit := do
  let savedGoals ← getGoals
  setGoals [hreal]
  try
    evalTactic (← `(tactic|
      intro r;
      simp only [LLexpr.eval_zero, LLexpr.eval_var, LLexpr.eval_add, LLexpr.eval_smul,
        LLexpr.eval_sup, LLexpr.eval_inf, smul_eq_mul];
      first
        | grind
        | (simp only [sup_eq_maxDefault, inf_eq_minDefault, max_def, min_def];
           (repeat' split_ifs);
           all_goals first
             | linarith
             | nlinarith)))
  catch ex =>
    setGoals savedGoals
    throwError "llarith failed to prove the associated real identity\n{ex.toMessageData}"
  let remaining ← getGoals
  unless remaining.isEmpty do
    setGoals savedGoals
    throwError "llarith failed to close the associated real identity"
  setGoals savedGoals

/-- Transfer a quoted real identity back to the original vector-lattice goal.

If `asLe` is true, the quoted equality has the form `lhs ⊔ rhs = rhs` and is
post-processed as a proof of `lhs ≤ rhs`. -/
def closeByTransfer (type : Expr) (lhsQ rhsQ : Quoted) (atoms : Array Expr) (asLe hasSigns : Bool) :
    TacticM Unit := do
  let arity := atoms.size
  let lhsE ← instantiateMVars (← lhsQ.toLLexpr arity)
  let rhsE ← instantiateMVars (← rhsQ.toLLexpr arity)
  let diffE ←
    instantiateMVars (← mkAppM ``LLexpr.add #[lhsE, ← mkAppM ``LLexpr.smul #[q((-1 : ℝ)), rhsE]])
  let hrealType ← mkAppM ``LLexpr.Vanishes #[q(ℝ), diffE]
  let hreal ← mkFreshExprMVar hrealType .syntheticOpaque `llarith_real
  proveRealVanishes hreal.mvarId!
  let hreal ← instantiateMVars hreal
  let tuple ← mkFinFun type atoms
  let proof ← mkAppM ``LLexpr.eval_eq_of_vanishes_real #[tuple, lhsE, rhsE, hreal]
  let proofType ← inferType proof
  let transferName := `llarith_transfer
  let (_, goal) ← (← (← getMainGoal).assert transferName proofType proof).intro1P
  setGoals [goal]
  let hIdent := mkIdent transferName
  if hasSigns then
    let savedState ← saveState
    try
      evalTactic (← `(tactic|
        simpa [*, LLexpr.eval_zero, LLexpr.eval_var, LLexpr.eval_add, LLexpr.eval_smul,
          LLexpr.eval_sup, LLexpr.eval_inf, posPart_def, negPart_def, abs, sub_eq_add_neg,
          neg_one_smul, add_assoc, add_comm, add_left_comm] using $hIdent:ident))
      return
    catch _ => savedState.restore
  if !hasSigns then
    if asLe then
      evalTactic (← `(tactic|
        first
          | simpa [LLexpr.eval_zero, LLexpr.eval_var, LLexpr.eval_add, LLexpr.eval_smul,
              LLexpr.eval_sup, LLexpr.eval_inf, posPart_def, negPart_def, abs, sub_eq_add_neg,
              neg_one_smul, add_assoc, add_comm, add_left_comm] using $hIdent:ident
          | (simp at $hIdent:ident ⊢;
             simp_all [LLexpr.eval_zero, LLexpr.eval_var, LLexpr.eval_add, LLexpr.eval_smul,
               LLexpr.eval_sup, LLexpr.eval_inf, posPart_def, negPart_def, abs, sub_eq_add_neg,
               neg_one_smul, add_assoc, add_comm, add_left_comm];
             all_goals first
               | exact $hIdent:ident
               | simpa [add_assoc, add_comm, add_left_comm] using $hIdent:ident)))
    else
      evalTactic (← `(tactic|
        first
          | simpa [LLexpr.eval_zero, LLexpr.eval_var, LLexpr.eval_add, LLexpr.eval_smul,
              LLexpr.eval_sup, LLexpr.eval_inf, posPart_def, negPart_def, abs, sub_eq_add_neg,
              neg_one_smul, add_assoc, add_comm, add_left_comm] using $hIdent:ident
          | (simp at $hIdent:ident ⊢;
             simp_all [LLexpr.eval_zero, LLexpr.eval_var, LLexpr.eval_add, LLexpr.eval_smul,
               LLexpr.eval_sup, LLexpr.eval_inf, posPart_def, negPart_def, abs, sub_eq_add_neg,
               neg_one_smul, add_assoc, add_comm, add_left_comm];
             all_goals first
               | exact $hIdent:ident
               | convert $hIdent:ident using 1 <;> abel_nf)))
  else if asLe then
    evalTactic (← `(tactic|
      simp at $hIdent:ident ⊢;
      simp_all [LLexpr.eval_zero, LLexpr.eval_var, LLexpr.eval_add, LLexpr.eval_smul,
        LLexpr.eval_sup, LLexpr.eval_inf, posPart_def, negPart_def, abs, sub_eq_add_neg,
        neg_one_smul, add_assoc, add_comm, add_left_comm];
      all_goals first
        | exact $hIdent:ident
        | simpa [add_assoc, add_comm, add_left_comm] using $hIdent:ident))
  else
    evalTactic (← `(tactic|
      simp at $hIdent:ident ⊢;
      simp_all [LLexpr.eval_zero, LLexpr.eval_var, LLexpr.eval_add, LLexpr.eval_smul,
        LLexpr.eval_sup, LLexpr.eval_inf, posPart_def, negPart_def, abs, sub_eq_add_neg,
        neg_one_smul, add_assoc, add_comm, add_left_comm];
      all_goals first
        | exact $hIdent:ident
        | convert $hIdent:ident using 1 <;> abel_nf))

/-- Implementation of the user-facing `llarith` tactic. -/
def evalLlarith : TacticM Unit := focus <| withMainContext do
  let goal ← getMainGoal
  evalTactic (← `(tactic| try rfl))
  if ← goal.isAssigned then return
  let target ← instantiateMVars (← getMainTarget)
  let targetWhnf ← whnf target
  if let some (_, lhs, rhs) := targetWhnf.eq? <|> target.eq? then
    let type ← inferType lhs
    unless ← withReducible (isDefEq type (← inferType rhs)) do
      throwError "llarith only supports homogeneous equality goals"
    let ((lhsQ, rhsQ), state) ←
      (do
      let lhsQ ← quoteExpr type lhs
      let rhsQ ← quoteExpr type rhs
      return (lhsQ, rhsQ)).run {}
    let signInfos ← collectAtomSigns type state.atoms
    assertAtomSignFacts signInfos
    let signs := AtomSignInfo.toSigns signInfos
    let hasSigns := signInfos.any Option.isSome
    closeByTransfer type (← (lhsQ.applySigns signs).simplify)
      (← (rhsQ.applySigns signs).simplify) state.atoms false hasSigns
  else if let some (type, lhs, rhs) := targetWhnf.le? <|> target.le? then
    unless ← withReducible (isDefEq type (← inferType lhs)) do
      throwError "llarith internal error: malformed inequality goal"
    unless ← withReducible (isDefEq type (← inferType rhs)) do
      throwError "llarith only supports homogeneous inequality goals"
    let ((lhsQ, rhsQ), state) ←
      (do
      let lhsQ ← quoteExpr type lhs
      let rhsQ ← quoteExpr type rhs
      return (lhsQ, rhsQ)).run {}
    let signInfos ← collectAtomSigns type state.atoms
    assertAtomSignFacts signInfos
    let signs := AtomSignInfo.toSigns signInfos
    let hasSigns := signInfos.any Option.isSome
    closeByTransfer type (← ((Quoted.sup lhsQ rhsQ).applySigns signs).simplify)
      (← (rhsQ.applySigns signs).simplify) state.atoms true hasSigns
  else
    throwUnsupportedTarget

/-- Prove lattice-linear identities by checking the corresponding identity over `ℝ`.

The tactic supports equality and non-strict inequality goals built from vector-valued atoms,
`0`, `+`, `-`, unary negation, real scalar multiplication, `⊔`, `⊓`, positive and negative
parts, and absolute values. It also uses atom-level sign hypotheses of the form `0 ≤ x`,
`x ≤ 0`, `0 < x`, or `x < 0`.
-/
elab "llarith" : tactic => evalLlarith

end Tactic

end LLexpr

end

section Tests

variable {E : Type*} [AddCommGroup E] [Lattice E] [IsOrderedAddMonoid E]
  [VectorLattice E]

example (x y : E) : (x ⊔ y) + (x ⊓ y) = x + y := by llarith

example (x y : E) : |x + y| ≤ |x| + |y| := by llarith

example (x y : E) : (2 : ℝ) • (x ⊔ y) = (2 : ℝ) • x ⊔ (2 : ℝ) • y := by llarith

example (x : E) (hx : 0 ≤ x) : |x| = x := by llarith

example (x : E) (hx : x ≤ 0) : |x| = -x := by llarith

example (x : E) (hx : 0 < x) : |x| = x := by llarith

example (x : E) (hx : x < 0) : |x| = -x := by llarith

example (x y : E) (hx : 0 ≤ x) (hy : y ≤ 0) : |x - y| = x - y := by llarith

example (x y : E) (hx : 0 ≤ x) (hy : y ≤ 0) : y ≤ x := by llarith

example (x : E) : x⁺ - x⁻ = x := by llarith

example : (0 : E) = 0 := by llarith

-- The evaluator sees all three goals and must return precisely the original two siblings.
example (x y : E) (P Q : Prop) (hP : P) (hQ : Q) :
    (x ⊔ y) + (x ⊓ y) = x + y ∧ P ∧ Q := by
  run_tac
    let [mainGoal, rest] ← (← Lean.Elab.Tactic.getMainGoal).applyConst ``And.intro
      | Lean.throwError "expected the main goal and sibling conjunction"
    let [pGoal, qGoal] ← rest.applyConst ``And.intro
      | Lean.throwError "expected two sibling goals"
    Lean.Elab.Tactic.setGoals [mainGoal, pGoal, qGoal]
    LLexpr.Tactic.evalLlarith
    unless ← mainGoal.isAssigned do
      Lean.throwError "llarith did not close its main goal"
    unless (← Lean.Elab.Tactic.getGoals) == [pGoal, qGoal] do
      Lean.throwError "llarith changed or reordered its sibling goals"
    pGoal.withContext do
      pGoal.assign (← Lean.Meta.getFVarFromUserName `hP)
    qGoal.withContext do
      qGoal.assign (← Lean.Meta.getFVarFromUserName `hQ)
    Lean.Elab.Tactic.setGoals []

example (x y : E) (hx : 0 ≤ x) (hy : y ≤ 0) (P Q : Prop) (hP : P) (hQ : Q) :
    y ≤ x ∧ P ∧ Q := by
  run_tac
    let [mainGoal, rest] ← (← Lean.Elab.Tactic.getMainGoal).applyConst ``And.intro
      | Lean.throwError "expected the main goal and sibling conjunction"
    let [pGoal, qGoal] ← rest.applyConst ``And.intro
      | Lean.throwError "expected two sibling goals"
    Lean.Elab.Tactic.setGoals [mainGoal, pGoal, qGoal]
    LLexpr.Tactic.evalLlarith
    unless ← mainGoal.isAssigned do
      Lean.throwError "llarith did not close its main goal"
    unless (← Lean.Elab.Tactic.getGoals) == [pGoal, qGoal] do
      Lean.throwError "llarith changed or reordered its sibling goals"
    pGoal.withContext do
      pGoal.assign (← Lean.Meta.getFVarFromUserName `hP)
    qGoal.withContext do
      qGoal.assign (← Lean.Meta.getFVarFromUserName `hQ)
    Lean.Elab.Tactic.setGoals []

end Tests
