/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.Tactic.RingModChar

open Lean Mathlib Meta Qq Tactic

namespace Mathlib.Tactic.RingModChar

open AtomM
open Ring

variable [Ring R]

theorem intCast_nat (n) : ((Nat.rawCast n : ℤ) : R) = Nat.rawCast n := by simp
theorem intCast_int (n) : ((Int.rawCast n : ℤ) : R) = Int.rawCast n := by simp

theorem intCast_mul (a₂) (_ : ((a₁ : ℤ) : R) = b₁) (_ : ((a₃ : ℤ) : R) = b₃) :
    ((a₁ ^ a₂ * a₃ : ℤ) : R) = b₁ ^ a₂ * b₃ := by subst_vars; simp

theorem intCast_zero : ((0 : ℤ) : R) = 0 := Int.cast_zero

theorem intCast_add (_ : ((a₁ : ℤ) : R) = b₁) (_ : ((a₂ : ℤ) : R) = b₂) :
    ((a₁ + a₂ : ℤ) : R) = b₁ + b₂ := by subst_vars; simp

/--
A typed expression of type `CommSemiring ℤ` used when we are working on
ring subexpressions of type `ℤ`.
-/
def sℤ : Q(CommSemiring ℤ) := q(Int.instCommRing.toCommSemiring)

variable {u : Level} {R : Q(Type u)} (sα : Q(CommSemiring $R)) (rR : Q(Ring $R))
variable {h : ($rR).toSemiring =Q ($sα).toSemiring}
variable (char : ℕ) (cpR : Option (Q(CharP $R $char)))

mutual

/-- Applies `Int.cast` to a int polynomial to produce a polynomial in `α`.

* An atom `e` causes `↑e` to be allocated as a new atom.
* A sum delegates to `ExSum.evalIntCast`.
-/
partial def ExBase.evalIntCast (va : ExBase sℤ a) : AtomM (Result (ExBase sα) q($a)) :=
  match va with
  | .atom _ => do
    let a' : Q($R) := q($a)
    let (i, a') ← addAtom a'
    pure ⟨a', ExBase.atom i, (q(Eq.refl $a') : Expr)⟩
  | .sum va => do
    let ⟨_, vc, p⟩ ← va.evalIntCast
    pure ⟨_, .sum vc, p⟩

/-- Applies `Int.cast` to a int monomial to produce a monomial in `α`.

* `↑c = c` if `c` is a numeric literal
* `↑(a ^ n * b) = ↑a ^ n * ↑b`
-/
partial def ExProd.evalIntCast (va : RingModChar.ExProd sℤ a) :
    AtomM (RingModChar.Result (RingModChar.ExProd sα) q($a)) :=
  match va with
  | .const c hc => do
    -- TODO: reduce modulo the characteristic
    match a with
    | ~q(Nat.rawCast $n) =>
      pure ⟨q(Nat.rawCast $n), .const c hc, q(intCast_nat (R := $R) $n)⟩
    | ~q(Int.rawCast $n) =>
      pure ⟨q(Int.rawCast $n), .const c hc, q(intCast_int (R := $R) $n)⟩
    | _ =>
      pure ⟨q(Int.rawCast $a), .const c hc, q(intCast_int (R := $R) $a)⟩
  | .mul (x := a₁) (e := a₂) (b := a₃) _ _ _ => do
    let e : Q($R) := q((($a₁ ^ $a₂ * $a₃ : ℤ) : $R))
    let (i, _) ← addAtom e
    let v := (ExBase.atom (sα := sα) i (e := e)).toProd (ExProd.mkNat sℕ 1).2
    pure ⟨_, v, (q(toProd_pf (Eq.refl $e)) : Expr)⟩

/-- Applies `Int.cast` to a int polynomial to produce a polynomial in `α`.

* `↑0 = 0`
* `↑(a + b) = ↑a + ↑b`
-/
partial def ExSum.evalIntCast (va : RingModChar.ExSum sℤ a) :
    AtomM (RingModChar.Result (RingModChar.ExSum sα) q($a)) :=
  match va with
  | .zero => do
    let e : Q($R) := q(((0 : ℤ) : $R))
    let (i, _) ← addAtom e
    let v := (ExBase.atom (sα := sα) i (e := e)).toProd (ExProd.mkNat sℕ 1).2 |>.toSum
    pure ⟨_, v, (q(atom_pf $e) : Expr)⟩
  | .add (a := a₁) (b := a₂) _ _ => do
    let e : Q($R) := q((($a₁ + $a₂ : ℤ) : $R))
    let (i, _) ← addAtom e
    let v := (ExBase.atom (sα := sα) i (e := e)).toProd (ExProd.mkNat sℕ 1).2 |>.toSum
    pure ⟨_, v, (q(atom_pf $e) : Expr)⟩

end

theorem smul_int (_ : (a * b : ℤ) = c) : a • b = c := by subst_vars; simp

theorem int_smul_eq_cast {R : Type*} [Ring R] {a' b c : R}
    (_ : ((a : ℤ) : R) = a') (_ : a' * b = c) : a • b = c := by
  subst_vars
  simp

/-- Constructs the scalar multiplication `n • a`, where both `n : ℤ` and `a : ℤ` are normalized
polynomial expressions.

* `a • b = a * b` if `α = ℤ`
-/
def evalZSMulInt (va : RingModChar.ExSum sℤ a) (vb : RingModChar.ExSum sℤ b) :
    AtomM (RingModChar.Result (RingModChar.ExSum sℤ) q($a • $b)) := do
  let ⟨_, vc, pc⟩ ← evalMul sℤ 0 none none va vb
  pure ⟨_, vc, q(smul_int $pc)⟩

/-- Constructs the scalar multiplication `n • a`, where both `n : ℤ` and `a : α` are normalized
polynomial expressions.

* `a • b = a * b` if `α = ℤ`
* `a • b = ↑a * b` otherwise
-/
def evalZSMul (char : ℕ) (cpR : Option (Q(CharP $R $char)))
    (va : RingModChar.ExSum sℤ a) (vb : RingModChar.ExSum sα b) :
    AtomM (RingModChar.Result (RingModChar.ExSum sα) q($a • $b)) := do
  if ← isDefEq sα sℤ then
    let ⟨_, va'⟩ := va.cast
    have _b : Q(ℤ) := b
    let ⟨(_c : Q(ℤ)), vc, (pc : Q($a * $_b = $_c))⟩ ← evalMul sα char rR cpR va' vb
    pure ⟨_, vc, (q(smul_int $pc) : Expr)⟩
  else do
    let e : Q($R) := q($a • $b)
    evalAtom sα e

end Mathlib.Tactic.RingModChar

/-- If `a = b` and we can evaluate `b`, then we can evaluate `a`. -/
def Mathlib.Meta.NormNum.Result.eq_trans {α : Q(Type u)} {a b : Q($α)} (eq : Q($a = $b)) :
    NormNum.Result b → NormNum.Result a
| .isBool true proof =>
  have a : Q(Prop) := a
  have b : Q(Prop) := b
  have eq : Q($a = $b) := eq
  have proof : Q($b) := proof
  .isTrue (x := a) q($eq ▸ $proof)
| .isBool false proof =>
  have a : Q(Prop) := a
  have b : Q(Prop) := b
  have eq : Q($a = $b) := eq
  have proof : Q(¬ $b) := proof
 .isFalse (x := a) q($eq ▸ $proof)
| .isNat inst lit proof => .isNat inst lit q($eq ▸ $proof)
| .isNegNat inst lit proof => .isNegNat inst lit q($eq ▸ $proof)
| .isNNRat inst q n d proof => .isNNRat inst q n d q($eq ▸ $proof)
| .isNegNNRat inst q n d proof => .isNegNNRat inst q n d q($eq ▸ $proof)

/-- Forget that we're evaluating `a` and instead evaluate `b`. -/
def Mathlib.Meta.NormNum.Result.uncheckedCast {α : Q(Type u)} {a b : Q($α)} :
    NormNum.Result b → NormNum.Result a
| .isBool true proof =>
  have a : Q(Prop) := a
  have b : Q(Prop) := b
  have proof : Q($b) := proof
  .isTrue (x := a) (q($proof) : Expr)
| .isBool false proof =>
  have a : Q(Prop) := a
  have b : Q(Prop) := b
  have proof : Q(¬ $b) := proof
 .isFalse (x := a) (q($proof) : Expr)
| .isNat inst lit proof => .isNat inst lit (q($proof) : Expr)
| .isNegNat inst lit proof => .isNegNat inst lit (q($proof) : Expr)
| .isNNRat inst q n d proof => .isNNRat inst q n d (q($proof) : Expr)
| .isNegNNRat inst q n d proof => .isNegNNRat inst q n d (q($proof) : Expr)

namespace NormTactic

class MResultClass (m : Type → Type) {u : Level} (R : Q(Type u))
    (r : (e : Q($R)) → Type) where
  rflM : {a : Q($R)} → m (r a)
  eqTransM : {a b : Q($R)} → (eq : Q($a = $b)) → r b → m (r a)
  uncheckedCast : {a b : Q($R)} → r b → r a
  out : {a : Q($R)} → r a → (a' : Q($R)) × Q($a = $a')

instance {α : Q(Type u)} : MResultClass MetaM α (fun e => NormNum.Result e) where
  out res := res.toRawEq
  rflM := NormNum.derive _
  eqTransM eq res := pure (res.eq_trans eq)
  uncheckedCast res := res.uncheckedCast

instance {R : Q(Type u)} {r : (e : Q($R)) → Type} [MResultClass m R r] {e : Q($R)} :
    Inhabited (m (r e)) where
  default := MResultClass.rflM

structure Result {α : Q(Type u)} (e : Q($α)) where
  (val : Q($α))
  (pf : Q($e = $val))

instance : ToString (Result e) where
  toString r := toString r.pf

def Result.trans_eq {α : Q(Type u)} {e e' : Q($α)} (h : Q($e = $e')) :
    Result e' → Result e
  | ⟨val, pf⟩ => ⟨val, q(Eq.trans $h $pf)⟩

def Result.uncheckedCast {α : Q(Type u)} {β : Q(Type v)} {e : Q($α)} {e' : Q($β)} :
    Result e → Result e'
  | ⟨val, pf⟩ => ⟨val, pf⟩

def Result.toSimpResult {α : Q(Type u)} {e : Q($α)} (r : Result e) : Simp.Result where
  expr := r.val
  proof? := r.pf

instance {α : Q(Type u)} [Pure m] : MResultClass m α Result where
  out res := ⟨res.val, res.pf⟩
  rflM := pure ⟨_, q(rfl)⟩
  eqTransM eq res := pure (Result.trans_eq eq res)
  uncheckedCast := Result.uncheckedCast

def Result.rfl {α : Q(Type u)} (e : Q($α)) : Result e where
  val := e
  pf := q(rfl)

def RingResult {α : Q(Type u)} (csr : Q(CommSemiring $α)) (e : Q($α)) : Type :=
  RingModChar.Result (RingModChar.ExSum csr) e

def RingResult.toResult {α : Q(Type u)} {csr : Q(CommSemiring $α)} {e : Q($α)}
    (res : RingResult csr e) : Result e where
  val := res.expr -- TODO: simp using the ring_nf set?
  pf := res.proof

def RingResult.uncheckedCast {α : Q(Type u)} {csr : Q(CommSemiring $α)} {e e' : Q($α)}
    (res : RingResult csr e) : RingResult csr e' where
  expr := res.expr
  val := res.val
  proof := res.proof

def RingResult.eqTrans {α : Q(Type u)} {csr : Q(CommSemiring $α)} {e e' : Q($α)}
    (pf : Q($e' = $e))
    (res : RingResult csr e) : MetaM (RingResult csr e') := do
  return ⟨res.expr, res.val, ← (mkEqTrans pf res.proof)⟩

def RingResult.mkRfl {α : Q(Type u)} (csr : Q(CommSemiring $α)) (e : Q($α)) :
    AtomM (RingResult csr e) := do
  let cache ← RingModChar.mkCache _ {}
  RingModChar.eval _ cache e

def _root_.Lean.Meta.Simp.Result.toResult {α : Q(Type u)} {e : Q($α)} (r : Simp.Result) :
    Result e :=
  have e' : Q($α) := r.expr
  match r.proof? with
  | none => Result.uncheckedCast ⟨e', q(rfl)⟩
  | some pf => ⟨r.expr, pf⟩

def _root_.Lean.Meta.Simp.Result.toRingResult {α : Q(Type u)} {csr : Q(CommSemiring $α)}
    {e : Q($α)} (r : Simp.Result) :
    AtomM (RingResult csr e) :=
  match r.proof? with
  | none => do
    return (← RingResult.mkRfl _ r.expr).uncheckedCast
  | some pf => do
    (← RingResult.mkRfl _ r.expr).eqTrans pf

def _root_.NormTactic.Result.toRingResult {α : Q(Type u)} {csr : Q(CommSemiring $α)}
    {e : Q($α)} (r : Result e) : AtomM (RingResult csr e) := do
  (← RingResult.mkRfl _ r.val).eqTrans r.pf

instance {α : Q(Type u)} {crr : Q(CommSemiring $α)} :
    MResultClass AtomM α (RingResult crr) where
  out res := ⟨res.expr, res.proof⟩
  rflM := RingResult.mkRfl crr _
  eqTransM eq res := RingResult.eqTrans eq res
  uncheckedCast := RingResult.uncheckedCast

instance [ToMessageData a] : ToMessageData (Except Exception a) where
  toMessageData e := match e with
  | .error _ => e.emoji
  | .ok a => toMessageData a

instance {R : Q(Type u)} {instCSrR : Q(CommSemiring $R)} (e) :
    ToMessageData (RingResult instCSrR e) where
  toMessageData e := toMessageData e.expr

structure CommSemiringResult (m : Type → Type) (R : Q(Type u))
    (r : (e : Q($R)) → Type) [MResultClass m R r]
    (instCSrR : Q(CommSemiring «$R») := by with_reducible assumption) where
  (char : ℕ) (instCPR : Option Q(CharP $R $char))
  (mkZero : r q((0 : $R))) (mkOne : r q((1 : $R)))
  (mkNSMul : ∀ (n : Q(ℕ)) {b : Q($R)}, r b → m (r q($n • $b)))
  (mkAdd : ∀ {a b : Q($R)}, r a → r b → m (r q($a + $b)))
  (mkMul : ∀ {a b : Q($R)}, r a → r b → m (r q($a * $b)))

variable {R : Q(Type u)} (instCSrR : Q(CommSemiring $R) := by with_reducible assumption)
variable (char : ℕ) (rR : Option (Q(Ring $R))) (cpR : Option (Q(CharP $R $char)))

def CommSemiring.mkZero : RingResult instCSrR q((0 : $R)) :=
  ⟨q(0), .zero, q(RingModChar.cast_zero ⟨by simp⟩)⟩

def CommSemiring.mkOne : RingResult instCSrR q((1 : $R)) :=
  ⟨_, (RingModChar.ExProd.mkNat instCSrR 1).2.toSum, q(RingModChar.cast_pos ⟨by simp⟩)⟩

def CommSemiring.mkNSMul
    (n : Q(ℕ)) {b : Q($R)} (rb : RingResult instCSrR b) :
    AtomM (RingResult instCSrR q($n • $b)) := do
  let n' ← RingResult.mkRfl _ n
  let r : RingResult _ _ ← RingModChar.evalNSMul instCSrR char rR cpR n'.val rb.val
  RingResult.eqTrans q(congr_arg₂ (fun x y => x • y) $n'.proof $rb.proof) r

def CommSemiring.mkAdd
    {a b : Q($R)} (ra : RingResult instCSrR a) (rb : RingResult instCSrR b) :
    AtomM (RingResult instCSrR q($a + $b)) := do
  -- TODO: we can use the characteristic of the ring here
  let r ← RingModChar.evalAdd instCSrR char rR cpR ra.val rb.val
  RingResult.eqTrans q(congr_arg₂ (fun x y => x + y) $ra.proof $rb.proof) r

def CommSemiring.mkMul
    {a b : Q($R)} (ra : RingResult instCSrR a) (rb : RingResult instCSrR b) :
    AtomM (RingResult instCSrR q($a * $b)) := do
  -- TODO: we can use the characteristic of the ring here
  let r ← RingModChar.evalMul instCSrR char rR cpR ra.val rb.val
  RingResult.eqTrans q(congr_arg₂ (fun x y => x * y) $ra.proof $rb.proof) r

def CommSemiringResult.ringResult : CommSemiringResult AtomM R (RingResult instCSrR) where
  char := char
  instCPR := cpR
  mkZero := CommSemiring.mkZero
  mkOne := CommSemiring.mkOne
  mkNSMul := CommSemiring.mkNSMul _ char rR cpR
  mkAdd a b := do CommSemiring.mkAdd _ char rR cpR a b
  mkMul a b := do CommSemiring.mkMul _ char rR cpR a b

structure CommRingResult (m : Type → Type) (R : Q(Type u)) (r : (e : Q($R)) → Type)
    [MResultClass m R r]
    (instCSrR : Q(CommSemiring «$R») := by with_reducible assumption)
    (instCRR : Q(CommRing «$R») := by with_reducible assumption)
    extends CommSemiringResult m R r instCSrR where
  (mkZSMul : ∀ (n : Q(ℤ)) {b : Q($R)}, r b → m (r q($n • $b)))
  (mkNeg : ∀ {b : Q($R)}, r b → m (r q(- $b)))
  (mkSub : ∀ {a b : Q($R)}, r a → r b → m (r q($a - $b)))

def CommRing.mkZSMul
    (instCRR : Q(CommRing $R) := by with_reducible assumption)
     (n : Q(ℤ)) {b : Q($R)} (rb : RingResult instCSrR b) :
    AtomM (RingResult instCSrR q($n • $b)) := do
  let n' ← RingResult.mkRfl _ n
  let r : RingResult _ _ ←
    RingModChar.evalZSMul instCSrR q(($instCRR).toRing) char cpR n'.val rb.val
  let res ← RingResult.eqTrans q(congr_arg₂ (fun x y => x • y) $n'.proof $rb.proof) r
  pure res

def CommRing.mkNeg
    (instCRR : Q(CommRing $R) := by with_reducible assumption)
    {b : Q($R)} (rb : RingResult instCSrR b) :
    AtomM (RingResult instCSrR q(- $b)) := do
  let r : RingResult _ _ ← RingModChar.evalNeg instCSrR char cpR q(($instCRR).toRing) rb.val
  RingResult.eqTrans q(congr_arg (fun x => -x) $rb.proof) r

def CommRing.mkSub
    (instCRR : Q(CommRing $R) := by with_reducible assumption)
    {a b : Q($R)} (ra : RingResult instCSrR a) (rb : RingResult instCSrR b) :
    AtomM (RingResult instCSrR q($a - $b)) := do
  -- TODO: we can use the characteristic of the ring here
  let r : RingResult _ _ ← RingModChar.evalSub instCSrR char cpR q(($instCRR).toRing) ra.val rb.val
  RingResult.eqTrans q(congr_arg₂ (fun x y => x - y) $ra.proof $rb.proof) r

def CommRingResult.ringResult
    (instCRR : Q(CommRing $R) := by with_reducible assumption) :
    CommRingResult AtomM R (RingResult instCSrR) where
  char := char
  instCPR := cpR
  mkZero := CommSemiring.mkZero
  mkOne := CommSemiring.mkOne
  mkNSMul := CommSemiring.mkNSMul _ char (.some q(($instCRR).toRing)) cpR
  mkAdd a b := do CommSemiring.mkAdd _ char (.some q(($instCRR).toRing)) cpR a b
  mkMul a b := do CommSemiring.mkMul _ char (.some q(($instCRR).toRing)) cpR a b
  mkZSMul := CommRing.mkZSMul _ char cpR _
  mkNeg a := do CommRing.mkNeg _ char cpR _ a
  mkSub a b := do CommRing.mkSub _ char cpR _ a b

def CommSemiringResult.toCommRingResult
    (crr : CommSemiringResult (m := AtomM) (R := R) (r := RingResult instCSrR))
    (instCRR : Q(CommRing $R) := by with_reducible assumption) :
    CommRingResult AtomM R (RingResult instCSrR) :=
  { crr with
    mkZSMul := CommRing.mkZSMul _ crr.char crr.instCPR _
    mkNeg := fun a => do CommRing.mkNeg _ crr.char crr.instCPR _ a
    mkSub := fun a b => do CommRing.mkSub _ crr.char crr.instCPR _ a b }

def CommSemiring.Result.mkZero {R : Q(Type u)}
    (_instCRR : Q(CommSemiring $R) := by with_reducible assumption) : Result q((0 : $R)) :=
  ⟨q(0), q(rfl)⟩

def CommSemiring.Result.mkOne {R : Q(Type u)}
    (_instCRR : Q(CommSemiring $R) := by with_reducible assumption) : Result q((1 : $R)) :=
  ⟨q(1), q(rfl)⟩

def CommRing.Result.mkNeg {R : Q(Type u)}
    (_instCRR : Q(CommRing $R) := by with_reducible assumption)
    {a : Q($R)} (ra : Result a) : Result q(-$a) :=
  ⟨q(-$(ra.val)), q($(ra.pf) ▸ rfl)⟩

def CommSemiring.Result.mkAdd {R : Q(Type u)}
    (_instCRR : Q(CommSemiring $R) := by with_reducible assumption)
    {a b : Q($R)} (ra : Result a) (rb : Result b) : (Result q($a + $b)) :=
  ⟨q($(ra.val) + $(rb.val)), q($(ra.pf) ▸ $(rb.pf) ▸ rfl)⟩

def CommRing.Result.mkSub {R : Q(Type u)}
    (_instCRR : Q(CommRing $R) := by with_reducible assumption)
    {a b : Q($R)} (ra : Result a) (rb : Result b) : (Result q($a - $b)) :=
  ⟨q($(ra.val) - $(rb.val)), q($(ra.pf) ▸ $(rb.pf) ▸ rfl)⟩

def CommSemiring.Result.mkMul {R : Q(Type u)}
    (_instCRR : Q(CommSemiring $R) := by with_reducible assumption)
    {a b : Q($R)} (ra : Result a) (rb : Result b) : (Result q($a * $b)) :=
  ⟨q($(ra.val) * $(rb.val)), q($(ra.pf) ▸ $(rb.pf) ▸ rfl)⟩

def CommSemiring.Result.mkNSMul {R : Q(Type u)}
    (_instCRR : Q(CommSemiring $R) := by with_reducible assumption)
    (a : Q(ℕ)) {b : Q($R)} (rb : Result b) : (Result q($a • $b)) :=
  ⟨q($a • $(rb.val)), q($(rb.pf) ▸ rfl)⟩

def CommRing.Result.mkZSMul {R : Q(Type u)}
    (_instCRR : Q(CommRing $R) := by with_reducible assumption)
    (a : Q(ℤ)) {b : Q($R)} (rb : Result b) : (Result q($a • $b)) :=
  ⟨q($a • $(rb.val)), q($(rb.pf) ▸ rfl)⟩

def CommRingResult.default {m : Type → Type} [Pure m]
    (instCRR : Q(CommRing $R) := by with_reducible assumption) :
    CommRingResult m R Result where
  char := char
  instCPR := cpR
  mkZero := CommSemiring.Result.mkZero
  mkOne := CommSemiring.Result.mkOne
  mkNeg a := pure (CommRing.Result.mkNeg _ a)
  mkAdd a b := pure (CommSemiring.Result.mkAdd _ a b)
  mkMul a b := pure (CommSemiring.Result.mkMul _ a b)
  mkNSMul a b rb := pure (CommSemiring.Result.mkNSMul _ a rb)
  mkZSMul a b rb := pure (CommRing.Result.mkZSMul _ a rb)
  mkSub a b := pure (CommRing.Result.mkSub _ a b)

end NormTactic
