/-
Copyright (c) 2026 Anne Baanen et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.Tactic.NormAttr
import LeanPool.RingOfIntegersProject.Tactic.NormNumBigop
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Util.Qq

open Lean Mathlib Meta Qq
open BigOperators
open NormTactic
open RoiNormNumBigop RoiNormNumBigop.NormNum

/-- Return the function (name) and arguments of an application. -/
def Lean.Expr.getAppFnLevelArgs (e : Expr) : Name × List Level × Array Expr :=
  Expr.withApp e fun e a => match e with
    | (.const _ ls) => (e.constName, ls, a)
    | _ => (e.constName, [], a)

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
def Int.mkOne : Result q((1 : ℤ)) :=
  ⟨q(1), q(rfl)⟩

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
inductive Fin.ProveZeroOrSuccResult {n : Q(ℕ)} (i : Q(Fin ($n).succ)) : Type where
  | zero (pf : Q($i = 0)) : Fin.ProveZeroOrSuccResult i
  | succ (j : Q(Fin $n)) (pf : Q($i = ($j).succ)) : Fin.ProveZeroOrSuccResult i

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
partial def Fin.proveZeroOrSucc {n : Q(ℕ)} (i : Q(Fin ($n).succ)) :
    MetaM (Fin.ProveZeroOrSuccResult i) := do
  match i.getAppFnArgs with
  | (`OfNat.ofNat, #[_, .lit (.natVal 0), (_inst : Q(OfNat (Fin ($n).succ) 0))]) => do
    have : $i =Q 0 := (← assertDefEqQ _ _).down
    pure (.zero (q(rfl) : Q($i = 0)))
  | (`OfNat.ofNat, #[_, (k : Q(ℕ)), _]) => do
    have : $i =Q OfNat.ofNat $k := (← assertDefEqQ _ _).down
    -- Note that `j` is defeq to `i`!
    let j : Q(Fin ($n).succ) := q(Fin.mk ($k % ($n).succ) (Nat.mod_lt $k (Nat.succ_pos _)))
    match ← Fin.proveZeroOrSucc j with
    | .zero j_pf => pure (.zero j_pf)
    | .succ n' j_pf => pure (.succ n' j_pf)
  | (`Fin.mk, #[_, (val : Q(ℕ)), (pf : Q($val < Nat.succ $n))]) => do
    let ⟨lit, eq_lit⟩ ← NormNum.deriveNat val q(inferInstance)
    have n := lit.natLit!
    match n with
    | 0 => do
      let n' : Q(ℕ) := .lit (.natVal 0)
      have : $i =Q Fin.mk $val $pf := ⟨⟩
      have : $lit =Q $n' := ⟨⟩
      pure (.zero q(Fin.ext (($eq_lit).to_eq rfl)))
    | .succ n => do
      have n' : Q(ℕ) := .lit (.natVal n)
      have : $i =Q Fin.mk $val $pf := ⟨⟩
      have : $lit =Q Nat.succ $n' := ⟨⟩
      have val_eq : Q($val = Nat.succ $n') := q(($eq_lit).to_eq rfl)
      let j := q(Fin.mk $n' (Nat.succ_lt_succ_iff.mp ($val_eq ▸ $pf)))
      pure (.succ j q(Fin.ext $val_eq))
  | (`Fin.succ, #[_, (j : Q(Fin $n))]) => do
    have : $i =Q Fin.succ $j := (← assertDefEqQ _ _).down
    pure (.succ j (q(rfl)))
  | (`Fin.castSucc, #[_, (j : Q(Fin $n))]) => do
    have : $i =Q Fin.castSucc $j := (← assertDefEqQ _ _).down
    match ← RoiNormNumBigop.Nat.unifyZeroOrSucc n with
    | .zero _pf =>
      throwError "Fin.proveZeroOrSucc: inconsistent context: \
        {n} is zero but Fin {n} has element {j}"
    | .succ n' _pf => do
      match ← Fin.proveZeroOrSucc (n := n') j with
      | .zero pf => return .zero q(show castSucc $j = 0 from $pf ▸ Fin.castSucc_zero)
      | .succ k pf => return (.succ q(castSucc $k)
          q(show castSucc $j = succ (castSucc $k) from $pf ▸ (Fin.succ_castSucc $k).symm))
  | (`Fin.succAbove, #[_, (j : Q(Fin ($n).succ)), (k : Q(Fin $n))]) => do
    have : $i =Q Fin.succAbove $j $k := (← assertDefEqQ _ _).down
    match ← Fin.proveZeroOrSucc j with
    | .zero j_pf =>
      pure (.succ k q(($j_pf ▸ congr_fun Fin.succAbove_zero $k : Fin.succAbove $j $k = _)))
    | .succ j' j_pf => do
      match ← RoiNormNumBigop.Nat.unifyZeroOrSucc n with
      | .zero _pf =>
        throwError "Fin.proveZeroOrSucc: inconsistent context: \
          {n} is zero but Fin {n} has element {k}"
      | .succ n' _pf => do
        match ← Fin.proveZeroOrSucc (n := n') k with
        | .zero k_pf =>
          pure (.zero q(($j_pf ▸ $k_pf ▸ Fin.succ_succAbove_zero _ : Fin.succAbove $j $k = _)))
        | .succ k' k_pf => pure (.succ q(succAbove $j' $k')
          q(($j_pf ▸ $k_pf ▸ Fin.succ_succAbove_succ $j' $k' : Fin.succAbove $j $k = _)))
  | (fn, args) => do
    throwError "Fin.proveZeroOrSucc: unsupported expression {i} ({fn}, {args})"

/-- A `norm_num` extension evaluating `Fin.val` of a concrete `Fin` element. -/
@[norm_num (Fin.val _)] partial def NormNum.evalFinVal :
    NormNum.NormNumExt where eval {u α} e := do
  -- `Fin.val` is a projection so we can't do naïve matching on `Expr.app`
  let .proj _ 0 a ← whnfR e | failure
  let .app _ (n : Q(ℕ)) ← inferType a | failure
  have a : Q(Fin $n) := a
  have : u =QL 0 := ⟨⟩
  have : $α =Q ℕ := ⟨⟩
  have : $e =Q Fin.val $a := ⟨⟩
  let ⟨n, pf⟩ ← core a
  pure (.isNat (α := q(ℕ)) (x := q(Fin.val $a)) _ n q(⟨$pf⟩))

  where
    /-- Recursively compute the numeral value of a concrete `Fin` element. -/
    core : {n : Q(ℕ)} → (a : Q(Fin $n)) → MetaM ((n : Q(ℕ)) × Q(Fin.val $a = $n)) :=
      fun {n} a => do
      -- TODO: we can probably do something smarter than unary recursion here
      match ← RoiNormNumBigop.Nat.unifyZeroOrSucc n with
      | .zero _pf =>
        throwError "evalFinVal: inconsistent context: \
          {n} is zero but `Fin {n}` has inhabitant {a}"
      | .succ n _pf => do
        match ← Fin.proveZeroOrSucc (n := n) a with
        | .zero pf => do
          pure ⟨mkRawNatLit 0, q($pf ▸ (Fin.val_zero _))⟩
        | .succ j pf => do
          let ⟨j_n, j_pf⟩ ← core j
          let nn : Q(ℕ) := mkRawNatLit (j_n.natLit! + 1)
          pure ⟨nn, (q($pf ▸ $j_pf ▸ (Fin.val_succ $j)) : Q(Fin.val $a = $j_n + 1))⟩

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
inductive Nat.ProveEvenOrOddResult (n : Q(ℕ)) : Type where
  | even : Q(Even $n) → Nat.ProveEvenOrOddResult n
  | odd : Q(Odd $n) → Nat.ProveEvenOrOddResult n

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
def Nat.proveEvenOrOdd (n : Q(ℕ)) : MetaM (Nat.ProveEvenOrOddResult n) := do
  let ⟨even?, pf⟩ ← NormNum.deriveBool q($n % 2 = 0)
  if even?
  then do
    have pf : Q($n % 2 = 0) := pf
    pure (.even q(Nat.even_iff.mpr $pf))
  else do
    have pf : Q($n % 2 ≠ 0) := pf
    pure (.odd q(not_even_iff_odd.mp (mt Nat.even_iff.mp $pf)))

variable [Monad m] [MonadLiftT MetaM m] [MResultClass m r]

/-- Try to prove that the result `res` is 0. -/
def MResultClass.zero? {u : Level} {R : Q(Type u)}
    (_instZR : Q(Zero «$R») := by with_reducible assumption)
    (α : Q($R)) (res : r α) : MetaM (Option Q($α = 0)) := do
  let ⟨x, hx⟩ := MResultClass.out m res
  match ← isDefEqQ x q(0) with
  | .defEq _h => pure <| .some q($hx)
  | .notDefEq => pure <| .none

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
def evalNegOnePowFin {u : Level} {R : Q(Type u)} (n : Q(ℕ))
    (instCSrR : Q(CommSemiring «$R») := by with_reducible assumption)
    (instCRR : Q(CommRing «$R») := by with_reducible assumption)
    (h : ($instCRR).toCommSemiring =Q $instCSrR)
    (crr : CommRingResult m r R)
    (j : Q(Fin (Nat.succ «$n»))) :
    m (r q((-1 : $R) ^ («$j» : ℕ))) := do
  have : ($instCRR).toCommSemiring =Q $instCSrR := h
  match ←(Nat.proveEvenOrOdd q(($j : ℕ))) with
  | .even pf => do
    MResultClass.eqTransM q(Even.neg_one_pow $pf) crr.mkOne
  | .odd pf => do
    let neg_one ← crr.mkNeg crr.mkOne
    MResultClass.eqTransM q(Odd.neg_one_pow $pf) neg_one

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
def evalDetTerm {u : Level} {R : Q(Type u)} (n : Q(ℕ))
    (M : Q(Matrix (Fin ($n).succ) (Fin ($n).succ) «$R»))
    (instCSrR : Q(CommSemiring «$R») := by with_reducible assumption)
    (instCRR : Q(CommRing «$R») := by with_reducible assumption)
    (h : ($instCRR).toCommSemiring =Q $instCSrR)
    (crr : CommRingResult m r R)
    (evalMatrix : (i j : Q(Fin (Nat.succ «$n»))) → m (r (α := R) q($M $i $j)))
    (evalMatrixDet : (n : Q(ℕ)) → (M' : Q(Matrix (Fin $n) (Fin $n) $R)) →
      (eM' : (i j : Q(Fin $n)) → m (r (α := R) q($M' $i $j))) →
      m (r (α := R) q(Matrix.det $M')))
    (j : Q(Fin (Nat.succ «$n»))) :
    m (r q((-1) ^ («$j» : ℕ) * «$M» 0 «$j» *
      Matrix.det (Matrix.submatrix «$M» Fin.succ (Fin.succAbove «$j»)))) := do
  let res₂ ← evalMatrix q(0) j
  -- If `res₂ = 0` we can skip the submatrix determinant computation;
  -- this should improve speed for sparse matrices.
  match ← MResultClass.zero? (r := r) (m := m) _ _ res₂ with
  | .some h => do
    MResultClass.eqTransM q(by rw [($h : $M 0 $j = 0), mul_zero, zero_mul])
      (MResultClass.uncheckedCast m crr.mkZero) -- TODO: check this cast!
  | .none => do
    let res₁ ← evalNegOnePowFin n instCSrR instCRR h crr j
    let res₃ ← evalMatrixDet n
      q(Matrix.submatrix «$M» Fin.succ (Fin.succAbove «$j»))
      (fun i' j' => do
        let res ← evalMatrix q(Fin.succ $i') q(Fin.succAbove $j $j')
        MResultClass.eqTransM q(Matrix.submatrix_apply $M _ _ $i' $j') res)
    let res₁₂ ← crr.mkMul res₁ res₂
    let res₁₂₃ ← crr.mkMul res₁₂ res₃
    return MResultClass.uncheckedCast m res₁₂₃ -- TODO: check this cast!

variable [MonadLiftT BaseIO m] [MonadLiftT IO m] [MonadRef m] [MonadTrace m]
variable [AddMessageContext m] [MonadOptions m] [MonadExcept Exception m]
variable [MonadAlwaysExcept Exception m]

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
def evalMatrixDetFinApply {n' : Q(ℕ)} {R : Q(Type u)}
    (M : Q(Matrix (Fin $n') (Fin $n') $R))
    (instCSrR : Q(CommSemiring «$R») := by with_reducible assumption)
    (instCRR : Q(CommRing «$R») := by with_reducible assumption)
    (h : ($instCRR).toCommSemiring =Q $instCSrR)
    (crr : CommRingResult m r R)
    (evalMatrix : (i j : Q(Fin $n')) → m (r (α := R) q($M $i $j)))
    (evalMatrixDet : (n : Q(ℕ)) → (M' : Q(Matrix (Fin $n) (Fin $n) $R)) →
      (eM' : (i j : Q(Fin $n)) → m (r (α := R) q($M' $i $j))) →
      m (r (α := R) q(Matrix.det $M'))) :
    m (r q(Matrix.det $M)) :=
  withTraceNode `norm.Matrix.Det (return m!"{·.emoji} determinant of: {M}") do
  match ← RoiNormNumBigop.Nat.unifyZeroOrSucc n' with
  | .zero _pf => MResultClass.eqTransM q(Matrix.det_fin_zero) crr.mkOne
  | .succ n _pf => do
    trace[norm.Matrix.Det] "evalMatrixDetFinApply: {M}"
    let M' : Q(Fin ($n).succ → Matrix (Fin $n) (Fin $n) $R) :=
      q(fun j => Matrix.submatrix $M Fin.succ (Fin.succAbove j))
    let f : Q(Fin ($n).succ → $R) :=
      q(fun j => (-1) ^ (j : ℕ) * $M 0 j * Matrix.det ($M' j))
    let resEmpty : r q(Finset.empty.sum $f) ← MResultClass.eqTransM q(Finset.sum_empty) crr.mkZero
    let res : r _ ← RoiNormNumBigop.NormNum.evalFinsetBigop
      (α := q(Fin ($n).succ)) (β := R) q(Finset.sum) f
      (fun j => do
        let res ← evalDetTerm n M instCSrR instCRR h crr evalMatrix evalMatrixDet j
        MResultClass.eqTransM q(rfl) res) -- TODO: why do we need an extra `rfl`?
      (MResultClass.uncheckedCast m resEmpty) -- TODO: why doesn't this unify?
      (fun {_a _s _h} x xs => do
        let res ← crr.mkAdd x xs
        MResultClass.eqTransM q(Finset.sum_cons _) res)
      (q(Finset.univ) : Q(Finset (Fin ($n).succ)))
    MResultClass.eqTransM q(Matrix.det_succ_row_zero (R := $R) (n := $n) $M) res

/-- Ties the recursive knot arising from `evalMatrixDetFinApply`. -/
partial def evalMatrixDetFin {n' : Q(ℕ)} {R : Q(Type u)}
    (M : Q(Matrix (Fin $n') (Fin $n') $R))
    (instCSrR : Q(CommSemiring «$R») := by with_reducible assumption)
    (instCRR : Q(CommRing «$R») := by with_reducible assumption)
    (h : ($instCRR).toCommSemiring =Q $instCSrR)
    (crr : CommRingResult m r R)
    (evalMatrix : (i j : Q(Fin $n')) → m (r (α := R) q($M $i $j))) :
    m (r q(Matrix.det $M)) :=
  evalMatrixDetFinApply M instCSrR instCRR h crr evalMatrix
    (fun _n M evalM => evalMatrixDetFin M instCSrR instCRR h crr evalM)

variable [MonadError m]

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
partial def normVecCons {R : Q(Type u)} {s : Q(ℕ)}
    (M : Q((Fin $s) → $R)) (i : Q(Fin $s)) :
    m (r (α := R) q($M $i)) := do
  match M.getAppFnArgs with
  | (`Matrix.vecCons, #[(_R' : Q(Type u)), (n : Q(ℕ)), (hd : Q($R)), (tl : Q(Fin $n → $R))]) =>
    withTraceNode `norm.Matrix.Det (return m!"{·.emoji} normVecCons: {hd} {tl} {i}") do
    have : $s =Q Nat.succ $n := (← assertDefEqQ _ _).down
    have : $M =Q Matrix.vecCons $hd $tl := ⟨⟩
    match ← Fin.proveZeroOrSucc (n := n) i with
    | .zero pf => do
      let res : r hd ← MResultClass.rflM
      MResultClass.eqTransM q($pf ▸ Matrix.cons_val_zero $hd $tl) res
    | .succ j pf => do
      let res ← normVecCons tl j
      MResultClass.eqTransM q($pf ▸ Matrix.cons_val_succ $hd $tl $j) res
  | (fn, args) => throwError "normVecCons: unsupported expression {M} ({fn}, {args})"

/-- A `simp` procedure evaluating indexing into a `Matrix.vecCons` vector literal. -/
simproc normVecCons.simproc (Matrix.vecCons _ _ _) :=
  /- A term of type `Expr → SimpM (Option Step) -/
  fun e => do
    guard (e.isAppOfArity ``Matrix.vecCons 5)
    match e.getAppFnLevelArgs with
    | (`Matrix.vecCons, [u], #[R, (s : Q(ℕ)), _h, _t, _i]) => do
      let M := e.appFn!
      let i := e.appArg!

      let r ← normVecCons (m := MetaM) (r := Result) (u := u) (R := R) (s := q(Nat.succ $s)) M i

      return .visit { expr := r.val, proof? := r.pf }
    | _ => failure

example : ![1, 2, 3, 4] (Fin.succ 0) = 2 := by simp only [normVecCons.simproc]
example : ![1, 2, 3, 4] 2 = 3 := by simp only [normVecCons.simproc]
example : ![1, 2, 3, 4] 1 = 2 := by simp only [normVecCons.simproc]

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
def evalMatrixOf {R : Q(Type u)} {s n : Q(ℕ)}
    (M : Q((Fin $s) → (Fin $n) → $R)) (i : Q(Fin $s)) (j : Q(Fin $n)) :
    m (r (α := R) q(Matrix.of $M $i $j)) := do
  let res₁ : r _ ← normVecCons (R := q(Fin $n → $R)) M i
  let ⟨v₁, p₁⟩ := MResultClass.out m res₁
  let res₂ ← normVecCons (R := R) v₁ j
  MResultClass.eqTransM q($p₁ ▸ Matrix.of_apply $M $i $j) res₂

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
def normMatrixOf {R : Q(Type u)} {s n : Q(ℕ)}
    (M : Q(Matrix (Fin $s) (Fin $n) $R)) (i : Q(Fin $s)) (j : Q(Fin $n)) :
    m (r (α := R) q($M $i $j)) := do
  -- Should match `(@DFunLike.coe _ _ _ _ (@Matrix.of s n α) M)
  match M.getAppFnArgs with
  | (`DFunLike.coe, #[_, _, _, _, matrixOf, (M' : Q(Fin $s → Fin $n → $R))]) => do
    match matrixOf.getAppFnArgs with
    | (`Matrix.of, #[(m' : Q(Type)), (n' : Q(Type)), (α : Q(Type u))]) => do
      have : $m' =Q Fin $s := ⟨⟩
      have : $n' =Q Fin $n := ⟨⟩
      have : $α =Q $R := ⟨⟩
      have : $M =Q Matrix.of $M' := ⟨⟩
      let res ← evalMatrixOf M' i j
      MResultClass.eqTransM q(rfl) res -- FIXME: why the `trans_eq`?
    | (fn, args) =>
      throwError "normMatrixOf: unsupported expression {M} (coeFn ({fn}, {args}) {M'})"
  | (fn, args) => throwError "normMatrixOf: unsupported expression {M} ({fn}, {args})"

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
def normMatrixOf' {R : Q(Type u)} {ι κ : Q(Type v)}
    (M : Q(Matrix $ι $κ $R)) (i : Q($ι)) (j : Q($κ)) :
    m (r (α := R) q($M $i $j)) := do
  match v with
  | .zero =>
    match ι, κ with
    | ~q(Fin $m), ~q(Fin $n) => normMatrixOf (s := m) (n := n) M i j
    | _ => throwError "normMatrixOf': unsupported expression {M}: types {ι} {κ} should be `Fin`"
  | _ => throwError "normMatrixOf': unsupported expression {M}: types {ι} {κ} \
    should be `Fin` (universe level mismatch {v} != 0)"

/-- A `simp` procedure evaluating indexing into a `Matrix.of` matrix literal. -/
simproc normMatrixOf.simproc (DFunLike.coe Matrix.of _ _ _) :=
  /- A term of type `Expr → SimpM (Option Step) -/
  fun e => do
    match e.getAppFnLevelArgs with
    | (`DFunLike.coe, [_u, _v, _w], #[_, _, _, _, matrixOf, M, i, j]) => do
      match matrixOf.getAppFnLevelArgs with
      | (`Matrix.of, [0, 0, u], #[ι, κ, R]) => do
        withTraceNode `norm.Matrix.Det (return m!"{·.emoji} matrix: {M} {i} {j}") do
        guard (ι.isAppOfArity ``Fin 1)
        let s := ι.appArg!
        guard (κ.isAppOfArity ``Fin 1)
        let n := κ.appArg!
        let r ← evalMatrixOf (m := MetaM) (r := Result) (u := u) (R := R) (s := s) (n := n) M i j

        return .visit { expr := r.val, proof? := r.pf }
      | _ => failure
    | _ => failure

example : !![1, 2, 3, 4; 5, 6, 7, 8] (Fin.succ 0) (Fin.succ (Fin.succ 0)) = 7 := by
  simp only [normMatrixOf.simproc]


open BigOperators in

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
def evalMatrixDetDiagonal {n' : Q(ℕ)} {R : Q(Type u)}
    (s : Q(Fin $n' → $R))
    (instCSrR : Q(CommSemiring «$R») := by with_reducible assumption)
    (instCRR : Q(CommRing «$R») := by with_reducible assumption)
    (h : ($instCRR).toCommSemiring =Q $instCSrR)
    (crr : CommRingResult m r R) :
    m (r q(Matrix.det (Matrix.diagonal $s))) :=
  withTraceNode `norm.Matrix.Det (return m!"{·.emoji} determinant of: Matrix.diagonal {s}") do
  have : ($instCRR).toCommSemiring =Q $instCSrR := h
  let res ← RoiNormNumBigop.NormNum.evalFinsetBigop
    _
    q(fun i => $s i)
    (fun i => do MResultClass.eqTransM q(rfl) (←normVecCons s i))
    (MResultClass.uncheckedCast m -- FIXME: why is this needed?
      (← MResultClass.eqTransM q(Finset.prod_empty (f := fun i => $s i)) crr.mkOne))
    (fun {_ _ _} res_ma res_s => do
      let res_prod ← crr.mkMul res_ma res_s
      MResultClass.eqTransM q(Finset.prod_cons _) res_prod)
    q(Finset.univ)
  MResultClass.eqTransM q(Matrix.det_diagonal) res

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
partial def evalMatrixDet {R : Q(Type u)} {ι : Q(Type v)}
    (instCSrR : Q(CommSemiring «$R») := by with_reducible assumption)
    (instCRR : Q(CommRing «$R») := by with_reducible assumption)
    (instDEι : Q(DecidableEq $ι) := by with_reducible assumption)
    (instFTι : Q(Fintype $ι) := by with_reducible assumption)
    (h : ($instCRR).toCommSemiring =Q $instCSrR)
    (M : Q(Matrix $ι $ι $R))
    (crr : CommRingResult m r R)
    (normMatrix : (i : Q($ι)) → (j : Q($ι)) → m (r (α := R) q($M $i $j))) :
    m (r q(Matrix.det $M)) := do
  let v : Level := ← mkFreshLevelMVar
  match ι.getAppFnArgs with
  | (`Fin, #[(n : Q(ℕ))]) => do
    try
      match M.getAppFnArgs with
      | (`Matrix.diagonal,
          #[_, _, (instDEι' : Q(DecidableEq $ι)), (_instZ : Q(Zero $R)), (s : Q($ι → $R))]) => do
        have : $instDEι =Q $instDEι' := ⟨⟩
        have : $M =Q Matrix.diagonal $s := ⟨⟩
        return MResultClass.uncheckedCast m
          (← evalMatrixDetDiagonal (n' := n) s instCSrR instCRR h crr)
      | _ => do
        let x ← evalMatrixDetFin (n' := n) M instCSrR instCRR h crr normMatrix
        return MResultClass.uncheckedCast m x
    catch e =>
      trace[norm.Matrix.Det] "internal error: {e.toMessageData}"
      throw e
  | _ => throwError "expected `Fin n`, got {ι}"

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
partial def normMatrixDet {R : Q(Type u)} (e : Q($R))
    (instCSrR : Q(CommSemiring «$R») := by with_reducible assumption)
    (instCRR : Q(CommRing «$R») := by with_reducible assumption)
    (h : ($instCRR).toCommSemiring =Q $instCSrR)
    (crr : CommRingResult m r R)
    (normMatrix : {v : Level} → {ι κ : Q(Type v)} → (M : Q(Matrix $ι $κ $R)) →
        (i : Q($ι)) → (j : Q($κ)) →
        m (r (α := R) q($M $i $j))) :
    m (r e) := do
  match e with
  | ~q(@Matrix.det ($ι) ($instDEι) ($instFTι) _ _ ($M)) => do
    let res ← evalMatrixDet instCSrR instCRR instDEι instFTι h M crr (normMatrix M)
    MResultClass.eqTransM q(rfl) res
  | _ => throwError "expected `Matrix.det M`, got {e}"

variable [MonadLiftT SimpM m]

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
def _root_.Lean.Meta.Simp.Result.toMResult {α : Q(Type u)} {e : Q($α)} (res : Simp.Result) :
    m (r e) := do
  have e' : Q($α) := res.expr
  match res.proof? with
  | none => do
    let res' ← MResultClass.rflM (a := e')
    return MResultClass.uncheckedCast (m := m) res'
  | some pf => do
    let res' ← MResultClass.rflM (a := e')
    MResultClass.eqTransM pf res'

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
partial def simpMatrix {R : Q(Type u)} {ι κ : Q(Type v)} (M : Q(Matrix $ι $κ $R))
    (i : Q($ι)) (j : Q($κ)) :
    m (r (α := R) q($M $i $j)) := do
  let expr := q($M $i $j)
  trace[norm.Matrix.Det] "simpMatrix: simplifying {expr}"
  let r ← liftM (m := SimpM) (Simp.simpImpl expr <|> pure { expr := expr, proof? := none })
  trace[norm.Matrix.Det] "simpMatrix: simplified to {r.expr}"
  r.toMResult

/-- Evaluate the determinant of a matrix in an arbitrary commutative ring.

See also `normMatrixDet`, which you can specialize for more complicated data types,
for example to take into account the characteristic of the ring.
-/
def convMatrixDet {R : Q(Type u)} (e : Q($R)) : MetaM (Result e) := do
  let instCRR : Q(CommRing $R) ← synthInstanceQ (q(CommRing $R) : Q(Type u))
  let instCSrR : Q(CommSemiring $R) := q(($instCRR).toCommSemiring)
  trace[norm.Matrix.Det] "running on {e}"
  normMatrixDet e instCSrR instCRR ⟨⟩ (CommRingResult.default _ 0 none)
    (normMatrix := normMatrixOf')

/-- Evaluate the determinant of a matrix in an arbitrary commutative ring, using the simplifier.

See also `normMatrixDet`, which you can specialize for more complicated data types,
for example to take into account the characteristic of the ring.
-/
def simpMatrixDet {R : Q(Type u)} (e : Q($R)) : SimpM (Result e) := do
  let instCRR : Q(CommRing $R) ← synthInstanceQ (q(CommRing $R) : Q(Type u))
  let instCSrR : Q(CommSemiring $R) := q(($instCRR).toCommSemiring)
  trace[norm.Matrix.Det] "simpMatrixDet: running on {e}"
  normMatrixDet e instCSrR instCRR ⟨⟩ (CommRingResult.default _ 0 none) (normMatrix := simpMatrix)

/-- Use `f` to simplify at each position. -/
partial def derive (f : {u : Level} → {α : Q(Type u)} → (e : Q($α)) → MetaM (Result e))
    (e : Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e

  let config : Simp.Config := {
    zeta := false
    beta := false
    eta  := false
    proj := false
    iota := false
  }
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx : Simp.Context ← Simp.mkContext config
    (simpTheorems := #[]) (congrTheorems := congrTheorems)
  let discharge : Expr → SimpM (Option Expr) := Mathlib.Meta.NormNum.discharge
  let r : Simp.Result := {expr := e}

  let simprocs ← Simp.getSimprocs
  let pre e := do
    (Simp.andThen (Simp.preDefault #[simprocs]) <| fun e _ => do
      let ⟨u', α, e⟩ ← inferTypeQ e
      let u ← (u'.dec).getM -- `α : Sort u'`, turn this into `α : Type u`
      have α : Q(Type u) := α
      try
        let r ← f (u := ← instantiateLevelMVars u) (α := ← instantiateMVars α)
          (← instantiateMVars e)
        return Simp.Step.done r.toSimpResult
      catch _ => pure Simp.Step.continue) e
  let post e := do
    Simp.postDefault #[simprocs] e
  let proc := fun e => Simp.main e ctx (methods := { pre, post, discharge? := discharge })
  r.mkEqTrans (← proc e).1

/-- Use `f` to simplify at each position. -/
partial def simpDerive (f : {u : Level} → {α : Q(Type u)} → (e : Q($α)) → SimpM (Result e))
    (e : Expr) : MetaM Simp.Result := do
  let e ← instantiateMVars e

  let config : Simp.Config := {
    zeta := false
    beta := false
    eta  := false
    proj := false
    iota := false
  }
  let congrTheorems ← Meta.getSimpCongrTheorems
  let simpTheorems ← Meta.getSimpTheorems
  let ctx : Simp.Context ← Simp.mkContext config
    (simpTheorems := #[simpTheorems]) (congrTheorems := congrTheorems)
  let discharge : Expr → SimpM (Option Expr) := Mathlib.Meta.NormNum.discharge
  let r : Simp.Result := {expr := e}

  let simprocs ← Simp.getSimprocs
  let pre e := do
    (Simp.andThen (Simp.preDefault #[simprocs]) <| fun e => do
      let ⟨u', α, e⟩ ← inferTypeQ e
      let u ← (u'.dec).getM -- `α : Sort u'`, turn this into `α : Type u`
      have α : Q(Type u) := α
      try
        let r ← f (u := ← instantiateLevelMVars u) (α := ← instantiateMVars α)
          (← instantiateMVars e)
        return Simp.Step.done r.toSimpResult
      catch _ => pure (Simp.Step.continue)) e
  let post e := do
    Simp.postDefault #[simprocs] e
  let proc := fun e => Simp.main e ctx (methods := { pre, post, discharge? := discharge })
  r.mkEqTrans (← proc e).1

open Lean Elab Tactic

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
partial def convTarget (f : {u : Level} → {α : Q(Type u)} → (e : Q($α)) → MetaM (Result e)) :
    TacticM Unit := do
  liftMetaTactic1 fun goal ↦ do
    let tgt ← instantiateMVars (← goal.getType)
    let prf ← derive @f tgt
    if prf.expr.consumeMData.isConstOf ``True then
      match prf.proof? with
      | some proof => goal.assign (← mkOfEqTrue proof)
      | none => goal.assign (mkConst ``True.intro)
      return none
    else
      applySimpResultToTarget goal tgt prf

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
partial def convHyp (f : {u : Level} → {α : Q(Type u)} → (e : Q($α)) → MetaM (Result e))
    (fvarId : FVarId) : TacticM Unit :=
  liftMetaTactic1 fun goal ↦ do
    let hyp ← instantiateMVars (← fvarId.getDecl).type
    let prf ← derive @f hyp
    return (← applySimpResultToLocalDecl goal fvarId prf false).map (·.snd)

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
partial def simpTarget (f : {u : Level} → {α : Q(Type u)} → (e : Q($α)) → SimpM (Result e)) :
    TacticM Unit := do
  liftMetaTactic1 fun goal ↦ do
    let tgt ← instantiateMVars (← goal.getType)
    let prf ← simpDerive @f tgt
    if prf.expr.consumeMData.isConstOf ``True then
      match prf.proof? with
      | some proof => goal.assign (← mkOfEqTrue proof)
      | none => goal.assign (mkConst ``True.intro)
      return none
    else
      applySimpResultToTarget goal tgt prf

/-- Auxiliary definition for the matrix-determinant `norm`/`simp` tactic. -/
partial def simpHyp (f : {u : Level} → {α : Q(Type u)} → (e : Q($α)) → SimpM (Result e))
    (fvarId : FVarId) : TacticM Unit :=
  liftMetaTactic1 fun goal ↦ do
    let hyp ← instantiateMVars (← fvarId.getDecl).type
    let prf ← simpDerive @f hyp
    return (← applySimpResultToLocalDecl goal fvarId prf false).map (·.snd)

open Parser.Tactic Elab.Tactic

/-- Normalise matrix determinants in the goal (or given location) by `conv`-rewriting. -/
syntax (name := conv_test) "conv_test" (location)? : tactic
/-- Normalise matrix determinants in the goal (or given location) via `simp`. -/
syntax (name := simp_test) "simp_test" (location)? : tactic

elab_rules : tactic
| `(tactic| conv_test) => unsafe do
  convTarget convMatrixDet
| `(tactic| conv_test $loc) => unsafe do
  withMainContext do
    match expandOptLocation loc with
    | Location.targets hyps target =>
      if target then convTarget convMatrixDet
      (← getFVarIds hyps).forM (convHyp convMatrixDet)
    | Location.wildcard =>
      convTarget convMatrixDet
      (← (← getMainGoal).getNondepPropHyps).forM (convHyp convMatrixDet)

elab_rules : tactic
| `(tactic| simp_test) => unsafe do
  simpTarget simpMatrixDet
| `(tactic| simp_test $loc) => unsafe do
  withMainContext do
    match expandOptLocation loc with
    | Location.targets hyps target =>
      if target then simpTarget simpMatrixDet
      (← getFVarIds hyps).forM (simpHyp simpMatrixDet)
    | Location.wildcard =>
      simpTarget simpMatrixDet
      (← (← getMainGoal).getNondepPropHyps).forM (simpHyp simpMatrixDet)

