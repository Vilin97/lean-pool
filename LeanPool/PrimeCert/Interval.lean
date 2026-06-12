/-
Copyright (c) 2026 Kenny Lau, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Bhavik Mehta
-/

import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Ring.Nat

/-! # Interval checking by binary search

The `checkInterval` tactic proves goals of the form
`∀ n, lo ≤ n → n < hi → P n` or `∀ n, lo ≤ n → n < hi → n % b = r → P n`
by building a balanced binary tree of `eagerReduce` proof terms, one per value in the range.
-/

section forallB

/-- `forallB f start len step` is `true` iff `f` holds on every element of
`List.range' start len step`. -/
noncomputable def forallB (f : ℕ → Bool) (start len : ℕ) (step : ℕ := 1) : Bool :=
  (Nat.rec (motive := fun _ ↦ ℕ × Bool) (start, true)
    (fun _ ih ↦ ih.rec fun i b ↦ (i.add step, (f i).and' b)) len).2

theorem forallB_iff_range' (f : ℕ → Bool) (start len step : ℕ) :
    forallB f start len step ↔ ∀ n ∈ List.range' start len step, f n := by
  unfold forallB
  simp only [Bool.and'_eq_and]
  induction len with
  | zero => simp
  | succ len ih =>
    simp only [Bool.and_eq_true, ih, List.range'_concat, List.forall_mem_append,
      List.forall_mem_singleton, and_comm]
    refine and_congr_left fun _a ↦ Eq.congr_left <| congr_arg f ?_
    clear ih _a
    induction len with
    | zero => simp
    | succ len ih => simp only; rw [ih, Nat.add_eq, mul_add_one, add_assoc]

theorem forallB_iff (f : ℕ → Bool) (start len step : ℕ) :
    forallB f start len step ↔ ∀ n < len, f (n * step + start) := by
  simp_rw [add_comm, mul_comm, forallB_iff_range', List.mem_range']; aesop

theorem forallB_iff' (f : ℕ → Bool) (start r len step : ℕ) :
    forallB f (start * step + r) len step ↔
    ∀ n, start ≤ n → n < start + len → f (n * step + r) := by
  simp_rw [forallB_iff, ← add_assoc, ← add_mul, le_iff_exists_add, exists_imp,
    forall_eq_apply_imp_iff, add_lt_add_iff_left, add_comm]

theorem forallB_one_iff (f : ℕ → Bool) (start len : ℕ) :
    forallB f start len ↔ ∀ n, start ≤ n → n < start + len → f n := by
  simp_rw [forallB_iff_range', List.mem_range'_1, and_imp]

end forallB

section forall_step
/-! # Tools for automation of ∀ n, lo ≤ n → n < hi → P n -/

theorem forall_start {P : ℕ → Prop} {hi : ℕ}
    (ih : ∀ n, 0 ≤ n → n < hi → P n) : ∀ n < hi, P n :=
  fun n hn ↦ ih n n.zero_le hn

theorem forall_step {P : ℕ → Prop} {curr hi : ℕ} (next : ℕ)
    (now : P curr) (h : curr.succ = next) (ih : ∀ n, next ≤ n → n < hi → P n) :
    ∀ n, curr ≤ n → n < hi → P n :=
  fun n hn₁ hn₂ ↦ (eq_or_lt_of_le hn₁).elim (· ▸ now) fun hn₃ ↦ ih n (h ▸ hn₃) hn₂

theorem forall_bisect {P : ℕ → Prop} {lo hi : ℕ} (mi : ℕ)
    (h₁ : ∀ n, lo ≤ n → n < mi → P n)
    (h₂ : ∀ n, mi ≤ n → n < hi → P n) :
    ∀ n, lo ≤ n → n < hi → P n :=
  fun n hn₁ hn₂ ↦ (le_or_gt mi n).elim (h₂ n · hn₂) (h₁ n hn₁ ·)

theorem forall_succ {P : ℕ → Prop} {lo hi : ℕ} (h : P lo) (spec : hi.ble lo.succ := by rfl) :
    ∀ n, lo ≤ n → n < hi → P n :=
  fun _n hn₁ hn₂ ↦ le_antisymm hn₁
    (Nat.le_of_lt_succ <| hn₂.trans_le <| Nat.le_of_ble_eq_true spec) ▸ h

theorem forall_last {P : ℕ → Prop} {hi : ℕ} :
    ∀ n, hi ≤ n → n < hi → P n :=
  fun _n hn₁ hn₂ ↦ (not_lt_of_ge hn₁ hn₂).elim

theorem forall_exceed {P : ℕ → Prop} {lo hi : ℕ} (h : hi.ble lo) :
    ∀ n, lo ≤ n → n < hi → P n :=
  fun _n hn₁ hn₂ ↦ (not_le_of_gt (hn₁.trans_lt hn₂) <| Nat.le_of_ble_eq_true h).elim

end forall_step

section forall_mod
/-! # Tools for automation of ∀ n, lo ≤ n → n < hi → n % b = r → P n -/

theorem forall_mod_start {P : ℕ → Prop} {hi b r : ℕ}
    (ih : ∀ n, r ≤ n → n < hi → n % b = r → P n) :
    ∀ n < hi, n % b = r → P n :=
  fun n h₂ h₃ ↦ ih n (h₃ ▸ Nat.mod_le n b) h₂ h₃

theorem forall_mod_step {P : ℕ → Prop} {lo hi b r : ℕ} (next : ℕ)
    (now : P lo) (ih : ∀ n, next ≤ n → n < hi → n % b = r → P n)
    (spec₁ : lo + b = next := by rfl) (spec₂ : lo % b = r := by rfl) :
    ∀ n, lo ≤ n → n < hi → n % b = r → P n :=
  fun n h₁ h₂ h₃ ↦ (eq_or_lt_of_le h₁).elim (· ▸ now) fun h₁ ↦ by
    suffices next ≤ n from ih n this h₂ h₃
    rw [← spec₁]
    rw [← Nat.div_add_mod' lo b, ← Nat.div_add_mod' n b, spec₂, h₃] at h₁ ⊢
    replace h₁ := Nat.succ_le_of_lt <| lt_of_mul_lt_mul_right' <| (add_lt_add_iff_right _).mp h₁
    grw [add_right_comm, ← Nat.succ_mul, h₁]

-- A useful closing tool.
theorem forall_mod_succ {P : ℕ → Prop} {lo hi b r : ℕ}
    (now : P lo) (spec₁ : lo % b = r := by rfl) (spec₂ : hi.ble (lo.add b) := by rfl) :
    ∀ n, lo ≤ n → n < hi → n % b = r → P n :=
  forall_mod_step (lo + b) now (forall_exceed spec₂) rfl spec₁

-- For convenience (so that `P` does not need to change).
theorem forall_mod_bisect {P : ℕ → Prop} {lo hi b r : ℕ} (mi : ℕ)
    (ih₁ : ∀ n, lo ≤ n → n < mi → n % b = r → P n)
    (ih₂ : ∀ n, mi ≤ n → n < hi → n % b = r → P n) :
    ∀ n, lo ≤ n → n < hi → n % b = r → P n :=
  forall_bisect mi ih₁ ih₂

-- For convenience (so that `P` does not need to change).
theorem forall_mod_exceed {P : ℕ → Prop} {lo hi b r : ℕ} (h : hi.ble lo) :
    ∀ n, lo ≤ n → n < hi → n % b = r → P n :=
  forall_exceed h

end forall_mod

section Meta

open Lean Meta

local notation:max "rnl%" n => mkRawNatLit n
local notation:max "reflNat%" n => mkApp2 (mkConst `Eq.refl [1]) (mkConst `Nat) n

/-- An expression to prove statement of the form `∀ n, lo ≤ n → n < hi → P n` -/
def makeForallBisectLoHi (P : Expr) (lo hi : ℕ) (pf : ℕ → Expr) : Expr :=
  if hi ≤ lo + 1 then
    mkApp5 (mkConst ``forall_succ) P (rnl% lo) (rnl% hi) (pf lo) reflBoolTrue
  else
    have mi := (lo + hi) / 2
    mkApp6 (mkConst ``forall_bisect) P (rnl% lo) (rnl% hi) (rnl% mi)
      (makeForallBisectLoHi P lo mi pf)
      (makeForallBisectLoHi P mi hi pf)

/-- An expression to prove statement of the form `∀ n < hi → P n` -/
def makeForallBisectHi (P : Expr) (hi : ℕ) (pf : ℕ → Expr) : Expr :=
  mkApp3 (mkConst ``forall_start) P (rnl% hi) <| makeForallBisectLoHi P 0 hi pf

/-- An expression to prove statement of the form `∀ n, lo ≤ n → n < hi → n % b = r → P n`.
This always assumes `lo % b = r`.

The `fuel` argument bounds the recursion depth so the definition is structurally recursive.
Each bisection at least halves the number of residue-class representatives in `[lo, hi)`, so the
recursion depth is at most `hi`; the callers supply that much fuel and the `fuel = 0` branch is
therefore never reached. -/
def makeForallModBisectLoHi
    (fuel : ℕ) (P : Expr) (lo hi b r : ℕ) (bE rE : Expr) (pf : ℕ → Expr) : Expr :=
  match fuel with
  | 0 =>
    mkApp8 (mkConst ``forall_mod_succ)
      P (rnl% lo) (rnl% hi) bE rE (pf lo) (reflNat% rE) reflBoolTrue
  | fuel + 1 =>
    if hi ≤ lo + b then
      mkApp8 (mkConst ``forall_mod_succ)
        P (rnl% lo) (rnl% hi) bE rE (pf lo) (reflNat% rE) reflBoolTrue
    else
      have mi := (lo / b + (hi - r) / b + 1) / 2 * b + r
      mkApp8 (mkConst ``forall_mod_bisect) P (rnl% lo) (rnl% hi) bE rE (rnl% mi)
        (makeForallModBisectLoHi fuel P lo mi b r bE rE pf)
        (makeForallModBisectLoHi fuel P mi hi b r bE rE pf)

/-- An expression to prove statement of the form `∀ n < hi → n % b = r → P n`. -/
def makeForallModBisectHi
    (P : Expr) (hi b r : ℕ) (bE rE : Expr) (pf : ℕ → Expr) : Expr :=
  mkApp5 (mkConst ``forall_mod_start) P (rnl% hi) bE rE <|
    makeForallModBisectLoHi hi P r hi b r bE rE pf

/-- Tactic to prove bounded universal statements by exhaustive kernel checking.
Accepts four goal shapes:

- `∀ n < hi, P n`
- `∀ n, lo ≤ n → n < hi → P n`
- `∀ n < hi, n % b = r → P n`
- `∀ n, lo ≤ n → n < hi → n % b = r → P n`

The predicate `P n` must reduce to `true` (via `eagerReduce`) for every `n` in range.
The tactic builds a balanced binary tree of proof terms, so the elaboration depth is
logarithmic in the range size.

```lean
-- Check that wieferichKR is false or mirimanoffKR is false for all n ≡ 1 (mod 6), n < 6000:
theorem wieferich_mirimanoff₁ : ∀ n < 6000, n % 6 = 1 →
    (wieferichKR n).not'.or' (mirimanoffKR n).not' := by
  checkInterval
```
-/
elab "checkInterval" : tactic => Elab.Tactic.liftMetaFinishingTactic fun mId ↦ do
  let goal ← inferType <| .mvar mId
  let .forallE _ _ P₀ _ := goal | throwError "goal is not ∀"
  let .forallE _ P₁ P₂ _ := P₀ | throwError "goal is not bounded (1)"
  let mut lo? : Option ℕ := none
  let mut hiPE : Expr := default
  let mut P : Expr := default
  match P₁.getAppFnArgs with
  | (``LE.le, #[_, _, loE, .bvar _]) =>
    lo? := loE.nat?
    unless lo?.isSome do throwError "goal is not bounded (2)"
    let .forallE _ P₃ P₄ _ := P₂ | throwError "goal is not bounded (3)"
    hiPE := P₃
    P := P₄
  | _ =>
    hiPE := P₁
    P := P₂
  let (``LT.lt, #[_, _, .bvar _, hiE]) := hiPE.getAppFnArgs | throwError "goal is not bounded (4)"
  let some hi := hiE.nat? | throwError "goal is not bounded (5)"
  have br? : Option (ℕ × ℕ × Expr) := do
    let .forallE _ P₅ P₆ _ := P | none
    let (``Eq, #[_, e, rE]) := P₅.getAppFnArgs | none
    let (``HMod.hMod, #[_, _, _, _, .bvar _, bE]) := e.getAppFnArgs | none
    return (← bE.nat?, ← rE.nat?, P₆)
  if let some (_, _, PE) := br? then P := PE
  P := P.lowerLooseBVars 1 1 |>.lowerLooseBVars 1 1 |>.lowerLooseBVars 1 1
  P := .lam `n (mkConst ``Nat) P .default
  match lo?, br? with
  | some lo, none =>
    mId.assign <| makeForallBisectLoHi P lo hi fun _ ↦ reflBoolTrue
  | none, none =>
    mId.assign <| makeForallBisectHi P hi fun _ ↦ reflBoolTrue
  | some lo, some (b, r, _) =>
    mId.assign <| makeForallModBisectLoHi hi P lo hi b r (rnl% b) (rnl% r) fun _ ↦ reflBoolTrue
  | none, some (b, r, _) =>
    mId.assign <| makeForallModBisectHi P hi b r (rnl% b) (rnl% r) fun _ ↦ reflBoolTrue

end Meta
