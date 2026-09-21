/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import Mathlib.Tactic

/-!
# The row-proof arithmetic layer, deep-embedded

This is step A of the proof-data source: affine forms, contexts, and the
entailment checker of the format spec §4.1 / §13.4, as `Bool` functions over
`List ℤ`, proved sound once.

## Representation discipline

Everything generated is `List ℤ` addressed with `List.getD`.  No `![…]`, no
`Fin`-indexed functions, no `Matrix.cons`.  This is not a style preference:
the accompanying analysis §5 measured 198 s of kernel
type-checking for one `rfl` through `![…]` at a `Fin` numeral against 15 ms
for the same goal by `decide`, and the accompanying analysis records 189,527
unfoldings of `instDecidableEqSum.decEq` from the same family of mistake.

## The one design decision worth recording

A form `c + Σ aᵢ xᵢ` is stored as the single list `c :: a`, and evaluated as
`dot g (1 :: x)` — the constant is just the coefficient of a leading `1`
coordinate.  Evaluation is then *literally* a dot product, so it is additive
and homogeneous in the form by two three-line inductions, and every soundness
step downstream is linear algebra rather than case analysis on the head.

Out-of-range certificate indices need no bounds check.  `List.getD` returns
`[]` there, `eval [] x = 0`, and a zero row is harmless on both sides: with a
nonnegative multiplier it contributes `0 ≥ 0` to the inequality part, and any
multiplier contributes `0` to the equality part.  So the checker is
fail-closed on malformed indices without spending a comparison on them.
-/

namespace Utilities.Subdivision.ClosedRowProof


/-- An affine form `c + Σ aᵢ xᵢ`, stored as `c :: a`. -/
abbrev Form := List ℤ

/-- Dot product, truncating at the shorter list. -/
def dot : List ℤ → List ℤ → ℤ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => a * b + dot as bs

/-- Evaluate a form at a point.  The constant term is the coefficient of the
leading `1`, which makes `eval` a dot product and hence linear in the form. -/
def eval (g : Form) (x : List ℤ) : ℤ := dot g (1 :: x)

@[simp] theorem dot_nil_left (y : List ℤ) : dot [] y = 0 := rfl

@[simp] theorem dot_nil_right (l : List ℤ) : dot l [] = 0 := by
  cases l <;> rfl

@[simp] theorem eval_nil (x : List ℤ) : eval [] x = 0 := rfl

/-- Sum of two forms, aligned at the constant term. -/
def addForm : Form → Form → Form
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: addForm as bs

/-- Scalar multiple of a form. -/
def smulForm (k : ℤ) (f : Form) : Form := f.map (fun a => k * a)

/-- Difference of two forms. -/
def subForm (f g : Form) : Form := addForm f (smulForm (-1) g)

theorem dot_addForm (f g : Form) (y : List ℤ) :
    dot (addForm f g) y = dot f y + dot g y := by
  induction f generalizing g y with
  | nil => simp [addForm]
  | cons a as ih =>
      cases g with
      | nil => simp [addForm]
      | cons b bs =>
          cases y with
          | nil => simp
          | cons c cs =>
              simp only [addForm, dot, ih]
              ring

theorem dot_smulForm (k : ℤ) (f : Form) (y : List ℤ) :
    dot (smulForm k f) y = k * dot f y := by
  induction f generalizing y with
  | nil => simp [smulForm]
  | cons a as ih =>
      cases y with
      | nil => simp
      | cons c cs =>
          have h := ih cs
          simp only [smulForm, List.map_cons, dot] at h ⊢
          rw [h]
          ring

theorem eval_addForm (f g : Form) (x : List ℤ) :
    eval (addForm f g) x = eval f x + eval g x := dot_addForm f g _

theorem eval_smulForm (k : ℤ) (f : Form) (x : List ℤ) :
    eval (smulForm k f) x = k * eval f x := dot_smulForm k f _

theorem eval_subForm (f g : Form) (x : List ℤ) :
    eval (subForm f g) x = eval f x - eval g x := by
  simp only [subForm, eval_addForm, eval_smulForm]
  ring

/-- A form all of whose coefficients vanish evaluates to `0`. -/
theorem dot_eq_zero_of_all_zero {l : List ℤ} (h : ∀ a ∈ l, a = 0)
    (y : List ℤ) : dot l y = 0 := by
  induction l generalizing y with
  | nil => simp
  | cons a as ih =>
      cases y with
      | nil => simp
      | cons c cs =>
          have ha : a = 0 := h a (by simp)
          have has : ∀ b ∈ as, b = 0 := fun b hb => h b (by simp [hb])
          simp [dot, ha, ih has]

/-- Syntactic equality of forms, up to padding: their difference is zero in
every coordinate. -/
def formEq (f g : Form) : Bool := (subForm f g).all (fun a => a == 0)

theorem eval_eq_of_formEq {f g : Form} (h : formEq f g = true) (x : List ℤ) :
    eval f x = eval g x := by
  have hz : ∀ a ∈ subForm f g, a = 0 := by
    intro a ha
    have := List.all_eq_true.mp h a ha
    simpa using this
  have : eval (subForm f g) x = 0 := dot_eq_zero_of_all_zero hz _
  rw [eval_subForm] at this
  omega

/-! ## Contexts -/

/-- A context: forms asserted `≥ 0` and forms asserted `= 0`. -/
structure Context where
  /-- Forms asserted nonnegative. -/
  ge : List Form
  /-- Forms asserted zero. -/
  eq : List Form

/-- The point `x` satisfies the context. -/
def Context.Holds (Γ : Context) (x : List ℤ) : Prop :=
  (∀ g ∈ Γ.ge, 0 ≤ eval g x) ∧ (∀ g ∈ Γ.eq, eval g x = 0)

/-! ## Entailment certificates

A certificate for `Γ ⊢ g ≥ 0` is `(k; λ; μ; c)` with `k ≥ 1`, `λ` sparse
nonnegative weights into `Γ.ge`, `μ` sparse weights into `Γ.eq`, `c ≥ 0`, and

    k · g  =  Σ λᵢ Γ.geᵢ  +  Σ μⱼ Γ.eqⱼ  +  c

as an identity of forms.  Nothing searches for `λ`; the generator supplies it.
-/

/-- A sparse combination of context rows. -/
def combineRows (rows : List Form) (w : List (ℕ × ℤ)) : Form :=
  w.foldr (fun p acc => addForm (smulForm p.2 (rows.getD p.1 [])) acc) []

/-- An entailment certificate. -/
structure Cert where
  /-- The positive scaling `k`. -/
  k : ℤ
  /-- Sparse nonnegative weights on the inequality rows. -/
  lam : List (ℕ × ℤ)
  /-- Sparse weights on the equality rows. -/
  mu : List (ℕ × ℤ)
  /-- The nonnegative slack constant. -/
  c : ℤ

/-- The form the certificate claims equals `k · g`. -/
def Cert.combination (w : Cert) (Γ : Context) : Form :=
  addForm [w.c] (addForm (combineRows Γ.ge w.lam) (combineRows Γ.eq w.mu))

/-- The checker of spec §4.1.  One pass over the sparse lists and one vector
comparison; **no rounding**, deliberately (§13.4). -/
def Cert.check (w : Cert) (Γ : Context) (g : Form) : Bool :=
  decide (1 ≤ w.k) && decide (0 ≤ w.c) &&
    w.lam.all (fun p => decide (0 ≤ p.2)) &&
    formEq (smulForm w.k g) (w.combination Γ)

/-- A `getD` into a list of nonnegative-valued forms is nonnegative-valued:
out of range it is `[]`, which evaluates to `0`. -/
theorem eval_getD_nonneg {rows : List Form} {x : List ℤ}
    (hrows : ∀ g ∈ rows, 0 ≤ eval g x) (i : ℕ) :
    0 ≤ eval (rows.getD i []) x := by
  induction rows generalizing i with
  | nil => simp
  | cons r rs ih =>
      cases i with
      | zero => exact hrows r (by simp)
      | succ j => exact ih (fun g hg => hrows g (by simp [hg])) j

/-- The same for a list of zero-valued forms. -/
theorem eval_getD_eq_zero {rows : List Form} {x : List ℤ}
    (hrows : ∀ g ∈ rows, eval g x = 0) (i : ℕ) :
    eval (rows.getD i []) x = 0 := by
  induction rows generalizing i with
  | nil => simp
  | cons r rs ih =>
      cases i with
      | zero => exact hrows r (by simp)
      | succ j => exact ih (fun g hg => hrows g (by simp [hg])) j

theorem combineRows_nonneg {rows : List Form} {w : List (ℕ × ℤ)} {x : List ℤ}
    (hrows : ∀ g ∈ rows, 0 ≤ eval g x)
    (hw : ∀ p ∈ w, 0 ≤ p.2) :
    0 ≤ eval (combineRows rows w) x := by
  induction w with
  | nil => simp [combineRows]
  | cons p ps ih =>
      have hp : 0 ≤ p.2 := hw p (by simp)
      have hps : ∀ q ∈ ps, 0 ≤ q.2 := fun q hq => hw q (by simp [hq])
      have hrow : 0 ≤ eval (rows.getD p.1 []) x := eval_getD_nonneg hrows p.1
      simp only [combineRows, List.foldr_cons, eval_addForm, eval_smulForm]
      have := ih hps
      simp only [combineRows] at this
      nlinarith

theorem combineRows_eq_zero {rows : List Form} {w : List (ℕ × ℤ)} {x : List ℤ}
    (hrows : ∀ g ∈ rows, eval g x = 0) :
    eval (combineRows rows w) x = 0 := by
  induction w with
  | nil => simp [combineRows]
  | cons p ps ih =>
      have hrow : eval (rows.getD p.1 []) x = 0 := eval_getD_eq_zero hrows p.1
      simp only [combineRows, List.foldr_cons, eval_addForm, eval_smulForm]
      simp only [combineRows] at ih
      rw [hrow, ih]
      ring

/-- **Soundness of the entailment layer.**

If the checker accepts, the form really is nonnegative everywhere on the
context.  This is the only thing the rest of the lowering may assume about
certificates. -/
theorem Cert.check_sound {w : Cert} {Γ : Context} {g : Form}
    (h : w.check Γ g = true) {x : List ℤ} (hx : Γ.Holds x) :
    0 ≤ eval g x := by
  simp only [Cert.check, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨hk, hc⟩, hlam⟩, heq⟩ := h
  have hlam' : ∀ p ∈ w.lam, 0 ≤ p.2 := by
    intro p hp
    simpa using hlam p hp
  -- The claimed identity of forms, evaluated at `x`.
  have hval : w.k * eval g x = eval (w.combination Γ) x := by
    rw [← eval_smulForm]
    exact eval_eq_of_formEq heq x
  -- The right-hand side is a sum of nonnegative pieces.
  have hge : 0 ≤ eval (combineRows Γ.ge w.lam) x :=
    combineRows_nonneg hx.1 hlam'
  have heqz : eval (combineRows Γ.eq w.mu) x = 0 := combineRows_eq_zero hx.2
  have hrhs : 0 ≤ eval (w.combination Γ) x := by
    simp only [Cert.combination, eval_addForm, heqz]
    have : eval [w.c] x = w.c := by simp [eval, dot]
    omega
  -- `k ≥ 1` and `k · g ≥ 0` give `g ≥ 0`.
  nlinarith [hval, hrhs, hk]

end Utilities.Subdivision.ClosedRowProof
