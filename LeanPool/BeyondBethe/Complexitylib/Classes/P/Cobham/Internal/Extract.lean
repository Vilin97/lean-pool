/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Blocks
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Algebra

/-!
# Reading a string out of an encoded tape — proof internals

The completeness direction ends by reading the simulated machine's output off
its encoded output tape. Once the output head has been driven back to cell `0`
(see `Complexitylib.Classes.P.Cobham.Internal.StepAlgebra`), that tape's right
half-block is the whole tape in order, two bits per cell: the first bit of a
cell says whether it holds data, the second is the data bit.

So the output is recovered by two short recursions on notation, both collected
here:

* `Complexity.cellBits` — every second bit of a string, from a fixed offset;
  used twice, once for the "is data" bits and once for the data bits;
* `Complexity.runTrue` — the leading run of `true`s, as a ruler; its length is
  where the first blank cell is, hence the output's length.

## Main results

- `Complexity.Cobham.cellBitsFn`, `Complexity.Cobham.runTrueFn` — both are in
  the algebra
- `Complexity.runTrue_length` — the run's length is where the first `false` is,
  clamped by the ruler
-/


@[expose] public section

namespace Complexity

/-! ## Reading a single bit -/

/-- The bit of `z` at position `p`, `false` past the end. -/
def bitOf (z : List Bool) (p : ℕ) : Bool := (z.drop p).headD false

/-- Within range, `bitOf` is the indexed bit. -/
theorem bitOf_eq_getElem {z : List Bool} {p : ℕ} (h : p < z.length) :
    bitOf z p = z[p] := by
  rw [bitOf, List.drop_eq_getElem_cons h, List.headD_cons]

/-- Past the end there is no bit. -/
theorem bitOf_of_le {z : List Bool} {p : ℕ} (h : z.length ≤ p) :
    bitOf z p = false := by
  rw [bitOf, List.drop_eq_nil_of_le h, List.headD_nil]

/-- Reading inside the first part of a concatenation. -/
theorem bitOf_append_left {a : List Bool} {p : ℕ} (h : p < a.length) (b : List Bool) :
    bitOf (a ++ b) p = bitOf a p := by
  rw [bitOf, bitOf, List.drop_append_of_le_length h.le, List.drop_eq_getElem_cons h]
  rw [List.cons_append, List.headD_cons, List.headD_cons]

/-- Reading past the first part of a concatenation. -/
theorem bitOf_append_right {a : List Bool} {p : ℕ} (h : a.length ≤ p) (b : List Bool) :
    bitOf (a ++ b) p = bitOf b (p - a.length) := by
  rw [bitOf, bitOf, List.drop_append, List.drop_eq_nil_of_le h, List.nil_append]

/-- `Cobham.bitAt` reads exactly one bit, and it is `bitOf`. -/
theorem bitAt_eq (r z : List Bool) : bitAt r z = [bitOf z r.length] := by
  rw [bitAt, bitOf]
  cases h : z.drop r.length with
  | nil => rw [caseBit₀_nil, List.headD_nil]
  | cons b l => cases b <;> rw [caseBit₀_cons] <;> rfl

/-! ## Every second bit

`cellBits o z m` lists the bits of `z` at positions `o, o + 2, …, o + 2(m-1)`.
With `z` a run of two-bit symbol codes, offset `o` picks out one bit of each
symbol — which is how both halves of a coded cell are read. -/

/-- The bits of `z` at positions `2i + o` for `i < m`. -/
def cellBits (o : ℕ) (z : List Bool) : ℕ → List Bool
  | 0 => []
  | m + 1 => cellBits o z m ++ [bitOf z (2 * m + o)]

@[simp] theorem cellBits_length (o : ℕ) (z : List Bool) (m : ℕ) :
    (cellBits o z m).length = m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [cellBits, List.length_append, ih]; rfl

theorem cellBits_getElem? (o : ℕ) (z : List Bool) :
    ∀ (m i : ℕ), i < m → (cellBits o z m)[i]? = some (bitOf z (2 * i + o)) := by
  intro m
  induction m with
  | zero => intro i h; omega
  | succ m ih =>
      intro i h
      rw [cellBits]
      rcases Nat.lt_or_ge i m with hi | hi
      · rw [List.getElem?_append_left (by simpa using hi)]
        exact ih i hi
      · have him : i = m := by omega
        subst him
        rw [List.getElem?_append_right (by simp)]
        simp

/-! ## The leading run of `true`s

The output tape's "is data" bits are `true` on the output and `false` at the
first blank past it, so the output's length is the length of the leading run of
`true`s. The recursion below computes it as a ruler, clamped at the width it is
run to: the guard `m ≤ |previous|` is what stops the run at the first `false`
rather than restarting after it. -/

/-- The leading run of `true`s of `z`, clamped to `m` bits, as a ruler. -/
def runTrue (z : List Bool) : ℕ → List Bool
  | 0 => []
  | m + 1 =>
      runTrue z m ++ (if m ≤ (runTrue z m).length ∧ bitOf z m = true then [true] else [])

theorem runTrue_length_le (z : List Bool) (m : ℕ) : (runTrue z m).length ≤ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [runTrue, List.length_append]
      split <;> simp <;> omega

/-- **The run's length is where the first `false` is.** The guard in `runTrue`
stops the run at the first `false` rather than restarting after it, so the run's
length is the position of the first `false`, clamped by the width. -/
theorem runTrue_length {z : List Bool} {n : ℕ} (htrue : ∀ i < n, bitOf z i = true)
    (hfalse : bitOf z n = false) (m : ℕ) :
    (runTrue z m).length = min m n := by
  induction m with
  | zero => simp [runTrue]
  | succ m ih =>
      rw [runTrue, List.length_append, ih]
      rcases Nat.lt_or_ge m n with hm | hm
      · rw [if_pos ⟨by omega, htrue m hm⟩]
        simp only [List.length_cons, List.length_nil]
        omega
      · rw [if_neg ?_]
        · simp only [List.length_nil]
          omega
        · rintro ⟨h1, h2⟩
          have hme : m = n := by omega
          rw [hme, hfalse] at h2
          exact Bool.noConfusion h2

/-! ## Both recursions are in the algebra -/

namespace Cobham

/-- The step of `cellBits`: append the bit of the string at twice the remaining
ruler's length, plus the offset. -/
private def cellStep (o : ℕ) (w : Fin 3 → List Bool) : List Bool :=
  w 1 ++ bitAt (w 0 ++ w 0 ++ List.replicate o false) (w 2)

private theorem cellStep_cons (o : ℕ) (x p : List Bool) (v : Fin 1 → List Bool) :
    cellStep o (Fin.cons x (Fin.cons p v))
      = p ++ bitAt (x ++ x ++ List.replicate o false) (v 0) := rfl

/-- The step of `runTrue`: extend the run by one only when it has kept pace with
the ruler so far and the next bit is `true`. -/
private def runStep (w : Fin 3 → List Bool) : List Bool :=
  w 1 ++ caseBit₀
    (andBit (notBit (nonemptyFlag ((w 0).drop (w 1).length))) (bitAt (w 0) (w 2)))
    [true] []

private theorem runStep_cons (x p : List Bool) (v : Fin 1 → List Bool) :
    runStep (Fin.cons x (Fin.cons p v))
      = p ++ caseBit₀
          (andBit (notBit (nonemptyFlag (x.drop p.length))) (bitAt x (v 0))) [true] [] :=
  rfl

/-- **Every second bit is in the algebra.** One limited recursion on notation:
each peeled bit of the ruler appends one more bit of `z`, read at twice the
remaining ruler's length plus the offset. -/
theorem cellBitsFn {n : ℕ} (o : ℕ) {gr gz : (Fin n → List Bool) → List Bool}
    (hr : Cobham gr) (hz : Cobham gz) :
    Cobham fun v : Fin n → List Bool => cellBits o (gz v) (gr v).length := by
  have hrec : ∀ (x : List Bool) (v : Fin 1 → List Bool),
      recNotation (fun _ : Fin 1 → List Bool => ([] : List Bool)) (cellStep o)
          (cellStep o) x v = cellBits o (v 0) x.length := by
    intro x v
    induction x with
    | nil => rfl
    | cons b x ih =>
        have hlen : (x ++ x ++ List.replicate o false).length = 2 * x.length + o := by
          simp; omega
        cases b <;>
          · rw [recNotation_cons]
            simp only [cond_true, cond_false]
            rw [cellStep_cons, ih, bitAt_eq, hlen, List.length_cons, cellBits]
  have hh : Cobham (cellStep o) :=
    (appendFn (Cobham.proj 1)
      (comp₂ bitAtFn
        (appendFn (appendFn (Cobham.proj 0) (Cobham.proj 0))
          (Cobham.const (List.replicate o false)))
        (Cobham.proj 2))).of_eq fun _ => rfl
  have hbase : Cobham fun v : Fin 2 → List Bool => cellBits o (v 1) (v 0).length := by
    refine (Cobham.boundedRec Cobham.empty hh hh (Cobham.proj 0) ?_).of_eq fun v => ?_
    · intro x v
      rw [hrec, cellBits_length, Fin.cons_zero]
    · rw [hrec]; rfl
  exact (comp₂ hbase hr hz).of_eq fun _ => rfl

/-- **The leading run of `true`s is in the algebra.** One limited recursion on
notation: the run grows by one only while it has kept pace with the ruler, which
is the length comparison `nonemptyFn`/`notFn` performs. -/
theorem runTrueFn {n : ℕ} {gr gz : (Fin n → List Bool) → List Bool}
    (hr : Cobham gr) (hz : Cobham gz) :
    Cobham fun v : Fin n → List Bool => runTrue (gz v) (gr v).length := by
  have hrec : ∀ (x : List Bool) (v : Fin 1 → List Bool),
      recNotation (fun _ : Fin 1 → List Bool => ([] : List Bool)) runStep runStep x v
        = runTrue (v 0) x.length := by
    intro x v
    induction x with
    | nil => rfl
    | cons b x ih =>
        cases b <;>
          · rw [recNotation_cons]
            simp only [cond_true, cond_false]
            rw [runStep_cons, ih, bitAt_eq, List.length_cons, runTrue]
            congr 1
            rcases Nat.lt_or_ge (runTrue (v 0) x.length).length x.length with hlt | hge
            · rw [if_neg (by omega)]
              cases hd : x.drop (runTrue (v 0) x.length).length with
              | nil => rw [List.drop_eq_nil_iff] at hd; omega
              | cons c l => cases c <;> rfl
            · rw [List.drop_eq_nil_of_le hge]
              cases hb : bitOf (v 0) x.length
              · rw [if_neg (by simp)]; rfl
              · rw [if_pos ⟨hge, rfl⟩]; rfl
  have hh : Cobham runStep :=
    (appendFn (Cobham.proj 1)
      (iteFn
        (andFn (notFn (nonemptyFn (dropFn (Cobham.proj 1) (Cobham.proj 0))))
          (comp₂ bitAtFn (Cobham.proj 0) (Cobham.proj 2)))
        (Cobham.const [true]) Cobham.empty)).of_eq fun _ => rfl
  have hbase : Cobham fun v : Fin 2 → List Bool => runTrue (v 1) (v 0).length := by
    refine (Cobham.boundedRec Cobham.empty hh hh (Cobham.proj 0) ?_).of_eq fun v => ?_
    · intro x v
      rw [hrec, Fin.cons_zero]
      exact runTrue_length_le _ _
    · rw [hrec]; rfl
  exact (comp₂ hbase hr hz).of_eq fun _ => rfl

end Cobham

end Complexity
