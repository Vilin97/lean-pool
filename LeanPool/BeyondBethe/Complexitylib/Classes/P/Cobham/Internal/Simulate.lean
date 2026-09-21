/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Extract
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.StepAlgebra
import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.OutputBounds

/-!
# Running a machine inside the algebra — proof internals

Everything the completeness direction needs about a *run*, as opposed to a single
step: a total step function that stands still once the machine has halted, the
standing invariants of a run (the left-end marker where it belongs, every head
inside the encoded window), and the iterated versions of `Cobham.stepFn` and
`Cobham.rewindFn`.

## Main results

- `Complexity.TM.runCfg` — the configuration after `n` steps, halting-idempotent
- `Complexity.Cobham.iterate_stepFn` — the encoded iteration tracks it
- `Complexity.Cobham.iterate_rewindFn` — the rewind iteration drives the head to
  cell `0`
-/


@[expose] public section

namespace Complexity

namespace TM

variable {k : ℕ}

/-! ## A total run -/

/-- The configuration after `n` steps, standing still once halted. -/
def runCfg (tm : TM k) (c : Cfg k tm.Q) : ℕ → Cfg k tm.Q
  | 0 => c
  | n + 1 => (tm.step (runCfg tm c n)).getD (runCfg tm c n)

@[simp] theorem runCfg_zero (tm : TM k) (c : Cfg k tm.Q) : runCfg tm c 0 = c := rfl

theorem runCfg_succ (tm : TM k) (c : Cfg k tm.Q) (n : ℕ) :
    runCfg tm c (n + 1) = (tm.step (runCfg tm c n)).getD (runCfg tm c n) := rfl

theorem runCfg_add (tm : TM k) (c : Cfg k tm.Q) (a b : ℕ) :
    runCfg tm c (a + b) = runCfg tm (runCfg tm c a) b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [show a + (b + 1) = (a + b) + 1 from by omega, runCfg_succ, ih,
      runCfg_succ]

/-- Once halted, the run stands still. -/
theorem runCfg_of_halted (tm : TM k) {c : Cfg k tm.Q} (h : c.state = tm.qhalt) (n : ℕ) :
    runCfg tm c n = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [runCfg_succ, ih, TM.step, if_pos h, Option.getD_none]

/-- A run of exactly `t` steps is the `t`-th iterate. -/
theorem runCfg_of_reachesIn (tm : TM k) {c c' : Cfg k tm.Q} {t : ℕ}
    (h : tm.reachesIn t c c') : runCfg tm c t = c' := by
  induction h with
  | zero => rfl
  | @step c c'' t c' hstep _ ih =>
      rw [show t + 1 = 1 + t from by omega, runCfg_add, runCfg_succ, runCfg_zero, hstep,
        Option.getD_some, ih]

/-! ## The standing invariants of a run -/

/-- One step preserves the left-end marker's position on every tape. -/
theorem step_startInvariant (tm : TM k) {c c' : Cfg k tm.Q} (h : tm.step c = some c')
    (hin : c.input.StartInvariant) (hwork : ∀ i, (c.work i).StartInvariant)
    (hout : c.output.StartInvariant) :
    c'.input.StartInvariant ∧ (∀ i, (c'.work i).StartInvariant) ∧
      c'.output.StartInvariant := by
  rw [TM.step, if_neg (TM.state_ne_qhalt_of_step h)] at h
  injection h with h
  subst h
  exact ⟨hin.move _, fun i => (hwork i).writeAndMove _ _, hout.writeAndMove _ _⟩

/-- One step moves every head by at most one cell. -/
theorem step_head_le (tm : TM k) {c c' : Cfg k tm.Q} (h : tm.step c = some c') :
    c'.input.head ≤ c.input.head + 1 ∧ (∀ i, (c'.work i).head ≤ (c.work i).head + 1) ∧
      c'.output.head ≤ c.output.head + 1 := by
  rw [TM.step, if_neg (TM.state_ne_qhalt_of_step h)] at h
  injection h with h
  subst h
  exact ⟨Tape.head_move_le _ _, fun i => Tape.head_writeAndMove_le _ _ _,
    Tape.head_writeAndMove_le _ _ _⟩

/-- **Every tape of a run keeps its left-end marker.** -/
theorem runCfg_startInvariant (tm : TM k) (x : List Bool) (n : ℕ) :
    (runCfg tm (tm.initCfg x) n).input.StartInvariant ∧
      (∀ i, ((runCfg tm (tm.initCfg x) n).work i).StartInvariant) ∧
      (runCfg tm (tm.initCfg x) n).output.StartInvariant := by
  induction n with
  | zero =>
      exact ⟨Tape.StartInvariant.init_ofBool x, fun _ => Tape.StartInvariant.init_nil,
        Tape.StartInvariant.init_nil⟩
  | succ n ih =>
      rw [runCfg_succ]
      cases hs : tm.step (runCfg tm (tm.initCfg x) n) with
      | none => rw [Option.getD_none]; exact ih
      | some c' =>
          rw [Option.getD_some]
          exact step_startInvariant tm hs ih.1 ih.2.1 ih.2.2

/-- **After `n` steps every head is within `n` cells of the start.** -/
theorem runCfg_head_le (tm : TM k) (x : List Bool) (n : ℕ) :
    (runCfg tm (tm.initCfg x) n).input.head ≤ n ∧
      (∀ i, ((runCfg tm (tm.initCfg x) n).work i).head ≤ n) ∧
      (runCfg tm (tm.initCfg x) n).output.head ≤ n := by
  induction n with
  | zero => exact ⟨by simp, fun _ => by simp, by simp⟩
  | succ n ih =>
      rw [runCfg_succ]
      cases hs : tm.step (runCfg tm (tm.initCfg x) n) with
      | none => rw [Option.getD_none]; exact ⟨by omega, fun i => by have := ih.2.1 i; omega,
          by omega⟩
      | some c' =>
          rw [Option.getD_some]
          obtain ⟨h1, h2, h3⟩ := step_head_le tm hs
          exact ⟨by omega, fun i => by have := h2 i; have := ih.2.1 i; omega, by omega⟩

end TM

namespace Cobham

variable {k : ℕ}

/-- The invariants of a run, in the form the encoding lemmas want. -/
theorem cfgTapes_runCfg_inv (tm : TM k) (x : List Bool) (n W : ℕ) (hn : n ≤ W) :
    (∀ t ∈ cfgTapes (TM.runCfg tm (tm.initCfg x) n), t.StartInvariant) ∧
      (∀ t ∈ cfgTapes (TM.runCfg tm (tm.initCfg x) n), t.head ≤ W) := by
  obtain ⟨i1, w1, o1⟩ := TM.runCfg_startInvariant tm x n
  obtain ⟨i2, w2, o2⟩ := TM.runCfg_head_le tm x n
  constructor <;> intro t ht <;>
    · rw [cfgTapes, List.mem_cons, List.mem_cons, List.mem_ofFn] at ht
      rcases ht with rfl | rfl | ⟨i, rfl⟩
      · first | exact i1 | omega
      · first | exact o1 | omega
      · first | exact w1 i | (have := w2 i; omega)

/-- **The encoded iteration tracks the run.** -/
theorem iterate_stepFn (tm : TM k) (W : ℕ) (x : List Bool)
    (hq : Fintype.card tm.Q ≤ blockWidth W) :
    ∀ n : ℕ, n ≤ W →
      (stepFn tm (blockRuler W))^[n] (cfgCode W (tm.initCfg x))
        = cfgCode W (TM.runCfg tm (tm.initCfg x) n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      obtain ⟨hinv, hW⟩ := cfgTapes_runCfg_inv tm x n W (by omega)
      rw [Function.iterate_succ_apply', ih (by omega), TM.runCfg_succ]
      cases hs : tm.step (TM.runCfg tm (tm.initCfg x) n) with
      | none =>
          rw [Option.getD_none]
          exact stepFn_halted tm (TM.step_eq_none_iff_halted.mp hs) hq hW
      | some c' =>
          rw [Option.getD_some]
          have hgood := stepActs_forall₂ tm _ hinv hW
          refine stepFn_eq tm hs hq hW ?_ ?_ hgood
          · exact hinv _ (by simp [cfgTapes])
          · intro i
            exact hinv _ (by
              rw [cfgTapes]
              exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_ofFn.mpr ⟨i, rfl⟩)))

/-! ## The rewind iteration -/

private theorem head_move_left (s : Tape) : (s.move Dir3.left).head = s.head - 1 := rfl

/-- Iterated left moves. -/
private theorem head_moveLeft (t : Tape) (n : ℕ) :
    ((fun s : Tape => s.move Dir3.left)^[n] t).head = t.head - n ∧
      ((fun s : Tape => s.move Dir3.left)^[n] t).cells = t.cells := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨?_, ?_⟩
      · rw [head_move_left, ih.1]
        omega
      · rw [Tape.move_cells, ih.2]

private theorem startInvariant_moveLeft (t : Tape) (h : t.StartInvariant) (n : ℕ) :
    ((fun s : Tape => s.move Dir3.left)^[n] t).StartInvariant := by
  induction n with
  | zero => exact h
  | succ n ih => rw [Function.iterate_succ_apply']; exact ih.move _

/-- **The rewind iteration walks the head left.** -/
theorem iterate_rewindFn {W : ℕ} (t : Tape) (hinv : t.StartInvariant) (hW : t.head ≤ W) :
    ∀ n : ℕ, (rewindFn (blockRuler W))^[n] (pairCode W t)
      = pairCode W ((fun s : Tape => s.move Dir3.left)^[n] t) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact rewindFn_eq _ (startInvariant_moveLeft t hinv n)
        (by have := (head_moveLeft t n).1; omega)

/-- **After enough rewinding the head is at cell `0`.** -/
theorem rewound (t : Tape) {n : ℕ} (h : t.head ≤ n) :
    (fun s : Tape => s.move Dir3.left)^[n] t
      = { head := 0, cells := t.cells } := by
  obtain ⟨h1, h2⟩ := head_moveLeft t n
  refine Tape.ext ?_ h2
  show ((fun s : Tape => s.move Dir3.left)^[n] t).head = 0
  rw [h1]
  omega

/-! ## Reading the output off the rewound tape

With the head at cell `0` the tape's right half-block is the whole window, in
order and two bits per cell. The first bit of each cell says whether it holds
data — `symCode` is arranged so that only `0` and `1` have it set — and the
second is the bit itself. So the output is the second bits, truncated where the
first bits stop: `Complexity.cellBits` twice and one `Complexity.runTrue`. -/

@[simp] theorem cellsCode_one (t : Tape) (i : ℕ) :
    cellsCode t i 1 = symCode (t.cells i) := by
  rw [cellsCode_succ_left, cellsCode_zero, List.append_nil]

/-- Reading one bit of an aligned window is reading one bit of a cell's code. -/
theorem bitOf_cellsCode (t : Tape) {w j : ℕ} (hj : j < w) {o : ℕ} (ho : o < 2) :
    bitOf (cellsCode t 0 w) (2 * j + o) = bitOf (symCode (t.cells j)) o := by
  have hsplit : cellsCode t 0 w
      = cellsCode t 0 j ++ (cellsCode t j 1 ++ cellsCode t (j + 1) (w - j - 1)) := by
    conv_lhs => rw [show w = j + (1 + (w - j - 1)) from by omega]
    rw [cellsCode_add t 0 j, cellsCode_add t (0 + j) 1 (w - j - 1)]
    simp only [Nat.zero_add]
  have hlen1 : (cellsCode t 0 j).length = 2 * j := cellsCode_length _ _ _
  have hlen2 : (cellsCode t j 1).length = 2 := by rw [cellsCode_one, symCode_length]
  rw [hsplit, bitOf_append_right (by omega), hlen1,
    show 2 * j + o - 2 * j = o from by omega, bitOf_append_left (by omega),
    cellsCode_one]

/-- A padded block of exactly the ruler's width is the block itself. -/
private theorem padTo_of_length_eq {r x : List Bool} (h : x.length = r.length) :
    padTo r x = x := by
  rw [padTo_eq_append r x h.le, h, Nat.sub_self, List.replicate_zero, List.append_nil]

/-- The aligned window of a rewound tape is its right half-block. -/
theorem drop_pairCode_rewound (W : ℕ) (t : Tape) :
    (pairCode W { head := 0, cells := t.cells }).drop (blockRuler W).length
      = cellsCode t 0 (W + 1) := by
  rw [drop_pairCode, rightCode]
  refine padTo_of_length_eq ?_
  rw [cellsCode_length, blockRuler_length, blockWidth]
  rfl

/-- **Reading the output off an aligned window.** -/
theorem output_of_cellsCode {W : ℕ} (t : Tape) (y : List Bool)
    (hy : t.HasOutput y) (hyW : y.length + 1 ≤ W) :
    (cellBits 3 (cellsCode t 0 (W + 1)) W).take
        (runTrue (cellBits 2 (cellsCode t 0 (W + 1)) W) W).length = y := by
  set u := cellsCode t 0 (W + 1) with hu
  -- Each cell's two bits, read out of the window.
  have hcell : ∀ (i : ℕ), i < W → ∀ o < 2,
      bitOf u (2 * i + (2 + o)) = bitOf (symCode (t.cells (i + 1))) o := by
    intro i hi o ho
    rw [hu, show 2 * i + (2 + o) = 2 * (i + 1) + o from by omega,
      bitOf_cellsCode t (by omega) ho]
  have hflag : ∀ i < W, bitOf (cellBits 2 u W) i
      = bitOf (symCode (t.cells (i + 1))) 0 := by
    intro i hi
    rw [bitOf_eq_getElem (by rw [cellBits_length]; exact hi),
      ← Option.some_inj, ← List.getElem?_eq_getElem, cellBits_getElem? 2 u W i hi,
      Option.some_inj]
    exact hcell i hi 0 (by omega)
  have hbit : ∀ i < W, bitOf (cellBits 3 u W) i
      = bitOf (symCode (t.cells (i + 1))) 1 := by
    intro i hi
    rw [bitOf_eq_getElem (by rw [cellBits_length]; exact hi),
      ← Option.some_inj, ← List.getElem?_eq_getElem, cellBits_getElem? 3 u W i hi,
      Option.some_inj]
    have := hcell i hi 1 (by omega)
    rwa [show 2 * i + (2 + 1) = 2 * i + 3 from by omega] at this
  -- The data flags are `true` exactly on the output.
  have hlen : (runTrue (cellBits 2 u W) W).length = y.length := by
    have h1 : ∀ i < y.length, bitOf (cellBits 2 u W) i = true := by
      intro i hi
      rw [hflag i (by omega), hy.1 i hi]
      cases y[i] <;> rfl
    have h2 : bitOf (cellBits 2 u W) y.length = false := by
      rw [hflag y.length (by omega), hy.2]
      rfl
    rw [runTrue_length h1 h2 W]
    omega
  rw [hlen]
  refine List.ext_getElem (by rw [List.length_take, cellBits_length]; omega) ?_
  intro i h1 h2
  rw [List.getElem_take]
  have hiy : i < y.length := by
    rwa [List.length_take, cellBits_length, min_eq_left (by omega : y.length ≤ W)] at h1
  rw [← bitOf_eq_getElem (by rw [cellBits_length]; omega), hbit i (by omega),
    hy.1 i hiy]
  cases hb : y[i] <;> rfl

/-! ## The whole simulation

Everything above, wired together: a clock long enough to run the machine to a
halt and to rewind the output head, a first iteration that runs the machine, a
second that rewinds, and the extraction. -/

private theorem length_flatten_replicate (u : List Bool) :
    ∀ n : ℕ, (List.replicate n u).flatten.length = n * u.length := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]
      ring

theorem initFn_length (tm : TM k) (R x : List Bool) :
    (initFn tm R x).length = (2 * (k + 2) + 1) * R.length := by
  rw [initFn]
  simp only [List.length_append, padTo_length, length_flatten_replicate]
  ring

/-- **A polynomial bound with room for the clock's other duties**: the clock has
to outlast the machine, cover the input, and be wide enough for the state code. -/
private theorem exists_clock_bound (tm : TM k) {T : ℕ → ℕ} {S D : ℕ}
    (hSD : ∀ n, T n ≤ S * (n + 1) ^ D) :
    ∃ C E : ℕ, ∀ n : ℕ, T n + n + Fintype.card tm.Q + 2 ≤ C * (n + 1) ^ E := by
  refine ⟨S + Fintype.card tm.Q + 2, max D 1, fun n => ?_⟩
  have h1 : T n ≤ S * (n + 1) ^ max D 1 :=
    le_trans (hSD n)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (le_max_left _ _)))
  have h2 : n + 1 ≤ (n + 1) ^ max D 1 := Nat.le_self_pow (by omega) _
  have h3 : n + Fintype.card tm.Q + 2 ≤ (Fintype.card tm.Q + 2) * (n + 1) := by
    have : 1 * n ≤ (Fintype.card tm.Q + 2) * n := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.mul_add, Nat.mul_one]
    omega
  calc T n + n + Fintype.card tm.Q + 2
      ≤ S * (n + 1) ^ max D 1 + (Fintype.card tm.Q + 2) * (n + 1) := by omega
    _ ≤ S * (n + 1) ^ max D 1 + (Fintype.card tm.Q + 2) * (n + 1) ^ max D 1 :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _
    _ = (S + Fintype.card tm.Q + 2) * (n + 1) ^ max D 1 := by ring

/-! ### The three stages, as functions of the clock

The clock string `u` fixes the encoded window: the ruler is `2|u|` bits wide, so
the window is `W = |u| - 1` cells and `u.tail` is a ruler of exactly `W` bits. -/

/-- The block ruler belonging to a clock value. -/
def clockRuler (u : List Bool) : List Bool := List.replicate (u ++ u).length false

theorem clockRuler_eq {u : List Bool} (h : 1 ≤ u.length) :
    clockRuler u = blockRuler (u.length - 1) := by
  rw [clockRuler, blockRuler, blockWidth]
  congr 1
  rw [List.length_append]
  omega

theorem clockRulerFn {n : ℕ} {gu : (Fin n → List Bool) → List Bool} (hu : Cobham gu) :
    Cobham fun w : Fin n → List Bool => clockRuler (gu w) :=
  (zeroBlockFn (appendFn hu hu)).of_eq fun _ => rfl

/-- Stage one: the encoding after running the machine to a halt. -/
noncomputable def runFn (tm : TM k) (u x : List Bool) : List Bool :=
  (stepFn tm (clockRuler u))^[u.tail.length] (initFn tm (clockRuler u) x)

/-- Stage two: the output tape's two half-blocks, head rewound to cell `0`. -/
noncomputable def outPairFn (tm : TM k) (u x : List Bool) : List Bool :=
  (rewindFn (clockRuler u))^[u.length]
    (blockAt (clockRuler u) (runFn tm u x) 3 ++ blockAt (clockRuler u) (runFn tm u x) 4)

/-- Stage three: the string on the rewound output tape. -/
noncomputable def simFn (tm : TM k) (u x : List Bool) : List Bool :=
  (cellBits 3 ((outPairFn tm u x).drop (clockRuler u).length) u.tail.length).take
    (runTrue (cellBits 2 ((outPairFn tm u x).drop (clockRuler u).length) u.tail.length)
      u.tail.length).length

/-- The simulated run never leaves its blocks. -/
theorem iterate_stepFn_length_le (tm : TM k) (R x : List Bool) (n : ℕ) :
    ((stepFn tm R)^[n] (initFn tm R x)).length ≤ (2 * (k + 2) + 1) * R.length := by
  induction n with
  | zero => exact (initFn_length tm R x).le
  | succ n ih => rw [Function.iterate_succ_apply']; exact stepFn_length_le tm R _ ih

/-- The rewind never leaves its two blocks. -/
theorem iterate_rewindFn_length_le (R z : List Bool) (hz : z.length ≤ 2 * R.length)
    (n : ℕ) : ((rewindFn R)^[n] z).length ≤ 2 * R.length := by
  induction n with
  | zero => exact hz
  | succ n ih => rw [Function.iterate_succ_apply']; exact rewindFn_length_le R _ ih

private theorem tail_cons₂ (a b : List Bool) : Fin.tail ![a, b] = fun _ => b := by
  funext i
  rw [Subsingleton.elim i 0]
  rfl

private theorem cons_val_one (s : List Bool) (v : Fin 1 → List Bool) :
    (Fin.cons s v : Fin 2 → List Bool) 1 = v 0 := rfl

private theorem cons_val_zero' (s : List Bool) (v : Fin 1 → List Bool) :
    (Fin.cons s v : Fin 2 → List Bool) 0 = s := rfl

/-- **The whole simulation is in the algebra.** -/
theorem simFn_mem (tm : TM k) {gu : (Fin 1 → List Bool) → List Bool}
    (hu : Cobham gu) : Cobham fun v : Fin 1 → List Bool => simFn tm (gu v) (v 0) := by
  have hu2 : Cobham fun w : Fin 2 → List Bool => gu (fun _ => w 1) :=
    (Cobham.comp hu fun _ : Fin 1 => Cobham.proj 1).of_eq fun _ => rfl
  have hu1 : Cobham fun w : Fin 1 → List Bool => gu (fun _ => w 0) :=
    (Cobham.comp hu fun _ : Fin 1 => Cobham.proj 0).of_eq fun _ => rfl
  have huu : ∀ w : Fin 1 → List Bool, gu (fun _ => w 0) = gu w := fun w => by
    congr 1
    funext i
    rw [Subsingleton.elim i 0]
  -- Stage one.
  have hrun : Cobham fun v : Fin 1 → List Bool => runFn tm (gu v) (v 0) := by
    have hstage :=
      iterFn (e := fun w : Fin 1 → List Bool =>
          initFn tm (clockRuler (gu (fun _ => w 0))) (w 0))
        (f := fun w : Fin 2 → List Bool =>
          stepFn tm (clockRuler (gu (fun _ => w 1))) (w 0))
        (j := fun w : Fin 2 → List Bool =>
          (List.replicate (2 * (k + 2) + 1)
            (clockRuler (gu (fun _ => w 1)))).flatten)
        (initFn_mem tm (clockRulerFn hu1) (Cobham.proj 0))
        (stepFn_mem tm (clockRulerFn hu2) (Cobham.proj 0))
        (repeatFn (clockRulerFn hu2) _) ?_
    · refine (comp₂ hstage (tailFn hu1) (Cobham.proj 0)).of_eq fun v => ?_
      simp only [tail_cons₂, cons_val_one, cons_val_zero', Matrix.cons_val_zero]
      rw [runFn, huu]
    · intro c v
      have := iterate_stepFn_length_le tm (clockRuler (gu fun _ => v 0)) (v 0) c.length
      rw [length_flatten_replicate]
      exact this
  -- Stage two.
  have hpair : Cobham fun v : Fin 1 → List Bool => outPairFn tm (gu v) (v 0) := by
    have hstage :=
      iterFn (e := fun w : Fin 1 → List Bool =>
          blockAt (clockRuler (gu (fun _ => w 0))) (runFn tm (gu (fun _ => w 0)) (w 0)) 3
            ++ blockAt (clockRuler (gu (fun _ => w 0)))
                (runFn tm (gu (fun _ => w 0)) (w 0)) 4)
        (f := fun w : Fin 2 → List Bool =>
          rewindFn (clockRuler (gu (fun _ => w 1))) (w 0))
        (j := fun w : Fin 2 → List Bool =>
          clockRuler (gu (fun _ => w 1)) ++ clockRuler (gu (fun _ => w 1)))
        (appendFn (blockFn (clockRulerFn hu1) (hrun.of_eq fun v => by rw [huu]) 3)
          (blockFn (clockRulerFn hu1) (hrun.of_eq fun v => by rw [huu]) 4))
        (rewindFn_mem (clockRulerFn hu2) (Cobham.proj 0))
        (appendFn (clockRulerFn hu2) (clockRulerFn hu2)) ?_
    · refine (comp₂ hstage hu1 (Cobham.proj 0)).of_eq fun v => ?_
      simp only [tail_cons₂, cons_val_one, cons_val_zero', Matrix.cons_val_zero]
      rw [outPairFn, huu]
    · intro c v
      simp only [cons_val_one, cons_val_zero']
      have hb : ((rewindFn (clockRuler (gu fun _ => v 0)))^[c.length]
          (blockAt (clockRuler (gu fun _ => v 0)) (runFn tm (gu fun _ => v 0) (v 0)) 3 ++
            blockAt (clockRuler (gu fun _ => v 0))
              (runFn tm (gu fun _ => v 0) (v 0)) 4)).length
          ≤ 2 * (clockRuler (gu fun _ => v 0)).length := by
        refine iterate_rewindFn_length_le _ _ ?_ _
        rw [List.length_append, blockAt, blockAt, List.length_take, List.length_take]
        omega
      rw [List.length_append]
      exact le_trans hb (by omega)
  -- Stage three.
  have hdrop : Cobham fun v : Fin 1 → List Bool =>
      (outPairFn tm (gu v) (v 0)).drop (clockRuler (gu v)).length :=
    dropFn (clockRulerFn hu) hpair
  exact (takeFn (runTrueFn (tailFn hu) (cellBitsFn 2 (tailFn hu) hdrop))
    (cellBitsFn 3 (tailFn hu) hdrop)).of_eq fun v => by rw [simFn]

/-- **The simulation computes the machine's function.** Provided the clock
outlasts the run, covers the input and is wide enough for the state code, the
three stages reproduce exactly the string the machine leaves on its output
tape. -/
theorem simFn_eq (tm : TM k) {T : ℕ → ℕ} {f : List Bool → List Bool}
    (hcomp : tm.ComputesInTime f T) (u x : List Bool)
    (hlen : T x.length + x.length + Fintype.card tm.Q + 2 ≤ u.length) :
    simFn tm u x = f x := by
  have hu1 : 1 ≤ u.length := by omega
  have hR : clockRuler u = blockRuler (u.length - 1) := clockRuler_eq hu1
  have htail : u.tail.length = u.length - 1 := List.length_tail
  have hq : Fintype.card tm.Q ≤ blockWidth (u.length - 1) := by rw [blockWidth]; omega
  obtain ⟨c', t, ht, hreach, hhalt, hout⟩ := hcomp x
  have hylen : (f x).length ≤ t := TM.output_length_le_of_reachesIn hreach hout
  have hrunW : TM.runCfg tm (tm.initCfg x) (u.length - 1) = c' := by
    rw [show u.length - 1 = t + (u.length - 1 - t) from by omega, TM.runCfg_add,
      TM.runCfg_of_reachesIn tm hreach, TM.runCfg_of_halted tm hhalt]
  have hrun : runFn tm u x = cfgCode (u.length - 1) c' := by
    rw [runFn, hR, htail, initFn_eq tm _ x (by omega),
      iterate_stepFn tm _ x hq _ le_rfl, hrunW]
  obtain ⟨hinv, hWh⟩ := cfgTapes_runCfg_inv tm x (u.length - 1) (u.length - 1) le_rfl
  rw [hrunW] at hinv hWh
  have hmem : c'.output ∈ cfgTapes c' := by simp [cfgTapes]
  have hstart : c'.output.StartInvariant := hinv _ hmem
  have hhead : c'.output.head ≤ u.length - 1 := hWh _ hmem
  obtain ⟨hb3, hb4⟩ :=
    blockAt_cfgCode_tape (u.length - 1) c' 1 (by rw [cfgTapes_length]; omega)
  have hidx : (cfgTapes c')[1]'(by rw [cfgTapes_length]; omega) = c'.output := rfl
  rw [hidx, show 2 * 1 + 1 = 3 from rfl] at hb3
  rw [hidx, show 2 * 1 + 2 = 4 from rfl] at hb4
  have hpair : blockAt (clockRuler u) (runFn tm u x) 3
      ++ blockAt (clockRuler u) (runFn tm u x) 4 = pairCode (u.length - 1) c'.output := by
    rw [hrun, hR, hb3, hb4, pairCode]
  have hrew : outPairFn tm u x
      = pairCode (u.length - 1) { head := 0, cells := c'.output.cells } := by
    rw [outPairFn, hpair, hR, iterate_rewindFn c'.output hstart hhead u.length,
      rewound c'.output (by omega)]
  have hdropeq : (outPairFn tm u x).drop (clockRuler u).length
      = cellsCode c'.output 0 (u.length - 1 + 1) := by
    rw [hrew, hR, drop_pairCode_rewound]
  rw [simFn, htail, hdropeq]
  exact output_of_cellsCode c'.output (f x) hout (by omega)

/-- **The completeness direction, for one machine.** -/
theorem computes_mem_CobhamFP (tm : TM k) {T : ℕ → ℕ} {S D : ℕ}
    (hSD : ∀ n, T n ≤ S * (n + 1) ^ D) {f : List Bool → List Bool}
    (hcomp : tm.ComputesInTime f T) : CobhamFP f := by
  obtain ⟨C, E, hCE⟩ := exists_clock_bound tm hSD
  obtain ⟨clk, hclk, hclklen⟩ := exists_pow_clock C E
  have hclk1 : Cobham fun w : Fin 1 → List Bool => clk (fun _ => w 0) :=
    (Cobham.comp hclk fun _ : Fin 1 => Cobham.proj 0).of_eq fun _ => rfl
  refine ((simFn_mem tm hclk1).of_eq fun v => ?_ : Cobham fun v : Fin 1 → List Bool =>
    f (v 0))
  refine simFn_eq tm hcomp _ (v 0) (le_trans (hCE (v 0).length) ?_)
  exact hclklen (fun _ => v 0)

end Cobham

end Complexity
