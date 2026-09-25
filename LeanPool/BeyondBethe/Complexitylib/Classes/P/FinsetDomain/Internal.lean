/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import Mathlib.Data.Fintype.Sets
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Finset.Lattice.Fold
public import LeanPool.BeyondBethe.Complexitylib.Mathlib.FinsetPrefixes
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.NormalForm
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Tape.Encoding
public import LeanPool.BeyondBethe.Complexitylib.Models.TuringMachine.Combinators

/-!
# Finite-domain lookup machine (internal)

Construction and correctness of a deterministic Turing machine computing a
function of the form `fun s => if s ∈ S then g s else []`, where `S` is a finite
set of "inputs of interest" and `g` an arbitrary target function. Such a
function differs from the constant empty-output function on only finitely many
inputs, so it can be computed by a table lookup that runs in linear time.

The machine has no work tapes. It works in two phases:

* **Read phase.** It scans the read-only input tape left to right, tracking in
  its finite state the prefix read so far — as long as that prefix is still a
  prefix of some element of `S`; otherwise it enters a "dead" state. The output
  head bumps off the left marker on the first step and then idles at cell one.
* **Write phase.** On reaching the first input blank it knows exactly which
  element of `S` (if any) the input was, hence which fixed output string to
  produce. It writes that string onto the output tape, one symbol per step,
  landing on the halting configuration.

Since the read phase takes `|x|` steps and the write phase is bounded by the
longest possible output, the runtime is linear.

The public statement (`ite_mem_finset_mem_FP`) lives in
`Complexitylib.Classes.P.FinsetDomain`.
-/

@[expose] public section

namespace Complexity

namespace TM.FinsetDomain

variable (g : List Bool → List Bool) (S : Finset (List Bool))

/-! ## Output finset

The read phase tracks membership in `S.prefixes` and the write phase tracks
membership in `(outputsFinset g S).suffixes`; both finsets come from the
generic `Finset.prefixes`/`Finset.suffixes` API. -/

/-- The possible output strings: `g s` for `s ∈ S`, together with `[]`. -/
def outputsFinset (g : List Bool → List Bool) (S : Finset (List Bool)) :
    Finset (List Bool) :=
  insert [] (S.image g)

theorem nil_mem_suffixes_outputsFinset :
    ([] : List Bool) ∈ (outputsFinset g S).suffixes :=
  Finset.nil_mem_suffixes ⟨[], Finset.mem_insert_self _ _⟩

theorem output_mem_suffixes_outputsFinset {input : List Bool} :
    (if input ∈ S then g input else ([] : List Bool)) ∈ (outputsFinset g S).suffixes := by
  refine Finset.mem_suffixes_self ?_
  unfold outputsFinset
  split
  · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem g ‹_›)
  · exact Finset.mem_insert_self _ _

/-! ## The lookup machine -/

instance : Fintype {p : List Bool // p ∈ S.prefixes} := Finset.Subtype.fintype _
instance : Fintype {w : List Bool // w ∈ (outputsFinset g S).suffixes} :=
  Finset.Subtype.fintype _

/-- States of the lookup machine. -/
inductive LookupState (g : List Bool → List Bool) (S : Finset (List Bool)) : Type where
  /-- Read phase: the viable prefix consumed so far, carried together with the
  proof that it is a prefix of some element of `S`, so that the transition
  function can use the proof directly. -/
  | read (p : List Bool) (hp : p ∈ S.prefixes) : LookupState g S
  /-- Read phase, dead state: the input read so far has diverged from every
  element of `S`. -/
  | dead : LookupState g S
  /-- Write phase: the output suffix still to be written. -/
  | write (w : List Bool) (hw : w ∈ (outputsFinset g S).suffixes) : LookupState g S
  /-- The halt state. -/
  | halt : LookupState g S

/-- `LookupState` as a sum of two finite subtypes and two extra states. This
equivalence supplies the `DecidableEq` and `Fintype` instances, which cannot be
derived because the `read`/`write` constructors have dependent fields. -/
def lookupStateEquiv :
    LookupState g S ≃
      (Option {p : List Bool // p ∈ S.prefixes} ⊕
        Option {w : List Bool // w ∈ (outputsFinset g S).suffixes}) where
  toFun
    | .read p hp => .inl (some ⟨p, hp⟩)
    | .dead => .inl none
    | .write w hw => .inr (some ⟨w, hw⟩)
    | .halt => .inr none
  invFun
    | .inl (some ⟨p, hp⟩) => .read p hp
    | .inl none => .dead
    | .inr (some ⟨w, hw⟩) => .write w hw
    | .inr none => .halt
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with (_ | ⟨p, hp⟩) | (_ | ⟨w, hw⟩) <;> rfl

instance : DecidableEq (LookupState g S) := (lookupStateEquiv g S).decidableEq
instance : Fintype (LookupState g S) := Fintype.ofEquiv _ (lookupStateEquiv g S).symm

/-- The read-phase state after consuming prefix `p`: the viable prefix `p` if it
is still a prefix of some element of `S`, otherwise the dead state. -/
def readState (p : List Bool) : LookupState g S :=
  if h : p ∈ S.prefixes then .read p h else .dead

/-- The write-phase state carrying output suffix `c`. -/
def writeState (c : List Bool) (hc : c ∈ (outputsFinset g S).suffixes) : LookupState g S :=
  .write c hc

/-- The halt state. -/
def haltState : LookupState g S := .halt

theorem readState_ne_haltState (p : List Bool) : readState g S p ≠ haltState g S := by
  rw [readState, haltState]
  split <;> simp

/-- The lookup machine for `g` and `S`. See the module docstring for the
construction. It has no work tapes. -/
def lookupTM : TM 0 where
  Q := LookupState g S
  qstart := readState g S []
  qhalt := haltState g S
  δ := fun state iHead wHeads oHead =>
    match state with
    | .read p hp =>
      match iHead with
      | Γ.blank =>
        -- end of input: hand off to the write phase
        (writeState g S (if p ∈ S then g p else [])
           (output_mem_suffixes_outputsFinset g S),
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      | Γ.start =>
        -- skip the left-end marker: move input right, keep the state
        (.read p hp,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      | Γ.zero =>
        (readState g S (p ++ [false]),
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      | Γ.one =>
        (readState g S (p ++ [true]),
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .dead =>
      match iHead with
      | Γ.blank =>
        -- end of input: no element of `S` matched, write the empty output
        (writeState g S [] (nil_mem_suffixes_outputsFinset g S),
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
      | Γ.start =>
        (.dead,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      | Γ.zero =>
        (.dead,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
      | Γ.one =>
        (.dead,
         fun i => readBackWrite (wHeads i), readBackWrite oHead,
         Dir3.right, fun i => idleDir (wHeads i), idleDir oHead)
    | .write [] _ =>
      (haltState g S,
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
    | .write (a :: rest) hw =>
      (writeState g S rest (Finset.mem_suffixes_of_suffix (List.suffix_cons a rest) hw),
       fun i => readBackWrite (wHeads i), Γw.ofBool a,
       idleDir iHead, fun i => idleDir (wHeads i), Dir3.right)
    | .halt =>
      (haltState g S,
       fun i => readBackWrite (wHeads i), readBackWrite oHead,
       idleDir iHead, fun i => idleDir (wHeads i), idleDir oHead)
  δ_right_of_start := by
    intro state iHead wHeads oHead
    match state with
    | .read p hp =>
      match iHead with
      | Γ.blank =>
        exact ⟨fun h => absurd h (by decide), fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
      | Γ.start =>
        exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
      | Γ.zero =>
        exact ⟨fun h => absurd h (by decide), fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
      | Γ.one =>
        exact ⟨fun h => absurd h (by decide), fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
    | .dead =>
      match iHead with
      | Γ.blank =>
        exact ⟨fun h => absurd h (by decide), fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
      | Γ.start =>
        exact ⟨fun _ => rfl, fun _ => idleDir_right_of_start, idleDir_right_of_start⟩
      | Γ.zero =>
        exact ⟨fun h => absurd h (by decide), fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
      | Γ.one =>
        exact ⟨fun h => absurd h (by decide), fun _ => idleDir_right_of_start,
          idleDir_right_of_start⟩
    | .write [] _ =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩
    | .write (a :: rest) hw =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start, fun _ => rfl⟩
    | .halt =>
      exact ⟨idleDir_right_of_start, fun _ => idleDir_right_of_start,
        idleDir_right_of_start⟩

/-! ## Correctness -/

/-- Reading a Boolean symbol in the read phase advances the tracked prefix and
moves the input head right. -/
private theorem lookup_read_bit_step (p : List Bool) (b : Bool)
    (c : Cfg 0 (lookupTM g S).Q)
    (hstate : c.state = readState g S p)
    (hread : c.input.read = Γ.ofBool b) :
    (lookupTM g S).step c = some
      { state := readState g S (p ++ [b])
        input := c.input.move Dir3.right
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
          (idleDir (c.work i).read)
        output := c.output.writeAndMove (readBackWrite c.output.read)
          (idleDir c.output.read) } := by
  have hne : c.state ≠ (lookupTM g S).qhalt := by
    rw [hstate]; exact readState_ne_haltState g S p
  by_cases hp : p ∈ S.prefixes
  · cases b <;>
      simp [TM.step, lookupTM, hstate, hread, readState, haltState, dif_pos hp, Γ.ofBool]
  · have hp' : p ++ [b] ∉ S.prefixes := fun h =>
      hp (Finset.mem_prefixes_of_prefix (List.prefix_append p [b]) h)
    cases b <;>
      simp [TM.step, lookupTM, hstate, hread, readState, haltState, dite_eq_right hp,
        dite_eq_right hp',
        Γ.ofBool]

/-- Writing back the (blank) symbol under an idle output head keeps the output
tape an empty binary prefix. -/
private theorem hasBinaryPrefix_idle {t : Tape} {bits : List Bool}
    (h : t.HasBinaryPrefix bits) :
    (t.writeAndMove (readBackWrite t.read) (idleDir t.read)).HasBinaryPrefix bits := by
  have hread : t.read = Γ.blank := h.read_blank
  have hne : t.read ≠ Γ.start := by rw [hread]; decide
  rw [writeAndMove_readBack t hne]
  have hstay : idleDir t.read = Dir3.stay := by rw [hread]; rfl
  rw [hstay]
  exact h

/-- The read phase: from a config tracking prefix `x.take k` with the input head
at `k + 1`, the machine consumes the remaining input in `|x| - k` steps, reaching
the state that tracks the full input `x`. -/
private theorem lookup_read_loop (x : List Bool) :
    ∀ rem k (c : Cfg 0 (lookupTM g S).Q),
      rem = x.length - k →
      c.state = readState g S (x.take k) →
      c.input.cells = (Tape.init (x.map Γ.ofBool)).cells →
      c.input.head = k + 1 →
      c.output.HasBinaryPrefix [] →
      k ≤ x.length →
      ∃ c',
        (lookupTM g S).reachesIn rem c c' ∧
        c'.state = readState g S x ∧
        c'.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
        c'.input.head = x.length + 1 ∧
        c'.output.HasBinaryPrefix [] := by
  intro rem
  induction rem with
  | zero =>
    intro k c hrem hstate hcells hhead houtput hk
    have hk_eq : k = x.length := by omega
    subst hk_eq
    rw [List.take_length] at hstate
    exact ⟨c, .zero, hstate, hcells, hhead, houtput⟩
  | succ rem ih =>
    intro k c hrem hstate hcells hhead houtput hk
    have hk_lt : k < x.length := by omega
    have hread : c.input.read = Γ.ofBool (x[k]'hk_lt) := by
      simp [Tape.read, hhead, hcells, Tape.init_ofBool_cells_lt x k hk_lt]
    have hstep := lookup_read_bit_step g S (x.take k) (x[k]'hk_lt) c hstate hread
    set c1 : Cfg 0 (lookupTM g S).Q :=
      { state := readState g S (x.take k ++ [x[k]'hk_lt])
        input := c.input.move Dir3.right
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
          (idleDir (c.work i).read)
        output := c.output.writeAndMove (readBackWrite c.output.read)
          (idleDir c.output.read) } with hc1
    have htake : x.take k ++ [x[k]'hk_lt] = x.take (k + 1) := List.take_concat_get' x k hk_lt
    have hstate1 : c1.state = readState g S (x.take (k + 1)) := by rw [hc1, htake]
    have hcells1 : c1.input.cells = (Tape.init (x.map Γ.ofBool)).cells := by
      simp [hc1, Tape.move_cells, hcells]
    have hhead1 : c1.input.head = k + 1 + 1 := by simp [hc1, Tape.move, hhead]
    have houtput1 : c1.output.HasBinaryPrefix [] := hasBinaryPrefix_idle houtput
    obtain ⟨c', hreach, hstate', hcells', hhead', houtput'⟩ :=
      ih (k + 1) c1 (by omega) hstate1 hcells1 hhead1 houtput1 (by omega)
    exact ⟨c', .step hstep hreach, hstate', hcells', hhead', houtput'⟩

/-- The first step skips the left-end markers: the input head advances to cell
one over the input contents and the output head bumps off its marker. -/
private theorem lookup_initial_step (x : List Bool) :
    ∃ c0, (lookupTM g S).step ((lookupTM g S).initCfg x) = some c0 ∧
      c0.state = readState g S [] ∧
      c0.input.cells = (Tape.init (x.map Γ.ofBool)).cells ∧
      c0.input.head = 1 ∧
      c0.output.HasBinaryPrefix [] := by
  set c0 : Cfg 0 (lookupTM g S).Q :=
    { state := readState g S []
      input := (Tape.init (x.map Γ.ofBool)).move Dir3.right
      work := fun _ => (Tape.init []).move Dir3.right
      output := (Tape.init ([] : List Γ)).move Dir3.right } with hc0
  have hg : ((lookupTM g S).initCfg x).state ≠ (lookupTM g S).qhalt :=
    readState_ne_haltState g S []
  have hstep : (lookupTM g S).step ((lookupTM g S).initCfg x) = some c0 := by
    by_cases h : ([] : List Bool) ∈ S.prefixes
    · simp only [TM.step, hc0, lookupTM, readState, dif_pos h]
      exact congrArg some (Cfg.ext rfl rfl (Subsingleton.elim _ _) rfl)
    · simp only [TM.step, hc0, lookupTM, readState, dite_eq_right h]
      exact congrArg some (Cfg.ext rfl rfl (Subsingleton.elim _ _) rfl)
  refine ⟨c0, hstep, rfl, ?_, ?_, ?_⟩
  · rw [hc0]; simp [Tape.move_cells]
  · rw [hc0]; simp [Tape.move]
  · rw [hc0]; exact Tape.init_nil_move_right_hasBinaryPrefix_nil

/-- The handoff step from read phase to write phase: on reaching the input blank
the machine commits to writing the fixed output `if inp ∈ S then g inp else []`. -/
private theorem lookup_handoff_step (inp : List Bool) (c : Cfg 0 (lookupTM g S).Q)
    (hstate : c.state = readState g S inp)
    (hread : c.input.read = Γ.blank)
    (houtput : c.output.HasBinaryPrefix []) :
    ∃ c', (lookupTM g S).step c = some c' ∧
      c'.state = writeState g S (if inp ∈ S then g inp else [])
        (output_mem_suffixes_outputsFinset g S) ∧
      c'.output.HasBinaryPrefix [] := by
  set c1 : Cfg 0 (lookupTM g S).Q :=
    { state := writeState g S (if inp ∈ S then g inp else [])
        (output_mem_suffixes_outputsFinset g S)
      input := c.input.move (idleDir c.input.read)
      work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
        (idleDir (c.work i).read)
      output := c.output.writeAndMove (readBackWrite c.output.read)
        (idleDir c.output.read) } with hc1
  have hstep : (lookupTM g S).step c = some c1 := by
    by_cases hp : inp ∈ S.prefixes
    · simp [TM.step, lookupTM, hstate, hread, readState, writeState, haltState, dif_pos hp, hc1]
    · have hpS : inp ∉ S := fun h => hp (Finset.mem_prefixes_self h)
      simp [TM.step, lookupTM, hstate, hread, readState, writeState, haltState, dite_eq_right hp,
        ite_eq_right hpS, hc1]
  refine ⟨c1, hstep, by rw [hc1], ?_⟩
  rw [hc1]
  exact hasBinaryPrefix_idle houtput

/-- Writing one output symbol in the write phase extends the written prefix and
advances to the remaining suffix. -/
private theorem lookup_write_cons_step (a : Bool) (rest : List Bool)
    (hw : a :: rest ∈ (outputsFinset g S).suffixes) (c : Cfg 0 (lookupTM g S).Q)
    (hstate : c.state = writeState g S (a :: rest) hw) :
    (lookupTM g S).step c = some
      { state := writeState g S rest (Finset.mem_suffixes_of_suffix (List.suffix_cons a rest) hw)
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
          (idleDir (c.work i).read)
        output := c.output.writeAndMove (Γ.ofBool a) Dir3.right } := by
  cases a <;> simp [TM.step, lookupTM, hstate, writeState, haltState, Γ.ofBool, Γw.ofBool]

/-- The write phase: from a config whose output already holds `written` and whose
state carries the remaining suffix `w`, the machine writes `w` and halts, in
`|w| + 1` steps, leaving `written ++ w` on the output tape. -/
private theorem lookup_write_loop (written : List Bool) :
    ∀ (w : List Bool) (hw : w ∈ (outputsFinset g S).suffixes) (c : Cfg 0 (lookupTM g S).Q),
      c.state = writeState g S w hw →
      c.output.HasBinaryPrefix written →
      ∃ c',
        (lookupTM g S).reachesIn (w.length + 1) c c' ∧
        (lookupTM g S).halted c' ∧
        c'.output.HasBinaryPrefix (written ++ w) := by
  intro w
  induction w generalizing written with
  | nil =>
    intro hw c hstate houtput
    have hne : c.state ≠ (lookupTM g S).qhalt := by
      rw [hstate, writeState]; simp [lookupTM, haltState]
    set c1 : Cfg 0 (lookupTM g S).Q :=
      { state := haltState g S
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
          (idleDir (c.work i).read)
        output := c.output.writeAndMove (readBackWrite c.output.read)
          (idleDir c.output.read) } with hc1
    have hstep : (lookupTM g S).step c = some c1 := by
      simp [TM.step, lookupTM, hstate, writeState, haltState, hc1]
    refine ⟨c1, .step hstep .zero, ?_, ?_⟩
    · show c1.state = (lookupTM g S).qhalt
      rw [hc1]; rfl
    · rw [List.append_nil, hc1]
      exact hasBinaryPrefix_idle houtput
  | cons a rest ih =>
    intro hw c hstate houtput
    have hstep := lookup_write_cons_step g S a rest hw c hstate
    set c1 : Cfg 0 (lookupTM g S).Q :=
      { state := writeState g S rest (Finset.mem_suffixes_of_suffix (List.suffix_cons a rest) hw)
        input := c.input.move (idleDir c.input.read)
        work := fun i => (c.work i).writeAndMove (readBackWrite (c.work i).read)
          (idleDir (c.work i).read)
        output := c.output.writeAndMove (Γ.ofBool a) Dir3.right } with hc1
    have hout1 : c1.output.HasBinaryPrefix (written ++ [a]) := by
      rw [hc1]; exact Tape.hasBinaryPrefix_write_bit a houtput
    obtain ⟨c', hreach, hhalt, hout'⟩ :=
      ih (written ++ [a]) (Finset.mem_suffixes_of_suffix (List.suffix_cons a rest) hw) c1 rfl hout1
    refine ⟨c', ?_, hhalt, ?_⟩
    · have : rest.length + 1 + 1 = (a :: rest).length + 1 := by simp [List.length_cons]
      rw [← this]
      exact .step hstep hreach
    · rwa [List.append_assoc, List.singleton_append] at hout'

/-- The lookup machine computes `fun s => if s ∈ S then g s else []` within a
linear time bound. -/
theorem lookupTM_computesInTime :
    (lookupTM g S).ComputesInTime (fun s => if s ∈ S then g s else [])
      (fun m => m + (S.sup fun s => (g s).length) + 3) := by
  intro x
  obtain ⟨c0, hstep0, hst0, hcells0, hhead0, hout0⟩ := lookup_initial_step g S x
  obtain ⟨c1, hreadloop, hst1, hcells1, hhead1, hout1⟩ :=
    lookup_read_loop g S x x.length 0 c0 (by omega) hst0 hcells0 hhead0 hout0 (Nat.zero_le _)
  have hread1_blank : c1.input.read = Γ.blank := by
    rw [Tape.read, hhead1, hcells1, Tape.init_ofBool_cells_ge x x.length le_rfl]
  obtain ⟨c2, hstep2, hst2, hout2⟩ := lookup_handoff_step g S x c1 hst1 hread1_blank hout1
  set cval : List Bool := if x ∈ S then g x else [] with hcval
  obtain ⟨c3, hwriteloop, hhalt3, hout3⟩ :=
    lookup_write_loop g S [] cval (output_mem_suffixes_outputsFinset g S) c2 hst2 hout2
  have hlen : cval.length ≤ S.sup fun s => (g s).length := by
    rw [hcval]
    split
    · exact Finset.le_sup (f := fun s => (g s).length) ‹x ∈ S›
    · exact Nat.zero_le _
  refine ⟨c3, x.length + cval.length + 3, by dsimp only; omega, ?_, hhalt3, ?_⟩
  · have hreach :=
      reachesIn.step hstep0
        (reachesIn_trans (lookupTM g S) hreadloop
          (reachesIn.step hstep2 hwriteloop))
    have heq : x.length + (cval.length + 1 + 1) + 1 = x.length + cval.length + 3 := by omega
    rwa [heq] at hreach
  · have hres : c3.output.HasOutput cval := by
      have h := hout3
      rw [List.nil_append] at h
      exact h.hasOutput
    exact hres

end TM.FinsetDomain

open Polynomial in
/-- Internal proof that a function supported on a finite set belongs to `FP`:
the lookup machine's linear time bound is packaged as a degree-one polynomial. -/
theorem ite_mem_finset_mem_FP_internal (g : List Bool → List Bool) (S : Finset (List Bool)) :
    (fun s => if s ∈ S then g s else []) ∈ FP := by
  rw [mem_FP_iff_computesInTime_polynomial]
  refine ⟨0, TM.FinsetDomain.lookupTM g S, X + C ((S.sup fun s => (g s).length) + 3), ?_⟩
  have heval : (X + C ((S.sup fun s => (g s).length) + 3)).eval
      = fun m : ℕ => m + (S.sup fun s => (g s).length) + 3 := by
    funext m
    simp only [eval_add, eval_X, eval_C]
    omega
  rw [heval]
  exact TM.FinsetDomain.lookupTM_computesInTime g S

end Complexity
