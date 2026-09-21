/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Algebra
public import LeanPool.BeyondBethe.Complexitylib.Classes.P.Cobham.Internal.Encoding
public import Mathlib.Data.Fintype.Prod

/-!
# The encoded machine step, inside the algebra — proof internals

`Complexitylib.Classes.P.Cobham.Internal.Encoding` shows that one machine step
acts on an encoded configuration blockwise, via `tapeStepBlocks`. This module
shows the other half: that `tapeStepBlocks` is *in Cobham's algebra* once the
written symbol and the direction are fixed constants — which they are inside one
branch of `Cobham.tableFn`, since the branch is selected by the (state,
read-symbols) key.

Each half-block of the successor is a short composition of toolkit members:
`Cobham.takeFn` and `Cobham.dropFn` at width two, `Cobham.appendFn`,
`Cobham.const`, and one `Cobham.padFn` to restore the block width.

## Main results

- `Complexity.Cobham.tapeStepBlocksFst`, `Complexity.Cobham.tapeStepBlocksSnd` —
  both half-blocks of a stepped tape are in the algebra
-/


@[expose] public section

namespace Complexity

namespace Cobham

/-- The two-bit ruler: dropping or taking `2` is `dropFn`/`takeFn` against this
constant. -/
private def twoRuler : List Bool := [false, false]

/-- **The left half-block after a step is in the algebra.** For a fixed direction
and written symbol it is one of: the old left block unchanged (stay), the symbol
prepended (right), or two bits dropped (left). -/
theorem tapeStepBlocksFst {n : ℕ} (s : Γ) (d : Dir3)
    {gR gL gRt : (Fin n → List Bool) → List Bool}
    (hR : Cobham gR) (hL : Cobham gL) (_hRt : Cobham gRt) :
    Cobham fun v : Fin n → List Bool =>
      (tapeStepBlocks (gR v) s d (gL v) (gRt v)).1 := by
  cases d
  · exact (padFn hR (dropFn (Cobham.const twoRuler) hL)).of_eq fun _ => rfl
  · exact (padFn hR (appendFn (Cobham.const (symCode s)) hL)).of_eq fun _ => rfl
  · exact hL.of_eq fun _ => rfl

/-- **The right half-block after a step is in the algebra.** For a fixed
direction and written symbol it is the old right block with its leading symbol
replaced (stay), consumed (right), or pushed back together with the nearest left
symbol (left). -/
theorem tapeStepBlocksSnd {n : ℕ} (s : Γ) (d : Dir3)
    {gR gL gRt : (Fin n → List Bool) → List Bool}
    (hR : Cobham gR) (hL : Cobham gL) (hRt : Cobham gRt) :
    Cobham fun v : Fin n → List Bool =>
      (tapeStepBlocks (gR v) s d (gL v) (gRt v)).2 := by
  cases d
  · exact (padFn hR (appendFn
      (appendFn (takeFn (Cobham.const twoRuler) hL) (Cobham.const (symCode s)))
      (dropFn (Cobham.const twoRuler) hRt))).of_eq fun _ => rfl
  · exact (padFn hR (dropFn (Cobham.const twoRuler) hRt)).of_eq fun _ => rfl
  · exact (padFn hR (appendFn (Cobham.const (symCode s))
      (dropFn (Cobham.const twoRuler) hRt))).of_eq fun _ => rfl

/-- **Tape `j`'s two half-blocks, read out of an encoded configuration.** Block
`0` is the state, so tape `j` occupies blocks `2j+1` and `2j+2` — exactly the
indices `tapesStepFn` addresses with `Cobham.blockFn`. -/
theorem blockAt_cfgCode_tape {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) (j : ℕ) (hj : j < (cfgTapes c).length) :
    blockAt (blockRuler W) (cfgCode W c) (2 * j + 1)
        = padTo (blockRuler W) (leftCode (cfgTapes c)[j]) ∧
      blockAt (blockRuler W) (cfgCode W c) (2 * j + 2)
        = padTo (blockRuler W) (rightCode (cfgTapes c)[j] W) := by
  have hj' : j < k + 2 := by rwa [cfgTapes_length] at hj
  have hblocks : (tapesBlocks W (cfgTapes c)).length = 2 * (k + 2) := by
    rw [tapesBlocks_length, cfgTapes_length]
  obtain ⟨h1, h2⟩ := getElem?_tapesBlocks W (cfgTapes c) j
  rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem hj] at h1 h2
  simp only [Option.map_some] at h1 h2
  replace h1 := Option.some_inj.mp h1
  replace h2 := Option.some_inj.mp h2
  -- Work through `getElem?` so no dependent index proofs appear under a rewrite.
  have key1 : (cfgBlocks W c)[2 * j + 1]? = (tapesBlocks W (cfgTapes c))[2 * j]? := by
    rw [cfgBlocks_eq]; exact List.getElem?_cons_succ
  have key2 : (cfgBlocks W c)[2 * j + 2]? = (tapesBlocks W (cfgTapes c))[2 * j + 1]? := by
    rw [cfgBlocks_eq]; exact List.getElem?_cons_succ
  rw [List.getElem?_eq_getElem (by rw [cfgBlocks_length]; omega),
    List.getElem?_eq_getElem (by omega)] at key1
  rw [List.getElem?_eq_getElem (by rw [cfgBlocks_length]; omega),
    List.getElem?_eq_getElem (by omega)] at key2
  exact ⟨by rw [blockAt_cfgCode W c (2 * j + 1) (by rw [cfgBlocks_length]; omega),
      Option.some_inj.mp key1, h1],
    by rw [blockAt_cfgCode W c (2 * j + 2) (by rw [cfgBlocks_length]; omega),
      Option.some_inj.mp key2, h2]⟩

/-! ## The transition key

The key is the state together with the symbol under every head. Reading it out of
an encoding is one `takeFn` per field: the state block truncated to `|Q|` bits,
then the first two bits of each tape's right half-block. -/

/-- The read symbols of the tapes from index `j` on, `m` of them. -/
def readsFn (R : List Bool) (m j : ℕ) (z : List Bool) : List Bool :=
  match m with
  | 0 => []
  | m + 1 => (blockAt R z (2 * j + 2)).take 2 ++ readsFn R m (j + 1) z

/-- The transition key, read out of an encoded configuration. -/
def keyFn (R : List Bool) (q m : ℕ) (z : List Bool) : List Bool :=
  (blockAt R z 0).take q ++ readsFn R m 0 z

/-- **Reading the head symbols is in the algebra.** -/
theorem readsFn_mem {n : ℕ} (m j : ℕ)
    {gR gz : (Fin n → List Bool) → List Bool} (hR : Cobham gR) (hz : Cobham gz) :
    Cobham fun v : Fin n → List Bool => readsFn (gR v) m j (gz v) := by
  induction m generalizing j with
  | zero => exact Cobham.empty.of_eq fun _ => rfl
  | succ m ih =>
      exact (appendFn (takeFn (Cobham.const twoRuler) (blockFn hR hz (2 * j + 2)))
        (ih (j + 1))).of_eq fun _ => rfl

/-- **Reading the transition key is in the algebra.** -/
theorem keyFn_mem {n : ℕ} (q m : ℕ)
    {gR gz : (Fin n → List Bool) → List Bool} (hR : Cobham gR) (hz : Cobham gz) :
    Cobham fun v : Fin n → List Bool => keyFn (gR v) q m (gz v) :=
  (appendFn (takeFn (Cobham.const (List.replicate q false)) (blockFn hR hz 0))
    (readsFn_mem m 0 hR hz)).of_eq fun _ => by rw [keyFn, List.length_replicate]

/-- **The extracted key is the transition key.** -/
theorem readsFn_eq {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) (hW : ∀ t ∈ cfgTapes c, t.head ≤ W) :
    ∀ (m j : ℕ), j + m = (cfgTapes c).length →
      readsFn (blockRuler W) m j (cfgCode W c)
        = ((cfgTapes c).drop j).flatMap fun t => symCode t.read := by
  intro m
  induction m with
  | zero =>
      intro j hj
      have : (cfgTapes c).drop j = [] := by
        rw [List.drop_eq_nil_iff]; omega
      rw [readsFn, this, List.flatMap_nil]
  | succ m ih =>
      intro j hj
      have hjlt : j < (cfgTapes c).length := by omega
      obtain ⟨_, hRt⟩ := blockAt_cfgCode_tape W c j hjlt
      have hmem : (cfgTapes c)[j] ∈ cfgTapes c := List.getElem_mem hjlt
      rw [readsFn, hRt, List.drop_eq_getElem_cons hjlt, List.flatMap_cons,
        take_padTo _ _ 2 (by rw [rightCode_length]; have := hW _ hmem; omega)
          (by rw [rightCode_length, blockRuler_length, blockWidth]
              have := hW _ hmem; omega),
        take_rightCode _ (hW _ hmem), ih (j + 1) (by omega)]

/-- The whole key, read out of an encoded configuration. -/
theorem keyFn_eq {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) (hq : Fintype.card Q ≤ blockWidth W)
    (hW : ∀ t ∈ cfgTapes c, t.head ≤ W) :
    keyFn (blockRuler W) (Fintype.card Q) (k + 2) (cfgCode W c) = keyCode c := by
  rw [keyFn, state_of_cfgCode W c hq,
    readsFn_eq W c hW (k + 2) 0 (by rw [cfgTapes_length]; omega), List.drop_zero,
    keyCode]

/-! ## Lifting across all the tapes

A machine has a fixed number of tapes, so stepping all of them is a *finite*
composition — the recursion below is at the meta level, over the list of
per-tape actions, not inside the algebra. Tape `j` occupies blocks `2j+1` and
`2j+2` (block `0` is the state), which `Cobham.blockFn` addresses. -/

/-- The successor's tape blocks for one transition-table branch, as a function of
the predecessor's encoding: tape `j`'s two half-blocks, stepped, concatenated. -/
def tapesStepFn (R : List Bool) (acts : List (Γ × Dir3)) (j : ℕ) (z : List Bool) :
    List Bool :=
  match acts with
  | [] => []
  | a :: rest =>
      (tapeStepBlocks R a.1 a.2 (blockAt R z (2 * j + 1))
        (blockAt R z (2 * j + 2))).1 ++
      ((tapeStepBlocks R a.1 a.2 (blockAt R z (2 * j + 1))
        (blockAt R z (2 * j + 2))).2 ++ tapesStepFn R rest (j + 1) z)

/-- **Stepping every tape is in the algebra.** -/
theorem tapesStepFn_mem {n : ℕ} (acts : List (Γ × Dir3)) (j : ℕ)
    {gR gz : (Fin n → List Bool) → List Bool} (hR : Cobham gR) (hz : Cobham gz) :
    Cobham fun v : Fin n → List Bool => tapesStepFn (gR v) acts j (gz v) := by
  induction acts generalizing j with
  | nil => exact Cobham.empty.of_eq fun _ => rfl
  | cons a rest ih =>
      exact (appendFn
        (tapeStepBlocksFst a.1 a.2 hR (blockFn hR hz (2 * j + 1))
          (blockFn hR hz (2 * j + 2)))
        (appendFn
          (tapeStepBlocksSnd a.1 a.2 hR (blockFn hR hz (2 * j + 1))
            (blockFn hR hz (2 * j + 2)))
          (ih (j + 1)))).of_eq fun _ => rfl

/-- **The algebra-side tape step computes the machine-side one.** Reading the
half-blocks out of the encoding (`blockAt`) gives exactly the tapes' own
half-blocks, so `tapesStepFn` reproduces the blockwise map of
`tapesBlocks_tapesStep`. -/
theorem tapesStepFn_eq {k : ℕ} {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : ℕ) (c : Cfg k Q) :
    ∀ (acts : List (Γ × Dir3)) (j : ℕ), j + acts.length ≤ (cfgTapes c).length →
      tapesStepFn (blockRuler W) acts j (cfgCode W c)
        = ((List.zipWith (fun a t =>
            [(tapeStepBlocks (blockRuler W) a.1 a.2 (padTo (blockRuler W) (leftCode t))
                (padTo (blockRuler W) (rightCode t W))).1,
             (tapeStepBlocks (blockRuler W) a.1 a.2 (padTo (blockRuler W) (leftCode t))
                (padTo (blockRuler W) (rightCode t W))).2])
            acts ((cfgTapes c).drop j)).flatten).flatten := by
  intro acts
  induction acts with
  | nil => intro j _; rfl
  | cons a rest ih =>
      intro j hj
      have hjlt : j < (cfgTapes c).length := by
        simp only [List.length_cons] at hj; omega
      obtain ⟨hL, hRt⟩ := blockAt_cfgCode_tape W c j hjlt
      rw [List.drop_eq_getElem_cons hjlt, List.zipWith_cons_cons, List.flatten_cons,
        List.flatten_append, tapesStepFn, hL, hRt,
        ih (j + 1) (by simp only [List.length_cons] at hj; omega)]
      simp [List.append_assoc]

/-- One whole branch of the transition table: the new state block (a fixedValue)
followed by every tape stepped. -/
def branchFn (R q' : List Bool) (acts : List (Γ × Dir3)) (z : List Bool) :
    List Bool :=
  padTo R q' ++ tapesStepFn R acts 0 z

/-- **A transition-table branch is in the algebra.** With the branch fixed, the
new state code and every tape's write and direction are constants, so the whole
successor configuration is a finite composition of toolkit members. -/
theorem branchFn_mem {n : ℕ} (q' : List Bool) (acts : List (Γ × Dir3))
    {gR gz : (Fin n → List Bool) → List Bool} (hR : Cobham gR) (hz : Cobham gz) :
    Cobham fun v : Fin n → List Bool => branchFn (gR v) q' acts (gz v) :=
  (appendFn (padFn hR (Cobham.const q')) (tapesStepFn_mem acts 0 hR hz)).of_eq
    fun _ => rfl

/-- **The join.** For a fixed transition-table branch, the algebra-side successor
`branchFn` — built purely from `takeFn`/`dropFn`/`appendFn`/`padFn`/`const` — *is*
the encoding of the machine's successor configuration.

This is the point where the two halves of the development meet: the machine side
(`cfgBlocks_step`, from the six write-and-move lemmas) and the algebra side
(`tapesStepFn`, in the class by `branchFn_mem`). -/
theorem branchFn_eq {k : ℕ} (tm : TM k) {c c' : Cfg k tm.Q} {W : ℕ}
    (h : tm.step c = some c') (hout : c.output.StartInvariant)
    (hwork : ∀ i, (c.work i).StartInvariant)
    (hgood : List.Forall₂ (fun (a : Γ × Dir3) (t : Tape) =>
      (t.head = 0 → a.1 = t.cells t.head) ∧
      (a.2 ≠ Dir3.right → t.head ≠ 0) ∧ t.head ≤ W) (stepActs tm c) (cfgTapes c)) :
    branchFn (blockRuler W) (stateCode c'.state) (stepActs tm c) (cfgCode W c)
      = cfgCode W c' := by
  rw [branchFn, tapesStepFn_eq W c (stepActs tm c) 0 (by simpa using hgood.length_eq.le)]
  conv_rhs => rw [cfgCode, cfgBlocks_step tm h hout hwork hgood, List.flatten_cons]
  simp

/-! ## The whole transition table

A machine has finitely many (state, read-symbols) keys, so the transition
function is a finite table: one `branchFn` per key, selected by matching the key
read out of the encoding against the key's fixedValue pattern. -/

/-- The transition table's index set: every (state, read-symbols) pair. -/
noncomputable def stepEntries {k : ℕ} (tm : TM k) :
    List (tm.Q × (Fin (k + 2) → Γ)) :=
  (Finset.univ : Finset (tm.Q × (Fin (k + 2) → Γ))).toList

/-- Every key is in the table. -/
theorem mem_stepEntries {k : ℕ} (tm : TM k) (p : tm.Q × (Fin (k + 2) → Γ)) :
    p ∈ stepEntries tm := Finset.mem_toList.mpr (Finset.mem_univ p)

/-- The branch a transition key selects. A halting key stands still: the machine
has stopped, but the *simulation* runs for a fixed polynomial number of steps, so
the encoding has to be a fixed point from then on. -/
noncomputable def stepBranch {k : ℕ} (tm : TM k) (R : List Bool)
    (p : tm.Q × (Fin (k + 2) → Γ)) (z : List Bool) : List Bool :=
  if p.1 = tm.qhalt then z
  else branchFn R (stateCode (stepStateOf tm p.1 p.2)) (stepActsOf tm p.1 p.2) z

theorem stepBranch_halt {k : ℕ} (tm : TM k) (R : List Bool)
    {p : tm.Q × (Fin (k + 2) → Γ)} (h : p.1 = tm.qhalt) (z : List Bool) :
    stepBranch tm R p z = z := if_pos h

theorem stepBranch_step {k : ℕ} (tm : TM k) (R : List Bool)
    {p : tm.Q × (Fin (k + 2) → Γ)} (h : p.1 ≠ tm.qhalt) (z : List Bool) :
    stepBranch tm R p z
      = branchFn R (stateCode (stepStateOf tm p.1 p.2)) (stepActsOf tm p.1 p.2) z :=
  if_neg h

/-- **One machine step, on encodings.** The table dispatches on the key read out
of the encoding and applies that key's branch. -/
noncomputable def stepFn {k : ℕ} (tm : TM k) (R z : List Bool) : List Bool :=
  (stepEntries tm).foldr
    (fun p acc =>
      caseBit₀ (matchPrefix (keyPattern p) (keyFn R (Fintype.card tm.Q) (k + 2) z))
        (stepBranch tm R p z) acc)
    []

/-- **The encoded step is in the algebra.** -/
theorem stepFn_mem {n k : ℕ} (tm : TM k)
    {gR gz : (Fin n → List Bool) → List Bool} (hR : Cobham gR) (hz : Cobham gz) :
    Cobham fun v : Fin n → List Bool => stepFn tm (gR v) (gz v) := by
  refine (tableFn (keyFn_mem (Fintype.card tm.Q) (k + 2) hR hz) Cobham.empty
    ((stepEntries tm).map fun p =>
      (keyPattern p, fun v : Fin n → List Bool => stepBranch tm (gR v) p (gz v)))
    ?_).of_eq fun v => ?_
  · rintro p hp
    obtain ⟨q, -, rfl⟩ := List.mem_map.mp hp
    by_cases hh : q.1 = tm.qhalt
    · exact hz.of_eq fun v => (stepBranch_halt tm (gR v) hh (gz v)).symm
    · exact (branchFn_mem _ _ hR hz).of_eq fun v =>
        (stepBranch_step tm (gR v) hh (gz v)).symm
  · rw [stepFn, List.foldr_map]

/-- **The table selects the configuration's own branch.** The key read out of the
encoding is the configuration's key, and by `keyPattern_injective` no other
entry's pattern matches it. -/
theorem stepFn_apply {k : ℕ} (tm : TM k) (c : Cfg k tm.Q) {W : ℕ}
    (hq : Fintype.card tm.Q ≤ blockWidth W) (hW : ∀ t ∈ cfgTapes c, t.head ≤ W) :
    stepFn tm (blockRuler W) (cfgCode W c)
      = stepBranch tm (blockRuler W) (c.state, cfgReads c) (cfgCode W c) := by
  have hkey := foldr_table_eq (keyCode c) []
    (stepBranch tm (blockRuler W) (c.state, cfgReads c) (cfgCode W c))
    ((stepEntries tm).map fun p =>
      (keyPattern p, stepBranch tm (blockRuler W) p (cfgCode W c))) ?_ ?_
  · rw [List.foldr_map] at hkey
    rw [stepFn, keyFn_eq W c hq hW]
    exact hkey
  · refine ⟨_, List.mem_map_of_mem (mem_stepEntries tm (c.state, cfgReads c)), ?_⟩
    show keyPattern (c.state, cfgReads c) <+: keyCode c
    rw [← keyCode_eq]
  · rintro q hq' hpre
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hq'
    replace hpre : keyPattern p <+: keyCode c := hpre
    have hlen : (keyPattern p).length = (keyCode c).length := by simp
    have hp : p = (c.state, cfgReads c) :=
      keyPattern_injective (by rw [hpre.eq_of_length hlen, keyCode_eq])
    rw [hp]

/-- **The encoded step computes the machine step.** -/
theorem stepFn_eq {k : ℕ} (tm : TM k) {c c' : Cfg k tm.Q} {W : ℕ}
    (h : tm.step c = some c') (hq : Fintype.card tm.Q ≤ blockWidth W)
    (hW : ∀ t ∈ cfgTapes c, t.head ≤ W)
    (hout : c.output.StartInvariant) (hwork : ∀ i, (c.work i).StartInvariant)
    (hgood : List.Forall₂ (fun (a : Γ × Dir3) (t : Tape) =>
      (t.head = 0 → a.1 = t.cells t.head) ∧
      (a.2 ≠ Dir3.right → t.head ≠ 0) ∧ t.head ≤ W) (stepActs tm c) (cfgTapes c)) :
    stepFn tm (blockRuler W) (cfgCode W c) = cfgCode W c' := by
  rw [stepFn_apply tm c hq hW,
    stepBranch_step tm _ (TM.state_ne_qhalt_of_step h), ← step_state_eq tm h,
    ← stepActs_eq_stepActsOf]
  exact branchFn_eq tm h hout hwork hgood

/-- **A halted encoding is a fixed point.** -/
theorem stepFn_halted {k : ℕ} (tm : TM k) {c : Cfg k tm.Q} {W : ℕ}
    (h : c.state = tm.qhalt) (hq : Fintype.card tm.Q ≤ blockWidth W)
    (hW : ∀ t ∈ cfgTapes c, t.head ≤ W) :
    stepFn tm (blockRuler W) (cfgCode W c) = cfgCode W c := by
  rw [stepFn_apply tm c hq hW, stepBranch_halt tm _ h]

/-! ## Length bounds

`Cobham.iterFn` needs one polynomial bound covering *every* iterate, including
the ones reached from junk inputs. Both simulated steps keep an encoding inside a
fixed number of blocks, which is all the bound needs. -/

/-- Total dispatch returns one of its two branches. -/
private theorem caseBit₀_cases (s x y : List Bool) :
    caseBit₀ s x y = x ∨ caseBit₀ s x y = y := by
  cases s with
  | nil => exact Or.inr rfl
  | cons b s => cases b <;> simp

/-- Both half-blocks of a stepped tape fit in one block each. -/
private theorem tapeStepBlocks_length_le (R : List Bool) (s : Γ) (d : Dir3)
    (L Rt : List Bool) (hL : L.length ≤ R.length) :
    (tapeStepBlocks R s d L Rt).1.length ≤ R.length ∧
      (tapeStepBlocks R s d L Rt).2.length ≤ R.length := by
  cases d <;> exact ⟨by simp [tapeStepBlocks, hL], by simp [tapeStepBlocks]⟩

theorem tapesStepFn_length_le (R : List Bool) :
    ∀ (acts : List (Γ × Dir3)) (j : ℕ) (z : List Bool),
      (tapesStepFn R acts j z).length ≤ 2 * acts.length * R.length := by
  intro acts
  induction acts with
  | nil => intro j z; simp [tapesStepFn]
  | cons a rest ih =>
      intro j z
      obtain ⟨h1, h2⟩ := tapeStepBlocks_length_le R a.1 a.2
        (blockAt R z (2 * j + 1)) (blockAt R z (2 * j + 2))
        (by rw [blockAt]; simp)
      have := ih (j + 1) z
      have hexp : 2 * (rest.length + 1) * R.length
          = 2 * rest.length * R.length + (R.length + R.length) := by ring
      rw [tapesStepFn, List.length_append, List.length_append, List.length_cons, hexp]
      omega

theorem branchFn_length_le (R q' : List Bool) (acts : List (Γ × Dir3)) (z : List Bool) :
    (branchFn R q' acts z).length ≤ (2 * acts.length + 1) * R.length := by
  have := tapesStepFn_length_le R acts 0 z
  have hexp : (2 * acts.length + 1) * R.length
      = 2 * acts.length * R.length + R.length := by ring
  rw [branchFn, List.length_append, padTo_length, hexp]
  omega

@[simp] theorem stepActsOf_length {k : ℕ} (tm : TM k) (q : tm.Q)
    (syms : Fin (k + 2) → Γ) : (stepActsOf tm q syms).length = k + 2 := by
  rw [stepActsOf]
  simp

/-- **An encoded configuration stays within its blocks.** -/
theorem stepFn_length_le {k : ℕ} (tm : TM k) (R z : List Bool)
    (hz : z.length ≤ (2 * (k + 2) + 1) * R.length) :
    (stepFn tm R z).length ≤ (2 * (k + 2) + 1) * R.length := by
  rw [stepFn]
  induction stepEntries tm with
  | nil => simp
  | cons p rest ih =>
      rw [List.foldr_cons]
      rcases caseBit₀_cases (matchPrefix (keyPattern p)
        (keyFn R (Fintype.card tm.Q) (k + 2) z))
        (stepBranch tm R p z) _ with h | h
      · rw [h]
        by_cases hh : p.1 = tm.qhalt
        · rw [stepBranch_halt tm R hh]; exact hz
        · rw [stepBranch_step tm R hh]
          have := branchFn_length_le R (stateCode (stepStateOf tm p.1 p.2))
            (stepActsOf tm p.1 p.2) z
          rwa [stepActsOf_length] at this
      · rw [h]; exact ih

/-! ## Rewinding the output head

The encoding splits a tape at its head, so reading a tape off an encoding is
easy only when the head sits at cell `0` — then the left half is empty and the
right half is the whole tape, in order. Driving the head back to cell `0` is a
*separate* iteration, of a step that moves one cell left and writes nothing.

It is stated on one tape's pair of half-blocks rather than on a whole
configuration: after the simulation only the output tape matters, and a pair of
blocks splits with one `takeFn`/`dropFn`. -/

/-- One tape as its two padded half-blocks, concatenated. -/
def pairCode (W : ℕ) (t : Tape) : List Bool :=
  padTo (blockRuler W) (leftCode t) ++ padTo (blockRuler W) (rightCode t W)

theorem take_pairCode (W : ℕ) (t : Tape) :
    (pairCode W t).take (blockRuler W).length = padTo (blockRuler W) (leftCode t) :=
  List.take_left' (by simp)

theorem drop_pairCode (W : ℕ) (t : Tape) :
    (pairCode W t).drop (blockRuler W).length = padTo (blockRuler W) (rightCode t W) :=
  List.drop_left' (by simp)

/-- One left move on a pair of half-blocks, writing back the symbol `s`. -/
def rewindStep (R : List Bool) (s : Γ) (z : List Bool) : List Bool :=
  (tapeStepBlocks R s Dir3.left (z.take R.length) (z.drop R.length)).1 ++
    (tapeStepBlocks R s Dir3.left (z.take R.length) (z.drop R.length)).2

/-- **One rewind step.** The head moves one cell left, except at cell `0` — where
it reads `▷` and stays put, which is also what the machine model does. The symbol
written back is the one just read, so nothing changes but the head. -/
def rewindFn (R z : List Bool) : List Bool :=
  caseBit₀ (matchPrefix (symCode Γ.start) (z.drop R.length)) z
    (caseBit₀ (matchPrefix (symCode Γ.blank) (z.drop R.length)) (rewindStep R Γ.blank z)
      (caseBit₀ (matchPrefix (symCode Γ.zero) (z.drop R.length)) (rewindStep R Γ.zero z)
        (rewindStep R Γ.one z)))

/-- **The rewind step is in the algebra.** -/
theorem rewindFn_mem {n : ℕ} {gR gz : (Fin n → List Bool) → List Bool}
    (hR : Cobham gR) (hz : Cobham gz) :
    Cobham fun v : Fin n → List Bool => rewindFn (gR v) (gz v) := by
  have hstep : ∀ s : Γ, Cobham fun v : Fin n → List Bool => rewindStep (gR v) s (gz v) :=
    fun s =>
      (appendFn (tapeStepBlocksFst s Dir3.left hR (takeFn hR hz) (dropFn hR hz))
        (tapeStepBlocksSnd s Dir3.left hR (takeFn hR hz) (dropFn hR hz))).of_eq
        fun _ => rfl
  have hkey : Cobham fun v : Fin n → List Bool => (gz v).drop (gR v).length :=
    dropFn hR hz
  exact (iteFn (matchPrefixFn hkey _) hz
    (iteFn (matchPrefixFn hkey _) (hstep _)
      (iteFn (matchPrefixFn hkey _) (hstep _) (hstep _)))).of_eq fun _ => rfl

/-- The first two bits of a tape's padded right half-block code its read symbol. -/
theorem take_two_drop_pairCode {W : ℕ} (t : Tape) (hW : t.head ≤ W) :
    ((pairCode W t).drop (blockRuler W).length).take 2 = symCode t.read := by
  rw [drop_pairCode,
    take_padTo _ _ 2 (by rw [rightCode_length]; omega)
      (by rw [rightCode_length, blockRuler_length, blockWidth]; omega),
    take_rightCode _ hW]

/-- A two-bit symbol code prefixes a padded right half-block exactly when it is
*the* read symbol's code. -/
private theorem matchPrefix_symCode {W : ℕ} (t : Tape) (hW : t.head ≤ W) (s : Γ) :
    matchPrefix (symCode s) ((pairCode W t).drop (blockRuler W).length)
      = if s = t.read then [true] else [false] := by
  have hlen : (symCode s).length = 2 := symCode_length s
  split
  · next h =>
      subst h
      refine (matchPrefix_eq_true_iff _ _).mpr ?_
      rw [← take_two_drop_pairCode t hW, ← hlen]
      exact List.take_prefix _ _
  · next h =>
      rcases matchPrefix_flag (symCode s)
        ((pairCode W t).drop (blockRuler W).length) with hm | hm
      · exfalso
        have hpre := (matchPrefix_eq_true_iff _ _).mp hm
        have : symCode s = symCode t.read := by
          rw [← take_two_drop_pairCode t hW, ← hlen]
          exact List.prefix_iff_eq_take.mp hpre
        exact h (symCode_injective this)
      · exact hm

/-- At cell `0` a left move stands still — `Nat` subtraction saturates. -/
private theorem move_left_of_head_zero {t : Tape} (h : t.head = 0) :
    t.move Dir3.left = t := by
  obtain ⟨hd, cs⟩ := t
  simp only at h
  subst h
  rfl

/-- **The rewind step computes a left move.** Away from cell `0` the symbol
written back is the one read, so `tapeStepBlocks_eq` applies with
`Tape.write_read_self`; at cell `0` the head reads `▷` and both sides stand
still. -/
theorem rewindFn_eq {W : ℕ} (t : Tape) (hinv : t.StartInvariant) (hW : t.head ≤ W) :
    rewindFn (blockRuler W) (pairCode W t) = pairCode W (t.move Dir3.left) := by
  by_cases h0 : t.head = 0
  · have hread : t.read = Γ.start := by rw [Tape.read, h0]; exact hinv.1
    have hmove : t.move Dir3.left = t := move_left_of_head_zero h0
    rw [rewindFn, matchPrefix_symCode t hW, if_pos hread.symm, caseBit₀_cons, cond_true,
      hmove]
  · have hread : t.read ≠ Γ.start := hinv.read_ne_start (by omega)
    have hstep : ∀ s : Γ, s = t.read →
        rewindStep (blockRuler W) s (pairCode W t) = pairCode W (t.move Dir3.left) := by
      rintro s rfl
      have := tapeStepBlocks_eq (W := W) t t.read Dir3.left (fun _ => rfl)
        (fun _ => h0) hW
      rw [rewindStep, take_pairCode, drop_pairCode, this, write_read_self, pairCode]
    rw [rewindFn, matchPrefix_symCode t hW, matchPrefix_symCode t hW,
      matchPrefix_symCode t hW]
    cases hr : t.read with
    | start => exact absurd hr hread
    | blank | zero | one =>
        simp +decide only [caseBit₀]
        exact hstep _ hr.symm

/-- **A rewound pair stays within its two blocks.** -/
theorem rewindFn_length_le (R z : List Bool) (hz : z.length ≤ 2 * R.length) :
    (rewindFn R z).length ≤ 2 * R.length := by
  have hstep : ∀ s : Γ, (rewindStep R s z).length = 2 * R.length := fun s => by
    rw [rewindStep, tapeStepBlocks, List.length_append, padTo_length, padTo_length]
    omega
  rw [rewindFn]
  rcases caseBit₀_cases (matchPrefix (symCode Γ.start) (z.drop R.length)) z _ with h | h
  · rw [h]; exact hz
  · rw [h]
    rcases caseBit₀_cases (matchPrefix (symCode Γ.blank) (z.drop R.length))
      (rewindStep R Γ.blank z) _ with h2 | h2
    · rw [h2]; exact (hstep _).le
    · rw [h2]
      rcases caseBit₀_cases (matchPrefix (symCode Γ.zero) (z.drop R.length))
        (rewindStep R Γ.zero z) _ with h3 | h3
      · rw [h3]; exact (hstep _).le
      · rw [h3]; exact (hstep _).le

/-! ## The initial encoding

At the start every tape but the input is blank and every head is at cell `0`, so
the encoding is a fixedValue apart from the input tape's right half-block — which
is the input string at two bits per cell. Zero padding *is* blank padding, which
is why `symCode Γ.blank = [0,0]`. -/

/-- A bitstring as tape cells, two bits each. -/
def encodeBits (x : List Bool) : List Bool := x.flatMap fun b => symCode (Γ.ofBool b)

@[simp] theorem encodeBits_nil : encodeBits [] = [] := rfl

@[simp] theorem encodeBits_cons (b : Bool) (x : List Bool) :
    encodeBits (b :: x) = symCode (Γ.ofBool b) ++ encodeBits x := rfl

@[simp] theorem encodeBits_length (x : List Bool) :
    (encodeBits x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih =>
      rw [encodeBits_cons, List.length_append, symCode_length, ih, List.length_cons]
      omega

/-- The step of `encodeBits`: prepend the peeled bit's two-bit code. -/
private def encStep (b : Bool) (w : Fin 2 → List Bool) : List Bool :=
  symCode (Γ.ofBool b) ++ w 1

private theorem encStep_cons (b : Bool) (x p : List Bool) (v : Fin 0 → List Bool) :
    encStep b (Fin.cons x (Fin.cons p v)) = symCode (Γ.ofBool b) ++ p := rfl

/-- **Coding a string as tape cells is in the algebra.** -/
theorem encodeBitsFn {n : ℕ} {g : (Fin n → List Bool) → List Bool} (h : Cobham g) :
    Cobham fun v : Fin n → List Bool => encodeBits (g v) := by
  have hrec : ∀ (x : List Bool) (v : Fin 0 → List Bool),
      recNotation (fun _ : Fin 0 → List Bool => ([] : List Bool)) (encStep false)
        (encStep true) x v = encodeBits x := by
    intro x v
    induction x with
    | nil => rfl
    | cons b x ih =>
        cases b <;>
          · rw [recNotation_cons]
            simp only [cond_true, cond_false]
            rw [encStep_cons, ih, encodeBits_cons]
  have hs : ∀ b : Bool, Cobham (encStep b) := fun b =>
    (appendFn (Cobham.const (symCode (Γ.ofBool b))) (Cobham.proj 1)).of_eq fun _ => rfl
  have hbase : Cobham fun v : Fin 1 → List Bool => encodeBits (v 0) := by
    refine (Cobham.boundedRec Cobham.empty (hs false) (hs true)
      (appendFn (Cobham.proj 0) (Cobham.proj 0)) ?_).of_eq fun v => ?_
    · intro x v
      rw [hrec, encodeBits_length, Fin.cons_zero, List.length_append]
      omega
    · rw [hrec]
  exact (Cobham.comp hbase fun _ : Fin 1 => h).of_eq fun _ => rfl

/-- **The initial encoding.** Everything but the input tape's right half-block is
a fixedValue of the machine. -/
noncomputable def initFn {k : ℕ} (tm : TM k) (R x : List Bool) : List Bool :=
  padTo R (stateCode tm.qstart) ++
    (padTo R [] ++ (padTo R (symCode Γ.start ++ encodeBits x) ++
      (List.replicate (k + 1) (padTo R [] ++ padTo R (symCode Γ.start))).flatten))

/-- **The initial encoding is in the algebra.** -/
theorem initFn_mem {n k : ℕ} (tm : TM k)
    {gR gx : (Fin n → List Bool) → List Bool} (hR : Cobham gR) (hx : Cobham gx) :
    Cobham fun v : Fin n → List Bool => initFn tm (gR v) (gx v) :=
  (appendFn (padFn hR (Cobham.const _))
    (appendFn (padFn hR Cobham.empty)
      (appendFn (padFn hR (appendFn (Cobham.const _) (encodeBitsFn hx)))
        (repeatFn (appendFn (padFn hR Cobham.empty)
          (padFn hR (Cobham.const _))) (k + 1))))).of_eq fun _ => rfl

/-! ### The initial tapes -/

private theorem flatten_tapesBlocks (W : ℕ) : ∀ ts : List Tape,
    (tapesBlocks W ts).flatten
      = (ts.map fun t => padTo (blockRuler W) (leftCode t)
          ++ padTo (blockRuler W) (rightCode t W)).flatten := by
  intro ts
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      rw [tapesBlocks, List.flatMap_cons, List.flatten_append, ← tapesBlocks, ih,
        List.map_cons, List.flatten_cons, tapeBlocks]
      simp

/-- Windows concatenate. -/
theorem cellsCode_add (t : Tape) (i a b : ℕ) :
    cellsCode t i (a + b) = cellsCode t i a ++ cellsCode t (i + a) b := by
  induction a generalizing i with
  | zero => simp
  | succ a ih =>
      rw [show a + 1 + b = (a + b) + 1 from by omega, cellsCode_succ_left,
        cellsCode_succ_left, ih, List.append_assoc,
        show i + 1 + a = i + (a + 1) from by omega]

private theorem cellsCode_of_bits (x : List Bool) :
    ∀ (t : Tape) (i : ℕ), (∀ j, ∀ hj : j < x.length, t.cells (i + j) = Γ.ofBool x[j]) →
      cellsCode t i x.length = encodeBits x := by
  induction x with
  | nil => intro t i _; rfl
  | cons b x ih =>
      intro t i hcells
      rw [List.length_cons, cellsCode_succ_left, encodeBits_cons,
        show t.cells i = Γ.ofBool b from by simpa using hcells 0 (by simp)]
      congr 1
      exact ih t (i + 1) fun j hj => by
        have := hcells (j + 1) (by rw [List.length_cons]; omega)
        rw [show i + 1 + j = i + (j + 1) from by omega]
        simpa using this

private theorem cellsCode_of_blank (t : Tape) (i w : ℕ)
    (h : ∀ j < w, t.cells (i + j) = Γ.blank) :
    cellsCode t i w = List.replicate (2 * w) false := by
  induction w generalizing i with
  | zero => rfl
  | succ w ih =>
      rw [cellsCode_succ_left, show t.cells i = Γ.blank from by simpa using h 0 (by omega),
        ih (i + 1) fun j hj => by
          rw [show i + 1 + j = i + (j + 1) from by omega]; exact h (j + 1) (by omega),
        show 2 * (w + 1) = 2 + 2 * w from by omega, List.replicate_add]
      rfl

/-- **The initial encoding is the initial configuration's.** -/
theorem initFn_eq {k : ℕ} (tm : TM k) (W : ℕ) (x : List Bool) (hx : x.length ≤ W) :
    initFn tm (blockRuler W) x = cfgCode W (tm.initCfg x) := by
  set R := blockRuler W with hR
  -- The input tape.
  have hin : padTo R (rightCode (Tape.init (x.map Γ.ofBool)) W)
      = padTo R (symCode Γ.start ++ encodeBits x) := by
    have h0 : cellsCode (Tape.init (x.map Γ.ofBool)) 0 1 = symCode Γ.start := by
      rw [cellsCode_succ_left, cellsCode_zero, List.append_nil, Tape.init_cells_zero]
    have h1 : cellsCode (Tape.init (x.map Γ.ofBool)) 1 x.length = encodeBits x :=
      cellsCode_of_bits x _ 1 fun j hj => by
        rw [show 1 + j = j + 1 from by omega, Tape.init_cells_succ]
        have hjm : j < (x.map Γ.ofBool).length := by simpa using hj
        rw [List.getElem?_eq_getElem hjm]
        simp
    have h2 : cellsCode (Tape.init (x.map Γ.ofBool)) (1 + x.length) (W - x.length)
        = List.replicate (2 * (W - x.length)) false :=
      cellsCode_of_blank _ _ _ fun j _ => by
        rw [show 1 + x.length + j = (x.length + j) + 1 from by omega,
          Tape.init_cells_succ, List.getElem?_eq_none (by simp)]
        rfl
    have hcells : cellsCode (Tape.init (x.map Γ.ofBool)) 0 (W + 1)
        = symCode Γ.start ++ (encodeBits x
            ++ List.replicate (2 * (W - x.length)) false) := by
      rw [show W + 1 = 1 + (x.length + (W - x.length)) from by omega,
        cellsCode_add _ 0 1 _, cellsCode_add _ (0 + 1) x.length _]
      simp only [Nat.zero_add]
      rw [h0, h1, h2]
    rw [rightCode, Tape.init_head, Nat.sub_zero, hcells, ← List.append_assoc,
      padTo_append_replicate]
  have hblank : padTo R (rightCode (Tape.init []) W) = padTo R (symCode Γ.start) := by
    have h0 : cellsCode (Tape.init ([] : List Γ)) 0 1 = symCode Γ.start := by
      rw [cellsCode_succ_left, cellsCode_zero, List.append_nil, Tape.init_cells_zero]
    have h2 : cellsCode (Tape.init ([] : List Γ)) 1 W
        = List.replicate (2 * W) false :=
      cellsCode_of_blank _ _ _ fun j _ => by
        rw [show 1 + j = j + 1 from by omega, Tape.init_nil_cells_succ]
    have hcells : cellsCode (Tape.init ([] : List Γ)) 0 (W + 1)
        = symCode Γ.start ++ List.replicate (2 * W) false := by
      rw [show W + 1 = 1 + W from by omega, cellsCode_add _ 0 1 W]
      simp only [Nat.zero_add]
      rw [h0, h2]
    rw [rightCode, Tape.init_head, Nat.sub_zero, hcells, padTo_append_replicate]
  have hleft : ∀ contents : List Γ, leftCode (Tape.init contents) = [] := fun _ => rfl
  have hct : cfgTapes (tm.initCfg x)
      = Tape.init (x.map Γ.ofBool) :: List.replicate (k + 1) (Tape.init []) := by
    rw [cfgTapes]
    congr 1
    show (Tape.init [] : Tape) :: List.ofFn (fun _ : Fin k => (Tape.init [] : Tape))
      = List.replicate (k + 1) (Tape.init [])
    rw [List.replicate_succ, List.ofFn_const]
  rw [cfgCode, cfgBlocks_eq, List.flatten_cons, flatten_tapesBlocks, hct,
    List.map_cons, List.flatten_cons, List.map_replicate, hleft, hleft, hin, hblank,
    initFn, List.append_assoc]

end Cobham

end Complexity
