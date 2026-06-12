/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import LeanPool.CircuitComplexity.Nondeterminism.Defs
import LeanPool.CircuitComplexity.Internal.ShannonUpper

/-! # Internal: Nondeterministic Quantification Circuit Constructions

This internal module provides the circuit constructions needed for the
nondeterministic quantification complexity bounds in `Circ.Nondeterminism`.

## Circuit restriction

Given a circuit computing `f : BitString ((k+1)+m) → Bool`, we construct
a circuit of the same size computing `restrictFirst f b : BitString (k+m) → Bool`
(the function with its first input hardwired to `b`).

The key construction is `restrictGateP`, which transforms each gate in-place:

* If **both inputs** reference wire 0 (the hardwired input), the gate becomes
  a constant gate producing the correct value.
* If **one input** references wire 0, the gate simplifies to either a constant
  or an identity on the other input, depending on the operation and the
  hardwired value.
* If **neither input** references wire 0, both wire indices are shifted down
  by 1 (since the hardwired input is removed).

In all cases, the gate count is preserved.

## OR combination

The OR of two Boolean functions has circuit complexity bounded by the sum
of their complexities plus one, using `ShannonUpper.binopCircuit`.
-/

namespace CircuitComplexity


variable {k m : Nat}

/-! ## Gate evaluation helpers -/

/-- Decompose the evaluation of a fan-in-2 AND/OR gate into a match on its
    operation applied to the two negation-adjusted input values. -/
private theorem andOr2_eval_two {W : Nat} (g : Gate Basis.andOr2 W)
    (wv : BitString W) :
    g.eval wv =
    let a0 := g.negated ⟨0,
      by rw [andOr2_fanIn]; omega⟩ ^^ wv (g.inputs ⟨0, by rw [andOr2_fanIn]; omega⟩)
    let a1 := g.negated ⟨1,
      by rw [andOr2_fanIn]; omega⟩ ^^ wv (g.inputs ⟨1, by rw [andOr2_fanIn]; omega⟩)
    match g.op with
    | .and => a0 && a1
    | .or  => a0 || a1 := by
  have hf := andOr2_fanIn g
  simp only [Gate.eval, Basis.andOr2]
  cases g.op <;> simp_all [AONOp.eval, Fin.foldl_succ_last, Fin.foldl_zero] <;>
    congr 1

/-! ## Restriction gate construction -/

/-- A constant-output gate: `OR(x, ¬x) = true` or `AND(x, ¬x) = false`. -/
private def mkConstGateP {G : Nat} [NeZero m] (val : Bool) (bound : Nat) :
    { g : Gate Basis.andOr2 (k + m + G) //
      ∀ j : Fin g.fanIn, (g.inputs j).val < k + m + bound } :=
  have hW : 0 < k + m + G := by have := NeZero.ne m; omega
  have hB : 0 < k + m + bound := by have := NeZero.ne m; omega
  if val then
    ⟨{ op := .or, fanIn := 2, arityOk := rfl,
       inputs := fun _ => ⟨0, hW⟩,
       negated := fun i => if i.val = 0 then false else true },
     fun _ => by dsimp; exact hB⟩
  else
    ⟨{ op := .and, fanIn := 2, arityOk := rfl,
       inputs := fun _ => ⟨0, hW⟩,
       negated := fun i => if i.val = 0 then false else true },
     fun _ => by dsimp; exact hB⟩

/-- An identity/passthrough gate: `OP(w, w)` with negation `neg`. -/
private def mkIdentGateP {G : Nat} (op : AONOp) (w : Fin (k + m + G)) (neg : Bool) (bound : Nat)
    (hw : w.val < k + m + bound) :
    { g : Gate Basis.andOr2 (k + m + G) //
      ∀ j : Fin g.fanIn, (g.inputs j).val < k + m + bound } :=
  ⟨{ op := op, fanIn := 2, arityOk := rfl,
     inputs := fun _ => w, negated := fun _ => neg },
   fun _ => by dsimp; exact hw⟩

private theorem mkConstGateP_eval {G : Nat} [NeZero m] (val : Bool) (bound : Nat)
    (wv : BitString (k + m + G)) :
    (mkConstGateP (k := k) (m := m) (G := G) val bound).val.eval wv = val := by
  unfold mkConstGateP
  split
  · rename_i hval; rw [andOr2_eval_two]; simp only
    cases wv ⟨0, by have := NeZero.ne m; omega⟩ <;> simp [hval]
  · rename_i hval; rw [andOr2_eval_two]; simp only
    cases wv ⟨0, by have := NeZero.ne m; omega⟩ <;>
      simp only [Bool.not_eq_true, ↓reduceIte, bne_self_eq_false, one_ne_zero, Bool.bne_false,
        Bool.and_true, Bool.false_eq, Bool.bne_true, Bool.not_false, Bool.and_false] at hval ⊢ <;>
      exact hval

private theorem mkIdentGateP_eval {G : Nat} (op : AONOp) (w : Fin (k + m + G)) (neg : Bool)
    (bound : Nat) (hw : w.val < k + m + bound)
    (wv : BitString (k + m + G)) :
    (mkIdentGateP (k := k) (m := m) (G := G) op w neg bound hw).val.eval wv = (neg ^^ wv w) := by
  unfold mkIdentGateP
  rw [andOr2_eval_two]; simp only
  cases op <;> cases (neg ^^ wv w) <;> simp

/-- Transform a gate by hardwiring wire 0 to constant `b`.

    The gate's two inputs are inspected. For each input referencing wire 0,
    the effective constant `b ^^ negated` is computed. The gate is then
    simplified: identity, constant, or shifted, depending on the case. -/
private def restrictGateP {G : Nat} [NeZero m] (b : Bool)
    (g : Gate Basis.andOr2 ((k + 1) + m + G))
    (hfanIn : g.fanIn = 2)
    (bound : Nat)
    (hbound : ∀ j : Fin g.fanIn, (g.inputs j).val < (k + 1) + m + bound) :
    { g' : Gate Basis.andOr2 (k + m + G) //
      ∀ j : Fin g'.fanIn, (g'.inputs j).val < k + m + bound } :=
  let w0 := g.inputs ⟨0, by omega⟩
  let w1 := g.inputs ⟨1, by omega⟩
  let n0 := g.negated ⟨0, by omega⟩
  let n1 := g.negated ⟨1, by omega⟩
  let eff0 := b.xor n0
  let eff1 := b.xor n1
  have hw0_bound := hbound ⟨0, by omega⟩
  have hw1_bound := hbound ⟨1, by omega⟩
  if hw0 : w0.val = 0 then
    if hw1 : w1.val = 0 then
      let result := match g.op with
        | .and => eff0 && eff1
        | .or => eff0 || eff1
      mkConstGateP (k := k) (m := m) (G := G) result bound
    else
      let w1' : Fin (k + m + G) := ⟨w1.val - 1, by omega⟩
      have hw1'_bound : w1'.val < k + m + bound := by simp [w1']; omega
      match g.op with
      | .and =>
        if eff0 then mkIdentGateP .and w1' n1 bound hw1'_bound
        else mkConstGateP (k := k) (m := m) (G := G) false bound
      | .or =>
        if eff0 then mkConstGateP (k := k) (m := m) (G := G) true bound
        else mkIdentGateP .or w1' n1 bound hw1'_bound
  else
    if hw1 : w1.val = 0 then
      let w0' : Fin (k + m + G) := ⟨w0.val - 1, by omega⟩
      have hw0'_bound : w0'.val < k + m + bound := by simp [w0']; omega
      match g.op with
      | .and =>
        if eff1 then mkIdentGateP .and w0' n0 bound hw0'_bound
        else mkConstGateP (k := k) (m := m) (G := G) false bound
      | .or =>
        if eff1 then mkConstGateP (k := k) (m := m) (G := G) true bound
        else mkIdentGateP .or w0' n0 bound hw0'_bound
    else
      ⟨{ op := g.op, fanIn := 2, arityOk := rfl,
         inputs := fun i => if i.val = 0 then ⟨w0.val - 1, by omega⟩
                             else ⟨w1.val - 1, by omega⟩,
         negated := fun i => if i.val = 0 then n0 else n1 },
       fun j => by simp only; split_ifs <;> simp <;> omega⟩

/-! ## Restricted circuit -/

/-- The restricted circuit: same gate count, with each gate transformed
    by `restrictGateP` to account for the hardwired first input. -/
def restrictCircuit {G : Nat} [NeZero m] (b : Bool)
    (c : Circuit Basis.andOr2 ((k + 1) + m) 1 G) :
    Circuit Basis.andOr2 (k + m) 1 G where
  gates i := (restrictGateP (k := k) (m := m) b (c.gates i) (andOr2_fanIn (c.gates i))
    i.val (fun j => c.acyclic i j)).val
  outputs j := (restrictGateP (k := k) (m := m) b (c.outputs j) (andOr2_fanIn (c.outputs j))
    G (fun j' => by have := ((c.outputs j).inputs j').isLt; omega)).val
  acyclic i := (restrictGateP (k := k) (m := m) b (c.gates i) (andOr2_fanIn (c.gates i))
    i.val (fun j => c.acyclic i j)).property

/-! ## Correctness of restriction -/

/-- The restricted gate evaluates identically to the original gate,
    given that wire 0 maps to `b` and all other wires shift down by 1. -/
private theorem restrictGateP_eval_eq {G : Nat} [NeZero m]
    (b : Bool) (g : Gate Basis.andOr2 ((k + 1) + m + G))
    (hfanIn : g.fanIn = 2)
    (bound : Nat) (hboundG : bound ≤ G)
    (hbound : ∀ j : Fin g.fanIn, (g.inputs j).val < (k + 1) + m + bound)
    (wvOld : BitString ((k + 1) + m + G))
    (wvNew : BitString (k + m + G))
    (hwv0 : wvOld ⟨0, by omega⟩ = b)
    (hwv : ∀ (i : Nat), (hi : i < (k + 1) + m + bound) → (hip : 0 < i) →
      wvOld ⟨i, by omega⟩ = wvNew ⟨i - 1, by omega⟩) :
    g.eval wvOld =
    (restrictGateP (k := k) (m := m) b g hfanIn bound hbound).val.eval wvNew := by
  set w0 := g.inputs ⟨0, by omega⟩ with hw0_def
  set w1 := g.inputs ⟨1, by omega⟩ with hw1_def
  set n0 := g.negated ⟨0, by omega⟩ with hn0_def
  set n1 := g.negated ⟨1, by omega⟩ with hn1_def
  have hwv0' : ∀ (w : Fin ((k+1)+m+G)), w.val = 0 → wvOld w = b := by
    intro w hw; rw [show w = ⟨0, by omega⟩ from Fin.ext hw]; exact hwv0
  have hwvS : ∀ (w : Fin ((k+1)+m+G)), w.val ≠ 0 → w.val < (k+1)+m+bound →
      wvOld w = wvNew ⟨w.val - 1, by have := w.isLt; have := NeZero.ne m; omega⟩ := by
    intro w hw hlt; exact hwv w.val hlt (by omega)
  rw [andOr2_eval_two g wvOld]
  unfold restrictGateP
  simp only [← hw0_def, ← hw1_def, ← hn0_def, ← hn1_def]
  by_cases hw0 : w0.val = 0 <;> by_cases hw1 : w1.val = 0 <;>
    simp only [hw0, hw1, dite_true, dite_false]
  · rw [hwv0' w0 hw0, hwv0' w1 hw1, mkConstGateP_eval]
    cases b <;> cases n0 <;> cases n1 <;> cases g.op <;> rfl
  · rw [hwv0' w0 hw0, hwvS w1 hw1 (hbound ⟨1, by omega⟩)]
    cases b <;> cases n0 <;> cases n1 <;> cases g.op <;>
      simp (config := { decide := true }) [mkIdentGateP_eval, mkConstGateP_eval]
  · rw [hwvS w0 hw0 (hbound ⟨0, by omega⟩), hwv0' w1 hw1]
    cases b <;> cases n0 <;> cases n1 <;> cases g.op <;>
      simp (config := { decide := true }) [mkIdentGateP_eval, mkConstGateP_eval]
  · rw [hwvS w0 hw0 (hbound ⟨0, by omega⟩), hwvS w1 hw1 (hbound ⟨1, by omega⟩)]
    rw [andOr2_eval_two]
    cases g.op <;> simp (config := { decide := true })

/-- The input to the old circuit obtained by prepending `b` to `x`. -/
private def prependInput (b : Bool) (x : BitString (k + m)) :
    BitString ((k + 1) + m) :=
  fun i => if h : i.val = 0 then b else x ⟨i.val - 1, by omega⟩

private theorem wireValue_zero {G : Nat} [NeZero m] (b : Bool)
    (c : Circuit Basis.andOr2 ((k + 1) + m) 1 G)
    (x : BitString (k + m)) :
    c.wireValue (prependInput b x) ⟨0, by omega⟩ = b := by
  rw [Circuit.wireValue_lt _ _ _ (by change 0 < (k + 1) + m; omega)]
  simp [prependInput]

/-- Wire value correspondence: for wires > 0, the old circuit's wire value
    with prepended input equals the restricted circuit's shifted wire value. -/
private theorem wireValue_restrict {G : Nat} [NeZero m] (b : Bool)
    (c : Circuit Basis.andOr2 ((k + 1) + m) 1 G)
    (x : BitString (k + m))
    (w : Nat) (hwlt : w < (k + 1) + m + G)
    (hw : 0 < w) :
    c.wireValue (prependInput b x) ⟨w, hwlt⟩ =
      (restrictCircuit (k := k) b c).wireValue x ⟨w - 1, by omega⟩ := by
  induction w using Nat.strongRecOn with
  | _ w ih =>
    by_cases hwN : w < (k + 1) + m
    · rw [Circuit.wireValue_lt _ _ _ (show (⟨w, hwlt⟩ : Fin _).val < (k + 1) + m by simp; omega)]
      rw [Circuit.wireValue_lt _ _ _
        (show (⟨w - 1, (by omega)⟩ : Fin _).val < k + m by simp; omega)]
      simp only [prependInput, show ¬ (w = 0) from by omega, dite_false]
    · push Not at hwN
      rw [Circuit.wireValue_ge _ _ _ (show ¬ (⟨w, hwlt⟩ : Fin _).val < (k + 1) + m by simp; omega)]
      rw [Circuit.wireValue_ge _ _ _
        (show ¬ (⟨w - 1, (by omega)⟩ : Fin _).val < k + m by simp; omega)]
      simp only [restrictCircuit]
      have hidx : w - 1 - (k + m) = w - (k + 1 + m) := by omega
      have hg_eq : (⟨w - 1 - (k + m), by omega⟩ : Fin G) = ⟨w - (k + 1 + m), by omega⟩ := by
        ext; exact hidx
      simp only [hg_eq]
      apply restrictGateP_eval_eq b (c.gates ⟨w-(k+1+m), by omega⟩) (andOr2_fanIn _)
        (w-1-(k+m)) (by omega)
        (fun j => by have := c.acyclic ⟨w-(k+1+m), by omega⟩ j; simp at this; omega)
        (c.wireValue (prependInput b x)) _ (wireValue_zero b c x)
      intro i hi hip
      exact ih i (by omega) (by omega) hip

/-- The restricted circuit computes `restrictFirst f b`. -/
theorem restrictCircuit_eval {G : Nat} [NeZero m] (b : Bool)
    (c : Circuit Basis.andOr2 ((k + 1) + m) 1 G)
    (f : BitString ((k + 1) + m) → Bool)
    (heval : (fun x => (c.eval x) 0) = f) :
    (fun x => ((restrictCircuit (k := k) b c).eval x) 0) = restrictFirst f b := by
  funext x
  have hrhs : restrictFirst f b x = f (prependInput b x) := rfl
  rw [hrhs, ← heval]
  simp only [Circuit.eval, restrictCircuit]
  symm
  apply restrictGateP_eval_eq b (c.outputs 0) (andOr2_fanIn _) G (le_refl G)
    (fun j => by have := ((c.outputs 0).inputs j).isLt; omega)
    (c.wireValue (prependInput b x)) ((restrictCircuit b c).wireValue x)
    (wireValue_zero b c x)
  intro i hi hip
  have := wireValue_restrict b c x i (by omega) hip
  convert this using 2

end CircuitComplexity
