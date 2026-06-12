/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import LeanPool.CircuitComplexity.EssentialInput
import LeanPool.CircuitComplexity.AON.Defs

/-! # Internal: Gate Elimination Lower Bound

This internal module proves the gate elimination lower bound: for any circuit
over a bounded fan-in k AND/OR basis, if the computed function depends on n'
essential variables, the circuit has size at least ⌈n'/k⌉.

The public definitions (`IsEssentialInput`, `EssentialInputs`) are in
`Circ.EssentialInput`. The public theorems (`gate_elimination_lower_bound`,
`lower_bound_all_inputs`) are accessible through `Circ.LowerBound`.
-/

namespace CircuitComplexity


namespace Circuit
variable {B : Basis} {N M G : Nat} [NeZero N] [NeZero M]

/-! ## Core insensitivity lemma -/

/-- If no internal gate reads primary input `i`, wire values at wires
    other than `i` are unchanged when input `i` is modified. -/
theorem wireValue_eq_of_unreferenced
    (c : Circuit B N M G) (i : Fin N) (b : Bool)
    (hno : ∀ g : Fin G, ∀ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val ≠ i.val)
    (x : BitString N) (w : Fin (N + G)) (hw : w.val ≠ i.val) :
    c.wireValue x w = c.wireValue (Function.update x i b) w := by
  by_cases h : w.val < N
  · -- Primary input wire, not wire i
    rw [wireValue_lt c x w h, wireValue_lt c _ w h]
    have hne : (⟨w.val, h⟩ : Fin N) ≠ i := fun heq => hw (congrArg Fin.val heq)
    exact (Function.update_of_ne hne b x).symm
  · -- Gate output wire: recurse on fan-in wires
    have hG : w.val - N < G := by omega
    rw [wireValue_ge c x w h, wireValue_ge c _ w h]
    simp only [Gate.eval]
    congr 1; funext k; congr 1
    exact wireValue_eq_of_unreferenced c i b hno x _ (hno ⟨w.val - N, hG⟩ k)
termination_by w.val
decreasing_by
  have hacyc := c.acyclic ⟨w.val - N, hG⟩ k
  have : (⟨w.val - N, hG⟩ : Fin G).val = w.val - N := rfl
  omega

/-- If no gate (internal or output) reads primary input `i`, the circuit
    output is unchanged when input `i` is modified. -/
theorem eval_eq_of_unreferenced
    (c : Circuit B N M G) (i : Fin N) (b : Bool)
    (hno_gates : ∀ g : Fin G, ∀ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val ≠ i.val)
    (hno_outputs : ∀ j : Fin M, ∀ k : Fin (c.outputs j).fanIn,
      ((c.outputs j).inputs k).val ≠ i.val)
    (x : BitString N) :
    c.eval x = c.eval (Function.update x i b) := by
  funext j; simp only [eval, Gate.eval]
  congr 1; funext k; congr 1
  exact wireValue_eq_of_unreferenced c i b hno_gates x _ (hno_outputs j k)

/-! ## Essential variables must be read -/

/-- If `c` computes `f` and `f` depends on variable `i`, some gate
    (internal or output) directly reads input wire `i`. -/
theorem exists_gate_reads_input
    (c : Circuit B N M G) (f : BitString N → BitString M)
    (hf : c.eval = f) (i : Fin N) (hdep : IsEssentialInput f i) :
    (∃ g : Fin G, ∃ k : Fin (c.gates g).fanIn,
      ((c.gates g).inputs k).val = i.val) ∨
    (∃ j : Fin M, ∃ k : Fin (c.outputs j).fanIn,
      ((c.outputs j).inputs k).val = i.val) := by
  by_contra h
  push Not at h
  obtain ⟨hg, ho⟩ := h
  obtain ⟨x, hx⟩ := hdep
  exact hx (hf ▸ eval_eq_of_unreferenced c i _ hg ho x)

/-! ## Counting argument -/

/-- The set of primary inputs directly wired into a gate. -/
def coveredInputs (g : Gate B (N + G)) : Finset (Fin N) :=
  Finset.univ.filter fun i : Fin N =>
    ∃ k : Fin g.fanIn, (g.inputs k).val = i.val

omit [NeZero N] in
theorem mem_coveredInputs (g : Gate B (N + G)) (i : Fin N) :
    i ∈ coveredInputs g ↔ ∃ k : Fin g.fanIn, (g.inputs k).val = i.val := by
  simp [coveredInputs]

theorem card_coveredInputs_le (g : Gate B (N + G)) :
    (coveredInputs g : Finset (Fin N)).card ≤ g.fanIn := by
  -- coveredInputs is contained in the image of a map from Fin g.fanIn
  suffices coveredInputs g ⊆
      (Finset.univ : Finset (Fin g.fanIn)).image
        (fun k => if h : (g.inputs k).val < N
          then ⟨(g.inputs k).val, h⟩
          else ⟨0, NeZero.pos N⟩) by
    calc (coveredInputs g).card
        ≤ _ := Finset.card_le_card this
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = g.fanIn := by simp
  intro i hi
  rw [mem_coveredInputs] at hi
  obtain ⟨k, hk⟩ := hi
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  refine ⟨k, ?_⟩
  have hlt : (g.inputs k).val < N := by omega
  simp [hk]

/-- For a gate over bounded fan-in k AON basis, covered inputs has card ≤ k. -/
theorem boundedAON_coveredInputs_card_le {k : Nat}
    (g : Gate (Basis.boundedAON k) (N + G)) :
    (coveredInputs g : Finset (Fin N)).card ≤ k := by
  have hfanIn : g.fanIn ≤ k := by
    have h := g.arityOk
    revert h; cases g.op <;> simp [Basis.boundedAON, Arity.satisfiedBy]
  exact le_trans (card_coveredInputs_le g) hfanIn

/-- Gate accessor for internal and output gates uniformly. -/
private def gateAt (c : Circuit B N M G) : Fin G ⊕ Fin M → Gate B (N + G)
  | .inl g => c.gates g
  | .inr j => c.outputs j

/-- Every essential variable is covered by some gate. -/
private theorem essential_subset_covered
    (c : Circuit B N M G) (f : BitString N → BitString M)
    (hf : c.eval = f) :
    EssentialInputs f ⊆ (Finset.univ : Finset (Fin G ⊕ Fin M)).biUnion
      (fun idx => coveredInputs (gateAt c idx)) := by
  intro i hi
  simp only [EssentialInputs, Finset.mem_filter] at hi
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  rcases exists_gate_reads_input c f hf i hi.2 with ⟨g, k, hk⟩ | ⟨j, k, hk⟩
  · exact ⟨.inl g, (mem_coveredInputs _ _).mpr ⟨k, hk⟩⟩
  · exact ⟨.inr j, (mem_coveredInputs _ _).mpr ⟨k, hk⟩⟩

/-- **Counting bound**: for bounded fan-in k, the number of essential
    variables is at most k times the circuit size. -/
theorem essential_inputs_le_mul_size {k : Nat}
    (c : Circuit (Basis.boundedAON k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f) :
    (EssentialInputs f).card ≤ k * c.size := by
  calc (EssentialInputs f).card
      ≤ ((Finset.univ : Finset (Fin G ⊕ Fin M)).biUnion
          (fun idx => coveredInputs (gateAt c idx))).card :=
        Finset.card_le_card (essential_subset_covered c f hf)
    _ ≤ ∑ idx : Fin G ⊕ Fin M,
          (coveredInputs (gateAt c idx)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _ : Fin G ⊕ Fin M, k :=
        Finset.sum_le_sum fun idx _ => boundedAON_coveredInputs_card_le _
    _ = (Fintype.card (Fin G ⊕ Fin M)) * k := by
        rw [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]
    _ = k * c.size := by
        simp [Fintype.card_sum, Fintype.card_fin, size, Nat.mul_comm]

/-- **Gate elimination lower bound**: for fan-in k, circuit size is at
    least ⌈n'/k⌉ where n' is the number of essential variables. -/
theorem gate_elimination_lower_bound {k : Nat}
    (c : Circuit (Basis.boundedAON k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f) :
    (EssentialInputs f).card ≤ k * c.size :=
  essential_inputs_le_mul_size c f hf

/-- Corollary: if `f` depends on all N inputs, then N ≤ k · size. -/
theorem lower_bound_all_inputs {k : Nat}
    (c : Circuit (Basis.boundedAON k) N M G)
    (f : BitString N → BitString M)
    (hf : c.eval = f)
    (hall : ∀ i : Fin N, IsEssentialInput f i) :
    N ≤ k * c.size := by
  have hcard : (EssentialInputs f).card = N := by
    have : EssentialInputs f = Finset.univ := by
      simp [EssentialInputs, Finset.filter_true_of_mem (fun i _ => hall i)]
    rw [this, Finset.card_univ, Fintype.card_fin]
  calc N = (EssentialInputs f).card := hcard.symm
    _ ≤ k * c.size := essential_inputs_le_mul_size c f hf

end Circuit

end CircuitComplexity
