/-
Copyright (c) 2026 Tom Adamczewski and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import LeanPool.Koethe.Pencil

/-!
# Finite homogeneous-linear systems

A system has a distinguished input, finitely many internal states, and an output
row. Its coefficients are linear combinations of the three generators, with no
scalar/identity edges. `Represents` is the elimination property of the internal
system. We construct this property directly, without needing a matrix inverse
or a nilpotence assumption on the ambient algebra.
-/

noncomputable section

open scoped BigOperators

namespace KoetheCounterexample
namespace Linearization

universe u v

variable {k : Type u} [Field k] {R : Type v} [Ring R] [Algebra k R]

/-- Evaluate one homogeneous-linear edge, as a constant polynomial. -/
def edge (a : Fin 3 → R) (c : Triple k) : Polynomial R :=
  Polynomial.C (∑ i : Fin 3, algebraMap k R (c i) * a i)

@[simp] theorem edge_zero (a : Fin 3 → R) : edge a (0 : Triple k) = 0 := by
  simp [edge]

@[simp] theorem edge_add (a : Fin 3 → R) (c d : Triple k) :
    edge a (c + d) = edge a c + edge a d := by
  simp [edge, add_mul, Finset.sum_add_distrib]

@[simp] theorem edge_smul (a : Fin 3 → R) (r : k) (c : Triple k) :
    edge a (r • c) = Polynomial.C (algebraMap k R r) * edge a c := by
  simp [edge, map_mul, mul_assoc, Finset.mul_sum]

/-- Coefficients selecting just one letter. -/
def letter (i : Fin 3) : Triple k := fun j => if j = i then 1 else 0

@[simp] theorem edge_letter (a : Fin 3 → R) (i : Fin 3) :
    edge a (letter (k := k) i) = Polynomial.C (a i) := by
  simp [edge, letter]

/-- A finite homogeneous-linear system. The root is not among `State`. -/
structure System (k : Type u) [Field k] where
  /-- The internal states. -/
  State : Type
  /-- The states are finitely many. -/
  fintype : Fintype State
  /-- Equality of states is decidable. -/
  decEq : DecidableEq State
  /-- The coefficient of the input in the output row. -/
  head : Triple k
  /-- The coefficient of each internal state in the output row. -/
  out : State → Triple k
  /-- The coefficient of the input in each internal equation. -/
  input : State → Triple k
  /-- The coefficient of each internal state in each internal equation. -/
  step : State → State → Triple k

attribute [instance] System.fintype System.decEq

/-- Every solution of the internal equations gives the specified output.
All equations take place in the polynomial ring over the possibly
noncommutative algebra `R`. -/
def Represents (S : System k) (a : Fin 3 → R) (x : R) : Prop :=
  ∀ (q₀ : Polynomial R) (q : S.State → Polynomial R),
    (∀ i, q i = edge a (S.input i) * q₀ +
      ∑ j, edge a (S.step i j) * q j) →
    edge a S.head * q₀ + ∑ j, edge a (S.out j) * q j =
      Polynomial.C x * q₀

/-- The elements admitting one of these finite linearizations. -/
def Linearizable (a : Fin 3 → R) (x : R) : Prop :=
  ∃ S : System k, Represents S a x

namespace System

/-- A single homogeneous-linear output, with no internal states. -/
def atom (c : Triple k) : System k where
  State := Empty
  fintype := inferInstance
  decEq := inferInstance
  head := c
  out := Empty.elim
  input := Empty.elim
  step := Empty.elim

/-- Disjoint union of systems, adding their output rows. -/
def add (S T : System k) : System k where
  State := S.State ⊕ T.State
  fintype := inferInstance
  decEq := inferInstance
  head := S.head + T.head
  out := Sum.elim S.out T.out
  input := Sum.elim S.input T.input
  step := fun i j => match i, j with
    | .inl i, .inl j => S.step i j
    | .inr i, .inr j => T.step i j
    | _, _ => 0

/-- Only the output row is scaled. -/
def smul (r : k) (S : System k) : System k where
  State := S.State
  fintype := S.fintype
  decEq := S.decEq
  head := r • S.head
  out := fun i => r • S.out i
  input := S.input
  step := S.step

/-- Prepend a generator: a new internal state computes the old output, and
one generator edge joins the new output to that state. -/
def prepend (i : Fin 3) (S : System k) : System k where
  State := Option S.State
  fintype := inferInstance
  decEq := inferInstance
  head := 0
  out := fun j => match j with
    | none => letter i
    | some _ => 0
  input := fun j => match j with
    | none => S.head
    | some j => S.input j
  step := fun j l => match j, l with
    | none, some l => S.out l
    | some j, some l => S.step j l
    | _, none => 0

/-- A sum over the (empty) state type of an atom vanishes. -/
theorem sum_atom_state {M : Type*} [AddCommMonoid M] (c : Triple k)
    (g : (atom c).State → M) : ∑ j, g j = 0 :=
  Finset.sum_eq_zero fun j _ => Empty.elim j

/-- A sum over the states of `S.add T` splits into the two summands. -/
theorem sum_add_state {M : Type*} [AddCommMonoid M] (S T : System k)
    (g : (S.add T).State → M) :
    ∑ j, g j = ∑ j, g (Sum.inl j) + ∑ j, g (Sum.inr j) :=
  Fintype.sum_sum_type g

/-- A sum over the states of `S.prepend i` isolates the new state. -/
theorem sum_prepend_state {M : Type*} [AddCommMonoid M] (i : Fin 3) (S : System k)
    (g : (S.prepend i).State → M) :
    ∑ j, g j = g none + ∑ j, g (some j) :=
  Fintype.sum_option g

end System

@[simp] theorem represents_atom (a : Fin 3 → R) (c : Triple k) :
    Represents (System.atom c) a (∑ i, algebraMap k R (c i) * a i) := by
  intro q₀ q _
  rw [System.sum_atom_state]
  simp [System.atom, edge]

theorem linearizable_zero (a : Fin 3 → R) : Linearizable (k := k) a 0 := by
  refine ⟨System.atom 0, ?_⟩
  simpa using represents_atom a (0 : Triple k)

theorem linearizable_letter (a : Fin 3 → R) (i : Fin 3) :
    Linearizable (k := k) a (a i) := by
  refine ⟨System.atom (letter i), ?_⟩
  simpa [letter] using represents_atom a (letter (k := k) i)

theorem Represents.add {S T : System k} {a : Fin 3 → R} {x y : R}
    (hS : Represents S a x) (hT : Represents T a y) :
    Represents (S.add T) a (x + y) := by
  intro q₀ q hq
  have hq' : ∀ i, q i = edge a ((S.add T).input i) * q₀ +
      (∑ j, edge a ((S.add T).step i (Sum.inl j)) * q (Sum.inl j) +
        ∑ j, edge a ((S.add T).step i (Sum.inr j)) * q (Sum.inr j)) := by
    intro i
    rw [hq i, System.sum_add_state]
  have hS' := hS q₀ (fun i => q (.inl i)) (fun i => by
    simpa [System.add] using hq' (Sum.inl i))
  have hT' := hT q₀ (fun i => q (.inr i)) (fun i => by
    simpa [System.add] using hq' (Sum.inr i))
  rw [System.sum_add_state]
  simp only [System.add, edge_add, Sum.elim_inl, Sum.elim_inr]
  calc
    (edge a S.head + edge a T.head) * q₀ +
        ((∑ j, edge a (S.out j) * q (.inl j)) +
          ∑ j, edge a (T.out j) * q (.inr j)) =
        (edge a S.head * q₀ + ∑ j, edge a (S.out j) * q (.inl j)) +
          (edge a T.head * q₀ + ∑ j, edge a (T.out j) * q (.inr j)) := by
      noncomm_ring
    _ = Polynomial.C x * q₀ + Polynomial.C y * q₀ := by rw [hS', hT']
    _ = Polynomial.C (x + y) * q₀ := by rw [map_add, add_mul]

theorem Represents.smul {S : System k} {a : Fin 3 → R} {x : R}
    (hS : Represents S a x) (r : k) :
    Represents (S.smul r) a (r • x) := by
  intro q₀ q hq
  have hS' := hS q₀ q hq
  change edge a (r • S.head) * q₀ +
      ∑ j, edge a (r • S.out j) * q j = _
  simp only [edge_smul, mul_assoc, ← Finset.mul_sum, ← mul_add]
  rw [hS', ← mul_assoc, ← map_mul, Algebra.smul_def]

theorem Represents.prepend {S : System k} {a : Fin 3 → R} {x : R}
    (hS : Represents S a x) (i : Fin 3) :
    Represents (S.prepend i) a (a i * x) := by
  intro q₀ q hq
  have hq' : ∀ j, q j = edge a ((S.prepend i).input j) * q₀ +
      (edge a ((S.prepend i).step j none) * q none +
        ∑ l, edge a ((S.prepend i).step j (some l)) * q (some l)) := by
    intro j
    rw [hq j, System.sum_prepend_state]
  have hS' := hS q₀ (fun j => q (some j)) (fun j => by
    simpa [System.prepend] using hq' (some j))
  have hn : q none = Polynomial.C x * q₀ := by
    have h := hq' none
    simp only [System.prepend, edge_zero, zero_mul, zero_add] at h
    exact h.trans hS'
  rw [System.sum_prepend_state]
  simp [System.prepend, hn, mul_assoc, map_mul]

theorem linearizable_add {a : Fin 3 → R} {x y : R}
    (hx : Linearizable (k := k) a x) (hy : Linearizable (k := k) a y) :
    Linearizable (k := k) a (x + y) := by
  obtain ⟨S, hS⟩ := hx
  obtain ⟨T, hT⟩ := hy
  exact ⟨S.add T, hS.add hT⟩

theorem linearizable_smul {a : Fin 3 → R} {x : R}
    (hx : Linearizable (k := k) a x) (r : k) : Linearizable (k := k) a (r • x) := by
  obtain ⟨S, hS⟩ := hx
  exact ⟨S.smul r, hS.smul r⟩

theorem linearizable_prepend {a : Fin 3 → R} {x : R}
    (hx : Linearizable (k := k) a x) (i : Fin 3) :
    Linearizable (k := k) a (a i * x) := by
  obtain ⟨S, hS⟩ := hx
  exact ⟨S.prepend i, hS.prepend i⟩

end Linearization
end KoetheCounterexample

end
