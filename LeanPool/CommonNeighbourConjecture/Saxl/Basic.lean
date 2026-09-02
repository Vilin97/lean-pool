/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/

import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Bases and Saxl adjacency

Foundational definitions for ordered tuple bases, ordinary and generalized
Saxl adjacency, exact base size, and common neighbours.
-/

namespace Saxl

variable (G Ω : Type*) [Group G] [MulAction G Ω]

/-- An ordered tuple whose pointwise stabilizer in `G` is trivial. -/
def IsBaseTuple {n : Nat} (x : Fin n → Ω) : Prop :=
  ∀ g : G, (∀ i, g • x i = x i) → g = 1

/-- An injective ordered tuple corresponding literally to a base as a set. -/
def IsSetBaseTuple {n : Nat} (x : Fin n → Ω) : Prop :=
  Function.Injective x ∧ IsBaseTuple G Ω x

/-- Base-two adjacency: the displayed ordered pair has trivial stabilizer. -/
def Adjacent (x y : Ω) : Prop :=
  IsBaseTuple G Ω (Fin.cons x (Fin.cons y Fin.elim0))

/-- Two vertices extend to an injective base of size `tail + 2`. -/
def GeneralizedAdjacent (tail : Nat) (x y : Ω) : Prop :=
  ∃ z : Fin tail → Ω,
    IsSetBaseTuple G Ω (Fin.cons x (Fin.cons y z))

/-- Two vertices have a common neighbour for a relation `R`. -/
def HasCommonNeighbour (R : Ω → Ω → Prop) (x y : Ω) : Prop :=
  ∃ z, R x z ∧ R z y

/-- Exact base size `n`, stated without a global minimum operator. -/
def ExactBaseSize (n : Nat) : Prop :=
  (∃ x : Fin n → Ω, IsSetBaseTuple G Ω x) ∧
    ∀ m < n, ¬ ∃ x : Fin m → Ω, IsSetBaseTuple G Ω x

/-- The pointwise stabilizer of all entries of an ordered tuple. -/
def tupleStabilizer {n : Nat} (x : Fin n → Ω) : Subgroup G :=
  ⨅ i, MulAction.stabilizer G (x i)

@[simp]
theorem mem_tupleStabilizer_iff {n : Nat} (x : Fin n → Ω) (g : G) :
    g ∈ tupleStabilizer G Ω x ↔ ∀ i, g • x i = x i := by
  simp [tupleStabilizer, MulAction.mem_stabilizer_iff]

/-- A tuple is a base exactly when its pointwise stabilizer is trivial. -/
theorem isBaseTuple_iff_tupleStabilizer_eq_bot {n : Nat} (x : Fin n → Ω) :
    IsBaseTuple G Ω x ↔ tupleStabilizer G Ω x = ⊥ := by
  simp [IsBaseTuple, Subgroup.eq_bot_iff_forall]

/-- The stabilizer characterization of ordinary Saxl adjacency. -/
theorem adjacent_iff_pair_stabilizer_eq_bot (x y : Ω) :
    Adjacent G Ω x y ↔
      MulAction.stabilizer G x ⊓ MulAction.stabilizer G y = ⊥ := by
  simp [Adjacent, IsBaseTuple, Fin.forall_fin_two, Subgroup.eq_bot_iff_forall,
    MulAction.mem_stabilizer_iff]

/-- A one-entry tuple is a base exactly when that point has trivial stabilizer. -/
theorem isBaseTuple_singleton_iff_stabilizer_eq_bot (x : Ω) :
    IsBaseTuple G Ω (fun _ : Fin 1 ↦ x) ↔ MulAction.stabilizer G x = ⊥ := by
  simp [IsBaseTuple, Subgroup.eq_bot_iff_forall, MulAction.mem_stabilizer_iff]

/-- Exact set-base size two means that a distinct adjacent pair exists, but no
single point has trivial stabilizer. -/
theorem exactBaseSize_two_iff :
    ExactBaseSize G Ω 2 ↔
      (∃ x y : Ω, x ≠ y ∧ Adjacent G Ω x y) ∧
        ∀ x : Ω, MulAction.stabilizer G x ≠ ⊥ := by
  constructor
  · rintro ⟨⟨b, hb⟩, hminimal⟩
    refine ⟨⟨b 0, b 1, hb.1.ne (by decide), ?_⟩, ?_⟩
    · simpa [Adjacent, IsBaseTuple, Fin.forall_fin_two] using hb.2
    · intro x hx
      apply hminimal 1 (by decide)
      refine ⟨fun _ ↦ x, ?_, (isBaseTuple_singleton_iff_stabilizer_eq_bot G Ω x).2 hx⟩
      intro i j _
      exact Subsingleton.elim i j
  · rintro ⟨⟨x, y, hxy, hbase⟩, hnontrivial⟩
    refine ⟨?_, ?_⟩
    · refine ⟨Fin.cons x (Fin.cons y Fin.elim0), ?_, hbase⟩
      simpa [Fin.cons_injective_iff, Function.Injective] using
        (And.intro hxy hxy.symm)
    · intro m hm
      cases m with
      | zero =>
          rintro ⟨b, hb⟩
          apply hnontrivial x
          apply (Subgroup.eq_bot_iff_forall _).2
          intro g _
          exact hb.2 g (fun i ↦ Fin.elim0 i)
      | succ m =>
          cases m with
          | zero =>
              rintro ⟨b, hb⟩
              apply hnontrivial (b 0)
              apply (isBaseTuple_singleton_iff_stabilizer_eq_bot G Ω (b 0)).1
              have hb_eq : b = fun _ : Fin 1 ↦ b 0 := by
                funext i
                rw [Fin.eq_zero i]
              exact hb_eq ▸ hb.2
          | succ m =>
              exact False.elim
                ((Nat.not_lt_of_ge
                  (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m)))) hm)

/-- To rule out a common neighbour it suffices to rule out every possible
witness, one vertex at a time. -/
theorem noCommonNeighbour {R : Ω → Ω → Prop} {x y : Ω}
    (h : ∀ z, R x z → R z y → False) :
    ¬ HasCommonNeighbour Ω R x y := by
  rintro ⟨z, hxz, hzy⟩
  exact h z hxz hzy

end Saxl
