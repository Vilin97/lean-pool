/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SemanticQuadratic

/-!
# Quadratic-circuit boundary

This file isolates the exact algebraic content needed from the standard
quadratic-circuit flattening theorem.  Everything after the definition of
`QuadraticFlattenable` is internal: target computation is pushed through the
quadratic coefficient projection, and the eight-form Hankel obstruction then
rules out a flattening with eight products.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The span of the quadratic projections of the eight gate outputs. -/
def projectedGateSpan (C : Circuit 8 8) : Submodule F₂ TwoForm :=
  Submodule.span F₂ (Set.range fun i => anfTwoProjection (C.gate i))

/-- Computing all seven multiplication coordinates forces their alternating
two-form target space into the span of the projected gate outputs. -/
theorem targetTwoSpace_le_projectedGateSpan (C : Circuit 8 8)
    (hC : C.Computes (Mul 4)) :
    targetTwoSpace ≤ projectedGateSpan C := by
  have htarget : mulTarget 4 ≤ C.finalWire := by
    rw [mulTarget, Submodule.span_le]
    rintro p ⟨s, rfl⟩
    exact hC s
  have hmap := C.map_finalWire_eq_span anfTwoProjection
    anfTwoProjection_kills_affine
  rintro q ⟨c, rfl⟩
  change targetTwo c ∈ projectedGateSpan C
  rw [← anfTwoProjection_targetANF]
  rw [projectedGateSpan, ← hmap]
  exact ⟨targetANF c, htarget (targetANF_mem_mulTarget c), rfl⟩

/-- A semantic quadratic flattening certificate: the projected span of the
original gates has a generating family of eight decomposable two-forms.

The classical Boyar--Find equivalence says that a circuit all of whose gates
have degree at most two has such a certificate.  Naming the certificate keeps
that transformation boundary explicit for the axiom audit. -/
def QuadraticFlattenable (C : Circuit 8 8) : Prop :=
  ∃ q : Fin 8 → TwoForm,
    (∀ i, IsDecomposableTwo (q i)) ∧
    projectedGateSpan C ≤ decomposableTwoSpan q

/-- Retain a gate projection when it is decomposable, and otherwise return zero. -/
noncomputable def flattenGenerator (C : Circuit 8 8) (i : Fin 8) : TwoForm := by
  classical
  exact if IsDecomposableTwo (anfTwoProjection (C.gate i)) then
      anfTwoProjection (C.gate i)
    else 0

theorem flattenGenerator_decomposable (C : Circuit 8 8) (i : Fin 8) :
    IsDecomposableTwo (flattenGenerator C i) := by
  classical
  unfold flattenGenerator
  split_ifs with h
  · exact h
  · refine ⟨0, 0, ?_⟩
    funext a b
    simp [vectorWedge]

theorem projection_mem_of_mem_wire
    (C : Circuit 8 8) (j : Nat) (S : Submodule F₂ TwoForm)
    (hprev : ∀ i : Fin 8, i.val < j →
      anfTwoProjection (C.gate i) ∈ S)
    {p : ANF 8} (hp : p ∈ wireSpace C.gate j) :
    anfTwoProjection p ∈ S := by
  rw [wireSpace] at hp
  rcases Submodule.mem_sup.mp hp with ⟨a, ha, w, hw, rfl⟩
  rw [map_add, anfTwoProjection_kills_affine ha, zero_add]
  refine Submodule.span_induction (p := fun w _ => anfTwoProjection w ∈ S)
    ?_ ?_ ?_ ?_ hw
  · intro z hz
    rcases hz with ⟨i, hi, rfl⟩
    exact hprev i hi
  · simp
  · intro x y _ _ hx hy
    simpa using Submodule.add_mem S hx hy
  · intro k x _ hx
    simpa using Submodule.smul_mem S k hx

theorem gate_projection_alternative (C : Circuit 8 8)
    (hall : ∀ i : Fin 8, C.gate i ∈ quadraticANFSpace 8)
    (i : Fin 8) :
    anfTwoProjection (C.gate i) ∈
        Submodule.span F₂
          {anfTwoProjection (C.left i), anfTwoProjection (C.right i)} ∨
      IsDecomposableTwo (anfTwoProjection (C.gate i)) := by
  have hwire : wireSpace C.gate i.val ≤ quadraticANFSpace 8 :=
    wireSpace_le_quadratic_of_prefix C.gate (fun k _ => hall k)
  exact quadratic_product_projection_alternative (C.gate_eq i)
    (hwire (C.left_mem i)) (hwire (C.right_mem i)) (hall i)

theorem projected_gate_mem_flatten_span
    (C : Circuit 8 8)
    (hall : ∀ i : Fin 8, C.gate i ∈ quadraticANFSpace 8)
    (i : Fin 8) :
    anfTwoProjection (C.gate i) ∈ decomposableTwoSpan (flattenGenerator C) := by
  classical
  let S := decomposableTwoSpan (flattenGenerator C)
  have hstrong : ∀ k : Nat, ∀ hk : k < 8,
      anfTwoProjection (C.gate ⟨k, hk⟩) ∈ S := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        let j : Fin 8 := ⟨k, hk⟩
        by_cases hdec : IsDecomposableTwo (anfTwoProjection (C.gate j))
        · apply Submodule.subset_span
          refine ⟨j, ?_⟩
          simp [j, flattenGenerator, hdec]
        · rcases gate_projection_alternative C hall j with hspan | hdec'
          · apply (Submodule.span_le.mpr ?_) hspan
            intro z hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rcases hz with rfl | rfl
            · exact projection_mem_of_mem_wire C k S
                (fun a ha => ih a ha a.isLt) (C.left_mem j)
            · exact projection_mem_of_mem_wire C k S
                (fun a ha => ih a ha a.isLt) (C.right_mem j)
          · exact (hdec hdec').elim
  exact hstrong i.val i.isLt

theorem quadratic_flattenable_of_all_gates_quadratic (C : Circuit 8 8)
    (hall : ∀ i : Fin 8, C.gate i ∈ quadraticANFSpace 8) :
    QuadraticFlattenable C := by
  refine ⟨flattenGenerator C, flattenGenerator_decomposable C, ?_⟩
  rw [projectedGateSpan, Submodule.span_le]
  rintro q ⟨i, rfl⟩
  exact projected_gate_mem_flatten_span C hall i

theorem no_quadratic_flattening_of_computes (C : Circuit 8 8)
    (hC : C.Computes (Mul 4)) : ¬ QuadraticFlattenable C := by
  rintro ⟨q, hdec, hspan⟩
  exact no_eight_decomposable_span q hdec
    ((targetTwoSpace_le_projectedGateSpan C hC).trans hspan)

/-- The normalized seed has a nonzero degree-at-least-three component. -/
theorem normalized_seed_high
    {C : Circuit 8 8} (hNorm : NormalizedEight C) :
    SeedHighNonzero C := by
  by_contra hseed
  have hall := normalized_all_gates_quadratic_of_seed_not_high hNorm hseed
  exact no_quadratic_flattening_of_computes C hNorm.computes
    (quadratic_flattenable_of_all_gates_quadratic C hall)

end

end N4
end UnrestrictedBooleanMul
