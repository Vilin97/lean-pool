/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.Exterior

/-!
# Decomposable target geometry

This file connects products of linear forms to the Hankel classification.  The
key argument is symbolic: the absence of `A ∧ A` terms makes the two `A`-side
vectors dependent, so the cross block is an outer product and every Hankel
minor vanishes.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Coordinate of an input coefficient in the first polynomial. -/
@[expose] def aCoord (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩
/-- Coordinate of an input coefficient in the second polynomial. -/
@[expose] def bCoord (j : Fin 4) : Fin 8 := ⟨4 + j.val, by omega⟩

/-- Restrict a linear form to the first polynomial input. -/
@[expose] def aPart (u : LinearForm) : Fin 4 → F₂ := fun i => u (aCoord i)
/-- Restrict a linear form to the second polynomial input. -/
@[expose] def bPart (u : LinearForm) : Fin 4 → F₂ := fun j => u (bCoord j)

/-- The mixed input coordinates of the exterior product of two linear forms. -/
@[expose] def crossPart (u v : LinearForm) (i j : Fin 4) : F₂ :=
  vectorWedge u v (aCoord i) (bCoord j)

/-- A target coefficient word is decomposable when it is the quadratic cross
part of two linear forms and their same-side exterior components vanish. -/
@[expose]
def IsDecomposableTarget (c : TargetCoeff) : Prop :=
  ∃ u v : LinearForm,
    (∀ i j : Fin 4, vectorWedge u v (aCoord i) (aCoord j) = 0) ∧
    (∀ i j : Fin 4, vectorWedge u v (bCoord i) (bCoord j) = 0) ∧
    (∀ i j : Fin 4, c ⟨i.val + j.val, by omega⟩ = crossPart u v i j)

/-- A decomposable target has Hankel rank at most one. -/
theorem decomposableTarget_rankOne {c : TargetCoeff}
    (h : IsDecomposableTarget c) : HankelRankLEOne c := by
  rcases h with ⟨u, v, hAA, _hBB, hcross⟩
  have hApart : ∀ i j : Fin 4,
      aPart u i * aPart v j + aPart u j * aPart v i = 0 := by
    intro i j
    simpa [aPart, vectorWedge] using hAA i j
  rcases dependent_of_vectorWedge_zero (aPart u) (aPart v) hApart with hu | hv | huv
  · intro i k j l
    simp only [hankelMatrix]
    rw [hcross i j, hcross k l, hcross i l, hcross k j]
    have hui : u (aCoord i) = 0 := congrFun hu i
    have huk : u (aCoord k) = 0 := congrFun hu k
    simp [crossPart, vectorWedge, hui, huk]
    ring
  · intro i k j l
    simp only [hankelMatrix]
    rw [hcross i j, hcross k l, hcross i l, hcross k j]
    have hvi : v (aCoord i) = 0 := congrFun hv i
    have hvk : v (aCoord k) = 0 := congrFun hv k
    simp [crossPart, vectorWedge, hvi, hvk]
    ring
  · intro i k j l
    simp only [hankelMatrix]
    rw [hcross i j, hcross k l, hcross i l, hcross k j]
    have hui : u (aCoord i) = v (aCoord i) := congrFun huv i
    have huk : u (aCoord k) = v (aCoord k) := congrFun huv k
    simp only [crossPart, vectorWedge, hui, huk]
    ring

/-- Rank-one target geometry in the form consumed by the prefix theorem. -/
theorem decomposableTarget_classification {c : TargetCoeff}
    (hdec : IsDecomposableTarget c) (hc : c ≠ 0) :
    c = rZeroCoeff ∨ c = rOneCoeff ∨ c = rInfinityCoeff :=
  rankOne_target_classification (decomposableTarget_rankOne hdec) hc

/-- Represent a linear combination of evaluations at zero, one, and infinity. -/
@[expose] def rationalCoeffRep (α : Fin 3 → F₂) : TargetCoeff :=
  α 0 • rZeroCoeff + α 1 • rOneCoeff + α 2 • rInfinityCoeff

theorem rationalCoeffRep_mem (α : Fin 3 → F₂) :
    rationalCoeffRep α ∈ rationalCoeffSpace := by
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_insert _ _))
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · exact Submodule.smul_mem _ _
      (Submodule.subset_span
        (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

theorem rationalCoeffRep_injective : Function.Injective rationalCoeffRep := by
  intro α β h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  have h6 := congrFun h 6
  simp only [rationalCoeffRep, Fin.isValue, rZeroCoeff, Matrix.smul_cons, smul_eq_mul,
    mul_one, mul_zero, Matrix.smul_empty, rOneCoeff, Matrix.add_cons, Matrix.head_cons,
    Matrix.tail_cons, zero_add, Matrix.empty_add_empty, rInfinityCoeff, Pi.add_apply,
    Matrix.cons_val_zero, add_zero, Matrix.cons_val] at h0 h2 h6
  funext i
  fin_cases i
  · rw [h2] at h0
    exact add_right_cancel h0
  · exact h2
  · rw [h2] at h6
    exact add_left_cancel h6

theorem IsRationalCoeff_iff (c : TargetCoeff) :
    IsRationalCoeff c ↔ ∃ α : Fin 3 → F₂, c = rationalCoeffRep α := by
  constructor
  · rintro ⟨α, β, γ, rfl⟩
    exact ⟨![α, β, γ], by simp [rationalCoeffRep]⟩
  · rintro ⟨α, rfl⟩
    exact ⟨α 0, α 1, α 2, rfl⟩

end

end N4
end UnrestrictedBooleanMul
