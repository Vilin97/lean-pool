/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.SliceExclusion

/-!
# Semantic recovery of cubic ANF coefficients

Quadratic semantic recovery is already provided by `pairPolarMap`.  The
quartic slice proof also needs the three-variable polarization identity.
The only finite certificate here is the fixed subset identity on three
indices; it contains no circuit data.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- The third finite difference at zero in three coordinate directions. -/
@[expose]
def triplePolarMap (i j k : Fin 8) : ANF 8 →ₗ[F₂] F₂ :=
  sparseEvalMap ∅ + sparseEvalMap {i} + sparseEvalMap {j} +
    sparseEvalMap {k} + sparseEvalMap {i, j} +
    sparseEvalMap {i, k} + sparseEvalMap {j, k} +
    sparseEvalMap {i, j, k}

/-- Extract the coefficient supported on the specified three variables. -/
@[expose]
def tripleCoeffMap (i j k : Fin 8) : ANF 8 →ₗ[F₂] F₂ where
  toFun p := p.coeff ⟨{i, j, k}⟩
  map_add' p q := by simp
  map_smul' a p := by simp

private theorem subset_iff_on_triple
    (s : Finset (Fin 8)) (i j k : Fin 8)
    (hs : s ⊆ {i, j, k}) (t : Finset (Fin 8)) :
    s ⊆ t ↔
      (i ∈ s → i ∈ t) ∧ (j ∈ s → j ∈ t) ∧ (k ∈ s → k ∈ t) := by
  constructor
  · intro h
    exact ⟨fun hi => h hi, fun hj => h hj, fun hk => h hk⟩
  · rintro ⟨hi, hj, hk⟩ x hx
    have hxTrip := hs hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxTrip
    rcases hxTrip with rfl | rfl | rfl
    · exact hi hx
    · exact hj hx
    · exact hk hx

private theorem eq_triple_iff_members
    (s : Finset (Fin 8)) (i j k : Fin 8)
    (hs : s ⊆ {i, j, k}) :
    s = {i, j, k} ↔ i ∈ s ∧ j ∈ s ∧ k ∈ s := by
  constructor
  · intro h
    subst s
    simp
  · rintro ⟨hi, hj, hk⟩
    apply Finset.Subset.antisymm hs
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption

/-- Möbius polarization on a three-element Boolean cube. -/
theorem subset_triple_polar_identity
    (s : Finset (Fin 8)) (i j k : Fin 8)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (if s ⊆ ∅ then (1 : F₂) else 0) +
      (if s ⊆ {i} then 1 else 0) +
      (if s ⊆ {j} then 1 else 0) +
      (if s ⊆ {k} then 1 else 0) +
      (if s ⊆ {i, j} then 1 else 0) +
      (if s ⊆ {i, k} then 1 else 0) +
      (if s ⊆ {j, k} then 1 else 0) +
      (if s ⊆ {i, j, k} then 1 else 0) =
        if s = {i, j, k} then 1 else 0 := by
  by_cases hs : s ⊆ {i, j, k}
  · simp only [subset_iff_on_triple s i j k hs, eq_triple_iff_members s i j k hs]
    by_cases hi : i ∈ s <;> by_cases hj : j ∈ s <;>
      by_cases hk : k ∈ s <;>
        simp [hi, hj, hk, hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk,] <;>
        ring_nf <;>
        simp [N3Certificate.two_eq_zero_f2, N3Certificate.four_eq_zero_f2,
          N3Certificate.eight_eq_zero_f2]
  · have hEmpty : ¬s ⊆ ∅ := fun h => hs (h.trans (by simp))
    have hI : ¬s ⊆ {i} := fun h => hs (h.trans (by simp))
    have hJ : ¬s ⊆ {j} := fun h => hs (h.trans (by simp))
    have hK : ¬s ⊆ {k} := fun h => hs (h.trans (by simp))
    have hIJ : ¬s ⊆ {i, j} := fun h => hs (h.trans (by simp))
    have hIK : ¬s ⊆ {i, k} := fun h => hs (h.trans (by simp))
    have hJK : ¬s ⊆ {j, k} := fun h => hs (h.trans (by simp))
    have hne : s ≠ {i, j, k} := fun h => hs (by rw [h])
    simp [hEmpty, hI, hJ, hK, hIJ, hIK, hJK, hs, hne]

theorem triplePolarMap_eq_tripleCoeffMap
    (i j k : Fin 8) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    triplePolarMap i j k = tripleCoeffMap i j k := by
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext
  intro c
  change triplePolarMap i j k (MonoidAlgebra.single s c) =
    tripleCoeffMap i j k (MonoidAlgebra.single s c)
  simp only [triplePolarMap, LinearMap.add_apply]
  rw [sparseEvalMap_single, sparseEvalMap_single,
    sparseEvalMap_single, sparseEvalMap_single,
    sparseEvalMap_single, sparseEvalMap_single,
    sparseEvalMap_single, sparseEvalMap_single]
  change
    c * (if s.vars ⊆ ∅ then 1 else 0) +
      c * (if s.vars ⊆ {i} then 1 else 0) +
      c * (if s.vars ⊆ {j} then 1 else 0) +
      c * (if s.vars ⊆ {k} then 1 else 0) +
      c * (if s.vars ⊆ {i, j} then 1 else 0) +
      c * (if s.vars ⊆ {i, k} then 1 else 0) +
      c * (if s.vars ⊆ {j, k} then 1 else 0) +
      c * (if s.vars ⊆ {i, j, k} then 1 else 0) =
        (MonoidAlgebra.single s c : ANF 8).coeff ⟨{i, j, k}⟩
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  have hid := subset_triple_polar_identity s.vars i j k hij hik hjk
  have heq : s = ⟨{i, j, k}⟩ ↔ s.vars = {i, j, k} := by
    constructor
    · intro h
      simp [h]
    · exact Monomial.ext
  calc
    _ = c *
        ((if s.vars ⊆ ∅ then 1 else 0) +
          (if s.vars ⊆ {i} then 1 else 0) +
          (if s.vars ⊆ {j} then 1 else 0) +
          (if s.vars ⊆ {k} then 1 else 0) +
          (if s.vars ⊆ {i, j} then 1 else 0) +
          (if s.vars ⊆ {i, k} then 1 else 0) +
          (if s.vars ⊆ {j, k} then 1 else 0) +
          (if s.vars ⊆ {i, j, k} then 1 else 0)) := by ring
    _ = c * (if s.vars = {i, j, k} then 1 else 0) := by rw [hid]
    _ = if s = ⟨{i, j, k}⟩ then c else 0 := by
      by_cases hs : s.vars = {i, j, k}
      · rw [ite_eq_left hs, ite_eq_left (heq.mpr hs), mul_one]
      · rw [ite_eq_right hs, ite_eq_right (fun h => hs (heq.mp h)), mul_zero]

/-- Equality of Boolean functions determines their homogeneous cubic
projection. -/
theorem anfThreeProjection_congr_of_eval_eq {p q : ANF 8}
    (h : ∀ x, eval p x = eval q x) :
    anfThreeProjection p = anfThreeProjection q := by
  exact congrArg anfThreeProjection (eval_injective 8 (funext h))

end

end N4
end UnrestrictedBooleanMul
