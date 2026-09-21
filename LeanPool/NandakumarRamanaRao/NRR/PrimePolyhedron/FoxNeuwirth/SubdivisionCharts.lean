/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.OrderComplexRealization
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FiniteCells
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionSmallSimplex

/-!
# Barycentric subdivision charts for the Fox--Neuwirth order complex

This module connects the compact global order-complex realization to the affine
barycentric-subdivision infrastructure already developed in the sphere-degree part of the
repository.

A strict chain `s : Simplex p d` gives a canonical affine chart from the standard simplex into the
global barycentric carrier.  Precomposing this chart with an iterated affine subdivision map gives
the refined simplex charts used in the S6 approximation theorem.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

namespace FoxNeuwirthOrderComplex

variable {p d : Nat}

namespace StandardSimplex

/-- The project standard simplex and Mathlib's topological standard simplex have the same
coordinate predicate. -/
def toDelta (w : StandardSimplex d) : Delta d :=
  ⟨w.1, w.2⟩

/-- Conversion back from the topological standard simplex. -/
def ofDelta (w : Delta d) : StandardSimplex d :=
  ⟨w.1, w.2⟩

@[simp] theorem ofDelta_toDelta (w : StandardSimplex d) : ofDelta (toDelta w) = w := rfl
@[simp] theorem toDelta_ofDelta (w : Delta d) : toDelta (ofDelta w) = w := rfl

/-- Canonical equivalence between the two simplex presentations. -/
def equivDelta : StandardSimplex d ≃ Delta d where
  toFun := toDelta
  invFun := ofDelta
  left_inv := ofDelta_toDelta
  right_inv := toDelta_ofDelta

end StandardSimplex

namespace Simplex

/-- Coordinate weight of a point in the affine chart of a strict chain. -/
noncomputable def chartWeight
    (s : Simplex p d) (w : StandardSimplex d) (c : BarredPermutation p) : Real :=
  ∑ i : Fin (d + 1), if s i = c then w i else 0

/-- A nonzero chart coordinate comes from a vertex of the strict chain. -/
theorem exists_vertex_of_chartWeight_ne_zero
    (s : Simplex p d) (w : StandardSimplex d) (c : BarredPermutation p)
    (h : s.chartWeight w c ≠ 0) :
    ∃ i : Fin (d + 1), s i = c := by
  classical
  by_contra hnone
  push Not at hnone
  apply h
  simp [chartWeight, hnone]

/-- Affine chart of an order-complex simplex into the global barycentric realization. -/
noncomputable def realizationPoint
    (s : Simplex p d) (w : StandardSimplex d) : Realization p :=
  ⟨s.chartWeight w, by
    refine ⟨?_, ?_, ?_⟩
    · intro c
      exact Finset.sum_nonneg fun i _ => by
        split_ifs
        · exact w.nonneg i
        · exact le_rfl
    · classical
      unfold chartWeight
      rw [Finset.sum_comm]
      simp [w.sum_eq_one]
    · intro a b ha hb hab
      obtain ⟨i, hi⟩ := s.exists_vertex_of_chartWeight_ne_zero w a ha
      obtain ⟨j, hj⟩ := s.exists_vertex_of_chartWeight_ne_zero w b hb
      subst a
      subst b
      have hij : i ≠ j := by
        intro h
        subst j
        exact hab rfl
      rcases lt_or_gt_of_ne hij with hij | hji
      · exact Or.inl (s.properFace hij)
      · exact Or.inr (s.properFace hji)⟩

@[simp] theorem realizationPoint_apply
    (s : Simplex p d) (w : StandardSimplex d) (c : BarredPermutation p) :
    s.realizationPoint w c = s.chartWeight w c := rfl

/-- A chart sends a standard vertex to the corresponding realization vertex. -/
theorem realizationPoint_vertex
    (s : Simplex p d) (i : Fin (d + 1)) :
    s.realizationPoint (StandardSimplex.ofDelta (stdSimplex.vertex (S := Real) i)) =
      Realization.vertex (s i) := by
  apply Realization.ext
  intro c
  classical
  change (∑ j, if s j = c then (stdSimplex.vertex (S := Real) i) j else 0) =
    if c = s i then 1 else 0
  by_cases hci : c = s i
  · subst c
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [s.vertex_injective.ne hji]
    · simp
  · have hnone : ∀ j, s j = c → j ≠ i := by
      intro j hj hji
      subst j
      exact hci hj.symm
    calc
      (∑ j, if s j = c then (stdSimplex.vertex (S := Real) i) j else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : s j = c
        · simp [hj, hnone j hj]
        · simp [hj]
      _ = (if c = s i then 1 else 0) := by simp [hci]

/-- The affine chart is continuous. -/
theorem continuous_realizationPoint (s : Simplex p d) :
    Continuous s.realizationPoint := by
  have hcoord (i : Fin (d + 1)) :
      Continuous (fun w : StandardSimplex d => w i) := by
    change @Continuous (StandardSimplex d) ℝ
      (TopologicalSpace.induced Subtype.val inferInstance) inferInstance _
    exact (continuous_apply i).comp continuous_induced_dom
  apply continuous_induced_rng.2
  apply continuous_pi
  intro c
  change Continuous (fun w : StandardSimplex d =>
    ∑ i : Fin (d + 1), if s i = c then w i else 0)
  exact continuous_finsetSum _ fun i _ => by
      by_cases h : s i = c
      · simpa only [h, ↓reduceIte] using hcoord i
      · simpa only [h, ↓reduceIte] using (continuous_const :
          Continuous (fun _ : StandardSimplex d => (0 : Real)))

/-- Bundled continuous simplex chart. -/
noncomputable def realizationContinuousMap (s : Simplex p d) :
    C(Delta d, Realization p) where
  toFun w := s.realizationPoint (StandardSimplex.ofDelta w)
  continuous_toFun := s.continuous_realizationPoint.comp
    (continuous_induced_rng.2 continuous_subtype_val)

end Simplex

/-- A word indexing one affine simplex of an `N`-fold barycentric subdivision. -/
abbrev RefinementWord (p N : Nat) :=
  Fin N → Equiv.Perm (Fin p)

namespace Simplex

variable (s : Simplex p (p - 1))

/-- Convert a label permutation to the simplex-index permutation. For `p = 0`, the source
permutation is vacuous and the target is the identity. -/
noncomputable def refinementIndexPerm (sigma : Equiv.Perm (Fin p)) :
    Equiv.Perm (Fin (p - 1 + 1)) := by
  by_cases hp0 : 0 < p
  · have hdim : p - 1 + 1 = p := Nat.sub_add_cancel hp0
    exact (Equiv.cast (congrArg Fin hdim)).trans sigma |>.trans
      (Equiv.cast (congrArg Fin hdim.symm))
  · exact 1

/-- Refined chart obtained by precomposing a maximal-chain chart with an iterated affine
barycentric subdivision map. -/
noncomputable def refinedContinuousMap
    (N : Nat) (rho : RefinementWord p N) : C(Delta (p - 1), Realization p) :=
  s.realizationContinuousMap.comp
    (AffineBarycentricSubdivision.affineCompMap (p - 1) N
      (fun k => refinementIndexPerm (rho k)))

/-- Pointwise form of a refined chart. -/
noncomputable def refinedPoint
    (N : Nat) (rho : RefinementWord p N) (w : StandardSimplex (p - 1)) :
    Realization p :=
  s.refinedContinuousMap N rho (StandardSimplex.toDelta w)

/-- Vertices of a refined simplex. -/
noncomputable def refinedVertex
    (N : Nat) (rho : RefinementWord p N) (i : Fin p) : Realization p := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero (by intro h; subst p; exact Fin.elim0 i)
  have hdim : p - 1 + 1 = p := Nat.sub_add_cancel hp0
  exact s.refinedContinuousMap N rho
    (stdSimplex.vertex (S := Real) (Fin.cast hdim.symm i))

@[simp] theorem refinedPoint_vertex
    (N : Nat) (rho : RefinementWord p N) (i : Fin p) :
    s.refinedPoint N rho
        (StandardSimplex.ofDelta (stdSimplex.vertex (S := Real)
          (Fin.cast (Nat.sub_add_cancel (Nat.pos_of_ne_zero
            (by intro h; subst p; exact Fin.elim0 i))).symm i))) =
      s.refinedVertex N rho i := by
  rfl

/-- The refined chart is continuous in barycentric coordinates. -/
theorem continuous_refinedPoint (N : Nat) (rho : RefinementWord p N) :
    Continuous (s.refinedPoint N rho) :=
  (s.refinedContinuousMap N rho).continuous.comp
    (continuous_induced_rng.2 continuous_subtype_val)

end Simplex

end FoxNeuwirthOrderComplex
end NRR
