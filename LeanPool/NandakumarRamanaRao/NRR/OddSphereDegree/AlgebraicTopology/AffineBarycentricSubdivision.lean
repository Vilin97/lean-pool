/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Affine barycentric subdivision maps on topological standard simplices

This file supplies the raw affine layer needed before the singular-chain
barycentric subdivision operator.

For a permutation `π : Equiv.Perm (Fin (n+1))`, the `π`-summand of the
barycentric subdivision of the topological standard simplex has vertices

`b_k = barycenter {π 0, ..., π k}`.

The file defines:

* `prefixVertex` : the ordered prefix map `Fin (k+1) -> Fin (n+1)`;
* `prefixBarycenter` : the barycenter of the first `k+1` vertices in that
 permuted order, as a point of `SphereOddDegree.finiteSimplex ℝ (Fin (n+1))`;
* `affineSubdivMap` : the affine self-map of `Δ^n` sending vertex `k` to
 `prefixBarycenter n π k`.

This deliberately does **not** claim the chain-level boundary identity or the
subdivision chain homotopy. Those are separate later files.
-/

open scoped BigOperators
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-- The ambient topological `n`-simplex, represented as the subtype of
nonnegative coordinate functions on `Fin (n+1)` summing to `1`. -/
abbrev Delta (n : ℕ) := ↑(SphereOddDegree.finiteSimplex ℝ (Fin (n + 1)))

/-- The `k`-prefix vertex map associated to a permutation of the vertices of
`Δ^n`. It sends `0,...,k` into `Fin (n+1)` by the permuted order `π`. -/
def prefixVertex (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    Fin (k.val + 1) → Fin (n + 1) :=
  fun i => π ⟨i.val, by
    have hi : i.val < k.val + 1 := i.isLt
    have hk : k.val < n + 1 := k.isLt
    omega⟩

/-- The barycenter of the first `k+1` vertices in the order given by `π`,
viewed as a point of the ambient simplex `Δ^n`. This uses Mathlib's existing
`SphereOddDegree.FiniteSimplex.barycenter` and `SphereOddDegree.FiniteSimplex.map`, avoiding a hand proof that the
coordinates are nonnegative and have total mass `1`. -/
noncomputable def prefixBarycenter (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) : Delta n :=
  SphereOddDegree.FiniteSimplex.map (S := ℝ) (prefixVertex n π k)
    (SphereOddDegree.FiniteSimplex.barycenter (X := Fin (k.val + 1)) (𝕜 := ℝ))

/-- Coordinate formula for `prefixBarycenter`. In words, the `j`-coordinate is
`1/(k+1)` if `j` occurs among `π 0, ..., π k`, and `0` otherwise. We keep it as
an unfolded `SphereOddDegree.FiniteSimplex.map` formula because this is the form most useful for
later `simp`-based face computations. -/
theorem prefixBarycenter_def (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    prefixBarycenter n π k =
      SphereOddDegree.FiniteSimplex.map (S := ℝ) (prefixVertex n π k)
        (SphereOddDegree.FiniteSimplex.barycenter (X := Fin (k.val + 1)) (𝕜 := ℝ)) := rfl

/-- The coordinate function of the affine map attached to the permutation `π`.
It is the convex combination of the prefix barycenters with weights given by
`x`. -/
noncomputable def affineSubdivMapFun (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) : Fin (n + 1) → ℝ :=
  fun j => ∑ k : Fin (n + 1), (x k) * (prefixBarycenter n π k j)

/-- Nonnegativity of every coordinate of `affineSubdivMapFun`. -/
theorem affineSubdivMapFun_nonneg (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (j : Fin (n + 1)) :
    0 ≤ affineSubdivMapFun n π x j := by
  unfold affineSubdivMapFun
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (SphereOddDegree.FiniteSimplex.zero_le x k) (SphereOddDegree.FiniteSimplex.zero_le (prefixBarycenter n π k) j)

/-- The coordinates of `affineSubdivMapFun` sum to `1`. -/
theorem affineSubdivMapFun_sum_eq_one (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) :
    (∑ j : Fin (n + 1), affineSubdivMapFun n π x j) = 1 := by
  unfold affineSubdivMapFun
  rw [Finset.sum_comm]
  have hk : ∀ k : Fin (n + 1),
      (∑ j : Fin (n + 1), x k * prefixBarycenter n π k j) = x k := by
    intro k
    rw [← Finset.mul_sum, SphereOddDegree.FiniteSimplex.sum_eq_one, mul_one]
  rw [Finset.sum_congr rfl (fun k _ => hk k)]
  exact SphereOddDegree.FiniteSimplex.sum_eq_one x

/-- The affine self-map of `Δ^n` associated to a permutation `π`; this is the
geometric simplex appearing as one signed summand in barycentric subdivision. -/
noncomputable def affineSubdivMap (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    Delta n → Delta n :=
  fun x => ⟨affineSubdivMapFun n π x,
    ⟨affineSubdivMapFun_nonneg n π x, affineSubdivMapFun_sum_eq_one n π x⟩⟩

@[simp] theorem affineSubdivMap_apply (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Delta n) (j : Fin (n + 1)) :
    affineSubdivMap n π x j =
      ∑ k : Fin (n + 1), x k * prefixBarycenter n π k j := rfl

/-- The affine map sends the `k`-th vertex of the domain simplex to the
`k`-th prefix barycenter. -/
theorem affineSubdivMap_vertex (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    affineSubdivMap n π (SphereOddDegree.FiniteSimplex.vertex (S := ℝ) k) = prefixBarycenter n π k := by
  apply SphereOddDegree.FiniteSimplex.ext
  funext j
  simp only [affineSubdivMap_apply]
  rw [Finset.sum_eq_single k]
  · simp [SphereOddDegree.FiniteSimplex.vertex]
  · intro b _ hb
    simp [SphereOddDegree.FiniteSimplex.vertex, Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- Naturality of the construction under postcomposition of the vertex
permutation. This is a lightweight bookkeeping lemma useful when comparing
adjacent permutation summands later. -/
theorem prefixVertex_comp (n : ℕ) (π τ : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    prefixVertex n (τ.trans π) k = fun i => π (prefixVertex n τ k i) := by
  funext i
  rfl

/-- The first prefix barycenter is the first permuted vertex. -/
theorem prefixBarycenter_zero (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    prefixBarycenter n π 0 = SphereOddDegree.FiniteSimplex.vertex (S := ℝ) (π 0) := by
  have h1 : (0 : Fin (n + 1)).val + 1 = 1 := rfl
  have : Unique (Fin ((0 : Fin (n + 1)).val + 1)) := by
    rw [h1]
    infer_instance
  have hb : (SphereOddDegree.FiniteSimplex.barycenter (X := Fin ((0 : Fin (n + 1)).val + 1)) (𝕜 := ℝ)) =
      SphereOddDegree.FiniteSimplex.vertex 0 := Subsingleton.elim _ _
  rw [prefixBarycenter, hb, SphereOddDegree.FiniteSimplex.map_vertex]
  rfl


end AffineBarycentricSubdivision
end SphereOddDegree
