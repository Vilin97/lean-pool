/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import LeanPool.PebblingLean.GraphIso
import LeanPool.PebblingLean.Hypercube
import LeanPool.PebblingLean.Product
import LeanPool.PebblingLean.UpperBound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Embedding

/-!
# Hypercubes as Cartesian products

This file starts the bridge from the abstract Cartesian-product pebbling theorem
to hypercubes.  The first ingredient is the coordinate split
`Q_{a+m} ≃ Q_a × Q_m`.
-/

namespace PebblingLean

namespace Hypercube

/-- Split a vertex of `Q_{a+m}` into its first `a` and last `m` coordinates. -/
def splitVertex (a m : ℕ) (v : HypercubeVertex (a + m)) :
    HypercubeVertex a × HypercubeVertex m :=
  (fun i => v (Fin.castAdd m i), fun j => v (Fin.natAdd a j))

/-- Append vertices of `Q_a` and `Q_m` to obtain a vertex of `Q_{a+m}`. -/
def appendVertex {a m : ℕ}
    (p : HypercubeVertex a × HypercubeVertex m) : HypercubeVertex (a + m) :=
  Fin.append p.1 p.2

/-- Coordinate splitting gives a vertex equivalence `Q_{a+m} ≃ Q_a × Q_m`. -/
def splitVertexEquiv (a m : ℕ) :
    HypercubeVertex (a + m) ≃ HypercubeVertex a × HypercubeVertex m where
  toFun := splitVertex a m
  invFun := appendVertex
  left_inv := by
    intro v
    exact Fin.append_castAdd_natAdd
  right_inv := by
    intro p
    ext i <;> simp [splitVertex, appendVertex]

@[simp]
theorem splitVertexEquiv_apply (a m : ℕ) (v : HypercubeVertex (a + m)) :
    splitVertexEquiv a m v = splitVertex a m v :=
  rfl

@[simp]
theorem splitVertexEquiv_symm_apply {a m : ℕ}
    (p : HypercubeVertex a × HypercubeVertex m) :
    (splitVertexEquiv a m).symm p = appendVertex p :=
  rfl

/-- Hamming distance splits over appended coordinates. -/
theorem dist_appendVertex {a m : ℕ}
    (x x' : HypercubeVertex a) (z z' : HypercubeVertex m) :
    dist (appendVertex (x, z)) (appendVertex (x', z')) =
      dist x x' + dist z z' := by
  classical
  let leftDiff : Finset (Fin (a + m)) :=
    (Finset.univ.filter fun i : Fin a => x i ≠ x' i).map (Fin.castAddEmb m)
  let rightDiff : Finset (Fin (a + m)) :=
    (Finset.univ.filter fun j : Fin m => z j ≠ z' j).map (Fin.natAddEmb a)
  have hdiff :
      (Finset.univ.filter fun k : Fin (a + m) =>
        appendVertex (x, z) k ≠ appendVertex (x', z') k) =
        leftDiff ∪ rightDiff := by
    ext k
    induction k using Fin.addCases with
    | left i =>
        have hnot_right : Fin.castAdd m i ∉ rightDiff := by
          intro hk
          rcases Finset.mem_map.mp hk with ⟨j, _hj, hj_eq⟩
          have hlt : ((Fin.castAdd m i : Fin (a + m)) : ℕ) < a := i.isLt
          have hge : a ≤ ((Fin.castAdd m i : Fin (a + m)) : ℕ) := by
            rw [← hj_eq]
            exact Nat.le_add_right a j
          exact (Nat.not_lt_of_ge hge) hlt
        simp [leftDiff, rightDiff, appendVertex, hnot_right]
    | right j =>
        have hnot_left : Fin.natAdd a j ∉ leftDiff := by
          intro hk
          rcases Finset.mem_map.mp hk with ⟨i, _hi, hi_eq⟩
          have hge : a ≤ ((Fin.natAdd a j : Fin (a + m)) : ℕ) :=
            Nat.le_add_right a j
          have hlt : ((Fin.natAdd a j : Fin (a + m)) : ℕ) < a := by
            rw [← hi_eq]
            exact i.isLt
          exact (Nat.not_lt_of_ge hge) hlt
        simp [leftDiff, rightDiff, appendVertex, hnot_left]
  have hdisjoint : Disjoint leftDiff rightDiff := by
    rw [Finset.disjoint_left]
    intro k hk_left hk_right
    rcases Finset.mem_map.mp hk_left with ⟨i, _hi, hi_eq⟩
    rcases Finset.mem_map.mp hk_right with ⟨j, _hj, hj_eq⟩
    have hlt : (k : ℕ) < a := by
      rw [← hi_eq]
      exact i.isLt
    have hge : a ≤ (k : ℕ) := by
      rw [← hj_eq]
      exact Nat.le_add_right a j
    exact (Nat.not_lt_of_ge hge) hlt
  unfold dist
  rw [hdiff, Finset.card_union_of_disjoint hdisjoint]
  simp [leftDiff, rightDiff]

/-- Appended vertices are adjacent exactly when one factor is adjacent and the
other factor is unchanged. -/
theorem appendVertex_adj_iff {a m : ℕ}
    (p q : HypercubeVertex a × HypercubeVertex m) :
    (graph (a + m)).Adj (appendVertex p) (appendVertex q) ↔
      (Graph.cartesianProduct (graph a) (graph m)).Adj p q := by
  constructor
  · intro h
    change dist (appendVertex p) (appendVertex q) = 1 at h
    rw [dist_appendVertex] at h
    rcases Nat.add_eq_one_iff.mp h with hcase | hcase
    · exact Or.inr ⟨dist_eq_zero_iff.mp hcase.1, hcase.2⟩
    · exact Or.inl ⟨hcase.1, dist_eq_zero_iff.mp hcase.2⟩
  · intro h
    change dist (appendVertex p) (appendVertex q) = 1
    rw [dist_appendVertex]
    rcases h with hleft | hright
    · rw [hleft.1, hleft.2, dist_self, Nat.add_zero]
    · rw [hright.1, dist_self, hright.2, Nat.zero_add]

/-- The coordinate split preserves adjacency. -/
theorem splitVertex_adj_iff {a m : ℕ} {v w : HypercubeVertex (a + m)} :
    (graph (a + m)).Adj v w ↔
      (Graph.cartesianProduct (graph a) (graph m)).Adj
        (splitVertex a m v) (splitVertex a m w) := by
  have hv : appendVertex (splitVertex a m v) = v :=
    (splitVertexEquiv a m).left_inv v
  have hw : appendVertex (splitVertex a m w) = w :=
    (splitVertexEquiv a m).left_inv w
  simpa [hv, hw] using
    appendVertex_adj_iff (p := splitVertex a m v) (q := splitVertex a m w)

/-- Graph isomorphism `Q_(a+m) ≃ Q_a □ Q_m`. -/
def splitGraphIso (a m : ℕ) :
    GraphIso (graph (a + m)) (Graph.cartesianProduct (graph a) (graph m)) where
  toEquiv := splitVertexEquiv a m
  adj_iff := by
    intro v w
    exact splitVertex_adj_iff

/-- Hypercube-specific deterministic product step.  A solvable distribution
`E` on `Q_m` specifies how many pebbles must be prepared in each `Q_a` fiber;
if those fiber demands can be met within the given costs, then `Q_(a+m)` has a
solvable distribution with the summed cost. -/
theorem hasSolvableAtMostSize_split_product_of_fiber_demands
    {a m : ℕ} {E : Pebbling (HypercubeVertex m)}
    {cost : HypercubeVertex m → ℕ}
    (hE : Pebbling.Solvable (graph m) E)
    (hcost :
      ∀ z : HypercubeVertex m,
        E z ≠ 0 → Pebbling.HasSolvableAtMostSize (graph a) (E z) (cost z)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else cost z) := by
  classical
  have hprod :
      Pebbling.HasSolvableAtMostSize
        (Graph.cartesianProduct (graph a) (graph m)) 1
        (∑ z : HypercubeVertex m, if E z = 0 then 0 else cost z) :=
    Pebbling.hasSolvableAtMostSize_product_of_fiber_demands
      (G := graph a) (H := graph m) hE hcost
  exact (splitGraphIso a m).symm.map_hasSolvableAtMostSize hprod

/-- Product step where the first-factor cost depends only on the demand value
`E z`, not on the fiber location `z`. -/
theorem hasSolvableAtMostSize_split_product_of_demand_cost
    {a m : ℕ} {E : Pebbling (HypercubeVertex m)} {demandCost : ℕ → ℕ}
    (hE : Pebbling.Solvable (graph m) E)
    (hcost :
      ∀ T : ℕ, T ≠ 0 →
        Pebbling.HasSolvableAtMostSize (graph a) T (demandCost T)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else demandCost (E z)) := by
  classical
  exact hasSolvableAtMostSize_split_product_of_fiber_demands
    (a := a) (m := m) (E := E)
    (cost := fun z : HypercubeVertex m => demandCost (E z))
    hE (fun z hz => hcost (E z) hz)

/-- Linear fiber-demand recurrence: if every demand `T` in `Q_a` can be solved
with at most `K*T` pebbles, then using a solvable distribution `E` on `Q_m` as
the second-factor demand pattern costs at most `K * |E|`. -/
theorem hasSolvableAtMostSize_split_product_of_linear_demand_cost
    {a m K : ℕ} {E : Pebbling (HypercubeVertex m)}
    (hE : Pebbling.Solvable (graph m) E)
    (hcost :
      ∀ T : ℕ,
        Pebbling.HasSolvableAtMostSize (graph a) T (K * T)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (K * Pebbling.size E) := by
  classical
  have hprod :=
    hasSolvableAtMostSize_split_product_of_demand_cost
      (a := a) (m := m) (E := E)
      (demandCost := fun T : ℕ => K * T)
      hE (fun T _hT => hcost T)
  have hsum :
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else K * E z) =
        K * Pebbling.size E := by
    rw [Pebbling.size, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro z _hz
    by_cases hEz : E z = 0
    · simp [hEz]
    · simp [hEz]
  simpa [hsum] using hprod

/-- If the second factor is `T`-solvable with `T ≥ 1`, it may be used as the
solvable demand pattern in the product step. -/
theorem hasSolvableAtMostSize_split_product_of_highDemand_demand_cost
    {a m T : ℕ} {E : Pebbling (HypercubeVertex m)} {demandCost : ℕ → ℕ}
    (hT : 1 ≤ T)
    (hE : Pebbling.SolvableAtLeast (graph m) E T)
    (hcost :
      ∀ t : ℕ, t ≠ 0 →
        Pebbling.HasSolvableAtMostSize (graph a) t (demandCost t)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else demandCost (E z)) :=
  hasSolvableAtMostSize_split_product_of_demand_cost
    (a := a) (m := m) (E := E) (demandCost := demandCost)
    (Pebbling.solvable_of_solvableAtLeast hT hE) hcost

/-- Uniform high-demand fiber recurrence.  If `E` is a `T`-solvable
second-factor distribution and every occupied pile of `E` has size at most
`Tfiber`, then one `Tfiber`-solvable construction in `Q_a` can be reused for
every occupied fiber. -/
theorem hasSolvableAtMostSize_split_product_of_uniform_fiber_bound
    {a m Tbase Tfiber K : ℕ} {E : Pebbling (HypercubeVertex m)}
    (hTbase : 1 ≤ Tbase)
    (hE : Pebbling.SolvableAtLeast (graph m) E Tbase)
    (hpile_le : ∀ z : HypercubeVertex m, E z ≤ Tfiber)
    (hfiber : Pebbling.HasSolvableAtMostSize (graph a) Tfiber K) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (Pebbling.supportSize E * K) := by
  classical
  have hprod :=
    hasSolvableAtMostSize_split_product_of_fiber_demands
      (a := a) (m := m) (E := E)
      (cost := fun _z : HypercubeVertex m => K)
      (Pebbling.solvable_of_solvableAtLeast hTbase hE)
      (fun z _hz =>
        Pebbling.hasSolvableAtMostSize_mono_demand (hpile_le z) hfiber)
  simpa [Pebbling.sum_ite_nonzero_const] using hprod

/-- Uniform fiber recurrence with occupied-pile compression.  If each occupied
pile of `E` has at least `S` pebbles, and a `Tfiber`-solvable construction in
`Q_a` costs at most `S*K`, then the product cost is bounded by `|E|*K`. -/
theorem hasSolvableAtMostSize_split_product_of_uniform_fiber_bound_minPile
    {a m Tbase Tfiber S K : ℕ} {E : Pebbling (HypercubeVertex m)}
    (hTbase : 1 ≤ Tbase)
    (hE : Pebbling.SolvableAtLeast (graph m) E Tbase)
    (hpile_le : ∀ z : HypercubeVertex m, E z ≤ Tfiber)
    (hmin : Pebbling.MinOccupiedPileSize E S)
    (hfiber : Pebbling.HasSolvableAtMostSize (graph a) Tfiber (S * K)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1
      (Pebbling.size E * K) := by
  have hprod :=
    hasSolvableAtMostSize_split_product_of_uniform_fiber_bound
      (a := a) (m := m) (Tbase := Tbase) (Tfiber := Tfiber)
      (K := S * K) (E := E)
      hTbase hE hpile_le hfiber
  exact Pebbling.hasSolvableAtMostSize_mono_size
    (Pebbling.supportSize_mul_minPileCost_le_size_mul hmin) hprod

/-- Recurrence step from a high-demand distribution.  If `Q_m` has a
`Tbase`-solvable distribution of size at most `costBound` whose occupied piles
have size at least `S`, and `Q_a` can solve demand `costBound` with cost
`S*K`, then `Q_(a+m)` has a solvable distribution with cost `costBound*K`. -/
theorem hasSolvableAtMostSize_split_product_of_highDemand
    {a m Tbase costBound S K : ℕ}
    (hTbase : 1 ≤ Tbase)
    (hhigh : HasHighDemandDistribution m Tbase costBound S)
    (hfiber : Pebbling.HasSolvableAtMostSize (graph a) costBound (S * K)) :
    Pebbling.HasSolvableAtMostSize (graph (a + m)) 1 (costBound * K) := by
  rcases hhigh with ⟨E, hsize, hE, hmin⟩
  have hpile_le : ∀ z : HypercubeVertex m, E z ≤ costBound := by
    intro z
    exact (Pebbling.le_size E z).trans hsize
  have hprod :=
    hasSolvableAtMostSize_split_product_of_uniform_fiber_bound_minPile
      (a := a) (m := m) (Tbase := Tbase) (Tfiber := costBound)
      (S := S) (K := K) (E := E)
      hTbase hE hpile_le hmin hfiber
  exact Pebbling.hasSolvableAtMostSize_mono_size
    (Nat.mul_le_mul_right K hsize) hprod

/-- High-demand product recurrence preserving the next pile-size invariant.
The same high-demand fiber construction in `Q_a` is reused for every occupied
fiber over `Q_m`; occupied-pile compression in the `Q_m` distribution pays for
this reuse. -/
theorem hasHighDemandDistribution_split_product_of_highDemand
    {a m Tbase costBound S K Snew : ℕ}
    (hTbase : 1 ≤ Tbase)
    (hhigh : HasHighDemandDistribution m Tbase costBound S)
    (hfiber : HasHighDemandDistribution a costBound (S * K) Snew) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) Snew := by
  classical
  rcases hhigh with ⟨E, hEsize, hEsolv, hEmin⟩
  rcases hfiber with ⟨Fbase, hFsize, hFsolv, hFmin⟩
  let F : HypercubeVertex m → Pebbling (HypercubeVertex a) :=
    fun z => if E z = 0 then (fun _ : HypercubeVertex a => 0) else Fbase
  let Dprod : Pebbling (HypercubeVertex a × HypercubeVertex m) :=
    Pebbling.fibersDistribution F
  let D : Pebbling (HypercubeVertex (a + m)) :=
    (splitGraphIso a m).symm.mapDistribution Dprod
  have hpile_le : ∀ z : HypercubeVertex m, E z ≤ costBound := by
    intro z
    exact (Pebbling.le_size E z).trans hEsize
  have hFsolv : ∀ z : HypercubeVertex m,
      Pebbling.SolvableAtLeast (graph a) (F z) (E z) := by
    intro z
    by_cases hz : E z = 0
    · simp [F, hz, Pebbling.solvableAtLeast_zero]
    · simpa [F, hz] using
        Pebbling.solvableAtLeast_mono (hpile_le z) hFsolv
  have hprod_solvable :
      Pebbling.Solvable
        (Graph.cartesianProduct (graph a) (graph m)) Dprod := by
    exact Pebbling.solvable_product_of_fiber_demands
      (G := graph a) (H := graph m)
      (Pebbling.solvable_of_solvableAtLeast hTbase hEsolv) hFsolv
  have hDsolv : Pebbling.Solvable (graph (a + m)) D := by
    exact (splitGraphIso a m).symm.map_solvableAtLeast hprod_solvable
  have hFsize_each : ∀ z : HypercubeVertex m,
      Pebbling.size (F z) ≤ if E z = 0 then 0 else S * K := by
    intro z
    by_cases hz : E z = 0
    · simp [F, hz]
    · simpa [F, hz] using hFsize
  have hprod_size :
      Pebbling.size Dprod ≤
        ∑ z : HypercubeVertex m, if E z = 0 then 0 else S * K := by
    exact Pebbling.size_fibersDistribution_le hFsize_each
  have hsum :
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else S * K) =
        Pebbling.supportSize E * (S * K) := by
    exact Pebbling.sum_ite_nonzero_const E (S * K)
  have hcompressed :
      Pebbling.supportSize E * (S * K) ≤ costBound * K :=
    (Pebbling.supportSize_mul_minPileCost_le_size_mul hEmin).trans
      (Nat.mul_le_mul_right K hEsize)
  have hDsize : Pebbling.size D ≤ costBound * K := by
    calc
      Pebbling.size D = Pebbling.size Dprod := by
        exact (splitGraphIso a m).symm.size_mapDistribution Dprod
      _ ≤ ∑ z : HypercubeVertex m, if E z = 0 then 0 else S * K := hprod_size
      _ = Pebbling.supportSize E * (S * K) := hsum
      _ ≤ costBound * K := hcompressed
  have hprod_min : Pebbling.MinOccupiedPileSize Dprod Snew := by
    intro p hp
    rcases p with ⟨x, z⟩
    by_cases hz : E z = 0
    · simp [Dprod, F, hz] at hp
    · have hpF : Fbase x ≠ 0 := by
        simpa [Dprod, F, Pebbling.fibersDistribution, hz] using hp
      exact (by
        simpa [Dprod, F, Pebbling.fibersDistribution, hz] using hFmin x hpF)
  have hDmin : Pebbling.MinOccupiedPileSize D Snew := by
    exact (splitGraphIso a m).symm.map_minOccupiedPileSize hprod_min
  exact ⟨D, hDsize, hDsolv, hDmin⟩

/-- Variable-demand high-demand product recurrence.

This is the paper-facing product step.  If an occupied second-factor pile has
size `s_z`, we use a first-factor construction for demand `s_z` and cost
`s_z*K`.  Summing over occupied fibers gives total cost `|E|*K`, and the
high-demand bound on `E` then gives `costBound*K`. -/
theorem hasHighDemandDistribution_split_product_of_highDemand_variable
    {a m Tbase costBound S K Snew : ℕ}
    (hTbase : 1 ≤ Tbase)
    (hhigh : HasHighDemandDistribution m Tbase costBound S)
    (hfiber :
      ∀ t : ℕ, S ≤ t → HasHighDemandDistribution a t (t * K) Snew) :
    HasHighDemandDistribution (a + m) 1 (costBound * K) Snew := by
  classical
  rcases hhigh with ⟨E, hEsize, hEsolv, hEmin⟩
  let F : HypercubeVertex m → Pebbling (HypercubeVertex a) :=
    fun z =>
      if hz : E z = 0 then
        fun _ : HypercubeVertex a => 0
      else
        Classical.choose (hfiber (E z) (hEmin z hz))
  let Dprod : Pebbling (HypercubeVertex a × HypercubeVertex m) :=
    Pebbling.fibersDistribution F
  let D : Pebbling (HypercubeVertex (a + m)) :=
    (splitGraphIso a m).symm.mapDistribution Dprod
  have hFsolv : ∀ z : HypercubeVertex m,
      Pebbling.SolvableAtLeast (graph a) (F z) (E z) := by
    intro z
    by_cases hz : E z = 0
    · simp [F, hz, Pebbling.solvableAtLeast_zero]
    · have hspec := Classical.choose_spec (hfiber (E z) (hEmin z hz))
      simpa [F, hz] using hspec.2.1
  have hprod_solvable :
      Pebbling.Solvable
        (Graph.cartesianProduct (graph a) (graph m)) Dprod := by
    exact Pebbling.solvable_product_of_fiber_demands
      (G := graph a) (H := graph m)
      (Pebbling.solvable_of_solvableAtLeast hTbase hEsolv) hFsolv
  have hDsolv : Pebbling.Solvable (graph (a + m)) D := by
    exact (splitGraphIso a m).symm.map_solvableAtLeast hprod_solvable
  have hFsize_each : ∀ z : HypercubeVertex m,
      Pebbling.size (F z) ≤ if E z = 0 then 0 else E z * K := by
    intro z
    by_cases hz : E z = 0
    · simp [F, hz]
    · have hspec := Classical.choose_spec (hfiber (E z) (hEmin z hz))
      simpa [F, hz] using hspec.1
  have hprod_size :
      Pebbling.size Dprod ≤
        ∑ z : HypercubeVertex m, if E z = 0 then 0 else E z * K := by
    exact Pebbling.size_fibersDistribution_le hFsize_each
  have hsum :
      (∑ z : HypercubeVertex m, if E z = 0 then 0 else E z * K) =
        Pebbling.size E * K := by
    rw [Pebbling.size, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro z _hz
    by_cases hz : E z = 0
    · simp [hz]
    · simp [hz]
  have hcompressed : Pebbling.size E * K ≤ costBound * K :=
    Nat.mul_le_mul_right K hEsize
  have hDsize : Pebbling.size D ≤ costBound * K := by
    calc
      Pebbling.size D = Pebbling.size Dprod := by
        exact (splitGraphIso a m).symm.size_mapDistribution Dprod
      _ ≤ ∑ z : HypercubeVertex m, if E z = 0 then 0 else E z * K := hprod_size
      _ = Pebbling.size E * K := hsum
      _ ≤ costBound * K := hcompressed
  have hprod_min : Pebbling.MinOccupiedPileSize Dprod Snew := by
    intro p hp
    rcases p with ⟨x, z⟩
    by_cases hz : E z = 0
    · simp [Dprod, F, hz] at hp
    · have hspec := Classical.choose_spec (hfiber (E z) (hEmin z hz))
      have hpF : (Classical.choose (hfiber (E z) (hEmin z hz))) x ≠ 0 := by
        simpa [Dprod, F, Pebbling.fibersDistribution, hz] using hp
      simpa [Dprod, F, Pebbling.fibersDistribution, hz] using hspec.2.2 x hpF
  have hDmin : Pebbling.MinOccupiedPileSize D Snew := by
    exact (splitGraphIso a m).symm.map_minOccupiedPileSize hprod_min
  exact ⟨D, hDsize, hDsolv, hDmin⟩

end Hypercube

end PebblingLean
