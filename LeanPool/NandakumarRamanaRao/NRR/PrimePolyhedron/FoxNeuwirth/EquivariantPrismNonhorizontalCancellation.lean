/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismGlobalCancellation
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RefinedChartCarrierEquivariant
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricBoundaryCancellation
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricFiniteCancellation
/-!
# Cancellation of the nonhorizontal refined-prism boundary

This file performs the finite reindexing in the refined prism argument.  There are three
layers.

* The boundary of an iterated barycentric subdivision is the corresponding iterated subdivision of
  the original boundary.  The proof is used only after applying an arbitrary weight to the induced
  face map, so it is stated as a finite weighted identity.
* The standard staircase triangulation of `Delta n x I` has boundary equal to the upper copy minus
  the lower copy minus the staircase prism on the spatial boundary.  Internal staircase faces pair
  with opposite signs.
* The spatial-side term is an equivariant function of an orbit facet.  Reindexing by facet orbits
  turns it into the boundary pairing of `PrimeOrbitCycle.orbitCycle`, hence it vanishes.

Together these statements prove that the `nonhorizontalContribution` isolated in
`EquivariantPrismGlobalCancellation` is zero.  No geometric transgression hypothesis is introduced:
the result is a consequence of the explicit subdivision signs, staircase signs, and the already
proved orbit-cycle boundary identity.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismNonhorizontalCancellation

open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open EquivariantPrismVertexParameters
open EquivariantPrismGenericityPolynomials
open EquivariantPrismGenericPerturbation
open EquivariantPrismGlobalCancellation
open SubdivisionPrismCharts
open RefinedAffineMap

variable {p : Nat}

/-! ## Weighted boundary of iterated barycentric subdivision -/

/-- Insert a zero barycentric coordinate at `k`. -/
noncomputable def cofacePoint
    (n : Nat) (k : Fin (n + 2)) (x : Delta n) : Delta (n + 1) :=
  SphereOddDegree.FiniteSimplex.map (S := Real) k.succAbove x

/-- Transport a standard-simplex point across an equality of dimensions. -/
noncomputable def deltaCast {m n : Nat} (h : m = n) : Delta m → Delta n :=
  fun x => h ▸ x

@[simp] theorem deltaCast_rfl {n : Nat} (x : Delta n) :
    deltaCast rfl x = x := rfl

@[simp] theorem deltaCast_vertex {m n : Nat} (h : m = n)
    (i : Fin (m + 1)) :
    deltaCast h (SphereOddDegree.FiniteSimplex.vertex (S := Real) i) =
      SphereOddDegree.FiniteSimplex.vertex (S := Real)
        (Fin.cast (congrArg (fun t => t + 1) h) i) := by
  subst n
  rfl

@[simp] theorem cofacePoint_apply_succAbove
    (n : Nat) (k : Fin (n + 2)) (x : Delta n) (i : Fin (n + 1)) :
    cofacePoint n k x (k.succAbove i) = x i := by
  unfold cofacePoint
  simp +decide [ Finset.filter_lt_eq_Ioi]
  simp +decide [FunOnFinite.linearMap,
    Finset.filter_lt_eq_Ioi]
  simp +decide [Finsupp.mapDomain, Finsupp.single_apply]
  exact fun h => h.symm

@[simp] theorem cofacePoint_apply_deleted
    (n : Nat) (k : Fin (n + 2)) (x : Delta n) :
    cofacePoint n k x k = 0 := by
  change (SphereOddDegree.FiniteSimplex.map (S := Real) k.succAbove x : Fin (n + 2) → Real) k = 0
  rw [SphereOddDegree.FiniteSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro i hi
  exact (Fin.succAbove_ne k i (Finset.mem_filter.mp hi).2).elim

@[simp] theorem cofacePoint_vertex
    (n : Nat) (k : Fin (n + 2)) (i : Fin (n + 1)) :
    cofacePoint n k (SphereOddDegree.FiniteSimplex.vertex (S := Real) i) =
      SphereOddDegree.FiniteSimplex.vertex (S := Real) (k.succAbove i) := by
  unfold cofacePoint
  rw [SphereOddDegree.FiniteSimplex.map_vertex]

/-- The value of `Fin.succAbove`, exposed without proof-term-sensitive casts. -/
theorem fin_succAbove_val {n : Nat} (k : Fin (n + 1)) (i : Fin n) :
    (k.succAbove i).1 = if i.1 < k.1 then i.1 else i.1 + 1 := by
  rcases lt_or_ge i.castSucc k with hlt | hge
  · rw [Fin.succAbove_of_castSucc_lt k i hlt, ite_eq_left]
    · rfl
    · simpa [Fin.lt_def] using hlt
  · rw [Fin.succAbove_of_le_castSucc k i hge, ite_eq_right]
    · rfl
    · simp only [Fin.le_def, Fin.val_castSucc] at hge
      omega

/-- Product of the orientation signs in an iterated subdivision word. -/
noncomputable def iteratedSign
    (R : Type) [CommRing R] (N : Nat)
    (rho : Fin N -> Equiv.Perm (Fin (n + 1))) : R :=
  ∏ r : Fin N, permSignCoeff R (rho r)

@[simp] theorem iteratedSign_zero
    (R : Type) [CommRing R]
    (rho : Fin 0 -> Equiv.Perm (Fin (n + 1))) :
    iteratedSign R 0 rho = 1 := by
  simp [iteratedSign]

/-- The induced facet map of one simplex in an iterated subdivision. -/
noncomputable def iteratedFacetMap
    {X : Type} (n N : Nat) (sigma : Delta (n + 1) -> X)
    (rho : Fin N -> Equiv.Perm (Fin (n + 2)))
    (k : Fin (n + 2)) : Delta n -> X :=
  fun x => sigma (affineCompMap (n + 1) N rho (cofacePoint n k x))

/-- The iterated subdivision of an original boundary face. -/
noncomputable def iteratedBoundaryMap
    {X : Type} (n N : Nat) (sigma : Delta (n + 1) -> X)
    (k : Fin (n + 2))
    (rho : Fin N -> Equiv.Perm (Fin (n + 1))) : Delta n -> X :=
  fun x => sigma (cofacePoint n k (affineCompMap n N rho x))

/-- One-step internal faces agree after the adjacent transposition. -/
theorem oneStep_internal_face_eq
    {X : Type} (n : Nat) (sigma : Delta (n + 1) -> X)
    (pi : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) :
    iteratedFacetMap n 1 sigma (fun _ => pi) (Fin.castSucc i) =
      iteratedFacetMap n 1 sigma
        (fun _ => (Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans pi)
        (Fin.castSucc i) := by
  funext x
  apply congrArg sigma
  rw [affineCompMap_succ, affineCompMap_succ]
  simp only [affineCompMap_zero, ContinuousMap.id_apply]
  apply affineSubdiv_face_internal_swap
  exact cofacePoint_apply_deleted n (Fin.castSucc i) x

/-- One-step final faces are precisely subdivisions of original boundary faces. -/
theorem oneStep_last_face_eq
    {X : Type} (n : Nat) (sigma : Delta (n + 1) -> X)
    (j : Fin (n + 2)) (rho : Equiv.Perm (Fin (n + 1))) :
    iteratedFacetMap n 1 sigma
        (fun _ => lastFaceEquiv n (j, rho)) (Fin.last (n + 1)) =
      iteratedBoundaryMap n 1 sigma j (fun _ => rho) := by
  funext x
  apply congrArg sigma
  rw [affineCompMap_succ, affineCompMap_succ]
  simp only [affineCompMap_zero, ContinuousMap.id_apply]
  let pi : Equiv.Perm (Fin (n + 2)) := lastFaceEquiv n (j, rho)
  have hj : j = pi (lastVertex n) := by
    simpa [pi, lastFaceEquiv_apply] using
      (lastFaceMap_apply_last j rho).symm
  have hrho : forall t : Fin (n + 1),
      j.succAbove (rho t) = pi (Fin.castSucc t) := by
    intro t
    simpa [pi, lastFaceEquiv_apply] using
      (lastFaceMap_apply_castSucc j rho t).symm
  apply affineSubdiv_face_last_eq_boundary_subdiv
      pi j.succAbove rho hrho
  · convert cofacePoint_apply_deleted n (Fin.last (n + 1)) x using 1
    apply congrArg (cofacePoint n (Fin.last (n + 1)) x)
    apply Fin.ext
    rfl
  · intro k
    simpa [cofacePoint, Fin.succAbove_last] using
      (cofacePoint_apply_succAbove n (Fin.last (n + 1)) x k).symm

/-- Weighted one-step subdivision boundary formula. -/
theorem oneStep_weighted_boundary
    {R X : Type} [CommRing R]
    (n : Nat) (sigma : Delta (n + 1) -> X)
    (W : (Delta n -> X) -> R) :
    (∑ pi : Equiv.Perm (Fin (n + 2)),
      permSignCoeff R pi *
        ∑ k : Fin (n + 2),
          SimplicialChain.faceSign k *
            W (iteratedFacetMap n 1 sigma (fun _ => pi) k)) =
    ∑ j : Fin (n + 2),
      SimplicialChain.faceSign j *
        ∑ rho : Equiv.Perm (Fin (n + 1)),
          permSignCoeff R rho *
            W (iteratedBoundaryMap n 1 sigma j (fun _ => rho)) := by
  classical
  have hinternal :
      (∑ pi : Equiv.Perm (Fin (n + 2)),
        ∑ i : Fin (n + 1),
          permSignCoeff R pi *
            (SimplicialChain.faceSign (Fin.castSucc i) *
              W (iteratedFacetMap n 1 sigma (fun _ => pi) (Fin.castSucc i)))) = 0 := by
    apply internal_faces_double_sum_cancel
      (swapFor := fun i pi =>
        (Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans pi)
      (hswap_invol := fun i => internalSwap_involutive i)
      (hswap_ne := fun i pi => internalSwap_ne i pi)
    intro i pi
    rw [permSignCoeff_adjacent_swap]
    rw [oneStep_internal_face_eq n sigma pi i]
    ring
  have hlast :
      (∑ pi : Equiv.Perm (Fin (n + 2)),
        permSignCoeff R pi *
          (SimplicialChain.faceSign (Fin.last (n + 1)) *
            W (iteratedFacetMap n 1 sigma (fun _ => pi) (Fin.last (n + 1))))) =
      ∑ j : Fin (n + 2),
        SimplicialChain.faceSign j *
          ∑ rho : Equiv.Perm (Fin (n + 1)),
            permSignCoeff R rho *
              W (iteratedBoundaryMap n 1 sigma j (fun _ => rho)) := by
    rw [← Equiv.sum_comp (lastFaceEquiv n)]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro rho hrho
    rw [oneStep_last_face_eq n sigma j rho]
    have hsign := permSignCoeff_last_face_of_faceData R
      (lastFaceEquiv n (j, rho)) j rho
      (by simpa [lastFaceEquiv_apply] using (lastFaceMap_apply_last j rho).symm)
      (by intro t
          simpa [lastFaceEquiv_apply] using
            (lastFaceMap_apply_castSucc j rho t).symm)
    simp only [SimplicialChain.faceSign, Fin.val_last] at hsign ⊢
    ring_nf at hsign ⊢
    calc
      _ = (-(permSignCoeff R ((lastFaceEquiv n) (j, rho)) * (-1 : R) ^ n)) *
          W (iteratedBoundaryMap n 1 sigma j (fun _ => rho)) := by ring
      _ = _ := by rw [hsign]; ring
  calc
    (∑ pi : Equiv.Perm (Fin (n + 2)),
      permSignCoeff R pi *
        ∑ k : Fin (n + 2),
          SimplicialChain.faceSign k *
            W (iteratedFacetMap n 1 sigma (fun _ => pi) k)) =
      (∑ pi : Equiv.Perm (Fin (n + 2)),
        ∑ i : Fin (n + 1),
          permSignCoeff R pi *
            (SimplicialChain.faceSign (Fin.castSucc i) *
              W (iteratedFacetMap n 1 sigma (fun _ => pi) (Fin.castSucc i)))) +
      (∑ pi : Equiv.Perm (Fin (n + 2)),
        permSignCoeff R pi *
          (SimplicialChain.faceSign (Fin.last (n + 1)) *
            W (iteratedFacetMap n 1 sigma (fun _ => pi) (Fin.last (n + 1))))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro pi hpi
        rw [Fin.sum_univ_castSucc]
        rw [mul_add, Finset.mul_sum]
    _ = _ := by rw [hinternal, zero_add, hlast]

/-- Splitting a word into its prefix and last permutation. -/
def wordSnocEquiv (N : Nat) (A : Type) :
    ((Fin N -> A) × A) ≃ (Fin (N + 1) -> A) where
  toFun z := Fin.snoc z.1 z.2
  invFun f := (fun i => f i.castSucc, f (Fin.last N))
  left_inv := by
    rintro ⟨f, a⟩
    apply Prod.ext
    · funext i
      simp
    · simp
  right_inv := by
    intro f
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp

@[simp] theorem iteratedSign_snoc
    (R : Type) [CommRing R] (N : Nat)
    (rho : Fin N → Equiv.Perm (Fin (n + 1)))
    (pi : Equiv.Perm (Fin (n + 1))) :
    iteratedSign R (N + 1) (Fin.snoc rho pi) =
      iteratedSign R N rho * permSignCoeff R pi := by
  rw [iteratedSign, Fin.prod_univ_castSucc]
  simp [iteratedSign]

/-- Reindex a finite sum over words by their prefix and final letter. -/
theorem sum_word_snoc
    {R A : Type} [AddCommMonoid R] [Fintype A]
    (N : Nat) (f : (Fin (N + 1) → A) → R) :
    (∑ eta : Fin (N + 1) → A, f eta) =
      ∑ rho : Fin N → A, ∑ a : A, f (Fin.snoc rho a) := by
  classical
  rw [← Equiv.sum_comp (wordSnocEquiv N A)]
  rw [Fintype.sum_prod_type]
  rfl

/-- Cycle three finite sums from `a,b,c` to `b,c,a`. -/
theorem sum_cycle_left3
    {R A B C : Type} [AddCommMonoid R] [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ a, ∑ c, f a b c := by
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c, ∑ a, f a b c := by
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]

/-- Cycle three finite sums from `a,b,c` to `c,a,b`. -/
theorem sum_cycle_right3
    {R A B C : Type} [AddCommMonoid R] [Fintype A] [Fintype B] [Fintype C]
    (f : A → B → C → R) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  classical
  calc
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ c, ∑ a, ∑ b, f a b c := by
      rw [Finset.sum_comm]

@[simp] theorem iteratedFacetMap_snoc
    {X : Type} (n N : Nat) (sigma : Delta (n + 1) → X)
    (rho : Fin N → Equiv.Perm (Fin (n + 2)))
    (pi : Equiv.Perm (Fin (n + 2))) (k : Fin (n + 2)) :
    iteratedFacetMap n (N + 1) sigma (Fin.snoc rho pi) k =
      iteratedFacetMap n 1
        (fun y => sigma (affineCompMap (n + 1) N rho y)) (fun _ => pi) k := by
  funext x
  simp [iteratedFacetMap,  affineCompMap_succ]

@[simp] theorem iteratedBoundaryMap_snoc
    {X : Type} (n N : Nat) (sigma : Delta (n + 1) → X)
    (j : Fin (n + 2))
    (eta : Fin N → Equiv.Perm (Fin (n + 1)))
    (theta : Equiv.Perm (Fin (n + 1))) :
    iteratedBoundaryMap n (N + 1) sigma j (Fin.snoc eta theta) =
      fun x => iteratedBoundaryMap n N sigma j eta (affineSubdivMap n theta x) := by
  funext x
  simp [iteratedBoundaryMap, affineCompMap_snoc]

@[simp] theorem iteratedFacetMap_zero
    {X : Type} (n : Nat) (sigma : Delta (n + 1) → X)
    (rho : Fin 0 → Equiv.Perm (Fin (n + 2))) (k : Fin (n + 2)) :
    iteratedFacetMap n 0 sigma rho k = fun x => sigma (cofacePoint n k x) := by
  funext x
  simp [iteratedFacetMap]

@[simp] theorem iteratedBoundaryMap_zero
    {X : Type} (n : Nat) (sigma : Delta (n + 1) → X)
    (j : Fin (n + 2)) (rho : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    iteratedBoundaryMap n 0 sigma j rho = fun x => sigma (cofacePoint n j x) := by
  funext x
  simp [iteratedBoundaryMap]

@[simp] theorem iteratedBoundaryMap_one_after_prefix
    {X : Type} (n N : Nat) (sigma : Delta (n + 1) → X)
    (rho : Fin N → Equiv.Perm (Fin (n + 2)))
    (j : Fin (n + 2)) (theta : Equiv.Perm (Fin (n + 1))) :
    iteratedBoundaryMap n 1
        (fun y => sigma (affineCompMap (n + 1) N rho y)) j (fun _ => theta) =
      fun x => iteratedFacetMap n N sigma rho j (affineSubdivMap n theta x) := by
  funext x
  simp [iteratedBoundaryMap, iteratedFacetMap, affineCompMap_succ,
    affineSubdivContinuousMap_apply]

/-- Weighted boundary formula for an arbitrary number of barycentric subdivisions. -/
theorem iterated_weighted_boundary
    {R X : Type} [CommRing R]
    (n N : Nat) (sigma : Delta (n + 1) -> X)
    (W : (Delta n -> X) -> R) :
    (∑ rho : Fin N -> Equiv.Perm (Fin (n + 2)),
      iteratedSign R N rho *
        ∑ k : Fin (n + 2),
          SimplicialChain.faceSign k * W (iteratedFacetMap n N sigma rho k)) =
    ∑ j : Fin (n + 2),
      SimplicialChain.faceSign j *
        ∑ eta : Fin N -> Equiv.Perm (Fin (n + 1)),
          iteratedSign R N eta * W (iteratedBoundaryMap n N sigma j eta) := by
  classical
  induction N generalizing sigma W with
  | zero =>
      simp [iteratedSign]
  | succ N ih =>
      rw [sum_word_snoc N]
      simp_rw [iteratedSign_snoc, iteratedFacetMap_snoc]
      calc
        (∑ rho : Fin N → Equiv.Perm (Fin (n + 2)),
            ∑ pi : Equiv.Perm (Fin (n + 2)),
              (iteratedSign R N rho * permSignCoeff R pi) *
                ∑ k : Fin (n + 2),
                  SimplicialChain.faceSign k *
                    W (iteratedFacetMap n 1
                      (fun y => sigma (affineCompMap (n + 1) N rho y))
                      (fun _ => pi) k)) =
          ∑ rho : Fin N → Equiv.Perm (Fin (n + 2)),
            iteratedSign R N rho *
              ∑ pi : Equiv.Perm (Fin (n + 2)),
                permSignCoeff R pi *
                  ∑ k : Fin (n + 2),
                    SimplicialChain.faceSign k *
                      W (iteratedFacetMap n 1
                        (fun y => sigma (affineCompMap (n + 1) N rho y))
                        (fun _ => pi) k) := by
            apply Finset.sum_congr rfl
            intro rho hrho
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro pi hpi
            ring
        _ = ∑ rho : Fin N → Equiv.Perm (Fin (n + 2)),
            iteratedSign R N rho *
              ∑ j : Fin (n + 2),
                SimplicialChain.faceSign j *
                  ∑ theta : Equiv.Perm (Fin (n + 1)),
                    permSignCoeff R theta *
                      W (iteratedBoundaryMap n 1
                        (fun y => sigma (affineCompMap (n + 1) N rho y))
                        j (fun _ => theta)) := by
            apply Finset.sum_congr rfl
            intro rho hrho
            rw [oneStep_weighted_boundary (R := R) n
              (fun y => sigma (affineCompMap (n + 1) N rho y)) W]
        _ = ∑ theta : Equiv.Perm (Fin (n + 1)),
            permSignCoeff R theta *
              (∑ rho : Fin N → Equiv.Perm (Fin (n + 2)),
                iteratedSign R N rho *
                  ∑ j : Fin (n + 2),
                    SimplicialChain.faceSign j *
                      (fun tau => W (fun x => tau (affineSubdivMap n theta x)))
                        (iteratedFacetMap n N sigma rho j)) := by
            simp_rw [Finset.mul_sum]
            rw [sum_cycle_right3]
            apply Finset.sum_congr rfl
            intro theta htheta
            apply Finset.sum_congr rfl
            intro rho hrho
            apply Finset.sum_congr rfl
            intro j hj
            rw [iteratedBoundaryMap_one_after_prefix]
            ring
        _ = ∑ theta : Equiv.Perm (Fin (n + 1)),
            permSignCoeff R theta *
              (∑ j : Fin (n + 2),
                SimplicialChain.faceSign j *
                  ∑ eta : Fin N → Equiv.Perm (Fin (n + 1)),
                    iteratedSign R N eta *
                      W (fun x => iteratedBoundaryMap n N sigma j eta
                        (affineSubdivMap n theta x))) := by
            apply Finset.sum_congr rfl
            intro theta htheta
            rw [ih (sigma := sigma)
              (W := fun tau => W (fun x => tau (affineSubdivMap n theta x)))]
        _ = ∑ j : Fin (n + 2),
            SimplicialChain.faceSign j *
              ∑ eta : Fin (N + 1) → Equiv.Perm (Fin (n + 1)),
                iteratedSign R (N + 1) eta *
                  W (iteratedBoundaryMap n (N + 1) sigma j eta) := by
            simp_rw [Finset.mul_sum]
            rw [sum_cycle_left3]
            apply Finset.sum_congr rfl
            intro j hj
            rw [sum_word_snoc N]
            apply Finset.sum_congr rfl
            intro eta heta
            apply Finset.sum_congr rfl
            intro theta htheta
            rw [iteratedSign_snoc, iteratedBoundaryMap_snoc]
            ring

/-! ## Staircase prism boundary -/

/-- Generic staircase time coordinate for a spatial `n`-simplex. -/
def genericStaircaseTime
    (k : Fin (n + 1)) (j : Fin (n + 2)) : Fin 2 :=
  if j.1 <= k.1 then 0 else 1

/-- Generic staircase spatial vertex. -/
def genericStaircaseSpatial
    (k : Fin (n + 1)) (j : Fin (n + 2)) : Fin (n + 1) :=
  if h : j.1 <= k.1 then
    ⟨j.1, lt_of_le_of_lt h k.2⟩
  else
    ⟨j.1 - 1, by have := j.2; have := Nat.lt_of_not_ge h; omega⟩

@[simp] theorem genericStaircaseSpatial_val
    (k : Fin (n + 1)) (j : Fin (n + 2)) :
    (genericStaircaseSpatial k j).1 =
      if j.1 ≤ k.1 then j.1 else j.1 - 1 := by
  unfold genericStaircaseSpatial
  split_ifs <;> rfl

/-- Spatial barycentric point in the generic staircase simplex. -/
noncomputable def genericStaircaseSpatialPoint
    (n : Nat) (k : Fin (n + 1)) (w : Delta (n + 1)) : Delta n := by
  refine ⟨fun i => ∑ j : Fin (n + 2),
      if genericStaircaseSpatial k j = i then w j else 0, ?_⟩
  constructor
  · intro i
    exact Finset.sum_nonneg fun j _ => by
      by_cases h : genericStaircaseSpatial k j = i
      · simp [h]
      · simp [h]
  · calc
      (∑ i, ∑ j : Fin (n + 2),
          if genericStaircaseSpatial k j = i then w j else 0) =
          ∑ j : Fin (n + 2), w j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        rw [Finset.sum_eq_single (genericStaircaseSpatial k j)]
        · simp
        · intro i hi hne
          rw [ite_eq_right (Ne.symm hne)]
        · simp
      _ = 1 := w.2.2

/-- Interval barycentric point in the generic staircase simplex. -/
noncomputable def genericStaircaseIntervalPoint
    (n : Nat) (k : Fin (n + 1)) (w : Delta (n + 1)) : Set.Icc (0 : Real) 1 := by
  refine ⟨∑ j : Fin (n + 2),
      if genericStaircaseTime k j = 1 then w j else 0, ?_⟩
  constructor
  · exact Finset.sum_nonneg fun j _ => by
      by_cases h : genericStaircaseTime k j = 1
      · simp [h]
      · simp [h]
  · calc
      (∑ j : Fin (n + 2), if genericStaircaseTime k j = 1 then w j else 0)
          <= ∑ j : Fin (n + 2), w j := by
            apply Finset.sum_le_sum
            intro j hj
            by_cases h : genericStaircaseTime k j = 1
            · simp [h]
            · simp [h]
      _ = 1 := w.2.2

/-- Generic staircase prism simplex over a spatial simplex map. -/
noncomputable def staircasePrismMap
    {X : Type} (n : Nat) (sigma : Delta n -> X) (k : Fin (n + 1)) :
    Delta (n + 1) -> X × Set.Icc (0 : Real) 1 :=
  fun w => (sigma (genericStaircaseSpatialPoint n k w),
    genericStaircaseIntervalPoint n k w)

/-- Lower endpoint copy of a spatial simplex map. -/
def lowerEndpointMap
    {X : Type} (sigma : Delta n -> X) : Delta n -> X × Set.Icc (0 : Real) 1 :=
  fun x => (sigma x, ⟨0, by constructor <;> norm_num⟩)

/-- Upper endpoint copy of a spatial simplex map. -/
def upperEndpointMap
    {X : Type} (sigma : Delta n -> X) : Delta n -> X × Set.Icc (0 : Real) 1 :=
  fun x => (sigma x, ⟨1, by constructor <;> norm_num⟩)

/-- A side staircase simplex over an original spatial face. -/
noncomputable def sidePrismMap
    {X : Type} (n : Nat) (sigma : Delta n -> X)
    (r : Fin (n + 1)) (h : Fin n) :
    Delta n -> X × Set.Icc (0 : Real) 1 := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by
    intro hn0
    subst n
    exact Fin.elim0 h)
  let r' : Fin ((n - 1) + 2) := Fin.cast (by omega) r
  let h' : Fin ((n - 1) + 1) := Fin.cast (by omega) h
  let sigma' : Delta (n - 1) → X := fun x =>
    sigma (deltaCast (Nat.sub_add_cancel hn) (cofacePoint (n - 1) r' x))
  exact fun x => staircasePrismMap (n - 1) sigma' h'
    (deltaCast (Nat.sub_add_cancel hn).symm x)

/-- Away from the duplicated staircase vertex, adjacent staircase simplices have the same
spatial label. -/
theorem genericStaircaseSpatial_adjacent_of_ne
    (h : Fin n) (j : Fin (n + 2))
    (hj : j ≠ (Fin.succ h).castSucc) :
    genericStaircaseSpatial h.castSucc j =
      genericStaircaseSpatial (Fin.succ h) j := by
  have hjval : j.1 ≠ h.1 + 1 := by
    intro heq
    apply hj
    apply Fin.ext
    simpa [Fin.val_succ, Fin.val_castSucc] using heq
  apply Fin.ext
  simp only [genericStaircaseSpatial, Fin.val_succ, Fin.val_castSucc]
  split <;> split <;> omega

/-- Away from the duplicated staircase vertex, adjacent staircase simplices have the same
interval label. -/
theorem genericStaircaseTime_adjacent_of_ne
    (h : Fin n) (j : Fin (n + 2))
    (hj : j ≠ (Fin.succ h).castSucc) :
    genericStaircaseTime h.castSucc j =
      genericStaircaseTime (Fin.succ h) j := by
  have hjval : j.1 ≠ h.1 + 1 := by
    intro heq
    apply hj
    apply Fin.ext
    simpa [Fin.val_succ, Fin.val_castSucc] using heq
  simp only [genericStaircaseTime, Fin.val_succ, Fin.val_castSucc]
  split <;> split <;> omega

/-- The spatial barycentric coordinates agree on the common internal face of two adjacent
staircase simplices. -/
theorem genericStaircaseSpatialPoint_internal_face
    (n : Nat) (h : Fin n) (x : Delta n) :
    genericStaircaseSpatialPoint n h.castSucc
        (cofacePoint n (Fin.succ h).castSucc x) =
      genericStaircaseSpatialPoint n (Fin.succ h)
        (cofacePoint n (Fin.succ h).castSucc x) := by
  apply SphereOddDegree.FiniteSimplex.ext
  funext i
  change
    (∑ j : Fin (n + 2),
      if genericStaircaseSpatial h.castSucc j = i then
        cofacePoint n (Fin.succ h).castSucc x j else 0) =
    ∑ j : Fin (n + 2),
      if genericStaircaseSpatial (Fin.succ h) j = i then
        cofacePoint n (Fin.succ h).castSucc x j else 0
  apply Finset.sum_congr rfl
  intro j hjmem
  by_cases hj : j = (Fin.succ h).castSucc
  · subst j
    simp
  · rw [genericStaircaseSpatial_adjacent_of_ne h j hj]

/-- The interval coordinate agrees on the common internal face of two adjacent staircase
simplices. -/
theorem genericStaircaseIntervalPoint_internal_face
    (n : Nat) (h : Fin n) (x : Delta n) :
    genericStaircaseIntervalPoint n h.castSucc
        (cofacePoint n (Fin.succ h).castSucc x) =
      genericStaircaseIntervalPoint n (Fin.succ h)
        (cofacePoint n (Fin.succ h).castSucc x) := by
  apply Subtype.ext
  change
    (∑ j : Fin (n + 2),
      if genericStaircaseTime h.castSucc j = 1 then
        cofacePoint n (Fin.succ h).castSucc x j else 0) =
    ∑ j : Fin (n + 2),
      if genericStaircaseTime (Fin.succ h) j = 1 then
        cofacePoint n (Fin.succ h).castSucc x j else 0
  apply Finset.sum_congr rfl
  intro j hjmem
  by_cases hj : j = (Fin.succ h).castSucc
  · subst j
    simp
  · rw [genericStaircaseTime_adjacent_of_ne h j hj]

/-- Pairing of the two internal facets between adjacent staircase simplices. -/
theorem staircase_internal_face_eq
    {X : Type} (n : Nat) (sigma : Delta n -> X) (h : Fin n) :
    (fun x => staircasePrismMap n sigma h.castSucc
      (cofacePoint n (Fin.succ h).castSucc x)) =
    (fun x => staircasePrismMap n sigma (Fin.succ h)
      (cofacePoint n (Fin.succ h).castSucc x)) := by
  funext x
  apply Prod.ext
  · exact congrArg sigma (genericStaircaseSpatialPoint_internal_face n h x)
  · exact genericStaircaseIntervalPoint_internal_face n h x

/-- Combinatorial classes of facets in the standard staircase triangulation.  The two `Unit`
summands are the upper and lower horizontal facets, the two `Fin n` summands are the two copies of
each internal facet, and the final product indexes spatial-side facets. -/
abbrev StaircaseFacetClass (n : Nat) :=
  Unit ⊕ (Unit ⊕ ((Fin n ⊕ Fin n) ⊕ (Fin (n + 1) × Fin n)))

/-- Classify a facet occurrence of a staircase simplex. -/
noncomputable def staircaseFacetClassify
    (n : Nat) (z : Fin (n + 1) × Fin (n + 2)) : StaircaseFacetClass n :=
  if hlt : z.2.1 < z.1.1 then
    Sum.inr (Sum.inr (Sum.inr
      (⟨z.2.1, by omega⟩, ⟨z.1.1 - 1, by omega⟩)))
  else if heq : z.2.1 = z.1.1 then
    if hz : z.1.1 = 0 then
      Sum.inl ()
    else
      Sum.inr (Sum.inr (Sum.inl (Sum.inl ⟨z.1.1 - 1, by omega⟩)))
  else if hnext : z.2.1 = z.1.1 + 1 then
    if hlast : z.1.1 = n then
      Sum.inr (Sum.inl ())
    else
      Sum.inr (Sum.inr (Sum.inl (Sum.inr ⟨z.1.1, by omega⟩)))
  else
    Sum.inr (Sum.inr (Sum.inr
      (⟨z.2.1 - 1, by omega⟩, ⟨z.1.1, by omega⟩)))

/-- Recover the unique staircase-simplex facet occurrence from its combinatorial class. -/
def staircaseFacetUnclassify
    (n : Nat) : StaircaseFacetClass n → Fin (n + 1) × Fin (n + 2)
  | Sum.inl _ => (0, 0)
  | Sum.inr (Sum.inl _) => (Fin.last n, Fin.last (n + 1))
  | Sum.inr (Sum.inr (Sum.inl (Sum.inl h))) =>
      (Fin.succ h, (Fin.succ h).castSucc)
  | Sum.inr (Sum.inr (Sum.inl (Sum.inr h))) =>
      (h.castSucc, (Fin.succ h).castSucc)
  | Sum.inr (Sum.inr (Sum.inr (r, h))) =>
      if r.1 ≤ h.1 then (Fin.succ h, r.castSucc)
      else (h.castSucc, Fin.succ r)

/-- The complete finite partition of staircase facet occurrences. -/
noncomputable def staircaseFacetEquiv
    (n : Nat) : (Fin (n + 1) × Fin (n + 2)) ≃ StaircaseFacetClass n where
  toFun := staircaseFacetClassify n
  invFun := staircaseFacetUnclassify n
  left_inv := by
    intro z
    rcases z with ⟨k, j⟩
    by_cases hlt : j.1 < k.1
    · have hside : j.1 ≤ k.1 - 1 := by omega
      apply Prod.ext
      · apply Fin.ext
        simp [staircaseFacetClassify, staircaseFacetUnclassify, hlt, hside]
        omega
      · apply Fin.ext
        simp [staircaseFacetClassify, staircaseFacetUnclassify, hlt, hside]
    · by_cases heq : j.1 = k.1
      · by_cases hz : k.1 = 0
        · apply Prod.ext <;> apply Fin.ext <;>
            simp [staircaseFacetClassify, staircaseFacetUnclassify,  heq, hz]
        · apply Prod.ext <;> apply Fin.ext <;>
            simp [staircaseFacetClassify, staircaseFacetUnclassify,  heq, hz] <;> omega
      · by_cases hnext : j.1 = k.1 + 1
        · by_cases hlast : k.1 = n
          · apply Prod.ext <;> apply Fin.ext <;>
              simp [staircaseFacetClassify, staircaseFacetUnclassify,
                hnext, hlast]
          · apply Prod.ext <;> apply Fin.ext <;>
              simp [staircaseFacetClassify, staircaseFacetUnclassify,
                hnext, hlast]
        · have hfar : k.1 + 1 < j.1 := by omega
          have hside : ¬ j.1 - 1 ≤ k.1 := by omega
          apply Prod.ext
          · apply Fin.ext
            simp [staircaseFacetClassify, staircaseFacetUnclassify, hlt, heq,
              hnext, hside]
          · apply Fin.ext
            simp [staircaseFacetClassify, staircaseFacetUnclassify, hlt, heq,
              hnext, hside]
            omega
  right_inv := by
    intro c
    rcases c with _ | c
    · simp [staircaseFacetClassify, staircaseFacetUnclassify]
    · rcases c with _ | c
      · simp [staircaseFacetClassify, staircaseFacetUnclassify]
      · rcases c with c | c
        · rcases c with h | h
          · simp [staircaseFacetClassify, staircaseFacetUnclassify]
          · have hh : h.1 ≠ n := by exact Nat.ne_of_lt h.isLt
            simp [staircaseFacetClassify, staircaseFacetUnclassify, hh]
        · rcases c with ⟨r, h⟩
          by_cases hrh : r.1 ≤ h.1
          · simp [staircaseFacetClassify, staircaseFacetUnclassify, hrh]
          · have hhr : h.1 < r.1 := Nat.lt_of_not_ge hrh
            have hrle : r.1 ≤ n := Nat.le_of_lt_succ r.isLt
            have hnot : ¬ r.1 ≤ h.1 := hrh
            have hlt' : ¬ r.1 + 1 < h.1 := by omega
            have heq' : r.1 + 1 ≠ h.1 := by omega
            have hnext' : r.1 ≠ h.1 := by omega
            simp [staircaseFacetClassify, staircaseFacetUnclassify,
              hlt', heq', hnext', hnot]

/-- The explicit spatial barycentric formula is the standard-simplex pushforward. -/
theorem genericStaircaseSpatialPoint_eq_map
    (n : Nat) (k : Fin (n + 1)) (w : Delta (n + 1)) :
    genericStaircaseSpatialPoint n k w =
      SphereOddDegree.FiniteSimplex.map (S := Real) (genericStaircaseSpatial k) w := by
  apply SphereOddDegree.FiniteSimplex.ext
  funext i
  rw [SphereOddDegree.FiniteSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  simp only [genericStaircaseSpatialPoint]
  rw [Finset.sum_filter]
  rfl

/-- The generic staircase interval coordinate is coordinate `1` of the simplex pushforward
along `genericStaircaseTime`. -/
theorem genericStaircaseIntervalPoint_eq_map_apply_one
    (n : Nat) (k : Fin (n + 1)) (w : Delta (n + 1)) :
    (genericStaircaseIntervalPoint n k w).1 =
      SphereOddDegree.FiniteSimplex.map (S := Real) (genericStaircaseTime k) w (1 : Fin 2) := by
  rw [SphereOddDegree.FiniteSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  simp only [genericStaircaseIntervalPoint]
  rw [Finset.sum_filter]

/-- Deleting a spatial vertex weakly before the staircase break commutes with the spatial
staircase projection. -/
theorem genericStaircaseSpatial_succ_comp_sideCoface_of_le
    (n : Nat) (r : Fin (n + 2)) (h : Fin (n + 1)) (hrh : r.1 ≤ h.1) :
    genericStaircaseSpatial (Fin.succ h) ∘ r.castSucc.succAbove =
      r.succAbove ∘ genericStaircaseSpatial h := by
  funext i
  apply Fin.ext
  simp only [Function.comp_apply, genericStaircaseSpatial_val, Fin.val_succ,
    Fin.val_castSucc, fin_succAbove_val]
  split_ifs <;> omega

/-- Deleting a spatial vertex weakly before the staircase break commutes with the interval
staircase projection. -/
theorem genericStaircaseTime_succ_comp_sideCoface_of_le
    (n : Nat) (r : Fin (n + 2)) (h : Fin (n + 1)) (hrh : r.1 ≤ h.1) :
    genericStaircaseTime (Fin.succ h) ∘ r.castSucc.succAbove =
      genericStaircaseTime h := by
  funext i
  apply Fin.ext
  simp only [Function.comp_apply, genericStaircaseTime, Fin.val_succ,
    Fin.val_castSucc, fin_succAbove_val]
  split_ifs <;> omega

/-- Deleting a spatial vertex after the staircase break commutes with the spatial staircase
projection. -/
theorem genericStaircaseSpatial_castSucc_comp_sideCoface_of_gt
    (n : Nat) (r : Fin (n + 2)) (h : Fin (n + 1)) (hrh : h.1 < r.1) :
    genericStaircaseSpatial h.castSucc ∘ (Fin.succ r).succAbove =
      r.succAbove ∘ genericStaircaseSpatial h := by
  funext i
  apply Fin.ext
  simp only [Function.comp_apply, genericStaircaseSpatial_val, Fin.val_succ,
    Fin.val_castSucc, fin_succAbove_val]
  split_ifs <;> omega

/-- Deleting a spatial vertex after the staircase break commutes with the interval staircase
projection. -/
theorem genericStaircaseTime_castSucc_comp_sideCoface_of_gt
    (n : Nat) (r : Fin (n + 2)) (h : Fin (n + 1)) (hrh : h.1 < r.1) :
    genericStaircaseTime h.castSucc ∘ (Fin.succ r).succAbove =
      genericStaircaseTime h := by
  funext i
  apply Fin.ext
  simp only [Function.comp_apply, genericStaircaseTime, Fin.val_succ,
    Fin.val_castSucc, fin_succAbove_val]
  split_ifs <;> omega

/-- Spatial-point naturality for a side face weakly before the staircase break. -/
theorem genericStaircaseSpatialPoint_side_of_le
    (n : Nat) (r : Fin (n + 2)) (h : Fin (n + 1)) (hrh : r.1 ≤ h.1)
    (x : Delta (n + 1)) :
    genericStaircaseSpatialPoint (n + 1) (Fin.succ h)
        (cofacePoint (n + 1) r.castSucc x) =
      cofacePoint n r (genericStaircaseSpatialPoint n h x) := by
  calc
    genericStaircaseSpatialPoint (n + 1) (Fin.succ h)
        (cofacePoint (n + 1) r.castSucc x) =
      SphereOddDegree.FiniteSimplex.map (S := Real)
        (genericStaircaseSpatial (Fin.succ h) ∘ r.castSucc.succAbove) x := by
          rw [genericStaircaseSpatialPoint_eq_map, cofacePoint,
            SphereOddDegree.FiniteSimplex.map_comp_apply]
    _ = SphereOddDegree.FiniteSimplex.map (S := Real)
        (r.succAbove ∘ genericStaircaseSpatial h) x := by
          rw [genericStaircaseSpatial_succ_comp_sideCoface_of_le n r h hrh]
    _ = cofacePoint n r (genericStaircaseSpatialPoint n h x) := by
          rw [genericStaircaseSpatialPoint_eq_map, cofacePoint,
            SphereOddDegree.FiniteSimplex.map_comp_apply]

/-- Interval-point naturality for a side face weakly before the staircase break. -/
theorem genericStaircaseIntervalPoint_side_of_le
    (n : Nat) (r : Fin (n + 2)) (h : Fin (n + 1)) (hrh : r.1 ≤ h.1)
    (x : Delta (n + 1)) :
    genericStaircaseIntervalPoint (n + 1) (Fin.succ h)
        (cofacePoint (n + 1) r.castSucc x) =
      genericStaircaseIntervalPoint n h x := by
  apply Subtype.ext
  calc
    (genericStaircaseIntervalPoint (n + 1) (Fin.succ h)
        (cofacePoint (n + 1) r.castSucc x)).1 =
      SphereOddDegree.FiniteSimplex.map (S := Real)
        (genericStaircaseTime (Fin.succ h) ∘ r.castSucc.succAbove) x
          (1 : Fin 2) := by
            rw [genericStaircaseIntervalPoint_eq_map_apply_one, cofacePoint,
              SphereOddDegree.FiniteSimplex.map_comp_apply]
    _ = SphereOddDegree.FiniteSimplex.map (S := Real) (genericStaircaseTime h) x (1 : Fin 2) := by
          rw [genericStaircaseTime_succ_comp_sideCoface_of_le n r h hrh]
    _ = (genericStaircaseIntervalPoint n h x).1 := by
          rw [genericStaircaseIntervalPoint_eq_map_apply_one]

/-- Spatial-point naturality for a side face after the staircase break. -/
theorem genericStaircaseSpatialPoint_side_of_gt
    (n : Nat) (r : Fin (n + 2)) (h : Fin (n + 1)) (hrh : h.1 < r.1)
    (x : Delta (n + 1)) :
    genericStaircaseSpatialPoint (n + 1) h.castSucc
        (cofacePoint (n + 1) (Fin.succ r) x) =
      cofacePoint n r (genericStaircaseSpatialPoint n h x) := by
  calc
    genericStaircaseSpatialPoint (n + 1) h.castSucc
        (cofacePoint (n + 1) (Fin.succ r) x) =
      SphereOddDegree.FiniteSimplex.map (S := Real)
        (genericStaircaseSpatial h.castSucc ∘ (Fin.succ r).succAbove) x := by
          rw [genericStaircaseSpatialPoint_eq_map, cofacePoint,
            SphereOddDegree.FiniteSimplex.map_comp_apply]
    _ = SphereOddDegree.FiniteSimplex.map (S := Real)
        (r.succAbove ∘ genericStaircaseSpatial h) x := by
          rw [genericStaircaseSpatial_castSucc_comp_sideCoface_of_gt n r h hrh]
    _ = cofacePoint n r (genericStaircaseSpatialPoint n h x) := by
          rw [genericStaircaseSpatialPoint_eq_map, cofacePoint,
            SphereOddDegree.FiniteSimplex.map_comp_apply]

/-- Interval-point naturality for a side face after the staircase break. -/
theorem genericStaircaseIntervalPoint_side_of_gt
    (n : Nat) (r : Fin (n + 2)) (h : Fin (n + 1)) (hrh : h.1 < r.1)
    (x : Delta (n + 1)) :
    genericStaircaseIntervalPoint (n + 1) h.castSucc
        (cofacePoint (n + 1) (Fin.succ r) x) =
      genericStaircaseIntervalPoint n h x := by
  apply Subtype.ext
  calc
    (genericStaircaseIntervalPoint (n + 1) h.castSucc
        (cofacePoint (n + 1) (Fin.succ r) x)).1 =
      SphereOddDegree.FiniteSimplex.map (S := Real)
        (genericStaircaseTime h.castSucc ∘ (Fin.succ r).succAbove) x
          (1 : Fin 2) := by
            rw [genericStaircaseIntervalPoint_eq_map_apply_one, cofacePoint,
              SphereOddDegree.FiniteSimplex.map_comp_apply]
    _ = SphereOddDegree.FiniteSimplex.map (S := Real) (genericStaircaseTime h) x (1 : Fin 2) := by
          rw [genericStaircaseTime_castSucc_comp_sideCoface_of_gt n r h hrh]
    _ = (genericStaircaseIntervalPoint n h x).1 := by
          rw [genericStaircaseIntervalPoint_eq_map_apply_one]
/-- The first facet of the first staircase simplex is the upper endpoint. -/
theorem staircase_upper_face_eq
    {X : Type} (n : Nat) (sigma : Delta n → X) :
    (fun x => staircasePrismMap n sigma 0 (cofacePoint n 0 x)) =
      upperEndpointMap sigma := by
  funext x
  apply Prod.ext
  · apply congrArg sigma
    rw [genericStaircaseSpatialPoint_eq_map, cofacePoint,
      SphereOddDegree.FiniteSimplex.map_comp_apply]
    have hf : genericStaircaseSpatial (0 : Fin (n + 1)) ∘
        Fin.succAbove (0 : Fin (n + 2)) = id := by
      funext i
      apply Fin.ext
      simp [genericStaircaseSpatial]
    rw [hf]
    apply SphereOddDegree.FiniteSimplex.ext
    funext i
    rw [SphereOddDegree.FiniteSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_eq_single i (by simp) (by simp)
  · apply Subtype.ext
    simp only [staircasePrismMap, upperEndpointMap,
      genericStaircaseIntervalPoint, genericStaircaseTime]
    rw [Fin.sum_univ_succ]
    simp +instances only [Fin.val_zero, zero_le, ↓reduceIte, Fin.val_succ]
    have hs : (∑ i : Fin (n + 1), cofacePoint n 0 x i.succ) =
        ∑ i : Fin (n + 1), x i := by
      apply Finset.sum_congr rfl
      intro i hi
      simpa using cofacePoint_apply_succAbove n 0 x i
    simp only [zero_ne_one, ↓reduceIte]
    change (0 + ∑ i : Fin (n + 1),
      if (if i.val + 1 ≤ 0 then (0 : Fin 2) else 1) = 1
      then cofacePoint n 0 x i.succ else 0) = 1
    have hpos : ∀ i : Fin (n + 1), ¬ i.val + 1 ≤ 0 := by intro i; omega
    simp_rw [ite_eq_right (hpos _)]
    simp only [↓reduceIte, zero_add]
    rw [hs]
    exact x.2.2
/-- The last facet of the last staircase simplex is the lower endpoint. -/
theorem staircase_lower_face_eq
    {X : Type} (n : Nat) (sigma : Delta n → X) :
    (fun x => staircasePrismMap n sigma (Fin.last n)
      (cofacePoint n (Fin.last (n + 1)) x)) = lowerEndpointMap sigma := by
  funext x
  apply Prod.ext
  · apply congrArg sigma
    rw [genericStaircaseSpatialPoint_eq_map, cofacePoint,
      SphereOddDegree.FiniteSimplex.map_comp_apply]
    have hf : genericStaircaseSpatial (Fin.last n) ∘
        (Fin.last (n + 1)).succAbove = id := by
      funext i
      apply Fin.ext
      simp only [Function.comp_apply]
      rw [Fin.succAbove_last]
      simp only [genericStaircaseSpatial]
      have hi : i.1 ≤ n := by omega
      simp [hi]
    rw [hf]
    apply SphereOddDegree.FiniteSimplex.ext
    funext i
    rw [SphereOddDegree.FiniteSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_eq_single i (by simp) (by simp)
  · apply Subtype.ext
    simp only [staircasePrismMap, lowerEndpointMap,
      genericStaircaseIntervalPoint, genericStaircaseTime]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hni : n < i.1
    · have hilast : i = Fin.last (n + 1) := by apply Fin.ext; simp; omega
      subst i
      simp [cofacePoint_apply_deleted]
    · simp [hni]
/-- Side facet formula when the deleted spatial vertex occurs weakly before the staircase break. -/
theorem staircase_side_face_of_le
    {X : Type} (n : Nat) (sigma : Delta n → X)
    (r : Fin (n + 1)) (h : Fin n) (hrh : r.1 ≤ h.1) :
    (fun x => staircasePrismMap n sigma (Fin.succ h)
      (cofacePoint n r.castSucc x)) = sidePrismMap n sigma r h := by
  cases n with
  | zero => exact Fin.elim0 h
  | succ n =>
      funext x
      apply Prod.ext
      · simpa [sidePrismMap, staircasePrismMap, deltaCast] using
          congrArg sigma (genericStaircaseSpatialPoint_side_of_le n r h hrh x)
      · simpa [sidePrismMap, staircasePrismMap, deltaCast] using
          genericStaircaseIntervalPoint_side_of_le n r h hrh x
/-- Side facet formula when the deleted spatial vertex occurs after the staircase break. -/
theorem staircase_side_face_of_gt
    {X : Type} (n : Nat) (sigma : Delta n → X)
    (r : Fin (n + 1)) (h : Fin n) (hrh : h.1 < r.1) :
    (fun x => staircasePrismMap n sigma h.castSucc
      (cofacePoint n (Fin.succ r) x)) = sidePrismMap n sigma r h := by
  cases n with
  | zero => exact Fin.elim0 h
  | succ n =>
      funext x
      apply Prod.ext
      · simpa [sidePrismMap, staircasePrismMap, deltaCast] using
          congrArg sigma (genericStaircaseSpatialPoint_side_of_gt n r h hrh x)
      · simpa [sidePrismMap, staircasePrismMap, deltaCast] using
          genericStaircaseIntervalPoint_side_of_gt n r h hrh x

/-- Sum decomposition induced by the staircase facet partition. -/
theorem staircaseFacet_sum_decomposition
    {M : Type} [AddCommMonoid M]
    (n : Nat) (F : Fin (n + 1) → Fin (n + 2) → M) :
    (∑ k : Fin (n + 1), ∑ j : Fin (n + 2), F k j) =
      F 0 0 +
        (F (Fin.last n) (Fin.last (n + 1)) +
          ((∑ h : Fin n, F (Fin.succ h) (Fin.succ h).castSucc) +
            (∑ h : Fin n, F h.castSucc (Fin.succ h).castSucc)) +
          ∑ r : Fin (n + 1), ∑ h : Fin n,
            if r.1 ≤ h.1 then F (Fin.succ h) r.castSucc
            else F h.castSucc (Fin.succ r)) := by
  rw [← Fintype.sum_prod_type (fun z : Fin (n + 1) × Fin (n + 2) => F z.1 z.2)]
  calc
    (∑ z : Fin (n + 1) × Fin (n + 2), F z.1 z.2) =
        ∑ c : StaircaseFacetClass n,
          F (staircaseFacetUnclassify n c).1
            (staircaseFacetUnclassify n c).2 := by
      apply Fintype.sum_equiv (staircaseFacetEquiv n)
      intro z
      have hz := (staircaseFacetEquiv n).left_inv z
      exact congrArg (fun z => F z.1 z.2) hz.symm
    _ = _ := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type,
        Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
      simp [staircaseFacetUnclassify]
      have hs :
          (∑ r : Fin (n + 1), ∑ h : Fin n,
            F (if r.1 ≤ h.1 then (Fin.succ h, r.castSucc)
              else (h.castSucc, Fin.succ r)).1
              (if r.1 ≤ h.1 then (Fin.succ h, r.castSucc)
              else (h.castSucc, Fin.succ r)).2) =
          ∑ r : Fin (n + 1), ∑ h : Fin n,
            if r.1 ≤ h.1 then F (Fin.succ h) r.castSucc
            else F h.castSucc (Fin.succ r) := by
        apply Finset.sum_congr rfl
        intro r hr
        apply Finset.sum_congr rfl
        intro h hh
        by_cases hrh : r.1 ≤ h.1 <;> simp [hrh]
      rw [hs]
      ac_rfl

/-- The square of every power of `-1` is one. -/
theorem negOnePow_mul_self
    {R : Type} [CommRing R] (m : Nat) :
    ((-1 : R) ^ m) * ((-1 : R) ^ m) = 1 := by
  rw [← pow_add]
  simp [← two_mul]

/-- Boundary formula for the staircase triangulation, after evaluation by an arbitrary weight. -/
theorem staircase_weighted_boundary
    {R X : Type} [CommRing R]
    (n : Nat) (sigma : Delta n -> X)
    (W : (Delta n -> X × Set.Icc (0 : Real) 1) -> R) :
    (∑ k : Fin (n + 1),
      ((-1 : R) ^ k.1) *
        ∑ j : Fin (n + 2),
          SimplicialChain.faceSign j *
            W (fun x => staircasePrismMap n sigma k (cofacePoint n j x))) =
      W (upperEndpointMap sigma) - W (lowerEndpointMap sigma) -
        ∑ r : Fin (n + 1),
          ((-1 : R) ^ r.1) *
            ∑ h : Fin n,
              ((-1 : R) ^ h.1) * W (sidePrismMap n sigma r h) := by
  classical
  let F : Fin (n + 1) -> Fin (n + 2) -> R := fun k j =>
    ((-1 : R) ^ k.1) *
      (SimplicialChain.faceSign j *
        W (fun x => staircasePrismMap n sigma k (cofacePoint n j x)))
  have hupper : F 0 0 = W (upperEndpointMap sigma) := by
    dsimp [F]
    rw [staircase_upper_face_eq]
    simp [SimplicialChain.faceSign]
  have hlower : F (Fin.last n) (Fin.last (n + 1)) =
      -W (lowerEndpointMap sigma) := by
    dsimp [F]
    rw [staircase_lower_face_eq]
    simp only [SimplicialChain.faceSign, Fin.val_last]
    rw [pow_succ]
    calc
      ((-1 : R) ^ n) *
          (((-1 : R) ^ n * -1) * W (lowerEndpointMap sigma)) =
        (((-1 : R) ^ n) * ((-1 : R) ^ n)) *
          (-1 * W (lowerEndpointMap sigma)) := by ring
      _ = -W (lowerEndpointMap sigma) := by
        rw [negOnePow_mul_self]
        ring
  have hinternal :
      ((∑ h : Fin n, F (Fin.succ h) (Fin.succ h).castSucc) +
        (∑ h : Fin n, F h.castSucc (Fin.succ h).castSucc)) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro h hh
    dsimp [F]
    have hi : h.castSucc.succ = (Fin.succ h).castSucc := by
      apply Fin.ext
      simp [Fin.val_succ, Fin.val_castSucc]
    rw [hi, ← staircase_internal_face_eq n sigma h]
    simp only [SimplicialChain.faceSign,   pow_succ]
    ring
  have hside :
      (∑ r : Fin (n + 1), ∑ h : Fin n,
        if r.1 <= h.1 then F (Fin.succ h) r.castSucc
        else F h.castSucc (Fin.succ r)) =
      -∑ r : Fin (n + 1),
        ((-1 : R) ^ r.1) *
          ∑ h : Fin n, ((-1 : R) ^ h.1) * W (sidePrismMap n sigma r h) := by
    calc
      (∑ r : Fin (n + 1), ∑ h : Fin n,
        if r.1 <= h.1 then F (Fin.succ h) r.castSucc
        else F h.castSucc (Fin.succ r)) =
          ∑ r : Fin (n + 1), ∑ h : Fin n,
            -((( -1 : R) ^ r.1) *
              (((-1 : R) ^ h.1) * W (sidePrismMap n sigma r h))) := by
            apply Finset.sum_congr rfl
            intro r hr
            apply Finset.sum_congr rfl
            intro h hh
            by_cases hrh : r.1 <= h.1
            · rw [ite_eq_left hrh]
              dsimp [F]
              rw [staircase_side_face_of_le n sigma r h hrh]
              simp only [SimplicialChain.faceSign,
                 Fin.val_castSucc]
              rw [pow_succ]
              ring
            · rw [ite_eq_right hrh]
              have hhr : h.1 < r.1 := Nat.lt_of_not_ge hrh
              dsimp [F]
              rw [staircase_side_face_of_gt n sigma r h hhr]
              simp only [SimplicialChain.faceSign, Fin.val_succ,
                Fin.castSucc_mk]
              rw [pow_succ]
              ring
      _ = -∑ r : Fin (n + 1),
          ((-1 : R) ^ r.1) *
            ∑ h : Fin n, ((-1 : R) ^ h.1) * W (sidePrismMap n sigma r h) := by
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro r hr
        rw [← Finset.sum_neg_distrib]
  simp_rw [Finset.mul_sum]
  change (∑ k : Fin (n + 1), ∑ j : Fin (n + 2), F k j) = _
  rw [staircaseFacet_sum_decomposition n F, hupper, hlower, hinternal, hside]
  simp_rw [Finset.mul_sum]
  ring

/-! ## From local occurrence sums to the orbit-cycle side sum -/

/-- The coface point of a facet occurrence, transported to the ambient `p`-simplex. -/
noncomputable def occurrenceCofacePoint
    (hp : Nat.Prime p) (k : Fin (p + 1)) (x : Delta (p - 1)) : Delta p :=
  deltaCast (Nat.sub_add_cancel hp.pos)
    (cofacePoint (p - 1) (facetFaceIndex hp k) x)

/-- The actual affine facet map of one local prism occurrence. -/
noncomputable def occurrenceFacetMap
    (hp : Nat.Prime p) (N L : Nat)
    (o : FacetOccurrence hp N L) :
    Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1 :=
  fun x => SubdivisionPrismCharts.chart hp N L o.1
    (occurrenceCofacePoint hp o.2 x)

@[simp] theorem occurrenceCofacePoint_vertex
    (hp : Nat.Prime p) (k : Fin (p + 1)) (i : Fin p) :
    occurrenceCofacePoint hp k
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) (facetCoordinateIndex i)) =
      SphereOddDegree.FiniteSimplex.vertex (S := Real) (k.succAbove i) := by
  unfold occurrenceCofacePoint
  rw [cofacePoint_vertex, deltaCast_vertex]
  congr 1
  apply Fin.ext
  simp only [Fin.val_cast, facetFaceIndex_val, facetCoordinateIndex,
    Fin.val_castLE, fin_succAbove_val]
  rfl

@[simp] theorem occurrenceFacetMap_vertex
    (hp : Nat.Prime p) (N L : Nat)
    (o : FacetOccurrence hp N L) (i : Fin p) :
    occurrenceFacetMap hp N L o
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) (facetCoordinateIndex i)) =
      SubdivisionPrismCharts.vertex hp N L o.1 (o.2.succAbove i) := by
  simp [occurrenceFacetMap, SubdivisionPrismCharts.vertex]

/-- Ordered cylinder vertices of an arbitrary affine facet map. -/
def mapVertexSignature
    (tau : Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1) :
    Fin p -> CylinderPoint p :=
  fun i => CylinderPoint.ofProd
    (tau (SphereOddDegree.FiniteSimplex.vertex (S := Real) (facetCoordinateIndex i)))

/-- Prime translation of an affine facet map. -/
def translateFacetMap
    (p : Nat) (g : PrimeSymmetry p)
    (tau : Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1) :
    Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1 :=
  fun x => (g • (tau x).1, (tau x).2)

@[simp] theorem mapVertexSignature_translateFacetMap
    (p : Nat) (g : PrimeSymmetry p)
    (tau : Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1) :
    mapVertexSignature (translateFacetMap p g tau) =
      fun i => g • mapVertexSignature tau i := by
  funext i
  rfl

/-- Ordered cylinder vertices of one actual facet occurrence. -/
noncomputable def occurrencePointSignature
    (hp : Nat.Prime p) (N L : Nat) (o : FacetOccurrence hp N L) :
    Fin p -> CylinderPoint p :=
  fun i => slotPoint hp N L (o.1, o.2.succAbove i)

@[simp] theorem mapVertexSignature_occurrenceFacetMap
    (hp : Nat.Prime p) (N L : Nat) (o : FacetOccurrence hp N L) :
    mapVertexSignature (occurrenceFacetMap hp N L o) =
      occurrencePointSignature hp N L o := by
  funext i
  simp [mapVertexSignature, occurrencePointSignature, slotPoint,
    occurrenceFacetMap_vertex]

/-- An affine facet map is realized when its ordered vertices are a simultaneous prime translate
of the ordered vertices of an actual triangulation facet.  Using the orbit closure, rather than
literal function equality, is what makes the auxiliary weight equivariant on all maps appearing in
the subdivision and staircase identities. -/
def FacetMapIsRealizedUpToPrime
    (hp : Nat.Prime p) (N L : Nat)
    (tau : Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1) : Prop :=
  ∃ o : FacetOccurrence hp N L, ∃ g : PrimeSymmetry p,
    mapVertexSignature tau = fun i => g • occurrencePointSignature hp N L o i

/-- Prime-equivalent ordered geometric occurrence signatures have equal unsigned indices for every
compatible assignment. -/
theorem occurrenceUnsignedFacetIndex_eq_of_pointSignature_eq_primeSmul
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L)
    (o o' : FacetOccurrence hp N L) (g : PrimeSymmetry p)
    (h : occurrencePointSignature hp N L o =
      fun i => g • occurrencePointSignature hp N L o' i) :
    unsignedFacetIndex hp (localVertexMap hp N L a o.1) o.2 =
      unsignedFacetIndex hp (localVertexMap hp N L a o'.1) o'.2 := by
  apply unsignedFacetIndex_eq_of_facetValue_eq_primeSmul hp g
    (localVertexMap hp N L a o'.1) (localVertexMap hp N L a o.1) o'.2 o.2
  intro i
  change vectorValue hp N L a (sampleVertex hp N L (o.1, o.2.succAbove i)) =
    g • vectorValue hp N L a (sampleVertex hp N L (o'.1, o'.2.succAbove i))
  have hs : sampleVertex hp N L (o.1, o.2.succAbove i) =
      g • sampleVertex hp N L (o'.1, o'.2.succAbove i) := by
    apply Quotient.sound
    change coverPoint hp N L
        ((1 : PrimeSymmetry p), (o.1, o.2.succAbove i)) =
      coverPoint hp N L (g, (o'.1, o'.2.succAbove i))
    simpa [coverPoint, occurrencePointSignature] using congrFun h i
  rw [hs, vectorValue_smul]

/-- Unsigned index attached to a realized affine facet map.  The chosen occurrence is immaterial by
`occurrenceUnsignedFacetIndex_eq_of_pointSignature_eq_primeSmul`. -/
noncomputable def realizedFacetWeight
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (tau : Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1) : ZMod p := by
  classical
  exact if h : FacetMapIsRealizedUpToPrime hp N L tau then
    unsignedFacetIndex hp
      (localVertexMap hp N L a (Classical.choose h).1)
      (Classical.choose h).2
  else 0

/-- The realized-map weight agrees with the signature weight of every occurrence. -/
theorem realizedFacetWeight_occurrence
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (o : FacetOccurrence hp N L) :
    realizedFacetWeight hp N L a (occurrenceFacetMap hp N L o) =
      signatureWeight hp N L a (facetSignature hp N L o) := by
  classical
  unfold realizedFacetWeight
  have hex : FacetMapIsRealizedUpToPrime hp N L
      (occurrenceFacetMap hp N L o) := by
    refine ⟨o, 1, ?_⟩
    simp
  rw [dif_pos hex, signatureWeight_facetSignature]
  let o' : FacetOccurrence hp N L := Classical.choose hex
  let g : PrimeSymmetry p := Classical.choose (Classical.choose_spec hex)
  have hg : mapVertexSignature (occurrenceFacetMap hp N L o) =
      fun i => g • occurrencePointSignature hp N L o' i :=
    Classical.choose_spec (Classical.choose_spec hex)
  have hocc : occurrencePointSignature hp N L o =
      fun i => g • occurrencePointSignature hp N L o' i := by
    rw [← mapVertexSignature_occurrenceFacetMap hp N L o]
    exact hg
  exact (occurrenceUnsignedFacetIndex_eq_of_pointSignature_eq_primeSmul
    hp N L a o o' g hocc).symm

/-- The realized facet weight is invariant under simultaneous prime translation. -/
theorem realizedFacetWeight_translateFacetMap
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L)
    (g : PrimeSymmetry p)
    (tau : Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1) :
    realizedFacetWeight hp N L a (translateFacetMap p g tau) =
      realizedFacetWeight hp N L a tau := by
  classical
  have hiff :
      FacetMapIsRealizedUpToPrime hp N L (translateFacetMap p g tau) ↔
        FacetMapIsRealizedUpToPrime hp N L tau := by
    constructor
    · rintro ⟨o, h, hh⟩
      refine ⟨o, g⁻¹ * h, ?_⟩
      funext i
      have hi := congrFun hh i
      simp only [mapVertexSignature_translateFacetMap] at hi
      have hi' := congrArg (fun z : CylinderPoint p => g⁻¹ • z) hi
      simpa [mul_smul] using hi'
    · rintro ⟨o, h, hh⟩
      refine ⟨o, g * h, ?_⟩
      funext i
      simp [mapVertexSignature_translateFacetMap, hh, mul_smul]
  unfold realizedFacetWeight
  by_cases hright : FacetMapIsRealizedUpToPrime hp N L tau
  · have hleft : FacetMapIsRealizedUpToPrime hp N L
        (translateFacetMap p g tau) := hiff.mpr hright
    rw [dif_pos hleft, dif_pos hright]
    let oL : FacetOccurrence hp N L := Classical.choose hleft
    let hL : PrimeSymmetry p := Classical.choose (Classical.choose_spec hleft)
    have heqL : mapVertexSignature (translateFacetMap p g tau) =
        fun i => hL • occurrencePointSignature hp N L oL i :=
      Classical.choose_spec (Classical.choose_spec hleft)
    let oR : FacetOccurrence hp N L := Classical.choose hright
    let hR : PrimeSymmetry p := Classical.choose (Classical.choose_spec hright)
    have heqR : mapVertexSignature tau =
        fun i => hR • occurrencePointSignature hp N L oR i :=
      Classical.choose_spec (Classical.choose_spec hright)
    have horbit : occurrencePointSignature hp N L oL =
        fun i => (hL⁻¹ * g * hR) • occurrencePointSignature hp N L oR i := by
      funext i
      have hi := congrArg (fun z : CylinderPoint p => hL⁻¹ • z)
        (congrFun heqL i).symm
      simp only [mapVertexSignature_translateFacetMap] at hi
      have hri := congrFun heqR i
      simpa [hri, mul_smul] using hi
    exact occurrenceUnsignedFacetIndex_eq_of_pointSignature_eq_primeSmul
      hp N L a oL oR (hL⁻¹ * g * hR) horbit
  · have hleft : ¬ FacetMapIsRealizedUpToPrime hp N L
        (translateFacetMap p g tau) := fun h => hright (hiff.mp h)
    rw [dif_neg hleft, dif_neg hright]

/-- A facet map is lower horizontal when every one of its vertices has time zero. -/
def MapIsLowerHorizontal
    (tau : Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1) : Prop :=
  ∀ i : Fin p,
    (tau (SphereOddDegree.FiniteSimplex.vertex (S := Real) (facetCoordinateIndex i))).2.1 = 0

/-- A facet map is upper horizontal when every one of its vertices has time one. -/
def MapIsUpperHorizontal
    (tau : Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1) : Prop :=
  ∀ i : Fin p,
    (tau (SphereOddDegree.FiniteSimplex.vertex (S := Real) (facetCoordinateIndex i))).2.1 = 1

/-- Weight used for the nonhorizontal part of the boundary. -/
noncomputable def nonhorizontalMapWeight
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L)
    (tau : Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1) : ZMod p := by
  classical
  exact if ¬ MapIsLowerHorizontal tau ∧ ¬ MapIsUpperHorizontal tau then
    realizedFacetWeight hp N L a tau
  else 0

/-- The auxiliary nonhorizontal weight vanishes on every lower endpoint facet. -/
theorem nonhorizontalMapWeight_lowerEndpointMap
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L)
    (sigma : Delta (p - 1) -> Realization p) :
    nonhorizontalMapWeight hp N L a (lowerEndpointMap sigma) = 0 := by
  unfold nonhorizontalMapWeight
  rw [ite_eq_right]
  intro h
  apply h.1
  intro i
  rfl

/-- The auxiliary nonhorizontal weight vanishes on every upper endpoint facet. -/
theorem nonhorizontalMapWeight_upperEndpointMap
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L)
    (sigma : Delta (p - 1) -> Realization p) :
    nonhorizontalMapWeight hp N L a (upperEndpointMap sigma) = 0 := by
  unfold nonhorizontalMapWeight
  rw [ite_eq_right]
  intro h
  apply h.2
  intro i
  rfl

/-- Occurrence expansion of the nonhorizontal signature contribution. -/
theorem nonhorizontalContribution_eq_occurrence_sum
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L) :
    nonhorizontalContribution hp N L a =
      ∑ o : FacetOccurrence hp N L,
        occurrenceCoefficient hp N L o *
          nonhorizontalMapWeight hp N L a (occurrenceFacetMap hp N L o) := by
  classical
  unfold nonhorizontalContribution signatureBoundaryCoefficient
  calc
    (∑ s : FacetSignature hp N L,
        if ¬ IsLowerHorizontal hp N L s ∧ ¬ IsUpperHorizontal hp N L s then
          (∑ o : FacetOccurrence hp N L,
            if facetSignature hp N L o = s then occurrenceCoefficient hp N L o else 0) *
              signatureWeight hp N L a s
        else 0) =
      ∑ s : FacetSignature hp N L,
        ∑ o : FacetOccurrence hp N L,
          if ¬ IsLowerHorizontal hp N L s ∧ ¬ IsUpperHorizontal hp N L s then
            if facetSignature hp N L o = s then
              occurrenceCoefficient hp N L o * signatureWeight hp N L a s
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hnon : ¬ IsLowerHorizontal hp N L s ∧ ¬ IsUpperHorizontal hp N L s
      · simp [hnon, Finset.sum_mul]
      · simp [hnon]
    _ = ∑ o : FacetOccurrence hp N L,
        ∑ s : FacetSignature hp N L,
          if ¬ IsLowerHorizontal hp N L s ∧ ¬ IsUpperHorizontal hp N L s then
            if facetSignature hp N L o = s then
              occurrenceCoefficient hp N L o * signatureWeight hp N L a s
            else 0
          else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ o : FacetOccurrence hp N L,
        occurrenceCoefficient hp N L o *
          nonhorizontalMapWeight hp N L a (occurrenceFacetMap hp N L o) := by
      apply Finset.sum_congr rfl
      intro o ho
      have hl : MapIsLowerHorizontal (occurrenceFacetMap hp N L o) ↔
          IsLowerHorizontal hp N L (facetSignature hp N L o) := by
        constructor <;> intro h i
        · have hi := h i
          rw [occurrenceFacetMap_vertex] at hi
          change (SubdivisionPrismCharts.vertex hp N L o.1 (o.2.succAbove i)).2.1 = 0
          exact hi
        · have hi := h i
          change (SubdivisionPrismCharts.vertex hp N L o.1 (o.2.succAbove i)).2.1 = 0 at hi
          rw [occurrenceFacetMap_vertex]
          exact hi
      have hu : MapIsUpperHorizontal (occurrenceFacetMap hp N L o) ↔
          IsUpperHorizontal hp N L (facetSignature hp N L o) := by
        constructor <;> intro h i
        · have hi := h i
          rw [occurrenceFacetMap_vertex] at hi
          change (SubdivisionPrismCharts.vertex hp N L o.1 (o.2.succAbove i)).2.1 = 1
          exact hi
        · have hi := h i
          change (SubdivisionPrismCharts.vertex hp N L o.1 (o.2.succAbove i)).2.1 = 1 at hi
          rw [occurrenceFacetMap_vertex]
          exact hi
      unfold nonhorizontalMapWeight
      rw [realizedFacetWeight_occurrence]
      by_cases hnon : ¬ IsLowerHorizontal hp N L (facetSignature hp N L o) ∧
          ¬ IsUpperHorizontal hp N L (facetSignature hp N L o)
      · have hmap : ¬ MapIsLowerHorizontal (occurrenceFacetMap hp N L o) ∧
            ¬ MapIsUpperHorizontal (occurrenceFacetMap hp N L o) := by
          exact ⟨fun h => hnon.1 (hl.mp h), fun h => hnon.2 (hu.mp h)⟩
        rw [Finset.sum_eq_single (facetSignature hp N L o)]
        · simp [hmap, hnon]
        · intro s hs hne
          simp [hne.symm]
        · simp
      · have hmap : ¬ (¬ MapIsLowerHorizontal (occurrenceFacetMap hp N L o) ∧
            ¬ MapIsUpperHorizontal (occurrenceFacetMap hp N L o)) := by
          intro hm
          exact hnon ⟨fun h => hm.1 (hl.mpr h), fun h => hm.2 (hu.mpr h)⟩
        rw [ite_eq_right hmap, mul_zero]
        apply Finset.sum_eq_zero
        intro s hs
        by_cases heq : facetSignature hp N L o = s
        · subst s
          simp [ hnon]
        · simp [heq]

/-- Prime relabelling does not change the nonhorizontal facet weight. -/
theorem nonhorizontalMapWeight_smul
    (hp : Nat.Prime p) (N L : Nat) (a : Assignment hp N L)
    (g : PrimeSymmetry p)
    (tau : Delta (p - 1) -> Realization p × Set.Icc (0 : Real) 1) :
    nonhorizontalMapWeight hp N L a
        (translateFacetMap p g tau) =
      nonhorizontalMapWeight hp N L a tau := by
  classical
  unfold nonhorizontalMapWeight
  have hl : MapIsLowerHorizontal (translateFacetMap p g tau) ↔
      MapIsLowerHorizontal tau := by rfl
  have hu : MapIsUpperHorizontal (translateFacetMap p g tau) ↔
      MapIsUpperHorizontal tau := by rfl
  by_cases h : ¬ MapIsLowerHorizontal tau ∧ ¬ MapIsUpperHorizontal tau
  · have hg : ¬ MapIsLowerHorizontal (translateFacetMap p g tau) ∧
        ¬ MapIsUpperHorizontal (translateFacetMap p g tau) := by
      exact ⟨fun hlow => h.1 (hl.mp hlow), fun hupp => h.2 (hu.mp hupp)⟩
    rw [ite_eq_left hg, ite_eq_left h]
    exact realizedFacetWeight_translateFacetMap hp N L a g tau
  · have hg : ¬ (¬ MapIsLowerHorizontal (translateFacetMap p g tau) ∧
        ¬ MapIsUpperHorizontal (translateFacetMap p g tau)) := by
      intro htrans
      exact h ⟨fun hlow => htrans.1 (hl.mpr hlow),
        fun hupp => htrans.2 (hu.mpr hupp)⟩
    rw [ite_eq_right hg, ite_eq_right h]

/-- Transport from the ambient prime-cardinality index to the face index of a
`(p - 2)`-simplex. -/
def orbitFacetEquiv (hp : Nat.Prime p) : Fin p ≃ Fin (p - 2 + 2) :=
  finCongr (by have := hp.two_le; omega)

/-- The face index corresponding to a labelled facet of a prime orbit. -/
noncomputable def orbitFacetIndex (hp : Nat.Prime p) (k : Fin p) : Fin (p - 2 + 2) :=
  orbitFacetEquiv hp k

/-- Reindex simplicial incidence by the ambient prime-cardinality face indices. -/
theorem simplicialIncidence_eq_orbitFace_sum
    (hp : Nat.Prime p) (target : Simplex p (p - 2))
    (source : Simplex p ((p - 2) + 1)) :
    SimplicialIncidence.incidence (R := ZMod p) target source =
      ∑ k : Fin p,
        if source.restrict (FaceMap.delete (orbitFacetIndex hp k)) = target then
          SimplicialChain.faceSign (R := ZMod p) (d := p - 2) (orbitFacetIndex hp k)
        else 0 := by
  unfold SimplicialIncidence.incidence
  symm
  apply Fintype.sum_equiv (orbitFacetEquiv hp)
  intro k
  rfl

/-- The facet of the chosen top representative obtained by deleting `k`. -/
noncomputable def orbitTopFace
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) (k : Fin p) :
    Simplex p (p - 2) :=
  (PrimeOrbitCycle.topRepresentative hp c).restrict
    (FaceMap.delete (orbitFacetIndex hp k))

/-- Orbit class of a face of the chosen top representative. -/
noncomputable def orbitFaceClass
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) (k : Fin p) :
    PrimeOrbitCycle.FacetOrbit hp :=
  Quotient.mk'' (orbitTopFace hp c k)

/-- A face and the canonical representative of its orbit differ by a prime relabelling. -/
theorem exists_orbitFaceTransport
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) (k : Fin p) :
    ∃ g : PrimeSymmetry p,
      g • PrimeOrbitCycle.facetRepresentative hp (orbitFaceClass hp c k) =
        orbitTopFace hp c k := by
  have hclass :
      (Quotient.mk'' (orbitTopFace hp c k) : PrimeOrbitCycle.FacetOrbit hp) =
        Quotient.mk'' (PrimeOrbitCycle.facetRepresentative hp (orbitFaceClass hp c k)) := by
    unfold orbitFaceClass PrimeOrbitCycle.facetRepresentative
      FiniteIncidenceCycle.facetRepresentative
    exact (Quotient.out_eq' _).symm
  exact Quotient.exact hclass

/-- A chosen prime relabelling that sends the canonical representative of a face orbit to the
actual face of the chosen top representative. -/
noncomputable def orbitFaceTransport
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) (k : Fin p) :
    PrimeSymmetry p :=
  Classical.choose (exists_orbitFaceTransport hp c k)

/-- Specification of the chosen face transporter. -/
theorem orbitFaceTransport_spec
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) (k : Fin p) :
    orbitFaceTransport hp c k •
        PrimeOrbitCycle.facetRepresentative hp (orbitFaceClass hp c k) =
      orbitTopFace hp c k :=
  Classical.choose_spec (exists_orbitFaceTransport hp c k)

/-- The unique member of the chosen top orbit whose `k`-th face is the canonical representative of
that face orbit. -/
noncomputable def orbitTopCellOfFace
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) (k : Fin p) : c.orbit :=
  ⟨(orbitFaceTransport hp c k)⁻¹ • PrimeOrbitCycle.topRepresentative hp c, by
    rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out c Quotient.out_eq']
    exact MulAction.mem_orbit_iff.mpr ⟨(orbitFaceTransport hp c k)⁻¹, rfl⟩⟩

/-- The selected top-orbit member has the canonical facet representative as its `k`-th face. -/
theorem orbitTopCellOfFace_restrict
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) (k : Fin p) :
    ((orbitTopCellOfFace hp c k : c.orbit) :
        (PrimeOrbitCycle.coveringCycle hp).TopCell).restrict
          (FaceMap.delete (orbitFacetIndex hp k)) =
      PrimeOrbitCycle.facetRepresentative hp (orbitFaceClass hp c k) := by
  change (((orbitFaceTransport hp c k)⁻¹ •
      PrimeOrbitCycle.topRepresentative hp c).restrict
        (FaceMap.delete (orbitFacetIndex hp k))) = _
  calc
    (((orbitFaceTransport hp c k)⁻¹ •
        PrimeOrbitCycle.topRepresentative hp c).restrict
          (FaceMap.delete (orbitFacetIndex hp k))) =
      (orbitFaceTransport hp c k)⁻¹ • orbitTopFace hp c k := by
        apply Simplex.ext
        intro i
        rfl
    _ = PrimeOrbitCycle.facetRepresentative hp (orbitFaceClass hp c k) := by
      rw [← orbitFaceTransport_spec hp c k]
      simp

/-- Incidence witnesses between one top orbit and the canonical facet representatives. -/
abbrev OrbitFaceWitness
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) :=
  {z : (PrimeOrbitCycle.FacetOrbit hp × c.orbit) × Fin p //
    ((z.1.2 : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell).restrict
        (FaceMap.delete (orbitFacetIndex hp z.2)) =
      PrimeOrbitCycle.facetRepresentative hp z.1.1}

/-- Enumerate the members of a finite top-cell orbit. -/
noncomputable local instance topOrbitMemberFintype
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) : Fintype c.orbit := by
  classical
  exact Subtype.fintype _

/-- Enumerate the face witnesses of a fixed top-cell orbit. -/
noncomputable local instance orbitFaceWitnessFintype
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) :
    Fintype (OrbitFaceWitness hp c) := Fintype.ofFinite _

/-- Every face of the chosen top representative determines exactly one nonzero orbit-incidence
witness. -/
noncomputable def orbitFaceWitnessEquiv
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp) :
    Fin p ≃ OrbitFaceWitness hp c where
  toFun k := ⟨((orbitFaceClass hp c k, orbitTopCellOfFace hp c k), k),
    orbitTopCellOfFace_restrict hp c k⟩
  invFun z := z.1.2
  left_inv := by intro k; rfl
  right_inv := by
    rintro ⟨⟨⟨qf, s⟩, k⟩, hface⟩
    have hsorbit : ((s : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell) ∈
        MulAction.orbit (PrimeSymmetry p) (PrimeOrbitCycle.topRepresentative hp c) := by
      change ((s : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell) ∈
        MulAction.orbit (PrimeSymmetry p) (Quotient.out c)
      rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out c Quotient.out_eq']
      exact s.property
    rcases MulAction.mem_orbit_iff.mp hsorbit with ⟨g, hg⟩
    have hfaceg :
        g • orbitTopFace hp c k = PrimeOrbitCycle.facetRepresentative hp qf := by
      calc
        g • orbitTopFace hp c k =
            (g • PrimeOrbitCycle.topRepresentative hp c).restrict
              (FaceMap.delete (orbitFacetIndex hp k)) := by
                apply Simplex.ext
                intro i
                rfl
        _ = ((s : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell).restrict
              (FaceMap.delete (orbitFacetIndex hp k)) := by rw [hg]
        _ = PrimeOrbitCycle.facetRepresentative hp qf := hface
    have hq : orbitFaceClass hp c k = qf := by
      unfold orbitFaceClass
      rw [← Quotient.out_eq' qf]
      apply Quotient.sound
      refine ⟨g⁻¹, ?_⟩
      change g⁻¹ • PrimeOrbitCycle.facetRepresentative hp qf = orbitTopFace hp c k
      calc
        g⁻¹ • PrimeOrbitCycle.facetRepresentative hp qf =
            g⁻¹ • (g • orbitTopFace hp c k) := congrArg (fun x => g⁻¹ • x) hfaceg.symm
        _ = orbitTopFace hp c k := by simp
    let a : PrimeSymmetry p := orbitFaceTransport hp c k
    have haspec : a • PrimeOrbitCycle.facetRepresentative hp qf =
        orbitTopFace hp c k := by
      simpa [a, hq] using orbitFaceTransport_spec hp c k
    have hstab : (g * a) • PrimeOrbitCycle.facetRepresentative hp qf =
        PrimeOrbitCycle.facetRepresentative hp qf := by
      rw [mul_smul, haspec, hfaceg]
    have hga : g * a = 1 :=
      Simplex.primeSymmetry_action_free p hstab
    have ha : a = g⁻¹ := by
      calc
        a = 1 * a := by simp
        _ = (g⁻¹ * g) * a := by simp
        _ = g⁻¹ * (g * a) := by rw [mul_assoc]
        _ = g⁻¹ := by rw [hga]; simp
    have hs : orbitTopCellOfFace hp c k = s := by
      apply Subtype.ext
      change a⁻¹ • PrimeOrbitCycle.topRepresentative hp c =
        ((s : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell)
      rw [ha]
      simpa using hg
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact hq
      · exact hs
    · rfl

open scoped Classical in
/-- Expand orbit incidence as a sum over its nonzero face witnesses. -/
theorem orbitFaceWitness_sum
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp)
    (W : Simplex p (p - 2) -> ZMod p) :
    (∑ qf : PrimeOrbitCycle.FacetOrbit hp,
      ∑ s : c.orbit, ∑ k : Fin p,
        if (((s : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell).restrict
              (FaceMap.delete (orbitFacetIndex hp k)) =
            PrimeOrbitCycle.facetRepresentative hp qf) then
          SimplicialChain.faceSign (R := ZMod p) (d := p - 2)
              (orbitFacetIndex hp k) * W (PrimeOrbitCycle.facetRepresentative hp qf)
        else 0) =
      ∑ z : OrbitFaceWitness hp c,
        SimplicialChain.faceSign (R := ZMod p) (d := p - 2)
            (orbitFacetIndex hp z.1.2) *
          W (PrimeOrbitCycle.facetRepresentative hp z.1.1.1) := by
  classical
  rw [← Fintype.sum_prod_type (fun z :
    PrimeOrbitCycle.FacetOrbit hp × c.orbit =>
      ∑ k : Fin p,
        if (((z.2 : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell).restrict
              (FaceMap.delete (orbitFacetIndex hp k)) =
            PrimeOrbitCycle.facetRepresentative hp z.1) then
          SimplicialChain.faceSign (R := ZMod p) (d := p - 2)
            (orbitFacetIndex hp k) * W (PrimeOrbitCycle.facetRepresentative hp z.1)
        else 0)]
  rw [← Fintype.sum_prod_type (fun z :
    (PrimeOrbitCycle.FacetOrbit hp × c.orbit) × Fin p =>
      if (((z.1.2 : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell).restrict
            (FaceMap.delete (orbitFacetIndex hp z.2)) =
          PrimeOrbitCycle.facetRepresentative hp z.1.1) then
        SimplicialChain.faceSign (R := ZMod p) (d := p - 2)
          (orbitFacetIndex hp z.2) * W (PrimeOrbitCycle.facetRepresentative hp z.1.1)
      else 0)]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype
    (p := fun z : (PrimeOrbitCycle.FacetOrbit hp × c.orbit) × Fin p =>
      (((z.1.2 : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell).restrict
          (FaceMap.delete (orbitFacetIndex hp z.2)) =
        PrimeOrbitCycle.facetRepresentative hp z.1.1))
    (Finset.univ.filter fun z : (PrimeOrbitCycle.FacetOrbit hp × c.orbit) × Fin p =>
      (((z.1.2 : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell).restrict
          (FaceMap.delete (orbitFacetIndex hp z.2)) =
        PrimeOrbitCycle.facetRepresentative hp z.1.1))
    (fun z => by simp)
    (fun z => SimplicialChain.faceSign (R := ZMod p) (d := p - 2)
        (orbitFacetIndex hp z.2) * W (PrimeOrbitCycle.facetRepresentative hp z.1.1))

/-- The orbit coboundary at a chosen top representative is its ordinary weighted face sum. -/
theorem orbit_coboundary_eq_face_sum
    (hp : Nat.Prime p) (c : PrimeOrbitCycle.TopOrbit hp)
    (W : Simplex p (p - 2) -> ZMod p)
    (hW : ∀ (g : PrimeSymmetry p) (f : Simplex p (p - 2)),
      W (g • f) = W f) :
    (∑ qf : PrimeOrbitCycle.FacetOrbit hp,
      (PrimeOrbitCycle.orbitCycle hp).incidence qf c *
        W (PrimeOrbitCycle.facetRepresentative hp qf)) =
      ∑ k : Fin p,
        SimplicialChain.faceSign (R := ZMod p) (d := p - 2)
            (orbitFacetIndex hp k) * W (orbitTopFace hp c k) := by
  classical
  change (∑ qf : PrimeOrbitCycle.FacetOrbit hp,
      (FiniteIncidenceCycle.orbitIncidence
        (G := PrimeSymmetry p) (PrimeOrbitCycle.coveringCycle hp) qf c) *
        W (PrimeOrbitCycle.facetRepresentative hp qf)) = _
  unfold FiniteIncidenceCycle.orbitIncidence
  change (∑ qf : PrimeOrbitCycle.FacetOrbit hp,
      (∑ s : c.orbit,
        SimplicialIncidence.incidence (R := ZMod p)
          (PrimeOrbitCycle.facetRepresentative hp qf)
          ((s : c.orbit) : (PrimeOrbitCycle.coveringCycle hp).TopCell)) *
        W (PrimeOrbitCycle.facetRepresentative hp qf)) = _
  simp_rw [simplicialIncidence_eq_orbitFace_sum hp, Finset.sum_mul]
  simp only [ite_mul, zero_mul]
  rw [orbitFaceWitness_sum hp c W]
  symm
  apply Fintype.sum_equiv (orbitFaceWitnessEquiv hp c)
  intro k
  change
    SimplicialChain.faceSign (R := ZMod p) (d := p - 2)
        (orbitFacetIndex hp k) * W (orbitTopFace hp c k) =
      SimplicialChain.faceSign (R := ZMod p) (d := p - 2)
        (orbitFacetIndex hp k) *
          W (PrimeOrbitCycle.facetRepresentative hp (orbitFaceClass hp c k))
  congr 1
  rw [← orbitFaceTransport_spec hp c k]
  exact hW (orbitFaceTransport hp c k)
    (PrimeOrbitCycle.facetRepresentative hp (orbitFaceClass hp c k))

/-- Weighted boundary pairing of the orbit cycle vanishes for every equivariant facet weight. -/
theorem orbit_boundary_pairing_eq_zero
    (hp : Nat.Prime p)
    (W : Simplex p (p - 2) -> ZMod p)
    (hW : ∀ (g : PrimeSymmetry p) (f : Simplex p (p - 2)),
      W (g • f) = W f) :
    (∑ c : PrimeOrbitCycle.TopOrbit hp,
      (PrimeOrbitCycle.orbitCycle hp).coefficient c *
        ∑ k : Fin p,
          SimplicialChain.faceSign (R := ZMod p) (d := p - 2) (orbitFacetIndex hp k) *
            W ((PrimeOrbitCycle.topRepresentative hp c).restrict
              (FaceMap.delete (orbitFacetIndex hp k)))) = 0 := by
  classical
  have hzero := (PrimeOrbitCycle.orbitCycle hp).zeroCount_coboundary_eq_zero
    (fun qf => W (PrimeOrbitCycle.facetRepresentative hp qf))
  unfold FiniteIncidenceCycle.zeroCount FiniteIncidenceCycle.coboundary at hzero
  calc
    (∑ c : PrimeOrbitCycle.TopOrbit hp,
      (PrimeOrbitCycle.orbitCycle hp).coefficient c *
        ∑ k : Fin p,
          SimplicialChain.faceSign (R := ZMod p) (d := p - 2) (orbitFacetIndex hp k) *
            W ((PrimeOrbitCycle.topRepresentative hp c).restrict
              (FaceMap.delete (orbitFacetIndex hp k)))) =
      ∑ c : PrimeOrbitCycle.TopOrbit hp,
        (PrimeOrbitCycle.orbitCycle hp).coefficient c *
          ∑ qf : PrimeOrbitCycle.FacetOrbit hp,
            (PrimeOrbitCycle.orbitCycle hp).incidence qf c *
              W (PrimeOrbitCycle.facetRepresentative hp qf) := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [orbit_coboundary_eq_face_sum hp c W hW]
        rfl
    _ = 0 := hzero

/-- In successor dimension, the concrete occurrence facet is the iterated facet map of the
corresponding unrefined staircase prism. -/
theorem occurrenceFacetMap_eq_iteratedFacetMap_succ
    (hp : Nat.Prime (n + 1)) (N L : Nat)
    (base : RefinedAffineMap.TopCell hp N) (k : Fin (n + 1))
    (rho : Fin L → Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2)) :
    occurrenceFacetMap hp N L (((base, k), rho), j) =
      iteratedFacetMap n L
        (staircasePrismMap n (RefinedAffineMap.chart hp N base) k)
        rho (facetFaceIndex hp j) := by
  funext x
  simp only [occurrenceFacetMap, occurrenceCofacePoint, iteratedFacetMap,
    SubdivisionPrismCharts.chart, staircasePrismMap,
    SubdivisionPrismCharts.staircasePoint]
  apply Prod.ext
  · apply congrArg (RefinedAffineMap.chart hp N base)
    apply Subtype.ext
    funext i
    simp only [StandardSimplex.toDelta, StandardSimplex.ofDelta,
      SubdivisionPrismCharts.spatialPoint, SubdivisionPrismCharts.spatialWeight,
      genericStaircaseSpatialPoint]
    apply Finset.sum_congr rfl
    intro q hq
    congr 1
  · apply Subtype.ext
    change (SubdivisionPrismCharts.intervalPoint k
      (StandardSimplex.ofDelta
        (affineCompMap (n + 1) L rho
          (deltaCast rfl
            (cofacePoint n (facetFaceIndex hp j) x))))).1 = _
    simp only [deltaCast_rfl, StandardSimplex.ofDelta,
      SubdivisionPrismCharts.intervalPoint,
      SubdivisionPrismCharts.intervalWeight, genericStaircaseIntervalPoint,
      SubdivisionPrismCharts.staircaseTime, genericStaircaseTime]
    rfl

/-- In positive successor dimension, the refined chart is the unrefined realization chart
precomposed with the same spatial refinement word. -/
theorem refined_chart_eq_affineCompMap
    (hp : Nat.Prime (n + 1)) (N : Nat)
    (orbit : PrimeOrbitCycle.TopOrbit hp)
    (spatial : RefinementWord (n + 1) N) :
    (RefinedAffineMap.chart hp N (orbit, spatial) : Delta n → Realization (n + 1)) =
      fun x => (ReferenceAffineOrbitCount.topRepr hp orbit).realizationPoint
        (StandardSimplex.ofDelta (affineCompMap n N spatial x)) := by
  funext x
  simp [RefinedAffineMap.chart, Simplex.refinedContinuousMap,
    Simplex.realizationContinuousMap, Simplex.refinementIndexPerm]

/-- Relabelling any simplex commutes with its realization chart. -/
theorem realizationPoint_prime_smul_any
    (p : Nat) (g : PrimeSymmetry p)
    (s : Simplex p d) (w : StandardSimplex d) :
    (g • s).realizationPoint w = g • s.realizationPoint w := by
  apply Realization.ext
  intro c
  classical
  simp +instances only [Simplex.realizationPoint_apply, Simplex.chartWeight,
    Realization.prime_smul_apply, Simplex.prime_smul_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : g • s i = c
  · have h' : s i = c.relabel (PrimeSymmetry.toPerm p g).symm := by
      have := congrArg (fun z : BarredPermutation p =>
        z.relabel (PrimeSymmetry.toPerm p g).symm) h
      simpa using this
    simp [ h']
  · have h' : s i ≠ c.relabel (PrimeSymmetry.toPerm p g).symm := by
      intro hs
      apply h
      have := congrArg (fun z : BarredPermutation p =>
        z.relabel (PrimeSymmetry.toPerm p g)) hs
      simpa using this
    change (if g • s i = c then w i else 0) =
      (if s i = c.relabel (PrimeSymmetry.toPerm p g).symm then w i else 0)
    rw [ite_eq_right h, ite_eq_right h']

/-- Weight of a staircase side simplex built over a spatial facet. -/
noncomputable def spatialSideWeight
    (hp : Nat.Prime (n + 1)) (N L : Nat) (a : Assignment hp N L)
    (eta : Fin L → Equiv.Perm (Fin (n + 1))) (h : Fin n)
    (tau : Delta (n - 1) → Realization (n + 1)) : ZMod (n + 1) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by
    intro hn0
    subst n
    exact Fin.elim0 h)
  let h' : Fin ((n - 1) + 1) := Fin.cast (by omega) h
  exact nonhorizontalMapWeight hp N L a (fun x =>
    staircasePrismMap (n - 1) tau h'
      (deltaCast (Nat.sub_add_cancel hn).symm (affineCompMap n L eta x)))

/-- A side simplex of a refined chart is the side weight of its iterated spatial facet. -/
theorem refined_side_eq_spatialSideWeight
    (hp : Nat.Prime (n + 1)) (N L : Nat) (a : Assignment hp N L)
    (orbit : PrimeOrbitCycle.TopOrbit hp)
    (spatial : RefinementWord (n + 1) N)
    (eta : Fin L → Equiv.Perm (Fin (n + 1)))
    (r : Fin (n + 1)) (h : Fin n) :
    let hn : 0 < n := Nat.pos_of_ne_zero (by
      intro hn0
      subst n
      exact Fin.elim0 h)
    let hd : n - 1 + 2 = n + 1 := by omega
    let spatial' : Fin N → Equiv.Perm (Fin (n - 1 + 2)) := fun k =>
      (Equiv.cast (congrArg Fin hd)).trans (spatial k) |>.trans
        (Equiv.cast (congrArg Fin hd.symm))
    let baseSimplex : Delta (n - 1 + 1) → Realization (n + 1) := fun x =>
      (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
        (deltaCast ((Nat.sub_add_cancel hn).trans (Nat.add_sub_cancel n 1).symm) x)
    nonhorizontalMapWeight hp N L a (fun x =>
      sidePrismMap n (RefinedAffineMap.chart hp N (orbit, spatial)) r h
        (affineCompMap n L eta x)) =
      spatialSideWeight hp N L a eta h
        (iteratedFacetMap (n - 1) N baseSimplex spatial'
          (Fin.cast hd.symm r)) := by
  cases n with
  | zero => exact Fin.elim0 h
  | succ n =>
      dsimp only
      rw [refined_chart_eq_affineCompMap]
      simp [spatialSideWeight, sidePrismMap, deltaCast, Equiv.cast]
      have hspatial :
          (fun k =>
            ((Equiv.cast (congrArg Fin (show n + 1 - 1 + 2 = n + 1 + 1 by omega))).trans
              (spatial k)).trans
              (Equiv.cast (congrArg Fin
                (show n + 1 + 1 = n + 1 - 1 + 2 by omega)))) = spatial := by
        funext k
        apply Equiv.ext
        intro i
        rfl
      change nonhorizontalMapWeight hp N L a _ = nonhorizontalMapWeight hp N L a _
      congr 1

/-- Successor-dimensional form of the refined side bridge, with transports normalized. -/
theorem refined_side_eq_spatialSideWeight_succ
    (hp : Nat.Prime (n + 1 + 1)) (N L : Nat) (a : Assignment hp N L)
    (orbit : PrimeOrbitCycle.TopOrbit hp)
    (spatial : RefinementWord (n + 1 + 1) N)
    (eta : Fin L → Equiv.Perm (Fin (n + 1 + 1)))
    (r : Fin (n + 1 + 1)) (h : Fin (n + 1)) :
    nonhorizontalMapWeight hp N L a (fun x =>
      sidePrismMap (n + 1) (RefinedAffineMap.chart hp N (orbit, spatial)) r h
        (affineCompMap (n + 1) L eta x)) =
      spatialSideWeight hp N L a eta h
        (iteratedFacetMap n N
          (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
          spatial r) := by
  rw [refined_side_eq_spatialSideWeight hp N L a orbit spatial eta r h]
  congr 2

/-- The spatial subdivision boundary identity specialized to a fixed side weight. -/
theorem spatialSide_weighted_boundary
    (hp : Nat.Prime (n + 1 + 1)) (N L : Nat) (a : Assignment hp N L)
    (eta : Fin L → Equiv.Perm (Fin (n + 1 + 1))) (h : Fin (n + 1))
    (orbit : PrimeOrbitCycle.TopOrbit hp) :
    (∑ spatial : RefinementWord (n + 1 + 1) N,
      iteratedSign (ZMod (n + 1 + 1)) N spatial *
        ∑ r : Fin (n + 1 + 1), SimplicialChain.faceSign r *
          spatialSideWeight hp N L a eta h
            (iteratedFacetMap n N
              (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
              spatial r)) =
      ∑ j : Fin (n + 1 + 1), SimplicialChain.faceSign j *
        ∑ theta : Fin N → Equiv.Perm (Fin (n + 1)),
          iteratedSign (ZMod (n + 1 + 1)) N theta *
            spatialSideWeight hp N L a eta h
              (iteratedBoundaryMap n N
                (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
                j theta) := by
  exact iterated_weighted_boundary
    (R := ZMod (n + 1 + 1)) (X := Realization (n + 1 + 1))
    (n := n) (N := N)
    (sigma := (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap)
    (W := spatialSideWeight hp N L a eta h)

/-- The scaled form of the spatial side boundary identity used in the final sum. -/
theorem spatialSide_scaled_boundary
    (hp : Nat.Prime (n + 1 + 1)) (N L : Nat) (a : Assignment hp N L)
    (eta : Fin L → Equiv.Perm (Fin (n + 1 + 1))) (h : Fin (n + 1))
    (orbit : PrimeOrbitCycle.TopOrbit hp) :
    (∑ spatial : RefinementWord (n + 1 + 1) N,
      ∑ r : Fin (n + 1 + 1),
        ((PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
          iteratedSign (ZMod (n + 1 + 1)) N spatial) *
        (iteratedSign (ZMod (n + 1 + 1)) L eta *
          (SimplicialChain.faceSign r *
            ((((-1 : ZMod (n + 1 + 1)) ^ h.1)) *
              spatialSideWeight hp N L a eta h
                (iteratedFacetMap n N
                  (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
                  spatial r))))) =
      ((PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
        iteratedSign (ZMod (n + 1 + 1)) L eta *
        ((-1 : ZMod (n + 1 + 1)) ^ h.1)) *
      (∑ j : Fin (n + 1 + 1), SimplicialChain.faceSign j *
        ∑ theta : Fin N → Equiv.Perm (Fin (n + 1)),
          iteratedSign (ZMod (n + 1 + 1)) N theta *
            spatialSideWeight hp N L a eta h
              (iteratedBoundaryMap n N
                (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
                j theta)) := by
  rw [← spatialSide_weighted_boundary hp N L a eta h orbit]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spatial hspatial
  apply Finset.sum_congr rfl
  intro r hr
  ring
/-- The prime-orbit boundary pairing vanishes for each fixed refinement word. -/
private theorem fixed_refined_side_cancels (N L n : ℕ) (hp : Nat.Prime (n + 1 + 1)) (a : Assignment hp N L)
  (eta : Fin L → Equiv.Perm (Fin (n + 1 + 1))) (h : Fin (n + 1)) (theta : Fin N → Equiv.Perm (Fin (n + 1))) :
  ∑ x,
      ∑ x_1,
        (PrimeOrbitCycle.orbitCycle hp).coefficient x * iteratedSign (ZMod (n + 1 + 1)) L eta * (-1) ^ h.1 *
          (SimplicialChain.faceSign x_1 *
            (iteratedSign (ZMod (n + 1 + 1)) N theta *
              spatialSideWeight hp N L a eta h
                (iteratedBoundaryMap n N (⇑(ReferenceAffineOrbitCount.topRepr hp x).realizationContinuousMap) x_1
                  theta))) =
    0 := by
  classical
  let W : Simplex (n + 1 + 1) n → ZMod (n + 1 + 1) := fun f =>
    spatialSideWeight hp N L a eta h (fun x =>
      f.realizationPoint
        (StandardSimplex.ofDelta (affineCompMap n N theta x)))
  have hW : ∀ (g : PrimeSymmetry (n + 1 + 1)) (f : Simplex (n + 1 + 1) n),
      W (g • f) = W f := by
    intro g f
    dsimp [W, spatialSideWeight]
    calc
      _ = nonhorizontalMapWeight hp N L a
          (translateFacetMap (n + 1 + 1) g (fun x =>
            staircasePrismMap n (fun y => f.realizationPoint
              (StandardSimplex.ofDelta (affineCompMap n N theta y))) h
              (deltaCast (Nat.sub_add_cancel (Nat.zero_lt_succ n)).symm
                (affineCompMap (n + 1) L eta x)))) := by
            congr 1
            funext x
            apply Prod.ext
            · simp only [translateFacetMap, staircasePrismMap]
              exact realizationPoint_prime_smul_any (n + 1 + 1) g f _
            · rfl
      _ = _ := nonhorizontalMapWeight_smul hp N L a g _
  have hz := orbit_boundary_pairing_eq_zero hp W hW
  have hmap (orbit : PrimeOrbitCycle.TopOrbit hp) (j : Fin (n + 1 + 1)) :
      spatialSideWeight hp N L a eta h
          (iteratedBoundaryMap n N
            (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
            j theta) =
        W ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
          (FaceMap.delete j)) := by
    congr 1
    funext x
    apply Realization.ext
    intro c
    simp [ iteratedBoundaryMap, ReferenceAffineOrbitCount.topRepr,
      Simplex.realizationContinuousMap, Simplex.realizationPoint,
      Simplex.chartWeight, cofacePoint, SphereOddDegree.FiniteSimplex.map_coe]
    change (∑ i : Fin (n + 1 + 1),
      if (ReferenceAffineOrbitCount.topRepr hp orbit) i = c then
        (StandardSimplex.ofDelta
          (SphereOddDegree.FiniteSimplex.map j.succAbove (affineCompMap n N theta x))) i else 0) = _
    have hs := Fin.sum_univ_succAbove (fun i : Fin (n + 1 + 1) =>
      if (ReferenceAffineOrbitCount.topRepr hp orbit) i = c then
        (StandardSimplex.ofDelta
          (SphereOddDegree.FiniteSimplex.map j.succAbove (affineCompMap n N theta x))) i else 0) j
    rw [hs]
    have hdeleted :
        (StandardSimplex.ofDelta
          (SphereOddDegree.FiniteSimplex.map j.succAbove (affineCompMap n N theta x))) j = 0 := by
      change (cofacePoint n j (affineCompMap n N theta x)) j = 0
      exact cofacePoint_apply_deleted n j (affineCompMap n N theta x)
    simp only [hdeleted, ite_self, zero_add]
    apply Finset.sum_congr rfl
    intro i hi
    change (if (ReferenceAffineOrbitCount.topRepr hp orbit) (j.succAbove i) = c then _ else 0) =
      if (ReferenceAffineOrbitCount.topRepr hp orbit) (j.succAbove i) = c then _ else 0
    by_cases hic : (ReferenceAffineOrbitCount.topRepr hp orbit) (j.succAbove i) = c
    · rw [ite_eq_left hic, ite_eq_left hic]
      change SphereOddDegree.FiniteSimplex.map (S := Real) j.succAbove
        (affineCompMap n N theta x) (j.succAbove i) =
          affineCompMap n N theta x i
      rw [SphereOddDegree.FiniteSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
      exact Finset.sum_eq_single i (by
        intro q hq hqi
        have hsucc : j.succAbove q ≠ j.succAbove i := by
          intro heq
          exact hqi (Fin.succAbove_right_injective heq)
        have hq' : j.succAbove q = j.succAbove i := by simpa using hq
        exact (hsucc hq').elim) (by simp)
    · rw [ite_eq_right hic, ite_eq_right hic]
  simp_rw [hmap]
  calc
    _ = (iteratedSign (ZMod (n + 1 + 1)) L eta *
          ((-1 : ZMod (n + 1 + 1)) ^ h.1) *
          iteratedSign (ZMod (n + 1 + 1)) N theta) *
        (∑ orbit,
          (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
            ∑ k,
              SimplicialChain.faceSign (orbitFacetIndex hp k) *
                W ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                  (FaceMap.delete (orbitFacetIndex hp k)))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro orbit horbit
          rw [Finset.mul_sum]
          have hreindex :
              (∑ j : Fin (n + 1 + 1),
                (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                  iteratedSign (ZMod (n + 1 + 1)) L eta *
                  ((-1 : ZMod (n + 1 + 1)) ^ h.1 *
                  (SimplicialChain.faceSign j *
                    (iteratedSign (ZMod (n + 1 + 1)) N theta *
                      W ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                        (FaceMap.delete j))))) =
                ∑ k : Fin (n + 1 + 1),
                  (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                    iteratedSign (ZMod (n + 1 + 1)) L eta *
                    ((-1 : ZMod (n + 1 + 1)) ^ h.1 *
                    (SimplicialChain.faceSign (orbitFacetIndex hp k) *
                      (iteratedSign (ZMod (n + 1 + 1)) N theta *
                        W ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                          (FaceMap.delete (orbitFacetIndex hp k))))))) := by
            exact (Equiv.sum_comp (orbitFacetEquiv hp) (fun j =>
              (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                iteratedSign (ZMod (n + 1 + 1)) L eta *
                ((-1 : ZMod (n + 1 + 1)) ^ h.1 *
                (SimplicialChain.faceSign j *
                  (iteratedSign (ZMod (n + 1 + 1)) N theta *
                    W ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                      (FaceMap.delete j))))))).symm
          calc
            _ = ∑ j : Fin (n + 1 + 1),
                (PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
                  iteratedSign (ZMod (n + 1 + 1)) L eta *
                  ((-1 : ZMod (n + 1 + 1)) ^ h.1 *
                  (SimplicialChain.faceSign j *
                    (iteratedSign (ZMod (n + 1 + 1)) N theta *
                      W ((PrimeOrbitCycle.topRepresentative hp orbit).restrict
                        (FaceMap.delete j))))) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
            _ = _ := hreindex
            _ = _ := by
              simp_rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k hk
              ring
    _ = 0 := by simpa only [hz, mul_zero]

/-- The complete nonhorizontal refined-prism contribution vanishes. -/
theorem nonhorizontalContribution_eq_zero_core
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) :
    nonhorizontalContribution hp N L a = 0 := by
  classical
  have hpdim : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.pos).symm
  generalize hn : p - 1 = n at hpdim ⊢
  subst p
  rw [nonhorizontalContribution_eq_occurrence_sum]
  -- First remove the final `L`-fold barycentric refinement of each staircase
  -- prism simplex.
  rw [Fintype.sum_prod_type]
  simp only [occurrenceCoefficient, prismCoefficient, prismSign,
    Int.cast_mul, Int.cast_prod]
  -- Apply the weighted subdivision identity cellwise, then the staircase
  -- boundary identity.  The horizontal terms are zero by definition of
  -- `nonhorizontalMapWeight`.
  conv_lhs =>
    enter [2, cell, 2, j]
    rw [occurrenceFacetMap_eq_iteratedFacetMap_succ]
  simp only [subdivisionSign, staircaseSign, iteratedSign]
  ring_nf
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]
  ring_nf
  conv_lhs =>
    enter [2, orbit, 2, spatial, 2, k, 2, j]
    rw [mul_assoc]
  conv_lhs =>
    enter [2, orbit, 2, spatial, 2, k]
    rw [← Finset.mul_sum, mul_assoc]
  conv_lhs =>
    enter [2, orbit, 2, spatial]
    rw [← Finset.mul_sum]
  have hfacetFaceIndex (j : Fin (n + 2)) : facetFaceIndex hp j = j := by
    apply Fin.ext
    rfl
  simp_rw [hfacetFaceIndex]
  conv_lhs =>
    enter [2, orbit, 2, spatial, 2]
    change ∑ rho, iteratedSign (ZMod (n + 1)) L rho *
      ∑ j, SimplicialChain.faceSign j *
        nonhorizontalMapWeight hp N L a
          (iteratedFacetMap n L
            (staircasePrismMap n (RefinedAffineMap.chart hp N orbit) spatial) rho j)
    rw [iterated_weighted_boundary
      (R := ZMod (n + 1))
      (X := Realization (n + 1) × Set.Icc (0 : Real) 1)
      (n := n) (N := L)]
  ring_nf
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]
  conv_lhs =>
    enter [2, orbit, 2, spatial]
    rw [mul_assoc]
  conv_lhs =>
    enter [2, orbit]
    rw [← Finset.mul_sum]
  conv_lhs =>
    enter [2, orbit, 2]
    rw [show
      (∑ spatial : Fin (n + 1), ((-1 : ZMod (n + 1)) ^ spatial.1) *
        ∑ j : Fin (n + 2), SimplicialChain.faceSign j *
          ∑ eta : Fin L → Equiv.Perm (Fin (n + 1)),
            iteratedSign (ZMod (n + 1)) L eta *
              nonhorizontalMapWeight hp N L a
                (iteratedBoundaryMap n L
                  (staircasePrismMap n (RefinedAffineMap.chart hp N orbit) spatial) j eta)) =
      ∑ eta : Fin L → Equiv.Perm (Fin (n + 1)),
        iteratedSign (ZMod (n + 1)) L eta *
          ∑ spatial : Fin (n + 1), ((-1 : ZMod (n + 1)) ^ spatial.1) *
            ∑ j : Fin (n + 2), SimplicialChain.faceSign j *
              nonhorizontalMapWeight hp N L a
                (fun x => staircasePrismMap n
                  (RefinedAffineMap.chart hp N orbit) spatial
                  (cofacePoint n j (affineCompMap n L eta x))) by
        simp_rw [Finset.mul_sum]
        conv_lhs =>
          enter [2, spatial]
          rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro eta heta
        apply Finset.sum_congr rfl
        intro spatial hspatial
        apply Finset.sum_congr rfl
        intro j hj
        have hmap :
            iteratedBoundaryMap n L
                (staircasePrismMap n (RefinedAffineMap.chart hp N orbit) spatial) j eta =
              fun x => staircasePrismMap n (RefinedAffineMap.chart hp N orbit) spatial
                (cofacePoint n j (affineCompMap n L eta x)) := rfl
        rw [hmap]
        ac_rfl]
  conv_lhs =>
    enter [2, orbit, 2]
    enter [2, eta, 2]
    rw [staircase_weighted_boundary
      (W := fun tau => nonhorizontalMapWeight hp N L a
        (fun x => tau (affineCompMap n L eta x)))]
  have hlower (eta : Fin L → Equiv.Perm (Fin (n + 1)))
      (sigma : Delta n → Realization (n + 1)) :
      nonhorizontalMapWeight hp N L a
          (fun x => lowerEndpointMap sigma (affineCompMap n L eta x)) = 0 := by
    change nonhorizontalMapWeight hp N L a
      (lowerEndpointMap (fun x => sigma (affineCompMap n L eta x))) = 0
    apply nonhorizontalMapWeight_lowerEndpointMap
  have hupper (eta : Fin L → Equiv.Perm (Fin (n + 1)))
      (sigma : Delta n → Realization (n + 1)) :
      nonhorizontalMapWeight hp N L a
          (fun x => upperEndpointMap sigma (affineCompMap n L eta x)) = 0 := by
    change nonhorizontalMapWeight hp N L a
      (upperEndpointMap (fun x => sigma (affineCompMap n L eta x))) = 0
    apply nonhorizontalMapWeight_upperEndpointMap
  simp_rw [hlower, hupper]
  simp only [zero_sub, sub_zero]
  -- The remaining side term is the iterated spatial boundary pairing.  Move
  -- the `N`-fold spatial subdivision to the original top-cell boundary.
  rw [Fintype.sum_prod_type]
  cases n with
  | zero => simp
  | succ n =>
    simp_rw [refined_side_eq_spatialSideWeight_succ]
    simp_rw [Finset.mul_sum]
    conv_lhs =>
      enter [2, orbit]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs =>
      enter [2, eta, 2, orbit, 2, spatial]
      rw [Finset.sum_comm]
    simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
    rw [neg_eq_zero]
    apply Finset.sum_eq_zero
    intro eta heta
    conv_lhs =>
      enter [2, orbit]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro h hh
    change ∑ orbit, ∑ spatial, ∑ r,
      ((PrimeOrbitCycle.orbitCycle hp).coefficient orbit *
        iteratedSign (ZMod (n + 1 + 1)) N spatial) *
      (iteratedSign (ZMod (n + 1 + 1)) L eta *
        (SimplicialChain.faceSign r *
          (((-1 : ZMod (n + 1 + 1)) ^ h.1) *
            spatialSideWeight hp N L a eta h
              (iteratedFacetMap n N
                (ReferenceAffineOrbitCount.topRepr hp orbit).realizationContinuousMap
                spatial r)))) = 0
    conv_lhs =>
      enter [2, orbit]
      rw [spatialSide_scaled_boundary hp N L a eta h orbit]
    simp_rw [Finset.mul_sum]
    conv_lhs =>
      enter [2, orbit]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro theta htheta
    exact fixed_refined_side_cancels N L n hp a eta h theta

/-- Nonhorizontal cancellation specialized to the compatible generic perturbation. -/
theorem Result.nonhorizontalContribution_eq_zero
    (hp : Nat.Prime p) (N L : Nat)
    {F0 F1 : EquivariantCoordinateHomotopy.ZeroFreeMap hp}
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F0 F1)
    (m : Real) (R : Result hp N L H m) :
    nonhorizontalContribution hp N L R.assignment = 0 :=
  NRR.FoxNeuwirthOrderComplex.EquivariantPrismNonhorizontalCancellation.nonhorizontalContribution_eq_zero_core
    hp N L R.assignment

/-- The two horizontal contributions of a generic perturbation are opposite. -/
theorem Result.lowerHorizontalContribution_eq_neg_upperHorizontalContribution
    (hp : Nat.Prime p) (N L : Nat)
    {F0 F1 : EquivariantCoordinateHomotopy.ZeroFreeMap hp}
    (H : EquivariantCoordinateHomotopy.ZeroFreeHomotopy hp F0 F1)
    (m : Real) (R : Result hp N L H m) :
    lowerHorizontalContribution hp N L R.assignment =
      -upperHorizontalContribution hp N L R.assignment :=
  _root_.NRR.FoxNeuwirthOrderComplex.EquivariantPrismGlobalCancellation.lowerHorizontalContribution_eq_neg_upper_of_nonhorizontal_eq_zero
    hp N L R.assignment R.generalPosition
    (_root_.NRR.FoxNeuwirthOrderComplex.EquivariantPrismNonhorizontalCancellation.nonhorizontalContribution_eq_zero_core
      hp N L R.assignment)

end EquivariantPrismNonhorizontalCancellation
end FoxNeuwirthOrderComplex
end NRR
