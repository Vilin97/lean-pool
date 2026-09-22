/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismHorizontalEndpointIdentification
/-!
# Refinement words carried by a prescribed boundary face

A barycentric refinement word on a `p - 1` dimensional endpoint simplex must be lifted to the
ambient `p` dimensional prism simplex.  At refinement level zero the endpoint is an original
staircase facet.  After one or more barycentric refinements, each endpoint summand appears as the
last facet of an ambient barycentric simplex.  This module supplies the corresponding ambient
permutations and proves the affine compatibility identity used by both the stable endpoint
interpolant and the explicit middle collar.
-/

namespace NRR

open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace EndpointFaceRefinement

open EquivariantPrismNonhorizontalCancellation
open EquivariantPrismHorizontalEndpointIdentification
open RefinedAffineMap
open SubdivisionPrismCharts

variable {p : Nat}

/-- Extend a spatial permutation by fixing the interval vertex. -/
def extendSpatialPermutation
    (pi : Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p + 1)) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr pi (Equiv.refl (Fin 1))).trans finSumFinEquiv)

/-- Extend every permutation in a spatial refinement word while fixing the interval vertex. -/
def extendSpatialRefinementWord
    (L : Nat) (eta : RefinementWord p L) : PrismRefinementWord p L :=
  fun r => extendSpatialPermutation (eta r)

/-- The block extension is the last-face permutation associated with the final boundary face. -/
theorem extendSpatialPermutation_eq_lastFaceEquiv
    (n : Nat) (pi : Equiv.Perm (Fin (n + 1))) :
    extendSpatialPermutation pi =
      lastFaceEquiv n (Fin.last (n + 1), pi) := by
  apply Equiv.ext
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [lastFaceEquiv_apply]
    have hlast :
        ((extendLastPerm pi).trans (insertLastPerm (Fin.last (n + 1))))
            (Fin.last (n + 1)) = Fin.last (n + 1) := by
      convert lastFaceMap_apply_last (Fin.last (n + 1)) pi using 1
      apply congrArg ((extendLastPerm pi).trans
        (insertLastPerm (Fin.last (n + 1))))
      apply Fin.ext
      rfl
    rw [hlast]
    apply Fin.ext
    simp [extendSpatialPermutation]
  · rw [lastFaceEquiv_apply]
    have hcast :
        ((extendLastPerm pi).trans (insertLastPerm (Fin.last (n + 1)))) j.castSucc =
          (Fin.last (n + 1)).succAbove (pi j) := by
      exact lastFaceMap_apply_castSucc (Fin.last (n + 1)) pi j
    rw [hcast]
    apply Fin.ext
    simp [extendSpatialPermutation]

/-- Iterated block extension carries the final facet of the refined ambient simplex to the
corresponding iterated refinement of the final boundary face. -/
theorem affineCompMap_extendSpatialRefinementWord_lastFace
    (n L : Nat) (eta : Fin L → Equiv.Perm (Fin (n + 1))) (x : Delta n) :
    affineCompMap (n + 1) L (extendSpatialRefinementWord L eta)
        (cofacePoint n (Fin.last (n + 1)) x) =
      cofacePoint n (Fin.last (n + 1)) (affineCompMap n L eta x) := by
  induction L generalizing x with
  | zero =>
      simp []
  | succ L ih =>
      have hstep := congrFun
        (oneStep_last_face_eq n (fun z : Delta (n + 1) => z)
          (Fin.last (n + 1)) (eta (Fin.last L))) x
      have hstep' :
          affineSubdivContinuousMap (n + 1)
              (extendSpatialPermutation (eta (Fin.last L)))
              (cofacePoint n (Fin.last (n + 1)) x) =
            cofacePoint n (Fin.last (n + 1))
              (affineSubdivContinuousMap n (eta (Fin.last L)) x) := by
        simpa [iteratedFacetMap, iteratedBoundaryMap, affineCompMap_succ,
          affineSubdivContinuousMap_apply,
          extendSpatialPermutation_eq_lastFaceEquiv] using hstep
      rw [affineCompMap_succ, affineCompMap_succ]
      change
        affineCompMap (n + 1) L
            (extendSpatialRefinementWord L (fun i => eta i.castSucc))
            (affineSubdivContinuousMap (n + 1)
              (extendSpatialPermutation (eta (Fin.last L)))
              (cofacePoint n (Fin.last (n + 1)) x)) =
          cofacePoint n (Fin.last (n + 1))
            (affineCompMap n L (fun i => eta i.castSucc)
              (affineSubdivContinuousMap n (eta (Fin.last L)) x))
      rw [hstep']
      exact ih (fun i => eta i.castSucc)
        (affineSubdivContinuousMap n (eta (Fin.last L)) x)

/-- Lift a refinement permutation of one boundary face to an ambient permutation whose final
facet is that boundary face. -/
noncomputable def liftFacePermutation
    (n : Nat) (j : Fin (n + 2)) (pi : Equiv.Perm (Fin (n + 1))) :
    Equiv.Perm (Fin (n + 2)) :=
  (extendLastPerm pi).trans (insertLastPerm j)

@[simp] theorem liftFacePermutation_eq_lastFaceEquiv
    (n : Nat) (j : Fin (n + 2)) (pi : Equiv.Perm (Fin (n + 1))) :
    liftFacePermutation n j pi = lastFaceEquiv n (j, pi) := rfl

/-- Lift the first permutation to the prescribed original face; subsequent permutations
preserve the canonical last face of the already-refined simplex. -/
noncomputable def liftFaceRefinementWord
    (n L : Nat) (j : Fin (n + 2))
    (eta : Fin L → Equiv.Perm (Fin (n + 1))) :
    Fin L → Equiv.Perm (Fin (n + 2)) :=
  match L with
  | 0 => fun r => Fin.elim0 r
  | _ + 1 => Fin.cases (liftFacePermutation n j (eta 0))
      (fun r => extendSpatialPermutation (eta r.succ))

/-- The facet omitted by the canonical endpoint occurrence.  Without further subdivision it is the
original face `j`; after at least one subdivision it is the final facet of a barycentric simplex. -/
def endpointOmitted
    (n : Nat) : (L : Nat) → Fin (n + 2) → Fin (n + 2)
  | 0, j => j
  | _ + 1, _ => Fin.last (n + 1)

/-- Iterated lifted refinement realizes the requested refined original boundary face. -/
theorem affineCompMap_liftFaceRefinementWord
    (n L : Nat) (j : Fin (n + 2))
    (eta : Fin L → Equiv.Perm (Fin (n + 1))) (x : Delta n) :
    affineCompMap (n + 1) L (liftFaceRefinementWord n L j eta)
        (cofacePoint n (endpointOmitted n L j) x) =
      cofacePoint n j (affineCompMap n L eta x) := by
  induction L generalizing x with
  | zero =>
      simp [liftFaceRefinementWord, endpointOmitted]
  | succ L ih =>
      cases L with
      | zero =>
          have hstep := congrFun
            (oneStep_last_face_eq n (fun z : Delta (n + 1) => z) j (eta 0)) x
          rw [affineCompMap_succ, affineCompMap_succ]
          simpa [liftFaceRefinementWord, endpointOmitted, iteratedFacetMap,
            iteratedBoundaryMap, affineCompMap_succ, affineSubdivContinuousMap_apply,
            liftFacePermutation_eq_lastFaceEquiv] using hstep
      | succ L =>
          have hstep := congrFun
            (oneStep_last_face_eq n (fun z : Delta (n + 1) => z)
              (Fin.last (n + 1)) (eta (Fin.last (L + 1)))) x
          have hstep' :
              affineSubdivContinuousMap (n + 1)
                  (extendSpatialPermutation (eta (Fin.last (L + 1))))
                  (cofacePoint n (Fin.last (n + 1)) x) =
                cofacePoint n (Fin.last (n + 1))
                  (affineSubdivContinuousMap n (eta (Fin.last (L + 1))) x) := by
            simpa [iteratedFacetMap, iteratedBoundaryMap, affineCompMap_succ,
              affineSubdivContinuousMap_apply,
              extendSpatialPermutation_eq_lastFaceEquiv] using hstep
          have hprefix :
              (fun i : Fin (L + 1) =>
                liftFaceRefinementWord n (L + 1 + 1) j eta i.castSucc) =
                liftFaceRefinementWord n (L + 1) j (fun i => eta i.castSucc) := by
            funext i
            refine Fin.cases ?_ (fun r => ?_) i <;> rfl
          have hfinal :
              liftFaceRefinementWord n (L + 1 + 1) j eta (Fin.last (L + 1)) =
                extendSpatialPermutation (eta (Fin.last (L + 1))) := by
            rfl
          rw [affineCompMap_succ (n + 1) (L + 1)
            (liftFaceRefinementWord n (L + 1 + 1) j eta),
            affineCompMap_succ n (L + 1) eta, hprefix, hfinal]
          simp only [ContinuousMap.comp_apply]
          change
            affineCompMap (n + 1) (L + 1)
                (liftFaceRefinementWord n (L + 1) j (fun i => eta i.castSucc))
                (affineSubdivContinuousMap (n + 1)
                  (extendSpatialPermutation (eta (Fin.last (L + 1))))
                  (cofacePoint n (Fin.last (n + 1)) x)) =
              cofacePoint n j
                (affineCompMap n (L + 1) (fun i => eta i.castSucc)
                  (affineSubdivContinuousMap n (eta (Fin.last (L + 1))) x))
          rw [hstep']
          exact ih (fun i => eta i.castSucc)
            (affineSubdivContinuousMap n (eta (Fin.last (L + 1))) x)

/-- Last-face lifting for a boundary face of `Fin (p + 1)`, without exposing predecessor casts in
subsequent definitions. -/
noncomputable def liftBoundaryPermutation
    {p : Nat} (j : Fin (p + 1)) (pi : Equiv.Perm (Fin p)) : Equiv.Perm (Fin (p + 1)) :=
  match p with
  | 0 => Equiv.refl (Fin 1)
  | n + 1 => liftFacePermutation n j pi

/-- Lift an endpoint refinement word to the ambient prism simplex. -/
noncomputable def liftBoundaryRefinementWord
    (L : Nat) (j : Fin (p + 1)) (eta : RefinementWord p L) :
    PrismRefinementWord p L :=
  match L with
  | 0 => fun r => Fin.elim0 r
  | _ + 1 => Fin.cases (liftBoundaryPermutation j (eta 0))
      (fun r => extendSpatialPermutation (eta r.succ))

/-- Facet omitted by a canonical endpoint occurrence. -/
def endpointOmittedPrime
    (L : Nat) (j : Fin (p + 1)) : Fin (p + 1) :=
  match L with
  | 0 => j
  | _ + 1 => Fin.last p

/-- The generic lift agrees with the standard last-face decomposition in successor dimensions. -/
theorem liftBoundaryPermutation_eq_liftFacePermutation
    (n : Nat) (j : Fin (n + 2)) (pi : Equiv.Perm (Fin (n + 1))) :
    liftBoundaryPermutation j pi = liftFacePermutation n j pi := rfl

/-- In successor dimensions, the generic boundary word is the canonical face-refinement word. -/
theorem liftBoundaryRefinementWord_eq_liftFaceRefinementWord
    (n L : Nat) (j : Fin (n + 2))
    (eta : Fin L → Equiv.Perm (Fin (n + 1))) :
    liftBoundaryRefinementWord L j eta = liftFaceRefinementWord n L j eta := by
  cases L with
  | zero => rfl
  | succ L =>
      funext r
      refine Fin.cases ?_ (fun i => ?_) r <;> rfl

/-- In successor dimensions, the two canonical omitted-index descriptions agree. -/
theorem endpointOmittedPrime_eq_endpointOmitted
    (n L : Nat) (j : Fin (n + 2)) :
    endpointOmittedPrime L j = endpointOmitted n L j := by
  cases L <;> rfl

/-- A lifted endpoint refinement realizes the requested refined boundary face. -/
theorem affineCompMap_liftBoundaryRefinementWord
    (n L : Nat) (j : Fin (n + 2))
    (eta : Fin L → Equiv.Perm (Fin (n + 1))) (x : Delta n) :
    affineCompMap (n + 1) L (liftBoundaryRefinementWord L j eta)
        (cofacePoint n (endpointOmittedPrime L j) x) =
      cofacePoint n j (affineCompMap n L eta x) := by
  rw [liftBoundaryRefinementWord_eq_liftFaceRefinementWord n L j eta,
    endpointOmittedPrime_eq_endpointOmitted n L j]
  exact affineCompMap_liftFaceRefinementWord n L j eta x

/-- Split a refinement word of length `N + L` into its prefix and tail. -/
def splitRefinementWord
    (N L : Nat) (rho : RefinementWord p (N + L)) :
    RefinementWord p N × RefinementWord p L :=
  (fun i => rho (Fin.castAdd L i), fun i => rho (Fin.natAdd N i))

/-- Concatenate two refinement words. -/
def appendRefinementWord
    (N L : Nat) (rho : RefinementWord p N) (eta : RefinementWord p L) :
    RefinementWord p (N + L) :=
  Fin.addCases rho eta

attribute [local simp] ContinuousMap.comp_apply

/-- Affine refinement along a concatenated word is tail refinement followed by prefix refinement. -/
theorem affineCompMap_append
    (n N L : Nat)
    (rho : Fin N → Equiv.Perm (Fin (n + 1)))
    (eta : Fin L → Equiv.Perm (Fin (n + 1))) :
    affineCompMap n (N + L) (appendRefinementWord N L rho eta) =
      (affineCompMap n N rho).comp (affineCompMap n L eta) := by
  induction L with
  | zero =>
      have hword : appendRefinementWord N 0 rho eta = rho := by
        funext i
        change Fin.addCases rho eta (Fin.castAdd 0 i) = rho i
        rw [Fin.addCases_left]
      rw [hword]
      rfl
  | succ L ih =>
      apply ContinuousMap.ext
      intro x
      change
        affineCompMap n ((N + L) + 1)
            (fun i => appendRefinementWord N (L + 1) rho eta (Fin.cast (by omega) i)) x = _
      rw [affineCompMap_succ]
      simp only [ContinuousMap.comp_apply]
      have hprefix :
          (fun i : Fin (N + L) =>
            appendRefinementWord N (L + 1) rho eta
              (Fin.cast (by omega) i.castSucc)) =
            appendRefinementWord N L rho (fun i => eta i.castSucc) := by
        funext i
        refine Fin.addCases ?_ ?_ i
        · intro j
          have hi :
              Fin.cast (by omega) (Fin.castAdd L j).castSucc =
                Fin.castAdd (L + 1) j := by
            apply Fin.ext
            rfl
          rw [hi]
          simp [appendRefinementWord]
        · intro j
          have hi :
              Fin.cast (by omega) (Fin.natAdd N j).castSucc =
                Fin.natAdd N j.castSucc := by
            apply Fin.ext
            rfl
          rw [hi]
          simp [appendRefinementWord]
      have hfinal :
          appendRefinementWord N (L + 1) rho eta
              (Fin.cast (by omega) (Fin.last (N + L))) = eta (Fin.last L) := by
        have hi :
            Fin.cast (by omega) (Fin.last (N + L)) =
              Fin.natAdd N (Fin.last L) := by
          apply Fin.ext
          simp
        unfold appendRefinementWord
        rw [hi]
        exact Fin.addCases_right (Fin.last L)
      rw [hprefix, hfinal]
      simpa only [ContinuousMap.comp_apply, affineCompMap_succ] using
        congrArg (fun f : C(Delta n, Delta n) =>
          f (affineSubdivContinuousMap n (eta (Fin.last L)) x))
          (ih (fun i => eta i.castSucc))

@[simp] theorem split_appendRefinementWord
    (N L : Nat) (rho : RefinementWord p N) (eta : RefinementWord p L) :
    splitRefinementWord N L (appendRefinementWord N L rho eta) = (rho, eta) := by
  ext i <;> simp [splitRefinementWord, appendRefinementWord]

@[simp] theorem append_splitRefinementWord
    (N L : Nat) (rho : RefinementWord p (N + L)) :
    appendRefinementWord N L (splitRefinementWord N L rho).1
      (splitRefinementWord N L rho).2 = rho := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [splitRefinementWord, appendRefinementWord]

/-- Reindex a horizontal endpoint simplex as a top cell at the combined refinement level. -/
noncomputable def endpointTopCell
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    TopCell hp (N + L) :=
  (q.1, appendRefinementWord N L q.2 eta)

/-- For a prime cardinality, the chart's simplex-index transport is the endpoint transport. -/
theorem refinementIndexPerm_eq_endpointRefinementPerm
    (hp : Nat.Prime p) (sigma : Equiv.Perm (Fin p)) :
    Simplex.refinementIndexPerm sigma =
      endpointRefinementWord hp 1 (fun _ => sigma) 0 := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ p => simp [Simplex.refinementIndexPerm, endpointRefinementWord]

/-- The endpoint spatial map is the ordinary chart at the combined refinement level. -/
theorem endpointSpatialMap_eq_chart
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp N) (eta : RefinementWord p L) :
    endpointSpatialMap hp N L q eta =
      chart hp (N + L) (endpointTopCell hp N L q eta) := by
  cases p with
  | zero => exact (Nat.not_prime_zero hp).elim
  | succ p =>
      have hrho :
          (fun k => Simplex.refinementIndexPerm (q.2 k)) =
            endpointRefinementWord hp N q.2 := by
        funext k
        exact refinementIndexPerm_eq_endpointRefinementPerm hp (q.2 k)
      have happ :
          (fun k => Simplex.refinementIndexPerm
            (appendRefinementWord N L q.2 eta k)) =
            appendRefinementWord N L (endpointRefinementWord hp N q.2)
              (endpointRefinementWord hp L eta) := by
        funext k
        refine Fin.addCases ?_ ?_ k
        · intro i
          simp [appendRefinementWord, endpointRefinementWord,
            Simplex.refinementIndexPerm]
        · intro i
          simp [appendRefinementWord, endpointRefinementWord,
            Simplex.refinementIndexPerm]
      funext x
      simp only [endpointSpatialMap, endpointTopCell, RefinedAffineMap.chart,
        Simplex.refinedContinuousMap, ContinuousMap.comp_apply]
      rw [hrho, happ, affineCompMap_append]
      rfl

/-- Every combined-level top cell has a split endpoint representation. -/
theorem endpointTopCell_surjective
    (hp : Nat.Prime p) (N L : Nat)
    (q : TopCell hp (N + L)) :
    ∃ q₀ : TopCell hp N, ∃ eta : RefinementWord p L,
      endpointTopCell hp N L q₀ eta = q := by
  refine ⟨(q.1, (splitRefinementWord N L q.2).1),
    (splitRefinementWord N L q.2).2, ?_⟩
  cases q
  simp [endpointTopCell]

end EndpointFaceRefinement
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
