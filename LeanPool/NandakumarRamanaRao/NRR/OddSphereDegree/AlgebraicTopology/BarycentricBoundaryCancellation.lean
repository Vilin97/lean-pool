/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionOperator
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.AffineInternalSwapFace
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.PermSignAdjacentSwap
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.AffineLastFaceIdentity
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.PermSignLastFaceFinished
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricFiniteCancellation
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Tactic

/-!
# Generator-level barycentric boundary cancellation `∂ (sd σ) = sd (∂ σ)`

This file proves the hard finite double-sum cancellation underlying the fact that
the degree-wise barycentric subdivision operator commutes with the singular
boundary on a single basis generator.

The main result is `expandedBarycentricBoundaryCancellation`:

```text
∂ (sd σ) = sd (∂ σ)
```

stated over the actual expanded sums, using the actual singular-boundary formula
(`singularBoundary_chainGenerator_formula`) and the actual subdivision operator
(`barycentricSubdivisionGenerator` / `barycentricSubdivisionLinearMap`).

## How the cancellation works

After expanding both sides on a generator `σ : singularSimplices X (n+1)` we get

```text
∂(sd σ) = Σ_{π} sign(π) Σ_{i : Fin (n+2)} (-1)^i [face_i (σ ∘ a_π)] .
```

Splitting the inner face index `i` into internal faces `i = castSucc i'`
(`i' : Fin (n+1)`) and the last face `i = Fin.last (n+1)`:

* **Internal faces cancel.** For a fixed internal index `i'`, pairing each
 permutation `π` with `π' = (swap (castSucc i') (succ i')).trans π` gives a
 fixed-point-free involution under which the affine faces are *equal*
 (`faceSimplex_internal_swap_eq`, from `affineSubdiv_face_internal_swap`) while
 the signs are *opposite* (`permSignCoeff_adjacent_swap`). Hence the sum over
 all permutations is `0`, via `internal_faces_double_sum_cancel`.

* **Last faces reindex.** Writing `j = π (last)` and letting `ρ : Perm (Fin (n+1))`
 be the induced permutation on the remaining vertices, the last face is the
 barycentric subdivision of the `j`-th boundary face of `σ`
 (`faceSimplex_last_eq_subdiv_faceData`, from
 `affineSubdiv_face_last_eq_boundary_subdiv`) and the signs match
 (`permSignCoeff_last_face_of_faceData`). The bijection
 `lastFaceEquiv : (Fin (n+2) × Perm (Fin (n+1))) ≃ Perm (Fin (n+2))`,
 `(j, ρ) ↦ (extendLastPerm ρ).trans (insertLastPerm j)`, reindexes the last-face
 sum onto `sd (∂ σ)`.
-/

open scoped BigOperators
open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open Finset

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-! ## 1. Naturality of `toSSetObjEquiv` and the topological coface map -/

/-- **Naturality of `TopCat.toSSetObjEquiv`.** Applying the simplicial-set map
`(toSSet.obj X).map g.op` corresponds, under `toSSetObjEquiv`, to precomposition
with the topological realization `toTop₀.map g` of the simplex-category morphism
`g`. -/
theorem toSSetObjEquiv_map_op_naturality (X : TopCat.{0}) (n m : ℕ)
    (g : (⦋n⦌ : SimplexCategory) ⟶ ⦋m⦌)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (⦋m⦌ : SimplexCategory))) :
    (TopCat.toSSetObjEquiv X (Opposite.op (⦋n⦌ : SimplexCategory)))
        ((TopCat.toSSet.obj X).map g.op σ)
      = (TopCat.toSSetObjEquiv X (Opposite.op (⦋m⦌ : SimplexCategory)) σ).comp
          (SimplexCategory.toTop₀.map g).hom := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- The topological coface map `Δⁿ → Δⁿ⁺¹` deleting the `k`-th vertex, as the
affine inclusion sending vertex `t` to vertex `k.succAbove t`. -/
noncomputable def cofaceTop (n : ℕ) (k : Fin (n + 2)) : C(Delta n, Delta (n + 1)) :=
  ⟨SphereOddDegree.FiniteSimplex.map (S := ℝ) (Fin.succAbove k), SphereOddDegree.FiniteSimplex.continuous_map _⟩

/-- The `k`-coordinate of `cofaceTop n k y` is zero: the affine coface never hits
the deleted vertex `k`. -/
theorem cofaceTop_apply_base (n : ℕ) (k : Fin (n + 2)) (y : Delta n) :
    (cofaceTop n k y : Fin (n + 2) → ℝ) k = 0 := by
  change (SphereOddDegree.FiniteSimplex.map (S := ℝ) (Fin.succAbove k) y : Fin (n + 2) → ℝ) k = 0
  rw [SphereOddDegree.FiniteSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  apply Finset.sum_eq_zero
  intro x hx
  exact (Fin.succAbove_ne k x (Finset.mem_filter.mp hx).2).elim

/-- The last coface `cofaceTop n (last)` is the standard `castSucc` inclusion:
its `castSucc t` coordinate is the `t` coordinate of `y`. -/
theorem cofaceTop_last_castSucc (n : ℕ) (t : Fin (n + 1)) (y : Delta n) :
    (cofaceTop n (Fin.last (n + 1)) y : Fin (n + 2) → ℝ) (Fin.castSucc t) = y t := by
  change (SphereOddDegree.FiniteSimplex.map (S := ℝ) (Fin.succAbove (Fin.last (n + 1))) y : Fin (n + 2) → ℝ)
      (Fin.castSucc t) = y t
  rw [SphereOddDegree.FiniteSimplex.map_coe, FunOnFinite.linearMap_apply_apply, Fin.succAbove_last]
  rw [Finset.sum_eq_single t]
  · intro b hb hbt
    exact (hbt (Fin.castSucc_injective _ (Finset.mem_filter.mp hb).2)).elim
  · intro h
    exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim

/-- The topological realization of the coface morphism `δ k` is the affine coface
`cofaceTop n k`. -/
theorem cofaceTop_eq (n : ℕ) (k : Fin (n + 2))
    (y : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    intrinsicSimplexCoordinates (n + 1)
        ((SimplexCategory.toTop₀.map (SimplexCategory.δ k)).hom y) =
      cofaceTop n k (intrinsicSimplexCoordinates n y) := by
  apply Subtype.ext
  change ⇑(Finsupp.mapDomain (Fin.succAbove k) y.weights) =
    FunOnFinite.map (Fin.succAbove k) (⇑y.weights)
  simp only [FunOnFinite.map, Finsupp.equivFunOnFinite_symm_coe]
  rfl

/-- **Face as a continuous map.** The `k`-th boundary face of a singular simplex
is, under `toSSetObjEquiv`, the precomposition with the topological coface
`cofaceTop n k`. -/
theorem faceSimplex_continuousMap (X : TopCat.{0}) (n : ℕ) (k : Fin (n + 2))
    (σ : singularSimplices X (n + 1)) :
    singularSimplexAsContinuousMap X n (AlexanderWhitney.faceSimplex X n k σ)
      = (singularSimplexAsContinuousMap X (n + 1) σ).comp (cofaceTop n k) := by
  rw [singularSimplexAsContinuousMap, singularSimplexAsContinuousMap,
    AlexanderWhitney.faceSimplex,
    toSSetObjEquiv_map_op_naturality X n (n + 1) (SimplexCategory.δ k) σ]
  apply ContinuousMap.ext
  intro y
  change ((X.toSSetObjEquiv (Opposite.op ⦋n + 1⦌)) σ)
      ((SimplexCategory.toTop₀.map (SimplexCategory.δ k)).hom
        ((intrinsicSimplexCoordinates n).symm y)) =
    ((X.toSSetObjEquiv (Opposite.op ⦋n + 1⦌)) σ)
      ((intrinsicSimplexCoordinates (n + 1)).symm (cofaceTop n k y))
  apply congrArg ((X.toSSetObjEquiv (Opposite.op ⦋n + 1⦌)) σ)
  apply (intrinsicSimplexCoordinates (n + 1)).injective
  simpa using cofaceTop_eq n k ((intrinsicSimplexCoordinates n).symm y)

/-! ## 2. Singular-simplex equality and the subdivision summand as a map -/

/-- Two singular simplices coincide as soon as their associated continuous maps
do (`toSSetObjEquiv` is injective). -/
theorem singularSimplices_ext {X : TopCat.{0}} {n : ℕ} {a b : singularSimplices X n}
    (h : singularSimplexAsContinuousMap X n a = singularSimplexAsContinuousMap X n b) : a = b := by
  have h' := congrArg (continuousMapAsSingularSimplex X n) h
  simpa using h'

/-- The barycentric subdivision summand `σ ∘ a_π`, viewed as a continuous map. -/
theorem barycentricSubdivSimplex_continuousMap (X : TopCat.{0}) (n : ℕ)
    (π : Equiv.Perm (Fin (n + 1))) (σ : singularSimplices X n) :
    singularSimplexAsContinuousMap X n (barycentricSubdivSimplex X n π σ)
      = (singularSimplexAsContinuousMap X n σ).comp (affineSubdivContinuousMap n π) := by
  exact singularSimplexAsContinuousMap_continuousMapAsSingularSimplex X n _

/-! ## 3. Internal-face bridge: affine faces agree under adjacent swap -/

/-- **Internal-face identity at the chain level.** For an internal face index
`castSucc i`, the corresponding boundary face of the `π`-subdivision summand
equals that of the adjacent-swapped permutation summand. -/
theorem faceSimplex_internal_swap_eq (X : TopCat.{0}) (n : ℕ)
    (π : Equiv.Perm (Fin (n + 2))) (i : Fin (n + 1)) (σ : singularSimplices X (n + 1)) :
    AlexanderWhitney.faceSimplex X n (Fin.castSucc i)
        (barycentricSubdivSimplex X (n + 1) π σ)
      = AlexanderWhitney.faceSimplex X n (Fin.castSucc i)
          (barycentricSubdivSimplex X (n + 1)
            ((Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π) σ) := by
  apply singularSimplices_ext
  rw [faceSimplex_continuousMap, faceSimplex_continuousMap,
    barycentricSubdivSimplex_continuousMap, barycentricSubdivSimplex_continuousMap]
  apply ContinuousMap.ext
  intro y
  simp only [ContinuousMap.comp_apply, affineSubdivContinuousMap_apply]
  congr 1
  exact affineSubdiv_face_internal_swap π i (cofaceTop n (Fin.castSucc i) y)
    (cofaceTop_apply_base n (Fin.castSucc i) y)

/-! ## 4. Last-face bridge and the last-face permutation bookkeeping -/

/-- `extendLastPerm ρ` sends `castSucc t` to `castSucc (ρ t)`. -/
theorem extendLastPerm_castSucc {n : ℕ} (ρ : Equiv.Perm (Fin (n + 1))) (t : Fin (n + 1)) :
    extendLastPerm ρ (Fin.castSucc t) = Fin.castSucc (ρ t) := by
  have h := Equiv.Perm.viaFintypeEmbedding_apply_image ρ Fin.castSuccOrderEmb.toEmbedding t
  exact h

/-- `extendLastPerm ρ` fixes the last vertex. -/
theorem extendLastPerm_lastVertex {n : ℕ} (ρ : Equiv.Perm (Fin (n + 1))) :
    extendLastPerm ρ (lastVertex n) = lastVertex n := by
  have hmem : (lastVertex n) ∉ Set.range (Fin.castSuccOrderEmb (n := n + 1)).toEmbedding := by
    rw [Set.mem_range]
    rintro ⟨t, ht⟩
    have : (Fin.castSucc t : Fin (n + 2)) = lastVertex n := ht
    have hval := congrArg Fin.val this
    simp [lastVertex] at hval
    omega
  have h := Equiv.Perm.viaFintypeEmbedding_apply_notMem_range ρ
    Fin.castSuccOrderEmb.toEmbedding hmem
  exact h

/-- The image of `(j, ρ)` under the last-face decomposition sends the last vertex
to `j`. -/
theorem lastFaceMap_apply_last {n : ℕ} (j : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1))) :
    ((extendLastPerm ρ).trans (insertLastPerm j)) (lastVertex n) = j := by
  rw [Equiv.trans_apply, extendLastPerm_lastVertex, insertLastPerm_last]

/-- The image of `(j, ρ)` under the last-face decomposition sends `castSucc t` to
`j.succAbove (ρ t)`. -/
theorem lastFaceMap_apply_castSucc {n : ℕ} (j : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1)))
    (t : Fin (n + 1)) :
    ((extendLastPerm ρ).trans (insertLastPerm j)) (Fin.castSucc t) = j.succAbove (ρ t) := by
  rw [Equiv.trans_apply, extendLastPerm_castSucc, insertLastPerm_castSucc]

/-- **Last-face identity at the chain level, face-data form.** If `j = π (last)`
and, on the remaining vertices, `π` is `j.succAbove ∘ ρ`, then the last boundary
face of the `π`-subdivision summand is the `ρ`-subdivision summand of the `j`-th
boundary face of `σ`. -/
theorem faceSimplex_last_eq_subdiv_faceData (X : TopCat.{0}) (n : ℕ)
    (π : Equiv.Perm (Fin (n + 2))) (j : Fin (n + 2)) (ρ : Equiv.Perm (Fin (n + 1)))
    (hρ : ∀ t : Fin (n + 1), j.succAbove (ρ t) = π (Fin.castSucc t))
    (σ : singularSimplices X (n + 1)) :
    AlexanderWhitney.faceSimplex X n (lastVertex n)
        (barycentricSubdivSimplex X (n + 1) π σ)
      = barycentricSubdivSimplex X n ρ (AlexanderWhitney.faceSimplex X n j σ) := by
  apply singularSimplices_ext
  rw [faceSimplex_continuousMap, barycentricSubdivSimplex_continuousMap,
    barycentricSubdivSimplex_continuousMap, faceSimplex_continuousMap]
  apply ContinuousMap.ext
  intro y
  simp only [ContinuousMap.comp_apply, affineSubdivContinuousMap_apply]
  congr 1
  -- key affine identity: a_π (cofaceTop last y) = cofaceTop j (a_ρ y)
  have hx :=
    affineSubdiv_face_last_eq_boundary_subdiv π (Fin.succAbove j) ρ hρ
      (cofaceTop n (lastVertex n) y) y
      (by
        have := cofaceTop_apply_base n (lastVertex n) y
        simpa [lastVertex] using this)
      (fun k => (cofaceTop_last_castSucc n k y).symm)
  -- `cofaceTop n j` is exactly `SphereOddDegree.FiniteSimplex.map (j.succAbove)`
  rw [hx]
  rfl

/-! ## 5. The last-face reindexing equivalence -/

/-- The map underlying the last-face decomposition equivalence:
`(j, ρ) ↦ (extendLastPerm ρ).trans (insertLastPerm j)`. -/
noncomputable def lastFaceMap (n : ℕ) :
    (Fin (n + 2) × Equiv.Perm (Fin (n + 1))) → Equiv.Perm (Fin (n + 2)) :=
  fun p => (extendLastPerm p.2).trans (insertLastPerm p.1)

theorem lastFaceMap_injective (n : ℕ) : Function.Injective (lastFaceMap n) := by
  rintro ⟨j, ρ⟩ ⟨j', ρ'⟩ h
  simp only [lastFaceMap] at h
  have hj : j = j' := by
    have h1 : ((extendLastPerm ρ).trans (insertLastPerm j)) (lastVertex n)
        = ((extendLastPerm ρ').trans (insertLastPerm j')) (lastVertex n) := by rw [h]
    rwa [lastFaceMap_apply_last, lastFaceMap_apply_last] at h1
  subst hj
  have hρ : ρ = ρ' := by
    apply Equiv.ext
    intro t
    have h2 : ((extendLastPerm ρ).trans (insertLastPerm j)) (Fin.castSucc t)
        = ((extendLastPerm ρ').trans (insertLastPerm j)) (Fin.castSucc t) := by rw [h]
    rw [lastFaceMap_apply_castSucc, lastFaceMap_apply_castSucc] at h2
    exact Fin.succAbove_right_injective h2
  subst hρ
  rfl

/-- The last-face decomposition equivalence
`(Fin (n+2) × Perm (Fin (n+1))) ≃ Perm (Fin (n+2))`. -/
noncomputable def lastFaceEquiv (n : ℕ) :
    (Fin (n + 2) × Equiv.Perm (Fin (n + 1))) ≃ Equiv.Perm (Fin (n + 2)) :=
  Equiv.ofBijective (lastFaceMap n) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨lastFaceMap_injective n, ?_⟩
    rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_fin,
      Fintype.card_fin, Nat.factorial_succ (n + 1)])

@[simp] theorem lastFaceEquiv_apply (n : ℕ) (p : Fin (n + 2) × Equiv.Perm (Fin (n + 1))) :
    lastFaceEquiv n p = (extendLastPerm p.2).trans (insertLastPerm p.1) := rfl

/-! ## 6. Internal involution facts -/

theorem internalSwap_involutive {n : ℕ} (i : Fin (n + 1)) :
    Function.Involutive
      (fun π : Equiv.Perm (Fin (n + 2)) =>
        (Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π) := by
  intro π
  ext x
  simp [Equiv.trans_apply, Equiv.swap_apply_self]

theorem internalSwap_ne {n : ℕ} (i : Fin (n + 1)) (π : Equiv.Perm (Fin (n + 2))) :
    (Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π ≠ π := by
  intro h
  have hh := congrArg (fun e : Equiv.Perm (Fin (n + 2)) => e (Fin.castSucc i)) h
  simp only [Equiv.trans_apply, Equiv.swap_apply_left] at hh
  exact (castSucc_ne_succ_adjacent i) (π.injective hh).symm

/-! ## 7. Internal faces cancel -/

/-- The internal-face double sum vanishes by adjacent-swap involution
cancellation. -/
theorem internal_faces_sum_eq_zero (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X (n + 1)) :
    (∑ π : Equiv.Perm (Fin (n + 2)),
        ∑ i : Fin (n + 1),
          permSignCoeff R π •
            ((-1 : R) ^ (Fin.castSucc i).val •
              chainGenerator R X n
                (AlexanderWhitney.faceSimplex X n (Fin.castSucc i)
                  (barycentricSubdivSimplex X (n + 1) π σ)))) = 0 := by
  apply internal_faces_double_sum_cancel
    (swapFor := fun i π => (Equiv.swap (Fin.castSucc i) (Fin.succ i)).trans π)
    (hswap_invol := fun i => internalSwap_involutive i)
    (hswap_ne := fun i π => internalSwap_ne i π)
  intro i π
  rw [permSignCoeff_adjacent_swap,
    ← faceSimplex_internal_swap_eq X n π i σ]
  rw [neg_smul]

/-! ## 8. Last faces reindex to `sd (∂ σ)` -/

/-- The last-face sum equals `sd (∂ σ)` after reindexing by `lastFaceEquiv`. -/
theorem last_faces_sum_eq_subdiv_boundary (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X (n + 1)) :
    (∑ π : Equiv.Perm (Fin (n + 2)),
        permSignCoeff R π •
          ((-1 : R) ^ (Fin.last (n + 1)).val •
            chainGenerator R X n
              (AlexanderWhitney.faceSimplex X n (Fin.last (n + 1))
                (barycentricSubdivSimplex X (n + 1) π σ))))
      = ∑ i : Fin (n + 2),
          (-1 : R) ^ i.val •
            barycentricSubdivisionGenerator R X n (AlexanderWhitney.faceSimplex X n i σ) := by
  -- Expand the right-hand subdivision generator and reorganize as a sum over `(i, ρ)`.
  have hrhs : (∑ i : Fin (n + 2),
        (-1 : R) ^ i.val •
          barycentricSubdivisionGenerator R X n (AlexanderWhitney.faceSimplex X n i σ))
      = ∑ p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)),
          (-1 : R) ^ p.1.val •
            (permSignCoeff R p.2 •
              chainGenerator R X n
                (barycentricSubdivSimplex X n p.2 (AlexanderWhitney.faceSimplex X n p.1 σ))) := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [barycentricSubdivisionGenerator, Finset.smul_sum]
  rw [hrhs, ← Equiv.sum_comp (lastFaceEquiv n)]
  apply Finset.sum_congr rfl
  rintro ⟨j, ρ⟩ _
  simp only [lastFaceEquiv_apply, Fin.val_last]
  rw [show (Fin.last (n + 1) : Fin (n + 2)) = lastVertex n from rfl,
    faceSimplex_last_eq_subdiv_faceData X n ((extendLastPerm ρ).trans (insertLastPerm j)) j ρ
      (fun t => (lastFaceMap_apply_castSucc j ρ t).symm) σ,
    smul_smul,
    mul_comm (permSignCoeff R ((extendLastPerm ρ).trans (insertLastPerm j))) ((-1 : R) ^ (n + 1)),
    permSignCoeff_last_face_of_faceData R ((extendLastPerm ρ).trans (insertLastPerm j)) j ρ
      (lastFaceMap_apply_last j ρ).symm (fun t => (lastFaceMap_apply_castSucc j ρ t).symm),
    ← smul_smul]

/-! ## 9. Main theorem -/

/-- **Expanded barycentric boundary cancellation on a generator.**
The singular boundary of the barycentric subdivision of a generator equals the
barycentric subdivision of its boundary:
```text
∂ (sd σ) = sd (∂ σ).
```
This is proved over the actual expanded sums, splitting the boundary of the
subdivision into internal faces (which cancel) and last faces (which reindex to
`sd (∂ σ)`). -/
theorem expandedBarycentricBoundaryCancellation (R : Type) [CommRing R] (X : TopCat.{0}) (n : ℕ)
    (σ : singularSimplices X (n + 1)) :
    (singularBoundary R X n).hom (barycentricSubdivisionGenerator R X (n + 1) σ)
      = (barycentricSubdivisionLinearMap R X n).hom
          ((singularBoundary R X n).hom (chainGenerator R X (n + 1) σ)) := by
  -- Expand the left-hand side: `∂` of the subdivision over all permutations.
  have hLHS : (singularBoundary R X n).hom (barycentricSubdivisionGenerator R X (n + 1) σ)
      = ∑ π : Equiv.Perm (Fin (n + 2)), ∑ i : Fin (n + 2),
          permSignCoeff R π •
            ((-1 : R) ^ i.val •
              chainGenerator R X n
                (AlexanderWhitney.faceSimplex X n i (barycentricSubdivSimplex X (n + 1) π σ))) := by
    rw [barycentricSubdivisionGenerator, map_sum]
    apply Finset.sum_congr rfl
    intro π _
    rw [map_smul, singularBoundary_chainGenerator_formula, Finset.smul_sum]
  -- Expand the right-hand side: subdivision of the boundary.
  have hRHS : (barycentricSubdivisionLinearMap R X n).hom
        ((singularBoundary R X n).hom (chainGenerator R X (n + 1) σ))
      = ∑ i : Fin (n + 2),
          (-1 : R) ^ i.val •
            barycentricSubdivisionGenerator R X n (AlexanderWhitney.faceSimplex X n i σ) := by
    rw [singularBoundary_chainGenerator_formula, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, barycentricSubdivisionLinearMap_generator]
  rw [hLHS, hRHS]
  -- Split the inner face sum into internal faces and the last face.
  have hsplit : ∀ π : Equiv.Perm (Fin (n + 2)),
      (∑ i : Fin (n + 2),
          permSignCoeff R π •
            ((-1 : R) ^ i.val •
              chainGenerator R X n
                (AlexanderWhitney.faceSimplex X n i (barycentricSubdivSimplex X (n + 1) π σ))))
        = (∑ i : Fin (n + 1),
            permSignCoeff R π •
              ((-1 : R) ^ (Fin.castSucc i).val •
                chainGenerator R X n
                  (AlexanderWhitney.faceSimplex X n (Fin.castSucc i)
                    (barycentricSubdivSimplex X (n + 1) π σ))))
          + permSignCoeff R π •
              ((-1 : R) ^ (Fin.last (n + 1)).val •
                chainGenerator R X n
                  (AlexanderWhitney.faceSimplex X n (Fin.last (n + 1))
                    (barycentricSubdivSimplex X (n + 1) π σ))) :=
    fun π => Fin.sum_univ_castSucc _
  rw [Finset.sum_congr rfl (fun π (_ : π ∈ Finset.univ) => hsplit π), Finset.sum_add_distrib,
    internal_faces_sum_eq_zero, zero_add, last_faces_sum_eq_subdiv_boundary]

end AffineBarycentricSubdivision
end SphereOddDegree
