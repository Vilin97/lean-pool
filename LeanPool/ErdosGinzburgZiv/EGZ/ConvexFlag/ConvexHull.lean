/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.ConvexFlag.Basic

/-!
# Convex closure for flag convex hulls

The flag convex hull is defined through finite relational convex
combinations.  This file proves the expected structural API, including the
flattening of a convex combination of convex combinations.  Strictly
positive supports are used throughout, so the least-upper-bound base is
preserved by flattening.
-/

open scoped BigOperators

namespace EGZ.ConvexFlag

namespace ConvexCombination

/-- Reindex a convex combination along an equivalence of finite index types. -/
theorem reindex {F : ConvexFlag} {I J : Type*} [Fintype I] [Fintype J]
    {points : I → F.Point} {weight : I → ℝ} {result : F.Point}
    (c : ConvexCombination points weight result) (e : J ≃ I) :
    ConvexCombination (points ∘ e) (weight ∘ e) result := by
  classical
  have hbase : IsLeast
      {x : F.Node | ∀ j, 0 < (weight ∘ e) j → ((points ∘ e) j).base ≤ x}
      result.base := by
    constructor
    · intro j hj
      exact c.base_isLUB.1 (e j) hj
    · intro x hx
      apply c.base_isLUB.2
      intro i hi
      have hi' : 0 < (weight ∘ e) (e.symm i) := by
        simpa only [Function.comp_apply, e.apply_symm_apply] using hi
      simpa only [Function.comp_apply, e.apply_symm_apply] using
        hx (e.symm i) hi'
  refine ⟨fun j ↦ c.nonnegative (e j), ?_, hbase, ?_⟩
  · exact (by simpa only [Function.comp_apply] using
      (e.sum_comp weight).trans c.sum_eq_one)
  · let ea : {j : J // 0 < (weight ∘ e) j} ≃ {i : I // 0 < weight i} :=
      e.subtypeEquiv (fun _ ↦ Iff.rfl)
    have hsum := ea.sum_comp (fun i : {i : I // 0 < weight i} ↦
      weight i • (points i).coord (c.base_isLUB.1 i i.property))
    rw [c.val_eq]
    simpa only [Function.comp_apply, ea, Equiv.subtypeEquiv,
      Equiv.coe_fn_mk] using hsum.symm

/-- The one-point convex combination. -/
theorem singleton {F : ConvexFlag} (q : F.Point) :
    ConvexCombination (fun _ : Fin 1 ↦ q) (fun _ ↦ (1 : ℝ)) q := by
  classical
  refine ⟨fun _ ↦ zero_le_one, by simp, ?_, ?_⟩
  · constructor
    · intro _ _
      exact le_rfl
    · intro x hx
      exact hx 0 zero_lt_one
  · simp

end ConvexCombination

/-- Every point of a set belongs to its flag convex hull. -/
theorem subset_convexHull (F : ConvexFlag) (S : Set F.Point) :
    S ⊆ F.convexHull S := by
  intro q hq
  exact ⟨1, fun _ ↦ q, fun _ ↦ 1, fun _ ↦ hq,
    ConvexCombination.singleton q⟩

/-- Flag convex hull is monotone. -/
theorem convexHull_mono {F : ConvexFlag} {S T : Set F.Point} (hST : S ⊆ T) :
    F.convexHull S ⊆ F.convexHull T := by
  rintro q ⟨n, points, weight, hpoints, hcomb⟩
  exact ⟨n, points, weight, fun i ↦ hST (hpoints i), hcomb⟩

/-- A convex combination of points which are themselves convex combinations
can be flattened to one convex combination.  The flattened index contains
only pairs on which both coefficients are strictly positive; this makes its
base exactly the iterated least upper bound. -/
theorem convexHull_convex_closed (F : ConvexFlag) (S : Set F.Point) :
    F.convexHull (F.convexHull S) ⊆ F.convexHull S := by
  classical
  rintro result ⟨n, outerPoint, outerWeight, houterPoint, outerComb⟩
  choose innerSize innerPoint innerWeight hinnerPoint innerComb using houterPoint
  let OuterActive := {i : Fin n // 0 < outerWeight i}
  let InnerActive (i : OuterActive) :=
    {j : Fin (innerSize i.1) // 0 < innerWeight i.1 j}
  let Flat := Σ i : OuterActive, InnerActive i
  let flatPoint (k : Flat) : F.Point := innerPoint k.1.1 k.2.1
  let flatWeight (k : Flat) : ℝ :=
    outerWeight k.1.1 * innerWeight k.1.1 k.2.1

  have outerBase (i : OuterActive) : (outerPoint i.1).base ≤ result.base :=
    outerComb.base_isLUB.1 i.1 i.2
  have innerBase (k : Flat) :
      (innerPoint k.1.1 k.2.1).base ≤ (outerPoint k.1.1).base :=
    (innerComb k.1.1).base_isLUB.1 k.2.1 k.2.2
  have flatBase (k : Flat) : (flatPoint k).base ≤ result.base :=
    (innerBase k).trans (outerBase k.1)
  have flatWeight_pos (k : Flat) : 0 < flatWeight k :=
    mul_pos k.1.2 k.2.2

  have flatWeight_sum : (∑ k : Flat, flatWeight k) = 1 := by
    calc
      (∑ k : Flat, flatWeight k) =
          ∑ i : OuterActive, ∑ j : InnerActive i,
            outerWeight i.1 * innerWeight i.1 j.1 :=
        (by simpa only [Flat, flatWeight] using
          (Fintype.sum_sigma' (fun (i : OuterActive) (j : InnerActive i) ↦
            outerWeight i.1 * innerWeight i.1 j.1)))
      _ = ∑ i : OuterActive,
          outerWeight i.1 * (∑ j : InnerActive i, innerWeight i.1 j.1) := by
        apply Fintype.sum_congr
        intro i
        rw [Finset.mul_sum]
      _ = ∑ i : OuterActive, outerWeight i.1 := by
        apply Fintype.sum_congr
        intro i
        rw [(innerComb i.1).sum_active, mul_one]
      _ = 1 := outerComb.sum_active

  have flatBase_isLUB : IsLeast
      {x : F.Node | ∀ k, 0 < flatWeight k → (flatPoint k).base ≤ x}
      result.base := by
    constructor
    · intro k _
      exact flatBase k
    · intro x hx
      apply outerComb.base_isLUB.2
      intro i hi
      apply (innerComb i).base_isLUB.2
      intro j hj
      let k : Flat := ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      exact hx k (flatWeight_pos k)

  have flatVal : result.val =
      ∑ k : Flat, flatWeight k • (flatPoint k).coord (flatBase k) := by
    calc
      result.val = ∑ i : OuterActive,
          outerWeight i.1 • (outerPoint i.1).coord (outerBase i) := by
        simpa only [OuterActive, outerBase] using outerComb.val_eq
      _ = ∑ i : OuterActive, outerWeight i.1 •
          (∑ j : InnerActive i, innerWeight i.1 j.1 •
            (innerPoint i.1 j.1).coord
              ((innerBase ⟨i, j⟩).trans (outerBase i))) := by
        apply Fintype.sum_congr
        intro i
        congr 1
        simpa only [InnerActive, innerBase] using
          (innerComb i.1).coord_eq (outerBase i)
      _ = ∑ i : OuterActive, ∑ j : InnerActive i,
          (outerWeight i.1 * innerWeight i.1 j.1) •
            (innerPoint i.1 j.1).coord
              ((innerBase ⟨i, j⟩).trans (outerBase i)) := by
        apply Fintype.sum_congr
        intro i
        rw [Finset.smul_sum]
        apply Fintype.sum_congr
        intro j
        rw [mul_smul]
      _ = ∑ k : Flat,
          flatWeight k • (flatPoint k).coord (flatBase k) := by
        rw [Fintype.sum_sigma]

  have flatComb : ConvexCombination flatPoint flatWeight result := by
    refine ⟨fun k ↦ (flatWeight_pos k).le, flatWeight_sum,
      flatBase_isLUB, ?_⟩
    let allActive : {k : Flat // 0 < flatWeight k} ≃ Flat :=
      Equiv.subtypeUnivEquiv flatWeight_pos
    have hsum := allActive.sum_comp (fun k : Flat ↦
      flatWeight k • (flatPoint k).coord (flatBase k))
    exact flatVal.trans (by
      simpa only [allActive, Equiv.subtypeUnivEquiv,
        Equiv.coe_fn_mk] using hsum.symm)

  let toFlat : Fin (Fintype.card Flat) ≃ Flat :=
    (Fintype.equivFin Flat).symm
  refine ⟨Fintype.card Flat, flatPoint ∘ toFlat, flatWeight ∘ toFlat,
    ?_, flatComb.reindex toFlat⟩
  intro i
  exact hinnerPoint (toFlat i).1.1 (toFlat i).2.1

/-- Flag convex hull is idempotent. -/
theorem convexHull_idempotent (F : ConvexFlag) (S : Set F.Point) :
    F.convexHull (F.convexHull S) = F.convexHull S := by
  apply Set.Subset.antisymm
  · exact convexHull_convex_closed F S
  · exact convexHull_mono (subset_convexHull F S)

end EGZ.ConvexFlag
