/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.OrderedTwoPointInduction
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Reindexing and sorting finite two-point systems
-/

open MeasureTheory Set
open scoped BigOperators

namespace Feige

noncomputable section

/-- Permutation which arranges `γ` in nonincreasing order. -/
noncomputable def descendingPerm {m : ℕ} (γ : Fin m → ℝ) :
    Equiv.Perm (Fin m) :=
  Tuple.sort (fun i => -γ i)

theorem antitone_comp_descendingPerm {m : ℕ} (γ : Fin m → ℝ) :
    Antitone (γ ∘ descendingPerm γ) := by
  have hmono := Tuple.monotone_sort (fun i : Fin m => -γ i)
  intro i j hij
  have h := hmono hij
  dsimp [descendingPerm] at h ⊢
  linarith

theorem dirichletK_comp_perm {m : ℕ}
    (y : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) :
    dirichletK (y ∘ σ) = dirichletK y := by
  let τ : Option (Fin m) ≃ Option (Fin m) := Equiv.optionCongr σ
  let T : (Option (Fin m) → NNReal) ≃ᵐ (Option (Fin m) → NNReal) :=
    MeasurableEquiv.piCongrLeft (fun _ : Option (Fin m) => NNReal) τ
  have hpres :
      MeasurePreserving T (expProductMeasure (Fin m))
        (expProductMeasure (Fin m)) := by
    simpa [T, τ, expProductMeasure] using
      (MeasureTheory.measurePreserving_piCongrLeft
        (fun _ : Option (Fin m) => nnexpMeasure) τ)
  have hevent : T ⁻¹' kEvent y = kEvent (y ∘ σ) := by
    ext e
    simp only [Set.mem_preimage, kEvent, Set.mem_ofPred_eq,
      Function.comp_apply]
    change
      (∑ i, (y i - 1) * ((T e) (some i) : ℝ)) ≤ ((T e) none : ℝ) ↔
      (∑ i, (y (σ i) - 1) * (e (some i) : ℝ)) ≤ (e none : ℝ)
    have hnone : T e none = e none := by
      have h := MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : Option (Fin m) => NNReal) τ e (τ.symm none)
      have hT : T e none = e (τ.symm none) := by
        simpa only [T, Equiv.apply_symm_apply] using h
      rw [hT]
      congr 1
    have hsome : ∀ i, T e (some i) = e (some (σ.symm i)) := by
      intro i
      have h := MeasurableEquiv.piCongrLeft_apply_apply
        (β := fun _ : Option (Fin m) => NNReal) τ e
        (τ.symm (some i))
      have hT : T e (some i) = e (τ.symm (some i)) := by
        simpa only [T, Equiv.apply_symm_apply] using h
      rw [hT]
      congr 2
    rw [hnone]
    simp_rw [hsome]
    rw [← Equiv.sum_comp σ]
    simp
  unfold dirichletK
  rw [← hevent]
  calc
    (expProductMeasure (Fin m)).real (T ⁻¹' kEvent y) =
        ((expProductMeasure (Fin m)).map T).real (kEvent y) :=
      (map_measureReal_apply T.measurable (measurableSet_kEvent y)).symm
    _ = (expProductMeasure (Fin m)).real (kEvent y) := by
      rw [hpres.map_eq]

theorem twoPointKFinset_comp_perm {m : ℕ}
    (γ β : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (S : Finset (Fin m)) :
    twoPointKFinset (γ ∘ σ) (β ∘ σ) S =
      twoPointKFinset γ β (S.map σ.toEmbedding) := by
  unfold twoPointKFinset twoPointK
  have hv :
      twoPointVector (γ ∘ σ) (β ∘ σ) (S : Set (Fin m)) =
        twoPointVector γ β (S.map σ.toEmbedding : Finset (Fin m)) ∘ σ := by
    funext i
    classical
    unfold twoPointVector
    simp [Function.comp_apply]
  rw [hv, dirichletK_comp_perm]

theorem highSetMass_comp_perm {m : ℕ}
    (p : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (S : Finset (Fin m)) :
    highSetMass (p ∘ σ) S =
      highSetMass p (S.map σ.toEmbedding) := by
  classical
  unfold highSetMass
  congr 1
  · rw [Finset.prod_map]
    rfl
  · have hcompl :
        Finset.univ \ S.map σ.toEmbedding =
          (Finset.univ \ S).map σ.toEmbedding := by
      ext i
      simp
    rw [hcompl, Finset.prod_map]
    rfl

theorem twoPointRejectionMass_comp_perm {m : ℕ}
    (γ β : Fin m → ℝ) (σ : Equiv.Perm (Fin m)) (α : ℝ) :
    twoPointRejectionMass (γ ∘ σ) (β ∘ σ) α =
      twoPointRejectionMass γ β α := by
  classical
  unfold twoPointRejectionMass
  simp only [Finset.sum_filter, Finset.powerset_univ]
  rw [← Equiv.sum_comp σ.symm.finsetCongr]
  apply Fintype.sum_congr
  intro S
  rw [Equiv.finsetCongr_apply,
    twoPointKFinset_comp_perm γ β σ (S.map σ.symm.toEmbedding)]
  have hp :
      twoPointHighProbability (γ ∘ σ) (β ∘ σ) =
        twoPointHighProbability γ β ∘ σ := by
    rfl
  rw [hp, highSetMass_comp_perm
    (twoPointHighProbability γ β) σ (S.map σ.symm.toEmbedding)]
  have hmap :
      (S.map σ.symm.toEmbedding).map σ.toEmbedding = S := by
    ext i
    simp
  rw [hmap]

/-- Arbitrary strict systems reduce to the ordered theorem by sorting the
`γ` coordinates and simultaneously transporting every product coordinate. -/
theorem strictTwoPoint_rejection_le_of_localInsertion
    (hlocal : StrictOrderedLocalInsertion)
    {m : ℕ} (γ β : Fin m → ℝ)
    (hγpos : ∀ i, 0 < γ i) (hγle : ∀ i, γ i ≤ 1)
    (hβpos : ∀ i, 0 < β i)
    {α : ℝ} (hα : 0 ≤ α) :
    twoPointRejectionMass γ β α ≤ α := by
  let σ := descendingPerm γ
  have hord : Antitone (γ ∘ σ) :=
    antitone_comp_descendingPerm γ
  have hordered :=
    orderedStrictTwoPoint_rejection_le_of_localInsertion hlocal
      (γ ∘ σ) (β ∘ σ)
      (fun i => hγpos (σ i))
      (fun i => hγle (σ i))
      (fun i => hβpos (σ i))
      hord hα
  rw [twoPointRejectionMass_comp_perm γ β σ α] at hordered
  exact hordered

end

end Feige
