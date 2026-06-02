/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanPool.LeanModularForms.ForMathlib.CongruenceSubgrps
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Extensions to `Mathlib.NumberTheory.ModularForms.CongruenceSubgroups`

The `Subgroup.width` API and `Gamma_width` formerly hosted here also live in the
companion file `LeanPool.LeanModularForms.ForMathlib.CongruenceSubgrps`, which is the
canonical one inside this project.  This file kept its own copy of the same definitions
under the original "Copy" filename, but to avoid clashing redeclarations of
`Subgroup.width` etc. in the project-wide mk_all index, we now import the canonical
companion and add only the genuinely-local extras (`mem_conjGL'`,
`finiteIndex_conjGL'` — the generalisation of `Mathlib.CongruenceSubgroup.finiteIndex_conjGL`
to an arbitrary finite-index `Γ`).
-/

open ConjAct Matrix.SpecialLinearGroup Matrix ModularGroup CongruenceSubgroup

open scoped MatrixGroups Pointwise Real

namespace CongruenceSubgroup

lemma mem_conjGL' {Γ : Subgroup SL(2, ℤ)} {g : GL (Fin 2) ℝ} {x : SL(2, ℤ)} :
    x ∈ conjGL Γ g ↔ ∃ y ∈ Γ, g⁻¹ * y * g = x := by
  rw [mem_conjGL]
  refine exists_congr fun y ↦ and_congr_right fun hy ↦ ?_
  rw [eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]

open Subgroup in
/-- If `Γ` has finite index in `SL(2, ℤ)`, then so does `g⁻¹ Γ g ∩ SL(2, ℤ)` for any
`g ∈ GL(2, ℚ)`. (This generalises `Mathlib`'s `finiteIndex_conjGL`, which only covers
`Γ = ⊤`.) -/
lemma finiteIndex_conjGL' (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (g : GL (Fin 2) ℚ) :
    (conjGL Γ (g.map <| Rat.castHom ℝ)).FiniteIndex := by
  constructor
  let t := (toConjAct <| g.map <| Rat.castHom ℝ)⁻¹
  let G := Γ.map (mapGL ℝ)
  let A := MonoidHom.range (mapGL ℝ : SL(2, ℤ) →* _)
  suffices (t • G ⊓ A).relIndex A ≠ 0 by rwa [conjGL, index_comap, ← inf_relIndex_right]
  apply relIndex_ne_zero_trans (K := t • A ⊓ A)
  · apply relIndex_inter_ne_zero
    rw [relIndex_pointwise_smul, ← index_comap,
      comap_map_eq_self_of_injective mapGL_injective]
    exact FiniteIndex.index_ne_zero
  · obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g 1
    rw [Gamma_one_top, ← MonoidHom.range_eq_map] at hN'
    suffices Γ(N) ≤ (t • A ⊓ A).comap (mapGL ℝ) by
      haveI _ : NeZero N := ⟨hN⟩
      simpa only [index_comap] using (finiteIndex_of_le this).index_ne_zero
    intro k hk
    have ht : t⁻¹ = toConjAct (g.map (Rat.castHom ℝ)) := inv_inv _
    simpa [mem_pointwise_smul_iff_inv_smul_mem, A, ht] using
      hN' <| smul_mem_pointwise_smul _ _ _ ⟨k, hk, rfl⟩

end CongruenceSubgroup
