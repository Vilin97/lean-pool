/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback
-/

import LeanPool.OSforGFF.Minlos.NuclearSpace
import LeanPool.OSforGFF.Minlos.PietschBridge
import LeanPool.OSforGFF.Minlos.Main
import LeanPool.OSforGFF.GaussianField.SchwartzNuclear.HermiteNuclear
import LeanPool.OSforGFF.GaussianField.Nuclear.NuclearSpace

/-!
# Nuclear Space Infrastructure for Schwartz Space

This file proves that Schwartz space is Hilbert-nuclear and separable,
bridging between the gaussian-field library (Hermite-basis proofs) and
the bochner library (Minlos theorem).

## Proof chain

- **SeparableSpace**: directly from gaussian-field's Hermite analysis
- **IsHilbertNuclear**: gaussian-field's `DyninMityaginSpace` → `NuclearSpace`
  → bochner's `IsNuclear` → `isHilbertNuclear_of_nuclear`

## References

- Trèves, "Topological Vector Spaces", Ch. 50-51
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
-/

/-! ### WithSeminorms reindexing

A general reindexing lemma: if `p` generates the topology and `e` is an equivalence,
then `p ∘ e` also generates the topology.
-/

open TopologicalSpace

section Reindex

variable {𝕜 E ι ι' : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- Reindexing a seminorm family by an equivalence preserves `WithSeminorms`. -/
theorem WithSeminorms.equiv {p : SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) (e : ι' ≃ ι) :
    WithSeminorms (p ∘ e) := by
  rw [SeminormFamily.withSeminorms_iff_nhds_eq_iInf] at hp ⊢
  simp_rw [Function.comp_apply, hp]
  exact (Equiv.iInf_comp e).symm

end Reindex

/-! ### Bridge: gaussian-field NuclearSpace → bochner IsNuclear

gaussian-field's `NuclearSpace` (Pietsch characterization with `‖f n x‖`) is
equivalent to bochner's `IsNuclear` (same, with `|f n x|`), since for `ℝ`-valued
CLFs, `‖y‖ = |y|`.
-/

section Bridge

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
/-- Convert gaussian-field's `NuclearSpace` to bochner's `IsNuclear`. -/
theorem nuclearSpace_to_isNuclear [hN : GaussianField.NuclearSpace E] : IsNuclear E := by
  intro p hp
  obtain ⟨q, hq_cont, hq_ge, f, c, hc_nn, hc_sum, hf_bnd, hdom⟩ :=
    hN.nuclear_dominance p hp
  refine ⟨q, hq_cont, hq_ge, f, c, hc_nn, hc_sum, fun n x => ?_, fun x => ?_⟩
  · -- ‖f n x‖ ≤ q x  →  |f n x| ≤ q x  (since ‖·‖ = |·| for ℝ)
    rw [← Real.norm_eq_abs]; exact hf_bnd n x
  · -- p x ≤ ∑' n, ‖f n x‖ * c n  →  p x ≤ ∑' n, |f n x| * c n
    have := hdom x; simp_rw [Real.norm_eq_abs] at this; exact this

end Bridge

/-! ### Main instances for Schwartz space -/

/-- Schwartz space is Hilbert-nuclear, proved via:
1. gaussian-field: `DyninMityaginSpace (SchwartzMap D ℝ)` (Hermite basis)
2. gaussian-field: `DyninMityaginSpace → NuclearSpace` (Pietsch characterization)
3. bridge: `NuclearSpace → IsNuclear` (norm = abs for ℝ)
4. bochner: `isHilbertNuclear_of_nuclear` (Pietsch → Hilbert-Schmidt embeddings)
-/
noncomputable instance schwartzIsHilbertNuclear {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] :
    IsHilbertNuclear (SchwartzMap E ℝ) := by
  -- Step 1: Get NuclearSpace from DyninMityaginSpace (gaussian-field)
  letI := GaussianField.DyninMityaginSpace.toNuclearSpace (SchwartzMap E ℝ)
  -- Step 2: Convert to bochner's IsNuclear
  have hIN := nuclearSpace_to_isNuclear (E := SchwartzMap E ℝ)
  -- Step 3: Get ℕ-indexed seminorms via Cantor pairing
  let q₀ : ℕ → Seminorm ℝ (SchwartzMap E ℝ) := schwartzSeminormFamily ℝ E ℝ ∘ Nat.pairEquiv.symm
  have hq₀ : WithSeminorms q₀ :=
    (schwartz_withSeminorms ℝ E ℝ).equiv Nat.pairEquiv.symm
  have hq₀_cont : ∀ n, Continuous (q₀ n) := fun n =>
    (schwartz_withSeminorms ℝ E ℝ).continuous_seminorm (Nat.pairEquiv.symm n)
  -- Step 4: Apply bochner's bridge theorem
  exact isHilbertNuclear_of_nuclear hIN q₀ hq₀ hq₀_cont

/-- Schwartz space is separable, proved via Hermite analysis (gaussian-field). -/
noncomputable instance schwartzSeparableSpace {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] :
    SeparableSpace (SchwartzMap E ℝ) :=
  GaussianField.schwartzSeparableSpace
