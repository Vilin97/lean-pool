/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SmallSimplices
import Mathlib.Tactic

/-!
# A Lebesgue number for a singular simplex against an open cover

Let `σ : Δⁿ → X` be a singular simplex (with `X` an *arbitrary* topological
space) and let `𝒰` be an open cover of `X`. Pulling `𝒰` back along `σ` gives an
open cover of the compact metric space `Δⁿ`, so the Lebesgue-number lemma yields
a uniform `ε > 0` such that every subset of the domain `Δⁿ` with diameter `< ε`
is mapped by `σ` into a single member of `𝒰`.

Only the domain `Δⁿ` needs to be metric and compact; `X` stays arbitrary.

## Main results

* `SphereOddDegree.ExistsCoverMemberContainingImage` — the predicate that the
 image `σ '' A` of a subset `A ⊆ Δⁿ` lies in one member of the cover.
* `SphereOddDegree.singularSimplex_hasLebesgueNumber_for_openCover` — the
 Lebesgue-number theorem: there is `ε > 0` such that `Metric.diam A < ε`
 implies `σ '' A` is contained in a cover member.

This is the compactness input that the project combines with the
diameter-shrinking theorem of the project: once a refined affine simplex has
domain diameter `< ε`, its image under `σ` lies in some `U ∈ 𝒰`.
-/

open CategoryTheory AlgebraicTopology
open SphereOddDegree.AffineBarycentricSubdivision
open scoped Topology

namespace SphereOddDegree

/-- A subset `A ⊆ Δⁿ` has its `σ`-image contained in a single member of the open
cover `𝒰`. -/
def ExistsCoverMemberContainingImage {X : TopCat.{0}} (𝒰 : OpenCoverData X) {n : ℕ}
    (σ : singularSimplices X n) (A : Set (Delta n)) : Prop :=
  ∃ U ∈ 𝒰.sets, (mvSimplexMap σ) '' A ⊆ U

/-
**Lebesgue number for a singular simplex and an open cover.**

For a singular `n`-simplex `σ` of an arbitrary topological space `X` and an open
cover `𝒰` of `X`, there is `ε > 0` such that every subset `A` of the domain
`Δⁿ` with `Metric.diam A < ε` is mapped by `σ` into one member of `𝒰`.
-/
theorem singularSimplex_hasLebesgueNumber_for_openCover
    {X : TopCat.{0}} (𝒰 : OpenCoverData X) {n : ℕ}
    (σ : singularSimplices X n) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ A : Set (Delta n), Metric.diam A < eps →
        ∃ U ∈ 𝒰.sets, (mvSimplexMap σ) '' A ⊆ U := by
  -- Apply the Lebesgue number lemma to the compact space `Delta n` and the open cover `𝒰`.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ x : Delta n, ∃ U ∈ 𝒰.sets, Metric.ball x δ ⊆ (mvSimplexMap σ) ⁻¹' U := by
    have h_lebesgue : ∀ {s : Set (Delta n)}, IsCompact s → (∀ U ∈ 𝒰.sets, IsOpen ((mvSimplexMap σ) ⁻¹' U)) → s ⊆ ⋃ U ∈ 𝒰.sets, (mvSimplexMap σ) ⁻¹' U → ∃ δ > 0, ∀ x ∈ s, ∃ U ∈ 𝒰.sets, Metric.ball x δ ⊆ (mvSimplexMap σ) ⁻¹' U := by
      intros s hs h_open h_cover;
      have := @lebesgue_number_lemma_of_metric;
      convert this hs ( fun i : { U : Set X // U ∈ 𝒰.sets } => h_open _ i.2 ) _;
      · exact ⟨ fun ⟨ U, hU₁, hU₂ ⟩ => ⟨ ⟨ U, hU₁ ⟩, hU₂ ⟩, fun ⟨ ⟨ U, hU₁ ⟩, hU₂ ⟩ => ⟨ U, hU₁, hU₂ ⟩ ⟩;
      · exact fun x hx => by rcases Set.mem_iUnion₂.mp ( h_cover hx ) with ⟨ U, hU, hxU ⟩ ; exact Set.mem_iUnion.mpr ⟨ ⟨ U, hU ⟩, hxU ⟩ ;
    convert h_lebesgue isCompact_univ _ _;
    · aesop;
    · exact fun U hU => IsOpen.preimage ( mvSimplexMap σ |>.continuous ) ( 𝒰.isOpen_mem U hU );
    · exact fun x _ => by rcases 𝒰.covers ( mvSimplexMap σ x ) with ⟨ U, hU₁, hU₂ ⟩ ; exact Set.mem_iUnion₂.mpr ⟨ U, hU₁, hU₂ ⟩ ;
  refine' ⟨ δ, hδ_pos, fun A hA => _ ⟩;
  by_cases hA_empty : A.Nonempty;
  · obtain ⟨ x, hx ⟩ := hA_empty;
    obtain ⟨ U, hU₁, hU₂ ⟩ := hδ x;
    refine' ⟨ U, hU₁, Set.image_subset_iff.mpr fun y hy => hU₂ <| Metric.mem_ball.mpr <| lt_of_le_of_lt ( Metric.dist_le_diam_of_mem ( show Bornology.IsBounded A from _ ) hy hx ) hA ⟩;
    exact isCompact_univ.isBounded.subset ( Set.subset_univ _ );
  · simp_all +decide [ Set.not_nonempty_iff_eq_empty.mp hA_empty ];
    exact Exists.elim ( hδ _ ( Classical.choose_spec ( show ∃ x : Fin ( n + 1 ) → ℝ, x ∈ Delta n from by
                                                        exact ⟨ fun _ => 1 / ( n + 1 ), fun _ => by positivity, by norm_num [ Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀, Nat.cast_add_one_ne_zero ] ⟩ ) ) ) fun U hU => ⟨ U, hU.1 ⟩

/-- Restatement of the Lebesgue-number theorem in terms of
`ExistsCoverMemberContainingImage`. -/
theorem singularSimplex_hasLebesgueNumber_for_openCover'
    {X : TopCat.{0}} (𝒰 : OpenCoverData X) {n : ℕ}
    (σ : singularSimplices X n) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ A : Set (Delta n), Metric.diam A < eps →
        ExistsCoverMemberContainingImage 𝒰 σ A := by
  simpa only [ExistsCoverMemberContainingImage] using
    singularSimplex_hasLebesgueNumber_for_openCover 𝒰 σ

end SphereOddDegree
