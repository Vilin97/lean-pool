/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement.StructuredCorrelation
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.NNRat.BigOperators

/-!
# The density-increment dichotomy

Tiling a structured insensitive intersection by subspaces and averaging over the tiles turns
structured correlation into a genuine density increment on a subspace.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- An ambient dimension supports all working dimensions needed by the density-increment
dichotomy. -/
def IncrementBoundSufficient (k d : ℕ) (δ : ℝ) (n : ℕ) : Prop :=
  ∀ (_ : 2 ≤ k), HasDensityHJ k → 1 ≤ d → 0 < δ → δ ≤ 1 →
    ∃ m, 1 ≤ m ∧
      insensitiveIntersectionDimension k δ ≤ m ∧
      manyLinesBound k m δ ≤ n ∧
      IsInsensitive.intersectionTilingBound k k d
        (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m

/-- Sufficient ambient dimensions for the density-increment dichotomy occur eventually. -/
lemma exists_eventually_incrementBoundSufficient (k d : ℕ) (δ : ℝ) :
    ∃ N, ∀ n ≥ N, IncrementBoundSufficient k d δ n := by
  let m := max (max 1 (insensitiveIntersectionDimension k δ))
    (IsInsensitive.intersectionTilingBound k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))))
  refine ⟨manyLinesBound k m δ, ?_⟩
  intro n hn _ _ _ _ _
  refine ⟨m, ?_, ?_, hn, ?_⟩ <;>
    dsimp only [m] <;> omega

/-- A sufficient ambient dimension for the density-increment dichotomy. -/
noncomputable def incrementBound (k d : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact Nat.find (exists_eventually_incrementBoundSufficient k d δ)

/-- Select one working dimension supporting both structured correlation and the final tiling
argument.

The bound simultaneously leaves enough ambient coordinates for the many-lines construction and
makes the resulting parameter cube large enough for the insensitive-intersection construction and
for tiling that intersection by `d`-subspaces. -/
lemma incrementBound_spec {k d : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) (hd : 1 ≤ d)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {n : ℕ} (hn : incrementBound k d δ ≤ n) :
    ∃ m, 1 ≤ m ∧
      insensitiveIntersectionDimension k δ ≤ m ∧
      manyLinesBound k m δ ≤ n ∧
      IsInsensitive.intersectionTilingBound k k d
        (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m := by
  classical
  unfold incrementBound at hn
  exact Nat.find_spec (exists_eventually_incrementBoundSufficient k d δ) n hn
    hk hDHJ hd hδ₀ hδ₁

/-- The insensitive-intersection tiling theorem supplies a nonempty finite family of disjoint
`d`-subspaces with small uncovered part. -/
lemma exists_finite_structured_tiling {k d m : ℕ}
    (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) (hd : 1 ≤ d) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_tiling : IsInsensitive.intersectionTilingBound k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m)
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hD : ∀ i, IsInsensitive i.castSucc (Fin.last k) (D i))
    (hDdense : Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ)) :
    ∃ 𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)),
      𝒱.Nonempty ∧
      (∀ W ∈ 𝒱, Subspace.IsContained W (IsInsensitive.intersection D)) ∧
      ((𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m))).PairwiseDisjoint fun W ↦
        (Subspace.range W : Set (Fin m → Fin (k + 1)))) ∧
      ((IsInsensitive.uncovered (η := Fin d)
        (IsInsensitive.intersection D) (𝒱 : Set _)).dens : ℝ) <
        Parameters.γ k δ ^ 2 / 2 := by
  classical
  let β := Parameters.γ k δ ^ 2 / (4 * (k : ℝ))
  have hγ₀ := Parameters.γ_pos hk hδ₀
  have hγ₁ : Parameters.γ k δ ≤ 1 := by
    linarith [Parameters.γ_le_three_mul_η k δ, Parameters.η_le_δ_div_six k δ]
  have hβ₀ : 0 < β := by positivity
  have hβ_simplify :
      2 * (k : ℝ) * β = Parameters.γ k δ ^ 2 / 2 := by
    dsimp only [β]
    field_simp
    ring
  have hDβ :
      2 * (k : ℝ) * β ≤ ((IsInsensitive.intersection D).dens : ℝ) := by
    rw [hβ_simplify]
    nlinarith
  obtain ⟨𝒱, h𝒱finite, hcontained, hpairwise, huncovered⟩ :=
    IsInsensitive.exists_disjoint_subspaces_iInter (k := k) k d m hDHJ (by omega) le_rfl hd
      β hβ₀ hm_tiling D (by
        simpa only [Fin.castLE_rfl, id_eq] using hD) hDβ
  have h𝒱nonempty : 𝒱.Nonempty := by
    by_contra h𝒱
    rw [Set.not_nonempty_iff_eq_empty.mp h𝒱] at huncovered
    have hempty :
        IsInsensitive.uncovered (η := Fin d)
          (IsInsensitive.intersection D) (∅ : Set _) =
            IsInsensitive.intersection D := by
      ext x
      simp [IsInsensitive.uncovered]
    rw [hempty, hβ_simplify] at huncovered
    nlinarith
  refine ⟨h𝒱finite.toFinset, h𝒱finite.toFinset_nonempty.mpr h𝒱nonempty, ?_, ?_, ?_⟩
  · intro W hW
    exact hcontained W (h𝒱finite.mem_toFinset.mp hW)
  · simpa only [h𝒱finite.coe_toFinset] using hpairwise
  · simpa only [h𝒱finite.coe_toFinset, hβ_simplify] using huncovered

/-- The structured correlation and the small uncovered part give an aggregate density gain over
the disjoint tile family. -/
lemma structured_tiling_density_sum {k d m n : ℕ}
    (hk : 2 ≤ k) {δ : ℝ} (hδ₀ : 0 < δ)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hDdense : Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ))
    (hcorrelation : (δ + Parameters.γ k δ) *
        ((IsInsensitive.intersection D).dens : ℝ) ≤
      ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ))
    (𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
    (hcontained : ∀ W ∈ 𝒱, Subspace.IsContained W (IsInsensitive.intersection D))
    (hpairwise :
      ((𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m))).PairwiseDisjoint fun W ↦
      (Subspace.range W : Set (Fin m → Fin (k + 1)))))
    (huncovered :
      ((IsInsensitive.uncovered (η := Fin d)
        (IsInsensitive.intersection D) (𝒱 : Set _)).dens : ℝ) <
        Parameters.γ k δ ^ 2 / 2) :
    (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) ≤
      ∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ) := by
  classical
  let C := IsInsensitive.intersection D
  let P := pullback V A
  let T := 𝒱.biUnion Subspace.range
  have hTsub : T ⊆ C := by
    intro x hx
    simp only [T, Finset.mem_biUnion] at hx
    obtain ⟨W, hW, hxW⟩ := hx
    obtain ⟨z, rfl⟩ := Subspace.mem_range.mp hxW
    exact hcontained W hW z
  have hpairwise_fin :
      Set.PairwiseDisjoint
        (𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
        Subspace.range := by
    intro W hW W' hW' hne
    apply Finset.disjoint_left.mpr
    intro x hxW hxW'
    exact Set.disjoint_left.mp (hpairwise hW hW' hne) hxW hxW'
  have hsumT :
      ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) = (T.dens : ℝ) := by
    exact_mod_cast (Finset.dens_biUnion hpairwise_fin).symm
  have hpairwise_inter :
      Set.PairwiseDisjoint
        (𝒱 : Set (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
        (fun W ↦ P ∩ Subspace.range W) := by
    intro W hW W' hW' hne
    exact (hpairwise_fin hW hW' hne).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hinterT :
      𝒱.biUnion (fun W ↦ P ∩ Subspace.range W) = P ∩ T := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_inter, T]
    aesop
  have hsumPT :
      ∑ W ∈ 𝒱, ((P ∩ Subspace.range W).dens : ℝ) = ((P ∩ T).dens : ℝ) := by
    rw [← hinterT]
    exact_mod_cast (Finset.dens_biUnion hpairwise_inter).symm
  have huncovered_eq : IsInsensitive.uncovered (η := Fin d) C (𝒱 : Set _) = C \ T := by
    ext x
    simp [IsInsensitive.uncovered, T]
  have hPT_eq : (P ∩ C) ∩ T = P ∩ T := by
    rw [Finset.inter_assoc, Finset.inter_eq_right.mpr hTsub]
  have hremainder_real :
      (((P ∩ C) \ T).dens : ℝ) ≤ ((C \ T).dens : ℝ) := by
    exact_mod_cast Finset.dens_le_dens
      (Finset.sdiff_subset_sdiff Finset.inter_subset_right (subset_refl T))
  have hdecomp :
      ((P ∩ T).dens : ℝ) + (((P ∩ C) \ T).dens : ℝ) =
        ((P ∩ C).dens : ℝ) := by
    norm_cast
    simpa only [hPT_eq] using Finset.dens_inter_add_dens_sdiff (P ∩ C) T
  have hTdens : (T.dens : ℝ) ≤ (C.dens : ℝ) := by exact_mod_cast Finset.dens_le_dens hTsub
  have hγ₀ := Parameters.γ_pos hk hδ₀
  have hcoefficient : 0 ≤ δ + Parameters.γ k δ / 2 := by linarith
  rw [hsumT, hsumPT]
  apply (mul_le_mul_of_nonneg_left hTdens hcoefficient).trans
  rw [huncovered_eq] at huncovered
  dsimp only [C, P] at hDdense hcorrelation huncovered hdecomp hremainder_real hTdens ⊢
  nlinarith

/-- Intersecting a family with a subspace range factors its ambient density into relative density
and range density. -/
lemma Subspace.dens_inter_range_eq_relativeDensity_mul_range
    {η α ι : Type*} [Fintype (η → α)] [Fintype (ι → α)]
    [DecidableEq (ι → α)]
    (W : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    ((A ∩ range W).dens : ℝ) =
      (relativeDensity W A : ℝ) * ((range W).dens : ℝ) := by
  classical
  let B := Finset.univ.filter fun x : η → α ↦ W x ∈ A
  have hAB : A ∩ range W = B.image W := by
    ext w
    simp only [B, range, Finset.mem_inter, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    grind
  rw [hAB]
  simp only [Finset.nnratCast_dens, relativeDensity, range, B]
  rw [Finset.card_image_iff.mpr (Subspace.injective W).injOn,
    Finset.card_image_iff.mpr (Subspace.injective W).injOn]
  by_cases h : Fintype.card (η → α) = 0
  · let : IsEmpty (η → α) := Fintype.card_eq_zero_iff.mp h
    have hB : (Finset.univ.filter fun x : η → α ↦ W x ∈ A) = ∅ :=
      Subsingleton.elim _ _
    rw [hB]
    simp
  · field_simp
    simp only [Finset.card_univ]

/-- Finite weighted averaging selects a tile whose pullback density realizes the aggregate
gain. -/
lemma exists_dense_tile_of_density_sum {k d m n : ℕ}
    {δ : ℝ} (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (𝒱 : Finset (Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin m)))
    (h𝒱 : 𝒱.Nonempty)
    (hsum : (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) ≤
      ∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ)) :
    ∃ W ∈ 𝒱,
      δ + Parameters.γ k δ / 2 ≤
        (Subspace.relativeDensity W (pullback V A) : ℝ) := by
  by_contra! h
  apply (not_lt_of_ge hsum)
  calc
    (∑ W ∈ 𝒱, ((pullback V A ∩ Subspace.range W).dens : ℝ)) <
        ∑ W ∈ 𝒱, (δ + Parameters.γ k δ / 2) *
          ((Subspace.range W).dens : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty h𝒱
      intro W hW
      rw [Subspace.dens_inter_range_eq_relativeDensity_mul_range]
      apply mul_lt_mul_of_pos_right (h W hW)
      exact_mod_cast Finset.dens_pos.mpr
        ⟨W (fun _ ↦ 0), Subspace.mem_range.mpr ⟨fun _ ↦ 0, rfl⟩⟩
    _ = (δ + Parameters.γ k δ / 2) *
        ∑ W ∈ 𝒱, ((Subspace.range W).dens : ℝ) := by
      rw [Finset.mul_sum]

/-- Relative density in a composite subspace is relative density in the inner subspace of the
outer pullback. -/
lemma Subspace.relativeDensity_compose {α η ζ ι : Type*}
    [Fintype (η → α)] [Fintype (ζ → α)] [DecidableEq (η → α)]
    [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (W : Combinatorics.Subspace ζ α η)
    (A : Finset (ι → α)) :
    (relativeDensity (compose V W) A : ℝ) =
      (relativeDensity W (pullback V A) : ℝ) := by
  simp only [relativeDensity, pullback, parameterPreimage, Finset.mem_filter, Finset.mem_univ,
    true_and,
    compose_apply]

/-- Tile a structured insensitive intersection and extract a dense tile.

Apply `IsInsensitive.exists_disjoint_subspaces_iInter` with error
`γ² / (4k)`.  Pairwise disjointness turns the densities on the tile ranges into finite sums, and
the uncovered-density estimate preserves half of the correlation gain.  Finite averaging then
selects one `d`-tile of relative `A`-density at least `δ + γ/2`; composing that tile with `V`
gives the required ambient subspace. -/
lemma exists_density_increment_subspace_of_structured_correlation {k d m n : ℕ}
    (hk : 2 ≤ k) (hDHJ : HasDensityHJ k) (hd : 1 ≤ d) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hm_tiling : IsInsensitive.intersectionTilingBound k k d
      (Parameters.γ k δ ^ 2 / (4 * (k : ℝ))) ≤ m)
    (A : Finset (Fin n → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n))
    (D : Fin k → Finset (Fin m → Fin (k + 1)))
    (hD : ∀ i, IsInsensitive i.castSucc (Fin.last k) (D i))
    (hDdense : Parameters.γ k δ ≤ ((IsInsensitive.intersection D).dens : ℝ))
    (hcorrelation : (δ + Parameters.γ k δ) *
        ((IsInsensitive.intersection D).dens : ℝ) ≤
      ((pullback V A ∩ IsInsensitive.intersection D).dens : ℝ)) :
    ∃ W : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
      δ + Parameters.γ k δ / 2 ≤ (Subspace.relativeDensity W A : ℝ) := by
  obtain ⟨𝒱, h𝒱, hcontained, hpairwise, huncovered⟩ :=
    exists_finite_structured_tiling hk hDHJ hd hδ₀ hδ₁ hm_tiling D hD hDdense
  obtain ⟨W, _, hW⟩ :=
    exists_dense_tile_of_density_sum A V 𝒱 h𝒱 <|
      structured_tiling_density_sum hk hδ₀ A V D hDdense hcorrelation 𝒱
        hcontained hpairwise huncovered
  refine ⟨Subspace.compose V W, ?_⟩
  rwa [Subspace.relativeDensity_compose]

/-- A dense word family either contains a line or has increased density on a prescribed-dimensional
subspace. -/
lemma density_increment {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (d : ℕ) (hd : 1 ≤ d) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : incrementBound k d δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ l : Combinatorics.Line (Fin (k + 1)) (Fin n), ∀ a, l a ∈ A) ∨
      ∃ V : Combinatorics.Subspace (Fin d) (Fin (k + 1)) (Fin n),
        δ + Parameters.γ k δ / 2 ≤ (Subspace.relativeDensity V A : ℝ) := by
  classical
  by_cases hfree : IsLineFree A
  · obtain ⟨m, hm, hm_large, hmn, hm_tiling⟩ :=
      incrementBound_spec hk hDHJ hd hδ₀ hδ₁ hn
    let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    let : Nonempty (Combinatorics.Line (Fin k) (Fin m)) :=
      ⟨Combinatorics.Line.diagonal (Fin k) (Fin m)⟩
    obtain ⟨V, D, hD, hDdense, hcorrelation⟩ :=
      exists_structured_correlation hk hDHJ m n hm δ hδ₀ hδ₁ hm_large hmn A hA hfree
    exact Or.inr <|
      exists_density_increment_subspace_of_structured_correlation hk hDHJ hd hδ₀ hδ₁ hm_tiling
        A V D hD hDdense hcorrelation
  · rw [IsLineFree] at hfree
    push Not at hfree
    left
    exact hfree

end DensityHalesJewett
