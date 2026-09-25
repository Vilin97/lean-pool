/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SmallChains
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionDiameter
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.BarycentricSubdivisionIter
public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.SingularSimplexLebesgueNumber
public import Mathlib.Tactic
/-!
# Each singular simplex eventually becomes small after iterated subdivision

For a singular simplex `σ : Δⁿ → X` and an open cover `𝒰` of `X`, some iterated
barycentric subdivision `sdᴺ([σ])` of the generator chain is a linear
combination of `𝒰`-small singular simplices.

The argument combines:

* the **Lebesgue number** of `σ` against `𝒰`
  (`singularSimplex_hasLebesgueNumber_for_openCover`, the project);
* the **diameter shrinking** of iterated barycentric subdivision
  (`exists_iteratedSubdivision_affine_diameter_lt`, the project);
* the **generator expansion** of the subdivision chain map.

## Strategy

Every singular simplex appearing in `sdᴺ([σ])` has the form `σ ∘ a` where
`a : Δⁿ → Δⁿ` is an `N`-fold *affine* subdivision composite
(`affineCompMap`). Working through the genuine linear map underlying the affine
subdivision (`affineSubdivLinear`), we identify the vertices of this composite
with the project's `iterVertices`, so its range has diameter
`< ε` for `N` large. The Lebesgue number then forces `σ ∘ a` to be `𝒰`-small,
and the whole chain to lie in the small-chain submodule.

## Main results

* `support_iteratedSubdivision_generator_subset_affineSummands` — `sdᴺ([σ])` is a
  span of generators `[σ ∘ a]` over affine subdivision composites `a`.
* `exists_iteratedSubdivision_generator_support_small` — for some `N` every
  affine-summand simplex appearing in `sdᴺ([σ])` is `𝒰`-small.
* `exists_iteratedSubdivision_generator_mem_smallChains` — for some `N`,
  `sdᴺ([σ])` lies in `smallChainSubmodule`.
-/

@[expose] public section

open scoped BigOperators
open CategoryTheory AlgebraicTopology Finset
open SphereOddDegree.AffineBarycentricSubdivision
open SphereOddDegree.BarycentricSubdivisionDiameter

namespace SphereOddDegree
namespace AffineBarycentricSubdivision

/-! ## 1. The affine subdivision map as a genuine linear map -/

/-- The affine subdivision map associated to a permutation `π`, packaged as a
genuine `ℝ`-linear self-map of `Fin (n+1) → ℝ`. On the standard simplex it
restricts to `affineSubdivMap n π`. -/
noncomputable def affineSubdivLinear (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := fun j => ∑ k : Fin (n + 1), x k * (prefixBarycenter n π k).val j
  map_add' := by
    intro x y; funext j; simp only [Pi.add_apply]; rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; ring
  map_smul' := by
    intro c x; funext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring

@[simp] theorem affineSubdivLinear_apply (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    affineSubdivLinear n π x j = ∑ k : Fin (n + 1), x k * (prefixBarycenter n π k).val j := rfl

theorem affineSubdivLinear_coe (n : ℕ) (π : Equiv.Perm (Fin (n + 1))) (x : Delta n) :
    affineSubdivLinear n π x.val = (affineSubdivMap n π x).val := by
  aesop

theorem prefixBarycenter_val_eq_stepVertices (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    (prefixBarycenter n π k).val = stepVertices n (stdVerts n) π k := by
  unfold prefixBarycenter stepVertices;
  ext j; simp +decide only [FiniteSimplex.map, FiniteSimplex.barycenter, Fintype.card_fin,
    Nat.cast_add, Nat.cast_one, stdVerts, Pi.smul_apply, Finset.sum_apply, smul_eq_mul];
  unfold FunOnFinite.linearMap; simp +decide only
    [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Finsupp.lmapDomain_apply, Finsupp.linearEquivFunOnFinite_apply];
  simp +decide [ Finsupp.mapDomain, Finsupp.linearEquivFunOnFinite, Pi.single_apply ];
  simp +decide [ Finsupp.sum_fintype, prefixVertex ];
  rw [ ← Finset.sum_subset ( show Finset.image ( fun x : Fin ( k.val + 1 ) => ⟨ x, by
    linarith [ Fin.is_lt x, Fin.is_lt k ] ⟩ ) Finset.univ ⊆ Finset.Iic k from ?_ ) ];
  · rw [ Finset.sum_image ] <;> norm_num;
    · exact Finset.sum_congr rfl fun _ _ => by rw [ Finsupp.single_apply ]; aesop;
    · exact fun x y h => by simpa [ Fin.ext_iff ] using h;
  · simp +decide [ Fin.ext_iff ];
    exact fun x hx₁ hx₂ hx₃ => False.elim <| hx₂ ⟨ x, by
      linarith [ Fin.is_lt x, Fin.is_lt k, show ( x : ℕ ) ≤ k from hx₁ ] ⟩ rfl;
  · exact Finset.image_subset_iff.mpr fun x _ => Finset.mem_Iic.mpr ( Nat.le_trans (
      Nat.le_of_lt_succ ( Fin.is_lt x ) ) ( Nat.le_refl _ ) )

theorem affineSubdivLinear_stdVerts (n : ℕ) (π : Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    affineSubdivLinear n π (stdVerts n k) = stepVertices n (stdVerts n) π k := by
  ext j; simp +decide only [stdVerts, affineSubdivLinear_apply, Pi.single_apply, ite_mul, one_mul,
    zero_mul, sum_ite_eq', mem_univ, ↓reduceIte];
  exact congr_fun ( prefixBarycenter_val_eq_stepVertices n π k ) j

/-- Compose the barycentric subdivision linear maps selected by a permutation word. -/
noncomputable def affineCompLinear (n : ℕ) :
    (N : ℕ) → (Fin N → Equiv.Perm (Fin (n + 1))) →
      ((Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ))
  | 0, _ => LinearMap.id
  | (N + 1), ρs =>
      (affineCompLinear n N (fun i => ρs i.castSucc)).comp
        (affineSubdivLinear n (ρs (Fin.last N)))

@[simp] theorem affineCompLinear_zero (n : ℕ) (ρs : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    affineCompLinear n 0 ρs = LinearMap.id := rfl

theorem affineCompLinear_succ (n N : ℕ) (ρs : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) :
    affineCompLinear n (N + 1) ρs
      = (affineCompLinear n N (fun i => ρs i.castSucc)).comp
          (affineSubdivLinear n (ρs (Fin.last N))) := rfl

theorem affineCompLinear_stdVerts (n N : ℕ) (ρs : Fin N → Equiv.Perm (Fin (n + 1)))
    (k : Fin (n + 1)) :
    affineCompLinear n N ρs (stdVerts n k) = iterVertices n N ρs (stdVerts n) k := by
  revert k
  induction N with
  | zero => intro k; rfl
  | succ N ih =>
    intro k
    rw [affineCompLinear_succ, iterVertices_succ]
    change (affineCompLinear n N (fun i => ρs i.castSucc)) (affineSubdivLinear n (ρs (Fin.last
      N)) (stdVerts n k)) = _
    rw [affineSubdivLinear_stdVerts]
    dsimp [stepVertices]
    rw [map_smul, map_sum]
    simp_rw [ih]

/-- The continuous simplex self-map associated with an iterated subdivision word. -/
noncomputable def affineCompMap (n : ℕ) :
    (N : ℕ) → (Fin N → Equiv.Perm (Fin (n + 1))) → C(Delta n, Delta n)
  | 0, _ => ContinuousMap.id _
  | (N + 1), ρs =>
      (affineCompMap n N (fun i => ρs i.castSucc)).comp
        (affineSubdivContinuousMap n (ρs (Fin.last N)))

@[simp] theorem affineCompMap_zero (n : ℕ) (ρs : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    affineCompMap n 0 ρs = ContinuousMap.id _ := rfl

theorem affineCompMap_succ (n N : ℕ) (ρs : Fin (N + 1) → Equiv.Perm (Fin (n + 1))) :
    affineCompMap n (N + 1) ρs
      = (affineCompMap n N (fun i => ρs i.castSucc)).comp
          (affineSubdivContinuousMap n (ρs (Fin.last N))) := rfl

theorem affineCompMap_coe (n N : ℕ) (ρs : Fin N → Equiv.Perm (Fin (n + 1))) (x : Delta n) :
    (affineCompMap n N ρs x).val = affineCompLinear n N ρs x.val := by
  induction N generalizing x with
  | zero => simp_all +decide
  | succ N ih =>
    simp_all +decide only [Subtype.forall, affineCompMap_succ, ContinuousMap.comp_apply,
      affineSubdivContinuousMap_apply, affineCompLinear_succ, LinearMap.coe_comp,
      Function.comp_apply]
    rw [← affineSubdivLinear_coe]

theorem affineCompMap_snoc (n N : ℕ) (ρs : Fin N → Equiv.Perm (Fin (n + 1)))
    (π : Equiv.Perm (Fin (n + 1))) :
    affineCompMap n (N + 1) (Fin.snoc ρs π)
      = (affineCompMap n N ρs).comp (affineSubdivContinuousMap n π) := by
  simp [affineCompMap_succ]

theorem range_affineCompMap_val (n N : ℕ) (ρs : Fin N → Equiv.Perm (Fin (n + 1))) :
    (Subtype.val) '' (Set.range (affineCompMap n N ρs))
      = convexHull ℝ (Set.range (iterVertices n N ρs (stdVerts n))) := by
  have h_range : Set.range (fun x : Delta n => (affineCompMap n N ρs x).val) = (affineCompLinear
    n N ρs) '' (SphereOddDegree.finiteSimplex ℝ (Fin (n + 1))) := by
    ext; simp [affineCompMap_coe];
  convert h_range using 1;
  · exact Set.ext fun x => ⟨ by
      rintro ⟨ y, ⟨ z, rfl ⟩, rfl ⟩; exact ⟨ z, rfl ⟩, by
      rintro ⟨ z, rfl ⟩; exact ⟨ _, ⟨ z, rfl ⟩, rfl ⟩ ⟩;
  · rw [ show SphereOddDegree.finiteSimplex ℝ ( Fin ( n + 1 ) ) = convexHull ℝ ( Set.range (
      stdVerts n ) ) from by
          have := (SphereOddDegree.convexHull_range_single_eq_finiteSimplex ℝ (Fin (n + 1))).symm
          exact this ];
    rw [ LinearMap.image_convexHull ]
    congr! 1
    ext; simp [affineCompLinear_stdVerts]

theorem diam_range_affineCompMap (n N : ℕ) (ρs : Fin N → Equiv.Perm (Fin (n + 1))) :
    Metric.diam (Set.range (affineCompMap n N ρs))
      = Metric.diam (Set.range (iterVertices n N ρs (stdVerts n))) := by
  rw [ ← isometry_subtype_coe.diam_image ];
  rw [ range_affineCompMap_val, convexHull_diam ]

theorem exists_diam_range_affineCompMap_lt (n : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ N : ℕ, ∀ ρs : Fin N → Equiv.Perm (Fin (n + 1)),
      Metric.diam (Set.range (affineCompMap n N ρs)) < eps := by
  obtain ⟨N, hN⟩ := exists_iteratedSubdivision_affine_diameter_lt n eps heps
  exact ⟨N, fun ρs => by rw [diam_range_affineCompMap]; exact hN ρs⟩

variable {X : TopCat.{0}}

/-- A singular simplex precomposed with one iterated barycentric subdivision map. -/
noncomputable def affineSummandSimplex (n N : ℕ) (σ : singularSimplices X n)
    (ρs : Fin N → Equiv.Perm (Fin (n + 1))) : singularSimplices X n :=
  continuousMapAsSingularSimplex X n ((mvSimplexMap σ).comp (affineCompMap n N ρs))

@[simp] theorem mvSimplexMap_affineSummandSimplex (n N : ℕ) (σ : singularSimplices X n)
    (ρs : Fin N → Equiv.Perm (Fin (n + 1))) :
    mvSimplexMap (affineSummandSimplex n N σ ρs)
      = (mvSimplexMap σ).comp (affineCompMap n N ρs) := by
  exact singularSimplexAsContinuousMap_continuousMapAsSingularSimplex X n _

theorem affineSummandSimplex_zero (n : ℕ) (σ : singularSimplices X n)
    (ρs : Fin 0 → Equiv.Perm (Fin (n + 1))) :
    affineSummandSimplex n 0 σ ρs = σ := by
  exact singularSimplices_ext rfl

theorem barycentricSubdivSimplex_affineSummandSimplex (n N : ℕ)
    (σ : singularSimplices X n) (ρs : Fin N → Equiv.Perm (Fin (n + 1)))
    (π : Equiv.Perm (Fin (n + 1))) :
    barycentricSubdivSimplex X n π (affineSummandSimplex n N σ ρs)
      = affineSummandSimplex n (N + 1) σ (Fin.snoc ρs π) := by
  unfold barycentricSubdivSimplex affineSummandSimplex;
  unfold affineCompMap; aesop;

theorem barycentricSubdivisionIterLinearMap_succ' (R : Type) [CommRing R] (X : TopCat.{0})
    (N n : ℕ) (c : singularChainGroup R X n) :
    barycentricSubdivisionIterLinearMap R X (N + 1) n c
      = (barycentricSubdivisionLinearMap R X n).hom
          (barycentricSubdivisionIterLinearMap R X N n c) := by
  induction N generalizing c with
  | zero =>
    rw [barycentricSubdivisionIterLinearMap_succ, barycentricSubdivisionIterLinearMap_zero,
        barycentricSubdivisionIterLinearMap_zero]
  | succ N ih =>
    rw [barycentricSubdivisionIterLinearMap_succ, ih, ← barycentricSubdivisionIterLinearMap_succ]

theorem support_iteratedSubdivision_generator_subset_affineSummands
    (R : Type) [CommRing R] (n N : ℕ) (σ : singularSimplices X n) :
    barycentricSubdivisionIterLinearMap R X N n (chainGenerator R X n σ)
      ∈ Submodule.span R
          {c | ∃ ρs : Fin N → Equiv.Perm (Fin (n + 1)),
            chainGenerator R X n (affineSummandSimplex n N σ ρs) = c} := by
  induction N generalizing σ with
  | zero =>
    refine Submodule.subset_span ⟨fun _ => Equiv.refl _, ?_⟩
    rw [barycentricSubdivisionIterLinearMap_zero, affineSummandSimplex_zero]
  | succ N ih =>
    rw [barycentricSubdivisionIterLinearMap_succ']
    generalize h_elem : barycentricSubdivisionIterLinearMap R X N n (chainGenerator R X n σ) = w
    have hw : w ∈ Submodule.span R {c | ∃ ρs : Fin N → Equiv.Perm (Fin (n + 1)), chainGenerator
      R X n (affineSummandSimplex n N σ ρs) = c} := by
      rw [← h_elem]; exact ih σ
    clear h_elem
    induction hw using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨ρs, rfl⟩ := hc
      simp only [barycentricSubdivisionLinearMap_generator_sum,
        barycentricSubdivSimplex_affineSummandSimplex]
      exact Submodule.sum_mem _ fun π _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | zero =>
      rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem exists_iteratedSubdivision_generator_support_small
    (n : ℕ) (σ : singularSimplices X n) (𝒰 : OpenCoverData X) :
    ∃ N : ℕ, ∀ ρs : Fin N → Equiv.Perm (Fin (n + 1)),
      IsSmallSimplex 𝒰 (affineSummandSimplex n N σ ρs) := by
  obtain ⟨eps, heps_pos, heps⟩ :=
    singularSimplex_hasLebesgueNumber_for_openCover 𝒰 σ
  obtain ⟨N, hN⟩ := exists_diam_range_affineCompMap_lt n eps heps_pos
  refine ⟨N, fun ρs => ?_⟩
  have hdiam : Metric.diam (Set.range (affineCompMap n N ρs)) < eps := hN ρs
  obtain ⟨U, hU_mem, hU_sub⟩ := heps (Set.range (affineCompMap n N ρs)) hdiam
  refine ⟨U, hU_mem, ?_⟩
  rw [mvSimplexMap_affineSummandSimplex]
  rw [ContinuousMap.coe_comp, Set.range_comp]
  exact hU_sub

theorem exists_iteratedSubdivision_generator_mem_smallChains
    (R : Type) [CommRing R] (n : ℕ) (σ : singularSimplices X n)
    (𝒰 : OpenCoverData X) :
    ∃ N : ℕ, barycentricSubdivisionIterLinearMap R X N n (chainGenerator R X n σ)
      ∈ smallChainSubmodule R X 𝒰 n := by
  obtain ⟨N, hN⟩ := exists_iteratedSubdivision_generator_support_small n σ 𝒰
  refine ⟨N, ?_⟩
  have h_supp := support_iteratedSubdivision_generator_subset_affineSummands R n N σ
  apply Submodule.span_le.mpr _ h_supp
  rintro c ⟨ρs, rfl⟩
  exact chainGenerator_mem_smallChainSubmodule (hN ρs)

end AffineBarycentricSubdivision
end SphereOddDegree
