/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.Geometry
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Definitions

/-!
# The `G`-factorization of the fixed-phase observable

For the Efron–Stein step of Proposition 4.3 (`p.fixed.phase.variance`) the fixed
phase observable

`F_σ(a) = P · 𝐀(U; a_σ) P`,  `U := cubeSet (originCube d m)`,  `a_σ := corridorField ℓ σ a`

must be exhibited as a *measurable function of the independent core restrictions*
`Y_k := a|_{coreBox ℓ σ k}` for the finitely many cores `k` meeting `U`.  This file
builds the reconstruction map `corePatch` from a tuple of per-core fields, and
proves the exact factorization

`F_σ (corePatch K (fun k => a|_{coreBox k})) = F_σ a`.

The reconstruction has a clean closed form on the diagonal input: for
`R a k := restrictCoeffField (coreBox ℓ σ k) a`,

`corePatch K (fun k => R a k) = extendByIdCoeffField (⋃ k ∈ K, coreBox ℓ σ k) a`,

an ambient-measurable *self*-map (`measurable_extendByIdCoeffField`).  The coarse
matrix only sees `U`, and on `U` the corridor of this glued field agrees with the
corridor of `a` (corridors are `1`; the residual `U ∖ corridor` is covered by the
cores in `K`), so the two coarse matrices coincide.

The cores are pairwise disjoint (`disjoint_coreBox`, from the `2`-separation
`areUnitSeparated_coreBox`), which makes the indicator-sum reconstruction
well-defined.
-/

open Homogenization
open scoped BigOperators

namespace Homogenization

variable {d : ℕ}

/-! ## Pairwise disjointness of the cores -/

/-- Distinct cores are disjoint: they are `2`-separated (`areUnitSeparated_coreBox`),
so a common point would have self-distance `≥ 1 > 0`. -/
theorem disjoint_coreBox {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (σ : Vec d) {k k' : Fin d → ℤ}
    (hne : k ≠ k') : Disjoint (coreBox ℓ σ k) (coreBox ℓ σ k') := by
  rw [Set.disjoint_left]
  intro x hxk hxk'
  have h := areUnitSeparated_coreBox hℓ σ hne hxk hxk'
  simp only [dist_self] at h
  linarith

/-- A point of a core is in no other core. -/
theorem not_mem_coreBox_of_mem {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (σ : Vec d) {k k' : Fin d → ℤ}
    (hne : k' ≠ k) {x : Vec d} (hx : x ∈ coreBox ℓ σ k) : x ∉ coreBox ℓ σ k' :=
  fun hx' => (Set.disjoint_left.1 (disjoint_coreBox hℓ σ hne)) hx' hx

/-! ## The finite index set of cores meeting `U` -/

/-- The finite set of core indices whose core meets the bounded region `U`. -/
noncomputable def coreMeetsFinset {ℓ : ℝ} (hℓ : 0 < ℓ) (σ : Vec d) {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) : Finset (Fin d → ℤ) :=
  (finite_coreBox_meets hℓ σ hU).toFinset

@[simp] theorem mem_coreMeetsFinset {ℓ : ℝ} (hℓ : 0 < ℓ) (σ : Vec d) {U : Set (Vec d)}
    (hU : Bornology.IsBounded U) (k : Fin d → ℤ) :
    k ∈ coreMeetsFinset hℓ σ hU ↔ (coreBox ℓ σ k ∩ U).Nonempty := by
  simp [coreMeetsFinset, Set.Finite.mem_toFinset]

/-! ## The core-restriction reconstruction map -/

/-- Reconstruct an ambient coefficient field from a tuple of per-core fields
`y : ↥K → CoeffField d`.  On the (disjoint) core `coreBox ℓ σ k` it reads `y k`;
off every core it is the identity.  The indicator-sum form is well-defined because
the cores are pairwise disjoint (at most one summand is nonzero). -/
noncomputable def corePatch (ℓ : ℝ) (σ : Vec d) (K : Finset (Fin d → ℤ))
    (y : {k // k ∈ K} → CoeffField d) : CoeffField d :=
  fun x => (1 : Mat d) +
    ∑ k : {k // k ∈ K}, (coreBox ℓ σ k.val).indicator (fun z => y k z - 1) x

/-- On the core `coreBox ℓ σ k₀` (with `k₀ ∈ K`) the reconstruction reads `y ⟨k₀⟩`. -/
theorem corePatch_apply_of_mem {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (σ : Vec d)
    {K : Finset (Fin d → ℤ)} (y : {k // k ∈ K} → CoeffField d)
    {k₀ : Fin d → ℤ} (hk₀ : k₀ ∈ K) {x : Vec d} (hx : x ∈ coreBox ℓ σ k₀) :
    corePatch ℓ σ K y x = y ⟨k₀, hk₀⟩ x := by
  classical
  have hsum : (∑ k : {k // k ∈ K},
      (coreBox ℓ σ k.val).indicator (fun z => y k z - 1) x)
      = y ⟨k₀, hk₀⟩ x - 1 := by
    rw [Finset.sum_eq_single (⟨k₀, hk₀⟩ : {k // k ∈ K})]
    · rw [Set.indicator_of_mem hx]
    · intro k' _ hk'ne
      have hval : k'.val ≠ k₀ := by
        intro h; exact hk'ne (Subtype.ext h)
      exact Set.indicator_of_notMem (not_mem_coreBox_of_mem hℓ σ hval hx) _
    · intro hnot; exact absurd (Finset.mem_univ _) hnot
  rw [corePatch, hsum]; abel

/-- Off every core in `K`, the reconstruction is the identity. -/
theorem corePatch_apply_of_not_mem {ℓ : ℝ} (σ : Vec d)
    {K : Finset (Fin d → ℤ)} (y : {k // k ∈ K} → CoeffField d)
    {x : Vec d} (hx : ∀ k ∈ K, x ∉ coreBox ℓ σ k) :
    corePatch ℓ σ K y x = 1 := by
  classical
  have hsum : (∑ k : {k // k ∈ K},
      (coreBox ℓ σ k.val).indicator (fun z => y k z - 1) x) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    exact Set.indicator_of_notMem (hx k.val k.property) _
  rw [corePatch, hsum, add_zero]

/-! ## The closed form of the reconstruction on core restrictions -/

/-- The union of the cores in `K`. -/
def coreUnion (ℓ : ℝ) (σ : Vec d) (K : Finset (Fin d → ℤ)) : Set (Vec d) :=
  ⋃ k ∈ K, coreBox ℓ σ k

theorem mem_coreUnion {ℓ : ℝ} {σ : Vec d} {K : Finset (Fin d → ℤ)} {x : Vec d} :
    x ∈ coreUnion ℓ σ K ↔ ∃ k ∈ K, x ∈ coreBox ℓ σ k := by
  simp [coreUnion]

/-- **Closed form.**  Feeding the core-restrictions of a single field `a` to the
reconstruction yields the identity-extension of `a` off the union of the cores.
This is the key identity: the reconstruction of a *diagonal* tuple is a genuine
ambient-measurable self-map (`extendByIdCoeffField`). -/
theorem corePatch_restrict_eq_extendById {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (σ : Vec d)
    (K : Finset (Fin d → ℤ)) (a : CoeffField d) :
    corePatch ℓ σ K (fun k => restrictCoeffField (coreBox ℓ σ k.val) a)
      = extendByIdCoeffField (coreUnion ℓ σ K) a := by
  classical
  funext x
  by_cases hx : x ∈ coreUnion ℓ σ K
  · rw [mem_coreUnion] at hx
    obtain ⟨k₀, hk₀, hxk₀⟩ := hx
    rw [corePatch_apply_of_mem hℓ σ _ hk₀ hxk₀,
      restrictCoeffField_apply_of_mem hxk₀,
      extendByIdCoeffField_apply_of_mem (by rw [mem_coreUnion]; exact ⟨k₀, hk₀, hxk₀⟩)]
  · have hxnot : ∀ k ∈ K, x ∉ coreBox ℓ σ k := by
      intro k hk hxk; exact hx (by rw [mem_coreUnion]; exact ⟨k, hk, hxk⟩)
    rw [corePatch_apply_of_not_mem σ _ hxnot,
      extendByIdCoeffField_apply_of_not_mem hx]

/-! ## The `extendByIdCoeffField` self-map is measurable -/

/-- The identity-extension self-map is ambient-measurable, by the same
pointwise/local case-split as `measurable_corridorField`: each entry is a
`by_cases x ∈ W` between a coordinate evaluation and the constant `1`, and the
map is spatially local. -/
theorem measurable_extendByIdCoeffField (W : Set (Vec d)) :
    Measurable (extendByIdCoeffField (d := d) W) := by
  classical
  refine measurable_coeffField_to_ambient ?_ (fun U hU => ?_)
  · refine measurable_pi_iff.2 fun x => measurable_pi_iff.2 fun i =>
      measurable_pi_iff.2 fun j => ?_
    by_cases hx : x ∈ W
    · simp only [extendByIdCoeffField_apply_of_mem hx]
      exact measurable_coeffField_entry (d := d) x i j
    · simp only [extendByIdCoeffField_apply_of_not_mem hx]
      exact measurable_const
  · refine measurable_localSigma_of_local (T := extendByIdCoeffField W) ?_ U hU
    intro V hV
    refine ⟨V, hV, ?_⟩
    intro a b hab x hxV
    by_cases hx : x ∈ W
    · rw [extendByIdCoeffField_apply_of_mem hx, extendByIdCoeffField_apply_of_mem hx, hab x hxV]
    · rw [extendByIdCoeffField_apply_of_not_mem hx, extendByIdCoeffField_apply_of_not_mem hx]

/-! ## The coarse matrix sees only `U` -/

/-- If two fields agree pointwise on the measurable set `U`, their coarse block
matrices on `U` coincide (both equal the coarse matrix of the common
`U`-restriction). -/
theorem coarseBlockMatrix_eq_of_eqOn {U : Set (Vec d)} (hU : MeasurableSet U)
    {a b : CoeffField d} (hab : Set.EqOn a b U) :
    coarseBlockMatrix U a = coarseBlockMatrix U b := by
  have hr : restrictCoeffField U a = restrictCoeffField U b := by
    funext x
    by_cases hx : x ∈ U
    · rw [restrictCoeffField_apply_of_mem hx, restrictCoeffField_apply_of_mem hx, hab hx]
    · rw [restrictCoeffField_apply_of_not_mem hx, restrictCoeffField_apply_of_not_mem hx]
  calc coarseBlockMatrix U a
      = coarseBlockMatrix U (restrictCoeffField U a) :=
        (coarseBlockMatrix_restrictCoeffField_eq hU a).symm
    _ = coarseBlockMatrix U (restrictCoeffField U b) := by rw [hr]
    _ = coarseBlockMatrix U b := coarseBlockMatrix_restrictCoeffField_eq hU b

/-! ## The exact factorization (Part 1c) -/

/-- On `U`, the corridor of the identity-extension `extendByIdCoeffField W a`
(with `W ⊇ U ∖ corridorSet`) agrees pointwise with the corridor of `a`: on the
corridor both are `1`; off the corridor inside `U` the point lies in some core
of `K`, so the extension reads `a`. -/
theorem corridorField_extendById_eqOn {ℓ : ℝ} (hℓ : 0 < ℓ) (σ : Vec d)
    {K : Finset (Fin d → ℤ)} {U : Set (Vec d)}
    (hK : ∀ k : Fin d → ℤ, (coreBox ℓ σ k ∩ U).Nonempty → k ∈ K)
    (a : CoeffField d) :
    Set.EqOn (corridorField ℓ σ (extendByIdCoeffField (coreUnion ℓ σ K) a))
      (corridorField ℓ σ a) U := by
  intro x hxU
  by_cases hxS : x ∈ corridorSet ℓ σ
  · rw [corridorField_apply_of_mem hxS, corridorField_apply_of_mem hxS]
  · rw [corridorField_apply_of_not_mem hxS, corridorField_apply_of_not_mem hxS]
    -- `x ∈ U ∖ corridorSet`, so `x` lies in some core, whose index meets `U`.
    have hxCompl : x ∈ (corridorSet ℓ σ)ᶜ := hxS
    rw [compl_corridorSet_eq_iUnion_coreBox hℓ σ, Set.mem_iUnion] at hxCompl
    obtain ⟨k₁, hxk₁⟩ := hxCompl
    have hk₁K : k₁ ∈ K := hK k₁ ⟨x, hxk₁, hxU⟩
    exact extendByIdCoeffField_apply_of_mem (by rw [mem_coreUnion]; exact ⟨k₁, hk₁K, hxk₁⟩)

/-- **Part 1c (exact `G`-factorization).**  With `U := cubeSet (originCube d m)`
and `K` the core indices meeting `U`, reconstructing the fixed-phase observable
from the per-core restrictions of `a` reproduces `F_σ(a)` exactly. -/
theorem phaseObservable_corePatch_restrict_eq [NeZero d] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {m : ℤ} {σ : Vec d} (P : BlockVec d) {K : Finset (Fin d → ℤ)}
    (hK : ∀ k : Fin d → ℤ,
      (coreBox ℓ σ k ∩ cubeSet (originCube d m)).Nonempty → k ∈ K)
    (a : CoeffField d) :
    blockVecDot P
        (blockMatVecMul
          (coarseBlockMatrix (cubeSet (originCube d m))
            (corridorField ℓ σ
              (corePatch ℓ σ K
                (fun k => restrictCoeffField (coreBox ℓ σ k.val) a)))) P)
      = blockVecDot P
          (blockMatVecMul
            (coarseBlockMatrix (cubeSet (originCube d m)) (corridorField ℓ σ a)) P) := by
  have hU : MeasurableSet (cubeSet (originCube d m)) := measurableSet_cubeSet (originCube d m)
  rw [corePatch_restrict_eq_extendById hℓ.le σ K a]
  rw [coarseBlockMatrix_eq_of_eqOn hU (corridorField_extendById_eqOn hℓ σ hK a)]

end Homogenization
