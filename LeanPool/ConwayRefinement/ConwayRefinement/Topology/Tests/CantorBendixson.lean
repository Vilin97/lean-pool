/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonProduct
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixsonReconstruction
public import Mathlib.Topology.Instances.ENat
import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Semantic checks for transfinite Cantor–Bendixson derivatives

In the order topology on extended naturals, stage one of the whole space is exactly infinity,
and stage two is empty. This separates derived set from closure and from a falsely discrete
ambient topology. The same calculation exercises a genuine limit stage. A two-to-one projection
also exercises the closed-map theorem without substituting injectivity for finite fibers.
-/

public noncomputable section

open Set Filter Topology TopologicalSpace Order

namespace Tests.CantorBendixson

private theorem derivedSet_finite {X : Type*} [TopologicalSpace X] [T1Space X]
    {s : Set X} (hs : s.Finite) : derivedSet s = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hs.not_infinite (Set.Infinite.of_accPt (mem_derivedSet.mp hx))

private theorem enat_derivedSet_univ : derivedSet (univ : Set ℕ∞) = {⊤} := by
  ext x
  constructor
  · intro hx
    by_contra hx0
    have hxne : x ≠ ⊤ := hx0
    have h := accPt_iff_frequently.mp (mem_derivedSet.mp hx)
    simp [ENat.nhds_eq_pure hxne] at h
  · intro hx
    have hx' : x = ⊤ := hx
    subst x
    apply mem_derivedSet.mpr
    apply accPt_iff_nhds.mpr
    intro U hU
    have he : ∀ᶠ n : ℕ in atTop, (n : ℕ∞) ∈ U := ENat.tendsto_natCast_nhds_top hU
    obtain ⟨n, hn⟩ := he.exists
    exact ⟨(n : ℕ∞), ⟨hn, mem_univ _⟩, ENat.coe_ne_top n⟩

/-- The convergent-sequence limit survives stage one; isolated finite points do not. -/
theorem enat_stage_one :
    ((⊤ : Closeds ℕ∞).cantorBendixson (1 : Ordinal) : Set ℕ∞) = {⊤} := by
  rw [show (1 : Ordinal) = 0 + 1 by simp, Closeds.cantorBendixson_add_one,
    Closeds.cantorBendixson_zero, Closeds.coe_derived, Closeds.coe_top]
  exact enat_derivedSet_univ

/-- The surviving limit point is isolated in the first derivative and disappears at stage two. -/
theorem enat_stage_two : (⊤ : Closeds ℕ∞).cantorBendixson (2 : Ordinal) = ⊥ := by
  apply Closeds.ext
  rw [show (2 : Ordinal) = 1 + 1 from one_add_one_eq_two.symm, Closeds.cantorBendixson_add_one,
    Closeds.coe_derived, enat_stage_one, Closeds.coe_bot]
  exact derivedSet_finite (finite_singleton _)

/-- A genuine limit stage is computed by intersections, not by restarting the derivative. -/
theorem enat_stage_omega :
    (⊤ : Closeds ℕ∞).cantorBendixson Ordinal.omega0 = ⊥ := by
  apply le_antisymm _ bot_le
  have h := (⊤ : Closeds ℕ∞).cantorBendixson_antitone
    (show (2 : Ordinal) ≤ Ordinal.omega0 from (Ordinal.natCast_lt_omega0 2).le)
  simpa only [enat_stage_two] using h

/-- The same finite points, in their own discrete ambient space, have no accumulation point. -/
theorem nat_stage_one : (⊤ : Closeds ℕ).cantorBendixson (1 : Ordinal) = ⊥ := by
  apply Closeds.ext
  rw [show (1 : Ordinal) = 0 + 1 by simp, Closeds.cantorBendixson_add_one,
    Closeds.cantorBendixson_zero, Closeds.coe_derived, Closeds.coe_top, Closeds.coe_bot]
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  have h := accPt_iff_frequently.mp (mem_derivedSet.mp hn)
  simp at h

/-- A closed projection with two-point fibers lifts every derivative, for arbitrary ordinals. -/
theorem two_point_projection (o : Ordinal) :
    ((⊤ : Closeds ℕ∞).cantorBendixson o : Set ℕ∞) ⊆
      Prod.fst '' ((⊤ : Closeds (ℕ∞ × Fin 2)).cantorBendixson o : Set (ℕ∞ × Fin 2)) := by
  have hf : IsClosedMap (Prod.fst : ℕ∞ × Fin 2 → ℕ∞) := isClosedMap_fst_of_compactSpace
  have hfin (y : ℕ∞) : (Prod.fst ⁻¹' {y} : Set (ℕ∞ × Fin 2)).Finite := by
    have heq : (Prod.fst ⁻¹' {y} : Set (ℕ∞ × Fin 2)) = {y} ×ˢ univ := by
      ext x
      simp
    rw [heq]
    exact (finite_singleton _).prod (finite_univ)
  have himage : (⟨Prod.fst '' (univ : Set (ℕ∞ × Fin 2)), hf _ isClosed_univ⟩ :
      Closeds ℕ∞) = ⊤ := by
    apply Closeds.ext
    simp only [Closeds.coe_mk, Closeds.coe_top, image_univ]
    exact Set.range_eq_univ.mpr Prod.fst_surjective
  simpa only [Closeds.coe_top, himage] using hf.cantorBendixson_image_subset hfin ⊤ o

/-- The product of two convergent sequences has no point at stage three. This exercises the
natural-sum bound with two nonzero coordinate ranks. -/
theorem enat_product_stage_three :
    (⊤ : Closeds (ℕ∞ × ℕ∞)).cantorBendixson (3 : Ordinal) = ⊥ := by
  let r (n : ℕ∞) : NatOrdinal := if n = ⊤ then 1 else 0
  have hr (x : ℕ∞) (_hx : x ∈ (⊤ : Closeds ℕ∞)) :
      ∀ᶠ z in 𝓝 x, z ∈ (⊤ : Closeds ℕ∞) → z ≠ x → r z < r x := by
    by_cases hx : x = ⊤
    · subst x
      exact Filter.Eventually.of_forall fun z _ hz ↦ by simp [r, hz]
    · simp [ENat.nhds_eq_pure hx]
  have hbound := (⊤ : Closeds ℕ∞).cantorBendixson_prod_subset_of_locally_lt
    ⊤ r r hr hr (3 : Ordinal)
  have hprod : (⊤ : Closeds ℕ∞) ×ˢ (⊤ : Closeds ℕ∞) = ⊤ := by
    ext x
    simp
  rw [hprod] at hbound
  apply Closeds.ext
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  have h := hbound hp
  change (3 : Ordinal) ≤ (r p.1 + r p.2).val at h
  have hle (n : ℕ∞) : r n ≤ 1 := by simp [r]; split <;> simp
  have hsum : (r p.1 + r p.2).val ≤ 2 := by
    have hs : r p.1 + r p.2 ≤ (2 : NatOrdinal) := by
      calc
        _ ≤ 1 + 1 := add_le_add (hle p.1) (hle p.2)
        _ = 2 := one_add_one_eq_two
    exact NatOrdinal.val.monotone hs
  have hnot : ¬ (3 : Ordinal) ≤ 2 := by
    exact_mod_cast (show ¬ (3 : ℕ) ≤ 2 by decide)
  exact hnot (h.trans hsum)

/-- The product bound is nondegenerate: the pair of limit points survives stage two. -/
theorem enat_product_top_mem_stage_two :
    (⊤, ⊤) ∈ (⊤ : Closeds (ℕ∞ × ℕ∞)).cantorBendixson (2 : Ordinal) := by
  have htop : (⊤ : ℕ∞) ∈ derivedSet (univ : Set ℕ∞) := by rw [enat_derivedSet_univ]; simp
  have hrow (y : ℕ∞) : (⊤, y) ∈ derivedSet (univ : Set (ℕ∞ × ℕ∞)) := by
    have h := (Continuous.prodMk_left y).image_derivedSet
      (fun _ _ heq ↦ congrArg Prod.fst heq) ⟨⊤, htop, rfl⟩
    exact derivedSet_mono _ _ (subset_univ _) h
  have hcol : (⊤, ⊤) ∈ derivedSet (derivedSet (univ : Set (ℕ∞ × ℕ∞))) := by
    have h := ((continuous_const : Continuous fun _ : ℕ∞ ↦ (⊤ : ℕ∞)).prodMk
      continuous_id).image_derivedSet (fun _ _ heq ↦ congrArg Prod.snd heq) ⟨⊤, htop, rfl⟩
    exact derivedSet_mono _ _ (by rintro _ ⟨y, _, rfl⟩; exact hrow y) h
  rw [show (2 : Ordinal) = (0 + 1) + 1 by simp only [zero_add, one_add_one_eq_two],
    Closeds.cantorBendixson_add_one, Closeds.cantorBendixson_add_one,
    Closeds.cantorBendixson_zero]
  change (⊤, ⊤) ∈ ((⊤ : Closeds (ℕ∞ × ℕ∞)).derived.derived : Set (ℕ∞ × ℕ∞))
  simpa only [Closeds.coe_derived, Closeds.coe_top] using hcol

/-- The sequence limit has point rank exactly one, rather than its order index `omega`. -/
theorem enat_top_rank :
    (⊤ : Closeds ℕ∞).cantorBendixsonRank (Set.isPWO_of_wellQuasiOrderedLE _) ⊤ = 1 := by
  apply ((⊤ : Closeds ℕ∞).cantorBendixsonRank_eq_iff (Set.isPWO_of_wellQuasiOrderedLE _)
    (by trivial) 1).mpr
  constructor
  · rw [enat_stage_one]
    exact mem_singleton _
  · rw [one_add_one_eq_two, enat_stage_two]
    exact notMem_empty _

/-- Every finite point is isolated, so its point rank is zero. -/
theorem enat_nat_rank (n : ℕ) :
    (⊤ : Closeds ℕ∞).cantorBendixsonRank (Set.isPWO_of_wellQuasiOrderedLE _) n = 0 := by
  apply ((⊤ : Closeds ℕ∞).cantorBendixsonRank_eq_iff (Set.isPWO_of_wellQuasiOrderedLE _)
    (by trivial) 0).mpr
  constructor
  · simp
  · rw [zero_add, enat_stage_one]
    exact ENat.coe_ne_top n

/-- The isolated rank-zero points are dense even though the limit point has rank one. -/
theorem enat_rank_zero_dense :
    closure {x : ℕ∞ | (⊤ : Closeds ℕ∞).cantorBendixsonRank
      (Set.isPWO_of_wellQuasiOrderedLE _) x = 0} = univ := by
  have hm (x : ℕ∞) : x ∈ (⊤ : Closeds ℕ∞) := by trivial
  simpa only [hm, true_and, Closeds.cantorBendixson_zero, Closeds.coe_top] using
    (⊤ : Closeds ℕ∞).closure_rank_level_eq (Set.isPWO_of_wellQuasiOrderedLE _) 0

end Tests.CantorBendixson
