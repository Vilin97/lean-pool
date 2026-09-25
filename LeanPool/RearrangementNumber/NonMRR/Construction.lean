/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vinicius de Oliveira Rodrigues
-/
module

/-
Copyright (c) 2026 Vinicius de Oliveira Rodrigues.
Released under Apache 2.0 license as described in the file LICENSE.
-/

public import LeanPool.RearrangementNumber.NonMRR.Selection
public import LeanPool.RearrangementNumber.NonMRR.Series
public import LeanPool.RearrangementNumber.NonMRR.Bounding
public import LeanPool.RearrangementNumber.NonMRR.Slaloms

/-!
# The challenge and response maps

This file proves the reduction from concrete finite block catalogues to slaloms.
The analytic hypotheses are precisely the conclusions of the finite construction;
they do not assume an inequality between cardinal characteristics.
-/

@[expose] public section

open Filter Finset Cardinal Set
open scoped Topology

namespace NonMRR

/-- The concrete finite block data needed by the construction, for every `g`. -/
structure BlockCatalogue (r : ℕ → ℕ) (b : ℕ → ℝ) where
  /-- The disjoint finite coordinate block at each stage. -/
  interval : (ℕ → ℕ) → ℕ → Finset ℕ
  /-- The balanced vectors supported on the stage blocks. -/
  vector : (ℕ → ℕ) → ℕ → ℕ → ℕ → ℝ
  disjoint : ∀ g, Pairwise (fun n m ↦ Disjoint (interval g n) (interval g m))
  support : ∀ g n k, k < g n → ∀ i, i ∉ interval g n → vector g n k i = 0
  balance : ∀ g n k, k < g n → ∑ i ∈ interval g n, vector g n k i = 0
  mass : ∀ g n k, k < g n → 1 ≤ ∑ i ∈ interval g n, ‖vector g n k i‖
  bad_card : ∀ g π n, (badValues (vector g) g π b n).card ≤ r n

namespace BlockCatalogue

variable {r : ℕ → ℕ} {b : ℕ → ℝ}

/-- The selected series, before testing its convergence. -/
noncomputable def candidate (C : BlockCatalogue r b) (e g : ℕ → ℕ) (i : ℕ) : ℝ :=
  ∑' n, selectedBlock (C.vector g) e g n i

/-- The exceptional-value slalom assigned to a growth function and a permutation. -/
noncomputable def response (C : BlockCatalogue r b) (p : (ℕ → ℕ) × Equiv.Perm ℕ) :
    Slalom r := ⟨badValues (C.vector p.1) p.1 p.2 b, C.bad_card p.1 p.2⟩

/-- A property used to select the genuine challenge or a fixed fallback challenge. -/
def CandidateGood (C : BlockCatalogue r b) (e g : ℕ → ℕ) : Prop :=
  Tendsto (partialSum (C.candidate e g)) atTop (𝓝 0) ∧
    ¬ Summable (fun i ↦ |C.candidate e g i|)

/-- The fallback ensures that the challenge map is defined even for bad choices of `g`. -/
noncomputable def challengeSeries (C : BlockCatalogue r b) (e g : ℕ → ℕ) :
    ConditionalSeries := by
  classical
  exact if h : C.CandidateGood e g then
    ⟨C.candidate e g, 0, hasSum_conditional_iff.mpr h.1, h.2⟩
  else Classical.choice conditionalSeries_nonempty

/-- Eventual avoidance gives the required common zero-sum witness. -/
theorem candidate_good_of_avoids (C : BlockCatalogue r b)
    (hb : Summable b) (hbnonneg : ∀ n, 0 ≤ b n)
    (e g : ℕ → ℕ) (π : Equiv.Perm ℕ)
    (hinfinite : FrequentlyLT e g)
    (havoid : ∀ᶠ n in atTop, e n ∉ (C.response (g, π)).val n) :
    C.CandidateGood e g ∧
      Tendsto (partialSum (C.candidate e g ∘ π)) atTop (𝓝 0) := by
  obtain ⟨hid, hπ, habs⟩ := selected_blocks_give_zero_witness
    (C.vector g) (C.interval g) e g π (C.disjoint g) (C.support g)
    (C.balance g) (C.mass g) b hb hbnonneg hinfinite havoid
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact hid
  · simpa only [candidate, Real.norm_eq_abs] using habs
  · exact hπ

/-- The central implication in the morphism: a rearrangement forces infinitely
many catches by its exceptional-value slalom. -/
theorem catches_of_rearranges (C : BlockCatalogue r b)
    (hb : Summable b) (hbnonneg : ∀ n, 0 ≤ b n)
    (e g : ℕ → ℕ) (π : Equiv.Perm ℕ)
    (hinfinite : FrequentlyLT e g) (hπ : Rearranges (C.challengeSeries e g) π) :
    ∃ᶠ n in atTop, e n ∈ (C.response (g, π)).val n := by
  classical
  by_contra h
  have havoid : ∀ᶠ n in atTop, e n ∉ (C.response (g, π)).val n := by
    simpa only [Filter.not_frequently] using h
  obtain ⟨hgood, hsum⟩ := C.candidate_good_of_avoids hb hbnonneg e g π hinfinite havoid
  apply hπ
  simpa only [challengeSeries, dite_eq_left hgood] using hasSum_conditional_iff.mpr hsum

/-- Images of an unbounded family and a rearranging family dominate the slalom relation. -/
theorem dominating_response_image (C : BlockCatalogue r b)
    (hr : ∀ n, 0 < r n) (hb : Summable b) (hbnonneg : ∀ n, 0 ≤ b n)
    {G : Set (ℕ → ℕ)} {P : Set (Equiv.Perm ℕ)}
    (hG : boundingRelation.Dominating G) (hP : IsRearranging P) :
    (slalomRelation r hr).Dominating (C.response '' (G ×ˢ P)) := by
  intro e
  obtain ⟨g, hg, heg⟩ := hG e
  obtain ⟨π, hπ, hbad⟩ := hP (C.challengeSeries e g)
  exact ⟨C.response (g, π), Set.mem_image_of_mem _ ⟨hg, hπ⟩,
    C.catches_of_rearranges hb hbnonneg e g π heg hbad⟩

/-- The cardinal bound before applying the classical inequality `b ≤ rr`. -/
theorem slalom_norm_le_bounding_mul_cardinal (C : BlockCatalogue r b)
    (hr : ∀ n, 0 < r n) (hb : Summable b) (hbnonneg : ∀ n, 0 ≤ b n)
    {P : Set (Equiv.Perm ℕ)} (hP : IsRearranging P) :
    (slalomRelation r hr).norm ≤ boundingNumber * #P := by
  obtain ⟨G, hG, hcard⟩ := boundingRelation.exists_dominating_of_norm
  calc
    (slalomRelation r hr).norm ≤ #(C.response '' (G ×ˢ P)) :=
      Relation.norm_le _ (C.dominating_response_image hr hb hbnonneg hG hP)
    _ ≤ #(G ×ˢ P) := Cardinal.mk_image_le
    _ = #G * #P := by
      simpa only [Cardinal.mk_prod, Cardinal.lift_id] using
        Cardinal.mk_congr (Equiv.Set.prod G P)
    _ = boundingNumber * #P := by rw [hcard]; rfl

end BlockCatalogue

end NonMRR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
