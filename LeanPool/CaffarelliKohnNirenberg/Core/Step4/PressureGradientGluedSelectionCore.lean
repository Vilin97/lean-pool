/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative

/-!
# Selecting one representative from a countable family of local functions

A countable family of functions that agree almost everywhere on their pairwise
overlaps is represented by a single function, and that representative inherits
local integrability on the union of the pieces.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace CKN

/-- A countable family of functions that agree almost everywhere on their
pairwise overlaps admits a single function that agrees with every member almost
everywhere on that member's own piece. -/
theorem exists_ae_eq_of_countable_family {d : ℕ}
    {V : ℕ → Set (Vec d)} (hV : ∀ n, MeasurableSet (V n))
    {g : ℕ → Vec d → ℝ}
    (hagree : ∀ m n, g m =ᵐ[volume.restrict (V m ∩ V n)] g n) :
    ∃ G : Vec d → ℝ, ∀ n, G =ᵐ[volume.restrict (V n)] g n := by
  classical
  let G : Vec d → ℝ :=
    fun x => if h : ∃ n, x ∈ V n then g (Nat.find h) x else 0
  refine ⟨G, ?_⟩
  intro n
  rw [Filter.EventuallyEq, ae_iff]
  rw [Measure.restrict_apply' (hV n)]
  have hsub : {x | ¬ (G x = g n x)} ∩ V n ⊆
      ⋃ m, ({x | g m x ≠ g n x} ∩ (V m ∩ V n)) := by
    intro x hx
    obtain ⟨hxnot, hxn⟩ := hx
    simp only [Set.mem_ofPred_eq] at hxnot
    have h : ∃ k, x ∈ V k := ⟨n, hxn⟩
    refine Set.mem_iUnion.mpr ⟨Nat.find h, ?_⟩
    refine ⟨?_, Nat.find_spec h, hxn⟩
    intro heq
    apply hxnot
    have hGx : G x = g (Nat.find h) x := by
      simp only [G, dite_eq_left h]
    rw [hGx, heq]
  have hnull : volume (⋃ m, ({x | g m x ≠ g n x} ∩ (V m ∩ V n))) = 0 := by
    apply measure_iUnion_null
    intro m
    have h0 := hagree m n
    rw [Filter.EventuallyEq, ae_iff] at h0
    rw [Measure.restrict_apply' ((hV m).inter (hV n))] at h0
    exact h0
  exact measure_mono_null hsub hnull

/-- Local integrability passes from the members of an open countable cover to any
function that agrees with each member almost everywhere on its piece. -/
theorem locallyIntegrableOn_of_ae_eq_cover {d : ℕ}
    {U : Set (Vec d)} {V : ℕ → Set (Vec d)}
    (hV : ∀ n, IsOpen (V n)) (hcover : U ⊆ ⋃ n, V n)
    {G : Vec d → ℝ} {g : ℕ → Vec d → ℝ}
    (hg : ∀ n, LocallyIntegrableOn (g n) (V n) volume)
    (hGg : ∀ n, G =ᵐ[volume.restrict (V n)] g n) :
    LocallyIntegrableOn G U volume := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp (hcover hx)
  have hVn_nhds : V n ∈ 𝓝 x := (hV n).mem_nhds hxn
  have hnhds : 𝓝[V n] x = 𝓝 x := nhdsWithin_eq_nhds.mpr hVn_nhds
  obtain ⟨t, ht_mem, ht_int⟩ := hg n x hxn
  rw [hnhds] at ht_mem
  have hinter : t ∩ V n ∈ 𝓝 x := Filter.inter_mem ht_mem hVn_nhds
  have hint : IntegrableOn (g n) (t ∩ V n) volume :=
    ht_int.mono_set Set.inter_subset_left
  have hae : G =ᵐ[volume.restrict (t ∩ V n)] g n :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right (hGg n)
  exact ⟨t ∩ V n, nhdsWithin_le_nhds hinter, hint.congr hae.symm⟩

end CKN
