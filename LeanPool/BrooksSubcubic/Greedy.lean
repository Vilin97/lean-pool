/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Finset.Max

/-!
# Subcubic Brooks theorem: Greedy

Part of the proof that a finite subcubic K₄-free graph is three-colourable.
-/

public section

section

open SimpleGraph Finset

namespace BrooksSubcubic

variable {V : Type*} [Fintype V]

/-- Greedy colouring picking the LEAST unused colour, with control: a vertex whose set of
strictly-lower-ranked neighbours is empty receives colour `0`. -/
theorem greedy_coloring_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 0 < k) (rank : V → ℕ) (hrank : Function.Injective rank)
    (h : ∀ v, ((G.neighborFinset v).filter fun w => rank w < rank v).card < k) :
    ∃ c : V → Fin k, (∀ u v, G.Adj u v → c u ≠ c v) ∧
      (∀ v, ((G.neighborFinset v).filter fun w => rank w < rank v).card = 0 → c v = ⟨0, hk⟩) := by
  classical
  have hwf : WellFounded (fun v w : V => rank v < rank w) := by
    constructor
    intro a
    have key : ∀ n, ∀ a, rank a = n → Acc (fun v w : V => rank v < rank w) a := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih => intro a ha; subst ha; exact Acc.intro a fun b hb => ih (rank b) hb b rfl
    exact key (rank a) a rfl
  let f : (v : V) → ((w : V) → rank w < rank v → Fin k) → Fin k := fun v x =>
    let lower : Finset V := (G.neighborFinset v).filter fun w => rank w < rank v
    let used : Finset (Fin k) := lower.attach.image fun ⟨w, hw⟩ => x w (Finset.mem_filter.mp hw).2
    let free : Finset (Fin k) := Finset.univ \ used
    have hfree : free.Nonempty := by
      rw [Finset.sdiff_nonempty]
      intro hsub
      have hcard_le : (Finset.univ : Finset (Fin k)).card ≤ used.card := Finset.card_le_card hsub
      have h1 : used.card ≤ lower.card := (Finset.card_image_le).trans (by rw [Finset.card_attach])
      have h2 : lower.card < k := h v
      rw [Finset.card_univ, Fintype.card_fin] at hcard_le
      omega
    free.min' hfree
  let c : V → Fin k := hwf.fix f
  have hc_eq : ∀ v, c v = f v (fun w _ => c w) := fun v => WellFounded.fix_eq hwf f v
  have hnotused : ∀ v, c v ∉ ((G.neighborFinset v).filter fun w => rank w < rank v).attach.image
      (fun p => c p.1) := by
    intro v hmem
    rw [hc_eq v] at hmem
    have hmin := Finset.min'_mem
      (Finset.univ \ (((G.neighborFinset v).filter fun w => rank w < rank v).attach.image
        (fun p => c p.1)))
      (by
        rw [Finset.sdiff_nonempty]; intro hsub
        have hcard_le := Finset.card_le_card hsub
        have h1 : (((G.neighborFinset v).filter fun w => rank w < rank v).attach.image
            (fun p => c p.1)).card ≤ ((G.neighborFinset v).filter fun w => rank w < rank v).card :=
          (Finset.card_image_le).trans (by rw [Finset.card_attach])
        have h2 := h v
        rw [Finset.card_univ, Fintype.card_fin] at hcard_le
        omega)
    rw [Finset.mem_sdiff] at hmin
    exact hmin.2 hmem
  refine ⟨c, ?_, ?_⟩
  · -- properness
    intro u v huv
    rcases lt_trichotomy (rank u) (rank v) with hlt | heq | hgt
    · have hu_low : u ∈ (G.neighborFinset v).filter fun w => rank w < rank v := by
        rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]; exact ⟨huv.symm, hlt⟩
      intro hcuv
      apply hnotused v
      rw [Finset.mem_image]
      exact ⟨⟨u, hu_low⟩, Finset.mem_attach _ _, hcuv⟩
    · exact absurd (hrank heq) huv.ne
    · have hv_low : v ∈ (G.neighborFinset u).filter fun w => rank w < rank u := by
        rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]; exact ⟨huv, hgt⟩
      intro hcuv
      apply hnotused u
      rw [Finset.mem_image]
      exact ⟨⟨v, hv_low⟩, Finset.mem_attach _ _, hcuv.symm⟩
  · -- control: empty lower ⟹ colour 0
    intro v hv0
    have hempty : ((G.neighborFinset v).filter fun w => rank w < rank v) = ∅ :=
      Finset.card_eq_zero.mp hv0
    have himg : (((G.neighborFinset v).filter fun w => rank w < rank v).attach.image
        (fun p => c p.1)) = ∅ := by rw [hempty]; simp
    rw [hc_eq v]
    change (Finset.univ \ (((G.neighborFinset v).filter fun w => rank w < rank v).attach.image
        (fun p => c p.1))).min' _ = ⟨0, hk⟩
    have hmem0 : (⟨0, hk⟩ : Fin k) ∈ Finset.univ \ (((G.neighborFinset v).filter
        fun w => rank w < rank v).attach.image (fun p => c p.1)) :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by rw [himg]; simp⟩
    apply le_antisymm
    · exact Finset.min'_le _ _ hmem0
    · exact Fin.le_def.mpr (Nat.zero_le _)

end BrooksSubcubic
end
