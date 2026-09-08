/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Two low-multiplicity colors from an increasing isosceles-base rule

See the project entry module for the exact coordinate restrictions and source roles.
This is an abstract counting theorem. Its geometric application requires a
proved ordering in which two equal spokes always have a larger base color.
-/

namespace LeanPool.RareDistanceFields.OrderedColors

noncomputable section

variable {V C : Type*} [Fintype V] [LinearOrder C]

open Classical in
/-- The simple graph of distinct pairs carrying a specified symmetric color. -/
def colorGraph (q : V → V → C) (hsym : ∀ a b, q a b = q b a) (r : C) : SimpleGraph V where
  Adj a b := a ≠ b ∧ q a b = r
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, (hsym b a).trans h.2⟩⟩

open Classical in
/-- The finite set of colors occurring between distinct labels. -/
def palette (q : V → V → C) : Finset C :=
  Finset.univ.offDiag.image (fun p : V × V => q p.1 p.2)

open Classical in
theorem mem_palette (q : V → V → C) (a b : V) (hab : a ≠ b) : q a b ∈ palette q := by
  exact Finset.mem_image.mpr ⟨(a, b), by simp [Finset.mem_offDiag, hab], rfl⟩

open Classical in
/-- Equal-colored spokes on three distinct labels force a strictly larger base color. -/
def IncreasingBases (q : V → V → C) : Prop :=
  ∀ a b c, a ≠ b → a ≠ c → b ≠ c → q a b = q a c → q a b < q b c

open Classical in
theorem palette_card_gt_one (q : V → V → C) (h : IncreasingBases q)
    (hn : 3 ≤ Fintype.card V) : 1 < (palette q).card := by
  have hn' : 2 < (Finset.univ : Finset V).card := by
    simp only [Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hn'
  by_cases he : q a b = q a c
  · exact Finset.one_lt_card.mpr ⟨q a b, mem_palette q a b hab, q b c,
      mem_palette q b c hbc, ne_of_lt (h a b c hab hac hbc he)⟩
  · exact Finset.one_lt_card.mpr ⟨q a b, mem_palette q a b hab, q a c,
      mem_palette q a c hac, he⟩

open Classical in
theorem degree_le_two (q : V → V → C) (hsym : ∀ a b, q a b = q b a)
    (h : IncreasingBases q) (r D : C)
    (hhigh : ∀ a b, a ≠ b → r < q a b → q a b = D) (p : V) :
    (colorGraph q hsym r).degree p ≤ 2 := by
  by_contra hn
  have hc : 2 < ((colorGraph q hsym r).neighborFinset p).card := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    omega
  obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc⟩ := Finset.two_lt_card.mp hc
  have hpa := (SimpleGraph.mem_neighborFinset _ _ _).mp ha
  have hpb := (SimpleGraph.mem_neighborFinset _ _ _).mp hb
  have hpc := (SimpleGraph.mem_neighborFinset _ _ _).mp hc
  have qab : q a b = D := hhigh a b hab (hpa.2 ▸ h p a b hpa.1 hpb.1 hab (hpa.2.trans hpb.2.symm))
  have qac : q a c = D := hhigh a c hac (hpa.2 ▸ h p a c hpa.1 hpc.1 hac (hpa.2.trans hpc.2.symm))
  have qbc : q b c = D := hhigh b c hbc (hpb.2 ▸ h p b c hpb.1 hpc.1 hbc (hpb.2.trans hpc.2.symm))
  have hlt := h a b c hab hac hbc (qab.trans qac.symm)
  rw [qab, qbc] at hlt
  exact lt_irrefl _ hlt

open Classical in
theorem multiplicity_le_card (q : V → V → C) (hsym : ∀ a b, q a b = q b a)
    (h : IncreasingBases q) (r D : C)
    (hhigh : ∀ a b, a ≠ b → r < q a b → q a b = D) :
    (colorGraph q hsym r).edgeFinset.card ≤ Fintype.card V := by
  have he : ∑ p, (colorGraph q hsym r).degree p ≤ ∑ _p : V, 2 := by
    apply Finset.sum_le_sum
    intro p hp
    exact degree_le_two q hsym h r D hhigh p
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges] at he
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at he
  omega

open Classical in
/-- Both selected colors occur; both counts are unordered edge multiplicities. -/
theorem two_rare_colors (q : V → V → C) (hsym : ∀ a b, q a b = q b a)
    (h : IncreasingBases q) (hn : 3 ≤ Fintype.card V) :
    ∃ r ∈ palette q, ∃ D ∈ palette q, r ≠ D ∧
      (colorGraph q hsym r).edgeFinset.card ≤ Fintype.card V ∧
      (colorGraph q hsym D).edgeFinset.card ≤ Fintype.card V := by
  have hc := palette_card_gt_one q h hn
  have hp : (palette q).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨D, hD, hmax⟩ := Finset.exists_max_image (palette q) id hp
  have he : ((palette q).erase D).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hD]
    omega
  obtain ⟨r, hr, hrmax⟩ := Finset.exists_max_image ((palette q).erase D) id he
  have hrD := (Finset.mem_erase.mp hr).1
  refine ⟨r, (Finset.mem_erase.mp hr).2, D, hD, hrD, ?_, ?_⟩
  · apply multiplicity_le_card q hsym h r D
    intro a b hab habr
    by_contra heq
    have habmem : q a b ∈ (palette q).erase D :=
      Finset.mem_erase.mpr ⟨heq, mem_palette q a b hab⟩
    exact (not_lt_of_ge (hrmax _ habmem)) habr
  · apply multiplicity_le_card q hsym h D D
    intro a b hab hlt
    exact False.elim ((not_lt_of_ge (hmax _ (mem_palette q a b hab))) hlt)

end
end LeanPool.RareDistanceFields.OrderedColors
