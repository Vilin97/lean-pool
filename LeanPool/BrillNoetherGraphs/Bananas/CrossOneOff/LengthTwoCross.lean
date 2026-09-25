/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.Semibreak

/-!
  Components of the length-two cross-exception argument.

  `Bananas.Semibreak` supplies the Dhar support lemma; this file records the
  midpoint, rank-difference, and dual-degree steps.
-/

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-! Dependent updates of the one-chip-per-strand representation. -/

def replaceSemibreakChip {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (β : Fin (g + 1)) (newChip : Option (Fin (B.length β - 1)))
    (γ : Fin (g + 1)) : Option (Fin (B.length γ - 1)) :=
  if h : γ = β then h ▸ newChip else chips γ

@[simp] theorem replaceSemibreakChip_same {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (β : Fin (g + 1)) (newChip : Option (Fin (B.length β - 1))) :
    replaceSemibreakChip B chips β newChip β = newChip := by
  simp [replaceSemibreakChip]

theorem replaceSemibreakChip_other {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (β γ : Fin (g + 1)) (newChip : Option (Fin (B.length β - 1)))
    (hγ : γ ≠ β) :
    replaceSemibreakChip B chips β newChip γ = chips γ := by
  simp [replaceSemibreakChip, hγ]

theorem semibreakDivisor_replace_chip {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (β : Fin (g + 1)) (oldChip newChip : Fin (B.length β - 1)) :
    semibreakDivisor B (replaceSemibreakChip B chips β (some newChip)) =
      semibreakDivisor B (replaceSemibreakChip B chips β (some oldChip)) +
        oneChip (B.interiorVertex β newChip) -
        oneChip (B.interiorVertex β oldChip) := by
  classical
  funext v
  rcases v with v | ⟨γ, offset⟩
  · simp [semibreakDivisor, oneChip,
      SubdivisionGraph.Spec.interiorVertex]
  · by_cases hγ : γ = β
    · subst γ
      simp [semibreakDivisor, replaceSemibreakChip, oneChip,
        SubdivisionGraph.Spec.interiorVertex]
      split_ifs <;> omega
    · simp [semibreakDivisor, replaceSemibreakChip, hγ, oneChip,
        SubdivisionGraph.Spec.interiorVertex]

theorem semibreakDivisor_remove_chip {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (β : Fin (g + 1)) (oldChip : Fin (B.length β - 1)) :
    semibreakDivisor B (replaceSemibreakChip B chips β none) =
      semibreakDivisor B (replaceSemibreakChip B chips β (some oldChip)) -
        oneChip (B.interiorVertex β oldChip) := by
  classical
  funext v
  rcases v with v | ⟨γ, offset⟩
  · simp [semibreakDivisor, oneChip,
      SubdivisionGraph.Spec.interiorVertex]
  · by_cases hγ : γ = β
    · subst γ
      simp [semibreakDivisor, replaceSemibreakChip, oneChip,
        SubdivisionGraph.Spec.interiorVertex]
      split_ifs <;> omega
    · simp [semibreakDivisor, replaceSemibreakChip, hγ, oneChip,
        SubdivisionGraph.Spec.interiorVertex]

theorem isSemibreak_remove_chip {g : ℕ} (B : Banana g)
    (chips : ∀ γ : Fin (g + 1), Option (Fin (B.length γ - 1)))
    (β : Fin (g + 1)) (_oldChip : Fin (B.length β - 1)) :
    IsSemibreak (B := B)
      (semibreakDivisor B (replaceSemibreakChip B chips β none)) := by
  exact ⟨replaceSemibreakChip B chips β none, rfl⟩

/-- Removing an occupied raw interior chip from a semibreak divisor remains
semibreak.  This is the coordinate-free form of the midpoint update below. -/
theorem isSemibreak_remove_interior_chip_of_eq_one {g : ℕ} (B : Banana g)
    (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (β : Fin (g + 1)) (offset : Fin (B.length β - 1))
    (hmem : E (B.interiorVertex β offset) = 1) :
    IsSemibreak (B := B) (E - oneChip (B.interiorVertex β offset)) := by
  rcases hE with ⟨chips, hchips⟩
  subst E
  have hchip : chips β = some offset := by
    simpa [semibreakDivisor_interiorVertex] using hmem
  have hsame : replaceSemibreakChip B chips β (some offset) = chips := by
    funext γ
    by_cases hγ : γ = β
    · subst γ
      simp [hchip]
    · exact replaceSemibreakChip_other B chips β γ _ hγ
  refine ⟨replaceSemibreakChip B chips β none, ?_⟩
  rw [semibreakDivisor_remove_chip B chips β offset, hsame]

/-! The preceding identity is phrased in the chip-coordinate API.  This
adapter exposes the same operation from the paper-facing `IsSemibreak`
predicate at a length-two midpoint. -/

theorem isSemibreak_remove_midpoint_chip {g : ℕ} (B : Banana g)
    (E : CFDiv B.graph) (hE : IsSemibreak B E)
    (α : Fin (g + 1)) (i : B.PathPosition α)
    (hα : B.length α = 2) (hi : i.val = 1)
    (hmem : E (strandVertex B α i) = 1) :
    IsSemibreak (B := B)
      (E - oneChip (strandVertex B α i)) := by
  rcases hE with ⟨chips, hchips⟩
  have hmid : strandVertex B α i = B.interiorVertex α ⟨0, by omega⟩ := by
    unfold strandVertex
    split_ifs with htail
    · rw [B.pathVertex_eq_interiorVertex α i ⟨by omega, by omega⟩]
      congr 2
      apply Fin.ext
      omega
    · let j : B.PathPosition α := ⟨B.length α - i.val, by omega⟩
      rw [B.pathVertex_eq_interiorVertex α j ⟨by dsimp [j]; omega, by dsimp [j]; omega⟩]
      congr 2
      apply Fin.ext
      dsimp [j]
      omega
  subst E
  rw [hmid] at hmem ⊢
  have hchip : chips α = some ⟨0, by omega⟩ := by
    simpa [semibreakDivisor_interiorVertex] using hmem
  have hsame : replaceSemibreakChip B chips α (some ⟨0, by omega⟩) = chips := by
    funext γ
    by_cases hγα : γ = α
    · subst γ
      simp [hchip]
    · exact replaceSemibreakChip_other B chips α γ _ hγα
  refine ⟨replaceSemibreakChip B chips α none, ?_⟩
  rw [semibreakDivisor_remove_chip B chips α ⟨0, by omega⟩]
  rw [hsame]

/-! In the low-degree range, removing a chip already present in the
semibreak part leaves the normal-form rank unchanged.  This is the rank
calculation used for the “midpoint is a base point” half of the proposed
exception proof. -/

theorem rank_bananaNormalForm_remove_midpoint_chip
    {g : ℕ} (B : Banana g) (E : CFDiv B.graph)
    (hE : IsSemibreak B E) (α : Fin (g + 1)) (i : B.PathPosition α)
    (hα : B.length α = 2) (hi : i.val = 1)
    (a b : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hdeg : a + b + deg E ≤ (g : ℤ))
    (hmem : E (strandVertex B α i) = 1) :
    rank B.graph (bananaNormalForm B a b E) =
      rank B.graph (bananaNormalForm B a b E -
        oneChip (strandVertex B α i)) := by
  have hE' := isSemibreak_remove_midpoint_chip B E hE α i hα hi hmem
  have hdeg' : b + deg (E - oneChip (strandVertex B α i)) ≤ (g : ℤ) := by
    rw [deg.map_sub, deg_one_chip]
    omega
  have hdeg_remove : deg (E - oneChip (strandVertex B α i)) = deg E - 1 := by
    rw [deg.map_sub, deg_one_chip]
  have hrewrite : bananaNormalForm B a b E -
      oneChip (strandVertex B α i) =
      bananaNormalForm B a b (E - oneChip (strandVertex B α i)) := by
    unfold bananaNormalForm
    abel
  rw [hrewrite]
  rw [rank_bananaNormalForm B a b E hE (by omega) hb
    (by omega : b + deg E ≤ (g : ℤ))]
  rw [rank_bananaNormalForm B a b (E - oneChip (strandVertex B α i)) hE'
    (by omega) hb hdeg']
  have hmin : min a b ≥ 0 := by omega
  have htop : a + b + deg E - (g : ℤ) ≤ min a b := by omega
  have htop' : a + b + deg (E - oneChip (strandVertex B α i)) -
      (g : ℤ) ≤ min a b := by
    rw [hdeg_remove]
    omega
  rw [max_eq_left htop, max_eq_left htop']

noncomputable def basePointDrop (M : TwiceMarked) (D : CFDiv M.graph) : ℤ :=
  rank M.graph D - rank M.graph (D - oneChip M.u)

/-! A convenient difference form of the path-pair sliding identities. -/

theorem linear_equiv_rearrange_pair {G : CFGraph} {A B C D : CFDiv G}
    (h : linearEquiv G (A + B) (C + D)) :
    linearEquiv G (A - C) (D - B) := by
  unfold linearEquiv at h ⊢
  convert h using 1 ; abel

theorem path_pair_linearEquiv_tail_sum_sub
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i k : B.PathPosition α)
    (hi : 0 < i.val) (hk : 0 < k.val)
    (hsum : i.val + k.val < B.length α) :
    linearEquiv B.graph
      (oneChip (B.pathVertex α i) -
        oneChip (B.coreVertex (B.core.tail α)))
      (oneChip (B.pathVertex α ⟨i.val + k.val, by omega⟩) -
        oneChip (B.pathVertex α k)) := by
  apply linear_equiv_rearrange_pair
  exact path_pair_linearEquiv_tail_sum B α i k hi hk hsum

theorem path_pair_linearEquiv_head_excess_sub
    {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i k : B.PathPosition α)
    (hi : i.val < B.length α) (hk : k.val < B.length α)
    (hsum : B.length α < i.val + k.val) :
    linearEquiv B.graph
      (oneChip (B.pathVertex α i) -
        oneChip (B.coreVertex (B.core.head α)))
      (oneChip (B.pathVertex α
          ⟨i.val + k.val - B.length α, by omega⟩) -
        oneChip (B.pathVertex α k)) := by
  unfold linearEquiv
  have h := path_pair_linearEquiv_head_excess B α i k hi hk hsum
  unfold linearEquiv at h
  convert h using 1 ; abel

theorem rankDelta_eq_basePointDrop_sub (M : TwiceMarked) (D : CFDiv M.graph) :
    rankDelta M D =
      basePointDrop M D - basePointDrop M (D - oneChip M.v) := by
  have hswap : D - oneChip M.u - oneChip M.v =
      D - oneChip M.v - oneChip M.u := by abel
  unfold rankDelta basePointDrop
  rw [hswap]
  ring

theorem two_smul_midpoint_linearEquiv_endpoints {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (i : B.PathPosition α)
    (hα : B.length α = 2) (hi : i.val = 1) :
    linearEquiv B.graph ((2 : ℤ) • oneChip (strandVertex B α i))
      (oneChip (leftEndpoint B) + oneChip (rightEndpoint B)) := by
  have hi' : i = ⟨1, by omega⟩ := by
    apply Fin.ext
    exact hi
  have hmirror : strandMirror B α i = i := by
    apply Fin.ext
    simp [strandMirror, hα, hi]
  have hreflection := endpoint_sum_linearEquiv_strand_reflection B α i
  rw [hmirror] at hreflection
  simpa [hi', two_smul] using hreflection.symm

theorem deg_canonical_dual {g : ℕ} (B : Banana g) (u v : B.graph.V)
    (D : CFDiv B.graph) :
    deg (canonicalDivisor B.graph + oneChip u + oneChip v - D) =
      2 * (g : ℤ) - deg D := by
  rw [deg.map_sub, deg.map_add, deg.map_add, degree_of_canonical_divisor,
    deg_one_chip, deg_one_chip, B.genus_graph]
  push_cast
  ring

end Bananas
