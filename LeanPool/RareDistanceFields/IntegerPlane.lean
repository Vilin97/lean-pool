/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.OrderedColors
import LeanPool.RareDistanceFields.DyadicNorm

/-!
# Two rare distances in every finite integer-coordinate planar set

See the project entry module for the exact coordinate restrictions and source roles.
Order squared distances by their 2-adic valuations, breaking ties numerically.
The dyadic circle lemma supplies the increasing-base rule. The two top classes
therefore have unordered multiplicity at most the number of points.
This is a restricted coordinate theorem; arbitrary real coordinates are not assumed rational.
-/

namespace LeanPool.RareDistanceFields.IntegerPlane

open DyadicNorm
noncomputable section

open Classical in
/-- An integer coordinate pair in the plane. -/
abbrev Point := ℤ × ℤ

open Classical in
/-- The integer squared Euclidean distance between two points. -/
def sqDist (p q : Point) : ℤ := normSq (p.1 - q.1) (p.2 - q.2)

open Classical in
theorem sqDist_symm (p q : Point) : sqDist p q = sqDist q p := by
  dsimp [sqDist, normSq]; ring

open Classical in
theorem sqDist_eq_zero (p q : Point) : sqDist p q = 0 ↔ p = q := by
  constructor
  · intro h
    dsimp [sqDist, normSq] at h
    apply Prod.ext <;> nlinarith [sq_nonneg (p.1 - q.1), sq_nonneg (p.2 - q.2)]
  · rintro rfl
    simp [sqDist, normSq]

open Classical in
/-- The lexicographic key of a squared distance: its 2-adic valuation, then its value. -/
def key (r : ℤ) : Lex (ℕ × ℤ) := toLex (padicValInt 2 r, r)

open Classical in
theorem key_injective : Function.Injective key := by
  intro a b h
  exact congrArg (fun r => (ofLex r).2) h

open Classical in
theorem equal_spokes_increase (p q r : Point) (hpq : p ≠ q) (hqr : q ≠ r)
    (he : sqDist p q = sqDist p r) : key (sqDist p q) < key (sqDist q r) := by
  have hn : normSq (p.1 - q.1) (p.2 - q.2) ≠ 0 := (sqDist_eq_zero p q).not.mpr hpq
  have hd : normSq ((p.1 - q.1) - (p.1 - r.1)) ((p.2 - q.2) - (p.2 - r.2)) ≠ 0 := by
    have hn' := (sqDist_eq_zero r q).not.mpr hqr.symm
    have heq : normSq ((p.1 - q.1) - (p.1 - r.1)) ((p.2 - q.2) - (p.2 - r.2)) = sqDist r q := by
      dsimp [sqDist, normSq]; ring
    rw [heq]
    exact hn'
  have hv := equal_norm_increase (p.1 - q.1) (p.2 - q.2) (p.1 - r.1) (p.2 - r.2) hn he hd
  have heq : normSq ((p.1 - q.1) - (p.1 - r.1)) ((p.2 - q.2) - (p.2 - r.2)) = sqDist q r := by
    dsimp [sqDist, normSq]; ring
  have hv' : padicValInt 2 (sqDist p q) < padicValInt 2 (sqDist q r) := by
    rw [heq] at hv
    exact hv
  exact Prod.Lex.left _ _ hv'

variable {V : Type*} [Fintype V]

open Classical in
/-- The simple graph of distinct labels at a specified integer squared distance. -/
def graph (x : V → Point) (r : ℤ) : SimpleGraph V :=
  OrderedColors.colorGraph (fun a b => sqDist (x a) (x b))
    (fun a b => sqDist_symm (x a) (x b)) r

omit [Fintype V] in
open Classical in
theorem graph_key (x : V → Point)
    (hsym : ∀ a b, key (sqDist (x a) (x b)) = key (sqDist (x b) (x a))) (r : ℤ) :
    OrderedColors.colorGraph (fun a b => key (sqDist (x a) (x b)))
      hsym (key r) = graph x r := by
  ext p q
  simp only [OrderedColors.colorGraph, graph, key_injective.eq_iff]

open Classical in
/-- An end-to-end statement with actual integer coordinates and occurring distances. -/
theorem two_rare_distances (x : V → Point) (hx : Function.Injective x)
    (hn : 3 ≤ Fintype.card V) :
    ∃ a b c d : V, a ≠ b ∧ c ≠ d ∧ sqDist (x a) (x b) ≠ sqDist (x c) (x d) ∧
      (graph x (sqDist (x a) (x b))).edgeFinset.card ≤ Fintype.card V ∧
      (graph x (sqDist (x c) (x d))).edgeFinset.card ≤ Fintype.card V := by
  let q := fun a b => key (sqDist (x a) (x b))
  have hs : ∀ a b, q a b = q b a := fun a b => congrArg key (sqDist_symm (x a) (x b))
  have hb : OrderedColors.IncreasingBases q := by
    intro a b c hab hac hbc he
    exact equal_spokes_increase (x a) (x b) (x c) (hx.ne hab) (hx.ne hbc) (key_injective he)
  obtain ⟨r, hr, D, hD, hrD, hrare, hrareD⟩ := OrderedColors.two_rare_colors q hs hb hn
  obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.mp hD
  have hab' : a ≠ b := (Finset.mem_offDiag.mp hab).2.2
  have hcd' : c ≠ d := (Finset.mem_offDiag.mp hcd).2.2
  refine ⟨a, b, c, d, hab', hcd', ?_, ?_, ?_⟩
  · intro he
    exact hrD (congrArg key he)
  · dsimp only [q] at hrare
    rw [graph_key x hs] at hrare
    exact hrare
  · dsimp only [q] at hrareD
    rw [graph_key x hs] at hrareD
    exact hrareD

end
end LeanPool.RareDistanceFields.IntegerPlane
