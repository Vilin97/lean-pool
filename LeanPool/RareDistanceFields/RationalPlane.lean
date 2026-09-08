/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.IntegerPlane
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Two rare distances for finite rational-coordinate planar sets

See the project entry module for the exact coordinate restrictions and source roles.
A single nonzero integer clears every coordinate denominator. The integer
dyadic theorem then transports both occurring distance classes and their exact
unordered multiplicities back to the original rational points.
Rational coordinates are an explicit restriction, not a reduction of arbitrary
real planar sets or of all sets with rational squared distances.
-/

namespace LeanPool.RareDistanceFields.RationalPlane

noncomputable section

open Classical in
/-- A rational coordinate pair in the plane. -/
abbrev Point := ℚ × ℚ
variable {V : Type*} [Fintype V]

open Classical in
/-- The rational squared Euclidean distance between two points. -/
def sqDist (p q : Point) : ℚ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

open Classical in
theorem sqDist_symm (p q : Point) : sqDist p q = sqDist q p := by
  dsimp [sqDist]; ring

open Classical in
theorem sqDist_pos (p q : Point) (hne : p ≠ q) : 0 < sqDist p q := by
  dsimp [sqDist]
  have hn : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
    by_contra h
    push Not at h
    exact hne (Prod.ext h.1 h.2)
  rcases hn with hn|hn
  · nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hn), sq_nonneg (p.2 - q.2)]
  · nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hn), sq_nonneg (p.1 - q.1)]

open Classical in
/-- The simple graph of distinct labels at a specified rational squared distance. -/
def graph (x : V → Point) (r : ℚ) : SimpleGraph V :=
  OrderedColors.colorGraph (fun a b => sqDist (x a) (x b))
    (fun a b => sqDist_symm (x a) (x b)) r

omit [Fintype V] in
open Classical in
theorem clear_denominators [Finite V] (x : V → Point) :
    ∃ B : ℤ, B ≠ 0 ∧ ∃ y : V → IntegerPlane.Point,
      ∀ p, ((y p).1 : ℚ) = B * (x p).1 ∧ ((y p).2 : ℚ) = B * (x p).2 := by
  let := Fintype.ofFinite V
  let f : V × Bool → ℚ := fun p => if p.2 then (x p.1).1 else (x p.1).2
  obtain ⟨B, hB⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  have hc : ∀ p : V, ∃ a b : ℤ, (a : ℚ) = (B : ℤ) * (x p).1 ∧ (b : ℚ) = (B : ℤ) * (x p).2 := by
    intro p
    obtain ⟨a, ha⟩ := hB (p, true)
    obtain ⟨b, hb⟩ := hB (p, false)
    refine ⟨a, b, ?_, ?_⟩
    · simpa [f, zsmul_eq_mul] using ha
    · simpa [f, zsmul_eq_mul] using hb
  choose a b ha hb using hc
  exact ⟨B, nonZeroDivisors.ne_zero B.property, fun p => (a p, b p), fun p => ⟨ha p, hb p⟩⟩

open Classical in
theorem two_rare_squared_distances (x : V → Point) (hx : Function.Injective x)
    (hn : 3 ≤ Fintype.card V) :
    ∃ a b c d : V, a ≠ b ∧ c ≠ d ∧ sqDist (x a) (x b) ≠ sqDist (x c) (x d) ∧
      (graph x (sqDist (x a) (x b))).edgeFinset.card ≤ Fintype.card V ∧
      (graph x (sqDist (x c) (x d))).edgeFinset.card ≤ Fintype.card V := by
  obtain ⟨B, hB, y, hy⟩ := clear_denominators x
  have hB' : (B : ℚ) ≠ 0 := by exact_mod_cast hB
  have hscale (p r : V) : (IntegerPlane.sqDist (y p) (y r) : ℚ) =
      (B : ℚ) ^ 2 * sqDist (x p) (x r) := by
    dsimp [IntegerPlane.sqDist, DyadicNorm.normSq, sqDist]
    push_cast
    rw [(hy p).1, (hy p).2, (hy r).1, (hy r).2]
    ring
  have hyinj : Function.Injective y := by
    intro p r h
    apply hx
    apply Prod.ext
    · apply mul_left_cancel₀ hB'
      rw [← (hy p).1, ← (hy r).1, h]
    · apply mul_left_cancel₀ hB'
      rw [← (hy p).2, ← (hy r).2, h]
  have heq (p r a b : V) :
      IntegerPlane.sqDist (y p) (y r) = IntegerPlane.sqDist (y a) (y b) ↔
        sqDist (x p) (x r) = sqDist (x a) (x b) := by
    constructor
    · intro h
      have hh := congrArg (fun z : ℤ => (z : ℚ)) h
      rw [hscale, hscale] at hh
      exact mul_left_cancel₀ (pow_ne_zero 2 hB') hh
    · intro h
      apply Int.cast_injective (α := ℚ)
      rw [hscale, hscale, h]
  have hg (a b : V) : IntegerPlane.graph y (IntegerPlane.sqDist (y a) (y b)) =
      graph x (sqDist (x a) (x b)) := by
    ext p r
    simp only [IntegerPlane.graph, graph, OrderedColors.colorGraph, heq]
  obtain ⟨a, b, c, d, hab, hcd, hne, hr, hs⟩ := IntegerPlane.two_rare_distances y hyinj hn
  exact ⟨a, b, c, d, hab, hcd, fun h => hne ((heq a b c d).mpr h), hg a b ▸ hr, hg c d ▸ hs⟩

open Classical in
/-- The standard complex embedding of a rational coordinate pair. -/
noncomputable def complexPoint (p : Point) : ℂ := ⟨p.1, p.2⟩

open Classical in
theorem complex_dist_sq (p q : Point) :
    dist (complexPoint p) (complexPoint q) ^ 2 = (sqDist p q : ℝ) := by
  rw [Complex.dist_eq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, complexPoint, sqDist]
  push_cast
  ring

open Classical in
/-- The simple graph of distinct labels at a specified embedded Euclidean distance. -/
def distanceGraph (x : V → Point) (d : ℝ) : SimpleGraph V :=
  OrderedColors.colorGraph (fun p q => dist (complexPoint (x p)) (complexPoint (x q)))
    (fun _ _ => dist_comm _ _) d

omit [Fintype V] in
open Classical in
theorem graph_eq_distanceGraph (x : V → Point) (a b : V) :
    graph x (sqDist (x a) (x b)) =
      distanceGraph x (dist (complexPoint (x a)) (complexPoint (x b))) := by
  ext p q
  simp only [graph, distanceGraph, OrderedColors.colorGraph]
  apply and_congr_right
  intro _hpq
  constructor
  · intro h
    have hh := congrArg (fun z : ℚ => (z : ℝ)) h
    rw [← complex_dist_sq, ← complex_dist_sq] at hh
    nlinarith [dist_nonneg (x := complexPoint (x p)) (y := complexPoint (x q)),
      dist_nonneg (x := complexPoint (x a)) (y := complexPoint (x b))]
  · intro h
    apply Rat.cast_injective (α := ℝ)
    rw [← complex_dist_sq, ← complex_dist_sq, h]

open Classical in
/-- Two occurring positive Euclidean lengths, with unordered multiplicities at most n. -/
theorem two_rare_euclidean_distances (x : V → Point) (hx : Function.Injective x)
    (hn : 3 ≤ Fintype.card V) :
    ∃ d e : ℝ, 0 < d ∧ 0 < e ∧ d ≠ e ∧
      (∃ a b, dist (complexPoint (x a)) (complexPoint (x b)) = d) ∧
      (∃ a b, dist (complexPoint (x a)) (complexPoint (x b)) = e) ∧
      (distanceGraph x d).edgeFinset.card ≤ Fintype.card V ∧
      (distanceGraph x e).edgeFinset.card ≤ Fintype.card V := by
  obtain ⟨a, b, c, d, hab, hcd, hne, hr, hs⟩ := two_rare_squared_distances x hx hn
  have hdpos (p q : V) (hpq : p ≠ q) : 0 < dist (complexPoint (x p)) (complexPoint (x q)) := by
    have hp := sqDist_pos (x p) (x q) (hx.ne hpq)
    have hp' : (0 : ℝ) < (sqDist (x p) (x q) : ℝ) := by exact_mod_cast hp
    rw [← complex_dist_sq] at hp'
    nlinarith [dist_nonneg (x := complexPoint (x p)) (y := complexPoint (x q))]
  refine ⟨_, _, hdpos a b hab, hdpos c d hcd, ?_, ⟨a, b, rfl⟩, ⟨c, d, rfl⟩, ?_, ?_⟩
  · intro he
    apply hne
    apply Rat.cast_injective (α := ℝ)
    rw [← complex_dist_sq, ← complex_dist_sq, he]
  · exact graph_eq_distanceGraph x a b ▸ hr
  · exact graph_eq_distanceGraph x c d ▸ hs

end
end LeanPool.RareDistanceFields.RationalPlane
