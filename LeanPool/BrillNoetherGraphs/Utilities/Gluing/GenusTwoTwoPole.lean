/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Foundations.RiemannRochWinnable
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.CanonicalWedge
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.TwoPole

/-!
# Genus-two seeds for two-pole gluing

The two-pole compatibility problem is most naturally studied after retaining
one cross-edge and contracting its separating bridge.  The result is a
genus-two/genus-two vertex wedge with glue vertex `a`.  Two uniform facts hold
there without any metric or combinatorial case split:

* the sum `K_A + K_B` of the factor canonical divisors has rank at least one;
* the four-chip glue pile has rank at least one and `4a - 2u` is winnable for
  every vertex `u` of the wedge.

The second statement is the marked seed.  Its proof is just the critical
degree form of Riemann's inequality on whichever genus-two factor contains
`u`.  The only remaining issue after restoring the second cross-edge is to
choose one seam phase compatible with the desired rank tests; that scalar
problem is represented by `TwoPoleProfile.lean`.
-/

namespace Utilities
namespace TwoPole

universe u v

/-- A divisor whose degree equals the genus is winnable. -/
theorem winnable_of_degree_eq_genus
    (G : CFGraph.{u}) (hG : graph_connected G) (D : CFDiv G)
    (hDegree : deg D = genus G) :
    winnable G D := by
  exact winnable_of_deg_ge_genus hG D (by omega)

/-- Degree of an integral pile at one vertex. -/
@[simp] theorem deg_zsmul_one_chip
    (G : CFGraph.{u}) (q : G.V) (n : ℤ) :
    deg (n • one_chip (G := G) q) = n := by
  rw [map_zsmul, deg_one_chip]
  simp

/-- **The local `4a - 2u` lemma.**  On a connected genus-two graph, four
chips at any anchor absorb a doubled chip at any marked vertex. -/
theorem winnable_four_pile_sub_two
    (G : CFGraph.{u}) (a uMark : G.V)
    (hG : graph_connected G) (hGenus : genus G = 2) :
    winnable G
      ((4 : ℤ) • one_chip a - (2 : ℤ) • one_chip uMark) := by
  apply winnable_of_degree_eq_genus G hG
  rw [deg.map_sub, deg_zsmul_one_chip, deg_zsmul_one_chip, hGenus]
  norm_num

/-! ## The four-chip pile on a genus-two/genus-two wedge -/

/-- The four-chip pile at the common vertex of a wedge. -/
def wedgeGluePile
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    CFDiv (vertexWedge G H x y) :=
  wedgeAddDivisor G H x y ((4 : ℤ) • one_chip x) 0

/-- The glue pile has the same presentation from the right factor. -/
theorem wedgeGluePile_eq_right
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) :
    wedgeGluePile G H x y =
      wedgeAddDivisor G H x y 0 ((4 : ℤ) • one_chip y) := by
  funext z
  cases z with
  | inl a => simp [wedgeGluePile, wedgeAddDivisor, one_chip]
  | inr b => simp [wedgeGluePile, wedgeAddDivisor, one_chip, b.2]
/-- Removing a doubled left vertex from the glue pile stays on the left
factor. -/
theorem wedgeGluePile_sub_two_inl
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V) (a : G.V) :
    wedgeGluePile G H x y -
        (2 : ℤ) • one_chip (Sum.inl a : (vertexWedge G H x y).V) =
      wedgeAddDivisor G H x y
        ((4 : ℤ) • one_chip x - (2 : ℤ) • one_chip a) 0 := by
  funext z
  cases z with
  | inl c =>
      simp only [wedgeGluePile, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        wedgeAddDivisor_left]
      by_cases hc : c = a
      · subst c
        simp [one_chip]
      · have hSum :
            (Sum.inl c : Sum G.V {b : H.V // b ≠ y}) ≠ Sum.inl a :=
            fun h => hc (Sum.inl.inj h)
        simp [one_chip, hc, hSum]
  | inr d =>
      simp only [wedgeGluePile, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        wedgeAddDivisor_right]
      simp [one_chip]
/-- Removing a doubled strictly-right vertex from the right presentation of
the glue pile stays on the right factor. -/
theorem wedgeGluePile_sub_two_inr
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (b : {b : H.V // b ≠ y}) :
    wedgeAddDivisor G H x y 0 ((4 : ℤ) • one_chip y) -
        (2 : ℤ) • one_chip (Sum.inr b : (vertexWedge G H x y).V) =
      wedgeAddDivisor G H x y 0
        ((4 : ℤ) • one_chip y - (2 : ℤ) • one_chip b.1) := by
  have hyb : y ≠ b.1 := fun h => b.2 h.symm
  funext z
  cases z with
  | inl c =>
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        wedgeAddDivisor_left]
      by_cases hc : c = x <;> simp [hc, one_chip, hyb]
  | inr d =>
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        wedgeAddDivisor_right]
      by_cases hd : d = b
      · subst d
        simp [one_chip]
      · have hval : d.1 ≠ b.1 := fun h => hd (Subtype.ext h)
        have hSum :
            (Sum.inr d : Sum G.V {b : H.V // b ≠ y}) ≠ Sum.inr b :=
          fun h => hd (Sum.inr.inj h)
        simp [one_chip, hval, hSum]

/-- **The wedge `4a - 2u` lemma.**  Four chips at the glue vertex of a
genus-two/genus-two wedge absorb a doubled chip at every vertex. -/
theorem winnable_wedgeGluePile_sub_two
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hG : graph_connected G) (hGenusG : genus G = 2)
    (hH : graph_connected H) (hGenusH : genus H = 2)
    (uMark : (vertexWedge G H x y).V) :
    winnable (vertexWedge G H x y)
      (wedgeGluePile G H x y - (2 : ℤ) • one_chip uMark) := by
  cases uMark with
  | inl a =>
      rw [wedgeGluePile_sub_two_inl]
      refine winnable_wedgeAddDivisor G H x y _ 0 ?_ ?_
      · exact winnable_four_pile_sub_two G x a hG hGenusG
      · exact winnable_of_effective H 0 (fun _ => le_rfl)
  | inr b =>
      rw [wedgeGluePile_eq_right, wedgeGluePile_sub_two_inr]
      refine winnable_wedgeAddDivisor G H x y 0 _ ?_ ?_
      · exact winnable_of_effective G 0 (fun _ => le_rfl)
      · exact winnable_four_pile_sub_two H y b.1 hH hGenusH

/-- Four chips at the glue vertex of a genus-two/genus-two wedge form a
rank-one divisor. -/
theorem rank_wedgeGluePile_ge_one
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hG : graph_connected G) (hGenusG : genus G = 2)
    (hH : graph_connected H) (hGenusH : genus H = 2) :
    rank (vertexWedge G H x y) (wedgeGluePile G H x y) ≥ 1 := by
  rw [rank_ge_one_iff_winnable_sub_one_chip]
  intro uMark
  have hDouble := winnable_wedgeGluePile_sub_two
    G H x y hG hGenusG hH hGenusH uMark
  have hAdd := winnable_add_effective_divisor (vertexWedge G H x y)
    (wedgeGluePile G H x y - (2 : ℤ) • one_chip uMark)
    (one_chip uMark) hDouble (eff_one_chip uMark)
  convert hAdd using 1
  funext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-! ## The unmarked local-canonical seed -/

/-- **Unmarked `K_A + K_B` lemma on the one-pole model.**  The sum of the two
factor canonical divisors has rank at least one on a wedge of connected
genus-two graphs. -/
theorem rank_wedge_canonicalSum_ge_one
    (G : CFGraph.{u}) (H : CFGraph.{v}) (x : G.V) (y : H.V)
    (hG : graph_connected G) (hGenusG : genus G = 2)
    (hH : graph_connected H) (hGenusH : genus H = 2) :
    rank (vertexWedge G H x y)
      (wedgeAddDivisor G H x y (canonical_divisor G) (canonical_divisor H)) ≥ 1 := by
  simpa only [wedgeCanonicalSum] using
    rank_wedgeCanonicalSum_ge_one_of_genus_sum_four G H x y hG hH (by
      rw [hGenusG, hGenusH]
      norm_num)

end TwoPole
end Utilities
