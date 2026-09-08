/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.IntegerPlane
import Mathlib.Analysis.Complex.Basic

/-!
# Integer coordinate division by 1+i

See the project entry module for the exact coordinate restrictions and source roles.
Within either parity class, division by 1+i after a fixed translation preserves
integer coordinates and divides every squared distance by two.
-/

namespace LeanPool.RareDistanceFields.DyadicCoordinates

open DyadicNorm IntegerPlane
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The parity of the sum of the two integer coordinates. -/
def parity (p : Point) : ℤ := (p.1 + p.2) % 2
/-- The translated, rotated half-scale coordinates for a chosen parity class. -/
def halfPoint (e : ℤ) (p : Point) : Point := ((p.1 + p.2 - e) / 2, (p.2 - p.1 + e) / 2)

theorem parity_zero_or_one (p : Point) : parity p = 0 ∨ parity p = 1 := by
  dsimp [parity]; omega

theorem norm_even_iff (p q : Point) : 2 ∣ sqDist p q ↔ parity p = parity q := by
  rw [Int.dvd_iff_emod_eq_zero]
  change normSq (p.1 - q.1) (p.2 - q.2) % 2 = 0 ↔ _
  rw [norm_mod_two]
  dsimp [parity]
  omega

theorem halfPoint_scale (e : ℤ) (p q : Point) (hp : parity p = e) (hq : parity q = e) :
    sqDist p q = 2 * sqDist (halfPoint e p) (halfPoint e q) := by
  have h1 : 2 * ((p.1 + p.2 - e) / 2) = p.1 + p.2 - e := by dsimp [parity] at hp; omega
  have h2 : 2 * ((p.2 - p.1 + e) / 2) = p.2 - p.1 + e := by dsimp [parity] at hp; omega
  have h3 : 2 * ((q.1 + q.2 - e) / 2) = q.1 + q.2 - e := by dsimp [parity] at hq; omega
  have h4 : 2 * ((q.2 - q.1 + e) / 2) = q.2 - q.1 + e := by dsimp [parity] at hq; omega
  have hx : p.1 - q.1 = (halfPoint e p).1 - (halfPoint e q).1-
      ((halfPoint e p).2 - (halfPoint e q).2) := by dsimp [halfPoint]; omega
  have hy : p.2 - q.2 = (halfPoint e p).1 - (halfPoint e q).1 +
      ((halfPoint e p).2 - (halfPoint e q).2) := by dsimp [halfPoint]; omega
  change (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 =
    2 * (((halfPoint e p).1 - (halfPoint e q).1) ^ 2 + ((halfPoint e p).2 - (halfPoint e q).2) ^ 2)
  rw [hx, hy]
  ring

theorem halfPoint_injective (e : ℤ) :
    Function.Injective (fun p : {p : Point // parity p = e} => halfPoint e p.1) := by
  intro p q h
  change halfPoint e p.1 = halfPoint e q.1 at h
  apply Subtype.ext
  apply (sqDist_eq_zero p.1 q.1).mp
  rw [halfPoint_scale e p.1 q.1 p.2 q.2, h]
  simp [sqDist, normSq]

theorem valuation_double (r : ℤ) (hr : r ≠ 0) :
    padicValInt 2 (2 * r) = 1 + padicValInt 2 r := by
  rw [padicValInt.mul (by norm_num) hr]
  have hlo := (padicValInt_dvd_iff (p := 2) 1 (2 : ℤ)).mp (by norm_num)
  have hhi : ¬2 ≤ padicValInt 2 (2 : ℤ) := by
    intro h
    have hh := (padicValInt_dvd_iff (p := 2) 2 (2 : ℤ)).mpr (Or.inr h)
    norm_num at hh
  have := hlo.resolve_left (by norm_num)
  omega

theorem valuation_zero_iff (r : ℤ) (hr : r ≠ 0) :
    padicValInt 2 r = 0 ↔ ¬2 ∣ r := by
  constructor
  · intro h hd
    have hv := (padicValInt_dvd_iff (p := 2) 1 r).mp (by simpa using hd)
    have := hv.resolve_left hr
    omega
  · exact padicValInt.eq_zero_of_not_dvd

theorem sqDist_pos (p q : Point) (h : p ≠ q) : 0 < sqDist p q := by
  have hn := (sqDist_eq_zero p q).not.mpr h
  have hnonneg : 0 ≤ sqDist p q := by dsimp [sqDist, normSq]; positivity
  omega

/-- The standard embedding of an integer coordinate pair into the complex plane. -/
noncomputable def complexPoint (p : Point) : ℂ := ⟨p.1, p.2⟩

theorem complexPoint_injective : Function.Injective complexPoint := by
  intro p q h
  apply Prod.ext
  · have := congrArg Complex.re h
    dsimp [complexPoint] at this
    exact_mod_cast this
  · have := congrArg Complex.im h
    dsimp [complexPoint] at this
    exact_mod_cast this

theorem complex_dist_sq (p q : Point) :
    dist (complexPoint p) (complexPoint q) ^ 2 = (sqDist p q : ℝ) := by
  rw [Complex.dist_eq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, complexPoint, sqDist, normSq]
  push_cast
  ring

end LeanPool.RareDistanceFields.DyadicCoordinates
