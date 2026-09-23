/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Algebra.RectangleSupport
public import Mathlib.Tactic.Linarith

/-
Upstream: https://github.com/boonsuan/nivat
Commit: 84fe839635bdebb7d5e80c209b4f578a0c767fcf
Originally released under MIT; the upstream copyright and permission notice follow.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-!
# Strict reduction of rectangular area

This module proves the geometry in Corollary 2.3 (`cor:line-descent`). The four
coordinate extrema describe the eroded rectangle. Two distinct support sites
force at least one side to shrink, so nonempty erosion has strictly smaller
area.

The main interface `exists_smaller_rectangle_of_annihilator` obtains the two
support sites directly from a nonzero annihilated configuration. This geometric
statement holds for arbitrary Laurent filters; in the corollary it is applied
to the line generator supplied by Theorem 4.1 (`thm:exact-ideal`). Nonemptiness
and the filtered complexity inequality in Corollary 2.3 come from
`Nivat.Descent.exact_complexity_descent`; the final rectangular induction
combines them with the geometry proved here.
-/

@[expose] public section

namespace Nivat.Algebra

/-- Auxiliary to Corollary 2.3 (`cor:line-descent`): the four coordinate extrema of the filter
support give the exact coordinate bounds of rectangular erosion. -/
private theorem mem_erodedWindow_iff_bounds (Φ : Laurent) (hΦ : Φ ≠ 0) (m n : ℕ)
    (loX hiX loY hiY : Lattice)
    (hloX : loX ∈ Φ.coeff.support) (hhiX : hiX ∈ Φ.coeff.support)
    (hloY : loY ∈ Φ.coeff.support) (hhiY : hiY ∈ Φ.coeff.support)
    (hminX : ∀ a ∈ Φ.coeff.support, loX.1 ≤ a.1)
    (hmaxX : ∀ a ∈ Φ.coeff.support, a.1 ≤ hiX.1)
    (hminY : ∀ a ∈ Φ.coeff.support, loY.2 ≤ a.2)
    (hmaxY : ∀ a ∈ Φ.coeff.support, a.2 ≤ hiY.2) (z : Lattice) :
    z ∈ erodedWindow Φ hΦ (rectangle m n) ↔
      -loX.1 ≤ z.1 ∧ z.1 < (m : ℤ) - hiX.1 ∧
        -loY.2 ≤ z.2 ∧ z.2 < (n : ℤ) - hiY.2 := by
  rw [mem_erodedWindow]
  constructor
  · intro hz
    have hloXBounds := (mem_rectangle _ m n).mp (hz loX hloX)
    have hhiXBounds := (mem_rectangle _ m n).mp (hz hiX hhiX)
    have hloYBounds := (mem_rectangle _ m n).mp (hz loY hloY)
    have hhiYBounds := (mem_rectangle _ m n).mp (hz hiY hhiY)
    simp only [Prod.fst_add, Prod.snd_add] at hloXBounds hhiXBounds hloYBounds hhiYBounds
    omega
  · intro hz a ha
    have hminXa := hminX a ha
    have hmaxXa := hmaxX a ha
    have hminYa := hminY a ha
    have hmaxYa := hmaxY a ha
    rw [mem_rectangle]
    simp only [Prod.fst_add, Prod.snd_add]
    omega

/-- The geometric reduction in Corollary 2.3 (`cor:line-descent`), stated for any filter with two
distinct support sites: a nonempty erosion is a translated positive axis-aligned rectangle of
strictly smaller area. -/
theorem exists_smaller_rectangle_of_erodedWindow_nonempty (Φ : Laurent) (hΦ : Φ ≠ 0)
    (m n : ℕ) (hS : (erodedWindow Φ hΦ (rectangle m n)).Nonempty)
    (htwo : ∃ u ∈ Φ.coeff.support, ∃ v ∈ Φ.coeff.support, u ≠ v) :
    ∃ m' n' : ℕ, ∃ o : Lattice, 0 < m' ∧ 0 < n' ∧ m' * n' < m * n ∧
      erodedWindow Φ hΦ (rectangle m n) = (rectangle m' n').image (fun z => z + o) := by
  classical
  have hne : Φ.coeff.support.Nonempty := by simpa [Finsupp.support_nonempty_iff] using hΦ
  obtain ⟨loX, hloX, hminX⟩ := Φ.coeff.support.exists_min_image Prod.fst hne
  obtain ⟨hiX, hhiX, hmaxX⟩ := Φ.coeff.support.exists_max_image Prod.fst hne
  obtain ⟨loY, hloY, hminY⟩ := Φ.coeff.support.exists_min_image Prod.snd hne
  obtain ⟨hiY, hhiY, hmaxY⟩ := Φ.coeff.support.exists_max_image Prod.snd hne
  have hbounds := mem_erodedWindow_iff_bounds Φ hΦ m n loX hiX loY hiY
    hloX hhiX hloY hhiY hminX hmaxX hminY hmaxY
  let m' : ℕ := ((m : ℤ) - hiX.1 + loX.1).toNat
  let n' : ℕ := ((n : ℤ) - hiY.2 + loY.2).toNat
  let o : Lattice := (-loX.1, -loY.2)
  have hshape : erodedWindow Φ hΦ (rectangle m n) =
      (rectangle m' n').image (fun z => z + o) := by
    ext z
    rw [hbounds, Finset.mem_image]
    constructor
    · intro hz
      refine ⟨z - o, ?_, by simp⟩
      rw [mem_rectangle]
      dsimp [m', n', o]
      omega
    · rintro ⟨w, hw, rfl⟩
      rw [mem_rectangle] at hw
      dsimp [m', n', o] at *
      omega
  obtain ⟨z, hz⟩ := hS
  have hzbound := (hbounds z).mp hz
  have hmpos : 0 < m' := by dsimp [m']; omega
  have hnpos : 0 < n' := by dsimp [n']; omega
  have hmle : m' ≤ m := by
    have := hminX hiX hhiX
    dsimp [m']
    omega
  have hnle : n' ≤ n := by
    have := hminY hiY hhiY
    dsimp [n']
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := htwo
  have hspan : loX.1 < hiX.1 ∨ loY.2 < hiY.2 := by
    by_contra! h
    have hminXu := hminX u hu
    have hmaxXu := hmaxX u hu
    have hminXv := hminX v hv
    have hmaxXv := hmaxX v hv
    have hminYu := hminY u hu
    have hmaxYu := hmaxY u hu
    have hminYv := hminY v hv
    have hmaxYv := hmaxY v hv
    apply huv
    apply Prod.ext <;> omega
  have hsmall : m' < m ∨ n' < n := by
    dsimp [m', n']
    omega
  refine ⟨m', n', o, hmpos, hnpos, ?_, hshape⟩
  rcases hsmall with hm | hn
  · exact (Nat.mul_lt_mul_of_pos_right hm hnpos).trans_le (Nat.mul_le_mul_left m hnle)
  · exact (Nat.mul_lt_mul_of_pos_left hn hmpos).trans_le (Nat.mul_le_mul_right n hmle)

/-- Auxiliary to Corollary 2.3 (`cor:line-descent`): a nonzero filter annihilating a nonzero
configuration has two distinct support sites, since a single shifted nonzero scalar acts
injectively. -/
private theorem one_lt_support_card_of_annihilates (Φ : Laurent) (hΦ : Φ ≠ 0)
    (d : Configuration ℚ) (hd : d ≠ 0) (hann : act Φ d = 0) :
    1 < Φ.coeff.support.card := by
  classical
  by_contra hcard
  have hcard' : Φ.coeff.support.card ≤ 1 := by omega
  have hne : Φ.coeff.support.Nonempty := by simpa [Finsupp.support_nonempty_iff] using hΦ
  obtain ⟨a, ha⟩ := hne
  have hsingle : Φ = AddMonoidAlgebra.single a (Φ.coeff a) := by
    apply AddMonoidAlgebra.coeff_injective
    apply Finsupp.support_subset_singleton.mp
    intro z hz
    exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp hcard') z hz a ha)
  have hk : Φ.coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
  rw [hsingle, act_single] at hann
  apply hd
  funext z
  have hv := congrFun hann (z - a)
  change Φ.coeff a * d ((z - a) + a) = 0 at hv
  rw [sub_add_cancel] at hv
  exact (mul_eq_zero.mp hv).resolve_left hk

/-- The strict-area conclusion of Corollary 2.3 (`cor:line-descent`): annihilation of a nonzero
configuration supplies the distinct support sites, and nonempty erosion is exactly a translated
positive rectangle of smaller area. -/
theorem exists_smaller_rectangle_of_annihilator (Φ : Laurent) (hΦ : Φ ≠ 0)
    (d : Configuration ℚ) (hd : d ≠ 0) (hann : act Φ d = 0)
    (m n : ℕ) (hS : (erodedWindow Φ hΦ (rectangle m n)).Nonempty) :
    ∃ m' n' : ℕ, ∃ o : Lattice, 0 < m' ∧ 0 < n' ∧ m' * n' < m * n ∧
      erodedWindow Φ hΦ (rectangle m n) = (rectangle m' n').image (fun z => z + o) :=
  exists_smaller_rectangle_of_erodedWindow_nonempty Φ hΦ m n hS
    (Finset.one_lt_card.mp (one_lt_support_card_of_annihilates Φ hΦ d hd hann))

end Nivat.Algebra
