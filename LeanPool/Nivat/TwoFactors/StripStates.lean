/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Core.Basic
public import LeanPool.Nivat.TwoFactors.FiniteState
public import Mathlib.Data.Finset.Max
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
# The finite description of whole-strip states

Lemma 5.6 (`lem:strip-states`) of `paper/nivat.tex`. The differences of
transverse translates have a horizontal period, so finitely many coordinates
distinguish their restrictions to an infinite strip. A deterministic predecessor
gives a transverse period. Otherwise the greatest disagreeing row positions
an agreeing strip immediately above a disagreement.
-/

public section

namespace Nivat.TwoFactors

/-- The infinite horizontal strip consisting of all sites on rows `1` through `W`. Lemma 5.6
(`lem:strip-states`). -/
def Strip (W : ℕ) : Set Lattice := {z | 1 ≤ z.2 ∧ z.2 ≤ W}

/-- The restriction of the `n`th transverse translate to the whole infinite strip. Lemma 5.6
(`lem:strip-states`). -/
def stripState {A : Type*} (c : Configuration A) (W : ℕ) (t : Lattice) (n : ℤ) :
    Strip W → A := fun z => shift (n • t) c z

/-- A mixed-difference identity makes the difference of any two integer transverse translates
periodic in the first direction. Lemma 5.6 (`lem:strip-states`). -/
theorem translate_difference_periodic {A : Type*} [AddCommGroup A]
    (c : Configuration A) (h t : Lattice)
    (hmix : difference h (difference t c) = 0) (m n : ℤ) :
    IsPeriod (shift (m • t) c - shift (n • t) c) h := by
  have hDt : IsPeriod (difference h c) t := by
    apply (difference_eq_zero_iff t _).mp
    rwa [difference_comm]
  intro z
  have hm := hDt.zsmul m z
  have hn := hDt.zsmul n z
  have hm' : shift (m • t) c (z + h) - shift (m • t) c z = difference h c z := by
    simpa only [difference_apply, shift_apply, add_right_comm _ h] using hm
  have hn' : shift (n • t) c (z + h) - shift (n • t) c z = difference h c z := by
    simpa only [difference_apply, shift_apply, add_right_comm _ h] using hn
  change shift (m • t) c (z + h) - shift (n • t) c (z + h) =
    shift (m • t) c z - shift (n • t) c z
  calc
    _ = ((shift (m • t) c (z + h) - shift (m • t) c z) -
      (shift (n • t) c (z + h) - shift (n • t) c z)) +
        (shift (m • t) c z - shift (n • t) c z) := by abel
    _ = _ := by rw [hm', hn', sub_self, zero_add]

/-- When a strip difference has horizontal period `q`, equality on `q` consecutive sites of
every row implies equality on the entire strip. Lemma 5.6 (`lem:strip-states`). -/
theorem strip_eq_of_finite_test {A : Type*} [AddCommGroup A]
    (x y : Configuration A) (q W : ℕ) (hq : 0 < q)
    (hdiff : IsPeriod (x - y) ((q : ℤ), 0))
    (htest : ∀ i j : ℤ, 0 ≤ i → i < q → 1 ≤ j → j ≤ W → x (i, j) = y (i, j)) :
    ∀ z : Lattice, 1 ≤ z.2 → z.2 ≤ W → x z = y z := by
  rintro ⟨i, j⟩ hj hW
  let d : ℤ → A := fun r => x (r, j) - y (r, j)
  have hperiod : Function.Periodic d (q : ℤ) := by
    intro r
    simpa only [d, Pi.sub_apply, Prod.mk_add_mk, add_zero] using hdiff (r, j)
  have heq : d i = d (i % (q : ℤ)) :=
    periodic_eq_of_emod_eq d (q : ℤ) hperiod (by simp only [Int.emod_emod])
  apply sub_eq_zero.mp
  change d i = 0
  rw [heq]
  exact sub_eq_zero.mpr (htest _ j (Int.emod_nonneg _ (by omega))
    (Int.emod_lt_of_pos _ (by omega)) hj hW)

/-- Only finitely many whole-strip states occur: restriction to `q * W` sites is injective on
them because their pairwise differences have horizontal period `q`. Lemma 5.6
(`lem:strip-states`). -/
theorem finite_stripState_range {A : Type*} [AddCommGroup A]
    (c : Configuration A) (hc : FiniteRange c) (q W : ℕ) (hq : 0 < q) (t : Lattice)
    (hmix : difference ((q : ℤ), 0) (difference t c) = 0) :
    (Set.range (stripState c W t)).Finite := by
  let key : (Strip W → A) → ((Fin q × Fin W) → A) :=
    fun s r => s ⟨((r.1 : ℕ), (r.2 : ℕ) + 1), by
      constructor <;> push_cast <;> omega⟩
  have hfinite : (key '' Set.range (stripState c W t)).Finite := by
    refine (Set.Finite.pi' (fun _ : Fin q × Fin W => hc)).subset ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩ r
    exact ⟨(((r.1 : ℕ), (r.2 : ℕ) + 1) : Lattice) + n • t, rfl⟩
  apply hfinite.of_finite_image
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ heq
  funext z
  apply strip_eq_of_finite_test (shift (m • t) c) (shift (n • t) c) q W hq
    (translate_difference_periodic c ((q : ℤ), 0) t hmix m n) _ z z.property.1 z.property.2
  intro i j hi hiq hj hjW
  have hir : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi
  have hjr : ((j - 1).toNat : ℤ) = j - 1 := Int.toNat_of_nonneg (by omega)
  let r : Fin q × Fin W := (⟨i.toNat, by omega⟩, ⟨(j - 1).toNat, by omega⟩)
  have h := congrFun heq r
  change shift (m • t) c ((i.toNat : ℤ), ((j - 1).toNat : ℤ) + 1) =
    shift (n • t) c ((i.toNat : ℤ), ((j - 1).toNat : ℤ) + 1) at h
  simpa only [hir, hjr, sub_add_cancel] using h

/-- Every lattice site can be moved by an integer multiple of `(a,M)` into rows `1` through `M`;
arbitrary horizontal shear is allowed. Lemma 5.6 (`lem:strip-states`). -/
theorem exists_transverse_strip_representative (a M : ℤ) (hM : 0 < M) (z : Lattice) :
    ∃ n : ℤ, ∃ w : Lattice, 1 ≤ w.2 ∧ w.2 ≤ M ∧ z = w + n • (a, M) := by
  let n : ℤ := (z.2 - 1) / M
  let w : Lattice := z - n • (a, M)
  have hw : w.2 = 1 + (z.2 - 1) % M := by
    dsimp [w, n]
    have he := Int.emod_add_mul_ediv (z.2 - 1) M
    nlinarith
  refine ⟨n, w, ?_, ?_, by dsimp [w]; abel⟩
  · rw [hw]
    have := Int.emod_nonneg (z.2 - 1) (ne_of_gt hM)
    omega
  · rw [hw]
    have := Int.emod_lt_of_pos (z.2 - 1) hM
    omega

/-- A period of the bilateral strip-state sequence gives a global multiple of the transverse
direction, since a strip at least `M` rows wide meets every transverse orbit. Lemma 5.6
(`lem:strip-states`). -/
theorem global_period_of_stripState_period {A : Type*} (c : Configuration A)
    (W : ℕ) (a M : ℤ) (hM : 0 < M) (hMW : M ≤ W) (p : ℕ)
    (hper : Function.Periodic (stripState c W (a, M)) (p : ℤ)) :
    IsPeriod c (p • (a, M)) := by
  intro z
  obtain ⟨n, w, hwlo, hwhi, rfl⟩ := exists_transverse_strip_representative a M hM z
  have h := congrFun (hper n) (⟨w, hwlo, hwhi.trans hMW⟩ : Strip W)
  simpa only [stripState, shift_apply, add_zsmul, natCast_zsmul, add_assoc] using h

/-- Translating the greatest nonpositive disagreement row to row zero places a full agreeing
strip directly above a disagreement. Lemma 5.6 (`lem:strip-states`). -/
theorem shift_at_greatest_disagreement {A : Type*} (x y : Configuration A)
    (W : ℕ) (b : ℤ)
    (hagree : ∀ z : Lattice, 1 ≤ z.2 → z.2 ≤ W → x z = y z)
    (hne : ∃ i s : ℤ, b ≤ s ∧ s ≤ 0 ∧ x (i, s) ≠ y (i, s)) :
    ∃ s : ℤ, b ≤ s ∧ s ≤ 0 ∧
      (∀ z : Lattice, 1 ≤ z.2 → z.2 ≤ W → shift (0, s) x z = shift (0, s) y z) ∧
      ∃ i : ℤ, shift (0, s) x (i, 0) ≠ shift (0, s) y (i, 0) := by
  classical
  let D : Finset ℤ := (Finset.Icc b 0).filter (fun s => ∃ i : ℤ, x (i, s) ≠ y (i, s))
  have hD : D.Nonempty := by
    obtain ⟨i, s, hb, hs, hneq⟩ := hne
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hb, hs⟩, i, hneq⟩⟩
  obtain ⟨s, hsD, hmax⟩ := Finset.exists_max_image D id hD
  obtain ⟨hsband, i, hi⟩ := Finset.mem_filter.mp hsD
  obtain ⟨hbs, hs0⟩ := Finset.mem_Icc.mp hsband
  refine ⟨s, hbs, hs0, ?_, i, ?_⟩
  · rintro ⟨r, j⟩ hj hjW
    change x (r + 0, j + s) = y (r + 0, j + s)
    by_cases hp : 1 ≤ j + s
    · exact hagree (r + 0, j + s) hp (by omega)
    · by_contra hbad
      have hjs : j + s ∈ D := Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, r + 0, hbad⟩
      have := hmax (j + s) hjs
      dsimp only [id] at this
      omega
  · simpa only [shift_apply, Prod.mk_add_mk, add_zero, zero_add] using hi

/-- Either a positive integer multiple of the transverse step is a global period, or two
translates agree on the whole strip, disagree on its lower boundary, and have a horizontally
periodic difference. Their relative translation remains an integer multiple of the
transverse step. Lemma 5.6 (`lem:strip-states`). -/
theorem finite_strip_dichotomy {A : Type*} [AddCommGroup A]
    (c : Configuration A) (hc : FiniteRange c) (q W : ℕ) (hq : 0 < q)
    (a M : ℤ) (hM : 0 < M) (hMW : M ≤ W)
    (hmix : difference ((q : ℤ), 0) (difference (a, M) c) = 0) :
    (∃ p : ℕ, 0 < p ∧ IsPeriod c (p • (a, M))) ∨
    ∃ u v : Lattice,
      (∀ z : Lattice, 1 ≤ z.2 → z.2 ≤ W → shift u c z = shift v c z) ∧
      (∃ i : ℤ, shift u c (i, 0) ≠ shift v c (i, 0)) ∧
      IsPeriod (shift u c - shift v c) ((q : ℤ), 0) ∧
      ∃ k : ℤ, v - u = k • (a, M) := by
  classical
  by_cases hpred : ∀ j k : ℤ,
      stripState c W (a, M) j = stripState c W (a, M) k →
      stripState c W (a, M) (j - 1) = stripState c W (a, M) (k - 1)
  · obtain ⟨p, hp, hper⟩ := periodic_of_deterministic_predecessor
      (stripState c W (a, M)) (finite_stripState_range c hc q W hq (a, M) hmix) hpred
    exact Or.inl ⟨p, hp, global_period_of_stripState_period c W a M hM hMW p hper⟩
  · push Not at hpred
    obtain ⟨j, k, hcurrent, hprevious⟩ := hpred
    let x := shift (j • (a, M)) c
    let y := shift (k • (a, M)) c
    have hagree : ∀ z : Lattice, 1 ≤ z.2 → z.2 ≤ W → x z = y z := by
      intro z hlo hhi
      exact congrFun hcurrent (⟨z, hlo, hhi⟩ : Strip W)
    obtain ⟨z, hz⟩ : ∃ z : Strip W,
        stripState c W (a, M) (j - 1) z ≠ stripState c W (a, M) (k - 1) z := by
      by_contra! h
      exact hprevious (funext h)
    let w : Lattice := z.val - (a, M)
    have hwne : x w ≠ y w := by
      simpa [x, y, w, stripState, shift_apply, sub_zsmul, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm, add_mul] using hz
    have hwlo : 1 - M ≤ w.2 := by
      have hzlo := z.property.1
      dsimp [w]
      omega
    have hwhi : w.2 ≤ W := by
      have hzhi := z.property.2
      dsimp [w]
      omega
    have hw0 : w.2 ≤ 0 := by
      by_contra! hpos
      exact hwne (hagree w (by omega) hwhi)
    obtain ⟨s, hslo, hs0, hstrip, i, hboundary⟩ :=
      shift_at_greatest_disagreement x y W (1 - M) hagree
        ⟨w.1, w.2, hwlo, hw0, hwne⟩
    let u : Lattice := (0, s) + j • (a, M)
    let v : Lattice := (0, s) + k • (a, M)
    refine Or.inr ⟨u, v, ?_, ?_, ?_, ?_⟩
    · simpa only [u, v, shift_add] using hstrip
    · exact ⟨i, by simpa only [u, v, shift_add] using hboundary⟩
    · have hd := (isPeriod_shift_iff (x - y) ((q : ℤ), 0) (0, s)).mpr
        (translate_difference_periodic c ((q : ℤ), 0) (a, M) hmix j k)
      intro z
      simpa only [u, v, x, y, shift_apply, Pi.sub_apply, add_assoc] using hd z
    · refine ⟨k - j, ?_⟩
      dsimp only [u, v]
      rw [sub_zsmul]
      abel

end Nivat.TwoFactors
