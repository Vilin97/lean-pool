/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Core.Basic
public import LeanPool.Nivat.TwoFactors.FiniteState
public import Mathlib.Algebra.Ring.Periodic
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
# Extending horizontal periodicity across rows

Lemma 5.8 (`lem:row-lifting`) of `paper/nivat.tex`. The boundary rule from
Lemma 5.5 supplies the recurrence in Lemma 5.4. It makes finitely many further
rows periodic. A common multiple of those row periods and the horizontal
mixed-difference direction gives a difference vanishing on a full transverse
fundamental strip; its transverse period then makes it vanish everywhere.
-/

@[expose] public section

namespace Nivat.TwoFactors

/-- A row has a positive integer period in the horizontal basis direction. Lemma 5.8
(`lem:row-lifting`). -/
def RowPeriodic {A : Type*} (x : ℤ × ℤ → A) (j : ℤ) : Prop :=
  ∃ p : ℕ, 0 < p ∧ Function.Periodic (fun i : ℤ => x (i, j)) (p : ℤ)

/-- Equal occurring interior patterns and equal first `k` boundary values determine the next
boundary value, the rule in equation `eq:boundary-rule`. Lemma 5.5 (`lem:boundary-window`). -/
def BoundaryRule {A : Type*} (x : ℤ × ℤ → A) (C : Finset (ℤ × ℤ)) (k : ℕ) : Prop :=
  ∀ z z' : ℤ × ℤ,
    (∀ u ∈ C, x (u + z) = x (u + z')) →
    (∀ r : Fin k, x (z + (((r : ℕ) : ℤ), 0)) = x (z' + (((r : ℕ) : ℤ), 0))) →
    x (z + ((k : ℤ), 0)) = x (z' + ((k : ℤ), 0))

/-- A finite family of periodic bilateral words has a common positive period, obtained by
multiplying their periods. Lemma 5.8 (`lem:row-lifting`). -/
theorem common_period_of_finite {A ι : Type*} (s : Finset ι) (f : ι → ℤ → A)
    (h : ∀ i ∈ s, ∃ p : ℕ, 0 < p ∧ Function.Periodic (f i) (p : ℤ)) :
    ∃ p : ℕ, 0 < p ∧ ∀ i ∈ s, Function.Periodic (f i) (p : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by omega, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨p, hp, hpi⟩ := h i (by simp)
    obtain ⟨q, hq, hqs⟩ := ih (fun j hj => h j (by simp [hj]))
    refine ⟨p * q, Nat.mul_pos hp hq, ?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simpa [Nat.cast_mul, mul_comm] using hpi.nat_mul q
    · simpa [Nat.cast_mul] using (hqs j hj).nat_mul p

/-- A configuration periodic by `(a,M)`, with `M > 0`, that is constant on any `M` consecutive
rows is constant everywhere: division with remainder moves every point into those rows.
Lemma 5.8 (`lem:row-lifting`). -/
theorem eq_const_of_periodic_of_strip {A : Type*} (d : ℤ × ℤ → A)
    (a M b : ℤ) (hM : 0 < M) (ht : Function.Periodic d (a, M)) (s : A)
    (hz : ∀ i j : ℤ, b ≤ j → j < b + M → d (i, j) = s) :
    ∀ z, d z = s := by
  intro z
  let n : ℤ := (z.2 - b) / M
  let w : ℤ × ℤ := z - n • (a, M)
  have hw : w.2 = b + (z.2 - b) % M := by
    dsimp [w, n]
    have he := Int.emod_add_mul_ediv (z.2 - b) M
    nlinarith
  have hlo : b ≤ w.2 := by
    rw [hw]
    have := Int.emod_nonneg (z.2 - b) (ne_of_gt hM)
    omega
  have hhi : w.2 < b + M := by
    rw [hw]
    have := Int.emod_lt_of_pos (z.2 - b) hM
    omega
  calc
    d z = d w := (ht.sub_zsmul_eq n).symm
    _ = s := hz w.1 w.2 hlo hhi

/-- A property determined by the next `H` rows propagates downward through any prescribed finite
number of rows. Lemma 5.8 (`lem:row-lifting`). -/
theorem propagate_rows_downward (P : ℤ → Prop) (H : ℕ)
    (hinit : ∀ j : ℤ, 1 ≤ j → j ≤ H → P j)
    (hstep : ∀ j : ℤ, (∀ r : ℤ, 1 ≤ r → r ≤ H → P (j + r)) → P j) :
    ∀ n : ℕ, ∀ j : ℤ, -(n : ℤ) < j → j ≤ H → P j := by
  intro n
  induction n with
  | zero =>
    intro j hj hH
    apply hinit j (by omega) hH
  | succ n ih =>
    intro j hj hH
    by_cases hj' : -(n : ℤ) < j
    · exact ih j hj' hH
    · have heq : j = -(n : ℤ) := by omega
      apply hstep j
      intro r hr hrH
      apply ih (j + r) <;> omega

/-- If each of the finitely many rows supporting the translated interior pattern is periodic,
their common period makes that pattern a periodic parameter. Lemma 5.8 (`lem:row-lifting`). -/
theorem interior_forcing_periodic {A : Type*} (x : ℤ × ℤ → A)
    (C : Finset (ℤ × ℤ)) (j : ℤ)
    (hrows : ∀ u ∈ C, RowPeriodic x (j + u.2)) :
    ∃ p : ℕ, 0 < p ∧
      Function.Periodic (fun i : ℤ => fun u : C => x (u.val + (i, j))) (p : ℤ) := by
  obtain ⟨p, hp, hper⟩ := common_period_of_finite C
    (fun u i => x (u + (i, j))) (by
      intro u hu
      obtain ⟨p, hp, hrow⟩ := hrows u hu
      refine ⟨p, hp, ?_⟩
      rcases u with ⟨a, b⟩
      simpa [Prod.mk_add_mk, add_comm] using hrow.add_const a)
  refine ⟨p, hp, ?_⟩
  intro i
  funext u
  exact hper u.val u.property i

/-- A boundary row is periodic when its interior rows are periodic: the boundary rule and
interior parameter satisfy the periodic-forcing lemma, including zero memory. Lemma 5.8
(`lem:row-lifting`), using Lemma 5.4 (`lem:forcing`). -/
theorem rowPeriodic_of_boundaryRule {A : Type*} (x : ℤ × ℤ → A)
    (hx : (Set.range x).Finite) (C : Finset (ℤ × ℤ)) (k : ℕ)
    (hrule : BoundaryRule x C k) (j : ℤ)
    (hrows : ∀ u ∈ C, RowPeriodic x (j + u.2)) : RowPeriodic x j := by
  obtain ⟨p, hp, hf⟩ := interior_forcing_periodic x C j hrows
  let a : ℤ → A := fun i => x (i, j)
  let f : ℤ → (C → A) := fun i u => x (u.val + (i, j))
  have ha : (Set.range a).Finite := hx.subset (by
    rintro v ⟨i, rfl⟩
    exact ⟨(i, j), rfl⟩)
  apply periodic_of_periodic_forcing a f ha p k hp hf
  intro i l heq hprev
  have hC : ∀ u ∈ C, x (u + (i, j)) = x (u + (l, j)) := by
    intro u hu
    exact congrFun heq ⟨u, hu⟩
  have hmem : ∀ r : Fin k,
      x ((i, j) + (((r : ℕ) : ℤ), 0)) =
        x ((l, j) + (((r : ℕ) : ℤ), 0)) := by
    intro r
    simpa [a, Prod.mk_add_mk] using hprev r
  simpa [a, Prod.mk_add_mk] using hrule (i, j) (l, j) hC hmem

/-- A vanishing mixed difference implies that the difference in a multiple of the first
direction still has the second direction as a period. Commutation and multiples of a period
give the operator consequence of equation `eq:telescoping-lift`. Lemma 5.8 (`lem:row-lifting`). -/
theorem difference_multiple_period {A : Type*} [AddCommGroup A]
    (x : Configuration A) (h t : Lattice)
    (hmix : difference h (difference t x) = 0) (n : ℕ) :
    IsPeriod (difference (n • h) x) t := by
  apply (difference_eq_zero_iff t _).mp
  rw [← difference_comm (n • h) t x]
  apply (difference_eq_zero_iff (n • h) _).mpr
  exact ((difference_eq_zero_iff h _).mp hmix).nsmul n

/-- A boundary rule and periodic initial interior rows yield a global horizontal period that is
a positive multiple of the supplied horizontal direction. Only finitely many row periods are
combined; the transverse mixed difference extends their common multiple across the plane.
Lemma 5.8 (`lem:row-lifting`). -/
theorem periodic_of_rows_boundaryRule (x : Configuration ℚ) (hx : FiniteRange x)
    (C : Finset Lattice) (k H : ℕ) (_hH : 0 < H)
    (hC : ∀ u ∈ C, 1 ≤ u.2 ∧ u.2 ≤ H) (hrule : BoundaryRule x C k)
    (q : ℕ) (_hq : 0 < q) (a M : ℤ) (hM : 0 < M)
    (hmix : difference ((q : ℤ), 0) (difference (a, M) x) = 0)
    (hrows : ∀ j : ℤ, 1 ≤ j → j ≤ H → RowPeriodic x j) :
    ∃ L : ℕ, 0 < L ∧ IsPeriod x (((L * q : ℕ) : ℤ), 0) := by
  have hall := propagate_rows_downward (RowPeriodic x) H hrows (by
    intro j hup
    apply rowPeriodic_of_boundaryRule x hx C k hrule j
    intro u hu
    exact hup u.2 (hC u hu).1 (hC u hu).2)
  let b : ℤ := (H : ℤ) - M + 1
  have hband : ∀ j ∈ Finset.Icc b (H : ℤ), RowPeriodic x j := by
    intro j hj
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hj
    apply hall (M - (H : ℤ)).toNat j _ hhi
    dsimp [b] at hlo
    omega
  obtain ⟨p, hp, hper⟩ := common_period_of_finite (Finset.Icc b (H : ℤ))
    (fun j i => x (i, j)) hband
  refine ⟨p, hp, ?_⟩
  let d := difference (((p * q : ℕ) : ℤ), 0) x
  have ht : Function.Periodic d (a, M) := by
    change IsPeriod d (a, M)
    have h := difference_multiple_period x ((q : ℤ), 0) (a, M) hmix p
    simpa [d, Prod.smul_mk, nsmul_eq_mul, Nat.cast_mul] using h
  have hz : ∀ i j : ℤ, b ≤ j → j < b + M → d (i, j) = 0 := by
    intro i j hlo hhi
    have hj : j ∈ Finset.Icc b (H : ℤ) := by
      apply Finset.mem_Icc.mpr
      dsimp [b] at hhi
      constructor <;> omega
    have hpj := (hper j hj).nat_mul q i
    have heq : x (i + ((p * q : ℕ) : ℤ), j) = x (i, j) := by
      simpa [Nat.cast_mul, mul_comm] using hpj
    simpa [d, difference_apply, Prod.mk_add_mk] using sub_eq_zero.mpr heq
  apply (difference_eq_zero_iff (((p * q : ℕ) : ℤ), 0) x).mp
  funext z
  exact eq_const_of_periodic_of_strip d a M b hM ht 0 hz z

end Nivat.TwoFactors
