/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.TwoFactors.BoundaryCounting

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
# Ambiguous boundaries and a common interior period

Lemma 5.7 (`lem:periodic-interior`) of `paper/nivat.tex`. A forward boundary
rule propagates agreement to a right half-line. Periodicity of the difference
then rules out agreement on any complete boundary edge. Counting the resulting
ambiguous extensions bounds the complexity of a word whose letters collect
all the interior rows; Morse–Hedlund gives one period for those rows.
-/

public section

namespace Nivat.TwoFactors

/-- An agreeing boundary block extends indefinitely to the right when the next value is
determined by the preceding `k` agreeing letters. Lemma 5.7 (`lem:periodic-interior`). -/
theorem agreement_extends_right {A : Type*} (a b : ℤ → A) (k e : ℕ) (hke : k < e)
    (hrule : ∀ i : ℤ, (∀ r : Fin k, a (i + (r : ℕ)) = b (i + (r : ℕ))) →
      a (i + k) = b (i + k)) (i : ℤ)
    (hinit : ∀ r : Fin e, a (i + (r : ℕ)) = b (i + (r : ℕ))) :
    ∀ n : ℕ, a (i + n) = b (i + n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hne : n < e
    · exact hinit ⟨n, hne⟩
    · have hkn : k ≤ n := by omega
      have hm := hrule (i + ((n - k : ℕ) : ℤ)) (by
        intro r
        have hr := r.isLt
        have hnr : n - k + (r : ℕ) < n := by omega
        convert ih (n - k + (r : ℕ)) hnr using 1 <;> push_cast <;> congr 1 <;> omega)
      convert hm using 1 <;> congr 1 <;> omega

/-- A periodic difference that vanishes on a right half-line vanishes at every integer index.
Lemma 5.7 (`lem:periodic-interior`). -/
theorem periodic_zero_of_right_ray {G : Type*} [AddGroup G]
    (d : ℤ → G) (q : ℕ) (hq : 0 < q) (hp : Function.Periodic d (q : ℤ))
    (i : ℤ) (hz : ∀ n : ℕ, d (i + n) = 0) : ∀ j, d j = 0 := by
  intro j
  let r : ℤ := (j - i) % q
  have hr : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hcast : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr
  have hj : d (i + r) = d j := by
    have ht := hp.int_mul ((j - i) / q) (i + r)
    have he : i + r + (j - i) / q * q = j := by
      dsimp [r]
      have h := Int.emod_add_ediv_mul (j - i) q
      omega
    simpa only [Int.cast_id, he] using ht.symm
  rw [← hj, ← hcast]
  exact hz r.toNat

/-- The occurring-pattern boundary rule holds for every translate of the configuration, because
translating both test positions preserves the rule. Lemma 5.8 (`lem:row-lifting`). -/
theorem boundaryRule_shift {A : Type*} (c : Configuration A) (C : Finset Lattice)
    (k : ℕ) (hr : BoundaryRule c C k) (u : Lattice) : BoundaryRule (shift u c) C k := by
  intro z z' hC hmem
  have hc : ∀ v ∈ C, c (v + (z + u)) = c (v + (z' + u)) := by
    simpa [shift, add_assoc] using hC
  have hm : ∀ r : Fin k,
      c ((z + u) + (((r : ℕ) : ℤ), 0)) = c ((z' + u) + (((r : ℕ) : ℤ), 0)) := by
    simpa [shift, add_assoc, add_comm, add_left_comm] using hmem
  simpa [shift, add_assoc, add_comm, add_left_comm] using hr (z + u) (z' + u) hc hm

/-- Two translates with agreeing interiors and a nonzero periodic boundary difference cannot
agree on any complete translated boundary edge: agreement would propagate to a half-line and
then to the whole boundary. Lemma 5.7 (`lem:periodic-interior`). -/
theorem every_edge_differs (c : Configuration ℚ) (C : Finset Lattice) (k e q : ℕ)
    (hke : k < e) (hq : 0 < q) (hrule : BoundaryRule c C k) (u v : Lattice)
    (hinner : ∀ i : ℤ, patternAt (shift u c) C (i, 0) =
      patternAt (shift v c) C (i, 0))
    (hperiod : IsPeriod (shift u c - shift v c) ((q : ℤ), 0))
    (hne : ∃ i : ℤ, shift u c (i, 0) ≠ shift v c (i, 0)) :
    ∀ i : ℤ, patternAt (shift u c) (rowPrefix e) (i, 0) ≠
      patternAt (shift v c) (rowPrefix e) (i, 0) := by
  intro i hi
  let a : ℤ → ℚ := fun j => shift u c (j, 0)
  let b : ℤ → ℚ := fun j => shift v c (j, 0)
  have hinit : ∀ r : Fin e, a (i + (r : ℕ)) = b (i + (r : ℕ)) := by
    intro r
    have hsite : (((r : ℕ) : ℤ), (0 : ℤ)) ∈ rowPrefix e :=
      (mem_rowPrefix _ _).mpr ⟨r, r.isLt, rfl⟩
    simpa [a, b, patternAt, add_comm] using congrFun hi ⟨_, hsite⟩
  have hstep : ∀ j : ℤ, (∀ r : Fin k, a (j + (r : ℕ)) = b (j + (r : ℕ))) →
      a (j + k) = b (j + k) := by
    intro j hj
    have hC : ∀ w ∈ C, c (w + ((j, 0) + u)) = c (w + ((j, 0) + v)) := by
      intro w hw
      simpa [patternAt, shift, add_assoc] using congrFun (hinner j) ⟨w, hw⟩
    have hm : ∀ r : Fin k, c (((j, 0) + u) + (((r : ℕ) : ℤ), 0)) =
        c (((j, 0) + v) + (((r : ℕ) : ℤ), 0)) := by
      simpa [a, b, shift, add_assoc, add_comm, add_left_comm] using hj
    simpa [a, b, shift, add_assoc, add_comm, add_left_comm] using
      hrule ((j, 0) + u) ((j, 0) + v) hC hm
  have hray := agreement_extends_right a b k e hke hstep i hinit
  have hdper : Function.Periodic (fun j => a j - b j) (q : ℤ) := by
    intro j
    simpa [a, b, Prod.mk_add_mk] using hperiod (j, 0)
  have hall := periodic_zero_of_right_ray (fun j => a j - b j) q hq hdper i
    (fun n => sub_eq_zero.mpr (hray n))
  obtain ⟨j, hj⟩ := hne
  exact hj (sub_eq_zero.mp (hall j))

/-- The interior patterns encountered by translating one configuration in the horizontal basis
direction. Lemma 5.7 (`lem:periodic-interior`). -/
@[expose] def innerOrbit {A : Type*} (x : Configuration A) (C : Finset Lattice) : Set (C → A) :=
  Set.range (fun i : ℤ => patternAt x C (i, 0))

/-- The horizontal interior orbit is finite because it is a subset of the patterns of a
finite-range configuration on a finite window. Lemma 5.7 (`lem:periodic-interior`). -/
theorem innerOrbit_finite {A : Type*} {x : Configuration A} (hx : FiniteRange x)
    (C : Finset Lattice) : (innerOrbit x C).Finite := by
  apply (patterns_finite hx C).subset
  rintro p ⟨i, rfl⟩
  exact ⟨(i, 0), rfl⟩

/-- When every horizontally translated edge differs but the interiors agree, each encountered
interior pattern has two boundary extensions, so their number is bounded by the total
boundary cost. Lemma 5.7 (`lem:periodic-interior`). -/
theorem innerOrbit_budget {A : Type*} (c : Configuration A) (hc : FiniteRange c)
    (C : Finset Lattice) (e : ℕ) (u v : Lattice)
    (hinner : ∀ i : ℤ, patternAt (shift u c) C (i, 0) =
      patternAt (shift v c) C (i, 0))
    (hedge : ∀ i : ℤ, patternAt (shift u c) (rowPrefix e) (i, 0) ≠
      patternAt (shift v c) (rowPrefix e) (i, 0)) :
    (innerOrbit (shift u c) C).ncard + complexity c C ≤ complexity c (prefixWindow C e) := by
  let B := prefixWindow C e
  have hCB : C ⊆ B := Finset.subset_union_left
  have hb := ambiguous_output_budget (restrictPattern hCB) (patterns_finite hc B)
    (Q := innerOrbit (shift u c) C) (by
      rintro p ⟨i, rfl⟩
      refine ⟨patternAt c B ((i, 0) + u), ⟨_, rfl⟩,
        patternAt c B ((i, 0) + v), ⟨_, rfl⟩, ?_, ?_, ?_⟩
      · intro heq
        apply hedge i
        funext z
        have hz : z.1 ∈ B := Finset.mem_union_right C z.2
        simpa [patternAt, shift, add_assoc] using congrFun heq ⟨z.1, hz⟩
      · funext z
        simp [restrictPattern, patternAt, shift, add_assoc]
      · funext z
        have hz := congrFun (hinner i).symm z
        simpa [restrictPattern, patternAt, shift, add_assoc] using hz)
  rw [restrict_patterns] at hb
  exact hb

/-- Collecting one staggered coordinate from each interior row gives a finite-alphabet word
whose length-`r` complexity is at most `r`; Morse–Hedlund supplies one period for every
entire interior row. Lemma 5.7 (`lem:periodic-interior`). -/
theorem common_inner_period {A : Type*} (x : Configuration A) (hx : FiniteRange x)
    (C : Finset Lattice) (H r : ℕ) (hr : 0 < r) (α : Fin H → ℤ)
    (hblocks : ∀ j : Fin H, ∀ t : Fin r,
      (α j + (t : ℕ), ((j : ℕ) : ℤ) + 1) ∈ C)
    (hcount : (innerOrbit x C).ncard ≤ r) :
    ∃ p : ℕ, 0 < p ∧ p ≤ r ∧ ∀ j : Fin H,
      Function.Periodic (fun i : ℤ => x (i, ((j : ℕ) : ℤ) + 1)) (p : ℤ) := by
  let a : ℤ → (Fin H → A) := fun i j => x (α j + i, ((j : ℕ) : ℤ) + 1)
  have ha : (Set.range a).Finite := by
    apply (Set.Finite.pi' (fun _ : Fin H => hx)).subset
    rintro b ⟨i, rfl⟩ j
    exact ⟨_, rfl⟩
  let F : (C → A) → (Fin r → Fin H → A) :=
    fun p t j => p ⟨(α j + (t : ℕ), ((j : ℕ) : ℤ) + 1), hblocks j t⟩
  have himage : F '' innerOrbit x C = Set.range (word a r) := by
    ext b
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      funext t j
      simp [F, word, a, patternAt, add_comm, add_left_comm]
    · rintro ⟨i, rfl⟩
      refine ⟨patternAt x C (i, 0), ⟨i, rfl⟩, ?_⟩
      funext t j
      simp [F, word, a, patternAt, add_comm, add_left_comm]
  have hword : wordComplexity a r ≤ r := by
    unfold wordComplexity
    rw [← himage]
    exact (Set.ncard_image_le (innerOrbit_finite hx C)).trans hcount
  obtain ⟨p, hp, hpr, hper⟩ := morse_hedlund a ha r hr hword
  refine ⟨p, hp, hpr, ?_⟩
  intro j i
  have h := congrFun (hper (i - α j)) j
  simpa [a, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h

end Nivat.TwoFactors
