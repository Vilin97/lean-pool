/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.Comparison

/-!
# The finite-dimensional second-variation contradiction

This module contains the sign-critical core of the Bonnet--Myers argument.  It
does not call a geometric theorem by name: the hypotheses explicitly provide
the transverse test fields, their integrability, the curvature comparison, and
the nonnegativity of the index form for a minimizing segment.  The conclusion
is then a checked contradiction with the sine test.

The geometric work still needed by the entry is to construct these fields from
parallel transport along a minimizing geodesic and to prove the index-form
nonnegativity from the endpoint-minimizing property.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set
open MeasureTheory
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace BigOperators

namespace BonnetMyersEntry

/-! ### A pointwise version of the curvature comparison -/

lemma indexForm_le_sineIndexForm
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {A : ℝ → V →L[ℝ] V} {L q : ℝ} {e : V}
    (he : ‖e‖ = 1) (hL : 0 ≤ L)
    (hA : ∀ t ∈ Icc (0 : ℝ) L,
      q * inner ℝ (vectorSineTest L e t) (vectorSineTest L e t) ≤
        inner ℝ (vectorSineTest L e t)
          (A t (vectorSineTest L e t)))
    (hJ : IntervalIntegrable
      (fun t ↦ inner ℝ (vectorSineTest L e t) (vectorSineTest L e t))
      volume 0 L)
    (hAJ : IntervalIntegrable
      (fun t ↦ inner ℝ (vectorSineTest L e t)
        (A t (vectorSineTest L e t))) volume 0 L) :
    indexForm A (vectorSineTest L e) (vectorSineTestDeriv L e) L ≤
      sineIndexForm q L := by
  have hle := indexForm_le_of_curvature_lower (A := A)
    (J := vectorSineTest L e) (DJ := vectorSineTestDeriv L e)
    (K := q) (L := L) hL hA hJ hAJ
  have hnorm :
      (∫ t in (0 : ℝ)..L,
        inner ℝ (vectorSineTest L e t) (vectorSineTest L e t)) =
        ∫ t in (0 : ℝ)..L, sineTest L t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    change inner ℝ (sineTest L t • e) (sineTest L t • e) = _
    have he' : inner ℝ e e = 1 := by
      rw [real_inner_self_eq_norm_sq, he]
      norm_num
    rw [real_inner_smul_left, real_inner_smul_right, he']
    ring
  have hderiv :
      (∫ t in (0 : ℝ)..L,
        inner ℝ (vectorSineTestDeriv L e t)
          (vectorSineTestDeriv L e t)) =
        ∫ t in (0 : ℝ)..L, sineTestDeriv L t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    change inner ℝ (sineTestDeriv L t • e) (sineTestDeriv L t • e) = _
    have he' : inner ℝ e e = 1 := by
      rw [real_inner_self_eq_norm_sq, he]
      norm_num
    rw [real_inner_smul_left, real_inner_smul_right, he']
    ring
  calc
    indexForm A (vectorSineTest L e) (vectorSineTestDeriv L e) L ≤
        (∫ t in (0 : ℝ)..L,
          inner ℝ (vectorSineTestDeriv L e t)
            (vectorSineTestDeriv L e t)) -
          q * (∫ t in (0 : ℝ)..L,
            inner ℝ (vectorSineTest L e t)
              (vectorSineTest L e t)) := hle
    _ = (∫ t in (0 : ℝ)..L, sineTestDeriv L t ^ 2) -
          q * (∫ t in (0 : ℝ)..L, sineTest L t ^ 2) := by
      rw [hderiv, hnorm]
    _ = sineIndexForm q L := by rfl

/-! ### Summing the transverse test fields -/

theorem no_long_minimizing_segment_of_index_form
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {n : ℕ} (hn : 2 ≤ n) {A : ℝ → V →L[ℝ] V}
    {K L : ℝ} (hK : 0 < K)
    (hL : Real.pi / Real.sqrt K < L)
    (e : Fin n → V) (q : Fin n → ℝ)
    (hunit : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin n),
      ‖e i‖ = 1)
    (hA : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin n),
      ∀ t ∈ Icc (0 : ℝ) L,
      q i * inner ℝ (vectorSineTest L (e i) t)
          (vectorSineTest L (e i) t) ≤
        inner ℝ (vectorSineTest L (e i) t)
          (A t (vectorSineTest L (e i) t)))
    (hJ : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin n),
      IntervalIntegrable
        (fun t ↦ inner ℝ (vectorSineTest L (e i) t)
          (vectorSineTest L (e i) t)) volume 0 L)
    (hAJ : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin n),
      IntervalIntegrable
        (fun t ↦ inner ℝ (vectorSineTest L (e i) t)
          (A t (vectorSineTest L (e i) t))) volume 0 L)
    (hq : ((n - 1 : ℕ) : ℝ) * K ≤
      Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin n)) q)
    (hmin : ∀ i ∈ Finset.univ.erase (⟨0, by omega⟩ : Fin n),
      0 ≤ indexForm A (vectorSineTest L (e i))
        (vectorSineTestDeriv L (e i)) L) :
    False := by
  let s := Finset.univ.erase (⟨0, by omega⟩ : Fin n)
  have hL0 : 0 ≤ L := by
    exact le_of_lt (lt_trans (div_pos Real.pi_pos (Real.sqrt_pos.2 hK)) hL)
  have hsum_le :
      Finset.sum s (fun i ↦
        indexForm A (vectorSineTest L (e i))
          (vectorSineTestDeriv L (e i)) L) ≤
      Finset.sum s (fun i ↦ sineIndexForm (q i) L) := by
    apply Finset.sum_le_sum
    intro i hi
    exact indexForm_le_sineIndexForm (A := A) (L := L) (e := e i) (q := q i)
      (hunit i hi) hL0
      (hA i hi) (hJ i hi) (hAJ i hi)
  have hsum_nonneg :
      0 ≤ Finset.sum s (fun i ↦
        indexForm A (vectorSineTest L (e i))
          (vectorSineTestDeriv L (e i)) L) := by
    exact Finset.sum_nonneg (fun i hi ↦ hmin i hi)
  have hsum_neg :
      Finset.sum s (fun i ↦ sineIndexForm (q i) L) < 0 :=
    sum_sineIndexForm_negative hn hK hL q hq
  linarith

end BonnetMyersEntry
