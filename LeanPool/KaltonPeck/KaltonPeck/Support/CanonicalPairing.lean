/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
import LeanPool.KaltonPeck.KaltonPeck.Support.Symplectic

/-!
# Canonical symplectic pairing identities

This file extends the finite-coordinate formulas for the canonical Kalton--Swanson form to
pairings with the canonical Hilbert-space inclusion.
-/


namespace KaltonPeck.Support.Symplectic

noncomputable section

open Coordinates
open Filter
open scoped lp Topology

private def pairingL2Trunc (m : ℕ) (x : CanonicalL2) : CanonicalL2 :=
  ∑ k ∈ Finset.range m, lp.single 2 k (x k)

private lemma pairingL2Trunc_apply (m k : ℕ) (x : CanonicalL2) :
    pairingL2Trunc m x k = if k < m then x k else 0 := by
  rw [pairingL2Trunc]
  change
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k)
        (∑ i ∈ Finset.range m, lp.single 2 i (x i)) =
      if k < m then x k else 0
  rw [map_sum]
  simp [lp.evalCLM, lp.single_apply, Pi.single_apply]

private lemma pairingL2Trunc_tendsto (x : CanonicalL2) :
    Tendsto (fun m => pairingL2Trunc m x) atTop (𝓝 x) :=
  (lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) x).tendsto_sum_nat

private lemma pairingL2Trunc_finite (m : ℕ) (x : CanonicalL2) :
    Set.Finite {k | pairingL2Trunc m x k ≠ 0} := by
  refine (Finset.finite_toSet (Finset.range m)).subset ?_
  intro k hk
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_range] at hk ⊢
  by_contra hkm
  rw [pairingL2Trunc_apply, if_neg hkm] at hk
  exact hk rfl

private lemma dense_pairingL2_finiteSupport :
    Dense {x : CanonicalL2 | Set.Finite {n | x n ≠ 0}} := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  exact mem_closure_of_tendsto (pairingL2Trunc_tendsto x)
    (Eventually.of_forall fun m => pairingL2Trunc_finite m x)

/-- The canonical form pairs the first-coordinate inclusion with the quotient by the
real Hilbert inner product. -/
theorem canonicalKaltonSwansonForm_inclusion_left
    (x : CanonicalL2) (z : CanonicalRealKaltonPeck) :
    canonicalKaltonSwansonForm.toDual (canonicalL2Inclusion x) z =
      inner ℝ x (canonicalL2Quotient z) := by
  let DX : Set CanonicalL2 := {u | Set.Finite {n | u n ≠ 0}}
  let DZ : Set CanonicalRealKaltonPeck :=
    {w | IsFiniteCoordinatePair (canonicalRealKaltonPeckPresentation.coordinates w)}
  have hDX : Dense DX := dense_pairingL2_finiteSupport
  have hDZ : Dense DZ := canonicalKaltonPeckBanach.2.2.2
  have hfinite : ∀ u ∈ DX, ∀ w ∈ DZ,
      canonicalKaltonSwansonForm.toDual (canonicalL2Inclusion u) w =
        inner ℝ u (canonicalL2Quotient w) := by
    intro u hu w hw
    have hiu : IsFiniteCoordinatePair
        (canonicalRealKaltonPeckPresentation.coordinates (canonicalL2Inclusion u)) := by
      rw [canonicalL2Inclusion_coordinates]
      exact ⟨hu, by simp⟩
    rw [canonicalKaltonSwansonForm_finite_coordinates _ _ hiu hw,
      canonicalL2Inclusion_coordinates, lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    simp only [RCLike.inner_apply, conj_trivial, canonicalL2Quotient_apply,
      Pi.zero_apply, mul_zero, sub_zero]
    ring
  refine eqOn_closure₂' hfinite ?_ ?_ ?_ ?_ x (hDX x) z (hDZ z)
  · intro u
    exact (canonicalKaltonSwansonForm.toDual (canonicalL2Inclusion u)).continuous
  · intro w
    exact Continuous.clm_apply
      (canonicalKaltonSwansonForm.toDual.continuous.comp canonicalL2Inclusion.continuous)
      continuous_const
  · intro u
    exact continuous_const.inner canonicalL2Quotient.continuous
  · intro w
    exact continuous_id.inner continuous_const

/-- The same pairing identity in the opposite order; alternation supplies the minus sign. -/
theorem canonicalKaltonSwansonForm_inclusion_right
    (z : CanonicalRealKaltonPeck) (x : CanonicalL2) :
    canonicalKaltonSwansonForm.toDual z (canonicalL2Inclusion x) =
      -inner ℝ (canonicalL2Quotient z) x := by
  have hskew :
      canonicalKaltonSwansonForm.toDual z (canonicalL2Inclusion x) =
        -canonicalKaltonSwansonForm.toDual (canonicalL2Inclusion x) z := by
    have h := canonicalKaltonSwansonForm.alternating (z + canonicalL2Inclusion x)
    simp only [map_add, add_apply, canonicalKaltonSwansonForm.alternating,
      add_zero, zero_add] at h
    linarith
  rw [hskew, canonicalKaltonSwansonForm_inclusion_left]
  congr 1
  exact (real_inner_comm x (canonicalL2Quotient z)).symm

end

end KaltonPeck.Support.Symplectic

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Avik Das

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

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
