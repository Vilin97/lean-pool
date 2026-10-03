/-
Copyright (c) 2026 Avik Das. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Avik Das
-/
module

/-
Copyright (c) 2026 adas1236. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: adas1236
-/
public import LeanPool.KaltonPeck.KaltonPeck.Support.Symplectic

/-!
# Canonical symplectic pairing identities

The unrestricted coordinate formula gives the pairing identities for the canonical
Hilbert-space inclusion directly.
-/

public section


namespace KaltonPeck.Support.Symplectic

noncomputable
section

open Coordinates
open Filter
open scoped lp Topology

/-- The canonical form pairs the first-coordinate inclusion with the quotient by the
real Hilbert inner product. -/
theorem canonicalKaltonSwansonForm_inclusion_left
    (x : CanonicalL2) (z : CanonicalRealKaltonPeck) :
    canonicalKaltonSwansonForm.toDual (canonicalL2Inclusion x) z =
      inner ℝ x (canonicalL2Quotient z) := by
  rw [canonicalKaltonSwansonForm_coordinates, canonicalL2Inclusion_coordinates,
    lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [RCLike.inner_apply, conj_trivial, canonicalL2Quotient_apply,
    Pi.zero_apply, mul_zero, sub_zero]
  ring

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
