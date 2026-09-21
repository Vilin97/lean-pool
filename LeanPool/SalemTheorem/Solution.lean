/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
/-
Solution: proofs of the challenge statements, transferred from the
bridge module SalemPisot — the Pisot-number form, and the assemblies of
PdtSalemEndgame (the main construction) and PdtSalemQuadUnit (the
reciprocal quadratic case) re-run there with the index and the family
root kept. The inline Salem block is definitionally
PDT.SalemEndgame.IsSalem; the inline product is definitionally
PDT.SalemCircle.P.
-/
import LeanPool.SalemTheorem.SalemPisot

/-! Completed statement bridges for Salem’s theorem. -/

namespace SalemTheorem

open Polynomial

/-- **Salem's theorem** for Pisot numbers: transported through the
pattern data of `minpoly ℤ α`. -/
theorem salem_theorem
    (alpha : ℝ) (halpha : 1 < alpha) (hint : IsIntegral ℤ alpha)
    (hpisot : ∀ z ∈ (minpoly ℚ alpha).aroots ℂ, z ≠ (alpha : ℂ) → ‖z‖ < 1)
    (eps : ℝ) (heps : 0 < eps) :
    (∃ tau : ℝ,
      (1 < tau ∧ IsIntegral ℤ tau ∧
        (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
          z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
        (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
      alpha - eps < tau ∧ tau < alpha) ∧
    (∃ tau : ℝ,
      (1 < tau ∧ IsIntegral ℤ tau ∧
        (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
          z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
        (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
      alpha < tau ∧ tau < alpha + eps) :=
  PDT.SalemPisot.salem_theorem alpha halpha hint hpisot eps heps

/-- **The main construction, with its family root.** -/
theorem salem_construction_two_sided
    (P : Polynomial ℤ) (hmonic : P.Monic)
    (alpha : ℝ) (halpha : 1 < alpha)
    (inside : Multiset ℂ) (hin : ∀ z ∈ inside, ‖z‖ < 1)
    (hconj : inside.map (starRingEnd ℂ) = inside)
    (hfac : P.map (Int.castRingHom ℂ)
      = (X - C (alpha : ℂ)) * (inside.map fun z => X - C z).prod)
    (hnd : (P.map (Int.castRingHom ℝ)).eval alpha⁻¹ ≠ 0)
    (eps : ℝ) (heps : 0 < eps) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧
      0 < (e : ℝ) * (P.map (Int.castRingHom ℝ)).eval alpha⁻¹ ∧
      (∃ m : ℕ, 2 ≤ m ∧ ∃ tau : ℝ,
        (1 < tau ∧ IsIntegral ℤ tau ∧
          (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
            z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
          (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
          (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
        ((X ^ m * P + C e * P.reverse).map (Int.castRingHom ℝ)).eval tau = 0 ∧
        alpha - eps < tau ∧ tau < alpha) ∧
      (∃ m : ℕ, 2 ≤ m ∧ ∃ tau : ℝ,
        (1 < tau ∧ IsIntegral ℤ tau ∧
          (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
            z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
          (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
          (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
        ((X ^ m * P - C e * P.reverse).map (Int.castRingHom ℝ)).eval tau = 0 ∧
        alpha < tau ∧ tau < alpha + eps) :=
  PDT.SalemPisot.salem_construction_two_sided P hmonic alpha halpha inside hin hconj
    hfac hnd eps heps

/-- **The reciprocal quadratic case, with its family root.** -/
theorem salem_quadratic_unit
    (r : ℤ) (hr : 3 ≤ r)
    (alpha : ℝ) (halpha : 1 < alpha)
    (hmin : alpha ^ 2 = (r : ℝ) * alpha - 1)
    (eps : ℝ) (heps : 0 < eps) :
    (∃ m : ℕ, 1 ≤ m ∧ ∃ tau : ℝ,
      (1 < tau ∧ IsIntegral ℤ tau ∧
        (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
          z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
        (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
      (((X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) + X ^ (m + 1) : Polynomial ℤ).map
        (Int.castRingHom ℝ)).eval tau = 0 ∧
      alpha - eps < tau ∧ tau < alpha) ∧
    (∃ m : ℕ, 1 ≤ m ∧ ∃ tau : ℝ,
      (1 < tau ∧ IsIntegral ℤ tau ∧
        (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 →
          z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
        (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0) ∧
      (((X ^ 2 - C r * X + 1) * (X ^ (2 * m) + 1) - X ^ (m + 1) : Polynomial ℤ).map
        (Int.castRingHom ℝ)).eval tau = 0 ∧
      alpha < tau ∧ tau < alpha + eps) :=
  PDT.SalemPisot.salem_quadratic_unit r hr alpha halpha hmin eps heps

end SalemTheorem

/-! ### Axiom audit — every build prints the audit for the compared theorems -/




/-
Upstream license notice:
MIT License

Copyright (c) 2026 Stephanie Alexander

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
