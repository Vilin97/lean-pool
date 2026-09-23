/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Algebra.Action
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer

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
# Integer scaling for the product-annihilator theorem

Appendix A (`app:product`), proving Proposition 3.3 (`prop:product`), begins by
scaling the finite rational alphabet and the finite filter coefficients
separately. `finiteRange_integer_scale` and `integer_filter_scale` provide the
two nonzero multipliers. The map `intLaurentCast` changes only the coefficient
ring, so the resulting equations still concern the full integer lattice.
-/

@[expose] public section

namespace Nivat.Algebra

/-- The integer-coefficient Laurent ring used in Appendix A (`app:product`) to prove Proposition 3.3
(`prop:product`). -/
abbrev IntegerLaurent := AddMonoidAlgebra ℤ Lattice

/-- The coefficient embedding from integer to rational Laurent polynomials in Appendix A
(`app:product`), preserving every lattice exponent. -/
noncomputable def intLaurentCast : IntegerLaurent →+* Laurent :=
  AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℚ)

/-- Auxiliary to the scaling step of Appendix A (`app:product`): coefficient embedding acts
pointwise by the integer-to-rational cast. -/
@[simp] theorem intLaurentCast_coeff (F : IntegerLaurent) (h : Lattice) :
    (intLaurentCast F).coeff h = (F.coeff h : ℚ) := by
  simp [intLaurentCast]

/-- The common-denominator step in Appendix A (`app:product`): one nonzero integer multiplier makes
every element of a finite rational set integral. -/
theorem finite_set_integer_scale (S : Set ℚ) (hS : S.Finite) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ S, ∃ a : ℤ, (n : ℚ) * x = (a : ℚ) := by
  classical
  obtain ⟨n, hn⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors ℤ) hS.toFinset
  refine ⟨n, mem_nonZeroDivisors_iff_ne_zero.mp n.property, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := hn x (hS.mem_toFinset.mpr hx)
  refine ⟨a, ?_⟩
  simpa using ha.symm

/-- The configuration scaling step of Appendix A (`app:product`): a nonzero integer multiple of a
finite-range rational configuration has finite integer range. -/
theorem finiteRange_integer_scale {c : Configuration ℚ} (hc : FiniteRange c) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ C : Configuration ℤ,
      FiniteRange C ∧ ∀ z, (n : ℚ) * c z = (C z : ℚ) := by
  classical
  obtain ⟨n, hn, hs⟩ := finite_set_integer_scale (Set.range c) hc
  choose C hC using fun z : Lattice => hs (c z) ⟨z, rfl⟩
  refine ⟨n, hn, C, ?_, hC⟩
  have hcast : FiniteRange (fun z => (C z : ℚ)) := by
    have heq : (fun z => (C z : ℚ)) = fun z => (n : ℚ) * c z := by
      funext z
      exact (hC z).symm
    rw [heq]
    exact hc.map (fun x => (n : ℚ) * x)
  apply Set.Finite.of_finite_image (f := fun a : ℤ => (a : ℚ)) ?_
    (Int.cast_injective.injOn)
  rw [← Set.range_comp]
  exact hcast

/-- The filter scaling step of Appendix A (`app:product`): a rational Laurent polynomial has a
nonzero integer multiple represented by an integer-coefficient filter. -/
theorem integer_filter_scale (f : Laurent) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ F : IntegerLaurent, intLaurentCast F = (n : ℚ) • f := by
  classical
  obtain ⟨n, hn, C, _, hC⟩ := finiteRange_integer_scale (c := f.coeff) f.coeff.finite_range
  have hsupport : ∀ h : Lattice, C h ≠ 0 → h ∈ f.coeff.support := by
    intro h hh
    by_contra hnot
    have hz := hC h
    rw [Finsupp.notMem_support_iff.mp hnot, mul_zero] at hz
    exact hh (Int.cast_eq_zero.mp hz.symm)
  let F : IntegerLaurent := AddMonoidAlgebra.ofCoeff (Finsupp.onFinset f.coeff.support C hsupport)
  refine ⟨n, hn, F, ?_⟩
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro h
  rw [intLaurentCast_coeff]
  change (C h : ℚ) = (n : ℚ) * f.coeff h
  exact (hC h).symm

end Nivat.Algebra
