/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Core.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Polynomial.Eval.Defs

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
# Laurent polynomial operators

This module implements the notation of Section 1.1. `Laurent` is the rational
Laurent ring, `act` is its forward-shift action, and `lineEval` substitutes a
lattice monomial into an ordinary polynomial.

The principal identities are `act_apply`, `act_mul`, `act_difference`, and
`act_lineEval_X_pow_sub_one`. The theorem `finiteRange_act` verifies that the
class of finite-range rational configurations is closed under every operator.
-/

@[expose] public section

namespace Nivat

/-- Section 1.1 (Notation): the rational Laurent polynomial ring on the full integer lattice. -/
abbrev Laurent := AddMonoidAlgebra ℚ Lattice

namespace Algebra

/-- Section 1.1 (Notation): a forward lattice translation as a rational linear endomorphism. -/
def shiftLinear (h : Lattice) : Module.End ℚ (Configuration ℚ) where
  toFun := shift h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Section 1.1 (Notation): the bundled translation evaluates to the forward shift. -/
@[simp] theorem shiftLinear_apply (h : Lattice) (c : Configuration ℚ) :
    shiftLinear h c = shift h c := rfl

/-- Section 1.1 (Notation): the additive lattice acts on configurations by commuting forward
shifts. -/
def shiftRepresentation : Multiplicative Lattice →* Module.End ℚ (Configuration ℚ) where
  toFun h := shiftLinear h.toAdd
  map_one' := by ext c z; simp [shiftLinear, shift]
  map_mul' h t := by
    ext c z
    change c (z + (h.toAdd + t.toAdd)) = c ((z + h.toAdd) + t.toAdd)
    rw [add_assoc]

/-- Section 1.1 (Notation): the algebra homomorphism extending lattice translations to Laurent
filters. -/
noncomputable def actionHom : Laurent →ₐ[ℚ] Module.End ℚ (Configuration ℚ) :=
  AddMonoidAlgebra.lift ℚ (Module.End ℚ (Configuration ℚ)) Lattice shiftRepresentation

/-- Section 1.1 (Notation): the finite Laurent polynomial operator applied to a rational
configuration. -/
noncomputable def act (f : Laurent) (c : Configuration ℚ) : Configuration ℚ :=
  actionHom f c

/-- Section 1.1 (Notation): the operator is the finite sum of coefficients times forward-shifted
values. -/
theorem act_apply (f : Laurent) (c : Configuration ℚ) (z : Lattice) :
    act f c z = f.coeff.sum (fun h a => a * c (z + h)) := by
  classical
  simp [act, actionHom, AddMonoidAlgebra.lift_apply, Finsupp.sum,
    shiftRepresentation, shiftLinear, shift, Finset.sum_apply]

/-- Section 1.1 (Notation): the zero filter sends every configuration to zero. -/
@[simp] theorem act_zero (c : Configuration ℚ) : act 0 c = 0 := by
  simp [act]

/-- Section 1.1 (Notation): the constant filter one acts as the identity. -/
@[simp] theorem act_one (c : Configuration ℚ) : act 1 c = c := by
  simp [act]

/-- Section 1.1 (Notation): adding filters adds their outputs. -/
theorem act_add (f g : Laurent) (c : Configuration ℚ) :
    act (f + g) c = act f c + act g c := by
  simp [act]

/-- Section 1.1 (Notation): multiplying filters composes their operators. -/
theorem act_mul (f g : Laurent) (c : Configuration ℚ) :
    act (f * g) c = act f (act g c) := by
  simp [act, Module.End.mul_apply]

/-- Section 1.1 (Notation): subtracting filters subtracts their outputs. -/
theorem act_sub (f g : Laurent) (c : Configuration ℚ) :
    act (f - g) c = act f c - act g c := by
  simp [act]

/-- Section 1.1 (Notation): negating a filter negates its output. -/
theorem act_neg (f : Laurent) (c : Configuration ℚ) : act (-f) c = -act f c := by
  simp [act]

/-- Section 1.1 (Notation): every Laurent filter annihilates the zero configuration. -/
@[simp] theorem act_config_zero (f : Laurent) : act f 0 = 0 := by
  exact map_zero (actionHom f)

/-- Section 1.1 (Notation): each Laurent operator preserves sums of configurations. -/
theorem act_config_add (f : Laurent) (c d : Configuration ℚ) :
    act f (c + d) = act f c + act f d := by
  exact map_add (actionHom f) c d

/-- Section 1.1 (Notation): each Laurent operator preserves differences of configurations. -/
theorem act_config_sub (f : Laurent) (c d : Configuration ℚ) :
    act f (c - d) = act f c - act f d := by
  exact map_sub (actionHom f) c d

/-- Section 1.1 (Notation): each Laurent operator commutes with rational scaling of the
configuration. -/
theorem act_config_smul (f : Laurent) (a : ℚ) (c : Configuration ℚ) :
    act f (a • c) = a • act f c := by
  exact map_smul (actionHom f) a c

/-- Section 1.1 (Notation): rational scaling of the filter scales its output. -/
theorem act_smul (a : ℚ) (f : Laurent) (c : Configuration ℚ) :
    act (a • f) c = a • act f c := by
  simp [act]

/-- Section 1.1 (Notation): a single supported coefficient acts by scaling a forward shift. -/
@[simp] theorem act_single (h : Lattice) (a : ℚ) (c : Configuration ℚ) :
    act (AddMonoidAlgebra.single h a) c = a • shift h c := by
  simp [act, actionHom, shiftRepresentation, shiftLinear]

/-- Section 1.1 (Notation): the lattice monomial with exponent `h` and coefficient one. -/
noncomputable def monomial (h : Lattice) : Laurent := AddMonoidAlgebra.single h 1

/-- Section 1.1 (Notation): the zero-exponent monomial is the multiplicative identity. -/
@[simp] theorem monomial_zero : monomial 0 = 1 := rfl

/-- Section 1.1 (Notation): multiplication of lattice monomials adds their exponents. -/
@[simp] theorem monomial_mul (h t : Lattice) :
    monomial h * monomial t = monomial (h + t) := by
  simp [monomial]

/-- Section 1.1 (Notation): a natural power of a monomial scales its exponent. -/
@[simp] theorem monomial_pow (h : Lattice) (q : ℕ) :
    monomial h ^ q = monomial (q • h) := by
  simp [monomial, AddMonoidAlgebra.single_pow]

/-- Section 1.1 (Notation): every lattice monomial is a unit, with inverse at the negated
exponent. -/
theorem monomial_isUnit (h : Lattice) : IsUnit (monomial h) := by
  exact ⟨⟨monomial h, monomial (-h), by simp, by simp⟩, rfl⟩

/-- Section 1.1 (Notation): a lattice monomial has a nonzero coefficient and is nonzero. -/
theorem monomial_ne_zero (h : Lattice) : monomial h ≠ 0 :=
  (monomial_isUnit h).ne_zero

/-- Section 1.1 (Notation): distinct lattice exponents give distinct monomials. -/
theorem monomial_injective : Function.Injective monomial :=
  AddMonoidAlgebra.single_left_injective one_ne_zero

/-- Section 1.1 (Notation): a nonzero direction gives a nonzero difference polynomial. -/
theorem monomial_sub_one_ne_zero {h : Lattice} (hh : h ≠ 0) :
    monomial h - 1 ≠ 0 := by
  intro heq
  have h : monomial h = monomial 0 := by simpa using sub_eq_zero.mp heq
  exact hh (monomial_injective h)

/-- Section 1.1 (Notation): a lattice monomial acts by its forward shift. -/
@[simp] theorem act_monomial (h : Lattice) (c : Configuration ℚ) :
    act (monomial h) c = shift h c := by simp [monomial]

/-- Section 1.1 (Notation): the polynomial `monomial h - 1` acts by the difference operator in
direction `h`. -/
theorem act_difference (h : Lattice) (c : Configuration ℚ) :
    act (monomial h - 1) c = difference h c := by
  simp [act_sub, difference]

/-- Section 1.1 (Notation): every Laurent operator commutes with lattice translations. -/
theorem act_shift (f : Laurent) (h : Lattice) (c : Configuration ℚ) :
    act f (shift h c) = shift h (act f c) := by
  rw [← act_monomial, ← act_mul, mul_comm, act_mul, act_monomial]

/-- Section 1.1 (Notation): every Laurent operator commutes with lattice differences. -/
theorem act_difference_comm (f : Laurent) (h : Lattice) (c : Configuration ℚ) :
    act f (difference h c) = difference h (act f c) := by
  simp [difference, act_config_sub, act_shift]

/-- Section 1.1 (Notation): a constant rational configuration has finite range. -/
theorem finiteRange_const (a : ℚ) : FiniteRange (fun _ : Lattice => a) := by
  simp [FiniteRange]

/-- Section 1.1 (Notation): the sum of two finite-range rational configurations has finite range. -/
theorem finiteRange_add {c d : Configuration ℚ} (hc : FiniteRange c)
    (hd : FiniteRange d) : FiniteRange (c + d) := by
  apply ((hc.prod hd).image (fun p : ℚ × ℚ => p.1 + p.2)).subset
  rintro _ ⟨z, rfl⟩
  exact ⟨(c z, d z), ⟨⟨z, rfl⟩, ⟨z, rfl⟩⟩, rfl⟩

/-- Section 1.1 (Notation): rational scaling preserves finite range. -/
theorem finiteRange_smul {c : Configuration ℚ} (hc : FiniteRange c) (a : ℚ) :
    FiniteRange (a • c) := by
  exact hc.map (fun x => a * x)

/-- Section 1.1 (Notation): the finite sum defining a Laurent operator preserves finite rational
range. -/
theorem finiteRange_act (f : Laurent) {c : Configuration ℚ} (hc : FiniteRange c) :
    FiniteRange (act f c) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero =>
    rw [act_zero]
    change FiniteRange (fun _ : Lattice => (0 : ℚ))
    exact finiteRange_const 0
  | add f g hf hg => rw [act_add]; exact finiteRange_add hf hg
  | single h a => rw [act_single]; exact finiteRange_smul (hc.shift h) a

/-- Section 1.1 (Notation): substitute the lattice monomial in direction `v` for a polynomial
variable. -/
noncomputable def lineEval (v : Lattice) : Polynomial ℚ →+* Laurent :=
  Polynomial.eval₂RingHom (algebraMap ℚ Laurent) (monomial v)

/-- Section 1.1 (Notation): the polynomial variable evaluates to the monomial in direction `v`. -/
@[simp] theorem lineEval_X (v : Lattice) : lineEval v Polynomial.X = monomial v := by
  simp [lineEval]

/-- Section 1.1 (Notation): a constant polynomial evaluates to the corresponding zero-exponent
Laurent coefficient. -/
@[simp] theorem lineEval_C (v : Lattice) (a : ℚ) :
    lineEval v (Polynomial.C a) = AddMonoidAlgebra.single 0 a := by
  simp [lineEval]

/-- Section 1.1 (Notation): substitution along a lattice direction preserves polynomial
divisibility. -/
theorem lineEval_dvd (v : Lattice) {f g : Polynomial ℚ} (h : f ∣ g) :
    lineEval v f ∣ lineEval v g := map_dvd (lineEval v) h

/-- Section 1.1 (Notation): a power of the polynomial variable evaluates to a scaled lattice
exponent. -/
@[simp] theorem lineEval_X_pow (v : Lattice) (q : ℕ) :
    lineEval v (Polynomial.X ^ q) = monomial (q • v) := by simp

/-- Section 1.1 (Notation): the period polynomial evaluates to the difference polynomial in
direction `q • v`. -/
theorem lineEval_X_pow_sub_one (v : Lattice) (q : ℕ) :
    lineEval v (Polynomial.X ^ q - 1) = monomial (q • v) - 1 := by simp

/-- Section 1.1 (Notation): the evaluated period polynomial acts as the difference in direction `q •
v`. -/
theorem act_lineEval_X_pow_sub_one (v : Lattice) (q : ℕ) (c : Configuration ℚ) :
    act (lineEval v (Polynomial.X ^ q - 1)) c = difference (q • v) c := by
  rw [lineEval_X_pow_sub_one, act_difference]

end Algebra
end Nivat
