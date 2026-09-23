/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Algebra.RationalScaling
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Nat.Factorial.Basic
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
# A product of difference operators from a nonzero annihilator

Proposition 3.3 (`prop:product`) is
`exists_product_differences_of_annihilator`. Appendix A (`app:product`) proves
it by separate integer scaling of the configuration and filter, prime dilation,
and polynomial interpolation. Every output direction is nonzero, and the
resulting list of difference factors is nonempty.

The action `coefficientAct` is defined over a commutative coefficient ring so
that reduction from integers to `ZMod p` commutes with filtering. Frobenius
identifies the prime power of a reduced filter with dilation of its exponents.
A common bound on all dilated integer outputs then forces sufficiently large
prime dilations of annihilators to annihilate. Factorization extends this to
the progression `1 + j * B!` in equation (`eq:dilation-family`).

The theorem `dilation_interpolation_identity` is equation (`eq:interpolation`)
with an arbitrary auxiliary polynomial. Translating one nonzero coefficient
to exponent zero and choosing factors `C(M) - X` isolates that coefficient and
gives a product of `M - 1`. Casting back to rationals and cancelling the
nonzero scaling factors concludes the proof.
-/

@[expose] public section

namespace Nivat.Algebra

section CoefficientAction

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): a forward translation
as a linear endomorphism over the coefficient ring. -/
def coefficientShift (h : Lattice) : Module.End R (Configuration R) where
  toFun := shift h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the integer lattice
acts by forward translations over a commutative ring. -/
def coefficientShiftRepresentation :
    Multiplicative Lattice →* Module.End R (Configuration R) where
  toFun h := coefficientShift h.toAdd
  map_one' := by
    ext c z
    change c (z + 0) = c z
    rw [add_zero]
  map_mul' h t := by
    ext c z
    change c (z + (h.toAdd + t.toAdd)) = c ((z + h.toAdd) + t.toAdd)
    rw [add_assoc]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): extend the
coefficient-ring shift representation to a Laurent algebra action. -/
noncomputable def coefficientActionHom :
    AddMonoidAlgebra R Lattice →ₐ[R] Module.End R (Configuration R) :=
  AddMonoidAlgebra.lift R (Module.End R (Configuration R)) Lattice coefficientShiftRepresentation

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the Laurent operator
over a commutative ring, permitting both integral coefficients and reduction modulo a prime. -/
noncomputable def coefficientAct (f : AddMonoidAlgebra R Lattice)
    (c : Configuration R) : Configuration R := coefficientActionHom f c

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the coefficient-ring
action is the finite sum of coefficients times translated values. -/
theorem coefficientAct_apply (f : AddMonoidAlgebra R Lattice) (c : Configuration R) (z : Lattice) :
    coefficientAct f c z = f.coeff.sum (fun h a => a * c (z + h)) := by
  classical
  simp [coefficientAct, coefficientActionHom, AddMonoidAlgebra.lift_apply, Finsupp.sum,
    coefficientShiftRepresentation, coefficientShift, shift, Finset.sum_apply]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the zero
coefficient-ring filter has zero output. -/
@[simp] theorem coefficientAct_zero (c : Configuration R) : coefficientAct 0 c = 0 := by
  simp [coefficientAct]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the identity
coefficient-ring filter acts identically. -/
@[simp] theorem coefficientAct_one (c : Configuration R) : coefficientAct 1 c = c := by
  simp [coefficientAct]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): every
coefficient-ring filter annihilates the zero configuration. -/
@[simp] theorem coefficientAct_config_zero (f : AddMonoidAlgebra R Lattice) :
    coefficientAct f 0 = 0 := map_zero (coefficientActionHom f)

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): adding
coefficient-ring filters adds their outputs. -/
theorem coefficientAct_add (f g : AddMonoidAlgebra R Lattice) (c : Configuration R) :
    coefficientAct (f + g) c = coefficientAct f c + coefficientAct g c := by
  simp [coefficientAct]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): multiplying
coefficient-ring filters composes their actions. -/
theorem coefficientAct_mul (f g : AddMonoidAlgebra R Lattice) (c : Configuration R) :
    coefficientAct (f * g) c = coefficientAct f (coefficientAct g c) := by
  simp [coefficientAct, Module.End.mul_apply]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the action of a
finite filter sum is the corresponding sum of outputs. -/
theorem coefficientAct_finset_sum {ι : Type*} (S : Finset ι)
    (f : ι → AddMonoidAlgebra R Lattice) (c : Configuration R) :
    coefficientAct (∑ j ∈ S, f j) c = ∑ j ∈ S, coefficientAct (f j) c := by
  change coefficientActionHom (∑ j ∈ S, f j) c = _
  rw [map_sum]
  exact LinearMap.sum_apply _ _ _

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): a single coefficient
acts as a scaled forward shift over the coefficient ring. -/
@[simp] theorem coefficientAct_single (h : Lattice) (a : R) (c : Configuration R) :
    coefficientAct (AddMonoidAlgebra.single h a) c = a • shift h c := by
  simp [coefficientAct, coefficientActionHom, coefficientShiftRepresentation, coefficientShift]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the general
coefficient-ring action agrees with the rational action from Section 1.1. -/
theorem coefficientAct_rat (f : Laurent) (c : Configuration ℚ) : coefficientAct f c = act f c := by
  funext z
  rw [coefficientAct_apply, act_apply]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): changing the
coefficient ring commutes with the action on the configuration, in particular for reduction
modulo a prime. -/
theorem coefficientAct_map (ρ : R →+* S) (f : AddMonoidAlgebra R Lattice)
    (c : Configuration R) :
    coefficientAct (AddMonoidAlgebra.mapRingHom Lattice ρ f) (ρ ∘ c) =
      ρ ∘ coefficientAct f c := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero =>
    funext z
    simp
  | add f g hf hg =>
    funext z
    simpa only [map_add, coefficientAct_add, Pi.add_apply, Function.comp_apply]
      using congrArg₂ (fun x y : S => x + y) (congrFun hf z) (congrFun hg z)
  | single h a =>
    funext z
    simp [coefficientAct_single, shift, Function.comp_apply, map_mul]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): natural scaling of
lattice exponents as an additive homomorphism. -/
def dilationLattice (n : ℕ) : Lattice →+ Lattice where
  toFun h := n • h
  map_zero' := nsmul_zero n
  map_add' h t := nsmul_add h t n

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the Laurent ring
homomorphism scaling all lattice exponents by a natural number. -/
noncomputable def dilate (n : ℕ) : AddMonoidAlgebra R Lattice →+* AddMonoidAlgebra R Lattice :=
  AddMonoidAlgebra.mapDomainRingHom R (dilationLattice n)

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): dilation scales the
exponent of a single coefficient without changing that coefficient. -/
@[simp] theorem dilate_single (n : ℕ) (h : Lattice) (a : R) :
    dilate n (AddMonoidAlgebra.single h a) = AddMonoidAlgebra.single (n • h) a := by
  simp [dilate, dilationLattice]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): dilation by one fixes
the filter. -/
@[simp] theorem dilate_one (f : AddMonoidAlgebra R Lattice) : dilate 1 f = f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single h a => simp

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): composition of
dilations multiplies their scaling parameters. -/
theorem dilate_dilate (m n : ℕ) (f : AddMonoidAlgebra R Lattice) :
    dilate m (dilate n f) = dilate (m * n) f := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single h a => simp only [dilate_single, smul_smul]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): a coefficient-ring
homomorphism commutes with dilation of the exponents. -/
theorem map_dilate (ρ : R →+* S) (n : ℕ) (f : AddMonoidAlgebra R Lattice) :
    AddMonoidAlgebra.mapRingHom Lattice ρ (dilate n f) =
      dilate n (AddMonoidAlgebra.mapRingHom Lattice ρ f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, hf, hg]
  | single h a => simp

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): every positive power
of an annihilator still annihilates the configuration. -/
theorem coefficientAct_pow_eq_zero (f : AddMonoidAlgebra R Lattice) (c : Configuration R)
    (hf : coefficientAct f c = 0) {n : ℕ} (hn : 0 < n) :
    coefficientAct (f ^ n) c = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [pow_succ, coefficientAct_mul, hf, coefficientAct_config_zero]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): a fixed finite filter
on a finite-range configuration has finitely many outputs across all dilation exponents and
lattice sites. -/
theorem finite_dilate_values (f : AddMonoidAlgebra R Lattice) {c : Configuration R}
    (hc : FiniteRange c) :
    (Set.range (fun nz : ℕ × Lattice => coefficientAct (dilate nz.1 f) c nz.2)).Finite := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    apply ((hf.prod hg).image (fun x : R × R => x.1 + x.2)).subset
    rintro _ ⟨nz, rfl⟩
    refine ⟨(coefficientAct (dilate nz.1 f) c nz.2,
      coefficientAct (dilate nz.1 g) c nz.2), ⟨⟨nz, rfl⟩, ⟨nz, rfl⟩⟩, ?_⟩
    simp [coefficientAct_add]
  | single h a =>
    apply (hc.image (fun x : R => a * x)).subset
    rintro _ ⟨nz, rfl⟩
    refine ⟨c (nz.2 + nz.1 • h), ⟨_, rfl⟩, ?_⟩
    simp [shift]

end CoefficientAction

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): Frobenius in
characteristic `p` identifies the `p`th power of a Laurent filter over `ZMod p` with its
dilation by `p`. -/
theorem zmod_pow_eq_dilate (p : ℕ) [Fact p.Prime]
    (f : AddMonoidAlgebra (ZMod p) Lattice) : f ^ p = dilate p f := by
  let : CharP (AddMonoidAlgebra (ZMod p) Lattice) p :=
    charP_of_injective_algebraMap' (ZMod p) p
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp [NeZero.ne p]
  | add f g hf hg =>
    rw [← frobenius_def, map_add, frobenius_def, frobenius_def, hf, hg, map_add]
  | single h a =>
    rw [AddMonoidAlgebra.single_pow, dilate_single, ZMod.pow_card]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the finite set of all
dilated integer outputs has a common natural absolute-value bound. -/
theorem exists_uniform_dilate_bound (f : IntegerLaurent) {c : Configuration ℤ}
    (hc : FiniteRange c) :
    ∃ B : ℕ, ∀ n : ℕ, ∀ z : Lattice, (coefficientAct (dilate n f) c z).natAbs ≤ B := by
  classical
  have hv := finite_dilate_values f hc
  refine ⟨hv.toFinset.sup Int.natAbs, fun n z => ?_⟩
  exact Finset.le_sup (f := Int.natAbs) (hv.mem_toFinset.mpr ⟨(n, z), rfl⟩)

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): dilation by a prime
larger than the common output bound preserves annihilation. Frobenius makes each output
divisible by that prime, and the strict absolute-value bound forces zero. -/
theorem prime_dilate_annihilates (f : IntegerLaurent) (c : Configuration ℤ)
    (B : ℕ)
    (hbound : ∀ n : ℕ, ∀ z : Lattice, (coefficientAct (dilate n f) c z).natAbs ≤ B)
    {m p : ℕ} (hp : p.Prime) (hBp : B < p)
    (hm : coefficientAct (dilate m f) c = 0) :
    coefficientAct (dilate (m * p) f) c = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let ρ : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let Fm := AddMonoidAlgebra.mapRingHom Lattice ρ (dilate m f)
  have hmod : coefficientAct Fm (ρ ∘ c) = 0 := by
    rw [coefficientAct_map, hm]
    funext z
    exact map_zero ρ
  have hpow := coefficientAct_pow_eq_zero Fm (ρ ∘ c) hmod hp.pos
  have heq : AddMonoidAlgebra.mapRingHom Lattice ρ (dilate (m * p) f) = Fm ^ p := by
    rw [zmod_pow_eq_dilate]
    dsimp only [Fm]
    rw [← map_dilate, dilate_dilate, mul_comm p m]
  have hnext : coefficientAct
      (AddMonoidAlgebra.mapRingHom Lattice ρ (dilate (m * p) f)) (ρ ∘ c) = 0 := by
    rw [heq]
    exact hpow
  rw [coefficientAct_map] at hnext
  funext z
  have hz := congrFun hnext z
  change ((coefficientAct (dilate (m * p) f) c z : ℤ) : ZMod p) = 0 at hz
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz)
  simpa only [Int.natAbs_natCast] using (hbound (m * p) z).trans_lt hBp

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): every prime factor of
an integer coprime to `B!` exceeds `B`. -/
private theorem prime_gt_of_coprime_factorial {B n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) (hn : n.Coprime B.factorial) : B < p := by
  by_contra hle
  have hcop : p.Coprime B.factorial := hn.of_dvd_left hpn
  exact (hp.coprime_iff_not_dvd.mp hcop)
    (Nat.dvd_factorial hp.pos (Nat.le_of_not_gt hle))

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): prime factorization
extends preservation of annihilation to every positive exponent coprime to the factorial bound. -/
theorem coprime_dilate_annihilates (f : IntegerLaurent) (c : Configuration ℤ)
    (B : ℕ)
    (hbound : ∀ n : ℕ, ∀ z : Lattice, (coefficientAct (dilate n f) c z).natAbs ≤ B)
    (hf : coefficientAct f c = 0) {n : ℕ} (hn : 0 < n) (hcop : n.Coprime B.factorial) :
    coefficientAct (dilate n f) c = 0 := by
  have hall : ∀ k : ℕ, 0 < k → k.Coprime B.factorial → coefficientAct (dilate k f) c = 0 := by
    apply induction_on_primes
    · intro h
      exact (Nat.not_lt_zero _ h).elim
    · intro _ _
      simpa only [dilate_one] using hf
    · intro p k hp ih hpos hc
      have hkp : 0 < k := by
        by_contra hz
        have hk : k = 0 := Nat.eq_zero_of_not_pos hz
        simp [hk] at hpos
      have hkc : k.Coprime B.factorial := hc.of_dvd_left (Nat.dvd_mul_left k p)
      have hBp := prime_gt_of_coprime_factorial hp (Nat.dvd_mul_right p k) hc
      rw [Nat.mul_comm p k]
      exact prime_dilate_annihilates f c B hbound hp hBp (ih hkp hkc)
  exact hall n hn hcop

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): equation
(`eq:dilation-family`): all dilations at exponents `1 + j * B!` annihilate. -/
theorem progression_dilate_annihilates (f : IntegerLaurent) (c : Configuration ℤ)
    (B : ℕ)
    (hbound : ∀ n : ℕ, ∀ z : Lattice, (coefficientAct (dilate n f) c z).natAbs ≤ B)
    (hf : coefficientAct f c = 0) (j : ℕ) :
    coefficientAct (dilate (1 + j * B.factorial) f) c = 0 := by
  have hn : 0 < 1 + j * B.factorial :=
    Nat.zero_lt_one.trans_le (Nat.le_add_right 1 _)
  have hcop : (1 + j * B.factorial).Coprime B.factorial :=
    (Nat.coprime_add_mul_right_left 1 B.factorial j).mpr (Nat.coprime_one_left _)
  exact coprime_dilate_annihilates f c B hbound hf hn hcop

section Interpolation

variable {R : Type*} [CommRing R]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): a dilated filter is
the finite sum of its original coefficients at their scaled exponents. -/
private theorem dilate_eq_sum (n : ℕ) (f : AddMonoidAlgebra R Lattice) :
    dilate n f = ∑ h ∈ f.coeff.support, AddMonoidAlgebra.single (n • h) (f.coeff h) := by
  conv_lhs => rw [← f.sum_coeff_single]
  simp only [Finsupp.sum, map_sum, dilate_single]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): the term with
exponent `(1 + j * r) • h` factors into the original monomial and a `j`th power. -/
private theorem single_affine_dilate (j r : ℕ) (h : Lattice) (a : R) :
    AddMonoidAlgebra.single ((1 + j * r) • h) a =
      AddMonoidAlgebra.single h a *
        (AddMonoidAlgebra.single (r • h) (1 : R)) ^ j := by
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single, one_pow, mul_one]
  simp only [add_nsmul, one_nsmul, smul_smul]

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): equation
(`eq:interpolation`): linear combinations of dilations along an arithmetic progression are
evaluations of the coefficient polynomial at the corresponding lattice monomials. -/
theorem dilation_interpolation_identity (r : ℕ) (f : AddMonoidAlgebra R Lattice)
    (H : Polynomial (AddMonoidAlgebra R Lattice)) :
    H.sum (fun j b => b * dilate (1 + j * r) f) =
      ∑ h ∈ f.coeff.support, AddMonoidAlgebra.single h (f.coeff h) *
        H.eval (AddMonoidAlgebra.single (r • h) 1) := by
  classical
  simp only [Polynomial.sum_def, dilate_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [single_affine_dilate]
  ac_rfl

end Interpolation

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): interpolation for an
integral annihilator with nonzero constant coefficient produces a product of nonzero-exponent
difference factors. The auxiliary factors `C(M) - X` evaluate at one to `M - 1`. -/
theorem integer_centered_product (f : IntegerLaurent) (hf0 : f.coeff 0 ≠ 0)
    (c : Configuration ℤ) (hc : FiniteRange c) (hf : coefficientAct f c = 0) :
    ∃ r : ℕ, 0 < r ∧ coefficientAct
      (∏ h ∈ f.coeff.support.erase 0,
        (AddMonoidAlgebra.single (r • h) (1 : ℤ) - 1)) c = 0 := by
  classical
  obtain ⟨B, hB⟩ := exists_uniform_dilate_bound f hc
  let r := B.factorial
  let S := f.coeff.support.erase 0
  let H : Polynomial IntegerLaurent :=
    ∏ h ∈ S, (Polynomial.C (AddMonoidAlgebra.single (r • h) 1) - Polynomial.X)
  let P : IntegerLaurent := ∏ h ∈ S, (AddMonoidAlgebra.single (r • h) 1 - 1)
  have hcomb : coefficientAct (H.sum (fun j b => b * dilate (1 + j * r) f)) c = 0 := by
    rw [Polynomial.sum_def, coefficientAct_finset_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [coefficientAct_mul, progression_dilate_annihilates f c B hB hf j,
      coefficientAct_config_zero]
  have hroot (h : Lattice) (hh : h ∈ S) :
      H.eval (AddMonoidAlgebra.single (r • h) 1) = 0 := by
    dsimp only [H]
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero hh
    simp
  have heval : H.eval (AddMonoidAlgebra.single (r • (0 : Lattice)) 1) = P := by
    rw [nsmul_zero]
    change H.eval (1 : IntegerLaurent) = P
    simp [H, P, Polynomial.eval_prod]
  have hident := dilation_interpolation_identity r f H
  rw [Finset.sum_eq_single 0] at hident
  · rw [heval] at hident
    rw [hident, coefficientAct_mul, coefficientAct_single] at hcomb
    refine ⟨r, Nat.factorial_pos B, ?_⟩
    change coefficientAct P c = 0
    funext z
    have hz := congrFun hcomb z
    change f.coeff 0 * coefficientAct P c (z + 0) = 0 at hz
    rw [add_zero] at hz
    exact (mul_eq_zero.mp hz).resolve_left hf0
  · intro h hh hn
    rw [hroot h (Finset.mem_erase.mpr ⟨hn, hh⟩), mul_zero]
  · intro hnot
    exact (hnot (Finsupp.mem_support_iff.mpr hf0)).elim

/-- Auxiliary to Proposition 3.3 (`prop:product`), Appendix A (`app:product`): translate a nonzero
coefficient to exponent zero and apply interpolation. Nonzeroness of the configuration forces a
nonempty factor list, and positive dilation preserves each nonzero direction. -/
theorem exists_integer_product_differences {c : Configuration ℤ} (hc : FiniteRange c)
    (hcne : c ≠ 0) {f : IntegerLaurent} (hfne : f ≠ 0) (hf : coefficientAct f c = 0) :
    ∃ hs : List Lattice, hs ≠ [] ∧ (∀ h ∈ hs, h ≠ 0) ∧
      coefficientAct ((hs.map (fun h => AddMonoidAlgebra.single h (1 : ℤ) - 1)).prod) c = 0 := by
  classical
  have hcoeff : f.coeff ≠ 0 := AddMonoidAlgebra.coeff_eq_zero.not.mpr hfne
  obtain ⟨u, hu⟩ := Finsupp.support_nonempty_iff.mpr hcoeff
  let F := AddMonoidAlgebra.single (-u) (1 : ℤ) * f
  have hF0 : F.coeff 0 ≠ 0 := by
    simpa [F, AddMonoidAlgebra.coeff_single_mul_apply] using Finsupp.mem_support_iff.mp hu
  have hF : coefficientAct F c = 0 := by
    rw [coefficientAct_mul, hf, coefficientAct_config_zero]
  obtain ⟨r, hr, hprod⟩ := integer_centered_product F hF0 c hc hF
  let S := F.coeff.support.erase 0
  let hs := S.toList.map (fun h => r • h)
  have hhs : coefficientAct
      ((hs.map (fun h => AddMonoidAlgebra.single h (1 : ℤ) - 1)).prod) c = 0 := by
    simpa only [hs, List.map_map, Finset.prod_map_toList, Function.comp_apply] using hprod
  refine ⟨hs, ?_, ?_, hhs⟩
  · intro he
    rw [he, List.map_nil, List.prod_nil, coefficientAct_one] at hhs
    exact hcne hhs
  · intro h hh
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hh
    have hx0 : x ≠ 0 := (Finset.mem_erase.mp (Finset.mem_toList.mp hx)).1
    exact smul_ne_zero (Nat.ne_of_gt hr) hx0

/-- Proposition 3.3 (`prop:product`), proved in Appendix A (`app:product`): every nonzero
finite-range rational configuration with a nonzero Laurent annihilator has a nonempty product of
differences in nonzero lattice directions as an annihilator. -/
theorem exists_product_differences_of_annihilator {c : Configuration ℚ}
    (hc : FiniteRange c) (hcne : c ≠ 0) {f : Laurent} (hfne : f ≠ 0)
    (hf : act f c = 0) :
    ∃ hs : List Lattice, hs ≠ [] ∧ (∀ h ∈ hs, h ≠ 0) ∧
      act ((hs.map (fun h => monomial h - 1)).prod) c = 0 := by
  classical
  obtain ⟨a, ha, C, hCfinite, hC⟩ := finiteRange_integer_scale hc
  obtain ⟨b, hb, F, hF⟩ := integer_filter_scale f
  have haq : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hbq : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hCeq : (Int.castRingHom ℚ) ∘ C = (a : ℚ) • c := by
    funext z
    exact (hC z).symm
  have hCne : C ≠ 0 := by
    intro hz
    apply hcne
    funext z
    have he := hC z
    rw [hz] at he
    exact (mul_eq_zero.mp he).resolve_left haq
  have hFne : F ≠ 0 := by
    intro hz
    apply hfne
    have he := hF
    rw [hz, map_zero] at he
    exact (smul_eq_zero_iff_right hbq).mp he.symm
  have hFC : coefficientAct F C = 0 := by
    have he : coefficientAct (intLaurentCast F) ((Int.castRingHom ℚ) ∘ C) = 0 := by
      rw [coefficientAct_rat, hF, hCeq, act_smul, act_config_smul, hf, smul_zero, smul_zero]
    change coefficientAct (AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℚ) F)
      ((Int.castRingHom ℚ) ∘ C) = 0 at he
    rw [coefficientAct_map] at he
    funext z
    exact Int.cast_eq_zero.mp (congrFun he z)
  obtain ⟨hs, hnil, hnz, hann⟩ := exists_integer_product_differences hCfinite hCne hFne hFC
  refine ⟨hs, hnil, hnz, ?_⟩
  have he := coefficientAct_map (Int.castRingHom ℚ)
    ((hs.map (fun h => AddMonoidAlgebra.single h (1 : ℤ) - 1)).prod) C
  rw [hann] at he
  have hcastprod : AddMonoidAlgebra.mapRingHom Lattice (Int.castRingHom ℚ)
      ((hs.map (fun h => AddMonoidAlgebra.single h (1 : ℤ) - 1)).prod) =
      (hs.map (fun h => monomial h - 1)).prod := by
    rw [map_list_prod, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro h hh
    simp [monomial]
  rw [hcastprod, coefficientAct_rat, hCeq, act_config_smul] at he
  apply (smul_eq_zero_iff_right haq).mp
  calc
    (a : ℚ) • act ((hs.map (fun h => monomial h - 1)).prod) c =
        (Int.castRingHom ℚ) ∘ (0 : Configuration ℤ) := he
    _ = 0 := by
      funext z
      rfl

end Nivat.Algebra
