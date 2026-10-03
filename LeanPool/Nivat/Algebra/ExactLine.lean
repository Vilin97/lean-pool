/-
Copyright (c) 2026 Boon Suan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boon Suan Ho
-/

module

public import LeanPool.Nivat.Algebra.Action
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.Int.LeastGreatest
public import Lean.Elab.Tactic.Omega

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
# The exact annihilator ideal of a one-sided periodic configuration

The normalized lattice-basis form of Theorem 4.1 (`thm:exact-ideal`) is
`exact_line_in_basis`. A nonzero configuration
with a positive period along the first basis vector and vanishing on negative
rows has a principal Laurent annihilator ideal. Its generator is a monic
nonconstant divisor of the horizontal period polynomial.

First, `exists_horizontal_period_generator` constructs the exact one-variable
generator. On the kernel of an irreducible horizontal polynomial, Bézout's
identity makes every coprime coefficient injective. Evaluating a transverse
relation at the first nonzero row then proves that the irreducible polynomial
divides each transverse coefficient.

The theorem `horizontal_generator_dvd_coefficients` iterates this argument by
degree. If the generator is `π * ψ`, apply the first-row argument to `ψ(T)d`,
then divide each transverse coefficient by `π` and apply the induction to
`π(T)d`, whose exact horizontal generator is `ψ`. Thus the argument accounts
for every factor multiplicity. Clearing negative horizontal exponents by a
monomial unit extends coefficient divisibility to all Laurent filters.
Finally, exponent reindexing transports the equality through the lattice basis.
-/

public section

namespace Nivat.Algebra

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): the first coordinate unit vector in the normalized
lattice basis. -/
def horizontal : Lattice := (1, 0)

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): every entry on a specified full integer row
vanishes. -/
def RowZero (d : Configuration ℚ) (b : ℤ) : Prop := ∀ a : ℤ, d (a, b) = 0

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): the ideal of ordinary polynomials whose horizontal
operators annihilate the configuration. -/
private noncomputable def horizontalAnnihilator (d : Configuration ℚ) : Ideal (Polynomial ℚ) where
  carrier := {p | act (lineEval horizontal p) d = 0}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq
    change act (lineEval horizontal (p + q)) d = 0
    rw [map_add, act_add, hp, hq, add_zero]
  smul_mem' := by
    intro a p hp
    change act (lineEval horizontal (a * p)) d = 0
    rw [map_mul, act_mul, hp, act_config_zero]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): normalize the generator of a nonzero horizontal
annihilator ideal to obtain a monic polynomial with exact one-variable divisibility. -/
theorem exists_monic_horizontal_generator {d : Configuration ℚ}
    (hex : ∃ p : Polynomial ℚ, p ≠ 0 ∧ act (lineEval horizontal p) d = 0) :
    ∃ φ : Polynomial ℚ, φ.Monic ∧
      ∀ p : Polynomial ℚ, act (lineEval horizontal p) d = 0 ↔ φ ∣ p := by
  classical
  let I := horizontalAnnihilator d
  let g := Submodule.IsPrincipal.generator I
  have hgexact (p : Polynomial ℚ) : act (lineEval horizontal p) d = 0 ↔ g ∣ p :=
    Submodule.IsPrincipal.mem_iff_generator_dvd I
  have hg : g ≠ 0 := by
    obtain ⟨p, hp, hann⟩ := hex
    intro hz
    have hdiv := (hgexact p).mp hann
    rw [hz, zero_dvd_iff] at hdiv
    exact hp hdiv
  refine ⟨normalize g, Polynomial.monic_normalize hg, fun p => ?_⟩
  rw [normalize_dvd_iff]
  exact hgexact p

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): a positive horizontal period gives a monic,
nonconstant exact horizontal generator dividing the period polynomial. -/
theorem exists_horizontal_period_generator {d : Configuration ℚ} (hd : d ≠ 0)
    {q : ℕ} (hq : 0 < q) (hperiod : IsPeriod d ((q : ℤ), 0)) :
    ∃ φ : Polynomial ℚ, φ.Monic ∧ 0 < φ.natDegree ∧
      φ ∣ Polynomial.X ^ q - 1 ∧
      ∀ p : Polynomial ℚ, act (lineEval horizontal p) d = 0 ↔ φ ∣ p := by
  have hpow : act (lineEval horizontal (Polynomial.X ^ q - 1)) d = 0 := by
    rw [act_lineEval_X_pow_sub_one, difference_eq_zero_iff]
    simpa [horizontal] using hperiod
  have hpne : (Polynomial.X : Polynomial ℚ) ^ q - 1 ≠ 0 := by
    simpa using Polynomial.X_pow_sub_C_ne_zero hq (1 : ℚ)
  obtain ⟨φ, hmonic, hexact⟩ := exists_monic_horizontal_generator ⟨_, hpne, hpow⟩
  refine ⟨φ, hmonic, ?_, (hexact _).mp hpow, hexact⟩
  apply Nat.pos_of_ne_zero
  intro hdeg
  have hone := Polynomial.eq_one_of_monic_natDegree_zero hmonic hdeg
  have hz := (hexact 1).mpr (by rw [hone])
  simp only [map_one, act_one] at hz
  exact hd hz

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): evaluation of a polynomial monomial gives its
coefficient at the scaled lattice exponent. -/
theorem lineEval_monomial (v : Lattice) (n : ℕ) (a : ℚ) :
    lineEval v (Polynomial.monomial n a) = AddMonoidAlgebra.single (n • v) a := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, lineEval_C, lineEval_X_pow]
  simp [monomial]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): a horizontal polynomial preserves a zero row
because its shifts stay on that row. -/
theorem rowZero_horizontal_act (p : Polynomial ℚ) {d : Configuration ℚ} {b : ℤ}
    (hd : RowZero d b) : RowZero (act (lineEval horizontal p) d) b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro a
    simp only [map_add, act_add, Pi.add_apply]
    rw [hp a, hq a, zero_add]
  | monomial n r =>
    intro a
    rw [lineEval_monomial, act_single]
    change r * d ((a, b) + n • horizontal) = 0
    simpa [horizontal] using
      (show r * d (a + (n : ℤ), b) = 0 by rw [hd, mul_zero])

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): Bézout coefficients for coprime horizontal
polynomials recover a row from their two outputs. -/
private theorem rowZero_of_isCoprime {p q : Polynomial ℚ} (hpq : IsCoprime p q)
    {d : Configuration ℚ} {b : ℤ}
    (hp : RowZero (act (lineEval horizontal p) d) b)
    (hq : RowZero (act (lineEval horizontal q) d) b) : RowZero d b := by
  obtain ⟨a, c, hac⟩ := hpq
  have hsum := congrArg (fun f : Polynomial ℚ => act (lineEval horizontal f) d) hac
  simp only [map_add, map_mul, act_add, act_mul, map_one, act_one] at hsum
  have ha := rowZero_horizontal_act a hp
  have hc := rowZero_horizontal_act c hq
  intro i
  have hi := congrFun hsum (i, b)
  change act (lineEval horizontal a) (act (lineEval horizontal p) d) (i, b) +
    act (lineEval horizontal c) (act (lineEval horizontal q) d) (i, b) = d (i, b) at hi
  rw [ha i, hc i, zero_add] at hi
  exact hi.symm

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): a polynomial not divisible by an irreducible
horizontal relation acts injectively on each row in the relation's kernel. -/
private theorem rowZero_of_irreducible {π p : Polynomial ℚ} (hπ : Irreducible π)
    (hdiv : ¬π ∣ p) {d : Configuration ℚ} {b : ℤ}
    (hker : act (lineEval horizontal π) d = 0)
    (hp : RowZero (act (lineEval horizontal p) d) b) : RowZero d b := by
  apply rowZero_of_isCoprime (hπ.coprime_iff_not_dvd.mpr hdiv) ?_ hp
  intro a
  rw [hker]
  rfl

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): a nonzero configuration vanishing below some
integer height has a first nonzero row. -/
private theorem exists_first_nonzero_row {d : Configuration ℚ} (hd : d ≠ 0)
    (hbelow : ∃ B : ℤ, ∀ b < B, RowZero d b) :
    ∃ b : ℤ, ¬RowZero d b ∧ ∀ j < b, RowZero d j := by
  classical
  obtain ⟨B, hB⟩ := hbelow
  have hex : ∃ b : ℤ, ¬RowZero d b := by
    by_contra h
    apply hd
    funext z
    have hall : ∀ b : ℤ, RowZero d b := by simpa using h
    exact hall z.2 z.1
  obtain ⟨b, hb, hleast⟩ := Int.exists_least_of_bdd
    (P := fun b => ¬RowZero d b) ⟨B, fun j hj => by
      by_contra hlt
      exact hj (hB j (lt_of_not_ge hlt))⟩ hex
  refine ⟨b, hb, fun j hj => ?_⟩
  by_contra hz
  exact (not_le_of_gt hj) (hleast j hz)

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): every multiple of a horizontal annihilator also
annihilates the configuration. -/
private theorem act_lineEval_eq_zero_of_dvd {π p : Polynomial ℚ} (hdiv : π ∣ p)
    {d : Configuration ℚ} (hker : act (lineEval horizontal π) d = 0) :
    act (lineEval horizontal p) d = 0 := by
  obtain ⟨r, rfl⟩ := hdiv
  rw [mul_comm π r, map_mul, act_mul, hker, act_config_zero]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): two Laurent operators commute because
multiplication in the Laurent ring is commutative. -/
theorem act_comm (f g : Laurent) (d : Configuration ℚ) :
    act f (act g d) = act g (act f d) := by
  rw [← act_mul, mul_comm, act_mul]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): a Laurent operator distributes over a finite sum
of configurations. -/
theorem act_config_finset_sum {ι : Type*} (f : Laurent) (S : Finset ι)
    (d : ι → Configuration ℚ) : act f (∑ j ∈ S, d j) = ∑ j ∈ S, act f (d j) :=
  map_sum (actionHom f) d S

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): a Laurent operator commutes with a finite sum of
horizontally filtered vertical shifts. -/
private theorem act_transverse_sum (a : Laurent) (S : Finset ℤ) (p : ℤ → Polynomial ℚ)
    (d : Configuration ℚ) :
    act a (∑ j ∈ S, act (lineEval horizontal (p j)) (shift (0, j) d)) =
      ∑ j ∈ S, act (lineEval horizontal (p j)) (shift (0, j) (act a d)) := by
  rw [act_config_finset_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [act_comm, act_shift]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): on the kernel of an irreducible horizontal
polynomial, every coefficient of a vanishing transverse relation is divisible by that
polynomial. The greatest nondivisible coefficient is isolated at the first nonzero row,
contradicting Bézout. -/
theorem irreducible_dvd_coefficients_of_sum_eq_zero
    {π : Polynomial ℚ} (hπ : Irreducible π)
    {d : Configuration ℚ} (hd : d ≠ 0)
    (hbelow : ∃ B : ℤ, ∀ b < B, RowZero d b)
    (hker : act (lineEval horizontal π) d = 0)
    (S : Finset ℤ) (p : ℤ → Polynomial ℚ)
    (hsum : (∑ j ∈ S, act (lineEval horizontal (p j)) (shift (0, j) d)) = 0) :
    ∀ j ∈ S, π ∣ p j := by
  classical
  intro j hj
  by_contra hbad
  let bad := S.filter (fun l => ¬π ∣ p l)
  have hne : bad.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, hbad⟩⟩
  let k := bad.max' hne
  have hkbad : k ∈ bad := Finset.max'_mem bad hne
  have hkS : k ∈ S := (Finset.mem_filter.mp hkbad).1
  have hkn : ¬π ∣ p k := (Finset.mem_filter.mp hkbad).2
  have hhigh : ∀ l ∈ S, k < l → π ∣ p l := by
    intro l hl hkl
    by_contra hn
    have hle : l ≤ k := Finset.le_max' bad l (Finset.mem_filter.mpr ⟨hl, hn⟩)
    exact (not_le_of_gt hkl) hle
  obtain ⟨b, hb, hfirst⟩ := exists_first_nonzero_row hd hbelow
  apply hb
  apply rowZero_of_irreducible hπ hkn hker
  intro i
  have hterm : ∀ l ∈ S, l ≠ k →
      act (lineEval horizontal (p l)) (shift (0, l) d) (i, b - k) = 0 := by
    intro l hl hlk
    rcases lt_or_gt_of_ne hlk with hlk | hkl
    · have hz := rowZero_horizontal_act (p l) (hfirst (b - k + l) (by omega)) i
      simpa only [act_shift, shift_apply, Prod.mk_add_mk, add_zero] using hz
    · have hz := act_lineEval_eq_zero_of_dvd (hhigh l hl hkl) hker
      rw [act_shift, hz]
      rfl
  have hi := congrFun hsum (i, b - k)
  simp only [Finset.sum_apply, Pi.zero_apply] at hi
  rw [Finset.sum_eq_single k hterm (fun hk => (hk hkS).elim)] at hi
  simpa only [act_shift, shift_apply, Prod.mk_add_mk, add_zero, sub_add_cancel] using hi

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): every coefficient of a vanishing transverse
relation is divisible by the exact horizontal generator. Degree induction removes an irreducible
factor from both the generator and the coefficients, including its full multiplicity. -/
theorem horizontal_generator_dvd_coefficients
    (φ : Polynomial ℚ) (hφ : φ ≠ 0) (d : Configuration ℚ)
    (hexact : ∀ p : Polynomial ℚ, act (lineEval horizontal p) d = 0 ↔ φ ∣ p)
    (hbelow : ∃ B : ℤ, ∀ b < B, RowZero d b)
    (S : Finset ℤ) (p : ℤ → Polynomial ℚ)
    (hsum : (∑ j ∈ S, act (lineEval horizontal (p j)) (shift (0, j) d)) = 0) :
    ∀ j ∈ S, φ ∣ p j := by
  classical
  by_cases hunit : IsUnit φ
  · exact fun _ _ => hunit.dvd
  obtain ⟨π, hπ, ψ, hφeq⟩ := WfDvdMonoid.exists_irreducible_factor hunit hφ
  have hψ : ψ ≠ 0 := by
    intro hz
    apply hφ
    rw [hφeq, hz, mul_zero]
  have hdeg : ψ.natDegree < φ.natDegree := by
    have hm := Polynomial.natDegree_mul hπ.ne_zero hψ
    have hp := hπ.natDegree_pos
    rw [← hφeq] at hm
    omega
  let e := act (lineEval horizontal ψ) d
  have he : e ≠ 0 := by
    intro hz
    have hdiv := (hexact ψ).mp hz
    have hle := Polynomial.natDegree_le_of_dvd hdiv hψ
    omega
  have heker : act (lineEval horizontal π) e = 0 := by
    change act (lineEval horizontal π) (act (lineEval horizontal ψ) d) = 0
    rw [← act_mul, ← map_mul, ← hφeq]
    exact (hexact φ).mpr dvd_rfl
  have hebelow : ∃ B : ℤ, ∀ b < B, RowZero e b := by
    obtain ⟨B, hB⟩ := hbelow
    exact ⟨B, fun b hb => rowZero_horizontal_act ψ (hB b hb)⟩
  have hesum : (∑ j ∈ S, act (lineEval horizontal (p j)) (shift (0, j) e)) = 0 := by
    rw [← act_transverse_sum, hsum, act_config_zero]
  have hdiv := irreducible_dvd_coefficients_of_sum_eq_zero hπ he hebelow heker S p hesum
  let d₁ := act (lineEval horizontal π) d
  have h₁exact : ∀ r : Polynomial ℚ,
      act (lineEval horizontal r) d₁ = 0 ↔ ψ ∣ r := by
    intro r
    change act (lineEval horizontal r) (act (lineEval horizontal π) d) = 0 ↔ ψ ∣ r
    rw [← act_mul, ← map_mul, hexact, hφeq, mul_comm r π,
      mul_dvd_mul_iff_left hπ.ne_zero]
  have h₁below : ∃ B : ℤ, ∀ b < B, RowZero d₁ b := by
    obtain ⟨B, hB⟩ := hbelow
    exact ⟨B, fun b hb => rowZero_horizontal_act π (hB b hb)⟩
  have h₁sum : (∑ j ∈ S, act (lineEval horizontal (p j / π)) (shift (0, j) d₁)) = 0 := by
    calc
      _ = ∑ j ∈ S, act (lineEval horizontal (p j)) (shift (0, j) d) := by
        apply Finset.sum_congr rfl
        intro j hj
        change act (lineEval horizontal (p j / π))
          (shift (0, j) (act (lineEval horizontal π) d)) = _
        rw [← act_shift, ← act_mul, ← map_mul, mul_comm (p j / π) π,
          EuclideanDomain.mul_div_cancel' hπ.ne_zero (hdiv j hj)]
      _ = 0 := hsum
  have ih := horizontal_generator_dvd_coefficients ψ hψ d₁ h₁exact h₁below S
    (fun j => p j / π) h₁sum
  intro j hj
  have h := mul_dvd_mul_left π (ih j hj)
  simpa only [← hφeq, EuclideanDomain.mul_div_cancel' hπ.ne_zero (hdiv j hj)] using h
termination_by φ.natDegree
decreasing_by exact hdeg

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): Laurent polynomials in the transverse variable
with ordinary horizontal polynomial coefficients. -/
private abbrev TransversePolynomial := AddMonoidAlgebra (Polynomial ℚ) ℤ

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): integer transverse exponents act by their vertical
Laurent monomials. -/
private noncomputable def verticalRepresentation : Multiplicative ℤ →* Laurent where
  toFun j := monomial (0, j.toAdd)
  map_one' := monomial_zero
  map_mul' i j := by rw [monomial_mul]; rfl

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): evaluate horizontal polynomial coefficients and
vertical Laurent monomials in the lattice ring. -/
private noncomputable def transverseEval : TransversePolynomial →+* Laurent :=
  AddMonoidAlgebra.liftNCRingHom (lineEval horizontal) verticalRepresentation
    (fun _ _ => Commute.all _ _)

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): a single transverse term evaluates to its
horizontal polynomial times its vertical monomial. -/
private theorem transverseEval_single (j : ℤ) (p : Polynomial ℚ) :
    transverseEval (AddMonoidAlgebra.single j p) =
      lineEval horizontal p * monomial (0, j) := by
  simp [transverseEval, verticalRepresentation]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): evaluation of a transverse Laurent polynomial is
its finite sum over supported exponents. -/
private theorem transverseEval_eq_sum (F : TransversePolynomial) :
    transverseEval F = ∑ j ∈ F.coeff.support,
      lineEval horizontal (F.coeff j) * monomial (0, j) := by
  conv_lhs => rw [← F.sum_coeff_single]
  simp only [Finsupp.sum, map_sum, transverseEval_single]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): the action distributes over a finite sum of
Laurent filters. -/
theorem act_filter_finset_sum {ι : Type*} (S : Finset ι) (f : ι → Laurent)
    (d : Configuration ℚ) : act (∑ j ∈ S, f j) d = ∑ j ∈ S, act (f j) d := by
  change actionHom (∑ j ∈ S, f j) d = _
  rw [map_sum]
  exact LinearMap.sum_apply _ _ _

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): the evaluated transverse polynomial acts as a
finite sum of horizontally filtered vertical shifts. -/
private theorem act_transverseEval (F : TransversePolynomial) (d : Configuration ℚ) :
    act (transverseEval F) d = ∑ j ∈ F.coeff.support,
      act (lineEval horizontal (F.coeff j)) (shift (0, j) d) := by
  rw [transverseEval_eq_sum, act_filter_finset_sum]
  simp only [act_mul, act_monomial]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): coefficientwise division constructs a Laurent
multiplier when every transverse coefficient is divisible by the horizontal generator. -/
private theorem lineEval_dvd_transverseEval (φ : Polynomial ℚ) (hφ : φ ≠ 0)
    (F : TransversePolynomial) (hdiv : ∀ j ∈ F.coeff.support, φ ∣ F.coeff j) :
    lineEval horizontal φ ∣ transverseEval F := by
  classical
  let G : TransversePolynomial := AddMonoidAlgebra.ofCoeff
    (F.coeff.mapRange (fun p => p / φ) (by simp))
  have hall (j : ℤ) : φ ∣ F.coeff j := by
    by_cases hj : j ∈ F.coeff.support
    · exact hdiv j hj
    · rw [Finsupp.notMem_support_iff.mp hj]
      exact dvd_zero φ
  have heq : F = AddMonoidAlgebra.single 0 φ * G := by
    apply AddMonoidAlgebra.ext
    apply Finsupp.ext
    intro j
    simp only [AddMonoidAlgebra.coeff_single_zero_mul]
    change F.coeff j = φ * (F.coeff j / φ)
    exact (EuclideanDomain.mul_div_cancel' hφ (hall j)).symm
  refine ⟨transverseEval G, ?_⟩
  rw [heq, map_mul, transverseEval_single]
  change (lineEval horizontal φ * monomial (0 : Lattice)) * transverseEval G = _
  rw [monomial_zero, mul_one]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): exact horizontal annihilation and one-sided
vanishing give exact Laurent divisibility for the transverse polynomial presentation. -/
private theorem transverseEval_annihilates_iff (φ : Polynomial ℚ) (hφ : φ ≠ 0)
    (d : Configuration ℚ)
    (hexact : ∀ p : Polynomial ℚ, act (lineEval horizontal p) d = 0 ↔ φ ∣ p)
    (hbelow : ∃ B : ℤ, ∀ b < B, RowZero d b) (F : TransversePolynomial) :
    act (transverseEval F) d = 0 ↔ lineEval horizontal φ ∣ transverseEval F := by
  constructor
  · intro hF
    apply lineEval_dvd_transverseEval φ hφ F
    apply horizontal_generator_dvd_coefficients φ hφ d hexact hbelow
    rwa [← act_transverseEval]
  · rintro ⟨g, hg⟩
    rw [hg, mul_comm, act_mul, (hexact φ).mpr dvd_rfl, act_config_zero]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): a constant transverse coefficient equal to a
horizontal power evaluates to its lattice monomial. -/
private theorem transverseEval_horizontal (n : ℕ) :
    transverseEval (AddMonoidAlgebra.single 0 ((Polynomial.X : Polynomial ℚ) ^ n)) =
      monomial ((n : ℤ), 0) := by
  rw [transverseEval_single, lineEval_X_pow]
  change monomial (n • horizontal) * monomial (0 : Lattice) = _
  simp [horizontal]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): multiplication by a horizontal monomial clears all
negative horizontal exponents of an arbitrary Laurent filter, yielding a transverse polynomial
presentation. -/
private theorem exists_horizontal_clear (f : Laurent) :
    ∃ n : ℕ, ∃ F : TransversePolynomial,
      monomial ((n : ℤ), 0) * f = transverseEval F := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg =>
    obtain ⟨a, F, hF⟩ := hf
    obtain ⟨b, G, hG⟩ := hg
    refine ⟨a + b, AddMonoidAlgebra.single 0 (Polynomial.X ^ b) * F +
      AddMonoidAlgebra.single 0 (Polynomial.X ^ a) * G, ?_⟩
    rw [map_add, map_mul, map_mul, transverseEval_horizontal, transverseEval_horizontal,
      ← hF, ← hG, mul_add]
    simp only [← mul_assoc, monomial_mul, Prod.mk_add_mk, add_zero, Nat.cast_add, add_comm]
  | single h r =>
    obtain ⟨x, y⟩ := h
    let n := (-x).toNat
    have hx : 0 ≤ x + (n : ℤ) := by dsimp [n]; omega
    refine ⟨n, AddMonoidAlgebra.single y (Polynomial.monomial (x + n).toNat r), ?_⟩
    rw [transverseEval_single, lineEval_monomial]
    simp [monomial, horizontal, Int.toNat_of_nonneg hx, add_comm]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): clearing horizontal exponents and cancelling the
monomial unit extends exact coefficient divisibility to every Laurent filter. -/
theorem horizontal_annihilates_iff (φ : Polynomial ℚ) (hφ : φ ≠ 0)
    (d : Configuration ℚ)
    (hexact : ∀ p : Polynomial ℚ, act (lineEval horizontal p) d = 0 ↔ φ ∣ p)
    (hbelow : ∃ B : ℤ, ∀ b < B, RowZero d b) (f : Laurent) :
    act f d = 0 ↔ lineEval horizontal φ ∣ f := by
  constructor
  · intro hf
    obtain ⟨n, F, hF⟩ := exists_horizontal_clear f
    have hann : act (transverseEval F) d = 0 := by
      rw [← hF, act_mul, hf, act_config_zero]
    obtain ⟨g, hg⟩ := (transverseEval_annihilates_iff φ hφ d hexact hbelow F).mp hann
    let u := monomial ((n : ℤ), 0)
    let u' := monomial (-((n : ℤ), 0))
    have hinv : u' * u = 1 := by
      dsimp only [u', u]
      rw [monomial_mul, neg_add_cancel, monomial_zero]
    refine ⟨u' * g, ?_⟩
    calc
      f = u' * (u * f) := by rw [← mul_assoc, hinv, one_mul]
      _ = u' * (lineEval horizontal φ * g) := by rw [hF, hg]
      _ = lineEval horizontal φ * (u' * g) := by ac_rfl
  · rintro ⟨g, hg⟩
    rw [hg, mul_comm, act_mul, (hexact φ).mpr dvd_rfl, act_config_zero]

/-- Theorem 4.1 (`thm:exact-ideal`) in horizontal coordinates: the whole Laurent annihilator ideal
of the one-sided periodic configuration has a monic nonconstant horizontal generator dividing
the period polynomial. -/
theorem exact_horizontal_line {d : Configuration ℚ} (hd : d ≠ 0)
    {q : ℕ} (hq : 0 < q) (hperiod : IsPeriod d ((q : ℤ), 0))
    (hbelow : ∀ b < 0, RowZero d b) :
    ∃ φ : Polynomial ℚ, φ.Monic ∧ 0 < φ.natDegree ∧
      φ ∣ Polynomial.X ^ q - 1 ∧
      ∀ f : Laurent, act f d = 0 ↔ lineEval (1, 0) φ ∣ f := by
  obtain ⟨φ, hmonic, hdeg, hdiv, hexact⟩ := exists_horizontal_period_generator hd hq hperiod
  exact ⟨φ, hmonic, hdeg, hdiv,
    horizontal_annihilates_iff φ hmonic.ne_zero d hexact ⟨0, hbelow⟩⟩

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): an integer lattice basis reindexes exponents by an
algebra equivalence of the Laurent ring. -/
noncomputable def laurentReindex (e : Lattice ≃+ Lattice) : Laurent ≃ₐ[ℚ] Laurent :=
  AddMonoidAlgebra.domCongr ℚ ℚ e

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): exponent reindexing and configuration
precomposition give the same operator value at corresponding sites. -/
theorem act_reindex_apply (e : Lattice ≃+ Lattice) (f : Laurent)
    (d : Configuration ℚ) (z : Lattice) :
    act (laurentReindex e f) d (e z) = act f (d ∘ e) z := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, act_add, Pi.add_apply, hf, hg]
  | single h r =>
    simp [laurentReindex, AddMonoidAlgebra.domCongr_single, act_single,
      shift, Function.comp_apply, map_add]

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): annihilator equations are preserved in both
directions by a lattice basis change. -/
theorem act_reindex_eq_zero_iff (e : Lattice ≃+ Lattice) (f : Laurent)
    (d : Configuration ℚ) :
    act (laurentReindex e f) d = 0 ↔ act f (d ∘ e) = 0 := by
  constructor
  · intro h
    funext z
    rw [← act_reindex_apply, h]
    rfl
  · intro h
    funext z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [act_reindex_apply, h]
    rfl

/-- Auxiliary to Theorem 4.1 (`thm:exact-ideal`): a basis change takes evaluation along a vector to
evaluation along its image. -/
theorem laurentReindex_lineEval (e : Lattice ≃+ Lattice) (v : Lattice)
    (p : Polynomial ℚ) :
    laurentReindex e (lineEval v p) = lineEval (e v) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n r =>
    rw [lineEval_monomial, lineEval_monomial]
    change AddMonoidAlgebra.domCongr ℚ ℚ e (AddMonoidAlgebra.single (n • v) r) = _
    rw [AddMonoidAlgebra.domCongr_single, map_nsmul]

/-- Theorem 4.1 (`thm:exact-ideal`) in an arbitrary integer lattice basis. The first basis vector is
the primitive period direction; negative second coordinates lie in the vanishing half-plane. The
conclusion identifies every Laurent annihilator in the original lattice coordinates with a
multiple of the line generator. -/
theorem exact_line_in_basis (e : Lattice ≃+ Lattice) {d : Configuration ℚ}
    (hd : d ≠ 0) {q : ℕ} (hq : 0 < q)
    (hperiod : IsPeriod d (e ((q : ℤ), 0)))
    (hbelow : ∀ b < 0, ∀ a : ℤ, d (e (a, b)) = 0) :
    ∃ φ : Polynomial ℚ, φ.Monic ∧ 0 < φ.natDegree ∧
      φ ∣ Polynomial.X ^ q - 1 ∧
      ∀ f : Laurent, act f d = 0 ↔ lineEval (e (1, 0)) φ ∣ f := by
  have hd' : (d ∘ e) ≠ 0 := by
    intro hz
    apply hd
    funext z
    obtain ⟨w, rfl⟩ := e.surjective z
    exact congrFun hz w
  have hp' : IsPeriod (d ∘ e) ((q : ℤ), 0) := by
    intro z
    change d (e (z + ((q : ℤ), 0))) = d (e z)
    rw [map_add, hperiod]
  obtain ⟨φ, hm, hdeg, hdiv, hexact⟩ := exact_horizontal_line hd' hq hp' hbelow
  refine ⟨φ, hm, hdeg, hdiv, fun f => ?_⟩
  let g := (laurentReindex e).symm f
  calc
    act f d = 0 ↔ act g (d ∘ e) = 0 := by
      simpa only [g, AlgEquiv.apply_symm_apply] using act_reindex_eq_zero_iff e g d
    _ ↔ lineEval (1, 0) φ ∣ g := hexact g
    _ ↔ lineEval (e (1, 0)) φ ∣ f := by
      rw [← map_dvd_iff (laurentReindex e), laurentReindex_lineEval]
      simp only [g, AlgEquiv.apply_symm_apply]

end Nivat.Algebra
