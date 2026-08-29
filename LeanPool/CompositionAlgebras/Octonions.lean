/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Tactic.NormNum


/-!
# The Octonion Algebra

The **octonions** O are the unique 8-dimensional normed division algebra
(Hurwitz 1898). They are non-associative and non-commutative.

## Role in the program

The Jordan-von Neumann-Wigner classification (1934) says all simple formally
real Jordan algebras are built from the four normed division algebras R, C, H, O
plus spin factors. The exceptional Jordan algebra h_3(O) is the unique Jordan
algebra that:
- Cannot embed in any C*-algebra (non-special)
- Cannot participate in any composite system (Barnum-Graydon-Wilce 2020)
- Has automorphism group F_4, which contains the SM gauge group

## Main definitions

* `Octonion` -- the octonion type as an 8-dim real algebra
* `Octonion.mul` -- the non-associative multiplication
* `Octonion.conj` -- the octonionic conjugation
* `Octonion.normSq` -- the norm-squared (composition algebra property)
* `Octonion.imagUnit` -- the 7 imaginary unit octonions (Fano plane)

## Main results

* `non_associative` -- octonion multiplication is not associative
* `norm_multiplicative` -- |ab| = |a||b|
* `CompositionAlgebra.left_alternative`, `CompositionAlgebra.right_alternative` -- the
  generic composition-algebra laws specialize to octonions via their instance

Hurwitz's classification, `Aut(𝕆) = G₂`, and `S⁶ = G₂/SU(3)` are *not* stated here:
they were carried as custom `axiom` declarations in the source tree and were dropped
on the way in, since this tree admits no custom axioms and nothing consumed them.
★ Of those three, Hurwitz's classification is since 2026-08-23 a *theorem* of this tree
(`Composition/Classification.lean`, `hurwitz_classification`, axioms `[]`) rather than a
dropped axiom. The other two remain unstated.

## References

* Baez, "The Octonions," Bull. AMS 39 (2002), arXiv:math/0105155
* Hurwitz, "Uber die Composition der quadratischen Formen von beliebig vielen Variablen," 1898
-/

noncomputable section

/-- The octonion algebra, represented as R^8.
    Basis: e_0 = 1 (real unit), e_1 through e_7 (imaginary units). -/
structure Octonion where
  /-- The 8 real components. -/
  coords : Fin 8 → ℝ

namespace Octonion

instance : Zero Octonion := ⟨⟨fun _ => 0⟩⟩
instance : Add Octonion := ⟨fun a b => ⟨fun i => a.coords i + b.coords i⟩⟩
instance : Neg Octonion := ⟨fun a => ⟨fun i => -(a.coords i)⟩⟩
instance : SMul ℝ Octonion := ⟨fun r a => ⟨fun i => r * a.coords i⟩⟩

@[ext]
theorem ext {a b : Octonion} (h : ∀ i, a.coords i = b.coords i) : a = b := by
  cases a; cases b; congr; funext i; exact h i

@[simp] lemma zero_coords (i : Fin 8) : (0 : Octonion).coords i = 0 := rfl
@[simp] lemma add_coords (a b : Octonion) (i : Fin 8) :
    (a + b).coords i = a.coords i + b.coords i := rfl

@[simp] lemma smul_coords (r : ℝ) (a : Octonion) (i : Fin 8) :
    (r • a).coords i = r * a.coords i := rfl
@[simp] lemma neg_coords (a : Octonion) (i : Fin 8) : (-a).coords i = -(a.coords i) := rfl

/-- The real unit octonion e_0 = (1, 0, 0, 0, 0, 0, 0, 0). -/
def one : Octonion := ⟨fun i => if i = 0 then 1 else 0⟩

/-- The i-th basis octonion e_i. -/
def basisVec (i : Fin 8) : Octonion := ⟨fun j => if j = i then 1 else 0⟩

/-- Octonionic multiplication. Non-associative, non-commutative.
    Defined via the Fano plane multiplication table (Baez convention).
    Triples: (1,2,4), (2,3,5), (3,4,6), (4,5,7), (5,6,1), (6,7,2), (7,1,3).
    For each triple (i,j,k): e_i * e_j = e_k (cyclic positive), e_j * e_i = -e_k.
    e_0 is the two-sided identity; e_i^2 = -e_0 for i > 0.
    Extended bilinearly: (sum a_i e_i) * (sum b_j e_j) = sum a_i b_j (e_i * e_j). -/
def mul (a b : Octonion) : Octonion where
  coords k :=
    if k.val = 0 then
      a.coords 0 * b.coords 0 - a.coords 1 * b.coords 1 - a.coords 2 * b.coords 2 -
        a.coords 3 * b.coords 3 - a.coords 4 * b.coords 4 - a.coords 5 * b.coords 5 -
          a.coords 6 * b.coords 6 - a.coords 7 * b.coords 7
    else if k.val = 1 then
      a.coords 0 * b.coords 1 + a.coords 1 * b.coords 0 + a.coords 2 * b.coords 4 -
        a.coords 4 * b.coords 2 + a.coords 3 * b.coords 7 - a.coords 7 * b.coords 3 +
          a.coords 5 * b.coords 6 - a.coords 6 * b.coords 5
    else if k.val = 2 then
      a.coords 0 * b.coords 2 + a.coords 2 * b.coords 0 + a.coords 4 * b.coords 1 -
        a.coords 1 * b.coords 4 + a.coords 3 * b.coords 5 - a.coords 5 * b.coords 3 +
          a.coords 6 * b.coords 7 - a.coords 7 * b.coords 6
    else if k.val = 3 then
      a.coords 0 * b.coords 3 + a.coords 3 * b.coords 0 + a.coords 5 * b.coords 2 -
        a.coords 2 * b.coords 5 + a.coords 4 * b.coords 6 - a.coords 6 * b.coords 4 +
          a.coords 7 * b.coords 1 - a.coords 1 * b.coords 7
    else if k.val = 4 then
      a.coords 0 * b.coords 4 + a.coords 4 * b.coords 0 + a.coords 1 * b.coords 2 -
        a.coords 2 * b.coords 1 + a.coords 6 * b.coords 3 - a.coords 3 * b.coords 6 +
          a.coords 5 * b.coords 7 - a.coords 7 * b.coords 5
    else if k.val = 5 then
      a.coords 0 * b.coords 5 + a.coords 5 * b.coords 0 + a.coords 2 * b.coords 3 -
        a.coords 3 * b.coords 2 + a.coords 7 * b.coords 4 - a.coords 4 * b.coords 7 +
          a.coords 6 * b.coords 1 - a.coords 1 * b.coords 6
    else if k.val = 6 then
      a.coords 0 * b.coords 6 + a.coords 6 * b.coords 0 + a.coords 3 * b.coords 4 -
        a.coords 4 * b.coords 3 + a.coords 1 * b.coords 5 - a.coords 5 * b.coords 1 +
          a.coords 7 * b.coords 2 - a.coords 2 * b.coords 7
    else
      a.coords 0 * b.coords 7 + a.coords 7 * b.coords 0 + a.coords 4 * b.coords 5 -
        a.coords 5 * b.coords 4 + a.coords 2 * b.coords 6 - a.coords 6 * b.coords 2 +
          a.coords 1 * b.coords 3 - a.coords 3 * b.coords 1

instance : Mul Octonion where mul := mul

/-- Octonionic conjugation: a* = 2 Re(a) - a.
    Equivalently: conjugate flips the sign of all imaginary components. -/
def conj (a : Octonion) : Octonion :=
  ⟨fun i => if i = 0 then a.coords 0 else -(a.coords i)⟩

/-- The real part of an octonion. -/
def re (a : Octonion) : ℝ := a.coords 0

/-- The norm-squared: N(a) = a * a* = sum of squares of components. -/
def normSq (a : Octonion) : ℝ := Finset.univ.sum fun i => (a.coords i) ^ 2

/-- The 7 imaginary unit octonions e_1, ..., e_7. -/
def imagUnit (i : Fin 7) : Octonion := basisVec ⟨i.val + 1, by omega⟩

-- Fundamental properties

/-- Octonionic multiplication has a two-sided identity. -/
theorem mul_one' (a : Octonion) : mul a one = a := by
  ext i; fin_cases i <;> simp [mul, one]

theorem one_mul' (a : Octonion) : mul one a = a := by
  ext i; fin_cases i <;> simp [mul, one]

/-- Octonions are NOT associative. There exist a, b, c with (ab)c != a(bc). -/
theorem non_associative : ∃ (a b c : Octonion),
    mul (mul a b) c ≠ mul a (mul b c) := by
  refine ⟨basisVec 1, basisVec 2, basisVec 3, ?_⟩
  intro h
  have h6 := congr_arg (fun x => x.coords 6) h
  simp [mul, basisVec] at h6
  linarith

-- Eight-square identity (Degen) expanded component-wise
/-- The norm is multiplicative: N(ab) = N(a) N(b).
    This is the composition algebra property, equivalent to Hurwitz's theorem. -/
theorem norm_multiplicative (a b : Octonion) :
    normSq (mul a b) = normSq a * normSq b := by
  simp only [normSq, Fin.sum_univ_eight, mul, Fin.isValue, Fin.val_zero, Fin.val_one]
  norm_num; ring

/-- Octonions form a division algebra: ab = 0 implies a = 0 or b = 0. -/
theorem mul_eq_zero_iff (a b : Octonion) :
    mul a b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · intro hab
    have h_norm : normSq a * normSq b = 0 := by
      rw [← norm_multiplicative]
      have : ∀ i, (mul a b).coords i = 0 := fun i => by
        have := congr_arg (·.coords i) hab; simpa using this
      simp only [normSq, this, Fin.sum_univ_eight]; norm_num
    rcases mul_eq_zero.mp h_norm with ha | hb
    · left; ext i
      have h_le : (a.coords i) ^ 2 ≤ normSq a :=
        Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have : (a.coords i) ^ 2 = 0 := by linarith [sq_nonneg (a.coords i)]
      simpa [sq_eq_zero_iff] using this
    · right; ext i
      have h_le : (b.coords i) ^ 2 ≤ normSq b :=
        Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have : (b.coords i) ^ 2 = 0 := by linarith [sq_nonneg (b.coords i)]
      simpa [sq_eq_zero_iff] using this
  · rintro (rfl | rfl) <;> ext i <;> fin_cases i <;> simp [mul]

-- Anti-involution expanded component-wise
/-- Conjugation is an anti-involution: (ab)* = b* a*. -/
theorem conj_mul (a b : Octonion) :
    conj (mul a b) = mul (conj b) (conj a) := by
  ext i; fin_cases i <;> simp [mul, conj, Fin.isValue] <;> ring

/-- Conjugation is involutive: a** = a. -/
theorem conj_conj (a : Octonion) : conj (conj a) = a := by
  ext i; simp only [conj]; split_ifs with h <;> simp_all

-- Norm-squared identity expanded component-wise
/-- a * a* = N(a) * 1. -/
theorem mul_conj (a : Octonion) :
    mul a (conj a) = normSq a • one := by
  ext i
  fin_cases i <;>
    simp [mul, conj, normSq, one, HSMul.hSMul, SMul.smul, Fin.sum_univ_eight] <;>
      ring

-- Bilinearity of octonionic multiplication, used to build the composition-algebra instance.

theorem mul_add' (a b c : Octonion) : mul a (b + c) = mul a b + mul a c := by
  ext i; fin_cases i <;> simp [mul, add_coords, Fin.isValue] <;> ring

theorem add_mul' (a b c : Octonion) : mul (a + b) c = mul a c + mul b c := by
  ext i; fin_cases i <;> simp [mul, add_coords, Fin.isValue] <;> ring

theorem smul_mul (r : ℝ) (a b : Octonion) : mul (r • a) b = r • mul a b := by
  ext i; fin_cases i <;> simp [mul, smul_coords, Fin.isValue] <;> ring

theorem mul_smul' (r : ℝ) (a b : Octonion) : mul a (r • b) = r • mul a b := by
  ext i; fin_cases i <;> simp [mul, smul_coords, Fin.isValue] <;> ring

end Octonion
