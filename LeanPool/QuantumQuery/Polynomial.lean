/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
module

public import LeanPool.QuantumQuery.Algorithms
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The polynomial method for value and XOR query oracles

Ported from the corresponding upstream modules listed by the source sections below.
References beginning with `Source` name these retained sections.
-/

public section

section SourcePolynomialBoolean

/-!
# Real polynomials on the Boolean cube

The small algebra API behind the polynomial method (`SourceQuantumPolynomialMethod`):

* `bit b`, the `0/1` real value of a Boolean, and `evalBool p a`, the evaluation of a real
  multivariate polynomial at a Boolean point of the cube (any finite index type `ι`);
* `select i P₀ P₁ = (1 − Xᵢ)·P₀ + Xᵢ·P₁`, which on the cube evaluates to the polynomial
  selected by the `i`-th bit and raises the degree bound by one — the one operation an
  oracle query performs on an amplitude;
* `AmpPoly ι`, a pair of real polynomials representing the real and imaginary parts of a
  complex amplitude, with the complex-scalar action and sums needed to push an
  input-independent unitary through a representation.  Working with two real
  polynomials avoids any coefficient-ring map: `Complex.re` is not a ring homomorphism.

Everything is stated for arbitrary finite `ι`, including `Fin n`.
-/

namespace QuantumQueryComplexity

open MvPolynomial

/-! ## Bits and evaluation -/

/-- The real value of a Boolean: `1` for `true`, `0` for `false`. -/
@[expose]
def bit (b : Bool) : ℝ := if b then 1 else 0

@[simp] lemma bit_true : bit true = 1 := rfl
@[simp] lemma bit_false : bit false = 0 := rfl

lemma bit_nonneg (b : Bool) : 0 ≤ bit b := by cases b <;> simp
lemma bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> simp
lemma one_sub_bit (b : Bool) : 1 - bit b = bit (!b) := by cases b <;> simp

variable {ι : Type*}

/-- Evaluating a real multivariate polynomial at a Boolean point of the cube. -/
noncomputable def evalBool (p : MvPolynomial ι ℝ) (a : ι → Bool) : ℝ :=
  MvPolynomial.eval (fun i => bit (a i)) p

@[simp] lemma evalBool_C (c : ℝ) (a : ι → Bool) : evalBool (C c) a = c := by
  simp [evalBool]

@[simp] lemma evalBool_X (i : ι) (a : ι → Bool) : evalBool (X i) a = bit (a i) := by
  simp [evalBool]

@[simp] lemma evalBool_add (p q : MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (p + q) a = evalBool p a + evalBool q a := by
  simp [evalBool]

@[simp] lemma evalBool_sub (p q : MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (p - q) a = evalBool p a - evalBool q a := by
  simp [evalBool]

@[simp] lemma evalBool_neg (p : MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (-p) a = -evalBool p a := by
  simp [evalBool]

@[simp] lemma evalBool_mul (p q : MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (p * q) a = evalBool p a * evalBool q a := by
  simp [evalBool]

@[simp] lemma evalBool_pow (p : MvPolynomial ι ℝ) (k : ℕ) (a : ι → Bool) :
    evalBool (p ^ k) a = evalBool p a ^ k := by
  simp [evalBool]

@[simp] lemma evalBool_zero (a : ι → Bool) : evalBool (0 : MvPolynomial ι ℝ) a = 0 := by
  simp [evalBool]

@[simp] lemma evalBool_one (a : ι → Bool) : evalBool (1 : MvPolynomial ι ℝ) a = 1 := by
  simp [evalBool]

lemma evalBool_sum {κ : Type*} (s : Finset κ) (p : κ → MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (∑ k ∈ s, p k) a = ∑ k ∈ s, evalBool (p k) a := by
  simp [evalBool]

/-! ## Total-degree conveniences -/

lemma totalDegree_finsetSum_le {κ : Type*} (s : Finset κ) (p : κ → MvPolynomial ι ℝ)
    {d : ℕ} (h : ∀ k ∈ s, (p k).totalDegree ≤ d) : (∑ k ∈ s, p k).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_finsetSum s p).trans (Finset.sup_le h)

lemma totalDegree_C_mul_le (c : ℝ) (p : MvPolynomial ι ℝ) :
    (C c * p).totalDegree ≤ p.totalDegree :=
  (MvPolynomial.totalDegree_mul _ _).trans (by simp)

lemma totalDegree_sq_le (p : MvPolynomial ι ℝ) {d : ℕ} (h : p.totalDegree ≤ d) :
    (p ^ 2).totalDegree ≤ 2 * d :=
  (MvPolynomial.totalDegree_pow _ _).trans (by omega)

/-! ## The selector -/

/-- `select i P₀ P₁ = (1 − Xᵢ)·P₀ + Xᵢ·P₁`: on the cube, `P₁` where the `i`-th bit is set
and `P₀` where it is not. -/
noncomputable def select (i : ι) (P₀ P₁ : MvPolynomial ι ℝ) : MvPolynomial ι ℝ :=
  (1 - X i) * P₀ + X i * P₁

lemma evalBool_select (i : ι) (P₀ P₁ : MvPolynomial ι ℝ) (a : ι → Bool) :
    evalBool (select i P₀ P₁) a = if a i then evalBool P₁ a else evalBool P₀ a := by
  simp only [select, evalBool_add, evalBool_mul, evalBool_sub, evalBool_one, evalBool_X]
  cases a i <;> simp

lemma totalDegree_select_le (i : ι) {P₀ P₁ : MvPolynomial ι ℝ} {t : ℕ}
    (h₀ : P₀.totalDegree ≤ t) (h₁ : P₁.totalDegree ≤ t) :
    (select i P₀ P₁).totalDegree ≤ t + 1 := by
  have hX : (X i : MvPolynomial ι ℝ).totalDegree ≤ 1 := le_of_eq (totalDegree_X i)
  have h1X : ((1 : MvPolynomial ι ℝ) - X i).totalDegree ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · simp
    · rw [totalDegree_neg]; exact hX
  refine (totalDegree_add _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_mul _ _).trans (by omega)
  · exact (totalDegree_mul _ _).trans (by omega)

/-! ## Amplitude polynomials

A complex amplitude, as a function of the input, is represented by two real polynomials:
its real and its imaginary part. -/

/-- A pair of real polynomials, standing for `re + im·I`. -/
structure AmpPoly (ι : Type*) where
  /-- The real part. -/
  re : MvPolynomial ι ℝ
  /-- The imaginary part. -/
  im : MvPolynomial ι ℝ

namespace AmpPoly

variable (P : AmpPoly ι)

/-- The complex value at a Boolean point. -/
@[expose]
noncomputable def evalC (P : AmpPoly ι) (a : ι → Bool) : ℂ :=
  ⟨evalBool P.re a, evalBool P.im a⟩

@[simp] lemma evalC_re (a : ι → Bool) : (P.evalC a).re = evalBool P.re a := rfl
@[simp] lemma evalC_im (a : ι → Bool) : (P.evalC a).im = evalBool P.im a := rfl

/-- Both parts have total degree at most `t`. -/
def DegLe (P : AmpPoly ι) (t : ℕ) : Prop := P.re.totalDegree ≤ t ∧ P.im.totalDegree ≤ t

lemma DegLe.mono {P : AmpPoly ι} {s t : ℕ} (h : P.DegLe s) (hst : s ≤ t) : P.DegLe t :=
  ⟨h.1.trans hst, h.2.trans hst⟩

/-- The constant amplitude `z`. -/
noncomputable def const (z : ℂ) : AmpPoly ι := ⟨C z.re, C z.im⟩

@[simp] lemma evalC_const (z : ℂ) (a : ι → Bool) : (const (ι := ι) z).evalC a = z := by
  apply Complex.ext <;> simp [const, evalC]

lemma degLe_const (z : ℂ) (t : ℕ) : (const (ι := ι) z).DegLe t := by
  constructor <;> simp [const]

/-- Multiplication by a fixed complex scalar `z`:
`(x + y I)(re + im I) = (x·re − y·im) + (y·re + x·im) I`. -/
noncomputable def cmul (z : ℂ) (P : AmpPoly ι) : AmpPoly ι :=
  ⟨C z.re * P.re - C z.im * P.im, C z.im * P.re + C z.re * P.im⟩

@[simp] lemma evalC_cmul (z : ℂ) (a : ι → Bool) : (cmul z P).evalC a = z * P.evalC a := by
  apply Complex.ext <;> simp [cmul, evalC, Complex.mul_re, Complex.mul_im] ; ring

lemma degLe_cmul (z : ℂ) {t : ℕ} (h : P.DegLe t) : (cmul z P).DegLe t := by
  constructor
  · rw [cmul, sub_eq_add_neg]
    refine (totalDegree_add _ _).trans (max_le ((totalDegree_C_mul_le _ _).trans h.1) ?_)
    rw [totalDegree_neg]
    exact (totalDegree_C_mul_le _ _).trans h.2
  · exact (totalDegree_add _ _).trans
      (max_le ((totalDegree_C_mul_le _ _).trans h.1) ((totalDegree_C_mul_le _ _).trans h.2))

/-- The sum of a finite family. -/
noncomputable def sum {κ : Type*} (s : Finset κ) (P : κ → AmpPoly ι) : AmpPoly ι :=
  ⟨∑ k ∈ s, (P k).re, ∑ k ∈ s, (P k).im⟩

@[simp] lemma evalC_sum {κ : Type*} (s : Finset κ) (P : κ → AmpPoly ι) (a : ι → Bool) :
    (sum s P).evalC a = ∑ k ∈ s, (P k).evalC a := by
  apply Complex.ext <;> simp [sum, evalC, evalBool_sum, Complex.re_sum, Complex.im_sum]

lemma degLe_sum {κ : Type*} (s : Finset κ) (P : κ → AmpPoly ι) {t : ℕ}
    (h : ∀ k ∈ s, (P k).DegLe t) : (sum s P).DegLe t :=
  ⟨totalDegree_finsetSum_le _ _ fun k hk => (h k hk).1,
   totalDegree_finsetSum_le _ _ fun k hk => (h k hk).2⟩

/-- The selector, applied to both parts. -/
noncomputable def select (i : ι) (P₀ P₁ : AmpPoly ι) : AmpPoly ι :=
  ⟨QuantumQueryComplexity.select i P₀.re P₁.re, QuantumQueryComplexity.select i P₀.im P₁.im⟩

lemma evalC_select (i : ι) (P₀ P₁ : AmpPoly ι) (a : ι → Bool) :
    (select i P₀ P₁).evalC a = if a i then P₁.evalC a else P₀.evalC a := by
  apply Complex.ext
  · simp only [select, evalC_re, evalBool_select]; split_ifs <;> rfl
  · simp only [select, evalC_im, evalBool_select]; split_ifs <;> rfl

lemma degLe_select (i : ι) {P₀ P₁ : AmpPoly ι} {t : ℕ} (h₀ : P₀.DegLe t) (h₁ : P₁.DegLe t) :
    (select i P₀ P₁).DegLe (t + 1) :=
  ⟨totalDegree_select_le i h₀.1 h₁.1, totalDegree_select_le i h₀.2 h₁.2⟩

/-- The squared modulus `re² + im²`, a real polynomial of twice the degree. -/
noncomputable def normSqPoly (P : AmpPoly ι) : MvPolynomial ι ℝ := P.re ^ 2 + P.im ^ 2

lemma evalBool_normSqPoly (a : ι → Bool) :
    evalBool P.normSqPoly a = Complex.normSq (P.evalC a) := by
  simp [normSqPoly, Complex.normSq_apply, sq]

lemma totalDegree_normSqPoly_le {t : ℕ} (h : P.DegLe t) : P.normSqPoly.totalDegree ≤ 2 * t :=
  (totalDegree_add _ _).trans (max_le (totalDegree_sq_le _ h.1) (totalDegree_sq_le _ h.2))

end AmpPoly

end QuantumQueryComplexity

end SourcePolynomialBoolean

section SourceQuantumPolynomialMethod

/-!
# The polynomial method (Beals–Buhrman–Cleve–Mosca–de Wolf)

A quantum algorithm making `t` queries to a Boolean input has, at every basis state, an
amplitude whose real and imaginary parts are real polynomials of total degree at most `t`
in the input bits; its acceptance probabilities are therefore polynomials of degree at most
`2·t`.  This is Lemmas 4.1 and 4.2 of *Quantum Lower Bounds by Polynomials*
(arXiv:quant-ph/9802049), proved here from the operational model of `SourceQuantumAlgorithm`.

The induction is stated once, for an arbitrary finite basis `B` and any oracle whose
action on a basis state is either input-independent or selected by one input bit
(`HasAmpPoly.selector`); the native value oracle (`oracleMap`) and the XOR oracle
(`SourceQuantumXorPolynomialMethod`) are two instances.  No query simulation between the models
is used, so both get the degree bound `2·t`, never `4·t`.

Main statements:

* `QAlg.hasAmpPoly_state`: the amplitudes after `t` queries have degree `≤ t`;
* `QAlg.exists_probability_polynomial`: output probabilities have degree at most `2·t`;
* `QAlg.exists_event_polynomial`: the same for the probability of a set of outputs;
* `ComputesWithErrorOn.exists_approx_polynomial`: a `t`-query algorithm computing a
  Boolean `f` on a promise with error `ε` yields a degree-`≤ 2t` polynomial within `ε` of
  `bit ∘ f` on the promise, with values in `[0, 1]` on the whole cube.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Representations of input-dependent vectors -/

/-- `Represents Φ φ t`: the amplitude polynomials `Φ b` represent the input-dependent vector
`φ`, with both parts of degree at most `t`. -/
def Represents {B : Type} (Φ : B → AmpPoly ι) (φ : (ι → Bool) → B → ℂ) (t : ℕ) : Prop :=
  (∀ b, (Φ b).DegLe t) ∧ ∀ a b, (Φ b).evalC a = φ a b

/-- `φ` has a representation of degree at most `t`. -/
def HasAmpPoly {B : Type} (φ : (ι → Bool) → B → ℂ) (t : ℕ) : Prop :=
  ∃ Φ : B → AmpPoly ι, Represents Φ φ t

variable {B : Type} {φ : (ι → Bool) → B → ℂ} {t : ℕ}

omit [DecidableEq ι] [Fintype ι] in
lemma hasAmpPoly_const (v : B → ℂ) : HasAmpPoly (fun _ : ι → Bool => v) 0 :=
  ⟨fun b => AmpPoly.const (v b), fun _ => AmpPoly.degLe_const _ _,
    fun _ _ => AmpPoly.evalC_const _ _⟩

omit [DecidableEq ι] [Fintype ι] in
lemma HasAmpPoly.mono (h : HasAmpPoly φ t) {t' : ℕ} (htt : t ≤ t') : HasAmpPoly φ t' := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  exact ⟨Φ, fun b => (hdeg b).mono htt, heval⟩

omit [DecidableEq ι] [Fintype ι] in
/-- **An input-independent linear map preserves the degree bound.** -/
lemma HasAmpPoly.mulVec [Fintype B] (U : Matrix B B ℂ) (h : HasAmpPoly φ t) :
    HasAmpPoly (fun a => U *ᵥ φ a) t := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  refine ⟨fun b => AmpPoly.sum Finset.univ fun c => AmpPoly.cmul (U b c) (Φ c),
    fun b => AmpPoly.degLe_sum _ _ fun c _ => AmpPoly.degLe_cmul _ _ (hdeg c), fun a b => ?_⟩
  simp [AmpPoly.evalC_sum, AmpPoly.evalC_cmul, heval, Matrix.mulVec, dotProduct]

omit [DecidableEq ι] [Fintype ι] in
/-- **A selector oracle raises the degree bound by one.**  An oracle whose action on each
basis state is either input-independent or the choice between two fixed basis states made
by one input bit. -/
lemma HasAmpPoly.selector (orc : (ι → Bool) → B → B)
    (horc : ∀ p, (∀ a, orc a p = p) ∨ ∃ i p₀ p₁, ∀ a, orc a p = if a i then p₁ else p₀)
    (h : HasAmpPoly φ t) : HasAmpPoly (fun a p => φ a (orc a p)) (t + 1) := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  have key : ∀ p, ∃ Q : AmpPoly ι, Q.DegLe (t + 1) ∧ ∀ a, Q.evalC a = φ a (orc a p) := by
    intro p
    rcases horc p with hid | ⟨i, p₀, p₁, hsel⟩
    · exact ⟨Φ p, (hdeg p).mono (Nat.le_succ t), fun a => by rw [heval, hid]⟩
    · refine ⟨AmpPoly.select i (Φ p₀) (Φ p₁), AmpPoly.degLe_select i (hdeg p₀) (hdeg p₁),
        fun a => ?_⟩
      rw [AmpPoly.evalC_select, hsel a]
      split_ifs <;> rw [heval]
  choose Φ' hΦ' using key
  exact ⟨Φ', fun p => (hΦ' p).1, fun a p => (hΦ' p).2 a⟩

/-! ## From amplitudes to probabilities -/

variable {O : Type} [DecidableEq O]

omit [DecidableEq ι] [Fintype ι] in
/-- **The probability polynomial**: the measured probability of an output is a real
polynomial of degree at most `2·t`. -/
theorem HasAmpPoly.exists_qProb_polynomial [Fintype B] (h : HasAmpPoly φ t) (rd : B → O)
    (o : O) : ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = qProb rd (φ a) o := by
  obtain ⟨Φ, hdeg, heval⟩ := h
  refine ⟨∑ b ∈ Finset.univ.filter (fun b => rd b = o), (Φ b).normSqPoly,
    totalDegree_finsetSum_le _ _ fun b _ => AmpPoly.totalDegree_normSqPoly_le _ (hdeg b),
    fun a => ?_⟩
  rw [evalBool_sum, qProb, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => by
    split_ifs
    · rw [AmpPoly.evalBool_normSqPoly, heval]
    · rfl

omit [DecidableEq ι] [Fintype ι] in
/-- The probability of an event (a finite set of outputs). -/
theorem HasAmpPoly.exists_event_polynomial [Fintype B] (h : HasAmpPoly φ t) (rd : B → O)
    (E : Finset O) : ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = ∑ o ∈ E, qProb rd (φ a) o := by
  classical
  have key : ∀ o : O, ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = qProb rd (φ a) o := fun o => h.exists_qProb_polynomial rd o
  choose P hP using key
  refine ⟨∑ o ∈ E, P o, totalDegree_finsetSum_le _ _ fun o _ => (hP o).1, fun a => ?_⟩
  rw [evalBool_sum]
  exact Finset.sum_congr rfl fun o _ => (hP o).2 a

/-! ## The native value oracle -/

variable {W : Type} [Fintype W] [DecidableEq W]

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
/-- The native oracle is a selector oracle: idle on index `none`, and at index `some i` a
swap determined by the bit `a i`. -/
lemma oracleMap_selector (p : QBasis ι Bool W) :
    (∀ a : ι → Bool, oracleMap a p = p) ∨
      ∃ i p₀ p₁, ∀ a : ι → Bool, oracleMap a p = if a i then p₁ else p₀ := by
  obtain ⟨(_ | i), s, w⟩ := p
  · exact Or.inl fun a => rfl
  · refine Or.inr ⟨i, (some i, Equiv.swap none (some false) s, w),
      (some i, Equiv.swap none (some true) s, w), fun a => ?_⟩
    rw [oracleMap_some]
    cases a i <;> simp

omit [DecidableEq O] in
/-- **Amplitudes after `t` queries have degree at most `t`** (BBCMW Lemma 4.1). -/
theorem QAlg.hasAmpPoly_state (A : QAlg ι Bool O W) (t : ℕ) :
    HasAmpPoly (fun a => A.state a t) t := by
  induction t with
  | zero => exact (hasAmpPoly_const A.init).mulVec (A.step 0)
  | succ t ih =>
      have h1 := ih.selector (fun a => oracleMap a) (fun p => oracleMap_selector p)
      have h2 : (fun a (p : QBasis ι Bool W) => A.state a t (oracleMap a p))
          = fun a => oracleMat a *ᵥ A.state a t := by
        funext a p
        exact (oracleMat_mulVec_apply a _ p).symm
      rw [h2] at h1
      exact h1.mulVec (A.step (t + 1))

/-- **The polynomial method** (BBCMW Lemma 4.2): the probability that a `t`-query
algorithm announces `o` is a real polynomial of total degree at most `2·t` in the input
bits, exactly, on the whole Boolean cube. -/
theorem QAlg.exists_probability_polynomial (A : QAlg ι Bool O W) (t : ℕ) (o : O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧ ∀ a, evalBool p a = A.prob a t o :=
  (A.hasAmpPoly_state t).exists_qProb_polynomial A.readout o

/-- The probability of announcing an output in `E`. -/
theorem QAlg.exists_event_polynomial (A : QAlg ι Bool O W) (t : ℕ) (E : Finset O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = ∑ o ∈ E, A.prob a t o :=
  (A.hasAmpPoly_state t).exists_event_polynomial A.readout E

/-! ## Probability bounds on the whole cube -/

/-- The probability bound specialized to the polynomial-method interface. -/
lemma qProb_le_one_of_isQState {H : Type} [Fintype H] {rd : H → O} {ψ : H → ℂ}
    (hψ : IsQState ψ) (o : O) : qProb rd ψ o ≤ 1 :=
  qProb_le_one hψ rd o

lemma QAlg.prob_le_one' (A : QAlg ι Bool O W) (a : ι → Bool) (t : ℕ) (o : O) :
    A.prob a t o ≤ 1 := A.prob_le_one a t o

/-- With finitely many outputs the output polynomials sum to `1` on the cube. -/
theorem QAlg.sum_prob_eq_one [Fintype O] (A : QAlg ι Bool O W) (a : ι → Bool) (t : ℕ) :
    ∑ o, A.prob a t o = 1 :=
  sum_qProb_eq_one (A.state_isQState a t) A.readout

/-! ## Correctness: the acceptance polynomial approximates the function -/

variable {X : Type} [Fintype X]

/-- `p` approximates the Boolean function `f` on the promise `read` within `ε`. -/
def ApproximatesOn (p : MvPolynomial ι ℝ) (read : X → ι → Bool) (f : X → Bool) (ε : ℝ) :
    Prop :=
  ∀ x, |evalBool p (read x) - bit (f x)| ≤ ε

/-- Two probabilities of a Boolean-output algorithm: correctness on `true` and on
`false`, translated into a two-sided bound on the acceptance probability. -/
lemma abs_qProb_true_sub_bit_le {H : Type} [Fintype H] {rd : H → Bool} {ψ : H → ℂ}
    (hψ : IsQState ψ) {b : Bool} {ε : ℝ} (h : 1 - ε ≤ qProb rd ψ b) :
    |qProb rd ψ true - bit b| ≤ ε := by
  classical
  have h0 : 0 ≤ qProb rd ψ true := qProb_nonneg _ _ _
  have h1 : qProb rd ψ true ≤ 1 := qProb_le_one_of_isQState hψ true
  cases b with
  | true =>
      rw [bit_true, abs_le]
      constructor <;> linarith
  | false =>
      have hsum : qProb rd ψ true + qProb rd ψ false ≤ 1 :=
        qProb_add_qProb_le_one hψ rd (by decide)
      rw [bit_false, sub_zero, abs_le]
      constructor <;> linarith

omit [Fintype X] in
/-- **Correctness transfers to the polynomial.** -/
theorem ComputesWithErrorOn.abs_prob_sub_bit_le {A : QAlg ι Bool Bool W} {t : ℕ}
    {read : X → ι → Bool} {f : X → Bool} {ε : ℝ} (h : ComputesWithErrorOn A t read f ε)
    (x : X) : |A.prob (read x) t true - bit (f x)| ≤ ε :=
  abs_qProb_true_sub_bit_le (A.state_isQState _ t) (h x)

omit [Fintype X] in
/-- **The approximating polynomial of a bounded-error algorithm**: degree at most `2·t`,
within `ε` of `bit ∘ f` on the promise, and with values in `[0, 1]` on the entire cube. -/
theorem ComputesWithErrorOn.exists_approx_polynomial {A : QAlg ι Bool Bool W} {t : ℕ}
    {read : X → ι → Bool} {f : X → Bool} {ε : ℝ} (h : ComputesWithErrorOn A t read f ε) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧ ApproximatesOn p read f ε ∧
      ∀ a, 0 ≤ evalBool p a ∧ evalBool p a ≤ 1 := by
  classical
  obtain ⟨p, hdeg, heval⟩ := A.exists_probability_polynomial t true
  refine ⟨p, hdeg, fun x => ?_, fun a => ?_⟩
  · rw [heval]
    exact h.abs_prob_sub_bit_le x
  · rw [heval]
    exact ⟨A.prob_nonneg _ _ _, A.prob_le_one' _ _ _⟩

end QuantumQueryComplexity

end SourceQuantumPolynomialMethod

section SourceQuantumXorPolynomialMethod

/-!
# The polynomial method for the XOR oracle

The same induction as `SourceQuantumPolynomialMethod`, run on the XOR-oracle semantics `xorState`
of `SourceQuantumXorOracle`.  The XOR oracle is again a selector oracle (idle at index
`none`; at index `some i` the answer register is XORed with the bit `a i`), so the shared
lemma `HasAmpPoly.selector` applies directly and the degree bound is `2·t` — the model
simulation of `SourceQuantumSimulation` is not used, which would have cost a factor two.
-/

namespace QuantumQueryComplexity

open scoped Matrix
open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {W : Type} [Fintype W] [DecidableEq W]
variable {O : Type} [DecidableEq O]

omit [DecidableEq W] [DecidableEq ι] [Fintype W] [Fintype ι] in
/-- The XOR oracle is a selector oracle. -/
lemma xorOracleMap_selector (p : QBasis ι Bool W) :
    (∀ a : ι → Bool, xorOracleMap a p = p) ∨
      ∃ i p₀ p₁, ∀ a : ι → Bool, xorOracleMap a p = if a i then p₁ else p₀ := by
  obtain ⟨(_ | i), s, w⟩ := p
  · exact Or.inl fun a => rfl
  · refine Or.inr ⟨i, (some i, optXor s (some false), w), (some i, optXor s (some true), w),
      fun a => ?_⟩
    rw [xorOracleMap_some]
    cases a i <;> simp

omit [DecidableEq O] in
/-- **XOR amplitudes after `t` queries have degree at most `t`.** -/
theorem hasAmpPoly_xorState (A : QAlg ι Bool O W) (t : ℕ) :
    HasAmpPoly (fun a => xorState A a t) t := by
  induction t with
  | zero => exact (hasAmpPoly_const A.init).mulVec (A.step 0)
  | succ t ih =>
      have h1 := ih.selector (fun a => xorOracleMap a) (fun p => xorOracleMap_selector p)
      have h2 : (fun a (p : QBasis ι Bool W) => xorState A a t (xorOracleMap a p))
          = fun a => xorOracleMat a *ᵥ xorState A a t := by
        funext a p
        exact (xorOracleMat_mulVec_apply a _ p).symm
      rw [h2] at h1
      exact h1.mulVec (A.step (t + 1))

/-- **The polynomial method, XOR oracle**: the acceptance probability after `t` XOR
queries is a real polynomial of total degree at most `2·t`. -/
theorem exists_xor_probability_polynomial (A : QAlg ι Bool O W) (t : ℕ) (o : O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = qProb A.readout (xorState A a t) o :=
  (hasAmpPoly_xorState A t).exists_qProb_polynomial A.readout o

/-- The probability of an event, XOR oracle. -/
theorem exists_xor_event_polynomial (A : QAlg ι Bool O W) (t : ℕ) (E : Finset O) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧
      ∀ a, evalBool p a = ∑ o ∈ E, qProb A.readout (xorState A a t) o :=
  (hasAmpPoly_xorState A t).exists_event_polynomial A.readout E

variable {X : Type} [Fintype X]

omit [Fintype X] in
/-- **Correctness transfers to the polynomial**, XOR oracle. -/
theorem XorComputesWithErrorOn.abs_prob_sub_bit_le {A : QAlg ι Bool Bool W} {t : ℕ}
    {read : X → ι → Bool} {f : X → Bool} {ε : ℝ}
    (h : XorComputesWithErrorOn A t read f ε) (x : X) :
    |qProb A.readout (xorState A (read x) t) true - bit (f x)| ≤ ε :=
  abs_qProb_true_sub_bit_le (xorState_isQState A _ t) (h x)

omit [Fintype X] in
/-- **The approximating polynomial of a bounded-error XOR algorithm.** -/
theorem XorComputesWithErrorOn.exists_approx_polynomial {A : QAlg ι Bool Bool W} {t : ℕ}
    {read : X → ι → Bool} {f : X → Bool} {ε : ℝ}
    (h : XorComputesWithErrorOn A t read f ε) :
    ∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ 2 * t ∧ ApproximatesOn p read f ε ∧
      ∀ a, 0 ≤ evalBool p a ∧ evalBool p a ≤ 1 := by
  classical
  obtain ⟨p, hdeg, heval⟩ := exists_xor_probability_polynomial A t true
  refine ⟨p, hdeg, fun x => ?_, fun a => ?_⟩
  · rw [heval]
    exact h.abs_prob_sub_bit_le x
  · rw [heval]
    exact ⟨qProb_nonneg _ _ _, qProb_le_one_of_isQState (xorState_isQState A a t) true⟩

end QuantumQueryComplexity

end SourceQuantumXorPolynomialMethod
