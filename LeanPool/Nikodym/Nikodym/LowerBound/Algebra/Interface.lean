/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import LeanPool.Nikodym.Nikodym.LowerBound.Hilbert.Defs
public import LeanPool.Nikodym.Nikodym.LowerBound.Jets.Defs
public import LeanPool.Nikodym.Nikodym.LowerBound.Lines.Basic

/-!
# The algebraic interface of the lower-bound proof

This file defines the two invariants of an ideal `I` of `P_d = MvPolynomial (Fin d) K` that the
combinatorial part of the proof consumes, and packages the algebraic input theorems (blueprint
nodes **A08**, **J02**, **B03** and the algebraic half of **C08**) as the `Prop`-valued structure
`Nikodym.LowerBound.AlgebraInterface K d`.

* `Nikodym.LowerBound.quotDim I : ℕ`, the Krull dimension `dim (P_d ⧸ I)` of the quotient ring
  (junk value `0` when the Krull dimension is `⊥` or `⊤`, which never happens for a proper ideal:
  `coe_quotDim`). We prove `quotDim_bot : quotDim ⊥ = d`, `quotDim_top`,
  `quotDim_le : quotDim I ≤ d`, `quotDim_lineIdeal : quotDim λ_{b,v} = 1`, antitonicity
  `quotDim_anti`, and strict antitonicity along strict inclusions of primes `quotDim_lt_of_lt`.
* `Nikodym.LowerBound.evPoly h : Polynomial ℚ`, the eventual polynomial of a function
  `h : ℕ → ℕ` (junk `0` if none exists), with `evPoly_spec`, uniqueness `evPoly_eq` and
  `evPoly_congr`.
* `Nikodym.LowerBound.affineHilbertPoly I : Polynomial ℚ`, the eventual polynomial of the affine
  Hilbert function `t ↦ hilbert I t`, definitionally `evPoly (hilbert I)`
  (`affineHilbertPoly_eq_evPoly`), with its specification `affineHilbertPoly_spec`, uniqueness
  `affineHilbertPoly_eq`, and the values at `⊥`, `⊤` and at line ideals.
* `Nikodym.LowerBound.degree I : ℕ`, the degree `(leading coefficient) * (natDegree)!` of the affine
  Hilbert polynomial, with `degree_bot = 1`, `degree_top = 0`, `degree_lineIdeal = 1`.
* `Nikodym.LowerBound.AlgebraInterface K d`: the input theorems A08, J02, B03, C08 as fields. The
  combinatorial assembly is proved conditionally on this structure; the final theorem must
  instantiate it with proofs about actual polynomial ideals (see the blueprint, Section 1).

The curve base case `eq_lineIdeal_of_le_of_quotDim_le_one` (a prime of quotient dimension at most
one containing a line ideal is that line ideal) is proved here unconditionally from
`quotDim_lt_of_lt`; the corresponding field of `AlgebraInterface` is therefore redundant and is
kept only for compatibility with the blueprint node list.
-/

@[expose] public section

namespace Nikodym.LowerBound

open Polynomial Filter

variable {K : Type*} [Field K] {d : ℕ}

/-! ### Krull dimension of the quotient -/

section QuotDim

/-- Blueprint A01/C08: the Krull dimension `dim (P_d ⧸ I)` of the coordinate ring, as a natural
number. The values `⊥` (zero ring) and `⊤` are sent to `0`; for a proper ideal neither occurs
(`coe_quotDim`). -/
noncomputable def quotDim (I : Ideal (MvPolynomial (Fin d) K)) : ℕ :=
  ((ringKrullDim (MvPolynomial (Fin d) K ⧸ I)).unbotD 0).toNat

/-- Blueprint A01: `dim P_d = d`. -/
theorem ringKrullDim_mvPolynomial_fin :
    ringKrullDim (MvPolynomial (Fin d) K) = (d : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing (R := K), ringKrullDim_eq_zero_of_field K,
    zero_add]
  simp

/-- Blueprint A01: `dim (P_d ⧸ I) ≤ d` in `WithBot ℕ∞`. -/
theorem ringKrullDim_quotient_le_natCast (I : Ideal (MvPolynomial (Fin d) K)) :
    ringKrullDim (MvPolynomial (Fin d) K ⧸ I) ≤ (d : WithBot ℕ∞) :=
  (ringKrullDim_quotient_le I).trans_eq ringKrullDim_mvPolynomial_fin

/-- Blueprint A01: `quotDim` recovers the Krull dimension of a natural-number value. -/
theorem quotDim_of_ringKrullDim_eq {I : Ideal (MvPolynomial (Fin d) K)} {n : ℕ}
    (h : ringKrullDim (MvPolynomial (Fin d) K ⧸ I) = (n : WithBot ℕ∞)) : quotDim I = n := by
  rw [quotDim, h, ← WithBot.coe_natCast, WithBot.unbotD_coe, ENat.toNat_natCast]

/-- Blueprint A01: for a proper ideal `I`, `quotDim I` is the Krull dimension of `P_d ⧸ I`
(no junk value occurs). -/
theorem coe_quotDim (I : Ideal (MvPolynomial (Fin d) K)) (hI : I ≠ ⊤) :
    (quotDim I : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin d) K ⧸ I) := by
  have : Nontrivial (MvPolynomial (Fin d) K ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin d) K ⧸ I) :=
    ringKrullDim_nonneg_of_nontrivial
  have hd := ringKrullDim_quotient_le_natCast I
  obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.zero_ne_bot h0)
  rw [← hx] at hd ⊢
  rw [← WithBot.coe_natCast, WithBot.coe_le_coe] at hd
  have hxtop : x ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hd
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hxtop
  rw [quotDim_of_ringKrullDim_eq (I := I) (n := n) (by rw [← hx, WithBot.coe_natCast])]
  exact WithBot.coe_natCast n

/-- Blueprint A01: `quotDim (0) = d`. -/
theorem quotDim_bot : quotDim (⊥ : Ideal (MvPolynomial (Fin d) K)) = d :=
  quotDim_of_ringKrullDim_eq
    ((ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).trans ringKrullDim_mvPolynomial_fin)

/-- Blueprint A01: `quotDim P_d = 0` (junk value for the zero ring). -/
theorem quotDim_top : quotDim (⊤ : Ideal (MvPolynomial (Fin d) K)) = 0 := by
  have : Subsingleton (MvPolynomial (Fin d) K ⧸ (⊤ : Ideal (MvPolynomial (Fin d) K))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  rw [quotDim, ringKrullDim_eq_bot_of_subsingleton, WithBot.unbotD_bot, ENat.toNat_zero]

/-- Blueprint A01: `quotDim I ≤ d`. -/
theorem quotDim_le (I : Ideal (MvPolynomial (Fin d) K)) : quotDim I ≤ d := by
  by_cases hI : I = ⊤
  · rw [hI, quotDim_top]
    exact Nat.zero_le d
  · have h := ringKrullDim_quotient_le_natCast I
    rw [← coe_quotDim I hI] at h
    exact_mod_cast h

/-- Blueprint C08: `quotDim λ_{b,v} = 1` for a nonzero direction `v`: the coordinate ring of a
line is `K[T]`. -/
theorem quotDim_lineIdeal (b : Fin d → K) {v : Fin d → K} (hv : v ≠ 0) :
    quotDim (lineIdeal b v) = 1 :=
  quotDim_of_ringKrullDim_eq <| by
    rw [ringKrullDim_eq_of_ringEquiv (lineQuotEquiv b hv).toRingEquiv,
      Polynomial.ringKrullDim_of_isNoetherianRing (R := K), ringKrullDim_eq_zero_of_field K,
      zero_add,
      Nat.cast_one]

/-- Blueprint C08: `quotDim` is antitone: `I ≤ J ≠ P_d` gives `quotDim J ≤ quotDim I`. -/
theorem quotDim_anti {I J : Ideal (MvPolynomial (Fin d) K)} (hIJ : I ≤ J) (hJ : J ≠ ⊤) :
    quotDim J ≤ quotDim I := by
  have hI : I ≠ ⊤ := fun h ↦ hJ (top_le_iff.mp (h ▸ hIJ))
  have h := ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIJ)
    (Ideal.Quotient.factor_surjective hIJ)
  rw [← coe_quotDim I hI, ← coe_quotDim J hJ] at h
  exact_mod_cast h

/-- Blueprint C08: a strict inclusion of primes strictly decreases the quotient dimension. Any
`r ∈ J \ I` is a nonzero, hence non-zero-divisor, element of the domain `P_d ⧸ I` killed by the
surjection `P_d ⧸ I → P_d ⧸ J`, so `dim (P_d ⧸ J) + 1 ≤ dim (P_d ⧸ I)`. -/
theorem quotDim_lt_of_lt {I J : Ideal (MvPolynomial (Fin d) K)} [I.IsPrime] [J.IsPrime]
    (hIJ : I < J) : quotDim J < quotDim I := by
  obtain ⟨r, hrJ, hrI⟩ := SetLike.exists_of_lt hIJ
  have hr : Ideal.Quotient.mk I r ∈ nonZeroDivisors (MvPolynomial (Fin d) K ⧸ I) :=
    mem_nonZeroDivisors_of_ne_zero (Ideal.Quotient.eq_zero_iff_mem.not.mpr hrI)
  have h := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hIJ.le)
    (Ideal.Quotient.factor_surjective hIJ.le) hr
    (by rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]; exact hrJ)
  rw [← coe_quotDim I Ideal.IsPrime.ne_top', ← coe_quotDim J Ideal.IsPrime.ne_top'] at h
  have h' : quotDim J + 1 ≤ quotDim I := by exact_mod_cast h
  omega

/-- Blueprint C08 (algebraic part): a prime ideal of quotient dimension at most one containing
the ideal of a line is the ideal of that line. -/
theorem eq_lineIdeal_of_le_of_quotDim_le_one {I : Ideal (MvPolynomial (Fin d) K)} [I.IsPrime]
    (hI : quotDim I ≤ 1) {b v : Fin d → K} (hv : v ≠ 0) (hle : I ≤ lineIdeal b v) :
    I = lineIdeal b v := by
  by_contra hne
  have := lineIdeal_isPrime b v
  have h := quotDim_lt_of_lt (lt_of_le_of_ne hle hne)
  rw [quotDim_lineIdeal b hv] at h
  omega

end QuotDim

/-! ### The affine Hilbert polynomial and the degree -/

section Degree

/-- Blueprint A03: two rational polynomials agreeing at all large natural numbers are equal. -/
theorem eventuallyEq_nat_unique {p q : Polynomial ℚ}
    (h : ∀ᶠ t : ℕ in atTop, p.eval (t : ℚ) = q.eval (t : ℚ)) : p = q := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  refine Polynomial.eq_of_infinite_eval_eq p q ?_
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ ↦ ((n + N : ℕ) : ℚ)) ?_ ?_
  · intro m n hmn
    have : ((m + N : ℕ) : ℚ) = ((n + N : ℕ) : ℚ) := hmn
    exact_mod_cast Nat.add_right_cancel (Nat.cast_injective this)
  · intro n
    exact hN (n + N) (Nat.le_add_left N n)

open scoped Classical in
/-- Blueprint A03: the eventual polynomial of a function `h : ℕ → ℕ`, i.e. the unique
`p : ℚ[X]` with `h t = p.eval t` for all large `t` (junk `0` if none exists). -/
noncomputable def evPoly (h : ℕ → ℕ) : Polynomial ℚ :=
  if hp : ∃ p : Polynomial ℚ, ∀ᶠ t : ℕ in atTop, (h t : ℚ) = p.eval (t : ℚ) then hp.choose
  else 0

/-- Blueprint A03: if `h` is eventually polynomial, `evPoly h` is that polynomial. -/
theorem evPoly_spec (h : ℕ → ℕ)
    (hp : ∃ p : Polynomial ℚ, ∀ᶠ t : ℕ in atTop, (h t : ℚ) = p.eval (t : ℚ)) :
    ∀ᶠ t : ℕ in atTop, (h t : ℚ) = (evPoly h).eval (t : ℚ) := by
  classical
  rw [evPoly, dite_eq_left hp]
  exact hp.choose_spec

/-- Blueprint A03: the eventual polynomial is determined by the function. -/
theorem evPoly_eq (h : ℕ → ℕ) {p : Polynomial ℚ}
    (hp : ∀ᶠ t : ℕ in atTop, (h t : ℚ) = p.eval (t : ℚ)) : evPoly h = p :=
  eventuallyEq_nat_unique <|
    ((evPoly_spec h ⟨p, hp⟩).and hp).mono fun _ ht ↦ ht.1.symm.trans ht.2

/-- Blueprint A03: equal functions have equal eventual polynomials (used across base change,
where the two Hilbert functions live over different fields). -/
theorem evPoly_congr (h₁ h₂ : ℕ → ℕ) (e : h₁ = h₂) : evPoly h₁ = evPoly h₂ := by
  subst e
  rfl

/-- Blueprint A03: the eventual polynomial of the affine Hilbert function `t ↦ hilbert I t`
(junk `0` if none exists); definitionally `evPoly (hilbert I)`. -/
noncomputable def affineHilbertPoly (I : Ideal (MvPolynomial (Fin d) K)) : Polynomial ℚ :=
  evPoly (hilbert I)

/-- Blueprint A03: `affineHilbertPoly I = evPoly (hilbert I)`, by definition. -/
theorem affineHilbertPoly_eq_evPoly (I : Ideal (MvPolynomial (Fin d) K)) :
    affineHilbertPoly I = evPoly (hilbert I) :=
  rfl

/-- Blueprint A03/A04: the degree `deg I = (leading coefficient of the affine Hilbert polynomial)
times `(natDegree)!`, as a natural number. -/
noncomputable def degree (I : Ideal (MvPolynomial (Fin d) K)) : ℕ :=
  ⌊(affineHilbertPoly I).leadingCoeff * ((affineHilbertPoly I).natDegree.factorial : ℚ)⌋₊

/-- Blueprint A03: if the Hilbert function is eventually polynomial, `affineHilbertPoly I` is
that polynomial. -/
theorem affineHilbertPoly_spec (I : Ideal (MvPolynomial (Fin d) K))
    (h : ∃ p : Polynomial ℚ, ∀ᶠ t : ℕ in atTop, (hilbert I t : ℚ) = p.eval (t : ℚ)) :
    ∀ᶠ t : ℕ in atTop, (hilbert I t : ℚ) = (affineHilbertPoly I).eval (t : ℚ) :=
  evPoly_spec (hilbert I) h

/-- Blueprint A03: the affine Hilbert polynomial is determined by the Hilbert function. -/
theorem affineHilbertPoly_eq (I : Ideal (MvPolynomial (Fin d) K)) {p : Polynomial ℚ}
    (hp : ∀ᶠ t : ℕ in atTop, (hilbert I t : ℚ) = p.eval (t : ℚ)) : affineHilbertPoly I = p :=
  evPoly_eq (hilbert I) hp

/-- Blueprint A03: the polynomial `t ↦ (t + d).choose d` over `ℚ`, namely
`(1 / d!) * (ascPochhammer ℚ d).comp (X + 1)`. -/
noncomputable def choosePoly (d : ℕ) : Polynomial ℚ :=
  C ((d.factorial : ℚ)⁻¹) * (ascPochhammer ℚ d).comp (X + 1)

/-- Blueprint A03: `(choosePoly d).eval t = (t + d).choose d` for `t : ℕ`. -/
theorem choosePoly_eval_natCast (d t : ℕ) :
    (choosePoly d).eval (t : ℚ) = ((t + d).choose d : ℚ) := by
  have h : ((t + 1).ascFactorial d : ℚ) = (d.factorial : ℚ) * ((t + d).choose d : ℚ) := by
    exact_mod_cast Nat.ascFactorial_eq_factorial_mul_choose t d
  rw [choosePoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_one, ← Nat.cast_one,
    ← Nat.cast_add, ascPochhammer_nat_eq_natCast_ascFactorial, h, ← mul_assoc,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr d.factorial_ne_zero), one_mul]

/-- Blueprint A03: `choosePoly d` has degree `d`. -/
theorem natDegree_choosePoly (d : ℕ) : (choosePoly d).natDegree = d := by
  rw [choosePoly, natDegree_C_mul (inv_ne_zero (Nat.cast_ne_zero.mpr d.factorial_ne_zero)),
    natDegree_comp, ascPochhammer_natDegree, ← C_1, natDegree_X_add_C, mul_one]

/-- Blueprint A03: `choosePoly d` has leading coefficient `1 / d!`. -/
theorem leadingCoeff_choosePoly (d : ℕ) :
    (choosePoly d).leadingCoeff = (d.factorial : ℚ)⁻¹ := by
  rw [choosePoly, leadingCoeff_mul, leadingCoeff_C, ← C_1,
    leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero), leadingCoeff_X_add_C,
    one_pow, mul_one, (monic_ascPochhammer ℚ d).leadingCoeff, mul_one]

/-- Blueprint A03: the affine Hilbert polynomial of `(0)` is `choosePoly d`. -/
theorem affineHilbertPoly_bot :
    affineHilbertPoly (⊥ : Ideal (MvPolynomial (Fin d) K)) = choosePoly d :=
  affineHilbertPoly_eq _ <| Eventually.of_forall fun t ↦ by
    rw [hilbert_bot, choosePoly_eval_natCast]

/-- Blueprint A04: `deg (0) = 1`. -/
theorem degree_bot : degree (⊥ : Ideal (MvPolynomial (Fin d) K)) = 1 := by
  rw [degree, affineHilbertPoly_bot, leadingCoeff_choosePoly, natDegree_choosePoly,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr d.factorial_ne_zero), Nat.floor_one]

/-- Blueprint A03: the affine Hilbert polynomial of `P_d` is `0`. -/
theorem affineHilbertPoly_top :
    affineHilbertPoly (⊤ : Ideal (MvPolynomial (Fin d) K)) = 0 :=
  affineHilbertPoly_eq _ <| Eventually.of_forall fun t ↦ by
    rw [hilbert_top, eval_zero, Nat.cast_zero]

/-- Blueprint A04: `deg P_d = 0` (junk value for the unit ideal). -/
theorem degree_top : degree (⊤ : Ideal (MvPolynomial (Fin d) K)) = 0 := by
  rw [degree, affineHilbertPoly_top, leadingCoeff_zero, zero_mul, Nat.floor_zero]

/-- Blueprint C08: the affine Hilbert polynomial of a line ideal is `X + 1`. -/
theorem affineHilbertPoly_lineIdeal (b : Fin d → K) {v : Fin d → K} (hv : v ≠ 0) :
    affineHilbertPoly (lineIdeal b v) = X + C 1 :=
  affineHilbertPoly_eq _ <| Eventually.of_forall fun t ↦ by
    rw [hilbert_lineIdeal b hv, eval_add, eval_X, eval_C, Nat.cast_add, Nat.cast_one]

/-- Blueprint C08: `deg λ_{b,v} = 1` for a nonzero direction `v`. -/
theorem degree_lineIdeal (b : Fin d → K) {v : Fin d → K} (hv : v ≠ 0) :
    degree (lineIdeal b v) = 1 := by
  rw [degree, affineHilbertPoly_lineIdeal b hv, leadingCoeff_X_add_C, natDegree_X_add_C,
    Nat.factorial_one, Nat.cast_one, one_mul, Nat.floor_one]

end Degree

/-! ### The interface structure -/

/-- The three algebraic input theorems of the lower-bound proof (blueprint A08, J02, B03) together
with the curve base case (C08). Stated for a fixed field `K` and dimension `d`. To be discharged
by the algebra backend; the combinatorial assembly is proved conditionally on this structure.
The final theorem must instantiate it with proofs about actual polynomial ideals; no instance is
declared here. -/
structure AlgebraInterface (K : Type*) [Field K] (d : ℕ) : Prop where
  /-- Blueprint A08: the uniform Hilbert upper bound `H_I(t) ≤ Δ (t + k).choose k` for a prime `I`
  of quotient dimension `k` and degree `Δ`. -/
  hilbert_le_degree_mul_choose : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → ∀ t : ℕ,
    hilbert I t ≤ degree I * (t + quotDim I).choose (quotDim I)
  /-- Blueprint J02: the local jet minimum `j_{I,x}(r) ≥ (r + k - 1).choose k` for a prime `I` of
  quotient dimension `k` and a rational point `x` on `I`. -/
  choose_le_jetDim : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → ∀ x : Fin d → K,
    I ≤ pointIdeal x → ∀ r : ℕ, 1 ≤ r → (r + quotDim I - 1).choose (quotDim I) ≤ jetDim I x r
  /-- Blueprint B03: the affine proper cut. Cutting a prime `I` of quotient dimension `k ≥ 2` by a
  polynomial `g ∉ I` of degree at most `T` with `I + (g) ≠ P_d` produces finitely many primes of
  quotient dimension `k - 1` and positive degree, of total degree at most `T · deg I`, such that
  every prime containing `I + (g)` contains one of them. -/
  proper_cut : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → 2 ≤ quotDim I →
    ∀ (g : MvPolynomial (Fin d) K) (T : ℕ), g ∉ I → g.totalDegree ≤ T → I ⊔ Ideal.span {g} ≠ ⊤ →
    ∃ S : Finset (Ideal (MvPolynomial (Fin d) K)),
      (∀ J ∈ S, J.IsPrime) ∧ (∀ J ∈ S, I ⊔ Ideal.span {g} ≤ J) ∧
      (∀ J ∈ S, quotDim J + 1 = quotDim I) ∧ (∀ J ∈ S, 0 < degree J) ∧
      (∑ J ∈ S, degree J) ≤ T * degree I ∧
      (∀ Q : Ideal (MvPolynomial (Fin d) K), Q.IsPrime → I ⊔ Ideal.span {g} ≤ Q → ∃ J ∈ S, J ≤ Q)
  /-- Blueprint C08, algebraic part: a curve containing a line is that line. This field is
  redundant: it is proved unconditionally as `eq_lineIdeal_of_le_of_quotDim_le_one` (via
  `quotDim_lt_of_lt` and `quotDim_lineIdeal`), and `AlgebraInterface.mk'` builds the structure
  without it. It is kept for compatibility with the blueprint node list. -/
  eq_lineIdeal_of_quotDim_eq_one : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime →
    quotDim I = 1 → ∀ b v : Fin d → K, v ≠ 0 → I ≤ lineIdeal b v → I = lineIdeal b v

namespace AlgebraInterface

variable (K)

/-- Blueprint C08: the last field of `AlgebraInterface` holds unconditionally. -/
theorem eq_lineIdeal_of_quotDim_eq_one' :
    ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → quotDim I = 1 → ∀ b v : Fin d → K,
      v ≠ 0 → I ≤ lineIdeal b v → I = lineIdeal b v := by
  intro I hI hdim b v hv hle
  have := hI
  exact eq_lineIdeal_of_le_of_quotDim_le_one hdim.le hv hle

variable {K}

/-- Build an `AlgebraInterface` from the three genuine input theorems A08, J02, B03; the curve
base case C08 is supplied by `eq_lineIdeal_of_le_of_quotDim_le_one`. -/
theorem mk' (h1 : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → ∀ t : ℕ,
      hilbert I t ≤ degree I * (t + quotDim I).choose (quotDim I))
    (h2 : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → ∀ x : Fin d → K,
      I ≤ pointIdeal x → ∀ r : ℕ, 1 ≤ r → (r + quotDim I - 1).choose (quotDim I) ≤ jetDim I x r)
    (h3 : ∀ (I : Ideal (MvPolynomial (Fin d) K)), I.IsPrime → 2 ≤ quotDim I →
      ∀ (g : MvPolynomial (Fin d) K) (T : ℕ), g ∉ I → g.totalDegree ≤ T →
      I ⊔ Ideal.span {g} ≠ ⊤ →
      ∃ S : Finset (Ideal (MvPolynomial (Fin d) K)),
        (∀ J ∈ S, J.IsPrime) ∧ (∀ J ∈ S, I ⊔ Ideal.span {g} ≤ J) ∧
        (∀ J ∈ S, quotDim J + 1 = quotDim I) ∧ (∀ J ∈ S, 0 < degree J) ∧
        (∑ J ∈ S, degree J) ≤ T * degree I ∧
        (∀ Q : Ideal (MvPolynomial (Fin d) K), Q.IsPrime → I ⊔ Ideal.span {g} ≤ Q →
          ∃ J ∈ S, J ≤ Q)) :
    AlgebraInterface K d :=
  ⟨h1, h2, h3, eq_lineIdeal_of_quotDim_eq_one' K⟩

/-- Blueprint C08: for any `H : AlgebraInterface K d`, a prime of quotient dimension at most one
containing a line ideal is that line ideal (in fact independent of `H`). -/
theorem eq_lineIdeal_of_le (_ : AlgebraInterface K d) {I : Ideal (MvPolynomial (Fin d) K)}
    (hI : I.IsPrime) (hdim : quotDim I ≤ 1) {b v : Fin d → K} (hv : v ≠ 0)
    (hle : I ≤ lineIdeal b v) : I = lineIdeal b v :=
  haveI := hI
  eq_lineIdeal_of_le_of_quotDim_le_one hdim hv hle

end AlgebraInterface

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
