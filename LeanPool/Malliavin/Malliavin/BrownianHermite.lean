/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# Algebraic Hermite bridge for Brownian chaos

The probabilists' Hermite polynomials, transported from integer to real coefficients, span the
real polynomial ring.  This is the finite-dimensional algebraic half of the standard Hermite
route from polynomial Brownian cylinders to Wiener--Itô chaos.
-/

noncomputable section

open MeasureTheory

namespace Malliavin.BrownianIteratedConstruction

/-- The probabilists' Hermite polynomial with real coefficients. -/
noncomputable def hermiteReal (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)

/-- Real Hermite polynomials are monic of their indexed degree. -/
theorem hermiteReal_isMonicOfDegree (n : ℕ) :
    Polynomial.IsMonicOfDegree (hermiteReal n) n := by
  refine ⟨?_, (Polynomial.hermite_monic n).map (Int.castRingHom ℝ)⟩
  rw [hermiteReal,
    Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective,
    Polynomial.natDegree_hermite]

/-- A degree-indexed monic polynomial family spans the full polynomial ring. -/
theorem span_range_eq_top_of_isMonicOfDegree (p : ℕ → Polynomial ℝ)
    (hp : ∀ n, Polynomial.IsMonicOfDegree (p n) n) :
    Submodule.span ℝ (Set.range p) = ⊤ := by
  let H := Submodule.span ℝ (Set.range p)
  apply top_unique
  intro f _hf
  change f ∈ H
  have hpow : ∀ n : ℕ, (Polynomial.X : Polynomial ℝ) ^ n ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : n = 0
        · subst n
          have hp0 : p 0 = 1 := Polynomial.isMonicOfDegree_zero_iff.mp (hp 0)
          have hgen : p 0 ∈ H := Submodule.subset_span ⟨0, rfl⟩
          simpa [hp0] using hgen
        · let q : Polynomial ℝ := p n - Polynomial.X ^ n
          have hqdeg : q.natDegree < n := (hp n).natDegree_sub_X_pow hn
          have hq : q ∈ H := by
            rw [q.as_sum_support_C_mul_X_pow]
            apply Submodule.sum_mem
            intro i hi
            rw [← Polynomial.smul_eq_C_mul]
            exact H.smul_mem (q.coeff i) <|
              ih i ((Polynomial.le_natDegree_of_mem_supp i hi).trans_lt hqdeg)
          have hgen : p n ∈ H := Submodule.subset_span ⟨n, rfl⟩
          have hrecover : p n - q = Polynomial.X ^ n := by
            simp [q]
          rw [← hrecover]
          exact H.sub_mem hgen hq
  rw [f.as_sum_support_C_mul_X_pow]
  apply Submodule.sum_mem
  intro i _hi
  rw [← Polynomial.smul_eq_C_mul]
  exact H.smul_mem (f.coeff i) (hpow i)

/-- The real Hermite polynomials algebraically span every real polynomial. -/
theorem span_range_hermiteReal :
    Submodule.span ℝ (Set.range hermiteReal) = ⊤ := by
  exact span_range_eq_top_of_isMonicOfDegree hermiteReal hermiteReal_isMonicOfDegree

/-- The monic Hermite family with variance parameter `variance`, characterized by
`H₀ = 1`, `H₁ = X`, and `Hₙ₊₂ = X Hₙ₊₁ - (n+1) variance Hₙ`. -/
noncomputable def varianceHermite (variance : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 =>
      Polynomial.X * varianceHermite variance (n + 1) -
        Polynomial.C (variance * (n + 1)) * varianceHermite variance n

/-- Unified successor recurrence for variance-parametrized Hermite polynomials. -/
theorem varianceHermite_succ (variance : ℝ) (n : ℕ) :
    varianceHermite variance (n + 1) =
      Polynomial.X * varianceHermite variance n -
        Polynomial.C (variance * n) * varianceHermite variance (n - 1) := by
  cases n with
  | zero => simp [varianceHermite]
  | succ n => simp [varianceHermite]

/-- Variance-parametrized Hermite polynomials form an Appell sequence. -/
theorem derivative_varianceHermite (variance : ℝ) (n : ℕ) :
    Polynomial.derivative (varianceHermite variance n) =
      Polynomial.C (n : ℝ) * varianceHermite variance (n - 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [varianceHermite]
  | one => simp [varianceHermite]
  | more n hn hn1 =>
      rw [varianceHermite]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_mul,
        Polynomial.derivative_X, Polynomial.derivative_C, one_mul, zero_mul, zero_add]
      simp only [Nat.add_sub_cancel] at hn1
      rw [hn1, hn]
      push_cast
      simp_rw [varianceHermite_succ variance n]
      simp only [map_add, map_mul]
      norm_num
      rw [show Polynomial.C (2 : ℝ) = (2 : Polynomial ℝ) by
        exact Polynomial.C_ofNat 2]
      ring

/-- Every variance-parametrized Hermite polynomial is monic of its indexed degree. -/
theorem varianceHermite_isMonicOfDegree (variance : ℝ) (n : ℕ) :
    Polynomial.IsMonicOfDegree (varianceHermite variance n) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [varianceHermite]
  | one => simpa [varianceHermite] using Polynomial.isMonicOfDegree_X ℝ
  | more n hn hn1 =>
      rw [varianceHermite]
      have hlead : Polynomial.IsMonicOfDegree
          (Polynomial.X * varianceHermite variance (n + 1)) (n + 2) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Polynomial.isMonicOfDegree_X ℝ).mul hn1
      apply hlead.sub
      exact (Polynomial.natDegree_C_mul_le
        (variance * (n + 1)) (varianceHermite variance n)).trans_lt <| by
          rw [hn.natDegree_eq]
          omega

/-- For every variance parameter, generalized Hermite polynomials span `ℝ[X]`. -/
theorem span_range_varianceHermite (variance : ℝ) :
    Submodule.span ℝ (Set.range (varianceHermite variance)) = ⊤ := by
  exact span_range_eq_top_of_isMonicOfDegree (varianceHermite variance)
    (varianceHermite_isMonicOfDegree variance)

variable {M : Type*} [AddCommMonoid M] [Module ℝ M]

/-- The linear map out of `ℝ[X]` prescribed by an arbitrary sequence on the monomial basis. -/
noncomputable def polynomialFamilyLinearMap (xpow : ℕ → M) :
    Polynomial ℝ →ₗ[ℝ] M :=
  (Polynomial.basisMonomials ℝ).constr ℝ xpow

/-- `polynomialFamilyLinearMap` has the prescribed value on every monomial. -/
@[simp]
theorem polynomialFamilyLinearMap_X_pow (xpow : ℕ → M) (n : ℕ) :
    polynomialFamilyLinearMap xpow (Polynomial.X ^ n) = xpow n := by
  rw [← Polynomial.monomial_one_right_eq_X_pow]
  change ((Polynomial.basisMonomials ℝ).constr ℝ xpow)
    ((Polynomial.basisMonomials ℝ) n) = xpow n
  exact (Polynomial.basisMonomials ℝ).constr_basis ℝ xpow n

/-- A polynomial family spanning `ℝ[X]` continues to span the prescribed monomial values after
applying `polynomialFamilyLinearMap`. -/
theorem span_range_polynomialFamilyLinearMap_of_span_eq_top
    (p : ℕ → Polynomial ℝ) (hp : Submodule.span ℝ (Set.range p) = ⊤)
    (xpow : ℕ → M) :
    Submodule.span ℝ (Set.range fun n ↦ polynomialFamilyLinearMap xpow (p n)) =
      Submodule.span ℝ (Set.range xpow) := by
  let T : Polynomial ℝ →ₗ[ℝ] M := polynomialFamilyLinearMap xpow
  change Submodule.span ℝ (Set.range fun n ↦ T (p n)) =
    Submodule.span ℝ (Set.range xpow)
  have hfamilyImage : T '' Set.range p = Set.range (fun n ↦ T (p n)) := by
    ext y
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨p n, ⟨n, rfl⟩, rfl⟩
  have hTpow (n : ℕ) : T (Polynomial.X ^ n) = xpow n := by
    exact polynomialFamilyLinearMap_X_pow xpow n
  have hpowerImage : T '' Set.range (fun n : ℕ ↦ (Polynomial.X : Polynomial ℝ) ^ n) =
      Set.range xpow := by
    ext y
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, (hTpow n).symm⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Polynomial.X ^ n, ⟨n, rfl⟩, hTpow n⟩
  have hpowerSpan : Submodule.span ℝ
      (Set.range fun n : ℕ ↦ (Polynomial.X : Polynomial ℝ) ^ n) = ⊤ :=
    span_range_eq_top_of_isMonicOfDegree _
      (Polynomial.isMonicOfDegree_X_pow ℝ)
  calc
    Submodule.span ℝ (Set.range fun n ↦ T (p n)) =
        Submodule.span ℝ (T '' Set.range p) := by rw [hfamilyImage]
    _ = (Submodule.span ℝ (Set.range p)).map T := Submodule.span_image T
    _ = (⊤ : Submodule ℝ (Polynomial ℝ)).map T := by rw [hp]
    _ = (Submodule.span ℝ
        (Set.range fun n : ℕ ↦ (Polynomial.X : Polynomial ℝ) ^ n)).map T := by
      rw [hpowerSpan]
    _ = Submodule.span ℝ
        (T '' Set.range fun n : ℕ ↦ (Polynomial.X : Polynomial ℝ) ^ n) := by
      rw [Submodule.map_span]
    _ = Submodule.span ℝ (Set.range xpow) := by rw [hpowerImage]

/-- Applying any linear map prescribed on monomials to the Hermite family does not change the
algebraic span of its values. -/
theorem span_range_polynomialFamilyLinearMap_hermiteReal (xpow : ℕ → M) :
    Submodule.span ℝ
        (Set.range fun n ↦ polynomialFamilyLinearMap xpow (hermiteReal n)) =
      Submodule.span ℝ (Set.range xpow) := by
  exact span_range_polynomialFamilyLinearMap_of_span_eq_top hermiteReal
    span_range_hermiteReal xpow

/-- Generalized Hermite values have the same algebraic span as the prescribed monomial values. -/
theorem span_range_polynomialFamilyLinearMap_varianceHermite
    (variance : ℝ) (xpow : ℕ → M) :
    Submodule.span ℝ
        (Set.range fun n ↦ polynomialFamilyLinearMap xpow (varianceHermite variance n)) =
      Submodule.span ℝ (Set.range xpow) := by
  exact span_range_polynomialFamilyLinearMap_of_span_eq_top
    (varianceHermite variance) (span_range_varianceHermite variance) xpow

variable {W : Type*} [MeasurableSpace W] {P : Measure W}

/-- If the prescribed monomial values represent powers of one random variable, then the induced
linear map represents pointwise polynomial evaluation. -/
theorem coeFn_polynomialFamilyLinearMap
    (xpow : ℕ → Lp ℝ 2 P) (X : W → ℝ)
    (hxpow : ∀ n, (xpow n : W → ℝ) =ᵐ[P] fun w ↦ X w ^ n)
    (p : Polynomial ℝ) :
    (polynomialFamilyLinearMap xpow p : W → ℝ) =ᵐ[P]
      fun w ↦ p.eval (X w) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add]
      filter_upwards [Lp.coeFn_add (polynomialFamilyLinearMap xpow p)
        (polynomialFamilyLinearMap xpow q), hp, hq] with w hadd hpw hqw
      rw [hadd, Pi.add_apply, hpw, hqw, Polynomial.eval_add]
  | monomial n a =>
      have hmonomial : Polynomial.monomial n a =
          a • (Polynomial.X : Polynomial ℝ) ^ n := by
        rw [Polynomial.smul_eq_C_mul, Polynomial.C_mul_X_pow_eq_monomial]
      rw [hmonomial, map_smul, polynomialFamilyLinearMap_X_pow]
      filter_upwards [Lp.coeFn_smul a (xpow n), hxpow n] with w hsmul hpow
      rw [hsmul, Pi.smul_apply, hpow, Polynomial.eval_smul]
      simp only [smul_eq_mul, Polynomial.eval_pow, Polynomial.eval_X]

end Malliavin.BrownianIteratedConstruction

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
