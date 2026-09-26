/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.FinitePlaceCompletion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic

/-!
# Orders at Dedekind places

Extend local orders to zero using a top value and prove their arithmetic and derivation
estimates through uniformizers.
-/

@[expose] public section

open scoped nonZeroDivisors
open IsDedekindDomain Multiplicative WithZero

namespace BGS.CorvajaZannier

noncomputable section

variable {R L : Type*} [CommRing R] [IsDedekindDomain R]
  [Field L] [Algebra R L] [IsFractionRing R L]

/-- The additive order at a finite place satisfies the ultrametric inequality
on nonzero inputs. -/
theorem finitePlaceOrder_add_ge_min
    (v : HeightOneSpectrum R) (x y : L)
    (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (finitePlaceOrder v x) (finitePlaceOrder v y) ≤
      finitePlaceOrder v (x + y) := by
  have hVal := (v.valuation L).map_add x y
  rw [valuation_eq_exp_neg_finitePlaceOrder v (x + y) hxy,
    valuation_eq_exp_neg_finitePlaceOrder v x hx,
    valuation_eq_exp_neg_finitePlaceOrder v y hy] at hVal
  by_cases hOrder : finitePlaceOrder v x ≤ finitePlaceOrder v y
  · rw [min_eq_left hOrder]
    have hExp : exp (-finitePlaceOrder v y) ≤ exp (-finitePlaceOrder v x) :=
      (WithZero.exp_le_exp).2 (neg_le_neg hOrder)
    rw [max_eq_left hExp] at hVal
    exact neg_le_neg_iff.mp ((WithZero.exp_le_exp).1 hVal)
  · have hOrder' : finitePlaceOrder v y ≤ finitePlaceOrder v x :=
      le_of_not_ge hOrder
    rw [min_eq_right hOrder']
    have hExp : exp (-finitePlaceOrder v x) ≤ exp (-finitePlaceOrder v y) :=
      (WithZero.exp_le_exp).2 (neg_le_neg hOrder')
    rw [max_eq_right hExp] at hVal
    exact neg_le_neg_iff.mp ((WithZero.exp_le_exp).1 hVal)

/-- The order attached to a height-one prime, with the zero element assigned
infinite order. -/
noncomputable def finitePlaceOrderTop (v : HeightOneSpectrum R) (x : L) : WithTop ℤ := by
  classical
  exact if x = 0 then ⊤ else finitePlaceOrder v x

@[simp]
theorem finitePlaceOrderTop_zero (v : HeightOneSpectrum R) :
    finitePlaceOrderTop (L := L) v 0 = ⊤ := by
  simp [finitePlaceOrderTop]

@[simp]
theorem finitePlaceOrderTop_eq_top_iff (v : HeightOneSpectrum R) (x : L) :
    finitePlaceOrderTop v x = ⊤ ↔ x = 0 := by
  simp [finitePlaceOrderTop]

theorem finitePlaceOrderTop_eq_coe (v : HeightOneSpectrum R)
    (x : L) (hx : x ≠ 0) :
    finitePlaceOrderTop v x = finitePlaceOrder v x := by
  simp [finitePlaceOrderTop, hx]

theorem finitePlaceOrderTop_add_ge_min
    (v : HeightOneSpectrum R) (x y : L) :
    min (finitePlaceOrderTop v x) (finitePlaceOrderTop v y) ≤
      finitePlaceOrderTop v (x + y) := by
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  by_cases hxy : x + y = 0
  · simp [finitePlaceOrderTop, hxy]
  simp only [finitePlaceOrderTop_eq_coe v x hx,
    finitePlaceOrderTop_eq_coe v y hy,
    finitePlaceOrderTop_eq_coe v (x + y) hxy]
  exact_mod_cast finitePlaceOrder_add_ge_min v x y hx hy hxy

theorem finitePlaceOrderTop_mul
    (v : HeightOneSpectrum R) (x y : L) :
    finitePlaceOrderTop v (x * y) =
      finitePlaceOrderTop v x + finitePlaceOrderTop v y := by
  by_cases hx : x = 0
  · subst x
    simp
  by_cases hy : y = 0
  · subst y
    simp
  rw [finitePlaceOrderTop_eq_coe v (x * y) (mul_ne_zero hx hy),
    finitePlaceOrderTop_eq_coe v x hx,
    finitePlaceOrderTop_eq_coe v y hy]
  norm_cast
  have hDivisor := finitePrincipalDivisor_mul (R := R) x y hx hy
  exact congrArg (fun D ↦ D v) hDivisor

@[simp]
theorem finitePlaceOrderTop_one (v : HeightOneSpectrum R) :
    finitePlaceOrderTop (L := L) v 1 = 0 := by
  rw [finitePlaceOrderTop_eq_coe v 1 one_ne_zero]
  have hvaluation := valuation_eq_exp_neg_finitePlaceOrder v (1 : L) one_ne_zero
  rw [map_one] at hvaluation
  have hexp : exp (0 : ℤ) = exp (-finitePlaceOrder v (1 : L)) := by
    simpa using hvaluation
  have hzero : (0 : ℤ) = -finitePlaceOrder v (1 : L) :=
    WithZero.exp_injective hexp
  have horder : finitePlaceOrder v (1 : L) = 0 := by omega
  exact_mod_cast horder

/-- The order of a natural power is the corresponding natural multiple of
the order.  The `WithTop` formulation also covers a zero base. -/
theorem finitePlaceOrderTop_pow
    (v : HeightOneSpectrum R) (x : L) (n : ℕ) :
    finitePlaceOrderTop v (x ^ n) = n • finitePlaceOrderTop v x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, finitePlaceOrderTop_mul, ih, succ_nsmul]

/-- A regular element of the Dedekind domain has nonnegative order at every
height-one place. -/
theorem finitePlaceOrderTop_algebraMap_nonnegative
    (v : HeightOneSpectrum R) (a : R) :
    (0 : WithTop ℤ) ≤ finitePlaceOrderTop v (algebraMap R L a) := by
  by_cases ha : a = 0
  · subst a
    simp
  have hmap : algebraMap R L a ≠ 0 := by
    intro hzero
    apply ha
    apply IsFractionRing.injective R L
    simpa using hzero
  rw [finitePlaceOrderTop_eq_coe v _ hmap]
  have hvaluation :=
    valuation_eq_exp_neg_finitePlaceOrder v (algebraMap R L a) hmap
  rw [HeightOneSpectrum.valuation_of_algebraMap,
    v.intValuation_eq_exp_neg_multiplicity ha] at hvaluation
  have horder :
      finitePlaceOrder v (algebraMap R L a) =
        (multiplicity v.asIdeal (Ideal.span {a}) : ℤ) := by
    exact (neg_injective (WithZero.exp_injective hvaluation)).symm
  rw [horder]
  exact_mod_cast Int.natCast_nonneg (multiplicity v.asIdeal (Ideal.span {a}))

section DVR

variable [IsDiscreteValuationRing R]

/-- At the place generated by a uniformizer, a unit times its `n`-th
integer power has order exactly `n`. -/
theorem finitePlaceOrder_unit_mul_uniformizer_zpow
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π}) (u : Rˣ) (n : ℤ) :
    finitePlaceOrder v
        ((algebraMap R L (u : R)) * (algebraMap R L π) ^ n) = n := by
  have hπ0 : algebraMap R L π ≠ 0 := by simpa using hπ.ne_zero
  have hu0 : algebraMap R L (u : R) ≠ 0 := by simp
  have hx0 :
      algebraMap R L (u : R) * (algebraMap R L π) ^ n ≠ 0 :=
    mul_ne_zero hu0 (zpow_ne_zero n hπ0)
  have hValπ : v.valuation L (algebraMap R L π) = exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_singleton v hπ.ne_zero hπIdeal]
  have hValu : v.valuation L (algebraMap R L (u : R)) = 1 := by
    exact Valuation.Integers.one_of_isUnit' u.isUnit
      (HeightOneSpectrum.valuation_le_one (K := L) v)
  have hValX :
      v.valuation L
          ((algebraMap R L (u : R)) * (algebraMap R L π) ^ n) =
        exp (-n) := by
    rw [map_mul, map_zpow₀ (v.valuation L) (algebraMap R L π) n,
      hValu, one_mul, hValπ, ← WithZero.exp_zsmul]
    congr 1
    simp
  rw [valuation_eq_exp_neg_finitePlaceOrder v _ hx0] at hValX
  exact neg_injective (WithZero.exp_injective hValX)

theorem finitePlaceOrder_uniformizer_zpow
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π}) (n : ℤ) :
    finitePlaceOrder v ((algebraMap R L π) ^ n) = n := by
  simpa using finitePlaceOrder_unit_mul_uniformizer_zpow
    (L := L) v π hπ hπIdeal (1 : Rˣ) n

theorem finitePlaceOrderTop_uniformizer_zpow
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π}) (n : ℤ) :
    finitePlaceOrderTop v ((algebraMap R L π) ^ n) = (n : WithTop ℤ) := by
  have hπ0 : algebraMap R L π ≠ 0 := by simpa using hπ.ne_zero
  rw [finitePlaceOrderTop_eq_coe v _ (zpow_ne_zero n hπ0)]
  exact_mod_cast finitePlaceOrder_uniformizer_zpow
    (L := L) v π hπ hπIdeal n

/-- Any derivation preserving a DVR lowers order by at most one.  No
normalization of the derivative of the chosen uniformizer is required.  The
`WithTop`-valued statement includes the cases `x = 0` and `D x = 0`. -/
theorem finitePlaceOrderTop_derivation_ge_sub_one_of_preserves
    {C : Type*} [Field C] [Algebra C L]
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R, D (algebraMap R L r) = algebraMap R L s)
    (x : L) :
    finitePlaceOrderTop v x + (-(1 : ℤ) : ℤ) ≤
      finitePlaceOrderTop v (D x) := by
  by_cases hx : x = 0
  · subst x
    simp
  obtain ⟨n, u, hxu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := L) hπ hx
  let a : L := algebraMap R L (u : R)
  let q : L := algebraMap R L π
  have hq0 : q ≠ 0 := by
    dsimp [q]
    simpa using hπ.ne_zero
  have ha0 : a ≠ 0 := by simp [a]
  have hx' : x = a * q ^ n := by
    simpa [a, q, Units.smul_def, Algebra.smul_def] using hxu
  have hOrderX : finitePlaceOrder v x = n := by
    rw [hx']
    exact finitePlaceOrder_unit_mul_uniformizer_zpow v π hπ hπIdeal u n
  by_cases hDx : D x = 0
  · simp [finitePlaceOrderTop, hDx]
  obtain ⟨da, hda⟩ := hDIntegral (u : R)
  have hDa : D a = algebraMap R L da := by simpa [a] using hda
  obtain ⟨dπ, hdπ⟩ := hDIntegral π
  have hDq : D q = algebraMap R L dπ := by simpa [q] using hdπ
  have hValπ : v.valuation L q = exp (-1 : ℤ) := by
    dsimp [q]
    calc
      v.valuation L (algebraMap R L π) = v.intValuation π :=
        HeightOneSpectrum.valuation_of_algebraMap v π
      _ = exp (-1 : ℤ) :=
        HeightOneSpectrum.intValuation_singleton v hπ.ne_zero hπIdeal
  have hValu : v.valuation L a = 1 := by
    dsimp [a]
    exact Valuation.Integers.one_of_isUnit' u.isUnit
      (HeightOneSpectrum.valuation_le_one (K := L) v)
  have hValPow (m : ℤ) : v.valuation L (q ^ m) = exp (-m) := by
    rw [map_zpow₀ (v.valuation L) q m, hValπ, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hValDa : v.valuation L (D a) ≤ 1 := by
    rw [hDa]
    exact HeightOneSpectrum.valuation_le_one (K := L) v da
  have hValDq : v.valuation L (D q) ≤ 1 := by
    rw [hDq]
    exact HeightOneSpectrum.valuation_le_one (K := L) v dπ
  have hValN : v.valuation L (n : L) ≤ 1 := by
    simpa using HeightOneSpectrum.valuation_le_one (K := L) v (n : R)
  have hDFormula :
      D x = D a * q ^ n + a * ((n : L) * q ^ (n - 1) * D q) := by
    rw [hx', D.leibniz, D.leibniz_zpow]
    simp only [smul_eq_mul]
    ring
  have hTermOne :
      v.valuation L (D a * q ^ n) ≤ exp (-(n - 1)) := by
    rw [map_mul, hValPow]
    calc
      v.valuation L (D a) * exp (-n) ≤ 1 * exp (-n) := by gcongr
      _ = exp (-n) := one_mul _
      _ ≤ exp (-(n - 1)) := (WithZero.exp_le_exp).2 (by omega)
  have hTermTwo :
      v.valuation L (a * ((n : L) * q ^ (n - 1) * D q)) ≤
        exp (-(n - 1)) := by
    rw [map_mul, map_mul, map_mul, hValu, one_mul, hValPow]
    calc
      v.valuation L (n : L) * exp (-(n - 1)) * v.valuation L (D q) ≤
          1 * exp (-(n - 1)) * 1 := by gcongr
      _ = exp (-(n - 1)) := by simp
  have hValDx : v.valuation L (D x) ≤ exp (-(n - 1)) := by
    rw [hDFormula]
    exact ((v.valuation L).map_add _ _).trans (max_le hTermOne hTermTwo)
  rw [valuation_eq_exp_neg_finitePlaceOrder v (D x) hDx] at hValDx
  have hOrderDx : n - 1 ≤ finitePlaceOrder v (D x) := by
    exact neg_le_neg_iff.mp ((WithZero.exp_le_exp).1 hValDx)
  rw [finitePlaceOrderTop_eq_coe v x hx,
    finitePlaceOrderTop_eq_coe v (D x) hDx, hOrderX]
  norm_cast

/-- The normalized-uniformizer version retained for callers that naturally
construct a local derivative. -/
theorem finitePlaceOrderTop_derivation_ge_sub_one
    {C : Type*} [Field C] [Algebra C R] [Algebra C L]
    [IsScalarTower C R L]
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R, D (algebraMap R L r) = algebraMap R L s)
    (_hDπ : D (algebraMap R L π) = 1) (x : L) :
    finitePlaceOrderTop v x + (-(1 : ℤ) : ℤ) ≤
      finitePlaceOrderTop v (D x) :=
  finitePlaceOrderTop_derivation_ge_sub_one_of_preserves
    v π hπ hπIdeal D hDIntegral x

/-- Iterating any DVR-preserving derivation lowers finite-place order by at
most the number of iterations. -/
theorem finitePlaceOrderTop_derivation_iterate_ge_sub_nat_of_preserves
    {C : Type*} [Field C] [Algebra C L]
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R, D (algebraMap R L r) = algebraMap R L s)
    (r : ℕ) (x : L) :
    finitePlaceOrderTop v x + (-(r : ℤ) : ℤ) ≤
      finitePlaceOrderTop v ((D : L → L)^[r] x) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      have hshift :=
        add_le_add_right ih ((-(1 : ℤ) : ℤ) : WithTop ℤ)
      have hshift' :
          (finitePlaceOrderTop v x + (-(r : ℤ) : ℤ)) +
              ((-(1 : ℤ) : ℤ) : WithTop ℤ) ≤
            finitePlaceOrderTop v ((D : L → L)^[r] x) +
              ((-(1 : ℤ) : ℤ) : WithTop ℤ) := by
        simpa [add_comm] using hshift
      have hstep := finitePlaceOrderTop_derivation_ge_sub_one_of_preserves
        v π hπ hπIdeal D hDIntegral ((D : L → L)^[r] x)
      calc
        finitePlaceOrderTop v x + (-(↑r.succ : ℤ) : ℤ) =
            (finitePlaceOrderTop v x + (-(r : ℤ) : ℤ)) +
              ((-(1 : ℤ) : ℤ) : WithTop ℤ) := by
          rw [add_assoc]
          congr 1
          exact_mod_cast (show -(↑r.succ : ℤ) = -(r : ℤ) + (-(1 : ℤ)) by omega)
        _ ≤ finitePlaceOrderTop v ((D : L → L)^[r] x) +
              ((-(1 : ℤ) : ℤ) : WithTop ℤ) := hshift'
        _ ≤ finitePlaceOrderTop v (D ((D : L → L)^[r] x)) := hstep

/-- The iterated normalized-uniformizer version retained for compatibility
with the local Wronskian API. -/
theorem finitePlaceOrderTop_derivation_iterate_ge_sub_nat
    {C : Type*} [Field C] [Algebra C R] [Algebra C L]
    [IsScalarTower C R L]
    (v : HeightOneSpectrum R) (π : R) (hπ : Irreducible π)
    (hπIdeal : v.asIdeal = Ideal.span {π})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R, D (algebraMap R L r) = algebraMap R L s)
    (_hDπ : D (algebraMap R L π) = 1) (r : ℕ) (x : L) :
    finitePlaceOrderTop v x + (-(r : ℤ) : ℤ) ≤
      finitePlaceOrderTop v ((D : L → L)^[r] x) :=
  finitePlaceOrderTop_derivation_iterate_ge_sub_nat_of_preserves
    v π hπ hπIdeal D hDIntegral r x

end DVR

end

end BGS.CorvajaZannier
