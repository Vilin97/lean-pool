/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.RRspace.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Degree.Support
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Adjoin.Polynomial.Bivariate
public import Mathlib.RingTheory.Localization.Integral

/-!
# Pole divisors and Stichtenoth 1.4.11
This file develops the pole divisor `(x)_∞` and the key degree identity:
`deg (polarDivisor x) = finrank k(X) K` for transcendental `x`.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

open Polynomial BigOperators Submodule IntermediateField

noncomputable section

namespace FunctionField.Chart

section TranscendentalPowers

variable (k L : Type*) [Field k] [Field L] [Algebra k L]

/-- Powers `x^j` with `j ≤ r` are `k`-linearly independent when `x` is transcendental. -/
theorem linearIndependent_fin_pow_of_transcendental {x : L} (hx : Transcendental k x) (r : ℕ) :
    LinearIndependent k fun j : Fin (r + 1) => x ^ (j : ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  let p : k[X] := ∑ i : Fin (r + 1), C (g i) * X ^ (i : ℕ)
  have hzero : aeval x p = 0 := by
    have hsum : aeval x p = ∑ i : Fin (r + 1), g i • x ^ (i : ℕ) := by
      simp only [p, map_sum, map_mul, aeval_C]
      congr 1
      ext i
      rw [aeval_X_pow, Algebra.smul_def, mul_comm]
    rw [hsum, hg]
  have hp0 : p = 0 := (transcendental_iff.mp hx) p hzero
  have hcoeffj : g j = 0 := by
    have hpgj : g j = p.coeff (j : ℕ) := by
      classical
      dsimp only [p]
      rw [finsetSum_coeff, Finset.sum_eq_single j]
      · rw [coeff_C_mul_X_pow, ite_eq_left rfl]
      · intro b _ ne
        rw [coeff_C_mul_X_pow]
        split_ifs with h
        · exact absurd h (Fin.val_ne_of_ne ne.symm)
        · rfl
      · simp
    rw [hpgj, hp0, coeff_zero]
  exact hcoeffj

end TranscendentalPowers

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K]

variable [IsFullConstantField k K]

/-- Decidable equality on coordinate places for polar divisor proofs. -/
local instance instDecidableEqPlaceAPolar : DecidableEq (PlaceA k K) := Classical.decEq _
/-- The classical decidable equality on `k(X)` used by the coordinate places. -/
local instance instDecidableEqRatFuncPolar : DecidableEq k⟮X⟯ := Classical.decEq _

section PolarDivisor

/-- The pole divisor `(x)_∞` of a nonzero function. -/
noncomputable def polarDivisor (x : K) : DivisorA k K :=
  by
  classical
  exact if hx : x = 0 then 0
    else (-principalDivisorA k K (Additive.ofMul (Units.mk0 x hx))) ⊔ 0

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem polarDivisor_zero : polarDivisor k K (0 : K) = 0 := by
  simp [polarDivisor]

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem polarDivisor_nonneg (x : K) : 0 ≤ polarDivisor k K x := by
  unfold polarDivisor
  split_ifs with hx
  · simp
  · exact le_sup_right

theorem polarDivisor_eq_zero_of_algebraic {x : K} (hx : IsAlgebraic k x) :
    polarDivisor k K x = 0 := by
  by_cases hx0 : x = 0
  · simp [polarDivisor, hx0]
  · obtain ⟨c, hc⟩ := IsFullConstantField.algebraic_mem (k := k) (K := K) x hx
    have hc0 : c ≠ 0 := fun hc0 => hx0 (hc.trans (by rw [hc0, map_zero]))
    have hdiv :
        principalDivisorA k K (Additive.ofMul (Units.mk0 x hx0)) = 0 := by
      have hmap : Units.mk0 x hx0 = Units.map (algebraMap k K) (Units.mk0 c hc0) := by
        ext
        exact hc
      rw [hmap, principalDivisorA_algebraMap k K (Units.mk0 c hc0)]
    ext v
    unfold polarDivisor
    simp only [dite_eq_right hx0, hdiv, neg_zero, Finsupp.sup_apply, max_self]

omit [IsFullConstantField k K] in
theorem exists_placeValuation_gt_one_of_not_algebraic {x : K} (_hx : x ≠ 0)
    (hnt : ¬IsAlgebraic k x) :
    ∃ v : PlaceA k K, 1 < placeValuation k K v x := by
  by_cases h : ∃ v : PlaceA k K, 1 < placeValuation k K v x
  · exact h
  · push Not at h
    exact absurd (isAlgebraic_of_placeValuation_le_one k K x h) hnt

omit [IsFullConstantField k K] in
theorem polarDivisor_pos {x : K} (hx : x ≠ 0) (hnt : ¬IsAlgebraic k x) :
    0 < deg k K (polarDivisor k K x) := by
  obtain ⟨v, hvgt⟩ := exists_placeValuation_gt_one_of_not_algebraic k K hx hnt
  have hvpos : 0 < placeDegree k K v := placeDegree_pos k K v
  have hord : 0 < (polarDivisor k K x) v := by
    unfold polarDivisor
    split_ifs with hx0
    · exact absurd hx0 hx
    · have hvval := placeValuation_eq_exp_neg_principalDivisor k K
        (Additive.ofMul (Units.mk0 x hx)) v
      change 1 < placeValuation k K v x at hvgt
      change placeValuation k K v x =
        WithZero.exp (-(principalDivisorA k K (Additive.ofMul (Units.mk0 x hx)) v)) at hvval
      rw [hvval] at hvgt
      let t := -(principalDivisorA k K (Additive.ofMul (Units.mk0 x hx)) v)
      have hexp1 : 1 < WithZero.exp t := hvgt
      have ht : 0 < t := by
        have hexpne : WithZero.exp t ≠ 0 := WithZero.exp_pos.ne'
        have hlog : WithZero.log 1 < WithZero.log (WithZero.exp t) :=
          (WithZero.log_lt_log one_ne_zero hexpne).2 hexp1
        rw [WithZero.log_one, WithZero.log_exp] at hlog
        exact hlog
      rw [Finsupp.sup_apply]
      exact lt_sup_iff.2 (Or.inl ht)
  have hsingle : Finsupp.single v (polarDivisor k K x v) ≤ polarDivisor k K x := by
    intro w
    by_cases hw : w = v
    · subst hw
      simp only [Finsupp.single_apply, ite_eq_left]
      exact le_rfl
    · rw [Finsupp.single_apply, ite_eq_right (Ne.symm hw)]
      exact polarDivisor_nonneg k K x w
  have hle : (placeDegree k K v : ℤ) * (polarDivisor k K x v) ≤
      deg k K (polarDivisor k K x) := by
    rw [← mul_comm (polarDivisor k K x v : ℤ), ← deg_single k K v (polarDivisor k K x v)]
    exact deg_mono k K hsingle
  have hdeg : 0 < (placeDegree k K v : ℤ) * (polarDivisor k K x v) := by
    exact mul_pos (mod_cast hvpos) (mod_cast hord)
  exact lt_of_lt_of_le hdeg hle

omit [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
/-- `¬IsAlgebraic` is equivalent to `Transcendental` over a field. -/
theorem not_isAlgebraic_iff_transcendental (x : K) :
    ¬IsAlgebraic k x ↔ Transcendental k x :=
  Iff.rfl

/-- If `n(r + 1) ≤ dr + c` for all natural `r` and `0 < d`, then `n ≤ d`.
Used in the `finrank ≤ deg B` half of Stichtenoth 1.4.11. -/
theorem le_of_forall_nat_mul_le {n d c : ℕ} (_hd : 0 < d)
    (h : ∀ r : ℕ, n * (r + 1) ≤ d * r + c) : n ≤ d := by
  by_contra hn
  have hn' : d < n := lt_of_not_ge hn
  have hnd : 0 < n - d := tsub_pos_of_lt hn'
  have step : ∀ r : ℕ, (n - d) * r + n ≤ c := by
    intro r
    have hr := h r
    have hsuc : n * (r + 1) = n * r + n := Nat.mul_succ n r
    have hn_eq : d + (n - d) = n := by rw [Nat.add_comm, Nat.sub_add_cancel (Nat.le_of_lt hn')]
    have hsplit : n * r = d * r + (n - d) * r := by
      conv_lhs => arg 1; rw [← hn_eq]
      exact add_mul d (n - d) r
    rw [hsuc, hsplit] at hr
    have hr' : (n - d) * r + n ≤ c := by omega
    exact hr'
  have _hnc : n ≤ c := by simpa [Nat.mul_zero, Nat.zero_add] using step 0
  have bound : ∀ r : ℕ, (n - d) * r ≤ c - n := by
    intro r
    have := step r
    omega
  set q := (c - n) / (n - d)
  have hq_lt : c - n < (q + 1) * (n - d) := by
    have hmod := Nat.mod_lt (c - n) hnd
    calc c - n
        = (n - d) * q + (c - n) % (n - d) := (Nat.div_add_mod (c - n) (n - d)).symm
      _ = q * (n - d) + (c - n) % (n - d) := by rw [Nat.mul_comm]
      _ < q * (n - d) + (n - d) := by gcongr
      _ = (q + 1) * (n - d) := by ring_nf
  have hcontra := bound (q + 1)
  rw [Nat.mul_comm] at hcontra
  exact lt_irrefl _ (Nat.lt_of_le_of_lt hcontra hq_lt)

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem memRRspace_polarDivisor_of_ne_zero {x : K} (hxne : x ≠ 0) :
    memRRspace k K (polarDivisor k K x) x := by
  intro v
  unfold polarDivisor
  split_ifs with hx0
  · exact absurd hx0 hxne
  · have hvval := placeValuation_eq_exp_neg_principalDivisor k K
      (Additive.ofMul (Units.mk0 x hx0)) v
    change placeValuation k K v x =
      WithZero.exp (-(principalDivisorA k K (Additive.ofMul (Units.mk0 x hx0)) v)) at hvval
    rw [hvval, Finsupp.sup_apply]
    exact WithZero.exp_le_exp.mpr (le_max_left _ 0)

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem memRRspace_smul_polar {x : K} (hxne : x ≠ 0) (n : ℕ) :
    memRRspace k K (n • polarDivisor k K x) (x ^ n) :=
  memRRspace.pow_mem (k := k) (K := K) (D := polarDivisor k K x) (f := x)
    (memRRspace_polarDivisor_of_ne_zero k K hxne) n

omit [Algebra k K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem nsmul_le_nsmul_polar {D : DivisorA k K} (hD : 0 ≤ D) {j r : ℕ} (hjr : j ≤ r) :
    j • D ≤ r • D := by
  intro v
  change (j : ℤ) * D v ≤ (r : ℤ) * D v
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjr) (hD v)

/-- A uniform pole bound for a finite family of functions. -/
noncomputable def basisPoleBound {ι : Type*} [Fintype ι] (f : ι → K) : DivisorA k K :=
  (Finset.univ : Finset ι).sum fun i => polarDivisor k K (f i)

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem polarDivisor_le_basisPoleBound {ι : Type*} [Fintype ι]
    (f : ι → K) (i : ι) :
    polarDivisor k K (f i) ≤ basisPoleBound k K f := by
  classical
  simp only [basisPoleBound]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => polarDivisor_nonneg k K (f j))

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem basisPoleBound_nonneg {ι : Type*} [Fintype ι] (f : ι → K) :
    0 ≤ basisPoleBound k K f := by
  intro v
  change 0 ≤ (basisPoleBound k K f) v
  simp only [basisPoleBound, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact Finset.sum_nonneg fun i _ => polarDivisor_nonneg k K (f i) v

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem memRRspace_basisPoleBound {ι : Type*} [Fintype ι]
    (f : ι → K) (i : ι) :
    memRRspace k K (basisPoleBound k K f) (f i) := by
  by_cases hi : f i = 0
  · rw [hi]
    exact memRRspace.zero_mem (k := k) (K := K) (basisPoleBound k K f)
  · exact (memRRspace.memRRspace_mono (k := k) (K := K) (polarDivisor_le_basisPoleBound k K f i))
      (memRRspace_polarDivisor_of_ne_zero k K hi)

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
theorem memRRspace_basis_smul_x_pow {ι : Type*} [Fintype ι]
    (f : ι → K) (x : K)
    (hxne : x ≠ 0) (r : ℕ) (i : ι) (j : ℕ) (hj : j ≤ r) :
    memRRspace k K (basisPoleBound k K f + r • polarDivisor k K x) (f i * x ^ j) :=
  memRRspace.mul_mem (k := k) (K := K)
    (memRRspace_basisPoleBound k K f i)
    ((memRRspace.memRRspace_mono (k := k) (K := K)
        (nsmul_le_nsmul_polar (D := polarDivisor k K x) (hD := polarDivisor_nonneg k K x)
          (hjr := hj)))
      (memRRspace_smul_polar k K hxne j))

section ChartVariable

/-- Scalar tower `k → k⟮X⟯ → K` for chart-variable arguments. -/
local instance instIsScalarTowerChart : IsScalarTower k k⟮X⟯ K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K,
      ← IsScalarTower.algebraMap_apply k k[X] k⟮X⟯]

/-- The chart variable `X_K` in `K`. -/
noncomputable def XK : K := algebraMap k⟮X⟯ K (RatFunc.X : k⟮X⟯)

omit [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem transcendental_XK : Transcendental k (XK k K) :=
  (transcendental_algebraMap_iff (algebraMap k⟮X⟯ K).injective).2 RatFunc.transcendental_X

omit [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem not_algebraic_XK : ¬IsAlgebraic k (XK k K) :=
  transcendental_XK k K

omit [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem XK_ne_zero : XK k K ≠ 0 := fun hx0 =>
  (not_algebraic_XK k K) (hx0 ▸ isAlgebraic_zero)

omit [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
/-- Powers `X_K^j` with `j ≤ r` are `k`-linearly independent. -/
theorem linearIndependent_fin_pow_XK (r : ℕ) :
    LinearIndependent k fun j : Fin (r + 1) => (XK k K) ^ (j : ℕ) :=
  linearIndependent_fin_pow_of_transcendental (k := k) (L := K) (transcendental_XK k K) r

omit [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
/-- The family `{b i · X_K^j}` is `k`-linearly independent over a `k⟮X⟯`-basis `b`. -/
theorem linearIndependent_basis_smul_XK_pow {n r : ℕ}
    (b : Module.Basis (Fin n) k⟮X⟯ K) :
    LinearIndependent k fun p : Fin n × Fin (r + 1) =>
      (b p.1 : K) * (XK k K) ^ (p.2 : ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let s : Fin n → k⟮X⟯ := fun i =>
    ∑ j : Fin (r + 1), g (i, j) • RatFunc.X ^ (j : ℕ)
  have hsingle : ∀ i, algebraMap k⟮X⟯ K (s i) * (b i : K) =
      ∑ j : Fin (r + 1), g (i, j) • ((b i : K) * (XK k K) ^ (j : ℕ)) := by
    intro i
    dsimp only [s, XK]
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [Algebra.smul_def, map_mul, map_pow, mul_assoc, mul_comm (b i : K),
      IsScalarTower.algebraMap_apply k k⟮X⟯ K (g (i, j))]
  have hcombo : ∑ i : Fin n, algebraMap k⟮X⟯ K (s i) * (b i : K) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => hsingle i, ← Finset.sum_product']
    exact hg
  have hcombo' : ∑ i : Fin n, s i • (b i : K) = 0 := by
    simpa only [Algebra.smul_def] using hcombo
  have hs : ∀ i, s i = 0 :=
    (Fintype.linearIndependent_iff.mp b.linearIndependent) s hcombo'
  intro p
  have hs' := hs p.1
  have hlin := linearIndependent_fin_pow_of_transcendental (k := k) (L := k⟮X⟯)
    RatFunc.transcendental_X r
  rw [Fintype.linearIndependent_iff] at hlin
  exact hlin (fun j => g (p.1, j)) (by dsimp only [s] at hs'; exact hs') p.2

omit [IsFullConstantField k K] in
/-- Growth along the pole family: `n(r+1) ≤ ℓ(C + r•B)`. -/
theorem ell_family_ge {n r : ℕ} (b : Module.Basis (Fin n) k⟮X⟯ K) :
    n * (r + 1) ≤ ell k K (basisPoleBound k K b + r • polarDivisor k K (XK k K)) := by
  let C := basisPoleBound k K b
  let B := polarDivisor k K (XK k K)
  let x := XK k K
  have hx0 : x ≠ 0 := XK_ne_zero k K
  have hDnn : 0 ≤ C + r • B := add_nonneg (basisPoleBound_nonneg k K b) fun v =>
    mul_nonneg (Nat.cast_nonneg r) (polarDivisor_nonneg k K x v)
  let v : Fin n × Fin (r + 1) → K := fun p => (b p.1 : K) * x ^ (p.2 : ℕ)
  have hmem : ∀ p, v p ∈ RRspace k K (C + r • B) := by
    intro p
    rw [mem_RRspace_iff]
    exact memRRspace_basis_smul_x_pow (k := k) (K := K) (f := b) x hx0 r p.1 (p.2 : ℕ)
      (Nat.le_of_lt_succ (Fin.is_lt p.2))
  have hlin : LinearIndependent k v :=
    linearIndependent_basis_smul_XK_pow (k := k) (K := K) b
  have hsubset : span k (Set.range v) ≤ RRspace k K (C + r • B) := by
    refine span_le.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact hmem p
  have hcard : n * (r + 1) ≤ Module.finrank k (span k (Set.range v)) := by
    have heq_card := finrank_span_eq_card (R := k) (M := K) hlin
    simp [heq_card, Fintype.card_prod, Fintype.card_fin]
  have hle : Module.finrank k (span k (Set.range v)) ≤ ell k K (C + r • B) :=
    Submodule.finrank_mono hsubset
  exact Nat.le_trans hcard hle

/-- Stichtenoth 1.4.11 counting half for the chart variable: `[K : k⟮X⟯] ≤ deg (X_K)_∞`. -/
theorem finrank_le_deg_polarX :
    Module.finrank k⟮X⟯ K ≤ deg k K (polarDivisor k K (XK k K)) := by
  let n := Module.finrank k⟮X⟯ K
  let b := Module.finBasis k⟮X⟯ K
  let C := basisPoleBound k K b
  let B := polarDivisor k K (XK k K)
  have hx : ¬IsAlgebraic k (XK k K) := not_algebraic_XK k K
  have hx0 : XK k K ≠ 0 := XK_ne_zero k K
  have hBpos : 0 < deg k K B := polarDivisor_pos k K hx0 hx
  have hBnn : 0 ≤ B := polarDivisor_nonneg k K (XK k K)
  have hBeff : IsEffective k K B := hBnn
  have hdegB0 := deg_nonneg k K hBeff
  have hdpos : 0 < (deg k K B).toNat := by
    rw [← Int.toNat_of_nonneg hdegB0] at hBpos
    exact Int.ofNat_lt.mp hBpos
  have hmain : n ≤ (deg k K B).toNat :=
    le_of_forall_nat_mul_le (d := (deg k K B).toNat) (c := (deg k K C).toNat + 1) hdpos fun r => by
      let D := C + r • B
      have hDnn : 0 ≤ D := add_nonneg (basisPoleBound_nonneg k K b) fun v =>
        mul_nonneg (Nat.cast_nonneg r) (hBnn v)
      have hDeff : IsEffective k K D := hDnn
      have hCeff : IsEffective k K C := basisPoleBound_nonneg k K b
      have hell : (ell k K D : ℤ) ≤ deg k K D + 1 :=
        ell_le_nonneg (k := k) (K := K) hDnn
      have hdeg : deg k K D = deg k K C + (r : ℤ) * deg k K B := by
        rw [add_comm, ← nsmul_eq_mul, deg_add, deg_nsmul, nsmul_eq_mul, add_comm]
      have hell_nat : n * (r + 1) ≤ ell k K D :=
        ell_family_ge (k := k) (K := K) (n := n) (r := r) b
      have hbound : (n * (r + 1) : ℤ) ≤ deg k K D + 1 :=
        (Nat.cast_le.mpr hell_nat).trans hell
      have hC0 := deg_nonneg k K hCeff
      have htoC : ((deg k K C).toNat : ℤ) = deg k K C := Int.toNat_of_nonneg hC0
      have htoB : ((deg k K B).toNat : ℤ) = deg k K B := Int.toNat_of_nonneg hdegB0
      have hsum :
          deg k K D + 1 = (deg k K B).toNat * r + ((deg k K C).toNat + 1) := by
        rw [hdeg, htoC, htoB]
        ring
      have hnat_z :
          (n * (r + 1) : ℤ) ≤ (deg k K B).toNat * r + ((deg k K C).toNat + 1) := by
        rw [← hsum]
        exact hbound
      exact_mod_cast hnat_z
  have hdegB := deg_nonneg k K hBeff
  rw [← Int.toNat_of_nonneg hdegB]
  exact_mod_cast hmain

end ChartVariable

section Auxiliary

/-- The rational function field `k(x) ⊆ K` generated by a transcendental element. -/
noncomputable def rationalSubfield (x : K) : IntermediateField k K :=
  IntermediateField.adjoin k {x}

omit [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
/-- The family `{b i * x^j}` is `k`-linearly independent over a `k(x)`-basis `b`. -/
theorem linearIndependent_basis_smul_x_pow {n r : ℕ} {x : K} (hx : Transcendental k x)
    (b : Module.Basis (Fin n) (rationalSubfield k K x) K) :
    LinearIndependent k fun p : Fin n × Fin (r + 1) =>
      (b p.1 : K) * x ^ (p.2 : ℕ) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let F := rationalSubfield k K x
  have hxF : x ∈ F := IntermediateField.mem_adjoin_of_mem k (Set.mem_singleton x)
  let s : Fin n → F := fun i =>
    ∑ j : Fin (r + 1), g (i, j) • ⟨x ^ (j : ℕ), by
      convert F.pow_mem hxF (Int.ofNat j) using 1
      exact (zpow_natCast x j).symm⟩
  have hsingle : ∀ i, s i • (b i : K) =
      ∑ j : Fin (r + 1), g (i, j) • ((b i : K) * x ^ (j : ℕ)) := by
    intro i
    simp only [s, Algebra.smul_def, map_sum]
    rw [Finset.sum_mul]
    congr 1
    ext j
    simp [mul_assoc, mul_comm, mul_left_comm]
  have hcombo : ∑ i : Fin n, s i • (b i : K) = 0 := by
    rw [Finset.sum_congr rfl fun i _ => hsingle i, ← Finset.sum_product']
    exact hg
  have hs : ∀ i, s i = 0 := (Fintype.linearIndependent_iff.mp b.linearIndependent) s hcombo
  intro p
  have hs' := hs p.1
  have hz : ∑ j : Fin (r + 1), g (p.1, j) • x ^ (j : ℕ) = 0 := by
    simpa [s] using congrArg Subtype.val hs'
  have hlin := linearIndependent_fin_pow_of_transcendental (k := k) (L := K) hx r
  rw [Fintype.linearIndependent_iff] at hlin
  exact hlin (fun j => g (p.1, j)) hz p.2

omit [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
/-- The structure map `k[X] → K` is evaluation of polynomials at the chart variable `X_K`. -/
theorem algebraMap_polynomial_eq_aeval_XK (p : k[X]) :
    algebraMap k[X] K p = aeval (XK k K) p := by
  have h : IsScalarTower.toAlgHom k k[X] K = aeval (XK k K) := by
    refine Polynomial.algHom_ext ?_
    rw [IsScalarTower.toAlgHom_apply, aeval_X,
      IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K, RatFunc.algebraMap_X]
    rfl
  calc algebraMap k[X] K p = IsScalarTower.toAlgHom k k[X] K p := rfl
    _ = aeval (XK k K) p := by rw [h]

omit [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
/-- The structure map `k⟮X⟯ → K` sends a rational function to the quotient of the
evaluations of its numerator and denominator at `X_K`. -/
theorem algebraMap_ratFunc_eq_div (c : k⟮X⟯) :
    algebraMap k⟮X⟯ K c = aeval (XK k K) c.num / aeval (XK k K) c.denom := by
  conv_lhs => rw [← RatFunc.num_div_denom c]
  rw [map_div₀, ← IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K,
    ← IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K,
    algebraMap_polynomial_eq_aeval_XK, algebraMap_polynomial_eq_aeval_XK]

omit [Algebra k[X] K] [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
/-- Coercion of `aeval` at the adjoined generator of `k(X_K)`. -/
theorem coe_aeval_adjoinSimple_gen_XK (p : k[X]) :
    ((aeval (AdjoinSimple.gen k (XK k K)) p : IntermediateField.adjoin k {XK k K}) : K)
      = aeval (XK k K) p := by
  have hgen : (IntermediateField.adjoin k {XK k K}).val (AdjoinSimple.gen k (XK k K)) = XK k K :=
    IntermediateField.AdjoinSimple.algebraMap_gen k (XK k K)
  calc ((aeval (AdjoinSimple.gen k (XK k K)) p : IntermediateField.adjoin k {XK k K}) : K)
      = (IntermediateField.adjoin k {XK k K}).val
          (aeval (AdjoinSimple.gen k (XK k K)) p) := rfl
    _ = aeval ((IntermediateField.adjoin k {XK k K}).val (AdjoinSimple.gen k (XK k K))) p :=
        (Polynomial.aeval_algHom_apply _ _ _).symm
    _ = aeval (XK k K) p := by rw [hgen]

omit [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
/-- The canonical `k`-embedding `k⟮X⟯ ≃ₐ k(X_K) ⊆ K` agrees with the structure map. -/
theorem coe_ratFuncAlgEquiv_XK (c : k⟮X⟯) :
    ((RatFunc.algEquivOfTranscendental (XK k K) (transcendental_XK k K) c :
        IntermediateField.adjoin k {XK k K}) : K)
      = algebraMap k⟮X⟯ K c := by
  conv_lhs => rw [← RatFunc.num_div_denom c]
  rw [map_div₀, RatFunc.algEquivOfTranscendental_algebraMap,
    RatFunc.algEquivOfTranscendental_algebraMap, IntermediateField.coe_div,
    coe_aeval_adjoinSimple_gen_XK, coe_aeval_adjoinSimple_gen_XK,
    algebraMap_ratFunc_eq_div]

/-! ### Target 2: finrank bridge -/

omit [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K] in
theorem finrank_eq_finrank_rationalSubfield_XK :
    Module.finrank k⟮X⟯ K =
      Module.finrank (rationalSubfield k K (algebraMap k⟮X⟯ K (RatFunc.X : k⟮X⟯))) K := by
  refine Algebra.finrank_eq_of_equiv_equiv
    (RatFunc.algEquivOfTranscendental (XK k K) (transcendental_XK k K)).toRingEquiv
    (RingEquiv.refl K) ?_
  ext c
  change algebraMap (IntermediateField.adjoin k {XK k K}) K
      (RatFunc.algEquivOfTranscendental (XK k K) (transcendental_XK k K) c)
    = algebraMap k⟮X⟯ K c
  rw [IntermediateField.algebraMap_apply]
  exact coe_ratFuncAlgEquiv_XK k K c

/-! ### Target 1: finite dimensionality over `k(x)` -/

omit [_root_.FunctionField k K] [IsFullConstantField k K] in
/-- Every element of `K` is algebraic over the polynomial subalgebra `k[X_K]`. -/
theorem isAlgebraic_adjoin_XK (z : K) :
    IsAlgebraic (Algebra.adjoin k {XK k K}) z := by
  have h1 : IsAlgebraic k⟮X⟯ z := Algebra.IsAlgebraic.isAlgebraic z
  have h2 : IsAlgebraic k[X] z := (IsFractionRing.isAlgebraic_iff k[X] k⟮X⟯ K).mpr h1
  obtain ⟨p, hp0, hpz⟩ := h2
  set e := Polynomial.algEquivOfTranscendental k (XK k K) (transcendental_XK k K) with he
  have hcomp : ((Algebra.adjoin k {XK k K}).val.comp e.toAlgHom : k[X] →ₐ[k] K)
      = IsScalarTower.toAlgHom k k[X] K := by
    refine Polynomial.algHom_ext ?_
    rw [AlgHom.comp_apply]
    have hex : e.toAlgHom X = e X := rfl
    rw [hex, he, Polynomial.algEquivOfTranscendental_apply_X,
      IsScalarTower.toAlgHom_apply, IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K,
      RatFunc.algebraMap_X]
    rfl
  refine ⟨p.map (e : k[X] →+* Algebra.adjoin k {XK k K}), ?_, ?_⟩
  · exact (Polynomial.map_ne_zero_iff e.injective).mpr hp0
  · rw [aeval_def, Polynomial.eval₂_map]
    have hring : ((algebraMap (Algebra.adjoin k {XK k K}) K).comp
        (e : k[X] →+* Algebra.adjoin k {XK k K})) = algebraMap k[X] K := by
      have := congrArg AlgHom.toRingHom hcomp
      exact this
    rw [hring, ← aeval_def]
    exact hpz

omit [_root_.FunctionField k K] [IsFullConstantField k K] in
/-- Exchange: if `x` is transcendental over `k`, then `X_K` is algebraic over `k[x]`. -/
theorem isAlgebraic_adjoin_x_XK {x : K} (hx : Transcendental k x) :
    IsAlgebraic (Algebra.adjoin k {x}) (XK k K) := by
  have h := IsAlgebraic.adjoin_singleton (R := k) (A := K) (B := K)
    (transcendental_XK k K) hx (isAlgebraic_adjoin_XK k K x)
  simpa using h

omit [_root_.FunctionField k K] [IsFullConstantField k K] in
/-- `X_K` is algebraic over the rational subfield `k(x)`. -/
theorem isAlgebraic_rationalSubfield_XK {x : K} (hx : Transcendental k x) :
    IsAlgebraic (rationalSubfield k K x) (XK k K) := by
  have hle : Algebra.adjoin k {x} ≤ (rationalSubfield k K x).toSubalgebra := by
    refine Algebra.adjoin_le ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact IntermediateField.subset_adjoin k {y} rfl
  exact (isAlgebraic_adjoin_x_XK k K hx).tower_top_of_subalgebra_le hle

omit [IsFullConstantField k K] in
/-- A function field is finite over the rational subfield generated by a transcendental element. -/
theorem finiteDimensional_rationalSubfield {x : K} (hx : Transcendental k x) :
    FiniteDimensional (rationalSubfield k K x) K := by
  set F := rationalSubfield k K x with hF
  set t := XK k K with ht
  have htF : IsIntegral F t := (isAlgebraic_rationalSubfield_XK k K hx).isIntegral
  have hFN : FiniteDimensional F (IntermediateField.adjoin F {t}) :=
    IntermediateField.adjoin.finiteDimensional htF
  set N := IntermediateField.adjoin F {t} with hN
  -- every polynomial evaluation at t lies in N
  have haev : ∀ p : k[X], aeval t p ∈ N := by
    intro p
    have h1 : aeval t (p.map (algebraMap k F)) = aeval t p :=
      Polynomial.aeval_map_algebraMap F t p
    rw [← h1]
    have h2 : aeval t (p.map (algebraMap k F)) ∈ Algebra.adjoin F ({t} : Set K) := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]
      exact ⟨p.map (algebraMap k F), rfl⟩
    exact IntermediateField.algebra_adjoin_le_adjoin F {t} h2
  -- the image of k⟮X⟯ inside K lies in N
  have hE : ∀ c : k⟮X⟯, algebraMap k⟮X⟯ K c ∈ N := by
    intro c
    rw [algebraMap_ratFunc_eq_div]
    exact div_mem (haev c.num) (haev c.denom)
  -- the subalgebra k[t] is contained in N
  have hsub : ∀ z : K, z ∈ Algebra.adjoin k ({t} : Set K) → z ∈ N := by
    intro z hz
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    exact haev p
  -- the inclusion ring hom k[t] →+* N
  let χ : Algebra.adjoin k ({t} : Set K) →+* N :=
    { toFun := fun a => ⟨a.1, hsub a.1 a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hχinj : Function.Injective χ := by
    intro a b hab
    have h : (a : K) = (b : K) := congrArg (fun z : N => (z : K)) hab
    exact Subtype.ext h
  -- basis of K over k⟮X⟯
  set b := Module.finBasis k⟮X⟯ K with hb
  -- each basis vector is integral over N
  have hbN : ∀ i, IsIntegral N (b i) := by
    intro i
    refine IsAlgebraic.isIntegral ?_
    obtain ⟨p, hp0, hpz⟩ := isAlgebraic_adjoin_XK k K (b i)
    refine ⟨p.map χ, (Polynomial.map_ne_zero_iff hχinj).mpr hp0, ?_⟩
    rw [aeval_def, Polynomial.eval₂_map]
    have hring : (algebraMap N K).comp χ
        = algebraMap (Algebra.adjoin k ({t} : Set K)) K := RingHom.ext fun a => rfl
    rw [hring, ← aeval_def]
    exact hpz
  -- K is generated over N by the basis vectors
  have htop : IntermediateField.adjoin N (Set.range ⇑b) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz := b.sum_repr z
    rw [← hz]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def]
    refine mul_mem ?_ (IntermediateField.subset_adjoin N _ ⟨i, rfl⟩)
    have hmem := hE (b.repr z i)
    have := IntermediateField.algebraMap_mem (IntermediateField.adjoin N (Set.range ⇑b))
      (⟨algebraMap k⟮X⟯ K (b.repr z i), hmem⟩ : N)
    rwa [IntermediateField.algebraMap_apply] at this
  have hfin : Finite (Set.range ⇑b) := (Set.finite_range ⇑b).to_subtype
  have hNtop : FiniteDimensional N (IntermediateField.adjoin N (Set.range ⇑b)) :=
    IntermediateField.finiteDimensional_adjoin fun z hz => by
      obtain ⟨i, rfl⟩ := hz
      exact hbN i
  have hNK : FiniteDimensional N K := by
    rw [htop] at hNtop
    exact (IntermediateField.topEquiv (F := N) (E := K)).toLinearEquiv.finiteDimensional
  exact Module.Finite.trans N K


/-- Stichtenoth 1.4.11 (≤) for general transcendental `x`. -/
theorem finrankAdjoin_le_deg_polar {x : K} (hx : ¬IsAlgebraic k x) :
    Module.finrank (rationalSubfield k K x) K ≤ deg k K (polarDivisor k K x) := by
  have hxT : Transcendental k x := hx
  by_cases hx0 : x = 0
  · subst hx0
    exact absurd isAlgebraic_zero hx
  have := finiteDimensional_rationalSubfield (k := k) (K := K) hxT
  let F := rationalSubfield k K x
  let n := Module.finrank F K
  let b := Module.finBasis F K
  let C := basisPoleBound k K b
  let B := polarDivisor k K x
  have hBpos : 0 < deg k K B := polarDivisor_pos k K hx0 hx
  have hBnn : 0 ≤ B := polarDivisor_nonneg k K x
  have hBeff : IsEffective k K B := polarDivisor_nonneg k K x
  have hdegB0 := deg_nonneg k K hBeff
  have hdpos : 0 < (deg k K B).toNat := by
    rw [← Int.toNat_of_nonneg hdegB0] at hBpos
    exact Int.ofNat_lt.mp hBpos
  have hmain : n ≤ (deg k K B).toNat :=
    le_of_forall_nat_mul_le (d := (deg k K B).toNat) (c := (deg k K C).toNat + 1) hdpos fun r => by
      let D := C + r • B
      have hDnn : 0 ≤ D := add_nonneg (basisPoleBound_nonneg k K b) fun v =>
        mul_nonneg (Nat.cast_nonneg r) (hBnn v)
      have hDeff : IsEffective k K D := hDnn
      have hCeff : IsEffective k K C := basisPoleBound_nonneg k K b
      let v : Fin n × Fin (r + 1) → K := fun p => (b p.1 : K) * x ^ (p.2 : ℕ)
      have hmem : ∀ p, v p ∈ RRspace k K D := by
        intro p
        rw [mem_RRspace_iff]
        exact memRRspace_basis_smul_x_pow (k := k) (K := K) (f := b) x hx0 r p.1 (p.2 : ℕ)
          (Nat.le_of_lt_succ (Fin.is_lt p.2))
      have hlin : LinearIndependent k v :=
        linearIndependent_basis_smul_x_pow (k := k) (K := K) hxT b
      have hsubset : span k (Set.range v) ≤ RRspace k K D := by
        refine span_le.mpr ?_
        rintro _ ⟨p, rfl⟩
        exact hmem p
      have hcard :
          n * (r + 1) ≤ Module.finrank k (span k (Set.range v)) := by
        have heq_card := finrank_span_eq_card (R := k) (M := K) hlin
        simp [heq_card, Fintype.card_prod, Fintype.card_fin]
      have hle : Module.finrank k (span k (Set.range v)) ≤ ell k K D :=
        Submodule.finrank_mono hsubset
      have hell : (ell k K D : ℤ) ≤ deg k K D + 1 :=
        ell_le_nonneg (k := k) (K := K) hDnn
      have hdeg : deg k K D = deg k K C + (r : ℤ) * deg k K B := by
        rw [add_comm, ← nsmul_eq_mul, deg_add, deg_nsmul, nsmul_eq_mul, add_comm]
      have hell_nat : n * (r + 1) ≤ ell k K D := Nat.le_trans hcard hle
      have hbound : (n * (r + 1) : ℤ) ≤ deg k K D + 1 :=
        (Nat.cast_le.mpr hell_nat).trans hell
      have hC0 := deg_nonneg k K hCeff
      have htoC : ((deg k K C).toNat : ℤ) = deg k K C := Int.toNat_of_nonneg hC0
      have htoB : ((deg k K B).toNat : ℤ) = deg k K B := Int.toNat_of_nonneg hdegB0
      have hsum :
          deg k K D + 1 = (deg k K B).toNat * r + ((deg k K C).toNat + 1) := by
        rw [hdeg, htoC, htoB]
        ring
      have hnat_z :
          (n * (r + 1) : ℤ) ≤ (deg k K B).toNat * r + ((deg k K C).toNat + 1) := by
        rw [← hsum]
        exact hbound
      exact_mod_cast hnat_z
  have hdegB := deg_nonneg k K hBeff
  rw [← Int.toNat_of_nonneg hdegB]
  exact_mod_cast hmain

/-- Coordinate-base specialization via the adjoin bridge. -/
theorem deg_polar_le_finrank {x : K} (hx : ¬IsAlgebraic k x)
    (hxgen : x = algebraMap k⟮X⟯ K (RatFunc.X : k⟮X⟯)) :
    Module.finrank k⟮X⟯ K ≤ deg k K (polarDivisor k K x) := by
  rw [hxgen] at hx ⊢
  have h := finrankAdjoin_le_deg_polar (k := k) (K := K) hx
  have hfin :
      Module.finrank k⟮X⟯ K =
        Module.finrank (rationalSubfield k K (algebraMap k⟮X⟯ K (RatFunc.X : k⟮X⟯))) K :=
    finrank_eq_finrank_rationalSubfield_XK k K
  exact hfin ▸ h

end Auxiliary

end PolarDivisor

end FunctionField.Chart

end
