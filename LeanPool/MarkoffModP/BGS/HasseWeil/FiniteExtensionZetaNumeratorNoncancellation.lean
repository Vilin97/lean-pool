/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionIndexedZetaRationality
public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionZetaSimplePole
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.RingTheory.PowerSeries.Expand

/-!
# Noncancellation of the indexed zeta numerator

The strict divisor-count growth across one degree-index step detects the
uncancelled factor `1 - T^d` in the indexed zeta denominator.  This file
proves the formal coefficient statement and then specializes it to the
finite-extension effective-divisor series.
-/

@[expose] public section

namespace BGS.HasseWeil

noncomputable section

open scoped Polynomial PowerSeries

/-- The partial sum of the coefficients of
`Z(T) (1 - T) (1 - q T)` is the boundary difference
`Z_{n+1} - q Z_n`. -/
theorem sum_range_coeff_mul_curveZetaDenominator
    (Z : PowerSeries ℂ) (q n : ℕ) :
    (∑ k ∈ Finset.range (n + 2),
        PowerSeries.coeff k (Z * curveZetaDenominator q)) =
      PowerSeries.coeff (n + 1) Z -
        (q : ℂ) * PowerSeries.coeff n Z := by
  induction n with
  | zero =>
      rw [show 0 + 2 = 2 by omega]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      have hcoeffOne :
          PowerSeries.coeff 1 (curveZetaDenominator q) =
            -((q : ℂ) + 1) := by
        rw [curveZetaDenominator, PowerSeries.coeff_one_mul]
        simp [linearPowerSeriesFactor]
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
        PowerSeries.coeff_one_mul, hcoeffOne]
      simp [curveZetaDenominator, linearPowerSeriesFactor]
      ring
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        Finset.sum_range_succ, ih,
        coeff_mul_curveZetaDenominator_succ_succ]
      ring

/-- For an ordinary curve denominator, every sufficiently late strict
boundary difference forces the numerator to be nonzero at `T = 1`. -/
theorem curveZetaNumerator_eval_one_ne_zero_of_boundary
    (Z : PowerSeries ℂ) (q n : ℕ) (P : Polynomial ℂ)
    (hdegree : P.natDegree < n + 2)
    (hboundary : (q : ℂ) * PowerSeries.coeff n Z ≠
      PowerSeries.coeff (n + 1) Z)
    (hform : HasCurveZetaRationalForm Z q P) :
    P.eval 1 ≠ 0 := by
  have heval : P.eval 1 =
      PowerSeries.coeff (n + 1) Z -
        (q : ℂ) * PowerSeries.coeff n Z := by
    rw [Polynomial.eval_eq_sum_range' hdegree]
    simp only [one_pow, mul_one]
    have hcoeff : ∀ k,
        P.coeff k = PowerSeries.coeff k
          (Z * curveZetaDenominator q) := by
      intro k
      have h := congrArg (PowerSeries.coeff k) hform
      simpa only [Polynomial.coeff_coe] using h.symm
    simp_rw [hcoeff]
    exact sum_range_coeff_mul_curveZetaDenominator Z q n
  rw [heval, sub_ne_zero]
  exact hboundary.symm

/-- Compress a power series supported in degrees divisible by `d`. -/
def compressPowerSeries (d : ℕ) (Z : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => PowerSeries.coeff (d * n) Z

/-- Expanding the compressed series recovers a series supported on multiples
of `d`. -/
theorem expand_compressPowerSeries_eq
    (Z : PowerSeries ℂ) (d : ℕ) (hd : 0 < d)
    (hsupport : ∀ n, ¬ d ∣ n → PowerSeries.coeff n Z = 0) :
    PowerSeries.expand d hd.ne' (compressPowerSeries d Z) = Z := by
  ext n
  rw [PowerSeries.coeff_expand]
  split_ifs with hn
  · simp only [compressPowerSeries, PowerSeries.coeff_mk]
    rw [show d * (n / d) = n by
      rw [mul_comm, Nat.div_mul_cancel hn]]
  · exact (hsupport n hn).symm

/-- Power-series expansion sends the ordinary denominator over `q^d` to the
indexed denominator over `q`. -/
theorem expand_curveZetaDenominator
    (q d : ℕ) (hd : 0 < d) :
    PowerSeries.expand d hd.ne' (curveZetaDenominator (q ^ d)) =
      indexedCurveZetaDenominator q d := by
  simp [curveZetaDenominator, indexedCurveZetaDenominator,
    linearPowerSeriesFactor]

/-- Polynomial and power-series expansion commute with the polynomial
coercion. -/
theorem coe_polynomial_expand
    (P : Polynomial ℂ) (d : ℕ) (hd : 0 < d) :
    ((Polynomial.expand ℂ d P : Polynomial ℂ) : PowerSeries ℂ) =
      PowerSeries.expand d hd.ne' (P : PowerSeries ℂ) := by
  ext n
  rw [Polynomial.coeff_coe, Polynomial.coeff_expand hd,
    PowerSeries.coeff_expand]
  split_ifs <;> simp only [Polynomial.coeff_coe]

/-- Indexed rationality for a series supported on multiples of `d` compresses
to ordinary rationality, with numerator `P.contract d`. -/
theorem hasCurveZetaRationalForm_compress_of_indexed
    (Z : PowerSeries ℂ) (q d : ℕ) (P : Polynomial ℂ)
    (hd : 0 < d)
    (hsupport : ∀ n, ¬ d ∣ n → PowerSeries.coeff n Z = 0)
    (hindexed : HasIndexedCurveZetaRationalForm Z q d P) :
    HasCurveZetaRationalForm (compressPowerSeries d Z) (q ^ d)
      (P.contract d) := by
  let B := compressPowerSeries d Z
  have hexpanded :
      PowerSeries.expand d hd.ne'
          (B * curveZetaDenominator (q ^ d)) =
        (P : PowerSeries ℂ) := by
    rw [map_mul, expand_compressPowerSeries_eq Z d hd hsupport,
      expand_curveZetaDenominator q d hd]
    exact hindexed
  ext n
  have h := congrArg (PowerSeries.coeff (d * n)) hexpanded
  simpa only [B, PowerSeries.coeff_expand_mul,
    Polynomial.coeff_coe, Polynomial.coeff_contract hd.ne', mul_comm] using h

/-- Under the same support hypothesis, the indexed polynomial is the
`d`-fold expansion of its contraction. -/
theorem polynomial_expand_contract_eq_of_indexed
    (Z : PowerSeries ℂ) (q d : ℕ) (P : Polynomial ℂ)
    (hd : 0 < d)
    (hsupport : ∀ n, ¬ d ∣ n → PowerSeries.coeff n Z = 0)
    (hindexed : HasIndexedCurveZetaRationalForm Z q d P) :
    Polynomial.expand ℂ d (P.contract d) = P := by
  apply Polynomial.coe_injective ℂ
  rw [coe_polynomial_expand (P.contract d) d hd]
  let B := compressPowerSeries d Z
  have hform := hasCurveZetaRationalForm_compress_of_indexed
    Z q d P hd hsupport hindexed
  calc
    PowerSeries.expand d hd.ne' ((P.contract d : Polynomial ℂ) :
        PowerSeries ℂ) =
        PowerSeries.expand d hd.ne'
          (B * curveZetaDenominator (q ^ d)) := by rw [hform]
    _ = Z * indexedCurveZetaDenominator q d := by
      rw [map_mul, expand_compressPowerSeries_eq Z d hd hsupport,
        expand_curveZetaDenominator q d hd]
    _ = (P : PowerSeries ℂ) := hindexed

/-- A sufficiently late strict growth witness in one admissible degree forces
noncancellation of the indexed numerator at `T = 1`.

The bound `P.natDegree < n + 2*d` is the exact condition needed after
compressing degrees by `d`; the admissibility condition `d ∣ n` identifies
the boundary coefficients with consecutive compressed coefficients. -/
theorem indexedCurveZetaNumerator_eval_one_ne_zero_of_growth
    (Z : PowerSeries ℂ) (A : ℕ → ℕ) (q d n : ℕ)
    (P : Polynomial ℂ)
    (hd : 0 < d)
    (hcoeff : ∀ m, PowerSeries.coeff m Z = (A m : ℂ))
    (hsupport : ∀ m, ¬ d ∣ m → A m = 0)
    (hn : d ∣ n)
    (hdegree : P.natDegree < n + 2 * d)
    (hgrowth : q ^ d * A n < A (n + d))
    (hindexed : HasIndexedCurveZetaRationalForm Z q d P) :
    P.eval 1 ≠ 0 := by
  let B := compressPowerSeries d Z
  let R := P.contract d
  have hZsupport : ∀ m, ¬ d ∣ m → PowerSeries.coeff m Z = 0 := by
    intro m hm
    rw [hcoeff, hsupport m hm]
    norm_num
  have hform : HasCurveZetaRationalForm B (q ^ d) R := by
    exact hasCurveZetaRationalForm_compress_of_indexed
      Z q d P hd hZsupport hindexed
  have hPexpand : Polynomial.expand ℂ d R = P := by
    exact polynomial_expand_contract_eq_of_indexed
      Z q d P hd hZsupport hindexed
  obtain ⟨k, hk⟩ := hn
  have hnEq : n = d * k := by omega
  have hdegreeR : R.natDegree < k + 2 := by
    have hdegreeExpand :
        (Polynomial.expand ℂ d R).natDegree < (k + 2) * d := by
      rw [hPexpand]
      calc
        P.natDegree < n + 2 * d := hdegree
        _ = (k + 2) * d := by rw [hnEq]; ring
    rw [Polynomial.natDegree_expand] at hdegreeExpand
    exact (Nat.mul_lt_mul_right hd).mp hdegreeExpand
  have hboundary : ((q ^ d : ℕ) : ℂ) * PowerSeries.coeff k B ≠
      PowerSeries.coeff (k + 1) B := by
    intro heq
    have hcoeffBoundary : ((q ^ d : ℕ) : ℂ) * (A n : ℂ) =
        (A (n + d) : ℂ) := by
      simpa only [B, compressPowerSeries, PowerSeries.coeff_mk,
        hcoeff, hnEq, Nat.mul_add, Nat.mul_one] using heq
    have hNat : q ^ d * A n = A (n + d) := by
      exact_mod_cast hcoeffBoundary
    exact (Nat.ne_of_lt hgrowth) hNat
  have hRone : R.eval 1 ≠ 0 :=
    curveZetaNumerator_eval_one_ne_zero_of_boundary
      B (q ^ d) k R hdegreeR hboundary hform
  have heval : P.eval 1 = R.eval 1 := by
    rw [← hPexpand, Polynomial.expand_eval]
    simp
  rwa [heval]

/-- The coefficient-cast effective-divisor series inherits indexed numerator
noncancellation from any sufficiently late admissible strict-growth witness. -/
theorem effectiveDivisorCountSeries_indexedNumerator_eval_one_ne_zero_of_growth
    (A : ℕ → ℕ) (q d n : ℕ) (P : Polynomial ℂ)
    (hd : 0 < d)
    (hsupport : ∀ m, ¬ d ∣ m → A m = 0)
    (hn : d ∣ n)
    (hdegree : P.natDegree < n + 2 * d)
    (hgrowth : q ^ d * A n < A (n + d))
    (hindexed : HasIndexedCurveZetaRationalForm
      (effectiveDivisorCountSeries A) q d P) :
    P.eval 1 ≠ 0 := by
  apply indexedCurveZetaNumerator_eval_one_ne_zero_of_growth
    (effectiveDivisorCountSeries A) A q d n P hd
  · intro m
    simp [effectiveDivisorCountSeries]
  · exact hsupport
  · exact hn
  · exact hdegree
  · exact hgrowth
  · exact hindexed

open BGS.CorvajaZannier

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [DecidableEq (RatFunc K)]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]

local instance numeratorNoncancellationConstantAlgebra : Algebra K L :=
  RingHom.toAlgebra ((algebraMap (RatFunc K) L).comp
    (algebraMap K (RatFunc K)))

local instance numeratorNoncancellationConstantTower :
    IsScalarTower K (RatFunc K) L :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The finite-extension effective-divisor series is supported precisely in
degrees admissible for the divisor-degree index. -/
theorem finiteExtensionEffectiveDivisorCount_eq_zero_of_not_dvd_index
    (n : ℕ)
    (hn : ¬ finiteExtensionDivisorDegreeIndex K L ∣ n) :
    finiteExtensionEffectiveDivisorCount K L n = 0 := by
  rw [finiteExtensionEffectiveDivisorCount]
  apply Fintype.card_eq_zero_iff.mpr
  refine ⟨fun D =>
    (not_exists_finiteExtensionDivisor_degree_eq_of_not_dvd K L n hn) ?_⟩
  refine ⟨finiteExtensionEffectiveDivisorToDivisor K L D.1, ?_⟩
  rw [← finiteExtensionEffectiveDivisorDegree_cast K L D.1, D.2]

/-- Strict growth witnesses supplied by uniform Riemann--Roch can be chosen
beyond any prescribed lower degree and remain divisible by the canonical
divisor-degree index. -/
theorem exists_finiteExtensionEffectiveDivisorCount_pow_mul_lt_add_index_ge
    (genus threshold lowerBound : ℕ)
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L))
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold) :
    ∃ n, lowerBound ≤ n ∧ threshold ≤ n ∧
      finiteExtensionDivisorDegreeIndex K L ∣ n ∧
      Nat.card K ^ finiteExtensionDivisorDegreeIndex K L *
          finiteExtensionEffectiveDivisorCount K L n <
        finiteExtensionEffectiveDivisorCount K L
          (n + finiteExtensionDivisorDegreeIndex K L) := by
  let d := finiteExtensionDivisorDegreeIndex K L
  let m := lowerBound + threshold
  let n := m * d
  have hd : 0 < d := finiteExtensionDivisorDegreeIndex_pos K L
  have hlower : lowerBound ≤ n := by
    dsimp only [n, m]
    nlinarith
  have hthreshold : threshold ≤ n := by
    dsimp only [n, m]
    nlinarith
  refine ⟨n, hlower, hthreshold, ?_, ?_⟩
  · dsimp only [n, d]
    exact dvd_mul_left _ _
  · apply
      finiteExtensionEffectiveDivisorCount_pow_mul_lt_add_index_of_uniformRiemann
        K L genus threshold n hconstants hRiemann hthreshold
    exact ⟨by simpa [n, d] using
      finiteExtensionDivisorClassOfDegreeIndexMul K L m⟩

/-- Uniform Riemann--Roch forces noncancellation for every indexed rational
form of the finite-extension effective-divisor series. -/
theorem finiteExtensionEffectiveDivisorZeta_indexedNumerator_eval_one_ne_zero_of_uniformRiemann
    (genus threshold : ℕ)
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L))
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (P : Polynomial ℂ)
    (hindexed : HasIndexedCurveZetaRationalForm
      (effectiveDivisorCountSeries
        (finiteExtensionEffectiveDivisorCount K L))
      (Nat.card K) (finiteExtensionDivisorDegreeIndex K L) P) :
    P.eval 1 ≠ 0 := by
  obtain ⟨n, hnDegree, _, hnDvd, hgrowth⟩ :=
    exists_finiteExtensionEffectiveDivisorCount_pow_mul_lt_add_index_ge
      K L genus threshold (P.natDegree + 1) hconstants hRiemann
  apply
    effectiveDivisorCountSeries_indexedNumerator_eval_one_ne_zero_of_growth
      (finiteExtensionEffectiveDivisorCount K L) (Nat.card K)
      (finiteExtensionDivisorDegreeIndex K L) n P
  · exact finiteExtensionDivisorDegreeIndex_pos K L
  · intro m hm
    exact finiteExtensionEffectiveDivisorCount_eq_zero_of_not_dvd_index
      K L m hm
  · exact hnDvd
  · have hd := finiteExtensionDivisorDegreeIndex_pos K L
    omega
  · exact hgrowth
  · exact hindexed

/-- Uniform Riemann--Roch also forces noncancellation for every indexed
rational form of the exhaustive closed-place point-count zeta series. -/
theorem finiteExtensionClosedPlaceZeta_indexedNumerator_eval_one_ne_zero_of_uniformRiemann
    (genus threshold : ℕ)
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L))
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold)
    (P : Polynomial ℂ)
    (hindexed : HasIndexedCurveZetaRationalForm
      (formalPointCountZeta
        (finiteExtensionClosedPlaceExtensionCount K L))
      (Nat.card K) (finiteExtensionDivisorDegreeIndex K L) P) :
    P.eval 1 ≠ 0 := by
  apply
    finiteExtensionEffectiveDivisorZeta_indexedNumerator_eval_one_ne_zero_of_uniformRiemann
      K L genus threshold hconstants hRiemann P
  rw [effectiveDivisorCountSeries_eq_formalPointCountZeta
    (finiteExtensionEffectiveDivisorCount K L)
    (finiteExtensionClosedPlaceExtensionCount K L)
    (finiteExtensionEffectiveDivisorCount_zero K L)
    (finiteExtensionEffectiveDivisorPointCountRecurrence K L)]
  exact hindexed

/-- The finite-extension closed-place zeta series has an indexed rational
form whose numerator is normalized and does not vanish at `T = 1`. -/
theorem exists_finiteExtensionClosedPlaceZeta_indexed_rational_nonvanishing
    (genus threshold : ℕ)
    (hconstants : algebraicClosure K L =
      (⊥ : IntermediateField K L))
    (hRiemann : HasFiniteExtensionUniformEventualRiemannFormula
      K L genus threshold) :
    ∃ P : Polynomial ℂ,
      P.coeff 0 = 1 ∧ P.eval 1 ≠ 0 ∧
        HasIndexedCurveZetaRationalForm
          (formalPointCountZeta
            (finiteExtensionClosedPlaceExtensionCount K L))
          (Nat.card K) (finiteExtensionDivisorDegreeIndex K L) P := by
  obtain ⟨P, hPzero, hPform⟩ :=
    exists_finiteExtensionClosedPlaceZeta_indexed_rational
      K L genus threshold hconstants hRiemann
  refine ⟨P, hPzero, ?_, hPform⟩
  exact
    finiteExtensionClosedPlaceZeta_indexedNumerator_eval_one_ne_zero_of_uniformRiemann
      K L genus threshold hconstants hRiemann P hPform

end

end BGS.HasseWeil
