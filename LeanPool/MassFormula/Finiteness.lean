/-
Copyright (c) 2026 Hyeon Seung-Hyeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hyeon Seung-Hyeon
-/

-- Adapted for Lean Pool from 0stellensatz/MassFormula at 7fa41a621f724f110183904d3fd19c6730a932ad.
module

public import LeanPool.MassFormula.Defs
import LeanPool.MassFormula.Discriminant
import LeanPool.MassFormula.EisensteinMonogenic
import LeanPool.MassFormula.First
import LeanPool.MassFormula.UniformizerParam
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.Algebra.Order.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Integral

/-!
# Auxiliary file: `sigma_infinite_iff`—the finiteness dichotomy of **Remark 1°** (p.1031)

`sigma K n` is infinite exactly when `K` has equal characteristic `p` and `p` divides `n`
([Serre 1978, Remark 1°, p.1031][Serre1978]). The two directions are separate goals:

- *Infinite implies equal characteristic and `p ∣ n`* (`eq_and_dvd_of_infinite`)—proved, and by the
  mass formula itself rather than by the tame classification and Krasner's finiteness theorem.
  Outside the asserted case `n` survives into `𝒪[K]` (`eq_and_dvd_of_natCast_eq_zero` is the
  characteristic bookkeeping), so at an Eisenstein generator `ξ` of any `L` in `sigma K n`
  (`exists_eisenstein_generator`) the term `n * ξ ^ (n - 1)` of the derivative of `g` at `ξ` has
  *finite* valuation `n * v + (n - 1)`, where `v` is the valuation of `n`, and orthogonality of the
  power basis (`le_addVal_sum_iff`) forbids the other terms from cancelling it:
  `d L ≤ n * v + n - 1` (`addVal_derivative_eq_d`), a bound uniform in `L`, that is `c L ≤ n * v`
  (`c_le_of_mem_sigma`). An infinite `sigma K n` would then feed infinitely many equal nonzero terms
  into the sum of Theorem 1, forcing it to `⊤` (`ENNReal.tsum_const_eq_top_of_ne_zero`), while
  `tsum_one_div_q_pow_c` evaluates it to `n`.
- *Equal characteristic and `p ∣ n` implies infinite* (`infinite_of_eq_of_dvd`)—proved by an
  explicit Eisenstein family rather than by the Artin–Schreier layers the classical argument
  composes. For each `1 ≤ m` the polynomial `X ^ n + π ^ m * X + π` is Eisenstein, so a root
  generates a member of `sigma K n` (`isTotallyRamified_adjoin`); and because `n` vanishes in
  `𝒪[K]`—this is where equal characteristic and `p ∣ n` enter—the term `n * X ^ (n - 1)` of the
  derivative dies, leaving the constant `π ^ m` *exactly*, so that `d L = n * m` for the member `L`
  it generates (`addVal_derivative_eq_d`; `exists_mem_sigma_d_eq`). The discriminant exponent is an
  invariant of the subfield, so these members are pairwise distinct and `m` indexes an injection of
  `ℕ` into `sigma K n`.

## References

* [Serre1978] J-P. Serre, *Une «formule de masse» pour les extensions totalement ramifiées de
  degré donné d'un corps local*, C. R. Acad. Sci. Paris **286** (1978), Série A, 1031–1036.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer, 1979.
-/

public section

open ValuativeRel IsDiscreteValuationRing
open scoped ENNReal

namespace MassFormula

variable (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
  [IsNonarchimedeanLocalField K]

omit [IsUniformAddGroup K] in
/-- The characteristic bookkeeping of Remark 1°: if a positive `n` vanishes in `𝒪[K]`, then `K` has
equal characteristic and the residue characteristic divides `n`—`ringChar K` is then a prime divisor
of `n`, and it vanishes in the residue field too, so the prime `ringChar 𝓀[K]` divides it and the
two coincide ([Serre 1978, Remark 1°, p.1031][Serre1978]). -/
private theorem eq_and_dvd_of_natCast_eq_zero (n : ℕ) (hn : 0 < n) (h0 : (n : ↥𝒪[K]) = 0) :
    ringChar K = ringChar 𝓀[K] ∧ ringChar 𝓀[K] ∣ n := by
  have : IsFractionRing ↥𝒪[K] K :=
    inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
  have hinj : Function.Injective (algebraMap ↥𝒪[K] K) := IsFractionRing.injective ↥𝒪[K] K
  -- `n` vanishes in `K`, so `ringChar K` is a prime divisor of `n`
  have hK : (n : K) = 0 := by
    have h1 := congrArg (algebraMap ↥𝒪[K] K) h0
    rwa [map_natCast, map_zero] at h1
  have hdvd : ringChar K ∣ n := ringChar.dvd hK
  have hKne : ringChar K ≠ 0 := fun hzero =>
    hn.ne' (Nat.eq_zero_of_zero_dvd (hzero ▸ hdvd))
  have hprime : (ringChar K).Prime :=
    (CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hKne
  -- `ringChar K` vanishes in `𝒪[K]`, hence in the residue field
  have hO : ((ringChar K : ℕ) : ↥𝒪[K]) = 0 := by
    apply hinj
    rw [map_natCast, map_zero]
    exact (ringChar.spec K (ringChar K)).mpr dvd_rfl
  have hres : ((ringChar K : ℕ) : 𝓀[K]) = 0 := by
    have h1 := congrArg (IsLocalRing.residue ↥𝒪[K]) hO
    rwa [map_natCast, map_zero] at h1
  -- so the prime `ringChar 𝓀[K]` divides the prime `ringChar K`, and the two coincide
  have heq : ringChar 𝓀[K] = ringChar K :=
    (hprime.eq_one_or_self_of_dvd _ (ringChar.dvd hres)).resolve_left
      (CharP.char_ne_one 𝓀[K] (ringChar 𝓀[K]))
  exact ⟨heq.symm, by rw [heq]; exact hdvd⟩

omit [IsUniformAddGroup K] in
/-- The uniform bound behind the finiteness half: when `n` does not vanish in `𝒪[K]`, writing `v`
for the valuation of `n`, every `L` in `sigma K n` has `c L ≤ n * v`. At an Eisenstein generator `ξ`
(`exists_eisenstein_generator`) the term of index `n - 1` of the derivative of `g` at `ξ`, the sum
of the terms `i * a i * ξ ^ (i - 1)`, is `n * ξ ^ (n - 1)`, of valuation exactly `n * v + (n - 1)`;
by orthogonality of the power basis (`le_addVal_sum_iff`) no other term can cancel it, so that
valuation is at most `n * v + n - 1`—and it *is* `d L` (`addVal_derivative_eq_d`). This is the
elementary form of the classical bound `d ≤ n - 1 + n * v` on the different of a totally ramified
extension ([Serre 1979, Chap. III, §6, Prop. 13][Serre1979]), the tame case `v = 0` included, with
no case split and no different ideal. Public rather than private: at `t = 0` it is also the tame
half of `c_eq_zero_iff`. -/
theorem c_le_of_mem_sigma (n t : ℕ) (hn : 0 < n)
    (ht : addVal ↥𝒪[K] (n : ↥𝒪[K]) = (t : ℕ∞)) (L : IntermediateField K (SeparableClosure K))
    (hL : L ∈ sigma K n) : c L ≤ n * t := by
  obtain ⟨x, π, hπ, hint, hei, hadj, hdeg⟩ := exists_eisenstein_generator K n hn L hL
  subst hadj
  subst hdeg
  have hDVR : IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x})) :=
    isDiscreteValuationRing_integers hπ hint hei
  -- the derivative of the minimal polynomial, as a combination of the power basis
  have hmonic : (minpoly 𝒪[K] x).Monic := minpoly.monic hint
  have hderivlt : (Polynomial.derivative (minpoly 𝒪[K] x)).natDegree <
      (minpoly 𝒪[K] x).natDegree := Polynomial.natDegree_derivative_lt hn.ne'
  have hsum : Polynomial.aeval (integralGen hint) (Polynomial.derivative (minpoly 𝒪[K] x)) =
      ∑ i : Fin (minpoly 𝒪[K] x).natDegree,
        algebraMap ↥𝒪[K] ↥(integers (IntermediateField.adjoin K {x}))
          ((Polynomial.derivative (minpoly 𝒪[K] x)).coeff (i : ℕ)) *
            integralGen hint ^ (i : ℕ) := by
    rw [Polynomial.aeval_eq_sum_range' hderivlt, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => Algebra.smul_def _ _
  -- the coefficient of index `n - 1` is `n` itself, by monicity
  have hcoeff : (Polynomial.derivative (minpoly 𝒪[K] x)).coeff
      ((minpoly 𝒪[K] x).natDegree - 1) = ((minpoly 𝒪[K] x).natDegree : ↥𝒪[K]) := by
    rw [Polynomial.coeff_derivative, Nat.sub_add_cancel hn, hmonic.coeff_natDegree, one_mul,
      ← Nat.cast_add_one, Nat.sub_add_cancel hn]
  -- its term has valuation `n * t + (n - 1)`, which orthogonality makes a cap on the sum's
  have hkey : addVal ↥(integers (IntermediateField.adjoin K {x}))
      (Polynomial.aeval (integralGen hint) (Polynomial.derivative (minpoly 𝒪[K] x))) ≤
        (((minpoly 𝒪[K] x).natDegree * t + ((minpoly 𝒪[K] x).natDegree - 1) : ℕ) : ℕ∞) := by
    by_contra hgt
    rw [not_le] at hgt
    have hm := (ENat.add_one_le_iff (ENat.natCast_ne_top _)).mpr hgt
    rw [hsum] at hm
    have hterm := (le_addVal_sum_iff hπ (irreducible_integralGen hπ hint hei) hn
      (associated_algebraMap_pow hπ hint hei) _ _).mp hm
        ⟨(minpoly 𝒪[K] x).natDegree - 1, by omega⟩
    rw [hcoeff, ht] at hterm
    have hcast : ((minpoly 𝒪[K] x).natDegree : ℕ∞) * (t : ℕ∞) +
        (((minpoly 𝒪[K] x).natDegree - 1 : ℕ) : ℕ∞) =
          (((minpoly 𝒪[K] x).natDegree * t + ((minpoly 𝒪[K] x).natDegree - 1) : ℕ) : ℕ∞) := by
      push_cast
      ring
    rw [hcast] at hterm
    exact absurd ((ENat.add_one_le_iff (ENat.natCast_ne_top _)).mp hterm) (lt_irrefl _)
  -- read the bound off `d`, and convert to `c`
  rw [addVal_derivative_eq_d hπ hint hei] at hkey
  have hd : d (IntermediateField.adjoin K {x}) ≤
      (minpoly 𝒪[K] x).natDegree * t + ((minpoly 𝒪[K] x).natDegree - 1) := by
    exact_mod_cast hkey
  have hfr : Module.finrank K ↥(IntermediateField.adjoin K {x}) =
      (minpoly 𝒪[K] x).natDegree := hL.1
  change d (IntermediateField.adjoin K {x}) + 1 -
      Module.finrank K ↥(IntermediateField.adjoin K {x}) ≤ (minpoly 𝒪[K] x).natDegree * t
  rw [hfr]
  generalize (minpoly 𝒪[K] x).natDegree * t = a at hd ⊢
  omega

/-- The finiteness half of Remark 1°, contrapositively: if `sigma K n` is infinite, then `K` has
equal characteristic and the residue characteristic divides `n`
([Serre 1978, Remark 1°, p.1031][Serre1978]). -/
theorem eq_and_dvd_of_infinite (n : ℕ) (hn : 0 < n) (h : (sigma K n).Infinite) :
    ringChar K = ringChar 𝓀[K] ∧ ringChar 𝓀[K] ∣ n := by
  by_contra hcon
  -- outside the asserted case `n` survives into `𝒪[K]`, so `c` is uniformly bounded on `Σ_n`
  have hne : (n : ↥𝒪[K]) ≠ 0 := fun h0 => hcon (eq_and_dvd_of_natCast_eq_zero K n hn h0)
  have hfin : addVal ↥𝒪[K] (n : ↥𝒪[K]) ≠ ⊤ := fun htop => hne (addVal_eq_top_iff.mp htop)
  obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.mp hfin
  -- an infinite family of terms `≥ q^{-n t}` would push the sum of Theorem 1 past its value `n`
  have := h.to_subtype
  have hbound : ∀ L : sigma K n,
      1 / (q K : ℝ≥0∞) ^ (n * t) ≤ 1 / (q K : ℝ≥0∞) ^ c L.1 := fun L => by
    rw [one_div, one_div]
    exact ENNReal.inv_le_inv.mpr (pow_le_pow_right'
      (by exact_mod_cast (one_lt_q K).le) (c_le_of_mem_sigma K n t hn ht.symm L.1 L.2))
  have htop : ∑' _ : sigma K n, 1 / (q K : ℝ≥0∞) ^ (n * t) = ⊤ :=
    ENNReal.tsum_const_eq_top_of_ne_zero (by
      rw [one_div, Ne, ENNReal.inv_eq_zero]
      exact ENNReal.pow_ne_top (ENNReal.natCast_ne_top (q K)))
  have hle : (⊤ : ℝ≥0∞) ≤ (n : ℝ≥0∞) :=
    calc (⊤ : ℝ≥0∞) = ∑' _ : sigma K n, 1 / (q K : ℝ≥0∞) ^ (n * t) := htop.symm
      _ ≤ ∑' L : sigma K n, 1 / (q K : ℝ≥0∞) ^ c L.1 := ENNReal.tsum_le_tsum hbound
      _ = n := tsum_one_div_q_pow_c K n hn
  exact ENNReal.natCast_ne_top n (top_le_iff.mp hle)

omit [IsUniformAddGroup K] in
/-- The Eisenstein family behind the infinitude half: when `n` vanishes in `𝒪[K]`, every prescribed
discriminant exponent `n * m` with `1 ≤ m` is attained on `sigma K n`. The member is generated by a
root of `X ^ n + π ^ m * X + π`—Eisenstein, hence irreducible and totally ramified of degree `n`
(`isTotallyRamified_adjoin`)—and since `n` is `0` in `𝒪[K]` the term `n * X ^ (n - 1)` dies, leaving
the derivative equal to the *constant* `π ^ m`, so `addVal_derivative_eq_d` evaluates `d L = n * m`
with no discriminant computation at all. -/
private theorem exists_mem_sigma_d_eq (n : ℕ) (hn2 : 2 ≤ n) (h0 : (n : ↥𝒪[K]) = 0)
    (m : ℕ) (hm : 0 < m) : ∃ L ∈ sigma K n, d L = n * m := by
  have : IsFractionRing ↥𝒪[K] K :=
    inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
  have hinj : Function.Injective (algebraMap ↥𝒪[K] K) := IsFractionRing.injective ↥𝒪[K] K
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥𝒪[K]
  -- the Eisenstein model `X ^ n + π ^ m X + π` and its shape
  set r : Polynomial ↥𝒪[K] := Polynomial.C (π ^ m) * Polynomial.X + Polynomial.C π with hr
  set g : Polynomial ↥𝒪[K] := Polynomial.X ^ n + r with hgdef
  have hrdeg : r.degree < (n : WithBot ℕ) :=
    lt_of_le_of_lt Polynomial.degree_linear_le (by exact_mod_cast (by omega : 1 < n))
  have hgmonic : g.Monic := Polynomial.monic_X_pow_add hrdeg
  have hgdeg : g.natDegree = n :=
    Polynomial.natDegree_eq_of_degree_eq_some (by
      rw [hgdef, Polynomial.degree_add_eq_left_of_degree_lt
        (by rw [Polynomial.degree_X_pow]; exact hrdeg), Polynomial.degree_X_pow])
  have hc0 : g.coeff 0 = π := by
    rw [hgdef, hr, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      ite_eq_right (by omega : ¬(0 = n)), Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
      Polynomial.coeff_C_zero, mul_zero, zero_add, zero_add]
  have hc1 : g.coeff 1 = π ^ m := by
    rw [hgdef, hr, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      ite_eq_right (by omega : ¬(1 = n)), Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
      Polynomial.coeff_C, ite_eq_right one_ne_zero, mul_one, zero_add, add_zero]
  have hck : ∀ k : ℕ, 2 ≤ k → k ≠ n → g.coeff k = 0 := by
    intro k hk2 hkn
    rw [hgdef, hr, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      ite_eq_right hkn, Polynomial.coeff_C_mul, Polynomial.coeff_X,
      ite_eq_right (by omega : ¬(1 = k)), Polynomial.coeff_C, ite_eq_right (by omega : ¬(k = 0)),
      mul_zero, add_zero, zero_add]
  -- the model is Eisenstein at `π`, hence irreducible over `𝒪[K]` and over `K`
  have hEis : g.IsEisensteinAt (Submodule.span ↥𝒪[K] {π}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hgmonic.leadingCoeff, Ideal.submodule_span_eq, Ideal.mem_span_singleton]
      exact fun hdvd => hπ.not_isUnit (isUnit_of_dvd_one hdvd)
    · intro k hk
      rw [hgdeg] at hk
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
      rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · interval_cases k
        · rw [hc0]
        · rw [hc1]
          exact dvd_pow_self π hm.ne'
      · rw [hck k hk2 (by omega)]
        exact dvd_zero π
    · rw [hc0, Ideal.submodule_span_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨z, hz⟩
      apply hπ.not_isUnit
      refine isUnit_of_dvd_one ⟨z, ?_⟩
      have h1 : π * 1 = π * (π * z) := by rw [mul_one, ← mul_assoc, ← sq, ← hz]
      exact mul_left_cancel₀ hπ.ne_zero h1
  have hprime : Ideal.IsPrime (Submodule.span ↥𝒪[K] ({π} : Set ↥𝒪[K])) := by
    rw [Ideal.submodule_span_eq, ← hπ.maximalIdeal_eq]
    exact Ideal.IsMaximal.isPrime inferInstance
  have h𝒪irr : Irreducible g :=
    hEis.irreducible hprime hgmonic.isPrimitive (by rw [hgdeg]; omega)
  set gK : Polynomial K := g.map (algebraMap ↥𝒪[K] K) with hgK
  have hKirr : Irreducible gK :=
    hgmonic.irreducible_iff_irreducible_map_fraction_map.mp h𝒪irr
  -- `(n : 𝒪[K]) = 0` kills the term `n X ^ (n - 1)`: the derivative is the constant `π ^ m`
  have hderiv : Polynomial.derivative g = Polynomial.C (π ^ m) := by
    rw [hgdef, hr, Polynomial.derivative_add, Polynomial.derivative_add,
      Polynomial.derivative_X_pow, Polynomial.derivative_C_mul_X, Polynomial.derivative_C,
      add_zero, h0, Polynomial.C_0, zero_mul, zero_add]
  -- so the model is separable, and a root exists in the separable closure
  have hgKderiv : Polynomial.derivative gK ≠ 0 := by
    rw [hgK, Polynomial.derivative_map, hderiv, Polynomial.map_C]
    simp only [Ne, Polynomial.C_eq_zero]
    exact (map_ne_zero_iff _ hinj).mpr (pow_ne_zero m hπ.ne_zero)
  have hKsep : gK.Separable := (Polynomial.separable_iff_derivative_ne_zero hKirr).mpr hgKderiv
  have hgKnatdeg : gK.natDegree = n := by rw [hgK, hgmonic.natDegree_map, hgdeg]
  have hgKdeg0 : gK.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree (hgmonic.map _).ne_zero, hgKnatdeg]
    exact_mod_cast (by omega : n ≠ 0)
  obtain ⟨x, hxroot⟩ := IsSepClosed.exists_aeval_eq_zero (SeparableClosure K) gK hgKdeg0 hKsep
  have haevg : Polynomial.aeval x g = 0 := by
    rw [hgK, Polynomial.aeval_map_algebraMap] at hxroot
    exact hxroot
  have hint : IsIntegral ↥𝒪[K] x := ⟨g, hgmonic, haevg⟩
  -- the minimal polynomial over `𝒪[K]` is the model itself
  have hmineq : minpoly ↥𝒪[K] x = g := by
    obtain ⟨c, hc⟩ := minpoly.isIntegrallyClosed_dvd hint haevg
    rcases h𝒪irr.isUnit_or_isUnit hc with hu | hu
    · exact absurd hu (Polynomial.not_isUnit_of_natDegree_pos _ (minpoly.natDegree_pos hint))
    · refine Polynomial.eq_of_monic_of_associated (minpoly.monic hint) hgmonic ?_
      exact ⟨hu.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩
  have hei : (minpoly ↥𝒪[K] x).IsEisensteinAt (Submodule.span ↥𝒪[K] {π}) := by
    rw [hmineq]
    exact hEis
  -- membership in `Σ_n`: degree `n` via the minimal polynomial, totally ramified by the Eisenstein
  -- shape of `gK`
  have hminK : minpoly K x = gK := by
    have hxroot' : Polynomial.aeval x gK = 0 := by
      rw [hgK, Polynomial.aeval_map_algebraMap]
      exact haevg
    exact (minpoly.eq_of_irreducible_of_monic hKirr hxroot' (hgmonic.map _)).symm
  have hfr : Module.finrank K ↥(IntermediateField.adjoin K {x}) = n := by
    rw [IntermediateField.adjoin.finrank hint.tower_top, hminK, hgKnatdeg]
  have hmem : IntermediateField.adjoin K {x} ∈ sigma K n :=
    mem_sigma.mpr ⟨hfr, isTotallyRamified_adjoin hπ hint hei⟩
  -- the discriminant exponent: `d = v_L (g' (ξ)) = v_L (π ^ m) = n * m`
  have hDVR : IsDiscreteValuationRing ↥(integers (IntermediateField.adjoin K {x})) :=
    isDiscreteValuationRing_integers hπ hint hei
  have hd := addVal_derivative_eq_d hπ hint hei
  have hval : addVal ↥(integers (IntermediateField.adjoin K {x}))
      (algebraMap ↥𝒪[K] ↥(integers (IntermediateField.adjoin K {x})) (π ^ m)) =
        (n : ℕ∞) * (m : ℕ∞) := by
    rw [addVal_algebraMap hπ (irreducible_integralGen hπ hint hei) (minpoly.natDegree_pos hint)
      (associated_algebraMap_pow hπ hint hei), hπ.addVal_pow, hmineq, hgdeg]
  rw [hmineq, hderiv, Polynomial.aeval_C, hval] at hd
  refine ⟨IntermediateField.adjoin K {x}, hmem, ?_⟩
  exact_mod_cast hd.symm

omit [IsUniformAddGroup K] in
/-- The infinitude half of Remark 1°: in equal characteristic `p` with `p ∣ n`, the set
`sigma K n` is infinite ([Serre 1978, Remark 1°, p.1031][Serre1978]). -/
theorem infinite_of_eq_of_dvd (n : ℕ) (hn : 0 < n) (hchar : ringChar K = ringChar 𝓀[K])
    (hdvd : ringChar 𝓀[K] ∣ n) : (sigma K n).Infinite := by
  -- the residue characteristic is prime, so `n ≥ 2`, and `n` vanishes in `𝒪[K]`
  have hp : (ringChar 𝓀[K]).Prime :=
    (CharP.char_is_prime_or_zero 𝓀[K] (ringChar 𝓀[K])).resolve_right
      (CharP.char_ne_zero_of_finite 𝓀[K] (ringChar 𝓀[K]))
  have hn2 : 2 ≤ n := le_trans hp.two_le (Nat.le_of_dvd hn hdvd)
  have h0 : (n : ↥𝒪[K]) = 0 := by
    have : IsFractionRing ↥𝒪[K] K :=
      inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
    apply IsFractionRing.injective ↥𝒪[K] K
    rw [map_natCast, map_zero]
    exact (ringChar.spec K n).mpr (by rw [hchar]; exact hdvd)
  -- the Eisenstein family realizes pairwise distinct discriminant exponents `n * (m + 1)`
  choose L hLmem hLd using fun m : ℕ =>
    exists_mem_sigma_d_eq K n hn2 h0 (m + 1) m.succ_pos
  have hinjL : Function.Injective L := by
    intro m₁ m₂ h12
    have h2 : n * (m₂ + 1) = n * (m₁ + 1) := by rw [← hLd m₂, ← h12, hLd m₁]
    have h3 := Nat.eq_of_mul_eq_mul_left (show 0 < n by omega) h2
    omega
  exact Set.infinite_of_injective_forall_mem hinjL hLmem

/-- `sigma K n` is infinite exactly when `K` has equal characteristic `p` and `p` divides `n`,
assembled from the two halves above
([Serre 1978, Remark 1°, p.1031][Serre1978]). -/
theorem sigma_infinite_iff (n : ℕ) (hn : 0 < n) :
    (sigma K n).Infinite ↔ ringChar K = ringChar 𝓀[K] ∧ ringChar 𝓀[K] ∣ n :=
  ⟨eq_and_dvd_of_infinite K n hn, fun h => infinite_of_eq_of_dvd K n hn h.1 h.2⟩

end MassFormula
