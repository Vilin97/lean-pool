/-
Copyright (c) 2026 Hyeon Seung-Hyeon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hyeon Seung-Hyeon
-/

-- Adapted for Lean Pool from 0stellensatz/MassFormula at 7fa41a621f724f110183904d3fd19c6730a932ad.
module

public import LeanPool.MassFormula.Defs
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import LeanPool.MassFormula.EisensteinMonogenic
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.Integral

/-!
# Auxiliary file: `sub_one_le_d`—the bound `n - 1 ≤ d (L)`

Footnote 1 of the paper refers to *Corps locaux* for the fact that `c L = d L - n + 1` is a
nonnegative integer ([Serre 1978, p.1031, footnote 1][Serre1978]); in the `ℕ`-valued
model this is the bound `n - 1 ≤ d L` for `L` in `sigma K n`.

The classical route: for `L` / `K` totally ramified of degree `n` the residue degree is `1`, so the
valuation of `K` composed with the norm is the valuation of `L` on the units of `L`, and `d L` is
the valuation of the discriminant, equal to the valuation of the different; and the different of a
totally ramified extension has valuation at least `e - 1 = n - 1`
([Serre 1979, Chap. III, §6][Serre1979]), with equality exactly in the tame case. In the hand-rolled
`discIdeal` model the natural approach is via the power basis of a uniformizer of `L`: its
discriminant is plus or minus the norm of the derivative of the (Eisenstein) minimal polynomial at
that uniformizer, and that derivative has valuation at least `n - 1` term by term.

## References

* [Serre1978] J-P. Serre, *Une «formule de masse» pour les extensions totalement ramifiées de
  degré donné d'un corps local*, C. R. Acad. Sci. Paris **286** (1978), Série A, 1031–1036.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer, 1979.
-/

public section

open ValuativeRel IntermediateField

namespace MassFormula

variable (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
  [IsNonarchimedeanLocalField K]

/-- In a Dedekind domain, an element `ξ` of `Q` outside `Q ^ 2`, for `Q` prime, has
`ξ ^ i ∉ Q ^ (i + 1)`: writing the ideal `(ξ)` as `Q * R` with `Q` not dividing `R`, the
divisibility of `Q ^ i * R ^ i` by `Q ^ (i + 1)` cancels to `Q ∣ R ^ i`, against the primality of
`Q`. -/
private theorem pow_notMem_pow_succ {A : Type*} [CommRing A] [IsDedekindDomain A]
    {Q : Ideal A} (hQp : Q.IsPrime) {ξ : A} (hξ : ξ ∈ Q) (hξ2 : ξ ∉ Q ^ 2) (i : ℕ) :
    ξ ^ i ∉ Q ^ (i + 1) := by
  intro h
  have hξ0 : ξ ≠ 0 := fun h0 => hξ2 (h0 ▸ (Q ^ 2).zero_mem)
  have hQ0 : Q ≠ ⊥ := fun hb => hξ0 (by simpa [hb] using hξ)
  have hQprime : Prime Q := Ideal.prime_of_isPrime hQ0 hQp
  obtain ⟨Rc, hRc⟩ : Q ∣ Ideal.span {ξ} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hξ)
  have hQR : ¬ Q ∣ Rc := by
    intro hd
    obtain ⟨R', hR'⟩ := hd
    have h2 : Q ^ 2 ∣ Ideal.span {ξ} := ⟨R', by rw [hRc, hR', pow_two, mul_assoc]⟩
    exact hξ2 (Ideal.le_of_dvd h2 (Ideal.mem_span_singleton_self ξ))
  have hdvd : Q ^ (i + 1) ∣ Ideal.span {ξ} ^ i := by
    rw [Ideal.span_singleton_pow]
    exact Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr h)
  rw [hRc, mul_pow, pow_succ] at hdvd
  have hQi : (Q : Ideal A) ^ i ≠ 0 := pow_ne_zero i (by simpa using hQ0)
  have hdvd' : Q ∣ Rc ^ i := (mul_dvd_mul_iff_left hQi).mp hdvd
  exact hQR (hQprime.dvd_of_dvd_pow hdvd')

/-- The Eisenstein shape, abstractly: over a local base `R`, a monic polynomial of degree at most
`n` annihilating an element `ξ` of `Q` outside `Q ^ 2`, for `Q` a prime of a Dedekind `R`-algebra
`A` whose extension of the maximal ideal of `R` lies in `Q ^ n`, has degree exactly `n`, all lower
coefficients in the maximal ideal of `R`, and constant coefficient outside its square—the three
Eisenstein conditions at once. Each part is the same one-liner: were it to fail, the relation
expressing `ξ ^ deg` as minus the sum of the terms `c j * ξ ^ j` would place some `ξ ^ i` in
`Q ^ (i + 1)`, against `pow_notMem_pow_succ`. -/
private theorem eisenstein_shape {R A : Type*} [CommRing R] [IsLocalRing R] [CommRing A]
    [IsDedekindDomain A] [Algebra R A]
    {n : ℕ} (hn : 0 < n) {Q : Ideal A} (hQp : Q.IsPrime)
    (hmap : Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) ≤ Q ^ n)
    {ξ : A} (hξ : ξ ∈ Q) (hξ2 : ξ ∉ Q ^ 2)
    {G : Polynomial R} (hGm : G.Monic) (hGa : Polynomial.aeval ξ G = 0)
    (hdeg : G.natDegree ≤ n) :
    G.natDegree = n ∧ (∀ i < n, G.coeff i ∈ IsLocalRing.maximalIdeal R) ∧
    G.coeff 0 ∉ IsLocalRing.maximalIdeal R ^ 2 := by
  set m := G.natDegree with hm
  -- the fundamental relation expressing `ξ ^ m` as minus the sum of the `c j * ξ ^ j` for `j < m`
  have hrel : (ξ : A) ^ m = -∑ j ∈ Finset.range m, algebraMap R A (G.coeff j) * ξ ^ j := by
    have h0 := hGa
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hGm.coeff_natDegree, one_smul] at h0
    have h1 := eq_neg_of_add_eq_zero_right h0
    simpa only [Algebra.smul_def] using h1
  -- every coefficient below the top is a nonunit
  have hcoeff : ∀ i < m, G.coeff i ∈ IsLocalRing.maximalIdeal R := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i IH =>
      intro him
      by_contra hui
      have hu : IsUnit (G.coeff i) := by
        rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hui
      have hmem : algebraMap R A (G.coeff i) * ξ ^ i ∈ Q ^ (i + 1) := by
        have hsplit := Finset.add_sum_erase (Finset.range m)
          (fun j => algebraMap R A (G.coeff j) * ξ ^ j) (Finset.mem_range.mpr him)
        have hval : algebraMap R A (G.coeff i) * ξ ^ i
            = -ξ ^ m - ∑ j ∈ (Finset.range m).erase i,
            algebraMap R A (G.coeff j) * ξ ^ j := by
          have h2 : algebraMap R A (G.coeff i) * ξ ^ i
              + ∑ j ∈ (Finset.range m).erase i, algebraMap R A (G.coeff j) * ξ ^ j
              = -ξ ^ m := by
            rw [hsplit, ← neg_eq_iff_eq_neg.mpr hrel]
          exact eq_sub_of_add_eq h2
        rw [hval]
        refine sub_mem (neg_mem ?_) (Ideal.sum_mem _ fun j hj => ?_)
        · exact Ideal.pow_le_pow_right him (Ideal.pow_mem_pow hξ m)
        · rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with hji | hji
          · have hj' : G.coeff j ∈ IsLocalRing.maximalIdeal R :=
              IH j hji (lt_trans hji him)
            have h3 : algebraMap R A (G.coeff j) ∈ Q ^ n :=
              hmap (Ideal.mem_map_of_mem _ hj')
            exact Ideal.mul_mem_right _ _
              (Ideal.pow_le_pow_right (by omega) h3)
          · exact Ideal.mul_mem_left _ _
              (Ideal.pow_le_pow_right hji (Ideal.pow_mem_pow hξ j))
      obtain ⟨v, hv⟩ := hu.map (algebraMap R A)
      rw [← hv] at hmem
      have h4 : ((v⁻¹ : Aˣ) : A) * ((v : A) * ξ ^ i) ∈ Q ^ (i + 1) :=
        Ideal.mul_mem_left _ _ hmem
      rw [← mul_assoc, Units.inv_mul, one_mul] at h4
      exact pow_notMem_pow_succ hQp hξ hξ2 i h4
  -- the degree is exactly `n`
  have hdegeq : m = n := by
    by_contra hne
    have hlt : m < n := lt_of_le_of_ne hdeg hne
    have h5 : ξ ^ m ∈ Q ^ (m + 1) := by
      rw [hrel]
      refine neg_mem (Ideal.sum_mem _ fun j hj => ?_)
      have hj' := hcoeff j (Finset.mem_range.mp hj)
      have h6 : algebraMap R A (G.coeff j) ∈ Q ^ n := hmap (Ideal.mem_map_of_mem _ hj')
      exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) h6)
    exact pow_notMem_pow_succ hQp hξ hξ2 m h5
  -- the constant coefficient avoids `𝓂 ^ 2`
  have hc0 : G.coeff 0 ∉ IsLocalRing.maximalIdeal R ^ 2 := by
    intro h0
    have himg : algebraMap R A (G.coeff 0) ∈ Q ^ (n + 1) := by
      have h1 : algebraMap R A (G.coeff 0)
          ∈ Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) ^ 2 := by
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ h0
      have h2 : Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) ^ 2
          ≤ Q ^ (2 * n) := by
        calc Ideal.map (algebraMap R A) (IsLocalRing.maximalIdeal R) ^ 2
            ≤ (Q ^ n) ^ 2 := Ideal.pow_right_mono hmap 2
          _ = Q ^ (2 * n) := by rw [← pow_mul, mul_comm]
      exact Ideal.pow_le_pow_right (by omega) (h2 h1)
    have h7 : ξ ^ n ∈ Q ^ (n + 1) := by
      rw [hdegeq] at hrel
      rw [hrel]
      refine neg_mem (Ideal.sum_mem _ fun j hj => ?_)
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        simpa using himg
      · have hj' := hcoeff j (by rw [hdegeq]; exact Finset.mem_range.mp hj)
        have h8 : algebraMap R A (G.coeff j) ∈ Q ^ n := hmap (Ideal.mem_map_of_mem _ hj')
        have h9 : ξ ^ j ∈ Q := Ideal.pow_mem_of_mem _ hξ j hj0
        have h10 := Ideal.mul_mem_mul h8 h9
        rwa [← pow_succ] at h10
    exact pow_notMem_pow_succ hQp hξ hξ2 n h7
  exact ⟨hdegeq, fun i hi => hcoeff i (by rw [hdegeq]; exact hi), hc0⟩

omit [IsUniformAddGroup K] in
private theorem exists_ramified_ideal_element (n : ℕ) (hn : 0 < n)
    (L : IntermediateField K (SeparableClosure K)) (hL : L ∈ sigma K n) :
    ∃ (π : 𝒪[K]) (Q : Ideal ↥(integers L)) (ξ : ↥(integers L)),
      Irreducible π ∧ Q.IsPrime ∧
      Ideal.map (algebraMap ↥𝒪[K] ↥(integers L)) 𝓂[K] ≤ Q ^ n ∧
      ξ ∈ Q ∧ ξ ∉ Q ^ 2 := by
  classical
  obtain ⟨hLn, hLram⟩ := hL
  have : IsFractionRing ↥𝒪[K] K :=
    inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
  have : FiniteDimensional K ↥L :=
    FiniteDimensional.of_finrank_pos (by rw [hLn]; exact hn)
  have hIC : IsIntegralClosure ↥(integers L) ↥𝒪[K] ↥L :=
    inferInstanceAs (IsIntegralClosure ↥(integralClosure ↥𝒪[K] ↥L) ↥𝒪[K] ↥L)
  have hDed : IsDedekindDomain ↥(integers L) :=
    IsIntegralClosure.isDedekindDomain ↥𝒪[K] K ↥L ↥(integers L)
  have hInt : Algebra.IsIntegral ↥𝒪[K] ↥(integers L) :=
    IsIntegralClosure.isIntegral_algebra ↥𝒪[K] (A := ↥(integers L)) ↥L
  -- a uniformizer of `𝒪[K]`
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥𝒪[K]
  have hπspan : 𝓂[K] = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  -- injectivity of the structure maps
  have hinjL : Function.Injective (algebraMap ↥𝒪[K] ↥L) := by
    rw [IsScalarTower.algebraMap_eq ↥𝒪[K] K ↥L]
    exact (algebraMap K ↥L).injective.comp (IsFractionRing.injective ↥𝒪[K] K)
  have hinj : Function.Injective (algebraMap ↥𝒪[K] ↥(integers L)) := by
    intro a b hab
    apply hinjL
    rw [IsScalarTower.algebraMap_apply ↥𝒪[K] ↥(integers L) ↥L, hab,
      ← IsScalarTower.algebraMap_apply]
  -- a maximal ideal `Q` of `integers L`, lying over `𝓂[K]`
  obtain ⟨Q, hQmax⟩ := Ideal.exists_maximal ↥(integers L)
  have := hQmax
  have hcom : Ideal.comap (algebraMap ↥𝒪[K] ↥(integers L)) Q = 𝓂[K] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q)
  have hmapQ : Ideal.map (algebraMap ↥𝒪[K] ↥(integers L)) 𝓂[K] ≤ Q := by
    rw [← hcom]
    exact Ideal.map_comap_le
  -- total ramifiedness: the extension of `𝓂[K]` to `integers L` lies in `Q ^ n`
  have hram : Ideal.ramificationIdx' 𝓂[K] (maximalIdealAbove L) = n := by
    have he : MassFormula.ramificationIdx L = n := by
      rw [← hLn]
      exact hLram
    exact he
  have hpow : Ideal.map (algebraMap ↥𝒪[K] ↥(integers L)) 𝓂[K] ≤ Q ^ n := by
    have h1 : Ideal.map (algebraMap ↥𝒪[K] ↥(integers L)) 𝓂[K]
        ≤ maximalIdealAbove L ^ n := by
      have h2 := Ideal.le_pow_ramificationIdx' (p := 𝓂[K]) (P := maximalIdealAbove L)
      rwa [hram] at h2
    have h3 : maximalIdealAbove L ≤ Q :=
      hQmax.isPrime.radical_le_iff.mpr hmapQ
    exact le_trans h1 (Ideal.pow_right_mono h3 n)
  -- `Q` is a nonzero proper ideal; pick `ξ ∈ Q ∖ Q²`
  have hQbot : Q ≠ ⊥ := by
    intro hb
    have hπm : π ∈ 𝓂[K] := hπspan ▸ Ideal.mem_span_singleton_self π
    have h1 : π ∈ Ideal.comap (algebraMap ↥𝒪[K] ↥(integers L)) Q := by
      rw [hcom]
      exact hπm
    rw [hb] at h1
    have h0 : algebraMap ↥𝒪[K] ↥(integers L) π = 0 :=
      Ideal.mem_bot.mp (Ideal.mem_comap.mp h1)
    exact hπ.ne_zero (hinj (by rw [h0, map_zero]))
  obtain ⟨ξ, hξQ, hξQ2⟩ : ∃ y ∈ Q ^ 1, y ∉ Q ^ 2 := by
    simpa using Q.exists_mem_pow_notMem_pow_succ hQbot hQmax.ne_top 1
  rw [pow_one] at hξQ
  exact ⟨π, Q, ξ, hπ, hQmax.isPrime, hpow, hξQ, hξQ2⟩

omit [IsUniformAddGroup K] in
/-- Every member of `sigma K n` is generated by a root of an Eisenstein polynomial—the extraction
converse to `isTotallyRamified_adjoin`. Route: `integers L` is a Dedekind domain (Krull–Akizuki
through the separable-finite route, `IsIntegralClosure.isDedekindDomain`); *any* maximal ideal `Q`
of `integers L` lies over `𝓂[K]` (integrality) and contains `maximalIdealAbove L`, so
`IsTotallyRamified` puts the extension of `𝓂[K]` inside `Q ^ n`; an element `ξ` of `Q` outside
`Q ^ 2` then satisfies `eisenstein_shape`, so its minimal polynomial is Eisenstein of degree exactly
`n` and `ξ` generates `L` by dimension count. No fundamental identity summing the `e i * f i` to
`n`, no localness of `integers L`, and no norm computation is needed—the paper's valuation-based
argument (p.1032, around eq. (5)) is replaced by divisibility of ideal powers. -/
theorem exists_eisenstein_generator (n : ℕ) (hn : 0 < n)
    (L : IntermediateField K (SeparableClosure K)) (hL : L ∈ sigma K n) :
    ∃ (x : SeparableClosure K) (π : 𝒪[K]), Irreducible π ∧ IsIntegral 𝒪[K] x ∧
      (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π}) ∧
      IntermediateField.adjoin K {x} = L ∧ (minpoly 𝒪[K] x).natDegree = n := by
  classical
  obtain ⟨hLn, hLram⟩ := hL
  have : IsFractionRing ↥𝒪[K] K :=
    inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
  have : FiniteDimensional K ↥L :=
    FiniteDimensional.of_finrank_pos (by rw [hLn]; exact hn)
  have hIC : IsIntegralClosure ↥(integers L) ↥𝒪[K] ↥L :=
    inferInstanceAs (IsIntegralClosure ↥(integralClosure ↥𝒪[K] ↥L) ↥𝒪[K] ↥L)
  have hDed : IsDedekindDomain ↥(integers L) :=
    IsIntegralClosure.isDedekindDomain ↥𝒪[K] K ↥L ↥(integers L)
  have hInt : Algebra.IsIntegral ↥𝒪[K] ↥(integers L) :=
    IsIntegralClosure.isIntegral_algebra ↥𝒪[K] (A := ↥(integers L)) ↥L
  obtain ⟨π, Q, ξ, hπ, hQprime, hpow, hξQ, hξQ2⟩ :=
    exists_ramified_ideal_element K n hn L ⟨hLn, hLram⟩
  have hπspan : 𝓂[K] = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  -- the minimal polynomial of `ξ` over `𝒪[K]`
  have hξint : IsIntegral ↥𝒪[K] ξ := Algebra.IsIntegral.isIntegral ξ
  set G : Polynomial ↥𝒪[K] := minpoly ↥𝒪[K] ξ with hG
  have hGmonic : G.Monic := minpoly.monic hξint
  have hGa : Polynomial.aeval ξ G = 0 := minpoly.aeval _ _
  -- transports of `ξ` up the tower
  set ξL : ↥L := algebraMap ↥(integers L) ↥L ξ with hξL
  set x : SeparableClosure K := algebraMap ↥L (SeparableClosure K) ξL with hx
  have hinjS : Function.Injective (algebraMap ↥L (SeparableClosure K)) :=
    (algebraMap ↥L (SeparableClosure K)).injective
  have hinjLL : Function.Injective (algebraMap ↥(integers L) ↥L) :=
    Subtype.val_injective
  have hξLint : IsIntegral ↥𝒪[K] ξL :=
    hξint.map (IsScalarTower.toAlgHom ↥𝒪[K] ↥(integers L) ↥L)
  have hxint : IsIntegral ↥𝒪[K] x :=
    hξLint.map (IsScalarTower.toAlgHom ↥𝒪[K] ↥L (SeparableClosure K))
  have hminξL : minpoly ↥𝒪[K] ξL = G := minpoly.algebraMap_eq hinjLL ξ
  have hminx : minpoly ↥𝒪[K] x = G := by
    rw [hx, minpoly.algebraMap_eq hinjS ξL, hminξL]
  -- degree bound `deg G ≤ n` through the field minimal polynomial
  have hmKx : minpoly K ξL = G.map (algebraMap ↥𝒪[K] K) := by
    rw [← hminξL]
    exact minpoly.isIntegrallyClosed_eq_field_fractions' K hξLint
  have hdegle : G.natDegree ≤ n := by
    have h1 : (minpoly K ξL).natDegree ≤ Module.finrank K ↥L := minpoly.natDegree_le ξL
    rwa [hmKx, hGmonic.natDegree_map, hLn] at h1
  -- the abstract core
  obtain ⟨hdegeq, hcoeffs, hc0⟩ :=
    eisenstein_shape hn hQprime hpow hξQ hξQ2 hGmonic hGa hdegle
  -- Eisenstein packaging
  have heis : G.IsEisensteinAt (Submodule.span ↥𝒪[K] {π}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hGmonic.leadingCoeff]
      intro h1
      have h2 : (Ideal.span {π} : Ideal ↥𝒪[K]) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one
      rw [← hπspan] at h2
      exact (IsLocalRing.maximalIdeal.isMaximal ↥𝒪[K]).ne_top h2
    · intro i hi
      have h1 := hcoeffs i (by rw [← hdegeq]; exact hi)
      rwa [hπspan] at h1
    · intro h1
      apply hc0
      rwa [hπspan]
  -- the adjoin recovers `L`
  have hxL : x ∈ L := by
    rw [hx]
    exact ξL.2
  have hle : IntermediateField.adjoin K {x} ≤ L := by
    rw [IntermediateField.adjoin_le_iff]
    simpa using hxL
  have hxKint : IsIntegral K x := hxint.tower_top
  have hfr : Module.finrank K ↥(IntermediateField.adjoin K {x}) = n := by
    rw [IntermediateField.adjoin.finrank hxKint]
    have h1 : minpoly K x = minpoly K ξL := minpoly.algebraMap_eq hinjS ξL
    rw [h1, hmKx, hGmonic.natDegree_map, hdegeq]
  have hadj : IntermediateField.adjoin K {x} = L := by
    apply IntermediateField.eq_of_le_of_finrank_le hle
    rw [hfr, hLn]
  refine ⟨x, π, hπ, hxint, ?_, hadj, ?_⟩
  · rw [hminx]
    exact heis
  · rw [hminx]
    exact hdegeq

private lemma aeval_derivative_mem_pow {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {g : Polynomial R} {ξ : A} (hgmonic : g.Monic)
    (hn : 0 < g.natDegree) (hcoeffmem : ∀ k, k < g.natDegree →
      algebraMap R A (g.coeff k) ∈ Ideal.span {ξ} ^ g.natDegree) :
    Polynomial.aeval ξ (Polynomial.derivative g) ∈ Ideal.span {ξ} ^ (g.natDegree - 1) := by
  let n := g.natDegree
  have hdeg : (Polynomial.derivative g).natDegree < n :=
    Polynomial.natDegree_derivative_lt hn.ne'
  rw [Polynomial.aeval_eq_sum_range' hdeg]
  refine Ideal.sum_mem _ fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Polynomial.coeff_derivative, Algebra.smul_def, map_mul]
  rcases Nat.lt_or_ge (i + 1) n with hi1 | hi1
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
      (Ideal.pow_le_pow_right (by omega) (hcoeffmem (i + 1) hi1)))
  · have hieq : i = n - 1 := by omega
    have hcoeff : g.coeff (i + 1) = 1 := by
      rw [show i + 1 = n from by omega]
      exact hgmonic.coeff_natDegree
    rw [hcoeff]
    refine Ideal.mul_mem_left _ _ ?_
    rw [hieq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

omit [IsUniformAddGroup K] in
/-- The norm of the derivative of `g` at an Eisenstein root has a preimage in the `n - 1`-st
power of `𝓂[K]`—the derivative lies in the `n - 1`-st power of the ideal `(ξ)` inside the integral
closure, and the norm of `ξ` is a sign times the constant coefficient, a uniformizer. -/
private theorem norm_derivative_core {π : 𝒪[K]} (hπ : Irreducible π) {x : SeparableClosure K}
    (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π})) :
    ∃ N₀ : 𝒪[K],
      algebraMap 𝒪[K] K N₀ =
        Algebra.norm K (Polynomial.aeval (IntermediateField.AdjoinSimple.gen K x)
          (Polynomial.derivative (minpoly K (IntermediateField.AdjoinSimple.gen K x)))) ∧
      N₀ ∈ 𝓂[K] ^ ((minpoly 𝒪[K] x).natDegree - 1) := by
  classical
  have : IsFractionRing 𝒪[K] K :=
    inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
  set L' := IntermediateField.adjoin K {x} with hL'
  set x' : ↥L' := IntermediateField.AdjoinSimple.gen K x with hx'
  set g : Polynomial 𝒪[K] := minpoly 𝒪[K] x with hg
  set n : ℕ := g.natDegree with hn'
  have hn : 0 < n := minpoly.natDegree_pos hint
  have hgmonic : g.Monic := minpoly.monic hint
  have hminKx : minpoly K x = g.map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hint
  have hminx' : minpoly K x' = minpoly K x :=
    (minpoly.algebraMap_eq (algebraMap ↥L' (SeparableClosure K)).injective x').symm
  -- the unit relation
  obtain ⟨ξ, u, hξval, hu, hbu⟩ := exists_unit_relation hπ hint hei
  have hvalaev : ∀ P : Polynomial 𝒪[K],
      ((Polynomial.aeval ξ P : ↥(integers L')) : ↥L') = Polynomial.aeval x' P := by
    intro P
    have h2 : Polynomial.aeval x' P =
        algebraMap ↥(integers L') ↥L' (Polynomial.aeval ξ P) := by
      rw [← Polynomial.aeval_algebraMap_apply,
        show algebraMap ↥(integers L') ↥L' ξ = x' from hξval]
    calc ((Polynomial.aeval ξ P : ↥(integers L')) : ↥L')
        = algebraMap ↥(integers L') ↥L' (Polynomial.aeval ξ P) := rfl
      _ = Polynomial.aeval x' P := h2.symm
  -- the associated-uniformizer structure of the constant coefficient
  have hπg₀ : Associated π (g.coeff 0) := associated_pi_coeff_zero hπ hint hei
  -- the constant coefficient sits in `(ξ) ^ n`
  have hb₀mem : algebraMap 𝒪[K] ↥(integers L') (g.coeff 0) ∈ Ideal.span {ξ} ^ n := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨w, hw⟩ := hu
    refine ⟨-((w⁻¹ : (↥(integers L'))ˣ) : ↥(integers L')), ?_⟩
    have h1 : algebraMap 𝒪[K] ↥(integers L') (g.coeff 0) = -ξ ^ n * ↑w⁻¹ := by
      calc algebraMap 𝒪[K] ↥(integers L') (g.coeff 0)
          = algebraMap 𝒪[K] ↥(integers L') (g.coeff 0) * ↑w * ↑w⁻¹ := by
            rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
        _ = -ξ ^ n * ↑w⁻¹ := by rw [hw, hbu]
    rw [h1]
    ring
  -- lower coefficients sit there too
  have hcoeffmem : ∀ k, k < n →
      algebraMap 𝒪[K] ↥(integers L') (g.coeff k) ∈ Ideal.span {ξ} ^ n := by
    intro k hk
    have h1 : π ∣ g.coeff k := by
      have := hei.mem hk
      rwa [Ideal.submodule_span_eq, Ideal.mem_span_singleton] at this
    obtain ⟨e, he⟩ := (hπg₀.symm.dvd).trans h1
    rw [he, map_mul]
    exact Ideal.mul_mem_right _ _ hb₀mem
  -- the derivative at `ξ` sits in `(ξ) ^ (n - 1)`
  have hYmem : Polynomial.aeval ξ (Polynomial.derivative g) ∈ Ideal.span {ξ} ^ (n - 1) :=
    aeval_derivative_mem_pow hgmonic hn hcoeffmem
  -- extract the cofactor and take norms
  obtain ⟨w, hw⟩ : ∃ w : ↥(integers L'),
      Polynomial.aeval ξ (Polynomial.derivative g) = ξ ^ (n - 1) * w := by
    have := hYmem
    rwa [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at this
  have hWint : IsIntegral 𝒪[K] ((w : ↥L')) := w.2
  obtain ⟨W, hWeq⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_norm K (R := 𝒪[K]) hWint)
  -- the norm of the generator
  set pb : PowerBasis K ↥L' := IntermediateField.adjoin.powerBasis hint.tower_top with hpb
  have hnormgen : Algebra.norm K x' =
      (-1) ^ pb.dim * algebraMap 𝒪[K] K (g.coeff 0) := by
    have h1 := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    have h2 : pb.gen = x' := rfl
    rw [h2] at h1
    rw [h1, hminx', hminKx, Polynomial.coeff_map]
  -- assemble
  refine ⟨(-1) ^ (pb.dim * (n - 1)) * g.coeff 0 ^ (n - 1) * W, ?_, ?_⟩
  · -- value identification
    have hy : Polynomial.aeval x' (Polynomial.derivative (minpoly K x')) =
        x' ^ (n - 1) * (w : ↥L') := by
      rw [hminx', hminKx, Polynomial.derivative_map, Polynomial.aeval_map_algebraMap,
        ← hvalaev, hw]
      push_cast
      rw [show ((ξ : ↥(integers L')) : ↥L') = x' from hξval]
    rw [hy, map_mul (f := (Algebra.norm K : ↥L' →* K)), map_pow (f := (Algebra.norm K : ↥L' →* K)),
      hnormgen, ← hWeq]
    simp only [map_mul, map_pow, map_neg, map_one]
    ring
  · -- membership
    have h1 : g.coeff 0 ^ (n - 1) ∈ 𝓂[K] ^ (n - 1) := by
      rw [hπ.maximalIdeal_eq,
        show Ideal.span {π} = Ideal.span {g.coeff 0} from
          Ideal.span_singleton_eq_span_singleton.mpr hπg₀,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [mul_comm ((-1) ^ (pb.dim * (n - 1))) _, mul_assoc]
    exact Ideal.mul_mem_right _ _ h1

omit [IsUniformAddGroup K] in
/-- The discriminant ideal at an adjoined Eisenstein root—the equality behind the bound
`sub_one_le_d_adjoin`, and the input the change of variables consumes. `discIdeal` is *generated* by
the discriminant of the power basis: every generator of `discIdeal` is the discriminant of an
integral basis, whose transition matrix from the power basis is integral by monogenicity
(`integers_eq_adjoin`), so that discriminant is the squared determinant times the power-basis
discriminant—while the power basis is itself an integral basis and so contributes its own
discriminant. The generator is exhibited in the form `norm_derivative_core` produces, the
power-basis discriminant being plus or minus the norm of the derivative of `g` at `ξ`, which is what
makes it land in the `n - 1`-st power of `𝓂[K]`. -/
theorem discIdeal_eq_span {π : 𝒪[K]} (hπ : Irreducible π) {x : SeparableClosure K}
    (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π})) :
    ∃ N₀ : 𝒪[K], N₀ ≠ 0 ∧ N₀ ∈ 𝓂[K] ^ ((minpoly 𝒪[K] x).natDegree - 1) ∧
      algebraMap 𝒪[K] K N₀ =
        Algebra.norm K (Polynomial.aeval (IntermediateField.AdjoinSimple.gen K x)
          (Polynomial.derivative (minpoly K (IntermediateField.AdjoinSimple.gen K x)))) ∧
      discIdeal (IntermediateField.adjoin K {x}) = Ideal.span {N₀} := by
  classical
  have : IsFractionRing 𝒪[K] K :=
    inferInstanceAs (IsFractionRing (valuation K).valuationSubring K)
  have hKint : IsIntegral K x := hint.tower_top
  set L' := IntermediateField.adjoin K {x} with hL'
  set x' : ↥L' := IntermediateField.AdjoinSimple.gen K x with hx'
  set g : Polynomial 𝒪[K] := minpoly 𝒪[K] x with hg
  set n : ℕ := g.natDegree with hn'
  have hn : 0 < n := minpoly.natDegree_pos hint
  have hgmonic : g.Monic := minpoly.monic hint
  set pb : PowerBasis K ↥L' := IntermediateField.adjoin.powerBasis hKint with hpb
  have : Module.Finite K ↥L' := pb.finite
  have hminK : minpoly K x = g.map (algebraMap 𝒪[K] K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hint
  have hdim : pb.dim = n := by
    have h1 : pb.dim = (minpoly K x).natDegree := rfl
    rw [h1, hminK, (minpoly.monic hint).natDegree_map]
  have hfr : Module.finrank K ↥L' = n := by
    rw [pb.finrank, hdim]
  -- the reindexed power basis, on the index type of `discIdeal`
  set b₀ : Module.Basis (Fin (Module.finrank K ↥L')) K ↥L' :=
    pb.basis.reindex (finCongr (by rw [hdim, hfr])) with hb₀
  have hb₀int : ∀ i, IsIntegral 𝒪[K] (b₀ i) := by
    intro i
    rw [hb₀, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
    exact ((isIntegral_algebraMap_iff (B := SeparableClosure K)).mp hint).pow _
  -- the nonzero witness: the discriminant of the reindexed power basis
  have hd₀int : IsIntegral 𝒪[K] (Algebra.discr K ⇑b₀) := Algebra.discr_isIntegral K hb₀int
  obtain ⟨D, hD⟩ := IsIntegrallyClosed.isIntegral_iff.mp hd₀int
  have hDne : D ≠ 0 := by
    intro h0
    have hdiscne : Algebra.discr K ⇑b₀ ≠ 0 := Algebra.discr_not_zero_of_basis K b₀
    exact hdiscne (by rw [← hD, h0, map_zero])
  have hDmem : D ∈ discIdeal L' := Ideal.subset_span ⟨b₀, hb₀int, hD⟩
  have hb₀pow : ∀ i, b₀ i = x' ^ (i : ℕ) := by
    intro i
    rw [hb₀, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow]
    rfl
  -- the power-basis discriminant is a sign times the norm of `g' (ξ)`
  obtain ⟨N₀, hN₀val, hN₀mem⟩ := norm_derivative_core K hπ hint hei
  have hb₀disc : Algebra.discr K ⇑b₀ =
      (-1) ^ (Module.finrank K ↥L' * (Module.finrank K ↥L' - 1) / 2) *
        algebraMap 𝒪[K] K N₀ := by
    rw [hb₀, Module.Basis.coe_reindex, Algebra.discr_reindex,
      Algebra.discr_powerBasis_eq_norm, hN₀val]
    rfl
  -- every generator of `discIdeal` is a multiple of that norm
  have hle : discIdeal L' ≤ Ideal.span {N₀} := by
    rw [discIdeal, Ideal.span_le]
    rintro x₀ ⟨b, hbint, hbdisc⟩
    rw [SetLike.mem_coe]
    -- coordinates of the basis entries in the power basis
    have haevg : Polynomial.aeval x' g = 0 := by
      have h1 := minpoly.aeval K x'
      rw [show minpoly K x' = minpoly K x from
          (minpoly.algebraMap_eq (algebraMap ↥L' (SeparableClosure K)).injective x').symm,
        hminK, Polynomial.aeval_map_algebraMap] at h1
      exact h1
    have hcoords : ∀ j, ∃ R : Polynomial 𝒪[K],
        R.natDegree < Module.finrank K ↥L' ∧ Polynomial.aeval x' R = b j := by
      intro j
      have h1 : b j ∈ Algebra.adjoin 𝒪[K] {x'} :=
        (integers_eq_adjoin hπ hint hei).le (hbint j)
      have h2 : b j ∈ (Polynomial.aeval x' : Polynomial 𝒪[K] →ₐ[𝒪[K]] ↥L').range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval]
        exact h1
      obtain ⟨P, hP⟩ := (AlgHom.mem_range _).mp h2
      refine ⟨P %ₘ g, ?_, ?_⟩
      · rw [hfr]
        by_cases h0 : P %ₘ g = 0
        · rw [h0]
          simpa using hn
        · have h3 : (P %ₘ g).degree < g.degree := Polynomial.degree_modByMonic_lt P hgmonic
          exact Polynomial.natDegree_lt_natDegree h0 h3
      · have h4 := congrArg (Polynomial.aeval x') (Polynomial.modByMonic_add_div P g)
        rw [map_add, map_mul, haevg, zero_mul, add_zero] at h4
        rw [h4]
        exact hP
    choose R hRdeg hRval using hcoords
    set M : Matrix (Fin (Module.finrank K ↥L')) (Fin (Module.finrank K ↥L')) 𝒪[K] :=
      Matrix.of fun i j => (R j).coeff (i : ℕ) with hM
    have hbeq : ⇑b = Matrix.vecMul ⇑b₀ ((M.map (algebraMap 𝒪[K] K)).map (algebraMap K ↥L')) := by
      funext j
      change b j = ∑ i, b₀ i * ((M.map (algebraMap 𝒪[K] K)).map (algebraMap K ↥L')) i j
      rw [← hRval j, Polynomial.aeval_eq_sum_range' (hRdeg j),
        ← Fin.sum_univ_eq_sum_range fun k => (R j).coeff k • x' ^ k]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb₀pow i, Algebra.smul_def, mul_comm]
      simp only [Matrix.map_apply, Matrix.of_apply, hM]
      rw [← IsScalarTower.algebraMap_apply]
    have hdiscr : Algebra.discr K ⇑b =
        (M.map (algebraMap 𝒪[K] K)).det ^ 2 * Algebra.discr K ⇑b₀ := by
      rw [hbeq]
      exact Algebra.discr_of_matrix_vecMul (⇑b₀) (M.map (algebraMap 𝒪[K] K))
    have hfinal : algebraMap 𝒪[K] K x₀ = algebraMap 𝒪[K] K
        (((M.det) ^ 2 * (-1) ^ (Module.finrank K ↥L' * (Module.finrank K ↥L' - 1) / 2)) *
          N₀) := by
      rw [hbdisc, hdiscr, hb₀disc,
        show ((M.map (algebraMap 𝒪[K] K)).det) = algebraMap 𝒪[K] K M.det from
          (RingHom.map_det (algebraMap 𝒪[K] K) M).symm]
      simp only [map_mul, map_pow, map_neg, map_one]
      ring
    have hx₀eq : x₀ = ((M.det) ^ 2 *
        (-1) ^ (Module.finrank K ↥L' * (Module.finrank K ↥L' - 1) / 2)) * N₀ :=
      IsFractionRing.injective 𝒪[K] K hfinal
    rw [hx₀eq]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_left N₀ _)
  -- conversely, the power basis is itself an integral basis, so its discriminant is a member
  have hDN₀ : D =
      (-1) ^ (Module.finrank K ↥L' * (Module.finrank K ↥L' - 1) / 2) * N₀ := by
    refine IsFractionRing.injective 𝒪[K] K ?_
    rw [hD, hb₀disc]
    simp only [map_mul, map_pow, map_neg, map_one]
  have hspanD : Ideal.span ({D} : Set 𝒪[K]) = Ideal.span {N₀} := by
    rw [hDN₀]
    exact Ideal.span_singleton_mul_left_unit (isUnit_one.neg.pow _) N₀
  refine ⟨N₀, ?_, hN₀mem, hN₀val, le_antisymm hle ?_⟩
  · intro h0
    exact hDne (by rw [hDN₀, h0, mul_zero])
  · rw [← hspanD, Ideal.span_le, Set.singleton_subset_iff]
    exact hDmem

omit [IsUniformAddGroup K] in
/-- The discriminant bound at an adjoined Eisenstein root. `discIdeal` is generated by the
power-basis discriminant (`discIdeal_eq_span`), which lands in the `n - 1`-st power of `𝓂[K]`;
finiteness of the multiplicity comes from its being nonzero. -/
theorem sub_one_le_d_adjoin {π : 𝒪[K]} (hπ : Irreducible π) {x : SeparableClosure K}
    (hint : IsIntegral 𝒪[K] x)
    (hei : (minpoly 𝒪[K] x).IsEisensteinAt (Submodule.span 𝒪[K] {π})) :
    (minpoly 𝒪[K] x).natDegree - 1 ≤ d (IntermediateField.adjoin K {x}) := by
  obtain ⟨N₀, hN₀ne, hN₀mem, -, hspan⟩ := discIdeal_eq_span K hπ hint hei
  set L' := IntermediateField.adjoin K {x} with hL'
  set n : ℕ := (minpoly 𝒪[K] x).natDegree with hn'
  have hle : discIdeal L' ≤ 𝓂[K] ^ (n - 1) := by
    rw [hspan, Ideal.span_le, Set.singleton_subset_iff]
    exact hN₀mem
  -- finite multiplicity, from the nonzero generator
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hN₀ne hπ
  obtain ⟨v, hv⟩ := hm.symm
  have hfin : FiniteMultiplicity 𝓂[K] (discIdeal L') := by
    refine ⟨m, fun hcon => ?_⟩
    have h1 : N₀ ∈ 𝓂[K] ^ (m + 1) := Ideal.dvd_iff_le.mp hcon
      (by rw [hspan]; exact Ideal.mem_span_singleton_self N₀)
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
    rw [← hv, pow_succ] at h1
    have h2 : π ∣ (v : 𝒪[K]) :=
      (mul_dvd_mul_iff_left (pow_ne_zero m hπ.ne_zero)).mp h1
    exact hπ.not_isUnit (isUnit_of_dvd_unit h2 v.isUnit)
  -- conclude through `emultiplicity`
  change n - 1 ≤ multiplicity 𝓂[K] (discIdeal L')
  exact hfin.le_multiplicity_of_le_emultiplicity
    (le_emultiplicity_of_pow_dvd (Ideal.dvd_iff_le.mpr hle))

omit [IsUniformAddGroup K] in
/-- `d L` as a `π`-adic order, the form the change of variables consumes: the discriminant of the
power basis at an Eisenstein generator is an associate of `π ^ d L`. `discIdeal` being the span of
that discriminant, the multiplicity of `𝓂[K]` in it is exactly the order of the generator. -/
theorem associated_pow_d {π : 𝒪[K]} (hπ : Irreducible π) {x : SeparableClosure K}
    {N₀ : 𝒪[K]} (hN₀ne : N₀ ≠ 0)
    (hspan : discIdeal (IntermediateField.adjoin K {x}) = Ideal.span {N₀}) :
    Associated N₀ (π ^ d (IntermediateField.adjoin K {x})) := by
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hN₀ne hπ
  obtain ⟨v, hv⟩ := hm.symm
  have hmem_iff : ∀ k : ℕ, 𝓂[K] ^ k ∣ Ideal.span ({N₀} : Set 𝒪[K]) ↔ π ^ k ∣ N₀ := by
    intro k
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff, hπ.maximalIdeal_eq,
      Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton]
  have hd : d (IntermediateField.adjoin K {x}) = m := by
    change multiplicity 𝓂[K] (discIdeal (IntermediateField.adjoin K {x})) = m
    rw [hspan]
    refine multiplicity_eq_of_dvd_of_not_dvd ((hmem_iff m).mpr hm.symm.dvd) ?_
    rw [hmem_iff, ← hv, pow_succ]
    intro hdvd
    exact hπ.not_isUnit (isUnit_of_dvd_unit
      ((mul_dvd_mul_iff_left (pow_ne_zero m hπ.ne_zero)).mp hdvd) v.isUnit)
  rw [hd]
  exact hm

omit [IsUniformAddGroup K] in
/-- The discriminant exponent of a totally ramified degree-`n` extension is at least `n - 1`. -/
theorem sub_one_le_d (n : ℕ) (hn : 0 < n) (L : IntermediateField K (SeparableClosure K))
    (hL : L ∈ sigma K n) : n - 1 ≤ d L := by
  obtain ⟨x, π, hπ, hint, hei, hLeq, hdeg⟩ := exists_eisenstein_generator K n hn L hL
  rw [← hLeq, ← hdeg]
  exact sub_one_le_d_adjoin K hπ hint hei

end MassFormula
