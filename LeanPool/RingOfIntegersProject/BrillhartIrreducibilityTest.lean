/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import LeanPool.RingOfIntegersProject.IrreduciblePolynomialZModp
import LeanPool.RingOfIntegersProject.PolynomialsAsLists
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Cardinality
import Mathlib.Data.List.Indexes
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!

# Prime witness irreducibility certificate.

We formalize the large prime witness certificate for irreducibility,
which incorporates information on a degree
bound given by reductions modulo primes.

## Main definitions:
- `cauchyBoundScaled` : the classic Cauchy bound for the roots of a polynomial
is not invariant under scalings. This is a scaled
version for a real number r > 0.
- `cauchyBoundScaledOfList` : A computable version of the scaled Cauchy bound for
polynomials over the integers given as lists.

## Main results:
- `irreducible_of_eval_mul_prime` : if a big enough `m` is found such that `|f(m)| = s * P` with
`P` a prime and `s` smaller than certain bound depending on a degree bound, then `f` is prime.
-`polynomial_roots_le_cauchy_bound_scale` : the roots of a complex polynomial are bounded by
  the scaled Cauchy bound.

## Certificates:
- `CertificateIrreducibleIntOfPrimeDegreeAnalysis` : the LPFW certificate, including degree analysis
  from factorizations of `f` modulo primes.
- `CertificateIrreducibleIntOfPrime` : LPFW certificate, with no factorization information.
  Taking d = 1 as default degree bound.

## Reference:
 Abbott J. Certifying Irreducibility in ℤ[X].
 https://doi.org/10.1007/978-3-030-52200-1_46

 The certificate can be seen as a refinement of Brillhart's certificate.

-/


open Polynomial Complex

section AuxiliaryLemmas

lemma List.pow_le_prod {R : Type*} [StrictOrderedSemiring R] (l : List R) (d : R)
    (hd : 0 ≤ d) (h : ∀ a ∈ l, d ≤ a) (hneq : l ≠ List.nil) : d ^ l.length ≤ l.prod := by
  induction l
  case _  =>
    contradiction
  case _ a  l' l_ih =>
    rw [List.prod_cons]
    have h' :=  h a
    simp only [List.find?, List.mem_cons, true_or, forall_true_left] at h'
    by_cases hk :  l' = List.nil
    rw [hk]
    simp only [List.prod_nil, mul_one, length_singleton, pow_one, gt_iff_lt]
    exact h'
    have := l_ih (λ a ha => h a (List.mem_cons_of_mem _ ha) ) hk
    simp only [length_cons, Nat.succ_eq_add_one, gt_iff_lt]
    rw [add_comm, pow_add, pow_one]
    refine mul_le_mul h' (this) ?_ ?_
    exact pow_nonneg hd l'.length
    exact Preorder.le_trans 0 d a hd h'

lemma List.map_maximum {α β: Type*} [LinearOrder α] [LinearOrder β] {l : List α}
    (f : α → β) (hf : Monotone f) : WithBot.map f (l.maximum ) = (l.map f).maximum := by
  induction' l with a as ha
  · simp only [maximum_nil, WithBot.map_bot, map_nil]
  · rw [← WithBot.monotone_map_iff] at hf
    rw [List.maximum_cons, map_cons, List.maximum_cons, Monotone.map_max hf, ha, WithBot.map_coe]

  end AuxiliaryLemmas

lemma pow_lt_abs_eval {R K : Type*} [CommRing R] [Field K] (m : R) (i : R →+* K)
    (ρ : ℝ) (d : ℕ) (hd : d ≠ 0) (abs : AbsoluteValue K ℝ) (p : Polynomial R)
    (hsplit : Polynomial.Splits i p ) (hdeg : (p.map i).natDegree = d )
    (hcoeff : 1 ≤  abs ((p.map i).leadingCoeff ))
    (hroots : ∀ x ∈ Polynomial.roots (p.map i), (abs x) ≤ ρ )
    (h : ρ ≤ abs (i m) ) : (abs (i m) - ρ) ^ d ≤ abs (i (p.eval m)) := by
  rw [← Polynomial.eval₂_hom , ← Polynomial.eval_map
    ,Polynomial.eq_prod_roots_of_splits_id ((Polynomial.splits_id_iff_splits i).2 hsplit) ]
  simp only [algebraMap.coe_one, eval_mul, eval_C, AbsoluteValue.map_mul]
  rw [Polynomial.eval_multiset_prod]
  simp only [Multiset.map_map, Function.comp_apply, eval_sub, eval_X, eval_C]
  rw [← one_mul ((abs (i m) - ρ) ^ d )]
  have leaux : 0 ≤ abs (i m) - ρ  := by linarith
  apply mul_le_mul hcoeff _
  · exact pow_nonneg leaux d
  · exact AbsoluteValue.nonneg abs (map i p).leadingCoeff
  have aux : d =
    (List.map (⇑abs) (Multiset.map (fun x => i m - x) (map i p).roots).toList).length := by
      simp only [List.length_map, Multiset.length_toList, Multiset.card_map]
      rw [← hdeg, Polynomial.natDegree_eq_card_roots
        (p := (p.map i)) ((Polynomial.splits_id_iff_splits i).2 hsplit), map_id]
  · simp_rw [← Multiset.prod_toList, map_list_prod]
    rw [aux]
    apply List.pow_le_prod
    · exact leaux
    · intro a ha
      simp only [List.mem_map, Multiset.mem_toList, Multiset.mem_map] at ha
      choose ar har habs using ha
      obtain ⟨r, hr, hsub⟩ := har
      rw [← hsub] at habs ; clear hsub
      have := hroots r hr
      have := (AbsoluteValue.le_sub abs (i m) r)
      rw [← habs]
      linarith
    · apply List.ne_nil_of_length_pos
      rw [← aux]
      exact Nat.zero_lt_of_ne_zero hd

lemma ne_mul_prime (s p : ℕ) (hp : Nat.Prime p) (q r : ℤ)
    (hq : s < |q|) (hr : s < |r| ) :
    ¬ |q * r| = s * p := by
  by_contra hc
  rw [← Int.natCast_natAbs, Int.natAbs_mul, ← Nat.cast_mul, Nat.cast_inj] at hc
  rw [← Int.natCast_natAbs, Nat.cast_lt] at hr hq
  wlog hdvd : p ∣ q.natAbs
  · have aux := (Nat.Prime.dvd_mul hp).1 (Dvd.intro_left _ hc.symm)
    simp only [hdvd, false_or] at aux
    rw [mul_comm] at hc
    exact this s p hp r q hr hq hc aux
  · obtain ⟨t, ht⟩ := hdvd
    rw [ht, mul_assoc, mul_comm] at hc
    simp only [mul_eq_mul_right_iff, Nat.Prime.ne_zero hp, or_false] at hc
    have htz : t ≠ 0 := by
      by_contra hct
      rw [hct, mul_zero] at ht
      rw [ht] at hq
      simp only [not_lt_zero'] at hq
    have := Nat.mul_lt_mul_of_pos_left hr (show (t > 0) by exact Nat.zero_lt_of_ne_zero htz)
    rw [hc, ← not_le] at this
    have aux := Nat.mul_le_mul_left s (show (1 ≤ t) by exact Nat.one_le_iff_ne_zero.mpr htz)
    rw [mul_one, mul_comm] at aux
    exact this aux

/-- An irreducibility result by J. Abbot, which is a refinement of Brillhart's irreducibility
test as it incorporates information on the degree of the factors.  -/
lemma irreducible_of_eval_mul_prime (m : ℤ) (ρ : ℝ) (d p s : ℕ) (hdn : d ≠ 0)
    (hprime : Nat.Prime p)
    (P : Polynomial ℤ) (hdeg : P.natDegree ≠ 0)
    (h : ∀ x ∈ Polynomial.roots (P.map (algebraMap ℤ ℂ)),  Complex.abs x ≤ ρ)
    (hd : ∀ q : ℤ[X], ¬ IsUnit q → q ∣ P → d ≤ q.natDegree)
    (hrho : ρ + 1 ≤ |m| ) (hs : s < (|m| - ρ) ^ d )
    (heval : |P.eval m|  =  s * p) : Irreducible P := by
  have mabs : ↑|m| = Complex.abs m := by simp only [Int.cast_abs, abs_intCast]
  rw [mabs] at hrho
  have hfnez : P ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (zero_lt_iff.2 hdeg)
  have hfanez' :  Polynomial.map (algebraMap ℤ ℂ) P ≠ 0 := by
    rw [Polynomial.map_ne_zero_iff]
    exact hfnez
    exact (algebraMap ℤ ℂ).injective_int
  have dvdaux : ∀ a , ¬ IsUnit a → a ∣ P → (|m| - ρ) ^ d ≤ |a.eval m| := by
    intro a hau hadvd
    have hanez :  a ≠ 0 := ne_zero_of_dvd_ne_zero hfnez hadvd
    have ha1: ∀ x ∈  (Polynomial.map (algebraMap ℤ ℂ) a).roots , Complex.abs x ≤ ρ := by
      intros x hx
      apply h x
      exact Multiset.subset_of_le (Polynomial.roots.le_of_dvd hfanez' (Polynomial.map_dvd _ hadvd )) hx
    have hadeg := hd a hau hadvd
    have hla : 1 ≤ Complex.abs (map (algebraMap ℤ ℂ) a).leadingCoeff := by
      have hazc : a.leadingCoeff ≠ 0 := by
        simp only [ne_eq, leadingCoeff_eq_zero, hanez, not_false_eq_true]
      rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ ?_]
      swap
      simp only [algebraMap_int_eq, eq_intCast, ne_eq, Int.cast_eq_zero, hazc, not_false_eq_true]
      simp only [algebraMap_int_eq, eq_intCast, abs_intCast, ge_iff_le, Eq.symm Int.cast_abs]
      rw [← Int.cast_one, Int.cast_le]
      apply Int.one_le_abs
      exact hazc
    have hrhoaux : ρ ≤ Complex.abs ((algebraMap ℤ ℂ) m) := by
      simp only [algebraMap_int_eq, eq_intCast]
      linarith
    have hadn : a.natDegree ≠ 0 :=  fun hca => by (rw [hca, Nat.le_zero] at hadeg ; exact hdn hadeg)
    convert le_trans (pow_le_pow_right₀ ?_ hadeg) (pow_lt_abs_eval m (algebraMap ℤ ℂ)
      ρ (a.natDegree) hadn (Complex.abs) a ?_ (Polynomial.natDegree_map_eq_of_injective
    (RingHom.injective_int (algebraMap ℤ ℂ)) _ ) hla ha1 hrhoaux)
    · simp only [Int.cast_abs, algebraMap_int_eq, eq_intCast, abs_intCast]
    · exact le_tsub_of_add_le_left hrho
    · rw [← Polynomial.splits_id_iff_splits]
      exact IsAlgClosed.splits (k := ℂ ) _
  rw [irreducible_iff]
  constructor
  · by_contra hu
    exact hdeg (Polynomial.natDegree_eq_zero_of_isUnit hu)
  · intros a b hab
    by_contra hcab
    push_neg at hcab
    apply ne_mul_prime s p hprime (eval m a) (eval m b)
    · rw [← Int.cast_lt (R := ℝ)]
      exact lt_of_lt_of_le hs (dvdaux a hcab.1 (Dvd.intro _ hab.symm))
    · rw [← Int.cast_lt (R := ℝ)]
      exact lt_of_lt_of_le hs (dvdaux b hcab.2 (Dvd.intro_left _ hab.symm))
    · rw [← heval, hab, eval_mul]

open BigOperators

/-- Given the polynomial `a₀ + a₁ * X + … + aₙ * X ^ n`, this returns `max {|a₀|,…,|aₙ₋₁|}`.
 For constant polynomials, it returns `0`.  -/
noncomputable def maxCoeffsAux (P : Polynomial ℂ) : ℝ :=
  let f : Fin (P.natDegree) → ℝ := fun n => Complex.abs (P.coeff n)
  (if h : P.natDegree = 0 then 0 else WithBot.unbot (List.maximum (List.ofFn f))
  (List.maximum_ne_bot_of_ne_nil (by simp only [map_div₀, ne_eq, List.ofFn_eq_nil_iff,
    h, not_false_eq_true, f] )))

lemma maxCoeffsAux_nonneg (P : Polynomial ℂ) : 0 ≤ maxCoeffsAux P := by
  unfold maxCoeffsAux
  by_cases h : P.natDegree = 0
  · simp only [h, ↓reduceDIte, le_refl]
  · haveI : NeZero (P.natDegree) := { out := h }
    simp only [h, ↓reduceDIte]
    rw [WithBot.le_unbot_iff, List.coe_le_maximum_iff]
    use (Complex.abs (P.coeff ↑0))
    simp only [apply_nonneg, and_true, List.mem_ofFn]
    use 0
    simp only [Fin.val_zero']

lemma coeffs_le_maxCoeffAux (P : Polynomial ℂ ) (n : ℕ) (hn : n < P.natDegree) (h : P.natDegree ≠ 0 ) :
    Complex.abs (P.coeff n) ≤ maxCoeffsAux P := by
  unfold maxCoeffsAux
  simp[h]
  refine List.le_maximum_of_mem
    (l := List.ofFn (fun n => Complex.abs (P.coeff ↑n) : Fin (P.natDegree) → ℝ)) ?_ ?_
  · rw [(show n = ↑(⟨n, hn⟩ : Fin (P.natDegree)) by rfl), List.mem_ofFn]
    use ⟨n, hn⟩
  · simp only [WithBot.coe_unbot]


/-- The standard Cauchy Bound for the roots of a complex polynomial. For constant polynomials
it returns the dummy value 1. Note that this bound is sensitive to scaling· -/
noncomputable def cauchyBound (P : Polynomial ℂ ) : ℝ := 1 + (maxCoeffsAux P) / abs (P.leadingCoeff)

/-- The roots of a non-constant complex polynomial are bounded by the Cauchy bound. -/
lemma polynomial_roots_le_cauchy_bound (P : Polynomial ℂ ) (z : ℂ)
    (hd : P.natDegree ≠ 0 ) (hr : z ∈ P.roots)  :
    Complex.abs z ≤ cauchyBound P := by
  have h : P ≠ 0 := Ne.symm (ne_of_apply_ne (fun P => P.natDegree) fun a => hd (id (Eq.symm a)))
  have heq : P.leadingCoeff * z ^ P.natDegree = - (P.eraseLead).eval z := by
    rw [← Polynomial.self_sub_C_mul_X_pow]
    simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
    rw [Polynomial.mem_roots_iff_aeval_eq_zero h, coe_aeval_eq_eval] at hr
    rw [hr, zero_sub, neg_neg]
  have aux1 : abs (- (P.eraseLead).eval z) ≤
    ∑ i ∈ Finset.range (P.natDegree), (abs (P.coeff i)) * (abs z) ^ i := by
    rw [map_neg_eq_map, Polynomial.eval_eq_sum_range]
    refine le_trans (AbsoluteValue.sum_le Complex.abs _ _) ?_
    by_cases he : P.eraseLead = 0
    · rw [he]
      simp only [natDegree_zero, zero_add, Finset.range_one, coeff_zero, zero_mul, map_zero,
        Finset.sum_const_zero]
      refine Finset.sum_nonneg ?_
      intro i _
      rw [← map_pow, ← map_mul]
      exact AbsoluteValue.nonneg _ _
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (s := Finset.range (P.eraseLead.natDegree + 1))
      (t := Finset.range P.natDegree) ?_ ?_ ) ?_
    · have aux := Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero P
      simp only [he, or_false] at aux
      simp only [Finset.range_subset]
      exact aux
    · intro i _ _
      exact AbsoluteValue.nonneg _ _
    · apply Finset.sum_le_sum
      intro i hi
      simp only [eraseLead_coeff, ne_of_lt (Finset.mem_range.1 hi), ↓reduceIte, map_mul, map_pow,
        le_refl]
  by_cases habs : 0 ≤ abs z - 1
  · have aux2 : (∑ i ∈ Finset.range (P.natDegree), (abs (P.coeff i)) * (abs z) ^ i) * (abs z - 1)
      ≤ (maxCoeffsAux P) * ((abs z) ^ P.natDegree - 1) := by
      have aux3 : ∑ i ∈ Finset.range (P.natDegree), (abs (P.coeff i)) * (abs z) ^ i
        ≤ (maxCoeffsAux P) * ∑ i ∈ Finset.range (P.natDegree), (abs z) ^ i := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        refine mul_le_mul_of_nonneg_right ?_ (by rw [← map_pow] ; exact AbsoluteValue.nonneg _ _ )
        exact coeffs_le_maxCoeffAux P _ (Finset.mem_range.1 hi) hd
      refine le_of_le_of_eq (mul_le_mul_of_nonneg_right aux3 habs) ?_
      rw [← geom_sum_mul _ _, mul_assoc]
    unfold cauchyBound
    rw [← sub_le_iff_le_add',
      le_div_iff₀ (AbsoluteValue.pos Complex.abs (Polynomial.leadingCoeff_ne_zero.2 h)),
      ←  mul_le_mul_iff_of_pos_right (a := (Complex.abs z ^ P.natDegree))]
    refine le_trans ?_ (le_trans aux2 (mul_le_mul_of_nonneg_left (le_of_lt (sub_one_lt _))
      (maxCoeffsAux_nonneg P)))
    rw [mul_assoc, ← map_pow, ← map_mul, heq, mul_comm]
    exact mul_le_mul_of_nonneg_right aux1 habs
    refine pow_pos (by linarith) _
  · push_neg at habs
    unfold cauchyBound
    have : 0 ≤ maxCoeffsAux P / Complex.abs P.leadingCoeff :=
      div_nonneg (maxCoeffsAux_nonneg P) (AbsoluteValue.nonneg _ _)
    linarith

noncomputable def maxCoeffsAuxScale (P : Polynomial ℂ) (r : ℝ) : ℝ :=
  let f : Fin (P.natDegree) → ℝ := fun n => Complex.abs (P.coeff n) * (1 / ↑r ^ (P.natDegree - n.val))
  (if h : P.natDegree = 0 then 0 else WithBot.unbot (List.maximum (List.ofFn f))
  (List.maximum_ne_bot_of_ne_nil (by simp only [map_div₀, ne_eq, List.ofFn_eq_nil_iff,
    h, not_false_eq_true, f] )))

/-- A scaled version of the Cauchy bound obtained by computing the Cauchy bound for `P(r * X)`
  and dividing by `r`. After choosing an appropiate `r > 0 `, this is usually smaller
  than the standard Cauchy bound. -/
noncomputable def cauchyBoundScaled (P : Polynomial ℂ) (r : ℝ) : ℝ :=
  r * (1 + (maxCoeffsAuxScale P r) / abs (P.leadingCoeff))

/-- The roots of a non-constant complex polynomial are bounded by
  the scaled Cauchy bound. -/
lemma polynomial_roots_le_cauchy_bound_scale (P : Polynomial ℂ) (z : ℂ)
    (hd : P.natDegree ≠ 0) (hr : z ∈ P.roots) (r : ℝ) (hs : 0 < r) :
    Complex.abs z ≤ cauchyBoundScaled P r := by
  have h : P ≠ 0 := Ne.symm (ne_of_apply_ne (fun P => P.natDegree) fun a => hd (id (Eq.symm a)))
  refine le_of_mul_le_mul_of_pos_left (a := r⁻¹) ?_ (inv_pos_of_pos hs)
  have : r⁻¹ * Complex.abs z = Complex.abs (r⁻¹ * z) := by
    rw [ofReal_inv, map_mul, map_inv₀, abs_ofReal, abs_of_nonneg (a := r) (le_of_lt hs)]
  rw [this, cauchyBoundScaled, ← mul_assoc, inv_mul_cancel₀ (Ne.symm (ne_of_lt hs)), one_mul]
  have hroots : r⁻¹ * z ∈ (P.scaleRoots r⁻¹).roots := by
    simp only [ofReal_inv, mem_roots', ne_eq, IsRoot.def]
    refine ⟨Polynomial.scaleRoots_ne_zero h r⁻¹ , ?_ ⟩
    rw [Polynomial.mem_roots_iff_aeval_eq_zero h] at hr
    refine Polynomial.scaleRoots_aeval_eq_zero hr
  convert polynomial_roots_le_cauchy_bound (P.scaleRoots r⁻¹) (r⁻¹ * z)
    (by rw [Polynomial.natDegree_scaleRoots] ; exact hd) hroots
  unfold cauchyBound Polynomial.leadingCoeff
  rw [Polynomial.natDegree_scaleRoots, Polynomial.coeff_scaleRoots_natDegree]
  congr
  unfold maxCoeffsAuxScale maxCoeffsAux
  simp only [hd, ↓reduceDIte, one_div, natDegree_scaleRoots, Fin.coe_cast, coeff_scaleRoots,
    inv_pow, map_mul, map_inv₀, map_pow, abs_ofReal]
  congr
  rw [abs_of_nonneg (a := r) (le_of_lt hs)]

/- # DEFINITIONS FOR COMPUTATION

We define computable versions of the previous functions that work on lists over the integers. -/

def maxCoeffsAuxScaleOfList (l : List ℤ) (r : ℚ) :=
  if h : l.length - 1 = 0 then 0 else
  WithBot.unbot (List.maximum ((List.dropLast l).mapIdx
  (fun n c => |(algebraMap ℤ ℚ c)| * (1 / ↑r ^ ((l.length - 1) - n)) )))
  (List.maximum_ne_bot_of_ne_nil (by
    rw [ne_eq, List.mapIdx_eq_nil_iff, ← ne_eq, ← List.length_pos , List.length_dropLast]
    exact (Nat.pos_of_ne_zero h) ))

lemma maxCoeffsAuxScale_ofList (l : List ℤ) (hl : l = l.dropTrailingZeros) (r : ℚ) :
    maxCoeffsAuxScale ((ofList l).map (algebraMap ℤ ℂ)) r = maxCoeffsAuxScaleOfList l r := by
  by_cases hz : l = []
  · rw [hz]
    simp only [maxCoeffsAuxScale, algebraMap_int_eq, ofList_nil, Polynomial.map_zero,
      natDegree_zero, ↓reduceDIte, maxCoeffsAuxScaleOfList, List.length_nil, ge_iff_le, zero_le,
      tsub_eq_zero_of_le, Rat.cast_zero]
  · by_cases hlen : l.length - 1 = 0
    · have hlenc := hlen
      rw [← (natDegree_ofList _ hz hl), add_tsub_cancel_right,
      ← Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℂ))] at hlen
      simp only [maxCoeffsAuxScale, hlen, ↓reduceDIte, maxCoeffsAuxScaleOfList, hlenc,
        Rat.cast_zero]
    · have hlenc := hlen
      rw [← (natDegree_ofList _ hz hl), add_tsub_cancel_right,
      ← Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℂ))] at hlen
      simp only [maxCoeffsAuxScale, hlen, ↓reduceDIte, coeff_map, eq_intCast, abs_intCast, one_div,
        maxCoeffsAuxScaleOfList, hlenc]
      rw [← WithBot.coe_inj, ← WithBot.map_coe, WithBot.coe_unbot, WithBot.coe_unbot,
        List.map_maximum _ (Rat.cast_mono)]
      congr
      rw [List.mapIdx_eq_ofFn, List.map_ofFn]
      have heq : (map (algebraMap ℤ ℂ) (ofList l)).natDegree  = (l.dropLast).length := by
        rw [List.length_dropLast,
        Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℂ)),
           ← (natDegree_ofList _ hz hl)]
        rfl
      symm
      refine List.ofFn_inj'.mpr (Fin.sigma_eq_iff_eq_comp_cast.mpr ?_)
      use heq.symm
      ext i
      dsimp at i
      simp only [List.get_eq_getElem, List.getElem_dropLast, Function.comp_apply, Rat.cast_mul,
        Rat.cast_abs, Rat.cast_intCast, Rat.cast_inv, Rat.cast_pow, algebraMap_int_eq, ofList_map,
        Int.coe_castRingHom, Fin.coe_cast]
      simp_rw [ ← (natDegree_ofList _ hz hl), add_tsub_cancel_right,
      ← Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℂ)),
         ofList_map _ _ ]
      congr
      exact (ofList_coeff (R := ℤ) _ _ _).symm

/-- A computable version of the scaled Cauchy bound of a polynomial given by a list. -/
def cauchyBoundScaledOfList (l : List ℤ) (r : ℚ) : ℚ :=
  if h : l = [] then r else
   r * (1 + (maxCoeffsAuxScaleOfList l r) / |l.getLast h|)

/-- For `l` a list over the integers, the roots of `ofList l` are bounded by the scaled Cauchy
bound for lists. -/
lemma ofList_roots_le_cauchy_bound_scale (l : List ℤ)
    (hl : l = l.dropTrailingZeros)(hdeg : 1 < l.length) (z : ℂ)
    (hr : z ∈ ((ofList l).map (algebraMap ℤ ℂ)).roots) (r : ℚ) (hs : 0 < r) :
    Complex.abs z ≤ cauchyBoundScaledOfList l r := by
  have : l ≠ [] := List.ne_nil_of_length_pos (lt_trans (zero_lt_one) hdeg)
  simp only [cauchyBoundScaledOfList, this, ↓reduceDIte, Int.cast_abs, Rat.cast_mul, Rat.cast_add,
    Rat.cast_one, Rat.cast_div, Rat.cast_abs, Rat.cast_intCast, ge_iff_le]
  rw [← maxCoeffsAuxScale_ofList l hl, ← (ofList_leadingCoeff _ this hl)]
  convert polynomial_roots_le_cauchy_bound_scale ((ofList l).map (algebraMap ℤ ℂ)) z ?_ hr r
    (Rat.cast_pos.mpr hs) using 1
  unfold cauchyBoundScaled
  congr
  rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero, algebraMap_int_eq,
    eq_intCast, abs_intCast]
  simp only [algebraMap_int_eq, eq_intCast, ne_eq, Int.cast_eq_zero, leadingCoeff_eq_zero]
  by_contra hc
  exact this (nil_of_ofList_eq_zero l hl hc)
  rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℂ))]
  rw [← natDegree_ofList l this hl] at hdeg
  linarith


/- # CERTIFICATES BASED ON PRIME WITNESS -/

/-- A certificiate for the irreducibility of `T` based on `irreducible_of_eval_mul_prime`.
If `d` is a known lower bound for the degrees of the factors of `T`, `ρ` is a
root bound, and there is a big enough `M` such that `|f(M)| = s * P` with `P` prime
and `s < (|M| - ρ) ^ d` then `T` is irreducible.

- `n` is the number of primes to consider for the reductions
- `d` is the degree bound inferred from the reduction factorizations.
- `M` is the value such that `|f(M)| = s * P`
- `P` is the prime witness.
- `r` is the scaling factor used for the Cauchy bound.
- `ρ` is the value of the Cauchy bound.
- `p` is the tuple of primes to consider for reduction.
- `m` gives the number of irreducible factors in each of the reductions.
- `D` gives the degree of such irreducible factors.
- `F` gives the irreducible factors as lists.

To get a proof of the irreducibility of `F i j` one can use `CertificateIrreducibleZModOfList'`  -/

structure CertificateIrreducibleIntOfPrimeDegreeAnalysis (f : Polynomial ℤ) (l : List ℤ) where
  hpol : f = ofList l
  hdeg : 1 < l.length
  hprim : List.foldr gcd 0 l = 1
  n : ℕ
  d : ℕ
  s : ℕ
  P : ℕ
  M : ℤ
  r : ℚ
  ρ : ℚ
  hPPrime : Nat.Prime P
  hrpos : 0 < r
  hnn : n ≠ 0
  hdn : d ≠ 0
  p : Fin n → ℕ
  hp : ∀ i , Nat.Prime (p i)
  hlc : ∀ i, algebraMap ℤ (ZMod (p i)) (l.getLast (List.ne_nil_of_length_pos (pos_of_gt hdeg))) ≠ 0
  m : Fin n → ℕ
  F : ∀ i , Fin (m i) → List (ZMod (p i))
  D : ∀ i , Fin (m i) → ℕ
  hl : ∀ i j, (F i j).length = D i j + 1
  hirr : ∀ i j , Irreducible (ofList (F i j))
  hm : ∀ i j, (F i j).getLast (List.ne_nil_of_length_pos (lt_of_lt_of_eq (Nat.succ_pos (D i j)) (hl i j).symm) ) ≠ 0
  hprod : ∀ i, (List.prod (List.ofFn (fun j => F i j))).dropTrailingZeros' = List.map (algebraMap ℤ (ZMod (p i))) l
  hinter : ((List.bagInterOfFn (fun i => partialSums (List.ofFn (D i)))).filter (fun a => a ≠ 0)).min? = some d
  hrhoeq : cauchyBoundScaledOfList l r = ρ
  hrho : ρ + 1 ≤ |M|
  hs : s < (|M| - ρ) ^ d
  heval : |f.eval M| = s * P


lemma irreducible_of_CertificateIrreducibleIntOfPrimeDegrees (f : Polynomial ℤ) (l : List ℤ)
 (C : CertificateIrreducibleIntOfPrimeDegreeAnalysis f l) : Irreducible f := by
  rw [C.hpol]
  haveI : ∀ i , Fact $ Nat.Prime (C.p i) := by
    intro i
    exact fact_iff.2 (C.hp i)
  haveI : NeZero (C.n) := neZero_iff.2 C.hnn
  have hlnnil : l ≠ 0 := List.ne_nil_of_length_pos (lt_trans (zero_lt_one) (C.hdeg))
  have hldrop : l = l.dropTrailingZeros := by
    rw [eq_dropTrailingZeros_iff_last_entry_ne_zero _ hlnnil]
    have := C.hlc 0
    by_contra hc
    rw [hc] at this
    simp only [algebraMap_int_eq, map_zero, ne_eq, not_true_eq_false] at this
  refine irreducible_of_eval_mul_prime C.M (C.ρ : ℝ) C.d C.P C.s C.hdn C.hPPrime _ ?_ ?_
    (le_natDegree_of_partialSums _ C.d ?_ C.n C.p (fun i => List.ofFn (C.D i)) ?_ ?_ ?_ ) ?_ ?_ ?_
  · have hcd := C.hdeg
    by_contra hc
    rw [← natDegree_ofList _ hlnnil hldrop, hc] at hcd
    contradiction
  · intro z hz
    rw [← C.hrhoeq]
    refine ofList_roots_le_cauchy_bound_scale l hldrop C.hdeg z hz C.r C.hrpos
  · exact ofList_isPrimitive 1 l C.hprim (isUnit_one)
  · rw [ofList_leadingCoeff l hlnnil hldrop]
    exact C.hlc
  · intro i
    convert natDegree_list_factors_of_lists (List.map (algebraMap ℤ (ZMod (C.p i))) l)
      _ (C.F i) (C.D i) (C.hl i) (C.hirr i) (C.hm i) (C.hprod i)
    exact ofList_map _ _
  · exact C.hinter
  · convert (Rat.cast_le (K := ℝ)).2 C.hrho
    norm_num
  · convert (Rat.cast_lt (K := ℝ)).2 C.hs
    norm_num
  · rw [← C.hpol]
    exact C.heval

/-- Similar to `CertificateIrreducibleIntOfPrimeDegreeAnalysis`, but without degree analysis information
 and taking `d = 1` as a known degree bound. This is convenient when knowing a bigger bound doesn't
 result in finding a smaller prime witness, so degree analysis
 doesn't provide an advantage.  -/
structure CertificateIrreducibleIntOfPrime (f : Polynomial ℤ) (l : List ℤ) where
  hpol : f = ofList l
  hdeg : 1 < l.length
  hprim : List.foldr gcd 0 l = 1
  hlz : l.getLast (List.ne_nil_of_length_pos (pos_of_gt hdeg)) ≠ 0
  s : ℕ
  P : ℕ
  M : ℤ
  r : ℚ
  ρ : ℚ
  hPPrime : Nat.Prime P
  hrpos : 0 < r
  hrhoeq : cauchyBoundScaledOfList l r = ρ
  hrho : ρ + 1 ≤ |M|
  hs : s < (|M| - ρ)
  heval : |f.eval M| = s * P


lemma irreducible_of_CertificateIrreducibleIntOfPrime (f : Polynomial ℤ) (l : List ℤ)
  (C : CertificateIrreducibleIntOfPrime f l) : Irreducible f := by
  have hlnnil : l ≠ 0 := List.ne_nil_of_length_pos (lt_trans (zero_lt_one) (C.hdeg))
  have hldrop : l = l.dropTrailingZeros := by
    rw [eq_dropTrailingZeros_iff_last_entry_ne_zero _ hlnnil]
    exact C.hlz
  rw [C.hpol]
  refine irreducible_of_eval_mul_prime C.M (C.ρ : ℝ) 1 C.P C.s (by decide) C.hPPrime _
    ?_ ?_ ?_ ?_ ?_ ?_
  · have hcd := C.hdeg
    by_contra hc
    rw [← natDegree_ofList _ hlnnil hldrop, hc] at hcd
    contradiction
  · intro z hz
    rw [← C.hrhoeq]
    refine ofList_roots_le_cauchy_bound_scale l hldrop C.hdeg z hz C.r C.hrpos
  · intro q hqu hqdvd
    by_contra hc
    simp only [not_le, Nat.lt_one_iff] at hc
    rw [Polynomial.eq_C_of_natDegree_eq_zero hc] at hqdvd hqu
    exact hqu (isUnit_C.2 (ofList_isPrimitive 1 l C.hprim (isUnit_one) _ hqdvd))
  · convert (Rat.cast_le (K := ℝ)).2 C.hrho
    norm_num
  · convert (Rat.cast_lt (K := ℝ)).2 C.hs
    norm_num
  · rw [← C.hpol]
    exact C.heval
