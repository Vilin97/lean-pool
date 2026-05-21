/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.FieldTheory.Finite.GaloisField
import LeanPool.RingOfIntegersProject.PolynomialsAsLists

/-! # Irreducibility of polynomials

We prove some results on irreducibility of polynomials over finite fields needed to prove
Rabin's test. We formalize different versions of this certificate.
We also prove a bound on the minimal degree of the factors of a polynomial based on
reductions modulo primes. We formalize a certificate for polynomials over the integers
based on degree analysis.

## Main results:
- `natDegree_dvd_iff_dvd_X_pow_sub_X` : the irreducible factors of `X ^ q ^ n - X` are
  the irreducible polynomials with degree dividing `n`.
- `irreducible_iff_dvd_X_pow_sub_X'` : statement used for Rabin's test.
- `le_natDegree_of_partialSums` : bound on the degree of non-unit divisors of a polynomial, based on
  degree analysis.

## Certificates:
- `IrreducibleCertificateIntPolynomial` : certifies irreducibility in `ℤ[X]` with degree analysis.
  Requires factorization information modulo primes. Uses list-based approach for polynomial arithemtic.
- `CertificateIrreducibleZMod` : Based on Rabin's test, certifies irreducibility of
  polynomials over `(ZMod p)`. Ranges through all divisors of the degree of the polynomial.
- `CertificateIrreducibleZMod'` : a version of `CertificateIrreducibleZMod` which only ranges
  over maximal proper divisors, but requires factorization data for the degree of the polynomial.
- `CertificateIrreducibleZModList`: A version of `CertificateIrreducibleZMod` using the
  list-based approach for polynomial arithmetic.
- `CertificateIrreducibleZModList'`: A version of `CertificateIrreducibleZMod'` using the
  list-based approach.  -/

open BigOperators Polynomial

section AuxiliaryLemmas

lemma isCoprime_sub_of_isCoprime_sub_dvd_sub {R : Type}[CommRing R]
    {a b c f: R}(h1: f ∣ a - b) (h2 : IsCoprime f (b - c)) :
    IsCoprime f (a - c) := by
  rcases h1 with ⟨z, hz⟩
  have : a - c = (b - c) + f * z := by rw [← hz] ; ring
  rw [this]
  apply IsCoprime.add_mul_left_right
  exact h2

lemma List.expand_ZMod (p : ℕ) [Fact $ Nat.Prime p] (l : List (ZMod p)) :
    (List.expand p l).dropTrailingZeros = (l ^ p).dropTrailingZeros := by
  rw [← List.expand_char]
  congr
  rw [ZMod.frobenius_zmod]
  exact (map_id'' (congrFun rfl) (expand p l)).symm

lemma pow_sub_one_dvd_pow_sub_one {α : Type*}[Ring α](x : α)(m n : ℕ)
    (hdvd : m ∣ n) : x ^ m - 1 ∣ x ^ n - 1 := by
  convert Commute.sub_dvd_pow_sub_pow (x := x ^ m) (y := 1)
    (Commute.one_right _) hdvd.choose using 1
  rw [one_pow, ← pow_mul, ← hdvd.choose_spec]

lemma pow_pow_sub_dvd_pow_pow_sub {α : Type*} [Ring α] {m n r: ℕ}
    (hpn : m ≠ 0) (hdvd : n ∣ r) (x : α) : (x ^ (m ^ n) - x) ∣ (x ^ (m ^ r) - x) := by
  have hdvdp: m ^ n - 1 ∣ m ^ r - 1 := by
    simp only [← Int.natCast_dvd_natCast, Nat.one_le_pow n m (Nat.zero_lt_of_ne_zero hpn),
    Nat.cast_sub, Nat.cast_pow, Nat.cast_one,
    Nat.one_le_pow r m (Nat.zero_lt_of_ne_zero hpn)]
    exact pow_sub_one_dvd_pow_sub_one _ _ _ hdvd
  convert mul_dvd_mul_left x (pow_sub_one_dvd_pow_sub_one x (m ^ n - 1) (m ^ r - 1) hdvdp) using 1
  rw [mul_sub, mul_pow_sub_one (pow_ne_zero n hpn) _, mul_one]
  rw [mul_sub, mul_pow_sub_one (pow_ne_zero r hpn) _, mul_one]

end AuxiliaryLemmas

section Morphisms

variable {F : Type*} [Field F] [DecidableEq F] {f : F[X]}
   [Fintype F] (hi : Irreducible f)

def charPOfCard (hp: Nat.Prime p) (hcard : Fintype.card F = p ^ n) : CharP F p := by
  have card_pow_ne_zero : n ≠ 0 :=
    fun h => (lt_self_iff_false _).1 (lt_of_lt_of_eq (Fintype.one_lt_card (α := F))
    (Eq.trans hcard (Eq.trans (congrArg (fun x => p ^ x) h) (pow_zero p))))
  have := FiniteField.cast_card_eq_zero (K:= F)
  rw [hcard] at this
  simp only [Nat.cast_pow, pow_eq_zero_iff', ne_eq, (card_pow_ne_zero),
    not_false_eq_true, and_true] at this
  rcases (Nat.dvd_prime hp).1 (ringChar.dvd this) with h1 | h2
  · have := ringChar.Nat.cast_ringChar (R:= F)
    rw [h1] at this
    simp only [Nat.cast_one, one_ne_zero] at this
  · exact ringChar.of_eq h2

/- A `(ZMod p)`-algebra morphism between two finite fields· -/
noncomputable def algHomOfCardPow (K : Type) {n m p: ℕ} [hp : Fact $ Nat.Prime p]
    [Field K] [Fintype K] [Algebra (ZMod p) F] [Algebra (ZMod p) K] (hdvd: m ∣ n)
    (hcp : Fintype.card F = p ^ m) (hc : Fintype.card K = p ^ n) : F →ₐ[ZMod p] K := by
  have : (X : (ZMod p)[X]) ^ p ^ m - X ∣ X ^ p ^ n - X := by
    have aux := pow_sub_one_dvd_pow_sub_one (p : ℤ) _ _ hdvd
    have hdvdp: p ^ m - 1 ∣ p ^ n - 1 := by
      simp only [← Int.natCast_dvd_natCast,
        Nat.one_le_pow m p (Nat.zero_lt_of_ne_zero (Ne.symm (NeZero.ne' p))),
        Nat.cast_sub, Nat.cast_pow, Nat.cast_one,
        Nat.one_le_pow n p (Nat.zero_lt_of_ne_zero (Ne.symm (NeZero.ne' p))), aux]
    have := mul_dvd_mul_left X (pow_sub_one_dvd_pow_sub_one (X : (ZMod p)[X]) _ _ hdvdp)
    rw [mul_sub, mul_sub, mul_pow_sub_one (pow_ne_zero m (Ne.symm (NeZero.ne' p))) _,
     mul_pow_sub_one (pow_ne_zero n (Ne.symm (NeZero.ne' p))) _, mul_one] at this
    exact this
  have := (pow_pow_sub_dvd_pow_pow_sub (α := (ZMod p)[X]) (m := p) ?_ (hdvd)) X
  rw [← hc] at this
  have hsplits := Polynomial.splits_of_splits_of_dvd (algebraMap (ZMod p) K) ?_ ?_ this
  have ϕ := Polynomial.IsSplittingField.lift (GaloisField p m) (X ^ p ^ m - X : (ZMod p)[X]) hsplits
  have : Fintype (GaloisField p m) := Fintype.ofFinite _
  have card_galoisField : m ≠ 0 → Fintype.card (GaloisField p m) = p ^ m := by
    intro hm
    rw [← GaloisField.card _ _ hm, Nat.card_eq_fintype_card]
  have iso:= FiniteField.algEquivOfCardEq (K:= F) (K':= (GaloisField p m)) (p:= p) ?_
  exact ϕ.comp iso.toAlgHom
  rw [card_galoisField, hcp]
  exact fun h => (lt_self_iff_false _).1 (lt_of_lt_of_eq (Fintype.one_lt_card (α := F))
    (Eq.trans hcp (Eq.trans (congrArg (fun x => p ^ x) h) (pow_zero p))))
  by_contra h
  nth_rw 2 [← pow_one X] at h
  rw [sub_eq_zero, Polynomial.X_pow_eq_monomial, Polynomial.X_pow_eq_monomial,
    Polynomial.monomial_left_inj] at h
  have := Fintype.one_lt_card (α := K)
  linarith
  exact one_ne_zero
  have hcomp : algebraMap (ZMod p) K = (RingHom.id K).comp (algebraMap (ZMod p) K) := rfl
  rw [hcomp, ← Polynomial.splits_map_iff, Polynomial.map_sub, Polynomial.map_pow, map_X]
  exact (Polynomial.IsSplittingField.splits')
  exact Nat.Prime.ne_zero hp.out

/- A ring homomorphism between two finite fields· -/
noncomputable def ringHomOfCardPow (K : Type) {n : ℕ} [Field K][Fintype K]
    (hc : Fintype.card K = (Fintype.card F) ^ n) : F →+* K := by
  choose p m hp hm using FiniteField.card' F
  rw [ hm, ← pow_mul] at hc
  have hdvd : (m : ℕ) ∣ m * n  := ⟨n, rfl⟩
  haveI := charPOfCard hp hm
  haveI := charPOfCard hp hc
  haveI : Fact $ Nat.Prime p := { out := hp }
  haveI : Algebra (ZMod p) F := ZMod.algebra F p
  haveI : Algebra (ZMod p) K := ZMod.algebra K p
  exact AlgHom.toRingHom (algHomOfCardPow K hdvd hm hc)

end Morphisms

section IrreducibilityTheory

variable {F : Type*} [Field F]  [CharP F p]
 {f : F[X]} (K : Type) [Field K] [Fintype K] [CharP K p] (hd : 0 < f.natDegree)
 (φ : F →+* K)

include hd in
 lemma exists_root_of_X_pow_card_sub_X
    (h : (Polynomial.map φ f : K[X]) ∣ (X ^ (Fintype.card K) - X : Polynomial K)) :
  ∃ a : K, Polynomial.eval₂ φ a f = 0 := by
  have : Polynomial.Splits (RingHom.id K) (Polynomial.map φ f) := by
    refine Polynomial.splits_of_splits_of_dvd (RingHom.id K) ?_ (Polynomial.IsSplittingField.splits') h
    by_contra hc
    rw [sub_eq_zero, Polynomial.X_pow_eq_monomial, ← pow_one X, Polynomial.X_pow_eq_monomial,
      Polynomial.monomial_left_inj (one_ne_zero)] at hc
    exact (lt_self_iff_false 1).mp (lt_of_lt_of_eq (Fintype.one_lt_card (α := K)) hc)
  rw [Polynomial.splits_iff_card_roots] at this
  have hdeg : (Polynomial.map φ f).natDegree = f.natDegree := natDegree_map _
  rw [hdeg] at this
  rw [← this] at hd
  obtain ⟨a,ha⟩:= Multiset.card_pos_iff_exists_mem.1 hd
  use a
  replace ha := (Polynomial.isRoot_of_mem_roots ha)
  rw [IsRoot, Polynomial.eval_map] at ha
  exact ha

noncomputable def algebraAdjoinRootOfDvd
    (hdvd : (Polynomial.map φ f : K[X]) ∣ (X ^ (Fintype.card K) - X : K[X]) ) :
    Algebra (AdjoinRoot f) K := by
  have := exists_root_of_X_pow_card_sub_X K hd φ hdvd
  choose a ha using this
  refine RingHom.toAlgebra (AdjoinRoot.lift φ a ha)

include hd in
lemma natDegree_dvd_of_dvd_X_pow_sub_X {n : ℕ} [Fintype F]
   (hn : n ≠ 0) (hi : Irreducible f) (h : f ∣ (X ^ ((Fintype.card F) ^ n) - X)) :
    f.natDegree ∣ n := by
  choose p m hp hm' using FiniteField.card' F
  haveI : Fact $ Nat.Prime p := { out := hp }
  have : ∀ m, Fintype (GaloisField p m) := fun m => Fintype.ofFinite _
  have hcard' : Fintype.card (GaloisField p (m * n)) = (Fintype.card F) ^ n := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p (m * n) ?_, hm', pow_mul]
    simp only [ne_eq, mul_eq_zero, PNat.ne_zero, false_or]
    exact hn
  let K := GaloisField p (m * n)
  let ψ := ringHomOfCardPow K hcard'
  replace h := Polynomial.map_dvd ψ h
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X] at h
  rw [← hcard'] at h
  have := exists_root_of_X_pow_card_sub_X K hd ψ h
  letI hal := algebraAdjoinRootOfDvd K hd ψ h
  letI hal2 : Algebra F K := RingHom.toAlgebra
    (RingHom.comp (algebraMap (AdjoinRoot f) K) (algebraMap F (AdjoinRoot f)))
  haveI hfinite: IsScalarTower F (AdjoinRoot f) K := IsScalarTower.of_algebraMap_eq' rfl
  haveI hfinite2 : FiniteDimensional F (AdjoinRoot f) :=
  PowerBasis.finite (AdjoinRoot.powerBasis (Irreducible.ne_zero hi))
  haveI : Fact $ Irreducible f := { out := hi }
  have := Module.finrank_mul_finrank F (AdjoinRoot f) K
  have hdim1: Module.finrank F (AdjoinRoot f)= f.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis (Irreducible.ne_zero hi)),
      AdjoinRoot.powerBasis_dim (Irreducible.ne_zero hi)]
  have hqo := Fintype.one_lt_card (α := F)
  have hdim2: Module.finrank F K = n := by
    have hcard:= @card_eq_pow_finrank F K _ _ _ _ _
    rw [hcard', pow_right_inj₀] at hcard
    exact hcard.symm
    linarith ; linarith
  rw [hdim1, hdim2] at this
  use (Module.finrank (AdjoinRoot f) K)
  exact this.symm

variable [DecidableEq F]

lemma dvd_X_pow_natDegree_sub_X [Fintype F] (hi : Irreducible f) :
     f ∣ (X ^ ((Fintype.card F) ^ (f.natDegree)) - X : F[X]) := by
  haveI := fact_iff.2 hi
  set m := f.natDegree with hmdef
  haveI hfinite : FiniteDimensional F (AdjoinRoot f) :=
  PowerBasis.finite (AdjoinRoot.powerBasis (Irreducible.ne_zero hi))
  have hdim1: Module.finrank F (AdjoinRoot f)= f.natDegree := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis (Irreducible.ne_zero hi)),
        AdjoinRoot.powerBasis_dim (Irreducible.ne_zero hi)]
  haveI hfin : Finite (AdjoinRoot f) := Module.finite_of_finite F
  haveI hfin : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hcard := @card_eq_pow_finrank F (AdjoinRoot f) _ _ _ _ _
  rw [hdim1, ← hmdef] at hcard
  set a := AdjoinRoot.root f
  have hpeval2 :
    Polynomial.eval₂ (AdjoinRoot.of f) a (X ^ (Fintype.card F) ^ f.natDegree - X) = 0 := by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_X]
    rw [← hmdef, ← hcard, FiniteField.pow_card, sub_self]
  have hgcdeval := Polynomial.eval₂_gcd_eq_zero (AdjoinRoot.eval₂_root f) hpeval2
  have hgcdnun: ¬ IsUnit (EuclideanDomain.gcd f (X ^ ( (Fintype.card F) ^ m) - X)) := by
    by_contra h
    rw [Polynomial.isUnit_iff] at h
    obtain ⟨r,hr1,hrp⟩:= h
    rw [←hmdef, ← hrp] at hgcdeval
    simp only [eval₂_C, _root_.map_eq_zero] at hgcdeval
    exact IsUnit.ne_zero hr1 hgcdeval
  obtain ⟨g, hg⟩:= EuclideanDomain.gcd_dvd_left f (X ^ ((Fintype.card F) ^ m) - X)
  have hunits:= Irreducible.isUnit_or_isUnit hi hg
  simp only [hgcdnun, false_or] at hunits
  obtain ⟨t, ht⟩:=  EuclideanDomain.gcd_dvd_right f (X ^ ((Fintype.card F) ^ m) - X)
  obtain ⟨gi, hgi⟩:= IsUnit.exists_right_inv hunits
  use (gi * t)
  rw [hg,  mul_assoc, ← mul_assoc g gi, hgi, one_mul]
  exact ht

variable [Fintype F]

lemma dvd_X_pow_natDegree_sub_X_of_natDegree_dvd (hi : Irreducible f)
    (hdvd : f.natDegree ∣ n) : f ∣ (X ^ ((Fintype.card F) ^ n) - X : F[X]) :=
  dvd_trans (dvd_X_pow_natDegree_sub_X hi)
  (pow_pow_sub_dvd_pow_pow_sub Fintype.card_ne_zero hdvd X)

/-- If `f` is irreducible, then its degree divides `n` if and only if `f` divides
  `X ^ ((Fintype.card F) ^ n) - X` -/
theorem natDegree_dvd_iff_dvd_X_pow_sub_X (hi : Irreducible f) :
    f.natDegree ∣ n ↔ f ∣ (X ^ ((Fintype.card F) ^ n) - X : F[X]) := by
  by_cases hn : n = 0
  · rw [hn]
    simp only [dvd_zero, pow_zero, pow_one, sub_self]
  · have hd : 0 < f.natDegree :=
      natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hi)
    constructor
    · exact dvd_X_pow_natDegree_sub_X_of_natDegree_dvd hi
    · refine natDegree_dvd_of_dvd_X_pow_sub_X hd hn hi

/-- A useful result to prove irreducibility of polynomials over finite fields. -/
theorem irreducible_iff_dvd_X_pow_sub_X (f : F[X]) (hd : 0 < f.natDegree) :
    Irreducible f ↔
    f ∣ (X ^ ((Fintype.card F) ^ (f.natDegree)) - X) ∧
    (∀ (m : ℕ), m ∣ (f.natDegree) →
      m ≠ f.natDegree → IsCoprime f (X ^ (((Fintype.card F)) ^ m) - X)) := by
  constructor
  · intro hi
    refine ⟨(natDegree_dvd_iff_dvd_X_pow_sub_X hi).1 dvd_rfl, ?_⟩
    intro m hmdvd hmne
    rcases (EuclideanDomain.dvd_or_coprime f (X ^ ((Fintype.card F) ^ m) - X) hi ) with h1 | h2
    · exfalso
      exact hmne (dvd_antisymm hmdvd ((natDegree_dvd_iff_dvd_X_pow_sub_X hi).2 h1))
    · exact h2
  · rintro ⟨hfdvd, hmh⟩
    obtain ⟨a, hai, b , heq⟩ := Polynomial.exists_irreducible_of_natDegree_pos hd
    have hadvd : natDegree a ∣ natDegree f :=
      (natDegree_dvd_iff_dvd_X_pow_sub_X hai).2 (dvd_trans ⟨b, heq⟩ hfdvd)
    have aux2: ¬ IsCoprime f (X^(Fintype.card F)^(natDegree a) - X) := by
      by_contra hc
      exact (Irreducible.not_unit hai )
        (IsCoprime.isUnit_of_dvd' hc ⟨b, heq⟩ ((natDegree_dvd_iff_dvd_X_pow_sub_X hai).1 dvd_rfl ))
    have hdeq := Not.imp aux2 (hmh (a.natDegree) hadvd)
    simp only [ne_eq, not_not] at hdeq
    exact Associated.irreducible
      (Polynomial.associated_of_dvd_of_natDegree_le ⟨b, heq⟩
        (ne_zero_of_natDegree_gt hd) (Nat.le_of_eq (id hdeq.symm)) ) hai

omit [DecidableEq F] in
lemma isCoprime_X_pow_sub_X_of_dvd_of_maximal_dvd (f : F[X])
  (h : ∀ (p : ℕ), Nat.Prime p → p ∣ (f.natDegree) →
  IsCoprime f (X ^ (((Fintype.card F)) ^ ((f.natDegree) / p)) - X)) :
  ∀ (m : ℕ), m ∣ (f.natDegree) →
      m ≠ f.natDegree → IsCoprime f (X ^ (((Fintype.card F)) ^ m) - X) := by
  intro m hmdvd hmne
  have hno : (f.natDegree) / m ≠ 1 := fun hc2 => hmne (Nat.eq_of_dvd_of_div_eq_one hmdvd hc2)
  have haux : m ∣ (f.natDegree / (f.natDegree / m).minFac) := by
    rw [Nat.dvd_div_iff_mul_dvd]
    nth_rw 2 [← Nat.div_mul_cancel hmdvd]
    refine mul_dvd_mul (Nat.minFac_dvd _) (dvd_rfl)
    refine dvd_trans (b := f.natDegree / m) (Nat.minFac_dvd _ )
      (Nat.div_dvd_of_dvd hmdvd)
  exact (IsCoprime.of_isCoprime_of_dvd_right ((h (f.natDegree / m).minFac
    (Nat.minFac_prime hno)
        (dvd_trans (b := f.natDegree / m) (Nat.minFac_dvd _ )
        (Nat.div_dvd_of_dvd hmdvd)) ))
        (pow_pow_sub_dvd_pow_pow_sub (Fintype.card_ne_zero) (haux) X))

/-- A version of `irreducible_iff_dvd_X_pow_sub_X` which only ranges through maximal proper
  divisors of the degree of `f`. This is the statament used for Rabin's test. -/
theorem irreducible_iff_dvd_X_pow_sub_X' (f : F[X]) (hd : 0 < f.natDegree) :
    Irreducible f ↔
    f ∣ (X ^ ((Fintype.card F) ^ (f.natDegree)) - X) ∧
    (∀ (p : ℕ), Nat.Prime p → p ∣ (f.natDegree) →
      IsCoprime f (X ^ (((Fintype.card F)) ^ ((f.natDegree) / p)) - X)) := by
  constructor
  · intro hi
    refine ⟨(natDegree_dvd_iff_dvd_X_pow_sub_X hi).1 dvd_rfl, ?_⟩
    intro p hp hpne
    rcases (EuclideanDomain.dvd_or_coprime f (X ^ ((Fintype.card F) ^ ((f.natDegree) / p)) - X) hi ) with h1 | h2
    · exfalso
      have hpdvd : (f.natDegree / p) ∣ f.natDegree := by exact Nat.div_dvd_of_dvd hpne
      have := (dvd_antisymm hpdvd ((natDegree_dvd_iff_dvd_X_pow_sub_X hi).2 h1))
      have := Nat.div_lt_self hd (Nat.Prime.one_lt hp)
      linarith
    · exact h2
  · rintro ⟨hfdvd, hmh'⟩
    exact (irreducible_iff_dvd_X_pow_sub_X f hd).2
      ⟨hfdvd , isCoprime_X_pow_sub_X_of_dvd_of_maximal_dvd f hmh'⟩

end IrreducibilityTheory


------------------------------------------------------------------------------------------

section DegreeAnalysisTheory

/-- If `a` divides `f`, there is a multiset of factors of `f` such that the
  degree of `a` is the sum of the degrees of the factors in this set.  -/
lemma natDegree_eq_sum_natDegree_factors_of_dvd {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq R] [UniqueFactorizationMonoid R] [NormalizationMonoid R]
    (f a : R[X]) (hfz : f ≠ 0) (hdvd : a ∣ f) :
    ∃ (S : Multiset R[X]) , S ≤ UniqueFactorizationMonoid.normalizedFactors f
      ∧ a.natDegree = Multiset.sum (Multiset.map natDegree S) := by
  have haz: a ≠ 0 := by
    by_contra h
    rw [h] at hdvd
    exact hfz (zero_dvd_iff.1 hdvd)
  use (UniqueFactorizationMonoid.normalizedFactors a)
  refine ⟨(UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors haz hfz).1 hdvd, ?_ ⟩
  rw [← Polynomial.degree_eq_iff_natDegree_eq haz,
  Polynomial.degree_eq_degree_of_associated (UniqueFactorizationMonoid.normalizedFactors_prod haz).symm,
  Polynomial.degree_eq_iff_natDegree_eq, Polynomial.natDegree_multiset_prod]
  · exact UniqueFactorizationMonoid.zero_not_mem_normalizedFactors a
  · simp only [ne_eq, Multiset.prod_eq_zero_iff]
    exact UniqueFactorizationMonoid.zero_not_mem_normalizedFactors a

lemma natDegree_eq_sum_natDegree_factors_of_dvd' {R : Type*} [CommRing R]
    [IsDomain R] [DecidableEq R] [UniqueFactorizationMonoid R] [NormalizationMonoid R]
    (f a : R[X]) (hfz : f ≠ 0) (hdvd : a ∣ f) :
    ∃ (S : Multiset ℕ), S ≤ (Multiset.map natDegree (UniqueFactorizationMonoid.normalizedFactors f))
    ∧ a.natDegree = Multiset.sum S := by
  obtain ⟨S, hS1, hS2⟩ := natDegree_eq_sum_natDegree_factors_of_dvd f a hfz hdvd
  use (Multiset.map natDegree S)
  exact ⟨Multiset.map_le_map hS1, hS2⟩

/-- If `a` divides `f` and `σ : R →+* K` maps the leading coefficient of `f` to a non-zero element,
  then the degree of `a` is the sum of the degrees of a subset of the factors of `map σ f`. -/
lemma natDegree_eq_sum_natDegree_map_factors_of_dvd {R : Type*} [CommRing R]
    [NoZeroDivisors R] {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    [UniqueFactorizationMonoid K] [NormalizationMonoid K]
    (f a : R[X]) (hdvd : a ∣ f) (σ : R →+* K) (hmf : σ (f.leadingCoeff) ≠ 0) :
    ∃ (S : Multiset ℕ),
    S ≤ (Multiset.map natDegree (UniqueFactorizationMonoid.normalizedFactors (map σ f)))
    ∧ a.natDegree = Multiset.sum S := by
  have hm : σ (a.leadingCoeff) ≠ 0 := by
    by_contra hc
    refine hmf (eq_zero_of_zero_dvd ?_)
    convert _root_.map_dvd σ (Polynomial.leadingCoeff_dvd_leadingCoeff hdvd)
    exact hc.symm
  convert natDegree_eq_sum_natDegree_factors_of_dvd' (map σ f) (map σ a)
    ?_ (Polynomial.map_dvd σ hdvd)
  exact (Polynomial.natDegree_map_of_leadingCoeff_ne_zero σ hm).symm
  by_contra hc
  rw [← Polynomial.leadingCoeff_eq_zero,
    Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero σ hmf] at hc
  exact hmf hc

lemma natDegree_eq_sum_natDegree_map_factors_of_dvd_monic {R : Type*} [CommRing R]
    {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    [UniqueFactorizationMonoid K] [NormalizationMonoid K]
    (f a : R[X]) (hf : Monic f) (hdvd : a ∣ f) (σ : R →+* K) (hm : σ (a.leadingCoeff) ≠ 0) :
    ∃ (S : Multiset ℕ),
    S ≤ (Multiset.map natDegree (UniqueFactorizationMonoid.normalizedFactors (map σ f)))
    ∧ a.natDegree = Multiset.sum S := by
  convert natDegree_eq_sum_natDegree_factors_of_dvd' (map σ f) (map σ a)
    (Polynomial.Monic.ne_zero (Polynomial.Monic.map σ hf)) (Polynomial.map_dvd σ hdvd)
  rw [← Polynomial.natDegree_map_of_leadingCoeff_ne_zero σ hm]

/-- Computes all the partial sums of list. -/
def partialSums {R : Type*} [AddMonoid R] (L : List R) : List R :=
  List.map (List.sum) (List.sublists L)

lemma multisetSum_mem_partialSums
    {R : Type*} [AddCommMonoid R] (S : Multiset R) (L : List R)
    (hle : S ≤ ↑L) :
    Multiset.sum S ∈ (partialSums L) := by
  have auxeq: ↑(Multiset.toList S ) = S := by exact Multiset.coe_toList S
  rw [← auxeq, Multiset.coe_le] at hle
  obtain ⟨L₂, hL1, hL2⟩ := hle
  rw [← List.mem_sublists] at hL2
  rw [← auxeq, Multiset.sum_coe, ← List.Perm.sum_eq hL1]
  exact List.mem_map_of_mem List.sum hL2

/-- If `a` divides `f` and `σ : R →+* K` maps the leading coefficient of `f` to a non-zero element,
  then the degree of `a` is contained in the list of partial sums of the degrees of the factors
  of `f`. -/
lemma natDegree_in_partialSums  {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    [UniqueFactorizationMonoid R] [NormalizationMonoid R] (f a : Polynomial R)
    (hdvd : a ∣ f)  (K : Type*) [CommRing K] [IsDomain K] [DecidableEq K]
    [UniqueFactorizationMonoid K] [NormalizationMonoid K]
    (σ : R →+* K) (L : List ℕ)
    (hmf : σ (f.leadingCoeff) ≠ 0 )
    (hfL :↑L = (Multiset.map natDegree (UniqueFactorizationMonoid.normalizedFactors (map σ f)))) :
      a.natDegree ∈ partialSums L := by
  have : σ (a.leadingCoeff) ≠ 0 := by
    by_contra hc
    refine hmf (eq_zero_of_zero_dvd ?_)
    convert _root_.map_dvd σ (Polynomial.leadingCoeff_dvd_leadingCoeff hdvd)
    exact hc.symm
  obtain ⟨S, hS1, hS2⟩ := natDegree_eq_sum_natDegree_map_factors_of_dvd f a hdvd σ hmf
  rw [← hfL] at hS1
  rw [hS2]
  exact multisetSum_mem_partialSums S L hS1

lemma natDegree_in_partialSums_monic {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    [UniqueFactorizationMonoid R] [NormalizationMonoid R] (f a : Polynomial R)
    (hf : Monic f) (hdvd : a ∣ f) (K : Type*) [CommRing K] [IsDomain K] [DecidableEq K]
    [UniqueFactorizationMonoid K] [NormalizationMonoid K]
    (σ : R →+* K) (L : List ℕ)
    (hfL : ↑L = (Multiset.map natDegree (UniqueFactorizationMonoid.normalizedFactors (map σ f)))) :
       a.natDegree ∈ partialSums L := by
  have : σ (a.leadingCoeff) ≠ 0 := by
    apply IsUnit.ne_zero
    apply IsUnit.map
    exact Polynomial.Monic.isUnit_leadingCoeff_of_dvd hf hdvd
  obtain ⟨S, hS1, hS2⟩ := natDegree_eq_sum_natDegree_map_factors_of_dvd_monic f a hf hdvd σ this
  rw [← hfL] at hS1
  rw [hS2]
  exact multisetSum_mem_partialSums S L hS1

lemma natDegree_in_partialSums_int (f a : Polynomial ℤ)
    (hdvd : a ∣ f) (p : Fin n → ℕ) [∀ i, Fact $ Nat.Prime (p i )]
    (L : Fin n → List ℕ) (hmf : ∀ i, (algebraMap ℤ (ZMod (p i))) (f.leadingCoeff) ≠ 0)
    (hfL : ∀ i , ↑(L i) = (Multiset.map natDegree (UniqueFactorizationMonoid.normalizedFactors
    (map (algebraMap ℤ (ZMod (p i))) f)))) :
    ∀ i, a.natDegree ∈ partialSums (L i) := by
  intro i
  refine natDegree_in_partialSums  f a hdvd
    (ZMod (p i)) (algebraMap ℤ (ZMod (p i))) (L i) (hmf i) (hfL i)

lemma natDegree_in_partialSums_int_monic (f a : Polynomial ℤ)
    (hf : Monic f) (hdvd : a ∣ f) (p : Fin n → ℕ)
    [∀ i, Fact $ Nat.Prime (p i )] (L : Fin n → List ℕ)
    (hfL : ∀ i , ↑(L i) = (Multiset.map natDegree (UniqueFactorizationMonoid.normalizedFactors
    (map (algebraMap ℤ (ZMod (p i))) f)))) :
      ∀ i, a.natDegree ∈ partialSums (L i) := by
  intro i
  refine natDegree_in_partialSums_monic f a hf hdvd
    (ZMod (p i)) (algebraMap ℤ (ZMod (p i))) (L i) (hfL i)

/- Computes the intersection of a finite number of lists· -/
def List.bagInterOfFn {R : Type*} [BEq R] {n : ℕ} : (Fin n → List R) → List R :=
  match n with
  | 0 => fun _ => []
  | 1 => fun f => (f ↑0)
  | Nat.succ (Nat.succ n) =>
      fun f =>
      let f' := fun i => f (i : Fin (Nat.succ n));
      List.bagInter (List.bagInterOfFn f') (f ↑(Nat.succ n))

lemma bagInterOfFn_mem {R : Type*} [DecidableEq R] {n : ℕ} [NeZero n] (L : Fin n → List R) (a : R) :
    a ∈ List.bagInterOfFn L ↔ ∀ i, a ∈ L i :=
  have : n ≠ 0 := by exact NeZero.ne n
  match n with
  | 0 => (by exact (this rfl).elim)
  | Nat.succ n => by
    induction n with
    | zero =>
      unfold List.bagInterOfFn
      constructor
      · intro ha  ; intro i ; fin_cases i ; exact ha
      · intro ha ; exact ha 0
    | succ n hn =>
      unfold List.bagInterOfFn
      constructor
      · intro ha ; intro i
        by_cases h : i = Fin.last _
        · rw [h]
          convert (List.mem_bagInter.1 ha).2
          simp only [Fin.natCast_eq_last]
        · convert (hn (λ i => L (i : Fin (Nat.succ n))) (by exact Nat.succ_ne_zero n)).1 (List.mem_bagInter.1 ha).1 (Fin.castPred i h)
          exact (Fin.cast_val_eq_self i).symm
      · intro h
        rw [List.mem_bagInter]
        constructor
        · rw [(hn (λ i => L (i : Fin (Nat.succ n))) (by exact Nat.succ_ne_zero n))]
          intro i
          exact h i
        · exact h (Nat.succ n)

/-- For `f` monic of degree `n`, if the intersection of the lists of partial sums of the degrees
  of the factors of `f` modulo a finite set of primes is equal to `[0, n]`, then `f` is irreducible. -/
lemma irreducible_of_partialSums (f : Polynomial ℤ) (n : ℕ)
    (hf : Monic f) (hdeg : f.natDegree = n) (hgt : n ≠ 0) (m : ℕ) [NeZero m]
    (p : Fin m → ℕ) [∀ i, Fact $ Nat.Prime (p i) ] (L : Fin m → List ℕ)
    (hL : ∀ i ,
    ↑(L i) = (Multiset.map natDegree
    (UniqueFactorizationMonoid.normalizedFactors (map (algebraMap ℤ (ZMod (p i))) f ))))
    (hinter : (List.bagInterOfFn (fun i => partialSums (L i))).dedup = [0 , n].dedup) :
    Irreducible f := by
  have : f ≠ 1 := by
    by_contra h
    rw [h, natDegree_one] at hdeg
    rw [← hdeg] at hgt
    contradiction
  rw [Polynomial.Monic.irreducible_iff_natDegree' hf]
  refine ⟨this, ?_ ⟩
  intro g h _ _ hmul
  have aux := natDegree_in_partialSums_int_monic f h hf (Dvd.intro_left _ hmul) p L ?_
  have aux2 : h.natDegree ∈ (List.bagInterOfFn (fun i => partialSums (L i))).dedup := by
    simp only [List.mem_dedup, bagInterOfFn_mem]
    exact aux
  rw [hinter] at aux2
  simp only [List.mem_dedup, List.mem_cons, List.mem_singleton] at aux2
  simp only [List.not_mem_nil, or_false] at aux2
  rcases aux2 with h1 | h2
  · rw [h1]
    simp only [Finset.mem_Ioc, lt_self_iff_false, zero_le, and_true, not_false_eq_true]
  · rw [hdeg, h2]
    simp only [Finset.mem_Ioc, not_and, not_le]
    intro hn
    by_cases ht : 2 ≤ n
    · exact Nat.log2_terminates n ht
    · have : n = 1 := by linarith
      rw [this]
      simp only [Nat.reduceDiv, zero_lt_one]
  exact hL

/-- For `f` primitive and a finite set of primes such that the leading coefficient of `f` is not
  zero modulo those primes, if the minimal element (excluding zero) of the
  intersection of the lists of partial sums of the degrees of the factors of `f` modulo those primes
  is equal to `d`, then any non-unit divisor of `f` has degree greater or equal to `d`. -/
lemma le_natDegree_of_partialSums (f : Polynomial ℤ) (d : ℕ) (hf : f.IsPrimitive)
    (m : ℕ) [NeZero m] (p : Fin m → ℕ)
    [∀ i, Fact $ Nat.Prime (p i) ] (L : Fin m → List ℕ)
    (hmf : ∀ i, (algebraMap ℤ (ZMod (p i))) (f.leadingCoeff) ≠ 0)
    (hL : ∀ i , ↑(L i) = (Multiset.map natDegree
      (UniqueFactorizationMonoid.normalizedFactors (map (algebraMap ℤ (ZMod (p i))) f ))))
    (hmin : ((List.bagInterOfFn (fun i => partialSums (L i))).filter (fun a => a ≠ 0)).min? = some d)
    : ∀ q : ℤ[X], ¬ IsUnit q → q ∣ f → d ≤ q.natDegree := by
  intro q hqu hqdvd
  have hdz : d ≠ 0 := by
    have :=  List.of_mem_filter (List.min?_mem (α := ℕ) (fun a b => min_choice a b) hmin)
    simp only [ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at this
    exact this
  have hqdeg : q.natDegree ≠ 0 := by
    intro hc
    rw [Polynomial.eq_C_of_natDegree_eq_zero hc] at hqdvd hqu
    exact hqu (Polynomial.isUnit_C.2 (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.1 hf (q.coeff 0) hqdvd))
  have := List.mem_filter_of_mem ((bagInterOfFn_mem _ _).2 (natDegree_in_partialSums_int f q hqdvd p L hmf hL))
    (p := fun a => a ≠ 0 )
    (by simp only [ne_eq, hqdeg, not_false_eq_true, decide_True])
  apply_fun Option.getD at hmin
  have aux := congr_fun hmin 0
  rw [Option.getD_some, List.getD_min?_eq_untop'_minimum, WithTop.untop'_eq_iff ] at aux
  rcases aux with h1 | h2
  · exact List.minimum_le_of_mem this h1
  · exfalso
    exact hdz h2.2

/-- The list of degrees of the normalized factors of `ofList l` is obtained from the lengths of
  the lists corresponding to irreducible polynomials that when multiplied together equal `l`. -/
lemma natDegree_list_factors_of_lists {K : Type u} [Field K] [DecidableEq K]
    (l : List K) (m : ℕ) (F : Fin m → List K) (deg : Fin m → ℕ)
    (hl : ∀ i, (F i).length = deg i + 1 )
    (hirr : ∀ i , Irreducible (ofList (F i)))
    (hm : ∀ i , (F i).getLast ((List.ne_nil_of_length_pos
    (lt_of_lt_of_eq (Nat.succ_pos (deg i)) (hl i).symm) )) ≠ 0)
    (hprod : (List.prod (List.ofFn (fun i => F i))).dropTrailingZeros' = l) :
    ↑(List.ofFn deg) = Multiset.map natDegree
    (UniqueFactorizationMonoid.normalizedFactors (ofList l)) := by
  apply_fun ofList at hprod
  rw [← dropTrailingZeros_eq_dropTrailingZeros',
  ofList_dropTrailingZeros_eq_ofList, list_sum_eq_ofList_prod] at hprod
  rw [← hprod, ← Fin.prod_ofFn, ← Multiset.prod_coe,
    UniqueFactorizationMonoid.normalizedFactors_prod_eq]
  simp only [ Multiset.map_coe, List.map_ofFn, Function.comp_def,
    Polynomial.natDegree_eq_of_degree_eq (Polynomial.degree_normalize)]
  have hd : ∀ i , natDegree (ofList (F i)) = deg i := by
    intro i
    rw [← Nat.succ_inj, Nat.succ_eq_add_one, Nat.succ_eq_add_one,
      ← hl, natDegree_ofList _ (((List.ne_nil_of_length_pos
        (lt_of_lt_of_eq (Nat.succ_pos (deg i)) (hl i).symm) )))]
    rw [eq_dropTrailingZeros_iff_last_entry_ne_zero _ (((List.ne_nil_of_length_pos
      (lt_of_lt_of_eq (Nat.succ_pos (deg i)) (hl i).symm) )))]
    exact hm i
  simp_rw [hd]
  simp only [Multiset.mem_coe, List.forall_mem_ofFn_iff]
  exact hirr

end DegreeAnalysisTheory

-----------------------------------------------------
/- # DEGREE ANALYSIS CERTIFICATE FOR IRREDUCIBILITY OF INTEGER POLYNOMIALS

In some cases, it's possible to prove the irreducibility of a polynomial `T` over the integers
by looking at its factorization type modulo different primes. A key requirement is to be able
to prove the irreducibility of polynomials over `(ZMod p)`. We provide a certificate for this
purpose later.  -/


/-- A certificate for the irreducibility of `T` using lists, based on degree analysis:
  - `n` is the length of the tuple of primes.
  - `p` is a tuple of primes such that the leading coefficient of `T` is non-zero modulo
      every `p i`.
  - `d` is the degree of the polynomial.
  - `m` is the tuple with the number of irreducible factors of `f` modulo primes in `p`.
  - `F` has the irreducible factors of `f` modulo primes in `p` (as lists).
  - `D` has the degrees of the irreducible factors of `f` modulo primes in `p`.

    If the minimal non-zero element in the intersection of the partial sums
    of the lists of degrees of the irreducible factors of `T` modulo those primes is equal to `d`,
    then `T` is irreducible.  -/
structure IrreducibleCertificateIntPolynomial (T : Polynomial ℤ) (l : List ℤ) where
  hpol : T = ofList l
  n : ℕ
  d : ℕ
  hprim : List.foldr gcd 0 l = 1
  hdeg : l.length = d + 1
  hnn : n ≠ 0
  hdn : d ≠ 0
  p : Fin n → ℕ
  hp : ∀ i , Nat.Prime (p i)
  hlc : ∀ i, algebraMap ℤ (ZMod (p i)) (l.getLast (List.ne_nil_of_length_eq_add_one hdeg)) ≠ 0
  m : Fin n → ℕ
  F : ∀ i , Fin (m i) → List (ZMod (p i))
  D : ∀ i , Fin (m i) → ℕ
  hl : ∀ i j, (F i j).length = D i j + 1
  hirr : ∀ i j , Irreducible (ofList (F i j))
  hm : ∀ i j, (F i j).getLast (List.ne_nil_of_length_pos (lt_of_lt_of_eq (Nat.succ_pos (D i j)) (hl i j).symm) ) ≠ 0
  hprod : ∀ i, (List.prod (List.ofFn (fun j => F i j))).dropTrailingZeros' = List.map (algebraMap ℤ (ZMod (p i))) l
  hinter : ((List.bagInterOfFn (fun i => partialSums (List.ofFn (D i)))).filter (fun a => a ≠ 0)).min? = some d

lemma irreducible_of_CertificateIntPolynomial (T : Polynomial ℤ) (l : List ℤ)
    (C : IrreducibleCertificateIntPolynomial T l) : Irreducible T := by
  rw [C.hpol]
  haveI : ∀ i , Fact $ Nat.Prime (C.p i) := by
    intro i
    exact fact_iff.2 (C.hp i)
  haveI : NeZero (C.n) := neZero_iff.2 C.hnn
  have hlnnil : l ≠ 0 := List.ne_nil_of_length_eq_add_one C.hdeg
  have hldrop : l = l.dropTrailingZeros := by
    rw [eq_dropTrailingZeros_iff_last_entry_ne_zero _ hlnnil]
    have := C.hlc 0
    by_contra hc
    rw [hc] at this
    simp only [algebraMap_int_eq, map_zero, ne_eq, not_true_eq_false] at this
  have Tdeqd : (ofList l).natDegree = C.d := by
    have hcd := C.hdeg
    rw [← natDegree_ofList _ hlnnil hldrop] at hcd
    exact Nat.add_right_cancel hcd
  have Tdeg : (ofList l).natDegree ≠ 0 := Ne.symm (ne_of_ne_of_eq (id (Ne.symm C.hdn))
    (id (Eq.symm Tdeqd)))
  rw [irreducible_iff]
  constructor
  · refine Polynomial.not_isUnit_of_natDegree_pos _ (Nat.pos_of_ne_zero Tdeg)
  · intro a b hab
    by_cases h: IsUnit b
    · exact Or.inr h
    · left
      have hbdeg : b.natDegree = (ofList l).natDegree := by
        refine le_antisymm (Polynomial.natDegree_le_of_dvd (Dvd.intro_left _ hab.symm)
        (Polynomial.ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero Tdeg))) ?_
        rw [Tdeqd]
        refine (le_natDegree_of_partialSums _ C.d ?_ C.n C.p
          (fun i => List.ofFn (C.D i)) ?_ ?_ ?_ ) b h
          (Dvd.intro_left _ hab.symm)
        · exact ofList_isPrimitive 1 l C.hprim (isUnit_one)
        · rw [ofList_leadingCoeff l hlnnil hldrop] ; exact C.hlc
        · intro i
          convert natDegree_list_factors_of_lists (List.map (algebraMap ℤ (ZMod (C.p i))) l)
            _ (C.F i) (C.D i) (C.hl i) (C.hirr i) (C.hm i) (C.hprod i)
          exact ofList_map _ _
        · exact C.hinter
      have : a.natDegree = 0 := by
        have hbn : b ≠ 0 := by
          intro hc
          rw [hc, natDegree_zero] at hbdeg
          exact Tdeg hbdeg.symm
        have han : a ≠ 0 := by
          intro hc
          rw [hc, zero_mul] at hab
          rw [hab, natDegree_zero] at Tdeg
          contradiction
        apply_fun natDegree at hab
        rw [natDegree_mul han hbn, hbdeg] at hab
        linarith
      rw [Polynomial.eq_C_of_natDegree_eq_zero this] at hab ⊢
      exact Polynomial.isUnit_C.2 (Polynomial.isPrimitive_iff_isUnit_of_C_dvd.1
        (ofList_isPrimitive 1 l C.hprim (isUnit_one)) (a.coeff 0) (Dvd.intro _ hab.symm))


------------------------------------------------------------------------
/- # CERTIFICATE FOR IRREDUCIBILITY MOD P

To prove irreducibility of polynomials over `(ZMod p)` we form a certificate based on
`irreducible_iff_dvd_X_pow_sub_X`. In order to prove `f ∣ X ^ n - X` we use repeated `t`-powering,
often taking `t = 2`, and provide certifying polynomials at each step.  -/


/-- Takes a function `Fin n → ℕ` and interprets it as a list of digits of a number in base `t`.
We use this instead of `Nat.ofDigits` to control for the number of digits.  -/
def FnToNat {n : ℕ} (t : ℕ) (b : Fin n → ℕ) : ℕ := ∑ i, (b i) * (t ^ (i : ℕ))

lemma FnToNat_eval_single {n : ℕ}(t : ℕ)(j : Fin n):
    FnToNat t (Finsupp.single j 1) = t ^ (j : ℕ) := by
  unfold FnToNat
  rw [Fintype.sum_eq_single j, Finsupp.single_eq_same, one_mul]
  intro x hx
  rw [Finsupp.single_apply]
  simp only [mul_eq_zero]
  simp only [hx.symm, ↓reduceIte, Fin.val_zero', pow_eq_zero_iff', ne_eq, true_or]


/-- The `square-and-multiply`-type algorithm. Gives a way to prove `x ^ n` by
  providing a list `y` with intermediate steps. -/
lemma square_and_multiply_algorithm {R : Type*} [Monoid R] {s t: ℕ} (y : Fin (s + 1) → R)
    (bit : Fin (s + 1) → ℕ) (x : R) (hs : y s = x ^ (bit s : ℕ))
    (hmul : ∀ (i : Fin s),
      y (Fin.castSucc i) = (y (Fin.succ i)) ^ t * x ^ (bit (Fin.castSucc i) : ℕ)) :
     y 0 = x ^ (FnToNat t bit) := by
  induction s with
  | zero =>
    erw [hs]
    unfold FnToNat
    simp only [Nat.cast_zero, Nat.reduceAdd, Finset.univ_unique, Fin.zero_eta,
      Fin.val_eq_zero, pow_zero, mul_one, Finset.sum_singleton, Fin.default_eq_zero]
  | succ s hsucc =>
    let bit' := λ (i : Fin (s + 1)) => bit (Fin.succ i)
    let y' := λ (i : Fin (s + 1)) => y (Fin.succ i)
    have aux : FnToNat t bit = t * (FnToNat t bit') + (bit 0 : ℕ) := by
      unfold FnToNat
      erw [Fin.sum_univ_succ, pow_zero, mul_one, add_comm, Finset.mul_sum]
      simp only [Fin.val_succ, add_left_inj]
      congr
      simp_rw [mul_comm, ← mul_assoc, pow_succ, mul_comm]
    rw [aux, mul_comm, pow_add, pow_mul]
    have aux2 := hsucc y' bit' ?_ ?_
    swap
    convert hs
    · repeat { rw [Fin.natCast_eq_last, Fin.natCast_eq_last] ; rfl }
    · rw [Fin.natCast_eq_last, Fin.natCast_eq_last] ; rfl
    rw [← aux2] ; exact (hmul 0)
    · intro i
      exact hmul (Fin.succ i)


lemma certificate_aux (p n t s : ℕ) [Fact $ Nat.Prime p] [NeZero n]
    (f : (ZMod p)[X]) (bit : Fin (s + 1) → ℕ)
    (hbits : FnToNat t bit = p) (h : Fin (n + 1) → (ZMod p)[X])
    (g : Fin n → Fin s → (ZMod p)[X])
    (h' : Fin n → Fin (s + 1) → (ZMod p)[X])
    (hs : ∀ (i : Fin n), h' i s = (h (Fin.castSucc i)) ^ (bit s))
    (hz : ∀ (i : Fin n), h' i 0 = h (Fin.succ i))
    (hmul : ∀ (i : Fin n) , ∀ (j : Fin s), f * (g i j) =
    (h' i (Fin.succ j)) ^ t * (h i) ^ (bit (Fin.castSucc j) : ℕ) - h' i (Fin.castSucc j))
    (i : Fin n) :
    f ∣ (h (Fin.castSucc i)) ^ p - h (Fin.succ i) := by
  have aux : ∀ i , ∀ j , f ∣ (h' i (Fin.succ j)) ^ t *
    (h i) ^ (bit (Fin.castSucc j) : ℕ) - h' i (Fin.castSucc j) := by
    intro i j
    use (g i j)
    exact (hmul i j).symm
  simp_rw [← Ideal.Quotient.eq_zero_iff_dvd, map_sub, map_pow, sub_eq_zero] at aux ⊢
  simp_rw [map_mul, map_pow] at aux
  simp_rw [← hbits, ← hz]
  let y : Fin (s + 1) → ((ZMod p)[X]) ⧸ (Ideal.span {f}) :=
    λ j => Ideal.Quotient.mk (Ideal.span {f}) (h' i j)
  refine (square_and_multiply_algorithm y (bit) _ ?_ ?_).symm
  · have := hs
    simp only [y]
    rw [hs i] ; rfl
  · intro j
    convert (aux i j).symm
    simp only [Fin.coe_eq_castSucc]

lemma certificate_aux' (p n t s : ℕ) [NeZero n] [hp : Fact $ Nat.Prime p]
    (f : (ZMod p)[X]) (bit : Fin (s + 1) → ℕ)
    (hbits : FnToNat t bit = p) (h : Fin (n + 1) → (ZMod p)[X])
    (g : Fin n → Fin s → (ZMod p)[X])
    (h' : Fin n → Fin (s + 1) → (ZMod p)[X])
    (hs : ∀ (i : Fin n), h' i s = (h (Fin.castSucc i)) ^ (bit s))
    (hz : ∀ (i : Fin n), h' i 0 = h (Fin.succ i))
    (hmul : ∀ (i : Fin n) , ∀ (j : Fin s), f * (g i j) =
      (h' i (Fin.succ j)) ^ t * (h i) ^ (bit (Fin.castSucc j) : ℕ) - h' i (Fin.castSucc j))
    (k : Fin (n + 1)) : f ∣ (h 0) ^ (p ^ (k : ℕ)) - h k := by
  have aux := certificate_aux p n t s f bit hbits h g h' hs hz hmul
  simp_rw [← Ideal.Quotient.eq_zero_iff_dvd, map_sub, map_pow, sub_eq_zero] at aux ⊢
  let bit := (Finsupp.single (k : Fin (k + 1)) (1 : ℕ))
  have hpow: FnToNat p bit = p ^ ( (k : Fin (k + 1)) : ℕ) := FnToNat_eval_single p (k : Fin (k + 1))
  have : ( (k : Fin (k + 1)) : ℕ)  = ((k : Fin (n + 1)) : ℕ ) :=
    by simp only [Fin.natCast_eq_last, Fin.val_last]
  rw [this] at hpow
  rw [← hpow]
  let y : (Fin (k + 1) → ((ZMod p)[X]) ⧸ (Ideal.span {f}) ) :=
    λ i => Ideal.Quotient.mk (Ideal.span {f}) (h (((k.val - i.val) : ℕ)))
  convert (square_and_multiply_algorithm y bit _ ?_ ?_).symm
  · simp only [Fin.val_zero, tsub_zero]
    exact (Fin.cast_val_eq_self k).symm
  · simp only [Fin.natCast_eq_last, Fin.val_last, ge_iff_le, le_refl, tsub_eq_zero_of_le,
    Nat.cast_zero, Finsupp.single_eq_same, pow_one, y, bit]
  · intro i
    have hnz: 0 < k.val - i.val := by zify[i.2] ; linarith[i.2]
    have hle: k.val - i.val - 1 < n := by zify[i.2, k.2, hnz] ; linarith [i.2, k.2, hnz]
    convert (aux ⟨k.val - i.val - 1 , hle ⟩).symm
    · rw [← Fin.val_inj, Fin.val_succ, Fin.val_cast_of_lt]
      simp only [Fin.coe_castSucc]
      exact Nat.eq_add_of_sub_eq hnz rfl
      exact (tsub_lt_iff_right (Nat.succ_le_of_lt hnz)).mp hle
    · have auxb: bit (Fin.castSucc i) = 0 := by
        refine Finsupp.single_eq_of_ne (Fin.ne_of_gt ?_)
        simp only [Fin.natCast_eq_last, Fin.castSucc_lt_last i]
      erw [auxb, pow_zero, mul_one]
      dsimp ;
      simp only [Fin.val_succ, y]
      congr
      rw [← Fin.val_inj, Fin.val_cast_of_lt]
      rfl
      exact Nat.lt_add_right 1 hle

/-- Certificate for irreducibility of a polynomial `f` over `(ZMod p)`.
- `t` is the base number used for the `t`-power-and-multiply approach (usually `t = 2` or `t = p`).
- `n` is the degree of `f`
- `bit` is the representation of `p` in base `t`.
- `h` tuple with the values of `X ^ p ^ i (mod f)` for `0 ≤ i ≤ n`
- `g` and `h'` certifiy the steps in the`t`-power-and-multiply algorithm to find `hᵢ ^ p mod f`.

The degree of the polynomials needed in the certificate is at most `2 * n * (t - 1)`.
The number of polynomials required is `2 * n * logₜ(p) + 3 * n`· Sometimes it might be advantageous
to take `t = p` because computing `p`-powers is easy in characteristic `p`.  -/
structure CertificateIrreducibleZMod (p n t s : ℕ) [Fact $ Nat.Prime p] [NeZero n] (f : (ZMod p)[X]) where
  hdeg : f.natDegree = n
  bit : Fin (s + 1) → ℕ
  hbits : FnToNat t bit = p
  h : Fin (n + 1) → (ZMod p)[X]
  g : Fin n → Fin s → (ZMod p)[X]
  h' : Fin n → Fin (s + 1) → (ZMod p)[X]
  hs : ∀ (i : Fin n), h' i s = (h (Fin.castSucc i)) ^ (bit s)
  hz : ∀ (i : Fin n), h' i 0 = h (Fin.succ i)
  hmul : ∀ (i : Fin n) , ∀ (j : Fin s), f * (g i j) =
    (h' i (Fin.succ j)) ^ t * (h i) ^ (bit (Fin.castSucc j) : ℕ) - h' i (Fin.castSucc j)
  a : Fin n → (ZMod p)[X]
  b : Fin n → (ZMod p)[X]
  hhz : h 0 = X
  hhn : h n = X
  hgcd : ∀ (m : Fin n), ↑m ∣ n → (a m) * f + (b m) * ((h (Fin.castSucc m)) - X) = 1



lemma irreducible_of_CertificateIrreducibleZMod (p n t s: ℕ)[Fact $ Nat.Prime p] [NeZero n]
    {f : (ZMod p)[X]} (C : CertificateIrreducibleZMod p n t s f) : Irreducible f := by
  have hd : 0 < f.natDegree := by
    rw [C.hdeg]
    exact Fin.size_pos'
  rw [irreducible_iff_dvd_X_pow_sub_X f hd, ZMod.card, C.hdeg]
  have aux := certificate_aux' p n t s f C.bit C.hbits C.h C.g C.h' C.hs C.hz C.hmul
  constructor
  · have aux1 := aux n
    rw [C.hhz, C.hhn, Fin.natCast_eq_last, Fin.val_last] at aux1
    exact aux1
  · intro m hmdvd hneq
    have hmlt1 : m < n := (lt_of_le_of_ne (Nat.le_of_dvd (Fin.size_pos') hmdvd) hneq )
    have hmlt : m < n + 1 := Nat.lt_add_right 1 hmlt1
    convert isCoprime_sub_of_isCoprime_sub_dvd_sub (aux ⟨m, hmlt⟩) ?_
    exact (C.hhz).symm
    use (C.a ⟨m, hmlt1⟩ ) , (C.b ⟨m, hmlt1⟩ )
    convert C.hgcd ⟨m, hmlt1⟩ hmdvd


/-- Certificate for irreducibility of a polynomial `f` over `(ZMod p)`.
This is the version of `CertificateIrreducibleZMod` in which `hgcd` only ranges through
maximal proper divisors of `n`. This requires a factorization of `n`. -/
structure CertificateIrreducibleZMod' (p n t s : ℕ) [Fact $ Nat.Prime p] [NeZero n] (f : (ZMod p)[X]) where
  m : ℕ
  P : Fin m → ℕ
  exp : Fin m → ℕ
  hneq : ∏ i : Fin m, (P i) ^ (exp i) = n
  hP : ∀ i, Nat.Prime (P i)
  hdeg : f.natDegree = n
  bit : Fin (s + 1) → ℕ
  hbits : FnToNat t bit = p
  h : Fin (n + 1) → (ZMod p)[X]
  g : Fin n → Fin s → (ZMod p)[X]
  h' : Fin n → Fin (s + 1) → (ZMod p)[X]
  hs : ∀ (i : Fin n), h' i s = (h (Fin.castSucc i)) ^ (bit s)
  hz : ∀ (i : Fin n), h' i 0 = h (Fin.succ i)
  hmul : ∀ (i : Fin n) , ∀ (j : Fin s), f * (g i j) =
    (h' i (Fin.succ j)) ^ t * (h i) ^ (bit (Fin.castSucc j) : ℕ) - h' i (Fin.castSucc j)
  a : Fin n → (ZMod p)[X]
  b : Fin n → (ZMod p)[X]
  hhz : h 0 = X
  hhn : h n = X
  hgcd : ∀ (i : Fin m), (a ↑(n / (P i))) * f + (b ↑(n / (P i))) * ((h ↑(n / (P i))) - X) = 1

lemma irreducible_of_CertificateIrreducibleZMod' (p n t s: ℕ)[Fact $ Nat.Prime p] [NeZero n]
    {f : (ZMod p)[X]} (C : CertificateIrreducibleZMod' p n t s f) : Irreducible f := by
  have hd : 0 < f.natDegree := by
    rw [C.hdeg]
    exact Fin.size_pos'
  rw [irreducible_iff_dvd_X_pow_sub_X' f hd, ZMod.card, C.hdeg]
  have aux := certificate_aux' p n t s f C.bit C.hbits C.h C.g C.h' C.hs C.hz C.hmul
  constructor
  · have aux1 := aux n
    rw [C.hhz, C.hhn, Fin.natCast_eq_last, Fin.val_last] at aux1
    exact aux1
  · intro q hq hqdvd
    have hmlt1 : (n / q) < n := by
      rw [← C.hdeg]
      exact Nat.div_lt_self hd (Nat.Prime.one_lt hq)
    have hmlt : (n / q) < n + 1 := Nat.lt_add_right 1 hmlt1
    convert isCoprime_sub_of_isCoprime_sub_dvd_sub (aux ⟨(n / q), hmlt⟩) ?_
    exact (C.hhz).symm
    use (C.a ⟨(n / q), hmlt1⟩ ) , (C.b ⟨(n / q), hmlt1⟩ )
    rw [← C.hneq, Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hq)] at hqdvd
    obtain ⟨i, _, hi2⟩ := hqdvd
    simp_rw [(Nat.prime_dvd_prime_iff_eq hq (C.hP i)).1 (Nat.Prime.dvd_of_dvd_pow hq hi2)]
      at hmlt1 hmlt ⊢
    convert (C.hgcd i)
    · simp only [Fin.val_natCast]
      exact (Nat.mod_eq_of_lt hmlt1).symm
    · simp only [Fin.val_natCast]
      exact (Nat.mod_eq_of_lt hmlt1).symm
    · simp only [Fin.val_natCast]
      exact (Nat.mod_eq_of_lt hmlt).symm

/-- Certificate for irreducibility of a polynomial `f` over `(ZMod p)`.
This is the version of `CertificateIrreducibleZMod` using lists, making the goals decidable.  -/
structure CertificateIrreducibleZModOfList (p n t s : ℕ) [Fact $ Nat.Prime p] [NeZero n]
(l : List (ZMod p)) where
  hlen : l.length = n + 1
  htr : l = l.dropTrailingZeros'
  bit : Fin (s + 1) → ℕ
  hbits : FnToNat t bit = p
  h : Fin (n + 1) → List (ZMod p)
  g : Fin n → Fin s → List (ZMod p)
  h' : Fin n → Fin (s + 1) → List (ZMod p)
  hs : ∀ (i : Fin n), h' i s = h (Fin.castSucc i) ^ (bit s)
  hz : ∀ (i : Fin n), h' i 0 = h (Fin.succ i)
  hmul : ∀ (i : Fin n) , ∀ (j : Fin s), (l * (g i j)).dropTrailingZeros' =
    ((h' i (Fin.succ j)) ^ t * (h i) ^ (bit (Fin.castSucc j) : ℕ) - h' i (Fin.castSucc j)).dropTrailingZeros'
  a : Fin n → List (ZMod p)
  b : Fin n → List (ZMod p)
  hhz : h 0 = [0, 1]
  hhn : h n = [0, 1]
  hgcd : ∀ (m : Fin n),
    ↑m ∣ n → ((a m) * l + (b m) * ((h (Fin.castSucc m)) - [(0 : ZMod p), 1])).dropTrailingZeros' = 1

lemma irreducible_ofList_ofCertificateIrreducibleZModOfList {p n t s : ℕ} [Fact $ Nat.Prime p] [NeZero n]
    {l : List (ZMod p)} (C : CertificateIrreducibleZModOfList p n t s l) : Irreducible (ofList l) := by
   refine irreducible_of_CertificateIrreducibleZMod (p := p) (n := n) (t:= t) (s:= s) ?_
   exact
   { hdeg := by
       rw [← Nat.succ_inj, ← Nat.add_one , natDegree_ofList l , C.hlen]
       exact List.ne_nil_of_length_eq_add_one C.hlen
       rw [dropTrailingZeros_eq_dropTrailingZeros'] ; exact C.htr,
     h := λ i => ofList (C.h i),
     g := λ i => λ j => ofList (C.g i j),
     h' := λ i => λ j => ofList (C.h' i j),
     a := λ i => ofList (C.a i),
     b := λ i => ofList (C.b i),
     bit := C.bit,
     hbits := C.hbits,
     hhz := by
       dsimp
       rw [C.hhz]
       simp only [ofList_cons, ofList_nil, map_zero, map_one, mul_zero, add_zero, mul_one, zero_add],
     hhn := by
       dsimp
       rw [C.hhn]
       simp only [ofList_cons, ofList_nil, map_zero, map_one, mul_zero, add_zero, mul_one, zero_add],
     hs := by intro i ; dsimp ; rw [C.hs i, ofList_pow_eq_pow]
     hz := by intro i ; dsimp ; rw [C.hz i]
     hgcd := by
       intro m hdvd
       dsimp
       have := C.hgcd m hdvd
       apply_fun ofList at this
       erw [← dropTrailingZeros_eq_dropTrailingZeros', ofList_dropTrailingZeros_eq_ofList,
        ofList_one, ofList_addPointwise_eq_add,
       ofList_convolve_eq_mul, ofList_convolve_eq_mul,
       ofList_addPointwise_eq_add, List.neg_eq_neg_one_mul ,  ofList_convolve_eq_mul] at this
       simp only [ofList_cons, ofList_nil, map_neg, map_one, mul_zero, add_zero,  neg_mul,
         one_mul, C_0, zero_add, mul_one] at this
       exact this
     hmul := by
       intro i j
       dsimp
       erw [← ofList_convolve_eq_mul, ← ofList_dropTrailingZeros_eq_ofList,
        dropTrailingZeros_eq_dropTrailingZeros', C.hmul,
       ← dropTrailingZeros_eq_dropTrailingZeros', ofList_dropTrailingZeros_eq_ofList,
       ofList_addPointwise_eq_add, List.neg_eq_neg_one_mul, ofList_convolve_eq_mul, ofList_pow_eq_pow,
       ofList_convolve_eq_mul, ofList_pow_eq_pow]
       simp only [ofList_cons, ofList_nil, map_neg, map_one, mul_zero, add_zero,  neg_mul, one_mul]
       rfl }


/-- Certificate for irreducibility of a polynomial `f` over `(ZMod p)`.
This is the version of `CertificateIrreducibleZMod'` using lists, in which `hgcd` only ranges through
maximal proper divisors of `n`. This requires a factorization of `n`.
(See `CertificateIrreducibleZMod` for explanation). -/
structure CertificateIrreducibleZModOfList' (p n t s : ℕ) [Fact $ Nat.Prime p] [NeZero n]
  (l : List (ZMod p)) where
  m : ℕ
  P : Fin m → ℕ
  exp : Fin m → ℕ
  hneq : ∏ i : Fin m, (P i) ^ (exp i) = n
  hP : ∀ i, Nat.Prime (P i)
  hlen : l.length = n + 1
  htr : l = l.dropTrailingZeros'
  bit : Fin (s + 1) → ℕ
  hbits : FnToNat t bit = p
  h : Fin (n + 1) → List (ZMod p)
  g : Fin n → Fin s → List (ZMod p)
  h' : Fin n → Fin (s + 1) → List (ZMod p)
  hs : ∀ (i : Fin n), h' i s = h (Fin.castSucc i) ^ (bit s)
  hz : ∀ (i : Fin n), h' i 0 = h (Fin.succ i)
  hmul : ∀ (i : Fin n) , ∀ (j : Fin s), (l * (g i j)).dropTrailingZeros' =
    ((h' i (Fin.succ j)) ^ t * (h i) ^ (bit (Fin.castSucc j) : ℕ) - h' i (Fin.castSucc j)).dropTrailingZeros'
  a : Fin n → List (ZMod p)
  b : Fin n → List (ZMod p)
  hhz : h 0 = [0, 1]
  hhn : h n = [0, 1]
  hgcd : ∀ (i : Fin m),
     ((a ↑(n / (P i))) * l + (b ↑(n / (P i))) * ((h ↑(n / (P i))) - [(0 : ZMod p), 1])).dropTrailingZeros' = 1


lemma irreducible_ofList_ofCertificateIrreducibleZModOfList' {p n t s : ℕ} [Fact $ Nat.Prime p]
    [NeZero n] {l : List (ZMod p)} (C : CertificateIrreducibleZModOfList' p n t s l) :
    Irreducible (ofList l) := by
   refine irreducible_of_CertificateIrreducibleZMod' (p := p) (n := n) (t:= t) (s:= s) ?_
   exact
   { P := C.P,
      exp := C.exp,
      hneq := C.hneq,
      hP := C.hP,
      hdeg := by
       rw [← Nat.succ_inj, ← Nat.add_one , natDegree_ofList l , C.hlen]
       exact List.ne_nil_of_length_eq_add_one C.hlen
       rw [dropTrailingZeros_eq_dropTrailingZeros'] ; exact C.htr,
     h := λ i => ofList (C.h i),
     g := λ i => λ j => ofList (C.g i j),
     h' := λ i => λ j => ofList (C.h' i j),
     a := λ i => ofList (C.a i),
     b := λ i => ofList (C.b i),
     bit := C.bit,
     hbits := C.hbits,
     hhz := by
       dsimp
       rw [C.hhz]
       simp only [ofList_cons, ofList_nil, map_zero, map_one, mul_zero, add_zero, mul_one, zero_add],
     hhn := by
       dsimp
       rw [C.hhn]
       simp only [ofList_cons, ofList_nil, map_zero, map_one, mul_zero, add_zero, mul_one, zero_add],
     hs := by intro i ; dsimp ; rw [C.hs i, ofList_pow_eq_pow]
     hz := by intro i ; dsimp ; rw [C.hz i]
     hgcd := by
       intro i
       dsimp
       have := C.hgcd i
       apply_fun ofList at this
       erw [← dropTrailingZeros_eq_dropTrailingZeros', ofList_dropTrailingZeros_eq_ofList,
        ofList_one, ofList_addPointwise_eq_add,
       ofList_convolve_eq_mul, ofList_convolve_eq_mul,
       ofList_addPointwise_eq_add, List.neg_eq_neg_one_mul ,  ofList_convolve_eq_mul] at this
       simp only [ofList_cons, ofList_nil, map_neg, map_one, mul_zero, add_zero,  neg_mul,
        one_mul, C_0, zero_add, mul_one] at this
       exact this
     hmul := by
       intro i j
       dsimp
       erw [← ofList_convolve_eq_mul, ← ofList_dropTrailingZeros_eq_ofList,
        dropTrailingZeros_eq_dropTrailingZeros', C.hmul,
       ← dropTrailingZeros_eq_dropTrailingZeros', ofList_dropTrailingZeros_eq_ofList,
       ofList_addPointwise_eq_add, List.neg_eq_neg_one_mul, ofList_convolve_eq_mul, ofList_pow_eq_pow,
       ofList_convolve_eq_mul, ofList_pow_eq_pow]
       simp only [ofList_cons, ofList_nil, map_neg, map_one, mul_zero, add_zero,  neg_mul, one_mul]
       rfl }


/-- List version of the fact that linear polynomials over a field are irreducible.  -/
lemma irreducible_ofList_of_linear {R : Type u} [Field R] [DecidableEq R] (l : List R)
  (hlen : l.length = 2) (htr : l = l.dropTrailingZeros') : Irreducible (ofList l) := by
  rw [← dropTrailingZeros_eq_dropTrailingZeros'] at htr
  apply Polynomial.irreducible_of_degree_eq_one
  erw [Polynomial.degree_eq_iff_natDegree_eq_of_pos (Nat.zero_lt_succ Nat.zero)]
  apply_fun (fun x => x + 1) using (add_left_injective 1)
  dsimp
  rw [natDegree_ofList _ (List.ne_nil_of_length_pos (Nat.lt_of_sub_eq_succ hlen)) htr, hlen]
