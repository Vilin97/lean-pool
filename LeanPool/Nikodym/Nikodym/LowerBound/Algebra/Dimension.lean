/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib

/-!
# Dimension theory of finitely generated domains over a field

This file implements blueprint node A01 (finite-type dimension and closed-point height), over an
arbitrary field `K`. Throughout, `A` is a domain which is a finitely generated `K`-algebra.

## Main declarations

* `ringKrullDim_eq_of_isIntegral`: an integral extension with injective structure map preserves
  the Krull dimension (`ringKrullDim S = ringKrullDim R`).
* `exists_mvPolynomial_algHom_injective_isIntegral`: Noether normalization together with
  `ringKrullDim A = s`; consequently `exists_ringKrullDim_eq_natCast` and `finiteRingKrullDim`.
* `height_eq_of_isMaximal_mvPolynomial_fin`: maximal ideals of `MvPolynomial (Fin s) K` have
  height `s`.
* `height_eq_ringKrullDim_of_isMaximal`: maximal ideals of `A` have height `ringKrullDim A`.
* `ringKrullDim_quotient_add_one_of_mem_minimalPrimes`: for `f ≠ 0` and `P` a minimal prime over
  `(f)`, `ringKrullDim (A ⧸ P) + 1 = ringKrullDim A`.
* `ringKrullDim_quotient_add_one_le_of_lt`: a strictly larger prime has strictly smaller quotient
  dimension.
* Section `PolynomialQuotient`: the same statements packaged for `MvPolynomial (Fin d) K ⧸ I`,
  `I` prime (`height_map_eq_ringKrullDim_of_isMaximal`,
  `ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup`, `finite_minimalPrimes_sup`,
  `exists_minimalPrimes_le`).
-/

namespace Nikodym.LowerBound

open Ideal

section IntegralExtension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Blueprint A01 (1): `comap` along an integral extension is strictly monotone on primes. -/
theorem primeSpectrum_comap_strictMono_of_isIntegral [Algebra.IsIntegral R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro P Q hPQ
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hPQ ⊢
  exact Ideal.IsIntegral.comap_lt_comap hPQ

/-- Blueprint A01 (1): the Krull dimension does not go up along an integral extension. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono _ primeSpectrum_comap_strictMono_of_isIntegral

/-- Blueprint A01 (1), going up along chains: a strict chain of primes in `R` lifts to a strict
chain of the same length in an integral extension `S` (with injective structure map), whose last
element lies over the last element of the original chain. -/
theorem exists_ltSeries_length_eq_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S]
    (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S), L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  induction l using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨Q, hQ, hQx⟩ := (Ideal.nonempty_primesOver (S := S) x.asIdeal).some
    refine ⟨RelSeries.singleton _ ⟨Q, hQ⟩, by simp, ?_⟩
    ext1
    simpa [PrimeSpectrum.comap_asIdeal] using hQx.over.symm
  | snoc l x hx ih =>
    obtain ⟨L, hlen, hlast⟩ := ih
    have hlt : l.last.asIdeal < x.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hx
    have hle : L.last.asIdeal.comap (algebraMap R S) ≤ x.asIdeal := by
      rw [← PrimeSpectrum.comap_asIdeal, hlast]
      exact hlt.le
    obtain ⟨Q, hLQ, hQ, hQx⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime x.asIdeal L.last.asIdeal hle
    have hLQ' : L.last < ⟨Q, hQ⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine lt_of_le_of_ne hLQ fun h ↦ hlt.ne ?_
      have h' := congrArg (Ideal.comap (algebraMap R S)) h
      rwa [← PrimeSpectrum.comap_asIdeal, hlast, hQx] at h'
    refine ⟨L.snoc ⟨Q, hQ⟩ hLQ', by simp [hlen], ?_⟩
    ext1
    simpa [PrimeSpectrum.comap_asIdeal] using hQx

/-- Blueprint A01 (1): the Krull dimension does not go down along an integral extension with
injective structure map (lying over + going up). -/
theorem ringKrullDim_ge_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim R ≤ ringKrullDim S := by
  unfold ringKrullDim Order.krullDim
  refine iSup_le fun l ↦ ?_
  obtain ⟨L, hL, -⟩ := exists_ltSeries_length_eq_of_isIntegral (S := S) l
  exact le_iSup_of_le L (by rw [hL])

/-- Blueprint A01 (1): **integral extensions preserve Krull dimension.** -/
theorem ringKrullDim_eq_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R :=
  le_antisymm ringKrullDim_le_of_isIntegral ringKrullDim_ge_of_isIntegral

/-- Blueprint A01 (4), auxiliary: the extension `(𝔪 ∩ R) S` of the contraction of an ideal `𝔪`
lies over `𝔪 ∩ R`. -/
theorem map_under_liesOver_under (𝔪 : Ideal S) :
    ((𝔪.under R).map (algebraMap R S)).LiesOver (𝔪.under R) :=
  ⟨le_antisymm Ideal.le_comap_map (Ideal.comap_mono (Ideal.map_le_iff_le_comap.mpr le_rfl))⟩

end IntegralExtension

section MvPolynomial

variable (K : Type*) [Field K]

/-- Blueprint A01 (2): the polynomial ring in `s` variables over a field has dimension `s`. -/
theorem ringKrullDim_mvPolynomial_fin_eq (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) K) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- Blueprint A01 (3): **maximal ideals of a polynomial ring over a field have full height.** -/
theorem height_eq_of_isMaximal_mvPolynomial_fin :
    ∀ (s : ℕ) (𝔫 : Ideal (MvPolynomial (Fin s) K)), 𝔫.IsMaximal → 𝔫.height = s
  | 0, 𝔫, h => by
    haveI := h
    let e := (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingEquiv
    have hmax : (𝔫.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    rcases Ideal.eq_bot_or_top (𝔫.map e) with h0 | h0
    · rw [← e.height_map 𝔫, h0, Ideal.height_bot]
      simp
    · exact absurd h0 hmax.ne_top
  | s + 1, 𝔫, h => by
    haveI := h
    let e := (MvPolynomial.finSuccEquiv K s).toRingEquiv
    haveI : (𝔫.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hmax : ((𝔫.map e).under (MvPolynomial (Fin s) K)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing (𝔫.map e)
    haveI := Ideal.over_under (A := MvPolynomial (Fin s) K) (𝔫.map e)
    rw [← e.height_map 𝔫, Polynomial.height_eq_height_add_one ((𝔫.map e).under _) (𝔫.map e),
      height_eq_of_isMaximal_mvPolynomial_fin s _ hmax]
    push_cast
    rfl

end MvPolynomial

section AffineDomain

variable (K : Type*) [Field K] {A : Type*} [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra.FiniteType K A]

variable (A) in
/-- Blueprint A01 (2): **Noether normalization gives the dimension.** There is an injective
`K`-algebra map from a polynomial ring in `s` variables into `A`, over which `A` is integral, and
`s` is the Krull dimension of `A`. -/
theorem exists_mvPolynomial_algHom_injective_isIntegral :
    ∃ (s : ℕ) (g : MvPolynomial (Fin s) K →ₐ[K] A), Function.Injective g ∧
      (g : MvPolynomial (Fin s) K →+* A).IsIntegral ∧ ringKrullDim A = s := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  refine ⟨s, g, hinj, hint, ?_⟩
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  rw [ringKrullDim_eq_of_isIntegral (R := MvPolynomial (Fin s) K),
    ringKrullDim_mvPolynomial_fin_eq]

include K in
/-- Blueprint A01 (2): the Krull dimension of a finitely generated domain over a field is a natural
number. -/
theorem exists_ringKrullDim_eq_natCast : ∃ n : ℕ, ringKrullDim A = n := by
  obtain ⟨s, -, -, -, hs⟩ := exists_mvPolynomial_algHom_injective_isIntegral K A
  exact ⟨s, hs⟩

include K in
/-- Blueprint A01 (2): a finitely generated domain over a field has finite Krull dimension. -/
theorem finiteRingKrullDim : FiniteRingKrullDim A := by
  obtain ⟨n, hn⟩ := exists_ringKrullDim_eq_natCast K (A := A)
  rw [finiteRingKrullDim_iff_ne_bot_and_top, hn, ← WithBot.coe_natCast, ← WithBot.coe_top]
  exact ⟨WithBot.coe_ne_bot, fun h ↦ ENat.coe_ne_top n (WithBot.coe_inj.mp h)⟩

end AffineDomain

section Normalized

/-! In this section `A` carries a fixed Noether normalization: an integral, injective algebra
structure over the polynomial ring `MvPolynomial (Fin s) K`. -/

variable (K : Type*) [Field K] {A : Type*} [CommRing A] [IsDomain A] {s : ℕ}
  [Algebra (MvPolynomial (Fin s) K) A] [Algebra.IsIntegral (MvPolynomial (Fin s) K) A]
  [FaithfulSMul (MvPolynomial (Fin s) K) A] [IsNoetherianRing A]

include K in
/-- Blueprint A01 (4), auxiliary: over a fixed Noether normalization in `s` variables, every
maximal ideal of `A` has height `s`. -/
private theorem height_eq_of_isMaximal_aux (𝔪 : Ideal A) [𝔪.IsMaximal] : 𝔪.height = s := by
  set S := MvPolynomial (Fin s) K
  set 𝔫 := 𝔪.under S with h𝔫
  haveI : 𝔫.IsMaximal := Ideal.IsMaximal.under S 𝔪
  haveI := Ideal.over_under (A := S) 𝔪
  haveI : (𝔫.map (algebraMap S A)).LiesOver 𝔫 := map_under_liesOver_under 𝔪
  have hfib : (𝔪.map (Ideal.Quotient.mk (𝔫.map (algebraMap S A)))).height = 0 := by
    have hdim : ringKrullDim (A ⧸ 𝔫.map (algebraMap S A)) ≤ 0 := by
      calc ringKrullDim (A ⧸ 𝔫.map (algebraMap S A))
          ≤ ringKrullDim (S ⧸ 𝔫) := ringKrullDim_le_of_isIntegral
        _ = 0 := ringKrullDim_eq_zero_of_isField
            ((Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔫).mp inferInstance)
    have h := (Ideal.height_le_ringKrullDim_of_isPrime
      (I := 𝔪.map (Ideal.Quotient.mk (𝔫.map (algebraMap S A))))).trans hdim
    rw [← WithBot.coe_zero, WithBot.coe_le_coe] at h
    exact nonpos_iff_eq_zero.mp h
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔫 𝔪, hfib, add_zero,
    height_eq_of_isMaximal_mvPolynomial_fin K s 𝔫 inferInstance]

include K in
/-- Blueprint A01 (5), auxiliary: over a fixed Noether normalization in `s` variables, a prime of
height one in `A` has quotient of dimension `s - 1`. -/
private theorem ringKrullDim_quotient_add_one_aux (P : Ideal A) [P.IsPrime] (hP : P.height = 1) :
    ringKrullDim (A ⧸ P) + 1 = s := by
  set S := MvPolynomial (Fin s) K
  set Q := P.under S with hQ
  haveI := Ideal.over_under (A := S) P
  have hQbot : Q ≠ ⊥ := Ideal.under_ne_bot S (Ideal.ne_bot_of_height_eq_one hP)
  have hQ1 : Q.height = 1 := by
    apply le_antisymm
    · have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown Q P
      rw [hP] at h
      exact h ▸ le_self_add
    · exact Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr
        (by rwa [Ne, Ideal.height_eq_zero_iff_eq_bot]))
  obtain ⟨p, hpQ, hp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot (inferInstance : Q.IsPrime) hQbot
  have hQp : Q = Ideal.span {p} := Ideal.eq_span_singleton_of_height_eq_one hQ1 hpQ hp
  have h1 : ringKrullDim (A ⧸ P) = ringKrullDim (S ⧸ Q) := ringKrullDim_eq_of_isIntegral
  have h2 : ringKrullDim (S ⧸ Q) + 1 ≤ s := by
    rw [hQp, ← ringKrullDim_mvPolynomial_fin_eq K s]
    exact ringKrullDim_quotient_succ_le_of_nonZeroDivisor
      (mem_nonZeroDivisors_of_ne_zero hp.ne_zero)
  have h3 : (s : WithBot ℕ∞) ≤ ringKrullDim (S ⧸ Q) + 1 := by
    obtain ⟨𝔫, h𝔫, hQ𝔫⟩ := Q.exists_le_maximal Ideal.IsPrime.ne_top'
    haveI := h𝔫
    have h := Ideal.height_le_ringKrullDim_quotient_add_one (p := 𝔫) (r := p) (hQ𝔫 hpQ)
    rwa [height_eq_of_isMaximal_mvPolynomial_fin K s 𝔫 h𝔫, WithBot.coe_natCast, ← hQp] at h
  rw [h1]
  exact le_antisymm h2 h3

end Normalized

section AffineDomain

variable (K : Type*) [Field K] {A : Type*} [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra.FiniteType K A]

include K in
/-- Blueprint A01 (4): **maximal ideals of an affine domain have height equal to the
dimension.** -/
theorem height_eq_ringKrullDim_of_isMaximal (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) :
    (𝔪.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨s, g, hinj, hint, hs⟩ := exists_mvPolynomial_algHom_injective_isIntegral K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  haveI := h𝔪
  rw [height_eq_of_isMaximal_aux K (s := s) 𝔪, hs]
  exact WithBot.coe_natCast s

include K in
/-- Blueprint A01 (4): `ℕ∞`-valued form of `height_eq_ringKrullDim_of_isMaximal`. -/
theorem height_eq_of_isMaximal_of_ringKrullDim_eq {n : ℕ} (hn : ringKrullDim A = n)
    (𝔪 : Ideal A) (h𝔪 : 𝔪.IsMaximal) : 𝔪.height = n := by
  have h := height_eq_ringKrullDim_of_isMaximal K 𝔪 h𝔪
  rw [hn, ← WithBot.coe_natCast] at h
  exact WithBot.coe_inj.mp h

include K in
/-- Blueprint A01 (5): **a minimal prime over a nonzero element drops the dimension by exactly
one.** -/
theorem ringKrullDim_quotient_add_one_of_mem_minimalPrimes {f : A} (hf : f ≠ 0) {P : Ideal A}
    (hP : P ∈ (Ideal.span {f}).minimalPrimes) :
    ringKrullDim (A ⧸ P) + 1 = ringKrullDim A := by
  obtain ⟨s, g, hinj, hint, hs⟩ := exists_mvPolynomial_algHom_injective_isIntegral K A
  letI : Algebra (MvPolynomial (Fin s) K) A := g.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) A := ⟨hint⟩
  haveI : FaithfulSMul (MvPolynomial (Fin s) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  haveI : P.IsPrime := hP.1.1
  have hfP : f ∈ P := hP.1.2 (Ideal.mem_span_singleton_self f)
  have hPbot : P ≠ ⊥ := fun h ↦ hf ((Submodule.mem_bot A).mp (h ▸ hfP))
  have hP1 : P.height = 1 := by
    haveI : (Ideal.span {f}).IsPrincipal := ⟨⟨f, rfl⟩⟩
    apply le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)
    exact Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr
      (by rwa [Ne, Ideal.height_eq_zero_iff_eq_bot]))
  rw [hs]
  exact ringKrullDim_quotient_add_one_aux K P hP1

end AffineDomain

section StrictInclusion

variable {R : Type*} [CommRing R]

/-- Blueprint A01: **strict inclusion of primes strictly decreases the quotient dimension**
(in any commutative ring, for `I` prime). -/
theorem ringKrullDim_quotient_add_one_le_of_lt {I J : Ideal R} [I.IsPrime] (h : I < J) :
    ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ I) := by
  obtain ⟨x, hxJ, hxI⟩ := SetLike.exists_of_lt h
  have hx : Ideal.Quotient.mk I x ∈ nonZeroDivisors (R ⧸ I) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE h.le).symm]
  refine ringKrullDim_succ_le_of_surjective _ Ideal.Quotient.mk_surjective hx ?_
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ hxJ

end StrictInclusion

section PolynomialQuotient

/-! Blueprint A01 (6): the package for prime quotients of the polynomial ring
`MvPolynomial (Fin d) K`, in the form consumed by later nodes. Note that
`MvPolynomial (Fin d) K ⧸ I` is a domain (`Ideal.Quotient.isDomain`) and of finite type over `K`
(`Algebra.FiniteType.quotient`) by Mathlib instances, so all results of the previous sections
apply to it. -/

variable (K : Type*) [Field K] {d : ℕ} (I : Ideal (MvPolynomial (Fin d) K)) [I.IsPrime]

/-- Blueprint A01 (6): the quotient of a polynomial ring by a prime is a domain. -/
theorem isDomain_quotient : IsDomain (MvPolynomial (Fin d) K ⧸ I) := inferInstance

omit [I.IsPrime] in
/-- Blueprint A01 (6): the quotient of a polynomial ring by an ideal is of finite type. -/
theorem finiteType_quotient : Algebra.FiniteType K (MvPolynomial (Fin d) K ⧸ I) := inferInstance

/-- Blueprint A01 (6): the dimension of a prime quotient of the polynomial ring is a natural
number. -/
theorem exists_ringKrullDim_quotient_eq_natCast :
    ∃ n : ℕ, ringKrullDim (MvPolynomial (Fin d) K ⧸ I) = n :=
  exists_ringKrullDim_eq_natCast K

/-- Blueprint A01 (6): **closed points have full height.** For a maximal ideal `𝔪 ⊇ I` of the
polynomial ring, the height of `𝔪 / I` in `P ⧸ I` equals the dimension of `P ⧸ I`. -/
theorem height_map_eq_ringKrullDim_of_isMaximal {𝔪 : Ideal (MvPolynomial (Fin d) K)}
    (h𝔪 : 𝔪.IsMaximal) (hI : I ≤ 𝔪) :
    ((𝔪.map (Ideal.Quotient.mk I)).height : WithBot ℕ∞) =
      ringKrullDim (MvPolynomial (Fin d) K ⧸ I) := by
  haveI := h𝔪
  exact height_eq_ringKrullDim_of_isMaximal K _
    (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker]))

/-- Blueprint A01 (6): **cutting by a polynomial not in `I` drops the dimension by one.** For
`g ∉ I` and `J` a minimal prime over `I + (g)`, `dim (P ⧸ J) + 1 = dim (P ⧸ I)`. -/
theorem ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup {g : MvPolynomial (Fin d) K}
    (hg : g ∉ I) {J : Ideal (MvPolynomial (Fin d) K)}
    (hJ : J ∈ (I ⊔ Ideal.span {g}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin d) K ⧸ J) + 1 = ringKrullDim (MvPolynomial (Fin d) K ⧸ I) := by
  have hIJ : I ≤ J := le_sup_left.trans hJ.1.2
  have hf : Ideal.Quotient.mk I g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hJ' : J.map (Ideal.Quotient.mk I) ∈ (Ideal.span {Ideal.Quotient.mk I g}).minimalPrimes := by
    have h := Ideal.minimalPrimes_map_of_surjective (Ideal.Quotient.mk_surjective (I := I))
      (Ideal.span {g})
    rw [Ideal.map_span, Set.image_singleton, Ideal.mk_ker, sup_comm] at h
    rw [h]
    exact ⟨J, hJ, rfl⟩
  have h := ringKrullDim_quotient_add_one_of_mem_minimalPrimes K hf hJ'
  rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIJ)] at h

/-- Blueprint A01 (6): a strictly larger prime has strictly smaller quotient dimension. -/
theorem ringKrullDim_quotient_add_one_le_of_lt' {J : Ideal (MvPolynomial (Fin d) K)} (h : I < J) :
    ringKrullDim (MvPolynomial (Fin d) K ⧸ J) + 1 ≤ ringKrullDim (MvPolynomial (Fin d) K ⧸ I) :=
  ringKrullDim_quotient_add_one_le_of_lt h

omit [I.IsPrime] in
/-- Blueprint A01 (6): an ideal of the polynomial ring has finitely many minimal primes. -/
theorem finite_minimalPrimes : I.minimalPrimes.Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing _ I

omit [I.IsPrime] in
/-- Blueprint A01 (6): `I + (g)` has finitely many minimal primes. -/
theorem finite_minimalPrimes_sup (g : MvPolynomial (Fin d) K) :
    (I ⊔ Ideal.span {g}).minimalPrimes.Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing _ _

omit [I.IsPrime] in
/-- Blueprint A01 (6): every prime containing an ideal contains a minimal prime over it. -/
theorem exists_minimalPrimes_le {Q : Ideal (MvPolynomial (Fin d) K)} [Q.IsPrime] (h : I ≤ Q) :
    ∃ p ∈ I.minimalPrimes, p ≤ Q :=
  Ideal.exists_minimalPrimes_le h

end PolynomialQuotient

end Nikodym.LowerBound

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
