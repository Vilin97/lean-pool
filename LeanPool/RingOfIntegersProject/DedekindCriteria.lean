/-
Copyright (c) 2026 Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best, Nirvana Coppola, Sander R. Dahmen
-/

import Mathlib.NumberTheory.NumberField.Basic
import LeanPool.RingOfIntegersProject.AlgebraAuxiliaryLemmas
import LeanPool.RingOfIntegersProject.PolynomialBasics
import LeanPool.RingOfIntegersProject.PolynomialRadical
import LeanPool.RingOfIntegersProject.QuotientModules
import LeanPool.RingOfIntegersProject.LinearAlgebraAuxiliaryLemmas

/-!
# Phost-Zassenhaus and Dedekind criterion

We prove a version of the Pohst-Zassenhaus theorem and Dedekind criterion.

## Main definitions
- `piMaximal` : a submodule `N` is `π`-maximal if `π` does not divide the index of N in M.
- `satisfiesDedekindCriterion` : the conditions to satisfy Dedekind criterion.

## Main results
- `order_piMaximal_of_order_eq_multiplierRing` : the Pohst-Zassenhaus theorem.
  If a subalgebra `O` is equal to the  multiplier ring of the radical of `π`,
  then `O` is `π`-maximal.
- `piMaximal_of_satisfiesDedekindCriteria` : if `T` satisfies Dedekind criterion at
  the prime `π`, then the subalgebra `R[X]/(T)` is `π`-maximal.   -/


open BigOperators Polynomial

---------------------------------------------------------------------------------------
/- Definition and results on piMaximality · -/

/-- If `P(0)` is false and there is a natural number `m` such that `P(m)` is true,
then there exists `n` such that `P(n)` is false and `P(n + 1)` is true·  -/
lemma exists_min_nat_prop_true (m : ℕ) (P : ℕ → Prop) (h1 : ¬ P 0) (h2 : P m) :
    ∃ (n : ℕ), ¬ P n ∧ P (n + 1) := by
  by_contra h
  push_neg at h
  have : ∀ (n : ℕ) , ¬ P n := by
    intro n
    induction n
    · exact h1
    · case _ n hn => exact h n hn
  exact this m h2

/-- If `M` is an `R`-module, and `N` is an `R`-Submodule of `M`, then `N` is `π`-maximal
  if `π` does not divide `[M : N]`·  -/
def piMaximal {R M : Type _} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (π : R)
    (N : Submodule R M) : Prop := ¬ (π ∣ Submodule.indexPID N)

lemma piMaximal_def {R M : Type _} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] (π : R)
    (N : Submodule R M) : piMaximal π N  ↔  ¬ (π ∣ Submodule.indexPID N) := Iff.rfl

/-- If `N` is `π`-maximal for every prime `π`, then `N` = ⊤· -/
lemma eq_top_of_piMaximal_at_all_primes {R M : Type _} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (hp : ∃ (q : R), Prime q)
    (N : Submodule R M) (hpm : ∀ (π : R), Prime π → piMaximal π N ) : N = ⊤ := by
  apply Submodule.eq_top_of_index_isUnit
  obtain ⟨q, hq⟩ := hp
  by_contra h
  if hz : Submodule.indexPID N = 0 then
  · refine hpm q hq ?_
    rw [hz]
    exact dvd_zero q
  else
  · obtain ⟨π, hp⟩ := UniqueFactorizationMonoid.exists_mem_factors hz h
    exact hpm π (UniqueFactorizationMonoid.prime_of_factor _ hp  )
      (UniqueFactorizationMonoid.dvd_of_mem_factors hp)

lemma piMaximal_primes_iff_piMaximal_natPrimes  [AddCommGroup M][Module.Free ℤ M] [Module.Finite ℤ M]
    (N : Submodule ℤ M) :
    ( ∀ (p : ℕ ), Nat.Prime p → piMaximal ↑p N ) ↔
       ( ∀ (π : ℤ ), Prime π → piMaximal π N ) := by
  constructor
  · intro hpn π hpi
    rw [Int.prime_iff_natAbs_prime] at hpi
    have := hpn (Int.natAbs π) hpi
    rw [piMaximal_def] at this ⊢
    by_contra h
    exact this (Int.natAbs_dvd.2 h)
  · intro hpz p hp
    refine hpz p ?_
    exact Nat.prime_iff_prime_int.mp hp

lemma eq_top_of_piMaximal_at_all_primes_int [AddCommGroup M][Module.Free ℤ M] [Module.Finite ℤ M]
  (N : Submodule ℤ M) (hpm : ∀ (p : ℕ ), Nat.Prime p → piMaximal ↑p N ) : N = ⊤ := by
    apply eq_top_of_piMaximal_at_all_primes ?_ N ?_
    · exact ⟨2, Int.prime_two⟩
    · exact (piMaximal_primes_iff_piMaximal_natPrimes _).1 hpm

/-- If `N₁ ≤ N₂` and `N₁` is `π`-maximal, then `N₂` is also `π`-maximal· -/
lemma piMaximal_of_piMaximal_lt {R M : Type _} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
     {N₁ N₂ : Submodule R M } (hlt : N₁ ≤ N₂) (π : R) : piMaximal π N₁ → piMaximal π N₂ := by
  unfold piMaximal
  contrapose
  rw [not_not, not_not]
  intro h
  exact dvd_trans h (Submodule.indexPID_dvd_of_le N₁ N₂ hlt)

/-- If `O` and `Om` are `R`-subalgebras of `M` with `O` ≤ `Om`, and
  `O` is `π`-maximal with respect to `Om`for every prime `π`, then `O` and `Om` are equal· -/
lemma eq_of_piMaximal_at_all_primes [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing M] [Algebra R M] (O Om : Subalgebra R M) (hm : O ≤ Om) [Module.Free R Om]
    [Module.Finite R Om] (hp : ∃ (q : R), Prime q)
    (hq : ∀ (π : R), Prime π → piMaximal π (Subalgebra.toSubmodule ((Subalgebra.inclusion hm).range))) :
    O = Om := by
  have : (Subalgebra.toSubmodule ((Subalgebra.inclusion hm).range)) = ⊤ :=
    eq_top_of_piMaximal_at_all_primes hp _ hq
  simp only [Algebra.toSubmodule_eq_top] at this
  refine le_antisymm hm ?_
  intros x hx
  have htop : (⟨x ,hx⟩ : Om) ∈ (⊤ : Subalgebra R Om) := Algebra.mem_top
  rw [← this] at htop
  obtain ⟨⟨y, hy⟩ , hyh⟩ := htop
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Subalgebra.inclusion_mk, Subtype.mk_eq_mk] at hyh
  rwa [← hyh]

lemma eq_of_piMaximal_at_all_primes_int [CommRing M] (O Om : Subalgebra ℤ M) (hm : O ≤ Om)
   [Module.Free ℤ Om] [Module.Finite ℤ Om]
   (hq : ∀ (p : ℕ), Nat.Prime p → piMaximal ↑p (Subalgebra.toSubmodule ((Subalgebra.inclusion hm).range))) :
    O = Om := by
    apply eq_of_piMaximal_at_all_primes O Om hm ?_ ?_
    · exact ⟨2, Int.prime_two⟩
    · exact (piMaximal_primes_iff_piMaximal_natPrimes _).1 hq

--------------------------------------------------------------------------------------------

section PartI

 /- `K` is the ambient space (say, for example, a number field) which has an
 `R`-algebra structure· Given an `R`-Subalgebras `O` and `Om` in `K`
  with `O ⊆ Om`, we define
  1·  The multiplier ring of an `O`-ideal.
  2·  The over ring of `O` in `Om` with respect to an element `α ∈ R `. -/


variable {R : Type _} [CommRing R]
variable {K : Type _} [CommRing K]  [Algebra R K]

/-- If `I` is an `O`-ideal, then the multiplier ring of `I` is an `R`-subalgebra
consisting of all the elements `x` in `K` such that `x I ⊆ I `· -/
def multiplierRing {O : Subalgebra R K} (I : Ideal O) : Subalgebra R K where
  carrier := {(x : K)  | ∀ (i : O), i ∈ I → ( ∃ (j : O), j ∈ I ∧ i * x = j )}
  mul_mem':= by
    intros a b ha hb i hi
    obtain ⟨ j, hj1, hj2 ⟩ := ha i hi
    obtain ⟨ k, hk1, hk2 ⟩ := hb j hj1
    use k
    constructor
    · exact hk1
    · rw [← mul_assoc ,hj2, hk2]
  one_mem' := by
    intros i hi
    use i
    constructor
    · exact hi
    · refine mul_one _
  add_mem' := by
    intros a b ha hb i hi
    obtain ⟨ j, hj1, hj2 ⟩ := ha i hi
    obtain ⟨ k, hk1, hk2 ⟩ := hb i hi
    use ( j+k )
    constructor
    · exact Ideal.add_mem I hj1 hk1
    · rw [mul_add, hj2, hk2]
      rfl
  zero_mem' := by
    intros i _
    use 0
    constructor
    · refine Ideal.zero_mem I
    · simp only [mul_zero]
      rfl
  algebraMap_mem' := by
    intros r i hi
    use (i * (algebraMap _ O r))
    constructor
    · refine (Ideal.mul_mem_right _ I hi)
    · have : (↑(algebraMap _ O r) : K) = algebraMap R K r := rfl
      rw [← this]
      rfl

lemma multiplierRing_mem {O : Subalgebra R K} (I : Ideal O) (x : K) :
    x ∈ multiplierRing I ↔
      ∀ (i : O), i ∈ I → (∃ (j : O), j ∈ I ∧ ↑i * x = j ) := by rfl


/-- `O` is contained in the multiplier ring of an `O`-ideal· -/
lemma subalgebra_le_multiplierRing {O : Subalgebra R K} (I : Ideal O) :
  O ≤ multiplierRing I := by
  intros x hx i hi
  refine ⟨⟨i * x, ?_⟩, ?_⟩
  refine mul_mem  (SetLike.coe_mem i) hx
  constructor
  have : (⟨↑i * x, id (mul_mem (SetLike.coe_mem i) hx)⟩ : O )= i * ( ⟨ x,hx ⟩ : O) := rfl
  rw [this]
  refine Ideal.mul_mem_right ⟨ x, hx ⟩ I hi
  rfl

/-- The over ring of `O` in `Om` with respect to `α ∈ R` is an
`R`-subalgebra consisting of the elements `x` in `Om` such that
   `α ^ j • x` is in `O` for some nonnegative integer `j`· -/
def overRing {O : Subalgebra R K} (α : R) {Om : Subalgebra R K} (_ : O ≤ Om) : Subalgebra R K where
  carrier := fun (x : K) => x ∈ Om ∧ ∃ (j : ℕ) , α ^ j • x ∈ O
  mul_mem' := by
    rintro a b ⟨ ha, ⟨ j,hj ⟩ ⟩ ⟨ hb, ⟨ j',hj' ⟩ ⟩
    constructor
    exact Om.mul_mem ha hb
    use ( j + j' )
    rw [pow_add, Algebra.smul_def, map_mul]
    have : (((algebraMap R K) (α ^ j)) * a) * (((algebraMap R K) (α ^ j'))  * b) =
      ((algebraMap R K) (α ^ j)) * ((algebraMap R K) (α ^ j'))  * (a * b) := by ring
    rw [← this]
    rw [Algebra.smul_def] at hj hj'
    exact O.mul_mem hj hj'
  one_mem' := by
    constructor
    exact Subalgebra.one_mem Om
    use 0
    rw [pow_zero, one_smul]
    exact Subalgebra.one_mem O
  add_mem' := by
    rintro a b ⟨ ha, ⟨ j,hj ⟩ ⟩ ⟨ hb, ⟨j',hj'⟩ ⟩
    constructor
    · exact Om.add_mem ha hb
    · use ( j + j' )
      have : (algebraMap R K α ^ (j + j')) * (a + b) =
        (algebraMap R K (α^ j')) * ((algebraMap R K (α ^ j)) * a) +
          (algebraMap R K (α ^ j)) * ((algebraMap R K (α ^ j'))* b) := by
        rw [pow_add, map_pow, map_pow, mul_add]
        ring
      rw [Algebra.smul_def, map_pow, this, ← Algebra.smul_def,
        ← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def]
      refine O.add_mem (O.smul_mem hj _) (O.smul_mem hj' _)
  zero_mem' := by
    constructor
    exact Subalgebra.zero_mem Om
    use 1
    rw [smul_zero]
    exact Subalgebra.zero_mem O
  algebraMap_mem' := by
    intro s
    constructor
    · exact Om.algebraMap_mem s
    · use 0
      ring_nf
      rw [one_smul]
      exact O.algebraMap_mem s

lemma overRing_mem {O : Subalgebra R K} (α : R) {Om: Subalgebra R K}
    (hm : O ≤ Om) (x : K) :
    x ∈ overRing α hm ↔ x ∈ Om ∧ ∃ (j : ℕ) , α  ^ j • x ∈ O := Iff.rfl

/-- The over-ring of `O` in `Om` with respect to `α`spo is contained in `Om`·   -/
lemma overRing_le {O : Subalgebra R K} (α : R) {Om: Subalgebra R K}
    (hm : O ≤ Om): overRing α hm ≤ Om :=
  λ (x : K) => (λ (hx : x ∈ overRing α hm) => ((overRing_mem α hm x).1 hx).1)

/-- The over-ring of `O` in `Om` with respect to `α` contains `O`· -/
 lemma subalgebra_le_overRing {O : Subalgebra R K} (α : R) {Om : Subalgebra R K}
    (hm : O ≤ Om): O ≤ overRing α hm :=
  λ x hx => ⟨hm hx, ⟨0, (by simp only [*, pow_zero, one_mul, one_smul])⟩ ⟩

variable [IsDomain R] [IsPrincipalIdealRing R]
variable {ι : Type _ } [Fintype ι]

/-- If `Oₐ` is the over ring of `O` in `Om` with respect to `α`, and `Om` is finite
 and free as an `R`-module, then there is `r ∈ ℕ` such that `α ^ r Oₐ ⊆ O`· -/
 lemma pow_mul_overRing_in_order {O : Subalgebra R K} (α : R) {Om : Subalgebra R K}
    (hm : O ≤ Om) (hb : Basis ι R Om) :
    ∃ (r : ℕ), ∀ (x : K), x ∈ overRing α hm → α  ^ r • x ∈ O := by
  have hm': Subalgebra.toSubmodule (overRing α hm) ≤ Subalgebra.toSubmodule Om := by
    simp only [overRing_le , OrderEmbedding.le_iff_le]
  obtain ⟨ k, bk ⟩ := Submodule.basisOfPidOfLE hm' hb
  have aux : ∀ (i : Fin k), ∃ (n : ℕ), (α ^ n) • (bk i : K) ∈ O := by
    intro i
    have : (bk i : K) ∈ overRing α hm := by
     exact SetLike.coe_mem _
    use (this.2).choose
    exact (this.2).choose_spec
  have aux2 : ∀ (i : Fin k), ∀ (m : ℕ), (aux i).choose ≤ m →  (α ^ m) • (bk i : K) ∈ O := by
    intros i m hlem
    set s := m - (aux i).choose with hs
    have hmeq : m = s + (aux i).choose := by
      rw [hs, Nat.sub_add_cancel]
      exact hlem
    rw [hmeq, pow_add, mul_smul]
    refine O.smul_mem (aux i).choose_spec _
  let f : (Fin k) → ℕ := λ (i : Fin k) => (aux i).choose
  let r:= ∑ i in @Fintype.elems (Fin k) _, f (i : Fin k)
  have hmb: ∀ (i : Fin k), f i ≤ r := by
    intro i
    refine Finset.single_le_sum ?_ ?_
    · intros j _
      simp only [zero_le']
    refine Fintype.complete _
  refine ⟨r, ?_⟩
  intros x hx
  have := Basis.sum_repr bk (⟨x,hx⟩: overRing α hm)
  rw [Subtype.ext_iff_val] at this
  simp only [AddSubmonoidClass.coe_finset_sum, SetLike.val_smul] at this
  rw [← this, Finset.smul_sum]
  refine O.sum_mem ?_
  · intro i _
    rw [← mul_smul, mul_comm, mul_smul]
    refine O.smul_mem (aux2 i r ?_) ?_
    exact hmb i

-- Shortcut instance that avoids a slow path via `IsScalarTower O O O → SMul O O`
instance : Pow (Ideal R) ℕ := inferInstanceAs (Pow (Submodule R R) ℕ)

/-- If `Oₐ` is the over ring of `O` in `Om` with respect to `α`, `Iₐ ` is the radical of `αO`,
 and `Om` is a finite free `R`-module, then there is `n ∈ ℕ` such that `Oₐ ⬝ (Iₐ ^ n) ⊆ O `.-/
lemma overRing_mul_radical_pow_in_order {O : Subalgebra R K} {Om : Subalgebra R K}
    (α : R) (hm : O ≤ Om) (hb : Basis ι R Om)  :
      ∃ (n : ℕ), ∀ (x : K) (y : O), x ∈ overRing α hm →
      y ∈ Ideal.radical (Ideal.span {(algebraMap R O α)}) ^ n → x * y ∈ O := by
  haveI instNR : IsNoetherianRing O := subalgebraIsNoetherianRingOfLeFreeFiniteSubalgebra O Om hm hb
  have hfg : (Ideal.span ({(algebraMap R O α)}: Set O)).radical.FG :=
    (isNoetherianRing_iff_ideal_fg O).mp instNR (Ideal.span {(algebraMap R O α)}).radical
  choose m hmm using Ideal.exists_radical_pow_le_of_fg (Ideal.span ({(algebraMap R O α)}: Set O)) hfg
  choose r hr using pow_mul_overRing_in_order α hm hb
  use (m * r)
  intros x y hx hy
  have aux :  ∃ (z : K), z ∈ O ∧ (y : K) = (algebraMap R K α) ^ r * z := by
    rw [pow_mul] at hy
    have hin: y ∈ Ideal.span {(algebraMap R O α)} ^ r:= (Ideal.pow_right_mono hmm r) hy
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at hin
    obtain ⟨⟨z,hz⟩,hzz ⟩:= hin
    use z
    constructor
    exact hz
    rw [mul_comm, eq_comm]
    rw [Subtype.ext_iff_val] at hzz
    exact hzz
  obtain ⟨z, hz, hzeq⟩:= aux
  rw [hzeq, ← mul_assoc, mul_comm x _, ← map_pow,  ← Algebra.smul_def]
  refine O.mul_mem (hr x hx) hz

/-- If `Oₐ` is the over ring of `O` in `Om` with respect to `α`, `Iₐ ` is the radical of `αO`,
 `Om` is finite free as an `R`-module, and `O ≠ Om`, then there is `n ∈ ℕ`
  such that `Oₐ ⬝ (Iₐ ^ n) ⊈ O ` and `Oₐ ⬝ (Iₐ ^ (n + 1)) ⊆ O `· -/
lemma exists_radical_pow_not_in_order {O : Subalgebra R K}  {Om : Subalgebra R K} (α : R)
    (hm : O ≤ Om) (hb : Basis ι R Om)
    (hn : (∃ (x : K),  x ∈ overRing α hm ∧  ¬ x ∈ O)) :
    ∃ (n : ℕ), (∃ (x : K) (y : O), x ∈ overRing α hm ∧
      y ∈ (Ideal.span ({(algebraMap R O α)}: Set O)).radical^(n) ∧ ¬ x * y ∈ O) ∧
      (∀ (x : K) (y : O), x ∈ overRing α hm →
      y ∈ (Ideal.span ({(algebraMap R O α)} : Set O)).radical^(n + 1) → x * y ∈ O) := by
  obtain ⟨ m, hm'⟩:= overRing_mul_radical_pow_in_order α hm hb
  have := exists_min_nat_prop_true m (λ n => ∀ (x : K) (y : O), x ∈ overRing α hm →
    y ∈ (Ideal.span ({(algebraMap R O α)}: Set O)).radical^(n) → x * y ∈ O) ?_ hm'
  swap
  · dsimp
    push_neg
    use hn.choose
    use 1
    simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top, OneMemClass.coe_one, mul_one, true_and]
    exact hn.choose_spec
  push_neg at this
  push_neg at this
  exact this


/-- If `α ∈ O` and `O` is equal to the multiplier ring of the radical of `α`, then
  `O` is equal to the over ring with respect to `α`· -/
lemma order_eq_overRing_of_multiplierRing_eq_order {O : Subalgebra R K}
    {Om : Subalgebra R K} (α : R) (hm: O ≤ Om) (hb : Basis ι R Om)
    (heq: O = multiplierRing (Ideal.span ({(algebraMap R O α)}: Set O)).radical) :
    O = overRing α hm := by
  have instNR : IsNoetherianRing O := subalgebraIsNoetherianRingOfLeFreeFiniteSubalgebra O Om hm hb
  ext x
  constructor
  exact (λ hx => subalgebra_le_overRing α hm hx)
  by_contra hc
  push_neg at hc
  obtain ⟨n, hn⟩ :=  exists_radical_pow_not_in_order α hm hb ⟨x, hc⟩
  have hfg : (Ideal.span ({(algebraMap R O α)}: Set O)).radical.FG := (isNoetherianRing_iff_ideal_fg O).mp instNR (Ideal.span {(algebraMap R O α)}).radical
  choose m hmm using Ideal.exists_radical_pow_le_of_fg (Ideal.span ({(algebraMap R O α)}: Set O)) hfg
  rcases hn with ⟨⟨t, y, ht, hy, hty ⟩, hn2⟩
  set z:= t * ↑y with hzeq
  have hzmem: z ∈ overRing α hm := (overRing α hm).mul_mem ht (subalgebra_le_overRing α hm y.2)
  have hin: ∀ (s : K)(r : O), s ∈  overRing α hm → r ∈ (Ideal.span ({(algebraMap R O α)}: Set O)).radical^(n + 1 + m) → (∃ j ∈ Ideal.span ({(algebraMap R O α)} : Set O), s * r = j) := by
    intros s r hs hr
    rw [pow_add] at hr
    let C := λ (k : O) => λ (_ : k ∈ (Ideal.span ({(algebraMap R O α)}: Set O)).radical ^ ( n + 1)*(Ideal.span ({(algebraMap R O α)}: Set O)).radical ^ (m)) => (∃ j ∈ Ideal.span ({(algebraMap R O α)} : Set O), s * k = j)
    have hcr : C r hr := by
      refine Submodule.mul_induction_on' ?_ ?_ hr
      · intros p hp q hq
        have : s*↑p ∈ O := hn2 s p hs hp
        use (⟨s * ↑p, this⟩ * q)
        constructor
        apply hmm
        refine Ideal.mul_mem_left _ _ hq
        simp only [MulMemClass.coe_mul, Subtype.coe_mk, mul_assoc]
      · intros p hp q hq hcp hcq
        obtain ⟨j,⟨hj, hjspec⟩⟩:= hcp
        obtain ⟨j',⟨hj', hj'spec⟩⟩:= hcq
        use (j+j')
        constructor
        refine Ideal.add_mem _ hj hj'
        simp only [AddMemClass.coe_add]
        rw [← hjspec, ← hj'spec, mul_add]
    exact hcr
  have hzmr: z ∈ multiplierRing (Ideal.span ({(algebraMap R O α)}: Set O)).radical := by
    intros i hi
    have zio: z * i ∈ O := by
      have : y * i ∈ (Ideal.span ({(algebraMap R O α)}: Set O)).radical^(n + 1) := by
        rw [pow_add, pow_one]
        exact Ideal.mul_mem_mul hy hi
      rw [hzeq, mul_assoc]
      convert hn2 t (y*i) ht this
    have himem: i ^ (n + 1 + m) ∈ (Ideal.span ({(algebraMap R O α)}: Set O)).radical^(n + 1 + m) := by
      exact Ideal.pow_mem_pow hi (n + 1 +m)
    have hzpowm: z ^ (n + 1 + m) ∈ overRing α hm := (overRing α hm).pow_mem hzmem _
    obtain ⟨j, hj, hzieq⟩  := hin (z ^ (n + 1 + m)) (i ^ (n + 1 +m)) hzpowm himem
    simp only [SubsemiringClass.coe_pow] at hzieq
    have auxeq: ↑(⟨z * i, zio⟩ : O) = z * ↑i := by
      simp only [Subtype.coe_mk]
    rw [← mul_pow , ← auxeq, ← SubsemiringClass.coe_pow, Subtype.coe_inj] at hzieq
    use ⟨z * i, zio⟩
    constructor
    · use (n + 1 + m)
      rw [hzieq]
      exact hj
    simp only [Subtype.coe_mk, mul_comm]
  rw [← heq] at hzmr
  exact hty hzmr

variable {O : Subalgebra R K} {Om: Subalgebra R K}(hm : O ≤ Om)
variable {π : R} (hp : Prime π)

local notation "Op" => AlgHom.range (Subalgebra.inclusion (overRing_le (π : R) hm))
local notation "O*" => Subalgebra.toSubmodule (AlgHom.range (Subalgebra.inclusion hm))

/-- If `O` and `Om` have equal rank, then the over ring with respect to `π`
  is `π`-maximal in `Om`. -/
lemma overRing_piMaximal [Module.Free R Om] [Module.Finite R Om]
    (heq : Module.rank R O = Module.rank R Om) (hp : Prime π) :
    piMaximal π (Subalgebra.toSubmodule Op) := by
  have hle1:= Submodule.rank_mono ((OrderEmbedding.le_iff_le  _).2 (subalgebra_le_overRing π hm) : Subalgebra.toSubmodule O ≤ Subalgebra.toSubmodule (overRing π hm))
  have hle2 := Submodule.rank_mono ((OrderEmbedding.le_iff_le  _).2 (overRing_le (π : R) hm) : Subalgebra.toSubmodule (overRing π hm) ≤ Subalgebra.toSubmodule Om)
  rw [Subalgebra.rank_toSubmodule Om] at hle2
  rw [Subalgebra.rank_toSubmodule, heq] at hle1
  have hle := le_antisymm hle2 hle1
  let B := Basis.reindex (Module.Free.chooseBasis R Om) (Fintype.equivFin (Module.Free.ChooseBasisIndex R Om))
  have heq' : Module.rank R (Subalgebra.toSubmodule Op) = Module.rank R Om := by
    rw [← LinearEquiv.rank_eq (Subalgebra.linearEquivOfInclusion _ _ (overRing_le (π : R) hm))]
    exact hle
  let b := Submodule.basisOfPID_of_eq_rank (Subalgebra.toSubmodule Op) heq'.symm
  unfold piMaximal
  by_contra hdvd
  obtain ⟨⟨mk,hmk⟩,hm1, hm2⟩ := Submodule.prime_dvd_index _ hp B b hdvd
  obtain ⟨⟨sk, hsk⟩, hs⟩:= hm2
  simp at hs
  have : mk ∈ overRing (π : R) hm := by
    rw [overRing_mem]
    constructor
    exact hmk
    obtain ⟨j, hy⟩ := hsk.2
    use (j + 1)
    rw [pow_add, pow_one, mul_smul, ← hs]
    exact hy
  apply hm1
  refine ⟨⟨mk, ?_⟩, ?_⟩
  simp only [*, Subalgebra.mem_toSubmodule]
  rfl

include hp in
/-- Pohst-Zassenhaus theorem:
  If `O` and `Om` have equal rank and `O` is equal to the multiplier ring of the radical of `πO`,
  then `O` is `π`-maximal· -/
theorem order_piMaximal_of_order_eq_multiplierRing [Module.Free R Om] [Module.Finite R Om]
    (heqr : Module.rank R O = Module.rank R Om)
    (heq : O = multiplierRing (Ideal.span {algebraMap R O π}).radical) :
    piMaximal π O* := by
  let B := Basis.reindex (Module.Free.chooseBasis R Om) (Fintype.equivFin (Module.Free.ChooseBasisIndex R Om))
  have aux2 :  (Subalgebra.inclusion hm).range = Op := by
    ext
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨⟨y, ?_⟩, rfl⟩
      convert y.2
      apply Eq.symm (order_eq_overRing_of_multiplierRing_eq_order _ _ B _)
      exact heq
    · rintro ⟨y, rfl⟩
      refine ⟨⟨y, ?_⟩, rfl⟩
      convert y.2
      apply order_eq_overRing_of_multiplierRing_eq_order _ _ B _
      exact heq
  rw [aux2]
  exact overRing_piMaximal hm heqr hp

end PartI

section PartII

/- In this section we specialize to the case where `O` is given by adjoining a root `θ`
  of an irreducible and monic polynomial `T` with coefficients in a PID `R` .
  Given a prime element `π` in `R`, we characterize the radical of `πO `
  as the ideal generated by `π` and `g(θ)`, where `g` is any lift of the
  radical of the polynomial `(f mod π )`.

  We give necessary and sufficient conditions for an element of
  the form `A(θ)/π` to be in the radical of `π`.
  This allows us to determine when an element is in the multiplier ring of the radical of `πO`·  -/

open Polynomial Pointwise

variable {R : Type*} [CommRing R] {π : R}
variable {ι : Type _ } [Fintype ι]
variable {T : Polynomial R} { O : Type _} [CommRing O] [Algebra R O] (j : IsAdjoinRoot O T)
variable {K : Type*} [Field K] (q : R →+* K ) 
  
local notation f:70 " mod " _π  :70 => (map q f)


/-- If `T` and `A` are a polynomials with coefficients in `R` and `θ` is a root of `T`,
 then `A(θ) ∈ πR[θ]` if and only if `T mod π ∣ A mod π`·  -/
lemma in_span_iff_minpoly_dvd_polynomial' (hqsurj : Function.Surjective q) (hqker : RingHom.ker q = Ideal.span {π})
    (A : Polynomial R) :
    j.map A ∈ Ideal.span ({(algebraMap R O π)}) ↔  (T mod π ) ∣ (A mod π) := by
  constructor
  · intro h1
    obtain ⟨q' , hq⟩:= Ideal.mem_span_singleton.1 h1
    obtain ⟨q1, hqq⟩:= (j.map_surjective) q'
    have hdvd: T ∣ (A - (C π) * q1) := by
      rw [← IsAdjoinRoot.map_eq_zero_iff j]
      simp only [map_sub, map_mul, map_natCast]
      rw [hq, hqq]
      convert sub_self ?_
      rw [IsAdjoinRoot.algebraMap_apply]
    obtain ⟨s,hs⟩:= hdvd
    use (s mod p)
    have : A = T * s + (C π) * q1 := by
      rw [← hs]
      ring
    rw [this]
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, add_right_eq_self, mul_eq_zero,
      _root_.map_eq_zero, ← RingHom.mem_ker, hqker, Ideal.mem_span_singleton_self, true_or]
  · rintro ⟨s, hs⟩
    obtain ⟨s', hs'⟩ := (map_surjective q) hqsurj  s
    have hpz: ((A - T * s') mod p) = 0 := by
      simp only [Polynomial.map_sub, Polynomial.map_mul]
      rw [hs, hs']
      ring
    rw [← pi_dvd_iff_mod_zero hqker (A - T * s')] at hpz
    obtain ⟨q,hq⟩:= hpz
    have : j.map (A - T * s')= j.map A := by
      simp only [map_sub, map_mul, IsAdjoinRoot.map_self, zero_mul, sub_zero]
    rw [← this, hq]
    simp only [C_eq_natCast, map_mul, map_natCast]
    rw [Ideal.mem_span_singleton, ← IsAdjoinRoot.algebraMap_apply]
    simp only [dvd_mul_right]

/-- If `T` and `A` are a polynomials with coefficients in `R`, `T` is monic and `θ` is a root of `T`,
 then `A(θ)` is in the radical of `πR[θ]` if and only if `g mod π ∣ A mod π`, where `g mod π` is
 the radical of `T mod π`·   -/
lemma in_radical_span_iff_radical_minpoly_dvd_polynomial (hqsurj : Function.Surjective q) (hqker : RingHom.ker q = Ideal.span {π})
  (hm : T.Monic)
  (A : R[X]) {g : R[X]} (hg : IsRadicalPart (g mod π ) (T mod π )):
  j.map A ∈ (Ideal.span ({(algebraMap R O π)})).radical ↔  (g mod π) ∣ (A mod π ) := by
  have htnz: (T mod π) ≠ 0 := map_monic_ne_zero hm
  constructor
  swap
  · intro hdvd
    obtain ⟨n, hn⟩ := dvd_pow_of_isRadicalPart htnz hg
    replace hdvd := pow_dvd_pow_of_dvd hdvd n
    have hdvdt : (T mod π) ∣ (A mod π) ^ n := dvd_trans hn hdvd
    have hpow : (A mod π) ^ n = ((A ^ n) mod π) := by
      simp only [Polynomial.map_pow]
    rw [hpow, ← in_span_iff_minpoly_dvd_polynomial' j q hqsurj hqker] at hdvdt
    simp only [map_pow] at hdvdt
    use n
  · rintro ⟨n,hn⟩
    have : (j.map A) ^ n= j.map (A ^ n) := by
      simp only [map_pow]
    rw [this , in_span_iff_minpoly_dvd_polynomial' j q hqsurj hqker (A ^ n), Polynomial.map_pow] at hn
    exact isRadicalPart_dvd_of_dvd_pow hg hn

/-- If `T` is a monic polynomial with coefficients in `R` and `θ` is a root of `T`, then
the radical of `πR[θ]` is generated by `π` and `g(θ)`, where `g` is an integral lift of the
radical of `(T mod π)`· -/
lemma radical_span_eq_span_radical_minpoly (hqsurj : Function.Surjective q) (hqker : RingHom.ker q = Ideal.span {π}) (hm : T.Monic)
    {g : Polynomial R}(hg : IsRadicalPart (g mod π ) (T mod π )) :
    (Ideal.span ({(algebraMap R O π)})).radical  = Ideal.span ({(algebraMap R O π), j.map g}):= by
  ext x
  constructor
  · obtain ⟨A, hA⟩ := (j.map_surjective) x
    intro hx
    rw [← hA] at hx
    rw [in_radical_span_iff_radical_minpoly_dvd_polynomial j q hqsurj hqker hm A hg] at hx
    obtain ⟨s,hs⟩ := hx
    obtain ⟨s',hs'⟩ := (map_surjective q hqsurj ) s
    have hpz : ((A - g * s') mod π)=0 := by
      simp only [Polynomial.map_sub, Polynomial.map_mul]
      rw [hs, hs']
      ring
    rw [← pi_dvd_iff_mod_zero hqker (A-g*s')] at hpz
    obtain ⟨q,hq⟩ := hpz
    rw [Ideal.mem_span_pair]
    have aux : A = (C π) * q +  s' * g := by
      rw [← hq]
      ring
    use j.map q, j.map s'
    rw [← map_mul , ← hA, aux]
    simp only [map_mul, map_add, map_natCast, add_left_inj, mul_comm, ← IsAdjoinRoot.algebraMap_apply]
  · intro hx
    obtain ⟨a, b,hab⟩ := Ideal.mem_span_pair.1 hx
    obtain ⟨a',ha'⟩ := j.map_surjective a
    obtain ⟨b',hb'⟩ := j.map_surjective b
    rw [← ha', ← hb'] at hab
    have aux: (j.map a') * (algebraMap R O π) + j.map b' * j.map g = j.map (a'* (C π) + b' * g) := by
      simp only [map_add, map_mul, ← IsAdjoinRoot.algebraMap_apply]
    rw [← hab, aux, in_radical_span_iff_radical_minpoly_dvd_polynomial j q hqsurj hqker hm _ hg]
    use (b' mod p)
    have aux : q π = 0 := by
      rw [← RingHom.mem_ker, hqker]
      exact Ideal.mem_span_singleton_self _
    simp only [Polynomial.map_add, Polynomial.map_mul, map_C, aux, map_zero, mul_zero, zero_add]
    rw [mul_comm]

variable [IsDomain R] [DecidableEq K]

/-- This lemma gives a necessary condition for an element of the form `A(θ)g(θ)/π` to be in
the radical of `πR[θ]` :  if the element is in the radical, then the product of `(T mod π)/(g mod π)`
with `(g mod π) / gcd (((g * h - T)/π mod π), (g mod π) )` divides `(A mod π)`· -/
lemma mul_dvd_polynomial_of_mem_radical_span (hqsurj : Function.Surjective q) (hqker : RingHom.ker q = Ideal.span {π}) (hm : T.Monic)
    {g h f A k : Polynomial R} (hg : IsRadicalPart (g mod π ) (T mod π )) (hpinz : π ≠ 0)
    (hf : f * (C π) =  g * h - T)
    (hk : (k mod π) * (EuclideanDomain.gcd (f mod π ) (g mod π)) = (g mod π)) {y : O}
    (hy' : y * (algebraMap R O π) = j.map (A * g)) :
    y ∈ (Ideal.span ({(algebraMap R O π)})).radical →  ((h * k) mod π) ∣ (A mod π) := by
  have auxq : q π = 0 := by
    rw [← RingHom.mem_ker, hqker]
    exact Ideal.mem_span_singleton_self _
  have hh : (h mod p) * (g mod p) = (T mod p) := by
    have : T = g * h - f * (C π ) := by rw [hf] ; ring
    rw [this, mul_comm]
    simp only [Polynomial.map_sub, Polynomial.map_mul, map_C, auxq, map_zero, mul_zero, zero_add, sub_zero]
  have hmm: (T mod p).Monic := Monic.map q hm
  have hgmnz: (g mod p) ≠ 0 := by
    by_contra hc
    rw [hc, mul_zero] at hh
    exact (Monic.ne_zero hmm) hh.symm
  intro hy
  rw [radical_span_eq_span_radical_minpoly j q hqsurj hqker hm hg] at hy
  obtain ⟨A₂' ,A₃', hA23⟩ := Ideal.mem_span_pair.1 hy
  obtain ⟨A₂, hA2⟩:= j.map_surjective A₂'
  obtain ⟨A₃, hA3⟩:= j.map_surjective A₃'
  rw [← hA2, ← hA3] at hA23
  have aux: (j.map) A₂ * (algebraMap R O π)  + (j.map) A₃ * (j.map) g= (j.map) ((C π) * A₂ + A₃ * g) := by
    simp only [map_add, map_mul, ← IsAdjoinRoot.algebraMap_apply, add_left_inj]
    rw [mul_comm]
  rw [aux] at hA23
  rw [← hA23] at hy'
  have aux2: j.map (A * g - (C π)*((C π) * A₂ + A₃ *g)) = 0 := by
    rw [map_sub, ← hy']
    simp only [map_add, map_mul, ← IsAdjoinRoot.algebraMap_apply]
    ring
  obtain ⟨A₄, hA4⟩:= (IsAdjoinRoot.map_eq_zero_iff j).1 aux2
  have : A * g = (C π) ^ 2 * A₂ + (C π) * A₃ * g + T * A₄ := by
    rw [← hA4]
    ring
  have hmodaux: (A mod π) * (g mod π)= ((A₄ * h) mod π) * (g mod π) := by
    rw [← Polynomial.map_mul,  this]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, auxq, map_zero,
      ne_eq, zero_pow, OfNat.ofNat_ne_zero, not_false_eq_true, zero_mul, add_zero, zero_add]
    rw [mul_assoc (map q A₄) _ _, hh, mul_comm]
  simp only [Polynomial.map_mul, mul_eq_mul_right_iff, hgmnz, or_false] at hmodaux
  rw [← Polynomial.map_mul, ← sub_eq_zero, ← Polynomial.map_sub, ← pi_dvd_iff_mod_zero hqker _] at hmodaux
  obtain ⟨A₅, hA5⟩:= hmodaux
  have haux2: (C π) * (f * A₄)= (C π) * ((C π) * A₂ + g * (A₃-A₅)) := by
    rw [← mul_assoc, mul_comm (C π) f, hf, sub_mul, ← hA4]
    ring_nf
    replace hA5 := eq_add_of_sub_eq hA5
    rw [hA5]
    simp only [C_eq_natCast, neg_add_rev, add_left_inj]
    ring
  simp only [mul_eq_mul_left_iff, C_eq_zero, hpinz, or_false] at haux2
  have haux3: (g mod p) ∣ ((A₄ mod π) * (f mod π)) := by
    use ((A₃ - A₅) mod π)
    rw [← Polynomial.map_mul, mul_comm, haux2]
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, auxq, map_zero,
      ne_eq, zero_pow, zero_mul, add_zero, zero_add]
  have hdvdgcd: (g mod p) ∣ (EuclideanDomain.gcd (f mod π) (g mod π))*(A₄ mod π) := by
    rw [EuclideanDomain.gcd_eq_gcd_ab, add_mul]
    refine dvd_add ?_ ?_
    · rw [mul_comm,  ← mul_assoc]
      exact dvd_mul_of_dvd_left haux3 (EuclideanDomain.gcdA (f mod π) (g mod π))
    · refine ⟨EuclideanDomain.gcdB (f mod π) (g mod π) * (A₄ mod π), by ring⟩
  have hkdvd: (k mod p) ∣ (A₄ mod π) := by
    obtain ⟨s,hs⟩ := hdvdgcd
    nth_rewrite 2 [← hk] at hs
    have haux4 : EuclideanDomain.gcd (f mod π) (g mod π) * (A₄ mod π) = EuclideanDomain.gcd (f mod π) (g mod π) *((k mod π) *  s) := by
      rw [hs]
      ring
    simp only [mul_eq_mul_left_iff] at haux4
    cases haux4
    · case _ haux4 =>
      exact ⟨s, haux4⟩
    · case _ haux4 =>
      exfalso
      rw [EuclideanDomain.gcd_eq_zero_iff] at haux4
      exact hgmnz haux4.2
  obtain ⟨t,ht⟩:=  hkdvd
  use t
  rw [eq_add_of_sub_eq hA5]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_C, auxq, map_zero,
      ne_eq, zero_pow, zero_mul, add_zero, zero_add]
  rw [ht]
  ring

/-- This lemma proves the other direction:
If the product of `(T mod π)/(g mod π)` with `(g mod π) / gcd (((g * h-T)/π mod π), (g mod π) )`
divides `(A mod π)` then `A(θ)g(θ)/π` is in the radical of `πR[θ]`· -/
lemma exists_mem_radical_span_of_mul_dvd_polynomial (hqsurj : Function.Surjective q) (hqker : RingHom.ker q = Ideal.span {π})
    (hm: T.Monic)(hp : Prime T)
    {g h f A k : Polynomial R }(hg : IsRadicalPart (g mod π ) (T mod π ))
    (hf: f * (C π)  = g * h - T)(hk : (k mod p) * (EuclideanDomain.gcd (f mod π) (g mod π ))= (g mod π )):
    ((h * k) mod π) ∣ (A mod π) → (∃ (y : O), y ∈ (Ideal.span ({(algebraMap R O π)})).radical ∧
       y * (algebraMap R O π) = j.map (A * g)) := by
  have auxq : q π = 0 := by
    rw [← RingHom.mem_ker, hqker]
    exact Ideal.mem_span_singleton_self _
  have hh : (h mod π) * (g mod π) = (T mod π) := by
    have : T = g * h - f * (C π) := by rw [hf] ; ring
    rw [this, mul_comm]
    simp only [Polynomial.map_sub, Polynomial.map_mul, map_C, auxq, map_zero, mul_zero, sub_zero]
  have hd : 0 < T.degree := by
    by_contra hz
    push_neg at hz
    have := Polynomial.eq_C_of_degree_le_zero hz
    unfold Monic at hm
    erw [this, Polynomial.leadingCoeff_C (coeff T 0)] at hm
    rw [this, hm] at hp
    simp only [map_one, not_prime_one] at hp
  have hmm: (T mod π).Monic := Monic.map q hm
  have hTmnz:= Monic.ne_zero hmm
  have hdegmod : (T mod π).natDegree = T.natDegree := Polynomial.Monic.natDegree_map hm _
  have hgmnz: (g mod π) ≠ 0 := by
    by_contra hc
    rw [hc, mul_zero] at hh
    exact (Monic.ne_zero hmm) hh.symm
  have hgcdnz: (EuclideanDomain.gcd (f mod π) (g mod π))≠ 0 := by
    by_contra hc
    rw [EuclideanDomain.gcd_eq_zero_iff] at hc
    exact hgmnz hc.2
  haveI := isDomainOfIsAdjointRootPrime T hp j
  intro hi
  obtain ⟨A₂, A₃,hA3⟩:= exists_of_dvd_mod_pi hqker hqsurj _ _ hi
  obtain ⟨q', hq⟩ := EuclideanDomain.gcd_dvd_left (f mod π) (g mod π)
  have hgdvdfk: (g mod π) ∣ ((f * k) mod π) := by
    use q'
    have aux: ((f * k) mod π)*(EuclideanDomain.gcd (f mod π) (g mod π)) =
      ((g mod π) * q')*(EuclideanDomain.gcd (f mod π) (g mod π)) := by
      rw [mul_assoc, mul_comm q', ← hq, Polynomial.map_mul, mul_assoc, hk, mul_comm]
    simp only [Polynomial.map_mul, mul_eq_mul_right_iff, or_false, hgcdnz] at aux
    convert aux
    rw [Polynomial.map_mul]
  have hgdvd2: (g mod π) ∣ ((f * k * A₂) mod π) := by
    rw [Polynomial.map_mul]
    refine dvd_mul_of_dvd_left hgdvdfk _
  obtain ⟨A₄, A₅, hA5⟩ := exists_of_dvd_mod_pi hqker hqsurj _ _ hgdvd2
  have aux3: (f * (C π) ) * A = (C π)  * (h * (f * k * A₂) + (f * (C π) ) * A₃) := by
    rw [hA3]
    ring
  rw [hA5, hf] at aux3
  apply_fun j.map at aux3
  simp only [map_mul, map_sub, IsAdjoinRoot.map_self, sub_zero, map_natCast, map_add] at aux3
  use j.map (g * (A₄ + A₃) + (C π) * A₅)
  constructor
  · rw [radical_span_eq_span_radical_minpoly j q hqsurj hqker hm hg, Ideal.mem_span_pair]
    use j.map A₅, j.map (A₄ + A₃)
    simp only [map_add, map_mul, ← IsAdjoinRoot.algebraMap_apply]
    ring
  · have : ((j.map) (g * (A₄ + A₃) + (C π) * A₅) * (algebraMap R O π))*(j.map h) =
      (j.map) (A * g) * (j.map h) := by
      rw [mul_comm, ← mul_assoc] at aux3
      rw [map_mul, aux3]
      simp only [map_add, map_mul, ← IsAdjoinRoot.algebraMap_apply]
      ring
    have hmaphnz: j.map h ≠ 0 := by
      by_contra hc
      rw [IsAdjoinRoot.map_eq_zero_iff] at hc
      have auxd := Polynomial.degree_eq_degree_of_associated
        (associated_of_dvd_dvd (Polynomial.map_dvd (q) hc) (dvd_of_mul_right_eq _ hh))
      erw [← hh, Polynomial.degree_mul,  ← add_zero (degree (map (q) h)), add_assoc, zero_add] at auxd
      have hgdegz := WithBot.add_left_cancel ?_ auxd
      swap
      simp only [ne_eq, degree_eq_bot]
      by_contra hc
      rw [hc, zero_mul] at hh
      exact hTmnz hh.symm
      have hTmoddeg: (T mod p).natDegree ≠ 0 := by
        erw [←pos_iff_ne_zero , hdegmod, Polynomial.natDegree_pos_iff_degree_pos]
        exact hd
      have := Polynomial.natDegree_pos_iff_degree_pos.1
        (pos_iff_ne_zero.2 (degree_ne_zero_of_isRadicalPart_of_degree_ne_zero (T mod π) (g mod π) hTmoddeg hg))
      erw [hgdegz] at this
      contradiction
    have aux5: ((j.map) (g * (A₄ + A₃) + (C π) * A₅) * (algebraMap R O π)) * (j.map h)
      = (j.map) (A * g) * (j.map h) := by
      rw [← this]
    simp only [hmaphnz, mul_eq_mul_right_iff, or_false] at aux5
    exact aux5

end PartII

section PartIII

/- We define Dedekind criterion for the polynomial `T`, and show that
if `T` satisifes the Dedekind's criterion for every prime, then the order
`R[θ]`, which is contained in `Om`, is actually equal to `Om`·  -/

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {π : R}
variable {T : Polynomial R} {K : Type _} [CommRing K] [Algebra R K] [NoZeroSMulDivisors R K]
variable (O : Subalgebra R K)
variable {F : Type*} [Field F]  [DecidableEq F] (q : R →+* F )
local notation f:70 " mod " _π  :70 => (map q f)


lemma order_eq_multiplierRing_of_dedekindCriterion' (hqsurj : Function.Surjective q)
    (hqker : RingHom.ker q = Ideal.span {π}) (j : IsAdjoinRoot O T)
    {g h f k : Polynomial R} {a b c: Polynomial F} (hm: T.Monic)
    (hg : IsRadicalPart (g mod π ) (T mod π )) (hpinz : π ≠ 0)
    (hf : f * (C π) = g * h - T) (hk : (k mod π ) * (EuclideanDomain.gcd (f mod π ) (g mod π )) = (g mod π ))
    (hgcd: a * (f mod π ) + b * (h mod π ) + c * (g mod π ) = 1) :
    O = multiplierRing (Ideal.span ({(algebraMap R O π)} : Set O)).radical := by
  have auxq : q π = 0 := by
    rw [← RingHom.mem_ker, hqker]
    exact Ideal.mem_span_singleton_self _
  have hh : (h mod π) * (g mod π) = (T mod π) := by
    have : T = g * h - f * (C π) := by rw [hf] ; ring
    rw [this, mul_comm]
    simp only [Polynomial.map_sub, Polynomial.map_mul, map_C, auxq, map_zero, mul_zero, sub_zero]
  refine le_antisymm (subalgebra_le_multiplierRing _) ?_
  intros x hx
  have hpinrad: (algebraMap R O π) ∈ (Ideal.span {((algebraMap R O π) : O)}).radical := by
    use 1
    rw [pow_one]
    exact Ideal.mem_span_singleton_self (algebraMap R O π)
  have hginrad: j.map g ∈ (Ideal.span {(algebraMap R O π)}).radical := by
    rw [radical_span_eq_span_radical_minpoly j q hqsurj hqker hm hg, Ideal.mem_span_pair]
    use 0,1
    rw [zero_mul, one_mul, zero_add]
  obtain ⟨y, hy1, (hy2 : (algebraMap R K π) * x = y)⟩ := hx (algebraMap R O π) hpinrad
  obtain ⟨t, ht1, ht2⟩ := hx (j.map g) hginrad
  obtain ⟨A, hA⟩:= j.map_surjective y
  have hgdvdA: (g mod π) ∣ (A mod π) := by
    rw [← in_radical_span_iff_radical_minpoly_dvd_polynomial j q hqsurj hqker hm A hg, hA]
    exact hy1
  have haux: t * (algebraMap R O π) = j.map (A * g) := by
    rw [map_mul, hA, ← Subtype.coe_inj]
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast]
    rw [← ht2,← hy2]
    norm_cast
    ring
  have hhkdvdA: ((h * k) mod π) ∣ (A mod π) := mul_dvd_polynomial_of_mem_radical_span j q hqsurj hqker hm hg hpinz hf hk haux ht1
  have hdvd1: (T mod π) ∣ (f mod π) * (A mod π) := by
    obtain ⟨s, hs⟩ := hhkdvdA
    obtain ⟨d, hd⟩ := EuclideanDomain.gcd_dvd_left (f mod π) (g mod π)
    rw [← hh, hs, ← hk]
    use d * s
    have aux: (h mod π) * ((k mod π) * EuclideanDomain.gcd (f mod π) (g mod π)) * (d * s) = (h mod π) * (k mod π) * (EuclideanDomain.gcd (f mod π) (g mod π) * d ) * s := by ring
    rw [aux, ← hd, Polynomial.map_mul]
    ring
  have hdvd2: (T mod π) ∣ (h mod π) * (A mod π) := by
    obtain ⟨s, hs⟩:= hgdvdA
    rw [← hh, hs]
    use s
    ring
  have hdvd3: (T mod π) ∣ (g mod π)*(A mod π) := by
    obtain ⟨s,hs⟩:= hhkdvdA
    rw [← hh, hs, Polynomial.map_mul]
    use (k mod p) * s
    ring
  have aux2: a * ((f mod π) * (A mod π)) + b * ((h mod π) * (A mod π)) + c * (((g mod π) * (A mod π))) = (A mod π) := by
    refine Eq.trans ?_ (one_mul (A mod p))
    rw [← hgcd]
    ring
  have hdvd: (T mod π) ∣ (A mod π) := by
  { rw [← aux2]
    refine dvd_add (dvd_add (dvd_mul_of_dvd_right hdvd1 _) (dvd_mul_of_dvd_right hdvd2 _)) (dvd_mul_of_dvd_right hdvd3 _) }
  rw [← in_span_iff_minpoly_dvd_polynomial' j q hqsurj hqker A] at hdvd
  obtain ⟨z, hz⟩:= Ideal.mem_span_singleton.1 hdvd
  rw [hA, ← Subtype.coe_inj, ← hy2, MulMemClass.coe_mul] at hz
  simp only [Subalgebra.coe_algebraMap, ← Algebra.smul_def] at hz
  rw [smul_right_inj hpinz] at hz
  rw [hz]
  simp only [SetLike.coe_mem]

/-- Let `T` be a monic polynomial in `R[X]` with root `θ` and `O = R[θ]`· Let
`g`,`h` and `f` be polynomials in `R[X]`, and `a`, `b` and `c` polynomials
with coefficients in `R / πR`· If  `f * π = g * h - T`, `g mod π` is the radical of `T mod p`, and
`a * (f mod π) + b * (g mod π) + c * (h mod π) = 1`, then
`O` is equal to the multiplier ring of the radical of `πO`· -/
lemma order_eq_multiplierRing_of_dedekindCriterion (hqsurj : Function.Surjective q)
    (hqker : RingHom.ker q = Ideal.span {π}) (j : IsAdjoinRoot O T)
    (hm : T.Monic) {g h f : Polynomial R}{a b c : Polynomial F}
    (hg : IsRadicalPart (g mod π) (T mod π)) (hpinz : π ≠ 0)
    (hf: f * (C π) = g * h - T) (hgcd : a * (f mod π) + b * (g mod π) + c * (h mod π) = 1) :
    O = multiplierRing (Ideal.span ({(algebraMap R O π)}: Set O)).radical := by
  obtain ⟨k', hk⟩ := EuclideanDomain.gcd_dvd_right (f mod π) (g mod π)
  rw [mul_comm , eq_comm] at hk
  obtain ⟨k, hkk⟩ := (map_surjective q) hqsurj k'
  rw [← hkk] at hk
  rw [add_assoc, add_comm _ (c * _), ← add_assoc] at hgcd
  exact order_eq_multiplierRing_of_dedekindCriterion' O q hqsurj hqker j hm hg hpinz hf hk hgcd


/- # DEFINITION OF DEDEKIND'S CRITERION

A polynomial `T` with coefficients in `R` satisfies Dedekind's criterion for the prime `π` if
`gcd (f, g, h) = 1`, where
  -- `g` is a lift of the radical of `(T mod π)`
  -- `h` is a lift of `(T mod π)/(g mod π)`
  -- `f` is the polynomial `(g * h - T)/π`

We formally define the Dedekind criterion in an equivalent but more convenient way, which avoids
divisions and is more suitable for computation· -/

/-- A polynomial `T` with coefficients in `R` satisfies the Dedekind criterion for the prime `π`
if there exist polynomials `f`, `g` and `h` with coefficients in `R` and polynomials
`a`, `b` and `c` with coefficients in the field `R/πR` such that :
  1·  `g mod π` is the radical of `T mod π`.
  2·  `f * π = g * h - T `.
  3·  `a * (f mod π) + b * (g mod π) + c * (h mod π) = 1`.
-/

def satisfiesDedekindCriterion (π : R)( T : Polynomial R) : Prop :=
  ∃ (f g h : Polynomial R)(a b c : Polynomial F),
  IsRadicalPart (g mod π ) (T mod π)
  ∧ f * (C π) = g * h - T
  ∧ (a * (f mod π) + b * (g mod π) + c * (h mod π) = 1)


variable (hqsurj : Function.Surjective q) (hqker : RingHom.ker q = Ideal.span {π})
include hqsurj hqker

/--  Let `T` be a monic prime polynomial in `R[X]` with root `θ` and `O = R[θ]`· If `T`
satisifes Dedekind criterion for the prime `π`, then `O` is equal to the
multiplier ring of the radical of `πO`· -/
lemma order_eq_of_satisfiesDedekindCriterion (j : IsAdjoinRoot O T)
    (hm : T.Monic) (hpinz : π ≠ 0):
    satisfiesDedekindCriterion q π T →  O = multiplierRing (Ideal.span ({(algebraMap R O π)}: Set O)).radical :=
  λ  ⟨_, _, _, _, _, _, hg, hf, hgcd⟩ => order_eq_multiplierRing_of_dedekindCriterion O q hqsurj hqker j hm hg hpinz hf hgcd

variable (O : Subalgebra R K) {Om : Subalgebra R K} (hmc : O ≤ Om)
local notation "O'" => AlgHom.range (Subalgebra.inclusion hmc)

variable [IsPrincipalIdealRing R]

/--  Let `T` be a monic prime polynomial in `R[X]` with root `θ` and `O = R[θ]`·
 If `O ⊆ Om`, both of equal rank, and `T` satisifes Dedekind criterion for
 the prime `π`, then `O` is `π`-maximal. -/
theorem piMaximal_of_satisfiesDedekindCriteria [Module.Free R Om] [Module.Finite R Om]
    (j: IsAdjoinRoot O T) (hp : Prime π )
    (hm: T.Monic)
    (heqr : Module.rank R O = Module.rank R Om)
    (h : satisfiesDedekindCriterion q π T) :
    piMaximal π (Subalgebra.toSubmodule O') := by
  refine order_piMaximal_of_order_eq_multiplierRing hmc hp heqr ?_
  refine order_eq_of_satisfiesDedekindCriterion O q hqsurj hqker j hm (Prime.ne_zero hp) h

/- We prove some results that, under certain conditions, allow us to conclude inthat `T` satisifes
  Dedekind's criterion for all but, at most, a finite amount of primes· -/

omit [IsDomain R] [DecidableEq F] hqsurj hqker [IsPrincipalIdealRing R] in
/-- If `(T mod π )` is its own radical part (i.e. it is separable), then `T` satisifes the Dedekind's
  criterion at `π`· -/
lemma satisfiesDedekindCriterion_of_poly_self_radical (T : Polynomial R)
    (hg : IsRadicalPart (T mod π) (T mod π)) :
    satisfiesDedekindCriterion q π T := by
  use 0, T , 1 , 0 , 0 , 1
  constructor
  · exact hg
  · constructor
    all_goals { norm_num }

omit [IsDomain R] hqsurj [IsPrincipalIdealRing R] in
/-- Let `a` and `b` be polynomials over `R` such that `a * T + b * T' = n`
with `n` a non-zero element in `R` (i.e· `T` is separable)· Then for every prime `π` such that
`π` is coprime with `n`, we have that `T` satisfies the Dedekind's criterion at `π`· -/
lemma satisfiesDedekindCriterion_of_coprime {n : R} (T a b : Polynomial R)
    (hgcd : a * T + b * (derivative T) = C n)
    (hndvd : IsCoprime n π) : satisfiesDedekindCriterion q π T := by
  apply satisfiesDedekindCriterion_of_poly_self_radical q T
  refine self_isRadicalPart_of_coprime' q hqker (T.map q) ?_ hndvd
  use (map q a) , (map q b)
  apply_fun (map q) at hgcd
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, ← derivative_map] at hgcd
  exact hgcd

end PartIII



section PartV

/- Dedekind criterion may be used even if the subalgebra is not of the form `R[θ]`-/
open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] {π : R} (hp : Prime π)
  {T : Polynomial R} (hm : Monic T)
  {K : Type _} [CommRing K] [Algebra R K]
  (O : Subalgebra R K) (Oₖ : Subalgebra R K)
  {F : Type*} [Field F] [DecidableEq F] (q : R →+* F )
  (hqsurj : Function.Surjective q)
  (hqker : RingHom.ker q = Ideal.span {π})

include hm hp hqsurj hqker in
/-- Consider subalgebras `O, Oₖ, Om` with `O ⊆ Oₖ ⊆ Om`.
  Suppose that `O = R[θ]` with `θ` a root of `T`, and that `Om` has equal rank to
  the degree of `T`, then if `T` satisfies Dedekind criterion at `π`, then
  `Oₖ` is `π`-maximal (in `Om`).  -/
lemma piMaximal_of_gt_adjoinRoot_of_satisfiesDedekindCriterion [NoZeroSMulDivisors R K] (Om : Subalgebra R K)
    [Module.Free R Om] [Module.Finite R Om](j : IsAdjoinRoot O T)
    (hmc' : O ≤ Oₖ ) (hmc : Oₖ ≤ Om)
    (heqr : T.natDegree  = Module.rank R Om)
    (hd : satisfiesDedekindCriterion q π T) :
  piMaximal π (Subalgebra.toSubmodule ((Subalgebra.inclusion hmc).range)) := by
  have hrO : Module.rank R O = T.natDegree := by
    rw [ rank_eq_card_basis (IsAdjoinRootMonic.basis ⟨j, hm⟩)]
    simp only [Fintype.card_fin]
  rw [← hrO] at heqr
  have : (Subalgebra.toSubmodule (Subalgebra.inclusion (le_trans hmc' hmc)).range) ≤ (Subalgebra.toSubmodule (Subalgebra.inclusion hmc).range) := by
    simp only [OrderEmbedding.le_iff_le]
    rintro x ⟨⟨s, hs'⟩ , hs⟩
    use ⟨s, hmc' hs' ⟩
    rw [←  hs]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Subalgebra.inclusion_mk]
  apply piMaximal_of_piMaximal_lt this π
  refine piMaximal_of_satisfiesDedekindCriteria q hqsurj hqker O (le_trans hmc' hmc) j hp hm heqr hd

/- We specialize further to the case where `K = Q(θ)`.  -/

variable {Q : Type*} [Field Q] [Algebra R Q] [Algebra Q K]
  [IsFractionRing R Q] [IsScalarTower R Q K]
  (A : IsAdjoinRoot K (map (algebraMap R Q) T))

local notation " θ " => A.root

include hm hp hqsurj hqker in
/-- Let `K = Q(θ)`. Consider subalgebras `O ⊆ Om`. If `θ ∈ O`, `Om` has
  rank equal to the degree of `T`, and `T` satisfies Dedekind critetion at `π`,
  then `O` is `π`-maximal.  -/
lemma piMaximal_of_root_in_subalgebra_of_satisfiesDedekindCriterion
    (Om : Subalgebra R K) [Module.Free R Om] [Module.Finite R Om]
    (hmc : O ≤ Om) (heqr : T.natDegree  = Module.rank R Om) (hroot : θ ∈ O)
    (hd : satisfiesDedekindCriterion q π T) :
    piMaximal π (Subalgebra.toSubmodule ((Subalgebra.inclusion hmc).range)) := by
  haveI : NoZeroSMulDivisors R K := NoZeroSMulDivisors.trans R Q K
  have hminpoly := IsAdjoinRoot.minpoly_root A (Monic.ne_zero (Monic.map (algebraMap R Q) hm))
  rw [(Polynomial.Monic.leadingCoeff (Monic.map (algebraMap R Q) hm))] at hminpoly
  simp only [ inv_one, map_one, mul_one] at hminpoly
  have hmc' : Algebra.adjoin R {θ} ≤ O := by
    apply Algebra.adjoin_le
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact hroot
  have j : IsAdjoinRoot (Algebra.adjoin R {θ}) T := Algebra.adjoin_isAdjoinRoot T hm θ hminpoly
  exact piMaximal_of_gt_adjoinRoot_of_satisfiesDedekindCriterion hp hm
    (Algebra.adjoin R {θ}) O q hqsurj hqker Om j hmc' hmc heqr hd


end PartV

section PartInteger

/- We specialize some of the definitions and results above to the case
where `R = ℤ` and `F = ZMod p` -/

variable {K : Type _} [CommRing K]
local notation f:70 " mod " p   :70 => (map (algebraMap ℤ (ZMod p)) f)


/-- Dedekind criterion for integer polynomials. -/
def satisfiesDedekindCriterionInt (T : Polynomial ℤ) (p : ℕ) : Prop :=
  ∃ (f g h : Polynomial ℤ)(a b c : Polynomial $ ZMod p),
  IsRadicalPart (g mod p) (T mod p)
  ∧ f * p = g * h - T
  ∧ (a * (f mod p) + b * (g mod p)+ c * (h mod p) = 1)

variable (O : Subalgebra ℤ K) {Om : Subalgebra ℤ K} (hmc : O ≤ Om)

local notation "O'" => AlgHom.range (Subalgebra.inclusion hmc)

lemma satisfiesDedekindCriterion_int_of_satisifesDedekindCriterion ( T : Polynomial ℤ) (p : ℕ)
   [hpr : Fact $ Nat.Prime p] (h : satisfiesDedekindCriterion (algebraMap ℤ (ZMod p)) (p : ℤ) T ) :
  satisfiesDedekindCriterionInt T p := by
  obtain ⟨f, g, h , a, b, c, hg, hf, hgcd⟩ := h
  use f, g, h, a, b, c
  refine ⟨hg, ?_, hgcd⟩
  · rw [← hf ]
    simp only [map_natCast]

variable [NoZeroSMulDivisors ℤ K]

/--  Let `T` be a monic prime polynomial in `ℤ[X]` with root `θ` and `O = ℤ[θ]`· If `T`
satisifes the Dedekind criteria for the prime number `p`, then `O` is equal to the
multiplier ring of the radical of `pO`· -/
lemma order_eq_of_satisfiesDedekindCriteria (j : IsAdjoinRoot O T) (p : ℕ) [hpr : Fact $ Nat.Prime p]
    (hm : T.Monic) :
    satisfiesDedekindCriterionInt T p →
    O = multiplierRing (Ideal.span ({(algebraMap ℤ O ↑p)}: Set O)).radical := by
  let q := algebraMap ℤ (ZMod p)
  have hqsurj : Function.Surjective q := ZMod.ringHom_surjective q
  have hqker : RingHom.ker q = Ideal.span {↑p} := ZMod.ker_intCastRingHom p
  have hpinz : (p : ℤ) ≠ 0 := by
    simp only [ne_eq, not_false_eq_true, Nat.cast_eq_zero, Nat.Prime.ne_zero, hpr.out]
  intro ⟨f, g, h , a, b, c, hg, hf, hgcd⟩
  have : satisfiesDedekindCriterion q p T := by
    use f , g, h, a, b, c
    exact ⟨ hg, hf, hgcd⟩
  exact order_eq_of_satisfiesDedekindCriterion O q hqsurj hqker j hm hpinz this


/-- Let `T` be a monic prime polynomial in `ℤ[X]` with root `θ`· Assume
 `O = ℤ[θ]` has equal rank as `Om`, with `Om` a `ℤ`-subalgebra, free and finite
  as `ℤ`-module. If `T` satisfies the Dedekind
criteria at the prime `p`, then `O` is `p`-maximal in `Om`·  -/
theorem piMaximal_of_satisfiesDedekindCriteria_int (j: IsAdjoinRoot O T)(p : ℕ)
    [hp:  Fact $ Nat.Prime p](hm: T.Monic) [Module.Free ℤ Om] [Module.Finite ℤ Om]
    (heqr : Module.rank ℤ O = Module.rank ℤ Om) (h : satisfiesDedekindCriterionInt T p ) :
    piMaximal (p : ℤ) (Subalgebra.toSubmodule O') :=
  order_piMaximal_of_order_eq_multiplierRing hmc (Nat.prime_iff_prime_int.mp hp.out)
  heqr (order_eq_of_satisfiesDedekindCriteria O j p hm h)

include hmc in
/-- Let `T` be a monic polynomial in `ℤ[X]` with root `θ`· Assume
 `O = ℤ[θ]` has equal rank as `Om`, with `Om` a `ℤ`-subalgebra, free and finite
  as `ℤ`-module. If `T` satisfies the Dedekind
  criteria at every prime `p`, then `O = Om`· -/
theorem maximal_of_satisfiesDedekindCriteria_all_primes (j: IsAdjoinRoot O T)(p : ℕ)
    [Fact $ Nat.Prime p] (hm: T.Monic) [Module.Free ℤ Om] [Module.Finite ℤ Om]
    (heqr : Module.rank ℤ O = Module.rank ℤ Om)
    (h : ∀ (p : ℕ), Nat.Prime p → satisfiesDedekindCriterionInt T p) :
    O = Om := by
  apply eq_of_piMaximal_at_all_primes_int O Om hmc
  intros q hq
  haveI := fact_iff.2 hq
  apply piMaximal_of_satisfiesDedekindCriteria_int O hmc j q hm heqr (h q hq)

/-- Let `a` and `b` be polynomials over `ℤ` such that `a * T + b * T' = n`
with `n` a non-zero integer (i.e· `T` is separable)· Then for every prime `p` such that
`p` does not divide `n`, we have that `T` satisfies the Dedekind criteria at `p`· -/
lemma satisfiesDedekindCriterion_of_coprime_int ( T a b : Polynomial ℤ) (p n : ℕ)
    [hp : Fact (Nat.Prime p)] (hgcd : a * T + b * (derivative T) = n) (hdvd : ¬ (p ∣ n) ) :
    satisfiesDedekindCriterionInt T p := by
  apply satisfiesDedekindCriterion_int_of_satisifesDedekindCriterion
  have : IsCoprime (n : ℤ) (p : ℤ) := by
    rw [← isCoprime_comm, Prime.coprime_iff_not_dvd, Int.natCast_dvd_natCast]
    exact hdvd
    exact Nat.prime_iff_prime_int.mp hp.out
  refine satisfiesDedekindCriterion_of_coprime (algebraMap ℤ (ZMod p)) ?_ T a b ?_ this
  exact ZMod.ker_intCastRingHom p
  rw [hgcd]
  simp only [map_natCast]

/- There's no need to introduce the discriminant of `T` to discard all but a finite amount
  of primes when checking for `p`-maximality.
  In fact, since the discriminant is the resultant of `T` and `T'`, it can be written in the form
  `a * T + b * T'`, so by choosing suitable polynomials `a` and `b`, we can make `n` equal to the
  discriminant of `T`·  -/

variable {T : Polynomial ℤ} (hm : T.Monic) (hpr : Prime T)

local notation " ℚ[θ] " => AdjoinRoot (map (algebraMap ℤ ℚ) T)

/-- A basis for the ring of integers of a number field `ℚ(θ)`, with `θ` a root of
  the monic prime polynomial `T`, indexed by `(Fin (T.natDegree))`.  -/
noncomputable def AdjoinRoot.basisIntegralClosure  :
    Basis (Fin (T.natDegree)) ℤ (integralClosure ℤ (ℚ[θ])) := by
  have hirr : Irreducible (map (algebraMap ℤ ℚ) T) :=
    (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (hm)).1
    (UniqueFactorizationMonoid.irreducible_iff_prime.2 hpr)
  have hdeg : (map (algebraMap ℤ ℚ) T).natDegree = T.natDegree := by
    apply Polynomial.natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int _
  haveI := (@fact_iff (Irreducible (map (algebraMap ℤ ℚ) T))).2 hirr
  have hequiv: Module.Free.ChooseBasisIndex ℤ (NumberField.RingOfIntegers ℚ[θ]) ≃ Fin (T.natDegree) := by
    refine Fintype.equivOfCardEq  ?_
    rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank, Fintype.card_fin, ← hdeg]
    convert (Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux (Irreducible.ne_zero hirr)))
    simp only [Fintype.card_fin]
  exact Basis.reindex (NumberField.RingOfIntegers.basis ℚ[θ]) hequiv

variable [Algebra ℚ K]
  (A : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T))

local notation "θ" => A.root

omit [NoZeroSMulDivisors ℤ K] in
/-- Let `K = ℚ(θ)`. Consider subalgebras `O ⊆ Om`. If `θ ∈ O`, `Om` has
  rank equal to the degree of `T`, and `T` satisfies Dedekind critetion at `p`,
  then `O` is `p`-maximal.  -/
lemma piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int {p : ℕ } {O Om: Subalgebra ℤ K}
  (hm : T.Monic) [hp : Fact $ Nat.Prime p] [Module.Free ℤ Om] [Module.Finite ℤ Om] (hmc : O ≤ Om)
  (heqr : T.natDegree  = Module.rank ℤ Om) (hroot : θ ∈ O) (hd : satisfiesDedekindCriterionInt T p) :
  piMaximal (p : ℤ)  (Subalgebra.toSubmodule ((Subalgebra.inclusion hmc).range))  := by
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    let q := algebraMap ℤ (ZMod p)
    have hqsurj : Function.Surjective q := ZMod.ringHom_surjective q
    have hqker : RingHom.ker q = Ideal.span {↑p} := ZMod.ker_intCastRingHom p
    refine piMaximal_of_root_in_subalgebra_of_satisfiesDedekindCriterion hpz hm
      O q hqsurj hqker A Om hmc heqr hroot ?_
    obtain ⟨f, g, h , a, b, c, hg, hf, hgcd⟩ := hd
    use f , g, h, a, b, c
    exact ⟨ hg, hf, hgcd⟩

end PartInteger
