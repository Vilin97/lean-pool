/-
Copyright (c) 2026 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import LeanPool.SelbergSieve4.Selberg

/-!
# LeanPool.SelbergSieve4.Applications.PrimeCountingUpperBound
-/

open scoped Nat Nat.Prime ArithmeticFunction.zeta ArithmeticFunction.Moebius
open scoped ArithmeticFunction.omega BigOperators

noncomputable section
namespace PrimeUpperBound

attribute [local instance] Classical.propDecidable

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

lemma prodDistinctPrimes_squarefree (s : Finset ℕ) (h : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  refine Iff.mpr Nat.squarefree_iff_prime_squarefree ?_
  intro p hp; by_contra h_dvd
  by_cases hps : p ∈ s
  · rw [← Finset.mul_prod_erase (a := p) (h := hps),
      mul_dvd_mul_iff_left (Nat.Prime.ne_zero hp)] at h_dvd
    obtain ⟨q, hq⟩ := Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) h_dvd
    rw [Finset.mem_erase] at hq
    exact hq.1.1 <| ((Nat.prime_dvd_prime_iff_eq hp (h q hq.1.2)).mp hq.2).symm
  · have : p ∣ ∏ p ∈ s, p := Trans.trans (dvd_mul_right p p) h_dvd
    obtain ⟨q, hq⟩ := Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) this
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (h q hq.1)).mp hq.2
    rw [heq] at hps; exact hps hq.1

lemma primorial_squarefree (n : ℕ) : Squarefree (primorial n) := by
  apply prodDistinctPrimes_squarefree
  simp_rw [Finset.mem_filter]
  exact fun _ h => h.2

theorem zeta_pos_of_prime :
    ∀ (p : ℕ), Nat.Prime p → (0 : ℝ) < (↑ζ : ArithmeticFunction ℝ) p := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num

theorem zeta_lt_self_of_prime :
    ∀ (p : ℕ), Nat.Prime p → (↑ζ : ArithmeticFunction ℝ) p < (p : ℝ) := by
  intro p hp
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg (Nat.Prime.ne_zero hp)]
  norm_num
  exact Nat.succ_le_iff.mp (Nat.Prime.two_le hp)

/-- Selberg sieve specialized to primes at most the real level `y`. -/
def primeSieve (N : ℕ) (y : ℝ) (hy : 1 ≤ y) : SelbergSieve := {
  support := Finset.range (N + 1)
  prodPrimes := primorial (Nat.floor y)
  prodPrimes_squarefree := primorial_squarefree _
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := N
  nu := (ζ : ArithmeticFunction ℝ).pdiv .id
  nu_mult := by arith_mult
  nu_pos_of_prime := fun p hp _ => by
    simp [if_neg hp.ne_zero, Nat.pos_of_ne_zero hp.ne_zero]
  nu_lt_one_of_prime := fun p hp _ => by
    simpa [hp.ne_zero] using
      (inv_lt_one_of_one_lt₀ (by norm_cast; exact hp.one_lt) : (p : ℝ)⁻¹ < 1)
  level := y
  one_le_level := hy
}

theorem prime_dvd_primorial_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ primorial n ↔ p ≤ n := by
  unfold primorial
  constructor
  · intro h
    let h' : ∃ i, i ∈ Finset.filter Nat.Prime (Finset.range (n + 1)) ∧ p ∣ i :=
      Prime.exists_mem_finset_dvd (Nat.Prime.prime hp) h
    obtain ⟨q, hq⟩ := h'
    rw [Finset.mem_filter, Finset.mem_range] at hq
    rw [prime_dvd_prime_iff_eq (Nat.Prime.prime hp) (Nat.Prime.prime hq.1.2)] at hq
    rw [hq.2]
    exact Nat.lt_succ_iff.mp hq.1.1
  · intro h
    apply Finset.dvd_prod_of_mem
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr h, hp⟩

theorem siftedSum_eq (s : SelbergSieve) (hw : ∀ i ∈ s.support, s.weights i = 1)
    (z : ℝ) (hz : 1 ≤ z) (hP : s.prodPrimes = primorial (Nat.floor z)) :
    s.siftedSum =
      (s.support.filter (fun d => ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ d)).card := by
  dsimp only [Sieve.siftedSum]
  rw [Finset.card_eq_sum_ones, ←Finset.sum_filter, Nat.cast_sum]
  apply Finset.sum_congr
  · rw [hP]
    ext d
    constructor
    · intro hd
      rw [Finset.mem_filter] at *
      constructor
      · exact hd.1
      · intro p hpp hpy
        rw [← Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.Coprime.coprime_dvd_left _ hd.2
        rw [prime_dvd_primorial_iff _ _ hpp]
        apply Nat.le_floor hpy
    · intro h
      rw [Finset.mem_filter] at *
      constructor
      · exact h.1
      refine Nat.coprime_of_dvd ?_
      intro p hp
      erw [prime_dvd_primorial_iff _ _ hp]
      intro hpy
      apply h.2 p hp
      trans ↑(Nat.floor z)
      · norm_cast
      · apply Nat.floor_le
        linarith only [hz]
  · simp_rw [Nat.cast_one]
    intro x hx
    rw [Finset.mem_filter] at hx
    apply hw x hx.1

theorem primeSieve_siftedSum_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (primeSieve N y hy).siftedSum =
      ((Finset.range (N + 1)).filter (fun d => ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ d)).card := by
  apply siftedSum_eq
  · exact fun _ _ => rfl
  · exact hy
  · rfl

theorem prime_subset (N : ℕ) (y : ℝ) :
    (Finset.range (N + 1)).filter Nat.Prime ⊆
      ((Finset.range (N + 1)).filter (fun d => ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ d))
      ∪ Finset.Icc 1 (Nat.floor y) := by
  intro p
  simp_rw [Finset.mem_union, Finset.mem_filter]
  intro h
  by_cases hp_le : p ≤ y
  · right
    rw [Finset.mem_Icc]
    exact ⟨le_of_lt h.2.one_lt, Nat.le_floor hp_le⟩
  · left
    constructor
    · exact h.1
    · intro q hq hq'
      rw [prime_dvd_prime_iff_eq hq.prime h.2.prime]
      intro hqp
      rw [hqp] at hq'
      linarith only [hp_le, hq']


theorem pi_le_siftedSum (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    π N ≤ (primeSieve N y hy).siftedSum + y := by
  trans ((primeSieve N y hy).siftedSum + Nat.floor y)
  · have : (Finset.Icc 1 (Nat.floor y)).card = Nat.floor y := by
      rw [Nat.card_Icc]; norm_num
    rw [primeSieve_siftedSum_eq, ←this]
    unfold Nat.primeCounting
    unfold Nat.primeCounting'
    rw [Nat.count_eq_card_filter_range]
    norm_cast
    trans (((Finset.range (N + 1)).filter
        (fun d => ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ d))
      ∪ Finset.Icc 1 (Nat.floor y)).card
    · exact Finset.card_le_card (prime_subset N y)
    apply Finset.card_union_le
  · gcongr
    apply Nat.floor_le
    linarith only [hy]

/-- Predicate asserting that an arithmetic function is completely multiplicative. -/
def CompletelyMultiplicative (f : ArithmeticFunction ℝ) : Prop :=
  f 1 = 1 ∧ ∀ a b, f (a * b) = f a * f b

namespace CompletelyMultiplicative
open ArithmeticFunction
theorem zeta : CompletelyMultiplicative ζ := by
  unfold CompletelyMultiplicative
  constructor
  · simp [ArithmeticFunction.zeta_apply]
  intro a b
  by_cases ha : a = 0
  · simp [ArithmeticFunction.zeta_apply, ha]
  by_cases hb : b = 0
  · simp [ArithmeticFunction.zeta_apply, hb]
  simp [ArithmeticFunction.zeta_apply, ha, hb, mul_eq_zero]

theorem id : CompletelyMultiplicative ArithmeticFunction.id := by
  constructor <;> simp

theorem pmul (f g : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pmul f g) := by
  constructor
  · rw [pmul_apply, hf.1, hg.1, mul_one]
  intro a b
  simp_rw [pmul_apply, hf.2, hg.2]; ring

theorem pdiv {f g : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f)
    (hg : CompletelyMultiplicative g) :
    CompletelyMultiplicative (ArithmeticFunction.pdiv f g) := by
  constructor
  · rw [pdiv_apply, hf.1, hg.1, div_one]
  intro a b
  simp_rw [pdiv_apply, hf.2, hg.2]; ring

theorem isMultiplicative {f : ArithmeticFunction ℝ} (hf : CompletelyMultiplicative f) :
    ArithmeticFunction.IsMultiplicative f :=
  ⟨hf.1, fun _ => hf.2 _ _⟩

theorem apply_pow (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (a n : ℕ) :
    f (a^n) = f a ^ n := by
  induction n with
  | zero => simpa using hf.1
  | succ n' ih =>
      calc
        f (a ^ (n' + 1)) = f (a ^ n' * a) := by rw [pow_succ]
        _ = f (a ^ n') * f a := hf.2 _ _
        _ = f a ^ n' * f a := by rw [ih]
        _ = f a ^ (n' + 1) := by rw [pow_succ]

end CompletelyMultiplicative

theorem prod_factors_one_div_compMult_ge (M : ℕ) (f : ArithmeticFunction ℝ)
    (hf : CompletelyMultiplicative f) (hf_nonneg : ∀ n, 0 ≤ f n) (d : ℕ)
    (hd : Squarefree d) (hf_size : ∀ n, n.Prime → n ∣ d → f n < 1) :
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
    ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n) := by
  calc
    f d * ∏ p ∈ d.primeFactors, 1 / (1 - f p)
        = ∏ p ∈ d.primeFactors, f p / (1 - f p) := by
      conv => { lhs; congr; rw [←Nat.prod_primeFactors_of_squarefree hd] }
      rw [hf.isMultiplicative.map_prod_of_subset_primeFactors _ _ subset_rfl,
        ← Finset.prod_mul_distrib]
      simp_rw [one_div, div_eq_mul_inv]
    _ ≥ ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, (f p) ^ n := by
      gcongr with p hp
      · exact fun p _ => Finset.sum_nonneg fun n _ => pow_nonneg (hf_nonneg p) n
      rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
      simpa [← Finset.Ico_succ_right_eq_Icc, pow_one] using
        (geom_sum_Ico_le_of_lt_one (m := 1) (n := M.succ) (x := f p) (hf_nonneg p)
          (hf_size p hp.1 hp.2))
    _ = ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n) := by
      simp_rw [hf.apply_pow]

theorem prod_factors_sum_pow_compMult (M : ℕ) (hM : M ≠ 0)
    (f : ArithmeticFunction ℝ) (hf : CompletelyMultiplicative f) (d : ℕ)
    (hd : Squarefree d) :
    ∏ p ∈ d.primeFactors, ∑ n ∈ Finset.Icc 1 M, f (p ^ n)
    = ∑ m ∈ (d ^ M).divisors.filter (d ∣ ·), f m := by
  rw [Finset.prod_sum]
  let i : (a : _) → (ha : a ∈ Finset.pi d.primeFactors fun p => Finset.Icc 1 M) → ℕ :=
    fun a _ => ∏ p ∈ d.primeFactors.attach, p.1 ^ (a p p.2)
  have hfact_i : ∀ a ha,
      ∀ p, Nat.factorization (i a ha) p = if hp : p ∈ d.primeFactors then a p hp else 0 := by
    intro a ha p
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp, Nat.factorization_prod, Finset.sum_apply',
        Finset.sum_eq_single ⟨p, hp⟩, Nat.factorization_pow, Finsupp.smul_apply,
          Nat.Prime.factorization_self (Nat.prime_of_mem_primeFactors hp)]
      · ring
      · intro q _ hq
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_zero]
        right
        apply Nat.factorization_eq_zero_of_not_dvd
        rw [Nat.Prime.dvd_iff_eq (Nat.prime_of_mem_primeFactors q.2)
          (Nat.prime_of_mem_primeFactors hp).ne_one, ← exists_eq_subtype_mk_iff]
        push Not
        exact fun _ => hq
      · intro h
        exfalso
        exact h (Finset.mem_attach _ _)
      · exact fun q _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactors q.2))
    · rw [dif_neg hp]
      by_cases hpp : p.Prime
      swap
      · apply Nat.factorization_eq_zero_of_not_prime _ hpp
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hp_dvd
      obtain ⟨⟨q, hq⟩, _, hp_dvd_pow⟩ := Prime.exists_mem_finset_dvd hpp.prime hp_dvd
      apply hp
      rw [Nat.mem_primeFactors]
      constructor
      · exact hpp
      · refine ⟨?_, hd.ne_zero⟩
        trans q
        · apply Nat.Prime.dvd_of_dvd_pow hpp hp_dvd_pow
        · apply Nat.dvd_of_mem_primeFactors hq
  have hi_ne_zero : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ≠ 0 := by
    intro a ha
    erw [Finset.prod_ne_zero_iff]
    exact fun p _ => pow_ne_zero _ (ne_of_gt (Nat.pos_of_mem_primeFactors p.property))
  have hi : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      i a ha ∈ (d ^ M).divisors.filter (d ∣ ·) := by
    intro a ha
    rw [Finset.mem_filter, Nat.mem_divisors,
      ← Nat.factorization_le_iff_dvd hd.ne_zero (hi_ne_zero a ha),
      ←Nat.factorization_le_iff_dvd (hi_ne_zero a ha) (pow_ne_zero _ hd.ne_zero)]
    constructor; constructor
    · rw [Finsupp.le_iff]; intro p _
      rw [hfact_i a ha]
      by_cases hp : p ∈ d.primeFactors
      · rw [dif_pos hp]
        rw [Nat.factorization_pow, Finsupp.smul_apply]
        simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
        trans (M • 1)
        · norm_num
          exact (ha p hp).2
        · gcongr
          rw [Nat.mem_primeFactors_of_ne_zero hd.ne_zero] at hp
          rw [←Nat.Prime.dvd_iff_one_le_factorization hp.1 hd.ne_zero]
          exact hp.2
      · rw [dif_neg hp]; norm_num
    · apply pow_ne_zero _ hd.ne_zero
    · rw [Finsupp.le_iff]; intro p hp
      rw [Nat.support_factorization] at hp
      rw [hfact_i a ha]
      rw [dif_pos hp]
      trans 1
      · exact hd.natFactorization_le_one p
      simp_rw [Finset.mem_pi, Finset.mem_Icc] at ha
      exact (ha p hp).1
  have h : ∀ (a : _) (ha : a ∈ Finset.pi d.primeFactors fun _p => Finset.Icc 1 M),
      ∏ p ∈ d.primeFactors.attach, f (p.1 ^ (a p p.2)) = f (i a ha) := by
    intro a ha
    apply symm
    apply hf.isMultiplicative.map_prod
    intro x _ y _ hxy
    simp_rw [Finset.mem_pi, Finset.mem_Icc, Nat.succ_le_iff] at ha
    apply (Nat.coprime_pow_left_iff (ha x x.2).1 ..).mpr
    apply (Nat.coprime_pow_right_iff (ha y y.2).1 ..).mpr
    have hxp := Nat.prime_of_mem_primeFactors x.2
    rw [Nat.Prime.coprime_iff_not_dvd hxp]
    rw [Nat.prime_dvd_prime_iff_eq hxp (Nat.prime_of_mem_primeFactors y.2)]
    exact fun hc => hxy (Subtype.ext hc)
  have i_inj : ∀ a ha b hb, i a ha = i b hb → a = b := by
    intro a ha b hb hiab
    apply_fun Nat.factorization at hiab
    ext p hp
    obtain hiabp := DFunLike.ext_iff.mp hiab p
    rw [hfact_i a ha, hfact_i b hb, dif_pos hp, dif_pos hp] at hiabp
    exact hiabp
  have i_surj : ∀ (b : ℕ), b ∈ (d^M).divisors.filter (d ∣ ·) → ∃ a ha, i a ha = b := by
    intro b hb
    have h : (fun p _ => (Nat.factorization b) p) ∈
        Finset.pi d.primeFactors fun p => Finset.Icc 1 M := by
      rw [Finset.mem_pi]
      intro p hp
      rw [Finset.mem_Icc]
      rw [Finset.mem_filter] at hb
      have hb_ne_zero : b ≠ 0 := ne_of_gt <| Nat.pos_of_mem_divisors hb.1
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      constructor
      · rw [←Nat.Prime.dvd_iff_one_le_factorization hpp hb_ne_zero]
        · exact Trans.trans (Nat.dvd_of_mem_primeFactors hp) hb.2
      · rw [Nat.mem_divisors] at hb
        trans Nat.factorization (d^M) p
        · exact (Nat.factorization_le_iff_dvd hb_ne_zero hb.left.right).mpr hb.left.left p
        rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        have : d.factorization p ≤ 1 := by
          apply hd.natFactorization_le_one
        exact (mul_le_iff_le_one_right (Nat.pos_of_ne_zero hM)).mpr this
    use (fun p _ => Nat.factorization b p)
    use h
    apply Nat.eq_of_factorization_eq
    · apply hi_ne_zero _ h
    · exact ne_of_gt <| Nat.pos_of_mem_divisors (Finset.mem_filter.mp hb).1
    intro p
    rw [hfact_i (fun p _ => (Nat.factorization b) p) h p]
    rw [Finset.mem_filter, Nat.mem_divisors] at hb
    by_cases hp : p ∈ d.primeFactors
    · rw [dif_pos hp]
    · rw [dif_neg hp, eq_comm, Nat.factorization_eq_zero_iff, ←or_assoc]
      rw [Nat.mem_primeFactors] at hp
      left
      push Not at hp
      by_cases hpp : p.Prime
      · right
        intro hpb
        exact hd.ne_zero <| hp hpp (hpp.dvd_of_dvd_pow (hpb.trans hb.1.1))
      · left
        exact hpp
  exact Finset.sum_bij i hi i_inj i_surj h

theorem lem0 (P : ℕ) {s : Finset ℕ} (h : ∀ p ∈ s, p ∣ P) (h' : ∀ p ∈ s, p.Prime) :
    ∏ p ∈ s, p ∣ P := by
  simp_rw [Nat.prime_iff] at h'
  apply Finset.prod_primes_dvd _ h' h

lemma sqrt_le_self (x : ℝ) (hx : 1 ≤ x) : Real.sqrt x ≤ x := by
  refine Iff.mpr Real.sqrt_le_iff ?_
  constructor
  · linarith
  nlinarith [sq_nonneg (x - 1)]

lemma nat_squarefree_dvd_pow (a b N : ℕ) (ha : Squarefree a) (hab : a ∣ b ^ N) :
    a ∣ b := by
  by_cases hb : b = 0
  · rw [hb]
    exact Nat.dvd_zero a
  rw [← Nat.factorization_le_iff_dvd ha.ne_zero hb]
  intro p
  by_cases hp : p.Prime
  · by_cases hpa : p ∣ a
    · have hp_b : p ∣ b := hp.dvd_of_dvd_pow (hpa.trans hab)
      exact (ha.natFactorization_le_one p).trans
        ((hp.dvd_iff_one_le_factorization hb).mp hp_b)
    · rw [Nat.factorization_eq_zero_of_not_dvd hpa]
      exact zero_le
  · rw [Nat.factorization_eq_zero_of_not_prime a hp]
    exact zero_le

theorem selbergBoundingSum_ge_sum_div (s : SelbergSieve)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s.level → p ∣ s.prodPrimes)
    (hnu : CompletelyMultiplicative s.nu) (hnu_nonneg : ∀ n, 0 ≤ s.nu n)
    (hnu_lt : ∀ p, p.Prime → p ∣ s.prodPrimes → s.nu p < 1) :
    s.selbergBoundingSum ≥
      ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), s.nu m := by
  calc ∑ l ∈ s.prodPrimes.divisors, (if l ^ 2 ≤ s.level then s.selbergTerms l else 0)
     ≥ ∑ l ∈ s.prodPrimes.divisors.filter (fun l : ℕ => l ^ 2 ≤ s.level),
        ∑ m ∈ (l ^ Nat.floor s.level).divisors.filter (l ∣ ·), s.nu m := ?_
   _ ≥ ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), s.nu m := ?_
  · rw [← Finset.sum_filter]
    apply Finset.sum_le_sum
    intro l hl
    rw [Finset.mem_filter, Nat.mem_divisors] at hl
    have hlsq : Squarefree l := Squarefree.squarefree_of_dvd hl.1.1 s.prodPrimes_squarefree
    trans (∏ p ∈ l.primeFactors, ∑ n ∈ Finset.Icc 1 (Nat.floor s.level), s.nu (p ^ n))
    · rw [prod_factors_sum_pow_compMult (Nat.floor s.level) _ s.nu]
      · exact hnu
      · exact hlsq
      · rw [ne_eq, Nat.floor_eq_zero, not_lt]
        exact s.one_le_level
    · rw [s.selbergTerms_apply l]
      apply prod_factors_one_div_compMult_ge _ _ hnu _ _ hlsq
      · intro p hpp hpl
        apply hnu_lt p hpp (Trans.trans hpl hl.1.1)
      · exact hnu_nonneg
  rw [← Finset.sum_biUnion]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro m hm
      have hprod_pos : 0 < (∏ p ∈ m.primeFactors, p) := by
        apply Finset.prod_pos
        intro p hp
        exact Nat.pos_of_mem_primeFactors hp
      have hprod_ne_zero : (∏ p ∈ m.primeFactors, p) ^ ⌊s.level⌋₊ ≠ 0 :=
        pow_ne_zero _ (ne_of_gt hprod_pos)
      rw [Finset.mem_biUnion]
      simp_rw [Finset.mem_filter, Nat.mem_divisors]
      rw [Finset.mem_Icc, Nat.le_floor_iff (Real.sqrt_nonneg s.level)] at hm
      have hm_ne_zero : m ≠ 0 := by
        exact ne_of_gt <| Nat.succ_le_iff.mp hm.1
      use ∏ p ∈ m.primeFactors, p
      constructor
      · constructor
        · constructor
          · apply lem0 <;> intro p hp
            · apply hP p <| Nat.prime_of_mem_primeFactors hp
              trans (m : ℝ)
              · norm_cast
                exact Nat.le_of_mem_primeFactors hp
              trans (Real.sqrt s.level)
              · exact hm.2
              apply sqrt_le_self s.level s.one_le_level
            · exact Nat.prime_of_mem_primeFactors hp
          · exact s.prodPrimes_ne_zero
        · rw [← Real.sqrt_le_sqrt_iff (by linarith only [s.one_le_level]), Nat.cast_pow,
            Real.sqrt_sq]
          · trans (m : ℝ)
            · norm_cast
              apply Nat.le_of_dvd (Nat.succ_le_iff.mp hm.1)
              exact Nat.prod_primeFactors_dvd m
            · exact hm.2
          · apply le_of_lt
            norm_cast
      · constructor
        · constructor
          · rw [← Nat.factorization_le_iff_dvd _ hprod_ne_zero, Nat.factorization_pow]
            · intro p
              have hy_mul_prod_nonneg :
                  0 ≤ ⌊s.level⌋₊ * (Nat.factorization (∏ p ∈ m.primeFactors, p)) p :=
                zero_le
              trans (Nat.factorization m) p * 1
              · rw [mul_one]
              trans ⌊s.level⌋₊ * Nat.factorization (∏ p ∈ m.primeFactors, p) p
              swap
              · apply le_rfl
              by_cases hpp : p.Prime
              swap
              · rw [Nat.factorization_eq_zero_of_not_prime _ hpp, zero_mul]
                exact hy_mul_prod_nonneg
              by_cases hpdvd : p ∣ m
              swap
              · rw [Nat.factorization_eq_zero_of_not_dvd hpdvd, zero_mul]
                exact hy_mul_prod_nonneg
              apply mul_le_mul
              · trans m
                · exact le_of_lt <| Nat.factorization_lt p hm_ne_zero
                apply Nat.le_floor
                refine le_trans hm.2 ?_
                apply sqrt_le_self _ s.one_le_level
              · rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp <| ne_of_gt hprod_pos,
                  pow_one]
                apply Finset.dvd_prod_of_mem
                rw [Nat.mem_primeFactors]
                exact ⟨hpp, hpdvd, hm_ne_zero⟩
              · norm_num
              · norm_num
            · exact hm_ne_zero
          · exact hprod_ne_zero
        · exact Nat.prod_primeFactors_dvd m
    · intro i _ _
      apply hnu_nonneg
  · intro i hi j hj hij t hti htj x hx
    exfalso
    specialize hti hx
    specialize htj hx
    simp_rw [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at *
    have h : ∀ i j {n}, i ∣ s.prodPrimes → i ∣ x → x ∣ j ^ n → i ∣ j := by
      intro i j n hiP hix hij
      apply nat_squarefree_dvd_pow i j n (s.squarefree_of_dvd_prodPrimes hiP)
      exact Trans.trans hix hij
    have hidvdj : i ∣ j := by
      apply h i j hi.1.1 hti.2 htj.1.1
    have hjdvdi : j ∣ i := by
      apply h j i hj.1.1 htj.2 hti.1.1
    exact hij <| Nat.dvd_antisymm hidvdj hjdvdi

theorem boundingSum_ge_sum (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥
      ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), 1 / (m : ℝ) := by
  trans ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)),
      (ζ : ArithmeticFunction ℝ).pdiv .id m
  · rw [← hnu]
    apply selbergBoundingSum_ge_sum_div
    · intro p hpp hple
      apply hP p hpp hple
    · rw [hnu]
      exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id
    · intro n
      rw [hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp [h]
      · simp
    · intro p hpp _
      rw [hnu]
      simpa [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, if_neg hpp.ne_zero, ArithmeticFunction.id_apply,
        one_div] using
          (inv_lt_one_of_one_lt₀ (by norm_cast; exact hpp.one_lt) : (p : ℝ)⁻¹ < 1)
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mem_Icc] at hm
  simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_one,
    ArithmeticFunction.id_apply]

theorem boundingSum_ge_log (s : SelbergSieve) (hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id)
    (hP : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ s.level → p ∣ s.prodPrimes) :
    s.selbergBoundingSum ≥ Real.log (s.level) / 2 := by
  trans (∑ m ∈ Finset.Icc 1 (Nat.floor (Real.sqrt s.level)), 1 / (m : ℝ))
  · exact boundingSum_ge_sum s hnu hP
  trans (Real.log (Real.sqrt s.level))
  · rw [ge_iff_le]
    simp_rw [one_div]
    apply Aux.log_le_sum_inv (Real.sqrt s.level)
    rw [Real.le_sqrt] <;> linarith [s.one_le_level]
  · apply ge_of_eq
    refine Real.log_sqrt ?h.hx
    linarith [s.one_le_level]

theorem primeSieve_boundingSum_ge (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (primeSieve N y hy).selbergBoundingSum ≥ Real.log y / 2 := by
  apply boundingSum_ge_log
  · rfl
  · intro p hpp hp
    erw [prime_dvd_primorial_iff _ _ hpp]
    exact Nat.le_floor hp

theorem card_range_filter_dvd (N d : ℕ) (hd : d ≠ 0) :
    ((Finset.range N).filter (d ∣ ·)).card = Nat.ceil ((N : ℝ) / d) := by
  let f : (i : ℕ) → i < (Nat.ceil ((N : ℝ) / d)) → ℕ := fun i _ => d * i
  apply Finset.card_eq_of_bijective f
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    use k / d
    constructor
    · refine Nat.mul_div_cancel' hk.2
    · rw [Nat.lt_ceil]
      rw [Nat.cast_div hk.2 (by exact_mod_cast hd : (d : ℝ) ≠ 0)]
      exact div_lt_div_of_pos_right
        (by exact_mod_cast hk.1 : (k : ℝ) < N)
        (by norm_cast; exact Nat.pos_of_ne_zero hd)
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range]
    rw [Nat.lt_ceil, lt_div_iff₀ (by norm_cast; exact Nat.pos_of_ne_zero hd : (0 : ℝ) < d),
      mul_comm] at hk
    norm_cast at hk
    exact ⟨hk, dvd_mul_right ..⟩
  · exact fun _ _ _ _ hij => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd) hij

theorem primeSieve_multSum_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) (hd : d ≠ 0) :
    (primeSieve N y hy).multSum d = Nat.ceil (((N + 1 : ℕ) : ℝ) / d) := by
  unfold primeSieve
  simp only [Sieve.multSum, Finset.sum_boole, Nat.cast_inj]
  apply card_range_filter_dvd
  exact hd


theorem primeSieve_rem_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) (hd : d ≠ 0) :
    (primeSieve N y hy).rem d = Nat.ceil (((N + 1 : ℕ) : ℝ) / d) - N / d := by
  unfold Sieve.rem
  rw [primeSieve_multSum_eq (hd := hd)]
  unfold primeSieve
  rw [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply, if_neg hd]
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.id_apply]
  ring_nf

theorem primeSieve_abs_rem_eq (N : ℕ) (y : ℝ) (hy : 1 ≤ y) (d : ℕ) (hd : d ≠ 0) :
    |(primeSieve N y hy).rem d| ≤ 2 := by
  rw [primeSieve_rem_eq (hd:=hd), abs_le]
  constructor
  · apply le_sub_right_of_add_le
    trans ((N + 1) / ↑d)
    · rw [add_comm, add_div]
      have : 0 ≤ 1/(d:ℝ) := by
        norm_num
      linarith
    simpa [Nat.cast_add, Nat.cast_one] using Nat.le_ceil (((N + 1 : ℕ) : ℝ) / d)
  · apply sub_left_le_of_le_add
    trans ↑(Nat.floor ((N+1)/d:ℝ)+1)
    · norm_cast
      apply Nat.ceil_le_floor_add_one
    trans ((N+1)/d+1:ℝ)
    · push_cast
      have hfloor : (↑⌊(↑N + 1) / (d : ℝ)⌋₊ : ℝ) ≤ (↑N + 1) / (d : ℝ) := by
        exact Nat.floor_le
          (div_nonneg (by norm_cast; norm_num) (by norm_num) :
            0 ≤ ((↑N + 1) / (d : ℝ)))
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hfloor 1
    have : 1 / (d : ℝ) ≤ 1 := by
      rw [one_div]
      apply inv_le_one_of_one_le₀
      norm_cast
      linarith [Nat.pos_of_ne_zero hd]
    rw [add_div]
    linarith

open ArithmeticFunction

theorem rem_sum_le_of_const (s : SelbergSieve) (C : ℝ) (hrem : ∀ d > 0, |s.rem d| ≤ C) :
    ∑ d ∈ s.prodPrimes.divisors,
        (if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0)
      ≤ C * s.level * (1 + Real.log s.level) ^ 3 := by
  rw [← Finset.sum_filter]
  trans (∑ d ∈ Finset.filter (fun d : ℕ => ↑d ≤ s.level)
      (s.toSieve.prodPrimes.divisors), 3 ^ ω d * C)
  · gcongr with d hd
    · norm_cast
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    apply hrem d
    apply Nat.pos_of_ne_zero
    apply ne_zero_of_dvd_ne_zero hd.1.2 hd.1.1
  rw [← Finset.sum_mul, mul_comm, mul_assoc]
  gcongr
  · linarith [abs_nonneg <| s.rem 1, hrem 1 (by norm_num)]
  simp_rw [Nat.cast_pow]
  push_cast
  rw [Finset.sum_filter]
  apply Aux.sum_pow_cardDistinctFactors_le_self_mul_log_pow (hx := s.one_le_level)
  apply Sieve.prodPrimes_squarefree

theorem primeSieve_rem_sum_le (N : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    ∑ d ∈ (primeSieve N y hy).prodPrimes.divisors,
        (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * |(primeSieve N y hy).rem d| else 0)
      ≤ 2 * y * (1 + Real.log y) ^ 3 := by
  apply rem_sum_le_of_const
  intro d hd
  push_cast
  apply primeSieve_abs_rem_eq
  omega

theorem pi_le_of_y (N : ℕ) (y : ℝ) (hy_lt : 1 < y) :
    π N ≤ 2 * N / Real.log y + 3 * y * (1 + Real.log y) ^ 3 := by
  have hy : 1 ≤ y := le_of_lt hy_lt
  trans ((primeSieve N y hy).siftedSum + y)
  · apply pi_le_siftedSum
  suffices Sieve.siftedSum (primeSieve N y hy).toSieve ≤
      2 * N / Real.log y + 2 * y * (1 + Real.log y) ^ 3 by
    push_cast at *
    have : y * (1 : ℝ) ≤ y * (1 + Real.log y) ^ 3 := by
      have hy_nonneg : 0 ≤ y := by linarith
      have hbase : (1 : ℝ) ≤ 1 + Real.log y := by linarith [Real.log_nonneg hy]
      have hpow : (1 : ℝ) ≤ (1 + Real.log y)^3 := one_le_pow₀ hbase
      have hdiff : (0 : ℝ) ≤ y * ((1 + Real.log y)^3 - 1) :=
        mul_nonneg hy_nonneg (sub_nonneg.mpr hpow)
      nlinarith
    rw [mul_one] at this
    linarith
  trans ((primeSieve N y hy).totalMass / (primeSieve N y hy).selbergBoundingSum) +
      ∑ d ∈ (primeSieve N y hy).prodPrimes.divisors,
        (if (d : ℝ) ≤ y then (3 : ℝ) ^ ω d * |(primeSieve N y hy).rem d| else 0)
  · apply (SelbergSieve.selberg_bound_simple)
  gcongr (?_ + ?_)
  · trans (N / (Real.log y / 2))
    · gcongr (?_ / ?_)
      · linarith [Real.log_pos hy_lt]
      · rfl
      rw [←ge_iff_le]
      apply primeSieve_boundingSum_ge
    rw [div_eq_mul_inv, inv_div, ←mul_div_assoc, mul_comm]
    push_cast
    rfl
  · apply primeSieve_rem_sum_le

lemma primeCounting_zero :
  π 0 = 0 := by decide
lemma primeCounting_one :
  π 1 = 0 := by decide

theorem loglog_nonneg (x : ℝ) (hx : 3 ≤ x) :
    0 ≤ Real.log (Real.log x) := by
  apply Real.log_nonneg
  rw [← Real.log_exp 1]
  gcongr
  trans 3
  · have := Real.exp_one_lt_d9
    trans (2.7182818286)
    · linarith [Real.exp_one_lt_d9]
    · norm_num
  · exact hx

theorem loglog_bigO_log :
    (fun N : ℕ => Real.log (Real.log N)) =O[Filter.atTop] (fun N : ℕ => Real.log N) := by
  apply Asymptotics.IsBigO.of_bound'
  rw [Filter.eventually_iff, Filter.mem_atTop_sets]
  use 10
  intro x hx; simp only [Real.norm_eq_abs, Set.mem_setOf_eq]
  rw [←Nat.cast_le (α:=ℝ)] at hx
  conv at hx => {lhs; norm_num}
  rw [le_abs]; left
  rw [abs_le]
  constructor
  · linarith only [Real.log_natCast_nonneg x, loglog_nonneg x (by linarith)]
  linarith [Real.log_le_sub_one_of_pos (x:= Real.log x) (Real.log_pos (by linarith))]


theorem _lemma5 : (Real.log ∘ Real.log) =o[Filter.atTop] Real.log := by
  simpa [Function.comp_def] using
    Asymptotics.IsLittleO.comp_tendsto Real.isLittleO_log_id_atTop Real.tendsto_log_atTop

theorem _lemma4 :
    (fun N : ℕ => Real.log (Real.log N)) =o[Filter.atTop] (fun N : ℕ => Real.log N) := by
  exact Asymptotics.IsLittleO.comp_tendsto _lemma5 tendsto_natCast_atTop_atTop

theorem _lemma3 (c : ℝ) :
    (fun N : ℕ => Real.log N) =O[Filter.atTop]
      (fun N : ℕ => Real.log N - c * Real.log (Real.log N)) := by
  exact (_lemma4.const_mul_left c).right_isBigO_sub

theorem _lemma2 (c : ℝ) :
    (fun N : ℕ => Real.log N + c * Real.log (Real.log N)) =O[Filter.atTop]
      (fun N : ℕ => Real.log N) := by
  apply Asymptotics.IsBigO.add
  · exact Asymptotics.isBigO_refl _ _
  apply Asymptotics.IsBigO.const_mul_left
  apply loglog_bigO_log

theorem pi_le_id_div_log_of_eps (N : ℕ) (ε : ℝ) (_hε_pos : ε > 0) (hε : ε < 1) :
    π N ≤ 2 / (1 - ε) * N / Real.log N +
      3 * (N : ℝ) ^ (1 - ε) * (1 + (1 - ε) * Real.log N) ^ 3 := by
  by_cases hN : N = 0
  · rw [hN, primeCounting_zero]
    norm_num
    rw [Real.zero_rpow (by linarith : 1 - ε ≠ 0)]
  by_cases hN_one : N = 1
  · rw [hN_one, primeCounting_one]
    norm_num
  · have : 1 < (N : ℝ) ^ (1 - ε) := by
      apply Real.one_lt_rpow
      · norm_cast
        rw [Nat.one_lt_iff_ne_zero_and_ne_one]
        exact ⟨hN, hN_one⟩
      · linarith
    have h := pi_le_of_y N ((N : ℝ) ^ (1 - ε)) this
    rw [Real.log_rpow (by norm_cast; exact Nat.pos_of_ne_zero hN)] at h
    apply le_trans h
    gcongr (?_ + ?_)
    · apply le_of_eq
      field_simp
      ring_nf
    · exact le_refl _

theorem pi_le_id_div_log (N : ℕ) :
    π N ≤ (4 : ℝ) * N / Real.log N +
      (3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log N) ^ 3 := by
  have h := pi_le_id_div_log_of_eps N (1 / 2) (by linarith) (by linarith)
  apply le_trans h
  gcongr ?_ + ?_
  · norm_num
  · norm_num

theorem _lemma0 :
    (fun N : ℕ => 4 * N / Real.log N) =O[Filter.atTop]
      fun N : ℕ => N / Real.log N := by
  simp_rw [mul_div_assoc]
  apply Asymptotics.IsBigO.const_mul_left
  exact Asymptotics.isBigO_refl _ _

theorem _lemma7 :
    ((fun x : ℝ => 1 + 1 / 2 * Real.log x) ∘ fun N : ℕ => (N : ℝ)) =O[Filter.atTop]
      ((fun x : ℝ => x ^ (1 / 12 : ℝ)) ∘ fun N : ℕ => ↑N) := by
  apply Asymptotics.IsBigO.comp_tendsto (l := Filter.atTop)
  · apply Asymptotics.IsBigO.add
    · apply Asymptotics.IsBigO.of_bound'
      rw [Filter.eventually_iff, Filter.mem_atTop_sets]
      use 1
      intro x hx
      simp only [norm_one, Real.norm_eq_abs, Set.mem_setOf_eq]
      rw [Real.abs_rpow_of_nonneg (by linarith)]
      apply Real.one_le_rpow
      · rw [le_abs]
        left
        linarith
      · norm_num
    · apply (isLittleO_log_rpow_atTop (by norm_num)).isBigO.const_mul_left _
  · exact tendsto_natCast_atTop_atTop

theorem _lemma8 :
    ((fun x : ℝ => x ^ (1 / 2 : ℝ) * x ^ (1 / 4 : ℝ)) ∘ fun N : ℕ => (N : ℝ))
      =O[Filter.atTop] ((fun x : ℝ => x / Real.log x) ∘ fun N : ℕ => ↑N) := by
  apply Asymptotics.IsBigO.comp_tendsto (l := Filter.atTop)
  · simp_rw [div_eq_mul_inv]
    trans (fun x => x * x ^ (-1 / 4 : ℝ))
    · apply Asymptotics.IsBigO.of_bound'
      rw [Filter.eventually_iff, Filter.mem_atTop_sets]
      use 1
      intro x hx
      simp only [norm_mul, Real.norm_eq_abs, Set.mem_setOf_eq]
      rw [← abs_mul, ← abs_mul]
      apply le_of_eq
      apply congr_arg
      trans (x ^ (1 : ℝ) * x ^ (-1 / 4 : ℝ))
      · rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]
        norm_num
      · rw [Real.rpow_one]
    · apply Asymptotics.IsBigO.mul
      · apply Asymptotics.isBigO_refl
      trans (fun x => (x ^ (1 / 4 : ℝ))⁻¹)
      · apply Asymptotics.IsBigO.of_bound'
        rw [Filter.eventually_iff, Filter.mem_atTop_sets]
        use 1
        intro x hx
        simp only [Real.norm_eq_abs, Set.mem_setOf_eq]
        rw [neg_div, Real.rpow_neg (by linarith : 0 ≤ x), abs_inv]
      apply Asymptotics.IsBigO.inv_rev
      · apply (isLittleO_log_rpow_atTop (by norm_num)).isBigO
      · rw [Filter.eventually_iff, Filter.mem_atTop_sets]
        use 100
        intro x hx
        rw [Set.mem_setOf_eq]
        intro hlog
        exfalso
        have hlog_pos : 0 < Real.log x := Real.log_pos (by linarith)
        linarith
  · exact tendsto_natCast_atTop_atTop

theorem _lemma1 :
    (fun N : ℕ => (3 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) *
      (1 + (1 / 2) * Real.log N) ^ 3) =O[Filter.atTop]
      fun N : ℕ => N / Real.log N := by
  simp_rw [mul_assoc]
  apply Asymptotics.IsBigO.const_mul_left
  trans (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (1 / 4 : ℝ))
  · have h0 : (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) =O[Filter.atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 / 2 : ℝ)) := by
      apply Asymptotics.isBigO_refl
    have h1 : (fun N : ℕ => (1 + 1 / 2 * Real.log N) ^ 3) =O[Filter.atTop]
        (fun N : ℕ => (N : ℝ) ^ (1 / 4 : ℝ)) := by
      trans (fun N : ℕ => ((N : ℝ) ^ (1 / 12 : ℝ)) ^ 3)
      · apply Asymptotics.IsBigO.pow
        apply _lemma7
      · simp_rw [← Real.rpow_natCast]
        conv => { lhs; ext N; rw [← Real.rpow_mul (Nat.cast_nonneg N)] }
        norm_num
        apply Asymptotics.isBigO_refl
    apply h0.mul h1
  · apply _lemma8

lemma _lemma9 :
    (fun N : ℕ => (π N : ℝ)) =O[Filter.atTop]
      (fun N : ℕ => 4 * N / Real.log N +
        3 * (N : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log N) ^ 3) := by
  apply Asymptotics.isBigO_of_le
  intro N
  simp_rw [RCLike.norm_natCast, Nat.cast_ofNat, Real.norm_eq_abs]
  apply le_trans _ (le_abs_self _)
  apply pi_le_id_div_log N


theorem pi_ll :
    (fun N : ℕ => (π N : ℝ)) =O[Filter.atTop] (fun N : ℕ => N / Real.log N) := by
  trans (fun N : ℕ => 4 * N / Real.log N +
      3 * (N : ℝ) ^ (1 / 2 : ℝ) * (1 + (1 / 2) * Real.log N) ^ 3)
  · exact _lemma9
  · apply Asymptotics.IsBigO.add
    · simp_rw [mul_div_assoc]
      apply Asymptotics.IsBigO.const_mul_left
      apply Asymptotics.isBigO_refl
    · apply _lemma1

theorem pi_le_mul : ∃ N C, ∀ n ≥ N, π n ≤ C*n/Real.log n := by
  obtain ⟨C, h⟩ := pi_ll.bound
  rw [Filter.eventually_iff, Filter.mem_atTop_sets] at h
  obtain ⟨N, h⟩ := h
  simp only [RCLike.norm_natCast, norm_div, Real.norm_eq_abs, Set.mem_setOf_eq] at h
  use N
  use C
  intro n
  specialize h n
  rw [abs_of_nonneg (Real.log_natCast_nonneg n)] at h
  intro hnN
  rw [mul_div_assoc]
  apply h (by linarith only [hnN])

end PrimeUpperBound
end
