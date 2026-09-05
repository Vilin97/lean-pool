/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Statement.Definitions
import LeanPool.KasamiCyclicAdditive.Phase.AdditiveCharacter
import LeanPool.KasamiCyclicAdditive.MCM.FrobeniusSum

/-!
# The MCM half-space packet

Derives the Muller--Cohen--Matthews parametrization of the Kasami derivative
image `Δ` algebraically, then uses the derivative-image half-size equation to
convert sums over the image into Artin--Schreier half-space sums. No APN or
two-to-one theorem for the Kasami derivative is imported.

Writing `A(b) = b² + b` for the Artin--Schreier map, `T_k(s) = ∑_{i<k} s^(2^i)`
and `M_k(s) = T_k(s)^(2^k+1) / s^(2^k)` for the MCM map, the main identities are

* `δ(b) = M_k(A(b))`, so `Δ` is the image of the Artin--Schreier image under
  `M_k`;
* the Artin--Schreier image is exactly the kernel of the canonical trace
  character, and has half the elements of `K`;
* consequently sums over `Δ` are half-space sums weighted by `1 + ψ(s)`.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- Artin--Schreier map in characteristic two. -/
def artinSchreier (b : K) : K := b ^ 2 + b

/-- Artin--Schreier image. -/
def asSet (K : Type*) [Field K] [Fintype K] [DecidableEq K] : Finset K :=
  Finset.image artinSchreier Finset.univ

/-- MCM map, with Lean's field convention making `M_k(0)=0`. -/
def mcmMap (k : ℕ) (s : K) : K :=
  frobSum k s ^ (2 ^ k + 1) / s ^ (2 ^ k)

/-! ### Traces of finite fields are Frobenius invariant -/

/-- The trace of a finite extension is invariant under the `#F`-power Frobenius. -/
theorem trace_pow_natCard {F L : Type*} [Field F] [Field L] [Finite L] [Algebra F L]
    (x : L) : Algebra.trace F L (x ^ Nat.card F) = Algebra.trace F L x := by
  have : Finite F := Finite.of_injective _ (FaithfulSMul.algebraMap_injective F L)
  cases nonempty_fintype F
  cases nonempty_fintype L
  apply FaithfulSMul.algebraMap_injective F L
  rw [FiniteField.algebraMap_trace_eq_sum_pow, FiniteField.algebraMap_trace_eq_sum_pow]
  set q := Nat.card F with hq
  set n := Module.finrank F L with hn
  have hcard : Nat.card L = q ^ n := by
    simp only [hq, hn, Nat.card_eq_fintype_card]
    exact Module.card_eq_pow_finrank
  have hxq : x ^ q ^ n = x := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact FiniteField.pow_card x
  have h1 : ∀ i, (x ^ q) ^ q ^ i = x ^ q ^ (i + 1) := by
    intro i; rw [← pow_mul, pow_succ']
  simp only [h1]
  have h2 := Finset.sum_range_succ' (fun i => x ^ q ^ i) n
  have h3 := Finset.sum_range_succ (fun i => x ^ q ^ i) n
  rw [h3, hxq, pow_zero, pow_one] at h2
  exact add_right_cancel h2.symm

/-- Congruence for an additive character after precomposition. -/
private lemma addChar_comp_congr {A B M : Type*} [AddMonoid A] [AddMonoid B] [Monoid M]
    (ψ : AddChar B M) (f : A →+ B) {a b : A} (h : f a = f b) :
    ψ.compAddMonoidHom f a = ψ.compAddMonoidHom f b := by
  rw [AddChar.compAddMonoidHom_apply, AddChar.compAddMonoidHom_apply, h]

omit [DecidableEq K] in
/-- In characteristic two the canonical trace character is invariant
under squaring. -/
theorem primitiveAddChar_sq (x : K) :
    primitiveAddChar K (x ^ 2) = primitiveAddChar K x := by
  have hrc : ringChar K = 2 := ringChar.eq K 2
  have hcp : CharP K (ringChar K) := ringChar.charP K
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  let : Algebra (ZMod (ringChar K)) K := ZMod.algebra _ _
  have hcard : Nat.card (ZMod (ringChar K)) = 2 := by rw [hrc]; simp
  have h : Algebra.trace (ZMod (ringChar K)) K (x ^ 2)
      = Algebra.trace (ZMod (ringChar K)) K x := by
    have := trace_pow_natCard (F := ZMod (ringChar K)) (L := K) x
    rwa [hcard] at this
  unfold primitiveAddChar AddChar.FiniteField.primitiveChar_to_Complex
    AddChar.FiniteField.primitiveChar
  simp only [MonoidHom.compAddChar_apply, Function.comp_apply]
  exact congrArg _ (addChar_comp_congr _ _ h)

/-! ### The algebraic MCM identity -/

omit [Fintype K] [DecidableEq K] in
/-- The Artin--Schreier map telescopes the Frobenius sum. -/
theorem frobSum_artinSchreier (k : ℕ) (b : K) :
    frobSum k (artinSchreier b) = b ^ (2 ^ k) + b := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  induction k with
  | zero => simp [frobSum, artinSchreier]; linear_combination (-b) * h2
  | succ n ih =>
      rw [frobSum, Finset.sum_range_succ, ← frobSum, ih]
      have h : (artinSchreier b) ^ (2 ^ n) = b ^ (2 ^ (n + 1)) + b ^ (2 ^ n) := by
        rw [artinSchreier, add_pow_char_pow, ← pow_mul, ← pow_succ']
      rw [h]
      linear_combination (b ^ (2 ^ n)) * h2

/-- The exponent arithmetic behind the cleared-denominator MCM identity. -/
private lemma kasamiExponent_add_two_pow (k : ℕ) :
    kasamiExponent k + 2 ^ k = 4 ^ k + 1 := by
  have hle : 2 ^ k ≤ 4 ^ k := Nat.pow_le_pow_left (by norm_num) k
  simp only [kasamiExponent]
  omega

omit [Fintype K] [DecidableEq K] in
/-- The cleared-denominator form of the MCM identity. -/
theorem kasamiDerivative_mul_artinSchreier_pow (k : ℕ) (b : K) :
    kasamiDerivative k b * (artinSchreier b) ^ (2 ^ k)
      = (frobSum k (artinSchreier b)) ^ (2 ^ k + 1) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hexp := kasamiExponent_add_two_pow k
  have h4 : (4 : ℕ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  set A := b ^ (2 ^ k) with hA
  set B := b ^ (4 ^ k) with hB
  have hA1 : (b + 1) ^ (2 ^ k) = A + 1 := by rw [hA, add_pow_char_pow, one_pow]
  have hB1 : (b + 1) ^ (4 ^ k) = B + 1 := by rw [hB, h4, add_pow_char_pow, one_pow]
  have hBA : A ^ (2 ^ k) = B := by rw [hA, hB, ← pow_mul, ← pow_add, h4, two_mul]
  have hAS : (artinSchreier b) ^ (2 ^ k) = A * (A + 1) := by
    rw [artinSchreier, add_pow_char_pow, ← pow_mul, hA,
      show (2 : ℕ) * 2 ^ k = 2 ^ k * 2 by ring, pow_mul]
    ring
  have e1 : (b + 1) ^ kasamiExponent k * (A + 1) = (B + 1) * (b + 1) := by
    rw [← hA1, ← pow_add, hexp, pow_succ, hB1]
  have e2 : b ^ kasamiExponent k * A = B * b := by
    rw [hA, ← pow_add, hexp, pow_succ, ← hB]
  have hfs : frobSum k (artinSchreier b) = A + b := by rw [frobSum_artinSchreier]
  have hrhs : (A + b) ^ (2 ^ k + 1) = (B + A) * (A + b) := by
    rw [pow_succ, add_pow_char_pow, hBA, hA]
  rw [hfs, hrhs, hAS, kasamiDerivative]
  calc ((b + 1) ^ kasamiExponent k + b ^ kasamiExponent k + 1) * (A * (A + 1))
      = A * ((b + 1) ^ kasamiExponent k * (A + 1)) + (A + 1) * (b ^ kasamiExponent k * A)
        + A * (A + 1) := by ring
    _ = A * ((B + 1) * (b + 1)) + (A + 1) * (B * b) + A * (A + 1) := by rw [e1, e2]
    _ = (B + A) * (A + b) := by linear_combination (A * B * b + A) * h2

omit [Fintype K] [DecidableEq K] in
/-- The algebraic MCM identity.  This includes the `b=0,1` denominator
cases; no nonzero hypothesis on `b^2+b` is assumed. -/
theorem kasamiDerivative_eq_mcmMap (k : ℕ) (b : K) :
    kasamiDerivative k b = mcmMap k (artinSchreier b) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hd : kasamiExponent k ≠ 0 := by simp [kasamiExponent]
  by_cases h : artinSchreier b = 0
  · rw [mcmMap, h, zero_pow (by positivity), div_zero]
    have hb : b = 0 ∨ b = 1 := by
      have hbb : b * (b + 1) = 0 := by rw [artinSchreier] at h; linear_combination h
      rcases mul_eq_zero.mp hbb with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by linear_combination h' - h2)
    rcases hb with rfl | rfl
    · rw [kasamiDerivative, zero_pow hd, zero_add, one_pow]
      linear_combination h2
    · rw [kasamiDerivative, one_pow]
      have h11 : (1 : K) + 1 = 0 := by linear_combination h2
      rw [h11, zero_pow hd]
      linear_combination h2
  · rw [mcmMap, eq_div_iff (pow_ne_zero _ h)]
    exact kasamiDerivative_mul_artinSchreier_pow k b

/-! ### The half-space sum -/

omit [Fintype K] [DecidableEq K] in
/-- The Artin--Schreier map is exactly two-to-one. -/
theorem artinSchreier_eq_iff (a b : K) :
    artinSchreier a = artinSchreier b ↔ a = b ∨ a = b + 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  constructor
  · intro h
    have hz : (a + b) * (a + b + 1) = 0 := by
      rw [artinSchreier, artinSchreier] at h
      linear_combination h + (a * b + b ^ 2 + b) * h2
    rcases mul_eq_zero.mp hz with h' | h'
    · exact Or.inl (by linear_combination h' - b * h2)
    · exact Or.inr (by linear_combination h' - (b + 1) * h2)
  · rintro (rfl | rfl)
    · rfl
    · rw [artinSchreier, artinSchreier]; linear_combination (b + 1) * h2

/-- Every fiber of the Artin--Schreier map is a two-element set `{b, b+1}`. -/
private lemma artinSchreier_fiber (b : K) :
    univ.filter (fun a => artinSchreier a = artinSchreier b) = {b, b + 1} := by
  ext a
  simp [artinSchreier_eq_iff]

/-- The Artin--Schreier image has exactly half of the elements of `K`. -/
theorem card_asSet : 2 * (asSet K).card = Fintype.card K := by
  have hmem : ∀ x ∈ (univ : Finset K), artinSchreier x ∈ asSet K := by
    intro x _; simp [asSet]
  have h := Finset.card_eq_sum_card_fiberwise hmem
  have hfib : ∀ t ∈ asSet K,
      (univ.filter (fun a => artinSchreier a = t)).card = 2 := by
    intro t ht
    simp only [asSet, Finset.mem_image] at ht
    obtain ⟨b, -, rfl⟩ := ht
    rw [artinSchreier_fiber, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      intro hb
      exact one_ne_zero (by linear_combination -hb : (1 : K) = 0)), Finset.card_singleton]
  rw [Finset.sum_congr rfl hfib] at h
  simp [Finset.card_univ, mul_comm] at h ⊢
  omega

omit [DecidableEq K] in
/-- Character values in characteristic two are square roots of `1`. -/
private lemma primitiveAddChar_mul_self (s : K) :
    primitiveAddChar K s * primitiveAddChar K s = 1 := by
  rw [← AddChar.map_add_eq_mul, CharTwo.add_self_eq_zero, AddChar.map_zero_eq_one]

omit [DecidableEq K] in
/-- The Artin--Schreier image lies in the kernel of the trace character. -/
theorem primitiveAddChar_artinSchreier (b : K) :
    primitiveAddChar K (artinSchreier b) = 1 := by
  rw [artinSchreier, AddChar.map_add_eq_mul, primitiveAddChar_sq, primitiveAddChar_mul_self]

omit [DecidableEq K] in
/-- Off its kernel the trace character takes the value `-1`. -/
private lemma primitiveAddChar_eq_neg_one {s : K} (h : primitiveAddChar K s ≠ 1) :
    primitiveAddChar K s = -1 := by
  have h1 := primitiveAddChar_mul_self (K := K) s
  have hz : (primitiveAddChar K s - 1) * (primitiveAddChar K s + 1) = 0 := by
    linear_combination h1
  rcases mul_eq_zero.mp hz with h' | h'
  · exact absurd (sub_eq_zero.mp h') h
  · linear_combination h'

omit [DecidableEq K] in
/-- The weight `1 + ψ(s)` vanishes off the kernel of the primitive additive character. -/
private lemma sum_one_add_char_mul_eq_zero (g : K → ℂ) :
    ∑ s ∈ univ.filter (fun s => ¬ primitiveAddChar K s = 1),
      (1 + primitiveAddChar K s) * g s = 0 := by
  refine Finset.sum_eq_zero (fun s hs => ?_)
  rw [primitiveAddChar_eq_neg_one (Finset.mem_filter.mp hs).2]
  ring

omit [DecidableEq K] [CharP K 2] in
/-- Orthogonality evaluates the total half-space weight. -/
private lemma sum_one_add_primitiveAddChar_eq_card :
    ∑ s : K, (1 + primitiveAddChar K s) = (Fintype.card K : ℂ) := by
  rw [Finset.sum_add_distrib,
    AddChar.sum_eq_zero_of_ne_one (ne_one_of_isPrimitive primitiveAddChar_isPrimitive)]
  simp [Finset.card_univ]

/-- Artin--Schreier trace-zero criterion: the Artin--Schreier image is exactly the
kernel of the trace character. -/
theorem asSet_eq_kernel :
    asSet K = univ.filter (fun s => primitiveAddChar K s = 1) := by
  have hsub : asSet K ⊆ univ.filter (fun s => primitiveAddChar K s = 1) := by
    intro t ht
    simp only [asSet, Finset.mem_image] at ht
    obtain ⟨b, -, rfl⟩ := ht
    simp [primitiveAddChar_artinSchreier]
  have hsum : ∑ s : K, (1 + primitiveAddChar K s)
      = 2 * ((univ.filter (fun s => primitiveAddChar K s = 1)).card : ℂ) := by
    rw [← Finset.sum_filter_add_sum_filter_not univ (fun s => primitiveAddChar K s = 1)]
    have h1 : ∑ s ∈ univ.filter (fun s => primitiveAddChar K s = 1),
        (1 + primitiveAddChar K s)
          = 2 * ((univ.filter (fun s => primitiveAddChar K s = 1)).card : ℂ) := by
      rw [Finset.sum_congr rfl (fun s hs => by rw [(Finset.mem_filter.mp hs).2]),
        Finset.sum_const, nsmul_eq_mul]
      ring
    have h0 := sum_one_add_char_mul_eq_zero (K := K) (fun _ => (1 : ℂ))
    simp only [mul_one] at h0
    rw [h1, h0, add_zero]
  have hcardK : 2 * (univ.filter (fun s => primitiveAddChar K s = 1)).card
      = Fintype.card K := by
    have hc : (2 * ((univ.filter (fun s => primitiveAddChar K s = 1)).card : ℂ))
        = (Fintype.card K : ℂ) := by rw [← hsum, sum_one_add_primitiveAddChar_eq_card]
    exact_mod_cast hc
  have hA := card_asSet (K := K)
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

/-- The derivative image is the image of the Artin--Schreier image under the MCM map. -/
theorem derivativeImage_eq_image (k : ℕ) :
    derivativeImage k K = Finset.image (mcmMap k) (asSet K) := by
  rw [derivativeImage, asSet, Finset.image_image]
  exact Finset.image_congr (fun x _ => kasamiDerivative_eq_mcmMap k x)

/-- Under half-size, `mcmMap` transfers sums over the derivative image to sums over the
Artin--Schreier image. -/
private lemma sum_derivativeImage_eq_sum_asSet {k : ℕ}
    (hhalf : 2 * (derivativeImage k K).card = Fintype.card K) (f : K → ℂ) :
    ∑ t ∈ derivativeImage k K, f t = ∑ s ∈ asSet K, f (mcmMap k s) := by
  have hA := card_asSet (K := K)
  have himg := derivativeImage_eq_image (K := K) k
  have hcards : (Finset.image (mcmMap k) (asSet K)).card = (asSet K).card := by
    rw [← himg]
    omega
  have hinj : Set.InjOn (mcmMap k) (↑(asSet K) : Set K) :=
    Finset.card_image_iff.mp hcards
  rw [himg, Finset.sum_image hinj]

/-- The MCM half-space identity, in the form consumed by the Fourier
argument.

`hhalf` is the half-size fact for the derivative image, and it is enough:
`kasamiDerivative_eq_mcmMap` gives a surjection `asSet → derivativeImage`, the
Artin--Schreier map has two-element fibers, so `|asSet| = |K|/2`, and the two
equal-size sets are therefore in bijection under `mcmMap`.  Moreover `asSet` is
exactly the kernel of `primitiveAddChar`, and every value of an additive
character on a characteristic-two group squares to `1`, so the weight
`1 + ψ(s)` is `2` on `asSet` and `0` off it. -/
theorem mcm_halfspace_sum
    {k : ℕ} (hhalf : 2 * (derivativeImage k K).card = Fintype.card K)
    (f : K → ℂ) :
    (2 : ℂ) * (∑ t ∈ derivativeImage k K, f t)
      = ∑ s : K, (1 + primitiveAddChar K s) * f (mcmMap k s) := by
  have hsum := sum_derivativeImage_eq_sum_asSet hhalf f
  have hker := asSet_eq_kernel (K := K)
  have hzero := sum_one_add_char_mul_eq_zero (K := K) (fun s => f (mcmMap k s))
  calc (2 : ℂ) * (∑ t ∈ derivativeImage k K, f t)
      = ∑ s ∈ asSet K, (1 + primitiveAddChar K s) * f (mcmMap k s) := by
        rw [hsum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s hs => ?_)
        rw [hker] at hs
        rw [(Finset.mem_filter.mp hs).2]
        ring
    _ = ∑ s : K, (1 + primitiveAddChar K s) * f (mcmMap k s) := by
        rw [hker, ← Finset.sum_filter_add_sum_filter_not univ
          (fun s => primitiveAddChar K s = 1)
          (fun s => (1 + primitiveAddChar K s) * f (mcmMap k s)), hzero, add_zero]

end KasamiCyclicAdditive
