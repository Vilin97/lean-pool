/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.IdealPrimeFactorization
public import LeanPool.Odlyzko.DedekindZeta.IdealSeries
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealFactor
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealSummability
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Logic.Equiv.Set
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Nat
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

namespace NumberField.Odlyzko

variable {α β E : Type*}

/-- An extend by zero used in the Odlyzko-bound argument. -/
noncomputable def extendByZero [AddCommMonoid E] (e : α → β) (f : α → E) (b : β) : E :=
  Function.extend e f 0 b

lemma extendByZero_apply [AddCommMonoid E] (e : α → β) (he : Function.Injective e)
    (f : α → E) (a : α) :
    extendByZero e f (e a) = f a := by
  exact he.extend_apply f 0 a

lemma extendByZero_eq_zero_of_not_mem_range [AddCommMonoid E] (e : α → β) (f : α → E)
    {b : β} (hb : b ∉ Set.range e) :
    extendByZero e f b = 0 := by
  exact Function.extend_apply' (f := e) f 0 b hb

theorem hasSum_extendByZero [AddCommMonoid E] [TopologicalSpace E]
    (e : α → β) (he : Function.Injective e)
    {f : α → E} {a : E} (hf : HasSum f a) :
    HasSum (extendByZero e f) a := by
  unfold extendByZero
  simp_all

theorem summable_extendByZero [AddCommMonoid E] [TopologicalSpace E]
    (e : α → β) (he : Function.Injective e)
    {f : α → E} (hf : Summable f) :
    Summable (extendByZero e f) := by
  unfold extendByZero
  simp_all

end NumberField.Odlyzko

section

open Complex Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem absNorm_idealOfPrimeFactors
    (m : Multiset (HeightOneSpectrum (𝓞 K))) :
    absNorm (idealOfPrimeFactors K m : Ideal (𝓞 K)) =
      (m.map (primeIdealNorm K)).prod := by
  rw [idealOfPrimeFactors_coe, map_multiset_prod]
  rw [Multiset.map_map]
  rfl

theorem inverseNormPower_idealOfPrimeFactors
    (m : Multiset (HeightOneSpectrum (𝓞 K))) (s : ℂ) :
    ((absNorm (idealOfPrimeFactors K m : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      (m.map (fun P ↦ inverseNormPower (primeIdealNorm K P) s)).prod := by
  rw [absNorm_idealOfPrimeFactors]
  induction m using Multiset.induction_on with
  | empty => simp
  | cons P m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      rw [Nat.cast_mul]
      rw [show
        ((primeIdealNorm K P : ℂ) *
            ((m.map (primeIdealNorm K)).prod : ℂ)) ^ (-s) =
          (primeIdealNorm K P : ℂ) ^ (-s) *
            ((m.map (primeIdealNorm K)).prod : ℂ) ^ (-s) by
        simpa only [ofReal_natCast] using mul_cpow_ofReal_nonneg
          (Nat.cast_nonneg (primeIdealNorm K P))
          (Nat.cast_nonneg (m.map (primeIdealNorm K)).prod) (-s)]
      rw [ih]
      rfl

theorem inverseNormPower_nonzeroIdealEquivPrimeFactors
    (I : NonzeroIdeal K) (s : ℂ) :
    ((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      ((nonzeroIdealEquivPrimeFactors K I).map
        (fun P ↦ inverseNormPower (primeIdealNorm K P) s)).prod := by
  rw [← inverseNormPower_idealOfPrimeFactors]
  congr 2
  exact congr_arg absNorm
    (congr_arg Subtype.val
      ((nonzeroIdealEquivPrimeFactors K).left_inv I).symm)

end NumberField.Odlyzko

end

namespace NumberField.Odlyzko

variable {M : Type*} [CommMonoidWithZero M]

/-- A prime value hom used in the Odlyzko-bound argument. -/
noncomputable def primeValueHom (a : ℕ → M) : ℕ →*₀ M where
  toFun n :=
    if n = 0 then 0 else
      n.factorization.prod fun p e ↦ a p ^ e
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    simp only [hm, hn, mul_ne_zero hm hn, ↓reduceIte]
    rw [Nat.factorization_mul hm hn]
    exact Finsupp.prod_add_index'
      (f := m.factorization) (g := n.factorization)
      (h := fun p e ↦ a p ^ e)
      (fun p ↦ pow_zero (a p))
      (fun p e₁ e₂ ↦ pow_add (a p) e₁ e₂)

@[simp] theorem primeValueHom_one (a : ℕ → M) :
    primeValueHom a 1 = 1 :=
  map_one _

@[simp] theorem primeValueHom_apply_of_prime (a : ℕ → M) {p : ℕ}
    (hp : p.Prime) :
    primeValueHom a p = a p := by
  rw [primeValueHom]
  simp [hp.ne_zero, hp.factorization]

@[simp] theorem primeValueHom_apply_prime_subtype (a : ℕ → M)
    (p : Nat.Primes) :
    primeValueHom a p = a p :=
  primeValueHom_apply_of_prime a p.prop

theorem primeValueHom_multiset_prod_of_prime (a : ℕ → M)
    {m : Multiset ℕ} (hm : ∀ p ∈ m, p.Prime) :
    primeValueHom a m.prod = (m.map a).prod := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons p m ih =>
      simp_all

end NumberField.Odlyzko

section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

noncomputable instance countableIdealRingOfIntegers :
    Countable (Ideal (𝓞 K)) := by
  letI (n : ℕ) : Fintype {I : Ideal (𝓞 K) // absNorm I = n} :=
    (Ideal.finite_setOf_absNorm_eq n).fintype
  exact Countable.of_equiv
    ((n : ℕ) × {I : Ideal (𝓞 K) // absNorm I = n})
    (Equiv.sigmaFiberEquiv (absNorm : Ideal (𝓞 K) → ℕ))

noncomputable instance countableHeightOneSpectrum :
    Countable (HeightOneSpectrum (𝓞 K)) :=
  HeightOneSpectrum.asIdeal_injective.countable

noncomputable instance encodableHeightOneSpectrum :
    Encodable (HeightOneSpectrum (𝓞 K)) :=
  Encodable.ofCountable _

/-- A prime ideal code used in the Odlyzko-bound argument. -/
noncomputable def primeIdealCode (P : HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.nth Nat.Prime (Encodable.encode P)

lemma prime_primeIdealCode (P : HeightOneSpectrum (𝓞 K)) :
    Nat.Prime (primeIdealCode K P) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime _

lemma primeIdealCode_injective :
    Function.Injective (primeIdealCode K) :=
  (Nat.nth_strictMono Nat.infinite_setOf_prime).injective.comp
    Encodable.encode_injective

/-- A prime ideal code embedding used in the Odlyzko-bound argument. -/
noncomputable def primeIdealCodeEmbedding :
    HeightOneSpectrum (𝓞 K) ↪ Nat.Primes where
  toFun P := ⟨primeIdealCode K P, prime_primeIdealCode K P⟩
  inj' := fun _ _ h ↦ primeIdealCode_injective K (Subtype.ext_iff.mp h)

end NumberField.Odlyzko

end

section

open Ideal IsDedekindDomain UniqueFactorizationMonoid

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- An ideal prime code used in the Odlyzko-bound argument. -/
noncomputable def idealPrimeCode (I : NonzeroIdeal K) : ℕ :=
  ((idealPrimeFactors K I).map (primeIdealCode K)).prod

lemma prime_mem_idealPrimeCode_factors (I : NonzeroIdeal K) :
    ∀ p ∈ (idealPrimeFactors K I).map (primeIdealCode K), p.Prime := by
  intro p hp
  obtain ⟨P, -, rfl⟩ := Multiset.mem_map.mp hp
  exact prime_primeIdealCode K P

lemma normalizedFactors_idealPrimeCode (I : NonzeroIdeal K) :
    normalizedFactors (idealPrimeCode K I) =
      (idealPrimeFactors K I).map (primeIdealCode K) := by
  apply normalizedFactors_prod_of_prime
  intro p hp
  exact Nat.prime_iff.mp (prime_mem_idealPrimeCode_factors K I p hp)

lemma idealPrimeCode_injective :
    Function.Injective (idealPrimeCode K) := by
  intro I J h
  apply (nonzeroIdealEquivPrimeFactors K).injective
  change idealPrimeFactors K I = idealPrimeFactors K J
  apply Multiset.map_injective (primeIdealCode_injective K)
  rw [← normalizedFactors_idealPrimeCode K I,
    ← normalizedFactors_idealPrimeCode K J, h]

end NumberField.Odlyzko

end

section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

/-- A prime ideal at code used in the Odlyzko-bound argument. -/
noncomputable def primeIdealAtCode (p : ℕ) :
    Option (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact if h : ∃ P, primeIdealCode K P = p then some (Classical.choose h) else none

lemma primeIdealAtCode_eq_some_iff {p : ℕ} {P : HeightOneSpectrum (𝓞 K)} :
    primeIdealAtCode K p = some P ↔ primeIdealCode K P = p := by
  classical
  constructor
  · intro h
    unfold primeIdealAtCode at h
    split at h
    · grind
    · simp at h
  · intro h
    unfold primeIdealAtCode
    rw [dif_pos ⟨P, h⟩]
    congr
    exact primeIdealCode_injective K
      ((Classical.choose_spec (show ∃ Q, primeIdealCode K Q = p from ⟨P, h⟩)).trans h.symm)

@[simp] lemma primeIdealAtCode_primeIdealCode
    (P : HeightOneSpectrum (𝓞 K)) :
    primeIdealAtCode K (primeIdealCode K P) = some P :=
  primeIdealAtCode_eq_some_iff K |>.2 rfl

/-- An encoded prime ideal weight used in the Odlyzko-bound argument. -/
noncomputable def encodedPrimeIdealWeight (s : ℂ) (p : ℕ) : ℂ :=
  (primeIdealAtCode K p).elim 0 fun P ↦
    inverseNormPower (primeIdealNorm K P) s

@[simp] lemma encodedPrimeIdealWeight_primeIdealCode
    (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) :
    encodedPrimeIdealWeight K s (primeIdealCode K P) =
      inverseNormPower (primeIdealNorm K P) s := by
  simp [encodedPrimeIdealWeight]

private lemma inverseNormPower_primeIdeal_ne_zero
    (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) :
    inverseNormPower (primeIdealNorm K P) s ≠ 0 := by
  rw [inverseNormPower, Complex.cpow_ne_zero_iff]
  left
  exact_mod_cast (Nat.zero_lt_of_lt (one_lt_primeIdealNorm K P)).ne'

lemma encodedPrimeIdealWeight_ne_zero_iff (s : ℂ) (p : ℕ) :
    encodedPrimeIdealWeight K s p ≠ 0 ↔
      ∃ P, primeIdealCode K P = p := by
  constructor
  · intro hw
    cases h : primeIdealAtCode K p with
    | none => simp [encodedPrimeIdealWeight, h] at hw
    | some P => exact ⟨P, (primeIdealAtCode_eq_some_iff K).1 h⟩
  · rintro ⟨P, hP⟩
    rw [encodedPrimeIdealWeight,
      (primeIdealAtCode_eq_some_iff K).2 hP]
    exact inverseNormPower_primeIdeal_ne_zero K s P

/-- An encoded ideal summand used in the Odlyzko-bound argument. -/
noncomputable def encodedIdealSummand (s : ℂ) : ℕ →*₀ ℂ :=
  primeValueHom (encodedPrimeIdealWeight K s)

lemma encodedIdealSummand_idealPrimeCode
    (s : ℂ) (I : NonzeroIdeal K) :
    encodedIdealSummand K s (idealPrimeCode K I) =
      ((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) := by
  rw [encodedIdealSummand, idealPrimeCode,
    primeValueHom_multiset_prod_of_prime
      (encodedPrimeIdealWeight K s)
      (prime_mem_idealPrimeCode_factors K I)]
  rw [inverseNormPower_nonzeroIdealEquivPrimeFactors]
  change
    (((idealPrimeFactors K I).map (primeIdealCode K)).map
      (encodedPrimeIdealWeight K s)).prod =
      ((idealPrimeFactors K I).map
        (fun P ↦ inverseNormPower (primeIdealNorm K P) s)).prod
  simp

lemma exists_idealPrimeCode_eq_of_primeFactors {n : ℕ} (hn : n ≠ 0)
    (hcodes : ∀ p ∈ (n.primeFactorsList : Multiset ℕ),
      ∃ P, primeIdealCode K P = p) :
    ∃ I : NonzeroIdeal K, idealPrimeCode K I = n := by
  classical
  let m : Multiset (HeightOneSpectrum (𝓞 K)) :=
    Multiset.pmap
      (fun p hp ↦ Classical.choose (hcodes p hp))
      (n.primeFactorsList : Multiset ℕ)
      (fun p hp ↦ hp)
  have hmap :
      m.map (primeIdealCode K) = (n.primeFactorsList : Multiset ℕ) := by
    -- At v4.32 `dsimp [m]` normalizes the `Multiset` coercion down to
    -- `List.map`/`List.pmap`, where `Multiset.map_pmap` no longer matches;
    -- unfold the `let` by hand instead.
    change (Multiset.pmap (fun p hp ↦ Classical.choose (hcodes p hp))
        (n.primeFactorsList : Multiset ℕ) (fun p hp ↦ hp)).map (primeIdealCode K) =
      (n.primeFactorsList : Multiset ℕ)
    rw [Multiset.map_pmap]
    calc
      Multiset.pmap
          (fun p hp ↦ primeIdealCode K (Classical.choose (hcodes p hp)))
          (n.primeFactorsList : Multiset ℕ) (fun p hp ↦ hp) =
          Multiset.pmap (fun p (_ : p ∈ (n.primeFactorsList : Multiset ℕ)) ↦ p)
            (n.primeFactorsList : Multiset ℕ) (fun p hp ↦ hp) := by grind
      _ = Multiset.map id (n.primeFactorsList : Multiset ℕ) :=
        Multiset.pmap_eq_map _ _ _ _
      _ = (n.primeFactorsList : Multiset ℕ) := Multiset.map_id _
  refine ⟨idealOfPrimeFactors K m, ?_⟩
  rw [idealPrimeCode, idealPrimeFactors_idealOfPrimeFactors, hmap,
    Multiset.prod_coe, Nat.prod_primeFactorsList hn]

lemma exists_idealPrimeCode_eq_of_encodedIdealSummand_ne_zero
    (s : ℂ) {n : ℕ} (hn : encodedIdealSummand K s n ≠ 0) :
    ∃ I : NonzeroIdeal K, idealPrimeCode K I = n := by
  have hn0 : n ≠ 0 := by grind
  apply exists_idealPrimeCode_eq_of_primeFactors K hn0
  intro p hp
  apply (encodedPrimeIdealWeight_ne_zero_iff K s p).1
  have hpsupp : p ∈ n.factorization.support := by simp_all
  have hprod : n.factorization.prod
      (fun q e ↦ encodedPrimeIdealWeight K s q ^ e) ≠ 0 := by
    simpa [encodedIdealSummand, primeValueHom, hn0] using hn
  have := (Finsupp.prod_ne_zero_iff.mp hprod p hpsupp)
  exact (pow_ne_zero_iff (Finsupp.mem_support_iff.mp hpsupp)).mp this

theorem encodedIdealSummand_ne_zero_iff (s : ℂ) (n : ℕ) :
    encodedIdealSummand K s n ≠ 0 ↔
      ∃ I : NonzeroIdeal K, idealPrimeCode K I = n := by
  constructor
  · exact exists_idealPrimeCode_eq_of_encodedIdealSummand_ne_zero K s
  · rintro ⟨I, rfl⟩
    rw [encodedIdealSummand_idealPrimeCode]
    apply Complex.cpow_ne_zero_iff.mpr
    left
    exact_mod_cast (show absNorm (I : Ideal (𝓞 K)) ≠ 0 by
      simpa [Ideal.absNorm_eq_zero_iff] using I.2)

end NumberField.Odlyzko

end

section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem summable_nonzeroIdeal_norm_inverseNormPower {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : NonzeroIdeal K ↦
      ‖((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s))‖) := by
  have hreal :
      Summable (fun I : NonzeroIdeal K ↦
        (absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s.re)) := by
    change Summable
      ((fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-s.re)) ∘
        Subtype.val)
    exact (summable_ideal_absNorm_rpow K hs).comp_injective
      Subtype.val_injective
  apply hreal.congr
  intro I
  rw [show ((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      inverseNormPower (absNorm (I : Ideal (𝓞 K))) s by rfl,
    norm_inverseNormPower]
  exact Nat.pos_of_ne_zero (by
    simpa [Ideal.absNorm_eq_zero_iff] using I.2)

lemma norm_encodedIdealSummand_eq_extendByZero (s : ℂ) :
    (fun n ↦ ‖encodedIdealSummand K s n‖) =
      extendByZero (idealPrimeCode K)
        (fun I : NonzeroIdeal K ↦
          ‖((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s))‖) := by
  funext n
  by_cases hn : encodedIdealSummand K s n = 0
  · rw [hn, norm_zero]
    symm
    apply extendByZero_eq_zero_of_not_mem_range
      (idealPrimeCode K) _
    intro hrange
    obtain ⟨I, hI⟩ := hrange
    apply (encodedIdealSummand_ne_zero_iff K s n).2 ⟨I, hI⟩
    simp_all
  · obtain ⟨I, hI⟩ :=
      (encodedIdealSummand_ne_zero_iff K s n).1 hn
    subst n
    rw [extendByZero_apply (idealPrimeCode K)
      (idealPrimeCode_injective K),
      encodedIdealSummand_idealPrimeCode]

theorem summable_norm_encodedIdealSummand {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ ‖encodedIdealSummand K s n‖) := by
  rw [norm_encodedIdealSummand_eq_extendByZero]
  exact summable_extendByZero
    (idealPrimeCode K) (idealPrimeCode_injective K)
    (summable_nonzeroIdeal_norm_inverseNormPower K hs)

end NumberField.Odlyzko

end

section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

lemma encodedIdealSummand_eq_extendByZero (s : ℂ) :
    (encodedIdealSummand K s : ℕ → ℂ) =
      extendByZero (idealPrimeCode K)
        (fun I : NonzeroIdeal K ↦
          ((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s))) := by
  funext n
  by_cases hn : encodedIdealSummand K s n = 0
  · rw [hn]
    symm
    apply extendByZero_eq_zero_of_not_mem_range
      (idealPrimeCode K) _
    intro hrange
    obtain ⟨I, hI⟩ := hrange
    exact ((encodedIdealSummand_ne_zero_iff K s n).2 ⟨I, hI⟩) hn
  · obtain ⟨I, hI⟩ :=
      (encodedIdealSummand_ne_zero_iff K s n).1 hn
    subst n
    rw [extendByZero_apply (idealPrimeCode K)
      (idealPrimeCode_injective K),
      encodedIdealSummand_idealPrimeCode]

theorem hasSum_encodedIdealSummand {s : ℂ} (hs : 1 < s.re) :
    HasSum (encodedIdealSummand K s) (NumberField.dedekindZeta K s) := by
  rw [encodedIdealSummand_eq_extendByZero]
  exact hasSum_extendByZero
    (idealPrimeCode K) (idealPrimeCode_injective K)
    (hasSum_nonzeroIdeal_inverseNormPower K hs)

/-- An encoded ideal factor used in the Odlyzko-bound argument. -/
noncomputable def encodedIdealFactor (s : ℂ) (p : Nat.Primes) : ℂ :=
  (1 - encodedIdealSummand K s p)⁻¹

lemma encodedIdealFactor_primeIdealCode (s : ℂ)
    (P : HeightOneSpectrum (𝓞 K)) :
    encodedIdealFactor K s (primeIdealCodeEmbedding K P) =
      primeIdealFactor K P s := by
  rw [encodedIdealFactor, encodedIdealSummand,
    show ((primeIdealCodeEmbedding K P : Nat.Primes) : ℕ) =
      primeIdealCode K P by rfl]
  rw [primeValueHom_apply_of_prime _
      (prime_primeIdealCode K P),
    encodedPrimeIdealWeight_primeIdealCode]
  rfl

lemma encodedIdealFactor_eq_one_of_not_mem_range (s : ℂ)
    (p : Nat.Primes)
    (hp : p ∉ Set.range (primeIdealCodeEmbedding K)) :
    encodedIdealFactor K s p = 1 := by
  have hnone : primeIdealAtCode K p = none := by
    cases h : primeIdealAtCode K p with
    | none => simp
    | some P =>
        exfalso
        apply hp
        refine ⟨P, Subtype.ext ?_⟩
        exact (primeIdealAtCode_eq_some_iff K).1 h
  rw [encodedIdealFactor, encodedIdealSummand,
    primeValueHom_apply_prime_subtype, encodedPrimeIdealWeight, hnone]
  simp

theorem dedekindZeta_primeIdeal_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re) :
    HasProd
      (fun P : HeightOneSpectrum (𝓞 K) ↦ primeIdealFactor K P s)
      (NumberField.dedekindZeta K s) := by
  have hEuler :
      HasProd (encodedIdealFactor K s)
        (∑' n, encodedIdealSummand K s n) := by
    exact EulerProduct.eulerProduct_completely_multiplicative_hasProd
      (summable_norm_encodedIdealSummand K hs)
  rw [(hasSum_encodedIdealSummand K hs).tsum_eq] at hEuler
  have hcodes :
      HasProd
        (encodedIdealFactor K s ∘ primeIdealCodeEmbedding K)
        (NumberField.dedekindZeta K s) :=
    ((primeIdealCodeEmbedding K).injective.hasProd_iff
      (encodedIdealFactor_eq_one_of_not_mem_range K s)).2 hEuler
  exact hcodes.congr_fun fun P ↦
    (encodedIdealFactor_primeIdealCode K s P).symm

theorem dedekindZeta_primeIdeal_eulerProduct_tprod {s : ℂ} (hs : 1 < s.re) :
    ∏' P : HeightOneSpectrum (𝓞 K), primeIdealFactor K P s =
      NumberField.dedekindZeta K s :=
  (dedekindZeta_primeIdeal_eulerProduct_hasProd K hs).tprod_eq

end NumberField.Odlyzko

end
