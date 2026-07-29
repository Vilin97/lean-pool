/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Data.Finite.Vector
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Generic number-field Euler-product infrastructure

The analytic number-field machinery for `ζ_K(s) = Σ_𝔞 N𝔞^{-s} = ∏_𝔭
(1 - N𝔭^{-s})^{-1}` and the per-prime-power decomposition used by
the Chebotarev cyclotomic and abelian cases.

Originally developed in `flt-regular-bernoulli`; portable to this
project unchanged (depends only on mathlib).
-/

@[expose] public section

noncomputable section

open NumberField
open scoped Topology nonZeroDivisors

noncomputable instance instFintypeSym (α : Type*) [Finite α] (n : ℕ) :
    Fintype (Sym α n) :=
  Fintype.ofFinite (Sym α n)

namespace Chebotarev

section NumberFieldEulerProduct

variable (L : Type*) [Field L] [NumberField L]

abbrev NonzeroIdeal : Type _ := {I : Ideal (𝓞 L) // I ≠ ⊥}

noncomputable def idealNormMultiplicity (n : ℕ) : ℕ :=
  Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}

lemma idealNormMultiplicity_zero : idealNormMultiplicity L 0 = 0 := by
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩

lemma idealNormMultiplicity_one : idealNormMultiplicity L 1 = 1 := by
  unfold idealNormMultiplicity
  have : Unique {I : NonzeroIdeal L // Ideal.absNorm I.1 = 1} :=
    { default := ⟨⟨⊤, by simp⟩, Ideal.absNorm_top⟩
      uniq := fun ⟨⟨I, hI⟩, hnorm⟩ ↦
        Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm)) }
  exact Nat.card_unique

omit [NumberField L] in
private lemma span_natCast_sup_span_natCast {m n : ℕ} (hcop : Nat.Coprime m n) :
    Ideal.span {(m : 𝓞 L)} ⊔ Ideal.span {(n : 𝓞 L)} = ⊤ := by
  rw [← Ideal.isCoprime_iff_sup_eq, Ideal.isCoprime_span_singleton_iff]
  simpa using (Nat.Coprime.isCoprime hcop).map (algebraMap ℤ (𝓞 L))

omit [NumberField L] in
private lemma sup_span_mul_sup_span {m n : ℕ} (hcop : Nat.Coprime m n) (I : Ideal (𝓞 L)) :
    (I ⊔ Ideal.span {(m : 𝓞 L)}) * (I ⊔ Ideal.span {(n : 𝓞 L)}) =
      I ⊔ Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)} := by
  rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup,
    mul_comm (Ideal.span {(m : 𝓞 L)}) I,
    Ideal.span_singleton_mul_span_singleton,
    show I * I ⊔ I * Ideal.span {(n : 𝓞 L)} ⊔
        (I * Ideal.span {(m : 𝓞 L)} ⊔ Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)}) =
        (I * I ⊔ I * Ideal.span {(n : 𝓞 L)} ⊔ I * Ideal.span {(m : 𝓞 L)}) ⊔
          Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)} by ac_rfl,
    ← Ideal.mul_sup, ← Ideal.mul_sup,
    show I ⊔ Ideal.span {(n : 𝓞 L)} ⊔ Ideal.span {(m : 𝓞 L)} = ⊤ by
      rw [sup_assoc, sup_comm (Ideal.span {(n : 𝓞 L)}) _,
        span_natCast_sup_span_natCast L hcop, sup_top_eq],
    Ideal.mul_top]

private lemma span_natCast_le_of_absNorm_eq {I : Ideal (𝓞 L)} {k : ℕ}
    (hI : Ideal.absNorm I = k) : Ideal.span {(k : 𝓞 L)} ≤ I := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact_mod_cast hI ▸ Ideal.absNorm_mem I

private lemma sup_span_natCast_mul_eq {I : Ideal (𝓞 L)} {m n : ℕ}
    (hI : Ideal.absNorm I = m * n) : I ⊔ Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)} = I := by
  rw [← Nat.cast_mul]
  exact sup_of_le_left (span_natCast_le_of_absNorm_eq L hI)

private lemma absNorm_sup_span_natCast {m n : ℕ} (hcop : Nat.Coprime m n) (hm : 0 < m)
    (hn : 0 < n) (I : Ideal (𝓞 L)) (hI : Ideal.absNorm I = m * n) :
    Ideal.absNorm (I ⊔ Ideal.span {(m : 𝓞 L)}) = m ∧
      Ideal.absNorm (I ⊔ Ideal.span {(n : 𝓞 L)}) = n := by
  set a := Ideal.absNorm (I ⊔ Ideal.span {(m : 𝓞 L)}) with ha_def
  set b := Ideal.absNorm (I ⊔ Ideal.span {(n : 𝓞 L)}) with hb_def
  have h_prod : (I ⊔ Ideal.span {(m : 𝓞 L)}) * (I ⊔ Ideal.span {(n : 𝓞 L)}) = I := by
    rw [sup_span_mul_sup_span L hcop I]
    exact sup_span_natCast_mul_eq L hI
  have h_ab : a * b = m * n := by rw [ha_def, hb_def, ← map_mul, h_prod, hI]
  have h_a_dvd_m : a ∣ m :=
    ((hcop.pow_left (Module.finrank ℤ (𝓞 L))).coprime_dvd_left
      (Ideal.absNorm_span_natCast (S := 𝓞 L) m ▸ Ideal.absNorm_dvd_absNorm_of_le
        le_sup_right)).dvd_of_dvd_mul_right ⟨b, h_ab.symm⟩
  have h_b_dvd_n : b ∣ n :=
    ((hcop.symm.pow_left (Module.finrank ℤ (𝓞 L))).coprime_dvd_left
      (Ideal.absNorm_span_natCast (S := 𝓞 L) n ▸ Ideal.absNorm_dvd_absNorm_of_le
        le_sup_right)).dvd_of_dvd_mul_right ⟨a, by linarith [h_ab, mul_comm a b, mul_comm m n]⟩
  have ha_le : a ≤ m := Nat.le_of_dvd hm h_a_dvd_m
  have hb_le : b ≤ n := Nat.le_of_dvd hn h_b_dvd_n
  refine ⟨Nat.le_antisymm ha_le ?_, Nat.le_antisymm hb_le ?_⟩ <;>
    nlinarith [h_ab, ha_le, hb_le, hm, hn]

private lemma mul_sup_span_natCast_left {m n : ℕ} (hcop : Nat.Coprime m n)
    (J L' : Ideal (𝓞 L)) (hJ : Ideal.absNorm J = m) (hL : Ideal.absNorm L' = n) :
    J * L' ⊔ Ideal.span {(m : 𝓞 L)} = J := by
  have h_cop_mL_sup : Ideal.span {(m : 𝓞 L)} ⊔ L' = ⊤ := by
    refine top_le_iff.mp ?_
    calc ⊤ = Ideal.span {(m : 𝓞 L)} ⊔ Ideal.span {(n : 𝓞 L)} :=
          (span_natCast_sup_span_natCast L hcop).symm
      _ ≤ Ideal.span {(m : 𝓞 L)} ⊔ L' :=
          sup_le_sup_left (span_natCast_le_of_absNorm_eq L hL) _
  refine le_antisymm (sup_le Ideal.mul_le_right (span_natCast_le_of_absNorm_eq L hJ)) ?_
  · calc J = J * ⊤ := (Ideal.mul_top J).symm
      _ = J * (Ideal.span {(m : 𝓞 L)} ⊔ L') := by rw [h_cop_mL_sup]
      _ = J * Ideal.span {(m : 𝓞 L)} ⊔ J * L' := Ideal.mul_sup _ _ _
      _ ≤ Ideal.span {(m : 𝓞 L)} ⊔ J * L' := sup_le_sup_right Ideal.mul_le_left _
      _ = J * L' ⊔ Ideal.span {(m : 𝓞 L)} := sup_comm _ _

lemma idealNormMultiplicity_mul {m n : ℕ} (hcop : Nat.Coprime m n) :
    idealNormMultiplicity L (m * n) =
      idealNormMultiplicity L m * idealNormMultiplicity L n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.Coprime, Nat.gcd_zero_left] at hcop
    subst hcop
    simp [idealNormMultiplicity_zero, idealNormMultiplicity_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.Coprime, Nat.gcd_zero_right] at hcop
    subst hcop
    simp [idealNormMultiplicity_zero, idealNormMultiplicity_one]
  rcases Nat.lt_or_ge 1 m with hm1 | hm1
  all_goals rcases Nat.lt_or_ge 1 n with hn1 | hn1
  · classical
    have h_sup_absNorm : ∀ (I : Ideal (𝓞 L)), Ideal.absNorm I = m * n →
        I ⊔ Ideal.span {(m : 𝓞 L) * (n : 𝓞 L)} = I := fun I hI ↦
      sup_span_natCast_mul_eq L hI
    have h_inv_n : ∀ (J L' : Ideal (𝓞 L)), Ideal.absNorm J = m → Ideal.absNorm L' = n →
        J * L' ⊔ Ideal.span {(n : 𝓞 L)} = L' := fun J L' hJ hL ↦
      mul_comm J L' ▸ mul_sup_span_natCast_left L hcop.symm L' J hL hJ
    let fwd : {I : NonzeroIdeal L // Ideal.absNorm I.1 = m * n} →
        {J : NonzeroIdeal L // Ideal.absNorm J.1 = m} ×
          {L' : NonzeroIdeal L // Ideal.absNorm L'.1 = n} :=
      fun ⟨⟨I, hI_ne⟩, hI_norm⟩ ↦
        ⟨⟨⟨I ⊔ Ideal.span {(m : 𝓞 L)}, fun h ↦ hI_ne (le_bot_iff.mp (h ▸ le_sup_left))⟩,
          (absNorm_sup_span_natCast L hcop hm hn I hI_norm).1⟩,
         ⟨⟨I ⊔ Ideal.span {(n : 𝓞 L)}, fun h ↦ hI_ne (le_bot_iff.mp (h ▸ le_sup_left))⟩,
          (absNorm_sup_span_natCast L hcop hm hn I hI_norm).2⟩⟩
    let bwd : {J : NonzeroIdeal L // Ideal.absNorm J.1 = m} ×
        {L' : NonzeroIdeal L // Ideal.absNorm L'.1 = n} →
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = m * n} :=
      fun ⟨⟨⟨J, hJ_ne⟩, hJ_norm⟩, ⟨⟨L', hL_ne⟩, hL_norm⟩⟩ ↦
        ⟨⟨J * L', fun h ↦ (Ideal.mul_eq_bot.mp h).elim hJ_ne hL_ne⟩,
         by rw [map_mul, hJ_norm, hL_norm]⟩
    have h_equiv :
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = m * n} ≃
          {J : NonzeroIdeal L // Ideal.absNorm J.1 = m} ×
            {L' : NonzeroIdeal L // Ideal.absNorm L'.1 = n} :=
      { toFun := fwd
        invFun := bwd
        left_inv := fun ⟨⟨I, hI_ne⟩, hI_norm⟩ ↦ by
          simp only [fwd, bwd]
          exact Subtype.ext (Subtype.ext
            ((sup_span_mul_sup_span L hcop I).trans (h_sup_absNorm I hI_norm)))
        right_inv := fun ⟨⟨⟨J, hJ_ne⟩, hJ_norm⟩, ⟨⟨L', hL_ne⟩, hL_norm⟩⟩ ↦ by
          simp only [fwd, bwd]
          exact Prod.ext
            (Subtype.ext (Subtype.ext (mul_sup_span_natCast_left L hcop J L' hJ_norm hL_norm)))
            (Subtype.ext (Subtype.ext (h_inv_n J L' hJ_norm hL_norm))) }
    unfold idealNormMultiplicity
    rw [Nat.card_congr h_equiv, Nat.card_prod]
  · interval_cases n
    simp [idealNormMultiplicity_one]
  · interval_cases m
    simp [idealNormMultiplicity_one]
  · interval_cases m
    interval_cases n
    simp [idealNormMultiplicity_one]

lemma dedekindZeta_eq_tsum_idealNormMultiplicity {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold NumberField.dedekindZeta LSeries
  refine tsum_congr fun n ↦ ?_
  unfold LSeries.term
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    simp [idealNormMultiplicity_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · simp only [hn.ne', ↓reduceIte]
    rw [Complex.cpow_neg, div_eq_mul_inv]
    congr 1
    unfold idealNormMultiplicity
    have hequiv : {I : Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} := by
      refine {
        toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
        invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
      intro h
      rw [h, Ideal.absNorm_bot] at hI
      lia
    exact_mod_cast Nat.card_congr hequiv

lemma summable_tsum_symGeometric (α : Type*) [Fintype α] {z : ℂ}
    (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ ↦ (Fintype.card (Sym α n) : ℂ) * z ^ n) ∧
      (∑' n : ℕ, (Fintype.card (Sym α n) : ℂ) * z ^ n) = ((1 - z)⁻¹) ^ Fintype.card α := by
  by_cases hα : Fintype.card α = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hα
    let term : ℕ → ℂ := fun n ↦ (Fintype.card (Sym α n) : ℂ) * z ^ n
    have hzero : ∀ n ≠ 0, term n = 0 := by
      intro n hn
      cases n with
      | zero => contradiction
      | succ n => simp [term, Sym.card_sym_eq_multichoose, Nat.multichoose_zero_succ]
    have hsupport : {n : ℕ | term n ≠ 0}.Finite :=
      Set.Finite.subset ({0} : Set ℕ).toFinite fun n hn ↦ not_imp_comm.mp (hzero n) hn
    refine ⟨summable_of_hasFiniteSupport hsupport, ?_⟩
    simpa [term, hα, Sym.card_sym_eq_multichoose] using tsum_eq_single 0 hzero
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hα
    have hterm : ∀ n : ℕ, ((n + k).choose k : ℂ) * z ^ n =
        (Fintype.card (Sym α n) : ℂ) * z ^ n := fun n ↦ by
      rw [Sym.card_sym_eq_choose, hk, Nat.succ_add_sub_one, Nat.add_comm k n, Nat.choose_symm_add]
    refine ⟨(summable_choose_mul_geometric_of_norm_lt_one k hz).congr hterm, ?_⟩
    rw [tsum_congr fun n ↦ (hterm n).symm, tsum_choose_mul_geometric_of_norm_lt_one k hz, one_div,
      hk, inv_pow]

/-- The partial sums of the ideal-norm multiplicity counting function grow like `O(n)`: the number
of nonzero ideals of `𝓞 L` with norm `≤ n` is `∑_{k ≤ n} idealNormMultiplicity L k`, and
`NumberField.Ideal.tendsto_norm_le_div_atTop₀` says this count is asymptotic to `c · n`. -/
lemma sum_idealNormMultiplicity_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ))
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
  classical
  have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal L | Ideal.absNorm I.1 = b}.Finite := fun b ↦
    Set.Finite.preimage (f := fun I : NonzeroIdeal L ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
      (Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) b)
  have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity L k =
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
    have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal L ↦
      Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
    rw [show ((fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
        {I : NonzeroIdeal L | Ideal.absNorm I.1 ≤ n} by
      ext ⟨I, hI⟩
      simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_setOf_eq]
      exact ⟨fun h ↦ h.2, fun h ↦
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
    exact key.symm
  have h_card_bridge : ∀ n : ℕ,
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} =
      Nat.card {I : (Ideal (𝓞 L))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
    fun n ↦ Nat.card_congr
      { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
          ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
        invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
          ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
      tendsto_natCast_atTop_atTop).congr' ?_)
  filter_upwards with n
  simp only [Function.comp_apply, Real.rpow_one]
  rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
  push_cast
  rfl

lemma summable_idealNormMultiplicity_mul_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦ ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ := by
  classical
  have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (f := fun n ↦ (idealNormMultiplicity L n : ℝ))
      (sum_idealNormMultiplicity_isBigO L) (fun _ ↦ Nat.cast_nonneg _) zero_le_one
      (by exact_mod_cast hs)
  have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s =
      fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
    funext n
    simp only [LSeries.term]
    split_ifs with hn
    · subst hn
      simp [idealNormMultiplicity_zero]
    · simp [Complex.cpow_neg, div_eq_mul_inv]
  exact (h_term_eq ▸ h_lss :
    Summable fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)).norm

lemma dedekindZeta_eq_tprod_primePowerSeries {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' q : Nat.Primes,
        (∑' k : ℕ, (idealNormMultiplicity L ((q : ℕ) ^ k) : ℂ) *
          ((((q : ℕ) ^ k : ℕ) : ℂ) ^ (-s))) := by
  let f : ℕ → ℂ := fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)
  have hf_zero : f 0 = 0 := by simp [f, idealNormMultiplicity_zero L]
  have hf_one : f 1 = 1 := by simp [f, idealNormMultiplicity_one L]
  have hf_mul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := fun {m n} hcop ↦ by
    simp only [f, idealNormMultiplicity_mul L hcop, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    ring
  have hf_sum : Summable fun n ↦ ‖f n‖ := summable_idealNormMultiplicity_mul_cpow_neg L hs
  rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs,
    ← EulerProduct.eulerProduct_tprod hf_one hf_mul hf_sum hf_zero]

/-! ### Sub-lemmas for `dedekindZeta_eq_tprod_primeIdeal`: the finite Euler-factor identity

The proof multiplies finitely many geometric series, one per prime `𝔭 ∈ S`, accumulating the
exponent of each `𝔭` into a vector `e : ↥S → ℕ`. The next two private lemmas implement the
inductive step: `insertPiEquiv` re-indexes exponent vectors over `insert a s` as a pair
`(e a, e|_s)`, and `prodInsertAttach` splits the corresponding product accordingly. -/

/-- Re-index exponent vectors on `insert a s` as `(value at a, restriction to s)`. -/
private noncomputable def insertPiEquiv {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) : ({i // i ∈ insert a s} → ℕ) ≃ ℕ × ({i // i ∈ s} → ℕ) :=
  ((Finset.subtypeInsertEquivOption ha).arrowCongr (Equiv.refl ℕ)).trans Equiv.piOptionEquivProd

@[simp] private lemma insertPiEquiv_fst {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) :
    (insertPiEquiv a s ha e).1 = e ⟨a, Finset.mem_insert_self a s⟩ := rfl

@[simp] private lemma insertPiEquiv_snd {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) (i : {i // i ∈ s}) :
    (insertPiEquiv a s ha e).2 i = e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ := rfl

/-- `∏_{i ∈ insert a s} g i ^ e i` splits off the factor at `a`, the rest re-indexed via
`insertPiEquiv`. -/
private lemma prodInsertAttach {ι : Type*} [DecidableEq ι] (g : ι → ℂ) (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) :
    ∏ i ∈ (insert a s).attach, g i.1 ^ e i =
      g a ^ (insertPiEquiv a s ha e).1 *
        ∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv a s ha e).2 i := by
  rw [insertPiEquiv_fst]
  conv_rhs => rw [show (∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv a s ha e).2 i)
    = ∏ i ∈ s.attach, g i.1 ^ e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ from
    Finset.prod_congr rfl fun i _ ↦ by rw [insertPiEquiv_snd]]
  rw [Finset.attach_insert, Finset.prod_insert, Finset.prod_image]
  · exact fun x _ y _ h ↦ Subtype.ext (Subtype.mk.inj h)
  · simpa only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and,
      Subtype.exists, exists_prop, exists_eq_right] using ha

/-! Sharifi, *Algebraic Number Theory*, Prop. 7.1.9 (p. 139), applied to ideals:

> "Let `S` be a finite set of prime numbers and `I_S` be the semigroup they generate. Then
> `∏_{p ∈ S} (1 − p^{-s})^{-1} = Σ_{n ∈ I_S} n^{-s}`."

For ideals, `I_S` is the multiplicative semigroup generated by the primes `𝔭 ∈ S`, i.e. the
ideals `∏_𝔭 𝔭^{e 𝔭}` indexed by exponent vectors `e : S →₀ ℕ`. The product of the geometric
Euler factors equals the sum over these exponent vectors; `absNorm_prod_pow_of_primeIdeal`
identifies the summand with the ideal norm `N(∏_𝔭 𝔭^{e 𝔭})^{-s}`.
-/

/-- Combinatorial heart of the finite Euler-factor identity: for `‖g i‖ < 1`,
`∏ i ∈ s, (1 - g i)⁻¹` is the norm-summable `tsum` over exponent vectors of `∏ i, g i ^ e i`. -/
private lemma finsetGeometricProd_summable_and_hasSum {ι : Type*} (g : ι → ℂ)
    (hg : ∀ i, ‖g i‖ < 1) (s : Finset ι) :
    (Summable fun e : {i // i ∈ s} → ℕ ↦ ‖∏ i ∈ s.attach, g i.1 ^ e i‖) ∧
      HasSum (fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i)
        (∏ i ∈ s, (1 - g i)⁻¹) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · have h1 : (fun e : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ ‖∏ i ∈ Finset.attach ∅, g i.1 ^ e i‖)
          = fun _ ↦ (1 : ℝ) := by
        funext e
        simp [Finset.attach_empty]
      rw [h1]
      exact (hasSum_unique (fun _ : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ (1 : ℝ))).summable
    · have h1 : (fun e : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ ∏ i ∈ Finset.attach ∅, g i.1 ^ e i)
          = fun _ ↦ (1 : ℂ) := by
        funext e
        simp [Finset.attach_empty]
      rw [h1]
      exact hasSum_unique (fun _ : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ (1 : ℂ))
  | insert a s ha ih =>
    obtain ⟨ihsum, ihhas⟩ := ih
    rw [Finset.prod_insert ha]
    have hgeo : HasSum (fun n : ℕ ↦ g a ^ n) (1 - g a)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (hg a)
    have hgeosum : Summable (fun n : ℕ ↦ ‖g a ^ n‖) := by
      simp_rw [norm_pow]
      exact summable_geometric_of_lt_one (norm_nonneg _) (hg a)
    have hprodsum : Summable (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) :=
      summable_mul_of_summable_norm (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeosum ihsum
    have hHsum : Summable (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        ‖g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i‖) :=
      Summable.mul_norm (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeosum ihsum
    have hHhas : HasSum (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) ((1 - g a)⁻¹ * ∏ i ∈ s, (1 - g i)⁻¹) :=
      HasSum.mul (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeo ihhas hprodsum
    refine ⟨?_, ?_⟩
    · have heq : (fun e : {i // i ∈ insert a s} → ℕ ↦ ‖∏ i ∈ (insert a s).attach, g i.1 ^ e i‖)
          = (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
              ‖g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i‖) ∘ insertPiEquiv a s ha := by
        funext e
        rw [Function.comp_apply, prodInsertAttach g a s ha e]
      rw [heq]
      exact (insertPiEquiv a s ha).summable_iff.mpr hHsum
    · have heq : (fun e : {i // i ∈ insert a s} → ℕ ↦ ∏ i ∈ (insert a s).attach, g i.1 ^ e i)
          = (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
              g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) ∘ insertPiEquiv a s ha := by
        funext e
        rw [Function.comp_apply, prodInsertAttach g a s ha e]
      rw [heq]
      exact (insertPiEquiv a s ha).hasSum_iff.mpr hHhas

/-- `∏ i ∈ S, (m i : ℂ) ^ z = ((∏ i ∈ S, m i : ℕ) : ℂ) ^ z`. -/
private lemma prod_natCast_cpow {ι : Type*} (S : Finset ι) (m : ι → ℕ) (z : ℂ) :
    (∏ i ∈ S, (m i : ℂ) ^ z) = ((∏ i ∈ S, m i : ℕ) : ℂ) ^ z := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]

/-- For `1 < Re s`, the ratio `N𝔭^{-s}` of a nonzero prime ideal has norm `< 1` (since `N𝔭 ≥ 2`). -/
lemma norm_absNorm_cpow_neg_lt_one {s : ℂ} (hs : 1 < s.re)
    (𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := by
  have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h ↦ 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h ↦ 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h2 : 2 ≤ Ideal.absNorm 𝔭.1 := by lia
  rw [Complex.norm_natCast_cpow_of_pos (by lia), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h2.trans_lt' one_lt_two) (by linarith)

/-- **Finite Euler-factor identity** (Sharifi, *Algebraic Number Theory*, Prop. 7.1.9, p. 139,
for ideals): for a `Finset S` of nonzero prime ideals of `𝓞 L` and `1 < Re s`,
`∏_{𝔭 ∈ S} (1 - N𝔭^{-s})^{-1} = Σ_{e : S →₀ ℕ} ∏_𝔭 N𝔭^{-(e 𝔭) · s}`, summing over
exponent vectors. -/
theorem prod_eulerFactor_eq_tsum_exponentVector {s : ℂ} (hs : 1 < s.re)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    (∏ 𝔭 ∈ S, (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) =
      ∑' e : S →₀ ℕ, ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) := by
  classical
  have hg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := norm_absNorm_cpow_neg_lt_one L hs
  have hHS := (finsetGeometricProd_summable_and_hasSum
    (fun 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) hg S).2
  have hrw : ∀ e : S → ℕ,
      (∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭) =
        ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) := fun e ↦
    Finset.prod_congr rfl fun 𝔭 _ ↦ by
      rw [← Complex.cpow_nat_mul]
      ring_nf
  rw [← hHS.tsum_eq, ← (Finsupp.equivFunOnFinite (α := S) (M := ℕ)).tsum_eq
    (fun e : S → ℕ ↦ ∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)]
  refine tsum_congr fun e ↦ ?_
  simp only [Finsupp.equivFunOnFinite_apply]
  rw [hrw]

/-- The norm of `∏_𝔭 𝔭^{e 𝔭}` factors as `∏_𝔭 (N𝔭)^{e 𝔭}`. -/
theorem absNorm_prod_pow_of_primeIdeal
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) =
      ∏ 𝔭 ∈ S.attach, Ideal.absNorm 𝔭.1.1 ^ e 𝔭 := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun 𝔭 _ ↦ map_pow Ideal.absNorm 𝔭.1.1 (e 𝔭)

/-- `∏_𝔭 N𝔭^{-(e 𝔭)·s} = (N(∏_𝔭 𝔭^{e 𝔭}))^{-s}`. -/
theorem prod_absNorm_cpow_eq_absNorm_prod_pow_cpow {s : ℂ}
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    (∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s)) =
      (Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) : ℂ) ^ (-s) := by
  have hinner : ∀ 𝔭 ∈ S.attach,
      (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) =
        ((Ideal.absNorm 𝔭.1.1 ^ e 𝔭 : ℕ) : ℂ) ^ (-s) := fun 𝔭 _ ↦ by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    ring_nf
  rw [Finset.prod_congr rfl hinner, prod_natCast_cpow, absNorm_prod_pow_of_primeIdeal]

/-! ### Sub-lemmas for `dedekindZeta_eq_tprod_primeIdeal`: the `S ↑ ⊤` limit (Sharifi 7.1.12)

Following Sharifi 7.1.12 (p. 140), the prime-ideal Euler product is the limit, over an
increasing finite set `S` of prime ideals, of the finite Euler products
`∏_{𝔭 ∈ S} (1 - N𝔭^{-s})^{-1}`. By `prod_eulerFactor_eq_tsum_exponentVector` and
`prod_absNorm_cpow_eq_absNorm_prod_pow_cpow`, the finite product is the Dirichlet partial sum
`∑_𝔞 N𝔞^{-s}` over the ideals `𝔞 = ∏_𝔭 𝔭^{e 𝔭}` divisible only by primes in `S`. The exponent
map `e ↦ ∏_𝔭 𝔭^{e 𝔭}` is injective with range exactly those `S`-factored ideals
(`UniqueFactorizationMonoid.factorization` of ideals); as `S ↑ ⊤` every nonzero ideal is
eventually captured, so the partial sums tend to `∑_𝔞 N𝔞^{-s} = ζ_K(s)`. -/

private instance instFiniteAbsNormFiber (n : ℕ) :
    Finite {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} :=
  Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal L ↦ I.1)
    ((Ideal.finite_setOf_absNorm_eq (S := 𝓞 L) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
    (fun _ _ _ _ ↦ Subtype.ext)

private lemma tsum_absNormFiber {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    [IsTopologicalAddGroup M] (n : ℕ) (g : ℕ → M) :
    (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}, g (Ideal.absNorm y.1.1))
      = idealNormMultiplicity L n • g n :=
  (tsum_congr fun y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
    (tsum_const (g n))

/-- For `1 < Re s`, `∑_𝔞 N𝔞^{-s}` over nonzero ideals of `𝓞 L` has sum `ζ_K(s)`. -/
theorem hasSum_nonzeroIdeal_absNorm_cpow {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))
      (NumberField.dedekindZeta L s) := by
  classical
  set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1)
  have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
      (Ideal.absNorm (y.1).1 : ℂ) ^ (-s)) = (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) :=
    fun n ↦ by rw [tsum_absNormFiber L n fun k ↦ (k : ℂ) ^ (-s), nsmul_eq_mul]
  have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
      ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-s)‖) = ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ :=
    fun n ↦ by
      rw [tsum_absNormFiber L n fun k ↦ ‖(k : ℂ) ^ (-s)‖, nsmul_eq_mul, norm_mul,
        Complex.norm_natCast]
  have hsummable : Summable fun I : NonzeroIdeal L ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-s)‖ := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
    exact (summable_idealNormMultiplicity_mul_cpow_neg L hs).congr fun n ↦ (hnorm n).symm
  have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦
      (Ideal.absNorm (e p).1 : ℂ) ^ (-s) :=
    (e.summable_iff (f := fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))).mpr
      hsummable.of_norm
  have hval_sum : (∑' I : NonzeroIdeal L, (Ideal.absNorm I.1 : ℂ) ^ (-s))
      = NumberField.dedekindZeta L s := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs,
      ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)), hsummable_sigma.tsum_sigma]
    exact tsum_congr hval
  exact hval_sum ▸ hsummable.of_norm.hasSum

open UniqueFactorizationMonoid in
/-- The exponent of `𝔮` in the factorization of `𝔭 ^ n` is `n` if `𝔮 = 𝔭`, else `0`. -/
private theorem factorization_primePow_apply
    (𝔭 𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (n : ℕ) :
    factorization (𝔭.1 ^ n) 𝔮.1 = if 𝔮 = 𝔭 then n else 0 := by
  rw [factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_eq_count,
    normalizedFactors_irreducible (Ideal.prime_of_isPrime 𝔭.2.2 𝔭.2.1).irreducible,
    normalize_eq, Multiset.count_singleton]
  split_ifs <;> simp_all [Subtype.ext_iff]

open UniqueFactorizationMonoid in
/-- The exponent of `𝔮` in `∏_{𝔭 ∈ S} 𝔭 ^ e 𝔭` is `∑_{𝔭 ∈ S} factorization (𝔭^{e 𝔭}) 𝔮`. -/
private theorem factorization_prod_primePow_apply
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (e : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℕ)
    (𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 =
      ∑ 𝔭 ∈ S.attach, factorization (𝔭.1.1 ^ e 𝔭.1) 𝔮.1 := by
  classical
  induction S using Finset.induction with
  | empty => rw [Finset.attach_empty, Finset.prod_empty, Finset.sum_empty, factorization_one,
      Finsupp.coe_zero, Pi.zero_apply]
  | insert a s ha ih =>
    rw [Finset.attach_insert, Finset.prod_insert, Finset.sum_insert,
      factorization_mul (pow_ne_zero _ a.2.2)
        (Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)), Finsupp.add_apply,
      Finset.prod_image (fun x _ y _ h ↦ Subtype.ext (by simpa using h)),
      Finset.sum_image (fun x _ y _ h ↦ Subtype.ext (by simpa using h)), ih] <;>
    · rw [Finset.mem_image]
      rintro ⟨x, -, hx⟩
      exact ha ((Subtype.mk.inj hx) ▸ x.2)

open UniqueFactorizationMonoid in
/-- The exponent of `𝔮` in `∏_{𝔭 ∈ S} 𝔭 ^ e 𝔭` is `e 𝔮` if `𝔮 ∈ S`, else `0`. -/
private theorem factorization_prod_primePow_eq
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (e : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℕ)
    (𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 = if 𝔮 ∈ S then e 𝔮 else 0 := by
  classical
  rw [factorization_prod_primePow_apply L S e 𝔮]
  simp_rw [factorization_primePow_apply L]
  by_cases h𝔮 : 𝔮 ∈ S
  · rw [if_pos h𝔮, Finset.sum_eq_single (⟨𝔮, h𝔮⟩ : {x // x ∈ S})]
    · rw [if_pos rfl]
    · rintro b _ hb
      rw [if_neg (fun h ↦ hb (Subtype.ext h.symm))]
    · exact fun h ↦ absurd (Finset.mem_attach S _) h
  · rw [if_neg h𝔮, Finset.sum_eq_zero]
    rintro ⟨b, hb⟩ -
    rw [if_neg (fun h : 𝔮 = b ↦ h𝔮 (h.symm ▸ hb))]

open UniqueFactorizationMonoid in
/-- The normalized prime factors of `𝔞` as a `Finset` of nonzero prime ideals. -/
private noncomputable def primeFactorsOf (𝔞 : NonzeroIdeal L) :
    Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
  (normalizedFactors 𝔞.1).toFinset.attach.map
    (⟨fun p : {x // x ∈ (normalizedFactors 𝔞.1).toFinset} ↦ (⟨p.1, by
        have hp := p.2
        rw [Multiset.mem_toFinset] at hp
        exact ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor p.1 hp),
          (prime_of_normalized_factor p.1 hp).ne_zero⟩⟩ :
        {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}),
      fun a b h ↦ Subtype.ext (congrArg
        (fun x : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (x : Ideal (𝓞 L))) h)⟩ :
      {x // x ∈ (normalizedFactors 𝔞.1).toFinset} ↪ {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})

open UniqueFactorizationMonoid in
/-- Every normalized prime factor `p` of `𝔞` is realised by an element of `primeFactorsOf 𝔞`. -/
private theorem mem_primeFactorsOf (𝔞 : NonzeroIdeal L) (p : Ideal (𝓞 L))
    (hp : p ∈ normalizedFactors 𝔞.1) :
    ∃ 𝔭 ∈ primeFactorsOf L 𝔞, 𝔭.1 = p := by
  refine ⟨⟨p, ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor p hp),
      (prime_of_normalized_factor p hp).ne_zero⟩⟩, ?_, rfl⟩
  rw [primeFactorsOf, Finset.mem_map]
  exact ⟨⟨p, by rwa [Multiset.mem_toFinset]⟩, Finset.mem_attach _ _, rfl⟩

open UniqueFactorizationMonoid in
private theorem factorization_idealOfExp_eq
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (f : S →₀ ℕ) (𝔮 : S) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭) 𝔮.1.1 = f 𝔮 := by
  classical
  have hprod : (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (fun q ↦ if h : q ∈ S then f ⟨q, h⟩ else 0) 𝔭.1)
      = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭 :=
    Finset.prod_congr rfl fun 𝔭 _ ↦ by simp only [dif_pos 𝔭.2]
  rw [← hprod, factorization_prod_primePow_eq L S
    (fun q ↦ if h : q ∈ S then f ⟨q, h⟩ else 0) 𝔮.1, if_pos 𝔮.2, dif_pos 𝔮.2]

open UniqueFactorizationMonoid in
private theorem prod_primePow_count_eq (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (𝔞 : NonzeroIdeal L) (hsupp : ∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) :
    (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1) = 𝔞.1 := by
  classical
  rw [show (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1)
      = ∏ p ∈ S.image (fun 𝔭 ↦ 𝔭.1), p ^ (normalizedFactors 𝔞.1).count p by
    rw [Finset.prod_image (fun x _ y _ h ↦ Subtype.ext h), ← Finset.prod_attach S
      (fun p ↦ p.1 ^ (normalizedFactors 𝔞.1).count p.1)]]
  rw [← Finset.prod_subset (s₁ := (normalizedFactors 𝔞.1).toFinset)
    (s₂ := S.image (fun 𝔭 ↦ 𝔭.1))
    (fun p hp ↦ by
      rw [Multiset.mem_toFinset] at hp
      obtain ⟨𝔭, h𝔭S, rfl⟩ := hsupp p hp
      exact Finset.mem_image.mpr ⟨𝔭, h𝔭S, rfl⟩)
    (fun p _ hp ↦ by
      rw [Multiset.mem_toFinset] at hp
      rw [Multiset.count_eq_zero_of_notMem hp, pow_zero])]
  conv_rhs => rw [← finprod_pow_count_eq_of_subsingleton_units 𝔞.2]
  exact (finprod_eq_finsetProd_of_mulSupport_subset _ (by
    intro p hp
    simp only [Function.mem_mulSupport] at hp
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    by_contra hc
    rw [Multiset.count_eq_zero_of_notMem hc, pow_zero] at hp
    exact hp rfl)).symm

/-! ### Weighted prime-ideal Euler product

A completely-multiplicative weight `w : Ideal (𝓞 L) → ℂ` with `‖w 𝔞‖ ≤ 1` twists the
prime-ideal Euler product into the weighted Dirichlet series
`Σ_𝔞 w(𝔞) N𝔞^{-s} = ∏_𝔭 (1 - w(𝔭) N𝔭^{-s})^{-1}`. With `w = 1` this is
`dedekindZeta_eq_tprod_primeIdeal`; the χ-twist `w = galoisCharacterOnIdeal K L χ` powers the
abelian Euler product (Sharifi 7.1.18). The proof mirrors the `w = 1` case verbatim, carrying
the multiplicative weight through the finite-`S` partial product and the `S ↑ ⊤` limit. -/

omit [NumberField L] in
/-- A completely-multiplicative weight `w` is multiplicative on prime-power products:
`w(∏_𝔭 𝔭^{e 𝔭}) = ∏_𝔭 w(𝔭)^{e 𝔭}`. The exponent is indexed over the subtype `S` to match
`prod_absNorm_cpow_eq_absNorm_prod_pow_cpow`. -/
private theorem weight_prod_primePow (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    w (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ S.attach, (w 𝔭.1.1) ^ e 𝔭 := by
  classical
  have wpow : ∀ (𝔭 : Ideal (𝓞 L)) (_ : 𝔭 ≠ ⊥) (k : ℕ), w (𝔭 ^ k) = (w 𝔭) ^ k := by
    intro 𝔭 h𝔭 k
    induction k with
    | zero => simpa using hw_one
    | succ n ih => rw [pow_succ, hw_mul (pow_ne_zero _ h𝔭) h𝔭, ih, pow_succ]
  have key : ∀ T : Finset S, w (∏ 𝔭 ∈ T, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ T, (w 𝔭.1.1) ^ e 𝔭 := by
    intro T
    induction T using Finset.induction with
    | empty => simpa using hw_one
    | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        hw_mul (pow_ne_zero _ a.1.2.2)
          (Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)),
        wpow a.1.1 a.1.2.2, ih]
  exact key S.attach

/-- The weighted finite Euler-factor identity: for the ratio `g 𝔭 = w(𝔭) N𝔭^{-s}`, the finite
product `∏_{𝔭 ∈ S} (1 - g 𝔭)⁻¹` is the Dirichlet partial sum `∑_𝔞 w(𝔞) N𝔞^{-s}` over the
`S`-factored ideals `𝔞 = ∏_𝔭 𝔭^{e 𝔭}`. -/
private theorem weighted_prod_eulerFactor_eq_tsum {s : ℂ} (hs : 1 < s.re)
    (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (idealOfExp : (S →₀ ℕ) → NonzeroIdeal L)
    (hidealOfExp : ∀ e : S →₀ ℕ,
      (idealOfExp e).1 = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭)
    (hinj : Function.Injective idealOfExp) :
    (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
      = ∑' 𝔞 : Set.range idealOfExp,
          w 𝔞.1.1 * (Ideal.absNorm 𝔞.1.1 : ℂ) ^ (-s) := by
  classical
  have hg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := fun 𝔭 ↦
    ((norm_mul_le_of_le (hw_norm _) le_rfl).trans_eq (one_mul _)).trans_lt
      (norm_absNorm_cpow_neg_lt_one L hs 𝔭)
  have hHS := (finsetGeometricProd_summable_and_hasSum
    (fun 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) hg S).2
  have hsummand : ∀ e : S →₀ ℕ,
      (∏ 𝔭 ∈ S.attach, (w 𝔭.1.1 * (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)
        = w (idealOfExp e).1 * (Ideal.absNorm (idealOfExp e).1 : ℂ) ^ (-s) := fun e ↦ by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib,
      show (∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)
        = ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) from
      Finset.prod_congr rfl fun 𝔭 _ ↦ by
        rw [← Complex.cpow_nat_mul]
        ring_nf,
      prod_absNorm_cpow_eq_absNorm_prod_pow_cpow L S (fun 𝔭 ↦ e 𝔭),
      ← weight_prod_primePow L w hw_one hw_mul S (fun 𝔭 ↦ e 𝔭), hidealOfExp e]
  have hHS' : HasSum
      (fun e : S →₀ ℕ ↦ w (idealOfExp e).1 * (Ideal.absNorm (idealOfExp e).1 : ℂ) ^ (-s))
      (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) := by
    have hbase := (Finsupp.equivFunOnFinite (α := S) (M := ℕ)).hasSum_iff.mpr hHS
    refine hbase.congr_fun fun e ↦ ?_
    simp only [Function.comp_apply, Finsupp.equivFunOnFinite_apply]
    exact (hsummand e).symm
  rw [← hHS'.tsum_eq]
  exact (tsum_range
    (fun 𝔞 : NonzeroIdeal L ↦ w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) hinj).symm

open UniqueFactorizationMonoid in
/-- **Weighted prime-ideal Euler product**: for a completely-multiplicative weight `w` with
`‖w 𝔞‖ ≤ 1` and `1 < Re s`,
`∑_𝔞 w(𝔞) N𝔞^{-s} = ∏_𝔭 (1 - w(𝔭) N𝔭^{-s})^{-1}` over the nonzero prime ideals. This is the
`w`-twisted analogue of `dedekindZeta_eq_tprod_primeIdeal` (Sharifi 7.1.18). -/
theorem weighted_eulerProduct_eq_tsum {s : ℂ} (hs : 1 < s.re)
    (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1) :
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
      = ∑' 𝔞 : NonzeroIdeal L, w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) := by
  classical
  set P := {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
  set Dw : NonzeroIdeal L → ℂ := fun 𝔞 ↦ w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) with hDw
  set idealOfExp : (S : Finset P) → (S →₀ ℕ) → NonzeroIdeal L :=
    fun S e ↦ ⟨∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭,
      Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)⟩ with hidealOfExp
  have hnormD : Summable fun 𝔞 : NonzeroIdeal L ↦ ‖Dw 𝔞‖ := by
    refine ((hasSum_nonzeroIdeal_absNorm_cpow L hs).summable.norm).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun 𝔞 ↦ ?_)
    rw [hDw]
    exact (norm_mul_le_of_le (hw_norm _) le_rfl).trans_eq (one_mul _)
  have hinj : ∀ S : Finset P, Function.Injective (idealOfExp S) := by
    intro S e e' h
    rw [hidealOfExp, Subtype.mk.injEq] at h
    ext 𝔮
    rw [← factorization_idealOfExp_eq L S e 𝔮, ← factorization_idealOfExp_eq L S e' 𝔮, h]
  have hmem : ∀ (S : Finset P) (𝔞 : NonzeroIdeal L),
      (∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) →
      𝔞 ∈ Set.range (idealOfExp S) := by
    intro S 𝔞 hsupp
    refine ⟨Finsupp.onFinset S.attach
      (fun 𝔭 ↦ (normalizedFactors 𝔞.1).count 𝔭.1.1) (by simp), ?_⟩
    rw [hidealOfExp, Subtype.ext_iff]
    simpa only [Finsupp.onFinset_apply] using prod_primePow_count_eq L S 𝔞 hsupp
  have hpartial : ∀ S : Finset P,
      (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
        = ∑' 𝔞 : Set.range (idealOfExp S), Dw 𝔞.1 := by
    intro S
    exact weighted_prod_eulerFactor_eq_tsum L hs w hw_one hw_mul hw_norm S (idealOfExp S)
      (fun e ↦ rfl) (hinj S)
  refine HasProd.tprod_eq ?_
  rw [HasProd, SummationFilter.unconditional, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero (fun 𝔞 ↦ ‖Dw 𝔞‖)).eventually
    (gt_mem_nhds hε)).exists
  refine ⟨F.biUnion (primeFactorsOf L), fun S hS ↦ ?_⟩
  have hF_sub : ∀ 𝔞 ∈ F, 𝔞 ∈ Set.range (idealOfExp S) := by
    intro 𝔞 h𝔞F
    refine hmem S 𝔞 fun p hp ↦ ?_
    obtain ⟨𝔭, h𝔭, rfl⟩ := mem_primeFactorsOf L 𝔞 p hp
    exact ⟨𝔭, hS (Finset.mem_biUnion.mpr ⟨𝔞, h𝔞F, h𝔭⟩), rfl⟩
  rw [dist_eq_norm, hpartial S]
  have hsplit : ∑' 𝔞 : NonzeroIdeal L, Dw 𝔞 =
      (∑' 𝔞 : Set.range (idealOfExp S), Dw 𝔞.1) +
        ∑' 𝔞 : ↥(Set.range (idealOfExp S))ᶜ, Dw 𝔞.1 :=
    (hnormD.of_norm.tsum_subtype_add_tsum_subtype_compl _).symm
  rw [hsplit, sub_add_cancel_left, norm_neg]
  refine (norm_tsum_le_tsum_norm (hnormD.subtype _)).trans_lt ?_
  refine lt_of_le_of_lt ?_ hF
  refine (hnormD.subtype _).tsum_le_tsum_of_inj
    (fun 𝔞 : ↥(Set.range (idealOfExp S))ᶜ ↦
      (⟨𝔞.1, fun h ↦ 𝔞.2 (hF_sub 𝔞.1 h)⟩ : {x // x ∉ F}))
    (fun x y h ↦ Subtype.ext (congrArg (fun z : {x // x ∉ F} ↦ (z : NonzeroIdeal L)) h))
    (fun _ _ ↦ norm_nonneg _) (fun _ ↦ le_rfl) (hnormD.subtype _)

open UniqueFactorizationMonoid in
/-- **Prime-ideal Euler product** (Sharifi, *Algebraic Number Theory*, Theorem 7.1.12,
p. 140): for `1 < Re s`, `ζ_K(s) = ∏_𝔭 (1 - N𝔭^{-s})^{-1}` over the nonzero prime ideals. -/
theorem dedekindZeta_eq_tprod_primeIdeal {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
        (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹ := by
  have hw := weighted_eulerProduct_eq_tsum L hs (fun _ ↦ 1) (by simp) (by simp) (by simp)
  simp only [one_mul] at hw
  exact (hw.trans (hasSum_nonzeroIdeal_absNorm_cpow L hs).tsum_eq).symm

/-- For real `s > 1`, `ζ_K(s)` is a positive real (Sharifi Def 7.1.11, p. 140). -/
theorem dedekindZeta_re_pos_of_one_lt (s : ℝ) (hs : 1 < s) :
    0 < (NumberField.dedekindZeta L (s : ℂ)).re := by
  have hs' : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  set g : ℕ → ℝ := fun n ↦ (idealNormMultiplicity L n : ℝ) * (n : ℝ) ^ (-s) with hg
  have key : ∀ n : ℕ,
      (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) = ((g n : ℝ) : ℂ) := by
    intro n
    have hcast : ((n : ℝ) ^ (-s) : ℝ) = ((n : ℂ) ^ (-(s : ℂ))) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-s)]
      norm_cast
    rw [hg]
    push_cast [hcast]
    ring
  have hsumC : Summable
      fun n : ℕ ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-(s : ℂ)) :=
    (summable_idealNormMultiplicity_mul_cpow_neg L hs').of_norm
  have hsumR : Summable g := Complex.summable_ofReal.mp (by simpa only [key] using hsumC)
  have hre : (NumberField.dedekindZeta L (s : ℂ)).re = ∑' n : ℕ, g n := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs']
    simp_rw [key]
    rw [Complex.re_tsum (by simpa only [key] using hsumC)]
    simp
  rw [hre]
  refine hsumR.tsum_pos (fun n ↦ ?_) 1 ?_
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rw [hg]
    simp [idealNormMultiplicity_one]

end NumberFieldEulerProduct

end Chebotarev
