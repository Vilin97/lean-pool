/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.CompleteDomain.CompleteDomain
import LeanPool.AndersonConjecture.Jensen.Construction.Construction
import Mathlib.Algebra.CharP.Algebra

/-!
# Jensen's Theorem on Completions of UFDs

Under suitable hypotheses on a complete local domain T, one
constructs a local UFD A whose adic completion is T and whose
generic formal fiber is trivial (Jensen, 2006, Corollary 2.4).
-/

noncomputable section

/-
## Verification conditions for T

T = ℂ[[x,y,z]]/(x²-yz) from CompleteDomain.lean must satisfy:
1. depth T ≥ 2 (regular sequence of length 2 in M)
2. |T| = |T/M| (both = |ℂ|)
3. No integer is a zero divisor (char 0 domain)
-/

instance T_charZero : CharZero T :=
  charZero_of_injective_algebraMap (R := ℂ) (FaithfulSMul.algebraMap_injective ℂ T)

/-- No nonzero integer maps to zero in T (char 0 domain). -/
theorem jensen_T_no_integer_zerodivisor
    (n : ℤ) (hn : n ≠ 0) : (algebraMap ℤ T n) ≠ 0 := by
  intro h
  apply hn
  rw [eq_intCast (algebraMap ℤ T)] at h
  have : ((n : ℤ) : T) = ((0 : ℤ) : T) := by push_cast
                                             exact h
  exact Int.cast_injective this

/-- |T| = |T/M|: both have cardinality |ℂ|. -/
theorem jensen_T_card_eq_residue_card :
    Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T) := by
  rw [T_card_eq, T_residueField_card]

open MvPowerSeries in
lemma conjI_le_ker_ccf :
    conjI ≤ RingHom.ker (MvPowerSeries.constantCoeff (σ := Fin 3) (R := ℂ)) := by
  apply Ideal.span_le.mpr
  intro g hg
  simp only [Set.mem_singleton_iff] at hg
  subst hg
  simp only [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, map_pow]
  simp [MvPowerSeries.constantCoeff_X]

open MvPowerSeries in
lemma mk_in_maxIdeal (f : MvPowerSeries (Fin 3) ℂ)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    Ideal.Quotient.mk conjI f ∈ IsLocalRing.maximalIdeal T := by
  rw [IsLocalRing.mem_maximalIdeal]
  intro ⟨u, hu⟩
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective u.inv
  have hmul : f * g - 1 ∈ conjI := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, map_mul, map_one]
    calc Ideal.Quotient.mk conjI f * Ideal.Quotient.mk conjI g
        = ↑u * u.inv := by rw [← hu, ← hg]
      _ = 1 := u.val_inv
  have h0 := conjI_le_ker_ccf hmul
  rw [RingHom.mem_ker, map_sub, map_mul, map_one, hf, zero_mul, zero_sub] at h0
  exact one_ne_zero (neg_eq_zero.mp h0)

open MvPowerSeries in
lemma coeff_gen_zero_of_le_single (s : Fin 3) (b : Fin 3 →₀ ℕ)
    (hb : ∀ i, b i ≤ (Finsupp.single s 1) i) :
    (MvPowerSeries.coeff b)
      ((X 0 : MvPowerSeries (Fin 3) ℂ) ^ 2 - X 1 * X 2) = 0 := by
  simp only [map_sub]
  have hX0sq : (MvPowerSeries.coeff b) ((X 0 : MvPowerSeries (Fin 3) ℂ) ^ 2) = 0 := by
    rw [sq, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨c, d⟩ hcd
    simp only [Finset.mem_antidiagonal] at hcd
    simp only [MvPowerSeries.coeff_X]
    by_cases hc : c = Finsupp.single 0 1
    · simp only [hc, ite_true, one_mul, ite_eq_right_iff, one_ne_zero, imp_false]
      intro hd
      have : b 0 = 2 := by
        have := congr_arg (· 0) hcd
        simp [hc, hd, Finsupp.add_apply] at this
        omega
      have : b 0 ≤ 1 := by
        calc b 0 ≤ (Finsupp.single s 1) 0 := hb 0
          _ ≤ 1 := by simp [Finsupp.single_apply]
                      split <;> omega
      omega
    · simp [hc]
  have hX1X2 : (MvPowerSeries.coeff b) ((X 1 : MvPowerSeries (Fin 3) ℂ) * X 2) = 0 := by
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨c, d⟩ hcd
    simp only [Finset.mem_antidiagonal] at hcd
    simp only [MvPowerSeries.coeff_X]
    by_cases hc : c = Finsupp.single 1 1
    · simp only [hc, ite_true, one_mul, ite_eq_right_iff, one_ne_zero, imp_false]
      intro hd
      have hb1 : b 1 = 1 := by
        have := congr_arg (· 1) hcd
        simp [hc, hd, Finsupp.add_apply] at this
        omega
      have hb2 : b 2 = 1 := by
        have := congr_arg (· 2) hcd
        simp [hc, hd, Finsupp.add_apply] at this
        omega
      fin_cases s
      · have := hb 1
        simp at this
        omega
      · have := hb 2
        simp at this
        omega
      · have := hb 1
        simp at this
        omega
    · simp [hc]
  rw [hX0sq, hX1X2, sub_self]

open MvPowerSeries in
lemma mk_X1_ne_zero' : (Ideal.Quotient.mk conjI (X 1) : T) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, conjI, Ideal.mem_span_singleton]
  intro ⟨h, hh⟩
  have hlhs : (MvPowerSeries.coeff (Finsupp.single 1 1))
      (X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ) = 1 := by simp [MvPowerSeries.coeff_X]
  have hrhs : (MvPowerSeries.coeff (Finsupp.single 1 1))
      (h * (X (0 : Fin 3) ^ 2 - X 1 * X 2)) = 0 := by
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨a, b⟩ hab
    simp only [Finset.mem_antidiagonal] at hab
    have hble : ∀ i, b i ≤ (Finsupp.single (1 : Fin 3) 1) i := by
      intro i
      have := congr_arg (· i) hab
      simp [Finsupp.add_apply] at this
      omega
    simp [coeff_gen_zero_of_le_single 1 b hble]
  rw [mul_comm] at hh
  exact one_ne_zero (hlhs.symm.trans
    (congr_arg (MvPowerSeries.coeff (Finsupp.single 1 1)) hh) |>.trans hrhs)

open MvPowerSeries in
lemma mk_X2_ne_zero' : (Ideal.Quotient.mk conjI (X 2) : T) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem, conjI, Ideal.mem_span_singleton]
  intro ⟨h, hh⟩
  have hlhs : (MvPowerSeries.coeff (Finsupp.single 2 1))
      (X (2 : Fin 3) : MvPowerSeries (Fin 3) ℂ) = 1 := by simp [MvPowerSeries.coeff_X]
  have hrhs : (MvPowerSeries.coeff (Finsupp.single 2 1))
      (h * (X (0 : Fin 3) ^ 2 - X 1 * X 2)) = 0 := by
    rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨a, b⟩ hab
    simp only [Finset.mem_antidiagonal] at hab
    have hble : ∀ i, b i ≤ (Finsupp.single (2 : Fin 3) 1) i := by
      intro i
      have := congr_arg (· i) hab
      simp [Finsupp.add_apply] at this
      omega
    simp [coeff_gen_zero_of_le_single 2 b hble]
  rw [mul_comm] at hh
  exact one_ne_zero (hlhs.symm.trans
    (congr_arg (MvPowerSeries.coeff (Finsupp.single 2 1)) hh) |>.trans hrhs)

lemma T_smulRegular_of_ne_zero_local (a : T) (ha : a ≠ 0) : IsSMulRegular T a := by
  intro x y h
  have : a * (x - y) = 0 := by rw [mul_sub]
                               exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ha)

open MvPowerSeries in
/-- Shift the `X₁`-exponent down by one: `(shiftX1' f)(m) = f (m + single 1 1)`. -/
noncomputable def shiftX1' (f : MvPowerSeries (Fin 3) ℂ) :
    MvPowerSeries (Fin 3) ℂ := fun m => f (m + Finsupp.single 1 1)

open MvPowerSeries in
/-- The "`X₁ = 0` restriction divided by `X₀²`": `(divR' f)(m) = f(m₀+2, 0, m₂)`
when `m₁ = 0`, and `0` otherwise. -/
noncomputable def divR' (f : MvPowerSeries (Fin 3) ℂ) :
    MvPowerSeries (Fin 3) ℂ :=
  fun m => if m 1 = 0 then f (Finsupp.update m 0 (m 0 + 2)) else 0

open MvPowerSeries in
lemma coeff_lhs' (f : MvPowerSeries (Fin 3) ℂ) (d : Fin 3 →₀ ℕ) :
    coeff d (f - X 1 * shiftX1' f) = if d 1 = 0 then coeff d f else 0 := by
  simp only [map_sub]
  rw [show (X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
    MvPowerSeries.monomial (R := ℂ) (Finsupp.single 1 1) 1 from rfl]
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases hle : Finsupp.single (1 : Fin 3) 1 ≤ d
  · have hd1 : d 1 ≠ 0 := by
      have := hle 1
      simp [Finsupp.single_eq_same] at this
      omega
    simp only [hle, ite_true, one_mul, hd1, ite_false, sub_eq_zero]
    change f d = shiftX1' f (d - Finsupp.single 1 1)
    simp only [shiftX1']
    show f d = f (d - Finsupp.single 1 1 + Finsupp.single 1 1)
    rw [tsub_add_cancel_of_le hle]
  · have hd1 : d 1 = 0 := by
      by_contra h
      apply hle
      intro i
      simp only [Finsupp.single_apply]
      by_cases hi : i = 1
      · subst hi
        simp
        omega
      · simp [show (1 : Fin 3) ≠ i from fun h => hi h.symm]
    simp [hle, hd1]

open MvPowerSeries in
lemma coeff_rhs' (f : MvPowerSeries (Fin 3) ℂ) (d : Fin 3 →₀ ℕ) :
    coeff d (X (0 : Fin 3) ^ 2 * divR' f) =
      if 2 ≤ d 0 ∧ d 1 = 0 then coeff d f else 0 := by
  rw [show (X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 =
    MvPowerSeries.monomial (R := ℂ) (Finsupp.single 0 2) 1 from
    MvPowerSeries.X_pow_eq 0 2]
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases hle : Finsupp.single (0 : Fin 3) 2 ≤ d
  · have hd0 : 2 ≤ d 0 := by
      have := hle 0
      simp only [Finsupp.single_eq_same] at this
      exact this
    simp only [hle, ite_true, one_mul]
    by_cases hd1 : d 1 = 0
    · simp only [hd0, hd1, true_and, ite_true]
      change divR' f (d - Finsupp.single 0 2) = f d
      unfold divR'
      set d' := (d - Finsupp.single (0 : Fin 3) 2 : Fin 3 →₀ ℕ) with hd'_def
      have hsub1 : d' 1 = 0 := by simp [hd'_def, Finsupp.tsub_apply, hd1]
      simp only [hsub1, ite_true]
      congr 1
      ext i
      simp only [Finsupp.update_apply, hd'_def, Finsupp.tsub_apply, Finsupp.single_apply]
      fin_cases i <;> simp_all
    · simp only [hd1, and_false, ite_false]
      change divR' f (d - Finsupp.single 0 2) = 0
      unfold divR'
      set d' := (d - Finsupp.single (0 : Fin 3) 2 : Fin 3 →₀ ℕ) with hd'_def
      have hsub1 : d' 1 = d 1 := by simp [hd'_def, Finsupp.tsub_apply]
      simp [hsub1, hd1]
  · have hd0 : ¬ (2 ≤ d 0) := by
      intro h
      apply hle
      intro i
      simp only [Finsupp.single_apply]
      by_cases hi : i = 0
      · subst hi
        simp only [Fin.isValue, ↓reduceIte]
        exact h
      · simp [show (0 : Fin 3) ≠ i from fun h => hi h.symm]
    simp [hle, hd0]

open MvPowerSeries in
lemma coeff_gen_zero' (a : Fin 3 →₀ ℕ) (ha0 : a 0 < 2) (ha1 : a 1 = 0) :
    coeff a (X (0 : Fin 3) ^ 2 - X 1 * X 2 : MvPowerSeries (Fin 3) ℂ) = 0 := by
  simp only [map_sub, sub_eq_zero]
  have hX0sq : coeff a ((X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2) = 0 := by
    rw [MvPowerSeries.coeff_X_pow]
    simp only [Fin.isValue, ite_eq_right_iff, one_ne_zero, imp_false]
    intro h
    subst h
    simp [Finsupp.single_eq_same] at ha0
  have hX1X2 : coeff a ((X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ) * X 2) = 0 := by
    rw [show (X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
      MvPowerSeries.monomial (R := ℂ) (Finsupp.single 1 1) 1 from rfl]
    rw [MvPowerSeries.coeff_monomial_mul]
    split_ifs with hle
    · exfalso
      have := hle 1
      simp [Finsupp.single_eq_same] at this
      omega
    · rfl
  rw [hX0sq, hX1X2]

open MvPowerSeries in
lemma coeff_gen_mul_zero' (k : MvPowerSeries (Fin 3) ℂ)
    (d : Fin 3 →₀ ℕ) (hd0 : d 0 < 2) (hd1 : d 1 = 0) :
    coeff d ((X (0 : Fin 3) ^ 2 - X 1 * X 2 : MvPowerSeries (Fin 3) ℂ) * k) = 0 := by
  rw [MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_antidiagonal] at hab
  have ha0 : a 0 < 2 := by
    have := congr_arg (· 0) hab
    simp [Finsupp.add_apply] at this
    omega
  have ha1 : a 1 = 0 := by
    have := congr_arg (· 1) hab
    simp [Finsupp.add_apply] at this
    omega
  simp [coeff_gen_zero' a ha0 ha1]

open MvPowerSeries in
lemma coeff_f_vanish' (f g : MvPowerSeries (Fin 3) ℂ)
    (hmem : X 2 * f - X 1 * g ∈ conjI) (d : Fin 3 →₀ ℕ)
    (hd1 : d 1 = 0) (hd0 : d 0 < 2) : coeff d f = 0 := by
  rw [conjI, Ideal.mem_span_singleton] at hmem
  obtain ⟨k, hk⟩ := hmem
  set e := d + Finsupp.single 2 1 with he_def
  have he0 : e 0 = d 0 := by simp [he_def, Finsupp.add_apply]
  have he1 : e 1 = 0 := by simp [he_def, Finsupp.add_apply, hd1]
  have hle2 : Finsupp.single (2 : Fin 3) 1 ≤ e := by
    intro i
    simp only [he_def, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hnle1 : ¬ Finsupp.single (1 : Fin 3) 1 ≤ e := by
    intro h
    have h1 := h 1
    simp only [Finsupp.single_apply, ite_true] at h1
    rw [he1] at h1
    omega
  have hlhs : coeff e (X 2 * f - X 1 * g) = coeff d f := by
    rw [map_sub]
    rw [show (X (2 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
      MvPowerSeries.monomial (R := ℂ) (Finsupp.single 2 1) 1 from rfl]
    rw [show (X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
      MvPowerSeries.monomial (R := ℂ) (Finsupp.single 1 1) 1 from rfl]
    rw [MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul]
    simp only [hle2, ite_true, hnle1, ite_false, one_mul, sub_zero]
    change f (e - Finsupp.single 2 1) = f d
    congr 1
    simp [he_def, add_tsub_cancel_right]
  have hrhs : coeff e ((X (0 : Fin 3) ^ 2 - X 1 * X 2) * k) = 0 :=
    coeff_gen_mul_zero' k e (he0 ▸ hd0) he1
  have := congr_arg (coeff e) hk
  rw [hlhs, hrhs] at this
  exact this

open MvPowerSeries in
lemma key_decomp' (f g : MvPowerSeries (Fin 3) ℂ)
    (hmem : X 2 * f - X 1 * g ∈ conjI) :
    f - X 1 * (shiftX1' f + X 2 * divR' f) ∈ conjI := by
  -- Step 1: f - X₁ * shiftX1' f = X₀² * divR' f
  have hrest : f - X 1 * shiftX1' f = (X (0 : Fin 3)) ^ 2 * divR' f := by
    ext d
    rw [coeff_lhs', coeff_rhs']
    by_cases hd1 : d 1 = 0
    · rw [if_pos hd1]
      by_cases hd0 : 2 ≤ d 0
      · rw [if_pos ⟨hd0, hd1⟩]
      · rw [if_neg (fun h => hd0 h.1)]
        exact coeff_f_vanish' f g hmem d hd1 (by omega)
    · rw [if_neg hd1, if_neg (fun h => hd1 h.2)]
  -- Step 2: f - X₁ * (shiftX1' f + X₂ * divR' f) = (X₀² - X₁X₂) * divR' f
  have heq : f - X 1 * (shiftX1' f + X 2 * divR' f) =
    (X 0 ^ 2 - X 1 * X 2 : MvPowerSeries (Fin 3) ℂ) * divR' f := by
    linear_combination hrest
  rw [heq, conjI, Ideal.mem_span_singleton]
  exact ⟨divR' f, rfl⟩

/-- depth T ≥ 2: the images of y and z form a regular sequence in M.
T = ℂ[[x,y,z]]/(x²-yz) is Cohen-Macaulay of dimension 2. -/
theorem jensen_T_depth_ge_two :
    ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b] := by
  open MvPowerSeries in
  refine ⟨Ideal.Quotient.mk conjI (X 1),
    Ideal.Quotient.mk conjI (X 2),
    mk_in_maxIdeal _ (by simp [MvPowerSeries.constantCoeff_X]),
    mk_in_maxIdeal _ (by simp [MvPowerSeries.constantCoeff_X]),
    ?_⟩
  apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;>
      exact mk_in_maxIdeal _ (by simp [MvPowerSeries.constantCoeff_X])
  · rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
    refine ⟨T_smulRegular_of_ne_zero_local _ mk_X1_ne_zero', ?_⟩
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
    refine ⟨?_, ⟨fun i hi => by simp at hi⟩⟩
    -- z is a non-zerodivisor in T/(y) = QuotSMulTop y T
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro x hx
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    obtain ⟨t, _, ht⟩ := hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective t
    have hmem : X 2 * f - X 1 * g ∈ conjI := by
      have : Ideal.Quotient.mk conjI (X 2 * f - X 1 * g) = 0 := by
        simp only [map_sub, map_mul]
        exact sub_eq_zero.mpr ht.symm
      rwa [Ideal.Quotient.eq_zero_iff_mem] at this
    refine ⟨Ideal.Quotient.mk conjI (shiftX1' f + X 2 * divR' f),
      Submodule.mem_top, ?_⟩
    change Ideal.Quotient.mk conjI (X 1) *
      Ideal.Quotient.mk conjI (shiftX1' f + X 2 * divR' f) =
      Ideal.Quotient.mk conjI f
    rw [← map_mul, eq_comm, ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (key_decomp' f g hmem)

/-
## Jensen's Corollary 2.4 — transfinite construction

For T a complete local domain with depth ≥ 2, |T/M| = |T|, char 0,
construct a local UFD A with Â ≅ T and HasTrivialGenericFormalFiber A.

The construction uses:
- initial_NSubring (NSubring.lean) — starting R₀ ≅ ℚ
- combined_step (CombinedStep.lean) — successor: adjoin + close-up
- transfinite_union (TransfiniteUnion.lean) — limit step
- heitmann_prop1 (Construction.lean) — surjectivity + closure ⟹ Noetherian + Â ≅ T
See references/heitmann_1993.md Theorem 8 and references/jensen_2006.md Corollary 2.4.
-/

-- Local copies of Construction.lean theorems (circular import workaround)

/-- In a local domain with depth ≥ 2, M is not an associated prime of T/rT
for any nonzero r. (Local copy of Construction.maximal_not_assoc_of_depth_ge_two.) -/
theorem maximal_not_assoc_local
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (r : T) (hr : r ≠ 0) :
    IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}) := by
  intro hM_assoc
  obtain ⟨a, b, ha_mem, hb_mem, hreg⟩ := hdepth
  rw [RingTheory.Sequence.isRegular_cons_iff] at hreg
  obtain ⟨ha_reg, hreg_b⟩ := hreg
  rw [RingTheory.Sequence.isRegular_cons_iff] at hreg_b
  obtain ⟨hb_reg_mod_a, _⟩ := hreg_b
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff] at hM_assoc
  obtain ⟨_, x, hx_ann⟩ := hM_assoc
  have hx_ne : x ≠ 0 := by
    intro hx0
    rw [hx0] at hx_ann
    have : IsLocalRing.maximalIdeal T = ⊤ := by
      rw [hx_ann]
      ext t
      simp
    exact (IsLocalRing.maximalIdeal.isMaximal T).ne_top this
  obtain ⟨x_lift, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hx_not_mem : x_lift ∉ Ideal.span ({r} : Set T) := by
    intro h
    apply hx_ne
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr h
  have ha_in_ann : a ∈ (⊥ : Submodule T (T ⧸ Ideal.span {r})).colon
      {Ideal.Quotient.mk (Ideal.span {r}) x_lift} := by
    rw [← hx_ann]
    exact ha_mem
  have ha_mul : a * x_lift ∈ Ideal.span ({r} : Set T) := by
    rw [Submodule.mem_colon] at ha_in_ann
    have := ha_in_ann (Ideal.Quotient.mk _ x_lift) (Set.mem_singleton _)
    rw [Submodule.mem_bot] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact this
  have hb_in_ann : b ∈ (⊥ : Submodule T (T ⧸ Ideal.span {r})).colon
      {Ideal.Quotient.mk (Ideal.span {r}) x_lift} := by
    rw [← hx_ann]
    exact hb_mem
  have hb_mul : b * x_lift ∈ Ideal.span ({r} : Set T) := by
    rw [Submodule.mem_colon] at hb_in_ann
    have := hb_in_ann (Ideal.Quotient.mk _ x_lift) (Set.mem_singleton _)
    rw [Submodule.mem_bot] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact this
  rw [Ideal.mem_span_singleton] at ha_mul hb_mul
  obtain ⟨y₁, hy₁⟩ := ha_mul
  obtain ⟨y₂, hy₂⟩ := hb_mul
  have h_eq : r * (b * y₁) = r * (a * y₂) := by
    have h1 : b * (a * x_lift) = a * (b * x_lift) := by ring
    rw [hy₁, hy₂] at h1
    calc r * (b * y₁) = b * (r * y₁) := by ring
    _ = a * (r * y₂) := h1
    _ = r * (a * y₂) := by ring
  have h_cancel : b * y₁ = a * y₂ := by
    have h_sub : r * (b * y₁ - a * y₂) = 0 := by rw [mul_sub]
                                                 exact sub_eq_zero.mpr h_eq
    exact sub_eq_zero.mp ((mul_eq_zero.mp h_sub).resolve_left hr)
  have hby₁_mem : b * y₁ ∈ Ideal.span ({a} : Set T) :=
    Ideal.mem_span_singleton.mpr ⟨y₂, h_cancel⟩
  open Pointwise in
  have hy₁_in_aT : y₁ ∈ Ideal.span ({a} : Set T) := by
    have h_eq : (Ideal.span ({a} : Set T) : Submodule T T) = (a • ⊤ : Submodule T T) := by
      ext x
      constructor
      · intro hx
        rw [Ideal.mem_span_singleton] at hx
        obtain ⟨c, rfl⟩ := hx
        exact Submodule.smul_mem_pointwise_smul c a ⊤ Submodule.mem_top
      · intro hx
        have : x ∈ (a • (⊤ : Set T) : Set T) := SetLike.mem_coe.mpr hx
        rw [Set.mem_smul_set] at this
        obtain ⟨c, _, rfl⟩ := this
        exact Ideal.mem_span_singleton.mpr ⟨c, by rw [smul_eq_mul]⟩
    have hby₁_smul : b * y₁ ∈ (a • ⊤ : Submodule T T) := h_eq ▸ hby₁_mem
    have hy₁_smul : y₁ ∈ (a • ⊤ : Submodule T T) :=
      mem_of_isSMulRegular_quotient_of_smul_mem hb_reg_mod_a (by rwa [smul_eq_mul])
    rw [h_eq]
    exact hy₁_smul
  rw [Ideal.mem_span_singleton] at hy₁_in_aT
  obtain ⟨z, hz⟩ := hy₁_in_aT
  have h_ax : a * x_lift = a * (r * z) := by rw [hy₁, hz]
                                             ring
  have h_x_eq : x_lift = r * z := by
    have := ha_reg (show a • x_lift = a • (r * z) by rwa [smul_eq_mul, smul_eq_mul])
    exact this
  exact hx_not_mem (Ideal.mem_span_singleton.mpr ⟨z, h_x_eq⟩)

/-- Heitmann's Proposition 1, Noetherian part: if R → T/M² is surjective and
IT ∩ R = I for all f.g. ideals, then R is Noetherian.
(Local copy of the first conjunct of Construction.heitmann_prop1.) -/
theorem heitmann_prop1_noetherian
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : Subring T) [IsLocalRing R]
    (h_closed : ∀ (I : Ideal R), I.FG →
      ∀ (c : R), (c : T) ∈ Ideal.map R.subtype I → c ∈ I) :
    IsNoetherianRing R := by
  rw [isNoetherianRing_iff_ideal_fg]
  intro I
  have hIT_fg : (Ideal.map R.subtype I).FG := IsNoetherian.noetherian _
  have hIT_eq : Ideal.map R.subtype I = Ideal.span (R.subtype '' (I : Set R)) := rfl
  rw [hIT_eq] at hIT_fg
  obtain ⟨s', hs'_sub, hs'_span⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R.subtype '' (I : Set R))).mp hIT_fg
  classical
  have h_preimage : ∀ t ∈ (s' : Set T), ∃ (r : R), r ∈ I ∧ R.subtype r = t := by
    intro t ht
    exact hs'_sub ht
  let f : (t : T) → t ∈ (s' : Set T) → R := fun t ht => (h_preimage t ht).choose
  have hf_mem : ∀ t (ht : t ∈ (s' : Set T)), f t ht ∈ I :=
    fun t ht => (h_preimage t ht).choose_spec.1
  have hf_eq : ∀ t (ht : t ∈ (s' : Set T)), R.subtype (f t ht) = t :=
    fun t ht => (h_preimage t ht).choose_spec.2
  set gen_set : Finset R :=
    s'.attach.image (fun ⟨t, ht⟩ => f t (Finset.mem_coe.mpr ht))
  have hgen_sub : (gen_set : Set R) ⊆ (I : Set R) := by
    intro r hr
    rw [Finset.mem_coe, Finset.mem_image] at hr
    obtain ⟨⟨t, ht⟩, _, rfl⟩ := hr
    exact hf_mem t (Finset.mem_coe.mpr ht)
  have hJ_fg : (Ideal.span (gen_set : Set R)).FG := ⟨gen_set, rfl⟩
  have hJT_eq : Ideal.map R.subtype (Ideal.span (gen_set : Set R)) =
      Ideal.map R.subtype I := by
    apply le_antisymm
    · rw [Ideal.map_span]
      apply Ideal.span_le.mpr
      intro t ht
      obtain ⟨r, hr, rfl⟩ := ht
      rw [hIT_eq]
      exact Ideal.subset_span ⟨r, hgen_sub hr, rfl⟩
    · rw [hIT_eq, Ideal.map_span]
      rw [show (Ideal.span (R.subtype '' (I : Set R)) : Ideal T) =
        Ideal.span (↑s' : Set T) from by exact_mod_cast hs'_span]
      apply Ideal.span_le.mpr
      intro t ht
      have ht' : t ∈ s' := Finset.mem_coe.mp ht
      apply Ideal.subset_span
      exact ⟨f t (Finset.mem_coe.mpr ht'),
        Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨t, ht'⟩, Finset.mem_attach _ _, rfl⟩),
        hf_eq t (Finset.mem_coe.mpr ht')⟩
  exact ⟨gen_set, le_antisymm (Ideal.span_le.mpr hgen_sub) (fun c hc =>
    h_closed _ hJ_fg c (hJT_eq ▸ Ideal.mem_map_of_mem R.subtype hc))⟩

lemma jensen_map_maxIdeal_le_of_closed
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : Subring T) [IsLocalRing ↥R]
    (h_closed : ∀ (I : Ideal ↥R), I.FG →
      ∀ (c : ↥R), (c : T) ∈ Ideal.map R.subtype I → c ∈ I) :
    Ideal.map R.subtype (IsLocalRing.maximalIdeal ↥R) ≤ IsLocalRing.maximalIdeal T := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap]
  by_contra hnotM
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hnotM
  have hI_fg : (Ideal.span ({r} : Set ↥R)).FG := ⟨{r}, by simp [Finset.coe_singleton]⟩
  have hr_map : (r : T) ∈ Ideal.map R.subtype (Ideal.span ({r} : Set ↥R)) :=
    Ideal.mem_map_of_mem R.subtype (Ideal.subset_span rfl)
  have htop : Ideal.map R.subtype (Ideal.span ({r} : Set ↥R)) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ hr_map hnotM
  have h1 : (1 : ↥R) ∈ Ideal.span ({r} : Set ↥R) := by
    apply h_closed _ hI_fg
    rw [htop]
    exact Submodule.mem_top
  have h_le : Ideal.span ({r} : Set ↥R) ≤ IsLocalRing.maximalIdeal ↥R :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hr)
  rw [(Ideal.eq_top_iff_one _).mpr h1] at h_le
  exact absurd (eq_top_iff.mpr h_le) (IsLocalRing.maximalIdeal.isMaximal ↥R).ne_top

lemma jensen_comap_maxIdeal_le_of_local
    (R : Subring T) [IsLocalRing ↥R] :
    (IsLocalRing.maximalIdeal T).comap R.subtype ≤ IsLocalRing.maximalIdeal ↥R := by
  intro r hr
  rw [Ideal.mem_comap] at hr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact fun hru => absurd hr (by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hru.map R.subtype)

-- Under Prop 1 hypotheses, M = M_R · T (extra synthesis budget needed for T's instance diamond)
lemma jensen_map_maxIdeal_eq_of_surj_closed
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : Subring T) [IsLocalRing ↥R]
    (h_surj : Function.Surjective (fun r : ↥R =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (r : T)))
    (h_closed : ∀ (I : Ideal ↥R), I.FG →
      ∀ (c : ↥R), (c : T) ∈ Ideal.map R.subtype I → c ∈ I) :
    Ideal.map R.subtype (IsLocalRing.maximalIdeal ↥R) = IsLocalRing.maximalIdeal T := by
  apply le_antisymm (jensen_map_maxIdeal_le_of_closed R h_closed)
  apply Submodule.le_of_le_smul_of_le_jacobson_bot
  · exact IsNoetherian.noetherian _
  · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
  · intro m hm
    obtain ⟨r, hr⟩ := h_surj (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) m)
    have hdiff : (r : T) - m ∈ IsLocalRing.maximalIdeal T ^ 2 :=
      (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal T ^ 2)).mp hr
    have hr_in_M : (r : T) ∈ IsLocalRing.maximalIdeal T := by
      rw [show (r : T) = ((r : T) - m) + m from by ring]
      exact (IsLocalRing.maximalIdeal T).add_mem (Ideal.pow_le_self two_ne_zero hdiff) hm
    have hr_in_MR : r ∈ IsLocalRing.maximalIdeal ↥R :=
      jensen_comap_maxIdeal_le_of_local R (Ideal.mem_comap.mpr hr_in_M)
    rw [show m = (r : T) + (m - (r : T)) from by ring]
    apply Submodule.add_mem_sup
    · exact Ideal.mem_map_of_mem R.subtype hr_in_MR
    · have hmr : m - (r : T) ∈ IsLocalRing.maximalIdeal T ^ 2 := by
        rw [show m - (r : T) = -((r : T) - m) from by ring]
        exact neg_mem hdiff
      rwa [sq] at hmr

-- jensen_construction unifies many deep typeclass instances across Construction/Application
/-- Jensen's Corollary 2.4 for P = (0): the deep transfinite construction.
Given verification conditions on T, produces a local UFD A with Â ≅ T
and trivial generic formal fiber. The full proof is in Construction.lean
and Application.lean
this local version avoids circular imports
since HasTrivialGenericFormalFiber is defined here and used in Construction.lean. -/
theorem jensen_construction
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (hcard : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hchar : ∀ (n : ℤ), n ≠ 0 → (algebraMap ℤ T n) ≠ 0)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsDomain A)
      (_ : UniqueFactorizationMonoid A) (_ : IsNoetherianRing A),
      Nonempty (AdicCompletion (@IsLocalRing.maximalIdeal A _ _) A ≃+* T) ∧
      @HasTrivialGenericFormalFiber A _ _ := by
  -- All primes P ≠ M have height ≤ 1 (from dim T = 2)
  have hht : ∀ (P : Ideal T), P.IsPrime →
      P ≠ IsLocalRing.maximalIdeal T → P.height ≤ 1 := by
    intro P hP hP_ne_M
    have hP_lt_M : P < IsLocalRing.maximalIdeal T :=
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hP.ne_top) hP_ne_M
    haveI : P.FiniteHeight := Ideal.finiteHeight_of_isNoetherianRing P
    have hP_ht_lt := Ideal.height_strict_mono_of_isPrime hP_lt_M
    have hM_ht : (IsLocalRing.maximalIdeal T).height = 2 := by
      have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := T)
      rw [T_ringKrullDim] at h
      exact WithBot.coe_injective h
    rw [hM_ht] at hP_ht_lt
    exact Order.le_of_lt_add_one hP_ht_lt
  -- Bridge algebra instance diamond: both ℤ-algebra maps on T equal Int.cast
  have hchar' : ∀ (n : ℤ), n ≠ 0 →
      @algebraMap ℤ T _ CommRing.toCommSemiring.toSemiring (Ring.toIntAlgebra T) n ≠ 0 := by
    intro n hn h
    apply hchar n hn
    rw [eq_intCast] at h ⊢
    exact h
  exact @jensen_construction_p0_uncountable T _ _ _ _ T_isAdicComplete hdepth hcard hchar'
    hT_aleph0 hht

/-
## jensen_special_case (= lem:jensen_special_case from blueprint)

Apply Jensen Cor 2.4 to T from CompleteDomain.lean with P = ⊥.
The output is a local UFD A whose completion is (isomorphic to) T,
and whose generic formal fiber is trivial (only ⊥ lies over ⊥).
-/

/-- There exists a 2-dimensional Noetherian local UFD A whose completion
is isomorphic to T and whose generic formal fiber is trivial.

This is Jensen's Corollary 2.4 applied to T with P = (0). -/
theorem jensen_special_case :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsDomain A)
      (_ : UniqueFactorizationMonoid A) (_ : IsNoetherianRing A),
      Nonempty (AdicCompletion (@IsLocalRing.maximalIdeal A _ _) A ≃+* T) ∧
      @HasTrivialGenericFormalFiber A _ _ := by
  have hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T := by
    rw [T_card_eq]
    rw [Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  exact jensen_construction
    jensen_T_depth_ge_two jensen_T_card_eq_residue_card
    jensen_T_no_integer_zerodivisor hT_aleph0

end
