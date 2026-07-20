/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.Construction.Construction
import LeanPool.AndersonConjecture.CompleteDomain.CompleteDomain

/-!
# Application to T = C[[x,y,z]]/(x^2 - yz)

The quotient T = C[[x,y,z]]/(x^2 - yz) is a complete local domain
of depth 2 with uncountable residue field C. We verify Jensen's
hypotheses (Corollary 2.4 with P = (0)) and apply the construction
to produce a local UFD whose completion is T.
-/

noncomputable section

open Cardinal Ideal MvPowerSeries Pointwise

/-!
## Helper lemmas for T conditions
-/

lemma conjI_ccf_zero (f : MvPowerSeries (Fin 3) ℂ)
    (hf : f ∈ conjI) : MvPowerSeries.constantCoeff f = 0 := by
  have hle : conjI ≤ RingHom.ker MvPowerSeries.constantCoeff := by
    apply Ideal.span_le.mpr
    simp_all
  exact RingHom.mem_ker.mp (hle hf)

lemma mk_mem_maxIdeal (f : MvPowerSeries (Fin 3) ℂ)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    Ideal.Quotient.mk conjI f ∈ IsLocalRing.maximalIdeal T := by
  rw [IsLocalRing.mem_maximalIdeal]
  intro ⟨u, hu⟩
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective u.inv
  have hmul : f * g - 1 ∈ conjI := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, map_mul, map_one]
    simp_all
  have h0 : MvPowerSeries.constantCoeff (f * g - 1) = 0 :=
    conjI_ccf_zero _ hmul
  simp_all

lemma coeff_conjI_zero_of_deg_le_one
    (m : Fin 3 →₀ ℕ)
    (hm : ∀ i, m i ≤ (Finsupp.single (1 : Fin 3) 1) i)
    (f : MvPowerSeries (Fin 3) ℂ) (hf : f ∈ conjI) :
    (coeff m) f = 0 := by
  rw [conjI, mem_span_singleton] at hf
  obtain ⟨h, rfl⟩ := hf
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_antidiagonal] at hab
  suffices hg : (coeff a) (X 0 ^ 2 - X 1 * X 2 : MvPowerSeries (Fin 3) ℂ) = 0 by
    simp [hg]
  have ha_le : ∀ i, a i ≤ (Finsupp.single (1 : Fin 3) 1) i := by
    intro i
    calc a i ≤ m i := by
          have := congr_arg (· i) hab
          simp at this ⊢
          omega
      _ ≤ _ := hm i
  simp only [map_sub, sub_eq_zero]
  have hX0sq : (coeff a) ((X 0 : MvPowerSeries (Fin 3) ℂ) ^ 2) = 0 := by
    rw [sq, coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨c, d⟩ hcd
    simp only [Finset.mem_antidiagonal] at hcd
    simp only [coeff_X]
    by_cases hc : c = Finsupp.single 0 1
    · simp only [hc, ite_true, one_mul, ite_eq_right_iff,
                  one_ne_zero, imp_false]
      intro hd
      have h0 := ha_le 0
      simp at h0
      have := congr_arg (· 0) hcd
      simp [hc, hd] at this
      omega
    · simp [hc]
  have hX1X2 : (coeff a) ((X 1 : MvPowerSeries (Fin 3) ℂ) * X 2) = 0 := by
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨c, d⟩ hcd
    simp only [Finset.mem_antidiagonal] at hcd
    simp only [coeff_X]
    by_cases hc : c = Finsupp.single 1 1
    · simp only [hc, ite_true, one_mul, ite_eq_right_iff, one_ne_zero, imp_false]
      intro hd
      have h2 := ha_le 2
      simp at h2
      have := congr_arg (· 2) hcd
      simp [hc, hd] at this
      omega
    · simp [hc]
  rw [hX0sq, hX1X2]

lemma mk_X1_ne_zero :
    (Ideal.Quotient.mk conjI (X 1) : T) ≠ 0 := by
  rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
  intro hf
  have h1 : (coeff (Finsupp.single 1 1 : Fin 3 →₀ ℕ)) (X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ)
      = 1 := by
    simp [coeff_X]
  have h2 := coeff_conjI_zero_of_deg_le_one _ (fun _ => le_refl _) _ hf
  simp_all

lemma T_smulRegular_of_ne_zero (a : T) (ha : a ≠ 0) :
    IsSMulRegular T a := by
  intro x y h
  simp_all

/-!
## Verify T conditions
-/

/-!
### Helper: z is a non-zerodivisor in T/(y)

We show that mk(X 2) is smul-regular on the quotient module T/(mk(X 1)·T).

**Proof idea**: Lift to MvPowerSeries (Fin 3) ℂ. If X₂f − X₁g ∈ conjI, then
f(a,0,c) = 0 for a < 2 (coefficient argument at the generator's degree).
Define shiftX1(f)(m) = f(m + single 1 1) (removes the X₁≥1 part) and
divR(f)(m) = f(m₀+2, 0, m₂) when m₁=0 (the X₀² quotient of the X₁=0 slice).
Then f − X₁·shiftX1(f) = X₀²·divR(f) (coefficient identity using the vanishing),
so f = X₁·(shiftX1(f) + X₂·divR(f)) + (X₀²−X₁X₂)·divR(f), giving
f ∈ (X₁) + conjI and hence mk(f) ∈ mk(X₁)·⊤.
-/

/-- Shift X₁-exponent by 1: (shiftX1 f)(m) = f(m + single 1 1). -/
def shiftX1'App (f : MvPowerSeries (Fin 3) ℂ) : MvPowerSeries (Fin 3) ℂ :=
  fun m => f (m + Finsupp.single 1 1)

/-- The "X₁=0 restriction divided by X₀²":
    (divR f)(m) = f(m₀+2, 0, m₂) when m₁=0, else 0. -/
def divR'App (f : MvPowerSeries (Fin 3) ℂ) : MvPowerSeries (Fin 3) ℂ :=
  fun m => if m 1 = 0 then f (Finsupp.update m 0 (m 0 + 2)) else 0

/-- LHS coefficient: (f - X₁ · shiftX1'App f)(d) = f(d) when d₁=0, else 0. -/
lemma coeff_lhs (f : MvPowerSeries (Fin 3) ℂ) (d : Fin 3 →₀ ℕ) :
    coeff d (f - X 1 * shiftX1'App f) = if d 1 = 0 then coeff d f else 0 := by
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
    change f d = shiftX1'App f (d - Finsupp.single 1 1)
    simp only [shiftX1'App]
    rw [tsub_add_cancel_of_le hle]
  · simp_all

/-- RHS coefficient: (X₀² · divR'App f)(d) = f(d) when d₀≥2 and d₁=0, else 0. -/
lemma coeff_rhs (f : MvPowerSeries (Fin 3) ℂ) (d : Fin 3 →₀ ℕ) :
    coeff d (X (0 : Fin 3) ^ 2 * divR'App f) =
      if 2 ≤ d 0 ∧ d 1 = 0 then coeff d f else 0 := by
  rw [show (X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 =
    MvPowerSeries.monomial (R := ℂ) (Finsupp.single 0 2) 1 from
    MvPowerSeries.X_pow_eq 0 2]
  rw [MvPowerSeries.coeff_monomial_mul]
  by_cases hle : Finsupp.single (0 : Fin 3) 2 ≤ d
  · have hd0 : 2 ≤ d 0 := by
      simp_all
    simp only [hle, ite_true, one_mul]
    by_cases hd1 : d 1 = 0
    · simp only [hd0, hd1, true_and, ite_true]
      change divR'App f (d - Finsupp.single 0 2) = f d
      unfold divR'App
      set d' := (d - Finsupp.single (0 : Fin 3) 2 : Fin 3 →₀ ℕ) with hd'_def
      have hsub1 : d' 1 = 0 := by
        simp [hd'_def, Finsupp.tsub_apply, hd1]
      simp only [hsub1, ite_true]
      congr 1
      ext i
      simp only [Finsupp.update_apply, hd'_def, Finsupp.tsub_apply, Finsupp.single_apply]
      fin_cases i <;> simp_all
    · simp only [hd1, and_false, ite_false]
      change divR'App f (d - Finsupp.single 0 2) = 0
      unfold divR'App
      simp_all
  · have hd0 : ¬ (2 ≤ d 0) := by
      simp_all
    simp [hle, hd0]

/-- Coefficient of the generator at a monomial with a₀ < 2 and a₁ = 0. -/
lemma coeff_gen_zero (a : Fin 3 →₀ ℕ) (ha0 : a 0 < 2) (ha1 : a 1 = 0) :
    coeff a (X (0 : Fin 3) ^ 2 - X 1 * X 2 : MvPowerSeries (Fin 3) ℂ) = 0 := by
  simp only [map_sub, sub_eq_zero]
  have hX0sq : coeff a ((X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2) = 0 := by
    rw [MvPowerSeries.coeff_X_pow]
    simp only [Fin.isValue, ite_eq_right_iff, one_ne_zero, imp_false]
    intro h
    simp_all
  have hX1X2 : coeff a ((X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ) * X 2) = 0 := by
    rw [show (X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
      MvPowerSeries.monomial (R := ℂ) (Finsupp.single 1 1) 1 from rfl]
    rw [MvPowerSeries.coeff_monomial_mul]
    simp_all
  rw [hX0sq, hX1X2]

/-- gen * k vanishes at d when d₀ < 2 and d₁ = 0. -/
lemma coeff_gen_mul_zero (k : MvPowerSeries (Fin 3) ℂ) (d : Fin 3 →₀ ℕ)
    (hd0 : d 0 < 2) (hd1 : d 1 = 0) :
    coeff d ((X (0 : Fin 3) ^ 2 - X 1 * X 2 : MvPowerSeries (Fin 3) ℂ) * k) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_antidiagonal] at hab
  have ha0 : a 0 < 2 := by
    have := congr_arg (· 0) hab
    simp at this
    omega
  have ha1 : a 1 = 0 := by
    have := congr_arg (· 1) hab
    simp at this
    omega
  simp [coeff_gen_zero a ha0 ha1]

/-- Vanishing of f at low X₀-degree when X₁-index is 0, derived from hmem. -/
lemma coeff_f_vanish (f g : MvPowerSeries (Fin 3) ℂ)
    (hmem : X 2 * f - X 1 * g ∈ conjI) (d : Fin 3 →₀ ℕ)
    (hd1 : d 1 = 0) (hd0 : d 0 < 2) : coeff d f = 0 := by
  rw [conjI, mem_span_singleton] at hmem
  obtain ⟨k, hk⟩ := hmem
  set e := d + Finsupp.single 2 1 with he_def
  have he0 : e 0 = d 0 := by simp [he_def, Finsupp.add_apply]
  have he1 : e 1 = 0 := by simp [he_def, Finsupp.add_apply, hd1]
  have hle2 : Finsupp.single (2 : Fin 3) 1 ≤ e := by
    simp_all
  have hnle1 : ¬ Finsupp.single (1 : Fin 3) 1 ≤ e := by
    simp_all
  have hlhs : coeff e (X 2 * f - X 1 * g) = coeff d f := by
    rw [map_sub]
    rw [show (X (2 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
      MvPowerSeries.monomial (R := ℂ) (Finsupp.single 2 1) 1 from rfl]
    rw [show (X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
      MvPowerSeries.monomial (R := ℂ) (Finsupp.single 1 1) 1 from rfl]
    rw [MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul]
    simp_all
  have hrhs : coeff e ((X (0 : Fin 3) ^ 2 - X 1 * X 2) * k) = 0 :=
    coeff_gen_mul_zero k e (he0 ▸ hd0) he1
  simp_all

/-- The coefficient identity: when X₂f − X₁g ∈ conjI, the "X₁=0 restriction" of f
    is divisible by X₀², yielding f − X₁·(shift) = X₀²·(quotient).
    The proof uses three facts:
    1. (f − X₁·shiftX1'App f)(d) = f(d) when d₁=0, 0 when d₁≥1
    2. (X₀²·divR'App f)(d) = f(d) when d₀≥2 and d₁=0, 0 otherwise
    3. f(d₀, 0, d₂) = 0 for d₀ < 2 (from the hypothesis, using coeff at d + single 2 1) -/
lemma rest_eq_X0sq_divR (f g : MvPowerSeries (Fin 3) ℂ)
    (hmem : X 2 * f - X 1 * g ∈ conjI) :
    f - X 1 * shiftX1'App f = (X (0 : Fin 3)) ^ 2 * divR'App f := by
  ext d
  rw [coeff_lhs, coeff_rhs]
  by_cases hd1 : d 1 = 0
  · rw [if_pos hd1]
    by_cases hd0 : 2 ≤ d 0
    · rw [if_pos ⟨hd0, hd1⟩]
    · rw [if_neg (fun h => hd0 h.1)]
      exact coeff_f_vanish f g hmem d hd1 (by omega)
  · rw [if_neg hd1, if_neg (fun h => hd1 h.2)]

lemma key_decomp'_app (f g : MvPowerSeries (Fin 3) ℂ)
    (hmem : X 2 * f - X 1 * g ∈ conjI) :
    f - X 1 * (shiftX1'App f + X 2 * divR'App f) ∈ conjI := by
  have h := rest_eq_X0sq_divR f g hmem
  have heq : f - X 1 * (shiftX1'App f + X 2 * divR'App f) =
    (X 0 ^ 2 - X 1 * X 2 : MvPowerSeries (Fin 3) ℂ) * divR'App f := by
    linear_combination h
  rw [heq, conjI, Ideal.mem_span_singleton]
  exact ⟨divR'App f, rfl⟩

/-- T has depth ≥ 2: there exists a regular sequence of length 2 in M.
Since T = ℂ[[x,y,z]]/(x²-yz) is Cohen-Macaulay of dimension 2,
the images of y and z form a regular sequence. -/
theorem T_depth_ge_two :
    ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b] := by
  refine ⟨Ideal.Quotient.mk conjI (X 1), Ideal.Quotient.mk conjI (X 2),
    mk_mem_maxIdeal _ (by simp [MvPowerSeries.constantCoeff_X]),
    mk_mem_maxIdeal _ (by simp [MvPowerSeries.constantCoeff_X]), ?_⟩
  apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
  · intro r hr
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl <;> exact mk_mem_maxIdeal _ (by simp [MvPowerSeries.constantCoeff_X])
  · rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
    refine ⟨T_smulRegular_of_ne_zero _ mk_X1_ne_zero, ?_⟩
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
    refine ⟨?_, ⟨fun i hi => by simp at hi⟩⟩
    -- z is regular on T/(y): if z*x = y*t, lift to power series and decompose
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
    intro x hx
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    obtain ⟨t, _, ht⟩ := hx
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective t
    have hmem : X 2 * f - X 1 * g ∈ conjI := by
      have : Ideal.Quotient.mk conjI (X 2 * f - X 1 * g) = 0 := by
        simp_all
      rwa [Ideal.Quotient.eq_zero_iff_mem] at this
    refine ⟨Ideal.Quotient.mk conjI (shiftX1'App f + X 2 * divR'App f), Submodule.mem_top, ?_⟩
    change Ideal.Quotient.mk conjI (X 1) *
      Ideal.Quotient.mk conjI (shiftX1'App f + X 2 * divR'App f) =
      Ideal.Quotient.mk conjI f
    rw [← map_mul, eq_comm, ← sub_eq_zero, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (key_decomp'_app f g hmem)

/-- |T| = |T/M|: both have cardinality |ℂ|.
T/M ≅ ℂ and |T| = |ℂ[[x,y,z]]/(x²-yz)| = |ℂ|. -/
theorem T_card_eq_residue_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T) :=
  T_card_eq.trans T_residueField_card.symm

/-- No integer is a zero divisor in T.
Since T is a domain of characteristic 0, and ℤ embeds into ℂ ⊆ T,
every nonzero integer maps to a nonzero (hence non-zerodivisor)
element. The key: algebraMap ℤ (MvPowerSeries (Fin 3) ℂ) n is a
unit (constantCoeff = (n : ℂ) ≠ 0), and units map to units under
the quotient map. -/
theorem T_no_integer_zerodivisor
    (n : ℤ) (hn : n ≠ 0) : (algebraMap ℤ T n) ≠ 0 := by
  change Ideal.Quotient.mk conjI
    (algebraMap ℤ (MvPowerSeries (Fin 3) ℂ) n) ≠ 0
  have hunit : IsUnit (algebraMap ℤ (MvPowerSeries (Fin 3) ℂ) n) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]
    simp_all
  exact (hunit.map (Ideal.Quotient.mk conjI)).ne_zero

/-- All primes P ≠ M in T have height ≤ 1.
Since ringKrullDim T = 2 and T is a local ring, height(M) = 2.
By strict monotonicity of height on primes, any P < M has height < 2. -/
theorem T_prime_height_le_one (P : Ideal T) [hP : P.IsPrime]
    (hne : P ≠ IsLocalRing.maximalIdeal T) : P.height ≤ 1 := by
  have hlt : P < IsLocalRing.maximalIdeal T :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime P) hne
  have hle : (↑P.height : WithBot ℕ∞) ≤ 2 :=
    T_ringKrullDim ▸ (ringKrullDim_le_iff_height_le _).mp le_rfl hP
  have hfin : P.FiniteHeight := by
    rw [Ideal.finiteHeight_iff]
    right
    intro htop
    rw [htop, WithBot.coe_top] at hle
    exact absurd (top_le_iff.mp hle) (by decide)
  have hstrict := Ideal.height_strict_mono_of_isPrime hlt
  have hmaxht : (IsLocalRing.maximalIdeal T).height = 2 := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := T)
    rw [T_ringKrullDim] at h
    rw [show (2 : WithBot ℕ∞) = ↑(2 : ℕ∞) from by norm_cast] at h
    exact WithBot.coe_injective h
  simp_all

/-!
## The main result

Apply jensen_construction_p0_uncountable to T to get A.
-/

/-- Jensen's Corollary 2.4 applied to T = ℂ[[x,y,z]]/(x²-yz):
There exists a 2-dimensional Noetherian local UFD A with Â ≅ T
and trivial generic formal fiber.

This directly proves jensen_special_case from Jensen.lean. -/
theorem jensen_special_case_proof :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A)
      (_ : IsDomain A) (_ : UniqueFactorizationMonoid A)
      (_ : IsNoetherianRing A),
      Nonempty (AdicCompletion
        (@IsLocalRing.maximalIdeal A _ _) A ≃+* T) ∧
      @HasTrivialGenericFormalFiber A _ _ := by
  have hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T := by
    rw [T_card_eq, Cardinal.mk_complex]
    exact Cardinal.aleph0_lt_continuum
  exact @jensen_construction_p0_uncountable T _ _ _ _ T_isAdicComplete
    T_depth_ge_two T_card_eq_residue_card
    (fun n hn => by
      convert T_no_integer_zerodivisor n hn using 1
      simp_all)
    hT_aleph0
    (fun P hP hne => @T_prime_height_le_one P hP hne)

end
