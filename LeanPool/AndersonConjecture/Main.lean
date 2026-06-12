/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.Jensen
import LeanPool.AndersonConjecture.QuasiCompleteRing.QuasiCompleteRing

/-!
# Main Theorem: WQC Does Not Imply QC

There exists a Noetherian local UFD that is weakly quasi-complete
but not quasi-complete. The ring is obtained via Jensen--Heitmann
with completion T = ℂ[[x,y,z]]/(x²-yz)
Anderson's theorems
reduce the problem to a quotient that fails weak quasi-completeness.
-/

noncomputable section

/-
## Step 1: A is weakly quasi-complete

The generic formal fiber of A is trivial (from jensen_special_case),
meaning every nonzero prime of  = T meets A nontrivially.
By Anderson Cor 2 Part 1 (= Farley Prop 1), A is WQC.
-/

/-- The ring A from jensen_special_case is weakly quasi-complete.
Uses: trivial generic formal fiber + isWeaklyQuasiComplete_iff_primes_meet. -/
theorem a_isWeaklyQuasiComplete
    (A : Type*) [CommRing A] [IsLocalRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [IsNoetherianRing A]
    (_hiso : Nonempty (AdicCompletion (IsLocalRing.maximalIdeal A) A ≃+* T))
    (htrivial : HasTrivialGenericFormalFiber A) :
    IsWeaklyQuasiComplete A := by
  rw [isWeaklyQuasiComplete_iff_primes_meet]
  intro P hP hPne h_comap_bot
  exact hPne (htrivial P hP h_comap_bot)

/-
## Step 2: There exists a prime a ∈ A such that A/aA is not WQC

Key steps:
- Q ∩ A ≠ 0 (trivial fiber + Q ≠ 0)
- ht(Q ∩ A) = 1 (faithful flatness)
- Q ∩ A = (a) for prime a (A is UFD)
- aT ⊆ Q but aT ≠ Q (Q not principal), so aT not prime
- T/aT not a domain → Â/aÂ not a domain → A/aA not analytically irred.
- dim(A/aA) = 1, so not analytically irred. → not WQC (Anderson Cor 2 Part 3)
-/

/-- X₀ is not in conjI = (x²-yz): coefficient at degree-1 monomial x is 1 for X₀
    but 0 for any multiple of x²-yz (which has minimum degree 2). -/
lemma X0_not_mem_conjI :
    (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ∉ conjI := by
  open MvPowerSeries in
  rw [conjI, Ideal.mem_span_singleton]
  intro ⟨f, hf⟩
  have h1 := MvPowerSeries.coeff_index_single_self_X (R := ℂ) (0 : Fin 3)
  have h2 := congr_arg (MvPowerSeries.coeff (σ := Fin 3) (R := ℂ) (Finsupp.single 0 1)) hf
  rw [h1] at h2
  rw [sub_mul, map_sub,
      show (X (0 : Fin 3) : MvPowerSeries (Fin 3) ℂ) ^ 2 =
        monomial (Finsupp.single 0 2) 1 from X_pow_eq 0 2,
      coeff_monomial_mul] at h2
  have hle1 : ¬ (Finsupp.single (0 : Fin 3) 2 ≤ Finsupp.single (0 : Fin 3) 1) := by
    simp only [Fin.isValue, Finsupp.single_le_iff, Finsupp.single_eq_same,
      Nat.not_ofNat_le_one, not_false_eq_true]
  rw [if_neg hle1, zero_sub, mul_assoc,
      show (X (1 : Fin 3) : MvPowerSeries (Fin 3) ℂ) =
        monomial (Finsupp.single 1 1) 1 from rfl,
      coeff_monomial_mul] at h2
  have hle2 : ¬ (Finsupp.single (1 : Fin 3) 1 ≤ Finsupp.single (0 : Fin 3) 1) := by
    intro h
    have := h (1 : Fin 3)
    simp only [Fin.isValue, Finsupp.single_eq_same, ne_eq, one_ne_zero, not_false_eq_true,
      Finsupp.single_eq_of_ne, nonpos_iff_eq_zero] at this
  rw [if_neg hle2, neg_zero] at h2
  exact one_ne_zero h2

/-- Q is not the zero ideal of T. (xbar ≠ 0 since X₀ ∉ conjI.) -/
lemma Q_ne_bot : Q ≠ ⊥ := by
  intro h
  have : Ideal.Quotient.mk conjI (MvPowerSeries.X 0) = 0 := by
    have hmem : Ideal.Quotient.mk conjI (MvPowerSeries.X 0) ∈ Q :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h] at hmem
    exact Ideal.mem_bot.mp hmem
  rw [Ideal.Quotient.eq_zero_iff_mem] at this
  exact X0_not_mem_conjI this

/-- Comap of a nonzero ideal under a ring isomorphism is nonzero. -/
lemma comap_ringEquiv_ne_bot {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) {I : Ideal S} (hI : I ≠ ⊥) :
    Ideal.comap e.toRingHom I ≠ ⊥ := by
  intro h
  apply hI
  have h1 := Ideal.map_comap_of_surjective e.toRingHom e.surjective I
  rw [h, Ideal.map_bot] at h1
  exact h1.symm

/-- The contraction of Q through the completion isomorphism has height 1.
    Uses faithful flatness of adic completion: 1 ≤ ht(q) ≤ ht(Q') = ht(Q) = 1. -/
lemma contraction_height_one
    (A : Type*) [CommRing A] [IsLocalRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [IsNoetherianRing A]
    (φ : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃+* T)
    (q : Ideal A) (hq_ne : q ≠ ⊥) (hq_prime : q.IsPrime)
    (hq_eq : q = Ideal.comap (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
                    (Ideal.comap φ.toRingHom Q)) :
    q.height = 1 := by
  set Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  set Q' := Ideal.comap φ.toRingHom Q
  haveI : IsNoetherianRing Ahat := isNoetherianRing_of_ringEquiv T φ.symm
  haveI : Module.Flat A Ahat := AdicCompletion.flat_of_isNoetherian _
  haveI : Algebra.HasGoingDown A Ahat := Algebra.HasGoingDown.of_flat
  haveI : Q.IsPrime := Q_isPrime
  haveI : Q'.IsPrime := Ideal.comap_isPrime φ.toRingHom Q
  haveI : Q'.LiesOver q := ⟨hq_eq⟩
  have hQ'_height : Q'.height = (1 : ℕ∞) := by
    rw [show Q' = Ideal.comap φ Q from rfl,
        RingEquiv.height_comap φ Q, Q_height_one]
  have h_upper : q.height ≤ 1 :=
    calc q.height
        ≤ q.height + (Ideal.map (Ideal.Quotient.mk
            (Ideal.map (algebraMap A Ahat) q)) Q').height := le_self_add
      _ = Q'.height :=
          (Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q').symm
      _ = 1 := hQ'_height
  have h_lower : 1 ≤ q.height := by
    haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
    have h := Ideal.height_add_one_le_of_lt_of_isPrime
      (bot_lt_iff_ne_bot.mpr hq_ne)
    rwa [show (⊥ : Ideal A).height = 0 from by
      rw [Ideal.height_eq_zero_iff,
          IsDomain.minimalPrimes_eq_singleton_bot]
      exact Set.mem_singleton _, zero_add] at h
  exact le_antisymm h_upper h_lower

/-- In a UFD, a prime ideal of height 1 is principal, generated by a prime element. -/
lemma ufd_height_one_principal
    {A : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]
    (q : Ideal A) (hq_prime : q.IsPrime) (hq_height : q.height = 1) :
    ∃ a : A, Prime a ∧ q = Ideal.span {a} := by
  have hq_ne : q ≠ ⊥ := by
    intro h
    rw [h] at hq_height
    simp only [Ideal.height_bot, zero_ne_one] at hq_height
  obtain ⟨a, ha_mem, ha_prime⟩ := hq_prime.exists_mem_prime_of_ne_bot hq_ne
  haveI : (Ideal.span {a}).IsPrime :=
    (Ideal.span_singleton_prime ha_prime.ne_zero).mpr ha_prime
  have h_le : Ideal.span {a} ≤ q := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha_mem)
  refine ⟨a, ha_prime, le_antisymm ?_ h_le⟩
  by_contra h_not_le
  have h_lt : Ideal.span {a} < q :=
    lt_of_le_of_ne h_le (fun h => h_not_le (le_of_eq h.symm))
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h_lt
  rw [hq_height] at h1
  haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  have h_bot_lt : (⊥ : Ideal A) < Ideal.span {a} :=
    bot_lt_iff_ne_bot.mpr (Ideal.span_singleton_eq_bot.not.mpr ha_prime.ne_zero)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime h_bot_lt
  have h3 : (⊥ : Ideal A).height = 0 := by
    rw [Ideal.height_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.mem_singleton _
  rw [h3] at h2
  have h4 : (1 : ℕ∞) ≤ (Ideal.span {a}).height := by simpa using h2
  exact absurd (le_trans (add_le_add_right h4 1 |>.trans_eq (add_comm _ _)) h1)
    (by norm_num : ¬((2 : ℕ∞) ≤ 1))

/-- dim(A) ≤ dim(Â) for Noetherian local rings via flat going-down.
    Proof: algebraMap A Â is a local ring hom (via evalOneₐ), so maximalIdeal Â lies over
    maximalIdeal A, then height_eq_height_add gives ht(M_A) ≤ ht(M_Â) = dim(Â). -/
lemma ringKrullDim_le_of_adic_completion
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    (φ : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃+* T) :
    ringKrullDim A ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  set M := IsLocalRing.maximalIdeal A
  set Ahat := AdicCompletion M A
  haveI : IsLocalRing Ahat := φ.symm.isLocalRing
  -- algebraMap A Ahat is local: r ∈ M → evalOneₐ(algebraMap r) = 0 → not a unit
  haveI : IsLocalHom (algebraMap A Ahat) := by
    constructor
    intro r hr
    by_contra h_not_unit
    have hr_mem : r ∈ M := (IsLocalRing.mem_maximalIdeal r).mpr h_not_unit
    have h_mk_zero : (Ideal.Quotient.mk M) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr_mem
    have h_eval_zero : (AdicCompletion.evalOneₐ M) (algebraMap A Ahat r) = 0 := by
      rw [show algebraMap A Ahat r = AdicCompletion.of M A r from by
        rw [AdicCompletion.algebraMap_apply]
        rfl]
      rw [AdicCompletion.evalOneₐ_of, h_mk_zero]
    have h_unit := hr.map (AdicCompletion.evalOneₐ M).toRingHom
    rw [AlgHom.toRingHom_eq_coe, show (AdicCompletion.evalOneₐ M : Ahat →+* _)
      (algebraMap A Ahat r) = (0 : A ⧸ M) from h_eval_zero] at h_unit
    exact not_isUnit_zero h_unit
  haveI : IsNoetherianRing Ahat := isNoetherianRing_of_ringEquiv T φ.symm
  haveI : Module.Flat A Ahat := AdicCompletion.flat_of_isNoetherian _
  haveI : Algebra.HasGoingDown A Ahat := Algebra.HasGoingDown.of_flat
  haveI : (IsLocalRing.maximalIdeal Ahat).LiesOver M :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  -- Going-down gives ht(M_A) ≤ ht(M_Â)
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
      ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := Ahat)]
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown M
    (IsLocalRing.maximalIdeal Ahat)
  simp only [h, WithBot.coe_le_coe]
  exact le_self_add

lemma smul_top_eq_bot_quotient {A : Type*} [CommRing A] [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A) •
      (⊤ : Submodule A (A ⧸ IsLocalRing.maximalIdeal A)) = ⊥ := by
  simp only [Ideal.smul_top_eq_map, Ideal.Quotient.algebraMap_eq, Ideal.map_quotient_self,
    Submodule.restrictScalars_bot]

lemma pow_smul_top_eq_bot_quotient {A : Type*} [CommRing A] [IsLocalRing A]
    (n : ℕ) (hn : n ≠ 0) :
    (IsLocalRing.maximalIdeal A) ^ n •
      (⊤ : Submodule A (A ⧸ IsLocalRing.maximalIdeal A)) = ⊥ := by
  exact le_antisymm ((Submodule.smul_mono_left (Ideal.pow_le_self hn)).trans
    (le_of_eq smul_top_eq_bot_quotient)) bot_le

lemma smul_top_eq_self {A : Type*} [CommRing A] [IsLocalRing A] :
    (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A A) =
      (IsLocalRing.maximalIdeal A : Submodule A A) := by
    simp only [smul_eq_mul, Ideal.mul_top]

/-- A/M is M-adic Hausdorff (M kills A/M, so the filtration is trivially zero). -/
instance residueField_isHausdorff (A : Type*) [CommRing A] [IsLocalRing A] :
    IsHausdorff (IsLocalRing.maximalIdeal A) (A ⧸ IsLocalRing.maximalIdeal A) where
  haus' x hx := by
    have h1 := hx 1
    rw [pow_one, smul_top_eq_bot_quotient] at h1
    rwa [SModEq.bot] at h1

/-- A/M is M-adic precomplete (the adic topology is discrete). -/
instance residueField_isPrecomplete (A : Type*) [CommRing A] [IsLocalRing A] :
    IsPrecomplete (IsLocalRing.maximalIdeal A) (A ⧸ IsLocalRing.maximalIdeal A) where
  prec' f hf := by
    use f 1
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
      exact SModEq.top
    · rw [pow_smul_top_eq_bot_quotient n hn]
      have h1 := hf (Nat.one_le_iff_ne_zero.mpr hn)
      rw [pow_one, smul_top_eq_bot_quotient] at h1
      rw [SModEq.bot] at h1
      rw [← h1]

/-- map mkQ (mk a) = of (evalOneₐ (mk a)) — component-wise comparison. -/
lemma map_mkQ_mk_eq_of_evalOneₐ {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A]
    (a : AdicCompletion.AdicCauchySequence (IsLocalRing.maximalIdeal A) A) :
    AdicCompletion.map (IsLocalRing.maximalIdeal A)
        ((IsLocalRing.maximalIdeal A : Submodule A A).mkQ)
      (AdicCompletion.mk _ A a) =
    AdicCompletion.of (IsLocalRing.maximalIdeal A) (A ⧸ IsLocalRing.maximalIdeal A)
      (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A)
        (AdicCompletion.mk _ A a)) := by
  apply AdicCompletion.ext
  intro n
  simp only [AdicCompletion.map_val_apply, AdicCompletion.mk_apply_coe,
    AdicCompletion.of_apply, LinearMap.reduceModIdeal_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  by_cases hn : n = 0
  · subst hn
    simp only [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    exact Submodule.mem_top
  · rw [pow_smul_top_eq_bot_quotient n hn, Submodule.mem_bot, sub_eq_zero]
    simp only [AdicCompletion.evalOneₐ, AlgHom.coe_comp, Function.comp_apply,
      AdicCompletion.evalₐ_mk, Ideal.Quotient.factorₐ_apply_mk]
    have hcauchy := a.property (show 1 ≤ n from Nat.one_le_iff_ne_zero.mpr hn)
    rw [pow_one, smul_top_eq_self] at hcauchy
    exact hcauchy.symm

/-- map mkQ x = 0 ↔ evalOneₐ x = 0 — kernel equivalence. -/
lemma map_mkQ_eq_zero_iff_evalOneₐ {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (x : AdicCompletion (IsLocalRing.maximalIdeal A) A) :
    AdicCompletion.map (IsLocalRing.maximalIdeal A)
        ((IsLocalRing.maximalIdeal A : Submodule A A).mkQ) x = 0 ↔
    AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A) x = 0 := by
  apply AdicCompletion.induction_on _ A x (fun a => ?_)
  constructor
  · intro hx
    rw [map_mkQ_mk_eq_of_evalOneₐ] at hx
    exact AdicCompletion.of_injective _ _ hx
  · intro hx
    rw [map_mkQ_mk_eq_of_evalOneₐ, hx, map_zero]

/-- range(map subtype) ⊆ Ideal.map algebraMap M — via tensor product description. -/
lemma range_map_subtype_le_ideal_map {A : Type u_1} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] :
    LinearMap.range (AdicCompletion.map (IsLocalRing.maximalIdeal A)
      ((IsLocalRing.maximalIdeal A : Submodule A A).subtype)) ≤
    (Ideal.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
      (IsLocalRing.maximalIdeal A) : Ideal _) := by
  intro x hx
  rw [LinearMap.mem_range] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨t, rfl⟩ :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
      (IsLocalRing.maximalIdeal A)
      (↥(IsLocalRing.maximalIdeal A : Submodule A A))).surjective z
  change (AdicCompletion.map _ (Submodule.subtype _))
    ((AdicCompletion.ofTensorProduct _ _) t) ∈ _
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mem]
  | tmul a m =>
    simp only [AdicCompletion.ofTensorProduct_tmul, map_smul, AdicCompletion.map_of]
    exact Ideal.mul_mem_left _ a (Ideal.mem_map_of_mem _ m.property)
  | add x y hx hy => simp only [map_add]
                     exact Ideal.add_mem _ hx hy

/-- ker(evalOneₐ M) = Ideal.map (algebraMap A Â) M for Noetherian local rings.
    Uses: exact sequence of completions + tensor product description + of_bijective. -/
lemma ker_evalOneₐ_eq_map_maximalIdeal
    {A : Type u_1} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    RingHom.ker (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A)) =
    Ideal.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
      (IsLocalRing.maximalIdeal A) := by
  apply le_antisymm
  · -- ker(evalOneₐ) ≤ Ideal.map algebraMap M
    intro x hx
    rw [RingHom.mem_ker] at hx
    have hmkQ : AdicCompletion.map _ ((IsLocalRing.maximalIdeal A : Submodule A A).mkQ) x = 0 :=
      (map_mkQ_eq_zero_iff_evalOneₐ x).mpr hx
    have hexact : Function.Exact
        (AdicCompletion.map (IsLocalRing.maximalIdeal A)
          ((IsLocalRing.maximalIdeal A : Submodule A A).subtype))
        (AdicCompletion.map (IsLocalRing.maximalIdeal A)
          ((IsLocalRing.maximalIdeal A : Submodule A A).mkQ)) :=
      @AdicCompletion.map_exact A _ (IsLocalRing.maximalIdeal A)
        (↥(IsLocalRing.maximalIdeal A : Submodule A A)) _ _ A _ _
        (A ⧸ (IsLocalRing.maximalIdeal A : Submodule A A)) _ _ _ _
        _ _ Subtype.val_injective
        (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
    rw [Function.Exact] at hexact
    have hrange : x ∈ LinearMap.range
        (AdicCompletion.map (IsLocalRing.maximalIdeal A)
          ((IsLocalRing.maximalIdeal A : Submodule A A).subtype)) := by
      rw [LinearMap.mem_range]
      exact (hexact x).mp hmkQ
    exact range_map_subtype_le_ideal_map hrange
  · rw [Ideal.map, Ideal.span_le]
    rintro x ⟨m, hm, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.commutes,
      Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hm

/-- Ideal.map (algebraMap A Â) M = maxIdeal Â for Noetherian local rings. -/
lemma map_maximalIdeal_eq {A : Type u_1} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A]
    [IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)] :
    Ideal.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
      (IsLocalRing.maximalIdeal A) =
    IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal A) A) := by
  rw [← ker_evalOneₐ_eq_map_maximalIdeal]
  letI : Field (A ⧸ IsLocalRing.maximalIdeal A) := Ideal.Quotient.field _
  exact IsLocalRing.ker_eq_maximalIdeal
    (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A)).toRingHom
    (AdicCompletion.evalOneₐ_surjective _)

/-- M^k kills A/I for k ≥ n when I = M^n: M^k • (A/M^n) = 0. -/
lemma pow_smul_top_eq_bot_quotient_pow {A : Type*} [CommRing A]
    (M : Ideal A) (n k : ℕ) (hk : n ≤ k) :
    M ^ k • (⊤ : Submodule A (A ⧸ M ^ n)) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine Submodule.smul_induction_on hx (fun r hr x _ => ?_) (fun x y hx hy => ?_)
  · induction x using Quotient.inductionOn' with | h a =>
    change r • Ideal.Quotient.mk (M ^ n) a = 0
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
    exact M.pow_le_pow_right hk (Ideal.mul_mem_right a _ hr)
  · rw [hx, hy, add_zero]

/-- evalₐ M n z = 0 implies map M (mkQ (M^n)) z = 0.
    Component-wise: each component of (map mkQ z) in (A/M^n)/(M^k•(A/M^n)) is 0. -/
lemma evalₐ_zero_imp_map_mkQ_pow_zero {A : Type*} [CommRing A]
    [IsNoetherianRing A] (M : Ideal A) (n : ℕ)
    (z : AdicCompletion M A)
    (hz : (AdicCompletion.evalₐ M n) z = 0) :
    AdicCompletion.map M ((M ^ n : Submodule A A).mkQ) z = 0 := by
  obtain ⟨seq, rfl⟩ := AdicCompletion.mk_surjective M A z
  rw [AdicCompletion.evalₐ_mk] at hz
  have hseqn : seq.val n ∈ (M ^ n : Ideal A) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  apply AdicCompletion.ext
  intro k
  simp only [AdicCompletion.map_val_apply, AdicCompletion.mk_apply_coe,
    LinearMap.reduceModIdeal_apply, Submodule.mkQ_apply, AdicCompletion.val_zero, Pi.zero_apply]
  by_cases hk : n ≤ k
  · have hcauchy_kn := SModEq.sub_mem.mp (seq.property hk)
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at hcauchy_kn
    have hseqk_mem : seq.val k ∈ (M ^ n : Ideal A) := by
      have : seq.val k = seq.val n - (seq.val n - seq.val k) := by ring
      rw [this]
      exact (M ^ n).sub_mem hseqn hcauchy_kn
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hseqk_mem]
  · -- k < n: seq.val k ∈ M^k via Cauchy condition and M^n ⊆ M^k
    push Not at hk
    have hkn : k ≤ n := Nat.le_of_lt hk
    have hcauchy := SModEq.sub_mem.mp (seq.property hkn)
    rw [Ideal.smul_eq_mul, Ideal.mul_top] at hcauchy
    have hseqk_mem : seq.val k ∈ (M ^ k : Ideal A) := by
      have h1 : seq.val n ∈ (M ^ k : Ideal A) :=
        Ideal.pow_le_pow_right hkn hseqn
      have : seq.val k = seq.val n + (seq.val k - seq.val n) := by ring
      rw [this]
      exact (M ^ k).add_mem h1 hcauchy
    rw [Submodule.Quotient.mk_eq_zero]
    rw [show Submodule.Quotient.mk (seq.val k) =
      seq.val k • (1 : A ⧸ (M ^ n : Submodule A A)) from by simp [Algebra.smul_def]]
    exact Submodule.smul_mem_smul hseqk_mem Submodule.mem_top

/-- range(map M (subtype (M^n))) ⊆ Ideal.map algebraMap (M^n). -/
lemma range_map_subtype_pow_le {A : Type u_1} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (n : ℕ) :
    LinearMap.range (AdicCompletion.map (IsLocalRing.maximalIdeal A)
      ((IsLocalRing.maximalIdeal A ^ n : Submodule A A).subtype)) ≤
    (Ideal.map (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
      (IsLocalRing.maximalIdeal A ^ n) : Ideal _) := by
  set M := IsLocalRing.maximalIdeal A
  intro x hx
  rw [LinearMap.mem_range] at hx
  obtain ⟨z, rfl⟩ := hx
  obtain ⟨t, rfl⟩ :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian M
      (↥(M ^ n : Submodule A A))).surjective z
  change (AdicCompletion.map _ (Submodule.subtype _))
    ((AdicCompletion.ofTensorProduct _ _) t) ∈ _
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero, zero_mem]
  | tmul a m =>
    simp only [AdicCompletion.ofTensorProduct_tmul, map_smul, AdicCompletion.map_of]
    exact Ideal.mul_mem_left _ a (Ideal.mem_map_of_mem _ m.property)
  | add x y hx hy => simp only [map_add]
                     exact Ideal.add_mem _ hx hy

/-- ker(evalₐ M n) ⊆ maximalIdeal(Â)^n for Noetherian local rings. -/
lemma ker_evalₐ_le_maximalIdeal_pow
    {A : Type u_1} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal A) A)]
    (n : ℕ) (z : AdicCompletion (IsLocalRing.maximalIdeal A) A)
    (hz : (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A) n) z = 0) :
    z ∈ IsLocalRing.maximalIdeal
      (AdicCompletion (IsLocalRing.maximalIdeal A) A) ^ n := by
  let M := IsLocalRing.maximalIdeal A
  let Ahat := AdicCompletion M A
  let Mhat := IsLocalRing.maximalIdeal Ahat
  have h_map_zero : AdicCompletion.map M ((M ^ n : Submodule A A).mkQ) z = 0 :=
    evalₐ_zero_imp_map_mkQ_pow_zero M n z hz
  -- By exact sequence, z ∈ range(map subtype (M^n))
  have hexact : Function.Exact
      (AdicCompletion.map M (M ^ n : Submodule A A).subtype)
      (AdicCompletion.map M (M ^ n : Submodule A A).mkQ) :=
    @AdicCompletion.map_exact A _ M
      (↥(M ^ n : Submodule A A)) _ _ A _ _
      (A ⧸ (M ^ n : Submodule A A)) _ _ _ _
      _ _ Subtype.val_injective
      (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _)
  rw [Function.Exact] at hexact
  have hrange : z ∈ LinearMap.range
      (AdicCompletion.map M (M ^ n : Submodule A A).subtype) := by
    rw [LinearMap.mem_range]
    exact (hexact z).mp h_map_zero
  have hle := @range_map_subtype_pow_le A _ _ _ n
  have h_map_eq : Ideal.map (algebraMap A Ahat) (M ^ n) = Mhat ^ n := by
    rw [Ideal.map_pow]
    exact congrArg (· ^ n) map_maximalIdeal_eq
  rw [h_map_eq] at hle
  exact hle hrange

/-- The quotient A/(a) has Krull dimension 1.
    Since A is a 2-dimensional UFD and a is prime, dim(A/(a)) = dim(A) - 1 = 1.
    Uses: dim(Â) = dim(A) via faithful flatness, and dim(T) = 2. -/
lemma quotient_prime_dim_one
    {A : Type*} [CommRing A] [IsLocalRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [IsNoetherianRing A]
    (hiso : Nonempty (AdicCompletion (IsLocalRing.maximalIdeal A) A ≃+* T))
    (a : A) (ha : Prime a) :
    letI : (Ideal.span {a}).IsPrime :=
      (Ideal.span_singleton_prime ha.ne_zero).mpr ha
    letI : Nontrivial (A ⧸ Ideal.span {a}) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top ha.not_unit)
    letI : IsLocalRing (A ⧸ Ideal.span {a}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    ringKrullDim (A ⧸ Ideal.span {a}) = 1 := by
  obtain ⟨φ⟩ := hiso
  set Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  haveI : IsNoetherianRing Ahat := isNoetherianRing_of_ringEquiv T φ.symm
  have hdim_Ahat : ringKrullDim Ahat = 2 :=
    ringKrullDim_eq_of_ringEquiv φ ▸ T_ringKrullDim
  have hdim_A_le : ringKrullDim A ≤ 2 :=
    (ringKrullDim_le_of_adic_completion φ).trans hdim_Ahat.le
  have h_eq := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (IsSMulRegular.of_ne_zero ha.ne_zero)
    ((IsLocalRing.mem_maximalIdeal a).mpr ha.not_unit)
  -- dim(A) = 2: going-down + fiber_height = 0 (since Ideal.map algebraMap M = maxIdeal Â)
  have hdim_A : ringKrullDim A = 2 := le_antisymm hdim_A_le (by
    set M := IsLocalRing.maximalIdeal A
    haveI : IsLocalRing Ahat := φ.symm.isLocalRing
    haveI : IsLocalHom (algebraMap A Ahat) := by
      constructor
      intro r hr
      by_contra h_not_unit
      have hr_mem : r ∈ M := (IsLocalRing.mem_maximalIdeal r).mpr h_not_unit
      have h_mk_zero : (Ideal.Quotient.mk M) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr_mem
      have h_eval_zero : (AdicCompletion.evalOneₐ M) (algebraMap A Ahat r) = 0 := by
        rw [show algebraMap A Ahat r = AdicCompletion.of M A r from by
          rw [AdicCompletion.algebraMap_apply]
          rfl]
        rw [AdicCompletion.evalOneₐ_of, h_mk_zero]
      have h_unit := hr.map (AdicCompletion.evalOneₐ M).toRingHom
      rw [AlgHom.toRingHom_eq_coe, show (AdicCompletion.evalOneₐ M : Ahat →+* _)
        (algebraMap A Ahat r) = (0 : A ⧸ M) from h_eval_zero] at h_unit
      exact not_isUnit_zero h_unit
    haveI : Module.Flat A Ahat := AdicCompletion.flat_of_isNoetherian _
    haveI : Algebra.HasGoingDown A Ahat := Algebra.HasGoingDown.of_flat
    haveI : (IsLocalRing.maximalIdeal Ahat).LiesOver M :=
      IsLocalRing.ResidueField.instLiesOverMaximalIdeal
    have h_gd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown M
      (IsLocalRing.maximalIdeal Ahat)
    have h_map_eq : Ideal.map (algebraMap A Ahat) M = IsLocalRing.maximalIdeal Ahat :=
      map_maximalIdeal_eq
    -- Fiber is trivial since M·Â = M_Â, so ht(M_A) = ht(M_Â) = dim(Â)
    have h_fiber_bot : Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A Ahat) M))
        (IsLocalRing.maximalIdeal Ahat) = ⊥ := by
      rw [h_map_eq, Ideal.map_quotient_self]
    haveI : Nontrivial (Ahat ⧸ Ideal.map (algebraMap A Ahat) M) := by
      rw [h_map_eq]
      exact Ideal.Quotient.nontrivial_iff.mpr (IsLocalRing.maximalIdeal.isMaximal Ahat).ne_top
    have h_fiber_height : (Ideal.map (Ideal.Quotient.mk (Ideal.map (algebraMap A Ahat) M))
        (IsLocalRing.maximalIdeal Ahat)).height = 0 := by
      rw [h_fiber_bot, Ideal.height_bot]
    rw [h_fiber_height, add_zero] at h_gd
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := Ahat)] at hdim_Ahat
    rw [show (↑(IsLocalRing.maximalIdeal A).height : WithBot ℕ∞) =
      ↑(IsLocalRing.maximalIdeal Ahat).height from congrArg _ h_gd.symm]
    exact hdim_Ahat.ge)
  rw [hdim_A] at h_eq
  have hne : ringKrullDim (A ⧸ Ideal.span {a}) ≠ ⊥ := by
    intro h
    rw [h] at h_eq
    simp only [WithBot.bot_add, WithBot.bot_ne_ofNat] at h_eq
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp hne
  have hne2 : n ≠ ⊤ := by
    intro hnt
    rw [← hn, hnt] at h_eq
    have h1 : (↑(⊤ : ℕ∞) : WithBot ℕ∞) + ↑(1 : ℕ∞) = ↑(2 : ℕ∞) := h_eq
    rw [← WithBot.coe_add] at h1
    exact absurd (WithBot.coe_injective h1) (by decide)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne2
  rw [← hk] at hn
  rw [← hn] at h_eq ⊢
  have h1 : (↑(↑k : ℕ∞) : WithBot ℕ∞) + ↑(1 : ℕ∞) = ↑(2 : ℕ∞) := h_eq
  rw [← WithBot.coe_add] at h1
  have h2 := WithBot.coe_injective h1
  norm_cast at h2 ⊢
  omega

/-- If `b ∈ Q` is nonzero, then `span {b}` is not prime: `span{b} ≤ Q` and `ht Q = 1`,
so if `span{b}` were prime it would equal `Q` (chain `⊥ < span{b} < Q` is too long),
contradicting that `Q` is not principal. -/
lemma span_singleton_not_isPrime_of_mem_Q {b : T} (hb_ne : b ≠ 0) (hb_mem : b ∈ Q) :
    ¬ (Ideal.span ({b} : Set T)).IsPrime := by
  haveI : IsDomain T := T_isDomain
  haveI : Q.IsPrime := Q_isPrime
  intro hprime
  have hne_bot : Ideal.span ({b} : Set T) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr hb_ne
  have hle : Ideal.span ({b} : Set T) ≤ Q :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hb_mem)
  by_cases heq : Ideal.span ({b} : Set T) = Q
  · exact Q_not_isPrincipal ⟨⟨b, heq.symm⟩⟩
  · have hlt : Ideal.span ({b} : Set T) < Q :=
      lt_of_le_of_ne hle heq
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have hQh : Q.height = 1 := Q_height_one
    rw [hQh] at h1
    haveI : (⊥ : Ideal T).IsPrime := Ideal.isPrime_bot
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime
      (bot_lt_iff_ne_bot.mpr hne_bot)
    have h3 : (⊥ : Ideal T).height = 0 := by
      rw [Ideal.height_eq_zero_iff,
          IsDomain.minimalPrimes_eq_singleton_bot]
      exact Set.mem_singleton _
    rw [h3, zero_add] at h2
    exact absurd (le_trans (add_le_add_right h2 1
      |>.trans_eq (add_comm _ _)) h1)
      (by norm_num : ¬((2 : ℕ∞) ≤ 1))

/-- The quotient A/(a) is not analytically irreducible.
    Key argument: b = φ(algebraMap a) ∈ Q, so span{b} ≤ Q. Since Q is not principal,
    span{b} ≠ Q. Since ht(Q) = 1, span{b} is not prime, so T/bT is not a domain.
    Since completion commutes with quotient: completion(A/(a)) ≅ T/bT, done. -/
lemma quotient_not_analytically_irreducible
    (A : Type*) [CommRing A] [IsLocalRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [IsNoetherianRing A]
    (φ : AdicCompletion (IsLocalRing.maximalIdeal A) A ≃+* T)
    (a : A) (ha : Prime a)
    (hq_eq : Ideal.span {a} = Ideal.comap
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))
        (Ideal.comap φ.toRingHom Q)) :
    letI : (Ideal.span {a}).IsPrime :=
      (Ideal.span_singleton_prime ha.ne_zero).mpr ha
    letI : Nontrivial (A ⧸ Ideal.span {a}) :=
      Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top ha.not_unit)
    letI : IsLocalRing (A ⧸ Ideal.span {a}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    ¬ IsAnalyticallyIrreducible (A ⧸ Ideal.span {a}) := by
  -- Use let (not set) for M to avoid φ/φ✝ renaming conflict
  let M : Ideal A := IsLocalRing.maximalIdeal A
  let Ahat : Type _ := AdicCompletion M A
  set b := φ (algebraMap A Ahat a) with hb_def
  haveI : IsDomain T := T_isDomain
  haveI : Q.IsPrime := Q_isPrime
  have hb_mem : b ∈ Q := by
    have : a ∈ Ideal.span {a} := Ideal.mem_span_singleton_self a
    rw [hq_eq, Ideal.mem_comap] at this
    exact this
  have hb_ne : b ≠ 0 := by
    intro h
    have h1 : algebraMap A Ahat a = 0 := by
      apply φ.injective
      rw [← hb_def, h, map_zero]
    have h_inj : Function.Injective (algebraMap A Ahat) := by
      exact AdicCompletion.of_injective _ _
    exact ha.ne_zero (h_inj (h1.trans (map_zero _).symm))
  -- span{b} ≤ Q with ht(Q)=1; if span{b} were prime then span{b}=Q, contradicting Q not principal
  have hb_not_prime : ¬ (Ideal.span ({b} : Set T)).IsPrime :=
    span_singleton_not_isPrime_of_mem_Q hb_ne hb_mem
  have hT_quot_not_domain : ¬ IsDomain (T ⧸ Ideal.span ({b} : Set T)) :=
    fun h => hb_not_prime
      (Ideal.Quotient.isDomain_iff_prime _ |>.mp h)
  -- Build injective T/bT →+* completion(A/(a)); if codomain is domain, contradiction
  intro h_ai
  unfold IsAnalyticallyIrreducible at h_ai
  set I := Ideal.span ({a} : Set A)
  set Abar := A ⧸ I
  set π := Ideal.Quotient.mk I
  haveI hI_prime : I.IsPrime := (Ideal.span_singleton_prime ha.ne_zero).mpr ha
  haveI : Nontrivial Abar :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top ha.not_unit)
  haveI : IsLocalRing Abar :=
    IsLocalRing.of_surjective' π Ideal.Quotient.mk_surjective
  haveI : IsDomain Abar := Ideal.Quotient.isDomain I
  haveI : IsNoetherianRing Abar := Ideal.Quotient.isNoetherianRing I
  set Mbar := IsLocalRing.maximalIdeal Abar
  letI hCommRing : CommRing (AdicCompletion Mbar Abar) := AdicCompletion.instCommRing Mbar
  have hmap_M : Ideal.map (π : A →+* Abar) M = Mbar :=
    IsLocalRing.map_maximalIdeal_of_surjective π Ideal.Quotient.mk_surjective
  have hmap_pow : ∀ n : ℕ, Ideal.map (π : A →+* Abar) (M ^ n) = Mbar ^ n := by
    intro n
    rw [Ideal.map_pow, hmap_M]
  let g_n : ∀ n : ℕ, A ⧸ M ^ n →+* Abar ⧸ Mbar ^ n := fun n =>
    Ideal.Quotient.lift (M ^ n)
      ((Ideal.Quotient.mk (Mbar ^ n)).comp π)
      (fun x hx => by
        simp only [RingHom.comp_apply]
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        rw [← hmap_pow]
        exact Ideal.mem_map_of_mem π hx)
  have hg_n_mk : ∀ n (x : A),
      g_n n (Ideal.Quotient.mk (M ^ n) x) =
        Ideal.Quotient.mk (Mbar ^ n) (π x) :=
    fun n x => Ideal.Quotient.lift_mk _ _ _
  let f_n : ∀ n : ℕ, T →+* Abar ⧸ Mbar ^ n := fun n =>
    (g_n n).comp ((AdicCompletion.evalₐ M n).toRingHom.comp φ.symm.toRingHom)
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow Mbar hle).comp (f_n n) = f_n m := by
    intro m n hle
    ext t
    simp only [RingHom.comp_apply]
    set xhat := φ.symm t
    change Ideal.Quotient.factorPow Mbar hle (f_n n t) = f_n m t
    change Ideal.Quotient.factorPow Mbar hle
      (g_n n ((AdicCompletion.evalₐ M n) xhat)) =
      g_n m ((AdicCompletion.evalₐ M m) xhat)
    induction xhat using AdicCompletion.induction_on with
    | h seq =>
      rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, hg_n_mk, hg_n_mk]
      change Ideal.Quotient.factorPow Mbar hle
        (Ideal.Quotient.mk (Mbar ^ n) (π (seq.val n))) =
        Ideal.Quotient.mk (Mbar ^ m) (π (seq.val m))
      simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
      rw [Ideal.Quotient.eq, ← map_sub, ← hmap_pow]
      apply Ideal.mem_map_of_mem
      have hcauchy := SModEq.sub_mem.mp (seq.property hle)
      rw [Ideal.smul_eq_mul, Ideal.mul_top] at hcauchy
      have : seq.val n - seq.val m = -(seq.val m - seq.val n) := by ring
      rw [this]
      exact (M ^ m).neg_mem hcauchy
  set ψ := AdicCompletion.liftRingHom Mbar f_n hcompat with hψ_def
  have hψb : ψ b = 0 := by
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [map_zero, AdicCompletion.evalₐ_liftRingHom]
    have hfn_b : f_n n b = 0 := by
      change (g_n n) ((AdicCompletion.evalₐ M n) (φ.symm b)) = 0
      have heval : (AdicCompletion.evalₐ M n) (φ.symm b) = Ideal.Quotient.mk (M ^ n) a := by
        have hφb : φ.symm b = AdicCompletion.of M A a := by
          rw [hb_def, RingEquiv.symm_apply_apply, AdicCompletion.algebraMap_apply]
          simp
        rw [hφb, AdicCompletion.evalₐ_of]
      rw [heval, hg_n_mk]
      simp [show π a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)]
    exact hfn_b
  let ψ' : T ⧸ Ideal.span ({b} : Set T) →+* AdicCompletion Mbar Abar :=
    Ideal.Quotient.lift (Ideal.span ({b} : Set T)) ψ (fun t ht => by
      rw [Ideal.mem_span_singleton] at ht
      obtain ⟨c, rfl⟩ := ht
      rw [map_mul]
      calc ψ b * ψ c = 0 * ψ c := by rw [hψb]
        _ = 0 := zero_mul _)
  have hψ'_inj : Function.Injective ψ' := by
    rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.lift_mk] at hx
    have hfn_zero : ∀ n, f_n n t = 0 := by
      intro n
      have key := AdicCompletion.evalₐ_liftRingHom Mbar f_n hcompat n t
      have heval : (AdicCompletion.evalₐ Mbar n) (ψ t) = 0 :=
        hx ▸ map_zero (AdicCompletion.evalₐ Mbar n)
      exact (key.symm.trans heval)
    set s := φ.symm t
    set J := Ideal.map (algebraMap A Ahat) I
    haveI : IsNoetherianRing Ahat := isNoetherianRing_of_ringEquiv T φ.symm
    haveI : IsLocalRing Ahat := φ.symm.isLocalRing
    set Mhat := IsLocalRing.maximalIdeal Ahat
    haveI : IsNoetherianRing (Ahat ⧸ J) := Ideal.Quotient.isNoetherianRing J
    haveI : Module.Finite Ahat (Ahat ⧸ J) := Module.IsNoetherian.finite Ahat (Ahat ⧸ J)
    haveI : IsHausdorff Mhat (Ahat ⧸ J) := inferInstance
    have hmap_M_hat : Ideal.map (algebraMap A Ahat) M = Mhat := map_maximalIdeal_eq
    suffices hmem : s ∈ J by
      have hJ_eq : J = Ideal.span {algebraMap A Ahat a} := by
        rw [show J = Ideal.map (algebraMap A Ahat) I from rfl,
            show I = Ideal.span {a} from rfl,
            Ideal.map_span, Set.image_singleton]
      rw [hJ_eq, Ideal.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      rw [Submodule.mem_bot]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [Ideal.mem_span_singleton]
      refine ⟨φ c, ?_⟩
      have hs : φ.symm t = s := rfl
      have ht : t = φ s := by rw [← φ.apply_symm_apply t, hs]
      rw [ht, hc, map_mul, ← hb_def]
    -- Show s ∈ J via Hausdorff property of Ahat/J
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hHaus : IsHausdorff Mhat (Ahat ⧸ J) := inferInstance
    apply IsHausdorff.haus hHaus _ (fun n => ?_)
    rw [SModEq.zero]
    simp only [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
               Ideal.Quotient.algebraMap_eq]
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    have hgn_zero : g_n n ((AdicCompletion.evalₐ M n) s) = 0 := by
      have := hfn_zero n
      change (g_n n).comp
        ((AdicCompletion.evalₐ M n).toRingHom.comp φ.symm.toRingHom) t = 0
      exact this
    obtain ⟨x, hx_lift⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ M n s)
    rw [← hx_lift, hg_n_mk] at hgn_zero
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hmap_pow,
        Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hgn_zero
    obtain ⟨y, hy_mem, hy_eq⟩ := hgn_zero
    have hxy : x - y ∈ I := by rw [← Ideal.Quotient.eq]
                               exact hy_eq.symm
    -- Decompose: s = (s - of(x)) + of(y) + of(x-y), each piece in Mhat^n or J
    have h_eval_of : AdicCompletion.evalₐ M n (AdicCompletion.of M A x) =
        Ideal.Quotient.mk (M ^ n) x := AdicCompletion.evalₐ_of M n x
    have h_eval_diff : AdicCompletion.evalₐ M n (s - AdicCompletion.of M A x) = 0 := by
      rw [map_sub, h_eval_of, hx_lift, sub_self]
    set d := s - AdicCompletion.of M A x
    have hmap_pow_hat : Ideal.map (algebraMap A Ahat) (M ^ n) = Mhat ^ n := by
      rw [Ideal.map_pow, hmap_M_hat]
    have h_of_y_mem : AdicCompletion.of M A y ∈ Mhat ^ n := by
      rw [← hmap_pow_hat, show AdicCompletion.of M A y = algebraMap A Ahat y from by
        rw [AdicCompletion.algebraMap_apply]
        rfl]
      exact Ideal.mem_map_of_mem _ hy_mem
    have hd_mem : d ∈ Mhat ^ n :=
      ker_evalₐ_le_maximalIdeal_pow n d h_eval_diff
    refine ⟨d + AdicCompletion.of M A y, add_mem hd_mem h_of_y_mem, ?_⟩
    rw [Ideal.Quotient.eq]
    change d + AdicCompletion.of M A y - s ∈ J
    rw [show d + AdicCompletion.of M A y - s =
      AdicCompletion.of M A y - AdicCompletion.of M A x from by
        simp only [d]
        ring]
    rw [← map_sub, show AdicCompletion.of M A (y - x) = algebraMap A Ahat (y - x) from by
      rw [AdicCompletion.algebraMap_apply]
      rfl]
    exact Ideal.mem_map_of_mem _ (by
                                    rw [← neg_sub]
                                    exact I.neg_mem hxy)
  haveI : IsDomain (AdicCompletion Mbar Abar) := h_ai
  exact hT_quot_not_domain (Function.Injective.isDomain ψ' hψ'_inj)

/-- There exists a prime element a in A such that A/(a) is a 1-dim
Noetherian local domain that is not weakly quasi-complete. -/
theorem exists_prime_bad_quotient
    (A : Type*) [CommRing A] [IsLocalRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] [IsNoetherianRing A]
    (hiso : Nonempty (AdicCompletion (IsLocalRing.maximalIdeal A) A ≃+* T))
    (htrivial : HasTrivialGenericFormalFiber A) :
    ∃ (a : A) (ha : Prime a),
      letI : Nontrivial (A ⧸ Ideal.span {a}) :=
        Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top ha.not_unit)
      letI : IsLocalRing (A ⧸ Ideal.span {a}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      ¬ IsWeaklyQuasiComplete (A ⧸ Ideal.span {a}) := by
  obtain ⟨φ⟩ := hiso
  set Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A with hAhat_def
  set Q' : Ideal Ahat := Ideal.comap φ.toRingHom Q with hQ'_def
  haveI : Q.IsPrime := Q_isPrime
  have hQ'_prime : Q'.IsPrime := Ideal.comap_isPrime φ.toRingHom Q
  have hQ'_ne : Q' ≠ ⊥ := comap_ringEquiv_ne_bot φ Q_ne_bot
  -- q = Q' ∩ A nonzero by trivial generic formal fiber; height 1 by faithful flatness
  set q : Ideal A := Ideal.comap (algebraMap A Ahat) Q' with hq_def
  have hq_prime : q.IsPrime := Ideal.comap_isPrime (algebraMap A Ahat) Q'
  have hq_ne : q ≠ ⊥ := by
    intro hq_bot
    exact hQ'_ne (htrivial Q' hQ'_prime hq_bot)
  have hq_height : q.height = 1 :=
    contraction_height_one A φ q hq_ne hq_prime rfl
  -- UFD: height-1 prime q = (a) for prime a
  obtain ⟨a, ha_prime, hq_eq⟩ := ufd_height_one_principal q hq_prime hq_height
  refine ⟨a, ha_prime, ?_⟩
  set I := Ideal.span {a} with hI_def
  haveI hI_prime : I.IsPrime := (Ideal.span_singleton_prime ha_prime.ne_zero).mpr ha_prime
  haveI : Nontrivial (A ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.span_singleton_ne_top ha_prime.not_unit)
  haveI : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsDomain (A ⧸ I) := Ideal.Quotient.isDomain I
  haveI : IsNoetherianRing (A ⧸ I) := Ideal.Quotient.isNoetherianRing I
  have hdim : ringKrullDim (A ⧸ I) = 1 := quotient_prime_dim_one ⟨φ⟩ a ha_prime
  have h_not_ai : ¬ IsAnalyticallyIrreducible (A ⧸ I) :=
    quotient_not_analytically_irreducible A φ a ha_prime hq_eq.symm
  -- Anderson Cor 2 Part 3: dim 1 + not analytically irred → not WQC
  rw [dim1_wqc_iff_analyticallyIrreducible (A ⧸ I) hdim]
  exact h_not_ai

/-
## Step 3: Main theorem

Combine: A is WQC + some quotient of A is not WQC
→ A is not QC (by Anderson Thm 5: QC ↔ all quotients WQC).
-/

/-- **Main Theorem**: There exists a weakly quasi-complete Noetherian
local ring that is not quasi-complete. -/
theorem anderson_main_theorem :
    ∃ (R : Type) (_ : CommRing R) (_ : IsLocalRing R) (_ : IsNoetherianRing R),
      IsWeaklyQuasiComplete R ∧ ¬ IsQuasiComplete R := by
  obtain ⟨A, instCR, instLR, instDom, instUFM, instNoeth, hiso, htrivial⟩ :=
    jensen_special_case
  have hwqc : @IsWeaklyQuasiComplete A instCR instLR :=
    @a_isWeaklyQuasiComplete A instCR instLR instDom instUFM instNoeth hiso htrivial
  -- Not QC: bad quotient A/(a) contradicts QC ↔ all quotients WQC (Anderson Thm 5)
  have hnqc : ¬ @IsQuasiComplete A instCR instLR := by
    intro hqc
    obtain ⟨a, ha, hbad⟩ :=
      @exists_prime_bad_quotient A instCR instLR instDom instUFM instNoeth hiso htrivial
    have hqc_iff := @isQuasiComplete_iff_quotients_wqc A instCR instLR instNoeth
    have hall_wqc := hqc_iff.mp hqc
    have hne_top : Ideal.span {a} ≠ ⊤ := Ideal.span_singleton_ne_top ha.not_unit
    exact hbad (hall_wqc (Ideal.span {a}) hne_top)
  exact ⟨A, instCR, instLR, instNoeth, hwqc, hnqc⟩

end
