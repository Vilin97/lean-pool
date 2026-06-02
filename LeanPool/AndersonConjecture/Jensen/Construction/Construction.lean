/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.Construction.HeitmannProp
import LeanPool.AndersonConjecture.Jensen.Construction.Transfinite
import LeanPool.AndersonConjecture.Jensen.Defs

/-!
# The Main Transfinite Construction

An ordinal-indexed chain of A-extensions whose union satisfies
Heitmann's Proposition 1 (surjectivity onto T/M² and ideal
contraction), yielding a Noetherian local domain with prescribed
completion (Jensen, 2006, Corollary 2.4).
-/

universe u

noncomputable section

open Cardinal Ideal

variable {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-- Jensen's Corollary 2.4 for P = (0), uncountable version:
Given T a complete local domain with depth ≥ 2, |T/M| = |T|, ℵ₀ < |T|, char 0,
there exists a local UFD A with Â ≅ T and trivial generic formal fiber.

This version uses the cardinal bound `ℵ₀ < #T` instead of countability. -/
private def jensen_construction_p0_uncountable_proof
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (hcard : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hchar : ∀ (n : ℤ), n ≠ 0 → (algebraMap ℤ T n) ≠ 0)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (hht : ∀ (P : Ideal T), P.IsPrime → P ≠ IsLocalRing.maximalIdeal T → P.height ≤ 1) : PLift (
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsDomain A)
      (_ : UniqueFactorizationMonoid A) (_ : IsNoetherianRing A),
      Nonempty (AdicCompletion (@IsLocalRing.maximalIdeal A _ _) A ≃+* T) ∧
      @HasTrivialGenericFormalFiber A _ _ ) := ⟨by
  have hM_not_assoc := maximal_not_assoc_of_depth_ge_two hdepth
  have hAss_ht := assoc_height_le_one_of_domain hdepth hht
  -- Run the transfinite construction to obtain A ⊆ T with surjectivity, closure, and prime data
  obtain ⟨A, hA_surj, hA_closed, hA_primes⟩ :=
    transfinite_construction hdepth hcard hchar hM_not_assoc hAss_ht hT_aleph0
  have hA_noeth : IsNoetherianRing A.carrier :=
    (heitmann_prop1 A.carrier hA_surj hA_closed).1
  have hmap_eq := map_maxIdeal_eq_of_surj_closed A.carrier hA_surj hA_closed
  have hmap_pow : ∀ n : ℕ,
      Ideal.map A.carrier.subtype (IsLocalRing.maximalIdeal A.carrier ^ n) =
        IsLocalRing.maximalIdeal T ^ n := by
    intro n
    rw [Ideal.map_pow, hmap_eq]
  have hclosed_pow : ∀ n : ℕ, ∀ c : A.carrier,
      (c : T) ∈ IsLocalRing.maximalIdeal T ^ n →
      c ∈ IsLocalRing.maximalIdeal A.carrier ^ n := by
    intro n c hc
    rw [← hmap_pow] at hc
    exact hA_closed _ (IsNoetherian.noetherian _) c hc
  -- Build the quotient maps A/(m_A)^n → T/(m_T)^n induced by the inclusion A ↪ T
  let quotMap : ∀ n : ℕ,
      A.carrier ⧸ IsLocalRing.maximalIdeal A.carrier ^ n →+*
        T ⧸ IsLocalRing.maximalIdeal T ^ n := fun n =>
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp A.carrier.subtype) (by
      intro r hr
      change Ideal.Quotient.mk _ (A.carrier.subtype r) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem, ← hmap_pow]
      exact Ideal.mem_map_of_mem A.carrier.subtype hr)
  let f_n : ∀ n : ℕ,
      AdicCompletion (IsLocalRing.maximalIdeal A.carrier) A.carrier →+*
        T ⧸ IsLocalRing.maximalIdeal T ^ n := fun n =>
    (quotMap n).comp (AdicCompletion.evalₐ _ n).toRingHom
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal T) hle).comp (f_n n) =
        f_n m := by
    intro m n hle
    ext x
    simp only [RingHom.comp_apply]
    induction x using AdicCompletion.induction_on with
    | h a =>
      change Ideal.Quotient.factorPow _ hle
        ((quotMap n) ((AdicCompletion.evalₐ _ n).toRingHom
          (AdicCompletion.mk _ _ a))) =
        (quotMap m) ((AdicCompletion.evalₐ _ m).toRingHom
          (AdicCompletion.mk _ _ a))
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          AdicCompletion.evalₐ_mk]
      rw [show (quotMap n) ((Ideal.Quotient.mk _) (a.val n)) =
          Ideal.Quotient.mk _ (A.carrier.subtype (a.val n)) from rfl,
        show Ideal.Quotient.factorPow _ hle
          (Ideal.Quotient.mk _ (A.carrier.subtype (a.val n))) =
          Ideal.Quotient.mk _ (A.carrier.subtype (a.val n)) from rfl,
        show (quotMap m) ((Ideal.Quotient.mk _) (a.val m)) =
          Ideal.Quotient.mk _ (A.carrier.subtype (a.val m)) from rfl,
        Ideal.Quotient.eq]
      rw [← hmap_pow, ← map_sub]
      apply Ideal.mem_map_of_mem A.carrier.subtype
      have hmem := SModEq.sub_mem.mp (a.property hle)
      rw [Ideal.smul_eq_mul, Ideal.mul_top] at hmem
      rw [show a.val n - a.val m = -(a.val m - a.val n) by ring]
      exact neg_mem hmem
  -- Lift the compatible system f_n to the canonical map φ : Â → T using completeness of T
  let φ : AdicCompletion (IsLocalRing.maximalIdeal A.carrier) A.carrier →+* T :=
    IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal T) f_n hcompat
  have hφ_compat : ∀ r : A.carrier,
      φ (algebraMap A.carrier
        (AdicCompletion (IsLocalRing.maximalIdeal A.carrier) A.carrier) r) =
        A.carrier.subtype r := by
    intro r
    rw [← sub_eq_zero]
    apply IsHausdorff.haus
      (IsAdicComplete.toIsHausdorff (I := IsLocalRing.maximalIdeal T))
    intro n
    rw [show (IsLocalRing.maximalIdeal T ^ n • ⊤ : Submodule T T) =
      (IsLocalRing.maximalIdeal T ^ n : Ideal T).restrictScalars T from by simp]
    rw [SModEq.sub_mem]
    simp only [sub_zero]
    change _ ∈ (IsLocalRing.maximalIdeal T ^ n : Ideal T)
    rw [← Ideal.Quotient.eq]
    have h_mk := RingHom.congr_fun
      (IsAdicComplete.mk_comp_liftRingHom _ f_n hcompat n) (algebraMap _ _ r)
    rw [RingHom.comp_apply] at h_mk
    rw [h_mk]
    change (quotMap n) ((AdicCompletion.evalₐ _ n).toRingHom (algebraMap _ _ r)) = _
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      show algebraMap A.carrier
        (AdicCompletion (IsLocalRing.maximalIdeal A.carrier) A.carrier) r =
        AdicCompletion.of (IsLocalRing.maximalIdeal A.carrier) A.carrier r from rfl,
      AdicCompletion.evalₐ_of]
    exact Ideal.Quotient.lift_mk _ _ _
  -- Injectivity of φ: use that each quotMap_n is injective (from ideal closure)
  have hφ_inj : Function.Injective φ := by
    have hqm_inj : ∀ n, Function.Injective (quotMap n) := by
      intro n
      apply RingHom.lift_injective_of_ker_le_ideal
      intro r hr
      rw [RingHom.mem_ker] at hr
      change Ideal.Quotient.mk _ (A.carrier.subtype r) = 0 at hr
      rw [Ideal.Quotient.eq_zero_iff_mem] at hr
      exact hclosed_pow n r hr
    intro x y hxy
    have h_eval_eq : ∀ n,
        (AdicCompletion.evalₐ _ n) x = (AdicCompletion.evalₐ _ n) y := by
      intro n
      apply hqm_inj n
      have h : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ n)).comp φ = f_n n :=
        IsAdicComplete.mk_comp_liftRingHom _ f_n hcompat n
      exact show f_n n x = f_n n y from by rw [← h]
                                           simp [hxy]
    exact AdicCompletion.ext_evalₐ h_eval_eq
  -- Surjectivity of φ: every t ∈ T can be approximated mod M^n by elements of A
  have hφ_surj : Function.Surjective φ := by
    have hsurj_pow : ∀ n : ℕ, Function.Surjective (fun r : A.carrier =>
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ n) (r : T)) := by
      intro n
      induction n with
      | zero =>
        intro q
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
        exact ⟨0, by
          change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ y
          rw [Ideal.Quotient.eq, show IsLocalRing.maximalIdeal T ^ 0 = ⊤ from by
            rw [pow_zero]
            exact Ideal.one_eq_top]
          exact Submodule.mem_top⟩
      | succ n _ih =>
        -- Inductive step: lift the mod-M^n approximation to mod-M^{n+1}
        set M := IsLocalRing.maximalIdeal T
        have hsurj1 : Function.Surjective (fun r : A.carrier =>
            Ideal.Quotient.mk M (r : T)) := by
          intro q
          obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
          obtain ⟨r, hr⟩ := hA_surj (Ideal.Quotient.mk _ t)
          exact ⟨r, by rw [Ideal.Quotient.eq] at hr ⊢
                       exact Ideal.pow_le_self two_ne_zero hr⟩
        -- Key lemma: any element of M^n can be corrected by an element of A to land in M^{n+1}
        have hkey : ∀ m : T, m ∈ M ^ n →
            ∃ d : A.carrier, (d : T) + m ∈ M ^ (n + 1) := by
          intro m hm
          rw [← hmap_pow] at hm
          induction hm using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨s, _, rfl⟩ := hx
            exact ⟨-s, by simp⟩
          | zero => exact ⟨0, by simp⟩
          | add x y _ _ ihx ihy =>
            obtain ⟨dx, hdx⟩ := ihx
            obtain ⟨dy, hdy⟩ := ihy
            exact ⟨dx + dy, by
              change ((dx : T) + (dy : T)) + (x + y) ∈ _
              rw [show ((dx : T) + (dy : T)) + (x + y) =
                ((dx : T) + x) + ((dy : T) + y) from by ring]
              exact (M ^ (n + 1)).add_mem hdx hdy⟩
          | smul a x hx_mem ihx =>
            obtain ⟨dx, hdx⟩ := ihx
            obtain ⟨r_a, hr_a⟩ := hsurj1 (Ideal.Quotient.mk M a)
            have hx_in : x ∈ M ^ n := by rw [← hmap_pow]
                                         exact hx_mem
            refine ⟨r_a * dx, ?_⟩
            change ((r_a : T) * (dx : T)) + a * x ∈ _
            rw [show ((r_a : T) * (dx : T)) + a * x =
              (r_a : T) * ((dx : T) + x) + (a - (r_a : T)) * x from by ring]
            refine (M ^ (n + 1)).add_mem (Ideal.mul_mem_left _ _ hdx) ?_
            have ha_sub : a - (r_a : T) ∈ M := by
              have := M.neg_mem ((Ideal.Quotient.eq (I := M)).mp hr_a)
              rwa [show -((r_a : T) - a) = a - (r_a : T) from by ring] at this
            rw [show M ^ (n + 1) = M * M ^ n from by
              rw [mul_comm]
              exact (pow_succ M n).symm]
            exact Ideal.mul_mem_mul ha_sub hx_in
        intro q
        obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
        obtain ⟨r₀, hr₀⟩ := _ih (Ideal.Quotient.mk _ t)
        have hm : (r₀ : T) - t ∈ M ^ n := (Ideal.Quotient.eq (I := M ^ n)).mp hr₀
        obtain ⟨d, hd⟩ := hkey _ hm
        exact ⟨r₀ + d, by
          change Ideal.Quotient.mk _ ((r₀ + d : A.carrier) : T) = Ideal.Quotient.mk _ t
          rw [Ideal.Quotient.eq]
          change ((r₀ : T) + (d : T)) - t ∈ _
          rw [show ((r₀ : T) + (d : T)) - t = (d : T) + ((r₀ : T) - t) from by ring]
          exact hd⟩
    intro t
    -- For each n, choose r(n) ∈ A with r(n) ≡ t mod M^n; these form a Cauchy sequence in Â
    choose r hr using fun n => hsurj_pow n (Ideal.Quotient.mk _ t)
    have h_cauchy : ∀ n : ℕ,
        r n ≡ r (n + 1) [SMOD (IsLocalRing.maximalIdeal A.carrier ^ n • ⊤ :
          Submodule A.carrier A.carrier)] := by
      intro n
      rw [show (IsLocalRing.maximalIdeal A.carrier ^ n • ⊤ :
        Submodule A.carrier A.carrier) =
        (IsLocalRing.maximalIdeal A.carrier ^ n : Ideal A.carrier).restrictScalars
          A.carrier from by simp]
      rw [SModEq.sub_mem]
      apply hclosed_pow n
      have hmem_n := Ideal.Quotient.eq.mp (hr n)
      have hmem_n1 := Ideal.pow_le_pow_right (Nat.le_succ n)
        (Ideal.Quotient.eq.mp (hr (n + 1)))
      have h1 := sub_mem hmem_n hmem_n1
      rw [sub_sub_sub_cancel_right] at h1
      change A.carrier.subtype (r n - r (n + 1)) ∈ _
      rwa [map_sub]
    -- Package the Cauchy sequence into an element of Â and verify φ maps it to t
    let seq := AdicCompletion.AdicCauchySequence.mk _ _ (fun n => r n) h_cauchy
    let xhat := AdicCompletion.mkₐ (IsLocalRing.maximalIdeal A.carrier) seq
    refine ⟨xhat, ?_⟩
    rw [← sub_eq_zero]
    apply IsHausdorff.haus
      (IsAdicComplete.toIsHausdorff (I := IsLocalRing.maximalIdeal T))
    intro n
    rw [show (IsLocalRing.maximalIdeal T ^ n • ⊤ : Submodule T T) =
      (IsLocalRing.maximalIdeal T ^ n : Ideal T).restrictScalars T from by simp]
    rw [SModEq.sub_mem]
    simp only [sub_zero]
    change _ ∈ (IsLocalRing.maximalIdeal T ^ n : Ideal T)
    rw [← Ideal.Quotient.eq]
    have h_mk :=
      RingHom.congr_fun (IsAdicComplete.mk_comp_liftRingHom _ f_n hcompat n) xhat
    rw [RingHom.comp_apply] at h_mk
    rw [h_mk]
    change (quotMap n) ((AdicCompletion.evalₐ _ n).toRingHom xhat) = _
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      show (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal A.carrier) n) xhat =
        Ideal.Quotient.mk _ (r n) from AdicCompletion.evalₐ_mkₐ ..]
    exact hr n
  -- φ is a ring isomorphism Â ≅ T; now verify the trivial generic formal fiber property
  let φ_equiv := RingEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  have hA_tgff : @HasTrivialGenericFormalFiber A.carrier _ _ := by
    intro P hP hP_comap
    -- Suppose P is a nonzero prime in Â lying over (0);
    -- push forward to Q in T and derive contradiction
    by_contra hP_ne
    set Q := P.map φ_equiv.toRingHom with hQ_def
    haveI : Q.IsPrime := Ideal.map_isPrime_of_equiv φ_equiv
    have hQ_ne : Q ≠ ⊥ := by
      intro h
      apply hP_ne
      rw [eq_bot_iff]
      intro x hx
      have hfx : φ_equiv x ∈ Q := Ideal.mem_map_of_mem _ hx
      rw [h, Ideal.mem_bot] at hfx
      rw [Ideal.mem_bot]
      exact φ_equiv.injective (by rw [hfx, map_zero])
    -- The transfinite construction guarantees Q ∩ A ≠ 0 for any nonzero prime Q of T
    obtain ⟨t, ht_mem, ht_ne⟩ := hA_primes Q inferInstance hQ_ne
    have h_alg_eq : algebraMap A.carrier
        (AdicCompletion (IsLocalRing.maximalIdeal A.carrier) A.carrier) t =
        φ_equiv.symm (A.carrier.subtype t) := by
      apply φ_equiv.injective
      rw [RingEquiv.apply_symm_apply]
      exact hφ_compat t
    have h_symm_mem : φ_equiv.symm (A.carrier.subtype t) ∈ P := by
      have h_in_map : φ_equiv (φ_equiv.symm (A.carrier.subtype t)) ∈
          Ideal.map φ_equiv.toRingHom P := by
        rw [RingEquiv.apply_symm_apply]
        exact ht_mem
      obtain ⟨y, hy_mem, hy_eq⟩ := (Ideal.mem_map_iff_of_surjective _
        φ_equiv.surjective).mp h_in_map
      have := φ_equiv.injective hy_eq
      rwa [this] at hy_mem
    rw [← h_alg_eq] at h_symm_mem
    have h_bot := hP_comap ▸ (Ideal.mem_comap.mpr h_symm_mem)
    rw [Ideal.mem_bot] at h_bot
    exact ht_ne (congrArg A.carrier.subtype h_bot)
  exact ⟨↥A.carrier, inferInstance, inferInstance, inferInstance, inferInstance,
    hA_noeth, ⟨φ_equiv⟩, hA_tgff⟩
⟩

theorem jensen_construction_p0_uncountable
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (hcard : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hchar : ∀ (n : ℤ), n ≠ 0 → (algebraMap ℤ T n) ≠ 0)
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (hht : ∀ (P : Ideal T), P.IsPrime → P ≠ IsLocalRing.maximalIdeal T → P.height ≤ 1) :
    ∃ (A : Type u) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsDomain A)
      (_ : UniqueFactorizationMonoid A) (_ : IsNoetherianRing A),
      Nonempty (AdicCompletion (@IsLocalRing.maximalIdeal A _ _) A ≃+* T) ∧
      @HasTrivialGenericFormalFiber A _ _ := by
  exact
    (jensen_construction_p0_uncountable_proof
      hdepth hcard hchar hT_aleph0 hht
    ).down
end
