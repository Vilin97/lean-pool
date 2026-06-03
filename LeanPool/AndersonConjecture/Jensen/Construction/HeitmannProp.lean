/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Heitmann's Proposition 1

If a subring R of a complete local domain T surjects onto T/M^2
and satisfies IT cap R = I for all finitely generated ideals I,
then R is Noetherian with completion isomorphic to T. Also: when
depth T >= 2, associated primes of T have height at most 1.

Heitmann, "Characterization of completions of UFDs", 1993, Prop. 1.
-/

universe u

noncomputable section

open Cardinal Ideal

variable {T : Type u} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

/-!
## Helper lemmas for the completion isomorphism
-/

omit [IsNoetherianRing T] [IsDomain T] in
/-- The maximal ideal of a local subring R maps into the maximal ideal of T
under the subtype inclusion, given the closedness condition IT ∩ R = I. -/
private lemma map_maxIdeal_le_of_closed
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

omit [IsNoetherianRing T] [IsDomain T] in
/-- The contraction of the maximal ideal of T to a local subring R
is contained in the maximal ideal of R (units in R map to units in T). -/
private lemma comap_maxIdeal_le_of_local
    (R : Subring T) [IsLocalRing ↥R] :
    (IsLocalRing.maximalIdeal T).comap R.subtype ≤ IsLocalRing.maximalIdeal ↥R := by
  intro r hr
  rw [Ideal.mem_comap] at hr
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact fun hru => absurd hr (by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    exact hru.map R.subtype)

omit [IsDomain T] in
/-- Under the hypotheses of Proposition 1, M = M_R · T.
This is a Nakayama argument: R + M² = T implies M ≤ Ideal.map R.subtype M_R + M²,
and since M is f.g. and M ≤ jacobson ⊥, Nakayama gives M ≤ Ideal.map R.subtype M_R. -/
lemma map_maxIdeal_eq_of_surj_closed
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : Subring T) [IsLocalRing ↥R]
    (h_surj : Function.Surjective (fun r : ↥R =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (r : T)))
    (h_closed : ∀ (I : Ideal ↥R), I.FG →
      ∀ (c : ↥R), (c : T) ∈ Ideal.map R.subtype I → c ∈ I) :
    Ideal.map R.subtype (IsLocalRing.maximalIdeal ↥R) = IsLocalRing.maximalIdeal T := by
  apply le_antisymm (map_maxIdeal_le_of_closed R h_closed)
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
      comap_maxIdeal_le_of_local R (Ideal.mem_comap.mpr hr_in_M)
    rw [show m = (r : T) + (m - (r : T)) from by ring]
    apply Submodule.add_mem_sup
    · exact Ideal.mem_map_of_mem R.subtype hr_in_MR
    · have hmr : m - (r : T) ∈ IsLocalRing.maximalIdeal T ^ 2 := by
        rw [show m - (r : T) = -((r : T) - m) from by ring]
        exact neg_mem hdiff
      rwa [sq] at hmr

/-!
## Proposition 1: Criterion for Noetherian completion

If (R, M ∩ R) ⊆ (T, M) with R → T/M² surjective and IT ∩ R = I for all
finitely generated ideals I, then R is Noetherian and R̂ ≅ T.
-/

omit [IsLocalRing T] [IsDomain T] in
/-- Under the closedness condition IT ∩ R = I for all finitely generated ideals I,
the subring R is Noetherian: every ideal of R is finitely generated because its
extension to T is, and generators pull back through `h_closed`. -/
private lemma heitmann_prop1_isNoetherian
    (R : Subring T)
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

omit [IsDomain T] in
/-- Under the hypotheses of Proposition 1, `R → T/Mⁿ` is surjective for every `n`,
by induction on `n` using surjectivity onto `T/M²` and a Nakayama-style argument
that lifts elements of `Mⁿ` modulo `Mⁿ⁺¹` to `R`. -/
private lemma heitmann_prop1_surj_pow
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : Subring T) [IsLocalRing R]
    (h_surj : Function.Surjective (fun r : R =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (r : T)))
    (h_closed : ∀ (I : Ideal R), I.FG →
      ∀ (c : R), (c : T) ∈ Ideal.map R.subtype I → c ∈ I) :
    ∀ n : ℕ, Function.Surjective (fun r : ↥R =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ n) (r : T)) := by
  have hmap_eq := map_maxIdeal_eq_of_surj_closed R h_surj h_closed
  have hmap_pow : ∀ n : ℕ,
      Ideal.map R.subtype (IsLocalRing.maximalIdeal ↥R ^ n) =
        IsLocalRing.maximalIdeal T ^ n := by
    intro n
    rw [Ideal.map_pow, hmap_eq]
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
    set M := IsLocalRing.maximalIdeal T
    have hsurj1 : Function.Surjective (fun r : ↥R =>
        Ideal.Quotient.mk M (r : T)) := by
      intro q
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective q
      obtain ⟨r, hr⟩ := h_surj (Ideal.Quotient.mk _ t)
      exact ⟨r, by rw [Ideal.Quotient.eq] at hr ⊢
                   exact Ideal.pow_le_self two_ne_zero hr⟩
    -- For m ∈ M^n, find d : R with (d:T) + m ∈ M^{n+1}
    have hkey : ∀ m : T, m ∈ M ^ n →
        ∃ d : ↥R, (d : T) + m ∈ M ^ (n + 1) := by
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
          rw [show ((dx : T) + (dy : T)) + (x + y) = ((dx : T) + x) + ((dy : T) + y)
            from by ring]
          exact (M ^ (n + 1)).add_mem hdx hdy⟩
      | smul a x hx_mem ihx =>
        obtain ⟨dx, hdx⟩ := ihx
        obtain ⟨r_a, hr_a⟩ := hsurj1 (Ideal.Quotient.mk M a)
        have he : (r_a : T) - a ∈ M := (Ideal.Quotient.eq (I := M)).mp hr_a
        have hx_in : x ∈ M ^ n := by rw [← hmap_pow]
                                     exact hx_mem
        refine ⟨r_a * dx, ?_⟩
        change ((r_a : T) * (dx : T)) + a * x ∈ _
        rw [show ((r_a : T) * (dx : T)) + a * x =
          (r_a : T) * ((dx : T) + x) + (a - (r_a : T)) * x from by ring]
        refine (M ^ (n + 1)).add_mem (Ideal.mul_mem_left _ _ hdx) ?_
        have ha_sub : a - (r_a : T) ∈ M := by
          have := M.neg_mem he
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
      change Ideal.Quotient.mk _ ((r₀ + d : ↥R) : T) = Ideal.Quotient.mk _ t
      rw [Ideal.Quotient.eq]
      change ((r₀ : T) + (d : T)) - t ∈ _
      rw [show ((r₀ : T) + (d : T)) - t = (d : T) + ((r₀ : T) - t) from by ring]
      exact hd⟩

omit [IsDomain T] in
/-- Heitmann's Proposition 1: A subring R of a complete local ring T satisfying
- R → T/M² surjective
- IT ∩ R = I for all finitely generated ideals I of R
is Noetherian with completion isomorphic to T. -/
theorem heitmann_prop1
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : Subring T) [IsLocalRing R]
    (h_surj : Function.Surjective (fun r : R =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (r : T)))
    (h_closed : ∀ (I : Ideal R), I.FG →
      ∀ (c : R), (c : T) ∈ Ideal.map R.subtype I → c ∈ I) :
    IsNoetherianRing R ∧
    ∃ (e : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* T),
      ∀ (a : R), e (AdicCompletion.of (IsLocalRing.maximalIdeal R) R a) = R.subtype a := by
  constructor
  · -- R is Noetherian: pull back f.g. from T via h_closed
    exact heitmann_prop1_isNoetherian R h_closed
  · -- Completion isomorphism: R̂ ≅ T
    have hmap_eq := map_maxIdeal_eq_of_surj_closed R h_surj h_closed
    have hmap_pow : ∀ n : ℕ,
        Ideal.map R.subtype (IsLocalRing.maximalIdeal ↥R ^ n) =
          IsLocalRing.maximalIdeal T ^ n := by
      intro n
      rw [Ideal.map_pow, hmap_eq]
    -- R → T/M^n is surjective for all n (induction)
    have hsurj_pow := heitmann_prop1_surj_pow R h_surj h_closed
    -- M^n ∩ R = M_R^n via h_closed
    have hclosed_pow : ∀ n : ℕ, ∀ c : ↥R,
        (c : T) ∈ IsLocalRing.maximalIdeal T ^ n →
        c ∈ IsLocalRing.maximalIdeal ↥R ^ n := by
      intro n c hc
      rw [← hmap_pow] at hc
      have hR_noeth : IsNoetherianRing ↥R := heitmann_prop1_isNoetherian R h_closed
      exact h_closed _ (IsNoetherian.noetherian _) c hc
    -- Build φ : AdicCompletion M_R R →+* T via compatible quotient maps
    let quotMap : ∀ n : ℕ,
        ↥R ⧸ IsLocalRing.maximalIdeal ↥R ^ n →+*
          T ⧸ IsLocalRing.maximalIdeal T ^ n := fun n =>
      Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp R.subtype) (by
        intro r hr
        change Ideal.Quotient.mk _ (R.subtype r) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, ← hmap_pow]
        exact Ideal.mem_map_of_mem R.subtype hr)
    let f_n : ∀ n : ℕ,
        AdicCompletion (IsLocalRing.maximalIdeal ↥R) ↥R →+*
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
            Ideal.Quotient.mk _ (R.subtype (a.val n)) from rfl,
          show Ideal.Quotient.factorPow _ hle
            (Ideal.Quotient.mk _ (R.subtype (a.val n))) =
            Ideal.Quotient.mk _ (R.subtype (a.val n)) from rfl,
          show (quotMap m) ((Ideal.Quotient.mk _) (a.val m)) =
            Ideal.Quotient.mk _ (R.subtype (a.val m)) from rfl,
          Ideal.Quotient.eq]
        rw [← hmap_pow, ← map_sub]
        apply Ideal.mem_map_of_mem R.subtype
        have hmem := SModEq.sub_mem.mp (a.property hle)
        rw [Ideal.smul_eq_mul, Ideal.mul_top] at hmem
        rw [show a.val n - a.val m = -(a.val m - a.val n) by ring]
        exact neg_mem hmem
    let φ : AdicCompletion (IsLocalRing.maximalIdeal ↥R) ↥R →+* T :=
      IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal T) f_n hcompat
    have hφ_surj : Function.Surjective φ := by
      intro t
      choose r hr using fun n =>
        hsurj_pow n (Ideal.Quotient.mk _ t)
      have h_cauchy : ∀ n : ℕ,
          r n ≡ r (n + 1)
            [SMOD (IsLocalRing.maximalIdeal ↥R ^ n • ⊤ :
              Submodule ↥R ↥R)] := by
        intro n
        rw [show (IsLocalRing.maximalIdeal ↥R ^ n • ⊤ : Submodule ↥R ↥R) =
          (IsLocalRing.maximalIdeal ↥R ^ n : Ideal ↥R).restrictScalars ↥R from by
            simp]
        rw [SModEq.sub_mem]
        apply hclosed_pow n
        have h1 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ n) (R.subtype (r n)) =
            Ideal.Quotient.mk _ t := hr n
        have h2 : Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ (n + 1))
            (R.subtype (r (n + 1))) = Ideal.Quotient.mk _ t := hr (n + 1)
        have hmem_n : R.subtype (r n) - t ∈ IsLocalRing.maximalIdeal T ^ n :=
          Ideal.Quotient.eq.mp h1
        have hmem_n1 : R.subtype (r (n + 1)) - t ∈ IsLocalRing.maximalIdeal T ^ n :=
          Ideal.pow_le_pow_right (Nat.le_succ n)
            (Ideal.Quotient.eq.mp h2)
        have : R.subtype (r n) - R.subtype (r (n + 1)) ∈
            IsLocalRing.maximalIdeal T ^ n :=
          show R.subtype (r n) - R.subtype (r (n + 1)) ∈ _ by
            have := sub_mem hmem_n hmem_n1
            rwa [sub_sub_sub_cancel_right] at this
        rwa [← map_sub] at this
      let seq := AdicCompletion.AdicCauchySequence.mk
        (IsLocalRing.maximalIdeal ↥R) (↥R) (fun n => r n) h_cauchy
      let xhat := AdicCompletion.mkₐ (IsLocalRing.maximalIdeal ↥R) seq
      refine ⟨xhat, ?_⟩
      -- Hausdorff separation: φ(xhat) = t
      rw [← sub_eq_zero]
      apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := IsLocalRing.maximalIdeal T))
      intro n
      rw [show (IsLocalRing.maximalIdeal T ^ n • ⊤ : Submodule T T) =
        (IsLocalRing.maximalIdeal T ^ n : Ideal T).restrictScalars T from by
          simp]
      rw [SModEq.sub_mem]
      simp only [sub_zero]
      change _ ∈ (IsLocalRing.maximalIdeal T ^ n : Ideal T)
      rw [← Ideal.Quotient.eq]
      have h_mk_φ : Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ n) (φ xhat) =
          f_n n xhat :=
        RingHom.congr_fun (IsAdicComplete.mk_comp_liftRingHom
          (IsLocalRing.maximalIdeal T) f_n hcompat n) xhat
      rw [h_mk_φ]
      change (quotMap n) ((AdicCompletion.evalₐ _ n).toRingHom xhat) = _
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        show (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal ↥R) n) xhat =
          Ideal.Quotient.mk _ (r n) from AdicCompletion.evalₐ_mkₐ ..]
      exact hr n
    -- φ is injective: quotMap n is injective for each n
    have hφ_inj : Function.Injective φ := by
      have hqm_inj : ∀ n, Function.Injective (quotMap n) := by
        intro n
        apply RingHom.lift_injective_of_ker_le_ideal
        intro r hr
        rw [RingHom.mem_ker] at hr
        change Ideal.Quotient.mk _ (R.subtype r) = 0 at hr
        rw [Ideal.Quotient.eq_zero_iff_mem] at hr
        exact hclosed_pow n r hr
      intro x y hxy
      have h_fn_eq : ∀ n, f_n n x = f_n n y := by
        intro n
        have : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ n)).comp φ = f_n n :=
          IsAdicComplete.mk_comp_liftRingHom _ f_n hcompat n
        rw [← this]
        simp [hxy]
      have h_eval_eq : ∀ n, (AdicCompletion.evalₐ _ n) x = (AdicCompletion.evalₐ _ n) y :=
        fun n => hqm_inj n (h_fn_eq n)
      exact AdicCompletion.ext_evalₐ h_eval_eq
    let φ_equiv := RingEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
    have hφ_compat : ∀ r : ↥R,
        φ_equiv (AdicCompletion.of (IsLocalRing.maximalIdeal ↥R) ↥R r) = R.subtype r := by
      intro r
      change φ (AdicCompletion.of _ _ r) = _
      rw [← sub_eq_zero]
      apply IsHausdorff.haus
        (IsAdicComplete.toIsHausdorff (I := IsLocalRing.maximalIdeal T))
      intro n
      rw [show (IsLocalRing.maximalIdeal T ^ n • ⊤ : Submodule T T) =
        (IsLocalRing.maximalIdeal T ^ n : Ideal T).restrictScalars T from by
          simp]
      rw [SModEq.sub_mem]
      simp only [sub_zero]
      change _ ∈ (IsLocalRing.maximalIdeal T ^ n : Ideal T)
      rw [← Ideal.Quotient.eq]
      have h_mk := RingHom.congr_fun
        (IsAdicComplete.mk_comp_liftRingHom _ f_n hcompat n)
        (AdicCompletion.of _ _ r)
      rw [RingHom.comp_apply] at h_mk
      rw [h_mk]
      change (quotMap n) ((AdicCompletion.evalₐ _ n).toRingHom
        (AdicCompletion.of _ _ r)) = _
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AdicCompletion.evalₐ_of]
      exact Ideal.Quotient.lift_mk _ _ _
    exact ⟨φ_equiv, hφ_compat⟩

/-!
## Auxiliary: Depth ≥ 2 implies associated prime conditions

From depth T ≥ 2, we derive:
1. M is not an associated prime of T/rT for any nonzero r (since ht(M) ≥ 2 > 1)
2. All associated primes of T/rT have height ≤ 1 (Krull PIT for principal ideals)
-/

/-- In a local domain with depth ≥ 2, the maximal ideal M is not an associated
prime of T/rT for any nonzero r. This follows because if M ∈ Ass(T/rT) then
depth(M, T/rT) = 0, but depth(M, T) ≥ 2 and r is regular (domain) so
depth(M, T/rT) ≥ 1 by the depth lemma. -/
theorem maximal_not_assoc_of_depth_ge_two
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
  -- Cancel r (domain), then use b regular on T/aT to get y₁ ∈ aT
  have h_cancel : b * y₁ = a * y₂ := mul_left_cancel₀ hr h_eq
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
  -- Cancel a (regular on T): x_lift = r * z, contradicting x ≠ 0
  have h_ax : a * x_lift = a * (r * z) := by rw [hy₁, hz]
                                             ring
  have h_x_eq : x_lift = r * z := by
    have := ha_reg (show a • x_lift = a • (r * z) by rwa [smul_eq_mul, smul_eq_mul])
    exact this
  exact hx_not_mem (Ideal.mem_span_singleton.mpr ⟨z, h_x_eq⟩)

/-- In a Noetherian local domain with depth ≥ 2, if all primes P ≠ M have height ≤ 1,
then associated primes of T/rT for nonzero r have height ≤ 1.
The height hypothesis holds for our concrete T (dim = 2). -/
theorem assoc_height_le_one_of_domain
    (hdepth : ∃ (a b : T), a ∈ IsLocalRing.maximalIdeal T ∧
      b ∈ IsLocalRing.maximalIdeal T ∧
      RingTheory.Sequence.IsRegular T [a, b])
    (hht : ∀ (P : Ideal T), P.IsPrime → P ≠ IsLocalRing.maximalIdeal T → P.height ≤ 1)
    (r : T) (hr : r ≠ 0)
    (P : Ideal T) (hP : P ∈ associatedPrimes T (T ⧸ Ideal.span {r})) :
    P.height ≤ 1 := by
  have hP_prime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hP_ne_M : P ≠ IsLocalRing.maximalIdeal T := by
    intro h
    subst h
    exact maximal_not_assoc_of_depth_ge_two hdepth r hr hP
  exact hht P hP_prime hP_ne_M

end
