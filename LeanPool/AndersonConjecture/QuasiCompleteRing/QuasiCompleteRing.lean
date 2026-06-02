/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.AdicLocal
import LeanPool.AndersonConjecture.AdicNoetherian
import LeanPool.AndersonConjecture.QuasiCompleteRing.Complete
import Mathlib.Order.BourbakiWitt
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# LeanPool.AndersonConjecture.QuasiCompleteRing.QuasiCompleteRing

Imported Lean Pool material for `LeanPool.AndersonConjecture.QuasiCompleteRing.QuasiCompleteRing`.
-/

open scoped Pointwise

/-!
# Anderson's Characterisations of Quasi-Complete Rings

Two results from Anderson (2014). Theorem 4: a Noetherian local
ring R is weakly quasi-complete iff every nonzero prime of its
completion contracts to a nonzero ideal of R. Theorem 5: R is
quasi-complete iff every quotient R/I is weakly quasi-complete.
-/

/-
## Anderson Corollary 2, Part 1 (= Farley Prop 1)

For a Noetherian local domain R:
  R is WQC ↔ for every nonzero prime P of the completion R̂,
  the contraction P ∩ R ≠ ⊥.

Here R̂ = AdicCompletion (IsLocalRing.maximalIdeal R) R,
and contraction = Ideal.comap (algebraMap R R̂).
-/
lemma Mhat_isMaximal
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
      (IsLocalRing.maximalIdeal R)).IsMaximal := by
  set M := IsLocalRing.maximalIdeal R
  set f := algebraMap R (AdicCompletion M R)
  set Mhat := Ideal.map f M
  have hM1 : M ^ 1 = M := pow_one M
  have heval_surj : Function.Surjective (AdicCompletion.evalₐ M 1).toRingHom := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨f r, AdicCompletion.evalₐ_of M 1 r⟩
  haveI : (⊥ : Ideal (R ⧸ M ^ 1)).IsMaximal := by
    rw [hM1]
    exact @Ideal.bot_isMaximal (R ⧸ M)
      (Ideal.Quotient.field M).toDivisionSemiring
  have hker_max : (Ideal.comap (AdicCompletion.evalₐ M 1).toRingHom ⊥).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ heval_surj
  have hcomap_bot : Ideal.comap (AdicCompletion.evalₐ M 1).toRingHom ⊥ =
      RingHom.ker (AdicCompletion.evalₐ M 1).toRingHom := by
    ext x
    simp [RingHom.mem_ker, Ideal.mem_comap]
  rw [hcomap_bot] at hker_max
  -- ker(evalₐ 1) = M̂
  have hker_eq : RingHom.ker (AdicCompletion.evalₐ M 1).toRingHom = Mhat := by
    apply le_antisymm
    · intro y hy
      rw [RingHom.mem_ker] at hy
      have := mem_map_pow_of_evalₐ_eq_zero R 1 y hy
      rwa [pow_one] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro m hm
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change (AdicCompletion.evalₐ M 1) (AdicCompletion.of M R m) = 0
      rw [AdicCompletion.evalₐ_of, hM1]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rwa [hker_eq] at hker_max

lemma iInf_comap_add_pow_eq_comap
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (A : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    (⨅ n, Ideal.comap (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
      (A ⊔ (Ideal.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))
        (IsLocalRing.maximalIdeal R)) ^ n)) =
    Ideal.comap (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) A := by
  haveI : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    adicCompletion_isNoetherianRing R
  haveI : IsLocalRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    adicCompletion_isLocalRing R
  set f := algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)
  set Mhat := Ideal.map f (IsLocalRing.maximalIdeal R)
  have hMhat_eq : Mhat = IsLocalRing.maximalIdeal (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    IsLocalRing.eq_maximalIdeal (Mhat_isMaximal R)
  have hkrull := krull_intersection_sup (R := AdicCompletion (IsLocalRing.maximalIdeal R) R) A
  rw [← hMhat_eq] at hkrull
  apply le_antisymm
  · intro r hr
    rw [Submodule.mem_iInf] at hr
    have hfr : f r ∈ A := by
      rw [← hkrull]
      rw [Submodule.mem_iInf]
      intro n
      exact Ideal.mem_comap.mp (hr n)
    exact Ideal.mem_comap.mpr hfr
  · exact le_iInf fun n => Ideal.comap_mono le_sup_left

-- WQC + domain implies every nonzero ideal of R̂ has nonzero contraction to R.
lemma wqc_implies_ideals_meet
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (hwqc : IsWeaklyQuasiComplete R)
    (A : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R)) (hA : A ≠ ⊥) :
    Ideal.comap (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) A ≠ ⊥ := by
  let M := IsLocalRing.maximalIdeal R
  let f := algebraMap R (AdicCompletion M R)
  let Mhat := Ideal.map f M
  intro hcontra
  apply hA
  clear hA
  let C : ℕ → Ideal R := fun n => Ideal.comap f (A + Mhat ^ n)
  have hC_anti : Antitone C := fun m n hmn => Ideal.comap_mono
    (sup_le_sup_left (Ideal.pow_le_pow_right hmn) A)
  have hC_iInf : ⨅ n, C n = ⊥ :=
    (iInf_comap_add_pow_eq_comap R A).trans hcontra
  suffices hk : ∀ k : ℕ, A ≤ Mhat ^ k by
    rw [eq_bot_iff]
    intro x hx
    apply (isHausdorff_iff.mp (inferInstance : IsHausdorff M (AdicCompletion M R))) x
    intro n
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_top_eq_map, Ideal.map_pow]
    exact hk n hx
  intro k
  obtain ⟨s, hs⟩ := hwqc C hC_anti hC_iInf k
  intro a ha
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (I := M ^ (max s k))
    (AdicCompletion.evalₐ M (max s k) a)
  have heval_eq : AdicCompletion.evalₐ M (max s k) (f r) =
      AdicCompletion.evalₐ M (max s k) a := by
    change AdicCompletion.evalₐ M _ (AdicCompletion.of M R r) = _
    rw [AdicCompletion.evalₐ_of, hr]
  have heval_diff : AdicCompletion.evalₐ M (max s k) (a - f r) = 0 := by
    set e := AdicCompletion.evalₐ M (max s k)
    show e (a - f r) = 0
    rw [map_sub, heval_eq, sub_self]
  have hdiff : a - f r ∈ Mhat ^ (max s k) :=
    mem_map_pow_of_evalₐ_eq_zero R (max s k) (a - f r) heval_diff
  have hfr_mem : f r ∈ A + Mhat ^ s :=
    Submodule.mem_sup.mpr ⟨a, ha, -(a - f r),
      neg_mem (Ideal.pow_le_pow_right (le_max_left s k) hdiff), by ring⟩
  have hr_Mk : r ∈ M ^ k := hs (Ideal.mem_comap.mpr hfr_mem)
  have hfr_Mk : f r ∈ Mhat ^ k := by
    have : f r ∈ Ideal.map f (M ^ k) := Ideal.mem_map_of_mem f hr_Mk
    rwa [Ideal.map_pow] at this
  have hdiff_Mk : a - f r ∈ (Mhat ^ k : Ideal (AdicCompletion M R)) :=
    Ideal.pow_le_pow_right (le_max_right s k) hdiff
  have : a = f r + (a - f r) := by ring
  rw [this]
  exact Ideal.add_mem _ hfr_Mk hdiff_Mk

lemma not_wqc_exists_maximal_zero_contraction
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (hnwqc : ¬IsWeaklyQuasiComplete R) :
    ∃ A : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      A ≠ ⊥ ∧
      Ideal.comap (algebraMap R
        (AdicCompletion (IsLocalRing.maximalIdeal R) R)) A = ⊥ ∧
      ∀ B : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R),
        A < B →
        Ideal.comap (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) B ≠ ⊥ := by
  set f := algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R) with hf_def
  -- ¬WQC implies ∃ nonzero ideal with zero contraction (contrapositive of Thm 4(3))
  have hexists : ∃ A₀ : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R),
      A₀ ≠ ⊥ ∧ Ideal.comap f A₀ = ⊥ := by
    set M := IsLocalRing.maximalIdeal R
    change ∃ A₀, A₀ ≠ ⊥ ∧ Ideal.comap (algebraMap R (AdicCompletion M R)) A₀ = ⊥
    set g := algebraMap R (AdicCompletion M R)
    set Mhat := Ideal.map g M
    by_contra hall
    push Not at hall
    apply hnwqc
    intro B hB hBinf k
    set B' : ℕ → Ideal (AdicCompletion M R) :=
      fun n => Ideal.map g (B n)
    have hB'_anti : Antitone B' :=
      fun _ _ hmn => Ideal.map_mono (hB hmn)
    have hB'inf : ⨅ n, B' n = ⊥ := by
      by_contra hne
      have hcomap_ne : Ideal.comap g (⨅ n, B' n) ≠ ⊥ := hall _ hne
      apply hcomap_ne
      rw [eq_bot_iff]
      intro r hr
      have hgr : g r ∈ ⨅ n, B' n := Ideal.mem_comap.mp hr
      have : ∀ n, r ∈ B n := fun n => by
        have hgr_n : g r ∈ B' n := (Submodule.mem_iInf _).mp hgr n
        have hmem : r ∈ Ideal.comap g (Ideal.map g (B n)) := Ideal.mem_comap.mpr hgr_n
        rwa [comap_map_algebraMap_adicCompletion] at hmem
      rw [← hBinf]
      exact (Submodule.mem_iInf _).mpr this
    haveI : IsNoetherianRing (AdicCompletion M R) := adicCompletion_isNoetherianRing R
    haveI : IsLocalRing (AdicCompletion M R) := adicCompletion_isLocalRing R
    have hMhat_max : Mhat.IsMaximal := Mhat_isMaximal R
    have hMhat_eq : Mhat = IsLocalRing.maximalIdeal (AdicCompletion M R) :=
      IsLocalRing.eq_maximalIdeal hMhat_max
    -- M^n•⊤ and Mhat^n coincide as subsets of R̂
    have hmem_R_iff : ∀ n (x : AdicCompletion M R),
        x ∈ (M ^ n • ⊤ : Submodule R (AdicCompletion M R)) ↔
        x ∈ (Mhat ^ n : Ideal (AdicCompletion M R)) := by
      intro n x
      rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
    have hmem_Rhat_iff : ∀ n (x : AdicCompletion M R),
        x ∈ (Mhat ^ n • ⊤ : Submodule (AdicCompletion M R) (AdicCompletion M R)) ↔
        x ∈ (Mhat ^ n : Ideal (AdicCompletion M R)) := by
      intro n x
      constructor
      · intro hx
        refine Submodule.smul_induction_on hx (fun a ha b _ => ?_) (fun a b ha hb => ?_)
        · exact Ideal.mul_mem_right b _ ha
        · exact (Mhat ^ n).add_mem ha hb
      · intro hx
        change x ∈ (Mhat ^ n • ⊤ : Submodule (AdicCompletion M R) (AdicCompletion M R))
        have h3 := Submodule.smul_mem_smul hx (Submodule.mem_top (R := AdicCompletion M R)
          (M := AdicCompletion M R) (x := (1 : AdicCompletion M R)))
        convert h3 using 1
        exact (mul_one x).symm
    have hsmod_R_to_Rhat : ∀ n (x y : AdicCompletion M R),
        x ≡ y [SMOD (M ^ n • ⊤ : Submodule R (AdicCompletion M R))] →
        x ≡ y [SMOD (Mhat ^ n • ⊤ :
          Submodule (AdicCompletion M R)
            (AdicCompletion M R))] := by
      intro n x y h
      rw [SModEq.sub_mem] at h ⊢
      exact (hmem_Rhat_iff n _).mpr ((hmem_R_iff n _).mp h)
    have hsmod_Rhat_to_R :
        ∀ n (x y : AdicCompletion M R),
        x ≡ y [SMOD (Mhat ^ n • ⊤ :
          Submodule (AdicCompletion M R)
            (AdicCompletion M R))] →
        x ≡ y [SMOD (M ^ n • ⊤ : Submodule R (AdicCompletion M R))] := by
      intro n x y h
      rw [SModEq.sub_mem] at h ⊢
      exact (hmem_R_iff n _).mpr ((hmem_Rhat_iff n _).mp h)
    -- Construct IsAdicComplete for R̂ w.r.t. its maximal ideal
    have hAC : IsAdicComplete (IsLocalRing.maximalIdeal (AdicCompletion M R))
        (AdicCompletion M R) := by
      rw [← hMhat_eq]
      have hHaus : IsHausdorff Mhat (AdicCompletion M R) :=
        IsHausdorff.map_algebraMap_iff.mpr inferInstance
      have hPrec : IsPrecomplete Mhat (AdicCompletion M R) :=
        ⟨fun c hc => by
          have hc' : ∀ {m n : ℕ}, m ≤ n →
              c m ≡ c n [SMOD (M ^ m • ⊤ : Submodule R (AdicCompletion M R))] :=
            fun hmn => hsmod_Rhat_to_R _ _ _ (hc hmn)
          obtain ⟨L, hL⟩ := (adicCompletion_isPrecomplete (R := R)).prec' c hc'
          exact ⟨L, fun n => hsmod_R_to_Rhat n _ _ (hL n)⟩⟩
      exact { toIsHausdorff := hHaus, toIsPrecomplete := hPrec }
    -- R̂ is QC (complete + Noetherian + local), apply WQC of R̂ to B'
    have hQC : IsQuasiComplete (AdicCompletion M R) :=
      anderson_complete_isQuasiComplete _ hAC
    have hWQC : IsWeaklyQuasiComplete (AdicCompletion M R) := hQC.isWeaklyQuasiComplete
    obtain ⟨s, hs⟩ := hWQC B' hB'_anti hB'inf k
    exact ⟨s, fun r hr => by
      have hgr : g r ∈ B' s := Ideal.mem_map_of_mem _ hr
      have hgr_Mk : g r ∈ (IsLocalRing.maximalIdeal (AdicCompletion M R)) ^ k := hs hgr
      rw [← hMhat_eq, ← Ideal.map_pow] at hgr_Mk
      have hmem : r ∈ Ideal.comap g (Ideal.map g (M ^ k)) := Ideal.mem_comap.mpr hgr_Mk
      rwa [comap_map_algebraMap_adicCompletion] at hmem⟩
  -- Zorn's lemma to find maximal such ideal
  set S : Set (Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :=
    {A | A ≠ ⊥ ∧ Ideal.comap f A = ⊥}
  obtain ⟨A₀, hA₀ne, hA₀zero⟩ := hexists
  obtain ⟨A, -, hAmax⟩ := zorn_le_nonempty₀ S
    (fun c hcS hchain y hyc => by
      refine ⟨sSup c, ⟨?_, ?_⟩, fun z hz => le_sSup hz⟩
      · exact fun h => (hcS hyc).1 (eq_bot_iff.mpr (h ▸ le_sSup hyc))
      · rw [eq_bot_iff]
        intro r hr
        have hfr : f r ∈ sSup c := Ideal.mem_comap.mp hr
        rw [Submodule.mem_sSup_of_directed ⟨y, hyc⟩ hchain.directedOn] at hfr
        obtain ⟨J, hJc, hfr'⟩ := hfr
        have hmem : r ∈ Ideal.comap f J := Ideal.mem_comap.mpr hfr'
        rw [(hcS hJc).2] at hmem
        exact hmem)
    A₀ ⟨hA₀ne, hA₀zero⟩
  exact ⟨A, hAmax.1.1, hAmax.1.2, fun B hAB hcontra =>
    lt_irrefl A (lt_of_lt_of_le hAB
      (hAmax.2 ⟨fun h => not_lt_bot (h ▸ hAB), hcontra⟩ hAB.le))⟩

theorem isWeaklyQuasiComplete_iff_primes_meet
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] :
    IsWeaklyQuasiComplete R ↔
      ∀ (P : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R)),
        P.IsPrime → P ≠ ⊥ →
        Ideal.comap (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) P ≠ ⊥ := by
  constructor
  · intro hwqc P _ hPne
    exact wqc_implies_ideals_meet R hwqc P hPne
  · -- Contrapositive: ¬WQC gives a nonzero prime with zero contraction
    intro hprimes
    by_contra hnwqc
    obtain ⟨A, hAne, hAzero, hAmax⟩ := not_wqc_exists_maximal_zero_contraction R hnwqc
    set f := algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)
    -- A is prime: use domain property of R and maximality of A
    have hAprime : A.IsPrime := by
      constructor
      · rintro rfl
        have h1 : (1 : R) ∈ Ideal.comap f ⊤ := Ideal.mem_comap.mpr Submodule.mem_top
        rw [hAzero, Ideal.mem_bot] at h1
        exact one_ne_zero h1
      · intro x y hxy
        by_contra habs
        push Not at habs
        obtain ⟨hxna, hyna⟩ := habs
        have hAx : A < A ⊔ Ideal.span {x} := by
          apply lt_of_le_of_ne le_sup_left
          intro heq
          apply hxna
          have hsub : Ideal.span {x} ≤ A :=
            le_of_le_of_eq le_sup_right heq.symm
          exact hsub (Ideal.subset_span rfl)
        have hAy : A < A ⊔ Ideal.span {y} := by
          apply lt_of_le_of_ne le_sup_left
          intro heq
          apply hyna
          have hsub : Ideal.span {y} ≤ A :=
            le_of_le_of_eq le_sup_right heq.symm
          exact hsub (Ideal.subset_span rfl)
        have hcx := hAmax _ hAx
        have hcy := hAmax _ hAy
        rw [Submodule.ne_bot_iff] at hcx hcy
        obtain ⟨r, hr, hrne⟩ := hcx
        obtain ⟨s, hs, hsne⟩ := hcy
        have hxy_span : Ideal.span {x * y} ≤ A :=
          Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxy)
        have hmul_le : (A ⊔ Ideal.span {x}) * (A ⊔ Ideal.span {y}) ≤ A := by
          rw [Ideal.sup_mul, Ideal.mul_sup, Ideal.mul_sup]
          apply sup_le
          · apply sup_le
            · exact Ideal.mul_le_right
            · exact Ideal.mul_le_right
          · apply sup_le
            · exact Ideal.mul_le_left
            · rw [Ideal.span_singleton_mul_span_singleton]
              exact hxy_span
        have hfr : f r ∈ A ⊔ Ideal.span {x} := Ideal.mem_comap.mp hr
        have hfs : f s ∈ A ⊔ Ideal.span {y} := Ideal.mem_comap.mp hs
        have hfrs : f (r * s) ∈ A := by
          rw [map_mul]
          exact hmul_le (Ideal.mul_mem_mul hfr hfs)
        have hmem : r * s ∈ Ideal.comap f A := Ideal.mem_comap.mpr hfrs
        rw [hAzero, Ideal.mem_bot] at hmem
        exact mul_ne_zero hrne hsne hmem
    exact hprimes A hAprime hAne hAzero

/-
## Anderson Corollary 2, Part 2

A weakly quasi-complete Noetherian local domain is analytically irreducible.

Proof idea: If R̂ is not a domain, take a minimal prime P of R̂.
Then P ⊆ Z(R̂). But P ∩ R ≠ 0 (WQC), so pick 0 ≠ r ∈ P ∩ R.
Then r ∈ Z(R̂) but r ∉ Z(R) (domain), contradicting flatness of R̂ over R.
-/
theorem IsWeaklyQuasiComplete.isAnalyticallyIrreducible
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (hwqc : IsWeaklyQuasiComplete R) :
    IsAnalyticallyIrreducible R := by
  set M := IsLocalRing.maximalIdeal R
  set Rhat := AdicCompletion M R
  set f := algebraMap R Rhat
  unfold IsAnalyticallyIrreducible
  by_contra hnotdom
  have hf_inj : Function.Injective f := AdicCompletion.of_injective M R
  haveI : Nontrivial Rhat := hf_inj.nontrivial
  have hnoNZD : ¬NoZeroDivisors Rhat := fun h => hnotdom (NoZeroDivisors.to_isDomain Rhat)
  -- Every minimal prime of R̂ is nonzero (since ⊥ is not prime)
  have hP_exists : ∃ P ∈ (⊥ : Ideal Rhat).minimalPrimes, P ≠ ⊥ := by
    have hne : (⊥ : Ideal Rhat) ≠ ⊤ := bot_ne_top
    obtain ⟨⟨P, hP⟩⟩ := Ideal.nonempty_minimalPrimes hne
    refine ⟨P, hP, ?_⟩
    intro heq
    subst heq
    exact hnoNZD ⟨fun {x} {y} hxy => hP.1.1.mul_mem_iff_mem_or_mem.mp
      (show x * y ∈ (⊥ : Ideal Rhat) from Ideal.mem_bot.mpr hxy)
      |>.imp Ideal.mem_bot.mp Ideal.mem_bot.mp⟩
  obtain ⟨P, hPmin, hPne⟩ := hP_exists
  have hPprime : P.IsPrime := hPmin.1.1
  have hP_disj := Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hPmin
  have hcomap_ne : Ideal.comap f P ≠ ⊥ :=
    (isWeaklyQuasiComplete_iff_primes_meet R).mp hwqc P hPprime hPne
  obtain ⟨r, hr, hrne⟩ : ∃ r ∈ Ideal.comap f P, r ≠ (0 : R) := by
    by_contra h
    push Not at h
    exact hcomap_ne (eq_bot_iff.mpr (fun x hx => Ideal.mem_bot.mpr (h x hx)))
  have hfr_P : f r ∈ P := Ideal.mem_comap.mp hr
  have hr_nzd : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hrne
  -- Flatness of R̂ over R makes f(r) SMul-regular, hence a nonzero divisor in R̂
  haveI : Module.Flat R Rhat := AdicCompletion.flat_of_isNoetherian M
  have hfr_reg : IsSMulRegular Rhat r :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hr_nzd
  have hfr_nzd : f r ∈ nonZeroDivisors Rhat := by
    rw [mem_nonZeroDivisors_iff]
    constructor
    · intro x hx
      have h1 : r • x = 0 := by rw [Algebra.smul_def]
                                exact hx
      have h2 : r • x = r • (0 : Rhat) := by rw [h1, smul_zero]
      exact hfr_reg h2
    · intro x hx
      have h1 : r • x = 0 := by rw [Algebra.smul_def, mul_comm]
                                exact hx
      have h2 : r • x = r • (0 : Rhat) := by rw [h1, smul_zero]
      exact hfr_reg h2
  exact Set.disjoint_iff.mp hP_disj ⟨hfr_P, hfr_nzd⟩

/-
## Anderson Corollary 2, Part 3

For a 1-dimensional Noetherian local domain:
  QC ↔ WQC ↔ analytically irreducible.

We state this as two implications + the general QC → WQC.
-/
/-- Helper: in a 1-dim Noetherian local domain R with completion a domain,
every nonzero prime P of the completion has nonzero contraction to R.

Proof outline:
1. `M ≠ ⊥` (dim R = 1 implies R is not a field).
2. `M̂ = Ideal.map f M` is maximal in R̂ (via `Mhat_isMaximal`).
3. If `comap f P = ⊥`, then `f(m) ∉ P` for all nonzero `m ∈ M`, so `M̂ ⊄ P`.
4. Since M̂ is maximal and P is proper prime, this means `P ⊊ M̂`.
5. But `comap f M̂ = M ≠ ⊥`, so `⊥ < P < M̂` with `comap P = ⊥` and `comap M̂ = M`.

The final contradiction uses going-down for flat extensions
(`AdicCompletion.flat_of_isNoetherian`): `height(M̂) ≤ height(M) + dim(fiber)`.
Since `R̂/M̂ ≅ R/M` is a field, `height(M̂) ≤ 1`, but `⊥ < P < M̂` gives
`height(M̂) ≥ 2`.
-/
lemma dim1_ai_nonzero_prime_contracts
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (hdim : ringKrullDim R = 1)
    (hAI : IsAnalyticallyIrreducible R)
    (P : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (hPprime : P.IsPrime) (hPne : P ≠ ⊥) :
    Ideal.comap (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) P ≠ ⊥ := by
  let M := IsLocalRing.maximalIdeal R
  let f := algebraMap R (AdicCompletion M R)
  let Mhat := Ideal.map f M
  intro hcontra
  have hM_ne_bot : M ≠ ⊥ := by
    intro habs
    have h0 : ringKrullDim R = 0 := ringKrullDim_eq_zero_of_isField
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr habs)
    rw [h0] at hdim
    norm_num at hdim
  have hfm_notin : ∀ m ∈ M, m ≠ (0 : R) → f m ∉ P := by
    intro m _ hm habs
    apply hm
    have : m ∈ Ideal.comap (algebraMap R _) P := Ideal.mem_comap.mpr habs
    rwa [hcontra] at this
  have hMhat_not_le_P : ¬(Mhat ≤ P) := by
    intro hle
    obtain ⟨m, hm, hm_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM_ne_bot
    exact hfm_notin m hm hm_ne (hle (Ideal.mem_map_of_mem f hm))
  have hMhat_max : Mhat.IsMaximal := Mhat_isMaximal R
  have hcomap_Mhat : Ideal.comap f Mhat = M := comap_map_algebraMap_adicCompletion M
  haveI : IsLocalRing (AdicCompletion M R) := adicCompletion_isLocalRing R
  have hMhat_eq : Mhat = IsLocalRing.maximalIdeal (AdicCompletion M R) :=
    IsLocalRing.eq_maximalIdeal hMhat_max
  have hP_le_Mhat : P ≤ Mhat := by
    rw [hMhat_eq]
    exact IsLocalRing.le_maximalIdeal hPprime.ne_top
  -- Height contradiction: ⊥ ⊊ P ⊊ Mhat but height(Mhat) = height(M) = 1
  haveI : IsDomain (AdicCompletion M R) := hAI
  haveI : IsNoetherianRing (AdicCompletion M R) := adicCompletion_isNoetherianRing R
  have hP_lt_Mhat : P < Mhat :=
    lt_of_le_of_ne hP_le_Mhat (fun h => hMhat_not_le_P (h ▸ le_refl P))
  have hbot_lt_P : (⊥ : Ideal (AdicCompletion M R)) < P := bot_lt_iff_ne_bot.mpr hPne
  letI : Mhat.LiesOver M := ⟨hcomap_Mhat.symm⟩
  have hht_eq := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown M Mhat
  have hfiber_bot : Ideal.map
      (Ideal.Quotient.mk (Ideal.map (algebraMap R (AdicCompletion M R)) M))
      Mhat = ⊥ := by
    change Ideal.map (Ideal.Quotient.mk Mhat) Mhat = ⊥
    exact Ideal.map_quotient_self Mhat
  haveI : Nontrivial (AdicCompletion M R ⧸ Mhat) :=
    Ideal.Quotient.nontrivial_iff.mpr hMhat_max.ne_top
  have hfiber_ht : (Ideal.map
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap R (AdicCompletion M R)) M))
      Mhat).height = 0 := by
    rw [hfiber_bot]
    exact Ideal.height_bot
  rw [hfiber_ht, add_zero] at hht_eq
  have hM_ht : (M : Ideal R).height = 1 := by
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hdim] at this
    exact_mod_cast this
  rw [hM_ht] at hht_eq
  haveI : (⊥ : Ideal (AdicCompletion M R)).IsPrime := Ideal.isPrime_bot
  have h1 : (⊥ : Ideal (AdicCompletion M R)).height < P.height :=
    Ideal.height_strict_mono_of_isPrime hbot_lt_P
  have h2 : P.height < Mhat.height := Ideal.height_strict_mono_of_isPrime hP_lt_Mhat
  rw [Ideal.height_bot] at h1
  rw [hht_eq] at h2
  exact absurd (Order.lt_one_iff.mp h2) (ne_of_gt h1)
theorem dim1_wqc_iff_analyticallyIrreducible
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (hdim : ringKrullDim R = 1) :
    IsWeaklyQuasiComplete R ↔ IsAnalyticallyIrreducible R := by
  constructor
  · exact IsWeaklyQuasiComplete.isAnalyticallyIrreducible R
  · intro hAI
    apply (isWeaklyQuasiComplete_iff_primes_meet R).mpr
    intro P hPprime hPne
    exact dim1_ai_nonzero_prime_contracts R hdim hAI P hPprime hPne

theorem dim1_qc_iff_wqc
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (hdim : ringKrullDim R = 1) :
    IsQuasiComplete R ↔ IsWeaklyQuasiComplete R := by
  constructor
  · exact IsQuasiComplete.isWeaklyQuasiComplete R
  · intro hwqc A hA k
    set I := ⨅ n, A n with hI_def
    by_cases hI_top : I = ⊤
    · exact ⟨0, by
        rw [hI_top]
        simp⟩
    by_cases hI_bot : I = ⊥
    · obtain ⟨s, hs⟩ := hwqc A hA hI_bot k
      exact ⟨s, fun x hx => Submodule.mem_sup.mpr
        ⟨0, Submodule.zero_mem _, x, hs hx, zero_add x⟩⟩
    · -- ⨅ A ≠ ⊥, ≠ ⊤: R/I is Artinian (dim 0), so chain stabilizes mod I
      have hI_ne_bot : ∃ r ∈ I, r ≠ (0 : R) := by
        by_contra h
        push Not at h
        exact hI_bot (eq_bot_iff.mpr (fun x hx => Ideal.mem_bot.mpr (h x hx)))
      obtain ⟨r, hrI, hrne⟩ := hI_ne_bot
      have hr_nzd : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hrne
      have hle_span : Ideal.span {r} ≤ I :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrI)
      have hdim_span : ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ (1 : WithBot ℕ∞) :=
        (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr_nzd).trans (le_of_eq hdim)
      have hdim_span_le : ringKrullDim (R ⧸ Ideal.span {r}) ≤ 0 := by
        by_contra hc
        push Not at hc
        have h1 : (1 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {r}) :=
          Order.succ_le_of_lt hc
        have h3 : (1 : WithBot ℕ∞) + 1 ≤ (1 : WithBot ℕ∞) := by
          have h2 : (1 : WithBot ℕ∞) + 1 ≤ ringKrullDim (R ⧸ Ideal.span {r}) + 1 :=
            add_le_add_left h1 1
          exact h2.trans hdim_span
        norm_num at h3
      have hdim_I : ringKrullDim (R ⧸ I) ≤ 0 :=
        (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle_span)
          (Ideal.Quotient.factor_surjective hle_span)).trans hdim_span_le
      haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_top
      haveI : IsLocalRing (R ⧸ I) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      haveI : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_iff.mpr hdim_I
      haveI : IsArtinianRing (R ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
      set mk := Ideal.Quotient.mk I
      set B : ℕ → Ideal (R ⧸ I) := fun n => Ideal.map mk (A n)
      have hB_anti : Antitone B := fun _ _ hmn => Ideal.map_mono (hA hmn)
      let B' : ℕ →o (Submodule (R ⧸ I) (R ⧸ I))ᵒᵈ :=
        ⟨fun n => OrderDual.toDual (B n), fun _ _ h => hB_anti h⟩
      have hWF : WellFoundedGT (Submodule (R ⧸ I) (R ⧸ I))ᵒᵈ :=
        (wellFoundedGT_dual_iff _).mpr inferInstance
      obtain ⟨N, hN⟩ := hWF.monotone_chain_condition B'
      have hstab : ∀ m, N ≤ m → B N = B m := fun m hm => hN m hm
      have hBinf : ⨅ n, B n = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Submodule.mem_iInf] at hx
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        suffices y ∈ I by exact Ideal.Quotient.eq_zero_iff_mem.mpr this
        rw [hI_def, Submodule.mem_iInf]
        intro n
        have hyn : mk y ∈ B n := hx n
        obtain ⟨z, hz, hzy⟩ := (Ideal.mem_map_iff_of_surjective mk
          Ideal.Quotient.mk_surjective).mp hyn
        have h_diff : z - y ∈ I := Ideal.Quotient.eq.mp hzy
        have h_diff_An : z - y ∈ A n := iInf_le (A ·) n h_diff
        have := (A n).sub_mem hz h_diff_An
        rwa [sub_sub_cancel] at this
      have hBN_eq : B N = ⨅ n, B n := le_antisymm
        (le_iInf fun n => by
          rcases le_or_gt N n with hle | hlt
          · exact (hstab n hle) ▸ le_refl _
          · exact hB_anti hlt.le)
        (iInf_le _ N)
      have hBN_bot : B N = ⊥ := hBN_eq.trans hBinf
      refine ⟨N, fun x hx => ?_⟩
      have hmkx : mk x ∈ B N := Ideal.mem_map_of_mem mk hx
      rw [hBN_bot, Ideal.mem_bot] at hmkx
      have hxI : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hmkx
      exact Submodule.mem_sup.mpr ⟨x, hxI, 0, Submodule.zero_mem _, add_zero x⟩

/-
## Anderson Theorem 5, Item 3

A Noetherian local ring R is QC ↔ every homomorphic image R/I is WQC.

The forward direction is in Basic.lean (IsQuasiComplete.quotient_isWeaklyQuasiComplete).
Here we state the full iff.
-/
theorem isQuasiComplete_iff_quotients_wqc
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsQuasiComplete R ↔
      ∀ (I : Ideal R) (hI : I ≠ ⊤),
        letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
        letI : IsLocalRing (R ⧸ I) :=
          IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        IsWeaklyQuasiComplete (R ⧸ I) := by
  constructor
  · intro hqc I hI
    exact IsQuasiComplete.quotient_isWeaklyQuasiComplete R hqc I hI
  · intro hall A hA k
    set I := ⨅ n, A n
    by_cases hI_top : I = ⊤
    · exact ⟨0, by rw [hI_top]
                   simp⟩
    · letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_top
      letI : IsLocalRing (R ⧸ I) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      set mk := Ideal.Quotient.mk I
      have hmk_surj := Ideal.Quotient.mk_surjective (I := I)
      haveI : IsLocalHom mk := IsLocalHom.of_surjective mk hmk_surj
      have hM_eq : IsLocalRing.maximalIdeal (R ⧸ I) =
          Ideal.map mk (IsLocalRing.maximalIdeal R) := by
        apply le_antisymm
        · intro x hx
          obtain ⟨r, rfl⟩ := hmk_surj x
          rw [IsLocalRing.mem_maximalIdeal] at hx
          exact (Ideal.mem_map_iff_of_surjective mk hmk_surj).mpr
            ⟨r, (IsLocalRing.mem_maximalIdeal r).mpr (fun hu => hx (hu.map mk)), rfl⟩
        · intro x hx
          obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective mk hmk_surj).mp hx
          rw [IsLocalRing.mem_maximalIdeal] at hr ⊢
          exact fun hu => hr (isUnit_of_map_unit mk r hu)
      set B : ℕ → Ideal (R ⧸ I) := fun n => Ideal.map mk (A n)
      have hB_anti : Antitone B := fun _ _ hmn => Ideal.map_mono (hA hmn)
      have hBinf : ⨅ n, B n = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        simp only [Submodule.mem_iInf] at hx
        obtain ⟨r, rfl⟩ := hmk_surj x
        suffices r ∈ I by exact Ideal.Quotient.eq_zero_iff_mem.mpr this
        change r ∈ ⨅ n, A n
        rw [Submodule.mem_iInf]
        intro n
        obtain ⟨y, hy, hry⟩ := (Ideal.mem_map_iff_of_surjective mk hmk_surj).mp (hx n)
        have h_yr : y - r ∈ A n := iInf_le A n (Ideal.Quotient.eq.mp hry)
        have := (A n).sub_mem hy h_yr
        rwa [sub_sub_cancel] at this
      obtain ⟨s, hs⟩ := hall I hI_top B hB_anti hBinf k
      refine ⟨s, fun x hx => ?_⟩
      have hmkx : mk x ∈ (IsLocalRing.maximalIdeal (R ⧸ I)) ^ k :=
        hs ((Ideal.mem_map_iff_of_surjective mk hmk_surj).mpr ⟨x, hx, rfl⟩)
      rw [hM_eq, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective mk hmk_surj] at hmkx
      obtain ⟨y, hy, hxy⟩ := hmkx
      have h_mem_I : x - y ∈ I := by
        have := I.neg_mem (Ideal.Quotient.eq.mp hxy)
        rwa [neg_sub] at this
      exact Submodule.mem_sup.mpr ⟨x - y, h_mem_I, y, hy, sub_add_cancel x y⟩
