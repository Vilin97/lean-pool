/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FrenzyMath
-/
import LeanPool.AndersonConjecture.Jensen.CloseUp.CoprimeSplit
import LeanPool.AndersonConjecture.Jensen.CloseUp.Factor
import LeanPool.AndersonConjecture.Jensen.CloseUp.NoCommonFactor

/-!
# Heitmann's Lemma 4 — Closing Up Finitely Generated Ideals

Given an N-subring R and c ∈ IT for a finitely generated ideal I
of R, construct an A-extension S with c ∈ IS. The proof uses
induction on generator count with GCD complexity as a
well-founded measure (Heitmann, 1993, Lemma 4).
-/

noncomputable section

open Cardinal Ideal

variable {T : Type*} [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsDomain T]

theorem close_up_aux_wf
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T)
    (n'' : ℕ)
    (ih : ∀ (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T)
      (s : Finset R.carrier) (_ : s.card ≤ n'' + 1 + 1) (c : R.carrier)
      (_ : (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier))),
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier))) :
    ∀ (m : ℕ) (R : NSubring T)
      (_ : Cardinal.mk R.carrier < Cardinal.mk T),
      letI : IsDomain R.carrier := NSubring.isDomain R
      letI : UniqueFactorizationMonoid R.carrier := R.isUFD
      ∀ (a : R.carrier) (s : Finset R.carrier),
      gcdComplexity s ≤ m →
      s.card = n'' + 1 + 1 + 1 → a ∈ s → ∀ (c : R.carrier),
      (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier)) →
      ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih_m =>
  intro R hR_card
  haveI : IsDomain R.carrier := NSubring.isDomain R
  haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
  haveI : DecidableEq R.carrier := Classical.decEq _
  intro a
  apply wellFounded_dvdNotUnit.induction a
  intro a ih_a s hs_gcd hs_eq ha_mem c hc
  set s' := s.erase a with hs'_def
  have hs_insert : s = insert a s' := (Finset.insert_erase ha_mem).symm
  have hs'_card : s'.card ≤ n'' + 1 + 1 := by
    rw [Finset.card_erase_of_mem ha_mem, hs_eq]
    omega
  by_cases hgcd : ∃ p : R.carrier, Prime p ∧ ∀ x ∈ s', p ∣ x
  · obtain ⟨p, hp, hp_dvd⟩ := hgcd
    by_cases hpa : p ∣ a
    · -- Case p | a: divide out and recurse.
      have hp_dvd_all : ∀ x ∈ s, p ∣ x := by
        intro x hx
        rw [hs_insert, Finset.mem_insert] at hx
        rcases hx with rfl | hx'
        · exact hpa
        · exact hp_dvd x hx'
      have h_span_le : span (↑s : Set R.carrier) ≤ span {p} :=
        Ideal.span_le.mpr fun x hx =>
          Ideal.mem_span_singleton.mpr (hp_dvd_all x (Finset.mem_coe.mp hx))
      have hc_pT : (c : T) ∈ span {(p : T)} := by
        have := Ideal.map_mono h_span_le hc
        rwa [Ideal.map_span, Set.image_singleton] at this
      have hcR := close_up_dvd R p c hc_pT
      obtain ⟨c', hcc'⟩ := Ideal.mem_span_singleton.mp hcR
      classical
      let div_p : R.carrier → R.carrier := fun x =>
        if h : p ∣ x then Classical.choose h else x
      have hdiv_spec : ∀ x ∈ s, x = p * div_p x := by
        intro x hx
        simpa only [div_p, dif_pos (hp_dvd_all x hx)] using Classical.choose_spec (hp_dvd_all x hx)
      let t_set := s.image div_p
      have h_ideal_eq : span (↑s : Set R.carrier) =
          span {p} * span (↑t_set : Set R.carrier) :=
        span_eq_mul_span_image_div p s hp_dvd_all div_p hdiv_spec
      rw [h_ideal_eq, Ideal.map_mul, Ideal.map_span, Set.image_singleton] at hc
      rw [Ideal.mem_span_singleton_mul] at hc
      obtain ⟨z, hz, hpz⟩ := hc
      have hp_ne : (p : T) ≠ 0 := fun h => hp.ne_zero (Subtype.val_injective h)
      have hpc : (p : T) * (c' : T) = (c : T) := by
        have := congr_arg R.carrier.subtype hcc'
        simp only [map_mul] at this
        exact this.symm
      have hz_eq : z = (c' : T) := mul_left_cancel₀ hp_ne (hpz.trans hpc.symm)
      have hc'_mem : (c' : T) ∈ Ideal.map R.carrier.subtype
          (span (↑t_set : Set R.carrier)) := hz_eq ▸ hz
      suffices hsuff : ∃ S : NSubring T, IsAExtension R S ∧
          ∃ (hle : R.carrier ≤ S.carrier),
            (⟨(c' : T), hle c'.2⟩ : S.carrier) ∈
              Ideal.map (Subring.inclusion hle)
                (span (↑t_set : Set R.carrier)) by
        obtain ⟨S, hAext, hle, hc'_S⟩ := hsuff
        refine ⟨S, hAext, hle, ?_⟩
        rw [h_ideal_eq, Ideal.map_mul]
        have hc_eq : (⟨(c : T), hle c.2⟩ : S.carrier) =
            ⟨(p : T), hle p.2⟩ * ⟨(c' : T), hle c'.2⟩ := by
          ext
          simpa only [Subring.coe_mul] using hpc.symm
        rw [hc_eq]
        exact Ideal.mul_mem_mul
          (Ideal.mem_map_of_mem _ (Ideal.subset_span rfl)) hc'_S
      have ha'_mem : div_p a ∈ t_set :=
        Finset.mem_image.mpr ⟨a, ha_mem, rfl⟩
      by_cases ha'_zero : div_p a = 0
      · have ha_zero : a = 0 := by
          rw [hdiv_spec a ha_mem, ha'_zero, mul_zero]
        set t₀ := t_set.erase (div_p a) with ht₀_def
        have ht₀_card : t₀.card ≤ n'' + 1 + 1 := by
          have h1 : t_set.card ≤ n'' + 1 + 1 + 1 :=
            (Finset.card_image_le (f := div_p) (s := s)).trans (le_of_eq hs_eq)
          simp only [ht₀_def, Finset.card_erase_of_mem ha'_mem]
          omega
        have hspan_eq : span (↑t_set : Set R.carrier) =
            span (↑t₀ : Set R.carrier) := by
          apply le_antisymm
          · apply Ideal.span_le.mpr
            intro x hx
            rcases eq_or_ne x (div_p a) with rfl | hne
            · rw [ha'_zero]
              exact zero_mem _
            · exact Ideal.subset_span (Finset.mem_coe.mpr
                (Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hx⟩))
          · exact Ideal.span_mono (Finset.coe_subset.mpr
              (Finset.erase_subset _ _))
        have hc'_t₀ : (c' : T) ∈ Ideal.map R.carrier.subtype
            (span (↑t₀ : Set R.carrier)) := hspan_eq ▸ hc'_mem
        obtain ⟨S, hAext, hle, hmem⟩ := ih R hR_card t₀ ht₀_card c' hc'_t₀
        exact ⟨S, hAext, hle, Ideal.map_mono
          (Ideal.span_mono (Finset.coe_subset.mpr
            (Finset.erase_subset _ _))) hmem⟩
      · by_cases ha'_unit : IsUnit (div_p a)
        · refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩,
              le_refl _, ?_⟩
          have h_id : Subring.inclusion (le_refl R.carrier) =
              RingHom.id R.carrier :=
            RingHom.ext fun x => Subtype.ext rfl
          change (⟨(c' : T), le_refl R.carrier c'.2⟩ : R.carrier) ∈
            Ideal.map (Subring.inclusion (le_refl R.carrier))
              (span (↑t_set : Set R.carrier))
          rw [h_id, Ideal.map_id,
            Ideal.eq_top_of_isUnit_mem _
              (Ideal.subset_span (Finset.mem_coe.mpr ha'_mem)) ha'_unit]
          exact Submodule.mem_top
        · have hdvd : DvdNotUnit (div_p a) a :=
            ⟨ha'_zero, ⟨p, hp.not_unit,
              (hdiv_spec a ha_mem).trans (mul_comm p (div_p a))⟩⟩
          have ht_card : t_set.card = n'' + 1 + 1 + 1 := by
            have hinj : Set.InjOn div_p ↑s := fun x hx y hy hxy => by
              have hx_eq := hdiv_spec x (Finset.mem_coe.mp hx)
              have hy_eq := hdiv_spec y (Finset.mem_coe.mp hy)
              calc x = p * div_p x := hx_eq
                _ = p * div_p y := by rw [hxy]
                _ = y := hy_eq.symm
            rw [show t_set = s.image div_p from rfl,
              Finset.card_image_of_injOn hinj, hs_eq]
          have ht_gcd : gcdComplexity t_set ≤ m := le_trans (by
            change gcdComplexity t_set ≤ gcdComplexity s
            have hinj : Set.InjOn div_p ↑s := fun x hx y hy hxy => by
              have hx_eq := hdiv_spec x (Finset.mem_coe.mp hx)
              have hy_eq := hdiv_spec y (Finset.mem_coe.mp hy)
              calc x = p * div_p x := hx_eq
                _ = p * div_p y := by rw [hxy]
                _ = y := hy_eq.symm
            exact gcdComplexity_div_le p hp s hp_dvd_all div_p hdiv_spec hinj) hs_gcd
          exact ih_a (div_p a) hdvd t_set ht_gcd ht_card ha'_mem c' hc'_mem
    · by_cases hgcd_factor :
          ∃ q : R.carrier, Prime q ∧ (∀ x ∈ s', q ∣ x) ∧ (q ∣ a ∨ q ∣ c)
      · exact close_up_aux_factor hM_not_assoc hAss_ht hT_card hT_aleph0 n'' ih
          m ih_m hR_card ih_a hs_gcd hs_eq ha_mem hc s' hs'_def hs_insert hs'_card
          ⟨p, hp, hp_dvd⟩ hp hp_dvd hpa hgcd_factor
      · exact close_up_aux_b2 hM_not_assoc hAss_ht hT_card hT_aleph0 n'' ih
          m ih_m hR_card hs_gcd hs_eq ha_mem hc s' hs'_def hs_insert hs'_card
          hp hp_dvd hpa hgcd_factor
  exact close_up_aux_no_common hM_not_assoc hAss_ht hT_card hT_aleph0 n'' ih
    hR_card hs_eq ha_mem hc s' hs'_def hs_insert hs'_card hgcd

/-- Helper for close_up: induction on generator count, universally quantified over
all NSubrings R. This allows the IH to apply to A-extensions in the n≥3 case. -/
theorem close_up_aux
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T) :
    ∀ (n : ℕ) (R : NSubring T) (_ : Cardinal.mk R.carrier < Cardinal.mk T)
      (s : Finset R.carrier) (_ : s.card ≤ n) (c : R.carrier)
      (_ : (c : T) ∈ Ideal.map R.carrier.subtype (Ideal.span (↑s : Set R.carrier))),
    ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
      (⟨(c : T), hle c.2⟩ : S.carrier) ∈
        Ideal.map (Subring.inclusion hle) (Ideal.span (↑s : Set R.carrier)) := by
  intro n
  induction n with
  | zero =>
    intro R _ s hs_card c hc
    have hs_empty : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs_card)
    subst hs_empty
    simp only [Finset.coe_empty, Ideal.span_empty,
      Ideal.map_bot, Submodule.mem_bot] at hc
    exact ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _,
      by simp only [Finset.coe_empty, Ideal.span_empty,
           Ideal.map_bot, Submodule.mem_bot]
         exact Subtype.val_injective hc⟩
  | succ n ih =>
    intro R hR_card s hs_card c hc
    haveI : DecidableEq R.carrier := Classical.decEq _
    by_cases hn : s.card ≤ n
    · exact ih R hR_card s hn c hc
    · have hs_eq : s.card = n + 1 := by omega
      rcases n with _ | _ | n''
      · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs_eq
        rw [Finset.coe_singleton, Ideal.map_span, Set.image_singleton] at hc
        have hcR := close_up_dvd R a c hc
        refine ⟨R, ⟨le_refl _, fun r hr => hr, le_max_right _ _⟩, le_refl _, ?_⟩
        rw [Finset.coe_singleton, Ideal.map_span, Set.image_singleton]
        exact Ideal.mem_span_singleton.mpr (Ideal.mem_span_singleton.mp hcR)
      · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs_eq
        have hc' : (↑c : T) ∈ span {(↑a : T), (↑b : T)} := by
          rwa [Finset.coe_pair, Ideal.map_span, Set.image_pair] at hc
        obtain ⟨S, hAext, hle, hcS⟩ :=
          close_up_two_gen R a b c hc' hM_not_assoc hAss_ht hR_card hT_card
        exact ⟨S, hAext, hle, by
          rw [Finset.coe_pair, Ideal.map_span, Set.image_pair]
          exact hcS⟩
      · -- n >= 2: Heitmann general case via WF on (gcdComplexity, dvdNotUnit).
        haveI : IsDomain R.carrier := NSubring.isDomain R
        haveI : UniqueFactorizationMonoid R.carrier := R.isUFD
        have hs_ne : s.Nonempty := Finset.card_pos.mp (by omega)
        obtain ⟨a₀, ha₀_mem⟩ := hs_ne
        suffices h_wf : ∀ (m : ℕ) (R : NSubring T)
            (_ : Cardinal.mk R.carrier < Cardinal.mk T),
            letI : IsDomain R.carrier := NSubring.isDomain R
            letI : UniqueFactorizationMonoid R.carrier := R.isUFD
            ∀ (a : R.carrier) (s : Finset R.carrier),
            gcdComplexity s ≤ m →
            s.card = n'' + 1 + 1 + 1 → a ∈ s → ∀ (c : R.carrier),
            (c : T) ∈ Ideal.map R.carrier.subtype (span (↑s : Set R.carrier)) →
            ∃ S : NSubring T, IsAExtension R S ∧ ∃ (hle : R.carrier ≤ S.carrier),
              (⟨(c : T), hle c.2⟩ : S.carrier) ∈
                Ideal.map (Subring.inclusion hle) (span (↑s : Set R.carrier)) from
          h_wf (gcdComplexity s) R hR_card a₀ s le_rfl hs_eq ha₀_mem c hc
        exact close_up_aux_wf hM_not_assoc hAss_ht hT_card hT_aleph0 n'' ih

/-- Heitmann Lemma 4 (main close-up theorem):
Given N-subring R, finitely generated ideal I of R, and c ∈ R with c ∈ IT,
there exists an A-extension S of R with c ∈ IS (in S.carrier).

Proof by induction on number of generators:
- n = 1: close_up_dvd
- n = 2: close_up_two_gen
- n > 2: Heitmann general case -/
theorem close_up
    [IsAdicComplete (IsLocalRing.maximalIdeal T) T]
    (R : NSubring T)
    (I : Ideal R.carrier) (hI_fg : I.FG)
    (c : R.carrier)
    (hc : (c : T) ∈ Ideal.map R.carrier.subtype I)
    (hM_not_assoc : ∀ (r : T), r ≠ 0 →
      IsLocalRing.maximalIdeal T ∉ associatedPrimes T (T ⧸ Ideal.span {r}))
    (hAss_ht : ∀ (r : T), r ≠ 0 →
      ∀ P ∈ associatedPrimes T (T ⧸ Ideal.span {r}), P.height ≤ 1)
    (hR_card : Cardinal.mk R.carrier < Cardinal.mk T)
    (hT_card : Cardinal.mk T = Cardinal.mk (IsLocalRing.ResidueField T))
    (hT_aleph0 : Cardinal.aleph0 < Cardinal.mk T) :
    ∃ S : NSubring T,
      IsAExtension R S ∧
      ∃ (hle : R.carrier ≤ S.carrier),
        (⟨(c : T), hle c.2⟩ : S.carrier) ∈
          Ideal.map (Subring.inclusion hle) I := by
  obtain ⟨s, hs⟩ := hI_fg
  subst hs
  exact close_up_aux hM_not_assoc hAss_ht hT_card hT_aleph0 s.card R hR_card s le_rfl c hc

end
