/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Cor832
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafTateStructure
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpvAITopology

/-!
# Faithful `HasLocLiftPowerBounded` (Wedhorn 7.52, source-justified)

The faithful replacement for the two opaque `sorry`s carried by the generic
`hasLocLiftPowerBounded_of_stronglyNoetherianTate'` instance (`Presheaf.lean`): its
`isUnit_canonicalMap_s_of_tate` (T001 `spa_point_nonOpen`) and
`locLift_divByS_isPowerBounded_completion_of_tate` (bare `sorry`, Wedhorn 7.41). This file
provides, for a **complete** strongly-noetherian Tate affinoid ring, both fields of
`HasLocLiftPowerBounded` resting on exactly two source-justified Wedhorn leaves:

* **(LL-unit)** `isUnit_canonicalMap_s_faithful` — Wedhorn 7.52(2) via the pair-free complete-affinoid
  unit criterion (Lemma 7.45 / Prop 7.49 route), sorry-free.
* **(LL-bdd)** `locLift_divByS_isPowerBounded_faithful` — Wedhorn 7.52(1)/7.18, reducing to the single
  external integral criterion `isPowerBounded_of_forall_vle_one_spa_of_complete` = [Hu2] Lemma 3.3
  (cited, not reproved, in Wedhorn).

Relocated upstream of `RelativePieceKeystone` (from `WedhornCechAcyclicity`, where the decls were
defined but never wired) so the Remark-7.55 flatness chain's per-step lemmas can
`haveI := hasLocLiftPowerBounded_faithful` and route their `restrictionMapHom`-over-`presheafValue`
through the source-justified route instead of the two opaque `sorry`s. Kept a `theorem` (not an
`instance`): the `CompleteSpace`-w.r.t.-right-uniformity binder is not instance-synthesizable for a
generic base, but for a concrete completion `presheafValue D` it is discharged locally by
`presheafValue_completeSpace_rightUniformSpace`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Prop 7.52, Prop 7.18, Prop 7.49, Lemma 7.45.
* [R. Huber, *Continuous valuations*][huber1993], Lemma 3.3 (the (LL-bdd) external leaf).
-/

@[expose] public section

namespace ValuationSpectrum

open Pointwise

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **Faithful (LL-unit), Wedhorn 7.52(2) / Prop 8.2.** For `R(D'.T/D'.s) ⊆ R(D.T/D.s)`
and `A⁺ ⊆ D'.P.A₀`, the image `D'.canonicalMap D.s` is a unit in `presheafValue D'`.

Routes through the pair-free complete-affinoid unit criterion
(`isUnit_iff_forall_not_vle_zero_of_complete_pairFree`, Lemma 7.45) + the **sorry-free**
`Spa(𝒪(D')) → rationalOpen(D')` pullback (`comap_canonicalMap_mem_rationalOpen`): every Spa-point `w`
of `𝒪(D')` pulls back into `rationalOpen(D') ⊆ rationalOpen(D)`, where `D.s` does not vanish, so
`w(D'.canonicalMap D.s) ≠ 0`. The reduction is complete; it bottoms at the single source-justified
leaf Prop 7.51(2)/7.49 (`exists_spa_point_supp_eq_maxIdeal_of_complete`) carried by the unit
criterion. NO `IsDomain`, NO noeth-`A₀`, NO T001 algebraic route — this is the reviewer-recommended
faithful replacement for `isUnit_canonicalMap_s_of_huber` (whose `spa_point_nonOpen` sorry is opaque). -/
theorem isUnit_canonicalMap_s_faithful
    [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    IsUnit (D'.canonicalMap D.s) := by
  haveI hTate : IsTateRing (presheafValue D') := presheafValue_isTateRing_concrete D'
  haveI : IsHuberRing (presheafValue D') := hTate.toIsHuberRing
  haveI : T2Space (presheafValue D') := inferInstance
  haveI : NonarchimedeanRing (presheafValue D') := inferInstance
  letI P_B : PairOfDefinition (presheafValue D') := presheafValue_concretePair D'
  haveI : IsAdicComplete P_B.I P_B.A₀ := presheafValue_isAdicComplete D'
  rw [isUnit_iff_forall_not_vle_zero_of_completePair P_B (D'.canonicalMap D.s)]
  intro w hw hvle
  have hmem := comap_canonicalMap_mem_rationalOpen D' (canonicalMap_continuous D') hw
  exact (h hmem).2.2 (by simpa only [comap_vle, map_zero] using hvle)

-- The Huber [Hu2] 3.3(i) localization infrastructure (`not_isUnit_invSelf_of_not_isIntegral`,
-- `exists_comap_isEquiv_of_field_hom`, `exists_valuation_extension_of_prime_over`,
-- `exists_dominating_valuation_of_minimalPrime_le`) and the FULL-HUBER LL chain
-- (`hasLocLiftPowerBounded_huber` + instance) moved to `HuberLocLift.lean` (M8/T909):
-- they must sit UPSTREAM of `StructureSheaf.lean` so `IsSheafy` can drop its
-- `[HasLocLiftPowerBounded A]` parameter (synthesized there via the huber instance).

/-- **Integral / power-bounded criterion (Wedhorn 7.52(1) = Prop 7.18(1) = [Hu2] Lemma 3.3).**
In the complete affinoid ring `B = presheafValue D'`, an element `x` with `v(x) ≤ 1` at every
Spa point is power-bounded.

Wedhorn 7.52(1) (p. 74) states `f ∈ B⁺ ⟺ |f(x)| ≤ 1 ∀ x ∈ Spa B` (a reformulation of
Prop 7.18(1)); combined with `B⁺ ⊆ B°` (Def 7.14(1), integral elements are power-bounded) this
gives the stated criterion. Wedhorn proves 7.18(1) by citing [Hu2] Lemma 3.3 (reviewer (LL-bdd)
reply, Q-bdd-1: "all Spa valuations ≤ 1 ⇒ x ∈ B⁺ (Prop 7.18) ⇒ x ∈ B° (B⁺ ⊆ power-bounded,
Def 7.14) ⇒ power-bounded").

SOURCE NOW IN HAND (`references/huber2-continuous-valuations.pdf`, OCR `references/huber2.txt`):
**[Hu2] = R. Huber, *Continuous valuations*, Math. Z. 212 (1993), 455–477. Lemma 3.3(i), p. 466
(`huber2.txt:624-627`)**: for an f-adic ring `A`, `σ : G ↦ {v ∈ Cont A | v(g) ≤ 1 ∀ g ∈ G}` and
`τ : F ↦ {a | v(a) ≤ 1 ∀ v ∈ F}` are mutually inverse bijections between the open-integrally-closed
subrings and `𝔊_A`. The substantive direction `τ(σ(G)) = G` is **hypothesis-free** — Huber's proof
(`huber2.txt:633-658`) uses a minimal prime of `G[a⁻¹]` + a valuation ring dominating the local
ring; **NO `[IsDomain]`, NO noetherian, NO Tate**. (The noetherian hypothesis appears ONLY in
3.3(iii) = Wedhorn 7.18(3), the *density* converse, which is NOT used here.)

This is a genuine **cited external leaf** ([Hu2] 3.3(i) — not reproved in Wedhorn). The in-repo
`isIntegral_of_forall_continuous_valuation_le_one` (Presheaf.lean) is `[IsDomain]`-gated (an
artifact of its FractionRing route, false for case-(b) non-domain `presheafValue D'`) + carries a
7.22 continuity sorry, so it does NOT discharge this. Should a faithful in-repo discharge be wanted
later, formalise Huber's hypothesis-free 3.3(i) proof directly (≈25 lines + his (3.1) continuity). -/
theorem mem_plus_of_forall_spa_vle_one
    [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)]
    (D' : RationalLocData A) (x : presheafValue D')
    (hx : ∀ w : Spv (presheafValue D'),
      w ∈ Spa (presheafValue D') (presheafValue D')⁺ → w.vle x 1) :
    x ∈ (presheafValue D')⁺ := by
  -- Huber [Hu2] 3.3(i) contradiction: if `x ∉ B⁺`, construct a Spa point `w` with `w(x) > 1`,
  -- contradicting `hx`.
  by_contra hxnot
  obtain ⟨w, hw_spa, hw⟩ :
      ∃ w : Spv (presheafValue D'),
        w ∈ Spa (presheafValue D') (presheafValue D')⁺ ∧ ¬ w.vle x 1 := by
    -- HU-a (huber2.txt:635-637): `x ∉ B⁺` ⟹ `x` is NOT integral over `B⁺` (contrapositive of
    -- `B⁺` integrally closed). This is what makes `x⁻¹` a non-unit of `B⁺[x⁻¹]`, opening Huber's
    -- localization argument. (v4.33: the subtype algebra is no longer instance-automatic —
    -- registered before first use.)
    letI : Algebra ↥(presheafValue D')⁺ (presheafValue D') := (presheafValue D')⁺.subtype.toAlgebra
    have hx_not_integral : ¬ IsIntegral ((presheafValue D')⁺) x := fun hint =>
      hxnot (IsRingOfIntegralElements.isIntegrallyClosed (B := (presheafValue D')⁺) x hint)
    -- HU-b: `x⁻¹` is a non-unit of `B⁺[x⁻¹] := adjoin B⁺ {x⁻¹} ⊆ B_x := Localization.Away x`.
    have hnonunit := not_isUnit_invSelf_of_not_isIntegral (Bx := Localization.Away x) x hx_not_integral
    -- HU-b': a maximal ideal `𝔪` of `B⁺[x⁻¹]` containing `x⁻¹` (proper since `x⁻¹` is a non-unit).
    obtain ⟨𝔪, h𝔪max, h𝔪ge⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hnonunit)
    have hxinv𝔪 : (⟨IsLocalization.Away.invSelf x, Algebra.subset_adjoin (Set.mem_singleton _)⟩ :
        Algebra.adjoin ↥(presheafValue D')⁺ {(IsLocalization.Away.invSelf x : Localization.Away x)})
        ∈ 𝔪 := h𝔪ge (Ideal.mem_span_singleton_self _)
    -- HU-c (huber2.txt:644-646): a minimal prime `q ⊆ 𝔪`; the dominating valuation `s` of
    -- `R := B⁺[x⁻¹]` with `supp s = q`, `s ≤ 1` on `R` (so on `B⁺` and at `x⁻¹`), `s < 1` on `𝔪`
    -- (so `s(x⁻¹) < 1`, since `x⁻¹ ∈ 𝔪`).
    haveI : 𝔪.IsPrime := h𝔪max.isPrime
    obtain ⟨q, hq_min, hq_le⟩ := Ideal.exists_minimalPrimes_le (J := 𝔪) bot_le
    obtain ⟨Γs, _, s, hs_supp, hs_le, hs_lt⟩ :=
      exists_dominating_valuation_of_minimalPrime_le hq_min hq_le
    -- HU-d (huber2.txt:646-648): a prime `q'` of `B_x` lying over `q = supp s` (Stacks 00FK, minimal
    -- prime under the injective inclusion `R := B⁺[x⁻¹] ↪ B_x`); extend `s` to a valuation `t` of
    -- `B_x` (`exists_valuation_extension_of_prime_over`); set `v := comap (B → B_x) (ofValuation t)`.
    set Radj := Algebra.adjoin ↑(presheafValue D')⁺ {(IsLocalization.Away.invSelf x : Localization.Away x)}
      with hRadj
    letI : Algebra ↑Radj (Localization.Away x) := Radj.val.toRingHom.toAlgebra
    have hinj : Function.Injective (algebraMap ↑Radj (Localization.Away x)) := Subtype.val_injective
    obtain ⟨q', hq'prime, hq'eq⟩ :=
      Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hinj q hq_min
    haveI := hq'prime
    obtain ⟨Γt, _, t, ht_equiv⟩ := exists_valuation_extension_of_prime_over s q'
      (hq'eq.trans hs_supp.symm) (FractionRing (↑Radj ⧸ s.supp)) (FractionRing (Localization.Away x ⧸ q'))
    -- ▸ Pre-extracted facts about the comap valuation `W a := t(algebraMap a)` (Huber's properties
    --   (b)(c)(d)), for the restricted-witness continuity wiring (T-SPVAI-4).
    have hW_le : ∀ f : presheafValue D', f ∈ (presheafValue D')⁺ →
        t (algebraMap (presheafValue D') (Localization.Away x) f) ≤ 1 := by
      intro f hf
      have hg_mem : algebraMap (presheafValue D') (Localization.Away x) f ∈ Radj := by
        rw [hRadj]
        exact (Algebra.adjoin (↥(presheafValue D')⁺)
          {(IsLocalization.Away.invSelf x : Localization.Away x)}).algebraMap_mem ⟨f, hf⟩
      have hkey := (ht_equiv
        (⟨algebraMap (presheafValue D') (Localization.Away x) f, hg_mem⟩ : ↥Radj) 1).mp
        (by rw [map_one]; exact hs_le _)
      rw [Valuation.comap_apply, Valuation.comap_apply, map_one, map_one] at hkey
      exact hkey
    have ht_inv : t (IsLocalization.Away.invSelf x) < 1 := by
      rw [← not_le]
      intro hge
      have h2 : s (1 : ↑Radj) ≤
          s ⟨IsLocalization.Away.invSelf x, Algebra.subset_adjoin (Set.mem_singleton _)⟩ := by
        refine (ht_equiv 1 _).mpr ?_
        simp only [Valuation.comap_apply, map_one]
        exact hge
      rw [map_one] at h2
      exact absurd h2 (not_le.mpr (hs_lt _ hxinv𝔪))
    -- Huber's continuity argument (c): `v < 1` on topologically nilpotent elements.
    have hW_lt_AOO : ∀ a : presheafValue D', IsTopologicallyNilpotent a →
        t (algebraMap (presheafValue D') (Localization.Away x) a) < 1 := by
      intro a ha
      obtain ⟨n, hn, hn1⟩ : ∃ n : ℕ, a ^ n * x ∈ (presheafValue D')⁺ ∧ 1 ≤ n := by
        have htend : Filter.Tendsto (fun n : ℕ => a ^ n * x) Filter.atTop (nhds 0) := by
          simpa using ha.mul_const x
        have hopen : IsOpen ((presheafValue D')⁺ : Set (presheafValue D')) :=
          IsRingOfIntegralElements.isOpen
        have hev := (htend.eventually (hopen.mem_nhds (Subring.zero_mem _))).and
          (Filter.eventually_ge_atTop 1)
        exact hev.exists
      have halg : algebraMap (presheafValue D') (Localization.Away x) (a ^ n) =
          algebraMap (presheafValue D') (Localization.Away x) (a ^ n * x) *
            IsLocalization.Away.invSelf x := by
        rw [map_mul, mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
      have ht2 : t (algebraMap (presheafValue D') (Localization.Away x) (a ^ n)) < 1 := by
        rw [halg, map_mul]
        calc t (algebraMap (presheafValue D') (Localization.Away x) (a ^ n * x)) *
              t (IsLocalization.Away.invSelf x)
            ≤ 1 * t (IsLocalization.Away.invSelf x) := by gcongr; exact hW_le _ hn
          _ = t (IsLocalization.Away.invSelf x) := one_mul _
          _ < 1 := ht_inv
      rw [map_pow, map_pow] at ht2
      by_contra hge
      rw [not_lt] at hge
      exact absurd ht2 (not_lt.mpr (one_le_pow₀ hge))
    have hW_x : 1 < t (algebraMap (presheafValue D') (Localization.Away x) x) := by
      by_contra hle
      rw [not_lt] at hle
      have hprod : t (algebraMap (presheafValue D') (Localization.Away x) x) *
          t (IsLocalization.Away.invSelf x) = 1 := by
        rw [← map_mul, IsLocalization.Away.mul_invSelf, map_one]
      have hlt : t (algebraMap (presheafValue D') (Localization.Away x) x) *
          t (IsLocalization.Away.invSelf x) < 1 := by
        calc t (algebraMap (presheafValue D') (Localization.Away x) x) *
              t (IsLocalization.Away.invSelf x)
            ≤ 1 * t (IsLocalization.Away.invSelf x) := by gcongr
          _ = t (IsLocalization.Away.invSelf x) := one_mul _
          _ < 1 := ht_inv
      rw [hprod] at hlt; exact lt_irrefl 1 hlt
    -- ▸ T-SPVAI-4: the continuous Spa witness is the RESTRICTION `W | cΓ_W((π))` of
    --   `W := t.comap(algebraMap)` by the principal generator `π` (Huber's `u | cΓ`). The facts
    --   `hW_lt_AOO`/`hW_le`/`hW_x` above are Huber's properties (c)/(b)/(witness `W(x) > 1`).
    haveI hTate : IsTateRing (presheafValue D') :=
      { exists_pairOfDefinition :=
          ⟨{ A₀ := presheafValue_ringOfDef D'
             I := presheafValue_idealOfDef D'
             isOpen := presheafValue_ringOfDef_isOpen D'
             fg := presheafValue_idealOfDef_fg D'
             isAdic := presheafValue_isAdic D' }⟩
        exists_topologicallyNilpotent_unit := presheafValue_topNilUnit D' }
    set P := IsTateRing.principalPair (presheafValue D') with hP_def
    set algB := algebraMap (presheafValue D') (Localization.Away x) with halgB_def
    set g : presheafValue D' := P.toPairOfDefinition.A₀.subtype P.π with hg_def
    -- `π` is a unit (`P.π_isUnit`), so `W g = t(algB g) ≠ 0`.
    have hWg : t (algB g) ≠ 0 := by
      have hgu : IsUnit (algB g) := (P.π_isUnit).map algB
      intro h0
      obtain ⟨u, hu⟩ := hgu
      have : (1 : _) = t (algB g) * t (↑u⁻¹) := by
        rw [← map_mul, ← hu, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
      rw [h0, zero_mul] at this
      exact one_ne_zero this
    -- `W := t.comap algB`; the restricted witness `w' := ofValuation (W.restrictIdealSingle g hWg)`.
    have hWg' : (t.comap algB) g ≠ 0 := hWg
    set rs := (t.comap algB).restrictIdealSingle g hWg' with hrs_def
    -- Bridge: `(ofValuation rs).vle a b ↔ rs a ≤ rs b`.
    have hbr : ∀ a b : presheafValue D', (ValuationSpectrum.ofValuation rs).vle a b ↔ rs a ≤ rs b := by
      intro a b
      letI : ValuativeRel (presheafValue D') := (ValuationSpectrum.ofValuation rs).toValuativeRel
      haveI : rs.Compatible := Valuation.Compatible.ofValuation rs
      exact Valuation.Compatible.vle_iff_le (v := rs) a b
    -- `W a = t(algB a)` definitionally, so the `hW_*` facts are facts about `W = t.comap algB`.
    refine ⟨ValuationSpectrum.ofValuation rs, ?_, ?_⟩
    · -- HU-e(1): `w' ∈ Spa(B, B⁺)` = `w'.IsContinuous ∧ ∀ f ∈ B⁺, w'.vle f 1` (`mem_spa_iff`).
      rw [mem_spa_iff]
      refine ⟨?_, ?_⟩
      · -- **Continuity of `w' = ofValuation rs`** (Huber [Hu2] Thm 3.1 = Wedhorn Thm 7.10 reverse,
        -- huber2.txt:585: `Cont A = {v ∈ Spv(A, A°°·A) | v(a) ≤ 1 ∀ a ∈ A°°}`). Discharged by the
        -- **faithful A°°-form, principal-pair** criterion `Spv.isContinuous_of_isInSpvAI_of_lt_one_principal`
        -- (SpvAI, axiom-clean), instantiated at `P := IsTateRing.principalPair (presheafValue D')`:
        --   • `h_in`  (Huber (d), `w' ∈ Spv(B,(π))`): `ofValuation_restrictIdealSingle_isInSpvAI`
        --     (the faithful Wedhorn Def 7.3 replacement for the FALSE `ofValuation_restrictIdeal_…`,
        --     B2 2026-06-22; T-SPVAI-1/2/3, axiom-clean);
        --   • `h_le_AOO` (Huber (c), `w' ≤ 1` on `A°°`): `hW_lt_AOO` above [Huber's `aⁿ·x ∈ B⁺` step]
        --     + `restrictIdealSingle_le_one`, through the `Compatible.IsEquiv` bridge `hequiv`;
        --   • `h_lt_one` (`w'(subtype a) < 1` for `a ∈ P.I`): `a ∈` ideal-of-def ⟹ `subtype a ∈ A°°`
        --     (`isTopologicallyNilpotent_of_mem`) ⟹ `hW_lt_AOO` + `restrictIdealSingle_lt_one`.
        -- The engine reduces `I^n`-decay faithfully via `a = π^(n-1)·(πb)`, `πb ∈ A°°`
        -- (`cofinalValue_principal_pow_lt`) — needing only the `A°°` bound, NOT the over-strong `A₀`-form.
        have h_in : Spv.IsInSpvAI (ValuationSpectrum.ofValuation rs)
            (Ideal.map P.toPairOfDefinition.A₀.subtype P.toPairOfDefinition.I) := by
          rw [P.I_eq_span, Ideal.map_span, Set.image_singleton]
          exact ofValuation_restrictIdealSingle_isInSpvAI (t.comap algB) g hWg'
        letI : ValuativeRel (presheafValue D') := (ValuationSpectrum.ofValuation rs).toValuativeRel
        haveI hrsC : rs.Compatible := Valuation.Compatible.ofValuation rs
        have hequiv : (ValuativeRel.valuation (presheafValue D')).IsEquiv rs := fun a b =>
          (Valuation.Compatible.vle_iff_le
              (v := ValuativeRel.valuation (presheafValue D')) a b).symm.trans
            (Valuation.Compatible.vle_iff_le (v := rs) a b)
        have hlt : ∀ p q : presheafValue D',
            ((ValuativeRel.valuation (presheafValue D')) p < (ValuativeRel.valuation (presheafValue D')) q
              ↔ rs p < rs q) := fun p q => le_iff_le_iff_lt_iff_lt.mp (hequiv q p)
        have h_le_AOO : ∀ a : presheafValue D', IsTopologicallyNilpotent a →
            (ValuativeRel.valuation (presheafValue D')) a ≤ 1 := by
          intro a ha
          have hrs_le : rs a ≤ 1 := restrictIdealSingle_le_one hWg' (le_of_lt (hW_lt_AOO a ha))
          have hkey := (hequiv a 1).mpr (by rw [map_one]; exact hrs_le)
          rwa [map_one] at hkey
        have h_lt_one : ∀ a ∈ P.toPairOfDefinition.I,
            (ValuativeRel.valuation (presheafValue D')) (P.toPairOfDefinition.A₀.subtype a) < 1 := by
          intro a ha
          have hnilp : IsTopologicallyNilpotent (P.toPairOfDefinition.A₀.subtype a) :=
            P.toPairOfDefinition.isTopologicallyNilpotent_of_mem ha
          have hrs_lt : rs (P.toPairOfDefinition.A₀.subtype a) < 1 :=
            restrictIdealSingle_lt_one hWg' (hW_lt_AOO _ hnilp)
          have hkey := (hlt (P.toPairOfDefinition.A₀.subtype a) 1).mpr (by rw [map_one]; exact hrs_lt)
          rwa [map_one] at hkey
        exact Spv.isContinuous_of_isInSpvAI_of_lt_one_principal P.toPairOfDefinition P.I_eq_span
          (ValuationSpectrum.ofValuation rs) h_in h_le_AOO h_lt_one
      · -- `w' ≤ 1` on `B⁺` (Huber property (b)): `f ∈ B⁺` ⟹ `W f = t(algB f) ≤ 1` (`hW_le`),
        -- lifted to `rs` by `restrictIdealSingle_le_one`, then to `w'.vle` by `hbr`.
        intro f hf
        rw [hbr, map_one]
        exact restrictIdealSingle_le_one hWg' (hW_le f hf)
    · -- HU-e(2): `¬ w'.vle x 1`, i.e. `w'(x) > 1`: `1 < W x = t(algB x)` (`hW_x`, the Huber
      -- witness `s(x⁻¹) < 1` + `x⁻¹·x = 1`), lifted to `rs` by `restrictIdealSingle_one_lt`,
      -- then to `w'.vle` by `hbr`.
      intro hvle
      rw [hbr, map_one] at hvle
      exact absurd hvle (not_le.mpr (restrictIdealSingle_one_lt hWg' hW_x))
  exact hw (hx w hw_spa)

/-- **Power-bounded from Spa-boundedness (Wedhorn 7.18(1) + Def 7.14(1)).** If every continuous
valuation `w ∈ Spa(B, B⁺)` of `B = presheafValue D'` satisfies `w(x) ≤ 1`, then `x` is power-bounded.
*Proof.* By `mem_plus_of_forall_spa_vle_one` (the substantive direction of Huber [Hu2] 3.3(i) =
Wedhorn 7.18(1)), `x ∈ B⁺`; and `B⁺ ⊆ B°` (`IsRingOfIntegralElements.subset_powerBounded`,
Def 7.14(1)), so `x ∈ B° = {power-bounded}`. -/
theorem isPowerBounded_of_forall_vle_one_spa_of_complete
    [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)]
    (D' : RationalLocData A) (x : presheafValue D')
    (hx : ∀ w : Spv (presheafValue D'),
      w ∈ Spa (presheafValue D') (presheafValue D')⁺ → w.vle x 1) :
    @TopologicalRing.IsPowerBounded (presheafValue D') _ inferInstance x :=
  IsRingOfIntegralElements.subset_powerBounded (mem_plus_of_forall_spa_vle_one D' x hx)

/-- **Faithful (LL-bdd), Wedhorn 7.52(1)/7.18 + Prop 8.2.** For `R(D'.T/D'.s) ⊆ R(D.T/D.s)`,
`A⁺ ⊆ D'.P.A₀`, and `t ∈ D.T`, the localization lift of `t/D.s` is power-bounded in the
completion `presheafValue D'`.

Faithful reduction (reviewer (LL-bdd) Q-bdd-1) to the single external criterion
`isPowerBounded_of_forall_vle_one_spa_of_complete`: every Spa point `w` of `O_X(D')` pulls back
(`comap_canonicalMap_mem_rationalOpen`) into `rationalOpen(D') ⊆ rationalOpen(D)`, where
`w(t) ≤ w(D.s)` (`t ∈ D.T`); the lift `x` satisfies `x · canMap(D.s) = canMap(t)` and `canMap(D.s)`
is a unit, so `w(x) ≤ 1`. NO `IsDomain`, NO noeth-`A₀`. The sorry-free (modulo the one external
[Hu2]-3.3 leaf) faithful replacement for `locLift_divByS_isPowerBounded_completion_of_tate`
(Presheaf.lean, bare `sorry`). -/
theorem locLift_divByS_isPowerBounded_faithful
    [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (t : A) (ht : t ∈ D.T) :
    @TopologicalRing.IsPowerBounded (presheafValue D') _ inferInstance
      (IsLocalization.Away.lift D.s (isUnit_canonicalMap_s_faithful D D' h)
        (divByS t D.s)) := by
  set hu := isUnit_canonicalMap_s_faithful D D' h with hu_def
  set x := IsLocalization.Away.lift D.s hu (divByS t D.s) with hx_def
  apply isPowerBounded_of_forall_vle_one_spa_of_complete D' x
  intro w hw
  -- Pull back: `comap w ∈ rationalOpen D' ⊆ rationalOpen D`, giving `w(t) ≤ w(D.s)`.
  have hmem := comap_canonicalMap_mem_rationalOpen D' (canonicalMap_continuous D') hw
  have hvle0 : (comap D'.canonicalMap w).vle t D.s := (h hmem).2.1 t ht
  rw [comap_vle] at hvle0
  -- Lift spec: `x · D'.canonicalMap D.s = D'.canonicalMap t`.
  have hspec_alg : divByS t D.s * algebraMap A (Localization.Away D.s) D.s =
      algebraMap A (Localization.Away D.s) t :=
    IsLocalization.mk'_spec _ t ⟨D.s, Submonoid.mem_powers D.s⟩
  have hspec : x * D'.canonicalMap D.s = D'.canonicalMap t := by
    have e1 : x * IsLocalization.Away.lift D.s hu
          (algebraMap A (Localization.Away D.s) D.s) =
        IsLocalization.Away.lift D.s hu (algebraMap A (Localization.Away D.s) t) := by
      rw [hx_def, ← map_mul, hspec_alg]
    rwa [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq] at e1
  -- Cancel the unit `D'.canonicalMap D.s` to get `w(x) ≤ 1`.
  rw [← hspec] at hvle0
  -- `hvle0 : w.vle (x * D'.canonicalMap D.s) (D'.canonicalMap D.s)`.
  obtain ⟨cinv, hcinv⟩ := hu.exists_right_inv
  have hmul := w.mul_vle_mul_left hvle0 cinv
  rwa [mul_assoc, hcinv, mul_one] at hmul

/-- **Faithful `HasLocLiftPowerBounded` (Wedhorn 7.52 + Prop 8.2).** For a complete strongly
noetherian Tate affinoid ring, both fields of `HasLocLiftPowerBounded` hold faithfully:

* **(LL-unit)** `isUnit_canonicalMap_s_faithful` (Wedhorn 7.52(2), sorry-free): `D.s` is a unit in
  the completion `O_X(D')` because it has no zero on `Spa(O_X(D'))`.
* **(LL-bdd)** `locLift_divByS_isPowerBounded_faithful` (Wedhorn 7.52(1)/7.18): each lift `t/D.s`
  has `v ≤ 1` on `Spa(O_X(D'))`, hence is power-bounded — modulo the single external integral
  criterion [Hu2] Lemma 3.3 (`isPowerBounded_of_forall_vle_one_spa_of_complete`).

**Pair-free** — `[CompatiblePlusSubring A]` is GONE (the (LL-unit) now routes through the pair-free
7.52(2) `isUnit_iff_forall_not_vle_zero_of_complete_pairFree`, Wedhorn's actual 7.51 route). This is
the faithful replacement for `hasLocLiftPowerBounded_of_stronglyNoetherianTate'` (Presheaf.lean),
whose `isUnit_canonicalMap_s_of_tate` carries the T001 `spa_point_nonOpen` sorry and whose
`locLift_divByS_isPowerBounded_completion_of_tate` is a bare `sorry`: this version replaces BOTH
opaque sorries by exactly two source-justified Wedhorn leaves — the pair-free Prop 7.51(2)
`exists_spa_point_supp_eq_maxIdeal_of_complete` (Prop 7.49 route) and [Hu2] 3.3.

Crucially this needs NO `[CompatiblePlusSubring (presheafValue D)]` (false-in-general for
completions), so it APPLIES to `B = presheafValue D`: callers `haveI := hasLocLiftPowerBounded_faithful`
(supplying `CompleteSpace` via `presheafValue_completeSpace_rightUniformSpace`) to shadow the
sorry-bearing Presheaf instance. Kept a `theorem` (not `instance`): the `CompleteSpace`-w.r.t.-
right-uniformity binder is not instance-synthesizable. -/
theorem hasLocLiftPowerBounded_faithful
    [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] :
    HasLocLiftPowerBounded A where
  isUnit_canonicalMap_s := fun D D' h => isUnit_canonicalMap_s_faithful D D' h
  locLift_divByS_isPowerBounded := fun D D' h t ht =>
    locLift_divByS_isPowerBounded_faithful D D' h t ht

/-- **Instance form of the faithful LL package** (2026-07-03, post carrier-#3/#5 discharge:
the faithful chain is axiom-clean). Priority above the sorry-carrying
`hasLocLiftPowerBounded_of_stronglyNoetherianTate` delegation chain
(StructureSheaf → Presheaf primed instance), so contexts that carry the
right-uniformity `CompleteSpace` binder — the whole Wedhorn-8.28(b) bundle — synthesize
the PROVEN package instead of the sorried one. The `CompleteSpace`-w.r.t.-`letI` binder
is exactly the shape those bundles carry, so synthesis fires there and nowhere else. -/
instance (priority := 1100) hasLocLiftPowerBounded_faithful_instance
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] :
    HasLocLiftPowerBounded A :=
  hasLocLiftPowerBounded_faithful

-- (full-Huber chain lives in HuberLocLift.lean)
end ValuationSpectrum
