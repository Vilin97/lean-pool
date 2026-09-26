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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.ChainReducedDef
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.CoeffLocalization
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.UniformDomain
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.FormalReduced
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AuditCleanWrappers
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyCompletionModel
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafFunctoriality
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RingEquivPresheafTransport
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalTransitivity
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafTateStructure

/-!
# Rational stable reducedness ([WP] §6.6)

Three layers:

1. **`lem:formal-series-reduced`**: `MvPowerSeries J P` over a reduced `P` is reduced,
   for an ARBITRARY index `J` — via the injection of a reduced ring into the product
   of its prime quotients, the coefficientwise product decomposition of
   `MvPowerSeries` over a product ring, and mathlib's
   `NoZeroDivisors (MvPowerSeries σ R)` (arbitrary `σ`).  Mathlib-grade statements.

2. **The descent mechanism** ([WP] thm:parity-rationally-reduced, proof): every
   rational localization `E` of `𝒜` is a `TailC0` over a head localization `P`
   (`nonempty_headModelData`); the twist element (image of `W`) is REGULAR on `P`
   because `W` is a nonzerodivisor of the head domain and the head localization is
   FLAT (Wedhorn 8.30, delivered as `prop_8_30_flat_clean_proof`); therefore the
   embedding `Φ` of `WP/Tail.lean` lands `E` in the reduced ring `ℱ_J(P)`.

3. **The head-reducedness wall** (BGR 7.3.2/10 for the heads): quarantined as the
   predicate `HeadLocsReduced`; endpoint (3) is delivered conditionally on it, and the
   predicate's own discharge is a separate sub-campaign (see
   `.mathlib-quality/wp-reduced/decomposition.md` § HRW).

"Finite iterated rational localization" is formalized by the chain recursion
`ChainReduced` (the project has no iterated-localization composition theorem; the
induction step re-applies `nonempty_headModelData` through the model transport).
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver

/-! ### `W`-regularity of head localizations ([WP] thm:parity-rationally-reduced:
"Affinoid rational localization is algebraically flat … multiplication by `W` is
injective on `P`") -/

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ)

variable {K w} in
/-- The twist element of the head model is regular: `W` is a nonzerodivisor of the
head (a domain), head localization is flat (Wedhorn 8.30,
`prop_8_30_flat_clean_proof`), and flatness preserves injectivity of multiplication
(`Module.Flat.rTensor_preserves_injective_linearMap`). -/
theorem rhoQ_regular {N : ℕ} (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational) :
    ∀ x : QHead DH, (rhoQ DH).val * x = 0 → x = 0 := by
  classical
  haveI hNoeth : IsNoetherianRing (WPHead K w N) :=
    isNoetherianRing_WPHead (w := w) (N := N) ϖ hK₀
  haveI hSN : IsStronglyNoetherian (WPHead K w N) :=
    isStronglyNoetherian_WPHead (w := w) (N := N) ϖ hK₀
  -- the restriction from the global datum is flat
  have hsub : rationalOpen DH.T DH.s ⊆
      rationalOpen (globalLocData DH.P).T (globalLocData DH.P).s := by
    rw [show (globalLocData DH.P).T = {1} from rfl,
      show (globalLocData DH.P).s = 1 from rfl, rationalOpen_singleton_one]
    exact rationalOpen_subset_spa
  letI : Algebra (presheafValue (globalLocData DH.P)) (presheafValue DH) :=
    (restrictionMapHom (globalLocData DH.P) DH hsub).toAlgebra
  haveI hflat : Module.Flat (presheafValue (globalLocData DH.P))
      (presheafValue DH) :=
    prop_8_30_flat_clean_proof (globalLocData DH.P) DH hsub
  -- `W` is regular upstairs: transport along the complete-ring equivalence
  set e0 := completeRingEquivCompletionModel (A := WPHead K w N) DH.P with he0
  have hW0 : WaHead K w N ≠ 0 := by
    intro h0
    have h1 := congrArg (fun z : WPHead K w N => ‖z‖) h0
    rw [show ‖WaHead K w N‖ = 1 from norm_WaHead, norm_zero] at h1
    linarith
  have hcW0 : (globalLocData DH.P).canonicalMap (WaHead K w N) ≠ 0 := by
    intro h0
    refine hW0 (e0.injective ?_)
    rw [map_zero]
    exact h0
  haveI hdomW : IsDomain (WPHead K w N) := inferInstance
  haveI hdom : IsDomain (presheafValue (globalLocData DH.P)) := by
    have h := Function.Injective.isDomain e0.symm.toRingHom e0.symm.injective
    exact h
  have hreg0 : IsSMulRegular (presheafValue (globalLocData DH.P))
      ((globalLocData DH.P).canonicalMap (WaHead K w N)) := by
    intro a b hab
    exact mul_left_cancel₀ hcW0 hab
  -- flat transport of regularity
  have hregS : IsSMulRegular (presheafValue DH)
      (algebraMap (presheafValue (globalLocData DH.P)) (presheafValue DH)
        ((globalLocData DH.P).canonicalMap (WaHead K w N))) :=
    hreg0.of_flat
  -- the transported element is the canonical `W`
  have hcan : algebraMap (presheafValue (globalLocData DH.P)) (presheafValue DH)
      ((globalLocData DH.P).canonicalMap (WaHead K w N)) =
      DH.canonicalMap (WaHead K w N) := by
    show restrictionMapHom (globalLocData DH.P) DH hsub
      ((globalLocData DH.P).canonicalMap (WaHead K w N)) =
      DH.canonicalMap (WaHead K w N)
    exact restrictionMapHom_canonicalMap_generic (globalLocData DH.P) DH hsub
      (WaHead K w N)
  -- transport to `QHead` along the head bridge
  intro x hx
  set e := headLocEquiv ϖ hK₀ DH hDH with he
  have hρ : (rhoQ DH).val = e (DH.canonicalMap (WaHead K w N)) := by
    rw [he, show headLocEquiv ϖ hK₀ DH hDH (DH.canonicalMap (WaHead K w N)) =
      headLocFwd ϖ DH hDH (DH.canonicalMap (WaHead K w N)) from rfl,
      show DH.canonicalMap (WaHead K w N) = DH.coeRingHom
        (algebraMap (WPHead K w N) (Localization.Away DH.s) (WaHead K w N))
        from rfl,
      headLocFwd_coe, headLocFwdAlg_algebraMap]
    rfl
  have h5 : DH.canonicalMap (WaHead K w N) * e.symm x = 0 := by
    have h6 := congrArg e.symm hx
    rw [map_mul, map_zero, hρ, RingEquiv.symm_apply_apply] at h6
    exact h6
  have h8 : e.symm x = 0 := by
    refine hregS ?_
    simp only [smul_eq_mul]
    rw [hcan, mul_zero]
    exact h5
  have h10 := congrArg e h8
  rw [RingEquiv.apply_symm_apply, map_zero] at h10
  exact h10

/-! ### The quarantined head-reducedness input (BGR 7.3.2/10) -/

/-- **The head-reducedness predicate** (the classical input BGR 7.3.2/10 at the
heads): every rational localization of every head is reduced.  [WP]
thm:parity-rationally-reduced cites: "A rational localization of a reduced affinoid
algebra is reduced [BGR, Corollary 7.3.2/10]; see also [KedlayaAWS, Remark 1.2.16].
Thus `P` is reduced."  Its discharge is a separate sub-campaign. -/
def HeadLocsReduced : Prop :=
  ∀ (N : ℕ) (DH : RationalLocData (WPHead K w N)), DH.IsRational →
    IsReduced (presheafValue DH)

/-! ### The conditional reducedness endpoints -/

variable {K w} in
/-- **Single-step reducedness** ([WP] thm:parity-rationally-reduced, single
localization): every rational localization of `𝒜` is reduced, conditionally on the
head input.  Route: finite-head model + `Φ`-embedding + `rhoQ_regular` +
`isReduced_mvPowerSeries`. -/
theorem isReduced_presheafValue_WPA (hred : HeadLocsReduced K w)
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (D : RationalLocData (WPA K w)) (hD : D.IsRational) :
    IsReduced (presheafValue D) := by
  classical
  obtain ⟨M⟩ := nonempty_headModelData ϖ hK₀ D hD
  haveI hredQ : IsReduced (QHead M.DH) := by
    haveI hP : IsReduced (presheafValue M.DH) := hred M.N M.DH M.hDH
    exact isReduced_of_injective (headLocEquiv ϖ hK₀ M.DH M.hDH).symm.toRingHom
      (headLocEquiv ϖ hK₀ M.DH M.hDH).symm.injective
  haveI hredT : IsReduced (TailC0 w M.N (QHead M.DH) (rhoQ M.DH)) := by
    refine isReduced_tailC0 w M.N _ ?_
    exact rhoQ_regular ϖ hK₀ M.DH M.hDH
  exact isReduced_of_injective M.e.toRingHom M.e.injective

/-! `ChainReduced` itself lives in `WP/ChainReducedDef.lean` (definition layer, so the
comparator challenge can state [WP] thm 6.2 (3) without importing this file's proofs). -/

universe uCRA uCRB

/-- **`ChainReduced` transports along bicontinuous ring equivalences** (the
[WP] induction's change-of-model step; 2026-07-29 ChatGPT-5.6 route review):
pull each rational datum back along `e.symm`, apply the chain hypothesis there,
and move the completed localizations across `presheafValueRingEquivOfRingEquiv`
using the valid-datum roundtrip. -/
theorem chainReduced_of_ringEquiv (n : ℕ) :
    ∀ {A : Type uCRA} {B : Type uCRB} [CommRing A] [TopologicalSpace A]
      [IsTateRing A] [CommRing B] [TopologicalSpace B] [IsTateRing B]
      (e : A ≃+* B), Continuous ⇑e → Continuous ⇑e.symm →
      ChainReduced A n → ChainReduced B n := by
  induction n with
  | zero =>
    intro A B _ _ _ _ _ _ e he he' h
    haveI : IsReduced A := h
    exact isReduced_of_injective e.symm.toRingHom e.symm.injective
  | succ n ih =>
    intro A B _ _ _ _ _ _ e he he' h
    refine ⟨?_, ?_⟩
    · haveI : IsReduced A := h.1
      exact isReduced_of_injective e.symm.toRingHom e.symm.injective
    · intro D hD
      have hDA : (D.mapRationalRingEquiv e.symm he' he hD).IsRational :=
        mapRationalRingEquiv_isRational e.symm he' he D hD
      have hchainA : ChainReduced
          (presheafValue (D.mapRationalRingEquiv e.symm he' he hD)) n :=
        h.2 (D.mapRationalRingEquiv e.symm he' he hD) hDA
      have he2 : Continuous ⇑e.symm.symm := by
        rw [RingEquiv.symm_symm]; exact he
      have h0 : (D.mapRationalRingEquiv e.symm he' he
          hD).mapRationalRingEquiv e he he' hDA = D :=
        RationalLocData.mapRationalRingEquiv_symm_map e.symm he' he2 D hD hDA
      haveI := presheafValue_isTateRing_concrete
        (D.mapRationalRingEquiv e.symm he' he hD)
      haveI := presheafValue_isTateRing_concrete D
      have key : ∀ D₂ : RationalLocData B,
          (D.mapRationalRingEquiv e.symm he' he
            hD).mapRationalRingEquiv e he he' hDA = D₂ →
          ChainReduced (presheafValue D₂) n := by
        intro D₂ h02
        cases h02
        haveI := presheafValue_isTateRing_concrete
          ((D.mapRationalRingEquiv e.symm he' he
            hD).mapRationalRingEquiv e he he' hDA)
        exact ih (presheafValueRingEquivOfRingEquiv e he he'
            (D.mapRationalRingEquiv e.symm he' he hD) hDA)
          (presheafValueRingEquivOfRingEquiv_continuous e he he'
            (D.mapRationalRingEquiv e.symm he' he hD) hDA)
          (presheafValueRingEquivOfRingEquiv_symm_continuous e he he'
            (D.mapRationalRingEquiv e.symm he' he hD) hDA)
          hchainA
      exact key D h0

variable {K w} in
/-- **Existential transitivity of rational localization at `𝒜`** ([WP] 1267–1269
"by transitivity of rational localization"; Huber Lemma 1.5(ii)–(iii) / Wedhorn
Prop 8.2(2) + Rem 8.4, existential form per the 2026-07-29 ChatGPT-5.6-sol
design): a rational localization of a rational localization of `𝒜` is
bicontinuously a single rational localization of `𝒜`. -/
theorem exists_transitivity_WPA (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (D : RationalLocData (WPA K w)) (hD : D.IsRational)
    (E : RationalLocData (presheafValue D)) (hE : E.IsRational) :
    ∃ (F : RationalLocData (WPA K w)) (_ : F.IsRational)
      (e : presheafValue E ≃+* presheafValue F),
      Continuous ⇑e ∧ Continuous ⇑e.symm := by
  classical
  haveI : HasLocLiftPowerBounded (WPA K w) := hasLocLiftPowerBounded_faithful
  exact ValuationSpectrum.exists_rationalLocalization_transitivity D hD E hE

variable {K w} in
/-- **Rational stable reducedness of `𝒜`, conditionally on the head input**
([WP] thm:rationally-reduced-example (3): "The ring `𝒜` is rationally stably
reduced").  Induction with the invariant `Qₙ := ∀ D rational,
ChainReduced (𝒪(D)) n`: the base is R3, the successor pulls a datum on `𝒪(D)`
down to `𝒜` by `exists_transitivity_WPA` and transports the chain along the
equivalence (`chainReduced_of_ringEquiv`). -/
theorem chainReduced_WPA (hred : HeadLocsReduced K w) (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) (n : ℕ) :
    ChainReduced (WPA K w) n := by
  classical
  have hQ : ∀ m : ℕ, ∀ (D : RationalLocData (WPA K w)), D.IsRational →
      ChainReduced (presheafValue D) m := by
    intro m
    induction m with
    | zero =>
      intro D hD
      exact isReduced_presheafValue_WPA hred ϖ hK₀ D hD
    | succ m ih =>
      intro D hD
      refine ⟨isReduced_presheafValue_WPA hred ϖ hK₀ D hD, ?_⟩
      intro E hE
      obtain ⟨F, hF, e, hec, hec'⟩ :=
        exists_transitivity_WPA ϖ hK₀ D hD E hE
      haveI : IsTateRing (presheafValue D) :=
        presheafValue_isTateRing_concrete D
      haveI : IsTateRing (presheafValue E) :=
        presheafValue_isTateRing_concrete E
      haveI : IsTateRing (presheafValue F) :=
        presheafValue_isTateRing_concrete F
      exact chainReduced_of_ringEquiv m e.symm hec' (by
        rw [RingEquiv.symm_symm]; exact hec) (ih F hF)
  have hred0 : IsReduced (WPA K w) := ⟨fun x hx => by
    obtain ⟨n, hn⟩ := hx
    rcases n with _ | n
    · rw [pow_zero] at hn; exact absurd hn one_ne_zero
    · exact (pow_eq_zero_iff (Nat.succ_ne_zero n)).mp hn⟩
  induction n with
  | zero => exact hred0
  | succ n _ =>
    exact ⟨hred0, fun D hD => hQ n D hD⟩

end WeightedParity
