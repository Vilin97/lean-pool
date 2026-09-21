/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.TateInstances
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.StrictLocalization
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.UniformDomain
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.Chart
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetFunctoriality

/-!
# Functoriality layer over a CDVF base: pushing rational data along the square, graph
bridges, and `HasLocLiftPowerBounded 𝓐`

Sources: [FJP] Lemma 1.1 (graph realization of rational localization — the universal
property), Lemma 4.6 (naturality), Lemma 5.1 (naturality on the rational basis), ported to
the generic base stack of the CDVF campaign (crosswalk D9) from
`FiniteJetFunctoriality.lean`. The pseudouniformizer bundle of each vertex is
ϖ-parametric (`piA ϖ`, …), so every pair of definition, pushed datum and
noetherianity-consuming statement takes the layer-1 data `(ϖ : Uniformizer K)` — and
`hK₀ : IsNoetherianRing (unitBall K)` where a noetherian pod enters. The generic helper
lemmas of the Laurent original (`span_image_eq_top`, the ultrametric-quotient and
nonarchimedean instances, `isPowerBounded_of_norm_le_one`, `gaussNorm_X_le_one`,
`span_mul_image_eq_top`, `span_insert_eq_top`) are base-field-free and are reused from it
directly.

This file supplies the covariant layer over `K`:

* pairs of definition for the four rings (unit balls with the pseudouniformizer ideal);
* `pushDatumB/C/D : RationalLocData 𝓐 → RationalLocData E` (image datum);
* `presheafValueMap : 𝒪_𝓐(D) → 𝒪_E(D_E)` (localization functoriality + completion), and
  its naturality with `restrictionMap`;
* the **graph bridge** `𝒪_E(D) ≃+* P_E ⧸ I_E` ([FJP] Lemma 1.1 + (4.21)), topological in
  both directions, for `E = 𝓐` and forward halves at the three vertices;
* pushed coverings, intersection data, and the Spa-point coverage transfer;
* `HasLocLiftPowerBounded` for all four rings (the faithful pair-free discharger applies
  once the Tate structure is supplied by `ϖ`).
-/

open Filter Topology

-- v4.33 (file-wide): the closed-ideal quotient-norm chains through the `PA`/`locA`
-- defs (`Submodule.Quotient.normedAddCommGroup`, `locA_t2`, `locA_completeSpace`, …)
-- are used in a dozen declarations here and their instance unification needs
-- semireducible unfolding; restore pre-v4.33 defeq behaviour for this FJP-internal
-- file (established bump-repair pattern, cf. `Over/StrictLocalization.lean` and the
-- Laurent original — reconfirmed necessary at the abstract base `K`).

namespace FiniteJetOver

open FiniteJet
open FiniteJet.RestrictedLaurent
open FiniteJet.GraphKoszul
open ValuationSpectrum
open FiniteJetOver.StrictLoc

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

noncomputable section

open scoped Classical

/-! ### Pairs of definition -/

/-- The unit-ball pair of definition of 𝓑 (the generic `unitBallPod` at `piB ϖ`;
the 𝓐-version `podA` lives in `Over/Chart.lean`). -/
def podB (ϖ : Uniformizer K) : PairOfDefinition (JetB K) :=
  unitBallPod (piB ϖ) (isUnit_piB ϖ) (by rw [norm_piB]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piB]; exact ϖ.norm_val_pos) (norm_piB_mul ϖ)

def podC (ϖ : Uniformizer K) : PairOfDefinition (JetC K) :=
  unitBallPod (piC ϖ) (isUnit_piC ϖ) (by rw [norm_piC]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piC]; exact ϖ.norm_val_pos) (norm_piC_mul ϖ)

def podD (ϖ : Uniformizer K) : PairOfDefinition (JetD K) :=
  unitBallPod (piD ϖ) (isUnit_piD ϖ) (by rw [norm_piD]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piD]; exact ϖ.norm_val_pos) (norm_piD_mul ϖ)

/-! ### The Huber/Tate structure of the four rings is uniformizer-free

Moved to `Over/TateInstances.lean` so that `Comparator/Challenge.lean` can state the
general-base conclusions without importing this file (whose closure contains
`Over/Chart.lean`, and so the proof of `not_isStablyUniform_JetA`). Re-exported here by
the import above, so downstream consumers are unaffected. -/


/-! ### Pushing rational localization data ([FJP] Lemma 5.1)

The `hopen` field for the pushed datum is the generic bounded-denominator statement for
span-⊤ data over a principal pair of definition in a Tate ring; the spanning-set image
lemma `FiniteJet.span_image_eq_top` is reused from the Laurent original. -/

variable {K}
variable (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))

/-- Push a rational datum of 𝓐 to 𝓑 (image datum, [FJP] Lemma 5.1). -/
def pushDatumB (D : RationalLocData (JetA K)) (hD : D.IsRational) :
    RationalLocData (JetB K) where
  P := podB K ϖ
  T := D.T.image (jB K)
  s := jB K D.s
  hopen := genPiece_hopen (podB K ϖ) (D.T.image (jB K)) (jB K D.s)
    (span_image_eq_top (jB K) hD.span_eq_top)

/-- Push a rational datum of 𝓐 to 𝓒. -/
def pushDatumC (D : RationalLocData (JetA K)) (hD : D.IsRational) :
    RationalLocData (JetC K) where
  P := podC K ϖ
  T := D.T.image (iotaC K)
  s := iotaC K D.s
  hopen := genPiece_hopen (podC K ϖ) (D.T.image (iotaC K)) (iotaC K D.s)
    (span_image_eq_top (iotaC K) hD.span_eq_top)

/-- Push a rational datum of 𝓐 to 𝓓. -/
def pushDatumD (D : RationalLocData (JetA K)) (hD : D.IsRational) :
    RationalLocData (JetD K) where
  P := podD K ϖ
  T := D.T.image ((rhoC K).comp (iotaC K))
  s := rhoC K (iotaC K D.s)
  hopen := genPiece_hopen (podD K ϖ) (D.T.image ((rhoC K).comp (iotaC K)))
    (rhoC K (iotaC K D.s))
    (span_image_eq_top ((rhoC K).comp (iotaC K)) hD.span_eq_top)

theorem pushDatumB_isRational {D : RationalLocData (JetA K)} (hD : D.IsRational) :
    (pushDatumB ϖ D hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_eq_top (jB K) hD.span_eq_top)

theorem pushDatumC_isRational {D : RationalLocData (JetA K)} (hD : D.IsRational) :
    (pushDatumC ϖ D hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_eq_top (iotaC K) hD.span_eq_top)

theorem pushDatumD_isRational {D : RationalLocData (JetA K)} (hD : D.IsRational) :
    (pushDatumD ϖ D hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_eq_top ((rhoC K).comp (iotaC K)) hD.span_eq_top)

/-! ### Continuity of the square's maps (norm bounds ⇒ 1-Lipschitz) -/

theorem continuous_jB : Continuous (jB K) :=
  AddMonoidHomClass.continuous_of_bound (jB K) 1 fun a => by
    rw [one_mul]; exact norm_jB_le K a

theorem continuous_iotaC : Continuous (iotaC K) :=
  AddMonoidHomClass.continuous_of_bound (iotaC K) 1 fun a => by
    rw [one_mul, norm_iotaC]

theorem continuous_rhoC : Continuous (rhoC K) :=
  AddMonoidHomClass.continuous_of_bound (rhoC K) 1 fun a => by
    rw [one_mul]; exact norm_rhoC_le K a

/-- The induced map on completed rational localizations along `ιC` ([FJP] Lemma 5.1's
`𝒪_X(U) → 𝒪_{Y_C}(U_C)`; built from `IsLocalization` functoriality, continuity for the
localization topologies, and `UniformSpace.Completion` functoriality). -/
noncomputable def presheafValueMapC (D : RationalLocData (JetA K)) (hD : D.IsRational) :
    presheafValue D →+* presheafValue (pushDatumC ϖ D hD) :=
  presheafValueMapOfHom (iotaC K) (continuous_iotaC) D (pushDatumC ϖ D hD) rfl
    (fun _ ht => Finset.mem_image_of_mem _ ht)

noncomputable def presheafValueMapB (D : RationalLocData (JetA K)) (hD : D.IsRational) :
    presheafValue D →+* presheafValue (pushDatumB ϖ D hD) :=
  presheafValueMapOfHom (jB K) (continuous_jB) D (pushDatumB ϖ D hD) rfl
    (fun _ ht => Finset.mem_image_of_mem _ ht)

noncomputable def presheafValueMapD (D : RationalLocData (JetA K)) (hD : D.IsRational) :
    presheafValue D →+* presheafValue (pushDatumD ϖ D hD) :=
  presheafValueMapOfHom ((rhoC K).comp (iotaC K))
    (by rw [RingHom.coe_comp]; exact (continuous_rhoC).comp (continuous_iotaC))
    D (pushDatumD ϖ D hD) rfl (fun _ ht => Finset.mem_image_of_mem _ ht)

theorem presheafValueMapC_continuous (D : RationalLocData (JetA K)) (hD : D.IsRational) :
    Continuous (presheafValueMapC ϖ D hD) :=
  presheafValueMapOfHom_continuous _ _ _ _ _ _

theorem presheafValueMapB_continuous (D : RationalLocData (JetA K)) (hD : D.IsRational) :
    Continuous (presheafValueMapB ϖ D hD) :=
  presheafValueMapOfHom_continuous _ _ _ _ _ _

theorem presheafValueMapC_canonicalMap (D : RationalLocData (JetA K)) (hD : D.IsRational)
    (a : JetA K) :
    presheafValueMapC ϖ D hD (D.canonicalMap a) =
      (pushDatumC ϖ D hD).canonicalMap (iotaC K a) :=
  presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ a

theorem presheafValueMapB_canonicalMap (D : RationalLocData (JetA K)) (hD : D.IsRational)
    (a : JetA K) :
    presheafValueMapB ϖ D hD (D.canonicalMap a) =
      (pushDatumB ϖ D hD).canonicalMap (jB K a) :=
  presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ a

/-! ### The graph bridge ([FJP] Lemma 1.1 + (4.21))

For an indexed enumeration `(g, f)` of a rational datum `(T, s)` (with `g = s`), the
project's completed rational localization is topologically the Banach graph quotient. -/

/-- An indexed enumeration of a `RationalLocData`: `f` lists `T`, `g = s`. -/
structure DatumEnum (D : RationalLocData (JetA K)) where
  /-- The arity. -/
  m : ℕ
  /-- The enumeration of `T`. -/
  f : Fin m → JetA K
  /-- Enumeration covers `T`. -/
  hf : ∀ t ∈ D.T, ∃ i, f i = t
  /-- Enumeration lands in `T`. -/
  hf' : ∀ i, f i ∈ D.T

/-- The canonical enumeration of a rational datum (via `Finset.equivFin`). -/
noncomputable def datumEnum (D : RationalLocData (JetA K)) : DatumEnum D where
  m := D.T.card
  f := fun i => (D.T.equivFin.symm i : JetA K)
  hf := fun t ht => ⟨D.T.equivFin ⟨t, ht⟩, by rw [Equiv.symm_apply_apply]⟩
  hf' := fun i => (D.T.equivFin.symm i).2

section GraphBridgeInfra

variable (D : RationalLocData (JetA K)) (e : DatumEnum D)

/-- The enumerated datum spans `({s} ∪ range f) = ⊤` (rationality + covering). -/
theorem DatumEnum.span_eq_top (hD : D.IsRational) :
    Ideal.span ({D.s} ∪ Set.range e.f) = ⊤ := by
  rw [← top_le_iff, ← hD.span_eq_top]
  refine Ideal.span_mono fun t ht => ?_
  obtain ⟨i, rfl⟩ := e.hf t ht
  exact Set.mem_union_right _ ⟨i, rfl⟩

/-- Scalars into `P_𝓐` (constant restricted series). -/
noncomputable def bridgeConst (m : ℕ) : JetA K →+* PA K m :=
  polyToP.comp MvPolynomial.C

/-- The base map `𝓐 → 𝓐_α = P_𝓐 ⧸ I_𝓐` (constants, then the graph quotient). -/
noncomputable def bridgeBase : JetA K →+* locA K e.m D.s e.f :=
  (Ideal.Quotient.mk (IA K e.m D.s e.f)).comp (bridgeConst e.m)

/-- The variable images `X̄ᵢ ∈ 𝓐_α`. -/
noncomputable def bridgeX (i : Fin e.m) : locA K e.m D.s e.f :=
  Ideal.Quotient.mk (IA K e.m D.s e.f) (polyToP (MvPolynomial.X i))

/-- The graph relation in the quotient: `s̄ · X̄ᵢ = f̄ᵢ` ([FJP] (4.6)). -/
theorem bridgeBase_s_mul_X (i : Fin e.m) :
    bridgeBase D e D.s * bridgeX D e i = bridgeBase D e (e.f i) := by
  have hmem : polyToP (MvPolynomial.C D.s) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (e.f i)) ∈ IA K e.m D.s e.f := by
    have hrw : rA K e.m D.s e.f i =
        polyToP (MvPolynomial.C D.s) * polyToP (MvPolynomial.X i) -
          polyToP (MvPolynomial.C (e.f i)) := by
      rw [rA, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (IA K e.m D.s e.f) (polyToP (MvPolynomial.C D.s)) *
      Ideal.Quotient.mk (IA K e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (IA K e.m D.s e.f) (polyToP (MvPolynomial.C (e.f i)))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (IA K e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

/-- `s̄` is a unit in `𝓐_α` ([FJP] (4.3): the span decomposition
`1 = c·s + Σ dᵢ·fᵢ` becomes `1 = s̄·(c̄ + Σ d̄ᵢ X̄ᵢ)` after the graph relations). -/
theorem isUnit_bridgeBase_s (hD : D.IsRational) : IsUnit (bridgeBase D e D.s) := by
  have h1 : (1 : JetA K) ∈ Ideal.span ({D.s} ∪ Set.range e.f) := by
    rw [e.span_eq_top D hD]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBase D e (d i * e.f i) =
      bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) := fun i => by
    rw [RingHom.map_mul (bridgeBase D e), bridgeBase_s_mul_X]
  have happ : bridgeBase D e c * bridgeBase D e D.s +
      ∑ i, bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) = 1 := by
    have h0 := congrArg (bridgeBase D e) hxy
    rw [RingHom.map_one (bridgeBase D e), RingHom.map_add (bridgeBase D e),
      RingHom.map_mul (bridgeBase D e),
      show (bridgeBase D e) (∑ i, d i * e.f i) = ∑ i, bridgeBase D e (d i * e.f i) from
        map_sum (bridgeBase D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBase D e D.s *
      (bridgeBase D e c + ∑ i, bridgeBase D e (d i) * bridgeX D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBase D e D.s * bridgeBase D e c +
        ∑ i, bridgeBase D e D.s * (bridgeBase D e (d i) * bridgeX D e i)
        = bridgeBase D e c * bridgeBase D e D.s +
          ∑ i, bridgeBase D e (d i) * (bridgeBase D e D.s * bridgeX D e i) := by
          rw [mul_comm (bridgeBase D e D.s) (bridgeBase D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

/-- `‖X̄ᵢ‖ ≤ 1` in the graph quotient. -/
theorem norm_bridgeX_le_one (i : Fin e.m) : ‖bridgeX D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact gaussNorm_X_le_one (S := JetA K) i

/-- `bridgeBase` is norm-nonincreasing (constants keep their norm, quotients contract). -/
theorem norm_bridgeBase_le (a : JetA K) : ‖bridgeBase D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := JetA K) (m := e.m) (MvPolynomial.C a) : PA K e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := JetA K) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetA K) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The loc-level forward map `A_s → 𝓐_α` (`IsLocalization.Away.lift` at the unit `s̄`). -/
noncomputable def bridgeLocHom (hD : D.IsRational) :
    Localization.Away D.s →+* locA K e.m D.s e.f :=
  IsLocalization.Away.lift D.s (isUnit_bridgeBase_s D e hD)

theorem bridgeLocHom_algebraMap (hD : D.IsRational) (a : JetA K) :
    bridgeLocHom D e hD (algebraMap (JetA K) (Localization.Away D.s) a) =
      bridgeBase D e a :=
  IsLocalization.Away.lift_eq _ _ a

/-- The forward map sends the rational generator `fᵢ/s` to the variable `X̄ᵢ`. -/
theorem bridgeLocHom_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHom D e hD (divByS (e.f i) D.s) = bridgeX D e i := by
  have hu := isUnit_bridgeBase_s D e hD
  have hspec : divByS (e.f i) D.s * algebraMap (JetA K) (Localization.Away D.s) D.s =
      algebraMap (JetA K) (Localization.Away D.s) (e.f i) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHom D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHom D e hD), bridgeLocHom_algebraMap,
    bridgeLocHom_algebraMap, ← bridgeBase_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBase D e D.s) (bridgeLocHom D e hD (divByS (e.f i) D.s))]
  exact happ

/-- Continuity of the loc-level forward map (universal property; the generators map to
the norm-≤-1 variables `X̄ᵢ`, which are power-bounded). -/
theorem bridgeLocHom_continuous (hD : D.IsRational) :
    @Continuous _ _ D.topology _ (bridgeLocHom D e hD) := by
  refine locTopology_continuous_lift D.P D.T D.s D.hopen _ ?_ ?_
  · have h_eq : (bridgeLocHom D e hD).comp
        (algebraMap (JetA K) (Localization.Away D.s)) = bridgeBase D e := by
      ext a; exact bridgeLocHom_algebraMap D e hD a
    rw [show ⇑((bridgeLocHom D e hD).comp
        (algebraMap (JetA K) (Localization.Away D.s)))
        = ⇑(bridgeBase D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBase D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBase_le D e a
  · intro t ht
    obtain ⟨i, rfl⟩ := e.hf t ht
    rw [bridgeLocHom_divByS]
    exact isPowerBounded_of_norm_le_one (norm_bridgeX_le_one D e i)

/-- Forward: `𝒪_𝓐(D) → 𝓐_α` (completion extension of the localization lift;
the target is complete Hausdorff since `I_𝓐` is closed, [FJP] (4.21)). -/
noncomputable def bridgeFwd (hD : D.IsRational) :
    presheafValue D →+* locA K e.m D.s e.f := by
  haveI hcl : IsClosed ((IA K e.m D.s e.f : Set (PA K e.m))) :=
    isClosed_IA K e.m D.s e.f ϖ hK₀ (e.span_eq_top D hD)
  haveI : NormedAddCommGroup (locA K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  haveI : T2Space (locA K e.m D.s e.f) :=
    locA_t2 K e.m D.s e.f ϖ hK₀ (e.span_eq_top D hD)
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (bridgeLocHom D e hD)
    (bridgeLocHom_continuous D e hD)

theorem bridgeFwd_coe (hD : D.IsRational) (a : Localization.Away D.s) :
    bridgeFwd ϖ hK₀ D e hD (D.coeRingHom a) = bridgeLocHom D e hD a := by
  haveI hcl : IsClosed ((IA K e.m D.s e.f : Set (PA K e.m))) :=
    isClosed_IA K e.m D.s e.f ϖ hK₀ (e.span_eq_top D hD)
  haveI : NormedAddCommGroup (locA K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  haveI : T2Space (locA K e.m D.s e.f) :=
    locA_t2 K e.m D.s e.f ϖ hK₀ (e.span_eq_top D hD)
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (bridgeLocHom D e hD)
    (bridgeLocHom_continuous D e hD) a

theorem bridgeFwd_canonicalMap (hD : D.IsRational) (a : JetA K) :
    bridgeFwd ϖ hK₀ D e hD (D.canonicalMap a) = bridgeBase D e a := by
  rw [show D.canonicalMap a =
      D.coeRingHom (algebraMap (JetA K) (Localization.Away D.s) a) from rfl,
    bridgeFwd_coe, bridgeLocHom_algebraMap]

theorem bridgeFwd_continuous (hD : D.IsRational) :
    Continuous (bridgeFwd ϖ hK₀ D e hD) := by
  letI := D.uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-! #### The reverse direction: evaluation `P_𝓐 → 𝒪_𝓐(D)` ([FJP] Lemma 1.1, bound (1.3)) -/

/-- Norm-decay restricted series are topologically restricted (the two restricted power
series notions agree over a normed base). -/
noncomputable def bridgeToRestricted (m : ℕ) :
    PA K m →+* ↥(restrictedMvPowerSeriesSubring m (JetA K)) where
  toFun p := ⟨p.1, by
    have hp : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) p.1 := p.2
    rw [MvPowerSeries.IsRestrictedGauss] at hp
    have hprod : ∀ t : Fin m →₀ ℕ, (t.prod fun _ k => (1 : ℝ) ^ k) = 1 := fun t => by simp
    simp only [hprod, mul_one] at hp
    show Filter.Tendsto (fun t : Fin m →₀ ℕ => MvPowerSeries.coeff t p.1)
      Filter.cofinite (nhds 0)
    rwa [tendsto_zero_iff_norm_tendsto_zero]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The rational generators `fᵢ/s ∈ 𝒪_𝓐(D)`. -/
noncomputable def bridgeGen (i : Fin e.m) : presheafValue D :=
  D.coeRingHom (divByS (e.f i) D.s)

/-- Each generator is power-bounded (its powers lie in the image of the bounded
`locSubring`). -/
theorem bridgeGen_isBounded (i : Fin e.m) :
    TopologicalRing.IsBounded (Set.range (bridgeGen D e i ^ · : ℕ → presheafValue D)) := by
  have hmem : divByS (e.f i) D.s ∈ locSubring D.P D.T D.s :=
    divByS_mem_locSubring D.P D.T D.s (e.hf' i)
  have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded D
  apply hbdd.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨divByS (e.f i) D.s ^ n, pow_mem hmem n, by
    rw [map_pow]; rfl⟩

/-- The evaluation `P_𝓐 →+* 𝒪_𝓐(D)`: `Σ a_v X^v ↦ Σ ρ(a_v)·(f/s)^v`
(convergent by [FJP] (1.3); built on the project's `mvEvalHomBounded`). -/
noncomputable def bridgeEval : PA K e.m →+* presheafValue D :=
  (mvEvalHomBounded D.canonicalMap (canonicalMap_continuous D)
    (bridgeGen D e) (bridgeGen_isBounded D e)).comp (bridgeToRestricted e.m)

theorem bridgeEval_const (a : JetA K) :
    bridgeEval D e (polyToP (MvPolynomial.C a)) = D.canonicalMap a := by
  have hcast : bridgeToRestricted (K := K) e.m (polyToP (MvPolynomial.C a)) =
      algebraMap (JetA K) ↥(restrictedMvPowerSeriesSubring e.m (JetA K)) a := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetA K) (m := e.m) (MvPolynomial.C a)).1 :
      MvPowerSeries (Fin e.m) (JetA K)) = _
    rw [show (polyToP (E := JetA K) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetA K) a from MvPolynomial.coe_C a]
    rfl
  rw [bridgeEval, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_algebraMap _ _ _ _ a

theorem bridgeEval_X (i : Fin e.m) :
    bridgeEval D e (polyToP (MvPolynomial.X i)) = bridgeGen D e i := by
  have hcast : bridgeToRestricted (K := K) e.m (polyToP (MvPolynomial.X i)) =
      ⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetA K) (m := e.m) (MvPolynomial.X i)).1 :
      MvPowerSeries (Fin e.m) (JetA K)) = _
    exact MvPolynomial.coe_X i
  rw [bridgeEval, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_X _ _ _ _ i

/-- The evaluation kills the graph ideal (`s·(fᵢ/s) = fᵢ` in the localization). -/
theorem IA_le_ker_bridgeEval : IA K e.m D.s e.f ≤ RingHom.ker (bridgeEval D e) := by
  rw [IA, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  have hval : bridgeEval D e (rA K e.m D.s e.f i) =
      D.canonicalMap D.s * bridgeGen D e i - D.canonicalMap (e.f i) :=
    (map_sub ((bridgeEval D e).comp polyToP)
        (MvPolynomial.C D.s * MvPolynomial.X i) (MvPolynomial.C (e.f i))).trans
      (congrArg₂ (· - ·)
        ((map_mul ((bridgeEval D e).comp polyToP)
            (MvPolynomial.C D.s) (MvPolynomial.X i)).trans
          (congrArg₂ (· * ·) (bridgeEval_const D e D.s) (bridgeEval_X D e i)))
        (bridgeEval_const D e (e.f i)))
  rw [hval, sub_eq_zero, bridgeGen]
  rw [show D.canonicalMap D.s = D.coeRingHom (algebraMap (JetA K)
      (Localization.Away D.s) D.s) from rfl, ← RingHom.map_mul D.coeRingHom,
    show algebraMap (JetA K) (Localization.Away D.s) D.s * divByS (e.f i) D.s =
      algebraMap (JetA K) (Localization.Away D.s) (e.f i) from by
    rw [mul_comm, divByS, IsLocalization.mk'_spec]]
  rfl

/-- Reverse: `𝓐_α → 𝒪_𝓐(D)` (the evaluation factors through the graph quotient). -/
noncomputable def bridgeRev : locA K e.m D.s e.f →+* presheafValue D :=
  Ideal.Quotient.lift (IA K e.m D.s e.f) (bridgeEval D e)
    (fun _ ha => RingHom.mem_ker.mp (IA_le_ker_bridgeEval D e ha))

theorem bridgeRev_mk (p : PA K e.m) :
    bridgeRev D e (Ideal.Quotient.mk (IA K e.m D.s e.f) p) = bridgeEval D e p := rfl

theorem bridgeRev_bridgeBase (a : JetA K) :
    bridgeRev D e (bridgeBase D e a) = D.canonicalMap a :=
  bridgeEval_const D e a

theorem bridgeRev_bridgeX (i : Fin e.m) :
    bridgeRev D e (bridgeX D e i) = bridgeGen D e i :=
  bridgeEval_X D e i

/-- Sums of open-subgroup members stay in the subgroup (local copy of the private
Wedhorn828 helper). -/
private theorem tsum_mem_of_isOpen_addSubgroup' {ι G₀ : Type*} [AddCommGroup G₀]
    [TopologicalSpace G₀] [IsTopologicalAddGroup G₀] {f : ι → G₀}
    (hf : Summable f) {G : AddSubgroup G₀} (hG : IsOpen (G : Set G₀))
    (hmem : ∀ i, f i ∈ G) : ∑' i, f i ∈ G := by
  have hclosed : IsClosed (G : Set G₀) := AddSubgroup.isClosed_of_isOpen G hG
  refine hclosed.mem_of_tendsto hf.hasSum (Filter.Eventually.of_forall ?_)
  intro s
  exact G.sum_mem fun i _ => hmem i

/-- The range of the generator product powers is bounded (local copy of the private
Wedhorn828 helper, at our tuple). -/
private theorem bridgeRangeProd_isBounded :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i, bridgeGen D e i ^ (v i))) := by
  classical
  suffices h : ∀ s : Finset (Fin e.m), TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i ∈ s, bridgeGen D e i ^ (v i))) from
    h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty => simpa using TopologicalRing.isBounded_singleton (1 : presheafValue D)
  | insert a s ha ih =>
      refine ((bridgeGen_isBounded D e a).mul ih).subset ?_
      rintro _ ⟨v, rfl⟩
      change ∏ i ∈ insert a s, bridgeGen D e i ^ (v i) ∈ _
      rw [Finset.prod_insert ha]
      exact Set.mul_mem_mul ⟨v a, rfl⟩ ⟨v, rfl⟩

/-- **Continuity of the evaluation** from the norm topology on `P_𝓐` ([FJP] (1.3) bound;
mirrors `mvEvalHomBounded_continuous` with the Gauss-norm ball basis in place of the
Tate-algebra basis: coefficients of a small series are small). -/
theorem bridgeEval_continuous : Continuous (bridgeEval D e) := by
  classical
  refine continuous_of_continuousAt_zero (bridgeEval D e).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  obtain ⟨V, hV, hVR⟩ := bridgeRangeProd_isBounded D e (W : Set (presheafValue D))
    (W.isOpen.mem_nhds W.zero_mem)
  have hpre : D.canonicalMap ⁻¹' V ∈ nhds (0 : JetA K) :=
    (canonicalMap_continuous D).continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : PA K e.m) hδ) ?_
  intro p hp
  rw [Metric.mem_ball, dist_zero_right] at hp
  apply hWU
  change (∑' v, mvEvalTerm D.canonicalMap (bridgeGen D e)
    (bridgeToRestricted e.m p) v) ∈ (W : Set (presheafValue D))
  refine tsum_mem_of_isOpen_addSubgroup'
    (mvEvalTerm_summable D.canonicalMap (canonicalMap_continuous D)
      (bridgeGen D e) (bridgeGen_isBounded D e) (bridgeToRestricted e.m p))
    W.isOpen fun v => ?_
  have hcoeff : ‖MvPowerSeries.coeff v p.1‖ < δ :=
    lt_of_le_of_lt (norm_coeff_le_gauss p v) hp
  have hVmem : D.canonicalMap (MvPowerSeries.coeff v p.1) ∈ V :=
    hball (by rwa [Metric.mem_ball, dist_zero_right])
  change mvEvalTerm D.canonicalMap (bridgeGen D e) (bridgeToRestricted e.m p) v ∈ W
  rw [show mvEvalTerm D.canonicalMap (bridgeGen D e) (bridgeToRestricted e.m p) v =
      (∏ i, bridgeGen D e i ^ (v i)) *
        D.canonicalMap (MvPowerSeries.coeff v p.1) from by
    rw [mvEvalTerm]; exact mul_comm _ _]
  exact hVR (Set.mul_mem_mul ⟨v, rfl⟩ hVmem)

/-- Continuity of the reverse map (the graph quotient carries the quotient topology). -/
theorem bridgeRev_continuous : Continuous (bridgeRev D e) := by
  rw [(QuotientRing.isOpenQuotientMap_mk (IA K e.m D.s e.f)).isQuotientMap.continuous_iff]
  exact bridgeEval_continuous D e

/-! #### Round trips (density + Hausdorff equalizers) -/

/-- Polynomials are dense in `P_𝓐` (truncate below any coefficient-norm level). -/
theorem polyToP_denseRange (m : ℕ) :
    DenseRange (polyToP : MvPolynomial (Fin m) (JetA K) → PA K m) := by
  classical
  rw [Metric.denseRange_iff]
  intro p ε hε
  refine ⟨∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
    MvPolynomial.monomial s (MvPowerSeries.coeff s p.1), ?_⟩
  rw [dist_eq_norm, MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine lt_of_le_of_lt (Real.iSup_le (fun s => ?_) (half_pos hε).le) (half_lt_self hε)
  rw [finsupp_prod_one, mul_one]
  show ‖MvPowerSeries.coeff s ((p - polyToP _ : PA K m)).1‖ ≤ ε / 2
  rw [show ((p - polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1)) : PA K m)).1 =
    p.1 - (polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1) : MvPolynomial (Fin m)
        (JetA K))).1 from rfl, map_sub, coeff_polyToP, MvPolynomial.coeff_sum]
  by_cases hs : ε / 2 ≤ ‖MvPowerSeries.coeff s p.1‖
  · rw [Finset.sum_eq_single s
      (fun b _ hb => by rw [MvPolynomial.coeff_monomial, if_neg hb])
      (fun hns => absurd ((finite_setOf_le_norm_coeff p (half_pos hε)).mem_toFinset.mpr hs)
        hns), MvPolynomial.coeff_monomial, if_pos rfl, sub_self, norm_zero]
    exact (half_pos hε).le
  · rw [Finset.sum_eq_zero fun b hb => ?_, sub_zero]
    · exact (not_le.mp hs).le
    · rw [MvPolynomial.coeff_monomial, if_neg]
      intro hbs
      rw [hbs] at hb
      exact hs ((finite_setOf_le_norm_coeff p (half_pos hε)).mem_toFinset.mp hb)

/-- `rev ∘ fwd = id` on `𝒪_𝓐(D)` (agreement on the dense localization image; both
composites with `algebraMap` are `canonicalMap`, so the localization universal property
applies, then extend by density to the completion). -/
theorem bridgeRev_bridgeFwd (hD : D.IsRational) (x : presheafValue D) :
    bridgeRev D e (bridgeFwd ϖ hK₀ D e hD x) = x := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : RegularSpace (presheafValue D) := UniformSpace.to_regularSpace
  have hcomp : (bridgeRev D e).comp (bridgeLocHom D e hD) = D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [bridgeLocHom_algebraMap, bridgeRev_bridgeBase]
    rfl
  have hdense : DenseRange (D.coeRingHom :
      Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have hagree : (fun y => bridgeRev D e (bridgeFwd ϖ hK₀ D e hD y)) ∘ D.coeRingHom =
      (fun y => y) ∘ (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    funext a
    show bridgeRev D e (bridgeFwd ϖ hK₀ D e hD (D.coeRingHom a)) = D.coeRingHom a
    rw [bridgeFwd_coe]
    exact DFunLike.congr_fun hcomp a
  have h_eq : (fun y => bridgeRev D e (bridgeFwd ϖ hK₀ D e hD y)) = fun y => y :=
    hdense.equalizer ((bridgeRev_continuous D e).comp (bridgeFwd_continuous ϖ hK₀ D e hD))
      continuous_id hagree
  exact congrFun h_eq x

/-- The graph-quotient projection is continuous (`1`-Lipschitz for the quotient norm). -/
theorem mkIA_continuous :
    Continuous (Ideal.Quotient.mk (IA K e.m D.s e.f)) :=
  AddMonoidHomClass.continuous_of_bound (Ideal.Quotient.mk (IA K e.m D.s e.f)) 1
    fun a => by rw [one_mul]; exact Ideal.Quotient.norm_mk_le _ a

/-- `fwd ∘ rev = id` on `𝓐_α` (agreement on constants and variables, hence on the dense
polynomial image; extend by density to the Banach quotient). -/
theorem bridgeFwd_bridgeRev (hD : D.IsRational) (y : locA K e.m D.s e.f) :
    bridgeFwd ϖ hK₀ D e hD (bridgeRev D e y) = y := by
  haveI hcl : IsClosed ((IA K e.m D.s e.f : Set (PA K e.m))) :=
    isClosed_IA K e.m D.s e.f ϖ hK₀ (e.span_eq_top D hD)
  haveI : NormedAddCommGroup (locA K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  haveI : T2Space (locA K e.m D.s e.f) :=
    locA_t2 K e.m D.s e.f ϖ hK₀ (e.span_eq_top D hD)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmkcont : Continuous (Ideal.Quotient.mk (IA K e.m D.s e.f)) :=
    mkIA_continuous D e
  have hpoly : ∀ q : MvPolynomial (Fin e.m) (JetA K),
      bridgeFwd ϖ hK₀ D e hD (bridgeEval D e (polyToP q)) =
        Ideal.Quotient.mk (IA K e.m D.s e.f) (polyToP q) := by
    have hhomeq : ((bridgeFwd ϖ hK₀ D e hD).comp ((bridgeEval D e).comp polyToP)) =
        (Ideal.Quotient.mk (IA K e.m D.s e.f)).comp
          (polyToP : MvPolynomial (Fin e.m) (JetA K) →+* PA K e.m) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · show bridgeFwd ϖ hK₀ D e hD (bridgeEval D e (polyToP (MvPolynomial.C a))) =
          Ideal.Quotient.mk (IA K e.m D.s e.f) (polyToP (MvPolynomial.C a))
        rw [bridgeEval_const, bridgeFwd_canonicalMap]
        rfl
      · show bridgeFwd ϖ hK₀ D e hD (bridgeEval D e (polyToP (MvPolynomial.X i))) =
          Ideal.Quotient.mk (IA K e.m D.s e.f) (polyToP (MvPolynomial.X i))
        rw [bridgeEval_X, bridgeGen, bridgeFwd_coe, bridgeLocHom_divByS]
        rfl
    intro q
    exact DFunLike.congr_fun hhomeq q
  have h_eq : (fun z : PA K e.m => bridgeFwd ϖ hK₀ D e hD (bridgeEval D e z)) =
      fun z : PA K e.m => Ideal.Quotient.mk (IA K e.m D.s e.f) z := by
    refine (polyToP_denseRange e.m).equalizer
      ((bridgeFwd_continuous ϖ hK₀ D e hD).comp (bridgeEval_continuous D e)) hmkcont ?_
    funext q
    exact hpoly q
  exact congrFun h_eq p

/-! #### The 𝓒-side forward bridge (for the [FJP] Lemma 5.1 naturality square) -/

/-- The base map `𝓒 → 𝓒_α` (constants into the 𝓒-graph quotient). -/
noncomputable def bridgeBaseC : JetC K →+* locC K e.m D.s e.f :=
  (Ideal.Quotient.mk (IC K e.m D.s e.f)).comp
    ((polyToP : MvPolynomial (Fin e.m) (JetC K) →+* PC K e.m).comp MvPolynomial.C)

/-- The variable images `X̄ᵢ ∈ 𝓒_α`. -/
noncomputable def bridgeXC (i : Fin e.m) : locC K e.m D.s e.f :=
  Ideal.Quotient.mk (IC K e.m D.s e.f) (polyToP (MvPolynomial.X i))

theorem bridgeBaseC_s_mul_X (i : Fin e.m) :
    bridgeBaseC D e (iotaC K D.s) * bridgeXC D e i =
      bridgeBaseC D e (iotaC K (e.f i)) := by
  have hmem : polyToP (MvPolynomial.C (iotaC K D.s)) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (iotaC K (e.f i))) ∈ IC K e.m D.s e.f := by
    have hrw : rC K e.m D.s e.f i = polyToP (MvPolynomial.C (iotaC K D.s)) *
        polyToP (MvPolynomial.X i) - polyToP (MvPolynomial.C (iotaC K (e.f i))) := by
      rw [rC_eq, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (IC K e.m D.s e.f) (polyToP (MvPolynomial.C (iotaC K D.s))) *
      Ideal.Quotient.mk (IC K e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (IC K e.m D.s e.f) (polyToP (MvPolynomial.C (iotaC K (e.f i))))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (IC K e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

theorem isUnit_bridgeBaseC_s (hD : D.IsRational) :
    IsUnit (bridgeBaseC D e (iotaC K D.s)) := by
  have h1 : (1 : JetC K) ∈
      Ideal.span ({iotaC K D.s} ∪ Set.range fun i => iotaC K (e.f i)) := by
    rw [span_pushed_C K e.m D.s e.f (e.span_eq_top D hD)]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBaseC D e (d i * iotaC K (e.f i)) =
      bridgeBaseC D e (d i) * (bridgeBaseC D e (iotaC K D.s) * bridgeXC D e i) :=
    fun i => by rw [RingHom.map_mul (bridgeBaseC D e), bridgeBaseC_s_mul_X]
  have happ : bridgeBaseC D e c * bridgeBaseC D e (iotaC K D.s) +
      ∑ i, bridgeBaseC D e (d i) * (bridgeBaseC D e (iotaC K D.s) * bridgeXC D e i) = 1 := by
    have h0 := congrArg (bridgeBaseC D e) hxy
    rw [RingHom.map_one (bridgeBaseC D e), RingHom.map_add (bridgeBaseC D e),
      RingHom.map_mul (bridgeBaseC D e),
      show (bridgeBaseC D e) (∑ i, d i * iotaC K (e.f i)) =
        ∑ i, bridgeBaseC D e (d i * iotaC K (e.f i)) from map_sum (bridgeBaseC D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBaseC D e (iotaC K D.s) *
      (bridgeBaseC D e c + ∑ i, bridgeBaseC D e (d i) * bridgeXC D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBaseC D e (iotaC K D.s) * bridgeBaseC D e c +
        ∑ i, bridgeBaseC D e (iotaC K D.s) * (bridgeBaseC D e (d i) * bridgeXC D e i)
        = bridgeBaseC D e c * bridgeBaseC D e (iotaC K D.s) +
          ∑ i, bridgeBaseC D e (d i) * (bridgeBaseC D e (iotaC K D.s) * bridgeXC D e i) := by
          rw [mul_comm (bridgeBaseC D e (iotaC K D.s)) (bridgeBaseC D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

theorem norm_bridgeXC_le_one (i : Fin e.m) : ‖bridgeXC D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact gaussNorm_X_le_one (S := JetC K) i

theorem norm_bridgeBaseC_le (a : JetC K) : ‖bridgeBaseC D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := JetC K) (m := e.m) (MvPolynomial.C a) : PC K e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := JetC K) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetC K) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The 𝓒-side localization lift. -/
noncomputable def bridgeLocHomC (hD : D.IsRational) :
    Localization.Away (pushDatumC ϖ D hD).s →+* locC K e.m D.s e.f :=
  IsLocalization.Away.lift (pushDatumC ϖ D hD).s (isUnit_bridgeBaseC_s D e hD)

theorem bridgeLocHomC_algebraMap (hD : D.IsRational) (a : JetC K) :
    bridgeLocHomC ϖ D e hD
      (algebraMap (JetC K) (Localization.Away (pushDatumC ϖ D hD).s) a) =
      bridgeBaseC D e a :=
  IsLocalization.Away.lift_eq _ _ a

theorem bridgeLocHomC_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHomC ϖ D e hD (divByS (iotaC K (e.f i)) (pushDatumC ϖ D hD).s) =
      bridgeXC D e i := by
  have hu := isUnit_bridgeBaseC_s D e hD
  have hspec : divByS (iotaC K (e.f i)) (pushDatumC ϖ D hD).s *
      algebraMap (JetC K) (Localization.Away (pushDatumC ϖ D hD).s) (pushDatumC ϖ D hD).s =
      algebraMap (JetC K) (Localization.Away (pushDatumC ϖ D hD).s) (iotaC K (e.f i)) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHomC ϖ D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHomC ϖ D e hD), bridgeLocHomC_algebraMap,
    bridgeLocHomC_algebraMap, ← bridgeBaseC_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBaseC D e (iotaC K D.s))
    (bridgeLocHomC ϖ D e hD (divByS (iotaC K (e.f i)) (pushDatumC ϖ D hD).s))]
  exact happ

theorem bridgeLocHomC_continuous (hD : D.IsRational) :
    @Continuous _ _ (pushDatumC ϖ D hD).topology _ (bridgeLocHomC ϖ D e hD) := by
  refine locTopology_continuous_lift (pushDatumC ϖ D hD).P (pushDatumC ϖ D hD).T
    (pushDatumC ϖ D hD).s (pushDatumC ϖ D hD).hopen _ ?_ ?_
  · have h_eq : (bridgeLocHomC ϖ D e hD).comp
        (algebraMap (JetC K) (Localization.Away (pushDatumC ϖ D hD).s)) =
        bridgeBaseC D e := by
      ext a; exact bridgeLocHomC_algebraMap ϖ D e hD a
    rw [show ⇑((bridgeLocHomC ϖ D e hD).comp
        (algebraMap (JetC K) (Localization.Away (pushDatumC ϖ D hD).s)))
        = ⇑(bridgeBaseC D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBaseC D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBaseC_le D e a
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, rfl⟩ := e.hf t₀ ht₀
    rw [bridgeLocHomC_divByS]
    exact isPowerBounded_of_norm_le_one (norm_bridgeXC_le_one D e i)

include ϖ hK₀ in
/-- `I_𝓒` is closed (noetherian-ball route, as in `isClosed_IA`'s vertex inputs). -/
theorem isClosed_IC' : IsClosed ((IC K e.m D.s e.f : Set (PC K e.m))) := by
  haveI := isNoetherianRing_PC K e.m ϖ hK₀
  exact isClosed_graphIdeal (piC ϖ) (isUnit_piC ϖ)
    (by rw [norm_piC]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piC]; exact ϖ.norm_val_pos)
    (norm_piC_mul ϖ) (isNoetherianRing_unitBall_PC K e.m ϖ hK₀) (rC K e.m D.s e.f)

/-- The 𝓒-side forward bridge `𝒪_𝓒(D_C) → 𝓒_α`. -/
noncomputable def bridgeFwdC (hD : D.IsRational) :
    presheafValue (pushDatumC ϖ D hD) →+* locC K e.m D.s e.f := by
  haveI hcl : IsClosed ((IC K e.m D.s e.f : Set (PC K e.m))) := isClosed_IC' ϖ hK₀ D e
  haveI : NormedAddCommGroup (locC K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumC ϖ D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumC ϖ D hD).s) :=
    (pushDatumC ϖ D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumC ϖ D hD).s) :=
    (pushDatumC ϖ D hD).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (bridgeLocHomC ϖ D e hD)
    (bridgeLocHomC_continuous ϖ D e hD)

theorem bridgeFwdC_coe (hD : D.IsRational) (a : Localization.Away (pushDatumC ϖ D hD).s) :
    bridgeFwdC ϖ hK₀ D e hD ((pushDatumC ϖ D hD).coeRingHom a) =
      bridgeLocHomC ϖ D e hD a := by
  haveI hcl : IsClosed ((IC K e.m D.s e.f : Set (PC K e.m))) := isClosed_IC' ϖ hK₀ D e
  haveI : NormedAddCommGroup (locC K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumC ϖ D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumC ϖ D hD).s) :=
    (pushDatumC ϖ D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumC ϖ D hD).s) :=
    (pushDatumC ϖ D hD).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (bridgeLocHomC ϖ D e hD)
    (bridgeLocHomC_continuous ϖ D e hD) a

theorem bridgeFwdC_continuous (hD : D.IsRational) :
    Continuous (bridgeFwdC ϖ hK₀ D e hD) := by
  letI := (pushDatumC ϖ D hD).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-! #### The 𝓑-side forward bridge (mirror of the 𝓒 block, consumed by the transfer) -/

/-- The base map `𝓑 → 𝓑_α`. -/
noncomputable def bridgeBaseB : JetB K →+* locB K e.m D.s e.f :=
  (Ideal.Quotient.mk (IB K e.m D.s e.f)).comp
    ((polyToP : MvPolynomial (Fin e.m) (JetB K) →+* PB K e.m).comp MvPolynomial.C)

/-- The variable images `X̄ᵢ ∈ 𝓑_α`. -/
noncomputable def bridgeXB (i : Fin e.m) : locB K e.m D.s e.f :=
  Ideal.Quotient.mk (IB K e.m D.s e.f) (polyToP (MvPolynomial.X i))

theorem bridgeBaseB_s_mul_X (i : Fin e.m) :
    bridgeBaseB D e (jB K D.s) * bridgeXB D e i =
      bridgeBaseB D e (jB K (e.f i)) := by
  have hmem : polyToP (MvPolynomial.C (jB K D.s)) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (jB K (e.f i))) ∈ IB K e.m D.s e.f := by
    have hrw : rB K e.m D.s e.f i = polyToP (MvPolynomial.C (jB K D.s)) *
        polyToP (MvPolynomial.X i) - polyToP (MvPolynomial.C (jB K (e.f i))) := by
      rw [rB_eq, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (IB K e.m D.s e.f) (polyToP (MvPolynomial.C (jB K D.s))) *
      Ideal.Quotient.mk (IB K e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (IB K e.m D.s e.f) (polyToP (MvPolynomial.C (jB K (e.f i))))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (IB K e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

theorem isUnit_bridgeBaseB_s (hD : D.IsRational) :
    IsUnit (bridgeBaseB D e (jB K D.s)) := by
  have h1 : (1 : JetB K) ∈
      Ideal.span ({jB K D.s} ∪ Set.range fun i => jB K (e.f i)) := by
    rw [span_pushed_B K e.m D.s e.f (e.span_eq_top D hD)]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBaseB D e (d i * jB K (e.f i)) =
      bridgeBaseB D e (d i) * (bridgeBaseB D e (jB K D.s) * bridgeXB D e i) :=
    fun i => by rw [RingHom.map_mul (bridgeBaseB D e), bridgeBaseB_s_mul_X]
  have happ : bridgeBaseB D e c * bridgeBaseB D e (jB K D.s) +
      ∑ i, bridgeBaseB D e (d i) * (bridgeBaseB D e (jB K D.s) * bridgeXB D e i) = 1 := by
    have h0 := congrArg (bridgeBaseB D e) hxy
    rw [RingHom.map_one (bridgeBaseB D e), RingHom.map_add (bridgeBaseB D e),
      RingHom.map_mul (bridgeBaseB D e),
      show (bridgeBaseB D e) (∑ i, d i * jB K (e.f i)) =
        ∑ i, bridgeBaseB D e (d i * jB K (e.f i)) from map_sum (bridgeBaseB D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBaseB D e (jB K D.s) *
      (bridgeBaseB D e c + ∑ i, bridgeBaseB D e (d i) * bridgeXB D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBaseB D e (jB K D.s) * bridgeBaseB D e c +
        ∑ i, bridgeBaseB D e (jB K D.s) * (bridgeBaseB D e (d i) * bridgeXB D e i)
        = bridgeBaseB D e c * bridgeBaseB D e (jB K D.s) +
          ∑ i, bridgeBaseB D e (d i) * (bridgeBaseB D e (jB K D.s) * bridgeXB D e i) := by
          rw [mul_comm (bridgeBaseB D e (jB K D.s)) (bridgeBaseB D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

theorem norm_bridgeXB_le_one (i : Fin e.m) : ‖bridgeXB D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact gaussNorm_X_le_one (S := JetB K) i

theorem norm_bridgeBaseB_le (a : JetB K) : ‖bridgeBaseB D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := JetB K) (m := e.m) (MvPolynomial.C a) : PB K e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := JetB K) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetB K) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The 𝓑-side localization lift. -/
noncomputable def bridgeLocHomB (hD : D.IsRational) :
    Localization.Away (pushDatumB ϖ D hD).s →+* locB K e.m D.s e.f :=
  IsLocalization.Away.lift (pushDatumB ϖ D hD).s (isUnit_bridgeBaseB_s D e hD)

theorem bridgeLocHomB_algebraMap (hD : D.IsRational) (a : JetB K) :
    bridgeLocHomB ϖ D e hD
      (algebraMap (JetB K) (Localization.Away (pushDatumB ϖ D hD).s) a) =
      bridgeBaseB D e a :=
  IsLocalization.Away.lift_eq _ _ a

theorem bridgeLocHomB_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHomB ϖ D e hD (divByS (jB K (e.f i)) (pushDatumB ϖ D hD).s) =
      bridgeXB D e i := by
  have hu := isUnit_bridgeBaseB_s D e hD
  have hspec : divByS (jB K (e.f i)) (pushDatumB ϖ D hD).s *
      algebraMap (JetB K) (Localization.Away (pushDatumB ϖ D hD).s) (pushDatumB ϖ D hD).s =
      algebraMap (JetB K) (Localization.Away (pushDatumB ϖ D hD).s) (jB K (e.f i)) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHomB ϖ D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHomB ϖ D e hD), bridgeLocHomB_algebraMap,
    bridgeLocHomB_algebraMap, ← bridgeBaseB_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBaseB D e (jB K D.s))
    (bridgeLocHomB ϖ D e hD (divByS (jB K (e.f i)) (pushDatumB ϖ D hD).s))]
  exact happ

theorem bridgeLocHomB_continuous (hD : D.IsRational) :
    @Continuous _ _ (pushDatumB ϖ D hD).topology _ (bridgeLocHomB ϖ D e hD) := by
  refine locTopology_continuous_lift (pushDatumB ϖ D hD).P (pushDatumB ϖ D hD).T
    (pushDatumB ϖ D hD).s (pushDatumB ϖ D hD).hopen _ ?_ ?_
  · have h_eq : (bridgeLocHomB ϖ D e hD).comp
        (algebraMap (JetB K) (Localization.Away (pushDatumB ϖ D hD).s)) =
        bridgeBaseB D e := by
      refine RingHom.ext fun a => ?_
      show bridgeLocHomB ϖ D e hD
        (algebraMap (JetB K) (Localization.Away (pushDatumB ϖ D hD).s) a) =
        bridgeBaseB D e a
      exact bridgeLocHomB_algebraMap ϖ D e hD a
    rw [show ⇑((bridgeLocHomB ϖ D e hD).comp
        (algebraMap (JetB K) (Localization.Away (pushDatumB ϖ D hD).s)))
        = ⇑(bridgeBaseB D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBaseB D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBaseB_le D e a
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, rfl⟩ := e.hf t₀ ht₀
    rw [bridgeLocHomB_divByS]
    exact isPowerBounded_of_norm_le_one (norm_bridgeXB_le_one D e i)

include ϖ hK₀ in
/-- `I_𝓑` is closed (noetherian-ball route). -/
theorem isClosed_IB' : IsClosed ((IB K e.m D.s e.f : Set (PB K e.m))) := by
  haveI := isNoetherianRing_PB K e.m ϖ hK₀
  exact isClosed_graphIdeal (piB ϖ) (isUnit_piB ϖ)
    (by rw [norm_piB]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piB]; exact ϖ.norm_val_pos)
    (norm_piB_mul ϖ) (isNoetherianRing_unitBall_PB K e.m ϖ hK₀) (rB K e.m D.s e.f)

/-- The 𝓑-side forward bridge `𝒪_𝓑(D_B) → 𝓑_α`. -/
noncomputable def bridgeFwdB (hD : D.IsRational) :
    presheafValue (pushDatumB ϖ D hD) →+* locB K e.m D.s e.f := by
  haveI hcl : IsClosed ((IB K e.m D.s e.f : Set (PB K e.m))) := isClosed_IB' ϖ hK₀ D e
  haveI : NormedAddCommGroup (locB K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumB ϖ D hD).uniformSpace
  haveI : @IsTopologicalRing (Localization.Away (pushDatumB ϖ D hD).s)
      ((pushDatumB ϖ D hD).topology) _ := (pushDatumB ϖ D hD).isTopologicalRing
  haveI : @IsUniformAddGroup (Localization.Away (pushDatumB ϖ D hD).s)
      ((pushDatumB ϖ D hD).uniformSpace) _ := (pushDatumB ϖ D hD).isUniformAddGroup
  exact @UniformSpace.Completion.extensionHom
    (Localization.Away (pushDatumB ϖ D hD).s) _
    ((pushDatumB ϖ D hD).uniformSpace) ((pushDatumB ϖ D hD).isTopologicalRing)
    ((pushDatumB ϖ D hD).isUniformAddGroup)
    (locB K e.m D.s e.f) _ _ _ _
    (bridgeLocHomB ϖ D e hD) (bridgeLocHomB_continuous ϖ D e hD) _ _

theorem bridgeFwdB_coe (hD : D.IsRational) (a : Localization.Away (pushDatumB ϖ D hD).s) :
    bridgeFwdB ϖ hK₀ D e hD ((pushDatumB ϖ D hD).coeRingHom a) =
      bridgeLocHomB ϖ D e hD a := by
  haveI hcl : IsClosed ((IB K e.m D.s e.f : Set (PB K e.m))) := isClosed_IB' ϖ hK₀ D e
  haveI : NormedAddCommGroup (locB K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumB ϖ D hD).uniformSpace
  haveI : @IsTopologicalRing (Localization.Away (pushDatumB ϖ D hD).s)
      ((pushDatumB ϖ D hD).topology) _ := (pushDatumB ϖ D hD).isTopologicalRing
  haveI : @IsUniformAddGroup (Localization.Away (pushDatumB ϖ D hD).s)
      ((pushDatumB ϖ D hD).uniformSpace) _ := (pushDatumB ϖ D hD).isUniformAddGroup
  exact @UniformSpace.Completion.extensionHom_coe
    (Localization.Away (pushDatumB ϖ D hD).s) _
    ((pushDatumB ϖ D hD).uniformSpace) ((pushDatumB ϖ D hD).isTopologicalRing)
    ((pushDatumB ϖ D hD).isUniformAddGroup)
    (locB K e.m D.s e.f) _ _ _ _
    (bridgeLocHomB ϖ D e hD) (bridgeLocHomB_continuous ϖ D e hD) _ _ a

theorem bridgeFwdB_continuous (hD : D.IsRational) :
    Continuous (bridgeFwdB ϖ hK₀ D e hD) := by
  letI := (pushDatumB ϖ D hD).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-! #### The 𝓓-side forward bridge (mirror, consumed by the transfer's 𝓓-matching) -/

/-- The base map `𝓓 → 𝓓_α`. -/
noncomputable def bridgeBaseD : JetD K →+* locD K e.m D.s e.f :=
  (Ideal.Quotient.mk (ID K e.m D.s e.f)).comp
    ((polyToP : MvPolynomial (Fin e.m) (JetD K) →+* PD K e.m).comp MvPolynomial.C)

/-- The variable images `X̄ᵢ ∈ 𝓓_α`. -/
noncomputable def bridgeXD (i : Fin e.m) : locD K e.m D.s e.f :=
  Ideal.Quotient.mk (ID K e.m D.s e.f) (polyToP (MvPolynomial.X i))

theorem bridgeBaseD_s_mul_X (i : Fin e.m) :
    bridgeBaseD D e (rhoC K (iotaC K D.s)) * bridgeXD D e i =
      bridgeBaseD D e (rhoC K (iotaC K (e.f i))) := by
  have hmem : polyToP (MvPolynomial.C (rhoC K (iotaC K D.s))) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (rhoC K (iotaC K (e.f i)))) ∈ ID K e.m D.s e.f := by
    have hrw : rD K e.m D.s e.f i = polyToP (MvPolynomial.C (rhoC K (iotaC K D.s))) *
        polyToP (MvPolynomial.X i) - polyToP (MvPolynomial.C (rhoC K (iotaC K (e.f i)))) := by
      rw [rD_eq, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (ID K e.m D.s e.f) (polyToP (MvPolynomial.C (rhoC K (iotaC K D.s)))) *
      Ideal.Quotient.mk (ID K e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (ID K e.m D.s e.f) (polyToP (MvPolynomial.C (rhoC K (iotaC K (e.f i)))))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (ID K e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

theorem isUnit_bridgeBaseD_s (hD : D.IsRational) :
    IsUnit (bridgeBaseD D e (rhoC K (iotaC K D.s))) := by
  have h1 : (1 : JetD K) ∈
      Ideal.span ({rhoC K (iotaC K D.s)} ∪ Set.range fun i => rhoC K (iotaC K (e.f i))) := by
    rw [span_pushed_D K e.m D.s e.f (e.span_eq_top D hD)]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBaseD D e (d i * rhoC K (iotaC K (e.f i))) =
      bridgeBaseD D e (d i) * (bridgeBaseD D e (rhoC K (iotaC K D.s)) * bridgeXD D e i) :=
    fun i => by rw [RingHom.map_mul (bridgeBaseD D e), bridgeBaseD_s_mul_X]
  have happ : bridgeBaseD D e c * bridgeBaseD D e (rhoC K (iotaC K D.s)) +
      ∑ i, bridgeBaseD D e (d i) * (bridgeBaseD D e (rhoC K (iotaC K D.s)) * bridgeXD D e i) = 1 := by
    have h0 := congrArg (bridgeBaseD D e) hxy
    rw [RingHom.map_one (bridgeBaseD D e), RingHom.map_add (bridgeBaseD D e),
      RingHom.map_mul (bridgeBaseD D e),
      show (bridgeBaseD D e) (∑ i, d i * rhoC K (iotaC K (e.f i))) =
        ∑ i, bridgeBaseD D e (d i * rhoC K (iotaC K (e.f i))) from map_sum (bridgeBaseD D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBaseD D e (rhoC K (iotaC K D.s)) *
      (bridgeBaseD D e c + ∑ i, bridgeBaseD D e (d i) * bridgeXD D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBaseD D e (rhoC K (iotaC K D.s)) * bridgeBaseD D e c +
        ∑ i, bridgeBaseD D e (rhoC K (iotaC K D.s)) * (bridgeBaseD D e (d i) * bridgeXD D e i)
        = bridgeBaseD D e c * bridgeBaseD D e (rhoC K (iotaC K D.s)) +
          ∑ i, bridgeBaseD D e (d i) * (bridgeBaseD D e (rhoC K (iotaC K D.s)) * bridgeXD D e i) := by
          rw [mul_comm (bridgeBaseD D e (rhoC K (iotaC K D.s))) (bridgeBaseD D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

theorem norm_bridgeXD_le_one (i : Fin e.m) : ‖bridgeXD D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact gaussNorm_X_le_one (S := JetD K) i

theorem norm_bridgeBaseD_le (a : JetD K) : ‖bridgeBaseD D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := JetD K) (m := e.m) (MvPolynomial.C a) : PD K e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := JetD K) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetD K) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The 𝓓-side localization lift. -/
noncomputable def bridgeLocHomD (hD : D.IsRational) :
    Localization.Away (pushDatumD ϖ D hD).s →+* locD K e.m D.s e.f :=
  IsLocalization.Away.lift (S := Localization.Away (pushDatumD ϖ D hD).s)
    (pushDatumD ϖ D hD).s (isUnit_bridgeBaseD_s D e hD)

theorem bridgeLocHomD_algebraMap (hD : D.IsRational) (a : JetD K) :
    bridgeLocHomD ϖ D e hD
      (algebraMap (JetD K) (Localization.Away (pushDatumD ϖ D hD).s) a) =
      bridgeBaseD D e a :=
  IsLocalization.Away.lift_eq _ _ a

theorem bridgeLocHomD_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHomD ϖ D e hD (divByS (rhoC K (iotaC K (e.f i))) (pushDatumD ϖ D hD).s) =
      bridgeXD D e i := by
  have hu := isUnit_bridgeBaseD_s D e hD
  have hspec : divByS (rhoC K (iotaC K (e.f i))) (pushDatumD ϖ D hD).s *
      algebraMap (JetD K) (Localization.Away (pushDatumD ϖ D hD).s) (pushDatumD ϖ D hD).s =
      algebraMap (JetD K) (Localization.Away (pushDatumD ϖ D hD).s) (rhoC K (iotaC K (e.f i))) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHomD ϖ D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHomD ϖ D e hD), bridgeLocHomD_algebraMap,
    bridgeLocHomD_algebraMap, ← bridgeBaseD_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBaseD D e (rhoC K (iotaC K D.s)))
    (bridgeLocHomD ϖ D e hD (divByS (rhoC K (iotaC K (e.f i))) (pushDatumD ϖ D hD).s))]
  exact happ

theorem bridgeLocHomD_continuous (hD : D.IsRational) :
    @Continuous _ _ (pushDatumD ϖ D hD).topology _ (bridgeLocHomD ϖ D e hD) := by
  refine locTopology_continuous_lift (pushDatumD ϖ D hD).P (pushDatumD ϖ D hD).T
    (pushDatumD ϖ D hD).s (pushDatumD ϖ D hD).hopen _ ?_ ?_
  · have h_eq : (bridgeLocHomD ϖ D e hD).comp
        (algebraMap (JetD K) (Localization.Away (pushDatumD ϖ D hD).s)) =
        bridgeBaseD D e := by
      refine RingHom.ext fun a => ?_
      show bridgeLocHomD ϖ D e hD
        (algebraMap (JetD K) (Localization.Away (pushDatumD ϖ D hD).s) a) =
        bridgeBaseD D e a
      exact bridgeLocHomD_algebraMap ϖ D e hD a
    rw [show ⇑((bridgeLocHomD ϖ D e hD).comp
        (algebraMap (JetD K) (Localization.Away (pushDatumD ϖ D hD).s)))
        = ⇑(bridgeBaseD D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBaseD D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBaseD_le D e a
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, rfl⟩ := e.hf t₀ ht₀
    show TopologicalRing.IsPowerBounded
      (bridgeLocHomD ϖ D e hD (divByS (rhoC K (iotaC K (e.f i))) (pushDatumD ϖ D hD).s))
    rw [bridgeLocHomD_divByS]
    exact isPowerBounded_of_norm_le_one (norm_bridgeXD_le_one D e i)

include ϖ hK₀ in
/-- `I_𝓓` is closed (noetherian-ball route). -/
theorem isClosed_ID' : IsClosed ((ID K e.m D.s e.f : Set (PD K e.m))) := by
  haveI := isNoetherianRing_PD K e.m ϖ hK₀
  exact isClosed_graphIdeal (piD ϖ) (isUnit_piD ϖ)
    (by rw [norm_piD]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piD]; exact ϖ.norm_val_pos)
    (norm_piD_mul ϖ) (isNoetherianRing_unitBall_PD K e.m ϖ hK₀) (rD K e.m D.s e.f)

/-- The 𝓓-side forward bridge `𝒪_𝓓(D_D) → 𝓓_α`. -/
noncomputable def bridgeFwdD (hD : D.IsRational) :
    presheafValue (pushDatumD ϖ D hD) →+* locD K e.m D.s e.f := by
  haveI hcl : IsClosed ((ID K e.m D.s e.f : Set (PD K e.m))) := isClosed_ID' ϖ hK₀ D e
  haveI : NormedAddCommGroup (locD K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumD ϖ D hD).uniformSpace
  haveI : @IsTopologicalRing (Localization.Away (pushDatumD ϖ D hD).s)
      ((pushDatumD ϖ D hD).topology) _ := (pushDatumD ϖ D hD).isTopologicalRing
  haveI : @IsUniformAddGroup (Localization.Away (pushDatumD ϖ D hD).s)
      ((pushDatumD ϖ D hD).uniformSpace) _ := (pushDatumD ϖ D hD).isUniformAddGroup
  exact @UniformSpace.Completion.extensionHom
    (Localization.Away (pushDatumD ϖ D hD).s) _
    ((pushDatumD ϖ D hD).uniformSpace) ((pushDatumD ϖ D hD).isTopologicalRing)
    ((pushDatumD ϖ D hD).isUniformAddGroup)
    (locD K e.m D.s e.f) _ _ _ _
    (bridgeLocHomD ϖ D e hD) (bridgeLocHomD_continuous ϖ D e hD) _ _

theorem bridgeFwdD_coe (hD : D.IsRational) (a : Localization.Away (pushDatumD ϖ D hD).s) :
    bridgeFwdD ϖ hK₀ D e hD ((pushDatumD ϖ D hD).coeRingHom a) =
      bridgeLocHomD ϖ D e hD a := by
  haveI hcl : IsClosed ((ID K e.m D.s e.f : Set (PD K e.m))) := isClosed_ID' ϖ hK₀ D e
  haveI : NormedAddCommGroup (locD K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumD ϖ D hD).uniformSpace
  haveI : @IsTopologicalRing (Localization.Away (pushDatumD ϖ D hD).s)
      ((pushDatumD ϖ D hD).topology) _ := (pushDatumD ϖ D hD).isTopologicalRing
  haveI : @IsUniformAddGroup (Localization.Away (pushDatumD ϖ D hD).s)
      ((pushDatumD ϖ D hD).uniformSpace) _ := (pushDatumD ϖ D hD).isUniformAddGroup
  exact @UniformSpace.Completion.extensionHom_coe
    (Localization.Away (pushDatumD ϖ D hD).s) _
    ((pushDatumD ϖ D hD).uniformSpace) ((pushDatumD ϖ D hD).isTopologicalRing)
    ((pushDatumD ϖ D hD).isUniformAddGroup)
    (locD K e.m D.s e.f) _ _ _ _
    (bridgeLocHomD ϖ D e hD) (bridgeLocHomD_continuous ϖ D e hD) _ _ a

theorem bridgeFwdD_continuous (hD : D.IsRational) :
    Continuous (bridgeFwdD ϖ hK₀ D e hD) := by
  letI := (pushDatumD ϖ D hD).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-! #### 𝓑-side reverse (evaluation) — the injectivity half of the 𝓑-bridge -/

/-- Norm-decay to topological decay at 𝓑. -/
noncomputable def bridgeToRestrictedB (m : ℕ) :
    PB K m →+* ↥(restrictedMvPowerSeriesSubring m (JetB K)) where
  toFun p := ⟨p.1, by
    have hp : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) p.1 := p.2
    rw [MvPowerSeries.IsRestrictedGauss] at hp
    have hprod : ∀ t : Fin m →₀ ℕ, (t.prod fun _ k => (1 : ℝ) ^ k) = 1 := fun t => by simp
    simp only [hprod, mul_one] at hp
    show Filter.Tendsto (fun t : Fin m →₀ ℕ => MvPowerSeries.coeff t p.1)
      Filter.cofinite (nhds 0)
    rwa [tendsto_zero_iff_norm_tendsto_zero]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The pushed rational generators in `𝒪_𝓑(D_B)`. -/
noncomputable def bridgeGenB (hD : D.IsRational) (i : Fin e.m) :
    presheafValue (pushDatumB ϖ D hD) :=
  (pushDatumB ϖ D hD).coeRingHom (divByS (jB K (e.f i)) (pushDatumB ϖ D hD).s)

theorem bridgeGenB_isBounded (hD : D.IsRational) (i : Fin e.m) :
    TopologicalRing.IsBounded
      (Set.range (bridgeGenB ϖ D e hD i ^ · : ℕ → presheafValue (pushDatumB ϖ D hD))) := by
  have hmem : divByS (jB K (e.f i)) (pushDatumB ϖ D hD).s ∈
      locSubring (pushDatumB ϖ D hD).P (pushDatumB ϖ D hD).T (pushDatumB ϖ D hD).s :=
    divByS_mem_locSubring _ _ _ (Finset.mem_image_of_mem _ (e.hf' i))
  have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded
    (pushDatumB ϖ D hD)
  apply hbdd.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨divByS (jB K (e.f i)) (pushDatumB ϖ D hD).s ^ n, pow_mem hmem n, by
    rw [map_pow]; rfl⟩

/-- The 𝓑-side evaluation `P_𝓑 →+* 𝒪_𝓑(D_B)`. -/
noncomputable def bridgeEvalB (hD : D.IsRational) :
    PB K e.m →+* presheafValue (pushDatumB ϖ D hD) :=
  (mvEvalHomBounded (pushDatumB ϖ D hD).canonicalMap
    (canonicalMap_continuous (pushDatumB ϖ D hD))
    (bridgeGenB ϖ D e hD) (bridgeGenB_isBounded ϖ D e hD)).comp (bridgeToRestrictedB e.m)

theorem bridgeEvalB_const (hD : D.IsRational) (a : JetB K) :
    bridgeEvalB ϖ D e hD (polyToP (MvPolynomial.C a)) =
      (pushDatumB ϖ D hD).canonicalMap a := by
  have hcast : bridgeToRestrictedB (K := K) e.m (polyToP (MvPolynomial.C a)) =
      algebraMap (JetB K) ↥(restrictedMvPowerSeriesSubring e.m (JetB K)) a := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetB K) (m := e.m) (MvPolynomial.C a)).1 :
      MvPowerSeries (Fin e.m) (JetB K)) = _
    rw [show (polyToP (E := JetB K) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetB K) a from MvPolynomial.coe_C a]
    rfl
  rw [bridgeEvalB, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_algebraMap _ _ _ _ a

theorem bridgeEvalB_X (hD : D.IsRational) (i : Fin e.m) :
    bridgeEvalB ϖ D e hD (polyToP (MvPolynomial.X i)) = bridgeGenB ϖ D e hD i := by
  have hcast : bridgeToRestrictedB (K := K) e.m (polyToP (MvPolynomial.X i)) =
      ⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetB K) (m := e.m) (MvPolynomial.X i)).1 :
      MvPowerSeries (Fin e.m) (JetB K)) = _
    exact MvPolynomial.coe_X i
  rw [bridgeEvalB, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_X _ _ _ _ i

theorem IB_le_ker_bridgeEvalB (hD : D.IsRational) :
    IB K e.m D.s e.f ≤ RingHom.ker (bridgeEvalB ϖ D e hD) := by
  rw [IB, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, rB_eq]
  have hval : bridgeEvalB ϖ D e hD (polyToP (MvPolynomial.C (jB K D.s) * MvPolynomial.X i -
      MvPolynomial.C (jB K (e.f i)))) =
      (pushDatumB ϖ D hD).canonicalMap (jB K D.s) * bridgeGenB ϖ D e hD i -
        (pushDatumB ϖ D hD).canonicalMap (jB K (e.f i)) :=
    (map_sub ((bridgeEvalB ϖ D e hD).comp polyToP)
        (MvPolynomial.C (jB K D.s) * MvPolynomial.X i)
        (MvPolynomial.C (jB K (e.f i)))).trans
      (congrArg₂ (· - ·)
        ((map_mul ((bridgeEvalB ϖ D e hD).comp polyToP)
            (MvPolynomial.C (jB K D.s)) (MvPolynomial.X i)).trans
          (congrArg₂ (· * ·) (bridgeEvalB_const ϖ D e hD (jB K D.s))
            (bridgeEvalB_X ϖ D e hD i)))
        (bridgeEvalB_const ϖ D e hD (jB K (e.f i))))
  rw [hval, sub_eq_zero, bridgeGenB]
  rw [show (pushDatumB ϖ D hD).canonicalMap (jB K D.s) =
      (pushDatumB ϖ D hD).coeRingHom (algebraMap (JetB K)
        (Localization.Away (pushDatumB ϖ D hD).s) (pushDatumB ϖ D hD).s) from rfl,
    ← RingHom.map_mul (pushDatumB ϖ D hD).coeRingHom,
    show algebraMap (JetB K) (Localization.Away (pushDatumB ϖ D hD).s) (pushDatumB ϖ D hD).s *
      divByS (jB K (e.f i)) (pushDatumB ϖ D hD).s =
      algebraMap (JetB K) (Localization.Away (pushDatumB ϖ D hD).s) (jB K (e.f i)) from by
    rw [mul_comm, divByS, IsLocalization.mk'_spec]]
  rfl

/-- The 𝓑-side reverse `𝓑_α → 𝒪_𝓑(D_B)`. -/
noncomputable def bridgeRevB (hD : D.IsRational) :
    locB K e.m D.s e.f →+* presheafValue (pushDatumB ϖ D hD) :=
  Ideal.Quotient.lift (IB K e.m D.s e.f) (bridgeEvalB ϖ D e hD)
    (fun _ ha => RingHom.mem_ker.mp (IB_le_ker_bridgeEvalB ϖ D e hD ha))

theorem bridgeRevB_bridgeBaseB (hD : D.IsRational) (a : JetB K) :
    bridgeRevB ϖ D e hD (bridgeBaseB D e a) = (pushDatumB ϖ D hD).canonicalMap a :=
  bridgeEvalB_const ϖ D e hD a

private theorem bridgeRangeProdB_isBounded (hD : D.IsRational) :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i, bridgeGenB ϖ D e hD i ^ (v i))) := by
  classical
  suffices h : ∀ s : Finset (Fin e.m), TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i ∈ s, bridgeGenB ϖ D e hD i ^ (v i))) from
    h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty =>
      simpa using
        TopologicalRing.isBounded_singleton (1 : presheafValue (pushDatumB ϖ D hD))
  | insert a s ha ih =>
      refine ((bridgeGenB_isBounded ϖ D e hD a).mul ih).subset ?_
      rintro _ ⟨v, rfl⟩
      change ∏ i ∈ insert a s, bridgeGenB ϖ D e hD i ^ (v i) ∈ _
      rw [Finset.prod_insert ha]
      exact Set.mul_mem_mul ⟨v a, rfl⟩ ⟨v, rfl⟩

theorem bridgeEvalB_continuous (hD : D.IsRational) :
    Continuous (bridgeEvalB ϖ D e hD) := by
  classical
  refine continuous_of_continuousAt_zero (bridgeEvalB ϖ D e hD).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  obtain ⟨V, hV, hVR⟩ := bridgeRangeProdB_isBounded ϖ D e hD
    (W : Set (presheafValue (pushDatumB ϖ D hD)))
    (W.isOpen.mem_nhds W.zero_mem)
  have hpre : (pushDatumB ϖ D hD).canonicalMap ⁻¹' V ∈ nhds (0 : JetB K) :=
    (canonicalMap_continuous (pushDatumB ϖ D hD)).continuousAt.preimage_mem_nhds
      (by rwa [map_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : PB K e.m) hδ) ?_
  intro p hp
  rw [Metric.mem_ball, dist_zero_right] at hp
  apply hWU
  change (∑' v, mvEvalTerm (pushDatumB ϖ D hD).canonicalMap (bridgeGenB ϖ D e hD)
    (bridgeToRestrictedB e.m p) v) ∈ (W : Set (presheafValue (pushDatumB ϖ D hD)))
  refine tsum_mem_of_isOpen_addSubgroup'
    (mvEvalTerm_summable (pushDatumB ϖ D hD).canonicalMap
      (canonicalMap_continuous (pushDatumB ϖ D hD))
      (bridgeGenB ϖ D e hD) (bridgeGenB_isBounded ϖ D e hD) (bridgeToRestrictedB e.m p))
    W.isOpen fun v => ?_
  have hcoeff : ‖MvPowerSeries.coeff v p.1‖ < δ :=
    lt_of_le_of_lt (norm_coeff_le_gauss p v) hp
  have hVmem : (pushDatumB ϖ D hD).canonicalMap (MvPowerSeries.coeff v p.1) ∈ V :=
    hball (by rwa [Metric.mem_ball, dist_zero_right])
  change mvEvalTerm (pushDatumB ϖ D hD).canonicalMap (bridgeGenB ϖ D e hD)
    (bridgeToRestrictedB e.m p) v ∈ W
  rw [show mvEvalTerm (pushDatumB ϖ D hD).canonicalMap (bridgeGenB ϖ D e hD)
      (bridgeToRestrictedB e.m p) v =
      (∏ i, bridgeGenB ϖ D e hD i ^ (v i)) *
        (pushDatumB ϖ D hD).canonicalMap (MvPowerSeries.coeff v p.1) from by
    rw [mvEvalTerm]; exact mul_comm _ _]
  exact hVR (Set.mul_mem_mul ⟨v, rfl⟩ hVmem)

theorem bridgeRevB_continuous (hD : D.IsRational) :
    Continuous (bridgeRevB ϖ D e hD) := by
  rw [(QuotientRing.isOpenQuotientMap_mk (IB K e.m D.s e.f)).isQuotientMap.continuous_iff]
  exact bridgeEvalB_continuous ϖ D e hD

/-- `revB ∘ fwdB = id` — the 𝓑-bridge is split-injective. -/
theorem bridgeRevB_bridgeFwdB (hD : D.IsRational)
    (x : presheafValue (pushDatumB ϖ D hD)) :
    bridgeRevB ϖ D e hD (bridgeFwdB ϖ hK₀ D e hD x) = x := by
  letI := (pushDatumB ϖ D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumB ϖ D hD).s) :=
    (pushDatumB ϖ D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumB ϖ D hD).s) :=
    (pushDatumB ϖ D hD).isUniformAddGroup
  haveI : RegularSpace (presheafValue (pushDatumB ϖ D hD)) := UniformSpace.to_regularSpace
  have hcomp : (bridgeRevB ϖ D e hD).comp (bridgeLocHomB ϖ D e hD) =
      (pushDatumB ϖ D hD).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (pushDatumB ϖ D hD).s) ?_
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [bridgeLocHomB_algebraMap, bridgeRevB_bridgeBaseB]
    rfl
  have hdense : DenseRange ((pushDatumB ϖ D hD).coeRingHom :
      Localization.Away (pushDatumB ϖ D hD).s → presheafValue (pushDatumB ϖ D hD)) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => bridgeRevB ϖ D e hD (bridgeFwdB ϖ hK₀ D e hD y)) = fun y => y :=
    hdense.equalizer
      ((bridgeRevB_continuous ϖ D e hD).comp (bridgeFwdB_continuous ϖ hK₀ D e hD))
      continuous_id (by
        funext a
        show bridgeRevB ϖ D e hD (bridgeFwdB ϖ hK₀ D e hD
          ((pushDatumB ϖ D hD).coeRingHom a)) = (pushDatumB ϖ D hD).coeRingHom a
        rw [bridgeFwdB_coe]
        exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

theorem bridgeFwdB_injective (hD : D.IsRational) :
    Function.Injective (bridgeFwdB ϖ hK₀ D e hD) :=
  Function.LeftInverse.injective (g := bridgeRevB ϖ D e hD)
    (bridgeRevB_bridgeFwdB ϖ hK₀ D e hD)

/-! #### 𝓒-side reverse (evaluation) — the injectivity half of the 𝓒-bridge -/

/-- Norm-decay to topological decay at 𝓒. -/
noncomputable def bridgeToRestrictedC (m : ℕ) :
    PC K m →+* ↥(restrictedMvPowerSeriesSubring m (JetC K)) where
  toFun p := ⟨p.1, by
    have hp : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) p.1 := p.2
    rw [MvPowerSeries.IsRestrictedGauss] at hp
    have hprod : ∀ t : Fin m →₀ ℕ, (t.prod fun _ k => (1 : ℝ) ^ k) = 1 := fun t => by simp
    simp only [hprod, mul_one] at hp
    show Filter.Tendsto (fun t : Fin m →₀ ℕ => MvPowerSeries.coeff t p.1)
      Filter.cofinite (nhds 0)
    rwa [tendsto_zero_iff_norm_tendsto_zero]⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- The pushed rational generators in `𝒪_𝓒(D_C)`. -/
noncomputable def bridgeGenC (hD : D.IsRational) (i : Fin e.m) :
    presheafValue (pushDatumC ϖ D hD) :=
  (pushDatumC ϖ D hD).coeRingHom (divByS (iotaC K (e.f i)) (pushDatumC ϖ D hD).s)

theorem bridgeGenC_isBounded (hD : D.IsRational) (i : Fin e.m) :
    TopologicalRing.IsBounded
      (Set.range (bridgeGenC ϖ D e hD i ^ · : ℕ → presheafValue (pushDatumC ϖ D hD))) := by
  have hmem : divByS (iotaC K (e.f i)) (pushDatumC ϖ D hD).s ∈
      locSubring (pushDatumC ϖ D hD).P (pushDatumC ϖ D hD).T (pushDatumC ϖ D hD).s :=
    divByS_mem_locSubring _ _ _ (Finset.mem_image_of_mem _ (e.hf' i))
  have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded
    (pushDatumC ϖ D hD)
  apply hbdd.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨divByS (iotaC K (e.f i)) (pushDatumC ϖ D hD).s ^ n, pow_mem hmem n, by
    rw [map_pow]; rfl⟩

/-- The 𝓒-side evaluation `P_𝓒 →+* 𝒪_𝓒(D_C)`. -/
noncomputable def bridgeEvalC (hD : D.IsRational) :
    PC K e.m →+* presheafValue (pushDatumC ϖ D hD) :=
  (mvEvalHomBounded (pushDatumC ϖ D hD).canonicalMap
    (canonicalMap_continuous (pushDatumC ϖ D hD))
    (bridgeGenC ϖ D e hD) (bridgeGenC_isBounded ϖ D e hD)).comp (bridgeToRestrictedC e.m)

theorem bridgeEvalC_const (hD : D.IsRational) (a : JetC K) :
    bridgeEvalC ϖ D e hD (polyToP (MvPolynomial.C a)) =
      (pushDatumC ϖ D hD).canonicalMap a := by
  have hcast : bridgeToRestrictedC (K := K) e.m (polyToP (MvPolynomial.C a)) =
      algebraMap (JetC K) ↥(restrictedMvPowerSeriesSubring e.m (JetC K)) a := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetC K) (m := e.m) (MvPolynomial.C a)).1 :
      MvPowerSeries (Fin e.m) (JetC K)) = _
    rw [show (polyToP (E := JetC K) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetC K) a from MvPolynomial.coe_C a]
    rfl
  rw [bridgeEvalC, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_algebraMap _ _ _ _ a

theorem bridgeEvalC_X (hD : D.IsRational) (i : Fin e.m) :
    bridgeEvalC ϖ D e hD (polyToP (MvPolynomial.X i)) = bridgeGenC ϖ D e hD i := by
  have hcast : bridgeToRestrictedC (K := K) e.m (polyToP (MvPolynomial.X i)) =
      ⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetC K) (m := e.m) (MvPolynomial.X i)).1 :
      MvPowerSeries (Fin e.m) (JetC K)) = _
    exact MvPolynomial.coe_X i
  rw [bridgeEvalC, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_X _ _ _ _ i

theorem IC_le_ker_bridgeEvalC (hD : D.IsRational) :
    IC K e.m D.s e.f ≤ RingHom.ker (bridgeEvalC ϖ D e hD) := by
  rw [IC, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, rC_eq]
  have hval : bridgeEvalC ϖ D e hD (polyToP (MvPolynomial.C (iotaC K D.s) * MvPolynomial.X i -
      MvPolynomial.C (iotaC K (e.f i)))) =
      (pushDatumC ϖ D hD).canonicalMap (iotaC K D.s) * bridgeGenC ϖ D e hD i -
        (pushDatumC ϖ D hD).canonicalMap (iotaC K (e.f i)) :=
    (map_sub ((bridgeEvalC ϖ D e hD).comp polyToP)
        (MvPolynomial.C (iotaC K D.s) * MvPolynomial.X i)
        (MvPolynomial.C (iotaC K (e.f i)))).trans
      (congrArg₂ (· - ·)
        ((map_mul ((bridgeEvalC ϖ D e hD).comp polyToP)
            (MvPolynomial.C (iotaC K D.s)) (MvPolynomial.X i)).trans
          (congrArg₂ (· * ·) (bridgeEvalC_const ϖ D e hD (iotaC K D.s))
            (bridgeEvalC_X ϖ D e hD i)))
        (bridgeEvalC_const ϖ D e hD (iotaC K (e.f i))))
  rw [hval, sub_eq_zero, bridgeGenC]
  rw [show (pushDatumC ϖ D hD).canonicalMap (iotaC K D.s) =
      (pushDatumC ϖ D hD).coeRingHom (algebraMap (JetC K)
        (Localization.Away (pushDatumC ϖ D hD).s) (pushDatumC ϖ D hD).s) from rfl,
    ← RingHom.map_mul (pushDatumC ϖ D hD).coeRingHom,
    show algebraMap (JetC K) (Localization.Away (pushDatumC ϖ D hD).s) (pushDatumC ϖ D hD).s *
      divByS (iotaC K (e.f i)) (pushDatumC ϖ D hD).s =
      algebraMap (JetC K) (Localization.Away (pushDatumC ϖ D hD).s) (iotaC K (e.f i)) from by
    rw [mul_comm, divByS, IsLocalization.mk'_spec]]
  rfl

/-- The 𝓒-side reverse `𝓒_α → 𝒪_𝓒(D_C)`. -/
noncomputable def bridgeRevC (hD : D.IsRational) :
    locC K e.m D.s e.f →+* presheafValue (pushDatumC ϖ D hD) :=
  Ideal.Quotient.lift (IC K e.m D.s e.f) (bridgeEvalC ϖ D e hD)
    (fun _ ha => RingHom.mem_ker.mp (IC_le_ker_bridgeEvalC ϖ D e hD ha))

theorem bridgeRevC_bridgeBaseC (hD : D.IsRational) (a : JetC K) :
    bridgeRevC ϖ D e hD (bridgeBaseC D e a) = (pushDatumC ϖ D hD).canonicalMap a :=
  bridgeEvalC_const ϖ D e hD a

private theorem bridgeRangeProdC_isBounded (hD : D.IsRational) :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i, bridgeGenC ϖ D e hD i ^ (v i))) := by
  classical
  suffices h : ∀ s : Finset (Fin e.m), TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i ∈ s, bridgeGenC ϖ D e hD i ^ (v i))) from
    h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty =>
      simpa using
        TopologicalRing.isBounded_singleton (1 : presheafValue (pushDatumC ϖ D hD))
  | insert a s ha ih =>
      refine ((bridgeGenC_isBounded ϖ D e hD a).mul ih).subset ?_
      rintro _ ⟨v, rfl⟩
      change ∏ i ∈ insert a s, bridgeGenC ϖ D e hD i ^ (v i) ∈ _
      rw [Finset.prod_insert ha]
      exact Set.mul_mem_mul ⟨v a, rfl⟩ ⟨v, rfl⟩

theorem bridgeEvalC_continuous (hD : D.IsRational) :
    Continuous (bridgeEvalC ϖ D e hD) := by
  classical
  refine continuous_of_continuousAt_zero (bridgeEvalC ϖ D e hD).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  obtain ⟨V, hV, hVR⟩ := bridgeRangeProdC_isBounded ϖ D e hD
    (W : Set (presheafValue (pushDatumC ϖ D hD)))
    (W.isOpen.mem_nhds W.zero_mem)
  have hpre : (pushDatumC ϖ D hD).canonicalMap ⁻¹' V ∈ nhds (0 : JetC K) :=
    (canonicalMap_continuous (pushDatumC ϖ D hD)).continuousAt.preimage_mem_nhds
      (by rwa [map_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : PC K e.m) hδ) ?_
  intro p hp
  rw [Metric.mem_ball, dist_zero_right] at hp
  apply hWU
  change (∑' v, mvEvalTerm (pushDatumC ϖ D hD).canonicalMap (bridgeGenC ϖ D e hD)
    (bridgeToRestrictedC e.m p) v) ∈ (W : Set (presheafValue (pushDatumC ϖ D hD)))
  refine tsum_mem_of_isOpen_addSubgroup'
    (mvEvalTerm_summable (pushDatumC ϖ D hD).canonicalMap
      (canonicalMap_continuous (pushDatumC ϖ D hD))
      (bridgeGenC ϖ D e hD) (bridgeGenC_isBounded ϖ D e hD) (bridgeToRestrictedC e.m p))
    W.isOpen fun v => ?_
  have hcoeff : ‖MvPowerSeries.coeff v p.1‖ < δ :=
    lt_of_le_of_lt (norm_coeff_le_gauss p v) hp
  have hVmem : (pushDatumC ϖ D hD).canonicalMap (MvPowerSeries.coeff v p.1) ∈ V :=
    hball (by rwa [Metric.mem_ball, dist_zero_right])
  change mvEvalTerm (pushDatumC ϖ D hD).canonicalMap (bridgeGenC ϖ D e hD)
    (bridgeToRestrictedC e.m p) v ∈ W
  rw [show mvEvalTerm (pushDatumC ϖ D hD).canonicalMap (bridgeGenC ϖ D e hD)
      (bridgeToRestrictedC e.m p) v =
      (∏ i, bridgeGenC ϖ D e hD i ^ (v i)) *
        (pushDatumC ϖ D hD).canonicalMap (MvPowerSeries.coeff v p.1) from by
    rw [mvEvalTerm]; exact mul_comm _ _]
  exact hVR (Set.mul_mem_mul ⟨v, rfl⟩ hVmem)

theorem bridgeRevC_continuous (hD : D.IsRational) :
    Continuous (bridgeRevC ϖ D e hD) := by
  rw [(QuotientRing.isOpenQuotientMap_mk (IC K e.m D.s e.f)).isQuotientMap.continuous_iff]
  exact bridgeEvalC_continuous ϖ D e hD

/-- `revC ∘ fwdC = id` — the 𝓒-bridge is split-injective. -/
theorem bridgeRevC_bridgeFwdC (hD : D.IsRational)
    (x : presheafValue (pushDatumC ϖ D hD)) :
    bridgeRevC ϖ D e hD (bridgeFwdC ϖ hK₀ D e hD x) = x := by
  letI := (pushDatumC ϖ D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumC ϖ D hD).s) :=
    (pushDatumC ϖ D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumC ϖ D hD).s) :=
    (pushDatumC ϖ D hD).isUniformAddGroup
  haveI : RegularSpace (presheafValue (pushDatumC ϖ D hD)) := UniformSpace.to_regularSpace
  have hcomp : (bridgeRevC ϖ D e hD).comp (bridgeLocHomC ϖ D e hD) =
      (pushDatumC ϖ D hD).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (pushDatumC ϖ D hD).s) ?_
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [bridgeLocHomC_algebraMap, bridgeRevC_bridgeBaseC]
    rfl
  have hdense : DenseRange ((pushDatumC ϖ D hD).coeRingHom :
      Localization.Away (pushDatumC ϖ D hD).s → presheafValue (pushDatumC ϖ D hD)) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => bridgeRevC ϖ D e hD (bridgeFwdC ϖ hK₀ D e hD y)) = fun y => y :=
    hdense.equalizer
      ((bridgeRevC_continuous ϖ D e hD).comp (bridgeFwdC_continuous ϖ hK₀ D e hD))
      continuous_id (by
        funext a
        show bridgeRevC ϖ D e hD (bridgeFwdC ϖ hK₀ D e hD
          ((pushDatumC ϖ D hD).coeRingHom a)) = (pushDatumC ϖ D hD).coeRingHom a
        rw [bridgeFwdC_coe]
        exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

theorem bridgeFwdC_injective (hD : D.IsRational) :
    Function.Injective (bridgeFwdC ϖ hK₀ D e hD) :=
  Function.LeftInverse.injective (g := bridgeRevC ϖ D e hD)
    (bridgeRevC_bridgeFwdC ϖ hK₀ D e hD)

/-! #### Second-level covariant maps `𝒪_𝓑(D_B) → 𝒪_𝓓(D_D)`, `𝒪_𝓒(D_C) → 𝒪_𝓓(D_D)`
and the coherence/naturality squares consumed by the 𝓓-matching step -/

theorem continuous_rhoB : Continuous (rhoB K) :=
  AddMonoidHomClass.continuous_of_bound (rhoB K) 1 fun a => by
    rw [one_mul, norm_rhoB]

/-- `ρ_B` pushes the 𝓑-datum to the 𝓓-datum (via the square identity). -/
noncomputable def mapBD (hD : D.IsRational) :
    presheafValue (pushDatumB ϖ D hD) →+* presheafValue (pushDatumD ϖ D hD) :=
  presheafValueMapOfHom (rhoB K) (continuous_rhoB) (pushDatumB ϖ D hD) (pushDatumD ϖ D hD)
    ((square_commutes K D.s).symm)
    (by
      intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
      rw [square_commutes K t₀]
      exact Finset.mem_image_of_mem _ ht₀)

/-- `ρ_C` pushes the 𝓒-datum to the 𝓓-datum. -/
noncomputable def mapCD (hD : D.IsRational) :
    presheafValue (pushDatumC ϖ D hD) →+* presheafValue (pushDatumD ϖ D hD) :=
  presheafValueMapOfHom (rhoC K) (continuous_rhoC) (pushDatumC ϖ D hD) (pushDatumD ϖ D hD)
    rfl
    (by
      intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_image_of_mem _ ht₀)

theorem mapBD_continuous (hD : D.IsRational) : Continuous (mapBD ϖ D hD) := by
  unfold mapBD
  exact presheafValueMapOfHom_continuous _ _ _ _ _ _

theorem mapCD_continuous (hD : D.IsRational) : Continuous (mapCD ϖ D hD) := by
  unfold mapCD
  exact presheafValueMapOfHom_continuous _ _ _ _ _ _

/-- The 𝓓-coherence of the two composite pushes ([FJP] (4.9): the square commutes on
sections). -/
theorem mapBD_mapB_eq_mapCD_mapC (hD : D.IsRational) :
    (mapBD ϖ D hD).comp (presheafValueMapB ϖ D hD) =
      (mapCD ϖ D hD).comp (presheafValueMapC ϖ D hD) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : RegularSpace (presheafValue (pushDatumD ϖ D hD)) := UniformSpace.to_regularSpace
  have hcomp : ((mapBD ϖ D hD).comp (presheafValueMapB ϖ D hD)).comp D.coeRingHom =
      ((mapCD ϖ D hD).comp (presheafValueMapC ϖ D hD)).comp D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [show D.coeRingHom (algebraMap (JetA K) (Localization.Away D.s) a) =
        D.canonicalMap a from rfl,
      presheafValueMapB_canonicalMap, presheafValueMapC_canonicalMap,
      show mapBD ϖ D hD ((pushDatumB ϖ D hD).canonicalMap (jB K a)) =
        (pushDatumD ϖ D hD).canonicalMap (rhoB K (jB K a)) from
        presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ (jB K a),
      show mapCD ϖ D hD ((pushDatumC ϖ D hD).canonicalMap (iotaC K a)) =
        (pushDatumD ϖ D hD).canonicalMap (rhoC K (iotaC K a)) from
        presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ (iotaC K a),
      square_commutes K a]
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : ⇑((mapBD ϖ D hD).comp (presheafValueMapB ϖ D hD)) =
      ⇑((mapCD ϖ D hD).comp (presheafValueMapC ϖ D hD)) :=
    hdense.equalizer
      ((mapBD_continuous ϖ D hD).comp (presheafValueMapB_continuous ϖ D hD))
      ((mapCD_continuous ϖ D hD).comp (presheafValueMapC_continuous ϖ D hD))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

/-- The quotient projections are norm-nonincreasing along `ρ` (ε-representatives). -/
theorem norm_locRhoB_le (x : locB K e.m D.s e.f) :
    ‖locRhoB K e.m D.s e.f x‖ ≤ ‖x‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨p, hp, hpn⟩ := Ideal.Quotient.norm_mk_lt x hε
  calc ‖locRhoB K e.m D.s e.f x‖
      = ‖locRhoB K e.m D.s e.f (Ideal.Quotient.mk (IB K e.m D.s e.f) p)‖ := by rw [hp]
    _ = ‖Ideal.Quotient.mk (ID K e.m D.s e.f) (extRhoB K e.m p)‖ := by
        rw [locRhoB_mk]
    _ ≤ ‖extRhoB K e.m p‖ := Ideal.Quotient.norm_mk_le _ _
    _ ≤ ‖p‖ := norm_mapRestricted_le _ _ _ p
    _ ≤ ‖x‖ + ε := hpn.le

theorem norm_locRhoC_le (x : locC K e.m D.s e.f) :
    ‖locRhoC K e.m D.s e.f x‖ ≤ ‖x‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨p, hp, hpn⟩ := Ideal.Quotient.norm_mk_lt x hε
  calc ‖locRhoC K e.m D.s e.f x‖
      = ‖locRhoC K e.m D.s e.f (Ideal.Quotient.mk (IC K e.m D.s e.f) p)‖ := by rw [hp]
    _ = ‖Ideal.Quotient.mk (ID K e.m D.s e.f) (extRhoC K e.m p)‖ := by
        rw [locRhoC_mk]
    _ ≤ ‖extRhoC K e.m p‖ := Ideal.Quotient.norm_mk_le _ _
    _ ≤ ‖p‖ := norm_mapRestricted_le _ _ _ p
    _ ≤ ‖x‖ + ε := hpn.le

theorem locRhoB_continuous : Continuous (locRhoB K e.m D.s e.f) :=
  AddMonoidHomClass.continuous_of_bound (locRhoB K e.m D.s e.f) 1 fun x => by
    rw [one_mul]; exact norm_locRhoB_le D e x

theorem locRhoC_continuous : Continuous (locRhoC K e.m D.s e.f) :=
  AddMonoidHomClass.continuous_of_bound (locRhoC K e.m D.s e.f) 1 fun x => by
    rw [one_mul]; exact norm_locRhoC_le D e x

/-- `ρ`-naturality, 𝓑-side: `locRhoB ∘ fwdB = fwdD ∘ mapBD`. -/
theorem locRhoB_bridgeFwdB (hD : D.IsRational) :
    (locRhoB K e.m D.s e.f).comp (bridgeFwdB ϖ hK₀ D e hD) =
      (bridgeFwdD ϖ hK₀ D e hD).comp (mapBD ϖ D hD) := by
  letI := (pushDatumB ϖ D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumB ϖ D hD).s) :=
    (pushDatumB ϖ D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumB ϖ D hD).s) :=
    (pushDatumB ϖ D hD).isUniformAddGroup
  haveI hcl : IsClosed ((ID K e.m D.s e.f : Set (PD K e.m))) := isClosed_ID' ϖ hK₀ D e
  haveI : NormedAddCommGroup (locD K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  have hdense : DenseRange ((pushDatumB ϖ D hD).coeRingHom :
      Localization.Away (pushDatumB ϖ D hD).s → presheafValue (pushDatumB ϖ D hD)) :=
    UniformSpace.Completion.denseRange_coe
  have hcomp : ((locRhoB K e.m D.s e.f).comp (bridgeFwdB ϖ hK₀ D e hD)).comp
      (pushDatumB ϖ D hD).coeRingHom =
      ((bridgeFwdD ϖ hK₀ D e hD).comp (mapBD ϖ D hD)).comp
        (pushDatumB ϖ D hD).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (pushDatumB ϖ D hD).s) ?_
    refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply]
    rw [show (pushDatumB ϖ D hD).coeRingHom (algebraMap (JetB K)
        (Localization.Away (pushDatumB ϖ D hD).s) b) =
        (pushDatumB ϖ D hD).canonicalMap b from rfl,
      show bridgeFwdB ϖ hK₀ D e hD ((pushDatumB ϖ D hD).canonicalMap b) =
        bridgeBaseB D e b from by
        rw [show (pushDatumB ϖ D hD).canonicalMap b =
          (pushDatumB ϖ D hD).coeRingHom (algebraMap (JetB K)
            (Localization.Away (pushDatumB ϖ D hD).s) b) from rfl,
          bridgeFwdB_coe, bridgeLocHomB_algebraMap],
      show mapBD ϖ D hD ((pushDatumB ϖ D hD).canonicalMap b) =
        (pushDatumD ϖ D hD).canonicalMap (rhoB K b) from
        presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ b,
      show bridgeFwdD ϖ hK₀ D e hD ((pushDatumD ϖ D hD).canonicalMap (rhoB K b)) =
        bridgeBaseD D e (rhoB K b) from by
        rw [show (pushDatumD ϖ D hD).canonicalMap (rhoB K b) =
          (pushDatumD ϖ D hD).coeRingHom (algebraMap (JetD K)
            (Localization.Away (pushDatumD ϖ D hD).s) (rhoB K b)) from rfl,
          bridgeFwdD_coe, bridgeLocHomD_algebraMap]]
    rw [show bridgeBaseB D e b =
        Ideal.Quotient.mk (IB K e.m D.s e.f) (polyToP (MvPolynomial.C b)) from rfl,
      locRhoB_mk,
      show extRhoB K e.m (polyToP (MvPolynomial.C b)) =
        polyToP (MvPolynomial.map (rhoB K) (MvPolynomial.C b)) from
        mapRestricted_polyToP _ _ _ (MvPolynomial.C b),
      MvPolynomial.map_C]
    rfl
  have h_eq : ⇑((locRhoB K e.m D.s e.f).comp (bridgeFwdB ϖ hK₀ D e hD)) =
      ⇑((bridgeFwdD ϖ hK₀ D e hD).comp (mapBD ϖ D hD)) :=
    hdense.equalizer
      ((locRhoB_continuous D e).comp (bridgeFwdB_continuous ϖ hK₀ D e hD))
      ((bridgeFwdD_continuous ϖ hK₀ D e hD).comp (mapBD_continuous ϖ D hD))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

/-- `ρ`-naturality, 𝓒-side: `locRhoC ∘ fwdC = fwdD ∘ mapCD`. -/
theorem locRhoC_bridgeFwdC (hD : D.IsRational) :
    (locRhoC K e.m D.s e.f).comp (bridgeFwdC ϖ hK₀ D e hD) =
      (bridgeFwdD ϖ hK₀ D e hD).comp (mapCD ϖ D hD) := by
  letI := (pushDatumC ϖ D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumC ϖ D hD).s) :=
    (pushDatumC ϖ D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumC ϖ D hD).s) :=
    (pushDatumC ϖ D hD).isUniformAddGroup
  haveI hcl : IsClosed ((ID K e.m D.s e.f : Set (PD K e.m))) := isClosed_ID' ϖ hK₀ D e
  haveI : NormedAddCommGroup (locD K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  have hdense : DenseRange ((pushDatumC ϖ D hD).coeRingHom :
      Localization.Away (pushDatumC ϖ D hD).s → presheafValue (pushDatumC ϖ D hD)) :=
    UniformSpace.Completion.denseRange_coe
  have hcomp : ((locRhoC K e.m D.s e.f).comp (bridgeFwdC ϖ hK₀ D e hD)).comp
      (pushDatumC ϖ D hD).coeRingHom =
      ((bridgeFwdD ϖ hK₀ D e hD).comp (mapCD ϖ D hD)).comp
        (pushDatumC ϖ D hD).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (pushDatumC ϖ D hD).s) ?_
    refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply]
    rw [show (pushDatumC ϖ D hD).coeRingHom (algebraMap (JetC K)
        (Localization.Away (pushDatumC ϖ D hD).s) b) =
        (pushDatumC ϖ D hD).canonicalMap b from rfl,
      show bridgeFwdC ϖ hK₀ D e hD ((pushDatumC ϖ D hD).canonicalMap b) =
        bridgeBaseC D e b from by
        rw [show (pushDatumC ϖ D hD).canonicalMap b =
          (pushDatumC ϖ D hD).coeRingHom (algebraMap (JetC K)
            (Localization.Away (pushDatumC ϖ D hD).s) b) from rfl,
          bridgeFwdC_coe, bridgeLocHomC_algebraMap],
      show mapCD ϖ D hD ((pushDatumC ϖ D hD).canonicalMap b) =
        (pushDatumD ϖ D hD).canonicalMap (rhoC K b) from
        presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ b,
      show bridgeFwdD ϖ hK₀ D e hD ((pushDatumD ϖ D hD).canonicalMap (rhoC K b)) =
        bridgeBaseD D e (rhoC K b) from by
        rw [show (pushDatumD ϖ D hD).canonicalMap (rhoC K b) =
          (pushDatumD ϖ D hD).coeRingHom (algebraMap (JetD K)
            (Localization.Away (pushDatumD ϖ D hD).s) (rhoC K b)) from rfl,
          bridgeFwdD_coe, bridgeLocHomD_algebraMap]]
    rw [show bridgeBaseC D e b =
        Ideal.Quotient.mk (IC K e.m D.s e.f) (polyToP (MvPolynomial.C b)) from rfl,
      locRhoC_mk,
      show extRhoC K e.m (polyToP (MvPolynomial.C b)) =
        polyToP (MvPolynomial.map (rhoC K) (MvPolynomial.C b)) from
        mapRestricted_polyToP _ _ _ (MvPolynomial.C b),
      MvPolynomial.map_C]
    rfl
  have h_eq : ⇑((locRhoC K e.m D.s e.f).comp (bridgeFwdC ϖ hK₀ D e hD)) =
      ⇑((bridgeFwdD ϖ hK₀ D e hD).comp (mapCD ϖ D hD)) :=
    hdense.equalizer
      ((locRhoC_continuous D e).comp (bridgeFwdC_continuous ϖ hK₀ D e hD))
      ((bridgeFwdD_continuous ϖ hK₀ D e hD).comp (mapCD_continuous ϖ D hD))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

end GraphBridgeInfra

/-- The graph bridge for 𝓐 ([FJP] Lemma 1.1: the separated completion of the graph
quotient "is therefore canonically the underlying Tate algebra of Huber's rational
localization `E_α`"; by Lemma 4.3 the ideal is closed so no further completion is needed).
Topological ring isomorphism `𝒪_𝓐(D) ≅ P_𝓐 ⧸ I_𝓐`. -/
def graphBridgeA (D : RationalLocData (JetA K)) (hD : D.IsRational) (e : DatumEnum D) :
    presheafValue D ≃+* locA (K := K) e.m D.s e.f where
  toFun := bridgeFwd ϖ hK₀ D e hD
  invFun := bridgeRev D e
  left_inv := bridgeRev_bridgeFwd ϖ hK₀ D e hD
  right_inv := bridgeFwd_bridgeRev ϖ hK₀ D e hD
  map_mul' := map_mul (bridgeFwd ϖ hK₀ D e hD)
  map_add' := map_add (bridgeFwd ϖ hK₀ D e hD)

theorem graphBridgeA_continuous (D : RationalLocData (JetA K)) (hD : D.IsRational)
    (e : DatumEnum D) : Continuous (graphBridgeA ϖ hK₀ D hD e) :=
  bridgeFwd_continuous ϖ hK₀ D e hD

theorem graphBridgeA_symm_continuous (D : RationalLocData (JetA K)) (hD : D.IsRational)
    (e : DatumEnum D) : Continuous (graphBridgeA ϖ hK₀ D hD e).symm :=
  bridgeRev_continuous D e

/-- The 𝓑-side naturality square (mirror of `graphBridge_natural_C`, consumed by the
transfer): `bridgeFwdB ∘ presheafValueMapB = locJB ∘ graphBridgeA`. -/
theorem graphBridge_natural_B (D : RationalLocData (JetA K)) (hD : D.IsRational)
    (e : DatumEnum D) :
    (bridgeFwdB ϖ hK₀ D e hD).comp (presheafValueMapB ϖ D hD) =
      (locJB K e.m D.s e.f).comp
        (graphBridgeA ϖ hK₀ D hD e : presheafValue D →+* locA K e.m D.s e.f) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI hcl : IsClosed ((IB K e.m D.s e.f : Set (PB K e.m))) := isClosed_IB' ϖ hK₀ D e
  haveI : NormedAddCommGroup (locB K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have hcomp : ((bridgeFwdB ϖ hK₀ D e hD).comp (presheafValueMapB ϖ D hD)).comp
      D.coeRingHom =
      ((locJB K e.m D.s e.f).comp
        (graphBridgeA ϖ hK₀ D hD e : presheafValue D →+* locA K e.m D.s e.f)).comp
        D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show (D.coeRingHom (algebraMap (JetA K) (Localization.Away D.s) a)) =
        D.canonicalMap a from rfl,
      presheafValueMapB_canonicalMap,
      show (pushDatumB ϖ D hD).canonicalMap (jB K a) =
        (pushDatumB ϖ D hD).coeRingHom (algebraMap (JetB K)
          (Localization.Away (pushDatumB ϖ D hD).s) (jB K a)) from rfl,
      bridgeFwdB_coe, bridgeLocHomB_algebraMap,
      show (graphBridgeA ϖ hK₀ D hD e : presheafValue D →+* locA K e.m D.s e.f)
        (D.canonicalMap a) = bridgeFwd ϖ hK₀ D e hD (D.canonicalMap a) from rfl,
      bridgeFwd_canonicalMap]
    rw [show bridgeBase D e a =
        Ideal.Quotient.mk (IA K e.m D.s e.f) (polyToP (MvPolynomial.C a)) from rfl,
      locJB_mk,
      show extJB K e.m (polyToP (MvPolynomial.C a)) =
        polyToP (MvPolynomial.map (jB K) (MvPolynomial.C a)) from
        mapRestricted_polyToP _ _ _ (MvPolynomial.C a),
      MvPolynomial.map_C]
    rfl
  have h_eq : ⇑((bridgeFwdB ϖ hK₀ D e hD).comp (presheafValueMapB ϖ D hD)) =
      ⇑((locJB K e.m D.s e.f).comp
        (graphBridgeA ϖ hK₀ D hD e : presheafValue D →+* locA K e.m D.s e.f)) :=
    hdense.equalizer
      ((bridgeFwdB_continuous ϖ hK₀ D e hD).comp (presheafValueMapB_continuous ϖ D hD))
      ((locJB_lipschitz K e.m D.s e.f).continuous.comp
        (graphBridgeA_continuous ϖ hK₀ D hD e))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

/-- The bridge intertwines the covariant maps with the coefficientwise localized square
([FJP] Lemma 4.6 / Lemma 5.1 naturality, 𝓒 side):
`bridgeFwdC ∘ presheafValueMapC = locIotaC ∘ graphBridgeA`. -/
theorem graphBridge_natural_C (D : RationalLocData (JetA K)) (hD : D.IsRational)
    (e : DatumEnum D) :
    (bridgeFwdC ϖ hK₀ D e hD).comp (presheafValueMapC ϖ D hD) =
      (locIotaC K e.m D.s e.f).comp
        (graphBridgeA ϖ hK₀ D hD e : presheafValue D →+* locA K e.m D.s e.f) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI hcl : IsClosed ((IC K e.m D.s e.f : Set (PC K e.m))) := isClosed_IC' ϖ hK₀ D e
  haveI : NormedAddCommGroup (locC K e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have hcomp : ((bridgeFwdC ϖ hK₀ D e hD).comp (presheafValueMapC ϖ D hD)).comp
      D.coeRingHom =
      ((locIotaC K e.m D.s e.f).comp
        (graphBridgeA ϖ hK₀ D hD e : presheafValue D →+* locA K e.m D.s e.f)).comp
        D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show (D.coeRingHom (algebraMap (JetA K) (Localization.Away D.s) a)) =
        D.canonicalMap a from rfl,
      presheafValueMapC_canonicalMap,
      show (pushDatumC ϖ D hD).canonicalMap (iotaC K a) =
        (pushDatumC ϖ D hD).coeRingHom (algebraMap (JetC K)
          (Localization.Away (pushDatumC ϖ D hD).s) (iotaC K a)) from rfl,
      bridgeFwdC_coe, bridgeLocHomC_algebraMap,
      show (graphBridgeA ϖ hK₀ D hD e : presheafValue D →+* locA K e.m D.s e.f)
        (D.canonicalMap a) = bridgeFwd ϖ hK₀ D e hD (D.canonicalMap a) from rfl,
      bridgeFwd_canonicalMap]
    -- `bridgeBaseC (ι a) = locIotaC (bridgeBase a)`: both are `mk (polyToP (C (ι a)))`.
    rw [show bridgeBase D e a =
        Ideal.Quotient.mk (IA K e.m D.s e.f) (polyToP (MvPolynomial.C a)) from rfl,
      locIotaC_mk,
      show extIotaC K e.m (polyToP (MvPolynomial.C a)) =
        polyToP (MvPolynomial.map (iotaC K) (MvPolynomial.C a)) from
        mapRestricted_polyToP _ _ _ (MvPolynomial.C a),
      MvPolynomial.map_C]
    rfl
  have h_eq : ⇑((bridgeFwdC ϖ hK₀ D e hD).comp (presheafValueMapC ϖ D hD)) =
      ⇑((locIotaC K e.m D.s e.f).comp
        (graphBridgeA ϖ hK₀ D hD e : presheafValue D →+* locA K e.m D.s e.f)) :=
    hdense.equalizer
      ((bridgeFwdC_continuous ϖ hK₀ D e hD).comp (presheafValueMapC_continuous ϖ D hD))
      ((locIotaC_lipschitz K e.m D.s e.f).continuous.comp
        (graphBridgeA_continuous ϖ hK₀ D hD e))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

/-! ### Naturality with restriction ([FJP] Lemma 4.6, Lemma 5.1)

With the loc-lift instances available, the project's `restrictionMap` vocabulary applies
to all four rings, and the covariant maps commute with it. -/

theorem presheafValueMapC_restriction (D D' : RationalLocData (JetA K))
    (hD : D.IsRational) (hD' : D'.IsRational)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hpush : rationalOpen (pushDatumC ϖ D' hD').T (pushDatumC ϖ D' hD').s ⊆
      rationalOpen (pushDatumC ϖ D hD).T (pushDatumC ϖ D hD).s) (x : presheafValue D) :
    presheafValueMapC ϖ D' hD' (restrictionMap D D' h x) =
      restrictionMap (pushDatumC ϖ D hD) (pushDatumC ϖ D' hD') hpush
        (presheafValueMapC ϖ D hD x) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : RegularSpace (presheafValue (pushDatumC ϖ D' hD')) :=
    UniformSpace.to_regularSpace
  have hcomp : ((presheafValueMapC ϖ D' hD').comp (restrictionMapHom D D' h)).comp
      D.coeRingHom =
      ((restrictionMapHom (pushDatumC ϖ D hD) (pushDatumC ϖ D' hD') hpush).comp
        (presheafValueMapC ϖ D hD)).comp D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show D.coeRingHom (algebraMap (JetA K) (Localization.Away D.s) a) =
        D.canonicalMap a from rfl,
      restrictionMapHom_canonicalMap_generic D D' h, presheafValueMapC_canonicalMap,
      presheafValueMapC_canonicalMap,
      restrictionMapHom_canonicalMap_generic (pushDatumC ϖ D hD) (pushDatumC ϖ D' hD')
        hpush]
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => presheafValueMapC ϖ D' hD' (restrictionMapHom D D' h y)) =
      fun y => restrictionMapHom (pushDatumC ϖ D hD) (pushDatumC ϖ D' hD') hpush
        (presheafValueMapC ϖ D hD y) :=
    hdense.equalizer
      ((presheafValueMapC_continuous ϖ D' hD').comp (restrictionMapHom_continuous D D' h))
      ((restrictionMapHom_continuous _ _ hpush).comp
        (presheafValueMapC_continuous ϖ D hD))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

theorem presheafValueMapB_restriction (D D' : RationalLocData (JetA K))
    (hD : D.IsRational) (hD' : D'.IsRational)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hpush : rationalOpen (pushDatumB ϖ D' hD').T (pushDatumB ϖ D' hD').s ⊆
      rationalOpen (pushDatumB ϖ D hD).T (pushDatumB ϖ D hD).s) (x : presheafValue D) :
    presheafValueMapB ϖ D' hD' (restrictionMap D D' h x) =
      restrictionMap (pushDatumB ϖ D hD) (pushDatumB ϖ D' hD') hpush
        (presheafValueMapB ϖ D hD x) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : RegularSpace (presheafValue (pushDatumB ϖ D' hD')) :=
    UniformSpace.to_regularSpace
  have hcomp : ((presheafValueMapB ϖ D' hD').comp (restrictionMapHom D D' h)).comp
      D.coeRingHom =
      ((restrictionMapHom (pushDatumB ϖ D hD) (pushDatumB ϖ D' hD') hpush).comp
        (presheafValueMapB ϖ D hD)).comp D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show D.coeRingHom (algebraMap (JetA K) (Localization.Away D.s) a) =
        D.canonicalMap a from rfl,
      restrictionMapHom_canonicalMap_generic D D' h, presheafValueMapB_canonicalMap,
      presheafValueMapB_canonicalMap,
      restrictionMapHom_canonicalMap_generic (pushDatumB ϖ D hD) (pushDatumB ϖ D' hD')
        hpush]
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => presheafValueMapB ϖ D' hD' (restrictionMapHom D D' h y)) =
      fun y => restrictionMapHom (pushDatumB ϖ D hD) (pushDatumB ϖ D' hD') hpush
        (presheafValueMapB ϖ D hD y) :=
    hdense.equalizer
      ((presheafValueMapB_continuous ϖ D' hD').comp (restrictionMapHom_continuous D D' h))
      ((restrictionMapHom_continuous _ _ hpush).comp
        (presheafValueMapB_continuous ϖ D hD))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

/-! ### Coverage transfer ([FJP] Lemma 5.2, first display: `U_E = ⋃ᵢ (Uᵢ)_E`) -/

include ϖ in
/-- Power-bounded elements of 𝓐 stay power-bounded under any norm-nonincreasing ring map
(the [FJP] "never bare continuity" transfer: 𝓐° = unit ball by Prop 2.3, and
norm-≤-1 elements are power-bounded in any seminormed ring). -/
theorem plus_le_comap_of_norm_le {E : Type*} [SeminormedCommRing E]
    (φ : JetA K →+* E) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) {x : JetA K}
    (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (φ x) :=
  isPowerBounded_of_norm_le_one
    (le_trans (hφ x) ((isPowerBounded_JetA_iff ϖ x).mp hx))

/-- Inverse images preserve the rational inequalities: pushed rational opens are the
`spaComap`-preimages. (Pointwise: `v ∈ rationalOpen (T_E, s_E) ↔ v ∘ ι ∈ rationalOpen (T, s)`
for `v` in the vertex spectrum.) -/
theorem mem_rationalOpen_pushDatumC_iff (D : RationalLocData (JetA K))
    (hD : D.IsRational) (v : Spv (JetC K)) (hv : v ∈ Spa (JetC K) (ringPlus (JetC K))) :
    v ∈ rationalOpen (pushDatumC ϖ D hD).T (pushDatumC ϖ D hD).s ↔
      ValuationSpectrum.comap (iotaC K) v ∈ rationalOpen D.T D.s := by
  have hcomap : ValuationSpectrum.comap (iotaC K) v ∈ Spa (JetA K) (ringPlus (JetA K)) :=
    comap_mem_spa (continuous_iotaC) (fun x hx =>
      plus_le_comap_of_norm_le ϖ (iotaC K) (fun a => le_of_eq (norm_iotaC K a)) hx) hv
  constructor
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hcomap, fun t ht => ?_, fun h0 => hs0 ?_⟩
    · rw [comap_vle]
      exact hvle (iotaC K t) (Finset.mem_image_of_mem _ ht)
    · have := (comap_vle (iotaC K) v D.s 0)
      rw [map_zero] at this
      rw [show (pushDatumC ϖ D hD).s = iotaC K D.s from rfl, ← this]
      exact h0
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun h0 => hs0 ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have := hvle t ht
      rwa [comap_vle] at this
    · have := (comap_vle (iotaC K) v D.s 0)
      rw [map_zero] at this
      rw [this]
      exact h0

-- (this declaration elaborated fine at the default; the file-wide `false` above makes
-- its `whnf`-checks explode -- restore the default here, as in the Laurent original)
theorem mem_rationalOpen_pushDatumB_iff (D : RationalLocData (JetA K))
    (hD : D.IsRational) (v : Spv (JetB K)) (hv : v ∈ Spa (JetB K) (ringPlus (JetB K))) :
    v ∈ rationalOpen (pushDatumB ϖ D hD).T (pushDatumB ϖ D hD).s ↔
      ValuationSpectrum.comap (jB K) v ∈ rationalOpen D.T D.s := by
  have hcomap : ValuationSpectrum.comap (jB K) v ∈ Spa (JetA K) (ringPlus (JetA K)) :=
    comap_mem_spa (continuous_jB) (fun x hx =>
      plus_le_comap_of_norm_le ϖ (jB K) (norm_jB_le K) hx) hv
  constructor
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hcomap, fun t ht => ?_, fun h0 => hs0 ?_⟩
    · rw [comap_vle]
      exact hvle (jB K t) (Finset.mem_image_of_mem _ ht)
    · have := (comap_vle (jB K) v D.s 0)
      rw [map_zero] at this
      rw [show (pushDatumB ϖ D hD).s = jB K D.s from rfl, ← this]
      exact h0
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun h0 => hs0 ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have := hvle t ht
      rwa [comap_vle] at this
    · have := (comap_vle (jB K) v D.s 0)
      rw [map_zero] at this
      rw [this]
      exact h0

/-- The 𝓓-side pointwise coverage transfer (supporting lemma for `pushCoveringD`). -/
theorem mem_rationalOpen_pushDatumD_iff (D : RationalLocData (JetA K))
    (hD : D.IsRational) (v : Spv (JetD K)) (hv : v ∈ Spa (JetD K) (ringPlus (JetD K))) :
    v ∈ rationalOpen (pushDatumD ϖ D hD).T (pushDatumD ϖ D hD).s ↔
      ValuationSpectrum.comap ((rhoC K).comp (iotaC K)) v ∈ rationalOpen D.T D.s := by
  have hcomap : ValuationSpectrum.comap ((rhoC K).comp (iotaC K)) v ∈
      Spa (JetA K) (ringPlus (JetA K)) :=
    comap_mem_spa (by rw [RingHom.coe_comp]; exact (continuous_rhoC).comp (continuous_iotaC))
      (fun x hx => Subring.mem_comap.mpr
        (plus_le_comap_of_norm_le ϖ ((rhoC K).comp (iotaC K))
          (fun a => le_trans (norm_rhoC_le K (iotaC K a)) (le_of_eq (norm_iotaC K a)))
          (show TopologicalRing.IsPowerBounded x from hx))) hv
  constructor
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hcomap, fun t ht => ?_, fun h0 => hs0 ?_⟩
    · rw [comap_vle]
      exact hvle (((rhoC K).comp (iotaC K)) t) (Finset.mem_image_of_mem _ ht)
    · have := (comap_vle ((rhoC K).comp (iotaC K)) v D.s 0)
      rw [map_zero] at this
      rw [show (pushDatumD ϖ D hD).s = ((rhoC K).comp (iotaC K)) D.s from rfl, ← this]
      exact h0
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun h0 => hs0 ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have := hvle t ht
      rwa [comap_vle] at this
    · have := (comap_vle ((rhoC K).comp (iotaC K)) v D.s 0)
      rw [map_zero] at this
      rw [this]
      exact h0

/-- The pushed covering of a rational covering of 𝓐, at the 𝓒-vertex
([FJP] Lemma 5.2: "Inverse images preserve the defining valuation inequalities and unions.
Hence, for `E = B, C, D`, `U_E = ⋃ᵢ (Uᵢ)_E` is a rational covering"). -/
def pushCoveringC (C : RationalCoveringData (JetA K)) (hC : C.IsRational) :
    RationalCoveringData (JetC K) where
  base := pushDatumC ϖ C.base hC.base
  covers := C.covers.attach.image fun d => pushDatumC ϖ d.1 (hC.piece d.2)
  hsubset := by
    intro D' hD' v hv
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
    have hvspa : v ∈ Spa (JetC K) (ringPlus (JetC K)) := hv.1
    exact (mem_rationalOpen_pushDatumC_iff ϖ C.base hC.base v hvspa).mpr
      (C.hsubset d.1 d.2
        ((mem_rationalOpen_pushDatumC_iff ϖ d.1 (hC.piece d.2) v hvspa).mp hv))
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (JetC K) (ringPlus (JetC K)) := hv.1
    obtain ⟨D₀, hD₀, hmem⟩ := C.hcover _
      ((mem_rationalOpen_pushDatumC_iff ϖ C.base hC.base v hvspa).mp hv)
    exact ⟨pushDatumC ϖ D₀ (hC.piece hD₀),
      Finset.mem_image.mpr ⟨⟨D₀, hD₀⟩, Finset.mem_attach _ _, rfl⟩,
      (mem_rationalOpen_pushDatumC_iff ϖ D₀ (hC.piece hD₀) v hvspa).mpr hmem⟩

def pushCoveringB (C : RationalCoveringData (JetA K)) (hC : C.IsRational) :
    RationalCoveringData (JetB K) where
  base := pushDatumB ϖ C.base hC.base
  covers := C.covers.attach.image fun d => pushDatumB ϖ d.1 (hC.piece d.2)
  hsubset := by
    intro D' hD' v hv
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
    have hvspa : v ∈ Spa (JetB K) (ringPlus (JetB K)) := hv.1
    exact (mem_rationalOpen_pushDatumB_iff ϖ C.base hC.base v hvspa).mpr
      (C.hsubset d.1 d.2
        ((mem_rationalOpen_pushDatumB_iff ϖ d.1 (hC.piece d.2) v hvspa).mp hv))
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (JetB K) (ringPlus (JetB K)) := hv.1
    obtain ⟨D₀, hD₀, hmem⟩ := C.hcover _
      ((mem_rationalOpen_pushDatumB_iff ϖ C.base hC.base v hvspa).mp hv)
    exact ⟨pushDatumB ϖ D₀ (hC.piece hD₀),
      Finset.mem_image.mpr ⟨⟨D₀, hD₀⟩, Finset.mem_attach _ _, rfl⟩,
      (mem_rationalOpen_pushDatumB_iff ϖ D₀ (hC.piece hD₀) v hvspa).mpr hmem⟩

def pushCoveringD (C : RationalCoveringData (JetA K)) (hC : C.IsRational) :
    RationalCoveringData (JetD K) where
  base := pushDatumD ϖ C.base hC.base
  covers := C.covers.attach.image fun d => pushDatumD ϖ d.1 (hC.piece d.2)
  hsubset := by
    intro D' hD' v hv
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
    have hvspa : v ∈ Spa (JetD K) (ringPlus (JetD K)) := hv.1
    exact (mem_rationalOpen_pushDatumD_iff ϖ C.base hC.base v hvspa).mpr
      (C.hsubset d.1 d.2
        ((mem_rationalOpen_pushDatumD_iff ϖ d.1 (hC.piece d.2) v hvspa).mp hv))
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (JetD K) (ringPlus (JetD K)) := hv.1
    obtain ⟨D₀, hD₀, hmem⟩ := C.hcover _
      ((mem_rationalOpen_pushDatumD_iff ϖ C.base hC.base v hvspa).mp hv)
    exact ⟨pushDatumD ϖ D₀ (hC.piece hD₀),
      Finset.mem_image.mpr ⟨⟨D₀, hD₀⟩, Finset.mem_attach _ _, rfl⟩,
      (mem_rationalOpen_pushDatumD_iff ϖ D₀ (hC.piece hD₀) v hvspa).mpr hmem⟩

theorem pushCoveringB_isRational {C : RationalCoveringData (JetA K)} (hC : C.IsRational) :
    (pushCoveringB ϖ C hC).IsRational := by
  refine ⟨pushDatumB_isRational ϖ hC.base, ?_⟩
  intro D' hD'
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
  exact pushDatumB_isRational ϖ (hC.piece d.2)

theorem pushCoveringC_isRational {C : RationalCoveringData (JetA K)} (hC : C.IsRational) :
    (pushCoveringC ϖ C hC).IsRational := by
  refine ⟨pushDatumC_isRational ϖ hC.base, ?_⟩
  intro D' hD'
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
  exact pushDatumC_isRational ϖ (hC.piece d.2)

theorem pushCoveringD_isRational {C : RationalCoveringData (JetA K)} (hC : C.IsRational) :
    (pushCoveringD ϖ C hC).IsRational := by
  refine ⟨pushDatumD_isRational ϖ hC.base, ?_⟩
  intro D' hD'
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
  exact pushDatumD_isRational ϖ (hC.piece d.2)

/-! ### Intersection data ([FJP] Lemma 5.2: `(U_{ij})_E = (U_i)_E ∩ (U_j)_E`)

The span facts `FiniteJet.span_mul_image_eq_top` / `FiniteJet.span_insert_eq_top` are
generic and reused from the Laurent original. -/

/-- The product-datum span fact, stated at 𝓐 (`s`-normalized factors). -/
theorem interDatum_span_eq_top (D₁ D₂ : RationalLocData (JetA K))
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) :
    Ideal.span ((((insert D₁.s D₁.T ×ˢ insert D₂.s D₂.T).image
      fun p => p.1 * p.2 : Finset (JetA K))) : Set (JetA K)) = ⊤ :=
  span_mul_image_eq_top (span_insert_eq_top D₁.s h₁.span_eq_top)
    (span_insert_eq_top D₂.s h₂.span_eq_top)

/-- The product (intersection) datum of two rational data ([FJP] Lemma 5.2 uses
`U_{ij} = U_i ∩ U_j`, "which is again rational"). The factors are `s`-normalized
(`insert sᵢ Tᵢ`) so that the pointwise intersection formula `rationalOpen_interDatum`
holds — `R(T/s) = R((T ∪ {s})/s)` on opens, but only the normalized product datum cuts
out the intersection. -/
def interDatum (D₁ D₂ : RationalLocData (JetA K))
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) : RationalLocData (JetA K) where
  P := podA K ϖ
  T := (insert D₁.s D₁.T ×ˢ insert D₂.s D₂.T).image fun p => p.1 * p.2
  s := D₁.s * D₂.s
  hopen := genPiece_hopen (podA K ϖ)
    ((insert D₁.s D₁.T ×ˢ insert D₂.s D₂.T).image fun p => p.1 * p.2)
    (D₁.s * D₂.s) (interDatum_span_eq_top D₁ D₂ h₁ h₂)

theorem rationalOpen_interDatum (D₁ D₂ : RationalLocData (JetA K))
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) :
    rationalOpen (interDatum ϖ D₁ D₂ h₁ h₂).T (interDatum ϖ D₁ D₂ h₁ h₂).s =
      rationalOpen D₁.T D₁.s ∩ rationalOpen D₂.T D₂.s := by
  ext v
  constructor
  · rintro ⟨hspa, hvle, hs0⟩
    have hs₁0 : ¬ v.vle D₁.s 0 := fun h0 => hs0 (by
      have := v.mul_vle_mul_left h0 D₂.s
      rwa [zero_mul] at this)
    have hs₂0 : ¬ v.vle D₂.s 0 := fun h0 => hs0 (by
      have := v.mul_vle_mul_left h0 D₁.s
      rw [zero_mul, mul_comm D₂.s D₁.s] at this
      exact this)
    refine ⟨⟨hspa, fun t ht => ?_, hs₁0⟩, ⟨hspa, fun t ht => ?_, hs₂0⟩⟩
    · have hpair : t * D₂.s ∈ (interDatum ϖ D₁ D₂ h₁ h₂).T :=
        Finset.mem_image.mpr ⟨(t, D₂.s), Finset.mem_product.mpr
          ⟨Finset.mem_insert_of_mem ht, Finset.mem_insert_self _ _⟩, rfl⟩
      exact v.vle_mul_cancel hs₂0 (hvle _ hpair)
    · have hpair : D₁.s * t ∈ (interDatum ϖ D₁ D₂ h₁ h₂).T :=
        Finset.mem_image.mpr ⟨(D₁.s, t), Finset.mem_product.mpr
          ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ht⟩, rfl⟩
      have h' := hvle _ hpair
      rw [show D₁.s * t = t * D₁.s from mul_comm _ _,
        show (interDatum ϖ D₁ D₂ h₁ h₂).s = D₂.s * D₁.s from mul_comm _ _] at h'
      exact v.vle_mul_cancel hs₁0 h'
  · rintro ⟨⟨hspa, hvle₁, hs₁0⟩, ⟨-, hvle₂, hs₂0⟩⟩
    have hvle₁' : ∀ t₁ ∈ insert D₁.s D₁.T, v.vle t₁ D₁.s := by
      intro t₁ ht₁
      rcases Finset.mem_insert.mp ht₁ with h | h
      · subst h; exact (v.vle_total _ _).elim id id
      · exact hvle₁ t₁ h
    have hvle₂' : ∀ t₂ ∈ insert D₂.s D₂.T, v.vle t₂ D₂.s := by
      intro t₂ ht₂
      rcases Finset.mem_insert.mp ht₂ with h | h
      · subst h; exact (v.vle_total _ _).elim id id
      · exact hvle₂ t₂ h
    refine ⟨hspa, fun t' ht' => ?_, fun h0 => ?_⟩
    · obtain ⟨⟨t₁, t₂⟩, hmem, rfl⟩ := Finset.mem_image.mp ht'
      obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp hmem
      have ha := v.mul_vle_mul_left (hvle₁' t₁ ht₁) t₂
      have hb := v.mul_vle_mul_left (hvle₂' t₂ ht₂) D₁.s
      rw [mul_comm t₂ D₁.s, mul_comm D₂.s D₁.s] at hb
      exact v.vle_trans ha hb
    · rw [show (interDatum ϖ D₁ D₂ h₁ h₂).s = D₁.s * D₂.s from rfl,
        show (0 : JetA K) = 0 * D₂.s from (zero_mul _).symm] at h0
      exact hs₁0 (v.vle_mul_cancel hs₂0 h0)

theorem interDatum_isRational {D₁ D₂ : RationalLocData (JetA K)}
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) : (interDatum ϖ D₁ D₂ h₁ h₂).IsRational :=
  RationalLocData.isRational_of_span_eq_top (interDatum_span_eq_top D₁ D₂ h₁ h₂)

end

end FiniteJetOver
