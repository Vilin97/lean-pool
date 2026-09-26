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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetStrictLocalization
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetUniformDomain
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FaithfulLocLift
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafFunctoriality

/-!
# Functoriality layer: pushing rational data along the square, graph bridges, and
`HasLocLiftPowerBounded 𝓐`

Sources: [FJP] Lemma 1.1 (graph realization of rational localization — the universal
property), Lemma 4.6 (naturality), Lemma 5.1 (naturality on the rational basis: "For every
rational domain `U ⊂ X`, its inverse image `U_E = p_E⁻¹(U)` is the rational domain in `Y_E`
defined by the image of the same datum").

This file supplies what the survey identified as the missing covariant layer:

* pairs of definition for the four rings (unit balls with the pseudouniformizer ideal);
* `pushDatumB/C/D : RationalLocData 𝓐 → RationalLocData E` (image datum; `hopen` via the
  generic span-⊤/principal-pod argument);
* `presheafValueMap : 𝒪_𝓐(D) → 𝒪_E(D_E)` (localization functoriality + completion), and its
  naturality with `restrictionMap`;
* the **graph bridge** `𝒪_E(D) ≃+* P_E ⧸ I_E` ([FJP] Lemma 1.1 + (4.21)), topological in
  both directions — the identification of the project's completed localization with the
  Banach graph quotient, for `E = 𝓐` (closed ideal by Lemma 4.3) and the three vertices
  (closed by Lemma 4.2);
* pushed coverings, intersection data, and the Spa-point coverage transfer (via the
  project's contravariant `spaComap`);
* `HasLocLiftPowerBounded 𝓐`, derived **componentwise through the Milnor square** from the
  vertices' instances (the project discharger is noetherian-bound and 𝓐 is not noetherian).
-/

@[expose] public section

open Filter Topology

-- v4.33 (file-wide): the closed-ideal quotient-norm chains through the `PA`/`locA`
-- defs (`Submodule.Quotient.normedAddCommGroup`, `locA_t2`, `locA_completeSpace`, …)
-- are used in a dozen declarations here and their instance unification needs
-- semireducible unfolding; restore pre-v4.33 defeq behaviour for this FJP-internal
-- file (established bump-repair pattern, cf. FiniteJetStrictLocalization).

namespace FiniteJet

open RestrictedLaurent ValuationSpectrum StrictLoc

variable (F : Type*) [Field F]

local notation "K" => LaurentSeries F

noncomputable section

open scoped Classical

/-! ### Pairs of definition -/

/-- The unit-ball pair of definition of 𝓐 (the generic `unitBallPod` at `tA`). -/
def podA : PairOfDefinition (JetA F) :=
  unitBallPod (tA F) (isUnit_tA F) (norm_tA_lt_one F) (norm_tA_pos F) (norm_tA_mul F)

def podB : PairOfDefinition (JetB F) :=
  unitBallPod (tB F) (isUnit_tB F) (by rw [norm_tB]; exact norm_t_lt_one F)
    (by rw [norm_tB]; exact norm_t_pos F) (norm_tB_mul F)

def podC : PairOfDefinition (JetC F) :=
  unitBallPod (tC F) (isUnit_tC F) (by rw [norm_tC]; exact norm_t_lt_one F)
    (by rw [norm_tC]; exact norm_t_pos F) (norm_tC_mul F)

def podD : PairOfDefinition (JetD F) :=
  unitBallPod (tD F) (isUnit_tD F) (by rw [norm_tD]; exact norm_t_lt_one F)
    (by rw [norm_tD]; exact norm_t_pos F) (norm_tD_mul F)

/-! ### Pushing rational localization data ([FJP] Lemma 5.1)

The `hopen` field for the pushed datum is the generic bounded-denominator statement for
span-⊤ data over a principal pair of definition in a Tate ring (risk item 3 of `plan.md`). -/

variable {F}

/-- Spans of finset images of spanning sets span (the `Ideal.map` argument). -/
theorem span_image_eq_top {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B)
    {T : Finset A} (h : Ideal.span (T : Set A) = ⊤) :
    Ideal.span ((T.image φ : Finset B) : Set B) = ⊤ := by
  have hmap := congrArg (Ideal.map φ) h
  rw [Ideal.map_span, Ideal.map_top] at hmap
  rw [Finset.coe_image, ← hmap]

/-- Push a rational datum of 𝓐 to 𝓑 (image datum, [FJP] Lemma 5.1). Signature completion
(recorded): rationality of `D` is required to discharge `hopen` via the generic span-⊤
computation `genPiece_hopen`. -/
def pushDatumB (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    RationalLocData (JetB F) where
  P := podB F
  T := D.T.image (jB F)
  s := jB F D.s
  hopen := genPiece_hopen (podB F) (D.T.image (jB F)) (jB F D.s)
    (span_image_eq_top (jB F) hD.span_eq_top)

/-- Push a rational datum of 𝓐 to 𝓒. -/
def pushDatumC (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    RationalLocData (JetC F) where
  P := podC F
  T := D.T.image (iotaC F)
  s := iotaC F D.s
  hopen := genPiece_hopen (podC F) (D.T.image (iotaC F)) (iotaC F D.s)
    (span_image_eq_top (iotaC F) hD.span_eq_top)

/-- Push a rational datum of 𝓐 to 𝓓. -/
def pushDatumD (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    RationalLocData (JetD F) where
  P := podD F
  T := D.T.image ((rhoC F).comp (iotaC F))
  s := rhoC F (iotaC F D.s)
  hopen := genPiece_hopen (podD F) (D.T.image ((rhoC F).comp (iotaC F)))
    (rhoC F (iotaC F D.s))
    (span_image_eq_top ((rhoC F).comp (iotaC F)) hD.span_eq_top)

theorem pushDatumB_isRational {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    (pushDatumB D hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_eq_top (jB F) hD.span_eq_top)

theorem pushDatumC_isRational {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    (pushDatumC D hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_eq_top (iotaC F) hD.span_eq_top)

theorem pushDatumD_isRational {D : RationalLocData (JetA F)} (hD : D.IsRational) :
    (pushDatumD D hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (span_image_eq_top ((rhoC F).comp (iotaC F)) hD.span_eq_top)

/-! ### Covariant maps on presheaf values

Generic layer: for a continuous ring homomorphism `φ : R →+* S` and rational data
`D`/`D'` with `D'.s = φ D.s` and `φ(D.T) ⊆ D'.T`, the localization functor gives
`Localization.Away D.s →+* Localization.Away D'.s`; it is continuous for the
localization topologies by the universal property `locTopology_continuous_lift` (the
generators land in `locSubring D'`, hence are power-bounded — no Nullstellensatz input
needed, unlike the restriction maps); completing gives `𝒪(D) →+* 𝒪(D')`. -/

-- (the generic `CovariantPush` functoriality moved to
-- `PresheafFunctoriality.lean`, `namespace ValuationSpectrum`; reused here via `open`.)


/-! ### Continuity of the square's maps (norm bounds ⇒ 1-Lipschitz) -/

theorem continuous_jB : Continuous (jB F) :=
  AddMonoidHomClass.continuous_of_bound (jB F) 1 fun a => by
    rw [one_mul]; exact norm_jB_le F a

theorem continuous_iotaC : Continuous (iotaC F) :=
  AddMonoidHomClass.continuous_of_bound (iotaC F) 1 fun a => by
    rw [one_mul, norm_iotaC]

theorem continuous_rhoC : Continuous (rhoC F) :=
  AddMonoidHomClass.continuous_of_bound (rhoC F) 1 fun a => by
    rw [one_mul]; exact norm_rhoC_le F a

/-- The induced map on completed rational localizations along `ιC` ([FJP] Lemma 5.1's
`𝒪_X(U) → 𝒪_{Y_C}(U_C)`; built from `IsLocalization` functoriality, continuity for the
localization topologies, and `UniformSpace.Completion` functoriality). -/
noncomputable def presheafValueMapC (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    presheafValue D →+* presheafValue (pushDatumC D hD) :=
  presheafValueMapOfHom (iotaC F) (continuous_iotaC) D (pushDatumC D hD) rfl
    (fun _ ht => Finset.mem_image_of_mem _ ht)

noncomputable def presheafValueMapB (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    presheafValue D →+* presheafValue (pushDatumB D hD) :=
  presheafValueMapOfHom (jB F) (continuous_jB) D (pushDatumB D hD) rfl
    (fun _ ht => Finset.mem_image_of_mem _ ht)

noncomputable def presheafValueMapD (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    presheafValue D →+* presheafValue (pushDatumD D hD) :=
  presheafValueMapOfHom ((rhoC F).comp (iotaC F))
    (by rw [RingHom.coe_comp]; exact (continuous_rhoC).comp (continuous_iotaC))
    D (pushDatumD D hD) rfl (fun _ ht => Finset.mem_image_of_mem _ ht)

theorem presheafValueMapC_continuous (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    Continuous (presheafValueMapC D hD) :=
  presheafValueMapOfHom_continuous _ _ _ _ _ _

theorem presheafValueMapB_continuous (D : RationalLocData (JetA F)) (hD : D.IsRational) :
    Continuous (presheafValueMapB D hD) :=
  presheafValueMapOfHom_continuous _ _ _ _ _ _

theorem presheafValueMapC_canonicalMap (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (a : JetA F) :
    presheafValueMapC D hD (D.canonicalMap a) =
      (pushDatumC D hD).canonicalMap (iotaC F a) :=
  presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ a

theorem presheafValueMapB_canonicalMap (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (a : JetA F) :
    presheafValueMapB D hD (D.canonicalMap a) =
      (pushDatumB D hD).canonicalMap (jB F a) :=
  presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ a

/-! ### The graph bridge ([FJP] Lemma 1.1 + (4.21))

For an indexed enumeration `(g, f)` of a rational datum `(T, s)` (with `g = s`), the
project's completed rational localization is topologically the Banach graph quotient. -/

/-- An indexed enumeration of a `RationalLocData`: `f` lists `T`, `g = s`. -/
structure DatumEnum (D : RationalLocData (JetA F)) where
  /-- The arity. -/
  m : ℕ
  /-- The enumeration of `T`. -/
  f : Fin m → JetA F
  /-- Enumeration covers `T`. -/
  hf : ∀ t ∈ D.T, ∃ i, f i = t
  /-- Enumeration lands in `T`. -/
  hf' : ∀ i, f i ∈ D.T

/-- The canonical enumeration of a rational datum (via `Finset.equivFin`). -/
noncomputable def datumEnum (D : RationalLocData (JetA F)) : DatumEnum D where
  m := D.T.card
  f := fun i => (D.T.equivFin.symm i : JetA F)
  hf := fun t ht => ⟨D.T.equivFin ⟨t, ht⟩, by rw [Equiv.symm_apply_apply]⟩
  hf' := fun i => (D.T.equivFin.symm i).2

section GraphBridgeInfra

open GraphKoszul

/-- Quotients of ultrametric seminormed rings are ultrametric: the quotient norm
inherits the max inequality up to `ε` via near-optimal representatives. -/
instance instIsUltrametricDistIdealQuotient {R : Type*} [SeminormedCommRing R]
    [IsUltrametricDist R] (I : Ideal R) : IsUltrametricDist (R ⧸ I) where
  dist_triangle_max x y z := by
    rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨a, ha, han⟩ := Ideal.Quotient.norm_mk_lt (x - y) hε
    obtain ⟨b, hb, hbn⟩ := Ideal.Quotient.norm_mk_lt (y - z) hε
    have hxz : x - z = Ideal.Quotient.mk I (a + b) := by rw [map_add, ha, hb]; ring
    calc ‖x - z‖ = ‖Ideal.Quotient.mk I (a + b)‖ := by rw [hxz]
      _ ≤ ‖a + b‖ := Ideal.Quotient.norm_mk_le _ _
      _ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max a b
      _ ≤ max (‖x - y‖ + ε) (‖y - z‖ + ε) := max_le_max han.le hbn.le
      _ = max ‖x - y‖ ‖y - z‖ + ε := max_add_add_right _ _ _

variable (D : RationalLocData (JetA F)) (e : DatumEnum D)

/-- The enumerated datum spans `({s} ∪ range f) = ⊤` (rationality + covering). -/
theorem DatumEnum.span_eq_top (hD : D.IsRational) :
    Ideal.span ({D.s} ∪ Set.range e.f) = ⊤ := by
  rw [← top_le_iff, ← hD.span_eq_top]
  refine Ideal.span_mono fun t ht => ?_
  obtain ⟨i, rfl⟩ := e.hf t ht
  exact Set.mem_union_right _ ⟨i, rfl⟩

/-- Scalars into `P_𝓐` (constant restricted series). -/
noncomputable def bridgeConst (m : ℕ) : JetA F →+* PA F m :=
  polyToP.comp MvPolynomial.C

/-- The base map `𝓐 → 𝓐_α = P_𝓐 ⧸ I_𝓐` (constants, then the graph quotient). -/
noncomputable def bridgeBase : JetA F →+* locA F e.m D.s e.f :=
  (Ideal.Quotient.mk (IA F e.m D.s e.f)).comp (bridgeConst e.m)

/-- The variable images `X̄ᵢ ∈ 𝓐_α`. -/
noncomputable def bridgeX (i : Fin e.m) : locA F e.m D.s e.f :=
  Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.X i))

/-- The graph relation in the quotient: `s̄ · X̄ᵢ = f̄ᵢ` ([FJP] (4.6)). -/
theorem bridgeBase_s_mul_X (i : Fin e.m) :
    bridgeBase D e D.s * bridgeX D e i = bridgeBase D e (e.f i) := by
  have hmem : polyToP (MvPolynomial.C D.s) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (e.f i)) ∈ IA F e.m D.s e.f := by
    have hrw : rA F e.m D.s e.f i =
        polyToP (MvPolynomial.C D.s) * polyToP (MvPolynomial.X i) -
          polyToP (MvPolynomial.C (e.f i)) := by
      rw [rA, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.C D.s)) *
      Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.C (e.f i)))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (IA F e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

/-- `s̄` is a unit in `𝓐_α` ([FJP] (4.3): the span decomposition
`1 = c·s + Σ dᵢ·fᵢ` becomes `1 = s̄·(c̄ + Σ d̄ᵢ X̄ᵢ)` after the graph relations). -/
theorem isUnit_bridgeBase_s (hD : D.IsRational) : IsUnit (bridgeBase D e D.s) := by
  have h1 : (1 : JetA F) ∈ Ideal.span ({D.s} ∪ Set.range e.f) := by
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

/- `instNonarchimedeanRingOfSeminormedUltra` moved to `FiniteJetRings.lean` (the
definition layer), so the comparator challenge and the full library resolve
`NonarchimedeanRing (JetA F)` identically. -/

/-- Norm-≤-1 elements of a seminormed comm ring are power-bounded. -/
theorem isPowerBounded_of_norm_le_one {R : Type*} [SeminormedCommRing R] {x : R}
    (hx : ‖x‖ ≤ 1) : TopologicalRing.IsPowerBounded x := by
  have hM : ∀ n : ℕ, ‖x ^ n‖ ≤ max ‖(1 : R)‖ 1 := by
    intro n
    cases n with
    | zero => simp only [pow_zero]; exact le_max_left _ _
    | succ k =>
      refine le_trans (norm_pow_le' x k.succ_pos) (le_max_of_le_right ?_)
      exact pow_le_one₀ (norm_nonneg _) hx
  have hMpos : (0 : ℝ) < max ‖(1 : R)‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  intro U hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨Metric.ball 0 (ε / max ‖(1 : R)‖ 1),
    Metric.ball_mem_nhds 0 (by positivity), ?_⟩
  rintro z ⟨s, ⟨n, rfl⟩, y, hy, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hy
  refine hball ?_
  rw [Metric.mem_ball, dist_zero_right]
  calc ‖x ^ n * y‖ ≤ ‖x ^ n‖ * ‖y‖ := norm_mul_le _ _
    _ ≤ max ‖(1 : R)‖ 1 * ‖y‖ := by
        exact mul_le_mul_of_nonneg_right (hM n) (norm_nonneg y)
    _ < max ‖(1 : R)‖ 1 * (ε / max ‖(1 : R)‖ 1) :=
        mul_lt_mul_of_pos_left hy hMpos
    _ = ε := mul_div_cancel₀ _ (ne_of_gt hMpos)

/-- The Gauss norm (radius 1) of a variable is at most one. -/
theorem gaussNorm_X_le_one {S : Type*} [NormedCommRing S] [NormOneClass S] {m : ℕ} (i : Fin m) :
    MvPowerSeries.gaussNorm (norm : S → ℝ) (fun _ : Fin m => (1 : ℝ))
      ((MvPolynomial.X i : MvPolynomial (Fin m) S) : MvPowerSeries (Fin m) S) ≤ 1 := by
  classical
  refine Real.iSup_le (fun t => ?_) zero_le_one
  have hprod : (t.prod fun _ k => (1 : ℝ) ^ k) = 1 := by
    simp
  rw [hprod, mul_one, MvPolynomial.coeff_coe, MvPolynomial.coeff_X]
  split
  · simp
  · simp

/-- `‖X̄ᵢ‖ ≤ 1` in the graph quotient. -/
theorem norm_bridgeX_le_one (i : Fin e.m) : ‖bridgeX D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact gaussNorm_X_le_one (S := JetA F) i

/-- `bridgeBase` is norm-nonincreasing (constants keep their norm, quotients contract). -/
theorem norm_bridgeBase_le (a : JetA F) : ‖bridgeBase D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := JetA F) (m := e.m) (MvPolynomial.C a) : PA F e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := JetA F) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetA F) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The loc-level forward map `A_s → 𝓐_α` (`IsLocalization.Away.lift` at the unit `s̄`). -/
noncomputable def bridgeLocHom (hD : D.IsRational) :
    Localization.Away D.s →+* locA F e.m D.s e.f :=
  IsLocalization.Away.lift D.s (isUnit_bridgeBase_s D e hD)

theorem bridgeLocHom_algebraMap (hD : D.IsRational) (a : JetA F) :
    bridgeLocHom D e hD (algebraMap (JetA F) (Localization.Away D.s) a) =
      bridgeBase D e a :=
  IsLocalization.Away.lift_eq _ _ a

/-- The forward map sends the rational generator `fᵢ/s` to the variable `X̄ᵢ`. -/
theorem bridgeLocHom_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHom D e hD (divByS (e.f i) D.s) = bridgeX D e i := by
  have hu := isUnit_bridgeBase_s D e hD
  have hspec : divByS (e.f i) D.s * algebraMap (JetA F) (Localization.Away D.s) D.s =
      algebraMap (JetA F) (Localization.Away D.s) (e.f i) := by
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
        (algebraMap (JetA F) (Localization.Away D.s)) = bridgeBase D e := by
      ext a; exact bridgeLocHom_algebraMap D e hD a
    rw [show ⇑((bridgeLocHom D e hD).comp
        (algebraMap (JetA F) (Localization.Away D.s)))
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
    presheafValue D →+* locA F e.m D.s e.f := by
  haveI hcl : IsClosed ((IA F e.m D.s e.f : Set (PA F e.m))) :=
    isClosed_IA F e.m D.s e.f (e.span_eq_top D hD)
  haveI : NormedAddCommGroup (locA F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  haveI : T2Space (locA F e.m D.s e.f) := locA_t2 F e.m D.s e.f (e.span_eq_top D hD)
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (bridgeLocHom D e hD)
    (bridgeLocHom_continuous D e hD)

theorem bridgeFwd_coe (hD : D.IsRational) (a : Localization.Away D.s) :
    bridgeFwd D e hD (D.coeRingHom a) = bridgeLocHom D e hD a := by
  haveI hcl : IsClosed ((IA F e.m D.s e.f : Set (PA F e.m))) :=
    isClosed_IA F e.m D.s e.f (e.span_eq_top D hD)
  haveI : NormedAddCommGroup (locA F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  haveI : T2Space (locA F e.m D.s e.f) := locA_t2 F e.m D.s e.f (e.span_eq_top D hD)
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (bridgeLocHom D e hD)
    (bridgeLocHom_continuous D e hD) a

theorem bridgeFwd_canonicalMap (hD : D.IsRational) (a : JetA F) :
    bridgeFwd D e hD (D.canonicalMap a) = bridgeBase D e a := by
  rw [show D.canonicalMap a =
      D.coeRingHom (algebraMap (JetA F) (Localization.Away D.s) a) from rfl,
    bridgeFwd_coe, bridgeLocHom_algebraMap]

theorem bridgeFwd_continuous (hD : D.IsRational) :
    Continuous (bridgeFwd D e hD) := by
  letI := D.uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-! #### The reverse direction: evaluation `P_𝓐 → 𝒪_𝓐(D)` ([FJP] Lemma 1.1, bound (1.3)) -/

/-- Norm-decay restricted series are topologically restricted (the two restricted power
series notions agree over a normed base). -/
noncomputable def bridgeToRestricted (m : ℕ) :
    PA F m →+* ↥(restrictedMvPowerSeriesSubring m (JetA F)) where
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
`locSubring`; mirrors `example638_genTuple_isBounded`). -/
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
noncomputable def bridgeEval : PA F e.m →+* presheafValue D :=
  (mvEvalHomBounded D.canonicalMap (canonicalMap_continuous D)
    (bridgeGen D e) (bridgeGen_isBounded D e)).comp (bridgeToRestricted e.m)

theorem bridgeEval_const (a : JetA F) :
    bridgeEval D e (polyToP (MvPolynomial.C a)) = D.canonicalMap a := by
  have hcast : bridgeToRestricted (F := F) e.m (polyToP (MvPolynomial.C a)) =
      algebraMap (JetA F) ↥(restrictedMvPowerSeriesSubring e.m (JetA F)) a := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetA F) (m := e.m) (MvPolynomial.C a)).1 :
      MvPowerSeries (Fin e.m) (JetA F)) = _
    rw [show (polyToP (E := JetA F) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetA F) a from MvPolynomial.coe_C a]
    rfl
  rw [bridgeEval, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_algebraMap _ _ _ _ a

theorem bridgeEval_X (i : Fin e.m) :
    bridgeEval D e (polyToP (MvPolynomial.X i)) = bridgeGen D e i := by
  have hcast : bridgeToRestricted (F := F) e.m (polyToP (MvPolynomial.X i)) =
      ⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetA F) (m := e.m) (MvPolynomial.X i)).1 :
      MvPowerSeries (Fin e.m) (JetA F)) = _
    exact MvPolynomial.coe_X i
  rw [bridgeEval, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_X _ _ _ _ i

/-- The evaluation kills the graph ideal (`s·(fᵢ/s) = fᵢ` in the localization). -/
theorem IA_le_ker_bridgeEval : IA F e.m D.s e.f ≤ RingHom.ker (bridgeEval D e) := by
  rw [IA, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  have hval : bridgeEval D e (rA F e.m D.s e.f i) =
      D.canonicalMap D.s * bridgeGen D e i - D.canonicalMap (e.f i) :=
    (map_sub ((bridgeEval D e).comp polyToP)
        (MvPolynomial.C D.s * MvPolynomial.X i) (MvPolynomial.C (e.f i))).trans
      (congrArg₂ (· - ·)
        ((map_mul ((bridgeEval D e).comp polyToP)
            (MvPolynomial.C D.s) (MvPolynomial.X i)).trans
          (congrArg₂ (· * ·) (bridgeEval_const D e D.s) (bridgeEval_X D e i)))
        (bridgeEval_const D e (e.f i)))
  rw [hval, sub_eq_zero, bridgeGen]
  rw [show D.canonicalMap D.s = D.coeRingHom (algebraMap (JetA F)
      (Localization.Away D.s) D.s) from rfl, ← RingHom.map_mul D.coeRingHom,
    show algebraMap (JetA F) (Localization.Away D.s) D.s * divByS (e.f i) D.s =
      algebraMap (JetA F) (Localization.Away D.s) (e.f i) from by
    rw [mul_comm, divByS, IsLocalization.mk'_spec]]
  rfl

/-- Reverse: `𝓐_α → 𝒪_𝓐(D)` (the evaluation factors through the graph quotient). -/
noncomputable def bridgeRev : locA F e.m D.s e.f →+* presheafValue D :=
  Ideal.Quotient.lift (IA F e.m D.s e.f) (bridgeEval D e)
    (fun _ ha => RingHom.mem_ker.mp (IA_le_ker_bridgeEval D e ha))

theorem bridgeRev_mk (p : PA F e.m) :
    bridgeRev D e (Ideal.Quotient.mk (IA F e.m D.s e.f) p) = bridgeEval D e p := rfl

theorem bridgeRev_bridgeBase (a : JetA F) :
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
  have hpre : D.canonicalMap ⁻¹' V ∈ nhds (0 : JetA F) :=
    (canonicalMap_continuous D).continuousAt.preimage_mem_nhds (by rwa [map_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : PA F e.m) hδ) ?_
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
  rw [(QuotientRing.isOpenQuotientMap_mk (IA F e.m D.s e.f)).isQuotientMap.continuous_iff]
  exact bridgeEval_continuous D e

/-! #### Round trips (density + Hausdorff equalizers) -/

/-- Polynomials are dense in `P_𝓐` (truncate below any coefficient-norm level). -/
theorem polyToP_denseRange (m : ℕ) :
    DenseRange (polyToP : MvPolynomial (Fin m) (JetA F) → PA F m) := by
  classical
  rw [Metric.denseRange_iff]
  intro p ε hε
  refine ⟨∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
    MvPolynomial.monomial s (MvPowerSeries.coeff s p.1), ?_⟩
  rw [dist_eq_norm, MvRestricted.norm_eq, MvPowerSeries.gaussNorm]
  refine lt_of_le_of_lt (Real.iSup_le (fun s => ?_) (half_pos hε).le) (half_lt_self hε)
  rw [finsupp_prod_one, mul_one]
  show ‖MvPowerSeries.coeff s ((p - polyToP _ : PA F m)).1‖ ≤ ε / 2
  rw [show ((p - polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1)) : PA F m)).1 =
    p.1 - (polyToP (∑ s ∈ (finite_setOf_le_norm_coeff p (half_pos hε)).toFinset,
      MvPolynomial.monomial s (MvPowerSeries.coeff s p.1) : MvPolynomial (Fin m)
        (JetA F))).1 from rfl, map_sub, coeff_polyToP, MvPolynomial.coeff_sum]
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
    bridgeRev D e (bridgeFwd D e hD x) = x := by
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
  have hagree : (fun y => bridgeRev D e (bridgeFwd D e hD y)) ∘ D.coeRingHom =
      (fun y => y) ∘ (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    funext a
    show bridgeRev D e (bridgeFwd D e hD (D.coeRingHom a)) = D.coeRingHom a
    rw [bridgeFwd_coe]
    exact DFunLike.congr_fun hcomp a
  have h_eq : (fun y => bridgeRev D e (bridgeFwd D e hD y)) = fun y => y :=
    hdense.equalizer ((bridgeRev_continuous D e).comp (bridgeFwd_continuous D e hD))
      continuous_id hagree
  exact congrFun h_eq x

/-- The graph-quotient projection is continuous (`1`-Lipschitz for the quotient norm). -/
theorem mkIA_continuous :
    Continuous (Ideal.Quotient.mk (IA F e.m D.s e.f)) :=
  AddMonoidHomClass.continuous_of_bound (Ideal.Quotient.mk (IA F e.m D.s e.f)) 1
    fun a => by rw [one_mul]; exact Ideal.Quotient.norm_mk_le _ a

/-- `fwd ∘ rev = id` on `𝓐_α` (agreement on constants and variables, hence on the dense
polynomial image; extend by density to the Banach quotient). -/
theorem bridgeFwd_bridgeRev (hD : D.IsRational) (y : locA F e.m D.s e.f) :
    bridgeFwd D e hD (bridgeRev D e y) = y := by
  haveI hcl : IsClosed ((IA F e.m D.s e.f : Set (PA F e.m))) :=
    isClosed_IA F e.m D.s e.f (e.span_eq_top D hD)
  haveI : NormedAddCommGroup (locA F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  haveI : T2Space (locA F e.m D.s e.f) := locA_t2 F e.m D.s e.f (e.span_eq_top D hD)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hmkcont : Continuous (Ideal.Quotient.mk (IA F e.m D.s e.f)) :=
    mkIA_continuous D e
  have hpoly : ∀ q : MvPolynomial (Fin e.m) (JetA F),
      bridgeFwd D e hD (bridgeEval D e (polyToP q)) =
        Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP q) := by
    have hhomeq : ((bridgeFwd D e hD).comp ((bridgeEval D e).comp polyToP)) =
        (Ideal.Quotient.mk (IA F e.m D.s e.f)).comp
          (polyToP : MvPolynomial (Fin e.m) (JetA F) →+* PA F e.m) := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
      · show bridgeFwd D e hD (bridgeEval D e (polyToP (MvPolynomial.C a))) =
          Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.C a))
        rw [bridgeEval_const, bridgeFwd_canonicalMap]
        rfl
      · show bridgeFwd D e hD (bridgeEval D e (polyToP (MvPolynomial.X i))) =
          Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.X i))
        rw [bridgeEval_X, bridgeGen, bridgeFwd_coe, bridgeLocHom_divByS]
        rfl
    intro q
    exact DFunLike.congr_fun hhomeq q
  have h_eq : (fun z : PA F e.m => bridgeFwd D e hD (bridgeEval D e z)) =
      fun z : PA F e.m => Ideal.Quotient.mk (IA F e.m D.s e.f) z := by
    refine (polyToP_denseRange e.m).equalizer
      ((bridgeFwd_continuous D e hD).comp (bridgeEval_continuous D e)) hmkcont ?_
    funext q
    exact hpoly q
  exact congrFun h_eq p

/-! #### The 𝓒-side forward bridge (for the [FJP] Lemma 5.1 naturality square) -/

/-- The base map `𝓒 → 𝓒_α` (constants into the 𝓒-graph quotient). -/
noncomputable def bridgeBaseC : JetC F →+* locC F e.m D.s e.f :=
  (Ideal.Quotient.mk (IC F e.m D.s e.f)).comp
    ((polyToP : MvPolynomial (Fin e.m) (JetC F) →+* PC F e.m).comp MvPolynomial.C)

/-- The variable images `X̄ᵢ ∈ 𝓒_α`. -/
noncomputable def bridgeXC (i : Fin e.m) : locC F e.m D.s e.f :=
  Ideal.Quotient.mk (IC F e.m D.s e.f) (polyToP (MvPolynomial.X i))

theorem bridgeBaseC_s_mul_X (i : Fin e.m) :
    bridgeBaseC D e (iotaC F D.s) * bridgeXC D e i =
      bridgeBaseC D e (iotaC F (e.f i)) := by
  have hmem : polyToP (MvPolynomial.C (iotaC F D.s)) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (iotaC F (e.f i))) ∈ IC F e.m D.s e.f := by
    have hrw : rC F e.m D.s e.f i = polyToP (MvPolynomial.C (iotaC F D.s)) *
        polyToP (MvPolynomial.X i) - polyToP (MvPolynomial.C (iotaC F (e.f i))) := by
      rw [rC_eq, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (IC F e.m D.s e.f) (polyToP (MvPolynomial.C (iotaC F D.s))) *
      Ideal.Quotient.mk (IC F e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (IC F e.m D.s e.f) (polyToP (MvPolynomial.C (iotaC F (e.f i))))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (IC F e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

theorem isUnit_bridgeBaseC_s (hD : D.IsRational) :
    IsUnit (bridgeBaseC D e (iotaC F D.s)) := by
  have h1 : (1 : JetC F) ∈
      Ideal.span ({iotaC F D.s} ∪ Set.range fun i => iotaC F (e.f i)) := by
    rw [span_pushed_C F e.m D.s e.f (e.span_eq_top D hD)]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBaseC D e (d i * iotaC F (e.f i)) =
      bridgeBaseC D e (d i) * (bridgeBaseC D e (iotaC F D.s) * bridgeXC D e i) :=
    fun i => by rw [RingHom.map_mul (bridgeBaseC D e), bridgeBaseC_s_mul_X]
  have happ : bridgeBaseC D e c * bridgeBaseC D e (iotaC F D.s) +
      ∑ i, bridgeBaseC D e (d i) * (bridgeBaseC D e (iotaC F D.s) * bridgeXC D e i) = 1 := by
    have h0 := congrArg (bridgeBaseC D e) hxy
    rw [RingHom.map_one (bridgeBaseC D e), RingHom.map_add (bridgeBaseC D e),
      RingHom.map_mul (bridgeBaseC D e),
      show (bridgeBaseC D e) (∑ i, d i * iotaC F (e.f i)) =
        ∑ i, bridgeBaseC D e (d i * iotaC F (e.f i)) from map_sum (bridgeBaseC D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBaseC D e (iotaC F D.s) *
      (bridgeBaseC D e c + ∑ i, bridgeBaseC D e (d i) * bridgeXC D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBaseC D e (iotaC F D.s) * bridgeBaseC D e c +
        ∑ i, bridgeBaseC D e (iotaC F D.s) * (bridgeBaseC D e (d i) * bridgeXC D e i)
        = bridgeBaseC D e c * bridgeBaseC D e (iotaC F D.s) +
          ∑ i, bridgeBaseC D e (d i) * (bridgeBaseC D e (iotaC F D.s) * bridgeXC D e i) := by
          rw [mul_comm (bridgeBaseC D e (iotaC F D.s)) (bridgeBaseC D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

theorem norm_bridgeXC_le_one (i : Fin e.m) : ‖bridgeXC D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact gaussNorm_X_le_one (S := JetC F) i

theorem norm_bridgeBaseC_le (a : JetC F) : ‖bridgeBaseC D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := JetC F) (m := e.m) (MvPolynomial.C a) : PC F e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := JetC F) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetC F) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The 𝓒-side localization lift. -/
noncomputable def bridgeLocHomC (hD : D.IsRational) :
    Localization.Away (pushDatumC D hD).s →+* locC F e.m D.s e.f :=
  IsLocalization.Away.lift (pushDatumC D hD).s (isUnit_bridgeBaseC_s D e hD)

theorem bridgeLocHomC_algebraMap (hD : D.IsRational) (a : JetC F) :
    bridgeLocHomC D e hD
      (algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s) a) =
      bridgeBaseC D e a :=
  IsLocalization.Away.lift_eq _ _ a

theorem bridgeLocHomC_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHomC D e hD (divByS (iotaC F (e.f i)) (pushDatumC D hD).s) =
      bridgeXC D e i := by
  have hu := isUnit_bridgeBaseC_s D e hD
  have hspec : divByS (iotaC F (e.f i)) (pushDatumC D hD).s *
      algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s) (pushDatumC D hD).s =
      algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s) (iotaC F (e.f i)) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHomC D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHomC D e hD), bridgeLocHomC_algebraMap,
    bridgeLocHomC_algebraMap, ← bridgeBaseC_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBaseC D e (iotaC F D.s))
    (bridgeLocHomC D e hD (divByS (iotaC F (e.f i)) (pushDatumC D hD).s))]
  exact happ

theorem bridgeLocHomC_continuous (hD : D.IsRational) :
    @Continuous _ _ (pushDatumC D hD).topology _ (bridgeLocHomC D e hD) := by
  refine locTopology_continuous_lift (pushDatumC D hD).P (pushDatumC D hD).T
    (pushDatumC D hD).s (pushDatumC D hD).hopen _ ?_ ?_
  · have h_eq : (bridgeLocHomC D e hD).comp
        (algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s)) =
        bridgeBaseC D e := by
      ext a; exact bridgeLocHomC_algebraMap D e hD a
    rw [show ⇑((bridgeLocHomC D e hD).comp
        (algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s)))
        = ⇑(bridgeBaseC D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBaseC D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBaseC_le D e a
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, rfl⟩ := e.hf t₀ ht₀
    rw [bridgeLocHomC_divByS]
    exact isPowerBounded_of_norm_le_one (norm_bridgeXC_le_one D e i)

/-- `I_𝓒` is closed (noetherian-ball route, as in `isClosed_IA`'s vertex inputs). -/
theorem isClosed_IC' : IsClosed ((IC F e.m D.s e.f : Set (PC F e.m))) := by
  haveI := isNoetherianRing_PC F e.m
  exact isClosed_graphIdeal (tC F) (isUnit_tC F)
    (by rw [norm_tC]; exact norm_t_lt_one F) (by rw [norm_tC]; exact norm_t_pos F)
    (norm_tC_mul F) (isNoetherianRing_unitBall_PC F e.m) (rC F e.m D.s e.f)

/-- The 𝓒-side forward bridge `𝒪_𝓒(D_C) → 𝓒_α`. -/
noncomputable def bridgeFwdC (hD : D.IsRational) :
    presheafValue (pushDatumC D hD) →+* locC F e.m D.s e.f := by
  haveI hcl : IsClosed ((IC F e.m D.s e.f : Set (PC F e.m))) := isClosed_IC' D e
  haveI : NormedAddCommGroup (locC F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumC D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom (bridgeLocHomC D e hD)
    (bridgeLocHomC_continuous D e hD)

theorem bridgeFwdC_coe (hD : D.IsRational) (a : Localization.Away (pushDatumC D hD).s) :
    bridgeFwdC D e hD ((pushDatumC D hD).coeRingHom a) = bridgeLocHomC D e hD a := by
  haveI hcl : IsClosed ((IC F e.m D.s e.f : Set (PC F e.m))) := isClosed_IC' D e
  haveI : NormedAddCommGroup (locC F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumC D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe (bridgeLocHomC D e hD)
    (bridgeLocHomC_continuous D e hD) a

theorem bridgeFwdC_continuous (hD : D.IsRational) :
    Continuous (bridgeFwdC D e hD) := by
  letI := (pushDatumC D hD).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-! #### The 𝓑-side forward bridge (mirror of the 𝓒 block, consumed by the transfer) -/

/-- The base map `𝓑 → 𝓑_α`. -/
noncomputable def bridgeBaseB : JetB F →+* locB F e.m D.s e.f :=
  (Ideal.Quotient.mk (IB F e.m D.s e.f)).comp
    ((polyToP : MvPolynomial (Fin e.m) (JetB F) →+* PB F e.m).comp MvPolynomial.C)

/-- The variable images `X̄ᵢ ∈ 𝓑_α`. -/
noncomputable def bridgeXB (i : Fin e.m) : locB F e.m D.s e.f :=
  Ideal.Quotient.mk (IB F e.m D.s e.f) (polyToP (MvPolynomial.X i))

theorem bridgeBaseB_s_mul_X (i : Fin e.m) :
    bridgeBaseB D e (jB F D.s) * bridgeXB D e i =
      bridgeBaseB D e (jB F (e.f i)) := by
  have hmem : polyToP (MvPolynomial.C (jB F D.s)) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (jB F (e.f i))) ∈ IB F e.m D.s e.f := by
    have hrw : rB F e.m D.s e.f i = polyToP (MvPolynomial.C (jB F D.s)) *
        polyToP (MvPolynomial.X i) - polyToP (MvPolynomial.C (jB F (e.f i))) := by
      rw [rB_eq, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (IB F e.m D.s e.f) (polyToP (MvPolynomial.C (jB F D.s))) *
      Ideal.Quotient.mk (IB F e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (IB F e.m D.s e.f) (polyToP (MvPolynomial.C (jB F (e.f i))))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (IB F e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

theorem isUnit_bridgeBaseB_s (hD : D.IsRational) :
    IsUnit (bridgeBaseB D e (jB F D.s)) := by
  have h1 : (1 : JetB F) ∈
      Ideal.span ({jB F D.s} ∪ Set.range fun i => jB F (e.f i)) := by
    rw [span_pushed_B F e.m D.s e.f (e.span_eq_top D hD)]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBaseB D e (d i * jB F (e.f i)) =
      bridgeBaseB D e (d i) * (bridgeBaseB D e (jB F D.s) * bridgeXB D e i) :=
    fun i => by rw [RingHom.map_mul (bridgeBaseB D e), bridgeBaseB_s_mul_X]
  have happ : bridgeBaseB D e c * bridgeBaseB D e (jB F D.s) +
      ∑ i, bridgeBaseB D e (d i) * (bridgeBaseB D e (jB F D.s) * bridgeXB D e i) = 1 := by
    have h0 := congrArg (bridgeBaseB D e) hxy
    rw [RingHom.map_one (bridgeBaseB D e), RingHom.map_add (bridgeBaseB D e),
      RingHom.map_mul (bridgeBaseB D e),
      show (bridgeBaseB D e) (∑ i, d i * jB F (e.f i)) =
        ∑ i, bridgeBaseB D e (d i * jB F (e.f i)) from map_sum (bridgeBaseB D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBaseB D e (jB F D.s) *
      (bridgeBaseB D e c + ∑ i, bridgeBaseB D e (d i) * bridgeXB D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBaseB D e (jB F D.s) * bridgeBaseB D e c +
        ∑ i, bridgeBaseB D e (jB F D.s) * (bridgeBaseB D e (d i) * bridgeXB D e i)
        = bridgeBaseB D e c * bridgeBaseB D e (jB F D.s) +
          ∑ i, bridgeBaseB D e (d i) * (bridgeBaseB D e (jB F D.s) * bridgeXB D e i) := by
          rw [mul_comm (bridgeBaseB D e (jB F D.s)) (bridgeBaseB D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

theorem norm_bridgeXB_le_one (i : Fin e.m) : ‖bridgeXB D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact gaussNorm_X_le_one (S := JetB F) i

theorem norm_bridgeBaseB_le (a : JetB F) : ‖bridgeBaseB D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := JetB F) (m := e.m) (MvPolynomial.C a) : PB F e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := JetB F) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetB F) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The 𝓑-side localization lift. -/
noncomputable def bridgeLocHomB (hD : D.IsRational) :
    Localization.Away (pushDatumB D hD).s →+* locB F e.m D.s e.f :=
  IsLocalization.Away.lift (pushDatumB D hD).s (isUnit_bridgeBaseB_s D e hD)

theorem bridgeLocHomB_algebraMap (hD : D.IsRational) (a : JetB F) :
    bridgeLocHomB D e hD
      (algebraMap (JetB F) (Localization.Away (pushDatumB D hD).s) a) =
      bridgeBaseB D e a :=
  IsLocalization.Away.lift_eq _ _ a

theorem bridgeLocHomB_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHomB D e hD (divByS (jB F (e.f i)) (pushDatumB D hD).s) =
      bridgeXB D e i := by
  have hu := isUnit_bridgeBaseB_s D e hD
  have hspec : divByS (jB F (e.f i)) (pushDatumB D hD).s *
      algebraMap (JetB F) (Localization.Away (pushDatumB D hD).s) (pushDatumB D hD).s =
      algebraMap (JetB F) (Localization.Away (pushDatumB D hD).s) (jB F (e.f i)) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHomB D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHomB D e hD), bridgeLocHomB_algebraMap,
    bridgeLocHomB_algebraMap, ← bridgeBaseB_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBaseB D e (jB F D.s))
    (bridgeLocHomB D e hD (divByS (jB F (e.f i)) (pushDatumB D hD).s))]
  exact happ

theorem bridgeLocHomB_continuous (hD : D.IsRational) :
    @Continuous _ _ (pushDatumB D hD).topology _ (bridgeLocHomB D e hD) := by
  refine locTopology_continuous_lift (pushDatumB D hD).P (pushDatumB D hD).T
    (pushDatumB D hD).s (pushDatumB D hD).hopen _ ?_ ?_
  · have h_eq : (bridgeLocHomB D e hD).comp
        (algebraMap (JetB F) (Localization.Away (pushDatumB D hD).s)) =
        bridgeBaseB D e := by
      refine RingHom.ext fun a => ?_
      show bridgeLocHomB D e hD
        (algebraMap (JetB F) (Localization.Away (pushDatumB D hD).s) a) =
        bridgeBaseB D e a
      exact bridgeLocHomB_algebraMap D e hD a
    rw [show ⇑((bridgeLocHomB D e hD).comp
        (algebraMap (JetB F) (Localization.Away (pushDatumB D hD).s)))
        = ⇑(bridgeBaseB D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBaseB D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBaseB_le D e a
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, rfl⟩ := e.hf t₀ ht₀
    rw [bridgeLocHomB_divByS]
    exact isPowerBounded_of_norm_le_one (norm_bridgeXB_le_one D e i)

/-- `I_𝓑` is closed (noetherian-ball route). -/
theorem isClosed_IB' : IsClosed ((IB F e.m D.s e.f : Set (PB F e.m))) := by
  haveI := isNoetherianRing_PB F e.m
  exact isClosed_graphIdeal (tB F) (isUnit_tB F)
    (by rw [norm_tB]; exact norm_t_lt_one F) (by rw [norm_tB]; exact norm_t_pos F)
    (norm_tB_mul F) (isNoetherianRing_unitBall_PB F e.m) (rB F e.m D.s e.f)

/-- The 𝓑-side forward bridge `𝒪_𝓑(D_B) → 𝓑_α`. -/
noncomputable def bridgeFwdB (hD : D.IsRational) :
    presheafValue (pushDatumB D hD) →+* locB F e.m D.s e.f := by
  haveI hcl : IsClosed ((IB F e.m D.s e.f : Set (PB F e.m))) := isClosed_IB' D e
  haveI : NormedAddCommGroup (locB F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumB D hD).uniformSpace
  haveI : @IsTopologicalRing (Localization.Away (pushDatumB D hD).s)
      ((pushDatumB D hD).topology) _ := (pushDatumB D hD).isTopologicalRing
  haveI : @IsUniformAddGroup (Localization.Away (pushDatumB D hD).s)
      ((pushDatumB D hD).uniformSpace) _ := (pushDatumB D hD).isUniformAddGroup
  exact @UniformSpace.Completion.extensionHom
    (Localization.Away (pushDatumB D hD).s) _
    ((pushDatumB D hD).uniformSpace) ((pushDatumB D hD).isTopologicalRing)
    ((pushDatumB D hD).isUniformAddGroup)
    (locB F e.m D.s e.f) _ _ _ _
    (bridgeLocHomB D e hD) (bridgeLocHomB_continuous D e hD) _ _

theorem bridgeFwdB_coe (hD : D.IsRational) (a : Localization.Away (pushDatumB D hD).s) :
    bridgeFwdB D e hD ((pushDatumB D hD).coeRingHom a) = bridgeLocHomB D e hD a := by
  haveI hcl : IsClosed ((IB F e.m D.s e.f : Set (PB F e.m))) := isClosed_IB' D e
  haveI : NormedAddCommGroup (locB F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumB D hD).uniformSpace
  haveI : @IsTopologicalRing (Localization.Away (pushDatumB D hD).s)
      ((pushDatumB D hD).topology) _ := (pushDatumB D hD).isTopologicalRing
  haveI : @IsUniformAddGroup (Localization.Away (pushDatumB D hD).s)
      ((pushDatumB D hD).uniformSpace) _ := (pushDatumB D hD).isUniformAddGroup
  exact @UniformSpace.Completion.extensionHom_coe
    (Localization.Away (pushDatumB D hD).s) _
    ((pushDatumB D hD).uniformSpace) ((pushDatumB D hD).isTopologicalRing)
    ((pushDatumB D hD).isUniformAddGroup)
    (locB F e.m D.s e.f) _ _ _ _
    (bridgeLocHomB D e hD) (bridgeLocHomB_continuous D e hD) _ _ a

theorem bridgeFwdB_continuous (hD : D.IsRational) :
    Continuous (bridgeFwdB D e hD) := by
  letI := (pushDatumB D hD).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-! #### The 𝓓-side forward bridge (mirror, consumed by the transfer's 𝓓-matching) -/

/-- The base map `𝓓 → 𝓓_α`. -/
noncomputable def bridgeBaseD : JetD F →+* locD F e.m D.s e.f :=
  (Ideal.Quotient.mk (ID F e.m D.s e.f)).comp
    ((polyToP : MvPolynomial (Fin e.m) (JetD F) →+* PD F e.m).comp MvPolynomial.C)

/-- The variable images `X̄ᵢ ∈ 𝓓_α`. -/
noncomputable def bridgeXD (i : Fin e.m) : locD F e.m D.s e.f :=
  Ideal.Quotient.mk (ID F e.m D.s e.f) (polyToP (MvPolynomial.X i))

theorem bridgeBaseD_s_mul_X (i : Fin e.m) :
    bridgeBaseD D e (rhoC F (iotaC F D.s)) * bridgeXD D e i =
      bridgeBaseD D e (rhoC F (iotaC F (e.f i))) := by
  have hmem : polyToP (MvPolynomial.C (rhoC F (iotaC F D.s))) * polyToP (MvPolynomial.X i) -
      polyToP (MvPolynomial.C (rhoC F (iotaC F (e.f i)))) ∈ ID F e.m D.s e.f := by
    have hrw : rD F e.m D.s e.f i = polyToP (MvPolynomial.C (rhoC F (iotaC F D.s))) *
        polyToP (MvPolynomial.X i) - polyToP (MvPolynomial.C (rhoC F (iotaC F (e.f i)))) := by
      rw [rD_eq, map_sub, map_mul]
    rw [← hrw]
    exact Ideal.subset_span ⟨i, rfl⟩
  show Ideal.Quotient.mk (ID F e.m D.s e.f) (polyToP (MvPolynomial.C (rhoC F (iotaC F D.s)))) *
      Ideal.Quotient.mk (ID F e.m D.s e.f) (polyToP (MvPolynomial.X i)) =
    Ideal.Quotient.mk (ID F e.m D.s e.f) (polyToP (MvPolynomial.C (rhoC F (iotaC F (e.f i)))))
  rw [← RingHom.map_mul (Ideal.Quotient.mk (ID F e.m D.s e.f))]
  exact Ideal.Quotient.eq.mpr hmem

theorem isUnit_bridgeBaseD_s (hD : D.IsRational) :
    IsUnit (bridgeBaseD D e (rhoC F (iotaC F D.s))) := by
  have h1 : (1 : JetD F) ∈
      Ideal.span ({rhoC F (iotaC F D.s)} ∪ Set.range fun i => rhoC F (iotaC F (e.f i))) := by
    rw [span_pushed_D F e.m D.s e.f (e.span_eq_top D hD)]; trivial
  rw [Ideal.span_union, Submodule.mem_sup] at h1
  obtain ⟨x, hx, y, hy, hxy⟩ := h1
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  rw [Ideal.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, rfl⟩ := hy
  have hterm : ∀ i, bridgeBaseD D e (d i * rhoC F (iotaC F (e.f i))) =
      bridgeBaseD D e (d i) * (bridgeBaseD D e (rhoC F (iotaC F D.s)) * bridgeXD D e i) :=
    fun i => by rw [RingHom.map_mul (bridgeBaseD D e), bridgeBaseD_s_mul_X]
  have happ : bridgeBaseD D e c * bridgeBaseD D e (rhoC F (iotaC F D.s)) +
      ∑ i, bridgeBaseD D e (d i) * (bridgeBaseD D e (rhoC F (iotaC F D.s)) * bridgeXD D e i) = 1 := by
    have h0 := congrArg (bridgeBaseD D e) hxy
    rw [RingHom.map_one (bridgeBaseD D e), RingHom.map_add (bridgeBaseD D e),
      RingHom.map_mul (bridgeBaseD D e),
      show (bridgeBaseD D e) (∑ i, d i * rhoC F (iotaC F (e.f i))) =
        ∑ i, bridgeBaseD D e (d i * rhoC F (iotaC F (e.f i))) from map_sum (bridgeBaseD D e) _ _,
      Finset.sum_congr rfl fun i _ => hterm i] at h0
    exact h0
  have hmul : bridgeBaseD D e (rhoC F (iotaC F D.s)) *
      (bridgeBaseD D e c + ∑ i, bridgeBaseD D e (d i) * bridgeXD D e i) = 1 := by
    rw [mul_add, Finset.mul_sum]
    calc bridgeBaseD D e (rhoC F (iotaC F D.s)) * bridgeBaseD D e c +
        ∑ i, bridgeBaseD D e (rhoC F (iotaC F D.s)) * (bridgeBaseD D e (d i) * bridgeXD D e i)
        = bridgeBaseD D e c * bridgeBaseD D e (rhoC F (iotaC F D.s)) +
          ∑ i, bridgeBaseD D e (d i) * (bridgeBaseD D e (rhoC F (iotaC F D.s)) * bridgeXD D e i) := by
          rw [mul_comm (bridgeBaseD D e (rhoC F (iotaC F D.s))) (bridgeBaseD D e c)]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := happ
  exact IsUnit.of_mul_eq_one _ hmul

theorem norm_bridgeXD_le_one (i : Fin e.m) : ‖bridgeXD D e i‖ ≤ 1 := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  rw [MvRestricted.norm_eq]
  exact gaussNorm_X_le_one (S := JetD F) i

theorem norm_bridgeBaseD_le (a : JetD F) : ‖bridgeBaseD D e a‖ ≤ ‖a‖ := by
  refine (Ideal.Quotient.norm_mk_le _ _).trans ?_
  show ‖(polyToP (E := JetD F) (m := e.m) (MvPolynomial.C a) : PD F e.m)‖ ≤ ‖a‖
  rw [MvRestricted.norm_eq,
    show (polyToP (E := JetD F) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetD F) a from MvPolynomial.coe_C a]
  exact le_of_eq (UnitDiscExample.gaussNorm_C_norm _ a)

/-- The 𝓓-side localization lift. -/
noncomputable def bridgeLocHomD (hD : D.IsRational) :
    Localization.Away (pushDatumD D hD).s →+* locD F e.m D.s e.f :=
  IsLocalization.Away.lift (S := Localization.Away (pushDatumD D hD).s)
    (pushDatumD D hD).s (isUnit_bridgeBaseD_s D e hD)

theorem bridgeLocHomD_algebraMap (hD : D.IsRational) (a : JetD F) :
    bridgeLocHomD D e hD
      (algebraMap (JetD F) (Localization.Away (pushDatumD D hD).s) a) =
      bridgeBaseD D e a :=
  IsLocalization.Away.lift_eq _ _ a

theorem bridgeLocHomD_divByS (hD : D.IsRational) (i : Fin e.m) :
    bridgeLocHomD D e hD (divByS (rhoC F (iotaC F (e.f i))) (pushDatumD D hD).s) =
      bridgeXD D e i := by
  have hu := isUnit_bridgeBaseD_s D e hD
  have hspec : divByS (rhoC F (iotaC F (e.f i))) (pushDatumD D hD).s *
      algebraMap (JetD F) (Localization.Away (pushDatumD D hD).s) (pushDatumD D hD).s =
      algebraMap (JetD F) (Localization.Away (pushDatumD D hD).s) (rhoC F (iotaC F (e.f i))) := by
    rw [divByS, IsLocalization.mk'_spec]
  have happ := congrArg (bridgeLocHomD D e hD) hspec
  rw [RingHom.map_mul (bridgeLocHomD D e hD), bridgeLocHomD_algebraMap,
    bridgeLocHomD_algebraMap, ← bridgeBaseD_s_mul_X] at happ
  refine hu.mul_left_cancel ?_
  rw [mul_comm (bridgeBaseD D e (rhoC F (iotaC F D.s)))
    (bridgeLocHomD D e hD (divByS (rhoC F (iotaC F (e.f i))) (pushDatumD D hD).s))]
  exact happ

theorem bridgeLocHomD_continuous (hD : D.IsRational) :
    @Continuous _ _ (pushDatumD D hD).topology _ (bridgeLocHomD D e hD) := by
  refine locTopology_continuous_lift (pushDatumD D hD).P (pushDatumD D hD).T
    (pushDatumD D hD).s (pushDatumD D hD).hopen _ ?_ ?_
  · have h_eq : (bridgeLocHomD D e hD).comp
        (algebraMap (JetD F) (Localization.Away (pushDatumD D hD).s)) =
        bridgeBaseD D e := by
      refine RingHom.ext fun a => ?_
      show bridgeLocHomD D e hD
        (algebraMap (JetD F) (Localization.Away (pushDatumD D hD).s) a) =
        bridgeBaseD D e a
      exact bridgeLocHomD_algebraMap D e hD a
    rw [show ⇑((bridgeLocHomD D e hD).comp
        (algebraMap (JetD F) (Localization.Away (pushDatumD D hD).s)))
        = ⇑(bridgeBaseD D e) from congrArg _ h_eq]
    exact AddMonoidHomClass.continuous_of_bound (bridgeBaseD D e) 1 fun a => by
      rw [one_mul]; exact norm_bridgeBaseD_le D e a
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨i, rfl⟩ := e.hf t₀ ht₀
    show TopologicalRing.IsPowerBounded
      (bridgeLocHomD D e hD (divByS (rhoC F (iotaC F (e.f i))) (pushDatumD D hD).s))
    rw [bridgeLocHomD_divByS]
    exact isPowerBounded_of_norm_le_one (norm_bridgeXD_le_one D e i)

/-- `I_𝓓` is closed (noetherian-ball route). -/
theorem isClosed_ID' : IsClosed ((ID F e.m D.s e.f : Set (PD F e.m))) := by
  haveI := isNoetherianRing_PD F e.m
  exact isClosed_graphIdeal (tD F) (isUnit_tD F)
    (by rw [norm_tD]; exact norm_t_lt_one F) (by rw [norm_tD]; exact norm_t_pos F)
    (norm_tD_mul F) (isNoetherianRing_unitBall_PD F e.m) (rD F e.m D.s e.f)

/-- The 𝓓-side forward bridge `𝒪_𝓓(D_D) → 𝓓_α`. -/
noncomputable def bridgeFwdD (hD : D.IsRational) :
    presheafValue (pushDatumD D hD) →+* locD F e.m D.s e.f := by
  haveI hcl : IsClosed ((ID F e.m D.s e.f : Set (PD F e.m))) := isClosed_ID' D e
  haveI : NormedAddCommGroup (locD F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumD D hD).uniformSpace
  haveI : @IsTopologicalRing (Localization.Away (pushDatumD D hD).s)
      ((pushDatumD D hD).topology) _ := (pushDatumD D hD).isTopologicalRing
  haveI : @IsUniformAddGroup (Localization.Away (pushDatumD D hD).s)
      ((pushDatumD D hD).uniformSpace) _ := (pushDatumD D hD).isUniformAddGroup
  exact @UniformSpace.Completion.extensionHom
    (Localization.Away (pushDatumD D hD).s) _
    ((pushDatumD D hD).uniformSpace) ((pushDatumD D hD).isTopologicalRing)
    ((pushDatumD D hD).isUniformAddGroup)
    (locD F e.m D.s e.f) _ _ _ _
    (bridgeLocHomD D e hD) (bridgeLocHomD_continuous D e hD) _ _

theorem bridgeFwdD_coe (hD : D.IsRational) (a : Localization.Away (pushDatumD D hD).s) :
    bridgeFwdD D e hD ((pushDatumD D hD).coeRingHom a) = bridgeLocHomD D e hD a := by
  haveI hcl : IsClosed ((ID F e.m D.s e.f : Set (PD F e.m))) := isClosed_ID' D e
  haveI : NormedAddCommGroup (locD F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  letI := (pushDatumD D hD).uniformSpace
  haveI : @IsTopologicalRing (Localization.Away (pushDatumD D hD).s)
      ((pushDatumD D hD).topology) _ := (pushDatumD D hD).isTopologicalRing
  haveI : @IsUniformAddGroup (Localization.Away (pushDatumD D hD).s)
      ((pushDatumD D hD).uniformSpace) _ := (pushDatumD D hD).isUniformAddGroup
  exact @UniformSpace.Completion.extensionHom_coe
    (Localization.Away (pushDatumD D hD).s) _
    ((pushDatumD D hD).uniformSpace) ((pushDatumD D hD).isTopologicalRing)
    ((pushDatumD D hD).isUniformAddGroup)
    (locD F e.m D.s e.f) _ _ _ _
    (bridgeLocHomD D e hD) (bridgeLocHomD_continuous D e hD) _ _ a

theorem bridgeFwdD_continuous (hD : D.IsRational) :
    Continuous (bridgeFwdD D e hD) := by
  letI := (pushDatumD D hD).uniformSpace
  exact UniformSpace.Completion.continuous_extension

/-! #### 𝓑-side reverse (evaluation) — the injectivity half of the 𝓑-bridge -/

/-- Norm-decay to topological decay at 𝓑. -/
noncomputable def bridgeToRestrictedB (m : ℕ) :
    PB F m →+* ↥(restrictedMvPowerSeriesSubring m (JetB F)) where
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
    presheafValue (pushDatumB D hD) :=
  (pushDatumB D hD).coeRingHom (divByS (jB F (e.f i)) (pushDatumB D hD).s)

theorem bridgeGenB_isBounded (hD : D.IsRational) (i : Fin e.m) :
    TopologicalRing.IsBounded
      (Set.range (bridgeGenB D e hD i ^ · : ℕ → presheafValue (pushDatumB D hD))) := by
  have hmem : divByS (jB F (e.f i)) (pushDatumB D hD).s ∈
      locSubring (pushDatumB D hD).P (pushDatumB D hD).T (pushDatumB D hD).s :=
    divByS_mem_locSubring _ _ _ (Finset.mem_image_of_mem _ (e.hf' i))
  have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded
    (pushDatumB D hD)
  apply hbdd.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨divByS (jB F (e.f i)) (pushDatumB D hD).s ^ n, pow_mem hmem n, by
    rw [map_pow]; rfl⟩

/-- The 𝓑-side evaluation `P_𝓑 →+* 𝒪_𝓑(D_B)`. -/
noncomputable def bridgeEvalB (hD : D.IsRational) :
    PB F e.m →+* presheafValue (pushDatumB D hD) :=
  (mvEvalHomBounded (pushDatumB D hD).canonicalMap
    (canonicalMap_continuous (pushDatumB D hD))
    (bridgeGenB D e hD) (bridgeGenB_isBounded D e hD)).comp (bridgeToRestrictedB e.m)

theorem bridgeEvalB_const (hD : D.IsRational) (a : JetB F) :
    bridgeEvalB D e hD (polyToP (MvPolynomial.C a)) =
      (pushDatumB D hD).canonicalMap a := by
  have hcast : bridgeToRestrictedB (F := F) e.m (polyToP (MvPolynomial.C a)) =
      algebraMap (JetB F) ↥(restrictedMvPowerSeriesSubring e.m (JetB F)) a := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetB F) (m := e.m) (MvPolynomial.C a)).1 :
      MvPowerSeries (Fin e.m) (JetB F)) = _
    rw [show (polyToP (E := JetB F) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetB F) a from MvPolynomial.coe_C a]
    rfl
  rw [bridgeEvalB, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_algebraMap _ _ _ _ a

theorem bridgeEvalB_X (hD : D.IsRational) (i : Fin e.m) :
    bridgeEvalB D e hD (polyToP (MvPolynomial.X i)) = bridgeGenB D e hD i := by
  have hcast : bridgeToRestrictedB (F := F) e.m (polyToP (MvPolynomial.X i)) =
      ⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetB F) (m := e.m) (MvPolynomial.X i)).1 :
      MvPowerSeries (Fin e.m) (JetB F)) = _
    exact MvPolynomial.coe_X i
  rw [bridgeEvalB, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_X _ _ _ _ i

theorem IB_le_ker_bridgeEvalB (hD : D.IsRational) :
    IB F e.m D.s e.f ≤ RingHom.ker (bridgeEvalB D e hD) := by
  rw [IB, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, rB_eq]
  have hval : bridgeEvalB D e hD (polyToP (MvPolynomial.C (jB F D.s) * MvPolynomial.X i -
      MvPolynomial.C (jB F (e.f i)))) =
      (pushDatumB D hD).canonicalMap (jB F D.s) * bridgeGenB D e hD i -
        (pushDatumB D hD).canonicalMap (jB F (e.f i)) :=
    (map_sub ((bridgeEvalB D e hD).comp polyToP)
        (MvPolynomial.C (jB F D.s) * MvPolynomial.X i)
        (MvPolynomial.C (jB F (e.f i)))).trans
      (congrArg₂ (· - ·)
        ((map_mul ((bridgeEvalB D e hD).comp polyToP)
            (MvPolynomial.C (jB F D.s)) (MvPolynomial.X i)).trans
          (congrArg₂ (· * ·) (bridgeEvalB_const D e hD (jB F D.s))
            (bridgeEvalB_X D e hD i)))
        (bridgeEvalB_const D e hD (jB F (e.f i))))
  rw [hval, sub_eq_zero, bridgeGenB]
  rw [show (pushDatumB D hD).canonicalMap (jB F D.s) =
      (pushDatumB D hD).coeRingHom (algebraMap (JetB F)
        (Localization.Away (pushDatumB D hD).s) (pushDatumB D hD).s) from rfl,
    ← RingHom.map_mul (pushDatumB D hD).coeRingHom,
    show algebraMap (JetB F) (Localization.Away (pushDatumB D hD).s) (pushDatumB D hD).s *
      divByS (jB F (e.f i)) (pushDatumB D hD).s =
      algebraMap (JetB F) (Localization.Away (pushDatumB D hD).s) (jB F (e.f i)) from by
    rw [mul_comm, divByS, IsLocalization.mk'_spec]]
  rfl

/-- The 𝓑-side reverse `𝓑_α → 𝒪_𝓑(D_B)`. -/
noncomputable def bridgeRevB (hD : D.IsRational) :
    locB F e.m D.s e.f →+* presheafValue (pushDatumB D hD) :=
  Ideal.Quotient.lift (IB F e.m D.s e.f) (bridgeEvalB D e hD)
    (fun _ ha => RingHom.mem_ker.mp (IB_le_ker_bridgeEvalB D e hD ha))

theorem bridgeRevB_bridgeBaseB (hD : D.IsRational) (a : JetB F) :
    bridgeRevB D e hD (bridgeBaseB D e a) = (pushDatumB D hD).canonicalMap a :=
  bridgeEvalB_const D e hD a

private theorem bridgeRangeProdB_isBounded (hD : D.IsRational) :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i, bridgeGenB D e hD i ^ (v i))) := by
  classical
  suffices h : ∀ s : Finset (Fin e.m), TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i ∈ s, bridgeGenB D e hD i ^ (v i))) from
    h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty =>
      simpa using
        TopologicalRing.isBounded_singleton (1 : presheafValue (pushDatumB D hD))
  | insert a s ha ih =>
      refine ((bridgeGenB_isBounded D e hD a).mul ih).subset ?_
      rintro _ ⟨v, rfl⟩
      change ∏ i ∈ insert a s, bridgeGenB D e hD i ^ (v i) ∈ _
      rw [Finset.prod_insert ha]
      exact Set.mul_mem_mul ⟨v a, rfl⟩ ⟨v, rfl⟩

theorem bridgeEvalB_continuous (hD : D.IsRational) :
    Continuous (bridgeEvalB D e hD) := by
  classical
  refine continuous_of_continuousAt_zero (bridgeEvalB D e hD).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  obtain ⟨V, hV, hVR⟩ := bridgeRangeProdB_isBounded D e hD
    (W : Set (presheafValue (pushDatumB D hD)))
    (W.isOpen.mem_nhds W.zero_mem)
  have hpre : (pushDatumB D hD).canonicalMap ⁻¹' V ∈ nhds (0 : JetB F) :=
    (canonicalMap_continuous (pushDatumB D hD)).continuousAt.preimage_mem_nhds
      (by rwa [map_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : PB F e.m) hδ) ?_
  intro p hp
  rw [Metric.mem_ball, dist_zero_right] at hp
  apply hWU
  change (∑' v, mvEvalTerm (pushDatumB D hD).canonicalMap (bridgeGenB D e hD)
    (bridgeToRestrictedB e.m p) v) ∈ (W : Set (presheafValue (pushDatumB D hD)))
  refine tsum_mem_of_isOpen_addSubgroup'
    (mvEvalTerm_summable (pushDatumB D hD).canonicalMap
      (canonicalMap_continuous (pushDatumB D hD))
      (bridgeGenB D e hD) (bridgeGenB_isBounded D e hD) (bridgeToRestrictedB e.m p))
    W.isOpen fun v => ?_
  have hcoeff : ‖MvPowerSeries.coeff v p.1‖ < δ :=
    lt_of_le_of_lt (norm_coeff_le_gauss p v) hp
  have hVmem : (pushDatumB D hD).canonicalMap (MvPowerSeries.coeff v p.1) ∈ V :=
    hball (by rwa [Metric.mem_ball, dist_zero_right])
  change mvEvalTerm (pushDatumB D hD).canonicalMap (bridgeGenB D e hD)
    (bridgeToRestrictedB e.m p) v ∈ W
  rw [show mvEvalTerm (pushDatumB D hD).canonicalMap (bridgeGenB D e hD)
      (bridgeToRestrictedB e.m p) v =
      (∏ i, bridgeGenB D e hD i ^ (v i)) *
        (pushDatumB D hD).canonicalMap (MvPowerSeries.coeff v p.1) from by
    rw [mvEvalTerm]; exact mul_comm _ _]
  exact hVR (Set.mul_mem_mul ⟨v, rfl⟩ hVmem)

theorem bridgeRevB_continuous (hD : D.IsRational) :
    Continuous (bridgeRevB D e hD) := by
  rw [(QuotientRing.isOpenQuotientMap_mk (IB F e.m D.s e.f)).isQuotientMap.continuous_iff]
  exact bridgeEvalB_continuous D e hD

/-- `revB ∘ fwdB = id` — the 𝓑-bridge is split-injective. -/
theorem bridgeRevB_bridgeFwdB (hD : D.IsRational)
    (x : presheafValue (pushDatumB D hD)) :
    bridgeRevB D e hD (bridgeFwdB D e hD x) = x := by
  letI := (pushDatumB D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumB D hD).s) :=
    (pushDatumB D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumB D hD).s) :=
    (pushDatumB D hD).isUniformAddGroup
  haveI : RegularSpace (presheafValue (pushDatumB D hD)) := UniformSpace.to_regularSpace
  have hcomp : (bridgeRevB D e hD).comp (bridgeLocHomB D e hD) =
      (pushDatumB D hD).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (pushDatumB D hD).s) ?_
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [bridgeLocHomB_algebraMap, bridgeRevB_bridgeBaseB]
    rfl
  have hdense : DenseRange ((pushDatumB D hD).coeRingHom :
      Localization.Away (pushDatumB D hD).s → presheafValue (pushDatumB D hD)) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => bridgeRevB D e hD (bridgeFwdB D e hD y)) = fun y => y :=
    hdense.equalizer ((bridgeRevB_continuous D e hD).comp (bridgeFwdB_continuous D e hD))
      continuous_id (by
        funext a
        show bridgeRevB D e hD (bridgeFwdB D e hD ((pushDatumB D hD).coeRingHom a)) =
          (pushDatumB D hD).coeRingHom a
        rw [bridgeFwdB_coe]
        exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

theorem bridgeFwdB_injective (hD : D.IsRational) :
    Function.Injective (bridgeFwdB D e hD) :=
  Function.LeftInverse.injective (g := bridgeRevB D e hD) (bridgeRevB_bridgeFwdB D e hD)

/-! #### 𝓒-side reverse (evaluation) — the injectivity half of the 𝓒-bridge -/

/-- Norm-decay to topological decay at 𝓒. -/
noncomputable def bridgeToRestrictedC (m : ℕ) :
    PC F m →+* ↥(restrictedMvPowerSeriesSubring m (JetC F)) where
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
    presheafValue (pushDatumC D hD) :=
  (pushDatumC D hD).coeRingHom (divByS (iotaC F (e.f i)) (pushDatumC D hD).s)

theorem bridgeGenC_isBounded (hD : D.IsRational) (i : Fin e.m) :
    TopologicalRing.IsBounded
      (Set.range (bridgeGenC D e hD i ^ · : ℕ → presheafValue (pushDatumC D hD))) := by
  have hmem : divByS (iotaC F (e.f i)) (pushDatumC D hD).s ∈
      locSubring (pushDatumC D hD).P (pushDatumC D hD).T (pushDatumC D hD).s :=
    divByS_mem_locSubring _ _ _ (Finset.mem_image_of_mem _ (e.hf' i))
  have hbdd := CompletionLocalization.coeRingHom_image_locSubring_isBounded
    (pushDatumC D hD)
  apply hbdd.subset
  rintro _ ⟨n, rfl⟩
  exact ⟨divByS (iotaC F (e.f i)) (pushDatumC D hD).s ^ n, pow_mem hmem n, by
    rw [map_pow]; rfl⟩

/-- The 𝓑-side evaluation `P_𝓒 →+* 𝒪_𝓒(D_C)`. -/
noncomputable def bridgeEvalC (hD : D.IsRational) :
    PC F e.m →+* presheafValue (pushDatumC D hD) :=
  (mvEvalHomBounded (pushDatumC D hD).canonicalMap
    (canonicalMap_continuous (pushDatumC D hD))
    (bridgeGenC D e hD) (bridgeGenC_isBounded D e hD)).comp (bridgeToRestrictedC e.m)

theorem bridgeEvalC_const (hD : D.IsRational) (a : JetC F) :
    bridgeEvalC D e hD (polyToP (MvPolynomial.C a)) =
      (pushDatumC D hD).canonicalMap a := by
  have hcast : bridgeToRestrictedC (F := F) e.m (polyToP (MvPolynomial.C a)) =
      algebraMap (JetC F) ↥(restrictedMvPowerSeriesSubring e.m (JetC F)) a := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetC F) (m := e.m) (MvPolynomial.C a)).1 :
      MvPowerSeries (Fin e.m) (JetC F)) = _
    rw [show (polyToP (E := JetC F) (m := e.m) (MvPolynomial.C a)).1 =
      MvPowerSeries.C (σ := Fin e.m) (R := JetC F) a from MvPolynomial.coe_C a]
    rfl
  rw [bridgeEvalC, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_algebraMap _ _ _ _ a

theorem bridgeEvalC_X (hD : D.IsRational) (i : Fin e.m) :
    bridgeEvalC D e hD (polyToP (MvPolynomial.X i)) = bridgeGenC D e hD i := by
  have hcast : bridgeToRestrictedC (F := F) e.m (polyToP (MvPolynomial.X i)) =
      ⟨MvPowerSeries.X i, MvPowerSeries.X_isRestricted i⟩ := by
    refine Subtype.ext ?_
    show ((polyToP (E := JetC F) (m := e.m) (MvPolynomial.X i)).1 :
      MvPowerSeries (Fin e.m) (JetC F)) = _
    exact MvPolynomial.coe_X i
  rw [bridgeEvalC, RingHom.comp_apply, hcast]
  exact mvEvalHomBounded_X _ _ _ _ i

theorem IC_le_ker_bridgeEvalC (hD : D.IsRational) :
    IC F e.m D.s e.f ≤ RingHom.ker (bridgeEvalC D e hD) := by
  rw [IC, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, rC_eq]
  have hval : bridgeEvalC D e hD (polyToP (MvPolynomial.C (iotaC F D.s) * MvPolynomial.X i -
      MvPolynomial.C (iotaC F (e.f i)))) =
      (pushDatumC D hD).canonicalMap (iotaC F D.s) * bridgeGenC D e hD i -
        (pushDatumC D hD).canonicalMap (iotaC F (e.f i)) :=
    (map_sub ((bridgeEvalC D e hD).comp polyToP)
        (MvPolynomial.C (iotaC F D.s) * MvPolynomial.X i)
        (MvPolynomial.C (iotaC F (e.f i)))).trans
      (congrArg₂ (· - ·)
        ((map_mul ((bridgeEvalC D e hD).comp polyToP)
            (MvPolynomial.C (iotaC F D.s)) (MvPolynomial.X i)).trans
          (congrArg₂ (· * ·) (bridgeEvalC_const D e hD (iotaC F D.s))
            (bridgeEvalC_X D e hD i)))
        (bridgeEvalC_const D e hD (iotaC F (e.f i))))
  rw [hval, sub_eq_zero, bridgeGenC]
  rw [show (pushDatumC D hD).canonicalMap (iotaC F D.s) =
      (pushDatumC D hD).coeRingHom (algebraMap (JetC F)
        (Localization.Away (pushDatumC D hD).s) (pushDatumC D hD).s) from rfl,
    ← RingHom.map_mul (pushDatumC D hD).coeRingHom,
    show algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s) (pushDatumC D hD).s *
      divByS (iotaC F (e.f i)) (pushDatumC D hD).s =
      algebraMap (JetC F) (Localization.Away (pushDatumC D hD).s) (iotaC F (e.f i)) from by
    rw [mul_comm, divByS, IsLocalization.mk'_spec]]
  rfl

/-- The 𝓑-side reverse `𝓒_α → 𝒪_𝓒(D_C)`. -/
noncomputable def bridgeRevC (hD : D.IsRational) :
    locC F e.m D.s e.f →+* presheafValue (pushDatumC D hD) :=
  Ideal.Quotient.lift (IC F e.m D.s e.f) (bridgeEvalC D e hD)
    (fun _ ha => RingHom.mem_ker.mp (IC_le_ker_bridgeEvalC D e hD ha))

theorem bridgeRevC_bridgeBaseC (hD : D.IsRational) (a : JetC F) :
    bridgeRevC D e hD (bridgeBaseC D e a) = (pushDatumC D hD).canonicalMap a :=
  bridgeEvalC_const D e hD a

private theorem bridgeRangeProdC_isBounded (hD : D.IsRational) :
    TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i, bridgeGenC D e hD i ^ (v i))) := by
  classical
  suffices h : ∀ s : Finset (Fin e.m), TopologicalRing.IsBounded
      (Set.range (fun v : Fin e.m →₀ ℕ => ∏ i ∈ s, bridgeGenC D e hD i ^ (v i))) from
    h Finset.univ
  intro s
  induction s using Finset.induction with
  | empty =>
      simpa using
        TopologicalRing.isBounded_singleton (1 : presheafValue (pushDatumC D hD))
  | insert a s ha ih =>
      refine ((bridgeGenC_isBounded D e hD a).mul ih).subset ?_
      rintro _ ⟨v, rfl⟩
      change ∏ i ∈ insert a s, bridgeGenC D e hD i ^ (v i) ∈ _
      rw [Finset.prod_insert ha]
      exact Set.mul_mem_mul ⟨v a, rfl⟩ ⟨v, rfl⟩

theorem bridgeEvalC_continuous (hD : D.IsRational) :
    Continuous (bridgeEvalC D e hD) := by
  classical
  refine continuous_of_continuousAt_zero (bridgeEvalC D e hD).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, Filter.tendsto_def]
  intro U hU
  obtain ⟨W, hWU⟩ := NonarchimedeanRing.is_nonarchimedean U hU
  obtain ⟨V, hV, hVR⟩ := bridgeRangeProdC_isBounded D e hD
    (W : Set (presheafValue (pushDatumC D hD)))
    (W.isOpen.mem_nhds W.zero_mem)
  have hpre : (pushDatumC D hD).canonicalMap ⁻¹' V ∈ nhds (0 : JetC F) :=
    (canonicalMap_continuous (pushDatumC D hD)).continuousAt.preimage_mem_nhds
      (by rwa [map_zero])
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : PC F e.m) hδ) ?_
  intro p hp
  rw [Metric.mem_ball, dist_zero_right] at hp
  apply hWU
  change (∑' v, mvEvalTerm (pushDatumC D hD).canonicalMap (bridgeGenC D e hD)
    (bridgeToRestrictedC e.m p) v) ∈ (W : Set (presheafValue (pushDatumC D hD)))
  refine tsum_mem_of_isOpen_addSubgroup'
    (mvEvalTerm_summable (pushDatumC D hD).canonicalMap
      (canonicalMap_continuous (pushDatumC D hD))
      (bridgeGenC D e hD) (bridgeGenC_isBounded D e hD) (bridgeToRestrictedC e.m p))
    W.isOpen fun v => ?_
  have hcoeff : ‖MvPowerSeries.coeff v p.1‖ < δ :=
    lt_of_le_of_lt (norm_coeff_le_gauss p v) hp
  have hVmem : (pushDatumC D hD).canonicalMap (MvPowerSeries.coeff v p.1) ∈ V :=
    hball (by rwa [Metric.mem_ball, dist_zero_right])
  change mvEvalTerm (pushDatumC D hD).canonicalMap (bridgeGenC D e hD)
    (bridgeToRestrictedC e.m p) v ∈ W
  rw [show mvEvalTerm (pushDatumC D hD).canonicalMap (bridgeGenC D e hD)
      (bridgeToRestrictedC e.m p) v =
      (∏ i, bridgeGenC D e hD i ^ (v i)) *
        (pushDatumC D hD).canonicalMap (MvPowerSeries.coeff v p.1) from by
    rw [mvEvalTerm]; exact mul_comm _ _]
  exact hVR (Set.mul_mem_mul ⟨v, rfl⟩ hVmem)

theorem bridgeRevC_continuous (hD : D.IsRational) :
    Continuous (bridgeRevC D e hD) := by
  rw [(QuotientRing.isOpenQuotientMap_mk (IC F e.m D.s e.f)).isQuotientMap.continuous_iff]
  exact bridgeEvalC_continuous D e hD

/-- `revC ∘ fwdC = id` — the 𝓒-bridge is split-injective. -/
theorem bridgeRevC_bridgeFwdC (hD : D.IsRational)
    (x : presheafValue (pushDatumC D hD)) :
    bridgeRevC D e hD (bridgeFwdC D e hD x) = x := by
  letI := (pushDatumC D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isUniformAddGroup
  haveI : RegularSpace (presheafValue (pushDatumC D hD)) := UniformSpace.to_regularSpace
  have hcomp : (bridgeRevC D e hD).comp (bridgeLocHomC D e hD) =
      (pushDatumC D hD).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (pushDatumC D hD).s) ?_
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [bridgeLocHomC_algebraMap, bridgeRevC_bridgeBaseC]
    rfl
  have hdense : DenseRange ((pushDatumC D hD).coeRingHom :
      Localization.Away (pushDatumC D hD).s → presheafValue (pushDatumC D hD)) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => bridgeRevC D e hD (bridgeFwdC D e hD y)) = fun y => y :=
    hdense.equalizer ((bridgeRevC_continuous D e hD).comp (bridgeFwdC_continuous D e hD))
      continuous_id (by
        funext a
        show bridgeRevC D e hD (bridgeFwdC D e hD ((pushDatumC D hD).coeRingHom a)) =
          (pushDatumC D hD).coeRingHom a
        rw [bridgeFwdC_coe]
        exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

theorem bridgeFwdC_injective (hD : D.IsRational) :
    Function.Injective (bridgeFwdC D e hD) :=
  Function.LeftInverse.injective (g := bridgeRevC D e hD) (bridgeRevC_bridgeFwdC D e hD)

/-! #### Second-level covariant maps `𝒪_𝓑(D_B) → 𝒪_𝓓(D_D)`, `𝒪_𝓒(D_C) → 𝒪_𝓓(D_D)`
and the coherence/naturality squares consumed by the 𝓓-matching step -/

theorem continuous_rhoB : Continuous (rhoB F) :=
  AddMonoidHomClass.continuous_of_bound (rhoB F) 1 fun a => by
    rw [one_mul, norm_rhoB]

/-- `ρ_B` pushes the 𝓑-datum to the 𝓓-datum (via the square identity). -/
noncomputable def mapBD (hD : D.IsRational) :
    presheafValue (pushDatumB D hD) →+* presheafValue (pushDatumD D hD) :=
  presheafValueMapOfHom (rhoB F) (continuous_rhoB) (pushDatumB D hD) (pushDatumD D hD)
    ((square_commutes F D.s).symm)
    (by
      intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
      rw [square_commutes F t₀]
      exact Finset.mem_image_of_mem _ ht₀)

/-- `ρ_C` pushes the 𝓒-datum to the 𝓓-datum. -/
noncomputable def mapCD (hD : D.IsRational) :
    presheafValue (pushDatumC D hD) →+* presheafValue (pushDatumD D hD) :=
  presheafValueMapOfHom (rhoC F) (continuous_rhoC) (pushDatumC D hD) (pushDatumD D hD)
    rfl
    (by
      intro t ht
      obtain ⟨t₀, ht₀, rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_image_of_mem _ ht₀)

theorem mapBD_continuous (hD : D.IsRational) : Continuous (mapBD D hD) := by
  unfold mapBD
  exact presheafValueMapOfHom_continuous _ _ _ _ _ _

theorem mapCD_continuous (hD : D.IsRational) : Continuous (mapCD D hD) := by
  unfold mapCD
  exact presheafValueMapOfHom_continuous _ _ _ _ _ _

/-- The 𝓓-coherence of the two composite pushes ([FJP] (4.9): the square commutes on
sections). -/
theorem mapBD_mapB_eq_mapCD_mapC (hD : D.IsRational) :
    (mapBD D hD).comp (presheafValueMapB D hD) =
      (mapCD D hD).comp (presheafValueMapC D hD) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : RegularSpace (presheafValue (pushDatumD D hD)) := UniformSpace.to_regularSpace
  have hcomp : ((mapBD D hD).comp (presheafValueMapB D hD)).comp D.coeRingHom =
      ((mapCD D hD).comp (presheafValueMapC D hD)).comp D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [show D.coeRingHom (algebraMap (JetA F) (Localization.Away D.s) a) =
        D.canonicalMap a from rfl,
      presheafValueMapB_canonicalMap, presheafValueMapC_canonicalMap,
      show mapBD D hD ((pushDatumB D hD).canonicalMap (jB F a)) =
        (pushDatumD D hD).canonicalMap (rhoB F (jB F a)) from
        presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ (jB F a),
      show mapCD D hD ((pushDatumC D hD).canonicalMap (iotaC F a)) =
        (pushDatumD D hD).canonicalMap (rhoC F (iotaC F a)) from
        presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ (iotaC F a),
      square_commutes F a]
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : ⇑((mapBD D hD).comp (presheafValueMapB D hD)) =
      ⇑((mapCD D hD).comp (presheafValueMapC D hD)) :=
    hdense.equalizer
      ((mapBD_continuous D hD).comp (presheafValueMapB_continuous D hD))
      ((mapCD_continuous D hD).comp (presheafValueMapC_continuous D hD))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

/-- The quotient projections are norm-nonincreasing along `ρ` (ε-representatives). -/
theorem norm_locRhoB_le (x : locB F e.m D.s e.f) :
    ‖locRhoB F e.m D.s e.f x‖ ≤ ‖x‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨p, hp, hpn⟩ := Ideal.Quotient.norm_mk_lt x hε
  calc ‖locRhoB F e.m D.s e.f x‖
      = ‖locRhoB F e.m D.s e.f (Ideal.Quotient.mk (IB F e.m D.s e.f) p)‖ := by rw [hp]
    _ = ‖Ideal.Quotient.mk (ID F e.m D.s e.f) (extRhoB F e.m p)‖ := by
        rw [locRhoB_mk]
    _ ≤ ‖extRhoB F e.m p‖ := Ideal.Quotient.norm_mk_le _ _
    _ ≤ ‖p‖ := norm_mapRestricted_le _ _ _ p
    _ ≤ ‖x‖ + ε := hpn.le

theorem norm_locRhoC_le (x : locC F e.m D.s e.f) :
    ‖locRhoC F e.m D.s e.f x‖ ≤ ‖x‖ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨p, hp, hpn⟩ := Ideal.Quotient.norm_mk_lt x hε
  calc ‖locRhoC F e.m D.s e.f x‖
      = ‖locRhoC F e.m D.s e.f (Ideal.Quotient.mk (IC F e.m D.s e.f) p)‖ := by rw [hp]
    _ = ‖Ideal.Quotient.mk (ID F e.m D.s e.f) (extRhoC F e.m p)‖ := by
        rw [locRhoC_mk]
    _ ≤ ‖extRhoC F e.m p‖ := Ideal.Quotient.norm_mk_le _ _
    _ ≤ ‖p‖ := norm_mapRestricted_le _ _ _ p
    _ ≤ ‖x‖ + ε := hpn.le

theorem locRhoB_continuous : Continuous (locRhoB F e.m D.s e.f) :=
  AddMonoidHomClass.continuous_of_bound (locRhoB F e.m D.s e.f) 1 fun x => by
    rw [one_mul]; exact norm_locRhoB_le D e x

theorem locRhoC_continuous : Continuous (locRhoC F e.m D.s e.f) :=
  AddMonoidHomClass.continuous_of_bound (locRhoC F e.m D.s e.f) 1 fun x => by
    rw [one_mul]; exact norm_locRhoC_le D e x

open GraphKoszul in
/-- `ρ`-naturality, 𝓑-side: `locRhoB ∘ fwdB = fwdD ∘ mapBD`. -/
theorem locRhoB_bridgeFwdB (hD : D.IsRational) :
    (locRhoB F e.m D.s e.f).comp (bridgeFwdB D e hD) =
      (bridgeFwdD D e hD).comp (mapBD D hD) := by
  letI := (pushDatumB D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumB D hD).s) :=
    (pushDatumB D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumB D hD).s) :=
    (pushDatumB D hD).isUniformAddGroup
  haveI hcl : IsClosed ((ID F e.m D.s e.f : Set (PD F e.m))) := isClosed_ID' D e
  haveI : NormedAddCommGroup (locD F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  have hdense : DenseRange ((pushDatumB D hD).coeRingHom :
      Localization.Away (pushDatumB D hD).s → presheafValue (pushDatumB D hD)) :=
    UniformSpace.Completion.denseRange_coe
  have hcomp : ((locRhoB F e.m D.s e.f).comp (bridgeFwdB D e hD)).comp
      (pushDatumB D hD).coeRingHom =
      ((bridgeFwdD D e hD).comp (mapBD D hD)).comp (pushDatumB D hD).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (pushDatumB D hD).s) ?_
    refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply]
    rw [show (pushDatumB D hD).coeRingHom (algebraMap (JetB F)
        (Localization.Away (pushDatumB D hD).s) b) =
        (pushDatumB D hD).canonicalMap b from rfl,
      show bridgeFwdB D e hD ((pushDatumB D hD).canonicalMap b) =
        bridgeBaseB D e b from by
        rw [show (pushDatumB D hD).canonicalMap b =
          (pushDatumB D hD).coeRingHom (algebraMap (JetB F)
            (Localization.Away (pushDatumB D hD).s) b) from rfl,
          bridgeFwdB_coe, bridgeLocHomB_algebraMap],
      show mapBD D hD ((pushDatumB D hD).canonicalMap b) =
        (pushDatumD D hD).canonicalMap (rhoB F b) from
        presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ b,
      show bridgeFwdD D e hD ((pushDatumD D hD).canonicalMap (rhoB F b)) =
        bridgeBaseD D e (rhoB F b) from by
        rw [show (pushDatumD D hD).canonicalMap (rhoB F b) =
          (pushDatumD D hD).coeRingHom (algebraMap (JetD F)
            (Localization.Away (pushDatumD D hD).s) (rhoB F b)) from rfl,
          bridgeFwdD_coe, bridgeLocHomD_algebraMap]]
    rw [show bridgeBaseB D e b =
        Ideal.Quotient.mk (IB F e.m D.s e.f) (polyToP (MvPolynomial.C b)) from rfl,
      locRhoB_mk,
      show extRhoB F e.m (polyToP (MvPolynomial.C b)) =
        polyToP (MvPolynomial.map (rhoB F) (MvPolynomial.C b)) from
        mapRestricted_polyToP _ _ _ (MvPolynomial.C b),
      MvPolynomial.map_C]
    rfl
  have h_eq : ⇑((locRhoB F e.m D.s e.f).comp (bridgeFwdB D e hD)) =
      ⇑((bridgeFwdD D e hD).comp (mapBD D hD)) :=
    hdense.equalizer
      ((locRhoB_continuous D e).comp (bridgeFwdB_continuous D e hD))
      ((bridgeFwdD_continuous D e hD).comp (mapBD_continuous D hD))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

open GraphKoszul in
/-- `ρ`-naturality, 𝓒-side: `locRhoC ∘ fwdC = fwdD ∘ mapCD`. -/
theorem locRhoC_bridgeFwdC (hD : D.IsRational) :
    (locRhoC F e.m D.s e.f).comp (bridgeFwdC D e hD) =
      (bridgeFwdD D e hD).comp (mapCD D hD) := by
  letI := (pushDatumC D hD).uniformSpace
  letI : IsTopologicalRing (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away (pushDatumC D hD).s) :=
    (pushDatumC D hD).isUniformAddGroup
  haveI hcl : IsClosed ((ID F e.m D.s e.f : Set (PD F e.m))) := isClosed_ID' D e
  haveI : NormedAddCommGroup (locD F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  have hdense : DenseRange ((pushDatumC D hD).coeRingHom :
      Localization.Away (pushDatumC D hD).s → presheafValue (pushDatumC D hD)) :=
    UniformSpace.Completion.denseRange_coe
  have hcomp : ((locRhoC F e.m D.s e.f).comp (bridgeFwdC D e hD)).comp
      (pushDatumC D hD).coeRingHom =
      ((bridgeFwdD D e hD).comp (mapCD D hD)).comp (pushDatumC D hD).coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (pushDatumC D hD).s) ?_
    refine RingHom.ext fun b => ?_
    simp only [RingHom.comp_apply]
    rw [show (pushDatumC D hD).coeRingHom (algebraMap (JetC F)
        (Localization.Away (pushDatumC D hD).s) b) =
        (pushDatumC D hD).canonicalMap b from rfl,
      show bridgeFwdC D e hD ((pushDatumC D hD).canonicalMap b) =
        bridgeBaseC D e b from by
        rw [show (pushDatumC D hD).canonicalMap b =
          (pushDatumC D hD).coeRingHom (algebraMap (JetC F)
            (Localization.Away (pushDatumC D hD).s) b) from rfl,
          bridgeFwdC_coe, bridgeLocHomC_algebraMap],
      show mapCD D hD ((pushDatumC D hD).canonicalMap b) =
        (pushDatumD D hD).canonicalMap (rhoC F b) from
        presheafValueMapOfHom_canonicalMap _ _ _ _ _ _ b,
      show bridgeFwdD D e hD ((pushDatumD D hD).canonicalMap (rhoC F b)) =
        bridgeBaseD D e (rhoC F b) from by
        rw [show (pushDatumD D hD).canonicalMap (rhoC F b) =
          (pushDatumD D hD).coeRingHom (algebraMap (JetD F)
            (Localization.Away (pushDatumD D hD).s) (rhoC F b)) from rfl,
          bridgeFwdD_coe, bridgeLocHomD_algebraMap]]
    rw [show bridgeBaseC D e b =
        Ideal.Quotient.mk (IC F e.m D.s e.f) (polyToP (MvPolynomial.C b)) from rfl,
      locRhoC_mk,
      show extRhoC F e.m (polyToP (MvPolynomial.C b)) =
        polyToP (MvPolynomial.map (rhoC F) (MvPolynomial.C b)) from
        mapRestricted_polyToP _ _ _ (MvPolynomial.C b),
      MvPolynomial.map_C]
    rfl
  have h_eq : ⇑((locRhoC F e.m D.s e.f).comp (bridgeFwdC D e hD)) =
      ⇑((bridgeFwdD D e hD).comp (mapCD D hD)) :=
    hdense.equalizer
      ((locRhoC_continuous D e).comp (bridgeFwdC_continuous D e hD))
      ((bridgeFwdD_continuous D e hD).comp (mapCD_continuous D hD))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

end GraphBridgeInfra

/-- The graph bridge for 𝓐 ([FJP] Lemma 1.1: the separated completion of the graph
quotient "is therefore canonically the underlying Tate algebra of Huber's rational
localization `E_α`"; by Lemma 4.3 the ideal is closed so no further completion is needed).
Topological ring isomorphism `𝒪_𝓐(D) ≅ P_𝓐 ⧸ I_𝓐`. -/
def graphBridgeA (D : RationalLocData (JetA F)) (hD : D.IsRational) (e : DatumEnum D) :
    presheafValue D ≃+* locA (F := F) e.m D.s e.f where
  toFun := bridgeFwd D e hD
  invFun := bridgeRev D e
  left_inv := bridgeRev_bridgeFwd D e hD
  right_inv := bridgeFwd_bridgeRev D e hD
  map_mul' := map_mul (bridgeFwd D e hD)
  map_add' := map_add (bridgeFwd D e hD)

theorem graphBridgeA_continuous (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (e : DatumEnum D) : Continuous (graphBridgeA D hD e) :=
  bridgeFwd_continuous D e hD

theorem graphBridgeA_symm_continuous (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (e : DatumEnum D) : Continuous (graphBridgeA D hD e).symm :=
  bridgeRev_continuous D e

open GraphKoszul in
/-- The 𝓑-side naturality square (mirror of `graphBridge_natural_C`, consumed by the
transfer): `bridgeFwdB ∘ presheafValueMapB = locJB ∘ graphBridgeA`. -/
theorem graphBridge_natural_B (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (e : DatumEnum D) :
    (bridgeFwdB D e hD).comp (presheafValueMapB D hD) =
      (locJB F e.m D.s e.f).comp
        (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI hcl : IsClosed ((IB F e.m D.s e.f : Set (PB F e.m))) := isClosed_IB' D e
  haveI : NormedAddCommGroup (locB F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have hcomp : ((bridgeFwdB D e hD).comp (presheafValueMapB D hD)).comp D.coeRingHom =
      ((locJB F e.m D.s e.f).comp
        (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f)).comp
        D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show (D.coeRingHom (algebraMap (JetA F) (Localization.Away D.s) a)) =
        D.canonicalMap a from rfl,
      presheafValueMapB_canonicalMap,
      show (pushDatumB D hD).canonicalMap (jB F a) =
        (pushDatumB D hD).coeRingHom (algebraMap (JetB F)
          (Localization.Away (pushDatumB D hD).s) (jB F a)) from rfl,
      bridgeFwdB_coe, bridgeLocHomB_algebraMap,
      show (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f)
        (D.canonicalMap a) = bridgeFwd D e hD (D.canonicalMap a) from rfl,
      bridgeFwd_canonicalMap]
    rw [show bridgeBase D e a =
        Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.C a)) from rfl,
      locJB_mk,
      show extJB F e.m (polyToP (MvPolynomial.C a)) =
        polyToP (MvPolynomial.map (jB F) (MvPolynomial.C a)) from
        mapRestricted_polyToP _ _ _ (MvPolynomial.C a),
      MvPolynomial.map_C]
    rfl
  have h_eq : ⇑((bridgeFwdB D e hD).comp (presheafValueMapB D hD)) =
      ⇑((locJB F e.m D.s e.f).comp
        (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f)) :=
    hdense.equalizer
      ((bridgeFwdB_continuous D e hD).comp (presheafValueMapB_continuous D hD))
      ((locJB_lipschitz F e.m D.s e.f).continuous.comp
        (graphBridgeA_continuous D hD e))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

open GraphKoszul in
/-- The bridge intertwines the covariant maps with the coefficientwise localized square
([FJP] Lemma 4.6 / Lemma 5.1 naturality, 𝓒 side; analogous statements for 𝓑, 𝓓 are
formulated in the transfer file where consumed). Statement fix (recorded, L5.4 attack 3):
the skeleton's `True` stub replaced by the real intertwining
`bridgeFwdC ∘ presheafValueMapC = locIotaC ∘ graphBridgeA`. -/
theorem graphBridge_natural_C (D : RationalLocData (JetA F)) (hD : D.IsRational)
    (e : DatumEnum D) :
    (bridgeFwdC D e hD).comp (presheafValueMapC D hD) =
      (locIotaC F e.m D.s e.f).comp
        (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI hcl : IsClosed ((IC F e.m D.s e.f : Set (PC F e.m))) := isClosed_IC' D e
  haveI : NormedAddCommGroup (locC F e.m D.s e.f) :=
    Submodule.Quotient.normedAddCommGroup _
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have hcomp : ((bridgeFwdC D e hD).comp (presheafValueMapC D hD)).comp D.coeRingHom =
      ((locIotaC F e.m D.s e.f).comp
        (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f)).comp
        D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show (D.coeRingHom (algebraMap (JetA F) (Localization.Away D.s) a)) =
        D.canonicalMap a from rfl,
      presheafValueMapC_canonicalMap,
      show (pushDatumC D hD).canonicalMap (iotaC F a) =
        (pushDatumC D hD).coeRingHom (algebraMap (JetC F)
          (Localization.Away (pushDatumC D hD).s) (iotaC F a)) from rfl,
      bridgeFwdC_coe, bridgeLocHomC_algebraMap,
      show (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f)
        (D.canonicalMap a) = bridgeFwd D e hD (D.canonicalMap a) from rfl,
      bridgeFwd_canonicalMap]
    -- `bridgeBaseC (ι a) = locIotaC (bridgeBase a)`: both are `mk (polyToP (C (ι a)))`.
    rw [show bridgeBase D e a =
        Ideal.Quotient.mk (IA F e.m D.s e.f) (polyToP (MvPolynomial.C a)) from rfl,
      locIotaC_mk,
      show extIotaC F e.m (polyToP (MvPolynomial.C a)) =
        polyToP (MvPolynomial.map (iotaC F) (MvPolynomial.C a)) from
        mapRestricted_polyToP _ _ _ (MvPolynomial.C a),
      MvPolynomial.map_C]
    rfl
  have h_eq : ⇑((bridgeFwdC D e hD).comp (presheafValueMapC D hD)) =
      ⇑((locIotaC F e.m D.s e.f).comp
        (graphBridgeA D hD e : presheafValue D →+* locA F e.m D.s e.f)) :=
    hdense.equalizer
      ((bridgeFwdC_continuous D e hD).comp (presheafValueMapC_continuous D hD))
      ((locIotaC_lipschitz F e.m D.s e.f).continuous.comp
        (graphBridgeA_continuous D hD e))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact DFunLike.ext _ _ fun x => congrFun h_eq x

/-! ### Vertices: loc-lift instances (noetherian discharger applies) -/

instance : HasLocLiftPowerBounded (JetB F) := hasLocLiftPowerBounded_faithful

instance : HasLocLiftPowerBounded (JetC F) := hasLocLiftPowerBounded_faithful

instance : HasLocLiftPowerBounded (JetD F) := hasLocLiftPowerBounded_faithful

/-! ### `HasLocLiftPowerBounded 𝓐`, componentwise

𝓐 is not noetherian, so `hasLocLiftPowerBounded_faithful` does not apply. Both fields are
derived through the Milnor description of `𝒪_𝓐(D)` ([FJP] Lemma 5.1 + Prop 4.5): a unit in
both comparison localizations whose inverses match in 𝓓 is a unit in the fiber product, and
power-boundedness in the max norm is componentwise. -/

instance hasLocLiftPowerBounded_JetA : HasLocLiftPowerBounded (JetA F) :=
  hasLocLiftPowerBounded_faithful

/-! ### Naturality with restriction ([FJP] Lemma 4.6, Lemma 5.1)

With the loc-lift instances available, the project's `restrictionMap` vocabulary applies to
all four rings, and the covariant maps commute with it. -/

-- (the private `restrictionMapHom_canonicalMap_generic` and the generic
-- `presheafValueMapOfHom_restriction` moved to `PresheafFunctoriality.lean`,
-- `namespace ValuationSpectrum`; reused here via `open`.)

theorem presheafValueMapC_restriction (D D' : RationalLocData (JetA F))
    (hD : D.IsRational) (hD' : D'.IsRational)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hpush : rationalOpen (pushDatumC D' hD').T (pushDatumC D' hD').s ⊆
      rationalOpen (pushDatumC D hD).T (pushDatumC D hD).s) (x : presheafValue D) :
    presheafValueMapC D' hD' (restrictionMap D D' h x) =
      restrictionMap (pushDatumC D hD) (pushDatumC D' hD') hpush
        (presheafValueMapC D hD x) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : RegularSpace (presheafValue (pushDatumC D' hD')) :=
    UniformSpace.to_regularSpace
  have hcomp : ((presheafValueMapC D' hD').comp (restrictionMapHom D D' h)).comp
      D.coeRingHom =
      ((restrictionMapHom (pushDatumC D hD) (pushDatumC D' hD') hpush).comp
        (presheafValueMapC D hD)).comp D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show D.coeRingHom (algebraMap (JetA F) (Localization.Away D.s) a) =
        D.canonicalMap a from rfl,
      restrictionMapHom_canonicalMap_generic D D' h, presheafValueMapC_canonicalMap,
      presheafValueMapC_canonicalMap,
      restrictionMapHom_canonicalMap_generic (pushDatumC D hD) (pushDatumC D' hD') hpush]
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => presheafValueMapC D' hD' (restrictionMapHom D D' h y)) =
      fun y => restrictionMapHom (pushDatumC D hD) (pushDatumC D' hD') hpush
        (presheafValueMapC D hD y) :=
    hdense.equalizer
      ((presheafValueMapC_continuous D' hD').comp (restrictionMapHom_continuous D D' h))
      ((restrictionMapHom_continuous _ _ hpush).comp (presheafValueMapC_continuous D hD))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

theorem presheafValueMapB_restriction (D D' : RationalLocData (JetA F))
    (hD : D.IsRational) (hD' : D'.IsRational)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s)
    (hpush : rationalOpen (pushDatumB D' hD').T (pushDatumB D' hD').s ⊆
      rationalOpen (pushDatumB D hD).T (pushDatumB D hD).s) (x : presheafValue D) :
    presheafValueMapB D' hD' (restrictionMap D D' h x) =
      restrictionMap (pushDatumB D hD) (pushDatumB D' hD') hpush
        (presheafValueMapB D hD x) := by
  letI := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : RegularSpace (presheafValue (pushDatumB D' hD')) :=
    UniformSpace.to_regularSpace
  have hcomp : ((presheafValueMapB D' hD').comp (restrictionMapHom D D' h)).comp
      D.coeRingHom =
      ((restrictionMapHom (pushDatumB D hD) (pushDatumB D' hD') hpush).comp
        (presheafValueMapB D hD)).comp D.coeRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers D.s) ?_
    ext a
    simp only [RingHom.comp_apply]
    rw [show D.coeRingHom (algebraMap (JetA F) (Localization.Away D.s) a) =
        D.canonicalMap a from rfl,
      restrictionMapHom_canonicalMap_generic D D' h, presheafValueMapB_canonicalMap,
      presheafValueMapB_canonicalMap,
      restrictionMapHom_canonicalMap_generic (pushDatumB D hD) (pushDatumB D' hD') hpush]
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.denseRange_coe
  have h_eq : (fun y => presheafValueMapB D' hD' (restrictionMapHom D D' h y)) =
      fun y => restrictionMapHom (pushDatumB D hD) (pushDatumB D' hD') hpush
        (presheafValueMapB D hD y) :=
    hdense.equalizer
      ((presheafValueMapB_continuous D' hD').comp (restrictionMapHom_continuous D D' h))
      ((restrictionMapHom_continuous _ _ hpush).comp (presheafValueMapB_continuous D hD))
      (by funext a; exact DFunLike.congr_fun hcomp a)
  exact congrFun h_eq x

/-! ### Coverage transfer ([FJP] Lemma 5.2, first display: `U_E = ⋃ᵢ (Uᵢ)_E`) -/

/-- Power-bounded elements of 𝓐 stay power-bounded under any norm-nonincreasing ring map
(the [FJP] "never bare continuity" transfer: 𝓐° = unit ball by Prop 2.3, and
norm-≤-1 elements are power-bounded in any seminormed ring). -/
theorem plus_le_comap_of_norm_le {E : Type*} [SeminormedCommRing E]
    (φ : JetA F →+* E) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) {x : JetA F}
    (hx : TopologicalRing.IsPowerBounded x) :
    TopologicalRing.IsPowerBounded (φ x) :=
  isPowerBounded_of_norm_le_one
    (le_trans (hφ x) ((isPowerBounded_JetA_iff F x).mp hx))

/-- Inverse images preserve the rational inequalities: pushed rational opens are the
`spaComap`-preimages. (Pointwise: `v ∈ rationalOpen (T_E, s_E) ↔ v ∘ ι ∈ rationalOpen (T, s)`
for `v` in the vertex spectrum.) -/
theorem mem_rationalOpen_pushDatumC_iff (D : RationalLocData (JetA F))
    (hD : D.IsRational) (v : Spv (JetC F)) (hv : v ∈ Spa (JetC F) (ringPlus (JetC F))) :
    v ∈ rationalOpen (pushDatumC D hD).T (pushDatumC D hD).s ↔
      ValuationSpectrum.comap (iotaC F) v ∈ rationalOpen D.T D.s := by
  have hcomap : ValuationSpectrum.comap (iotaC F) v ∈ Spa (JetA F) (ringPlus (JetA F)) :=
    comap_mem_spa (continuous_iotaC) (fun x hx =>
      plus_le_comap_of_norm_le (iotaC F) (fun a => le_of_eq (norm_iotaC F a)) hx) hv
  constructor
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hcomap, fun t ht => ?_, fun h0 => hs0 ?_⟩
    · rw [comap_vle]
      exact hvle (iotaC F t) (Finset.mem_image_of_mem _ ht)
    · have := (comap_vle (iotaC F) v D.s 0)
      rw [map_zero] at this
      rw [show (pushDatumC D hD).s = iotaC F D.s from rfl, ← this]
      exact h0
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun h0 => hs0 ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have := hvle t ht
      rwa [comap_vle] at this
    · have := (comap_vle (iotaC F) v D.s 0)
      rw [map_zero] at this
      rw [this]
      exact h0

-- (this declaration elaborated fine at the default; the file-wide `false` above makes
-- its `whnf`-checks explode — restore the default here)
theorem mem_rationalOpen_pushDatumB_iff (D : RationalLocData (JetA F))
    (hD : D.IsRational) (v : Spv (JetB F)) (hv : v ∈ Spa (JetB F) (ringPlus (JetB F))) :
    v ∈ rationalOpen (pushDatumB D hD).T (pushDatumB D hD).s ↔
      ValuationSpectrum.comap (jB F) v ∈ rationalOpen D.T D.s := by
  have hcomap : ValuationSpectrum.comap (jB F) v ∈ Spa (JetA F) (ringPlus (JetA F)) :=
    comap_mem_spa (continuous_jB) (fun x hx =>
      plus_le_comap_of_norm_le (jB F) (norm_jB_le F) hx) hv
  constructor
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hcomap, fun t ht => ?_, fun h0 => hs0 ?_⟩
    · rw [comap_vle]
      exact hvle (jB F t) (Finset.mem_image_of_mem _ ht)
    · have := (comap_vle (jB F) v D.s 0)
      rw [map_zero] at this
      rw [show (pushDatumB D hD).s = jB F D.s from rfl, ← this]
      exact h0
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun h0 => hs0 ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have := hvle t ht
      rwa [comap_vle] at this
    · have := (comap_vle (jB F) v D.s 0)
      rw [map_zero] at this
      rw [this]
      exact h0

/-- The 𝓓-side pointwise coverage transfer (supporting lemma for `pushCoveringD`). -/
theorem mem_rationalOpen_pushDatumD_iff (D : RationalLocData (JetA F))
    (hD : D.IsRational) (v : Spv (JetD F)) (hv : v ∈ Spa (JetD F) (ringPlus (JetD F))) :
    v ∈ rationalOpen (pushDatumD D hD).T (pushDatumD D hD).s ↔
      ValuationSpectrum.comap ((rhoC F).comp (iotaC F)) v ∈ rationalOpen D.T D.s := by
  have hcomap : ValuationSpectrum.comap ((rhoC F).comp (iotaC F)) v ∈
      Spa (JetA F) (ringPlus (JetA F)) :=
    comap_mem_spa (by rw [RingHom.coe_comp]; exact (continuous_rhoC).comp (continuous_iotaC))
      (fun x hx => Subring.mem_comap.mpr
        (plus_le_comap_of_norm_le ((rhoC F).comp (iotaC F))
          (fun a => le_trans (norm_rhoC_le F (iotaC F a)) (le_of_eq (norm_iotaC F a)))
          (show TopologicalRing.IsPowerBounded x from hx))) hv
  constructor
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hcomap, fun t ht => ?_, fun h0 => hs0 ?_⟩
    · rw [comap_vle]
      exact hvle (((rhoC F).comp (iotaC F)) t) (Finset.mem_image_of_mem _ ht)
    · have := (comap_vle ((rhoC F).comp (iotaC F)) v D.s 0)
      rw [map_zero] at this
      rw [show (pushDatumD D hD).s = ((rhoC F).comp (iotaC F)) D.s from rfl, ← this]
      exact h0
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun h0 => hs0 ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have := hvle t ht
      rwa [comap_vle] at this
    · have := (comap_vle ((rhoC F).comp (iotaC F)) v D.s 0)
      rw [map_zero] at this
      rw [this]
      exact h0

/-- The pushed covering of a rational covering of 𝓐, at the 𝓒-vertex
([FJP] Lemma 5.2: "Inverse images preserve the defining valuation inequalities and unions.
Hence, for `E = B, C, D`, `U_E = ⋃ᵢ (Uᵢ)_E` is a rational covering"). -/
def pushCoveringC (C : RationalCoveringData (JetA F)) (hC : C.IsRational) :
    RationalCoveringData (JetC F) where
  base := pushDatumC C.base hC.base
  covers := C.covers.attach.image fun d => pushDatumC d.1 (hC.piece d.2)
  hsubset := by
    intro D' hD' v hv
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
    have hvspa : v ∈ Spa (JetC F) (ringPlus (JetC F)) := hv.1
    exact (mem_rationalOpen_pushDatumC_iff C.base hC.base v hvspa).mpr
      (C.hsubset d.1 d.2
        ((mem_rationalOpen_pushDatumC_iff d.1 (hC.piece d.2) v hvspa).mp hv))
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (JetC F) (ringPlus (JetC F)) := hv.1
    obtain ⟨D₀, hD₀, hmem⟩ := C.hcover _
      ((mem_rationalOpen_pushDatumC_iff C.base hC.base v hvspa).mp hv)
    exact ⟨pushDatumC D₀ (hC.piece hD₀),
      Finset.mem_image.mpr ⟨⟨D₀, hD₀⟩, Finset.mem_attach _ _, rfl⟩,
      (mem_rationalOpen_pushDatumC_iff D₀ (hC.piece hD₀) v hvspa).mpr hmem⟩

def pushCoveringB (C : RationalCoveringData (JetA F)) (hC : C.IsRational) :
    RationalCoveringData (JetB F) where
  base := pushDatumB C.base hC.base
  covers := C.covers.attach.image fun d => pushDatumB d.1 (hC.piece d.2)
  hsubset := by
    intro D' hD' v hv
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
    have hvspa : v ∈ Spa (JetB F) (ringPlus (JetB F)) := hv.1
    exact (mem_rationalOpen_pushDatumB_iff C.base hC.base v hvspa).mpr
      (C.hsubset d.1 d.2
        ((mem_rationalOpen_pushDatumB_iff d.1 (hC.piece d.2) v hvspa).mp hv))
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (JetB F) (ringPlus (JetB F)) := hv.1
    obtain ⟨D₀, hD₀, hmem⟩ := C.hcover _
      ((mem_rationalOpen_pushDatumB_iff C.base hC.base v hvspa).mp hv)
    exact ⟨pushDatumB D₀ (hC.piece hD₀),
      Finset.mem_image.mpr ⟨⟨D₀, hD₀⟩, Finset.mem_attach _ _, rfl⟩,
      (mem_rationalOpen_pushDatumB_iff D₀ (hC.piece hD₀) v hvspa).mpr hmem⟩

def pushCoveringD (C : RationalCoveringData (JetA F)) (hC : C.IsRational) :
    RationalCoveringData (JetD F) where
  base := pushDatumD C.base hC.base
  covers := C.covers.attach.image fun d => pushDatumD d.1 (hC.piece d.2)
  hsubset := by
    intro D' hD' v hv
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
    have hvspa : v ∈ Spa (JetD F) (ringPlus (JetD F)) := hv.1
    exact (mem_rationalOpen_pushDatumD_iff C.base hC.base v hvspa).mpr
      (C.hsubset d.1 d.2
        ((mem_rationalOpen_pushDatumD_iff d.1 (hC.piece d.2) v hvspa).mp hv))
  hcover := by
    intro v hv
    have hvspa : v ∈ Spa (JetD F) (ringPlus (JetD F)) := hv.1
    obtain ⟨D₀, hD₀, hmem⟩ := C.hcover _
      ((mem_rationalOpen_pushDatumD_iff C.base hC.base v hvspa).mp hv)
    exact ⟨pushDatumD D₀ (hC.piece hD₀),
      Finset.mem_image.mpr ⟨⟨D₀, hD₀⟩, Finset.mem_attach _ _, rfl⟩,
      (mem_rationalOpen_pushDatumD_iff D₀ (hC.piece hD₀) v hvspa).mpr hmem⟩

theorem pushCoveringB_isRational {C : RationalCoveringData (JetA F)} (hC : C.IsRational) :
    (pushCoveringB C hC).IsRational := by
  refine ⟨pushDatumB_isRational hC.base, ?_⟩
  intro D' hD'
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
  exact pushDatumB_isRational (hC.piece d.2)

theorem pushCoveringC_isRational {C : RationalCoveringData (JetA F)} (hC : C.IsRational) :
    (pushCoveringC C hC).IsRational := by
  refine ⟨pushDatumC_isRational hC.base, ?_⟩
  intro D' hD'
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
  exact pushDatumC_isRational (hC.piece d.2)

theorem pushCoveringD_isRational {C : RationalCoveringData (JetA F)} (hC : C.IsRational) :
    (pushCoveringD C hC).IsRational := by
  refine ⟨pushDatumD_isRational hC.base, ?_⟩
  intro D' hD'
  obtain ⟨d, -, rfl⟩ := Finset.mem_image.mp hD'
  exact pushDatumD_isRational (hC.piece d.2)

/-! ### Intersection data ([FJP] Lemma 5.2: `(U_{ij})_E = (U_i)_E ∩ (U_j)_E`) -/

open scoped Pointwise in
/-- Spans of pointwise-product finsets of two spanning sets span (`⊤ * ⊤ = ⊤`).
The `DecidableEq` binder is deliberate: it makes the use site instantiate `Finset.image`
with the ambient instance, so the conclusion matches syntactically (at `JetA` the ambient
instance is `Subtype.instDecidableEq`, not `Classical.decEq`, and defeq-checking the two
unfolds the whole jet tower). -/
theorem span_mul_image_eq_top {A : Type*} [CommRing A] [DecidableEq A] {T₁ T₂ : Finset A}
    (h₁ : Ideal.span (T₁ : Set A) = ⊤) (h₂ : Ideal.span (T₂ : Set A) = ⊤) :
    Ideal.span ((((T₁ ×ˢ T₂).image fun p => p.1 * p.2 : Finset A)) : Set A) = ⊤ := by
  have hcoe : ((((T₁ ×ˢ T₂).image fun p => p.1 * p.2 : Finset A)) : Set A)
      = (T₁ : Set A) * (T₂ : Set A) := by
    rw [Finset.coe_image, Finset.coe_product]
    exact Set.image_mul_prod
  rw [hcoe, ← Ideal.span_mul_span', h₁, h₂, Ideal.top_mul]

/-- Spans of `insert`-enlarged spanning sets span. The `DecidableEq` binder makes the
use site instantiate `insert` with the ambient instance (see `span_mul_image_eq_top`). -/
theorem span_insert_eq_top {A : Type*} [CommRing A] [DecidableEq A] {T : Finset A} (a : A)
    (h : Ideal.span (T : Set A) = ⊤) :
    Ideal.span ((insert a T : Finset A) : Set A) = ⊤ := by
  rw [← top_le_iff, ← h]
  exact Ideal.span_mono (by rw [Finset.coe_insert]; exact Set.subset_insert a _)

/-- The product-datum span fact, stated at 𝓐 (`s`-normalized factors). -/
theorem interDatum_span_eq_top (D₁ D₂ : RationalLocData (JetA F))
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) :
    Ideal.span ((((insert D₁.s D₁.T ×ˢ insert D₂.s D₂.T).image
      fun p => p.1 * p.2 : Finset (JetA F))) : Set (JetA F)) = ⊤ :=
  span_mul_image_eq_top (span_insert_eq_top D₁.s h₁.span_eq_top)
    (span_insert_eq_top D₂.s h₂.span_eq_top)

/-- The product (intersection) datum of two rational data ([FJP] Lemma 5.2 uses
`U_{ij} = U_i ∩ U_j`, "which is again rational"). Signature completion (recorded):
rationality of both data discharges `hopen`. Definition normalization (recorded, the
L5.8 fallback): the factors are `s`-normalized (`insert sᵢ Tᵢ`) so that the pointwise
intersection formula `rationalOpen_interDatum` holds — `R(T/s) = R((T ∪ {s})/s)` on
opens, but only the normalized product datum cuts out the intersection. -/
def interDatum (D₁ D₂ : RationalLocData (JetA F))
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) : RationalLocData (JetA F) where
  P := podA F
  T := (insert D₁.s D₁.T ×ˢ insert D₂.s D₂.T).image fun p => p.1 * p.2
  s := D₁.s * D₂.s
  hopen := genPiece_hopen (podA F)
    ((insert D₁.s D₁.T ×ˢ insert D₂.s D₂.T).image fun p => p.1 * p.2)
    (D₁.s * D₂.s) (interDatum_span_eq_top D₁ D₂ h₁ h₂)

theorem rationalOpen_interDatum (D₁ D₂ : RationalLocData (JetA F))
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) :
    rationalOpen (interDatum D₁ D₂ h₁ h₂).T (interDatum D₁ D₂ h₁ h₂).s =
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
    · have hpair : t * D₂.s ∈ (interDatum D₁ D₂ h₁ h₂).T :=
        Finset.mem_image.mpr ⟨(t, D₂.s), Finset.mem_product.mpr
          ⟨Finset.mem_insert_of_mem ht, Finset.mem_insert_self _ _⟩, rfl⟩
      exact v.vle_mul_cancel hs₂0 (hvle _ hpair)
    · have hpair : D₁.s * t ∈ (interDatum D₁ D₂ h₁ h₂).T :=
        Finset.mem_image.mpr ⟨(D₁.s, t), Finset.mem_product.mpr
          ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ht⟩, rfl⟩
      have h' := hvle _ hpair
      rw [show D₁.s * t = t * D₁.s from mul_comm _ _,
        show (interDatum D₁ D₂ h₁ h₂).s = D₂.s * D₁.s from mul_comm _ _] at h'
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
    · rw [show (interDatum D₁ D₂ h₁ h₂).s = D₁.s * D₂.s from rfl,
        show (0 : JetA F) = 0 * D₂.s from (zero_mul _).symm] at h0
      exact hs₁0 (v.vle_mul_cancel hs₂0 h0)

theorem interDatum_isRational {D₁ D₂ : RationalLocData (JetA F)}
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) : (interDatum D₁ D₂ h₁ h₂).IsRational :=
  RationalLocData.isRational_of_span_eq_top (interDatum_span_eq_top D₁ D₂ h₁ h₂)

end

end FiniteJet
