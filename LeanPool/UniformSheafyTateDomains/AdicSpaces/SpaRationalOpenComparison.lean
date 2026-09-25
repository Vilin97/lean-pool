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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafIdentification
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornSpaRationalOpenLiftWrapper
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletedResidueField
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.RingTheory.Valuation.Integral

/-!
# Wedhorn Proposition 8.2: `Spa` of the completed rational localization

The canonical comparison between `Spa (presheafValue D) ((presheafValue D)⁺)` and
the rational subset `R(D.T/D.s) ∩ Spa (A, A⁺)`, by pull-back of valuations along
`D.canonicalMap : A →+* presheafValue D` (Wedhorn Proposition 8.2, p. 74;
factored as localization extension + completion extension per Wedhorn's proof).

All results in this module are **axiom-clean** (`{propext, Classical.choice,
Quot.sound}`); this module deliberately does *not* import `StructureSheaf.lean`.
(History: extracted 2026-07-20 from `SpaPresheafValueEquivalence.lean`, whose
remaining content was circular scaffolding around the then-sorry-bodied headline;
the unused noetherian/strongly-noetherian binders were dropped in the move.)

* `valuation_extends_to_localization_of_rationalOpen` — Wedhorn 8.2's
  localization half: `v ∈ R(T/s)` extends to a Spa-point of
  `Localization.Away D.s` (with the localization topology).
* `spa_completion_of_spa_localization` — the completion half: a Spa-point of the
  localization bounded on `locPlusSubring` extends to a Spa-point of
  `presheafValue D`.
* `exists_spa_presheafValue_of_rationalOpen` — the composed ⊇ direction.
* `comap_algebraMap_injective`, `comap_coeRingHom_injOn_spa`,
  `comap_canonicalMap_injOn_spa`, `…_inj_of_isContinuous` — uniqueness of the
  extension (Wedhorn 8.2:3736 and 7.48-injectivity via density).
* `comap_canonicalMap_mem_rationalOpen_inter_spa` — the ⊆ direction.
* `spaPresheafValueEquivRationalOpen` — **the canonical `Equiv`** (forward map
  literally `comap D.canonicalMap`, see the `@[simp]` lemma), with
  `comap_canonicalMap_image_spa` (exact image equality) and
  `spaPresheafValueEquivRationalOpen_continuous` (forward continuity).
* `Spa_presheafValue_eq_rationalOpen` — the (formerly sorry-bodied, now
  discharged) headline, moved here from `StructureSheaf.lean`.

The transported plus ring is the canonical completed one:
`(presheafValue D)⁺ = D.completedPlusSubring` (`RationalLocData.presheafValuePlusSubring`),
and its **correctness** — being a genuine ring of integral elements — is the
existing instance `RationalLocData.presheafValuePlus_isRingOfIntegralElements`
(Presheaf.lean; Wedhorn 8.16 via 7.19 + 7.47).

The full **homeomorphism** statement additionally needs that the forward map is
open onto its image, which is Wedhorn's "maps rational subsets to rational
subsets" (8.2(2) second half) — that requires the parameter-perturbation
machinery (Wedhorn 7.48 / Kedlaya Ex. 1.2.2) and lands separately.
-/

@[expose] public section

noncomputable section

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **(C3.1, NEW-A2.1)**: a Spa-point `v` of `A` lying in
`rationalOpen D.T D.s` extends to a Spa-point `w` of `Localization.Away D.s`
(with the localization topology `D.topology`, bounded by the canonical
plus-subring `localizationAwayPlusSubring D.s`) such that
`comap (algebraMap A _) w = v`.

Existence half of "extends uniquely"; uniqueness is a separate (smaller)
lemma orthogonal to the IsSheafy chain.

**Proof**: pure invocation of `valuationLocalizationLift_of_spa_rationalOpen`
(WedhornSpaRationalOpenLiftWrapper.lean:68). The hypotheses match up
1-1 once we unpack `D.hopen`. -/
theorem valuation_extends_to_localization_of_rationalOpen
    (D : RationalLocData A)
    {v : Spv A} (hv_rat : v ∈ rationalOpen D.T D.s) :
    ∃ w : Spv (Localization.Away D.s),
      w ∈ @Spa (Localization.Away D.s) _ D.topology
        (localizationAwayPlusSubring D.s).toSubring ∧
      comap (algebraMap A (Localization.Away D.s)) w = v := by
  obtain ⟨hv, hv_T, hvs⟩ := hv_rat
  -- Wedhorn 8.2:3738 — the lift's continuity needs ONLY `v(tᵢ) ≤ v(s)` (not `v ≤ 1` on A₀);
  -- the A₀-coefficients of any `locSubring`-multiple are absorbed into the ideal of definition
  -- (Wedhorn §8.1 absorption, `extendToLocalization_mul_pow_lt`). So no `hA₀_le`/`hν_A₀`,
  -- and crucially no dependency on the false ∀-Cont-A power-bounded characterization
  -- (the `wedhorn_7_42_forward` chain, since DELETED as false 2026-05-31).
  exact valuationLocalizationLift_of_bounded D.P D.T D.s D.hopen hv hv_T hvs

/-- The residue-field valuation `K(w) → Γ` of any `Spv`-point is **surjective** onto its
value group: every value group element is `valuation a / valuation b`, realised in the
fraction field `K(w)` as `algebraMap(mk a) / algebraMap(mk b)`. (Extracted as a standalone
lemma so its defeq-heavy proof has its own heartbeat budget.) -/
theorem residueFieldValuation_surjective {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (w : Spv R) :
    Function.Surjective (ValuationSpectrum.residueFieldValuation R w) := by
  intro γ
  letI : ValuativeRel R := w.toValuativeRel
  obtain ⟨a, b, hab⟩ := ValuativeRel.exists_valuation_div_valuation_eq (R := R) γ
  refine ⟨algebraMap (R ⧸ w.supp) (FractionRing (R ⧸ w.supp)) (Ideal.Quotient.mk w.supp a) /
          algebraMap (R ⧸ w.supp) (FractionRing (R ⧸ w.supp))
            (Ideal.Quotient.mk w.supp (b : R)), ?_⟩
  rw [ValuationSpectrum.residueFieldValuation, Valuation.map_div,
      Valuation.extendToLocalization_apply_map_apply, Valuation.extendToLocalization_apply_map_apply]
  exact hab

/-- Pulling back the `ofValuation` point of a valued ring along a ring hom: if `V (φ f) ≤ 1`,
then `(comap φ (ofValuation V)).vle f 1`. (Extracted as a general lemma — `B` a variable — so the
`ValuativeRel`/`Compatible` defeq is paid in its own heartbeat budget, not inline at `val.Completion`.) -/
theorem vle_one_comap_ofValuation {B C : Type*} [CommRing B] [CommRing C]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (V : Valuation B Γ) (φ : C →+* B)
    {f : C} (h : V (φ f) ≤ 1) : (comap φ (ofValuation V)).vle f 1 := by
  rw [comap_vle, map_one]
  letI : ValuativeRel B := ValuativeRel.ofValuation V
  haveI : V.Compatible := Valuation.Compatible.ofValuation V
  exact (Valuation.vle_iff_le V).mpr (by simpa using h)

/-- `Spv`-boundedness via the canonical valuation: `w.vle d 1 ⟹ canonicalValuation w d ≤ 1`.
(Extracted — `R` a variable — own heartbeat budget.) -/
theorem canonicalValuation_le_one_of_vle {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (w : Spv R) {d : R} (h : w.vle d 1) :
    ValuationSpectrum.canonicalValuation R w d ≤ 1 := by
  letI : ValuativeRel R := w.toValuativeRel
  exact (Valuation.vle_iff_le (ValuativeRel.valuation R)).mp h

/-- The iff form of `canonicalValuation_le_one_of_vle`. -/
theorem vle_one_iff_canonicalValuation_le {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (w : Spv R) {d : R} :
    w.vle d 1 ↔ ValuationSpectrum.canonicalValuation R w d ≤ 1 := by
  letI : ValuativeRel R := w.toValuativeRel
  exact Valuation.vle_iff_le (ValuativeRel.valuation R) (x := d) (y := 1)

/-- **`hw_loc` threading (Wedhorn 8.2, wedhorn.txt:3739-3740).** If `v ∈ rationalOpen D.T D.s`
(`v(t) ≤ v(s)`, `v(s) ≠ 0`) and `w` extends `v` to `Localization.Away D.s` (`comap algebraMap w = v`),
then `w ≤ 1` on `locSubring = A₀[t/s]`: on the generators `algebraMap '' A₀` (via `v ≤ 1` on `A⁺ ⊇ A₀`)
and `divByS t s` (via `v(t) ≤ v(s)` and `divByS t s · s = t`), then on the generated subring
(the valuation integers form a subring). -/
theorem extension_vle_one_on_locPlusSubring (D : RationalLocData A)
    {v : Spv A} (hv_rat : v ∈ rationalOpen D.T D.s)
    {w : Spv (Localization.Away D.s)}
    (hw_comap : comap (algebraMap A (Localization.Away D.s)) w = v) :
    ∀ d ∈ (D.locPlusSubring : Set (Localization.Away D.s)), w.vle d 1 := by
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  obtain ⟨hv_spa, hv_T, hv_s⟩ := hv_rat
  -- A⁺-based generators (Wedhorn 8.2): `A⁺[t/s]`. The `A⁺`-bound comes directly
  -- from `v ∈ Spa A` (no `A₀ ⊆ A⁺` detour), and `t/s ≤ 1` from `v(t) ≤ v(s)`.
  have hgen : (algebraMap A (Localization.Away D.s)) '' (A⁺ : Set A) ∪
      Set.range (fun t : D.T ↦ divByS (t : A) D.s) ⊆ {d | w.vle d 1} := by
    rintro x (⟨a, ha, rfl⟩ | ⟨t, rfl⟩)
    · show w.vle (algebraMap A (Localization.Away D.s) a) 1
      have hva : v.vle a 1 := vle_one_of_mem_spa hv_spa ha
      rw [← hw_comap, comap_vle, map_one] at hva
      exact hva
    · show w.vle (divByS (t : A) D.s) 1
      have hts : w.vle (algebraMap A (Localization.Away D.s) (t : A))
          (algebraMap A (Localization.Away D.s) D.s) := by
        have h := hv_T (t : A) t.2; rw [← hw_comap, comap_vle] at h; exact h
      have hsne : ¬ w.vle (algebraMap A (Localization.Away D.s) D.s) 0 := by
        intro hc; apply hv_s; rw [← hw_comap, comap_vle, map_zero]; exact hc
      refine w.vle_mul_cancel hsne ?_
      rw [one_mul, show divByS (t : A) D.s * algebraMap A (Localization.Away D.s) D.s
          = algebraMap A (Localization.Away D.s) (t : A) from by
        rw [divByS]; exact IsLocalization.mk'_spec _ _ _]
      exact hts
  have hsub : D.locPlusSubring ≤
      (ValuationSpectrum.canonicalValuation (Localization.Away D.s) w).integer := by
    rw [RationalLocData.locPlusSubring, Subring.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Valuation.mem_integer_iff]
    exact (vle_one_iff_canonicalValuation_le w).mp (hgen hx)
  intro d hd
  exact (vle_one_iff_canonicalValuation_le w).mpr ((Valuation.mem_integer_iff _ _).mp (hsub hd))

/-- The residue ring hom `Localization.Away D.s → WithVal (residueFieldValuation w)` underlying the
completion extension (algebraic; the heavy proofs about it are extracted into own-budget lemmas). -/
noncomputable def scResHom (D : RationalLocData A) (w : Spv (Localization.Away D.s)) :
    Localization.Away D.s →+*
      WithVal (ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w) :=
  ((WithVal.equiv (ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w)).symm.toRingHom).comp
    ((algebraMap ((Localization.Away D.s) ⧸ w.supp)
        (FractionRing ((Localization.Away D.s) ⧸ w.supp))).comp
      (Ideal.Quotient.mk w.supp))

/-- The residue valuation of `scResHom D w a` equals `w`'s canonical valuation at `a`. -/
theorem scResHom_val (D : RationalLocData A) (w : Spv (Localization.Away D.s))
    (a : Localization.Away D.s) :
    Valued.v (scResHom D w a) =
      ValuationSpectrum.canonicalValuation (Localization.Away D.s) w a := by
  rw [← WithVal.val_apply_equiv]
  have heq : WithVal.equiv (ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w)
        (scResHom D w a)
      = algebraMap ((Localization.Away D.s) ⧸ w.supp)
          (FractionRing ((Localization.Away D.s) ⧸ w.supp)) (Ideal.Quotient.mk w.supp a) := by
    rw [scResHom]; simp
  rw [heq, ValuationSpectrum.residueFieldValuation, Valuation.extendToLocalization_apply_map_apply]
  rfl

/-- `scResHom D w` is continuous (w.r.t. `D.topology`): preimages of valuation-nbhds are the
`w`-continuity nbhds, via the value-group embedding bridge and `scResHom_val`. (Own-budget extraction
of the `hφ` core.) -/
theorem scResHom_continuous (D : RationalLocData A) (w : Spv (Localization.Away D.s))
    (hw_cont : @ValuationSpectrum.IsContinuous _ _ D.topology w) :
    @Continuous (Localization.Away D.s)
      (WithVal (ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w))
      D.topology _ (scResHom D w) := by
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  apply continuous_of_continuousAt_zero (scResHom D w).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  rw [(Valued.hasBasis_nhds_zero
    (WithVal (ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w)) _).tendsto_right_iff]
  rintro γ -
  have hδ_ne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠
      (0 : ValuationSpectrum.valueGroup (Localization.Away D.s) w) := fun h =>
    Units.ne_zero γ (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective
      (h.trans (map_zero _).symm))
  have hopen : IsOpen {a : Localization.Away D.s |
      ValuationSpectrum.canonicalValuation (Localization.Away D.s) w a
        < MonoidWithZeroHom.ValueGroup₀.embedding γ.1} := by
    simpa using (Valuation.isContinuous_iff_units
      (ValuationSpectrum.canonicalValuation (Localization.Away D.s) w)).mp hw_cont
      (Units.mk0 _ hδ_ne)
  have key : ∀ x : Localization.Away D.s,
      ((Valued.v).restrict ((scResHom D w).toAddMonoidHom x) < γ.1) ↔
      (ValuationSpectrum.canonicalValuation (Localization.Away D.s) w x
        < MonoidWithZeroHom.ValueGroup₀.embedding γ.1) := by
    intro x
    rw [Valuation.restrict_lt_iff_lt_embedding]
    show Valued.v (scResHom D w x) < _ ↔ _
    rw [scResHom_val D w x]
  simp only [Set.mem_setOf_eq, key]
  exact Filter.eventually_iff.mpr (hopen.mem_nhds (by
    simp only [Set.mem_setOf_eq, map_zero]; exact zero_lt_iff.mpr hδ_ne))

/-- The completion-extension's pullback recovers the original point (general — `R`/`L` variables,
own heartbeat budget). `L` is valued in `w`'s value group. -/
theorem comap_coeRingHom_extensionHom_ofValuation_eq {R : Type*} [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] (w : Spv R)
    {L : Type*} [Field L] [Valued L (ValuationSpectrum.valueGroup R w)] [CompleteSpace L] [T0Space L]
    (φ : R →+* L) (hφ : Continuous φ)
    (hval : ∀ a, Valued.v (φ a) = ValuationSpectrum.canonicalValuation R w a) :
    comap (UniformSpace.Completion.coeRingHom)
      (comap (UniformSpace.Completion.extensionHom φ hφ) (ofValuation Valued.v)) = w := by
  have hcomp : (UniformSpace.Completion.extensionHom φ hφ).comp
      UniformSpace.Completion.coeRingHom = φ := by
    ext a; exact UniformSpace.Completion.extensionHom_coe φ hφ a
  have key : comap (UniformSpace.Completion.coeRingHom)
      (comap (UniformSpace.Completion.extensionHom φ hφ) (ofValuation Valued.v))
      = comap ((UniformSpace.Completion.extensionHom φ hφ).comp
          UniformSpace.Completion.coeRingHom) (ofValuation Valued.v) := by
    rw [comap_comp]; rfl
  rw [key, hcomp, comap_ofValuation,
    show (Valued.v : Valuation L (ValuationSpectrum.valueGroup R w)).comap φ
        = ValuationSpectrum.canonicalValuation R w from
      Valuation.ext (fun a => (Valuation.comap_apply _ _ _).trans (hval a))]
  exact ofValuation_valuation w

/-- INFRASTRUCTURE (not in Wedhorn): the valuation integer is integrally closed, so if a
ring hom `φ : R →+* K` carries a subring `S` into `{x | v (φ x) ≤ 1}`, then every element of
`R` integral over `S` also satisfies `v (φ c) ≤ 1`. This is the integral-closure half of
`completedPlusSubring = Ĉ` being a ring of integral elements (Wedhorn 7.14(1)/7.19): `Ĉ` is the
closure of the image of the *integral closure* `(A⁺[T/s])^int`, so the Spa bound must extend
from the generators `locPlusSubring` to their integral closure. -/
private theorem vle_image_le_one_of_isIntegral_of_subring
    {R K Γ : Type*} [CommRing R] [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (φ : R →+* K) (S : Subring R)
    (hS : ∀ x ∈ S, v (φ x) ≤ 1) {c : R} (hc : IsIntegral S c) :
    v (φ c) ≤ 1 := by
  have hφc_int : IsIntegral (↥v.integer) (φ c) := by
    refine IsIntegral.map_of_comp_eq
      ((φ.comp S.subtype).codRestrict v.integer ?_) φ ?_ hc
    · intro x
      rw [Valuation.mem_integer_iff]
      exact hS x.1 x.2
    · ext x; rfl
  exact (Valuation.mem_integer_iff _ _).mp
    ((Valuation.integer.integers v).mem_of_integral hφc_int)

/-- **Completion step (Wedhorn Lemma 8.2, completion half).** A Spa-point `w`
of the rational localization `Localization.Away D.s` extends to a Spa-point `w'`
of its completion `presheafValue D`, pulling back along `D.coeRingHom`.

Discharge: a continuous valuation on `Localization.Away D.s` extends to its
completion `presheafValue D` (universal property of `UniformSpace.Completion`),
with `SpvCompletionExtension.ne_zero_of_unit_completion` ensuring the extended
valuation is non-degenerate on units; the Spa (`v ≤ 1` on the plus-subring)
condition transfers along the dense inclusion. -/
theorem spa_completion_of_spa_localization
    (D : RationalLocData A)
    {w : Spv (Localization.Away D.s)}
    (hw : w ∈ @Spa (Localization.Away D.s) _ D.topology
      (localizationAwayPlusSubring D.s).toSubring)
    (hw_loc : ∀ d ∈ (D.locPlusSubring : Set (Localization.Away D.s)), w.vle d 1) :
    ∃ w' : Spv (presheafValue D),
      w' ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
      comap D.coeRingHom w' = w := by
  classical
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  set val := ValuationSpectrum.residueFieldValuation (Localization.Away D.s) w with hval_def
  set φ : (Localization.Away D.s) →+* val.Completion :=
    (UniformSpace.Completion.coeRingHom).comp (scResHom D w) with hφ_def
  have hφ : Continuous φ :=
    (UniformSpace.Completion.continuous_coeRingHom).comp (scResHom_continuous D w hw.1)
  set φhat : presheafValue D →+* val.Completion :=
    UniformSpace.Completion.extensionHom φ hφ with hφhat_def
  set w' : Spv (presheafValue D) := comap φhat (ofValuation Valued.v) with hw'_def
  letI : TopologicalSpace (ValuationSpectrum.valueGroup (Localization.Away D.s) w) :=
    WithZeroTopology.topologicalSpace
  haveI : OrderClosedTopology (ValuationSpectrum.valueGroup (Localization.Away D.s) w) :=
    WithZeroTopology.orderClosedTopology
  have hVcont : Continuous
      (Valued.v : val.Completion → ValuationSpectrum.valueGroup (Localization.Away D.s) w) :=
    Valued.continuous_valuation_of_surjective (by
      rw [Valued.valuedCompletion_surjective_iff]
      exact (residueFieldValuation_surjective w).comp (WithVal.equiv val).surjective)
  refine ⟨w', ?_, ?_⟩
  · rw [mem_spa_iff]
    refine ⟨?_, ?_⟩
    · exact ValuationSpectrum.comap_isContinuous
        UniformSpace.Completion.continuous_extension
        (isContinuous_ofValuation_of _ (fun γ =>
          hVcont.isOpen_preimage _ WithZeroTopology.isOpen_Iio))
    · intro f hf
      -- `f ∈ (presheafValue D)⁺ = integralClosure(completedPlusSubringBase)` (refactor): `f` is
      -- integral over `completedPlusSubringBase`, which maps into the valuation integer (the
      -- closure-minimality argument, unchanged); `vle_image_le_one_of_isIntegral_of_subring` lifts
      -- the `≤ 1` bound from the base to `f`.
      have hf_int : IsIntegral ↥(D.completedPlusSubringBase) f :=
        (mem_integralClosure_iff _ _).mp (Subalgebra.mem_toSubring.mp hf)
      have hbase_le : D.completedPlusSubringBase ≤ ((Valued.v).integer).comap φhat := by
        rw [RationalLocData.completedPlusSubringBase]
        refine Subring.topologicalClosure_minimal
          ((integralClosure ↥(D.locPlusSubring) (Localization.Away D.s)).toSubring.map
            D.coeRingHom) ?_
          ((isClosed_le hVcont continuous_const).preimage
            UniformSpace.Completion.continuous_extension)
        rintro _ ⟨c, hc, rfl⟩
        show φhat (D.coeRingHom c) ∈ (Valued.v).integer
        rw [Valuation.mem_integer_iff]
        have hφc : φhat (D.coeRingHom c) = φ c := by
          rw [hφhat_def]; exact UniformSpace.Completion.extensionHom_coe φ hφ c
        erw [hφc]
        -- `c` is integral over `locPlusSubring`; the valuation integer is integrally closed and `φ`
        -- carries `locPlusSubring` into it (the Spa bound `hw_loc`), so `Valued.v (φ c) ≤ 1`.
        refine vle_image_le_one_of_isIntegral_of_subring Valued.v φ D.locPlusSubring ?_
          ((mem_integralClosure_iff _ _).mp (Subalgebra.mem_toSubring.mp hc))
        intro d hd
        show Valued.v ((scResHom D w d : WithVal val) : val.Completion) ≤ 1
        rw [Valued.valuedCompletion_apply, scResHom_val D w d]
        exact canonicalValuation_le_one_of_vle w (hw_loc d hd)
      have hf_le : Valued.v (φhat f) ≤ 1 :=
        vle_image_le_one_of_isIntegral_of_subring Valued.v φhat D.completedPlusSubringBase
          (fun d hd => (Valuation.mem_integer_iff _ _).mp (Subring.mem_comap.mp (hbase_le hd)))
          hf_int
      rw [hw'_def]
      exact vle_one_comap_ofValuation Valued.v φhat hf_le
  · have hval_φ : ∀ a, Valued.v (φ a) =
        ValuationSpectrum.canonicalValuation (Localization.Away D.s) w a := by
      intro a
      show Valued.v ((scResHom D w a : WithVal val) : val.Completion) = _
      rw [Valued.valuedCompletion_apply]; exact scResHom_val D w a
    exact comap_coeRingHom_extensionHom_ofValuation_eq w φ hφ hval_φ
/-- **Genuine ⊇ direction**: every Spa-point `v` of `A` in `rationalOpen D.T D.s`
is the `D.canonicalMap`-pullback of a Spa-point of `presheafValue D`. Composes the
sorry-free `valuation_extends_to_localization_of_rationalOpen` (to `Localization.Away`)
with `spa_completion_of_spa_localization` (to the completion). -/
theorem exists_spa_presheafValue_of_rationalOpen
    (D : RationalLocData A)
    {v : Spv A} (hv_rat : v ∈ rationalOpen D.T D.s) :
    ∃ w' : Spv (presheafValue D),
      w' ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
      comap D.canonicalMap w' = v := by
  obtain ⟨w, hw_spa, hw_comap⟩ :=
    valuation_extends_to_localization_of_rationalOpen D hv_rat
  have hw_loc : ∀ d ∈ (D.locPlusSubring : Set (Localization.Away D.s)), w.vle d 1 :=
    extension_vle_one_on_locPlusSubring D hv_rat hw_comap
  obtain ⟨w', hw'_spa, hw'_comap⟩ := spa_completion_of_spa_localization D hw_spa hw_loc
  refine ⟨w', hw'_spa, ?_⟩
  have hcomp : D.canonicalMap =
      (D.coeRingHom).comp (algebraMap A (Localization.Away D.s)) := rfl
  rw [hcomp, comap_comp, Function.comp_apply, hw'_comap, hw_comap]

/-! ## Injectivity of the Spa-pullback (Wedhorn 8.2: the extension is unique)

Wedhorn 8.2:3721 factors `j = Spa(ρ)` as `Spa(ρ') ∘ Spa(ι)`:
- `Spa(ρ') = comap (algebraMap A Aₛ)` is injective — "a valuation `v` on `A` extends
  *necessarily uniquely* to `Aₛ`" (wedhorn.txt:3736), since `D.s` is a unit in `Aₛ`;
- `Spa(ι) = comap D.coeRingHom` is injective on continuous valuations — a continuous
  valuation on the completion `Â⟨T/s⟩` is determined by its restriction to the dense
  image of `Aₛ` (wedhorn.txt:3729–3730: "Spa(ι) is a homeomorphism … by Proposition
  7.48"; Wedhorn defers 7.48 to [Hu2] Prop 3.9). -/

/-- **(Wedhorn 8.2:3736 — localization extension is unique)** A valuation on the rational
localisation `Localization.Away D.s` is determined by its restriction to `A` (every element
is `a/sⁿ`, and `v(a/sⁿ)` is fixed by `v(a)`, `v(s) ≠ 0`): `comap (algebraMap A Aₛ)` is
injective. -/
theorem comap_algebraMap_injective (D : RationalLocData A) :
    Function.Injective (comap (algebraMap A (Localization.Away D.s))) := by
  intro w₁ w₂ h
  refine ValuationSpectrum.ext (funext₂ fun x y => propext ?_)
  -- Write `x = a/sᵃ`, `y = b/sᵇ`; the common denominator `sᵃ·sᵇ ∈ powers s` maps to a unit.
  obtain ⟨⟨a, sa, hsa⟩, rfl⟩ := IsLocalization.mk'_surjective (M := Submonoid.powers D.s) x
  obtain ⟨⟨b, sb, hsb⟩, rfl⟩ := IsLocalization.mk'_surjective (M := Submonoid.powers D.s) y
  dsimp only
  have hsab : sa * sb ∈ Submonoid.powers D.s := Submonoid.mul_mem _ hsa hsb
  have hunit : IsUnit (algebraMap A (Localization.Away D.s) (sa * sb)) :=
    IsLocalization.map_units (Localization.Away D.s) ⟨sa * sb, hsab⟩
  -- `vle` is invariant under multiplication by the unit `algebraMap (sa·sb)`.
  have vle_unit_iff : ∀ (w : Spv (Localization.Away D.s)) (p q : Localization.Away D.s),
      w.vle (p * algebraMap A (Localization.Away D.s) (sa * sb))
            (q * algebraMap A (Localization.Away D.s) (sa * sb)) ↔ w.vle p q :=
    fun w p q => ⟨w.vle_mul_cancel (not_vle_zero_of_isUnit hunit w),
      fun hpq => w.mul_vle_mul_left hpq (algebraMap A (Localization.Away D.s) (sa * sb))⟩
  -- Clearing denominators: `(a/sᵃ)·(sᵃ·sᵇ) = a·sᵇ` and `(b/sᵇ)·(sᵃ·sᵇ) = b·sᵃ` (images of `A`).
  have hxa : IsLocalization.mk' (Localization.Away D.s) a ⟨sa, hsa⟩
        * algebraMap A (Localization.Away D.s) (sa * sb)
      = algebraMap A (Localization.Away D.s) (a * sb) := by
    rw [map_mul, ← mul_assoc, IsLocalization.mk'_spec, ← map_mul]
  have hyb : IsLocalization.mk' (Localization.Away D.s) b ⟨sb, hsb⟩
        * algebraMap A (Localization.Away D.s) (sa * sb)
      = algebraMap A (Localization.Away D.s) (b * sa) := by
    rw [mul_comm sa sb, map_mul, ← mul_assoc, IsLocalization.mk'_spec, ← map_mul]
  -- So `w.vle (a/sᵃ) (b/sᵇ)` is determined by `comap (algebraMap A Aₛ) w` (Wedhorn 8.2:3736).
  have key : ∀ w : Spv (Localization.Away D.s),
      w.vle (IsLocalization.mk' (Localization.Away D.s) a ⟨sa, hsa⟩)
            (IsLocalization.mk' (Localization.Away D.s) b ⟨sb, hsb⟩)
      ↔ (comap (algebraMap A (Localization.Away D.s)) w).vle (a * sb) (b * sa) := by
    intro w
    rw [comap_vle, ← hxa, ← hyb, vle_unit_iff]
  rw [key w₁, key w₂, h]

/-- **(Wedhorn 8.2:3729 / Prop 7.48 — completion extension is unique)** A *continuous*
valuation on the completion `presheafValue D = Â⟨T/s⟩` is determined by its restriction to
the dense image of `Localization.Away D.s`: `comap D.coeRingHom` is injective on Spa-points.

This is the injectivity half of `Spa(ι)` being a homeomorphism (Wedhorn 8.2:3729–3730);
Wedhorn defers Prop 7.48 to [Hu2] Prop 3.9. Content: density of `Aₛ ↪ Â⟨T/s⟩`
(`UniformSpace.Completion.denseRange_coe`) + continuity pins the `vle` relation on all of
`Â⟨T/s⟩`. -/
theorem comap_coeRingHom_injOn_spa (D : RationalLocData A)
    {w₁ w₂ : Spv (presheafValue D)}
    (hw₁ : w₁ ∈ Spa (presheafValue D) (presheafValue D)⁺)
    (hw₂ : w₂ ∈ Spa (presheafValue D) (presheafValue D)⁺)
    (h : comap D.coeRingHom w₁ = comap D.coeRingHom w₂) :
    w₁ = w₂ := by
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    intro y
    exact @UniformSpace.Completion.denseRange_coe (Localization.Away D.s) D.uniformSpace y
  exact ValuationSpectrum.eq_of_isContinuous_of_comap_eq_of_denseRange hdense
    ((mem_spa_iff w₁).mp hw₁).1 ((mem_spa_iff w₂).mp hw₂).1 h

/-- **(Wedhorn 8.2:3740 — `j = Spa(ρ)` is injective)** The Spa-pullback along the canonical
map `A → presheafValue D` is injective on Spa-points of the completion. Composes the
localization-uniqueness and completion-uniqueness halves via `canonicalMap = coeRingHom ∘
algebraMap`. -/
theorem comap_canonicalMap_injOn_spa (D : RationalLocData A)
    {w₁ w₂ : Spv (presheafValue D)}
    (hw₁ : w₁ ∈ Spa (presheafValue D) (presheafValue D)⁺)
    (hw₂ : w₂ ∈ Spa (presheafValue D) (presheafValue D)⁺)
    (h : comap D.canonicalMap w₁ = comap D.canonicalMap w₂) :
    w₁ = w₂ := by
  have hcomp : D.canonicalMap
      = D.coeRingHom.comp (algebraMap A (Localization.Away D.s)) := rfl
  rw [hcomp, comap_comp] at h
  simp only [Function.comp_apply] at h
  exact comap_coeRingHom_injOn_spa D hw₁ hw₂ (comap_algebraMap_injective D h)

/-- **Continuity-only form of `comap_coeRingHom_injOn_spa`.** The completion Spa-injectivity
needs only *continuity* of the two valuations (not the full plus-bounded Spa-membership): this
is exactly the hypothesis of the T-SUM-7 keystone. Useful for lifting points along restrictions
where the restricted point is not (yet) known to be plus-bounded. -/
theorem comap_coeRingHom_inj_of_isContinuous (D : RationalLocData A)
    {w₁ w₂ : Spv (presheafValue D)} (h₁ : w₁.IsContinuous) (h₂ : w₂.IsContinuous)
    (h : comap D.coeRingHom w₁ = comap D.coeRingHom w₂) : w₁ = w₂ := by
  have hdense : DenseRange (D.coeRingHom : Localization.Away D.s → presheafValue D) := by
    intro y
    exact @UniformSpace.Completion.denseRange_coe (Localization.Away D.s) D.uniformSpace y
  exact ValuationSpectrum.eq_of_isContinuous_of_comap_eq_of_denseRange hdense h₁ h₂ h

/-- **Continuity-only form of `comap_canonicalMap_injOn_spa`** (`comap D.canonicalMap` is
injective on *continuous* points of `Spv (presheafValue D)`). -/
theorem comap_canonicalMap_inj_of_isContinuous (D : RationalLocData A)
    {w₁ w₂ : Spv (presheafValue D)} (h₁ : w₁.IsContinuous) (h₂ : w₂.IsContinuous)
    (h : comap D.canonicalMap w₁ = comap D.canonicalMap w₂) : w₁ = w₂ := by
  have hcomp : D.canonicalMap
      = D.coeRingHom.comp (algebraMap A (Localization.Away D.s)) := rfl
  rw [hcomp, comap_comp] at h
  simp only [Function.comp_apply] at h
  exact comap_coeRingHom_inj_of_isContinuous D h₁ h₂ (comap_algebraMap_injective D h)

/-- The pulled-back valuation along
`D.canonicalMap` of a Spa-point of `presheafValue D` lies in `Spa A A⁺`.

Closed via the standard pattern (see `Presheaf.exists_rationalOpen_of_completion_spa`):
* `PresheafIdentification.canonicalMap_continuous D` provides continuity;
* `D.canonicalMap_integral (CompatiblePlusSubring.aplus_le_A₀ D)` provides
  the integrality condition `A⁺ ≤ (presheafValue D)⁺.comap D.canonicalMap`,
  derived from the `[CompatiblePlusSubring A]` typeclass (Wedhorn Remark 7.17);
* `AdicSpectrum.comap_mem_spa` assembles them.

The `[CompatiblePlusSubring A]` hypothesis is the standard Wedhorn assumption
`A⁺ ⊆ A₀` for affinoid pairs; it is *not* work-deferral because the result is
literally false without it (the comap can fail to bound `A⁺` by `1`). -/
theorem comap_canonicalMap_mem_spa
    (D : RationalLocData A) (w : Spa (presheafValue D) (presheafValue D)⁺) :
    ValuationSpectrum.comap D.canonicalMap w.val ∈ Spa A A⁺ :=
  comap_mem_spa (canonicalMap_continuous D) D.canonicalMap_integral w.property

/-! ## The canonical comparison (Wedhorn 8.2) -/

/-- **The ⊆ direction of Wedhorn 8.2**: the pull-back along `D.canonicalMap` of a
Spa-point of `presheafValue D` lies in `R(T/s) ∩ Spa (A, A⁺)`. -/
theorem comap_canonicalMap_mem_rationalOpen_inter_spa
    (D : RationalLocData A) (w : Spa (presheafValue D) (presheafValue D)⁺) :
    comap D.canonicalMap w.val ∈
      (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)) :=
  ⟨⟨comap_canonicalMap_mem_spa D w,
      fun t ht => D.comap_canonicalMap_vle w.property.2 ht,
      D.comap_canonicalMap_not_vle_s_zero⟩,
    comap_canonicalMap_mem_spa D w⟩

/-- **The canonical equivalence of Wedhorn Proposition 8.2**: `Spa` of the
completed rational localization is in bijection with the rational subset, with
forward map *literally* the valuation pull-back along `D.canonicalMap`
(see `spaPresheafValueEquivRationalOpen_apply_coe`). Injectivity is uniqueness of
the extension; surjectivity is `exists_spa_presheafValue_of_rationalOpen`. -/
def spaPresheafValueEquivRationalOpen (D : RationalLocData A) :
    ↥(Spa (presheafValue D) (presheafValue D)⁺) ≃
      ↥(rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)) :=
  Equiv.ofBijective
    (fun w => ⟨comap D.canonicalMap w.val,
      comap_canonicalMap_mem_rationalOpen_inter_spa D w⟩)
    ⟨fun w₁ w₂ hw => Subtype.ext (comap_canonicalMap_injOn_spa D w₁.property
        w₂.property (congrArg Subtype.val hw)),
      by
        rintro ⟨v, hv_rat, hv_spa⟩
        obtain ⟨w', hw'_spa, hw'_comap⟩ :=
          exists_spa_presheafValue_of_rationalOpen D hv_rat
        exact ⟨⟨w', hw'_spa⟩, Subtype.ext hw'_comap⟩⟩

/-- The forward map of the canonical equivalence is the valuation pull-back. -/
@[simp] theorem spaPresheafValueEquivRationalOpen_apply_coe
    (D : RationalLocData A) (w : ↥(Spa (presheafValue D) (presheafValue D)⁺)) :
    ((spaPresheafValueEquivRationalOpen D w : ↥(rationalOpen D.T D.s ∩ Spa A A⁺)) :
      Spv A) = comap D.canonicalMap w.val := rfl

/-- **Exact image equality** (Wedhorn 8.2: "the image of `j` is `R(T/s)`"):
`comap D.canonicalMap` maps `Spa (presheafValue D)` *onto* the rational subset. -/
theorem comap_canonicalMap_image_spa (D : RationalLocData A) :
    (comap D.canonicalMap) '' (Spa (presheafValue D) (presheafValue D)⁺) =
      (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)) := by
  apply Set.eq_of_subset_of_subset
  · rintro _ ⟨w, hw, rfl⟩
    exact comap_canonicalMap_mem_rationalOpen_inter_spa D ⟨w, hw⟩
  · rintro v ⟨hv_rat, hv_spa⟩
    obtain ⟨w', hw'_spa, hw'_comap⟩ :=
      exists_spa_presheafValue_of_rationalOpen D hv_rat
    exact ⟨w', hw'_spa, hw'_comap⟩

/-- The forward map of the canonical equivalence is continuous (restriction of the
continuous `comap D.canonicalMap` to the subspaces). Inverse continuity — the
homeomorphism half of Wedhorn 8.2(2) — awaits the parameter-perturbation
machinery (Kedlaya Ex. 1.2.2) and is *not* claimed here. -/
theorem spaPresheafValueEquivRationalOpen_continuous (D : RationalLocData A) :
    Continuous (spaPresheafValueEquivRationalOpen D) :=
  Continuous.subtype_mk
    ((comap_continuous D.canonicalMap).comp continuous_subtype_val) _

/-- **(Wedhorn 8.2 — Spa of `presheafValue` equals rational subset)**
*"`Spa A⟨T/s⟩ → Spa A` is a homeomorphism onto `R(T/s)`"* — the bijection half,
as the `Nonempty (… ≃ …)` headline (moved from `StructureSheaf.lean` and
**discharged** 2026-07-20 by `spaPresheafValueEquivRationalOpen`; the former
noetherian/strongly-noetherian/T2/nonarchimedean binders were unused and are
dropped). -/
theorem Spa_presheafValue_eq_rationalOpen (D : RationalLocData A) :
    Nonempty (Spa (presheafValue D) (presheafValue D)⁺ ≃
      (rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A))) :=
  ⟨spaPresheafValueEquivRationalOpen D⟩

end ValuationSpectrum
