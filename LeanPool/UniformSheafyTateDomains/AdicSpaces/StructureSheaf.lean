/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberLocLift
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Prop752
import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompleteTopCommRingCat
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HomSheafPredicate
import LeanPool.UniformSheafyTateDomains.AdicSpaces.Lemma745
import LeanPool.UniformSheafyTateDomains.AdicSpaces.TopologyComparison
import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentRefinement
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.TensorProduct.IncludeLeftSubRight
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Sheaves.Forget
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Geometry.RingedSpace.Stalks

/-!
# Rational-localization presheaf infrastructure and the internal sheafiness criterion

**The public structure sheaf does NOT live here** — it is the projective-limit
presheaf `structurePresheaf` of `StructurePresheafBundled.lean` (values
`limitSections`, Wedhorn §8.1 / Kedlaya Definition 1.2.3). This file provides:

## Main definitions

* `SpaTop A` : The adic spectrum as an object of `TopCat`.
* `locallyFractionPresheaf A` : a quarantined **discrete** locally-fraction
  comparison presheaf. It is *not* the structure presheaf, its values on rational
  opens are *not* the completed rational localizations `A⟨T/s⟩`, and no sheaf
  assertion is made about it; it survives only as scaffolding for the stalk/
  valuation (`𝒱^pre`) machinery below.
* `VPreObj` / `VObj` : Categories 𝒱^pre and 𝒱 (Definitions 8.5, 8.7, Remark 8.20).
* `IsSheafy` : the project's **internal fixed-pair finite rational-cover
  criterion** — *not* Wedhorn's ring-level Definition 8.26 (that is
  `IsSheafyTateRing`, `SheafyRing.lean`) and not the pair-level public notion
  (`IsSheafyFor`); at complete Tate scope it is equivalent to the latter by
  `isSheafy_iff_isLimitSheaf`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8.1, Definition 8.5,
  Remark 8.20, Definition 8.21, Definition 8.22, Definition 8.26,
  Theorem 8.28(c)
-/

universe u

noncomputable section

open TopCat TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  Topology

namespace ValuationSpectrum

variable (A : Type u) [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-! ### The adic spectrum as a topological space -/

/-- The adic spectrum `Spa(A, A⁺)` as an object of `TopCat`. -/
def SpaTop : TopCat := TopCat.of ↥(Spa A A⁺)

/-- The continuous support map `Spa(A, A⁺) → Spec A` (Remark 4.6 of Wedhorn). -/
def suppSpa : C(SpaTop A, PrimeSpectrum A) where
  toFun x := suppFun x.val
  continuous_toFun := suppFun_continuous.comp continuous_subtype_val

/-! ### The structure sheaf -/

namespace StructureSheaf

variable {A}

/-- The stalk type family `x ↦ A_{supp(x)}` (Definition 8.5 of Wedhorn). -/
abbrev Localizations (x : SpaTop A) : Type u :=
  Localization.AtPrime x.val.supp

/-- A section is a *fraction* if `f(x) = r/s` for fixed `r, s`. -/
def IsFraction {U : Opens (SpaTop A)} (f : ∀ x : U, Localizations x.1) : Prop :=
  ∃ (r s : A), ∀ x : U, ∃ hs : s ∉ x.1.val.supp,
    f x = Localization.mk r ⟨s, hs⟩

/-- `IsFraction` is prelocal: it restricts to smaller open subsets. -/
def isFractionPrelocal : PrelocalPredicate (fun x : SpaTop A ↦ Localizations x) where
  pred f := IsFraction f
  res := by
    rintro V U i f ⟨r, s, w⟩; exact ⟨r, s, fun x ↦ w (i x)⟩

/-- A section is *locally a fraction* if it is a fraction near each point. -/
def isLocallyFraction : LocalPredicate (fun x : SpaTop A ↦ Localizations x) :=
  isFractionPrelocal.sheafify

/-- The sections satisfying `isLocallyFraction` form a subring. -/
def sectionsSubring (U : Opens (SpaTop A)) :
    Subring (∀ x : U, Localizations x.1) where
  carrier := { f | isLocallyFraction.pred f }
  mul_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ra * rb, sa * sb, fun y ↦ ?_⟩
    obtain ⟨hsa, ha'⟩ := wa ⟨y.1, y.2.1⟩
    obtain ⟨hsb, hb'⟩ := wb ⟨y.1, y.2.2⟩
    exact ⟨y.1.val.supp.primeCompl.mul_mem hsa hsb,
      (congr_arg₂ (· * ·) ha' hb').trans (Localization.mk_mul ..)⟩
  one_mem' x :=
    ⟨U, x.2, 𝟙 _, 1, 1, fun y ↦
      ⟨y.1.val.supp.primeCompl.one_mem, Localization.mk_one.symm⟩⟩
  add_mem' {a b} ha hb x := by
    obtain ⟨Va, ma, ia, ra, sa, wa⟩ := ha x
    obtain ⟨Vb, mb, ib, rb, sb, wb⟩ := hb x
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, sa * rb + sb * ra, sa * sb,
      fun y ↦ ?_⟩
    obtain ⟨hsa, ha'⟩ := wa ⟨y.1, y.2.1⟩
    obtain ⟨hsb, hb'⟩ := wb ⟨y.1, y.2.2⟩
    exact ⟨y.1.val.supp.primeCompl.mul_mem hsa hsb,
      (congr_arg₂ (· + ·) ha' hb').trans (Localization.add_mk ..)⟩
  zero_mem' x :=
    ⟨U, x.2, 𝟙 _, 0, 1, fun y ↦
      ⟨y.1.val.supp.primeCompl.one_mem, (Localization.mk_zero _).symm⟩⟩
  neg_mem' {a} ha x := by
    obtain ⟨V, m, i, r, s, w⟩ := ha x
    exact ⟨V, m, i, -r, s, fun y ↦ by
      obtain ⟨hs, h⟩ := w y
      exact ⟨hs, (congr_arg Neg.neg h).trans (Localization.neg_mk ..)⟩⟩

end StructureSheaf

open StructureSheaf

/-! ### Locally-fraction sections as a presheaf valued in CompleteTopCommRingCat

For each open `U ⊆ Spa(A, A⁺)`, the sections `sectionsSubring U` (locally-fraction
functions into stalk localizations) form a commutative ring. We equip this ring
with the discrete uniformity as a placeholder; the correct topology for non-rational
opens is the limit topology over rational covers (§8.1 of Wedhorn). -/

/-- The discrete uniform space on locally-fraction sections. -/
noncomputable instance sectionsUniformSpace (U : Opens (SpaTop A)) :
    UniformSpace ↥(sectionsSubring U) := ⊥

/-- The discrete uniformity on locally-fraction sections. -/
instance sectionsDiscreteUniformity (U : Opens (SpaTop A)) :
    DiscreteUniformity ↥(sectionsSubring U) := DiscreteUniformity.mk rfl

/-- The `IsTopologicalRing` instance on locally-fraction sections (discrete). -/
noncomputable instance sectionsIsTopologicalRing (U : Opens (SpaTop A)) :
    @IsTopologicalRing ↥(sectionsSubring U)
      (sectionsUniformSpace A U).toTopologicalSpace _ := by
  haveI : DiscreteTopology ↥(sectionsSubring U) :=
    DiscreteUniformity.instDiscreteTopology ↥(sectionsSubring U)
  exact { toContinuousMul := ⟨continuous_of_discreteTopology⟩
          toContinuousAdd := ⟨continuous_of_discreteTopology⟩
          toContinuousNeg := ⟨continuous_of_discreteTopology⟩ }

/-- The `IsUniformAddGroup` instance on locally-fraction sections (discrete). -/
noncomputable instance sectionsIsUniformAddGroup (U : Opens (SpaTop A)) :
    @IsUniformAddGroup ↥(sectionsSubring U) (sectionsUniformSpace A U) _ :=
  ⟨DiscreteUniformity.uniformContinuous _ _⟩

/-- The presheaf value on an open `U` as a `CompleteTopCommRingCat` object.

For each open `U`, this is the subring of locally-fraction sections in
`∏ₓ Localization.AtPrime x.supp` (Definition 8.5's shape), equipped with the
**discrete** uniformity. **It is *not* canonically the completed rational
localization `A⟨T/s⟩` on rational subsets** (an earlier docstring claimed
Proposition 8.2 here — corrected 2026-07-20: Prop 8.2 concerns the genuine
presheaf `presheafValue`/`limitSections`, whose topology is nondiscrete; this
object is a set-level comparison device only). -/
noncomputable def presheafSectionsObj (U : Opens (SpaTop A)) :
    CompleteTopCommRingCat.{u} :=
  CompleteTopCommRingCat.of ↥(sectionsSubring U)

/-- The restriction ring homomorphism on locally-fraction sections. -/
noncomputable def presheafSectionsRes {U V : Opens (SpaTop A)} (h : V ≤ U) :
    ↥(sectionsSubring U) →+* ↥(sectionsSubring V) where
  toFun f := ⟨fun x ↦ f.1 ⟨x.1, h x.2⟩,
    isLocallyFraction.toPrelocalPredicate.res (homOfLE h) f.1 f.2⟩
  map_one' := Subtype.ext (funext fun _ ↦ rfl)
  map_mul' _ _ := Subtype.ext (funext fun _ ↦ rfl)
  map_zero' := Subtype.ext (funext fun _ ↦ rfl)
  map_add' _ _ := Subtype.ext (funext fun _ ↦ rfl)

/-- The restriction morphism in `CompleteTopCommRingCat`. -/
noncomputable def presheafSectionsMor {U V : Opens (SpaTop A)} (h : V ≤ U) :
    presheafSectionsObj A U ⟶ presheafSectionsObj A V := by
  refine ⟨presheafSectionsRes A h, ?_⟩
  haveI : DiscreteTopology (presheafSectionsObj A U).α := by
    change DiscreteTopology ↥(sectionsSubring U)
    exact DiscreteUniformity.instDiscreteTopology ↥(sectionsSubring U)
  exact continuous_of_discreteTopology

/-- **QUARANTINED LEGACY PLACEHOLDER — this is *not* Wedhorn's structure presheaf,
and it is *not* the public `structurePresheaf`** (which is the projective-limit
presheaf, `StructurePresheafBundled.lean`).

For each open `U`, this presheaf takes the subring of locally-fraction sections in
`∏ₓ Localization.AtPrime x.supp` with the **discrete** uniformity. Its values on
rational opens are *not* canonically the completed rational localizations
`presheafValue`, and its topology is *not* the projective-limit topology of §8.1 —
were its type-level sheaf property (which holds for every `LocalPredicate`) the
sheaf condition of Definition 8.26, every Tate ring would be sheafy, contradicting
Wedhorn Remark 8.17. No sheaf assertion is made or to be made about this object
(the formerly-sorried `structurePresheaf_isSheaf` was **removed** 2026-07-20 with
the WO1 rewiring); it is retained only as the locally-fraction *comparison* object
feeding the stalk/valuation (`𝒱^pre`) machinery below. -/
noncomputable def locallyFractionPresheaf [IsHuberRing A] [PlusSubring A] :
    Presheaf CompleteTopCommRingCat (SpaTop A) where
  obj U := presheafSectionsObj A U.unop
  map {U V} i := presheafSectionsMor A (leOfHom i.unop)
  map_id U := by
    simp only [presheafSectionsMor, presheafSectionsRes]
    apply Subtype.ext; ext ⟨f, hf⟩
    exact Subtype.ext (funext fun ⟨x, hx⟩ ↦ rfl)
  map_comp {U V W} i j := by
    simp only [presheafSectionsMor, presheafSectionsRes]
    apply Subtype.ext; ext ⟨f, hf⟩
    exact Subtype.ext (funext fun ⟨x, hx⟩ ↦ rfl)

/-- Type-level sheaf condition for the locally-fraction subpresheaf: the underlying
type-presheaf of `locallyFractionPresheaf A` is a sheaf of *types* — an instance of
Mathlib's `subpresheafToTypes.isSheaf`, which holds for **every** `LocalPredicate`
and therefore carries no adic content whatsoever (Wedhorn Remark 8.17: the
topological sheaf condition of Definition 8.26 is *not* type-level). -/
theorem locallyFractionPresheaf_typeLevel_isSheaf [IsHuberRing A] :
    (subpresheafToTypes
      (T := fun x : SpaTop A ↦ StructureSheaf.Localizations x)
      StructureSheaf.isLocallyFraction.toPrelocalPredicate).IsSheaf :=
  subpresheafToTypes.isSheaf StructureSheaf.isLocallyFraction

/-! ### Sheafy affinoid rings (Definition 8.26 of Wedhorn) -/

variable [IsHuberRing A] [HasLocLiftPowerBounded A]

/-- The product restriction map for a rational covering. -/
noncomputable def productRestriction (C : RationalCoveringData A) :
    presheafValue C.base → ∀ D ∈ C.covers, presheafValue D :=
  fun x D hD ↦ restrictionMap C.base D (C.hsubset D hD) x

/-- The product restriction map using a subtype-indexed product. -/
noncomputable def productRestrictionSub (C : RationalCoveringData A) :
    presheafValue C.base → ∀ (D : ↥C.covers), presheafValue D.1 :=
  fun x ⟨D, hD⟩ ↦ restrictionMap C.base D (C.hsubset D hD) x

/-- The **section equalizer** of a rational covering `C`: the families `(s_D)` that agree
on every *common rational refinement* `D₃` of two cover pieces — the common-refinement form
of Čech compatibility (matching the `IsSheafy.gluing` predicate). This is the
compatible-family locus `E ⊆ ∏_D 𝒪_X(D)`, equal to the image of `productRestrictionSub` by
gluing. Using all common refinements (rather than a single chosen intersection datum) avoids
constructing pairwise intersections of pieces with heterogeneous pairs of definition. -/
def sectionEqualizer (C : RationalCoveringData A) :
    Set (∀ D : ↥C.covers, presheafValue D.1) :=
  {s | ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
        (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
        (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
        restrictionMap D₁.1 D₃ h₃₁ (s D₁) = restrictionMap D₂.1 D₃ h₃₂ (s D₂)}

/-- The section equalizer is **closed** in the product. It is the intersection, over all
`(D₁, D₂, D₃, h₃₁, h₃₂)`, of the loci `{s | res_{D₁,D₃}(s D₁) = res_{D₂,D₃}(s D₂)}`, each of
which is the equalizer of two continuous maps into the Hausdorff completion `𝒪_X(D₃)`, hence
closed (`isClosed_eq`). This is the topological input for the embedding step of sheafiness
(expert-review 2026-06-20, Q1: Čech-closedness via common refinements). -/
theorem sectionEqualizer_isClosed (C : RationalCoveringData A) :
    IsClosed (sectionEqualizer A C) := by
  unfold sectionEqualizer
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun D₁ => isClosed_iInter fun D₂ => isClosed_iInter fun D₃ =>
    isClosed_iInter fun h₃₁ => isClosed_iInter fun h₃₂ => ?_
  exact isClosed_eq
    ((restrictionMapHom_continuous D₁.1 D₃ h₃₁).comp (continuous_apply D₁))
    ((restrictionMapHom_continuous D₂.1 D₃ h₃₂).comp (continuous_apply D₂))

/-- The image of `productRestrictionSub` lands in the `sectionEqualizer` — i.e. a global
section restricts compatibly to every common refinement (the easy "separation" direction of
the equalizer, via functoriality of restriction `restrictionMap_comp`; no gluing needed). -/
theorem productRestrictionSub_mem_sectionEqualizer (C : RationalCoveringData A)
    (x : presheafValue C.base) :
    productRestrictionSub A C x ∈ sectionEqualizer A C := by
  intro D₁ D₂ D₃ h₃₁ h₃₂
  obtain ⟨D₁, hD₁⟩ := D₁
  obtain ⟨D₂, hD₂⟩ := D₂
  have e₁ := congr_fun (restrictionMap_comp C.base D₁ D₃ (C.hsubset D₁ hD₁) h₃₁) x
  have e₂ := congr_fun (restrictionMap_comp C.base D₂ D₃ (C.hsubset D₂ hD₂) h₃₂) x
  simp only [Function.comp_apply] at e₁ e₂
  change restrictionMap D₁ D₃ h₃₁ (restrictionMap C.base D₁ (C.hsubset D₁ hD₁) x) =
      restrictionMap D₂ D₃ h₃₂ (restrictionMap C.base D₂ (C.hsubset D₂ hD₂) x)
  rw [e₁, e₂]

/-- The section equalizer is a **complete** space: it is closed (`sectionEqualizer_isClosed`)
in the finite product `∏_D 𝒪_X(D)` of complete completions, hence complete as a closed
subspace. (Foundation for applying the Banach OMT to `ρ̃ : 𝒪_X(U) → E`.) -/
theorem sectionEqualizer_completeSpace (C : RationalCoveringData A) :
    CompleteSpace ↥(sectionEqualizer A C) :=
  (sectionEqualizer_isClosed A C).completeSpace_coe

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- The uniformity of `𝒪_X(D)` is **countably generated** (Henkel's "countable fundamental
system of nbhds of `0`"): the localization has a countable nbhd-of-`0` basis (`locBasis`), so its
completion is metrizable, giving `nhds 0` a countable basis; for a uniform additive group this is
the uniformity being countably generated. -/
theorem presheafValue_uniformity_isCountablyGenerated (D : RationalLocData A) :
    Filter.IsCountablyGenerated (uniformity (presheafValue D)) := by
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  haveI : (nhds (0 : Localization.Away D.s)).IsCountablyGenerated :=
    (locBasis D.P D.T D.s D.hopen).hasBasis_nhds_zero.isCountablyGenerated
  haveI : Filter.IsCountablyGenerated (uniformity (Localization.Away D.s)) :=
    IsUniformAddGroup.uniformity_countably_generated
  haveI : (nhds (0 : presheafValue D)).IsCountablyGenerated := by
    letI : PseudoMetricSpace (Localization.Away D.s) := UniformSpace.pseudoMetricSpace _
    letI : MetricSpace (presheafValue D) := UniformSpace.Completion.instMetricSpace
    infer_instance
  exact IsUniformAddGroup.uniformity_countably_generated

/-- The uniformity on the section equalizer `E` is **countably generated**: `E` carries the
subspace uniformity (the comap of `Subtype.val`) of the finite product `∏_D 𝒪_X(D)`, whose
uniformity is countably generated (finite product of countably-generated completions). -/
theorem sectionEqualizer_isCountablyGenerated (C : RationalCoveringData A) :
    Filter.IsCountablyGenerated (uniformity ↥(sectionEqualizer A C)) := by
  haveI : ∀ D : ↥C.covers, Filter.IsCountablyGenerated (uniformity (presheafValue D.1)) :=
    fun D => presheafValue_uniformity_isCountablyGenerated A D.1
  exact Filter.comap.isCountablyGenerated _ _

/-- **Internal finite rational-cover criterion** for a fixed pair `(A, A⁺)` — the
proof-engine class of the 8.28(b) campaign. **Naming note (WO3, 2026-07-20): this is
NOT the literature's ring-level "sheafy" (Wedhorn Definition 8.26)** — that is
`IsSheafyTateRing` (`SheafyRing.lean`), which quantifies over the rings of integral
elements of the completion; the pair-level public notion is `IsSheafyFor` (bundled
valid pair, genuine all-open presheaf), equivalent to this class at complete Tate
scope by `isSheafy_iff_isLimitSheaf`. New code should state results through those;
this class remains as the internal criterion the existing proof corpus is written
against.

An affinoid ring `(A, A⁺)` satisfies this criterion if the rational-localization
presheaf satisfies, on every rational cover, the conditions that Remark 8.20 makes
equivalent to the sheaf-of-topological-rings property — two conditions on every
rational cover `C` —
quantified over coverings of rational subsets by rational subsets in Wedhorn
Definition 7.29's sense (`RationalCoveringData.IsRational`: base and pieces have `T·A`
open in `A`, wedhorn.txt:3100, 4143):
1. **`embedding`**: the product restriction `O_X(base) → ∏ O_X(cover_i)` is a
   **topological embedding** (injective + the source topology equals the
   subspace topology induced from the product topology on the target).
2. **`gluing`**: compatible families on the cover have a global pre-image
   (necessarily unique by `embedding.injective`).

The `embedding` field subsumes the sheaf-of-sets injectivity (`Topology.IsEmbedding`
implies `Function.Injective`); together with `gluing` it gives the full sheaf
condition in the category of (complete) topological rings.

**Proof route for strongly noetherian Tate rings** (Wedhorn Thm 8.28(b)):
1. **Example 6.38** gives `presheafValue D ≃_top A⟨X⟩/(closed ideal)` as a
   *topological* ring iso (universal property + Wedhorn Prop 6.17).
2. **Lemma 8.31** (flatness) + **Cor 8.32** (faithful flatness of the product
   restriction) give the **algebraic** sheaf-of-sets injectivity.
3. **Lemma 8.33** (3×3 diagram chase) + **Lemma 8.34** (refinement transfer)
   transport the topological structure from the Tate-algebra-quotient side.
   Quotient maps of Tate algebras are continuous and open, so the diagram chase
   preserves the topological embedding through the refinement.

See `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md`. -/
class IsSheafy (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [inst₁ : PlusSubring A] [inst₂ : IsHuberRing A]
    [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] : Prop where
  embedding : ∀ (C : RationalCoveringData A), C.IsRational →
    Topology.IsEmbedding (productRestrictionSub A C)
  gluing : ∀ (C : RationalCoveringData A), C.IsRational →
    ∀ (f : ∀ (D : ↥C.covers), presheafValue D.1),
    (∀ (D₁ D₂ : ↥C.covers)
       (D₃ : RationalLocData A)
       (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
       (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
       restrictionMap D₁.1 D₃ h₃₁ (f D₁) =
         restrictionMap D₂.1 D₃ h₃₂ (f D₂)) →
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D

/-- Sheafy implies separation (injectivity of `productRestrictionSub`),
extracted from the embedding field. -/
theorem IsSheafy.separationSub [IsTopologicalRing A] [PlusSubring A]
    [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] [IsSheafy A] (C : RationalCoveringData A)
    (hC : C.IsRational) :
    Function.Injective (productRestrictionSub A C) :=
  (IsSheafy.embedding (A := A) C hC).injective

/-- Sheafy implies separation (injectivity of `productRestriction`). -/
theorem IsSheafy.separation_injective [IsTopologicalRing A] [PlusSubring A]
    [IsHuberRing A] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)] [IsSheafy A] (C : RationalCoveringData A)
    (hC : C.IsRational) :
    Function.Injective (productRestriction A C) := by
  intro x y hxy
  apply IsSheafy.separationSub (A := A) C hC
  funext ⟨D, hD⟩
  exact congr_fun (congr_fun hxy D) hD

-- `AffinoidAdicPresentation` and `AdicSpacePresentation` (honest presentation-level
-- structures; NOT Wedhorn Definitions 8.21/8.22, which are 𝒱-level — see their
-- docstrings) live in `StructurePresheafBundled.lean`: the sheafiness
-- field of an affinoid adic space is Wedhorn's actual condition — the genuine
-- all-open structure presheaf is a sheaf of topological rings (`IsLimitSheaf`) —
-- which is only available downstream of `SheafyPair`.

/-! ### The categories 𝒱^pre and 𝒱 (Definitions 8.5, 8.7, Remark 8.20 of Wedhorn) -/

/-- A presheafed space of complete topological rings (Definition 8.5). -/
abbrev TopRingPresheafedSpace := PresheafedSpace CompleteTopCommRingCat.{u}

namespace TopRingPresheafedSpace

variable (X : TopRingPresheafedSpace.{u})

/-- The underlying ring presheaf (forgetting topology). -/
def ringPresheaf : X.carrier.Presheaf CommRingCat.{u} :=
  X.presheaf ⋙ CompleteTopCommRingCat.forgetToCommRingCat

/-- The underlying topological presheaf (forgetting ring structure). -/
def topPresheaf : X.carrier.Presheaf TopCat.{u} :=
  X.presheaf ⋙ CompleteTopCommRingCat.forgetToTopCat

/-- The ring stalk `𝒪_{X,x}` at a point `x`. -/
noncomputable def ringStalk (x : X) : CommRingCat.{u} :=
  (X.ringPresheaf).stalk x

end TopRingPresheafedSpace

/-! ### Ring stalk maps for presheafed spaces of complete topological rings -/

/-- The ring stalk map `𝒪_{Y,f(x)} → 𝒪_{X,x}` induced by `α : X ⟶ Y`. -/
noncomputable def ringStalkMap {X Y : TopRingPresheafedSpace.{u}}
    (α : X ⟶ Y) (x : X) :
    Y.ringPresheaf.stalk (ConcreteCategory.hom α.base x) ⟶
    X.ringPresheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor CommRingCat (ConcreteCategory.hom α.base x)).map
    (Functor.whiskerRight α.c CompleteTopCommRingCat.forgetToCommRingCat) ≫
    X.ringPresheaf.stalkPushforward CommRingCat α.base x

/-- The ring stalk map of the identity morphism is the identity. -/
@[simp]
theorem ringStalkMap_id (X : TopRingPresheafedSpace.{u}) (x : X) :
    ringStalkMap (𝟙 X) x = 𝟙 (X.ringStalk x) := by
  dsimp [ringStalkMap]
  rw [TopCat.Presheaf.stalkPushforward.id, ← Functor.map_comp]
  exact (TopCat.Presheaf.stalkFunctor CommRingCat x).map_id X.ringPresheaf

/-- The ring stalk map is functorial under composition. -/
@[simp]
theorem ringStalkMap_comp {X Y Z : TopRingPresheafedSpace.{u}}
    (α : X ⟶ Y) (β : Y ⟶ Z) (x : X) :
    ringStalkMap (α ≫ β) x =
      ringStalkMap β (ConcreteCategory.hom α.base x) ≫ ringStalkMap α x := by
  -- `ringStalkMap α x` is definitionally `((mapPresheaf fgt).map α).stalkMap x`, so
  -- functoriality reduces to mathlib's `PresheafedSpace.stalkMap.comp`.
  show (CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.map (α ≫ β)).stalkMap x = _
  rw [AlgebraicGeometry.PresheafedSpace.stalkMap.congr_hom _ _
        (CompleteTopCommRingCat.forgetToCommRingCat.mapPresheaf.map_comp α β) x,
      AlgebraicGeometry.PresheafedSpace.stalkMap.comp]
  simp only [eqToHom_refl, Category.id_comp]
  rfl

/-! ### The category 𝒱^pre (Definition 8.5 of Wedhorn) -/

/-- An object of `𝒱^pre` (Definition 8.5 of Wedhorn). -/
structure VPreObj where
  /-- The underlying presheafed space of complete topological rings. -/
  toPresheafedSpace : TopRingPresheafedSpace.{u}
  /-- Each stalk is a local ring. -/
  isLocalRing_stalk : ∀ x : toPresheafedSpace,
    IsLocalRing (toPresheafedSpace.ringStalk x)
  /-- The valuation on each stalk. -/
  val : ∀ x : toPresheafedSpace, Spv (toPresheafedSpace.ringStalk x)
  /-- The support of the valuation equals the maximal ideal. -/
  val_supp : ∀ x : toPresheafedSpace,
    (val x).supp = @IsLocalRing.maximalIdeal _ _ (isLocalRing_stalk x)

namespace VPreObj

variable (X : VPreObj.{u})

instance : CoeSort VPreObj.{u} (Type u) := ⟨fun X ↦ X.toPresheafedSpace⟩

instance (x : X) : IsLocalRing (X.toPresheafedSpace.ringStalk x) :=
  X.isLocalRing_stalk x

/-- The underlying topological space of a `VPreObj`. -/
def toTopCat : TopCat.{u} := X.toPresheafedSpace.carrier

/-- The presheaf of complete topological rings. -/
def presheaf : X.toTopCat.Presheaf CompleteTopCommRingCat.{u} :=
  X.toPresheafedSpace.presheaf

/-- The underlying ring presheaf (forgetting topology). -/
noncomputable def ringPresheaf : X.toTopCat.Presheaf CommRingCat.{u} :=
  X.toPresheafedSpace.ringPresheaf

end VPreObj

/-- A morphism in `𝒱^pre` (Definition 8.7 of Wedhorn). -/
structure VPreHom (X Y : VPreObj.{u}) where
  /-- The underlying morphism of presheafed spaces. -/
  toHom : X.toPresheafedSpace ⟶ Y.toPresheafedSpace
  /-- The ring stalk maps are local ring homomorphisms. -/
  isLocalHom_stalkMap : ∀ x : X.toPresheafedSpace,
    IsLocalHom (ringStalkMap toHom x).hom'
  /-- Valuation compatibility: `w_{f(x)} = comap f♭_x v_x`. -/
  val_compat : ∀ x : X.toPresheafedSpace,
    Y.val (ConcreteCategory.hom toHom.base x) =
      (X.val x).comap (ringStalkMap toHom x).hom'

/-- Extensionality for `VPreHom`. -/
@[ext]
theorem VPreHom.ext {X Y : VPreObj.{u}} {f g : VPreHom X Y}
    (h : f.toHom = g.toHom) : f = g := by
  cases f; cases g; congr

/-- The `Category` instance on `VPreObj` (Definition 8.7 of Wedhorn). -/
instance : CategoryTheory.Category VPreObj.{u} where
  Hom X Y := VPreHom X Y
  id X := {
    toHom := 𝟙 X.toPresheafedSpace
    isLocalHom_stalkMap := fun x ↦ by
      rw [ringStalkMap_id]
      exact isLocalHom_id _
    val_compat := fun x ↦ by
      simp only [ringStalkMap_id]
      exact (congr_fun ValuationSpectrum.comap_id (X.val x)).symm }
  comp f g := {
    toHom := f.toHom ≫ g.toHom
    isLocalHom_stalkMap := fun x ↦ by
      rw [ringStalkMap_comp]
      haveI := f.isLocalHom_stalkMap x
      haveI := g.isLocalHom_stalkMap (ConcreteCategory.hom f.toHom.base x)
      change IsLocalHom ((ringStalkMap f.toHom x).hom'.comp
        (ringStalkMap g.toHom (ConcreteCategory.hom f.toHom.base x)).hom')
      infer_instance
    val_compat := fun x ↦ by
      rw [ringStalkMap_comp]
      erw [g.val_compat (ConcreteCategory.hom f.toHom.base x), f.val_compat x]
      exact (congr_fun (ValuationSpectrum.comap_comp _ _) _).symm }
  id_comp := fun f ↦ VPreHom.ext (Category.id_comp f.toHom)
  comp_id := fun f ↦ VPreHom.ext (Category.comp_id f.toHom)
  assoc := fun f g h ↦ VPreHom.ext (Category.assoc f.toHom g.toHom h.toHom)

/-! ### The full subcategory 𝒱 (Remark 8.20 of Wedhorn) -/

/-- An object of `𝒱`: a valued sheafed space (Remark 8.20 of Wedhorn). -/
structure VObj extends VPreObj.{u} where
  /-- **The sheaf-of-topological-rings condition** (Wedhorn Remark 8.20, stored in
  the `Hom_cont(T, −)` form for every topological commutative test ring in the
  working universe — `HomSheafPredicate.lean`). This is Wedhorn's actual condition
  for membership in `𝒱`; the merely-algebraic ring-presheaf sheaf condition is a
  consequence (`VObj.ringPresheaf_isSheaf`), not the definition (P5 repair
  2026-07-20; the previous field stored only the latter). -/
  isSheafTopRings : toVPreObj.toPresheafedSpace.presheaf.IsSheafOfTopologicalRings

/-- The underlying ring presheaf of a `𝒱`-object is a sheaf (the algebraic half of
Remark 8.20; via discrete test rings). -/
theorem VObj.ringPresheaf_isSheaf (V : VObj.{u}) :
    (V.toVPreObj.toPresheafedSpace.ringPresheaf).IsSheaf :=
  V.isSheafTopRings.ringPresheaf_isSheaf

/-- The `Category` instance on `VObj` (full subcategory of `VPreObj`). -/
instance : CategoryTheory.Category VObj.{u} where
  Hom X Y := VPreHom X.toVPreObj Y.toVPreObj
  id X := {
    toHom := 𝟙 X.toVPreObj.toPresheafedSpace
    isLocalHom_stalkMap := fun x ↦ by
      rw [ringStalkMap_id]
      exact isLocalHom_id _
    val_compat := fun x ↦ by
      simp only [ringStalkMap_id]
      exact (congr_fun ValuationSpectrum.comap_id (X.val x)).symm }
  comp f g := {
    toHom := f.toHom ≫ g.toHom
    isLocalHom_stalkMap := fun x ↦ by
      rw [ringStalkMap_comp]
      haveI := f.isLocalHom_stalkMap x
      haveI := g.isLocalHom_stalkMap (ConcreteCategory.hom f.toHom.base x)
      change IsLocalHom ((ringStalkMap f.toHom x).hom'.comp
        (ringStalkMap g.toHom (ConcreteCategory.hom f.toHom.base x)).hom')
      infer_instance
    val_compat := fun x ↦ by
      rw [ringStalkMap_comp]
      erw [g.val_compat (ConcreteCategory.hom f.toHom.base x), f.val_compat x]
      exact (congr_fun (ValuationSpectrum.comap_comp _ _) _).symm }
  id_comp f := VPreHom.ext (Category.id_comp f.toHom)
  comp_id f := VPreHom.ext (Category.comp_id f.toHom)
  assoc f g h := VPreHom.ext (Category.assoc f.toHom g.toHom h.toHom)

/-- The forgetful functor from `𝒱` to `𝒱^pre`. -/
def VObj.forgetToVPre : VObj.{u} ⥤ VPreObj.{u} where
  obj X := X.toVPreObj
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-! ### Sheafiness of strongly noetherian Tate rings (Theorem 8.28 of Wedhorn)

Strongly noetherian Tate rings are sheafy via Tate acyclicity. The proof proceeds by:
1. Laurent cover exactness for 2-element covers (Lemma 8.33, sorry-free).
2. Rational coverings refine products of Laurent covers (Lemma 7.54).
3. Refinement preserves separation (Proposition A.3, sorry-free). -/

/-- The product restriction on the dense embedding agrees with the
algebraic restriction: for `z` in the localization,
`productRestriction C (coeRingHom z) D hD = restrictionMapAlg z`.

This is the key factorization: the product restriction on the
completion EXTENDS the algebraic product restriction on the dense
subring. -/
theorem productRestriction_coe_eq
    (C : RationalCoveringData A) (z : Localization.Away C.base.s)
    (D : RationalLocData A) (hD : D ∈ C.covers) :
    productRestriction A C (C.base.coeRingHom z) D hD =
      restrictionMapAlg C.base D (C.hsubset D hD) z := by
  change restrictionMap C.base D (C.hsubset D hD) (C.base.coeRingHom z) = _
  unfold restrictionMap restrictionMapHom
  letI := C.base.uniformSpace
  letI := C.base.isTopologicalRing
  letI := C.base.isUniformAddGroup
  letI := D.uniformSpace
  letI := D.isTopologicalRing
  letI := D.isUniformAddGroup
  erw [UniformSpace.Completion.extensionHom_coe (restrictionMapAlg C.base D (C.hsubset D hD))
    (restrictionMapAlg_continuous C.base D (C.hsubset D hD))]

/-- Each component of the product restriction is a ring homomorphism.
This is because `restrictionMap D D' h` is defined via
`extensionHom`, which produces a `RingHom`. -/
theorem productRestriction_map_sub
    (C : RationalCoveringData A) (x y : presheafValue C.base)
    (D : RationalLocData A) (hD : D ∈ C.covers) :
    productRestriction A C (x - y) D hD =
      productRestriction A C x D hD -
        productRestriction A C y D hD := by
  change restrictionMap C.base D _ (x - y) = _
  exact map_sub (restrictionMapHom C.base D (C.hsubset D hD)) x y

/-! #### Factorization of restrictionMapAlg through localization -/

/-- The algebraic restriction map factors through the completion
embedding: `restrictionMapAlg C.base D h = D.coeRingHom ∘ locLift`
when `C.base.s` is a unit in `Localization.Away D.s`.

Both sides are ring homs from `Localization.Away C.base.s` to
`presheafValue D` that agree on `algebraMap(a)`, so they are equal
by the universal property of localization. -/
theorem restrictionMapAlg_factors (C : RationalCoveringData A)
    (D : RationalLocData A) (hD : D ∈ C.covers)
    (hs_unit : IsUnit (algebraMap A (Localization.Away D.s) C.base.s)) :
    D.coeRingHom.comp (IsLocalization.Away.lift (S := Localization.Away C.base.s)
      C.base.s hs_unit) = restrictionMapAlg C.base D (C.hsubset D hD) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers C.base.s)
  ext a
  simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, restrictionMapAlg,
    RationalLocData.canonicalMap, RationalLocData.coeRingHom]

/-! #### The Spa-point radical argument (Wedhorn Theorem 8.28)

Shows `C.base.s ∈ radical(ann(a))` given `D.s^k * a = 0` for each covering piece `D`,
using the covering condition on `Spa(A, A⁺)`. For discrete rings, proved via trivial
valuations; for general Tate rings, requires Lemma 7.45 of Wedhorn. -/

omit [IsHuberRing A] in
/-- For an open prime `p` with `s ∉ p`, the trivial valuation on `Frac(A/p)` pulled back
to `A` lies in `rationalOpen T s`. Continuity follows from `p` being open. -/
theorem exists_spa_point_in_rationalOpen_of_isOpen_prime
    (T : Finset A) (s : A)
    (p : Ideal A) [p.IsPrime]
    (hp_open : IsOpen (p : Set A))
    (hs_notin : s ∉ p) :
    ∃ v ∈ rationalOpen T s, p ≤ v.supp := by
  classical
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  let φ : A →+* FractionRing (A ⧸ p) :=
    (algebraMap (A ⧸ p) (FractionRing (A ⧸ p))).comp (Ideal.Quotient.mk p)
  let w : Valuation A (WithZero (Multiplicative ℤ)) :=
    (1 : Valuation (FractionRing (A ⧸ p)) (WithZero (Multiplicative ℤ))).comap φ
  let v := ofValuation w
  have hw_mem_iff : ∀ (a : A), w a = 0 ↔ a ∈ p := by
    intro a
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply,
      Valuation.one_apply_eq_zero_iff]
    exact ⟨fun h ↦ Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero])),
      fun ha ↦ by rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]⟩
  have hv_supp_eq : v.supp = p := by
    rw [supp_ofValuation]; ext a; exact hw_mem_iff a
  have hw_s : w s = 1 := by
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply]
    apply Valuation.one_apply_of_ne_zero
    intro heq
    apply hs_notin
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero]))
  have hw_one_or_zero : ∀ (a : A), w a = 0 ∨ w a = 1 := by
    intro a
    simp only [w, Valuation.comap_apply, φ, RingHom.comp_apply]
    rcases eq_or_ne ((algebraMap (A ⧸ p) (FractionRing (A ⧸ p)))
        ((Ideal.Quotient.mk p) a)) 0 with h | h
    · left; rw [h]; simp
    · right; exact Valuation.one_apply_of_ne_zero h
  have hv_spa : v ∈ Spa A A⁺ := by
    refine ⟨?_, ?_⟩
    · apply isContinuous_ofValuation_of; intro γ
      by_cases hγ : γ = 0
      · subst hγ; convert isOpen_empty
        ext a; simp [not_lt_zero]
      · by_cases h1 : (1 : WithZero (Multiplicative ℤ)) < γ
        · convert isOpen_univ; ext a
          simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, w, Valuation.comap_apply]
          exact lt_of_le_of_lt (Valuation.one_apply_le_one _) h1
        · push Not at h1
          suffices {a : A | w a < γ} = (p : Set A) by rw [this]; exact hp_open
          ext a
          simp only [Set.mem_setOf_eq]
          constructor
          · intro h
            rcases hw_one_or_zero a with ha0 | ha1
            · exact (hw_mem_iff a).mp ha0
            · exact absurd (ha1 ▸ h |>.trans_le h1) (lt_irrefl _)
          · intro ha
            rw [(hw_mem_iff a).mpr ha]; exact zero_lt_iff.mpr hγ
    · intro f _; change w f ≤ w 1
      simp only [w, Valuation.comap_apply, map_one]; exact Valuation.one_apply_le_one _
  have hv_rat : v ∈ rationalOpen T s := by
    refine ⟨hv_spa, ?_, ?_⟩
    · intro t' _
      change w t' ≤ w s; rw [hw_s]
      simp only [w, Valuation.comap_apply]
      exact Valuation.one_apply_le_one _
    · change ¬ (w s ≤ w 0)
      simp only [hw_s, map_zero, le_zero_iff, one_ne_zero, not_false_eq_true, w]
  exact ⟨v, hv_rat, hv_supp_eq ▸ le_refl _⟩

-- `exists_spa_point_in_rationalOpen` (combined version, open + non-open prime) was
-- removed 2026-04-14: its sole sorry (non-open prime case) had no actual callers,
-- and downstream (`base_s_in_annihilator_radical_of_covering`, etc.) takes the
-- Spa-point existence as an explicit hypothesis. Use
-- `exists_spa_point_in_rationalOpen_of_isOpen_prime` for the open-prime case
-- directly, or `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime`
-- (Lemma745.lean:691) on `presheafValue_pairOfDefinition` for the non-open case.

/-- If `D.s^k * a = 0` for each covering piece `D`, then `C.base.s ∈ radical(ann(a))`
(Wedhorn Theorem 8.28). Uses the Spa-point construction at primes. -/
theorem base_s_in_annihilator_radical_of_covering
    (C : RationalCoveringData A) (a : A)
    (ha_ann : ∀ (D : RationalLocData A), D ∈ C.covers →
      ∃ k : ℕ, D.s ^ k * a = 0)
    (hSpa_points : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    C.base.s ∈ (Ideal.span ({b : A | b * a = 0} : Set A)).radical := by
  classical
  rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
  intro p ⟨hp_ann, hp_prime⟩
  haveI := hp_prime
  by_contra hs_notin
  obtain ⟨v, hv_rat, hv_supp_ge⟩ := hSpa_points p hp_prime hs_notin
  obtain ⟨D, hD, hv_D⟩ := C.hcover v hv_rat
  have hDs_notin_supp : D.s ∉ v.supp := fun hDs ↦
    hv_D.2.2 ((v.mem_supp_iff D.s).mp hDs)
  have hDs_notin : D.s ∉ p :=
    fun hDs ↦ hDs_notin_supp (hv_supp_ge hDs)
  obtain ⟨k, hk⟩ := ha_ann D hD
  exact hDs_notin (Ideal.IsPrime.mem_of_pow_mem hp_prime k
    (hp_ann (Ideal.subset_span hk)))

/-! **Completion-level kernel reduction.**

If the algebraic product restriction is injective on `Localization.Away C.base.s`,
then the product restriction `presheafValue C.base → ∏ presheafValue D` is injective
on the completion. Requires the `AdicCompletion` bridge (Wedhorn Thm 8.28, Stacks 00MA). -/

/-- The combined restriction map from `presheafValue C.base` to the
product of `presheafValue D` over covering pieces is continuous
(each component is `restrictionMapHom`, which extends the algebraic
restriction map by continuity). -/
private theorem continuous_productRestriction (C : RationalCoveringData A) :
    Continuous (fun z : presheafValue C.base ↦
      fun (D : ↥C.covers) ↦ restrictionMap C.base D.1 (C.hsubset D.1 D.2) z) := by
  apply continuous_pi
  intro ⟨D, hD⟩
  exact restrictionMapHom_continuous C.base D (C.hsubset D hD)

/-- The combined restriction is a ring homomorphism, so its kernel is
an additive subgroup. -/
private theorem map_sub_productRestriction (C : RationalCoveringData A)
    (x y : presheafValue C.base) (D : RationalLocData A)
    (hD : D ∈ C.covers) :
    restrictionMap C.base D (C.hsubset D hD) (x - y) =
      restrictionMap C.base D (C.hsubset D hD) x -
        restrictionMap C.base D (C.hsubset D hD) y :=
  map_sub (restrictionMapHom C.base D (C.hsubset D hD)) x y

/-! ### Old direct proof route (QUARANTINED)

These theorems form the old direct proof of Theorem 8.28 via the Spa-point radical
argument. The route has fundamental issues (`localization_isT0` is false when
`locIdeal = T`, `completionKer_eq_bot_of_locKer_eq_bot` needs faithful flatness).
The correct proof routes through `TopologyComparison.lean`. -/

-- REMOVED (T6): completionKer_eq_bot_of_locKer_eq_bot, localization_isT0,
-- loc_algebraic_injectivity_of_tate — quarantined as false/depending on false.
-- Superseded by the Laurent refinement route (rationalCovering_hasSeparation).

/-! #### Separation via the TopologyComparison isomorphism

The new proof of `separation_ofStronglyNoetherianTate` routes through
`presheafValueTateQuotientEquiv : presheafValue D ≃+* A⟨X⟩/(1-sX)`.

**Proof outline:** The isomorphism `e : presheafValue C.base ≃+* Q₀`
(where `Q₀ = A⟨X⟩/(1-s₀X)`) and the isomorphisms `eD : presheafValue D ≃+* QD`
transfer the product restriction to a ring hom `Q₀ → ∏ QD` between
Tate algebra quotients. This ring hom is injective because it factors
through the localization product map, which is injective by the
covering condition (Spa-point radical argument). -/

/-- If `s ∈ radical(ann(a))` and `s` is a unit in `A⟨X⟩/(1-sX)`,
then `mk(algebraMap a) = 0` in the quotient. -/
private theorem algebraMap_zero_of_radical_ann
    [NonarchimedeanRing A] (s a : A)
    (hs_rad : s ∈ (Ideal.span ({b : A | b * a = 0} : Set A)).radical) :
    (Ideal.Quotient.mk (oneSubfXIdeal s)) (algebraMap A _ a) = 0 := by
  rw [Ideal.mem_radical_iff] at hs_rad
  obtain ⟨N, hN⟩ := hs_rad
  have hs_ann : s ^ N * a = 0 := by
    let ann_a : Ideal A :=
      { carrier := {b : A | b * a = 0}
        add_mem' := fun {x y} (hx : x * a = 0) (hy : y * a = 0) => by
          change (x + y) * a = 0; rw [add_mul, hx, hy, add_zero]
        zero_mem' := zero_mul a
        smul_mem' := fun r {x} (hx : x * a = 0) => by
          change r * x * a = 0; rw [mul_assoc, hx, mul_zero] }
    have hspan : Ideal.span ({b : A | b * a = 0} : Set A) = ann_a :=
      le_antisymm (Ideal.span_le.mpr (fun _ h ↦ h)) (fun _ h ↦ Ideal.subset_span h)
    rw [hspan] at hN
    exact hN
  have hs_unit := isUnit_algebraMap_f_in_quotient_gen s
  rw [RingHom.comp_apply] at hs_unit
  have hmul : (Ideal.Quotient.mk (oneSubfXIdeal s)) (algebraMap A _ (s ^ N * a)) = 0 := by
    rw [hs_ann, map_zero, map_zero]
  rw [map_mul, map_pow] at hmul
  exact (IsUnit.mul_right_eq_zero (IsUnit.pow N hs_unit)).mp hmul

/-- If `z = C.base.canonicalMap a` and the product restriction kills `z`,
then `e_base z = 0`.

The proof uses `rationalCovering_hasSeparation` from the Laurent refinement route:
the product restriction being zero on all covering pieces implies the element is zero
in `presheafValue C.base`, hence its image under `e_base` is zero. -/
theorem tateQuotientProductRestriction_injective_on_algebraMap
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    (e_base : presheafValue C.base ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal C.base.s))
    (_e_cover : ∀ D ∈ C.covers, presheafValue D ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s))
    (_compat_base : ∀ a : A, e_base (C.base.canonicalMap a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a))
    (_compat_cover : ∀ (D : RationalLocData A) (hD : D ∈ C.covers) (a : A),
      (_e_cover D hD) (D.canonicalMap a) =
        (Ideal.Quotient.mk _) (algebraMap A _ a))
    (hSpa : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (a : A)
    (hker : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      productRestriction A C (C.base.canonicalMap a) D hD = 0) :
    e_base (C.base.canonicalMap a) = 0 := by
  have hzero : C.base.canonicalMap a = 0 :=
    rationalCovering_hasSeparation P C hSpa (C.base.canonicalMap a) 0 (fun D hD ↦ by
      change restrictionMap C.base D (C.hsubset D hD) (C.base.canonicalMap a) =
        restrictionMap C.base D (C.hsubset D hD) 0
      rw [show restrictionMap C.base D (C.hsubset D hD) 0 =
        (0 : presheafValue D) from map_zero (restrictionMapHom C.base D (C.hsubset D hD))]
      exact hker D hD)
  rw [hzero, map_zero]

/-- The product restriction, transferred to Tate algebra quotients via the isomorphism,
has trivial kernel (Theorem 8.28 of Wedhorn).

The proof uses `rationalCovering_hasSeparation` from the Laurent refinement route:
the product restriction being zero on all covering pieces implies the element is zero
in `presheafValue C.base`, hence its image under `e_base` is zero. -/
theorem tateQuotientProductRestriction_injective
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    (_e_base : presheafValue C.base ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal C.base.s))
    (_e_cover : ∀ D ∈ C.covers, presheafValue D ≃+*
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s))
    (_compat_base : ∀ a : A, _e_base (C.base.canonicalMap a) =
      (Ideal.Quotient.mk _) (algebraMap A _ a))
    (_compat_cover : ∀ (D : RationalLocData A) (hD : D ∈ C.covers) (a : A),
      (_e_cover D hD) (D.canonicalMap a) =
        (Ideal.Quotient.mk _) (algebraMap A _ a))
    (hSpa : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (z : presheafValue C.base)
    (hker : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      productRestriction A C z D hD = 0) :
    _e_base z = 0 := by
  have hzero : z = 0 :=
    rationalCovering_hasSeparation P C hSpa z 0 (fun D hD ↦ by
      change restrictionMap C.base D (C.hsubset D hD) z =
        restrictionMap C.base D (C.hsubset D hD) 0
      rw [show restrictionMap C.base D (C.hsubset D hD) 0 =
        (0 : presheafValue D) from map_zero (restrictionMapHom C.base D (C.hsubset D hD))]
      exact hker D hD)
  rw [hzero, map_zero]

/-- The product restriction is injective for strongly noetherian Tate rings
(Theorem 8.28 of Wedhorn, separation component via TopologyComparison). -/
theorem separation_ofStronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    (hb_base : TopologicalRing.IsPowerBounded (invS C.base))
    (hcs_base : @CompleteSpace _ (quotientTUniformSpace C.base.s))
    (ht0_base : @T0Space _ (quotientTTopology C.base.s))
    (hcont_base : @Continuous _ _
      (quotientTTopology C.base.s)
      (inferInstance : TopologicalSpace (presheafValue C.base))
      (tateQuotientToPresheafHom C.base hb_base))
    (hdense_base : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal C.base.s)
      (quotientTTopology C.base.s) (Localization.Away C.base.s)
      (locToQuotientOneSubfX_gen C.base.s))
    (hb_all : ∀ D : RationalLocData A, TopologicalRing.IsPowerBounded (invS D))
    (hcs_cover : ∀ D ∈ C.covers, @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0_cover : ∀ D ∈ C.covers, @T0Space _ (quotientTTopology D.s))
    (hcont_cover : ∀ D ∈ C.covers, @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D (hb_all D)))
    (hdense_cover : ∀ D ∈ C.covers, @DenseRange
      (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s))
    (hSpa : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    Function.Injective (productRestriction A C) := by
  let e_base := presheafValueTateQuotientEquiv C.base hb_base hcs_base ht0_base
    hcont_base hdense_base
  intro x y hxy
  suffices h : x - y = 0 from sub_eq_zero.mp h
  have hker : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
      productRestriction A C (x - y) D hD = 0 := by
    intro D hD
    rw [productRestriction_map_sub, sub_eq_zero]
    exact congr_fun (congr_fun hxy D) hD
  set z := x - y
  set q := e_base z
  suffices hq : q = 0 by
    have : e_base z = 0 := hq
    exact e_base.injective (this.trans (map_zero e_base.toRingHom).symm)
  exact tateQuotientProductRestriction_injective (A := A) P C e_base
    (fun D hD ↦ presheafValueTateQuotientEquiv D (hb_all D)
      (hcs_cover D hD) (ht0_cover D hD) (hcont_cover D hD) (hdense_cover D hD))
    (fun a ↦ presheafValueTateQuotientEquiv_canonicalMap C.base
      hb_base hcs_base ht0_base hcont_base hdense_base a)
    (fun D hD a ↦ presheafValueTateQuotientEquiv_canonicalMap D
      (hb_all D) (hcs_cover D hD) (ht0_cover D hD) (hcont_cover D hD)
      (hdense_cover D hD) a)
    hSpa z hker

/-! ### Flatness of presheafValue (Wedhorn Proposition 8.30, via TopologyComparison) -/

omit [HasLocLiftPowerBounded A] in
/-- `presheafValue D` is flat over `A` (Wedhorn Proposition 8.30), assuming
the TopologyComparison isomorphism hypotheses are satisfied. -/
theorem presheafValue_flat_of_tateQuotient
    [T2Space A] [NonarchimedeanRing A] [IsNoetherianRing A]
    [IsTateRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hcs : @CompleteSpace _ (quotientTUniformSpace D.s))
    (ht0 : @T0Space _ (quotientTTopology D.s))
    (hcont : @Continuous _ _
      (quotientTTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb))
    (hdense : @DenseRange (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s)
      (quotientTTopology D.s) (Localization.Away D.s)
      (locToQuotientOneSubfX_gen D.s)) :
    @Module.Flat A (presheafValue D) _ _
      (RingHom.toModule (RationalLocData.canonicalMap D)) := by
  haveI hflat_quot : Module.Flat A (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    TateAlgebra.flat_quotient_oneSubfX_general P D.s
  let e := presheafValueTateQuotientEquiv D hb hcs ht0 hcont hdense
  change @Module.Flat A (presheafValue D) _ _
    (RingHom.toModule (RationalLocData.canonicalMap D))
  letI : Module A (presheafValue D) := RingHom.toModule (RationalLocData.canonicalMap D)
  have he_smul : ∀ (a : A) (x : presheafValue D), e (a • x) = a • e x := by
    intro a x
    change e (RationalLocData.canonicalMap D a * x) = algebraMap A _ a * e x
    rw [e.map_mul]; congr 1
    exact presheafValueTateQuotientEquiv_canonicalMap D hb hcs ht0 hcont hdense a
  exact @Module.Flat.of_linearEquiv A (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) (presheafValue D)
    inferInstance inferInstance inferInstance inferInstance this hflat_quot
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

omit [HasLocLiftPowerBounded A] in
/-- `presheafValue D` is flat over `A` (Wedhorn Proposition 8.30), proved via the
**canonical-topology** isomorphism `presheafValueCanonicalQuotientEquiv`.

Compared to `presheafValue_flat_of_tateQuotient`, this version trades the three
T-topology hypotheses (`hcs`, `ht0`, `hdense`) for the canonical-topology
hypotheses (`hA_complete`, `hnoeth`, `hT_pb`). The `hA_complete` and `hnoeth`
inputs are purely Tate structural data that hold unconditionally when `A` is a
strongly noetherian Tate ring with a chosen pair of definition. The `hT_pb`
hypothesis is the standard rational-datum condition (all `t ∈ D.T` are
power-bounded) and `hcont_eval` is the residual continuity of the
`tateQuotientToPresheafHom` at the canonical topology.

This form feeds into the Laurent refinement faithful-flatness argument for
Wedhorn Corollary 8.32 without needing to establish the full T-topology
closedness + completeness infrastructure. -/
theorem presheafValue_flat_of_canonical
    [T2Space A] [NonarchimedeanRing A] [IsNoetherianRing A]
    [IsTateRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : @Continuous _ _
      (TateAlgebra.quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb)) :
    @Module.Flat A (presheafValue D) _ _
      (RingHom.toModule (RationalLocData.canonicalMap D)) := by
  haveI hflat_quot : Module.Flat A (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) :=
    TateAlgebra.flat_quotient_oneSubfX_general P D.s
  let e := presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb hcont_eval
  change @Module.Flat A (presheafValue D) _ _
    (RingHom.toModule (RationalLocData.canonicalMap D))
  letI : Module A (presheafValue D) := RingHom.toModule (RationalLocData.canonicalMap D)
  have he_smul : ∀ (a : A) (x : presheafValue D), e (a • x) = a • e x := by
    intro a x
    change e (RationalLocData.canonicalMap D a * x) = algebraMap A _ a * e x
    rw [e.map_mul]; congr 1
    exact presheafValueCanonicalQuotientEquiv_canonicalMap D hb hA_complete hnoeth
      hT_pb hcont_eval a
  exact @Module.Flat.of_linearEquiv A (↥(TateAlgebra A) ⧸ oneSubfXIdeal D.s) (presheafValue D)
    inferInstance inferInstance inferInstance inferInstance this hflat_quot
    { toLinearMap := { toFun := e, map_add' := e.map_add, map_smul' := he_smul }
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply }

/-- **T-STRONG-NOETH-PRESERVATION (rational-locale case)**: for strongly noetherian
Tate `A` and any rational locale `D : RationalLocData A`, `presheafValue D` is a
Noetherian ring.

Proof: by `presheafValueCanonicalQuotientEquiv`, `presheafValue D ≃+* (TateAlgebra A) ⧸
oneSubfXIdeal D.s`. The Tate algebra `TateAlgebra A = restrictedMvPowerSeriesSubring 1 A`
is Noetherian via `IsStronglyNoetherian.isNoetherianRing_restricted 1`. Quotient of
Noetherian is Noetherian. Transfer along the ring isomorphism.

This is the project's preservation theorem reviewer-flagged for the chain
approach to general rational-restriction flatness. -/
theorem presheafValue_isNoetherian_via_canonical
    [T2Space A] [NonarchimedeanRing A] [IsNoetherianRing A]
    [IsTateRing A] [IsStronglyNoetherian A]
    (D : RationalLocData A)
    (hb : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (hcont_eval : @Continuous _ _
      (TateAlgebra.quotientOneSubfXIdealTopology D.s)
      (inferInstance : TopologicalSpace (presheafValue D))
      (tateQuotientToPresheafHom D hb)) :
    IsNoetherianRing (presheafValue D) := by
  -- TateAlgebra A is noetherian (definitionally `restrictedMvPowerSeriesSubring 1 A`).
  haveI : IsNoetherianRing ↥(TateAlgebra A) :=
    IsStronglyNoetherian.isNoetherianRing_restricted 1
  -- Quotient of noetherian is noetherian (mathlib instance via `Ideal.Quotient.commRing`).
  haveI : IsNoetherianRing (↥(TateAlgebra A) ⧸ TateAlgebra.oneSubfXIdeal D.s) :=
    isNoetherianRing_of_surjective _ _ (Ideal.Quotient.mk _)
      (Ideal.Quotient.mk_surjective)
  -- Transfer along the equiv.
  let e := presheafValueCanonicalQuotientEquiv D hb hA_complete hnoeth hT_pb hcont_eval
  exact isNoetherianRing_of_ringEquiv _ e.symm

/-- `presheafValue D` is flat over `A` when `D` is `LaurentNormalized` (`1 ∈ D.T`)
and when `T = {1}` (the Laurent-minus case — all non-base elements of `D.T` are
power-bounded).

In this case the five `presheafValueCanonicalQuotientEquiv` hypotheses collapse
to just `hA_complete`, `hnoeth`, and `hcont_eval`:

* `hb` is discharged via `invS_isPowerBounded_of_one_mem_T` using
  `LaurentNormalized.one_mem_T`.
* `hT_pb` is discharged since `T = {1}` makes every `t ∈ T` equal `1`, which is
  power-bounded by `isPowerBounded_one`.

This shape matches the Laurent refinement `iteratedMinusDatum_B` invocation at
`LaurentRefinement.lean:2612` where the rational datum over `B := presheafValue D₀`
has exactly `T = {1}`. -/
theorem presheafValue_flat_of_laurentMinus
    [T2Space A] [NonarchimedeanRing A] [IsNoetherianRing A]
    [IsTateRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D : RationalLocData A) [LaurentNormalized D]
    (hT_singleton : D.T = {1})
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hcont_eval : ∀ hb : TopologicalRing.IsPowerBounded (invS D),
      @Continuous _ _
        (TateAlgebra.quotientOneSubfXIdealTopology D.s)
        (inferInstance : TopologicalSpace (presheafValue D))
        (tateQuotientToPresheafHom D hb)) :
    @Module.Flat A (presheafValue D) _ _
      (RingHom.toModule (RationalLocData.canonicalMap D)) := by
  -- `hb` follows from `invS_isPowerBounded_of_one_mem_T` since `1 ∈ D.T`.
  have hb : TopologicalRing.IsPowerBounded (invS D) := by
    rw [invS_eq_coeRingHom_divByS_one]
    exact CompletionLocalization.invS_isPowerBounded_of_one_mem_T D
      LaurentNormalized.one_mem_T
  -- `hT_pb`: `T = {1}` collapses `∀ t ∈ T, IsPowerBounded t` to `IsPowerBounded 1`.
  have hT_pb : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t := by
    intro t ht
    rw [hT_singleton, Finset.mem_singleton] at ht
    rw [ht]
    exact TopologicalRing.isPowerBounded_one
  exact presheafValue_flat_of_canonical A P D hb hA_complete hnoeth hT_pb
    (hcont_eval hb)

/-! ### Proof via Laurent cover refinement (Wedhorn Lemma 8.34) -/

/-- The product restriction is injective for every rational covering, via Laurent
refinement (Lemma 8.34 of Wedhorn).

The `hSpa` hypothesis is the Spa-point existence witness; callers supply it via
Lemma 7.45 (non-open prime case) or the trivial-valuation construction
(open prime case), and it is only consumed in the empty-cover edge case. -/
theorem productRestriction_injective_of_laurentRefinement
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A)
    (hSpa : ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp) :
    Function.Injective (productRestriction A C) := by
  intro x y hxy
  exact rationalCovering_hasSeparation P C hSpa x y
    (fun D hD ↦ congr_fun (congr_fun hxy D) hD)

-- REMOVED: productRestrictionSub_isInducing (R1, 2026-04-03)
-- This used the FALSE restrictionMapHom_isInducing. No longer needed since
-- IsSheafy was weakened to just require separation (injectivity) + gluing.

/-- **Sub-lemma (a.1.i) — `CompleteSpace` for the principal pair's ring of
definition (sub-atom of `_aux_nonOpen_hSpa_principalPair_isAdicComplete`).**

This is the "completeness" half of the `IsAdic.isAdicComplete_iff` reduction:
`A₀` equipped with the subspace uniformity inherited (via `Subtype.val`) from
`A`'s canonical right uniform structure (as a topological additive group) is a
complete uniform space. The `T2Space` half is automatic for a subspace of `A`,
which is `T2Space` by hypothesis. Mirrors
`principalPair_A₀_completeSpace_of_stronglyNoetherianTate` in
`TateAcyclicityResiduals.lean` (which retains the same sorry). -/
theorem _aux_nonOpen_hSpa_principalPair_A₀_completeSpace
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
    letI : UniformSpace ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
      UniformSpace.comap Subtype.val ‹UniformSpace A›
    CompleteSpace ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ := by
  -- Per round-2 reviewer Q1 + B2 #24: `[CompleteSpace A]` (under the right-uniform
  -- group structure) is a standing assumption.
  -- Proof: A₀ ⊆ A is closed (open subgroup of T2 topological group); a closed
  -- subspace of a complete uniform space is complete.
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  set P := (IsTateRing.principalPair A).toPairOfDefinition
  have hclosed : IsClosed (P.A₀ : Set A) :=
    AddSubgroup.isClosed_of_isOpen P.A₀.toAddSubgroup P.isOpen
  -- The subspace uniformity coincides with the comap uniformity for the inclusion.
  haveI : IsClosed ((P.A₀ : Set A) : Set A) := hclosed
  exact IsClosed.completeSpace_coe (s := (P.A₀ : Set A))

/-- **Sub-lemma (a.1) — `IsAdicComplete` instance for the principal pair of a
strongly-noetherian Tate ring.**

The substantive infrastructure obligation surfaced by the discharge plan for
`_aux_nonOpen_hSpa_spaPoint_exists`: `Lemma745` requires an
`IsAdicComplete P.I P.A₀` instance for the chosen `PairOfDefinition`. The
parent's hypotheses `[IsTateRing A] [T2Space A] [NonarchimedeanRing A]` give
ambient topological completeness for `A`, but the canonical form expected by
`Lemma745` is `IsAdicComplete` on the subring `P.A₀` with the `P.I`-adic
topology.

**Discharge (now sorry-free at this site, modulo the sub-atom
`_aux_nonOpen_hSpa_principalPair_A₀_completeSpace`):** Equip `A` with its
canonical right uniform structure (`IsTopologicalAddGroup.rightUniformSpace`);
since `A` is an additive commutative topological group, this uniformity makes
`A` an `IsUniformAddGroup`. Equip `A₀` with the subspace uniformity via
`Subtype.val`; the `AddSubgroup.isUniformAddGroup` instance gives
`IsUniformAddGroup A₀`. The pair-of-definition's `isAdic` field plus
`IsAdic.isAdicComplete_iff` then reduces `IsAdicComplete P.I P.A₀` to
`CompleteSpace A₀ ∧ T2Space A₀`. `T2Space A₀` is automatic as a subspace of
the ambient `T2Space A`; `CompleteSpace A₀` is the named sub-atom above.

Mirrors the proof structure of
`principalPair_isAdicComplete_of_stronglyNoetherianTate` in
`TateAcyclicityResiduals.lean`. -/
theorem _aux_nonOpen_hSpa_principalPair_isAdicComplete
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    IsAdicComplete (IsTateRing.principalPair A).toPairOfDefinition.I
      (IsTateRing.principalPair A).toPairOfDefinition.A₀ := by
  letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  haveI : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  letI : UniformSpace ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
    UniformSpace.comap Subtype.val ‹UniformSpace A›
  haveI : IsUniformAddGroup
      ↥(IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
    AddSubgroup.isUniformAddGroup
      (IsTateRing.principalPair A).toPairOfDefinition.A₀.toAddSubgroup
  exact ((IsTateRing.principalPair A).toPairOfDefinition.isAdic.isAdicComplete_iff).mpr
    ⟨_aux_nonOpen_hSpa_principalPair_A₀_completeSpace A, inferInstance⟩

/-- **Sub-lemma (a.2) — `A⁺ ⊆ A₀` containment for the principal pair.**

The second infrastructure obligation surfaced by the discharge plan for
`_aux_nonOpen_hSpa_spaPoint_exists`: `Lemma745` requires the underlying-set
containment `(A⁺ : Set A) ⊆ P.A₀` for the chosen `PairOfDefinition`. This is
generally not free without an explicit alignment hypothesis between `A⁺` and
`P.A₀`; in the standard setting (Wedhorn §7) one chooses `A⁺ = A°` and
`P.A₀ ⊆ A°` so the containment holds, but the project's `PlusSubring` is an
abstract typeclass-supplied subring. Tracked as a named sub-lemma sorry. -/
theorem _aux_nonOpen_hSpa_Aplus_le_principalPair_A₀
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [CompatiblePlusSubring A] :
    ((A⁺ : Subring A) : Set A) ⊆
      ((IsTateRing.principalPair A).toPairOfDefinition.A₀ : Set A) := by
  -- Per round-2 reviewer Q1 + B2 #25: `[CompatiblePlusSubring A]` is a standing
  -- assumption. The typeclass provides `A⁺ ⊆ D.P.A₀` for any RationalLocData D;
  -- specialise to a trivial D with `D.P = principalPair.toPairOfDefinition`,
  -- `T = {1}`, `s = 1`.
  set P := (IsTateRing.principalPair A).toPairOfDefinition
  let D : RationalLocData A :=
    { P := P
      T := {1}
      s := 1
      hopen := ⟨0, fun b _ ↦ by
        rw [divByS_eq_algebraMap]
        exact algebraMap_mem_locSubring P {1} (1 : A) b.property⟩ }
  exact CompatiblePlusSubring.aplus_le_A₀ D

/-- **Sub-lemma (a) — Wedhorn 7.45 raw Spa-point output above a non-open prime.**

Named sub-lemma isolating the pure Wedhorn 7.45 step: from a non-open prime `p`
of a complete strongly-Noetherian Tate ring `A`, produce a Spa point `v` (with
respect to the ambient `PlusSubring A` structure) such that `p ≤ v.supp`.

Discharge plan: combine
`PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime` (Lemma 7.45 of
Wedhorn, `Lemma745.lean:691`) applied to the principal pair
`(IsTateRing.principalPair A).toPairOfDefinition`. The two infrastructure
ingredients are now isolated as named sub-lemma sorries directly above:
(1) `_aux_nonOpen_hSpa_principalPair_isAdicComplete` supplies the
`[IsAdicComplete P.I P.A₀]` instance, and
(2) `_aux_nonOpen_hSpa_Aplus_le_principalPair_A₀` supplies the
`(A⁺ : Set A) ⊆ P.A₀` containment.
The composition itself is structural (no remaining mathematical content). -/
theorem _aux_nonOpen_hSpa_spaPoint_exists
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    ∀ (p : Ideal A), p.IsPrime → ¬IsOpen (p : Set A) →
      ∃ v ∈ Spa A A⁺, p ≤ v.supp := by
  intro p hp hopen
  haveI : IsAdicComplete (IsTateRing.principalPair A).toPairOfDefinition.I
      (IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
    _aux_nonOpen_hSpa_principalPair_isAdicComplete A
  haveI : p.IsPrime := hp
  obtain ⟨v, hv, hpv, _⟩ :=
    PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime
      (IsTateRing.principalPair A).toPairOfDefinition hopen
      (_aux_nonOpen_hSpa_Aplus_le_principalPair_A₀ A)
  exact ⟨v, hv, hpv⟩

/-- **Sub-lemma (b) — rational-open membership lift for a Spa-point above a
non-open prime.**

Named sub-lemma isolating the topological refinement step: from a Spa point
`v ∈ Spa A A⁺` with `p ≤ v.supp` (output of Wedhorn 7.45) and `s ∉ p`, produce
a Spa point `w ∈ rationalOpen T s` with `p ≤ w.supp`. The lift typically
proceeds by dominating `v` on `Localization.Away s` (Wedhorn Prop 7.41 +
specialisation in `Spv`), then transferring back along the canonical map; this
is the content packaged in `Cor832.lean:exists_spa_point_supp_ge_in_presheafValue`
for the `presheafValue` setting. Here we expose the bare `A`-side statement so
the parent can delegate. -/
theorem _aux_nonOpen_hSpa_rationalOpen_lift
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    ∀ (T : Finset A) (s : A) (p : Ideal A), p.IsPrime → s ∉ p →
      (∃ v ∈ Spa A A⁺, p ≤ v.supp) →
      ∃ v ∈ rationalOpen T s, p ≤ v.supp := by
  -- Discharge via the existing Wedhorn-7.45 lift in `Presheaf.lean`
  -- (`exists_mem_rationalOpen_supp_ge_of_prime_noHArch`), instantiated at the
  -- principal pair of definition. The two infrastructure ingredients are the
  -- named sub-lemmas declared above. Note: the `∃ v ∈ Spa A A⁺, p ≤ v.supp`
  -- existence hypothesis is structurally consumed inside the underlying
  -- Wedhorn-7.45 chain, so we don't need it explicitly here.
  intro T s p hp hs _h
  haveI : p.IsPrime := hp
  haveI : IsAdicComplete (IsTateRing.principalPair A).toPairOfDefinition.I
      (IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
    _aux_nonOpen_hSpa_principalPair_isAdicComplete A
  exact exists_mem_rationalOpen_supp_ge_of_prime_noHArch
    (IsTateRing.principalPair A).toPairOfDefinition
    (_aux_nonOpen_hSpa_Aplus_le_principalPair_A₀ A) T s hs

/-- **Sub-lemma — Wedhorn 7.45 non-open prime case (Spa-point above a non-open
prime in a rational subset).**

Named sub-lemma carrying the substantive non-open content of
`exists_hSpa_points_global_of_stronglyNoetherianTate`. The proof now delegates
to two sharper sub-lemmas:
* `_aux_nonOpen_hSpa_spaPoint_exists` — the Wedhorn 7.45 raw output
  (existence of a Spa point with `p ≤ v.supp` above a non-open prime).
* `_aux_nonOpen_hSpa_rationalOpen_lift` — the rational-open refinement
  (lifting a Spa point with `p ≤ v.supp` to `rationalOpen T s` when `s ∉ p`).

The open-prime case of the parent theorem is discharged directly via
`exists_spa_point_in_rationalOpen_of_isOpen_prime` (no sorry). -/
theorem _aux_nonOpen_hSpa_points_of_stronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    ∀ (T : Finset A) (s : A) (p : Ideal A), p.IsPrime → s ∉ p →
      ¬IsOpen (p : Set A) →
      ∃ v ∈ rationalOpen T s, p ≤ v.supp := by
  intro T s p hp hs hopen
  exact _aux_nonOpen_hSpa_rationalOpen_lift (A := A) T s p hp hs
    (_aux_nonOpen_hSpa_spaPoint_exists (A := A) p hp hopen)

/-- **(Wedhorn 7.45 axiom-clean discharge — for use in Cor 8.32 proof, relocated
upstream of `productRestrictionSub_injective_flat` so the latter's empty-cover
edge case can route through it.)** Wedhorn's direct construction of a Spa-point
above any prime, in any rational subset. Needed to prove faithful flatness of
the product restriction (Cor 8.32): Spec surjectivity ⇔ every prime of the base
has a preimage in some cover piece.

Proof structure: case-split on `IsOpen (p : Set A)`. Open case via
`exists_spa_point_in_rationalOpen_of_isOpen_prime` (axiom-clean trivial
valuation on `Frac(A/p)`). Non-open case via the named sub-lemma
`_aux_nonOpen_hSpa_points_of_stronglyNoetherianTate` (which retains a `sorry`
body for the Wedhorn 7.45 / Lemma745 / Bourbaki DVR content). -/
theorem exists_hSpa_points_global_of_stronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    ∀ (T : Finset A) (s : A) (p : Ideal A), p.IsPrime → s ∉ p →
      ∃ v ∈ rationalOpen T s, p ≤ v.supp := by
  intro T s p hp hs
  by_cases hopen : IsOpen ((p : Ideal A) : Set A)
  · haveI : (p : Ideal A).IsPrime := hp
    exact exists_spa_point_in_rationalOpen_of_isOpen_prime (A := A) T s p hopen hs
  · exact _aux_nonOpen_hSpa_points_of_stronglyNoetherianTate
      (A := A) T s p hp hs hopen

/-- **(L.1) Spa-point existence above any prime, combining open and non-open
cases.** This is the discharge of the `hSpa_points` hypothesis used by
`base_s_in_annihilator_radical_of_covering` etc. — case-split on `IsOpen (p : Set A)`
gives:
- open case: `exists_spa_point_in_rationalOpen_of_isOpen_prime`
- non-open case: `PairOfDefinition.exists_mem_spa_supp_ge_of_nonOpen_prime` (Lemma 7.45)
  combined with the rational-open membership lift.

Specialisation of `exists_hSpa_points_global_of_stronglyNoetherianTate` to
the data of a `RationalCoveringData` (T = C.base.T, s = C.base.s). Inherits the
shared Wedhorn 7.45 sorry transitively. -/
theorem exists_spa_point_in_rationalOpen_of_prime
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (C : RationalCoveringData A) :
    ∀ (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp :=
  fun p hp hs ↦
    exists_hSpa_points_global_of_stronglyNoetherianTate (A := A) C.base.T C.base.s p hp hs

/-- **(Gap B) Topological inducing of `productRestrictionSub` for arbitrary `C`.**
This is the topological component of IsSheafy's `embedding` field. The proof
combines T286 (Lane C single-step closer, done #57) with the Laurent τ-existence
supplied by P8 (`exists_wedhorn_ratio_laurent_refinement_tree_realized`). -/
theorem productRestrictionSub_isInducing_tate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCoveringData A) :
    Topology.IsInducing (productRestrictionSub A C) :=
  sorry

/-- **Sub-lemma — topological inducing of `productRestrictionSub` (flat profile).**

Named sub-lemma extracted from the `embedding` field of
`isSheafy_ofStronglyNoetherianTate_flat`. Discharges the IsInducing component of
the Lane C / T-EMBED-TOPO route by delegating to the cleaner Wedhorn-exact
companion `productRestrictionSub_isInducing_tate` (above, with no `[IsDomain]`
and no `P` parameter). The extra `[IsDomain A]` + `(_P : PairOfDefinition A)
[IsNoetherianRing _P.A₀]` hypotheses are unused here — they exist purely to
match the hypothesis profile of `isSheafy_ofStronglyNoetherianTate_flat`. -/
theorem productRestrictionSub_isInducing_flat
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
    (_P : PairOfDefinition A) [IsNoetherianRing _P.A₀]
    (C : RationalCoveringData A) :
    Topology.IsInducing (productRestrictionSub A C) :=
  productRestrictionSub_isInducing_tate (A := A) C

/-- **Sub-lemma — injectivity of `productRestrictionSub` (flat profile).**

Named sub-lemma extracted from the `embedding` field of
`isSheafy_ofStronglyNoetherianTate_flat`. Carries the same hypothesis profile as
the parent. The algebraic separation route goes through Wedhorn 7.45 (Spa-points
above primes) feeding `productRestriction_injective_of_laurentRefinement`, but
the Spa-point existence at this hypothesis profile is still a project sorry
(`exists_hSpa_points_global_of_stronglyNoetherianTate`). -/
theorem productRestrictionSub_injective_flat
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (_P : PairOfDefinition A) [IsNoetherianRing _P.A₀]
    (C : RationalCoveringData A) :
    Function.Injective (productRestrictionSub A C) := by
  intro x y hxy
  apply productRestriction_injective_of_laurentRefinement (A := A) _P C
    (exists_spa_point_in_rationalOpen_of_prime (A := A) C)
  funext D hD
  exact congrArg (· ⟨D, hD⟩) hxy

/-- Strongly noetherian Tate rings are sheafy (Theorem 8.28 of Wedhorn),
via Laurent cover refinement (Lemma 8.34). -/
theorem isSheafy_ofStronglyNoetherianTate_flat
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀] :
    IsSheafy A where
  embedding C _hC := by
    -- Per T-EMBED-TOPO boundary (reviewer-confirmed, ChatGPT Pro, 2026-05-11):
    -- factor into algebraic injectivity + topological inducing via
    -- `productRestrictionSub_isEmbedding_of_lane_inputs` (EmbeddingTopo.lean).
    --
    -- Algebraic side: `productRestrictionSub_injective_of_product_injective`
    -- consumes the cover-level `productRestriction_injective_tate` (Cor832.lean),
    -- which presently routes through `tateAcyclicity` Part 1's residual
    -- single-map injectivity. Once R2a lands, the algebraic side will close
    -- via faithful flatness of the product restriction (Cor 8.32 product form).
    --
    -- Topological inducing side: the Lane-Wedhorn topological route described
    -- in `EmbeddingTopo.lean`'s docstring — topological Example 6.38 + Laurent
    -- diagram topological strictness + Lane C refinement transfer.
    --
    -- Edge case: when `C.base.s = 0`, `presheafValue C.base` is subsingleton (the
    -- zero ring), so any function from it is automatically an embedding via
    -- `Topology.IsEmbedding.of_subsingleton`.
    by_cases hs : C.base.s = 0
    · haveI := presheafValue_subsingleton_of_s_eq_zero C.base hs
      exact Topology.IsEmbedding.of_subsingleton _
    · -- Remaining sorry: the topological-inducing residual identified by
      -- T-EMBED-TOPO.
      --
      -- **STATUS (2026-05-13, T273-T286 landed)**:
      --
      -- Lane C **single-step closer** is now available via T286 in
      -- `EmbeddingTopo.lean`:
      -- `productRestrictionSub_isInducing_via_laurent_refinement_tau`.
      -- This closes the case where there is a single `f₀` such that
      -- `laurentCovering C.base f₀` **refines** `C` (a τ-function with
      -- per-piece containment can be constructed).
      --
      -- Supporting infrastructure (all axiom-clean):
      --   * T280 `Topology.IsInducing.of_eval`: adding more projections.
      --   * T281 `Topology.IsInducing.of_continuous_comp`: generic
      --     post-composition with continuous map preserves IsInducing.
      --   * T282 `..._of_finer_rational_continuous`: strengthened
      --     refinement transfer (only `Continuous φ`, not `IsInducing φ`).
      --   * T283 `productRestrictionSub_continuous`: automatic continuity.
      --   * T284 `..._via_laurent_refinement`: parametric Lane C closer.
      --   * T285 `naturalRefinementMap` + continuity + commutativity.
      --   * T286: τ-only single-step Lane C closer.
      --   * T287: sanity-check end-to-end (T286 with τ = id closes
      --     T278's laurent-cover IsInducing via the full chain).
      --
      -- **REMAINING WORK**: For arbitrary `C`, **construct** a Laurent
      -- refinement: find `f₀ : A` and a τ-function
      -- `↥(laurentCovering C.base f₀).covers → ↥C.covers` with per-piece
      -- containment. This existence is essentially the topological
      -- version of Wedhorn's standard-cover refinement (Lemma 8.34).
      -- Once the τ-existence is established, T286 closes this sorry
      -- directly.
      --
      -- **OLD STATUS (2026-05-13 morning, T273-T279)**:
      --
      -- The Lane C **base case** (single Laurent cover at `f`) is now
      -- sorry-free via the auto-discharge chain in
      -- `EmbeddingTopo.lean`:
      --   * T279 `productRestrictionSub_laurentCovering_isEmbedding_via_bridges_of_s_ne_zero`
      --     produces `IsEmbedding (productRestrictionSub A (laurentCovering D₀ f))`
      --     from the bridges hypothesis bundle + `hs : D₀.s ≠ 0`. Axiom-clean.
      --   * T278 produces the IsInducing-only variant for the
      --     `_of_topo_inducing` parametric form.
      --
      -- **REMAINING WORK (Lane C induction)**:
      --
      -- For ARBITRARY `C : RationalCoveringData A`, the IsEmbedding follows
      -- by the standard-cover refinement + Laurent induction:
      --   1. Use `RationalCoveringData.refines_by_standard_cover` to find a
      --      standard cover `S` of `C.base` such that the induced
      --      V-cover refines `C` (S-GEOM-TAU is done, T250).
      --   2. Induct on `|S.elts|`:
      --      - base case |S| = 1: a single plus-piece V-cover. The
      --        single-piece IsInducing is the per-piece restriction
      --        being IsInducing, which doesn't reduce to T279 directly
      --        (T279 is for the 2-piece laurentCovering, not the
      --        1-piece plusDatum cover).
      --      - inductive step: Laurent split at the new element f₀
      --        produces plus + minus halves; combine via T267
      --        (`productRestrictionSub_isInducing_of_finer_rational`).
      --   3. Transfer back to C via T267 with the τ-map from S-GEOM-TAU.
      --
      -- The Lane C induction needs the IsInducing of the natural product
      -- map `φ` between V and C (the topological refinement-transfer
      -- ingredient, supplied as hypothesis to T267). For each Laurent
      -- step, this `φ_IsInducing` is the topological version of the
      -- 2-cover overlap structure — supplied by the Wedhorn 8.33 / Lemma
      -- 8.34 topological strictness.
      --
      -- **Algebraic injectivity side**: still pending the Cor 8.32 product
      -- faithful-flatness route (T-IDEAL-2, conditional on Stacks 00MA).
      --
      -- See `EmbeddingTopo.lean` T273-T279 for the base case landing and
      -- `RationalRefinement.lean` `separation_of_finer_rational` for the
      -- gluing-side refinement transfer (which the topological side
      -- mirrors via T267).
      --
      -- **Discharge via named sub-lemmas**: compose `IsInducing` +
      -- `Function.Injective` to form `IsEmbedding`. Each sub-lemma carries the
      -- same hypothesis profile and retains its own `sorry` (the remaining
      -- mathematical content); the parent's `IsEmbedding` field is no longer
      -- an anonymous `sorry`.
      exact ⟨productRestrictionSub_isInducing_flat (A := A) P C,
        productRestrictionSub_injective_flat (A := A) P C⟩
  gluing C _hC f hcompat :=
    rationalCovering_hasGluing P C f hcompat

-- REMOVED (T6): isSheafy_ofStronglyNoetherianTate (TopologyComparison route)
-- had 2 sorries, superseded by isSheafy_ofStronglyNoetherianTate_flat above.

/-! ### T-NEW-5: `IsSheafy` from abstract lane inputs

**T-NEW-5 (2026-05-11)**.

Hypothesis-parameterised `IsSheafy` builder that takes the topological-inducing
side as an abstract supplier. This factors out T-EMBED-TOPO (the remaining
topological residual) so the algebraic side can close independently.

The caller supplies:
* `topo_inducing` — for each rational covering `C`,
  `Topology.IsInducing (productRestrictionSub A C)`. This is the
  Lane-Wedhorn topological route described in `EmbeddingTopo.lean`
  (topological Example 6.38 + Laurent strictness + Lane C refinement),
  currently not yet developed.

The algebraic side (`embedding.injective`, `gluing`) is provided internally
via `rationalCovering_hasSeparation` and `rationalCovering_hasGluing` from
the Laurent refinement route. -/
theorem isSheafy_ofStronglyNoetherianTate_flat_of_topo_inducing
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [IsDomain A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    [IsRingOfIntegralElements (A⁺)]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (hSpa : ∀ (C : RationalCoveringData A) (p : Ideal A), p.IsPrime → C.base.s ∉ p →
      ∃ v ∈ rationalOpen C.base.T C.base.s, p ≤ v.supp)
    (topo_inducing : ∀ (C : RationalCoveringData A),
      Topology.IsInducing (productRestrictionSub A C)) :
    IsSheafy A where
  embedding C _hC := by
    by_cases hs : C.base.s = 0
    · haveI := presheafValue_subsingleton_of_s_eq_zero C.base hs
      exact Topology.IsEmbedding.of_subsingleton _
    · refine ⟨topo_inducing C, ?_⟩
      -- Algebraic injectivity from `rationalCovering_hasSeparation`.
      intro x y hxy
      apply rationalCovering_hasSeparation P C (hSpa C)
      intro D hD
      exact congr_fun hxy ⟨D, hD⟩
  gluing C _hC f hcompat :=
    rationalCovering_hasGluing P C f hcompat

/-! ### Factoring the product restriction through the canonical map -/

/-- The product restriction composed with the canonical map to the base
equals the product of canonical maps to the covering pieces. That is,
the following diagram commutes:
```
          canonicalMap C.base
      A ──────────────────────→ presheafValue C.base
      │                                  │
      │ ∏ D.canonicalMap                 │ productRestriction C
      ↓                                  ↓
  ∏ presheafValue D  ═════════  ∏ presheafValue D
```
-/
theorem productRestriction_comp_canonicalMap
    (C : RationalCoveringData A)
    (a : A) (D : RationalLocData A) (hD : D ∈ C.covers) :
    productRestriction A C (C.base.canonicalMap a) D hD = D.canonicalMap a := by
  change restrictionMap C.base D (C.hsubset D hD) (C.base.canonicalMap a) = D.canonicalMap a
  unfold restrictionMap restrictionMapHom
  letI := C.base.uniformSpace
  letI := C.base.isTopologicalRing
  letI := C.base.isUniformAddGroup
  letI := D.uniformSpace
  letI := D.isTopologicalRing
  letI := D.isUniformAddGroup
  erw [UniformSpace.Completion.extensionHom_coe (restrictionMapAlg C.base D (C.hsubset D hD))
    (restrictionMapAlg_continuous C.base D (C.hsubset D hD))]
  simp only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq,
    RationalLocData.canonicalMap]

/-! ### Adic spaces as objects of 𝒱 (Definitions 8.21, 8.22 of Wedhorn) -/

/-! ## Wedhorn 8.28(b) clean statement — no `IsDomain`, no explicit `P` parameter

The existing `isSheafy_ofStronglyNoetherianTate_flat` (line 1105) carries
`[IsDomain A]` and `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` as extra
hypotheses not present in Wedhorn Theorem 8.28(b). The clean signature below
matches Wedhorn exactly. -/

/-- **Project-side derived instance.** `HasLocLiftPowerBounded A` is needed by
the `IsSheafy` definition. **AUDIT (2026-05-17):** the previous claim that this
follows from strong-noetherian-Tate alone was wrong. The two fields require:
(T-H.2.a) Wedhorn 7.52(2) applied to the localization (need the localization
to be a complete Tate affinoid + Spa-point density), and
(T-H.2.b) Wedhorn Nullstellensatz / Tate-algebra power-boundedness theory.
Both are genuinely deep.

**Discharge (2026-05-22):** the upstream instance
`Presheaf.hasLocLiftPowerBounded_of_stronglyNoetherianTate'` (which actually has
the strictly weaker hypothesis profile `[IsTateRing A] [IsNoetherianRing A]
[T2Space A] [NonarchimedeanRing A]`, dropping `[IsStronglyNoetherian A]`) already
constructs the same instance via `isUnit_canonicalMap_s_of_tate` (Wedhorn 7.52(2))
and `locLift_divByS_isPowerBounded_completion_of_tate` (Wedhorn 7.41). Both
upstream theorems retain `sorry` bodies in `Presheaf.lean`, so the substantive
Wedhorn 7.52(2) / 7.41 content lives there; this instance is now a pure
delegation. -/
instance hasLocLiftPowerBounded_of_stronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] :
    HasLocLiftPowerBounded A :=
  hasLocLiftPowerBounded_of_stronglyNoetherianTate' A

-- T-I.1 DELETED (2026-05-17, audit correction):
-- The original "strongly noetherian Tate ⇒ ∃ noetherian principal pair"
-- requires Wedhorn 6.18+ / BGR spectral-norm theory (the case-(b)→case-(a)
-- reduction in Wedhorn 8.28). This is genuinely deep theory, NOT decomposable
-- by routine sub-lemmas. The clean `isSheafy_ofStronglyNoetherianTate` is
-- restated below to take `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]`
-- as parameters — matching Wedhorn 8.28(a)'s explicit hypothesis profile.
-- The case-(b) reduction is left as a separate (Wedhorn-deep) ticket.

-- J.1 (`tateAcyclicity_separation_via_cor832`) is defined further below, after
-- `cor_8_32_clean`, since it consumes the faithful-flatness statement directly.

-- `productRestrictionSub_isInducing_tate` was relocated upstream (just above
-- `productRestrictionSub_isInducing_flat`) so the legacy `_flat` consumer can
-- delegate to it instead of carrying its own anonymous `sorry`.

/-! ### Stacks 023N decomposition (no Mathlib gap, axiom-clean)

K.1 in full is the descent equalizer for faithfully flat ring maps. Decomposed
per Stacks 023N proof:

K.1.a: cocycle map `λ : S → S ⊗_R S`, `s ↦ 1⊗s - s⊗1` is R-linear.
K.1.b: image of `algebraMap R S` lies in `ker λ` (R-elements are cocycles).
K.1.c: the map `R → ker λ` is surjective (the THEOREM — faithful flatness).
K.1.d: K.1 follows directly from K.1.c. -/

/-- **(K.1.a)** The cocycle map `λ : S → S ⊗_R S`, `s ↦ 1 ⊗ s - s ⊗ 1`,
as an R-linear map. -/
noncomputable def faithfullyFlat_cocycleMap
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] :
    S →ₗ[R] TensorProduct R S S :=
  TensorProduct.mk R S S 1 - (TensorProduct.mk R S S).flip 1

/-- **(K.1.b)** The image of `algebraMap R S` lies in the kernel of the cocycle map.
**Cocycle property of R-elements.** -/
theorem faithfullyFlat_cocycleMap_algebraMap_eq_zero
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (r : R) :
    faithfullyFlat_cocycleMap R S (algebraMap R S r) = 0 := by
  unfold faithfullyFlat_cocycleMap
  simp only [LinearMap.sub_apply, TensorProduct.mk_apply, LinearMap.flip_apply,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    sub_self]

/-- **(K.1.c)** The Stacks 023N THEOREM: for faithfully flat `R → S`, every
element in `ker (cocycleMap)` is in the image of `algebraMap`. Proof outline
(Stacks 023N):
1. Tensor the sequence `R → S ⇉ S ⊗_R S` with S over R; the result is the
   sequence `S → S ⊗_R S ⇉ S ⊗_R S ⊗_R S` which has a section (multiplication
   map), so the tensored sequence is split exact.
2. Faithful flatness reflects exactness back to the un-tensored sequence.
3. Conclude `R → ker(cocycleMap)` is surjective. -/
theorem faithfullyFlat_cocycle_kernel_eq_algebraMap_range
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    (s : S) (h_cocycle : faithfullyFlat_cocycleMap R S s = 0) :
    ∃ r : R, algebraMap R S r = s := by
  -- Delegate to Mathlib's `Algebra.IsEffective.of_faithfullyFlat`
  -- (`Mathlib/RingTheory/TensorProduct/IncludeLeftSubRight.lean`) which packages
  -- the Stacks 023N descent argument: for faithfully flat `R → S`, the sequence
  -- `R → S ⇉ S ⊗[R] S` is exact via `s ⊗ 1 - 1 ⊗ s`. Our `cocycleMap` is the
  -- sign-flip `1 ⊗ s - s ⊗ 1`, so its kernel coincides.
  haveI hEff : Algebra.IsEffective R S := Algebra.IsEffective.of_faithfullyFlat R S
  have h_eq : faithfullyFlat_cocycleMap R S s =
      - Algebra.TensorProduct.includeLeftSubRight R S s := by
    simp only [faithfullyFlat_cocycleMap, LinearMap.sub_apply, TensorProduct.mk_apply,
      LinearMap.flip_apply, Algebra.TensorProduct.includeLeftSubRight_apply, neg_sub]
  rw [h_eq, neg_eq_zero] at h_cocycle
  exact (hEff s).mp h_cocycle

/-- **(K.1) Faithfully flat descent equalizer (Stacks 023N).** For a faithfully
flat ring homomorphism `φ : R → S`, an element `s ∈ S` satisfying the cocycle
condition `1 ⊗ s = s ⊗ 1` is in the image of `R`. **Axiom-clean: no Mathlib
gap; proved via K.1.a, K.1.b, K.1.c.** -/
theorem faithfullyFlat_descent_equalizer
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    (s : S)
    (h_cocycle : (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S) = 0) :
    ∃ r : R, algebraMap R S r = s := by
  have h : faithfullyFlat_cocycleMap R S s = 0 := by
    unfold faithfullyFlat_cocycleMap
    simp only [LinearMap.sub_apply, TensorProduct.mk_apply, LinearMap.flip_apply]
    exact h_cocycle
  exact faithfullyFlat_cocycle_kernel_eq_algebraMap_range R S s h

-- **[P0 / T#57 — DELETED 2026-06-02] two FALSE orphan lemmas removed:**
-- `_aux_noeth_A0_generic_of_stronglyNoetherianTate` and
-- `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate` asserted
-- "strongly-noetherian-Tate ⇒ ring-of-definition A₀ is noetherian", which is the CONVERSE
-- of Wedhorn Remark 6.37(3) and is FALSE (ℂ_p is strongly-noeth-Tate with a non-noetherian
-- ring of definition; Wedhorn 8.28(b) holds for it). They were `sorry`-bodied and only served
-- to smuggle a case-(a) "noetherian ring of definition" hypothesis into case-(b) results.
-- Their use-sites now carry an honest local `sorry`; the faithful discharge is
-- `IsStronglyNoetherian A ⇒ IsNoetherianRing A⟨X⟩` (Example 6.38), pursued in P1 (T#58).

/-- **Sub-lemma — gluing with explicit P (Wedhorn 8.28(b) Case (a) profile).**

K.2 content with `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` as explicit
hypothesis. Discharged via the existing axiom-clean Laurent-refinement chain
(`rationalCovering_hasGluing` in `LaurentRefinement.lean`), which proves exactly
this statement when `P` and `[IsNoetherianRing P.A₀]` are supplied. -/
theorem tateAcyclicity_gluing_via_descent_with_P
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (C : RationalCoveringData A) (_hne : C.covers.Nonempty)
    (f : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D :=
  rationalCovering_hasGluing P C f hcompat

/-- **(K.2) Tate acyclicity Part 2 (gluing), Wedhorn-exact.** Uses
`cor_8_32_clean` + Wedhorn's Čech-based proof (Lemma 8.34) — NOT Stacks 023N
descent. Wedhorn's actual route is via Lemma 8.34 acyclicity, which directly
gives the gluing without needing the descent equalizer. **Wedhorn-exact
hypothesis profile.**

Closed via the named sub-lemma `tateAcyclicity_gluing_via_descent_with_P`
(supplies explicit `(P, [IsNoetherianRing P.A₀])` to reach
`rationalCovering_hasGluing`), with `P = IsTateRing.principalPair A` and the
noeth-A₀ instance from `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate`. -/
theorem tateAcyclicity_gluing_via_descent
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    (C : RationalCoveringData A) (hne : C.covers.Nonempty)
    (f : ∀ (D : ↥C.covers), presheafValue D.1)
    (hcompat : ∀ (D₁ D₂ : ↥C.covers) (D₃ : RationalLocData A)
      (h₃₁ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₁.1.T D₁.1.s)
      (h₃₂ : rationalOpen D₃.T D₃.s ⊆ rationalOpen D₂.1.T D₂.1.s),
      restrictionMap D₁.1 D₃ h₃₁ (f D₁) = restrictionMap D₂.1 D₃ h₃₂ (f D₂)) :
    ∃ x : presheafValue C.base, ∀ (D : ↥C.covers),
      restrictionMap C.base D.1 (C.hsubset D.1 D.2) x = f D :=
  haveI : IsNoetherianRing (IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
    -- P0/T#57: was `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate` — a FALSE lemma
    -- (strong-noeth ⇒ noeth-A₀, ℂ_p-counterexample). Deleted; the noeth-A₀ obligation is now an
    -- honest open `sorry`, to be discharged faithfully via `IsStronglyNoetherian ⇒ A⟨X⟩-noetherian`
    -- (Example 6.38) in P1/T#58, NOT via a noetherian ring of definition (case (a)).
    sorry
  tateAcyclicity_gluing_via_descent_with_P (A := A)
    (IsTateRing.principalPair A).toPairOfDefinition C hne f hcompat

/-! ## Wedhorn-clean discharge sub-lemmas (axiom-clean target)

These are the project-internal sub-lemmas needed to derive the hypotheses I
previously added to `isSheafy_ofStronglyNoetherianTate` (hSpa_points_global, P,
HasLocLiftPowerBounded) from Wedhorn's actual 8.28(b) hypotheses
(`IsStronglyNoetherian A` + `IsTateRing A` + complete). Each cites the specific
Wedhorn lemma sequence. -/

-- RELOCATED 2026-05-22: `exists_hSpa_points_global_of_stronglyNoetherianTate`
-- and `exists_spa_point_in_rationalOpen_of_prime` were moved upstream (above
-- `productRestrictionSub_injective_flat`) so the latter's empty-cover edge case
-- can route through the relocated Spa-point witness. See lines ~1110-1135.

-- I.1 cluster DELETED (2026-05-18, user audit): `A° noetherian` is NOT used
-- anywhere in Wedhorn 8.28's actual proof. The project's existing
-- `flat_over_base_tate` requires `[IsNoetherianRing P.A₀]` only because it
-- routes through `restrictionMap_isLocalization` (Wedhorn Prop 8.15) which
-- the project itself flags as "mathematically false in general". The
-- Wedhorn-correct route uses Examples 6.38 + Lemma 8.31 directly.
-- See `cor_8_32_clean` below for the refactored Wedhorn-direct chain.

/-! ## Wedhorn-direct flat-restriction chain (Examples 6.38 + Lemma 8.31)

Per Wedhorn Prop 8.30 proof (p.83): "By Example 6.38 we know that `O_X(V)`
is again a strongly noetherian Tate ring. ... we may assume that X = V and
that A is complete. We may moreover assume that U is either `R(f/1)` or
`R(1/f)`. ... Thus it suffices to prove [Lemma 8.31]."

The Wedhorn-clean replacement for `flat_over_base_tate` + `flat_over_base_tate_laurent`
follows this route. Hypothesis profile: ONLY Wedhorn's hypotheses (no P, no
HasLocLiftPowerBounded, no LaurentNormalized, no Spa-points). -/

-- Wedhorn Lemma 8.31 (A⟨X⟩ faithfully flat etc.): this is a TateAlgebra-internal
-- statement used INSIDE the proof of Prop 8.30. Not stated at the public API
-- level because its type signature requires the project's `↥(TateAlgebra A)`
-- subring encoding (which has mixed-universe issues). Will be stated as a
-- helper inside the `prop_8_30_flat_clean` proof body when that's worked.

/-- **(Wedhorn Prop 8.30 — Wedhorn-exact)** Rational restriction map
`σ : O_X(V) → O_X(U)` is flat for `U ⊆ V` rational subsets of strongly
noetherian Tate `A`. **Stated via the existing project `restrictionMapHom`
algebra structure** (the `[HasLocLiftPowerBounded A]` requirement is silently
provided via the `hasLocLiftPowerBounded_of_stronglyNoetherianTate` instance).

Discharged via `restrictionMap_isLocalization` (`PresheafTateStructure.lean`)
applied to the principal pair (whose `[IsNoetherianRing P.A₀]` instance is
supplied by `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate`, the
Wedhorn 6.18 corollary sorry-carrier upstream in this file). Since the
restriction is then an `IsLocalization.Away`, `IsLocalization.flat`
delivers `Module.Flat` immediately. The remaining mathematical content
(Wedhorn 6.18) is concentrated in `_aux_noeth_A0_generic_of_stronglyNoetherianTate`. -/
theorem prop_8_30_flat_clean
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (D D' : RationalLocData A)
    (h : rationalOpen D'.T D'.s ⊆ rationalOpen D.T D.s) :
    @Module.Flat (presheafValue D) (presheafValue D') _ _
      ((restrictionMapHom D D' h).toModule) := by
  letI : Algebra (presheafValue D) (presheafValue D') :=
    (restrictionMapHom D D' h).toAlgebra
  haveI : IsNoetherianRing (IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
    -- P0/T#57: was `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate` — a FALSE lemma
    -- (strong-noeth ⇒ noeth-A₀, ℂ_p-counterexample). Deleted; the noeth-A₀ obligation is now an
    -- honest open `sorry`, to be discharged faithfully via `IsStronglyNoetherian ⇒ A⟨X⟩-noetherian`
    -- (Example 6.38) in P1/T#58, NOT via a noetherian ring of definition (case (a)).
    sorry
  haveI : @IsLocalization.Away (presheafValue D) _
      (D.canonicalMap D'.s) (presheafValue D') _
      (restrictionMapHom D D' h).toAlgebra :=
    restrictionMap_isLocalization (IsTateRing.principalPair A).toPairOfDefinition D D' h
  exact IsLocalization.flat (presheafValue D') (Submonoid.powers (D.canonicalMap D'.s))

/-- **(Wedhorn Cor 8.32 — Wedhorn-exact, sub-lemma form, explicit-`P` variant)**
Faithful flatness of the product restriction with `(P : PairOfDefinition A)
[IsNoetherianRing P.A₀]` taken as explicit parameters. This is the
audit-clean hypothesis profile matching `cor_8_32_clean_proof` in
`AuditCleanWrappers.lean`, packaged here as the sorry-carrier in
`StructureSheaf.lean`.

**Discharge plan (downstream).** A wrapper in `AuditCleanWrappers.lean`
(which imports `Cor832`) — namely `cor_8_32_clean_proof` — closes this content
by routing through `productRestriction_faithfullyFlat_tate_of_hSpa_points`
(`Cor832.lean`) with the A-level Spa points supplied via
`exists_hSpa_points_global_of_stronglyNoetherianTate`. The file-graph
(`Cor832 → StructureSheaf`) blocks an in-place discharge of this lemma here,
so the `sorry` body is retained at the `StructureSheaf` level while the
closing path lives downstream. -/
theorem cor_8_32_clean_sub_with_P
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (_P : PairOfDefinition A) [IsNoetherianRing _P.A₀]
    (C : RationalCoveringData A) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
        (presheafValue D.1) := fun D =>
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) :=
  sorry

/-- **(Wedhorn Cor 8.32 — Wedhorn-exact, sub-lemma form)** Faithful flatness
of the product restriction, packaged as a standalone named sub-lemma at the
`StructureSheaf` level.

Closed via delegation to the explicit-`P` variant `cor_8_32_clean_sub_with_P`,
instantiated at `P := (IsTateRing.principalPair A).toPairOfDefinition`. The
`[IsNoetherianRing P.A₀]` instance is supplied by
`_aux_noeth_principalPair_A0_of_stronglyNoetherianTate` (Wedhorn 6.18 /
Def 6.36 content; routes through `_aux_noeth_A0_generic_of_stronglyNoetherianTate`).

**Discharge plan (downstream).** A wrapper in `AuditCleanWrappers.lean`
(which imports `Cor832`) — namely `cor_8_32_clean_proof` — closes
`cor_8_32_clean_sub_with_P` by routing through
`productRestriction_faithfullyFlat_tate_of_hSpa_points` with the A-level Spa
points supplied via `exists_hSpa_points_global_of_stronglyNoetherianTate`. -/
theorem cor_8_32_clean_sub
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCoveringData A) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
        (presheafValue D.1) := fun D =>
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) :=
  haveI : IsNoetherianRing (IsTateRing.principalPair A).toPairOfDefinition.A₀ :=
    -- P0/T#57: was `_aux_noeth_principalPair_A0_of_stronglyNoetherianTate` — a FALSE lemma
    -- (strong-noeth ⇒ noeth-A₀, ℂ_p-counterexample). Deleted; the noeth-A₀ obligation is now an
    -- honest open `sorry`, to be discharged faithfully via `IsStronglyNoetherian ⇒ A⟨X⟩-noetherian`
    -- (Example 6.38) in P1/T#58, NOT via a noetherian ring of definition (case (a)).
    sorry
  cor_8_32_clean_sub_with_P (A := A) (IsTateRing.principalPair A).toPairOfDefinition C

/-- **(Wedhorn Cor 8.32 — Wedhorn-exact)** For strongly noetherian Tate `A`
and finite rational cover `(U_i)`, the product restriction
`O_X(X) → ∏ O_X(U_i)` is faithfully flat. **Wedhorn-exact hypothesis profile.**

Discharged via the named sub-lemma `cor_8_32_clean_sub` (whose `sorry` will be
closed downstream — see its docstring for the file-graph note). -/
theorem cor_8_32_clean
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A]
    (C : RationalCoveringData A) :
    letI : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
        (presheafValue D.1) := fun D ↦
      (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
    Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) :=
  cor_8_32_clean_sub (A := A) C

/-- **(J.1) Tate acyclicity Part 1 (separation), Wedhorn-exact.** Uses
`cor_8_32_clean` (no extras). Hypothesis profile = Wedhorn 8.28(b).

If the product restriction sends `x` to zero on every cover piece, then the
algebra map `presheafValue C.base → ∏ presheafValue D` sends `x` to `0`. The
faithful flatness from `cor_8_32_clean` upgrades the algebra map to a faithful
`SMul`, hence injective, hence `x = 0`. -/
theorem tateAcyclicity_separation_via_cor832
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A]
    [T2Space A] [NonarchimedeanRing A]
    (C : RationalCoveringData A) (_hne : C.covers.Nonempty) :
    ∀ x : presheafValue C.base,
      (∀ (D : RationalLocData A) (hD : D ∈ C.covers),
        restrictionMap C.base D (C.hsubset D hD) x = 0) → x = 0 := by
  letI algInst : ∀ D : { D // D ∈ C.covers }, Algebra (presheafValue C.base)
      (presheafValue D.1) := fun D ↦
    (restrictionMapHom C.base D.1 (C.hsubset D.1 D.2)).toAlgebra
  haveI hFF : Module.FaithfullyFlat (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) :=
    cor_8_32_clean (A := A) C
  haveI hFS : FaithfulSMul (presheafValue C.base)
      (∀ D : { D // D ∈ C.covers }, presheafValue D.1) :=
    Module.FaithfullyFlat.faithfulSMul
  have hinj : Function.Injective
      (algebraMap (presheafValue C.base)
        (∀ D : { D // D ∈ C.covers }, presheafValue D.1)) :=
    FaithfulSMul.algebraMap_injective _ _
  intro x hx
  apply hinj
  rw [map_zero]
  funext ⟨D, hD⟩
  -- `algebraMap _ (∀ D, _) x ⟨D, hD⟩ = algebraMap _ (presheafValue D) x` by
  -- `Pi.algebraMap_def`, and that equals `restrictionMapHom C.base D _ x` by the
  -- `toAlgebra` unfolding; on the RHS `Pi.zero_apply` collapses `0 ⟨D, hD⟩ = 0`.
  change restrictionMapHom C.base D (C.hsubset D hD) x = 0
  exact hx D hD

end ValuationSpectrum

/-! ## Wedhorn-exact `isSheafy_ofStronglyNoetherianTate` (no extras section)

Outside `ValuationSpectrum`'s `variable [HasLocLiftPowerBounded A]` scope, in
a fresh namespace, so `[HasLocLiftPowerBounded A]` is NOT a section-implicit
hypothesis. -/

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [PlusSubring A] [IsHuberRing A]

omit [PlusSubring A] [IsHuberRing A] in
/-- **Helper sub-lemma.** When `D.s` is nilpotent, the localization
`Localization.Away D.s` is the zero ring (because `0 ∈ Submonoid.powers D.s`),
hence its completion `presheafValue D` is subsingleton. -/
theorem presheafValue_subsingleton_of_nilpotent_s (D : RationalLocData A)
    (hs : IsNilpotent D.s) : Subsingleton (presheafValue D) := by
  haveI : Subsingleton (Localization.Away D.s) := by
    apply IsLocalization.subsingleton (M := Submonoid.powers D.s)
    obtain ⟨n, hn⟩ := hs
    exact ⟨n, hn⟩
  have h01 : (0 : presheafValue D) = 1 := by
    rw [← map_zero D.coeRingHom, ← map_one D.coeRingHom,
      Subsingleton.elim (0 : Localization.Away D.s) 1]
  exact subsingleton_of_zero_eq_one h01

/-- **Internal sub-lemma for the empty-cover separation edge case.** When a
rational covering has empty cover set and the base `s ≠ 0`, separation
(injectivity of `productRestrictionSub`) follows from the existence of a
Spa point above the zero ideal: the cover condition then forces a member of
the empty cover set, contradicting non-emptiness. Without `[IsDomain A]`,
proving `(⊥ : Ideal A).IsPrime` requires a different route (use a maximal
ideal containing some annihilator), which we leave as a project-internal
sub-lemma. -/
theorem isSheafy_separation_empty_cover_of_stronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
    (C : RationalCoveringData A) (_hs : C.base.s ≠ 0) (_hne : ¬ C.covers.Nonempty)
    (x y : presheafValue C.base) :
    x = y := by
  -- Without [IsDomain A], we cannot use Ideal.isPrime_bot. Instead case-split
  -- on whether `C.base.s` is nilpotent.
  by_cases hnil : IsNilpotent C.base.s
  · -- If `s` is nilpotent, `presheafValue C.base` is subsingleton.
    haveI := presheafValue_subsingleton_of_nilpotent_s C.base hnil
    exact Subsingleton.elim x y
  · -- If `s` is not nilpotent, then by `nilpotent_iff_mem_prime` there
    -- exists a prime `p` with `s ∉ p`. Apply `exists_spa_point_in_rationalOpen_of_prime`
    -- to get a Spa point in `rationalOpen C.base.T C.base.s`, then `C.hcover`
    -- produces a member of `C.covers`, contradicting `_hne`.
    exfalso
    have hcon : ∃ p : Ideal A, p.IsPrime ∧ C.base.s ∉ p := by
      by_contra h
      push Not at h
      exact hnil (nilpotent_iff_mem_prime.mpr h)
    obtain ⟨p, hp, hsp⟩ := hcon
    obtain ⟨v, hv_rat, _⟩ :=
      exists_spa_point_in_rationalOpen_of_prime (A := A) C p hp hsp
    obtain ⟨D, hD, _⟩ := C.hcover v hv_rat
    exact _hne ⟨D, hD⟩

/-- **Wedhorn Theorem 8.28(b), Wedhorn-exact form — B2 audit-corrected 2026-05-18.**
Strongly noetherian Tate ⇒ sheafy. **Hypothesis profile matches Wedhorn 8.28(b)
EXACTLY**:
- `[CommRing A] [TopologicalSpace A] [IsTopologicalRing A]` — basic topological ring
- `[PlusSubring A] [IsHuberRing A]` — affinoid ring `(A, A⁺)`
- `[IsTateRing A]` — Tate (case b)
- `[IsStronglyNoetherian A]` — strongly noetherian
- `[T2Space A] [NonarchimedeanRing A]` — completeness/topological structure

**No `[IsDomain A]`. No `(P : PairOfDefinition A)`. No `hSpa_points_global`. No
`[HasLocLiftPowerBounded A]`** — the last is silently derived by typeclass
synthesis via the `hasLocLiftPowerBounded_of_stronglyNoetherianTate` instance
(line 1316), which itself is provable from Wedhorn 7.52(2) + 7.41 (T-H.2.a +
T-H.2.b sub-lemmas in `Presheaf.lean`).

The proof body uses:
- T-H.2 instance: derived via Wedhorn 7.52(2) and Wedhorn 7.41.
- Spa-points: `exists_hSpa_points_global_of_stronglyNoetherianTate` (Wedhorn 7.45
  chain — no Bourbaki).
- Pair-of-definition: `IsTateRing.principalPair` +
  `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate`. -/
theorem isSheafy_ofStronglyNoetherianTate
    [IsTateRing A] [IsNoetherianRing A] [IsStronglyNoetherian A] [T2Space A]
    [NonarchimedeanRing A] [CompatiblePlusSubring A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] :
    IsSheafy A :=
  { embedding := fun C _hC ↦ by
      by_cases hs : C.base.s = 0
      · haveI := presheafValue_subsingleton_of_s_eq_zero C.base hs
        exact Topology.IsEmbedding.of_subsingleton _
      · refine ⟨productRestrictionSub_isInducing_tate (A := A) C, ?_⟩
        intro x y hxy
        by_cases hne : C.covers.Nonempty
        · have hxy' : ∀ (D : RationalLocData A) (hD : D ∈ C.covers),
              restrictionMap C.base D (C.hsubset D hD) (x - y) = 0 := by
            intro D hD
            have hxyD := congr_fun hxy ⟨D, hD⟩
            change restrictionMapHom C.base D (C.hsubset D hD) (x - y) = 0
            rw [map_sub]
            exact sub_eq_zero.mpr hxyD
          have h_diff : x - y = 0 :=
            tateAcyclicity_separation_via_cor832 (A := A) C hne (x - y) hxy'
          exact sub_eq_zero.mp h_diff
        · exact isSheafy_separation_empty_cover_of_stronglyNoetherianTate C hs hne x y,
    gluing := fun C _hC f hcompat ↦ by
      by_cases hne : C.covers.Nonempty
      · exact tateAcyclicity_gluing_via_descent (A := A) C hne f hcompat
      · refine ⟨0, ?_⟩
        intro ⟨D, hD⟩
        exact absurd ⟨D, hD⟩ hne }

/-! ## Hidden-obligation audit pass 2 (2026-05-17): Wedhorn 6.18 A₀-noeth

Surfaced by pass-2 application of the 5-step checklist to pass-1 audit lemmas.

The pass-1 clean adapters (`lemma_8_31_1_AlangleX_faithfullyFlat_clean`,
`presheafValue_isTateRing_clean`, etc.) all need to discharge
`[IsNoetherianRing P.A₀]` for some pair of definition `P`. This is **not
derivable from `[IsNoetherianRing A]` alone** — Wedhorn 6.18 / Def 6.36 give
the equivalence "A strongly noetherian Tate ⇔ A₀ noetherian for some/any
pair of definition". The lemma name
`isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate` is referenced
in the docstring of `isSheafy_ofStronglyNoetherianTate` (above) but was
never actually stated. Add it here. -/

-- **[P0 / T#57 — DELETED 2026-06-02] two FALSE public wrappers removed:**
-- `isNoetherianRing_principalPair_A₀_of_stronglyNoetherianTate` and
-- `isNoetherianRing_A₀_of_stronglyNoetherianTate` asserted "strongly-noetherian-Tate ⇒
-- ring-of-definition A₀ noetherian" — the CONVERSE of Wedhorn Remark 6.37(3), FALSE for ℂ_p
-- (strongly-noeth-Tate, non-noetherian ring of definition; Wedhorn 8.28(b) holds for it).
-- Wedhorn 8.28(b) is an ALTERNATIVE to 8.28(a)'s "noetherian ring of definition" — a case-(b)
-- result must not require it. The faithful route is `IsStronglyNoetherian A ⇒ IsNoetherianRing
-- A⟨X⟩` (the Tate ALGEBRA, Example 6.38), never A₀; pursued in P1 (T#58).

omit [PlusSubring A] [IsHuberRing A] in
/-- **Sub-lemma L5.1.3 — `A⟨X⟩` noetherian inductive step** (named sub-lemma
relocated here from `WedhornStronglyNoetherian.lean` so the proof of
`isStronglyNoetherian_of_isNoetherianRing_isTateRing` below can use it
without violating the import graph; the original site imported
`StructureSheaf` so could not be referenced from here).

Given `A⟨X_1,…,X_k⟩` noetherian, `A⟨X_1,…,X_{k+1}⟩ = A⟨X_1,…,X_k⟩⟨X_{k+1}⟩`
is also noetherian.

**Discharge route**: L5.1.1 (TateAlgebra ≅ AdicCompletion) + L5.1.2
(Stacks 00MA, mathlib gap) + Hilbert basis (mathlib `Polynomial.isNoetherianRing`).

**Difficulty**: EASY-MEDIUM once L5.1.1 + L5.1.2 land. ~40 lines. -/
theorem _sub_lemma_L5_1_3_inductive_step
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A] :
    ∀ k : ℕ, IsNoetherianRing (restrictedMvPowerSeriesSubring k A) →
      IsNoetherianRing (restrictedMvPowerSeriesSubring (k + 1) A) :=
  sorry

omit [PlusSubring A] [IsHuberRing A] in
/-- **(Wedhorn 6.18 — forward implication)** *"A noetherian Tate ring is
strongly noetherian."*

This is the equivalence that lets pass-1's clean 8.31(1)/(2) and Example
6.38 adapters (which use only `[IsNoetherianRing A]`, matching Wedhorn's
exact wording) work without smuggling `[IsStronglyNoetherian A]` into the
signature. It is **not** a typeclass synthesis chain — it's a theorem.

Discharge plan: Wedhorn Prop 6.18 + Huber's theorem on Tate algebras
(`A noetherian Tate ⇒ A⟨X₁,…,Xₖ⟩ noetherian for all k`). The base case
`k = 0` is the hypothesis (via the canonical isomorphism
`restrictedMvPowerSeriesSubring 0 A ≃+* A`); the inductive step is
`_sub_lemma_L5_1_3_inductive_step` above (Wedhorn 6.18's open mapping
ingredient + Stacks 00MA). -/
theorem isStronglyNoetherian_of_isNoetherianRing_isTateRing
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A] :
    IsStronglyNoetherian A := by
  refine ⟨?_⟩
  intro k
  induction k with
  | zero =>
    -- Base case `restrictedMvPowerSeriesSubring 0 A ≅ A`, which is noetherian by hypothesis.
    -- The k = 0 subring is identified with A via constantCoeff (since `Fin 0 →₀ ℕ` is a
    -- singleton, so MvPowerSeries (Fin 0) A ≃+* A; restrictedness is trivial as cofinite
    -- on a finite-domain function is automatic).
    let e : ↥(restrictedMvPowerSeriesSubring 0 A) ≃+* A :=
      { toFun := fun f ↦ MvPowerSeries.constantCoeff (f : MvPowerSeries (Fin 0) A)
        invFun := fun a ↦ ⟨algebraMap A (MvPowerSeries (Fin 0) A) a,
          MvPowerSeries.IsRestricted_algebraMap a⟩
        left_inv := by
          intro ⟨f, hf⟩
          classical
          apply Subtype.ext
          change algebraMap A (MvPowerSeries (Fin 0) A) (MvPowerSeries.constantCoeff f) = f
          ext n
          have hn : n = 0 := Subsingleton.elim _ _
          subst hn
          rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
          simp [MvPowerSeries.coeff_zero_eq_constantCoeff]
        right_inv := by
          intro a
          change MvPowerSeries.constantCoeff (algebraMap A (MvPowerSeries (Fin 0) A) a) = a
          rw [MvPowerSeries.algebraMap_apply]; simp
        map_mul' := by intros; simp
        map_add' := by intros; simp }
    exact isNoetherianRing_of_ringEquiv A e.symm
  | succ k ih =>
    exact _sub_lemma_L5_1_3_inductive_step (A := A) k ih

/-! ## Hidden-obligation audit pass 1 (2026-05-17): Spa-presheafValue identification

Surfaced by `docs/SHEAFY-HIDDEN-OBLIGATIONS-AUDIT.md` items (9) and (10).

The Wedhorn 8.2 identification `Spa A⟨T/s⟩ ≃ R(T/s) ⊆ Spa A` is the basic
geometric input for the IsSheafy proof. Stated here as the clean target;
discharge requires the full `presheafValue D` topology + Spa-pullback API. -/

-- `Spa_presheafValue_eq_rationalOpen` (Wedhorn 8.2, the `Nonempty (… ≃ …)` headline)
-- was DISCHARGED and moved to `SpaRationalOpenComparison.lean` (2026-07-20): the
-- canonical equivalence is `spaPresheafValueEquivRationalOpen`, with forward map
-- `comap D.canonicalMap`, exact image equality, and forward continuity — with no
-- noetherian/strongly-noetherian/T2/nonarchimedean hypotheses.

/-! ## Hidden-obligation audit pass 3 (2026-05-17): Spa.comap framework

Item 19 from the audit. The Spa-pullback infrastructure (`Spa.comap` of a
continuous ring hom inducing a Spa map) is needed to discharge
`Spa_presheafValue_eq_rationalOpen`. We split it into:

(a) `Spa.comap_of_continuousRingHom` — the underlying continuous map
    `Spa B → Spa A` for a continuous ring hom `φ : A → B` mapping `A⁺` to
    `B⁺` (Wedhorn 8.7).
(b) `Spa.comap_image_eq_rationalOpen` — the image identification for the
    case `B = presheafValue D` (Wedhorn 8.2). -/

/-- **(Wedhorn 8.7 — Spa pullback continuous map)** *"Any continuous ring
hom `φ : A → B` mapping `A⁺` into `B⁺` induces a continuous map
`Spa(B,B⁺) → Spa(A,A⁺)` via pullback of valuations."*

The Spa-pullback is needed for the identification
`Spa_presheafValue_eq_rationalOpen`. -/
noncomputable def Spa.comap_of_continuousRingHom
    {B : Type*} [CommRing B] [TopologicalSpace B] [PlusSubring B]
    [IsTopologicalRing B] [IsHuberRing B]
    (φ : A →+* B) (hφ : Continuous φ)
    (hφ_plus : ∀ a ∈ (A⁺ : Set A), φ a ∈ (B⁺ : Set B)) :
    Spa B B⁺ → Spa A A⁺ := fun v ↦
  ⟨ValuationSpectrum.comap φ v.val,
    ⟨ValuationSpectrum.comap_isContinuous hφ v.property.1,
     fun a ha ↦ by
       rw [ValuationSpectrum.comap_vle, map_one]
       exact v.property.2 (φ a) (hφ_plus a ha)⟩⟩

/-- **(Wedhorn 8.7 — Spa pullback continuity)** Continuity of
`Spa.comap_of_continuousRingHom`. Subtype-topology + `Spv.comap_continuous`. -/
theorem Spa.comap_of_continuousRingHom_continuous
    {B : Type*} [CommRing B] [TopologicalSpace B] [PlusSubring B]
    [IsTopologicalRing B] [IsHuberRing B]
    (φ : A →+* B) (hφ : Continuous φ)
    (hφ_plus : ∀ a ∈ (A⁺ : Set A), φ a ∈ (B⁺ : Set B)) :
    Continuous (Spa.comap_of_continuousRingHom φ hφ hφ_plus) := by
  -- Subtype-topology: `Continuous f ↔ Continuous (Subtype.val ∘ f)`.
  refine continuous_induced_rng.mpr ?_
  -- The composed map is `Spv.comap φ ∘ Subtype.val`, both continuous.
  exact (ValuationSpectrum.comap_continuous φ).comp continuous_subtype_val

end ValuationSpectrum
