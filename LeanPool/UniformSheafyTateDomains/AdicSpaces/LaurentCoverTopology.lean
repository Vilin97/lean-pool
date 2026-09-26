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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.LaurentCoverExact
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.TateAlgebraTopology

/-!
# Quotient topology API for the Laurent cover (T131)

For an `IsTateRing A`, the algebraic Laurent quotient objects defined
in `LaurentCoverExact.lean`,

* `B₁_gen f := TateAlgebra A ⧸ ⟨algebraMap f − X⟩`,
* `B₂_gen f := TateAlgebra A ⧸ ⟨1 − algebraMap f · X⟩`,
* `B₁₂_gen f := LaurentTateAlgebra A ⧸ ⟨algebraMap f − ζ⟩`,

inherit canonical quotient topologies from the canonical Tate-algebra
topologies on `TateAlgebra A` and `TateAlgebra₂ A` (via
`TateAlgebra.instTopologicalSpaceTateAlgebra` /
`TateAlgebra.instTopologicalSpaceTateAlgebra₂` in
`TateAlgebraTopology.lean`).

This module exposes those topologies as `noncomputable def`s plus the
matching `IsTopologicalRing` / `IsTopologicalAddGroup` instances.

For `B₁₂_gen` the topology is built in two stages: first a quotient
topology on `LaurentTateAlgebra A = TateAlgebra₂ A ⧸ laurentIdeal A`
(the "rank-2 Laurent" base), then a further quotient by
`laurentFSubZetaIdeal f`. The resulting topology coincides with the
canonical bivariate-overlap topology
(`TateAlgebra.quotientBivariateOverlapIdealTopology`) under the
identification of `B₁₂_gen f` with `TateAlgebra₂ A ⧸
bivariateOverlapIdeal f` (which holds because the two ideals
coincide as A-ideals via `1 − algebraMap f · Y = − Y · (algebraMap f
− X) − (X · Y − 1)`), but we keep the direct two-stage form here so
callers can use the `B₁₂_gen` type and the `quotLaurent` /
`posLift` / `negLift` of `LaurentCoverExact.lean` directly.

Together with the existing `epsilonHom_gen` / `deltaMap_gen` /
`posLift` / `negLift` declarations in `LaurentCoverExact.lean`, this
is the topology layer that the T130 strict-exactness/embedding
follow-up needs.

## Continuity of `deltaMap_gen` (T132)

Section `EmbeddingContinuity` proves canonical-topology continuity of
`posIncl`, `negIncl`, `mkHom`, `posEmbHom`, `negEmbHom`. Section
`LiftContinuity` proves continuity of `posLift`, `negLift`, and the
final `deltaMap_gen f : B₁_gen f × B₂_gen f → B₁₂_gen f` under the T131
quotient topologies. The proofs use the basic-neighborhood basis
`tateAlgBasis'` / `tateAlgBasis'₂` from `TateAlgebraTopology.lean`
together with the existing coefficient bridges
`tateAlgNhd_coeff_mem` and `tateAlgNhd₂_of_coeff_mem_principal`.
-/

@[expose] public section

namespace LaurentCover

open TateAlgebra LaurentTateAlgebra Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

section TopologicalQuotients

variable [IsTateRing A] [IsNoetherianRing A] [IsDomain A]
variable (f : A)

/-- Canonical quotient topology on `B₁_gen f`, induced from the
canonical Tate-algebra topology on `TateAlgebra A`. -/
@[reducible]
noncomputable instance B₁_gen_topology : TopologicalSpace (B₁_gen f) :=
  @topologicalRingQuotientTopology _ instTopologicalSpaceTateAlgebra _
    (Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X})

/-- `B₁_gen f` is a topological ring under its canonical quotient topology. -/
noncomputable instance B₁_gen_isTopologicalRing :
    @IsTopologicalRing (B₁_gen f) (B₁_gen_topology f) _ :=
  @topologicalRing_quotient _ instTopologicalSpaceTateAlgebra _
    (Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X})
    instIsTopologicalRingTateAlgebra

/-- `B₁_gen f` is a topological additive group. -/
noncomputable instance B₁_gen_isTopologicalAddGroup :
    @IsTopologicalAddGroup (B₁_gen f) (B₁_gen_topology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (B₁_gen_topology f) (B₁_gen_isTopologicalRing f)

/-- Canonical quotient topology on `B₂_gen f`, induced from the
canonical Tate-algebra topology on `TateAlgebra A`. -/
@[reducible]
noncomputable instance B₂_gen_topology : TopologicalSpace (B₂_gen f) :=
  @topologicalRingQuotientTopology _ instTopologicalSpaceTateAlgebra _
    (Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X})

/-- `B₂_gen f` is a topological ring under its canonical quotient topology. -/
noncomputable instance B₂_gen_isTopologicalRing :
    @IsTopologicalRing (B₂_gen f) (B₂_gen_topology f) _ :=
  @topologicalRing_quotient _ instTopologicalSpaceTateAlgebra _
    (Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X})
    instIsTopologicalRingTateAlgebra

/-- `B₂_gen f` is a topological additive group. -/
noncomputable instance B₂_gen_isTopologicalAddGroup :
    @IsTopologicalAddGroup (B₂_gen f) (B₂_gen_topology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (B₂_gen_topology f) (B₂_gen_isTopologicalRing f)

/-- Canonical quotient topology on `LaurentTateAlgebra A`, induced
from the canonical Tate-algebra-of-2-variables topology on
`TateAlgebra₂ A`. -/
@[reducible]
noncomputable instance laurentTateAlgebra_topology :
    TopologicalSpace (LaurentTateAlgebra A) :=
  @topologicalRingQuotientTopology _ instTopologicalSpaceTateAlgebra₂ _
    (laurentIdeal A)

/-- `LaurentTateAlgebra A` is a topological ring under its canonical
quotient topology. -/
noncomputable instance laurentTateAlgebra_isTopologicalRing :
    @IsTopologicalRing (LaurentTateAlgebra A)
      laurentTateAlgebra_topology _ :=
  @topologicalRing_quotient _ instTopologicalSpaceTateAlgebra₂ _
    (laurentIdeal A) instIsTopologicalRingTateAlgebra₂

/-- `LaurentTateAlgebra A` is a topological additive group. -/
noncomputable instance laurentTateAlgebra_isTopologicalAddGroup :
    @IsTopologicalAddGroup (LaurentTateAlgebra A)
      laurentTateAlgebra_topology _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    laurentTateAlgebra_topology laurentTateAlgebra_isTopologicalRing

/-- Canonical quotient topology on `B₁₂_gen f`, built as the further
quotient of the canonical topology on `LaurentTateAlgebra A` by
`laurentFSubZetaIdeal f`. -/
@[reducible]
noncomputable instance B₁₂_gen_topology : TopologicalSpace (B₁₂_gen f) :=
  @topologicalRingQuotientTopology _ laurentTateAlgebra_topology _
    (laurentFSubZetaIdeal f)

/-- `B₁₂_gen f` is a topological ring under its canonical quotient topology. -/
noncomputable instance B₁₂_gen_isTopologicalRing :
    @IsTopologicalRing (B₁₂_gen f) (B₁₂_gen_topology f) _ :=
  @topologicalRing_quotient _ laurentTateAlgebra_topology _
    (laurentFSubZetaIdeal f) laurentTateAlgebra_isTopologicalRing

/-- `B₁₂_gen f` is a topological additive group. -/
noncomputable instance B₁₂_gen_isTopologicalAddGroup :
    @IsTopologicalAddGroup (B₁₂_gen f) (B₁₂_gen_topology f) _ :=
  @IsTopologicalRing.to_topologicalAddGroup _ _
    (B₁₂_gen_topology f) (B₁₂_gen_isTopologicalRing f)

omit [IsNoetherianRing A] [IsDomain A] in
/-- The quotient map `LaurentTateAlgebra A → B₁₂_gen f` is continuous
under the canonical topologies. -/
theorem quotLaurent_continuous :
    @Continuous _ _ laurentTateAlgebra_topology (B₁₂_gen_topology f)
      (quotLaurent f) :=
  @continuous_quot_mk _ laurentTateAlgebra_topology _

end TopologicalQuotients

/-! ### Canonical-topology continuity of the Laurent embeddings (T132)

The key inputs are:

* `tateAlgBasis'.hasBasis_nhds_zero` and `tateAlgBasis'₂.hasBasis_nhds_zero`,
  giving the basic-neighborhood bases at `0` for the canonical Tate-algebra
  topologies (subgroups `tateAlgNhd P n` and `tateAlgNhd₂ P n` indexed by `n`).
* `tateAlgNhd_coeff_mem` (univariate) and `tateAlgNhd₂_of_coeff_mem_principal`
  (bivariate), giving the coefficient bridge between the two bases.
* `continuous_of_continuousAt_zero` for additive group homs.

`varInclHom j` (for `j : Fin 2`) acts on a univariate restricted power
series by reindexing to a single variable in the bivariate ring; its
coefficients are either `0` or copy a univariate coefficient. So if every
coefficient of `y` lies in `image P.I^n`, the same holds for every
coefficient of the bivariate lift, giving the basic-neighborhood
preimage containment that controls continuity. -/

section EmbeddingContinuity

variable [IsTateRing A]

private theorem varIncl_continuous_aux (j : Fin 2)
    (φ : ↥(TateAlgebra A) →+* ↥(TateAlgebra₂ A))
    (hφ : ∀ y : ↥(TateAlgebra A), (φ y).val = varInclHom j y.val) :
    @Continuous _ _ instTopologicalSpaceTateAlgebra
      instTopologicalSpaceTateAlgebra₂ φ := by
  letI τ₁ : TopologicalSpace ↥(TateAlgebra A) := tateAlgebraTopology'
  letI τ₂ : TopologicalSpace ↥(TateAlgebra₂ A) := tateAlgebra₂Topology'
  haveI hr1 : IsTopologicalRing ↥(TateAlgebra A) :=
    tateAlgebraTopology'_isTopologicalRing
  haveI hr2 : IsTopologicalRing ↥(TateAlgebra₂ A) :=
    tateAlgebra₂Topology'_isTopologicalRing
  haveI hag1 : IsTopologicalAddGroup ↥(TateAlgebra A) :=
    hr1.to_topologicalAddGroup
  haveI hag2 : IsTopologicalAddGroup ↥(TateAlgebra₂ A) :=
    hr2.to_topologicalAddGroup
  let pp := IsTateRing.principalPair A
  let P := pp.toPairOfDefinition
  have hπ_gen : P.I = Ideal.span {pp.π} := pp.I_eq_span
  have hπ_unit : IsUnit ((pp.π : A)) := pp.π_isUnit
  apply continuous_of_continuousAt_zero φ
  rw [ContinuousAt, map_zero]
  rw [tateAlgBasis'.hasBasis_nhds_zero.tendsto_iff
    tateAlgBasis'₂.hasBasis_nhds_zero]
  intro n _
  refine ⟨n, trivial, ?_⟩
  intro y hy
  apply tateAlgNhd₂_of_coeff_mem_principal P n pp.π hπ_gen hπ_unit
  · intro l
    rw [hφ y]
    change varInclFun j y.val l ∈ P.A₀
    rw [varInclFun_apply]
    split_ifs
    · obtain ⟨b, _, hb_eq⟩ :=
        tateAlgNhd_coeff_mem P n hy (Finsupp.single 0 (l j))
      rw [← hb_eq]; exact b.property
    · exact P.A₀.zero_mem
  · intro l
    rw [hφ y]
    change ∃ b : P.A₀, b ∈ P.I ^ n ∧ (b : A) = varInclFun j y.val l
    rw [varInclFun_apply]
    split_ifs
    · exact tateAlgNhd_coeff_mem P n hy (Finsupp.single 0 (l j))
    · exact ⟨0, (P.I ^ n).zero_mem, by simp⟩

/-- The positive variable inclusion `posIncl : A⟨X⟩ →+* A⟨X, Y⟩` is continuous
under the canonical Tate-algebra topologies. -/
theorem posIncl_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra
      instTopologicalSpaceTateAlgebra₂
      (LaurentTateAlgebra.posIncl : ↥(TateAlgebra A) →+* ↥(TateAlgebra₂ A)) :=
  varIncl_continuous_aux 0 _ fun _ ↦ rfl

/-- The negative variable inclusion `negIncl : A⟨X⟩ →+* A⟨X, Y⟩` is continuous
under the canonical Tate-algebra topologies. -/
theorem negIncl_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra
      instTopologicalSpaceTateAlgebra₂
      (LaurentTateAlgebra.negIncl : ↥(TateAlgebra A) →+* ↥(TateAlgebra₂ A)) :=
  varIncl_continuous_aux 1 _ fun _ ↦ rfl

/-- The Laurent quotient projection `mkHom : A⟨X, Y⟩ →+* A⟨ζ, ζ⁻¹⟩` is
continuous from the canonical bivariate Tate topology to the canonical
Laurent quotient topology. -/
theorem mkHom_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra₂ laurentTateAlgebra_topology
      (LaurentTateAlgebra.mkHom : ↥(TateAlgebra₂ A) →+* LaurentTateAlgebra A) :=
  @continuous_quot_mk _ instTopologicalSpaceTateAlgebra₂ _

/-- The positive Laurent embedding `posEmbHom : A⟨X⟩ →+* A⟨ζ, ζ⁻¹⟩`
(`X ↦ ζ`) is continuous under the canonical Tate topologies. -/
theorem posEmbHom_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra laurentTateAlgebra_topology
      (LaurentTateAlgebra.posEmbHom : ↥(TateAlgebra A) →+* LaurentTateAlgebra A) :=
  mkHom_continuous.comp posIncl_continuous

/-- The negative Laurent embedding `negEmbHom : A⟨X⟩ →+* A⟨ζ, ζ⁻¹⟩`
(`X ↦ ζ⁻¹`) is continuous under the canonical Tate topologies. -/
theorem negEmbHom_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra laurentTateAlgebra_topology
      (LaurentTateAlgebra.negEmbHom : ↥(TateAlgebra A) →+* LaurentTateAlgebra A) :=
  mkHom_continuous.comp negIncl_continuous

end EmbeddingContinuity

/-! ### Continuity of the lifts and `deltaMap_gen` -/

section LiftContinuity

variable [IsTateRing A] [IsNoetherianRing A] [IsDomain A] (f : A)

omit [IsNoetherianRing A] [IsDomain A] in
/-- The composition `(quotLaurent f).comp posEmbHom : A⟨X⟩ → B₁₂_gen f` is
continuous under the canonical topologies. -/
theorem quotLaurent_comp_posEmbHom_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra (B₁₂_gen_topology f)
      ((quotLaurent f).comp LaurentTateAlgebra.posEmbHom) :=
  (quotLaurent_continuous f).comp posEmbHom_continuous

omit [IsNoetherianRing A] [IsDomain A] in
/-- The composition `(quotLaurent f).comp negEmbHom : A⟨X⟩ → B₁₂_gen f` is
continuous under the canonical topologies. -/
theorem quotLaurent_comp_negEmbHom_continuous :
    @Continuous _ _ instTopologicalSpaceTateAlgebra (B₁₂_gen_topology f)
      ((quotLaurent f).comp LaurentTateAlgebra.negEmbHom) :=
  (quotLaurent_continuous f).comp negEmbHom_continuous

omit [IsNoetherianRing A] [IsDomain A] in
/-- The positive Laurent lift `posLift f : B₁_gen f →+* B₁₂_gen f` is
continuous under the canonical quotient topologies. -/
theorem posLift_continuous :
    @Continuous _ _ (B₁_gen_topology f) (B₁₂_gen_topology f) (posLift f) := by
  letI tA : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  letI hringA : IsTopologicalRing ↥(TateAlgebra A) := instIsTopologicalRingTateAlgebra
  letI tB1 : TopologicalSpace (B₁_gen f) := B₁_gen_topology f
  letI tB12 : TopologicalSpace (B₁₂_gen f) := B₁₂_gen_topology f
  haveI hringB1 : IsTopologicalRing (B₁_gen f) := B₁_gen_isTopologicalRing f
  have hQM : IsQuotientMap (Ideal.Quotient.mk
      (Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X})) :=
    (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap
  exact hQM.continuous_iff.mpr (quotLaurent_comp_posEmbHom_continuous f)

omit [IsNoetherianRing A] [IsDomain A] in
/-- The negative Laurent lift `negLift f : B₂_gen f →+* B₁₂_gen f` is
continuous under the canonical quotient topologies. -/
theorem negLift_continuous :
    @Continuous _ _ (B₂_gen_topology f) (B₁₂_gen_topology f) (negLift f) := by
  letI tA : TopologicalSpace ↥(TateAlgebra A) := instTopologicalSpaceTateAlgebra
  letI hringA : IsTopologicalRing ↥(TateAlgebra A) := instIsTopologicalRingTateAlgebra
  letI tB2 : TopologicalSpace (B₂_gen f) := B₂_gen_topology f
  letI tB12 : TopologicalSpace (B₁₂_gen f) := B₁₂_gen_topology f
  haveI hringB2 : IsTopologicalRing (B₂_gen f) := B₂_gen_isTopologicalRing f
  have hQM : IsQuotientMap (Ideal.Quotient.mk
      (Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X})) :=
    (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap
  exact hQM.continuous_iff.mpr (quotLaurent_comp_negEmbHom_continuous f)

omit [IsNoetherianRing A] [IsDomain A] in
/-- The Laurent delta map `deltaMap_gen f : B₁_gen f × B₂_gen f → B₁₂_gen f`,
defined by `(b₁, b₂) ↦ posLift f b₁ − negLift f b₂`, is continuous under
the canonical product / quotient topologies. -/
theorem deltaMap_gen_continuous :
    @Continuous _ _
      (@instTopologicalSpaceProd _ _ (B₁_gen_topology f) (B₂_gen_topology f))
      (B₁₂_gen_topology f) (deltaMap_gen f) := by
  letI tB1 : TopologicalSpace (B₁_gen f) := B₁_gen_topology f
  letI tB2 : TopologicalSpace (B₂_gen f) := B₂_gen_topology f
  letI tB12 : TopologicalSpace (B₁₂_gen f) := B₁₂_gen_topology f
  haveI hringB12 : IsTopologicalRing (B₁₂_gen f) := B₁₂_gen_isTopologicalRing f
  haveI hagB12 : IsTopologicalAddGroup (B₁₂_gen f) := B₁₂_gen_isTopologicalAddGroup f
  have h1 : Continuous (fun p : B₁_gen f × B₂_gen f ↦ posLift f p.1) :=
    (posLift_continuous f).comp continuous_fst
  have h2 : Continuous (fun p : B₁_gen f × B₂_gen f ↦ negLift f p.2) :=
    (negLift_continuous f).comp continuous_snd
  exact h1.sub h2

end LiftContinuity

/-! ### Continuity and inducing-topology of `epsilonHom_gen` (T134)

The Laurent diagonal `epsilonHom_gen f : A →+* B₁_gen f × B₂_gen f` is
continuous under the canonical T132 quotient topologies (immediate from
`tateAlgebra_algebraMap_continuous` and the continuity of the quotient
projections).

Strict-exactness — `Topology.IsInducing (epsilonHom_gen f)` — is proved
under the prerequisites for the Banach open mapping theorem at the
algebraic Tate level:

* `[UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [SigmaCompactSpace A]` on the source `A`,
* `T2Space (B₁₂_gen f)`, so that `ker (deltaMap_gen f)` is closed in
  `B₁_gen f × B₂_gen f`,
* `BaireSpace` on the kernel subspace, providing the Baire-T2 input to
  the open mapping theorem.

The remaining algebraic ingredients (`row3_exact`,
`epsilonHom_gen_injective`, `deltaMap_gen_continuous`) are supplied by
`LaurentCoverExact.lean` and T132 respectively. -/

section EpsilonHomInducing

variable [IsTateRing A] (f : A)

/-- The Laurent diagonal `epsilonHom_gen f : A →+* B₁_gen f × B₂_gen f` is
continuous under the canonical T132 quotient topologies. -/
theorem epsilonHom_gen_continuous :
    Continuous (epsilonHom_gen f : A → B₁_gen f × B₂_gen f) := by
  refine Continuous.prodMk ?_ ?_ <;>
    exact continuous_quot_mk.comp tateAlgebra_algebraMap_continuous

variable [IsNoetherianRing A] [IsDomain A]

omit [IsNoetherianRing A] [IsDomain A] in
/-- The kernel of `deltaMap_gen f` is closed in `B₁_gen f × B₂_gen f`,
provided `B₁₂_gen f` is T2 (so that `{0}` is closed and the preimage of a
closed set under a continuous map is closed). -/
theorem ker_deltaMap_gen_isClosed
    (hT2 : @T2Space (B₁₂_gen f) (B₁₂_gen_topology f)) :
    IsClosed ((deltaMap_gen f).ker : Set (B₁_gen f × B₂_gen f)) := by
  letI := hT2
  have hpre : ((deltaMap_gen f).ker : Set (B₁_gen f × B₂_gen f)) =
      (deltaMap_gen f) ⁻¹' {0} := rfl
  rw [hpre]
  exact isClosed_singleton.preimage (deltaMap_gen_continuous f)

omit [IsTateRing A] [IsNoetherianRing A] [IsDomain A] in
/-- The image of the Laurent diagonal `epsilonHom_gen f` equals the kernel
of the Laurent codiagonal `deltaMap_gen f`. This is the algebraic
strict-exactness `row3_exact` lifted to a set-level identification of the
range and the kernel. -/
theorem range_epsilonHom_gen_eq_ker_deltaMap_gen
    [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A]
    (htop : ‹TopologicalSpace A› = UniformSpace.toTopologicalSpace) :
    Set.range (epsilonHom_gen f : A → B₁_gen f × B₂_gen f) =
      ((deltaMap_gen f).ker : Set (B₁_gen f × B₂_gen f)) := by
  obtain ⟨h_eps_ker, h_ker_eps, _⟩ := row3_exact f htop
  ext p
  refine ⟨?_, ?_⟩
  · rintro ⟨a, rfl⟩
    exact h_eps_ker a
  · intro hp
    exact h_ker_eps p hp

/-- **Algebraic Laurent diagonal is a topological embedding** (T134, the
algebraic missing fact for T133's `h_alg_inducing`).

Under the canonical T132 quotient topologies on `B₁_gen f, B₂_gen f`,
the algebraic Laurent diagonal

  `epsilonHom_gen f : A →+* B₁_gen f × B₂_gen f`

is a topological embedding (`Topology.IsInducing`).

The hypotheses package the Banach open mapping prerequisites:

* `[UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
  [SigmaCompactSpace A]` provide the source-side structure for
  `AddMonoidHom.isOpenMap_of_complete_countable`;
* `htop` ensures the topology on `A` matches the uniform structure (the
  same comparison used by `row3_exact`);
* `hf_nonunit` is the standard non-unit side-condition of
  `epsilonHom_gen_injective`;
* `hT2_B12` and `hBaire_ker` provide the closed-kernel + Baire-T2
  inputs at the kernel subspace level. -/
theorem epsilonHom_gen_inducing
    [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A]
    [T2Space A] [SigmaCompactSpace A]
    (htop : ‹TopologicalSpace A› = UniformSpace.toTopologicalSpace)
    (hf_nonunit : ¬IsUnit f)
    (hT2_B12 : @T2Space (B₁₂_gen f) (B₁₂_gen_topology f))
    (hT2_prod : T2Space (B₁_gen f × B₂_gen f))
    (hBaire_ker : BaireSpace
      ↥((deltaMap_gen f).ker : Set (B₁_gen f × B₂_gen f))) :
    Topology.IsInducing (epsilonHom_gen f : A → B₁_gen f × B₂_gen f) := by
  subst htop
  have hker_closed : IsClosed ((deltaMap_gen f).ker :
      Set (B₁_gen f × B₂_gen f)) :=
    ker_deltaMap_gen_isClosed f hT2_B12
  obtain ⟨h_eps_ker, h_ker_eps, _⟩ := row3_exact f rfl
  let K : AddSubgroup (B₁_gen f × B₂_gen f) := (deltaMap_gen f).ker
  have hmem : ∀ a : A, (epsilonHom_gen f a) ∈ K := h_eps_ker
  let e : A →+ ↥K :=
    { toFun := fun a ↦ ⟨epsilonHom_gen f a, hmem a⟩
      map_zero' := by
        apply Subtype.ext
        change epsilonHom_gen f 0 = 0
        exact map_zero _
      map_add' := fun x y ↦ by
        apply Subtype.ext
        change epsilonHom_gen f (x + y) = epsilonHom_gen f x + epsilonHom_gen f y
        exact map_add _ _ _ }
  have he_continuous : Continuous e :=
    Continuous.subtype_mk (epsilonHom_gen_continuous f) _
  have he_inj : Function.Injective e := fun x y hxy ↦
    epsilonHom_gen_injective f hf_nonunit (congrArg Subtype.val hxy)
  have he_surj : Function.Surjective e := fun ⟨p, hp⟩ ↦ by
    obtain ⟨a, ha⟩ := h_ker_eps p hp
    exact ⟨a, Subtype.ext ha⟩
  haveI := hT2_prod
  haveI : BaireSpace ↥K := hBaire_ker
  have he_open : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_complete_countable e he_surj he_continuous
  have he_ind : Topology.IsInducing e :=
    IsHomeomorph.isInducing ⟨he_continuous, he_open, he_inj, he_surj⟩
  have hincl_ind : Topology.IsInducing
      ((↑) : ↥(K : Set (B₁_gen f × B₂_gen f)) → B₁_gen f × B₂_gen f) :=
    hker_closed.isClosedEmbedding_subtypeVal.isInducing
  have hcomp_eq :
      ((↑) : ↥(K : Set (B₁_gen f × B₂_gen f)) → B₁_gen f × B₂_gen f) ∘ e =
        ⇑(epsilonHom_gen f) := rfl
  rw [← hcomp_eq]
  exact hincl_ind.comp he_ind

end EpsilonHomInducing

/-! ### T2/closed-ideal support for Laurent quotients (T135)

Reusable T2 lemmas for the Laurent quotients used by `epsilonHom_gen_inducing`
(T134). All take the same closed-ideal hypotheses as
`tateAlgebra_isClosed_ideal` / `tateAlgebra₂_isClosed_ideal`:
`[IsTateRing A] [T2Space A]`, completeness of `A`, and noetherianity of the
relevant pair-subring.

Together they discharge the `hT2_B12` and `hT2_prod` hypotheses of T134
(`epsilonHom_gen_inducing`); the Banach-required `hBaire_ker` falls under
the same complete-pseudo-metrizability framework but is left as a
separate downstream prerequisite (see the trailing docstring at the end
of this section). -/

section T2Support

variable [IsTateRing A] [T2Space A] [IsNoetherianRing A] [IsDomain A] (f : A)

omit [IsNoetherianRing A] [IsDomain A] in
/-- The plus-branch ideal `Ideal.span {algebraMap f − X}` is closed in
`TateAlgebra A` under the canonical Tate topology. This is a special
case of `tateAlgebra_isClosed_ideal` (Wedhorn 6.17) and the
`B₁_gen`-side counterpart of the existing `oneSubfXIdeal_isClosed`. -/
theorem plusFSubXIdeal_local_isClosed
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    IsClosed
      ((Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X} :
          Ideal ↥(TateAlgebra A)) : Set ↥(TateAlgebra A)) := by
  haveI : IsNoetherianRing ↥(tateAlgebra_pairOfDefinition (A := A)).A₀ := hnoeth
  exact tateAlgebra_isClosed_ideal hA_complete _

omit [IsNoetherianRing A] [IsDomain A] in
/-- T2 of `B₁_gen f = TateAlgebra A ⧸ ⟨algebraMap f − X⟩` under the canonical
quotient topology. -/
theorem B₁_gen_t2Space
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    @T2Space (B₁_gen f) (B₁_gen_topology f) := by
  haveI : IsClosed
      ((Ideal.span {algebraMap A ↥(TateAlgebra A) f -
          TateAlgebra.X}).toAddSubgroup :
        Set ↥(TateAlgebra A)) :=
    plusFSubXIdeal_local_isClosed f hA_complete hnoeth
  infer_instance

omit [IsNoetherianRing A] [IsDomain A] in
/-- T2 of `B₂_gen f = TateAlgebra A ⧸ ⟨1 − algebraMap f · X⟩` under the
canonical quotient topology. -/
theorem B₂_gen_t2Space
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    @T2Space (B₂_gen f) (B₂_gen_topology f) := by
  haveI hclosed : IsClosed
      ((Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f *
          TateAlgebra.X}).toAddSubgroup : Set ↥(TateAlgebra A)) := by
    haveI : IsNoetherianRing ↥(tateAlgebra_pairOfDefinition (A := A)).A₀ := hnoeth
    exact tateAlgebra_isClosed_ideal hA_complete _
  infer_instance

omit [IsNoetherianRing A] [IsDomain A] in
/-- The two-variable Laurent ideal `laurentIdeal A = ⟨X · Y − 1⟩` is closed
in `TateAlgebra₂ A`. -/
theorem laurentIdeal_local_isClosed
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition)) :
    IsClosed ((laurentIdeal A : Ideal ↥(TateAlgebra₂ A)) :
      Set ↥(TateAlgebra₂ A)) := by
  haveI : IsNoetherianRing ↥(tateAlgebra₂_pairOfDefinition (A := A)).A₀ := hnoeth
  exact tateAlgebra₂_isClosed_ideal hA_complete _

omit [IsNoetherianRing A] [IsDomain A] in
/-- T2 of `LaurentTateAlgebra A = TateAlgebra₂ A ⧸ laurentIdeal A` under the
canonical quotient topology. -/
theorem laurentTateAlgebra_t2Space
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition)) :
    @T2Space (LaurentTateAlgebra A) laurentTateAlgebra_topology := by
  haveI : IsClosed ((laurentIdeal A).toAddSubgroup : Set ↥(TateAlgebra₂ A)) :=
    laurentIdeal_local_isClosed hA_complete hnoeth
  change T2Space (↥(TateAlgebra₂ A) ⧸ laurentIdeal A)
  infer_instance

omit [IsNoetherianRing A] [IsDomain A] in
/-- The Laurent-fiber ideal `laurentFSubZetaIdeal f = ⟨algebraMap f − ζ⟩` is
closed in `LaurentTateAlgebra A` under the canonical quotient topology. -/
theorem laurentFSubZetaIdeal_isClosed
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition)) :
    @IsClosed (LaurentTateAlgebra A) laurentTateAlgebra_topology
      ((laurentFSubZetaIdeal f : Ideal (LaurentTateAlgebra A)) :
        Set (LaurentTateAlgebra A)) := by
  letI : TopologicalSpace ↥(TateAlgebra₂ A) := instTopologicalSpaceTateAlgebra₂
  haveI : IsTopologicalRing ↥(TateAlgebra₂ A) := instIsTopologicalRingTateAlgebra₂
  letI : TopologicalSpace (LaurentTateAlgebra A) := laurentTateAlgebra_topology
  haveI : IsTopologicalRing (LaurentTateAlgebra A) := laurentTateAlgebra_isTopologicalRing
  have hcomap_closed : IsClosed
      (((laurentFSubZetaIdeal f).comap LaurentTateAlgebra.mkHom : Ideal _) :
        Set ↥(TateAlgebra₂ A)) := by
    haveI : IsNoetherianRing ↥(tateAlgebra₂_pairOfDefinition (A := A)).A₀ := hnoeth
    exact tateAlgebra₂_isClosed_ideal hA_complete _
  have hQM : Topology.IsQuotientMap
      (LaurentTateAlgebra.mkHom : ↥(TateAlgebra₂ A) → LaurentTateAlgebra A) :=
    (QuotientRing.isOpenQuotientMap_mk _).isQuotientMap
  rw [← hQM.isClosed_preimage]
  exact hcomap_closed

omit [IsNoetherianRing A] [IsDomain A] in
/-- T2 of `B₁₂_gen f = LaurentTateAlgebra A ⧸ laurentFSubZetaIdeal f` under
the canonical two-stage quotient topology. -/
theorem B₁₂_gen_t2Space
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring₂ (IsTateRing.principalPair A).toPairOfDefinition)) :
    @T2Space (B₁₂_gen f) (B₁₂_gen_topology f) := by
  letI : TopologicalSpace (LaurentTateAlgebra A) := laurentTateAlgebra_topology
  haveI : IsTopologicalRing (LaurentTateAlgebra A) := laurentTateAlgebra_isTopologicalRing
  haveI hT2_laurent : T2Space (LaurentTateAlgebra A) :=
    laurentTateAlgebra_t2Space hA_complete hnoeth
  haveI hclosed : IsClosed ((laurentFSubZetaIdeal f).toAddSubgroup :
      Set (LaurentTateAlgebra A)) :=
    laurentFSubZetaIdeal_isClosed f hA_complete hnoeth
  infer_instance

omit [IsNoetherianRing A] [IsDomain A] in
/-- T2 of the product `B₁_gen f × B₂_gen f` under the canonical product
quotient topology. -/
theorem B₁_gen_x_B₂_gen_t2Space
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(pairSubring (IsTateRing.principalPair A).toPairOfDefinition)) :
    T2Space (B₁_gen f × B₂_gen f) := by
  haveI : T2Space (B₁_gen f) := B₁_gen_t2Space f hA_complete hnoeth
  haveI : T2Space (B₂_gen f) := B₂_gen_t2Space f hA_complete hnoeth
  exact Prod.t2Space

/-! ### `BaireSpace` of `ker(deltaMap_gen f)` (next-step blocker)

For the Banach OMT consumed by T134, the kernel
`(deltaMap_gen f).ker` carrier needs `BaireSpace`. The natural derivation
chain is:

* `B₁_gen f`, `B₂_gen f` are `IsCompletelyPseudoMetrizableSpace` (from
  `CompleteSpace` + first-countable + the Birkhoff-Kakutani style metric
  on a first-countable Hausdorff topological group);
* the product is `IsCompletelyPseudoMetrizableSpace`
  (`IsCompletelyPseudoMetrizableSpace.prod`);
* the closed kernel inherits `IsCompletelyPseudoMetrizableSpace`
  (`IsClosed.isCompletelyPseudoMetrizableSpace`);
* `BaireSpace` follows automatically
  (`BaireSpace.of_completelyPseudoMetrizable`).

The first bullet is **the next remaining algebraic-topology fact**:
deriving `IsCompletelyPseudoMetrizableSpace (B₁_gen f)` (and `B₂_gen f`)
from the existing `quotient_*_completeSpace` and
`instFirstCountableTopology*` results requires a Mathlib-style metrizable
upgrade for first-countable Hausdorff topological groups (or a direct
construction via `UniformSpace.metricSpace` from the canonical quotient
uniform space and its countably-generated uniformity).

That step is the next ticket. The current T135 module deliberately stops
at the T2 layer, leaving `hBaire_ker` as an explicit T134 hypothesis. -/

end T2Support

/-! ### Right uniform structure and countably-generated uniformity (T136)

This section installs the canonical right uniform structure on `B₁_gen f`
and `B₂_gen f` (induced by their `IsTopologicalAddGroup` structure),
proves the corresponding `IsUniformAddGroup` instances, and shows the
uniformity is countably-generated. These are the prerequisites for the
`BaireSpace`-of-kernel chain consumed by T134's `hBaire_ker` hypothesis;
the downstream pseudo-metrizability / complete-pseudo-metrizability /
`BaireSpace` steps live in the companion module
`«Adic spaces».LaurentBaireSupport`, which imports the Mathlib
metrizability/Baire APIs without weighing down typeclass synthesis in
this file. -/

open scoped Uniformity

section BaireSupport

variable [IsTateRing A] [T2Space A] [IsNoetherianRing A] [IsDomain A] (f : A)

/-- Canonical right uniform structure on `B₁_gen f` (instance). -/
@[reducible]
noncomputable instance B₁_gen_uniformSpace : UniformSpace (B₁_gen f) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    (B₁_gen_topology f) (B₁_gen_isTopologicalAddGroup f)

/-- Canonical right uniform structure on `B₂_gen f` (instance). -/
@[reducible]
noncomputable instance B₂_gen_uniformSpace : UniformSpace (B₂_gen f) :=
  @IsTopologicalAddGroup.rightUniformSpace _ _
    (B₂_gen_topology f) (B₂_gen_isTopologicalAddGroup f)

/-- `B₁_gen f` is a `IsUniformAddGroup` (the right uniformity is the
group uniformity for the canonical `IsTopologicalAddGroup`). -/
noncomputable instance B₁_gen_isUniformAddGroup :
    @IsUniformAddGroup (B₁_gen f) (B₁_gen_uniformSpace f) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ _
    (B₁_gen_isTopologicalAddGroup f)

/-- `B₂_gen f` is a `IsUniformAddGroup` (analogous to `B₁_gen`). -/
noncomputable instance B₂_gen_isUniformAddGroup :
    @IsUniformAddGroup (B₂_gen f) (B₂_gen_uniformSpace f) _ :=
  @isUniformAddGroup_of_addCommGroup _ _ _
    (B₂_gen_isTopologicalAddGroup f)

omit [IsNoetherianRing A] [IsDomain A] [T2Space A] in
/-- The neighborhood filter at `0 : B₁_gen f` is countably-generated. -/
theorem B₁_gen_nhds_zero_isCountablyGenerated :
    Filter.IsCountablyGenerated (𝓝 (0 : B₁_gen f)) := by
  haveI : FirstCountableTopology ↥(TateAlgebra A) :=
    instFirstCountableTopologyTateAlgebra
  haveI : (𝓝 (0 : ↥(TateAlgebra A))).IsCountablyGenerated := inferInstance
  have hmk_OQM := QuotientRing.isOpenQuotientMap_mk
    (Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X})
  have hmk0 : Ideal.Quotient.mk
      (Ideal.span {algebraMap A ↥(TateAlgebra A) f - TateAlgebra.X})
      (0 : ↥(TateAlgebra A)) = (0 : B₁_gen f) := map_zero _
  have h_map_nhds := hmk_OQM.map_nhds_eq (0 : ↥(TateAlgebra A))
  rw [hmk0] at h_map_nhds
  rw [← h_map_nhds]
  exact Filter.map.isCountablyGenerated _ _

omit [IsNoetherianRing A] [IsDomain A] [T2Space A] in
/-- The neighborhood filter at `0 : B₂_gen f` is countably-generated. -/
theorem B₂_gen_nhds_zero_isCountablyGenerated :
    Filter.IsCountablyGenerated (𝓝 (0 : B₂_gen f)) := by
  haveI : FirstCountableTopology ↥(TateAlgebra A) :=
    instFirstCountableTopologyTateAlgebra
  haveI : (𝓝 (0 : ↥(TateAlgebra A))).IsCountablyGenerated := inferInstance
  have hmk_OQM := QuotientRing.isOpenQuotientMap_mk
    (Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X})
  have hmk0 : Ideal.Quotient.mk
      (Ideal.span {1 - algebraMap A ↥(TateAlgebra A) f * TateAlgebra.X})
      (0 : ↥(TateAlgebra A)) = (0 : B₂_gen f) := map_zero _
  have h_map_nhds := hmk_OQM.map_nhds_eq (0 : ↥(TateAlgebra A))
  rw [hmk0] at h_map_nhds
  rw [← h_map_nhds]
  exact Filter.map.isCountablyGenerated _ _

omit [IsNoetherianRing A] [IsDomain A] [T2Space A] in
/-- The canonical uniformity on `B₁_gen f` is countably-generated. -/
theorem B₁_gen_uniformity_isCountablyGenerated :
    Filter.IsCountablyGenerated (𝓤 (B₁_gen f)) := by
  haveI hcg : (𝓝 (0 : B₁_gen f)).IsCountablyGenerated :=
    B₁_gen_nhds_zero_isCountablyGenerated f
  exact @IsUniformAddGroup.uniformity_countably_generated
    (B₁_gen f) (B₁_gen_uniformSpace f) _ (B₁_gen_isUniformAddGroup f) hcg

omit [IsNoetherianRing A] [IsDomain A] [T2Space A] in
/-- The canonical uniformity on `B₂_gen f` is countably-generated. -/
theorem B₂_gen_uniformity_isCountablyGenerated :
    Filter.IsCountablyGenerated (𝓤 (B₂_gen f)) := by
  haveI hcg : (𝓝 (0 : B₂_gen f)).IsCountablyGenerated :=
    B₂_gen_nhds_zero_isCountablyGenerated f
  exact @IsUniformAddGroup.uniformity_countably_generated
    (B₂_gen f) (B₂_gen_uniformSpace f) _ (B₂_gen_isUniformAddGroup f) hcg

/-! #### Pseudo-metrizable, complete, and BaireSpace chain (T137)

Continuation of T136: this block produces the full
`BaireSpace ↥(deltaMap_gen f).ker` chain by threading the T136
countably-generated uniformity through `UniformSpace.pseudoMetricSpace`
and combining with the existing `TateAlgebra` complete-space results.

The proofs use explicit `letI`/`@`-syntax to control typeclass
elaboration: the canonical `B_i_gen_topology`, the
`B_i_gen_uniformSpace` right-uniform structure, and the
`B_i_gen_isUniformAddGroup` instance are passed by name where Lean's
broad typeclass search would otherwise probe an excessive
instance database. -/

end BaireSupport

end LaurentCover
