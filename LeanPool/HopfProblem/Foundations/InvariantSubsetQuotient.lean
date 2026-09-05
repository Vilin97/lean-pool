/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyTheory.FirstHurewicz2
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz2

/-!
# Hopf problem: foundations · invariant subset quotient

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def ProductRestriction.productPreimageHomeomorph {K X Y : Type*} [TopologicalSpace K]
    [TopologicalSpace X] (f : K × X → Y) (B : Set X) (C : Set Y) (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B) :
    K × B ≃ₜ (f ⁻¹' C)
    where
  toFun p := ⟨(p.1, (p.2 : X)), (hpre _).mpr p.2.property⟩
  invFun p := (p.1.1, ⟨p.1.2, (hpre _).mp p.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

private def
    ProductRestriction.productRestriction {K X Y : Type*} (f : K × X → Y) (B : Set X) (C : Set Y)
    (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B) (p : K × B) : C :=
  ⟨f (p.1, (p.2 : X)), (hpre _).mpr p.2.property⟩

private theorem
    ProductRestriction.productRestriction_continuous {K X Y : Type*} [TopologicalSpace K]
    [TopologicalSpace X] [TopologicalSpace Y] (f : K × X → Y) (B : Set X) (C : Set Y)
    (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B) (hf : Continuous f) :
    Continuous (productRestriction f B C hpre) :=
  hf.restrictPreimage.comp (productPreimageHomeomorph f B C hpre).continuous

private theorem
    ProductRestriction.productRestriction_isClosedMap {K X Y : Type*} [TopologicalSpace K]
    [TopologicalSpace X] [TopologicalSpace Y] (f : K × X → Y) (B : Set X) (C : Set Y)
    (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B) (hf : IsClosedMap f) :
    IsClosedMap (productRestriction f B C hpre) :=
  (hf.restrictPreimage C).comp (productPreimageHomeomorph f B C hpre).isClosedMap

private theorem
    ProductRestriction.productRestriction_surjective {K X Y : Type*} [TopologicalSpace K]
    [TopologicalSpace X] (f : K × X → Y) (B : Set X) (C : Set Y) (hpre : ∀ p, f p ∈ C ↔ p.2 ∈ B)
    (hf : Function.Surjective f) : Function.Surjective (productRestriction f B C hpre) :=
  (hf.restrictPreimage C).comp (productPreimageHomeomorph f B C hpre).surjective

private def
    InvariantSubsetQuotient.imageProject {M Q : Type*} (q : M → Q) (S : Set M) (x : S) : q '' S :=
  ⟨q x, x, x.2, rfl⟩

private theorem
    InvariantSubsetQuotient.imageProject_surjective {M Q : Type*} {q : M → Q} {S : Set M} :
    Function.Surjective (imageProject q S) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem
    InvariantSubsetQuotient.imageProject_continuous {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] (hq : Continuous q) :
    Continuous (imageProject q S) :=
  (hq.comp continuous_subtype_val).subtype_mk _

private theorem InvariantSubsetQuotient.preimage_image_eq {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) : q ⁻¹' (q '' S) = S := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨g, hg⟩ := hq.apply_eq_iff_mem_orbit.mp hxy.symm
    have he : ((g • (⟨y, hy⟩ : S) : S) : M) = x := (hcompat g ⟨y, hy⟩).trans hg
    exact he ▸ (g • (⟨y, hy⟩ : S)).2
  · intro hx
    exact ⟨x, hx, rfl⟩

private def InvariantSubsetQuotient.preimageImageHomeomorph {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) : S ≃ₜ q ⁻¹' (q '' S) :=
  Homeomorph.setCongr (InvariantSubsetQuotient.preimage_image_eq hq hcompat).symm

private theorem
    InvariantSubsetQuotient.imageProject_isCoveringMap {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) :
    IsCoveringMap (imageProject q S) := by
  exact
    (hq.isCoveringMap.restrictPreimage (q '' S)).comp_homeomorph
      (preimageImageHomeomorph hq hcompat)

private theorem InvariantSubsetQuotient.subtypeAction_continuousConstSMul {M Q : Type*} {q : M → Q}
    {S : Set M} [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) : ContinuousConstSMul G S where
  continuous_const_smul
    g := by
    apply Topology.IsInducing.subtypeVal.continuous_iff.mpr
    simpa only [Function.comp_def, hcompat] using
      (hq.continuous_const_smul g).comp continuous_subtype_val

private theorem InvariantSubsetQuotient.imageProject_eq_iff_mem_orbit {M Q : Type*} {q : M → Q}
    {S : Set M} [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) {x y : S} :
    imageProject q S x = imageProject q S y ↔ x ∈ MulAction.orbit G y := by
  rw [Subtype.ext_iff]
  change q x = q y ↔ _
  rw [hq.apply_eq_iff_mem_orbit]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext ((hcompat g y).trans hg)⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (hcompat g y).symm.trans (congrArg Subtype.val hg)⟩

private theorem InvariantSubsetQuotient.imageProject_isQuotientCoveringMap {M Q : Type*} {q : M → Q}
    {S : Set M} [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) :
    IsQuotientCoveringMap (imageProject q S) G
    where
  __ := (imageProject_isCoveringMap hq hcompat).isQuotientMap imageProject_surjective
  __ := subtypeAction_continuousConstSMul hq hcompat
  apply_eq_iff_mem_orbit := imageProject_eq_iff_mem_orbit hq hcompat
  disjoint
    x := by
    obtain ⟨U, hU, hdisj⟩ := hq.disjoint (x : M)
    refine
      ⟨Subtype.val ⁻¹' U, continuous_subtype_val.continuousAt.preimage_mem_nhds hU, fun g hg =>
        ?_⟩
    obtain ⟨y, ⟨z, hz, hzy⟩, hy⟩ := hg
    apply hdisj g
    refine ⟨(y : M), ⟨(z : M), hz, ?_⟩, hy⟩
    exact (hcompat g z).symm.trans (congrArg Subtype.val hzy)

private def InvariantSubsetQuotient.quotientEquiv {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) :
    Quotient (MulAction.orbitRel G S) ≃ q '' S :=
  (Quotient.congrRight (fun _ _ => (imageProject_eq_iff_mem_orbit hq hcompat).symm)).trans
    (Setoid.quotientKerEquivOfSurjective (imageProject q S) imageProject_surjective)

@[simp]
private theorem InvariantSubsetQuotient.quotientEquiv_mk {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) (x : S) :
    quotientEquiv hq hcompat (Quotient.mk (MulAction.orbitRel G S) x) = imageProject q S x :=
  rfl

@[simp]
private theorem InvariantSubsetQuotient.quotientEquiv_symm_imageProject {M Q : Type*} {q : M → Q}
    {S : Set M} [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) (x : S) :
    (quotientEquiv hq hcompat).symm (imageProject q S x) =
      Quotient.mk (MulAction.orbitRel G S) x := by
  rw [← quotientEquiv_mk hq hcompat x, Equiv.symm_apply_apply]

private def InvariantSubsetQuotient.quotientHomeomorph {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) :
    Quotient (MulAction.orbitRel G S) ≃ₜ q '' S
    where
  toEquiv := quotientEquiv hq hcompat
  continuous_toFun :=
    isQuotientMap_quotient_mk'.continuous_iff.mpr (imageProject_continuous hq.continuous)
  continuous_invFun := by
    apply (imageProject_isQuotientCoveringMap hq hcompat).toIsQuotientMap.continuous_iff.mpr
    change Continuous ((quotientEquiv hq hcompat).symm ∘ imageProject q S)
    have he :
      (quotientEquiv hq hcompat).symm ∘ imageProject q S = Quotient.mk (MulAction.orbitRel G S) :=
      by
      funext x
      exact quotientEquiv_symm_imageProject hq hcompat x
    rw [he]
    exact continuous_quotient_mk'

public
theorem InvariantSubsetQuotient.isClosed_image {M Q : Type*} {q : M → Q} {S : Set M}
    [TopologicalSpace M] [TopologicalSpace Q] {G : Type*} [Group G] [MulAction G M]
    [MulAction G S] (hq : IsQuotientCoveringMap q G)
    (hcompat : ∀ (g : G) (x : S), ((g • x : S) : M) = g • (x : M)) (hS : IsClosed S) :
    IsClosed (q '' S) := by
  apply hq.isCoinducing.isClosed_preimage.mp
  rwa [InvariantSubsetQuotient.preimage_image_eq hq hcompat]

private def CoveringOrthant.localChart {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) :
    OpenPartialHomeomorph Q H :=
  (hq.isCoveringMap.isLocalHomeomorph.localInverseAt a).trans e

private theorem CoveringOrthant.self_mem_localChart_source {G M Q H : Type*} [Group G]
    [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) (ha : a ∈ e.source) :
    q a ∈ (localChart hq e a).source := by
  change
    q a ∈ (hq.isCoveringMap.isLocalHomeomorph.localInverseAt a).source ∧
      hq.isCoveringMap.isLocalHomeomorph.localInverseAt a (q a) ∈ e.source
  exact
    ⟨hq.isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source, by
      simpa only [IsLocalHomeomorph.localInverseAt_apply_self] using ha⟩

private theorem CoveringOrthant.localChart_symm {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) :
    ((localChart hq e a).symm : H → Q) = q ∘ e.symm := by
  simp only [localChart, OpenPartialHomeomorph.coe_trans_symm,
    IsLocalHomeomorph.localInverseAt_symm]

@[simp]
private theorem
    CoveringOrthant.localChart_symm_apply {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) (z : H) :
    (localChart hq e a).symm z = q (e.symm z) := by rw [localChart_symm, Function.comp_apply]

private theorem
    CoveringOrthant.localChart_target_subset {G M Q H : Type*} [Group G] [TopologicalSpace M]
    [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) :
    (localChart hq e a).target ⊆ e.target := fun _ hz => hz.1

private theorem CoveringOrthant.localChart_coordinate_identity {G M Q H : Type*} [Group G]
    [TopologicalSpace M] [TopologicalSpace Q] [TopologicalSpace H] [MulAction G M] {q : M → Q}
    (hq : IsQuotientCoveringMap q G) (e : OpenPartialHomeomorph M H) (a : M) {R : Type*}
    (f : Q → R) (F : H → R) (he : ∀ x ∈ e.source, f (q x) = F (e x)) :
    ∀ z ∈ (localChart hq e a).target, f ((localChart hq e a).symm z) = F z := by
  intro z hz
  have hze := localChart_target_subset hq e a hz
  rw [localChart_symm_apply, he (e.symm z) (e.map_target hze), e.right_inv hze]

end Mathoverflow1973

end
