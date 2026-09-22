/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Degree.FrobeniusFixedField
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianSubextension
import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.NormTopology
/-!
# Continuity of the normalized valuation

The proof uses the neighbourhoods `f ℤ̂`.  We construct the
required unramified extension of degree `f` as the fixed field of the kernel
of reduction modulo `f` after the normalized degree map `d_K`.  The norm--valuation formula then
sends its norm subgroup into the prescribed neighbourhood.
-/

noncomputable section

open scoped Topology

namespace ClassFormation

open ClassFormation CyclicCohomology KummerTheory

universe u

section DegreeOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Reduction modulo `f` after the normalized degree `d_K`. -/
def unramifiedDegreeHom (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f) :
    K.toSubgroup →ₜ* Multiplicative (ZMod f) :=
  (zHatReductionMul f hf).comp (D.normalizedDegree K)

/-- The subgroup of `G_K` fixing the degree-`f` unramified extension. -/
def unramifiedDegreeKernelWithin (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f) :
    Subgroup K.toSubgroup :=
  (unramifiedDegreeHom D K f hf).toMonoidHom.ker

/-- The defining kernel equation for the reduction subgroup. -/
theorem unramifiedDegreeKernelWithin_eq_ker (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f) :
    unramifiedDegreeKernelWithin D K f hf =
      (unramifiedDegreeHom D K f hf).toMonoidHom.ker := by
  rfl

/--
The kernel of normalized degree modulo a positive integer is closed inside the finite-residue
field subgroup.
-/
theorem unramifiedDegreeKernelWithin_isClosed (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    IsClosed (unramifiedDegreeKernelWithin D K f hf :
      Set K.toSubgroup) := by
  change IsClosed
    ((unramifiedDegreeHom D K f hf) ⁻¹' ({1} :
      Set (Multiplicative (ZMod f))))
  exact isClosed_singleton.preimage
    (unramifiedDegreeHom D K f hf).continuous_toFun

/-- The actual fixed field of the reduction-modulo-`f` kernel of `d_K`. -/
def unramifiedExtensionOfDegree (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) : ClosedSubgroup G where
  toSubgroup :=
    (unramifiedDegreeKernelWithin D K f hf).map K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      (Subtype.val ''
        (unramifiedDegreeKernelWithin D K f hf : Set K.toSubgroup))
    exact K.field.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      (unramifiedDegreeKernelWithin_isClosed D K f hf)

/--
Characterizes `g ∈ unramifiedExtensionOfDegree D K f hf` by the equivalent condition `∃ k :
K.toSubgroup, k ∈ unramifiedDegreeKernelWithin D K f hf ∧ k.1 = g`.
-/
@[simp]
theorem mem_unramifiedExtensionOfDegree_iff (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) (g : G) :
    g ∈ unramifiedExtensionOfDegree D K f hf ↔
      ∃ k : K.toSubgroup,
        k ∈ unramifiedDegreeKernelWithin D K f hf ∧ k.1 = g :=
  Iff.rfl

/-- Proves the bound `(unramifiedExtensionOfDegree D K f hf).toSubgroup ≤ K.toSubgroup`. -/
theorem unramifiedExtensionOfDegree_le (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    (unramifiedExtensionOfDegree D K f hf).toSubgroup ≤
      K.toSubgroup := by
  rintro g ⟨k, _, rfl⟩
  exact k.2

/--
Establishes the identity `extensionSubgroup K.field (unramifiedExtensionOfDegree D K f hf)
(unramifiedExtensionOfDegree_le D K f hf) = unramifiedDegreeKernelWithin D K f hf`.
-/
theorem extensionSubgroup_unramifiedExtensionOfDegree (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    extensionSubgroup K.field (unramifiedExtensionOfDegree D K f hf)
        (unramifiedExtensionOfDegree_le D K f hf) =
      unramifiedDegreeKernelWithin D K f hf := by
  ext k
  constructor
  · intro hk
    obtain ⟨t, ht, hts⟩ := hk
    have htk : t = k := by
      apply Subtype.ext
      exact hts
    simpa [htk] using ht
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- The specified map is surjective: `Function.Surjective (unramifiedDegreeHom D K f hf)`. -/
theorem unramifiedDegreeHom_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    Function.Surjective (unramifiedDegreeHom D K f hf) := by
  intro z
  obtain ⟨w, hw⟩ := zHatReduction_surjective f hf z.toAdd
  obtain ⟨k, hk⟩ :=
    D.normalizedDegree_surjective K (Multiplicative.ofAdd w)
  refine ⟨k, ?_⟩
  apply Multiplicative.ext
  change zHatReduction f hf (D.normalizedDegree K k).toAdd = z.toAdd
  rw [hk]
  exact hw

/--
The extension subgroup of the canonical unramified degree-`f` extension is normal.
-/
instance unramifiedExtensionOfDegree_normal (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    (extensionSubgroup K.field (unramifiedExtensionOfDegree D K f hf)
      (unramifiedExtensionOfDegree_le D K f hf)).Normal := by
  rw [extensionSubgroup_unramifiedExtensionOfDegree D K f hf]
  change (unramifiedDegreeHom D K f hf).toMonoidHom.ker.Normal
  infer_instance

/-- The reduction kernel packages an actual finite Galois extension of `K`. -/
def finiteUnramifiedExtension (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) : FiniteGaloisSubextension K.field where
  field := unramifiedExtensionOfDegree D K f hf
  below := unramifiedExtensionOfDegree_le D K f hf
  normal := inferInstance
  finite := by
    rw [extensionSubgroup_unramifiedExtensionOfDegree D K f hf]
    let : NeZero f := ⟨Nat.ne_of_gt hf⟩
    let : Finite (Multiplicative (ZMod f)) := by
      change Finite (ZMod f)
      infer_instance
    let q := (unramifiedDegreeHom D K f hf).toMonoidHom
    exact Finite.of_injective
      (QuotientGroup.quotientKerEquivOfSurjective q
        (unramifiedDegreeHom_surjective D K f hf))
      (QuotientGroup.quotientKerEquivOfSurjective q
        (unramifiedDegreeHom_surjective D K f hf)).injective

/-- The extension subgroup carried by the bundled finite unramified
extension is the reduction kernel used to construct it. -/
theorem extensionSubgroup_finiteUnramifiedExtension
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f) :
    extensionSubgroup K.field (D.finiteUnramifiedExtension K f hf).field
        (D.finiteUnramifiedExtension K f hf).below =
      unramifiedDegreeKernelWithin D K f hf := by
  simpa only [finiteUnramifiedExtension] using
    extensionSubgroup_unramifiedExtensionOfDegree D K f hf

/-- The finite unramified extension is abelian: its Galois quotient is the
cyclic quotient detected by the normalized degree modulo `f`. -/
def finiteUnramifiedAbelianExtension (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) : FiniteAbelianSubextension K.field where
  toFiniteGaloisExtension := finiteUnramifiedExtension D K f hf
  commutative := by
    let :
        (extensionSubgroup K.field
          (D.finiteUnramifiedExtension K f hf).field
          (D.finiteUnramifiedExtension K f hf).below).Normal :=
      (D.finiteUnramifiedExtension K f hf).normal
    change IsMulCommutative
      (K.toSubgroup ⧸
        extensionSubgroup K.field
          (D.finiteUnramifiedExtension K f hf).field
          (D.finiteUnramifiedExtension K f hf).below)
    let q := (unramifiedDegreeHom D K f hf).toMonoidHom
    have hsub :
        extensionSubgroup K.field
            (D.finiteUnramifiedExtension K f hf).field
            (D.finiteUnramifiedExtension K f hf).below =
          q.ker := by
      rw [D.extensionSubgroup_finiteUnramifiedExtension K f hf,
        D.unramifiedDegreeKernelWithin_eq_ker K f hf]
    let e :
        (K.toSubgroup ⧸
            extensionSubgroup K.field
              (D.finiteUnramifiedExtension K f hf).field
              (D.finiteUnramifiedExtension K f hf).below) ≃*
          Multiplicative (ZMod f) :=
      (QuotientGroup.quotientMulEquivOfEq hsub).trans
        (QuotientGroup.quotientKerEquivOfSurjective q
          (unramifiedDegreeHom_surjective D K f hf))
    exact
      { is_comm.comm := fun x y => by
          apply e.injective
          rw [map_mul, map_mul, mul_comm] }

/-- Forgetting commutativity from the abelian package recovers the canonical
finite unramified Galois extension. -/
@[simp]
theorem finiteUnramifiedAbelianExtension_toFiniteGaloisExtension
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    (D.finiteUnramifiedAbelianExtension K f hf).toFiniteGaloisExtension =
      D.finiteUnramifiedExtension K f hf := by
  rfl

/-- The reduction kernel contains inertia, so its fixed field is unramified. -/
theorem unramifiedExtensionOfDegree_isUnramified (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    (DegreeData.AbstractExtension.mk (unramifiedExtensionOfDegree D K f hf) K.field
      (unramifiedExtensionOfDegree_le D K f hf)).IsUnramified D := by
  rw [(DegreeData.AbstractExtension.mk
    (unramifiedExtensionOfDegree D K f hf) K.field
    (unramifiedExtensionOfDegree_le D K f hf)).isUnramified_iff_inertia_le D]
  rintro g ⟨hgK, hgI⟩
  let k : K.toSubgroup := ⟨g, hgK⟩
  have hkI : k ∈ D.fieldInertiaWithin K.field := hgI
  have hkDegree : D.normalizedDegree K k = 1 := by
    have hkKer : k ∈ (D.normalizedDegree K).toMonoidHom.ker := by
      rw [D.normalizedDegree_ker K]
      exact hkI
    exact hkKer
  have hkReduction :
      k ∈ unramifiedDegreeKernelWithin D K f hf := by
    change unramifiedDegreeHom D K f hf k = 1
    change zHatReductionMul f hf (D.normalizedDegree K k) = 1
    rw [hkDegree, map_one]
  exact ⟨k, hkReduction, rfl⟩

/-- The finite extension cut out by reduction modulo `f` has positive degree
`f`. -/
theorem finiteUnramifiedExtension_degree (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    (((finiteUnramifiedExtension D K f hf).toFiniteAbstractExtension.degree : ℕ)) = f := by
  let : NeZero f := ⟨hf.ne'⟩
  let : Fintype (ZMod f) := ZMod.fintype f
  let q := (unramifiedDegreeHom D K f hf).toMonoidHom
  rw [← (finiteUnramifiedExtension D K f
    hf).toFiniteAbstractExtension.extensionSubgroup_index_eq_degree]
  change (extensionSubgroup K.field
      (D.finiteUnramifiedExtension K f hf).field
      (D.finiteUnramifiedExtension K f hf).below).index = f
  rw [D.extensionSubgroup_finiteUnramifiedExtension K f hf]
  rw [D.unramifiedDegreeKernelWithin_eq_ker K f hf]
  rw [Subgroup.index_ker]
  rw [MonoidHom.range_eq_top_of_surjective q
    (unramifiedDegreeHom_surjective D K f hf)]
  calc
    Nat.card (↑(⊤ : Subgroup (Multiplicative (ZMod f)))) =
        Nat.card (Multiplicative (ZMod f)) :=
      Nat.card_congr
        { toFun := fun x ↦ x.1
          invFun := fun x ↦ ⟨x, Subgroup.mem_top x⟩
          left_inv := fun x ↦ Subtype.ext rfl
          right_inv := fun _ ↦ rfl }
    _ = Nat.card (ZMod f) :=
      Nat.card_congr
        { toFun := Multiplicative.toAdd
          invFun := Multiplicative.ofAdd
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    _ = f := Nat.card_zmod f

/-- Thus the positive relative residue degree is also `f`. -/
theorem finiteUnramifiedExtension_residueDegree (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) (hf : 0 < f) :
    (((finiteUnramifiedExtension D K f hf).toFiniteAbstractExtension.residueDegree D : ℕ)) = f := by
  let E := (finiteUnramifiedExtension D K f hf).toFiniteAbstractExtension
  have hE : E.IsUnramified D := by
    simpa [E, finiteUnramifiedExtension,
      FiniteGaloisSubextension.toFiniteAbstractExtension] using
      unramifiedExtensionOfDegree_isUnramified D K f hf
  rw [E.residueDegree_eq_degree_of_isUnramified D hE]
  exact finiteUnramifiedExtension_degree D K f hf

end DegreeData

end DegreeOnly

section Representation

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- Every neighbourhood of zero in the value group contains all `f`-fold
multiples for some `f > 0`.  This is the subspace-topology form of the
neighbourhood basis `f ℤ̂`. -/
theorem exists_nsmul_mem_of_valueGroup_mem_nhds
    (v : ValuationData D A) {U : Set v.valueGroup}
    (hU : U ∈ 𝓝 (0 : v.valueGroup)) :
    ∃ f : ℕ, 0 < f ∧ ∀ z : v.valueGroup, f • z ∈ U := by
  rcases (mem_nhds_subtype (v.valueGroup : Set ZHat)
    (0 : v.valueGroup) U).1 hU with ⟨W, hW, hWU⟩
  rcases mem_nhds_iff.mp hW with ⟨W₀, hW₀W, hW₀open, hzero⟩
  let Wm : Set ZHatMul := {z | z.toAdd ∈ W₀}
  have hWmOpen : IsOpen Wm := by
    change IsOpen W₀
    exact hW₀open
  have hone : (1 : ZHatMul) ∈ Wm := by
    change (0 : ZHat) ∈ W₀
    exact hzero
  let : TotallyDisconnectedSpace ZHatMul := by
    change TotallyDisconnectedSpace ZHat
    infer_instance
  obtain ⟨H, hHWm⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (G := ZHatMul) hWmOpen hone
  let HAdd : AddSubgroup ZHat :=
    Subgroup.toAddSubgroup' (H : Subgroup ZHatMul)
  let : Finite (ZHatMul ⧸ (H : Subgroup ZHatMul)) :=
    Subgroup.quotient_finite_of_isOpen (H : Subgroup ZHatMul)
      H.toOpenSubgroup.isOpen'
  have hindex : HAdd.index ≠ 0 := by
    change (H : Subgroup ZHatMul).index ≠ 0
    exact (H : Subgroup ZHatMul).index_ne_zero_of_finite
  let f := HAdd.index
  have hf : f ≠ 0 := hindex
  have hHAdd :
      HAdd = (zHatMulNat f).toAddMonoidHom.range := by
    simpa only [f] using
      zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero HAdd hindex
  refine ⟨f, Nat.pos_of_ne_zero hf, ?_⟩
  intro z
  apply hWU
  apply hW₀W
  have hzHAdd : f • (z.1 : ZHat) ∈ HAdd := by
    rw [hHAdd]
    exact ⟨z.1, zHatMulNat_apply f z.1⟩
  have hzH : Multiplicative.ofAdd (f • (z.1 : ZHat)) ∈
      (H : Subgroup ZHatMul) := hzHAdd
  exact hHWm hzH

/-- **continuity of the normalized valuation.** The normalized valuation is continuous from the
norm topology on `A_K` to the value group with its `ℤ̂`-subspace topology. -/
theorem normTopology_valuation_continuous
    [IsTopologicalGroup G] (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    IsContinuousFromNormTopology A K.field (v.valuationAt K) := by
  unfold IsContinuousFromNormTopology
  let : TopologicalSpace (ambientFixedAddSubgroup A K.field) :=
    normTopology A K.field
  let : IsTopologicalAddGroup (ambientFixedAddSubgroup A K.field) :=
    (normFilterBasis A K.field).isTopologicalAddGroup
  apply continuous_of_continuousAt_zero (v.valuationAt K)
  rw [ContinuousAt, map_zero]
  rw [(normFilterBasis A K.field).nhds_zero_hasBasis.tendsto_left_iff]
  intro U hU
  obtain ⟨f, hf, hfU⟩ := exists_nsmul_mem_of_valueGroup_mem_nhds v hU
  let Kresidue : DegreeData.FiniteResidueAbstractField D :=
    K.toFiniteResidueAbstractField D
  let L : FiniteGaloisSubextension K.field :=
    DegreeData.finiteUnramifiedExtension D Kresidue f hf
  let hLfinite : Finite
      (K.field.toSubgroup ⧸ extensionSubgroup K.field L.field L.below) := L.finite
  let hLabsoluteFinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) L.field (le_baseField L.field)) :=
    relativeTowerQuotientFinite (baseField G) K.field L.field L.below
      (le_baseField K.field)
  let Lfinite : FiniteAbstractField G := ⟨L.field, hLabsoluteFinite⟩
  let E : FiniteAbstractFieldExtension G :=
    { field := Lfinite
      base := K
      below := L.below
      finiteQuotient := L.finite }
  refine ⟨(FiniteGaloisSubextension.normSubgroup A L :
      Set (ambientFixedAddSubgroup A K.field)),
    ⟨L, rfl⟩, ?_⟩
  intro x hx
  change x ∈ FiniteGaloisSubextension.normSubgroup A L at hx
  rcases hx with ⟨a, rfl⟩
  have hres : (E.residueDegree D : ℕ) = f := by
    change ((L.toFiniteAbstractExtension.residueDegree D : ℕ)) = f
    simpa only [L] using
      DegreeData.finiteUnramifiedExtension_residueDegree D Kresidue f hf
  have hvaluation :
      v.valuationAt K (relativeNorm A K.field L.field L.below a) =
        f • v.valuationAt Lfinite a := by
    apply Subtype.ext
    change ((v.valuationAt K
      (relativeNorm A K.field L.field L.below a) : v.valueGroup) : ZHat) =
        f • ((v.valuationAt Lfinite a : v.valueGroup) : ZHat)
    rw [← hres]
    exact (v.normalizedValuation_tower E a).symm
  rw [hvaluation]
  exact hfU (v.valuationAt Lfinite a)

end ValuationData

end Representation

end ClassFormation
