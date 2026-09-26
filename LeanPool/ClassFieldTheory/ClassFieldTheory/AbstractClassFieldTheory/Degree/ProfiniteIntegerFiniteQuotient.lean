/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.GroupTheory.Archimedean
public import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import LeanPool.ClassFieldTheory.GaloisCohomology.ProfiniteIntegers.ProfiniteIntegerCore

/-! # Profinite Integer Finite Quotient -/

@[expose] public section
namespace ClassFormation

open CategoryTheory CategoryTheory.Limits

/-!
# Finite quotient reductions of profinite integers

This module extends the concrete `ZHat` reduction maps to every finite-index
additive quotient of `ℤ`.  The construction first identifies such a subgroup
with the multiples of its index, then uses the existing reduction to `ZMod`
and Mathlib's `ZMod.lift`.
-/

noncomputable
section

private theorem finiteIndexNormalAddSubgroup_eq_zmultiples_index
    (H : FiniteIndexNormalAddSubgroup ℤ) :
    H.toAddSubgroup =
      AddSubgroup.zmultiples (H.toAddSubgroup.index : ℤ) := by
  obtain ⟨d, hd⟩ := Int.subgroup_cyclic H.toAddSubgroup
  have hH : H.toAddSubgroup = AddSubgroup.zmultiples d :=
    hd.trans (AddSubgroup.zmultiples_eq_closure d).symm
  have hindex : H.toAddSubgroup.index = d.natAbs := by
    rw [hH, Int.index_zmultiples]
  calc
    H.toAddSubgroup = AddSubgroup.zmultiples d := hH
    _ = AddSubgroup.zmultiples (d.natAbs : ℤ) :=
      (Int.zmultiples_natAbs d).symm
    _ = AddSubgroup.zmultiples (H.toAddSubgroup.index : ℤ) := by
      rw [hindex]

private theorem finiteIndexNormalAddSubgroup_index_pos
    (H : FiniteIndexNormalAddSubgroup ℤ) :
    0 < H.toAddSubgroup.index :=
  Nat.pos_of_ne_zero H.isFiniteIndex'.index_ne_zero

private theorem finiteIndexNormalAddSubgroup_index_mem
    (H : FiniteIndexNormalAddSubgroup ℤ) :
    (H.toAddSubgroup.index : ℤ) ∈ H.toAddSubgroup := by
  let n := H.toAddSubgroup.index
  change (n : ℤ) ∈ H.toAddSubgroup
  have hH : H.toAddSubgroup = AddSubgroup.zmultiples (n : ℤ) := by
    simpa only [n] using finiteIndexNormalAddSubgroup_eq_zmultiples_index H
  rw [hH, Int.mem_zmultiples_iff]

/-- Reduction modulo the subgroup index followed by the corresponding integer quotient map. -/
noncomputable def zHatFiniteIndexQuotientReduction
    (H : FiniteIndexNormalAddSubgroup ℤ) :
    ZMod H.toAddSubgroup.index →+ ℤ ⧸ H.toAddSubgroup :=
  ZMod.lift H.toAddSubgroup.index
    ⟨QuotientAddGroup.mk' H.toAddSubgroup, by
      change ((H.toAddSubgroup.index : ℤ) : ℤ ⧸ H.toAddSubgroup) = 0
      exact (QuotientAddGroup.eq_zero_iff _).mpr
        (finiteIndexNormalAddSubgroup_index_mem H)⟩

/-- The canonical reduction of `ZHat` to the finite quotient of `ℤ` by `H`. -/
noncomputable def zHatReductionToFiniteIndexQuotient
    (H : FiniteIndexNormalAddSubgroup ℤ) :
    ZHat →ₜ+ ℤ ⧸ H.toAddSubgroup := by
  let quotientReduction :
      ZMod H.toAddSubgroup.index →ₜ+ ℤ ⧸ H.toAddSubgroup :=
    { toAddMonoidHom := zHatFiniteIndexQuotientReduction H
      continuous_toFun := continuous_of_discreteTopology }
  exact quotientReduction.comp
    (zHatReduction H.toAddSubgroup.index
      (by exact finiteIndexNormalAddSubgroup_index_pos H))

/-- The finite quotient reduction extends the ordinary quotient map on integers. -/
@[simp]
theorem zHatReductionToFiniteIndexQuotient_intCast
    (H : FiniteIndexNormalAddSubgroup ℤ) (a : ℤ) :
    zHatReductionToFiniteIndexQuotient H (a : ZHat) =
      QuotientAddGroup.mk' H.toAddSubgroup a := by
  change zHatFiniteIndexQuotientReduction H
      (zHatReduction H.toAddSubgroup.index
        (by exact finiteIndexNormalAddSubgroup_index_pos H) (a : ZHat)) =
    QuotientAddGroup.mk' H.toAddSubgroup a
  rw [zHatReduction_intCast]
  unfold zHatFiniteIndexQuotientReduction
  exact ZMod.lift_coe H.toAddSubgroup.index _ a

/-- The reduction to a finite-index quotient, regarded as a leg of the
finite-quotient diagram defining Mathlib's profinite completion of `ℤ`. -/
noncomputable def zHatFiniteIndexQuotientDiagramLeg
    (H : FiniteIndexNormalAddSubgroup ℤ) :
    zHatProfiniteAddGrp ⟶
      (ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ)).obj H := by
  change zHatProfiniteAddGrp ⟶
    ProfiniteAddGrp.ofFiniteAddGrp
      (FiniteAddGrp.of (ℤ ⧸ H.toAddSubgroup))
  let Q := FiniteAddGrp.of (ℤ ⧸ H.toAddSubgroup)
  letI : TopologicalSpace Q := ⊥
  letI : DiscreteTopology Q := discreteTopology_bot Q
  let quotientReduction : ZMod H.toAddSubgroup.index →ₜ+ Q :=
    { toAddMonoidHom := zHatFiniteIndexQuotientReduction H
      continuous_toFun := continuous_of_discreteTopology }
  let reduction : ZHat →ₜ+ Q :=
    quotientReduction.comp
      (zHatReduction H.toAddSubgroup.index
        (by exact finiteIndexNormalAddSubgroup_index_pos H))
  exact ProfiniteAddGrp.ofHom reduction

/-- The diagram leg agrees with quotient reduction on the dense copy of
the integers in `ZHat`. -/
@[simp]
theorem zHatFiniteIndexQuotientDiagramLeg_intCast
    (H : FiniteIndexNormalAddSubgroup ℤ) (a : ℤ) :
    (zHatFiniteIndexQuotientDiagramLeg H).hom (a : ZHat) =
      QuotientAddGroup.mk' H.toAddSubgroup a := by
  change zHatReductionToFiniteIndexQuotient H (a : ZHat) =
    QuotientAddGroup.mk' H.toAddSubgroup a
  exact zHatReductionToFiniteIndexQuotient_intCast H a

/-- The finite-quotient reductions form a cone over the diagram of finite
index quotients of `ℤ`. -/
theorem zHatFiniteIndexQuotientDiagramLeg_naturality
    {H K : FiniteIndexNormalAddSubgroup ℤ} (f : H ⟶ K) :
    zHatFiniteIndexQuotientDiagramLeg H ≫
        (ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ)).map f =
      zHatFiniteIndexQuotientDiagramLeg K := by
  let intCast : ℤ → zHatProfiniteAddGrp := fun a => (a : ZHat)
  have hdense : DenseRange intCast := by
    change DenseRange (Int.castRingHom ZHat)
    exact denseRange_intCast_zHat
  have hfun :
      ((zHatFiniteIndexQuotientDiagramLeg H ≫
          (ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ)).map f).hom :
        zHatProfiniteAddGrp → _) =
        (zHatFiniteIndexQuotientDiagramLeg K).hom :=
    hdense.equalizer
      ((zHatFiniteIndexQuotientDiagramLeg H ≫
        (ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ)).map f).hom.continuous_toFun)
      (zHatFiniteIndexQuotientDiagramLeg K).hom.continuous_toFun (by
        funext a
        change
          ((ProfiniteAddGrp.ProfiniteCompletion.diagram
            (AddGrpCat.of ℤ)).map f).hom
              ((zHatFiniteIndexQuotientDiagramLeg H).hom (a : ZHat)) =
            (zHatFiniteIndexQuotientDiagramLeg K).hom (a : ZHat)
        rw [zHatFiniteIndexQuotientDiagramLeg_intCast H a,
          zHatFiniteIndexQuotientDiagramLeg_intCast K a]
        rfl)
  exact ConcreteCategory.hom_ext _ _ fun x => congrFun hfun x

/-- The finite quotient reductions of `ZHat` are a cone over the finite-index
quotient diagram used by Mathlib to define the profinite completion of `ℤ`. -/
noncomputable def zHatFiniteIndexQuotientCone :
    Cone (ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ)) where
  pt := zHatProfiniteAddGrp
  π :=
    { app := zHatFiniteIndexQuotientDiagramLeg
      naturality := by
        intro H K f
        change 𝟙 zHatProfiniteAddGrp ≫ zHatFiniteIndexQuotientDiagramLeg K =
          zHatFiniteIndexQuotientDiagramLeg H ≫
            (ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ)).map f
        simpa only [Category.id_comp] using
          (zHatFiniteIndexQuotientDiagramLeg_naturality f).symm }

/-- The continuous additive map from `ZHat` to Mathlib's profinite completion
of the additive group of integers, induced by its finite quotient reductions. -/
noncomputable def zHatToIntegerProfiniteCompletion :
    zHatProfiniteAddGrp ⟶
      ProfiniteAddGrp.ProfiniteCompletion.completion (AddGrpCat.of ℤ) :=
  (ProfiniteAddGrp.limitConeIsLimit
    (ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ))).lift
      zHatFiniteIndexQuotientCone

/-- Projecting the induced map to a finite quotient recovers its reduction map. -/
theorem zHatToIntegerProfiniteCompletion_fac
    (H : FiniteIndexNormalAddSubgroup ℤ) :
    zHatToIntegerProfiniteCompletion ≫
        (ProfiniteAddGrp.limitCone
          (ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ))).π.app H =
      zHatFiniteIndexQuotientDiagramLeg H := by
  exact (ProfiniteAddGrp.limitConeIsLimit
    (ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ))).fac
      zHatFiniteIndexQuotientCone H

/-- On ordinary integers, the induced map is Mathlib's canonical completion map. -/
theorem zHatToIntegerProfiniteCompletion_intCast
    (a : ℤ) :
    zHatToIntegerProfiniteCompletion (a : ZHat) =
      ProfiniteAddGrp.ProfiniteCompletion.etaFn (AddGrpCat.of ℤ) a := by
  apply Subtype.ext
  funext H
  change
    ((ProfiniteAddGrp.limitCone
      (ProfiniteAddGrp.ProfiniteCompletion.diagram (AddGrpCat.of ℤ))).π.app H).hom
        (zHatToIntegerProfiniteCompletion (a : ZHat)) =
      QuotientAddGroup.mk' H.toAddSubgroup a
  rw [← zHatFiniteIndexQuotientDiagramLeg_intCast H a]
  exact ConcreteCategory.congr_hom
    (zHatToIntegerProfiniteCompletion_fac H) (a : ZHat)

private theorem zHatFiniteIndexQuotientReduction_injective
    (H : FiniteIndexNormalAddSubgroup ℤ) :
    Function.Injective (zHatFiniteIndexQuotientReduction H) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  have hquotient :
      QuotientAddGroup.mk' H.toAddSubgroup a =
        QuotientAddGroup.mk' H.toAddSubgroup b := by
    simpa only [zHatFiniteIndexQuotientReduction, ZMod.lift_coe] using hxy
  have hmem : a - b ∈ H.toAddSubgroup :=
    (QuotientAddGroup.eq_iff_sub_mem).mp hquotient
  rw [finiteIndexNormalAddSubgroup_eq_zmultiples_index H,
    Int.mem_zmultiples_iff] at hmem
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  simpa only [neg_sub] using dvd_neg.mpr hmem

private theorem zHatToIntegerProfiniteCompletion_injective :
    Function.Injective
      (fun z : ZHat => zHatToIntegerProfiniteCompletion z) := by
  intro x y hxy
  apply ZHat.ext
  intro n hn
  have hnatAbs : (n : ℤ).natAbs = n := by
    cases n <;> rfl
  let H : FiniteIndexNormalAddSubgroup ℤ :=
    { toAddSubgroup := AddSubgroup.zmultiples (n : ℤ)
      isFiniteIndex' :=
        ⟨by
          simpa only [Int.index_zmultiples, hnatAbs] using
            Nat.ne_of_gt hn⟩ }
  have hindex : H.toAddSubgroup.index = n := by
    simp only [H, Int.index_zmultiples, hnatAbs]
  have hprojection := congrArg
    (fun z =>
      ((ProfiniteAddGrp.limitCone
        (ProfiniteAddGrp.ProfiniteCompletion.diagram
          (AddGrpCat.of ℤ))).π.app H).hom z)
    hxy
  have hleg :
      (zHatFiniteIndexQuotientDiagramLeg H).hom x =
        (zHatFiniteIndexQuotientDiagramLeg H).hom y := by
    calc
      (zHatFiniteIndexQuotientDiagramLeg H).hom x =
          ((ProfiniteAddGrp.limitCone
            (ProfiniteAddGrp.ProfiniteCompletion.diagram
              (AddGrpCat.of ℤ))).π.app H).hom
            (zHatToIntegerProfiniteCompletion x) :=
        (ConcreteCategory.congr_hom
          (zHatToIntegerProfiniteCompletion_fac H) x).symm
      _ = ((ProfiniteAddGrp.limitCone
            (ProfiniteAddGrp.ProfiniteCompletion.diagram
              (AddGrpCat.of ℤ))).π.app H).hom
            (zHatToIntegerProfiniteCompletion y) := hprojection
      _ = (zHatFiniteIndexQuotientDiagramLeg H).hom y :=
        ConcreteCategory.congr_hom
          (zHatToIntegerProfiniteCompletion_fac H) y
  have hreduction :
      zHatReduction H.toAddSubgroup.index
          (by exact finiteIndexNormalAddSubgroup_index_pos H) x =
        zHatReduction H.toAddSubgroup.index
          (by exact finiteIndexNormalAddSubgroup_index_pos H) y := by
    apply zHatFiniteIndexQuotientReduction_injective H
    change zHatReductionToFiniteIndexQuotient H x =
      zHatReductionToFiniteIndexQuotient H y
    exact hleg
  have hreductionAll :
      ∀ hm : 0 < H.toAddSubgroup.index,
        zHatReduction H.toAddSubgroup.index hm x =
          zHatReduction H.toAddSubgroup.index hm y := by
    intro hm
    exact hreduction
  have hreductionAtN :
      ∀ hm : 0 < n,
        zHatReduction n hm x = zHatReduction n hm y :=
    hindex ▸ hreductionAll
  exact hreductionAtN hn

private theorem zHatToIntegerProfiniteCompletion_surjective :
    Function.Surjective
      (fun z : ZHat => zHatToIntegerProfiniteCompletion z) := by
  have hsubset :
      Set.range
          (ProfiniteAddGrp.ProfiniteCompletion.etaFn
            (AddGrpCat.of ℤ)) ⊆
        Set.range (fun z : ZHat => zHatToIntegerProfiniteCompletion z) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨(a : ZHat), zHatToIntegerProfiniteCompletion_intCast a⟩
  have hdense : DenseRange
      (fun z : ZHat => zHatToIntegerProfiniteCompletion z) :=
    (ProfiniteAddGrp.ProfiniteCompletion.denseRange
      (G := AddGrpCat.of ℤ)).mono hsubset
  have hclosed : IsClosed
      (Set.range (fun z : ZHat => zHatToIntegerProfiniteCompletion z)) :=
    zHatToIntegerProfiniteCompletion.hom.continuous_toFun.isClosedMap.isClosed_range
  rw [← Set.range_eq_univ, ← closure_eq_iff_isClosed.mpr hclosed,
    Dense.closure_eq hdense]

/-- The canonical topological additive equivalence between `ZHat` and the
profinite completion of the additive group of integers. -/
noncomputable def zHatContinuousAddEquivIntegerProfiniteCompletion :
    ZHat ≃ₜ+
      ProfiniteAddGrp.ProfiniteCompletion.completion (AddGrpCat.of ℤ) := by
  have hcontinuous :
      Continuous (fun z : ZHat => zHatToIntegerProfiniteCompletion z) := by
    exact zHatToIntegerProfiniteCompletion.hom.continuous_toFun
  exact
    { (Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofBijective
        (fun z : ZHat => zHatToIntegerProfiniteCompletion z)
        ⟨by exact zHatToIntegerProfiniteCompletion_injective,
          by exact zHatToIntegerProfiniteCompletion_surjective⟩)
      hcontinuous) with
      map_add' := zHatToIntegerProfiniteCompletion.hom.map_add }

/-- The forward map of the completion equivalence is the finite-quotient
comparison map. -/
@[simp]
theorem zHatContinuousAddEquivIntegerProfiniteCompletion_apply (z : ZHat) :
    zHatContinuousAddEquivIntegerProfiniteCompletion z =
      zHatToIntegerProfiniteCompletion z :=
  rfl

/-- The canonical continuous additive map from the profinite completion of
the integers back to `ZHat`. -/
noncomputable def integerProfiniteCompletionToZHat :
    ProfiniteAddGrp.ProfiniteCompletion.completion (AddGrpCat.of ℤ) ⟶
      zHatProfiniteAddGrp :=
  ProfiniteAddGrp.ofHom
    (zHatContinuousAddEquivIntegerProfiniteCompletion.symm :
      ProfiniteAddGrp.ProfiniteCompletion.completion (AddGrpCat.of ℤ) →ₜ+ ZHat)

/-- The map from the profinite completion to `ZHat` extends the ordinary
integer embedding. -/
@[simp]
theorem integerProfiniteCompletionToZHat_etaFn (a : ℤ) :
    integerProfiniteCompletionToZHat
        (ProfiniteAddGrp.ProfiniteCompletion.etaFn (AddGrpCat.of ℤ) a) =
      (a : ZHat) := by
  change zHatContinuousAddEquivIntegerProfiniteCompletion.symm
      (ProfiniteAddGrp.ProfiniteCompletion.etaFn (AddGrpCat.of ℤ) a) =
    (a : ZHat)
  apply zHatContinuousAddEquivIntegerProfiniteCompletion.injective
  rw [zHatContinuousAddEquivIntegerProfiniteCompletion.apply_symm_apply]
  simpa only [zHatContinuousAddEquivIntegerProfiniteCompletion_apply] using
    (zHatToIntegerProfiniteCompletion_intCast a).symm

/-- The inverse map of the completion equivalence is the canonical comparison
map back to `ZHat`. -/
@[simp]
theorem zHatContinuousAddEquivIntegerProfiniteCompletion_symm_apply
    (x : ProfiniteAddGrp.ProfiniteCompletion.completion
      (AddGrpCat.of ℤ)) :
    zHatContinuousAddEquivIntegerProfiniteCompletion.symm x =
      integerProfiniteCompletionToZHat x :=
  rfl

end

end ClassFormation
