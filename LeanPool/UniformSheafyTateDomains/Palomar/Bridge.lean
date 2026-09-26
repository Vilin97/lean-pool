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
public import LeanPool.UniformSheafyTateDomains.Palomar.Defs
public import LeanPool.UniformSheafyTateDomains.AdicSpaces
public import Mathlib.Topology.Sheaves.Functors

/-!
# The Challenge's definitions are the library's

`Challenge.lean` restates the notions the certified theorems are phrased in — bounded
sets, Huber and Tate rings, the adic spectrum, rational localisations, the structure presheaf,
sheafiness — self-containedly on Mathlib, because Palomar forbids project source in a
Challenge's import closure. This file proves that each restatement agrees with the library's
own definition, so that a Challenge statement is the library's theorem and not a weaker
cousin of it.

Most agreements are definitional (`rfl`): the localisation topology, the completed rational
localisation `presheafValue`, the canonical maps. The ones that need an argument are:

* `spvEquiv` — the Challenge's `Spv` and the library's are distinct one-field structures
  wrapping `ValuativeRel`, so they are transported rather than identified;
* `RestrictionFamily.subsingleton` — any two families of restriction maps agree, by the
  universal property of the localisation, density of `Aₛ` in `A⟨T/s⟩`, and Hausdorffness;
* `isSheafy_iff` — the Challenge's `IsSheafy` (Mathlib's `TopCat.Presheaf.IsSheaf` for the
  structure presheaf built from any restriction family, valued in `TopCommRingCat`) is the
  library's `IsSheafy` (the finite rational-cover criterion), via the library's own
  `isSheafy_iff_structurePresheaf_forgetToTopCommRingCat_isSheaf`.
-/

@[expose] public section


noncomputable section

open CategoryTheory TopologicalSpace Opposite
open ValuationSpectrum

namespace PalomarBridge

universe u

/-! ### The valuation spectrum -/

section ValSpec

variable {A : Type u} [CommRing A]

/-- The Challenge's `Spv` and the library's are the same one-field wrapper of `ValuativeRel`. -/
def spvEquiv : Palomar.ValuationSpectrum A ≃ ValuationSpectrum A where
  toFun v := ⟨v.toValuativeRel⟩
  invFun v := ⟨v.toValuativeRel⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem spvEquiv_vle (v : Palomar.ValuationSpectrum A) (a b : A) :
    (spvEquiv v).vle a b ↔ v.vle a b := Iff.rfl

theorem spvEquiv_preimage_basicOpen (f s : A) :
    spvEquiv ⁻¹' basicOpen f s = Palomar.ValuationSpectrum.basicOpen f s := rfl

theorem spvEquiv_symm_preimage_basicOpen (f s : A) :
    spvEquiv.symm ⁻¹' Palomar.ValuationSpectrum.basicOpen f s = basicOpen f s := rfl

theorem spvEquiv_continuous : Continuous (spvEquiv (A := A)) := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro _ ⟨f, s, rfl⟩
  rw [spvEquiv_preimage_basicOpen]
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨f, s, rfl⟩

theorem spvEquiv_symm_continuous : Continuous (spvEquiv (A := A)).symm := by
  refine continuous_generateFrom_iff.mpr ?_
  rintro _ ⟨f, s, rfl⟩
  rw [spvEquiv_symm_preimage_basicOpen]
  exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨f, s, rfl⟩

/-- `spvEquiv` as a homeomorphism. -/
def spvHomeo : Palomar.ValuationSpectrum A ≃ₜ ValuationSpectrum A where
  toEquiv := spvEquiv
  continuous_toFun := spvEquiv_continuous
  continuous_invFun := spvEquiv_symm_continuous

end ValSpec

/-! ### The adic spectrum -/

section Spa

variable {A : Type u} [CommRing A] [TopologicalSpace A] [PlusSubring A]

/-- The library's `A⁺` read as the Challenge's. -/
instance palomarPlusSubring : Palomar.ValuationSpectrum.PlusSubring A := ⟨A⁺⟩

omit [TopologicalSpace A] in
theorem ringPlus_eq : Palomar.ValuationSpectrum.ringPlus A = A⁺ := rfl

theorem spvEquiv_preimage_Cont : spvEquiv ⁻¹' Cont A = Palomar.ValuationSpectrum.Cont A := rfl

theorem spvEquiv_preimage_Spa (B : Subring A) :
    spvEquiv ⁻¹' Spa A B = Palomar.ValuationSpectrum.Spa A B := rfl

theorem spvEquiv_preimage_rationalOpen (T : Finset A) (s : A) :
    spvEquiv ⁻¹' rationalOpen T s = Palomar.ValuationSpectrum.rationalOpen T s := rfl

theorem rationalOpen_subset_iff {T T' : Finset A} {s s' : A} :
    Palomar.ValuationSpectrum.rationalOpen T' s' ⊆ Palomar.ValuationSpectrum.rationalOpen T s ↔
      rationalOpen T' s' ⊆ rationalOpen T s := by
  rw [← spvEquiv_preimage_rationalOpen T s, ← spvEquiv_preimage_rationalOpen T' s']
  exact spvEquiv.preimage_subset _ _

/-- The Challenge's `Spa (A, A⁺)` and the library's are homeomorphic via `spvHomeo`. -/
def spaHomeo :
    ↥(Palomar.ValuationSpectrum.Spa A (Palomar.ValuationSpectrum.ringPlus A)) ≃ₜ ↥(Spa A A⁺) :=
  spvHomeo.subtype fun _ => Iff.rfl

/-- The Challenge's `SpaTop` and the library's, as isomorphic objects of `TopCat`. -/
def spaIso : Palomar.ValuationSpectrum.SpaTop A ≅ SpaTop A := TopCat.isoOfHomeo spaHomeo

end Spa

/-! ### Pairs of definition and rational localisation data -/

section Loc

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The Challenge's `PairOfDefinition` read as the library's. -/
def podTo (P : Palomar.PairOfDefinition A) : PairOfDefinition A :=
  ⟨P.A₀, P.I, P.isOpen, P.fg, P.isAdic⟩

/-- The library's `PairOfDefinition` read as the Challenge's. -/
def podOf (P : PairOfDefinition A) : Palomar.PairOfDefinition A :=
  ⟨P.A₀, P.I, P.isOpen, P.fg, P.isAdic⟩

@[simp] theorem podTo_podOf (P : PairOfDefinition A) : podTo (podOf P) = P := rfl
@[simp] theorem podOf_podTo (P : Palomar.PairOfDefinition A) : podOf (podTo P) = P := rfl

variable [IsTopologicalRing A]

/-- The Challenge's `RationalLocData` read as the library's. -/
def rldTo (D : Palomar.ValuationSpectrum.RationalLocData A) : RationalLocData A :=
  ⟨podTo D.P, D.T, D.s, D.hopen⟩

/-- The library's `RationalLocData` read as the Challenge's. -/
def rldOf (D : RationalLocData A) : Palomar.ValuationSpectrum.RationalLocData A :=
  ⟨podOf D.P, D.T, D.s, D.hopen⟩

@[simp] theorem rldTo_rldOf (D : RationalLocData A) : rldTo (rldOf D) = D := rfl
@[simp] theorem rldOf_rldTo (D : Palomar.ValuationSpectrum.RationalLocData A) :
    rldOf (rldTo D) = D := rfl

/-- The two completed rational localisations are **the same type**: the localisation topology
is built from a `RingSubgroupsBasis`, a proposition, so the two constructions coincide. -/
theorem presheafValue_eq (D : Palomar.ValuationSpectrum.RationalLocData A) :
    Palomar.ValuationSpectrum.presheafValue D = presheafValue (rldTo D) := rfl

theorem canonicalMap_eq (D : Palomar.ValuationSpectrum.RationalLocData A) :
    Palomar.ValuationSpectrum.RationalLocData.canonicalMap D = (rldTo D).canonicalMap := rfl

theorem coeRingHom_eq (D : Palomar.ValuationSpectrum.RationalLocData A) :
    Palomar.ValuationSpectrum.RationalLocData.coeRingHom D = (rldTo D).coeRingHom := rfl

theorem isRational_iff (D : Palomar.ValuationSpectrum.RationalLocData A) :
    D.IsRational ↔ (rldTo D).IsRational := Iff.rfl

end Loc

/-! ### Uniqueness of the restriction maps

A family of restriction maps is pinned down by compatibility with the canonical maps from `A`:
a ring map out of `Aₛ` is determined by its restriction to `A` (the universal property of
the localisation), the image of `Aₛ` is dense in `A⟨T/s⟩`, and `A⟨T'/s'⟩` is Hausdorff. So
any two `RestrictionFamily`s are equal, and the Challenge's `∀ R` ranges over one element. -/

section Unique

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Palomar.ValuationSpectrum.PlusSubring A]

theorem RestrictionFamily.res_eq (R R' : Palomar.ValuationSpectrum.RestrictionFamily A)
    (D D' : Palomar.ValuationSpectrum.RationalLocData A)
    (h : Palomar.ValuationSpectrum.rationalOpen D'.T D'.s ⊆
      Palomar.ValuationSpectrum.rationalOpen D.T D.s) :
    R.res D D' h = R'.res D D' h := by
  -- the two maps agree after the completion map, by the universal property of `Aₛ`
  have hloc : (R.res D D' h).comp D.coeRingHom = (R'.res D D' h).comp D.coeRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers D.s)
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    exact (R.res_compat D D' h).trans (R'.res_compat D D' h).symm
  -- hence everywhere, by density and continuity
  have hd : DenseRange D.coeRingHom :=
    @UniformSpace.Completion.denseRange_coe _ D.uniformSpace
  refine RingHom.ext (congrFun ?_)
  refine Continuous.ext_on hd (R.res_continuous D D' h) (R'.res_continuous D D' h) ?_
  rintro _ ⟨a, rfl⟩
  exact RingHom.congr_fun hloc a

theorem RestrictionFamily.ext' (R R' : Palomar.ValuationSpectrum.RestrictionFamily A) :
    R = R' := by
  obtain ⟨res, rc, rcomp⟩ := R
  obtain ⟨res', rc', rcomp'⟩ := R'
  have : res = res' := by
    funext D D' h
    exact RestrictionFamily.res_eq ⟨res, rc, rcomp⟩ ⟨res', rc', rcomp'⟩ D D' h
  subst this
  rfl

instance : Subsingleton (Palomar.ValuationSpectrum.RestrictionFamily A) :=
  ⟨RestrictionFamily.ext'⟩

end Unique

/-! ### The canonical restriction family

The library's restriction maps (Wedhorn Proposition 8.2, `restrictionMapHom`) form a
`RestrictionFamily`; by uniqueness they are the only one. -/

section Canonical

variable {A : Type u} [CommRing A] [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
  [HasLocLiftPowerBounded A]

/-- The library's restriction maps, read as a Challenge `RestrictionFamily`. -/
def canonicalRF : Palomar.ValuationSpectrum.RestrictionFamily A where
  res D D' h := restrictionMapHom (rldTo D) (rldTo D') (rationalOpen_subset_iff.mp h)
  res_continuous D D' h := restrictionMapHom_continuous _ _ _
  res_compat D D' h := RingHom.ext fun a => restrictionMapHom_canonicalMap_generic _ _ _ a

theorem canonicalRF_res (D D' : Palomar.ValuationSpectrum.RationalLocData A)
    (h : Palomar.ValuationSpectrum.rationalOpen D'.T D'.s ⊆
      Palomar.ValuationSpectrum.rationalOpen D.T D.s) :
    (canonicalRF (A := A)).res D D' h =
      restrictionMapHom (rldTo D) (rldTo D') (rationalOpen_subset_iff.mp h) := rfl

/-- Every `RestrictionFamily` is the canonical one. -/
theorem eq_canonicalRF (R : Palomar.ValuationSpectrum.RestrictionFamily A) : R = canonicalRF :=
  Subsingleton.elim _ _

end Canonical

/-! ### The structure presheaf

The Challenge's structure presheaf, built from the canonical restriction family, is the
library's `structurePresheaf` (viewed in `TopCommRingCat`), transported across the
homeomorphism `spaIso` between the two `Spa`s. Both are `lim_{R(T/s) ⊆ V} A⟨T/s⟩`; the
isomorphism is reindexing along the correspondence of rational indices. -/

section PresheafIso

open scoped AlgebraicGeometry

variable {A : Type u} [CommRing A] [TopologicalSpace A] [PlusSubring A] [IsHuberRing A]
  [HasLocLiftPowerBounded A]

theorem mem_map_spaIso {V : Opens ↥(SpaTop A)} {x : ↥(Palomar.ValuationSpectrum.SpaTop A)} :
    x ∈ (Opens.map spaIso.hom).obj V ↔ spaHomeo x ∈ V := Iff.rfl

theorem spaHomeo_mem_spaOpen_iff (D : Palomar.ValuationSpectrum.RationalLocData A)
    (x : ↥(Palomar.ValuationSpectrum.SpaTop A)) :
    spaHomeo x ∈ spaOpen (rldTo D) ↔ x ∈ Palomar.ValuationSpectrum.spaOpen D := Iff.rfl

theorem spaHomeo_symm_mem_spaOpen_iff (D : RationalLocData A) (w : ↥(SpaTop A)) :
    spaHomeo.symm w ∈ Palomar.ValuationSpectrum.spaOpen (rldOf D) ↔ w ∈ spaOpen D := Iff.rfl

/-- The rational indices of `spaIso⁻¹ V` (Challenge side) and of `V` (library side). -/
def idxEquiv (V : Opens ↥(SpaTop A)) :
    Palomar.ValuationSpectrum.RationalIndex ((Opens.map spaIso.hom).obj V) ≃ RationalIndex V where
  toFun i := ⟨rldTo i.D, i.isRational, fun w hw => by
    have h1 : spaHomeo.symm w ∈ (Opens.map spaIso.hom).obj V :=
      i.subset ((spaHomeo_symm_mem_spaOpen_iff (rldTo i.D) w).mpr hw)
    have h2 : spaHomeo (spaHomeo.symm w) ∈ V := mem_map_spaIso.mp h1
    rwa [Homeomorph.apply_symm_apply] at h2⟩
  invFun j := ⟨rldOf j.D, j.isRational, fun x hx =>
    mem_map_spaIso.mpr (j.subset ((spaHomeo_mem_spaOpen_iff (rldOf j.D) x).mpr hx))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindexing: the Challenge's limit sections over `spaIso⁻¹ V` are the library's over `V`. -/
def limitSectionsEquiv (V : Opens ↥(SpaTop A)) :
    ↥(Palomar.ValuationSpectrum.limitSections (canonicalRF (A := A))
        ((Opens.map spaIso.hom).obj V)) ≃+* ↥(limitSections V) where
  toFun x := ⟨fun j => x.1 ((idxEquiv V).symm j), fun j j' h =>
    x.2 ((idxEquiv V).symm j) ((idxEquiv V).symm j') (rationalOpen_subset_iff.mpr h)⟩
  invFun y := ⟨fun i => y.1 (idxEquiv V i), fun i i' h =>
    y.2 (idxEquiv V i) (idxEquiv V i') (rationalOpen_subset_iff.mp h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem limitSectionsEquiv_continuous (V : Opens ↥(SpaTop A)) :
    Continuous (limitSectionsEquiv V) := by
  refine continuous_induced_rng.2 (continuous_pi fun j => ?_)
  exact (continuous_apply ((idxEquiv V).symm j)).comp continuous_subtype_val

theorem limitSectionsEquiv_symm_continuous (V : Opens ↥(SpaTop A)) :
    Continuous (limitSectionsEquiv V).symm := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  exact (continuous_apply (idxEquiv V i)).comp continuous_subtype_val

/-- The object-level isomorphism in `TopCommRingCat`. -/
def objIso (V : Opens ↥(SpaTop A)) :
    (spaIso.hom _* Palomar.ValuationSpectrum.structurePresheaf (canonicalRF (A := A))).obj
        (op V) ≅
      (structurePresheaf A ⋙ CompleteTopCommRingCat.forgetToTopCommRingCat).obj (op V) where
  hom := ⟨(limitSectionsEquiv V).toRingHom, limitSectionsEquiv_continuous V⟩
  inv := ⟨(limitSectionsEquiv V).symm.toRingHom, limitSectionsEquiv_symm_continuous V⟩
  hom_inv_id := Subtype.ext (RingHom.ext fun x => (limitSectionsEquiv V).symm_apply_apply x)
  inv_hom_id := Subtype.ext (RingHom.ext fun x => (limitSectionsEquiv V).apply_symm_apply x)

/-- The Challenge's structure presheaf is the library's. -/
def canonicalIso :
    spaIso.hom _* Palomar.ValuationSpectrum.structurePresheaf (canonicalRF (A := A)) ≅
      structurePresheaf A ⋙ CompleteTopCommRingCat.forgetToTopCommRingCat :=
  NatIso.ofComponents (fun V => objIso V.unop) (fun _ =>
    Subtype.ext (RingHom.ext fun _ => Subtype.ext (funext fun _ => rfl)))

end PresheafIso

/-! ### Sheafiness -/

section Sheaf

/-- `IsSheaf` is invariant under pushforward along an isomorphism of spaces. -/
theorem isSheaf_pushforward_iso_iff {C : Type*} [Category C] {X Y : TopCat.{u}} (e : X ≅ Y)
    (P : TopCat.Presheaf C X) :
    TopCat.Presheaf.IsSheaf ((TopCat.Presheaf.pushforward C e.hom).obj P) ↔
      TopCat.Presheaf.IsSheaf P := by
  constructor
  · intro h
    have h2 := TopCat.Sheaf.pushforward_sheaf_of_sheaf e.inv h
    rwa [← TopCat.Presheaf.Pushforward.comp_eq, e.hom_inv_id,
      TopCat.Presheaf.Pushforward.id_eq] at h2
  · exact TopCat.Sheaf.pushforward_sheaf_of_sheaf e.hom

variable {A : Type u} [CommRing A] [TopologicalSpace A] [PlusSubring A] [IsTateRing A]
  [IsRingOfIntegralElements (A⁺ : Subring A)] [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

-- The binder list is the library's own (`ValuationSpectrum.IsSheafy`), which the linter
-- flags as overlapping; it is reproduced verbatim so the statement reads as the library's.
/-- **The Challenge's `IsSheafy` is the library's.** The Challenge states sheafiness as
Mathlib's `TopCat.Presheaf.IsSheaf` for the structure presheaf built from any restriction
family; the library states the finite rational-cover criterion. They agree. -/
theorem isSheafy_iff : Palomar.ValuationSpectrum.IsSheafy A ↔ IsSheafy A := by
  classical
  rw [isSheafy_iff_structurePresheaf_forgetToTopCommRingCat_isSheaf]
  constructor
  · rintro ⟨-, h⟩
    exact (TopCat.Presheaf.isSheaf_iso_iff canonicalIso).mp
      ((isSheaf_pushforward_iso_iff spaIso _).mpr (h canonicalRF))
  · intro h
    refine ⟨⟨canonicalRF⟩, fun R => ?_⟩
    rw [eq_canonicalRF R]
    exact (isSheaf_pushforward_iso_iff spaIso _).mp
      ((TopCat.Presheaf.isSheaf_iso_iff canonicalIso).mpr h)

end Sheaf

/-! ### Huber and Tate rings, rings of integral elements, uniformity -/

section Classes

variable {A : Type u} [CommRing A] [TopologicalSpace A]

/-- A Challenge Huber ring is a library Huber ring (the pairs of definition correspond). -/
instance (priority := 50) isHuberRing_of_palomar [h : Palomar.IsHuberRing A] : IsHuberRing A :=
  { toIsTopologicalRing := h.toIsTopologicalRing
    exists_pairOfDefinition := h.exists_pairOfDefinition.map podTo }

/-- A Challenge Tate ring is a library Tate ring. -/
instance (priority := 50) isTateRing_of_palomar [h : Palomar.IsTateRing A] : IsTateRing A :=
  { isHuberRing_of_palomar with
    exists_topologicallyNilpotent_unit := h.exists_topologicallyNilpotent_unit }

theorem isHuberRing_iff : Palomar.IsHuberRing A ↔ IsHuberRing A :=
  ⟨fun _ => inferInstance, fun h =>
    { toIsTopologicalRing := h.toIsTopologicalRing
      exists_pairOfDefinition := h.exists_pairOfDefinition.map podOf }⟩

theorem isTateRing_iff : Palomar.IsTateRing A ↔ IsTateRing A :=
  ⟨fun _ => inferInstance, fun h =>
    { isHuberRing_iff.mpr h.toIsHuberRing with
      exists_topologicallyNilpotent_unit := h.exists_topologicallyNilpotent_unit }⟩

theorem isRingOfIntegralElements_iff (B : Subring A) :
    Palomar.ValuationSpectrum.IsRingOfIntegralElements B ↔ IsRingOfIntegralElements B :=
  ⟨fun h => ⟨h.1, h.2, h.3⟩, fun h => ⟨h.1, h.2, h.3⟩⟩

theorem isUniform_iff [IsTopologicalRing A] :
    Palomar.IsUniform A ↔ TopologicalRing.IsUniform A :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

theorem isStablyUniform_iff [Palomar.IsHuberRing A] [PlusSubring A] :
    Palomar.ValuationSpectrum.IsStablyUniform A ↔ TopologicalRing.IsStablyUniform A :=
  ⟨fun h => ⟨fun D => h.1 (rldOf D)⟩, fun h => ⟨fun D => h.1 (rldTo D)⟩⟩

end Classes

/-! ### Ring-level sheafiness -/

section SheafyComplete

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTateRing A] [T2Space A]
  [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]

/-- **The Challenge's `IsSheafyComplete` is the library's**: sheafiness for every ring of integral
elements, in the Challenge's formulation of sheafiness, is sheafiness for every ring of integral
elements in the library's. -/
theorem isSheafyComplete_iff :
    Palomar.ValuationSpectrum.IsSheafyComplete A ↔ IsSheafyComplete A := by
  classical
  constructor
  · intro h Aplus
    letI := Aplus.toPlusSubring
    haveI : IsRingOfIntegralElements (A⁺ : Subring A) := Aplus.2
    haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
    show IsLimitSheaf A
    have hp : Palomar.ValuationSpectrum.IsSheafy A :=
      h Aplus.1 ((isRingOfIntegralElements_iff _).mpr Aplus.2)
    exact isSheafy_iff_isLimitSheaf.mp (isSheafy_iff.mp hp)
  · intro h B hB
    letI : PlusSubring A := ⟨B⟩
    haveI : IsRingOfIntegralElements (A⁺ : Subring A) := (isRingOfIntegralElements_iff _).mp hB
    haveI : HasLocLiftPowerBounded A := hasLocLiftPowerBounded_faithful
    have hl : IsLimitSheaf A := h ⟨B, (isRingOfIntegralElements_iff _).mp hB⟩
    exact isSheafy_iff.mpr (isSheafy_iff_isLimitSheaf.mpr hl)

end SheafyComplete

end PalomarBridge
