/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom

/-! # Tate Transport -/

@[expose] public section
namespace LocalClassFieldTheory

open ClassFormation

/-!
# The local class-field-axiom theorem: transport of cyclic Tate complexes

The fixed-field realization of an abstract extension changes both the
presentation of its cyclic group and the presentation of its coefficient
module.  This file records the two honest functorial comparisons needed to
transport the local class-field-axiom theorem: reindexing a representation along a group
isomorphism and replacing a representation by an isomorphic one.
-/

noncomputable
section

open CategoryTheory

section CyclicGenerator

variable {Q P : Type} [Group Q] [Group P]

/-- A generator remains a generator after applying a group isomorphism. -/
theorem map_cyclicGenerator (e : Q ≃* P) (g : Q)
    (hg : ∀ q : Q, q ∈ Subgroup.zpowers g) :
    ∀ p : P, p ∈ Subgroup.zpowers (e g) := by
  intro p
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (e.symm p))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  rw [← map_zpow e, hn, e.apply_symm_apply]

end CyclicGenerator

section GroupEquiv

variable {R Q P : Type} [CommRing R]
  [CommGroup Q] [CommGroup P] [Fintype Q] [Fintype P]

private theorem res_norm_eq (e : Q ≃* P) (A : Rep R P) :
    let Ares : Rep R Q :=
      Rep.res e.toMonoidHom A
    ModuleCat.ofHom Ares.norm.hom.toLinearMap =
      ModuleCat.ofHom A.norm.hom.toLinearMap := by
  let Ares : Rep R Q :=
    Rep.res e.toMonoidHom A
  apply congrArg ModuleCat.ofHom
  change Representation.norm Ares.ρ = Representation.norm A.ρ
  simp only [Representation.norm]
  exact Fintype.sum_equiv e.toEquiv
    (fun q : Q => Ares.ρ q)
    (fun p : P => A.ρ p) (fun _ => rfl)

/-- Reindexing along a group isomorphism preserves the cyclic `H⁰`
short complex. -/
def normHomCompSubResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    Rep.FiniteCyclicGroup.normHomCompSub
        (Rep.res e.toMonoidHom A) g ≅
      Rep.FiniteCyclicGroup.normHomCompSub A (e g) := by
  let Ares : Rep R Q :=
    Rep.res e.toMonoidHom A
  let i : ModuleCat.of R Ares.V ≅ ModuleCat.of R A.V := Iso.refl _
  exact ShortComplex.isoMk i i i
    (by simpa [Ares, i] using (res_norm_eq e A).symm) (by rfl)

/-- Reindexing along a group isomorphism preserves the cyclic `H⁻¹`
short complex. -/
def subCompNormHomResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.res e.toMonoidHom A) g ≅
      Rep.FiniteCyclicGroup.subCompNormHom A (e g) := by
  let Ares : Rep R Q :=
    Rep.res e.toMonoidHom A
  let i : ModuleCat.of R Ares.V ≅ ModuleCat.of R A.V := Iso.refl _
  exact ShortComplex.isoMk i i i
    (by rfl) (by simpa [Ares, i] using (res_norm_eq e A).symm)

/-- Homology-level group-reindexing comparison in degree zero. -/
def normHomCompSubHomologyResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    (Rep.FiniteCyclicGroup.normHomCompSub
        (Rep.res e.toMonoidHom A) g).homology ≅
      (Rep.FiniteCyclicGroup.normHomCompSub A (e g)).homology :=
  ShortComplex.homologyMapIso (normHomCompSubResEquivIso e A g)

/-- Homology-level group-reindexing comparison in degree minus one. -/
def subCompNormHomHomologyResEquivIso
    (e : Q ≃* P) (A : Rep R P) (g : Q) :
    (Rep.FiniteCyclicGroup.subCompNormHom
        (Rep.res e.toMonoidHom A) g).homology ≅
      (Rep.FiniteCyclicGroup.subCompNormHom A (e g)).homology :=
  ShortComplex.homologyMapIso (subCompNormHomResEquivIso e A g)

end GroupEquiv

section RepresentationIso

variable {R Q : Type} [CommRing R] [CommGroup Q] [Fintype Q]

/-- Isomorphic representations have isomorphic cyclic `H⁰` short
complexes. -/
def normHomCompSubIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    Rep.FiniteCyclicGroup.normHomCompSub M g ≅
      Rep.FiniteCyclicGroup.normHomCompSub N g := by
  let i : ModuleCat.of R M.V ≅ ModuleCat.of R N.V :=
    (forget₂ (Rep R Q) (ModuleCat R)).mapIso e
  refine ShortComplex.isoMk i i i ?_ ?_
  · have h := congrArg
      (fun f : M ⟶ N => ModuleCat.ofHom f.hom.toLinearMap)
      (Rep.norm_comm e.hom)
    simpa [i, Rep.norm] using h
  · have hrep :
        e.hom ≫ (Rep.applyAsHom N g - 𝟙 N) =
          (Rep.applyAsHom M g - 𝟙 M) ≫ e.hom := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
        Category.id_comp, Rep.applyAsHom_comm]
    let F := forget₂ (Rep R Q) (ModuleCat R)
    change F.map e.hom ≫ F.map (Rep.applyAsHom N g - 𝟙 N) =
      F.map (Rep.applyAsHom M g - 𝟙 M) ≫ F.map e.hom
    rw [← F.map_comp, ← F.map_comp, hrep]

/-- Isomorphic representations have isomorphic cyclic `H⁻¹` short
complexes. -/
def subCompNormHomIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    Rep.FiniteCyclicGroup.subCompNormHom M g ≅
      Rep.FiniteCyclicGroup.subCompNormHom N g := by
  let i : ModuleCat.of R M.V ≅ ModuleCat.of R N.V :=
    (forget₂ (Rep R Q) (ModuleCat R)).mapIso e
  refine ShortComplex.isoMk i i i ?_ ?_
  · have hrep :
        e.hom ≫ (Rep.applyAsHom N g - 𝟙 N) =
          (Rep.applyAsHom M g - 𝟙 M) ≫ e.hom := by
      rw [Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
        Category.id_comp, Rep.applyAsHom_comm]
    let F := forget₂ (Rep R Q) (ModuleCat R)
    change F.map e.hom ≫ F.map (Rep.applyAsHom N g - 𝟙 N) =
      F.map (Rep.applyAsHom M g - 𝟙 M) ≫ F.map e.hom
    rw [← F.map_comp, ← F.map_comp, hrep]
  · have h := congrArg
      (fun f : M ⟶ N => ModuleCat.ofHom f.hom.toLinearMap)
      (Rep.norm_comm e.hom)
    simpa [i, Rep.norm] using h

/-- Homology-level representation-isomorphism comparison in degree zero. -/
def normHomCompSubHomologyIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    (Rep.FiniteCyclicGroup.normHomCompSub M g).homology ≅
      (Rep.FiniteCyclicGroup.normHomCompSub N g).homology :=
  ShortComplex.homologyMapIso (normHomCompSubIsoOfRepIso e g)

/-- Homology-level representation-isomorphism comparison in degree
minus one. -/
def subCompNormHomHomologyIsoOfRepIso
    {M N : Rep R Q} (e : M ≅ N) (g : Q) :
    (Rep.FiniteCyclicGroup.subCompNormHom M g).homology ≅
      (Rep.FiniteCyclicGroup.subCompNormHom N g).homology :=
  ShortComplex.homologyMapIso (subCompNormHomIsoOfRepIso e g)

end RepresentationIso

end
end LocalClassFieldTheory
