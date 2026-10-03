/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation

/-! # Cyclic Norm Quotient -/

@[expose] public section
namespace ClassFormation

open KummerTheory

open CyclicCohomology

/-!
# Cyclic norm quotients as degree-zero Tate cohomology

For a finite cyclic abstract extension `L / K`, this file identifies the
actual quotient `A_K / N_{L/K} A_L` with the degree-zero Tate homology
object used in the class-field axiom.  This is the source comparison needed before the
cardinality assertion of the class field axiom can be applied to the
reciprocity map.
-/

noncomputable
section

open CategoryTheory

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The actual fixed group `A_K` is the kernel of `ρ(g)-1` on `A_L`
when `g` generates `G(L/K)`. -/
def cyclicFixedCycleEquiv
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    ambientFixedAddSubgroup A K ≃+
      T.moduleCatLeftHomologyData.K := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  letI : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  letI : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let toCycle : ambientFixedAddSubgroup A K →
      T.moduleCatLeftHomologyData.K := fun a => by
    let aL := fixedFieldInclusion A K L hLK a
    let aM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm aL
    refine ⟨aM, sub_eq_zero.mpr ?_⟩
    refine Quotient.inductionOn' g ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 a.1 = a.1
    exact a.2 k
  let fromCycle : T.moduleCatLeftHomologyData.K →
      ambientFixedAddSubgroup A K := fun x => by
    let aM : M.V := x.1
    let aL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal aM
    have hxzero : T.g.hom aM = 0 := x.2
    have hxg : M.ρ g aM = aM := by
      apply sub_eq_zero.mp
      exact hxzero
    have hxall : ∀ q, M.ρ q aM = aM := by
      let : Module ℤ M := M.hV2
      exact (Representation.mem_invariants_iff_of_forall_mem_zpowers
        M.ρ g hg aM).2 hxg
    refine ⟨aL.1, ?_⟩
    intro k
    have hk := hxall
      ((QuotientGroup.mk' (extensionSubgroup K L hLK)) k)
    have haction := extensionFixedRepresentation_action_coe
      A K L hLK hnormal
      ((QuotientGroup.mk' (extensionSubgroup K L hLK)) k) aM
    have haction' :
        (M.ρ ((QuotientGroup.mk'
          (extensionSubgroup K L hLK)) k) aM).1 =
          A.ρ k.1 aL.1 := by
      calc
        _ = relativeCosetAction A K L hLK aL
              ((QuotientGroup.mk'
                (extensionSubgroup K L hLK)) k) := haction
        _ = A.ρ k.1 aL.1 :=
          relativeCosetAction_mk A K L hLK aL k
    exact haction'.symm.trans ((congrArg Subtype.val hk).trans rfl)
  exact
    { toFun := toCycle
      invFun := fromCycle
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl
      map_add' := by
        intro a b
        apply Subtype.ext
        apply Subtype.ext
        rfl }

/-- The canonical map from `A_K` to the concrete kernel/range quotient
computing degree-zero Tate cohomology. -/
def cyclicNormClassHom
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    ambientFixedAddSubgroup A K →+
      T.moduleCatLeftHomologyData.H := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  letI : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  letI : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let e := cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
  exact
    { toFun := fun a => T.moduleCatLeftHomologyData.π (e a)
      map_zero' := by simp
      map_add' := by
        intro a b
        simp }

/--
The cyclic norm-class map evaluates by applying the fixed-cycle equivalence and projecting to
cyclic homology.
-/
@[simp]
theorem cyclicNormClassHom_apply
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (a : ambientFixedAddSubgroup A K) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    cyclicNormClassHom A K L hLK hnormal hfinite g hg a =
      T.moduleCatLeftHomologyData.π
        (cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg a) := by
  rfl

/-- Under the fixed-cycle equivalence, the actual relative norm is the
first differential in the cyclic Tate complex. -/
theorem cyclicFixedCycleEquiv_relativeNorm
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (a : ambientFixedAddSubgroup A L) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
        (relativeNorm A K L hLK a) =
      T.moduleCatToCycles
        ((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a) := by
  dsimp only
  let := hnormal
  let := hfinite
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  let : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  apply Subtype.ext
  apply Subtype.ext
  exact (extensionFixedRepresentation_norm_coe
    A K L hLK hnormal
      ((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a)).symm

/-- The kernel of the concrete Tate-class map is exactly the actual norm
subgroup `N_{L/K} A_L`. -/
theorem cyclicNormClassHom_ker
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    (cyclicNormClassHom A K L hLK hnormal hfinite g hg).ker =
      finiteNormSubgroup A K L hLK := by
  let := hnormal
  let := hfinite
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  let : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let : Module ℤ T.X₁ := T.X₁.isModule
  let : Module ℤ (LinearMap.ker T.g.hom) :=
    (LinearMap.ker T.g.hom).module
  let e := cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
  ext a
  constructor
  · intro ha
    change cyclicNormClassHom A K L hLK hnormal hfinite g hg a = 0 at ha
    rw [cyclicNormClassHom_apply] at ha
    let ea : T.moduleCatLeftHomologyData.K := e a
    have ha' :
        Submodule.mkQ (LinearMap.range T.moduleCatToCycles) ea = 0 := by
      exact ha
    have harange : ea ∈ LinearMap.range T.moduleCatToCycles :=
      (Submodule.Quotient.mk_eq_zero _).1 ha'
    obtain ⟨y, hy⟩ := harange
    change a ∈ (relativeNorm A K L hLK).range
    let b : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal y
    refine ⟨b, ?_⟩
    apply Subtype.ext
    calc
      (relativeNorm A K L hLK b).1 = (M.norm.hom y).1 :=
        (extensionFixedRepresentation_norm_coe
          A K L hLK hnormal y).symm
      _ = ea.1.1 :=
        congrArg Subtype.val (congrArg Subtype.val hy)
      _ = a.1 := rfl
  · intro ha
    change a ∈ (relativeNorm A K L hLK).range at ha
    obtain ⟨b, rfl⟩ := ha
    change cyclicNormClassHom A K L hLK hnormal hfinite g hg
      (relativeNorm A K L hLK b) = 0
    rw [cyclicNormClassHom_apply]
    let eb : T.moduleCatLeftHomologyData.K :=
      e (relativeNorm A K L hLK b)
    change Submodule.mkQ (LinearMap.range T.moduleCatToCycles)
      eb = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    refine ⟨(extensionFixedRepresentationEquiv
      A K L hLK hnormal).symm b, ?_⟩
    exact (cyclicFixedCycleEquiv_relativeNorm
      A K L hLK hnormal hfinite g hg b).symm

/-- Every concrete Tate class has a representative in the actual fixed
group `A_K`. -/
theorem cyclicNormClassHom_surjective
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    Function.Surjective
      (cyclicNormClassHom A K L hLK hnormal hfinite g hg) := by
  let := hnormal
  let := hfinite
  let := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  let : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  let : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let e := cyclicFixedCycleEquiv A K L hLK hnormal hfinite g hg
  have hπ : Function.Surjective T.moduleCatLeftHomologyData.π :=
    (ModuleCat.epi_iff_surjective
      T.moduleCatLeftHomologyData.π).1 inferInstance
  intro z
  obtain ⟨x, hx⟩ := hπ z
  refine ⟨e.symm x, ?_⟩
  rw [cyclicNormClassHom_apply, e.apply_symm_apply]
  exact hx

/-- The actual finite norm quotient is the concrete kernel/range quotient
which computes degree-zero Tate cohomology. -/
def cyclicFiniteNormQuotientEquivConcrete
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    FiniteNormQuotient A K L hLK ≃+
      T.moduleCatLeftHomologyData.H := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  letI : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  letI : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let f := cyclicNormClassHom A K L hLK hnormal hfinite g hg
  exact
    (finiteNormQuotientConcreteEquiv A K L hLK).trans
      ((QuotientAddGroup.quotientAddEquivOfEq
        (cyclicNormClassHom_ker A K L hLK hnormal hfinite g hg).symm).trans
        (QuotientAddGroup.quotientKerEquivOfSurjective f
          (cyclicNormClassHom_surjective
            A K L hLK hnormal hfinite g hg)))

/-- The concrete kernel/range quotient is the homology object used in the
definition of `tateHZero`. -/
def cyclicConcreteEquivTateHZero
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    letI : IsCyclic
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      isCyclic_of_generator g hg
    letI : CommGroup
        (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    T.moduleCatLeftHomologyData.H ≃+ tateCohomology M 0 := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  letI : IsCyclic (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    isCyclic_of_generator g hg
  letI : CommGroup (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  exact
    (T.moduleCatHomologyIso.symm ≪≫
      (TateCohomology.isoFiniteCyclicZero M g hg).symm).toLinearEquiv.toAddEquiv

/-- Canonical identification of the actual norm quotient with
degree-zero Tate cohomology for a finite cyclic extension. -/
def cyclicFiniteNormQuotientEquivTateHZero
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K L hLK))
    (g : K.toSubgroup ⧸ extensionSubgroup K L hLK)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)
    let M := extensionFixedRepresentation A K L hLK hnormal
    FiniteNormQuotient A K L hLK ≃+ tateCohomology M 0 := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ extensionSubgroup K L hLK)
  exact
    (cyclicFiniteNormQuotientEquivConcrete
      A K L hLK hnormal hfinite g hg).trans
      (cyclicConcreteEquivTateHZero
        A K L hLK hnormal hfinite g hg)

/-- The class-field axiom first gives genuine finiteness of the actual norm
quotient, transported from finite degree-zero Tate cohomology. -/
theorem finiteNormQuotientFiniteOfClassFieldAxiom
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finite (FiniteNormQuotient A E.base E.field E.below) := by
  let := hnormal
  let := E.finiteQuotient
  let := Fintype.ofFinite
    (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
  let M := extensionFixedRepresentation A E.base E.field E.below hnormal
  let Kcf : FiniteAbstractField G := ⟨E.base, hKfinite⟩
  let Ecf : FiniteCyclicSubextension Kcf :=
    { field := E.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  let : Finite (tateCohomology (Ecf.fixedRepresentation A) 0) :=
    (hcf Kcf Ecf).finiteTateHZero
  exact Finite.of_equiv (tateCohomology (Ecf.fixedRepresentation A) 0) (by
    simpa [Kcf, Ecf, FiniteCyclicSubextension.fixedRepresentation] using
        (cyclicFiniteNormQuotientEquivTateHZero
          A E.base E.field E.below hnormal E.finiteQuotient g hg).symm.toEquiv)

/-- The class-field axiom gives the exact order of the actual norm quotient in the
cyclic case. -/
theorem finiteNormQuotient_card_of_classFieldAxiom
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card (FiniteNormQuotient A E.base E.field E.below) =
      (E.degree : ℕ) := by
  let := hnormal
  let := E.finiteQuotient
  let := Fintype.ofFinite
    (E.base.toSubgroup ⧸ extensionSubgroup E.base E.field E.below)
  let M := extensionFixedRepresentation A E.base E.field E.below hnormal
  let Kcf : FiniteAbstractField G := ⟨E.base, hKfinite⟩
  let Ecf : FiniteCyclicSubextension Kcf :=
    { field := E.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }
  let : Finite (tateCohomology (Ecf.fixedRepresentation A) 0) :=
    (hcf Kcf Ecf).finiteTateHZero
  let : Finite (tateCohomology M 0) := by
    simpa [M, Kcf, Ecf,
      FiniteCyclicSubextension.fixedRepresentation] using
        (inferInstance :
          Finite (tateCohomology (Ecf.fixedRepresentation A) 0))
  let : Finite (FiniteNormQuotient A E.base E.field E.below) :=
    finiteNormQuotientFiniteOfClassFieldAxiom A hcf E hnormal g hg
  calc
    Nat.card (FiniteNormQuotient A E.base E.field E.below) =
        Nat.card (tateCohomology M 0) :=
      Nat.card_congr
        (cyclicFiniteNormQuotientEquivTateHZero
          A E.base E.field E.below hnormal E.finiteQuotient g hg).toEquiv
    _ = (E.degree : ℕ) :=
      by
        simpa [Kcf, Ecf,
          FiniteCyclicSubextension.fixedRepresentation,
          FiniteCyclicSubextension.toFiniteAbstractExtension] using
            hcf.tateHZero_card Kcf Ecf

/-- The additive Galois quotient has the extension degree as its order. -/
theorem additiveExtensionQuotient_card
    (E : DegreeData.FiniteAbstractExtension G) :
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
      (E.degree : ℕ) := by
  calc
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
        Nat.card
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below) :=
      (Nat.card_congr
        (Additive.ofMul :
          (E.base.toSubgroup ⧸
              extensionSubgroup E.base E.field E.below) ≃
            Additive
              (E.base.toSubgroup ⧸
                extensionSubgroup E.base E.field E.below))).symm
    _ = (extensionSubgroup E.base E.field E.below).index :=
      (Subgroup.index_eq_card
        (extensionSubgroup E.base E.field E.below)).symm
    _ = (E.degree : ℕ) := E.extensionSubgroup_index_eq_degree

/-- Under the class-field axiom, the cyclic Galois quotient and its actual norm
quotient have the same finite order. -/
theorem cyclicReciprocity_card_equality
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            extensionSubgroup E.base E.field E.below)) =
      Nat.card (FiniteNormQuotient A E.base E.field E.below) := by
  rw [additiveExtensionQuotient_card E,
    finiteNormQuotient_card_of_classFieldAxiom
      A hcf E hnormal g hg]

/-- The cyclic norm quotient is finite as an actual type under the class-field axiom. -/
theorem finiteNormQuotient_finite_of_classFieldAxiom
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : DegreeData.FiniteAbstractExtension G)
    [Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) E.base (le_baseField E.base))]
    (hnormal : (extensionSubgroup E.base E.field E.below).Normal)
    (g : E.base.toSubgroup ⧸
      extensionSubgroup E.base E.field E.below)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finite (FiniteNormQuotient A E.base E.field E.below) :=
  finiteNormQuotientFiniteOfClassFieldAxiom A hcf E hnormal g hg

end
end ClassFormation
