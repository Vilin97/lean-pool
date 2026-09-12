/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.EuclideanSphere
public import LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Foundations.TriangleRegularBaseFundamentalGroup
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen1
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Elliptic.Core4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Foundations.EuclideanSphere
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology1

/-!
# Hopf problem: pi 1 · fundamental group van kampen 2

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

private theorem ThreefoldOverlapMappingTorus.Elliptic.root_sub_order (j : Elliptic.Kind) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r)
    (t : ThreefoldOverlapMappingTorus.Circle) :
    ThreefoldOverlapMappingTorus.root j.order r a
        (t - (((1 : ℝ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle)) =
      Elliptic.familyRotation j (ThreefoldOverlapMappingTorus.root j.order r a t) := by
  apply Subtype.ext
  rw [Elliptic.LogGauge.familyRotation_val_exponential]
  change
    (a : ℝ) •
        (ThreefoldOverlapMappingTorus.phase
            (t - (((1 : ℝ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle)) :
          ℂ) =
      CuspUniformization.exponential (-(1 / (j.order : ℂ))) *
        ((a : ℝ) • (ThreefoldOverlapMappingTorus.phase t : ℂ))
  rw [sub_eq_add_neg, ← AddCircle.coe_neg, ThreefoldOverlapMappingTorus.phase_add,
    _root_.Circle.coe_mul, ThreefoldOverlapMappingTorus.phase_real]
  have he : (((-(1 / (j.order : ℝ))) : ℝ) : ℂ) = -(1 / (j.order : ℂ)) := by
    push_cast
    rfl
  rw [he, Complex.real_smul, Complex.real_smul]
  ring

private theorem ThreefoldOverlapMappingTorus.Elliptic.root_add_order (j : Elliptic.Kind) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r)
    (t : ThreefoldOverlapMappingTorus.Circle) :
    ThreefoldOverlapMappingTorus.root j.order r a
        (t + (((1 : ℝ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle)) =
      (Elliptic.familyRotation j).symm (ThreefoldOverlapMappingTorus.root j.order r a t) := by
  apply (Elliptic.familyRotation j).injective
  exact
    ((root_sub_order j r a
              (t + (((1 : ℝ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle))).symm.trans
          (congrArg (ThreefoldOverlapMappingTorus.root j.order r a)
            (add_sub_cancel_right _ _))).trans
      ((Elliptic.familyRotation j).apply_symm_apply _).symm

private def ThreefoldOverlapMappingTorus.Elliptic.polarFamilyAt (j : Elliptic.Kind) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r)
    (p : ThreefoldOverlapMappingTorus.Circle × RealTorus₄) : Elliptic.Family j :=
  (ThreefoldOverlapMappingTorus.root j.order r a p.1, p.2)

private theorem
    ThreefoldOverlapMappingTorus.Elliptic.polarFamilyAt_injective (j : Elliptic.Kind) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) :
    Function.Injective (polarFamilyAt j r a) := by
  intro p q hpq
  apply Prod.ext
  · have hz :
      ThreefoldOverlapMappingTorus.polarRoot j.order r (a, p.1) =
        ThreefoldOverlapMappingTorus.polarRoot j.order r (a, q.1) :=
      Subtype.ext (congrArg Prod.fst hpq)
    have he := congrArg (ThreefoldOverlapMappingTorus.rootAngle j.order r) hz
    simpa only [ThreefoldOverlapMappingTorus.rootAngle_polarRoot] using he
  · exact congrArg (fun y : Elliptic.Family j => y.2) hpq

private theorem ThreefoldOverlapMappingTorus.Elliptic.polarFamilyAt_twist (j : Elliptic.Kind)
    (v : Lattice) (r : ℝ) (a : ThreefoldOverlapMappingTorus.Radius j.order r)
    (p : ThreefoldOverlapMappingTorus.Circle × RealTorus₄) :
    polarFamilyAt j r a
        (Elliptic.HigherHomology.MappingTorusQuotient.twist j.order
          (Elliptic.flatTorusAffine j v).symm p) =
      (Elliptic.familyPermutation j v).symm (polarFamilyAt j r a p) := by
  change
    (ThreefoldOverlapMappingTorus.root j.order r a
          (p.1 + (((1 : ℝ) / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle)),
        (Elliptic.flatTorusAffine j v).symm p.2) =
      ((Elliptic.familyRotation j).symm (ThreefoldOverlapMappingTorus.root j.order r a p.1),
        (Elliptic.flatTorusAffine j v).symm p.2)
  exact Prod.ext (root_add_order j r a p.1) rfl

private theorem
    ThreefoldOverlapMappingTorus.Elliptic.polarFamilyAt_smul (j : Elliptic.Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (r : ℝ) (a : ThreefoldOverlapMappingTorus.Radius j.order r)
    (g : Elliptic.CyclicGroup j) (p : ThreefoldOverlapMappingTorus.Circle × RealTorus₄) :
    letI :=
      Elliptic.HigherHomology.MappingTorusQuotient.productAction j.order
        (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv)
    letI := Elliptic.familyAction j v hv
    polarFamilyAt j r a (g • p) = g⁻¹ • polarFamilyAt j r a p := by
  let :=
    Elliptic.HigherHomology.MappingTorusQuotient.productAction j.order
      (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv)
  let := Elliptic.familyAction j v hv
  have he : g⁻¹ = Multiplicative.ofAdd (-(g.toAdd.val : ℤ) : ZMod j.order) := by
    apply Multiplicative.ext
    simp
  have hright :
    g⁻¹ • polarFamilyAt j r a p =
      ((Elliptic.familyPermutation j v).symm :
            Elliptic.Family j → Elliptic.Family j)^[g.toAdd.val]
        (polarFamilyAt j r a p) := by
    rw [he]
    have hc :=
      Elliptic.HigherHomology.MappingTorusQuotient.cyclicAction_ofAdd_intCast_smul j.order
        (Elliptic.familyPermutation j v) (Elliptic.familyPermutation_pow_order j v hv)
        (-(g.toAdd.val : ℤ)) (polarFamilyAt j r a p)
    simp only [Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast] at hc
    rw [← inv_pow, Equiv.Perm.coe_pow] at hc
    simpa only [Int.cast_natCast, Equiv.Perm.inv_def] using hc
  rw [hright]
  change
    polarFamilyAt j r a
        ((Elliptic.HigherHomology.MappingTorusQuotient.twist j.order
                (Elliptic.flatTorusAffine j v).symm :
              _ → _)^[g.toAdd.val]
          p) =
      _
  exact Function.Semiconj.iterate_right (polarFamilyAt_twist j v r a) g.toAdd.val p

private def ThreefoldOverlapMappingTorus.quotientComparison {X Y Z : Type*} (q : X → Y) (p : X → Z)
    (hq : Function.Surjective q) : Y → Z := fun y => p (hq y).choose

private theorem ThreefoldOverlapMappingTorus.quotientComparison_apply {X Y Z : Type*} (q : X → Y)
    (p : X → Z) (hq : Function.Surjective q) (h : ∀ x x', q x = q x' ↔ p x = p x') (x : X) :
    quotientComparison q p hq (q x) = p x :=
  (h _ _).mp (hq (q x)).choose_spec

private theorem ThreefoldOverlapMappingTorus.quotientComparison_continuous {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (q : X → Y) (p : X → Z)
    (hq : Topology.IsQuotientMap q) (hp : Continuous p) (h : ∀ x x', q x = q x' ↔ p x = p x') :
    Continuous (quotientComparison q p hq.surjective) := by
  apply hq.continuous_iff.mpr
  have he : quotientComparison q p hq.surjective ∘ q = p :=
    funext (quotientComparison_apply q p hq.surjective h)
  rw [he]
  exact hp

private def ThreefoldOverlapMappingTorus.quotientHomeomorph {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] (q : X → Y) (p : X → Z)
    (hq : Topology.IsQuotientMap q) (hp : Topology.IsQuotientMap p)
    (h : ∀ x x', q x = q x' ↔ p x = p x') : Y ≃ₜ Z
    where
  toFun := quotientComparison q p hq.surjective
  invFun := quotientComparison p q hp.surjective
  left_inv
    y := by
    obtain ⟨x, rfl⟩ := hq.surjective y
    rw [quotientComparison_apply q p hq.surjective h,
      quotientComparison_apply p q hp.surjective (fun x x' => (h x x').symm)]
  right_inv
    z := by
    obtain ⟨x, rfl⟩ := hp.surjective z
    rw [quotientComparison_apply p q hp.surjective (fun x x' => (h x x').symm),
      quotientComparison_apply q p hq.surjective h]
  continuous_toFun := quotientComparison_continuous q p hq hp.continuous h
  continuous_invFun :=
    quotientComparison_continuous p q hp hq.continuous (fun x x' => (h x x').symm)

@[simp]
private theorem ThreefoldOverlapMappingTorus.quotientHomeomorph_symm_apply {X Y Z : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (q : X → Y) (p : X → Z)
    (hq : Topology.IsQuotientMap q) (hp : Topology.IsQuotientMap p)
    (h : ∀ x x', q x = q x' ↔ p x = p x') (x : X) :
    (quotientHomeomorph q p hq hp h).symm (p x) = q x :=
  quotientComparison_apply p q hp.surjective (fun x x' => (h x x').symm) x

private def ThreefoldOverlapMappingTorus.Elliptic.puncturedSet (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) : Set (Elliptic.Filling j v hv) :=
  {y |
    (Elliptic.fillingProjection j v hv y : ℂ) ≠ 0 ∧
      ‖(Elliptic.fillingProjection j v hv y : ℂ)‖ < r}

private abbrev
    ThreefoldOverlapMappingTorus.Elliptic.PuncturedFilling (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :=
  puncturedSet j v hv r

private abbrev
    ThreefoldOverlapMappingTorus.Elliptic.PuncturedUpstairs (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :=
  Elliptic.fillingQuotient j v hv ⁻¹' puncturedSet j v hv r

private theorem ThreefoldOverlapMappingTorus.Elliptic.puncturedUpstairs_mem (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) (x : Elliptic.Family j) :
    x ∈ PuncturedUpstairs j v hv r ↔ (x.1 : ℂ) ≠ 0 ∧ ‖(x.1 : ℂ)‖ ^ j.order < r := by
  change ((x.1 : ℂ) ^ j.order ≠ 0 ∧ ‖(x.1 : ℂ) ^ j.order‖ < r) ↔ _
  rw [norm_pow]
  constructor
  · rintro ⟨hne, hnorm⟩
    exact ⟨fun hz => hne (by rw [hz, zero_pow j.order_pos.ne']), hnorm⟩
  · rintro ⟨hne, hnorm⟩
    exact ⟨pow_ne_zero _ hne, hnorm⟩

private def
    ThreefoldOverlapMappingTorus.Elliptic.upstairsRootHomeomorph (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    PuncturedUpstairs j v hv r ≃ₜ ThreefoldOverlapMappingTorus.RootDisc j.order r × RealTorus₄
    where
  toFun y := (⟨y.val.1, (puncturedUpstairs_mem j v hv r y.val).mp y.property⟩, y.val.2)
  invFun p := ⟨(p.1.val, p.2), (puncturedUpstairs_mem j v hv r (p.1.val, p.2)).mpr p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    ((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

private def ThreefoldOverlapMappingTorus.Elliptic.upstairsPolarHomeomorph (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    PuncturedUpstairs j v hv r ≃ₜ
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄) :=
  (upstairsRootHomeomorph j v hv r).trans
    (((ThreefoldOverlapMappingTorus.polarHomeomorph j.order r).prodCongr
          (Homeomorph.refl RealTorus₄)).trans
      (Homeomorph.prodAssoc _ _ _))

private def ThreefoldOverlapMappingTorus.Elliptic.polarQuotient (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (p :
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄)) :
    PuncturedFilling j v hv r :=
  (puncturedSet j v hv r).restrictPreimage (Elliptic.fillingQuotient j v hv)
    ((upstairsPolarHomeomorph j v hv r).symm p)

private theorem
    ThreefoldOverlapMappingTorus.Elliptic.polarQuotient_isOpenQuotientMap (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    IsOpenQuotientMap (polarQuotient j v hv r) := by
  have hq : IsOpenQuotientMap (Elliptic.fillingQuotient j v hv) :=
    ⟨Elliptic.fillingQuotient_surjective j v hv, Elliptic.fillingQuotient_continuous j v hv,
      (Elliptic.fillingQuotient_isCoveringMap j v hv).isOpenMap⟩
  have hr := hq.restrictPreimage (puncturedSet j v hv r)
  let e := (upstairsPolarHomeomorph j v hv r).symm
  exact
    ⟨hr.surjective.comp e.surjective, hr.continuous.comp e.continuous,
      hr.isOpenMap.comp e.isOpenMap⟩

@[simp]
private theorem
    ThreefoldOverlapMappingTorus.Elliptic.polarQuotient_projection_norm (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (p :
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄)) :
    ‖(Elliptic.fillingProjection j v hv (polarQuotient j v hv r p) : ℂ)‖ = (p.1 : ℝ) ^ j.order := by
  change ‖(ThreefoldOverlapMappingTorus.root j.order r p.1 p.2.1 : ℂ) ^ j.order‖ = _
  rw [norm_pow, ThreefoldOverlapMappingTorus.root_norm]

private abbrev
    ThreefoldOverlapMappingTorus.Elliptic.BoundaryQuotient (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) :=
  Elliptic.HigherHomology.MappingTorusQuotient.ProductQuotient j.order
    (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)

private def ThreefoldOverlapMappingTorus.Elliptic.radialQuotient (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (p :
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄)) :
    ThreefoldOverlapMappingTorus.Radius j.order r × BoundaryQuotient j v hv :=
  (p.1,
    Elliptic.HigherHomology.MappingTorusQuotient.project j.order
      (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1) p.2)

private theorem
    ThreefoldOverlapMappingTorus.Elliptic.radialQuotient_isOpenQuotientMap (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    IsOpenQuotientMap (radialQuotient j v hv r) := by
  let :=
    Elliptic.HigherHomology.MappingTorusQuotient.productAction j.order
      (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)
  let :=
    Elliptic.HigherHomology.MappingTorusQuotient.productAction_continuousConstSMul j.order
      (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)
  exact
    IsOpenQuotientMap.id.prodMap
      (Elliptic.FiniteQuotient.project_isOpenQuotientMap (Elliptic.CyclicGroup j)
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄))

private theorem ThreefoldOverlapMappingTorus.Elliptic.polarQuotient_eq_iff (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (p q :
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄)) :
    polarQuotient j v hv r p = polarQuotient j v hv r q ↔
      radialQuotient j v hv r p = radialQuotient j v hv r q := by
  let :=
    Elliptic.HigherHomology.MappingTorusQuotient.productAction j.order
      (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)
  let := Elliptic.familyAction j v hv.1
  rcases p with ⟨a, p⟩
  rcases q with ⟨b, q⟩
  constructor
  · intro h
    have hpow :=
      congrArg (fun y : PuncturedFilling j v hv r => ‖(Elliptic.fillingProjection j v hv y : ℂ)‖)
        h
    simp only [polarQuotient_projection_norm] at hpow
    have hab : a = b :=
      Subtype.ext ((pow_left_inj₀ a.property.1.le b.property.1.le j.order_pos.ne').mp hpow)
    subst b
    apply Prod.ext
    · rfl
    have hq :
      Elliptic.fillingQuotient j v hv (polarFamilyAt j r a p) =
        Elliptic.fillingQuotient j v hv (polarFamilyAt j r a q) :=
      congrArg Subtype.val h
    obtain ⟨g, hg⟩ :=
      (Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (Elliptic.CyclicGroup j)
            (Elliptic.Family j) _ _).mp
        hq
    apply
      (Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (Elliptic.CyclicGroup j)
          (ThreefoldOverlapMappingTorus.Circle × RealTorus₄) _ _).mpr
    refine ⟨g⁻¹, (polarFamilyAt_injective j r a) ?_⟩
    have he := polarFamilyAt_smul j v hv.1 r a g⁻¹ q
    have he' : polarFamilyAt j r a (g⁻¹ • q) = g • polarFamilyAt j r a q := by
      simpa only [inv_inv] using he
    exact he'.trans hg
  · intro h
    have hab : a = b := congrArg Prod.fst h
    subst b
    have hp :
      Elliptic.HigherHomology.MappingTorusQuotient.project j.order
          (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1) p =
        Elliptic.HigherHomology.MappingTorusQuotient.project j.order
          (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1) q :=
      congrArg Prod.snd h
    obtain ⟨g, hg⟩ :=
      (Elliptic.FiniteQuotient.project_eq_iff_mem_orbit (Elliptic.CyclicGroup j)
            (ThreefoldOverlapMappingTorus.Circle × RealTorus₄) _ _).mp
        hp
    apply Subtype.ext
    change
      Elliptic.fillingQuotient j v hv (polarFamilyAt j r a p) =
        Elliptic.fillingQuotient j v hv (polarFamilyAt j r a q)
    rw [← hg, polarFamilyAt_smul j v hv.1]
    exact Elliptic.FiniteQuotient.project_smul (Elliptic.CyclicGroup j) (Elliptic.Family j) g⁻¹ _

private def ThreefoldOverlapMappingTorus.Elliptic.puncturedPolarHomeomorph (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    PuncturedFilling j v hv r ≃ₜ
      ThreefoldOverlapMappingTorus.Radius j.order r × BoundaryQuotient j v hv :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph (polarQuotient j v hv r)
    (radialQuotient j v hv r) (polarQuotient_isOpenQuotientMap j v hv r).isQuotientMap
    (radialQuotient_isOpenQuotientMap j v hv r).isQuotientMap (polarQuotient_eq_iff j v hv r)

@[simp]
private theorem ThreefoldOverlapMappingTorus.Elliptic.puncturedPolarHomeomorph_symm_radialQuotient
    (j : Elliptic.Kind) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (p :
      ThreefoldOverlapMappingTorus.Radius j.order r ×
        (ThreefoldOverlapMappingTorus.Circle × RealTorus₄)) :
    (puncturedPolarHomeomorph j v hv r).symm (radialQuotient j v hv r p) =
      polarQuotient j v hv r p :=
  ThreefoldOverlapMappingTorus.quotientHomeomorph_symm_apply _ _ _ _ _ p

private abbrev ThreefoldOverlapMappingTorus.Elliptic.Boundary (j : Elliptic.Kind) (v : Lattice) :=
  MappingTorus.Torus (Elliptic.flatTorusAffine j v)

private def ThreefoldOverlapMappingTorus.Elliptic.puncturedProductHomeomorph (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ) :
    PuncturedFilling j v hv r ≃ₜ ThreefoldOverlapMappingTorus.Radius j.order r × Boundary j v :=
  (puncturedPolarHomeomorph j v hv r).trans
    ((Homeomorph.refl _).prodCongr
      (Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph j.order
        (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)))

private theorem ThreefoldOverlapMappingTorus.Elliptic.puncturedProductHomeomorph_symm_mk
    (j : Elliptic.Kind) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) (t : ℝ) (x : RealTorus₄) :
    (puncturedProductHomeomorph j v hv r).symm
        (a, MappingTorus.mk (Elliptic.flatTorusAffine j v) (t, x)) =
      polarQuotient j v hv r
        (a, (((t / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle), x)) := by
  change
    (puncturedPolarHomeomorph j v hv r).symm
        (a,
          (Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph j.order
                (Elliptic.flatTorusAffine j v).symm (affine_symm_pow_order j v hv.1)).symm
            (MappingTorus.mk _ (t, x))) =
      _
  rw [Elliptic.HigherHomology.MappingTorusQuotient.mappingTorusHomeomorph_symm_mk]
  exact
    puncturedPolarHomeomorph_symm_radialQuotient j v hv r
      (a, (((t / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle), x))

private def
    ThreefoldOverlapMappingTorus.Elliptic.puncturedMappingTorusHomotopyEquiv (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) :
    PuncturedFilling j v hv r ≃ₕ Boundary j v :=
  (puncturedProductHomeomorph j v hv r).toHomotopyEquiv.trans
    (ThreefoldOverlapMappingTorus.radiusProductHomotopyEquiv a (Boundary j v))

private def
    ThreefoldOverlapMappingTorus.Elliptic.boundaryInclusion (j : Elliptic.Kind) (v : Lattice)
    (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) :
    C(Boundary j v, PuncturedFilling j v hv r) :=
  ⟨(puncturedMappingTorusHomotopyEquiv j v hv r a).symm,
    (puncturedMappingTorusHomotopyEquiv j v hv r a).symm.continuous⟩

@[simp]
private theorem ThreefoldOverlapMappingTorus.Elliptic.boundaryInclusion_mk (j : Elliptic.Kind)
    (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (r : ℝ)
    (a : ThreefoldOverlapMappingTorus.Radius j.order r) (t : ℝ) (x : RealTorus₄) :
    boundaryInclusion j v hv r a (MappingTorus.mk (Elliptic.flatTorusAffine j v) (t, x)) =
      polarQuotient j v hv r
        (a, (((t / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle), x)) :=
  puncturedProductHomeomorph_symm_mk j v hv r a t x

private def FundamentalGroupVanKampen.TwoOpenCover.chartPath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    Path (D.baseChart i) x :=
  FundamentalGroupVanKampen.pathIn (D.pathTo x.val) (D.base_mem_chart i) x.property
    (D.pathTo_mem i x.val x.property)

@[simp]
private theorem
    FundamentalGroupVanKampen.TwoOpenCover.chartPath_base {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) :
    D.chartPath i (D.baseChart i) = Path.refl (D.baseChart i) := by
  simp only [chartPath, baseChart, D.pathTo_base, FundamentalGroupVanKampen.pathIn_refl]

private def FundamentalGroupVanKampen.TwoOpenCover.chartPathClass {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    Path.Homotopic.Quotient (D.baseChart i) x :=
  Path.Homotopic.Quotient.mk (D.chartPath i x)

@[simp]
private theorem FundamentalGroupVanKampen.TwoOpenCover.chartPathClass_base {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) :
    D.chartPathClass i (D.baseChart i) = Path.Homotopic.Quotient.refl (D.baseChart i) := by
  simp only [chartPathClass, D.chartPath_base, Path.Homotopic.Quotient.mk_refl]

private def FundamentalGroupVanKampen.TwoOpenCover.closePath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) {x y : D.chart i} (p : Path x y) :
    FundamentalGroup (D.chart i) (D.baseChart i) :=
  TriangleRegularBaseFundamentalGroup.basedLoop (D.chartPathClass i)
    (Path.Homotopic.Quotient.mk p)

@[simp]
private theorem
    FundamentalGroupVanKampen.TwoOpenCover.closePath_refl {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (x : D.chart i) :
    D.closePath i (Path.refl x) = 1 :=
  TriangleRegularBaseFundamentalGroup.basedLoop_refl _ _

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.closePath_trans {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) {x y z : D.chart i} (p : Path x y)
    (q : Path y z) : D.closePath i (p.trans q) = D.closePath i q * D.closePath i p := by
  exact
    TriangleRegularBaseFundamentalGroup.basedLoop_trans (D.chartPathClass i)
      (Path.Homotopic.Quotient.mk p) (Path.Homotopic.Quotient.mk q)

private theorem FundamentalGroupVanKampen.TwoOpenCover.closePath_homotopic {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool)
    {x y : D.chart i} {p q : Path x y} (hpq : Path.Homotopic p q) :
    D.closePath i p = D.closePath i q := by
  unfold closePath
  rw [Path.Homotopic.Quotient.eq.mpr hpq]

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.closePath_loop {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool)
    (p : Path (D.baseChart i) (D.baseChart i)) : D.closePath i p = Path.Homotopic.Quotient.mk p :=
  by
  simp only [closePath, TriangleRegularBaseFundamentalGroup.basedLoop, D.chartPathClass_base,
    Path.Homotopic.Quotient.refl_trans]
  exact Path.Homotopic.Quotient.trans_refl _

private def
    FundamentalGroupVanKampen.TwoOpenCover.chartHom {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) : FundamentalGroup (D.chart i) (D.baseChart i) →* G := by
  cases i
  · exact fU
  · exact fV

private def
    FundamentalGroupVanKampen.TwoOpenCover.localValue {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ D.chart i) : G :=
  (D.chartHom fU fV i
      (D.closePath i
        (FundamentalGroupVanKampen.pathIn (S := (D.chart i : Set X)) p (by simpa using hp 0)
          (by simpa using hp 1) hp)))⁻¹

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.localValue_refl {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) (x : X) (hx : ∀ t, Path.refl x t ∈ D.chart i) :
    D.localValue fU fV i (Path.refl x) hx = 1 := by
  simp only [localValue, FundamentalGroupVanKampen.pathIn_refl, D.closePath_refl, map_one,
    inv_one]

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.localValue_trans {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (i : Bool) {x y z : X} (p : Path x y) (q : Path y z)
    (hp : ∀ t, p t ∈ D.chart i) (hq : ∀ t, q t ∈ D.chart i) (hpq : ∀ t, p.trans q t ∈ D.chart i) :
    D.localValue fU fV i (p.trans q) hpq =
      D.localValue fU fV i p hp * D.localValue fU fV i q hq := by
  have hx : x ∈ D.chart i := by simpa using hp 0
  have hy : y ∈ D.chart i := by simpa using hp 1
  have hz : z ∈ D.chart i := by simpa using hq 1
  unfold localValue
  rw [FundamentalGroupVanKampen.pathIn_trans p q hx hy hz hp hq hpq, D.closePath_trans, map_mul,
    mul_inv_rev]

private theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_subpath_mul {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool) {x y : X} (p : Path x y)
    (a b c : (unitInterval)) (hab : a ≤ b) (hbc : b ≤ c) (hpab : ∀ t, p.subpath a b t ∈ D.chart i)
    (hpbc : ∀ t, p.subpath b c t ∈ D.chart i) (hpac : ∀ t, p.subpath a c t ∈ D.chart i) :
    D.localValue fU fV i (p.subpath a c) hpac =
      D.localValue fU fV i (p.subpath a b) hpab * D.localValue fU fV i (p.subpath b c) hpbc := by
  have ha : p a ∈ D.chart i := by simpa using hpab 0
  have hb : p b ∈ D.chart i := by simpa using hpab 1
  have hc : p c ∈ D.chart i := by simpa using hpbc 1
  have H :=
    FundamentalGroupVanKampen.subpathTransSubpathIn p a b c hab hbc ha hb hc hpab hpbc hpac
  unfold localValue
  rw [← D.closePath_homotopic i ⟨H⟩, D.closePath_trans, map_mul, mul_inv_rev]

private theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_homotopy {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool) {x y : X} (p q : Path x y)
    (hp : ∀ t, p t ∈ D.chart i) (hq : ∀ t, q t ∈ D.chart i) (H : Path.Homotopy p q)
    (hH : ∀ s, H s ∈ D.chart i) : D.localValue fU fV i p hp = D.localValue fU fV i q hq := by
  have hx : x ∈ D.chart i := by simpa using hp 0
  have hy : y ∈ D.chart i := by simpa using hp 1
  unfold localValue
  rw [D.closePath_homotopic i ⟨FundamentalGroupVanKampen.homotopyIn p q hx hy hp hq H hH⟩]

private def FundamentalGroupVanKampen.TwoOpenCover.overlapPath {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : D.overlap) : Path D.baseOverlapPoint x :=
  FundamentalGroupVanKampen.pathIn (S := (D.overlap : Set X)) (D.pathTo x.val) ⟨D.baseU, D.baseV⟩
    x.property
    (fun t =>
      ⟨D.pathTo_mem Bool.false x.val x.property.1 t, D.pathTo_mem Bool.true x.val x.property.2 t⟩)

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.overlapPath_map_U {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : D.overlap) :
    (D.overlapPath x).map D.overlapToU.continuous = D.chartPath Bool.false (D.overlapToU x) := by
  ext t
  rfl

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.overlapPath_map_V {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (x : D.overlap) :
    (D.overlapPath x).map D.overlapToV.continuous = D.chartPath Bool.true (D.overlapToV x) := by
  ext t
  rfl

private def FundamentalGroupVanKampen.TwoOpenCover.overlapClose {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.OverlapGroup :=
  TriangleRegularBaseFundamentalGroup.basedLoop
    (fun x => Path.Homotopic.Quotient.mk (D.overlapPath x)) (Path.Homotopic.Quotient.mk p)

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.overlapHomU_close {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.overlapHomU (D.overlapClose p) = D.closePath Bool.false (p.map D.overlapToU.continuous) := by
  change
    Path.Homotopic.Quotient.mk
        ((((D.overlapPath x).trans p).trans (D.overlapPath y).symm).map D.overlapToU.continuous) =
      Path.Homotopic.Quotient.mk
        (((D.chartPath Bool.false (D.overlapToU x)).trans (p.map D.overlapToU.continuous)).trans
          (D.chartPath Bool.false (D.overlapToU y)).symm)
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, D.overlapPath_map_U, D.overlapPath_map_U]
  rfl

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.overlapHomV_close {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) {x y : D.overlap} (p : Path x y) :
    D.overlapHomV (D.overlapClose p) = D.closePath Bool.true (p.map D.overlapToV.continuous) := by
  change
    Path.Homotopic.Quotient.mk
        ((((D.overlapPath x).trans p).trans (D.overlapPath y).symm).map D.overlapToV.continuous) =
      Path.Homotopic.Quotient.mk
        (((D.chartPath Bool.true (D.overlapToV x)).trans (p.map D.overlapToV.continuous)).trans
          (D.chartPath Bool.true (D.overlapToV y)).symm)
  rw [Path.map_trans, Path.map_trans, ← Path.map_symm, D.overlapPath_map_V, D.overlapPath_map_V]
  rfl

private theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_compatible_UV {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) {x y : X} (p : Path x y)
    (hU : ∀ t, p t ∈ D.U) (hV : ∀ t, p t ∈ D.V) :
    D.localValue fU fV Bool.false p hU = D.localValue fU fV Bool.true p hV := by
  have hxU : x ∈ D.U := by simpa using hU 0
  have hxV : x ∈ D.V := by simpa using hV 0
  have hyU : y ∈ D.U := by simpa using hU 1
  have hyV : y ∈ D.V := by simpa using hV 1
  let pI :=
    FundamentalGroupVanKampen.pathIn (S := (D.overlap : Set X)) p ⟨hxU, hxV⟩ ⟨hyU, hyV⟩
      (fun t => ⟨hU t, hV t⟩)
  have hpU : pI.map D.overlapToU.continuous = FundamentalGroupVanKampen.pathIn p hxU hyU hU := by
    ext t
    rfl
  have hpV : pI.map D.overlapToV.continuous = FundamentalGroupVanKampen.pathIn p hxV hyV hV := by
    ext t
    rfl
  have h := DFunLike.congr_fun hf (D.overlapClose pI)
  change fU (D.overlapHomU (D.overlapClose pI)) = fV (D.overlapHomV (D.overlapClose pI)) at h
  have hU' := congrArg fU ((D.overlapHomU_close pI).trans (congrArg (D.closePath Bool.false) hpU))
  have hV' := congrArg fV ((D.overlapHomV_close pI).trans (congrArg (D.closePath Bool.true) hpV))
  exact congrArg (fun a : G => a⁻¹) (hU'.symm.trans (h.trans hV'))

private theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_compatible {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) (i j : Bool) {x y : X}
    (p : Path x y) (hi : ∀ t, p t ∈ D.chart i) (hj : ∀ t, p t ∈ D.chart j) :
    D.localValue fU fV i p hi = D.localValue fU fV j p hj := by
  cases i <;> cases j
  · rfl
  · exact D.localValue_compatible_UV fU fV hf p hi hj
  · exact (D.localValue_compatible_UV fU fV hf p hj hi).symm
  · rfl

private def FundamentalGroupVanKampen.TwoOpenCover.localPathValue {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    FundamentalGroupVanKampen.LocalPathValue (fun i => (D.chart i : Set X)) G
    where
  value := D.localValue fU fV
  refl := D.localValue_refl fU fV
  trans := D.localValue_trans fU fV
  subpath_mul := D.localValue_subpath_mul fU fV
  compatible := D.localValue_compatible fU fV hf

private theorem FundamentalGroupVanKampen.TwoOpenCover.localPathValue_homotopyInvariant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.localPathValue fU fV hf).HomotopyInvariant :=
  D.localValue_homotopy fU fV

private theorem FundamentalGroupVanKampen.TwoOpenCover.localValue_map_loop {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (i : Bool)
    (p : Path (D.baseChart i) (D.baseChart i)) :
    D.localValue fU fV i (p.map continuous_subtype_val) (fun t => (p t).property) =
      (D.chartHom fU fV i (Path.Homotopic.Quotient.mk p))⁻¹ := by
  unfold localValue
  apply
    congrArg (fun a : FundamentalGroup (D.chart i) (D.baseChart i) => (D.chartHom fU fV i a)⁻¹)
  rw [D.closePath_loop]
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

private def FundamentalGroupVanKampen.PathValue.fundamentalGroupHom {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G) (hV : V.HomotopyInvariant)
    (o : X) : FundamentalGroup X o →* G
    where
  toFun :=
    _root_.Quotient.lift (fun p : Path o o => (V.value p)⁻¹)
      (fun p q h => congrArg (fun a : G => a⁻¹) (hV p q h))
  map_one' := by
    change (V.value (Path.refl o))⁻¹ = 1
    rw [V.refl, inv_one]
  map_mul' := by
    intro a b
    obtain ⟨p⟩ := a
    obtain ⟨q⟩ := b
    change (V.value (q.trans p))⁻¹ = (V.value p)⁻¹ * (V.value q)⁻¹
    rw [V.trans, mul_inv_rev]

private theorem
    FundamentalGroupVanKampen.mem_of_subpath_mem {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) {a b : (unitInterval)} (hab : a ≤ b) {s : Set X}
    (hp : ∀ t, p.subpath a b t ∈ s) {t : (unitInterval)} (ht : t ∈ Set.Icc a b) : p t ∈ s := by
  have hsub : Set.range (p.subpath a b) ⊆ s := Set.range_subset_iff.mpr hp
  rw [p.range_subpath_of_le a b hab] at hsub
  exact hsub ⟨t, ht, rfl⟩

private theorem
    FundamentalGroupVanKampen.subpath_mem_mono {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) {a b c d : (unitInterval)} (hab : a ≤ b) (hcd : c ≤ d) (hac : a ≤ c)
    (hdb : d ≤ b) {s : Set X} (hp : ∀ t, p.subpath a b t ∈ s) : ∀ t, p.subpath c d t ∈ s := by
  apply subpath_mem_of_mem_Icc p hcd
  intro t ht
  exact mem_of_subpath_mem p hab hp ⟨hac.trans ht.1, ht.2.trans hdb⟩

private theorem FundamentalGroupVanKampen.exists_path_subdivision {X : Type*} [TopologicalSpace X]
    {ι : Type*} {U : ι → Set X} (hopen : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ)
    {x y : X} (p : Path x y) :
    ∃ t : ℕ → (unitInterval),
      t 0 = 0 ∧
        Monotone t ∧ (∃ n, t n = 1) ∧ ∀ n, ∃ i, ∀ s ∈ Set.Icc (t n) (t (n + 1)), p s ∈ U i := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval (fun i ↦ (hopen i).preimage p.continuous)
      (by
        intro s _
        have hs : p s ∈ ⋃ i, U i := by rw [hcover]; trivial
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
        exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  exact ⟨t, ht0, hmono, ⟨n, hn n le_rfl⟩, fun n ↦ hsub n⟩

private def FundamentalGroupVanKampen.LocalPathValue.IsPrimitive {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    (F : (unitInterval) → G) : Prop :=
  ∀ (a b : (unitInterval)),
    a ≤ b → ∀ i (h : ∀ t, p.subpath a b t ∈ U i), F b = F a * L.value i (p.subpath a b) h

private def
    FundamentalGroupVanKampen.LocalPathValue.IsPrimitiveUpTo {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    (F : (unitInterval) → G) (r : (unitInterval)) : Prop :=
  ∀ (a b : (unitInterval)),
    a ≤ b → b ≤ r → ∀ i (h : ∀ t, p.subpath a b t ∈ U i), F b = F a * L.value i (p.subpath a b) h

private theorem FundamentalGroupVanKampen.LocalPathValue.isPrimitiveUpTo_zero {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) {x y : X} (p : Path x y) :
    L.IsPrimitiveUpTo p (fun _ ↦ 1) 0 := by
  intro a b hab hb i hi
  have ha0 : a = 0 := le_antisymm (hab.trans hb) bot_le
  have hb0 : b = 0 := le_antisymm hb bot_le
  subst a
  subst b
  simp only [Path.subpath_self, L.refl, mul_one]

private theorem FundamentalGroupVanKampen.LocalPathValue.exists_primitiveUpTo_step {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    {F : (unitInterval) → G} {a b : (unitInterval)} (_hab : a ≤ b) (i : ι)
    (hi : ∀ t ∈ Set.Icc a b, p t ∈ U i) (hF : L.IsPrimitiveUpTo p F a) :
    ∃ H : (unitInterval) → G, H 0 = F 0 ∧ L.IsPrimitiveUpTo p H b := by
  classical
  let memi (s t : (unitInterval)) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    ∀ u, p.subpath s t u ∈ U i :=
    FundamentalGroupVanKampen.subpath_mem_of_mem_Icc p hst
      (fun u hu ↦ hi u ⟨has.trans hu.1, hu.2.trans htb⟩)
  let H (t : (unitInterval)) : G :=
    if hta : t ≤ a then F t
    else
      if htb : t ≤ b then F a * L.value i (p.subpath a t) (memi a t le_rfl (le_of_not_ge hta) htb)
      else 1
  have hleft (t : (unitInterval)) (hta : t ≤ a) : H t = F t := by exact dite_eq_left hta
  have hright (t : (unitInterval)) (hat : a ≤ t) (htb : t ≤ b) :
    H t = F a * L.value i (p.subpath a t) (memi a t le_rfl hat htb) := by
    by_cases hta : t ≤ a
    · have ht : t = a := le_antisymm hta hat
      subst t
      rw [hleft a le_rfl]
      simp only [Path.subpath_self, L.refl, mul_one]
    · dsimp only [H]
      rw [dite_eq_right hta, dite_eq_left htb]
  refine ⟨H, hleft 0 bot_le, ?_⟩
  intro s t hst htb j hj
  by_cases hta : t ≤ a
  · rw [hleft t hta, hleft s (hst.trans hta)]
    exact hF s t hst hta j hj
  have hat : a ≤ t := le_of_not_ge hta
  by_cases hsa : s ≤ a
  · have hjsa : ∀ u, p.subpath s a u ∈ U j :=
      FundamentalGroupVanKampen.subpath_mem_mono p hst hsa le_rfl hat hj
    have hjat : ∀ u, p.subpath a t u ∈ U j :=
      FundamentalGroupVanKampen.subpath_mem_mono p hst hat hsa le_rfl hj
    calc
      H t = F a * L.value i (p.subpath a t) (memi a t le_rfl hat htb) := hright t hat htb
      _ = F a * L.value j (p.subpath a t) hjat := by rw [L.compatible i j (p.subpath a t) _ hjat]
      _ = (F s * L.value j (p.subpath s a) hjsa) * L.value j (p.subpath a t) hjat := by
        rw [hF s a hsa le_rfl j hjsa]
      _ = F s * L.value j (p.subpath s t) hj := by
        rw [L.subpath_mul j p s a t hsa hat hjsa hjat hj, mul_assoc]
      _ = H s * L.value j (p.subpath s t) hj := by rw [hleft s hsa]
  · have has : a ≤ s := le_of_not_ge hsa
    rw [hright t hat htb, hright s has (hst.trans htb)]
    rw [L.compatible j i (p.subpath s t) hj (memi s t has hst htb)]
    rw [L.subpath_mul i p a s t has hst (memi a s le_rfl has (hst.trans htb))
        (memi s t has hst htb) (memi a t le_rfl hat htb)]
    exact (mul_assoc _ _ _).symm

private theorem
    FundamentalGroupVanKampen.LocalPathValue.exists_primitive {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    ∃ F : (unitInterval) → G, F 0 = 1 ∧ L.IsPrimitive p F := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    FundamentalGroupVanKampen.exists_path_subdivision hopen hcover p
  have hprefix : ∀ m, ∃ F : (unitInterval) → G, F 0 = 1 ∧ L.IsPrimitiveUpTo p F (t m) := by
    intro m
    induction m with
    | zero =>
      refine ⟨fun _ ↦ 1, rfl, ?_⟩
      rw [ht0]
      exact L.isPrimitiveUpTo_zero p
    | succ m ih =>
      obtain ⟨F, hF0, hF⟩ := ih
      obtain ⟨i, hi⟩ := hsub m
      obtain ⟨H, hH0, hH⟩ := L.exists_primitiveUpTo_step p (hmono m.le_succ) i hi hF
      exact ⟨H, hH0.trans hF0, hH⟩
  obtain ⟨F, hF0, hF⟩ := hprefix n
  refine ⟨F, hF0, ?_⟩
  intro a b hab i hi
  exact hF a b hab (by rw [hn]; exact le_top) i hi

private theorem
    FundamentalGroupVanKampen.LocalPathValue.primitive_unique {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) {F H : (unitInterval) → G}
    (hF : L.IsPrimitive p F) (hH : L.IsPrimitive p H) (h0 : F 0 = H 0) : F = H := by
  obtain ⟨t, ht0, hmono, ⟨n, hn⟩, hsub⟩ :=
    FundamentalGroupVanKampen.exists_path_subdivision hopen hcover p
  have hprefix : ∀ m, ∀ s ≤ t m, F s = H s := by
    intro m
    induction m with
    | zero =>
      intro s hs
      have hs0 : s = 0 := le_antisymm (by simpa only [ht0] using hs) bot_le
      simpa only [hs0] using h0
    | succ m ih =>
      intro s hs
      by_cases hst : s ≤ t m
      · exact ih s hst
      have hts : t m ≤ s := le_of_not_ge hst
      obtain ⟨i, hi⟩ := hsub m
      have hlocal : ∀ u, p.subpath (t m) s u ∈ U i :=
        FundamentalGroupVanKampen.subpath_mem_of_mem_Icc p hts
          (fun u hu ↦ hi u ⟨hu.1, hu.2.trans hs⟩)
      rw [hF (t m) s hts i hlocal, hH (t m) s hts i hlocal, ih (t m) le_rfl]
  funext s
  exact hprefix n s (by rw [hn]; exact le_top)

private theorem FundamentalGroupVanKampen.convexComb_monotone {a b : (unitInterval)} (hab : a ≤ b) :
    Monotone (Set.Icc.convexComb a b) := by
  intro s t hst
  change (1 - (s : ℝ)) * a + s * b ≤ (1 - (t : ℝ)) * a + t * b
  have hab' : (a : ℝ) ≤ b := hab
  have hst' : (s : ℝ) ≤ t := hst
  nlinarith [mul_nonneg (sub_nonneg.mpr hab') (sub_nonneg.mpr hst')]

private theorem FundamentalGroupVanKampen.convexComb_comp (a b s t u : (unitInterval)) :
    Set.Icc.convexComb a b (Set.Icc.convexComb s t u) =
      Set.Icc.convexComb (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) u := by
  apply Subtype.ext
  simp only [Set.Icc.coe_convexComb]
  ring

private theorem FundamentalGroupVanKampen.subpath_subpath {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) (a b s t : (unitInterval)) :
    (p.subpath a b).subpath s t =
      p.subpath (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) := by
  ext u
  change
    p (Set.Icc.convexComb a b (Set.Icc.convexComb s t u)) =
      p (Set.Icc.convexComb (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) u)
  rw [convexComb_comp]

private def FundamentalGroupVanKampen.intervalHalf : (unitInterval) :=
  ⟨1 / 2, by norm_num⟩

private theorem
    FundamentalGroupVanKampen.trans_convexComb_first_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) (t : (unitInterval)) :
    (p.trans q) (Set.Icc.convexComb 0 intervalHalf t) = p t := by
  have ht : (Set.Icc.convexComb 0 intervalHalf t : ℝ) ≤ 1 / 2 := by
    change (1 - (t : ℝ)) * 0 + t * (1 / 2) ≤ 1 / 2
    linarith [t.2.2]
  rw [← Path.extend_apply (p.trans q), Path.extend_trans_of_le_half p q ht]
  have heq : 2 * (Set.Icc.convexComb 0 intervalHalf t : ℝ) = t := by
    change 2 * ((1 - (t : ℝ)) * 0 + t * (1 / 2)) = t
    ring
  rw [heq, Path.extend_apply]

private theorem
    FundamentalGroupVanKampen.trans_convexComb_second_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) (t : (unitInterval)) :
    (p.trans q) (Set.Icc.convexComb intervalHalf 1 t) = q t := by
  have ht : 1 / 2 ≤ (Set.Icc.convexComb intervalHalf 1 t : ℝ) := by
    change 1 / 2 ≤ (1 - (t : ℝ)) * (1 / 2) + t * 1
    linarith [t.2.1]
  rw [← Path.extend_apply (p.trans q), Path.extend_trans_of_half_le p q ht]
  have heq : 2 * (Set.Icc.convexComb intervalHalf 1 t : ℝ) - 1 = t := by
    change 2 * ((1 - (t : ℝ)) * (1 / 2) + t * 1) - 1 = t
    ring
  rw [heq, Path.extend_apply]

@[simp]
private theorem FundamentalGroupVanKampen.trans_apply_intervalHalf {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) : (p.trans q) intervalHalf = y := by
  simpa using trans_convexComb_first_half p q 1

private theorem FundamentalGroupVanKampen.trans_subpath_first_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (p.trans q).subpath 0 intervalHalf =
      p.cast (p.trans q).source (trans_apply_intervalHalf p q) := by
  ext t
  exact trans_convexComb_first_half p q t

private theorem FundamentalGroupVanKampen.trans_subpath_second_half {X : Type*} [TopologicalSpace X]
    {x y z : X} (p : Path x y) (q : Path y z) :
    (p.trans q).subpath intervalHalf 1 =
      q.cast (trans_apply_intervalHalf p q) (p.trans q).target := by
  ext t
  exact trans_convexComb_second_half p q t

private theorem FundamentalGroupVanKampen.LocalPathValue.value_eq_of_path_eq {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (i : ι) {x y : X} {p q : Path x y}
    (h : p = q) (hp : ∀ t, p t ∈ U i) (hq : ∀ t, q t ∈ U i) : L.value i p hp = L.value i q hq := by
  cases h
  rfl

private theorem FundamentalGroupVanKampen.LocalPathValue.isPrimitive_subpath {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) {x y : X} (p : Path x y)
    {F : (unitInterval) → G} (hF : L.IsPrimitive p F) (a b : (unitInterval)) (hab : a ≤ b) :
    L.IsPrimitive (p.subpath a b) (fun t => (F a)⁻¹ * F (Set.Icc.convexComb a b t)) := by
  intro s t hst i hi
  have heq := FundamentalGroupVanKampen.subpath_subpath p a b s t
  have hlocal : ∀ v, p.subpath (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t) v ∈ U i := by
    intro v
    rw [← heq]
    exact hi v
  have hv := L.value_eq_of_path_eq i heq hi hlocal
  have hstep :=
    hF (Set.Icc.convexComb a b s) (Set.Icc.convexComb a b t)
      (FundamentalGroupVanKampen.convexComb_monotone hab hst) i hlocal
  change
    (F a)⁻¹ * F (Set.Icc.convexComb a b t) =
      ((F a)⁻¹ * F (Set.Icc.convexComb a b s)) * L.value i ((p.subpath a b).subpath s t) hi
  rw [hv, hstep, mul_assoc]
  rfl

private def FundamentalGroupVanKampen.LocalPathValue.transport {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) : (unitInterval) → G :=
  (L.exists_primitive hopen hcover p).choose

@[simp]
private theorem
    FundamentalGroupVanKampen.LocalPathValue.transport_zero {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.transport hopen hcover p 0 = 1 :=
  (L.exists_primitive hopen hcover p).choose_spec.1

private theorem FundamentalGroupVanKampen.LocalPathValue.transport_isPrimitive {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.IsPrimitive p (L.transport hopen hcover p) :=
  (L.exists_primitive hopen hcover p).choose_spec.2

private theorem FundamentalGroupVanKampen.LocalPathValue.transport_subpath {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) (a b : (unitInterval)) (hab : a ≤ b)
    (t : (unitInterval)) :
    L.transport hopen hcover (p.subpath a b) t =
      (L.transport hopen hcover p a)⁻¹ * L.transport hopen hcover p (Set.Icc.convexComb a b t) := by
  apply
    congrFun
      (L.primitive_unique hopen hcover (p.subpath a b)
        (L.transport_isPrimitive hopen hcover (p.subpath a b))
        (L.isPrimitive_subpath p (L.transport_isPrimitive hopen hcover p) a b hab) ?_)
      t
  simp only [transport_zero, Set.Icc.convexComb_zero, inv_mul_cancel]

private def
    FundamentalGroupVanKampen.LocalPathValue.rawValue {X : Type*} [TopologicalSpace X] {ι : Type*}
    {G : Type*} [Group G] {U : ι → Set X} (L : FundamentalGroupVanKampen.LocalPathValue U G)
    (hopen : ∀ i, IsOpen (U i)) (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) : G :=
  L.transport hopen hcover p 1

private theorem
    FundamentalGroupVanKampen.LocalPathValue.rawValue_cast {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y x' y' : X} (p : Path x y) (hx : x' = x) (hy : y' = y) :
    L.rawValue hopen hcover (p.cast hx hy) = L.rawValue hopen hcover p := by
  cases hx
  cases hy
  rfl

private theorem FundamentalGroupVanKampen.LocalPathValue.rawValue_subpath_zero_one {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) :
    L.rawValue hopen hcover (p.subpath 0 1) = L.rawValue hopen hcover p := by
  rw [Path.subpath_zero_one, L.rawValue_cast]

private theorem
    FundamentalGroupVanKampen.LocalPathValue.rawValue_subpath {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) (a b : (unitInterval))
    (hab : a ≤ b) :
    L.rawValue hopen hcover (p.subpath a b) =
      (L.transport hopen hcover p a)⁻¹ * L.transport hopen hcover p b := by
  simpa only [rawValue, Set.Icc.convexComb_one] using L.transport_subpath hopen hcover p a b hab 1

private theorem
    FundamentalGroupVanKampen.LocalPathValue.rawValue_local {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (i : ι) {x y : X} (p : Path x y) (hp : ∀ t, p t ∈ U i) :
    L.rawValue hopen hcover p = L.value i p hp := by
  have hs : ∀ t, p.subpath 0 1 t ∈ U i := fun t => hp _
  have h := L.transport_isPrimitive hopen hcover p 0 1 (by exact zero_le_one) i hs
  rw [L.transport_zero, one_mul] at h
  change L.rawValue hopen hcover p = _ at h
  have hc : ∀ t, p.cast p.source p.target t ∈ U i := hp
  exact
    h.trans
      ((L.value_eq_of_path_eq i (Path.subpath_zero_one p) hs hc).trans
        (L.value_cast i p p.source p.target hp hc))

private theorem
    FundamentalGroupVanKampen.LocalPathValue.rawValue_refl {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) (x : X) : L.rawValue hopen hcover (Path.refl x) = 1 := by
  have hx : x ∈ ⋃ i, U i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hp : ∀ t, Path.refl x t ∈ U i := fun _ => hi
  rw [L.rawValue_local hopen hcover i (Path.refl x) hp, L.refl]

private theorem FundamentalGroupVanKampen.LocalPathValue.rawValue_subpath_mul {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y : X} (p : Path x y) (a b c : (unitInterval))
    (hab : a ≤ b) (hbc : b ≤ c) :
    L.rawValue hopen hcover (p.subpath a c) =
      L.rawValue hopen hcover (p.subpath a b) * L.rawValue hopen hcover (p.subpath b c) := by
  rw [L.rawValue_subpath hopen hcover p a c (hab.trans hbc),
    L.rawValue_subpath hopen hcover p a b hab, L.rawValue_subpath hopen hcover p b c hbc,
    mul_assoc, mul_inv_cancel_left]

private theorem
    FundamentalGroupVanKampen.LocalPathValue.rawValue_trans {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) {x y z : X} (p : Path x y) (q : Path y z) :
    L.rawValue hopen hcover (p.trans q) = L.rawValue hopen hcover p * L.rawValue hopen hcover q :=
  by
  calc
    L.rawValue hopen hcover (p.trans q) = L.rawValue hopen hcover ((p.trans q).subpath 0 1) :=
      (L.rawValue_subpath_zero_one hopen hcover (p.trans q)).symm
    _ =
        L.rawValue hopen hcover ((p.trans q).subpath 0 FundamentalGroupVanKampen.intervalHalf) *
          L.rawValue hopen hcover
            ((p.trans q).subpath FundamentalGroupVanKampen.intervalHalf 1) :=
      (L.rawValue_subpath_mul hopen hcover (p.trans q) 0 FundamentalGroupVanKampen.intervalHalf 1
        unitInterval.nonneg' unitInterval.le_one')
    _ = L.rawValue hopen hcover p * L.rawValue hopen hcover q := by
      rw [FundamentalGroupVanKampen.trans_subpath_first_half,
        FundamentalGroupVanKampen.trans_subpath_second_half, L.rawValue_cast, L.rawValue_cast]

private def FundamentalGroupVanKampen.LocalPathValue.extension {X : Type*} [TopologicalSpace X]
    {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) : FundamentalGroupVanKampen.PathValue X G
    where
  value := L.rawValue hopen hcover
  refl := L.rawValue_refl hopen hcover
  trans := L.rawValue_trans hopen hcover
  subpath_mul := L.rawValue_subpath_mul hopen hcover

private theorem FundamentalGroupVanKampen.LocalPathValue.extension_extends {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : (⋃ i, U i) = Set.univ) : (L.extension hopen hcover).Extends L := by
  intro i x y p hp
  exact L.rawValue_local hopen hcover i p hp

private def FundamentalGroupVanKampen.squareHorizontal {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s : (unitInterval)) : Path (F (s, 0)) (F (s, 1))
    where
  toFun t := F (s, t)
  continuous_toFun := F.continuous.comp (continuous_const.prodMk continuous_id)
  source' := rfl
  target' := rfl

private def FundamentalGroupVanKampen.squareVertical {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (t : (unitInterval)) : Path (F (0, t)) (F (1, t))
    where
  toFun s := F (s, t)
  continuous_toFun := F.continuous.comp (continuous_id.prodMk continuous_const)
  source' := rfl
  target' := rfl

private def FundamentalGroupVanKampen.squarePathHomotopy {x y : (unitInterval) × (unitInterval)}
    (p q : Path x y) : Path.Homotopy p q
    where
  toFun
    u := (Set.Icc.convexComb (p u.2).1 (q u.2).1 u.1, Set.Icc.convexComb (p u.2).2 (q u.2).2 u.1)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact
        Set.Icc.continuous_convexComb_prod.comp
          (((p.continuous.comp continuous_snd).fst).prodMk
            (((q.continuous.comp continuous_snd).fst).prodMk continuous_fst))
    · exact
        Set.Icc.continuous_convexComb_prod.comp
          (((p.continuous.comp continuous_snd).snd).prodMk
            (((q.continuous.comp continuous_snd).snd).prodMk continuous_fst))
  map_zero_left u := by simp
  map_one_left u := by simp
  prop' r u hu := by rcases hu with rfl | rfl <;> simp

public
theorem FundamentalGroupVanKampen.convexComb_mem_Icc {s t u v : (unitInterval)}
    (hu : u ∈ Set.Icc s t) (hv : v ∈ Set.Icc s t) (r : (unitInterval)) :
    Set.Icc.convexComb u v r ∈ Set.Icc s t := by
  change (Set.Icc.convexComb u v r : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ)
  exact
    convex_Icc (s : ℝ) (t : ℝ) (show (u : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ) from hu)
      (show (v : ℝ) ∈ Set.Icc (s : ℝ) (t : ℝ) from hv) (unitInterval.one_minus_nonneg r)
      (unitInterval.nonneg r) (sub_add_cancel _ _)

private theorem FundamentalGroupVanKampen.squarePathHomotopy_mem_rectangle
    {x y : (unitInterval) × (unitInterval)} (p q : Path x y) (s t a b : (unitInterval))
    (hp : ∀ u, p u ∈ Set.Icc s t ×ˢ Set.Icc a b) (hq : ∀ u, q u ∈ Set.Icc s t ×ˢ Set.Icc a b)
    (u : (unitInterval) × (unitInterval)) :
    squarePathHomotopy p q u ∈ Set.Icc s t ×ˢ Set.Icc a b :=
  ⟨convexComb_mem_Icc (hp u.2).1 (hq u.2).1 u.1, convexComb_mem_Icc (hp u.2).2 (hq u.2).2 u.1⟩

private def FundamentalGroupVanKampen.rectangleHorizontalVertical (s t a b : (unitInterval)) :
    Path (s, a) (t, b) :=
  ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) s).subpath a b).trans
    ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) b).subpath s t)

private def FundamentalGroupVanKampen.rectangleVerticalHorizontal (s t a b : (unitInterval)) :
    Path (s, a) (t, b) :=
  ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) a).subpath s t).trans
    ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) t).subpath a b)

private theorem
    FundamentalGroupVanKampen.rectangleHorizontalVertical_map {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    (rectangleHorizontalVertical s t a b).map F.continuous =
      ((squareHorizontal F s).subpath a b).trans ((squareVertical F b).subpath s t) := by
  exact
    Path.map_trans
      ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) s).subpath a b)
      ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) b).subpath s t)
      F.continuous

private theorem
    FundamentalGroupVanKampen.rectangleVerticalHorizontal_map {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    (rectangleVerticalHorizontal s t a b).map F.continuous =
      ((squareVertical F a).subpath s t).trans ((squareHorizontal F t).subpath a b) := by
  exact
    Path.map_trans
      ((squareVertical (ContinuousMap.id ((unitInterval) × (unitInterval))) a).subpath s t)
      ((squareHorizontal (ContinuousMap.id ((unitInterval) × (unitInterval))) t).subpath a b)
      F.continuous

private theorem FundamentalGroupVanKampen.rectangleHorizontalVertical_mem (s t a b : (unitInterval))
    (hst : s ≤ t) (hab : a ≤ b) :
    ∀ u, rectangleHorizontalVertical s t a b u ∈ Set.Icc s t ×ˢ Set.Icc a b := by
  apply SimplyConnectedCover.trans_mem
  · intro u
    exact ⟨⟨le_rfl, hst⟩, Set.Icc.le_convexComb hab u, Set.Icc.convexComb_le hab u⟩
  · intro u
    exact ⟨⟨Set.Icc.le_convexComb hst u, Set.Icc.convexComb_le hst u⟩, hab, le_rfl⟩

private theorem FundamentalGroupVanKampen.rectangleVerticalHorizontal_mem (s t a b : (unitInterval))
    (hst : s ≤ t) (hab : a ≤ b) :
    ∀ u, rectangleVerticalHorizontal s t a b u ∈ Set.Icc s t ×ˢ Set.Icc a b := by
  apply SimplyConnectedCover.trans_mem
  · intro u
    exact ⟨⟨Set.Icc.le_convexComb hst u, Set.Icc.convexComb_le hst u⟩, le_rfl, hab⟩
  · intro u
    exact ⟨⟨hst, le_rfl⟩, Set.Icc.le_convexComb hab u, Set.Icc.convexComb_le hab u⟩

private def FundamentalGroupVanKampen.rectangleBoundaryHomotopy {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) :
    Path.Homotopy (((squareHorizontal F s).subpath a b).trans ((squareVertical F b).subpath s t))
      (((squareVertical F a).subpath s t).trans ((squareHorizontal F t).subpath a b)) :=
  ((squarePathHomotopy (rectangleHorizontalVertical s t a b)
            (rectangleVerticalHorizontal s t a b)).map
        F).cast
    (rectangleHorizontalVertical_map F s t a b) (rectangleVerticalHorizontal_map F s t a b)

private theorem
    FundamentalGroupVanKampen.rectangleBoundaryHomotopy_apply {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval))
    (u : (unitInterval) × (unitInterval)) :
    rectangleBoundaryHomotopy F s t a b u =
      F
        (squarePathHomotopy (rectangleHorizontalVertical s t a b)
          (rectangleVerticalHorizontal s t a b) u) :=
  rfl

private theorem
    FundamentalGroupVanKampen.rectangleBoundaryHomotopy_mem {X : Type*} [TopologicalSpace X]
    (F : C((unitInterval) × (unitInterval), X)) (s t a b : (unitInterval)) (hst : s ≤ t)
    (hab : a ≤ b) {A : Set X} (hcell : ∀ u ∈ Set.Icc s t ×ˢ Set.Icc a b, F u ∈ A)
    (u : (unitInterval) × (unitInterval)) : rectangleBoundaryHomotopy F s t a b u ∈ A := by
  rw [rectangleBoundaryHomotopy_apply]
  exact
    hcell _
      (squarePathHomotopy_mem_rectangle _ _ s t a b
        (rectangleHorizontalVertical_mem s t a b hst hab)
        (rectangleVerticalHorizontal_mem s t a b hst hab) u)

private theorem
    FundamentalGroupVanKampen.PathValue.square_cell_of_local {X : Type*} [TopologicalSpace X]
    {ι G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G) {U : ι → Set X}
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hExt : V.Extends L)
    (hL : L.HomotopyInvariant) (i : ι) (F : C((unitInterval) × (unitInterval), X))
    (s t a b : (unitInterval)) (hst : s ≤ t) (hab : a ≤ b)
    (hcell : ∀ u ∈ Set.Icc s t ×ˢ Set.Icc a b, F u ∈ U i) :
    V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath a b) *
        V.value ((FundamentalGroupVanKampen.squareVertical F b).subpath s t) =
      V.value ((FundamentalGroupVanKampen.squareVertical F a).subpath s t) *
        V.value ((FundamentalGroupVanKampen.squareHorizontal F t).subpath a b) := by
  let H := FundamentalGroupVanKampen.rectangleBoundaryHomotopy F s t a b
  have hH : ∀ u, H u ∈ U i :=
    FundamentalGroupVanKampen.rectangleBoundaryHomotopy_mem F s t a b hst hab hcell
  have hp :
    ∀ u,
      ((FundamentalGroupVanKampen.squareHorizontal F s).subpath a b).trans
          ((FundamentalGroupVanKampen.squareVertical F b).subpath s t) u ∈
        U i := by
    intro u
    exact (congrArg (fun x => x ∈ U i) (H.map_zero_left u)).mp (hH (0, u))
  have hq :
    ∀ u,
      ((FundamentalGroupVanKampen.squareVertical F a).subpath s t).trans
          ((FundamentalGroupVanKampen.squareHorizontal F t).subpath a b) u ∈
        U i := by
    intro u
    exact (congrArg (fun x => x ∈ U i) (H.map_one_left u)).mp (hH (1, u))
  calc
    _ =
        V.value
          (((FundamentalGroupVanKampen.squareHorizontal F s).subpath a b).trans
            ((FundamentalGroupVanKampen.squareVertical F b).subpath s t)) :=
      (V.trans _ _).symm
    _ = L.value i _ hp := (hExt i _ hp)
    _ = L.value i _ hq := (hL i _ _ hp hq H hH)
    _ =
        V.value
          (((FundamentalGroupVanKampen.squareVertical F a).subpath s t).trans
            ((FundamentalGroupVanKampen.squareHorizontal F t).subpath a b)) :=
      (hExt i _ hq).symm
    _ = _ := V.trans _ _

private theorem FundamentalGroupVanKampen.PathValue.value_eq_one_of_constant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    {x y : X} (p : Path x y) (hp : ∀ t, p t = x) : V.value p = 1 := by
  have hy : y = x := p.target.symm.trans (hp 1)
  subst y
  have heq : p = Path.refl x := by
    ext t
    exact hp t
  rw [heq, V.refl]

private theorem FundamentalGroupVanKampen.PathValue.square_strip {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    (F : C((unitInterval) × (unitInterval), X)) (s t : (unitInterval)) (d : ℕ → (unitInterval))
    (hmono : Monotone d) (n : ℕ)
    (hcell :
      ∀ k < n,
        V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d k) (d (k + 1))) *
            V.value ((FundamentalGroupVanKampen.squareVertical F (d (k + 1))).subpath s t) =
          V.value ((FundamentalGroupVanKampen.squareVertical F (d k)).subpath s t) *
            V.value
              ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d k) (d (k + 1)))) :
    V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
        V.value ((FundamentalGroupVanKampen.squareVertical F (d n)).subpath s t) =
      V.value ((FundamentalGroupVanKampen.squareVertical F (d 0)).subpath s t) *
        V.value ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d 0) (d n)) := by
  induction n with
  | zero => simp only [Path.subpath_self, V.refl, one_mul, mul_one]
  | succ n ih =>
    have hprev := ih (fun k hk => hcell k (Nat.lt_succ_of_lt hk))
    rw [V.subpath_mul _ (d 0) (d n) (d (n + 1)) (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n)),
      V.subpath_mul _ (d 0) (d n) (d (n + 1)) (hmono (Nat.zero_le n)) (hmono (Nat.le_succ n))]
    calc
      _ =
          V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
            (V.value
                ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d n) (d (n + 1))) *
              V.value ((FundamentalGroupVanKampen.squareVertical F (d (n + 1))).subpath s t)) :=
        mul_assoc _ _ _
      _ =
          V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
            (V.value ((FundamentalGroupVanKampen.squareVertical F (d n)).subpath s t) *
              V.value
                ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d n) (d (n + 1)))) := by
        rw [hcell n (Nat.lt_succ_self n)]
      _ =
          (V.value ((FundamentalGroupVanKampen.squareHorizontal F s).subpath (d 0) (d n)) *
              V.value ((FundamentalGroupVanKampen.squareVertical F (d n)).subpath s t)) *
            V.value
              ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d n) (d (n + 1))) :=
        (mul_assoc _ _ _).symm
      _ =
          (V.value ((FundamentalGroupVanKampen.squareVertical F (d 0)).subpath s t) *
              V.value ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d 0) (d n))) *
            V.value
              ((FundamentalGroupVanKampen.squareHorizontal F t).subpath (d n) (d (n + 1))) := by
        rw [hprev]
      _ = _ := mul_assoc _ _ _

private theorem FundamentalGroupVanKampen.PathValue.value_squareHorizontal_homotopy {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s : (unitInterval)) :
    V.value (FundamentalGroupVanKampen.squareHorizontal H.toContinuousMap s) =
      V.value (H.eval s) := by
  have heq :
    FundamentalGroupVanKampen.squareHorizontal H.toContinuousMap s =
      (H.eval s).cast (H.source s) (H.target s) := by
    ext t
    rfl
  rw [heq, V.value_cast]

private theorem FundamentalGroupVanKampen.PathValue.value_squareVertical_homotopy_zero {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s t : (unitInterval)) :
    V.value ((FundamentalGroupVanKampen.squareVertical H.toContinuousMap 0).subpath s t) = 1 := by
  apply V.value_eq_one_of_constant
  intro u
  change H (_, 0) = H (s, 0)
  simp only [Path.Homotopy.source]

private theorem FundamentalGroupVanKampen.PathValue.value_squareVertical_homotopy_one {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (V : FundamentalGroupVanKampen.PathValue X G)
    {x y : X} {p q : Path x y} (H : Path.Homotopy p q) (s t : (unitInterval)) :
    V.value ((FundamentalGroupVanKampen.squareVertical H.toContinuousMap 1).subpath s t) = 1 := by
  apply V.value_eq_one_of_constant
  intro u
  change H (_, 1) = H (s, 1)
  simp only [Path.Homotopy.target]

private theorem FundamentalGroupVanKampen.PathValue.value_eq_of_homotopy_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (V : FundamentalGroupVanKampen.PathValue X G)
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (hExt : V.Extends L) (hL : L.HomotopyInvariant) {x y : X}
    (p q : Path x y) (H : Path.Homotopy p q) : V.value p = V.value q := by
  have hpre : Set.univ ⊆ ⋃ i, H ⁻¹' U i := by
    rw [← Set.preimage_iUnion, hcover, Set.preimage_univ]
  obtain ⟨d, hd0, hdmono, ⟨n, hn⟩, hrect⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval_prod_self
      (fun i => (hopen i).preimage (ContinuousMapClass.map_continuous H)) hpre
  have hstep (k : ℕ) : V.value (H.eval (d k)) = V.value (H.eval (d (k + 1))) := by
    have hstrip :=
      V.square_strip H.toContinuousMap (d k) (d (k + 1)) d hdmono n
        (fun m _ => by
          obtain ⟨i, hi⟩ := hrect k m
          exact
            V.square_cell_of_local L hExt hL i H.toContinuousMap (d k) (d (k + 1)) (d m)
              (d (m + 1)) (hdmono (Nat.le_succ k)) (hdmono (Nat.le_succ m)) hi)
    rw [hd0, hn n le_rfl] at hstrip
    simpa only [V.value_subpath_zero_one, V.value_squareVertical_homotopy_zero,
      V.value_squareVertical_homotopy_one, V.value_squareHorizontal_homotopy, mul_one,
      one_mul] using hstrip
  have hwalk : ∀ k, V.value (H.eval (d 0)) = V.value (H.eval (d k)) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => exact ih.trans (hstep k)
  have hfinish := hwalk n
  simpa only [hd0, hn n le_rfl, Path.Homotopy.eval_zero, Path.Homotopy.eval_one] using hfinish

private theorem FundamentalGroupVanKampen.PathValue.homotopyInvariant_of_open_cover {X : Type*}
    [TopologicalSpace X] {ι : Type*} {G : Type*} [Group G] {U : ι → Set X}
    (V : FundamentalGroupVanKampen.PathValue X G)
    (L : FundamentalGroupVanKampen.LocalPathValue U G) (hopen : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ) (hExt : V.Extends L) (hL : L.HomotopyInvariant) :
    V.HomotopyInvariant := by
  intro x y p q h
  obtain ⟨H⟩ := h
  exact V.value_eq_of_homotopy_of_open_cover L hopen hcover hExt hL p q H

private def FundamentalGroupVanKampen.TwoOpenCover.globalPathValue {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) : FundamentalGroupVanKampen.PathValue X G :=
  (D.localPathValue fU fV hf).extension D.chart_open D.chart_cover

private theorem FundamentalGroupVanKampen.TwoOpenCover.globalPathValue_extends {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.globalPathValue fU fV hf).Extends (D.localPathValue fU fV hf) :=
  (D.localPathValue fU fV hf).extension_extends D.chart_open D.chart_cover

private theorem FundamentalGroupVanKampen.TwoOpenCover.globalPathValue_homotopyInvariant {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.globalPathValue fU fV hf).HomotopyInvariant :=
  FundamentalGroupVanKampen.PathValue.homotopyInvariant_of_open_cover (D.globalPathValue fU fV hf)
    (D.localPathValue fU fV hf) D.chart_open D.chart_cover (D.globalPathValue_extends fU fV hf)
    (D.localPathValue_homotopyInvariant fU fV hf)

private def FundamentalGroupVanKampen.TwoOpenCover.lift {X : Type*} [TopologicalSpace X] {G : Type*}
    [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) : FundamentalGroup X D.base →* G :=
  (D.globalPathValue fU fV hf).fundamentalGroupHom (D.globalPathValue_homotopyInvariant fU fV hf)
    D.base

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.lift_mk_of_mem {X : Type*} [TopologicalSpace X]
    {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X) (fU : D.UGroup →* G)
    (fV : D.VGroup →* G) (hf : D.Compatible fU fV) (i : Bool) (p : Path D.base D.base)
    (hp : ∀ t, p t ∈ D.chart i) :
    D.lift fU fV hf (Path.Homotopic.Quotient.mk p) = (D.localValue fU fV i p hp)⁻¹ :=
  congrArg (fun a : G => a⁻¹) (D.globalPathValue_extends fU fV hf i p hp)

private theorem FundamentalGroupVanKampen.TwoOpenCover.lift_comp_inclusionU {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.lift fU fV hf).comp D.inclusionHomU = fU := by
  ext γ
  obtain ⟨p⟩ := γ
  have h :=
    D.lift_mk_of_mem fU fV hf Bool.false (p.map continuous_subtype_val) (fun t => (p t).property)
  rw [D.localValue_map_loop, inv_inv] at h
  exact h

private theorem FundamentalGroupVanKampen.TwoOpenCover.lift_comp_inclusionV {X : Type*}
    [TopologicalSpace X] {G : Type*} [Group G] (D : FundamentalGroupVanKampen.TwoOpenCover X)
    (fU : D.UGroup →* G) (fV : D.VGroup →* G) (hf : D.Compatible fU fV) :
    (D.lift fU fV hf).comp D.inclusionHomV = fV := by
  ext γ
  obtain ⟨p⟩ := γ
  have h :=
    D.lift_mk_of_mem fU fV hf Bool.true (p.map continuous_subtype_val) (fun t => (p t).property)
  rw [D.localValue_map_loop, inv_inv] at h
  exact h

private abbrev FundamentalGroupVanKampen.TwoOpenCover.ChartGroup {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) :=
  FundamentalGroup (D.chart i) (D.baseChart i)

private def FundamentalGroupVanKampen.TwoOpenCover.overlapHom {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : (i : Bool) → D.OverlapGroup →* D.ChartGroup i
  | false => D.overlapHomU
  | true => D.overlapHomV

private def FundamentalGroupVanKampen.TwoOpenCover.inclusionHom {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    (i : Bool) → D.ChartGroup i →* FundamentalGroup X D.base
  | false => D.inclusionHomU
  | true => D.inclusionHomV

private theorem FundamentalGroupVanKampen.TwoOpenCover.inclusionHom_comp_overlapHom {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) :
    (D.inclusionHom i).comp (D.overlapHom i) = D.inclusionHomU.comp D.overlapHomU := by
  cases i
  · rfl
  · exact D.inclusionHom_compatible.symm

private abbrev FundamentalGroupVanKampen.TwoOpenCover.Pushout {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) :=
  Monoid.PushoutI D.overlapHom

private def FundamentalGroupVanKampen.TwoOpenCover.pushoutOfU {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.UGroup →* D.Pushout :=
  Monoid.PushoutI.of (φ := D.overlapHom) Bool.false

private def FundamentalGroupVanKampen.TwoOpenCover.pushoutOfV {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.VGroup →* D.Pushout :=
  Monoid.PushoutI.of (φ := D.overlapHom) Bool.true

private def FundamentalGroupVanKampen.TwoOpenCover.pushoutBase {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.OverlapGroup →* D.Pushout :=
  Monoid.PushoutI.base D.overlapHom

private theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutOfU_comp_overlapHomU {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.pushoutOfU.comp D.overlapHomU = D.pushoutBase :=
  Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) Bool.false

private theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutOfV_comp_overlapHomV {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.pushoutOfV.comp D.overlapHomV = D.pushoutBase :=
  Monoid.PushoutI.of_comp_eq_base (φ := D.overlapHom) Bool.true

private theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutOf_compatible {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.Compatible D.pushoutOfU D.pushoutOfV :=
  D.pushoutOfU_comp_overlapHomU.trans D.pushoutOfV_comp_overlapHomV.symm

private def FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.Pushout →* FundamentalGroup X D.base :=
  Monoid.PushoutI.lift D.inclusionHom (D.inclusionHomU.comp D.overlapHomU)
    D.inclusionHom_comp_overlapHom

@[simp]
private theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup_of {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool)
    (g : D.ChartGroup i) :
    D.pushoutToFundamentalGroup (Monoid.PushoutI.of i g) = D.inclusionHom i g :=
  Monoid.PushoutI.lift_of _ _ _ g

private theorem FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_of {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) :
    D.pushoutToFundamentalGroup.comp (Monoid.PushoutI.of i) = D.inclusionHom i := by
  ext g
  exact D.pushoutToFundamentalGroup_of i g

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_ofU {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.pushoutOfU = D.inclusionHomU :=
  D.pushoutToFundamentalGroup_comp_of Bool.false

private theorem
    FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_ofV {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.pushoutOfV = D.inclusionHomV :=
  D.pushoutToFundamentalGroup_comp_of Bool.true

private def FundamentalGroupVanKampen.TwoOpenCover.fundamentalGroupToPushout {X : Type*}
    [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    FundamentalGroup X D.base →* D.Pushout :=
  D.lift D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

private theorem FundamentalGroupVanKampen.TwoOpenCover.fundamentalGroupToPushout_comp_inclusionU
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.inclusionHomU = D.pushoutOfU :=
  D.lift_comp_inclusionU D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

private theorem FundamentalGroupVanKampen.TwoOpenCover.fundamentalGroupToPushout_comp_inclusionV
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.inclusionHomV = D.pushoutOfV :=
  D.lift_comp_inclusionV D.pushoutOfU D.pushoutOfV D.pushoutOf_compatible

private theorem
  FundamentalGroupVanKampen.TwoOpenCover.fundamentalGroupToPushout_comp_pushoutToFundamentalGroup
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup = MonoidHom.id D.Pushout := by
  apply Monoid.PushoutI.hom_ext_nonempty
  intro i
  cases i
  · change
      (D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup).comp D.pushoutOfU =
        (MonoidHom.id D.Pushout).comp D.pushoutOfU
    rw [MonoidHom.comp_assoc, D.pushoutToFundamentalGroup_comp_ofU,
      D.fundamentalGroupToPushout_comp_inclusionU, MonoidHom.id_comp]
  · change
      (D.fundamentalGroupToPushout.comp D.pushoutToFundamentalGroup).comp D.pushoutOfV =
        (MonoidHom.id D.Pushout).comp D.pushoutOfV
    rw [MonoidHom.comp_assoc, D.pushoutToFundamentalGroup_comp_ofV,
      D.fundamentalGroupToPushout_comp_inclusionV, MonoidHom.id_comp]

private theorem
  FundamentalGroupVanKampen.TwoOpenCover.pushoutToFundamentalGroup_comp_fundamentalGroupToPushout
    {X : Type*} [TopologicalSpace X] (D : FundamentalGroupVanKampen.TwoOpenCover X) :
    D.pushoutToFundamentalGroup.comp D.fundamentalGroupToPushout =
      MonoidHom.id (FundamentalGroup X D.base) := by
  apply D.hom_ext
  · rw [MonoidHom.comp_assoc, D.fundamentalGroupToPushout_comp_inclusionU,
      D.pushoutToFundamentalGroup_comp_ofU, MonoidHom.id_comp]
  · rw [MonoidHom.comp_assoc, D.fundamentalGroupToPushout_comp_inclusionV,
      D.pushoutToFundamentalGroup_comp_ofV, MonoidHom.id_comp]

private def FundamentalGroupVanKampen.TwoOpenCover.pushoutEquiv {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) : D.Pushout ≃* FundamentalGroup X D.base
    where
  toFun := D.pushoutToFundamentalGroup
  invFun := D.fundamentalGroupToPushout
  left_inv g := DFunLike.congr_fun D.fundamentalGroupToPushout_comp_pushoutToFundamentalGroup g
  right_inv g := DFunLike.congr_fun D.pushoutToFundamentalGroup_comp_fundamentalGroupToPushout g
  map_mul' := D.pushoutToFundamentalGroup.map_mul

@[simp]
private theorem
    FundamentalGroupVanKampen.TwoOpenCover.pushoutEquiv_of {X : Type*} [TopologicalSpace X]
    (D : FundamentalGroupVanKampen.TwoOpenCover X) (i : Bool) (g : D.ChartGroup i) :
    D.pushoutEquiv (Monoid.PushoutI.of i g) = D.inclusionHom i g :=
  D.pushoutToFundamentalGroup_of i g

private abbrev
    ThreefoldOverlapMappingTorus.PuncturedPiece (i : SpecialPeriods.Threefold.Puncture) :=
  { x : SpecialPeriods.Threefold.localPiece (Option.some i) //
    SpecialPeriods.Threefold.localProjectionToBase (Option.some i) x ∈
      SpecialPeriods.Threefold.regularPatch }

private theorem ThreefoldOverlapMappingTorus.inclusion_mem_regular_iff
    (i : SpecialPeriods.Threefold.Puncture)
    (x : SpecialPeriods.Threefold.localPiece (Option.some i)) :
    SpecialPeriods.Threefold.inclusion (Option.some i) x ∈
        SpecialPeriods.Threefold.liftedPatch Option.none ↔
      SpecialPeriods.Threefold.localProjectionToBase (Option.some i) x ∈
        SpecialPeriods.Threefold.regularPatch := by
  change
    SpecialPeriods.Threefold.projection (SpecialPeriods.Threefold.inclusion (Option.some i) x) ∈
        SpecialPeriods.Threefold.regularPatch ↔
      _
  rw [SpecialPeriods.Threefold.projection_inclusion]

private def
    ThreefoldOverlapMappingTorus.overlapPieceHomeomorph (i : SpecialPeriods.Threefold.Puncture) :
    SpecialPeriods.Threefold.RegularOverlap i ≃ₜ PuncturedPiece i
    where
  toFun
    x :=
    ⟨ThreefoldHomology.overlapToFilling i x,
      by
      apply (inclusion_mem_regular_iff i _).mp
      rw [ThreefoldHomology.inclusion_overlapToFilling]
      exact x.property.1⟩
  invFun
    x :=
    ⟨SpecialPeriods.Threefold.inclusion (Option.some i) x.val,
      (inclusion_mem_regular_iff i x.val).mpr x.property,
      (ThreefoldHomology.originalPatchHomeomorph (Option.some i) x.val).property⟩
  left_inv x := Subtype.ext (ThreefoldHomology.inclusion_overlapToFilling i x)
  right_inv
    x := by
    apply Subtype.ext
    apply (SpecialPeriods.Threefold.inclusion_openEmbedding (Option.some i)).injective
    exact ThreefoldHomology.inclusion_overlapToFilling i _
  continuous_toFun := (ThreefoldHomology.overlapToFilling i).continuous.subtype_mk _
  continuous_invFun :=
    ((SpecialPeriods.Threefold.inclusion_openEmbedding (Option.some i)).continuous.comp
          continuous_subtype_val).subtype_mk
      _

private def
    ThreefoldOverlapMappingTorus.puncturedPieceInclusion (i : SpecialPeriods.Threefold.Puncture) :
    C(PuncturedPiece i, SpecialPeriods.Threefold.localPiece (Option.some i)) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def
    ThreefoldOverlapMappingTorus.puncturedPieceToRegular (i : SpecialPeriods.Threefold.Puncture) :
    C(PuncturedPiece i, SpecialPeriods.Threefold.SpecialRegularFamily) :=
  (ThreefoldHomology.overlapToRegularFamily i).comp
    ((overlapPieceHomeomorph i).symm :
      C(PuncturedPiece i, SpecialPeriods.Threefold.RegularOverlap i))

private theorem ThreefoldOverlapMappingTorus.puncturedPieceToRegular_inclusion
    (i : SpecialPeriods.Threefold.Puncture) (x : PuncturedPiece i) :
    SpecialPeriods.Threefold.inclusion Option.none (puncturedPieceToRegular i x) =
      SpecialPeriods.Threefold.inclusion (Option.some i) x.val :=
  ThreefoldHomology.inclusion_overlapToRegularFamily i ((overlapPieceHomeomorph i).symm x)

private theorem ThreefoldOverlapMappingTorus.Elliptic.specialPiece_regular_iff (j : Elliptic.Kind)
    (x : SpecialPeriods.Threefold.SpecialEllipticPiece j) :
    SpecialPeriods.Threefold.localProjectionToBase (Option.some (Option.some j)) x ∈
        SpecialPeriods.Threefold.regularPatch ↔
      (SpecialPeriods.EllipticFilling.specialFullFillingProjection j x.val : ℂ) ≠ 0 :=
  SpecialPeriods.EllipticFilling.pieceProjectionToBase_mem_regular_iff
    SpecialPeriods.specialPeriodMap SpecialPeriods.specialPeriodMap_generator₁
    SpecialPeriods.specialPeriodMap_generator₂ SpecialPeriods.Threefold.specialBaseCover j x

private def ThreefoldOverlapMappingTorus.Elliptic.specialPuncturedHomeomorph (j : Elliptic.Kind) :
    ThreefoldOverlapMappingTorus.PuncturedPiece (Option.some j) ≃ₜ
      PuncturedFilling j j.twist (Elliptic.mainTwist_admissible j)
        (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
    where
  toFun
    x :=
    ⟨(SpecialPeriods.EllipticFilling.specialLocalData j).fillingHomeomorph j.twist
        (Elliptic.mainTwist_admissible j)
        ((x.val : SpecialPeriods.Threefold.SpecialEllipticPiece j).val),
      (specialPiece_regular_iff j x.val).mp x.property,
      (x.val : SpecialPeriods.Threefold.SpecialEllipticPiece j).property⟩
  invFun
    y :=
    ⟨(⟨((SpecialPeriods.EllipticFilling.specialLocalData j).fillingHomeomorph j.twist
                (Elliptic.mainTwist_admissible j)).symm
            y.val,
          y.property.2⟩ :
        SpecialPeriods.Threefold.SpecialEllipticPiece j),
      (specialPiece_regular_iff j _).mpr y.property.1⟩
  left_inv
    x := by
    apply Subtype.ext
    apply Subtype.ext
    exact
      ((SpecialPeriods.EllipticFilling.specialLocalData j).fillingHomeomorph j.twist
            (Elliptic.mainTwist_admissible j)).symm_apply_apply
        _
  right_inv
    y := by
    apply Subtype.ext
    exact
      ((SpecialPeriods.EllipticFilling.specialLocalData j).fillingHomeomorph j.twist
            (Elliptic.mainTwist_admissible j)).apply_symm_apply
        _
  continuous_toFun :=
    (((SpecialPeriods.EllipticFilling.specialLocalData j).fillingHomeomorph j.twist
              (Elliptic.mainTwist_admissible j)).continuous.comp
          (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk
      _
  continuous_invFun :=
    ((((SpecialPeriods.EllipticFilling.specialLocalData j).fillingHomeomorph j.twist
                  (Elliptic.mainTwist_admissible j)).symm.continuous.comp
              continuous_subtype_val).subtype_mk
          _).subtype_mk
      _

private def ThreefoldOverlapMappingTorus.Elliptic.specialRootRadius (j : Elliptic.Kind) :
    ThreefoldOverlapMappingTorus.Radius j.order
      (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) :=
  Classical.choice
    (ThreefoldOverlapMappingTorus.radius_nonempty j.order j.order_pos
      (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
      (SpecialPeriods.Threefold.specialBaseCover.radius_pos (Option.some j)))

private abbrev ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary (j : Elliptic.Kind) :=
  Boundary j j.twist

private def
    ThreefoldOverlapMappingTorus.Elliptic.specialMappingTorusHomotopyEquiv (j : Elliptic.Kind) :
    ThreefoldOverlapMappingTorus.PuncturedPiece (Option.some j) ≃ₕ SpecialBoundary j :=
  (specialPuncturedHomeomorph j).toHomotopyEquiv.trans
    (puncturedMappingTorusHomotopyEquiv j j.twist (Elliptic.mainTwist_admissible j)
      (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j)) (specialRootRadius j))

private def ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryInclusion (j : Elliptic.Kind) :
    C(SpecialBoundary j, ThreefoldOverlapMappingTorus.PuncturedPiece (Option.some j)) :=
  ⟨(specialMappingTorusHomotopyEquiv j).symm,
    (specialMappingTorusHomotopyEquiv j).symm.continuous⟩

private def ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToPiece (j : Elliptic.Kind) :
    C(SpecialBoundary j, SpecialPeriods.Threefold.SpecialEllipticPiece j) :=
  (ThreefoldOverlapMappingTorus.puncturedPieceInclusion (Option.some j)).comp
    (specialBoundaryInclusion j)

private theorem
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryInclusion_mk (j : Elliptic.Kind)
    (t : ℝ) (x : RealTorus₄) :
    ((specialBoundaryInclusion j
              (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x))).val :
          SpecialPeriods.Threefold.SpecialEllipticPiece j).val =
      (SpecialPeriods.EllipticFilling.specialLocalData j).quotient j.twist
        (Elliptic.mainTwist_admissible j)
        (ThreefoldOverlapMappingTorus.root j.order
            (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
            (specialRootRadius j) ((t / j.order : ℝ) : ThreefoldOverlapMappingTorus.Circle),
          x) := by
  change
    (((specialPuncturedHomeomorph j).symm
              (boundaryInclusion j j.twist (Elliptic.mainTwist_admissible j)
                (SpecialPeriods.Threefold.specialBaseCover.radius (Option.some j))
                (specialRootRadius j) (MappingTorus.mk _ (t, x)))).val :
          SpecialPeriods.Threefold.SpecialEllipticPiece j).val =
      _
  rw [boundaryInclusion_mk]
  rfl

private def ThreefoldOverlapMappingTorus.Cusp.specialData : SpecialPeriods.CuspFamily.Data :=
  SpecialPeriods.Threefold.CuspPiece.restrictedData SpecialPeriods.specialCuspData
    SpecialPeriods.Threefold.specialBaseCover SpecialPeriods.Threefold.specialCuspRadius_le

private abbrev ThreefoldOverlapMappingTorus.Cusp.SpecialPuncturedPiece :=
  {x : SpecialPeriods.Threefold.SpecialCuspPiece |
    SpecialPeriods.Threefold.specialCuspPieceProjectionToBase x ∈
      SpecialPeriods.Threefold.regularPatch}

private def ThreefoldOverlapMappingTorus.Cusp.specialPuncturedHomeomorph :
    SpecialPuncturedPiece ≃ₜ
      CuspUniformization.PuncturedQuotient specialData.correction specialData.radius
    where
  toFun
    x :=
    ⟨x.1,
      (SpecialPeriods.Threefold.CuspPiece.projectionToBase_mem_regular_iff
            SpecialPeriods.specialCuspData SpecialPeriods.Threefold.specialBaseCover x.1).mp
        x.property⟩
  invFun
    x :=
    ⟨x.1,
      (SpecialPeriods.Threefold.CuspPiece.projectionToBase_mem_regular_iff
            SpecialPeriods.specialCuspData SpecialPeriods.Threefold.specialBaseCover x.1).mpr
        x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

private def ThreefoldOverlapMappingTorus.Cusp.specialHeight : Height specialData.radius :=
  ⟨heightThreshold specialData.radius + 1,
    by
    change heightThreshold specialData.radius < heightThreshold specialData.radius + 1
    exact lt_add_one _⟩

private def ThreefoldOverlapMappingTorus.Cusp.specialMappingTorusHomotopyEquivAt
    (h : Height specialData.radius) : SpecialPuncturedPiece ≃ₕ Boundary :=
  specialPuncturedHomeomorph.toHomotopyEquiv.trans
    (puncturedMappingTorusHomotopyEquiv specialData h)

private def ThreefoldOverlapMappingTorus.Cusp.specialMappingTorusHomotopyEquiv :
    SpecialPuncturedPiece ≃ₕ Boundary :=
  specialMappingTorusHomotopyEquivAt specialHeight

private def ThreefoldOverlapMappingTorus.Cusp.specialBoundaryInclusion :
    C(Boundary, SpecialPuncturedPiece) :=
  specialMappingTorusHomotopyEquiv.invFun

private def ThreefoldOverlapMappingTorus.Cusp.specialBoundaryToPiece :
    C(Boundary, SpecialPeriods.Threefold.SpecialCuspPiece) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
        C(SpecialPuncturedPiece, SpecialPeriods.Threefold.SpecialCuspPiece)).comp
    specialBoundaryInclusion

private def ThreefoldOverlapMappingTorus.Cusp.specialFibreToPiece :
    C(RealTorus₄, SpecialPeriods.Threefold.SpecialCuspPiece) :=
  specialBoundaryToPiece.comp (MappingTorus.HomologyCover.fibreInclusion monodromy)

private def ThreefoldOverlapMappingTorus.monodromy :
    SpecialPeriods.Threefold.Puncture → (RealTorus₄ ≃ₜ RealTorus₄)
  | none => Cusp.monodromy
  | some j => Elliptic.flatTorusAffine j j.twist

private abbrev ThreefoldOverlapMappingTorus.Boundary (i : SpecialPeriods.Threefold.Puncture) :=
  MappingTorus.Torus (monodromy i)

private def ThreefoldOverlapMappingTorus.pieceMappingTorusHomotopyEquiv
    (i : SpecialPeriods.Threefold.Puncture) : PuncturedPiece i ≃ₕ Boundary i := by
  cases i with
  | none => exact Cusp.specialMappingTorusHomotopyEquiv
  | some j => exact Elliptic.specialMappingTorusHomotopyEquiv j

private def ThreefoldOverlapMappingTorus.overlapMappingTorusHomotopyEquiv
    (i : SpecialPeriods.Threefold.Puncture) :
    SpecialPeriods.Threefold.RegularOverlap i ≃ₕ Boundary i :=
  (overlapPieceHomeomorph i).toHomotopyEquiv.trans (pieceMappingTorusHomotopyEquiv i)

private def ThreefoldOverlapMappingTorus.boundaryToOverlap (i : SpecialPeriods.Threefold.Puncture) :
    C(Boundary i, SpecialPeriods.Threefold.RegularOverlap i) :=
  ⟨(overlapMappingTorusHomotopyEquiv i).symm,
    (overlapMappingTorusHomotopyEquiv i).symm.continuous⟩

private def
    ThreefoldOverlapMappingTorus.boundaryToRegularFamily (i : SpecialPeriods.Threefold.Puncture) :
    C(Boundary i, SpecialPeriods.Threefold.SpecialRegularFamily) :=
  (ThreefoldHomology.overlapToRegularFamily i).comp (boundaryToOverlap i)

private def ThreefoldOverlapMappingTorus.boundaryToFilling (i : SpecialPeriods.Threefold.Puncture) :
    C(Boundary i, SpecialPeriods.Threefold.localPiece (Option.some i)) :=
  (ThreefoldHomology.overlapToFilling i).comp (boundaryToOverlap i)

private theorem ThreefoldOverlapMappingTorus.boundaryToRegularFamily_ambient
    (i : SpecialPeriods.Threefold.Puncture) (x : Boundary i) :
    SpecialPeriods.Threefold.inclusion Option.none (boundaryToRegularFamily i x) =
      (boundaryToOverlap i x).val :=
  ThreefoldHomology.inclusion_overlapToRegularFamily i (boundaryToOverlap i x)

private theorem ThreefoldOverlapMappingTorus.boundaryToFilling_ambient
    (i : SpecialPeriods.Threefold.Puncture) (x : Boundary i) :
    SpecialPeriods.Threefold.inclusion (Option.some i) (boundaryToFilling i x) =
      (boundaryToOverlap i x).val :=
  ThreefoldHomology.inclusion_overlapToFilling i (boundaryToOverlap i x)

private theorem
    ThreefoldOverlapMappingTorus.boundary_maps_agree (i : SpecialPeriods.Threefold.Puncture) :
    ThreefoldHomology.originalRegularInclusion.comp (boundaryToRegularFamily i) =
      (ThreefoldHomology.originalPieceInclusion (Option.some i)).comp (boundaryToFilling i) := by
  apply ContinuousMap.ext
  intro x
  exact (boundaryToRegularFamily_ambient i x).trans (boundaryToFilling_ambient i x).symm

@[simp]
private theorem
    ThreefoldOverlapMappingTorus.boundaryToOverlap_cusp_piece (x : Boundary Option.none) :
    overlapPieceHomeomorph Option.none (boundaryToOverlap Option.none x) =
      Cusp.specialBoundaryInclusion x :=
  (overlapPieceHomeomorph Option.none).apply_symm_apply _

@[simp]
private theorem ThreefoldOverlapMappingTorus.boundaryToOverlap_elliptic_piece (j : Elliptic.Kind)
    (x : Boundary (Option.some j)) :
    overlapPieceHomeomorph (Option.some j) (boundaryToOverlap (Option.some j) x) =
      Elliptic.specialBoundaryInclusion j x :=
  (overlapPieceHomeomorph (Option.some j)).apply_symm_apply _

private theorem ThreefoldOverlapMappingTorus.boundaryToFilling_cusp :
    boundaryToFilling Option.none = Cusp.specialBoundaryToPiece := by
  apply ContinuousMap.ext
  intro x
  exact congrArg Subtype.val (boundaryToOverlap_cusp_piece x)

private theorem ThreefoldOverlapMappingTorus.boundaryToFilling_elliptic (j : Elliptic.Kind) :
    boundaryToFilling (Option.some j) = Elliptic.specialBoundaryToPiece j := by
  apply ContinuousMap.ext
  intro x
  exact congrArg Subtype.val (boundaryToOverlap_elliptic_piece j x)

private def ThreefoldOverlapMappingTorus.overlapRetraction (i : SpecialPeriods.Threefold.Puncture) :
    C(SpecialPeriods.Threefold.RegularOverlap i, Boundary i) :=
  ⟨overlapMappingTorusHomotopyEquiv i, (overlapMappingTorusHomotopyEquiv i).continuous⟩

private theorem ThreefoldOverlapMappingTorus.boundary_overlap_retraction_homotopic
    (i : SpecialPeriods.Threefold.Puncture) :
    ((boundaryToOverlap i).comp (overlapRetraction i)).Homotopic (ContinuousMap.id _) :=
  (overlapMappingTorusHomotopyEquiv i).left_inv

private theorem ThreefoldOverlapMappingTorus.boundary_regular_retraction_homotopic
    (i : SpecialPeriods.Threefold.Puncture) :
    ((boundaryToRegularFamily i).comp (overlapRetraction i)).Homotopic
      (ThreefoldHomology.overlapToRegularFamily i) := by
  simpa only [boundaryToRegularFamily, ContinuousMap.comp_assoc, ContinuousMap.comp_id] using
    (ContinuousMap.Homotopic.refl (ThreefoldHomology.overlapToRegularFamily i)).comp
      (boundary_overlap_retraction_homotopic i)

private theorem ThreefoldOverlapMappingTorus.boundary_filling_retraction_homotopic
    (i : SpecialPeriods.Threefold.Puncture) :
    ((boundaryToFilling i).comp (overlapRetraction i)).Homotopic
      (ThreefoldHomology.overlapToFilling i) := by
  simpa only [boundaryToFilling, ContinuousMap.comp_assoc, ContinuousMap.comp_id] using
    (ContinuousMap.Homotopic.refl (ThreefoldHomology.overlapToFilling i)).comp
      (boundary_overlap_retraction_homotopic i)

private def
    ThreefoldOverlapMappingTorus.fibreToRegularFamily (i : SpecialPeriods.Threefold.Puncture) :
    C(RealTorus₄, SpecialPeriods.Threefold.SpecialRegularFamily) :=
  (boundaryToRegularFamily i).comp (MappingTorus.HomologyCover.fibreInclusion (monodromy i))

private def ThreefoldOverlapMappingTorus.fibreToFilling (i : SpecialPeriods.Threefold.Puncture) :
    C(RealTorus₄, SpecialPeriods.Threefold.localPiece (Option.some i)) :=
  (boundaryToFilling i).comp (MappingTorus.HomologyCover.fibreInclusion (monodromy i))

private def
    ThreefoldOverlapMappingTorus.overlapHomologyEquiv (i : SpecialPeriods.Threefold.Puncture)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.RegularOverlap i) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (Boundary i) n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapMappingTorusHomotopyEquiv i) n

@[simp]
private theorem ThreefoldOverlapMappingTorus.overlapHomologyEquiv_toLinearMap
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    (overlapHomologyEquiv i n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap (overlapRetraction i) n :=
  rfl

private def ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (Boundary i) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology SpecialPeriods.Threefold.SpecialRegularFamily n :=
  SingularMayerVietoris.singularHomologyMap (boundaryToRegularFamily i) n

private def ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (Boundary i) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (SpecialPeriods.Threefold.localPiece (Option.some i))
        n :=
  SingularMayerVietoris.singularHomologyMap (boundaryToFilling i) n

private theorem ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_eq
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    boundaryFillingHomologyMap i n =
      (SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.overlapToFilling i) n).comp
        (overlapHomologyEquiv i n).symm.toLinearMap :=
  PeriodTorusHigherHomology.singularHomologyMap_comp (boundaryToOverlap i)
    (ThreefoldHomology.overlapToFilling i) n

private theorem ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap_retraction
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    (boundaryRegularHomologyMap i n).comp (overlapHomologyEquiv i n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.overlapToRegularFamily i) n := by
  rw [overlapHomologyEquiv_toLinearMap]
  change
    (SingularMayerVietoris.singularHomologyMap (boundaryToRegularFamily i) n).comp
        (SingularMayerVietoris.singularHomologyMap (overlapRetraction i) n) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact
    PeriodTorusHigherHomology.homotopic_homologyMap (boundary_regular_retraction_homotopic i) n

private theorem ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_retraction
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    (boundaryFillingHomologyMap i n).comp (overlapHomologyEquiv i n).toLinearMap =
      SingularMayerVietoris.singularHomologyMap (ThreefoldHomology.overlapToFilling i) n := by
  rw [overlapHomologyEquiv_toLinearMap]
  change
    (SingularMayerVietoris.singularHomologyMap (boundaryToFilling i) n).comp
        (SingularMayerVietoris.singularHomologyMap (overlapRetraction i) n) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact
    PeriodTorusHigherHomology.homotopic_homologyMap (boundary_filling_retraction_homotopic i) n

private theorem ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap_fibre
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    (boundaryRegularHomologyMap i n).comp
        (SingularMayerVietoris.singularHomologyMap
          (MappingTorus.HomologyCover.fibreInclusion (monodromy i)) n) =
      SingularMayerVietoris.singularHomologyMap (fibreToRegularFamily i) n :=
  (PeriodTorusHigherHomology.singularHomologyMap_comp
      (MappingTorus.HomologyCover.fibreInclusion (monodromy i)) (boundaryToRegularFamily i)
      n).symm

private theorem ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap_fibre
    (i : SpecialPeriods.Threefold.Puncture) (n : ℕ) :
    (boundaryFillingHomologyMap i n).comp
        (SingularMayerVietoris.singularHomologyMap
          (MappingTorus.HomologyCover.fibreInclusion (monodromy i)) n) =
      SingularMayerVietoris.singularHomologyMap (fibreToFilling i) n :=
  (PeriodTorusHigherHomology.singularHomologyMap_comp
      (MappingTorus.HomologyCover.fibreInclusion (monodromy i)) (boundaryToFilling i) n).symm

private def MappingTorusHomology.Algebra.difference {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : M →ₗ[ℤ] M) : M →ₗ[ℤ] M :=
  LinearMap.id - F

private def MappingTorusHomology.Algebra.twoArcMap {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : M →ₗ[ℤ] M) : (M × M) →ₗ[ℤ] (M × M) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun p := (p.1 + p.2, -(p.1 + F p.2))
      map_zero' := by simp
      map_add' p
        q := by
        apply Prod.ext
        · exact add_add_add_comm p.1 q.1 p.2 q.2
        · change -((p.1 + q.1) + F (p.2 + q.2)) = -(p.1 + F p.2) + -(q.1 + F q.2)
          rw [map_add]
          abel }

@[simp]
private theorem
    MappingTorusHomology.Algebra.twoArcMap_apply {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : M →ₗ[ℤ] M) (p : M × M) : twoArcMap F p = (p.1 + p.2, -(p.1 + F p.2)) :=
  rfl

private theorem
    MappingTorusHomology.Algebra.pairSum_twoArcMap {M : Type*} [AddCommGroup M] [Module ℤ M]
    (F : M →ₗ[ℤ] M) (p : M × M) :
    PeriodTorusHigherHomology.pairSumMap M (twoArcMap F p) = difference F p.2 := by
  change (p.1 + p.2) + -(p.1 + F p.2) = p.2 - F p.2
  abel

private theorem MappingTorusHomology.Algebra.twoArcMap_kernel_iff {M : Type*} [AddCommGroup M]
    [Module ℤ M] (F : M →ₗ[ℤ] M) (p : M × M) :
    twoArcMap F p = 0 ↔ p.1 = -p.2 ∧ difference F p.2 = 0 := by
  constructor
  · intro hp
    have hsum : p.1 + p.2 = 0 := congrArg Prod.fst hp
    refine ⟨eq_neg_of_add_eq_zero_left hsum, ?_⟩
    rw [← pairSum_twoArcMap F p, hp, map_zero]
  · rintro ⟨hfst, hfix⟩
    have hF : F p.2 = p.2 := (sub_eq_zero.mp hfix).symm
    rw [twoArcMap_apply, hfst, hF, neg_add_cancel, neg_zero]
    rfl

private theorem MappingTorusHomology.Algebra.range_difference_eq_ker {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ :
      LinearMap.range (twoArcMap F) =
        LinearMap.ker (i.comp (PeriodTorusHigherHomology.pairSumMap M))) :
    LinearMap.range (difference F) = LinearMap.ker i := by
  ext x
  constructor
  · rintro ⟨b, rfl⟩
    have hb : twoArcMap F (0, b) ∈ LinearMap.range (twoArcMap F) := ⟨(0, b), rfl⟩
    rw [hJ] at hb
    change i (PeriodTorusHigherHomology.pairSumMap M (twoArcMap F (0, b))) = 0 at hb
    rw [pairSum_twoArcMap] at hb
    exact hb
  · intro hx
    have hix : i x = 0 := LinearMap.mem_ker.mp hx
    have hp : (x, 0) ∈ LinearMap.ker (i.comp (PeriodTorusHigherHomology.pairSumMap M)) := by
      change i (x + 0) = 0
      simpa only [add_zero] using hix
    rw [← hJ] at hp
    obtain ⟨p, hp⟩ := hp
    refine ⟨p.2, ?_⟩
    calc
      difference F p.2 = PeriodTorusHigherHomology.pairSumMap M (twoArcMap F p) :=
        (pairSum_twoArcMap F p).symm
      _ = x := by rw [hp, PeriodTorusHigherHomology.pairSumMap_apply, add_zero]

private def MappingTorusHomology.Algebra.boundary {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (d : N →ₗ[ℤ] (P × P)) : N →ₗ[ℤ] P :=
  (PeriodTorusHigherHomology.negativeFirstMap P).comp d

@[simp]
private theorem
    MappingTorusHomology.Algebra.boundary_apply {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (d : N →ₗ[ℤ] (P × P)) (n : N) : boundary d n = -(d n).1 :=
  rfl

private theorem MappingTorusHomology.Algebra.connecting_mem_kernel {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    d n ∈ LinearMap.ker (twoArcMap F) := by
  rw [← hd]
  exact ⟨n, rfl⟩

private theorem
    MappingTorusHomology.Algebra.boundary_eq_snd {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) : boundary d n = (d n).2 := by
  have hp := (twoArcMap_kernel_iff F (d n)).mp (connecting_mem_kernel F d hd n)
  rw [boundary_apply, hp.1, neg_neg]

private theorem
    MappingTorusHomology.Algebra.connecting_eq_antidiagonal {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    d n = (-boundary d n, boundary d n) := by
  apply Prod.ext
  · simp only [boundary_apply, neg_neg]
  · exact (boundary_eq_snd F d hd n).symm

private theorem MappingTorusHomology.Algebra.boundary_mem_kernel {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    boundary d n ∈ LinearMap.ker (difference F) := by
  rw [boundary_eq_snd F d hd n]
  exact ((twoArcMap_kernel_iff F (d n)).mp (connecting_mem_kernel F d hd n)).2

private theorem
    MappingTorusHomology.Algebra.boundary_range {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.range (boundary d) = LinearMap.ker (difference F) := by
  ext b
  constructor
  · rintro ⟨n, rfl⟩
    exact boundary_mem_kernel F d hd n
  · intro hb
    have hp : (-b, b) ∈ LinearMap.ker (twoArcMap F) :=
      (twoArcMap_kernel_iff F (-b, b)).mpr ⟨rfl, hb⟩
    rw [← hd] at hp
    obtain ⟨n, hn⟩ := hp
    refine ⟨n, ?_⟩
    rw [boundary_apply, hn]
    exact neg_neg b

private theorem
    MappingTorusHomology.Algebra.boundary_ker {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.ker (boundary d) = LinearMap.ker d := by
  ext n
  change boundary d n = 0 ↔ d n = 0
  constructor
  · intro hn
    rw [connecting_eq_antidiagonal F d hd n, hn, neg_zero]
    rfl
  · intro hn
    rw [boundary_apply, hn]
    exact neg_zero

private theorem MappingTorusHomology.Algebra.range_inclusion_eq_ker_boundary {M N P : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N] [AddCommGroup P] [Module ℤ P]
    (F : P →ₗ[ℤ] P) (i : M →ₗ[ℤ] N) (d : N →ₗ[ℤ] (P × P))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.range i = LinearMap.ker (boundary d) :=
  hi.trans (boundary_ker F d hd).symm

private abbrev
    MappingTorusHomology.monodromyHomologyMap {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n :=
  SingularMayerVietoris.singularHomologyMap (f : C(X, X)) n

private abbrev MappingTorusHomology.fibreHomologyMap {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) n :=
  SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.fibreInclusion f) n

private def
    MappingTorusHomology.arcHomologyEquiv {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology (MappingTorus.HomologyCover.U f) n ×
        SingularMayerVietoris.SingularHomology (MappingTorus.HomologyCover.V f) n) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (MappingTorus.HomologyCover.homotopyEquivU f) n).toAddEquiv.prodCongr
      (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (MappingTorus.HomologyCover.homotopyEquivV f) n).toAddEquiv).toIntLinearEquiv

private def
    MappingTorusHomology.intersectionHomologyEquiv {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (MappingTorus.HomologyCover.intersectionHomotopyEquiv f) n).trans
    (PeriodTorusHigherHomology.sumHomologyEquiv X X n)

@[simp]
private theorem MappingTorusHomology.intersectionHomologyEquiv_apply {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n) :
    intersectionHomologyEquiv f n a =
      PeriodTorusHigherHomology.sumHomologyEquiv X X n
        (SingularMayerVietoris.singularHomologyMap
          (MappingTorus.HomologyCover.intersectionHomotopyEquiv f).toFun n a) :=
  rfl

private theorem
    MappingTorusHomology.inclusionU_homology {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.inclusionU f) n =
      (fibreHomologyMap f n).comp
        (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
            (MappingTorus.HomologyCover.homotopyEquivU f) n).toLinearMap := by
  rw [PeriodTorusHigherHomology.homotopy_homologyMap
      (MappingTorus.HomologyCover.inclusionUHomotopy f) n,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private theorem
    MappingTorusHomology.inclusionV_homology {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.inclusionV f) n =
      (fibreHomologyMap f n).comp
        (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
            (MappingTorus.HomologyCover.homotopyEquivV f) n).toLinearMap := by
  rw [PeriodTorusHigherHomology.homotopy_homologyMap
      (MappingTorus.HomologyCover.inclusionVHomotopy f) n,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private theorem
    MappingTorusHomology.intersectionToU_homology {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n) :
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (MappingTorus.HomologyCover.homotopyEquivU f) n
        (SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.intersectionToU f)
          n a) =
      (intersectionHomologyEquiv f n a).1 + (intersectionHomologyEquiv f n a).2 := by
  change
    SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.homotopyEquivU f).toFun
        n
        (SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.intersectionToU f)
          n a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    MappingTorus.HomologyCover.intersectionToU_fold,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  simp only [LinearMap.comp_apply, intersectionHomologyEquiv_apply]
  exact
    PeriodTorusHigherHomology.sumHomologyEquiv_fold (X := X) n
      (SingularMayerVietoris.singularHomologyMap
        (MappingTorus.HomologyCover.intersectionHomotopyEquiv f).toFun n a)

private theorem
    MappingTorusHomology.intersectionToV_homology {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n) :
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (MappingTorus.HomologyCover.homotopyEquivV f) n
        (SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.intersectionToV f)
          n a) =
      (intersectionHomologyEquiv f n a).1 +
        monodromyHomologyMap f n (intersectionHomologyEquiv f n a).2 := by
  change
    SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.homotopyEquivV f).toFun
        n
        (SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.intersectionToV f)
          n a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    MappingTorus.HomologyCover.intersectionToV_twistedFold,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  simp only [LinearMap.comp_apply, intersectionHomologyEquiv_apply]
  have h :=
    PeriodTorusHigherHomology.sumHomologyEquiv_sumElim (ContinuousMap.id X) (f : C(X, X)) n
      (SingularMayerVietoris.singularHomologyMap
        (MappingTorus.HomologyCover.intersectionHomotopyEquiv f).toFun n a)
  simpa only [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] using h

private theorem MappingTorusHomology.leftHomologyMap_coordinates {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n) :
    arcHomologyEquiv f n
        (SingularMayerVietoris.leftHomologyMap (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) n a) =
      Algebra.twoArcMap (monodromyHomologyMap f n) (intersectionHomologyEquiv f n a) := by
  rw [SingularMayerVietoris.leftHomologyMap_apply]
  change
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (MappingTorus.HomologyCover.homotopyEquivU f) n
          (SingularMayerVietoris.singularHomologyMap
            (MappingTorus.HomologyCover.intersectionToU f) n a),
        PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (MappingTorus.HomologyCover.homotopyEquivV f) n
          (-SingularMayerVietoris.singularHomologyMap
              (MappingTorus.HomologyCover.intersectionToV f) n a)) =
      _
  rw [map_neg, intersectionToU_homology, intersectionToV_homology]
  rfl

private theorem MappingTorusHomology.rightHomologyMap_coordinates {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (MappingTorus.HomologyCover.U f) n ×
        SingularMayerVietoris.SingularHomology (MappingTorus.HomologyCover.V f) n) :
    SingularMayerVietoris.rightHomologyMap (MappingTorus.HomologyCover.U f)
        (MappingTorus.HomologyCover.V f) n a =
      fibreHomologyMap f n ((arcHomologyEquiv f n a).1 + (arcHomologyEquiv f n a).2) := by
  rw [SingularMayerVietoris.rightHomologyMap_apply]
  change
    SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.inclusionU f) n a.1 +
        SingularMayerVietoris.singularHomologyMap (MappingTorus.HomologyCover.inclusionV f) n
          a.2 =
      _
  rw [inclusionU_homology, inclusionV_homology]
  exact (map_add (fibreHomologyMap f n) _ _).symm

private def
    MappingTorusHomology.Algebra.cokernelInclusion {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ :
      LinearMap.range (twoArcMap F) =
        LinearMap.ker (i.comp (PeriodTorusHigherHomology.pairSumMap M))) :
    (M ⧸ LinearMap.range (difference F)) →ₗ[ℤ] N :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    ((LinearMap.range (difference F)).liftQ i (range_difference_eq_ker F i hJ).le).toAddMonoidHom

private theorem
    MappingTorusHomology.Algebra.cokernelInclusion_injective {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ :
      LinearMap.range (twoArcMap F) =
        LinearMap.ker (i.comp (PeriodTorusHigherHomology.pairSumMap M))) :
    Function.Injective (cokernelInclusion F i hJ) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := (LinearMap.range (difference F)).mkQ_surjective x
  obtain ⟨b, rfl⟩ := (LinearMap.range (difference F)).mkQ_surjective y
  change i a = i b at hxy
  apply (Submodule.Quotient.eq (LinearMap.range (difference F))).mpr
  rw [range_difference_eq_ker F i hJ]
  change i (a - b) = 0
  rw [map_sub, hxy, sub_self]

private theorem MappingTorusHomology.Algebra.cokernelInclusion_range {M N : Type*} [AddCommGroup M]
    [Module ℤ M] [AddCommGroup N] [Module ℤ N] (F : M →ₗ[ℤ] M) (i : M →ₗ[ℤ] N)
    (hJ :
      LinearMap.range (twoArcMap F) =
        LinearMap.ker (i.comp (PeriodTorusHigherHomology.pairSumMap M))) :
    LinearMap.range (cokernelInclusion F i hJ) = LinearMap.range i := by
  ext n
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨a, rfl⟩ := (LinearMap.range (difference F)).mkQ_surjective x
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨Submodule.Quotient.mk a, rfl⟩

private def MappingTorusHomology.Algebra.kernelBoundary {N P : Type*} [AddCommGroup N] [Module ℤ N]
    [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    N →ₗ[ℤ] LinearMap.ker (difference F) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun n := ⟨boundary d n, boundary_mem_kernel F d hd n⟩
      map_zero' := by
        apply Subtype.ext
        exact map_zero (boundary d)
      map_add' n
        m := by
        apply Subtype.ext
        exact map_add (boundary d) n m }

private theorem
    MappingTorusHomology.Algebra.kernelBoundary_eq_zero_iff {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) (n : N) :
    kernelBoundary F d hd n = 0 ↔ boundary d n = 0 := by
  constructor
  · intro hn
    exact congrArg Subtype.val hn
  · intro hn
    exact Subtype.ext hn

private theorem MappingTorusHomology.Algebra.kernelBoundary_ker {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    LinearMap.ker (kernelBoundary F d hd) = LinearMap.ker (boundary d) := by
  ext n
  exact kernelBoundary_eq_zero_iff F d hd n

private theorem
    MappingTorusHomology.Algebra.kernelBoundary_surjective {N P : Type*} [AddCommGroup N]
    [Module ℤ N] [AddCommGroup P] [Module ℤ P] (F : P →ₗ[ℤ] P) (d : N →ₗ[ℤ] (P × P))
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F)) :
    Function.Surjective (kernelBoundary F d hd) := by
  intro b
  have hb : (b : P) ∈ LinearMap.range (boundary d) := by
    rw [boundary_range F d hd]
    exact b.property
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, Subtype.ext hn⟩

private theorem
    MappingTorusHomology.Algebra.cokernelInclusion_range_eq_ker_kernelBoundary {M N P : Type*}
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N] [AddCommGroup P] [Module ℤ P]
    (F : M →ₗ[ℤ] M) (F' : P →ₗ[ℤ] P) (i : M →ₗ[ℤ] N) (d : N →ₗ[ℤ] (P × P))
    (hJ :
      LinearMap.range (twoArcMap F) =
        LinearMap.ker (i.comp (PeriodTorusHigherHomology.pairSumMap M)))
    (hi : LinearMap.range i = LinearMap.ker d)
    (hd : LinearMap.range d = LinearMap.ker (twoArcMap F')) :
    LinearMap.range (cokernelInclusion F i hJ) = LinearMap.ker (kernelBoundary F' d hd) := by
  rw [cokernelInclusion_range, kernelBoundary_ker, boundary_ker F' d hd]
  exact hi

private def
    MappingTorusHomology.wangDifference {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ] SingularMayerVietoris.SingularHomology X n :=
  Algebra.difference (monodromyHomologyMap f n)

@[simp]
private theorem
    MappingTorusHomology.wangDifference_apply {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    wangDifference f n a = a - SingularMayerVietoris.singularHomologyMap (f : C(X, X)) n a :=
  rfl

private theorem
    MappingTorusHomology.twoArc_exact_at_pair {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    LinearMap.range (Algebra.twoArcMap (monodromyHomologyMap f n)) =
      LinearMap.ker
        ((fibreHomologyMap f n).comp
          (PeriodTorusHigherHomology.pairSumMap (SingularMayerVietoris.SingularHomology X n))) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have h :=
      LinearMap.congr_fun
        (SingularMayerVietoris.leftHomologyMap_comp_right (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) n)
        ((intersectionHomologyEquiv f n).symm b)
    change
      SingularMayerVietoris.rightHomologyMap (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) n
          (SingularMayerVietoris.leftHomologyMap (MappingTorus.HomologyCover.U f)
            (MappingTorus.HomologyCover.V f) n ((intersectionHomologyEquiv f n).symm b)) =
        0 at h
    rw [rightHomologyMap_coordinates, leftHomologyMap_coordinates,
      LinearEquiv.apply_symm_apply] at h
    exact h
  · intro ha
    have hright :
      (arcHomologyEquiv f n).symm a ∈
        LinearMap.ker
          (SingularMayerVietoris.rightHomologyMap (MappingTorus.HomologyCover.U f)
            (MappingTorus.HomologyCover.V f) n) := by
      change
        SingularMayerVietoris.rightHomologyMap (MappingTorus.HomologyCover.U f)
            (MappingTorus.HomologyCover.V f) n ((arcHomologyEquiv f n).symm a) =
          0
      rw [rightHomologyMap_coordinates, LinearEquiv.apply_symm_apply]
      exact ha
    rw [←
      SingularMayerVietoris.exact_at_pair (MappingTorus.HomologyCover.U f)
        (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
        (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f) n] at hright
    obtain ⟨b, hb⟩ := hright
    refine ⟨intersectionHomologyEquiv f n b, ?_⟩
    rw [← leftHomologyMap_coordinates, hb, LinearEquiv.apply_symm_apply]

private abbrev
    MappingTorusHomology.mayerVietorisConnecting {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
          Set (MappingTorus.Torus f))
        n :=
  SingularMayerVietoris.connectingHomomorphism (MappingTorus.HomologyCover.U f)
    (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
    (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f) n

private def MappingTorusHomology.boundaryCoordinates {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :=
  (intersectionHomologyEquiv f n).toLinearMap.comp (mayerVietorisConnecting f n)

@[simp]
private theorem MappingTorusHomology.boundaryCoordinates_apply {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    boundaryCoordinates f n a = intersectionHomologyEquiv f n (mayerVietorisConnecting f n a) :=
  rfl

private theorem MappingTorusHomology.boundaryCoordinates_range {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ) :
    LinearMap.range (boundaryCoordinates f n) =
      LinearMap.ker (Algebra.twoArcMap (monodromyHomologyMap f n)) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    have hb : mayerVietorisConnecting f n b ∈ LinearMap.range (mayerVietorisConnecting f n) :=
      ⟨b, rfl⟩
    rw [SingularMayerVietoris.exact_at_intersection (MappingTorus.HomologyCover.U f)
        (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
        (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f)] at hb
    have h := congrArg (arcHomologyEquiv f n) hb
    rw [leftHomologyMap_coordinates, map_zero] at h
    exact h
  · intro ha
    have hl :
      SingularMayerVietoris.leftHomologyMap (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) n ((intersectionHomologyEquiv f n).symm a) =
        0 := by
      apply (arcHomologyEquiv f n).injective
      rw [leftHomologyMap_coordinates, LinearEquiv.apply_symm_apply, map_zero]
      exact ha
    have hr :
      (intersectionHomologyEquiv f n).symm a ∈ LinearMap.range (mayerVietorisConnecting f n) := by
      rw [SingularMayerVietoris.exact_at_intersection (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
          (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f)]
      exact hl
    obtain ⟨b, hb⟩ := hr
    refine ⟨b, ?_⟩
    rw [boundaryCoordinates_apply, hb, LinearEquiv.apply_symm_apply]

private theorem
    MappingTorusHomology.rightHomologyMap_range {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    LinearMap.range
        (SingularMayerVietoris.rightHomologyMap (MappingTorus.HomologyCover.U f)
          (MappingTorus.HomologyCover.V f) n) =
      LinearMap.range (fibreHomologyMap f n) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact
      ⟨(arcHomologyEquiv f n a).1 + (arcHomologyEquiv f n a).2,
        (rightHomologyMap_coordinates f n a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(arcHomologyEquiv f n).symm (a, 0), ?_⟩
    rw [rightHomologyMap_coordinates, LinearEquiv.apply_symm_apply]
    exact congrArg (fibreHomologyMap f n) (add_zero a)

private theorem
    MappingTorusHomology.boundaryCoordinates_ker {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) :
    LinearMap.range (fibreHomologyMap f (n + 1)) = LinearMap.ker (boundaryCoordinates f n) := by
  rw [boundaryCoordinates, SingularMayerVietoris.rightTransport_second_ker]
  rw [←
    SingularMayerVietoris.exact_at_ambient (MappingTorus.HomologyCover.U f)
      (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
      (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f)]
  exact (rightHomologyMap_range f (n + 1)).symm

private def MappingTorusHomology.wangBoundary {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X n :=
  Algebra.boundary (boundaryCoordinates f n)

@[simp]
private theorem MappingTorusHomology.wangBoundary_apply {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    wangBoundary f n a = -(boundaryCoordinates f n a).1 :=
  rfl

private theorem
    MappingTorusHomology.boundaryCoordinates_eq_antidiagonal {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    boundaryCoordinates f n a = (-wangBoundary f n a, wangBoundary f n a) :=
  Algebra.connecting_eq_antidiagonal _ _ (boundaryCoordinates_range f n) a

private theorem
    MappingTorusHomology.wang_exact_at_fibre {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) : LinearMap.range (wangDifference f n) = LinearMap.ker (fibreHomologyMap f n) :=
  Algebra.range_difference_eq_ker _ _ (twoArc_exact_at_pair f n)

private theorem MappingTorusHomology.wang_exact_at_mappingTorus {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ) :
    LinearMap.range (fibreHomologyMap f (n + 1)) = LinearMap.ker (wangBoundary f n) :=
  Algebra.range_inclusion_eq_ker_boundary _ _ _ (boundaryCoordinates_ker f n)
    (boundaryCoordinates_range f n)

private theorem MappingTorusHomology.wangBoundary_range {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) : LinearMap.range (wangBoundary f n) = LinearMap.ker (wangDifference f n) :=
  Algebra.boundary_range _ _ (boundaryCoordinates_range f n)

private def
    MappingTorusHomology.cokernelInclusion {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology X n ⧸ LinearMap.range (wangDifference f n)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) n :=
  Algebra.cokernelInclusion _ _ (twoArc_exact_at_pair f n)

@[simp]
private theorem
    MappingTorusHomology.cokernelInclusion_mk {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    cokernelInclusion f n (Submodule.Quotient.mk a) = fibreHomologyMap f n a :=
  rfl

private theorem MappingTorusHomology.cokernelInclusion_injective {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ) : Function.Injective (cokernelInclusion f n) :=
  Algebra.cokernelInclusion_injective _ _ (twoArc_exact_at_pair f n)

private def
    MappingTorusHomology.kernelBoundary {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1) →ₗ[ℤ]
      LinearMap.ker (wangDifference f n) :=
  Algebra.kernelBoundary _ _ (boundaryCoordinates_range f n)

private theorem MappingTorusHomology.kernelBoundary_surjective {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (n : ℕ) : Function.Surjective (kernelBoundary f n) :=
  Algebra.kernelBoundary_surjective _ _ (boundaryCoordinates_range f n)

private theorem MappingTorusHomology.cokernelInclusion_range_eq_ker_kernelBoundary {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (n : ℕ) :
    LinearMap.range (cokernelInclusion f (n + 1)) = LinearMap.ker (kernelBoundary f n) :=
  Algebra.cokernelInclusion_range_eq_ker_kernelBoundary _ _ _ _ (twoArc_exact_at_pair f (n + 1))
    (boundaryCoordinates_ker f n) (boundaryCoordinates_range f n)

private theorem
    MappingTorusHomology.fibreHomologyMap_zero_surjective {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) : Function.Surjective (fibreHomologyMap f 0) := by
  intro b
  obtain ⟨a, ha⟩ :=
    SingularMayerVietoris.rightHomologyMap_zero_surjective (MappingTorus.HomologyCover.U f)
      (MappingTorus.HomologyCover.V f) (MappingTorus.HomologyCover.U_open f)
      (MappingTorus.HomologyCover.V_open f) (MappingTorus.HomologyCover.cover f) b
  exact
    ⟨(arcHomologyEquiv f 0 a).1 + (arcHomologyEquiv f 0 a).2,
      (rightHomologyMap_coordinates f 0 a).symm.trans ha⟩

private theorem
    MappingTorusHomology.cokernelInclusion_zero_surjective {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) : Function.Surjective (cokernelInclusion f 0) := by
  intro b
  obtain ⟨a, ha⟩ := fibreHomologyMap_zero_surjective f b
  exact ⟨Submodule.Quotient.mk a, ha⟩

private def
    MappingTorusHomology.degreeZeroHomologyEquiv {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) 0 ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X 0 ⧸ LinearMap.range (wangDifference f 0)) :=
  (LinearEquiv.ofBijective (cokernelInclusion f 0)
      ⟨cokernelInclusion_injective f 0, cokernelInclusion_zero_surjective f⟩).symm

private def ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToFullFilling (j : Elliptic.Kind) :
    C(SpecialBoundary j, SpecialPeriods.EllipticFilling.SpecialFullFilling j) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
        C(SpecialPeriods.Threefold.SpecialEllipticPiece j,
          SpecialPeriods.EllipticFilling.SpecialFullFilling j)).comp
    (specialBoundaryToPiece j)

private abbrev ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface (j : Elliptic.Kind) :=
  Elliptic.Surface j (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod j.twist
    (Elliptic.mainTwist_admissible j)

end Mathoverflow1973

end
