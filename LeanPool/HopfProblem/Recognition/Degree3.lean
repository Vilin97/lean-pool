/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods12
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz2
import all LeanPool.HopfProblem.Hurewicz.SecondHurewicz
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Recognition.Smale5
import all LeanPool.HopfProblem.Recognition.Degree1
import all LeanPool.HopfProblem.Recognition.Degree2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Recognition.Smale6
import all LeanPool.HopfProblem.Recognition.Smale8
import all LeanPool.HopfProblem.Recognition.Smale9
import all LeanPool.HopfProblem.Recognition.Smale10
import all LeanPool.HopfProblem.Threefold.SpecialPeriods11
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube1
import all LeanPool.HopfProblem.Recognition.Smale11
import all LeanPool.HopfProblem.Hurewicz.HigherHurewicz1
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube2
import all LeanPool.HopfProblem.Recognition.Smale12
import all LeanPool.HopfProblem.Hurewicz.SixthHurewicz
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods12

/-!
# Hopf problem: recognition · degree 3

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

private theorem Degree.sphereMap_piSix_bijective (x : SpecialPeriods.Threefold.Space) :
    Function.Bijective
      (SixthHurewicz.homotopyMap (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)
        SixSphereCube.sphereBasePoint) := by
  let f := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
  let := Sphere.piTwo_subsingleton SixSphereCube.sphereBasePoint
  let := Sphere.piThree_subsingleton SixSphereCube.sphereBasePoint
  let := Sphere.piFour_subsingleton SixSphereCube.sphereBasePoint
  let := Sphere.piFive_subsingleton SixSphereCube.sphereBasePoint
  let := SpecialPeriods.Threefold.space_simplyConnected
  let := SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton (f SixSphereCube.sphereBasePoint)
  let :=
    SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton (f SixSphereCube.sphereBasePoint)
  let :=
    SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton (f SixSphereCube.sphereBasePoint)
  let :=
    SpecialPeriods.Threefold.HomotopyFive.piFive_subsingleton (f SixSphereCube.sphereBasePoint)
  let source := SixthHurewicz.hurewiczLinearEquiv SixSphereCube.sphereBasePoint
  let target := SixthHurewicz.hurewiczLinearEquiv (f SixSphereCube.sphereBasePoint)
  let middle := SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyEquiv x 6
  have natural (a : π_ 6 SixSphereCube.StandardSphere SixSphereCube.sphereBasePoint) :
    middle (source (Additive.ofMul a)) =
      target (Additive.ofMul (SixthHurewicz.homotopyMap f SixSphereCube.sphereBasePoint a)) :=
    SixthHurewicz.hurewiczLinearEquiv_natural f SixSphereCube.sphereBasePoint (Additive.ofMul a)
  constructor
  · intro a b hab
    have hm : middle (source (Additive.ofMul a)) = middle (source (Additive.ofMul b)) :=
      (natural a).trans
        ((congrArg (fun c => target (Additive.ofMul c)) hab).trans (natural b).symm)
    exact congrArg Additive.toMul (source.injective (middle.injective hm))
  · intro b
    let a := source.symm (middle.symm (target (Additive.ofMul b)))
    refine ⟨Additive.toMul a, ?_⟩
    have ht :
      target
          (Additive.ofMul
            (SixthHurewicz.homotopyMap f SixSphereCube.sphereBasePoint (Additive.toMul a))) =
        target (Additive.ofMul b) := by
      calc
        _ = middle (source a) := (natural (Additive.toMul a)).symm
        _ = target (Additive.ofMul b) := by
          dsimp [a]
          rw [source.apply_symm_apply, middle.apply_symm_apply]
    exact congrArg Additive.toMul (target.injective ht)

private theorem Degree.BasedDiskLifting.exists_based_disk_lift {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (x : SpecialPeriods.Threefold.Space)
    (L : V ≃L[ℝ] (Fin 6 → ℝ))
    (u : C(Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space))
    (hu :
      ∀ z : Degree.DiskCylinder.Disk (E := V),
        ‖(z : V)‖ = 1 →
          u z =
            SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
              SixSphereCube.sphereBasePoint) :
    ∃ v : C(Degree.DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere),
      (∀ z : Degree.DiskCylinder.Disk (E := V),
          ‖(z : V)‖ = 1 → v z = SixSphereCube.sphereBasePoint) ∧
        ((SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x).comp v).HomotopicRel u
          {z : Degree.DiskCylinder.Disk (E := V) | ‖(z : V)‖ = 1} := by
  let F := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
  let e := Degree.DiskCube.homeomorph L
  let q : GenLoop (Fin 6) SpecialPeriods.Threefold.Space (F SixSphereCube.sphereBasePoint) :=
    ⟨u.comp (e.symm : C(_, _)), fun z hz =>
      hu (e.symm z) ((Degree.DiskCube.symm_boundary_iff L z).mpr hz)⟩
  obtain ⟨a, ha⟩ := (Degree.sphereMap_piSix_bijective x).2 ⟦q⟧
  obtain ⟨p, hp⟩ := Quotient.exists_rep a
  have he : SixthHurewicz.homotopyMap F SixSphereCube.sphereBasePoint ⟦p⟧ = ⟦q⟧ :=
    (congrArg (SixthHurewicz.homotopyMap F SixSphereCube.sphereBasePoint) hp).trans ha
  have hh : GenLoop.Homotopic (SecondHurewicz.mapGenLoop F SixSphereCube.sphereBasePoint p) q :=
    Quotient.exact he
  obtain ⟨H⟩ := hh
  let v : C(Degree.DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere) :=
    p.val.comp (e : C(_, _))
  refine
    ⟨v, ?_,
      ⟨{  toFun := fun z => H (z.1, e z.2)
          continuous_toFun :=
            H.continuous.comp (continuous_fst.prodMk (e.continuous.comp continuous_snd))
          map_zero_left := ?_
          map_one_left := ?_
          prop' := ?_ }⟩⟩
  · intro z hz
    exact p.property (e z) ((Degree.DiskCube.boundary_iff L z).mpr hz)
  · intro z
    exact H.apply_zero (e z)
  · intro z
    exact (H.apply_one (e z)).trans (congrArg u (e.symm_apply_apply z))
  · intro t z hz
    exact H.eq_fst t ((Degree.DiskCube.boundary_iff L z).mpr hz)

private def Degree.CylinderBall.boundary {V : Type*} [NormedAddCommGroup V] :
    Set ((unitInterval) × Degree.DiskCylinder.Disk (E := V)) :=
  {p | p.1 = 0 ∨ p.1 = 1 ∨ ‖(p.2 : V)‖ = 1}

private theorem
    Degree.CylinderBall.time_norm_le (t : (unitInterval)) : ‖(2 * t.val - 1 : ℝ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [t.property.1, t.property.2]

private def Degree.CylinderBall.forward {V : Type*} [NormedAddCommGroup V] :
    C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Degree.DiskCylinder.Disk (E := ℝ × V))
    where
  toFun
    p :=
    ⟨(2 * p.1.val - 1, p.2.val),
      mem_closedBall_zero_iff.mpr
        (max_le (time_norm_le p.1) (mem_closedBall_zero_iff.mp p.2.property))⟩
  continuous_toFun :=
    (((continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub
              continuous_const).prodMk
          (continuous_subtype_val.comp continuous_snd)).subtype_mk
      _

private def Degree.CylinderBall.inverseTime {V : Type*} [NormedAddCommGroup V]
    (z : Degree.DiskCylinder.Disk (E := ℝ × V)) : (unitInterval) :=
  ⟨(z.val.1 + 1) / 2,
    by
    have hn : |z.val.1| ≤ 1 := (max_le_iff.mp (mem_closedBall_zero_iff.mp z.property)).1
    rcases abs_le.mp hn with ⟨hl, hu⟩
    constructor <;> linarith⟩

private def Degree.CylinderBall.inverseSpace {V : Type*} [NormedAddCommGroup V]
    (z : Degree.DiskCylinder.Disk (E := ℝ × V)) : Degree.DiskCylinder.Disk (E := V) :=
  ⟨z.val.2,
    mem_closedBall_zero_iff.mpr ((max_le_iff.mp (mem_closedBall_zero_iff.mp z.property)).2)⟩

private def Degree.CylinderBall.inverse {V : Type*} [NormedAddCommGroup V] :
    C(Degree.DiskCylinder.Disk (E := ℝ × V), (unitInterval) × Degree.DiskCylinder.Disk (E := V))
    where
  toFun z := (inverseTime z, inverseSpace z)
  continuous_toFun := by
    have ht : Continuous (fun z : Degree.DiskCylinder.Disk (E := ℝ × V) => (z.val.1 + 1) / 2) := by
      fun_prop
    exact (ht.subtype_mk _).prodMk ((continuous_snd.comp continuous_subtype_val).subtype_mk _)

private def Degree.CylinderBall.homeomorph {V : Type*} [NormedAddCommGroup V] :
    ((unitInterval) × Degree.DiskCylinder.Disk (E := V)) ≃ₜ Degree.DiskCylinder.Disk (E := ℝ × V)
    where
  toFun := forward
  invFun := inverse
  left_inv
    p := by
    apply Prod.ext
    · apply Subtype.ext
      change ((2 * p.1.val - 1) + 1) / 2 = p.1.val
      ring
    · rfl
  right_inv
    z := by
    apply Subtype.ext
    apply Prod.ext
    · change 2 * ((z.val.1 + 1) / 2) - 1 = z.val.1
      ring
    · rfl
  continuous_toFun := forward.continuous
  continuous_invFun := inverse.continuous

private theorem Degree.CylinderBall.norm_eq_one_iff {V : Type*} [NormedAddCommGroup V]
    (p : (unitInterval) × Degree.DiskCylinder.Disk (E := V)) :
    ‖((homeomorph (V := V) p).val)‖ = 1 ↔ p ∈ boundary := by
  change Max.max ‖(2 * p.1.val - 1 : ℝ)‖ ‖p.2.val‖ = 1 ↔ _
  constructor
  · intro he
    rcases le_total ‖(2 * p.1.val - 1 : ℝ)‖ ‖p.2.val‖ with h | h
    · exact Or.inr (Or.inr (by rwa [max_eq_right h] at he))
    · rw [max_eq_left h, Real.norm_eq_abs] at he
      have he' : |2 * p.1.val - 1| = |(1 : ℝ)| := by simpa using he
      rcases abs_eq_abs.mp he' with h | h
      · exact Or.inr (Or.inl (Subtype.ext (show p.1.val = (1 : ℝ) by linarith)))
      · exact Or.inl (Subtype.ext (show p.1.val = (0 : ℝ) by linarith))
  · rintro (h | h | h)
    · have ht : p.1.val = 0 := congrArg Subtype.val h
      rw [ht]
      norm_num
      exact mem_closedBall_zero_iff.mp p.2.property
    · have ht : p.1.val = 1 := congrArg Subtype.val h
      rw [ht]
      norm_num
      exact mem_closedBall_zero_iff.mp p.2.property
    · rw [h, max_eq_right (time_norm_le p.1)]

private def Degree.CylinderBall.diskSphereHomeomorph {V : Type*} [NormedAddCommGroup V] :
    { z : Degree.DiskCylinder.Disk (E := V) // ‖(z : V)‖ = 1 } ≃ₜ
      Degree.DiskCylinder.Sphere (E := V)
    where
  toFun z := ⟨z.val.val, mem_sphere_zero_iff_norm.mpr z.property⟩
  invFun s := ⟨Degree.DiskCylinder.boundaryToDisk s, mem_sphere_zero_iff_norm.mp s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := Degree.DiskCylinder.boundaryToDisk.continuous.subtype_mk _

private def Degree.CylinderBall.boundaryHomeomorph {V : Type*} [NormedAddCommGroup V] :
    boundary (V := V) ≃ₜ Degree.DiskCylinder.Sphere (E := ℝ × V) :=
  ((homeomorph (V := V)).subtype (fun p => (norm_eq_one_iff p).symm)).trans diskSphereHomeomorph

private def Degree.CylinderBoundary.lower {V : Type*} [NormedAddCommGroup V] :
    C(Degree.DiskCylinder.bottomOrSide (E := V), Degree.CylinderBall.boundary (V := V)) :=
  ⟨fun p => ⟨p.val, p.property.elim Or.inl (fun h => Or.inr (Or.inr h))⟩,
    continuous_subtype_val.subtype_mk _⟩

private def Degree.CylinderBoundary.top {V : Type*} [NormedAddCommGroup V] :
    C(Degree.DiskCylinder.Disk (E := V), Degree.CylinderBall.boundary (V := V)) :=
  ⟨fun z => ⟨(1, z), Or.inr (Or.inl rfl)⟩, (continuous_const.prodMk continuous_id).subtype_mk _⟩

private def Degree.CylinderBoundary.quotient {V : Type*} [NormedAddCommGroup V] :
    C(Degree.DiskCylinder.bottomOrSide (E := V) ⊕ Degree.DiskCylinder.Disk (E := V),
      Degree.CylinderBall.boundary (V := V)) :=
  ⟨Sum.elim Degree.CylinderBoundary.lower top,
    Degree.CylinderBoundary.lower.continuous.sumElim top.continuous⟩

private theorem Degree.CylinderBoundary.quotient_surjective {V : Type*} [NormedAddCommGroup V] :
    Function.Surjective (quotient (V := V)) := by
  rintro ⟨⟨t, z⟩, ht | ht | hz⟩
  · exact ⟨.inl ⟨(t, z), Or.inl ht⟩, rfl⟩
  · change t = 1 at ht
    subst t
    exact ⟨.inr z, rfl⟩
  · exact ⟨.inl ⟨(t, z), Or.inr hz⟩, rfl⟩

private theorem Degree.CylinderBoundary.quotient_isQuotientMap {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] : Topology.IsQuotientMap (quotient (V := V)) := by
  have hclosed : IsClosed (Degree.DiskCylinder.bottomOrSide (E := V)) :=
    (isClosed_eq continuous_fst continuous_const).union
      (isClosed_eq (continuous_subtype_val.comp continuous_snd).norm continuous_const)
  let : CompactSpace (Degree.DiskCylinder.bottomOrSide (E := V)) :=
    isCompact_iff_compactSpace.mp hclosed.isCompact
  exact .of_surjective_continuous quotient_surjective quotient.continuous

private theorem Degree.CylinderBoundary.lower_top_compat {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(Degree.DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (Degree.DiskCylinder.boundaryToDisk s))
    (a : Degree.DiskCylinder.bottomOrSide (E := V)) (b : Degree.DiskCylinder.Disk (E := V))
    (he : Degree.CylinderBoundary.lower a = top b) :
    Degree.DiskCylinder.gluedBottomSide f H h0 a = g b := by
  have ht : a.val.1 = (1 : (unitInterval)) :=
    congrArg (fun p : Degree.CylinderBall.boundary (V := V) => p.val.1) he
  have hz : a.val.2 = b := congrArg (fun p : Degree.CylinderBall.boundary (V := V) => p.val.2) he
  have hs : ‖(a.val.2 : V)‖ = 1 := by
    rcases a.property with h | h
    · exact False.elim (zero_ne_one (h.symm.trans ht))
    · exact h
  let s : Degree.DiskCylinder.Sphere (E := V) := ⟨a.val.2.val, mem_sphere_zero_iff_norm.mpr hs⟩
  have ha : a = Degree.DiskCylinder.sideMap (1, s) := Subtype.ext (Prod.ext ht rfl)
  rw [ha, Degree.DiskCylinder.gluedBottomSide_side]
  exact (h1 s).trans (congrArg g hz)

private def Degree.CylinderBoundary.data {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(Degree.DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (Degree.DiskCylinder.boundaryToDisk s)) :
    C(Degree.DiskCylinder.bottomOrSide (E := V) ⊕ Degree.DiskCylinder.Disk (E := V), X) :=
  ⟨Sum.elim (Degree.DiskCylinder.gluedBottomSide f H h0) g,
    (Degree.DiskCylinder.gluedBottomSide f H h0).continuous.sumElim g.continuous⟩

private theorem Degree.CylinderBoundary.data_constant_on_fibres {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(Degree.DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (Degree.DiskCylinder.boundaryToDisk s))
    (a b : Degree.DiskCylinder.bottomOrSide (E := V) ⊕ Degree.DiskCylinder.Disk (E := V))
    (he : quotient a = quotient b) : data f g H h0 a = data f g H h0 b := by
  cases a with
  | inl a =>
    cases b with
    | inl
      b =>
      have hv : a.val = b.val :=
        congrArg (fun p : Degree.CylinderBall.boundary (V := V) => p.val) he
      exact congrArg (Degree.DiskCylinder.gluedBottomSide f H h0) (Subtype.ext hv)
    | inr b => exact lower_top_compat f g H h0 h1 a b he
  | inr a =>
    cases b with
    | inl b => exact (lower_top_compat f g H h0 h1 b a he.symm).symm
    | inr b =>
      exact congrArg g (congrArg (fun p : Degree.CylinderBall.boundary (V := V) => p.val.2) he)

private def Degree.CylinderBoundary.glued {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(Degree.DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (Degree.DiskCylinder.boundaryToDisk s)) :
    C(Degree.CylinderBall.boundary (V := V), X) :=
  quotient_isQuotientMap.lift (data f g H h0) (data_constant_on_fibres f g H h0 h1)

private theorem
    Degree.CylinderBoundary.glued_lower {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(Degree.DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (Degree.DiskCylinder.boundaryToDisk s))
    (a : Degree.DiskCylinder.bottomOrSide (E := V)) :
    glued f g H h0 h1 (Degree.CylinderBoundary.lower a) =
      Degree.DiskCylinder.gluedBottomSide f H h0 a :=
  ContinuousMap.congr_fun
    (quotient_isQuotientMap.lift_comp (data f g H h0) (data_constant_on_fibres f g H h0 h1))
    (.inl a)

private theorem
    Degree.CylinderBoundary.glued_top {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(Degree.DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (Degree.DiskCylinder.boundaryToDisk s))
    (z : Degree.DiskCylinder.Disk (E := V)) : glued f g H h0 h1 (top z) = g z :=
  ContinuousMap.congr_fun
    (quotient_isQuotientMap.lift_comp (data f g H h0) (data_constant_on_fibres f g H h0 h1))
    (.inr z)

private theorem
    Degree.CylinderBoundary.glued_bottom {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(Degree.DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (Degree.DiskCylinder.boundaryToDisk s))
    (z : Degree.DiskCylinder.Disk (E := V)) :
    glued f g H h0 h1 (Degree.CylinderBoundary.lower (Degree.DiskCylinder.bottomMap z)) = f z := by
  rw [glued_lower, Degree.DiskCylinder.gluedBottomSide_bottom]

private theorem
    Degree.CylinderBoundary.glued_side {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {X : Type*} [TopologicalSpace X]
    (f g : C(Degree.DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (Degree.DiskCylinder.boundaryToDisk s)) (t : (unitInterval))
    (s : Degree.DiskCylinder.Sphere (E := V)) :
    glued f g H h0 h1 (Degree.CylinderBoundary.lower (Degree.DiskCylinder.sideMap (t, s))) =
      H (t, s) := by rw [glued_lower, Degree.DiskCylinder.gluedBottomSide_side]

private abbrev Degree.SphereCube.Sphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

private def Degree.SphereCube.compactification (n : ℕ) :
    OnePoint (SixSphereCube.CubeInteriorN n) ≃ₜ Sphere n :=
  (SixSphereCube.cubeInteriorEuclideanHomeomorph n).onePointCongr.trans
    (onePointEquivSphereOfFinrankEq (V := EuclideanSpace ℝ (Fin n)) (ι := Fin (n + 1)) (by simp))

private def Degree.SphereCube.point (n : ℕ) : Sphere n :=
  compactification n (OnePoint.infty)

private def Degree.SphereCube.quotient (n : ℕ) : C(Fin n → (unitInterval), Sphere n) :=
  (compactification n : C(OnePoint (SixSphereCube.CubeInteriorN n), Sphere n)).comp
    (SixSphereCube.collapseMap (Cube.boundary (Fin n)) (SixSphereCube.isClosed_cubeBoundaryN n))

private theorem Degree.SphereCube.quotient_boundary (n : ℕ) (z : Fin n → (unitInterval))
    (hz : z ∈ Cube.boundary (Fin n)) : quotient n z = point n := by
  change
    compactification n (SixSphereCube.collapse (Cube.boundary (Fin n)) z) =
      compactification n (OnePoint.infty)
  rw [SixSphereCube.collapse_of_mem _ hz]

private theorem Degree.SphereCube.zero_boundary {n : ℕ} (hn : 0 < n) :
    (0 : Fin n → (unitInterval)) ∈ Cube.boundary (Fin n) :=
  ⟨⟨0, hn⟩, Or.inl rfl⟩

private theorem Degree.SphereCube.quotient_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (quotient n) :=
  (compactification n).surjective.comp
    (SixSphereCube.collapse_surjective (Cube.boundary (Fin n)) ⟨0, zero_boundary hn⟩)

private theorem Degree.SphereCube.quotient_eq_iff (n : ℕ) (z w : Fin n → (unitInterval)) :
    quotient n z = quotient n w ↔ z = w ∨ z ∈ Cube.boundary (Fin n) ∧ w ∈ Cube.boundary (Fin n) :=
  by
  change
    compactification n (SixSphereCube.collapse (Cube.boundary (Fin n)) z) =
        compactification n (SixSphereCube.collapse (Cube.boundary (Fin n)) w) ↔
      _
  rw [(compactification n).injective.eq_iff, SixSphereCube.collapse_eq_iff]

private def Degree.SphereCube.cylinder (n : ℕ) :
    C((unitInterval) × (Fin n → (unitInterval)), (unitInterval) × Sphere n) :=
  (ContinuousMap.id (unitInterval)).prodMap (quotient n)

private theorem Degree.SphereCube.cylinder_surjective {n : ℕ} (hn : 0 < n) :
    Function.Surjective (cylinder n) := by
  rintro ⟨t, z⟩
  obtain ⟨w, rfl⟩ := quotient_surjective hn z
  exact ⟨(t, w), rfl⟩

private theorem Degree.SphereCube.cylinder_isQuotientMap {n : ℕ} (hn : 0 < n) :
    Topology.IsQuotientMap (cylinder n) :=
  .of_surjective_continuous (cylinder_surjective hn) (cylinder n).continuous

private def
    Degree.SphereCube.basedCube {n : ℕ} {X : Type*} [TopologicalSpace X] (u : C(Sphere n, X)) :
    GenLoop (Fin n) X (u (point n)) :=
  ⟨u.comp (quotient n), fun z hz => congrArg u (quotient_boundary n z hz)⟩

private theorem Degree.SphereCube.homotopicRel_const_of_subsingleton {n : ℕ} {X : Type*}
    [TopologicalSpace X] (hn : 0 < n) (u : C(Sphere n, X)) [Subsingleton (π_ n X (u (point n)))] :
    u.HomotopicRel (ContinuousMap.const (Sphere n) (u (point n))) {point n} := by
  let H := HigherHurewicz.nativeCubeNullHomotopy (basedCube u)
  have hfib : ∀ a b, cylinder n a = cylinder n b → H a = H b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : quotient n z = quotient n w := congrArg Prod.snd h
    rcases (quotient_eq_iff n z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact
        ((H.eq_fst t hz).trans ((basedCube u).property z hz)).trans
          ((H.eq_fst t hw).trans ((basedCube u).property w hw)).symm
  let G := (cylinder_isQuotientMap hn).lift H.toHomotopy.toContinuousMap hfib
  have hG (t : (unitInterval)) (z : Fin n → (unitInterval)) : G (t, quotient n z) = H (t, z) :=
    ContinuousMap.congr_fun
      ((cylinder_isQuotientMap hn).lift_comp H.toHomotopy.toContinuousMap hfib) (t, z)
  refine
    ⟨{  toContinuousMap := G
        map_zero_left := ?_
        map_one_left := ?_
        prop' := ?_ }⟩
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 0 w).trans (H.apply_zero w)
  · intro z
    obtain ⟨w, rfl⟩ := quotient_surjective hn z
    exact (hG 1 w).trans (H.apply_one w)
  · intro t z hz
    have hz' : z = point n := hz
    subst z
    change G (t, point n) = u (point n)
    rw [← quotient_boundary n 0 (zero_boundary hn), hG]
    exact H.eq_fst t (zero_boundary hn)

private theorem Degree.Sphere.pi_subsingleton {n : ℕ} (hn : 0 < n) (hn6 : n < 6)
    (x : SixSphereCube.StandardSphere) : Subsingleton (π_ n SixSphereCube.StandardSphere x) := by
  have hn5 : n ≤ 5 := by omega
  interval_cases n
  · exact (HomotopyGroup.pi1EquivFundamentalGroup).injective.subsingleton
  · exact piTwo_subsingleton x
  · exact piThree_subsingleton x
  · exact piFour_subsingleton x
  · exact piFive_subsingleton x

private theorem Degree.Sphere.homotopic_const_discrete {Z X : Type} [TopologicalSpace Z]
    [DiscreteTopology Z] [TopologicalSpace X] [PathConnectedSpace X] (u : C(Z, X)) (x : X) :
    u.Homotopic (ContinuousMap.const Z x) := by
  refine
    ⟨{  toFun := fun p => (PathConnectedSpace.somePath (u p.2) x) p.1
        continuous_toFun :=
          continuous_prod_of_discrete_right.mpr
            (fun z => (PathConnectedSpace.somePath (u z) x).continuous)
        map_zero_left := fun z => (PathConnectedSpace.somePath (u z) x).source
        map_one_left := fun z => (PathConnectedSpace.somePath (u z) x).target }⟩

private theorem Degree.Sphere.real_unitSphere_finite : (Metric.sphere (0 : ℝ) 1).Finite := by
  apply (Set.toFinite ({1, -1} : Set ℝ)).subset
  intro x hx
  have h : |x| = |(1 : ℝ)| := by simpa using mem_sphere_zero_iff_norm.mp hx
  rcases abs_eq_abs.mp h with h | h <;> simp [h]

private theorem Degree.Sphere.homotopic_const_of_homeomorph {Z W X : Type} [TopologicalSpace Z]
    [TopologicalSpace W] [TopologicalSpace X] (e : Z ≃ₜ W) (u : C(Z, X)) (x : X)
    (h : (u.comp (e.symm : C(W, Z))).Homotopic (ContinuousMap.const W x)) :
    u.Homotopic (ContinuousMap.const Z x) := by
  have hh := h.comp (ContinuousMap.Homotopic.refl (e : C(Z, W)))
  convert hh using 1
  · apply ContinuousMap.ext
    intro z
    exact (congrArg u (e.symm_apply_apply z)).symm
  · rfl

private theorem Degree.Sphere.boundary_homotopic_const_of_pi {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] {d : ℕ} (hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))
    (hd : Module.finrank ℝ V ≤ d) (u : C(Degree.DiskCylinder.Sphere (E := V), X)) (x : X) :
    u.Homotopic (ContinuousMap.const _ x) := by
  classical
    cases subsingleton_or_nontrivial V with
  | inl
    h =>
    have hempty (s : Degree.DiskCylinder.Sphere (E := V)) : False :=
      Degree.UnitSphereEquiv.vector_ne_zero s (Subsingleton.elim _ _)
    have he : u = ContinuousMap.const _ x := ContinuousMap.ext (fun s => (hempty s).elim)
    rw [he]
  | inr h =>
    by_cases hd1 : Module.finrank ℝ V = 1
    · obtain ⟨L⟩ :=
        FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
          (show Module.finrank ℝ V = Module.finrank ℝ ℝ by simpa using hd1)
      let e := Degree.UnitSphereEquiv.homeomorph L
      let : Finite (Degree.DiskCylinder.Sphere (E := ℝ)) := real_unitSphere_finite.to_subtype
      let : Finite (Degree.DiskCylinder.Sphere (E := V)) := Finite.of_injective e e.injective
      exact homotopic_const_discrete u x
    · have hdpos : 0 < Module.finrank ℝ V := Module.finrank_pos
      let n := Module.finrank ℝ V - 1
      have hn : 0 < n := by dsimp [n]; omega
      have hnd : n < d := by dsimp [n]; omega
      obtain ⟨L⟩ :=
        FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
          (show Module.finrank ℝ V = Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
            by
            simp only [finrank_euclideanSpace, Fintype.card_fin]
            dsimp [n]
            omega)
      let e := Degree.UnitSphereEquiv.homeomorph L
      let v : C(Degree.SphereCube.Sphere n, X) := u.comp (e.symm : C(_, _))
      let := hpi n hn hnd (v (Degree.SphereCube.point n))
      obtain ⟨H⟩ := Degree.SphereCube.homotopicRel_const_of_subsingleton hn v
      have hstart : v.Homotopic (ContinuousMap.const _ (v (Degree.SphereCube.point n))) :=
        ⟨H.toHomotopy⟩
      have hv : v.Homotopic (ContinuousMap.const _ x) :=
        hstart.trans
          ⟨(PathConnectedSpace.somePath (v (Degree.SphereCube.point n)) x).toHomotopyConst⟩
      exact homotopic_const_of_homeomorph e u x hv

private theorem Degree.Sphere.exists_boundary_extension_of_pi {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {X : Type} [TopologicalSpace X]
    [PathConnectedSpace X] {d : ℕ} (hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))
    (hd : Module.finrank ℝ V ≤ d) (u : C(Degree.DiskCylinder.Sphere (E := V), X)) (x : X) :
    ∃ v : C(Degree.DiskCylinder.Disk (E := V), X),
      (∀ s, v (Degree.DiskCylinder.boundaryToDisk s) = u s) ∧ v ⟨0, by simp⟩ = x := by
  classical
    cases isEmpty_or_nonempty (Degree.DiskCylinder.Sphere (E := V)) with
  | inl h => exact ⟨ContinuousMap.const _ x, fun s => isEmptyElim s, rfl⟩
  | inr h =>
    let s0 : Degree.DiskCylinder.Sphere (E := V) := Classical.choice h
    obtain ⟨H⟩ := (boundary_homotopic_const_of_pi hpi hd u x).symm
    let G := H.toContinuousMap
    have h0 : ∀ s, G (0, s) = x := H.map_zero_left
    refine ⟨Degree.DiskCone.extension s0 G x h0, ?_, Degree.DiskCone.extension_center s0 G x h0⟩
    intro s
    exact (Degree.DiskCone.extension_boundary s0 G x h0 s).trans (H.map_one_left s)

private theorem
    Degree.Sphere.boundary_homotopic_const {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (hd : Module.finrank ℝ V ≤ 6)
    (u : C(Degree.DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere))
    (x : SixSphereCube.StandardSphere) : u.Homotopic (ContinuousMap.const _ x) :=
  boundary_homotopic_const_of_pi (fun _ hn hn6 => pi_subsingleton hn hn6) hd u x

private theorem Degree.Sphere.exists_boundary_extension {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hd : Module.finrank ℝ V ≤ 6)
    (u : C(Degree.DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere))
    (x : SixSphereCube.StandardSphere) :
    ∃ v : C(Degree.DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere),
      (∀ s, v (Degree.DiskCylinder.boundaryToDisk s) = u s) ∧ v ⟨0, by simp⟩ = x :=
  exists_boundary_extension_of_pi (fun _ hn hn6 => pi_subsingleton hn hn6) hd u x

private theorem Degree.CylinderFilling.exists_filling {V X : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace X] [PathConnectedSpace X] {d : ℕ}
    (hpi : ∀ n, 0 < n → n < d → ∀ x : X, Subsingleton (π_ n X x))
    (hd : Module.finrank ℝ V + 1 ≤ d) (f g : C(Degree.DiskCylinder.Disk (E := V), X))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), X))
    (h0 : ∀ s, H (0, s) = f (Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ s, H (1, s) = g (Degree.DiskCylinder.boundaryToDisk s)) (x : X) :
    ∃ G : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), X),
      (∀ z, G (0, z) = f z) ∧
        (∀ z, G (1, z) = g z) ∧ ∀ t s, G (t, Degree.DiskCylinder.boundaryToDisk s) = H (t, s) := by
  let b := Degree.CylinderBoundary.glued f g H h0 h1
  let e := Degree.CylinderBall.boundaryHomeomorph (V := V)
  let u :=
    b.comp
      (e.symm : C(Degree.DiskCylinder.Sphere (E := ℝ × V), Degree.CylinderBall.boundary (V := V)))
  have hdim : Module.finrank ℝ (ℝ × V) ≤ d := by
    simpa only [Module.finrank_prod, Module.finrank_self, Nat.add_comm] using hd
  obtain ⟨v, hv, _⟩ := Degree.Sphere.exists_boundary_extension_of_pi hpi hdim u x
  let G : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), X) :=
    v.comp (Degree.CylinderBall.homeomorph (V := V) : C(_, _))
  have hb (p : Degree.CylinderBall.boundary (V := V)) : G p.val = b p := by
    change v (Degree.DiskCylinder.boundaryToDisk (Degree.CylinderBall.boundaryHomeomorph p)) = b p
    exact
      (hv (Degree.CylinderBall.boundaryHomeomorph p)).trans
        (congrArg b (Degree.CylinderBall.boundaryHomeomorph.symm_apply_apply p))
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z
    exact
      (hb (Degree.CylinderBoundary.lower (Degree.DiskCylinder.bottomMap z))).trans
        (Degree.CylinderBoundary.glued_bottom f g H h0 h1 z)
  · intro z
    exact
      (hb (Degree.CylinderBoundary.top z)).trans (Degree.CylinderBoundary.glued_top f g H h0 h1 z)
  · intro t s
    exact
      (hb (Degree.CylinderBoundary.lower (Degree.DiskCylinder.sideMap (t, s)))).trans
        (Degree.CylinderBoundary.glued_side f g H h0 h1 t s)

private abbrev
    Degree.Attachment.Union {K M : Type*} [TopologicalSpace K] [TopologicalSpace M] (A : Set M)
    (h : C(K, M)) :=
  ↥(A ∪ Set.range h)

private def Degree.Attachment.sumQuotient {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (h : C(K, M)) : C(A ⊕ K, Degree.Attachment.Union A h) :=
  ⟨Smale.ClosedAttachment.sumMap A h, Smale.ClosedAttachment.continuous_sumMap A h⟩

private theorem Degree.Attachment.sumQuotient_surjective {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (h : C(K, M)) : Function.Surjective (sumQuotient A h) := by
  rintro ⟨x, hx | ⟨k, rfl⟩⟩
  · exact ⟨.inl ⟨x, hx⟩, rfl⟩
  · exact ⟨.inr k, rfl⟩

private def
    Degree.Attachment.cylinderQuotient {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (h : C(K, M)) :
    C((unitInterval) × (A ⊕ K), (unitInterval) × Degree.Attachment.Union A h) :=
  (ContinuousMap.id (unitInterval)).prodMap (sumQuotient A h)

private theorem Degree.Attachment.cylinderQuotient_surjective {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (h : C(K, M)) : Function.Surjective (cylinderQuotient A h) :=
  by
  rintro ⟨t, x⟩
  obtain ⟨z, rfl⟩ := sumQuotient_surjective A h x
  exact ⟨(t, z), rfl⟩

private theorem Degree.Attachment.cylinderQuotient_isQuotientMap {K M : Type*} [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (h : C(K, M)) :
    Topology.IsQuotientMap (cylinderQuotient A h) :=
  .of_surjective_continuous (cylinderQuotient_surjective A h) (cylinderQuotient A h).continuous

private def Degree.Attachment.familyOnSum {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) {r : C(K, K)}
    (H : (ContinuousMap.id K).HomotopyRel r B) :
    C((unitInterval) × (A ⊕ K), Degree.Attachment.Union A h)
    where
  toFun
    p :=
    match p.2 with
    | .inl a => ⟨a.val, Or.inl a.property⟩
    | .inr k => ⟨h (H (p.1, k)), Or.inr ⟨H (p.1, k), rfl⟩⟩
  continuous_toFun := by
    have ha :
      Continuous
        (fun p : (unitInterval) × A =>
          (⟨p.2.val, Or.inl p.2.property⟩ : Degree.Attachment.Union A h)) :=
      (continuous_subtype_val.comp continuous_snd).subtype_mk _
    have hk :
      Continuous
        (fun p : (unitInterval) × K =>
          (⟨h (H p), Or.inr ⟨H p, rfl⟩⟩ : Degree.Attachment.Union A h)) :=
      (h.continuous.comp H.continuous).subtype_mk _
    convert
      (ha.sumElim hk).comp
        (Homeomorph.prodSumDistrib : (unitInterval) × (A ⊕ K) ≃ₜ _).continuous using
      1
    funext p
    rcases p with ⟨t, a | k⟩ <;> rfl

private theorem Degree.Attachment.familyOnSum_constant_on_fibres {K M : Type*} [TopologicalSpace K]
    [TopologicalSpace M] (A : Set M) (B : Set K) (h : C(K, M)) {r : C(K, K)}
    (H : (ContinuousMap.id K).HomotopyRel r B) (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) (p q : (unitInterval) × (A ⊕ K))
    (heq : cylinderQuotient A h p = cylinderQuotient A h q) :
    familyOnSum A B h H p = familyOnSum A B h H q := by
  rcases p with ⟨t, a⟩
  rcases q with ⟨s, b⟩
  have ht : t = s := congrArg Prod.fst heq
  subst s
  have hab : sumQuotient A h a = sumQuotient A h b := congrArg Prod.snd heq
  have hv := congrArg Subtype.val hab
  cases a with
  | inl a =>
    cases b with
    | inl b => exact Subtype.ext hv
    | inr k =>
      change a.val = h k at hv
      have hk : k ∈ B := (hface k).mp (hv ▸ a.property)
      apply Subtype.ext
      change a.val = h (H (t, k))
      rw [H.eq_fst t hk]
      exact hv
  | inr k =>
    cases b with
    | inl b =>
      change h k = b.val at hv
      have hk : k ∈ B := (hface k).mp (hv.symm ▸ b.property)
      apply Subtype.ext
      change h (H (t, k)) = b.val
      rw [H.eq_fst t hk]
      exact hv
    | inr l =>
      have hkl : k = l := hinj hv
      subst l
      rfl

private def Degree.Attachment.unionFamily {K M : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (B : Set K) (h : C(K, M))
    {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B) (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) :
    C((unitInterval) × Degree.Attachment.Union A h, Degree.Attachment.Union A h) :=
  (cylinderQuotient_isQuotientMap A h).lift (familyOnSum A B h H)
    (familyOnSum_constant_on_fibres A B h H hinj hface)

@[simp]
private theorem
    Degree.Attachment.unionFamily_apply {K M : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (B : Set K) (h : C(K, M))
    {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B) (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) (t : (unitInterval)) (z : A ⊕ K) :
    unionFamily A B h H hinj hface (t, sumQuotient A h z) = familyOnSum A B h H (t, z) :=
  ContinuousMap.congr_fun
    ((cylinderQuotient_isQuotientMap A h).lift_comp (familyOnSum A B h H)
      (familyOnSum_constant_on_fibres A B h H hinj hface))
    (t, z)

private theorem Degree.Attachment.unionFamily_fixed_lower {K M : Type*} [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (B : Set K)
    (h : C(K, M)) {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B)
    (hinj : Function.Injective h) (hface : ∀ k, h k ∈ A ↔ k ∈ B) (t : (unitInterval)) (a : A) :
    unionFamily A B h H hinj hface (t, ⟨a.val, Or.inl a.property⟩) = ⟨a.val, Or.inl a.property⟩ :=
  unionFamily_apply A B h H hinj hface t (.inl a)

private theorem Degree.Attachment.unionFamily_on_handle {K M : Type*} [TopologicalSpace K]
    [CompactSpace K] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (B : Set K)
    (h : C(K, M)) {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B)
    (hinj : Function.Injective h) (hface : ∀ k, h k ∈ A ↔ k ∈ B) (t : (unitInterval)) (k : K) :
    (unionFamily A B h H hinj hface (t, ⟨h k, Or.inr ⟨k, rfl⟩⟩)).val = h (H (t, k)) :=
  congrArg Subtype.val (unionFamily_apply A B h H hinj hface t (.inr k))

private theorem
    Degree.Attachment.unionFamily_zero {K M : Type*} [TopologicalSpace K] [CompactSpace K]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A] (B : Set K) (h : C(K, M))
    {r : C(K, K)} (H : (ContinuousMap.id K).HomotopyRel r B) (hinj : Function.Injective h)
    (hface : ∀ k, h k ∈ A ↔ k ∈ B) (x : Degree.Attachment.Union A h) :
    unionFamily A B h H hinj hface (0, x) = x := by
  obtain ⟨z, rfl⟩ := sumQuotient_surjective A h x
  rw [unionFamily_apply]
  cases z with
  | inl a => rfl
  | inr k =>
    apply Subtype.ext
    exact congrArg h (H.apply_zero k)

private def Degree.Handle.interpolate {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (t : (unitInterval)) (z : Space (N := N) (P := P)) :
    Space (N := N) (P := P) :=
  (⟨(1 - (t : ℝ)) • (z.1 : N) + (t : ℝ) • ((retraction z).1 : N),
      (convex_closedBall (0 : N) 1 : Convex ℝ _) z.1.property (retraction z).1.property
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩,
    ⟨(1 - (t : ℝ)) • (z.2 : P) + (t : ℝ) • ((retraction z).2 : P),
      (convex_closedBall (0 : P) 1 : Convex ℝ _) z.2.property (retraction z).2.property
        (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩)

private theorem Degree.Handle.continuous_interpolate {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] :
    Continuous (fun tz : (unitInterval) × Space (N := N) (P := P) => interpolate tz.1 tz.2) := by
  have ht : Continuous (fun tz : (unitInterval) × Space (N := N) (P := P) => (tz.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun tz : (unitInterval) × Space (N := N) (P := P) => (tz.2.1 : N)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hv : Continuous (fun tz : (unitInterval) × Space (N := N) (P := P) => (tz.2.2 : P)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hr : Continuous (fun tz : (unitInterval) × Space (N := N) (P := P) => retraction tz.2) :=
    retraction.continuous.comp continuous_snd
  exact
    (((continuous_const.sub ht).smul hu).add
            (ht.smul (continuous_subtype_val.comp (continuous_fst.comp hr)))).subtype_mk
        _ |>.prodMk
      ((((continuous_const.sub ht).smul hv).add
            (ht.smul (continuous_subtype_val.comp (continuous_snd.comp hr)))).subtype_mk
        _)

@[simp]
private theorem
    Degree.Handle.interpolate_zero {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Space (N := N) (P := P)) :
    interpolate 0 z = z := by apply Prod.ext <;> apply Subtype.ext <;> simp [interpolate]

@[simp]
private theorem Degree.Handle.interpolate_one {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (z : Space (N := N) (P := P)) :
    interpolate 1 z = retraction z := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [interpolate]

private theorem
    Degree.Handle.interpolate_fixed {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] (t : (unitInterval)) (z : Space (N := N) (P := P))
    (hz : z ∈ faceCore) : interpolate t z = z := by
  have hr := retraction_eq_self z hz
  apply Prod.ext <;> apply Subtype.ext <;> simp [interpolate, hr, ← add_smul]

private def Degree.Handle.deformation {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (ContinuousMap.id (Space (N := N) (P := P))).HomotopyRel retraction faceCore
    where
  toFun tz := interpolate tz.1 tz.2
  continuous_toFun := continuous_interpolate
  map_zero_left := interpolate_zero
  map_one_left := interpolate_one
  prop' := interpolate_fixed

private abbrev
    Degree.CoreAttachment.Core {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P] :
    Set (Degree.Handle.Space (N := N) (P := P)) :=
  {z | (z.2 : P) = 0}

private abbrev
    Degree.CoreAttachment.Face {N P : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P] :
    Set (Degree.Handle.Space (N := N) (P := P)) :=
  {z | ‖(z.1 : N)‖ = 1}

private def
    Degree.CoreAttachment.faceDeformation {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (ContinuousMap.id (Degree.Handle.Space (N := N) (P := P))).HomotopyRel
      Degree.Handle.retraction Face
    where
  __ := Degree.Handle.deformation.toHomotopy
  prop' t z hz := Degree.Handle.interpolate_fixed t z (Or.inl hz)

private abbrev Degree.CoreAttachment.CoreUnion {N P M : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [TopologicalSpace M] (A : Set M)
    (h : C(Degree.Handle.Space (N := N) (P := P), M)) :=
  ↥(A ∪ h '' Core)

private def Degree.CoreAttachment.family {N P M : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N] [FiniteDimensional ℝ P]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Degree.Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) :
    C((unitInterval) × Degree.Attachment.Union A h, Degree.Attachment.Union A h) :=
  Degree.Attachment.unionFamily A Face h faceDeformation hinj hface

private theorem
    Degree.CoreAttachment.family_zero {N P M : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N] [FiniteDimensional ℝ P]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Degree.Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) (x : Degree.Attachment.Union A h) :
    family A h hinj hface (0, x) = x :=
  Degree.Attachment.unionFamily_zero A Face h faceDeformation hinj hface x

private theorem Degree.CoreAttachment.family_fixed_lower {N P M : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Degree.Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) (t : (unitInterval)) (a : A) :
    family A h hinj hface (t, ⟨a.val, Or.inl a.property⟩) = ⟨a.val, Or.inl a.property⟩ :=
  Degree.Attachment.unionFamily_fixed_lower A Face h faceDeformation hinj hface t a

private theorem Degree.CoreAttachment.family_on_handle {N P M : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Degree.Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) (t : (unitInterval))
    (z : Degree.Handle.Space (N := N) (P := P)) :
    (family A h hinj hface (t, ⟨h z, Or.inr ⟨z, rfl⟩⟩)).val = h (Degree.Handle.interpolate t z) :=
  Degree.Attachment.unionFamily_on_handle A Face h faceDeformation hinj hface t z

private theorem
    Degree.CoreAttachment.family_one_mem_coreUnion {N P M : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Degree.Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) (x : Degree.Attachment.Union A h) :
    (family A h hinj hface (1, x)).val ∈ A ∪ h '' Core := by
  rcases x with ⟨x, hx | ⟨z, rfl⟩⟩
  · have he := family_fixed_lower A h hinj hface 1 ⟨x, hx⟩
    exact Or.inl (congrArg Subtype.val he ▸ hx)
  · rw [family_on_handle, Degree.Handle.interpolate_one]
    rcases Degree.Handle.retraction_mem_faceCore z with hz | hz
    · exact Or.inl ((hface (Degree.Handle.retraction z)).mpr hz)
    · exact Or.inr ⟨Degree.Handle.retraction z, hz, rfl⟩

private def
    Degree.CoreAttachment.inclusion {N P M : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
    [TopologicalSpace M] (A : Set M) (h : C(Degree.Handle.Space (N := N) (P := P), M)) :
    C(CoreUnion A h, Degree.Attachment.Union A h) :=
  ⟨fun x =>
    ⟨x.val,
      x.property.elim Or.inl (fun hx => Or.inr (by obtain ⟨z, _, hz⟩ := hx; exact ⟨z, hz⟩))⟩,
    continuous_subtype_val.subtype_mk _⟩

private def Degree.CoreAttachment.reduce {N P M : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N] [FiniteDimensional ℝ P]
    [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Degree.Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) : C(Degree.Attachment.Union A h, CoreUnion A h) :=
  ⟨fun x => ⟨(family A h hinj hface (1, x)).val, family_one_mem_coreUnion A h hinj hface x⟩,
    ((continuous_subtype_val.comp (family A h hinj hface).continuous).comp
          (continuous_const.prodMk continuous_id)).subtype_mk
      _⟩

private theorem Degree.CoreAttachment.family_fixed_coreUnion {N P M : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Degree.Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) (t : (unitInterval)) (x : CoreUnion A h) :
    family A h hinj hface (t, Degree.CoreAttachment.inclusion A h x) =
      Degree.CoreAttachment.inclusion A h x := by
  rcases x with ⟨x, hx | ⟨z, hz, rfl⟩⟩
  · exact family_fixed_lower A h hinj hface t ⟨x, hx⟩
  · apply Subtype.ext
    change (family A h hinj hface (t, ⟨h z, Or.inr ⟨z, rfl⟩⟩)).val = h z
    rw [family_on_handle, Degree.Handle.interpolate_fixed t z (Or.inr hz)]

private def Degree.CoreAttachment.coreUnionHomotopyEquiv {N P M : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ N]
    [FiniteDimensional ℝ P] [TopologicalSpace M] [T2Space M] (A : Set M) [CompactSpace A]
    (h : C(Degree.Handle.Space (N := N) (P := P), M)) (hinj : Function.Injective h)
    (hface : ∀ z, h z ∈ A ↔ z ∈ Face) : CoreUnion A h ≃ₕ Degree.Attachment.Union A h
    where
  toFun := Degree.CoreAttachment.inclusion A h
  invFun := reduce A h hinj hface
  left_inv := by
    have he :
      (reduce A h hinj hface).comp (Degree.CoreAttachment.inclusion A h) =
        ContinuousMap.id (CoreUnion A h) := by
      apply ContinuousMap.ext
      intro x
      apply Subtype.ext
      change (family A h hinj hface (1, Degree.CoreAttachment.inclusion A h x)).val = x.val
      exact congrArg Subtype.val (family_fixed_coreUnion A h hinj hface 1 x)
    rw [he]
  right_inv := by
    let H :
      (ContinuousMap.id (Degree.Attachment.Union A h)).Homotopy
        ((Degree.CoreAttachment.inclusion A h).comp (reduce A h hinj hface)) :=
      { toContinuousMap := family A h hinj hface
        map_zero_left := family_zero A h hinj hface
        map_one_left := fun _ => rfl }
    exact ⟨H.symm⟩

private theorem
    Degree.MorseCells.core_dimension_le {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.NegativeCoordinates ≤ Module.finrank ℝ E := by
  classical
  change Module.finrank ℝ (EuclideanSpace ℝ (Smale.MorseHandle.Negative c.weights)) ≤ _
  rw [finrank_euclideanSpace]
  exact (Fintype.card_subtype_le (fun i => c.weights i = -1)).trans_eq (Fintype.card_fin _)

private def Degree.MorseCells.coreCellMap {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    C(Smale.MorseHandle.UnitDisk c.NegativeCoordinates, M) :=
  (c.attachingHandleMap ρ hρ hblock).comp
    ⟨fun u => (u, ⟨0, by simp⟩), continuous_id.prodMk continuous_const⟩

private theorem Degree.MorseCells.coreCellMap_injective {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    Function.Injective (coreCellMap c ρ hρ hblock) := by
  intro u v h
  exact congrArg Prod.fst (c.attachingHandleMap_injective ρ hρ hblock h)

private theorem Degree.MorseCells.coreCellMap_lower_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    (u : Smale.MorseHandle.UnitDisk c.NegativeCoordinates) :
    f (coreCellMap c ρ hρ hblock u) ≤ f p - ρ ^ 2 ↔ ‖(u : c.NegativeCoordinates)‖ = 1 :=
  c.attachingHandleMap_lower_iff ρ hρ hblock (u, ⟨0, by simp⟩)

private theorem Degree.MorseCells.image_core {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target) :
    (c.attachingHandleMap ρ hρ hblock) '' Degree.CoreAttachment.Core =
      Set.range (coreCellMap c ρ hρ hblock) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.1, ?_⟩
    apply congrArg (c.attachingHandleMap ρ hρ hblock)
    exact Prod.ext rfl (Subtype.ext hz.symm)
  · rintro ⟨u, rfl⟩
    exact ⟨(u, ⟨0, by simp⟩), rfl, rfl⟩

private def Degree.MorseCells.cellHandleHomotopyEquiv {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p) (ρ : ℝ) (hρ : 0 < ρ)
    (hblock :
      Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
          Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
        c.splitChart.target)
    [T2Space M] [CompactSpace M] (hf : Continuous f) :
    Smale.ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
        {u : Smale.MorseHandle.UnitDisk c.NegativeCoordinates | ‖(u : c.NegativeCoordinates)‖ = 1}
        (coreCellMap c ρ hρ hblock) ≃ₕ
      Smale.ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
        {z | ‖(z.1 : c.NegativeCoordinates)‖ = 1} (c.attachingHandleMap ρ hρ hblock) := by
  let A := {x : M | f x ≤ f p - ρ ^ 2}
  have hA : IsCompact A := (isClosed_le hf continuous_const).isCompact
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let cell :=
    Smale.ClosedAttachment.unionHomeomorph A _ (coreCellMap c ρ hρ hblock) hA
      (coreCellMap_injective c ρ hρ hblock) (coreCellMap_lower_iff c ρ hρ hblock)
  let core :=
    Degree.CoreAttachment.coreUnionHomotopyEquiv A (c.attachingHandleMap ρ hρ hblock)
      (c.attachingHandleMap_injective ρ hρ hblock) (c.attachingHandleMap_lower_iff ρ hρ hblock)
  let mark := Homeomorph.setCongr (congrArg (fun S : Set M => A ∪ S) (image_core c ρ hρ hblock))
  exact
    cell.toHomotopyEquiv.trans
      (mark.symm.toHomotopyEquiv.trans
        (core.trans (c.attachingHandleUnionHomeomorph hf ρ hρ hblock).symm.toHomotopyEquiv))

private inductive Degree.FiniteCells.Built (d : ℕ) : (X : Type) → [TopologicalSpace X] → Prop
  | empty (X : Type) [TopologicalSpace X] [IsEmpty X] : Built d X
  |
  equiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (h : Built d X) :
    Built d Y
  |
  attach {V M : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [TopologicalSpace M] (A : Set M) (h : C(Smale.MorseHandle.UnitDisk V, M))
    (hboundary : ∀ u : Smale.MorseHandle.UnitDisk V, ‖(u : V)‖ = 1 → h u ∈ A)
    (hdim : Module.finrank ℝ V ≤ d) (hA : Built d A) :
    Built d (Smale.ClosedAttachment.Space A {u : Smale.MorseHandle.UnitDisk V | ‖(u : V)‖ = 1} h)

private def
    Degree.AttachmentMaps.oldInclusion {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) : C(A, Smale.ClosedAttachment.Space A B h) :=
  ⟨fun a => Quot.mk _ (.inl a), continuous_quot_mk.comp continuous_inl⟩

private def
    Degree.AttachmentMaps.cellInclusion {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) : C(K, Smale.ClosedAttachment.Space A B h) :=
  ⟨fun k => Quot.mk _ (.inr k), continuous_quot_mk.comp continuous_inr⟩

private theorem
    Degree.AttachmentMaps.boundary_eq {K M : Type*} [TopologicalSpace K] [TopologicalSpace M]
    (A : Set M) (B : Set K) (h : C(K, M)) (a : A) (k : K) (hk : k ∈ B) (ha : a.val = h k) :
    oldInclusion A B h a = cellInclusion A B h k :=
  Quot.sound ⟨hk, ha⟩

private theorem Degree.AttachmentMaps.sum_respects {K M X : Type*} [TopologicalSpace K]
    [TopologicalSpace M] [TopologicalSpace X] (A : Set M) (B : Set K) (h : C(K, M)) (f : C(A, X))
    (g : C(K, X)) (hc : ∀ a k, k ∈ B → a.val = h k → f a = g k) (a b : A ⊕ K)
    (hab : Smale.ClosedAttachment.Rel A B h a b) : Sum.elim f g a = Sum.elim f g b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact hab.elim
    | inr k => exact hc a k hab.1 hab.2
  | inr k => cases b <;> exact hab.elim

private def Degree.AttachmentMaps.glue {K M X : Type*} [TopologicalSpace K] [TopologicalSpace M]
    [TopologicalSpace X] (A : Set M) (B : Set K) (h : C(K, M)) (f : C(A, X)) (g : C(K, X))
    (hc : ∀ a k, k ∈ B → a.val = h k → f a = g k) : C(Smale.ClosedAttachment.Space A B h, X)
    where
  toFun := Quot.lift (Sum.elim f g) (sum_respects A B h f g hc)
  continuous_toFun := continuous_quot_lift _ (continuous_sum_dom.mpr ⟨f.continuous, g.continuous⟩)

private def Degree.AttachmentMaps.familyOld {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
    (A : Set M) (F : C((unitInterval) × A, X)) (t : (unitInterval)) : C(A, X) :=
  F.comp ⟨fun a => (t, a), continuous_const.prodMk continuous_id⟩

private def Degree.AttachmentMaps.familyCell {K X : Type*} [TopologicalSpace K] [TopologicalSpace X]
    (G : C((unitInterval) × K, X)) (t : (unitInterval)) : C(K, X) :=
  G.comp ⟨fun k => (t, k), continuous_const.prodMk continuous_id⟩

private def
    Degree.AttachmentMaps.glueFamily {K M X : Type*} [TopologicalSpace K] [TopologicalSpace M]
    [TopologicalSpace X] (A : Set M) (B : Set K) (h : C(K, M)) (F : C((unitInterval) × A, X))
    (G : C((unitInterval) × K, X)) (hFG : ∀ t a k, k ∈ B → a.val = h k → F (t, a) = G (t, k)) :
    C((unitInterval) × Smale.ClosedAttachment.Space A B h, X)
    where
  toFun p := glue A B h (familyOld A F p.1) (familyCell G p.1) (hFG p.1) p.2
  continuous_toFun := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    have hc :
      Continuous (fun p : ((unitInterval) × A) ⊕ ((unitInterval) × K) => Sum.elim F G p) :=
      continuous_sum_dom.mpr ⟨F.continuous, G.continuous⟩
    convert hc.comp (Homeomorph.prodSumDistrib : (unitInterval) × (A ⊕ K) ≃ₜ _).continuous using 1
    funext p
    rcases p with ⟨t, a | k⟩ <;> rfl

private def
    Degree.FiniteCells.RelativeDiskLifting {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X, Y)) (d : ℕ) : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Module.finrank ℝ V ≤ d →
      ∀ (a : C(Degree.DiskCylinder.Sphere (E := V), X))
        (u : C(Degree.DiskCylinder.Disk (E := V), Y))
        (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), Y)),
        (∀ s, H (0, s) = F (a s)) →
          (∀ s, H (1, s) = u (Degree.DiskCylinder.boundaryToDisk s)) →
            ∃ (v : C(Degree.DiskCylinder.Disk (E := V), X)) (G :
              C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y)),
              (∀ s, v (Degree.DiskCylinder.boundaryToDisk s) = a s) ∧
                (∀ z, G (0, z) = F (v z)) ∧
                  (∀ z, G (1, z) = u z) ∧
                    ∀ t s, G (t, Degree.DiskCylinder.boundaryToDisk s) = H (t, s)

private def Degree.FiniteCells.MapsLift {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X, Y)) (Z : Type) [TopologicalSpace Z] : Prop :=
  ∀ u : C(Z, Y), ∃ v : C(Z, X), (F.comp v).Homotopic u

private theorem
    Degree.FiniteCells.mapsLift_empty {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X, Y)) (Z : Type) [TopologicalSpace Z] [IsEmpty Z] : MapsLift F Z := by
  intro u
  let v : C(Z, X) := ⟨isEmptyElim, continuous_iff_continuousAt.mpr (fun z => isEmptyElim z)⟩
  refine ⟨v, ?_⟩
  have he : F.comp v = u := ContinuousMap.ext (fun z => isEmptyElim z)
  rw [he]

private theorem
    Degree.FiniteCells.mapsLift_equiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X, Y)) {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W] (e : Z ≃ₕ W)
    (h : MapsLift F Z) : MapsLift F W := by
  intro u
  obtain ⟨v, hv⟩ := h (u.comp e.toFun)
  refine ⟨v.comp e.invFun, ?_⟩
  have h₁ := hv.comp (ContinuousMap.Homotopic.refl e.invFun)
  have h₂ := (ContinuousMap.Homotopic.refl u).comp e.right_inv
  simpa only [ContinuousMap.comp_assoc, ContinuousMap.comp_id] using h₁.trans h₂

private theorem
    Degree.FiniteCells.mapsLift_attach {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (F : C(X, Y)) {d : ℕ} (hF : RelativeDiskLifting F d) {V M : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace M] (A : Set M)
    (h : C(Smale.MorseHandle.UnitDisk V, M))
    (hb : ∀ z : Smale.MorseHandle.UnitDisk V, ‖(z : V)‖ = 1 → h z ∈ A)
    (hd : Module.finrank ℝ V ≤ d) (hA : MapsLift F A) :
    MapsLift F
      (Smale.ClosedAttachment.Space A {z : Smale.MorseHandle.UnitDisk V | ‖(z : V)‖ = 1} h) := by
  intro u
  let B : Set (Smale.MorseHandle.UnitDisk V) := {z | ‖(z : V)‖ = 1}
  let iA := Degree.AttachmentMaps.oldInclusion A B h
  let iD := Degree.AttachmentMaps.cellInclusion A B h
  obtain ⟨vA, ⟨HA⟩⟩ := hA (u.comp iA)
  let b : C(Degree.DiskCylinder.Sphere (E := V), A) :=
    ⟨fun s =>
      ⟨h (Degree.DiskCylinder.boundaryToDisk s),
        hb (Degree.DiskCylinder.boundaryToDisk s) (mem_sphere_zero_iff_norm.mp s.property)⟩,
      (h.continuous.comp Degree.DiskCylinder.boundaryToDisk.continuous).subtype_mk _⟩
  let H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), Y) :=
    HA.toContinuousMap.comp ((ContinuousMap.id (unitInterval)).prodMap b)
  have h0 : ∀ s, H (0, s) = F ((vA.comp b) s) := fun s => HA.map_zero_left (b s)
  have h1 : ∀ s, H (1, s) = (u.comp iD) (Degree.DiskCylinder.boundaryToDisk s) := by
    intro s
    change HA (1, b s) = u (iD (Degree.DiskCylinder.boundaryToDisk s))
    exact
      (HA.map_one_left (b s)).trans
        (congrArg u
          (Degree.AttachmentMaps.boundary_eq A B h (b s) (Degree.DiskCylinder.boundaryToDisk s)
            (mem_sphere_zero_iff_norm.mp s.property) rfl))
  obtain ⟨vD, GD, hvD, hGD0, hGD1, hGDside⟩ := hF V hd (vA.comp b) (u.comp iD) H h0 h1
  have hcompat : ∀ a z, z ∈ B → a.val = h z → vA a = vD z := by
    intro a z hz ha
    let s : Degree.DiskCylinder.Sphere (E := V) := ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
    have hab : a = b s := Subtype.ext ha
    exact (congrArg vA hab).trans (hvD s).symm
  let v := Degree.AttachmentMaps.glue A B h vA vD hcompat
  have hhom : ∀ t a z, z ∈ B → a.val = h z → HA (t, a) = GD (t, z) := by
    intro t a z hz ha
    let s : Degree.DiskCylinder.Sphere (E := V) := ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
    have hab : a = b s := Subtype.ext ha
    exact (congrArg (fun a => HA (t, a)) hab).trans (hGDside t s).symm
  refine
    ⟨v, ⟨{
          toContinuousMap := Degree.AttachmentMaps.glueFamily A B h HA.toContinuousMap GD hhom
          map_zero_left := ?_
          map_one_left := ?_ }⟩⟩
  · intro z
    induction z using Quot.inductionOn with
    | _ z =>
      cases z with
      | inl a => exact HA.map_zero_left a
      | inr z => exact hGD0 z
  · intro z
    induction z using Quot.inductionOn with
    | _ z =>
      cases z with
      | inl a => exact HA.map_one_left a
      | inr z => exact hGD1 z

private theorem Degree.FiniteCells.mapsLift_of_built {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (F : C(X, Y)) {d : ℕ} (hF : RelativeDiskLifting F d) {Z : Type}
    [TopologicalSpace Z] (hZ : Built d Z) : MapsLift F Z := by
  induction hZ with
  | empty Z => exact mapsLift_empty F Z
  | equiv e _ ih => exact mapsLift_equiv F e ih
  | attach A h hb hd _ ih => exact mapsLift_attach F hF A h hb hd ih

private theorem Degree.LowCellLifting.relativeDiskLifting_five {Y : Type} [TopologicalSpace Y]
    [PathConnectedSpace Y] (F : C(SixSphereCube.StandardSphere, Y))
    (hpi : ∀ n, 0 < n → n < 6 → ∀ y : Y, Subsingleton (π_ n Y y)) :
    Degree.FiniteCells.RelativeDiskLifting F 5 := by
  intro V _ _ _ hd a u H h0 h1
  obtain ⟨v, hv, _⟩ :=
    Degree.Sphere.exists_boundary_extension (hd.trans (by decide)) a SixSphereCube.sphereBasePoint
  have h0' : ∀ s, H (0, s) = (F.comp v) (Degree.DiskCylinder.boundaryToDisk s) := by
    intro s
    exact (h0 s).trans (congrArg F (hv s).symm)
  obtain ⟨G, hG0, hG1, hGside⟩ :=
    Degree.CylinderFilling.exists_filling hpi (by omega : Module.finrank ℝ V + 1 ≤ 6) (F.comp v) u
      H h0' h1 (F SixSphereCube.sphereBasePoint)
  exact ⟨v, G, hv, hG0, hG1, hGside⟩

attribute [local instance] SpecialPeriods.Threefold.space_simplyConnected in
private theorem Degree.LowCellLifting.threefold_pi_subsingleton {n : ℕ} (hn : 0 < n) (hn6 : n < 6)
    (x : SpecialPeriods.Threefold.Space) : Subsingleton (π_ n SpecialPeriods.Threefold.Space x) :=
  by
  have hn5 : n ≤ 5 := by omega
  interval_cases n
  · exact (HomotopyGroup.pi1EquivFundamentalGroup).injective.subsingleton
  · exact SpecialPeriods.Threefold.HomotopyTwo.piTwo_subsingleton x
  · exact SpecialPeriods.Threefold.HomotopyThree.piThree_subsingleton x
  · exact SpecialPeriods.Threefold.HomotopyFour.piFour_subsingleton x
  · exact SpecialPeriods.Threefold.HomotopyFive.piFive_subsingleton x

attribute [local instance] SpecialPeriods.Threefold.space_simplyConnected in
private theorem Degree.LowCellLifting.sphereMap_relativeDiskLifting_five
    (x : SpecialPeriods.Threefold.Space) :
    Degree.FiniteCells.RelativeDiskLifting
      (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x) 5 :=
  relativeDiskLifting_five _ (fun _ hn hn6 => threefold_pi_subsingleton hn hn6)

private def Degree.MappingPaths.ofHomotopy {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {f g : C(A, B)} (H : f.Homotopy g) : Path f g
    where
  toContinuousMap := H.curry
  source' := H.curry_zero
  target' := H.curry_one

private def Degree.MappingPaths.toHomotopy {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [LocallyCompactSpace A] {f g : C(A, B)} (p : Path f g) : f.Homotopy g
    where
  toContinuousMap := p.toContinuousMap.uncurry
  map_zero_left a := ContinuousMap.congr_fun p.source a
  map_one_left a := ContinuousMap.congr_fun p.target a

private def
    Degree.MappingPaths.Over {A B : Type*} [TopologicalSpace A] [TopologicalSpace B] {a₀ a₁ : A}
    {b₀ b₁ : B} (r : A → B) (p : Path a₀ a₁) (q : Path b₀ b₁) : Prop :=
  ∀ t, r (p t) = q t

private theorem
    Degree.MappingPaths.Over.symm {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a₀ a₁ : A} {b₀ b₁ : B} {r : A → B} {p : Path a₀ a₁} {q : Path b₀ b₁}
    (h : Degree.MappingPaths.Over r p q) : Degree.MappingPaths.Over r p.symm q.symm := fun t =>
  h (unitInterval.symm t)

private theorem
    Degree.MappingPaths.Over.trans {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    {a₀ a₁ a₂ : A} {b₀ b₁ b₂ : B} {r : A → B} {p₀ : Path a₀ a₁} {p₁ : Path a₁ a₂}
    {q₀ : Path b₀ b₁} {q₁ : Path b₁ b₂} (h₀ : Degree.MappingPaths.Over r p₀ q₀)
    (h₁ : Degree.MappingPaths.Over r p₁ q₁) :
    Degree.MappingPaths.Over r (p₀.trans p₁) (q₀.trans q₁) := by
  intro t
  simp only [Path.trans_apply]
  split_ifs <;>
    first
    | exact h₀ _
    | exact h₁ _

private theorem Degree.MappingPaths.normalization_cancellation {B : Type*} [TopologicalSpace B]
    {b₀ b₁ b₂ : B} (a : Path b₀ b₁) (h : Path b₁ b₂) :
    (a.symm.trans ((Path.refl b₀).trans ((h.symm.trans a.symm).symm))).Homotopic h := by
  rw [Path.trans_symm, Path.symm_symm, Path.symm_symm]
  have hunit := Path.Homotopic.refl_trans (a.trans h)
  have hfirst := (Path.Homotopic.refl a.symm).hcomp hunit
  have hassoc := (Path.Homotopic.trans_assoc a.symm a h).symm
  have hcancel := (Path.Homotopic.symm_trans a).hcomp (Path.Homotopic.refl h)
  exact hfirst.trans (hassoc.trans (hcancel.trans (Path.Homotopic.refl_trans h)))

private theorem Degree.BoundaryPathTransport.exists_transport {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f : C(Degree.DiskCylinder.Disk (E := V), Y))
    {a b : C(Degree.DiskCylinder.Sphere (E := V), Y)} (A : Path a b)
    (ha : f.comp Degree.DiskCylinder.boundaryToDisk = a) :
    ∃ g : C(Degree.DiskCylinder.Disk (E := V), Y),
      ∃ P : Path f g,
        Degree.MappingPaths.Over
            (fun v : C(Degree.DiskCylinder.Disk (E := V), Y) =>
              v.comp Degree.DiskCylinder.boundaryToDisk)
            P A ∧
          g.comp Degree.DiskCylinder.boundaryToDisk = b := by
  let H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), Y) := A.toContinuousMap.uncurry
  have h0 : ∀ s, H (0, s) = f (Degree.DiskCylinder.boundaryToDisk s) := by
    intro s
    exact (ContinuousMap.congr_fun A.source s).trans (ContinuousMap.congr_fun ha.symm s)
  let g := Degree.DiskCylinder.extensionEndpoint f H h0
  let P := Degree.MappingPaths.ofHomotopy (Degree.DiskCylinder.extensionHomotopy f H h0)
  have hP :
    Degree.MappingPaths.Over
      (fun v : C(Degree.DiskCylinder.Disk (E := V), Y) =>
        v.comp Degree.DiskCylinder.boundaryToDisk)
      P A := by
    intro t
    apply ContinuousMap.ext
    intro s
    exact Degree.DiskCylinder.extend_side f H h0 t s
  refine ⟨g, P, hP, ?_⟩
  simpa using hP 1

private def Degree.CylinderBoundaryFamilies.bottomFamily {V Y : Type*} [NormedAddCommGroup V]
    [TopologicalSpace Y] (f : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y)) :
    C(Degree.DiskCylinder.Disk (E := V), C((unitInterval), Y)) :=
  (f.comp ContinuousMap.prodSwap).curry

private def Degree.CylinderBoundaryFamilies.topFamily {V Y : Type*} [NormedAddCommGroup V]
    [TopologicalSpace Y] (g : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y)) :
    C(Degree.DiskCylinder.Disk (E := V), C((unitInterval), Y)) :=
  (g.comp ContinuousMap.prodSwap).curry

private def Degree.CylinderBoundaryFamilies.sideFamily {V Y : Type*} [NormedAddCommGroup V]
    [TopologicalSpace Y]
    (H : C((unitInterval) × ((unitInterval) × Degree.DiskCylinder.Sphere (E := V)), Y)) :
    C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), C((unitInterval), Y)) :=
  (H.comp ContinuousMap.prodSwap).curry

private def
    Degree.CylinderBoundaryFamilies.glued {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f g : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y))
    (H : C((unitInterval) × ((unitInterval) × Degree.DiskCylinder.Sphere (E := V)), Y))
    (h0 : ∀ t s, H (t, 0, s) = f (t, Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ t s, H (t, 1, s) = g (t, Degree.DiskCylinder.boundaryToDisk s)) :
    C((unitInterval) × Degree.CylinderBall.boundary (V := V), Y) :=
  (Degree.CylinderBoundary.glued (bottomFamily f) (topFamily g) (sideFamily H)
        (fun s => ContinuousMap.ext (fun t => h0 t s))
        (fun s => ContinuousMap.ext (fun t => h1 t s))).uncurry.comp
    ContinuousMap.prodSwap

private theorem Degree.CylinderBoundaryFamilies.glued_bottom {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f g : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y))
    (H : C((unitInterval) × ((unitInterval) × Degree.DiskCylinder.Sphere (E := V)), Y))
    (h0 : ∀ t s, H (t, 0, s) = f (t, Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ t s, H (t, 1, s) = g (t, Degree.DiskCylinder.boundaryToDisk s)) (t : (unitInterval))
    (z : Degree.DiskCylinder.Disk (E := V)) :
    glued f g H h0 h1 (t, Degree.CylinderBoundary.lower (Degree.DiskCylinder.bottomMap z)) =
      f (t, z) :=
  ContinuousMap.congr_fun
    (Degree.CylinderBoundary.glued_bottom (bottomFamily f) (topFamily g) (sideFamily H)
      (fun s => ContinuousMap.ext (fun t => h0 t s))
      (fun s => ContinuousMap.ext (fun t => h1 t s)) z)
    t

private theorem Degree.CylinderBoundaryFamilies.glued_top {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f g : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y))
    (H : C((unitInterval) × ((unitInterval) × Degree.DiskCylinder.Sphere (E := V)), Y))
    (h0 : ∀ t s, H (t, 0, s) = f (t, Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ t s, H (t, 1, s) = g (t, Degree.DiskCylinder.boundaryToDisk s)) (t : (unitInterval))
    (z : Degree.DiskCylinder.Disk (E := V)) :
    glued f g H h0 h1 (t, Degree.CylinderBoundary.top z) = g (t, z) :=
  ContinuousMap.congr_fun
    (Degree.CylinderBoundary.glued_top (bottomFamily f) (topFamily g) (sideFamily H)
      (fun s => ContinuousMap.ext (fun t => h0 t s))
      (fun s => ContinuousMap.ext (fun t => h1 t s)) z)
    t

private theorem Degree.CylinderBoundaryFamilies.glued_side {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f g : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y))
    (H : C((unitInterval) × ((unitInterval) × Degree.DiskCylinder.Sphere (E := V)), Y))
    (h0 : ∀ t s, H (t, 0, s) = f (t, Degree.DiskCylinder.boundaryToDisk s))
    (h1 : ∀ t s, H (t, 1, s) = g (t, Degree.DiskCylinder.boundaryToDisk s)) (t r : (unitInterval))
    (s : Degree.DiskCylinder.Sphere (E := V)) :
    glued f g H h0 h1 (t, Degree.CylinderBoundary.lower (Degree.DiskCylinder.sideMap (r, s))) =
      H (t, r, s) :=
  ContinuousMap.congr_fun
    (Degree.CylinderBoundary.glued_side (bottomFamily f) (topFamily g) (sideFamily H)
      (fun s => ContinuousMap.ext (fun t => h0 t s))
      (fun s => ContinuousMap.ext (fun t => h1 t s)) r s)
    t

private theorem
    Degree.CylinderHEP.exists_extension {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace Y]
    (f : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y))
    (J : C((unitInterval) × Degree.CylinderBall.boundary (V := V), Y))
    (h0 : ∀ p, J (0, p) = f p.val) :
    ∃ K : C((unitInterval) × ((unitInterval) × Degree.DiskCylinder.Disk (E := V)), Y),
      (∀ p, K (0, p) = f p) ∧
        ∀ (t : (unitInterval)) (p : Degree.CylinderBall.boundary (V := V)),
          K (t, p.val) = J (t, p) := by
  let e := Degree.CylinderBall.homeomorph (V := V)
  let b := Degree.CylinderBall.boundaryHomeomorph (V := V)
  let f' : C(Degree.DiskCylinder.Disk (E := ℝ × V), Y) := f.comp (e.symm : C(_, _))
  let J' : C((unitInterval) × Degree.DiskCylinder.Sphere (E := ℝ × V), Y) :=
    J.comp ((ContinuousMap.id (unitInterval)).prodMap (b.symm : C(_, _)))
  have h0' : ∀ s, J' (0, s) = f' (Degree.DiskCylinder.boundaryToDisk s) := fun s => h0 (b.symm s)
  let H := Degree.DiskCylinder.extend f' J' h0'
  let K : C((unitInterval) × ((unitInterval) × Degree.DiskCylinder.Disk (E := V)), Y) :=
    H.comp ((ContinuousMap.id (unitInterval)).prodMap (e : C(_, _)))
  refine ⟨K, ?_, ?_⟩
  · intro p
    change H (0, e p) = f p
    exact
      (Degree.DiskCylinder.extend_bottom f' J' h0' (e p)).trans
        (congrArg f (e.symm_apply_apply p))
  · intro t p
    change H (t, Degree.DiskCylinder.boundaryToDisk (b p)) = J (t, p)
    exact
      (Degree.DiskCylinder.extend_side f' J' h0' t (b p)).trans
        (congrArg (fun p => J (t, p)) (b.symm_apply_apply p))

private theorem Degree.SideRectification.boundary_cases {V : Type*} [NormedAddCommGroup V]
    (p : Degree.CylinderBall.boundary (V := V)) :
    (∃ z, p = Degree.CylinderBoundary.lower (Degree.DiskCylinder.bottomMap z)) ∨
      (∃ z, p = Degree.CylinderBoundary.top z) ∨
        ∃ t s, p = Degree.CylinderBoundary.lower (Degree.DiskCylinder.sideMap (t, s)) := by
  rcases p with ⟨⟨t, z⟩, ht | ht | hz⟩
  · change t = 0 at ht
    subst t
    exact Or.inl ⟨z, rfl⟩
  · change t = 1 at ht
    subst t
    exact Or.inr (Or.inl ⟨z, rfl⟩)
  · exact Or.inr (Or.inr ⟨t, ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩, rfl⟩)

private theorem Degree.SideRectification.exists_rectification {V Y : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace Y]
    {f g : C(Degree.DiskCylinder.Disk (E := V), Y)} (P : Path f g)
    {a b : C(Degree.DiskCylinder.Sphere (E := V), Y)} (Q H : Path a b)
    (hP :
      Degree.MappingPaths.Over
        (fun v : C(Degree.DiskCylinder.Disk (E := V), Y) =>
          v.comp Degree.DiskCylinder.boundaryToDisk)
        P Q)
    (hQ : Q.Homotopic H) :
    ∃ G : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y),
      (∀ z, G (0, z) = f z) ∧
        (∀ z, G (1, z) = g z) ∧ ∀ t s, G (t, Degree.DiskCylinder.boundaryToDisk s) = H t s := by
  obtain ⟨K⟩ := hQ
  have hfa : f.comp Degree.DiskCylinder.boundaryToDisk = a := by simpa using hP 0
  have hgb : g.comp Degree.DiskCylinder.boundaryToDisk = b := by simpa using hP 1
  let side : C((unitInterval) × ((unitInterval) × Degree.DiskCylinder.Sphere (E := V)), Y) :=
    K.toHomotopy.toContinuousMap.uncurry.comp
      ((Homeomorph.prodAssoc (unitInterval) (unitInterval)
            (Degree.DiskCylinder.Sphere (E := V))).symm :
        C(_, _))
  let fb : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y) := f.comp ContinuousMap.snd
  let gt : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y) := g.comp ContinuousMap.snd
  have hs0 : ∀ t s, side (t, 0, s) = fb (t, Degree.DiskCylinder.boundaryToDisk s) := by
    intro t s
    have he : K (t, 0) = a := (K.eq_fst t (by simp)).trans Q.source
    exact (congrArg (fun v => v s) he).trans (ContinuousMap.congr_fun hfa.symm s)
  have hs1 : ∀ t s, side (t, 1, s) = gt (t, Degree.DiskCylinder.boundaryToDisk s) := by
    intro t s
    have he : K (t, 1) = b := (K.eq_fst t (by simp)).trans Q.target
    exact (congrArg (fun v => v s) he).trans (ContinuousMap.congr_fun hgb.symm s)
  let J := Degree.CylinderBoundaryFamilies.glued fb gt side hs0 hs1
  have hJ0 :
    ∀ p : Degree.CylinderBall.boundary (V := V),
      J (0, p) = Degree.MappingPaths.toHomotopy P p.val := by
    intro p
    rcases boundary_cases p with ⟨z, rfl⟩ | ⟨z, rfl⟩ | ⟨t, s, rfl⟩
    · exact
        (Degree.CylinderBoundaryFamilies.glued_bottom fb gt side hs0 hs1 0 z).trans
          (ContinuousMap.congr_fun P.source z).symm
    · exact
        (Degree.CylinderBoundaryFamilies.glued_top fb gt side hs0 hs1 0 z).trans
          (ContinuousMap.congr_fun P.target z).symm
    · exact
        (Degree.CylinderBoundaryFamilies.glued_side fb gt side hs0 hs1 0 t s).trans
          ((congrArg (fun v => v s) (K.apply_zero t)).trans
            (ContinuousMap.congr_fun (hP t) s).symm)
  obtain ⟨W, _, hW⟩ :=
    Degree.CylinderHEP.exists_extension (Degree.MappingPaths.toHomotopy P).toContinuousMap J hJ0
  let G : C((unitInterval) × Degree.DiskCylinder.Disk (E := V), Y) :=
    W.comp ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z
    exact
      (hW 1 (Degree.CylinderBoundary.lower (Degree.DiskCylinder.bottomMap z))).trans
        (Degree.CylinderBoundaryFamilies.glued_bottom fb gt side hs0 hs1 1 z)
  · intro z
    exact
      (hW 1 (Degree.CylinderBoundary.top z)).trans
        (Degree.CylinderBoundaryFamilies.glued_top fb gt side hs0 hs1 1 z)
  · intro t s
    exact
      (hW 1 (Degree.CylinderBoundary.lower (Degree.DiskCylinder.sideMap (t, s)))).trans
        ((Degree.CylinderBoundaryFamilies.glued_side fb gt side hs0 hs1 1 t s).trans
          (congrArg (fun v => v s) (K.apply_one t)))

private theorem Degree.TopCellLifting.exists_top_disk_lift {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (x : SpecialPeriods.Threefold.Space)
    (L : V ≃L[ℝ] (Fin 6 → ℝ)) (hd : Module.finrank ℝ V ≤ 6)
    (a : C(Degree.DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere))
    (u : C(Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space))
    (H : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), SpecialPeriods.Threefold.Space))
    (h0 : ∀ s, H (0, s) = SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x (a s))
    (h1 : ∀ s, H (1, s) = u (Degree.DiskCylinder.boundaryToDisk s)) :
    ∃ (v : C(Degree.DiskCylinder.Disk (E := V), SixSphereCube.StandardSphere)) (G :
      C((unitInterval) × Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space)),
      (∀ s, v (Degree.DiskCylinder.boundaryToDisk s) = a s) ∧
        (∀ z, G (0, z) = SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x (v z)) ∧
          (∀ z, G (1, z) = u z) ∧ ∀ t s, G (t, Degree.DiskCylinder.boundaryToDisk s) = H (t, s) :=
  by
  let F := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
  let c : C(Degree.DiskCylinder.Sphere (E := V), SixSphereCube.StandardSphere) :=
    ContinuousMap.const _ SixSphereCube.sphereBasePoint
  obtain ⟨Ac⟩ := (Degree.Sphere.boundary_homotopic_const hd a SixSphereCube.sphereBasePoint).symm
  let A : Path c a := Degree.MappingPaths.ofHomotopy Ac
  let FA : Path (F.comp c) (F.comp a) := A.map (ContinuousMap.continuous_postcomp F)
  let HP : Path (F.comp a) (u.comp Degree.DiskCylinder.boundaryToDisk) :=
    { toContinuousMap := H.curry
      source' := ContinuousMap.ext h0
      target' := ContinuousMap.ext h1 }
  let K := HP.symm.trans FA.symm
  obtain ⟨u₀, E, hE, hu₀⟩ := Degree.BoundaryPathTransport.exists_transport u K rfl
  have hu₀' :
    ∀ z : Degree.DiskCylinder.Disk (E := V),
      ‖(z : V)‖ = 1 → u₀ z = F SixSphereCube.sphereBasePoint := by
    intro z hz
    exact ContinuousMap.congr_fun hu₀ ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩
  obtain ⟨p, hp, ⟨B⟩⟩ := Degree.BasedDiskLifting.exists_based_disk_lift x L u₀ hu₀'
  have hp' : p.comp Degree.DiskCylinder.boundaryToDisk = c := by
    apply ContinuousMap.ext
    intro s
    exact hp (Degree.DiskCylinder.boundaryToDisk s) (mem_sphere_zero_iff_norm.mp s.property)
  obtain ⟨v, P, hP, hv⟩ := Degree.BoundaryPathTransport.exists_transport p A hp'
  let FP : Path (F.comp p) (F.comp v) := P.map (ContinuousMap.continuous_postcomp F)
  let BP := Degree.MappingPaths.ofHomotopy B.toHomotopy
  have hFP :
    Degree.MappingPaths.Over
      (fun w : C(Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space) =>
        w.comp Degree.DiskCylinder.boundaryToDisk)
      FP FA := by
    intro t
    apply ContinuousMap.ext
    intro s
    exact congrArg F (ContinuousMap.congr_fun (hP t) s)
  have hBP :
    Degree.MappingPaths.Over
      (fun w : C(Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space) =>
        w.comp Degree.DiskCylinder.boundaryToDisk)
      BP (Path.refl (F.comp c)) := by
    intro t
    apply ContinuousMap.ext
    intro s
    have hs : ‖(Degree.DiskCylinder.boundaryToDisk s : V)‖ = 1 :=
      mem_sphere_zero_iff_norm.mp s.property
    exact (B.eq_fst t hs).trans (congrArg F (hp (Degree.DiskCylinder.boundaryToDisk s) hs))
  let R := FP.symm.trans (BP.trans E.symm)
  let Q := FA.symm.trans ((Path.refl (F.comp c)).trans K.symm)
  have hR :
    Degree.MappingPaths.Over
      (fun w : C(Degree.DiskCylinder.Disk (E := V), SpecialPeriods.Threefold.Space) =>
        w.comp Degree.DiskCylinder.boundaryToDisk)
      R Q :=
    hFP.symm.trans (hBP.trans hE.symm)
  have hQ : Q.Homotopic HP := Degree.MappingPaths.normalization_cancellation FA HP
  obtain ⟨G, hG0, hG1, hGside⟩ := Degree.SideRectification.exists_rectification R Q HP hR hQ
  exact ⟨v, G, fun s => ContinuousMap.congr_fun hv s, hG0, hG1, hGside⟩

private theorem Degree.TopCellLifting.sphereMap_relativeDiskLifting_six
    (x : SpecialPeriods.Threefold.Space) :
    Degree.FiniteCells.RelativeDiskLifting
      (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x) 6 := by
  intro V _ _ _ hd a u H h0 h1
  by_cases hlow : Module.finrank ℝ V ≤ 5
  · exact Degree.LowCellLifting.sphereMap_relativeDiskLifting_five x V hlow a u H h0 h1
  · have heq : Module.finrank ℝ V = 6 := by omega
    obtain ⟨L⟩ :=
      FiniteDimensional.nonempty_continuousLinearEquiv_of_finrank_eq
        (show Module.finrank ℝ V = Module.finrank ℝ (Fin 6 → ℝ) by simpa using heq)
    exact exists_top_disk_lift x L hd a u H h0 h1

private theorem
    Degree.MorseCells.exists_morse_cell_attachment_lt {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f) {p : M}
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hunique : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x = f p → x = p) {R : ℝ}
    (hR : 0 < R) :
    ∃ (ρ : ℝ) (hρ : 0 < ρ),
      ρ < R ∧
        ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) f p,
          ∃ hblock :
            Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
                Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
              c.splitChart.target,
            (∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
                f x ∈ Set.Icc (f p - ρ ^ 2) (f p + ρ ^ 2) → x = p) ∧
              Module.finrank ℝ c.NegativeCoordinates ≤ Module.finrank ℝ E ∧
                Nonempty
                  (Smale.ClosedAttachment.Space {x : M | f x ≤ f p - ρ ^ 2}
                      {u : Smale.MorseHandle.UnitDisk c.NegativeCoordinates |
                        ‖(u : c.NegativeCoordinates)‖ = 1}
                      (coreCellMap c ρ hρ hblock) ≃ₕ
                    { x : M // f x ≤ f p + ρ ^ 2 }) := by
  obtain ⟨V, F, hV, hcurve, hzero, hdesc, hcharts, _, _, _⟩ :=
    Smale.FlowConstruction.exists_adaptedDescentFlow hf hm
  obtain ⟨c, heq⟩ := hcharts p hp
  obtain ⟨r, hr, W, hW, _, heqW, hblockr⟩ := c.exists_fieldCompatibleBlock V heq
  obtain ⟨ρ, hρ, hρmin, hband⟩ :=
    Smale.ManifoldMorse.exists_isolating_radius (Smale.ManifoldMorse.finite_criticalPoints hf hm)
      p hunique (lt_min hr hR)
  have hρr : ρ < r := hρmin.trans_le (min_le_left r R)
  have hρR : ρ < R := hρmin.trans_le (min_le_right r R)
  have hblockW :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
    intro z hz
    apply hblockr
    have hrad : 2 * ρ ≤ 2 * r := by linarith
    exact
      ⟨Metric.closedBall_subset_closedBall hrad hz.1,
        Metric.closedBall_subset_closedBall hrad hz.2⟩
  have hblock :
    Metric.closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        Metric.closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
      c.splitChart.target :=
    fun z hz => (hblockW hz).1
  have hagreement :
    ∀ x ∈ Set.range (c.attachingHandleMap ρ hρ hblock), ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    rintro _ ⟨z, rfl⟩
    have hxW : c.attachingHandleMap ρ hρ hblock z ∈ W :=
      (hblockW (Smale.MorseHandle.modelMap_mem_product hρ z)).2
    filter_upwards [hW.mem_nhds hxW] with y hy
    exact heqW y hy
  obtain ⟨e, _⟩ :=
    c.exists_attachingUnionHomotopyEquiv hf hV hzero hdesc F hcurve ρ hρ hblock hagreement hband
  refine ⟨ρ, hρ, hρR, c, hblock, hband, core_dimension_le c, ?_⟩
  exact
    ⟨(cellHandleHomotopyEquiv c ρ hρ hblock hf.continuous).trans
        ((c.attachingHandleUnionHomeomorph hf.continuous ρ hρ hblock).toHomotopyEquiv.trans e)⟩

private structure Degree.MorseCells.Cell {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (p : M) where
  radius : ℝ
  radius_pos : 0 < radius
  chart : Smale.ManifoldMorse.SignedMorseChart (E := E) f p
  block :
    Metric.closedBall (0 : chart.NegativeCoordinates) (2 * radius) ×ˢ
        Metric.closedBall (0 : chart.PositiveCoordinates) (2 * radius) ⊆
      chart.splitChart.target
  isolated :
    ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
      f x ∈ Set.Icc (f p - radius ^ 2) (f p + radius ^ 2) → x = p
  dimension_le : Module.finrank ℝ chart.NegativeCoordinates ≤ Module.finrank ℝ E
  comparison :
    Smale.ClosedAttachment.Space {x : M | f x ≤ f p - radius ^ 2}
        {u : Smale.MorseHandle.UnitDisk chart.NegativeCoordinates |
          ‖(u : chart.NegativeCoordinates)‖ = 1}
        (coreCellMap chart radius radius_pos block) ≃ₕ
      { x : M // f x ≤ f p + radius ^ 2 }

private def Degree.MorseCells.Cell.band {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (c : Degree.MorseCells.Cell (E := E) f p) : Set ℝ :=
  Set.Icc (f p - c.radius ^ 2) (f p + c.radius ^ 2)

private theorem
    Degree.MorseCells.exists_cell_lt {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {p : M}
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hunique : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, f x = f p → x = p) {R : ℝ}
    (hR : 0 < R) : ∃ c : Cell (E := E) f p, c.radius < R := by
  obtain ⟨ρ, hρ, hlt, c, hb, hi, hd, ⟨e⟩⟩ := exists_morse_cell_attachment_lt hf hm hp hunique hR
  exact ⟨⟨ρ, hρ, c, hb, hi, hd, e⟩, hlt⟩

private theorem Degree.MorseCells.exists_disjoint_cells {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f)) :
    ∃ c : (p : Smale.ManifoldMorse.criticalPoints E f) → Cell (E := E) f p.val,
      ∀ p q, p ≠ q → Disjoint (c p).band (c q).band := by
  have hR (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∃ R > (0 : ℝ),
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        f x ∈ Set.Icc (f p - R ^ 2) (f p + R ^ 2) → x = p := by
    obtain ⟨R, hR, _, hi⟩ :=
      Smale.ManifoldMorse.exists_isolating_radius
        (Smale.ManifoldMorse.finite_criticalPoints hf hm) p.val
        (fun x hx heq => hinj hx p.property heq) zero_lt_one
    exact ⟨R, hR, hi⟩
  choose R hR hiso using hR
  have hc (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∃ c : Cell (E := E) f p.val, c.radius < R p / 2 :=
    exists_cell_lt hf hm p.property (fun x hx heq => hinj hx p.property heq) (half_pos (hR p))
  choose c hc using hc
  refine ⟨c, ?_⟩
  have hordered (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q) :
    Disjoint (c p).band (c q).band := by
    have hne : (p : M) ≠ q := fun he => (ne_of_lt hpq) (congrArg f he)
    have hp : (R p) ^ 2 < f q - f p := by
      by_contra h
      have he :=
        hiso p q q.property
          (show f q ∈ Set.Icc (f p - (R p) ^ 2) (f p + (R p) ^ 2) from
            ⟨by nlinarith [sq_nonneg (R p)], by linarith⟩)
      exact hne he.symm
    have hq : (R q) ^ 2 < f q - f p := by
      by_contra h
      have he :=
        hiso q p p.property
          (show f p ∈ Set.Icc (f q - (R q) ^ 2) (f q + (R q) ^ 2) from
            ⟨by linarith, by nlinarith [sq_nonneg (R q)]⟩)
      exact hne he
    have hsp : (c p).radius ^ 2 < (R p / 2) ^ 2 :=
      (sq_lt_sq₀ (c p).radius_pos.le (half_pos (hR p)).le).mpr (hc p)
    have hsq : (c q).radius ^ 2 < (R q / 2) ^ 2 :=
      (sq_lt_sq₀ (c q).radius_pos.le (half_pos (hR q)).le).mpr (hc q)
    apply Set.disjoint_left.mpr
    intro t htp htq
    change f p - (c p).radius ^ 2 ≤ t ∧ t ≤ f p + (c p).radius ^ 2 at htp
    change f q - (c q).radius ^ 2 ≤ t ∧ t ≤ f q + (c q).radius ^ 2 at htq
    nlinarith [htp.2, htq.1]
  intro p q hpq
  rcases lt_trichotomy (f p) (f q) with h | h | h
  · exact hordered p q h
  · exact (hpq (Subtype.ext (hinj p.property q.property h))).elim
  · exact (hordered q p h).symm

private theorem Degree.MorseCells.upper_lt_lower_of_disjoint {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p q : M}
    (c : Cell (E := E) f p) (d : Cell (E := E) f q) (h : Disjoint c.band d.band)
    (hpq : f p < f q) : f p + c.radius ^ 2 < f q - d.radius ^ 2 := by
  by_contra hn
  have hle : f q - d.radius ^ 2 ≤ f p + c.radius ^ 2 := le_of_not_gt hn
  let t := Max.max (f p - c.radius ^ 2) (f q - d.radius ^ 2)
  have hc : t ∈ c.band := by
    exact ⟨le_max_left _ _, max_le (by nlinarith [sq_nonneg c.radius]) hle⟩
  have hd : t ∈ d.band := by
    refine ⟨le_max_right _ _, max_le ?_ ?_⟩
    · nlinarith [sq_nonneg c.radius, sq_nonneg d.radius]
    · nlinarith [sq_nonneg d.radius]
  exact Set.disjoint_left.mp h hc hd

private theorem
    Degree.MorseCells.isEmpty_sublevel_of_no_critical {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (h : ∀ p ∈ Smale.ManifoldMorse.criticalPoints E f, ¬f p ≤ a) : IsEmpty { x : M // f x ≤ a } :=
  by
  refine ⟨fun x => ?_⟩
  obtain ⟨p, _, hmin⟩ :=
    isCompact_univ.exists_isMinOn ⟨x.val, Set.mem_univ _⟩ hf.continuous.continuousOn
  have hp : p ∈ Smale.ManifoldMorse.criticalPoints E f :=
    Smale.ManifoldMorse.mem_criticalPoints_of_localMin hf
      (Filter.Eventually.of_forall (fun y => hmin (Set.mem_univ y)))
  exact h p hp ((hmin (Set.mem_univ x.val)).trans x.property)

private theorem Degree.MorseCells.built_upper_sublevels {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f)
    (hinj : Set.InjOn f (Smale.ManifoldMorse.criticalPoints E f))
    (c : (p : Smale.ManifoldMorse.criticalPoints E f) → Cell (E := E) f p.val)
    (hdis : ∀ p q, p ≠ q → Disjoint (c p).band (c q).band)
    (p : Smale.ManifoldMorse.criticalPoints E f) :
    Degree.FiniteCells.Built (Module.finrank ℝ E) { x : M // f x ≤ f p + (c p).radius ^ 2 } := by
  classical
  let K := Smale.ManifoldMorse.criticalPoints E f
  let : Fintype K := (Smale.ManifoldMorse.finite_criticalPoints hf hm).fintype
  let : LinearOrder K :=
    LinearOrder.lift' (fun p : K => f p.val)
      (fun p q h => Subtype.ext (hinj p.property q.property h))
  have hstep (p : K) :
    Degree.FiniteCells.Built (Module.finrank ℝ E) { x : M // f x ≤ f p + (c p).radius ^ 2 } := by
    induction p using WellFoundedLT.induction with
    | ind p
      ih =>
      have hlower :
        Degree.FiniteCells.Built (Module.finrank ℝ E) { x : M // f x ≤ f p - (c p).radius ^ 2 } :=
        by
        by_cases hex : ∃ q : K, q < p
        · let s : Finset K := Finset.univ.filter (fun q => q < p)
          have hs : s.Nonempty := by
            obtain ⟨q, hq⟩ := hex
            exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩⟩
          let q := s.max' hs
          have hqp : q < p := (Finset.mem_filter.mp (s.max'_mem hs)).2
          have hgap : f q + (c q).radius ^ 2 < f p - (c p).radius ^ 2 :=
            upper_lt_lower_of_disjoint (c q) (c p) (hdis q p (ne_of_lt hqp)) hqp
          obtain ⟨e, _⟩ :=
            Smale.FlowConstruction.exists_regularSublevelHomotopyEquiv hf hgap.le
              (by
                intro x hx hcrit
                let r : K := ⟨x, hcrit⟩
                have hrp : r < p := by
                  change f x < f p
                  nlinarith [sq_pos_of_pos (c p).radius_pos, hx.2]
                have hrq : r ≤ q := s.le_max' r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrp⟩)
                change f x ≤ f q at hrq
                nlinarith [sq_pos_of_pos (c q).radius_pos, hx.1])
          exact Degree.FiniteCells.Built.equiv e (ih q hqp)
        · let : IsEmpty { x : M // f x ≤ f p - (c p).radius ^ 2 } :=
            isEmpty_sublevel_of_no_critical hf
              (by
                intro x hx hle
                apply hex
                refine ⟨⟨x, hx⟩, ?_⟩
                change f x < f p
                nlinarith [sq_pos_of_pos (c p).radius_pos])
          exact Degree.FiniteCells.Built.empty _
      apply Degree.FiniteCells.Built.equiv (c p).comparison
      exact
        Degree.FiniteCells.Built.attach _
          (coreCellMap (c p).chart (c p).radius (c p).radius_pos (c p).block)
          (fun u hu =>
            (coreCellMap_lower_iff (c p).chart (c p).radius (c p).radius_pos (c p).block u).mpr
              hu)
          (c p).dimension_le hlower
  exact hstep p

private theorem
    Degree.MorseCells.built_of_compact_smooth_manifold {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] :
    Degree.FiniteCells.Built (Module.finrank ℝ E) M := by
  classical
    cases isEmpty_or_nonempty M with
  | inl h => exact Degree.FiniteCells.Built.empty _
  | inr
    h =>
    obtain ⟨f, hf, hm, _, hinj⟩ :=
      Smale.ManifoldMorse.exists_morse_function_with_distinct_critical_values E M
    obtain ⟨c, hdis⟩ := exists_disjoint_cells hf hm hinj
    obtain ⟨p, _, hmax⟩ :=
      isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hf.continuous.continuousOn
    have hp : p ∈ Smale.ManifoldMorse.criticalPoints E f :=
      Smale.ManifoldMorse.mem_criticalPoints_of_localMax hf
        (Filter.Eventually.of_forall (fun y => hmax (Set.mem_univ y)))
    let q : Smale.ManifoldMorse.criticalPoints E f := ⟨p, hp⟩
    have hb := built_upper_sublevels hf hm hinj c hdis q
    have hfull : {x : M | f x ≤ f q + (c q).radius ^ 2} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      change f x ≤ f p + (c q).radius ^ 2
      exact (hmax (Set.mem_univ x)).trans (le_add_of_nonneg_right (sq_nonneg (c q).radius))
    exact
      Degree.FiniteCells.Built.equiv
        ((Homeomorph.setCongr hfull).trans (Homeomorph.Set.univ M)).toHomotopyEquiv hb

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
    SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
    SpecialPeriods.Threefold.space_isSmoothRealManifold in
private theorem Degree.Threefold.finite_homotopy_cells :
    Degree.FiniteCells.Built 6 SpecialPeriods.Threefold.Space := by
  simpa only [SpecialPeriods.Threefold.real_dimension] using
    (Degree.MorseCells.built_of_compact_smooth_manifold (E := ℂ × ComplexPlane₂) (M :=
      SpecialPeriods.Threefold.Space))

private theorem Degree.exists_right_homotopy_inverse (x : SpecialPeriods.Threefold.Space) :
    ∃ g : C(SpecialPeriods.Threefold.Space, SixSphereCube.StandardSphere),
      ((SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x).comp g).Homotopic
        (ContinuousMap.id SpecialPeriods.Threefold.Space) :=
  FiniteCells.mapsLift_of_built (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)
    (TopCellLifting.sphereMap_relativeDiskLifting_six x) Threefold.finite_homotopy_cells
    (ContinuousMap.id SpecialPeriods.Threefold.Space)

private def Degree.cylinderQuotient :
    C((unitInterval) × (Fin 6 → (unitInterval)), (unitInterval) × SixSphereCube.StandardSphere) :=
  (ContinuousMap.id (unitInterval)).prodMap SixSphereCube.cubeSphereMap

private theorem Degree.cylinderQuotient_surjective : Function.Surjective cylinderQuotient := by
  rintro ⟨t, z⟩
  obtain ⟨u, rfl⟩ := SixSphereCube.cubeSphereMap_surjective z
  exact ⟨(t, u), rfl⟩

private theorem Degree.cylinderQuotient_isQuotientMap : Topology.IsQuotientMap cylinderQuotient :=
  .of_surjective_continuous cylinderQuotient_surjective cylinderQuotient.continuous

private theorem
    Degree.cubeHomotopy_constant_on_cylinderFibres {X : Type*} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6)))
    (a b : (unitInterval) × (Fin 6 → (unitInterval)))
    (h : cylinderQuotient a = cylinderQuotient b) : H a = H b := by
  rcases a with ⟨t, u⟩
  rcases b with ⟨s, v⟩
  have ht : t = s := congrArg Prod.fst h
  subst s
  have huv : SixSphereCube.cubeSphereMap u = SixSphereCube.cubeSphereMap v := congrArg Prod.snd h
  rcases (SixSphereCube.cubeSphereMap_eq_iff u v).mp huv with rfl | ⟨hu, hv⟩
  · rfl
  · exact
      ((H.eq_fst t hu).trans (p.property u hu)).trans
        ((H.eq_fst t hv).trans (p.property v hv)).symm

private def
    Degree.cubeHomotopyLift {X : Type*} [TopologicalSpace X] {x : X} {p q : GenLoop (Fin 6) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6))) :
    C((unitInterval) × SixSphereCube.StandardSphere, X) :=
  cylinderQuotient_isQuotientMap.lift H.toHomotopy.toContinuousMap
    (cubeHomotopy_constant_on_cylinderFibres H)

private theorem Degree.cubeHomotopyLift_apply {X : Type*} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6)))
    (t : (unitInterval)) (u : Fin 6 → (unitInterval)) :
    cubeHomotopyLift H (t, SixSphereCube.cubeSphereMap u) = H (t, u) :=
  ContinuousMap.congr_fun
    (cylinderQuotient_isQuotientMap.lift_comp H.toHomotopy.toContinuousMap
      (cubeHomotopy_constant_on_cylinderFibres H))
    (t, u)

private def
    Degree.factorHomotopy {X : Type*} [TopologicalSpace X] {x : X} {p q : GenLoop (Fin 6) X x}
    (H : p.val.HomotopyRel q.val (Cube.boundary (Fin 6))) :
    (SixSphereCube.factorMap p).HomotopyRel (SixSphereCube.factorMap q)
      { SixSphereCube.sphereBasePoint }
    where
  toContinuousMap := cubeHomotopyLift H
  map_zero_left
    z := by
    obtain ⟨u, rfl⟩ := SixSphereCube.cubeSphereMap_surjective z
    change
      cubeHomotopyLift H (0, SixSphereCube.cubeSphereMap u) =
        SixSphereCube.factorMap p (SixSphereCube.cubeSphereMap u)
    rw [cubeHomotopyLift_apply, H.apply_zero, SixSphereCube.factorMap_cubeSphereMap]
    rfl
  map_one_left
    z := by
    obtain ⟨u, rfl⟩ := SixSphereCube.cubeSphereMap_surjective z
    change
      cubeHomotopyLift H (1, SixSphereCube.cubeSphereMap u) =
        SixSphereCube.factorMap q (SixSphereCube.cubeSphereMap u)
    rw [cubeHomotopyLift_apply, H.apply_one, SixSphereCube.factorMap_cubeSphereMap]
    rfl
  prop' t z
    hz := by
    have hz' : z = SixSphereCube.sphereBasePoint := hz
    subst z
    change
      cubeHomotopyLift H (t, SixSphereCube.sphereBasePoint) =
        SixSphereCube.factorMap p SixSphereCube.sphereBasePoint
    rw [← SixSphereCube.cubeSphereMap_boundary 0 SixSphereCube.zero_mem_cubeBoundary,
      cubeHomotopyLift_apply]
    rw [H.eq_fst t SixSphereCube.zero_mem_cubeBoundary, SixSphereCube.factorMap_cubeSphereMap]
    rfl

private theorem Degree.factorMap_homotopicRel {X : Type*} [TopologicalSpace X] {x : X}
    {p q : GenLoop (Fin 6) X x} (h : GenLoop.Homotopic p q) :
    (SixSphereCube.factorMap p).HomotopicRel (SixSphereCube.factorMap q)
      { SixSphereCube.sphereBasePoint } := by
  obtain ⟨H⟩ := h
  exact ⟨factorHomotopy H⟩

private theorem Degree.SphereBasepoint.exists_adjustment {Y : Type*} [TopologicalSpace Y] {y : Y}
    (u : C(SixSphereCube.StandardSphere, Y)) (P : Path (u SixSphereCube.sphereBasePoint) y) :
    ∃ v : C(SixSphereCube.StandardSphere, Y),
      v SixSphereCube.sphereBasePoint = y ∧ u.Homotopic v := by
  let V := Fin 6 → ℝ
  let L : V ≃L[ℝ] V := ContinuousLinearEquiv.refl ℝ V
  let e := Degree.DiskCube.homeomorph L
  let f : C(Degree.DiskCylinder.Disk (E := V), Y) :=
    u.comp (SixSphereCube.cubeSphereMap.comp (e : C(_, _)))
  let side : C((unitInterval) × Degree.DiskCylinder.Sphere (E := V), Y) :=
    P.toContinuousMap.comp ContinuousMap.fst
  have h0 : ∀ s, side (0, s) = f (Degree.DiskCylinder.boundaryToDisk s) := by
    intro s
    have hs :=
      (Degree.DiskCube.boundary_iff L (Degree.DiskCylinder.boundaryToDisk s)).mpr
        (mem_sphere_zero_iff_norm.mp s.property)
    exact P.source.trans (congrArg u (SixSphereCube.cubeSphereMap_boundary _ hs)).symm
  let W := Degree.DiskCylinder.extend f side h0
  let C : C((unitInterval) × (Fin 6 → (unitInterval)), Y) :=
    W.comp ((ContinuousMap.id (unitInterval)).prodMap (e.symm : C(_, _)))
  have hCboundary (t : (unitInterval)) (z : Fin 6 → (unitInterval))
    (hz : z ∈ Cube.boundary (Fin 6)) : C (t, z) = P t := by
    let s : Degree.DiskCylinder.Sphere (E := V) :=
      ⟨(e.symm z).val,
        mem_sphere_zero_iff_norm.mpr ((Degree.DiskCube.symm_boundary_iff L z).mpr hz)⟩
    exact Degree.DiskCylinder.extend_side f side h0 t s
  have hfib : ∀ a b, Degree.cylinderQuotient a = Degree.cylinderQuotient b → C a = C b := by
    rintro ⟨t, z⟩ ⟨s, w⟩ h
    have ht : t = s := congrArg Prod.fst h
    subst s
    have hzw : SixSphereCube.cubeSphereMap z = SixSphereCube.cubeSphereMap w :=
      congrArg Prod.snd h
    rcases (SixSphereCube.cubeSphereMap_eq_iff z w).mp hzw with rfl | ⟨hz, hw⟩
    · rfl
    · exact (hCboundary t z hz).trans (hCboundary t w hw).symm
  let G := Degree.cylinderQuotient_isQuotientMap.lift C hfib
  have hG (t : (unitInterval)) (z : Fin 6 → (unitInterval)) :
    G (t, SixSphereCube.cubeSphereMap z) = C (t, z) :=
    ContinuousMap.congr_fun (Degree.cylinderQuotient_isQuotientMap.lift_comp C hfib) (t, z)
  let v : C(SixSphereCube.StandardSphere, Y) :=
    G.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  refine
    ⟨v, ?_,
      ⟨{  toContinuousMap := G
          map_zero_left := ?_
          map_one_left := fun _ => rfl }⟩⟩
  · change G (1, SixSphereCube.sphereBasePoint) = y
    rw [← SixSphereCube.cubeSphereMap_boundary 0 SixSphereCube.zero_mem_cubeBoundary, hG]
    exact (hCboundary 1 0 SixSphereCube.zero_mem_cubeBoundary).trans P.target
  · intro z
    obtain ⟨w, rfl⟩ := SixSphereCube.cubeSphereMap_surjective z
    exact
      (hG 0 w).trans
        ((Degree.DiskCylinder.extend_bottom f side h0 (e.symm w)).trans
          (congrArg (fun q => u (SixSphereCube.cubeSphereMap q)) (e.apply_symm_apply w)))

private def Degree.basedSphereCube {X : Type} [TopologicalSpace X] {x : X}
    (f : C(SixSphereCube.StandardSphere, X)) (hf : f SixSphereCube.sphereBasePoint = x) :
    GenLoop (Fin 6) X x :=
  ⟨f.comp SixSphereCube.cubeSphereMap, by
    intro u hu
    change f (SixSphereCube.cubeSphereMap u) = x
    rw [SixSphereCube.cubeSphereMap_boundary u hu]
    exact hf⟩

@[simp]
private theorem Degree.factorMap_basedSphereCube {X : Type} [TopologicalSpace X] {x : X}
    (f : C(SixSphereCube.StandardSphere, X)) (hf : f SixSphereCube.sphereBasePoint = x) :
    SixSphereCube.factorMap (basedSphereCube f hf) = f := by
  symm
  apply SixSphereCube.factorMap_unique
  rfl

private theorem Degree.basedSphereCube_homologyClass {X : Type} [TopologicalSpace X] {x : X}
    (f : C(SixSphereCube.StandardSphere, X)) (hf : f SixSphereCube.sphereBasePoint = x) :
    SixthHurewicz.cubeHomologyClass (basedSphereCube f hf) =
      SingularMayerVietoris.singularHomologyMap f 6
        (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) := by
  rw [← SixSphereCube.factor_cubeHomologyClass, factorMap_basedSphereCube]

private theorem Degree.sphere_homotopicRel_of_topClass_eq {X : Type} [TopologicalSpace X] {x : X}
    [SimplyConnectedSpace X] [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
    [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] (f g : C(SixSphereCube.StandardSphere, X))
    (hf : f SixSphereCube.sphereBasePoint = x) (hg : g SixSphereCube.sphereBasePoint = x)
    (h :
      SingularMayerVietoris.singularHomologyMap f 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) =
        SingularMayerVietoris.singularHomologyMap g 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop)) :
    f.HomotopicRel g { SixSphereCube.sphereBasePoint } := by
  have he : (⟦basedSphereCube f hf⟧ : π_ 6 X x) = ⟦basedSphereCube g hg⟧ := by
    apply (SixthHurewicz.hurewiczPi6Equiv x).injective
    change
      Multiplicative.ofAdd (SixthHurewicz.cubeHomologyClass (basedSphereCube f hf)) =
        Multiplicative.ofAdd (SixthHurewicz.cubeHomologyClass (basedSphereCube g hg))
    rw [basedSphereCube_homologyClass, basedSphereCube_homologyClass, h]
  have hh := factorMap_homotopicRel (Quotient.exact he)
  simpa only [factorMap_basedSphereCube] using hh

private theorem Degree.Sphere.based_homotopicRel_id_of_topClass
    (g : C(SixSphereCube.StandardSphere, SixSphereCube.StandardSphere))
    (hg : g SixSphereCube.sphereBasePoint = SixSphereCube.sphereBasePoint)
    (hd :
      SingularMayerVietoris.singularHomologyMap g 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) =
        SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) :
    g.HomotopicRel (ContinuousMap.id SixSphereCube.StandardSphere)
      { SixSphereCube.sphereBasePoint } := by
  let := piTwo_subsingleton SixSphereCube.sphereBasePoint
  let := piThree_subsingleton SixSphereCube.sphereBasePoint
  let := piFour_subsingleton SixSphereCube.sphereBasePoint
  let := piFive_subsingleton SixSphereCube.sphereBasePoint
  apply
    Degree.sphere_homotopicRel_of_topClass_eq g (ContinuousMap.id SixSphereCube.StandardSphere) hg
      rfl
  simpa only [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] using hd

private theorem Degree.Sphere.homotopic_id_of_topClass
    (g : C(SixSphereCube.StandardSphere, SixSphereCube.StandardSphere))
    (hd :
      SingularMayerVietoris.singularHomologyMap g 6
          (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) =
        SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) :
    g.Homotopic (ContinuousMap.id SixSphereCube.StandardSphere) := by
  obtain ⟨v, hv, hgv⟩ :=
    Degree.SphereBasepoint.exists_adjustment g
      (PathConnectedSpace.somePath (g SixSphereCube.sphereBasePoint)
        SixSphereCube.sphereBasePoint)
  have hmap := PeriodTorusHigherHomology.homotopic_homologyMap hgv 6
  have hvd :
    SingularMayerVietoris.singularHomologyMap v 6
        (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop) =
      SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop :=
    (LinearMap.congr_fun hmap _).symm.trans hd
  obtain ⟨H⟩ := based_homotopicRel_id_of_topClass v hv hvd
  exact hgv.trans ⟨H.toHomotopy⟩

private theorem Degree.right_inverse_is_left_inverse (x : SpecialPeriods.Threefold.Space)
    (g : C(SpecialPeriods.Threefold.Space, SixSphereCube.StandardSphere))
    (hfg :
      ((SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x).comp g).Homotopic
        (ContinuousMap.id SpecialPeriods.Threefold.Space)) :
    (g.comp (SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x)).Homotopic
      (ContinuousMap.id SixSphereCube.StandardSphere) := by
  let F := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
  have hh : (F.comp (g.comp F)).Homotopic F := by
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
      hfg.comp (ContinuousMap.Homotopic.refl F)
  apply Sphere.homotopic_id_of_topClass
  apply (SpecialPeriods.Threefold.SphereHomologyEquivalence.homologyMap_bijective x 6).1
  have he :=
    LinearMap.congr_fun (PeriodTorusHigherHomology.homotopic_homologyMap hh 6)
      (SixthHurewicz.cubeHomologyClass SixSphereCube.cubeSphereLoop)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply] at he
  exact he

private def Degree.sphereHomotopyEquiv (x : SpecialPeriods.Threefold.Space) :
    SixSphereCube.StandardSphere ≃ₕ SpecialPeriods.Threefold.Space := by
  let g := Classical.choose (exists_right_homotopy_inverse x)
  have hfg := Classical.choose_spec (exists_right_homotopy_inverse x)
  exact
    { toFun := SpecialPeriods.Threefold.SphereHomologyEquivalence.sphereMap x
      invFun := g
      left_inv := right_inverse_is_left_inverse x g hfg
      right_inv := hfg }

private def Degree.threefoldHomotopyEquiv :
    SpecialPeriods.Threefold.Space ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin 7)) 1 :=
  (sphereHomotopyEquiv (Classical.choice SpecialPeriods.Threefold.space_nonempty)).symm

private theorem MorseCancel.nativeMorseCount_eq_interval_length {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
        {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (k a b : ℕ) (hab : a ≤ b) (hb : b ≤ S.count)
    (hindex : ∀ i : Fin S.count, nativeMorseIndex E f (S.point i) = k ↔ a ≤ i.val ∧ i.val < b) :
    nativeMorseCount E f k = b - a := by
  let K : Set M := {x | x ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f x = k}
  let u : Fin (b - a) → K := fun j =>
    ⟨(S.point ⟨a + j.val, by omega⟩).val, (S.point ⟨a + j.val, by omega⟩).property,
      (hindex ⟨a + j.val, by omega⟩).mpr
        (show a ≤ a + j.val ∧ a + j.val < b from ⟨by omega, by omega⟩)⟩
  have hu : Function.Bijective u := by
    constructor
    · intro i j hij
      have hv : (u i).val = (u j).val := congrArg Subtype.val hij
      have hp : S.point ⟨a + i.val, by omega⟩ = S.point ⟨a + j.val, by omega⟩ := Subtype.ext hv
      have he := congrArg Fin.val (S.point.injective hp)
      exact Fin.ext (by simpa only [Nat.add_left_cancel_iff] using he)
    · intro x
      let i := S.point.symm ⟨x.val, x.property.1⟩
      have hi : S.point i = ⟨x.val, x.property.1⟩ := S.point.apply_symm_apply _
      have hxi : nativeMorseIndex E f (S.point i) = k := by
        rw [hi]
        exact x.property.2
      have hib := (hindex i).mp hxi
      refine ⟨⟨i.val - a, by omega⟩, ?_⟩
      apply Subtype.ext
      change (S.point ⟨a + (i.val - a), _⟩).val = x.val
      have he : (⟨a + (i.val - a), by omega⟩ : Fin S.count) = i :=
        Fin.ext (show a + (i.val - a) = i.val by omega)
      rw [he, hi]
  have hc := (Nat.card_congr (Equiv.ofBijective u hu)).symm
  change K.ncard = b - a
  rw [← Nat.card_coe_set_eq]
  simpa only [Nat.card_fin] using hc

private theorem MorseCancel.native_middle_block_counts {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hafter :
      ∀ i : Fin S.count,
        r + c < i.val → 4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates) :
    nativeMorseCount E f 2 = r ∧ nativeMorseCount E f 3 = c := by
  have hn := S.count_pos hf
  have hi0 (i : Fin S.count) (hi : i.val = 0) : nativeMorseIndex E f (S.point i) = 0 := by
    have he : i = ⟨0, hn⟩ := Fin.ext hi
    rw [he]
    exact (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  have hi2 (i : Fin S.count) (hi : 0 < i.val) (hir : i.val ≤ r) :
    nativeMorseIndex E f (S.point i) = 2 :=
    (nativeMorseIndex_eq_chart (S.data (S.point i)).chart).trans (htwo i hi hir)
  have hi3 (i : Fin S.count) (hri : r < i.val) (hic : i.val ≤ r + c) :
    nativeMorseIndex E f (S.point i) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (S.point i)).chart).trans (hthree i hri hic)
  have hi4 (i : Fin S.count) (hic : r + c < i.val) : 4 ≤ nativeMorseIndex E f (S.point i) := by
    rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart]
    exact hafter i hic
  have hcases (i : Fin S.count) :
    (i.val = 0 ∧ nativeMorseIndex E f (S.point i) = 0) ∨
      (0 < i.val ∧ i.val ≤ r ∧ nativeMorseIndex E f (S.point i) = 2) ∨
        (r < i.val ∧ i.val ≤ r + c ∧ nativeMorseIndex E f (S.point i) = 3) ∨
          (r + c < i.val ∧ 4 ≤ nativeMorseIndex E f (S.point i)) := by
    by_cases hz : i.val = 0
    · exact Or.inl ⟨hz, hi0 i hz⟩
    by_cases hr : i.val ≤ r
    · exact Or.inr (Or.inl ⟨by omega, hr, hi2 i (by omega) hr⟩)
    by_cases hrc : i.val ≤ r + c
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, hrc, hi3 i (by omega) hrc⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, hi4 i (by omega)⟩))
  constructor
  · have hh :=
      nativeMorseCount_eq_interval_length S 2 1 (r + 1) (by omega) (by omega)
        (fun i => by have h := hcases i; omega)
    simpa only [Nat.add_sub_cancel_right] using hh
  · have hh :=
      nativeMorseCount_eq_interval_length S 3 (r + 1) (r + c + 1) (by omega) (by omega)
        (fun i => by have h := hcases i; omega)
    have he : r + c + 1 - (r + 1) = c := by omega
    simpa only [he] using hh

private theorem AdaptedWindows.attaching_sphere_reaches_of_compact_basin_section {E M X : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    [TopologicalSpace X] [CompactSpace X] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) (n : ℕ)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = n + 1)]
    [PreconnectedSpace (Smale.Hemisphere.Sphere n)] {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (α : C(X, { y : M // f y = a })) (x₀ : X)
    (hfull :
      ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val)) :
    ∀ u : Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1,
      ((S.data p).surgery.attachingSphere u).val ∈
        Degree.FlowCancellation.levelBasin S.flow f a := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  have hback (x : X) := (hfull (α x)).mp (Set.mem_range_self x)
  have hreach (x : X) :=
    S.backward_basin_reaches_attaching_level hf p (ha (α x).val (α x).property) (hback x)
  obtain ⟨t₀, ht₀⟩ := hreach x₀
  obtain ⟨D, hsource, htarget, horbit⟩ :=
    S.exists_native_level_basin_transport hf ha (S.data p).lower_regular (α x₀)
      ⟨S.flow t₀ (α x₀).val, ht₀⟩
  have hsrc (x : X) : α x ∈ D.source := hsource.symm ▸ hreach x
  let β : X → (S.data p).LowerLevel := D ∘ α
  have hβ : Continuous β := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact
      (D.contMDiffOn_toFun.continuousOn.continuousAt (D.open_source.mem_nhds (hsrc x))).comp
        α.continuous.continuousAt
  have hβback (x : X) : Filter.Tendsto (fun t => S.flow t (β x).val) Filter.atBot (𝓝 p.val) := by
    obtain ⟨t, ht⟩ := horbit (α x) (hsrc x)
    change Filter.Tendsto (fun t => S.flow t (D (α x)).val) Filter.atBot (𝓝 p.val)
    rw [← ht]
    exact (MorseCancel.flow_time_atBot_limit_iff S.flow t (α x).val p.val).mpr (hback x)
  let e :=
    (Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
        n).toHomeomorph
  let A : C(Smale.Hemisphere.Sphere n, (S.data p).LowerLevel) :=
    (S.data p).surgery.attachingSphere.comp (e : C(_, _))
  let U : Set (Smale.Hemisphere.Sphere n) := A ⁻¹' D.target
  have hUeq : U = A ⁻¹' Set.range β := by
    ext u
    constructor
    · intro hu
      have hxu : D.symm (A u) ∈ D.source := D.map_target' hu
      have hright : D (D.symm (A u)) = A u := D.right_inv' hu
      obtain ⟨t, ht⟩ := horbit (D.symm (A u)) hxu
      rw [hright] at ht
      have hAback : Filter.Tendsto (fun t => S.flow t (A u).val) Filter.atBot (𝓝 p.val) :=
        (S.attaching_basin_iff hf p (A u)).mpr ⟨e u, rfl⟩
      have hxb : Filter.Tendsto (fun t => S.flow t (D.symm (A u)).val) Filter.atBot (𝓝 p.val) := by
        rw [← ht] at hAback
        exact (MorseCancel.flow_time_atBot_limit_iff S.flow t (D.symm (A u)).val p.val).mp hAback
      obtain ⟨x, hx⟩ := (hfull (D.symm (A u))).mpr hxb
      exact ⟨x, (congrArg D hx).trans hright⟩
    · rintro ⟨x, hx⟩
      change A u ∈ D.target
      rw [← hx]
      exact D.map_source' (hsrc x)
  have hUopen : IsOpen U := D.open_target.preimage A.continuous
  have hUclosed : IsClosed U := by
    rw [hUeq]
    exact (isCompact_range hβ).isClosed.preimage A.continuous
  have hUne : U.Nonempty := by
    obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p (β x₀)).mp (hβback x₀)
    obtain ⟨v, hv⟩ := e.surjective u
    refine ⟨v, ?_⟩
    change A v ∈ D.target
    have heq : A v = β x₀ := by change (S.data p).surgery.attachingSphere (e v) = _; rw [hv, hu]
    rw [heq]
    exact D.map_source' (hsrc x₀)
  have hUall : U = Set.univ := IsClopen.eq_univ ⟨hUclosed, hUopen⟩ hUne
  intro u
  obtain ⟨v, rfl⟩ := e.surjective u
  have hv : A v ∈ D.target := show v ∈ U from hUall.symm ▸ Set.mem_univ v
  rw [htarget] at hv
  exact hv

private theorem
    MorseCancel.nativeIndexThreeAttachingSphere_regular {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : nativeMorseIndex E f p = 3) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (nativeIndexThreeAttachingSphere S p hp) ∧
      Topology.IsClosedEmbedding (nativeIndexThreeAttachingSphere S p hp) ∧
        ∀ x,
          Function.Injective
            (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E)
              (nativeIndexThreeAttachingSphere S p hp) x) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  let e := Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2
  have hs :
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (nativeIndexThreeAttachingSphere S p hp) :=
    ((S.data p).attaching_smooth hf 2).comp e.contMDiff
  have hi : Function.Injective (nativeIndexThreeAttachingSphere S p hp) :=
    (S.data p).attaching_isClosedEmbedding.injective.comp e.injective
  refine ⟨hs, hs.continuous.isClosedEmbedding hi, ?_⟩
  intro x
  change
    Function.Injective
      (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ((S.data p).surgery.attachingSphere ∘ e) x)
  rw [mfderiv_comp x (((S.data p).attaching_smooth hf 2).mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiableAt (by simp))]
  exact
    ((S.data p).attaching_derivative_injective hf 2 (e x)).comp
      (e.mfderivToContinuousLinearEquiv (by simp) x).injective

private theorem AdaptedWindows.exists_canonical_basin_sphere {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) {X : Type} [TopologicalSpace X] [CompactSpace X]
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (α : C(X, { y : M // f y = a })) (x₀ : X)
    (hfull :
      ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val)) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ∃ γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
      ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ ∧
        Topology.IsClosedEmbedding γ ∧
          (∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) γ x)) ∧
            Set.range γ = Set.range α ∧
              (∀ x,
                  ∃ t : ℝ,
                    S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S p hp x).val =
                      (γ x).val) ∧
                ∀ y,
                  y ∈ Set.range γ ↔
                    Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).lower_regular
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hreach := S.attaching_sphere_reaches_of_compact_basin_section hf p 2 ha α x₀ hfull
  obtain ⟨hs, he, hi⟩ := MorseCancel.nativeIndexThreeAttachingSphere_regular S hf p hp
  let z₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  obtain ⟨D, -, -, γ, hγ, hγi, hγd, -, -, horbit⟩ :=
    S.exists_embedded_level_transport hf (S.data p).lower_regular ha
      (MorseCancel.nativeIndexThreeAttachingSphere S p hp) z₀ hs he.injective hi
      (fun z => hreach _)
  have hγfull (y : { x : M // f x = a }) :
    y ∈ Set.range γ ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val) :=
    S.transported_attaching_range_iff hf p ha
      (Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates 2)
      (Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
          2).surjective
      γ horbit y
  exact
    ⟨γ, hγ, hγ.continuous.isClosedEmbedding hγi, hγd,
      Set.ext (fun y => (hγfull y).trans (hfull y).symm), horbit, hγfull⟩

private theorem AdaptedWindows.exists_canonical_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (α : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = a })
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p α) :
    ∃ γ : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = a },
      MorseCancel.IsNativeMiddleBasinFamily S hf ha p γ ∧
        (∀ j, Set.range (γ j) = Set.range (α j)) ∧
          ∀ j x,
            ∃ t : ℝ,
              S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S (p j) (hp j) x).val =
                (γ j x).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  obtain ⟨hαs, -, -, hαpair, hαfull⟩ := hα
  let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  have hex (j : Fin n) :=
    S.exists_canonical_basin_sphere hf (p j) (hp j) ha ⟨α j, (hαs j).continuous⟩ x₀ (hαfull j)
  choose γ hγs hγe hγi hγrange hγflow hγfull using hex
  refine ⟨fun j => γ j, ⟨hγs, hγe, hγi, ?_, hγfull⟩, hγrange, hγflow⟩
  intro i j hij
  rw [hγrange i, hγrange j]
  exact hαpair hij

private def MorseCancel.levelSublevelMap {M : Type} [TopologicalSpace M] (f : M → ℝ) {a b : ℝ}
    (hab : a ≤ b) : C({ y : M // f y = a }, { y : M // f y ≤ b }) :=
  ⟨fun y => ⟨y.val, y.property.le.trans hab⟩, continuous_subtype_val.subtype_mk _⟩

private theorem
    AdaptedWindows.level_transport_homotopic_in_sublevel {E M X : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ} [TopologicalSpace X]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (g : C(X, { y : M // f y = b })) (γ : C(X, { y : M // f y = a }))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (g x).val = (γ x).val) :
    ContinuousMap.Homotopic ((MorseCancel.levelSublevelMap f le_rfl).comp g)
      ((MorseCancel.levelSublevelMap f hab.le).comp γ) := by
  have hboundary (y : M) (hy : f y = a) : mvfderiv 𝓘(ℝ, E) f y (S.field y) < 0 :=
    S.descent y (ha y hy)
  have hreach (x : X) : (g x).val ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
    obtain ⟨t, ht⟩ := horbit x
    exact ⟨t, by rw [ht]; exact (γ x).property⟩
  let θ : X → ℝ := fun x => Degree.FlowCancellation.signedLevelTime S.flow f a (g x).val
  obtain ⟨hB, htime, -⟩ :=
    Degree.FlowCancellation.smooth_signed_level_time hf S.smooth S.flow S.integral hboundary
  have hθ : Continuous θ := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact
      ContinuousAt.comp (f := fun y : X => (g y).val)
        (htime.continuousOn.continuousAt (hB.mem_nhds (hreach x)))
        (continuous_subtype_val.comp g.continuous).continuousAt
  have hhit (x : X) : f (S.flow (θ x) (g x).val) = a :=
    Degree.FlowCancellation.signedLevelTime_hits S.flow f a (hreach x)
  have hθpos (x : X) : 0 < θ x := by
    by_contra h
    have hh :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent (g x).val
        (le_of_not_gt h)
    change f (S.flow 0 (g x).val) ≤ f (S.flow (θ x) (g x).val) at hh
    rw [S.flow.map_zero_apply, (g x).property, hhit x] at hh
    exact not_le_of_gt hab hh
  have hend (x : X) : S.flow (θ x) (g x).val = (γ x).val := by
    obtain ⟨t, ht⟩ := horbit x
    have hθt : θ x = t :=
      Degree.FlowCancellation.signedLevelTime_eq_of_level S.flow hf.continuous
        (MorseCancel.contMDiff_directionalDerivative hf S.smooth).continuous
        (fun y s => Smale.FlowConstruction.hasDerivAt_comp_integralCurve hf (S.integral y) s)
        hboundary (by rw [ht]; exact (γ x).property)
    rw [hθt]
    exact ht
  have hstay (u : unitInterval) (x : X) : f (S.flow ((u : ℝ) * θ x) (g x).val) ≤ b := by
    have hh :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent (g x).val
        (mul_nonneg u.property.1 (hθpos x).le)
    simpa only [S.flow.map_zero_apply, (g x).property] using hh
  refine
    ⟨{  toFun := fun z => ⟨S.flow ((z.1 : ℝ) * θ z.2) (g z.2).val, hstay z.1 z.2⟩
        continuous_toFun :=
          (S.flow.continuous
                ((continuous_subtype_val.comp continuous_fst).mul (hθ.comp continuous_snd))
                (continuous_subtype_val.comp (g.continuous.comp continuous_snd))).subtype_mk
            _
        map_zero_left := ?_
        map_one_left := ?_ }⟩
  · intro x
    apply Subtype.ext
    change S.flow ((0 : ℝ) * θ x) (g x).val = (g x).val
    simp
  · intro x
    apply Subtype.ext
    change S.flow ((1 : ℝ) * θ x) (g x).val = (γ x).val
    simpa only [one_mul] using hend x

private theorem
    Smale.ManifoldMorse.MorseSurgeryData.indexThreeAttachingClass_parametrized {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    [hindex : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)] :
    d.indexThreeAttachingClass hindex.out =
      SingularMayerVietoris.singularHomologyMap
        (d.coreBoundaryMap.comp
          (Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
              2).toHomeomorph.toHomotopyEquiv.toFun)
        2 (SphereHomology.unitSphereTopClass 1) := by
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private def
    MorseCancel.sublevelMap {M : Type} [TopologicalSpace M] (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) :
    C({ y : M // f y ≤ a }, { y : M // f y ≤ b }) :=
  ⟨fun y => ⟨y.val, y.property.trans hab⟩, continuous_subtype_val.subtype_mk _⟩

private def MorseCancel.middleSectionClass {M : Type} [TopologicalSpace M] {f : M → ℝ} {a : ℝ}
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 :=
  SingularMayerVietoris.singularHomologyMap ((levelSublevelMap f le_rfl).comp γ) 2
    (SphereHomology.unitSphereTopClass 1)

private theorem
    AdaptedWindows.native_attaching_class_of_flow_section {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hab : a < S.toSurgeryWindows.lower p)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ,
          S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S p hp x).val = (γ x).val) :
    SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hab.le) 2
        (MorseCancel.middleSectionClass γ) =
      (S.data p).indexThreeAttachingClass
        ((MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp) := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hh :=
    S.level_transport_homotopic_in_sublevel hf hab ha
      (MorseCancel.nativeIndexThreeAttachingSphere S p hp) γ horbit
  have hm := PeriodTorusHigherHomology.homotopic_homologyMap hh 2
  have hparam :
    SingularMayerVietoris.singularHomologyMap
        ((MorseCancel.levelSublevelMap f (le_refl (S.toSurgeryWindows.lower p))).comp
          (MorseCancel.nativeIndexThreeAttachingSphere S p hp))
        2 (SphereHomology.unitSphereTopClass 1) =
      (S.data p).indexThreeAttachingClass
        ((MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp) :=
    (S.data p).indexThreeAttachingClass_parametrized.symm
  rw [← hparam, hm]
  rw [MorseCancel.middleSectionClass, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private theorem
    AdaptedWindows.exists_native_core_inclusion_equiv {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∃ e :
      ↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ Set.range (S.data p).coreMap) ≃ₕ
        { y : M // f y ≤ S.toSurgeryWindows.upper p },
      ∀ x, (e x).val = x.val := by
  let d := S.data p
  have hagreement :
    ∀ x ∈ Set.range (d.chart.attachingHandleMap d.radius d.radius_pos d.block),
      ∀ᶠ y in 𝓝 x, S.field y = d.chart.descentField y := by
    rintro x ⟨z, rfl⟩
    exact S.model_germ p _ (Smale.MorseHandle.modelMap_mem_product d.radius_pos z)
  obtain ⟨B, hB⟩ :=
    d.chart.exists_attachingUnionHomotopyEquiv hf S.smooth S.zero S.descent S.flow S.integral
      d.radius d.radius_pos d.block hagreement (S.isolated p)
  let C :=
    Smale.ClosedHandleCore.unionHomotopyEquiv {y : M | f y ≤ S.toSurgeryWindows.lower p}
      d.handleMap (isClosed_le hf.continuous continuous_const)
      (d.chart.attachingHandleMap_isClosedEmbedding d.radius d.radius_pos d.block)
      (d.chart.attachingHandleMap_lower_iff d.radius d.radius_pos d.block)
  exact ⟨C.trans B, fun x => hB (C x)⟩

private theorem AdaptedWindows.exists_core_inclusion_homology_comparison {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f) (k : ℕ) :
    ∃ A :
      SingularMayerVietoris.SingularHomology
          (↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ Set.range (S.data p).coreMap)) k ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ S.toSurgeryWindows.upper p } k,
      ∀ a,
        A
            (((S.data p).coreCellPresentation hf.continuous).oldHomologyMap k
              ((S.data p).cellOldHomologyEquiv hf.continuous k a)) =
          SingularMayerVietoris.singularHomologyMap
            (MorseCancel.sublevelMap f
              ((S.toSurgeryWindows.lower_lt_value p).trans
                  (S.toSurgeryWindows.value_lt_upper p)).le)
            k a := by
  obtain ⟨B, hB⟩ := S.exists_native_core_inclusion_equiv hf p
  let d := S.data p
  let A := PeriodTorusHigherHomology.homotopyEquivHomologyEquiv B k
  let old :=
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C((d.coreCellPresentation hf.continuous).old,
        ↥({y : M | f y ≤ S.toSurgeryWindows.lower p} ∪ Set.range d.coreMap)))
  have hmaps :
    (B.toFun.comp old).comp (d.cellOldHomeomorph hf.continuous).toHomotopyEquiv.toFun =
      MorseCancel.sublevelMap f
        ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hB _)
  refine ⟨A, ?_⟩
  intro a
  change
    SingularMayerVietoris.singularHomologyMap B.toFun k
        (SingularMayerVietoris.singularHomologyMap old k
          (SingularMayerVietoris.singularHomologyMap
            (d.cellOldHomeomorph hf.continuous).toHomotopyEquiv.toFun k a)) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, ←
    LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, hmaps]
  rfl

private theorem AdaptedWindows.native_sublevel_inclusion_exact {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f) (k : ℕ)
    (hk : k ≠ 0) :
    LinearMap.range ((S.data p).coreBoundaryHomologyMap k) =
      LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (MorseCancel.sublevelMap f
            ((S.toSurgeryWindows.lower_lt_value p).trans
                (S.toSurgeryWindows.value_lt_upper p)).le)
          k) := by
  obtain ⟨A, hA⟩ := S.exists_core_inclusion_homology_comparison hf p k
  let d := S.data p
  refine
    Smale.HomologyTransport.exact_of_equivalences (LinearEquiv.refl ℤ _)
      (d.cellOldHomologyEquiv hf.continuous k).symm A
      ((d.coreCellPresentation hf.continuous).attachingHomologyMap k)
      ((d.coreCellPresentation hf.continuous).oldHomologyMap k) (d.coreBoundaryHomologyMap k) _ ?_
      ?_ ((d.coreCellPresentation hf.continuous).cell_exact_at_old k hk)
  · intro a
    change
      d.coreBoundaryHomologyMap k a =
        (d.cellOldHomologyEquiv hf.continuous k).symm
          ((d.coreCellPresentation hf.continuous).attachingHomologyMap k a)
    rw [d.cellAttachingHomology_compare, LinearEquiv.symm_apply_apply]
  · intro a
    have hh := hA ((d.cellOldHomologyEquiv hf.continuous k).symm a)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh.symm

private theorem
    AdaptedWindows.native_index_three_inclusion_relation {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) :
    let I :=
      SingularMayerVietoris.singularHomologyMap
        (MorseCancel.sublevelMap f
          ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le)
        2
    Function.Surjective I ∧
      LinearMap.ker I =
        Submodule.span ℤ
          {(S.data p).indexThreeAttachingClass
              ((MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp)} := by
  let d := S.data p
  have hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3 :=
    (MorseCancel.nativeMorseIndex_eq_chart d.chart).symm.trans hp
  let _ :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (Metric.sphere (0 : d.chart.NegativeCoordinates) 1)
        1) :=
    d.attachingHomology_subsingleton_of_index 1 one_ne_zero (by omega) (by omega)
  have hsurj : Function.Surjective ((d.coreCellPresentation hf.continuous).oldHomologyMap 2) := by
    intro a
    have ha : a ∈ LinearMap.ker ((d.coreCellPresentation hf.continuous).cellConnectingMap 1) :=
      Subsingleton.elim _ _
    rw [← (d.coreCellPresentation hf.continuous).cell_exact_at_ambient 1] at ha
    exact ha
  obtain ⟨A, hA⟩ := S.exists_core_inclusion_homology_comparison hf p 2
  constructor
  · intro a
    obtain ⟨x, hx⟩ := hsurj (A.symm a)
    refine ⟨(d.cellOldHomologyEquiv hf.continuous 2).symm x, ?_⟩
    have hh := hA ((d.cellOldHomologyEquiv hf.continuous 2).symm x)
    rw [LinearEquiv.apply_symm_apply, hx, LinearEquiv.apply_symm_apply] at hh
    exact hh.symm
  · rw [← S.native_sublevel_inclusion_exact hf p 2 (by decide), d.coreBoundary_two_range hindex]

private theorem
    MorseCancel.sublevelMap_trans {M : Type} [TopologicalSpace M]
    (f : M → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (sublevelMap f hbc).comp (sublevelMap f hab) = sublevelMap f (hab.trans hbc) :=
  rfl

private theorem MorseCancel.sublevelHomologyMap_comp {M : Type} [TopologicalSpace M]
     (f : M → ℝ) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (k : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (sublevelMap f hbc) k).comp
        (SingularMayerVietoris.singularHomologyMap (sublevelMap f hab) k) =
      SingularMayerVietoris.singularHomologyMap (sublevelMap f (hab.trans hbc)) k := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, sublevelMap_trans]

private theorem MorseCancel.regular_sublevel_inclusion_bijective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hband : ∀ x, f x ∈ Set.Icc a b → x ∉ Smale.ManifoldMorse.criticalPoints E f) (k : ℕ) :
    Function.Bijective (SingularMayerVietoris.singularHomologyMap (sublevelMap f hab) k) := by
  obtain ⟨e, he⟩ := Smale.FlowConstruction.exists_regularSublevelHomotopyEquiv hf hab hband
  have hmap : e.toFun = sublevelMap f hab := by
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (he x)
  have hh := (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e k).bijective
  change Function.Bijective (SingularMayerVietoris.singularHomologyMap e.toFun k) at hh
  rwa [hmap] at hh

private theorem
    AdaptedWindows.middle_inclusion_step {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hbp : b < S.toSurgeryWindows.lower p)
    (hband :
      ∀ y,
        f y ∈ Set.Icc b (S.toSurgeryWindows.lower p) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ, S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S p hp x).val = (γ x).val)
    (hsurj :
      Function.Surjective
        (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hab) 2)) :
    let hau :=
      (hab.trans hbp.le).trans
        ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le
    Function.Surjective
        (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hau) 2) ∧
      LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hau) 2) =
        LinearMap.ker
            (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hab) 2) ⊔
          Submodule.span ℤ {MorseCancel.middleSectionClass γ} := by
  let hl := (S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)
  let P := SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hab) 2
  let J := SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hbp.le) 2
  let Q := SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hl.le) 2
  have hJ : Function.Bijective J :=
    MorseCancel.regular_sublevel_inclusion_bijective hf hbp.le hband 2
  obtain ⟨hQ, hkerQ⟩ := S.native_index_three_inclusion_relation hf p hp
  have hclass := S.native_attaching_class_of_flow_section hf p hp ha (hab.trans_lt hbp) γ horbit
  have hcomp :
    J.comp P =
      SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f (hab.trans hbp.le))
        2 :=
    MorseCancel.sublevelHomologyMap_comp f hab hbp.le 2
  have htotal :
    Q.comp (J.comp P) =
      SingularMayerVietoris.singularHomologyMap
        (MorseCancel.sublevelMap f ((hab.trans hbp.le).trans hl.le)) 2 := by
    rw [hcomp]
    exact MorseCancel.sublevelHomologyMap_comp f (hab.trans hbp.le) hl.le 2
  have hkerJ : LinearMap.ker (J.comp P) = LinearMap.ker P := by
    ext v
    change J (P v) = 0 ↔ P v = 0
    exact ⟨fun h => hJ.injective (h.trans (map_zero J).symm), fun h => by rw [h, map_zero]⟩
  have hker :
    LinearMap.ker Q = Submodule.span ℤ {(J.comp P) (MorseCancel.middleSectionClass γ)} := by
    rw [hcomp, hclass]
    exact hkerQ
  constructor
  · rw [← htotal]
    exact hQ.comp (hJ.surjective.comp hsurj)
  · rw [← htotal,
      Smale.HomologyTransport.ker_comp_span_singleton (J.comp P) Q
        (MorseCancel.middleSectionClass γ) hker,
      hkerJ]

private theorem MorseCancel.span_prefix_succ {A : Type} [AddCommGroup A] [Module ℤ A] {n k : ℕ}
    (v : Fin n → A) (hk : k < n) :
    Submodule.span ℤ (Set.range (fun j : Fin k => v ⟨j.val, j.isLt.trans hk⟩)) ⊔
        Submodule.span ℤ {v ⟨k, hk⟩} =
      Submodule.span ℤ (Set.range (fun j : Fin (k + 1) => v ⟨j.val, by omega⟩)) := by
  have heq :
    (fun j : Fin (k + 1) => v ⟨j.val, by omega⟩) =
      Fin.snoc (fun j : Fin k => v ⟨j.val, j.isLt.trans hk⟩) (v ⟨k, hk⟩) := by
    funext j
    cases j using Fin.lastCases <;> simp
  rw [heq, Fin.range_snoc, Submodule.span_insert, sup_comm]

private theorem AdaptedWindows.finite_middle_inclusion_relations {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (n : ℕ)
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3) (cut : Fin (n + 1) → ℝ)
    (ha : ∀ y, f y = cut 0 → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hbase : ∀ i, cut 0 ≤ cut i) (hnext : ∀ j, cut j.succ = S.toSurgeryWindows.upper (p j))
    (hlower : ∀ j, cut j.castSucc < S.toSurgeryWindows.lower (p j))
    (hband :
      ∀ j y,
        f y ∈ Set.Icc (cut j.castSucc) (S.toSurgeryWindows.lower (p j)) →
          y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = cut 0 }))
    (horbit :
      ∀ j x,
        ∃ t : ℝ,
          S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S (p j) (hp j) x).val =
            (γ j x).val) :
    Function.Surjective
        (SingularMayerVietoris.singularHomologyMap
          (MorseCancel.sublevelMap f (hbase (Fin.last n))) 2) ∧
      LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap
            (MorseCancel.sublevelMap f (hbase (Fin.last n))) 2) =
        Submodule.span ℤ (Set.range (fun j => MorseCancel.middleSectionClass (γ j))) := by
  have hprefix (k : ℕ) :
    ∀ hk : k ≤ n,
      Function.Surjective
          (SingularMayerVietoris.singularHomologyMap
            (MorseCancel.sublevelMap f (hbase ⟨k, by omega⟩)) 2) ∧
        LinearMap.ker
            (SingularMayerVietoris.singularHomologyMap
              (MorseCancel.sublevelMap f (hbase ⟨k, by omega⟩)) 2) =
          Submodule.span ℤ
            (Set.range
              (fun j : Fin k =>
                MorseCancel.middleSectionClass (γ ⟨j.val, j.isLt.trans_le hk⟩))) := by
    induction k with
    | zero =>
      intro hk
      have hid :
        SingularMayerVietoris.singularHomologyMap
            (MorseCancel.sublevelMap f (hbase ⟨0, by omega⟩)) 2 =
          LinearMap.id := by
        change
          SingularMayerVietoris.singularHomologyMap (ContinuousMap.id { y : M // f y ≤ cut 0 })
              2 =
            _
        exact PeriodTorusHigherHomology.singularHomologyMap_id _ _
      constructor
      · rw [hid]
        exact Function.surjective_id
      · rw [hid]
        simp only [Set.range_eq_empty, Submodule.span_empty]
        ext v
        rfl
    | succ k ih =>
      intro hk
      have hkn : k < n := by omega
      let j : Fin n := ⟨k, hkn⟩
      obtain ⟨hprev, hkernel⟩ := ih (by omega)
      have hstep :=
        S.middle_inclusion_step hf (p j) (hp j) (hbase j.castSucc) ha (hlower j) (hband j) (γ j)
          (horbit j) hprev
      have hstep' :
        Function.Surjective
            (SingularMayerVietoris.singularHomologyMap
              (MorseCancel.sublevelMap f (hbase ⟨k + 1, by omega⟩)) 2) ∧
          LinearMap.ker
              (SingularMayerVietoris.singularHomologyMap
                (MorseCancel.sublevelMap f (hbase ⟨k + 1, by omega⟩)) 2) =
            LinearMap.ker
                (SingularMayerVietoris.singularHomologyMap
                  (MorseCancel.sublevelMap f (hbase j.castSucc)) 2) ⊔
              Submodule.span ℤ {MorseCancel.middleSectionClass (γ j)} := by
        have heq : cut ⟨k + 1, by omega⟩ = S.toSurgeryWindows.upper (p j) := hnext j
        have aux (b : ℝ) (hb : cut 0 ≤ b) (he : b = S.toSurgeryWindows.upper (p j)) :
          Function.Surjective
              (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hb) 2) ∧
            LinearMap.ker
                (SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hb) 2) =
              LinearMap.ker
                  (SingularMayerVietoris.singularHomologyMap
                    (MorseCancel.sublevelMap f (hbase j.castSucc)) 2) ⊔
                Submodule.span ℤ {MorseCancel.middleSectionClass (γ j)} := by
          subst b
          exact hstep
        exact aux _ _ heq
      refine ⟨hstep'.1, ?_⟩
      rw [hstep'.2, hkernel]
      exact MorseCancel.span_prefix_succ (fun i => MorseCancel.middleSectionClass (γ i)) hkn
  simpa only using hprefix n le_rfl

private def MorseCancel.nativeMiddleBaseCut {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S : AdaptedWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) : ℝ :=
  S.toSurgeryWindows.upper (S.toSurgeryWindows.point ⟨r, by omega⟩)

private def
    MorseCancel.nativeMiddleCutSequence {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count) :
    Fin (n + 1) → ℝ :=
  Fin.cases (nativeMiddleBaseCut S r n hn)
    (fun j => T.toSurgeryWindows.upper (nativeMiddleBlockPoint S r n hn j))

private theorem MorseCancel.nativeMiddleCutSequence_bands {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hn <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j)) :
    let p := nativeMiddleBlockPoint S r n hn
    let cut := nativeMiddleCutSequence S T r n hn
    (∀ i, cut 0 ≤ cut i) ∧
      (∀ j, cut j.succ = T.toSurgeryWindows.upper (p j)) ∧
        (∀ j, cut j.castSucc < T.toSurgeryWindows.lower (p j)) ∧
          ∀ j y,
            f y ∈ Set.Icc (cut j.castSucc) (T.toSurgeryWindows.lower (p j)) →
              y ∉ Smale.ManifoldMorse.criticalPoints E f := by
  let p := nativeMiddleBlockPoint S r n hn
  let cut := nativeMiddleCutSequence S T r n hn
  have hbase (i : Fin (n + 1)) : cut 0 ≤ cut i := by
    cases i using Fin.cases with
    | zero => exact le_rfl
    | succ j =>
      exact
        ((hbefore j).trans
            ((T.toSurgeryWindows.lower_lt_value (p j)).trans
              (T.toSurgeryWindows.value_lt_upper (p j)))).le
  have hstep (j : Fin n) : cut j.castSucc < T.toSurgeryWindows.lower (p j) := by
    cases n with
    | zero => exact Fin.elim0 j
    | succ n =>
      cases j using Fin.cases with
      | zero => exact hbefore 0
      | succ
        j =>
        change T.toSurgeryWindows.upper (p j.castSucc) < T.toSurgeryWindows.lower (p j.succ)
        apply T.separated
        apply S.toSurgeryWindows.point_strictMono
        change r + j.val + 1 < r + (j.val + 1) + 1
        omega
  have hpred (j : Fin n) : f (S.toSurgeryWindows.point ⟨r + j.val, by omega⟩) < cut j.castSucc := by
    cases n with
    | zero => exact Fin.elim0 j
    | succ n =>
      cases j using Fin.cases with
      | zero => exact S.toSurgeryWindows.value_lt_upper _
      | succ j => exact T.toSurgeryWindows.value_lt_upper (p j.castSucc)
  refine ⟨hbase, fun _ => rfl, hstep, ?_⟩
  intro j y hy hcrit
  have hconsecutive :=
    S.toSurgeryWindows.point_consecutive ⟨r + j.val, by omega⟩ ⟨r + j.val + 1, by omega⟩ rfl
  exact
    hconsecutive ⟨y, hcrit⟩
      ⟨(hpred j).trans_le hy.1, hy.2.trans_lt (T.toSurgeryWindows.lower_lt_value (p j))⟩

private theorem MorseCancel.ordered_middle_inclusion_relations {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r n : ℕ) (hn : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hn j) = 3)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hn <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hn j))
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = nativeMiddleBaseCut S r n hn }))
    (horbit :
      ∀ j x,
        ∃ t : ℝ,
          T.flow t
              (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hn j) (hp j)
                  x).val =
            (γ j x).val) :
    ∃ h : nativeMiddleBaseCut S r n hn ≤ nativeMiddleCutSequence S T r n hn (Fin.last n),
      Function.Surjective (SingularMayerVietoris.singularHomologyMap (sublevelMap f h) 2) ∧
        LinearMap.ker (SingularMayerVietoris.singularHomologyMap (sublevelMap f h) 2) =
          Submodule.span ℤ (Set.range (fun j => middleSectionClass (γ j))) := by
  obtain ⟨hbase, hnext, hlower, hband⟩ := nativeMiddleCutSequence_bands S T r n hn hbefore
  refine ⟨hbase (Fin.last n), ?_⟩
  exact
    T.finite_middle_inclusion_relations hf n (nativeMiddleBlockPoint S r n hn) hp
      (nativeMiddleCutSequence S T r n hn)
      (S.data (S.toSurgeryWindows.point ⟨r, by omega⟩)).upper_regular hbase hnext hlower hband γ
      horbit

private theorem MorseCancel.native_middle_terminal_homology_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n) :
    ∃ hrc : r + n < S.toSurgeryWindows.count,
      Subsingleton
        (SingularMayerVietoris.SingularHomology
          { y : M // f y ≤ S.toSurgeryWindows.upper (S.toSurgeryWindows.point ⟨r + n, hrc⟩) }
          2) := by
  obtain ⟨r', n', htwo, hrc, hthree, hj, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr', hn'⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r' n' htwo hrc hthree hafter
  have hrr : r' = r := hr'.symm.trans hr
  have hnn : n' = n := hn'.symm.trans hn
  rw [hrr, hnn] at hrc hj hafter
  refine ⟨hrc, ?_⟩
  exact
    S.toSurgeryWindows.upper_homology_subsingleton_of_later_indices hf hdim e ⟨r + n, hrc⟩ hj 2
      (by norm_num) (by norm_num)
      (fun i hi _ => by have hh := hafter i hi; exact ⟨by omega, by omega⟩)

private theorem MorseCancel.nativeMiddleCutSequence_terminal_homology_subsingleton {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M]
    {f : M → ℝ} (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology
        { y : M // f y ≤ nativeMiddleCutSequence S T r n hrc (Fin.last n) } 2) := by
  cases n with
  |
    zero =>
    obtain ⟨h, hH⟩ :=
      native_middle_terminal_homology_subsingleton S hf hdim e horder hzero hone r 0 hr hn
    exact hH
  | succ
    n =>
    obtain ⟨h, hH⟩ :=
      native_middle_terminal_homology_subsingleton T hf hdim e horder hzero hone r (n + 1) hr hn
    exact hH

private theorem MorseCancel.middle_section_classes_span {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hrc j) = 3)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hrc <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hrc j))
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = nativeMiddleBaseCut S r n hrc }))
    (horbit :
      ∀ j x,
        ∃ t : ℝ,
          T.flow t
              (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hrc j) (hp j)
                  x).val =
            (γ j x).val) :
    Submodule.span ℤ (Set.range (fun j => middleSectionClass (γ j))) = ⊤ := by
  obtain ⟨h, -, hker⟩ := ordered_middle_inclusion_relations S T hf r n hrc hp hbefore γ horbit
  let _ :=
    nativeMiddleCutSequence_terminal_homology_subsingleton S T hf hdim e horder hzero hone r n hr
      hn hrc
  apply top_unique
  intro v hv
  rw [← hker]
  exact Subsingleton.elim _ _

private def MorseCancel.classCoordinateMatrix {A : Type} [AddCommGroup A] [Module ℤ A] {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) : Matrix (Fin r) (Fin n) ℤ := fun i j =>
  B.symm (v j) i

private theorem MorseCancel.classCoordinateMatrix_mulVec {A : Type} [AddCommGroup A] [Module ℤ A]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A) (z : Fin n → ℤ) :
    B ((classCoordinateMatrix B v).mulVec z) = ∑ j, z j • v j := by
  have hvec : (classCoordinateMatrix B v).mulVec z = ∑ j, z j • B.symm (v j) := by
    funext i
    simp [classCoordinateMatrix, Matrix.mulVec, dotProduct, mul_comm]
  rw [hvec, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_zsmul, LinearEquiv.apply_symm_apply]

private theorem
    MorseCancel.classCoordinateMatrix_surjective {A : Type} [AddCommGroup A] [hA : Module ℤ A]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] A) (v : Fin n → A)
    (hspan : Submodule.span ℤ (Set.range v) = ⊤) :
    Function.Surjective (classCoordinateMatrix B v).mulVec := by
  intro w
  have hw : B w ∈ Submodule.span ℤ (Set.range v) := by rw [hspan]; trivial
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hw
  refine ⟨z, B.injective ?_⟩
  rw [classCoordinateMatrix_mulVec]
  have hsum : (∑ j, z j • v j) = ∑ j, hA.smul (z j) (v j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact (int_smul_eq_zsmul hA (z j) (v j)).symm
  exact hsum.trans hz

private def MorseCancel.canonicalMiddleMatrix {M : Type} [TopologicalSpace M] {f : M → ℝ} {r n : ℕ}
    {a : ℝ} (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    Matrix (Fin r) (Fin n) ℤ :=
  classCoordinateMatrix B (fun j => middleSectionClass (γ j))

private theorem MorseCancel.canonical_middle_matrix_surjective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hp : ∀ j, nativeMorseIndex E f (nativeMiddleBlockPoint S r n hrc j) = 3)
    (hbefore :
      ∀ j,
        nativeMiddleBaseCut S r n hrc <
          T.toSurgeryWindows.lower (nativeMiddleBlockPoint S r n hrc j))
    (B :
      (Fin r → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ nativeMiddleBaseCut S r n hrc } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = nativeMiddleBaseCut S r n hrc }))
    (horbit :
      ∀ j x,
        ∃ t : ℝ,
          T.flow t
              (nativeIndexThreeAttachingSphere T (nativeMiddleBlockPoint S r n hrc j) (hp j)
                  x).val =
            (γ j x).val) :
    Function.Surjective (canonicalMiddleMatrix B γ).mulVec :=
  classCoordinateMatrix_surjective B _
    (middle_section_classes_span S T hf hdim e horder hzero hone r n hr hn hrc hp hbefore γ
      horbit)

private theorem AdaptedWindows.no_connection_above_canonical_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hpq : f p < f q) (hq : MorseCancel.nativeMorseIndex E f q = 3) {a : ℝ} (hap : a < f p)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ,
          S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S q hq x).val = (γ x).val) :
    ∀ x,
      ¬(Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 q.val) ∧
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p.val)) := by
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  let e := Smale.SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates 2
  intro x hx
  have hplower : f p < S.toSurgeryWindows.lower q :=
    (S.toSurgeryWindows.value_lt_upper p).trans (S.separated p q hpq)
  obtain ⟨t, ht⟩ :=
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits S.flow hf.continuous hx.1
      hx.2 (S.toSurgeryWindows.lower_lt_value q) hplower
  let y : (S.data q).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Filter.Tendsto (fun s => S.flow s y.val) Filter.atBot (𝓝 q.val) :=
    (MorseCancel.flow_time_atBot_limit_iff S.flow t x q.val).mpr hx.1
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf q y).mp hyback
  obtain ⟨z, hz⟩ := e.surjective u
  have hpoint : MorseCancel.nativeIndexThreeAttachingSphere S q hq z = y := by
    change (S.data q).surgery.attachingSphere (e z) = y
    exact (congrArg (S.data q).surgery.attachingSphere (show e z = u from hz)).trans hu
  obtain ⟨s, hs⟩ := horbit z
  rw [hpoint] at hs
  have hyforward : Filter.Tendsto (fun v => S.flow v y.val) Filter.atTop (𝓝 p.val) :=
    (MorseCancel.flow_time_atTop_limit_iff S.flow t x p.val).mpr hx.2
  have hγforward := (MorseCancel.flow_time_atTop_limit_iff S.flow s y.val p.val).mpr hyforward
  rw [hs] at hγforward
  have hheight : Filter.Tendsto (fun v => f (S.flow v (γ z).val)) Filter.atTop (𝓝 (f p)) :=
    hf.continuous.continuousAt.tendsto.comp hγforward
  have hh :=
    (Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent
          (γ z).val).le_of_tendsto
      hheight 0
  have hpa : f p ≤ a := by simpa only [S.flow.map_zero_apply, (γ z).property] using hh
  exact not_le_of_gt hap hpa

private theorem
    MorseCancel.lower_cuts_preserved_of_critical_bound {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f g : M → ℝ} (hf : Continuous f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    {l a : ℝ} (ha : a < l) (hexterior : ∀ y, f y ≤ l → g =ᶠ[𝓝 y] f)
    (hcritical : ∀ y ∈ Smale.ManifoldMorse.criticalPoints E g, l ≤ f y → l ≤ g y) :
    (∀ y, g y ≤ a ↔ f y ≤ a) ∧ (∀ y, g y = a ↔ f y = a) ∧ ∀ y, f y ≤ a → g =ᶠ[𝓝 y] f := by
  have hbound :=
    superlevel_bound_of_critical_bound hf hg
      (fun y hy => (hexterior y hy.le).self_of_nhds.trans hy) hcritical
  have hbelow (y : M) (hy : g y ≤ a) : f y ≤ l := by
    by_contra h
    exact (ha.trans_le (hbound y (le_of_not_ge h))).not_ge hy
  refine ⟨?_, ?_, fun y hy => hexterior y (hy.trans ha.le)⟩
  · intro y
    constructor
    · intro hy
      exact ((hexterior y (hbelow y hy)).self_of_nhds) ▸ hy
    · intro hy
      rw [(hexterior y (hy.trans ha.le)).self_of_nhds]
      exact hy
  · intro y
    constructor
    · intro hy
      exact ((hexterior y (hbelow y hy.le)).self_of_nhds).symm.trans hy
    · intro hy
      exact (hexterior y (hy ▸ ha.le)).self_of_nhds.trans hy

private theorem AdaptedWindows.exists_common_cut_value_exchange {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] {f : M → ℝ} [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (p q : Smale.ManifoldMorse.criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hq : MorseCancel.nativeMorseIndex E f q = 3) (hal : a < S.toSurgeryWindows.lower p)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit :
      ∀ x,
        ∃ t : ℝ,
          S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S q hq x).val = (γ x).val) :
    ∃ g : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
        Smale.ManifoldMorse.IsMorse E g ∧
          Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f ∧
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
              g p = f q ∧
                g q = f p ∧
                  (∀ z,
                      f z ∉ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) →
                        g =ᶠ[𝓝 z] f) ∧
                    (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                        z ≠ p.val → z ≠ q.val → g =ᶠ[𝓝 z] f) ∧
                      (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                          MorseCancel.nativeMorseIndex E g z =
                            MorseCancel.nativeMorseIndex E f z) ∧
                        (∀ k,
                            MorseCancel.nativeMorseCount E g k =
                              MorseCancel.nativeMorseCount E f k) ∧
                          (∀ y, g y ≤ a ↔ f y ≤ a) ∧
                            (∀ y, g y = a ↔ f y = a) ∧
                              (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                (∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g) ∧
                                  ∃ T : AdaptedWindows E g,
                                    T.field = S.field ∧
                                      T.flow = S.flow ∧
                                        (∀ r : Smale.ManifoldMorse.criticalPoints E g,
                                            g r < a → T.toSurgeryWindows.upper r < a) ∧
                                          ∀ r : Smale.ManifoldMorse.criticalPoints E g,
                                            a < g r → a < T.toSurgeryWindows.lower r := by
  have hpband : f p ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨S.toSurgeryWindows.lower_lt_value p, hpq.trans (S.toSurgeryWindows.value_lt_upper q)⟩
  have hqband : f q ∈ Set.Ioo (S.toSurgeryWindows.lower p) (S.toSurgeryWindows.upper q) :=
    ⟨(S.toSurgeryWindows.lower_lt_value p).trans hpq, S.toSurgeryWindows.value_lt_upper q⟩
  have hnoconnection :=
    S.no_connection_above_canonical_cut hf p q hpq hq
      (hal.trans (S.toSurgeryWindows.lower_lt_value p)) γ horbit
  obtain ⟨g, hg, hmg, hcrit, hgp, hgq, hdesc, hexterior, hpgerm, hqgerm, hothers, hindices⟩ :=
    Degree.MorseRearrangement.exists_morse_rearrangement_of_no_connection hf hm S.smooth S.flow
      S.integral S.zero S.descent S.distinct (S.data p).chart (S.data q).chart
      (S.critical_model_germ p) (S.critical_model_germ q) hpband hqband hpq hqband hpband
      (MorseCancel.surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive) hnoconnection
  have hinjg : Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) := by
    rw [hcrit]
    exact
      MorseCancel.injOn_of_exchanged_values S.distinct p.property q.property hgp hgq
        (fun x hx hxp hxq => (hothers x hx hxp hxq).self_of_nhds)
  have hnewmodels (r : Smale.ManifoldMorse.criticalPoints E g) :
    ∃ c : Smale.ManifoldMorse.SignedMorseChart (E := E) g r.val,
      ∀ᶠ y in 𝓝 r.val, S.field y = c.descentField y := by
    have hr : r.val ∈ Smale.ManifoldMorse.criticalPoints E f := hcrit ▸ r.property
    by_cases hrp : r.val = p.val
    · obtain ⟨c, hc⟩ :=
        MorseCancel.exists_signed_morse_chart_of_shift_germ_preserving_field (S.data p).chart
          hpgerm
      rw [hrp]
      exact ⟨c, hc ▸ S.critical_model_germ p⟩
    by_cases hrq : r.val = q.val
    · obtain ⟨c, hc⟩ :=
        MorseCancel.exists_signed_morse_chart_of_shift_germ_preserving_field (S.data q).chart
          hqgerm
      rw [hrq]
      exact ⟨c, hc ▸ S.critical_model_germ q⟩
    obtain ⟨c, hc⟩ :=
      MorseCancel.exists_signed_morse_chart_of_germ_preserving_field (S.data ⟨r.val, hr⟩).chart
        (hothers r hr hrp hrq)
    exact ⟨c, hc ▸ S.critical_model_germ ⟨r.val, hr⟩⟩
  have hout (y : M) (hy : f y ≤ S.toSurgeryWindows.lower p) : g =ᶠ[𝓝 y] f :=
    hexterior y (fun h => h.1.not_ge hy)
  have hbound (y : M) (hy : y ∈ Smale.ManifoldMorse.criticalPoints E g)
    (hfy : S.toSurgeryWindows.lower p ≤ f y) : S.toSurgeryWindows.lower p ≤ g y := by
    by_cases hyp : y = p.val
    · rw [hyp, hgp]
      exact hqband.1.le
    by_cases hyq : y = q.val
    · rw [hyq, hgq]
      exact hpband.1.le
    rw [(hothers y (hcrit ▸ hy) hyp hyq).self_of_nhds]
    exact hfy
  obtain ⟨hsub, hlevel, hgerm⟩ :=
    MorseCancel.lower_cuts_preserved_of_critical_bound hf.continuous hg hal hout hbound
  have hga (y : M) (hy : g y = a) : y ∉ Smale.ManifoldMorse.criticalPoints E g := by
    rw [hcrit]
    exact ha y ((hlevel y).mp hy)
  choose c hc using hnewmodels
  obtain ⟨T₀, hfield₀, hflow₀, -⟩ :=
    MorseCancel.exists_adapted_windows_with_prescribed_flow hg hmg hinjg S.smooth S.flow
      S.integral (fun x hx => S.zero x (hcrit ▸ hx)) (fun x hx => hdesc x (hcrit ▸ hx)) c hc
  obtain ⟨T, hfield, hflow, -, hbelow, habove⟩ :=
    T₀.exists_same_flow_windows_avoiding_level hg hmg hga
  exact
    ⟨g, hg, hmg, hcrit, hinjg, hgp, hgq, hexterior, hothers, hindices,
      MorseCancel.nativeMorseCount_eq_of_preserved_indices hcrit hindices, hsub, hlevel, hgerm,
      hga, T, hfield.trans hfield₀, hflow.trans hflow₀, hbelow, habove⟩

private def MorseCancel.equalCutSection {M : Type} [TopologicalSpace M] {f g : M → ℝ} {a : ℝ}
    (hlevel : ∀ y, g y = a ↔ f y = a) (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    C((Smale.Hemisphere.Sphere 2), { y : M // g y = a }) :=
  ⟨fun x => ⟨(γ x).val, (hlevel _).mpr (γ x).property⟩,
    (continuous_subtype_val.comp γ.continuous).subtype_mk _⟩

private def
    MorseCancel.equalCutSublevelHomeomorph {M : Type} [TopologicalSpace M] {f g : M → ℝ} {a : ℝ}
    (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) : { y : M // f y ≤ a } ≃ₜ { y : M // g y ≤ a }
    where
  toFun y := ⟨y.val, (hsub y).mpr y.property⟩
  invFun y := ⟨y.val, (hsub y).mp y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

private def MorseCancel.equalCutHomologyEquiv {M : Type} [TopologicalSpace M] {f g : M → ℝ} {a : ℝ}
    (hsub : ∀ y, g y ≤ a ↔ f y ≤ a) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // g y ≤ a } 2 :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
    (equalCutSublevelHomeomorph hsub).toHomotopyEquiv 2

private theorem MorseCancel.equalCutSection_class {M : Type} [TopologicalSpace M]
     {f g : M → ℝ} {a : ℝ} (hsub : ∀ y, g y ≤ a ↔ f y ≤ a)
    (hlevel : ∀ y, g y = a ↔ f y = a) (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    equalCutHomologyEquiv hsub (middleSectionClass γ) =
      middleSectionClass (equalCutSection hlevel γ) := by
  have hmaps :
    (equalCutSublevelHomeomorph hsub).toHomotopyEquiv.toFun.comp
        ((levelSublevelMap f le_rfl).comp γ) =
      (levelSublevelMap g le_rfl).comp (equalCutSection hlevel γ) := by
    apply ContinuousMap.ext
    intro x
    rfl
  change
    SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph hsub).toHomotopyEquiv.toFun 2 (middleSectionClass γ) =
      _
  rw [middleSectionClass, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, hmaps]
  rfl

private theorem
    MorseCancel.canonicalMiddleMatrix_equalCut {M : Type} [TopologicalSpace M]
     {f g : M → ℝ} {a : ℝ} (hsub : ∀ y, g y ≤ a ↔ f y ≤ a)
    (hlevel : ∀ y, g y = a ↔ f y = a) {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    canonicalMiddleMatrix (B.trans (equalCutHomologyEquiv hsub))
        (fun j => equalCutSection hlevel (γ j)) =
      canonicalMiddleMatrix B γ := by
  funext i j
  change
    B.symm ((equalCutHomologyEquiv hsub).symm (middleSectionClass (equalCutSection hlevel (γ j))))
        i =
      B.symm (middleSectionClass (γ j)) i
  rw [← equalCutSection_class hsub hlevel, LinearEquiv.symm_apply_apply]

private theorem MorseCancel.nativeMiddleBasinFamily_equalCut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f g : M → ℝ} {a : ℝ}
    (S : AdaptedWindows E f) (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hlevel : ∀ y, g y = a ↔ f y = a) (hflow : T.flow = S.flow) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j)) :
    IsNativeMiddleBasinFamily T hg hga (fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩)
      (fun j => equalCutSection hlevel (γ j)) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hg hga
  let e := equalLevelDiffeomorph hf hg ha hga hlevel
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hγ
  have hβs (j : Fin n) :
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (equalCutSection hlevel (γ j)) := by
    change ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (e ∘ γ j)
    exact e.contMDiff.comp (hs j)
  refine ⟨hβs, ?_, ?_, ?_, ?_⟩
  · intro j
    apply (hβs j).continuous.isClosedEmbedding
    change Function.Injective (e ∘ γ j)
    exact e.injective.comp (he j).injective
  · intro j x
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (e ∘ γ j) x)
    rw [mfderiv_comp x (e.contMDiff.mdifferentiableAt (by simp))
        ((hs j).mdifferentiableAt (by simp))]
    exact (e.mfderivToContinuousLinearEquiv (by simp) (γ j x)).injective.comp (hi j x)
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro y hiy hjy
    obtain ⟨x, hx⟩ := hiy
    obtain ⟨z, hz⟩ := hjy
    have hsame : γ i x = γ j z := e.injective (hx.trans hz.symm)
    exact Set.disjoint_left.mp (hpair hij) (Set.mem_range_self x) ⟨z, hsame.symm⟩
  · intro j y
    have hmem : y ∈ Set.range (equalCutSection hlevel (γ j)) ↔ e.symm y ∈ Set.range (γ j) := by
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x, ?_⟩
        apply e.injective
        exact hx.trans (e.apply_symm_apply y).symm
      · rintro ⟨x, hx⟩
        exact ⟨x, (congrArg e hx).trans (e.apply_symm_apply y)⟩
    rw [hmem, hfull j]
    rw [hflow]
    rfl

private theorem
    MorseCancel.native_index_order_of_equal_index_exchange {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
       {f g : M → ℝ}
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hequal : nativeMorseIndex E f p = nativeMorseIndex E f q)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hgp : g p = f q) (hgq : g q = f p)
    (hothers : ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f, x ≠ p.val → x ≠ q.val → g x = f x)
    (hindices :
      ∀ x ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g x = nativeMorseIndex E f x) :
    ∀ x y : Smale.ManifoldMorse.criticalPoints E g,
      g x < g y → nativeMorseIndex E g x ≤ nativeMorseIndex E g y := by
  classical
  have hform (x : Smale.ManifoldMorse.criticalPoints E f) : g x = f (Equiv.swap p q x) := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hgp
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hgq
    simpa only [Equiv.swap_apply_def, ite_eq_right hxp, ite_eq_right hxq] using
      hothers x x.property (fun h => hxp (Subtype.ext h)) (fun h => hxq (Subtype.ext h))
  have hind (x : Smale.ManifoldMorse.criticalPoints E f) :
    nativeMorseIndex E f (Equiv.swap p q x) = nativeMorseIndex E f x := by
    by_cases hxp : x = p
    · subst x
      simpa only [Equiv.swap_apply_left] using hequal.symm
    by_cases hxq : x = q
    · subst x
      simpa only [Equiv.swap_apply_right] using hequal
    simp only [Equiv.swap_apply_def, ite_eq_right hxp, ite_eq_right hxq]
  intro x y hxy
  let x' : Smale.ManifoldMorse.criticalPoints E f := ⟨x.val, hcrit ▸ x.property⟩
  let y' : Smale.ManifoldMorse.criticalPoints E f := ⟨y.val, hcrit ▸ y.property⟩
  have hxy' : f (Equiv.swap p q x') < f (Equiv.swap p q y') := by
    rw [← hform, ← hform]
    exact hxy
  have hh := horder (Equiv.swap p q x') (Equiv.swap p q y') hxy'
  rw [hind, hind] at hh
  rw [hindices x x'.property, hindices y y'.property]
  exact hh

private theorem
    AdaptedWindows.exists_middle_family_value_exchange {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PreconnectedSpace M]
     (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec) (i j : Fin n)
    (hij : f (p i) < f (p j))
    (hconsecutive :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f, ¬(f (p i) < f z ∧ f z < f (p j))) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        Smale.ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
            Set.InjOn g (Smale.ManifoldMorse.criticalPoints E g) ∧
              g (p i) = f (p j) ∧
                g (p j) = f (p i) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      z ≠ (p i).val → z ≠ (p j).val → g z = f z) ∧
                    (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                        g x < g y →
                          MorseCancel.nativeMorseIndex E g x ≤
                            MorseCancel.nativeMorseIndex E g y) ∧
                      (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                          MorseCancel.nativeMorseIndex E g z =
                            MorseCancel.nativeMorseIndex E f z) ∧
                        (∀ k,
                            MorseCancel.nativeMorseCount E g k =
                              MorseCancel.nativeMorseCount E f k) ∧
                          ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                            ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                              ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                                ∃ T : AdaptedWindows E g,
                                  T.field = S.field ∧
                                    T.flow = S.flow ∧
                                      (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                        let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                          fun k => ⟨(p k).val, hcrit.symm ▸ (p k).property⟩
                                        let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                        let γ' := fun k =>
                                          MorseCancel.equalCutSection hlevel (γ k)
                                        (∀ k, MorseCancel.nativeMorseIndex E g (p' k) = 3) ∧
                                          (∀ k, a < T.toSurgeryWindows.lower (p' k)) ∧
                                            MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                                (fun k => γ' k) ∧
                                              (∀ k x, (γ' k x).val = (γ k x).val) ∧
                                                MorseCancel.canonicalMiddleMatrix B' γ' =
                                                    MorseCancel.canonicalMiddleMatrix B γ ∧
                                                  Function.Surjective
                                                    (MorseCancel.canonicalMiddleMatrix B'
                                                        γ').mulVec := by
  obtain ⟨δ, -, -, -, -, horbit, -⟩ :=
    S.exists_canonical_basin_sphere hf (p j) (hp j) ha (γ j)
      (Smale.Hemisphere.point Bool.true ⟨0, by simp⟩) (hγ.2.2.2.2 j)
  obtain
    ⟨g, hg, hmg, hcrit, hinj, hgp, hgq, -, hothers, hindices, hcounts, hsub, hlevel, hgerm, hga,
      T, hfield, hflow, -, habove⟩ :=
    S.exists_common_cut_value_exchange hf hm ha (p i) (p j) hij hconsecutive (hp j) (hlower i) δ
      horbit
  have hneworder :=
    MorseCancel.native_index_order_of_equal_index_exchange horder (p i) (p j)
      ((hp i).trans (hp j).symm) hcrit hgp hgq
      (fun x hx hxi hxj => (hothers x hx hxi hxj).self_of_nhds) hindices
  have hheight (k : Fin n) : a < g (p k) := by
    by_cases hki : (p k).val = (p i).val
    · rw [hki, hgp]
      exact (hlower j).trans (S.toSurgeryWindows.lower_lt_value (p j))
    by_cases hkj : (p k).val = (p j).val
    · rw [hkj, hgq]
      exact (hlower i).trans (S.toSurgeryWindows.lower_lt_value (p i))
    rw [(hothers (p k) (p k).property hki hkj).self_of_nhds]
    exact (hlower k).trans (S.toSurgeryWindows.lower_lt_value (p k))
  have hmatrix := MorseCancel.canonicalMiddleMatrix_equalCut hsub hlevel B γ
  refine
    ⟨g, hg, hmg, hcrit, hinj, hgp, hgq, (fun z hz hzi hzj => (hothers z hz hzi hzj).self_of_nhds),
      hneworder, hindices, hcounts, hsub, hlevel, hga, T, hfield, hflow, hgerm, ?_, ?_, ?_, ?_,
      hmatrix, ?_⟩
  · intro k
    exact (hindices (p k) (p k).property).trans (hp k)
  · intro k
    exact habove ⟨(p k).val, hcrit.symm ▸ (p k).property⟩ (hheight k)
  · exact MorseCancel.nativeMiddleBasinFamily_equalCut S T hf hg ha hga hcrit hlevel hflow p γ hγ
  · intro k x
    rfl
  · rw [hmatrix]
    exact hsurj

private theorem
    MorseCancel.nativeMiddleBasinFamily_labels_injective {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : IsNativeMiddleBasinFamily S hf ha p (fun j => γ j)) : Function.Injective p := by
  intro i j hij
  by_contra hne
  let x : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  have hbasin := (hγ.2.2.2.2 i (γ i x)).mp (Set.mem_range_self x)
  have hj : γ i x ∈ Set.range (γ j) := by
    apply (hγ.2.2.2.2 j (γ i x)).mpr
    simpa only [hij] using hbasin
  exact Set.disjoint_left.mp (hγ.2.2.2.1 hne) (Set.mem_range_self x) hj

private theorem AdaptedWindows.exists_first_middle_pivot {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} [PreconnectedSpace M]
     (S₀ : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S₀.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S₀ hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec) (q : Fin n) :
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        Smale.ManifoldMorse.IsMorse E g ∧
          ∃ hcrit :
            Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
            (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                g x < g y →
                  MorseCancel.nativeMorseIndex E g x ≤ MorseCancel.nativeMorseIndex E g y) ∧
              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                  MorseCancel.nativeMorseIndex E g z = MorseCancel.nativeMorseIndex E f z) ∧
                (∀ k, MorseCancel.nativeMorseCount E g k = MorseCancel.nativeMorseCount E f k) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      (∀ j, z ≠ (p j).val) → g z = f z) ∧
                    (∀ j, j ≠ q → g (p q) < g (p j)) ∧
                      ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                          ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                            ∃ T : AdaptedWindows E g,
                              T.field = S₀.field ∧
                                T.flow = S₀.flow ∧
                                  (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                    let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                      fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                    let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                    let γ' := fun j => MorseCancel.equalCutSection hlevel (γ j)
                                    (∀ j, MorseCancel.nativeMorseIndex E g (p' j) = 3) ∧
                                      (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                        MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                            (fun j => γ' j) ∧
                                          (∀ j x, (γ' j x).val = (γ j x).val) ∧
                                            MorseCancel.canonicalMiddleMatrix B' γ' =
                                                MorseCancel.canonicalMiddleMatrix B γ ∧
                                              Function.Surjective
                                                (MorseCancel.canonicalMiddleMatrix B'
                                                    γ').mulVec := by
  classical
  have hpinj := MorseCancel.nativeMiddleBasinFamily_labels_injective S₀ hf ha p γ hγ
  let P : ℕ → Prop := fun m =>
    ∃ g : M → ℝ,
      ∃ hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g,
        Smale.ManifoldMorse.IsMorse E g ∧
          ∃ hc : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f,
            ∃ hs : ∀ y, g y ≤ a ↔ f y ≤ a,
              ∃ hl : ∀ y, g y = a ↔ f y = a,
                ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                  ∃ T : AdaptedWindows E g,
                    (∀ x y : Smale.ManifoldMorse.criticalPoints E g,
                        g x < g y →
                          MorseCancel.nativeMorseIndex E g x ≤
                            MorseCancel.nativeMorseIndex E g y) ∧
                      (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                          MorseCancel.nativeMorseIndex E g z =
                            MorseCancel.nativeMorseIndex E f z) ∧
                        (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                            (∀ j, z ≠ (p j).val) → g z = f z) ∧
                          T.field = S₀.field ∧
                            T.flow = S₀.flow ∧
                              (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                (∀ j,
                                    a <
                                      T.toSurgeryWindows.lower
                                        ⟨(p j).val, hc.symm ▸ (p j).property⟩) ∧
                                  Degree.MorseRearrangement.beforeValueRank (fun j => g (p j)) q =
                                    m
  have hex : ∃ m, P m :=
    ⟨Degree.MorseRearrangement.beforeValueRank (fun j => f (p j)) q, f, hf, hm, rfl, fun _ =>
      Iff.rfl, fun _ => Iff.rfl, ha, S₀, horder, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl,
      fun _ _ => Filter.EventuallyEq.rfl, hlower, rfl⟩
  obtain
    ⟨g, hg, hmg, hcrit, hsub, hlevel, hga, T, hgorder, hindices, houtside, hfield, hflow, hgerm,
      hglower, hrank⟩ :=
    Nat.find_spec hex
  let pg : Fin n → Smale.ManifoldMorse.criticalPoints E g := fun j =>
    ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
  let Bg := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
  let γg := fun j => MorseCancel.equalCutSection hlevel (γ j)
  have hpg (j : Fin n) : MorseCancel.nativeMorseIndex E g (pg j) = 3 :=
    (hindices (p j) (p j).property).trans (hp j)
  have hfamily : MorseCancel.IsNativeMiddleBasinFamily T hg hga pg (fun j => γg j) :=
    MorseCancel.nativeMiddleBasinFamily_equalCut S₀ T hf hg ha hga hcrit hlevel hflow p γ hγ
  have hmatrix :
    MorseCancel.canonicalMiddleMatrix Bg γg = MorseCancel.canonicalMiddleMatrix B γ :=
    MorseCancel.canonicalMiddleMatrix_equalCut hsub hlevel B γ
  have hgsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix Bg γg).mulVec := by
    rw [hmatrix]
    exact hsurj
  have hvalueinj : Function.Injective (fun j => g (p j)) := by
    intro i j hij
    exact hpinj (Subtype.ext (T.distinct (pg i).property (pg j).property hij))
  have hfirst : ∀ j, j ≠ q → g (p q) < g (p j) := by
    intro j hj
    by_contra hnot
    have hjq : g (p j) < g (p q) :=
      lt_of_le_of_ne (le_of_not_gt hnot) (fun heq => hj (hvalueinj heq))
    let K := Finset.univ.filter (fun k => g (p k) < g (p q))
    have hjK : j ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjq⟩
    obtain ⟨i, hi, hmax⟩ := K.exists_max_image (fun k => g (p k)) ⟨j, hjK⟩
    have hiq : g (p i) < g (p q) := (Finset.mem_filter.mp hi).2
    have hconsecutive : ∀ k, ¬(g (p i) < g (p k) ∧ g (p k) < g (p q)) := by
      intro k hk
      exact (not_lt_of_ge (hmax k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.2⟩))) hk.1
    have hglobal :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g, ¬(g (pg i) < g z ∧ g z < g (pg q)) := by
      intro z hz
      have hidx : MorseCancel.nativeMorseIndex E g z = 3 := by
        apply Nat.le_antisymm
        · exact (hgorder z (pg q) hz.2).trans_eq (hpg q)
        · exact (hpg i).symm.trans_le (hgorder (pg i) z hz.1)
      let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
      have hzf : MorseCancel.nativeMorseIndex E f zf = 3 :=
        (hindices z zf.property).symm.trans hidx
      obtain ⟨k, hk⟩ := hcomplete zf hzf
      exact hconsecutive k (by simpa only [hk] using hz)
    obtain
      ⟨u, hu, hmu, hcu, -, hui, huq, huothers, huorder, huindices, -, hus, hul, hua, U, hufield,
        huflow, hugerm, -, hulower, -, -, -, -⟩ :=
      T.exists_middle_family_value_exchange hg hmg hga hgorder pg hpg hglower Bg γg hfamily hgsurj
        i q hiq hglobal
    have hdecrease :
      Degree.MorseRearrangement.beforeValueRank (fun k => u (p k)) q <
        Degree.MorseRearrangement.beforeValueRank (fun k => g (p k)) q := by
      apply
        Degree.MorseRearrangement.beforeValueRank_exchange_lt hvalueinj hiq hconsecutive hui huq
      intro k hki hkq
      apply huothers (pg k) (pg k).property
      · exact fun heq => hki (hpinj (Subtype.ext heq))
      · exact fun heq => hkq (hpinj (Subtype.ext heq))
    have hminimal :=
      Nat.find_min' hex
        (show P (Degree.MorseRearrangement.beforeValueRank (fun k => u (p k)) q) from
          ⟨u, hu, hmu, hcu.trans hcrit, fun y => (hus y).trans (hsub y), fun y =>
            (hul y).trans (hlevel y), hua, U, huorder, fun z hz =>
            (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz), fun z hz hzoutside =>
            (huothers z (hcrit.symm ▸ hz) (hzoutside i) (hzoutside q)).trans
              (houtside z hz hzoutside),
            hufield.trans hfield, huflow.trans hflow, fun y hy =>
            (hugerm y ((hsub y).mpr hy)).trans (hgerm y hy), hulower, rfl⟩)
    rw [← hrank] at hminimal
    exact (not_le_of_gt hdecrease) hminimal
  exact
    ⟨g, hg, hmg, hcrit, hgorder, hindices,
      MorseCancel.nativeMorseCount_eq_of_preserved_indices hcrit hindices, houtside, hfirst, hsub,
      hlevel, hga, T, hfield, hflow, hgerm, hpg, hglower, hfamily, fun _ _ => rfl, hmatrix,
      hgsurj⟩

private theorem
    AdaptedWindows.backward_basin_reaches_compact_section {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hp : MorseCancel.nativeMorseIndex E f p = 3) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (α : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfull :
      ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p.val))
    {x : M} (hx : x ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p.val)) :
    x ∈ Degree.FlowCancellation.levelBasin S.flow f a := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hreach :=
    S.attaching_sphere_reaches_of_compact_basin_section hf p 2 ha α
      (Smale.Hemisphere.point Bool.true ⟨0, by simp⟩) hfull
  obtain ⟨t, ht⟩ := S.backward_basin_reaches_attaching_level hf p hx hback
  let y : (S.data p).LowerLevel := ⟨S.flow t x, ht⟩
  have hyback : Filter.Tendsto (fun s => S.flow s y.val) Filter.atBot (𝓝 p.val) :=
    (MorseCancel.flow_time_atBot_limit_iff S.flow t x p.val).mpr hback
  obtain ⟨u, hu⟩ := (S.attaching_basin_iff hf p y).mp hyback
  apply (Degree.FlowCancellation.levelBasin_flow_iff S.flow f a t x).mp
  change y.val ∈ Degree.FlowCancellation.levelBasin S.flow f a
  rw [← hu]
  exact hreach u

private theorem
    AdaptedWindows.backward_basin_reaches_intermediate_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {x p : M}
    (hback : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) {b : ℝ} (hxb : f x < b)
    (hbp : b < f p) : x ∈ Degree.FlowCancellation.levelBasin S.flow f b := by
  have hh : Filter.Tendsto (fun t => f (S.flow t x)) Filter.atBot (𝓝 (f p)) :=
    hf.continuous.continuousAt.tendsto.comp hback
  obtain ⟨t, ht⟩ := (hh.eventually (eventually_gt_nhds hbp)).exists
  apply
    mem_range_of_exists_le_of_exists_ge
      (hf.continuous.comp (S.flow.continuous continuous_id continuous_const))
  · refine ⟨0, ?_⟩
    change f (S.flow 0 x) ≤ b
    rw [S.flow.map_zero_apply]
    exact hxb.le
  · exact ⟨t, ht.le⟩

private theorem
    AdaptedWindows.transported_basin_image_of_reaching {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {X : Type} {a b : ℝ}
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) (p : M)
    (α : X → { y : M // f y = a }) (β : X → { y : M // f y = b })
    (hfull : ∀ y, y ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (α x).val = (β x).val)
    (hreach :
      ∀ y : { z : M // f z = b },
        Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p) →
          y.val ∈ Degree.FlowCancellation.levelBasin S.flow f a) :
    ∀ y, y ∈ Set.range β ↔ Filter.Tendsto (fun t => S.flow t y.val) Filter.atBot (𝓝 p) := by
  intro y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨t, ht⟩ := horbit z
    rw [← ht]
    exact
      (MorseCancel.flow_time_atBot_limit_iff S.flow t (α z).val p).mpr
        ((hfull (α z)).mp (Set.mem_range_self z))
  · intro hy
    obtain ⟨s, hs⟩ := hreach y hy
    let x : { z : M // f z = a } := ⟨S.flow s y.val, hs⟩
    have hx : Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p) :=
      (MorseCancel.flow_time_atBot_limit_iff S.flow s y.val p).mpr hy
    obtain ⟨z, hz⟩ := (hfull x).mpr hx
    obtain ⟨t, ht⟩ := horbit z
    have hshared : S.flow 0 (β z).val = S.flow (t + s) y.val := by
      rw [S.flow.map_zero_apply, ← ht, hz]
      exact (S.flow.map_add t s y.val).symm
    refine ⟨z, Subtype.ext ?_⟩
    exact
      MorseCancel.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (hb z hz)) (β z).property y.property hshared

private theorem AdaptedWindows.exists_higher_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (j₀ : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3) (hpb : ∀ j, b < f (p j))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) :
    ∃ β : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = b }),
      MorseCancel.IsNativeMiddleBasinFamily S hf hb p (fun j => β j) ∧
        ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  have hreach (j : Fin n) (x : (Smale.Hemisphere.Sphere 2)) :
    (α j x).val ∈ Degree.FlowCancellation.levelBasin S.flow f b := by
    apply
      S.backward_basin_reaches_intermediate_cut hf ((hfull j (α j x)).mp (Set.mem_range_self x))
    · simpa only [(α j x).property] using hab
    · exact hpb j
  let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  obtain ⟨t₀, ht₀⟩ := hreach j₀ x₀
  obtain ⟨β, hβs, hβe, hβi, hβpair, horbit⟩ :=
    S.exists_native_family_level_transport hf ha hb (α j₀ x₀) ⟨S.flow t₀ (α j₀ x₀).val, ht₀⟩
      (fun j => α j) hs (fun j => (he j).injective) hi hpair hreach
  refine ⟨fun j => ⟨β j, (hβs j).continuous⟩, ⟨hβs, hβe, hβi, hβpair, ?_⟩, horbit⟩
  intro j
  apply S.transported_basin_image_of_reaching hf hb (p j).val (α j) (β j) (hfull j) (horbit j)
  intro y hy
  exact
    S.backward_basin_reaches_compact_section hf (p j) (hp j) ha (α j) (hfull j)
      (hb y.val y.property) hy

private theorem
    AdaptedWindows.upper_point_not_on_belt_of_lower_orbit {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : Smale.ManifoldMorse.criticalPoints E f) {a : ℝ}
    (ha : a < f q) (x : { y : M // f y = a }) (y : (S.data q).UpperLevel)
    (horbit : ∃ t : ℝ, S.flow t x.val = y.val) : y ∉ Set.range (S.data q).surgery.beltSphere := by
  intro hy
  have hyforward := (S.belt_basin_iff hf q y).mpr hy
  obtain ⟨t, ht⟩ := horbit
  have hxforward : Filter.Tendsto (fun s => S.flow s x.val) Filter.atTop (𝓝 q.val) := by
    rw [← ht] at hyforward
    exact (MorseCancel.flow_time_atTop_limit_iff S.flow t x.val q.val).mp hyforward
  have hheight : Filter.Tendsto (fun s => f (S.flow s x.val)) Filter.atTop (𝓝 (f q)) :=
    hf.continuous.continuousAt.tendsto.comp hxforward
  have hh :=
    (Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent
          x.val).le_of_tendsto
      hheight 0
  have hqa : f q ≤ a := by simpa only [S.flow.map_zero_apply, x.property] using hh
  exact ha.not_ge hqa

private theorem MorseCancel.lower_backward_basins_preserved {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) W)
    (hgeometry :
      ∀ x,
        Set.range (fun t => H t x) = Set.range (fun t => S.flow t x) ∧
          (∀ p,
              Filter.Tendsto (fun t => H t x) Filter.atTop (𝓝 p) ↔
                Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p)) ∧
            ∀ p,
              Filter.Tendsto (fun t => H t x) Filter.atBot (𝓝 p) ↔
                Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p))
    {l : ℝ} (hout : ∀ y, f y ≤ l → T.field y = W y) (p : M) (hp : f p ≤ l) :
    (∀ x,
        Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 p) ↔
          Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) ∧
      ∀ x,
        Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p) →
          Set.range (fun t => T.flow t x) = Set.range (fun t => S.flow t x) := by
  have hnew (x : M) (hx : Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 p)) :
    ∀ t, T.flow t x = H t x := by
    have hheight := hf.continuous.continuousAt.tendsto.comp hx
    have hmono :=
      Smale.FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent x
    have hagree (t : ℝ) : T.field (T.flow t x) = W (T.flow t x) :=
      hout _ ((hmono.ge_of_tendsto hheight t).trans hp)
    intro t
    rcases le_total 0 t with ht | ht
    · exact
        Degree.FlowCancellation.native_flow_eq_on_positive_halfline (hW.of_le (by simp)) H T.flow
          hH T.integral (fun s _ => hagree s) t ht
    · exact
        Degree.FlowCancellation.native_flow_eq_on_negative_halfline (hW.of_le (by simp)) H T.flow
          hH T.integral (fun s _ => hagree s) t ht
  have hold (x : M) (hx : Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) :
    ∀ t, H t x = T.flow t x := by
    have hheight := hf.continuous.continuousAt.tendsto.comp hx
    have hmono :=
      Smale.FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent x
    have hbound (t : ℝ) : f (H t x) ≤ l := by
      have hm : H t x ∈ Set.range (fun s => S.flow s x) := (hgeometry x).1 ▸ Set.mem_range_self t
      obtain ⟨s, hs⟩ := hm
      rw [← hs]
      exact (hmono.ge_of_tendsto hheight s).trans hp
    have hagree (t : ℝ) : W (H t x) = T.field (H t x) := (hout _ (hbound t)).symm
    intro t
    rcases le_total 0 t with ht | ht
    · exact
        Degree.FlowCancellation.native_flow_eq_on_positive_halfline (T.smooth.of_le (by simp))
          T.flow H T.integral hH (fun s _ => hagree s) t ht
    · exact
        Degree.FlowCancellation.native_flow_eq_on_negative_halfline (T.smooth.of_le (by simp))
          T.flow H T.integral hH (fun s _ => hagree s) t ht
  refine ⟨?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have heq : (fun t => T.flow t x) = fun t => H t x := funext (hnew x hx)
      rw [heq] at hx
      exact ((hgeometry x).2.2 p).mp hx
    · intro hx
      have heq : (fun t => H t x) = fun t => T.flow t x := funext (hold x hx)
      have hh := ((hgeometry x).2.2 p).mpr hx
      rwa [heq] at hh
  · intro x hx
    have heq : (fun t => H t x) = fun t => T.flow t x := funext (hold x hx)
    rw [← heq]
    exact (hgeometry x).1

private theorem MorseCancel.lower_forward_basins_preserved {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {W : (x : M) → TangentSpace 𝓘(ℝ, E) x}
    (hW : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞ (fun x => (⟨x, W x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (H : Flow ℝ M) (hH : ∀ x, IsMIntegralCurve (fun t => H t x) W)
    (hgeometry :
      ∀ x p,
        Filter.Tendsto (fun t => H t x) Filter.atTop (𝓝 p) ↔
          Filter.Tendsto (fun t => S.flow t x) Filter.atTop (𝓝 p))
    {l : ℝ} (hout : ∀ y, f y ≤ l → T.field y = W y) (y : M) (hy : f y ≤ l) :
    ∀ p,
      Filter.Tendsto (fun t => T.flow t y) Filter.atTop (𝓝 p) ↔
        Filter.Tendsto (fun t => S.flow t y) Filter.atTop (𝓝 p) := by
  have hmono :=
    Smale.FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent y
  have hbound (t : ℝ) (ht : 0 ≤ t) : f (T.flow t y) ≤ l := by
    have hh := hmono ht
    change f (T.flow t y) ≤ f (T.flow 0 y) at hh
    rw [T.flow.map_zero_apply] at hh
    exact hh.trans hy
  have heq : (fun t => T.flow t y) =ᶠ[Filter.atTop] (fun t => H t y) := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    exact
      Degree.FlowCancellation.native_flow_eq_on_positive_halfline (hW.of_le (by simp)) H T.flow hH
        T.integral (fun s hs => hout _ (hbound s hs)) t ht
  intro p
  exact (Filter.tendsto_congr' heq).trans (hgeometry y p)

private theorem AdaptedWindows.reaches_cut_of_forward_holonomy {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (D : { y : M // f y = b } → { y : M // f y = b })
    (hforward :
      ∀ x : { y : M // f y = b },
        ∀ p : M,
          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p))
    (x : { y : M // f y = b }) (y : { z : M // f z = a })
    (horbit : ∃ t : ℝ, S.flow t (D x).val = y.val) :
    x.val ∈ Degree.FlowCancellation.levelBasin T.flow f a := by
  obtain ⟨p, hp, q, hq, -, hytop, hyheight⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf S.smooth S.flow S.integral S.zero
      S.descent S.distinct y.val
  have hqa : f q < a := by simpa only [y.property] using (hyheight (ha y.val y.property)).1
  obtain ⟨t, ht⟩ := horbit
  have hDx : Filter.Tendsto (fun s => S.flow s (D x).val) Filter.atTop (𝓝 q) := by
    rw [← ht] at hytop
    exact (MorseCancel.flow_time_atTop_limit_iff S.flow t (D x).val q).mp hytop
  have hxtop := (hforward x q).mpr hDx
  obtain ⟨r, hr, s, hs, hxback, -, hxheight⟩ :=
    Degree.FlowCancellation.exists_native_descent_endpoints hf T.smooth T.flow T.integral T.zero
      T.descent T.distinct x.val
  have hbr : b < f r := by simpa only [x.property] using (hxheight (hb x.val x.property)).2
  exact
    Degree.FlowCancellation.exists_level_crossing_of_endpoint_limits T.flow hf.continuous hxback
      hxtop (hab.trans hbr) hqa

private theorem
    AdaptedWindows.exists_relative_surgery_cut_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (q : Smale.ManifoldMorse.criticalPoints E f) (z : (S.data q).UpperLevel)
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ p, 0 < ε p) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          (S.data q).UpperLevel (S.data q).UpperLevel ∞)
      (K P : Set (S.data q).UpperLevel),
      IsCompact K →
        Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K P →
          ∃ T : AdaptedWindows E f,
            (∀ p, (T.data p).chart = (S.data p).chart) ∧
              (∀ p, (T.data p).radius < ε p) ∧
                (∀ p ∈ Smale.ManifoldMorse.criticalPoints E f,
                    ∀ᶠ y in 𝓝 p, T.field y = S.field y) ∧
                  (∀ x : (S.data q).UpperLevel,
                      ∀ p : M,
                        Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p) ↔
                          Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p)) ∧
                    (∀ x : (S.data q).UpperLevel,
                        ∀ p : M,
                          Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
                            Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p)) ∧
                      (∀ x ∈ P,
                          Set.range (fun t => T.flow t x.val) =
                            Set.range (fun t => S.flow t x.val)) ∧
                        (∀ x : (S.data q).UpperLevel,
                            ∀ {b : ℝ},
                              b < f q →
                                (∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f) →
                                  ∀ y : { z : M // f z = b },
                                    (∃ t : ℝ, T.flow t x.val = y.val) ↔
                                      ∃ t : ℝ, S.flow t (D x).val = y.val) ∧
                          ∀ p : M,
                            f p ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 p) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 p) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t p) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t p) Filter.atTop (𝓝 v) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  dsimp only
  intro D K P hK I
  obtain ⟨l, u, hl, hu, hband⟩ := S.regular_interval_around_level (S.data q).upper_regular
  have hql : f q < l := by
    by_contra h
    exact
      hband q ⟨le_of_not_gt h, (S.toSurgeryWindows.value_lt_upper q).le.trans hu.le⟩ q.property
  obtain
    ⟨r, C, W, V, H, G, hr, hrbound, hC, hCband, hW, hH, hgeometry, hV, hG, hzero, hdesc, hgerms,
      houtside, hend, hheight, hleft, hright, hprotected⟩ :=
    Degree.FlowSuspension.exists_relative_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hl hu hband (S.data q).upper_regular z D K P hK I
  have hmodel (p : Smale.ManifoldMorse.criticalPoints E f) :
    ∀ᶠ y in 𝓝 p.val, V y = (S.data p).chart.descentField y := by
    filter_upwards [hgerms p.val p.property, S.critical_model_germ p] with y hy hys
    exact hy.trans hys
  obtain ⟨T, hfield, hflow, hcharts, hradii⟩ :=
    MorseCancel.exists_adapted_windows_with_prescribed_flow_lt hf hm S.distinct hV G hG
      (fun y hy => (hzero y).mpr (S.zero y hy)) hdesc (fun p => (S.data p).chart) hmodel ε hε
  obtain ⟨hback₀, hforward₀⟩ :=
    Degree.FlowSuspension.whole_level_basins_of_holonomy S.flow H G Subtype.val D
      (fun x p => (hgeometry x).2.1 p) (fun x p => (hgeometry x).2.2 p) hend hleft hright
  have hback (x : (S.data q).UpperLevel) (p : M) :
    Filter.Tendsto (fun t => T.flow t x.val) Filter.atBot (𝓝 p) ↔
      Filter.Tendsto (fun t => S.flow t x.val) Filter.atBot (𝓝 p) := by
    rw [hflow]
    exact hback₀ x p
  have hforward (x : (S.data q).UpperLevel) (p : M) :
    Filter.Tendsto (fun t => T.flow t x.val) Filter.atTop (𝓝 p) ↔
      Filter.Tendsto (fun t => S.flow t (D x).val) Filter.atTop (𝓝 p) := by
    rw [hflow]
    exact hforward₀ x p
  have hlowexit {b : ℝ} (hb : b < f q) : b < S.toSurgeryWindows.upper q - r := by
    have hr' : r < S.toSurgeryWindows.upper q - l := hrbound
    linarith
  have htransport (x : (S.data q).UpperLevel) {b : ℝ} (hb : b < f q) (y : { z : M // f z = b })
    (hxy : ∃ t : ℝ, T.flow t x.val = y.val) : ∃ t : ℝ, S.flow t (D x).val = y.val := by
    obtain ⟨t, ht⟩ := hxy
    have hstart : f (T.flow 1 x.val) = S.toSurgeryWindows.upper q - r := by
      rw [hflow, hend, hheight]
      rfl
    have htone : 1 < t := by
      by_contra h
      have hh :=
        (Smale.FlowConstruction.antitone_flow_height hf T.flow T.integral T.zero T.descent x.val)
          (le_of_not_gt h)
      change f (T.flow 1 x.val) ≤ f (T.flow t x.val) at hh
      rw [hstart, ht, y.property] at hh
      exact (hlowexit hb).not_ge hh
    have heq : G t x.val = H t (D x).val := by
      calc
        G t x.val = G (t - 1) (G 1 x.val) := by rw [← G.map_add, sub_add_cancel]
        _ = H (t - 1) (H 1 (D x).val) := by
          rw [hend, hright (D x) (t - 1) (sub_nonneg.mpr htone.le)]
        _ = H t (D x).val := by rw [← H.map_add, sub_add_cancel]
    have hmem : H t (D x).val ∈ Set.range (fun s => S.flow s (D x).val) :=
      (hgeometry (D x).val).1 ▸ Set.mem_range_self t
    obtain ⟨s, hs⟩ := hmem
    exact ⟨s, hs.trans (heq.symm.trans (hflow ▸ ht))⟩
  refine ⟨T, hcharts, hradii, ?_, hback, hforward, ?_, ?_, ?_⟩
  · intro p hp
    rw [hfield]
    exact hgerms p hp
  · intro x hx
    rw [hflow]
    have heq : (fun t => G t x.val) = fun t => H t x.val := funext (hprotected x hx)
    rw [heq]
    exact (hgeometry x.val).1
  · intro x b hbq hb y
    refine ⟨htransport x hbq y, ?_⟩
    rintro ⟨t, ht⟩
    obtain ⟨s, hs⟩ :=
      S.reaches_cut_of_forward_holonomy T hf (hbq.trans (S.toSurgeryWindows.value_lt_upper q)) hb
        (S.data q).upper_regular D hforward x y ⟨t, ht⟩
    let y' : { z : M // f z = b } := ⟨T.flow s x.val, hs⟩
    obtain ⟨v, hv⟩ := htransport x hbq y' ⟨s, rfl⟩
    have hshared : S.flow 0 y'.val = S.flow (v - t) y.val := by
      rw [S.flow.map_zero_apply, ← hv, ← ht, ← S.flow.map_add, sub_add_cancel]
    have heq : y'.val = y.val :=
      MorseCancel.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z (hb z hz)) y'.property y.property hshared
    exact ⟨s, heq⟩
  · intro p hp
    have hlow (y : M) (hy : f y ≤ l) : T.field y = W y := by
      rw [hfield]
      exact (houtside y (fun h => (hCband h).1.not_ge hy)).self_of_nhds
    have hb :=
      MorseCancel.lower_backward_basins_preserved S T hf hW H hH hgeometry hlow p
        (hp.trans hql.le)
    exact
      ⟨hb.1, hb.2,
        MorseCancel.lower_forward_basins_preserved S T hf hW H hH (fun x v => (hgeometry x).2.1 v)
          hlow p (hp.trans hql.le)⟩

private theorem
    AdaptedWindows.exists_relative_family_lower_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).UpperLevel))
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => α j))
    (havoid : ∀ j, Disjoint (Set.range (α j)) (Set.range (S.data q).surgery.beltSphere))
    (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∀
      (D :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
          (S.data q).UpperLevel (S.data q).UpperLevel ∞)
      (K : Set (S.data q).UpperLevel),
      IsCompact K →
        Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K
            (Degree.MorseRearrangement.otherSheetImages (fun j => α j) i) →
          (∀ j, Disjoint (Set.range (D ∘ α j)) (Set.range (S.data q).surgery.beltSphere)) →
            ∃ T : AdaptedWindows E f,
              (∀ z, (T.data z).chart = (S.data z).chart) ∧
                (∀ z, (T.data z).radius < ε z) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                    ∃ β δ : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel),
                      MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).lower_regular p
                          (fun j => β j) ∧
                        MorseCancel.IsNativeMiddleBasinFamily T hf (S.data q).lower_regular p
                            (fun j => δ j) ∧
                          (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
                            (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (δ j x).val) ∧
                              (∀ j x, ∃ t : ℝ, S.flow t (D (α j x)).val = (δ j x).val) ∧
                                (∀ j, j ≠ i → δ j = β j) ∧
                                  (∀ j,
                                      j ≠ i →
                                        ∀ x,
                                          Set.range (fun t => T.flow t (α j x).val) =
                                            Set.range (fun t => S.flow t (α j x).val)) ∧
                                    ∀ z : M,
                                      f z ≤ f q →
                                        (∀ x,
                                            Filter.Tendsto (fun t => T.flow t x) Filter.atBot
                                                (𝓝 z) ↔
                                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot
                                                (𝓝 z)) ∧
                                          (∀ x,
                                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot
                                                  (𝓝 z) →
                                                Set.range (fun t => T.flow t x) =
                                                  Set.range (fun t => S.flow t x)) ∧
                                            ∀ v,
                                              Filter.Tendsto (fun t => T.flow t z) Filter.atTop
                                                  (𝓝 v) ↔
                                                Filter.Tendsto (fun t => S.flow t z) Filter.atTop
                                                  (𝓝 v) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  dsimp only
  intro D K hK I hDavoid
  let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  let u :=
    Smale.SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates 2 x₀
  obtain ⟨T, hcharts, hradii, hgerms, hback, hforward, hprotected, hcut, hkeep⟩ :=
    S.exists_relative_surgery_cut_transport hf hm q (α i x₀) ε hε D K
      (Degree.MorseRearrangement.otherSheetImages (fun j => α j) i) hK I
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  have holdreach (j : Fin n) (x : (Smale.Hemisphere.Sphere 2)) :=
    S.belt_complement_reaches_lower_level hf q (α j x)
      (fun h => Set.disjoint_left.mp (havoid j) (Set.mem_range_self x) h)
  have hnewreach (j : Fin n) (x : (Smale.Hemisphere.Sphere 2)) :=
    S.reaches_old_lower_of_belt_avoidance T hf q D hforward (α j x)
      (fun h => Set.disjoint_left.mp (hDavoid j) (Set.mem_range_self x) h)
  obtain ⟨β₀, hβs, hβe, hβi, hβpair, hβflow⟩ :=
    S.exists_native_family_level_transport hf (S.data q).upper_regular (S.data q).lower_regular
      (α i x₀) ((S.data q).surgery.attachingSphere u) (fun j => α j) hs
      (fun j => (he j).injective) hi hpair holdreach
  obtain ⟨δ₀, hδs, hδe, hδi, hδpair, hδflow⟩ :=
    T.exists_native_family_level_transport hf (S.data q).upper_regular (S.data q).lower_regular
      (α i x₀) ((S.data q).surgery.attachingSphere u) (fun j => α j) hs
      (fun j => (he j).injective) hi hpair hnewreach
  let β : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel) := fun j =>
    ⟨β₀ j, (hβs j).continuous⟩
  let δ : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel) := fun j =>
    ⟨δ₀ j, (hδs j).continuous⟩
  have hδold (j : Fin n) (x : (Smale.Hemisphere.Sphere 2)) :
    ∃ t : ℝ, S.flow t (D (α j x)).val = (δ j x).val :=
    (hcut (α j x) (S.toSurgeryWindows.lower_lt_value q) (S.data q).lower_regular (δ j x)).mp
      (hδflow j x)
  have hab := (S.toSurgeryWindows.lower_lt_value q).trans (S.toSurgeryWindows.value_lt_upper q)
  refine ⟨T, hcharts, hradii, hgerms, β, δ, ?_, ?_, hβflow, hδflow, hδold, ?_, ?_, hkeep⟩
  · refine ⟨hβs, hβe, hβi, hβpair, ?_⟩
    intro j
    exact
      S.transported_backward_basin_image hf hab (S.data q).lower_regular (p j).val (hhigh j) (α j)
        (β j) (hfull j) (hβflow j)
  · refine ⟨hδs, hδe, hδi, hδpair, ?_⟩
    intro j
    apply
      T.transported_backward_basin_image hf hab (S.data q).lower_regular (p j).val (hhigh j) (α j)
        (δ j) ?_ (hδflow j)
    intro x
    exact (hfull j x).trans (hback x (p j).val).symm
  · intro j hji
    apply ContinuousMap.ext
    intro x
    obtain ⟨s, hs⟩ := hδold j x
    have hfix : D (α j x) = α j x :=
      I.endpoint_fixed_on (α j x)
        (Degree.MorseRearrangement.mem_otherSheetImages (fun j => α j) i j hji x)
    rw [hfix] at hs
    obtain ⟨t, ht⟩ := hβflow j x
    change S.flow t (α j x).val = (β j x).val at ht
    have hshared : S.flow 0 (δ j x).val = S.flow (s - t) (β j x).val := by
      rw [S.flow.map_zero_apply, ← hs, ← ht, ← S.flow.map_add, sub_add_cancel]
    apply Subtype.ext
    exact
      MorseCancel.native_same_level_orbit_points hf S.smooth S.flow S.integral
        (fun z hz => S.descent z ((S.data q).lower_regular z hz)) (δ j x).property
        (β j x).property hshared
  · intro j hji x
    exact
      hprotected (α j x) (Degree.MorseRearrangement.mem_otherSheetImages (fun j => α j) i j hji x)

private theorem AdaptedWindows.section_class_of_flow_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (β : C((Smale.Hemisphere.Sphere 2), { y : M // f y = b }))
    (α : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (horbit : ∀ x, ∃ t : ℝ, S.flow t (β x).val = (α x).val) :
    SingularMayerVietoris.singularHomologyMap (MorseCancel.sublevelMap f hab.le) 2
        (MorseCancel.middleSectionClass α) =
      MorseCancel.middleSectionClass β := by
  have hm :=
    PeriodTorusHigherHomology.homotopic_homologyMap
      (S.level_transport_homotopic_in_sublevel hf hab ha β α horbit) 2
  have hmaps :
    (MorseCancel.sublevelMap f hab.le).comp ((MorseCancel.levelSublevelMap f le_rfl).comp α) =
      (MorseCancel.levelSublevelMap f hab.le).comp α := by
    apply ContinuousMap.ext
    intro x
    rfl
  rw [MorseCancel.middleSectionClass, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, hmaps, ← hm]
  rfl

private theorem
    MorseCancel.signed_relation_of_regular_cut_transport {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} (S T : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hab : a < b)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (β δ γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = b }))
    (α ζ θ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) (k : ℤ)
    (hβ : ∀ x, ∃ t : ℝ, S.flow t (β x).val = (α x).val)
    (hδ : ∀ x, ∃ t : ℝ, T.flow t (δ x).val = (ζ x).val)
    (hγ : ∀ x, ∃ t : ℝ, S.flow t (γ x).val = (θ x).val)
    (hmap :
      SingularMayerVietoris.singularHomologyMap δ 2 =
        SingularMayerVietoris.singularHomologyMap β 2 +
          k • SingularMayerVietoris.singularHomologyMap γ 2) :
    middleSectionClass ζ = middleSectionClass α + k • middleSectionClass θ := by
  have heval :
    (k • SingularMayerVietoris.singularHomologyMap γ 2) (SphereHomology.unitSphereTopClass 1) =
      k • SingularMayerVietoris.singularHomologyMap γ 2 (SphereHomology.unitSphereTopClass 1) :=
    map_zsmul (LinearMap.evalAddMonoidHom (SphereHomology.unitSphereTopClass 1)) k
      (SingularMayerVietoris.singularHomologyMap γ 2)
  have hclasses : middleSectionClass δ = middleSectionClass β + k • middleSectionClass γ := by
    simp only [middleSectionClass, PeriodTorusHigherHomology.singularHomologyMap_comp,
      LinearMap.comp_apply, hmap, LinearMap.add_apply, heval, map_add, map_zsmul]
  apply (regular_sublevel_inclusion_bijective hf hab.le hband 2).1
  rw [map_add, map_zsmul, T.section_class_of_flow_transport hf hab ha δ ζ hδ,
    S.section_class_of_flow_transport hf hab ha β α hβ,
    S.section_class_of_flow_transport hf hab ha γ θ hγ]
  exact hclasses

private theorem MorseCancel.same_image_sphere_maps_unit {Y : Type} [TopologicalSpace Y]
    (α β : C((Smale.Hemisphere.Sphere 2), Y)) (hα : Topology.IsEmbedding α)
    (hβ : Topology.IsEmbedding β) (hrange : Set.range β = Set.range α) :
    ∃ k : ℤ,
      (k = 1 ∨ k = -1) ∧
        SingularMayerVietoris.singularHomologyMap β 2 =
          k • SingularMayerVietoris.singularHomologyMap α 2 := by
  let e : (Smale.Hemisphere.Sphere 2) ≃ₜ (Smale.Hemisphere.Sphere 2) :=
    hβ.toHomeomorph.trans ((Homeomorph.setCongr hrange).trans hα.toHomeomorph.symm)
  have heq : α.comp (e : C((Smale.Hemisphere.Sphere 2), (Smale.Hemisphere.Sphere 2))) = β := by
    apply ContinuousMap.ext
    intro x
    have hh :=
      congrArg Subtype.val
        (hα.toHomeomorph.apply_symm_apply ((Homeomorph.setCongr hrange) (hβ.toHomeomorph x)))
    exact hh
  have hbij :
    Function.Bijective
      (SingularMayerVietoris.singularHomologyMap
        (e : C((Smale.Hemisphere.Sphere 2), (Smale.Hemisphere.Sphere 2))) 2) :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv e 2).bijective
  obtain ⟨k, hk, hu⟩ :=
    two_sphere_map_unit_of_homology_bijective (Homeomorph.refl (Smale.Hemisphere.Sphere 2))
      (e : C((Smale.Hemisphere.Sphere 2), (Smale.Hemisphere.Sphere 2))) hbij
  rcases hk with rfl | rfl
  · refine ⟨1, Or.inl rfl, ?_⟩
    simp only [one_smul] at hu ⊢
    rw [← heq, PeriodTorusHigherHomology.singularHomologyMap_comp, hu]
    change
      (SingularMayerVietoris.singularHomologyMap α 2).comp
          (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.id (Smale.Hemisphere.Sphere 2)) 2) =
        _
    rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.comp_id]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [neg_one_zsmul] at hu ⊢
    rw [← heq, PeriodTorusHigherHomology.singularHomologyMap_comp, hu, LinearMap.comp_neg]
    change
      -((SingularMayerVietoris.singularHomologyMap α 2).comp
            (SingularMayerVietoris.singularHomologyMap
              (ContinuousMap.id (Smale.Hemisphere.Sphere 2)) 2)) =
        _
    rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.comp_id]

private theorem
    MorseCancel.same_image_section_classes_unit {M : Type} [TopologicalSpace M]
     {f : M → ℝ} {a : ℝ}
    (α β : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) (hα : Topology.IsEmbedding α)
    (hβ : Topology.IsEmbedding β) (hrange : Set.range β = Set.range α) :
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧ middleSectionClass β = k • middleSectionClass α := by
  obtain ⟨k, hk, hm⟩ := same_image_sphere_maps_unit α β hα hβ hrange
  have heval :
    (k • SingularMayerVietoris.singularHomologyMap α 2) (SphereHomology.unitSphereTopClass 1) =
      k • SingularMayerVietoris.singularHomologyMap α 2 (SphereHomology.unitSphereTopClass 1) :=
    map_zsmul (LinearMap.evalAddMonoidHom (SphereHomology.unitSphereTopClass 1)) k
      (SingularMayerVietoris.singularHomologyMap α 2)
  refine ⟨k, hk, ?_⟩
  simp only [middleSectionClass, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply, hm, heval, map_zsmul]

private theorem MorseCancel.nativeMiddleBasinFamily_replace_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n : ℕ}
    (q : Smale.ManifoldMorse.criticalPoints E f)
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (αq βq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily : IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (hrange : Set.range βq = Set.range αq) :
    let _ := Smale.RegularLevel.chartedSpace hf ha
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ βq →
      Topology.IsClosedEmbedding βq →
        (∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) βq x)) →
          IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases βq (fun j => α j)) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  dsimp only
  intro hβs hβe hβi
  have hr (j : Fin (n + 1)) :
    Set.range (Fin.cases βq (fun j => α j) j) = Set.range (Fin.cases αq (fun j => α j) j) := by
    cases j using Fin.cases with
    | zero => exact hrange
    | succ j => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    cases j using Fin.cases with
    | zero => exact hβs
    | succ j => exact hfamily.1 j.succ
  · intro j
    cases j using Fin.cases with
    | zero => exact hβe
    | succ j => exact hfamily.2.1 j.succ
  · intro j
    cases j using Fin.cases with
    | zero => exact hβi
    | succ j => exact hfamily.2.2.1 j.succ
  · intro j k hjk
    rw [hr j, hr k]
    exact hfamily.2.2.2.1 hjk
  · intro j y
    rw [hr j]
    exact hfamily.2.2.2.2 j y

public
theorem MorseCancel.mul_transvection_surjective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (hij : i ≠ j) (k : ℤ) (hA : Function.Surjective A.mulVec) :
    Function.Surjective (A * Matrix.transvection i j k).mulVec := by
  intro y
  obtain ⟨z, hz⟩ := hA y
  refine ⟨(Matrix.transvection i j (-k)).mulVec z, ?_⟩
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.transvection_mul_transvection_same i j hij,
    add_neg_cancel, Matrix.transvection_zero, Matrix.mul_one]
  exact hz

private theorem
    MorseCancel.eq_mul_transvection_of_columns {r n : ℕ} (A A' : Matrix (Fin r) (Fin n) ℤ)
    (i j : Fin n) (k : ℤ) (hchanged : ∀ u, A' u j = A u j + k * A u i)
    (hother : ∀ u v, v ≠ j → A' u v = A u v) : A' = A * Matrix.transvection i j k := by
  funext u v
  by_cases hv : v = j
  · subst v
    exact (hchanged u).trans (Matrix.mul_transvection_apply_same i j u k A).symm
  · exact (hother u v hv).trans (Matrix.mul_transvection_apply_of_ne i j u v hv k A).symm

private theorem
    MorseCancel.exists_sheet_arc_tube_with_normal_change {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a) (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞)
    (hΦ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source)
    (hΦ₁ : ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0)) (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {O : Set M} (hO : IsOpen O) (haO : Set.MapsTo a (Set.Icc (0 : ℝ) 1) O)
    (C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) :
    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
            𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
          Set.Icc (0 : ℝ) 1 ×ˢ
                Metric.closedBall (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                  ε ⊆
              Φ.source ∧
            (∀ t : ℝ, Φ (t, 0) = a t) ∧
              ((Φ :
                    (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                      M) =ᶠ[𝓝
                    (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                  Φ₀) ∧
                ((Φ :
                      (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                        M) =ᶠ[𝓝
                      ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                    linearTransverseChart (C.prodCongr R) Φ₁) ∧
                  Φ.target ⊆ O := by
  let Φ₂ :=
    linearTransverseChart (C.prodCongr (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))))
      Φ₁
  have hΦ₂ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source _ Φ₁ 1).mpr hΦ₁
  have hright₂ : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₂ (t, 0) := by
    filter_upwards [hright] with t ht
    exact ht.trans (linearTransverseChart_axis _ Φ₁ t).symm
  obtain ⟨R, ε, hε, Φ, hprod, haxis, hgl, hgr, htarget⟩ :=
    exists_sheet_arc_tube ha hinj hi hdim Φ₀ Φ₂ hΦ₀ hΦ₂ hleft hright₂ hO haO
  refine ⟨R, ε, hε, Φ, hprod, haxis, hgl, ?_, htarget⟩
  filter_upwards [hgr] with z hz
  exact hz

private theorem MorseCancel.exists_clean_sheet_arc_tube_with_normal_change {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {a : ℝ → M}
    (ha : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ a) (hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1))
    (hi : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) a t))
    (hdim : Module.finrank ℝ E = 5)
    (Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞)
    (hΦ₀ : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source)
    (hΦ₁ : ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source)
    (hleft : a =ᶠ[𝓝 (0 : ℝ)] fun t => Φ₀ (t, 0)) (hright : a =ᶠ[𝓝 (1 : ℝ)] fun t => Φ₁ (t, 0))
    {S T O : Set M} (hS : IsClosed S) (hT : IsClosed T)
    (hrec₀ : ∀ z ∈ Φ₀.source, Φ₀ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hrec₁ : ∀ z ∈ Φ₁.source, Φ₁ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0)
    (hcount₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ S ↔ t = 0)
    (hcount₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, a t ∈ T ↔ t = 1) (hO : IsOpen O)
    (haO : Set.MapsTo a (Set.Icc (0 : ℝ) 1) O)
    (C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) :
    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
      0 < ε ∧
        ∃ Φ :
          PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
            𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
          Set.Icc (0 : ℝ) 1 ×ˢ
                Metric.closedBall (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                  ε ⊆
              Φ.source ∧
            (∀ t : ℝ, Φ (t, 0) = a t) ∧
              ((Φ :
                    (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                      M) =ᶠ[𝓝
                    (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                  Φ₀) ∧
                ((Φ :
                      (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) →
                        M) =ᶠ[𝓝
                      ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))]
                    linearTransverseChart (C.prodCongr R) Φ₁) ∧
                  (∀ z ∈ Φ.source, Φ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                    (∀ z ∈ Φ.source, Φ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0) ∧ Φ.target ⊆ O := by
  obtain ⟨R, r, hr, Ψ, hΨprod, haxis, hgl, hgr, hΨO⟩ :=
    exists_sheet_arc_tube_with_normal_change ha hinj hi hdim Φ₀ Φ₁ hΦ₀ hΦ₁ hleft hright hO haO C
  let Φ₂ := linearTransverseChart (C.prodCongr R) Φ₁
  have hΦ₂ :
    ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₂.source :=
    (linearTransverseChart_axis_source _ Φ₁ 1).mpr hΦ₁
  have hrec₂ : ∀ z ∈ Φ₂.source, Φ₂ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    intro z hz
    change Φ₁ (z.1, (C z.2.1, R z.2.2)) ∈ T ↔ _
    rw [hrec₁ (z.1, (C z.2.1, R z.2.2)) hz.2, map_eq_zero_iff C C.injective]
  have hlocal₀ :
    ∀ᶠ z : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) in
      𝓝 (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))),
      Ψ z ∈ S ↔ z.1 = 0 ∧ z.2.2 = 0 := by
    filter_upwards [hgl, Φ₀.open_source.mem_nhds hΦ₀] with z he hz
    rw [he]
    exact hrec₀ z hz
  have hlocal₁ :
    ∀ᶠ z : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) in
      𝓝 ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))),
      Ψ z ∈ T ↔ z.1 = 1 ∧ z.2.1 = 0 := by
    filter_upwards [hgr, Φ₂.open_source.mem_nhds hΦ₂] with z he hz
    rw [he]
    exact hrec₂ z hz
  have hzero :
    Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))} ⊆
      Ψ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hΨprod ⟨ht, Metric.mem_closedBall_self hr.le⟩
  have haway₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≠ 0 → Ψ (t, 0) ∉ S := by
    intro t ht hne hh
    rw [haxis] at hh
    exact hne ((hcount₀ t ht).mp hh)
  have haway₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≠ 1 → Ψ (t, 0) ∉ T := by
    intro t ht hne hh
    rw [haxis] at hh
    exact hne ((hcount₁ t ht).mp hh)
  obtain ⟨ε, hε, Φ, hprod, hformula, hΦΨ, hrecS, hrecT⟩ :=
    exists_clean_axis_tube_restriction Ψ CompactIccSpace.isCompact_Icc hzero hS hT 0 1
      {v : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))) | v.2 = 0}
      {v : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))) | v.1 = 0} hlocal₀ hlocal₁
      haway₀ haway₁
  refine
    ⟨R, ε, hε, Φ, hprod, fun t => (hformula _).trans (haxis t), ?_, ?_, hrecS, hrecT,
      hΦΨ.trans hΨO⟩
  · filter_upwards [hgl] with z hz
    exact (hformula z).trans hz
  · filter_upwards [hgr] with z hz
    exact (hformula z).trans hz

private theorem MorseCancel.exists_relative_sheet_passages_with_normal_change {E M X Y Z : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [IsManifold (𝓡 2) ∞ X] [CompactSpace X]
    [SecondCountableTopology X] [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y]
    [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y] [SecondCountableTopology Y] [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z]
    {f : X → M} {g : Y → M} {b : Z → M} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g) (hfe : Topology.IsEmbedding f)
    (hge : Topology.IsEmbedding g) (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (Set.range f) (Set.range g)) (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b)
    (hbc : IsClosed (Set.range b)) (hdim : Module.finrank ℝ E = 5) (x : X) (y : Y)
    (hbx : f x ∉ Set.range b) (hby : g y ∉ Set.range b) (γ : Path (f x) (g y)) :
    ∃ Φ₀ Φ₁ :
      PartialDiffeomorph 𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
        𝓘(ℝ, E) (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
      (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₀.source ∧
        ((1 : ℝ), (0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ₁.source ∧
          Φ₀ 0 = f x ∧
            Φ₁ (1, 0) = g y ∧
              (∀ z ∈ Φ₀.source, Φ₀ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                (∀ z ∈ Φ₁.source, Φ₁ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                  ∀ C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)),
                    ∃ (R : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2))) (ε : ℝ),
                      0 < ε ∧
                        ∃ Φ :
                          PartialDiffeomorph
                            𝓘(ℝ, (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))))
                            𝓘(ℝ, E)
                            (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)))) M ∞,
                          ∃ A : LongitudinalTubeMotion Φ,
                            Set.Icc (0 : ℝ) 1 ×ˢ
                                  Metric.closedBall
                                    (0 :
                                      ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))
                                    ε ⊆
                                Φ.source ∧
                              Φ 0 = f x ∧
                                Φ (1, 0) = g y ∧
                                  ((Φ :
                                        (ℝ ×
                                            ((EuclideanSpace ℝ (Fin 2)) ×
                                              (EuclideanSpace ℝ (Fin 2)))) →
                                          M) =ᶠ[𝓝
                                        (0 :
                                          (ℝ ×
                                            ((EuclideanSpace ℝ (Fin 2)) ×
                                              (EuclideanSpace ℝ (Fin 2)))))]
                                      Φ₀) ∧
                                    ((Φ :
                                          (ℝ ×
                                              ((EuclideanSpace ℝ (Fin 2)) ×
                                                (EuclideanSpace ℝ (Fin 2)))) →
                                            M) =ᶠ[𝓝
                                          ((1 : ℝ),
                                            (0 :
                                              ((EuclideanSpace ℝ (Fin 2)) ×
                                                (EuclideanSpace ℝ (Fin 2)))))]
                                        linearTransverseChart (C.prodCongr R) Φ₁) ∧
                                      (∀ z ∈ Φ.source, Φ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0) ∧
                                        (∀ z ∈ Φ.source,
                                            Φ z ∈ Set.range g ↔ z.1 = 1 ∧ z.2.1 = 0) ∧
                                          Φ.target ⊆ (Set.range b)ᶜ ∧
                                            (∀ t z, z ∈ Set.range b → A.family (t, z) = z) ∧
                                              (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                                  ∀ u : X,
                                                    ∀ v : Y,
                                                      A.family (t, f u) = g v ↔
                                                        t = A.time ∧ u = x ∧ v = y) ∧
                                                Smale.NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2))
                                                  (𝓡 2) 𝓘(ℝ, E)
                                                  (fun p : ℝ × X => A.family (p.1, f p.2)) g
                                                  (A.time, x) y := by
  have hx : f x ∉ Set.range g := fun h => (Set.disjoint_left.mp hdisj) ⟨x, rfl⟩ h
  have hy : g y ∉ Set.range f := fun h => (Set.disjoint_left.mp hdisj) h ⟨y, rfl⟩
  obtain
    ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, hrec₁, a, ha, hleft, hright, hemb, hi, hcount₀, hcount₁,
      haO⟩ :=
    exists_clean_two_sheet_arc_avoiding hf hg hfe hge hfi hgi hb hbc hdim x y hx hy hbx hby γ
  refine ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, hrec₁, ?_⟩
  intro C
  have hinj : Set.InjOn a (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) hst)
  obtain ⟨R, ε, hε, Φ, hprod, haxis, hgl, hgr, hrecf, hrecg, hΦO⟩ :=
    exists_clean_sheet_arc_tube_with_normal_change ha hinj hi hdim Φ₀ Φ₁ hΦ₀ hΦ₁ hleft hright
      (isCompact_range hf.continuous).isClosed (isCompact_range hg.continuous).isClosed hrec₀
      hrec₁ hcount₀ hcount₁ hbc.isOpen_compl haO C
  have hzero :
    Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))} ⊆
      Φ.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hprod ⟨ht, Metric.mem_closedBall_self hε.le⟩
  have h0 : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source :=
    hzero ⟨⟨le_rfl, zero_le_one⟩, rfl⟩
  have hfx : Φ 0 = f x := (haxis 0).trans (hleft.eq_of_nhds.trans hΦx)
  have hgy : Φ (1, 0) = g y := (haxis 1).trans (hright.eq_of_nhds.trans hΦy)
  obtain ⟨A⟩ := nonempty_longitudinalTubeMotion Φ hzero
  refine
    ⟨R, ε, hε, Φ, A, hprod, hfx, hgy, hgl, hgr, hrecf, hrecg, hΦO, ?_,
      A.whole_sheet_crossing_iff hfe.injective hge.injective hdisj hrecf hrecg x y hfx hgy h0,
      A.whole_sheet_transverse (hf.mdifferentiable (by simp) x) (hg.mdifferentiable (by simp) y)
        (hfi x) (hgi y) hrecf hrecg hfx hgy h0⟩
  intro t z hz
  exact A.fixed_outside_target t z (fun h => hΦO h hz)

private theorem
    MorseCancel.LongitudinalTubeMotion.sheet_trace_germ_of_endpoint_germs {U V E M X : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [TopologicalSpace X] {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞}
    (A : MorseCancel.LongitudinalTubeMotion Φ)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞) (C : U ≃L[ℝ] U)
    (R : V ≃L[ℝ] V) {f : X → M} {x : X} (hf : ContinuousAt f x)
    (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) (hΦ₀ : (0 : ℝ × (U × V)) ∈ Φ₀.source) (hx : Φ₀ 0 = f x)
    (hrec : ∀ z ∈ Φ₀.source, Φ₀ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hleft : (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 (0 : ℝ × (U × V))] Φ₀)
    (hright :
      (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 ((1 : ℝ), (0 : U × V))]
        MorseCancel.linearTransverseChart (C.prodCongr R) Φ₁) :
    (fun p : ℝ × X => A.family (p.1, f p.2)) =ᶠ[𝓝 (A.time, x)] fun p =>
      Φ₁ (Real.smoothTransition p.1 * A.destination, (C (Φ₀.symm (f p.2)).2.1, 0)) := by
  let W := ℝ × (U × V)
  let a : X → W := Φ₀.symm ∘ f
  have hfx : f x ∈ Φ₀.target := hx ▸ Φ₀.map_source hΦ₀
  have ha : ContinuousAt a x :=
    (Φ₀.symm.contMDiffOn_toFun.continuousOn.continuousAt (Φ₀.open_target.mem_nhds hfx)).comp hf
  have ha0 : a x = 0 := (congrArg Φ₀.symm hx).symm.trans (Φ₀.left_inv hΦ₀)
  have hat : Filter.Tendsto a (𝓝 x) (𝓝 (0 : W)) := by simpa only [ha0] using ha.tendsto
  have hfn : ∀ᶠ q in 𝓝 x, f q ∈ Φ₀.target := hf.eventually (Φ₀.open_target.mem_nhds hfx)
  have hplane : ∀ᶠ q in 𝓝 x, (a q).1 = 0 ∧ (a q).2.2 = 0 := by
    filter_upwards [hfn] with q hq
    exact (hrec (a q) (Φ₀.map_target hq)).mp ⟨q, (Φ₀.right_inv hq).symm⟩
  have hat' : Filter.Tendsto (fun p : ℝ × X => a p.2) (𝓝 (A.time, x)) (𝓝 (0 : W)) :=
    hat.comp continuous_snd.continuousAt
  have hpair :
    Filter.Tendsto (fun p : ℝ × X => (p.1, a p.2)) (𝓝 (A.time, x)) (𝓝 (A.time, (0 : W))) :=
    continuous_fst.continuousAt.prodMk_nhds hat'
  let z : ℝ × X → W := fun p => (Real.smoothTransition p.1 * A.destination, ((a p.2).2.1, 0))
  have hap : ContinuousAt (fun p : ℝ × X => a p.2) (A.time, x) :=
    ContinuousAt.comp (g := a) (f := fun p : ℝ × X => p.2) ha continuousAt_snd
  have hz : ContinuousAt z (A.time, x) :=
    ((Real.smoothTransition.continuous.continuousAt.comp continuousAt_fst).mul
          continuousAt_const).prodMk
      (hap.snd.fst.prodMk continuousAt_const)
  have hz0 : z (A.time, x) = (1, 0) := by
    simp only [z, A.time_value, ha0, Prod.fst_zero, Prod.snd_zero]
    rfl
  have hzt : Filter.Tendsto z (𝓝 (A.time, x)) (𝓝 ((1 : ℝ), (0 : U × V))) := by
    simpa only [hz0] using hz.tendsto
  filter_upwards [hpair.eventually (A.native_germ h0 A.time), hat'.eventually hleft,
    continuous_snd.continuousAt.eventually hfn, continuous_snd.continuousAt.eventually hplane,
    hzt.eventually hright] with p hm hl hf' hp hr
  have hpoint : Φ (a p.2) = f p.2 := hl.trans (Φ₀.right_inv hf')
  calc
    A.family (p.1, f p.2) = A.family (p.1, Φ (a p.2)) :=
      congrArg (fun y => A.family (p.1, y)) hpoint.symm
    _ = Φ ((a p.2).1 + Real.smoothTransition p.1 * A.destination, (a p.2).2) := hm
    _ = Φ (z p) := by
      apply congrArg Φ
      rw [hp.1, zero_add]
      exact Prod.ext rfl (Prod.ext rfl hp.2)
    _ = Φ₁ (Real.smoothTransition p.1 * A.destination, (C (Φ₀.symm (f p.2)).2.1, 0)) := by
      change Φ (z p) = Φ₁ (Real.smoothTransition p.1 * A.destination, (C (a p.2).2.1, 0))
      rw [hr]
      change Φ₁ (Real.smoothTransition p.1 * A.destination, (C (a p.2).2.1, R 0)) = _
      rw [map_zero]

private theorem MorseCancel.exists_centered_passage_clock {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      D 0 = 0 ∧
        D 1 = 1 ∧
          D (1 / 2) = τ ∧
            StrictMono D ∧
              Set.MapsTo D (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) ∧
                ((D : ℝ → ℝ) =ᶠ[𝓝 (1 / 2 : ℝ)] fun t => t + (τ - 1 / 2)) ∧
                  HasDerivAt (D : ℝ → ℝ) 1 (1 / 2) := by
  obtain ⟨D, hfix, hgerm, hpoint, hmono, -⟩ :=
    Degree.MorseRearrangement.exists_increasing_interval_translation
      (show (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 by constructor <;> norm_num) hτ
  have h0 : D 0 = 0 := hfix 0 (by simp)
  have h1 : D 1 = 1 := hfix 1 (by simp)
  refine ⟨D, h0, h1, hpoint, hmono, ?_, hgerm, ?_⟩
  · intro t ht
    exact ⟨h0 ▸ hmono.monotone ht.1, h1 ▸ hmono.monotone ht.2⟩
  · exact ((hasDerivAt_id (1 / 2 : ℝ)).add_const (τ - 1 / 2)).congr_of_eventuallyEq hgerm

private theorem MorseCancel.exists_radial_link_meridian_with_derivative {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (H : C(ℝ × (Smale.Hemisphere.Sphere 2), d.UpperLevel)) {τ : ℝ} (hτ : τ ∈ Set.Ioo (0 : ℝ) 1)
    (x₀ : (Smale.Hemisphere.Sphere 2)) (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1)
    (hpoint : d.surgery.beltSphere v = H (τ, x₀))
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : (Smale.Hemisphere.Sphere 2),
          H (t, x) ∈ Set.range d.surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (hL :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) => d.beltNormal (H (radialParameterChart τ x₀ z)))
        L.toContinuousLinearMap 0) :
    let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ H (τ, x₀) →
      ∃ (ε : ℝ) (hε : 0 < ε) (hεx : ε < Real.exp τ),
        ∃ (w : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (β :
          C((Smale.Hemisphere.Sphere 2), Metric.sphere (0 : d.chart.NegativeCoordinates) 1)),
          SingularMayerVietoris.singularHomologyMap β 2 =
              SingularMayerVietoris.singularHomologyMap
                (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 ∧
            ((Degree.PassageHomology.puncturedPassageTrace H (Set.range d.surgery.beltSphere) hτ
                      x₀ hcross).comp
                  (Degree.PassageHomology.cylinderLink τ x₀ ε hε hεx)).Homotopic
              ((nativeBeltTubeMeridian d w (1 / 2) (by norm_num) (by norm_num)).comp β) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hg
  let Ψ := radialParameterChart τ x₀
  have hΨ0 : (0 : (EuclideanSpace ℝ (Fin 3))) ∈ Ψ.source :=
    radialParameterChart_zero_mem_source τ x₀
  have hΨ : ContMDiffAt (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Ψ 0 :=
    Ψ.contMDiffOn_toFun.contMDiffAt (Ψ.open_source.mem_nhds hΨ0)
  have hΨc : ContinuousAt Ψ 0 := hΨ.continuousAt
  have htime :
    (fun z : (EuclideanSpace ℝ (Fin 3)) => (Ψ z).1) ⁻¹' Set.Ioo (0 : ℝ) 1 ∈
      𝓝 (0 : (EuclideanSpace ℝ (Fin 3))) := by
    apply hΨc.fst.preimage_mem_nhds
    apply isOpen_Ioo.mem_nhds
    simpa only [Ψ, radialParameterChart_zero] using hτ
  let t :=
    Ψ.source ∩
      (Metric.ball (0 : (EuclideanSpace ℝ (Fin 3))) (Real.exp τ) ∩
        (fun z : (EuclideanSpace ℝ (Fin 3)) => (Ψ z).1) ⁻¹' Set.Ioo (0 : ℝ) 1)
  have ht : t ∈ 𝓝 (0 : (EuclideanSpace ℝ (Fin 3))) :=
    Filter.inter_mem (Ψ.open_source.mem_nhds hΨ0)
      (Filter.inter_mem (Metric.ball_mem_nhds _ (Real.exp_pos τ)) htime)
  have hc : ContinuousOn (fun z : (EuclideanSpace ℝ (Fin 3)) => H (Ψ z)) t :=
    H.continuous.comp_continuousOn (Ψ.contMDiffOn_toFun.continuousOn.mono Set.inter_subset_left)
  have hcenter : H (Ψ 0) = d.surgery.beltSphere v := by
    rw [show Ψ 0 = (τ, x₀) from radialParameterChart_zero τ x₀]
    exact hpoint.symm
  obtain ⟨s, hs, hst, hcs, hdomain, hsmall⟩ :=
    exists_small_native_belt_neighborhood d (fun z : (EuclideanSpace ℝ (Fin 3)) => H (Ψ z)) v ht
      hc hcenter
  have hgΨ : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ H (Ψ 0) := by
    rw [show Ψ 0 = (τ, x₀) from radialParameterChart_zero τ x₀]
    exact hg
  have hnormal :=
    d.contMDiffOn_beltNormal hf |>.contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  have hnormal' :
    ContMDiffAt 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, d.chart.NegativeCoordinates) ∞ d.beltNormal
      (H (Ψ 0)) := by
    rw [hcenter]
    exact hnormal
  have hF : ContDiffAt ℝ ∞ (fun z : (EuclideanSpace ℝ (Fin 3)) => d.beltNormal (H (Ψ z))) 0 :=
    (ContMDiffAt.comp (g := d.beltNormal) (f := fun z : (EuclideanSpace ℝ (Fin 3)) => H (Ψ z)) 0
        hnormal' (hgΨ.comp 0 hΨ)).contDiffAt
  have hF0 : d.beltNormal (H (Ψ 0)) = 0 := by rw [hcenter, d.beltNormal_belt]
  obtain ⟨b⟩ := Smale.LocalDegree.nonempty_boundaryData_of_contDiffAt L hL hF0 hs hF
  have hball (u : (Smale.Hemisphere.Sphere 2)) : b.radius • u.val ∈ s := by
    apply b.ball_subset
    rw [mem_closedBall_zero_iff, Smale.LocalDegree.norm_radius_smul b.radius b.radius_pos u]
  have hεx : b.radius < Real.exp τ := by
    have hh := (hst (hball x₀)).2.1
    rwa [mem_ball_zero_iff, Smale.LocalDegree.norm_radius_smul b.radius b.radius_pos x₀] at hh
  obtain ⟨J, hJ, w, hmeridian⟩ :=
    normal_boundary_homotopic_native_meridian d (fun z : (EuclideanSpace ℝ (Fin 3)) => H (Ψ z)) b
      hcs hdomain hsmall (1 / 2) (by norm_num) (by norm_num)
  have hlink :
    (Degree.PassageHomology.puncturedPassageTrace H (Set.range d.surgery.beltSphere) hτ x₀
            hcross).comp
        (Degree.PassageHomology.cylinderLink τ x₀ b.radius b.radius_pos hεx) =
      J := by
    apply ContinuousMap.ext
    intro u
    apply Subtype.ext
    have htimeu :
      (Degree.PassageHomology.cylinderLink τ x₀ b.radius b.radius_pos hεx u).val.1 ∈
        Set.Icc (0 : ℝ) 1 := by
      rw [← radialParameterChart_link τ x₀ b.radius b.radius_pos hεx u]
      exact ⟨(hst (hball u)).2.2.1.le, (hst (hball u)).2.2.2.le⟩
    rw [ContinuousMap.comp_apply,
      Degree.PassageHomology.puncturedPassageTrace_on_interval H (Set.range d.surgery.beltSphere)
        hτ x₀ hcross _ htimeu,
      hJ]
    rw [show Ψ (b.radius • u.val) = _ from
        radialParameterChart_link τ x₀ b.radius b.radius_pos hεx u]
  refine ⟨b.radius, b.radius_pos, hεx, w, b.normalizedMap, b.normalized_homology_compare 2, ?_⟩
  rw [hlink]
  exact hmeridian

private theorem AdaptedWindows.exists_passage_derivative_class_addition {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : Smale.ManifoldMorse.criticalPoints E f)
    [Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1)]
    (H : C(ℝ × (Smale.Hemisphere.Sphere 2), (S.data p).UpperLevel)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (x₀ : (Smale.Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (hpoint : (S.data p).surgery.beltSphere v = H (τ, x₀))
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : (Smale.Hemisphere.Sphere 2),
          H (t, x) ∈ Set.range (S.data p).surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (S.data p).chart.NegativeCoordinates)
    (hL :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) =>
          (S.data p).beltNormal (H (MorseCancel.radialParameterChart τ x₀ z)))
        L.toContinuousLinearMap 0) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ H (τ, x₀) →
      ∃ D :
        C(((Set.range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
          (S.data p).LowerLevel),
        (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
          (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
            let G :=
              D.comp
                (Degree.PassageHomology.puncturedPassageTrace H
                  (Set.range (S.data p).surgery.beltSphere) hτ x₀ hcross)
            SingularMayerVietoris.singularHomologyMap
                (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
              SingularMayerVietoris.singularHomologyMap
                  (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
                SingularMayerVietoris.singularHomologyMap
                  ((S.data p).surgery.attachingSphere.comp
                    (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
                  2 := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  dsimp only
  intro hg
  let e :
    (Smale.Hemisphere.Sphere 2) ≃ₜ Metric.sphere (0 : (S.data p).chart.NegativeCoordinates) 1 :=
    (Smale.SphereCoordinates.standardParametrization (S.data p).chart.NegativeCoordinates
        2).toHomeomorph
  obtain ⟨D, horbit, hunique, hmeridian, _, hrelation⟩ :=
    S.exists_lower_passage_homology_relation hf p (e x₀) v H hτ x₀ hcross
  obtain ⟨ε, hε, hεx, w, β, hβ, hlink⟩ :=
    MorseCancel.exists_radial_link_meridian_with_derivative (S.data p) hf H hτ x₀ v hpoint hcross
      L hL hg
  let σ : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hσ : 0 < (σ : ℝ) := by norm_num [σ]
  have htube :
    MorseCancel.nativeBeltTubeMeridian (S.data p) w (1 / 2) (by norm_num) (by norm_num) =
      MorseCancel.nativeUpperMeridianInComplement S p w σ hσ :=
    MorseCancel.nativeBeltTubeMeridian_eq S p w (1 / 2) (by norm_num) (by norm_num)
  rw [htube] at hlink
  let G :=
    D.comp
      (Degree.PassageHomology.puncturedPassageTrace H (Set.range (S.data p).surgery.beltSphere) hτ
        x₀ hcross)
  have hDlink :
    (G.comp (Degree.PassageHomology.cylinderLink τ x₀ ε hε hεx)).Homotopic
      ((D.comp (MorseCancel.nativeUpperMeridianInComplement S p w σ hσ)).comp β) :=
    (ContinuousMap.Homotopic.refl D).comp hlink
  have hatt :
    ((D.comp (MorseCancel.nativeUpperMeridianInComplement S p w σ hσ)).comp β).Homotopic
      ((S.data p).surgery.attachingSphere.comp β) :=
    (hmeridian w σ hσ).comp (ContinuousMap.Homotopic.refl β)
  have hlinkMap := PeriodTorusHigherHomology.homotopic_homologyMap (hDlink.trans hatt) 2
  have hderivativeMap :
    SingularMayerVietoris.singularHomologyMap ((S.data p).surgery.attachingSphere.comp β) 2 =
      SingularMayerVietoris.singularHomologyMap
        ((S.data p).surgery.attachingSphere.comp
          (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
        2 := by
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
      PeriodTorusHigherHomology.singularHomologyMap_comp, hβ]
  refine ⟨D, horbit, hunique, ?_⟩
  have hh := hrelation ε hε hεx
  change
    SingularMayerVietoris.singularHomologyMap
        (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
      SingularMayerVietoris.singularHomologyMap
          (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
        SingularMayerVietoris.singularHomologyMap
          (G.comp (Degree.PassageHomology.cylinderLink τ x₀ ε hε hεx)) 2 at hh
  rw [hlinkMap, hderivativeMap] at hh
  exact hh

private theorem MorseCancel.attaching_contributions_opposite_of_relative_det_neg {N Y : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] [TopologicalSpace Y]
    (a : C(Metric.sphere (0 : N) 1, Y)) (L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] N)
    (hdet : (L₁.trans L₀.symm).toLinearEquiv.toLinearMap.det < 0) :
    SingularMayerVietoris.singularHomologyMap
        (a.comp (Smale.LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective)) 2 =
      -SingularMayerVietoris.singularHomologyMap
          (a.comp (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective)) 2 :=
  by
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp]
  apply LinearMap.ext
  intro u
  have h := Smale.LinearSphereAction.homology_relative_sign 1 L₁ L₀ 1 u
  rw [sign_eq_neg_one_iff.mpr hdet] at h
  simp only [SignType.coe_neg, SignType.coe_one, neg_one_zsmul] at h
  change
    SingularMayerVietoris.singularHomologyMap a 2
        (SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective) 2 u) =
      -SingularMayerVietoris.singularHomologyMap a 2
          (SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 u)
  rw [h, map_neg]

private def
    MorseCancel.passageNormalProduct {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] (c : ℝ)
    (hc : c ≠ 0) (C : U ≃L[ℝ] U) : (ℝ × U) ≃L[ℝ] (ℝ × U) :=
  (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv.prodCongr C

private theorem
    MorseCancel.passageNormalProduct_det {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] (c : ℝ) (hc : c ≠ 0) (C : U ≃L[ℝ] U) :
    (passageNormalProduct c hc C).toLinearMap.det = c * C.toLinearMap.det := by
  have hscale :
    (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toLinearMap = c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ) := by
    ext
    rfl
  change LinearMap.det ((LinearEquiv.smulOfNeZero ℝ ℝ c hc).toLinearMap.prodMap C.toLinearMap) = _
  rw [LinearMap.det_prodMap, hscale, LinearMap.det_smul, Module.finrank_self, pow_one,
    LinearMap.det_id, mul_one]

private theorem MorseCancel.relative_normal_frame_det {U N : Type} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N)
    (Q₀ Q₁ : (ℝ × U) ≃L[ℝ] (ℝ × U)) :
    (((P.trans Q₁).trans B).trans ((P.trans Q₀).trans B).symm).toLinearMap.det =
      Q₀.toLinearMap.det⁻¹ * Q₁.toLinearMap.det := by
  have heq :
    (((P.trans Q₁).trans B).trans ((P.trans Q₀).trans B).symm).toLinearMap =
      P.symm.toLinearMap.comp ((Q₀.symm.toLinearMap.comp Q₁.toLinearMap).comp P.toLinearMap) := by
    apply LinearMap.ext
    intro z
    change P.symm (Q₀.symm (B.symm (B (Q₁ (P z))))) = P.symm (Q₀.symm (Q₁ (P z)))
    rw [B.symm_apply_apply]
  rw [heq]
  have hconj := LinearMap.det_conj (Q₀.symm.toLinearMap.comp Q₁.toLinearMap) P.symm.toLinearEquiv
  calc
    _ = (Q₀.symm.toLinearMap.comp Q₁.toLinearMap).det := hconj
    _ = _ := by
      rw [LinearMap.det_comp]
      exact
        congrArg (fun t : ℝ => t * Q₁.toLinearMap.det) (LinearEquiv.det_coe_symm Q₀.toLinearEquiv)

private theorem MorseCancel.passage_normal_relative_det_neg {U N : Type} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [FiniteDimensional ℝ U] [NormedAddCommGroup N] [NormedSpace ℝ N]
    (P : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (ℝ × U)) (B : (ℝ × U) ≃L[ℝ] N) {c₀ c₁ : ℝ}
    (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (C : U ≃L[ℝ] U) (hC : C.toLinearMap.det < 0) :
    (((P.trans (passageNormalProduct c₁ hc₁.ne' C)).trans B).trans
          ((P.trans (passageNormalProduct c₀ hc₀.ne' (ContinuousLinearEquiv.refl ℝ U))).trans
              B).symm).toLinearMap.det <
      0 := by
  rw [relative_normal_frame_det, passageNormalProduct_det, passageNormalProduct_det]
  change (c₀ * (LinearMap.id : U →ₗ[ℝ] U).det)⁻¹ * (c₁ * C.toLinearMap.det) < 0
  rw [LinearMap.det_id, mul_one]
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hc₀) (mul_neg_of_pos_of_neg hc₁ hC)

private theorem MorseCancel.mfderiv_normal_trace_model {U H X N : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N] {α : X → U} {x : X}
    (hα : MDifferentiableAt I 𝓘(ℝ, U) α x) (hα0 : α x = 0) {η : ℝ → ℝ} {τ κ : ℝ}
    (hη : HasDerivAt η κ τ) (hη1 : η τ = 1) (C : U ≃L[ℝ] U) {G : (ℝ × U) → N}
    {B : (ℝ × U) →L[ℝ] N} (hG : HasFDerivAt G B 0) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => G (η p.1 - 1, C (α p.2))) (τ, x) :
        (ℝ × U) →L[ℝ] N) =
      B.comp
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).prodMap
          (C.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, U) α x))) := by
  have ht :=
    (hη.sub_const 1).hasFDerivAt.hasMFDerivAt.comp (τ, x)
      (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hu := C.hasFDerivAt.hasMFDerivAt.comp x hα.hasMFDerivAt
  have hu' := hu.comp (τ, x) (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (τ, x))
  have hpair :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × U) (fun p : ℝ × X => (η p.1 - 1, C (α p.2))) (τ, x)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) κ).prodMap
        (C.toContinuousLinearMap.comp (mfderiv I 𝓘(ℝ, U) α x))) := by convert! ht.prodMk hu' using 1
  have hcenter : (η τ - 1, C (α x)) = (0 : ℝ × U) := by
    rw [hη1, hα0, map_zero, sub_self]
    rfl
  have hG' : HasFDerivAt G B (η τ - 1, C (α x)) := by rw [hcenter]; exact hG
  exact (hG'.hasMFDerivAt.comp (τ, x) hpair).mfderiv

private theorem MorseCancel.LongitudinalTubeMotion.normal_trace_mfderiv {U H X N : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H}
    [TopologicalSpace X] [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N]
    {V E M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞}
    (A : MorseCancel.LongitudinalTubeMotion Φ)
    (Φ₀ Φ₁ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞) (C : U ≃L[ℝ] U)
    (R : V ≃L[ℝ] V) {f : X → M} {x : X} (hf : MDifferentiableAt I 𝓘(ℝ, E) f x)
    (h0 : (0 : ℝ × (U × V)) ∈ Φ.source) (hΦ₀ : (0 : ℝ × (U × V)) ∈ Φ₀.source) (hx : Φ₀ 0 = f x)
    (hrec : ∀ z ∈ Φ₀.source, Φ₀ z ∈ Set.range f ↔ z.1 = 0 ∧ z.2.2 = 0)
    (hleft : (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 (0 : ℝ × (U × V))] Φ₀)
    (hright :
      (Φ : ℝ × (U × V) → M) =ᶠ[𝓝 ((1 : ℝ), (0 : U × V))]
        MorseCancel.linearTransverseChart (C.prodCongr R) Φ₁)
    (n : M → N) (B : (ℝ × U) →L[ℝ] N)
    (hB : HasFDerivAt (fun z : ℝ × U => n (Φ₁ (1 + z.1, (z.2, 0)))) B 0) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => n (A.family (p.1, f p.2))) (A.time, x) :
        (ℝ × U) →L[ℝ] N) =
      B.comp
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
              (deriv Real.smoothTransition A.time * A.destination)).prodMap
          (C.toContinuousLinearMap.comp
            (mfderiv I 𝓘(ℝ, U) (fun q : X => (Φ₀.symm (f q)).2.1) x))) := by
  let W := ℝ × (U × V)
  let a : X → W := Φ₀.symm ∘ f
  let P : W →L[ℝ] U := (ContinuousLinearMap.fst ℝ U V).comp (ContinuousLinearMap.snd ℝ ℝ (U × V))
  let α : X → U := P ∘ a
  have hfx : f x ∈ Φ₀.target := hx ▸ Φ₀.map_source hΦ₀
  have ha : MDifferentiableAt I 𝓘(ℝ, W) a x := (Φ₀.symm.mdifferentiableAt (by simp) hfx).comp x hf
  have hα : MDifferentiableAt I 𝓘(ℝ, U) α x := P.differentiableAt.mdifferentiableAt.comp x ha
  have ha0 : a x = 0 := (congrArg Φ₀.symm hx).symm.trans (Φ₀.left_inv hΦ₀)
  have hα0 : α x = 0 := by change P (a x) = 0; rw [ha0, map_zero]
  let η : ℝ → ℝ := fun t => Real.smoothTransition t * A.destination
  have hη : HasDerivAt η (deriv Real.smoothTransition A.time * A.destination) A.time :=
    ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
          A.time).hasDerivAt.mul_const
      _
  let G : (ℝ × U) → N := fun z => n (Φ₁ (1 + z.1, (z.2, 0)))
  have htrace :=
    A.sheet_trace_germ_of_endpoint_germs Φ₀ Φ₁ C R hf.continuousAt h0 hΦ₀ hx hrec hleft hright
  have heq :
    (fun p : ℝ × X => n (A.family (p.1, f p.2))) =ᶠ[𝓝 (A.time, x)] fun p =>
      G (η p.1 - 1, C (α p.2)) := by
    filter_upwards [htrace] with p hp
    rw [hp]
    change n (Φ₁ (η p.1, (C (α p.2), 0))) = n (Φ₁ (1 + (η p.1 - 1), (C (α p.2), 0)))
    rw [show 1 + (η p.1 - 1) = η p.1 by ring]
  rw [heq.mfderiv_eq]
  exact MorseCancel.mfderiv_normal_trace_model hα hα0 hη A.time_value C hB

private theorem MorseCancel.mfderiv_retime_unit_rate {U H X N : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N] {F : ℝ × X → N} {x : X} {σ τ : ℝ}
    (hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x)) {D : ℝ → ℝ} (hD : HasDerivAt D 1 σ)
    (hpoint : D σ = τ) :
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => F (D p.1, p.2)) (σ, x) :
        (ℝ × U) →L[ℝ] N) =
      mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x) := by
  subst τ
  have hDmf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) D σ (ContinuousLinearMap.id ℝ ℝ) := by
    have hid : ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ) = ContinuousLinearMap.id ℝ ℝ := by
      ext
      simp
    have h := hD.hasFDerivAt
    change HasFDerivAt D (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) σ at h
    rw [hid] at h
    exact h.hasMFDerivAt
  have ht := hDmf.comp (σ, x) (hasMFDerivAt_fst (I := 𝓘(ℝ, ℝ)) (I' := I) (σ, x))
  have hp :
    HasMFDerivAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) (fun p : ℝ × X => (D p.1, p.2)) (σ, x)
      (ContinuousLinearMap.id ℝ (ℝ × U)) := by
    convert! ht.prodMk (hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ)) (I' := I) (σ, x)) using 1
  have hF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) := hF
  have hc := (hF'.hasMFDerivAt.comp (σ, x) hp).mfderiv
  change
    (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) (fun p : ℝ × X => F (D p.1, p.2)) (σ, x) :
        (ℝ × U) →L[ℝ] N) =
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) : (ℝ × U) →L[ℝ] N).comp
        (ContinuousLinearMap.id ℝ (ℝ × U)) at hc
  apply ContinuousLinearMap.ext
  intro z
  exact congrArg (fun L : (ℝ × U) →L[ℝ] N => L z) hc

private theorem MorseCancel.fderiv_retimed_trace_parameter {U H X N : Type*} [NormedAddCommGroup U]
    [NormedSpace ℝ U] [TopologicalSpace H] {I : ModelWithCorners ℝ U H} [TopologicalSpace X]
    [ChartedSpace H X] [NormedAddCommGroup N] [NormedSpace ℝ N] {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] {F : ℝ × X → N} {x : X} {σ τ : ℝ}
    (hF : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x)) {D : ℝ → ℝ} (hD : HasDerivAt D 1 σ)
    (hpoint : D σ = τ) (Ψ : PartialDiffeomorph 𝓘(ℝ, A) (𝓘(ℝ, ℝ).prod I) A (ℝ × X) ∞)
    (hΨ : (0 : A) ∈ Ψ.source) (hcenter : Ψ 0 = (σ, x)) :
    fderiv ℝ (fun z : A => F (D (Ψ z).1, (Ψ z).2)) 0 =
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x) : (ℝ × U) →L[ℝ] N).comp
        (mfderiv 𝓘(ℝ, A) (𝓘(ℝ, ℝ).prod I) Ψ 0) := by
  let G : ℝ × X → N := fun p => F (D p.1, p.2)
  have hF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (D σ, x) := by
    rw [hpoint]
    exact hF
  have hG : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (σ, x) :=
    hF'.comp (σ, x)
      ((hD.differentiableAt.mdifferentiableAt.comp (σ, x) mdifferentiableAt_fst).prodMk
        mdifferentiableAt_snd)
  have hG' : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (Ψ 0) := by
    rw [hcenter]
    exact hG
  change fderiv ℝ (G ∘ Ψ) 0 = _
  rw [← mfderiv_eq_fderiv, mfderiv_comp 0 hG' (Ψ.mdifferentiableAt (by simp) hΨ), hcenter]
  rw [show
      (mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) G (σ, x) : (ℝ × U) →L[ℝ] N) =
        mfderiv (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, N) F (τ, x)
      from mfderiv_retime_unit_rate hF hD hpoint]
  rfl

private theorem MorseCancel.exists_shared_passage_frames {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    (P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))))
    (B : (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N)
    (Q : (ℝ × (EuclideanSpace ℝ (Fin 2))) ≃L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))))
    (hdim : Module.finrank ℝ N = 3)
    (hbij : Function.Bijective (B.comp (Q.toContinuousLinearMap.comp P))) :
    ∃ (P' : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2)))) (B' :
      (ℝ × (EuclideanSpace ℝ (Fin 2))) ≃L[ℝ] N),
      P'.toContinuousLinearMap = P ∧ B'.toContinuousLinearMap = B := by
  have hPi : Function.Injective P := by
    intro x y hxy
    apply hbij.injective
    change B (Q (P x)) = B (Q (P y))
    rw [hxy]
  have hBs : Function.Surjective B := by
    intro y
    obtain ⟨x, hx⟩ := hbij.surjective y
    exact ⟨Q (P x), hx⟩
  have hdimP :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (ℝ × (EuclideanSpace ℝ (Fin 2))) := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
  have hdimB : Module.finrank ℝ (ℝ × (EuclideanSpace ℝ (Fin 2))) = Module.finrank ℝ N := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdim]
  have hPb : Function.Bijective P :=
    ⟨hPi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimP).mp hPi⟩
  have hBb : Function.Bijective B :=
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimB).mpr hBs, hBs⟩
  exact
    ⟨(LinearEquiv.ofBijective P.toLinearMap hPb).toContinuousLinearEquiv,
      (LinearEquiv.ofBijective B.toLinearMap hBb).toContinuousLinearEquiv, rfl, rfl⟩

private structure MorseCancel.CenteredSheetPassage (E : Type*) {M : Type*} {X : Type*} {Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (f : X → M)
    (g : Y → M) (x : X) (y : Y) (O : Set M) where
  family : ℝ × M → M
  support : Set M
  compact_support : IsCompact support
  avoids : support ⊆ Oᶜ
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ family
  zero : ∀ z, family (0, z) = z
  slices : ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ z, d z = family (t, z)
  fixedOutside : ∀ t z, z ∉ support → family (t, z) = z
  crossing :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u : X, ∀ v : Y, family (t, f u) = g v ↔ t = 1 / 2 ∧ u = x ∧ v = y

private def MorseCancel.LongitudinalTubeMotion.centeredSheetPassage {E M X Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) 𝓘(ℝ, E) (ℝ × V) M ∞}
    (A : MorseCancel.LongitudinalTubeMotion Φ) (D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
    (hD0 : D 0 = 0) (hpoint : D (1 / 2) = A.time)
    (hinterval : Set.MapsTo D (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1)) {f : X → M} {g : Y → M}
    {x : X} {y : Y} {O : Set M} (havoid : Φ.target ⊆ Oᶜ)
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ u : X, ∀ v : Y, A.family (t, f u) = g v ↔ t = A.time ∧ u = x ∧ v = y) :
    MorseCancel.CenteredSheetPassage E f g x y O
    where
  family := fun p => A.family (D p.1, p.2)
  support := A.support
  compact_support := A.compact_support
  avoids := A.support_subset.trans havoid
  smooth := A.smooth.comp ((D.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd)
  zero := by intro z; change A.family (D 0, z) = z; rw [hD0, A.zero]
  slices := fun t => A.slices (D t)
  fixedOutside := fun t z hz => A.fixedOutside (D t) z hz
  crossing := by
    intro t ht u v
    rw [hcross (D t) (hinterval ht) u v]
    constructor
    · rintro ⟨h, hu, hv⟩
      exact ⟨D.injective (h.trans hpoint.symm), hu, hv⟩
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨hpoint, rfl, rfl⟩

private theorem MorseCancel.bijective_trace_normal_of_native_transverse {E M U H X V H' Y N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U] [TopologicalSpace H]
    {I : ModelWithCorners ℝ U H} [TopologicalSpace X] [ChartedSpace H X] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [TopologicalSpace H'] {I' : ModelWithCorners ℝ V H'} [TopologicalSpace Y]
    [ChartedSpace H' Y] [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {f : X → M} {g : Y → M} {n : M → N} {x : X} {y : Y} (hf : MDifferentiableAt I 𝓘(ℝ, E) f x)
    (hn : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)) (hpoint : g y = f x)
    (htrans : Smale.NativeTransversality.At I I' 𝓘(ℝ, E) f g x y)
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)))
    (hzero : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y) : E →L[ℝ] N).comp (mfderiv I' 𝓘(ℝ, E) g y) = 0)
    (hdim : Module.finrank ℝ U = Module.finrank ℝ N) :
    Function.Bijective (mfderiv I 𝓘(ℝ, N) (n ∘ f) x) := by
  let Q : E →L[ℝ] N := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)
  let B : V →L[ℝ] E := mfderiv I' 𝓘(ℝ, E) g y
  let A : U →L[ℝ] E := mfderiv I 𝓘(ℝ, E) f x
  have hbij : Function.Bijective (Q.comp A) :=
    Smale.TransverseCoordinates.bijective_normal_comp Q B A hsurj
      (Smale.TransverseCoordinates.surjective_coprod_swap A B (htrans hpoint)) hzero hdim
  have hn' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, N) n (f x) := hpoint ▸ hn
  have hder : (mfderiv I 𝓘(ℝ, N) (n ∘ f) x : U →L[ℝ] N) = Q.comp A := by
    rw [mfderiv_comp x hn' hf, ← hpoint]
    rfl
  rw [hder]
  exact hbij

private theorem
    MorseCancel.hasFDerivAt_terminal_normal_factor {E M U V N : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup U]
    [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup N]
    [NormedSpace ℝ N] (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) (ℝ × (U × V)) M ∞)
    (hΦ : ((1 : ℝ), (0 : U × V)) ∈ Φ.source) {n : M → N}
    (hn : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ (1, 0))) :
    HasFDerivAt (fun z : ℝ × U => n (Φ (1 + z.1, (z.2, 0))))
      (fderiv ℝ (fun z : ℝ × U => n (Φ (1 + z.1, (z.2, 0)))) 0) 0 := by
  let Q : (ℝ × U) → ℝ × (U × V) := fun z => (1 + z.1, (z.2, 0))
  have hQ : ContDiff ℝ ∞ Q :=
    (contDiff_const.add contDiff_fst).prodMk (contDiff_snd.prodMk contDiff_const)
  have hQ0 : Q 0 = (1, 0) := by
    change ((1 : ℝ) + 0, ((0 : U), (0 : V))) = (1, 0)
    rw [add_zero]
    rfl
  have hΦ' : ContMDiffAt 𝓘(ℝ, ℝ × (U × V)) 𝓘(ℝ, E) ∞ Φ (Q 0) := by
    rw [hQ0]
    exact Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hΦ)
  have hn' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ (Q 0)) := by rw [hQ0]; exact hn
  have hs : ContDiffAt ℝ ∞ (fun z : ℝ × U => n (Φ (Q z))) 0 :=
    (ContMDiffAt.comp (g := n) (f := fun z : ℝ × U => Φ (Q z)) 0 hn'
        (hΦ'.comp 0 hQ.contMDiff.contMDiffAt)).contDiffAt
  exact (hs.differentiableAt (by simp)).hasFDerivAt

private theorem MorseCancel.exists_centered_passage_normal_factors {E M Y Z N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Y] [IsManifold (𝓡 2) ∞ Y] [CompactSpace Y]
    [SecondCountableTopology Y] [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z]
    [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z] [NormedAddCommGroup N] [NormedSpace ℝ N]
    [FiniteDimensional ℝ N] {f : (Smale.Hemisphere.Sphere 2) → M} {g : Y → M} {b : Z → M}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ f) (hg : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ g)
    (hfe : Topology.IsEmbedding f) (hge : Topology.IsEmbedding g)
    (hfi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) f x))
    (hgi : ∀ y, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, E) g y))
    (hdisj : Disjoint (Set.range f) (Set.range g)) (hb : ContMDiff (𝓡 2) 𝓘(ℝ, E) ∞ b)
    (hbc : IsClosed (Set.range b)) (hdim : Module.finrank ℝ E = 5)
    (x : (Smale.Hemisphere.Sphere 2)) (y : Y) (hbx : f x ∉ Set.range b) (hby : g y ∉ Set.range b)
    (γ : Path (f x) (g y)) (n : M → N) (hn : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (g y))
    (hsurj : Function.Surjective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y)))
    (hzero : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, N) n (g y) : E →L[ℝ] N).comp (mfderiv (𝓡 2) 𝓘(ℝ, E) g y) = 0)
    (hdimN : Module.finrank ℝ N = 3) :
    ∃ (P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2)))) (B :
      (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N),
      ∀ C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)),
        ∃ (c : ℝ) (hc : 0 < c),
          ∃ A : CenteredSheetPassage E f g x y (Set.range b),
            HasFDerivAt
                (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                  n
                    (A.family
                      ((radialParameterChart (1 / 2) x z).1,
                        f (radialParameterChart (1 / 2) x z).2)))
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 ∧
              Function.Bijective
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) := by
  obtain ⟨Φ₀, Φ₁, hΦ₀, hΦ₁, hΦx, hΦy, hrec₀, _, hchoices⟩ :=
    exists_relative_sheet_passages_with_normal_change hf hg hfe hge hfi hgi hdisj hb hbc hdim x y
      hbx hby γ
  let Ψ := radialParameterChart (1 / 2) x
  have hΨ0 : (0 : (EuclideanSpace ℝ (Fin 3))) ∈ Ψ.source :=
    radialParameterChart_zero_mem_source (1 / 2) x
  have hΨpoint : Ψ 0 = ((1 / 2 : ℝ), x) := radialParameterChart_zero (1 / 2) x
  let J : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))) :=
    mfderiv (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 2)) Ψ 0
  let K : (EuclideanSpace ℝ (Fin 2)) →L[ℝ] (EuclideanSpace ℝ (Fin 2)) :=
    mfderiv (𝓡 2) 𝓘(ℝ, (EuclideanSpace ℝ (Fin 2)))
      (fun q : (Smale.Hemisphere.Sphere 2) => (Φ₀.symm (f q)).2.1) x
  let P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))) :=
    ((ContinuousLinearMap.id ℝ ℝ).prodMap K).comp J
  let G : (ℝ × (EuclideanSpace ℝ (Fin 2))) → N := fun z => n (Φ₁ (1 + z.1, (z.2, 0)))
  let B : (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N := fderiv ℝ G 0
  have hnΦ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (Φ₁ (1, 0)) := by rw [hΦy]; exact hn
  have hB : HasFDerivAt G B 0 := hasFDerivAt_terminal_normal_factor Φ₁ hΦ₁ hnΦ
  refine ⟨P, B, ?_⟩
  intro C
  obtain ⟨R, ε, hε, Φ, A, hprod, _, _, hleft, hright, _, _, havoid, _, hcross, htrans⟩ :=
    hchoices C
  have h0 : (0 : (ℝ × ((EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2))))) ∈ Φ.source :=
    hprod ⟨⟨le_rfl, zero_le_one⟩, Metric.mem_closedBall_self hε.le⟩
  obtain ⟨D, hD0, _, hDpoint, _, hDinterval, _, hDder⟩ := exists_centered_passage_clock A.time_mem
  let T := A.centeredSheetPassage D hD0 hDpoint hDinterval havoid hcross
  let c : ℝ := deriv Real.smoothTransition A.time * A.destination
  have hc : 0 < c := A.time_rate
  let F : ℝ × (Smale.Hemisphere.Sphere 2) → M := fun p => A.family (p.1, f p.2)
  have hF : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E) ∞ F :=
    A.smooth.comp (contMDiff_fst.prodMk (hf.comp contMDiff_snd))
  have hpoint : F (A.time, x) = g y :=
    (hcross A.time ⟨A.time_mem.1.le, A.time_mem.2.le⟩ x y).mpr ⟨rfl, rfl, rfl⟩
  have hnF : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, N) ∞ n (F (A.time, x)) := by rw [hpoint]; exact hn
  let NF : ℝ × (Smale.Hemisphere.Sphere 2) → N := n ∘ F
  have hNF : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :=
    (hnF.comp (A.time, x) hF.contMDiffAt).mdifferentiableAt (by simp)
  have hNFbij : Function.Bijective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x)) :=
    bijective_trace_normal_of_native_transverse (hF.mdifferentiable (by simp) (A.time, x))
      (hn.mdifferentiableAt (by simp)) hpoint.symm htrans hsurj hzero
      (by simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin, hdimN])
  have hret :
    fderiv ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2))) 0 =
      (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :
            (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N).comp
        J :=
    fderiv_retimed_trace_parameter hNF hDder hDpoint Ψ hΨ0 hΨpoint
  have hfactor :
    (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (A.time, x) :
        (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N) =
      B.comp
        ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) c).prodMap
          (C.toContinuousLinearMap.comp K)) :=
    A.normal_trace_mfderiv Φ₀ Φ₁ C R (hf.mdifferentiable (by simp) x) h0 hΦ₀ hΦx hrec₀ hleft
      hright n B hB
  have heq :
    fderiv ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2))) 0 =
      B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P) := by
    rw [hret, hfactor]
    apply ContinuousLinearMap.ext
    intro z
    change B ((J z).1 * c, C (K (J z).2)) = B (c * (J z).1, C (K (J z).2))
    rw [mul_comm]
  let H : ℝ × (Smale.Hemisphere.Sphere 2) → N := fun p => NF (D p.1, p.2)
  have hNF' : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) NF (D (1 / 2), x) := by
    rw [hDpoint]
    exact hNF
  have hH : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) H (1 / 2, x) :=
    MDifferentiableAt.comp (g := NF) (f := fun p : ℝ × (Smale.Hemisphere.Sphere 2) =>
      (D p.1, p.2)) (1 / 2, x) hNF'
      ((hDder.differentiableAt.mdifferentiableAt.comp (1 / 2, x) mdifferentiableAt_fst).prodMk
        mdifferentiableAt_snd)
  have hH' : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, N) H (Ψ 0) := by
    rw [hΨpoint]
    exact hH
  have hdiff :
    DifferentiableAt ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2)))
      0 :=
    (hH'.comp 0 (Ψ.mdifferentiableAt (by simp) hΨ0)).differentiableAt
  have hder :
    HasFDerivAt (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2)))
      (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 := by
    rw [← heq]
    exact hdiff.hasFDerivAt
  have hbij :
    Function.Bijective
      (fderiv ℝ (fun z : (EuclideanSpace ℝ (Fin 3)) => n (T.family ((Ψ z).1, f (Ψ z).2))) 0) := by
    rw [hret]
    exact hNFbij.comp (Smale.PartialChart.bijective_mfderiv Ψ hΨ0)
  exact ⟨c, hc, T, hder, heq ▸ hbij⟩

private theorem MorseCancel.opposite_centered_passages_of_normal_factors {E M Y N : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] [FiniteDimensional ℝ N]
    {f : (Smale.Hemisphere.Sphere 2) → M} {g : Y → M} {x : (Smale.Hemisphere.Sphere 2)} {y : Y}
    {O : Set M} (n : M → N) (hdim : Module.finrank ℝ N = 3)
    (P : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (ℝ × (EuclideanSpace ℝ (Fin 2))))
    (B : (ℝ × (EuclideanSpace ℝ (Fin 2))) →L[ℝ] N)
    (hchoices :
      ∀ C : (EuclideanSpace ℝ (Fin 2)) ≃L[ℝ] (EuclideanSpace ℝ (Fin 2)),
        ∃ (c : ℝ) (hc : 0 < c),
          ∃ A : CenteredSheetPassage E f g x y O,
            HasFDerivAt
                (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                  n
                    (A.family
                      ((radialParameterChart (1 / 2) x z).1,
                        f (radialParameterChart (1 / 2) x z).2)))
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P)) 0 ∧
              Function.Bijective
                (B.comp ((passageNormalProduct c hc.ne' C).toContinuousLinearMap.comp P))) :
    ∃ A₀ A₁ : CenteredSheetPassage E f g x y O,
      ∃ L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] N,
        HasFDerivAt
            (fun z : (EuclideanSpace ℝ (Fin 3)) =>
              n
                (A₀.family
                  ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
            L₀.toContinuousLinearMap 0 ∧
          HasFDerivAt
              (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                n
                  (A₁.family
                    ((radialParameterChart (1 / 2) x z).1,
                      f (radialParameterChart (1 / 2) x z).2)))
              L₁.toContinuousLinearMap 0 ∧
            (L₁.trans L₀.symm).toLinearMap.det < 0 := by
  obtain ⟨C, hC⟩ :=
    Degree.SupportedGerms.exists_linearEquiv_with_det (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (0 : Fin 2) (show (-1 : ℝ) ≠ 0 by norm_num)
  have hCneg : C.toLinearMap.det < 0 := by rw [hC]; norm_num
  obtain ⟨c₀, hc₀, A₀, hA₀, hbij₀⟩ :=
    hchoices (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
  obtain ⟨c₁, hc₁, A₁, hA₁, _⟩ := hchoices C
  let Q₀ :=
    passageNormalProduct c₀ hc₀.ne' (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2)))
  let Q₁ := passageNormalProduct c₁ hc₁.ne' C
  obtain ⟨P', B', hP, hB⟩ := exists_shared_passage_frames P B Q₀ hdim hbij₀
  let L₀ := (P'.trans Q₀).trans B'
  let L₁ := (P'.trans Q₁).trans B'
  have hL₀ : L₀.toContinuousLinearMap = B.comp (Q₀.toContinuousLinearMap.comp P) := by
    change
      B'.toContinuousLinearMap.comp (Q₀.toContinuousLinearMap.comp P'.toContinuousLinearMap) = _
    rw [hP, hB]
  have hL₁ : L₁.toContinuousLinearMap = B.comp (Q₁.toContinuousLinearMap.comp P) := by
    change
      B'.toContinuousLinearMap.comp (Q₁.toContinuousLinearMap.comp P'.toContinuousLinearMap) = _
    rw [hP, hB]
  refine ⟨A₀, A₁, L₀, L₁, ?_, ?_, ?_⟩
  · rw [hL₀]
    exact hA₀
  · rw [hL₁]
    exact hA₁
  · exact passage_normal_relative_det_neg P' B' hc₀ hc₁ C hCneg

private theorem
    MorseCancel.exists_native_opposite_centered_passages {E M Z : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z] [SecondCountableTopology Z]
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (α : C((Smale.Hemisphere.Sphere 2), d.UpperLevel)) (hαe : Topology.IsEmbedding α)
    (hdisj : Disjoint (Set.range α) (Set.range d.surgery.beltSphere)) (b : Z → d.UpperLevel)
    (hbc : IsClosed (Set.range b)) (x : (Smale.Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (hx : α x ∉ Set.range b)
    (hv : d.surgery.beltSphere v ∉ Set.range b) (γ : Path (α x) (d.surgery.beltSphere v)) :
    let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α →
      (∀ z, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) α z)) →
        ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ b →
          ∃ A₀ A₁ :
            CenteredSheetPassage (Smale.RegularLevel.Model E) α d.surgery.beltSphere x v
              (Set.range b),
            ∃ L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates,
              HasFDerivAt
                  (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                    d.beltNormal
                      (A₀.family
                        ((radialParameterChart (1 / 2) x z).1,
                          α (radialParameterChart (1 / 2) x z).2)))
                  L₀.toContinuousLinearMap 0 ∧
                HasFDerivAt
                    (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                      d.beltNormal
                        (A₁.family
                          ((radialParameterChart (1 / 2) x z).1,
                            α (radialParameterChart (1 / 2) x z).2)))
                    L₁.toContinuousLinearMap 0 ∧
                  (L₁.trans L₀.symm).toLinearMap.det < 0 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ := Smale.RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  dsimp only
  intro hα hαi hb
  have hleveldim : Module.finrank ℝ (Smale.RegularLevel.Model E) = 5 := by
    simp [Smale.RegularLevel.Model, hdim]
  have hn :=
    d.contMDiffOn_beltNormal hf |>.contMDiffAt
      (d.isOpen_beltNormalDomain.mem_nhds (d.belt_mem_normalDomain v))
  obtain ⟨P, B, hchoices⟩ :=
    exists_centered_passage_normal_factors hα (d.belt_smooth hf 2) hαe
      d.belt_isClosedEmbedding.isEmbedding hαi (d.belt_derivative_injective hf 2) hdisj hb hbc
      hleveldim x v hx hv γ d.beltNormal hn (d.surjective_beltNormal_derivative hf v)
      (d.beltNormal_derivative_comp_belt hf 2 v) (by exact Fact.out)
  exact opposite_centered_passages_of_normal_factors d.beltNormal (by exact Fact.out) P B hchoices

private theorem MorseCancel.choose_prescribed_normal_passage {E M Y N : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup N]
    [NormedSpace ℝ N] {f : (Smale.Hemisphere.Sphere 2) → M} {g : Y → M}
    {x : (Smale.Hemisphere.Sphere 2)} {y : Y} {O : Set M} (n : M → N)
    (e : (Smale.Hemisphere.Sphere 2) ≃ₜ Metric.sphere (0 : N) 1)
    (A₀ A₁ : CenteredSheetPassage E f g x y O) (L₀ L₁ : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] N)
    (hL₀ :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) =>
          n
            (A₀.family
              ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
        L₀.toContinuousLinearMap 0)
    (hL₁ :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) =>
          n
            (A₁.family
              ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
        L₁.toContinuousLinearMap 0)
    (hdet : (L₁.trans L₀.symm).toLinearMap.det < 0) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    ∃ (A : CenteredSheetPassage E f g x y O) (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] N),
      HasFDerivAt
          (fun z : (EuclideanSpace ℝ (Fin 3)) =>
            n
              (A.family
                ((radialParameterChart (1 / 2) x z).1, f (radialParameterChart (1 / 2) x z).2)))
          L.toContinuousLinearMap 0 ∧
        SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
          k •
            SingularMayerVietoris.singularHomologyMap
              (e : C((Smale.Hemisphere.Sphere 2), Metric.sphere (0 : N) 1)) 2 := by
  have hbij :
    Function.Bijective
      (SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2) := by
    have heq :
      (Smale.LinearSphereAction.homologyEquiv L₀ 2 :
          SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere 2) 2 →
            SingularMayerVietoris.SingularHomology (Metric.sphere (0 : N) 1) 2) =
        SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 :=
      funext (Smale.LinearSphereAction.homologyEquiv_apply L₀ 2)
    rw [← heq]
    exact (Smale.LinearSphereAction.homologyEquiv L₀ 2).bijective
  obtain ⟨u, hu, hunit⟩ :=
    two_sphere_map_unit_of_homology_bijective e
      (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) hbij
  have hopp :
    SingularMayerVietoris.singularHomologyMap
        (Smale.LinearSphereAction.sphereMap L₁.toContinuousLinearMap L₁.injective) 2 =
      -SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap L₀.toContinuousLinearMap L₀.injective) 2 := by
    simpa using
      attaching_contributions_opposite_of_relative_det_neg
        (ContinuousMap.id (Metric.sphere (0 : N) 1)) L₀ L₁ hdet
  by_cases huk : u = k
  · exact ⟨A₀, L₀, hL₀, huk ▸ hunit⟩
  · have hneg : -u = k := by
      rcases hu with rfl | rfl <;> rcases hk with rfl | rfl <;> norm_num at *
    refine ⟨A₁, L₁, hL₁, ?_⟩
    rw [hopp, hunit, ← neg_zsmul, hneg]

end Mathoverflow1973

end
