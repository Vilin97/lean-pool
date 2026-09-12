/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus2
public import LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology2
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.PeriodFamily.PeriodDomain
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus1
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods6
import all LeanPool.HopfProblem.Toric.DiagonalQuotient1
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods7
import all LeanPool.HopfProblem.Elliptic.Core3
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods8
import all LeanPool.HopfProblem.Threefold.SpecialPeriods9
import all LeanPool.HopfProblem.Toric.DiagonalQuotient2
import all LeanPool.HopfProblem.Foundations.SplitGroupExtension
import all LeanPool.HopfProblem.Uniformization.CuspUniformization4
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology2
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus2

/-!
# Hopf problem: period family · core 3

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

private def
    PeriodFamily.Boundary.EllipticCapProduct.twistCylinderMap {X : Type*} [TopologicalSpace X]
    (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1)
    (p : ℝ × ((Elliptic.HigherHomology.MappingTorusQuotient.Circle) × X)) :
    Elliptic.HigherHomology.MappingTorusQuotient.ProductQuotient m B hB ×
      (Elliptic.HigherHomology.MappingTorusQuotient.Circle) :=
  (Elliptic.HigherHomology.MappingTorusQuotient.project m B hB p.2,
    p.2.1 + (((p.1 / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle))))

private theorem PeriodFamily.Boundary.EllipticCapProduct.twistCylinderMap_continuous {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Continuous (twistCylinderMap m B hB) :=
  ((Elliptic.HigherHomology.MappingTorusQuotient.project_continuous m B hB).comp
        continuous_snd).prodMk
    ((continuous_fst.comp continuous_snd).add
      ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_fst.div_const (m : ℝ))))

private theorem PeriodFamily.Boundary.EllipticCapProduct.twistCylinderMap_deck {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (n : ℤ)
    (p : ℝ × ((Elliptic.HigherHomology.MappingTorusQuotient.Circle) × X)) :
    twistCylinderMap m B hB
        (MappingTorus.deck (Elliptic.HigherHomology.MappingTorusQuotient.twist m B) n p) =
      twistCylinderMap m B hB p := by
  rcases p with ⟨t, a, x⟩
  simp only [twistCylinderMap, MappingTorus.deck,
    Elliptic.HigherHomology.MappingTorusQuotient.twist_zpow_apply]
  apply Prod.ext
  · exact (Elliptic.HigherHomology.MappingTorusQuotient.project_eq_iff m B hB _ _).mpr ⟨-n, rfl⟩
  · change
      (a + ((((-n : ℤ) : ℝ) / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle))) +
          (((t + (n : ℝ)) / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle)) =
        a + ((t / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle))
    rw [add_assoc, ← AddCircle.coe_add]
    congr 2
    push_cast
    ring

private def
    PeriodFamily.Boundary.EllipticCapProduct.twistProductMap {X : Type*} [TopologicalSpace X]
    (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    MappingTorus.Torus (Elliptic.HigherHomology.MappingTorusQuotient.twist m B) →
      Elliptic.HigherHomology.MappingTorusQuotient.ProductQuotient m B hB ×
        (Elliptic.HigherHomology.MappingTorusQuotient.Circle) :=
  Quotient.lift (twistCylinderMap m B hB)
    (by
      rintro p q ⟨n, rfl⟩
      exact (twistCylinderMap_deck m B hB n p).symm)

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapProduct.twistProductMap_mk {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) (t : ℝ)
    (a : (Elliptic.HigherHomology.MappingTorusQuotient.Circle)) (x : X) :
    twistProductMap m B hB
        (MappingTorus.mk (Elliptic.HigherHomology.MappingTorusQuotient.twist m B) (t, (a, x))) =
      (Elliptic.HigherHomology.MappingTorusQuotient.project m B hB (a, x),
        a + ((t / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle))) :=
  rfl

private theorem PeriodFamily.Boundary.EllipticCapProduct.twistProductMap_continuous {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Continuous (twistProductMap m B hB) :=
  (twistCylinderMap_continuous m B hB).quotient_lift _

private theorem PeriodFamily.Boundary.EllipticCapProduct.twistProductMap_injective {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Function.Injective (twistProductMap m B hB) := by
  intro p q hpq
  obtain ⟨⟨t, a, x⟩, rfl⟩ :=
    MappingTorus.mk_surjective (Elliptic.HigherHomology.MappingTorusQuotient.twist m B) p
  obtain ⟨⟨s, b, y⟩, rfl⟩ :=
    MappingTorus.mk_surjective (Elliptic.HigherHomology.MappingTorusQuotient.twist m B) q
  have hq :
    Elliptic.HigherHomology.MappingTorusQuotient.project m B hB (a, x) =
      Elliptic.HigherHomology.MappingTorusQuotient.project m B hB (b, y) :=
    congrArg Prod.fst hpq
  have hc :
    a + ((t / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle)) =
      b + ((s / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle)) :=
    congrArg Prod.snd hpq
  obtain ⟨n, hn⟩ := (Elliptic.HigherHomology.MappingTorusQuotient.project_eq_iff m B hB _ _).mp hq
  have ha : a = b + (((n : ℝ) / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle)) :=
    congrArg Prod.fst hn
  have ht :
    ((s / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle)) =
      ((t / m + (n : ℝ) / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle)) := by
    apply add_left_cancel (a := b)
    rw [AddCircle.coe_add]
    rw [ha, add_assoc] at hc
    exact hc.symm.trans (by abel)
  obtain ⟨k, hk⟩ :=
    (Elliptic.HigherHomology.MappingTorusQuotient.circle_scaled_eq_iff m s t n).mp ht
  apply Eq.symm
  apply
    (MappingTorus.mk_eq_mk_iff (Elliptic.HigherHomology.MappingTorusQuotient.twist m B)
        (s, (b, y)) (t, (a, x))).mpr
  refine ⟨-(n + (m : ℤ) * k), ?_, ?_⟩
  · push_cast at hk ⊢
    linarith
  · rw [neg_neg,
      Elliptic.HigherHomology.MappingTorusQuotient.fibre_zpow_add_mul_period m
        (Elliptic.HigherHomology.MappingTorusQuotient.twist m B)
        (Elliptic.HigherHomology.MappingTorusQuotient.twist_pow_order m B hB),
      Elliptic.HigherHomology.MappingTorusQuotient.twist_zpow_apply]
    exact hn

private theorem PeriodFamily.Boundary.EllipticCapProduct.twistProductMap_surjective {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) :
    Function.Surjective (twistProductMap m B hB) := by
  rintro ⟨q, c⟩
  obtain ⟨⟨a, x⟩, rfl⟩ := Elliptic.HigherHomology.MappingTorusQuotient.project_surjective m B hB q
  obtain ⟨u, hu⟩ := QuotientAddGroup.mk_surjective (c - a)
  change (u : (Elliptic.HigherHomology.MappingTorusQuotient.Circle)) = c - a at hu
  refine
    ⟨MappingTorus.mk (Elliptic.HigherHomology.MappingTorusQuotient.twist m B) (u * m, (a, x)), ?_⟩
  rw [twistProductMap_mk]
  apply Prod.ext
  · rfl
  · have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
    change a + (((u * m) / m : ℝ) : (Elliptic.HigherHomology.MappingTorusQuotient.Circle)) = c
    rw [mul_div_cancel_right₀ u hm, hu]
    abel

private def PeriodFamily.Boundary.EllipticCapProduct.twistProductHomeomorph {X : Type*}
    [TopologicalSpace X] (m : ℕ) [NeZero m] (B : X ≃ₜ X) (hB : B ^ m = 1) [CompactSpace X]
    [T2Space X] :
    MappingTorus.Torus (Elliptic.HigherHomology.MappingTorusQuotient.twist m B) ≃ₜ
      Elliptic.HigherHomology.MappingTorusQuotient.ProductQuotient m B hB ×
        (Elliptic.HigherHomology.MappingTorusQuotient.Circle) :=
  Continuous.homeoOfEquivCompactToT2 (f :=
    Equiv.ofBijective (twistProductMap m B hB)
      ⟨twistProductMap_injective m B hB, twistProductMap_surjective m B hB⟩)
    (twistProductMap_continuous m B hB)

private def PeriodFamily.Boundary.EllipticCapProduct.homeomorphConjugation {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) : (X ≃ₜ X) →* (Y ≃ₜ Y)
    where
  toFun f := e.symm.trans (f.trans e)
  map_one' := by ext y; simp
  map_mul' f h := by ext y; simp

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapProduct.homeomorphConjugation_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) (f : X ≃ₜ X) (y : Y) :
    homeomorphConjugation e f y = e (f (e.symm y)) :=
  rfl

private theorem PeriodFamily.Boundary.EllipticCapProduct.mappingTorusConjugacy_zpow {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : X ≃ₜ Y)
    (he : ∀ x, e (f x) = g (e x)) (n : ℤ) (x : X) : e ((f ^ n) x) = (g ^ n) (e x) := by
  have hfg : homeomorphConjugation e f = g := by
    ext y
    change e (f (e.symm y)) = g y
    rw [he, e.apply_symm_apply]
  have hpow := congrArg (fun h : Y ≃ₜ Y ↦ h (e x)) ((homeomorphConjugation e).map_zpow f n)
  simpa only [homeomorphConjugation_apply, e.symm_apply_apply, hfg] using hpow

private theorem PeriodFamily.Boundary.EllipticCapProduct.mappingTorusConjugacy_symm_generator
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : X ≃ₜ Y)
    (he : ∀ x, e (f x) = g (e x)) (y : Y) : e.symm (g y) = f (e.symm y) := by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply]

private theorem PeriodFamily.Boundary.EllipticCapProduct.mappingTorusConjugacy_deck {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : X ≃ₜ Y)
    (he : ∀ x, e (f x) = g (e x)) (n : ℤ) (p : ℝ × X) :
    ((MappingTorus.deck f n p).1, e (MappingTorus.deck f n p).2) =
      MappingTorus.deck g n (p.1, e p.2) := by
  apply Prod.ext
  · rfl
  · exact mappingTorusConjugacy_zpow f g e he (-n) p.2

private def PeriodFamily.Boundary.EllipticCapProduct.mappingTorusConjugacyMap {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : X ≃ₜ Y)
    (he : ∀ x, e (f x) = g (e x)) : C(MappingTorus.Torus f, MappingTorus.Torus g)
    where
  toFun :=
    Quotient.lift (fun p : ℝ × X ↦ MappingTorus.mk g (p.1, e p.2))
      (by
        rintro p q ⟨n, rfl⟩
        rw [mappingTorusConjugacy_deck f g e he, MappingTorus.mk_deck])
  continuous_toFun :=
    ((MappingTorus.mk_continuous g).comp
          (continuous_fst.prodMk (e.continuous.comp continuous_snd))).quotient_lift
      _

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapProduct.mappingTorusConjugacyMap_mk {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : X ≃ₜ Y)
    (he : ∀ x, e (f x) = g (e x)) (t : ℝ) (x : X) :
    mappingTorusConjugacyMap f g e he (MappingTorus.mk f (t, x)) = MappingTorus.mk g (t, e x) :=
  rfl

private def PeriodFamily.Boundary.EllipticCapProduct.mappingTorusConjugacy {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : X ≃ₜ Y)
    (he : ∀ x, e (f x) = g (e x)) : MappingTorus.Torus f ≃ₜ MappingTorus.Torus g
    where
  toFun := mappingTorusConjugacyMap f g e he
  invFun := mappingTorusConjugacyMap g f e.symm (mappingTorusConjugacy_symm_generator f g e he)
  left_inv
    q := by
    obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective f q
    simp only [mappingTorusConjugacyMap_mk, e.symm_apply_apply]
  right_inv
    q := by
    obtain ⟨⟨t, y⟩, rfl⟩ := MappingTorus.mk_surjective g q
    simp only [mappingTorusConjugacyMap_mk, e.apply_symm_apply]
  continuous_toFun := (mappingTorusConjugacyMap f g e he).continuous
  continuous_invFun :=
    (mappingTorusConjugacyMap g f e.symm
        (mappingTorusConjugacy_symm_generator f g e he)).continuous

private def PeriodFamily.Boundary.EllipticCapProduct.splitBoundaryHomeomorph (j : Elliptic.Kind) :
    (ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j ≃ₜ
      MappingTorus.Torus
        (Elliptic.HigherHomology.MappingTorusQuotient.twist j.order
          (Elliptic.HigherHomology.fibreTorusHomeomorph j)) :=
  mappingTorusConjugacy (Elliptic.flatTorusAffine j j.twist)
    (Elliptic.HigherHomology.MappingTorusQuotient.twist j.order
      (Elliptic.HigherHomology.fibreTorusHomeomorph j))
    (Elliptic.HigherHomology.splitFlatTorusHomeomorph j)
    (Elliptic.HigherHomology.splitFlatTorusHomeomorph_flatTorusAffine j)

@[simp]
private theorem
    PeriodFamily.Boundary.EllipticCapProduct.splitBoundaryHomeomorph_mk (j : Elliptic.Kind)
    (t : ℝ) (x : RealTorus₄) :
    splitBoundaryHomeomorph j (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      MappingTorus.mk
        (Elliptic.HigherHomology.MappingTorusQuotient.twist j.order
          (Elliptic.HigherHomology.fibreTorusHomeomorph j))
        (t, Elliptic.HigherHomology.splitFlatTorusHomeomorph j x) :=
  rfl

private def PeriodFamily.Boundary.EllipticCapProduct.boundaryProductHomeomorph (j : Elliptic.Kind) :
    (ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j ≃ₜ
      ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j × MappingTorus.Circle :=
  (splitBoundaryHomeomorph j).trans
    ((twistProductHomeomorph j.order (Elliptic.HigherHomology.fibreTorusHomeomorph j)
          (Elliptic.HigherHomology.fibreTorusHomeomorph_pow_order j)).trans
      (((Elliptic.HigherHomology.surfaceSplitQuotientHomeomorph j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm).prodCongr
        (Homeomorph.refl MappingTorus.Circle)))

private theorem PeriodFamily.Boundary.EllipticCapProduct.splitPeriodTorusHomeomorph_symm_splitFlat
    (j : Elliptic.Kind) (p : PeriodDomain) (x : RealTorus₄) :
    (Elliptic.HigherHomology.splitPeriodTorusHomeomorph j p).symm
        (Elliptic.HigherHomology.splitFlatTorusHomeomorph j x) =
      Elliptic.flatTorusPeriodHomeomorph p x := by
  apply (Elliptic.HigherHomology.splitPeriodTorusHomeomorph j p).injective
  rw [Homeomorph.apply_symm_apply]
  change
    Elliptic.HigherHomology.splitFlatTorusHomeomorph j x =
      Elliptic.HigherHomology.splitFlatTorusHomeomorph j
        ((Elliptic.flatTorusPeriodHomeomorph p).symm (Elliptic.flatTorusPeriodHomeomorph p x))
  rw [Homeomorph.symm_apply_apply]

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.boundaryProductHomeomorph_mk (j : Elliptic.Kind)
    (t : ℝ) (x : RealTorus₄) :
    boundaryProductHomeomorph j (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)) =
      (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j
          (MappingTorus.mk (Elliptic.flatTorusAffine j j.twist) (t, x)),
        (Elliptic.HigherHomology.splitFlatTorusHomeomorph j x).1 +
          ((t / j.order : ℝ) : MappingTorus.Circle)) := by
  rw [boundaryProductHomeomorph, Homeomorph.trans_apply, splitBoundaryHomeomorph_mk,
    Homeomorph.trans_apply]
  change
    ((Elliptic.HigherHomology.surfaceSplitQuotientHomeomorph j
              (SpecialPeriods.EllipticFilling.specialLocalData j).centralPeriod).symm
          (Elliptic.HigherHomology.MappingTorusQuotient.project j.order
            (Elliptic.HigherHomology.fibreTorusHomeomorph j)
            (Elliptic.HigherHomology.fibreTorusHomeomorph_pow_order j)
            (Elliptic.HigherHomology.splitFlatTorusHomeomorph j x)),
        (Elliptic.HigherHomology.splitFlatTorusHomeomorph j x).1 +
          ((t / j.order : ℝ) : MappingTorus.Circle)) =
      _
  rw [Elliptic.HigherHomology.surfaceSplitQuotientHomeomorph_symm_project,
    splitPeriodTorusHomeomorph_symm_splitFlat,
    ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral_mk]

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.boundaryProductHomeomorph_fst (j : Elliptic.Kind)
    (q : (ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) :
    (boundaryProductHomeomorph j q).1 =
      ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j q := by
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective (Elliptic.flatTorusAffine j j.twist) q
  exact congrArg Prod.fst (boundaryProductHomeomorph_mk j t x)

private def PeriodFamily.Boundary.EllipticCapProduct.capSection (j : Elliptic.Kind) :
    C(ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface j,
      (ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) :=
  ((boundaryProductHomeomorph j).symm : C(_, _)).comp
    ⟨fun x => (x, (0 : MappingTorus.Circle)), continuous_id.prodMk continuous_const⟩

private def
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCircleFirstHomeomorph (j : Elliptic.Kind) :
    (ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j ≃ₜ
      MappingTorus.Circle × (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j :=
  (boundaryProductHomeomorph j).trans (Homeomorph.prodComm _ _)

private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryCircleFirstHomeomorph_projection
    (j : Elliptic.Kind) :
    (PeriodTorusHigherHomology.CircleTopology.productProjection
            ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j)).comp
        (boundaryCircleFirstHomeomorph j : C(_, _)) =
      ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j := by
  ext q
  exact boundaryProductHomeomorph_fst j q

private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryCircleFirstHomeomorph_section
    (j : Elliptic.Kind) :
    (boundaryCircleFirstHomeomorph j : C(_, _)).comp (capSection j) =
      PeriodTorusHigherHomology.CircleTopology.productSection
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) := by
  apply ContinuousMap.ext
  intro x
  change
    Prod.swap (boundaryProductHomeomorph j ((boundaryProductHomeomorph j).symm (x, 0))) = (0, x)
  rw [Homeomorph.apply_symm_apply]
  rfl

private def PeriodFamily.Boundary.EllipticCapProduct.boundaryCapHomologyEquiv (j : Elliptic.Kind)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) (n + 1) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology
          ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) (n + 1) ×
        SingularMayerVietoris.SingularHomology
          ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (boundaryCircleFirstHomeomorph j)
        (n + 1)).trans
    (PeriodTorusHigherHomology.circleProductHomologyEquiv
      ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n)

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCapHomologyEquiv_fst (j : Elliptic.Kind)
    (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) (n + 1)) :
    (boundaryCapHomologyEquiv j n a).1 =
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j) (n + 1) a := by
  change
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.CircleTopology.productProjection
          ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j))
        (n + 1)
        (SingularMayerVietoris.singularHomologyMap (boundaryCircleFirstHomeomorph j : C(_, _))
          (n + 1) a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    boundaryCircleFirstHomeomorph_projection]

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryCapHomologyEquiv_section
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) (n + 1)) :
    boundaryCapHomologyEquiv j n
        (SingularMayerVietoris.singularHomologyMap (capSection j) (n + 1) a) =
      (a, 0) := by
  change
    PeriodTorusHigherHomology.circleProductHomologyEquiv
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n
        (SingularMayerVietoris.singularHomologyMap (boundaryCircleFirstHomeomorph j : C(_, _))
          (n + 1) (SingularMayerVietoris.singularHomologyMap (capSection j) (n + 1) a)) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    boundaryCircleFirstHomeomorph_section]
  exact
    PeriodTorusHigherHomology.circleProductHomologyEquiv_section
      ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n a

private def PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross (j : Elliptic.Kind)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) (n + 1) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (boundaryCircleFirstHomeomorph j)
        (n + 1)).symm.toLinearMap.comp
    (PeriodTorusHigherHomology.positiveCircleCross
      ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n)

private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryPositiveCircleCross_apply
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n) :
    boundaryPositiveCircleCross j n a =
      SingularMayerVietoris.singularHomologyMap ((boundaryCircleFirstHomeomorph j).symm : C(_, _))
        (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross
          ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n a) :=
  rfl

@[simp]
private theorem
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCapHomologyEquiv_positiveCircleCross
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n) :
    boundaryCapHomologyEquiv j n (boundaryPositiveCircleCross j n a) = (0, a) := by
  change
    PeriodTorusHigherHomology.circleProductHomologyEquiv
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (boundaryCircleFirstHomeomorph j)
          (n + 1)
          ((PeriodTorusHigherHomology.homeomorphHomologyEquiv (boundaryCircleFirstHomeomorph j)
                (n + 1)).symm
            (PeriodTorusHigherHomology.positiveCircleCross
              ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n a))) =
      _
  rw [LinearEquiv.apply_symm_apply,
    PeriodTorusHigherHomology.circleProductHomologyEquiv_positiveCircleCross]

private def
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCapHomologyZeroEquiv (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) 0 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) 0 :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (boundaryCircleFirstHomeomorph j) 0).trans
    (PeriodTorusHigherHomology.circleProductHomologyZeroEquiv
      ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j))

private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryCapHomologyZeroEquiv_apply
    (j : Elliptic.Kind)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) 0) :
    boundaryCapHomologyZeroEquiv j a =
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j) 0 a := by
  change
    SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.CircleTopology.productProjection
          ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j))
        0
        (SingularMayerVietoris.singularHomologyMap (boundaryCircleFirstHomeomorph j : C(_, _)) 0
          a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    boundaryCircleFirstHomeomorph_projection]

private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryToFilling_centralRetraction
    (j : Elliptic.Kind) :
    (SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceRetraction j).comp
        (ThreefoldOverlapMappingTorus.boundaryToFilling (Option.some j)) =
      ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j := by
  rw [ThreefoldOverlapMappingTorus.boundaryToFilling_elliptic]
  rfl

private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryFillingHomologyMap_central
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) n) :
    ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j n
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) n a) =
      SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.Elliptic.specialBoundaryToCentral j) n a := by
  change
    SingularMayerVietoris.singularHomologyMap
        (SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceRetraction j) n
        (SingularMayerVietoris.singularHomologyMap
          (ThreefoldOverlapMappingTorus.boundaryToFilling (Option.some j)) n a) =
      _
  exact
    (LinearMap.congr_fun
          (PeriodTorusHigherHomology.singularHomologyMap_comp
            (ThreefoldOverlapMappingTorus.boundaryToFilling (Option.some j))
            (SpecialPeriods.Threefold.EllipticGeometry.pieceSurfaceRetraction j) n)
          a).symm.trans
      (congrArg
        (fun f :
            C((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j,
              (ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) =>
          SingularMayerVietoris.singularHomologyMap f n a)
        (boundaryToFilling_centralRetraction j))

private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryFillingHomologyMap_first
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) (n + 1)) :
    ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j (n + 1)
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1) a) =
      (boundaryCapHomologyEquiv j n a).1 :=
  (boundaryFillingHomologyMap_central j (n + 1) a).trans (boundaryCapHomologyEquiv_fst j n a).symm

private theorem
    PeriodFamily.Boundary.EllipticCapProduct.boundaryFillingHomologyMap_eq_retraction_symm
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) (n + 1)) :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1) a =
      (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j (n + 1)).symm
        (boundaryCapHomologyEquiv j n a).1 := by
  apply (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j (n + 1)).injective
  rw [boundaryFillingHomologyMap_first, LinearEquiv.apply_symm_apply]

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryFillingHomologyMap_section
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) (n + 1)) :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1)
        (SingularMayerVietoris.singularHomologyMap (capSection j) (n + 1) a) =
      (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j (n + 1)).symm a := by
  rw [boundaryFillingHomologyMap_eq_retraction_symm, boundaryCapHomologyEquiv_section]

@[simp]
private theorem
    PeriodFamily.Boundary.EllipticCapProduct.boundaryFillingHomologyMap_positiveCircleCross
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n) :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1)
        (boundaryPositiveCircleCross j n a) =
      0 := by
  rw [boundaryFillingHomologyMap_eq_retraction_symm, boundaryCapHomologyEquiv_positiveCircleCross,
    map_zero]

private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryFillingHomologyMap_surjective
    (j : Elliptic.Kind) (n : ℕ) :
    Function.Surjective
      (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) n) := by
  cases n with
  | zero =>
    intro a
    obtain ⟨b, hb⟩ :=
      (boundaryCapHomologyZeroEquiv j).surjective
        (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 0 a)
    refine
      ⟨b, (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j 0).injective ?_⟩
    rw [boundaryFillingHomologyMap_central, ← boundaryCapHomologyZeroEquiv_apply]
    exact hb
  | succ n =>
    intro a
    refine
      ⟨SingularMayerVietoris.singularHomologyMap (capSection j) (n + 1)
          (ThreefoldHomology.Finiteness.ellipticPieceRetractionHomologyEquiv j (n + 1) a),
        ?_⟩
    rw [boundaryFillingHomologyMap_section, LinearEquiv.symm_apply_apply]

private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryFillingHomologyMap_eq_zero_iff
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.SpecialBoundary) j) (n + 1)) :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1) a = 0 ↔
      (boundaryCapHomologyEquiv j n a).1 = 0 := by
  constructor
  · intro h
    rw [← boundaryFillingHomologyMap_first, h, map_zero]
  · intro h
    rw [boundaryFillingHomologyMap_eq_retraction_symm, h, map_zero]

private def
    PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv (j : Elliptic.Kind) (n : ℕ) :
    LinearMap.ker
        (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n :=
  ({    toFun a := (boundaryCapHomologyEquiv j n a.val).2
        map_add' a b := congrArg Prod.snd ((boundaryCapHomologyEquiv j n).map_add a.val b.val)
        invFun
          b :=
          ⟨boundaryPositiveCircleCross j n b,
            boundaryFillingHomologyMap_positiveCircleCross j n b⟩
        left_inv
          a := by
          apply Subtype.ext
          apply (boundaryCapHomologyEquiv j n).injective
          rw [boundaryCapHomologyEquiv_positiveCircleCross]
          exact
            Prod.ext ((boundaryFillingHomologyMap_eq_zero_iff j n a.val).mp a.property).symm rfl
        right_inv b := congrArg Prod.snd (boundaryCapHomologyEquiv_positiveCircleCross j n b) } :
      LinearMap.ker
          (ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap (Option.some j) (n + 1)) ≃+
        SingularMayerVietoris.SingularHomology
          ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n).toIntLinearEquiv

@[simp]
private theorem PeriodFamily.Boundary.EllipticCapProduct.boundaryCapKernelEquiv_symm_val
    (j : Elliptic.Kind) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((ThreefoldOverlapMappingTorus.Elliptic.BoundaryCentralSurface) j) n) :
    ((boundaryCapKernelEquiv j n).symm a).val = boundaryPositiveCircleCross j n a :=
  rfl

private theorem PeriodFamily.Boundary.Cylinder.projection_isOpenQuotientMap {X : Type}
    [TopologicalSpace X] (φ : X ≃ₜ X) : IsOpenQuotientMap (MappingTorus.mk φ) :=
  ⟨MappingTorus.mk_surjective φ, MappingTorus.mk_continuous φ, MappingTorus.mk_open φ⟩

private def
    PeriodFamily.Boundary.Cylinder.descend {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X ≃ₜ X) (F : C(ℝ × X, Y)) (hF : ∀ (k : ℤ) p, F (MappingTorus.deck φ k p) = F p) :
    C(MappingTorus.Torus φ, Y)
    where
  toFun :=
    Quotient.lift F
      (by
        rintro p q ⟨k, rfl⟩
        exact (hF k p).symm)
  continuous_toFun := F.continuous.quotient_lift _

private def PeriodFamily.Boundary.Cylinder.descendHomotopy {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (φ : X ≃ₜ X) (F G : C(ℝ × X, Y))
    (hF : ∀ (k : ℤ) p, F (MappingTorus.deck φ k p) = F p)
    (hG : ∀ (k : ℤ) p, G (MappingTorus.deck φ k p) = G p) (H : F.Homotopy G)
    (hH : ∀ (s : unitInterval) (k : ℤ) p, H (s, MappingTorus.deck φ k p) = H (s, p)) :
    (descend φ F hF).Homotopy (descend φ G hG)
    where
  toFun
    z :=
    Quotient.lift (fun p => H (z.1, p))
      (by
        rintro p q ⟨k, rfl⟩
        exact (hH z.1 k p).symm)
      z.2
  continuous_toFun := by
    apply (IsOpenQuotientMap.id.prodMap (projection_isOpenQuotientMap φ)).continuous_comp_iff.mp
    exact H.continuous
  map_zero_left
    x := by
    obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective φ x
    exact H.apply_zero p
  map_one_left
    x := by
    obtain ⟨p, rfl⟩ := MappingTorus.mk_surjective φ x
    exact H.apply_one p

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.baseHomotopyLift
    (H : C(unitInterval × ℝ, SpecialPeriods.TriangleRegularQuotient))
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hzero : ∀ t, H (0, t) = SpecialPeriods.triangleRegularProject (L t)) :
    C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint) :=
  SpecialPeriods.triangleRegularProject_covering.isCoveringMap.liftHomotopy H L hzero

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Boundary.baseHomotopyLift_zero
    (H : C(unitInterval × ℝ, SpecialPeriods.TriangleRegularQuotient))
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hzero : ∀ t, H (0, t) = SpecialPeriods.triangleRegularProject (L t)) (t : ℝ) :
    baseHomotopyLift H L hzero (0, t) = L t :=
  SpecialPeriods.triangleRegularProject_covering.isCoveringMap.liftHomotopy_zero H L hzero t

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.baseHomotopyLift_projection
    (H : C(unitInterval × ℝ, SpecialPeriods.TriangleRegularQuotient))
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hzero : ∀ t, H (0, t) = SpecialPeriods.triangleRegularProject (L t)) (s : unitInterval)
    (t : ℝ) :
    SpecialPeriods.triangleRegularProject (baseHomotopyLift H L hzero (s, t)) = H (s, t) :=
  congr_fun
    (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.liftHomotopy_lifts H L hzero)
    (s, t)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.baseHomotopyLift_translate
    (H : C(unitInterval × ℝ, SpecialPeriods.TriangleRegularQuotient))
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint))
    (hzero : ∀ t, H (0, t) = SpecialPeriods.triangleRegularProject (L t))
    (g : SpecialPeriods.TriangleGroup)
    (hperiod : ∀ (s : unitInterval) (k : ℤ) t, H (s, t + k) = H (s, t))
    (hdeck : ∀ (k : ℤ) t, L (t + k) = (g ^ (-k)) • L t) (s : unitInterval) (k : ℤ) (t : ℝ) :
    baseHomotopyLift H L hzero (s, t + k) = (g ^ (-k)) • baseHomotopyLift H L hzero (s, t) := by
  have hleft : Continuous (fun u : unitInterval => baseHomotopyLift H L hzero (u, t + k)) :=
    (baseHomotopyLift H L hzero).continuous.comp (continuous_id.prodMk continuous_const)
  have hright :
    Continuous (fun u : unitInterval => (g ^ (-k)) • baseHomotopyLift H L hzero (u, t)) :=
    (ContinuousConstSMul.continuous_const_smul (g ^ (-k))).comp
      ((baseHomotopyLift H L hzero).continuous.comp (continuous_id.prodMk continuous_const))
  have he :
    SpecialPeriods.triangleRegularProject ∘
        (fun u : unitInterval => baseHomotopyLift H L hzero (u, t + k)) =
      SpecialPeriods.triangleRegularProject ∘
        (fun u : unitInterval => (g ^ (-k)) • baseHomotopyLift H L hzero (u, t)) := by
    funext u
    simp only [Function.comp_apply, baseHomotopyLift_projection,
      SpecialPeriods.triangleRegularProject_covering.map_smul, hperiod]
  exact
    congr_fun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq hleft hright he
        0 (by simp only [baseHomotopyLift_zero, hdeck]))
      s

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.familyCylinderMap {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint)) (G : C(ℝ × X, RealTorus₄)) :
    C(ℝ × X, D.Space) :=
  ⟨fun p => D.quotient (L p.1, G p),
    D.quotient_continuous.comp ((L.continuous.comp continuous_fst).prodMk G.continuous)⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.familyCylinderMap_deck {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint)) (G : C(ℝ × X, RealTorus₄))
    (g : SpecialPeriods.TriangleGroup) (hL : ∀ (k : ℤ) t, L (t + k) = (g ^ (-k)) • L t)
    (hG : ∀ (k : ℤ) p, G (MappingTorus.deck φ k p) = (g ^ (-k)) • G p) (k : ℤ) (p : ℝ × X) :
    familyCylinderMap D L G (MappingTorus.deck φ k p) = familyCylinderMap D L G p := by
  change D.quotient (L (p.1 + k), G (MappingTorus.deck φ k p)) = D.quotient (L p.1, G p)
  rw [hL, hG]
  exact
    DiagonalQuotient.quotient_smul SpecialPeriods.TriangleGroup
      SpecialPeriods.TriangleRegularPoint RealTorus₄ (g ^ (-k)) (L p.1, G p)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.familyBoundaryMap {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (L : C(ℝ, SpecialPeriods.TriangleRegularPoint)) (G : C(ℝ × X, RealTorus₄))
    (g : SpecialPeriods.TriangleGroup) (hL : ∀ (k : ℤ) t, L (t + k) = (g ^ (-k)) • L t)
    (hG : ∀ (k : ℤ) p, G (MappingTorus.deck φ k p) = (g ^ (-k)) • G p) :
    C(MappingTorus.Torus φ, D.Space) :=
  Cylinder.descend φ (familyCylinderMap D L G) (familyCylinderMap_deck D φ L G g hL hG)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.baseHomotopySlice
    (H : C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint)) (s : unitInterval) :
    C(ℝ, SpecialPeriods.TriangleRegularPoint) :=
  ⟨fun t => H (s, t), H.continuous.comp (continuous_const.prodMk continuous_id)⟩

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.familyCylinderHomotopy {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint)
    (H : C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint)) (G : C(ℝ × X, RealTorus₄)) :
    (familyCylinderMap D (baseHomotopySlice H 0) G).Homotopy
      (familyCylinderMap D (baseHomotopySlice H 1) G)
    where
  toFun p := D.quotient (H (p.1, p.2.1), G p.2)
  continuous_toFun :=
    D.quotient_continuous.comp
      ((H.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (G.continuous.comp continuous_snd))
  map_zero_left _ := rfl
  map_one_left _ := rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Boundary.familyCylinderHomotopy_deck {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (H : C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint)) (G : C(ℝ × X, RealTorus₄))
    (g : SpecialPeriods.TriangleGroup)
    (hH : ∀ (s : unitInterval) (k : ℤ) t, H (s, t + k) = (g ^ (-k)) • H (s, t))
    (hG : ∀ (k : ℤ) p, G (MappingTorus.deck φ k p) = (g ^ (-k)) • G p) (s : unitInterval) (k : ℤ)
    (p : ℝ × X) :
    familyCylinderHomotopy D H G (s, MappingTorus.deck φ k p) =
      familyCylinderHomotopy D H G (s, p) := by
  change D.quotient (H (s, p.1 + k), G (MappingTorus.deck φ k p)) = D.quotient (H (s, p.1), G p)
  rw [hH, hG]
  exact
    DiagonalQuotient.quotient_smul SpecialPeriods.TriangleGroup
      SpecialPeriods.TriangleRegularPoint RealTorus₄ (g ^ (-k)) (H (s, p.1), G p)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Boundary.familyBoundaryHomotopy {X : Type} [TopologicalSpace X]
    (D : PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint) (φ : X ≃ₜ X)
    (H : C(unitInterval × ℝ, SpecialPeriods.TriangleRegularPoint)) (G : C(ℝ × X, RealTorus₄))
    (g : SpecialPeriods.TriangleGroup)
    (hH : ∀ (s : unitInterval) (k : ℤ) t, H (s, t + k) = (g ^ (-k)) • H (s, t))
    (hG : ∀ (k : ℤ) p, G (MappingTorus.deck φ k p) = (g ^ (-k)) • G p) :
    (familyBoundaryMap D φ (baseHomotopySlice H 0) G g (hH 0) hG).Homotopy
      (familyBoundaryMap D φ (baseHomotopySlice H 1) G g (hH 1) hG) :=
  Cylinder.descendHomotopy φ _ _ (familyCylinderMap_deck D φ _ G g (hH 0) hG)
    (familyCylinderMap_deck D φ _ G g (hH 1) hG) (familyCylinderHomotopy D H G)
    (familyCylinderHomotopy_deck D φ H G g hH hG)

private def PeriodFamily.Boundary.loopSquareLift {a b : SpecialPeriods.TriangleRegularQuotient}
    {p : Path a a} {q : Path b b} (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q)
    (L : C(unitInterval, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ t, SpecialPeriods.triangleRegularProject (L t) = p t) :
    C(unitInterval × unitInterval, SpecialPeriods.TriangleRegularPoint) :=
  SpecialPeriods.triangleRegularProject_covering.isCoveringMap.liftHomotopy S.map L
    (fun t => (S.initial t).trans (hL t).symm)

@[simp]
private theorem
    PeriodFamily.Boundary.loopSquareLift_zero {a b : SpecialPeriods.TriangleRegularQuotient}
    {p : Path a a} {q : Path b b} (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q)
    (L : C(unitInterval, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ t, SpecialPeriods.triangleRegularProject (L t) = p t) (t : unitInterval) :
    loopSquareLift S L hL (0, t) = L t :=
  SpecialPeriods.triangleRegularProject_covering.isCoveringMap.liftHomotopy_zero _ _ _ t

private theorem PeriodFamily.Boundary.loopSquareLift_projection
    {a b : SpecialPeriods.TriangleRegularQuotient} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q)
    (L : C(unitInterval, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ t, SpecialPeriods.triangleRegularProject (L t) = p t) (s t : unitInterval) :
    SpecialPeriods.triangleRegularProject (loopSquareLift S L hL (s, t)) = S.map (s, t) :=
  congr_fun
    (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.liftHomotopy_lifts _ _
      (fun t => (S.initial t).trans (hL t).symm))
    (s, t)

private theorem PeriodFamily.Boundary.loopSquareLift_endpoint
    {a b : SpecialPeriods.TriangleRegularQuotient} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q)
    (L : C(unitInterval, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ t, SpecialPeriods.triangleRegularProject (L t) = p t)
    (g : SpecialPeriods.TriangleGroup) (hend : L 1 = g • L 0) (s : unitInterval) :
    loopSquareLift S L hL (s, 1) = g • loopSquareLift S L hL (s, 0) := by
  have hleft : Continuous (fun u : unitInterval => loopSquareLift S L hL (u, 1)) :=
    (loopSquareLift S L hL).continuous.comp (continuous_id.prodMk continuous_const)
  have hright : Continuous (fun u : unitInterval => g • loopSquareLift S L hL (u, 0)) :=
    (ContinuousConstSMul.continuous_const_smul g).comp
      ((loopSquareLift S L hL).continuous.comp (continuous_id.prodMk continuous_const))
  have he :
    SpecialPeriods.triangleRegularProject ∘
        (fun u : unitInterval => loopSquareLift S L hL (u, 1)) =
      SpecialPeriods.triangleRegularProject ∘
        (fun u : unitInterval => g • loopSquareLift S L hL (u, 0)) := by
    funext u
    simp only [Function.comp_apply, loopSquareLift_projection,
      SpecialPeriods.triangleRegularProject_covering.map_smul]
    exact (S.closed u).symm
  exact
    congr_fun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq hleft hright he
        0 (by simpa only [loopSquareLift_zero] using hend))
      s

private theorem PeriodFamily.Boundary.loopSquareLift_final_frame
    {a b : SpecialPeriods.TriangleRegularQuotient} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q)
    (L : C(unitInterval, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ t, SpecialPeriods.triangleRegularProject (L t) = p t)
    (K : C(unitInterval, SpecialPeriods.TriangleRegularPoint))
    (hK : ∀ t, SpecialPeriods.triangleRegularProject (K t) = q t)
    (d : SpecialPeriods.TriangleGroup) (hd : loopSquareLift S L hL (1, 0) = d • K 0)
    (t : unitInterval) : loopSquareLift S L hL (1, t) = d • K t := by
  have hleft : Continuous (fun u : unitInterval => loopSquareLift S L hL (1, u)) :=
    (loopSquareLift S L hL).continuous.comp (continuous_const.prodMk continuous_id)
  have hright : Continuous (fun u : unitInterval => d • K u) :=
    (ContinuousConstSMul.continuous_const_smul d).comp K.continuous
  have he :
    SpecialPeriods.triangleRegularProject ∘
        (fun u : unitInterval => loopSquareLift S L hL (1, u)) =
      SpecialPeriods.triangleRegularProject ∘ (fun u : unitInterval => d • K u) := by
    funext u
    simp only [Function.comp_apply, loopSquareLift_projection, S.final,
      SpecialPeriods.triangleRegularProject_covering.map_smul, hK]
  exact
    congr_fun
      (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.eq_of_comp_eq hleft hright he
        0 hd)
      t

private theorem PeriodFamily.Boundary.loopSquareLift_frame_relation
    {a b : SpecialPeriods.TriangleRegularQuotient} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q)
    (L : C(unitInterval, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ t, SpecialPeriods.triangleRegularProject (L t) = p t)
    (g : SpecialPeriods.TriangleGroup) (hend : L 1 = g • L 0)
    (K : C(unitInterval, SpecialPeriods.TriangleRegularPoint))
    (hK : ∀ t, SpecialPeriods.triangleRegularProject (K t) = q t)
    (h : SpecialPeriods.TriangleGroup) (hKend : K 1 = h • K 0) (d : SpecialPeriods.TriangleGroup)
    (hd : loopSquareLift S L hL (1, 0) = d • K 0) : g * d = d * h := by
  let := SpecialPeriods.triangleRegularProject_covering.isCancelSMul
  apply IsCancelSMul.right_cancel _ _ (K 0)
  calc
    (g * d) • K 0 = g • loopSquareLift S L hL (1, 0) := by rw [SemigroupAction.mul_smul, hd]
    _ = loopSquareLift S L hL (1, 1) := (loopSquareLift_endpoint S L hL g hend 1).symm
    _ = d • K 1 := (loopSquareLift_final_frame S L hL K hK d hd 1)
    _ = (d * h) • K 0 := by rw [hKend, SemigroupAction.mul_smul]

private theorem PeriodFamily.Boundary.loopSquareLift_exists_frame
    {a b : SpecialPeriods.TriangleRegularQuotient} {p : Path a a} {q : Path b b}
    (S : SpecialPeriods.EllipticAttachingMeridians.LoopSquare p q)
    (L : C(unitInterval, SpecialPeriods.TriangleRegularPoint))
    (hL : ∀ t, SpecialPeriods.triangleRegularProject (L t) = p t)
    (z : SpecialPeriods.TriangleRegularPoint) (hz : SpecialPeriods.triangleRegularProject z = b) :
    ∃ d : SpecialPeriods.TriangleGroup, loopSquareLift S L hL (1, 0) = d • z := by
  have he :
    SpecialPeriods.triangleRegularProject (loopSquareLift S L hL (1, 0)) =
      SpecialPeriods.triangleRegularProject z := by
    rw [loopSquareLift_projection, S.final, q.source, hz]
  obtain ⟨d, hd⟩ := SpecialPeriods.triangleRegularProject_covering.apply_eq_iff_mem_orbit.mp he
  exact ⟨d, hd.symm⟩

private def PeriodFamily.Meridians.halfFordRealPreimage (x : ℝ) :
    SpecialPeriods.Triangle.halfFordRegion :=
  RiemannMapping.halfFordNormalizationHomeomorph.symm
    ⟨(x : ℂ), by simp [RiemannSphere.closedOrientedHalfPlane]⟩

private theorem PeriodFamily.Meridians.halfFordRealPreimage_normalization (x : ℝ) :
    (RiemannMapping.halfFordNormalizationHomeomorph (halfFordRealPreimage x) : ℂ) = (x : ℂ) :=
  congrArg
    (fun w : RiemannSphere.closedOrientedHalfPlane RiemannMapping.normalizationOrientation =>
      (w : ℂ))
    (RiemannMapping.halfFordNormalizationHomeomorph.apply_symm_apply _)

private theorem PeriodFamily.Meridians.halfFordRealPreimage_not_mem_interior (x : ℝ) :
    (halfFordRealPreimage x : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior := by
  apply (RiemannMapping.halfFordNormalizationHomeomorph_boundary_iff _).mp
  rw [halfFordRealPreimage_normalization]
  exact Complex.ofReal_im x

private def
    PeriodFamily.Meridians.halfFordBoundaryValue (z : SpecialPeriods.Triangle.halfFordRegion) :
    ℝ :=
  (RiemannMapping.halfFordNormalizationHomeomorph z : ℂ).re

private theorem PeriodFamily.Meridians.halfFordBoundaryValue_continuous :
    Continuous halfFordBoundaryValue :=
  Complex.continuous_re.comp
    (continuous_subtype_val.comp RiemannMapping.halfFordNormalizationHomeomorph.continuous)

@[simp]
private theorem PeriodFamily.Meridians.halfFordBoundaryValue_realPreimage (x : ℝ) :
    halfFordBoundaryValue (halfFordRealPreimage x) = x := by
  rw [halfFordBoundaryValue, halfFordRealPreimage_normalization, Complex.ofReal_re]

@[simp]
private theorem PeriodFamily.Meridians.halfFordBoundaryValue_centerOne :
    halfFordBoundaryValue
        ⟨SpecialPeriods.Triangle.centerOne,
          SpecialPeriods.Triangle.centerOne_mem_halfFordRegion⟩ =
      0 := by
  rw [halfFordBoundaryValue, RiemannMapping.halfFordNormalizationHomeomorph_centerOne,
    Complex.zero_re]

@[simp]
private theorem PeriodFamily.Meridians.halfFordBoundaryValue_centerTwo :
    halfFordBoundaryValue
        ⟨SpecialPeriods.Triangle.centerTwo,
          SpecialPeriods.Triangle.centerTwo_mem_halfFordRegion⟩ =
      1 := by
  rw [halfFordBoundaryValue, RiemannMapping.halfFordNormalizationHomeomorph_centerTwo,
    Complex.one_re]

private theorem PeriodFamily.Meridians.halfFordBoundaryValue_coe
    (z : SpecialPeriods.Triangle.halfFordRegion)
    (hz : (z : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior) :
    (halfFordBoundaryValue z : ℂ) = (RiemannMapping.halfFordNormalizationHomeomorph z : ℂ) := by
  apply Complex.ext
  · exact Complex.ofReal_re _
  · rw [Complex.ofReal_im, (RiemannMapping.halfFordNormalizationHomeomorph_boundary_iff z).mpr hz]

private theorem PeriodFamily.Meridians.halfFordBoundaryValue_injOn :
    Set.InjOn halfFordBoundaryValue
      {z : SpecialPeriods.Triangle.halfFordRegion |
        (z : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior} := by
  intro z hz w hw he
  apply RiemannMapping.halfFordNormalizationHomeomorph.injective
  apply Subtype.ext
  rw [← halfFordBoundaryValue_coe z hz, ← halfFordBoundaryValue_coe w hw, he]

private abbrev PeriodFamily.Meridians.RegularHalfPlane : Type :=
  { w : RiemannSphere.closedOrientedHalfPlane RiemannMapping.normalizationOrientation //
    (w : ℂ) ≠ 0 ∧ (w : ℂ) ≠ 1 }

private def PeriodFamily.Meridians.halfPlaneValue (w : RegularHalfPlane) :
    SpecialPeriods.Triangle.TwicePuncturedPlane :=
  ⟨(w.val : ℂ), w.property⟩

private def PeriodFamily.Meridians.halfPlaneConjugateValue (w : RegularHalfPlane) :
    SpecialPeriods.Triangle.TwicePuncturedPlane := by
  refine ⟨conj (w.val : ℂ), ?_, ?_⟩
  · intro h
    apply w.property.1
    simpa using congrArg conj h
  · intro h
    apply w.property.2
    simpa using congrArg conj h

private theorem PeriodFamily.Meridians.halfFordNormalization_symm_projection
    (w : RiemannSphere.closedOrientedHalfPlane RiemannMapping.normalizationOrientation) :
    SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph
        (SpecialPeriods.triangleOrbitProjection
          (RiemannMapping.halfFordNormalizationHomeomorph.symm w : ℍ)) =
      (w : ℂ) := by
  rw [SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph_projection
      (RiemannMapping.halfFordNormalizationHomeomorph.symm w).property,
    RiemannMapping.triangleSignedHalfPlaneMap_of_mem
      (RiemannMapping.halfFordNormalizationHomeomorph.symm w).property]
  exact
    congrArg
      (fun v : RiemannSphere.closedOrientedHalfPlane RiemannMapping.normalizationOrientation =>
        (v : ℂ))
      (RiemannMapping.halfFordNormalizationHomeomorph.apply_symm_apply w)

private theorem PeriodFamily.Meridians.triangleRegularLocus_iff_planeUniformization (z : ℍ) :
    z ∈ SpecialPeriods.triangleRegularLocus ↔
      SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph
            (SpecialPeriods.triangleOrbitProjection z) ≠
          0 ∧
        SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph
            (SpecialPeriods.triangleOrbitProjection z) ≠
          1 := by
  rw [← SpecialPeriods.triangleOrbitProjection_mem_regularDomain_iff,
    SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph_regular_iff]
  rfl

private theorem
    PeriodFamily.Meridians.halfFordNormalization_symm_mem_regular (w : RegularHalfPlane) :
    (RiemannMapping.halfFordNormalizationHomeomorph.symm w.val : ℍ) ∈
      SpecialPeriods.triangleRegularLocus := by
  apply (triangleRegularLocus_iff_planeUniformization _).mpr
  rw [halfFordNormalization_symm_projection]
  exact w.property

private def PeriodFamily.Meridians.halfPlaneLift (w : RegularHalfPlane) :
    SpecialPeriods.TriangleRegularPoint :=
  ⟨(RiemannMapping.halfFordNormalizationHomeomorph.symm w.val : ℍ),
    halfFordNormalization_symm_mem_regular w⟩

private theorem PeriodFamily.Meridians.halfPlaneLift_mem_halfFordRegion (w : RegularHalfPlane) :
    (halfPlaneLift w : ℍ) ∈ SpecialPeriods.Triangle.halfFordRegion :=
  (RiemannMapping.halfFordNormalizationHomeomorph.symm w.val).property

private theorem PeriodFamily.Meridians.halfPlaneLift_continuous : Continuous halfPlaneLift :=
  (continuous_subtype_val.comp
        (RiemannMapping.halfFordNormalizationHomeomorph.symm.continuous.comp
          continuous_subtype_val)).subtype_mk
    _

@[simp]
private theorem PeriodFamily.Meridians.halfPlaneLift_projection (w : RegularHalfPlane) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (halfPlaneLift w)) =
      halfPlaneValue w := by
  apply Subtype.ext
  exact halfFordNormalization_symm_projection w.val

private def PeriodFamily.Meridians.realHalfPlaneValue (x : ℝ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    RegularHalfPlane := by
  refine ⟨⟨(x : ℂ), by simp [RiemannSphere.closedOrientedHalfPlane]⟩, ?_, ?_⟩
  · change (x : ℂ) ≠ 0
    exact_mod_cast hx0
  · change (x : ℂ) ≠ 1
    exact_mod_cast hx1

private theorem PeriodFamily.Meridians.triangleOrbitProjection_circleReflection (z : ℍ) :
    SpecialPeriods.triangleOrbitProjection (SpecialPeriods.Triangle.circleReflection z) =
      SpecialPeriods.triangleOrbitProjection (SpecialPeriods.Triangle.rightReflection z) := by
  have h :=
    SpecialPeriods.triangleOrbitProjection_smul SpecialPeriods.triangleGenerator₁
      (SpecialPeriods.Triangle.circleReflection z)
  rw [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply,
    SpecialPeriods.Triangle.generatorOne_reflections,
    SpecialPeriods.Triangle.circleReflection_involutive] at h
  exact h.symm

private theorem
    PeriodFamily.Meridians.trianglePlaneUniformizationHomeomorph_circleReflection {z : ℍ}
    (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) :
    SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph
        (SpecialPeriods.triangleOrbitProjection (SpecialPeriods.Triangle.circleReflection z)) =
      conj (RiemannMapping.triangleSignedHalfPlaneMap z) := by
  rw [triangleOrbitProjection_circleReflection]
  change
    RiemannMapping.triangleSignedHalfPlaneMap.quotientHomeomorph
        RiemannMapping.triangleSignedHalfPlaneMap_isProperMap
        (SpecialPeriods.triangleOrbitProjection (SpecialPeriods.Triangle.rightReflection z)) =
      _
  rw [RiemannMapping.triangleSignedHalfPlaneMap.quotientHomeomorph_projection
      RiemannMapping.triangleSignedHalfPlaneMap_isProperMap
      (SpecialPeriods.Triangle.rightReflection z)
      (SpecialPeriods.Triangle.rightReflection_mapsTo_fordRegion hz.1)]
  exact RiemannMapping.triangleSignedHalfPlaneMap.toBoundaryMap.foldedFordMap_reflected z hz

private theorem
  PeriodFamily.Meridians.trianglePlaneUniformizationHomeomorph_circleReflection_normalization
    {z : ℍ} (hz : z ∈ SpecialPeriods.Triangle.halfFordRegion) :
    SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph
        (SpecialPeriods.triangleOrbitProjection (SpecialPeriods.Triangle.circleReflection z)) =
      conj (RiemannMapping.halfFordNormalizationHomeomorph ⟨z, hz⟩ : ℂ) := by
  rw [trianglePlaneUniformizationHomeomorph_circleReflection hz,
    RiemannMapping.triangleSignedHalfPlaneMap_of_mem hz]

private theorem
    PeriodFamily.Meridians.circleReflection_halfPlaneLift_projection (w : RegularHalfPlane) :
    SpecialPeriods.Triangle.trianglePlaneUniformizationHomeomorph
        (SpecialPeriods.triangleOrbitProjection
          (SpecialPeriods.Triangle.circleReflection (halfPlaneLift w : ℍ))) =
      conj (w.val : ℂ) := by
  rw [trianglePlaneUniformizationHomeomorph_circleReflection_normalization
      (halfPlaneLift_mem_halfFordRegion w)]
  exact
    congrArg
      (fun v : RiemannSphere.closedOrientedHalfPlane RiemannMapping.normalizationOrientation =>
        conj (v : ℂ))
      (RiemannMapping.halfFordNormalizationHomeomorph.apply_symm_apply w.val)

private theorem
    PeriodFamily.Meridians.circleReflection_halfPlaneLift_mem_regular (w : RegularHalfPlane) :
    SpecialPeriods.Triangle.circleReflection (halfPlaneLift w : ℍ) ∈
      SpecialPeriods.triangleRegularLocus := by
  apply (triangleRegularLocus_iff_planeUniformization _).mpr
  rw [circleReflection_halfPlaneLift_projection]
  exact (halfPlaneConjugateValue w).property

private def PeriodFamily.Meridians.reflectedHalfPlaneLift (w : RegularHalfPlane) :
    SpecialPeriods.TriangleRegularPoint :=
  ⟨SpecialPeriods.Triangle.circleReflection (halfPlaneLift w : ℍ),
    circleReflection_halfPlaneLift_mem_regular w⟩

private theorem PeriodFamily.Meridians.reflectedHalfPlaneLift_continuous :
    Continuous reflectedHalfPlaneLift :=
  (SpecialPeriods.Triangle.circleReflection.continuous.comp
        (continuous_subtype_val.comp halfPlaneLift_continuous)).subtype_mk
    _

@[simp]
private theorem PeriodFamily.Meridians.reflectedHalfPlaneLift_projection (w : RegularHalfPlane) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (reflectedHalfPlaneLift w)) =
      halfPlaneConjugateValue w := by
  apply Subtype.ext
  exact circleReflection_halfPlaneLift_projection w

private def PeriodFamily.Meridians.normalizationReversesMeridians : Bool :=
  Decidable.decide (0 < RiemannMapping.normalizationOrientation)

private theorem PeriodFamily.Meridians.halfCircle_im_nonneg_mo1973_23809 (t : unitInterval) :
    0 ≤ (SpecialPeriods.Triangle.meridianHalfCircle t).im := by
  rw [SpecialPeriods.Triangle.meridianHalfCircle, circleMap_zero_im]
  apply mul_nonneg (by norm_num)
  exact
    Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg Real.pi_pos.le t.property.1)
      (by nlinarith [Real.pi_pos, t.property.2])

private theorem PeriodFamily.Meridians.upperZeroPath_im_nonneg (t : unitInterval) :
    0 ≤ (SpecialPeriods.Triangle.upperZeroPath t : ℂ).im :=
  halfCircle_im_nonneg_mo1973_23809 t

private theorem PeriodFamily.Meridians.lowerZeroPath_im_nonpos (t : unitInterval) :
    (SpecialPeriods.Triangle.lowerZeroPath t : ℂ).im ≤ 0 := by
  change (conj (SpecialPeriods.Triangle.meridianHalfCircle t)).im ≤ 0
  simpa using halfCircle_im_nonneg_mo1973_23809 t

private theorem PeriodFamily.Meridians.upperOnePath_im_nonneg (t : unitInterval) :
    0 ≤ (SpecialPeriods.Triangle.upperOnePath t : ℂ).im := by
  change 0 ≤ (1 - conj (SpecialPeriods.Triangle.meridianHalfCircle t)).im
  simpa using halfCircle_im_nonneg_mo1973_23809 t

private theorem PeriodFamily.Meridians.lowerOnePath_im_nonpos (t : unitInterval) :
    (SpecialPeriods.Triangle.lowerOnePath t : ℂ).im ≤ 0 := by
  change (1 - SpecialPeriods.Triangle.meridianHalfCircle t).im ≤ 0
  simpa using halfCircle_im_nonneg_mo1973_23809 t

private def PeriodFamily.Meridians.zeroHalfPath :
    Path SpecialPeriods.Triangle.meridianBasepoint SpecialPeriods.Triangle.meridianLeftPoint :=
  if 0 < RiemannMapping.normalizationOrientation then SpecialPeriods.Triangle.upperZeroPath
  else SpecialPeriods.Triangle.lowerZeroPath

private def PeriodFamily.Meridians.oneHalfPath :
    Path SpecialPeriods.Triangle.meridianBasepoint SpecialPeriods.Triangle.meridianRightPoint :=
  if 0 < RiemannMapping.normalizationOrientation then SpecialPeriods.Triangle.upperOnePath
  else SpecialPeriods.Triangle.lowerOnePath

private def PeriodFamily.Meridians.oppositeZeroPath :
    Path SpecialPeriods.Triangle.meridianBasepoint SpecialPeriods.Triangle.meridianLeftPoint :=
  if 0 < RiemannMapping.normalizationOrientation then SpecialPeriods.Triangle.lowerZeroPath
  else SpecialPeriods.Triangle.upperZeroPath

private def PeriodFamily.Meridians.oppositeOnePath :
    Path SpecialPeriods.Triangle.meridianBasepoint SpecialPeriods.Triangle.meridianRightPoint :=
  if 0 < RiemannMapping.normalizationOrientation then SpecialPeriods.Triangle.lowerOnePath
  else SpecialPeriods.Triangle.upperOnePath

private theorem PeriodFamily.Meridians.zeroHalfPath_mem_halfPlane (t : unitInterval) :
    0 ≤ RiemannMapping.normalizationOrientation * (zeroHalfPath t : ℂ).im := by
  by_cases ho : 0 < RiemannMapping.normalizationOrientation
  · rw [zeroHalfPath, ite_eq_left ho]
    exact mul_nonneg ho.le (upperZeroPath_im_nonneg t)
  · rw [zeroHalfPath, ite_eq_right ho]
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt ho) (lowerZeroPath_im_nonpos t)

private theorem PeriodFamily.Meridians.oneHalfPath_mem_halfPlane (t : unitInterval) :
    0 ≤ RiemannMapping.normalizationOrientation * (oneHalfPath t : ℂ).im := by
  by_cases ho : 0 < RiemannMapping.normalizationOrientation
  · rw [oneHalfPath, ite_eq_left ho]
    exact mul_nonneg ho.le (upperOnePath_im_nonneg t)
  · rw [oneHalfPath, ite_eq_right ho]
    exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt ho) (lowerOnePath_im_nonpos t)

private theorem PeriodFamily.Meridians.oppositeZeroPath_coe (t : unitInterval) :
    (oppositeZeroPath t : ℂ) = conj (zeroHalfPath t : ℂ) := by
  by_cases ho : 0 < RiemannMapping.normalizationOrientation
  · rw [oppositeZeroPath, zeroHalfPath, ite_eq_left ho, ite_eq_left ho]
    rfl
  · rw [oppositeZeroPath, zeroHalfPath, ite_eq_right ho, ite_eq_right ho]
    exact (Complex.conj_conj (SpecialPeriods.Triangle.meridianHalfCircle t)).symm

private theorem PeriodFamily.Meridians.oppositeOnePath_coe (t : unitInterval) :
    (oppositeOnePath t : ℂ) = conj (oneHalfPath t : ℂ) := by
  by_cases ho : 0 < RiemannMapping.normalizationOrientation
  · rw [oppositeOnePath, oneHalfPath, ite_eq_left ho, ite_eq_left ho]
    change
      1 - SpecialPeriods.Triangle.meridianHalfCircle t =
        conj (1 - conj (SpecialPeriods.Triangle.meridianHalfCircle t))
    simp only [map_sub, map_one, Complex.conj_conj]
  · rw [oppositeOnePath, oneHalfPath, ite_eq_right ho, ite_eq_right ho]
    change
      1 - conj (SpecialPeriods.Triangle.meridianHalfCircle t) =
        conj (1 - SpecialPeriods.Triangle.meridianHalfCircle t)
    simp only [map_sub, map_one]

private def PeriodFamily.Meridians.compatiblePlanarMeridian (b : Bool) :
    Path SpecialPeriods.Triangle.meridianBasepoint SpecialPeriods.Triangle.meridianBasepoint :=
  if b then oneHalfPath.trans oppositeOnePath.symm else oppositeZeroPath.trans zeroHalfPath.symm

private theorem PeriodFamily.Meridians.compatiblePlanarMeridian_eq (b : Bool) :
    compatiblePlanarMeridian b =
      if 0 < RiemannMapping.normalizationOrientation then
        (if b then SpecialPeriods.Triangle.positiveMeridianOne
          else SpecialPeriods.Triangle.positiveMeridianZero).symm
      else
        if b then SpecialPeriods.Triangle.positiveMeridianOne
        else SpecialPeriods.Triangle.positiveMeridianZero := by
  cases b <;> by_cases ho : 0 < RiemannMapping.normalizationOrientation <;>
    simp [compatiblePlanarMeridian, zeroHalfPath, oneHalfPath, oppositeZeroPath, oppositeOnePath,
      ho, SpecialPeriods.Triangle.positiveMeridianZero,
      SpecialPeriods.Triangle.positiveMeridianOne, Path.trans_symm, Path.symm_symm]

private theorem PeriodFamily.Meridians.compatiblePlanarMeridian_class (b : Bool) :
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (compatiblePlanarMeridian b)) =
      FreeMeridianMarking.orientedClass normalizationReversesMeridians b := by
  rw [compatiblePlanarMeridian_eq]
  by_cases ho : 0 < RiemannMapping.normalizationOrientation
  · simp only [ite_eq_left ho, FreeMeridianMarking.orientedClass, normalizationReversesMeridians,
      decide_eq_true_eq.mpr ho, ↓reduceIte]
    rfl
  · simp only [ite_eq_right ho, FreeMeridianMarking.orientedClass, normalizationReversesMeridians,
      decide_eq_false_iff_not.mpr ho, Bool.false_eq_true, ↓reduceIte]
    rfl

private theorem PeriodFamily.Meridians.norm_mono_of_re_eq_im_le_mo1973_23882 {a z : ℂ}
    (hre : z.re = a.re) (ha : 0 ≤ a.im) (him : a.im ≤ z.im) : ‖a‖ ≤ ‖z‖ := by
  have hi : a.im ^ 2 ≤ z.im ^ 2 := (sq_le_sq₀ ha (ha.trans him)).mpr him
  apply (sq_le_sq₀ (norm_nonneg a) (norm_nonneg z)).mp
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, hre]
  nlinarith

private theorem PeriodFamily.Meridians.halfFordRegion_vertical_mono (a z : ℍ)
    (ha : a ∈ SpecialPeriods.Triangle.halfFordRegion) (hre : z.re = a.re) (him : a.im ≤ z.im) :
    z ∈ SpecialPeriods.Triangle.halfFordRegion := by
  have hn : ‖(a : ℂ)‖ ≤ ‖(z : ℂ)‖ := norm_mono_of_re_eq_im_le_mo1973_23882 hre a.im_pos.le him
  have hp : ‖(a : ℂ) + 1‖ ≤ ‖(z : ℂ) + 1‖ := by
    apply norm_mono_of_re_eq_im_le_mo1973_23882
    · simpa only [Complex.add_re, Complex.one_re, UpperHalfPlane.coe_re] using
        congrArg (fun x : ℝ => x + 1) hre
    · simpa only [Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_im] using
        a.im_pos.le
    · simpa only [Complex.add_im, Complex.one_im, add_zero, UpperHalfPlane.coe_im] using him
  refine ⟨⟨hre ▸ ha.1.1, hre ▸ ha.1.2.1, ha.1.2.2.1.trans hp, ha.1.2.2.2.trans hn⟩, ?_⟩
  change z.re ≤ -(1 / 2)
  rw [hre]
  exact ha.2

private theorem PeriodFamily.Meridians.circle_left_re_lt_right_re_mo1973_23890 :
    SpecialPeriods.Triangle.centerTwo.re < SpecialPeriods.Triangle.centerOne.re := by
  change (SpecialPeriods.Triangle.centerTwo : ℂ).re < (SpecialPeriods.Triangle.centerOne : ℂ).re
  rw [SpecialPeriods.Triangle.centerTwo_coe_re, SpecialPeriods.Triangle.centerOne_coe_re]
  exact SpecialPeriods.Triangle.stripLeft_lt_right

private def PeriodFamily.Meridians.halfFordCircleReal (t : unitInterval) : ℝ :=
  (1 - (t : ℝ)) * SpecialPeriods.Triangle.centerOne.re +
    (t : ℝ) * SpecialPeriods.Triangle.centerTwo.re

@[fun_prop]
private theorem
    PeriodFamily.Meridians.halfFordCircleReal_continuous : Continuous halfFordCircleReal := by
  unfold halfFordCircleReal
  fun_prop

private theorem
    PeriodFamily.Meridians.halfFordCircleReal_strictAnti : StrictAnti halfFordCircleReal := by
  intro s t hst
  have ht : (s : ℝ) < (t : ℝ) := hst
  have hp := mul_pos (sub_pos.mpr ht) (sub_pos.mpr circle_left_re_lt_right_re_mo1973_23890)
  dsimp only [halfFordCircleReal]
  nlinarith

private theorem PeriodFamily.Meridians.halfFordCircleReal_mem (t : unitInterval) :
    halfFordCircleReal t ∈ Set.Icc SpecialPeriods.Triangle.stripLeft (-1 / 2) := by
  have hbounds :
    SpecialPeriods.Triangle.centerTwo.re ≤ halfFordCircleReal t ∧
      halfFordCircleReal t ≤ SpecialPeriods.Triangle.centerOne.re := by
    constructor
    · dsimp only [halfFordCircleReal]
      nlinarith [mul_nonneg (sub_nonneg.mpr t.property.2)
          (sub_nonneg.mpr circle_left_re_lt_right_re_mo1973_23890.le)]
    · dsimp only [halfFordCircleReal]
      nlinarith [mul_nonneg t.property.1
          (sub_nonneg.mpr circle_left_re_lt_right_re_mo1973_23890.le)]
  have h₁ : SpecialPeriods.Triangle.centerOne.re = -1 / 2 :=
    SpecialPeriods.Triangle.centerOne_coe_re
  have h₂ : SpecialPeriods.Triangle.centerTwo.re = SpecialPeriods.Triangle.stripLeft :=
    SpecialPeriods.Triangle.centerTwo_coe_re
  simpa only [Set.mem_Icc, h₁, h₂] using hbounds

private theorem PeriodFamily.Meridians.boundaryCircle_norm_mo1973_23895 (x : ℝ)
    (hl : SpecialPeriods.Triangle.stripLeft ≤ x) (hr : x ≤ -1 / 2) :
    ‖(⟨x, SpecialPeriods.Triangle.boundaryHeight x⟩ : ℂ) + 1‖ = 1 := by
  have hs : SpecialPeriods.Triangle.boundaryHeight x ^ 2 = 1 - (x + 1) ^ 2 :=
    Real.sq_sqrt
      (Real.sqrt_pos.mp (SpecialPeriods.Triangle.boundaryHeight_pos_of_closed_bounds hl hr)).le
  apply (sq_eq_sq₀ (norm_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)).mp
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    add_zero, one_pow]
  nlinarith

private def PeriodFamily.Meridians.halfFordCirclePoint (t : unitInterval) :
    SpecialPeriods.Triangle.halfFordRegion :=
  ⟨⟨⟨halfFordCircleReal t, SpecialPeriods.Triangle.boundaryHeight (halfFordCircleReal t)⟩,
      SpecialPeriods.Triangle.boundaryHeight_pos_of_closed_bounds (halfFordCircleReal_mem t).1
        (halfFordCircleReal_mem t).2⟩,
    by
    apply (SpecialPeriods.Triangle.coe_mem_triangleClosedRegion_iff_halfFordRegion _).mp
    apply (SpecialPeriods.Triangle.mem_triangleClosedRegion_iff_epigraph _).mpr
    exact ⟨(halfFordCircleReal_mem t).1, (halfFordCircleReal_mem t).2, le_rfl⟩⟩

@[simp]
private theorem PeriodFamily.Meridians.halfFordCirclePoint_re (t : unitInterval) :
    (halfFordCirclePoint t : ℍ).re =
      (1 - (t : ℝ)) * SpecialPeriods.Triangle.centerOne.re +
        (t : ℝ) * SpecialPeriods.Triangle.centerTwo.re :=
  rfl

@[simp]
private theorem PeriodFamily.Meridians.halfFordCirclePoint_im (t : unitInterval) :
    (halfFordCirclePoint t : ℍ).im =
      SpecialPeriods.Triangle.boundaryHeight (halfFordCirclePoint t : ℍ).re :=
  rfl

private theorem
    PeriodFamily.Meridians.halfFordCirclePoint_continuous : Continuous halfFordCirclePoint := by
  have hc :
    Continuous
      (fun t : unitInterval =>
        (⟨halfFordCircleReal t, SpecialPeriods.Triangle.boundaryHeight (halfFordCircleReal t)⟩ :
          ℂ)) := by
    simp_rw [Complex.mk_eq_add_mul_I]
    exact
      (Complex.continuous_ofReal.comp halfFordCircleReal_continuous).add
        ((Complex.continuous_ofReal.comp
              (SpecialPeriods.Triangle.continuous_boundaryHeight.comp
                halfFordCircleReal_continuous)).mul
          continuous_const)
  exact (hc.upperHalfPlaneMk _).subtype_mk _

@[simp]
private theorem PeriodFamily.Meridians.halfFordCirclePoint_norm_add_one (t : unitInterval) :
    ‖((halfFordCirclePoint t : ℍ) : ℂ) + 1‖ = 1 :=
  boundaryCircle_norm_mo1973_23895 _ (halfFordCircleReal_mem t).1 (halfFordCircleReal_mem t).2

@[simp]
private theorem PeriodFamily.Meridians.halfFordCirclePoint_zero :
    halfFordCirclePoint 0 =
      (⟨SpecialPeriods.Triangle.centerOne, SpecialPeriods.Triangle.centerOne_mem_halfFordRegion⟩ :
        SpecialPeriods.Triangle.halfFordRegion) := by
  apply Subtype.ext
  apply UpperHalfPlane.ext
  apply SpecialPeriods.Triangle.complex_eq_of_re_eq_norm_add_one_eq
  · change
      (1 - (0 : ℝ)) * SpecialPeriods.Triangle.centerOne.re +
          0 * SpecialPeriods.Triangle.centerTwo.re =
        SpecialPeriods.Triangle.centerOne.re
    simp
  · exact (halfFordCirclePoint 0 : ℍ).im_pos
  · exact SpecialPeriods.Triangle.centerOne.im_pos
  · rw [halfFordCirclePoint_norm_add_one, SpecialPeriods.Triangle.centerOne_norm_add_one]

@[simp]
private theorem PeriodFamily.Meridians.halfFordCirclePoint_one :
    halfFordCirclePoint 1 =
      (⟨SpecialPeriods.Triangle.centerTwo, SpecialPeriods.Triangle.centerTwo_mem_halfFordRegion⟩ :
        SpecialPeriods.Triangle.halfFordRegion) := by
  apply Subtype.ext
  apply UpperHalfPlane.ext
  apply SpecialPeriods.Triangle.complex_eq_of_re_eq_norm_add_one_eq
  · change
      (1 - (1 : ℝ)) * SpecialPeriods.Triangle.centerOne.re +
          1 * SpecialPeriods.Triangle.centerTwo.re =
        SpecialPeriods.Triangle.centerTwo.re
    simp
  · exact (halfFordCirclePoint 1 : ℍ).im_pos
  · exact SpecialPeriods.Triangle.centerTwo.im_pos
  · rw [halfFordCirclePoint_norm_add_one, SpecialPeriods.Triangle.centerTwo_norm_add_one]

private theorem PeriodFamily.Meridians.halfFordCirclePoint_injective :
    Function.Injective halfFordCirclePoint := by
  intro s t h
  apply halfFordCircleReal_strictAnti.injective
  exact congrArg (fun z : SpecialPeriods.Triangle.halfFordRegion => (z : ℍ).re) h

private theorem PeriodFamily.Meridians.halfFordCirclePoint_range :
    Set.range halfFordCirclePoint =
      {z : SpecialPeriods.Triangle.halfFordRegion | ‖((z : ℍ) : ℂ) + 1‖ = 1} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact halfFordCirclePoint_norm_add_one t
  · intro hz
    have hclosed :=
      (SpecialPeriods.Triangle.coe_mem_triangleClosedRegion_iff_halfFordRegion (z : ℍ)).mpr
        z.property
    have hl : SpecialPeriods.Triangle.centerTwo.re ≤ (z : ℍ).re := by
      change (SpecialPeriods.Triangle.centerTwo : ℂ).re ≤ ((z : ℍ) : ℂ).re
      rw [SpecialPeriods.Triangle.centerTwo_coe_re]
      exact hclosed.1
    have hr : (z : ℍ).re ≤ SpecialPeriods.Triangle.centerOne.re := by
      change ((z : ℍ) : ℂ).re ≤ (SpecialPeriods.Triangle.centerOne : ℂ).re
      rw [SpecialPeriods.Triangle.centerOne_coe_re]
      exact hclosed.2.1
    have hd : 0 < SpecialPeriods.Triangle.centerOne.re - SpecialPeriods.Triangle.centerTwo.re :=
      sub_pos.mpr circle_left_re_lt_right_re_mo1973_23890
    let t : unitInterval :=
      ⟨(SpecialPeriods.Triangle.centerOne.re - (z : ℍ).re) /
          (SpecialPeriods.Triangle.centerOne.re - SpecialPeriods.Triangle.centerTwo.re),
        div_nonneg (sub_nonneg.mpr hr) hd.le, (div_le_one hd).mpr (by linarith)⟩
    have ht : halfFordCircleReal t = (z : ℍ).re := by
      dsimp only [halfFordCircleReal, t]
      field_simp [hd.ne']
      ring
    refine ⟨t, ?_⟩
    apply Subtype.ext
    apply UpperHalfPlane.ext
    apply SpecialPeriods.Triangle.complex_eq_of_re_eq_norm_add_one_eq
    · exact ht
    · exact (halfFordCirclePoint t : ℍ).im_pos
    · exact (z : ℍ).im_pos
    · exact (halfFordCirclePoint_norm_add_one t).trans hz.symm

private def PeriodFamily.Meridians.halfFordCirclePath :
    Path
      (⟨SpecialPeriods.Triangle.centerOne, SpecialPeriods.Triangle.centerOne_mem_halfFordRegion⟩ :
        SpecialPeriods.Triangle.halfFordRegion)
      ⟨SpecialPeriods.Triangle.centerTwo, SpecialPeriods.Triangle.centerTwo_mem_halfFordRegion⟩
    where
  toFun := halfFordCirclePoint
  continuous_toFun := halfFordCirclePoint_continuous
  source' := halfFordCirclePoint_zero
  target' := halfFordCirclePoint_one

private def PeriodFamily.Meridians.boundaryRise_mo1973_23910 (t : ℝ) : ℝ :=
  Max.max (-t) 0 + Max.max (t - 1) 0

private theorem PeriodFamily.Meridians.boundaryRise_nonneg_mo1973_23911 (t : ℝ) :
    0 ≤ boundaryRise_mo1973_23910 t :=
  add_nonneg (le_max_right _ _) (le_max_right _ _)

private theorem PeriodFamily.Meridians.boundaryRise_of_nonpos_mo1973_23912 {t : ℝ} (ht : t ≤ 0) :
    boundaryRise_mo1973_23910 t = -t := by
  rw [boundaryRise_mo1973_23910, max_eq_left (by linarith), max_eq_right (by linarith), add_zero]

private theorem PeriodFamily.Meridians.boundaryRise_of_unit_mo1973_23913 {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : boundaryRise_mo1973_23910 t = 0 := by
  rw [boundaryRise_mo1973_23910, max_eq_right (by linarith), max_eq_right (by linarith), add_zero]

private theorem PeriodFamily.Meridians.boundaryRise_of_one_le_mo1973_23914 {t : ℝ} (ht : 1 ≤ t) :
    boundaryRise_mo1973_23910 t = t - 1 := by
  rw [boundaryRise_mo1973_23910, max_eq_right (by linarith), max_eq_left (by linarith), zero_add]

private def PeriodFamily.Meridians.halfFordBoundaryParam (t : ℝ) :
    SpecialPeriods.Triangle.halfFordRegion :=
  let a : SpecialPeriods.Triangle.halfFordRegion := halfFordCirclePath.extend t
  let z : ℍ :=
    ⟨⟨(a : ℍ).re, (a : ℍ).im + boundaryRise_mo1973_23910 t⟩,
      lt_of_lt_of_le (a : ℍ).im_pos (le_add_of_nonneg_right (boundaryRise_nonneg_mo1973_23911 t))⟩
  ⟨z,
    halfFordRegion_vertical_mono a z a.property rfl
      (le_add_of_nonneg_right (boundaryRise_nonneg_mo1973_23911 t))⟩

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_re_mo1973_23916 (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).re = (halfFordCirclePath.extend t : ℍ).re :=
  rfl

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_im_mo1973_23917 (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).im =
      (halfFordCirclePath.extend t : ℍ).im + boundaryRise_mo1973_23910 t :=
  rfl

@[fun_prop]
private theorem PeriodFamily.Meridians.continuous_halfFordBoundaryParam :
    Continuous halfFordBoundaryParam := by
  have hbase : Continuous (fun t : ℝ => (halfFordCirclePath.extend t : ℍ)) :=
    continuous_subtype_val.comp halfFordCirclePath.continuous_extend
  have hr : Continuous (fun t : ℝ => boundaryRise_mo1973_23910 t) := by
    unfold boundaryRise_mo1973_23910
    fun_prop
  apply Continuous.subtype_mk
  apply Continuous.upperHalfPlaneMk
  simp_rw [Complex.mk_eq_add_mul_I]
  exact
    (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_re.comp hbase)).add
      ((Complex.continuous_ofReal.comp ((UpperHalfPlane.continuous_im.comp hbase).add hr)).mul
        continuous_const)

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_re_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    (halfFordBoundaryParam t : ℍ).re = SpecialPeriods.Triangle.centerOne.re := by
  rw [halfFordBoundaryParam_re_mo1973_23916, halfFordCirclePath.extend_of_le_zero ht]

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_im_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    (halfFordBoundaryParam t : ℍ).im = SpecialPeriods.Triangle.centerOne.im - t := by
  rw [halfFordBoundaryParam_im_mo1973_23917, halfFordCirclePath.extend_of_le_zero ht,
    boundaryRise_of_nonpos_mo1973_23912 ht]
  rfl

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_eq_circle {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : halfFordBoundaryParam t = halfFordCirclePoint ⟨t, ht0, ht1⟩ := by
  apply Subtype.ext
  apply UpperHalfPlane.ext_re_im
  · rw [halfFordBoundaryParam_re_mo1973_23916, Path.extend_apply _ ⟨ht0, ht1⟩]
    rfl
  · rw [halfFordBoundaryParam_im_mo1973_23917, Path.extend_apply _ ⟨ht0, ht1⟩,
      boundaryRise_of_unit_mo1973_23913 ht0 ht1, add_zero]
    rfl

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_re_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    (halfFordBoundaryParam t : ℍ).re = SpecialPeriods.Triangle.centerTwo.re := by
  rw [halfFordBoundaryParam_re_mo1973_23916, halfFordCirclePath.extend_of_one_le ht]

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_im_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    (halfFordBoundaryParam t : ℍ).im = SpecialPeriods.Triangle.centerTwo.im + t - 1 := by
  rw [halfFordBoundaryParam_im_mo1973_23917, halfFordCirclePath.extend_of_one_le ht,
    boundaryRise_of_one_le_mo1973_23914 ht]
  ring

@[simp]
private theorem PeriodFamily.Meridians.halfFordBoundaryParam_zero :
    halfFordBoundaryParam 0 =
      (⟨SpecialPeriods.Triangle.centerOne, SpecialPeriods.Triangle.centerOne_mem_halfFordRegion⟩ :
        SpecialPeriods.Triangle.halfFordRegion) := by
  rw [halfFordBoundaryParam_eq_circle (by norm_num) (by norm_num)]
  exact halfFordCirclePoint_zero

@[simp]
private theorem PeriodFamily.Meridians.halfFordBoundaryParam_one :
    halfFordBoundaryParam 1 =
      (⟨SpecialPeriods.Triangle.centerTwo, SpecialPeriods.Triangle.centerTwo_mem_halfFordRegion⟩ :
        SpecialPeriods.Triangle.halfFordRegion) := by
  rw [halfFordBoundaryParam_eq_circle (by norm_num) (by norm_num)]
  exact halfFordCirclePoint_one

private theorem PeriodFamily.Meridians.centerTwo_re_lt_centerOne_re_mo1973_23926 :
    SpecialPeriods.Triangle.centerTwo.re < SpecialPeriods.Triangle.centerOne.re := by
  change (SpecialPeriods.Triangle.centerTwo : ℂ).re < (SpecialPeriods.Triangle.centerOne : ℂ).re
  rw [SpecialPeriods.Triangle.centerOne_coe_re, SpecialPeriods.Triangle.centerTwo_coe_re]
  exact SpecialPeriods.Triangle.stripLeft_lt_right

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_re_eq_centerOne_iff (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).re = SpecialPeriods.Triangle.centerOne.re ↔ t ≤ 0 := by
  constructor
  · intro hr
    by_contra ht
    have ht0 : 0 < t := lt_of_not_ge ht
    by_cases ht1 : t ≤ 1
    · rw [halfFordBoundaryParam_eq_circle ht0.le ht1, halfFordCirclePoint_re] at hr
      have hp := mul_pos ht0 (sub_pos.mpr centerTwo_re_lt_centerOne_re_mo1973_23926)
      dsimp at hr
      nlinarith
    · rw [halfFordBoundaryParam_re_of_one_le (le_of_not_ge ht1)] at hr
      exact centerTwo_re_lt_centerOne_re_mo1973_23926.ne hr
  · exact halfFordBoundaryParam_re_of_nonpos

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_re_eq_centerTwo_iff (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).re = SpecialPeriods.Triangle.centerTwo.re ↔ 1 ≤ t := by
  constructor
  · intro hr
    by_contra ht
    have ht1 : t < 1 := lt_of_not_ge ht
    by_cases ht0 : t ≤ 0
    · rw [halfFordBoundaryParam_re_of_nonpos ht0] at hr
      exact centerTwo_re_lt_centerOne_re_mo1973_23926.ne' hr
    · rw [halfFordBoundaryParam_eq_circle (le_of_not_ge ht0) ht1.le, halfFordCirclePoint_re] at hr
      have hp := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr centerTwo_re_lt_centerOne_re_mo1973_23926)
      dsimp at hr
      nlinarith
  · exact halfFordBoundaryParam_re_of_one_le

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_re_eq_right_iff (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).re = -(1 / 2) ↔ t ≤ 0 := by
  have h : SpecialPeriods.Triangle.centerOne.re = -(1 / 2) := by
    change (SpecialPeriods.Triangle.centerOne : ℂ).re = -(1 / 2)
    simpa only [neg_div] using SpecialPeriods.Triangle.centerOne_coe_re
  rw [← h]
  exact halfFordBoundaryParam_re_eq_centerOne_iff t

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_re_eq_left_iff (t : ℝ) :
    (halfFordBoundaryParam t : ℍ).re = SpecialPeriods.Triangle.stripLeft ↔ 1 ≤ t := by
  rw [← SpecialPeriods.Triangle.centerTwo_coe_re]
  exact halfFordBoundaryParam_re_eq_centerTwo_iff t

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_norm_add_one_eq_one_iff (t : ℝ) :
    ‖((halfFordBoundaryParam t : ℍ) : ℂ) + 1‖ = 1 ↔ 0 ≤ t ∧ t ≤ 1 := by
  constructor
  · intro hn
    by_cases ht0 : t ≤ 0
    · have he : ((halfFordBoundaryParam t : ℍ) : ℂ) = (SpecialPeriods.Triangle.centerOne : ℂ) :=
        SpecialPeriods.Triangle.complex_eq_of_re_eq_norm_add_one_eq
          (halfFordBoundaryParam_re_of_nonpos ht0) (halfFordBoundaryParam t : ℍ).im_pos
          SpecialPeriods.Triangle.centerOne.im_pos
          (hn.trans SpecialPeriods.Triangle.centerOne_norm_add_one.symm)
      have hi := congrArg Complex.im he
      change (halfFordBoundaryParam t : ℍ).im = SpecialPeriods.Triangle.centerOne.im at hi
      rw [halfFordBoundaryParam_im_of_nonpos ht0] at hi
      have ht : t = 0 := by linarith
      subst t
      norm_num
    · by_cases ht1 : 1 ≤ t
      · have he : ((halfFordBoundaryParam t : ℍ) : ℂ) = (SpecialPeriods.Triangle.centerTwo : ℂ) :=
          SpecialPeriods.Triangle.complex_eq_of_re_eq_norm_add_one_eq
            (halfFordBoundaryParam_re_of_one_le ht1) (halfFordBoundaryParam t : ℍ).im_pos
            SpecialPeriods.Triangle.centerTwo.im_pos
            (hn.trans SpecialPeriods.Triangle.centerTwo_norm_add_one.symm)
        have hi := congrArg Complex.im he
        change (halfFordBoundaryParam t : ℍ).im = SpecialPeriods.Triangle.centerTwo.im at hi
        rw [halfFordBoundaryParam_im_of_one_le ht1] at hi
        have ht : t = 1 := by linarith
        subst t
        norm_num
      · exact ⟨le_of_not_ge ht0, le_of_not_ge ht1⟩
  · rintro ⟨ht0, ht1⟩
    rw [halfFordBoundaryParam_eq_circle ht0 ht1]
    exact halfFordCirclePoint_norm_add_one _

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_notMem_interior (t : ℝ) :
    (halfFordBoundaryParam t : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior := by
  intro hi
  have hI : ((halfFordBoundaryParam t : ℍ) : ℂ) ∈ SpecialPeriods.Triangle.triangleInterior := by
    simpa only [SpecialPeriods.Triangle.halfFordInterior_eq_preimage_triangleInterior,
      Set.mem_preimage] using hi
  by_cases ht0 : t ≤ 0
  · have hr := halfFordBoundaryParam_re_eq_right_iff t |>.mpr ht0
    have hu := hI.2.1
    change (halfFordBoundaryParam t : ℍ).re < -1 / 2 at hu
    linarith
  · by_cases ht1 : 1 ≤ t
    · have hr := halfFordBoundaryParam_re_eq_left_iff t |>.mpr ht1
      have hl := hI.1
      change SpecialPeriods.Triangle.stripLeft < (halfFordBoundaryParam t : ℍ).re at hl
      linarith
    · have hn :=
        (halfFordBoundaryParam_norm_add_one_eq_one_iff t).mpr ⟨le_of_not_ge ht0, le_of_not_ge ht1⟩
      have hgt := hI.2.2.2
      rw [hn] at hgt
      exact lt_irrefl _ hgt

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_injective :
    Function.Injective halfFordBoundaryParam := by
  intro s t he
  have hr := congrArg (fun z : SpecialPeriods.Triangle.halfFordRegion => (z : ℍ).re) he
  have hi := congrArg (fun z : SpecialPeriods.Triangle.halfFordRegion => (z : ℍ).im) he
  by_cases hs0 : s ≤ 0
  · have ht0 : t ≤ 0 :=
      (halfFordBoundaryParam_re_eq_centerOne_iff t).mp
        (hr.symm.trans (halfFordBoundaryParam_re_of_nonpos hs0))
    rw [halfFordBoundaryParam_im_of_nonpos hs0, halfFordBoundaryParam_im_of_nonpos ht0] at hi
    linarith
  · by_cases hs1 : 1 ≤ s
    · have ht1 : 1 ≤ t :=
        (halfFordBoundaryParam_re_eq_centerTwo_iff t).mp
          (hr.symm.trans (halfFordBoundaryParam_re_of_one_le hs1))
      rw [halfFordBoundaryParam_im_of_one_le hs1, halfFordBoundaryParam_im_of_one_le ht1] at hi
      linarith
    · have hs : 0 ≤ s ∧ s ≤ 1 := ⟨le_of_not_ge hs0, le_of_not_ge hs1⟩
      have ht : 0 ≤ t ∧ t ≤ 1 := by
        apply (halfFordBoundaryParam_norm_add_one_eq_one_iff t).mp
        rw [← he]
        exact (halfFordBoundaryParam_norm_add_one_eq_one_iff s).mpr hs
      rw [halfFordBoundaryParam_eq_circle hs.1 hs.2,
        halfFordBoundaryParam_eq_circle ht.1 ht.2] at he
      exact congrArg Subtype.val (halfFordCirclePoint_injective he)

private theorem PeriodFamily.Meridians.centerOne_im_eq_boundaryHeight_mo1973_23934 :
    SpecialPeriods.Triangle.centerOne.im =
      SpecialPeriods.Triangle.boundaryHeight SpecialPeriods.Triangle.centerOne.re := by
  simpa only [halfFordCirclePoint_zero] using halfFordCirclePoint_im 0

private theorem PeriodFamily.Meridians.centerTwo_im_eq_boundaryHeight_mo1973_23935 :
    SpecialPeriods.Triangle.centerTwo.im =
      SpecialPeriods.Triangle.boundaryHeight SpecialPeriods.Triangle.centerTwo.re := by
  simpa only [halfFordCirclePoint_one] using halfFordCirclePoint_im 1

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_range :
    Set.range halfFordBoundaryParam =
      {z : SpecialPeriods.Triangle.halfFordRegion |
        (z : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior} := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact halfFordBoundaryParam_notMem_interior t
  · intro hz
    have hclosed : ((z : ℍ) : ℂ) ∈ SpecialPeriods.Triangle.triangleClosedRegion :=
      (SpecialPeriods.Triangle.coe_mem_triangleClosedRegion_iff_halfFordRegion _).mpr z.property
    have hheight : SpecialPeriods.Triangle.boundaryHeight (z : ℍ).re ≤ (z : ℍ).im :=
      (SpecialPeriods.Triangle.mem_triangleClosedRegion_iff_epigraph _).mp hclosed |>.2.2
    by_cases hr : (z : ℍ).re = SpecialPeriods.Triangle.centerOne.re
    · have hi : SpecialPeriods.Triangle.centerOne.im ≤ (z : ℍ).im := by
        simpa only [hr, ← centerOne_im_eq_boundaryHeight_mo1973_23934] using hheight
      have ht : SpecialPeriods.Triangle.centerOne.im - (z : ℍ).im ≤ 0 := sub_nonpos.mpr hi
      refine
        ⟨SpecialPeriods.Triangle.centerOne.im - (z : ℍ).im,
          Subtype.ext (UpperHalfPlane.ext_re_im ?_ ?_)⟩
      · exact (halfFordBoundaryParam_re_of_nonpos ht).trans hr.symm
      · rw [halfFordBoundaryParam_im_of_nonpos ht]
        ring
    · by_cases hl : (z : ℍ).re = SpecialPeriods.Triangle.centerTwo.re
      · have hi : SpecialPeriods.Triangle.centerTwo.im ≤ (z : ℍ).im := by
          simpa only [hl, ← centerTwo_im_eq_boundaryHeight_mo1973_23935] using hheight
        have ht : 1 ≤ 1 + (z : ℍ).im - SpecialPeriods.Triangle.centerTwo.im := by linarith
        refine
          ⟨1 + (z : ℍ).im - SpecialPeriods.Triangle.centerTwo.im,
            Subtype.ext (UpperHalfPlane.ext_re_im ?_ ?_)⟩
        · exact (halfFordBoundaryParam_re_of_one_le ht).trans hl.symm
        · rw [halfFordBoundaryParam_im_of_one_le ht]
          ring
      · have hnorm : ‖((z : ℍ) : ℂ) + 1‖ = 1 := by
          by_contra hn
          have hleft : SpecialPeriods.Triangle.stripLeft < (z : ℍ).re := by
            have hc : SpecialPeriods.Triangle.centerTwo.re = SpecialPeriods.Triangle.stripLeft :=
              SpecialPeriods.Triangle.centerTwo_coe_re
            have hne : (z : ℍ).re ≠ SpecialPeriods.Triangle.stripLeft := fun he =>
              hl (he.trans hc.symm)
            exact lt_of_le_of_ne hclosed.1 hne.symm
          have hright : (z : ℍ).re < -1 / 2 := by
            have hc : SpecialPeriods.Triangle.centerOne.re = -1 / 2 :=
              SpecialPeriods.Triangle.centerOne_coe_re
            have hne : (z : ℍ).re ≠ -1 / 2 := fun he => hr (he.trans hc.symm)
            exact lt_of_le_of_ne hclosed.2.1 hne
          apply hz
          rw [SpecialPeriods.Triangle.halfFordInterior_eq_preimage_triangleInterior]
          exact
            ⟨hleft, hright, (z : ℍ).im_pos, lt_of_le_of_ne hclosed.2.2.2 (fun he => hn he.symm)⟩
        have hc : z ∈ Set.range halfFordCirclePoint := by
          rw [halfFordCirclePoint_range]
          exact hnorm
        obtain ⟨t, rfl⟩ := hc
        exact ⟨t, halfFordBoundaryParam_eq_circle t.property.1 t.property.2⟩

private theorem PeriodFamily.Meridians.halfFordBoundaryParam_mem_boundary_mo1973_23937 (t : ℝ) :
    (halfFordBoundaryParam t : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior := by
  change
    halfFordBoundaryParam t ∈
      {z : SpecialPeriods.Triangle.halfFordRegion |
        (z : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior}
  rw [← halfFordBoundaryParam_range]
  exact Set.mem_range_self t

private def PeriodFamily.Meridians.halfFordNormalizedBoundaryParam (t : ℝ) : ℝ :=
  halfFordBoundaryValue (halfFordBoundaryParam t)

private theorem PeriodFamily.Meridians.halfFordNormalizedBoundaryParam_continuous :
    Continuous halfFordNormalizedBoundaryParam :=
  halfFordBoundaryValue_continuous.comp continuous_halfFordBoundaryParam

private theorem PeriodFamily.Meridians.halfFordNormalizedBoundaryParam_injective :
    Function.Injective halfFordNormalizedBoundaryParam := by
  intro s t h
  apply halfFordBoundaryParam_injective
  exact
    halfFordBoundaryValue_injOn (halfFordBoundaryParam_mem_boundary_mo1973_23937 s)
      (halfFordBoundaryParam_mem_boundary_mo1973_23937 t) h

@[simp]
private theorem PeriodFamily.Meridians.halfFordNormalizedBoundaryParam_zero :
    halfFordNormalizedBoundaryParam 0 = 0 := by
  rw [halfFordNormalizedBoundaryParam, halfFordBoundaryParam_zero,
    halfFordBoundaryValue_centerOne]

@[simp]
private theorem PeriodFamily.Meridians.halfFordNormalizedBoundaryParam_one :
    halfFordNormalizedBoundaryParam 1 = 1 := by
  rw [halfFordNormalizedBoundaryParam, halfFordBoundaryParam_one, halfFordBoundaryValue_centerTwo]

private theorem PeriodFamily.Meridians.halfFordNormalizedBoundaryParam_strictMono :
    StrictMono halfFordNormalizedBoundaryParam := by
  apply
    (halfFordNormalizedBoundaryParam_continuous.strictMono_of_inj
        halfFordNormalizedBoundaryParam_injective).resolve_right
  intro h
  have hh := h (show (0 : ℝ) < 1 by norm_num)
  rw [halfFordNormalizedBoundaryParam_zero, halfFordNormalizedBoundaryParam_one] at hh
  linarith

private theorem PeriodFamily.Meridians.halfFordBoundaryValue_right_iff
    (z : SpecialPeriods.Triangle.halfFordRegion)
    (hz : (z : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior) :
    (z : ℍ).re = -(1 / 2) ↔ halfFordBoundaryValue z ≤ 0 := by
  have hm : z ∈ Set.range halfFordBoundaryParam := by
    rw [halfFordBoundaryParam_range]
    exact hz
  obtain ⟨t, rfl⟩ := hm
  rw [halfFordBoundaryParam_re_eq_right_iff]
  change t ≤ 0 ↔ halfFordNormalizedBoundaryParam t ≤ 0
  simpa only [halfFordNormalizedBoundaryParam_zero] using
    (halfFordNormalizedBoundaryParam_strictMono.le_iff_le (a := t) (b := 0)).symm

private theorem PeriodFamily.Meridians.halfFordBoundaryValue_left_iff
    (z : SpecialPeriods.Triangle.halfFordRegion)
    (hz : (z : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior) :
    (z : ℍ).re = SpecialPeriods.Triangle.stripLeft ↔ 1 ≤ halfFordBoundaryValue z := by
  have hm : z ∈ Set.range halfFordBoundaryParam := by
    rw [halfFordBoundaryParam_range]
    exact hz
  obtain ⟨t, rfl⟩ := hm
  rw [halfFordBoundaryParam_re_eq_left_iff]
  change 1 ≤ t ↔ 1 ≤ halfFordNormalizedBoundaryParam t
  simpa only [halfFordNormalizedBoundaryParam_one] using
    (halfFordNormalizedBoundaryParam_strictMono.le_iff_le (a := 1) (b := t)).symm

private theorem PeriodFamily.Meridians.halfFordBoundaryValue_circle_iff
    (z : SpecialPeriods.Triangle.halfFordRegion)
    (hz : (z : ℍ) ∉ SpecialPeriods.Triangle.halfFordInterior) :
    ‖((z : ℍ) : ℂ) + 1‖ = 1 ↔ halfFordBoundaryValue z ∈ Set.Icc (0 : ℝ) 1 := by
  have hm : z ∈ Set.range halfFordBoundaryParam := by
    rw [halfFordBoundaryParam_range]
    exact hz
  obtain ⟨t, rfl⟩ := hm
  rw [halfFordBoundaryParam_norm_add_one_eq_one_iff]
  change
    (0 ≤ t ∧ t ≤ 1) ↔
      (0 ≤ halfFordNormalizedBoundaryParam t ∧ halfFordNormalizedBoundaryParam t ≤ 1)
  apply and_congr
  · simpa only [halfFordNormalizedBoundaryParam_zero] using
      (halfFordNormalizedBoundaryParam_strictMono.le_iff_le (a := 0) (b := t)).symm
  · simpa only [halfFordNormalizedBoundaryParam_one] using
      (halfFordNormalizedBoundaryParam_strictMono.le_iff_le (a := t) (b := 1)).symm

private theorem PeriodFamily.Meridians.halfFordRealPreimage_re_eq_right_iff (x : ℝ) :
    (halfFordRealPreimage x : ℍ).re = -(1 / 2) ↔ x ≤ 0 := by
  simpa only [halfFordBoundaryValue_realPreimage] using
    halfFordBoundaryValue_right_iff (halfFordRealPreimage x)
      (halfFordRealPreimage_not_mem_interior x)

private theorem PeriodFamily.Meridians.halfFordRealPreimage_re_eq_left_iff (x : ℝ) :
    (halfFordRealPreimage x : ℍ).re = SpecialPeriods.Triangle.stripLeft ↔ 1 ≤ x := by
  simpa only [halfFordBoundaryValue_realPreimage] using
    halfFordBoundaryValue_left_iff (halfFordRealPreimage x)
      (halfFordRealPreimage_not_mem_interior x)

private theorem PeriodFamily.Meridians.halfFordRealPreimage_norm_add_one_eq_one_iff (x : ℝ) :
    ‖((halfFordRealPreimage x : ℍ) : ℂ) + 1‖ = 1 ↔ x ∈ Set.Icc (0 : ℝ) 1 := by
  simpa only [halfFordBoundaryValue_realPreimage] using
    halfFordBoundaryValue_circle_iff (halfFordRealPreimage x)
      (halfFordRealPreimage_not_mem_interior x)

private theorem PeriodFamily.Meridians.halfFordRealPreimage_rightReflection (x : ℝ) (hx : x ≤ 0) :
    SpecialPeriods.Triangle.rightReflection (halfFordRealPreimage x : ℍ) =
      (halfFordRealPreimage x : ℍ) :=
  (SpecialPeriods.Triangle.rightReflection_fixed_iff _).mpr
    ((halfFordRealPreimage_re_eq_right_iff x).mpr hx)

private theorem PeriodFamily.Meridians.halfFordRealPreimage_leftReflection (x : ℝ) (hx : 1 ≤ x) :
    SpecialPeriods.Triangle.leftReflection (halfFordRealPreimage x : ℍ) =
      (halfFordRealPreimage x : ℍ) :=
  (SpecialPeriods.Triangle.leftReflection_fixed_iff _).mpr
    ((halfFordRealPreimage_re_eq_left_iff x).mpr hx)

private theorem PeriodFamily.Meridians.halfFordRealPreimage_circleReflection (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    SpecialPeriods.Triangle.circleReflection (halfFordRealPreimage x : ℍ) =
      (halfFordRealPreimage x : ℍ) :=
  (SpecialPeriods.Triangle.circleReflection_fixed_iff _).mpr
    ((halfFordRealPreimage_norm_add_one_eq_one_iff x).mpr hx)

private def PeriodFamily.Meridians.halfPlaneMeridianBasepoint : RegularHalfPlane :=
  realHalfPlaneValue (1 / 2) (by norm_num) (by norm_num)

private def PeriodFamily.Meridians.halfPlaneMeridianLeftPoint : RegularHalfPlane :=
  realHalfPlaneValue (-1 / 2) (by norm_num) (by norm_num)

private def PeriodFamily.Meridians.halfPlaneMeridianRightPoint : RegularHalfPlane :=
  realHalfPlaneValue (3 / 2) (by norm_num) (by norm_num)

@[simp]
private theorem PeriodFamily.Meridians.halfPlaneValue_basepoint :
    halfPlaneValue halfPlaneMeridianBasepoint = SpecialPeriods.Triangle.meridianBasepoint := by
  apply Subtype.ext
  norm_num [halfPlaneValue, halfPlaneMeridianBasepoint, realHalfPlaneValue,
    SpecialPeriods.Triangle.meridianBasepoint]

@[simp]
private theorem PeriodFamily.Meridians.halfPlaneValue_leftPoint :
    halfPlaneValue halfPlaneMeridianLeftPoint = SpecialPeriods.Triangle.meridianLeftPoint := by
  apply Subtype.ext
  norm_num [halfPlaneValue, halfPlaneMeridianLeftPoint, realHalfPlaneValue,
    SpecialPeriods.Triangle.meridianLeftPoint]

@[simp]
private theorem PeriodFamily.Meridians.halfPlaneValue_rightPoint :
    halfPlaneValue halfPlaneMeridianRightPoint = SpecialPeriods.Triangle.meridianRightPoint := by
  apply Subtype.ext
  norm_num [halfPlaneValue, halfPlaneMeridianRightPoint, realHalfPlaneValue,
    SpecialPeriods.Triangle.meridianRightPoint]

private def PeriodFamily.Meridians.normalizedRegularMeridianBasepoint :
    SpecialPeriods.TriangleRegularPoint :=
  halfPlaneLift halfPlaneMeridianBasepoint

private def PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint :
    SpecialPeriods.TriangleRegularPoint :=
  halfPlaneLift halfPlaneMeridianLeftPoint

private def PeriodFamily.Meridians.normalizedRegularMeridianRightPoint :
    SpecialPeriods.TriangleRegularPoint :=
  halfPlaneLift halfPlaneMeridianRightPoint

@[simp]
private theorem PeriodFamily.Meridians.normalizedRegularMeridianBasepoint_coordinate :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject normalizedRegularMeridianBasepoint) =
      SpecialPeriods.Triangle.meridianBasepoint := by
  rw [normalizedRegularMeridianBasepoint, halfPlaneLift_projection, halfPlaneValue_basepoint]

@[simp]
private theorem PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint_coordinate :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject normalizedRegularMeridianLeftPoint) =
      SpecialPeriods.Triangle.meridianLeftPoint := by
  rw [normalizedRegularMeridianLeftPoint, halfPlaneLift_projection, halfPlaneValue_leftPoint]

@[simp]
private theorem PeriodFamily.Meridians.normalizedRegularMeridianRightPoint_coordinate :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject normalizedRegularMeridianRightPoint) =
      SpecialPeriods.Triangle.meridianRightPoint := by
  rw [normalizedRegularMeridianRightPoint, halfPlaneLift_projection, halfPlaneValue_rightPoint]

private theorem PeriodFamily.Meridians.normalizedRegularMeridianBasepoint_circleReflection :
    SpecialPeriods.Triangle.circleReflection (normalizedRegularMeridianBasepoint : ℍ) =
      (normalizedRegularMeridianBasepoint : ℍ) :=
  halfFordRealPreimage_circleReflection (1 / 2) (by norm_num)

private theorem PeriodFamily.Meridians.normalizedRegularMeridianLeftPoint_rightReflection :
    SpecialPeriods.Triangle.rightReflection (normalizedRegularMeridianLeftPoint : ℍ) =
      (normalizedRegularMeridianLeftPoint : ℍ) :=
  halfFordRealPreimage_rightReflection (-1 / 2) (by norm_num)

private theorem PeriodFamily.Meridians.normalizedRegularMeridianRightPoint_leftReflection :
    SpecialPeriods.Triangle.leftReflection (normalizedRegularMeridianRightPoint : ℍ) =
      (normalizedRegularMeridianRightPoint : ℍ) :=
  halfFordRealPreimage_leftReflection (3 / 2) (by norm_num)

@[simp]
private theorem PeriodFamily.Meridians.reflectedHalfPlaneLift_basepoint :
    reflectedHalfPlaneLift halfPlaneMeridianBasepoint = normalizedRegularMeridianBasepoint := by
  apply Subtype.ext
  exact normalizedRegularMeridianBasepoint_circleReflection

private theorem PeriodFamily.Meridians.circleReflection_eq_inverse_generatorOne (z : ℍ)
    (hz : SpecialPeriods.Triangle.rightReflection z = z) :
    SpecialPeriods.Triangle.circleReflection z =
      SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₁⁻¹ z := by
  rw [map_inv]
  apply
    (SpecialPeriods.triangleGeometricRepresentation
        SpecialPeriods.triangleGenerator₁).eq_symm_apply.mpr
  rw [SpecialPeriods.triangleGeometricRepresentation_generator₁_apply,
    SpecialPeriods.Triangle.generatorOne_reflections,
    SpecialPeriods.Triangle.circleReflection_involutive, hz]

private theorem PeriodFamily.Meridians.circleReflection_eq_generatorTwo (z : ℍ)
    (hz : SpecialPeriods.Triangle.leftReflection z = z) :
    SpecialPeriods.Triangle.circleReflection z =
      SpecialPeriods.triangleGeometricRepresentation SpecialPeriods.triangleGenerator₂ z := by
  rw [SpecialPeriods.triangleGeometricRepresentation_generator₂_apply,
    SpecialPeriods.Triangle.generatorTwo_reflections, hz]

@[simp]
private theorem PeriodFamily.Meridians.reflectedHalfPlaneLift_leftPoint :
    reflectedHalfPlaneLift halfPlaneMeridianLeftPoint =
      SpecialPeriods.triangleGenerator₁⁻¹ • normalizedRegularMeridianLeftPoint := by
  apply Subtype.ext
  exact
    circleReflection_eq_inverse_generatorOne _ normalizedRegularMeridianLeftPoint_rightReflection

@[simp]
private theorem PeriodFamily.Meridians.reflectedHalfPlaneLift_rightPoint :
    reflectedHalfPlaneLift halfPlaneMeridianRightPoint =
      SpecialPeriods.triangleGenerator₂ • normalizedRegularMeridianRightPoint := by
  apply Subtype.ext
  exact circleReflection_eq_generatorTwo _ normalizedRegularMeridianRightPoint_leftReflection

private def PeriodFamily.Meridians.halfPlaneZeroPath :
    Path halfPlaneMeridianBasepoint halfPlaneMeridianLeftPoint
    where
  toFun t := ⟨⟨(zeroHalfPath t : ℂ), zeroHalfPath_mem_halfPlane t⟩, (zeroHalfPath t).property⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp zeroHalfPath.continuous).subtype_mk _).subtype_mk _
  source' := by
    apply Subtype.ext
    apply Subtype.ext
    change (zeroHalfPath 0 : ℂ) = _
    rw [Path.source]
    norm_num [halfPlaneMeridianBasepoint, realHalfPlaneValue,
      SpecialPeriods.Triangle.meridianBasepoint]
  target' := by
    apply Subtype.ext
    apply Subtype.ext
    change (zeroHalfPath 1 : ℂ) = _
    rw [Path.target]
    norm_num [halfPlaneMeridianLeftPoint, realHalfPlaneValue,
      SpecialPeriods.Triangle.meridianLeftPoint]

private def PeriodFamily.Meridians.halfPlaneOnePath :
    Path halfPlaneMeridianBasepoint halfPlaneMeridianRightPoint
    where
  toFun t := ⟨⟨(oneHalfPath t : ℂ), oneHalfPath_mem_halfPlane t⟩, (oneHalfPath t).property⟩
  continuous_toFun :=
    ((continuous_subtype_val.comp oneHalfPath.continuous).subtype_mk _).subtype_mk _
  source' := by
    apply Subtype.ext
    apply Subtype.ext
    change (oneHalfPath 0 : ℂ) = _
    rw [Path.source]
    norm_num [halfPlaneMeridianBasepoint, realHalfPlaneValue,
      SpecialPeriods.Triangle.meridianBasepoint]
  target' := by
    apply Subtype.ext
    apply Subtype.ext
    change (oneHalfPath 1 : ℂ) = _
    rw [Path.target]
    norm_num [halfPlaneMeridianRightPoint, realHalfPlaneValue,
      SpecialPeriods.Triangle.meridianRightPoint]

@[simp]
private theorem PeriodFamily.Meridians.halfPlaneZeroPath_conjugateValue (t : unitInterval) :
    halfPlaneConjugateValue (halfPlaneZeroPath t) = oppositeZeroPath t := by
  apply Subtype.ext
  exact (oppositeZeroPath_coe t).symm

@[simp]
private theorem PeriodFamily.Meridians.halfPlaneOnePath_conjugateValue (t : unitInterval) :
    halfPlaneConjugateValue (halfPlaneOnePath t) = oppositeOnePath t := by
  apply Subtype.ext
  exact (oppositeOnePath_coe t).symm

private def PeriodFamily.Meridians.liftedZeroHalfPath :
    Path normalizedRegularMeridianBasepoint normalizedRegularMeridianLeftPoint :=
  halfPlaneZeroPath.map halfPlaneLift_continuous

private def PeriodFamily.Meridians.liftedOneHalfPath :
    Path normalizedRegularMeridianBasepoint normalizedRegularMeridianRightPoint :=
  halfPlaneOnePath.map halfPlaneLift_continuous

private def PeriodFamily.Meridians.reflectedZeroHalfPath :
    Path normalizedRegularMeridianBasepoint
      (SpecialPeriods.triangleGenerator₁⁻¹ • normalizedRegularMeridianLeftPoint) :=
  (halfPlaneZeroPath.map reflectedHalfPlaneLift_continuous).cast
    reflectedHalfPlaneLift_basepoint.symm reflectedHalfPlaneLift_leftPoint.symm

private def PeriodFamily.Meridians.reflectedOneHalfPath :
    Path normalizedRegularMeridianBasepoint
      (SpecialPeriods.triangleGenerator₂ • normalizedRegularMeridianRightPoint) :=
  (halfPlaneOnePath.map reflectedHalfPlaneLift_continuous).cast
    reflectedHalfPlaneLift_basepoint.symm reflectedHalfPlaneLift_rightPoint.symm

@[simp]
private theorem PeriodFamily.Meridians.liftedZeroHalfPath_coordinate (t : unitInterval) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (liftedZeroHalfPath t)) =
      zeroHalfPath t :=
  halfPlaneLift_projection (halfPlaneZeroPath t)

@[simp]
private theorem PeriodFamily.Meridians.liftedOneHalfPath_coordinate (t : unitInterval) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (liftedOneHalfPath t)) =
      oneHalfPath t :=
  halfPlaneLift_projection (halfPlaneOnePath t)

@[simp]
private theorem PeriodFamily.Meridians.reflectedZeroHalfPath_coordinate (t : unitInterval) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (reflectedZeroHalfPath t)) =
      oppositeZeroPath t :=
  (reflectedHalfPlaneLift_projection (halfPlaneZeroPath t)).trans
    (halfPlaneZeroPath_conjugateValue t)

@[simp]
private theorem PeriodFamily.Meridians.reflectedOneHalfPath_coordinate (t : unitInterval) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (reflectedOneHalfPath t)) =
      oppositeOnePath t :=
  (reflectedHalfPlaneLift_projection (halfPlaneOnePath t)).trans
    (halfPlaneOnePath_conjugateValue t)

private def
    PeriodFamily.Data.deckTransportHom {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [TopologicalSpace B] [ChartedSpace V B] [MulAction SpecialPeriods.TriangleGroup B]
    (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B) :
    FundamentalGroup D.BaseSpace (D.baseQuotient b) →* SpecialPeriods.TriangleGroup :=
  (MulEquiv.inv' SpecialPeriods.TriangleGroup).symm.toMonoidHom.comp
    (hq.fundamentalGroupToMulOpposite ⟨b, rfl⟩)

private theorem PeriodFamily.Data.deckTransportHom_monodromy {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    (D.deckTransportHom hq b γ)⁻¹ • b = (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) := by
  change ((hq.fundamentalGroupToMulOpposite ⟨b, rfl⟩ γ).unop⁻¹)⁻¹ • b = _
  rw [inv_inv]
  exact hq.unop_fundamentalGroupToMulOpposite_smul

private theorem PeriodFamily.Data.deckTransportHom_eq_of_inverse_endpoint {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (γ : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (g : SpecialPeriods.TriangleGroup)
    (hγ : (hq.isCoveringMap.monodromy γ ⟨b, rfl⟩ : B) = g⁻¹ • b) :
    D.deckTransportHom hq b γ = g := by
  let := hq.isCancelSMul
  apply inv_injective
  exact IsCancelSMul.right_cancel _ _ b ((D.deckTransportHom_monodromy hq b γ).trans hγ)

private def PeriodFamily.FlatTorus.periodVector : Lattice →+ RealPlane₄
    where
  toFun := Elliptic.realCast
  map_zero' := by ext i; simp [Elliptic.realCast]
  map_add' c d := by ext i; simp [Elliptic.realCast]

private theorem
    PeriodFamily.FlatTorus.periodVector_injective : Function.Injective periodVector := by
  intro c d h
  ext i
  have hi : (c i : ℝ) = (d i : ℝ) := congrFun h i
  exact_mod_cast hi

private theorem PeriodFamily.FlatTorus.periodVector_mem_standardLattice (c : Lattice) :
    periodVector c ∈ standardLattice :=
  (Elliptic.standardLattice_mem_iff _).mpr ⟨c, rfl⟩

private def PeriodFamily.FlatTorus.periodLatticeMap : Lattice →+ standardLattice :=
  periodVector.codRestrict standardLattice.toAddSubgroup periodVector_mem_standardLattice

private theorem
    PeriodFamily.FlatTorus.periodLatticeMap_bijective : Function.Bijective periodLatticeMap :=
  by
  constructor
  · intro c d h
    exact periodVector_injective (congrArg Subtype.val h)
  · intro z
    obtain ⟨c, hc⟩ := (Elliptic.standardLattice_mem_iff z).mp z.property
    exact ⟨c, Subtype.ext hc.symm⟩

private def PeriodFamily.FlatTorus.periodLatticeEquiv : Lattice ≃+ standardLattice :=
  AddEquiv.ofBijective periodLatticeMap periodLatticeMap_bijective

private def PeriodFamily.FlatTorus.latticeEquiv : standardLattice ≃+ Lattice :=
  periodLatticeEquiv.symm

private theorem PeriodFamily.FlatTorus.periodVector_latticeEquiv (z : standardLattice) :
    periodVector (latticeEquiv z) = z :=
  congrArg Subtype.val (periodLatticeEquiv.apply_symm_apply z)

private theorem PeriodFamily.FlatTorus.quotientCovering :
    IsAddQuotientCoveringMap standardLattice.mkQ standardLattice.toAddSubgroup := by
  apply standardLattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm
  change IsDiscrete (standardLattice : Set RealPlane₄)
  let : DiscreteTopology (standardLattice : Set RealPlane₄) := standardLattice_discrete
  exact DiscreteTopology.isDiscrete

private def PeriodFamily.FlatTorus.zeroLift : standardLattice.mkQ ⁻¹' ({0} : Set RealTorus₄) :=
  ⟨0, by simp⟩

private def PeriodFamily.FlatTorus.fundamentalGroupEquiv :
    FundamentalGroup RealTorus₄ 0 ≃* Multiplicative Lattice :=
  ((quotientCovering.fundamentalGroupEquiv zeroLift).trans MulOpposite.opMulEquiv.symm).trans
    latticeEquiv.toMultiplicative

private theorem PeriodFamily.FlatTorus.fundamentalGroupEquiv_monodromy
    (γ : FundamentalGroup RealTorus₄ 0) :
    periodVector (fundamentalGroupEquiv γ).toAdd =
      (quotientCovering.isCoveringMap.monodromy γ zeroLift : RealPlane₄) := by
  have h := quotientCovering.unop_fundamentalGroupToMulOpposite_smul (e := zeroLift) (γ := γ)
  change
    periodVector
        (latticeEquiv (quotientCovering.fundamentalGroupToMulOpposite zeroLift γ).unop.toAdd) =
      _
  rw [periodVector_latticeEquiv]
  change
    ((quotientCovering.fundamentalGroupToMulOpposite zeroLift γ).unop.toAdd : RealPlane₄) + 0 =
      _ at h
  simpa only [add_zero] using h

private theorem PeriodFamily.FlatTorus.mkQ_periodVector (c : Lattice) :
    standardLattice.mkQ (periodVector c) = 0 :=
  (Submodule.Quotient.mk_eq_zero standardLattice).mpr (periodVector_mem_standardLattice c)

private def PeriodFamily.FlatTorus.periodLoop (c : Lattice) : Path (0 : RealTorus₄) 0 :=
  ((Path.segment (0 : RealPlane₄) (periodVector c)).map standardLattice.continuous_mkQ).cast
    (map_zero standardLattice.mkQ).symm (mkQ_periodVector c).symm

private theorem PeriodFamily.FlatTorus.periodLoop_apply (c : Lattice) (t : unitInterval) :
    periodLoop c t = standardLattice.mkQ ((t : ℝ) • Elliptic.realCast c) := by
  change standardLattice.mkQ (Path.segment (0 : RealPlane₄) (Elliptic.realCast c) t) = _
  simp only [Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add]

private theorem PeriodFamily.FlatTorus.periodLoop_monodromy (c : Lattice) :
    quotientCovering.isCoveringMap.monodromy (FirstHurewicz.loopQuotient (periodLoop c))
        zeroLift =
      ⟨periodVector c, mkQ_periodVector c⟩ := by
  apply
    quotientCovering.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk (Path.segment (0 : RealPlane₄) (periodVector c)))
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

@[simp]
private theorem PeriodFamily.FlatTorus.fundamentalGroupEquiv_periodLoop (c : Lattice) :
    fundamentalGroupEquiv (FirstHurewicz.loopQuotient (periodLoop c)) = Multiplicative.ofAdd c := by
  apply Multiplicative.toAdd.injective
  apply periodVector_injective
  rw [fundamentalGroupEquiv_monodromy, periodLoop_monodromy]
  rfl

private theorem PeriodFamily.FlatTorus.fundamentalGroupEquiv_symm_apply (c : Lattice) :
    fundamentalGroupEquiv.symm (Multiplicative.ofAdd c) =
      FirstHurewicz.loopQuotient (periodLoop c) := by
  apply fundamentalGroupEquiv.injective
  rw [MulEquiv.apply_symm_apply, fundamentalGroupEquiv_periodLoop]

private def
    PeriodFamily.FlatTorus.singularH1Equiv : FirstHurewicz.SingularH1 RealTorus₄ ≃ₗ[ℤ] Lattice :=
  FirstHurewicz.singularH1EquivOfPi1 (0 : RealTorus₄) fundamentalGroupEquiv

@[simp]
private theorem
    PeriodFamily.FlatTorus.singularH1Equiv_loopHomologyClass (p : Path (0 : RealTorus₄) 0) :
    singularH1Equiv (FirstHurewicz.loopHomologyClass p) =
      (fundamentalGroupEquiv (FirstHurewicz.loopQuotient p)).toAdd :=
  FirstHurewicz.singularH1EquivOfPi1_loopHomologyClass (0 : RealTorus₄) fundamentalGroupEquiv p

private theorem PeriodFamily.FlatTorus.singularH1Equiv_periodLoop (c : Lattice) :
    singularH1Equiv (FirstHurewicz.loopHomologyClass (periodLoop c)) = c := by
  rw [singularH1Equiv_loopHomologyClass, fundamentalGroupEquiv_periodLoop]
  rfl

@[simp]
private theorem PeriodFamily.FlatTorus.singularH1Equiv_symm_apply (c : Lattice) :
    singularH1Equiv.symm c = FirstHurewicz.loopHomologyClass (periodLoop c) := by
  apply singularH1Equiv.injective
  rw [LinearEquiv.apply_symm_apply, singularH1Equiv_periodLoop]

private theorem PeriodFamily.FlatTorus.periodLoop_map_triangle (g : SpecialPeriods.TriangleGroup)
    (c : Lattice) :
    (periodLoop c).map (SpecialPeriods.triangleTorusHomeomorph g).continuous =
      (periodLoop ((SpecialPeriods.triangleDualRepresentation g : LatticeMatrix) *ᵥ c)).cast
        (SpecialPeriods.triangleTorusHomeomorph_zero g)
        (SpecialPeriods.triangleTorusHomeomorph_zero g) := by
  ext t
  change
    SpecialPeriods.triangleTorusHomeomorph g (periodLoop c t) =
      periodLoop ((SpecialPeriods.triangleDualRepresentation g : LatticeMatrix) *ᵥ c) t
  rw [periodLoop_apply, SpecialPeriods.triangleTorusHomeomorph_mkQ, periodLoop_apply, map_smul,
    SpecialPeriods.triangleRealEquiv_realCast]

private theorem PeriodFamily.FlatTorus.inducedHomology_periodLoop_triangle
    (g : SpecialPeriods.TriangleGroup) (c : Lattice) :
    FirstHurewicz.inducedHomology
        (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄))
        (FirstHurewicz.loopHomologyClass (periodLoop c)) =
      FirstHurewicz.loopHomologyClass
        (periodLoop ((SpecialPeriods.triangleDualRepresentation g : LatticeMatrix) *ᵥ c)) := by
  rw [FirstHurewicz.inducedHomology_loopHomologyClass, periodLoop_map_triangle]
  rfl

private theorem PeriodFamily.FlatTorus.singularH1Equiv_inducedHomology_triangle
    (g : SpecialPeriods.TriangleGroup) (a : FirstHurewicz.SingularH1 RealTorus₄) :
    singularH1Equiv
        (FirstHurewicz.inducedHomology
          (SpecialPeriods.triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) a) =
      (SpecialPeriods.triangleDualRepresentation g : LatticeMatrix) *ᵥ singularH1Equiv a := by
  obtain ⟨c, rfl⟩ := singularH1Equiv.symm.surjective a
  rw [singularH1Equiv_symm_apply, inducedHomology_periodLoop_triangle, singularH1Equiv_periodLoop,
    singularH1Equiv_periodLoop]

private theorem PeriodFamily.Data.periodEquiv_realCast {V B : Type} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B) (c : Lattice) :
    D.periods.periodEquiv b (Elliptic.realCast c) = (D.periods.point b).periodVector c := by
  rw [D.periodEquiv_matrix, PeriodDomain.periodVector_apply]
  simp only [Elliptic.realCast, Complex.ofReal_intCast]

private def PeriodFamily.Meridians.projectLift (b : SpecialPeriods.TriangleRegularPoint)
    (g : SpecialPeriods.TriangleGroup) (δ : Path b (g⁻¹ • b)) :
    Path (SpecialPeriods.triangleRegularProject b) (SpecialPeriods.triangleRegularProject b) :=
  (δ.map SpecialPeriods.triangleRegularProject_covering.continuous).cast rfl
    (SpecialPeriods.triangleRegularProject_covering.map_smul g⁻¹).symm

private theorem
    PeriodFamily.Meridians.projectLift_monodromy (b : SpecialPeriods.TriangleRegularPoint)
    (g : SpecialPeriods.TriangleGroup) (δ : Path b (g⁻¹ • b)) :
    SpecialPeriods.triangleRegularProject_covering.isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk (projectLift b g δ)) ⟨b, rfl⟩ =
      ⟨g⁻¹ • b, SpecialPeriods.triangleRegularProject_covering.map_smul g⁻¹⟩ := by
  apply
    SpecialPeriods.triangleRegularProject_covering.isCoveringMap.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk δ)
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

private theorem PeriodFamily.Meridians.trans_coordinate_mo1973_24201 {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {a b c : X} {x y z : Y} (f : X → Y) (p : Path a b)
    (q : Path b c) (α : Path x y) (β : Path y z) (hp : ∀ t : unitInterval, f (p t) = α t)
    (hq : ∀ t : unitInterval, f (q t) = β t) (t : unitInterval) :
    f ((p.trans q) t) = (α.trans β) t := by
  simp only [Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

private def PeriodFamily.Meridians.liftedMeridianZero :
    Path normalizedRegularMeridianBasepoint
      (SpecialPeriods.triangleGenerator₁⁻¹ • normalizedRegularMeridianBasepoint) :=
  reflectedZeroHalfPath.trans
    (liftedZeroHalfPath.symm.map
      (ContinuousConstSMul.continuous_const_smul SpecialPeriods.triangleGenerator₁⁻¹))

private def PeriodFamily.Meridians.liftedMeridianOne :
    Path normalizedRegularMeridianBasepoint
      (SpecialPeriods.triangleGenerator₂⁻¹ • normalizedRegularMeridianBasepoint) :=
  liftedOneHalfPath.trans
    ((reflectedOneHalfPath.symm.map
          (ContinuousConstSMul.continuous_const_smul SpecialPeriods.triangleGenerator₂⁻¹)).cast
      (inv_smul_smul SpecialPeriods.triangleGenerator₂ normalizedRegularMeridianRightPoint).symm
      rfl)

private theorem PeriodFamily.Meridians.liftedMeridianZero_coordinate (t : unitInterval) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (liftedMeridianZero t)) =
      compatiblePlanarMeridian Bool.false t := by
  change
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject
          ((reflectedZeroHalfPath.trans
              (liftedZeroHalfPath.symm.map
                (ContinuousConstSMul.continuous_const_smul SpecialPeriods.triangleGenerator₁⁻¹)))
            t)) =
      (oppositeZeroPath.trans zeroHalfPath.symm) t
  apply
    trans_coordinate_mo1973_24201
      (fun z =>
        SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
          (SpecialPeriods.triangleRegularProject z))
  · exact reflectedZeroHalfPath_coordinate
  · intro s
    change
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
          (SpecialPeriods.triangleRegularProject
            (SpecialPeriods.triangleGenerator₁⁻¹ • liftedZeroHalfPath (unitInterval.symm s))) =
        zeroHalfPath (unitInterval.symm s)
    rw [SpecialPeriods.triangleRegularProject_covering.map_smul]
    exact liftedZeroHalfPath_coordinate _

private theorem PeriodFamily.Meridians.liftedMeridianOne_coordinate (t : unitInterval) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (liftedMeridianOne t)) =
      compatiblePlanarMeridian Bool.true t := by
  change
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject
          ((liftedOneHalfPath.trans
              ((reflectedOneHalfPath.symm.map
                    (ContinuousConstSMul.continuous_const_smul
                      SpecialPeriods.triangleGenerator₂⁻¹)).cast
                (inv_smul_smul SpecialPeriods.triangleGenerator₂
                    normalizedRegularMeridianRightPoint).symm
                rfl))
            t)) =
      (oneHalfPath.trans oppositeOnePath.symm) t
  apply
    trans_coordinate_mo1973_24201
      (fun z =>
        SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
          (SpecialPeriods.triangleRegularProject z))
  · exact liftedOneHalfPath_coordinate
  · intro s
    change
      SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
          (SpecialPeriods.triangleRegularProject
            (SpecialPeriods.triangleGenerator₂⁻¹ • reflectedOneHalfPath (unitInterval.symm s))) =
        oppositeOnePath (unitInterval.symm s)
    rw [SpecialPeriods.triangleRegularProject_covering.map_smul]
    exact reflectedOneHalfPath_coordinate _

private def PeriodFamily.Meridians.compatibleMeridianGenerator : Bool → SpecialPeriods.TriangleGroup
  | false => SpecialPeriods.triangleGenerator₁
  | true => SpecialPeriods.triangleGenerator₂

private def PeriodFamily.Meridians.compatibleMeridianLift (b : Bool) :
    Path normalizedRegularMeridianBasepoint
      ((compatibleMeridianGenerator b)⁻¹ • normalizedRegularMeridianBasepoint) :=
  match b with
  | false => liftedMeridianZero
  | true => liftedMeridianOne

private theorem
    PeriodFamily.Meridians.compatibleMeridianLift_coordinate (b : Bool) (t : unitInterval) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
        (SpecialPeriods.triangleRegularProject (compatibleMeridianLift b t)) =
      compatiblePlanarMeridian b t := by
  cases b
  · exact liftedMeridianZero_coordinate t
  · exact liftedMeridianOne_coordinate t

private def PeriodFamily.Meridians.compatibleRegularMeridian (b : Bool) :
    Path (SpecialPeriods.triangleRegularProject normalizedRegularMeridianBasepoint)
      (SpecialPeriods.triangleRegularProject normalizedRegularMeridianBasepoint) :=
  projectLift normalizedRegularMeridianBasepoint (compatibleMeridianGenerator b)
    (compatibleMeridianLift b)

@[simp]
private theorem PeriodFamily.Meridians.compatibleRegularMeridian_coordinate (b : Bool)
    (t : unitInterval) :
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph (compatibleRegularMeridian b t) =
      compatiblePlanarMeridian b t :=
  compatibleMeridianLift_coordinate b t

private theorem PeriodFamily.Meridians.compatibleRegularMeridian_monodromy (b : Bool) :
    (SpecialPeriods.triangleRegularProject_covering.isCoveringMap.monodromy
          (Path.Homotopic.Quotient.mk (compatibleRegularMeridian b))
          ⟨normalizedRegularMeridianBasepoint, rfl⟩ :
        SpecialPeriods.TriangleRegularPoint) =
      (compatibleMeridianGenerator b)⁻¹ • normalizedRegularMeridianBasepoint :=
  congrArg Subtype.val (projectLift_monodromy _ _ _)

private def PeriodFamily.Meridians.compatibleRegularMeridianClass (b : Bool) :
    FundamentalGroup SpecialPeriods.TriangleRegularQuotient
      (SpecialPeriods.triangleRegularProject normalizedRegularMeridianBasepoint) :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (compatibleRegularMeridian b))

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Data.fundamentalGroupBasepoint {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B) : D.Space :=
  D.quotient (b, 0)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Data.flatFibreFundamentalGroupHom {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B) :
    FundamentalGroup RealTorus₄ 0 →* FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) :=
  FundamentalGroup.map
    ⟨fun x : RealTorus₄ => D.quotient (b, x),
      D.quotient_continuous.comp (continuous_const.prodMk continuous_id)⟩
    0

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Data.latticeFundamentalGroupHom {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B) :
    Multiplicative Lattice →* FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) :=
  (D.flatFibreFundamentalGroupHom b).comp
    PeriodFamily.FlatTorus.fundamentalGroupEquiv.symm.toMonoidHom

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Data.projectionFundamentalGroupHom {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B) :
    FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) →*
      FundamentalGroup D.BaseSpace (D.baseQuotient b) :=
  FundamentalGroup.map ⟨D.projection, D.projection_continuous⟩ (D.fundamentalGroupBasepoint b)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Data.sectionFundamentalGroupHom {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B) :
    FundamentalGroup D.BaseSpace (D.baseQuotient b) →*
      FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) :=
  FundamentalGroup.map ⟨D.zeroSection, D.zeroSection_continuous⟩ (D.baseQuotient b)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Data.projectionFundamentalGroupHom_comp_section {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B) :
    (D.projectionFundamentalGroupHom b).comp (D.sectionFundamentalGroupHom b) =
      MonoidHom.id (FundamentalGroup D.BaseSpace (D.baseQuotient b)) :=
  DiagonalQuotient.projectionFundamentalGroupHom_comp_section (0 : RealTorus₄)
    SpecialPeriods.triangleTorusAction_zero b

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Data.latticeFundamentalGroupHom_periodLoop {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B) (b : B) (v : Lattice) :
    D.latticeFundamentalGroupHom b (Multiplicative.ofAdd v) =
      D.flatFibreFundamentalGroupHom b
        (Path.Homotopic.Quotient.mk (PeriodFamily.FlatTorus.periodLoop v)) := by
  change
    D.flatFibreFundamentalGroupHom b
        (PeriodFamily.FlatTorus.fundamentalGroupEquiv.symm (Multiplicative.ofAdd v)) =
      _
  rw [PeriodFamily.FlatTorus.fundamentalGroupEquiv_symm_apply]
  rfl

@[instance_reducible]
private def
    PeriodFamily.FlatTorus.instMulAction1 : MulAction SpecialPeriods.TriangleGroup RealTorus₄ :=
  SpecialPeriods.triangleTorusAction

attribute [local instance] PeriodFamily.FlatTorus.instMulAction1 in
private theorem PeriodFamily.FlatTorus.instContinuousConstSMul1 :
    ContinuousConstSMul SpecialPeriods.TriangleGroup RealTorus₄ :=
  SpecialPeriods.triangleTorusAction_continuous

attribute [local instance] PeriodFamily.FlatTorus.instMulAction1
    PeriodFamily.FlatTorus.instContinuousConstSMul1 in
private theorem PeriodFamily.FlatTorus.fibreActionFundamentalGroupHom_periodLoop
    (g : SpecialPeriods.TriangleGroup) (c : Lattice) :
    DiagonalQuotient.fibreActionFundamentalGroupHom (0 : RealTorus₄)
        SpecialPeriods.triangleTorusAction_zero g (FirstHurewicz.loopQuotient (periodLoop c)) =
      FirstHurewicz.loopQuotient
        (periodLoop ((SpecialPeriods.triangleDualRepresentation g : LatticeMatrix) *ᵥ c)) := by
  rw [DiagonalQuotient.fibreActionFundamentalGroupHom, FundamentalGroup.mapOfEq_apply]
  change
    Path.Homotopic.Quotient.mk
        (((periodLoop c).map (SpecialPeriods.triangleTorusHomeomorph g).continuous).cast
          (SpecialPeriods.triangleTorusHomeomorph_zero g).symm
          (SpecialPeriods.triangleTorusHomeomorph_zero g).symm) =
      _
  rw [periodLoop_map_triangle]
  rfl

attribute [local instance] PeriodFamily.FlatTorus.instMulAction1
    PeriodFamily.FlatTorus.instContinuousConstSMul1 in
private theorem PeriodFamily.FlatTorus.fundamentalGroupEquiv_fibreAction
    (g : SpecialPeriods.TriangleGroup) (γ : FundamentalGroup RealTorus₄ 0) :
    fundamentalGroupEquiv
        (DiagonalQuotient.fibreActionFundamentalGroupHom (0 : RealTorus₄)
          SpecialPeriods.triangleTorusAction_zero g γ) =
      SpecialPeriods.triangleLatticeMulAutHom g (fundamentalGroupEquiv γ) := by
  obtain ⟨c, rfl⟩ := fundamentalGroupEquiv.symm.surjective γ
  change
    fundamentalGroupEquiv
        (DiagonalQuotient.fibreActionFundamentalGroupHom (0 : RealTorus₄)
          SpecialPeriods.triangleTorusAction_zero g
          (fundamentalGroupEquiv.symm (Multiplicative.ofAdd c.toAdd))) =
      _
  rw [fundamentalGroupEquiv_symm_apply, fibreActionFundamentalGroupHom_periodLoop,
    fundamentalGroupEquiv_periodLoop, MulEquiv.apply_symm_apply]
  rfl

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Data.flatFibreFundamentalGroupHom_injective {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B) :
    Function.Injective (D.flatFibreFundamentalGroupHom b) :=
  DiagonalQuotient.fibreFundamentalGroupHom_injective hq b (0 : RealTorus₄)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Data.latticeFundamentalGroupHom_injective {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B) :
    Function.Injective (D.latticeFundamentalGroupHom b) :=
  (D.flatFibreFundamentalGroupHom_injective hq b).comp
    PeriodFamily.FlatTorus.fundamentalGroupEquiv.symm.injective

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Data.latticeFundamentalGroupHom_range_eq_ker {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B) :
    (D.latticeFundamentalGroupHom b).range = (D.projectionFundamentalGroupHom b).ker := by
  have hflat :
    (D.flatFibreFundamentalGroupHom b).range = (D.projectionFundamentalGroupHom b).ker :=
    DiagonalQuotient.fibreFundamentalGroupHom_range_eq_ker hq b (0 : RealTorus₄)
  rw [← hflat]
  ext γ
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨PeriodFamily.FlatTorus.fundamentalGroupEquiv.symm v, rfl⟩
  · rintro ⟨δ, rfl⟩
    refine ⟨PeriodFamily.FlatTorus.fundamentalGroupEquiv δ, ?_⟩
    change
      D.flatFibreFundamentalGroupHom b
          (PeriodFamily.FlatTorus.fundamentalGroupEquiv.symm
            (PeriodFamily.FlatTorus.fundamentalGroupEquiv δ)) =
        _
    rw [MulEquiv.symm_apply_apply]

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Data.fundamentalGroupAction {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B) :
    FundamentalGroup D.BaseSpace (D.baseQuotient b) →* MulAut (Multiplicative Lattice) :=
  SpecialPeriods.triangleLatticeMulAutHom.comp (D.deckTransportHom hq b)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private theorem PeriodFamily.Data.latticeFundamentalGroupHom_conjugation {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (β : FundamentalGroup D.BaseSpace (D.baseQuotient b)) (v : Multiplicative Lattice) :
    D.latticeFundamentalGroupHom b (D.fundamentalGroupAction hq b β v) =
      D.sectionFundamentalGroupHom b β * D.latticeFundamentalGroupHom b v *
        (D.sectionFundamentalGroupHom b β)⁻¹ := by
  have hmark :
    PeriodFamily.FlatTorus.fundamentalGroupEquiv.symm
        (SpecialPeriods.triangleLatticeMulAutHom (D.deckTransportHom hq b β) v) =
      DiagonalQuotient.fibreActionFundamentalGroupHom (0 : RealTorus₄)
        SpecialPeriods.triangleTorusAction_zero (D.deckTransportHom hq b β)
        (PeriodFamily.FlatTorus.fundamentalGroupEquiv.symm v) := by
    apply PeriodFamily.FlatTorus.fundamentalGroupEquiv.injective
    simp only [PeriodFamily.FlatTorus.fundamentalGroupEquiv_fibreAction,
      MulEquiv.apply_symm_apply]
  change
    D.flatFibreFundamentalGroupHom b
        (PeriodFamily.FlatTorus.fundamentalGroupEquiv.symm
          (SpecialPeriods.triangleLatticeMulAutHom (D.deckTransportHom hq b β) v)) =
      _
  rw [hmark]
  exact
    (DiagonalQuotient.sectionFundamentalGroupHom_conjugate_fibre hq (0 : RealTorus₄)
        SpecialPeriods.triangleTorusAction_zero b β
        (PeriodFamily.FlatTorus.fundamentalGroupEquiv.symm v)).symm

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Data.semidirectFundamentalGroupEquiv {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B) :
    (Multiplicative Lattice) ⋊[D.fundamentalGroupAction hq b]
        (FundamentalGroup D.BaseSpace (D.baseQuotient b)) ≃*
      FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) :=
  SplitGroupExtension.mulEquiv (D.latticeFundamentalGroupHom b)
    (D.projectionFundamentalGroupHom b) (D.sectionFundamentalGroupHom b)
    (D.fundamentalGroupAction hq b) (D.latticeFundamentalGroupHom_injective hq b)
    (D.projectionFundamentalGroupHom_comp_section b)
    (D.latticeFundamentalGroupHom_range_eq_ker hq b)
    (D.latticeFundamentalGroupHom_conjugation hq b)

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
private def PeriodFamily.Data.fundamentalGroupSemidirectEquiv {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B) :
    FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) ≃*
      (Multiplicative Lattice) ⋊[D.fundamentalGroupAction hq b]
        (FundamentalGroup D.BaseSpace (D.baseQuotient b)) :=
  (D.semidirectFundamentalGroupEquiv hq b).symm

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Data.fundamentalGroupSemidirectEquiv_lattice {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (v : Multiplicative Lattice) :
    D.fundamentalGroupSemidirectEquiv hq b (D.latticeFundamentalGroupHom b v) =
      SemidirectProduct.inl v :=
  SplitGroupExtension.mulEquiv_symm_inclusion _ _ _ _ _ _ _ _ v

attribute [local instance] SpecialPeriods.triangleTorusAction
    SpecialPeriods.triangleTorusAction_continuous in
@[simp]
private theorem PeriodFamily.Data.fundamentalGroupSemidirectEquiv_section {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (β : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    D.fundamentalGroupSemidirectEquiv hq b (D.sectionFundamentalGroupHom b β) =
      SemidirectProduct.inr β :=
  SplitGroupExtension.mulEquiv_symm_section _ _ _ _ _ _ _ _ β

private def PeriodFamily.Data.freeFundamentalGroupAction {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (e : FundamentalGroup D.BaseSpace (D.baseQuotient b) ≃* FreeGroup Bool) :
    FreeGroup Bool →* MulAut (Multiplicative Lattice) :=
  (D.fundamentalGroupAction hq b).comp e.symm.toMonoidHom

private def PeriodFamily.Data.semidirectFreeReparametrization {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (e : FundamentalGroup D.BaseSpace (D.baseQuotient b) ≃* FreeGroup Bool) :
    (Multiplicative Lattice) ⋊[D.fundamentalGroupAction hq b]
        (FundamentalGroup D.BaseSpace (D.baseQuotient b)) ≃*
      (Multiplicative Lattice) ⋊[D.freeFundamentalGroupAction hq b e] (FreeGroup Bool) := by
  refine SemidirectProduct.congr (MulEquiv.refl (Multiplicative Lattice)) e ?_
  intro β
  apply MulEquiv.ext
  intro v
  change D.fundamentalGroupAction hq b β v = D.fundamentalGroupAction hq b (e.symm (e β)) v
  rw [MulEquiv.symm_apply_apply]

@[simp]
private theorem
    PeriodFamily.Data.semidirectFreeReparametrization_inl {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (e : FundamentalGroup D.BaseSpace (D.baseQuotient b) ≃* FreeGroup Bool)
    (v : Multiplicative Lattice) :
    D.semidirectFreeReparametrization hq b e (SemidirectProduct.inl v) =
      SemidirectProduct.inl v := by
  apply SemidirectProduct.ext
  · rfl
  · exact e.map_one

@[simp]
private theorem
    PeriodFamily.Data.semidirectFreeReparametrization_inr {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (e : FundamentalGroup D.BaseSpace (D.baseQuotient b) ≃* FreeGroup Bool)
    (β : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    D.semidirectFreeReparametrization hq b e (SemidirectProduct.inr β) =
      SemidirectProduct.inr (e β) :=
  rfl

private def
    PeriodFamily.Data.fundamentalGroupFreeSemidirectEquiv {V B : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (e : FundamentalGroup D.BaseSpace (D.baseQuotient b) ≃* FreeGroup Bool) :
    FundamentalGroup D.Space (D.fundamentalGroupBasepoint b) ≃*
      (Multiplicative Lattice) ⋊[D.freeFundamentalGroupAction hq b e] (FreeGroup Bool) :=
  (D.fundamentalGroupSemidirectEquiv hq b).trans (D.semidirectFreeReparametrization hq b e)

@[simp]
private theorem PeriodFamily.Data.fundamentalGroupFreeSemidirectEquiv_lattice {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (e : FundamentalGroup D.BaseSpace (D.baseQuotient b) ≃* FreeGroup Bool)
    (v : Multiplicative Lattice) :
    D.fundamentalGroupFreeSemidirectEquiv hq b e (D.latticeFundamentalGroupHom b v) =
      SemidirectProduct.inl v := by
  change
    D.semidirectFreeReparametrization hq b e
        (D.fundamentalGroupSemidirectEquiv hq b (D.latticeFundamentalGroupHom b v)) =
      _
  rw [D.fundamentalGroupSemidirectEquiv_lattice, D.semidirectFreeReparametrization_inl]

@[simp]
private theorem PeriodFamily.Data.fundamentalGroupFreeSemidirectEquiv_section {V B : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [TopologicalSpace B] [ChartedSpace V B]
    [MulAction SpecialPeriods.TriangleGroup B] (D : PeriodFamily.Data V B)
    (hq : IsQuotientCoveringMap D.baseQuotient SpecialPeriods.TriangleGroup) (b : B)
    (e : FundamentalGroup D.BaseSpace (D.baseQuotient b) ≃* FreeGroup Bool)
    (β : FundamentalGroup D.BaseSpace (D.baseQuotient b)) :
    D.fundamentalGroupFreeSemidirectEquiv hq b e (D.sectionFundamentalGroupHom b β) =
      SemidirectProduct.inr (e β) := by
  change
    D.semidirectFreeReparametrization hq b e
        (D.fundamentalGroupSemidirectEquiv hq b (D.sectionFundamentalGroupHom b β)) =
      _
  rw [D.fundamentalGroupSemidirectEquiv_section, D.semidirectFreeReparametrization_inr]

private def PeriodFamily.Meridians.pointedHomeomorphFundamentalGroupEquiv_mo1973_24733
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {x : X} {y : Y}
    (h : e x = y) : FundamentalGroup X x ≃* FundamentalGroup Y y
    where
  __ := FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h
  invFun :=
    FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
      ((congrArg e.symm h).symm.trans (e.symm_apply_apply x))
  left_inv
    γ := by
    change
      FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
          ((congrArg e.symm h).symm.trans (e.symm_apply_apply x))
          (FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h γ) =
        γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.symm_apply_apply (γ t)
  right_inv
    γ := by
    change
      FundamentalGroup.mapOfEq ⟨e, e.continuous⟩ h
          (FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
            ((congrArg e.symm h).symm.trans (e.symm_apply_apply x)) γ) =
        γ
    rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.apply_symm_apply (γ t)

private def PeriodFamily.Meridians.compatibleBasePlaneEquiv :
    FundamentalGroup SpecialPeriods.TriangleRegularQuotient
        (SpecialPeriods.triangleRegularProject normalizedRegularMeridianBasepoint) ≃*
      FundamentalGroup SpecialPeriods.Triangle.TwicePuncturedPlane
        SpecialPeriods.Triangle.meridianBasepoint :=
  pointedHomeomorphFundamentalGroupEquiv_mo1973_24733
    SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph
    normalizedRegularMeridianBasepoint_coordinate

@[simp]
private theorem PeriodFamily.Meridians.compatibleBasePlaneEquiv_apply
    (γ :
      FundamentalGroup SpecialPeriods.TriangleRegularQuotient
        (SpecialPeriods.triangleRegularProject normalizedRegularMeridianBasepoint)) :
    compatibleBasePlaneEquiv γ =
      FundamentalGroup.mapOfEq
        ⟨SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph,
          SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.continuous⟩
        normalizedRegularMeridianBasepoint_coordinate γ :=
  rfl

private theorem PeriodFamily.Meridians.compatibleBasePlaneEquiv_meridianClass (b : Bool) :
    compatibleBasePlaneEquiv (compatibleRegularMeridianClass b) =
      FreeMeridianMarking.orientedClass normalizationReversesMeridians b := by
  rw [compatibleBasePlaneEquiv_apply, FundamentalGroup.mapOfEq_apply, ←
    compatiblePlanarMeridian_class]
  apply congrArg Path.Homotopic.Quotient.mk
  apply Path.ext
  funext t
  exact compatibleRegularMeridian_coordinate b t

private def PeriodFamily.Meridians.compatibleRegularFundamentalGroupEquiv :
    FundamentalGroup SpecialPeriods.TriangleRegularQuotient
        (SpecialPeriods.triangleRegularProject normalizedRegularMeridianBasepoint) ≃*
      FreeGroup Bool :=
  compatibleBasePlaneEquiv.trans
    (FreeMeridianMarking.orientedEquiv normalizationReversesMeridians)

@[simp]
private theorem
    PeriodFamily.Meridians.compatibleRegularFundamentalGroupEquiv_meridianClass (b : Bool) :
    compatibleRegularFundamentalGroupEquiv (compatibleRegularMeridianClass b) = FreeGroup.of b := by
  change
    FreeMeridianMarking.orientedEquiv normalizationReversesMeridians
        (compatibleBasePlaneEquiv (compatibleRegularMeridianClass b)) =
      _
  rw [compatibleBasePlaneEquiv_meridianClass, FreeMeridianMarking.orientedEquiv_orientedClass]

@[simp]
private theorem PeriodFamily.Meridians.compatibleRegularFundamentalGroupEquiv_symm_of (b : Bool) :
    compatibleRegularFundamentalGroupEquiv.symm (FreeGroup.of b) =
      compatibleRegularMeridianClass b := by
  apply compatibleRegularFundamentalGroupEquiv.injective
  rw [MulEquiv.apply_symm_apply, compatibleRegularFundamentalGroupEquiv_meridianClass]

private def PeriodFamily.Meridians.sourceFreeTriangleHom :
    FreeGroup Bool →* SpecialPeriods.TriangleGroup :=
  FreeGroup.lift compatibleMeridianGenerator

@[simp]
private theorem PeriodFamily.Meridians.sourceFreeTriangleHom_of (b : Bool) :
    sourceFreeTriangleHom (FreeGroup.of b) = compatibleMeridianGenerator b :=
  FreeGroup.lift_apply_of

private def PeriodFamily.Meridians.sourceFreeLatticeAction :
    FreeGroup Bool →* MulAut (Multiplicative Lattice) :=
  SpecialPeriods.triangleLatticeMulAutHom.comp sourceFreeTriangleHom

@[simp]
private theorem PeriodFamily.Meridians.sourceFreeLatticeAction_of (b : Bool) :
    sourceFreeLatticeAction (FreeGroup.of b) =
      SpecialPeriods.triangleLatticeMulAutHom (compatibleMeridianGenerator b) := by
  change SpecialPeriods.triangleLatticeMulAutHom (sourceFreeTriangleHom (FreeGroup.of b)) = _
  rw [sourceFreeTriangleHom_of]

private theorem PeriodFamily.Meridians.sourceFreeLatticeAction_first (v : Multiplicative Lattice) :
    (sourceFreeLatticeAction (FreeGroup.of Bool.false) v).toAdd = A₁ *ᵥ v.toAdd := by
  rw [sourceFreeLatticeAction_of, SpecialPeriods.triangleLatticeMulAutHom_toAdd]
  exact
    congrArg (fun A : LatticeMatrix => A *ᵥ v.toAdd)
      SpecialPeriods.triangleDualRepresentation_generator₁_matrix

private theorem PeriodFamily.Meridians.sourceFreeLatticeAction_second (v : Multiplicative Lattice) :
    (sourceFreeLatticeAction (FreeGroup.of Bool.true) v).toAdd = A₂ *ᵥ v.toAdd := by
  rw [sourceFreeLatticeAction_of, SpecialPeriods.triangleLatticeMulAutHom_toAdd]
  exact
    congrArg (fun A : LatticeMatrix => A *ᵥ v.toAdd)
      SpecialPeriods.triangleDualRepresentation_generator₂_matrix

private theorem PeriodFamily.compatibleMeridian_deckTransport (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (b : Bool) :
    ((regularData P h₁ h₂)).deckTransportHom (regularCovering P h₁ h₂)
        (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
        (Meridians.compatibleRegularMeridianClass b) =
      Meridians.compatibleMeridianGenerator b :=
  ((regularData P h₁ h₂)).deckTransportHom_eq_of_inverse_endpoint (regularCovering P h₁ h₂)
    (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) _ _
    (Meridians.compatibleRegularMeridian_monodromy b)

private def PeriodFamily.markedRegularFundamentalGroupAction (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    FreeGroup Bool →* MulAut (Multiplicative Lattice) :=
  ((regularData P h₁ h₂)).freeFundamentalGroupAction (regularCovering P h₁ h₂)
    (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
    Meridians.compatibleRegularFundamentalGroupEquiv

@[simp]
private theorem PeriodFamily.markedRegularFundamentalGroupAction_of (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (b : Bool) :
    markedRegularFundamentalGroupAction P h₁ h₂ (FreeGroup.of b) =
      SpecialPeriods.triangleLatticeMulAutHom (Meridians.compatibleMeridianGenerator b) := by
  change
    SpecialPeriods.triangleLatticeMulAutHom
        (((regularData P h₁ h₂)).deckTransportHom (regularCovering P h₁ h₂)
          (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
          (Meridians.compatibleRegularFundamentalGroupEquiv.symm (FreeGroup.of b))) =
      _
  rw [Meridians.compatibleRegularFundamentalGroupEquiv_symm_of, compatibleMeridian_deckTransport]

private theorem PeriodFamily.markedRegularFundamentalGroupAction_eq (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    markedRegularFundamentalGroupAction P h₁ h₂ = Meridians.sourceFreeLatticeAction := by
  apply FreeGroup.ext_hom
  intro b
  rw [markedRegularFundamentalGroupAction_of, Meridians.sourceFreeLatticeAction_of]

private def PeriodFamily.markedSemidirectReparametrization (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    (Multiplicative Lattice) ⋊[markedRegularFundamentalGroupAction P h₁ h₂] (FreeGroup Bool) ≃*
      (Multiplicative Lattice) ⋊[Meridians.sourceFreeLatticeAction] (FreeGroup Bool) := by
  refine SemidirectProduct.congr (MulEquiv.refl _) (MulEquiv.refl _) ?_
  intro w
  apply MulEquiv.ext
  intro v
  change markedRegularFundamentalGroupAction P h₁ h₂ w v = Meridians.sourceFreeLatticeAction w v
  rw [markedRegularFundamentalGroupAction_eq]

@[simp]
private theorem PeriodFamily.markedSemidirectReparametrization_inl (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (v : Multiplicative Lattice) :
    markedSemidirectReparametrization P h₁ h₂ (SemidirectProduct.inl v) =
      SemidirectProduct.inl v :=
  rfl

@[simp]
private theorem PeriodFamily.markedSemidirectReparametrization_inr (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (w : FreeGroup Bool) :
    markedSemidirectReparametrization P h₁ h₂ (SemidirectProduct.inr w) =
      SemidirectProduct.inr w :=
  rfl

private def PeriodFamily.markedRegularFundamentalGroupEquiv (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    FundamentalGroup ((regularData P h₁ h₂)).Space
        (((regularData P h₁ h₂)).fundamentalGroupBasepoint
          (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)) ≃*
      (Multiplicative Lattice) ⋊[Meridians.sourceFreeLatticeAction] (FreeGroup Bool) :=
  (((regularData P h₁ h₂)).fundamentalGroupFreeSemidirectEquiv (regularCovering P h₁ h₂)
        (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
        Meridians.compatibleRegularFundamentalGroupEquiv).trans
    (markedSemidirectReparametrization P h₁ h₂)

@[simp]
private theorem
    PeriodFamily.markedRegularFundamentalGroupEquiv_lattice (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (v : Multiplicative Lattice) :
    markedRegularFundamentalGroupEquiv P h₁ h₂
        (((regularData P h₁ h₂)).latticeFundamentalGroupHom
          (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) v) =
      SemidirectProduct.inl v := by
  change
    markedSemidirectReparametrization P h₁ h₂
        (((regularData P h₁ h₂)).fundamentalGroupFreeSemidirectEquiv (regularCovering P h₁ h₂)
          (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
          Meridians.compatibleRegularFundamentalGroupEquiv
          (((regularData P h₁ h₂)).latticeFundamentalGroupHom
            (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) v)) =
      _
  exact
    (congrArg (markedSemidirectReparametrization P h₁ h₂)
          (((regularData P h₁ h₂)).fundamentalGroupFreeSemidirectEquiv_lattice
            (regularCovering P h₁ h₂) (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
            Meridians.compatibleRegularFundamentalGroupEquiv v)).trans
      (markedSemidirectReparametrization_inl P h₁ h₂ v)

@[simp]
private theorem
    PeriodFamily.markedRegularFundamentalGroupEquiv_meridian (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (b : Bool) :
    markedRegularFundamentalGroupEquiv P h₁ h₂
        (((regularData P h₁ h₂)).sectionFundamentalGroupHom
          (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
          (Meridians.compatibleRegularMeridianClass b)) =
      SemidirectProduct.inr (FreeGroup.of b) := by
  change
    markedSemidirectReparametrization P h₁ h₂
        (((regularData P h₁ h₂)).fundamentalGroupFreeSemidirectEquiv (regularCovering P h₁ h₂)
          (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
          Meridians.compatibleRegularFundamentalGroupEquiv
          (((regularData P h₁ h₂)).sectionFundamentalGroupHom
            (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
            (Meridians.compatibleRegularMeridianClass b))) =
      _
  have hs :=
    congrArg (markedSemidirectReparametrization P h₁ h₂)
      (((regularData P h₁ h₂)).fundamentalGroupFreeSemidirectEquiv_section
        (regularCovering P h₁ h₂) (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
        Meridians.compatibleRegularFundamentalGroupEquiv
        (Meridians.compatibleRegularMeridianClass b))
  exact
    hs.trans
      ((congrArg
            (fun w : FreeGroup Bool =>
              markedSemidirectReparametrization P h₁ h₂ (SemidirectProduct.inr w))
            (Meridians.compatibleRegularFundamentalGroupEquiv_meridianClass b)).trans
        (markedSemidirectReparametrization_inr P h₁ h₂ (FreeGroup.of b)))

public
theorem PeriodFamily.freeSemidirect_subgroup_eq_top {N α : Type*} [Group N]
    (φ : FreeGroup α →* MulAut N) (S : Subgroup (N ⋊[φ] FreeGroup α))
    (hN : ∀ n, SemidirectProduct.inl n ∈ S)
    (hG : ∀ a, SemidirectProduct.inr (FreeGroup.of a) ∈ S) : S = ⊤ := by
  have hc :
    (⊤ : Subgroup (FreeGroup α)) ≤
      S.comap (SemidirectProduct.inr : FreeGroup α →* N ⋊[φ] FreeGroup α) := by
    rw [← FreeGroup.closure_range_of α]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨a, rfl⟩
    exact hG a
  apply top_unique
  intro x _
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  exact S.mul_mem (hN x.left) (hc (Subgroup.mem_top x.right))

private def PeriodFamily.markedRegularFundamentalGroupGenerators (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Set
      (FundamentalGroup ((regularData P h₁ h₂)).Space
        (((regularData P h₁ h₂)).fundamentalGroupBasepoint
          (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint))) :=
  Set.range
      (((regularData P h₁ h₂)).latticeFundamentalGroupHom
        (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)) ∪
    Set.range
      (fun b : Bool =>
        ((regularData P h₁ h₂)).sectionFundamentalGroupHom
          (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
          (Meridians.compatibleRegularMeridianClass b))

private theorem
    PeriodFamily.markedRegularFundamentalGroup_subgroup_eq_top (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    (S :
      Subgroup
        (FundamentalGroup ((regularData P h₁ h₂)).Space
          (((regularData P h₁ h₂)).fundamentalGroupBasepoint
            (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint))))
    (hL :
      ∀ v : Multiplicative Lattice,
        ((regularData P h₁ h₂)).latticeFundamentalGroupHom
            (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) v ∈
          S)
    (hM :
      ∀ b : Bool,
        ((regularData P h₁ h₂)).sectionFundamentalGroupHom
            (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
            (Meridians.compatibleRegularMeridianClass b) ∈
          S) :
    S = ⊤ := by
  let e := markedRegularFundamentalGroupEquiv P h₁ h₂
  have hmap : S.map e.toMonoidHom = ⊤ := by
    apply freeSemidirect_subgroup_eq_top
    · intro v
      exact
        ⟨((regularData P h₁ h₂)).latticeFundamentalGroupHom
            (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) v,
          hL v, markedRegularFundamentalGroupEquiv_lattice P h₁ h₂ v⟩
    · intro b
      exact
        ⟨((regularData P h₁ h₂)).sectionFundamentalGroupHom
            (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
            (Meridians.compatibleRegularMeridianClass b),
          hM b, markedRegularFundamentalGroupEquiv_meridian P h₁ h₂ b⟩
  apply top_unique
  intro γ _
  have hγ : e γ ∈ S.map e.toMonoidHom := by
    rw [hmap]
    trivial
  obtain ⟨δ, hδ, he⟩ := hγ
  exact e.injective he ▸ hδ

private theorem PeriodFamily.markedRegularFundamentalGroup_generators_closure
    (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂) :
    Subgroup.closure (markedRegularFundamentalGroupGenerators P h₁ h₂) = ⊤ := by
  apply markedRegularFundamentalGroup_subgroup_eq_top P h₁ h₂
  · intro v
    exact Subgroup.subset_closure (Or.inl ⟨v, rfl⟩)
  · intro b
    exact Subgroup.subset_closure (Or.inr ⟨b, rfl⟩)

private theorem PeriodFamily.markedRegularFundamentalGroupHom_ext (P : HolomorphicPeriodMap ℂ ℍ)
    (h₁ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorOneSL • z) = (P.point z).step₁)
    (h₂ : ∀ z : ℍ, P.point (SpecialPeriods.Triangle.generatorTwoSL • z) = (P.point z).step₂)
    {A : Type*} [Monoid A]
    (f g :
      FundamentalGroup ((regularData P h₁ h₂)).Space
          (((regularData P h₁ h₂)).fundamentalGroupBasepoint
            (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)) →*
        A)
    (hL :
      ∀ v : Multiplicative Lattice,
        f
            (((regularData P h₁ h₂)).latticeFundamentalGroupHom
              (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) v) =
          g
            (((regularData P h₁ h₂)).latticeFundamentalGroupHom
              (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint) v))
    (hM :
      ∀ b : Bool,
        f
            (((regularData P h₁ h₂)).sectionFundamentalGroupHom
              (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
              (Meridians.compatibleRegularMeridianClass b)) =
          g
            (((regularData P h₁ h₂)).sectionFundamentalGroupHom
              (PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)
              (Meridians.compatibleRegularMeridianClass b))) :
    f = g := by
  apply MonoidHom.eq_of_eqOn_dense (markedRegularFundamentalGroup_generators_closure P h₁ h₂)
  rintro γ (⟨v, rfl⟩ | ⟨b, rfl⟩)
  · exact hL v
  · exact hM b

private theorem PeriodFamily.Boundary.compatibleLift_projection (b : Bool) (t : unitInterval) :
    SpecialPeriods.triangleRegularProject (PeriodFamily.Meridians.compatibleMeridianLift b t) =
      PeriodFamily.Meridians.compatibleRegularMeridian b t := by
  apply SpecialPeriods.Triangle.triangleRegularPlaneHomeomorph.injective
  exact
    (PeriodFamily.Meridians.compatibleMeridianLift_coordinate b t).trans
      (PeriodFamily.Meridians.compatibleRegularMeridian_coordinate b t).symm

private def PeriodFamily.Boundary.clockwiseLiftEndpoint (b : Bool) : SpecialPeriods.TriangleGroup :=
  if PeriodFamily.Meridians.normalizationReversesMeridians then
    (PeriodFamily.Meridians.compatibleMeridianGenerator b)⁻¹
  else PeriodFamily.Meridians.compatibleMeridianGenerator b

private def PeriodFamily.Boundary.clockwiseFinalLift (b : Bool) :
    C(unitInterval, SpecialPeriods.TriangleRegularPoint) :=
  if PeriodFamily.Meridians.normalizationReversesMeridians then
    (PeriodFamily.Meridians.compatibleMeridianLift b).toContinuousMap
  else
    ((PeriodFamily.Meridians.compatibleMeridianLift b).symm.map
        (ContinuousConstSMul.continuous_const_smul
          (PeriodFamily.Meridians.compatibleMeridianGenerator b))).toContinuousMap

@[simp]
private theorem PeriodFamily.Boundary.clockwiseFinalLift_zero (b : Bool) :
    clockwiseFinalLift b 0 = PeriodFamily.Meridians.normalizedRegularMeridianBasepoint := by
  by_cases h : PeriodFamily.Meridians.normalizationReversesMeridians = Bool.true
  · rw [clockwiseFinalLift, ite_eq_left h]
    exact (PeriodFamily.Meridians.compatibleMeridianLift b).source
  · rw [clockwiseFinalLift, ite_eq_right h]
    exact
      (((PeriodFamily.Meridians.compatibleMeridianLift b).symm.map
              (ContinuousConstSMul.continuous_const_smul
                (PeriodFamily.Meridians.compatibleMeridianGenerator b))).source).trans
        (smul_inv_smul (PeriodFamily.Meridians.compatibleMeridianGenerator b)
          PeriodFamily.Meridians.normalizedRegularMeridianBasepoint)

private theorem PeriodFamily.Boundary.clockwiseFinalLift_one (b : Bool) :
    clockwiseFinalLift b 1 = clockwiseLiftEndpoint b • clockwiseFinalLift b 0 := by
  rw [clockwiseFinalLift_zero]
  by_cases h : PeriodFamily.Meridians.normalizationReversesMeridians = Bool.true
  · rw [clockwiseFinalLift, clockwiseLiftEndpoint, ite_eq_left h, ite_eq_left h]
    exact (PeriodFamily.Meridians.compatibleMeridianLift b).target
  · rw [clockwiseFinalLift, clockwiseLiftEndpoint, ite_eq_right h, ite_eq_right h]
    exact
      ((PeriodFamily.Meridians.compatibleMeridianLift b).symm.map
          (ContinuousConstSMul.continuous_const_smul
            (PeriodFamily.Meridians.compatibleMeridianGenerator b))).target

end Mathoverflow1973

end
