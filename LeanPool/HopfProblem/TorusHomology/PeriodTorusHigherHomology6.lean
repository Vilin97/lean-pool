/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.PeriodDomain
public import LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.PeriodFamily.PeriodDomain
import all LeanPool.HopfProblem.Recognition.Smale4

/-!
# Hopf problem: torus homology · period torus higher homology 6

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

private def PeriodTorusHigherHomologyExterior.squareA₁ : Matrix (Fin 6) (Fin 6) ℤ :=
  LocalSystemMatrices.exteriorSquare A₁

private def PeriodTorusHigherHomologyExterior.squareA₂ : Matrix (Fin 6) (Fin 6) ℤ :=
  LocalSystemMatrices.exteriorSquare A₂

private def PeriodTorusHigherHomologyExterior.squareM₀ : Matrix (Fin 6) (Fin 6) ℤ :=
  LocalSystemMatrices.exteriorSquare M₀

private def PeriodTorusHigherHomologyExterior.cubeA₁ : LatticeMatrix :=
  LocalSystemMatrices.exteriorCube A₁

private def PeriodTorusHigherHomologyExterior.cubeA₂ : LatticeMatrix :=
  LocalSystemMatrices.exteriorCube A₂

private def PeriodTorusHigherHomologyExterior.cubeM₀ : LatticeMatrix :=
  LocalSystemMatrices.exteriorCube M₀

private theorem PeriodTorusHigherHomologyExterior.squareA₁_eq :
    squareA₁ =
      !![0, 1, 0, 0, 0, 0;
        -1, -1, 0, 0, 0, 0;
        1, 0, 1, 0, 0, 0;
        -6, 0, 0, 1, 0, 0;
        6, 2, 6, -1, 0, 1;
        -8, -2, -6, 1, -1, -1] := by decide

private theorem PeriodTorusHigherHomologyExterior.squareA₂_eq :
    squareA₂ =
      !![0, -1, 0, 0, 0, 0;
        1, 0, 0, 0, 0, 0;
        0, 1, 1, 0, 0, 0;
        0, -6, 0, 1, 0, 0;
        0, 3, 0, 0, 0, -1;
        -3, -6, -6, 1, 1, 0] := by decide

private theorem PeriodTorusHigherHomologyExterior.squareM₀_eq :
    squareM₀ =
      !![1, 0, 0, 0, 0, 0;
        1, 1, 0, 0, 0, 0;
        0, 0, 1, 0, 0, 0;
        0, 0, 0, 1, 0, 0;
        1, 0, 0, 0, 1, 0;
        1, 1, 0, 0, 1, 1] := by decide

private theorem PeriodTorusHigherHomologyExterior.cubeA₁_eq :
    cubeA₁ = !![1, 0, 0, 0; -1, 0, 1, 0; 1, -1, -1, 0; -2, -6, 0, 1] := by decide

private theorem PeriodTorusHigherHomologyExterior.cubeA₂_eq :
    cubeA₂ = !![1, 0, 0, 0; 0, 0, -1, 0; 1, 1, 0, 0; 3, 0, -6, 1] := by decide

private theorem PeriodTorusHigherHomologyExterior.cubeM₀_eq :
    cubeM₀ = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 1, 1, 0; -1, 0, 0, 1] := by decide

/-- The product of `n` unit circles. -/
public
abbrev PeriodTorusHigherHomology.ProductTorus (n : ℕ) :=
  Fin n → AddCircle (1 : ℝ)

/-- The additive quotient map from real coordinates to the product torus. -/
public
def PeriodTorusHigherHomology.coordinateProjection (n : ℕ) : (Fin n → ℝ) →+ ProductTorus n
    where
  toFun x i := (x i : AddCircle (1 : ℝ))
  map_zero' := by ext i; rfl
  map_add' x y := by ext i; exact AddCircle.coe_add (1 : ℝ) (x i) (y i)

@[simp]
private theorem
    PeriodTorusHigherHomology.coordinateProjection_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    coordinateProjection n x i = (x i : AddCircle (1 : ℝ)) :=
  rfl

private theorem PeriodTorusHigherHomology.coordinateProjection_continuous (n : ℕ) :
    Continuous (coordinateProjection n) := by
  exact continuous_pi (fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i))

private theorem PeriodTorusHigherHomology.coordinateProjection_eq_zero_iff (n : ℕ) (x : Fin n → ℝ) :
    coordinateProjection n x = 0 ↔ ∃ v : Fin n → ℤ, x = fun i => (v i : ℝ) := by
  constructor
  · intro h
    have hi : ∀ i, ∃ k : ℤ, (k : ℝ) = x i := by
      intro i
      have hz := congrFun h i
      change (x i : AddCircle (1 : ℝ)) = 0 at hz
      simpa only [zsmul_eq_mul, mul_one] using (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
    choose v hv using hi
    exact ⟨v, funext fun i => (hv i).symm⟩
  · rintro ⟨v, rfl⟩
    ext i
    change ((v i : ℝ) : AddCircle (1 : ℝ)) = 0
    apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
    exact ⟨v i, by simp⟩

private theorem PeriodTorusHigherHomology.coordinateProjection_surjective (n : ℕ) :
    Function.Surjective (coordinateProjection n) := by
  intro t
  have h : ∀ i, ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = t i := by
    intro i
    exact QuotientAddGroup.mk_surjective (t i)
  choose x hx using h
  exact ⟨x, funext hx⟩

private def PeriodTorusHigherHomology.productTorusSuccHomeomorph (n : ℕ) :
    ProductTorus (n + 1) ≃ₜ AddCircle (1 : ℝ) × ProductTorus n
    where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cons x.1 x.2
  left_inv x := Fin.cons_self_tail x
  right_inv x := by simp
  continuous_toFun := (continuous_apply 0).prodMk (continuous_pi fun i => continuous_apply i.succ)
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst
    · exact (continuous_apply j).comp continuous_snd

@[simp]
private theorem PeriodTorusHigherHomology.productTorusSuccHomeomorph_apply (n : ℕ)
    (x : ProductTorus (n + 1)) : productTorusSuccHomeomorph n x = (x 0, fun i => x i.succ) :=
  rfl

private def PeriodTorusHigherHomology.productTorusZeroHomeomorph : ProductTorus 0 ≃ₜ PUnit
    where
  toFun _ := PUnit.unit
  invFun _ := Fin.elim0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  continuous_toFun := continuous_const
  continuous_invFun := continuous_const

private def PeriodTorusHigherHomology.coordinatePeriodLoop (n : ℕ) (v : Fin n → ℤ) :
    Path (0 : ProductTorus n) 0 :=
  ((Path.segment (0 : Fin n → ℝ) (fun i => (v i : ℝ))).map
        (coordinateProjection_continuous n)).cast
    (map_zero (coordinateProjection n)).symm
    ((coordinateProjection_eq_zero_iff n _).mpr ⟨v, rfl⟩).symm

@[simp]
private theorem PeriodTorusHigherHomology.coordinatePeriodLoop_apply (n : ℕ) (v : Fin n → ℤ)
    (t : unitInterval) (i : Fin n) :
    coordinatePeriodLoop n v t i = ((t : ℝ) * (v i : ℝ) : AddCircle (1 : ℝ)) := by
  simp only [coordinatePeriodLoop, Path.cast_coe, Path.map_coe, Function.comp_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module, smul_zero, zero_add,
    coordinateProjection_apply, Pi.smul_apply, smul_eq_mul]

private theorem PeriodTorusHigherHomology.standardLattice_le_coordinateProjection_ker :
    standardLattice ≤ LinearMap.ker (coordinateProjection 4).toIntLinearMap := by
  intro x hx
  obtain ⟨v, rfl⟩ := (Elliptic.standardLattice_mem_iff x).mp hx
  exact (coordinateProjection_eq_zero_iff 4 _).mpr ⟨v, rfl⟩

private def PeriodTorusHigherHomology.flatTorusCircleMap : RealTorus₄ →ₗ[ℤ] ProductTorus 4 :=
  standardLattice.liftQ (coordinateProjection 4).toIntLinearMap
    standardLattice_le_coordinateProjection_ker

private theorem
    PeriodTorusHigherHomology.flatTorusCircleMap_continuous : Continuous flatTorusCircleMap :=
  by
  apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
  exact coordinateProjection_continuous 4

private theorem PeriodTorusHigherHomology.flatTorusCircleMap_injective :
    Function.Injective flatTorusCircleMap := by
  intro a b hab
  obtain ⟨x, rfl⟩ := standardLattice.mkQ_surjective a
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective b
  have hz : coordinateProjection 4 (x - y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hab
  obtain ⟨v, hv⟩ := (coordinateProjection_eq_zero_iff 4 (x - y)).mp hz
  apply (Elliptic.flatTorus_mkQ_eq_iff x y).mpr
  exact ⟨v, hv⟩

private theorem PeriodTorusHigherHomology.flatTorusCircleMap_surjective :
    Function.Surjective flatTorusCircleMap := by
  intro t
  obtain ⟨x, hx⟩ := coordinateProjection_surjective 4 t
  exact ⟨standardLattice.mkQ x, hx⟩

private def PeriodTorusHigherHomology.flatTorusCircleHomeomorph : RealTorus₄ ≃ₜ ProductTorus 4 :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective flatTorusCircleMap
      ⟨flatTorusCircleMap_injective, flatTorusCircleMap_surjective⟩)
    flatTorusCircleMap_continuous flatTorusCircleMap_continuous.isClosedMap

private theorem PeriodTorusHigherHomology.flatTorusCircleHomeomorph_mkQ (x : RealPlane₄) :
    flatTorusCircleHomeomorph (standardLattice.mkQ x) = coordinateProjection 4 x :=
  rfl

private def PeriodTorusHigherHomology.periodTorusCircleHomeomorph (p : PeriodDomain) :
    p.Torus ≃ₜ ProductTorus 4 :=
  (Elliptic.flatTorusPeriodHomeomorph p).symm.trans flatTorusCircleHomeomorph

@[simp]
private theorem
    PeriodTorusHigherHomology.periodTorusCircleHomeomorph_flatProjection (p : PeriodDomain)
    (x : RealPlane₄) :
    periodTorusCircleHomeomorph p (Elliptic.flatProjection p x) = coordinateProjection 4 x := by
  rw [periodTorusCircleHomeomorph, Homeomorph.trans_apply,
    Elliptic.flatTorusPeriodHomeomorph_symm_flatProjection, flatTorusCircleHomeomorph_mkQ]

@[simp]
private theorem PeriodTorusHigherHomology.periodTorusCircleHomeomorph_zero (p : PeriodDomain) :
    periodTorusCircleHomeomorph p 0 = 0 := by
  have h := periodTorusCircleHomeomorph_flatProjection p 0
  simpa only [Elliptic.flatProjection, map_zero] using h

private theorem
    PeriodTorusHigherHomology.periodTorusCircleHomeomorph_periodLoop_apply (p : PeriodDomain)
    (v : Lattice) (t : unitInterval) :
    periodTorusCircleHomeomorph p (p.periodLoop v t) = coordinatePeriodLoop 4 v t := by
  rw [PeriodDomain.periodLoop_apply]
  have hv : (t : ℝ) • p.periodVector v = Elliptic.periodEquiv p ((t : ℝ) • Elliptic.realCast v) :=
    by rw [map_smul, Elliptic.periodEquiv_realCast, p.periodVector_eq_sum]
  rw [hv]
  change
    periodTorusCircleHomeomorph p (Elliptic.flatProjection p ((t : ℝ) • Elliptic.realCast v)) = _
  rw [periodTorusCircleHomeomorph_flatProjection]
  ext i
  rw [coordinatePeriodLoop_apply]
  rfl

private theorem PeriodTorusHigherHomology.periodTorusCircleHomeomorph_periodLoop (p : PeriodDomain)
    (v : Lattice) :
    (p.periodLoop v).map (periodTorusCircleHomeomorph p).continuous =
      (coordinatePeriodLoop 4 v).cast (periodTorusCircleHomeomorph_zero p)
        (periodTorusCircleHomeomorph_zero p) := by
  apply Path.ext
  funext t
  exact periodTorusCircleHomeomorph_periodLoop_apply p v t

private def PeriodTorusHigherHomology.CirclePaths.circleTranslation (a : ℝ) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle),
      (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  ⟨fun z => (a : (PeriodTorusHigherHomology.CircleTopology.Circle)) + z, by
    exact
      (continuous_const :
            Continuous
              (fun _ : (PeriodTorusHigherHomology.CircleTopology.Circle) =>
                (a : (PeriodTorusHigherHomology.CircleTopology.Circle)))).add
        continuous_id⟩

@[simp]
private theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_apply (a : ℝ)
    (z : (PeriodTorusHigherHomology.CircleTopology.Circle)) :
    circleTranslation a z = (a : (PeriodTorusHigherHomology.CircleTopology.Circle)) + z :=
  rfl

private def PeriodTorusHigherHomology.CirclePaths.circleTranslationHomotopy (a : ℝ) :
    (circleTranslation a).Homotopy
      (ContinuousMap.id (PeriodTorusHigherHomology.CircleTopology.Circle))
    where
  toFun
    p := ((((1 - (p.1 : ℝ)) * a : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) + p.2)
  continuous_toFun :=
    ((AddCircle.continuous_mk' (1 : ℝ)).comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            continuous_const)).add
      continuous_snd
  map_zero_left z := by simp
  map_one_left z := by simp

@[simp]
private theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_singularHomologyMap (a : ℝ)
    (n : ℕ) : SingularMayerVietoris.singularHomologyMap (circleTranslation a) n = LinearMap.id := by
  rw [PeriodTorusHigherHomology.homotopy_homologyMap (circleTranslationHomotopy a) n,
    PeriodTorusHigherHomology.singularHomologyMap_id]

private theorem PeriodTorusHigherHomology.CirclePaths.circleTranslation_inducedHomology (a : ℝ) :
    FirstHurewicz.inducedHomology (circleTranslation a) = LinearMap.id :=
  circleTranslation_singularHomologyMap a 1

private theorem
    PeriodTorusHigherHomology.CirclePaths.loopHomologyClass_map_circleTranslation (a : ℝ)
    {x : (PeriodTorusHigherHomology.CircleTopology.Circle)} (p : Path x x) :
    FirstHurewicz.loopHomologyClass (p.map (circleTranslation a).continuous) =
      FirstHurewicz.loopHomologyClass p := by
  rw [← FirstHurewicz.inducedHomology_loopHomologyClass (circleTranslation a) x p,
    circleTranslation_inducedHomology]
  rfl

private def PeriodTorusHigherHomology.CirclePaths.quarterIntersection :
    ↥(PeriodTorusHigherHomology.CircleTopology.arcU ∩
        PeriodTorusHigherHomology.CircleTopology.arcV) :=
  PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph.symm
    (Sum.inl ⟨(1 / 4 : ℝ), by norm_num⟩)

private def PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersection :
    ↥(PeriodTorusHigherHomology.CircleTopology.arcU ∩
        PeriodTorusHigherHomology.CircleTopology.arcV) :=
  PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph.symm
    (Sum.inr ⟨(3 / 4 : ℝ), by norm_num⟩)

private def PeriodTorusHigherHomology.CirclePaths.quarterPoint :
    (PeriodTorusHigherHomology.CircleTopology.Circle) :=
  quarterIntersection.val

private def PeriodTorusHigherHomology.CirclePaths.threeQuarterPoint :
    (PeriodTorusHigherHomology.CircleTopology.Circle) :=
  threeQuarterIntersection.val

@[simp]
private theorem PeriodTorusHigherHomology.CirclePaths.quarterPoint_coe :
    quarterPoint = ((1 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl

@[simp]
private theorem PeriodTorusHigherHomology.CirclePaths.quarterIntersection_component :
    PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph quarterIntersection =
      Sum.inl ⟨(1 / 4 : ℝ), by norm_num⟩ :=
  PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph.apply_symm_apply _

@[simp]
private theorem PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersection_component :
    PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph threeQuarterIntersection =
      Sum.inr ⟨(3 / 4 : ℝ), by norm_num⟩ :=
  PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph.apply_symm_apply _

private def PeriodTorusHigherHomology.CirclePaths.quarterU :
    PeriodTorusHigherHomology.CircleTopology.arcU :=
  ⟨quarterPoint, quarterIntersection.property.1⟩

private def PeriodTorusHigherHomology.CirclePaths.quarterV :
    PeriodTorusHigherHomology.CircleTopology.arcV :=
  ⟨quarterPoint, quarterIntersection.property.2⟩

private def PeriodTorusHigherHomology.CirclePaths.threeQuarterU :
    PeriodTorusHigherHomology.CircleTopology.arcU :=
  ⟨threeQuarterPoint, threeQuarterIntersection.property.1⟩

private def PeriodTorusHigherHomology.CirclePaths.threeQuarterV :
    PeriodTorusHigherHomology.CircleTopology.arcV :=
  ⟨threeQuarterPoint, threeQuarterIntersection.property.2⟩

private def PeriodTorusHigherHomology.CirclePaths.uPath : Path quarterU threeQuarterU
    where
  toFun
    t :=
    PeriodTorusHigherHomology.CircleTopology.arcUHomeomorph.symm
      ⟨(1 / 4 : ℝ) + (t : ℝ) / 2, by
        have ht := t.property
        constructor <;> linarith [ht.1, ht.2]⟩
  continuous_toFun :=
    PeriodTorusHigherHomology.CircleTopology.arcUHomeomorph.symm.continuous.comp
      ((continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk
        (fun t => by
          change (1 / 4 : ℝ) + (t : ℝ) / 2 ∈ Set.Ioo (0 : ℝ) 1
          constructor <;> linarith [t.property.1, t.property.2]))
  source' := by
    apply Subtype.ext
    change
      (((1 / 4 : ℝ) + (0 : unitInterval) / 2 : ℝ) :
          (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        ((1 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
    norm_num
  target' := by
    apply Subtype.ext
    change
      (((1 / 4 : ℝ) + (1 : unitInterval) / 2 : ℝ) :
          (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        ((3 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
    norm_num

private def PeriodTorusHigherHomology.CirclePaths.vPath : Path threeQuarterV quarterV
    where
  toFun
    t :=
    PeriodTorusHigherHomology.CircleTopology.arcVHomeomorph.symm
      ⟨(3 / 4 : ℝ) + (t : ℝ) / 2, by
        have ht := t.property
        constructor <;> linarith [ht.1, ht.2]⟩
  continuous_toFun :=
    PeriodTorusHigherHomology.CircleTopology.arcVHomeomorph.symm.continuous.comp
      ((continuous_const.add (continuous_subtype_val.div_const 2)).subtype_mk
        (fun t => by
          change (3 / 4 : ℝ) + (t : ℝ) / 2 ∈ Set.Ioo (1 / 2 : ℝ) (3 / 2)
          constructor <;> linarith [t.property.1, t.property.2]))
  source' := by
    apply Subtype.ext
    change
      (((3 / 4 : ℝ) + (0 : unitInterval) / 2 : ℝ) :
          (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        ((3 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
    norm_num
  target' := by
    apply Subtype.ext
    change
      (((3 / 4 : ℝ) + (1 : unitInterval) / 2 : ℝ) :
          (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        ((1 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
    convert AddCircle.coe_add_period (1 : ℝ) (1 / 4 : ℝ) using 1
    norm_num

private def
    PeriodTorusHigherHomology.CirclePaths.uCirclePath : Path quarterPoint threeQuarterPoint :=
  uPath.map continuous_subtype_val

private def
    PeriodTorusHigherHomology.CirclePaths.vCirclePath : Path threeQuarterPoint quarterPoint :=
  vPath.map continuous_subtype_val

@[simp]
private theorem PeriodTorusHigherHomology.CirclePaths.uCirclePath_apply (t : unitInterval) :
    uCirclePath t =
      (((1 / 4 : ℝ) + (t : ℝ) / 2 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl

@[simp]
private theorem PeriodTorusHigherHomology.CirclePaths.vCirclePath_apply (t : unitInterval) :
    vCirclePath t =
      (((3 / 4 : ℝ) + (t : ℝ) / 2 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl

private def PeriodTorusHigherHomology.CirclePaths.quarterLoop : Path quarterPoint quarterPoint
    where
  toFun t := (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  continuous_toFun :=
    (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_const.add continuous_subtype_val)
  source' := by
    change
      (((1 / 4 : ℝ) + (0 : unitInterval) : ℝ) :
          (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        _;
    simp
  target' := AddCircle.coe_add_period (1 : ℝ) (1 / 4 : ℝ)

@[simp]
private theorem PeriodTorusHigherHomology.CirclePaths.quarterLoop_apply (t : unitInterval) :
    quarterLoop t =
      (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl

private theorem PeriodTorusHigherHomology.CirclePaths.uCirclePath_trans_vCirclePath :
    uCirclePath.trans vCirclePath = quarterLoop := by
  apply Path.ext
  funext t
  rw [Path.trans_apply]
  split_ifs <;> simp only [uCirclePath_apply, vCirclePath_apply, quarterLoop_apply]
  · congr 1
    ring
  · congr 1
    ring

/-- The positively oriented standard loop around the unit circle. -/
public
def PeriodTorusHigherHomology.CirclePaths.positiveLoop :
    Path (0 : (PeriodTorusHigherHomology.CircleTopology.Circle)) 0
    where
  toFun t := ((t : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_subtype_val
  source' := AddCircle.coe_zero (1 : ℝ)
  target' := AddCircle.coe_period (1 : ℝ)

@[simp]
private theorem PeriodTorusHigherHomology.CirclePaths.positiveLoop_apply (t : unitInterval) :
    positiveLoop t = ((t : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) :=
  rfl

private theorem PeriodTorusHigherHomology.CirclePaths.quarterTranslation_zero :
    circleTranslation (1 / 4) (0 : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      quarterPoint := by simp only [circleTranslation_apply, add_zero, quarterPoint_coe]

private theorem PeriodTorusHigherHomology.CirclePaths.quarterLoop_eq_translation :
    quarterLoop =
      (positiveLoop.map (circleTranslation (1 / 4)).continuous).cast quarterTranslation_zero.symm
        quarterTranslation_zero.symm := by
  apply Path.ext
  funext t
  change
    (((1 / 4 : ℝ) + (t : ℝ) : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      ((1 / 4 : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) +
        ((t : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle))
  exact AddCircle.coe_add (1 : ℝ) (1 / 4 : ℝ) (t : ℝ)

private theorem PeriodTorusHigherHomology.CirclePaths.quarterLoop_homologyClass :
    FirstHurewicz.loopHomologyClass quarterLoop = FirstHurewicz.loopHomologyClass positiveLoop := by
  have hc :
    FirstHurewicz.loopHomologyClass quarterLoop =
      FirstHurewicz.loopHomologyClass (positiveLoop.map (circleTranslation (1 / 4)).continuous) :=
    by
    apply
      FirstHurewicz.homologyToChainClass_injective
        (PeriodTorusHigherHomology.CircleTopology.Circle)
    rw [FirstHurewicz.homologyToChainClass_loopHomologyClass,
      FirstHurewicz.homologyToChainClass_loopHomologyClass, quarterLoop_eq_translation,
      FirstHurewicz.pathClass_cast]
  exact hc.trans (loopHomologyClass_map_circleTranslation (1 / 4) positiveLoop)

private theorem PeriodTorusHigherHomology.CirclePaths.boundaryOne_arcSum :
    FirstHurewicz.boundaryOne (PeriodTorusHigherHomology.CircleTopology.Circle)
        (FirstHurewicz.pathChain uCirclePath + FirstHurewicz.pathChain vCirclePath) =
      0 := by
  rw [map_add, FirstHurewicz.boundaryOne_pathChain, FirstHurewicz.boundaryOne_pathChain]
  abel

private def PeriodTorusHigherHomology.CirclePaths.arcSumCycle :
    FirstHurewicz.Cycles1 (PeriodTorusHigherHomology.CircleTopology.Circle) :=
  FirstHurewicz.mkCycle1 (PeriodTorusHigherHomology.CircleTopology.Circle)
    (FirstHurewicz.pathChain uCirclePath + FirstHurewicz.pathChain vCirclePath) boundaryOne_arcSum

private theorem PeriodTorusHigherHomology.CirclePaths.arcSumCycle_class :
    FirstHurewicz.cycleClass (PeriodTorusHigherHomology.CircleTopology.Circle) arcSumCycle =
      FirstHurewicz.loopHomologyClass quarterLoop := by
  apply
    FirstHurewicz.homologyToChainClass_injective (PeriodTorusHigherHomology.CircleTopology.Circle)
  rw [FirstHurewicz.homologyToChainClass_cycleClass,
    FirstHurewicz.homologyToChainClass_loopHomologyClass]
  change
    FirstHurewicz.chainClass (PeriodTorusHigherHomology.CircleTopology.Circle)
        (FirstHurewicz.pathChain uCirclePath + FirstHurewicz.pathChain vCirclePath) =
      _
  rw [map_add, ← uCirclePath_trans_vCirclePath, FirstHurewicz.pathClass_trans]
  rfl

private theorem PeriodTorusHigherHomology.CirclePaths.arcSumCycle_positiveLoop_class :
    FirstHurewicz.cycleClass (PeriodTorusHigherHomology.CircleTopology.Circle) arcSumCycle =
      FirstHurewicz.loopHomologyClass positiveLoop :=
  arcSumCycle_class.trans quarterLoop_homologyClass

private def PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection (X : Type*)
    [TopologicalSpace X] :
    C(X,
      ↥(PeriodTorusHigherHomology.CircleTopology.productU X ∩
          PeriodTorusHigherHomology.CircleTopology.productV X)) :=
  ⟨fun x => ⟨(quarterPoint, x), quarterIntersection.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

private def PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection (X : Type*)
    [TopologicalSpace X] :
    C(X,
      ↥(PeriodTorusHigherHomology.CircleTopology.productU X ∩
          PeriodTorusHigherHomology.CircleTopology.productV X)) :=
  ⟨fun x => ⟨(threeQuarterPoint, x), threeQuarterIntersection.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩

@[simp]
private theorem
    PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection_component (X : Type*)
    [TopologicalSpace X] (x : X) :
    PeriodTorusHigherHomology.CircleTopology.productIntersectionHomotopyEquiv X
        (quarterIntersectionSection X x) =
      Sum.inl x := by
  change
    Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
        (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
        (Homeomorph.sumProdDistrib
          (PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph quarterIntersection,
            x)) =
      _
  rw [quarterIntersection_component]
  rfl

private theorem PeriodTorusHigherHomology.CirclePaths.quarterIntersectionSection_comp (X : Type*)
    [TopologicalSpace X] :
    (PeriodTorusHigherHomology.CircleTopology.productIntersectionHomotopyEquiv X).toFun.comp
        (quarterIntersectionSection X) =
      ⟨Sum.inl, continuous_inl⟩ := by
  apply ContinuousMap.ext
  intro x
  exact quarterIntersectionSection_component X x

@[simp]
private theorem PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection_component
    (X : Type*) [TopologicalSpace X] (x : X) :
    PeriodTorusHigherHomology.CircleTopology.productIntersectionHomotopyEquiv X
        (threeQuarterIntersectionSection X x) =
      Sum.inr x := by
  change
    Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
        (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
        (Homeomorph.sumProdDistrib
          (PeriodTorusHigherHomology.CircleTopology.intersectionHomeomorph
              threeQuarterIntersection,
            x)) =
      _
  rw [threeQuarterIntersection_component]
  rfl

private theorem
    PeriodTorusHigherHomology.CirclePaths.threeQuarterIntersectionSection_comp (X : Type*)
    [TopologicalSpace X] :
    (PeriodTorusHigherHomology.CircleTopology.productIntersectionHomotopyEquiv X).toFun.comp
        (threeQuarterIntersectionSection X) =
      ⟨Sum.inr, continuous_inr⟩ := by
  apply ContinuousMap.ext
  intro x
  exact threeQuarterIntersectionSection_component X x

private def PeriodTorusHigherHomology.positiveCircleCross (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1) :=
  crossProductHomology (PeriodTorusHigherHomology.CircleTopology.Circle) X n
    (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop)

private theorem PeriodTorusHigherHomology.positiveCircleCross_arcSum_cycleClass (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    positiveCircleCross X n
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        (n + 1)
        (crossProductCycles (PeriodTorusHigherHomology.CircleTopology.Circle) X n
          CirclePaths.arcSumCycle b) := by
  have h :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex (PeriodTorusHigherHomology.CircleTopology.Circle)) 1
        CirclePaths.arcSumCycle =
      FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop :=
    CirclePaths.arcSumCycle_positiveLoop_class
  change
    crossProductHomology (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop)
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) =
      _
  rw [← h]
  exact
    crossProductHomology_cycleClass (PeriodTorusHigherHomology.CircleTopology.Circle) X n
      CirclePaths.arcSumCycle b

private theorem PeriodTorusHigherHomology.quarterIntersectionHomology_coordinates (X : Type)
    [TopologicalSpace X] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    productIntersectionHomologyEquiv X n
        (SingularMayerVietoris.singularHomologyMap (CirclePaths.quarterIntersectionSection X) n
          a) =
      (a, 0) := by
  rw [productIntersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    CirclePaths.quarterIntersectionSection_comp]
  exact sumHomologyEquiv_inl X X n a

private theorem PeriodTorusHigherHomology.threeQuarterIntersectionHomology_coordinates (X : Type)
    [TopologicalSpace X] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    productIntersectionHomologyEquiv X n
        (SingularMayerVietoris.singularHomologyMap (CirclePaths.threeQuarterIntersectionSection X)
          n a) =
      (0, a) := by
  rw [productIntersectionHomologyEquiv_apply, ← LinearMap.comp_apply, ← singularHomologyMap_comp,
    CirclePaths.threeQuarterIntersectionSection_comp]
  exact sumHomologyEquiv_inr X X n a

private def
    PeriodTorusHigherHomology.intersectionDifferenceCycle (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.Cycle
      (FirstHurewicz.singularComplex
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)))
      n :=
  SingularMayerVietoris.ModuleHomology.mapCycles
      (FirstHurewicz.singularChainMap (CirclePaths.threeQuarterIntersectionSection X)) n b -
    SingularMayerVietoris.ModuleHomology.mapCycles
      (FirstHurewicz.singularChainMap (CirclePaths.quarterIntersectionSection X)) n b

@[simp]
private theorem
    PeriodTorusHigherHomology.intersectionDifferenceCycle_val (X : Type) [TopologicalSpace X]
    (n : ℕ) (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    (intersectionDifferenceCycle X n b).1 =
      FirstHurewicz.inducedChain (CirclePaths.threeQuarterIntersectionSection X) n b.1 -
        FirstHurewicz.inducedChain (CirclePaths.quarterIntersectionSection X) n b.1 := by
  change
    (SingularMayerVietoris.ModuleHomology.mapCycles
            (FirstHurewicz.singularChainMap (CirclePaths.threeQuarterIntersectionSection X)) n
            b).1 -
        (SingularMayerVietoris.ModuleHomology.mapCycles
            (FirstHurewicz.singularChainMap (CirclePaths.quarterIntersectionSection X)) n b).1 =
      _
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val,
    SingularMayerVietoris.ModuleHomology.mapCycles_val]

private theorem PeriodTorusHigherHomology.intersectionDifferenceCycle_class_coordinates (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    productIntersectionHomologyEquiv X n
        (SingularMayerVietoris.ModuleHomology.cycleClass
          (FirstHurewicz.singularComplex
            (CircleTopology.productU X ∩ CircleTopology.productV X :
              Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)))
          n (intersectionDifferenceCycle X n b)) =
      (-SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b,
        SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) := by
  rw [intersectionDifferenceCycle, map_sub, map_sub, ←
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, ←
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass]
  change
    productIntersectionHomologyEquiv X n
          (SingularMayerVietoris.singularHomologyMap
            (CirclePaths.threeQuarterIntersectionSection X) n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b)) -
        productIntersectionHomologyEquiv X n
          (SingularMayerVietoris.singularHomologyMap (CirclePaths.quarterIntersectionSection X) n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b)) =
      _
  rw [threeQuarterIntersectionHomology_coordinates, quarterIntersectionHomology_coordinates]
  simp only [Prod.mk_sub_mk, zero_sub, sub_zero]

private theorem
    PeriodTorusHigherHomology.quarterIntersectionSection_toU (X : Type) [TopologicalSpace X] :
    (CircleTopology.productIntersectionToU X).comp (CirclePaths.quarterIntersectionSection X) =
      ((CircleTopology.productUHomeomorph X).symm :
            C(CircleTopology.arcU × X, CircleTopology.productU X)).comp
        ((ContinuousMap.const X CirclePaths.quarterU).prodMk (ContinuousMap.id X)) :=
  rfl

private theorem
    PeriodTorusHigherHomology.quarterIntersectionSection_toV (X : Type) [TopologicalSpace X] :
    (CircleTopology.productIntersectionToV X).comp (CirclePaths.quarterIntersectionSection X) =
      ((CircleTopology.productVHomeomorph X).symm :
            C(CircleTopology.arcV × X, CircleTopology.productV X)).comp
        ((ContinuousMap.const X CirclePaths.quarterV).prodMk (ContinuousMap.id X)) :=
  rfl

private theorem PeriodTorusHigherHomology.threeQuarterIntersectionSection_toU (X : Type)
    [TopologicalSpace X] :
    (CircleTopology.productIntersectionToU X).comp
        (CirclePaths.threeQuarterIntersectionSection X) =
      ((CircleTopology.productUHomeomorph X).symm :
            C(CircleTopology.arcU × X, CircleTopology.productU X)).comp
        ((ContinuousMap.const X CirclePaths.threeQuarterU).prodMk (ContinuousMap.id X)) :=
  rfl

private theorem PeriodTorusHigherHomology.threeQuarterIntersectionSection_toV (X : Type)
    [TopologicalSpace X] :
    (CircleTopology.productIntersectionToV X).comp
        (CirclePaths.threeQuarterIntersectionSection X) =
      ((CircleTopology.productVHomeomorph X).symm :
            C(CircleTopology.arcV × X, CircleTopology.productV X)).comp
        ((ContinuousMap.const X CirclePaths.threeQuarterV).prodMk (ContinuousMap.id X)) :=
  rfl

private theorem PeriodTorusHigherHomology.crossProductEdge_boundary_of_right_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : FirstHurewicz.Chains X 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n) :
    ((FirstHurewicz.singularComplex (X × Y)).d (n + 1) n).hom (crossProductEdge X Y n a b.1) =
      crossProductZeroLeft X Y n (((FirstHurewicz.singularComplex X).d 1 0).hom a) b.1 := by
  cases n with
  | zero => exact crossProductEdge_boundary_zero a b.1
  | succ
    n =>
    have hb : ((FirstHurewicz.singularComplex Y).d (n + 1) n).hom b.1 = 0 := by
      simpa only [Nat.succ_sub_one] using
        SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex Y)
          (n + 1) b
    simp only [crossProductEdge_boundary, hb, map_zero, sub_zero]

private theorem
    PeriodTorusHigherHomology.crossProductEdge_path_boundary {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) {x y : X} (p : Path x y)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n) :
    ((FirstHurewicz.singularComplex (X × Y)).d (n + 1) n).hom
        (crossProductEdge X Y n (FirstHurewicz.pathChain p) b.1) =
      FirstHurewicz.inducedChain (crossInsertLeft y) n b.1 -
        FirstHurewicz.inducedChain (crossInsertLeft x) n b.1 := by
  rw [crossProductEdge_boundary_of_right_cycle]
  change
    crossProductZeroLeft X Y n (FirstHurewicz.boundaryOne X (FirstHurewicz.pathChain p)) b.1 = _
  rw [FirstHurewicz.boundaryOne_pathChain, map_sub, LinearMap.sub_apply]
  simp only [FirstHurewicz.pointChain, crossProductZeroLeft_simplex_left]
  rfl

private theorem PeriodTorusHigherHomology.const_prodMk_id_eq_crossInsertLeft_mo1973_12793
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (x : X) :
    (ContinuousMap.const Y x).prodMk (ContinuousMap.id Y) = crossInsertLeft x := by
  apply ContinuousMap.ext
  intro y
  rfl

private def PeriodTorusHigherHomology.uCrossChain (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.Chains (CircleTopology.productU X) (n + 1) :=
  FirstHurewicz.inducedChain
    ((CircleTopology.productUHomeomorph X).symm :
      C(CircleTopology.arcU × X, CircleTopology.productU X))
    (n + 1)
    (crossProductEdge CircleTopology.arcU X n (FirstHurewicz.pathChain CirclePaths.uPath) b.1)

private def PeriodTorusHigherHomology.vCrossChain (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.Chains (CircleTopology.productV X) (n + 1) :=
  FirstHurewicz.inducedChain
    ((CircleTopology.productVHomeomorph X).symm :
      C(CircleTopology.arcV × X, CircleTopology.productV X))
    (n + 1)
    (crossProductEdge CircleTopology.arcV X n (FirstHurewicz.pathChain CirclePaths.vPath) b.1)

private theorem
    PeriodTorusHigherHomology.uCrossChain_boundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    ((FirstHurewicz.singularComplex (CircleTopology.productU X)).d (n + 1) n).hom
        (uCrossChain X n b) =
      FirstHurewicz.inducedChain (CircleTopology.productIntersectionToU X) n
        (intersectionDifferenceCycle X n b).1 := by
  rw [uCrossChain, ← FirstHurewicz.inducedChain_boundary, crossProductEdge_path_boundary,
    intersectionDifferenceCycle_val]
  simp only [map_sub]
  congr 1
  · have h :=
      congrArg (fun f => FirstHurewicz.inducedChain f n b.1)
        (threeQuarterIntersectionSection_toU X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, FirstHurewicz.inducedChain_comp,
      LinearMap.comp_apply] using h.symm
  · have h :=
      congrArg (fun f => FirstHurewicz.inducedChain f n b.1) (quarterIntersectionSection_toU X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, FirstHurewicz.inducedChain_comp,
      LinearMap.comp_apply] using h.symm

private theorem
    PeriodTorusHigherHomology.vCrossChain_boundary (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    ((FirstHurewicz.singularComplex (CircleTopology.productV X)).d (n + 1) n).hom
        (vCrossChain X n b) =
      -FirstHurewicz.inducedChain (CircleTopology.productIntersectionToV X) n
          (intersectionDifferenceCycle X n b).1 := by
  rw [vCrossChain, ← FirstHurewicz.inducedChain_boundary, crossProductEdge_path_boundary,
    intersectionDifferenceCycle_val]
  simp only [map_sub, neg_sub]
  congr 1
  · have h :=
      congrArg (fun f => FirstHurewicz.inducedChain f n b.1) (quarterIntersectionSection_toV X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, FirstHurewicz.inducedChain_comp,
      LinearMap.comp_apply] using h.symm
  · have h :=
      congrArg (fun f => FirstHurewicz.inducedChain f n b.1)
        (threeQuarterIntersectionSection_toV X)
    simpa only [const_prodMk_id_eq_crossInsertLeft_mo1973_12793, FirstHurewicz.inducedChain_comp,
      LinearMap.comp_apply] using h.symm

private theorem
    PeriodTorusHigherHomology.uCrossChain_inclusion (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.inducedChain (CircleTopology.productUInclusion X) (n + 1) (uCrossChain X n b) =
      crossProductEdge (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        (FirstHurewicz.pathChain CirclePaths.uCirclePath) b.1 := by
  have hi :
    (CircleTopology.productUInclusion X).comp
        ((CircleTopology.productUHomeomorph X).symm :
          C(CircleTopology.arcU × X, CircleTopology.productU X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ :
            C(CircleTopology.arcU, (PeriodTorusHigherHomology.CircleTopology.Circle))).prodMap
        (ContinuousMap.id X) :=
    rfl
  rw [uCrossChain, ← LinearMap.comp_apply, ← FirstHurewicz.inducedChain_comp, hi,
    crossProductEdge_natural, FirstHurewicz.inducedChain_id, LinearMap.id_apply,
    FirstHurewicz.inducedChain_pathChain]
  rfl

private theorem
    PeriodTorusHigherHomology.vCrossChain_inclusion (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.inducedChain (CircleTopology.productVInclusion X) (n + 1) (vCrossChain X n b) =
      crossProductEdge (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        (FirstHurewicz.pathChain CirclePaths.vCirclePath) b.1 := by
  have hi :
    (CircleTopology.productVInclusion X).comp
        ((CircleTopology.productVHomeomorph X).symm :
          C(CircleTopology.arcV × X, CircleTopology.productV X)) =
      (⟨Subtype.val, continuous_subtype_val⟩ :
            C(CircleTopology.arcV, (PeriodTorusHigherHomology.CircleTopology.Circle))).prodMap
        (ContinuousMap.id X) :=
    rfl
  rw [vCrossChain, ← LinearMap.comp_apply, ← FirstHurewicz.inducedChain_comp, hi,
    crossProductEdge_natural, FirstHurewicz.inducedChain_id, LinearMap.id_apply,
    FirstHurewicz.inducedChain_pathChain]
  rfl

private theorem
    PeriodTorusHigherHomology.arcCrossChains_inclusion_sum (X : Type) [TopologicalSpace X]
    (n : ℕ) (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    FirstHurewicz.inducedChain (CircleTopology.productUInclusion X) (n + 1) (uCrossChain X n b) +
        FirstHurewicz.inducedChain (CircleTopology.productVInclusion X) (n + 1)
          (vCrossChain X n b) =
      crossProductEdge (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        (FirstHurewicz.pathChain CirclePaths.uCirclePath +
          FirstHurewicz.pathChain CirclePaths.vCirclePath)
        b.1 := by rw [uCrossChain_inclusion, vCrossChain_inclusion, map_add, LinearMap.add_apply]

private def PeriodTorusHigherHomology.biprodElement_mo1973_12801
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ) (a : K.X n) (b : L.X n) : (K ⊞ L).X n :=
  ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom a +
    ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom b

private theorem PeriodTorusHigherHomology.biprod_lift_f_apply_mo1973_12802
    {J K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : J ⟶ K) (g : J ⟶ L) (n : ℕ) (z : J.X n) :
    ((CategoryTheory.Limits.biprod.lift f g).f n).hom z =
      ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom ((f.f n).hom z) +
        ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom ((g.f n).hom z) := by
  have htotal :=
    congrArg (fun h => h.hom (((CategoryTheory.Limits.biprod.lift f g).f n).hom z))
      (HomologicalComplex.biprod_total_f K L n)
  have hfst := congrArg (fun h => h.hom z) (HomologicalComplex.biprod_lift_fst_f f g n)
  have hsnd := congrArg (fun h => h.hom z) (HomologicalComplex.biprod_lift_snd_f f g n)
  change
    ((CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K).f n).hom
        (((CategoryTheory.Limits.biprod.lift f g).f n).hom z) =
      (f.f n).hom z at hfst
  change
    ((CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L).f n).hom
        (((CategoryTheory.Limits.biprod.lift f g).f n).hom z) =
      (g.f n).hom z at hsnd
  change
    ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom
          (((CategoryTheory.Limits.biprod.fst : K ⊞ L ⟶ K).f n).hom
            (((CategoryTheory.Limits.biprod.lift f g).f n).hom z)) +
        ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom
          (((CategoryTheory.Limits.biprod.snd : K ⊞ L ⟶ L).f n).hom
            (((CategoryTheory.Limits.biprod.lift f g).f n).hom z)) =
      ((CategoryTheory.Limits.biprod.lift f g).f n).hom z at htotal
  rw [hfst, hsnd] at htotal
  exact htotal.symm

private theorem PeriodTorusHigherHomology.biprodElement_desc_mo1973_12803
    {K L T : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : K ⟶ T) (g : L ⟶ T) (n : ℕ) (a : K.X n)
    (b : L.X n) :
    ((CategoryTheory.Limits.biprod.desc f g).f n).hom (biprodElement_mo1973_12801 K L n a b) =
      (f.f n).hom a + (g.f n).hom b := by
  change
    ((CategoryTheory.Limits.biprod.desc f g).f n).hom
        (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f n).hom a +
          ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f n).hom b) =
      _
  rw [map_add]
  congr 1
  · exact congrArg (fun h => h.hom a) (HomologicalComplex.biprod_inl_desc_f f g n)
  · exact congrArg (fun h => h.hom b) (HomologicalComplex.biprod_inr_desc_f f g n)

private theorem PeriodTorusHigherHomology.biprodElement_boundary_mo1973_12804
    (K L : ChainComplex (ModuleCat.{0} ℤ) ℕ) (i j : ℕ) (a : K.X i) (b : L.X i) :
    ((K ⊞ L).d i j).hom (biprodElement_mo1973_12801 K L i a b) =
      biprodElement_mo1973_12801 K L j ((K.d i j).hom a) ((L.d i j).hom b) := by
  have hK := congrArg (fun f => f.hom a) ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).comm i j)
  have hL := congrArg (fun f => f.hom b) ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).comm i j)
  change
    ((K ⊞ L).d i j).hom (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f i).hom a) =
      ((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f j).hom ((K.d i j).hom a) at hK
  change
    ((K ⊞ L).d i j).hom (((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f i).hom b) =
      ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f j).hom ((L.d i j).hom b) at hL
  change
    ((K ⊞ L).d i j).hom
        (((CategoryTheory.Limits.biprod.inl : K ⟶ K ⊞ L).f i).hom a +
          ((CategoryTheory.Limits.biprod.inr : L ⟶ K ⊞ L).f i).hom b) =
      _
  rw [map_add, hK, hL]
  rfl

private theorem PeriodTorusHigherHomology.biprod_lift_eq_boundary_mo1973_12805
    {J K L : ChainComplex (ModuleCat.{0} ℤ) ℕ} (f : J ⟶ K) (g : J ⟶ L) (i j : ℕ) (a : K.X i)
    (b : L.X i) (z : J.X j) (ha : (K.d i j).hom a = (f.f j).hom z)
    (hb : (L.d i j).hom b = (g.f j).hom z) :
    ((CategoryTheory.Limits.biprod.lift f g).f j).hom z =
      ((K ⊞ L).d i j).hom (biprodElement_mo1973_12801 K L i a b) := by
  have hlift := biprod_lift_f_apply_mo1973_12802 f g j z
  have hboundary := biprodElement_boundary_mo1973_12804 K L i j a b
  have hab := congrArg₂ (biprodElement_mo1973_12801 K L j) ha hb
  exact hlift.trans (hab.symm.trans hboundary.symm)

private def
    PeriodTorusHigherHomology.twoChainMiddle {X : Type} [TopologicalSpace X] (U V : Set X) (n : ℕ)
    (a : FirstHurewicz.Chains U (n + 1)) (b : FirstHurewicz.Chains V (n + 1)) :
    (SingularMayerVietoris.middleComplex U V).X (n + 1) :=
  biprodElement_mo1973_12801 (FirstHurewicz.singularComplex U) (FirstHurewicz.singularComplex V)
    (n + 1) a b

private theorem PeriodTorusHigherHomology.twoChainMiddle_rightMap {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : FirstHurewicz.Chains U (n + 1))
    (b : FirstHurewicz.Chains V (n + 1)) :
    ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b) =
      ((SingularMayerVietoris.toSmallLeft U V).f (n + 1)).hom a +
        ((SingularMayerVietoris.toSmallRight U V).f (n + 1)).hom b :=
  biprodElement_desc_mo1973_12803 (SingularMayerVietoris.toSmallLeft U V)
    (SingularMayerVietoris.toSmallRight U V) (n + 1) a b

private theorem PeriodTorusHigherHomology.twoChainMiddle_boundary {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : FirstHurewicz.Chains U (n + 1))
    (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    ((SingularMayerVietoris.leftMap U V).f n).hom z.1 =
      ((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom (twoChainMiddle U V n a b) :=
  biprod_lift_eq_boundary_mo1973_12805 (SingularMayerVietoris.intersectionToLeft U V)
    (-(SingularMayerVietoris.intersectionToRight U V)) (n + 1) n a b z.1 ha hb

private theorem
    PeriodTorusHigherHomology.twoChainSmallCycle_condition {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : FirstHurewicz.Chains U (n + 1))
    (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    ((SingularMayerVietoris.smallComplex U V).d (n + 1) n).hom
        (((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b)) =
      0 := by
  have hcomm :=
    congrArg (fun f => f.hom (twoChainMiddle U V n a b))
      ((SingularMayerVietoris.rightMap U V).comm (n + 1) n)
  have hzero := congrArg (fun f => (f.f n).hom z.1) (SingularMayerVietoris.leftMap_rightMap U V)
  calc
    _ =
        ((SingularMayerVietoris.rightMap U V).f n).hom
          (((SingularMayerVietoris.middleComplex U V).d (n + 1) n).hom
            (twoChainMiddle U V n a b)) :=
      hcomm
    _ =
        ((SingularMayerVietoris.rightMap U V).f n).hom
          (((SingularMayerVietoris.leftMap U V).f n).hom z.1) :=
      (congrArg ((SingularMayerVietoris.rightMap U V).f n).hom
        (twoChainMiddle_boundary U V n a b z ha hb).symm)
    _ = 0 := hzero

private def
    PeriodTorusHigherHomology.twoChainSmallCycle {X : Type} [TopologicalSpace X] (U V : Set X)
    (n : ℕ) (a : FirstHurewicz.Chains U (n + 1)) (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    SingularMayerVietoris.ModuleHomology.Cycle (SingularMayerVietoris.smallComplex U V) (n + 1) :=
  SingularMayerVietoris.ModuleHomology.mkCycle (SingularMayerVietoris.smallComplex U V) (n + 1)
    (((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b))
    (by
      rw [Nat.add_sub_cancel]
      exact twoChainSmallCycle_condition U V n a b z ha hb)

@[simp]
private theorem PeriodTorusHigherHomology.twoChainSmallCycle_val {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : FirstHurewicz.Chains U (n + 1))
    (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    (twoChainSmallCycle U V n a b z ha hb).1 =
      ((SingularMayerVietoris.rightMap U V).f (n + 1)).hom (twoChainMiddle U V n a b) :=
  rfl

private theorem
    PeriodTorusHigherHomology.twoChainSmallCycle_ambient_val {X : Type} [TopologicalSpace X]
    (U V : Set X) (n : ℕ) (a : FirstHurewicz.Chains U (n + 1))
    (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    (SingularMayerVietoris.ModuleHomology.mapCycles (SingularMayerVietoris.smallInclusion U V)
          (n + 1) (twoChainSmallCycle U V n a b z ha hb)).1 =
      FirstHurewicz.inducedChain (SingularMayerVietoris.subtypeInclusion U) (n + 1) a +
        FirstHurewicz.inducedChain (SingularMayerVietoris.subtypeInclusion V) (n + 1) b := by
  rw [SingularMayerVietoris.ModuleHomology.mapCycles_val, twoChainSmallCycle_val,
    twoChainMiddle_rightMap, map_add]
  have hU :=
    congrArg (fun f => (f.f (n + 1)).hom a) (SingularMayerVietoris.toSmallLeft_inclusion U V)
  have hV :=
    congrArg (fun f => (f.f (n + 1)).hom b) (SingularMayerVietoris.toSmallRight_inclusion U V)
  exact congrArg₂ (· + ·) hU hV

private theorem
    PeriodTorusHigherHomology.connectingHomomorphism_twoChain {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (a : FirstHurewicz.Chains U (n + 1)) (b : FirstHurewicz.Chains V (n + 1))
    (z :
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (U ∩ V : Set X))
        n)
    (ha :
      ((FirstHurewicz.singularComplex U).d (n + 1) n).hom a =
        FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) n
          z.1)
    (hb :
      ((FirstHurewicz.singularComplex V).d (n + 1) n).hom b =
        -FirstHurewicz.inducedChain (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V))
            n z.1) :
    SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) (n + 1)
          (SingularMayerVietoris.ModuleHomology.mapCycles
            (SingularMayerVietoris.smallInclusion U V) (n + 1)
            (twoChainSmallCycle U V n a b z ha hb))) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex (U ∩ V : Set X)) n z :=
  connectingHomomorphism_cycleClass U V hU hV hcover n (twoChainSmallCycle U V n a b z ha hb)
    (twoChainMiddle U V n a b) rfl z (twoChainMiddle_boundary U V n a b z ha hb)

private def
    PeriodTorusHigherHomology.positiveCircleSmallCycle (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.Cycle
      (SingularMayerVietoris.smallComplex (CircleTopology.productU X) (CircleTopology.productV X))
      (n + 1) :=
  twoChainSmallCycle (CircleTopology.productU X) (CircleTopology.productV X) n (uCrossChain X n b)
    (vCrossChain X n b) (intersectionDifferenceCycle X n b) (uCrossChain_boundary X n b)
    (vCrossChain_boundary X n b)

private theorem PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_val (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (CircleTopology.productU X)
            (CircleTopology.productV X))
          (n + 1) (positiveCircleSmallCycle X n b)).1 =
      crossProductEdge (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        (FirstHurewicz.pathChain CirclePaths.uCirclePath +
          FirstHurewicz.pathChain CirclePaths.vCirclePath)
        b.1 :=
  (twoChainSmallCycle_ambient_val (CircleTopology.productU X) (CircleTopology.productV X) n
        (uCrossChain X n b) (vCrossChain X n b) (intersectionDifferenceCycle X n b)
        (uCrossChain_boundary X n b) (vCrossChain_boundary X n b)).trans
    (arcCrossChains_inclusion_sum X n b)

private theorem PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_eq (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.mapCycles
        (SingularMayerVietoris.smallInclusion (CircleTopology.productU X)
          (CircleTopology.productV X))
        (n + 1) (positiveCircleSmallCycle X n b) =
      crossProductCycles (PeriodTorusHigherHomology.CircleTopology.Circle) X n
        CirclePaths.arcSumCycle b := by
  apply Subtype.ext
  exact positiveCircleSmallCycle_ambient_val X n b

private theorem PeriodTorusHigherHomology.positiveCircleSmallCycle_ambient_class (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        (n + 1)
        (SingularMayerVietoris.ModuleHomology.mapCycles
          (SingularMayerVietoris.smallInclusion (CircleTopology.productU X)
            (CircleTopology.productV X))
          (n + 1) (positiveCircleSmallCycle X n b)) =
      positiveCircleCross X n
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) :=
  by
  rw [positiveCircleSmallCycle_ambient_eq]
  exact (positiveCircleCross_arcSum_cycleClass X n b).symm

private theorem PeriodTorusHigherHomology.circleConnecting_positiveCircleCross_cycleClass (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    circleMayerVietorisConnecting X n
        (positiveCircleCross X n
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
            b)) =
      SingularMayerVietoris.ModuleHomology.cycleClass
        (FirstHurewicz.singularComplex
          (CircleTopology.productU X ∩ CircleTopology.productV X :
            Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X)))
        n (intersectionDifferenceCycle X n b) := by
  rw [← positiveCircleSmallCycle_ambient_class]
  exact
    connectingHomomorphism_twoChain (CircleTopology.productU X) (CircleTopology.productV X)
      (CircleTopology.productU_open X) (CircleTopology.productV_open X)
      (CircleTopology.product_cover X) n (uCrossChain X n b) (vCrossChain X n b)
      (intersectionDifferenceCycle X n b) (uCrossChain_boundary X n b)
      (vCrossChain_boundary X n b)

private theorem PeriodTorusHigherHomology.circleBoundaryCoordinates_positiveCircleCross_cycleClass
    (X : Type) [TopologicalSpace X] (n : ℕ)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) n) :
    circleBoundaryCoordinates X n
        (positiveCircleCross X n
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
            b)) =
      (-SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b,
        SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n b) := by
  change
    productIntersectionHomologyEquiv X n
        (circleMayerVietorisConnecting X n
          (positiveCircleCross X n
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) n
              b))) =
      _
  rw [circleConnecting_positiveCircleCross_cycleClass]
  exact intersectionDifferenceCycle_class_coordinates X n b

private theorem PeriodTorusHigherHomology.circleBoundaryCoordinates_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleBoundaryCoordinates X n (positiveCircleCross X n b) = (-b, b) := by
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) n
      b
  exact circleBoundaryCoordinates_positiveCircleCross_cycleClass X n c

private theorem PeriodTorusHigherHomology.circleBoundary_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleBoundary X n (positiveCircleCross X n b) = b := by
  rw [circleBoundary_apply, circleBoundaryCoordinates_positiveCircleCross]
  exact neg_neg b

private def PeriodTorusHigherHomology.circleProductMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    C((PeriodTorusHigherHomology.CircleTopology.Circle) × X,
      (PeriodTorusHigherHomology.CircleTopology.Circle) × Y) :=
  ⟨fun z => (z.1, f z.2), continuous_fst.prodMk (f.continuous.comp continuous_snd)⟩

private def PeriodTorusHigherHomology.intersectionProductMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    C(↥(CircleTopology.productU X ∩ CircleTopology.productV X),
      ↥(CircleTopology.productU Y ∩ CircleTopology.productV Y)) :=
  ⟨fun z => ⟨circleProductMap f z.val, z.property⟩,
    ((circleProductMap f).continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem
    PeriodTorusHigherHomology.circleProductMap_projection {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    (CircleTopology.productProjection Y).comp (circleProductMap f) =
      f.comp (CircleTopology.productProjection X) :=
  rfl

private theorem PeriodTorusHigherHomology.intersectionProductMap_homotopyEquiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (CircleTopology.productIntersectionHomotopyEquiv Y).toFun.comp (intersectionProductMap f) =
      (CircleTopology.sumContinuousMap f f).comp
        (CircleTopology.productIntersectionHomotopyEquiv X).toFun := by
  apply ContinuousMap.ext
  intro z
  let c : ↥(CircleTopology.arcU ∩ CircleTopology.arcV) := ⟨z.val.1, z.property⟩
  change
    Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × Y => t.2)
        (fun t : Set.Ioo (1 / 2 : ℝ) 1 × Y => t.2)
        (Homeomorph.sumProdDistrib (CircleTopology.intersectionHomeomorph c, f z.val.2)) =
      Sum.map f f
        (Sum.map (fun t : Set.Ioo (0 : ℝ) (1 / 2) × X => t.2)
          (fun t : Set.Ioo (1 / 2 : ℝ) 1 × X => t.2)
          (Homeomorph.sumProdDistrib (CircleTopology.intersectionHomeomorph c, z.val.2)))
  cases h : CircleTopology.intersectionHomeomorph c <;> rfl

private theorem PeriodTorusHigherHomology.circleProjectionHomology_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    (circleProjectionHomology Y n).comp
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) n) =
      (SingularMayerVietoris.singularHomologyMap f n).comp (circleProjectionHomology X n) := by
  rw [← singularHomologyMap_comp, circleProductMap_projection, singularHomologyMap_comp]

private theorem
    PeriodTorusHigherHomology.sumHomologyEquiv_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {X' Y' : Type} [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X'))
    (g : C(Y, Y')) (n : ℕ) (a : SingularMayerVietoris.SingularHomology (X ⊕ Y) n) :
    sumHomologyEquiv X' Y' n
        (SingularMayerVietoris.singularHomologyMap (CircleTopology.sumContinuousMap f g) n a) =
      (SingularMayerVietoris.singularHomologyMap f n (sumHomologyEquiv X Y n a).1,
        SingularMayerVietoris.singularHomologyMap g n (sumHomologyEquiv X Y n a).2) := by
  have hsum :
    CircleTopology.sumContinuousMap f g =
      sumElimMap ((sumInlMap X' Y').comp f) ((sumInrMap X' Y').comp g) := by
    ext x
    cases x <;> rfl
  simp only [hsum, sumHomologyEquiv_sumElim, singularHomologyMap_comp, LinearMap.comp_apply,
    map_add, sumHomologyEquiv_inl, sumHomologyEquiv_inr, Prod.mk_add_mk, add_zero, zero_add]

private theorem PeriodTorusHigherHomology.productIntersectionHomologyEquiv_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        (CircleTopology.productU X ∩ CircleTopology.productV X :
          Set ((PeriodTorusHigherHomology.CircleTopology.Circle) × X))
        n) :
    productIntersectionHomologyEquiv Y n
        (SingularMayerVietoris.singularHomologyMap (intersectionProductMap f) n a) =
      (SingularMayerVietoris.singularHomologyMap f n (productIntersectionHomologyEquiv X n a).1,
        SingularMayerVietoris.singularHomologyMap f n
          (productIntersectionHomologyEquiv X n a).2) := by
  have h :=
    congrArg (fun g => SingularMayerVietoris.singularHomologyMap g n)
      (intersectionProductMap_homotopyEquiv f)
  rw [singularHomologyMap_comp, singularHomologyMap_comp] at h
  calc
    _ =
        sumHomologyEquiv Y Y n
          (SingularMayerVietoris.singularHomologyMap (CircleTopology.sumContinuousMap f f) n
            (SingularMayerVietoris.singularHomologyMap
              (CircleTopology.productIntersectionHomotopyEquiv X).toFun n a)) :=
      congrArg (sumHomologyEquiv Y Y n) (LinearMap.congr_fun h a)
    _ = _ := sumHomologyEquiv_naturality f f n _

private theorem PeriodTorusHigherHomology.circleProductMap_mapsToU {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    Set.MapsTo (circleProductMap f) (CircleTopology.productU X) (CircleTopology.productU Y) :=
  fun _ h => h

private theorem PeriodTorusHigherHomology.circleProductMap_mapsToV {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) :
    Set.MapsTo (circleProductMap f) (CircleTopology.productV X) (CircleTopology.productV Y) :=
  fun _ h => h

private theorem PeriodTorusHigherHomology.circleProductIntersectionRestriction_eq {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    SingularMayerVietoris.intersectionRestriction (circleProductMap f) (CircleTopology.productU X)
        (CircleTopology.productV X) (CircleTopology.productU Y) (CircleTopology.productV Y)
        (circleProductMap_mapsToU f) (circleProductMap_mapsToV f) =
      intersectionProductMap f :=
  rfl

private theorem PeriodTorusHigherHomology.circleMayerVietorisConnecting_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (intersectionProductMap f) n).comp
        (circleMayerVietorisConnecting X n) =
      (circleMayerVietorisConnecting Y n).comp
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)) := by
  have h :=
    SingularMayerVietoris.connectingHomomorphism_naturality (circleProductMap f)
      (CircleTopology.productU X) (CircleTopology.productV X) (CircleTopology.productU Y)
      (CircleTopology.productV Y) (circleProductMap_mapsToU f) (circleProductMap_mapsToV f)
      (CircleTopology.productU_open X) (CircleTopology.productV_open X)
      (CircleTopology.product_cover X) (CircleTopology.productU_open Y)
      (CircleTopology.productV_open Y) (CircleTopology.product_cover Y) n
  rw [circleProductIntersectionRestriction_eq] at h
  exact h

private theorem PeriodTorusHigherHomology.circleBoundaryCoordinates_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleBoundaryCoordinates Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) =
      (SingularMayerVietoris.singularHomologyMap f n (circleBoundaryCoordinates X n a).1,
        SingularMayerVietoris.singularHomologyMap f n (circleBoundaryCoordinates X n a).2) := by
  have h := LinearMap.congr_fun (circleMayerVietorisConnecting_naturality f n) a
  change
    SingularMayerVietoris.singularHomologyMap (intersectionProductMap f) n
        (circleMayerVietorisConnecting X n a) =
      circleMayerVietorisConnecting Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) at h
  change
    productIntersectionHomologyEquiv Y n
        (circleMayerVietorisConnecting Y n
          (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a)) =
      _
  rw [← h]
  exact productIntersectionHomologyEquiv_naturality f n (circleMayerVietorisConnecting X n a)

private theorem
    PeriodTorusHigherHomology.circleBoundary_naturality {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleBoundary Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap f n (circleBoundary X n a) := by
  change
    -(circleBoundaryCoordinates Y n
            (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a)).1 =
      SingularMayerVietoris.singularHomologyMap f n (-(circleBoundaryCoordinates X n a).1)
  rw [circleBoundaryCoordinates_naturality, map_neg]

private theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology
        ((PeriodTorusHigherHomology.CircleTopology.Circle) × X) (n + 1)) :
    circleProductHomologyEquiv Y n
        (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1) a) =
      (SingularMayerVietoris.singularHomologyMap f (n + 1) (circleProductHomologyEquiv X n a).1,
        SingularMayerVietoris.singularHomologyMap f n (circleProductHomologyEquiv X n a).2) := by
  apply Prod.ext
  · exact LinearMap.congr_fun (circleProjectionHomology_naturality f (n + 1)) a
  · exact circleBoundary_naturality f n a

private theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)
        ((circleProductHomologyEquiv X n).symm a) =
      (circleProductHomologyEquiv Y n).symm
        (SingularMayerVietoris.singularHomologyMap f (n + 1) a.1,
          SingularMayerVietoris.singularHomologyMap f n a.2) := by
  apply (circleProductHomologyEquiv Y n).injective
  rw [circleProductHomologyEquiv_naturality, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductCycles_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n) :
    SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap (f.prodMap g))
        (n + 1) (crossProductCycles X Y n a b) =
      crossProductCycles X' Y' n
        (SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap f) 1 a)
        (SingularMayerVietoris.ModuleHomology.mapCycles (FirstHurewicz.singularChainMap g) n b) :=
  by
  apply Subtype.ext
  simp only [SingularMayerVietoris.ModuleHomology.mapCycles_val, crossProductCycles_val]
  exact crossProductEdge_natural f g n a.1 b.1

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductHomology_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (a : (FirstHurewicz.singularComplex X).homology 1)
    (b : (FirstHurewicz.singularComplex Y).homology n) :
    (HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap (f.prodMap g)) (n + 1)).hom
        (crossProductHomology X Y n a b) =
      crossProductHomology X' Y' n
        ((HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap f) 1).hom a)
        ((HomologicalComplex.homologyMap (FirstHurewicz.singularChainMap g) n).hom b) := by
  obtain ⟨a, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) 1
      a
  obtain ⟨b, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex Y) n
      b
  rw [crossProductHomology_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass,
    SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass, crossProductHomology_cycleClass,
    crossProductCycles_natural]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductHomology_snd {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : SingularMayerVietoris.SingularHomology X 1)
    (b : SingularMayerVietoris.SingularHomology Y n) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.snd : C(X × Y, Y)) (n + 1)
        (crossProductHomology X Y n a b) =
      0 := by
  let : Subsingleton (SingularMayerVietoris.SingularHomology Unit 1) :=
    point_homology_subsingleton 1 (by decide)
  let f : C(X, Unit) := ContinuousMap.const X ()
  have hz : SingularMayerVietoris.singularHomologyMap f 1 a = 0 := Subsingleton.elim _ _
  have hn := crossProductHomology_natural f (ContinuousMap.id Y) n a b
  change
    SingularMayerVietoris.singularHomologyMap (f.prodMap (ContinuousMap.id Y)) (n + 1)
        (crossProductHomology X Y n a b) =
      crossProductHomology Unit Y n (SingularMayerVietoris.singularHomologyMap f 1 a)
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id Y) n b) at hn
  rw [hz, map_zero, LinearMap.zero_apply] at hn
  calc
    _ =
        SingularMayerVietoris.singularHomologyMap (ContinuousMap.snd : C(Unit × Y, Y)) (n + 1)
          (SingularMayerVietoris.singularHomologyMap (f.prodMap (ContinuousMap.id Y)) (n + 1)
            (crossProductHomology X Y n a b)) := by
      exact
        LinearMap.congr_fun
          (singularHomologyMap_comp (f.prodMap (ContinuousMap.id Y))
            (ContinuousMap.snd : C(Unit × Y, Y)) (n + 1))
          (crossProductHomology X Y n a b)
    _ = 0 := by rw [hn, map_zero]

@[simp]
private theorem PeriodTorusHigherHomology.circleProjection_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleProjectionHomology X (n + 1) (positiveCircleCross X n b) = 0 :=
  crossProductHomology_snd n (FirstHurewicz.loopHomologyClass CirclePaths.positiveLoop) b

private theorem PeriodTorusHigherHomology.circleProductHomologyEquiv_positiveCircleCross (X : Type)
    [TopologicalSpace X] (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    circleProductHomologyEquiv X n (positiveCircleCross X n b) = (0, b) := by
  apply Prod.ext
  · exact circleProjection_positiveCircleCross X n b
  · exact circleBoundary_positiveCircleCross X n b

private theorem
    PeriodTorusHigherHomology.positiveCircleCross_eq_symm (X : Type) [TopologicalSpace X]
    (n : ℕ) (b : SingularMayerVietoris.SingularHomology X n) :
    positiveCircleCross X n b = (circleProductHomologyEquiv X n).symm (0, b) := by
  apply (circleProductHomologyEquiv X n).injective
  rw [circleProductHomologyEquiv_positiveCircleCross, LinearEquiv.apply_symm_apply]

private theorem
    PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_eq_section_add_cross (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :
    (circleProductHomologyEquiv X n).symm a =
      circleSectionHomology X (n + 1) a.1 + positiveCircleCross X n a.2 := by
  apply (circleProductHomologyEquiv X n).injective
  rw [LinearEquiv.apply_symm_apply, map_add, circleProductHomologyEquiv_section,
    circleProductHomologyEquiv_positiveCircleCross]
  exact Prod.ext (add_zero _).symm (zero_add _).symm

private theorem
    PeriodTorusHigherHomology.positiveCircleCross_naturality {X : Type} [TopologicalSpace X]
    {Y : Type} [TopologicalSpace Y] (f : C(X, Y)) (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)
        (positiveCircleCross X n b) =
      positiveCircleCross Y n (SingularMayerVietoris.singularHomologyMap f n b) := by
  calc
    _ =
        SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1)
          ((circleProductHomologyEquiv X n).symm (0, b)) :=
      congrArg (SingularMayerVietoris.singularHomologyMap (circleProductMap f) (n + 1))
        (positiveCircleCross_eq_symm X n b)
    _ =
        (circleProductHomologyEquiv Y n).symm
          (0, SingularMayerVietoris.singularHomologyMap f n b) := by
      simpa only [map_zero] using circleProductHomologyEquiv_symm_naturality f n (0, b)
    _ = _ :=
      (positiveCircleCross_eq_symm Y n (SingularMayerVietoris.singularHomologyMap f n b)).symm

private abbrev PeriodTorusHigherHomology.binomialModule (r n : ℕ) :=
  Fin (r.choose n) → ℤ

private def PeriodTorusHigherHomology.binomialPascalIndexEquiv (r n : ℕ) :
    Fin ((r + 1).choose (n + 1)) ≃ Fin (r.choose (n + 1)) ⊕ Fin (r.choose n) :=
  (finCongr ((Nat.choose_succ_succ' r n).trans (Nat.add_comm _ _))).trans finSumFinEquiv.symm

private def PeriodTorusHigherHomology.binomialModuleSuccEquiv (r n : ℕ) :
    binomialModule (r + 1) (n + 1) ≃ₗ[ℤ] binomialModule r (n + 1) × binomialModule r n :=
  (LinearEquiv.piCongrLeft' ℤ (fun _ => ℤ) (binomialPascalIndexEquiv r n)).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ ℤ ℤ)

@[simp]
private theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_apply_fst (r n : ℕ)
    (x : binomialModule (r + 1) (n + 1)) (i : Fin (r.choose (n + 1))) :
    (binomialModuleSuccEquiv r n x).1 i = x ((binomialPascalIndexEquiv r n).symm (Sum.inl i)) :=
  rfl

@[simp]
private theorem PeriodTorusHigherHomology.binomialModuleSuccEquiv_apply_snd (r n : ℕ)
    (x : binomialModule (r + 1) (n + 1)) (i : Fin (r.choose n)) :
    (binomialModuleSuccEquiv r n x).2 i = x ((binomialPascalIndexEquiv r n).symm (Sum.inr i)) :=
  rfl

private def
    PeriodTorusHigherHomology.integerBinomialZeroEquiv (r : ℕ) : ℤ ≃ₗ[ℤ] binomialModule r 0 :=
  (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm.trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ => ℤ) (finCongr (Nat.choose_zero_right r)).symm)

private theorem PeriodTorusHigherHomology.binomialModule_finrank (r n : ℕ) :
    Module.finrank ℤ (binomialModule r n) = r.choose n :=
  Module.finrank_fin_fun ℤ

private theorem PeriodTorusHigherHomology.binomialModule_subsingleton_of_lt {r n : ℕ} (h : r < n) :
    Subsingleton (binomialModule r n) := by
  change Subsingleton (Fin (r.choose n) → ℤ)
  rw [Nat.choose_eq_zero_of_lt h]
  infer_instance

private instance PeriodTorusHigherHomology.binomialModule_zero_succ_subsingleton (n : ℕ) :
    Subsingleton (binomialModule 0 (n + 1)) :=
  binomialModule_subsingleton_of_lt (Nat.zero_lt_succ n)

private theorem PeriodTorusHigherHomology.binomialModule_eq_zero_of_lt {r n : ℕ} (h : r < n)
    (x : binomialModule r n) : x = 0 :=
  @Subsingleton.elim (binomialModule r n) (binomialModule_subsingleton_of_lt h) x 0

private def PeriodTorusHigherHomology.productTorusHomologyEquiv :
    (r n : ℕ) → SingularMayerVietoris.SingularHomology (ProductTorus r) n ≃ₗ[ℤ] binomialModule r n
  | r, 0 => (connectedHomologyZeroEquiv (ProductTorus r)).trans (integerBinomialZeroEquiv r)
  | 0, n + 1 =>
    by
    letI := totallyDisconnected_homology_subsingleton PUnit (n + 1) (Nat.succ_ne_zero n)
    exact
      (homeomorphHomologyEquiv productTorusZeroHomeomorph (n + 1)).trans
        (LinearEquiv.ofSubsingleton (SingularMayerVietoris.SingularHomology PUnit (n + 1))
          (binomialModule 0 (n + 1)))
  | r + 1, n + 1 =>
    ((homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)).toAddEquiv.trans
        ((circleProductHomologyEquiv (ProductTorus r) n).toAddEquiv.trans
          (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
                (productTorusHomologyEquiv r n).toAddEquiv).trans
            (binomialModuleSuccEquiv r n).symm.toAddEquiv))).toIntLinearEquiv

@[simp]
private theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_zero (r : ℕ) :
    productTorusHomologyEquiv r 0 =
      (connectedHomologyZeroEquiv (ProductTorus r)).trans (integerBinomialZeroEquiv r) := by
  cases r <;> rfl

private theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ (r n : ℕ) :
    productTorusHomologyEquiv (r + 1) (n + 1) =
      ((homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1)).toAddEquiv.trans
          ((circleProductHomologyEquiv (ProductTorus r) n).toAddEquiv.trans
            (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
                  (productTorusHomologyEquiv r n).toAddEquiv).trans
              (binomialModuleSuccEquiv r n).symm.toAddEquiv))).toIntLinearEquiv :=
  rfl

private theorem PeriodTorusHigherHomology.productTorusHomologyEquiv_succ_apply (r n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (ProductTorus (r + 1)) (n + 1)) :
    binomialModuleSuccEquiv r n (productTorusHomologyEquiv (r + 1) (n + 1) a) =
      (productTorusHomologyEquiv r (n + 1)
          (circleProjectionHomology (ProductTorus r) (n + 1)
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)),
        productTorusHomologyEquiv r n
          (circleBoundary (ProductTorus r) n
            (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a))) := by
  rw [productTorusHomologyEquiv_succ]
  change
    binomialModuleSuccEquiv r n
        ((binomialModuleSuccEquiv r n).symm
          (((productTorusHomologyEquiv r (n + 1)).toAddEquiv.prodCongr
              (productTorusHomologyEquiv r n).toAddEquiv)
            (circleProductHomologyEquiv (ProductTorus r) n
              (homeomorphHomologyEquiv (productTorusSuccHomeomorph r) (n + 1) a)))) =
      _
  rw [LinearEquiv.apply_symm_apply, circleProductHomologyEquiv_apply]
  rfl

private theorem PeriodTorusHigherHomology.productTorus_homology_free (r n : ℕ) :
    Module.Free ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) :=
  Module.Free.of_equiv (productTorusHomologyEquiv r n).symm

private theorem PeriodTorusHigherHomology.productTorus_homology_finite (r n : ℕ) :
    Module.Finite ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) :=
  Module.Finite.of_surjective (productTorusHomologyEquiv r n).symm.toLinearMap
    (productTorusHomologyEquiv r n).symm.surjective

private theorem PeriodTorusHigherHomology.productTorus_homology_finrank (r n : ℕ) :
    Module.finrank ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) = r.choose n := by
  rw [(productTorusHomologyEquiv r n).finrank_eq]
  exact binomialModule_finrank r n

private theorem PeriodTorusHigherHomology.productTorus_homology_torsionFree (r n : ℕ) :
    Module.IsTorsionFree ℤ (SingularMayerVietoris.SingularHomology (ProductTorus r) n) := by
  let := productTorus_homology_free r n
  infer_instance

private theorem
    PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt {r n : ℕ} (h : r < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology (ProductTorus r) n) := by
  let := binomialModule_subsingleton_of_lt h
  exact (productTorusHomologyEquiv r n).injective.subsingleton

end Mathoverflow1973

end
