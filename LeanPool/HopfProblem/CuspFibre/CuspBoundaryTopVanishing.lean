/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.PeriodFamily.Core8
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Toric.ToricSpace2
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.CuspFibre.CuspPositiveRetraction
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Toric.CuspHoneycombHexagon
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology3
import all LeanPool.HopfProblem.CuspFibre.CuspSpecialization
import all LeanPool.HopfProblem.HomologyOfX.CuspCoinvariants
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology4
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing1
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldHomology1
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Pi1.TwistGroup
import all LeanPool.HopfProblem.PeriodFamily.Core5
import all LeanPool.HopfProblem.PeriodFamily.Core6
import all LeanPool.HopfProblem.PeriodFamily.Core8

/-!
# Hopf problem: cusp fibre · cusp boundary top vanishing

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

private theorem CuspBoundaryTopVanishing.hexagon_second_eq_zero_of_baseFirstZero
    {y : CuspHoneycombTiling.Plane} (hy : y ∈ CuspHoneycombTiling.baseCell)
    (hzero : CuspCentralHomology.baseTorusPoint y 0 = 0) : y 1 = 0 := by
  change ((-y 1 : ℝ) : AddCircle (1 : ℝ)) = 0 at hzero
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  have hn' : (n : ℝ) = -y 1 := by simpa only [zsmul_eq_mul, mul_one] using hn
  have hb : |(n : ℝ)| < 1 := by
    rw [hn', abs_neg]
    exact (CuspHoneycombTiling.baseCell_coordinate_bound_sharp hy 1).trans_lt (by norm_num)
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast (abs_lt.mp hb).1
  have hnhi : n < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hb).2
  have hnzero : n = 0 := by omega
  rw [hnzero, Int.cast_zero] at hn'
  linarith

private theorem CuspBoundaryTopVanishing.baseTorusProjection_overlapPhaseHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) (a : ℝ) (p : CuspCentralHomology.OverlapPhaseCell a) :
    CuspCentralHomology.baseTorusProjection C r hr
        (CuspCentralHomology.overlapPhaseHomeomorph C r hr hr1 hC hR a p :
          CuspRetraction.QuotientCentralFibre C r) =
      CuspCentralHomology.baseTorusPoint (p.2 : CuspHoneycombTiling.Plane) := by
  rw [CuspCentralHomology.overlapPhaseHomeomorph_coe,
    CuspCentralHomology.baseTorusProjection_honeycombCollapseMap]

private theorem CuspBoundaryTopVanishing.baseTorusPoint_overlapPhaseHomeomorph_symm
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) (a : ℝ) (q : CuspCentralHomology.overlapRegion C r hr a) :
    CuspCentralHomology.baseTorusPoint
        (((CuspCentralHomology.overlapPhaseHomeomorph C r hr hr1 hC hR a).symm q).2 :
          CuspHoneycombTiling.Plane) =
      CuspCentralHomology.baseTorusProjection C r hr
        (q : CuspRetraction.QuotientCentralFibre C r) := by
  have h :=
    baseTorusProjection_overlapPhaseHomeomorph C r hr hr1 hC hR a
      ((CuspCentralHomology.overlapPhaseHomeomorph C r hr hr1 hC hR a).symm q)
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

private theorem CuspBoundaryTopVanishing.overlapPhaseHomeomorph_symm_second_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) (a : ℝ) (q : CuspCentralHomology.overlapRegion C r hr a)
    (hzero :
      CuspCentralHomology.baseTorusProjection C r hr (q : CuspRetraction.QuotientCentralFibre C r)
          0 =
        0) :
    (((CuspCentralHomology.overlapPhaseHomeomorph C r hr hr1 hC hR a).symm q).2 :
          CuspHoneycombTiling.Plane)
        1 =
      0 := by
  apply hexagon_second_eq_zero_of_baseFirstZero
  · exact
      (CuspCentralHomology.Radial.mem_baseCell_iff _).mpr
        ((CuspCentralHomology.overlapPhaseHomeomorph C r hr hr1 hC hR a).symm q).2.2.2.le
  · rw [baseTorusPoint_overlapPhaseHomeomorph_symm]
    exact hzero

private abbrev CuspBoundaryTopVanishing.AxisAnnulus (a : ℝ) :=
  { x : CuspCentralHomology.Radial.Annulus a // (x : (CuspHoneycombTiling.Plane)) 1 = 0 }

private def CuspBoundaryTopVanishing.axisAnnulusInclusion (a : ℝ) :
    C(AxisAnnulus a, CuspCentralHomology.Radial.Annulus a) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private theorem
    CuspBoundaryTopVanishing.axisAnnulus_ne_zero (a : ℝ) (ha : 0 ≤ a) (x : AxisAnnulus a) :
    (x.1 : (CuspHoneycombTiling.Plane)) ≠ 0 :=
  (CuspCentralHomology.Radial.cellGauge_pos_iff _).mp (ha.trans_lt x.1.2.1)

private def CuspBoundaryTopVanishing.axisAnnulusDirection : (CuspHoneycombTiling.Plane) :=
  ![0, (1 / 2 : ℝ)]

@[simp]
private theorem CuspBoundaryTopVanishing.axisAnnulusDirection_gauge :
    CuspCentralHomology.Radial.cellGauge axisAnnulusDirection = 1 := by
  norm_num [axisAnnulusDirection, CuspCentralHomology.Radial.cellGauge]

private def
    CuspBoundaryTopVanishing.axisAnnulusBlend (a : ℝ) (s : unitInterval) (x : AxisAnnulus a) :
    (CuspHoneycombTiling.Plane) :=
  (1 - (s : ℝ)) • (x.1 : (CuspHoneycombTiling.Plane)) + (s : ℝ) • axisAnnulusDirection

@[simp]
private theorem CuspBoundaryTopVanishing.axisAnnulusBlend_zero (a : ℝ) (x : AxisAnnulus a) :
    axisAnnulusBlend a 0 x = (x.1 : (CuspHoneycombTiling.Plane)) := by simp [axisAnnulusBlend]

@[simp]
private theorem CuspBoundaryTopVanishing.axisAnnulusBlend_one (a : ℝ) (x : AxisAnnulus a) :
    axisAnnulusBlend a 1 x = axisAnnulusDirection := by simp [axisAnnulusBlend]

private theorem CuspBoundaryTopVanishing.axisAnnulusBlend_second (a : ℝ) (s : unitInterval)
    (x : AxisAnnulus a) : axisAnnulusBlend a s x 1 = (s : ℝ) / 2 := by
  simp [axisAnnulusBlend, axisAnnulusDirection, x.2, div_eq_mul_inv]

private theorem
    CuspBoundaryTopVanishing.axisAnnulusBlend_ne_zero (a : ℝ) (ha : 0 ≤ a) (s : unitInterval)
    (x : AxisAnnulus a) : axisAnnulusBlend a s x ≠ 0 := by
  intro hzero
  have hs : (s : ℝ) = 0 := by
    have h := congrFun hzero 1
    rw [axisAnnulusBlend_second] at h
    change (s : ℝ) / 2 = 0 at h
    linarith
  apply axisAnnulus_ne_zero a ha x
  simpa [axisAnnulusBlend, hs] using hzero

private theorem CuspBoundaryTopVanishing.axisAnnulusBlend_gauge_pos (a : ℝ) (ha : 0 ≤ a)
    (s : unitInterval) (x : AxisAnnulus a) :
    0 < CuspCentralHomology.Radial.cellGauge (axisAnnulusBlend a s x) :=
  (CuspCentralHomology.Radial.cellGauge_pos_iff _).mpr (axisAnnulusBlend_ne_zero a ha s x)

private theorem CuspBoundaryTopVanishing.axisAnnulusBlend_continuous (a : ℝ) :
    Continuous (fun p : unitInterval × AxisAnnulus a => axisAnnulusBlend a p.1 p.2) := by
  have hx :
    Continuous (fun p : unitInterval × AxisAnnulus a => (p.2.1 : (CuspHoneycombTiling.Plane))) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul hx).add
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const)

private def
    CuspBoundaryTopVanishing.axisAnnulusRadius (a : ℝ) (s : unitInterval) (x : AxisAnnulus a) :
    ℝ :=
  CuspCentralHomology.Radial.radiusBlend ((a + 1) / 2) s
    (CuspCentralHomology.Radial.cellGauge (x.1 : (CuspHoneycombTiling.Plane)))

@[simp]
private theorem CuspBoundaryTopVanishing.axisAnnulusRadius_zero (a : ℝ) (x : AxisAnnulus a) :
    axisAnnulusRadius a 0 x =
      CuspCentralHomology.Radial.cellGauge (x.1 : (CuspHoneycombTiling.Plane)) := by
  simp [axisAnnulusRadius, CuspCentralHomology.Radial.radiusBlend]

@[simp]
private theorem CuspBoundaryTopVanishing.axisAnnulusRadius_one (a : ℝ) (x : AxisAnnulus a) :
    axisAnnulusRadius a 1 x = (a + 1) / 2 := by
  simp [axisAnnulusRadius, CuspCentralHomology.Radial.radiusBlend]

private theorem
    CuspBoundaryTopVanishing.axisAnnulusRadius_mem (a : ℝ) (ha1 : a < 1) (s : unitInterval)
    (x : AxisAnnulus a) : axisAnnulusRadius a s x ∈ Set.Ioo a 1 :=
  CuspCentralHomology.Radial.radiusBlend_mem (convex_Ioo a 1) ((a + 1) / 2)
    ⟨by linarith, by linarith⟩ s _ x.1.2

private theorem CuspBoundaryTopVanishing.axisAnnulusRadius_continuous (a : ℝ) :
    Continuous (fun p : unitInterval × AxisAnnulus a => axisAnnulusRadius a p.1 p.2) := by
  have hx :
    Continuous (fun p : unitInterval × AxisAnnulus a => (p.2.1 : (CuspHoneycombTiling.Plane))) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  exact
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          (CuspCentralHomology.Radial.cellGauge_continuous.comp hx)).add
      ((continuous_subtype_val.comp continuous_fst).mul continuous_const)

private def
    CuspBoundaryTopVanishing.axisAnnulusContractionPoint (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    CuspCentralHomology.Radial.Annulus a :=
  ⟨((a + 1) / 2) • axisAnnulusDirection,
    by
    rw [CuspCentralHomology.Radial.cellGauge_smul_of_nonneg _ (by linarith : 0 ≤ (a + 1) / 2),
      axisAnnulusDirection_gauge, mul_one]
    constructor <;> linarith⟩

@[simp]
private theorem CuspBoundaryTopVanishing.axisAnnulusContractionPoint_coe (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    (axisAnnulusContractionPoint a ha ha1 : (CuspHoneycombTiling.Plane)) =
      ((a + 1) / 2) • axisAnnulusDirection :=
  rfl

private theorem CuspBoundaryTopVanishing.axisAnnulusContractFormula_gauge_mo1973_29730 (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval) (x : AxisAnnulus a) :
    CuspCentralHomology.Radial.cellGauge
        ((axisAnnulusRadius a s x /
            CuspCentralHomology.Radial.cellGauge (axisAnnulusBlend a s x)) •
          axisAnnulusBlend a s x) =
      axisAnnulusRadius a s x := by
  have hz := axisAnnulusBlend_gauge_pos a ha s x
  have hr := ha.trans_lt (axisAnnulusRadius_mem a ha1 s x).1
  rw [CuspCentralHomology.Radial.cellGauge_smul_of_nonneg _ (div_nonneg hr.le hz.le),
    div_mul_cancel₀ _ hz.ne']

private def CuspBoundaryTopVanishing.axisAnnulusContract (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : AxisAnnulus a) : CuspCentralHomology.Radial.Annulus a :=
  ⟨(axisAnnulusRadius a s x / CuspCentralHomology.Radial.cellGauge (axisAnnulusBlend a s x)) •
      axisAnnulusBlend a s x,
    by
    rw [axisAnnulusContractFormula_gauge_mo1973_29730 a ha ha1 s x]
    exact axisAnnulusRadius_mem a ha1 s x⟩

@[simp]
private theorem CuspBoundaryTopVanishing.axisAnnulusContract_coe (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (x : AxisAnnulus a) :
    (axisAnnulusContract a ha ha1 s x : (CuspHoneycombTiling.Plane)) =
      (axisAnnulusRadius a s x / CuspCentralHomology.Radial.cellGauge (axisAnnulusBlend a s x)) •
        axisAnnulusBlend a s x :=
  rfl

private theorem CuspBoundaryTopVanishing.axisAnnulusContract_continuous (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) :
    Continuous (fun p : unitInterval × AxisAnnulus a => axisAnnulusContract a ha ha1 p.1 p.2) :=
  (((axisAnnulusRadius_continuous a).div
            (CuspCentralHomology.Radial.cellGauge_continuous.comp (axisAnnulusBlend_continuous a))
            (fun p => (axisAnnulusBlend_gauge_pos a ha p.1 p.2).ne')).smul
        (axisAnnulusBlend_continuous a)).subtype_mk
    _

@[simp]
private theorem CuspBoundaryTopVanishing.axisAnnulusContract_zero (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (x : AxisAnnulus a) : axisAnnulusContract a ha ha1 0 x = x.1 := by
  apply Subtype.ext
  simp only [axisAnnulusContract_coe, axisAnnulusRadius_zero, axisAnnulusBlend_zero,
    div_self (ha.trans_lt x.1.2.1).ne', one_smul]

@[simp]
private theorem CuspBoundaryTopVanishing.axisAnnulusContract_one (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (x : AxisAnnulus a) :
    axisAnnulusContract a ha ha1 1 x = axisAnnulusContractionPoint a ha ha1 := by
  apply Subtype.ext
  simp only [axisAnnulusContract_coe, axisAnnulusRadius_one, axisAnnulusBlend_one,
    axisAnnulusDirection_gauge, div_one, axisAnnulusContractionPoint_coe]

private def CuspBoundaryTopVanishing.axisAnnulusContraction (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (axisAnnulusInclusion a).Homotopy
      (ContinuousMap.const (AxisAnnulus a) (axisAnnulusContractionPoint a ha ha1))
    where
  toFun p := axisAnnulusContract a ha ha1 p.1 p.2
  continuous_toFun := axisAnnulusContract_continuous a ha ha1
  map_zero_left := axisAnnulusContract_zero a ha ha1
  map_one_left := axisAnnulusContract_one a ha ha1

private theorem CuspBoundaryTopVanishing.homologyLinearMap_comp_eq_zero_of_subsingleton {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (g : C(X, Z))
    (h : C(Z, Y)) (n : ℕ) [Subsingleton (SingularMayerVietoris.SingularHomology Z n)] :
    (SingularMayerVietoris.singularHomologyMap h n).comp
        (SingularMayerVietoris.singularHomologyMap g n) =
      0 := by
  apply LinearMap.ext
  intro a
  change
    SingularMayerVietoris.singularHomologyMap h n
        (SingularMayerVietoris.singularHomologyMap g n a) =
      0
  rw [Subsingleton.elim (SingularMayerVietoris.singularHomologyMap g n a) 0, map_zero]

private theorem
    CuspBoundaryTopVanishing.singularHomologyMap_comp_eq_zero_of_subsingleton {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (g : C(X, Z))
    (h : C(Z, Y)) (n : ℕ) [Subsingleton (SingularMayerVietoris.SingularHomology Z n)] :
    SingularMayerVietoris.singularHomologyMap (h.comp g) n = 0 := by
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact homologyLinearMap_comp_eq_zero_of_subsingleton g h n

private theorem
    CuspBoundaryTopVanishing.singularHomologyMap_eq_zero_of_homotopic_factor {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] {Z : Type} [TopologicalSpace Z] (f : C(X, Y))
    (g : C(X, Z)) (h : C(Z, Y)) (hfac : f.Homotopic (h.comp g)) (n : ℕ)
    [Subsingleton (SingularMayerVietoris.SingularHomology Z n)] :
    SingularMayerVietoris.singularHomologyMap f n = 0 := by
  rw [PeriodTorusHigherHomology.homotopic_homologyMap hfac n]
  exact singularHomologyMap_comp_eq_zero_of_subsingleton g h n

private theorem CuspBoundaryTopVanishing.singularHomologyMap_eq_zero_of_connecting {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U V : Set X) (U' V' : Set Y)
    (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V') (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (hU' : IsOpen U') (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ)
    (n : ℕ)
    (hinj :
      Function.Injective (SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hcover' n))
    (hzero :
      SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.intersectionRestriction f U V U' V' hfU hfV) n =
        0) :
    SingularMayerVietoris.singularHomologyMap f (n + 1) = 0 := by
  apply LinearMap.ext
  intro a
  apply hinj
  simpa only [hzero, LinearMap.zero_apply, map_zero] using
    (SingularMayerVietoris.connectingHomomorphism_naturality_apply f U V U' V' hfU hfV hU hV
        hcover hU' hV' hcover' n a).symm

private def CuspBoundaryTopVanishing.pullbackIntersectionMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U' V' : Set Y) :
    C(((f ⁻¹' U') ∩ (f ⁻¹' V') : Set X), (U' ∩ V' : Set Y)) :=
  SingularMayerVietoris.intersectionRestriction f (f ⁻¹' U') (f ⁻¹' V') U' V' (fun _ hx => hx)
    (fun _ hx => hx)

private theorem CuspBoundaryTopVanishing.pullback_cover {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (U' V' : Set Y) (hcover' : U' ∪ V' = Set.univ) :
    (f ⁻¹' U') ∪ (f ⁻¹' V') = Set.univ := by rw [← Set.preimage_union, hcover', Set.preimage_univ]

private theorem
    CuspBoundaryTopVanishing.singularHomologyMap_eq_zero_of_pullback_connecting {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (U' V' : Set Y) (hU' : IsOpen U')
    (hV' : IsOpen V') (hcover' : U' ∪ V' = Set.univ) (n : ℕ)
    (hinj :
      Function.Injective (SingularMayerVietoris.connectingHomomorphism U' V' hU' hV' hcover' n))
    (hzero : SingularMayerVietoris.singularHomologyMap (pullbackIntersectionMap f U' V') n = 0) :
    SingularMayerVietoris.singularHomologyMap f (n + 1) = 0 :=
  singularHomologyMap_eq_zero_of_connecting f (f ⁻¹' U') (f ⁻¹' V') U' V' (fun _ hx => hx)
    (fun _ hx => hx) (hU'.preimage f.continuous) (hV'.preimage f.continuous)
    (pullback_cover f U' V' hcover') hU' hV' hcover' n hinj hzero

private def CuspBoundaryTopVanishing.centralH4Connecting (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha1 : a < 1) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 4 →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (CuspCentralHomology.overlapRegion C ε hε a) 3 :=
  SingularMayerVietoris.connectingHomomorphism (CuspCentralHomology.outerRegion C ε hε a)
    (CuspCentralHomology.innerRegion C ε hε)
    (CuspCentralHomology.outerRegion_isOpen C ε hε hε1 hC hR a)
    (CuspCentralHomology.innerRegion_isOpen C ε hε hε1 hC hR)
    (CuspCentralHomology.outerRegion_union_innerRegion C ε hε a ha1) 3

private theorem
    CuspBoundaryTopVanishing.centralH4Connecting_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Function.Injective (centralH4Connecting C ε hε hε1 hC hR a ha1) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (CuspCentralHomology.outerRegion C ε hε a) 4) :=
    CuspCentralHomology.outerRegion_homology_subsingleton C ε hε hε1 hC hR a ha ha1 1
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (CuspCentralHomology.innerRegion C ε hε) 4) :=
    CuspCentralHomology.innerRegion_homology_subsingleton C ε hε hε1 hC hR 1
  exact
    CuspCentralHomology.coverConnecting_injective_of_vanishing
      (CuspCentralHomology.outerRegion C ε hε a) (CuspCentralHomology.innerRegion C ε hε)
      (CuspCentralHomology.outerRegion_isOpen C ε hε hε1 hC hR a)
      (CuspCentralHomology.innerRegion_isOpen C ε hε hε1 hC hR)
      (CuspCentralHomology.outerRegion_union_innerRegion C ε hε a ha1) 3

private def
    CuspBoundaryTopVanishing.centralPullbackIntersectionMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) {X : Type} [TopologicalSpace X] (a : ℝ)
    (f : C(X, CuspRetraction.QuotientCentralFibre C ε)) :
    C(((f ⁻¹' CuspCentralHomology.outerRegion C ε hε a) ∩
          (f ⁻¹' CuspCentralHomology.innerRegion C ε hε) :
        Set X),
      CuspCentralHomology.overlapRegion C ε hε a) :=
  pullbackIntersectionMap f (CuspCentralHomology.outerRegion C ε hε a)
    (CuspCentralHomology.innerRegion C ε hε)

private theorem CuspBoundaryTopVanishing.central_homologyFourMap_eq_zero_of_intersection
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {X : Type} [TopologicalSpace X] (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (f : C(X, CuspRetraction.QuotientCentralFibre C ε))
    (hzero :
      SingularMayerVietoris.singularHomologyMap (centralPullbackIntersectionMap C ε hε a f) 3 =
        0) :
    SingularMayerVietoris.singularHomologyMap f 4 = 0 :=
  singularHomologyMap_eq_zero_of_pullback_connecting f (CuspCentralHomology.outerRegion C ε hε a)
    (CuspCentralHomology.innerRegion C ε hε)
    (CuspCentralHomology.outerRegion_isOpen C ε hε hε1 hC hR a)
    (CuspCentralHomology.innerRegion_isOpen C ε hε hε1 hC hR)
    (CuspCentralHomology.outerRegion_union_innerRegion C ε hε a ha1) 3
    (centralH4Connecting_injective C ε hε hε1 hC hR a ha ha1) hzero

private theorem CuspBoundaryTopVanishing.central_homologyFourMap_eq_zero_of_homotopic_factor
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {X : Type} [TopologicalSpace X] {Y : Type}
    [TopologicalSpace Y] [Subsingleton (SingularMayerVietoris.SingularHomology Y 3)] (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) (f : C(X, CuspRetraction.QuotientCentralFibre C ε))
    (g :
      C(((f ⁻¹' CuspCentralHomology.outerRegion C ε hε a) ∩
            (f ⁻¹' CuspCentralHomology.innerRegion C ε hε) :
          Set X),
        Y))
    (k : C(Y, CuspCentralHomology.overlapRegion C ε hε a))
    (hfactor : (centralPullbackIntersectionMap C ε hε a f).Homotopic (k.comp g)) :
    SingularMayerVietoris.singularHomologyMap f 4 = 0 := by
  apply central_homologyFourMap_eq_zero_of_intersection C ε hε hε1 hC hR a ha ha1 f
  exact
    singularHomologyMap_eq_zero_of_homotopic_factor (centralPullbackIntersectionMap C ε hε a f) g
      k hfactor 3

private theorem CuspBoundaryTopVanishing.central_homologyFourMap_eq_zero_of_phase_homotopic_factor
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {X : Type} [TopologicalSpace X] (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (f : C(X, CuspRetraction.QuotientCentralFibre C ε))
    (g :
      C(((f ⁻¹' CuspCentralHomology.outerRegion C ε hε a) ∩
            (f ⁻¹' CuspCentralHomology.innerRegion C ε hε) :
          Set X),
        ToricSpace.CompactFibreTorus))
    (k : C(ToricSpace.CompactFibreTorus, CuspCentralHomology.overlapRegion C ε hε a))
    (hfactor : (centralPullbackIntersectionMap C ε hε a f).Homotopic (k.comp g)) :
    SingularMayerVietoris.singularHomologyMap f 4 = 0 := by
  let : Subsingleton (SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus 3) :=
    CuspCentralHomology.compactFibreTorus_homology_subsingleton 0
  exact
    central_homologyFourMap_eq_zero_of_homotopic_factor C ε hε hε1 hC hR a ha ha1 f g k hfactor

private theorem CuspBoundaryTopVanishing.baseFirstZero_overlap_homotopic_phase
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) {X : Type} [TopologicalSpace X] (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (hzero : ∀ x, CuspCentralHomology.baseTorusProjection C r hr (f x) 0 = 0) :
    ∃ g :
      C(((f ⁻¹' CuspCentralHomology.outerRegion C r hr a) ∩
            (f ⁻¹' CuspCentralHomology.innerRegion C r hr) :
          Set X),
        ToricSpace.CompactFibreTorus),
      ∃ k : C(ToricSpace.CompactFibreTorus, CuspCentralHomology.overlapRegion C r hr a),
        (centralPullbackIntersectionMap C r hr a f).Homotopic (k.comp g) := by
  let e := CuspCentralHomology.overlapPhaseHomeomorph C r hr hr1 hC hR a
  let i := centralPullbackIntersectionMap C r hr a f
  let g :
    C(((f ⁻¹' CuspCentralHomology.outerRegion C r hr a) ∩
          (f ⁻¹' CuspCentralHomology.innerRegion C r hr) :
        Set X),
      ToricSpace.CompactFibreTorus) :=
    ⟨fun x => (e.symm (i x)).1, (e.symm.continuous.comp i.continuous).fst⟩
  let b :
    C(((f ⁻¹' CuspCentralHomology.outerRegion C r hr a) ∩
          (f ⁻¹' CuspCentralHomology.innerRegion C r hr) :
        Set X),
      AxisAnnulus a) :=
    ⟨fun x =>
      ⟨(e.symm (i x)).2,
        overlapPhaseHomeomorph_symm_second_zero C r hr hr1 hC hR a (i x) (hzero x.1)⟩,
      (e.symm.continuous.comp i.continuous).snd.subtype_mk _⟩
  let k : C(ToricSpace.CompactFibreTorus, CuspCentralHomology.overlapRegion C r hr a) :=
    ⟨fun z => e (z, axisAnnulusContractionPoint a ha ha1),
      e.continuous.comp (continuous_id.prodMk continuous_const)⟩
  refine ⟨g, k, ⟨?_⟩⟩
  refine
    { toFun := fun p => e (g p.2, axisAnnulusContraction a ha ha1 (p.1, b p.2))
      continuous_toFun :=
        e.continuous.comp
          ((g.continuous.comp continuous_snd).prodMk
            ((axisAnnulusContraction a ha ha1).continuous.comp
              (continuous_fst.prodMk (b.continuous.comp continuous_snd))))
      map_zero_left := ?_
      map_one_left := ?_ }
  · intro x
    change e ((e.symm (i x)).1, axisAnnulusContract a ha ha1 0 (b x)) = i x
    rw [axisAnnulusContract_zero]
    exact e.apply_symm_apply (i x)
  · intro x
    change
      e (g x, axisAnnulusContract a ha ha1 1 (b x)) =
        e (g x, axisAnnulusContractionPoint a ha ha1)
    rw [axisAnnulusContract_one]

private theorem CuspBoundaryTopVanishing.central_homologyFourMap_eq_zero_of_baseFirstZero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r))
    (hR : ToricSpace.SmallDrift C r) {X : Type} [TopologicalSpace X]
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (hzero : ∀ x, CuspCentralHomology.baseTorusProjection C r hr (f x) 0 = 0) :
    SingularMayerVietoris.singularHomologyMap f 4 = 0 := by
  obtain ⟨g, k, hfactor⟩ :=
    baseFirstZero_overlap_homotopic_phase C r hr hr1 hC hR (1 / 2) (by norm_num) (by norm_num) f
      hzero
  exact
    central_homologyFourMap_eq_zero_of_phase_homotopic_factor C r hr hr1 hC hR (1 / 2)
      (by norm_num) (by norm_num) f g k hfactor

private theorem
    CuspSpecialization.expFibreAction_exponentialPoint (w : Fin 2 → ℂ) {t : ℂ} (ht : t ≠ 0)
    (z : ComplexPlane₂) :
    CuspRetraction.expFibreAction w (CuspUniformization.exponentialPoint t z) =
      CuspUniformization.exponentialPoint t (w + z) := by
  have hx := CuspUniformization.exponentialPoint_mem ht z
  have hx' :
    CuspRetraction.expFibreAction w (CuspUniformization.exponentialPoint t z) ∈
      ToricSpace.openTorus := by
    apply (ToricSpace.mem_openTorus_iff _).mpr
    rw [CuspRetraction.time_expFibreAction, CuspUniformization.time_exponentialPoint ht]
    exact ht
  apply
    CuspUniformization.torusCoordinates_injective hx'
      (CuspUniformization.exponentialPoint_mem ht _)
  rw [CuspRetraction.expFibreAction, ToricSpace.torusCoordinates_action _ hx,
    CuspUniformization.torusCoordinates_exponentialPoint ht,
    CuspUniformization.torusCoordinates_exponentialPoint ht]
  ext i
  fin_cases i <;>
    simp [ToricSpace.fibreMultiplier, CuspRetraction.expFibreUnits_coe,
      CuspUniformization.exponentialCoordinates, CuspUniformization.exponential_add]

private theorem
    CuspSpecialization.position_exponentialPoint {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    ToricSpace.position (CuspUniformization.exponentialPoint t z) = fun i =>
      (-2 * Real.pi * (z i).im) / Real.log ‖t‖ := by
  ext i
  simp only [ToricSpace.position, CuspUniformization.time_exponentialPoint ht,
    ToricSpace.logCoordinates, ToricSpace.logNorm,
    CuspUniformization.torusCoordinates_exponentialPoint ht]
  have he :
    CuspUniformization.exponentialCoordinates t z i.castSucc =
      CuspUniformization.exponential (z i) := by fin_cases i <;> rfl
  rw [he, CuspUniformization.log_norm_exponential]

private theorem CuspSpecialization.markedCoordinate_im (Z : Matrix (Fin 2) (Fin 2) ℂ)
    (a β : (CuspHoneycombTiling.Plane)) (i : Fin 2) :
    ((CuspRetraction.realToComplex a + Z *ᵥ CuspRetraction.realToComplex β) i).im =
      (Z.map Complex.im *ᵥ β) i := by
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.mul_im, ]

private theorem
    CuspSpecialization.position_markedExponentialPoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (hlog : Real.log ‖CuspUniformization.exponential s‖ ≠ 0)
    (a β : (CuspHoneycombTiling.Plane)) :
    ToricSpace.position
        (CuspUniformization.exponentialPoint (CuspUniformization.exponential s)
          (CuspRetraction.realToComplex a +
            CuspUniformization.logarithmicPeriod C s *ᵥ CuspRetraction.realToComplex β)) =
      ToricSpace.displacement C (CuspUniformization.exponential s) β := by
  rw [position_exponentialPoint (CuspUniformization.exponential_ne_zero s)]
  ext i
  rw [markedCoordinate_im]
  apply (div_eq_iff hlog).mpr
  have h := congrFun (CuspUniformization.imaginary_displacement C s hlog β) i
  simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using h.symm

private theorem
    CuspSpecialization.changeTwist_markedExponentialPoint (C D : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (s : ℂ) (hlog : Real.log ‖CuspUniformization.exponential s‖ < 0)
    (hR :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4)
    (a β : (CuspHoneycombTiling.Plane)) :
    CuspRetraction.changeTwist C D
        (CuspUniformization.exponentialPoint (CuspUniformization.exponential s)
          (CuspRetraction.realToComplex a +
            CuspUniformization.logarithmicPeriod C s *ᵥ CuspRetraction.realToComplex β)) =
      CuspUniformization.exponentialPoint (CuspUniformization.exponential s)
        (CuspRetraction.realToComplex a +
          CuspUniformization.logarithmicPeriod D s *ᵥ CuspRetraction.realToComplex β) := by
  unfold CuspRetraction.changeTwist CuspRetraction.correction
  rw [CuspUniformization.time_exponentialPoint (CuspUniformization.exponential_ne_zero s),
    position_markedExponentialPoint C s hlog.ne,
    ToricSpace.inverseDisplacement_displacement C hlog hR,
    expFibreAction_exponentialPoint _ (CuspUniformization.exponential_ne_zero s)]
  congr 1
  simp only [CuspUniformization.logarithmicPeriod, Matrix.add_mulVec, Matrix.sub_mulVec]
  abel

private theorem CuspBoundaryTopVanishing.baseTorusProjection_centralProject
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (x : CuspRetraction.CentralFibre) :
    CuspCentralHomology.baseTorusProjection C r hr (CuspCollapse.centralProject C r hr x) =
      CuspCentralHomology.baseTorusPoint
        ((CuspHoneycomb.honeycombHomeomorph (C 0)).symm (CuspCollapse.centralModulus x)) := by
  obtain ⟨p, rfl⟩ := CuspHoneycomb.honeycombPolarMap_surjective (C 0) x
  change
    CuspCentralHomology.baseTorusProjection C r hr (CuspHoneycomb.honeycombCollapseMap C r hr p) =
      CuspCentralHomology.baseTorusPoint
        ((CuspHoneycomb.honeycombHomeomorph (C 0)).symm
          (CuspCollapse.centralModulus
            (CuspCollapse.centralPolarMap (CuspHoneycomb.phaseCoordinatesHomeomorph (C 0) p))))
  rw [CuspCentralHomology.baseTorusProjection_honeycombCollapseMap,
    CuspCollapse.centralModulus_centralPolarMap]
  exact
    congrArg CuspCentralHomology.baseTorusPoint
      ((CuspHoneycomb.honeycombHomeomorph (C 0)).symm_apply_apply p.2).symm

private theorem CuspBoundaryTopVanishing.position_modulus {x : ToricSpace.Space}
    (hx : ToricSpace.time x ≠ 0) :
    ToricSpace.position (ToricSpace.modulus x) = ToricSpace.position x := by
  ext i
  simp only [ToricSpace.position, ToricSpace.time_modulus, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), ToricSpace.logCoordinates, ToricSpace.logNorm,
    CuspSpecialization.torusCoordinates_modulus ((ToricSpace.mem_openTorus_iff x).mpr hx),
    ToricCharts.coordinateModulus_apply]

private theorem CuspBoundaryTopVanishing.normalizedPosition_modulus (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x ≠ 0) :
    CuspControlledRetraction.normalizedPosition C₀ (ToricSpace.modulus x) =
      CuspControlledRetraction.normalizedPosition C₀ x := by
  simp only [CuspControlledRetraction.normalizedPosition, ToricSpace.time_modulus,
    position_modulus hx, CuspControlledRetraction.inverseDisplacement_positiveTwist_norm]

private theorem CuspBoundaryTopVanishing.baseTorusProjection_prescribedCollapse
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (η : ℝ)
    (x : CuspControlledRetraction.PuncturedClosedTube η) :
    CuspCentralHomology.baseTorusProjection C r hr
        (CuspCollapse.centralProject C r hr
          (CuspControlledRetraction.prescribedCollapse (C 0) η x)) =
      CuspCentralHomology.baseTorusPoint
        (CuspControlledRetraction.normalizedPosition (C 0) (x.1 : ToricSpace.Space)) := by
  rw [baseTorusProjection_centralProject, CuspControlledRetraction.prescribedCollapse_modulus]
  change
    CuspCentralHomology.baseTorusPoint
        ((CuspHoneycomb.honeycombHomeomorph (C 0)).symm
          (CuspHoneycomb.honeycombHomeomorph (C 0)
            (CuspControlledRetraction.normalizedPosition (C 0)
              (((CuspControlledRetraction.puncturedPolarHomeomorph η).symm x).2.1.1 :
                ToricSpace.Space)))) =
      _
  rw [Homeomorph.symm_apply_apply,
    CuspControlledRetraction.puncturedPolarHomeomorph_symm_positive_coe]
  change
    CuspCentralHomology.baseTorusPoint
        (CuspControlledRetraction.normalizedPosition (C 0)
          (ToricSpace.modulus (x.1 : ToricSpace.Space))) =
      _
  rw [normalizedPosition_modulus (C 0) x.2]

private theorem CuspBoundaryTopVanishing.inverseDisplacement_positiveTwist_frozen
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    ToricSpace.inverseDisplacement (CuspPositive.positiveTwist (C 0)) t =
      ToricSpace.inverseDisplacement (CuspRetraction.frozen C) t := by
  unfold ToricSpace.inverseDisplacement ToricSpace.displacementMatrix
  rw [CuspPositive.driftMatrix_positiveTwist]
  rfl

private theorem CuspBoundaryTopVanishing.normalizedPosition_changeTwist_markedPoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ)
    (hlog : Real.log ‖CuspUniformization.exponential s‖ < 0)
    (hRC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4)
    (hR0 :
      ToricSpace.entryNorm
          (ToricSpace.driftMatrix (CuspRetraction.frozen C) (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4)
    (a β : (CuspHoneycombTiling.Plane)) :
    CuspControlledRetraction.normalizedPosition (C 0)
        (CuspRetraction.changeTwist C (CuspRetraction.frozen C)
          (CuspUniformization.exponentialPoint (CuspUniformization.exponential s)
            (CuspRetraction.realToComplex a +
              CuspUniformization.logarithmicPeriod C s *ᵥ CuspRetraction.realToComplex β))) =
      ToricSpace.realCuspVector β := by
  rw [CuspSpecialization.changeTwist_markedExponentialPoint C (CuspRetraction.frozen C) s hlog
      hRC,
    CuspControlledRetraction.normalizedPosition,
    CuspUniformization.time_exponentialPoint (CuspUniformization.exponential_ne_zero s),
    CuspSpecialization.position_markedExponentialPoint (CuspRetraction.frozen C) s hlog.ne,
    inverseDisplacement_positiveTwist_frozen,
    ToricSpace.inverseDisplacement_displacement (CuspRetraction.frozen C) hlog hR0]

private def CuspBoundaryTopVanishing.markedPointPunctured (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (s : ℂ) (hη : ‖CuspUniformization.exponential s‖ ≤ η) (a β : (CuspHoneycombTiling.Plane)) :
    CuspControlledRetraction.PuncturedClosedTube η :=
  ⟨⟨CuspUniformization.exponentialPoint (CuspUniformization.exponential s)
        (CuspRetraction.realToComplex a +
          CuspUniformization.logarithmicPeriod C s *ᵥ CuspRetraction.realToComplex β),
      by
      rw [CuspUniformization.time_exponentialPoint (CuspUniformization.exponential_ne_zero s)]
      exact hη⟩,
    by
    change
      ToricSpace.time (CuspUniformization.exponentialPoint (CuspUniformization.exponential s) _) ≠
        0
    rw [CuspUniformization.time_exponentialPoint (CuspUniformization.exponential_ne_zero s)]
    exact CuspUniformization.exponential_ne_zero s⟩

private theorem CuspBoundaryTopVanishing.baseTorusProjection_straightened_markedPoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (η : ℝ) (s : ℂ)
    (hη : ‖CuspUniformization.exponential s‖ ≤ η)
    (hlog : Real.log ‖CuspUniformization.exponential s‖ < 0)
    (hRC :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4)
    (hR0 :
      ToricSpace.entryNorm
          (ToricSpace.driftMatrix (CuspRetraction.frozen C) (CuspUniformization.exponential s)) ≤
        -Real.log ‖CuspUniformization.exponential s‖ / 4)
    (a β : (CuspHoneycombTiling.Plane)) :
    CuspCentralHomology.baseTorusProjection C r hr
        (CuspCollapse.centralProject C r hr
          (CuspControlledRetraction.straightenedPrescribedCollapse C η
            (markedPointPunctured C η s hη a β))) =
      PeriodTorusHigherHomology.coordinateProjection 2 β := by
  rw [CuspControlledRetraction.straightenedPrescribedCollapse, Function.comp_apply,
    baseTorusProjection_prescribedCollapse]
  change
    CuspCentralHomology.baseTorusPoint
        (CuspControlledRetraction.normalizedPosition (C 0)
          (CuspRetraction.changeTwist C (CuspRetraction.frozen C)
            (CuspUniformization.exponentialPoint (CuspUniformization.exponential s)
              (CuspRetraction.realToComplex a +
                CuspUniformization.logarithmicPeriod C s *ᵥ CuspRetraction.realToComplex β)))) =
      _
  rw [normalizedPosition_changeTwist_markedPoint C s hlog hRC hR0,
    CuspCentralHomology.baseTorusPoint_realCuspVector]

private theorem CuspBoundaryTopVanishing.periodEquiv_split (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) (x : RealPlane₄) :
    D.periods.periodEquiv s x =
      CuspRetraction.realToComplex ![x 2, x 3] +
        CuspUniformization.logarithmicPeriod D.correction (s : ℂ) *ᵥ
          CuspRetraction.realToComplex ![x 0, x 1] := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates, ← D.point_leftBlock s]
  ext i
  fin_cases i <;>
      simp [SpecialPeriods.CuspFamily.Data.periods_point, PeriodPoint.leftBlock,
        CuspRetraction.realToComplex, dotProduct, Fin.sum_univ_two] <;>
    ring

private def CuspBoundaryTopVanishing.periodLogCover (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) (x : RealPlane₄) :
    CuspUniformization.LogCover D.radius :=
  ⟨((s : ℂ), D.periods.periodEquiv s x), s.2⟩

private def
    CuspBoundaryTopVanishing.periodPointPunctured (D : SpecialPeriods.CuspFamily.Data) (η : ℝ)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius)
    (hη : ‖CuspUniformization.exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄) :
    CuspControlledRetraction.PuncturedClosedTube η :=
  ⟨⟨CuspUniformization.totalExponentialPoint (periodLogCover D s x),
      by
      rw [CuspUniformization.time_totalExponentialPoint]
      exact hη⟩,
    by
    change ToricSpace.time (CuspUniformization.totalExponentialPoint (periodLogCover D s x)) ≠ 0
    rw [CuspUniformization.time_totalExponentialPoint]
    exact CuspUniformization.exponential_ne_zero (s : ℂ)⟩

@[simp]
private theorem
    CuspBoundaryTopVanishing.periodPointPunctured_coe (D : SpecialPeriods.CuspFamily.Data)
    (η : ℝ) (s : SpecialPeriods.CuspFamily.LogBase D.radius)
    (hη : ‖CuspUniformization.exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄) :
    ((periodPointPunctured D η s hη x).1 : ToricSpace.Space) =
      CuspUniformization.totalExponentialPoint (periodLogCover D s x) :=
  rfl

private theorem CuspBoundaryTopVanishing.periodPointPunctured_quotient
    (D : SpecialPeriods.CuspFamily.Data) (η : ℝ) (hηr : η < D.radius)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius)
    (hη : ‖CuspUniformization.exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄) :
    (CuspRetraction.closedQuotientMap D.correction hηr (periodPointPunctured D η s hη x).1).1 =
      (CuspUniformization.puncturedCuspCover D.correction D.radius (periodLogCover D s x)).1 :=
  rfl

private theorem CuspBoundaryTopVanishing.periodPointPunctured_eq_markedPoint
    (D : SpecialPeriods.CuspFamily.Data) (η : ℝ) (s : SpecialPeriods.CuspFamily.LogBase D.radius)
    (hη : ‖CuspUniformization.exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄) :
    periodPointPunctured D η s hη x =
      markedPointPunctured D.correction η (s : ℂ) hη ![x 2, x 3] ![x 0, x 1] := by
  apply Subtype.ext
  apply Subtype.ext
  change
    CuspUniformization.exponentialPoint (CuspUniformization.exponential (s : ℂ))
        (D.periods.periodEquiv s x) =
      _
  rw [periodEquiv_split]
  rfl

private theorem CuspBoundaryTopVanishing.baseTorusProjection_straightened_periodPoint
    (D : SpecialPeriods.CuspFamily.Data) (η : ℝ) (s : SpecialPeriods.CuspFamily.LogBase D.radius)
    (hη : ‖CuspUniformization.exponential (s : ℂ)‖ ≤ η)
    (hR0 :
      ToricSpace.entryNorm
          (ToricSpace.driftMatrix (CuspRetraction.frozen D.correction)
            (CuspUniformization.exponential (s : ℂ))) ≤
        -Real.log ‖CuspUniformization.exponential (s : ℂ)‖ / 4)
    (x : RealPlane₄) :
    CuspCentralHomology.baseTorusProjection D.correction D.radius D.radius_pos
        (CuspCollapse.centralProject D.correction D.radius D.radius_pos
          (CuspControlledRetraction.straightenedPrescribedCollapse D.correction η
            (periodPointPunctured D η s hη x))) =
      PeriodTorusHigherHomology.coordinateProjection 2 ![x 0, x 1] := by
  rw [periodPointPunctured_eq_markedPoint]
  exact
    baseTorusProjection_straightened_markedPoint D.correction D.radius D.radius_pos η s hη
      (D.logarithmic_height s) (D.logarithmic_drift s) hR0 ![x 2, x 3] ![x 0, x 1]

private theorem CuspBoundaryTopVanishing.baseTorusProjection_straightened_periodPoint_of_smallDrift
    (D : SpecialPeriods.CuspFamily.Data) (δ : ℝ)
    (hR0 : ToricSpace.SmallDrift (CuspRetraction.frozen D.correction) δ) (η : ℝ)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius)
    (hδ : ‖CuspUniformization.exponential (s : ℂ)‖ < δ)
    (hη : ‖CuspUniformization.exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄) :
    CuspCentralHomology.baseTorusProjection D.correction D.radius D.radius_pos
        (CuspCollapse.centralProject D.correction D.radius D.radius_pos
          (CuspControlledRetraction.straightenedPrescribedCollapse D.correction η
            (periodPointPunctured D η s hη x))) =
      PeriodTorusHigherHomology.coordinateProjection 2 ![x 0, x 1] :=
  baseTorusProjection_straightened_periodPoint D η s hη
    (hR0 _ (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero _)) hδ) x

private theorem
    CuspBoundaryTopVanishing.exists_period_base_radius (D : SpecialPeriods.CuspFamily.Data) :
    ∃ δ : ℝ,
      0 < δ ∧
        δ < D.radius ∧
          δ < 1 ∧
            ∀ (η : ℝ) (s : SpecialPeriods.CuspFamily.LogBase D.radius),
              ‖CuspUniformization.exponential (s : ℂ)‖ < δ →
                ∀ (hη : ‖CuspUniformization.exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄),
                  CuspCentralHomology.baseTorusProjection D.correction D.radius D.radius_pos
                      (CuspCollapse.centralProject D.correction D.radius D.radius_pos
                        (CuspControlledRetraction.straightenedPrescribedCollapse D.correction η
                          (periodPointPunctured D η s hη x))) =
                    PeriodTorusHigherHomology.coordinateProjection 2 ![x 0, x 1] := by
  obtain ⟨δ, hδ, hδr, hδ1, _, hR0⟩ :=
    CuspRetraction.exists_common_frozen_radius D.correction D.radius_pos
      (fun i j => (D.holomorphic i j).continuousOn)
  exact
    ⟨δ, hδ, hδr, hδ1, fun η s hs hη x =>
      baseTorusProjection_straightened_periodPoint_of_smallDrift D δ hR0 η s hs hη x⟩

private abbrev
    CuspBoundaryTopVanishingCircle.NormCircle (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r ρ : ℝ) :=
  { q : CuspQuotient.QuotientSpace C r // ‖CuspQuotient.projection C r q‖ = ρ }

private def CuspBoundaryTopVanishingCircle.normCircleIntoClosed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r η ρ : ℝ) (hρη : ρ ≤ η) : C(NormCircle C r ρ, CuspRetraction.ClosedQuotient C r η)
    where
  toFun q := ⟨q.1, q.2.trans_le hρη⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private theorem CuspBoundaryTopVanishingCircle.normCircle_projection_ne_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r ρ : ℝ) (hρ : 0 < ρ) (q : NormCircle C r ρ) :
    CuspQuotient.projection C r q ≠ 0 := by
  apply norm_pos_iff.mp
  rw [q.2]
  exact hρ

private def
    CuspBoundaryTopVanishingCircle.prescribedCircleCollapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (η ρ : ℝ) (hρ : 0 < ρ) (hρη : ρ ≤ η) (hηr : η < r)
    (q : NormCircle C r ρ) : CuspRetraction.QuotientCentralFibre C r :=
  CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr
    (CuspQuotient.projection C r q) (normCircle_projection_ne_zero C r ρ hρ q) (q.2.trans_le hρη)
    ⟨q.1, rfl⟩

private def
    CuspBoundaryTopVanishingCircle.HasPrescribedCircleEndpoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) (η ρ : ℝ)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r)) :
    Prop :=
  ∀ (hηr : η < r) (x : CuspControlledRetraction.PuncturedClosedTube η),
    ‖ToricSpace.time (x.1 : ToricSpace.Space)‖ = ρ →
      R (CuspRetraction.closedQuotientMap C hηr x.1) =
        CuspCollapse.centralProject C r hr
          (CuspControlledRetraction.straightenedPrescribedCollapse C η x)

private theorem CuspBoundaryTopVanishingCircle.controlledRetraction_actualFibre_eq
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (η ρ : ℝ) (hρη : ρ ≤ η) (hηr : η < r)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hEnd : HasPrescribedCircleEndpoint C r hr η ρ R) (t : ℂ) (ht : t ≠ 0) (hnorm : ‖t‖ = ρ)
    (q : CuspControlledRetraction.ActualQuotientFibre C r t) :
    R
        ((CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t (hnorm.trans_le hρη)).symm
            q).1 =
      CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht (hnorm.trans_le hρη)
        q := by
  have he :=
    CuspControlledRetraction.prescribedFibreCollapse_eq_of_endpoint C r hr hηr t ht R
      (fun x hx => hEnd hηr x (hx.trans hnorm))
  exact
    congrFun he
      ((CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t (hnorm.trans_le hρη)).symm
        q)

private theorem CuspBoundaryTopVanishingCircle.controlledRetraction_normCircle_eq
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (η ρ : ℝ) (hρ : 0 < ρ) (hρη : ρ ≤ η)
    (hηr : η < r)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hEnd : HasPrescribedCircleEndpoint C r hr η ρ R) (q : NormCircle C r ρ) :
    R (normCircleIntoClosed C r η ρ hρη q) = prescribedCircleCollapse C r hr η ρ hρ hρη hηr q :=
  controlledRetraction_actualFibre_eq C r hr η ρ hρη hηr R hEnd (CuspQuotient.projection C r q)
    (normCircle_projection_ne_zero C r ρ hρ q) q.2 ⟨q.1, rfl⟩

private theorem CuspBoundaryTopVanishingCircle.prescribedCircleCollapse_continuous_of_endpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (η ρ : ℝ) (hρ : 0 < ρ) (hρη : ρ ≤ η)
    (hηr : η < r)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hEnd : HasPrescribedCircleEndpoint C r hr η ρ R) :
    Continuous (prescribedCircleCollapse C r hr η ρ hρ hρη hηr) := by
  have he :
    (fun q => R (normCircleIntoClosed C r η ρ hρη q)) =
      prescribedCircleCollapse C r hr η ρ hρ hρη hηr :=
    funext (controlledRetraction_normCircle_eq C r hr η ρ hρ hρη hηr R hEnd)
  rw [← he]
  exact R.continuous.comp (normCircleIntoClosed C r η ρ hρη).continuous

private theorem
    CuspBoundaryTopVanishingCircle.prescribedActualFibreCollapse_continuous_of_circle_endpoint
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (η ρ : ℝ) (hρη : ρ ≤ η) (hηr : η < r)
    (R : C(CuspRetraction.ClosedQuotient C r η, CuspRetraction.QuotientCentralFibre C r))
    (hEnd : HasPrescribedCircleEndpoint C r hr η ρ R) (t : ℂ) (ht : t ≠ 0) (hnorm : ‖t‖ = ρ) :
    Continuous
      (CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht
        (hnorm.trans_le hρη)) := by
  have he :
    (fun q : CuspControlledRetraction.ActualQuotientFibre C r t =>
        R
          ((CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t
                  (hnorm.trans_le hρη)).symm
              q).1) =
      CuspControlledRetraction.prescribedActualFibreCollapse C r hr hηr t ht
        (hnorm.trans_le hρη) :=
    funext (controlledRetraction_actualFibre_eq C r hr η ρ hρη hηr R hEnd t ht hnorm)
  rw [← he]
  exact
    (R.continuous.comp continuous_subtype_val).comp
      (CuspControlledRetraction.quotientLevelFibreHomeomorph C r η t
          (hnorm.trans_le hρη)).symm.continuous

private theorem CuspBoundaryTopVanishingCircle.exists_controlled_circle_retraction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ} (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 r)) :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        η₀ < r ∧
          η₀ < 1 ∧
            ∀ (η : ℝ) (hη : 0 < η),
              η ≤ η₀ →
                ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρη : ρ ≤ η),
                  ∃ R :
                    C(CuspRetraction.ClosedQuotient C r η,
                      CuspRetraction.QuotientCentralFibre C r),
                    R.comp (CuspRetraction.quotientCentralIntoClosed C r η hη.le) =
                        ContinuousMap.id (CuspRetraction.QuotientCentralFibre C r) ∧
                      ∃ H :
                        (ContinuousMap.id (CuspRetraction.ClosedQuotient C r η)).HomotopyRel
                          ((CuspRetraction.quotientCentralIntoClosed C r η hη.le).comp R)
                          {q : CuspRetraction.ClosedQuotient C r η |
                            CuspQuotient.projection C r q = 0},
                        (∀ s q,
                            ‖CuspQuotient.projection C r (H (s, q))‖ ≤
                              ‖CuspQuotient.projection C r q‖) ∧
                          HasPrescribedCircleEndpoint C r hr η ρ R ∧
                            ∀ hηr : η < r,
                              Continuous (prescribedCircleCollapse C r hr η ρ hρ hρη hηr) ∧
                                (∀ q : NormCircle C r ρ,
                                    R (normCircleIntoClosed C r η ρ hρη q) =
                                      prescribedCircleCollapse C r hr η ρ hρ hρη hηr q) ∧
                                  ∀ (t : ℂ) (ht : t ≠ 0) (hnorm : ‖t‖ = ρ),
                                    Continuous
                                        (CuspControlledRetraction.prescribedActualFibreCollapse C
                                          r hr hηr t ht (hnorm.trans_le hρη)) ∧
                                      ∀ q : CuspControlledRetraction.ActualQuotientFibre C r t,
                                        R
                                            ((CuspControlledRetraction.quotientLevelFibreHomeomorph
                                                    C r η t (hnorm.trans_le hρη)).symm
                                                q).1 =
                                          CuspControlledRetraction.prescribedActualFibreCollapse C
                                            r hr hηr t ht (hnorm.trans_le hρη) q := by
  obtain ⟨η₀, hη₀, hη₀r, hη₀1, hret⟩ :=
    CuspControlledRetraction.exists_closed_quotient_controlled_strongDeformationRetraction C hr hC
  refine ⟨η₀, hη₀, hη₀r, hη₀1, ?_⟩
  intro η hη hηη₀ ρ hρ hρη
  obtain ⟨R, hR, H, hmono, hEnd⟩ := hret η hη hηη₀ ρ hρ hρη
  refine ⟨R, hR, H, hmono, hEnd, ?_⟩
  intro hηr
  refine
    ⟨prescribedCircleCollapse_continuous_of_endpoint C r hr η ρ hρ hρη hηr R hEnd,
      controlledRetraction_normCircle_eq C r hr η ρ hρ hρη hηr R hEnd, ?_⟩
  intro t ht hnorm
  exact
    ⟨prescribedActualFibreCollapse_continuous_of_circle_endpoint C r hr η ρ hρη hηr R hEnd t ht
        hnorm,
      controlledRetraction_actualFibre_eq C r hr η ρ hρη hηr R hEnd t ht hnorm⟩

private def CuspBoundaryGammaZero.restrictedMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; 1, 1, 0; 0, 0, 1]

private def CuspBoundaryGammaZero.restrictedInverseMatrix : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, 0; -1, 1, 0; 0, 0, 1]

@[simp]
private theorem CuspBoundaryGammaZero.restrictedMatrix_det : restrictedMatrix.det = 1 := by decide

private theorem CuspBoundaryGammaZero.restrictedInverseMatrix_mul :
    restrictedInverseMatrix * restrictedMatrix = 1 := by decide

private theorem CuspBoundaryGammaZero.restrictedMatrix_mul_inverse :
    restrictedMatrix * restrictedInverseMatrix = 1 := by decide

private def CuspBoundaryGammaZero.restrictedMonodromy :
    PeriodTorusHigherHomology.ProductTorus 3 ≃ₜ PeriodTorusHigherHomology.ProductTorus 3 :=
  Elliptic.HigherHomology.matrixTorusHomeomorph restrictedMatrix restrictedInverseMatrix
    restrictedInverseMatrix_mul restrictedMatrix_mul_inverse

@[simp]
private theorem CuspBoundaryGammaZero.restrictedMonodromy_apply
    (y : PeriodTorusHigherHomology.ProductTorus 3) :
    restrictedMonodromy y = PeriodTorusHigherHomology.torusMatrixMap restrictedMatrix y :=
  rfl

private theorem CuspBoundaryGammaZero.restrictedMatrix_real_apply (x : Fin 3 → ℝ) :
    restrictedMatrix.map (Int.castRingHom ℝ) *ᵥ x = ![x 0, x 0 + x 1, x 2] := by
  ext i
  fin_cases i <;> simp [restrictedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

private theorem CuspBoundaryGammaZero.restrictedMonodromy_coordinateProjection (x : Fin 3 → ℝ) :
    restrictedMonodromy (PeriodTorusHigherHomology.coordinateProjection 3 x) =
      PeriodTorusHigherHomology.coordinateProjection 3 ![x 0, x 0 + x 1, x 2] := by
  rw [restrictedMonodromy_apply, PeriodTorusHigherHomology.torusMatrixMap_coordinateProjection,
    restrictedMatrix_real_apply]

private def
    CuspBoundaryGammaZero.fibreMap : C(PeriodTorusHigherHomology.ProductTorus 3, RealTorus₄) :=
  PeriodFamily.GammaZero.fibreInclusion.comp
    (PeriodFamily.GammaZero.fibreHomeomorph.symm :
      C(PeriodTorusHigherHomology.ProductTorus 3, PeriodFamily.GammaZero.Fibre))

@[simp]
private theorem CuspBoundaryGammaZero.fibreMap_coordinateProjection (x : Fin 3 → ℝ) :
    fibreMap (PeriodTorusHigherHomology.coordinateProjection 3 x) =
      standardLattice.mkQ (Fin.cons 0 x) :=
  PeriodFamily.GammaZero.fibreHomeomorph_symm_coordinateProjection x

@[simp]
private theorem
    CuspBoundaryGammaZero.fibreMap_gamma (y : PeriodTorusHigherHomology.ProductTorus 3) :
    PeriodFamily.GammaZero.fibreGamma (fibreMap y) = 0 :=
  (PeriodFamily.GammaZero.fibreHomeomorph.symm y).property

private theorem CuspBoundaryGammaZero.cuspRealEquiv_cons_zero (x : Fin 3 → ℝ) :
    SpecialPeriods.CuspFamily.cuspRealEquiv 1 (Fin.cons 0 x) =
      Fin.cons 0 ![x 0, x 0 + x 1, x 2] := by
  ext i
  fin_cases i <;> simp [SpecialPeriods.CuspFamily.cuspRealEquiv, add_comm] <;> rfl

private theorem
    CuspBoundaryGammaZero.fibreMap_monodromy (y : PeriodTorusHigherHomology.ProductTorus 3) :
    fibreMap (restrictedMonodromy y) = ThreefoldOverlapMappingTorus.Cusp.monodromy (fibreMap y) :=
  by
  obtain ⟨x, rfl⟩ := PeriodTorusHigherHomology.coordinateProjection_surjective 3 y
  rw [restrictedMonodromy_coordinateProjection, fibreMap_coordinateProjection,
    fibreMap_coordinateProjection]
  change
    standardLattice.mkQ (Fin.cons 0 ![x 0, x 0 + x 1, x 2]) =
      SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1 (standardLattice.mkQ (Fin.cons 0 x))
  rw [SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ, cuspRealEquiv_cons_zero]

public
theorem CuspBoundaryGammaZero.equivariant_zpow_mo1973_29887 {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y))
    (he : ∀ x, e (f x) = g (e x)) (n : ℤ) (x : X) : e ((f ^ n) x) = (g ^ n) (e x) := by
  have hinv (x : X) : e (f.symm x) = g.symm (e x) := by
    apply g.injective
    rw [← he, f.apply_symm_apply, g.apply_symm_apply]
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    simp only [zpow_add_one, Homeomorph.mul_apply]
    rw [ih, he]
  | pred n ih =>
    simp only [zpow_sub_one, Homeomorph.mul_apply, Homeomorph.inv_apply]
    rw [ih, hinv]

private def
    CuspBoundaryGammaZero.mappingTorusMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x)) :
    C(MappingTorus.Torus f, MappingTorus.Torus g)
    where
  toFun :=
    Quotient.lift (fun p : ℝ × X => MappingTorus.mk g (p.1, e p.2))
      (by
        rintro p q ⟨n, rfl⟩
        change
          MappingTorus.mk g (p.1, e p.2) = MappingTorus.mk g (p.1 + (n : ℝ), e ((f ^ (-n)) p.2))
        rw [equivariant_zpow_mo1973_29887 f g e he]
        exact (MappingTorus.mk_deck g n (p.1, e p.2)).symm)
  continuous_toFun :=
    ((MappingTorus.mk_continuous g).comp
          (continuous_fst.prodMk (e.continuous.comp continuous_snd))).quotient_lift
      _

@[simp]
private theorem CuspBoundaryGammaZero.mappingTorusMap_mk {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x))
    (t : ℝ) (x : X) :
    mappingTorusMap f g e he (MappingTorus.mk f (t, x)) = MappingTorus.mk g (t, e x) :=
  rfl

@[simp]
private theorem CuspBoundaryGammaZero.mappingTorusMap_base {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x))
    (q : MappingTorus.Torus f) :
    MappingTorus.base g (mappingTorusMap f g e he q) = MappingTorus.base f q := by
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective f q
  rfl

private abbrev CuspBoundaryGammaZero.Boundary :=
  MappingTorus.Torus restrictedMonodromy

private def
    CuspBoundaryGammaZero.boundaryMap : C(Boundary, ThreefoldOverlapMappingTorus.Cusp.Boundary) :=
  mappingTorusMap restrictedMonodromy ThreefoldOverlapMappingTorus.Cusp.monodromy fibreMap
    fibreMap_monodromy

@[simp]
private theorem CuspBoundaryGammaZero.boundaryMap_mk (t : ℝ)
    (y : PeriodTorusHigherHomology.ProductTorus 3) :
    boundaryMap (MappingTorus.mk restrictedMonodromy (t, y)) =
      MappingTorus.mk ThreefoldOverlapMappingTorus.Cusp.monodromy (t, fibreMap y) :=
  rfl

private def CuspBoundaryTopVanishing.gammaBoundaryToPunctured (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    C(CuspBoundaryGammaZero.Boundary,
      CuspUniformization.PuncturedQuotient D.correction D.radius) :=
  (ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion D h).comp CuspBoundaryGammaZero.boundaryMap

private def CuspBoundaryTopVanishing.gammaBoundaryToFull (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    C(CuspBoundaryGammaZero.Boundary, CuspQuotient.QuotientSpace D.correction D.radius) :=
  (⟨Subtype.val, continuous_subtype_val⟩ :
        C(CuspUniformization.PuncturedQuotient D.correction D.radius,
          CuspQuotient.QuotientSpace D.correction D.radius)).comp
    (gammaBoundaryToPunctured D h)

private theorem
    CuspBoundaryTopVanishing.gammaBoundaryToPunctured_mk (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (t : ℝ)
    (x : PeriodTorusHigherHomology.ProductTorus 3) :
    gammaBoundaryToPunctured D h
        (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy (t, x)) =
      ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder D h
        (t, CuspBoundaryGammaZero.fibreMap x) :=
  rfl

private theorem CuspBoundaryTopVanishing.gammaBoundaryToFull_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (t : ℝ) (x : Fin 3 → ℝ) :
    gammaBoundaryToFull D h
        (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy
          (t, PeriodTorusHigherHomology.coordinateProjection 3 x)) =
      (CuspUniformization.puncturedCuspCover D.correction D.radius
          ⟨((ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h : ℂ),
              D.periods.periodEquiv
                (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h)
                (Fin.cons 0 x)),
            (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t
                h).property⟩).val := by
  change
    (gammaBoundaryToPunctured D h
          (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy
            (t, PeriodTorusHigherHomology.coordinateProjection 3 x))).val =
      _
  rw [gammaBoundaryToPunctured_mk, CuspBoundaryGammaZero.fibreMap_coordinateProjection]
  exact
    congrArg Subtype.val
      (ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_realCoordinates D h t (Fin.cons 0 x))

private theorem
    CuspBoundaryTopVanishing.logPoint_exponential_norm (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (t : ℝ) :
    ‖CuspUniformization.exponential
          (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h : ℂ)‖ =
      ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ := by
  rw [ThreefoldHomologyCuspFibre.heightParameter_norm]
  calc
    _ =
        Real.exp
          (Real.log
            ‖CuspUniformization.exponential
                (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h : ℂ)‖) :=
      (Real.exp_log (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero _))).symm
    _ = _ := by
      rw [CuspUniformization.log_norm_exponential, ThreefoldOverlapMappingTorus.Cusp.logPoint_im]

private theorem CuspBoundaryTopVanishing.gammaBoundaryToFull_projection_norm
    (D : SpecialPeriods.CuspFamily.Data) (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (q : CuspBoundaryGammaZero.Boundary) :
    ‖CuspQuotient.projection D.correction D.radius (gammaBoundaryToFull D h q)‖ =
      ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ := by
  obtain ⟨⟨t, x⟩, rfl⟩ := MappingTorus.mk_surjective CuspBoundaryGammaZero.restrictedMonodromy q
  change
    ‖CuspQuotient.projection D.correction D.radius
          (gammaBoundaryToPunctured D h
            (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy (t, x)))‖ =
      _
  rw [gammaBoundaryToPunctured_mk, ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_base]
  exact logPoint_exponential_norm D h t

private def CuspBoundaryTopVanishing.gammaBoundaryToClosed (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (η : ℝ)
    (hη : ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ ≤ η) :
    C(CuspBoundaryGammaZero.Boundary, CuspRetraction.ClosedQuotient D.correction D.radius η)
    where
  toFun
    q :=
    ⟨gammaBoundaryToFull D h q,
      by
      rw [gammaBoundaryToFull_projection_norm]
      exact hη⟩
  continuous_toFun := (gammaBoundaryToFull D h).continuous.subtype_mk _

@[simp]
private theorem
    CuspBoundaryTopVanishing.gammaBoundaryToClosed_coe (D : SpecialPeriods.CuspFamily.Data)
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (η : ℝ)
    (hη : ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ ≤ η)
    (q : CuspBoundaryGammaZero.Boundary) :
    (gammaBoundaryToClosed D h η hη q).val = gammaBoundaryToFull D h q :=
  rfl

private def
    CuspBoundaryTopVanishing.gammaBoundaryHeightHomotopy (D : SpecialPeriods.CuspFamily.Data)
    (h₀ h₁ : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    (gammaBoundaryToFull D h₀).Homotopy (gammaBoundaryToFull D h₁)
    where
  toFun
    p :=
    ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
        (ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀ (p.1, h₁),
          CuspBoundaryGammaZero.boundaryMap p.2)).val
  continuous_toFun :=
    continuous_subtype_val.comp
      ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm.continuous.comp
        (((ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀).continuous.comp
              (continuous_fst.prodMk continuous_const)).prodMk
          (CuspBoundaryGammaZero.boundaryMap.continuous.comp continuous_snd)))
  map_zero_left
    q :=
    congrArg
      (fun h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius =>
        ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
            (h, CuspBoundaryGammaZero.boundaryMap q)).val)
      ((ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀).map_zero_left h₁)
  map_one_left
    q :=
    congrArg
      (fun h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius =>
        ((ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph D).symm
            (h, CuspBoundaryGammaZero.boundaryMap q)).val)
      ((ThreefoldOverlapMappingTorus.Cusp.heightContraction D.radius h₀).map_one_left h₁)

private theorem CuspBoundaryTopVanishing.gammaBoundaryToFull_homology_eq
    (D : SpecialPeriods.CuspFamily.Data)
    (h₀ h₁ : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (gammaBoundaryToFull D h₀) n =
      SingularMayerVietoris.singularHomologyMap (gammaBoundaryToFull D h₁) n :=
  PeriodTorusHigherHomology.homotopy_homologyMap (gammaBoundaryHeightHomotopy D h₀ h₁) n

private theorem CuspBoundaryTopVanishing.gammaBoundaryToFilling_eq :
    (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none).comp
        CuspBoundaryGammaZero.boundaryMap =
      gammaBoundaryToFull ThreefoldOverlapMappingTorus.Cusp.specialData
        ThreefoldOverlapMappingTorus.Cusp.specialHeight := by
  rw [ThreefoldOverlapMappingTorus.boundaryToFilling_cusp]
  rfl

private theorem CuspBoundaryTopVanishing.gammaBoundaryToClosed_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (η : ℝ) (hη : ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ ≤ η) (hηr : η < D.radius)
    (t : ℝ) (x : Fin 3 → ℝ) :
    gammaBoundaryToClosed D h η hη
        (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy
          (t, PeriodTorusHigherHomology.coordinateProjection 3 x)) =
      CuspRetraction.closedQuotientMap D.correction hηr
        (periodPointPunctured D η
            (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h)
            ((logPoint_exponential_norm D h t).trans_le hη) (Fin.cons 0 x)).1 := by
  apply Subtype.ext
  rw [gammaBoundaryToClosed_coe, periodPointPunctured_quotient]
  exact gammaBoundaryToFull_realCoordinates D h t x

private theorem CuspBoundaryTopVanishing.retraction_gammaBoundaryToClosed_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (η : ℝ) (hη : ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ ≤ η) (hηr : η < D.radius)
    (R :
      C(CuspRetraction.ClosedQuotient D.correction D.radius η,
        CuspRetraction.QuotientCentralFibre D.correction D.radius))
    (hEnd :
      CuspBoundaryTopVanishingCircle.HasPrescribedCircleEndpoint D.correction D.radius
        D.radius_pos η ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ R)
    (t : ℝ) (x : Fin 3 → ℝ) :
    R
        (gammaBoundaryToClosed D h η hη
          (MappingTorus.mk CuspBoundaryGammaZero.restrictedMonodromy
            (t, PeriodTorusHigherHomology.coordinateProjection 3 x))) =
      CuspCollapse.centralProject D.correction D.radius D.radius_pos
        (CuspControlledRetraction.straightenedPrescribedCollapse D.correction η
          (periodPointPunctured D η
            (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h)
            ((logPoint_exponential_norm D h t).trans_le hη) (Fin.cons 0 x))) := by
  rw [gammaBoundaryToClosed_realCoordinates D h η hη hηr]
  apply hEnd hηr
  rw [periodPointPunctured_coe, CuspUniformization.time_totalExponentialPoint]
  exact logPoint_exponential_norm D h t

private theorem CuspBoundaryTopVanishing.retraction_gammaBoundary_base_zero
    (D : SpecialPeriods.CuspFamily.Data) (δ : ℝ)
    (hbase :
      ∀ (η : ℝ) (s : SpecialPeriods.CuspFamily.LogBase D.radius),
        ‖CuspUniformization.exponential (s : ℂ)‖ < δ →
          ∀ (hη : ‖CuspUniformization.exponential (s : ℂ)‖ ≤ η) (x : RealPlane₄),
            CuspCentralHomology.baseTorusProjection D.correction D.radius D.radius_pos
                (CuspCollapse.centralProject D.correction D.radius D.radius_pos
                  (CuspControlledRetraction.straightenedPrescribedCollapse D.correction η
                    (periodPointPunctured D η s hη x))) =
              PeriodTorusHigherHomology.coordinateProjection 2 ![x 0, x 1])
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) (η : ℝ)
    (hη : ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ ≤ η) (hηr : η < D.radius)
    (hδ : ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ < δ)
    (R :
      C(CuspRetraction.ClosedQuotient D.correction D.radius η,
        CuspRetraction.QuotientCentralFibre D.correction D.radius))
    (hEnd :
      CuspBoundaryTopVanishingCircle.HasPrescribedCircleEndpoint D.correction D.radius
        D.radius_pos η ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ R)
    (q : CuspBoundaryGammaZero.Boundary) :
    CuspCentralHomology.baseTorusProjection D.correction D.radius D.radius_pos
        (R (gammaBoundaryToClosed D h η hη q)) 0 =
      0 := by
  obtain ⟨⟨t, y⟩, rfl⟩ := MappingTorus.mk_surjective CuspBoundaryGammaZero.restrictedMonodromy q
  obtain ⟨x, rfl⟩ := PeriodTorusHigherHomology.coordinateProjection_surjective 3 y
  rw [retraction_gammaBoundaryToClosed_realCoordinates D h η hη hηr R hEnd]
  have hb :=
    hbase η (ThreefoldOverlapMappingTorus.Cusp.logPoint D.radius D.radius_pos t h)
      ((logPoint_exponential_norm D h t).trans_lt hδ)
      ((logPoint_exponential_norm D h t).trans_le hη) (Fin.cons 0 x)
  simpa using congrFun hb (0 : Fin 2)

private def
    CuspBoundaryTopVanishing.gammaBoundaryCentralHomotopy (D : SpecialPeriods.CuspFamily.Data)
    (η : ℝ) (hη₀ : 0 ≤ η)
    (R :
      C(CuspRetraction.ClosedQuotient D.correction D.radius η,
        CuspRetraction.QuotientCentralFibre D.correction D.radius))
    (H :
      (ContinuousMap.id (CuspRetraction.ClosedQuotient D.correction D.radius η)).Homotopy
        ((CuspRetraction.quotientCentralIntoClosed D.correction D.radius η hη₀).comp R))
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (hη : ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ ≤ η) :
    (gammaBoundaryToFull D h).Homotopy
      ((ThreefoldHomologyFinitenessCusp.fullCentralInclusion D).comp
        (R.comp (gammaBoundaryToClosed D h η hη)))
    where
  toFun p := (H (p.1, gammaBoundaryToClosed D h η hη p.2)).val
  continuous_toFun :=
    continuous_subtype_val.comp
      (H.continuous.comp
        (continuous_fst.prodMk ((gammaBoundaryToClosed D h η hη).continuous.comp continuous_snd)))
  map_zero_left q := congrArg Subtype.val (H.map_zero_left (gammaBoundaryToClosed D h η hη q))
  map_one_left q := congrArg Subtype.val (H.map_one_left (gammaBoundaryToClosed D h η hη q))

private theorem CuspBoundaryTopVanishing.gammaBoundaryToFull_homology_eq_central
    (D : SpecialPeriods.CuspFamily.Data) (η : ℝ) (hη₀ : 0 ≤ η)
    (R :
      C(CuspRetraction.ClosedQuotient D.correction D.radius η,
        CuspRetraction.QuotientCentralFibre D.correction D.radius))
    (H :
      (ContinuousMap.id (CuspRetraction.ClosedQuotient D.correction D.radius η)).Homotopy
        ((CuspRetraction.quotientCentralIntoClosed D.correction D.radius η hη₀).comp R))
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (hη : ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ ≤ η) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (gammaBoundaryToFull D h) n =
      (SingularMayerVietoris.singularHomologyMap
            (ThreefoldHomologyFinitenessCusp.fullCentralInclusion D) n).comp
        (SingularMayerVietoris.singularHomologyMap (R.comp (gammaBoundaryToClosed D h η hη)) n) :=
  by
  rw [PeriodTorusHigherHomology.homotopy_homologyMap
      (gammaBoundaryCentralHomotopy D η hη₀ R H h hη) n,
    PeriodTorusHigherHomology.singularHomologyMap_comp]

private theorem CuspBoundaryTopVanishing.gammaBoundaryToFull_homology_eq_zero_of_retraction
    (D : SpecialPeriods.CuspFamily.Data) (η : ℝ) (hη₀ : 0 ≤ η)
    (R :
      C(CuspRetraction.ClosedQuotient D.correction D.radius η,
        CuspRetraction.QuotientCentralFibre D.correction D.radius))
    (H :
      (ContinuousMap.id (CuspRetraction.ClosedQuotient D.correction D.radius η)).Homotopy
        ((CuspRetraction.quotientCentralIntoClosed D.correction D.radius η hη₀).comp R))
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (hη : ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ ≤ η) (n : ℕ)
    (hzero :
      SingularMayerVietoris.singularHomologyMap (R.comp (gammaBoundaryToClosed D h η hη)) n = 0) :
    SingularMayerVietoris.singularHomologyMap (gammaBoundaryToFull D h) n = 0 := by
  rw [gammaBoundaryToFull_homology_eq_central D η hη₀ R H h hη n, hzero, LinearMap.comp_zero]

private theorem CuspBoundaryTopVanishing.gammaBoundaryToFull_homologyFour_eq_zero_of_retraction
    (D : SpecialPeriods.CuspFamily.Data) (η : ℝ) (hη₀ : 0 ≤ η)
    (R :
      C(CuspRetraction.ClosedQuotient D.correction D.radius η,
        CuspRetraction.QuotientCentralFibre D.correction D.radius))
    (H :
      (ContinuousMap.id (CuspRetraction.ClosedQuotient D.correction D.radius η)).Homotopy
        ((CuspRetraction.quotientCentralIntoClosed D.correction D.radius η hη₀).comp R))
    (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius)
    (hη : ‖ThreefoldHomologyCuspFibre.heightParameter D h‖ ≤ η)
    (hzero :
      SingularMayerVietoris.singularHomologyMap (R.comp (gammaBoundaryToClosed D h η hη)) 4 = 0) :
    SingularMayerVietoris.singularHomologyMap (gammaBoundaryToFull D h) 4 = 0 :=
  gammaBoundaryToFull_homology_eq_zero_of_retraction D η hη₀ R H h hη 4 hzero

private theorem CuspBoundaryTopVanishing.gammaBoundaryToFull_homologyFour_eq_zero
    (D : SpecialPeriods.CuspFamily.Data) (h : ThreefoldOverlapMappingTorus.Cusp.Height D.radius) :
    SingularMayerVietoris.singularHomologyMap (gammaBoundaryToFull D h) 4 = 0 := by
  obtain ⟨δ, hδ, _hδr, _hδ1, hbase⟩ := exists_period_base_radius D
  obtain ⟨η₀, hη₀, hη₀r, _hη₀1, hret⟩ :=
    CuspBoundaryTopVanishingCircle.exists_controlled_circle_retraction D.correction D.radius_pos
      D.holomorphic
  let η := Min.min η₀ δ
  have hη : 0 < η := lt_min hη₀ hδ
  have hηr : η < D.radius := (min_le_left η₀ δ).trans_lt hη₀r
  obtain ⟨h', hh'⟩ := ThreefoldHomologyCuspFibre.exists_smallHeight D hη
  have hρ : 0 < ‖ThreefoldHomologyCuspFibre.heightParameter D h'‖ :=
    norm_pos_iff.mpr (ThreefoldHomologyCuspFibre.heightParameter_ne_zero D h')
  obtain ⟨R, _hR, H, _hmono, hEnd, _hall⟩ :=
    hret η hη (min_le_left η₀ δ) ‖ThreefoldHomologyCuspFibre.heightParameter D h'‖ hρ hh'.le
  have hzero :
    SingularMayerVietoris.singularHomologyMap (R.comp (gammaBoundaryToClosed D h' η hh'.le)) 4 =
      0 := by
    apply
      central_homologyFourMap_eq_zero_of_baseFirstZero D.correction D.radius D.radius_pos
        D.radius_lt_one D.holomorphic D.smallDrift
    intro q
    exact
      retraction_gammaBoundary_base_zero D δ hbase h' η hh'.le hηr
        (hh'.trans_le (min_le_right η₀ δ)) R hEnd q
  rw [gammaBoundaryToFull_homology_eq D h h' 4]
  exact
    gammaBoundaryToFull_homologyFour_eq_zero_of_retraction D η hη.le R H.toHomotopy h' hh'.le
      hzero

private theorem CuspBoundaryGammaZero.fibreMap_eq_capSectionFibre (j : Elliptic.Kind) :
    fibreMap = PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre j 0 := by
  apply ContinuousMap.ext
  intro y
  obtain ⟨x, rfl⟩ := PeriodTorusHigherHomology.coordinateProjection_surjective 3 y
  rw [fibreMap_coordinateProjection,
    PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_zero_coordinateProjection]

private theorem CuspBoundaryGammaZero.fibreMap_h3_coordinates
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (SingularMayerVietoris.singularHomologyMap fibreMap 3 a) =
      Pi.single (3 : Fin 4) (Elliptic.HigherHomology.torusH3Coordinates a) := by
  rw [fibreMap_eq_capSectionFibre .three]
  exact PeriodFamily.Boundary.EllipticCapProduct.capSectionFibre_zero_h3 .three a

private theorem CuspBoundaryGammaZero.fibreMap_h3_top :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (SingularMayerVietoris.singularHomologyMap fibreMap 3
          (Elliptic.HigherHomology.torusH3Coordinates.symm 1)) =
      Pi.single (3 : Fin 4) 1 := by rw [fibreMap_h3_coordinates, LinearEquiv.apply_symm_apply]

private theorem CuspBoundaryGammaZero.restrictedMonodromy_h3_identity :
    MappingTorusHomology.monodromyHomologyMap restrictedMonodromy 3 = LinearMap.id := by
  apply LinearMap.ext
  intro a
  apply Elliptic.HigherHomology.torusH3Coordinates.injective
  change
    Elliptic.HigherHomology.torusH3Coordinates
        (SingularMayerVietoris.singularHomologyMap
          (PeriodTorusHigherHomology.torusMatrixMap restrictedMatrix) 3 a) =
      Elliptic.HigherHomology.torusH3Coordinates a
  rw [Elliptic.HigherHomology.torusH3Coordinates_matrix_natural, restrictedMatrix_det, one_mul]

private theorem CuspBoundaryGammaZero.topWang_injective :
    Function.Injective (MappingTorusHomology.wangBoundary restrictedMonodromy 3) := by
  let :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 4) :=
    PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt (by decide : 3 < 4)
  have hzero : MappingTorusHomology.fibreHomologyMap restrictedMonodromy 4 = 0 := by
    apply LinearMap.ext
    intro a
    exact
      (congrArg (MappingTorusHomology.fibreHomologyMap restrictedMonodromy 4)
            (Subsingleton.elim a 0)).trans
        (map_zero (MappingTorusHomology.fibreHomologyMap restrictedMonodromy 4))
  apply LinearMap.ker_eq_bot.mp
  rw [← MappingTorusHomology.wang_exact_at_mappingTorus restrictedMonodromy 3, hzero,
    LinearMap.range_zero]

private theorem CuspBoundaryGammaZero.topWang_surjective :
    Function.Surjective (MappingTorusHomology.wangBoundary restrictedMonodromy 3) := by
  intro a
  have ha : a ∈ LinearMap.ker (MappingTorusHomology.wangDifference restrictedMonodromy 3) := by
    change a - MappingTorusHomology.monodromyHomologyMap restrictedMonodromy 3 a = 0
    rw [restrictedMonodromy_h3_identity, LinearMap.id_apply, sub_self]
  rw [← MappingTorusHomology.wangBoundary_range restrictedMonodromy 3] at ha
  exact ha

private def CuspBoundaryGammaZero.topWangEquiv :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus restrictedMonodromy) 4 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3 :=
  LinearEquiv.ofBijective (MappingTorusHomology.wangBoundary restrictedMonodromy 3)
    ⟨topWang_injective, topWang_surjective⟩

private def CuspBoundaryGammaZero.H4Coordinates :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus restrictedMonodromy) 4 ≃ₗ[ℤ] ℤ :=
  topWangEquiv.trans Elliptic.HigherHomology.torusH3Coordinates

private def CuspBoundaryGammaZero.fundamentalClass :
    SingularMayerVietoris.SingularHomology (MappingTorus.Torus restrictedMonodromy) 4 :=
  H4Coordinates.symm 1

@[simp]
private theorem CuspBoundaryGammaZero.H4Coordinates_fundamentalClass :
    H4Coordinates fundamentalClass = 1 :=
  H4Coordinates.apply_symm_apply 1

private theorem CuspBoundaryGammaZero.wangBoundary_fundamentalClass :
    MappingTorusHomology.wangBoundary restrictedMonodromy 3 fundamentalClass =
      Elliptic.HigherHomology.torusH3Coordinates.symm 1 := by
  apply Elliptic.HigherHomology.torusH3Coordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  exact H4Coordinates_fundamentalClass

private theorem CuspBoundaryGammaZero.mappingTorusMap_mapsTo_U {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x)) :
    Set.MapsTo (mappingTorusMap f g e he) (MappingTorus.HomologyCover.U f)
      (MappingTorus.HomologyCover.U g) := by
  intro q hq
  change MappingTorus.base g (mappingTorusMap f g e he q) ≠ ((0 : ℝ) : MappingTorus.Circle)
  rw [mappingTorusMap_base]
  exact hq

private theorem CuspBoundaryGammaZero.mappingTorusMap_mapsTo_V {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x)) :
    Set.MapsTo (mappingTorusMap f g e he) (MappingTorus.HomologyCover.V f)
      (MappingTorus.HomologyCover.V g) := by
  intro q hq
  change MappingTorus.base g (mappingTorusMap f g e he q) ≠ ((-(1 / 2 : ℝ)) : MappingTorus.Circle)
  rw [mappingTorusMap_base]
  exact hq

private def CuspBoundaryGammaZero.mappingTorusIntersectionMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x)) :
    C((MappingTorus.HomologyCover.U f ∩ MappingTorus.HomologyCover.V f :
        Set (MappingTorus.Torus f)),
      (MappingTorus.HomologyCover.U g ∩ MappingTorus.HomologyCover.V g :
        Set (MappingTorus.Torus g))) :=
  SingularMayerVietoris.intersectionRestriction (mappingTorusMap f g e he)
    (MappingTorus.HomologyCover.U f) (MappingTorus.HomologyCover.V f)
    (MappingTorus.HomologyCover.U g) (MappingTorus.HomologyCover.V g)
    (mappingTorusMap_mapsTo_U f g e he) (mappingTorusMap_mapsTo_V f g e he)

private theorem
    CuspBoundaryGammaZero.mappingTorusIntersectionMap_lower {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x)) :
    (mappingTorusIntersectionMap f g e he).comp (PeriodFamily.Boundary.lowerComponentFibre f) =
      (PeriodFamily.Boundary.lowerComponentFibre g).comp e := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    mappingTorusMap f g e he (PeriodFamily.Boundary.lowerComponentFibre f x).val =
      (PeriodFamily.Boundary.lowerComponentFibre g (e x)).val
  simp only [PeriodFamily.Boundary.lowerComponentFibre_coe, mappingTorusMap_mk]

private theorem
    CuspBoundaryGammaZero.mappingTorusIntersectionMap_upper {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x)) :
    (mappingTorusIntersectionMap f g e he).comp (PeriodFamily.Boundary.upperComponentFibre f) =
      (PeriodFamily.Boundary.upperComponentFibre g).comp e := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    mappingTorusMap f g e he (PeriodFamily.Boundary.upperComponentFibre f x).val =
      (PeriodFamily.Boundary.upperComponentFibre g (e x)).val
  simp only [PeriodFamily.Boundary.upperComponentFibre_coe, mappingTorusMap_mk]

private def
    CuspBoundaryGammaZero.mappingTorusIntersectionComparison {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x))
    (n : ℕ) :
    (SingularMayerVietoris.SingularHomology X n ×
        SingularMayerVietoris.SingularHomology X n) →ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology Y n × SingularMayerVietoris.SingularHomology Y n) :=
  (MappingTorusHomology.intersectionHomologyEquiv g n).toLinearMap.comp
    ((SingularMayerVietoris.singularHomologyMap (mappingTorusIntersectionMap f g e he) n).comp
      (MappingTorusHomology.intersectionHomologyEquiv f n).symm.toLinearMap)

@[simp]
private theorem CuspBoundaryGammaZero.mappingTorusIntersectionComparison_apply {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y))
    (he : ∀ x, e (f x) = g (e x)) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X n × SingularMayerVietoris.SingularHomology X n) :
    mappingTorusIntersectionComparison f g e he n a =
      MappingTorusHomology.intersectionHomologyEquiv g n
        (SingularMayerVietoris.singularHomologyMap (mappingTorusIntersectionMap f g e he) n
          ((MappingTorusHomology.intersectionHomologyEquiv f n).symm a)) :=
  rfl

private theorem CuspBoundaryGammaZero.mappingTorusIntersectionComparison_lower {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y))
    (he : ∀ x, e (f x) = g (e x)) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    mappingTorusIntersectionComparison f g e he n (a, 0) =
      (SingularMayerVietoris.singularHomologyMap e n a, 0) := by
  rw [mappingTorusIntersectionComparison_apply,
    PeriodFamily.Boundary.intersectionHomologyEquiv_symm_lower, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, mappingTorusIntersectionMap_lower,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    PeriodFamily.Boundary.lowerComponentFibre_homology]

private theorem CuspBoundaryGammaZero.mappingTorusIntersectionComparison_upper {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y))
    (he : ∀ x, e (f x) = g (e x)) (n : ℕ) (a : SingularMayerVietoris.SingularHomology X n) :
    mappingTorusIntersectionComparison f g e he n (0, a) =
      (0, SingularMayerVietoris.singularHomologyMap e n a) := by
  rw [mappingTorusIntersectionComparison_apply,
    PeriodFamily.Boundary.intersectionHomologyEquiv_symm_upper, ← LinearMap.comp_apply, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp, mappingTorusIntersectionMap_upper,
    PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    PeriodFamily.Boundary.upperComponentFibre_homology]

private theorem CuspBoundaryGammaZero.mappingTorusIntersectionComparison_pair {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y))
    (he : ∀ x, e (f x) = g (e x)) (n : ℕ) (a b : SingularMayerVietoris.SingularHomology X n) :
    mappingTorusIntersectionComparison f g e he n (a, b) =
      (SingularMayerVietoris.singularHomologyMap e n a,
        SingularMayerVietoris.singularHomologyMap e n b) := by
  have hab : (a, b) = (a, (0 : SingularMayerVietoris.SingularHomology X n)) + (0, b) := by
    ext <;> simp
  rw [hab, map_add, mappingTorusIntersectionComparison_lower,
    mappingTorusIntersectionComparison_upper]
  simp

private theorem CuspBoundaryGammaZero.mappingTorus_boundaryCoordinates_naturality {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y))
    (he : ∀ x, e (f x) = g (e x)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n
        (SingularMayerVietoris.singularHomologyMap (mappingTorusMap f g e he) (n + 1) a) =
      MappingTorusHomology.intersectionHomologyEquiv g n
        (SingularMayerVietoris.singularHomologyMap (mappingTorusIntersectionMap f g e he) n
          (MappingTorusHomology.mayerVietorisConnecting f n a)) := by
  have h :=
    SingularMayerVietoris.connectingHomomorphism_naturality_apply (mappingTorusMap f g e he)
      (MappingTorus.HomologyCover.U f) (MappingTorus.HomologyCover.V f)
      (MappingTorus.HomologyCover.U g) (MappingTorus.HomologyCover.V g)
      (mappingTorusMap_mapsTo_U f g e he) (mappingTorusMap_mapsTo_V f g e he)
      (MappingTorus.HomologyCover.U_open f) (MappingTorus.HomologyCover.V_open f)
      (MappingTorus.HomologyCover.cover f) (MappingTorus.HomologyCover.U_open g)
      (MappingTorus.HomologyCover.V_open g) (MappingTorus.HomologyCover.cover g) n a
  exact (congrArg (MappingTorusHomology.intersectionHomologyEquiv g n) h).symm

private theorem CuspBoundaryGammaZero.mappingTorus_boundaryCoordinates_comparison {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y))
    (he : ∀ x, e (f x) = g (e x)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n
        (SingularMayerVietoris.singularHomologyMap (mappingTorusMap f g e he) (n + 1) a) =
      mappingTorusIntersectionComparison f g e he n
        (-MappingTorusHomology.wangBoundary f n a, MappingTorusHomology.wangBoundary f n a) := by
  rw [mappingTorus_boundaryCoordinates_naturality f g e he,
    PeriodFamily.Boundary.mappingTorusConnecting_eq_marked_boundary f n a]
  rfl

private theorem CuspBoundaryGammaZero.mappingTorus_boundaryCoordinates_pair {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y))
    (he : ∀ x, e (f x) = g (e x)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    MappingTorusHomology.boundaryCoordinates g n
        (SingularMayerVietoris.singularHomologyMap (mappingTorusMap f g e he) (n + 1) a) =
      (-SingularMayerVietoris.singularHomologyMap e n (MappingTorusHomology.wangBoundary f n a),
        SingularMayerVietoris.singularHomologyMap e n
          (MappingTorusHomology.wangBoundary f n a)) := by
  rw [mappingTorus_boundaryCoordinates_comparison f g e he,
    mappingTorusIntersectionComparison_pair, map_neg]

private theorem CuspBoundaryGammaZero.wangBoundary_mappingTorusMap {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : X ≃ₜ X) (g : Y ≃ₜ Y) (e : C(X, Y)) (he : ∀ x, e (f x) = g (e x))
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology (MappingTorus.Torus f) (n + 1)) :
    MappingTorusHomology.wangBoundary g n
        (SingularMayerVietoris.singularHomologyMap (mappingTorusMap f g e he) (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap e n (MappingTorusHomology.wangBoundary f n a) := by
  change
    -(MappingTorusHomology.boundaryCoordinates g n
            (SingularMayerVietoris.singularHomologyMap (mappingTorusMap f g e he) (n + 1) a)).1 =
      _
  rw [mappingTorus_boundaryCoordinates_pair f g e he, neg_neg]

private theorem CuspBoundaryGammaZero.boundaryMap_wang (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology Boundary (n + 1)) :
    MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy n
        (SingularMayerVietoris.singularHomologyMap boundaryMap (n + 1) a) =
      SingularMayerVietoris.singularHomologyMap fibreMap n
        (MappingTorusHomology.wangBoundary restrictedMonodromy n a) :=
  wangBoundary_mappingTorusMap restrictedMonodromy ThreefoldOverlapMappingTorus.Cusp.monodromy
    fibreMap fibreMap_monodromy n a

private def CuspBoundaryGammaZero.nativeClass :
    SingularMayerVietoris.SingularHomology ThreefoldOverlapMappingTorus.Cusp.Boundary 4 :=
  SingularMayerVietoris.singularHomologyMap boundaryMap 4 fundamentalClass

private theorem CuspBoundaryGammaZero.nativeClass_wang :
    MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3 nativeClass =
      SingularMayerVietoris.singularHomologyMap fibreMap 3
        (Elliptic.HigherHomology.torusH3Coordinates.symm 1) := by
  change
    MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
        (SingularMayerVietoris.singularHomologyMap boundaryMap 4 fundamentalClass) =
      _
  rw [boundaryMap_wang, wangBoundary_fundamentalClass]

private theorem CuspBoundaryGammaZero.nativeClass_wang_coordinates :
    PeriodFamily.FlatTorus.singularH3Coordinates
        (MappingTorusHomology.wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 3
          nativeClass) =
      Pi.single (3 : Fin 4) 1 := by rw [nativeClass_wang, fibreMap_h3_top]

private theorem CuspBoundaryTopVanishing.boundaryToFilling_gammaBoundary_homologyFour_eq_zero :
    SingularMayerVietoris.singularHomologyMap
        ((ThreefoldOverlapMappingTorus.boundaryToFilling Option.none).comp
          CuspBoundaryGammaZero.boundaryMap)
        4 =
      0 := by
  rw [gammaBoundaryToFilling_eq]
  exact
    gammaBoundaryToFull_homologyFour_eq_zero ThreefoldOverlapMappingTorus.Cusp.specialData
      ThreefoldOverlapMappingTorus.Cusp.specialHeight

private theorem CuspBoundaryTopVanishing.boundaryToFilling_boundaryMap_homologyFour
    (a : SingularMayerVietoris.SingularHomology CuspBoundaryGammaZero.Boundary 4) :
    SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none) 4
        (SingularMayerVietoris.singularHomologyMap CuspBoundaryGammaZero.boundaryMap 4 a) =
      0 := by
  have h := LinearMap.congr_fun boundaryToFilling_gammaBoundary_homologyFour_eq_zero a
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp CuspBoundaryGammaZero.boundaryMap
      (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none) 4] at h
  exact h

private theorem CuspBoundaryTopVanishing.boundaryToFilling_nativeClass_eq_zero :
    SingularMayerVietoris.singularHomologyMap
        (ThreefoldOverlapMappingTorus.boundaryToFilling Option.none) 4
        CuspBoundaryGammaZero.nativeClass =
      0 :=
  boundaryToFilling_boundaryMap_homologyFour CuspBoundaryGammaZero.fundamentalClass

private theorem CuspBoundaryTopVanishing.boundaryFillingHomologyMap_nativeClass_eq_zero :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap Option.none 4
        CuspBoundaryGammaZero.nativeClass =
      0 :=
  boundaryToFilling_nativeClass_eq_zero

private theorem CuspBoundaryGammaZero.regularMap_gamma_zero (q : Boundary) :
    PeriodFamily.GammaZero.familyGamma ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
        (ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none (boundaryMap q)) =
      0 := by
  obtain ⟨⟨t, y⟩, rfl⟩ := MappingTorus.mk_surjective restrictedMonodromy q
  rw [boundaryMap_mk, ThreefoldOverlapMappingTorus.Cusp.boundaryToRegularFamily_cusp_mk,
    PeriodFamily.GammaZero.familyGamma_quotient, fibreMap_gamma]

private def CuspBoundaryGammaZero.regularGammaZeroMap :
    C(Boundary,
      PeriodFamily.GammaZero.Space ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData) :=
  PeriodFamily.GammaZero.lift ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData
    ((ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none).comp boundaryMap)
    regularMap_gamma_zero

@[simp]
private theorem CuspBoundaryGammaZero.inclusion_comp_regularGammaZeroMap :
    (PeriodFamily.GammaZero.inclusion ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData).comp
        regularGammaZeroMap =
      (ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none).comp boundaryMap :=
  rfl

private theorem CuspBoundaryGammaZero.boundaryRegularHomologyMap_gammaZero_factor (n : ℕ) :
    (ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none n).comp
        (SingularMayerVietoris.singularHomologyMap boundaryMap n) =
      (SingularMayerVietoris.singularHomologyMap
            (PeriodFamily.GammaZero.inclusion
              ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData)
            n).comp
        (SingularMayerVietoris.singularHomologyMap regularGammaZeroMap n) := by
  have h :=
    PeriodTorusHigherHomology.singularHomologyMap_comp regularGammaZeroMap
      (PeriodFamily.GammaZero.inclusion ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData) n
  rw [inclusion_comp_regularGammaZeroMap] at h
  exact
    (PeriodTorusHigherHomology.singularHomologyMap_comp boundaryMap
          (ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none) n).symm.trans
      h

private theorem CuspBoundaryGammaZero.boundaryRegularHomologyMap_gammaZero_mem_range (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology Boundary n) :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none n
        (SingularMayerVietoris.singularHomologyMap boundaryMap n a) ∈
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.GammaZero.inclusion ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData)
          n) := by
  refine ⟨SingularMayerVietoris.singularHomologyMap regularGammaZeroMap n a, ?_⟩
  exact (LinearMap.congr_fun (boundaryRegularHomologyMap_gammaZero_factor n) a).symm

private theorem CuspBoundaryGammaZero.nativeClass_regular_mem_range :
    ThreefoldOverlapMappingTorus.boundaryRegularHomologyMap Option.none 4 nativeClass ∈
      LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (PeriodFamily.GammaZero.inclusion ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData)
          4) :=
  boundaryRegularHomologyMap_gammaZero_mem_range 4 fundamentalClass

private def CuspNegation.triangleNeg (s : ToricFan.Triangle) : ToricFan.Triangle :=
  ⟨-s.a - 1, -s.b - 1, !s.upper⟩

private def
    CuspNegation.permute (z : ToricCharts.CoordinateSpace 3) : ToricCharts.CoordinateSpace 3 :=
  fun j => z j.rev

private theorem CuspNegation.triangleNeg_involutive : Function.Involutive triangleNeg := by
  intro s
  ext <;> simp [triangleNeg]

private theorem CuspNegation.permute_involutive : Function.Involutive permute := by
  intro z
  funext j
  simp [permute]

private theorem CuspNegation.permute_holomorphic : ContDiff ℂ ω permute :=
  contDiff_pi.mpr fun j => contDiff_apply ℂ ℂ j.rev

private theorem CuspNegation.time_permute (z : ToricCharts.CoordinateSpace 3) :
    ToricFan.Triangle.time (permute z) = ToricFan.Triangle.time z := by
  simp [ToricFan.Triangle.time, permute, Fin.rev]
  ring

private theorem CuspNegation.triangleNeg_shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    triangleNeg (s.shift v) = (triangleNeg s).shift (-v) := by
  ext <;> simp [triangleNeg, ToricFan.Triangle.shift] <;> ring

private theorem CuspNegation.transition_triangleNeg (s t : ToricFan.Triangle) (i j : Fin 3) :
    ToricFan.Triangle.transition (triangleNeg s) (triangleNeg t) i j =
      ToricFan.Triangle.transition s t i.rev j.rev := by
  cases hs : s.upper <;> cases ht : t.upper <;> fin_cases i <;> fin_cases j <;>
      simp [ToricFan.Triangle.transition, ToricFan.Triangle.dual, ToricFan.Triangle.rays,
        triangleNeg, hs, ht, Matrix.mul_apply, Fin.sum_univ_succ, Fin.rev] <;>
    ring

private theorem CuspNegation.chartChange_triangleNeg_source_iff (s t : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    permute z ∈ (ToricFan.Triangle.chartChange (triangleNeg s) (triangleNeg t)).source ↔
      z ∈ (ToricFan.Triangle.chartChange s t).source := by
  simp only [ToricFan.Triangle.chartChange_source]
  constructor
  · intro h i j hij
    have hneg : ToricFan.Triangle.transition (triangleNeg s) (triangleNeg t) i.rev j.rev < 0 := by
      simpa only [transition_triangleNeg, Fin.rev_rev] using hij
    simpa only [permute, Fin.rev_rev] using h i.rev j.rev hneg
  · intro h i j hij
    exact h i.rev j.rev (by simpa only [transition_triangleNeg] using hij)

private theorem CuspNegation.chartChange_triangleNeg_apply (s t : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricFan.Triangle.chartChange (triangleNeg s) (triangleNeg t) (permute z) =
      permute (ToricFan.Triangle.chartChange s t z) := by
  funext i
  change
    (∏ j, z j.rev ^ ToricFan.Triangle.transition (triangleNeg s) (triangleNeg t) i j) =
      ∏ j, z j ^ ToricFan.Triangle.transition s t i.rev j
  simp only [transition_triangleNeg]
  simp [Fin.prod_univ_succ, Fin.rev, mul_comm, mul_left_comm, mul_assoc]

private theorem CuspNegation.cuspVector_neg (v : Fin 2 → ℤ) :
    ToricSpace.cuspVector (-v) = -ToricSpace.cuspVector v := by
  ext i
  fin_cases i <;> simp [ToricSpace.cuspVector]

private theorem
    CuspNegation.exponentialMultiplier_neg (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (t : ℂ) :
    ToricSpace.exponentialMultiplier C (-v) t = (ToricSpace.exponentialMultiplier C v t)⁻¹ := by
  have he : (fun i => ((-v) i : ℂ)) = -(fun i => (v i : ℂ)) := by
    ext i
    simp
  ext j
  change
    Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => ((-v) i : ℂ))) j) =
      (Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => (v i : ℂ))) j))⁻¹
  rw [he, Matrix.mulVec_neg]
  simp only [Pi.neg_apply, mul_neg, Complex.exp_neg]

private def CuspNegation.logNeg (p : ℂ × ComplexPlane₂) : ℂ × ComplexPlane₂ :=
  (p.1, -p.2)

private theorem CuspNegation.negation_compatible (s t : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) (hz : z ∈ (ToricFan.Triangle.chartChange s t).source) :
    ToricSpace.inclusion (triangleNeg t) (permute (ToricFan.Triangle.chartChange s t z)) =
      ToricSpace.inclusion (triangleNeg s) (permute z) := by
  apply ((ToricSpace.inclusion_eq_iff (triangleNeg s) (triangleNeg t) (permute z) _).mpr ?_).symm
  exact ⟨(chartChange_triangleNeg_source_iff s t z).mpr hz, chartChange_triangleNeg_apply s t z⟩

private def CuspNegation.toricNegation : ToricSpace.Space → ToricSpace.Space :=
  ToricSpace.descend (fun s z => ToricSpace.inclusion (triangleNeg s) (permute z))

@[simp]
private theorem CuspNegation.toricNegation_inclusion (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    toricNegation (ToricSpace.inclusion s z) = ToricSpace.inclusion (triangleNeg s) (permute z) :=
  ToricSpace.descend_inclusion _ negation_compatible s z

private theorem CuspNegation.toricNegation_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω toricNegation :=
  ToricSpace.descend_holomorphic _ _ negation_compatible
    (fun s =>
      (ToricSpace.inclusion_holomorphic (triangleNeg s)).comp permute_holomorphic.contMDiff)

private theorem CuspNegation.toricNegation_involutive : Function.Involutive toricNegation := by
  intro x
  obtain ⟨s, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
  rw [toricNegation_inclusion, toricNegation_inclusion, triangleNeg_involutive s,
    permute_involutive z]

@[simp]
private theorem CuspNegation.time_toricNegation (x : ToricSpace.Space) :
    ToricSpace.time (toricNegation x) = ToricSpace.time x := by
  obtain ⟨s, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
  rw [toricNegation_inclusion, ToricSpace.time_inclusion, ToricSpace.time_inclusion, time_permute]

private theorem CuspNegation.toricNegation_translate (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    toricNegation (ToricSpace.translate v x) = ToricSpace.translate (-v) (toricNegation x) := by
  obtain ⟨s, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
  rw [ToricSpace.translate_inclusion, toricNegation_inclusion, toricNegation_inclusion,
    ToricSpace.translate_inclusion, triangleNeg_shift]

private theorem CuspNegation.factors_triangleNeg_inverse (s : ToricFan.Triangle) (u : Fin 2 → ℂˣ) :
    ToricSpace.factors (triangleNeg s) (ToricSpace.fibreMultiplier u⁻¹) =
      permute (ToricSpace.factors s (ToricSpace.fibreMultiplier u)) := by
  ext i
  cases hs : s.upper <;> fin_cases i <;>
    simp [ToricSpace.factors, ToricCharts.monomial, ToricFan.Triangle.dual, triangleNeg, permute,
      hs, ToricSpace.fibreMultiplier, Fin.prod_univ_succ, Fin.rev, mul_comm]

private theorem CuspNegation.permute_scale (s : ToricFan.Triangle) (u : Fin 2 → ℂˣ)
    (z : ToricCharts.CoordinateSpace 3) :
    permute (ToricSpace.scale s (ToricSpace.fibreMultiplier u) z) =
      ToricSpace.scale (triangleNeg s) (ToricSpace.fibreMultiplier u⁻¹) (permute z) := by
  ext i
  change
    ToricSpace.factors s (ToricSpace.fibreMultiplier u) i.rev * z i.rev =
      ToricSpace.factors (triangleNeg s) (ToricSpace.fibreMultiplier u⁻¹) i * z i.rev
  rw [factors_triangleNeg_inverse]
  rfl

private theorem CuspNegation.toricNegation_fibreMultiplier (u : Fin 2 → ℂˣ) (x : ToricSpace.Space) :
    toricNegation (ToricSpace.torusAction (ToricSpace.fibreMultiplier u) x) =
      ToricSpace.torusAction (ToricSpace.fibreMultiplier u⁻¹) (toricNegation x) := by
  obtain ⟨s, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
  rw [ToricSpace.torusAction_inclusion, toricNegation_inclusion, toricNegation_inclusion,
    ToricSpace.torusAction_inclusion, permute_scale]

private theorem CuspNegation.toricNegation_variableMultiplier (u : ℂ → Fin 2 → ℂˣ)
    (x : ToricSpace.Space) :
    toricNegation (ToricSpace.variableMultiplier u x) =
      ToricSpace.variableMultiplier (fun t => (u t)⁻¹) (toricNegation x) := by
  simp only [ToricSpace.variableMultiplier, toricNegation_fibreMultiplier, time_toricNegation]

private theorem CuspNegation.toricNegation_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (x : ToricSpace.Space) :
    toricNegation (ToricSpace.twistedTranslate C v x) =
      ToricSpace.twistedTranslate C (-v) (toricNegation x) := by
  have he :
    (fun t => (ToricSpace.exponentialMultiplier C v t)⁻¹) =
      ToricSpace.exponentialMultiplier C (-v) :=
    funext fun t => (exponentialMultiplier_neg C v t).symm
  rw [ToricSpace.twistedTranslate, toricNegation_variableMultiplier, toricNegation_translate, he,
    ToricSpace.twistedTranslate, cuspVector_neg]

private def CuspNegation.tubeNegation (D : TopologicalSpace.Opens ℂ) (x : ToricSpace.Tube D) :
    ToricSpace.Tube D :=
  ⟨toricNegation x, by
    change ToricSpace.time (toricNegation x) ∈ D
    rw [time_toricNegation]
    exact x.2⟩

private theorem CuspNegation.tubeNegation_involutive (D : TopologicalSpace.Opens ℂ) :
    Function.Involutive (tubeNegation D) := fun x => Subtype.ext (toricNegation_involutive x)

private theorem CuspNegation.tubeNegation_continuous (D : TopologicalSpace.Opens ℂ) :
    Continuous (tubeNegation D) :=
  (toricNegation_holomorphic.continuous.comp continuous_subtype_val).subtype_mk _

private theorem CuspNegation.tubeNegation_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (D : TopologicalSpace.Opens ℂ) (v : Fin 2 → ℤ) (x : ToricSpace.Tube D) :
    tubeNegation D (ToricSpace.tubeTranslate C D v x) =
      ToricSpace.tubeTranslate C D (-v) (tubeNegation D x) :=
  Subtype.ext (toricNegation_twistedTranslate C v x)

private theorem CuspNegation.tubeNegation_related (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    {x y : ToricSpace.Tube (CuspQuotient.disc ε)} (hxy : (CuspQuotient.relation C ε).r x y) :
    (CuspQuotient.relation C ε).r (tubeNegation (CuspQuotient.disc ε) x)
      (tubeNegation (CuspQuotient.disc ε) y) := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  change x ∈ MulAction.orbit CuspQuotient.LatticeGroup y at hxy
  change
    tubeNegation (CuspQuotient.disc ε) x ∈
      MulAction.orbit CuspQuotient.LatticeGroup (tubeNegation (CuspQuotient.disc ε) y)
  obtain ⟨g, rfl⟩ := hxy
  refine ⟨Multiplicative.ofAdd (-g.toAdd), ?_⟩
  exact (tubeNegation_translate C (CuspQuotient.disc ε) g.toAdd y).symm

private def CuspNegation.quotientNegation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    CuspQuotient.QuotientSpace C ε → CuspQuotient.QuotientSpace C ε :=
  Quotient.map (tubeNegation (CuspQuotient.disc ε)) (fun _ _ h => tubeNegation_related C ε h)

@[simp]
private theorem CuspNegation.quotientNegation_quotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (x : ToricSpace.Tube (CuspQuotient.disc ε)) :
    quotientNegation C ε (CuspQuotient.quotientMap C ε x) =
      CuspQuotient.quotientMap C ε (tubeNegation (CuspQuotient.disc ε) x) :=
  rfl

private theorem
    CuspNegation.quotientNegation_involutive (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Function.Involutive (quotientNegation C ε) := by
  intro q
  induction q using Quotient.inductionOn with
  | h
    x =>
    change
      CuspQuotient.quotientMap C ε
          (tubeNegation (CuspQuotient.disc ε) (tubeNegation (CuspQuotient.disc ε) x)) =
        CuspQuotient.quotientMap C ε x
    rw [tubeNegation_involutive (CuspQuotient.disc ε) x]

private theorem
    CuspNegation.quotientNegation_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (quotientNegation C ε) :=
  ((CuspQuotient.quotientMap_continuous C ε).comp
        (tubeNegation_continuous (CuspQuotient.disc ε))).quotient_lift
    _

private def CuspNegation.quotientHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    CuspQuotient.QuotientSpace C ε ≃ₜ CuspQuotient.QuotientSpace C ε
    where
  toFun := quotientNegation C ε
  invFun := quotientNegation C ε
  left_inv := quotientNegation_involutive C ε
  right_inv := quotientNegation_involutive C ε
  continuous_toFun := quotientNegation_continuous C ε
  continuous_invFun := quotientNegation_continuous C ε

private def CuspNegation.fibreReciprocal (w : ToricCharts.CoordinateSpace 3) :
    ToricCharts.CoordinateSpace 3 :=
  ![(w 0)⁻¹, (w 1)⁻¹, w 2]

private theorem CuspNegation.fibreReciprocal_mem_torus {w : ToricCharts.CoordinateSpace 3}
    (hw : w ∈ ToricCharts.torus) : fibreReciprocal w ∈ ToricCharts.torus := by
  intro i
  fin_cases i
  · exact inv_ne_zero (hw 0)
  · exact inv_ne_zero (hw 1)
  · exact hw 2

private theorem CuspNegation.permute_mem_torus {w : ToricCharts.CoordinateSpace 3}
    (hw : w ∈ ToricCharts.torus) : permute w ∈ ToricCharts.torus := fun i => hw i.rev

private theorem CuspNegation.rays_triangleNeg (s : ToricFan.Triangle) (i j : Fin 3) :
    (triangleNeg s).rays i j = if i = 2 then s.rays i j.rev else -s.rays i j.rev := by
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
      simp [ToricFan.Triangle.rays, triangleNeg, hs, Fin.rev] <;>
    ring

private theorem CuspNegation.monomial_rays_triangleNeg (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricCharts.monomial (triangleNeg s).rays (permute z) =
      fibreReciprocal (ToricCharts.monomial s.rays z) := by
  have hp (i : Fin 3) : (∏ j : Fin 3, z j.rev ^ s.rays i j.rev) = ∏ j : Fin 3, z j ^ s.rays i j :=
    Equiv.prod_comp Fin.revPerm (fun j => z j ^ s.rays i j)
  ext i
  by_cases hi : i = 2
  · subst i
    change (∏ j, z j.rev ^ (triangleNeg s).rays 2 j) = ∏ j, z j ^ s.rays 2 j
    simp only [rays_triangleNeg]
    exact hp 2
  · have ht :
      fibreReciprocal (ToricCharts.monomial s.rays z) i = (ToricCharts.monomial s.rays z i)⁻¹ := by
      fin_cases i <;> simp_all [fibreReciprocal]
    rw [ht]
    change (∏ j, z j.rev ^ (triangleNeg s).rays i j) = (∏ j, z j ^ s.rays i j)⁻¹
    simp only [rays_triangleNeg, hi, ite_false, zpow_neg, Finset.prod_inv_distrib]
    exact congrArg Inv.inv (hp i)

private theorem CuspNegation.torusCoordinates_toricNegation {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.openTorus) :
    ToricSpace.torusCoordinates (toricNegation x) =
      fibreReciprocal (ToricSpace.torusCoordinates x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [toricNegation_inclusion, ToricSpace.torusCoordinates_inclusion _ (permute_mem_torus hz),
    ToricSpace.torusCoordinates_inclusion _ hz, monomial_rays_triangleNeg]

private theorem CuspNegation.toricNegation_mem_openTorus {x : ToricSpace.Space}
    (hx : x ∈ ToricSpace.openTorus) : toricNegation x ∈ ToricSpace.openTorus := by
  apply (ToricSpace.mem_openTorus_iff _).mpr
  rw [time_toricNegation]
  exact (ToricSpace.mem_openTorus_iff _).mp hx

private theorem CuspNegation.toricNegation_torusPoint {w : ToricCharts.CoordinateSpace 3}
    (hw : w ∈ ToricCharts.torus) :
    toricNegation (CuspUniformization.torusPoint w) =
      CuspUniformization.torusPoint (fibreReciprocal w) := by
  apply
    CuspUniformization.torusCoordinates_injective
      (toricNegation_mem_openTorus (CuspUniformization.torusPoint_mem hw))
      (CuspUniformization.torusPoint_mem (fibreReciprocal_mem_torus hw))
  rw [torusCoordinates_toricNegation (CuspUniformization.torusPoint_mem hw),
    CuspUniformization.torusCoordinates_torusPoint hw,
    CuspUniformization.torusCoordinates_torusPoint (fibreReciprocal_mem_torus hw)]

private theorem CuspNegation.exponential_neg (z : ℂ) :
    CuspUniformization.exponential (-z) = (CuspUniformization.exponential z)⁻¹ := by
  simp only [CuspUniformization.exponential, mul_neg, Complex.exp_neg]

private theorem CuspNegation.fibreReciprocal_exponentialCoordinates (t : ℂ) (z : ComplexPlane₂) :
    fibreReciprocal (CuspUniformization.exponentialCoordinates t z) =
      CuspUniformization.exponentialCoordinates t (-z) := by
  ext i
  fin_cases i <;>
    simp [fibreReciprocal, CuspUniformization.exponentialCoordinates, exponential_neg]

private theorem
    CuspNegation.toricNegation_exponentialPoint {t : ℂ} (ht : t ≠ 0) (z : ComplexPlane₂) :
    toricNegation (CuspUniformization.exponentialPoint t z) =
      CuspUniformization.exponentialPoint t (-z) := by
  change
    toricNegation
        (CuspUniformization.torusPoint (CuspUniformization.exponentialCoordinates t z)) =
      CuspUniformization.torusPoint (CuspUniformization.exponentialCoordinates t (-z))
  rw [toricNegation_torusPoint (CuspUniformization.exponentialCoordinates_mem ht z),
    fibreReciprocal_exponentialCoordinates]

private def CuspNegation.logCoverNegation (ε : ℝ) (p : CuspUniformization.LogCover ε) :
    CuspUniformization.LogCover ε :=
  ⟨logNeg p, p.2⟩

private theorem CuspNegation.totalExponentialPoint_logNeg (p : ℂ × ComplexPlane₂) :
    toricNegation (CuspUniformization.totalExponentialPoint p) =
      CuspUniformization.totalExponentialPoint (logNeg p) :=
  toricNegation_exponentialPoint (CuspUniformization.exponential_ne_zero p.1) p.2

private theorem CuspNegation.tubeNegation_totalExponentialLift (ε : ℝ)
    (p : CuspUniformization.LogCover ε) :
    tubeNegation (CuspQuotient.disc ε) (CuspUniformization.totalExponentialLift ε p) =
      CuspUniformization.totalExponentialLift ε (logCoverNegation ε p) :=
  Subtype.ext (totalExponentialPoint_logNeg p)

private theorem
    CuspNegation.quotientNegation_totalCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (p : CuspUniformization.LogCover ε) :
    quotientNegation C ε (CuspUniformization.totalCuspCover C ε p) =
      CuspUniformization.totalCuspCover C ε (logCoverNegation ε p) := by
  change
    quotientNegation C ε
        (CuspQuotient.quotientMap C ε (CuspUniformization.totalExponentialLift ε p)) =
      _
  rw [quotientNegation_quotientMap, tubeNegation_totalExponentialLift]
  rfl

private theorem CuspNegation.quotientNegation_puncturedCuspCover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p : CuspUniformization.LogCover ε) :
    quotientNegation C ε (CuspUniformization.puncturedCuspCover C ε p).val =
      (CuspUniformization.puncturedCuspCover C ε (logCoverNegation ε p)).val :=
  quotientNegation_totalCuspCover C ε p

end Mathoverflow1973

end
