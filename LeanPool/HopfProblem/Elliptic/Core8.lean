/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods11
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Elliptic.Core7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods11

/-!
# Hopf problem: elliptic · core 8

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

private def Elliptic.HigherHomology.periodAffineHomeomorph (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : p.val.Torus ≃ₜ p.val.Torus :=
  (Elliptic.affineBiholomorph j p j.twist).toHomeomorph

private def Elliptic.HigherHomology.periodCircleHomologyEquiv (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    SingularMayerVietoris.SingularHomology p.val.Torus (n + 1) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) (n + 1) ×
        SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
        (n + 1)).trans
    (PeriodTorusHigherHomology.circleProductHomologyEquiv
      (PeriodTorusHigherHomology.ProductTorus 3) n)

private theorem Elliptic.HigherHomology.splitPeriodTorusHomeomorph_comp_fibreIntoPeriodTorus
    (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) :
    (splitPeriodTorusHomeomorph j p.val :
            C(p.val.Torus,
              (PeriodTorusHigherHomology.CircleTopology.Circle) ×
                PeriodTorusHigherHomology.ProductTorus 3)).comp
        (fibreIntoPeriodTorus j p) =
      PeriodTorusHigherHomology.CircleTopology.productSection
        (PeriodTorusHigherHomology.ProductTorus 3) := by
  apply ContinuousMap.ext
  intro x
  change
    splitPeriodTorusHomeomorph j p.val ((splitPeriodTorusHomeomorph j p.val).symm (0, x)) = (0, x)
  exact (splitPeriodTorusHomeomorph j p.val).apply_symm_apply (0, x)

private theorem Elliptic.HigherHomology.splitPeriodTorusHomology_fibre_map (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
            n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) n) =
      PeriodTorusHigherHomology.circleSectionHomology (PeriodTorusHigherHomology.ProductTorus 3)
        n := by
  rw [PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    splitPeriodTorusHomeomorph_comp_fibreIntoPeriodTorus]

private theorem Elliptic.HigherHomology.splitPeriodTorusHomology_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n
        (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) n a) =
      PeriodTorusHigherHomology.circleSectionHomology (PeriodTorusHigherHomology.ProductTorus 3) n
        a :=
  DFunLike.congr_fun (splitPeriodTorusHomology_fibre_map j p n) a

@[simp]
private theorem Elliptic.HigherHomology.periodCircleHomologyEquiv_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) (n + 1)) :
    periodCircleHomologyEquiv j p n
        (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) (n + 1) a) =
      (a, 0) := by
  change
    PeriodTorusHigherHomology.circleProductHomologyEquiv
        (PeriodTorusHigherHomology.ProductTorus 3) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
          (n + 1)
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) (n + 1) a)) =
      _
  rw [splitPeriodTorusHomology_fibre,
    PeriodTorusHigherHomology.circleProductHomologyEquiv_section]

private abbrev Elliptic.HigherHomology.DeckHomology.Circle :=
  MappingTorus.Circle

private abbrev Elliptic.HigherHomology.DeckHomology.fibreProductMap {X : Type} [TopologicalSpace X]
    (B : C(X, X)) :
    C(Elliptic.HigherHomology.DeckHomology.Circle × X,
      Elliptic.HigherHomology.DeckHomology.Circle × X) :=
  PeriodTorusHigherHomology.circleProductMap B

private def
    Elliptic.HigherHomology.DeckHomology.translatedProductMap {X : Type} [TopologicalSpace X]
    (s : ℝ) (B : C(X, X)) :
    C(Elliptic.HigherHomology.DeckHomology.Circle × X,
      Elliptic.HigherHomology.DeckHomology.Circle × X)
    where
  toFun p := (p.1 + (s : Elliptic.HigherHomology.DeckHomology.Circle), B p.2)
  continuous_toFun :=
    (continuous_fst.add continuous_const).prodMk (B.continuous.comp continuous_snd)

private def Elliptic.HigherHomology.DeckHomology.productTranslationHomotopy {X : Type}
    [TopologicalSpace X] (s : ℝ) (B : C(X, X)) :
    (fibreProductMap B).Homotopy (translatedProductMap s B)
    where
  toFun
    p := (p.2.1 + ((((p.1 : ℝ) * s : ℝ)) : Elliptic.HigherHomology.DeckHomology.Circle), B p.2.2)
  continuous_toFun := by
    have ht :
      Continuous
        (fun p : unitInterval × (Elliptic.HigherHomology.DeckHomology.Circle × X) =>
          (p.1 : ℝ) * s) :=
      (continuous_subtype_val.comp continuous_fst).mul_const s
    have hc :
      Continuous
        (fun p : unitInterval × (Elliptic.HigherHomology.DeckHomology.Circle × X) =>
          (((p.1 : ℝ) * s : ℝ) : Elliptic.HigherHomology.DeckHomology.Circle)) :=
      (AddCircle.continuous_mk' (1 : ℝ)).comp ht
    exact
      ((continuous_fst.comp continuous_snd).add hc).prodMk
        (B.continuous.comp (continuous_snd.comp continuous_snd))
  map_zero_left
    p := by
    change
      (p.1 + (((((0 : unitInterval) : ℝ) * s : ℝ)) : Elliptic.HigherHomology.DeckHomology.Circle),
          B p.2) =
        (p.1, B p.2)
    simp
  map_one_left
    p := by
    change
      (p.1 + (((((1 : unitInterval) : ℝ) * s : ℝ)) : Elliptic.HigherHomology.DeckHomology.Circle),
          B p.2) =
        (p.1 + (s : Elliptic.HigherHomology.DeckHomology.Circle), B p.2)
    simp

private def Elliptic.HigherHomology.DeckHomology.productTranslationChainHomotopy {X : Type}
    [TopologicalSpace X] (s : ℝ) (B : C(X, X)) :
    _root_.Homotopy (FirstHurewicz.singularChainMap (fibreProductMap B))
      (FirstHurewicz.singularChainMap (translatedProductMap s B)) :=
  PeriodTorusHigherHomology.singularChainHomotopy (productTranslationHomotopy s B)

private theorem Elliptic.HigherHomology.DeckHomology.productTranslation_homologyMap {X : Type}
    [TopologicalSpace X] (s : ℝ) (B : C(X, X)) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (fibreProductMap B) n =
      SingularMayerVietoris.singularHomologyMap (translatedProductMap s B) n :=
  congrArg ModuleCat.Hom.hom ((productTranslationChainHomotopy s B).homologyMap_eq n)

private theorem Elliptic.HigherHomology.DeckHomology.translatedProductMap_homologyMap {X : Type}
    [TopologicalSpace X] (s : ℝ) (B : C(X, X)) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (translatedProductMap s B) n =
      SingularMayerVietoris.singularHomologyMap (PeriodTorusHigherHomology.circleProductMap B)
        n :=
  (productTranslation_homologyMap s B n).symm

private theorem Elliptic.HigherHomology.splitPeriodTorusHomeomorph_comp_affine (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    (splitPeriodTorusHomeomorph j p.val :
            C(p.val.Torus,
              PeriodTorusHigherHomology.CircleTopology.Circle ×
                PeriodTorusHigherHomology.ProductTorus 3)).comp
        (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)) =
      (DeckHomology.translatedProductMap (1 / (j.order : ℝ))
            (fibreTorusHomeomorph j :
              C(PeriodTorusHigherHomology.ProductTorus 3,
                PeriodTorusHigherHomology.ProductTorus 3))).comp
        (splitPeriodTorusHomeomorph j p.val :
          C(p.val.Torus,
            PeriodTorusHigherHomology.CircleTopology.Circle ×
              PeriodTorusHigherHomology.ProductTorus 3)) := by
  apply ContinuousMap.ext
  intro x
  exact splitPeriodTorusHomeomorph_affineBiholomorph j p x

private theorem Elliptic.HigherHomology.splitPeriodTorusHomology_affine_map (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
            n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap
          (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)) n) =
      (SingularMayerVietoris.singularHomologyMap
            (PeriodTorusHigherHomology.circleProductMap
              (fibreTorusHomeomorph j :
                C(PeriodTorusHigherHomology.ProductTorus 3,
                  PeriodTorusHigherHomology.ProductTorus 3)))
            n).comp
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
            n).toLinearMap := by
  simp only [PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap]
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp,
    splitPeriodTorusHomeomorph_comp_affine, PeriodTorusHigherHomology.singularHomologyMap_comp,
    DeckHomology.translatedProductMap_homologyMap]

private theorem Elliptic.HigherHomology.splitPeriodTorusHomology_affine (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus n) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n
        (SingularMayerVietoris.singularHomologyMap
          (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)) n a) =
      SingularMayerVietoris.singularHomologyMap
        (PeriodTorusHigherHomology.circleProductMap
          (fibreTorusHomeomorph j :
            C(PeriodTorusHigherHomology.ProductTorus 3,
              PeriodTorusHigherHomology.ProductTorus 3)))
        n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n
          a) :=
  DFunLike.congr_fun (splitPeriodTorusHomology_affine_map j p n) a

private theorem Elliptic.HigherHomology.periodCircleHomologyEquiv_affine (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus (n + 1)) :
    periodCircleHomologyEquiv j p n
        (SingularMayerVietoris.singularHomologyMap
          (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)) (n + 1) a) =
      (SingularMayerVietoris.singularHomologyMap
          (fibreTorusHomeomorph j :
            C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
          (n + 1) (periodCircleHomologyEquiv j p n a).1,
        SingularMayerVietoris.singularHomologyMap
          (fibreTorusHomeomorph j :
            C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
          n (periodCircleHomologyEquiv j p n a).2) := by
  change
    PeriodTorusHigherHomology.circleProductHomologyEquiv
        (PeriodTorusHigherHomology.ProductTorus 3) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
          (n + 1)
          (SingularMayerVietoris.singularHomologyMap
            (periodAffineHomeomorph j p : C(p.val.Torus, p.val.Torus)) (n + 1) a)) =
      _
  rw [splitPeriodTorusHomology_affine]
  exact
    PeriodTorusHigherHomology.circleProductHomologyEquiv_naturality
      (fibreTorusHomeomorph j :
        C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
      n _

private theorem Elliptic.HigherHomology.periodCircleHomologyEquiv_affine_symm (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus (n + 1)) :
    periodCircleHomologyEquiv j p n
        (SingularMayerVietoris.singularHomologyMap
          ((periodAffineHomeomorph j p).symm : C(p.val.Torus, p.val.Torus)) (n + 1) a) =
      (SingularMayerVietoris.singularHomologyMap
          ((fibreTorusHomeomorph j).symm :
            C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
          (n + 1) (periodCircleHomologyEquiv j p n a).1,
        SingularMayerVietoris.singularHomologyMap
          ((fibreTorusHomeomorph j).symm :
            C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
          n (periodCircleHomologyEquiv j p n a).2) := by
  let A := PeriodTorusHigherHomology.homeomorphHomologyEquiv (periodAffineHomeomorph j p) (n + 1)
  let D :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (fibreTorusHomeomorph j) (n + 1)).prodCongr
      (PeriodTorusHigherHomology.homeomorphHomologyEquiv (fibreTorusHomeomorph j) n)
  have h := periodCircleHomologyEquiv_affine j p n (A.symm a)
  change
    periodCircleHomologyEquiv j p n (A (A.symm a)) =
      D (periodCircleHomologyEquiv j p n (A.symm a)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  change periodCircleHomologyEquiv j p n (A.symm a) = D.symm (periodCircleHomologyEquiv j p n a)
  apply D.injective
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

private def
    Elliptic.HigherHomology.periodDeckDifference (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j)
    (n : ℕ) :
    SingularMayerVietoris.SingularHomology p.val.Torus n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology p.val.Torus n :=
  LinearMap.id -
    SingularMayerVietoris.singularHomologyMap
      ((periodAffineHomeomorph j p).symm : C(p.val.Torus, p.val.Torus)) n

@[simp]
private theorem Elliptic.HigherHomology.periodDeckDifference_apply (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus n) :
    periodDeckDifference j p n a =
      a -
        SingularMayerVietoris.singularHomologyMap
          ((periodAffineHomeomorph j p).symm : C(p.val.Torus, p.val.Torus)) n a :=
  rfl

private theorem
    Elliptic.HigherHomology.periodCircleHomologyEquiv_periodDeckDifference (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus (n + 1)) :
    periodCircleHomologyEquiv j p n (periodDeckDifference j p (n + 1) a) =
      (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm (n + 1)
          (periodCircleHomologyEquiv j p n a).1,
        MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm n
          (periodCircleHomologyEquiv j p n a).2) := by
  rw [periodDeckDifference_apply, map_sub, periodCircleHomologyEquiv_affine_symm]
  rfl

@[instance_reducible]
private def
    Elliptic.HigherHomology.cokernelProductModule {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] : Module ℤ (M × N) :=
  Prod.instModule

attribute [local instance] Elliptic.HigherHomology.cokernelProductModule in
private def Elliptic.HigherHomology.prodCokernelEquiv {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] M) (g : N →ₗ[ℤ] N) :
    ((M × N) ⧸ LinearMap.range (f.prodMap g)) ≃ₗ[ℤ]
      (M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g) :=
  ((QuotientAddGroup.quotientAddEquivOfEq
          (show
            (LinearMap.range (f.prodMap g)).toAddSubgroup =
              (LinearMap.range f).toAddSubgroup.prod (LinearMap.range g).toAddSubgroup
            from congrArg Submodule.toAddSubgroup (LinearMap.range_prodMap f g))).trans
      (QuotientAddGroup.prodAddEquiv (LinearMap.range f).toAddSubgroup
        (LinearMap.range g).toAddSubgroup)).toIntLinearEquiv

attribute [local instance] Elliptic.HigherHomology.cokernelProductModule in
private theorem
    Elliptic.HigherHomology.triangularFinTwo_apply (F : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)) (d : ℤ)
    (hfirst : F ![1, 0] = ![1, 0]) (hsecond : ∀ v, F v 1 = d * v 1) (v : Fin 2 → ℤ) :
    F v = ![v 0 + (F ![0, 1]) 0 * v 1, d * v 1] := by
  have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp [Pi.add_apply]
  have hF : F v = v 0 • ![1, 0] + v 1 • F ![0, 1] := by
    calc
      F v = F (v 0 • ![1, 0] + v 1 • ![0, 1]) := congrArg F hv
      _ = v 0 • ![1, 0] + v 1 • F ![0, 1] := by rw [map_add, map_smul, map_smul, hfirst]
  ext i
  fin_cases i
  · simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun hF 0
  · exact hsecond v

attribute [local instance] Elliptic.HigherHomology.cokernelProductModule in
public
theorem
    Elliptic.HigherHomology.triangularFinTwo_injective (F : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ))
    (d : ℤ) (hfirst : F ![1, 0] = ![1, 0]) (hsecond : ∀ v, F v 1 = d * v 1) (hd : d ≠ 0) :
    Function.Injective F := by
  intro v w h
  have hm : d * v 1 = d * w 1 := by rw [← hsecond v, ← hsecond w, h]
  have h₁ : v 1 = w 1 := mul_left_cancel₀ hd hm
  rw [triangularFinTwo_apply F d hfirst hsecond v,
    triangularFinTwo_apply F d hfirst hsecond w] at h
  have h₀ := congrFun h 0
  change v 0 + (F ![0, 1]) 0 * v 1 = w 0 + (F ![0, 1]) 0 * w 1 at h₀
  rw [h₁] at h₀
  have h₀' : v 0 = w 0 := add_right_cancel h₀
  ext i
  fin_cases i
  · exact h₀'
  · exact h₁

private abbrev Elliptic.HigherHomology.PeriodDeckCoinvariants (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :=
  SingularMayerVietoris.SingularHomology p.val.Torus n ⧸
    LinearMap.range (periodDeckDifference j p n)

private def Elliptic.HigherHomology.periodDeckCoinvariantsEquivProd (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    PeriodDeckCoinvariants j p (n + 1) ≃ₗ[ℤ]
      ((SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3)
            (n + 1) ⧸
          LinearMap.range
            (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm (n + 1))) ×
        (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n ⧸
          LinearMap.range
            (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm n))) :=
  ((conjugacyCokernelEquiv (periodCircleHomologyEquiv j p n) (periodDeckDifference j p (n + 1))
          (((MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm
                  (n + 1)).toAddMonoidHom.prodMap
              (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm
                  n).toAddMonoidHom).toIntLinearMap)
          (periodCircleHomologyEquiv_periodDeckDifference j p n)).toAddEquiv.trans
      (prodCokernelEquiv
          (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm (n + 1))
          (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm
            n)).toAddEquiv).toIntLinearEquiv

private def Elliptic.HigherHomology.periodDeckCoinvariantsH1Equiv (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : PeriodDeckCoinvariants j p 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((periodDeckCoinvariantsEquivProd j p 0).toAddEquiv.trans
      (((mappingTorusCokernelOneEquiv j).toAddEquiv.prodCongr
            (mappingTorusCokernelZeroEquiv j).toAddEquiv).trans
        (LinearEquiv.finTwoArrow ℤ ℤ).symm.toAddEquiv)).toIntLinearEquiv

private def Elliptic.HigherHomology.periodDeckCoinvariantsH2Equiv (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : PeriodDeckCoinvariants j p 2 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((periodDeckCoinvariantsEquivProd j p 1).toAddEquiv.trans
      (((mappingTorusCokernelTwoEquiv j).toAddEquiv.prodCongr
            (mappingTorusCokernelOneEquiv j).toAddEquiv).trans
        (LinearEquiv.finTwoArrow ℤ ℤ).symm.toAddEquiv)).toIntLinearEquiv

private def Elliptic.HigherHomology.periodDeckCoinvariantsH3Equiv (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : PeriodDeckCoinvariants j p 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((periodDeckCoinvariantsEquivProd j p 2).toAddEquiv.trans
      (((mappingTorusCokernelThreeEquiv j).toAddEquiv.prodCongr
            (mappingTorusCokernelTwoEquiv j).toAddEquiv).trans
        (LinearEquiv.finTwoArrow ℤ ℤ).symm.toAddEquiv)).toIntLinearEquiv

private def Elliptic.HigherHomology.periodDeckCoinvariantsH4Equiv (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : PeriodDeckCoinvariants j p 4 ≃ₗ[ℤ] ℤ := by
  have :=
    PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt (show 3 < 4 by decide)
  letI :
    Unique
      (SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 4 ⧸
        LinearMap.range (MappingTorusHomology.wangDifference (fibreTorusHomeomorph j).symm 4)) :=
    uniqueOfSubsingleton 0
  exact
    ((periodDeckCoinvariantsEquivProd j p 3).toAddEquiv.trans
        (AddEquiv.uniqueProd.trans
          (mappingTorusCokernelThreeEquiv j).toAddEquiv)).toIntLinearEquiv

@[simp]
private theorem Elliptic.HigherHomology.periodDeckCoinvariantsH1Equiv_mk (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (a : SingularMayerVietoris.SingularHomology p.val.Torus 1) :
    periodDeckCoinvariantsH1Equiv j p (Submodule.Quotient.mk a) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv (periodCircleHomologyEquiv j p 0 a).1),
        torusH0Coordinates (periodCircleHomologyEquiv j p 0 a).2] :=
  rfl

@[simp]
private theorem Elliptic.HigherHomology.periodDeckCoinvariantsH2Equiv_mk (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (a : SingularMayerVietoris.SingularHomology p.val.Torus 2) :
    periodDeckCoinvariantsH2Equiv j p (Submodule.Quotient.mk a) =
      ![torusH2Coordinates (periodCircleHomologyEquiv j p 1 a).1 0,
        fibreCoinvariantCoordinate j (torusH1Equiv (periodCircleHomologyEquiv j p 1 a).2)] :=
  rfl

@[simp]
private theorem Elliptic.HigherHomology.periodDeckCoinvariantsH3Equiv_mk (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (a : SingularMayerVietoris.SingularHomology p.val.Torus 3) :
    periodDeckCoinvariantsH3Equiv j p (Submodule.Quotient.mk a) =
      ![torusH3Coordinates (periodCircleHomologyEquiv j p 2 a).1,
        torusH2Coordinates (periodCircleHomologyEquiv j p 2 a).2 0] :=
  rfl

@[simp]
private theorem Elliptic.HigherHomology.periodDeckCoinvariantsH4Equiv_mk (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (a : SingularMayerVietoris.SingularHomology p.val.Torus 4) :
    periodDeckCoinvariantsH4Equiv j p (Submodule.Quotient.mk a) =
      torusH3Coordinates (periodCircleHomologyEquiv j p 3 a).2 :=
  rfl

private theorem Elliptic.HigherHomology.periodDeckCoinvariantsH1Equiv_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    periodDeckCoinvariantsH1Equiv j p
        (Submodule.Quotient.mk
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 1 a)) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] := by
  simp only [periodDeckCoinvariantsH1Equiv_mk, periodCircleHomologyEquiv_fibre, map_zero]

private theorem Elliptic.HigherHomology.periodDeckCoinvariantsH2Equiv_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    periodDeckCoinvariantsH2Equiv j p
        (Submodule.Quotient.mk
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 2 a)) =
      ![torusH2Coordinates a 0, 0] := by
  simp only [periodDeckCoinvariantsH2Equiv_mk, periodCircleHomologyEquiv_fibre, map_zero]

private theorem Elliptic.HigherHomology.periodDeckCoinvariantsH3Equiv_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    periodDeckCoinvariantsH3Equiv j p
        (Submodule.Quotient.mk
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 3 a)) =
      ![torusH3Coordinates a, 0] := by
  simp only [periodDeckCoinvariantsH3Equiv_mk, periodCircleHomologyEquiv_fibre, map_zero,
    Pi.zero_apply]

private theorem Elliptic.HigherHomology.periodCover_affine_eq (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : p.val.Torus) :
    periodCover j p v hv (Elliptic.affineBiholomorph j p v x) = periodCover j p v hv x := by
  let := Elliptic.affineAction j p v hv.1
  rw [← Elliptic.affineAction_generator_smul j p v hv.1 x]
  exact
    Elliptic.FiniteQuotient.project_smul (Elliptic.CyclicGroup j) p.val.Torus
      (Elliptic.CyclicAction.generator j.order) x

private theorem Elliptic.HigherHomology.periodCover_affine_symm_eq (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v)
    (x : p.val.Torus) :
    periodCover j p v hv ((Elliptic.affineBiholomorph j p v).toHomeomorph.symm x) =
      periodCover j p v hv x := by
  have h :=
    periodCover_affine_eq j p v hv ((Elliptic.affineBiholomorph j p v).toHomeomorph.symm x)
  change
    periodCover j p v hv
        ((Elliptic.affineBiholomorph j p v).toHomeomorph
          ((Elliptic.affineBiholomorph j p v).toHomeomorph.symm x)) =
      _ at h
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

private theorem Elliptic.HigherHomology.periodCover_comp_affine_symm (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) :
    (periodCover j p v hv).comp
        ((Elliptic.affineBiholomorph j p v).toHomeomorph.symm : C(p.val.Torus, p.val.Torus)) =
      periodCover j p v hv := by
  ext x
  exact periodCover_affine_symm_eq j p v hv x

private theorem Elliptic.HigherHomology.periodCover_homology_affine_symm_comp (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (periodCover j p v hv) n).comp
        (SingularMayerVietoris.singularHomologyMap
          ((Elliptic.affineBiholomorph j p v).toHomeomorph.symm : C(p.val.Torus, p.val.Torus))
          n) =
      SingularMayerVietoris.singularHomologyMap (periodCover j p v hv) n := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, periodCover_comp_affine_symm]

private theorem
    Elliptic.HigherHomology.periodCover_homology_comp_affineDifference (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (v : Lattice) (hv : Elliptic.AdmissibleTwist j v) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (periodCover j p v hv) n).comp
        (LinearMap.id -
          SingularMayerVietoris.singularHomologyMap
            ((Elliptic.affineBiholomorph j p v).toHomeomorph.symm : C(p.val.Torus, p.val.Torus))
            n) =
      0 := by
  rw [LinearMap.comp_sub, LinearMap.comp_id, periodCover_homology_affine_symm_comp, sub_self]

private theorem
    Elliptic.HigherHomology.periodCover_homology_comp_periodDeckDifference (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n).comp
        (periodDeckDifference j p n) =
      0 :=
  periodCover_homology_comp_affineDifference j p j.twist (Elliptic.mainTwist_admissible j) n

private theorem
    Elliptic.HigherHomology.periodCover_homology_periodDeckDifference (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus n) :
    SingularMayerVietoris.singularHomologyMap
        (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n
        (periodDeckDifference j p n a) =
      0 :=
  DFunLike.congr_fun (periodCover_homology_comp_periodDeckDifference j p n) a

private theorem
    Elliptic.HigherHomology.periodDeckDifference_range_le_periodCover_ker (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    LinearMap.range (periodDeckDifference j p n) ≤
      LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n) := by
  rintro a ⟨b, rfl⟩
  exact periodCover_homology_periodDeckDifference j p n b

private def Elliptic.HigherHomology.periodCoverFromDeckCoinvariants (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    (SingularMayerVietoris.SingularHomology p.val.Torus n ⧸
        LinearMap.range (periodDeckDifference j p n)) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology
        (Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) n
    where
  toFun :=
    (LinearMap.range (periodDeckDifference j p n)).liftQ
      (SingularMayerVietoris.singularHomologyMap
        (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n)
      (periodDeckDifference_range_le_periodCover_ker j p n)
  map_add' a b := map_add _ a b
  map_smul' r
    a := by
    let f :=
      (LinearMap.range (periodDeckDifference j p n)).liftQ
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n)
        (periodDeckDifference_range_le_periodCover_ker j p n)
    change
      f (r • a) =
        (SingularMayerVietoris.SingularHomology
              (Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) n).isModule.smul
          r (f a)
    rw [int_smul_eq_zsmul]
    exact map_zsmul f r a

@[simp]
private theorem Elliptic.HigherHomology.periodCoverFromDeckCoinvariants_mk (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus n) :
    periodCoverFromDeckCoinvariants j p n (Submodule.Quotient.mk a) =
      SingularMayerVietoris.singularHomologyMap
        (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n a :=
  rfl

private def Elliptic.HigherHomology.periodCoverCoinvariantH1Map (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH1Equiv j p).toLinearMap.comp
    ((periodCoverFromDeckCoinvariants j p 1).comp
      (periodDeckCoinvariantsH1Equiv j p).symm.toLinearMap)

private def Elliptic.HigherHomology.periodCoverCoinvariantH2Map (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH2Equiv j p).toLinearMap.comp
    ((periodCoverFromDeckCoinvariants j p 2).comp
      (periodDeckCoinvariantsH2Equiv j p).symm.toLinearMap)

private def Elliptic.HigherHomology.periodCoverCoinvariantH3Map (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH3Equiv j p).toLinearMap.comp
    ((periodCoverFromDeckCoinvariants j p 3).comp
      (periodDeckCoinvariantsH3Equiv j p).symm.toLinearMap)

private theorem Elliptic.HigherHomology.periodCoverCoinvariantH1Map_firstAxis (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (t : ℤ) : periodCoverCoinvariantH1Map j p ![t, 0] = ![t, 0] := by
  obtain ⟨v, hv⟩ := fibreCoinvariantCoordinate_surjective j t
  let a := torusH1Equiv.symm v
  have ha : fibreCoinvariantCoordinate j (torusH1Equiv a) = t := by
    simpa only [a, LinearEquiv.apply_symm_apply] using hv
  have hs :
    periodDeckCoinvariantsH1Equiv j p
        (Submodule.Quotient.mk
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 1 a)) =
      ![t, 0] := by rw [periodDeckCoinvariantsH1Equiv_fibre, ha]
  change
    surfaceH1Equiv j p
        (periodCoverFromDeckCoinvariants j p 1
          ((periodDeckCoinvariantsH1Equiv j p).symm ![t, 0])) =
      _
  conv_lhs => rw [← hs]
  rw [LinearEquiv.symm_apply_apply, periodCoverFromDeckCoinvariants_mk,
    surfaceH1Equiv_periodCover_fibre, ha]

private theorem Elliptic.HigherHomology.periodCoverCoinvariantH2Map_firstAxis (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (t : ℤ) : periodCoverCoinvariantH2Map j p ![t, 0] = ![t, 0] := by
  let a := torusH2Coordinates.symm ![t, 0, 0]
  have ha : torusH2Coordinates a 0 = t := by
    rw [show a = torusH2Coordinates.symm ![t, 0, 0] from rfl, LinearEquiv.apply_symm_apply]
    rfl
  have hs :
    periodDeckCoinvariantsH2Equiv j p
        (Submodule.Quotient.mk
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 2 a)) =
      ![t, 0] := by rw [periodDeckCoinvariantsH2Equiv_fibre, ha]
  change
    surfaceH2Equiv j p
        (periodCoverFromDeckCoinvariants j p 2
          ((periodDeckCoinvariantsH2Equiv j p).symm ![t, 0])) =
      _
  conv_lhs => rw [← hs]
  rw [LinearEquiv.symm_apply_apply, periodCoverFromDeckCoinvariants_mk,
    surfaceH2Equiv_periodCover_fibre, ha]

private theorem Elliptic.HigherHomology.periodCoverCoinvariantH3Map_firstAxis (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (t : ℤ) : periodCoverCoinvariantH3Map j p ![t, 0] = ![t, 0] := by
  let a := torusH3Coordinates.symm t
  have ha : torusH3Coordinates a = t := LinearEquiv.apply_symm_apply _ t
  have hs :
    periodDeckCoinvariantsH3Equiv j p
        (Submodule.Quotient.mk
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 3 a)) =
      ![t, 0] := by rw [periodDeckCoinvariantsH3Equiv_fibre, ha]
  change
    surfaceH3Equiv j p
        (periodCoverFromDeckCoinvariants j p 3
          ((periodDeckCoinvariantsH3Equiv j p).symm ![t, 0])) =
      _
  conv_lhs => rw [← hs]
  rw [LinearEquiv.symm_apply_apply, periodCoverFromDeckCoinvariants_mk,
    surfaceH3Equiv_periodCover_fibre, ha]

private theorem
    Elliptic.HigherHomology.periodCoverFromDeckCoinvariants_h1_second (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (a : PeriodDeckCoinvariants j p 1) :
    surfaceH1Equiv j p (periodCoverFromDeckCoinvariants j p 1 a) 1 =
      (j.order : ℤ) * periodDeckCoinvariantsH1Equiv j p a 1 := by
  obtain ⟨b, rfl⟩ :=
    Submodule.Quotient.mk_surjective (LinearMap.range (periodDeckDifference j p 1)) a
  rw [periodCoverFromDeckCoinvariants_mk, periodDeckCoinvariantsH1Equiv_mk]
  change
    surfacePeriodCoverH1Coordinates j p b 1 =
      (j.order : ℤ) * torusH0Coordinates (surfacePeriodCoverCircleBoundary j p 0 b)
  have h := DFunLike.congr_fun (surfacePeriodCoverH1Coordinates_secondMap j p) b
  change
    surfacePeriodCoverH1Coordinates j p b 1 =
      fibreHomologyNormZeroCoordinate j (surfacePeriodCoverCircleBoundary j p 0 b) at h
  rw [h, fibreHomologyNormZeroCoordinate_apply]

private theorem
    Elliptic.HigherHomology.periodCoverFromDeckCoinvariants_h2_second (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (a : PeriodDeckCoinvariants j p 2) :
    surfaceH2Equiv j p (periodCoverFromDeckCoinvariants j p 2 a) 1 =
      (fibreNormIndex j : ℤ) * periodDeckCoinvariantsH2Equiv j p a 1 := by
  obtain ⟨b, rfl⟩ :=
    Submodule.Quotient.mk_surjective (LinearMap.range (periodDeckDifference j p 2)) a
  rw [periodCoverFromDeckCoinvariants_mk, periodDeckCoinvariantsH2Equiv_mk]
  change
    surfacePeriodCoverH2Coordinates j p b 1 =
      (fibreNormIndex j : ℤ) *
        fibreCoinvariantCoordinate j (torusH1Equiv (surfacePeriodCoverCircleBoundary j p 1 b))
  have h := DFunLike.congr_fun (surfacePeriodCoverH2Coordinates_secondMap j p) b
  change
    surfacePeriodCoverH2Coordinates j p b 1 =
      fibreHomologyNormOneCoordinate j (surfacePeriodCoverCircleBoundary j p 1 b) at h
  rw [h, fibreHomologyNormOneCoordinate_apply]

private theorem
    Elliptic.HigherHomology.periodCoverFromDeckCoinvariants_h3_second (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (a : PeriodDeckCoinvariants j p 3) :
    surfaceH3Equiv j p (periodCoverFromDeckCoinvariants j p 3 a) 1 =
      (fibreNormIndex j : ℤ) * periodDeckCoinvariantsH3Equiv j p a 1 := by
  obtain ⟨b, rfl⟩ :=
    Submodule.Quotient.mk_surjective (LinearMap.range (periodDeckDifference j p 3)) a
  rw [periodCoverFromDeckCoinvariants_mk, periodDeckCoinvariantsH3Equiv_mk]
  change
    surfacePeriodCoverH3Coordinates j p b 1 =
      (fibreNormIndex j : ℤ) * torusH2Coordinates (surfacePeriodCoverCircleBoundary j p 2 b) 0
  have h := DFunLike.congr_fun (surfacePeriodCoverH3Coordinates_secondMap j p) b
  change
    surfacePeriodCoverH3Coordinates j p b 1 =
      fibreHomologyNormTwoCoordinate j (surfacePeriodCoverCircleBoundary j p 2 b) at h
  rw [h, fibreHomologyNormTwoCoordinate_apply]

private theorem Elliptic.HigherHomology.periodCoverCoinvariantH1Map_second (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH1Map j p v 1 = (j.order : ℤ) * v 1 := by
  change
    surfaceH1Equiv j p
        (periodCoverFromDeckCoinvariants j p 1 ((periodDeckCoinvariantsH1Equiv j p).symm v)) 1 =
      _
  rw [periodCoverFromDeckCoinvariants_h1_second, LinearEquiv.apply_symm_apply]

private theorem Elliptic.HigherHomology.periodCoverCoinvariantH2Map_second (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH2Map j p v 1 = (fibreNormIndex j : ℤ) * v 1 := by
  change
    surfaceH2Equiv j p
        (periodCoverFromDeckCoinvariants j p 2 ((periodDeckCoinvariantsH2Equiv j p).symm v)) 1 =
      _
  rw [periodCoverFromDeckCoinvariants_h2_second, LinearEquiv.apply_symm_apply]

private theorem Elliptic.HigherHomology.periodCoverCoinvariantH3Map_second (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (v : Fin 2 → ℤ) :
    periodCoverCoinvariantH3Map j p v 1 = (fibreNormIndex j : ℤ) * v 1 := by
  change
    surfaceH3Equiv j p
        (periodCoverFromDeckCoinvariants j p 3 ((periodDeckCoinvariantsH3Equiv j p).symm v)) 1 =
      _
  rw [periodCoverFromDeckCoinvariants_h3_second, LinearEquiv.apply_symm_apply]

private theorem Elliptic.HigherHomology.periodCoverCoinvariantH1Map_injective (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : Function.Injective (periodCoverCoinvariantH1Map j p) :=
  triangularFinTwo_injective _ _ (periodCoverCoinvariantH1Map_firstAxis j p 1)
    (periodCoverCoinvariantH1Map_second j p) (by exact_mod_cast j.order_pos.ne')

private theorem Elliptic.HigherHomology.periodCoverCoinvariantH2Map_injective (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : Function.Injective (periodCoverCoinvariantH2Map j p) :=
  triangularFinTwo_injective _ _ (periodCoverCoinvariantH2Map_firstAxis j p 1)
    (periodCoverCoinvariantH2Map_second j p) (by exact_mod_cast (fibreNormIndex_pos j).ne')

private theorem Elliptic.HigherHomology.periodCoverCoinvariantH3Map_injective (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : Function.Injective (periodCoverCoinvariantH3Map j p) :=
  triangularFinTwo_injective _ _ (periodCoverCoinvariantH3Map_firstAxis j p 1)
    (periodCoverCoinvariantH3Map_second j p) (by exact_mod_cast (fibreNormIndex_pos j).ne')

private theorem
    Elliptic.HigherHomology.periodCoverFromDeckCoinvariants_h1_injective (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : Function.Injective (periodCoverFromDeckCoinvariants j p 1) := by
  intro a b h
  apply (periodDeckCoinvariantsH1Equiv j p).injective
  apply periodCoverCoinvariantH1Map_injective j p
  change
    surfaceH1Equiv j p
        (periodCoverFromDeckCoinvariants j p 1
          ((periodDeckCoinvariantsH1Equiv j p).symm (periodDeckCoinvariantsH1Equiv j p a))) =
      surfaceH1Equiv j p
        (periodCoverFromDeckCoinvariants j p 1
          ((periodDeckCoinvariantsH1Equiv j p).symm (periodDeckCoinvariantsH1Equiv j p b)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, h]

private theorem
    Elliptic.HigherHomology.periodCoverFromDeckCoinvariants_h2_injective (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : Function.Injective (periodCoverFromDeckCoinvariants j p 2) := by
  intro a b h
  apply (periodDeckCoinvariantsH2Equiv j p).injective
  apply periodCoverCoinvariantH2Map_injective j p
  change
    surfaceH2Equiv j p
        (periodCoverFromDeckCoinvariants j p 2
          ((periodDeckCoinvariantsH2Equiv j p).symm (periodDeckCoinvariantsH2Equiv j p a))) =
      surfaceH2Equiv j p
        (periodCoverFromDeckCoinvariants j p 2
          ((periodDeckCoinvariantsH2Equiv j p).symm (periodDeckCoinvariantsH2Equiv j p b)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, h]

private theorem
    Elliptic.HigherHomology.periodCoverFromDeckCoinvariants_h3_injective (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : Function.Injective (periodCoverFromDeckCoinvariants j p 3) := by
  intro a b h
  apply (periodDeckCoinvariantsH3Equiv j p).injective
  apply periodCoverCoinvariantH3Map_injective j p
  change
    surfaceH3Equiv j p
        (periodCoverFromDeckCoinvariants j p 3
          ((periodDeckCoinvariantsH3Equiv j p).symm (periodDeckCoinvariantsH3Equiv j p a))) =
      surfaceH3Equiv j p
        (periodCoverFromDeckCoinvariants j p 3
          ((periodDeckCoinvariantsH3Equiv j p).symm (periodDeckCoinvariantsH3Equiv j p b)))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply, h]

private theorem
    Elliptic.HigherHomology.periodCoverFromDeckCoinvariants_h4_coordinate (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (a : PeriodDeckCoinvariants j p 4) :
    surfaceH4Equiv j p (periodCoverFromDeckCoinvariants j p 4 a) =
      (j.order : ℤ) * periodDeckCoinvariantsH4Equiv j p a := by
  obtain ⟨b, rfl⟩ :=
    Submodule.Quotient.mk_surjective (LinearMap.range (periodDeckDifference j p 4)) a
  rw [periodCoverFromDeckCoinvariants_mk, periodDeckCoinvariantsH4Equiv_mk]
  change
    surfacePeriodCoverH4Coordinates j p b =
      (j.order : ℤ) * torusH3Coordinates (surfacePeriodCoverCircleBoundary j p 3 b)
  exact surfacePeriodCoverH4Coordinates_apply j p b

private theorem
    Elliptic.HigherHomology.periodCoverFromDeckCoinvariants_h4_injective (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : Function.Injective (periodCoverFromDeckCoinvariants j p 4) := by
  intro a b h
  apply (periodDeckCoinvariantsH4Equiv j p).injective
  apply mul_left_cancel₀ (show (j.order : ℤ) ≠ 0 by exact_mod_cast j.order_pos.ne')
  rw [← periodCoverFromDeckCoinvariants_h4_coordinate, ←
    periodCoverFromDeckCoinvariants_h4_coordinate, h]

private theorem
  Elliptic.HigherHomology.periodCover_ker_eq_deckDifference_range_of_injective_mo1973_29635
    (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) (n : ℕ)
    (h : Function.Injective (periodCoverFromDeckCoinvariants j p n)) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n) =
      LinearMap.range (periodDeckDifference j p n) := by
  apply le_antisymm _ (periodDeckDifference_range_le_periodCover_ker j p n)
  intro a ha
  apply (Submodule.Quotient.mk_eq_zero (LinearMap.range (periodDeckDifference j p n))).mp
  apply h
  rw [periodCoverFromDeckCoinvariants_mk, map_zero]
  exact ha

private theorem
    Elliptic.HigherHomology.periodCover_h1_ker_eq_deckDifference_range (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 1) =
      LinearMap.range (periodDeckDifference j p 1) :=
  periodCover_ker_eq_deckDifference_range_of_injective_mo1973_29635 j p 1
    (periodCoverFromDeckCoinvariants_h1_injective j p)

private theorem
    Elliptic.HigherHomology.periodCover_h2_ker_eq_deckDifference_range (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 2) =
      LinearMap.range (periodDeckDifference j p 2) :=
  periodCover_ker_eq_deckDifference_range_of_injective_mo1973_29635 j p 2
    (periodCoverFromDeckCoinvariants_h2_injective j p)

private theorem
    Elliptic.HigherHomology.periodCover_h3_ker_eq_deckDifference_range (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 3) =
      LinearMap.range (periodDeckDifference j p 3) :=
  periodCover_ker_eq_deckDifference_range_of_injective_mo1973_29635 j p 3
    (periodCoverFromDeckCoinvariants_h3_injective j p)

private theorem
    Elliptic.HigherHomology.periodCover_h4_ker_eq_deckDifference_range (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 4) =
      LinearMap.range (periodDeckDifference j p 4) :=
  periodCover_ker_eq_deckDifference_range_of_injective_mo1973_29635 j p 4
    (periodCoverFromDeckCoinvariants_h4_injective j p)

private theorem Elliptic.HigherHomology.periodCover_h0_injective (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap
        (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 0) := by
  intro a b hab
  apply (PeriodTorusHigherHomology.connectedHomologyZeroEquiv p.val.Torus).injective
  have h :=
    congrArg
      (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
        (Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)))
      hab
  exact
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) a).symm.trans
      (h.trans
        (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) b))

private theorem Elliptic.HigherHomology.periodDeckDifference_zero (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : periodDeckDifference j p 0 = 0 := by
  ext a
  rw [periodDeckDifference_apply]
  apply sub_eq_zero.mpr
  apply (PeriodTorusHigherHomology.connectedHomologyZeroEquiv p.val.Torus).injective
  exact
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural
        ((periodAffineHomeomorph j p).symm : C(p.val.Torus, p.val.Torus)) a).symm

private theorem
    Elliptic.HigherHomology.periodCover_h0_ker_eq_deckDifference_range (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 0) =
      LinearMap.range (periodDeckDifference j p 0) := by
  rw [LinearMap.ker_eq_bot.mpr (periodCover_h0_injective j p), periodDeckDifference_zero,
    LinearMap.range_zero]

end Mathoverflow1973

end
