/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Recognition.Degree3
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology1
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology2
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Recognition.Degree1
import all LeanPool.HopfProblem.Recognition.Smale6
import all LeanPool.HopfProblem.Recognition.Smale7
import all LeanPool.HopfProblem.Recognition.Smale8
import all LeanPool.HopfProblem.Recognition.Smale9
import all LeanPool.HopfProblem.Recognition.Smale10
import all LeanPool.HopfProblem.Recognition.Smale11
import all LeanPool.HopfProblem.Recognition.Smale12
import all LeanPool.HopfProblem.MainTheorem.SixSphereCube3
import all LeanPool.HopfProblem.Recognition.Degree3

/-!
# Hopf problem: recognition · smale 13

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

private theorem MorseCancel.exists_native_prescribed_centered_passage {E M Z : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    [TopologicalSpace Z] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) Z] [IsManifold (𝓡 2) ∞ Z]
    [SecondCountableTopology Z] (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (α : C((Smale.Hemisphere.Sphere 2), d.UpperLevel)) (hαe : Topology.IsEmbedding α)
    (hdisj : Disjoint (Set.range α) (Set.range d.surgery.beltSphere)) (b : Z → d.UpperLevel)
    (hbc : IsClosed (Set.range b)) (x : (Smale.Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1) (hx : α x ∉ Set.range b)
    (hv : d.surgery.beltSphere v ∉ Set.range b) (γ : Path (α x) (d.surgery.beltSphere v)) (k : ℤ)
    (hk : k = 1 ∨ k = -1) :
    let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α →
      (∀ z, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) α z)) →
        ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ b →
          ∃ A :
            CenteredSheetPassage (Smale.RegularLevel.Model E) α d.surgery.beltSphere x v
              (Set.range b),
            ∃ L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates,
              HasFDerivAt
                  (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                    d.beltNormal
                      (A.family
                        ((radialParameterChart (1 / 2) x z).1,
                          α (radialParameterChart (1 / 2) x z).2)))
                  L.toContinuousLinearMap 0 ∧
                SingularMayerVietoris.singularHomologyMap
                    (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
                  k •
                    SingularMayerVietoris.singularHomologyMap
                      ((Smale.SphereCoordinates.standardParametrization
                            d.chart.NegativeCoordinates 2).toHomeomorph :
                        C((Smale.Hemisphere.Sphere 2),
                          Metric.sphere (0 : d.chart.NegativeCoordinates) 1))
                      2 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro hα hαi hb
  obtain ⟨A₀, A₁, L₀, L₁, hL₀, hL₁, hdet⟩ :=
    exists_native_opposite_centered_passages d hf hdim α hαe hdisj b hbc x v hx hv γ hα hαi hb
  exact
    choose_prescribed_normal_passage d.beltNormal
      (Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates 2).toHomeomorph
      A₀ A₁ L₀ L₁ hL₀ hL₁ hdet k hk

private theorem MorseCancel.exists_native_prescribed_finite_family_passage {ι E M : Type} [Finite ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 2 + 1)]
    [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 2 + 1)]
    (a : ι → C((Smale.Hemisphere.Sphere 2), d.UpperLevel))
    (hpair : Pairwise (fun j k => Disjoint (Set.range (a j)) (Set.range (a k)))) (i : ι)
    (hfe : Topology.IsEmbedding (a i))
    (hdisj : Disjoint (Set.range (a i)) (Set.range d.surgery.beltSphere))
    (x : (Smale.Hemisphere.Sphere 2)) (v : Metric.sphere (0 : d.chart.PositiveCoordinates) 1)
    (hv : d.surgery.beltSphere v ∉ Degree.MorseRearrangement.otherSheetImages (fun j => a j) i)
    (γ : Path (a i x) (d.surgery.beltSphere v)) (k : ℤ) (hk : k = 1 ∨ k = -1) :
    let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
    (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (a j)) →
      (∀ z, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (a i) z)) →
        ∃ A :
          CenteredSheetPassage (Smale.RegularLevel.Model E) (a i) d.surgery.beltSphere x v
            (Degree.MorseRearrangement.otherSheetImages (fun j => a j) i),
          ∃ L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] d.chart.NegativeCoordinates,
            HasFDerivAt
                (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                  d.beltNormal
                    (A.family
                      ((radialParameterChart (1 / 2) x z).1,
                        a i (radialParameterChart (1 / 2) x z).2)))
                L.toContinuousLinearMap 0 ∧
              SingularMayerVietoris.singularHomologyMap
                  (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
                k •
                  SingularMayerVietoris.singularHomologyMap
                    ((Smale.SphereCoordinates.standardParametrization d.chart.NegativeCoordinates
                          2).toHomeomorph :
                      C((Smale.Hemisphere.Sphere 2),
                        Metric.sphere (0 : d.chart.NegativeCoordinates) 1))
                    2 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  dsimp only
  intro ha hfi
  obtain ⟨n, b, hb, hbrange⟩ :=
    Degree.MorseRearrangement.exists_sheetSumMap_for_finite_family
      (fun j : { j : ι // j ≠ i } => a j.val) (fun j => ha j.val)
  have hrange : Set.range b = Degree.MorseRearrangement.otherSheetImages (fun j => a j) i :=
    hbrange
  have hbc : IsClosed (Set.range b) := (isCompact_range hb.continuous).isClosed
  have hx : a i x ∉ Set.range b := by
    rw [hrange]
    intro hx
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hpair (Ne.symm j.property)) (Set.mem_range_self x) hj
  have hvb : d.surgery.beltSphere v ∉ Set.range b := by rwa [hrange]
  obtain ⟨A, L, hL, hunit⟩ :=
    exists_native_prescribed_centered_passage d hf hdim (a i) hfe hdisj b hbc x v hx hvb γ k hk
      (ha i) hfi hb
  let A' :
    CenteredSheetPassage (Smale.RegularLevel.Model E) (a i) d.surgery.beltSphere x v
      (Degree.MorseRearrangement.otherSheetImages (fun j => a j) i) :=
    { A with avoids := by rw [← hrange]; exact A.avoids }
  exact ⟨A', L, hL, hunit⟩

private theorem
    AdaptedWindows.exists_higher_family_prescribed_passage {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) (haq : a < f q)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) (k : ℤ)
    (hk : k = 1 ∨ k = -1) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by
        have hsplit := (S.data q).chart.finrank_negative_add_positive
        have hn := (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
        omega⟩
    let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
      ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
    ∃ β : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).UpperLevel),
      MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => β j) ∧
        (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
          (∀ j, Disjoint (Set.range (β j)) (Set.range (S.data q).surgery.beltSphere)) ∧
            ∃ (x : (Smale.Hemisphere.Sphere 2)) (v :
              Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1),
              ∃ A :
                MorseCancel.CenteredSheetPassage (Smale.RegularLevel.Model E) (β i)
                  (S.data q).surgery.beltSphere x v
                  (Degree.MorseRearrangement.otherSheetImages (fun j => β j) i),
                ∃ L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (S.data q).chart.NegativeCoordinates,
                  HasFDerivAt
                      (fun z : (EuclideanSpace ℝ (Fin 3)) =>
                        (S.data q).beltNormal
                          (A.family
                            ((MorseCancel.radialParameterChart (1 / 2) x z).1,
                              β i (MorseCancel.radialParameterChart (1 / 2) x z).2)))
                      L.toContinuousLinearMap 0 ∧
                    SingularMayerVietoris.singularHomologyMap
                        (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective)
                        2 =
                      k •
                        SingularMayerVietoris.singularHomologyMap
                          ((Smale.SphereCoordinates.standardParametrization
                                (S.data q).chart.NegativeCoordinates 2).toHomeomorph :
                            C((Smale.Hemisphere.Sphere 2),
                              Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1))
                          2 := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := Smale.RegularLevel.isManifold hf (S.data q).upper_regular
  let _ : CompactSpace (S.data q).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by
      have hsplit := (S.data q).chart.finrank_negative_add_positive
      have hn := (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
      omega⟩
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  obtain ⟨β₀, hβ₀, horbit₀⟩ :=
    S.exists_higher_middle_family hf (haq.trans (S.toSurgeryWindows.value_lt_upper q)) ha
      (S.data q).upper_regular p i hp hhigh α hα
  let β : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).UpperLevel) := β₀
  have hβ :
    MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => β j) := hβ₀
  have horbit : ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := horbit₀
  have hdisj (j : Fin n) : Disjoint (Set.range (β j)) (Set.range (S.data q).surgery.beltSphere) :=
    by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ hy
    exact S.upper_point_not_on_belt_of_lower_orbit hf q haq (α j x) (β j x) (horbit j x) hy
  let x : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  let v :=
    Smale.SphereCoordinates.standardParametrization (S.data q).chart.PositiveCoordinates 2 x
  have hv :
    (S.data q).surgery.beltSphere v ∉
      Degree.MorseRearrangement.otherSheetImages (fun j => β j) i := by
    intro h
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp h
    exact Set.disjoint_left.mp (hdisj j.val) hj (Set.mem_range_self v)
  let _ : PathConnectedSpace (S.data q).UpperLevel :=
    S.pathConnectedSpace_index_three_upper_level hf hdim horder q hq (β i x)
  obtain ⟨A, L, hL, hunit⟩ :=
    MorseCancel.exists_native_prescribed_finite_family_passage (S.data q) hf hdim β hβ.2.2.2.1 i
      (hβ.2.1 i).isEmbedding (hdisj i) x v hv
      (PathConnectedSpace.somePath (β i x) ((S.data q).surgery.beltSphere v)) k hk hβ.1
      (hβ.2.2.1 i)
  exact ⟨β, hβ, horbit, hdisj, x, v, A, L, hL, hunit⟩

private theorem AdaptedWindows.prescribed_passage_actual_endpoint_classes {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    [Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1)]
    (H : C(ℝ × (Smale.Hemisphere.Sphere 2), (S.data q).UpperLevel)) {τ : ℝ}
    (hτ : τ ∈ Set.Ioo (0 : ℝ) 1) (x₀ : (Smale.Hemisphere.Sphere 2))
    (v : Metric.sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hpoint : (S.data q).surgery.beltSphere v = H (τ, x₀))
    (hcross :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ x : (Smale.Hemisphere.Sphere 2),
          H (t, x) ∈ Set.range (S.data q).surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (β δ : C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel))
    (hβ : ∀ x, ∃ t : ℝ, S.flow t (H (0, x)).val = (β x).val)
    (hδ : ∀ x, ∃ t : ℝ, S.flow t (H (1, x)).val = (δ x).val) (k : ℤ)
    (L : (EuclideanSpace ℝ (Fin 3)) ≃L[ℝ] (S.data q).chart.NegativeCoordinates)
    (hL :
      HasFDerivAt
        (fun z : (EuclideanSpace ℝ (Fin 3)) =>
          (S.data q).beltNormal (H (MorseCancel.radialParameterChart τ x₀ z)))
        L.toContinuousLinearMap 0)
    (hunit :
      SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective) 2 =
        k •
          SingularMayerVietoris.singularHomologyMap
            ((Smale.SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates
                  2).toHomeomorph :
              C((Smale.Hemisphere.Sphere 2),
                Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1))
            2) :
    let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ H (τ, x₀) →
      SingularMayerVietoris.singularHomologyMap δ 2 =
        SingularMayerVietoris.singularHomologyMap β 2 +
          k •
            SingularMayerVietoris.singularHomologyMap
              (MorseCancel.nativeIndexThreeAttachingSphere S q hq) 2 := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  dsimp only
  intro hH
  obtain ⟨D, _, hunique, hrelation⟩ :=
    S.exists_passage_derivative_class_addition hf q H hτ x₀ v hpoint hcross L hL hH
  let G :=
    D.comp
      (Degree.PassageHomology.puncturedPassageTrace H (Set.range (S.data q).surgery.beltSphere) hτ
        x₀ hcross)
  have hmap (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) (hsτ : s ≠ τ)
    (σ : C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel))
    (hσ : ∀ x, ∃ t : ℝ, S.flow t (H (s, x)).val = (σ x).val) :
    G.comp (Degree.PassageHomology.cylinderSlice τ x₀ s hsτ) = σ := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨t, ht⟩ := hσ x
    apply hunique _ (σ x) t
    have heq :=
      Degree.PassageHomology.puncturedPassageTrace_on_interval H
        (Set.range (S.data q).surgery.beltSphere) hτ x₀ hcross
        (Degree.PassageHomology.cylinderSlice τ x₀ s hsτ x) hs
    change
      S.flow t
          (Degree.PassageHomology.puncturedPassageTrace H
              (Set.range (S.data q).surgery.beltSphere) hτ x₀ hcross
              (Degree.PassageHomology.cylinderSlice τ x₀ s hsτ x)).val.val =
        (σ x).val
    rw [heq]
    exact ht
  have hzero := hmap 0 ⟨le_rfl, zero_le_one⟩ hτ.1.ne β hβ
  have hone := hmap 1 ⟨zero_le_one, le_rfl⟩ hτ.2.ne' δ hδ
  have hcoef :
    SingularMayerVietoris.singularHomologyMap
        ((S.data q).surgery.attachingSphere.comp
          (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
        2 =
      k •
        SingularMayerVietoris.singularHomologyMap
          (MorseCancel.nativeIndexThreeAttachingSphere S q hq) 2 := by
    change
      SingularMayerVietoris.singularHomologyMap
          ((S.data q).surgery.attachingSphere.comp
            (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
          2 =
        k •
          SingularMayerVietoris.singularHomologyMap
            ((S.data q).surgery.attachingSphere.comp
              ((Smale.SphereCoordinates.standardParametrization
                    (S.data q).chart.NegativeCoordinates 2).toHomeomorph :
                C((Smale.Hemisphere.Sphere 2),
                  Metric.sphere (0 : (S.data q).chart.NegativeCoordinates) 1)))
            2
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
      PeriodTorusHigherHomology.singularHomologyMap_comp, hunit]
    apply LinearMap.ext
    intro a
    exact
      map_zsmul (SingularMayerVietoris.singularHomologyMap (S.data q).surgery.attachingSphere 2) k
        _
  change
    SingularMayerVietoris.singularHomologyMap
        (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
      SingularMayerVietoris.singularHomologyMap
          (G.comp (Degree.PassageHomology.cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
        SingularMayerVietoris.singularHomologyMap
          ((S.data q).surgery.attachingSphere.comp
            (Smale.LinearSphereAction.sphereMap L.toContinuousLinearMap L.injective))
          2 at hrelation
  rw [hone, hzero, hcoef] at hrelation
  exact hrelation

private theorem AdaptedWindows.exists_prescribed_family_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) (haq : a < f q)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) (k : ℤ)
    (hk : k = 1 ∨ k = -1) (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius < ε z) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            ∃ β δ : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data q).LowerLevel),
              MorseCancel.IsNativeMiddleBasinFamily S hf (S.data q).lower_regular p
                  (fun j => β j) ∧
                MorseCancel.IsNativeMiddleBasinFamily T hf (S.data q).lower_regular p
                    (fun j => δ j) ∧
                  (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
                    (∀ j, j ≠ i → δ j = β j) ∧
                      (∀ j, j ≠ i → ∀ x, ∃ t : ℝ, T.flow t (δ j x).val = (α j x).val) ∧
                        (SingularMayerVietoris.singularHomologyMap (δ i) 2 =
                            SingularMayerVietoris.singularHomologyMap (β i) 2 +
                              k •
                                SingularMayerVietoris.singularHomologyMap
                                  (MorseCancel.nativeIndexThreeAttachingSphere S q hq) 2) ∧
                          ∀ z : M,
                            f z ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by
      have hsplit := (S.data q).chart.finrank_negative_add_positive
      have hn := (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
      omega⟩
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  obtain ⟨γ, hγ, hαγ, havoid, x₀, v, A, L, hL, hunit⟩ :=
    S.exists_higher_family_prescribed_passage hf hdim horder q hq ha haq p i hp hhigh α hα k hk
  let τ : ℝ := 1 / 2
  have hτ : τ ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> norm_num [τ]
  let F := A.family
  let K := A.support
  have hK := A.compact_support
  have hKU := A.avoids
  have hF := A.smooth
  have hF0 := A.zero
  have hFd := A.slices
  have hFfix := A.fixedOutside
  have hcount := A.crossing
  obtain ⟨D, hD⟩ := hFd 1
  have I :
    Smale.SupportedDiffeomorph.SupportedRelativeIsotopy D K
      (Degree.MorseRearrangement.otherSheetImages (fun j => γ j) i) :=
    { family := F
      smooth := hF
      zero := hF0
      one := fun x => (hD x).symm
      slices := hFd
      fixedOutside := hFfix
      fixedOn := fun t x hx => hFfix t x (fun h => hKU h hx) }
  have hDavoid (j : Fin n) :
    Disjoint (Set.range (D ∘ γ j)) (Set.range (S.data q).surgery.beltSphere) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ ⟨w, hw⟩
    by_cases hji : j = i
    · subst j
      have heq : F (1, γ i x) = (S.data q).surgery.beltSphere w := (hD _).symm.trans hw.symm
      exact hτ.2.ne' ((hcount 1 ⟨zero_le_one, le_rfl⟩ x w).mp heq).1
    · have heq : D (γ j x) = γ j x :=
        I.endpoint_fixed_on (γ j x)
          (Degree.MorseRearrangement.mem_otherSheetImages (fun j => γ j) i j hji x)
      exact Set.disjoint_left.mp (havoid j) (Set.mem_range_self x) ⟨w, hw.trans heq⟩
  obtain
    ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, hβflow, hδflow, hδold, hother, hprotected,
      hkeep⟩ :=
    S.exists_relative_family_lower_transport hf hm q hq p i hhigh γ hγ havoid ε hε D K hK I
      hDavoid
  let H : C(ℝ × (Smale.Hemisphere.Sphere 2), (S.data q).UpperLevel) :=
    ⟨fun z => F (z.1, γ i z.2),
      hF.continuous.comp (continuous_fst.prodMk ((γ i).continuous.comp continuous_snd))⟩
  have hH : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ H :=
    hF.comp (contMDiff_fst.prodMk ((hγ.1 i).comp contMDiff_snd))
  have hpoint : (S.data q).surgery.beltSphere v = H (τ, x₀) :=
    ((hcount τ ⟨hτ.1.le, hτ.2.le⟩ x₀ v).mpr ⟨rfl, rfl, rfl⟩).symm
  have hcross :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ x : (Smale.Hemisphere.Sphere 2),
        H (t, x) ∈ Set.range (S.data q).surgery.beltSphere ↔ t = τ ∧ x = x₀ := by
    intro t ht x
    constructor
    · rintro ⟨w, hw⟩
      have hh := (hcount t ht x w).mp hw.symm
      exact ⟨hh.1, hh.2.1⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨v, hpoint⟩
  have hstart (x : (Smale.Hemisphere.Sphere 2)) :
    ∃ t : ℝ, S.flow t (H (0, x)).val = (β i x).val := by
    change ∃ t : ℝ, S.flow t (A.family (0, γ i x)).val = (β i x).val
    rw [hF0]
    exact hβflow i x
  have hend (x : (Smale.Hemisphere.Sphere 2)) : ∃ t : ℝ, S.flow t (H (1, x)).val = (δ i x).val := by
    change ∃ t : ℝ, S.flow t (A.family (1, γ i x)).val = (δ i x).val
    rw [← hD]
    exact hδold i x
  have hclasses :=
    S.prescribed_passage_actual_endpoint_classes hf q hq H hτ x₀ v hpoint hcross (β i) (δ i)
      hstart hend k L hL hunit hH.contMDiffAt
  refine ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, ?_, hother, ?_, hclasses, hkeep⟩
  · intro j x
    obtain ⟨s, hs⟩ := hαγ j x
    obtain ⟨t, ht⟩ := hβflow j x
    exact ⟨t + s, by rw [S.flow.map_add, hs, ht]⟩
  · intro j hji x
    obtain ⟨s, hs⟩ := hαγ j x
    have hm : (α j x).val ∈ Set.range (fun t => S.flow t (γ j x).val) := by
      refine ⟨-s, ?_⟩
      change S.flow (-s) (γ j x).val = (α j x).val
      rw [← hs, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]
    rw [← hprotected j hji x] at hm
    obtain ⟨t, ht⟩ := hm
    change T.flow t (γ j x).val = (α j x).val at ht
    obtain ⟨u, hu⟩ := hδflow j x
    exact ⟨t - u, by rw [← hu, ← T.flow.map_add, sub_add_cancel, ht]⟩

private theorem
    AdaptedWindows.exists_common_cut_prescribed_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (hαq :
      ∀ x,
        ∃ t : ℝ, S.flow t (MorseCancel.nativeIndexThreeAttachingSphere S q hq x).val = (αq x).val)
    (k : ℤ) (hk : k = 1 ∨ k = -1) (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ)
    (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius < ε z) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            ∃ Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
              MorseCancel.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                  (Fin.cases αq (fun j => Γ j)) ∧
                (∀ j, j ≠ i → Γ j = α j) ∧
                  (MorseCancel.middleSectionClass (Γ i) =
                      MorseCancel.middleSectionClass (α i) +
                        k • MorseCancel.middleSectionClass αq) ∧
                    ∀ z : M,
                      f z ≤ f q →
                        (∀ x,
                            Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                          (∀ x,
                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                Set.range (fun t => T.flow t x) =
                                  Set.range (fun t => S.flow t x)) ∧
                            ∀ v,
                              Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hfamily
  have hα : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => α j) := by
    refine ⟨fun j => hs j.succ, fun j => he j.succ, fun j => hi j.succ, ?_, fun j => hfull j.succ⟩
    intro j k hjk
    exact hpair (fun h => hjk (Fin.succ_inj.mp h))
  obtain ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, hαβ, hother, hprotected, hmaps, hkeep⟩ :=
    S.exists_prescribed_family_slide hf hm hdim horder q hq ha
      (hal.trans (S.toSurgeryWindows.lower_lt_value q)) p i hp hhigh α hα k hk ε hε
  have hgap :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, f z ∉ Set.Icc a (S.toSurgeryWindows.lower q) :=
    fun z hz h => hband z h hz
  have hpabove (j : Fin n) : S.toSurgeryWindows.lower q < f (p j) :=
    (S.toSurgeryWindows.lower_lt_value q).trans
      ((S.toSurgeryWindows.value_lt_upper q).trans (hhigh j))
  let x₀ : (Smale.Hemisphere.Sphere 2) := Smale.Hemisphere.point Bool.true ⟨0, by simp⟩
  obtain ⟨Γ₀, hΓ₀, hδΓ⟩ :=
    T.exists_regular_band_middle_basin_family hf hal (S.data q).lower_regular ha hgap (δ i x₀) p
      hpabove (fun j => δ j) hδ
  let Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }) := fun j =>
    ⟨Γ₀ j, (hΓ₀.1 j).continuous⟩
  have hΓ : MorseCancel.IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) := hΓ₀
  have hαqfull (y : { z : M // f z = a }) :
    y ∈ Set.range αq ↔ Filter.Tendsto (fun t => T.flow t y.val) Filter.atBot (𝓝 q.val) :=
    (hfull 0 y).trans ((hkeep q.val le_rfl).1 y.val).symm
  have hdisj (j : Fin n) : Disjoint (Set.range αq) (Set.range (Γ j)) := by
    apply Set.disjoint_left.mpr
    intro y hyq hyj
    have heq : q.val = (p j).val :=
      tendsto_nhds_unique ((hαqfull y).mp hyq) ((hΓ.2.2.2.2 j y).mp hyj)
    exact ((S.toSurgeryWindows.value_lt_upper q).trans (hhigh j)).ne (congrArg f heq)
  have hΓpair :
    Pairwise
      (fun j k =>
        Disjoint (Set.range (Fin.cases αq (fun j => Γ j) j))
          (Set.range (Fin.cases αq (fun j => Γ j) k))) := by
    intro j k hjk
    cases j using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero => exact (hjk rfl).elim
      | succ k => exact hdisj k
    | succ j =>
      cases k using Fin.cases with
      | zero => exact (hdisj j).symm
      | succ k => exact hΓ.2.2.2.1 (fun h => hjk (congrArg Fin.succ h))
  refine ⟨T, hcharts, hradii, hgerms, Γ, ?_, ?_, ?_, hkeep⟩
  · refine ⟨?_, ?_, ?_, hΓpair, ?_⟩
    · intro j
      cases j using Fin.cases with
      | zero => exact hs 0
      | succ j => exact hΓ.1 j
    · intro j
      cases j using Fin.cases with
      | zero => exact he 0
      | succ j => exact hΓ.2.1 j
    · intro j
      cases j using Fin.cases with
      | zero => exact hi 0
      | succ j => exact hΓ.2.2.1 j
    · intro j
      cases j using Fin.cases with
      | zero => exact hαqfull
      | succ j => exact hΓ.2.2.2.2 j
  · intro j hji
    apply ContinuousMap.ext
    intro x
    obtain ⟨s, hs⟩ := hδΓ j x
    change T.flow s (δ j x).val = (Γ j x).val at hs
    obtain ⟨t, ht⟩ := hprotected j hji x
    have hshared : T.flow 0 (Γ j x).val = T.flow (s - t) (α j x).val := by
      rw [T.flow.map_zero_apply, ← hs, ← ht, ← T.flow.map_add, sub_add_cancel]
    apply Subtype.ext
    exact
      MorseCancel.native_same_level_orbit_points hf T.smooth T.flow T.integral
        (fun z hz => T.descent z (ha z hz)) (Γ j x).property (α j x).property hshared
  · have hβα (x : (Smale.Hemisphere.Sphere 2)) : ∃ t : ℝ, S.flow t (β i x).val = (α i x).val := by
      obtain ⟨t, ht⟩ := hαβ i x
      exact ⟨-t, by rw [← ht, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]⟩
    exact
      MorseCancel.signed_relation_of_regular_cut_transport S T hf hal ha hband (β i) (δ i)
        (MorseCancel.nativeIndexThreeAttachingSphere S q hq) (α i) (Γ i) αq k hβα (hδΓ i) hαq
        hmaps

private theorem AdaptedWindows.exists_common_cut_prescribed_family_slide {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [PathConnectedSpace M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1) (ε : Smale.ManifoldMorse.criticalPoints E f → ℝ)
    (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius < ε z) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            ∃ Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
              MorseCancel.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                  (Fin.cases αq (fun j => Γ j)) ∧
                (∀ j, j ≠ i → Γ j = α j) ∧
                  (MorseCancel.middleSectionClass (Γ i) =
                      MorseCancel.middleSectionClass (α i) +
                        k • MorseCancel.middleSectionClass αq) ∧
                    ∀ z : M,
                      f z ≤ f q →
                        (∀ x,
                            Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                          (∀ x,
                              Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                Set.range (fun t => T.flow t x) =
                                  Set.range (fun t => S.flow t x)) ∧
                            ∀ v,
                              Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  let _ := Smale.RegularLevel.chartedSpace hf ha
  obtain ⟨βq, hβs, hβe, hβi, hrange, horbit, -⟩ :=
    S.exists_canonical_basin_sphere hf q hq ha αq (Smale.Hemisphere.point Bool.true ⟨0, by simp⟩)
      (hfamily.2.2.2.2 0)
  have hβfamily :=
    MorseCancel.nativeMiddleBasinFamily_replace_zero S hf ha q p αq βq α hfamily hrange hβs hβe
      hβi
  obtain ⟨u, hu, hunit⟩ :=
    MorseCancel.same_image_section_classes_unit αq βq (hfamily.2.1 0).isEmbedding hβe.isEmbedding
      hrange
  have hku : k * u = 1 ∨ k * u = -1 := by
    rcases hk with rfl | rfl <;> rcases hu with rfl | rfl <;> norm_num
  obtain ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, hclass, hkeep⟩ :=
    S.exists_common_cut_prescribed_slide hf hm hdim horder q hq ha hal hband p i hp hhigh βq α
      hβfamily horbit (k * u) hku ε hε
  have hrestored :=
    MorseCancel.nativeMiddleBasinFamily_replace_zero T hf ha q p βq αq Γ hΓ hrange.symm
      (hfamily.1 0) (hfamily.2.1 0) (hfamily.2.2.1 0)
  have hcancel : (k * u) * u = k := by rcases hu with rfl | rfl <;> ring
  refine ⟨T, hcharts, hradii, hgerms, Γ, hrestored, hother, ?_, hkeep⟩
  rw [hclass, hunit, ← SemigroupAction.mul_smul, hcancel]

private theorem
    MorseCancel.regular_below_pivot_of_regular_lower_band {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    {a : ℝ}
    (hband : ∀ y, f y ∈ Set.Icc a (S.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    ∀ y, f y ∈ Set.Ico a (f q) → y ∉ Smale.ManifoldMorse.criticalPoints E f := by
  intro y hy hcrit
  by_cases hlow : f y ≤ S.lower q
  · exact hband y ⟨hy.1, hlow⟩ hcrit
  · have heq : y = q.val :=
      S.isolated q y hcrit ⟨(lt_of_not_ge hlow).le, hy.2.le.trans (S.value_lt_upper q).le⟩
    exact hy.2.ne (congrArg f heq)

private theorem MorseCancel.lower_window_le_of_radius_le {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S T : Smale.ManifoldMorse.SurgeryWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    (hr : (T.data q).radius ≤ (S.data q).radius) : S.lower q ≤ T.lower q := by
  have hs : (T.data q).radius ^ 2 ≤ (S.data q).radius ^ 2 :=
    (sq_le_sq₀ (T.data q).radius_pos.le (S.data q).radius_pos.le).mpr hr
  exact sub_le_sub_left hs (f q)

private theorem MorseCancel.common_cut_band_of_smaller_radius {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S T : Smale.ManifoldMorse.SurgeryWindows E f) (q : Smale.ManifoldMorse.criticalPoints E f)
    {a : ℝ} (hal : a < S.lower q)
    (hband : ∀ y, f y ∈ Set.Icc a (S.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hr : (T.data q).radius ≤ (S.data q).radius) :
    a < T.lower q ∧
      ∀ y, f y ∈ Set.Icc a (T.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f := by
  refine ⟨hal.trans_le (lower_window_le_of_radius_le S T q hr), ?_⟩
  intro y hy
  exact
    regular_below_pivot_of_regular_lower_band S q hband y
      ⟨hy.1, hy.2.trans_lt (T.lower_lt_value q)⟩

private theorem
    MorseCancel.higher_window_separation_of_value_order {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    (S T : Smale.ManifoldMorse.SurgeryWindows E f) (q p : Smale.ManifoldMorse.criticalPoints E f)
    (hhigh : S.upper q < f p) : T.upper q < f p :=
  (T.upper_lt_lower q p ((S.value_lt_upper q).trans hhigh)).trans (T.lower_lt_value p)

private theorem AdaptedWindows.exists_repeatable_column_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            a < T.toSurgeryWindows.lower q ∧
              (∀ y,
                  f y ∈ Set.Icc a (T.toSurgeryWindows.lower q) →
                    y ∉ Smale.ManifoldMorse.criticalPoints E f) ∧
                (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
                  ∃ Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
                    MorseCancel.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                        (Fin.cases αq (fun j => Γ j)) ∧
                      (∀ j, j ≠ i → Γ j = α j) ∧
                        (MorseCancel.middleSectionClass (Γ i) =
                            MorseCancel.middleSectionClass (α i) +
                              k • MorseCancel.middleSectionClass αq) ∧
                          ∀ z : M,
                            f z ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  obtain ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, hclass, hkeep⟩ :=
    S.exists_common_cut_prescribed_family_slide hf hm hdim horder q hq ha hal hband p i hp hhigh
      αq α hfamily k hk (fun z => (S.data z).radius) (fun z => (S.data z).radius_pos)
  obtain ⟨hcut, hregular⟩ :=
    MorseCancel.common_cut_band_of_smaller_radius S.toSurgeryWindows T.toSurgeryWindows q hal
      hband (hradii q).le
  have hseparated : ∀ j, T.toSurgeryWindows.upper q < f (p j) := fun j =>
    MorseCancel.higher_window_separation_of_value_order S.toSurgeryWindows T.toSurgeryWindows q
      (p j) (hhigh j)
  exact
    ⟨T, hcharts, fun z => (hradii z).le, hgerms, hcut, hregular, hseparated, Γ, hΓ, hother,
      hclass, hkeep⟩

private theorem AdaptedWindows.exists_iterated_column_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1) (m : ℕ) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            a < T.toSurgeryWindows.lower q ∧
              (∀ y,
                  f y ∈ Set.Icc a (T.toSurgeryWindows.lower q) →
                    y ∉ Smale.ManifoldMorse.criticalPoints E f) ∧
                (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
                  ∃ Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
                    MorseCancel.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                        (Fin.cases αq (fun j => Γ j)) ∧
                      (∀ j, j ≠ i → Γ j = α j) ∧
                        (MorseCancel.middleSectionClass (Γ i) =
                            MorseCancel.middleSectionClass (α i) +
                              ((m : ℤ) * k) • MorseCancel.middleSectionClass αq) ∧
                          ∀ z : M,
                            f z ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  induction m with
  |
    zero =>
    refine
      ⟨S, fun _ => rfl, fun _ => le_rfl, ?_, hal, hband, hhigh, α, hfamily, fun _ _ => rfl, ?_,
        ?_⟩
    · intro z hz
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · simp only [Nat.cast_zero, MulZeroClass.zero_mul, zero_smul, add_zero]
    · intro z hz
      exact ⟨fun _ => Iff.rfl, fun _ _ => rfl, fun _ => Iff.rfl⟩
  | succ m
    ih =>
    obtain
      ⟨T, hcharts, hradii, hgerms, hcut, hregular, hseparated, Γ, hΓ, hother, hclass, hkeep⟩ := ih
    obtain
      ⟨U, ucharts, uradii, ugerms, ucut, uregular, useparated, Δ, hΔ, uother, uclass, ukeep⟩ :=
      T.exists_repeatable_column_slide hf hm hdim horder q hq ha hcut hregular p i hp hseparated
        αq Γ hΓ k hk
    refine
      ⟨U, fun z => (ucharts z).trans (hcharts z), fun z => (uradii z).trans (hradii z), ?_, ucut,
        uregular, useparated, Δ, hΔ, fun j hji => (uother j hji).trans (hother j hji), ?_, ?_⟩
    · intro z hz
      filter_upwards [ugerms z hz, hgerms z hz] with y hy hy'
      exact hy.trans hy'
    · rw [uclass, hclass, add_assoc, ← add_zsmul]
      have hcoef : (m : ℤ) * k + k = ((m + 1 : ℕ) : ℤ) * k := by
        push_cast
        ring
      rw [hcoef]
    · intro z hz
      have hUT := ukeep z hz
      have hTS := hkeep z hz
      exact
        ⟨fun x => (hUT.1 x).trans (hTS.1 x), fun x hx =>
          (hUT.2.1 x ((hTS.1 x).mpr hx)).trans (hTS.2.1 x hx), fun v =>
          (hUT.2.2 v).trans (hTS.2.2 v)⟩

private theorem AdaptedWindows.exists_integer_column_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ p q : Smale.ManifoldMorse.criticalPoints E f,
        f p < f q → MorseCancel.nativeMorseIndex E f p ≤ MorseCancel.nativeMorseIndex E f q)
    (q : Smale.ManifoldMorse.criticalPoints E f) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower q) → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f) (i : Fin n)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (α : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hfamily :
      MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases q p) (Fin.cases αq (fun j => α j)))
    (k : ℤ) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            a < T.toSurgeryWindows.lower q ∧
              (∀ y,
                  f y ∈ Set.Icc a (T.toSurgeryWindows.lower q) →
                    y ∉ Smale.ManifoldMorse.criticalPoints E f) ∧
                (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
                  ∃ Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
                    MorseCancel.IsNativeMiddleBasinFamily T hf ha (Fin.cases q p)
                        (Fin.cases αq (fun j => Γ j)) ∧
                      (∀ j, j ≠ i → Γ j = α j) ∧
                        (MorseCancel.middleSectionClass (Γ i) =
                            MorseCancel.middleSectionClass (α i) +
                              k • MorseCancel.middleSectionClass αq) ∧
                          ∀ z : M,
                            f z ≤ f q →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa only [mul_one] using
      S.exists_iterated_column_slide hf hm hdim horder q hq ha hal hband p i hp hhigh αq α hfamily
        1 (Or.inl rfl) m
  · simpa only [mul_neg_one] using
      S.exists_iterated_column_slide hf hm hdim horder q hq ha hal hband p i hp hhigh αq α hfamily
        (-1) (Or.inr rfl) m

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem MorseCancel.nativeMiddleBasinFamily_reindex {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {n m : ℕ}
    (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (γ : Fin n → (Smale.Hemisphere.Sphere 2) → { y : M // f y = a })
    (hγ : IsNativeMiddleBasinFamily S hf ha p γ) (e : Fin m → Fin n) (he : Function.Injective e) :
    IsNativeMiddleBasinFamily S hf ha (p ∘ e) (γ ∘ e) := by
  obtain ⟨hs, hi, hd, hpair, hfull⟩ := hγ
  exact
    ⟨fun j => hs (e j), fun j => hi (e j), fun j => hd (e j), fun i j hij =>
      hpair (fun h => hij (he h)), fun j => hfull (e j)⟩

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem
    MorseCancel.canonicalMiddleMatrix_single_class_addition {M : Type} [TopologicalSpace M]
      {f : M → ℝ} {a : ℝ} {r n : ℕ}
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (α Γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) (q i : Fin n) (k : ℤ)
    (hother : ∀ j, j ≠ i → Γ j = α j)
    (hclass :
      middleSectionClass (Γ i) = middleSectionClass (α i) + k • middleSectionClass (α q)) :
    canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B Γ =
      canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n := n) B α *
        Matrix.transvection q i k := by
  refine eq_mul_transvection_of_columns _ _ q i k ?_ ?_
  · intro u
    simp only [canonicalMiddleMatrix, classCoordinateMatrix]
    rw [hclass, map_add, map_zsmul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro u j hji
    simp only [canonicalMiddleMatrix, classCoordinateMatrix, hother j hji]

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem MorseCancel.SurgeryWindows.regular_before_first_middle_pivot {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ}
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (q : Fin n) (hfirst : ∀ j, j ≠ q → f (p q) < f (p j)) :
    ∀ y, f y ∈ Set.Icc a (S.lower (p q)) → y ∉ Smale.ManifoldMorse.criticalPoints E f := by
  intro y hy hcrit
  let z : Smale.ManifoldMorse.criticalPoints E f := ⟨y, hcrit⟩
  have hlt : f z < f (p q) := hy.2.trans_lt (S.lower_lt_value (p q))
  have hle : MorseCancel.nativeMorseIndex E f z ≤ 3 := (horder z (p q) hlt).trans_eq (hp q)
  have heq : MorseCancel.nativeMorseIndex E f z = 3 := by
    apply Nat.le_antisymm hle
    by_contra hnot
    exact (hcut z (lt_of_not_ge hnot)).not_ge hy.1
  obtain ⟨j, hj⟩ := hcomplete z heq
  by_cases hjq : j = q
  · exact (ne_of_lt hlt) (congrArg f (congrArg Subtype.val (hj.symm.trans (congrArg p hjq))))
  · have hreverse : f (p q) < f z := by simpa only [hj] using hfirst j hjq
    exact hlt.not_gt hreverse

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem
    MorseCancel.low_index_cut_of_preserved_other_values {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
       {f : M → ℝ} {g : M → ℝ} {a : ℝ}
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hindices :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    {n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (houtside : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, (∀ j, z ≠ (p j).val) → g z = f z)
    (hcut : ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z < 3 → f z < a) :
    ∀ z : Smale.ManifoldMorse.criticalPoints E g, nativeMorseIndex E g z < 3 → g z < a := by
  intro z hz
  let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
  have hidx : nativeMorseIndex E f zf < 3 := by
    rw [← hindices z zf.property]
    exact hz
  have hother : ∀ j, z.val ≠ (p j).val := by
    intro j hj
    have heq : zf = p j := Subtype.ext hj
    rw [heq, hp j] at hidx
    exact (lt_irrefl _ hidx)
  rw [houtside z zf.property hother]
  exact hcut zf hidx

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem AdaptedWindows.exists_labelled_integer_slide {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f) {r n : ℕ}
    (p : Fin (n + 1) → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin (n + 1) → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec)
    (q i : Fin (n + 1)) (hqi : q ≠ i) (hfirst : ∀ j, j ≠ q → f (p q) < f (p j))
    (hband :
      ∀ y,
        f y ∈ Set.Icc a (S.toSurgeryWindows.lower (p q)) →
          y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (k : ℤ) :
    ∃ T : AdaptedWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
          (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
            (∀ j, a < T.toSurgeryWindows.lower (p j)) ∧
              ∃ Γ : Fin (n + 1) → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }),
                MorseCancel.IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) ∧
                  (∀ j, j ≠ i → Γ j = γ j) ∧
                    MorseCancel.middleSectionClass (Γ i) =
                        MorseCancel.middleSectionClass (γ i) +
                          k • MorseCancel.middleSectionClass (γ q) ∧
                      MorseCancel.canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r) (n :=
                            n + 1) B Γ =
                          MorseCancel.canonicalMiddleMatrix (M := M) (f := f) (a := a) (r := r)
                              (n := n + 1) B γ *
                            Matrix.transvection q i k ∧
                        Function.Surjective (MorseCancel.canonicalMiddleMatrix B Γ).mulVec ∧
                          ∀ z : M,
                            f z ≤ f (p q) →
                              (∀ x,
                                  Filter.Tendsto (fun t => T.flow t x) Filter.atBot (𝓝 z) ↔
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z)) ∧
                                (∀ x,
                                    Filter.Tendsto (fun t => S.flow t x) Filter.atBot (𝓝 z) →
                                      Set.range (fun t => T.flow t x) =
                                        Set.range (fun t => S.flow t x)) ∧
                                  ∀ v,
                                    Filter.Tendsto (fun t => T.flow t z) Filter.atTop (𝓝 v) ↔
                                      Filter.Tendsto (fun t => S.flow t z) Filter.atTop (𝓝 v) := by
  classical
  let e := Equiv.swap (0 : Fin (n + 1)) q
  have he0 : e 0 = q := Equiv.swap_apply_left _ _
  have heq : e q = 0 := Equiv.swap_apply_right _ _
  have hee (j : Fin (n + 1)) : e (e j) = j := Equiv.swap_apply_self _ _ _
  have hne : e i ≠ 0 := fun hi => hqi (e.injective (heq.trans hi.symm))
  obtain ⟨l, hl⟩ := Fin.exists_succ_eq_of_ne_zero hne
  have hel : e l.succ = i := by rw [hl, hee]
  have hpcases : Fin.cases (p q) (fun j => p (e j.succ)) = p ∘ e := by
    funext j
    cases j using Fin.cases with
    | zero => simp only [Fin.cases_zero, Function.comp_apply, he0]
    | succ j => rfl
  have hγcases : Fin.cases (γ q) (fun j => γ (e j.succ)) = γ ∘ e := by
    funext j
    cases j using Fin.cases with
    | zero => simp only [Fin.cases_zero, Function.comp_apply, he0]
    | succ j => rfl
  have hfamily :
    MorseCancel.IsNativeMiddleBasinFamily S hf ha (Fin.cases (p q) (fun j => p (e j.succ)))
      (Fin.cases (fun x => γ q x) (fun j x => γ (e j.succ) x)) := by
    have hmaps :
      Fin.cases (fun x => γ q x) (fun j x => γ (e j.succ) x) = (fun j x => γ j x) ∘ e := by
      funext j x
      cases j using Fin.cases with
      | zero => simp only [Fin.cases_zero, Function.comp_apply, he0]
      | succ j => rfl
    rw [hpcases, hmaps]
    exact MorseCancel.nativeMiddleBasinFamily_reindex S hf ha p (fun j => γ j) hγ e e.injective
  have hhigh (j : Fin n) : S.toSurgeryWindows.upper (p q) < f (p (e j.succ)) := by
    have hjq : e j.succ ≠ q := by
      intro hj
      have hzero : j.succ = 0 := e.injective (hj.trans he0.symm)
      exact Fin.succ_ne_zero j hzero
    exact
      (S.toSurgeryWindows.upper_lt_lower (p q) (p (e j.succ)) (hfirst _ hjq)).trans
        (S.toSurgeryWindows.lower_lt_value _)
  obtain ⟨T, hcharts, hradii, hgerms, -, -, -, Δ, hΔ, hother, hclass, hkeep⟩ :=
    S.exists_integer_column_slide hf hm hdim horder (p q) (hp q) ha (hlower q) hband
      (fun j => p (e j.succ)) l (fun j => hp (e j.succ)) hhigh (γ q) (fun j => γ (e j.succ))
      hfamily k
  let δ : Fin (n + 1) → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }) := Fin.cases (γ q) Δ
  let Γ := δ ∘ e
  have hΓ : MorseCancel.IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) := by
    have hh :=
      MorseCancel.nativeMiddleBasinFamily_reindex T hf ha
        (Fin.cases (p q) (fun j => p (e j.succ))) (Fin.cases (fun x => γ q x) (fun j x => Δ j x))
        hΔ e e.injective
    have hlabels : (Fin.cases (p q) (fun j => p (e j.succ))) ∘ e = p := by
      rw [hpcases]
      funext j
      exact congrArg p (hee j)
    rw [hlabels] at hh
    have hmaps : (Fin.cases (fun x => γ q x) (fun j x => Δ j x)) ∘ e = (fun j x => Γ j x) := by
      funext j x
      change
        Fin.cases (motive := fun _ : Fin (n + 1) =>
            (Smale.Hemisphere.Sphere 2) → { y : M // f y = a }) (fun x => γ q x)
            (fun j x => Δ j x) (e j) x =
          (Fin.cases (motive := fun _ : Fin (n + 1) =>
              C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) (γ q) Δ (e j))
            x
      cases e j using Fin.cases <;> rfl
    rw [hmaps] at hh
    exact hh
  have hΓother (j : Fin (n + 1)) (hji : j ≠ i) : Γ j = γ j := by
    change Fin.cases (γ q) Δ (e j) = γ j
    by_cases hjzero : e j = 0
    · have hjq : j = q := e.injective (hjzero.trans heq.symm)
      rw [hjzero, Fin.cases_zero, hjq]
    · obtain ⟨v, hv⟩ := Fin.exists_succ_eq_of_ne_zero hjzero
      have hvl : v ≠ l := by
        intro hvl
        apply hji
        exact e.injective (hv.symm.trans ((congrArg Fin.succ hvl).trans hl))
      rw [← hv, Fin.cases_succ, hother v hvl]
      exact congrArg γ (by rw [hv, hee])
  have hΓclass :
    MorseCancel.middleSectionClass (Γ i) =
      MorseCancel.middleSectionClass (γ i) + k • MorseCancel.middleSectionClass (γ q) := by
    change MorseCancel.middleSectionClass (Fin.cases (γ q) Δ (e i)) = _
    rw [← hl, Fin.cases_succ]
    simpa only [hel] using hclass
  have hmatrix :=
    MorseCancel.canonicalMiddleMatrix_single_class_addition (f := f) (a := a) B γ Γ q i k hΓother
      hΓclass
  refine ⟨T, hcharts, hradii, hgerms, ?_, Γ, hΓ, hΓother, hΓclass, hmatrix, ?_, hkeep⟩
  · intro j
    exact
      (hlower j).trans_le
        (MorseCancel.lower_window_le_of_radius_le S.toSurgeryWindows T.toSurgeryWindows (p j)
          (hradii _))
  · rw [hmatrix]
    exact MorseCancel.mul_transvection_surjective _ q i hqi k hsurj

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem AdaptedWindows.exists_arbitrary_column_addition {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec) (q i : Fin n)
    (hqi : q ≠ i) (k : ℤ) :
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
                (∀ d, MorseCancel.nativeMorseCount E g d = MorseCancel.nativeMorseCount E f d) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      (∀ j, z ≠ (p j).val) → g z = f z) ∧
                    (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                        MorseCancel.nativeMorseIndex E g z < 3 → g z < a) ∧
                      ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                          ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                            ∃ T : AdaptedWindows E g,
                              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                                  ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                                (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                  let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                    fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                  let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                  (∀ j, MorseCancel.nativeMorseIndex E g (p' j) = 3) ∧
                                    (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                                        MorseCancel.nativeMorseIndex E g z = 3 → ∃ j, p' j = z) ∧
                                      (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                        ∃ Γ :
                                          Fin n →
                                            C((Smale.Hemisphere.Sphere 2), { y : M // g y = a }),
                                          MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                              (fun j => Γ j) ∧
                                            (∀ j,
                                                j ≠ i →
                                                  Γ j =
                                                    MorseCancel.equalCutSection hlevel (γ j)) ∧
                                              MorseCancel.canonicalMiddleMatrix (M := M) (f := g)
                                                    (a := a) (r := r) (n := n) B' Γ =
                                                  MorseCancel.canonicalMiddleMatrix (M := M) (f :=
                                                      f) (a := a) (r := r) (n := n) B γ *
                                                    Matrix.transvection q i k ∧
                                                Function.Surjective
                                                    (MorseCancel.canonicalMiddleMatrix B'
                                                        Γ).mulVec ∧
                                                  ∀ z : M,
                                                    f z ≤ a →
                                                      (∀ x,
                                                          Filter.Tendsto (fun t => T.flow t x)
                                                              Filter.atBot (𝓝 z) ↔
                                                            Filter.Tendsto (fun t => S.flow t x)
                                                              Filter.atBot (𝓝 z)) ∧
                                                        (∀ x,
                                                            Filter.Tendsto (fun t => S.flow t x)
                                                                Filter.atBot (𝓝 z) →
                                                              Set.range (fun t => T.flow t x) =
                                                                Set.range (fun t => S.flow t x)) ∧
                                                          ∀ v,
                                                            Filter.Tendsto (fun t => T.flow t z)
                                                                Filter.atTop (𝓝 v) ↔
                                                              Filter.Tendsto (fun t => S.flow t z)
                                                                Filter.atTop (𝓝 v) := by
  cases n with
  | zero => exact Fin.elim0 q
  | succ
    n =>
    obtain
      ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hfirst, hsub, hlevel, hga, T,
        hfield, hflow, hgerm, hpg, hglower, hfamily, -, hmatrix, hgsurj⟩ :=
      S.exists_first_middle_pivot hf hm ha horder p hp hcomplete hlower B γ hγ hsurj q
    let pg : Fin (n + 1) → Smale.ManifoldMorse.criticalPoints E g := fun j =>
      ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
    let Bg := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
    let γg := fun j => MorseCancel.equalCutSection hlevel (γ j)
    have hgcut :=
      MorseCancel.low_index_cut_of_preserved_other_values hcrit hindices p hp houtside hcut
    have hgcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g,
        MorseCancel.nativeMorseIndex E g z = 3 → ∃ j, pg j = z := by
      intro z hz
      let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
      have hzf : MorseCancel.nativeMorseIndex E f zf = 3 := (hindices z zf.property).symm.trans hz
      obtain ⟨j, hj⟩ := hcomplete zf hzf
      exact
        ⟨j, Subtype.ext (congrArg (fun z : Smale.ManifoldMorse.criticalPoints E f => z.val) hj)⟩
    have hband :=
      MorseCancel.SurgeryWindows.regular_before_first_middle_pivot T.toSurgeryWindows hgorder
        hgcut pg hpg hgcomplete q hfirst
    obtain ⟨U, -, -, ugerms, ulower, Γ, hΓ, uother, -, umatrix, usurj, ukeep⟩ :=
      T.exists_labelled_integer_slide hg hmg hdim hgorder hga pg hpg hglower Bg γg hfamily hgsurj
        q i hqi hfirst hband k
    refine
      ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut, hsub, hlevel, hga, U, ?_,
        hgerm, hpg, hgcomplete, ulower, Γ, hΓ, uother, ?_, usurj, ?_⟩
    · intro z hz
      filter_upwards [ugerms z (hcrit.symm ▸ hz)] with y hy
      exact hy.trans (congrFun hfield y)
    · exact umatrix.trans (congrArg (fun A => A * Matrix.transvection q i k) hmatrix)
    · intro z hz
      have hheight : g z ≤ g (pg q) :=
        ((hsub z).mpr hz).trans ((hglower q).trans (T.toSurgeryWindows.lower_lt_value (pg q))).le
      simpa only [hflow] using ukeep z hheight

private theorem
    MorseCancel.equalCutSection_trans {M : Type} [TopologicalSpace M] {f g h : M → ℝ} {a : ℝ}
    (hfg : ∀ y, g y = a ↔ f y = a) (hgh : ∀ y, h y = a ↔ g y = a)
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })) :
    equalCutSection hgh (equalCutSection hfg γ) =
      equalCutSection (fun y => (hgh y).trans (hfg y)) γ :=
  rfl

private theorem MorseCancel.equalCutHomologyEquiv_refl {M : Type} [TopologicalSpace M] {f : M → ℝ}
    {a : ℝ} :
    equalCutHomologyEquiv (f := f) (a := a) (fun _ => Iff.rfl) =
      LinearEquiv.refl ℤ (SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2) := by
  apply LinearEquiv.ext
  intro x
  change
    SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph (f := f) (a := a) (fun _ => Iff.rfl)).toHomotopyEquiv.toFun 2
        x =
      x
  have hmap :
    (equalCutSublevelHomeomorph (f := f) (a := a) (fun _ => Iff.rfl)).toHomotopyEquiv.toFun =
      ContinuousMap.id { y : M // f y ≤ a } :=
    rfl
  rw [hmap, PeriodTorusHigherHomology.singularHomologyMap_id]
  rfl

private theorem
    MorseCancel.equalCutHomologyEquiv_trans {M : Type} [TopologicalSpace M] {f g h : M → ℝ}
    {a : ℝ} (hfg : ∀ y, g y ≤ a ↔ f y ≤ a) (hgh : ∀ y, h y ≤ a ↔ g y ≤ a) :
    (equalCutHomologyEquiv hfg).trans (equalCutHomologyEquiv hgh) =
      equalCutHomologyEquiv (fun y => (hgh y).trans (hfg y)) := by
  apply LinearEquiv.ext
  intro x
  change
    SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph hgh).toHomotopyEquiv.toFun 2
        (SingularMayerVietoris.singularHomologyMap
          (equalCutSublevelHomeomorph hfg).toHomotopyEquiv.toFun 2 x) =
      SingularMayerVietoris.singularHomologyMap
        (equalCutSublevelHomeomorph (fun y => (hgh y).trans (hfg y))).toHomotopyEquiv.toFun 2 x
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem AdaptedWindows.exists_arbitrary_column_sequence {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec)
    (ops : List (Fin n × Fin n × ℤ)) (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
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
                (∀ d, MorseCancel.nativeMorseCount E g d = MorseCancel.nativeMorseCount E f d) ∧
                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                      (∀ j, z ≠ (p j).val) → g z = f z) ∧
                    (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                        MorseCancel.nativeMorseIndex E g z < 3 → g z < a) ∧
                      ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                        ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                          ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                            ∃ T : AdaptedWindows E g,
                              (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                                  ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                                (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                  let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                    fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                  let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                  (∀ j, MorseCancel.nativeMorseIndex E g (p' j) = 3) ∧
                                    (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                                        MorseCancel.nativeMorseIndex E g z = 3 → ∃ j, p' j = z) ∧
                                      (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                        ∃ Γ :
                                          Fin n →
                                            C((Smale.Hemisphere.Sphere 2), { y : M // g y = a }),
                                          MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                              (fun j => Γ j) ∧
                                            (∀ j,
                                                (∀ op ∈ ops, op.2.1 ≠ j) →
                                                  Γ j =
                                                    MorseCancel.equalCutSection hlevel (γ j)) ∧
                                              MorseCancel.canonicalMiddleMatrix (M := M) (f := g)
                                                    (a := a) (r := r) (n := n) B' Γ =
                                                  MorseCancel.canonicalMiddleMatrix (M := M) (f :=
                                                      f) (a := a) (r := r) (n := n) B γ *
                                                    (ops.map
                                                        (fun op =>
                                                          Matrix.transvection op.1 op.2.1
                                                            op.2.2)).prod ∧
                                                Function.Surjective
                                                    (MorseCancel.canonicalMiddleMatrix B'
                                                        Γ).mulVec ∧
                                                  ∀ z : M,
                                                    f z ≤ a →
                                                      (∀ x,
                                                          Filter.Tendsto (fun t => T.flow t x)
                                                              Filter.atBot (𝓝 z) ↔
                                                            Filter.Tendsto (fun t => S.flow t x)
                                                              Filter.atBot (𝓝 z)) ∧
                                                        (∀ x,
                                                            Filter.Tendsto (fun t => S.flow t x)
                                                                Filter.atBot (𝓝 z) →
                                                              Set.range (fun t => T.flow t x) =
                                                                Set.range (fun t => S.flow t x)) ∧
                                                          ∀ v,
                                                            Filter.Tendsto (fun t => T.flow t z)
                                                                Filter.atTop (𝓝 v) ↔
                                                              Filter.Tendsto (fun t => S.flow t z)
                                                                Filter.atTop (𝓝 v) := by
  revert hvalid
  induction ops using List.reverseRecOn with
  | nil =>
    intro hvalid
    have hB :
      B.trans (MorseCancel.equalCutHomologyEquiv (f := f) (a := a) (fun _ => Iff.rfl)) = B := by
      rw [MorseCancel.equalCutHomologyEquiv_refl, LinearEquiv.trans_refl]
    refine
      ⟨f, hf, hm, rfl, horder, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, hcut, fun _ =>
        Iff.rfl, fun _ => Iff.rfl, ha, S, ?_, fun _ _ => Filter.EventuallyEq.rfl, hp, hcomplete,
        hlower, γ, hγ, fun _ _ => rfl, ?_, ?_, ?_⟩
    · intro z hz
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · rw [hB]
      simp only [List.map_nil, List.prod_nil, Matrix.mul_one]
    · rw [hB]
      exact hsurj
    · intro z hz
      exact ⟨fun _ => Iff.rfl, fun _ _ => rfl, fun _ => Iff.rfl⟩
  | append_singleton ops op ih =>
    intro hvalid
    have hprev : ∀ e ∈ ops, e.1 ≠ e.2.1 := fun e he => hvalid e (List.mem_append.mpr (Or.inl he))
    have hop : op.1 ≠ op.2.1 :=
      hvalid op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op)))
    obtain
      ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut, hsub, hlevel, hga, T,
        hgerms, hfgerms, hpg, hgcomplete, hglower, Γ, hΓ, hother, hmatrix, hgsurj, hkeep⟩ :=
      ih hprev
    let pg : Fin n → Smale.ManifoldMorse.criticalPoints E g := fun j =>
      ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
    let Bg := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
    obtain
      ⟨u, hu, hmu, hcu, huorder, huindices, hucounts, huoutside, hucut, husub, hulevel, hua, U,
        hugerms, hufgerms, hpu, hucomplete, hulower, Δ, hΔ, huother, humatrix, husurj, hukeep⟩ :=
      T.exists_arbitrary_column_addition hg hmg hdim hgorder hga hgcut pg hpg hgcomplete hglower
        Bg Γ hΓ hgsurj op.1 op.2.1 hop op.2.2
    let hsub' : ∀ y, u y ≤ a ↔ f y ≤ a := fun y => (husub y).trans (hsub y)
    let hlevel' : ∀ y, u y = a ↔ f y = a := fun y => (hulevel y).trans (hlevel y)
    have hB :
      Bg.trans (MorseCancel.equalCutHomologyEquiv husub) =
        B.trans (MorseCancel.equalCutHomologyEquiv hsub') := by
      change
        (B.trans (MorseCancel.equalCutHomologyEquiv hsub)).trans
            (MorseCancel.equalCutHomologyEquiv husub) =
          _
      rw [LinearEquiv.trans_assoc, MorseCancel.equalCutHomologyEquiv_trans]
    refine
      ⟨u, hu, hmu, hcu.trans hcrit, huorder,
        (fun z hz => (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz)),
        (fun d => (hucounts d).trans (hcounts d)),
        (fun z hz hzo => (huoutside z (hcrit.symm ▸ hz) hzo).trans (houtside z hz hzo)), hucut,
        hsub', hlevel', hua, U, ?_, ?_, hpu, hucomplete, hulower, Δ, hΔ, ?_, ?_, ?_, ?_⟩
    · intro z hz
      filter_upwards [hugerms z (hcrit.symm ▸ hz), hgerms z hz] with y hy hy'
      exact hy.trans hy'
    · intro y hy
      exact (hufgerms y ((hsub y).mpr hy)).trans (hfgerms y hy)
    · intro j hj
      have hlast : j ≠ op.2.1 := fun heq =>
        hj op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op))) heq.symm
      have hbefore : ∀ e ∈ ops, e.2.1 ≠ j := fun e he => hj e (List.mem_append.mpr (Or.inl he))
      rw [huother j hlast, hother j hbefore]
      exact MorseCancel.equalCutSection_trans hlevel hulevel (γ j)
    · rw [← hB, humatrix, hmatrix, Matrix.mul_assoc]
      simp only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
    · rw [← hB]
      exact husurj
    · intro z hz
      have hUT := hukeep z ((hsub z).mpr hz)
      have hTS := hkeep z hz
      exact
        ⟨fun x => (hUT.1 x).trans (hTS.1 x), fun x hx =>
          (hUT.2.1 x ((hTS.1 x).mpr hx)).trans (hTS.2.1 x hx), fun v =>
          (hUT.2.2 v).trans (hTS.2.2 v)⟩

private theorem
    MorseCancel.mul_transvection_list_surjective {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℤ)
    (hA : Function.Surjective A.mulVec) (ops : List (Fin n × Fin n × ℤ))
    (hvalid : ∀ op ∈ ops, op.1 ≠ op.2.1) :
    Function.Surjective
      (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod).mulVec := by
  revert hvalid
  induction ops using List.reverseRecOn with
  | nil =>
    intro hvalid
    simpa only [List.map_nil, List.prod_nil, Matrix.mul_one] using hA
  | append_singleton ops op ih =>
    intro hvalid
    have hprev : ∀ e ∈ ops, e.1 ≠ e.2.1 := fun e he => hvalid e (List.mem_append.mpr (Or.inl he))
    have hop := hvalid op (List.mem_append.mpr (Or.inr (List.mem_singleton_self op)))
    simpa only [List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
      ← Matrix.mul_assoc] using mul_transvection_surjective _ op.1 op.2.1 hop op.2.2 (ih hprev)

private theorem MorseCancel.primitive_row_has_unit_after_column_additions {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) ℤ) (hA : Function.Surjective A.mulVec) :
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
        ∃ i : Fin n,
          (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i = 1 ∨
            (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i = -1 := by
  classical
  have hnonzero : ∃ j, A 0 j ≠ 0 := by
    by_contra hnot
    push Not at hnot
    obtain ⟨x, hx⟩ := hA 1
    have hh := congrFun hx 0
    change ∑ j, A 0 j * x j = 1 at hh
    simp only [hnot, MulZeroClass.zero_mul, Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  let P : ℕ → Prop := fun m =>
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
        ∃ i : Fin n,
          (A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i ≠ 0 ∧
            ((A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod) 0 i).natAbs =
              m
  obtain ⟨j₀, hj₀⟩ := hnonzero
  have hex : ∃ m, P m := by
    refine ⟨(A 0 j₀).natAbs, [], ?_, j₀, ?_, ?_⟩
    · intro op hop
      simp only [List.not_mem_nil] at hop
    · simpa only [List.map_nil, List.prod_nil, Matrix.mul_one] using hj₀
    · simp only [List.map_nil, List.prod_nil, Matrix.mul_one]
  obtain ⟨ops, hvalid, i, hi, hrank⟩ := Nat.find_spec hex
  let C := A * (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod
  have hC : Function.Surjective C.mulVec := mul_transvection_list_surjective A hA ops hvalid
  have hdiv (j : Fin n) : C 0 i ∣ C 0 j := by
    by_cases hij : i = j
    · subst j
      exact dvd_refl _
    apply Int.dvd_of_emod_eq_zero
    by_contra hrem
    let op : Fin n × Fin n × ℤ := (i, j, -(C 0 j / C 0 i))
    let ops' := ops ++ [op]
    have hvalid' : ∀ e ∈ ops', e.1 ≠ e.2.1 := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact hvalid e he
      · have heq : e = op := List.mem_singleton.mp he
        subst e
        exact hij
    have hnew :
      A * (ops'.map (fun e => Matrix.transvection e.1 e.2.1 e.2.2)).prod =
        C * Matrix.transvection i j (-(C 0 j / C 0 i)) := by
      simp only [ops', List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
        ← Matrix.mul_assoc]
      rfl
    have hentry :
      (A * (ops'.map (fun e => Matrix.transvection e.1 e.2.1 e.2.2)).prod) 0 j = C 0 j % C 0 i := by
      rw [hnew, Matrix.mul_transvection_apply_same, Int.emod_def]
      ring
    have hsmall : (C 0 j % C 0 i).natAbs < (C 0 i).natAbs := by
      have hh :=
        Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg (C 0 j) hi)
          (Int.emod_lt_abs (C 0 j) hi)
      simpa only [Int.natAbs_abs] using hh
    have hminimal :=
      Nat.find_min' hex
        (show P (C 0 j % C 0 i).natAbs from
          ⟨ops', hvalid', j, (by rw [hentry]; exact hrem), congrArg Int.natAbs hentry⟩)
    rw [← hrank] at hminimal
    exact (not_le_of_gt hsmall) hminimal
  obtain ⟨x, hx⟩ := hC 1
  have hsum := congrFun hx 0
  change ∑ j, C 0 j * x j = 1 at hsum
  have hdvd : C 0 i ∣ 1 := by
    rw [← hsum]
    exact Finset.dvd_sum (fun j _ => dvd_mul_of_dvd_left (hdiv j) (x j))
  obtain ⟨v, hv⟩ := hdvd
  exact ⟨ops, hvalid, i, Int.eq_one_or_neg_one_of_mul_eq_one hv.symm⟩

private theorem MorseCancel.functional_class_row_surjective {H : Type} [AddCommGroup H] [Module ℤ H]
    {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (v : Fin n → H)
    (hA : Function.Surjective (classCoordinateMatrix B v).mulVec) (L : H →ₗ[ℤ] ℤ)
    (hL : Function.Surjective L) :
    Function.Surjective (Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j))).mulVec := by
  intro y
  obtain ⟨h, hh⟩ := hL (y 0)
  obtain ⟨x, hx⟩ := hA (B.symm h)
  have hsum : (∑ j, x j • v j) = h := by
    rw [← classCoordinateMatrix_mulVec B v x, hx, LinearEquiv.apply_symm_apply]
  refine ⟨x, ?_⟩
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have heq := congrArg L hsum
  rw [map_sum] at heq
  simp only [map_zsmul, smul_eq_mul] at heq
  change ∑ j, L (v j) * x j = y 0
  rw [← hh, ← heq]
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

private theorem MorseCancel.transported_classes_of_matrix_product {H K : Type} [AddCommGroup H]
    [Module ℤ H] [AddCommGroup K] [Module ℤ K] {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (e : H ≃ₗ[ℤ] K)
    (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : classCoordinateMatrix (B.trans e) w = classCoordinateMatrix B v * P) (j : Fin n) :
    e.symm (w j) = ∑ i, P i j • v i := by
  have hvec : (classCoordinateMatrix B v).mulVec (fun i => P i j) = (B.trans e).symm (w j) := by
    funext i
    exact (congrFun (congrFun hmatrix i) j).symm
  calc
    e.symm (w j) = B ((classCoordinateMatrix B v).mulVec (fun i => P i j)) := by
      rw [hvec]
      exact (B.apply_symm_apply (e.symm (w j))).symm
    _ = _ := classCoordinateMatrix_mulVec B v _

private theorem
    MorseCancel.functional_rows_of_matrix_product {H K : Type} [AddCommGroup H] [Module ℤ H]
    [AddCommGroup K] [Module ℤ K] {r n : ℕ} (B : (Fin r → ℤ) ≃ₗ[ℤ] H) (e : H ≃ₗ[ℤ] K)
    (v : Fin n → H) (w : Fin n → K) (P : Matrix (Fin n) (Fin n) ℤ)
    (hmatrix : classCoordinateMatrix (B.trans e) w = classCoordinateMatrix B v * P)
    (L : H →ₗ[ℤ] ℤ) :
    Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (e.symm (w j))) =
      Matrix.of (fun (_ : Fin 1) (j : Fin n) => L (v j)) * P := by
  funext u j
  change L (e.symm (w j)) = ∑ i, L (v i) * P i j
  rw [transported_classes_of_matrix_product B e v w P hmatrix j, map_sum]
  simp only [map_zsmul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem AdaptedWindows.exists_primitive_functional_unit {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → MorseCancel.nativeMorseIndex E f x ≤ MorseCancel.nativeMorseIndex E f y)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z < 3 → f z < a)
    {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, MorseCancel.nativeMorseIndex E f (p j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        MorseCancel.nativeMorseIndex E f z = 3 → ∃ j, p j = z)
    (hlower : ∀ j, a < S.toSurgeryWindows.lower (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec)
    (L : SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 →ₗ[ℤ] ℤ)
    (hL : Function.Surjective L) :
    ∃ ops : List (Fin n × Fin n × ℤ),
      (∀ op ∈ ops, op.1 ≠ op.2.1) ∧
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
                    (∀ d,
                        MorseCancel.nativeMorseCount E g d = MorseCancel.nativeMorseCount E f d) ∧
                      (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                          (∀ j, z ≠ (p j).val) → g z = f z) ∧
                        (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                            MorseCancel.nativeMorseIndex E g z < 3 → g z < a) ∧
                          ∃ hsub : ∀ y, g y ≤ a ↔ f y ≤ a,
                            ∃ hlevel : ∀ y, g y = a ↔ f y = a,
                              ∃ hga : ∀ y, g y = a → y ∉ Smale.ManifoldMorse.criticalPoints E g,
                                ∃ T : AdaptedWindows E g,
                                  (∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
                                      ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
                                    (∀ y, f y ≤ a → g =ᶠ[𝓝 y] f) ∧
                                      let p' : Fin n → Smale.ManifoldMorse.criticalPoints E g :=
                                        fun j => ⟨(p j).val, hcrit.symm ▸ (p j).property⟩
                                      let B' := B.trans (MorseCancel.equalCutHomologyEquiv hsub)
                                      (∀ j, MorseCancel.nativeMorseIndex E g (p' j) = 3) ∧
                                        (∀ z : Smale.ManifoldMorse.criticalPoints E g,
                                            MorseCancel.nativeMorseIndex E g z = 3 →
                                              ∃ j, p' j = z) ∧
                                          (∀ j, a < T.toSurgeryWindows.lower (p' j)) ∧
                                            ∃ Γ :
                                              Fin n →
                                                C((Smale.Hemisphere.Sphere 2),
                                                  { y : M // g y = a }),
                                              MorseCancel.IsNativeMiddleBasinFamily T hg hga p'
                                                  (fun j => Γ j) ∧
                                                (∀ j,
                                                    (∀ op ∈ ops, op.2.1 ≠ j) →
                                                      Γ j =
                                                        MorseCancel.equalCutSection hlevel
                                                          (γ j)) ∧
                                                  MorseCancel.canonicalMiddleMatrix (M := M) (f :=
                                                        g) (a := a) (r := r) (n := n) B' Γ =
                                                      MorseCancel.canonicalMiddleMatrix (M := M)
                                                          (f := f) (a := a) (r := r) (n := n) B
                                                          γ *
                                                        (ops.map
                                                            (fun op =>
                                                              Matrix.transvection op.1 op.2.1
                                                                op.2.2)).prod ∧
                                                    Function.Surjective
                                                        (MorseCancel.canonicalMiddleMatrix B'
                                                            Γ).mulVec ∧
                                                      (∃ i : Fin n,
                                                          L
                                                                ((MorseCancel.equalCutHomologyEquiv
                                                                      hsub).symm
                                                                  (MorseCancel.middleSectionClass
                                                                    (Γ i))) =
                                                              1 ∨
                                                            L
                                                                ((MorseCancel.equalCutHomologyEquiv
                                                                      hsub).symm
                                                                  (MorseCancel.middleSectionClass
                                                                    (Γ i))) =
                                                              -1) ∧
                                                        ∀ z : M,
                                                          f z ≤ a →
                                                            (∀ x,
                                                                Filter.Tendsto
                                                                    (fun t => T.flow t x)
                                                                    Filter.atBot (𝓝 z) ↔
                                                                  Filter.Tendsto
                                                                    (fun t => S.flow t x)
                                                                    Filter.atBot (𝓝 z)) ∧
                                                              (∀ x,
                                                                  Filter.Tendsto
                                                                      (fun t => S.flow t x)
                                                                      Filter.atBot (𝓝 z) →
                                                                    Set.range
                                                                        (fun t => T.flow t x) =
                                                                      Set.range
                                                                        (fun t => S.flow t x)) ∧
                                                                ∀ v,
                                                                  Filter.Tendsto
                                                                      (fun t => T.flow t z)
                                                                      Filter.atTop (𝓝 v) ↔
                                                                    Filter.Tendsto
                                                                      (fun t => S.flow t z)
                                                                      Filter.atTop (𝓝 v) := by
  let A : Matrix (Fin 1) (Fin n) ℤ := fun _ j => L (MorseCancel.middleSectionClass (γ j))
  have hsurj' :
    Function.Surjective
      (MorseCancel.classCoordinateMatrix B
          (fun j => MorseCancel.middleSectionClass (γ j))).mulVec := by
    simpa only [MorseCancel.canonicalMiddleMatrix] using hsurj
  have hA : Function.Surjective A.mulVec :=
    MorseCancel.functional_class_row_surjective B (fun j => MorseCancel.middleSectionClass (γ j))
      hsurj' L hL
  obtain ⟨ops, hvalid, i, hi⟩ := MorseCancel.primitive_row_has_unit_after_column_additions A hA
  obtain
    ⟨g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut, hsub, hlevel, hga, T, hgerms,
      hfgerms, hpg, hgcomplete, hglower, Γ, hΓ, hother, hmatrix, hgsurj, hkeep⟩ :=
    S.exists_arbitrary_column_sequence hf hm hdim horder ha hcut p hp hcomplete hlower B γ hγ
      hsurj ops hvalid
  have hcoord :
    MorseCancel.classCoordinateMatrix (B.trans (MorseCancel.equalCutHomologyEquiv hsub))
        (fun j => MorseCancel.middleSectionClass (Γ j)) =
      MorseCancel.classCoordinateMatrix B (fun j => MorseCancel.middleSectionClass (γ j)) *
        (ops.map (fun op => Matrix.transvection op.1 op.2.1 op.2.2)).prod := by
    simpa only [MorseCancel.canonicalMiddleMatrix] using hmatrix
  have hrows :=
    MorseCancel.functional_rows_of_matrix_product B (MorseCancel.equalCutHomologyEquiv hsub)
      (fun j => MorseCancel.middleSectionClass (γ j))
      (fun j => MorseCancel.middleSectionClass (Γ j)) _ hcoord L
  have hentry := congrFun (congrFun hrows 0) i
  refine
    ⟨ops, hvalid, g, hg, hmg, hcrit, hgorder, hindices, hcounts, houtside, hgcut, hsub, hlevel,
      hga, T, hgerms, hfgerms, hpg, hgcomplete, hglower, Γ, hΓ, hother, hmatrix, hgsurj, ⟨i, ?_⟩,
      hkeep⟩
  exact hi.elim (fun h => Or.inl (hentry.trans h)) (fun h => Or.inr (hentry.trans h))

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private def
    MorseCancel.regularCutHomologyEquiv {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ}
    (hab : a ≤ b) (hband : ∀ y, f y ∈ Set.Icc a b → y ∉ Smale.ManifoldMorse.criticalPoints E f) :
    SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2 ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology { y : M // f y ≤ b } 2 :=
  LinearEquiv.ofBijective (SingularMayerVietoris.singularHomologyMap (sublevelMap f hab) 2)
    (regular_sublevel_inclusion_bijective hf hab hband 2)

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem AdaptedWindows.exists_lower_cut_geometric_matrix {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a b : ℝ} (hba : b < a)
    (ha : ∀ y, f y = a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (hband : ∀ y, f y ∈ Set.Icc b a → y ∉ Smale.ManifoldMorse.criticalPoints E f)
    (za : { y : M // f y = a }) {r n : ℕ} (p : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hp : ∀ j, a < f (p j))
    (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }))
    (hγ : MorseCancel.IsNativeMiddleBasinFamily S hf ha p (fun j => γ j))
    (hsurj : Function.Surjective (MorseCancel.canonicalMiddleMatrix B γ).mulVec) :
    ∃ β : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = b }),
      MorseCancel.IsNativeMiddleBasinFamily S hf hb p (fun j => β j) ∧
        (∀ j x, ∃ t : ℝ, S.flow t (γ j x).val = (β j x).val) ∧
          (∀ j,
              MorseCancel.regularCutHomologyEquiv hf hba.le hband
                  (MorseCancel.middleSectionClass (β j)) =
                MorseCancel.middleSectionClass (γ j)) ∧
            let B' := B.trans (MorseCancel.regularCutHomologyEquiv hf hba.le hband).symm
            MorseCancel.canonicalMiddleMatrix B' β = MorseCancel.canonicalMiddleMatrix B γ ∧
              Function.Surjective (MorseCancel.canonicalMiddleMatrix B' β).mulVec := by
  let _ := Smale.RegularLevel.chartedSpace hf hb
  obtain ⟨β₀, hβ, horbit⟩ :=
    S.exists_regular_band_middle_basin_family hf hba ha hb (fun y hy h => hband y h hy) za p hp
      (fun j => γ j) hγ
  let β : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = b }) := fun j =>
    ⟨β₀ j, (hβ.1 j).continuous⟩
  have hclass (j : Fin n) :
    MorseCancel.regularCutHomologyEquiv hf hba.le hband (MorseCancel.middleSectionClass (β j)) =
      MorseCancel.middleSectionClass (γ j) :=
    S.section_class_of_flow_transport hf hba hb (γ j) (β j) (horbit j)
  let B' := B.trans (MorseCancel.regularCutHomologyEquiv hf hba.le hband).symm
  have hmatrix : MorseCancel.canonicalMiddleMatrix B' β = MorseCancel.canonicalMiddleMatrix B γ :=
    by
    funext i j
    simp only [MorseCancel.canonicalMiddleMatrix, MorseCancel.classCoordinateMatrix]
    change
      B.symm
          (MorseCancel.regularCutHomologyEquiv hf hba.le hband
            (MorseCancel.middleSectionClass (β j)))
          i =
        B.symm (MorseCancel.middleSectionClass (γ j)) i
    rw [hclass j]
  refine ⟨β, hβ, horbit, hclass, hmatrix, ?_⟩
  rw [hmatrix]
  exact hsurj

private theorem MorseCancel.native_middle_block_complete_and_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count) :
    (∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z = 3 → ∃ j, nativeMiddleBlockPoint S r n hrc j = z) ∧
      (∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z < 3 → f z < nativeMiddleBaseCut S r n hrc) := by
  obtain ⟨r', n', htwo, hrc', hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr', hn'⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r' n' htwo hrc' hthree hafter
  have hrr : r' = r := hr'.symm.trans hr
  have hnn : n' = n := hn'.symm.trans hn
  rw [hrr] at htwo
  rw [hrr, hnn] at hthree hafter
  let W := S.toSurgeryWindows
  have hrcW : r + n < W.count := hrc
  have hpos := W.count_pos hf
  have hi0 (i : Fin W.count) (hi : i.val = 0) : nativeMorseIndex E f (W.point i) = 0 := by
    have he : i = ⟨0, hpos⟩ := Fin.ext hi
    rw [he]
    exact
      (nativeMorseIndex_eq_chart (S.data (W.first hpos)).chart).trans (W.first_index_zero hf hpos)
  have hi2 (i : Fin W.count) (hi : 0 < i.val) (hir : i.val ≤ r) :
    nativeMorseIndex E f (W.point i) = 2 :=
    (nativeMorseIndex_eq_chart (S.data (W.point i)).chart).trans (htwo i hi hir)
  have hi3 (i : Fin W.count) (hri : r < i.val) (hin : i.val ≤ r + n) :
    nativeMorseIndex E f (W.point i) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (W.point i)).chart).trans (hthree i hri hin)
  have hi4 (i : Fin W.count) (hin : r + n < i.val) : 4 ≤ nativeMorseIndex E f (W.point i) := by
    rw [nativeMorseIndex_eq_chart (S.data (W.point i)).chart]
    exact hafter i hin
  constructor
  · intro z hz
    obtain ⟨i, rfl⟩ := W.point.surjective z
    have hiz : i.val ≠ 0 := by
      intro hi
      have hh := hi0 i hi
      omega
    have hri : r < i.val := by
      by_contra hnot
      have hh := hi2 i (by omega) (le_of_not_gt hnot)
      omega
    have hin : i.val ≤ r + n := by
      by_contra hnot
      have hh := hi4 i (lt_of_not_ge hnot)
      omega
    refine ⟨⟨i.val - (r + 1), by omega⟩, ?_⟩
    apply congrArg W.point
    apply Fin.ext
    change r + (i.val - (r + 1)) + 1 = i.val
    omega
  · intro z hz
    obtain ⟨i, rfl⟩ := W.point.surjective z
    have hir : i.val ≤ r := by
      by_contra hnot
      by_cases hin : i.val ≤ r + n
      · have hh := hi3 i (lt_of_not_ge hnot) hin
        omega
      · have hh := hi4 i (lt_of_not_ge hin)
        omega
    exact
      (W.point_strictMono.monotone (show i ≤ ⟨r, by omega⟩ from hir)).trans_lt
        (W.value_lt_upper _)

private theorem
    Smale.HomologyTransport.integerEquiv_one_natAbs (e : ℤ ≃ₗ[ℤ] ℤ) : (e 1).natAbs = 1 := by
  have h : e.symm 1 * e 1 = 1 := by
    calc
      e.symm 1 * e 1 = e (e.symm 1 • (1 : ℤ)) := by
        rw [map_zsmul, zsmul_eq_mul]
        simp
      _ = 1 := by simp
  exact Int.isUnit_iff_natAbs_eq.mp (IsUnit.of_mul_eq_one_right _ h)

private theorem Smale.SpherePoint.sourceCountMark_topClass_natAbs (n : ℕ) {N : Type}
    [NormedAddCommGroup N] [NormedSpace ℝ N] (j : (ℝ × N) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] N) :
    (sourceCountMark n j B (SphereHomology.unitSphereTopClass (n + 1))).natAbs = 1 :=
  Smale.HomologyTransport.integerEquiv_one_natAbs
    ((SphereHomology.unitSphereHomologyTopEquiv (n + 1)).symm.trans (sourceCountMark n j B))

private theorem
    Smale.OnePointCover.overlapHomologyEquiv_symm_include {N : Type} [NormedAddCommGroup N]
    [NormedSpace ℝ N] (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.PuncturedRadial.Space N) k) :
    (overlapHomologyEquiv r hr k).symm
        (SingularMayerVietoris.singularHomologyMap overlapHomeomorph.toHomotopyEquiv.toFun k a) =
      SingularMayerVietoris.singularHomologyMap Smale.PuncturedRadial.toSphere k a := by
  change
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (overlapSphereEquiv r hr) k).symm _ = _
  rw [PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_symm_apply]
  have heq :
    (overlapSphereEquiv (N := N) r hr).symm.toFun.comp overlapHomeomorph.toHomotopyEquiv.toFun =
      Smale.PuncturedRadial.toSphere := by
    apply ContinuousMap.ext
    intro x
    change Smale.PuncturedRadial.toSphere (overlapHomeomorph.symm (overlapHomeomorph x)) = _
    rw [Homeomorph.symm_apply_apply]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp, heq]

attribute [local instance 100] Classical.propDecidable in
private def Smale.ManifoldMorse.MorseSurgeryData.collapseComponentConnecting {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ) :
    SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1) →ₗ[ℤ]
      (∀ i : d.beltIntersectionPoints m g,
        SingularMayerVietoris.SingularHomology
          (↥((d.beltIntersectionPoints m g)ᶜ ∩ D.neighborhood i)) k) :=
  Smale.CoverLocalContributions.componentConnecting (d.beltIntersectionPoints m g)ᶜ D.neighborhood
    (Set.toFinite _).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint D.open_cover
    k

attribute [local instance 100] Classical.propDecidable in
private def
    Smale.ManifoldMorse.MorseSurgeryData.collapseLocalClass {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1))
    (i : d.beltIntersectionPoints m g) :
    SingularMayerVietoris.SingularHomology (Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) k :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv i) k).symm
    (d.collapseComponentConnecting m g D k a i)

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.collapseConnecting_sum_overlaps {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1)) :
    SingularMayerVietoris.connectingHomomorphism Smale.OnePointCover.oldPatch
        Smale.OnePointCover.finitePatch Smale.OnePointCover.oldPatch_open
        Smale.OnePointCover.finitePatch_open Smale.OnePointCover.cover k
        (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (d.collapseOverlapMap hf m g D i) k
          (d.collapseComponentConnecting m g D k a i) :=
  Smale.CoverLocalContributions.connecting_sum (d.beltIntersectionPoints m g)ᶜ D.neighborhood
    (Set.toFinite _).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint D.open_cover
    Smale.OnePointCover.oldPatch Smale.OnePointCover.finitePatch (d.attachingCollapse hf m g)
    (d.attachingCollapse_maps_old hf m g) (d.attachingCollapse_maps_neighborhood hf m g D)
    Smale.OnePointCover.oldPatch_open Smale.OnePointCover.finitePatch_open
    Smale.OnePointCover.cover k a

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.collapseConnecting_sum_boundaries {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1)) :
    SingularMayerVietoris.connectingHomomorphism Smale.OnePointCover.oldPatch
        Smale.OnePointCover.finitePatch Smale.OnePointCover.oldPatch_open
        Smale.OnePointCover.finitePatch_open Smale.OnePointCover.cover k
        (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap
          (Smale.OnePointCover.overlapHomeomorph.toHomotopyEquiv.toFun.comp
            (D.data i).innerBoundary.map)
          k (d.collapseLocalClass m g D k a i) := by
  rw [d.collapseConnecting_sum_overlaps hf m g D k a]
  apply Finset.sum_congr rfl
  intro i _
  have h :
    SingularMayerVietoris.singularHomologyMap (D.overlapSphereEquiv i).toFun k
        (d.collapseLocalClass m g D k a i) =
      d.collapseComponentConnecting m g D k a i :=
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv i)
          k).apply_symm_apply
      _
  rw [← h, ← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp,
    d.collapseOverlapMap_sphereEquiv hf m g D i]

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.collapseSphereConnecting_sum {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (m : ℕ) (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1)) :
    Smale.OnePointCover.sphereConnecting r hr k
        (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a) =
      ∑ i,
        SingularMayerVietoris.singularHomologyMap (D.data i).innerBoundary.normalizedMap k
          (d.collapseLocalClass m g D k a i) := by
  change
    (Smale.OnePointCover.overlapHomologyEquiv (N := d.chart.NegativeCoordinates) r hr k).symm
        (SingularMayerVietoris.connectingHomomorphism Smale.OnePointCover.oldPatch
          Smale.OnePointCover.finitePatch Smale.OnePointCover.oldPatch_open
          Smale.OnePointCover.finitePatch_open Smale.OnePointCover.cover k
          (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf m g) (k + 1) a)) =
      _
  rw [d.collapseConnecting_sum_boundaries hf m g D k a, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply,
    Smale.OnePointCover.overlapHomologyEquiv_symm_include]
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

private theorem Smale.CoverOverlapHomology.homologyEquiv_symm_single {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U)
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (k : ℕ) (i : ι)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :
    (homologyEquiv U V hU hV hd k).symm (Pi.single i a) =
      SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k a := by
  rw [homologyEquiv_symm_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ hji
    rw [Pi.single_eq_of_ne hji, map_zero]
  · simp

private theorem Smale.CoverOverlapHomology.homologyEquiv_inclusion {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] [DecidableEq ι] (U : Set X) (V : ι → Set X) (hU : IsOpen U)
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (k : ℕ) (i : ι)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ V i)) k) :
    homologyEquiv U V hU hV hd k
        (SingularMayerVietoris.singularHomologyMap (componentInclusion U V i) k a) =
      Pi.single i a := by
  apply (homologyEquiv U V hU hV hd k).symm.injective
  rw [LinearEquiv.symm_apply_apply, homologyEquiv_symm_single]

private def
    Smale.CoverOverlapHomology.componentMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y) (f : C(X, Y))
    (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) (i : ι) :
    C(↥(U ∩ V i), ↥(U' ∩ V' i)) :=
  Smale.CoverNaturality.mapOn f _ _ (fun _ hx => ⟨hfU hx.1, hfV i hx.2⟩)

private def
    Smale.CoverOverlapHomology.overlapMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y) (f : C(X, Y))
    (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) :
    C(↥(U ∩ ⋃ i, V i), ↥(U' ∩ ⋃ i, V' i)) :=
  Smale.CoverNaturality.mapOn f _ _
    (by
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx.2
      exact ⟨hfU hx.1, Set.mem_iUnion.mpr ⟨i, hfV i hi⟩⟩)

private theorem Smale.CoverOverlapHomology.overlapMap_component {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y)
    (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) (i : ι) :
    (overlapMap U V U' V' f hfU hfV).comp (componentInclusion U V i) =
      (componentInclusion U' V' i).comp (componentMap U V U' V' f hfU hfV i) :=
  rfl

private theorem Smale.CoverOverlapHomology.homologyEquiv_map {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] {ι : Type} (U : Set X) (V : ι → Set X) (U' : Set Y) (V' : ι → Set Y)
    (f : C(X, Y)) (hfU : Set.MapsTo f U U') (hfV : ∀ i, Set.MapsTo f (V i) (V' i)) [Fintype ι]
    (hU : IsOpen U) (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (hU' : IsOpen U')
    (hV' : ∀ i, IsOpen (V' i)) (hd' : Pairwise (Disjoint on V')) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (↥(U ∩ ⋃ i, V i)) k) :
    homologyEquiv U' V' hU' hV' hd' k
        (SingularMayerVietoris.singularHomologyMap (overlapMap U V U' V' f hfU hfV) k a) =
      fun i =>
      SingularMayerVietoris.singularHomologyMap (componentMap U V U' V' f hfU hfV i) k
        (homologyEquiv U V hU hV hd k a i) := by
  apply (homologyEquiv U' V' hU' hV' hd' k).symm.injective
  rw [LinearEquiv.symm_apply_apply, homologyEquiv_symm_apply, homology_map_out U V hU hV hd]
  apply Finset.sum_congr rfl
  intro i _
  rw [overlapMap_component, PeriodTorusHigherHomology.singularHomologyMap_comp,
    LinearMap.comp_apply]

private theorem
    Smale.CoverLocalContributions.componentConnecting_enlarge {X : Type} [TopologicalSpace X]
    {ι : Type} [Fintype ι] (U U' : Set X) (V : ι → Set X) (hU : IsOpen U) (hU' : IsOpen U')
    (hV : ∀ i, IsOpen (V i)) (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = Set.univ)
    (hsub : U ⊆ U') (i : ι) (hci : U' ∪ V i = Set.univ) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (k + 1)) :
    SingularMayerVietoris.singularHomologyMap
        (Smale.CoverOverlapHomology.componentMap U V U' V (ContinuousMap.id X) hsub
          (fun _ _ hx => hx) i)
        k (componentConnecting U V hU hV hd hc k a i) =
      SingularMayerVietoris.connectingHomomorphism U' (V i) hU' (hV i) hci k a := by
  classical
  have hc' : U' ∪ (⋃ j, V j) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ U ∪ (⋃ j, V j) := hc.symm ▸ Set.mem_univ x
    exact hx.elim (fun hu => Or.inl (hsub hu)) Or.inr
  have hbig :=
    Smale.CoverNaturality.connecting_naturality_apply U (⋃ j, V j) U' (⋃ j, V j)
      (ContinuousMap.id X) hsub (fun _ hx => hx) hU (isOpen_iUnion hV) hc hU' (isOpen_iUnion hV)
      hc' k a
  rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at hbig
  change
    SingularMayerVietoris.singularHomologyMap
        (Smale.CoverOverlapHomology.overlapMap U V U' V (ContinuousMap.id X) hsub
          (fun _ _ hx => hx))
        k
        (SingularMayerVietoris.connectingHomomorphism U (⋃ j, V j) hU (isOpen_iUnion hV) hc k a) =
      SingularMayerVietoris.connectingHomomorphism U' (⋃ j, V j) hU' (isOpen_iUnion hV) hc' k
        a at hbig
  have hcoord :=
    congrArg (fun b => Smale.CoverOverlapHomology.homologyEquiv U' V hU' hV hd k b i) hbig
  have hnat :=
    congrFun
      (Smale.CoverOverlapHomology.homologyEquiv_map U V U' V (ContinuousMap.id X) hsub
        (fun _ _ hx => hx) hU hV hd hU' hV hd k
        (SingularMayerVietoris.connectingHomomorphism U (⋃ j, V j) hU (isOpen_iUnion hV) hc k a))
      i
  rw [hnat] at hcoord
  have hsmall :=
    Smale.CoverNaturality.connecting_naturality_apply U' (V i) U' (⋃ j, V j) (ContinuousMap.id X)
      (fun _ hx => hx) (Set.subset_iUnion V i) hU' (hV i) hci hU' (isOpen_iUnion hV) hc' k a
  rw [PeriodTorusHigherHomology.singularHomologyMap_id, LinearMap.id_apply] at hsmall
  change
    SingularMayerVietoris.singularHomologyMap
        (Smale.CoverOverlapHomology.componentInclusion U' V i) k
        (SingularMayerVietoris.connectingHomomorphism U' (V i) hU' (hV i) hci k a) =
      SingularMayerVietoris.connectingHomomorphism U' (⋃ j, V j) hU' (isOpen_iUnion hV) hc' k
        a at hsmall
  have hsingle :=
    congrArg (fun b => Smale.CoverOverlapHomology.homologyEquiv U' V hU' hV hd k b i) hsmall
  rw [Smale.CoverOverlapHomology.homologyEquiv_inclusion, Pi.single_eq_same] at hsingle
  exact hcoord.trans hsingle.symm

private def Smale.LocalDegree.SeparatedNeighborhoods.pointComplementInclusion {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M} {f : M → F}
    {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    C(↥(Pᶜ ∩ D.neighborhood x), ↥({(x : M)}ᶜ ∩ D.neighborhood x)) :=
  (Homeomorph.setCongr (D.overlap_eq x)).toHomotopyEquiv.toFun

private theorem Smale.LocalDegree.SeparatedNeighborhoods.pointComplementInclusion_sphereEquiv
    {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {P : Set M}
    {f : M → F} {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) (x : P) :
    (D.pointComplementInclusion x).comp (D.overlapSphereEquiv x).toFun =
      (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).toFun := by
  apply ContinuousMap.ext
  intro u
  rfl

private theorem
    Smale.LocalDegree.SeparatedNeighborhoods.componentConnecting_singlePoint {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] {P : Set M}
    {f : M → F} {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) [Fintype P]
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) (x : P) :
    SingularMayerVietoris.singularHomologyMap (D.pointComplementInclusion x) k
        (Smale.CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
          (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint
          D.open_cover k a x) =
      SingularMayerVietoris.connectingHomomorphism {(x : M)}ᶜ (D.neighborhood x)
        isClosed_singleton.isOpen_compl (D.isOpen_neighborhood x)
        (Smale.LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a := by
  have hsub : Pᶜ ⊆ {(x : M)}ᶜ := by
    intro y hy hxy
    exact hy (hxy ▸ x.property)
  exact
    Smale.CoverLocalContributions.componentConnecting_enlarge Pᶜ {(x : M)}ᶜ D.neighborhood
      (Set.toFinite P).isClosed.isOpen_compl isClosed_singleton.isOpen_compl D.isOpen_neighborhood
      D.pairwise_disjoint D.open_cover hsub x
      (Smale.LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a

private theorem Smale.LocalDegree.SeparatedNeighborhoods.sphereConnecting_component {E F M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T1Space M] {P : Set M}
    {f : M → F} {W : Set M} (D : Smale.LocalDegree.SeparatedNeighborhoods E P f W) [Fintype P]
    (k : ℕ) (a : SingularMayerVietoris.SingularHomology M (k + 1)) (x : P) :
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
        (Smale.CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
          (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint
          D.open_cover k a x) =
      Smale.LocalDegree.NativeNeighborhood.sphereConnecting (x : M) (D.data x) k a := by
  let c :=
    Smale.CoverLocalContributions.componentConnecting Pᶜ D.neighborhood
      (Set.toFinite P).isClosed.isOpen_compl D.isOpen_neighborhood D.pairwise_disjoint
      D.open_cover k a x
  apply
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k).injective
  change
    SingularMayerVietoris.singularHomologyMap
        (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).toFun k
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
          c) =
      (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k)
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
              (Smale.LocalDegree.NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)) k).symm
          _)
  rw [LinearEquiv.apply_symm_apply, ← D.pointComplementInclusion_sphereEquiv x]
  change
    SingularMayerVietoris.singularHomologyMap
        ((D.pointComplementInclusion x).comp (D.overlapSphereEquiv x).toFun) k
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
          c) =
      SingularMayerVietoris.connectingHomomorphism {(x : M)}ᶜ (D.neighborhood x)
        isClosed_singleton.isOpen_compl (D.isOpen_neighborhood x)
        (Smale.LocalDegree.NativeNeighborhood.singlePoint_cover (x : M) (D.data x)) k a
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp, LinearMap.comp_apply]
  have h :
    SingularMayerVietoris.singularHomologyMap (D.overlapSphereEquiv x).toFun k
        ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x) k).symm
          c) =
      c :=
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (D.overlapSphereEquiv x)
          k).apply_symm_apply
      c
  rw [h]
  exact D.componentConnecting_singlePoint k a x

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.collapseLocalClass_singlePoint {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (g : C(Smale.Hemisphere.Sphere m, d.UpperLevel)) (D : d.CollapseNeighborhoods m g)
    [Fintype (d.beltIntersectionPoints m g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (Smale.Hemisphere.Sphere m) (k + 1))
    (i : d.beltIntersectionPoints m g) :
    d.collapseLocalClass m g D k a i =
      Smale.LocalDegree.NativeNeighborhood.sphereConnecting i.val (D.data i) k a :=
  D.sphereConnecting_component k a i

private theorem Smale.SphereNormalCoordinates.localBoundary_homology_outward {V F : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (n : ℕ) [Fact (Module.finrank ℝ V = (n + 2) + 1)]
    (c :
      PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 2))) (𝓡 (n + 2))
        (EuclideanSpace ℝ (Fin (n + 2))) (Metric.sphere (0 : V) 1) ∞)
    (j : (ℝ × F) ≃L[ℝ] V) (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (hz : (0 : EuclideanSpace ℝ (Fin (n + 2))) ∈ c.source) (f : Metric.sphere (0 : V) 1 → F)
    (hf : MDifferentiableAt (𝓡 (n + 2)) 𝓘(ℝ, F) f (c 0))
    (hA : (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f (c 0)).IsInvertible)
    (L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F)
    (hL : L.toContinuousLinearMap = fderiv ℝ (f ∘ c) 0) {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
    (b : Smale.LocalDegree.BoundaryData (f ∘ c) L s) (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1)) (k + 1)) :
    SingularMayerVietoris.singularHomologyMap b.normalizedMap (k + 1)
        ((SignType.sign (chartJacobian c j B 0) : ℤ) • a) =
      (SignType.sign (normalJacobian j (c 0) (mfderiv (𝓡 (n + 2)) 𝓘(ℝ, F) f (c 0))) : ℤ) •
        SingularMayerVietoris.singularHomologyMap
          (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1) a := by
  have hs := chartJacobian_sign_factor c j B hz f hf hA
  have hd :
    (L.trans B.symm).toLinearEquiv.toLinearMap.det =
      (B.symm.toContinuousLinearMap.comp (fderiv ℝ (f ∘ c) 0)).det := by
    rw [← hL]
    rfl
  rw [← hd] at hs
  have hi := congrArg (fun v : SignType => (v : ℤ)) hs
  simp only [SignType.coe_mul] at hi
  rw [map_zsmul, b.normalized_homology_eq_sign_smul n B k a, smul_smul, hi]

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.collapseLocalBoundary_homology_sign_of_transverse
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : Smale.Hemisphere.Sphere (n + 2) → d.UpperLevel) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient ((n + 2) + 1)) = (n + 2) + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (x : Smale.Hemisphere.Sphere (n + 2)),
      x ∈ d.beltIntersectionPoints (n + 2) g →
        ∀ (L : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates),
          L.toContinuousLinearMap =
              fderiv ℝ ((d.collapseNormal ∘ g) ∘ Smale.NativeParametrization.centered x) 0 →
            ∀ {s : Set (EuclideanSpace ℝ (Fin (n + 2)))}
              (b :
                Smale.LocalDegree.BoundaryData
                  ((d.collapseNormal ∘ g) ∘ Smale.NativeParametrization.centered x) L s)
              (k : ℕ)
              (a :
                SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 1))
                  (k + 1)),
              SingularMayerVietoris.singularHomologyMap b.normalizedMap (k + 1)
                  ((SignType.sign
                        (Smale.SphereNormalCoordinates.chartJacobian
                          (Smale.NativeParametrization.centered x) j B 0) :
                      ℤ) •
                    a) =
                (d.beltIntersectionSign (n + 2) j g x : ℤ) •
                  SingularMayerVietoris.singularHomologyMap
                    (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective)
                    (k + 1) a := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient ((n + 2) + 1)) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg ht x hx L hL s b k a
  have hs := d.contMDiffAt_collapseNormal_comp hf (n + 2) g hg x hx
  have hA := d.isInvertible_collapseNormal_comp_of_transverse hf q (n + 2) hdim g hg ht x hx
  have hc0 := Smale.NativeParametrization.centered_zero (D := EuclideanSpace ℝ (Fin (n + 2))) x
  have h :=
    Smale.SphereNormalCoordinates.localBoundary_homology_outward n
      (Smale.NativeParametrization.centered x) j B
      (Smale.NativeParametrization.zero_mem_centered_source x) (d.collapseNormal ∘ g)
      (hc0.symm ▸ hs.mdifferentiableAt (by simp)) (hc0.symm ▸ hA) L hL b k a
  rw [hc0, d.collapseNormal_comp_sign_of_transverse hf q (n + 2) hdim j g hg ht x hx] at h
  exact h

private theorem Smale.ManifoldMorse.MorseSurgeryData.instLocal1 (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
  ⟨by simp⟩

attribute [local instance] Smale.ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.collapseLocalClass_eq_outward {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (n : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Smale.Hemisphere.Sphere (n + 2), d.UpperLevel)) (D : d.CollapseNeighborhoods (n + 2) g)
    [Fintype (d.beltIntersectionPoints (n + 2) g)] (k : ℕ)
    (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2))
    (i : d.beltIntersectionPoints (n + 2) g) :
    d.collapseLocalClass (n + 2) g D (k + 1) a i =
      (SignType.sign
            (Smale.SphereNormalCoordinates.chartJacobian
              (Smale.NativeParametrization.centered i.val) j B 0) :
          ℤ) •
        Smale.SpherePoint.outwardClass n j B k a := by
  rw [d.collapseLocalClass_singlePoint]
  exact Smale.SpherePoint.pointConnecting_eq_outward n j B i.val (D.data i) k a

attribute [local instance] Smale.ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.collapseLocalBoundary_outward {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Smale.Hemisphere.Sphere (n + 2), d.UpperLevel)) (D : d.CollapseNeighborhoods (n + 2) g)
    [Fintype (d.beltIntersectionPoints (n + 2) g)] :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (k : ℕ)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2))
      (i : d.beltIntersectionPoints (n + 2) g),
      SingularMayerVietoris.singularHomologyMap (D.data i).innerBoundary.normalizedMap (k + 1)
          (d.collapseLocalClass (n + 2) g D (k + 1) a i) =
        (d.beltIntersectionSign (n + 2) j g i.val : ℤ) •
          SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1)
            (Smale.SpherePoint.outwardClass n j B k a) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg ht k a i
  rw [d.collapseLocalClass_eq_outward n j B g D k a i]
  exact
    d.collapseLocalBoundary_homology_sign_of_transverse hf q n hdim j B g hg ht i.val i.property
      (D.linear i) (D.derivative_eq i) (D.data i).innerBoundary k _

attribute [local instance] Smale.ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.beltIntersectionCount_smul {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (m : ℕ)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient (m + 1))
    (g : Smale.Hemisphere.Sphere m → d.UpperLevel) [Fintype (d.beltIntersectionPoints m g)]
    (hfin : (d.beltIntersectionPoints m g).Finite) {A : Type*} [AddCommGroup A] (a : A) :
    (∑ i : d.beltIntersectionPoints m g, (d.beltIntersectionSign m j g i.val : ℤ) • a) =
      d.beltIntersectionCount m j g hfin • a := by
  have hcount :
    (∑ i : d.beltIntersectionPoints m g, (d.beltIntersectionSign m j g i.val : ℤ)) =
      d.beltIntersectionCount m j g hfin :=
    (Finset.sum_subtype hfin.toFinset (fun _ => hfin.mem_toFinset)
        (fun x => (d.beltIntersectionSign m j g x : ℤ))).symm
  exact Finset.sum_smul.symm.trans (congrArg (fun z : ℤ => z • a) hcount)

attribute [local instance] Smale.ManifoldMorse.MorseSurgeryData.instLocal1 in
attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.collapseSphereConnecting_signed_count {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ}
    {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) [FiniteDimensional ℝ E] [T2Space M]
    [IsManifold 𝓘(ℝ, E) ∞ M] (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q n : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Smale.Hemisphere.Sphere (n + 2), d.UpperLevel)) (D : d.CollapseNeighborhoods (n + 2) g)
    [Finite (d.beltIntersectionPoints (n + 2) g)] :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (r : ℝ) (hr : 0 < r) (k : ℕ)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)),
      Smale.OnePointCover.sphereConnecting r hr (k + 1)
          (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf.continuous (n + 2) g)
            (k + 2) a) =
        d.beltIntersectionCount (n + 2) j g (Set.toFinite _) •
          SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1)
            (Smale.SpherePoint.outwardClass n j B k a) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fintype (d.beltIntersectionPoints (n + 2) g) := Fintype.ofFinite _
  intro hg ht r hr k a
  apply (d.collapseSphereConnecting_sum hf.continuous (n + 2) g D r hr (k + 1) a).trans
  apply
    Eq.trans
      (Finset.sum_congr rfl
        (fun i _ => d.collapseLocalBoundary_outward hf q n hdim j B g D hg ht k a i))
  exact d.beltIntersectionCount_smul (n + 2) j g (Set.toFinite _) _

private theorem Smale.ManifoldMorse.MorseSurgeryData.collapse_homology_signed_count {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hdim : Module.finrank ℝ d.chart.NegativeCoordinates = n + 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient ((n + 2) + 1))
    (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] d.chart.NegativeCoordinates)
    (g : C(Smale.Hemisphere.Sphere (n + 2), d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 (n + 2)) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g)
      (hinj : Function.Injective g)
      (ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 (n + 2)) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (r : ℝ) (hr : 0 < r) (k : ℕ)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere (n + 2)) (k + 2)),
      Smale.OnePointCover.sphereConnecting r hr (k + 1)
          (SingularMayerVietoris.singularHomologyMap (d.attachingCollapse hf.continuous (n + 2) g)
            (k + 2) a) =
        d.beltIntersectionCount (n + 2) j g
            (d.finite_beltIntersectionPoints hf q (n + 2) hdim g hg hinj ht) •
          SingularMayerVietoris.singularHomologyMap
            (Smale.LinearSphereAction.sphereMap B.toContinuousLinearMap B.injective) (k + 1)
            (Smale.SpherePoint.outwardClass n j B k a) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht r hr k a
  let _ : Fintype (d.beltIntersectionPoints (n + 2) g) :=
    (d.finite_beltIntersectionPoints hf q (n + 2) hdim g hg hinj ht).fintype
  obtain ⟨D⟩ := d.nonempty_collapseNeighborhoods hf q (n + 2) hdim g hg hinj ht
  exact d.collapseSphereConnecting_signed_count hf q n hdim j B g D hg ht r hr k a

private theorem Smale.ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_signed_count {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (hinj : Function.Injective g)
      (ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 2) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y)
      (a : SingularMayerVietoris.SingularHomology (SphereHomology.UnitSphere 2) 2),
      d.indexTwoCollapseCoordinate hf.continuous hindex
          (SingularMayerVietoris.singularHomologyMap (d.upperLevelInclusion.comp g) 2 a) =
        d.beltIntersectionCount 2 j g
            (d.finite_beltIntersectionPoints hf q 2 hindex g hg hinj ht) *
          Smale.SpherePoint.sourceCountMark 0 j (d.indexTwoNormalModel hindex) a := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht a
  have h :=
    Smale.SpherePoint.countMark_of_connecting 0 j (d.indexTwoNormalModel hindex) _ a _
      (d.collapse_homology_signed_count hf q 0 hindex j (d.indexTwoNormalModel hindex) g hg hinj
        ht 1 zero_lt_one 0 a)
  have hc :
    d.attachingCollapse hf.continuous 2 g =
      (d.upperCollapseMap hf.continuous).comp (d.upperLevelInclusion.comp g) :=
    rfl
  rw [hc, PeriodTorusHigherHomology.singularHomologyMap_comp] at h
  exact h

private theorem Smale.ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_topClass_natAbs {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (q : ℕ)
    [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = q + 1)]
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (hinj : Function.Injective g)
      (ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 2) (𝓡 q) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            d.surgery.beltSphere x y),
      (d.indexTwoCollapseCoordinate hf.continuous hindex
            (SingularMayerVietoris.singularHomologyMap (d.upperLevelInclusion.comp g) 2
              (SphereHomology.unitSphereTopClass 1))).natAbs =
        (d.beltIntersectionCount 2 j g
            (d.finite_beltIntersectionPoints hf q 2 hindex g hg hinj ht)).natAbs := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hg hinj ht
  rw [d.indexTwoCoordinate_signed_count hf q hindex j g hg hinj ht, Int.natAbs_mul,
    Smale.SpherePoint.sourceCountMark_topClass_natAbs, mul_one]

private theorem
    Smale.ManifoldMorse.MorseSurgeryData.indexTwoCoordinate_transverse_natAbs {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M] [CompactSpace M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (j : (ℝ × d.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, d.UpperLevel))
    (hgood : d.IsTransverseBeltSphere hf hdim hindex g) :
    (d.indexTwoCollapseCoordinate hf.continuous hindex
          (SingularMayerVietoris.singularHomologyMap (d.upperLevelInclusion.comp g) 2
            (SphereHomology.unitSphereTopClass 1))).natAbs =
      (d.beltIntersectionCount 2 j g
          (d.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood)).natAbs := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have h := d.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hg, hinj, _, ht⟩ := hgood
  exact d.indexTwoCoordinate_topClass_natAbs hf 3 hindex j g hg hinj ht

private theorem MorseCancel.last_index_two_collapse_is_primitive {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hrpos : 0 < r) (hrc : r + n < S.toSurgeryWindows.count) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    ∃ hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2,
      Function.Surjective ((S.data q).indexTwoCollapseCoordinate hf.continuous hindex) ∧
        ∀ γ : C(Smale.Hemisphere.Sphere 1, (S.data q).LowerLevel),
          ∃ z, γ.Homotopic (ContinuousMap.const _ z) := by
  obtain ⟨r', n', htwo, hrc', hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr', -⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r' n' htwo hrc' hthree hafter
  have hrr : r' = r := hr'.symm.trans hr
  rw [hrr] at htwo
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  have hindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 :=
    htwo ⟨r, by omega⟩ hrpos le_rfl
  let _ :
    Subsingleton
      (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f q - (S.data q).radius ^ 2 } 1) :=
    S.toSurgeryWindows.lower_homologyOne_subsingleton_of_indices hf ⟨r, by omega⟩ hrpos
      (fun i hi hir => by have hh := htwo i hi hir.le; omega)
  have hnidx : nativeMorseIndex E f q = 2 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).trans hindex
  exact
    ⟨hindex, (S.data q).indexTwoCoordinate_surjective hf.continuous hindex,
      lower_circle_nullhomotopies_of_ordered_native_indices S.toSurgeryWindows hf hdim q hnidx
        hzero hone (fun z hz => (horder z q hz).trans_eq hnidx)⟩

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem MorseCancel.exists_native_belt_cut_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S T : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0) (r n : ℕ)
    (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n) (hrpos : 0 < r)
    (hrc : r + n < S.toSurgeryWindows.count)
    (hradii : ∀ z, (T.data z).radius < (S.data z).radius) :
    let q := S.toSurgeryWindows.point ⟨r, by omega⟩
    let a := nativeMiddleBaseCut S r n hrc
    let p := nativeMiddleBlockPoint S r n hrc
    ∀ (_ : ∀ j, a < T.toSurgeryWindows.lower (p j))
      (B : (Fin r → ℤ) ≃ₗ[ℤ] SingularMayerVietoris.SingularHomology { y : M // f y ≤ a } 2)
      (γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a })),
      IsNativeMiddleBasinFamily T hf (S.data q).upper_regular p (fun j => γ j) →
        Function.Surjective (canonicalMiddleMatrix B γ).mulVec →
          ∃ hindex : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 2,
            Function.Surjective ((T.data q).indexTwoCollapseCoordinate hf.continuous hindex) ∧
              (∀ δ : C(Smale.Hemisphere.Sphere 1, (T.data q).LowerLevel),
                  ∃ z, δ.Homotopic (ContinuousMap.const _ z)) ∧
                (∀ z : Smale.ManifoldMorse.criticalPoints E f,
                    nativeMorseIndex E f z < 3 → f z < T.toSurgeryWindows.upper q) ∧
                  (∀ z : Smale.ManifoldMorse.criticalPoints E f,
                      nativeMorseIndex E f z = 3 → ∃ j, p j = z) ∧
                    (∀ j, T.toSurgeryWindows.upper q < T.toSurgeryWindows.lower (p j)) ∧
                      ∃ β : Fin n → C((Smale.Hemisphere.Sphere 2), (T.data q).UpperLevel),
                        IsNativeMiddleBasinFamily T hf (T.data q).upper_regular p (fun j => β j) ∧
                          (∀ j x, ∃ t : ℝ, T.flow t (γ j x).val = (β j x).val) ∧
                            ∃ B' :
                              (Fin r → ℤ) ≃ₗ[ℤ]
                                SingularMayerVietoris.SingularHomology
                                  { y : M // f y ≤ T.toSurgeryWindows.upper q } 2,
                              canonicalMiddleMatrix B' β = canonicalMiddleMatrix B γ ∧
                                Function.Surjective (canonicalMiddleMatrix B' β).mulVec := by
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  let a := nativeMiddleBaseCut S r n hrc
  let p := nativeMiddleBlockPoint S r n hrc
  dsimp only
  intro hlower B γ hγ hsurj
  have hrcT : r + n < T.toSurgeryWindows.count := hrc
  obtain ⟨hindex, hprimitive, hnull⟩ :=
    last_index_two_collapse_is_primitive T hf hdim horder hzero hone r n hr hrpos hrcT
  obtain ⟨hcomplete, hcut⟩ :=
    native_middle_block_complete_and_cut T hf hdim horder hzero hone r n hr hn hrcT
  have hba : T.toSurgeryWindows.upper q < a := by
    change f q + (T.data q).radius ^ 2 < f q + (S.data q).radius ^ 2
    have hh := hradii q
    nlinarith [(T.data q).radius_pos, (S.data q).radius_pos]
  have hband :
    ∀ y,
      f y ∈ Set.Icc (T.toSurgeryWindows.upper q) a → y ∉ Smale.ManifoldMorse.criticalPoints E f :=
    by
    intro y hy hcrit
    have hqy : f q < f y := (T.toSurgeryWindows.value_lt_upper q).trans_le hy.1
    have heq : y = q.val :=
      S.isolated q y hcrit ⟨((S.toSurgeryWindows.lower_lt_value q).trans hqy).le, hy.2⟩
    exact hqy.ne (congrArg f heq).symm
  have hnpos : 0 < n := by
    by_contra hnot
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hnot
    obtain ⟨x, hx⟩ := hsurj 1
    have hh := congrFun hx ⟨0, hrpos⟩
    let _ : IsEmpty (Fin n) := ⟨fun j => by have hj := j.isLt; omega⟩
    simp only [Matrix.mulVec, dotProduct, Finset.univ_eq_empty, Finset.sum_empty,
      Pi.one_apply] at hh
    exact zero_ne_one hh
  let za := γ ⟨0, hnpos⟩ (Smale.Hemisphere.point Bool.true ⟨0, by simp⟩)
  obtain ⟨β, hβ, horbit, -, hmatrix, hsurj'⟩ :=
    T.exists_lower_cut_geometric_matrix hf hba (S.data q).upper_regular (T.data q).upper_regular
      hband za p (fun j => (hlower j).trans (T.toSurgeryWindows.lower_lt_value (p j))) B γ hγ
      hsurj
  exact
    ⟨hindex, hprimitive, hnull, hcut, hcomplete, fun j => hba.trans (hlower j), β, hβ, horbit,
      B.trans (regularCutHomologyEquiv hf hba.le hband).symm, hmatrix, hsurj'⟩

private theorem Smale.SupportedDiffeomorph.IsotopicToIdentity.homotopic {F H M : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞}
    (he : Smale.SupportedDiffeomorph.IsotopicToIdentity e) :
    (ContinuousMap.id M).Homotopic e.toHomeomorph.toHomotopyEquiv.toFun := by
  obtain ⟨A, hA, hA₀, hA₁, _⟩ := he
  exact
    ⟨{  toFun := fun p => A (p.1.val, p.2)
        continuous_toFun :=
          hA.continuous.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        map_zero_left := hA₀
        map_one_left := hA₁ }⟩

private theorem Smale.SupportedDiffeomorph.IsotopicToIdentity.comp_homotopic {F H M : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] {e : Diffeomorph J J M M ∞} {X : Type*}
    [TopologicalSpace X] (he : Smale.SupportedDiffeomorph.IsotopicToIdentity e) (g : C(X, M)) :
    g.Homotopic (e.toHomeomorph.toHomotopyEquiv.toFun.comp g) := by
  simpa using he.homotopic.comp (ContinuousMap.Homotopic.refl g)

private theorem Smale.ManifoldMorse.MorseSurgeryData.exists_transverse_representative {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (g₀ : C(Smale.Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg₀ : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g₀)
      (_hinj : Function.Injective g₀)
      (_himm : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g₀ x)),
      ∃ e :
        Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E) d.UpperLevel
          d.UpperLevel ∞,
        ∃ g : C(Smale.Hemisphere.Sphere 2, d.UpperLevel),
          Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
            (∀ x, g x = e (g₀ x)) ∧ d.IsTransverseBeltSphere hf hdim hindex g ∧ g₀.Homotopic g := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ := Smale.RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have h := d.chart.finrank_negative_add_positive; omega⟩
  intro hg₀ hinj himm
  have hdim' :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) + Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
      Module.finrank ℝ (Smale.RegularLevel.Model E) := by simp [Smale.RegularLevel.Model, hdim]
  obtain ⟨e, hiso, ht⟩ :=
    Smale.NativeTransversality.exists_ambient_transverse_diffeomorph hg₀ (d.belt_smooth hf 3)
      hdim'
  let g := e.toHomeomorph.toHomotopyEquiv.toFun.comp g₀
  have hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g := e.contMDiff.comp hg₀
  have hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g x) := by
    intro x
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (e ∘ g₀) x)
    rw [mfderiv_comp x (e.mdifferentiable (by simp) _) (hg₀.mdifferentiable (by simp) x)]
    exact
      ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective (by trivial)).comp
        (himm x)
  exact ⟨e, g, hiso, fun _ => rfl, ⟨hg, e.injective.comp hinj, hi, ht⟩, hiso.comp_homotopic g₀⟩

private theorem MorseCancel.exists_single_intersection_of_unit_coordinate {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Smale.Hemisphere.Sphere 1, d.LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (γ : C((Smale.Hemisphere.Sphere 2), d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_ : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ) (_ : Function.Injective γ)
      (_ : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) γ x)),
      (d.indexTwoCollapseCoordinate hf.continuous hindex
              (middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ)).natAbs =
          1 →
        ∃ D :
          Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
            d.UpperLevel d.UpperLevel ∞,
          ∃ δ : C((Smale.Hemisphere.Sphere 2), d.UpperLevel),
            Smale.SupportedDiffeomorph.IsotopicToIdentity D ∧
              (∀ x, δ x = D (γ x)) ∧
                d.IsTransverseBeltSphere hf hdim hindex δ ∧
                  (Set.range δ ∩ Set.range d.surgery.beltSphere).ncard = 1 := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  intro hγ hinj himm hunit
  obtain ⟨D₀, γ₀, hD₀, hγ₀, hgood₀, hhom⟩ :=
    d.exists_transverse_representative hf hdim hindex γ hγ hinj himm
  have hmaps := PeriodTorusHigherHomology.homotopic_homologyMap hhom 2
  have hclass :
    middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ₀ =
      middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ := by
    simp only [middleSectionClass, PeriodTorusHigherHomology.singularHomologyMap_comp,
      LinearMap.comp_apply]
    rw [← hmaps]
  have hcount :
    (d.beltIntersectionCount 2 (d.beltNormalReference 2 hindex) γ₀
          (d.finite_points_of_isTransverseBeltSphere hf hdim hindex hgood₀)).natAbs =
      1 := by
    rw [←
      d.indexTwoCoordinate_transverse_natAbs hf hdim hindex (d.beltNormalReference 2 hindex) γ₀
        hgood₀]
    change
      (d.indexTwoCollapseCoordinate hf.continuous hindex
            (middleSectionClass (f := f) (a := f p + d.radius ^ 2) γ₀)).natAbs =
        1
    rw [hclass]
    exact hunit
  obtain ⟨D₁, δ, x, hD₁, hδ, hgood, -, hinter⟩ :=
    d.exists_single_belt_intersection_of_unit_count hf hdim hindex hnull
      (d.beltNormalReference 2 hindex) γ₀ hgood₀ hcount
  refine ⟨D₀.trans D₁, δ, hD₀.trans hD₁, (fun x => (hδ x).trans (congrArg D₁ (hγ₀ x))), hgood, ?_⟩
  rw [hinter, Set.ncard_singleton]

private theorem
    AdaptedWindows.cancel_single_basin_section_isotopy {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {Y : Type}
    [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y] (S : AdaptedWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : Smale.ManifoldMorse.IsMorse E f)
    (hdim : Module.finrank ℝ E = 6) (p q : Smale.ManifoldMorse.criticalPoints E f)
    (hconsecutive : ∀ r : Smale.ManifoldMorse.criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hp : MorseCancel.nativeMorseIndex E f p = 2) (hq : MorseCancel.nativeMorseIndex E f q = 3)
    {c : ℝ} (hpc : f p < c) (hcq : c < f q)
    (hc : ∀ z, f z = c → z ∉ Smale.ManifoldMorse.criticalPoints E f) :
    letI := Smale.RegularLevel.chartedSpace hf hc
    ∀ (α : Smale.Hemisphere.Sphere 2 → { z : M // f z = c }) (β : Y → { z : M // f z = c }),
      ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α →
        ContMDiff (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ β →
          (∀ z,
              z ∈ Set.range α ↔ Filter.Tendsto (fun t => S.flow t z.val) Filter.atBot (𝓝 q.val)) →
            (∀ z,
                z ∈ Set.range β ↔
                  Filter.Tendsto (fun t => S.flow t z.val) Filter.atTop (𝓝 p.val)) →
              ∀ D :
                Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
                  { z : M // f z = c } { z : M // f z = c } ∞,
                Smale.SupportedDiffeomorph.IsotopicToIdentity D →
                  (∀ x y,
                      Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E)
                        (D ∘ α) β x y) →
                    (Set.range (D ∘ α) ∩ Set.range β).ncard = 1 →
                      ∃ g : M → ℝ,
                        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧
                          Smale.ManifoldMorse.IsMorse E g ∧
                            (Smale.ManifoldMorse.criticalPoints E g).ncard + 2 =
                                (Smale.ManifoldMorse.criticalPoints E f).ncard ∧
                              (∀ z,
                                  z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
                                    z ∈ Smale.ManifoldMorse.criticalPoints E f ∧
                                      z ≠ p.val ∧ z ≠ q.val) ∧
                                ∀ z,
                                  f z ∉
                                      Set.Ioo (S.toSurgeryWindows.lower p)
                                        (S.toSurgeryWindows.upper q) →
                                    g =ᶠ[𝓝 z] f := by
  let _ := Smale.RegularLevel.chartedSpace hf hc
  intro α β hα hβ hback hforward D hD htrans hsingle
  let δ := D.symm ∘ β
  have hδ : ContMDiff (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ δ := D.symm.contMDiff.comp hβ
  have hDα : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (D ∘ α) := D.contMDiff.comp hα
  have hαeq : D.symm ∘ (D ∘ α) = α := by
    funext x
    exact D.symm_apply_apply (α x)
  have hrange (z : { w : M // f w = c }) : z ∈ Set.range α ↔ D z ∈ Set.range (D ∘ α) := by
    constructor
    · rintro ⟨x, rfl⟩
      exact Set.mem_range_self x
    · rintro ⟨x, hx⟩
      exact ⟨x, D.injective hx⟩
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hsingle
  have hzmem : z ∈ Set.range (D ∘ α) ∩ Set.range β := by
    rw [hz]
    exact Set.mem_singleton z
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hzmem
  have hcross : β y = (D ∘ α) x := hy.trans hx.symm
  have hcross' : δ y = α x := by exact (congrArg D.symm hcross).trans (D.symm_apply_apply (α x))
  have ht : Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) α δ x y := by
    have hh :=
      (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff
            D.symm.toPartialDiffeomorph (hDα.mdifferentiableAt (by simp))
            (hβ.mdifferentiableAt (by simp)) hcross (Set.mem_univ _)).mp
        (htrans x y)
    change
      Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E)
        (D.symm ∘ (D ∘ α)) δ x y at hh
    rwa [hαeq] at hh
  have hcount :
    {w : { z : M // f z = c } |
          Filter.Tendsto (fun t => S.flow t w.val) Filter.atBot (𝓝 q.val) ∧
            Filter.Tendsto (fun t => S.flow t (D w).val) Filter.atTop (𝓝 p.val)}.ncard =
      1 := by
    have heq :
      {w : { z : M // f z = c } |
          Filter.Tendsto (fun t => S.flow t w.val) Filter.atBot (𝓝 q.val) ∧
            Filter.Tendsto (fun t => S.flow t (D w).val) Filter.atTop (𝓝 p.val)} =
        {D.symm z} := by
      ext w
      change (_ ∧ _) ↔ w = D.symm z
      rw [← hback w, ← hforward (D w), hrange w]
      change D w ∈ Set.range (D ∘ α) ∩ Set.range β ↔ w = D.symm z
      rw [hz, Set.mem_singleton_iff]
      exact
        ⟨fun h => (D.symm_apply_apply w).symm.trans (congrArg D.symm h), fun h =>
          (congrArg D h).trans (D.apply_symm_apply z)⟩
    rw [heq, Set.ncard_singleton]
  have hαbasin :
    ∀ᶠ w in 𝓝 x, Filter.Tendsto (fun t => S.flow t (α w).val) Filter.atBot (𝓝 q.val) :=
    Filter.Eventually.of_forall (fun w => (hback (α w)).mp (Set.mem_range_self w))
  have hδbasin :
    ∀ᶠ w in 𝓝 y, Filter.Tendsto (fun t => S.flow t (D (δ w)).val) Filter.atTop (𝓝 p.val) := by
    apply Filter.Eventually.of_forall
    intro w
    change Filter.Tendsto (fun t => S.flow t (D (D.symm (β w))).val) Filter.atTop (𝓝 p.val)
    rw [D.apply_symm_apply]
    exact (hforward (β w)).mp (Set.mem_range_self w)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b, hcb, hbq⟩ := exists_between hcq
  have hweightp : Fintype.card { i // (S.data p).chart.weights i = -1 } = 2 := by
    have hh := (MorseCancel.nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp
    simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using hh
  have hweightq : Fintype.card { i // (S.data q).chart.weights i = -1 } = 3 := by
    have hh := (MorseCancel.nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
    simpa only [Smale.ManifoldMorse.SignedMorseChart.NegativeCoordinates,
      Smale.MorseHandle.NegativeSpace, finrank_euclideanSpace] using hh
  exact
    MorseCancel.cancel_of_transverse_level_isotopy (m := 5) (S.data p).chart (S.data q).chart hf
      hm hdim (by omega) S.field S.smooth S.zero S.descent S.flow S.integral S.distinct p.property
      q.property (S.toSurgeryWindows.lower_lt_value p) (S.toSurgeryWindows.value_lt_upper q)
      (MorseCancel.surgery_pair_band_isolation S.toSurgeryWindows p q hconsecutive) hac hcb hpc
      hcq (MorseCancel.surgery_pair_inner_band_regular p q hconsecutive hpa hbq) hc
      (S.critical_model_germ p) (S.critical_model_germ q) D hD hcount α δ x y
      (hα.mdifferentiableAt (by simp)) (hδ.mdifferentiableAt (by simp)) hcross' ht hαbasin hδbasin

private theorem MorseCancel.conjugate_level_isotopy {V H X Y : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [TopologicalSpace H] {J : ModelWithCorners ℝ V H} [TopologicalSpace X]
    [ChartedSpace H X] [TopologicalSpace Y] [ChartedSpace H Y] (e : Diffeomorph J J X Y ∞)
    (D : Diffeomorph J J X X ∞) (hD : Smale.SupportedDiffeomorph.IsotopicToIdentity D) :
    Smale.SupportedDiffeomorph.IsotopicToIdentity (e.symm.trans (D.trans e)) := by
  obtain ⟨A, hA, hzero, hone, hslices⟩ := hD
  refine
    ⟨fun z : ℝ × Y => e (A (z.1, e.symm z.2)),
      e.contMDiff.comp (hA.comp (contMDiff_fst.prodMk (e.symm.contMDiff.comp contMDiff_snd))), ?_,
      ?_, ?_⟩
  · intro y
    change e (A (0, e.symm y)) = y
    rw [hzero, e.apply_symm_apply]
  · intro y
    change e (A (1, e.symm y)) = e (D (e.symm y))
    rw [hone]
  · intro t
    obtain ⟨Dt, hDt⟩ := hslices t
    refine ⟨e.symm.trans (Dt.trans e), ?_⟩
    intro y
    change e (A (t, e.symm y)) = e (Dt (e.symm y))
    rw [hDt]

private theorem MorseCancel.intersection_count_under_injective_map {A B X Y : Type*} (e : X → Y)
    (he : Function.Injective e) (α : A → X) (β : B → X) :
    (Set.range (e ∘ α) ∩ Set.range (e ∘ β)).ncard = (Set.range α ∩ Set.range β).ncard := by
  have hset : Set.range (e ∘ α) ∩ Set.range (e ∘ β) = e '' (Set.range α ∩ Set.range β) := by
    ext y
    constructor
    · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
      have hab : α a = β b := he (ha.trans hb.symm)
      exact ⟨α a, ⟨Set.mem_range_self a, ⟨b, hab.symm⟩⟩, ha⟩
    · rintro ⟨x, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hx⟩
      exact ⟨⟨a, (congrArg e ha).trans hx⟩, ⟨b, (congrArg e hb).trans hx⟩⟩
  rw [hset]
  exact Set.ncard_image_of_injective _ he

private theorem MorseCancel.cancel_from_preserved_unit_belt_cut {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f g : M → ℝ} (S : AdaptedWindows E f)
    (T : AdaptedWindows E g) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g) (hmg : Smale.ManifoldMorse.IsMorse E g)
    (hdim : Module.finrank ℝ E = 6) (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hpcg : p.val ∈ Smale.ManifoldMorse.criticalPoints E g) (hpg : nativeMorseIndex E g p = 2)
    (q : Smale.ManifoldMorse.criticalPoints E g) (hq : nativeMorseIndex E g q = 3)
    (hconsecutive : ∀ z : Smale.ManifoldMorse.criticalPoints E g, ¬(g p < g z ∧ g z < g q))
    (hpc : g p < (f p + (S.data p).radius ^ 2)) (hcq : (f p + (S.data p).radius ^ 2) < g q)
    (hsub : ∀ y, g y ≤ (f p + (S.data p).radius ^ 2) ↔ f y ≤ (f p + (S.data p).radius ^ 2))
    (hlevel : ∀ y, g y = (f p + (S.data p).radius ^ 2) ↔ f y = (f p + (S.data p).radius ^ 2))
    (hga : ∀ y, g y = (f p + (S.data p).radius ^ 2) → y ∉ Smale.ManifoldMorse.criticalPoints E g)
    (hforward :
      ∀ y : (S.data p).UpperLevel,
        Filter.Tendsto (fun t => T.flow t y.val) Filter.atTop (𝓝 p.val) ↔
          Filter.Tendsto (fun t => S.flow t y.val) Filter.atTop (𝓝 p.val))
    (γ : C((Smale.Hemisphere.Sphere 2), { y : M // g y = (f p + (S.data p).radius ^ 2) })) :
    letI := Smale.RegularLevel.chartedSpace hg hga
    ∀ (_ : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ γ) (_ : Function.Injective γ)
      (_ : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) γ x)),
      (∀ y, y ∈ Set.range γ ↔ Filter.Tendsto (fun t => T.flow t y.val) Filter.atBot (𝓝 q.val)) →
        ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex
                ((equalCutHomologyEquiv hsub).symm (middleSectionClass γ))).natAbs =
            1 →
          ∃ v : M → ℝ,
            ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧
              Smale.ManifoldMorse.IsMorse E v ∧
                (Smale.ManifoldMorse.criticalPoints E v).ncard + 2 =
                    (Smale.ManifoldMorse.criticalPoints E g).ncard ∧
                  (∀ z,
                      z ∈ Smale.ManifoldMorse.criticalPoints E v ↔
                        z ∈ Smale.ManifoldMorse.criticalPoints E g ∧ z ≠ p.val ∧ z ≠ q.val) ∧
                    ∀ z,
                      g z ∉
                          Set.Ioo (T.toSurgeryWindows.lower ⟨p.val, hpcg⟩)
                            (T.toSurgeryWindows.upper q) →
                        v =ᶠ[𝓝 z] g := by
  let _ := Smale.RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := Smale.RegularLevel.chartedSpace hg hga
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := (S.data p).chart.finrank_negative_add_positive; omega⟩
  intro hγ hinj himm hback hunit
  let e := equalLevelDiffeomorph hf hg (S.data p).upper_regular hga hlevel
  let α : C((Smale.Hemisphere.Sphere 2), (S.data p).UpperLevel) :=
    equalCutSection (fun y => (hlevel y).symm) γ
  have hα : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ α := by
    change ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ (e.symm ∘ γ)
    exact e.symm.contMDiff.comp hγ
  have hαinj : Function.Injective α := e.symm.injective.comp hinj
  have hαimm (x : (Smale.Hemisphere.Sphere 2)) :
    Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) α x) := by
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (e.symm ∘ γ) x)
    rw [mfderiv_comp x (e.symm.contMDiff.mdifferentiableAt (by simp))
        (hγ.mdifferentiableAt (by simp))]
    exact (e.symm.mfderivToContinuousLinearEquiv (by simp) (γ x)).injective.comp (himm x)
  have hsection : equalCutSection hlevel α = γ := rfl
  have hclass := equalCutSection_class hsub hlevel α
  rw [hsection] at hclass
  have hpull : (equalCutHomologyEquiv hsub).symm (middleSectionClass γ) = middleSectionClass α := by
    rw [← hclass, LinearEquiv.symm_apply_apply]
  have hαunit :
    ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex (middleSectionClass α)).natAbs =
      1 := by rwa [hpull] at hunit
  obtain ⟨D, δ, hD, hδ, hgood, hsingle⟩ :=
    exists_single_intersection_of_unit_coordinate (S.data p) hf hdim hindex hnull α hα hαinj hαimm
      hαunit
  let β₀ := (S.data p).surgery.beltSphere
  let β := e ∘ β₀
  have hβ₀ : ContMDiff (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ β₀ := (S.data p).belt_smooth hf 3
  have hβ : ContMDiff (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ β := e.contMDiff.comp hβ₀
  let D' := e.symm.trans (D.trans e)
  have hD' : Smale.SupportedDiffeomorph.IsotopicToIdentity D' := conjugate_level_isotopy e D hD
  have hDγ : D' ∘ γ = e ∘ δ := by
    funext x
    change e (D (α x)) = e (δ x)
    exact congrArg e (hδ x).symm
  have hβfull (y : { z : M // g z = (f p + (S.data p).radius ^ 2) }) :
    y ∈ Set.range β ↔ Filter.Tendsto (fun t => T.flow t y.val) Filter.atTop (𝓝 p.val) := by
    have hmem : y ∈ Set.range β ↔ e.symm y ∈ Set.range β₀ := by
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, e.injective (hx.trans (e.apply_symm_apply y).symm)⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, (congrArg e hx).trans (e.apply_symm_apply y)⟩
    rw [hmem]
    exact (S.belt_basin_iff hf p (e.symm y)).symm.trans (hforward (e.symm y)).symm
  have ht :
    ∀ x y,
      Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) (D' ∘ γ) β x y :=
    by
    rw [hDγ]
    intro x y hxy
    have hold : β₀ y = δ x := e.injective hxy
    have hh :=
      (Degree.TransverseGerms.native_transversality_partial_diffeomorph_iff e.toPartialDiffeomorph
            (hgood.1.mdifferentiableAt (by simp)) (hβ₀.mdifferentiableAt (by simp)) hold
            (Set.mem_univ _)).mp
        (hgood.2.2.2 x y)
    exact hh hxy
  have hcount : (Set.range (D' ∘ γ) ∩ Set.range β).ncard = 1 := by
    rw [hDγ]
    exact (intersection_count_under_injective_map e e.injective δ β₀).trans hsingle
  exact
    T.cancel_single_basin_section_isotopy hg hmg hdim ⟨p.val, hpcg⟩ q hconsecutive hpg hq hpc hcq
      hga γ β hγ hβ hback hβfull D' hD' ht hcount

private theorem MorseCancel.consecutive_last_two_first_three {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {f g : M → ℝ} (S : Smale.ManifoldMorse.SurgeryWindows E f)
    (p : Smale.ManifoldMorse.criticalPoints E f) (hp : nativeMorseIndex E f p = 2)
    (hcrit : Smale.ManifoldMorse.criticalPoints E g = Smale.ManifoldMorse.criticalPoints E f)
    (hindices :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E g z = nativeMorseIndex E f z)
    (hfixed :
      ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z ≠ 3 → g z = f z)
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z < 3 → f z < S.upper p)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E g,
        g x < g y → nativeMorseIndex E g x ≤ nativeMorseIndex E g y)
    (q : Smale.ManifoldMorse.criticalPoints E g) (hq : nativeMorseIndex E g q = 3)
    (hfirst :
      ∀ z : Smale.ManifoldMorse.criticalPoints E g,
        nativeMorseIndex E g z = 3 → z ≠ q → g q < g z) :
    ∀ z : Smale.ManifoldMorse.criticalPoints E g, ¬(g p < g z ∧ g z < g q) := by
  let pg : Smale.ManifoldMorse.criticalPoints E g := ⟨p.val, hcrit.symm ▸ p.property⟩
  have hpg : nativeMorseIndex E g pg = 2 := (hindices p p.property).trans hp
  have hgp : g p = f p := hfixed p p.property (by omega)
  intro z hz
  have hle : nativeMorseIndex E g z ≤ 3 := (horder z q hz.2).trans_eq hq
  have hge : 2 ≤ nativeMorseIndex E g z := hpg.symm.trans_le (horder pg z hz.1)
  have hcases : nativeMorseIndex E g z = 2 ∨ nativeMorseIndex E g z = 3 := by omega
  rcases hcases with hi2 | hi3
  · let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit ▸ z.property⟩
    have hfidx : nativeMorseIndex E f zf = 2 := (hindices z zf.property).symm.trans hi2
    have hgz : g z = f z := hfixed z zf.property (by change nativeMorseIndex E f zf ≠ 3; omega)
    have hvalue : f p < f z := by
      have hh := hz.1
      rwa [hgp, hgz] at hh
    have hupper : f z < S.upper p := hcut zf (by omega)
    have heq : z.val = p.val :=
      S.isolated p z zf.property ⟨((S.lower_lt_value p).trans hvalue).le, hupper.le⟩
    exact hvalue.ne (congrArg f heq).symm
  · have hne : z ≠ q := fun heq =>
      hz.2.ne (congrArg (fun x : Smale.ManifoldMorse.criticalPoints E g => g x) heq)
    exact (hfirst z hi3 hne).not_gt hz.2

attribute [local irreducible] MorseCancel.canonicalMiddleMatrix in
private theorem MorseCancel.cancel_from_complete_middle_family {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (p : Smale.ManifoldMorse.criticalPoints E f)
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hnull :
      ∀ δ : C(Smale.Hemisphere.Sphere 1, (S.data p).LowerLevel),
        ∃ z, δ.Homotopic (ContinuousMap.const _ z))
    (hprimitive :
      Function.Surjective ((S.data p).indexTwoCollapseCoordinate hf.continuous hindex))
    (hcut :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z < 3 → f z < f p + (S.data p).radius ^ 2)
    {r n : ℕ} (labels : Fin n → Smale.ManifoldMorse.criticalPoints E f)
    (hlabels : ∀ j, nativeMorseIndex E f (labels j) = 3)
    (hcomplete :
      ∀ z : Smale.ManifoldMorse.criticalPoints E f,
        nativeMorseIndex E f z = 3 → ∃ j, labels j = z)
    (hlower : ∀ j, f p + (S.data p).radius ^ 2 < S.toSurgeryWindows.lower (labels j))
    (B :
      (Fin r → ℤ) ≃ₗ[ℤ]
        SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + (S.data p).radius ^ 2 } 2)
    (γ : Fin n → C((Smale.Hemisphere.Sphere 2), (S.data p).UpperLevel))
    (hγ : IsNativeMiddleBasinFamily S hf (S.data p).upper_regular labels (fun j => γ j))
    (hsurj : Function.Surjective (canonicalMiddleMatrix B γ).mulVec) :
    ∃ v : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v ∧
        Smale.ManifoldMorse.IsMorse E v ∧
          Set.InjOn v (Smale.ManifoldMorse.criticalPoints E v) ∧
            (Smale.ManifoldMorse.criticalPoints E v).ncard + 2 =
              (Smale.ManifoldMorse.criticalPoints E f).ncard := by
  let c := f p + (S.data p).radius ^ 2
  let L := (S.data p).indexTwoCollapseCoordinate hf.continuous hindex
  have hpold : nativeMorseIndex E f p = 2 :=
    (nativeMorseIndex_eq_chart (S.data p).chart).trans hindex
  obtain
    ⟨ops, -, g, hg, hmg, hcrit, hgorder, hindices, -, houtside, hgcut, hsub, hlevel, hga, T, -, -,
      hpg, hgcomplete, hglower, Γ, hΓ, -, -, hgsurj, ⟨i, hi⟩, hkeep⟩ :=
    S.exists_primitive_functional_unit hf hm hdim horder (S.data p).upper_regular hcut labels
      hlabels hcomplete hlower B γ hγ hsurj L hprimitive
  let pg : Fin n → Smale.ManifoldMorse.criticalPoints E g := fun j =>
    ⟨(labels j).val, hcrit.symm ▸ (labels j).property⟩
  let Bg := B.trans (equalCutHomologyEquiv hsub)
  obtain
    ⟨u, hu, hmu, hcu, huorder, huindices, -, huoutside, hfirst, husub, hulevel, hua, U, -, huflow,
      -, hpu, hulower, hfamily, -, -, -⟩ :=
    T.exists_first_middle_pivot hg hmg hga hgorder pg hpg hgcomplete hglower Bg Γ hΓ hgsurj i
  let hcrit' := hcu.trans hcrit
  let hsub' : ∀ y, u y ≤ c ↔ f y ≤ c := fun y => (husub y).trans (hsub y)
  let hlevel' : ∀ y, u y = c ↔ f y = c := fun y => (hulevel y).trans (hlevel y)
  let q : Smale.ManifoldMorse.criticalPoints E u :=
    ⟨(labels i).val, hcrit'.symm ▸ (labels i).property⟩
  let Δ := fun j => equalCutSection hulevel (Γ j)
  have hids (z : M) (hz : z ∈ Smale.ManifoldMorse.criticalPoints E f) :
    nativeMorseIndex E u z = nativeMorseIndex E f z :=
    (huindices z (hcrit.symm ▸ hz)).trans (hindices z hz)
  have hfixed (z : M) (hz : z ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hidx : nativeMorseIndex E f z ≠ 3) : u z = f z := by
    have hnotlabel (j : Fin n) : z ≠ (labels j).val := by
      intro heq
      apply hidx
      rw [heq]
      exact hlabels j
    exact (huoutside z (hcrit.symm ▸ hz) hnotlabel).trans (houtside z hz hnotlabel)
  have hpcrit : p.val ∈ Smale.ManifoldMorse.criticalPoints E u := hcrit'.symm ▸ p.property
  have hpnew : nativeMorseIndex E u p = 2 := (hids p p.property).trans hpold
  have hq : nativeMorseIndex E u q = 3 := (hids (labels i) (labels i).property).trans (hlabels i)
  have hfirstcrit (z : Smale.ManifoldMorse.criticalPoints E u) (hz : nativeMorseIndex E u z = 3)
    (hne : z ≠ q) : u q < u z := by
    let zf : Smale.ManifoldMorse.criticalPoints E f := ⟨z.val, hcrit' ▸ z.property⟩
    have hzidx : nativeMorseIndex E f zf = 3 := (hids z zf.property).symm.trans hz
    obtain ⟨j, hj⟩ := hcomplete zf hzidx
    have hji : j ≠ i := by
      intro hji
      apply hne
      apply Subtype.ext
      exact
        (congrArg (fun z : Smale.ManifoldMorse.criticalPoints E f => z.val) hj).symm.trans
          (congrArg (fun k => (labels k).val) hji)
    have hh := hfirst j hji
    change u (labels i) < u (labels j) at hh
    simpa only [hj] using hh
  have hconsecutive :=
    consecutive_last_two_first_three S.toSurgeryWindows p hpold hcrit' hids hfixed hcut huorder q
      hq hfirstcrit
  have hpc : u p < c := by
    rw [hfixed p p.property (by omega)]
    exact S.toSurgeryWindows.value_lt_upper p
  have hcq : c < u q := (hulower i).trans (U.toSurgeryWindows.lower_lt_value q)
  have hclass := equalCutSection_class husub hulevel (Γ i)
  have hpull :
    (equalCutHomologyEquiv hsub').symm (middleSectionClass (Δ i)) =
      (equalCutHomologyEquiv hsub).symm (middleSectionClass (Γ i)) := by
    rw [← equalCutHomologyEquiv_trans hsub husub]
    change
      (equalCutHomologyEquiv hsub).symm
          ((equalCutHomologyEquiv husub).symm (middleSectionClass (Δ i))) =
        _
    rw [← hclass, LinearEquiv.symm_apply_apply]
  have hunit : (L ((equalCutHomologyEquiv hsub').symm (middleSectionClass (Δ i)))).natAbs = 1 := by
    rw [hpull]
    rcases hi with hi | hi <;> rw [hi] <;> norm_num
  have hforward (y : (S.data p).UpperLevel) :
    Filter.Tendsto (fun t => U.flow t y.val) Filter.atTop (𝓝 p.val) ↔
      Filter.Tendsto (fun t => S.flow t y.val) Filter.atTop (𝓝 p.val) := by
    rw [huflow]
    exact (hkeep y.val y.property.le).2.2 p.val
  let _ := Smale.RegularLevel.chartedSpace hu hua
  obtain ⟨v, hv, hmv, hcard, hcv, hext⟩ :=
    cancel_from_preserved_unit_belt_cut S U hf hu hmu hdim p hindex hnull hpcrit hpnew q hq
      hconsecutive hpc hcq hsub' hlevel' hua hforward (Δ i) (hfamily.1 i)
      (hfamily.2.1 i).injective (hfamily.2.2.1 i) (hfamily.2.2.2.2 i) hunit
  obtain ⟨-, hinj, -⟩ :=
    adapted_surgeries_after_pair_removal U.toSurgeryWindows ⟨p.val, hpcrit⟩ q hconsecutive hv hmv
      hcv hext
  refine ⟨v, hv, hmv, hinj, ?_⟩
  rwa [hcrit'] at hcard

private theorem MorseCancel.minimal_ordered_index_two_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (hminimal :
      ∀ v : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v →
          Smale.ManifoldMorse.IsMorse E v →
            Set.InjOn v (Smale.ManifoldMorse.criticalPoints E v) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E v).ncard) :
    nativeMorseCount E f 2 = 0 := by
  obtain ⟨r, n, htwo, hrc, hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr, hn⟩ := native_middle_block_counts S.toSurgeryWindows hf r n htwo hrc hthree hafter
  rw [hr]
  by_contra hnot
  have hrpos : 0 < r := Nat.pos_of_ne_zero hnot
  obtain ⟨T, -, hradii, -, α, hα⟩ :=
    S.exists_ordered_middle_family hf hm hdim r n hrc hthree (fun p => (S.data p).radius)
      (fun p => (S.data p).radius_pos)
  let q := S.toSurgeryWindows.point ⟨r, by omega⟩
  let a := S.toSurgeryWindows.upper q
  let p := nativeMiddleBlockPoint S r n hrc
  have hp (j : Fin n) : nativeMorseIndex E f (p j) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hthree ⟨r + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  have hlower (j : Fin n) : a < T.toSurgeryWindows.lower (p j) := by
    have hqj : f q < f (p j) :=
      S.toSurgeryWindows.point_strictMono (by change r < r + j.val + 1; omega)
    have hsep := S.separated q (p j) hqj
    have hh :=
      mul_pos (sub_pos.mpr (hradii (p j)))
        (add_pos (S.data (p j)).radius_pos (T.data (p j)).radius_pos)
    change a < f (p j) - (T.data (p j)).radius ^ 2
    change a < f (p j) - (S.data (p j)).radius ^ 2 at hsep
    nlinarith
  obtain ⟨β, hβ, -, hβflow⟩ :=
    T.exists_canonical_middle_family hf (S.data q).upper_regular p hp α hα
  let _ := Smale.RegularLevel.chartedSpace hf (S.data q).upper_regular
  let γ : Fin n → C((Smale.Hemisphere.Sphere 2), { y : M // f y = a }) := fun j =>
    ⟨β j, (hβ.1 j).continuous⟩
  let B := S.toSurgeryWindows.indexTwoBasis hf r (by omega) htwo
  have hsurj :=
    canonical_middle_matrix_surjective S T hf hdim e horder hzero hone r n hr hn hrc hp hlower B γ
      hβflow
  obtain ⟨hindex, hprimitive, hnull, hcut, hcomplete, hbelow, δ, hδ, -, B', -, hsurj'⟩ :=
    exists_native_belt_cut_family S T hf hdim horder hzero hone r n hr hn hrpos hrc hradii hlower
      B γ hβ hsurj
  obtain ⟨v, hv, hmv, hinj, hcard⟩ :=
    cancel_from_complete_middle_family T hf hm hdim horder q hindex hnull hprimitive hcut p hp
      hcomplete hbelow B' δ hδ hsurj'
  have hmin := hminimal v hv hmv hinj
  omega

private theorem
    MorseCancel.minimal_ordered_index_four_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] [PathConnectedSpace M]
    {f : M → ℝ} (S : AdaptedWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : Smale.ManifoldMorse.IsMorse E f) (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hsix : nativeMorseCount E f 6 = 1) (hfive : nativeMorseCount E f 5 = 0)
    (hminimal :
      ∀ v : M → ℝ,
        ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ v →
          Smale.ManifoldMorse.IsMorse E v →
            Set.InjOn v (Smale.ManifoldMorse.criticalPoints E v) →
              (Smale.ManifoldMorse.criticalPoints E f).ncard ≤
                (Smale.ManifoldMorse.criticalPoints E v).ncard) :
    nativeMorseCount E f 4 = 0 := by
  obtain ⟨T⟩ :=
    nonempty_adaptedSurgeryWindows hf.neg (isMorse_neg hm)
      (distinct_critical_values_neg S.distinct)
  have horderN :
    ∀ p q : Smale.ManifoldMorse.criticalPoints E (fun x => -f x),
      -f p < -f q → nativeMorseIndex E (fun x => -f x) p ≤ nativeMorseIndex E (fun x => -f x) q :=
    by
    intro p q hpq
    let pf : Smale.ManifoldMorse.criticalPoints E f :=
      ⟨p.val, by simpa only [Smale.ManifoldMorse.criticalPoints_neg] using p.property⟩
    let qf : Smale.ManifoldMorse.criticalPoints E f :=
      ⟨q.val, by simpa only [Smale.ManifoldMorse.criticalPoints_neg] using q.property⟩
    have hrev := horder qf pf (neg_lt_neg_iff.mp hpq)
    have hp := nativeMorseIndex_neg_add (S.data pf).chart
    have hq := nativeMorseIndex_neg_add (S.data qf).chart
    change nativeMorseIndex E f q.val ≤ nativeMorseIndex E f p.val at hrev
    change nativeMorseIndex E (fun x => -f x) p.val + nativeMorseIndex E f p.val = _ at hp
    change nativeMorseIndex E (fun x => -f x) q.val + nativeMorseIndex E f q.val = _ at hq
    omega
  have hn6 := nativeMorseCount_neg hf hm (k := 6) (by omega)
  have hn5 := nativeMorseCount_neg hf hm (k := 5) (by omega)
  have hn4 := nativeMorseCount_neg hf hm (k := 4) (by omega)
  simp only [hdim, Nat.reduceSub] at hn6 hn5 hn4
  have hh :=
    minimal_ordered_index_two_count_zero T hf.neg (isMorse_neg hm) hdim e horderN (hn6.trans hsix)
      (hn5.trans hfive) (minimal_excellent_morse_neg hminimal)
  rwa [hn4] at hh

private theorem
    Smale.ManifoldMorse.MorseSurgeryData.coreBoundary_two_injective_of_upper {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 3)]
    (hf : Continuous f) : Function.Injective (d.coreBoundaryHomologyMap 2) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← d.morse_exact_at_attachingSphere hf 2 (by norm_num)]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  change d.morseConnectingMap hf 2 a = 0
  rw [Subsingleton.elim a 0, map_zero]

private theorem Smale.ManifoldMorse.MorseSurgeryData.indexThreeAttaching_zsmul_eq_zero {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 3)]
    (hf : Continuous f) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3) (z : ℤ)
    (hz : z • d.indexThreeAttachingClass hindex = 0) : z = 0 := by
  have hcore : d.coreBoundaryHomologyMap 2 (z • (d.indexThreeBoundaryEquiv hindex).symm 1) = 0 := by
    rw [map_zsmul]
    exact hz
  have hs : z • (d.indexThreeBoundaryEquiv hindex).symm 1 = 0 :=
    d.coreBoundary_two_injective_of_upper hf (hcore.trans (map_zero _).symm)
  have h := congrArg (d.indexThreeBoundaryEquiv hindex) hs
  rw [map_zsmul, LinearEquiv.apply_symm_apply, map_zero, zsmul_eq_mul, mul_one] at h
  simpa using h

private theorem Smale.IntegerPresentation.ofEquiv_matrix_injective {B : Type*} [AddCommGroup B]
    [Module ℤ B] {r : ℕ} (e : (Fin r → ℤ) ≃ₗ[ℤ] B) :
    Function.Injective (ofEquiv e).matrix.mulVec := fun _ _ _ => Subsingleton.elim _ _

private theorem
    Smale.IntegerPresentation.adjoin_mulVec {B C : Type*} [AddCommGroup B] [AddCommGroup C]
    [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : Smale.IntegerPresentation B r c) (q : B →ₗ[ℤ] C)
    (hq : Function.Surjective q) (b : B) (hker : LinearMap.ker q = Submodule.span ℤ { b })
    (z : Fin (c + 1) → ℤ) :
    (P.adjoin q hq b hker).matrix.mulVec z =
      z 0 • P.liftRelation b + P.matrix.mulVec (Fin.tail z) := by
  rw [← (P.adjoin q hq b hker).columns_sum_eq_mulVec, Fin.sum_univ_succ]
  change z 0 • P.liftRelation b + (∑ i, z i.succ • P.columns i) = _
  rw [P.columns_sum_eq_mulVec]
  rfl

private theorem Smale.IntegerPresentation.adjoin_coefficient {B C : Type*} [AddCommGroup B]
    [AddCommGroup C] [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : Smale.IntegerPresentation B r c)
    (q : B →ₗ[ℤ] C) (hq : Function.Surjective q) (b : B)
    (hker : LinearMap.ker q = Submodule.span ℤ { b }) (z : Fin (c + 1) → ℤ) :
    P.map ((P.adjoin q hq b hker).matrix.mulVec z) = z 0 • b := by
  rw [P.adjoin_mulVec q hq b hker, map_add, map_zsmul, P.map_liftRelation, P.matrix_relation,
    add_zero]

private theorem Smale.IntegerPresentation.adjoin_matrix_injective {B C : Type*} [AddCommGroup B]
    [AddCommGroup C] [Module ℤ B] [Module ℤ C] {r c : ℕ} (P : Smale.IntegerPresentation B r c)
    (q : B →ₗ[ℤ] C) (hq : Function.Surjective q) (b : B)
    (hker : LinearMap.ker q = Submodule.span ℤ { b }) (hP : Function.Injective P.matrix.mulVec)
    (hb : ∀ z : ℤ, z • b = 0 → z = 0) : Function.Injective (P.adjoin q hq b hker).matrix.mulVec :=
  by
  have hzero (z : Fin (c + 1) → ℤ) (hz : (P.adjoin q hq b hker).matrix.mulVec z = 0) : z = 0 := by
    have hcoeff : z 0 • b = 0 :=
      (P.adjoin_coefficient q hq b hker z).symm.trans ((congrArg P.map hz).trans (map_zero P.map))
    have hz0 := hb (z 0) hcoeff
    have htail : P.matrix.mulVec (Fin.tail z) = 0 := by
      rw [P.adjoin_mulVec q hq b hker, hz0, zero_smul, zero_add] at hz
      exact hz
    have hzero' : P.matrix.mulVec (0 : Fin c → ℤ) = 0 := by simp
    have ht : Fin.tail z = 0 := hP (htail.trans hzero'.symm)
    funext i
    exact Fin.cases hz0 (fun j => congrFun ht j) i
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  rw [Matrix.mulVec_sub, hxy, sub_self]

private theorem
    Smale.ManifoldMorse.MorseSurgeryData.indexThreePresentation_matrix_injective {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {f : M → ℝ} {p : M} (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : Continuous f)
    (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 3)
    [Subsingleton
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p + d.radius ^ 2 } 3)]
    {r c : ℕ}
    (P :
      Smale.IntegerPresentation
        (SingularMayerVietoris.SingularHomology { y : M // f y ≤ f p - d.radius ^ 2 } 2) r c)
    (hP : Function.Injective P.matrix.mulVec) :
    Function.Injective (d.indexThreePresentation hf hindex P).matrix.mulVec :=
  P.adjoin_matrix_injective _ _ _ _ hP (d.indexThreeAttaching_zsmul_eq_zero hf hindex)

private theorem
    Smale.ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_upper_third {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (r : ℕ)
    (htwo : S.HasIndexTwoPrefix r) :
    ∀ (c : ℕ) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c),
      (∀ i : Fin S.count,
          r < i.val →
            i.val ≤ r + c →
              Subsingleton
                (SingularMayerVietoris.SingularHomology { x : M // f x ≤ S.upper (S.point i) }
                  3)) →
        Function.Injective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  intro c
  induction c with
  | zero =>
    intro hc hthree _
    exact Smale.IntegerPresentation.ofEquiv_matrix_injective (S.indexTwoBasis hf r hc htwo)
  | succ c ih =>
    intro hc hthree hvan
    let P :=
      S.middlePresentation hf r htwo c (Nat.lt_of_succ_lt hc)
        (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
    let B := S.consecutiveBandData hf ⟨r + c, Nat.lt_of_succ_lt hc⟩ ⟨r + (c + 1), hc⟩ rfl
    have hP : Function.Injective P.matrix.mulVec :=
      ih (Nat.lt_of_succ_lt hc) (S.indexThreeBlock_mono (Nat.le_succ c) hthree)
        (fun i hi him => hvan i hi (him.trans (Nat.le_succ (r + c))))
    let :
      Subsingleton
        (SingularMayerVietoris.SingularHomology
          { x : M //
            f x ≤
              f (S.point ⟨r + (c + 1), hc⟩) + (S.data (S.point ⟨r + (c + 1), hc⟩)).radius ^ 2 }
          3) :=
      hvan ⟨r + (c + 1), hc⟩ (by change r < r + (c + 1); omega) le_rfl
    exact
      (S.data (S.point ⟨r + (c + 1), hc⟩)).indexThreePresentation_matrix_injective hf.continuous
        (S.indexThreeBlock_last r c hc hthree) (P.transport (B.homologyEquiv 2)) hP

private theorem
    Smale.ManifoldMorse.SurgeryWindows.middleMatrix_injective_of_complete_blocks {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) :
    Function.Injective (S.middleMatrix hf r c htwo hc hthree).mulVec := by
  apply S.middleMatrix_injective_of_upper_third hf r htwo c hc hthree
  intro i hri hic
  have hi : i.val + 1 < S.count := by omega
  apply
    S.upper_homology_subsingleton_of_later_indices hf hdim hM i hi 3 (by norm_num) (by norm_num)
  intro j hij hj
  have h3 := hthree j (hri.trans hij) (by omega)
  exact ⟨by omega, by omega⟩

private theorem
    Smale.ManifoldMorse.SurgeryWindows.middleMatrix_bijective_of_complete_blocks {E M : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) :
    Function.Bijective (S.middleMatrix hf r c htwo hc hthree).mulVec :=
  ⟨S.middleMatrix_injective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount,
    S.middleMatrix_surjective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount⟩

public
theorem Smale.HomologyTransport.matrix_sizes_eq_of_bijective {R : Type*} [CommRing R]
     [StrongRankCondition R] {r c : ℕ} (A : Matrix (Fin r) (Fin c) R)
    (hA : Function.Bijective A.mulVec) : c = r := by
  let e := LinearEquiv.ofBijective A.mulVecLin hA
  simpa using e.finrank_eq

private theorem
    Smale.ManifoldMorse.SurgeryWindows.middle_counts_equal {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) (r c : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hc : r + c < S.count) (hthree : S.HasIndexThreeBlock r c)
    (hcount : r + c + 2 = S.count) : r = c :=
  (Smale.HomologyTransport.matrix_sizes_eq_of_bijective (S.middleMatrix hf r c htwo hc hthree)
      (S.middleMatrix_bijective_of_complete_blocks hf hdim hM r c htwo hc hthree hcount)).symm

private theorem MorseCancel.native_index_excluded_of_count_zero {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
        {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) {k : ℕ} (hcount : nativeMorseCount E f k = 0) :
    ∀ z ∈ Smale.ManifoldMorse.criticalPoints E f, nativeMorseIndex E f z ≠ k := by
  have hfinite :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  have hempty :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} = ∅ :=
    (Set.ncard_eq_zero hfinite).mp hcount
  intro z hz hi
  have hmem :
    z ∈ {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} :=
    ⟨hz, hi⟩
  rw [hempty] at hmem
  exact hmem

private theorem
    MorseCancel.middle_blocks_complete_of_no_four_five {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (r n : ℕ) (htwo : S.HasIndexTwoPrefix r)
    (hrc : r + n < S.count) (hthree : S.HasIndexThreeBlock r n)
    (hafter :
      ∀ i : Fin S.count,
        r + n < i.val → 4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates)
    (hsix : nativeMorseCount E f 6 = 1) (hfour : nativeMorseCount E f 4 = 0)
    (hfive : nativeMorseCount E f 5 = 0) : r + n + 2 = S.count := by
  have hpos := S.count_pos hf
  have hidx (i : Fin S.count) :
    nativeMorseIndex E f (S.point i) = 6 ↔ r + n + 1 ≤ i.val ∧ i.val < S.count := by
    have hle : nativeMorseIndex E f (S.point i) ≤ 6 := by
      simpa only [hdim] using (nativeMorseIndex_le (E := E) (f := f) (p := (S.point i).val))
    have hne4 := native_index_excluded_of_count_zero S hfour _ (S.point i).property
    have hne5 := native_index_excluded_of_count_zero S hfive _ (S.point i).property
    by_cases ha : r + n < i.val
    · have hh := hafter i ha
      rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart] at hh
      have hi := i.isLt
      omega
    · have hh : nativeMorseIndex E f (S.point i) ≤ 3 := by
        by_cases hz : i.val = 0
        · have he : i = ⟨0, hpos⟩ := Fin.ext hz
          have hzidx : nativeMorseIndex E f (S.point i) = 0 := by
            rw [he]
            exact
              (nativeMorseIndex_eq_chart (S.data (S.first hpos)).chart).trans
                (S.first_index_zero hf hpos)
          omega
        · by_cases hr : i.val ≤ r
          · rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart, htwo i (by omega) hr]
            omega
          · rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart,
              hthree i (by omega) (by omega)]
      omega
  have hcount :=
    nativeMorseCount_eq_interval_length S 6 (r + n + 1) S.count (by omega) le_rfl hidx
  omega

private theorem MorseCancel.ordered_no_middle_indices_count_two {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder :
      ∀ x y : Smale.ManifoldMorse.criticalPoints E f,
        f x < f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hone : nativeMorseCount E f 1 = 0) (htwo : nativeMorseCount E f 2 = 0)
    (hfour : nativeMorseCount E f 4 = 0) (hfive : nativeMorseCount E f 5 = 0) :
    nativeMorseCount E f 3 = 0 ∧ S.count = 2 := by
  obtain ⟨r, n, hprefix, hrc, hblock, -, hafter⟩ :=
    exists_middle_index_blocks S hf hdim horder hzero hone
  obtain ⟨hr, hn⟩ := native_middle_block_counts S hf r n hprefix hrc hblock hafter
  have hcount :=
    middle_blocks_complete_of_no_four_five S hf hdim r n hprefix hrc hblock hafter hsix hfour
      hfive
  have heq := S.middle_counts_equal hf hdim e r n hprefix hrc hblock hcount
  omega

private def Smale.negLevelHomeomorph {M : Type*} [TopologicalSpace M] (f : M → ℝ) (a : ℝ) :
    { x : M // -f x = -a } ≃ₜ { x : M // f x = a }
    where
  toFun x := ⟨x.1, neg_inj.mp x.2⟩
  invFun x := ⟨x.1, congrArg Neg.neg x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

private def
    Smale.twoDiskDecompositionOfSublevels {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ}
    {f : M → ℝ} {a : ℝ} (L : SublevelDisk n f a) (R : SublevelDisk n (fun x => -f x) (-a)) :
    TwoDiskDecomposition n M := by
  let B := L.boundaryHomeomorph
  let C := R.boundaryHomeomorph.trans (negLevelHomeomorph f a)
  let e := B.trans C.symm
  refine
    { boundaryEquiv := e
      left := L.map
      right := R.map
      left_injective := L.map_injective
      right_injective := R.map_injective
      covers := ?_
      overlap := ?_ }
  · intro y
    by_cases hy : f y ≤ a
    · left
      exact
        ⟨L.homeomorph.symm ⟨y, hy⟩, congrArg Subtype.val (L.homeomorph.apply_symm_apply ⟨y, hy⟩)⟩
    · right
      have hy' : -f y ≤ -a := neg_le_neg (le_of_not_ge hy)
      exact
        ⟨R.homeomorph.symm ⟨y, hy'⟩,
          congrArg Subtype.val (R.homeomorph.apply_symm_apply ⟨y, hy'⟩)⟩
  · intro x y
    constructor
    · intro h
      have hL : f (L.map x) ≤ a := (L.homeomorph x).2
      have hR : -f (R.map y) ≤ -a := (R.homeomorph y).2
      have hxlevel : f (L.map x) = a := by rw [← h] at hR; linarith
      have hylevel : -f (R.map y) = -a := by rw [← h, hxlevel]
      have hxnorm := (L.boundary_iff x).mp hxlevel
      have hynorm := (R.boundary_iff y).mp hylevel
      let z : DiskDouble.Boundary (Hemisphere.Ambient n) :=
        ⟨x.1, mem_sphere_zero_iff_norm.mpr hxnorm⟩
      let w : DiskDouble.Boundary (Hemisphere.Ambient n) :=
        ⟨y.1, mem_sphere_zero_iff_norm.mpr hynorm⟩
      have hbc : B z = C w := Subtype.ext h
      have hew : e z = w := by
        apply C.injective
        change C (C.symm (B z)) = C w
        rw [C.apply_symm_apply]
        exact hbc
      refine ⟨z, rfl, ?_⟩
      rw [hew]
      rfl
    · rintro ⟨z, rfl, rfl⟩
      have heq := congrArg Subtype.val (C.apply_symm_apply (B z))
      exact heq.symm

private def
    Smale.homeomorphSphereOfSublevelDisks {M : Type*} [TopologicalSpace M] [T2Space M] {n : ℕ}
    {f : M → ℝ} {a : ℝ} (L : SublevelDisk n f a) (R : SublevelDisk n (fun x => -f x) (-a)) :
    M ≃ₜ Hemisphere.Sphere n :=
  (twoDiskDecompositionOfSublevels L R).homeomorphSphere

private theorem Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f) {p q : M} (hpq : f p < f q)
    (hcrit : criticalPoints E f = { p, q }) :
    Nonempty (M ≃ₜ Smale.Hemisphere.Sphere (Module.finrank ℝ E)) := by
  have hcover : ∀ x ∈ criticalPoints E f, x = p ∨ x = q := by
    intro x hx
    rw [hcrit] at hx
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  have hp : p ∈ criticalPoints E f := by rw [hcrit]; simp
  have hq : q ∈ criticalPoints E f := by rw [hcrit]; simp
  obtain ⟨hmin, hmax⟩ := unique_extrema_of_two_critical_values hf hpq hcover
  obtain ⟨cp⟩ := nonempty_signedMorseChart hf hm p hp
  obtain ⟨cq⟩ := nonempty_signedMorseChart hf hm q hq
  let a := (f p + f q) / 2
  have hpa : f p < a := by dsimp [a]; linarith
  have haq : a < f q := by dsimp [a]; linarith
  have hregularL : ∀ x, f p < f x → f x ≤ a → x ∉ criticalPoints E f := by
    intro x hxlo hxhi hxcrit
    rcases hcover x hxcrit with h | h
    · rw [h] at hxlo
      exact lt_irrefl _ hxlo
    · rw [h] at hxhi
      exact not_le_of_gt haq hxhi
  obtain ⟨L⟩ := cp.nonempty_sublevelDisk_before_next_critical hf hmin hpa hregularL
  have hminNeg : ∀ x, -f x ≤ -f q → x = q := fun x hx => hmax x (neg_le_neg_iff.mp hx)
  have hregularR : ∀ x, -f q < -f x → -f x ≤ -a → x ∉ criticalPoints E (fun y => -f y) := by
    intro x hxlo hxhi hxcrit
    have hxcrit' : x ∈ criticalPoints E f := by
      rw [← criticalPoints_neg (E := E) f]
      exact hxcrit
    rcases hcover x hxcrit' with h | h
    · rw [h] at hxhi
      linarith
    · rw [h] at hxlo
      exact lt_irrefl _ hxlo
  obtain ⟨R⟩ :=
    cq.neg.nonempty_sublevelDisk_before_next_critical hf.neg hminNeg (neg_lt_neg haq) hregularR
  exact ⟨Smale.homeomorphSphereOfSublevelDisks L R⟩

private theorem MorseCancel.critical_pair_of_surgery_count_two {E M : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
       {f : M → ℝ}
    (S : Smale.ManifoldMorse.SurgeryWindows E f) (hcount : S.count = 2) :
    ∃ p q : M, f p < f q ∧ Smale.ManifoldMorse.criticalPoints E f = { p, q } := by
  let p := S.point ⟨0, by omega⟩
  let q := S.point ⟨1, by omega⟩
  refine ⟨p.val, q.val, S.point_strictMono (by change (0 : ℕ) < 1; omega), ?_⟩
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi⟩ := S.point.surjective ⟨z, hz⟩
    have hib := i.isLt
    have hcases : i.val = 0 ∨ i.val = 1 := by omega
    rcases hcases with hzero | hone
    · have he : i = ⟨0, by omega⟩ := Fin.ext hzero
      have hv := congrArg (fun x : Smale.ManifoldMorse.criticalPoints E f => x.val) hi
      rw [he] at hv
      exact Set.mem_insert_iff.mpr (Or.inl hv.symm)
    · have he : i = ⟨1, by omega⟩ := Fin.ext hone
      have hv := congrArg (fun x : Smale.ManifoldMorse.criticalPoints E f => x.val) hi
      rw [he] at hv
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr hv.symm))
  · intro hz
    rcases Set.mem_insert_iff.mp hz with hp | hq
    · exact hp ▸ p.property
    · exact (Set.mem_singleton_iff.mp hq) ▸ q.property

private theorem
    MorseCancel.exists_two_critical_point_morse_of_homotopySixSphere (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) :
    ∃ f : M → ℝ,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
        Smale.ManifoldMorse.IsMorse E f ∧
          ∃ p q : M, f p < f q ∧ Smale.ManifoldMorse.criticalPoints E f = { p, q } := by
  let _ := Smale.pathConnectedSpace_of_homotopySixSphere e
  obtain ⟨f, hf, hm, S, horder, hzero, hsix, hone, hfive, hminimal⟩ :=
    exists_minimal_ordered_morse_system_without_outer_indices E M e hdim
  have htwo := minimal_ordered_index_two_count_zero S hf hm hdim e horder hzero hone hminimal
  have hfour := minimal_ordered_index_four_count_zero S hf hm hdim e horder hsix hfive hminimal
  obtain ⟨-, hcount⟩ :=
    ordered_no_middle_indices_count_two S.toSurgeryWindows hf hdim e horder hzero hsix hone htwo
      hfour hfive
  exact ⟨f, hf, hm, critical_pair_of_surgery_count_two S.toSurgeryWindows hcount⟩

private theorem MorseCancel.nonempty_homeomorph_of_homotopySixSphere (E : Type) (M : Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere) : Nonempty (M ≃ₜ SixSphere) := by
  obtain ⟨f, hf, hm, p, q, hpq, hcrit⟩ :=
    exists_two_critical_point_morse_of_homotopySixSphere E M hdim e
  have hh := Smale.ManifoldMorse.nonempty_homeomorphSphere_of_two_critical_points hf hm hpq hcrit
  change Nonempty (M ≃ₜ Smale.Hemisphere.Sphere (Module.finrank ℝ E)) at hh
  rw [hdim] at hh
  exact hh

private theorem Smale.homeomorphic_sixSphere_of_homotopySixSphere (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (M : Type) [TopologicalSpace M] [T2Space M]
     [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M]
    (hdim : Module.finrank ℝ E = 6) (hM : M ≃ₕ Smale.SixSphere) :
    Nonempty (M ≃ₜ Smale.SixSphere) :=
  MorseCancel.nonempty_homeomorph_of_homotopySixSphere E M hdim hM

end Mathoverflow1973

end
