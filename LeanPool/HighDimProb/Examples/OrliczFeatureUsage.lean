/-
Copyright (c) 2026 Zhihao Guo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhihao Guo, freezed-corpse-143
-/

import LeanPool.HighDimProb.Orlicz
import LeanPool.HighDimProb.RandomVector

/-!
# Orlicz feature usage example

This examples-only file shows how the existing `Psi1Bound` and `Psi2Bound`
predicates can package feature, activation, and gradient assumptions for later
concentration theorems. It intentionally does not prove Orlicz-to-tail,
Orlicz-to-MGF, or vector concentration implications.
-/

namespace HighDimProb.Examples.OrliczFeatureUsage

open MeasureTheory

noncomputable section

/-- Coordinatewise `psi_2` feature-vector assumption with a shared scale. -/
structure CoordinatewisePsi2Feature {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (X : RandomVector Omega (n + 1)) (K : Real) : Prop where
  coordinatePsi2 : forall i : Fin (n + 1), Psi2Bound P (coord X i) K

/-- Coordinatewise `psi_1` gradient-vector assumption with a shared scale. -/
structure CoordinatewisePsi1Gradient {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (G : RandomVector Omega (n + 1)) (K : Real) : Prop where
  coordinatePsi1 : forall i : Fin (n + 1), Psi1Bound P (coord G i) K

/-- Mixed Orlicz package for examples with both features and gradients. -/
structure FeatureGradientOrliczAssumptions {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    (X G : RandomVector Omega (n + 1)) (KFeature KGradient : Real) : Prop where
  featurePsi2 : CoordinatewisePsi2Feature (P := P) X KFeature
  gradientPsi1 : CoordinatewisePsi1Gradient (P := P) G KGradient

/-- A coordinatewise `psi_2` assumption gives finite `psi_2` size for each
coordinate. -/
theorem hasFinitePsi2_coord_of_coordinatewise {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {X : RandomVector Omega (n + 1)} {K : Real}
    (hX : CoordinatewisePsi2Feature (P := P) X K)
    (i : Fin (n + 1)) :
    HasFinitePsi2 P (coord X i) := by
  exact Exists.intro K (hX.coordinatePsi2 i)

/-- A coordinatewise `psi_1` assumption gives finite `psi_1` size for each
coordinate. -/
theorem hasFinitePsi1_coord_of_coordinatewise {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {n : Nat}
    {G : RandomVector Omega (n + 1)} {K : Real}
    (hG : CoordinatewisePsi1Gradient (P := P) G K)
    (i : Fin (n + 1)) :
    HasFinitePsi1 P (coord G i) := by
  exact Exists.intro K (hG.coordinatePsi1 i)

/-- Finite table of feature vectors, matching random-feature and NTK examples. -/
abbrev OrliczFeatureTable (Omega : Type*)
    (width n : Nat) :=
  Fin width -> RandomVector Omega (n + 1)

/-- Coordinatewise Orlicz package for a finite feature table. -/
structure CoordinatewisePsi2FeatureTable {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {width n : Nat}
    (Phi : OrliczFeatureTable Omega width n) (K : Real) : Prop where
  featureCoordinatePsi2 :
    forall a : Fin width, forall i : Fin (n + 1),
      Psi2Bound P (coord (Phi a) i) K

/-- Feature-table assumptions specialize to the single-feature vector package. -/
theorem coordinatewisePsi2Feature_of_table {Omega : Type*}
    [MeasurableSpace Omega] {P : Measure Omega} {width n : Nat}
    {Phi : OrliczFeatureTable Omega width n} {K : Real}
    (hPhi : CoordinatewisePsi2FeatureTable (P := P) Phi K)
    (a : Fin width) :
    CoordinatewisePsi2Feature (P := P) (Phi a) K := by
  exact CoordinatewisePsi2Feature.mk
    (fun i => hPhi.featureCoordinatePsi2 a i)

end

end HighDimProb.Examples.OrliczFeatureUsage
