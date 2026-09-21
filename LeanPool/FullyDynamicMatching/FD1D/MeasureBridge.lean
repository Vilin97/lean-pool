/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Kernel.Basic
import LeanPool.FullyDynamicMatching.FD1D.FinalArithmetic
import LeanPool.FullyDynamicMatching.FD1D.InvariantTransport
import LeanPool.FullyDynamicMatching.FD1D.Realization

/-! # Measure Bridge -/

namespace FD1D

noncomputable section

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal

/-!
# Finite laws as measures

This file connects the project's elementary `FiniteLaw` API to Mathlib
probability measures. It also transfers bounds indexed by a finite count
state to arbitrary random spatial configurations having that count
pushforward.
-/

namespace FiniteLaw

variable {α β Ω : Type*} [Fintype α]

/-- The probability mass function represented by a `FiniteLaw`. -/
def toPMF (μ : FiniteLaw α) : PMF α :=
  PMF.ofFintype (fun x => ENNReal.ofReal (μ.mass x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun x _ => μ.mass_nonneg x), μ.sum_mass]
    simp)

@[simp]
theorem toPMF_apply (μ : FiniteLaw α) (x : α) :
    μ.toPMF x = ENNReal.ofReal (μ.mass x) :=
  rfl

/--
The probability measure represented by a `FiniteLaw`.

On a finite type it is enough to assume measurable singletons: this already
makes every function from the type measurable.
-/
def toMeasure [MeasurableSpace α] (μ : FiniteLaw α) : Measure α :=
  μ.toPMF.toMeasure

instance toMeasure.isProbabilityMeasure [MeasurableSpace α]
    (μ : FiniteLaw α) : IsProbabilityMeasure μ.toMeasure := by
  unfold toMeasure
  infer_instance

@[simp]
theorem toMeasure_apply_singleton [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : FiniteLaw α) (x : α) :
    μ.toMeasure ({x} : Set α) = ENNReal.ofReal (μ.mass x) := by
  rw [toMeasure,
    PMF.toMeasure_apply_singleton μ.toPMF x (MeasurableSet.singleton x)]
  rfl

@[simp]
theorem toMeasure_real_singleton [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : FiniteLaw α) (x : α) :
    μ.toMeasure.real ({x} : Set α) = μ.mass x := by
  rw [Measure.real, toMeasure_apply_singleton,
    ENNReal.toReal_ofReal (μ.mass_nonneg x)]

/-- Integration against the associated measure is `FiniteLaw.expect`. -/
@[simp]
theorem integral_toMeasure_eq_expect [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : FiniteLaw α) (f : α → ℝ) :
    ∫ x, f x ∂μ.toMeasure = μ.expect f := by
  rw [toMeasure, PMF.integral_eq_sum]
  simp only [toPMF_apply, ENNReal.toReal_ofReal (μ.mass_nonneg _),
    smul_eq_mul, expect]

/-- Every real observable is integrable under a finite law's measure. -/
theorem integrable_toMeasure [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : FiniteLaw α) (f : α → ℝ) :
    Integrable f μ.toMeasure :=
  Integrable.of_finite

/--
A generic pushforward bridge. If `X` has finite law `μ`, then any integrable
random cost bounded by a state observable has expectation bounded by the
corresponding `FiniteLaw.expect`.
-/
theorem integral_le_expect_of_map_eq
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (P : Measure Ω) (μ : FiniteLaw α)
    (X : Ω → α) (cost : Ω → ℝ) (bound : α → ℝ)
    (hX : AEMeasurable X P)
    (hcost : Integrable cost P)
    (hpoint : ∀ᵐ ω ∂P, cost ω ≤ bound (X ω))
    (hmap : Measure.map X P = μ.toMeasure) :
    ∫ ω, cost ω ∂P ≤ μ.expect bound := by
  have hboundMap : Integrable bound (Measure.map X P) := by
    rw [hmap]
    exact μ.integrable_toMeasure bound
  have hbound :
      Integrable (bound ∘ X) P :=
    hboundMap.comp_aemeasurable hX
  calc
    ∫ ω, cost ω ∂P ≤ ∫ ω, (bound ∘ X) ω ∂P :=
      integral_mono_ae hcost hbound hpoint
    _ = ∫ x, bound x ∂Measure.map X P :=
      (integral_map hX hboundMap.aestronglyMeasurable).symm
    _ = ∫ x, bound x ∂μ.toMeasure := by rw [hmap]
    _ = μ.expect bound := integral_toMeasure_eq_expect μ bound

/-- A convenient final-bound form of `integral_le_expect_of_map_eq`. -/
theorem integral_le_of_map_eq_of_expect_le
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace Ω]
    (P : Measure Ω) (μ : FiniteLaw α)
    (X : Ω → α) (cost : Ω → ℝ) (bound : α → ℝ) (B : ℝ)
    (hX : AEMeasurable X P)
    (hcost : Integrable cost P)
    (hpoint : ∀ᵐ ω ∂P, cost ω ≤ bound (X ω))
    (hmap : Measure.map X P = μ.toMeasure)
    (hbound : μ.expect bound ≤ B) :
    ∫ ω, cost ω ∂P ≤ B :=
  (integral_le_expect_of_map_eq P μ X cost bound
    hX hcost hpoint hmap).trans hbound

end FiniteLaw

namespace FiniteKernel

variable {α : Type*} [Fintype α]

/-- The probability law represented by one row of a finite kernel. -/
def rowLaw (K : FiniteKernel α) (x : α) : FiniteLaw α where
  mass := K x
  mass_nonneg := K.trans_nonneg x
  sum_mass := K.sum_trans x

@[simp]
theorem rowLaw_mass (K : FiniteKernel α) (x y : α) :
    (K.rowLaw x).mass y = K x y :=
  rfl

/-- A project `FiniteKernel`, viewed as a Mathlib Markov kernel. -/
noncomputable def toKernel [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : FiniteKernel α) : Kernel α α where
  toFun x := (K.rowLaw x).toMeasure
  measurable' := measurable_of_finite _

@[simp]
theorem toKernel_apply [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : FiniteKernel α) (x : α) :
    K.toKernel x = (K.rowLaw x).toMeasure :=
  rfl

instance toKernel.isMarkovKernel
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (K : FiniteKernel α) : IsMarkovKernel K.toKernel where
  isProbabilityMeasure x := by
    change IsProbabilityMeasure (K.rowLaw x).toMeasure
    infer_instance

end FiniteKernel

namespace HierarchicalDynamics

variable {L m : ℕ}

/-- The actual one-period cost of a concrete spatial configuration. -/
def actualConfigurationCost (a : ℝ) (hm : 0 < m)
    (C : SupplyConfiguration L m) : ℝ :=
  C.expectedActualDistance (stateDyadicMass a C.countState)
    (SupplyConfiguration.canonicalFallback hm)

/--
An arbitrary spatial law is bounded by the finite-law expectation of the
canonical Haar pointwise majorant whenever its count-state pushforward is the
given finite law.
-/
theorem integral_actualConfigurationCost_le_expect
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (InventoryState (DyadicNode L) m)]
    [MeasurableSingletonClass (InventoryState (DyadicNode L) m)]
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (P : Measure Ω)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (C : Ω → SupplyConfiguration L m)
    (hstate : AEMeasurable (fun ω => (C ω).countState) P)
    (hcost : Integrable (fun ω => actualConfigurationCost a hm (C ω)) P)
    (hmap :
      Measure.map (fun ω => (C ω).countState) P = μ.toMeasure) :
    ∫ ω, actualConfigurationCost a hm (C ω) ∂P ≤
      μ.expect (fun x =>
        1 / ((2 ^ L : ℕ) : ℝ) +
          cdfTransportArea
            (haarCombination (haarNodeLeft (L := L))
              (haarNodeWidth (L := L))
              (stateHaarCoefficient a x))) := by
  apply FiniteLaw.integral_le_expect_of_map_eq P μ
    (fun ω => (C ω).countState)
    (fun ω => actualConfigurationCost a hm (C ω))
    (fun x =>
      1 / ((2 ^ L : ℕ) : ℝ) +
        cdfTransportArea
          (haarCombination (haarNodeLeft (L := L))
            (haarNodeWidth (L := L))
            (stateHaarCoefficient a x)))
    hstate hcost
  · filter_upwards with ω
    exact stateActualCost_pointwise a ha hm (C ω)
      (SupplyConfiguration.canonicalFallback hm)
  · exact hmap

/--
Stationary equation (3) for an arbitrary random spatial configuration. Only
the count pushforward is required to be stationary; configurations in the
same count-state fiber may have any distribution.
-/
theorem stationary_actualConfigurationCost_equation_three
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (InventoryState (DyadicNode L) m)]
    [MeasurableSingletonClass (InventoryState (DyadicNode L) m)]
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (P : Measure Ω)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (C : Ω → SupplyConfiguration L m)
    (hstate : AEMeasurable (fun ω => (C ω).countState) P)
    (hcost : Integrable (fun ω => actualConfigurationCost a hm (C ω)) P)
    (hmap :
      Measure.map (fun ω => (C ω).countState) P = μ.toMeasure)
    (hμ : (kernel (L := L) (m := m) a ha hm).IsStationary μ) :
    ∫ ω, actualConfigurationCost a hm (C ω) ∂P ≤
      1 / ((2 ^ L : ℕ) : ℝ) +
        a / Real.sqrt 6 *
          Real.sqrt
            (μ.expect (fun x => stateHazardEnergy a x L) -
              1 / (m : ℝ) ^ 2) := by
  let bound : InventoryState (DyadicNode L) m → ℝ := fun x =>
    1 / ((2 ^ L : ℕ) : ℝ) +
      cdfTransportArea
        (haarCombination (haarNodeLeft (L := L))
          (haarNodeWidth (L := L))
          (stateHaarCoefficient a x))
  have hspatial :
      ∫ ω, actualConfigurationCost a hm (C ω) ∂P ≤
        μ.expect bound := by
    simpa [bound] using
      integral_actualConfigurationCost_le_expect
        a ha hm P μ C hstate hcost hmap
  have hfinite :
      μ.expect bound ≤
        1 / ((2 ^ L : ℕ) : ℝ) +
          a / Real.sqrt 6 *
            Real.sqrt
              (μ.expect (fun x => stateHazardEnergy a x L) -
                1 / (m : ℝ) ^ 2) := by
    apply concrete_transport_equation_three
      μ (fun x => x) bound a ha hm
    · intro x
      exact le_rfl
    · simpa using
        concrete_stationary_haar_crossTerm_symmetry
          a ha hm μ (kernel_irreducible a ha hm) hμ
  exact hspatial.trans hfinite

end HierarchicalDynamics

/--
The stationary `6a/m` result transferred from a finite count law to an
arbitrary random law of actual spatial configurations.
-/
theorem stationary_expected_actualConfigurationCost_le_six
    {m : ℕ} (hm : 1 ≤ m)
    {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace
      (InventoryState (DyadicNode (treeDepth m)) m)]
    [MeasurableSingletonClass
      (InventoryState (DyadicNode (treeDepth m)) m)]
    (P : Measure Ω)
    (μ : FiniteLaw
      (InventoryState (DyadicNode (treeDepth m)) m))
    (C : Ω → SupplyConfiguration (treeDepth m) m)
    (hstate : AEMeasurable (fun ω => (C ω).countState) P)
    (hcost : Integrable (fun ω =>
      HierarchicalDynamics.actualConfigurationCost
        (parameterA m : ℝ) (by omega) (C ω)) P)
    (hmap :
      Measure.map (fun ω => (C ω).countState) P = μ.toMeasure)
    (hμ : (parameterizedKernel m hm).IsStationary μ) :
    ∫ ω,
        HierarchicalDynamics.actualConfigurationCost
          (parameterA m : ℝ) (by omega) (C ω) ∂P ≤
      6 * (parameterA m : ℝ) / (m : ℝ) := by
  have ha := parameterA_cast_pos hm
  have hmpos : 0 < m := by omega
  let bound :
      InventoryState (DyadicNode (treeDepth m)) m → ℝ := fun x =>
    1 / ((2 ^ treeDepth m : ℕ) : ℝ) +
      cdfTransportArea
        (haarCombination (haarNodeLeft (L := treeDepth m))
          (haarNodeWidth (L := treeDepth m))
          (HierarchicalDynamics.stateHaarCoefficient
            (parameterA m : ℝ) x))
  have hspatial :
      ∫ ω,
          HierarchicalDynamics.actualConfigurationCost
            (parameterA m : ℝ) hmpos (C ω) ∂P ≤
        μ.expect bound := by
    simpa [bound] using
      (HierarchicalDynamics.integral_actualConfigurationCost_le_expect
        (L := treeDepth m) (m := m)
        (parameterA m : ℝ) ha hmpos P μ C hstate hcost hmap)
  have hμ' :
      (HierarchicalDynamics.kernel
        (L := treeDepth m) (m := m)
        (parameterA m : ℝ) ha hmpos).IsStationary μ := by
    simpa [parameterizedKernel] using hμ
  have hHazard :
      parameterizedHazardEnergy m =
        fun x => HierarchicalDynamics.stateHazardEnergy
          (parameterA m : ℝ) x (treeDepth m) := rfl
  have htransport :
      μ.expect bound ≤
        1 / (leafCount m : ℝ) +
          (parameterA m : ℝ) / Real.sqrt 6 *
            Real.sqrt
              (μ.expect (parameterizedHazardEnergy m) -
                1 / (m : ℝ) ^ 2) := by
    rw [hHazard]
    simpa [bound, leafCount] using
      (HierarchicalDynamics.concrete_transport_equation_three
        μ (fun x => x) bound (parameterA m : ℝ) ha hmpos
        (fun _ => le_rfl)
        (by
          simpa using
            HierarchicalDynamics.concrete_stationary_haar_crossTerm_symmetry
              (parameterA m : ℝ) ha hmpos μ
              (HierarchicalDynamics.kernel_irreducible
                (parameterA m : ℝ) ha hmpos) hμ'))
  exact hspatial.trans
    (stationary_expected_cost_le_six hm μ bound hμ htransport)

end

end FD1D
