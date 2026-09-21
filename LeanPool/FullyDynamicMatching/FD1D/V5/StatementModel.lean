/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Paper-facing model for fully dynamic matching on the line

This module gives a compact, Mathlib-only statement vocabulary for the main
theorem. An online policy sees the current inventory and current demand, selects
one live supply, pays their distance, and replaces that supply by an independent
uniform replenishment. The path measure below is the homogeneous Markov law
driven by iid uniform demand/replenishment pairs.
-/

namespace FD1D.V5.Palomar

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory Topology unitInterval

/-- A labeled inventory of `m` supplies in `[0,1]`. -/
abbrev Inventory (m : ℕ) := Fin m → unitInterval

/-- One period's independent demand and replenishment coordinates. -/
abbrev Noise := unitInterval × unitInterval

/-- The law of an independent uniform demand/replenishment pair. -/
def noiseLaw : Measure Noise :=
  (volume : Measure unitInterval).prod volume

instance noiseLaw_isProbabilityMeasure :
    IsProbabilityMeasure noiseLaw := by
  unfold noiseLaw
  infer_instance

/--
An online matching policy. The selected label depends only on the current
inventory and current demand. The second measurability field records the exact
coordinate replacement map used to construct its Markov law.
-/
structure OnlinePolicy (m : ℕ) where
  /-- Selected inventory label as a function of the current state and uniform demand. -/
  select : Inventory m → unitInterval → Fin m
  selectMeasurable :
    Measurable (fun p : Inventory m × unitInterval => select p.1 p.2)
  stepMeasurable :
    Measurable (fun p : Inventory m × Noise =>
      Function.update p.1 (select p.1 p.2.1) p.2.2)

/-- Replace the selected supply by the replenishment coordinate. -/
def step (P : OnlinePolicy m) (s : Inventory m) (z : Noise) :
    Inventory m :=
  Function.update s (P.select s z.1) z.2

/-- The pre-match inventory together with the current random coordinates. -/
abbrev ProcessState (m : ℕ) := Inventory m × Noise

/-- Apply the current noise and attach fresh noise for the next period. -/
def processAdvance (P : OnlinePolicy m)
    (p : ProcessState m × Noise) : ProcessState m :=
  (step P p.1.1 p.1.2, p.2)

theorem processAdvance_measurable (P : OnlinePolicy m) :
    Measurable (processAdvance P) := by
  exact (P.stepMeasurable.comp measurable_fst).prodMk measurable_snd

/-- The homogeneous one-period kernel of an online policy. -/
def processKernel (P : OnlinePolicy m) :
    Kernel (ProcessState m) (ProcessState m) :=
  (Kernel.id ×ₖ Kernel.const (ProcessState m) noiseLaw).map
    (processAdvance P)

instance processKernel_isMarkovKernel (P : OnlinePolicy m) :
    IsMarkovKernel (processKernel P) := by
  unfold processKernel
  exact Kernel.IsMarkovKernel.map _ (processAdvance_measurable P)

/-- Attach an independent first demand/replenishment pair to an inventory law. -/
def initialProcessLaw (μ₀ : Measure (Inventory m)) :
    Measure (ProcessState m) :=
  μ₀.prod noiseLaw

instance initialProcessLaw_isProbabilityMeasure
    (μ₀ : Measure (Inventory m)) [IsProbabilityMeasure μ₀] :
    IsProbabilityMeasure (initialProcessLaw μ₀) := by
  unfold initialProcessLaw
  infer_instance

/-- A homogeneous kernel viewed as a history-dependent kernel. -/
def historyKernel (P : OnlinePolicy m) (n : ℕ) :
    Kernel ((i : Finset.Iic n) → ProcessState m) (ProcessState m) :=
  (processKernel P).comap
    (fun h => h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (by fun_prop)

instance historyKernel_isMarkovKernel (P : OnlinePolicy m) (n : ℕ) :
    IsMarkovKernel (historyKernel P n) := by
  unfold historyKernel
  infer_instance

/-- The path-space law generated from an arbitrary initial inventory law. -/
def trajectoryFrom (P : OnlinePolicy m)
    (μ₀ : Measure (Inventory m)) :
    Measure (ℕ → ProcessState m) :=
  Kernel.trajMeasure (X := fun _ => ProcessState m)
    (initialProcessLaw μ₀) (historyKernel P)

/-- The trajectory law from a fixed initial inventory. -/
def trajectoryFromState (P : OnlinePolicy m) (s₀ : Inventory m) :
    Measure (ℕ → ProcessState m) :=
  trajectoryFrom P (Measure.dirac s₀)

/-- The iid uniform law of the inventory produced by scheduled replacement. -/
def uniformInventoryLaw (m : ℕ) : Measure (Inventory m) :=
  Measure.pi fun _ : Fin m => (volume : Measure unitInterval)

instance uniformInventoryLaw_isProbabilityMeasure :
    IsProbabilityMeasure (uniformInventoryLaw m) := by
  unfold uniformInventoryLaw
  infer_instance

/-- The policy trajectory after iid uniform initialization. -/
def uniformTrajectory (P : OnlinePolicy m) :
    Measure (ℕ → ProcessState m) :=
  trajectoryFrom P (uniformInventoryLaw m)

/-- The distance paid in one period. -/
def processCost (P : OnlinePolicy m) (z : ProcessState m) : ℝ :=
  |(z.1 (P.select z.1 z.2.1) : ℝ) - (z.2.1 : ℝ)|

/-- Root mean square one-period cost from a fixed initial inventory. -/
def trajectoryRMSCostFromState
    (P : OnlinePolicy m) (s₀ : Inventory m) (t : ℕ) : ℝ :=
  Real.sqrt
    (∫ path : ℕ → ProcessState m,
      processCost P (path t) ^ 2 ∂trajectoryFromState P s₀)

/--
The total cost of matching once to every original labeled supply during the
first `m` periods.
-/
def initializationCost (initial demand : Inventory m) : ℝ :=
  ∑ j, |(demand j : ℝ) - (initial j : ℝ)|

/--
Average cost over `N` periods: scheduled replacement first, followed by the
online policy on the resulting iid uniform inventory.
-/
def initializedAverageCost
    (P : OnlinePolicy m) (initial demand : Inventory m) (N : ℕ)
    (path : ℕ → ProcessState m) : ℝ :=
  (initializationCost initial demand +
      ∑ t ∈ Finset.range (N - m), processCost P (path t)) / (N : ℝ)

/-- The manuscript's regularization parameter. -/
def regularization (m : ℕ) : ℕ :=
  2000 * Nat.clog 2 (m + 1)

/-- The dyadic tree depth used by the policy. -/
def treeDepth (m : ℕ) : ℕ :=
  Nat.log 2 (max 1 (m / regularization m))

/-- The dyadic leaf count used by the policy. -/
def leafCount (m : ℕ) : ℕ :=
  2 ^ treeDepth m

/-- Abstract primitive-operation count in the real-arithmetic model. -/
def operationCount (m : ℕ) : ℕ :=
  20 * (treeDepth m + 1)

/-- Abstract memory-word count in the real-arithmetic model. -/
def memoryCount (m : ℕ) : ℕ :=
  m + 4 * leafCount m

/-- One explicit universal constant for both cost bounds. -/
def universalConstant : ℝ :=
  72000 / Real.log 2

/-- The two quantitative guarantees for one inventory size. -/
structure PolicyGuarantees (m : ℕ) (P : OnlinePolicy m) : Prop where
  arbitraryInitialRMS :
    ∀ s₀ : Inventory m,
      Filter.limsup (trajectoryRMSCostFromState P s₀) atTop ≤
        universalConstant * Real.log ((m + 1 : ℕ) : ℝ) / (m : ℝ)
  initializedFiniteHorizon :
    ∀ N : ℕ, 2 * m ^ 2 ≤ N →
      ∀ initial demand : Inventory m,
        (∫ path : ℕ → ProcessState m,
          initializedAverageCost P initial demand N path
            ∂uniformTrajectory P) ≤
          universalConstant * Real.log ((m + 1 : ℕ) : ℝ) / (m : ℝ)

/-- Explicit and asymptotic resource accounting for the policy family. -/
structure ResourceGuarantees : Prop where
  operationsExplicit :
    ∀ {m : ℕ}, 2 ≤ m →
      (operationCount m : ℝ) ≤
        (100 / Real.log 2) * Real.log (m : ℝ)
  memoryExplicit :
    ∀ {m : ℕ}, 1 ≤ m → memoryCount m ≤ 5 * m
  operationsAsymptotic :
    (fun m : ℕ => (operationCount m : ℝ)) =O[atTop]
      (fun m : ℕ => Real.log (m : ℝ))
  memoryAsymptotic :
    (fun m : ℕ => (memoryCount m : ℝ)) =O[atTop]
      (fun m : ℕ => (m : ℝ))

/-- Exact compared content of the formalized stochastic cost upper bound. -/
structure OptimalDynamicMatchingUpperBound : Prop where
  policy :
    ∀ (m : ℕ), 2 ≤ m →
      ∃ P : OnlinePolicy m, PolicyGuarantees m P

end

end FD1D.V5.Palomar
