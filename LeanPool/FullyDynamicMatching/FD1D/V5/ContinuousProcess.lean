/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.ContinuousState
import LeanPool.FullyDynamicMatching.FD1D.KernelBridge
import LeanPool.FullyDynamicMatching.FD1D.V5.Process
import LeanPool.FullyDynamicMatching.FD1D.TrajectoryBridge
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! # Continuous Process -/

namespace FD1D

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory unitInterval

/-!
# The continuous-coordinate matching process

This module constructs the policy on one probability space.  A state records
the live supply coordinates together with the current independent demand and
replenishment coordinates.  The reward and the inventory update therefore
use the same demand sample.
-/

namespace V5.ContinuousProcess

variable {L m : ℕ}

/-- One period's independent demand and replenishment coordinates. -/
abbrev Noise := unitInterval × unitInterval

/-- The law of an independent uniform demand/replenishment pair. -/
def noiseLaw : Measure Noise :=
  (volume : Measure unitInterval).prod volume

instance noiseLaw.isProbabilityMeasure :
    IsProbabilityMeasure noiseLaw := by
  unfold noiseLaw
  infer_instance

/-- Coercing the canonical unit-interval law gives restricted Lebesgue measure. -/
theorem map_coe_volume :
    Measure.map (fun u : unitInterval => (u : ℝ)) volume =
      DyadicMass.uniformDemand := by
  simpa [DyadicMass.uniformDemand] using
    unitInterval.measurePreserving_coe.map_eq

/-- A continuous uniform coordinate has the finite selected-index law. -/
theorem map_selectedIndex_volume
    (q : DyadicMass L) (hq : q.IsProbability) :
    Measure.map (fun u : unitInterval => q.selectedIndex (u : ℝ)) volume =
      (q.selectedIndexLaw hq).toMeasure := by
  change
    Measure.map
        (q.selectedIndex ∘ (fun u : unitInterval => (u : ℝ))) volume =
      (q.selectedIndexLaw hq).toMeasure
  rw [← Measure.map_map q.selectedIndex_measurable measurable_subtype_coe]
  rw [map_coe_volume]
  letI : IsProbabilityMeasure DyadicMass.uniformDemand := by
    rw [← map_coe_volume]
    exact Measure.isProbabilityMeasure_map
      measurable_subtype_coe.aemeasurable
  apply FiniteLaw.measure_ext_of_singletons
  intro i
  rw [FiniteLaw.toMeasure_apply_singleton]
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [DyadicMass.selectedIndexLaw_mass]
  rw [ENNReal.toReal_ofReal (q.leafMass_nonneg hq.nonneg i)]
  exact q.selectedIndexPushforwardMass_eq_leafMass hq i

/-- The replenishment coordinate induces the uniform dyadic-leaf law. -/
theorem map_uniformArrivalLeaf_volume (L : ℕ) :
    Measure.map
        (fun u : unitInterval =>
          DyadicMass.uniformArrivalLeaf L (u : ℝ)) volume =
      (FiniteLaw.uniform : FiniteLaw (DyadicNode L)).toMeasure := by
  calc
    Measure.map
        (fun u : unitInterval =>
          DyadicMass.uniformArrivalLeaf L (u : ℝ)) volume =
        (DyadicMass.uniformArrivalLeafLaw L).toMeasure := by
      simpa [DyadicMass.uniformArrivalLeaf,
        DyadicMass.uniformArrivalLeafLaw] using
        (map_selectedIndex_volume
          (DyadicMass.uniformArrivalMass L)
          (DyadicMass.uniformArrivalMass_isProbability L))
    _ = (FiniteLaw.uniform : FiniteLaw (DyadicNode L)).toMeasure := by
      rw [DyadicMass.uniformArrivalLeafLaw_eq_uniform]

/-- The two leaf labels extracted from one noise pair have the product law. -/
theorem map_noiseLeaves
    (q : DyadicMass L) (hq : q.IsProbability) :
    Measure.map
        (fun z : Noise =>
          (q.selectedIndex (z.1 : ℝ),
            DyadicMass.uniformArrivalLeaf L (z.2 : ℝ)))
        noiseLaw =
      ((q.selectedIndexLaw hq).product
        (FiniteLaw.uniform : FiniteLaw (DyadicNode L))).toMeasure := by
  rw [FiniteLaw.toMeasure_product, noiseLaw]
  rw [← map_selectedIndex_volume q hq,
    ← map_uniformArrivalLeaf_volume L]
  exact (Measure.map_prod_map volume volume
    (q.selectedIndex_measurable.comp measurable_subtype_coe)
    ((DyadicMass.uniformArrivalMass L).selectedIndex_measurable.comp
      measurable_subtype_coe)).symm

/-- Iid continuous coordinates for the refreshed live inventory. -/
def initialSpatialLaw (m : ℕ) : Measure (SpatialState m) :=
  Measure.pi fun _ : Fin m => (volume : Measure unitInterval)

instance initialSpatialLaw.isProbabilityMeasure :
    IsProbabilityMeasure (initialSpatialLaw m) := by
  unfold initialSpatialLaw
  infer_instance

/-- The leaf assignment obtained from iid continuous coordinates is uniform. -/
theorem map_spatialLeaves_initialSpatialLaw (L m : ℕ) :
    Measure.map (spatialLeaves L) (initialSpatialLaw m) =
      (FiniteLaw.uniform : FiniteLaw (DyadicAssignment L m)).toMeasure := by
  change
    Measure.map
        (fun s : SpatialState m =>
          fun j =>
            ((DyadicMass.uniformArrivalMass L).selectedIndex ∘
              (fun u : unitInterval => (u : ℝ))) (s j))
        (initialSpatialLaw m) =
      (FiniteLaw.uniform : FiniteLaw (DyadicAssignment L m)).toMeasure
  have hcoordinate :
      Measure.map
          ((DyadicMass.uniformArrivalMass L).selectedIndex ∘
            (fun u : unitInterval => (u : ℝ))) volume =
        (FiniteLaw.uniform : FiniteLaw (DyadicNode L)).toMeasure := by
    change
      Measure.map
          (fun u : unitInterval =>
            DyadicMass.uniformArrivalLeaf L (u : ℝ)) volume =
        (FiniteLaw.uniform : FiniteLaw (DyadicNode L)).toMeasure
    exact map_uniformArrivalLeaf_volume L
  rw [initialSpatialLaw]
  rw [Measure.pi_map_pi fun _ =>
    ((DyadicMass.uniformArrivalMass L).selectedIndex_measurable.comp
      measurable_subtype_coe).aemeasurable]
  simp_rw [hcoordinate]
  apply FiniteLaw.measure_ext_of_singletons
  intro assignment
  rw [Measure.pi_singleton, FiniteLaw.toMeasure_apply_singleton]
  simp only [FiniteLaw.mass_uniform]
  rw [Fintype.card_fun]
  simp only [FiniteLaw.toMeasure_apply_singleton, FiniteLaw.mass_uniform,
    Finset.prod_const, Finset.card_univ]
  rw [← ENNReal.ofReal_pow (by positivity :
    0 ≤ (1 / Fintype.card (DyadicNode L) : ℝ))]
  congr 1
  simp only [Fintype.card_fin]
  push_cast
  exact one_div_pow _ _

/-- The refreshed continuous inventory projects to the existing refreshed count law. -/
theorem map_spatialCount_initialSpatialLaw (L m : ℕ) :
    Measure.map (spatialCount L) (initialSpatialLaw m) =
      (refreshedLaw L m).toMeasure := by
  have hcount :
      (spatialCount (m := m) L :
          SpatialState m → InventoryState (DyadicNode L) m) =
        assignmentState ∘ (spatialLeaves (m := m) L) := by
    funext s
    apply InventoryState.ext
    intro i
    rfl
  rw [hcount, ← Measure.map_map
    (measurable_of_finite assignmentState)
    (spatialLeaves_measurable (m := m) L)]
  rw [map_spatialLeaves_initialSpatialLaw]
  simpa [refreshedLaw] using
    (FiniteLaw.toMeasure_map
      (FiniteLaw.uniform : FiniteLaw (DyadicAssignment L m))
      assignmentState (measurable_of_finite assignmentState))

/-! ## One-step lumping to the finite count kernel -/

/-- The finite deleted/arrived leaf pair generated at a fixed spatial state. -/
def leafPairLaw (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (s : SpatialState m) :
    FiniteLaw (DyadicNode L × DyadicNode L) :=
  ((Dynamics.stateDyadicMass a (spatialCount L s)).selectedIndexLaw
      (Dynamics.stateDyadicMass_isProbability
        a ha hm (spatialCount L s))).product
    (FiniteLaw.uniform : FiniteLaw (DyadicNode L))

/-- Forgetting the leaf pair after its move gives exactly one finite-kernel row. -/
theorem leafPairLaw_map_move
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (s : SpatialState m) :
    (leafPairLaw (L := L) a ha hm s).map
        (fun p => InventoryState.move (spatialCount L s) p.1 p.2) =
      (Dynamics.kernel
        (L := L) (m := m) a ha hm).rowLaw (spatialCount L s) := by
  classical
  apply FiniteLaw.ext
  intro y
  rw [FiniteLaw.mass_map, FiniteKernel.rowLaw_mass]
  change
    (∑ p with
      InventoryState.move (toConfiguration L s).countState p.1 p.2 = y,
        (leafPairLaw (L := L) a ha hm s).mass p) =
      Dynamics.kernel a ha hm
        (toConfiguration L s).countState y
  rw [← Dynamics.configured_transition_eq_kernel
    a ha hm (toConfiguration L s) y]
  rw [Finset.sum_filter]
  conv_lhs => rw [Fintype.sum_prod_type]
  simp only [leafPairLaw, FiniteLaw.mass_product,
    FiniteLaw.mass_uniform, toConfiguration_countState]

/-- The zero demand endpoint is null under the continuous noise law. -/
theorem noise_demand_ne_zero_ae :
    ∀ᵐ z : Noise ∂noiseLaw, (z.1 : ℝ) ≠ 0 := by
  rw [ae_iff]
  have hbad :
      {z : Noise | ¬(z.1 : ℝ) ≠ 0} =
        ({⟨0, by norm_num⟩} : Set unitInterval) ×ˢ Set.univ := by
    ext z
    simp only [mem_setOf_eq, mem_prod, mem_singleton_iff, mem_univ,
      and_true, not_ne_iff]
    constructor
    · intro hz
      exact Subtype.ext hz
    · intro hz
      exact congrArg Subtype.val hz
  rw [hbad, noiseLaw, Measure.prod_prod]
  simp

/-- The continuous noise pair, mapped to deleted/arrived leaves, has `leafPairLaw`. -/
theorem map_noiseLeaves_eq_leafPairLaw
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (s : SpatialState m) :
    Measure.map
        (fun z : Noise =>
          ((Dynamics.stateDyadicMass a (spatialCount L s)).selectedIndex
              (z.1 : ℝ),
            DyadicMass.uniformArrivalLeaf L (z.2 : ℝ)))
        noiseLaw =
      (leafPairLaw (L := L) a ha hm s).toMeasure := by
  exact map_noiseLeaves
    (Dynamics.stateDyadicMass a (spatialCount L s))
    (Dynamics.stateDyadicMass_isProbability
      a ha hm (spatialCount L s))

/--
The count projection of one continuous-coordinate update is exactly the
measure-valued row of the finite count kernel.
-/
theorem map_spatialCount_spatialStep
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (s : SpatialState m) :
    Measure.map (spatialCount L)
        (Measure.map (spatialStep L a fallback s) noiseLaw) =
      (Dynamics.kernel
        (L := L) (m := m) a ha hm).toKernel (spatialCount L s) := by
  rw [Measure.map_map (spatialCount_measurable L)
    (spatialStep_noise_measurable L a fallback s)]
  let pairMap : Noise → DyadicNode L × DyadicNode L := fun z =>
    ((Dynamics.stateDyadicMass a (spatialCount L s)).selectedIndex
        (z.1 : ℝ),
      DyadicMass.uniformArrivalLeaf L (z.2 : ℝ))
  let moveMap : DyadicNode L × DyadicNode L →
      InventoryState (DyadicNode L) m := fun p =>
    InventoryState.move (spatialCount L s) p.1 p.2
  have hpair :
      Measurable pairMap := by
    exact
      (((Dynamics.stateDyadicMass
        a (spatialCount L s)).selectedIndex_measurable.comp
          (measurable_subtype_coe.comp measurable_fst)).prodMk
        ((DyadicMass.uniformArrivalMass L).selectedIndex_measurable.comp
          (measurable_subtype_coe.comp measurable_snd)))
  have hmove : Measurable moveMap :=
    measurable_of_finite _
  have hpath :
      (spatialCount L ∘ spatialStep L a fallback s) =ᵐ[noiseLaw]
        moveMap ∘ pairMap := by
    filter_upwards [noise_demand_ne_zero_ae] with z hz
    exact spatialCount_spatialStep_eq_selectedIndex
      L a ha hm fallback s z hz
  rw [Measure.map_congr hpath]
  rw [← Measure.map_map hmove hpair]
  rw [show Measure.map pairMap noiseLaw =
      (leafPairLaw (L := L) a ha hm s).toMeasure by
    exact map_noiseLeaves_eq_leafPairLaw a ha hm s]
  rw [FiniteLaw.toMeasure_map
    (leafPairLaw (L := L) a ha hm s) moveMap hmove]
  rw [leafPairLaw_map_move a ha hm s]
  rfl

/-! ## The spatial Markov kernel and its count marginals -/

/-- One Markov step: sample fresh continuous noise and apply `spatialStep`. -/
def spatialKernel (a : ℝ) (fallback : Fin m) :
    Kernel (SpatialState m) (SpatialState m) :=
  (Kernel.id ×ₖ Kernel.const (SpatialState m) noiseLaw).map
    (fun p => spatialStep L a fallback p.1 p.2)

instance spatialKernel.isMarkovKernel
    (a : ℝ) (fallback : Fin m) :
    IsMarkovKernel (spatialKernel (L := L) a fallback) := by
  unfold spatialKernel
  exact Kernel.IsMarkovKernel.map _
    (spatialStep_measurable L a fallback)

/-- The row of `spatialKernel` is the pushforward of one independent noise pair. -/
theorem spatialKernel_apply
    (a : ℝ) (fallback : Fin m) (s : SpatialState m) :
    spatialKernel (L := L) a fallback s =
      Measure.map (spatialStep L a fallback s) noiseLaw := by
  rw [spatialKernel, Kernel.map_apply
    (Kernel.id ×ₖ Kernel.const (SpatialState m) noiseLaw)
    (spatialStep_measurable L a fallback)]
  rw [Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod]
  rw [Measure.map_map
    (spatialStep_measurable L a fallback)
    measurable_prodMk_left]
  rfl

/-- Mapping every spatial-kernel row through counts gives the finite row. -/
theorem spatialKernel_map_count
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) :
    (spatialKernel (L := L) a fallback).map (spatialCount L) =
      (Dynamics.kernel
        (L := L) (m := m) a ha hm).toKernel.comap
          (spatialCount L) (spatialCount_measurable L) := by
  apply Kernel.ext
  intro s
  rw [Kernel.map_apply _ (spatialCount_measurable L)]
  rw [Kernel.comap_apply]
  rw [spatialKernel_apply]
  exact map_spatialCount_spatialStep a ha hm fallback s

/-- A kernel comap composed with a measure is composition after pushforward. -/
private theorem comap_comp_measure
    {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (κ : Kernel β γ) (f : α → β) (hf : Measurable f)
    (μ : Measure α) :
    κ.comap f hf ∘ₘ μ = κ ∘ₘ Measure.map f μ := by
  rw [← Kernel.comp_deterministic_eq_comap κ hf]
  rw [← Measure.comp_assoc]
  rw [Measure.deterministic_comp_eq_map hf]

/-- The continuous spatial law after `t` policy steps. -/
def spatialLaw (a : ℝ) (fallback : Fin m) :
    ℕ → Measure (SpatialState m)
  | 0 => initialSpatialLaw m
  | t + 1 =>
      spatialKernel (L := L) a fallback ∘ₘ spatialLaw a fallback t

@[simp]
theorem spatialLaw_zero (a : ℝ) (fallback : Fin m) :
    spatialLaw (L := L) a fallback 0 = initialSpatialLaw m :=
  rfl

@[simp]
theorem spatialLaw_succ (a : ℝ) (fallback : Fin m) (t : ℕ) :
    spatialLaw (L := L) a fallback (t + 1) =
      spatialKernel (L := L) a fallback ∘ₘ
        spatialLaw (L := L) a fallback t :=
  rfl

instance spatialLaw.isProbabilityMeasure
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    IsProbabilityMeasure (spatialLaw (L := L) a fallback t) := by
  induction t with
  | zero =>
      rw [spatialLaw_zero]
      infer_instance
  | succ t ih =>
      rw [spatialLaw_succ]
      infer_instance

/-- Every continuous spatial marginal has exactly the finite count-chain law. -/
theorem map_spatialCount_spatialLaw
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    Measure.map (spatialCount L) (spatialLaw (L := L) a fallback t) =
      ((Dynamics.kernel
        (L := L) (m := m) a ha hm).iterate t
          (refreshedLaw L m)).toMeasure := by
  induction t with
  | zero =>
      simpa using map_spatialCount_initialSpatialLaw L m
  | succ t ih =>
      rw [spatialLaw_succ]
      rw [Measure.map_comp _ _ (spatialCount_measurable L)]
      rw [spatialKernel_map_count a ha hm fallback]
      rw [comap_comp_measure]
      rw [ih]
      rw [FiniteKernel.toMeasure_step]
      rfl

/-! ## A single joint continuous trajectory -/

/--
At a policy time, the joint state contains the pre-match inventory and the
current independent demand/replenishment pair.
-/
abbrev ProcessState (m : ℕ) := SpatialState m × Noise

/-- The refreshed inventory and first noise pair are independent. -/
def initialProcessLaw (m : ℕ) : Measure (ProcessState m) :=
  (initialSpatialLaw m).prod noiseLaw

instance initialProcessLaw.isProbabilityMeasure :
    IsProbabilityMeasure (initialProcessLaw m) := by
  unfold initialProcessLaw
  infer_instance

/--
Apply the current noise pair to the inventory, then attach the freshly sampled
noise pair for the following period.
-/
def processAdvance (L : ℕ) (a : ℝ) (fallback : Fin m)
    (p : ProcessState m × Noise) : ProcessState m :=
  (spatialStep L a fallback p.1.1 p.1.2, p.2)

theorem processAdvance_measurable
    (L : ℕ) (a : ℝ) (fallback : Fin m) :
    Measurable (processAdvance L a fallback) := by
  exact
    ((spatialStep_measurable L a fallback).comp
      ((measurable_fst.comp measurable_fst).prodMk
        (measurable_snd.comp measurable_fst))).prodMk measurable_snd

/-- The homogeneous transition kernel of the joint process. -/
def processKernel (a : ℝ) (fallback : Fin m) :
    Kernel (ProcessState m) (ProcessState m) :=
  (Kernel.id ×ₖ Kernel.const (ProcessState m) noiseLaw).map
    (processAdvance L a fallback)

instance processKernel.isMarkovKernel
    (a : ℝ) (fallback : Fin m) :
    IsMarkovKernel (processKernel (L := L) a fallback) := by
  unfold processKernel
  exact Kernel.IsMarkovKernel.map _
    (processAdvance_measurable L a fallback)

/-- Spatial-kernel composition is the pushforward of state/noise product law. -/
theorem spatialKernel_comp
    (a : ℝ) (fallback : Fin m)
    (μ : Measure (SpatialState m)) [SFinite μ] :
    spatialKernel (L := L) a fallback ∘ₘ μ =
      Measure.map
        (fun p : SpatialState m × Noise =>
          spatialStep L a fallback p.1 p.2)
        (μ.prod noiseLaw) := by
  rw [spatialKernel]
  rw [← Measure.map_comp μ
    (Kernel.id ×ₖ Kernel.const (SpatialState m) noiseLaw)
    (spatialStep_measurable L a fallback)]
  rw [← Measure.compProd_eq_comp_prod]
  rw [Measure.compProd_const]

/-- Starting from an independent state/noise pair preserves that factorization. -/
theorem processKernel_comp_product
    (a : ℝ) (fallback : Fin m)
    (μ : Measure (SpatialState m)) [SFinite μ] :
    processKernel (L := L) a fallback ∘ₘ (μ.prod noiseLaw) =
      (spatialKernel (L := L) a fallback ∘ₘ μ).prod noiseLaw := by
  rw [processKernel]
  rw [← Measure.map_comp (μ.prod noiseLaw)
    (Kernel.id ×ₖ Kernel.const (ProcessState m) noiseLaw)
    (processAdvance_measurable L a fallback)]
  rw [← Measure.compProd_eq_comp_prod]
  rw [Measure.compProd_const]
  let step : SpatialState m × Noise → SpatialState m := fun p =>
    spatialStep L a fallback p.1 p.2
  have hstep : Measurable step :=
    spatialStep_measurable L a fallback
  change
    Measure.map (Prod.map step id) ((μ.prod noiseLaw).prod noiseLaw) =
      (spatialKernel (L := L) a fallback ∘ₘ μ).prod noiseLaw
  rw [← Measure.map_prod_map (μ.prod noiseLaw) noiseLaw hstep measurable_id]
  rw [Measure.map_id]
  rw [← spatialKernel_comp a fallback μ]

/-- The recursively iterated joint-state law. -/
def processLaw (a : ℝ) (fallback : Fin m) (t : ℕ) :
    Measure (ProcessState m) :=
  TrajectoryBridge.iterateLaw
    (processKernel (L := L) a fallback) (initialProcessLaw m) t

instance processLaw.isProbabilityMeasure
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    IsProbabilityMeasure (processLaw (L := L) a fallback t) := by
  induction t with
  | zero =>
      rw [processLaw, TrajectoryBridge.iterateLaw_zero]
      infer_instance
  | succ t ih =>
      letI : IsProbabilityMeasure
          (processLaw (L := L) a fallback t) := ih
      rw [processLaw, TrajectoryBridge.iterateLaw_succ]
      change IsProbabilityMeasure
        (processKernel (L := L) a fallback ∘ₘ
          processLaw (L := L) a fallback t)
      infer_instance

/-- At every time, current noise remains independent of the live inventory. -/
theorem processLaw_eq_product
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    processLaw (L := L) a fallback t =
      (spatialLaw (L := L) a fallback t).prod noiseLaw := by
  induction t with
  | zero =>
      rfl
  | succ t ih =>
      rw [processLaw, TrajectoryBridge.iterateLaw_succ]
      change
        processKernel (L := L) a fallback ∘ₘ
            processLaw (L := L) a fallback t =
          (spatialLaw (L := L) a fallback (t + 1)).prod noiseLaw
      rw [ih, processKernel_comp_product, spatialLaw_succ]

/-- One path-space law carrying the entire joint continuous process. -/
def trajectoryLaw (a : ℝ) (fallback : Fin m) :
    Measure (ℕ → ProcessState m) :=
  TrajectoryBridge.trajectoryLaw
    (initialProcessLaw m) (processKernel (L := L) a fallback)

instance trajectoryLaw.isProbabilityMeasure
    (a : ℝ) (fallback : Fin m) :
    IsProbabilityMeasure (trajectoryLaw (L := L) a fallback) := by
  letI : IsProbabilityMeasure (initialProcessLaw m) :=
    initialProcessLaw.isProbabilityMeasure
  letI : IsMarkovKernel (processKernel (L := L) a fallback) :=
    processKernel.isMarkovKernel a fallback
  unfold trajectoryLaw TrajectoryBridge.trajectoryLaw
  infer_instance

/-- Each coordinate of the single path law is the corresponding joint-state law. -/
theorem trajectoryLaw_marginal
    (a : ℝ) (fallback : Fin m) (t : ℕ) :
    Measure.map (fun path : ℕ → ProcessState m => path t)
        (trajectoryLaw (L := L) a fallback) =
      processLaw (L := L) a fallback t := by
  exact TrajectoryBridge.trajectoryLaw_marginal
    (initialProcessLaw m) (processKernel (L := L) a fallback) t

/-- The count at every path coordinate has the existing finite-chain law. -/
theorem trajectoryLaw_count_marginal
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    Measure.map
        (fun path : ℕ → ProcessState m =>
          spatialCount L (path t).1)
        (trajectoryLaw (L := L) a fallback) =
      ((Dynamics.kernel
        (L := L) (m := m) a ha hm).iterate t
          (refreshedLaw L m)).toMeasure := by
  have hrewrite :
      Measure.map
          (fun path : ℕ → ProcessState m =>
            spatialCount L (path t).1)
          (trajectoryLaw (L := L) a fallback) =
        Measure.map (spatialCount L)
          (Measure.map Prod.fst
            (Measure.map (fun path : ℕ → ProcessState m => path t)
              (trajectoryLaw (L := L) a fallback))) := by
    symm
    rw [Measure.map_map (spatialCount_measurable L) measurable_fst]
    rw [Measure.map_map
      ((spatialCount_measurable L).comp measurable_fst)
      (measurable_pi_apply t)]
    rfl
  rw [hrewrite]
  rw [trajectoryLaw_marginal]
  rw [processLaw_eq_product]
  rw [Measure.map_fst_prod, measure_univ, one_smul]
  exact map_spatialCount_spatialLaw a ha hm fallback t

/-! ## Reward from the same demand coordinate used by the update -/

/-- Evaluation at a measurably selected finite label is measurable. -/
theorem spatialLookup_measurable :
    Measurable (fun p : SpatialState m × Fin m => p.1 p.2) := by
  have hswap :
      Measurable (fun p : Fin m × SpatialState m => p.2 p.1) := by
    apply measurable_from_prod_countable_right
    intro j
    exact measurable_pi_apply j
  exact hswap.comp measurable_swap

/-- The actual matching cost paid at one joint process state. -/
def processCost (L : ℕ) (a : ℝ) (fallback : Fin m)
    (z : ProcessState m) : ℝ :=
  Dynamics.actualStepCost a (toConfiguration L z.1)
    fallback (z.2.1 : ℝ)

theorem processCost_measurable
    (L : ℕ) (a : ℝ) (fallback : Fin m) :
    Measurable (processCost L a fallback) := by
  have hlabel :
      Measurable (fun z : ProcessState m =>
        spatialSelectedLabel L a fallback z.1 z.2.1) :=
    (spatialSelectedLabel_measurable L a fallback).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hpoint :
      Measurable (fun z : ProcessState m =>
        (z.1 (spatialSelectedLabel L a fallback z.1 z.2.1) : ℝ)) :=
    measurable_subtype_coe.comp
      (spatialLookup_measurable.comp (measurable_fst.prodMk hlabel))
  have hdemand :
      Measurable (fun z : ProcessState m => (z.2.1 : ℝ)) :=
    measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)
  change Measurable (fun z : ProcessState m =>
    |(toConfiguration L z.1).location
        (Dynamics.selectedSupplyLabel
          a (toConfiguration L z.1) fallback (z.2.1 : ℝ)) -
      (z.2.1 : ℝ)|)
  simpa only [toConfiguration_location, spatialSelectedLabel, Pi.sub_apply] using
    (hpoint.sub hdemand).abs

theorem processCost_nonneg
    (L : ℕ) (a : ℝ) (fallback : Fin m) (z : ProcessState m) :
    0 ≤ processCost L a fallback z := by
  unfold processCost Dynamics.actualStepCost
  positivity

theorem processCost_le_one
    (L : ℕ) (a : ℝ) (fallback : Fin m) (z : ProcessState m) :
    processCost L a fallback z ≤ 1 := by
  unfold processCost Dynamics.actualStepCost
  have hs :=
    (toConfiguration L z.1).location_mem_unit
      (Dynamics.selectedSupplyLabel
        a (toConfiguration L z.1) fallback (z.2.1 : ℝ))
  have hu := z.2.1.property
  exact abs_le.2 ⟨by linarith [hs.1, hu.2], by linarith [hs.2, hu.1]⟩

/-- The process cost is integrable under every finite measure. -/
theorem processCost_integrable
    (L : ℕ) (a : ℝ) (fallback : Fin m)
    (μ : Measure (ProcessState m)) [IsFiniteMeasure μ] :
    Integrable (processCost L a fallback) μ := by
  apply Integrable.of_bound
    (processCost_measurable L a fallback).aestronglyMeasurable 1
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (processCost_nonneg L a fallback z)]
  exact processCost_le_one L a fallback z

/-- The squared matching cost paid at one joint process state. -/
def processSquaredCost (L : ℕ) (a : ℝ) (fallback : Fin m)
    (z : ProcessState m) : ℝ :=
  Dynamics.actualStepSquaredCost a (toConfiguration L z.1)
    fallback (z.2.1 : ℝ)

@[simp]
theorem processSquaredCost_eq_sq
    (L : ℕ) (a : ℝ) (fallback : Fin m) (z : ProcessState m) :
    processSquaredCost L a fallback z =
      processCost L a fallback z ^ 2 := by
  unfold processSquaredCost processCost Dynamics.actualStepSquaredCost
    Dynamics.actualStepCost
  rw [sq_abs]

theorem processSquaredCost_measurable
    (L : ℕ) (a : ℝ) (fallback : Fin m) :
    Measurable (processSquaredCost L a fallback) := by
  rw [show processSquaredCost L a fallback =
      fun z => processCost L a fallback z ^ 2 by
    funext z
    exact processSquaredCost_eq_sq L a fallback z]
  exact (processCost_measurable L a fallback).pow_const 2

theorem processSquaredCost_nonneg
    (L : ℕ) (a : ℝ) (fallback : Fin m) (z : ProcessState m) :
    0 ≤ processSquaredCost L a fallback z := by
  rw [processSquaredCost_eq_sq]
  positivity

theorem processSquaredCost_le_one
    (L : ℕ) (a : ℝ) (fallback : Fin m) (z : ProcessState m) :
    processSquaredCost L a fallback z ≤ 1 := by
  rw [processSquaredCost_eq_sq]
  nlinarith [processCost_nonneg L a fallback z,
    processCost_le_one L a fallback z]

/-- The squared process cost is integrable under every finite measure. -/
theorem processSquaredCost_integrable
    (L : ℕ) (a : ℝ) (fallback : Fin m)
    (μ : Measure (ProcessState m)) [IsFiniteMeasure μ] :
    Integrable (processSquaredCost L a fallback) μ := by
  apply Integrable.of_bound
    (processSquaredCost_measurable L a fallback).aestronglyMeasurable 1
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (processSquaredCost_nonneg L a fallback z)]
  exact processSquaredCost_le_one L a fallback z

/--
The reward and next inventory use the same current demand and replenishment
coordinates, pathwise.
-/
theorem processAdvance_configuration
    (L : ℕ) (a : ℝ) (fallback : Fin m)
    (z : ProcessState m) (fresh : Noise) :
    toConfiguration L (processAdvance L a fallback (z, fresh)).1 =
      Dynamics.actualStep a (toConfiguration L z.1) fallback
        (z.2.1 : ℝ) (z.2.2 : ℝ) z.2.2.property := by
  exact toConfiguration_spatialStep L a fallback z.1 z.2

/-- Integrating a fixed inventory over its current noise gives its actual configured cost. -/
theorem integral_processCost_noise
    (L : ℕ) (a : ℝ) (fallback : Fin m) (s : SpatialState m) :
    ∫ z : Noise, processCost L a fallback (s, z) ∂noiseLaw =
      (toConfiguration L s).expectedActualDistance
        (Dynamics.stateDyadicMass a (spatialCount L s))
        fallback := by
  let f : unitInterval → ℝ := fun u =>
    Dynamics.actualStepCost a (toConfiguration L s)
      fallback (u : ℝ)
  have hreal :
      (∫ u : ℝ,
          Dynamics.actualStepCost a (toConfiguration L s)
            fallback u ∂DyadicMass.uniformDemand) =
        ∫ u : unitInterval, f u ∂volume := by
    rw [← map_coe_volume]
    apply integral_map measurable_subtype_coe.aemeasurable
    exact
      (((toConfiguration L s).selectedSupplyPoint_measurable
        (Dynamics.stateDyadicMass a (spatialCount L s))
        fallback).sub measurable_id).abs.aestronglyMeasurable
  change
    (∫ z : Noise, f z.1 ∂noiseLaw) =
      (toConfiguration L s).expectedActualDistance
        (Dynamics.stateDyadicMass a (spatialCount L s))
        fallback
  calc
    (∫ z : Noise, f z.1 ∂noiseLaw) =
        ∫ z : unitInterval × unitInterval,
          f z.1 * (1 : ℝ) ∂(volume.prod volume) := by
      simp [noiseLaw]
    _ = (∫ u : unitInterval, f u ∂volume) *
          ∫ _v : unitInterval, (1 : ℝ) ∂volume := by
      exact integral_prod_mul f (fun _ : unitInterval => (1 : ℝ))
    _ = ∫ u : unitInterval, f u ∂volume := by simp
    _ = ∫ u : ℝ,
          Dynamics.actualStepCost a (toConfiguration L s)
            fallback u ∂DyadicMass.uniformDemand := hreal.symm
    _ = (toConfiguration L s).expectedActualDistance
          (Dynamics.stateDyadicMass a (spatialCount L s))
          fallback := by
      simpa [DyadicMass.uniformDemand] using
        (Dynamics.integral_actualStepCost_eq_expectedActualDistance
          a (toConfiguration L s) fallback)

/-- With the canonical fallback, the conditional reward is `actualConfigurationCost`. -/
theorem integral_processCost_noise_eq_actualConfigurationCost
    (L : ℕ) (a : ℝ) (hm : 0 < m) (s : SpatialState m) :
    (∫ z : Noise,
        processCost L a (SupplyConfiguration.canonicalFallback hm)
          (s, z) ∂noiseLaw) =
      Dynamics.actualConfigurationCost
        a hm (toConfiguration L s) := by
  simpa [Dynamics.actualConfigurationCost] using
    integral_processCost_noise
      L a (SupplyConfiguration.canonicalFallback hm) s

/-- Integrating the squared cost over current noise gives the configured
conditional second moment. -/
theorem integral_processSquaredCost_noise
    (L : ℕ) (a : ℝ) (fallback : Fin m) (s : SpatialState m) :
    ∫ z : Noise, processSquaredCost L a fallback (s, z) ∂noiseLaw =
      Transport.expectedActualSquaredDistance
        (toConfiguration L s)
        (Dynamics.stateDyadicMass a (spatialCount L s))
        fallback := by
  let f : unitInterval → ℝ := fun u =>
    Dynamics.actualStepSquaredCost a (toConfiguration L s)
      fallback (u : ℝ)
  have hreal :
      (∫ u : ℝ,
          Dynamics.actualStepSquaredCost a (toConfiguration L s)
            fallback u ∂DyadicMass.uniformDemand) =
        ∫ u : unitInterval, f u ∂volume := by
    rw [← map_coe_volume]
    apply integral_map measurable_subtype_coe.aemeasurable
    have hmeas :
        Measurable (fun u : ℝ =>
          ((toConfiguration L s).selectedSupplyPoint
              (Dynamics.stateDyadicMass a (spatialCount L s))
              fallback u - u) ^ 2) :=
      (((toConfiguration L s).selectedSupplyPoint_measurable
          (Dynamics.stateDyadicMass a (spatialCount L s))
          fallback).sub measurable_id).pow_const 2
    change AEStronglyMeasurable
      (fun u : ℝ =>
        ((toConfiguration L s).selectedSupplyPoint
            (Dynamics.stateDyadicMass a (spatialCount L s))
            fallback u - u) ^ 2) _
    exact hmeas.aestronglyMeasurable
  change
    (∫ z : Noise, f z.1 ∂noiseLaw) =
      Transport.expectedActualSquaredDistance
        (toConfiguration L s)
        (Dynamics.stateDyadicMass a (spatialCount L s))
        fallback
  calc
    (∫ z : Noise, f z.1 ∂noiseLaw) =
        ∫ z : unitInterval × unitInterval,
          f z.1 * (1 : ℝ) ∂(volume.prod volume) := by
      simp [noiseLaw]
    _ = (∫ u : unitInterval, f u ∂volume) *
          ∫ _v : unitInterval, (1 : ℝ) ∂volume := by
      exact integral_prod_mul f (fun _ : unitInterval => (1 : ℝ))
    _ = ∫ u : unitInterval, f u ∂volume := by simp
    _ = ∫ u : ℝ,
          Dynamics.actualStepSquaredCost a (toConfiguration L s)
            fallback u ∂DyadicMass.uniformDemand := hreal.symm
    _ = Transport.expectedActualSquaredDistance
          (toConfiguration L s)
          (Dynamics.stateDyadicMass a (spatialCount L s))
          fallback := by
      simpa [DyadicMass.uniformDemand] using
        (Dynamics.integral_actualStepSquaredCost_eq_expected
          a (toConfiguration L s) fallback)

/-- With the canonical fallback, the conditional squared reward is
`actualConfigurationSquaredCost`. -/
theorem integral_processSquaredCost_noise_eq_actualConfigurationSquaredCost
    (L : ℕ) (a : ℝ) (hm : 0 < m) (s : SpatialState m) :
    (∫ z : Noise,
        processSquaredCost L a (SupplyConfiguration.canonicalFallback hm)
          (s, z) ∂noiseLaw) =
      Dynamics.actualConfigurationSquaredCost
        a hm (toConfiguration L s) := by
  simpa [Dynamics.actualConfigurationSquaredCost] using
    integral_processSquaredCost_noise
      L a (SupplyConfiguration.canonicalFallback hm) s

/-- The configured-cost observable is integrable under every spatial marginal. -/
theorem actualConfigurationCost_spatial_integrable
    (a : ℝ) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    Integrable
      (fun s : SpatialState m =>
        Dynamics.actualConfigurationCost
          a hm (toConfiguration L s))
      (spatialLaw (L := L) a fallback t) := by
  have hprod :
      Integrable
        (processCost L a (SupplyConfiguration.canonicalFallback hm))
        ((spatialLaw (L := L) a fallback t).prod noiseLaw) :=
    processCost_integrable L a
      (SupplyConfiguration.canonicalFallback hm) _
  have hinter := hprod.integral_prod_left
  simpa only [integral_processCost_noise_eq_actualConfigurationCost]
    using hinter

/-- Expected joint-state reward equals expected configured inventory cost. -/
theorem integral_processCost_processLaw
    (a : ℝ) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    (∫ z : ProcessState m,
        processCost L a (SupplyConfiguration.canonicalFallback hm) z
          ∂processLaw (L := L) a fallback t) =
      ∫ s : SpatialState m,
        Dynamics.actualConfigurationCost
          a hm (toConfiguration L s)
          ∂spatialLaw (L := L) a fallback t := by
  rw [processLaw_eq_product]
  have hprod :
      Integrable
        (processCost L a (SupplyConfiguration.canonicalFallback hm))
        ((spatialLaw (L := L) a fallback t).prod noiseLaw) :=
    processCost_integrable L a
      (SupplyConfiguration.canonicalFallback hm) _
  rw [integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards with s
  exact integral_processCost_noise_eq_actualConfigurationCost L a hm s

/-- One-period reward, integrated on the single infinite trajectory law. -/
def trajectoryExpectedCost
    (a : ℝ) (hm : 0 < m) (fallback : Fin m) (t : ℕ) : ℝ :=
  ∫ path : ℕ → ProcessState m,
    processCost L a (SupplyConfiguration.canonicalFallback hm) (path t)
      ∂trajectoryLaw (L := L) a fallback

/-- The path-coordinate reward is the corresponding spatial marginal cost. -/
theorem trajectoryExpectedCost_eq_spatial
    (a : ℝ) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    trajectoryExpectedCost (L := L) a hm fallback t =
      ∫ s : SpatialState m,
        Dynamics.actualConfigurationCost
          a hm (toConfiguration L s)
          ∂spatialLaw (L := L) a fallback t := by
  unfold trajectoryExpectedCost
  calc
    (∫ path : ℕ → ProcessState m,
        processCost L a (SupplyConfiguration.canonicalFallback hm) (path t)
          ∂trajectoryLaw (L := L) a fallback) =
        ∫ z : ProcessState m,
          processCost L a (SupplyConfiguration.canonicalFallback hm) z
            ∂Measure.map (fun path : ℕ → ProcessState m => path t)
              (trajectoryLaw (L := L) a fallback) := by
      symm
      exact integral_map (measurable_pi_apply t).aemeasurable
        (processCost_measurable L a
          (SupplyConfiguration.canonicalFallback hm)).aestronglyMeasurable
    _ = ∫ z : ProcessState m,
          processCost L a (SupplyConfiguration.canonicalFallback hm) z
            ∂processLaw (L := L) a fallback t := by
      rw [trajectoryLaw_marginal]
    _ = ∫ s : SpatialState m,
          Dynamics.actualConfigurationCost
            a hm (toConfiguration L s)
            ∂spatialLaw (L := L) a fallback t :=
      integral_processCost_processLaw a hm fallback t

/-- The configured squared-cost observable is integrable under every spatial
marginal. -/
theorem actualConfigurationSquaredCost_spatial_integrable
    (a : ℝ) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    Integrable
      (fun s : SpatialState m =>
        Dynamics.actualConfigurationSquaredCost
          a hm (toConfiguration L s))
      (spatialLaw (L := L) a fallback t) := by
  have hprod :
      Integrable
        (processSquaredCost L a
          (SupplyConfiguration.canonicalFallback hm))
        ((spatialLaw (L := L) a fallback t).prod noiseLaw) :=
    processSquaredCost_integrable L a
      (SupplyConfiguration.canonicalFallback hm) _
  have hinter := hprod.integral_prod_left
  simpa only [
    integral_processSquaredCost_noise_eq_actualConfigurationSquaredCost]
    using hinter

/-- Expected joint-state squared reward equals expected configured squared
inventory cost. -/
theorem integral_processSquaredCost_processLaw
    (a : ℝ) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    (∫ z : ProcessState m,
        processSquaredCost L a
          (SupplyConfiguration.canonicalFallback hm) z
          ∂processLaw (L := L) a fallback t) =
      ∫ s : SpatialState m,
        Dynamics.actualConfigurationSquaredCost
          a hm (toConfiguration L s)
          ∂spatialLaw (L := L) a fallback t := by
  rw [processLaw_eq_product]
  have hprod :
      Integrable
        (processSquaredCost L a
          (SupplyConfiguration.canonicalFallback hm))
        ((spatialLaw (L := L) a fallback t).prod noiseLaw) :=
    processSquaredCost_integrable L a
      (SupplyConfiguration.canonicalFallback hm) _
  rw [integral_prod _ hprod]
  apply integral_congr_ae
  filter_upwards with s
  exact
    integral_processSquaredCost_noise_eq_actualConfigurationSquaredCost
      L a hm s

/-- One-period squared reward, integrated on the single infinite trajectory
law. -/
def trajectoryExpectedSquaredCost
    (a : ℝ) (hm : 0 < m) (fallback : Fin m) (t : ℕ) : ℝ :=
  ∫ path : ℕ → ProcessState m,
    processSquaredCost L a
      (SupplyConfiguration.canonicalFallback hm) (path t)
      ∂trajectoryLaw (L := L) a fallback

/-- The path-coordinate squared reward is the corresponding spatial marginal
cost. -/
theorem trajectoryExpectedSquaredCost_eq_spatial
    (a : ℝ) (hm : 0 < m)
    (fallback : Fin m) (t : ℕ) :
    trajectoryExpectedSquaredCost (L := L) a hm fallback t =
      ∫ s : SpatialState m,
        Dynamics.actualConfigurationSquaredCost
          a hm (toConfiguration L s)
          ∂spatialLaw (L := L) a fallback t := by
  unfold trajectoryExpectedSquaredCost
  calc
    (∫ path : ℕ → ProcessState m,
        processSquaredCost L a
          (SupplyConfiguration.canonicalFallback hm) (path t)
          ∂trajectoryLaw (L := L) a fallback) =
        ∫ z : ProcessState m,
          processSquaredCost L a
            (SupplyConfiguration.canonicalFallback hm) z
            ∂Measure.map (fun path : ℕ → ProcessState m => path t)
              (trajectoryLaw (L := L) a fallback) := by
      symm
      exact integral_map (measurable_pi_apply t).aemeasurable
        (processSquaredCost_measurable L a
          (SupplyConfiguration.canonicalFallback hm)).aestronglyMeasurable
    _ = ∫ z : ProcessState m,
          processSquaredCost L a
            (SupplyConfiguration.canonicalFallback hm) z
            ∂processLaw (L := L) a fallback t := by
      rw [trajectoryLaw_marginal]
    _ = ∫ s : SpatialState m,
          Dynamics.actualConfigurationSquaredCost
            a hm (toConfiguration L s)
            ∂spatialLaw (L := L) a fallback t :=
      integral_processSquaredCost_processLaw a hm fallback t

end V5.ContinuousProcess

end

end FD1D
