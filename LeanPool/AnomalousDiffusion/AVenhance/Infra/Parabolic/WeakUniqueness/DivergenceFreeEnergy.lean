/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.ZeroDataEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.PeriodicCutoff
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinGenerator
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsDivFree

/-!
# Divergence-free transport cancellation and the weak energy identity

The compact cutoff from `Infra.Heat.PeriodicCutoff` turns distributional divergence-free tests
on the plane into periodic tests on the torus. Fourier approximation then extends the cancellation
to the periodic `H¹` carrier.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Parabolic.WeakUniqueness

open AVenhance.Infra.Heat
open AVenhance.Infra.Torus
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Classical

local instance divFreeEnergyFiniteUnitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  unfold AVenhance.unitCube
  rw [Measure.restrict_apply_univ, volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance divFreeEnergyFiniteUnitCell :
    IsFiniteMeasure (volume.restrict (AVenhance.Infra.Torus.unitCell 2)) := by
  rw [Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube]
  infer_instance

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance divFreeEnergyMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance divFreeEnergyIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance divFreeEnergyProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance divFreeEnergyProbabilityTorus : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

/-- Closed symmetric unit box used for the divergence-free energy cutoff. -/
def DivergenceFreeEnergy.divFreeClosedBox : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-1 : ℝ) 1)

theorem DivergenceFreeEnergy.divFreeClosedBox_compact : IsCompact
    DivergenceFreeEnergy.divFreeClosedBox := by
  simpa [DivergenceFreeEnergy.divFreeClosedBox] using
    (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)

theorem DivergenceFreeEnergy.divFreeTile_subset_closedBox (b : Bool × Bool) :
    heatPeriodicTile b ⊆ DivergenceFreeEnergy.divFreeClosedBox := by
  intro x hx
  change x ∈ unitCellAt 2 (heatPeriodicTileStart b) at hx
  change ∀ j : Fin 2, x j ∈ Set.Ioc (heatPeriodicTileStart b j)
    (heatPeriodicTileStart b j + 1) at hx
  change ∀ j ∈ (Set.univ : Set (Fin 2)), x j ∈ Set.Icc (-1 : ℝ) 1
  intro i _hi
  have hi := hx i
  fin_cases i <;> rcases b with ⟨b₀, b₁⟩ <;>
    cases b₀ <;> cases b₁ <;>
      simp [heatPeriodicTileStart, heatPeriodicTileShift, intVector] at hi ⊢ <;>
        constructor <;> linarith

theorem DivergenceFreeEnergy.divFree_continuous_bound_on_box {F : Vec 2 → ℝ}
    (hF : Continuous F) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ DivergenceFreeEnergy.divFreeClosedBox, ‖F x‖ ≤ M := by
  have hbounded : Bornology.IsBounded (F '' DivergenceFreeEnergy.divFreeClosedBox) :=
    DivergenceFreeEnergy.divFreeClosedBox_compact.image hF |>.isBounded
  obtain ⟨M, hM, hbound⟩ := hbounded.subset_ball_lt 0 0
  refine ⟨M, hM.le, ?_⟩
  intro x hx
  have h := hbound ⟨x, hx, rfl⟩
  have h' : ‖F x‖ < M := by simpa [Metric.mem_ball, dist_eq_norm] using h
  exact h'.le

theorem DivergenceFreeEnergy.divFree_tile_volume_lt_top (b : Bool × Bool) :
    volume (heatPeriodicTile b) < ⊤ := by
  calc
    volume (heatPeriodicTile b) ≤ volume DivergenceFreeEnergy.divFreeClosedBox :=
      measure_mono (DivergenceFreeEnergy.divFreeTile_subset_closedBox b)
    _ < ⊤ := DivergenceFreeEnergy.divFreeClosedBox_compact.measure_lt_top

theorem DivergenceFreeEnergy.divFree_component_factor_integrable_on
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C)
    {F : Vec 2 → ℝ} (hF : Continuous F)
    (hFBound : ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ DivergenceFreeEnergy.divFreeClosedBox, ‖F x‖ ≤ M)
    {S : Set (Vec 2)} (hS : S ⊆ DivergenceFreeEnergy.divFreeClosedBox)
    (hSmeas : MeasurableSet S) (hSfinite : volume S < ⊤) (i : Fin 2) :
    IntegrableOn (fun x => b x i * F x) S := by
  obtain ⟨C, hC, hCb⟩ := hbBound
  obtain ⟨M, hM, hMb⟩ := hFBound
  have hmeas : AEStronglyMeasurable (fun x => b x i * F x) volume := by
    exact ((continuous_apply i).comp_aestronglyMeasurable hbMeas).mul
      hF.measurable.aestronglyMeasurable
  refine Measure.integrableOn_of_bounded (μ := volume)
    (s := S) (f := fun x => b x i * F x) (M := C * M)
    hSfinite.ne hmeas ?_
  filter_upwards [ae_restrict_mem hSmeas] with x hx
  calc
    ‖b x i * F x‖ = ‖b x i‖ * ‖F x‖ := norm_mul _ _
    _ ≤ C * M := mul_le_mul
      ((norm_le_pi_norm (b x) i).trans (hCb x)) (hMb x (hS hx))
      (norm_nonneg _) hC

theorem DivergenceFreeEnergy.divFree_component_factor_integrable_tile
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C)
    {F : Vec 2 → ℝ} (hF : Continuous F)
    (hFBound : ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ DivergenceFreeEnergy.divFreeClosedBox, ‖F x‖ ≤ M)
    (i : Fin 2) (tile : Bool × Bool) :
    IntegrableOn (fun x => b x i * F x) (heatPeriodicTile tile) := by
  apply DivergenceFreeEnergy.divFree_component_factor_integrable_on hbMeas hbBound hF hFBound
    (DivergenceFreeEnergy.divFreeTile_subset_closedBox tile)
    (measurableSet_unitCellAt 2 (heatPeriodicTileStart tile))
    (DivergenceFreeEnergy.divFree_tile_volume_lt_top tile) i

theorem DivergenceFreeEnergy.frozenPeriodic_to_heatPeriodic {F : Vec 2 → ℝ}
    (hF : AVenhance.IsZ2Periodic F) : IsZdPeriodic F := by
  exact (isZdPeriodic_iff_frozen F).2 hF

theorem isDivFree_integral_periodic_smooth_test
    {b : Vec 2 → Vec 2}
    (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C)
    (hbPeriodic : AVenhance.IsZ2Periodic b)
    (hDiv : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, Homogenization.vecDot (b x) (AVenhance.spaceGrad φ x) = 0)
    {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfPeriodic : AVenhance.IsZ2Periodic f) :
    ∫ x in unitCell 2, Homogenization.vecDot (b x)
      (AVenhance.spaceGrad f x) = 0 := by
  let χ : Vec 2 → ℝ := heatPeriodicCutoff2
  let test : Vec 2 → ℝ := χ * f
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := heatPeriodicCutoff2_contDiff
  have htest : ContDiff ℝ (⊤ : ℕ∞) test := by
    exact hχ.mul hf
  have htestCompact : HasCompactSupport test := by
    exact heatPeriodicCutoff2_hasCompactSupport.mul_right
  have htestDiv := hDiv test htest htestCompact
  have hgradTest (x : Vec 2) (i : Fin 2) :
      AVenhance.spaceGrad test x i =
        AVenhance.spaceGrad χ x i * f x + χ x * AVenhance.spaceGrad f x i := by
    change fderiv ℝ (χ * f) x (Homogenization.basisVec i) = _
    have hχdiff : DifferentiableAt ℝ χ x :=
      (hχ.contDiffAt).differentiableAt (by simp)
    have hfdiff : DifferentiableAt ℝ f x :=
      (hf.contDiffAt).differentiableAt (by simp)
    rw [fderiv_mul hχdiff hfdiff]
    simp only [add_apply, smul_apply, smul_eq_mul]
    simp only [AVenhance.spaceGrad]
    ring
  let main (i : Fin 2) : Vec 2 → ℝ := fun x => b x i * AVenhance.spaceGrad f x i
  let edge (i : Fin 2) : Vec 2 → ℝ := fun x => b x i * f x
  let dχ (i : Fin 2) : Vec 2 → ℝ := fun x => AVenhance.spaceGrad χ x i
  have hgradPeriodic (i : Fin 2) :
      AVenhance.IsZ2Periodic (fun x => AVenhance.spaceGrad f x i) :=
    AVenhance.Infra.Classical.periodic_spaceGrad_component hfPeriodic i
  have hmainPeriodic (i : Fin 2) :
      IsZdPeriodic (main i) := by
    apply DivergenceFreeEnergy.frozenPeriodic_to_heatPeriodic
    intro n x
    simp [main, hbPeriodic n x, hgradPeriodic i n x]
  have hedgePeriodic (i : Fin 2) : IsZdPeriodic (edge i) := by
    apply DivergenceFreeEnergy.frozenPeriodic_to_heatPeriodic
    intro n x
    simp [edge, hbPeriodic n x, hfPeriodic n x]
  have hgradFContinuous (i : Fin 2) :
      Continuous (fun x => AVenhance.spaceGrad f x i) := by
    change Continuous (fun x => fderiv ℝ f x (Homogenization.basisVec i))
    exact (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdχContinuous (i : Fin 2) : Continuous (dχ i) := by
    change Continuous (fun x => fderiv ℝ χ x (Homogenization.basisVec i))
    exact (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχFold (i : Fin 2) :
      ∫ x, main i x * χ x = ∫ x in unitCell 2, main i x := by
    exact integral_periodic_heatPeriodicCutoff2 (hmainPeriodic i)
      (fun tile => DivergenceFreeEnergy.divFree_component_factor_integrable_tile hbMeas hbBound
        (hgradFContinuous i) (DivergenceFreeEnergy.divFree_continuous_bound_on_box
            (hgradFContinuous i)) i tile)
  have hEdgeIntegrable (i : Fin 2) (tile : Bool × Bool) :
      IntegrableOn (fun x => edge i x * dχ i x) (heatPeriodicTile tile) := by
    have hfactor : Continuous (fun x => f x * dχ i x) := hf.continuous.mul (hdχContinuous i)
    exact (DivergenceFreeEnergy.divFree_component_factor_integrable_tile hbMeas hbBound hfactor
      (DivergenceFreeEnergy.divFree_continuous_bound_on_box hfactor) i tile).congr
        (Filter.Eventually.of_forall fun x => by
          simp only [edge, dχ]
          ring)
  have hsum (i : Fin 2) : ∀ x ∈ unitCell 2,
      ∑ tile : Bool × Bool, dχ i (x + heatPeriodicTileStart tile) = 0 := by
    intro x hx
    simpa [dχ, AVenhance.spaceGrad, heatPeriodicTileStart, Pi.add_apply] using
      (sum_heatPeriodicCutoff2_coordDeriv_translates i hx)
  have hEdgeFold (i : Fin 2) :
      ∫ x, edge i x * dχ i x = 0 := by
    have hfold := integral_periodic_weight2 (hedgePeriodic i)
      (heatPeriodicCutoff2_coordDeriv_support_subset_tiles i)
      (hEdgeIntegrable i) (by intro x hx; exact hsum i x hx)
    simpa [edge, dχ, AVenhance.spaceGrad] using hfold.2
  have hmainInt (i : Fin 2) : Integrable (fun x => main i x * χ x) volume := by
    let F : Vec 2 → ℝ := fun x => AVenhance.spaceGrad f x i * χ x
    have hF : Continuous F := (hgradFContinuous i).mul hχ.continuous
    have hlocal : IntegrableOn (fun x => b x i * F x) DivergenceFreeEnergy.divFreeClosedBox := by
      exact DivergenceFreeEnergy.divFree_component_factor_integrable_on hbMeas hbBound hF
        (DivergenceFreeEnergy.divFree_continuous_bound_on_box hF) (by intro x hx; exact hx)
        (by
          unfold DivergenceFreeEnergy.divFreeClosedBox
          exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
        DivergenceFreeEnergy.divFreeClosedBox_compact.measure_lt_top i
    have hsupport : Function.support (fun x => main i x * χ x) ⊆
        DivergenceFreeEnergy.divFreeClosedBox := by
      intro x hx
      have hχx : χ x ≠ 0 := by
        intro hz
        apply hx
        simp [hz]
      obtain ⟨tile, htile⟩ := Set.mem_iUnion.mp
        (heatPeriodicCutoff2_support_subset_tiles (by simpa [χ] using hχx))
      exact DivergenceFreeEnergy.divFreeTile_subset_closedBox tile htile
    have hlocal' : IntegrableOn (fun x => main i x * χ x) DivergenceFreeEnergy.divFreeClosedBox :=
        by
      convert hlocal using 1
      ext x
      simp [F, main]
      ring
    exact (integrableOn_iff_integrable_of_support_subset hsupport).mp hlocal'
  have hEdgeInt (i : Fin 2) : Integrable (fun x => edge i x * dχ i x) volume :=
      (integral_periodic_weight2 (hedgePeriodic i)
      (heatPeriodicCutoff2_coordDeriv_support_subset_tiles i)
      (hEdgeIntegrable i) (by intro x hx; exact hsum i x hx)).1
  have htermInt (i : Fin 2) : Integrable
      (fun x => main i x * χ x + edge i x * dχ i x) volume :=
    (hmainInt i).add (hEdgeInt i)
  have hsumInt : Integrable
      (fun x => ∑ i : Fin 2, (main i x * χ x + edge i x * dχ i x)) volume :=
    integrable_finsetSum Finset.univ (fun i hi => htermInt i)
  have hpoint (x : Vec 2) :
      Homogenization.vecDot (b x) (AVenhance.spaceGrad test x) =
        ∑ i : Fin 2, (main i x * χ x + edge i x * dχ i x) := by
    simp [Homogenization.vecDot, Fin.sum_univ_two, main, edge, dχ,
      hgradTest x, mul_add]
    ring
  have hsumIntegral :
      (∫ x, Homogenization.vecDot (b x) (AVenhance.spaceGrad test x)) =
        ∑ i : Fin 2,
          ((∫ x, main i x * χ x) + ∫ x, edge i x * dχ i x) := by
    calc
      _ = ∫ x, ∑ i : Fin 2, (main i x * χ x + edge i x * dχ i x) := by
        apply integral_congr_ae
        filter_upwards with x
        exact hpoint x
      _ = ∑ i : Fin 2, ∫ x, (main i x * χ x + edge i x * dχ i x) :=
        integral_finsetSum Finset.univ (fun i hi => htermInt i)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        exact integral_add (hmainInt i) (hEdgeInt i)
  have hcellDot :
      (∫ x in unitCell 2, Homogenization.vecDot (b x)
        (AVenhance.spaceGrad f x)) =
        ∑ i : Fin 2, ∫ x in unitCell 2, main i x := by
    rw [show (fun x => Homogenization.vecDot (b x) (AVenhance.spaceGrad f x)) =
      fun x => ∑ i : Fin 2, main i x by
        funext x
        simp [Homogenization.vecDot, main]]
    calc
      _ = ∫ x in unitCell 2, ∑ i : Fin 2, main i x := by
        apply setIntegral_congr_fun (measurableSet_unitCell 2)
        intro x hx
        simp [main]
      _ = ∑ i : Fin 2, ∫ x in unitCell 2, main i x := by
        apply integral_finsetSum Finset.univ
        intro i hi
        have hcell : IntegrableOn (main i) (unitCell 2) := by
          simpa [main, heatPeriodicTile, heatPeriodicTileStart,
            heatPeriodicTileShift, intVector, AVenhance.Infra.Torus.unitCell,
            AVenhance.Infra.Torus.unitCellAt] using
            DivergenceFreeEnergy.divFree_component_factor_integrable_tile hbMeas hbBound
              (hgradFContinuous i) (DivergenceFreeEnergy.divFree_continuous_bound_on_box
                  (hgradFContinuous i))
              i (true, true)
        exact hcell
  have hsumFold :
      (∫ x, Homogenization.vecDot (b x) (AVenhance.spaceGrad test x)) =
        ∫ x in unitCell 2, Homogenization.vecDot (b x) (AVenhance.spaceGrad f x) := by
    rw [hsumIntegral]
    simp_rw [hχFold, hEdgeFold]
    simpa using hcellDot.symm
  rw [htestDiv] at hsumFold
  exact hsumFold.symm

theorem DivergenceFreeEnergy.divFree_torusInner_cell {f g : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) (hg : MemL2On AVenhance.unitCube g) :
    inner ℝ
        ((weakProjection_realCellToTorus_memLp hf).toLp
          (AVenhance.Infra.Torus.periodicToTorus f))
        ((weakProjection_realCellToTorus_memLp hg).toLp
          (AVenhance.Infra.Torus.periodicToTorus g)) =
      ∫ x in unitCell 2, f x * g x := by
  rw [MeasureTheory.L2.inner_def]
  calc
    ∫ z : Torus,
        inner ℝ
          (((weakProjection_realCellToTorus_memLp hf).toLp
            (AVenhance.Infra.Torus.periodicToTorus f)) z)
          (((weakProjection_realCellToTorus_memLp hg).toLp
            (AVenhance.Infra.Torus.periodicToTorus g)) z) =
      ∫ z : Torus,
        ((weakProjection_realCellToTorus_memLp hf).toLp
          (AVenhance.Infra.Torus.periodicToTorus f)) z *
        ((weakProjection_realCellToTorus_memLp hg).toLp
          (AVenhance.Infra.Torus.periodicToTorus g)) z := by
          apply integral_congr_ae
          filter_upwards with z
          simp [mul_comm]
    _ =
      ∫ z : Torus, AVenhance.Infra.Torus.periodicToTorus
        (fun x => f x * g x) z := by
          apply integral_congr_ae
          filter_upwards [
            (weakProjection_realCellToTorus_memLp hf).coeFn_toLp,
            (weakProjection_realCellToTorus_memLp hg).coeFn_toLp] with z hfz hgz
          rw [hfz, hgz]
          rfl
    _ = ∫ x in unitCell 2, f x * g x :=
      integral_periodicToTorus_eq_unitCell _

theorem DivergenceFreeEnergy.divFree_unitCube_measurable :
    MeasurableSet AVenhance.unitCube := by
  unfold AVenhance.unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem DivergenceFreeEnergy.divFree_component_memLp_top_cell
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (i : Fin 2) :
    MemLp (fun x => b x i) ⊤ (volume.restrict AVenhance.unitCube) := by
  obtain ⟨C, hC, hCb⟩ := hbBound
  have hbiMeas : AEStronglyMeasurable (fun x => b x i)
      (volume.restrict AVenhance.unitCube) := by
    exact (continuous_apply i).comp_aestronglyMeasurable
      (hbMeas.mono_measure Measure.restrict_le_self)
  apply MemLp.of_bound hbiMeas C
  filter_upwards [ae_restrict_mem DivergenceFreeEnergy.divFree_unitCube_measurable] with x hx
  have hcoord : ‖b x i‖ ≤ ‖b x‖ := norm_le_pi_norm (b x) i
  exact hcoord.trans (hCb x)

theorem DivergenceFreeEnergy.divFree_periodicComponent_memLp_top_torus
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (i : Fin 2) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus (fun x => b x i)) ⊤ volume := by
  obtain ⟨C, hC, hCb⟩ := hbBound
  have hbBound' : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C := ⟨C, hC, hCb⟩
  have hcell : MemL2On AVenhance.unitCube (fun x => b x i) :=
    (DivergenceFreeEnergy.divFree_component_memLp_top_cell hbMeas hbBound' i).mono_exponent (by
        norm_num)
  have htor := weakProjection_realCellToTorus_memLp hcell
  apply MemLp.of_bound htor.aestronglyMeasurable C
  filter_upwards with z
  have hcoord : ‖b (AVenhance.Infra.Torus.unitTorusRepresentative 2 z) i‖ ≤
      ‖b (AVenhance.Infra.Torus.unitTorusRepresentative 2 z)‖ :=
    norm_le_pi_norm _ _
  have hbound := hcoord.trans (hCb _)
  simpa [AVenhance.Infra.Torus.periodicToTorus, Real.norm_eq_abs] using hbound

theorem DivergenceFreeEnergy.divFree_torus_product_memLp_two
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C)
    {g : Vec 2 → ℝ} (hg : MemL2On AVenhance.unitCube g) (i : Fin 2) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus (fun x => b x i * g x)) 2 volume := by
  have hbi := DivergenceFreeEnergy.divFree_component_memLp_top_cell hbMeas hbBound i
  have hprod : MemLp (fun x => b x i * g x) 2
      (volume.restrict AVenhance.unitCube) := hbi.mul hg
  exact weakProjection_realCellToTorus_memLp hprod

theorem DivergenceFreeEnergy.divFree_cell_pairing_tendsto
    {F : ℕ → Vec 2 → ℝ} {f g : Vec 2 → ℝ}
    (hFN : ∀ N, MemL2On AVenhance.unitCube (F N))
    (hf : MemL2On AVenhance.unitCube f) (hg : MemL2On AVenhance.unitCube g)
    (hconv : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hFN N)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (F N))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp hf).toLp
        (AVenhance.Infra.Torus.periodicToTorus f)))) :
    Tendsto (fun N => ∫ x in unitCell 2, F N x * g x) atTop
      (𝓝 (∫ x in unitCell 2, f x * g x)) := by
  let TF : ℕ → ScalarTorusL2 := fun N =>
    (weakProjection_realCellToTorus_memLp (hFN N)).toLp
      (AVenhance.Infra.Torus.periodicToTorus (F N))
  let Tf : ScalarTorusL2 := (weakProjection_realCellToTorus_memLp hf).toLp
    (AVenhance.Infra.Torus.periodicToTorus f)
  let Tg : ScalarTorusL2 := (weakProjection_realCellToTorus_memLp hg).toLp
    (AVenhance.Infra.Torus.periodicToTorus g)
  have hpair : Tendsto (fun N => inner ℝ (TF N) Tg) atTop
      (𝓝 (inner ℝ Tf Tg)) := by
    have hcont : Continuous (fun p : ScalarTorusL2 × ScalarTorusL2 =>
        inner ℝ p.1 p.2) := continuous_inner
    have hcontTendsto := hcont.tendsto (Tf, Tg)
    have hprod : Tendsto (fun N => (TF N, Tg)) atTop (𝓝 (Tf, Tg)) := by
      exact hconv.prodMk_nhds tendsto_const_nhds
    simpa only [Function.comp_def] using hcontTendsto.comp hprod
  have hpair' : Tendsto (fun N => ∫ x in unitCell 2, F N x * g x) atTop
      (𝓝 (inner ℝ Tf Tg)) := by
    exact hpair.congr' (Filter.Eventually.of_forall fun N =>
      DivergenceFreeEnergy.divFree_torusInner_cell (hFN N) hg)
  rw [← DivergenceFreeEnergy.divFree_torusInner_cell hf hg]
  exact hpair'

private theorem divFree_static_h1_cancellation_finite1 :
  ∀ {b : Vec (2 : ℕ) → Vec (2 : ℕ)}, (∀ (f : Vec (2 : ℕ) → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop
    ℕ∞) f → IsZ2Periodic f → ∫ (x : Vec (2 : ℕ)) in unitCell (2 : ℕ), Homogenization.vecDot (b
    x) (spaceGrad f x) = (0 : ℝ)) → ∀ {u : Vec (2 : ℕ) → ℝ},
  let upath : ℝ → Vec (2 : ℕ) → ℝ := fun (_ : ℝ) => u;
  let P : ℕ → Vec (2 : ℕ) → ℝ := fun (N : ℕ) => weakFourierModeProjection N upath (0 : ℝ);
  let Bcoord : Fin (2 : ℕ) → Vec (2 : ℕ) → ℝ := fun (i : Fin (2 : ℕ)) (x : Vec (2 : ℕ)) => b x
    i;
  let GradP : ℕ → Fin (2 : ℕ) → Vec (2 : ℕ) → ℝ := fun (N : ℕ) (i : Fin (2 : ℕ)) (x : Vec (2 :
    ℕ)) => spaceGrad (P N) x i;
  (∀ (N : ℕ), ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) (P N)) → (∀ (N : ℕ), IsZ2Periodic (P N)) → (∀
    (N : ℕ), MemL2On unitCube (P N)) → (∀ (N : ℕ) (i : Fin (2 : ℕ)), MemL2On unitCube (GradP N
    i)) → (∀ (i : Fin (2 : ℕ)), MemLp (Bcoord i) ⊤ (volume.restrict unitCube)) → ∀ (N M : ℕ), (∑
    i : Fin (2 : ℕ), ∫ (x : Vec (2 : ℕ)) in unitCell (2 : ℕ), b x i * GradP N i x * P M x) + ∑ i
    : Fin (2 : ℕ), ∫ (x : Vec (2 : ℕ)) in unitCell (2 : ℕ), b x i * GradP M i x * P N x = (0 :
    ℝ)
    := by
  intro b hdiv u upath P Bcoord GradP hPCont hPPer hPmem hgradMem hbMem N M
  have hPdiff (x : Vec 2) (i : Fin 2) :
      AVenhance.spaceGrad (fun y => P N y * P M y) x i =
        GradP N i x * P M x + P N x * GradP M i x := by
    change fderiv ℝ (fun y => P N y * P M y) x
      (Homogenization.basisVec i) = _
    rw [fderiv_fun_mul
      ((hPCont N).contDiffAt.differentiableAt (by simp))
      ((hPCont M).contDiffAt.differentiableAt (by simp))]
    simp only [add_apply, smul_apply, smul_eq_mul]
    dsimp [GradP, AVenhance.spaceGrad]
    ring
  have htestCont : ContDiff ℝ (⊤ : ℕ∞) (fun x => P N x * P M x) :=
    (hPCont N).mul (hPCont M)
  have htestPer : AVenhance.IsZ2Periodic (fun x => P N x * P M x) := by
    intro k x
    simp [hPPer N k x, hPPer M k x]
  have hcancel := hdiv (fun x => P N x * P M x) htestCont htestPer
  have hterm (x : Vec 2) :
      Homogenization.vecDot (b x)
          (AVenhance.spaceGrad (fun y => P N y * P M y) x) =
        ∑ i : Fin 2,
          ((b x i * GradP N i x) * P M x +
            (b x i * GradP M i x) * P N x) := by
    simp [Homogenization.vecDot, Fin.sum_univ_two, hPdiff]
    ring
  have hBint (i : Fin 2) : Integrable
      (fun x => (b x i * GradP M i x) * P N x)
      (volume.restrict (unitCell 2)) := by
    have hfirst : MemLp (fun x => b x i * GradP M i x) 2
        (volume.restrict AVenhance.unitCube) := (hbMem i).mul (hgradMem M i)
    have hproduct : MemLp (fun x => (b x i * GradP M i x) * P N x) 1
        (volume.restrict AVenhance.unitCube) := hfirst.mul (hPmem N)
    have hproductCell : MemLp (fun x => (b x i * GradP M i x) * P N x) 1
        (volume.restrict (unitCell 2)) := by
      rw [Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube]
      exact hproduct
    exact hproductCell.integrable le_rfl
  have hAintCell (i : Fin 2) : Integrable
      (fun x => (b x i * GradP N i x) * P M x)
      (volume.restrict (unitCell 2)) := by
    have hfirst : MemLp (fun x => b x i * GradP N i x) 2
        (volume.restrict AVenhance.unitCube) := (hbMem i).mul (hgradMem N i)
    have hproduct : MemLp (fun x => (b x i * GradP N i x) * P M x) 1
        (volume.restrict AVenhance.unitCube) := hfirst.mul (hPmem M)
    have hproductCell : MemLp (fun x => (b x i * GradP N i x) * P M x) 1
        (volume.restrict (unitCell 2)) := by
      rw [Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube]
      exact hproduct
    exact hproductCell.integrable le_rfl
  have hsumInt : Integrable
      (fun x => ∑ i : Fin 2,
        ((b x i * GradP N i x) * P M x +
          (b x i * GradP M i x) * P N x))
      (volume.restrict (unitCell 2)) := by
    exact integrable_finsetSum Finset.univ (fun i hi =>
      (hAintCell i).add (hBint i))
  have hsumEq :
      (∫ x in unitCell 2, Homogenization.vecDot (b x)
        (AVenhance.spaceGrad (fun y => P N y * P M y) x)) =
      ((∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * GradP N i x) * P M x) +
       (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * GradP M i x) * P N x)) := by
    calc
      _ = ∫ x in unitCell 2, ∑ i : Fin 2,
          ((b x i * GradP N i x) * P M x +
            (b x i * GradP M i x) * P N x) := by
        apply setIntegral_congr_fun (measurableSet_unitCell 2)
        intro x hx
        exact hterm x
      _ = ∑ i : Fin 2, ∫ x in unitCell 2,
          ((b x i * GradP N i x) * P M x +
            (b x i * GradP M i x) * P N x) :=
        integral_finsetSum Finset.univ (fun i hi => (hAintCell i).add (hBint i))
      _ = _ := by
        calc
          _ = ∑ i : Fin 2,
              ((∫ x in unitCell 2, (b x i * GradP N i x) * P M x) +
                ∫ x in unitCell 2, (b x i * GradP M i x) * P N x) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact integral_add (hAintCell i) (hBint i)
          _ = _ := Finset.sum_add_distrib
  rw [hcancel] at hsumEq
  exact hsumEq.symm

theorem DivergenceFreeEnergy.divFree_static_h1_cancellation
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C)
    (hdiv : ∀ f : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      AVenhance.IsZ2Periodic f →
      ∫ x in unitCell 2, Homogenization.vecDot (b x)
        (AVenhance.spaceGrad f x) = 0)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : AVenhance.IsPeriodicH1With u Du) :
    ∫ x in unitCell 2,
      Homogenization.vecDot (b x) (Du x) * u x = 0 := by
  let upath : ℝ → Vec 2 → ℝ := fun _ => u
  let Dpath : ℝ → Vec 2 → Vec 2 := fun _ => Du
  let P (N : ℕ) : Vec 2 → ℝ := weakFourierModeProjection N upath 0
  let Bcoord (i : Fin 2) : Vec 2 → ℝ := fun x => b x i
  let GradP (N : ℕ) (i : Fin 2) : Vec 2 → ℝ :=
    fun x => AVenhance.spaceGrad (P N) x i
  let A (N : ℕ) : ℝ :=
    ∑ i : Fin 2, ∫ x in unitCell 2, (b x i * GradP N i x) * u x
  let B (N : ℕ) : ℝ :=
    ∑ i : Fin 2, ∫ x in unitCell 2, (b x i * Du x i) * P N x
  have hPCont (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (P N) := by
    have h := realFourierModeAmbientExpansion_contDiff N
      (weakFourierCoefficientPath N upath 0)
    have h' : ContDiff ℝ (⊤ : ℕ∞)
        (realFourierModeAmbientExpansion N (weakFourierCoefficientPath N upath 0)) :=
      h.of_le (m := (⊤ : ℕ∞)) (by simp)
    simpa [P, weakFourierModeProjection] using h'
  have hPPer (N : ℕ) : AVenhance.IsZ2Periodic (P N) := by
    change AVenhance.IsZ2Periodic
      (realFourierModeAmbientExpansion N (weakFourierCoefficientPath N upath 0))
    exact realFourierModeAmbientExpansion_periodic N _
  have hgradCont (N : ℕ) (i : Fin 2) :
      Continuous (GradP N i) := by
    change Continuous (fun x => fderiv ℝ (P N) x (Homogenization.basisVec i))
    exact (hPCont N).continuous_fderiv (by simp) |>.clm_apply continuous_const
  have hPmem (N : ℕ) : MemL2On AVenhance.unitCube (P N) :=
    weak_continuous_memL2On (hPCont N).continuous
  have hgradMem (N : ℕ) (i : Fin 2) :
      MemL2On AVenhance.unitCube (GradP N i) :=
    weak_continuous_memL2On (hgradCont N i)
  have huMem : MemL2On AVenhance.unitCube u := hu.2.2.1
  have hDuMem (i : Fin 2) : MemL2On AVenhance.unitCube (fun x => Du x i) :=
    hu.2.2.2.1 i
  have hbMem (i : Fin 2) :
      MemLp (Bcoord i) ⊤ (volume.restrict AVenhance.unitCube) :=
    DivergenceFreeEnergy.divFree_component_memLp_top_cell hbMeas hbBound i
  have huH1 : AVenhance.IsPeriodicH1With (upath 0) (Dpath 0) := by
    simpa [upath, Dpath] using hu
  have hprojVal : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hPmem N)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (P N))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp huMem).toLp
        (AVenhance.Infra.Torus.periodicToTorus u))) := by
    have h := weakFourierProjectionL2_tendsto (u := upath) (t := 0) huMem
    simpa [P, weakFourierProjectionL2_eq_expansionTransfer] using h
  have hprojGrad (i : Fin 2) : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hgradMem N i)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (GradP N i))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp (hDuMem i)).toLp
        (AVenhance.Infra.Torus.periodicToTorus (fun x => Du x i)))) := by
    have h := weakFourierProjectionGradientL2_tendsto huH1 i
    have h' : Tendsto (fun N => weakFourierProjectionGradientL2 N upath 0 i) atTop
        (𝓝 ((weakProjection_realCellToTorus_memLp (hDuMem i)).toLp
          (AVenhance.Infra.Torus.periodicToTorus (fun x => Du x i)))) := by
      simpa [weakFourierProjectionGradientL2] using h
    simpa [P, GradP, weakFourierProjectionGradientL2_eq_expansionTransfer] using h'
  have hPairFirst (i : Fin 2) : Tendsto (fun N =>
      ∫ x in unitCell 2, (b x i * GradP N i x) * u x) atTop
      (𝓝 (∫ x in unitCell 2, (b x i * Du x i) * u x)) := by
    have hcoeff : MemL2On AVenhance.unitCube (fun x => b x i * u x) :=
      (hbMem i).mul huMem
    have h := DivergenceFreeEnergy.divFree_cell_pairing_tendsto (fun N => hgradMem N i)
      (hDuMem i) hcoeff (hprojGrad i)
    simpa [GradP, mul_assoc, mul_comm, mul_left_comm] using h
  have hPairSecond (i : Fin 2) : Tendsto (fun N =>
      ∫ x in unitCell 2, (b x i * Du x i) * P N x) atTop
      (𝓝 (∫ x in unitCell 2, (b x i * Du x i) * u x)) := by
    have hcoeff : MemL2On AVenhance.unitCube (fun x => b x i * Du x i) :=
      (hbMem i).mul (hDuMem i)
    have h := DivergenceFreeEnergy.divFree_cell_pairing_tendsto (fun N => hPmem N) huMem hcoeff
        hprojVal
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hAconv (N : ℕ) : Tendsto (fun M =>
      ∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * GradP N i x) * P M x) atTop
      (𝓝 (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * GradP N i x) * u x)) := by
    apply tendsto_finsetSum
    intro i hi
    have hcoeff : MemL2On AVenhance.unitCube (fun x => b x i * GradP N i x) :=
      (hbMem i).mul (hgradMem N i)
    have h := DivergenceFreeEnergy.divFree_cell_pairing_tendsto (fun M => hPmem M) huMem hcoeff
        hprojVal
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  have hBconv (N : ℕ) : Tendsto (fun M =>
      ∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * GradP M i x) * P N x) atTop
      (𝓝 (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * Du x i) * P N x)) := by
    apply tendsto_finsetSum
    intro i hi
    have hcoeff : MemL2On AVenhance.unitCube (fun x => b x i * P N x) :=
      (hbMem i).mul (hPmem N)
    have h := DivergenceFreeEnergy.divFree_cell_pairing_tendsto (fun M => hgradMem M i)
      (hDuMem i) hcoeff (hprojGrad i)
    simpa [GradP, mul_assoc, mul_comm, mul_left_comm] using h
  have hfinite (N M : ℕ) :
      (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * GradP N i x) * P M x) +
      (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * GradP M i x) * P N x) = 0 := by
    exact @divFree_static_h1_cancellation_finite1 b hdiv u hPCont hPPer hPmem hgradMem hbMem N M
  have hMixed (N : ℕ) : A N + B N = 0 := by
    have hsumConv := (hAconv N).add (hBconv N)
    have hconst := hsumConv.congr' (Filter.Eventually.of_forall fun M => hfinite N M)
    have hzero : A N + B N = 0 := by
      exact tendsto_nhds_unique hconst tendsto_const_nhds
    simpa [A, B] using hzero
  have hAto : Tendsto A atTop
      (𝓝 (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * Du x i) * u x)) := by
    dsimp [A]
    apply tendsto_finsetSum
    intro i hi
    exact hPairFirst i
  have hBto : Tendsto B atTop
      (𝓝 (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * Du x i) * u x)) := by
    dsimp [B]
    apply tendsto_finsetSum
    intro i hi
    exact hPairSecond i
  have hfinal := hAto.add hBto
  have hconst := hfinal.congr' (Filter.Eventually.of_forall fun N => hMixed N)
  have htwice :
      (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * Du x i) * u x) +
      (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * Du x i) * u x) = 0 :=
    tendsto_nhds_unique hconst tendsto_const_nhds
  have hresult :
      (∫ x in unitCell 2, Homogenization.vecDot (b x) (Du x) * u x) =
        ∑ i : Fin 2, ∫ x in unitCell 2, (b x i * Du x i) * u x := by
    have hpoint (x : Vec 2) : Homogenization.vecDot (b x) (Du x) * u x =
        ∑ i : Fin 2, (b x i * Du x i) * u x := by
      simp [Homogenization.vecDot]
      ring
    calc
      _ = ∫ x in unitCell 2, ∑ i : Fin 2, (b x i * Du x i) * u x := by
        apply setIntegral_congr_fun (measurableSet_unitCell 2)
        intro x hx
        exact hpoint x
      _ = ∑ i : Fin 2, ∫ x in unitCell 2, (b x i * Du x i) * u x := by
        have hint (i : Fin 2) : Integrable
            (fun x => (b x i * Du x i) * u x)
            (volume.restrict (unitCell 2)) := by
          have hprod : MemLp (fun x => (b x i * Du x i) * u x) 1
              (volume.restrict AVenhance.unitCube) := by
            have hfirst : MemLp (fun x => b x i * Du x i) 2
                (volume.restrict AVenhance.unitCube) := (hbMem i).mul (hDuMem i)
            exact hfirst.mul huMem
          have hprodCell : MemLp (fun x => (b x i * Du x i) * u x) 1
              (volume.restrict (unitCell 2)) := by
            rw [Measure.restrict_congr_set AVenhance.Infra.Torus.unitCell_ae_eq_unitCube]
            exact hprod
          exact hprodCell.integrable le_rfl
        exact integral_finsetSum Finset.univ (fun i hi => hint i)
  rw [hresult]
  linarith

theorem DivergenceFreeEnergy.divFree_openCylinder_measure :
    (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec 2)))) =
      (volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (volume : Measure (Vec 2)) := by
  have h := Measure.restrict_prod_eq_prod_univ
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
    (s := Set.Ioo (0 : ℝ) 1)
  rw [← Measure.volume_eq_prod ℝ (Vec 2)] at h
  exact h.symm

/-- For a divergence-free periodic drift, the signed transport contribution in the weak energy
identity vanishes on every truncated time-space cell. The slice cancellation holds a.e. in time,
which is all the Fubini representation of the spacetime integral requires. -/
theorem weak_solution_divFree_drift_pairing_zero
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∫ p in weakEnergyRegion t,
      Homogenization.vecDot (b p.1 p.2) (D p.1 p.2) * u p.1 p.2 = 0 := by
  let drift : ℝ × Vec 2 → ℝ := fun p =>
    Homogenization.vecDot (b p.1 p.2) (D p.1 p.2)
  let value : ℝ × Vec 2 → ℝ := fun p => u p.1 p.2
  let pairing : ℝ → ℝ := fun s =>
    ∫ x in AVenhance.unitCube, drift (s, x) * value (s, x)
  have hdrift : MemLp drift 2 (volume.restrict AVenhance.timeCube) :=
    weakEnergy_drift_memLp_two hu hb_meas hb_bdd
  have hvalue : MemLp value 2 (volume.restrict AVenhance.timeCube) := hu.2.2.1
  have hproduct : Integrable (fun p => drift p * value p)
      (volume.restrict AVenhance.timeCube) :=
    weak_product_integrable_timeCube hdrift hvalue
  have hspaceMeas : AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => b p.1 p.2)
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (volume : Measure (Vec 2))) := by
    have hopen : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
        (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec 2)))) :=
      hb_meas.mono_measure (Measure.restrict_mono
        (Set.prod_mono Set.Ioo_subset_Icc_self (subset_rfl)) le_rfl)
    rw [← DivergenceFreeEnergy.divFree_openCylinder_measure]
    exact hopen
  have hslice := hspaceMeas.prodMk_left
  have hH1 := hu.2.2.2.2.1
  have hpairingZero : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)), pairing s = 0 := by
    filter_upwards [hslice, hH1, ae_restrict_mem measurableSet_Ioo]
      with s hbs hH1s hsOpen
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hsOpen.1, le_of_lt hsOpen.2⟩
    obtain ⟨C, hC⟩ := hb_bdd
    have hCnonneg : 0 ≤ C := le_trans (norm_nonneg (b s 0)) (hC s hs 0)
    have hBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b s x‖ ≤ C := ⟨C, hCnonneg, hC s hs⟩
    have hperiodic : AVenhance.IsZ2Periodic (b s) := hb_per s hs
    have hdivSmooth : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        AVenhance.IsZ2Periodic ψ →
        ∫ x in unitCell 2, Homogenization.vecDot (b s x)
          (AVenhance.spaceGrad ψ x) = 0 := by
      intro ψ hψ hψper
      exact isDivFree_integral_periodic_smooth_test hbs hBound hperiodic
        (fun φ hφ hcompact => hdiv s hs φ hφ hcompact) hψ hψper
    have hzero := DivergenceFreeEnergy.divFree_static_h1_cancellation hbs hBound hdivSmooth hH1s
    change (∫ x in unitCell 2,
      Homogenization.vecDot (b s x) (D s x) * u s x) = 0 at hzero
    rw [integral_unitCell_eq_unitCube] at hzero
    simpa [pairing, drift, value] using hzero
  have hregionZero : ∫ s in Set.Ioo (0 : ℝ) t, pairing s = 0 := by
    have hμ : volume.restrict (Set.Ioo (0 : ℝ) t) ≤
        volume.restrict (Set.Ioo (0 : ℝ) 1) :=
      Measure.restrict_mono (by
        intro s hs
        rcases hs with ⟨hs0, hst⟩
        exact ⟨hs0, lt_of_lt_of_le hst ht.2⟩) le_rfl
    have hzero : pairing =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) t)] 0 :=
      hpairingZero.filter_mono (MeasureTheory.ae_mono hμ)
    calc
      ∫ s in Set.Ioo (0 : ℝ) t, pairing s =
          ∫ s, pairing s ∂(volume.restrict (Set.Ioo (0 : ℝ) t)) := rfl
      _ = 0 := integral_eq_zero_of_ae hzero
  have htimeZero : ∫ s in (0 : ℝ)..t, pairing s = 0 := by
    rw [← weakEnergy_Ioo_intervalIntegral ht.1]
    exact hregionZero
  rw [weakEnergy_region_integral_eq_interval hproduct ht]
  simpa [pairing, drift, value] using htimeZero

/-- The signed weak energy identity reduces to the exact divergence-free energy identity on the
periodic class. -/
theorem weak_solution_divFree_energy_identity
    {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {D : ℝ → Vec 2 → Vec 2}
    (hu : AVenhance.IsWeakSolutionGrad b κ f u D)
    (hf : MemL2On AVenhance.unitCube f)
    (hb_meas : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2)
      (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)))
    (hb_bdd : ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖b t x‖ ≤ C)
    (hb_per : ∀ t ∈ Set.Icc (0 : ℝ) 1, AVenhance.IsZ2Periodic (b t))
    (hdiv : AVenhance.IsDivFree b) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      AVenhance.l2NormSq (u t) +
        2 * κ * (∫ p in Set.Ioo (0 : ℝ) t ×ˢ AVenhance.unitCube,
          Homogenization.vecNormSq (D p.1 p.2)) =
        AVenhance.l2NormSq f := by
  intro t ht
  have henergy := weak_solution_energy_identity hu hf hb_meas hb_bdd ht
  have hdrift := weak_solution_divFree_drift_pairing_zero
    hu hb_meas hb_bdd hb_per hdiv ht
  rw [hdrift] at henergy
  have hgrad :
      (∫ p in weakEnergyRegion t,
        Homogenization.vecDot (D p.1 p.2) (D p.1 p.2)) =
      ∫ p in weakEnergyRegion t, Homogenization.vecNormSq (D p.1 p.2) := by
    apply integral_congr_ae
    filter_upwards with p
    simp [Homogenization.vecNormSq]
  change AVenhance.l2NormSq (u t) +
      2 * κ * (∫ p in weakEnergyRegion t,
        Homogenization.vecNormSq (D p.1 p.2)) =
      AVenhance.l2NormSq f
  rw [← hgrad]
  nlinarith [henergy]

end AVenhance.Infra.Parabolic.WeakUniqueness

end
