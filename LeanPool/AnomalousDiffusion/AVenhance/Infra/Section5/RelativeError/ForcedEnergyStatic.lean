/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy

/-!
# Static divergence-free cancellation on periodic `H¹`

For a bounded measurable periodic field that is divergence free against smooth periodic tests, the
transport pairing `∫ b·Du u` vanishes for every periodic `H¹` function `u`. The proof is the
Fourier approximation argument of `Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy`, whose
corresponding statement is private there; it is reproduced here with a public name.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open Homogenization
open scoped Topology

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance.Infra.Heat
open AVenhance.Infra.Torus
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Classical
open AVenhance.Infra.Parabolic.WeakUniqueness

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

theorem ForcedEnergyStatic.divFree_torusInner_cell {f g : Vec 2 → ℝ}
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

theorem ForcedEnergyStatic.divFree_unitCube_measurable :
    MeasurableSet AVenhance.unitCube := by
  unfold AVenhance.unitCube
  exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)

theorem ForcedEnergyStatic.divFree_component_memLp_top_cell
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (i : Fin 2) :
    MemLp (fun x => b x i) ⊤ (volume.restrict AVenhance.unitCube) := by
  obtain ⟨C, hC, hCb⟩ := hbBound
  have hbiMeas : AEStronglyMeasurable (fun x => b x i)
      (volume.restrict AVenhance.unitCube) := by
    exact (continuous_apply i).comp_aestronglyMeasurable
      (hbMeas.mono_measure Measure.restrict_le_self)
  apply MemLp.of_bound hbiMeas C
  filter_upwards [ae_restrict_mem ForcedEnergyStatic.divFree_unitCube_measurable] with x hx
  have hcoord : ‖b x i‖ ≤ ‖b x‖ := norm_le_pi_norm (b x) i
  exact hcoord.trans (hCb x)

theorem ForcedEnergyStatic.divFree_periodicComponent_memLp_top_torus
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C) (i : Fin 2) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus (fun x => b x i)) ⊤ volume := by
  obtain ⟨C, hC, hCb⟩ := hbBound
  have hbBound' : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C := ⟨C, hC, hCb⟩
  have hcell : MemL2On AVenhance.unitCube (fun x => b x i) :=
    (ForcedEnergyStatic.divFree_component_memLp_top_cell hbMeas hbBound' i).mono_exponent (by
        norm_num)
  have htor := weakProjection_realCellToTorus_memLp hcell
  apply MemLp.of_bound htor.aestronglyMeasurable C
  filter_upwards with z
  have hcoord : ‖b (AVenhance.Infra.Torus.unitTorusRepresentative 2 z) i‖ ≤
      ‖b (AVenhance.Infra.Torus.unitTorusRepresentative 2 z)‖ :=
    norm_le_pi_norm _ _
  have hbound := hcoord.trans (hCb _)
  simpa [AVenhance.Infra.Torus.periodicToTorus, Real.norm_eq_abs] using hbound

theorem ForcedEnergyStatic.divFree_torus_product_memLp_two
    {b : Vec 2 → Vec 2} (hbMeas : AEStronglyMeasurable b volume)
    (hbBound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖b x‖ ≤ C)
    {g : Vec 2 → ℝ} (hg : MemL2On AVenhance.unitCube g) (i : Fin 2) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus (fun x => b x i * g x)) 2 volume := by
  have hbi := ForcedEnergyStatic.divFree_component_memLp_top_cell hbMeas hbBound i
  have hprod : MemLp (fun x => b x i * g x) 2
      (volume.restrict AVenhance.unitCube) := hbi.mul hg
  exact weakProjection_realCellToTorus_memLp hprod

theorem ForcedEnergyStatic.divFree_cell_pairing_tendsto
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
      ForcedEnergyStatic.divFree_torusInner_cell (hFN N) hg)
  rw [← ForcedEnergyStatic.divFree_torusInner_cell hf hg]
  exact hpair'

private theorem static_divFree_h1_cancellation_finite1 :
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

theorem static_divFree_h1_cancellation
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
    ForcedEnergyStatic.divFree_component_memLp_top_cell hbMeas hbBound i
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
    have h := ForcedEnergyStatic.divFree_cell_pairing_tendsto (fun N => hgradMem N i)
      (hDuMem i) hcoeff (hprojGrad i)
    simpa [GradP, mul_assoc, mul_comm, mul_left_comm] using h
  have hPairSecond (i : Fin 2) : Tendsto (fun N =>
      ∫ x in unitCell 2, (b x i * Du x i) * P N x) atTop
      (𝓝 (∫ x in unitCell 2, (b x i * Du x i) * u x)) := by
    have hcoeff : MemL2On AVenhance.unitCube (fun x => b x i * Du x i) :=
      (hbMem i).mul (hDuMem i)
    have h := ForcedEnergyStatic.divFree_cell_pairing_tendsto (fun N => hPmem N) huMem hcoeff
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
    have h := ForcedEnergyStatic.divFree_cell_pairing_tendsto (fun M => hPmem M) huMem hcoeff
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
    have h := ForcedEnergyStatic.divFree_cell_pairing_tendsto (fun M => hgradMem M i)
      (hDuMem i) hcoeff (hprojGrad i)
    simpa [GradP, mul_assoc, mul_comm, mul_left_comm] using h
  have hfinite (N M : ℕ) :
      (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * GradP N i x) * P M x) +
      (∑ i : Fin 2, ∫ x in unitCell 2,
        (b x i * GradP M i x) * P N x) = 0 := by
    exact @static_divFree_h1_cancellation_finite1 b hdiv u hPCont hPPer hPmem hgradMem hbMem N M
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

end AVenhance.Infra.Section5.RelativeError

end
