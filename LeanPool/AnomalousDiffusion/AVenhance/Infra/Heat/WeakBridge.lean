/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FourierCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.ClassicalDerivative
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsPeriodicH1With
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Heat.Energy

/-! # Weak Bridge

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open AVenhance.Infra.Torus
open scoped ENNReal

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance heatWeakMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance heatWeakIsAddHaarUnitAddCircle : Measure.IsAddHaarMeasure (volume : Measure
    UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance heatWeakProbabilityUnitAddCircle : IsProbabilityMeasure (volume : Measure
    UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Heat

/-- The subtype carrier for the half-open unit fundamental cell. -/
abbrev HeatCell := {x : Vec 2 // x ∈ unitCell 2}

/-- Membership of the canonical cell transfer in torus `L²`. -/
theorem memLp_frozenCellTransfer {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) :
    MemLp (periodicToTorus (fun x => (f x : ℂ))) 2 volume := by
  have hcell : MemLp f 2 (volume.restrict (unitCell 2)) := by
    have hμ : (volume : Measure (Vec 2)).restrict (unitCell 2) =
        volume.restrict AVenhance.unitCube :=
      Measure.restrict_congr_set unitCell_ae_eq_unitCube
    rw [hμ]
    exact hf
  let μS : Measure HeatCell := volume.comap (Subtype.val : HeatCell → Vec 2)
  have hmpSub : MeasurePreserving (Subtype.val : HeatCell → Vec 2) μS
      (volume.restrict (unitCell 2)) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (measurableSet_unitCell 2) volume]
  have hsub : MemLp (fun x : HeatCell => (f x.1 : ℂ)) 2 μS := by
    exact hcell.ofReal.comp_measurePreserving hmpSub
  have hmp := UnitAddTorus.measurePreserving_equivPiIoc
    (fun _ : Fin 2 => (0 : ℝ))
  have hc := hsub.comp_measurePreserving hmp
  have heq : periodicToTorus (fun x => (f x : ℂ)) =
      (fun y => (fun x : HeatCell => (f x.1 : ℂ))
        (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ)) y)) := by
    funext y
    rfl
  rw [heq]
  exact hc

/-- Put a real function with the cell `L²` control into the torus `L²`
space by using its values on the canonical half-open cell. -/
noncomputable def frozenCellToTorusL2 {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) : TorusL2 2 :=
  (memLp_frozenCellTransfer hf).toLp
    (periodicToTorus (fun x => (f x : ℂ)))

/-- Coordinate `L²` transfer of the weak gradient. -/
noncomputable def frozenCellGradientToTorusL2 {Du : Vec 2 → Vec 2}
    (hDu : GradMemL2On AVenhance.unitCube Du) (i : Fin 2) : TorusL2 2 :=
  frozenCellToTorusL2 (hDu i)

/-- Scalar torus `L²` carrier associated to periodic `H¹` data. -/
noncomputable def frozenPeriodicH1ValueL2 {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) : TorusL2 2 :=
  frozenCellToTorusL2 h.2.2.1

/-- A coordinate of the weak gradient of periodic `H¹` data, transferred
to torus `L²`. -/
noncomputable def frozenPeriodicH1GradientL2 {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With u Du) (i : Fin 2) : TorusL2 2 :=
  frozenCellGradientToTorusL2 h.2.2.2.1 i

theorem WeakBridge.normSq_memLpToLp_eq_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (g : α → ℂ) (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 ∂μ := by
  let q : ℝ≥0∞ := ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ
  have hformula : eLpNorm g 2 μ = q ^ (1 / 2 : ℝ) := by
    dsimp [q]
    simpa using eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2 : ℝ≥0∞))
      (by norm_num) (by norm_num) hg.aestronglyMeasurable
  have hnorm : ‖hg.toLp g‖ = q.toReal ^ (1 / 2 : ℝ) := by
    rw [Lp.norm_toLp, hformula, ENNReal.toReal_rpow]
  rw [hnorm, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · symm
    calc
      ∫ x, ‖g x‖ ^ 2 ∂μ =
          (∫⁻ x, ENNReal.ofReal (‖g x‖ ^ 2) ∂μ).toReal := by
        apply integral_eq_lintegral_of_nonneg_ae
        · filter_upwards with x
          positivity
        · have hInt : Integrable (fun x => ‖g x‖ ^ (2 : ℕ)) μ := by
            have hbase := hg.integrable_norm_rpow (by norm_num) (by norm_num)
            convert hbase using 1
            norm_num [Real.rpow_natCast]
          exact hInt.aestronglyMeasurable
      _ = q.toReal := by
        congr 1
        apply lintegral_congr_ae
        filter_upwards with x
        simp [enorm]
  · exact ENNReal.toReal_nonneg

/-- The torus norm of the cell transfer is exactly its cell
`L²` integral. -/
theorem normSq_frozenCellToTorusL2_eq {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) :
    ‖frozenCellToTorusL2 hf‖ ^ 2 = AVenhance.l2NormSq f := by
  rw [frozenCellToTorusL2, WeakBridge.normSq_memLpToLp_eq_integral]
  calc
    ∫ y : UnitAddTorus (Fin 2),
        ‖periodicToTorus (fun x => (f x : ℂ)) y‖ ^ 2 =
      ∫ y : UnitAddTorus (Fin 2),
        periodicToTorus (fun x : Vec 2 => ‖(f x : ℂ)‖ ^ 2) y := by
          rfl
    _ = ∫ x in unitCell 2, ‖(f x : ℂ)‖ ^ 2 :=
      integral_periodicToTorus_eq_unitCell _
    _ = AVenhance.l2NormSq f := by
      rw [integral_unitCell_eq_unitCube]
      simp [AVenhance.l2NormSq, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- Fourier coefficients of the cell transfer are the usual complex
Fourier integrals over the unit cell. -/
theorem mFourierCoeff_frozenCellToTorusL2 {f : Vec 2 → ℝ}
    (hf : MemL2On AVenhance.unitCube f) (k : Frequency) :
    UnitAddTorus.mFourierCoeff (frozenCellToTorusL2 hf) k =
      ∫ x in unitCell 2, torusCharacter k x * (f x : ℂ) := by
  let g : UnitAddTorus (Fin 2) → ℂ := periodicToTorus (fun x => (f x : ℂ))
  have hg : MemLp g 2 volume := by
    simpa [g] using memLp_frozenCellTransfer hf
  calc
    UnitAddTorus.mFourierCoeff (frozenCellToTorusL2 hf) k =
        ∫ y : UnitAddTorus (Fin 2),
          UnitAddTorus.mFourier (-k) y *
            (frozenCellToTorusL2 hf : UnitAddTorus (Fin 2) → ℂ) y := by
      rfl
    _ = ∫ y : UnitAddTorus (Fin 2), UnitAddTorus.mFourier (-k) y * g y := by
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp] with y hy
      simp [g, frozenCellToTorusL2, hy]
    _ = ∫ y : UnitAddTorus (Fin 2),
          periodicToTorus (fun x : Vec 2 => torusCharacter k x * (f x : ℂ)) y := by
      apply integral_congr_ae
      filter_upwards with y
      change UnitAddTorus.mFourier (-k) y *
          (f (unitTorusRepresentative 2 y) : ℂ) =
        UnitAddTorus.mFourier (-k)
          (toUnitTorus 2 (unitTorusRepresentative 2 y)) *
          (f (unitTorusRepresentative 2 y) : ℂ)
      rw [toUnitTorus_unitTorusRepresentative]
    _ = ∫ x in unitCell 2, torusCharacter k x * (f x : ℂ) :=
      integral_periodicToTorus_eq_unitCell _

/-- The classical derivative bound from item 2, stated for the `IsPeriodicH1With` scalar carrier. -/
theorem norm_heatTorusSmoothLift_multiIndexDerivative_le_frozenH1
    {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (h : AVenhance.IsPeriodicH1With f Df) {s : ℝ} (hs : 0 < s)
    (α : Fin 2 → ℕ) :
    ‖ContinuousMap.toLp 2 volume ℂ
        (heatDerivativeTorusContinuous hs (frozenPeriodicH1ValueL2 h) α)‖ ≤
      (Nat.factorial (multiIndexDegree α) : ℝ) *
        (1 / Real.sqrt s) ^ multiIndexDegree α *
          Real.sqrt (AVenhance.l2NormSq f) := by
  have hnormSq : ‖frozenPeriodicH1ValueL2 h‖ ^ 2 = AVenhance.l2NormSq f := by
    exact normSq_frozenCellToTorusL2_eq h.2.2.1
  have hnorm : ‖frozenPeriodicH1ValueL2 h‖ = Real.sqrt (AVenhance.l2NormSq f) := by
    calc
      ‖frozenPeriodicH1ValueL2 h‖ =
          Real.sqrt (‖frozenPeriodicH1ValueL2 h‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = Real.sqrt (AVenhance.l2NormSq f) := congrArg Real.sqrt hnormSq
  rw [← hnorm]
  exact norm_heatTorusSmoothLift_multiIndexDerivative_le hs
    (frozenPeriodicH1ValueL2 h) α

end AVenhance.Infra.Heat
