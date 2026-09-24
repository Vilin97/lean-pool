/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.CZUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.PressureDecayMeasurability
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore
public import LeanPool.CaffarelliKohnNirenberg.Setting.UTensor
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Setting.TimeHolder

/-!
# CZCylinder Bridge

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN
open CKN.Core.Step3

/-! The product-cylinder part of the solution-level bridge. -/

theorem eLpNorm'_cylinder_le_of_ae_slice_bound
    {P : Vec3 × ℝ → ℝ} {B : ℝ → ℝ≥0∞}
    {x₀ : Vec3} {t r q : ℝ} (_ : 0 < r) (hq : 0 < q)
    (hP : AEStronglyMeasurable P
      (volume.restrict (parabolicCylinder x₀ t r)))
    (hB : ∀ᵐ s ∂volume.restrict (Ioc (t - r ^ 2) t),
      MemLp (fun x : Vec3 => P (x, s)) (ENNReal.ofReal q) volume ∧
        eLpNorm (fun x : Vec3 => P (x, s)) (ENNReal.ofReal q) volume ≤ B s) :
    eLpNorm' P q (volume.restrict (parabolicCylinder x₀ t r)) ≤
      (∫⁻ s in Ioc (t - r ^ 2) t, B s ^ q) ^ (1 / q : ℝ) := by
  let μx : Measure Vec3 := volume.restrict (vec3Ball x₀ r)
  let μt : Measure ℝ := volume.restrict (Ioc (t - r ^ 2) t)
  have hμ : μx.prod μt = volume.restrict (parabolicCylinder x₀ t r) := by
    dsimp [μx, μt, parabolicCylinder]
    exact Measure.prod_restrict _ _
  have hPprod : AEStronglyMeasurable P (μx.prod μt) := by
    rw [hμ]
    exact hP
  have hF : AEMeasurable (fun z : Vec3 × ℝ => ‖P z‖ₑ ^ q) (μx.prod μt) :=
    hPprod.enorm.pow_const q
  have hswap : (∫⁻ z, ‖P z‖ₑ ^ q ∂(μx.prod μt)) =
      ∫⁻ s, ∫⁻ x, ‖P (x, s)‖ₑ ^ q ∂μx ∂μt := by
    calc
      (∫⁻ z, ‖P z‖ₑ ^ q ∂(μx.prod μt)) =
          ∫⁻ x, ∫⁻ s, ‖P (x, s)‖ₑ ^ q ∂μt ∂μx :=
        MeasureTheory.lintegral_prod _ hF
      _ = ∫⁻ s, ∫⁻ x, ‖P (x, s)‖ₑ ^ q ∂μx ∂μt :=
        MeasureTheory.lintegral_lintegral_swap
          (f := fun x s => ‖P (x, s)‖ₑ ^ q) hF
  have hinner : ∀ᵐ s ∂μt,
      (∫⁻ x, ‖P (x, s)‖ₑ ^ q ∂μx) ≤ B s ^ q := by
    filter_upwards [hB] with s hs
    rcases hs with ⟨hsMem, hsBound⟩
    have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
    have hqtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
    have hsNorm : eLpNorm (fun x : Vec3 => P (x, s))
        (ENNReal.ofReal q) volume =
        eLpNorm' (fun x : Vec3 => P (x, s)) q volume := by
      rw [eLpNorm_eq_eLpNorm' hq0 hqtop hsMem.aestronglyMeasurable]
      simp only [ENNReal.toReal_ofReal hq.le]
    have hsBall : eLpNorm' (fun x : Vec3 => P (x, s)) q μx ≤
        eLpNorm' (fun x : Vec3 => P (x, s)) q volume := by
      exact eLpNorm'_mono_measure _ Measure.restrict_le_self hq.le
    calc
      (∫⁻ x, ‖P (x, s)‖ₑ ^ q ∂μx) =
          eLpNorm' (fun x : Vec3 => P (x, s)) q μx ^ q :=
        lintegral_rpow_enorm_eq_rpow_eLpNorm' hq
      _ ≤ eLpNorm' (fun x : Vec3 => P (x, s)) q volume ^ q :=
        ENNReal.rpow_le_rpow hsBall hq.le
      _ = eLpNorm (fun x : Vec3 => P (x, s))
          (ENNReal.ofReal q) volume ^ q := by rw [hsNorm]
      _ ≤ B s ^ q := ENNReal.rpow_le_rpow hsBound hq.le
  have htotal : (∫⁻ z, ‖P z‖ₑ ^ q ∂(μx.prod μt)) ≤
      ∫⁻ s, B s ^ q ∂μt := by
    rw [hswap]
    exact lintegral_mono_ae hinner
  calc
    eLpNorm' P q (volume.restrict (parabolicCylinder x₀ t r)) =
        eLpNorm' P q (μx.prod μt) := by
      exact congrArg (fun m : Measure (Vec3 × ℝ) => eLpNorm' P q m) hμ.symm
    _ = (∫⁻ z, ‖P z‖ₑ ^ q ∂(μx.prod μt)) ^ (1 / q : ℝ) := by
      rw [eLpNorm'_eq_lintegral_enorm]
    _ ≤ (∫⁻ s, B s ^ q ∂μt) ^ (1 / q : ℝ) :=
      ENNReal.rpow_le_rpow htotal (by positivity)
    _ = (∫⁻ s in Ioc (t - r ^ 2) t, B s ^ q) ^ (1 / q : ℝ) := by
      rfl

/-! The temporal source estimate needed by the p₁ bridge.  Its right hand side
is the slice form of `eq:slice-norm-bounds`: the factor `9` is the concrete
`U`-tensor constant, and the numerical coefficient is fixed before the fields.
-/

theorem utensor_slice_scale_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    {C : ℝ} (hC : 0 ≤ C) :
    (∫⁻ s in Ioc (z.2 - r ^ 2) z.2,
      ENNReal.ofReal (C *
        (∫ y in vec3Ball z.1 ρ,
          (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) ^
            (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) ≤
      ENNReal.ofReal (C * (9 * sobolevPoincareL6Constant.toReal) *
        r ^ (1 / 3 : ℝ) * ρ * alpha u z ρ * beta u Du z ρ) := by
  let Bρ : Set Vec3 := vec3Ball z.1 ρ
  let Tρ : Set ℝ := Ioc (z.2 - ρ ^ 2) z.2
  let Tr : Set ℝ := Ioc (z.2 - r ^ 2) z.2
  let F : Vec3 × ℝ → ℝ := fun w => spatialGradientSq u Du w
  let G : ℝ → ℝ := fun s =>
    |∫ x in Bρ, F (x, s)| ^ (1 / 2 : ℝ)
  let U : ℝ → ℝ := fun s =>
    (∫ y in Bρ, (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)
  let A : ℝ := 9 * sobolevPoincareL6Constant.toReal *
    Real.sqrt ρ * alpha u z ρ
  obtain ⟨Ω', J, hbox, hball, htime⟩ :=
    pressure_box_geometry hsol hρ hsub
  have hgradInt : Integrable F ((volume.restrict Bρ).prod
      (volume.restrict Tρ)) := by
    have hc := pressure_gradient_integrable hsol hρ hsub
    rw [parabolicCylinder, Integration.volume_parabolicPoint_eq_prod] at hc
    change Integrable (fun w : Vec3 × ℝ => spatialGradientSq u Du w)
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (Bρ ×ˢ Tρ)) at hc
    rw [← Measure.prod_restrict] at hc
    simpa [F] using hc
  have hGae : AEMeasurable (fun s : ℝ => ∫ x in Bρ, F (x, s))
      (volume.restrict Tρ) := by
    have hswap := hgradInt.aestronglyMeasurable.prod_swap.integral_prod_right'
    simpa only [Prod.swap_prod_mk] using hswap.aemeasurable
  have hGmeas : AEStronglyMeasurable G (volume.restrict Tρ) := by
    have hc : Continuous (fun x : ℝ => |x| ^ (1 / 2 : ℝ)) :=
      continuous_abs.rpow_const (fun _ => Or.inr (by norm_num))
    have htmp := (hc.measurable.comp_aemeasurable hGae).aestronglyMeasurable
    convert htmp using 1 ; dsimp [G, Function.comp_def]
  have hGnonneg : 0 ≤ᵐ[volume.restrict Tρ] G :=
    Eventually.of_forall (fun s => Real.rpow_nonneg (abs_nonneg _) _)
  have hGbound : eLpNorm' G 2 (volume.restrict Tρ) ≤
      ENNReal.ofReal (Real.sqrt ρ * beta u Du z ρ) := by
    have hgrad := pressure_time_norm_bound (B := Bρ) (T := Tρ) (F := F)
      (G := G) (D := ENNReal.ofReal (ρ * beta u Du z ρ ^ 2))
      (p₀ := 2) (by norm_num) hgradInt hGmeas
      (by
        intro s
        dsimp [G]
        rw [abs_of_nonneg]
        exact integral_nonneg_of_ae (Eventually.of_forall fun x => by
          dsimp [F]
          unfold spatialGradientSq
          positivity))
      (by
        intro w
        dsimp [F]
        unfold spatialGradientSq
        positivity)
      (by
        have heq := sws_lintegral_spatialGradientSq_eq_ofReal_beta_sq
          hsol z hρ hsub
        rw [parabolicCylinder, Integration.volume_parabolicPoint_eq_prod] at heq
        change (∫⁻ w in Bρ ×ˢ Tρ,
            ENNReal.ofReal (spatialGradientSq u Du w) ∂
              ((volume : Measure Vec3).prod (volume : Measure ℝ))) = _ at heq
        exact heq.le)
    have hβ : 0 ≤ beta u Du z ρ := by unfold beta; positivity
    have hroot : (ENNReal.ofReal (ρ * beta u Du z ρ ^ 2)) ^
        (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt ρ * beta u Du z ρ) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hρ.le (sq_nonneg _))
        (by norm_num)]
      have hreal : (ρ * beta u Du z ρ ^ 2) ^ (1 / 2 : ℝ) =
          Real.sqrt ρ * beta u Du z ρ := by
        rw [show beta u Du z ρ ^ 2 = beta u Du z ρ ^ (2 : ℝ) by
          norm_num [Real.rpow_natCast]]
        rw [Real.mul_rpow hρ.le (Real.rpow_nonneg hβ 2),
          Real.sqrt_eq_rpow, ← Real.rpow_mul hβ]
        norm_num
      rw [hreal]
    rw [← hroot]
    exact hgrad
  have hU := U_bounds hsol hρ hsub
  have henergy := pressure_energy_bound hsol hρ hsub
  have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hS : 0 ≤ sobolevPoincareL6Constant.toReal := ENNReal.toReal_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hTr : Tr ⊆ Tρ := by
    intro s hs
    have hρ0 : 0 ≤ ρ := by
      have h0 : 0 ≤ ρ / 2 := le_of_lt (lt_of_lt_of_le hr hhalf)
      linarith only [h0]
    have hsq : r ^ 2 ≤ ρ ^ 2 := by
      apply (sq_le_sq₀ hr.le hρ0).2
      linarith only [hhalf, hρ0]
    exact ⟨by linarith only [hs.1, hsq], hs.2⟩
  have hpoint : ∀ᵐ s ∂volume.restrict Tρ, 0 ≤ U s ∧
      U s ≤ A * G s := by
    filter_upwards [hU, henergy] with s hUs hEs
    refine ⟨?_, ?_⟩
    · dsimp [U]
      exact Real.rpow_nonneg
        (integral_nonneg_of_ae (Eventually.of_forall fun y => by
          have hnorm : 0 ≤ utensorNorm u z.1 ρ s y := by
            unfold utensorNorm
            exact Real.sqrt_nonneg _
          exact Real.rpow_nonneg hnorm _)) _
    · dsimp [U, A, G]
      calc
        (∫ y in Bρ, (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^
            (2 / 3 : ℝ) ≤
          9 * sobolevPoincareL6Constant.toReal *
            (∫ y in Bρ, vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^
              (1 / 2 : ℝ) *
            (∫ y in Bρ, spatialGradientSq u Du (y, s)) ^
              (1 / 2 : ℝ) := by
          simpa [Bρ] using hUs.1
        _ ≤ 9 * sobolevPoincareL6Constant.toReal *
            (Real.sqrt ρ * alpha u z ρ) *
            (∫ y in Bρ, spatialGradientSq u Du (y, s)) ^
              (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right
          · apply mul_le_mul_of_nonneg_left hEs
            positivity
          · exact Real.rpow_nonneg
              (integral_nonneg_of_ae (Eventually.of_forall fun y => by
                dsimp [F]
                unfold spatialGradientSq
                positivity)) _
        _ ≤ A * |∫ x in Bρ, F (x, s)| ^ (1 / 2 : ℝ) := by
          have hFnonneg : 0 ≤ ∫ x in Bρ, F (x, s) :=
            integral_nonneg_of_ae (Eventually.of_forall fun y => by
              dsimp [F]
              unfold spatialGradientSq
              positivity)
          rw [abs_of_nonneg hFnonneg]
          dsimp [A, F]
          ring_nf
          exact le_rfl
  have hpointTr := ae_restrict_of_ae_restrict_of_subset hTr hpoint
  have hholder := time_holder (t₀ := z.2) hr hhalf hGmeas hGnonneg
  have hX : (∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^
      (2 / 3 : ℝ) ≤ ENNReal.ofReal (r ^ (1 / 3 : ℝ)) *
        ENNReal.ofReal (Real.sqrt ρ * beta u Du z ρ) := by
    calc
      _ = (∫⁻ s in Tr, ENNReal.ofReal (G s) ^
          (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
        congr 1
        apply lintegral_congr
        intro s
        rw [Real.enorm_eq_ofReal (by positivity : 0 ≤ G s)]
      _ ≤ ENNReal.ofReal r ^ (1 / 3 : ℝ) *
          eLpNorm' G 2 (volume.restrict Tρ) := hholder.1
      _ ≤ _ := by
        have hrpow : ENNReal.ofReal r ^ (1 / 3 : ℝ) =
            ENNReal.ofReal (r ^ (1 / 3 : ℝ)) :=
          ENNReal.ofReal_rpow_of_nonneg hr.le (by norm_num)
        rw [hrpow]
        gcongr
  have hscale :
      (∫⁻ s in Tr, ENNReal.ofReal (C * U s) ^ (3 / 2 : ℝ)) ^
          (2 / 3 : ℝ) ≤
        ENNReal.ofReal (C * (9 * sobolevPoincareL6Constant.toReal) *
          r ^ (1 / 3 : ℝ) * ρ * alpha u z ρ * beta u Du z ρ) := by
    have hpoint' : ∀ᵐ s ∂volume.restrict Tr,
        ENNReal.ofReal (C * U s) ^ (3 / 2 : ℝ) ≤
          ENNReal.ofReal (C * A) ^ (3 / 2 : ℝ) *
            (‖G s‖ₑ ^ (3 / 2 : ℝ)) := by
      filter_upwards [hpointTr] with s hs
      have hCU : C * U s ≤ C * (A * G s) :=
        mul_le_mul_of_nonneg_left hs.2 hC
      have hCA : ENNReal.ofReal (C * U s) ≤
          ENNReal.ofReal (C * A) * ‖G s‖ₑ := by
        have hGs : 0 ≤ G s := by
          dsimp [G]
          exact Real.rpow_nonneg (abs_nonneg _) _
        rw [Real.enorm_eq_ofReal hGs]
        calc
          ENNReal.ofReal (C * U s) ≤ ENNReal.ofReal (C * (A * G s)) :=
            ENNReal.ofReal_le_ofReal hCU
          _ = ENNReal.ofReal (C * A) * ENNReal.ofReal (G s) := by
            calc
              ENNReal.ofReal (C * (A * G s)) =
                  ENNReal.ofReal C *
                    (ENNReal.ofReal A * ENNReal.ofReal (G s)) := by
                rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_mul hA]
              _ = ENNReal.ofReal (C * A) * ENNReal.ofReal (G s) := by
                rw [ENNReal.ofReal_mul hC]
                ac_rfl
      calc
        ENNReal.ofReal (C * U s) ^ (3 / 2 : ℝ) ≤
            (ENNReal.ofReal (C * A) * ‖G s‖ₑ) ^ (3 / 2 : ℝ) :=
          ENNReal.rpow_le_rpow hCA (by norm_num)
        _ = ENNReal.ofReal (C * A) ^ (3 / 2 : ℝ) *
            ‖G s‖ₑ ^ (3 / 2 : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    have hDint :
        (∫⁻ s in Tr, ENNReal.ofReal (C * U s) ^ (3 / 2 : ℝ)) ≤
          ENNReal.ofReal (C * A) ^ (3 / 2 : ℝ) *
            (∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) := by
      calc
        _ ≤ ∫⁻ s in Tr, ENNReal.ofReal (C * A) ^ (3 / 2 : ℝ) *
            ‖G s‖ₑ ^ (3 / 2 : ℝ) := lintegral_mono_ae hpoint'
        _ = _ := by
          exact lintegral_const_mul' (μ := volume.restrict Tr)
            (ENNReal.ofReal (C * A) ^ (3 / 2 : ℝ))
            (fun s => ‖G s‖ₑ ^ (3 / 2 : ℝ))
            (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
              ENNReal.ofReal_ne_top)
    have hroot := ENNReal.rpow_le_rpow hDint (by norm_num : (0 : ℝ) ≤ 2 / 3)
    calc
      _ ≤ (ENNReal.ofReal (C * A) ^ (3 / 2 : ℝ) *
          (∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) := hroot
      _ = ENNReal.ofReal (C * A) *
          (∫⁻ s in Tr, ‖G s‖ₑ ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        have hq : (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 := by norm_num
        rw [hq, ENNReal.rpow_one]
      _ ≤ ENNReal.ofReal (C * A) *
          (ENNReal.ofReal (r ^ (1 / 3 : ℝ)) *
            ENNReal.ofReal (Real.sqrt ρ * beta u Du z ρ)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      _ = ENNReal.ofReal (C * (9 * sobolevPoincareL6Constant.toReal) *
          r ^ (1 / 3 : ℝ) * ρ * alpha u z ρ * beta u Du z ρ) := by
        have hsqrt : (Real.sqrt ρ) * Real.sqrt ρ = ρ := by
          nlinarith only [Real.sq_sqrt hρ.le]
        have hreal :
            (C * (9 * sobolevPoincareL6Constant.toReal * Real.sqrt ρ *
              alpha u z ρ)) *
              (r ^ (1 / 3 : ℝ) * (Real.sqrt ρ * beta u Du z ρ)) =
            C * (9 * sobolevPoincareL6Constant.toReal) *
              r ^ (1 / 3 : ℝ) * ρ * alpha u z ρ * beta u Du z ρ := by
          calc
            _ = C * (9 * sobolevPoincareL6Constant.toReal) *
                r ^ (1 / 3 : ℝ) *
                (Real.sqrt ρ * Real.sqrt ρ) *
                (alpha u z ρ * beta u Du z ρ) := by ring
            _ = _ := by rw [hsqrt]; ring
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ (1 / 3 : ℝ)),
          ← ENNReal.ofReal_mul (by positivity :
            0 ≤ C * A), ← hreal]
  simpa [Bρ, Tρ, Tr, U] using hscale

/-! The solution-level export below is the exact cylinder shape consumed by
`thetaDecay_T_of_inputs`.  The hypothesis is the global `L^(3/2)` slice estimate;
the preceding two lemmas perform the product-measure and time-scaling steps. -/

theorem hCZ_p1_cylinder_of_global_slice
    (C_CZ : ℝ) (hC_CZ : 0 ≤ C_CZ)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (fun x : Vec3 => pressureP1
        (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
        p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (fun x : Vec3 => pressureP1
        (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
        p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        C_CZ *
          (∫ y in vec3Ball z.1 ρ,
            (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint => pressureP1
          (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
          p f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
      ENNReal.ofReal ((C_CZ * (9 * sobolevPoincareL6Constant.toReal)) *
        (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ) := by
  let P : ParabolicPoint → ℝ := fun w => pressureP1
    (mollifiedBallCutoff z.1 hρ) u
    (fun t j => MeasureTheory.average
      (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
    p f w.2 w.1
  have hPouter : AEStronglyMeasurable P
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    obtain ⟨B, T, η, c, hB, hT, hη, hc, hP, -⟩ :=
      pressure_source_measurable_on_cylinder hsol hρ hsub
    have hc' : c = (fun s => fun j =>
        MeasureTheory.average (volume.restrict (vec3Ball z.1 ρ))
          (fun y => u (y, s) j)) := by
      funext s
      rw [hc s, hB]
    simpa [P, hB, hT, hη, hc'] using hP
  have hρ0 : 0 ≤ ρ := by
    have h0 : 0 ≤ ρ / 2 := le_of_lt (lt_of_lt_of_le hr hhalf)
    linarith only [h0]
  have hrrho : r ≤ ρ := by
    linarith only [hhalf, hρ0]
  have hsq : r ^ 2 ≤ ρ ^ 2 := by
    apply (sq_le_sq₀ hr.le hρ0).2
    exact hrrho
  have htime : Ioc (z.2 - r ^ 2) z.2 ⊆ Ioc (z.2 - ρ ^ 2) z.2 := by
    intro s hs
    exact ⟨by linarith only [hs.1, hsq], hs.2⟩
  have hcyl : parabolicCylinder z.1 z.2 r ⊆
      parabolicCylinder z.1 z.2 ρ := by
    intro w hw
    change (w.1 ∈ vec3Ball z.1 r ∧
      w.2 ∈ Ioc (z.2 - r ^ 2) z.2) at hw
    change (w.1 ∈ vec3Ball z.1 ρ ∧
      w.2 ∈ Ioc (z.2 - ρ ^ 2) z.2)
    refine ⟨?_, ?_⟩
    · rw [mem_vec3Ball] at hw ⊢
      exact lt_of_lt_of_le hw.1 hrrho
    · exact ⟨by linarith only [hw.2.1, hsq], hw.2.2⟩
  have hPinner : AEStronglyMeasurable P
      (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    hPouter.mono_measure (Measure.restrict_mono_set volume hcyl)
  have hCZr := ae_restrict_of_ae_restrict_of_subset htime hCZ_p1
  have hB : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - r ^ 2) z.2),
      MemLp (fun x : Vec3 => P (x, s)) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
        eLpNorm (fun x : Vec3 => P (x, s)) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
          ENNReal.ofReal (C_CZ *
            (∫ y in vec3Ball z.1 ρ,
              (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) := by
    filter_upwards [hCZr] with s hs
    rcases hs with ⟨hsMem, hsBound⟩
    refine ⟨hsMem, ?_⟩
    have hU0 : 0 ≤
        (∫ y in vec3Ball z.1 ρ,
          (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
      apply Real.rpow_nonneg
      exact integral_nonneg_of_ae (Eventually.of_forall fun y => by
        have hy : 0 ≤ utensorNorm u z.1 ρ s y := by
          unfold utensorNorm
          exact Real.sqrt_nonneg _
        exact Real.rpow_nonneg hy _)
    have hbound : (eLpNorm (fun x : Vec3 => P (x, s))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal ≤
        C_CZ * (∫ y in vec3Ball z.1 ρ,
          (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
      simpa only [lpNorm, P] using hsBound
    calc
      eLpNorm (fun x : Vec3 => P (x, s))
          (ENNReal.ofReal (3 / 2 : ℝ)) volume =
          ENNReal.ofReal ((eLpNorm (fun x : Vec3 => P (x, s))
            (ENNReal.ofReal (3 / 2 : ℝ)) volume).toReal) :=
        (ENNReal.ofReal_toReal hsMem.ne).symm
      _ ≤ ENNReal.ofReal (C_CZ *
          (∫ y in vec3Ball z.1 ρ,
            (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) :=
        ENNReal.ofReal_le_ofReal (by
          exact hbound)
  have hinner := eLpNorm'_cylinder_le_of_ae_slice_bound
    (P := P)
    (B := fun s => ENNReal.ofReal (C_CZ *
      (∫ y in vec3Ball z.1 ρ,
        (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)))
    hr (by norm_num) hPinner hB
  have hinner' := hinner
  norm_num at hinner'
  have hscale := utensor_slice_scale_bound hsol hρ hr hhalf hsub hC_CZ
  have hraw : ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) * eLpNorm' P
      (3 / 2 : ℝ) (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        ENNReal.ofReal (C_CZ * (9 * sobolevPoincareL6Constant.toReal) *
          r ^ (1 / 3 : ℝ) * ρ * alpha u z ρ * beta u Du z ρ) := by
    calc
      _ ≤ ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          (∫⁻ s in Ioc (z.2 - r ^ 2) z.2,
            ENNReal.ofReal (C_CZ *
              (∫ y in vec3Ball z.1 ρ,
                (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) ^
              (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hinner' (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)
  have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hβ : 0 ≤ beta u Du z ρ := by unfold beta; positivity
  have hS : 0 ≤ sobolevPoincareL6Constant.toReal := ENNReal.toReal_nonneg
  have hreal : r ^ (-4 / 3 : ℝ) *
        (C_CZ * (9 * sobolevPoincareL6Constant.toReal) *
          r ^ (1 / 3 : ℝ) * ρ * alpha u z ρ * beta u Du z ρ) =
      (C_CZ * (9 * sobolevPoincareL6Constant.toReal)) *
        (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ := by
    have hrpow : r ^ (-4 / 3 : ℝ) * r ^ (1 / 3 : ℝ) = r⁻¹ := by
      rw [← Real.rpow_add hr]
      norm_num [Real.rpow_neg_one]
    have hratio : (r / ρ)⁻¹ = r⁻¹ * ρ := by
      field_simp [hr.ne', hρ.ne']
    calc
      r ^ (-4 / 3 : ℝ) *
          (C_CZ * (9 * sobolevPoincareL6Constant.toReal) *
            r ^ (1 / 3 : ℝ) * ρ * alpha u z ρ * beta u Du z ρ) =
          (C_CZ * (9 * sobolevPoincareL6Constant.toReal)) *
            (r ^ (-4 / 3 : ℝ) * r ^ (1 / 3 : ℝ)) * ρ *
              alpha u z ρ * beta u Du z ρ := by ring
      _ = (C_CZ * (9 * sobolevPoincareL6Constant.toReal)) *
          (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ := by
        rw [hrpow, hratio]
        ring
  calc
    _ ≤ ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        ENNReal.ofReal (C_CZ * (9 * sobolevPoincareL6Constant.toReal) *
          r ^ (1 / 3 : ℝ) * ρ * alpha u z ρ * beta u Du z ρ) := by
      simpa [P] using hraw
    _ = ENNReal.ofReal ((C_CZ * (9 * sobolevPoincareL6Constant.toReal)) *
        (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ) := by
      rw [← ENNReal.ofReal_mul (by positivity :
        0 ≤ r ^ (-4 / 3 : ℝ)), hreal]

/-! A comparison adapter lets the fixed coefficient used by the provider be
chosen before the solution fields, as required by the theorem-A/B consumers. -/

theorem hCZ_p1_cylinder_of_global_slice_le
    (C₁₂_p1 C_CZ : ℝ) (hC_CZ : 0 ≤ C_CZ)
    (hconst : C_CZ * (9 * sobolevPoincareL6Constant.toReal) ≤ C₁₂_p1)
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (fun x : Vec3 => pressureP1
        (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
        p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (fun x : Vec3 => pressureP1
        (mollifiedBallCutoff z.1 hρ) u
        (fun t j => MeasureTheory.average
          (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
        p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
        C_CZ *
          (∫ y in vec3Ball z.1 ρ,
            (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint => pressureP1
          (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
          p f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
      ENNReal.ofReal (C₁₂_p1 * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ) := by
  have hbase := hCZ_p1_cylinder_of_global_slice C_CZ hC_CZ hsol
    hρ hr hhalf hsub hCZ_p1
  have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hβ : 0 ≤ beta u Du z ρ := by unfold beta; positivity
  have hfactor : 0 ≤ (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ := by
    positivity
  have hcoeff :
      (C_CZ * (9 * sobolevPoincareL6Constant.toReal)) *
          (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ ≤
        C₁₂_p1 * (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ := by
    calc
      _ = (C_CZ * (9 * sobolevPoincareL6Constant.toReal)) *
          ((r / ρ)⁻¹ * alpha u z ρ) * beta u Du z ρ := by ring
      _ ≤ C₁₂_p1 * ((r / ρ)⁻¹ * alpha u z ρ) * beta u Du z ρ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hconst (by positivity)) hβ
      _ = _ := by ring
  calc
    _ ≤ ENNReal.ofReal ((C_CZ * (9 * sobolevPoincareL6Constant.toReal)) *
        (r / ρ)⁻¹ * alpha u z ρ * beta u Du z ρ) := by
      simpa only [] using hbase
    _ ≤ _ := ENNReal.ofReal_mono hcoeff


end CKN.Foundation.Euclidean
