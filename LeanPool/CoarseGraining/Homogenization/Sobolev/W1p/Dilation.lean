/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1Dilation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.Seminorms

/-! # Dilation -/

@[expose] public section

namespace Homogenization

open scoped ENNReal Pointwise

noncomputable section

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

/-- Push a scalar `W^{1,p}(U)` witness forward to `W^{1,p}(a • U)` by the
positive dilation `x ↦ a⁻¹ x`.  The weak gradient has the corresponding
chain-rule factor `a⁻¹`. -/
noncomputable def dilate {a : ℝ} (ha : 0 < a)
    (u : W1pFunction U p) : W1pFunction (a • U) p := by
  let V : Set (Vec d) := a • U
  let T : Vec d → Vec d := fun x => a⁻¹ • x
  have ha_ne : a ≠ 0 := ha.ne'
  have hmap := map_smul_volume_restrict (d := d) (a := a⁻¹) (inv_pos.mpr ha) V
  have hpre : a⁻¹ • V = U := by
    ext x
    simp [V, ha_ne]
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict V) :=
    (measurable_const_smul a⁻¹).aemeasurable
  refine
    { toFun := fun x => u.toFun (T x)
      grad := fun x => a⁻¹ • u.grad (T x)
      memLp := ?_
      gradMemLp := ?_
      hasWeakGradient := ?_ }
  · have hu_map : MeasureTheory.MemLp u.toFun p
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) := by
      rw [hmap, hpre]
      exact u.memLp.smul_measure ENNReal.ofReal_ne_top
    exact MeasureTheory.MemLp.comp_of_map hu_map hT_meas
  · intro i
    have hgrad_map : MeasureTheory.MemLp (fun x => u.grad x i) p
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) := by
      rw [hmap, hpre]
      exact (u.gradMemLp i).smul_measure ENNReal.ofReal_ne_top
    have hcomp : MeasureTheory.MemLp (fun x => u.grad (T x) i) p
        (MeasureTheory.volume.restrict V) :=
      MeasureTheory.MemLp.comp_of_map hgrad_map hT_meas
    have hsmul : MeasureTheory.MemLp (fun x => a⁻¹ * u.grad (T x) i) p
        (MeasureTheory.volume.restrict V) :=
      hcomp.const_mul a⁻¹
    simpa [Pi.smul_apply, smul_eq_mul] using hsmul
  · intro i φ hφ hφ_supp hφ_sub
    let ψ : Vec d → ℝ := fun y => φ (a • y)
    have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      simpa [ψ] using! hφ.comp (contDiff_const_smul a)
    have hψ_supp : HasCompactSupport ψ := by
      show HasCompactSupport (φ ∘ Homeomorph.smulOfNeZero a ha_ne)
      simpa [ψ, Function.comp] using
        hφ_supp.comp_homeomorph (Homeomorph.smulOfNeZero a ha_ne)
    have hψ_sub : tsupport ψ ⊆ U := by
      intro y hy
      have hy' : a • y ∈ tsupport φ := by
        rw [show ψ = φ ∘ Homeomorph.smulOfNeZero a ha_ne by rfl,
          tsupport_comp_eq_preimage φ (Homeomorph.smulOfNeZero a ha_ne)] at hy
        exact hy
      have hyV : a • y ∈ V := hφ_sub hy'
      simpa [V, Set.mem_smul_set_iff_inv_smul_mem, ha_ne] using hyV
    have hweak := u.hasWeakGradient i ψ hψ_smooth hψ_supp hψ_sub
    have hderivψ : ∀ y : Vec d,
        (fderiv ℝ ψ y) (basisVec i) =
          a * (fderiv ℝ φ (a • y)) (basisVec i) := by
      intro y
      have hderiv :
          fderiv ℝ (fun z : Vec d => φ (a • z)) y =
            a • fderiv ℝ φ (a • y) := by
        simpa [ψ] using (fderiv_comp_smul (𝕜 := ℝ) (f := φ) (x := y) a)
      simpa [smul_eq_mul] using
        congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hderiv
    have hweak_scaled :
        a * ∫ y in U, u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume =
          -∫ y in U, u.grad y i * φ (a • y) ∂MeasureTheory.volume := by
      have hfun :
          (fun y => u.toFun y * (fderiv ℝ ψ y) (basisVec i)) =
            fun y => a * (u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i)) := by
        funext y
        rw [hderivψ y]
        ring
      rw [hfun, MeasureTheory.integral_const_mul] at hweak
      simpa [ψ] using hweak
    have hchange_left :
        ∫ y in U, u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume =
          (a ^ d)⁻¹ * ∫ x in V,
            u.toFun (T x) * (fderiv ℝ φ x) (basisVec i)
              ∂MeasureTheory.volume := by
      simpa only [V, T, smul_smul, inv_mul_cancel₀ ha_ne, one_smul, smul_eq_mul,
        Module.finrank_fin_fun] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun x : Vec d =>
            u.toFun (T x) * (fderiv ℝ φ x) (basisVec i))
          (s := U) ha)
    have hchange_right :
        ∫ y in U, u.grad y i * φ (a • y) ∂MeasureTheory.volume =
          (a ^ d)⁻¹ * ∫ x in V,
            u.grad (T x) i * φ x ∂MeasureTheory.volume := by
      simpa only [V, T, smul_smul, inv_mul_cancel₀ ha_ne, one_smul, smul_eq_mul,
        Module.finrank_fin_fun] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun x : Vec d => u.grad (T x) i * φ x)
          (s := U) ha)
    have hpow_ne : a ^ d ≠ 0 := (pow_pos ha d).ne'
    have htarget :
        ∫ x in V, u.toFun (T x) * (fderiv ℝ φ x) (basisVec i)
            ∂MeasureTheory.volume =
          -(a⁻¹ * ∫ x in V, u.grad (T x) i * φ x ∂MeasureTheory.volume) := by
      rw [hchange_left, hchange_right] at hweak_scaled
      field_simp [hpow_ne, ha_ne] at hweak_scaled ⊢
      linarith
    calc
      ∫ x in V, u.toFun (T x) * (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume =
        -(a⁻¹ * ∫ x in V, u.grad (T x) i * φ x ∂MeasureTheory.volume) := htarget
      _ = -∫ x in V, (a⁻¹ • u.grad (T x)) i * φ x
          ∂MeasureTheory.volume := by
        have hfun :
            (fun x : Vec d => (a⁻¹ • u.grad (T x)) i * φ x) =
              fun x : Vec d => a⁻¹ * (u.grad (T x) i * φ x) := by
          funext x
          simp [Pi.smul_apply, smul_eq_mul]
          ring
        rw [hfun, MeasureTheory.integral_const_mul]

@[simp] theorem dilate_toFun {a : ℝ} (ha : 0 < a)
    (u : W1pFunction U p) (x : Vec d) :
    (u.dilate ha).toFun x = u.toFun (a⁻¹ • x) :=
  rfl

@[simp] theorem dilate_grad {a : ℝ} (ha : 0 < a)
    (u : W1pFunction U p) (x : Vec d) :
    (u.dilate ha).grad x = a⁻¹ • u.grad (a⁻¹ • x) :=
  rfl

/-- Pull a scalar `W^{1,p}(a • U)` witness back to `W^{1,p}(U)` by
precomposition with `x ↦ a • x`.  Its weak gradient is
`a • ∇u(a • x)`. -/
noncomputable def unscale {a : ℝ} (ha : 0 < a)
    (u : W1pFunction (a • U) p) : W1pFunction U p := by
  let V : Set (Vec d) := a • U
  let T : Vec d → Vec d := fun x => a • x
  have hmap := map_smul_volume_restrict (d := d) (a := a) ha U
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict U) :=
    (measurable_const_smul a).aemeasurable
  refine
    { toFun := fun x => u.toFun (T x)
      grad := fun x => a • u.grad (T x)
      memLp := ?_
      gradMemLp := ?_
      hasWeakGradient := ?_ }
  · have hu_map : MeasureTheory.MemLp u.toFun p
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
      rw [hmap]
      exact u.memLp.smul_measure ENNReal.ofReal_ne_top
    exact MeasureTheory.MemLp.comp_of_map hu_map hT_meas
  · intro i
    have hgrad_map : MeasureTheory.MemLp (fun x => u.grad x i) p
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
      rw [hmap]
      exact (u.gradMemLp i).smul_measure ENNReal.ofReal_ne_top
    have hcomp : MeasureTheory.MemLp (fun x => u.grad (T x) i) p
        (MeasureTheory.volume.restrict U) :=
      MeasureTheory.MemLp.comp_of_map hgrad_map hT_meas
    have hsmul : MeasureTheory.MemLp (fun x => a * u.grad (T x) i) p
        (MeasureTheory.volume.restrict U) :=
      hcomp.const_mul a
    simpa [Pi.smul_apply, smul_eq_mul] using hsmul
  · intro i φ hφ hφ_supp hφ_sub
    let ψ : Vec d → ℝ := fun y => φ (a⁻¹ • y)
    have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      simpa [ψ] using! hφ.comp (contDiff_const_smul a⁻¹)
    have hψ_supp : HasCompactSupport ψ := by
      show HasCompactSupport (φ ∘ Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))
      simpa [ψ, Function.comp] using
        hφ_supp.comp_homeomorph (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))
    have hψ_sub : tsupport ψ ⊆ V := by
      intro y hy
      have hy' : a⁻¹ • y ∈ tsupport φ := by
        rw [show ψ = φ ∘ Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne') by rfl,
          tsupport_comp_eq_preimage φ (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))] at hy
        exact hy
      exact ⟨a⁻¹ • y, hφ_sub hy', by simp [smul_smul, ha.ne']⟩
    have hweak := u.hasWeakGradient i ψ hψ_smooth hψ_supp hψ_sub
    have hderivψ : ∀ y : Vec d,
        (fderiv ℝ ψ y) (basisVec i) =
          a⁻¹ * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i) := by
      intro y
      have hderiv :
          fderiv ℝ (fun z : Vec d => φ (a⁻¹ • z)) y =
            a⁻¹ • fderiv ℝ φ (a⁻¹ • y) := by
        simpa [ψ] using (fderiv_comp_smul (𝕜 := ℝ) (f := φ) (x := y) a⁻¹)
      simpa [smul_eq_mul] using
        congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hderiv
    have hweak_scaled :
        ∫ y in V, u.toFun y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i)
            ∂MeasureTheory.volume =
          -a * ∫ y in V, u.grad y i * φ (a⁻¹ • y) ∂MeasureTheory.volume := by
      have hfun :
          (fun y => u.toFun y * (fderiv ℝ ψ y) (basisVec i)) =
            fun y => a⁻¹ * (u.toFun y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i)) := by
        funext y
        rw [hderivψ y]
        ring
      have hleft :
          ∫ y in V, u.toFun y * (fderiv ℝ ψ y) (basisVec i) ∂MeasureTheory.volume =
            a⁻¹ * ∫ y in V,
              u.toFun y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i) ∂MeasureTheory.volume := by
        rw [hfun, MeasureTheory.integral_const_mul]
      rw [hleft] at hweak
      have hmul := congrArg (fun t : ℝ => a * t) hweak
      have hcancel : a * (a⁻¹ *
          ∫ y in V, u.toFun y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i)
            ∂MeasureTheory.volume) =
          ∫ y in V, u.toFun y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i)
            ∂MeasureTheory.volume := by
        field_simp [ha.ne']
      simpa [hcancel, mul_neg, mul_assoc, mul_comm, mul_left_comm] using hmul
    have hchange_left :
        ∫ x in U, u.toFun (T x) * (fderiv ℝ φ x) (basisVec i)
            ∂MeasureTheory.volume =
          (a ^ d)⁻¹ * ∫ y in V,
            u.toFun y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i)
              ∂MeasureTheory.volume := by
      simpa only [V, T, smul_smul, inv_mul_cancel₀ ha.ne', one_smul, smul_eq_mul,
        Module.finrank_fin_fun] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun y : Vec d => u.toFun y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i))
          (s := U) ha)
    have hchange_right :
        ∫ x in U, (a • u.grad (T x)) i * φ x ∂MeasureTheory.volume =
          (a ^ d)⁻¹ * ∫ y in V,
            (a • u.grad y) i * φ (a⁻¹ • y) ∂MeasureTheory.volume := by
      simpa only [V, T, smul_smul, inv_mul_cancel₀ ha.ne', one_smul, smul_eq_mul,
        Module.finrank_fin_fun] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun y : Vec d => (a • u.grad y) i * φ (a⁻¹ • y))
          (s := U) ha)
    have hgrad_scaled_integral :
        ∫ y in V, (a • u.grad y) i * φ (a⁻¹ • y) ∂MeasureTheory.volume =
          a * ∫ y in V, u.grad y i * φ (a⁻¹ • y) ∂MeasureTheory.volume := by
      have hfun :
          (fun y : Vec d => (a • u.grad y) i * φ (a⁻¹ • y)) =
            fun y : Vec d => a * (u.grad y i * φ (a⁻¹ • y)) := by
        funext y
        simp [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hfun, MeasureTheory.integral_const_mul]
    calc
      ∫ x in U, u.toFun (T x) * (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume =
        (a ^ d)⁻¹ * ∫ y in V,
          u.toFun y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i)
            ∂MeasureTheory.volume := hchange_left
      _ = (a ^ d)⁻¹ *
          (-a * ∫ y in V, u.grad y i * φ (a⁻¹ • y) ∂MeasureTheory.volume) := by
            rw [hweak_scaled]
      _ = -((a ^ d)⁻¹ *
          ∫ y in V, (a • u.grad y) i * φ (a⁻¹ • y) ∂MeasureTheory.volume) := by
            rw [hgrad_scaled_integral]
            ring
      _ = -∫ x in U, (a • u.grad (T x)) i * φ x ∂MeasureTheory.volume := by
            rw [hchange_right]

@[simp] theorem unscale_toFun {a : ℝ} (ha : 0 < a)
    (u : W1pFunction (a • U) p) (x : Vec d) :
    (u.unscale ha).toFun x = u.toFun (a • x) :=
  rfl

@[simp] theorem unscale_grad {a : ℝ} (ha : 0 < a)
    (u : W1pFunction (a • U) p) (x : Vec d) :
    (u.unscale ha).grad x = a • u.grad (a • x) :=
  rfl

/-- The common `L^p` measure factor in a positive dilation of `Vec d`. -/
noncomputable def dilationLpFactor (d : ℕ) (p : ENNReal) (a : ℝ) : ℝ :=
  (ENNReal.ofReal (((a⁻¹) ^ d)⁻¹) ^ (1 / p).toReal).toReal

/-- Positivity of the finite-dimensional dilation norm factor. -/
theorem dilationLpFactor_pos (d : ℕ) (p : ENNReal) {a : ℝ} (ha : 0 < a) :
    0 < dilationLpFactor d p a := by
  unfold dilationLpFactor
  have hbase : 0 < ENNReal.ofReal (((a⁻¹) ^ d)⁻¹) := by
    rw [ENNReal.ofReal_pos]
    exact inv_pos.mpr (pow_pos (inv_pos.mpr ha) d)
  apply ENNReal.toReal_pos
  · exact (ENNReal.rpow_pos hbase ENNReal.ofReal_ne_top).ne'
  · exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top

/-- Change of variables for an `L^p` norm under the forward positive dilation. -/
theorem eLpNorm_comp_smul_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    {f : Vec d → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f (volumeMeasureOn (a • U))) :
    MeasureTheory.eLpNorm (fun x => f (a • x)) p (volumeMeasureOn U) =
      ENNReal.ofReal ((a ^ d)⁻¹) ^ (1 / p).toReal *
        MeasureTheory.eLpNorm f p (volumeMeasureOn (a • U)) := by
  let V : Set (Vec d) := a • U
  let T : Vec d → Vec d := fun x => a • x
  have hmap := map_smul_volume_restrict (d := d) (a := a) ha U
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict U) :=
    (measurable_const_smul a).aemeasurable
  have hf_map :
      MeasureTheory.AEStronglyMeasurable f
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
    rw [hmap]
    exact hf.mono_ac MeasureTheory.Measure.smul_absolutelyContinuous
  have hmap_eLp :
      MeasureTheory.eLpNorm f p
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) =
        MeasureTheory.eLpNorm (fun x => f (T x)) p
          (MeasureTheory.volume.restrict U) := by
    exact MeasureTheory.eLpNorm_map_measure hf_map hT_meas
  change MeasureTheory.eLpNorm (fun x => f (T x)) p
      (MeasureTheory.volume.restrict U) = _
  rw [← hmap_eLp, hmap, MeasureTheory.eLpNorm_smul_measure_of_ne_top hp_top f _ hf]
  simp only [smul_eq_mul, volumeMeasureOn]

/-- The `eLpNorm` of a value representative after pulling it back by dilation. -/
theorem eLpNorm_unscale_toFun {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction (a • U) p) :
    MeasureTheory.eLpNorm (u.unscale ha).toFun p (volumeMeasureOn U) =
      ENNReal.ofReal ((a ^ d)⁻¹) ^ (1 / p).toReal *
        MeasureTheory.eLpNorm u.toFun p (volumeMeasureOn (a • U)) := by
  simpa using! eLpNorm_comp_smul_eq (U := U) (p := p) ha hp_top
    u.memLp.aestronglyMeasurable

/-- The scalar value `L^p` seminorm under pullback by positive dilation. -/
theorem valueLpSeminorm_unscale_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction (a • U) p) :
    (u.unscale ha).valueLpSeminorm =
      dilationLpFactor d p a⁻¹ * u.valueLpSeminorm := by
  have hfactor :
      dilationLpFactor d p a⁻¹ =
        (ENNReal.ofReal ((a ^ d)⁻¹) ^ (1 / p).toReal).toReal := by
    simp [dilationLpFactor]
  unfold valueLpSeminorm
  rw [eLpNorm_unscale_toFun ha hp_top u, ENNReal.toReal_mul]
  rw [← hfactor]

/-- The `eLpNorm` of one weak-gradient coordinate after dilation pullback. -/
theorem eLpNorm_unscale_gradCoord {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction (a • U) p) (i : Fin d) :
    MeasureTheory.eLpNorm (fun x => (u.unscale ha).grad x i) p
        (volumeMeasureOn U) =
      ENNReal.ofReal a *
        (ENNReal.ofReal ((a ^ d)⁻¹) ^ (1 / p).toReal *
          MeasureTheory.eLpNorm (fun x => u.grad x i) p (volumeMeasureOn (a • U))) := by
  have hgrad_meas :
      MeasureTheory.AEStronglyMeasurable (fun x => u.grad x i)
        (volumeMeasureOn (a • U)) :=
    (u.gradMemLp i).aestronglyMeasurable
  change MeasureTheory.eLpNorm (fun x => (a • u.grad (a • x)) i) p
      (volumeMeasureOn U) = _
  have hfun :
      (fun x : Vec d => (a • u.grad (a • x)) i) =
        a • fun x : Vec d => u.grad (a • x) i := rfl
  rw [hfun, MeasureTheory.eLpNorm_const_smul,
    Real.enorm_eq_ofReal ha.le, eLpNorm_comp_smul_eq ha hp_top hgrad_meas]

/-- The coordinate gradient `L^p` seminorm under pullback by positive dilation. -/
theorem gradCoordLpSeminorm_unscale_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction (a • U) p) (i : Fin d) :
    (u.unscale ha).gradCoordLpSeminorm i =
      a * dilationLpFactor d p a⁻¹ * u.gradCoordLpSeminorm i := by
  have hfactor :
      dilationLpFactor d p a⁻¹ =
        (ENNReal.ofReal ((a ^ d)⁻¹) ^ (1 / p).toReal).toReal := by
    simp [dilationLpFactor]
  unfold gradCoordLpSeminorm
  rw [eLpNorm_unscale_gradCoord ha hp_top u i,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le]
  rw [← hfactor]
  ring

/-- The coordinate-sum gradient `L^p` seminorm under dilation pullback. -/
theorem gradientCoordLpSeminormSum_unscale_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction (a • U) p) :
    (u.unscale ha).gradientCoordLpSeminormSum =
      a * dilationLpFactor d p a⁻¹ * u.gradientCoordLpSeminormSum := by
  unfold gradientCoordLpSeminormSum
  calc
    ∑ i, (u.unscale ha).gradCoordLpSeminorm i =
        ∑ i, a * dilationLpFactor d p a⁻¹ * u.gradCoordLpSeminorm i := by
          refine Finset.sum_congr rfl fun i _ => gradCoordLpSeminorm_unscale_eq ha hp_top u i
    _ = a * dilationLpFactor d p a⁻¹ * ∑ i, u.gradCoordLpSeminorm i := by
      rw [← Finset.mul_sum]

/-- Integral averages commute with the pullback of a scalar witness by
positive dilation. -/
theorem integralAverage_unscale_eq {a : ℝ} (ha : 0 < a)
    (u : W1pFunction (a • U) p) :
    integralAverage U (u.unscale ha).toFun = integralAverage (a • U) u.toFun := by
  have hvolume :
      (MeasureTheory.volume (a • U)).toReal =
        a ^ d * (MeasureTheory.volume U).toReal := by
    have hmeasure :
        MeasureTheory.volume (a • U) =
          ENNReal.ofReal (a ^ d) * MeasureTheory.volume U := by
      simpa [Vec] using
        (MeasureTheory.Measure.addHaar_smul_of_nonneg
          (μ := MeasureTheory.volume) (E := Vec d) ha.le U)
    rw [hmeasure, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ha.le d)]
  have hsetIntegral :
      ∫ x in U, (u.unscale ha).toFun x ∂MeasureTheory.volume =
        (a ^ d)⁻¹ * ∫ y in a • U, u.toFun y ∂MeasureTheory.volume := by
    simpa only [unscale_toFun, Module.finrank_fin_fun, smul_eq_mul] using
      (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume) (f := u.toFun) (s := U) ha)
  unfold integralAverage
  rw [hsetIntegral, hvolume]
  by_cases hU_zero : (MeasureTheory.volume U).toReal = 0
  · simp [hU_zero]
  · field_simp [hU_zero, (pow_pos ha d).ne']

/-- Pullback by a positive dilation preserves the zero-average condition. -/
theorem meanZeroOn_unscale {a : ℝ} (ha : 0 < a)
    (u : W1pFunction (a • U) p) (hmean : MeanZeroOn (a • U) u.toFun) :
    MeanZeroOn U (u.unscale ha).toFun := by
  change ∫ x in U, u.toFun (a • x) ∂MeasureTheory.volume = 0
  rw [MeasureTheory.Measure.setIntegral_comp_smul_of_pos
    (μ := MeasureTheory.volume) (f := u.toFun) (s := U) ha]
  rw [hmean]
  simp

/-- The mean-subtracted scalar `L^p` seminorm under pullback by positive
dilation. -/
theorem subAverageLpSeminorm_unscale_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction (a • U) p) :
    (u.unscale ha).subAverageLpSeminorm =
      dilationLpFactor d p a⁻¹ * u.subAverageLpSeminorm := by
  have hfactor :
      dilationLpFactor d p a⁻¹ =
        (ENNReal.ofReal ((a ^ d)⁻¹) ^ (1 / p).toReal).toReal := by
    simp [dilationLpFactor]
  have hsub_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun x => u.toFun x - integralAverage (a • U) u.toFun)
        (volumeMeasureOn (a • U)) :=
    u.memLp.aestronglyMeasurable.sub MeasureTheory.aestronglyMeasurable_const
  unfold subAverageLpSeminorm
  rw [integralAverage_unscale_eq ha u]
  change
    (MeasureTheory.eLpNorm
      (fun x => u.toFun (a • x) - integralAverage (a • U) u.toFun) p
      (volumeMeasureOn U)).toReal = _
  have hfun :
      (fun x => u.toFun (a • x) - integralAverage (a • U) u.toFun) =
        fun x => (fun y => u.toFun y - integralAverage (a • U) u.toFun) (a • x) := rfl
  rw [hfun, eLpNorm_comp_smul_eq ha hp_top hsub_meas, ENNReal.toReal_mul,
    ← hfactor]

/-- Change of variables for an `L^p` norm under the inverse positive dilation.
The assumption is measurability rather than `MemLp`, so it also applies to
the mean-subtracted representative in the Poincare seminorm. -/
theorem eLpNorm_comp_dilate_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    {f : Vec d → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f (volumeMeasureOn U)) :
    MeasureTheory.eLpNorm (fun x => f (a⁻¹ • x)) p (volumeMeasureOn (a • U)) =
      ENNReal.ofReal (((a⁻¹) ^ d)⁻¹) ^ (1 / p).toReal *
        MeasureTheory.eLpNorm f p (volumeMeasureOn U) := by
  let V : Set (Vec d) := a • U
  let T : Vec d → Vec d := fun x => a⁻¹ • x
  have hmap := map_smul_volume_restrict (d := d) (a := a⁻¹) (inv_pos.mpr ha) V
  have hpre : a⁻¹ • V = U := by
    ext x
    simp [V, ha.ne']
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict V) :=
    (measurable_const_smul a⁻¹).aemeasurable
  have hf_map :
      MeasureTheory.AEStronglyMeasurable f
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) := by
    rw [hmap, hpre]
    exact hf.mono_ac MeasureTheory.Measure.smul_absolutelyContinuous
  have hmap_eLp :
      MeasureTheory.eLpNorm f p
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) =
        MeasureTheory.eLpNorm (fun x => f (T x)) p
          (MeasureTheory.volume.restrict V) := by
    exact MeasureTheory.eLpNorm_map_measure hf_map hT_meas
  change MeasureTheory.eLpNorm (fun x => f (T x)) p
      (MeasureTheory.volume.restrict V) = _
  rw [← hmap_eLp, hmap, hpre,
    MeasureTheory.eLpNorm_smul_measure_of_ne_top hp_top f _ hf]
  simp only [smul_eq_mul, volumeMeasureOn]

/-- The `eLpNorm` of the value representative after a positive dilation. -/
theorem eLpNorm_dilate_toFun {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction U p) :
    MeasureTheory.eLpNorm (u.dilate ha).toFun p (volumeMeasureOn (a • U)) =
      ENNReal.ofReal (((a⁻¹) ^ d)⁻¹) ^ (1 / p).toReal *
        MeasureTheory.eLpNorm u.toFun p (volumeMeasureOn U) := by
  simpa using! eLpNorm_comp_dilate_eq (U := U) (p := p) ha hp_top
    u.memLp.aestronglyMeasurable

/-- The scalar value `L^p` seminorm under positive dilation. -/
theorem valueLpSeminorm_dilate_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction U p) :
    (u.dilate ha).valueLpSeminorm =
      dilationLpFactor d p a * u.valueLpSeminorm := by
  unfold valueLpSeminorm dilationLpFactor
  rw [eLpNorm_dilate_toFun ha hp_top u, ENNReal.toReal_mul]

/-- The `eLpNorm` of one weak-gradient coordinate after positive dilation. -/
theorem eLpNorm_dilate_gradCoord {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction U p) (i : Fin d) :
    MeasureTheory.eLpNorm (fun x => (u.dilate ha).grad x i) p
        (volumeMeasureOn (a • U)) =
      ENNReal.ofReal a⁻¹ *
        (ENNReal.ofReal (((a⁻¹) ^ d)⁻¹) ^ (1 / p).toReal *
          MeasureTheory.eLpNorm (fun x => u.grad x i) p (volumeMeasureOn U)) := by
  let V : Set (Vec d) := a • U
  let T : Vec d → Vec d := fun x => a⁻¹ • x
  have hmap := map_smul_volume_restrict (d := d) (a := a⁻¹) (inv_pos.mpr ha) V
  have hpre : a⁻¹ • V = U := by
    ext x
    simp [V, ha.ne']
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict V) :=
    (measurable_const_smul a⁻¹).aemeasurable
  have hgrad_aesm_map :
      MeasureTheory.AEStronglyMeasurable (fun x => u.grad x i)
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) := by
    rw [hmap, hpre]
    exact (u.gradMemLp i).aestronglyMeasurable.mono_ac
      MeasureTheory.Measure.smul_absolutelyContinuous
  have hmap_eLp :
      MeasureTheory.eLpNorm (fun x => u.grad x i) p
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) =
        MeasureTheory.eLpNorm (fun x => u.grad (T x) i) p
          (MeasureTheory.volume.restrict V) := by
    exact MeasureTheory.eLpNorm_map_measure hgrad_aesm_map hT_meas
  change MeasureTheory.eLpNorm (fun x => (a⁻¹ • u.grad (T x)) i) p
      (MeasureTheory.volume.restrict V) = _
  have hfun :
      (fun x : Vec d => (a⁻¹ • u.grad (T x)) i) =
        a⁻¹ • fun x : Vec d => u.grad (T x) i := rfl
  rw [hfun, MeasureTheory.eLpNorm_const_smul,
    Real.enorm_eq_ofReal (inv_nonneg.mpr ha.le), ← hmap_eLp, hmap, hpre,
    MeasureTheory.eLpNorm_smul_measure_of_ne_top hp_top (fun x => u.grad x i) _
      (u.gradMemLp i).aestronglyMeasurable]
  simp only [smul_eq_mul, volumeMeasureOn]

/-- The coordinate gradient `L^p` seminorm under positive dilation. -/
theorem gradCoordLpSeminorm_dilate_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction U p) (i : Fin d) :
    (u.dilate ha).gradCoordLpSeminorm i =
      a⁻¹ * dilationLpFactor d p a * u.gradCoordLpSeminorm i := by
  unfold gradCoordLpSeminorm dilationLpFactor
  rw [eLpNorm_dilate_gradCoord ha hp_top u i,
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)]
  ring

/-- The coordinate-sum gradient `L^p` seminorm under positive dilation. -/
theorem gradientCoordLpSeminormSum_dilate_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction U p) :
    (u.dilate ha).gradientCoordLpSeminormSum =
      a⁻¹ * dilationLpFactor d p a * u.gradientCoordLpSeminormSum := by
  unfold gradientCoordLpSeminormSum
  calc
    ∑ i, (u.dilate ha).gradCoordLpSeminorm i =
        ∑ i, a⁻¹ * dilationLpFactor d p a * u.gradCoordLpSeminorm i := by
          refine Finset.sum_congr rfl fun i _ => gradCoordLpSeminorm_dilate_eq ha hp_top u i
    _ = a⁻¹ * dilationLpFactor d p a * ∑ i, u.gradCoordLpSeminorm i := by
      rw [← Finset.mul_sum]

/-- Integral averages commute with positive dilation of a scalar witness. -/
theorem integralAverage_dilate_eq {a : ℝ} (ha : 0 < a)
    (u : W1pFunction U p) :
    integralAverage (a • U) (u.dilate ha).toFun = integralAverage U u.toFun := by
  have hvolume :
      (MeasureTheory.volume (a • U)).toReal =
        a ^ d * (MeasureTheory.volume U).toReal := by
    have hmeasure :
        MeasureTheory.volume (a • U) =
          ENNReal.ofReal (a ^ d) * MeasureTheory.volume U := by
      simpa [Vec] using
        (MeasureTheory.Measure.addHaar_smul_of_nonneg
          (μ := MeasureTheory.volume) (E := Vec d) ha.le U)
    rw [hmeasure, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg ha.le d)]
  have hsetIntegral :
      ∫ x in a • U, (u.dilate ha).toFun x ∂MeasureTheory.volume =
        a ^ d * ∫ y in U, u.toFun y ∂MeasureTheory.volume := by
    have hchange :=
      MeasureTheory.Measure.setIntegral_comp_smul_of_pos
        (μ := MeasureTheory.volume)
        (f := fun x : Vec d => (u.dilate ha).toFun x)
        (s := U) ha
    have hpow_ne : a ^ d ≠ 0 := (pow_pos ha d).ne'
    change ∫ x in a • U, u.toFun (a⁻¹ • x) ∂MeasureTheory.volume = _
    have hchange' :
        ∫ y in U, u.toFun y ∂MeasureTheory.volume =
          (a ^ d)⁻¹ * ∫ x in a • U,
            u.toFun (a⁻¹ • x) ∂MeasureTheory.volume := by
      simpa only [dilate_toFun, smul_smul, inv_mul_cancel₀ ha.ne', one_smul,
        smul_eq_mul, Module.finrank_fin_fun] using hchange
    rw [hchange']
    field_simp [hpow_ne]
  unfold integralAverage
  rw [hsetIntegral, hvolume]
  by_cases hU_zero : (MeasureTheory.volume U).toReal = 0
  · simp [hU_zero]
  · field_simp [hU_zero, (pow_pos ha d).ne']

/-- The mean-subtracted scalar `L^p` seminorm under positive dilation. -/
theorem subAverageLpSeminorm_dilate_eq {a : ℝ} (ha : 0 < a) (hp_top : p ≠ ∞)
    (u : W1pFunction U p) :
    (u.dilate ha).subAverageLpSeminorm =
      dilationLpFactor d p a * u.subAverageLpSeminorm := by
  unfold subAverageLpSeminorm dilationLpFactor
  rw [integralAverage_dilate_eq ha u]
  have hsub_meas :
      MeasureTheory.AEStronglyMeasurable
        (fun x => u.toFun x - integralAverage U u.toFun) (volumeMeasureOn U) :=
    u.memLp.aestronglyMeasurable.sub MeasureTheory.aestronglyMeasurable_const
  change
    (MeasureTheory.eLpNorm
      (fun x => u.toFun (a⁻¹ • x) - integralAverage U u.toFun) p
      (volumeMeasureOn (a • U))).toReal = _
  have hfun :
      (fun x => u.toFun (a⁻¹ • x) - integralAverage U u.toFun) =
        fun x => (fun y => u.toFun y - integralAverage U u.toFun) (a⁻¹ • x) := rfl
  rw [hfun]
  rw [eLpNorm_comp_dilate_eq ha hp_top hsub_meas, ENNReal.toReal_mul]

end W1pFunction

end

end Homogenization
