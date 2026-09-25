/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Coercive H1Dilation -/

@[expose] public section

namespace Homogenization

open scoped ENNReal Pointwise

noncomputable section

/-- Scaling by a positive scalar maps restricted Lebesgue measure on `U` to the
corresponding scalar multiple of restricted Lebesgue measure on `a • U`. -/
theorem map_smul_volume_restrict {d : ℕ} {a : ℝ} (ha : 0 < a)
    (U : Set (Vec d)) :
    MeasureTheory.Measure.map (fun x : Vec d => a • x)
        (MeasureTheory.volume.restrict U) =
      ENNReal.ofReal ((a ^ d)⁻¹) • MeasureTheory.volume.restrict (a • U) := by
  have ha_ne : a ≠ 0 := ha.ne'
  let e : Homeomorph (Vec d) (Vec d) := Homeomorph.smulOfNeZero a ha_ne
  have heq : (fun x : Vec d => e x) = fun x : Vec d => a • x := rfl
  have hrestrict :
      MeasureTheory.Measure.map (fun x : Vec d => a • x)
          (MeasureTheory.volume.restrict U) =
        (MeasureTheory.Measure.map (fun x : Vec d => a • x) MeasureTheory.volume).restrict
          (a • U) := by
    have htmp :
        (MeasureTheory.volume.restrict U).map e =
          (MeasureTheory.volume.map e).restrict (e '' U) := by
      have h :=
        ((e.toMeasurableEquiv.restrict_map
          (μ := MeasureTheory.volume) (s := e '' U)).symm)
      simpa [Set.preimage_image_eq _ e.injective] using h
    simpa [heq] using htmp
  have hmap :
      MeasureTheory.Measure.map (fun x : Vec d => a • x) MeasureTheory.volume =
        ENNReal.ofReal ((a ^ d)⁻¹) • MeasureTheory.volume := by
    let f : Vec d →ₗ[ℝ] Vec d := a • (1 : Vec d →ₗ[ℝ] Vec d)
    have hf : LinearMap.det f ≠ 0 := by
      simp [f, ha_ne]
    have hdet : LinearMap.det f = a ^ d := by
      simp [f]
    have hmapf :=
      Real.map_linearMap_volume_pi_eq_smul_volume_pi
        (ι := Fin d) (f := f) hf
    have hpow_inv_nonneg : 0 ≤ (a ^ d)⁻¹ := by
      positivity
    rw [hdet] at hmapf
    simpa [f, abs_of_nonneg hpow_inv_nonneg] using! hmapf
  rw [hrestrict, hmap, MeasureTheory.Measure.restrict_smul]

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- Push an `H¹(U)` witness forward to `H¹(a • U)` by the dilation
`x ↦ a⁻¹ x`, with the value normalized by the factor `a`.  With this
normalization the gradient is the plain pullback of the original gradient. -/
noncomputable def dilate {a : ℝ} (ha : 0 < a)
    (u : H1Function U) : H1Function (a • U) := by
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
    { toFun := fun x => a * u.toFun (T x)
      grad := fun x => u.grad (T x)
      memL2 := ?_
      gradMemL2 := ?_
      hasWeakGradient := ?_ }
  · have hu_map : MeasureTheory.MemLp u.toFun 2
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) := by
      rw [hmap, hpre]
      exact u.memL2.smul_measure ENNReal.ofReal_ne_top
    exact (MeasureTheory.MemLp.comp_of_map hu_map hT_meas).const_mul a
  · intro i
    have hgrad_map : MeasureTheory.MemLp (fun x => u.grad x i) 2
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) := by
      rw [hmap, hpre]
      exact (u.gradMemL2 i).smul_measure ENNReal.ofReal_ne_top
    exact MeasureTheory.MemLp.comp_of_map hgrad_map hT_meas
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
        ∫ y in U, a * (u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i))
            ∂MeasureTheory.volume =
          (a ^ d)⁻¹ * ∫ x in V,
            a * u.toFun (T x) * (fderiv ℝ φ x) (basisVec i)
              ∂MeasureTheory.volume := by
      simpa only [V, T, smul_smul, inv_mul_cancel₀ ha_ne, one_smul, smul_eq_mul,
        Module.finrank_fin_fun, mul_assoc] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun x : Vec d =>
            a * u.toFun (T x) * (fderiv ℝ φ x) (basisVec i))
          (s := U) ha)
    have hchange_right :
        ∫ y in U, u.grad y i * φ (a • y) ∂MeasureTheory.volume =
          (a ^ d)⁻¹ * ∫ x in V, u.grad (T x) i * φ x ∂MeasureTheory.volume := by
      simpa only [V, T, smul_smul, inv_mul_cancel₀ ha_ne, one_smul, smul_eq_mul,
        Module.finrank_fin_fun] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun x : Vec d => u.grad (T x) i * φ x)
          (s := U) ha)
    have hscale_left :
        ∫ y in U, a * (u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i))
            ∂MeasureTheory.volume =
          a * ∫ y in U, u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume := by
      rw [MeasureTheory.integral_const_mul]
    calc
      ∫ x in V, a * u.toFun (T x) * (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume
          = (a ^ d) * ∫ y in U,
              a * (u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i))
                ∂MeasureTheory.volume := by
            have hpos : (a ^ d) ≠ 0 := (pow_pos ha d).ne'
            rw [hchange_left]
            field_simp [hpos]
      _ = (a ^ d) *
            (a * ∫ y in U, u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i)
              ∂MeasureTheory.volume) := by
            rw [hscale_left]
      _ = (a ^ d) * (-∫ y in U, u.grad y i * φ (a • y)
              ∂MeasureTheory.volume) := by
            rw [hweak_scaled]
      _ = -((a ^ d) * ∫ y in U, u.grad y i * φ (a • y)
              ∂MeasureTheory.volume) := by
            ring
      _ = -∫ x in V, u.grad (T x) i * φ x ∂MeasureTheory.volume := by
            have hpos : (a ^ d) ≠ 0 := (pow_pos ha d).ne'
            rw [hchange_right]
            field_simp [hpos]

@[simp] theorem dilate_toFun {a : ℝ} (ha : 0 < a)
    (u : H1Function U) (x : Vec d) :
    (u.dilate ha).toFun x = a * u.toFun (a⁻¹ • x) :=
  rfl

@[simp] theorem dilate_grad {a : ℝ} (ha : 0 < a)
    (u : H1Function U) (x : Vec d) :
    (u.dilate ha).grad x = u.grad (a⁻¹ • x) :=
  rfl

/-- Push an `H¹(U)` witness forward to any domain `V` that is propositionally
equal to `a • U`.  This avoids casts when geometric APIs identify the dilated
set by an extensional equality. -/
noncomputable def dilateSet {V : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (hV : V = a • U) (u : H1Function U) : H1Function V := by
  let T : Vec d → Vec d := fun x => a⁻¹ • x
  have ha_ne : a ≠ 0 := ha.ne'
  have hmap := map_smul_volume_restrict (d := d) (a := a⁻¹) (inv_pos.mpr ha) V
  have hpre : a⁻¹ • V = U := by
    rw [hV]
    ext x
    simp [ha_ne]
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict V) :=
    (measurable_const_smul a⁻¹).aemeasurable
  refine
    { toFun := fun x => a * u.toFun (T x)
      grad := fun x => u.grad (T x)
      memL2 := ?_
      gradMemL2 := ?_
      hasWeakGradient := ?_ }
  · have hu_map : MeasureTheory.MemLp u.toFun 2
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) := by
      rw [hmap, hpre]
      exact u.memL2.smul_measure ENNReal.ofReal_ne_top
    exact (MeasureTheory.MemLp.comp_of_map hu_map hT_meas).const_mul a
  · intro i
    have hgrad_map : MeasureTheory.MemLp (fun x => u.grad x i) 2
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict V)) := by
      rw [hmap, hpre]
      exact (u.gradMemL2 i).smul_measure ENNReal.ofReal_ne_top
    exact MeasureTheory.MemLp.comp_of_map hgrad_map hT_meas
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
      rw [hV] at hyV
      simpa [Set.mem_smul_set_iff_inv_smul_mem, ha_ne] using hyV
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
        ∫ y in U, a * (u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i))
            ∂MeasureTheory.volume =
          (a ^ d)⁻¹ * ∫ x in V,
            a * u.toFun (T x) * (fderiv ℝ φ x) (basisVec i)
              ∂MeasureTheory.volume := by
      rw [hV]
      simpa only [T, smul_smul, inv_mul_cancel₀ ha_ne, one_smul, smul_eq_mul,
        Module.finrank_fin_fun, mul_assoc] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun x : Vec d =>
            a * u.toFun (T x) * (fderiv ℝ φ x) (basisVec i))
          (s := U) ha)
    have hchange_right :
        ∫ y in U, u.grad y i * φ (a • y) ∂MeasureTheory.volume =
          (a ^ d)⁻¹ * ∫ x in V, u.grad (T x) i * φ x ∂MeasureTheory.volume := by
      rw [hV]
      simpa only [T, smul_smul, inv_mul_cancel₀ ha_ne, one_smul, smul_eq_mul,
        Module.finrank_fin_fun] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun x : Vec d => u.grad (T x) i * φ x)
          (s := U) ha)
    have hscale_left :
        ∫ y in U, a * (u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i))
            ∂MeasureTheory.volume =
          a * ∫ y in U, u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i)
            ∂MeasureTheory.volume := by
      rw [MeasureTheory.integral_const_mul]
    calc
      ∫ x in V, a * u.toFun (T x) * (fderiv ℝ φ x) (basisVec i)
          ∂MeasureTheory.volume
          = (a ^ d) * ∫ y in U,
              a * (u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i))
                ∂MeasureTheory.volume := by
            have hpos : (a ^ d) ≠ 0 := (pow_pos ha d).ne'
            rw [hchange_left]
            field_simp [hpos]
      _ = (a ^ d) *
            (a * ∫ y in U, u.toFun y * (fderiv ℝ φ (a • y)) (basisVec i)
              ∂MeasureTheory.volume) := by
            rw [hscale_left]
      _ = (a ^ d) * (-∫ y in U, u.grad y i * φ (a • y)
              ∂MeasureTheory.volume) := by
            rw [hweak_scaled]
      _ = -((a ^ d) * ∫ y in U, u.grad y i * φ (a • y)
              ∂MeasureTheory.volume) := by
            ring
      _ = -∫ x in V, u.grad (T x) i * φ x ∂MeasureTheory.volume := by
            have hpos : (a ^ d) ≠ 0 := (pow_pos ha d).ne'
            rw [hchange_right]
            field_simp [hpos]

@[simp] theorem dilateSet_toFun {V : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (hV : V = a • U) (u : H1Function U) (x : Vec d) :
    (u.dilateSet ha hV).toFun x = a * u.toFun (a⁻¹ • x) :=
  rfl

@[simp] theorem dilateSet_grad {V : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (hV : V = a • U) (u : H1Function U) (x : Vec d) :
    (u.dilateSet ha hV).grad x = u.grad (a⁻¹ • x) :=
  rfl

/-- Pull an `H¹(a • U)` witness back to `H¹(U)` by precomposition with
`x ↦ a • x`. The weak gradient is `a • ∇u(a x)`. -/
noncomputable def unscale {a : ℝ} (ha : 0 < a)
    (u : H1Function (a • U)) : H1Function U := by
  let V : Set (Vec d) := a • U
  let T : Vec d → Vec d := fun x => a • x
  have ha_ne : a ≠ 0 := ha.ne'
  have hmap := map_smul_volume_restrict (d := d) (a := a) ha U
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict U) :=
    (measurable_const_smul a).aemeasurable
  refine
    { toFun := fun x => u (T x)
      grad := fun x => a • u.grad (T x)
      memL2 := ?_
      gradMemL2 := ?_
      hasWeakGradient := ?_ }
  · have hu_map : MemL2On V u.toFun := u.memL2
    have hu_smul :
        MeasureTheory.MemLp u.toFun 2
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
      rw [hmap]
      exact hu_map.smul_measure ENNReal.ofReal_ne_top
    exact MeasureTheory.MemLp.comp_of_map hu_smul hT_meas
  · intro i
    have hgrad_map : MemL2On V (fun x => u.grad x i) := u.gradMemL2 i
    have hgrad_smul_measure :
        MeasureTheory.MemLp (fun x => u.grad x i) 2
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
      rw [hmap]
      exact hgrad_map.smul_measure ENNReal.ofReal_ne_top
    have hcomp :
        MeasureTheory.MemLp (fun x => u.grad (T x) i) 2
          (MeasureTheory.volume.restrict U) :=
      MeasureTheory.MemLp.comp_of_map hgrad_smul_measure hT_meas
    have hmul : MeasureTheory.MemLp (fun x => a * u.grad (T x) i) 2
        (MeasureTheory.volume.restrict U) :=
      hcomp.const_mul a
    simpa [Pi.smul_apply, T, smul_eq_mul] using hmul
  · intro i φ hφ hφ_supp hφ_sub
    let ψ : Vec d → ℝ := fun y => φ (a⁻¹ • y)
    have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
      simpa [ψ] using! hφ.comp (contDiff_const_smul a⁻¹)
    have hψ_supp : HasCompactSupport ψ := by
      show HasCompactSupport (φ ∘ Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha_ne))
      simpa [ψ, Function.comp] using
        hφ_supp.comp_homeomorph (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha_ne))
    have hψ_sub : tsupport ψ ⊆ V := by
      intro y hy
      have hy' : a⁻¹ • y ∈ tsupport φ := by
        rw [show ψ = φ ∘ Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha_ne) by rfl,
          tsupport_comp_eq_preimage φ (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha_ne))] at hy
        exact hy
      exact ⟨a⁻¹ • y, hφ_sub hy', by simp [ha_ne, smul_smul]⟩
    have hweak := u.hasWeakGradient i ψ hψ_smooth hψ_supp hψ_sub
    have hderivψ :
        ∀ y : Vec d,
          (fderiv ℝ ψ y) (basisVec i) =
            a⁻¹ * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i) := by
      intro y
      have hderiv :
          fderiv ℝ (fun z : Vec d => φ (a⁻¹ • z)) y =
            a⁻¹ • fderiv ℝ φ (a⁻¹ • y) := by
        simpa [ψ] using (fderiv_comp_smul (𝕜 := ℝ) (f := φ) (x := y) a⁻¹)
      simpa [smul_eq_mul] using congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hderiv
    have hweak_scaled :
        ∫ y in V,
            u y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i) ∂MeasureTheory.volume =
          -a * ∫ y in V, u.grad y i * φ (a⁻¹ • y) ∂MeasureTheory.volume := by
      have hfun :
          (fun y => u y * (fderiv ℝ ψ y) (basisVec i)) =
            fun y => a⁻¹ * (u y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i)) := by
        funext y
        rw [hderivψ y]
        ring
      have hleft :
          ∫ y in V, u y * (fderiv ℝ ψ y) (basisVec i) ∂MeasureTheory.volume =
            a⁻¹ * ∫ y in V,
              u y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i) ∂MeasureTheory.volume := by
        rw [hfun, MeasureTheory.integral_const_mul]
      rw [hleft] at hweak
      have hmul := congrArg (fun t : ℝ => a * t) hweak
      have hcancel : a * (a⁻¹ *
          ∫ y in V, u y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i) ∂MeasureTheory.volume) =
          ∫ y in V, u y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i) ∂MeasureTheory.volume := by
        field_simp [ha_ne]
      simpa [hcancel, mul_neg, mul_assoc, mul_comm, mul_left_comm] using hmul
    have hchange_left :
        ∫ x in U, u (T x) * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
          (a ^ d)⁻¹ * ∫ y in V,
            u y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i) ∂MeasureTheory.volume := by
      simpa only [V, T, smul_smul, inv_mul_cancel₀ ha_ne, one_smul, smul_eq_mul,
        Module.finrank_fin_fun] using
        (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
          (μ := MeasureTheory.volume)
          (f := fun y : Vec d => u y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i))
          (s := U) ha)
    have hchange_right :
        ∫ x in U, (a • u.grad (T x)) i * φ x ∂MeasureTheory.volume =
          (a ^ d)⁻¹ *
            ∫ y in V, (a • u.grad y) i * φ (a⁻¹ • y) ∂MeasureTheory.volume := by
      simpa only [V, T, smul_smul, inv_mul_cancel₀ ha_ne, one_smul, smul_eq_mul,
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
      ∫ x in U, u (T x) * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume
          = (a ^ d)⁻¹ * ∫ y in V,
              u y * (fderiv ℝ φ (a⁻¹ • y)) (basisVec i) ∂MeasureTheory.volume :=
            hchange_left
      _ = (a ^ d)⁻¹ *
            (-a * ∫ y in V, u.grad y i * φ (a⁻¹ • y) ∂MeasureTheory.volume) := by
            rw [hweak_scaled]
      _ = -((a ^ d)⁻¹ *
            ∫ y in V, (a • u.grad y) i * φ (a⁻¹ • y) ∂MeasureTheory.volume) := by
            rw [hgrad_scaled_integral]
            ring
      _ = -∫ x in U, (a • u.grad (T x)) i * φ x ∂MeasureTheory.volume := by
            rw [hchange_right]

@[simp] theorem unscale_toFun {d : ℕ} {U : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (u : H1Function (a • U)) (x : Vec d) :
    (u.unscale ha).toFun x = u.toFun (a • x) := rfl

@[simp] theorem unscale_grad {d : ℕ} {U : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (u : H1Function (a • U)) (x : Vec d) :
    (u.unscale ha).grad x = a • u.grad (a • x) := rfl

/-- Pull an `H¹(V)` witness back to `H¹(U)` when `V = a • U`, with the
normalization inverse to `H1Function.dilateSet`: `u(a x) / a`. -/
noncomputable def undilateSet {V : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (hV : V = a • U) (u : H1Function V) : H1Function U := by
  subst V
  exact a⁻¹ • u.unscale ha

@[simp] theorem undilateSet_toFun {V : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (hV : V = a • U) (u : H1Function V) (x : Vec d) :
    (u.undilateSet ha hV).toFun x = a⁻¹ * u.toFun (a • x) := by
  subst V
  simp [undilateSet]

@[simp] theorem undilateSet_grad {V : Set (Vec d)} {a : ℝ} (ha : 0 < a)
    (hV : V = a • U) (u : H1Function V) (x : Vec d) :
    (u.undilateSet ha hV).grad x = u.grad (a • x) := by
  subst V
  ext i
  simp [undilateSet, Pi.smul_apply, smul_eq_mul, ha.ne']

end H1Function

namespace H10Function

variable {d : ℕ} {U : Set (Vec d)}

/-- Pull an `H¹₀(a • U)` witness back to `H¹₀(U)` by precomposition with
`x ↦ a x`. -/
noncomputable def unscale {a : ℝ} (ha : 0 < a)
    (u : H10Function (a • U)) : H10Function U := by
  let V : Set (Vec d) := a • U
  let T : Vec d → Vec d := fun x => a • x
  have ha_ne : a ≠ 0 := ha.ne'
  have hmap := map_smul_volume_restrict (d := d) (a := a) ha U
  let C : ℝ≥0∞ := ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)
  have hC_ne_top : C ≠ ⊤ := by
    simp [C]
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict U) :=
    (measurable_const_smul a).aemeasurable
  refine
    { toH1Function := u.toH1Function.unscale ha
      approx := fun m x => u.approx m (T x)
      approx_smooth := ?_
      approx_hasCompactSupport := ?_
      approx_support_subset := ?_
      tendsto_approx := ?_
      tendsto_approx_grad := ?_ }
  · intro m
    simpa [T] using! (u.approx_smooth m).comp (contDiff_const_smul a)
  · intro m
    show HasCompactSupport (u.approx m ∘ Homeomorph.smulOfNeZero a ha_ne)
    simpa [T, Function.comp] using
      (u.approx_hasCompactSupport m).comp_homeomorph (Homeomorph.smulOfNeZero a ha_ne)
  · intro m x hx
    have hx' : a • x ∈ tsupport (u.approx m) := by
      rw [show (fun y => u.approx m (T y)) =
            u.approx m ∘ Homeomorph.smulOfNeZero a ha_ne by rfl,
        tsupport_comp_eq_preimage (u.approx m) (Homeomorph.smulOfNeZero a ha_ne)] at hx
      exact hx
    have hV : a • x ∈ V := u.approx_support_subset m hx'
    simpa [V, Set.mem_smul_set_iff_inv_smul_mem, ha_ne] using hV
  · have hEq :
        (fun m =>
          MeasureTheory.eLpNorm
            (fun x => u.approx m (T x) - (u.toH1Function.unscale ha).toFun x)
            2 (MeasureTheory.volume.restrict U)) =
          fun m => C * MeasureTheory.eLpNorm
            (fun x => u.approx m x - u.toH1Function.toFun x)
            2 (MeasureTheory.volume.restrict V) := by
      funext m
      let g : Vec d → ℝ := fun x => u.approx m x - u.toH1Function.toFun x
      have hg_map : MeasureTheory.AEStronglyMeasurable g
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
        rw [hmap]
        exact ((u.approx_smooth m).continuous.aestronglyMeasurable.sub
          u.toH1Function.memL2.aestronglyMeasurable).mono_ac
            MeasureTheory.Measure.smul_absolutelyContinuous
      have hmap_eLp :
          MeasureTheory.eLpNorm g 2
              (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) =
            MeasureTheory.eLpNorm (fun x => g (T x)) 2
              (MeasureTheory.volume.restrict U) := by
        exact (MeasureTheory.eLpNorm_map_measure
          (g := g) (f := T) hg_map hT_meas)
      have hfun :
          (fun x => u.approx m (T x) - (u.toH1Function.unscale ha).toFun x) =
            fun x => g (T x) := by
        funext x
        simp [g, T]
      rw [hfun, ← hmap_eLp, hmap]
      rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero]
      · rfl
      · simp [pow_pos ha d]
    rw [hEq]
    simpa [V] using ENNReal.Tendsto.const_mul u.tendsto_approx (Or.inr hC_ne_top)
  · intro k
    have hEq :
        (fun m =>
          MeasureTheory.eLpNorm
            (fun x =>
              (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                (u.toH1Function.unscale ha).grad x k)
            2 (MeasureTheory.volume.restrict U)) =
          fun m => (ENNReal.ofReal a * C) * MeasureTheory.eLpNorm
            (fun x => (fderiv ℝ (u.approx m) x) (basisVec k) -
              u.toH1Function.grad x k)
            2 (MeasureTheory.volume.restrict V) := by
      funext m
      let g : Vec d → ℝ :=
        fun x => (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k
      have hg_map : MeasureTheory.AEStronglyMeasurable g
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
        rw [hmap]
        exact (((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
          continuous_const |>.aestronglyMeasurable.sub
            (u.toH1Function.gradMemL2 k).aestronglyMeasurable).mono_ac
              MeasureTheory.Measure.smul_absolutelyContinuous
      have hmap_eLp :
          MeasureTheory.eLpNorm g 2
              (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) =
            MeasureTheory.eLpNorm (fun x => g (T x)) 2
              (MeasureTheory.volume.restrict U) := by
        exact (MeasureTheory.eLpNorm_map_measure
          (g := g) (f := T) hg_map hT_meas)
      have hfun :
          (fun x =>
              (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                (u.toH1Function.unscale ha).grad x k) =
            fun x => a * g (T x) := by
        funext x
        have hderiv :
            fderiv ℝ (fun y : Vec d => u.approx m (a • y)) x =
              a • fderiv ℝ (u.approx m) (a • x) := by
          simpa [T] using (fderiv_comp_smul (𝕜 := ℝ) (f := u.approx m) (x := x) a)
        simp [g, T, hderiv, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hfun]
      change MeasureTheory.eLpNorm (a • fun x => g (T x)) 2
          (MeasureTheory.volume.restrict U) =
        ENNReal.ofReal a * C * MeasureTheory.eLpNorm g 2
          (MeasureTheory.volume.restrict V)
      rw [MeasureTheory.eLpNorm_const_smul]
      rw [Real.enorm_eq_ofReal ha.le]
      rw [← hmap_eLp, hmap]
      rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero]
      · simp [C, V, smul_eq_mul, mul_assoc]
      · simp [pow_pos ha d]
    rw [hEq]
    have hconst_ne_top : ENNReal.ofReal a * C ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hC_ne_top
    simpa [V] using
      ENNReal.Tendsto.const_mul (u.tendsto_approx_grad k) (Or.inr hconst_ne_top)

@[simp] theorem unscale_toH1Function {a : ℝ} (ha : 0 < a)
    (u : H10Function (a • U)) :
    (u.unscale ha).toH1Function = u.toH1Function.unscale ha :=
  rfl

end H10Function

/-- The common `L²` measure factor produced by pulling back along
`x ↦ a • x`. -/
noncomputable def dilationL2Factor (d : ℕ) (a : ℝ) : ℝ :=
  (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal

theorem dilationL2Factor_eq {d : ℕ} {a : ℝ} (ha : 0 < a) :
    dilationL2Factor d a = ((a ^ d)⁻¹) ^ (1 / 2 : ℝ) := by
  have hhalf : ((1 / (2 : ℝ≥0∞)).toReal : ℝ) = (1 / 2 : ℝ) := by
    norm_num
  have hbase_nonneg : 0 ≤ (a ^ d)⁻¹ := by
    positivity
  unfold dilationL2Factor
  rw [hhalf]
  rw [ENNReal.ofReal_rpow_of_nonneg hbase_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hbase_nonneg _)]

theorem dilationL2Factor_pos {d : ℕ} {a : ℝ} (ha : 0 < a) :
    0 < dilationL2Factor d a := by
  rw [dilationL2Factor_eq (d := d) ha]
  exact Real.rpow_pos_of_pos (inv_pos.mpr (pow_pos ha d)) _

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)}

/-- The scalar `L²` norm of an `H¹` function after dilation pullback. -/
theorem norm_toScalarL2_unscale_eq {a : ℝ} (ha : 0 < a)
    (u : H1Function (a • U)) :
    ‖(u.unscale ha).toScalarL2‖ =
      dilationL2Factor d a * ‖u.toScalarL2‖ := by
  let T : Vec d → Vec d := fun x => a • x
  have hmap := map_smul_volume_restrict (d := d) (a := a) ha U
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict U) :=
    (measurable_const_smul a).aemeasurable
  have hu_aesm_map :
      MeasureTheory.AEStronglyMeasurable u.toFun
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
    rw [hmap]
    exact u.memL2.aestronglyMeasurable.mono_ac
      MeasureTheory.Measure.smul_absolutelyContinuous
  have hmap_eLp :
      MeasureTheory.eLpNorm u.toFun (2 : ℝ≥0∞)
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) =
        MeasureTheory.eLpNorm (fun x => u.toFun (T x)) (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict U) := by
    exact
      (MeasureTheory.eLpNorm_map_measure
        (g := u.toFun) (f := T) hu_aesm_map hT_meas)
  unfold H1Function.toScalarL2 Homogenization.toScalarL2 dilationL2Factor
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  change
    (MeasureTheory.eLpNorm (fun x => u.toFun (T x)) (2 : ℝ≥0∞)
      (MeasureTheory.volume.restrict U)).toReal =
      (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal *
        (MeasureTheory.eLpNorm u.toFun (2 : ℝ≥0∞)
          (volumeMeasureOn (a • U))).toReal
  rw [← hmap_eLp, hmap]
  rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero]
  · change
      ((ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
          MeasureTheory.eLpNorm u.toFun (2 : ℝ≥0∞)
            (MeasureTheory.volume.restrict (a • U))).toReal) =
        (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal *
          (MeasureTheory.eLpNorm u.toFun (2 : ℝ≥0∞)
            (volumeMeasureOn (a • U))).toReal
    rw [ENNReal.toReal_mul]
  · simp [pow_pos ha d]

/-- The coordinate-gradient `L²` norm of an `H¹` function after dilation
pullback. -/
theorem norm_gradCoordToScalarL2_unscale_eq {a : ℝ} (ha : 0 < a)
    (u : H1Function (a • U)) (i : Fin d) :
    ‖(u.unscale ha).gradCoordToScalarL2 i‖ =
      a * dilationL2Factor d a * ‖u.gradCoordToScalarL2 i‖ := by
  let T : Vec d → Vec d := fun x => a • x
  have hmap := map_smul_volume_restrict (d := d) (a := a) ha U
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict U) :=
    (measurable_const_smul a).aemeasurable
  have hgrad_aesm_map :
      MeasureTheory.AEStronglyMeasurable (fun x => u.grad x i)
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
    rw [hmap]
    exact (u.grad_memL2 i).aestronglyMeasurable.mono_ac
      MeasureTheory.Measure.smul_absolutelyContinuous
  have hmap_eLp :
      MeasureTheory.eLpNorm (fun x => u.grad x i) (2 : ℝ≥0∞)
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) =
        MeasureTheory.eLpNorm (fun x => u.grad (T x) i) (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict U) := by
    exact
      (MeasureTheory.eLpNorm_map_measure
        (g := fun x => u.grad x i) (f := T) hgrad_aesm_map hT_meas)
  unfold H1Function.gradCoordToScalarL2 Homogenization.toScalarL2 dilationL2Factor
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  change
    (MeasureTheory.eLpNorm (fun x => (a • u.grad (T x)) i) (2 : ℝ≥0∞)
      (MeasureTheory.volume.restrict U)).toReal =
      a * (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal *
        (MeasureTheory.eLpNorm (fun x => u.grad x i) (2 : ℝ≥0∞)
          (volumeMeasureOn (a • U))).toReal
  have hfun :
      (fun x : Vec d => (a • u.grad (T x)) i) =
        a • fun x : Vec d => u.grad (T x) i := rfl
  rw [hfun]
  rw [MeasureTheory.eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal (le_of_lt ha)]
  rw [← hmap_eLp, hmap]
  rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero]
  · change
      ((ENNReal.ofReal a *
          (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
            MeasureTheory.eLpNorm (fun x => u.grad x i) (2 : ℝ≥0∞)
              (MeasureTheory.volume.restrict (a • U)))).toReal) =
        a * (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal *
          (MeasureTheory.eLpNorm (fun x => u.grad x i) (2 : ℝ≥0∞)
            (volumeMeasureOn (a • U))).toReal
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le]
    ring
  · simp [pow_pos ha d]

/-- The coordinate-gradient norm sum after dilation pullback. -/
theorem gradientCoordL2NormSum_unscale_eq {a : ℝ} (ha : 0 < a)
    (u : H1Function (a • U)) :
    (u.unscale ha).gradientCoordL2NormSum =
      a * dilationL2Factor d a * u.gradientCoordL2NormSum := by
  unfold H1Function.gradientCoordL2NormSum
  calc
    ∑ i, ‖(u.unscale ha).gradCoordToScalarL2 i‖ =
        ∑ i, a * dilationL2Factor d a * ‖u.gradCoordToScalarL2 i‖ := by
          apply Finset.sum_congr rfl
          intro i _
          exact H1Function.norm_gradCoordToScalarL2_unscale_eq ha u i
    _ = a * dilationL2Factor d a * ∑ i, ‖u.gradCoordToScalarL2 i‖ := by
          rw [← Finset.mul_sum]

end H1Function

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)}

/-- Pull a mean-zero `H¹(a • U)` witness back to `H¹(U)`. -/
noncomputable def unscale {a : ℝ} (ha : 0 < a)
    (u : H1MeanZeroFunction (a • U)) : H1MeanZeroFunction U where
  toH1Function := u.toH1Function.unscale ha
  meanZero := by
    change ∫ x in U, u.toH1Function.toFun (a • x) ∂MeasureTheory.volume = 0
    rw [MeasureTheory.Measure.setIntegral_comp_smul_of_pos
      (μ := MeasureTheory.volume) (f := u.toH1Function.toFun) (s := U) ha]
    rw [u.meanZero]
    simp

@[simp] theorem unscale_toH1Function {a : ℝ} (ha : 0 < a)
    (u : H1MeanZeroFunction (a • U)) :
    (u.unscale ha).toH1Function = u.toH1Function.unscale ha :=
  rfl

@[simp] theorem unscale_apply {a : ℝ} (ha : 0 < a)
    (u : H1MeanZeroFunction (a • U)) (x : Vec d) :
    u.unscale ha x = u (a • x) :=
  rfl

@[simp] theorem unscale_grad {a : ℝ} (ha : 0 < a)
    (u : H1MeanZeroFunction (a • U)) (x : Vec d) :
    (u.unscale ha).toH1Function.grad x = a • u.toH1Function.grad (a • x) :=
  rfl

/-- The scalar `L²` norm after dilation pullback. -/
theorem valueL2Norm_unscale_eq {a : ℝ} (ha : 0 < a)
    (u : H1MeanZeroFunction (a • U)) :
    (u.unscale ha).valueL2Norm =
      dilationL2Factor d a * u.valueL2Norm := by
  let V : Set (Vec d) := a • U
  let T : Vec d → Vec d := fun x => a • x
  have hmap := map_smul_volume_restrict (d := d) (a := a) ha U
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict U) :=
    (measurable_const_smul a).aemeasurable
  have hu_aesm_map :
      MeasureTheory.AEStronglyMeasurable u.toH1Function.toFun
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
    rw [hmap]
    exact u.toH1Function.memL2.aestronglyMeasurable.mono_ac
      MeasureTheory.Measure.smul_absolutelyContinuous
  have hmap_eLp :
      MeasureTheory.eLpNorm u.toH1Function.toFun (2 : ℝ≥0∞)
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) =
        MeasureTheory.eLpNorm (fun x => u.toH1Function.toFun (T x)) (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict U) := by
    exact
      (MeasureTheory.eLpNorm_map_measure
        (g := u.toH1Function.toFun) (f := T)
        hu_aesm_map hT_meas)
  unfold H1MeanZeroFunction.valueL2Norm H1MeanZeroFunction.toScalarL2
    H1Function.toScalarL2 Homogenization.toScalarL2 dilationL2Factor
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  change
    (MeasureTheory.eLpNorm (fun x => u.toH1Function.toFun (T x)) (2 : ℝ≥0∞)
      (MeasureTheory.volume.restrict U)).toReal =
      (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal *
        (MeasureTheory.eLpNorm u.toH1Function.toFun (2 : ℝ≥0∞)
          (volumeMeasureOn (a • U))).toReal
  rw [← hmap_eLp, hmap]
  rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero]
  · change
      ((ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
          MeasureTheory.eLpNorm u.toH1Function.toFun (2 : ℝ≥0∞)
            (MeasureTheory.volume.restrict (a • U))).toReal) =
        (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal *
          (MeasureTheory.eLpNorm u.toH1Function.toFun (2 : ℝ≥0∞)
            (volumeMeasureOn (a • U))).toReal
    rw [ENNReal.toReal_mul]
  · simp [pow_pos ha d]

/-- The gradient `L²` norm after dilation pullback. -/
theorem gradientL2Norm_unscale_eq {a : ℝ} (ha : 0 < a)
    (u : H1MeanZeroFunction (a • U)) :
    (u.unscale ha).gradientL2Norm =
      a * dilationL2Factor d a * u.gradientL2Norm := by
  let V : Set (Vec d) := a • U
  let T : Vec d → Vec d := fun x => a • x
  have hmap := map_smul_volume_restrict (d := d) (a := a) ha U
  have hT_meas : AEMeasurable T (MeasureTheory.volume.restrict U) :=
    (measurable_const_smul a).aemeasurable
  have hgrad_aesm_map :
      MeasureTheory.AEStronglyMeasurable u.toH1Function.grad
        (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) := by
    rw [hmap]
    exact u.toH1Function.grad_memVectorL2.aestronglyMeasurable.mono_ac
      MeasureTheory.Measure.smul_absolutelyContinuous
  have hmap_eLp :
      MeasureTheory.eLpNorm u.toH1Function.grad (2 : ℝ≥0∞)
          (MeasureTheory.Measure.map T (MeasureTheory.volume.restrict U)) =
        MeasureTheory.eLpNorm (fun x => u.toH1Function.grad (T x)) (2 : ℝ≥0∞)
          (MeasureTheory.volume.restrict U) := by
    exact
      (MeasureTheory.eLpNorm_map_measure
        (g := u.toH1Function.grad) (f := T)
        hgrad_aesm_map hT_meas)
  unfold H1MeanZeroFunction.gradientL2Norm H1MeanZeroFunction.gradToVectorL2
    H1Function.gradToVectorL2 Homogenization.toVectorL2 dilationL2Factor
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  change
    (MeasureTheory.eLpNorm (fun x => a • u.toH1Function.grad (T x)) (2 : ℝ≥0∞)
      (MeasureTheory.volume.restrict U)).toReal =
      a * (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal *
        (MeasureTheory.eLpNorm u.toH1Function.grad (2 : ℝ≥0∞)
          (volumeMeasureOn (a • U))).toReal
  have hfun :
      (fun x : Vec d => a • u.toH1Function.grad (T x)) =
        a • fun x : Vec d => u.toH1Function.grad (T x) := rfl
  rw [hfun]
  rw [MeasureTheory.eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal (le_of_lt ha)]
  rw [← hmap_eLp, hmap]
  rw [MeasureTheory.eLpNorm_smul_measure_of_ne_zero]
  · change
      ((ENNReal.ofReal a *
          (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
            MeasureTheory.eLpNorm u.toH1Function.grad (2 : ℝ≥0∞)
              (MeasureTheory.volume.restrict (a • U)))).toReal) =
        a * (ENNReal.ofReal ((a ^ d)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)).toReal *
          (MeasureTheory.eLpNorm u.toH1Function.grad (2 : ℝ≥0∞)
            (volumeMeasureOn (a • U))).toReal
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha.le]
    ring
  · simp [pow_pos ha d]

end H1MeanZeroFunction

namespace H1CoerciveEstimate

variable {d : ℕ} {U : Set (Vec d)}

/-- Dilation transports a mean-zero coercive `H¹` estimate from `U` to
`a • U`, multiplying the constant by the dilation factor `a`. -/
noncomputable def dilate {a : ℝ} (ha : 0 < a)
    (hC : H1CoerciveEstimate U) : H1CoerciveEstimate (a • U) where
  fixedValue := a * hC.fixedValue
  constant_nonneg := mul_nonneg ha.le hC.constant_nonneg
  bound := by
    intro u
    let v : H1MeanZeroFunction U := u.unscale ha
    have hv := hC.bound v
    have hvalue := H1MeanZeroFunction.valueL2Norm_unscale_eq (U := U) ha u
    have hgrad := H1MeanZeroFunction.gradientL2Norm_unscale_eq (U := U) ha u
    have hFpos : 0 < dilationL2Factor d a := dilationL2Factor_pos (d := d) ha
    have hscaled :
        dilationL2Factor d a * u.valueL2Norm ≤
          hC.fixedValue * (a * dilationL2Factor d a * u.gradientL2Norm) := by
      simpa [v, hvalue, hgrad] using hv
    have hscaled' :
        dilationL2Factor d a * u.valueL2Norm ≤
          dilationL2Factor d a * ((a * hC.fixedValue) * u.gradientL2Norm) := by
      calc
        dilationL2Factor d a * u.valueL2Norm
            ≤ hC.fixedValue * (a * dilationL2Factor d a * u.gradientL2Norm) := hscaled
        _ = dilationL2Factor d a * ((a * hC.fixedValue) * u.gradientL2Norm) := by
              ring
    exact (mul_le_mul_iff_right₀ hFpos).1 hscaled'

@[simp] theorem dilate_constant {d : ℕ} {U : Set (Vec d)} {a : ℝ}
    (ha : 0 < a) (hC : H1CoerciveEstimate U) :
    (hC.dilate ha).fixedValue = a * hC.fixedValue :=
  rfl

end H1CoerciveEstimate

end

end Homogenization
