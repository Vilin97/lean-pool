/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.Translation
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.BasicLemmas

/-! # Translation -/

namespace Homogenization

open scoped Topology

noncomputable section

namespace W1pFunction

/--
Translate a `W^{1,p}(U)` witness to `W^{1,p}(U + z)` by precomposing with
`x ↦ x - z`.
-/
noncomputable def translate {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
    (u : W1pFunction U p) (z : Vec d) :
    W1pFunction (translateSet z U) p := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x - z
  let hμ := measurePreserving_subRight_restrict_translateSet (d := d) z U
  refine
    { toFun := fun x => u (T x)
      grad := fun x => u.grad (T x)
      memLp := by
        show MemLpOn V p (u.toFun ∘ T)
        simpa [MemLpOn, V, T, Function.comp] using u.memLp.comp_measurePreserving hμ
      gradMemLp := by
        intro i
        show MemLpOn V p ((fun x => u.grad x i) ∘ T)
        simpa [MemLpOn, V, T, Function.comp] using (u.gradMemLp i).comp_measurePreserving hμ
      hasWeakGradient := ?_ }
  intro i φ hφ hφ_supp hφ_sub
  let ψ : Vec d → ℝ := fun x => φ (x + z)
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ] using! hφ.comp (contDiff_id.add contDiff_const)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (φ ∘ Homeomorph.addRight z)
    simpa [ψ, Function.comp] using hφ_supp.comp_homeomorph (Homeomorph.addRight z)
  have hψ_sub : tsupport ψ ⊆ U := by
    intro x hx
    have hx' : x + z ∈ tsupport φ := by
      rw [show ψ = φ ∘ Homeomorph.addRight z by rfl,
        tsupport_comp_eq_preimage φ (Homeomorph.addRight z)] at hx
      exact hx
    have hxV : x + z ∈ V := hφ_sub hx'
    simpa [V, mem_translateSet_iff_sub_mem, sub_eq_add_neg, add_assoc] using hxV
  have hweak := u.hasWeakGradient i ψ hψ_smooth hψ_supp hψ_sub
  have hmain :
      ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i) ∂MeasureTheory.volume =
        -∫ x in U, u.grad x i * φ (x + z) ∂MeasureTheory.volume := by
    have hfun :
        (fun x => u x * (fderiv ℝ φ (x + z)) (basisVec i)) =
          fun x => u x * (fderiv ℝ ψ x) (basisVec i) := by
      funext x
      have hderiv :
          fderiv ℝ (fun y : Vec d => φ (y + z)) x =
            fderiv ℝ φ (x + z) := by
        simpa using (fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := x) z)
      simp [ψ, hderiv]
    calc
      ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i) ∂MeasureTheory.volume
        = ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec i) ∂MeasureTheory.volume := by rw [hfun]
      _ = -∫ x in U, u.grad x i * ψ x ∂MeasureTheory.volume := hweak
      _ = -∫ x in U, u.grad x i * φ (x + z) ∂MeasureTheory.volume := by rfl
  have hchange_left :
      ∫ x in V, u (x - z) * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
        ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i) ∂MeasureTheory.volume := by
    symm
    simpa [V, T, sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) z U
        (fun x => u (x - z) * (fderiv ℝ φ x) (basisVec i)))
  have hchange_right :
      ∫ x in U, u.grad x i * φ (x + z) ∂MeasureTheory.volume =
        ∫ x in V, u.grad (x - z) i * φ x ∂MeasureTheory.volume := by
    simpa [V, T, sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) z U
        (fun x => u.grad (x - z) i * φ x))
  calc
    ∫ x in V, u (x - z) * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume
      = ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i) ∂MeasureTheory.volume := hchange_left
    _ = -∫ x in U, u.grad x i * φ (x + z) ∂MeasureTheory.volume := hmain
    _ = -∫ x in V, u.grad (x - z) i * φ x ∂MeasureTheory.volume := by rw [hchange_right]

@[simp] theorem translate_toFun {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
    (u : W1pFunction U p) (z : Vec d) (x : Vec d) :
    (u.translate z).toFun x = u.toFun (x - z) := rfl

@[simp] theorem translate_grad {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
    (u : W1pFunction U p) (z : Vec d) (x : Vec d) :
    (u.translate z).grad x = u.grad (x - z) := rfl

end W1pFunction

namespace W10pFunction

/--
Translate a `W^{1,p}_0(U)` witness to `W^{1,p}_0(U + z)` by precomposing with
`x ↦ x - z`.
-/
noncomputable def translate {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
    (u : W10pFunction U p) (z : Vec d) :
    W10pFunction (translateSet z U) p := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x - z
  let hμ := measurePreserving_subRight_restrict_translateSet (d := d) z U
  refine
    { toW1pFunction := u.toW1pFunction.translate z
      approx := fun m x => u.approx m (T x)
      approx_smooth := by
        intro m
        simpa [T, sub_eq_add_neg] using! (u.approx_smooth m).comp (contDiff_id.sub contDiff_const)
      approx_hasCompactSupport := by
        intro m
        show HasCompactSupport (u.approx m ∘ Homeomorph.subRight z)
        simpa [T, Function.comp] using
          (u.approx_hasCompactSupport m).comp_homeomorph (Homeomorph.subRight z)
      approx_support_subset := by
        intro m x hx
        have hx' : x - z ∈ tsupport (u.approx m) := by
          rw [show (fun y => u.approx m (T y)) = u.approx m ∘ Homeomorph.subRight z by rfl,
            tsupport_comp_eq_preimage (u.approx m) (Homeomorph.subRight z)] at hx
          exact hx
        exact (mem_translateSet_iff_sub_mem).2 (u.approx_support_subset m hx')
      tendsto_approx := by
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x => u.approx m (T x) - (u.toW1pFunction.translate z).toFun x)
                p (MeasureTheory.volume.restrict V)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x => u.approx m x - u.toW1pFunction.toFun x)
                  p (MeasureTheory.volume.restrict U)) := by
          funext m
          let g : Vec d → ℝ := fun x => u.approx m x - u.toW1pFunction.toFun x
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict U) := by
            exact (u.approx_smooth m).continuous.aestronglyMeasurable.sub
              u.toW1pFunction.memLp.aestronglyMeasurable
          have hfun :
              (fun x => u.approx m (T x) - (u.toW1pFunction.translate z).toFun x) = g ∘ T := by
            funext x
            simp [g, T, Function.comp, W1pFunction.translate]
          rw [hfun]
          simpa [g, T, Function.comp] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := p) hg hμ)
        rw [hEq]
        exact u.tendsto_approx
      tendsto_approx_grad := by
        intro k
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x =>
                  (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                    (u.toW1pFunction.translate z).grad x k)
                p (MeasureTheory.volume.restrict V)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x => (fderiv ℝ (u.approx m) x) (basisVec k) - u.toW1pFunction.grad x k)
                  p (MeasureTheory.volume.restrict U)) := by
          funext m
          let g : Vec d → ℝ :=
            fun x => (fderiv ℝ (u.approx m) x) (basisVec k) - u.toW1pFunction.grad x k
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict U) := by
            exact ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
              continuous_const |>.aestronglyMeasurable.sub
                (u.toW1pFunction.gradMemLp k).aestronglyMeasurable
          have hfun :
              (fun x =>
                (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                  (u.toW1pFunction.translate z).grad x k) = g ∘ T := by
            funext x
            simp [g, T, Function.comp, W1pFunction.translate]
            have hderiv :
                fderiv ℝ (fun y : Vec d => u.approx m (y - z)) x =
                  fderiv ℝ (u.approx m) (x - z) := by
              simpa [T, sub_eq_add_neg] using
                (fderiv_comp_sub (𝕜 := ℝ) (f := u.approx m) (x := x) z)
            simpa [T, sub_eq_add_neg] using
              congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec k)) hderiv
          rw [hfun]
          simpa [g, T, Function.comp] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := p) hg hμ)
        rw [hEq]
        exact u.tendsto_approx_grad k }

@[simp] theorem translate_toW1pFunction {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
    (u : W10pFunction U p) (z : Vec d) :
    (u.translate z).toW1pFunction = u.toW1pFunction.translate z := rfl

end W10pFunction

end

end Homogenization
