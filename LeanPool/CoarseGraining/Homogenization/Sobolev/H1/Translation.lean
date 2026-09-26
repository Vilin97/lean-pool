/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.Translation
public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Definitions

/-! # Translation -/

@[expose] public section

namespace Homogenization

open scoped Topology

noncomputable section

namespace H1Function

/--
Translate an `H¹(U)` witness to `H¹(U + z)` by precomposing with `x ↦ x - z`.
-/
noncomputable def translate {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (z : Vec d) :
    H1Function (translateSet z U) := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x - z
  let hμ := measurePreserving_subRight_restrict_translateSet (d := d) z U
  refine
    { toFun := fun x => u (T x)
      grad := fun x => u.grad (T x)
      memL2 := by
        show MemL2On V (u.toFun ∘ T)
        simpa [MemL2On, V, T, Function.comp] using u.memL2.comp_measurePreserving hμ
      gradMemL2 := by
        intro i
        show MemL2On V ((fun x => u.grad x i) ∘ T)
        simpa [MemL2On, V, T, Function.comp] using (u.gradMemL2 i).comp_measurePreserving hμ
      hasWeakGradient := ?_ }
  intro i φ hφ hφ_supp hφ_sub
  let ψ : Vec d → ℝ := fun x => φ (x + z)
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ, Function.comp_def] using hφ.comp (contDiff_id.add contDiff_const)
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

@[simp] theorem translate_toFun {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (z : Vec d)
    (x : Vec d) :
    (u.translate z).toFun x = u.toFun (x - z) := rfl

@[simp] theorem translate_grad {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (z : Vec d)
    (x : Vec d) :
    (u.translate z).grad x = u.grad (x - z) := rfl

/--
Pull an `H¹(U + z)` witness back to `H¹(U)` by precomposing with `x ↦ x + z`.
-/
noncomputable def untranslate {d : ℕ} {U : Set (Vec d)}
    (z : Vec d) (u : H1Function (translateSet z U)) : H1Function U := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x + z
  let hμ := measurePreserving_addRight_restrict_translateSet (d := d) z U
  refine
    { toFun := fun x => u (T x)
      grad := fun x => u.grad (T x)
      memL2 := by
        show MemL2On U (u.toFun ∘ T)
        simpa [MemL2On, V, T, Function.comp] using u.memL2.comp_measurePreserving hμ
      gradMemL2 := by
        intro i
        show MemL2On U ((fun x => u.grad x i) ∘ T)
        simpa [MemL2On, V, T, Function.comp] using (u.gradMemL2 i).comp_measurePreserving hμ
      hasWeakGradient := ?_ }
  intro i φ hφ hφ_supp hφ_sub
  let ψ : Vec d → ℝ := fun x => φ (x - z)
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    simpa [ψ, Function.comp_def] using hφ.comp (contDiff_id.sub contDiff_const)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (φ ∘ Homeomorph.subRight z)
    simpa [ψ, Function.comp] using hφ_supp.comp_homeomorph (Homeomorph.subRight z)
  have hψ_sub : tsupport ψ ⊆ V := by
    intro x hx
    have hx' : x - z ∈ tsupport φ := by
      rw [show ψ = φ ∘ Homeomorph.subRight z by rfl,
        tsupport_comp_eq_preimage φ (Homeomorph.subRight z)] at hx
      exact hx
    exact (mem_translateSet_iff_sub_mem).2 (hφ_sub hx')
  have hweak := u.hasWeakGradient i ψ hψ_smooth hψ_supp hψ_sub
  have hmain :
      ∫ x in V, u x * (fderiv ℝ φ (x - z)) (basisVec i) ∂MeasureTheory.volume =
        -∫ x in V, u.grad x i * φ (x - z) ∂MeasureTheory.volume := by
    have hfun :
        (fun x => u x * (fderiv ℝ φ (x - z)) (basisVec i)) =
          fun x => u x * (fderiv ℝ ψ x) (basisVec i) := by
      funext x
      have hderiv :
          fderiv ℝ (fun y : Vec d => φ (y - z)) x =
            fderiv ℝ φ (x - z) := by
        simpa using (fderiv_comp_sub (𝕜 := ℝ) (f := φ) (x := x) z)
      simp [ψ, hderiv]
    calc
      ∫ x in V, u x * (fderiv ℝ φ (x - z)) (basisVec i) ∂MeasureTheory.volume
        = ∫ x in V, u x * (fderiv ℝ ψ x) (basisVec i) ∂MeasureTheory.volume := by rw [hfun]
      _ = -∫ x in V, u.grad x i * ψ x ∂MeasureTheory.volume := hweak
      _ = -∫ x in V, u.grad x i * φ (x - z) ∂MeasureTheory.volume := by rfl
  have hchange_left :
      ∫ x in U, u (x + z) * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
        ∫ x in V, u x * (fderiv ℝ φ (x - z)) (basisVec i) ∂MeasureTheory.volume := by
    simpa [V, T, sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) z U
        (fun x => u x * (fderiv ℝ φ (x - z)) (basisVec i)))
  have hchange_right :
      ∫ x in V, u.grad x i * φ (x - z) ∂MeasureTheory.volume =
        ∫ x in U, u.grad (x + z) i * φ x ∂MeasureTheory.volume := by
    simpa [V, T, sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) z U
        (fun x => u.grad x i * φ (x - z))).symm
  calc
    ∫ x in U, u (x + z) * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume
      = ∫ x in V, u x * (fderiv ℝ φ (x - z)) (basisVec i) ∂MeasureTheory.volume :=
        hchange_left
    _ = -∫ x in V, u.grad x i * φ (x - z) ∂MeasureTheory.volume := hmain
    _ = -∫ x in U, u.grad (x + z) i * φ x ∂MeasureTheory.volume := by rw [hchange_right]

@[simp] theorem untranslate_toFun {d : ℕ} {U : Set (Vec d)}
    (z : Vec d) (u : H1Function (translateSet z U)) (x : Vec d) :
    (H1Function.untranslate z u).toFun x = u.toFun (x + z) := rfl

@[simp] theorem untranslate_grad {d : ℕ} {U : Set (Vec d)}
    (z : Vec d) (u : H1Function (translateSet z U)) (x : Vec d) :
    (H1Function.untranslate z u).grad x = u.grad (x + z) := rfl

end H1Function

namespace H10Function

/--
Translate an `H¹₀(U)` witness to `H¹₀(U + z)` by precomposing with `x ↦ x - z`.
-/
noncomputable def translate {d : ℕ} {U : Set (Vec d)} (u : H10Function U) (z : Vec d) :
    H10Function (translateSet z U) := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x - z
  let hμ := measurePreserving_subRight_restrict_translateSet (d := d) z U
  refine
    { toH1Function := u.toH1Function.translate z
      approx := fun m x => u.approx m (T x)
      approx_smooth := by
        intro m
        simpa [T, sub_eq_add_neg, Function.comp_def] using
          (u.approx_smooth m).comp (contDiff_id.sub contDiff_const)
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
                (fun x => u.approx m (T x) - (u.toH1Function.translate z).toFun x)
                2 (MeasureTheory.volume.restrict V)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x => u.approx m x - u.toH1Function.toFun x)
                  2 (MeasureTheory.volume.restrict U)) := by
          funext m
          let g : Vec d → ℝ := fun x => u.approx m x - u.toH1Function.toFun x
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict U) := by
            exact (u.approx_smooth m).continuous.aestronglyMeasurable.sub
              u.toH1Function.memL2.aestronglyMeasurable
          have hfun :
              (fun x => u.approx m (T x) - (u.toH1Function.translate z).toFun x) = g ∘ T := by
            funext x
            simp [g, T, Function.comp, H1Function.translate]
          rw [hfun]
          simpa [g, T, Function.comp] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := (2 : ENNReal)) hg hμ)
        rw [hEq]
        exact u.tendsto_approx
      tendsto_approx_grad := by
        intro k
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x =>
                  (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                    (u.toH1Function.translate z).grad x k)
                2 (MeasureTheory.volume.restrict V)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x => (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)
                  2 (MeasureTheory.volume.restrict U)) := by
          funext m
          let g : Vec d → ℝ :=
            fun x => (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict U) := by
            exact ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
              continuous_const |>.aestronglyMeasurable.sub
                (u.toH1Function.gradMemL2 k).aestronglyMeasurable
          have hfun :
              (fun x =>
                (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                  (u.toH1Function.translate z).grad x k) = g ∘ T := by
            funext x
            simp [g, T, Function.comp, H1Function.translate]
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
              (g := g) (p := (2 : ENNReal)) hg hμ)
        rw [hEq]
        exact u.tendsto_approx_grad k }

@[simp] theorem translate_toH1Function {d : ℕ} {U : Set (Vec d)} (u : H10Function U) (z : Vec d) :
    (u.translate z).toH1Function = u.toH1Function.translate z := rfl

/--
Pull an `H¹₀(U + z)` witness back to `H¹₀(U)` by precomposing with `x ↦ x + z`.
-/
noncomputable def untranslate {d : ℕ} {U : Set (Vec d)}
    (z : Vec d) (u : H10Function (translateSet z U)) : H10Function U := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x + z
  let hμ := measurePreserving_addRight_restrict_translateSet (d := d) z U
  refine
    { toH1Function := H1Function.untranslate z u.toH1Function
      approx := fun m x => u.approx m (T x)
      approx_smooth := by
        intro m
        simpa [T, Function.comp_def] using
          (u.approx_smooth m).comp (contDiff_id.add contDiff_const)
      approx_hasCompactSupport := by
        intro m
        show HasCompactSupport (u.approx m ∘ Homeomorph.addRight z)
        simpa [T, Function.comp] using
          (u.approx_hasCompactSupport m).comp_homeomorph (Homeomorph.addRight z)
      approx_support_subset := by
        intro m x hx
        have hx' : x + z ∈ tsupport (u.approx m) := by
          rw [show (fun y => u.approx m (T y)) = u.approx m ∘ Homeomorph.addRight z by rfl,
            tsupport_comp_eq_preimage (u.approx m) (Homeomorph.addRight z)] at hx
          exact hx
        have hxV : x + z ∈ V := u.approx_support_subset m hx'
        simpa [V, mem_translateSet_iff_sub_mem, sub_eq_add_neg, add_assoc] using hxV
      tendsto_approx := by
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x => u.approx m (T x) - (H1Function.untranslate z u.toH1Function).toFun x)
                2 (MeasureTheory.volume.restrict U)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x => u.approx m x - u.toH1Function.toFun x)
                  2 (MeasureTheory.volume.restrict V)) := by
          funext m
          let g : Vec d → ℝ := fun x => u.approx m x - u.toH1Function.toFun x
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict V) := by
            exact (u.approx_smooth m).continuous.aestronglyMeasurable.sub
              u.toH1Function.memL2.aestronglyMeasurable
          have hfun :
              (fun x => u.approx m (T x) -
                  (H1Function.untranslate z u.toH1Function).toFun x) = g ∘ T := by
            funext x
            simp [g, T, Function.comp, H1Function.untranslate]
          rw [hfun]
          simpa [g, T, Function.comp, V] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := (2 : ENNReal)) hg hμ)
        rw [hEq]
        exact u.tendsto_approx
      tendsto_approx_grad := by
        intro k
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x =>
                  (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                    (H1Function.untranslate z u.toH1Function).grad x k)
                2 (MeasureTheory.volume.restrict U)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x => (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)
                  2 (MeasureTheory.volume.restrict V)) := by
          funext m
          let g : Vec d → ℝ :=
            fun x => (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict V) := by
            exact ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
              continuous_const |>.aestronglyMeasurable.sub
                (u.toH1Function.gradMemL2 k).aestronglyMeasurable
          have hfun :
              (fun x =>
                (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                  (H1Function.untranslate z u.toH1Function).grad x k) = g ∘ T := by
            funext x
            simp [g, T, Function.comp, H1Function.untranslate]
            have hderiv :
                fderiv ℝ (fun y : Vec d => u.approx m (y + z)) x =
                  fderiv ℝ (u.approx m) (x + z) := by
              simpa [T] using
                (fderiv_comp_add_right (𝕜 := ℝ) (f := u.approx m) (x := x) z)
            simpa [T] using
              congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec k)) hderiv
          rw [hfun]
          simpa [g, T, Function.comp, V] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := (2 : ENNReal)) hg hμ)
        rw [hEq]
        exact u.tendsto_approx_grad k }

@[simp] theorem untranslate_toH1Function {d : ℕ} {U : Set (Vec d)}
    (z : Vec d) (u : H10Function (translateSet z U)) :
    (H10Function.untranslate z u).toH1Function =
      H1Function.untranslate z u.toH1Function := rfl

end H10Function

end

end Homogenization
