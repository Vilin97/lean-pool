/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInterior

/-! # Hessian Translation -/

@[expose] public section

namespace Homogenization

open scoped ENNReal Topology

noncomputable section

namespace HasWeakPartialDerivOn

theorem congr_of_eqOn {d : ℕ} {U : Set (Vec d)}
    (hU_meas : MeasurableSet U) {i : Fin d}
    {u v gi hi : Vec d → ℝ} (huv : Set.EqOn u v U)
    (hgi : Set.EqOn gi hi U)
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn U i v hi := by
  intro φ hφ hφ_supp hφ_sub
  have hleft :
      ∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
        ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hU_meas ?_
    intro x hx
    change v x * (fderiv ℝ φ x) (basisVec i) =
      u x * (fderiv ℝ φ x) (basisVec i)
    rw [← huv hx]
  have hright :
      ∫ x in U, gi x * φ x ∂MeasureTheory.volume =
        ∫ x in U, hi x * φ x ∂MeasureTheory.volume := by
    refine MeasureTheory.setIntegral_congr_fun hU_meas ?_
    intro x hx
    change gi x * φ x = hi x * φ x
    rw [hgi hx]
  calc
    ∫ x in U, v x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume
        = ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume := hleft
    _ = -∫ x in U, gi x * φ x ∂MeasureTheory.volume :=
      h φ hφ hφ_supp hφ_sub
    _ = -∫ x in U, hi x * φ x ∂MeasureTheory.volume := by
      rw [hright]

theorem translate {d : ℕ} {U : Set (Vec d)} {i : Fin d}
    {u gi : Vec d → ℝ} (h : HasWeakPartialDerivOn U i u gi) (z : Vec d) :
    HasWeakPartialDerivOn (translateSet z U) i
      (fun x => u (x - z)) (fun x => gi (x - z)) := by
  intro φ hφ hφ_supp hφ_sub
  let V : Set (Vec d) := translateSet z U
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
  have hweak := h ψ hψ_smooth hψ_supp hψ_sub
  have hmain :
      ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i) ∂MeasureTheory.volume =
        -∫ x in U, gi x * φ (x + z) ∂MeasureTheory.volume := by
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
          = ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec i) ∂MeasureTheory.volume := by
            rw [hfun]
      _ = -∫ x in U, gi x * ψ x ∂MeasureTheory.volume := hweak
      _ = -∫ x in U, gi x * φ (x + z) ∂MeasureTheory.volume := by rfl
  have hchange_left :
      ∫ x in V, u (x - z) * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume =
        ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i) ∂MeasureTheory.volume := by
    symm
    simpa [V, sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) z U
        (fun x => u (x - z) * (fderiv ℝ φ x) (basisVec i)))
  have hchange_right :
      ∫ x in U, gi x * φ (x + z) ∂MeasureTheory.volume =
        ∫ x in V, gi (x - z) * φ x ∂MeasureTheory.volume := by
    simpa [V, sub_eq_add_neg, add_assoc] using
      (setIntegral_comp_addRight_translateSet (d := d) z U
        (fun x => gi (x - z) * φ x))
  calc
    ∫ x in V, u (x - z) * (fderiv ℝ φ x) (basisVec i) ∂MeasureTheory.volume
        = ∫ x in U, u x * (fderiv ℝ φ (x + z)) (basisVec i) ∂MeasureTheory.volume :=
          hchange_left
    _ = -∫ x in U, gi x * φ (x + z) ∂MeasureTheory.volume := hmain
    _ = -∫ x in V, gi (x - z) * φ x ∂MeasureTheory.volume := by
          rw [hchange_right]

end HasWeakPartialDerivOn

namespace HasWeakHessianOn

variable {d : ℕ} {U : Set (Vec d)} {u : H1Function U}

/-- Translate a weak Hessian witness from `U` to `U + z`. -/
noncomputable def translate (H : HasWeakHessianOn U u) (z : Vec d) :
    HasWeakHessianOn (translateSet z U) (u.translate z) where
  hess := fun i j x => H.hess i j (x - z)
  hess_memL2 := by
    intro i j
    let V : Set (Vec d) := translateSet z U
    let T : Vec d → Vec d := fun x => x - z
    have hμ := measurePreserving_subRight_restrict_translateSet (d := d) z U
    show MemScalarL2 V ((H.hess i j) ∘ T)
    simpa [MemScalarL2, volumeMeasureOn, V, T, Function.comp] using
      (H.hess_memL2 i j).comp_measurePreserving hμ
  weak_second := by
    intro i j
    simpa [H1Function.translate] using
      (H.weak_second i j).translate z

theorem translate_hess (H : HasWeakHessianOn U u) (z : Vec d)
    (i j : Fin d) (x : Vec d) :
    (H.translate z).hess i j x = H.hess i j (x - z) :=
  rfl

theorem norm_hessCoordToScalarL2_translate_eq
    (H : HasWeakHessianOn U u) (z : Vec d) (i j : Fin d) :
    ‖(H.translate z).hessCoordToScalarL2 i j‖ = ‖H.hessCoordToScalarL2 i j‖ := by
  let V : Set (Vec d) := translateSet z U
  let T : Vec d → Vec d := fun x => x - z
  have hμ := measurePreserving_subRight_restrict_translateSet (d := d) z U
  unfold hessCoordToScalarL2 Homogenization.toScalarL2
  rw [MeasureTheory.Lp.norm_toLp, MeasureTheory.Lp.norm_toLp]
  exact congrArg ENNReal.toReal (by
    simpa [HasWeakHessianOn.translate, MemScalarL2, volumeMeasureOn, V, T, Function.comp] using!
      (MeasureTheory.eLpNorm_comp_measurePreserving
        (g := H.hess i j) (p := (2 : ℝ≥0∞))
        (H.hess_memL2 i j).aestronglyMeasurable hμ))

theorem hessianCoordL2NormSum_translate_eq
    (H : HasWeakHessianOn U u) (z : Vec d) :
    (H.translate z).hessianCoordL2NormSum = H.hessianCoordL2NormSum := by
  unfold hessianCoordL2NormSum
  refine Finset.sum_congr rfl ?_
  intro i _hi
  refine Finset.sum_congr rfl ?_
  intro j _hj
  exact H.norm_hessCoordToScalarL2_translate_eq z i j

end HasWeakHessianOn

end

end Homogenization
