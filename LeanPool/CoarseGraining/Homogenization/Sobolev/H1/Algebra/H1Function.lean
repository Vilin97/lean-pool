/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.BasicLemmas
import LeanPool.CoarseGraining.Homogenization.Sobolev.W1p.ConvexApproxSmoothing
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! # H1Function -/

namespace Homogenization

namespace H1Function

instance {d : ℕ} {U : Set (Vec d)} : Zero (H1Function U) where
  zero :=
    { toFun := 0
      grad := 0
      memL2 := by
        exact
          (MeasureTheory.MemLp.zero :
            MeasureTheory.MemLp (0 : Vec d → ℝ) 2 (MeasureTheory.volume.restrict U))
      gradMemL2 := by
        intro i
        exact
          (MeasureTheory.MemLp.zero :
            MeasureTheory.MemLp (0 : Vec d → ℝ) 2 (MeasureTheory.volume.restrict U))
      hasWeakGradient := by
        intro i φ hφ hφ_supp hφ_sub
        simp }

instance {d : ℕ} {U : Set (Vec d)} : SMul ℝ (H1Function U) where
  smul c u :=
    { toFun := fun x => c * u x
      grad := fun x => c • u.grad x
      memL2 := u.memL2.const_mul c
      gradMemL2 := by
        intro i
        simpa [Pi.smul_apply, smul_eq_mul] using (u.gradMemL2 i).const_mul c
      hasWeakGradient := by
        intro i φ hφ hφ_supp hφ_sub
        let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
        have hu_eq := u.hasWeakGradient i φ hφ hφ_supp hφ_sub
        have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
        have hdφ_cont : Continuous dφ := by
          simpa [dφ] using
            (hφ1.continuous_fderiv (by simp)).clm_apply
              continuous_const
        have hdφ_supp : HasCompactSupport dφ := by
          simpa [dφ] using hφ_supp.fderiv_apply (𝕜 := ℝ) (basisVec i)
        have hu_int :
            MeasureTheory.Integrable (fun x => u x * dφ x) (MeasureTheory.volume.restrict U) := by
          have hu_loc : MeasureTheory.LocallyIntegrable u (MeasureTheory.volume.restrict U) :=
            u.memL2.locallyIntegrable (by norm_num)
          simpa [smul_eq_mul] using
            hu_loc.integrable_smul_right_of_hasCompactSupport hdφ_cont hdφ_supp
        have hgrad :
            (fun x => c * (u.grad x i * φ x)) =
              (fun x => ((fun x => c • u.grad x) x i) * φ x) := by
          funext x
          simp [Pi.smul_apply, smul_eq_mul]
          ring
        have hgrad_int :
            ∫ x in U, c * (u.grad x i * φ x) ∂MeasureTheory.volume =
              ∫ x in U, ((fun x => c • u.grad x) x i) * φ x ∂MeasureTheory.volume := by
          rw [hgrad]
        calc
          ∫ x in U, (c * u x) * dφ x ∂MeasureTheory.volume
              = ∫ x in U, c * (u x * dφ x) ∂MeasureTheory.volume := by
                  congr with x
                  ring
          _ = c * ∫ x in U, u x * dφ x ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_const_mul]
          _ = c * (-∫ x in U, u.grad x i * φ x ∂MeasureTheory.volume) := by
                rw [hu_eq]
          _ = -(c * ∫ x in U, u.grad x i * φ x ∂MeasureTheory.volume) := by
                ring
          _ = -∫ x in U, c * (u.grad x i * φ x) ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_const_mul]
          _ = -∫ x in U, ((fun x => c • u.grad x) x i) * φ x ∂MeasureTheory.volume := by
                show -(∫ x in U, c * (u.grad x i * φ x) ∂MeasureTheory.volume) =
                  -(∫ x in U, ((fun x => c • u.grad x) x i) * φ x ∂MeasureTheory.volume)
                exact congrArg Neg.neg hgrad_int
      }

instance {d : ℕ} {U : Set (Vec d)} : Neg (H1Function U) where
  neg u := (-1 : ℝ) • u

instance {d : ℕ} {U : Set (Vec d)} : Add (H1Function U) where
  add u v :=
    { toFun := fun x => u x + v x
      grad := fun x => u.grad x + v.grad x
      memL2 := u.memL2.add v.memL2
      gradMemL2 := by
        intro i
        simpa [Pi.add_apply] using! (u.gradMemL2 i).add (v.gradMemL2 i)
      hasWeakGradient := by
        intro i φ hφ hφ_supp hφ_sub
        let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
        have hu_eq := u.hasWeakGradient i φ hφ hφ_supp hφ_sub
        have hv_eq := v.hasWeakGradient i φ hφ hφ_supp hφ_sub
        have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
        have hdφ_cont : Continuous dφ := by
          simpa [dφ] using
            (hφ1.continuous_fderiv (by simp)).clm_apply
              continuous_const
        have hdφ_supp : HasCompactSupport dφ := by
          simpa [dφ] using hφ_supp.fderiv_apply (𝕜 := ℝ) (basisVec i)
        have hu_int :
            MeasureTheory.Integrable (fun x => u x * dφ x) (MeasureTheory.volume.restrict U) := by
          have hu_loc : MeasureTheory.LocallyIntegrable u (MeasureTheory.volume.restrict U) :=
            u.memL2.locallyIntegrable (by norm_num)
          simpa [smul_eq_mul] using
            hu_loc.integrable_smul_right_of_hasCompactSupport hdφ_cont hdφ_supp
        have hv_int :
            MeasureTheory.Integrable (fun x => v x * dφ x) (MeasureTheory.volume.restrict U) := by
          have hv_loc : MeasureTheory.LocallyIntegrable v (MeasureTheory.volume.restrict U) :=
            v.memL2.locallyIntegrable (by norm_num)
          simpa [smul_eq_mul] using
            hv_loc.integrable_smul_right_of_hasCompactSupport hdφ_cont hdφ_supp
        have hgu_int :
            MeasureTheory.Integrable (fun x => u.grad x i * φ x) (MeasureTheory.volume.restrict U) := by
          have hgu_loc :
              MeasureTheory.LocallyIntegrable (fun x => u.grad x i)
                (MeasureTheory.volume.restrict U) :=
            (u.gradMemL2 i).locallyIntegrable (by norm_num)
          simpa [smul_eq_mul] using
            hgu_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
        have hgv_int :
            MeasureTheory.Integrable (fun x => v.grad x i * φ x) (MeasureTheory.volume.restrict U) := by
          have hgv_loc :
              MeasureTheory.LocallyIntegrable (fun x => v.grad x i)
                (MeasureTheory.volume.restrict U) :=
            (v.gradMemL2 i).locallyIntegrable (by norm_num)
          simpa [smul_eq_mul] using
            hgv_loc.integrable_smul_right_of_hasCompactSupport hφ.continuous hφ_supp
        have hgrad :
            (fun x => u.grad x i * φ x + v.grad x i * φ x) =
              (fun x => ((u.grad x + v.grad x) i) * φ x) := by
          funext x
          simp [Pi.add_apply]
          ring
        have hgrad_int :
            ∫ x in U, (u.grad x i * φ x + v.grad x i * φ x) ∂MeasureTheory.volume =
              ∫ x in U, ((u.grad x + v.grad x) i) * φ x ∂MeasureTheory.volume := by
          rw [hgrad]
        calc
          ∫ x in U, (u x + v x) * dφ x ∂MeasureTheory.volume
              = ∫ x in U, (u x * dφ x + v x * dφ x) ∂MeasureTheory.volume := by
                  congr with x
                  ring
          _ = ∫ x in U, u x * dφ x ∂MeasureTheory.volume +
                ∫ x in U, v x * dφ x ∂MeasureTheory.volume := by
                  rw [MeasureTheory.integral_add hu_int hv_int]
          _ = (-∫ x in U, u.grad x i * φ x ∂MeasureTheory.volume) +
                (-∫ x in U, v.grad x i * φ x ∂MeasureTheory.volume) := by
                  rw [hu_eq, hv_eq]
          _ = -((∫ x in U, u.grad x i * φ x ∂MeasureTheory.volume) +
                (∫ x in U, v.grad x i * φ x ∂MeasureTheory.volume)) := by
                  ring
          _ = -∫ x in U, (u.grad x i * φ x + v.grad x i * φ x) ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_add hgu_int hgv_int]
          _ = -∫ x in U, ((u.grad x + v.grad x) i) * φ x ∂MeasureTheory.volume := by
                show -(∫ x in U, (u.grad x i * φ x + v.grad x i * φ x) ∂MeasureTheory.volume) =
                  -(∫ x in U, ((u.grad x + v.grad x) i) * φ x ∂MeasureTheory.volume)
                exact congrArg Neg.neg hgrad_int
      }

instance {d : ℕ} {U : Set (Vec d)} : Sub (H1Function U) where
  sub u v := u + (-v)

@[simp] theorem zero_toFun {d : ℕ} {U : Set (Vec d)} :
    (0 : H1Function U).toFun = 0 :=
  rfl

@[simp] theorem zero_grad {d : ℕ} {U : Set (Vec d)} :
    (0 : H1Function U).grad = 0 :=
  rfl

@[simp] theorem add_toFun {d : ℕ} {U : Set (Vec d)} (u v : H1Function U) :
    (u + v).toFun = fun x => u x + v x :=
  rfl

@[simp] theorem add_grad {d : ℕ} {U : Set (Vec d)} (u v : H1Function U) :
    (u + v).grad = fun x => u.grad x + v.grad x :=
  rfl

@[simp] theorem smul_toFun {d : ℕ} {U : Set (Vec d)} (c : ℝ) (u : H1Function U) :
    (c • u).toFun = fun x => c * u x :=
  rfl

@[simp] theorem smul_grad {d : ℕ} {U : Set (Vec d)} (c : ℝ) (u : H1Function U) :
    (c • u).grad = fun x => c • u.grad x :=
  rfl

@[simp] theorem neg_toFun {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    (-u).toFun = fun x => -u x := by
  show ((-1 : ℝ) • u).toFun = fun x => -u x
  funext x
  simp

@[simp] theorem neg_grad {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    (-u).grad = fun x => -u.grad x := by
  show ((-1 : ℝ) • u).grad = fun x => -u.grad x
  funext x
  simp

@[simp] theorem sub_toFun {d : ℕ} {U : Set (Vec d)} (u v : H1Function U) :
    (u - v).toFun = fun x => u x - v x := by
  show (u + (-v)).toFun = fun x => u x - v x
  funext x
  simp [sub_eq_add_neg]

@[simp] theorem sub_grad {d : ℕ} {U : Set (Vec d)} (u v : H1Function U) :
    (u - v).grad = fun x => u.grad x - v.grad x := by
  show (u + (-v)).grad = fun x => u.grad x - v.grad x
  funext x
  simp [sub_eq_add_neg]

instance {d : ℕ} {U : Set (Vec d)} : SMul ℕ (H1Function U) where
  smul n u := (n : ℝ) • u

instance {d : ℕ} {U : Set (Vec d)} : SMul ℤ (H1Function U) where
  smul n u := (n : ℝ) • u

theorem toFunGrad_injective {d : ℕ} {U : Set (Vec d)} :
    Function.Injective (fun u : H1Function U => (u.toFun, u.grad)) := by
  intro u v h
  exact H1Function.ext
    (by simpa using congrArg Prod.fst h)
    (by simpa using congrArg Prod.snd h)

instance {d : ℕ} {U : Set (Vec d)} : AddCommGroup (H1Function U) :=
  Function.Injective.addCommGroup
    (fun u : H1Function U => (u.toFun, u.grad))
    toFunGrad_injective
    rfl
    (fun _ _ => rfl)
    (fun _ => by ext x <;> simp)
    (fun _ _ => by ext x <;> simp [sub_eq_add_neg])
    (fun u n => by
      apply Prod.ext
      · funext x
        change (((n : ℝ) • u).toFun x) = (n • u.toFun) x
        simp [nsmul_eq_mul]
      · funext x
        ext i
        change (((n : ℝ) • u).grad x i) = (n • u.grad) x i
        simp [nsmul_eq_mul])
    (fun u n => by
      apply Prod.ext
      · funext x
        change (((n : ℝ) • u).toFun x) = (n • u.toFun) x
        simp [zsmul_eq_mul]
      · funext x
        ext i
        change (((n : ℝ) • u).grad x i) = (n • u.grad) x i
        simp [zsmul_eq_mul])

noncomputable def toFunGradAddMonoidHom {d : ℕ} {U : Set (Vec d)} :
    H1Function U →+ ((Vec d → ℝ) × (Vec d → Vec d)) where
  toFun := fun u => (u.toFun, u.grad)
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance {d : ℕ} {U : Set (Vec d)} : Module ℝ (H1Function U) :=
  Function.Injective.module ℝ
    toFunGradAddMonoidHom
    (toFunGrad_injective (d := d) (U := U))
    (fun _ _ => rfl)

/-- Multiplication of an `H¹` function by a smooth scalar multiplier which is
bounded, together with its first derivatives, on the underlying domain.  This
is the non-compact-support variant of `mulContDiffHasCompactSupport`; the test
function still provides the compact support in the weak-gradient identity. -/
noncomputable def mulContDiffMemLpTop {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) (MeasureTheory.volume.restrict U))
    (hdφ_memTop : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => (fderiv ℝ φ x) (basisVec i))
        (⊤ : ENNReal) (MeasureTheory.volume.restrict U)) : H1Function U := by
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  let Dφ : Vec d → Vec d := fun x i => (fderiv ℝ φ x) (basisVec i)
  have hφ_cont : Continuous φ := hφ.continuous
  refine
    { toFun := fun x => φ x * u x
      grad := fun x i => φ x * u.grad x i + u x * Dφ x i
      memL2 := ?_
      gradMemL2 := ?_
      hasWeakGradient := ?_ }
  · simpa [Dφ, μU, mul_comm] using u.memL2.fun_mul (r := 2) hφ_memTop
  · intro i
    let dφ : Vec d → ℝ := fun x => Dφ x i
    have hfirst :
        MeasureTheory.MemLp (fun x => φ x * u.grad x i) 2 μU := by
      simpa [μU, mul_comm] using (u.gradMemL2 i).fun_mul (r := 2) hφ_memTop
    have hsecond :
        MeasureTheory.MemLp (fun x => u x * dφ x) 2 μU := by
      simpa [dφ, Dφ, μU, mul_comm] using u.memL2.mul' (hdφ_memTop i)
    simpa [dφ, Dφ, Pi.add_apply] using! hfirst.add hsecond
  · intro i ψ hψ_smooth hψ_compact hψ_sub
    let ei : Vec d := basisVec i
    let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) ei
    let dψ : Vec d → ℝ := fun x => (fderiv ℝ ψ x) ei
    let ψφ : Vec d → ℝ := fun x => φ x * ψ x
    change
      ∫ x, (φ x * u x) * dψ x ∂μU =
        -∫ x, (φ x * u.grad x i + u x * dφ x) * ψ x ∂μU
    have hψ_cont : Continuous ψ := hψ_smooth.continuous
    have hdφ_cont : Continuous dφ := by
      simpa [dφ] using
        (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψ_cont : Continuous dψ := by
      simpa [dψ] using
        (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψ_compact : HasCompactSupport dψ := by
      simpa [dψ] using hψ_compact.fderiv_apply (𝕜 := ℝ) ei
    have hψφ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψφ := hφ.mul hψ_smooth
    have hψφ_compact : HasCompactSupport ψφ := by
      simpa [ψφ] using! hψ_compact.mul_left (f := φ)
    have hdψφ_cont : Continuous (fun x => (fderiv ℝ ψφ x) ei) := by
      simpa [ei] using
        (hψφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψφ_compact : HasCompactSupport (fun x => (fderiv ℝ ψφ x) ei) := by
      simpa [ei] using hψφ_compact.fderiv_apply (𝕜 := ℝ) ei
    have hψφ_sub : tsupport ψφ ⊆ U := by
      exact (tsupport_mul_subset_right (f := φ) (g := ψ)).trans hψ_sub
    have hu_eq :
        ∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU =
          -∫ x, u.grad x i * ψφ x ∂μU := by
      simpa [μU] using u.hasWeakGradient i ψφ hψφ_smooth hψφ_compact hψφ_sub
    have hu_loc : MeasureTheory.LocallyIntegrable u μU :=
      u.memL2.locallyIntegrable (by norm_num)
    have hgrad_loc : MeasureTheory.LocallyIntegrable (fun x => u.grad x i) μU :=
      (u.gradMemL2 i).locallyIntegrable (by norm_num)
    have hmul1_cont : Continuous (fun x => φ x * dψ x) := hφ_cont.mul hdψ_cont
    have hmul1_compact : HasCompactSupport (fun x => φ x * dψ x) := by
      simpa using! hdψ_compact.mul_left (f := φ)
    have hu_mul1_int :
        MeasureTheory.Integrable (fun x => u x * (φ x * dψ x)) μU := by
      simpa [smul_eq_mul, μU, mul_assoc] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hmul1_cont hmul1_compact
    have hmul2_cont : Continuous (fun x => ψ x * dφ x) := hψ_cont.mul hdφ_cont
    have hmul2_compact : HasCompactSupport (fun x => ψ x * dφ x) := by
      simpa using! hψ_compact.mul_right (f' := dφ)
    have hu_mul2_int :
        MeasureTheory.Integrable (fun x => u x * (ψ x * dφ x)) μU := by
      simpa [smul_eq_mul, μU, mul_assoc] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hmul2_cont hmul2_compact
    have hu_ψφ_int :
        MeasureTheory.Integrable (fun x => u x * (fderiv ℝ ψφ x) ei) μU := by
      simpa [smul_eq_mul, μU] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hdψφ_cont hdψφ_compact
    have hgrad_mul1_int :
        MeasureTheory.Integrable (fun x => u.grad x i * (φ x * ψ x)) μU := by
      simpa [smul_eq_mul, μU, mul_assoc] using
        hgrad_loc.integrable_smul_right_of_hasCompactSupport
          (hφ_cont.mul hψ_cont) hψφ_compact
    have hu_mul2ψ_int :
        MeasureTheory.Integrable (fun x => (u x * dφ x) * ψ x) μU := by
      simpa [smul_eq_mul, μU, mul_assoc, mul_left_comm, mul_comm] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hmul2_cont hmul2_compact
    have hprod_deriv :
        ∀ x, (fderiv ℝ ψφ x) ei = φ x * dψ x + ψ x * dφ x := by
      intro x
      have hφ_diff : DifferentiableAt ℝ φ x :=
        (hφ.contDiffAt).differentiableAt (by simp)
      have hψ_diff : DifferentiableAt ℝ ψ x :=
        (hψ_smooth.contDiffAt).differentiableAt (by simp)
      rw [show ψφ = φ * ψ by rfl, fderiv_mul hφ_diff hψ_diff]
      simp [dφ, dψ, ei, smul_eq_mul]
    have hleft_eq :
        ∫ x, (φ x * u x) * dψ x ∂μU =
          ∫ x, u x * (φ x * dψ x) ∂μU := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro x
      ring
    have hsplit :
        ∫ x, u x * (φ x * dψ x) ∂μU =
          ∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU -
            ∫ x, u x * (ψ x * dφ x) ∂μU := by
      calc
        ∫ x, u x * (φ x * dψ x) ∂μU
            = ∫ x, (u x * (fderiv ℝ ψφ x) ei) - u x * (ψ x * dφ x) ∂μU := by
                refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
                intro x
                have hx :
                    u x * (φ x * dψ x) =
                      u x * (fderiv ℝ ψφ x) ei - u x * (ψ x * dφ x) := by
                  rw [hprod_deriv x]
                  ring
                exact hx
        _ = ∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU -
              ∫ x, u x * (ψ x * dφ x) ∂μU := by
                rw [MeasureTheory.integral_sub hu_ψφ_int hu_mul2_int]
    have hright_eq :
        -∫ x, u.grad x i * ψφ x ∂μU -
            ∫ x, u x * (ψ x * dφ x) ∂μU =
          -∫ x, (φ x * u.grad x i + u x * dφ x) * ψ x ∂μU := by
      have hgrad_term :
          ∫ x, u.grad x i * ψφ x ∂μU =
            ∫ x, u.grad x i * (φ x * ψ x) ∂μU := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        simp [ψφ]
      have hu_term :
          ∫ x, u x * (ψ x * dφ x) ∂μU =
            ∫ x, (u x * dφ x) * ψ x ∂μU := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        ring
      have hsum :
          ∫ x, (φ x * u.grad x i + u x * dφ x) * ψ x ∂μU =
            ∫ x, u.grad x i * (φ x * ψ x) ∂μU +
              ∫ x, (u x * dφ x) * ψ x ∂μU := by
        calc
          ∫ x, (φ x * u.grad x i + u x * dφ x) * ψ x ∂μU
              = ∫ x, u.grad x i * (φ x * ψ x) + (u x * dφ x) * ψ x ∂μU := by
                  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
                  intro x
                  ring
          _ = ∫ x, u.grad x i * (φ x * ψ x) ∂μU +
                ∫ x, (u x * dφ x) * ψ x ∂μU := by
                  rw [MeasureTheory.integral_add hgrad_mul1_int hu_mul2ψ_int]
      rw [hgrad_term, hu_term, hsum]
      ring
    calc
      ∫ x, (φ x * u x) * dψ x ∂μU
          = ∫ x, u x * (φ x * dψ x) ∂μU := hleft_eq
      _ = ∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU -
            ∫ x, u x * (ψ x * dφ x) ∂μU := hsplit
      _ = -∫ x, u.grad x i * ψφ x ∂μU -
            ∫ x, u x * (ψ x * dφ x) ∂μU := by
            rw [hu_eq]
      _ = -∫ x, (φ x * u.grad x i + u x * dφ x) * ψ x ∂μU := hright_eq

@[simp] theorem mulContDiffMemLpTop_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) (MeasureTheory.volume.restrict U))
    (hdφ_memTop : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => (fderiv ℝ φ x) (basisVec i))
        (⊤ : ENNReal) (MeasureTheory.volume.restrict U)) :
    (u.mulContDiffMemLpTop hφ hφ_memTop hdφ_memTop).toFun = fun x => φ x * u x :=
  by
    simp [H1Function.mulContDiffMemLpTop]

@[simp] theorem mulContDiffMemLpTop_grad {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) (MeasureTheory.volume.restrict U))
    (hdφ_memTop : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => (fderiv ℝ φ x) (basisVec i))
        (⊤ : ENNReal) (MeasureTheory.volume.restrict U)) :
    (u.mulContDiffMemLpTop hφ hφ_memTop hdφ_memTop).grad =
      fun x i => φ x * u.grad x i + u x * (fderiv ℝ φ x) (basisVec i) :=
  by
    simp [H1Function.mulContDiffMemLpTop]

noncomputable def mulContDiffHasCompactSupport {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) : H1Function U := by
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  let Dφ : Vec d → Vec d := fun x i => (fderiv ℝ φ x) (basisVec i)
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) (MeasureTheory.volume.restrict U) :=
    (hφ_cont.memLp_of_hasCompactSupport hφ_compact).restrict U
  refine
    { toFun := fun x => φ x * u x
      grad := fun x i => φ x * u.grad x i + u x * Dφ x i
      memL2 := ?_
      gradMemL2 := ?_
      hasWeakGradient := ?_ }
  · simpa [Dφ, μU, mul_comm] using u.memL2.fun_mul (r := 2) hφ_memTop
  · intro i
    let dφ : Vec d → ℝ := fun x => Dφ x i
    have hdφ_cont : Continuous dφ := by
      simpa [dφ, Dφ] using
        (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφ_compact : HasCompactSupport dφ := by
      simpa [dφ, Dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hdφ_memTop : MeasureTheory.MemLp dφ (⊤ : ENNReal) (MeasureTheory.volume.restrict U) :=
      (hdφ_cont.memLp_of_hasCompactSupport hdφ_compact).restrict U
    have hfirst :
        MeasureTheory.MemLp (fun x => φ x * u.grad x i) 2 μU := by
      simpa [μU, mul_comm] using (u.gradMemL2 i).fun_mul (r := 2) hφ_memTop
    have hsecond :
        MeasureTheory.MemLp (fun x => u x * dφ x) 2 μU := by
      simpa [dφ, μU, mul_comm] using u.memL2.mul' hdφ_memTop
    simpa [dφ, Dφ, Pi.add_apply] using! hfirst.add hsecond
  · intro i ψ hψ_smooth hψ_compact hψ_sub
    let ei : Vec d := basisVec i
    let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) ei
    let dψ : Vec d → ℝ := fun x => (fderiv ℝ ψ x) ei
    let ψφ : Vec d → ℝ := fun x => φ x * ψ x
    change
      ∫ x, (φ x * u x) * dψ x ∂μU =
        -∫ x, (φ x * u.grad x i + u x * dφ x) * ψ x ∂μU
    have hψ_cont : Continuous ψ := hψ_smooth.continuous
    have hdφ_cont : Continuous dφ := by
      simpa [dφ] using
        (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψ_cont : Continuous dψ := by
      simpa [dψ] using
        (hψ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφ_compact : HasCompactSupport dφ := by
      simpa [dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) ei
    have hdψ_compact : HasCompactSupport dψ := by
      simpa [dψ] using hψ_compact.fderiv_apply (𝕜 := ℝ) ei
    have hψφ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψφ := hφ.mul hψ_smooth
    have hψφ_compact : HasCompactSupport ψφ := by
      simpa [ψφ] using! hψ_compact.mul_left (f := φ)
    have hdψφ_cont : Continuous (fun x => (fderiv ℝ ψφ x) ei) := by
      simpa [ei] using
        (hψφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdψφ_compact : HasCompactSupport (fun x => (fderiv ℝ ψφ x) ei) := by
      simpa [ei] using hψφ_compact.fderiv_apply (𝕜 := ℝ) ei
    have hψφ_sub : tsupport ψφ ⊆ U := by
      exact (tsupport_mul_subset_right (f := φ) (g := ψ)).trans hψ_sub
    have hu_eq :
        ∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU =
          -∫ x, u.grad x i * ψφ x ∂μU := by
      simpa [μU] using u.hasWeakGradient i ψφ hψφ_smooth hψφ_compact hψφ_sub
    have hu_loc : MeasureTheory.LocallyIntegrable u μU :=
      u.memL2.locallyIntegrable (by norm_num)
    have hgrad_loc : MeasureTheory.LocallyIntegrable (fun x => u.grad x i) μU :=
      (u.gradMemL2 i).locallyIntegrable (by norm_num)
    have hmul1_cont : Continuous (fun x => φ x * dψ x) := hφ_cont.mul hdψ_cont
    have hmul1_compact : HasCompactSupport (fun x => φ x * dψ x) := by
      simpa using! hdψ_compact.mul_left (f := φ)
    have hu_mul1_int :
        MeasureTheory.Integrable (fun x => u x * (φ x * dψ x)) μU := by
      simpa [smul_eq_mul, μU, mul_assoc] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hmul1_cont hmul1_compact
    have hmul2_cont : Continuous (fun x => ψ x * dφ x) := hψ_cont.mul hdφ_cont
    have hmul2_compact : HasCompactSupport (fun x => ψ x * dφ x) := by
      simpa [mul_comm] using! hdφ_compact.mul_left (f := ψ)
    have hu_mul2_int :
        MeasureTheory.Integrable (fun x => u x * (ψ x * dφ x)) μU := by
      simpa [smul_eq_mul, μU, mul_assoc] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hmul2_cont hmul2_compact
    have hu_ψφ_int :
        MeasureTheory.Integrable (fun x => u x * (fderiv ℝ ψφ x) ei) μU := by
      simpa [smul_eq_mul, μU] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hdψφ_cont hdψφ_compact
    have hgrad_mul1_int :
        MeasureTheory.Integrable (fun x => u.grad x i * (φ x * ψ x)) μU := by
      simpa [smul_eq_mul, μU, mul_assoc] using
        hgrad_loc.integrable_smul_right_of_hasCompactSupport
          (hφ_cont.mul hψ_cont) hψφ_compact
    have hu_mul2ψ_int :
        MeasureTheory.Integrable (fun x => (u x * dφ x) * ψ x) μU := by
      simpa [smul_eq_mul, μU, mul_assoc, mul_left_comm, mul_comm] using
        hu_loc.integrable_smul_right_of_hasCompactSupport hmul2_cont hmul2_compact
    have hprod_deriv :
        ∀ x, (fderiv ℝ ψφ x) ei = φ x * dψ x + ψ x * dφ x := by
      intro x
      have hφ_diff : DifferentiableAt ℝ φ x :=
        (hφ.contDiffAt).differentiableAt (by simp)
      have hψ_diff : DifferentiableAt ℝ ψ x :=
        (hψ_smooth.contDiffAt).differentiableAt (by simp)
      rw [show ψφ = φ * ψ by rfl, fderiv_mul hφ_diff hψ_diff]
      simp [dφ, dψ, ei, smul_eq_mul]
    have hleft_eq :
        ∫ x, (φ x * u x) * dψ x ∂μU =
          ∫ x, u x * (φ x * dψ x) ∂μU := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro x
      ring
    have hsplit :
        ∫ x, u x * (φ x * dψ x) ∂μU =
          ∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU -
            ∫ x, u x * (ψ x * dφ x) ∂μU := by
      calc
        ∫ x, u x * (φ x * dψ x) ∂μU
            = ∫ x, (u x * (fderiv ℝ ψφ x) ei) - u x * (ψ x * dφ x) ∂μU := by
                refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
                intro x
                have hx :
                    u x * (φ x * dψ x) =
                      u x * (fderiv ℝ ψφ x) ei - u x * (ψ x * dφ x) := by
                  rw [hprod_deriv x]
                  ring
                exact hx
        _ = ∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU -
              ∫ x, u x * (ψ x * dφ x) ∂μU := by
                rw [MeasureTheory.integral_sub hu_ψφ_int hu_mul2_int]
    have hright_eq :
        -∫ x, u.grad x i * ψφ x ∂μU -
            ∫ x, u x * (ψ x * dφ x) ∂μU =
          -∫ x, (φ x * u.grad x i + u x * dφ x) * ψ x ∂μU := by
      have hgrad_term :
          ∫ x, u.grad x i * ψφ x ∂μU =
            ∫ x, u.grad x i * (φ x * ψ x) ∂μU := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        simp [ψφ]
      have hu_term :
          ∫ x, u x * (ψ x * dφ x) ∂μU =
            ∫ x, (u x * dφ x) * ψ x ∂μU := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro x
        ring
      have hsum :
          ∫ x, (φ x * u.grad x i + u x * dφ x) * ψ x ∂μU =
            ∫ x, u.grad x i * (φ x * ψ x) ∂μU +
              ∫ x, (u x * dφ x) * ψ x ∂μU := by
        calc
          ∫ x, (φ x * u.grad x i + u x * dφ x) * ψ x ∂μU
              = ∫ x, u.grad x i * (φ x * ψ x) + (u x * dφ x) * ψ x ∂μU := by
                  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
                  intro x
                  ring
          _ = ∫ x, u.grad x i * (φ x * ψ x) ∂μU +
                ∫ x, (u x * dφ x) * ψ x ∂μU := by
                  rw [MeasureTheory.integral_add hgrad_mul1_int hu_mul2ψ_int]
      rw [hgrad_term, hu_term, hsum]
      ring
    calc
      ∫ x, (φ x * u x) * dψ x ∂μU
          = ∫ x, u x * (φ x * dψ x) ∂μU := hleft_eq
      _ = ∫ x, u x * (fderiv ℝ ψφ x) ei ∂μU -
            ∫ x, u x * (ψ x * dφ x) ∂μU := hsplit
      _ = -∫ x, u.grad x i * ψφ x ∂μU -
            ∫ x, u x * (ψ x * dφ x) ∂μU := by
            rw [hu_eq]
      _ = -∫ x, (φ x * u.grad x i + u x * dφ x) * ψ x ∂μU := hright_eq

@[simp] theorem mulContDiffHasCompactSupport_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφ_compact).toFun = fun x => φ x * u x :=
  by
    simp [H1Function.mulContDiffHasCompactSupport]

@[simp] theorem mulContDiffHasCompactSupport_grad {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφ_compact).grad =
      fun x i => φ x * u.grad x i + u x * (fderiv ℝ φ x) (basisVec i) :=
  by
    simp [H1Function.mulContDiffHasCompactSupport]

end H1Function

end Homogenization
