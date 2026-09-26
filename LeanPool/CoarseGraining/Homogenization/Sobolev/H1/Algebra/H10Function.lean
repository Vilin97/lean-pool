/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Algebra.H1Function

/-! # H10Function -/

@[expose] public section

namespace Homogenization
namespace H10Function

instance {d : ℕ} {U : Set (Vec d)} : Zero (H10Function U) where
  zero :=
    { toH1Function := 0
      approx := fun _ => 0
      approx_smooth := by
        intro n
        simpa using! (contDiff_zero_fun : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d => (0 : ℝ)))
      approx_hasCompactSupport := by
        intro n
        simpa using (HasCompactSupport.zero : HasCompactSupport (0 : Vec d → ℝ))
      approx_support_subset := by
        intro n
        simp
      tendsto_approx := by
        simp
      tendsto_approx_grad := by
        intro i
        simp }

instance {d : ℕ} {U : Set (Vec d)} : SMul ℝ (H10Function U) where
  smul c u :=
    { toH1Function := c • u.toH1Function
      approx := fun n x => c * u.approx n x
      approx_smooth := by
        intro n
        simpa [smul_eq_mul] using (u.approx_smooth n).const_smul c
      approx_hasCompactSupport := by
        intro n
        simpa [Pi.smul_apply, smul_eq_mul] using!
          (u.approx_hasCompactSupport n).smul_left (f := fun _ : Vec d => c)
      approx_support_subset := by
        intro n
        simpa [Pi.smul_apply, smul_eq_mul] using
          (tsupport_smul_subset_right (fun _ : Vec d => c) (u.approx n)).trans
            (u.approx_support_subset n)
      tendsto_approx := by
        have hscaled :
            Filter.Tendsto
              (fun n =>
                ‖c‖ₑ *
                  MeasureTheory.eLpNorm
                    (fun x => u.approx n x - u.toH1Function.toFun x) 2
                    (MeasureTheory.volume.restrict U))
              Filter.atTop (nhds (‖c‖ₑ * 0)) :=
          ENNReal.Tendsto.const_mul u.tendsto_approx (Or.inr ENNReal.coe_ne_top)
        have hEq :
            (fun n =>
              MeasureTheory.eLpNorm
                (fun x => c * u.approx n x - (c • u.toH1Function).toFun x) 2
                (MeasureTheory.volume.restrict U)) =
              (fun n =>
                ‖c‖ₑ *
                  MeasureTheory.eLpNorm
                    (fun x => u.approx n x - u.toH1Function.toFun x) 2
                    (MeasureTheory.volume.restrict U)) := by
          funext n
          have hfun :
              (fun x => c * u.approx n x - (c • u.toH1Function).toFun x) =
                c • (fun x => u.approx n x - u.toH1Function.toFun x) := by
            funext x
            change c * u.approx n x - c * u.toH1Function.toFun x =
              c * (u.approx n x - u.toH1Function.toFun x)
            ring
          rw [hfun, MeasureTheory.eLpNorm_const_smul]
        rw [hEq]
        simpa using hscaled
      tendsto_approx_grad := by
        intro i
        have hscaled :
            Filter.Tendsto
              (fun n =>
                ‖c‖ₑ *
                  MeasureTheory.eLpNorm
                    (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                    2 (MeasureTheory.volume.restrict U))
              Filter.atTop (nhds (‖c‖ₑ * 0)) :=
          ENNReal.Tendsto.const_mul (u.tendsto_approx_grad i) (Or.inr ENNReal.coe_ne_top)
        have hEq :
            (fun n =>
              MeasureTheory.eLpNorm
                (fun x =>
                  (fderiv ℝ (fun y => c * u.approx n y) x) (basisVec i) -
                    (c • u.toH1Function).grad x i)
                2 (MeasureTheory.volume.restrict U)) =
              (fun n =>
                ‖c‖ₑ *
                  MeasureTheory.eLpNorm
                    (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                    2 (MeasureTheory.volume.restrict U)) := by
          funext n
          have hfun :
              (fun x =>
                (fderiv ℝ (fun y => c * u.approx n y) x) (basisVec i) -
                  (c • u.toH1Function).grad x i) =
                c • (fun x =>
                  (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i) := by
            funext x
            have hfd : fderiv ℝ (fun y => c * u.approx n y) x = c • fderiv ℝ (u.approx n) x := by
              simpa [smul_eq_mul] using!
                congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := u.approx n) c) x
            rw [hfd]
            have hgrad : (c • u.toH1Function).grad x i = c * u.grad x i := by
              rfl
            rw [hgrad]
            simp [Pi.smul_apply, smul_eq_mul]
            ring
          rw [hfun, MeasureTheory.eLpNorm_const_smul]
        rw [hEq]
        simpa using hscaled }

instance {d : ℕ} {U : Set (Vec d)} : Neg (H10Function U) where
  neg u := (-1 : ℝ) • u

instance {d : ℕ} {U : Set (Vec d)} : Add (H10Function U) where
  add u v :=
    { toH1Function := u.toH1Function + v.toH1Function
      approx := fun n x => u.approx n x + v.approx n x
      approx_smooth := by
        intro n
        exact (u.approx_smooth n).add (v.approx_smooth n)
      approx_hasCompactSupport := by
        intro n
        exact (u.approx_hasCompactSupport n).add (v.approx_hasCompactSupport n)
      approx_support_subset := by
        intro n
        exact (tsupport_add (u.approx n) (v.approx n)).trans <|
          Set.union_subset (u.approx_support_subset n) (v.approx_support_subset n)
      tendsto_approx := by
        have hupper :
            ∀ n,
              MeasureTheory.eLpNorm
                  (fun x => (u.approx n x + v.approx n x) - (u.toH1Function + v.toH1Function).toFun x)
                  2 (MeasureTheory.volume.restrict U) ≤
                MeasureTheory.eLpNorm
                    (fun x => u.approx n x - u.toH1Function.toFun x)
                    2 (MeasureTheory.volume.restrict U) +
                  MeasureTheory.eLpNorm
                    (fun x => v.approx n x - v.toH1Function.toFun x)
                    2 (MeasureTheory.volume.restrict U) := by
          intro n
          have hu_mem : MeasureTheory.MemLp (u.approx n) 2 (MeasureTheory.volume.restrict U) :=
            ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport (u.approx_hasCompactSupport n)).restrict U
          have hv_mem : MeasureTheory.MemLp (v.approx n) 2 (MeasureTheory.volume.restrict U) :=
            ((v.approx_smooth n).continuous.memLp_of_hasCompactSupport (v.approx_hasCompactSupport n)).restrict U
          have hdu_mem :
              MeasureTheory.MemLp
                (fun x => u.approx n x - u.toH1Function.toFun x) 2
                (MeasureTheory.volume.restrict U) :=
            hu_mem.sub u.toH1Function.memL2
          have hdv_mem :
              MeasureTheory.MemLp
                (fun x => v.approx n x - v.toH1Function.toFun x) 2
                (MeasureTheory.volume.restrict U) :=
            hv_mem.sub v.toH1Function.memL2
          have hEq :
              (fun x => (u.approx n x + v.approx n x) - (u.toH1Function + v.toH1Function).toFun x) =
                (fun x =>
                  (u.approx n x - u.toH1Function.toFun x) +
                    (v.approx n x - v.toH1Function.toFun x)) := by
            funext x
            change
              (u.approx n x + v.approx n x) - (u.toH1Function.toFun x + v.toH1Function.toFun x) =
                (u.approx n x - u.toH1Function.toFun x) + (v.approx n x - v.toH1Function.toFun x)
            ring
          rw [hEq]
          exact MeasureTheory.eLpNorm_add_le (by norm_num)
        have hsum :
            Filter.Tendsto
              (fun n =>
                MeasureTheory.eLpNorm
                    (fun x => u.approx n x - u.toH1Function.toFun x)
                    2 (MeasureTheory.volume.restrict U) +
                  MeasureTheory.eLpNorm
                    (fun x => v.approx n x - v.toH1Function.toFun x)
                    2 (MeasureTheory.volume.restrict U))
              Filter.atTop (nhds (0 + 0)) :=
          u.tendsto_approx.add v.tendsto_approx
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds ?_ (fun n => zero_le) hupper
        simpa using hsum
      tendsto_approx_grad := by
        intro i
        have hupper :
            ∀ n,
              MeasureTheory.eLpNorm
                  (fun x =>
                    (fderiv ℝ (fun y => u.approx n y + v.approx n y) x) (basisVec i) -
                      (u.toH1Function + v.toH1Function).grad x i)
                  2 (MeasureTheory.volume.restrict U) ≤
                MeasureTheory.eLpNorm
                    (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                    2 (MeasureTheory.volume.restrict U) +
                  MeasureTheory.eLpNorm
                    (fun x => (fderiv ℝ (v.approx n) x) (basisVec i) - v.toH1Function.grad x i)
                    2 (MeasureTheory.volume.restrict U) := by
          intro n
          have hderiv_u_smooth :
              ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) :=
            ((u.approx_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
              contDiff_const
          have hderiv_v_smooth :
              ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ (v.approx n) x) (basisVec i)) :=
            ((v.approx_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
              contDiff_const
          have hderiv_u_mem :
              MeasureTheory.MemLp
                (fun x => (fderiv ℝ (u.approx n) x) (basisVec i))
                2 (MeasureTheory.volume.restrict U) :=
            (hderiv_u_smooth.continuous.memLp_of_hasCompactSupport
              ((u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict U
          have hderiv_v_mem :
              MeasureTheory.MemLp
                (fun x => (fderiv ℝ (v.approx n) x) (basisVec i))
                2 (MeasureTheory.volume.restrict U) :=
            (hderiv_v_smooth.continuous.memLp_of_hasCompactSupport
              ((v.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict U
          have hdu_mem :
              MeasureTheory.MemLp
                (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                2 (MeasureTheory.volume.restrict U) :=
            hderiv_u_mem.sub (u.toH1Function.gradMemL2 i)
          have hdv_mem :
              MeasureTheory.MemLp
                (fun x => (fderiv ℝ (v.approx n) x) (basisVec i) - v.toH1Function.grad x i)
                2 (MeasureTheory.volume.restrict U) :=
            hderiv_v_mem.sub (v.toH1Function.gradMemL2 i)
          have hEq :
              (fun x =>
                (fderiv ℝ (fun y => u.approx n y + v.approx n y) x) (basisVec i) -
                  (u.toH1Function + v.toH1Function).grad x i) =
                (fun x =>
                  ((fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i) +
                    ((fderiv ℝ (v.approx n) x) (basisVec i) - v.toH1Function.grad x i)) := by
            funext x
            have hfd :
                fderiv ℝ (fun y => u.approx n y + v.approx n y) x =
                  fderiv ℝ (u.approx n) x + fderiv ℝ (v.approx n) x := by
              have hu_diff : DifferentiableAt ℝ (u.approx n) x :=
                ((u.approx_smooth n).contDiffAt).differentiableAt (by norm_num)
              have hv_diff : DifferentiableAt ℝ (v.approx n) x :=
                ((v.approx_smooth n).contDiffAt).differentiableAt (by norm_num)
              exact fderiv_add hu_diff hv_diff
            rw [hfd]
            have hgrad : (u.toH1Function + v.toH1Function).grad x i = u.grad x i + v.grad x i := by
              rfl
            rw [hgrad]
            change
              ((fderiv ℝ (u.approx n) x) (basisVec i) + (fderiv ℝ (v.approx n) x) (basisVec i)) -
                  (u.grad x i + v.grad x i) =
                ((fderiv ℝ (u.approx n) x) (basisVec i) - u.grad x i) +
                  ((fderiv ℝ (v.approx n) x) (basisVec i) - v.grad x i)
            ring
          rw [hEq]
          exact MeasureTheory.eLpNorm_add_le (by norm_num)
        have hsum :
            Filter.Tendsto
              (fun n =>
                MeasureTheory.eLpNorm
                    (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                    2 (MeasureTheory.volume.restrict U) +
                  MeasureTheory.eLpNorm
                    (fun x => (fderiv ℝ (v.approx n) x) (basisVec i) - v.toH1Function.grad x i)
                    2 (MeasureTheory.volume.restrict U))
              Filter.atTop (nhds (0 + 0)) :=
          (u.tendsto_approx_grad i).add (v.tendsto_approx_grad i)
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds ?_ (fun n => zero_le) hupper
        simpa using hsum }

instance {d : ℕ} {U : Set (Vec d)} : Sub (H10Function U) where
  sub u v := u + (-v)

/-- Multiplication of an `H¹₀` function by a smooth scalar multiplier which is
bounded, together with its first derivatives, on the underlying domain.  The
approximants remain compactly supported in the domain because the original
`H¹₀` approximants are compactly supported there. -/
noncomputable def mulContDiffMemLpTop {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) (MeasureTheory.volume.restrict U))
    (hdφ_memTop : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => (fderiv ℝ φ x) (basisVec i))
        (⊤ : ENNReal) (MeasureTheory.volume.restrict U)) :
    H10Function U := by
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  let uφ : H1Function U := u.toH1Function.mulContDiffMemLpTop hφ hφ_memTop hdφ_memTop
  let Dφ : Vec d → Vec d := fun x i => (fderiv ℝ φ x) (basisVec i)
  refine
    { toH1Function := uφ
      approx := fun n x => φ x * u.approx n x
      approx_smooth := ?_
      approx_hasCompactSupport := ?_
      approx_support_subset := ?_
      tendsto_approx := ?_
      tendsto_approx_grad := ?_ }
  · intro n
    exact hφ.mul (u.approx_smooth n)
  · intro n
    simpa using! (u.approx_hasCompactSupport n).mul_left (f := φ)
  · intro n
    exact (tsupport_mul_subset_right (f := φ) (g := u.approx n)).trans
      (u.approx_support_subset n)
  ·
    have hconst_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU)
          Filter.atTop
          (nhds (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0)) :=
      ENNReal.Tendsto.const_mul u.tendsto_approx
        (Or.inr hφ_memTop.eLpNorm_lt_top.ne)
    have hupper :
        ∀ n,
          MeasureTheory.eLpNorm
              (fun x => φ x * u.approx n x - uφ.toFun x) 2 μU ≤
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
      intro n
      have hdiff_mem :
          MeasureTheory.MemLp
            (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
        have happrox_mem :
            MeasureTheory.MemLp (u.approx n) 2 μU :=
          ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
            (u.approx_hasCompactSupport n)).restrict U
        exact happrox_mem.sub u.toH1Function.memL2
      have hEq :
          (fun x => φ x * u.approx n x - uφ.toFun x) =
            φ • (fun x => u.approx n x - u.toH1Function.toFun x) := by
        funext x
        change φ x * u.approx n x - φ x * u.toH1Function.toFun x =
          φ x * (u.approx n x - u.toH1Function.toFun x)
        ring
      rw [hEq]
      exact MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (φ := φ) 2 (by norm_num)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun n => zero_le) hupper
    simpa using hconst_tendsto
  · intro i
    let dφ : Vec d → ℝ := fun x => Dφ x i
    have hfirst_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                2 μU)
          Filter.atTop
          (nhds (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0)) :=
      ENNReal.Tendsto.const_mul (u.tendsto_approx_grad i)
        (Or.inr hφ_memTop.eLpNorm_lt_top.ne)
    have hsecond_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU)
          Filter.atTop
          (nhds (MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU * 0)) :=
      ENNReal.Tendsto.const_mul u.tendsto_approx
        (Or.inr (by simpa [dφ, Dφ, μU] using (hdφ_memTop i).eLpNorm_lt_top.ne))
    have hsum_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                  2 μU +
              MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU)
          Filter.atTop
          (nhds
            (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0 +
              MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU * 0)) :=
      hfirst_tendsto.add hsecond_tendsto
    have hupper :
        ∀ n,
          MeasureTheory.eLpNorm
              (fun x =>
                (fderiv ℝ (fun y => φ y * u.approx n y) x) (basisVec i) - uφ.grad x i)
              2 μU ≤
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                  2 μU +
              MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
      intro n
      let A : Vec d → ℝ := fun x => φ x *
        ((fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
      let B : Vec d → ℝ := fun x => dφ x * (u.approx n x - u.toH1Function.toFun x)
      have hbase_grad_mem :
          MeasureTheory.MemLp
            (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
            2 μU := by
        have happrox_grad_smooth :
            ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) :=
          ((u.approx_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
            contDiff_const
        have happrox_grad_mem :
            MeasureTheory.MemLp
              (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) 2 μU :=
          (happrox_grad_smooth.continuous.memLp_of_hasCompactSupport
            ((u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict U
        exact happrox_grad_mem.sub (u.toH1Function.gradMemL2 i)
      have hbase_mem :
          MeasureTheory.MemLp
            (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
        have happrox_mem :
            MeasureTheory.MemLp (u.approx n) 2 μU :=
          ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
            (u.approx_hasCompactSupport n)).restrict U
        exact happrox_mem.sub u.toH1Function.memL2
      have hA_mem :
          MeasureTheory.MemLp A 2 μU := by
        simpa [A, μU, mul_comm] using hbase_grad_mem.fun_mul (r := 2) hφ_memTop
      have hB_mem :
          MeasureTheory.MemLp B 2 μU := by
        simpa [B, dφ, Dφ, μU, mul_comm] using hbase_mem.fun_mul (r := 2) (hdφ_memTop i)
      have hEq :
          (fun x =>
            (fderiv ℝ (fun y => φ y * u.approx n y) x) (basisVec i) - uφ.grad x i) =
            fun x => A x + B x := by
        funext x
        have hφ_diff : DifferentiableAt ℝ φ x :=
          (hφ.contDiffAt).differentiableAt (by simp)
        have hu_diff : DifferentiableAt ℝ (u.approx n) x :=
          ((u.approx_smooth n).contDiffAt).differentiableAt (by simp)
        rw [show (fun y => φ y * u.approx n y) = φ * u.approx n by rfl,
          fderiv_mul hφ_diff hu_diff]
        simp [A, B, dφ, Dφ, uφ, H1Function.mulContDiffMemLpTop_grad,
          smul_eq_mul]
        ring
      rw [hEq]
      refine (MeasureTheory.eLpNorm_add_le (by norm_num)).trans ?_
      refine add_le_add ?_ ?_
      · simpa [A, mul_comm, mul_left_comm, mul_assoc] using!
          (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μU)
            (φ := φ) (f := fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.grad x i)
            2 (by norm_num))
      · simpa [B, dφ, mul_comm, mul_left_comm, mul_assoc] using!
          (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μU) (φ := dφ)
            (f := fun x => u.approx n x - u.toH1Function.toFun x) 2 (by norm_num))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun n => zero_le) hupper
    simpa [zero_add] using hsum_tendsto

@[simp] theorem mulContDiffMemLpTop_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) (MeasureTheory.volume.restrict U))
    (hdφ_memTop : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => (fderiv ℝ φ x) (basisVec i))
        (⊤ : ENNReal) (MeasureTheory.volume.restrict U)) :
    (u.mulContDiffMemLpTop hφ hφ_memTop hdφ_memTop).toH1Function.toFun =
      fun x => φ x * u x :=
  by
    simp [H10Function.mulContDiffMemLpTop]

@[simp] theorem mulContDiffMemLpTop_grad {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) (MeasureTheory.volume.restrict U))
    (hdφ_memTop : ∀ i : Fin d,
      MeasureTheory.MemLp (fun x => (fderiv ℝ φ x) (basisVec i))
        (⊤ : ENNReal) (MeasureTheory.volume.restrict U)) :
    (u.mulContDiffMemLpTop hφ hφ_memTop hdφ_memTop).toH1Function.grad =
      fun x i => φ x * u.toH1Function.grad x i + u.toH1Function.toFun x *
        (fderiv ℝ φ x) (basisVec i) :=
  by
    simp [H10Function.mulContDiffMemLpTop, H1Function.mulContDiffMemLpTop_grad]

/-- Multiplication of an `H¹₀` function by a smooth compactly supported scalar
function.  Unlike `mulSmoothCutoff`, the multiplier itself need not be
supported in the domain: the `H¹₀` approximants already have support in the
domain, and multiplying them by the scalar multiplier preserves that support. -/
noncomputable def mulContDiffHasCompactSupport {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ) :
    H10Function U := by
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  let uφ : H1Function U := u.toH1Function.mulContDiffHasCompactSupport hφ hφ_compact
  let Dφ : Vec d → Vec d := fun x i => (fderiv ℝ φ x) (basisVec i)
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) μU :=
    (hφ_cont.memLp_of_hasCompactSupport hφ_compact).restrict U
  refine
    { toH1Function := uφ
      approx := fun n x => φ x * u.approx n x
      approx_smooth := ?_
      approx_hasCompactSupport := ?_
      approx_support_subset := ?_
      tendsto_approx := ?_
      tendsto_approx_grad := ?_ }
  · intro n
    exact hφ.mul (u.approx_smooth n)
  · intro n
    simpa using! (u.approx_hasCompactSupport n).mul_left (f := φ)
  · intro n
    exact (tsupport_mul_subset_right (f := φ) (g := u.approx n)).trans
      (u.approx_support_subset n)
  ·
    have hconst_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU)
          Filter.atTop
          (nhds (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0)) :=
      ENNReal.Tendsto.const_mul u.tendsto_approx
        (Or.inr hφ_memTop.eLpNorm_lt_top.ne)
    have hupper :
        ∀ n,
          MeasureTheory.eLpNorm
              (fun x => φ x * u.approx n x - uφ.toFun x) 2 μU ≤
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
      intro n
      have hdiff_mem :
          MeasureTheory.MemLp
            (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
        have happrox_mem :
            MeasureTheory.MemLp (u.approx n) 2 μU :=
          ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
            (u.approx_hasCompactSupport n)).restrict U
        exact happrox_mem.sub u.toH1Function.memL2
      have hEq :
          (fun x => φ x * u.approx n x - uφ.toFun x) =
            φ • (fun x => u.approx n x - u.toH1Function.toFun x) := by
        funext x
        change φ x * u.approx n x - φ x * u.toH1Function.toFun x =
          φ x * (u.approx n x - u.toH1Function.toFun x)
        ring
      rw [hEq]
      exact MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (φ := φ) 2 (by norm_num)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun n => zero_le) hupper
    simpa using hconst_tendsto
  · intro i
    let dφ : Vec d → ℝ := fun x => Dφ x i
    have hdφ_cont : Continuous dφ := by
      simpa [dφ, Dφ] using
        (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφ_compact : HasCompactSupport dφ := by
      simpa [dφ, Dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hdφ_memTop : MeasureTheory.MemLp dφ (⊤ : ENNReal) μU :=
      (hdφ_cont.memLp_of_hasCompactSupport hdφ_compact).restrict U
    have hfirst_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                2 μU)
          Filter.atTop
          (nhds (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0)) :=
      ENNReal.Tendsto.const_mul (u.tendsto_approx_grad i)
        (Or.inr hφ_memTop.eLpNorm_lt_top.ne)
    have hsecond_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU)
          Filter.atTop
          (nhds (MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU * 0)) :=
      ENNReal.Tendsto.const_mul u.tendsto_approx
        (Or.inr hdφ_memTop.eLpNorm_lt_top.ne)
    have hsum_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                  2 μU +
              MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU)
          Filter.atTop
          (nhds
            (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0 +
              MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU * 0)) :=
      hfirst_tendsto.add hsecond_tendsto
    have hupper :
        ∀ n,
          MeasureTheory.eLpNorm
              (fun x =>
                (fderiv ℝ (fun y => φ y * u.approx n y) x) (basisVec i) - uφ.grad x i)
              2 μU ≤
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                  2 μU +
              MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
      intro n
      let A : Vec d → ℝ := fun x => φ x *
        ((fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
      let B : Vec d → ℝ := fun x => dφ x * (u.approx n x - u.toH1Function.toFun x)
      have hbase_grad_mem :
          MeasureTheory.MemLp
            (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
            2 μU := by
        have happrox_grad_smooth :
            ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) :=
          ((u.approx_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
            contDiff_const
        have happrox_grad_mem :
            MeasureTheory.MemLp
              (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) 2 μU :=
          (happrox_grad_smooth.continuous.memLp_of_hasCompactSupport
            ((u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict U
        exact happrox_grad_mem.sub (u.toH1Function.gradMemL2 i)
      have hbase_mem :
          MeasureTheory.MemLp
            (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
        have happrox_mem :
            MeasureTheory.MemLp (u.approx n) 2 μU :=
          ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
            (u.approx_hasCompactSupport n)).restrict U
        exact happrox_mem.sub u.toH1Function.memL2
      have hA_mem :
          MeasureTheory.MemLp A 2 μU := by
        simpa [A, μU, mul_comm] using hbase_grad_mem.fun_mul (r := 2) hφ_memTop
      have hB_mem :
          MeasureTheory.MemLp B 2 μU := by
        simpa [B, dφ, μU, mul_comm] using hbase_mem.fun_mul (r := 2) hdφ_memTop
      have hEq :
          (fun x =>
            (fderiv ℝ (fun y => φ y * u.approx n y) x) (basisVec i) - uφ.grad x i) =
            fun x => A x + B x := by
        funext x
        have hφ_diff : DifferentiableAt ℝ φ x :=
          (hφ.contDiffAt).differentiableAt (by simp)
        have hu_diff : DifferentiableAt ℝ (u.approx n) x :=
          ((u.approx_smooth n).contDiffAt).differentiableAt (by simp)
        rw [show (fun y => φ y * u.approx n y) = φ * u.approx n by rfl,
          fderiv_mul hφ_diff hu_diff]
        simp [A, B, dφ, Dφ, uφ, H1Function.mulContDiffHasCompactSupport_grad,
          smul_eq_mul]
        ring
      rw [hEq]
      refine (MeasureTheory.eLpNorm_add_le (by norm_num)).trans ?_
      refine add_le_add ?_ ?_
      · simpa [A, mul_comm, mul_left_comm, mul_assoc] using!
          (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μU)
            (φ := φ) (f := fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.grad x i)
            2 (by norm_num))
      · simpa [B, dφ, mul_comm, mul_left_comm, mul_assoc] using!
          (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μU) (φ := dφ)
            (f := fun x => u.approx n x - u.toH1Function.toFun x) 2 (by norm_num))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun n => zero_le) hupper
    simpa [zero_add] using hsum_tendsto

@[simp] theorem mulContDiffHasCompactSupport_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H10Function U) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ) :
    (u.mulContDiffHasCompactSupport hφ hφ_compact).toH1Function.toFun =
      fun x => φ x * u x :=
  by
    simp [H10Function.mulContDiffHasCompactSupport]

noncomputable def mulSmoothCutoff {d : ℕ} {U : Set (Vec d)} (u : H10Function U)
    {φ : Vec d → ℝ} (hU : IsOpen U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    H10Function U := by
  let _ := hU
  let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
  let uφ : H1Function U := u.toH1Function.mulContDiffHasCompactSupport hφ hφ_compact
  let Dφ : Vec d → Vec d := fun x i => (fderiv ℝ φ x) (basisVec i)
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) (MeasureTheory.volume.restrict U) :=
    (hφ_cont.memLp_of_hasCompactSupport hφ_compact).restrict U
  refine
    { toH1Function := uφ
      approx := fun n x => φ x * u.approx n x
      approx_smooth := ?_
      approx_hasCompactSupport := ?_
      approx_support_subset := ?_
      tendsto_approx := ?_
      tendsto_approx_grad := ?_ }
  · intro n
    exact hφ.mul (u.approx_smooth n)
  · intro n
    simpa using! (u.approx_hasCompactSupport n).mul_left (f := φ)
  · intro n
    exact (tsupport_mul_subset_left (f := φ) (g := u.approx n)).trans hφ_sub
  ·
    have hconst_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU)
          Filter.atTop
          (nhds (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0)) :=
      ENNReal.Tendsto.const_mul u.tendsto_approx
        (Or.inr hφ_memTop.eLpNorm_lt_top.ne)
    have hupper :
        ∀ n,
          MeasureTheory.eLpNorm
              (fun x => φ x * u.approx n x - uφ.toFun x) 2 μU ≤
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
      intro n
      have hdiff_mem :
          MeasureTheory.MemLp
            (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
        have happrox_mem :
            MeasureTheory.MemLp (u.approx n) 2 μU :=
          ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
            (u.approx_hasCompactSupport n)).restrict U
        exact happrox_mem.sub u.toH1Function.memL2
      have hEq :
          (fun x => φ x * u.approx n x - uφ.toFun x) =
            φ • (fun x => u.approx n x - u.toH1Function.toFun x) := by
        funext x
        change φ x * u.approx n x - φ x * u.toH1Function.toFun x =
          φ x * (u.approx n x - u.toH1Function.toFun x)
        ring
      rw [hEq]
      exact MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (φ := φ) 2 (by norm_num)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun n => zero_le) hupper
    simpa using hconst_tendsto
  · intro i
    let dφ : Vec d → ℝ := fun x => Dφ x i
    have hdφ_cont : Continuous dφ := by
      simpa [dφ, Dφ] using
        (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφ_compact : HasCompactSupport dφ := by
      simpa [dφ, Dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
    have hdφ_memTop : MeasureTheory.MemLp dφ (⊤ : ENNReal) (MeasureTheory.volume.restrict U) :=
      (hdφ_cont.memLp_of_hasCompactSupport hdφ_compact).restrict U
    have hfirst_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                2 μU)
          Filter.atTop
          (nhds (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0)) :=
      ENNReal.Tendsto.const_mul (u.tendsto_approx_grad i)
        (Or.inr hφ_memTop.eLpNorm_lt_top.ne)
    have hsecond_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
              MeasureTheory.eLpNorm
                (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU)
          Filter.atTop
          (nhds (MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU * 0)) :=
      ENNReal.Tendsto.const_mul u.tendsto_approx
        (Or.inr hdφ_memTop.eLpNorm_lt_top.ne)
    have hsum_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                  2 μU +
              MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU)
          Filter.atTop
          (nhds
            (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0 +
              MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU * 0)) :=
      hfirst_tendsto.add hsecond_tendsto
    have hupper :
        ∀ n,
          MeasureTheory.eLpNorm
              (fun x =>
                (fderiv ℝ (fun y => φ y * u.approx n y) x) (basisVec i) - uφ.grad x i)
              2 μU ≤
            MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
                  2 μU +
              MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
                MeasureTheory.eLpNorm
                  (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
      intro n
      let A : Vec d → ℝ := fun x => φ x *
        ((fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
      let B : Vec d → ℝ := fun x => dφ x * (u.approx n x - u.toH1Function.toFun x)
      have hbase_grad_mem :
          MeasureTheory.MemLp
            (fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.toH1Function.grad x i)
            2 μU := by
        have happrox_grad_smooth :
            ContDiff ℝ (⊤ : ℕ∞) (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) :=
          ((u.approx_smooth n).fderiv_right (m := (⊤ : ℕ∞)) (by norm_cast)).clm_apply
            contDiff_const
        have happrox_grad_mem :
            MeasureTheory.MemLp
              (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) 2 μU :=
          (happrox_grad_smooth.continuous.memLp_of_hasCompactSupport
            ((u.approx_hasCompactSupport n).fderiv_apply (𝕜 := ℝ) (basisVec i))).restrict U
        exact happrox_grad_mem.sub (u.toH1Function.gradMemL2 i)
      have hbase_mem :
          MeasureTheory.MemLp
            (fun x => u.approx n x - u.toH1Function.toFun x) 2 μU := by
        have happrox_mem :
            MeasureTheory.MemLp (u.approx n) 2 μU :=
          ((u.approx_smooth n).continuous.memLp_of_hasCompactSupport
            (u.approx_hasCompactSupport n)).restrict U
        exact happrox_mem.sub u.toH1Function.memL2
      have hA_mem :
          MeasureTheory.MemLp A 2 μU := by
        simpa [A, μU, mul_comm] using hbase_grad_mem.fun_mul (r := 2) hφ_memTop
      have hB_mem :
          MeasureTheory.MemLp B 2 μU := by
        simpa [B, dφ, μU, mul_comm] using hbase_mem.fun_mul (r := 2) hdφ_memTop
      have hEq :
          (fun x =>
            (fderiv ℝ (fun y => φ y * u.approx n y) x) (basisVec i) - uφ.grad x i) =
            fun x => A x + B x := by
        funext x
        have hφ_diff : DifferentiableAt ℝ φ x :=
          (hφ.contDiffAt).differentiableAt (by simp)
        have hu_diff : DifferentiableAt ℝ (u.approx n) x :=
          ((u.approx_smooth n).contDiffAt).differentiableAt (by simp)
        rw [show (fun y => φ y * u.approx n y) = φ * u.approx n by rfl, fderiv_mul hφ_diff hu_diff]
        simp [A, B, dφ, Dφ, uφ, H1Function.mulContDiffHasCompactSupport_grad, smul_eq_mul]
        ring
      rw [hEq]
      refine (MeasureTheory.eLpNorm_add_le (by norm_num)).trans ?_
      refine add_le_add ?_ ?_
      · simpa [A, mul_comm, mul_left_comm, mul_assoc] using!
          (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μU)
            (φ := φ) (f := fun x => (fderiv ℝ (u.approx n) x) (basisVec i) - u.grad x i)
            2 (by norm_num))
      · simpa [B, dφ, mul_comm, mul_left_comm, mul_assoc] using!
          (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μU) (φ := dφ)
            (f := fun x => u.approx n x - u.toH1Function.toFun x) 2 (by norm_num))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds ?_ (fun n => zero_le) hupper
    simpa [zero_add] using hsum_tendsto

@[simp] theorem mulSmoothCutoff_toFun {d : ℕ} {U : Set (Vec d)} (u : H10Function U)
    {φ : Vec d → ℝ} (hU : IsOpen U) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    (u.mulSmoothCutoff hU hφ hφ_compact hφ_sub).toH1Function.toFun =
      fun x => φ x * u x :=
  by
    simp [H10Function.mulSmoothCutoff]

end H10Function

end Homogenization
