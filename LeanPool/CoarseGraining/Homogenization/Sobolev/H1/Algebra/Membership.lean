/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.Algebra.H10Function

/-! # Membership -/

@[expose] public section

namespace Homogenization

theorem memH1_zero {d : ℕ} {U : Set (Vec d)} : MemH1 U (0 : Vec d → ℝ) :=
  (0 : H1Function U).memH1

theorem memH1_smul {d : ℕ} {U : Set (Vec d)} (c : ℝ) {u : Vec d → ℝ} (hu : MemH1 U u) :
    MemH1 U (fun x => c * u x) := by
  rcases hu with ⟨v, rfl⟩
  simpa using ((c • v : H1Function U).memH1)

theorem memH1_neg {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ} (hu : MemH1 U u) :
    MemH1 U (fun x => -u x) := by
  rcases hu with ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  funext x
  change (-1 : ℝ) * v x = -(v x)
  ring

theorem memH1_add {d : ℕ} {U : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : MemH1 U u) (hv : MemH1 U v) : MemH1 U (fun x => u x + v x) := by
  rcases hu with ⟨u', rfl⟩
  rcases hv with ⟨v', rfl⟩
  simpa using ((u' + v' : H1Function U).memH1)

theorem memH1_sub {d : ℕ} {U : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : MemH1 U u) (hv : MemH1 U v) : MemH1 U (fun x => u x - v x) := by
  simpa [sub_eq_add_neg] using memH1_add hu (memH1_neg hv)

theorem memH10_zero {d : ℕ} {U : Set (Vec d)} : MemH10 U (0 : Vec d → ℝ) :=
  (0 : H10Function U).memH10

theorem memH10_smul {d : ℕ} {U : Set (Vec d)} (c : ℝ) {u : Vec d → ℝ} (hu : MemH10 U u) :
    MemH10 U (fun x => c * u x) := by
  rcases hu with ⟨v, rfl⟩
  simpa using! ((c • v : H10Function U).memH10)

theorem memH10_neg {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ} (hu : MemH10 U u) :
    MemH10 U (fun x => -u x) := by
  rcases hu with ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  funext x
  change (-1 : ℝ) * v x = -(v x)
  ring

theorem memH10_add {d : ℕ} {U : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : MemH10 U u) (hv : MemH10 U v) : MemH10 U (fun x => u x + v x) := by
  rcases hu with ⟨u', rfl⟩
  rcases hv with ⟨v', rfl⟩
  simpa using! ((u' + v' : H10Function U).memH10)

theorem memH10_sub {d : ℕ} {U : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : MemH10 U u) (hv : MemH10 U v) : MemH10 U (fun x => u x - v x) := by
  simpa [sub_eq_add_neg] using memH10_add hu (memH10_neg hv)

theorem memH1_mul_of_contDiff_hasCompactSupport {d : ℕ} {U : Set (Vec d)}
    {φ u : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hu : MemH1 U u) :
    MemH1 U (fun x => φ x * u x) := by
  rcases hu with ⟨u', rfl⟩
  simpa using (u'.mulContDiffHasCompactSupport hφ hφ_compact).memH1

theorem memH10_mul_of_contDiff_hasCompactSupport {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {φ u : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) (hu : MemH1 U u) :
    MemH10 U (fun x => φ x * u x) := by
  rcases hu with ⟨u', rfl⟩
  by_cases hts : tsupport φ = ∅
  · have hφ_zero : φ = 0 := tsupport_eq_empty_iff.mp hts
    simpa [hφ_zero] using! (memH10_zero (U := U))
  · obtain ⟨x0, hx0⟩ : (tsupport φ).Nonempty := Set.nonempty_iff_ne_empty.mpr hts
    have hx0U : x0 ∈ U := hφ_sub hx0
    rcases Metric.mem_nhds_iff.mp (hU.isOpen.mem_nhds hx0U) with ⟨r, hr_pos, hr_sub⟩
    let r0 : ℝ := r / 2
    have hr0_pos : 0 < r0 := by
      dsimp [r0]
      positivity
    have hball : Metric.closedBall x0 r0 ⊆ U := by
      refine (Metric.closedBall_subset_ball ?_).trans hr_sub
      dsimp [r0]
      exact half_lt_self hr_pos
    let ρ : Vec d → ℝ := unitConvexApproxKernel (d := d)
    let ε : ℕ → ℝ := unitConvexApproxScale
    let ψ : ℕ → Vec d → ℝ := fun n =>
      convexApproxSmoothRepresentative U ρ u' x0 r0 (ε n)
    let uφ : H1Function U := u'.mulContDiffHasCompactSupport hφ hφ_compact
    have hρ : IsConvexApproxKernel ρ := by
      simpa [ρ] using isConvexApproxKernel_unitConvexApproxKernel (d := d)
    have hε_pos : ∀ n : ℕ, 0 < ε n := by
      intro n
      dsimp [ε, unitConvexApproxScale]
      positivity
    have hε_eventually_lt_one : ∀ᶠ n : ℕ in Filter.atTop, ε n < 1 := by
      simpa [ε] using
        (((tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 1 zero_lt_one).mono
          (fun _ hn => hn))
    have hψ_smooth : ∀ n : ℕ, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := by
      intro n
      dsimp [ψ]
      exact contDiff_convexApproxSmoothRepresentative
        hU.isOpen.measurableSet hρ (by norm_num : (1 : ENNReal) ≤ 2) u'.memL2 hr0_pos
        (hε_pos n)
    have hψ_memL2 : ∀ n : ℕ, MeasureTheory.MemLp (ψ n) 2 (MeasureTheory.volume.restrict U) := by
      intro n
      let v : H1Function U :=
        H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU ((hψ_smooth n).of_le (by simp))
      simpa [ψ, v, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
        H1Function.ofContDiffOnIsSobolevRegularDomain]
        using v.memL2
    have hψ_grad_memL2 : ∀ n : ℕ, ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => (fderiv ℝ (ψ n) x) (basisVec i))
          2 (MeasureTheory.volume.restrict U) := by
      intro n i
      let v : H1Function U :=
        H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU ((hψ_smooth n).of_le (by simp))
      simpa [ψ, v, H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
        H1Function.ofContDiffOnIsSobolevRegularDomain]
        using v.gradMemL2 i
    have hψ_tendsto :
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm (fun x => ψ n x - u' x) 2
              (MeasureTheory.volume.restrict U))
          Filter.atTop (nhds 0) := by
      have hraw :=
        tendsto_eLpNorm_sub_zero_unitConvexApproxSequence_of_memLpOn
          (U := U) hU (by norm_num : (1 : ENNReal) ≤ 2) (by simp : (2 : ENNReal) ≠ ⊤)
          u'.memL2 hball hr0_pos
      refine hraw.congr' ?_
      filter_upwards [hε_eventually_lt_one] with n hε1
      apply MeasureTheory.eLpNorm_congr_ae
      filter_upwards [MeasureTheory.ae_restrict_mem hU.isOpen.measurableSet] with x hx
      have hEq :=
        convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
          (u := u') hU hρ hx hball hr0_pos (hε_pos n) hε1
      simpa [ψ, ρ, ε, unitConvexApproxSequence] using hEq.symm
    have hψ_grad_tendsto : ∀ i : Fin d,
        Filter.Tendsto
          (fun n =>
            MeasureTheory.eLpNorm
              (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - u'.grad x i)
              2 (MeasureTheory.volume.restrict U))
          Filter.atTop (nhds 0) := by
      intro i
      have hraw :=
        tendsto_eLpNorm_sub_zero_one_sub_mul_unitConvexApproxSequence_of_memLpOn
          (U := U) hU (by norm_num : (1 : ENNReal) ≤ 2) (by simp : (2 : ENNReal) ≠ ⊤)
          (u'.grad_memL2 i) hball hr0_pos
      refine hraw.congr' ?_
      filter_upwards [hε_eventually_lt_one] with n hε1
      apply MeasureTheory.eLpNorm_congr_ae
      have hbridge :=
        ae_eq_fderiv_convexApproxSmoothRepresentative_apply_basisVec
          (U := U) (ρ := ρ) (u := u') (gi := fun y => u'.grad y i)
          (i := i) (p := (2 : ENNReal)) hU hρ (by norm_num : (1 : ENNReal) ≤ 2)
          u'.memL2 (u'.grad_memL2 i) (u'.hasWeakPartialDerivOn i)
          hball hr0_pos (hε_pos n) hε1
      filter_upwards [hbridge, MeasureTheory.ae_restrict_mem hU.isOpen.measurableSet] with x hx hxU
      have hEq :=
        convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem
          (u := fun y => u'.grad y i) hU hρ hxU hball hr0_pos (hε_pos n) hε1
      rw [hx]
      simpa [ψ, ρ, ε, unitConvexApproxSequence] using congrArg
        (fun t : ℝ => (1 - unitConvexApproxScale n) * t - u'.grad x i) hEq.symm
    refine ⟨
      { toH1Function := uφ
        approx := fun n x => φ x * ψ n x
        approx_smooth := by
          intro n
          exact hφ.mul (hψ_smooth n)
        approx_hasCompactSupport := by
          intro n
          simpa [mul_comm] using! (hφ_compact.mul_left (f := ψ n))
        approx_support_subset := by
          intro n
          exact (tsupport_mul_subset_left (f := φ) (g := ψ n)).trans hφ_sub
        tendsto_approx := by
          let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
          have hφ_cont : Continuous φ := hφ.continuous
          have hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) μU :=
            (hφ_cont.memLp_of_hasCompactSupport hφ_compact).restrict U
          have hconst_tendsto :
              Filter.Tendsto
                (fun n =>
                  MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                    MeasureTheory.eLpNorm (fun x => ψ n x - u' x) 2 μU)
                Filter.atTop
                (nhds (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0)) :=
            ENNReal.Tendsto.const_mul hψ_tendsto
              (Or.inr hφ_memTop.eLpNorm_lt_top.ne)
          have hupper :
              ∀ n,
                MeasureTheory.eLpNorm (fun x => φ x * ψ n x - uφ.toFun x) 2 μU ≤
                  MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                    MeasureTheory.eLpNorm (fun x => ψ n x - u' x) 2 μU := by
            intro n
            have hdiff_mem :
                MeasureTheory.MemLp (fun x => ψ n x - u' x) 2 μU := by
              exact (hψ_memL2 n).sub u'.memL2
            have hEq :
                (fun x => φ x * ψ n x - uφ.toFun x) =
                  φ • (fun x => ψ n x - u' x) := by
              funext x
              change φ x * ψ n x - φ x * u' x = φ x * (ψ n x - u' x)
              ring
            rw [hEq]
            exact MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (φ := φ) 2 (by norm_num)
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le
            tendsto_const_nhds ?_ (fun n => zero_le) hupper
          simpa using hconst_tendsto
        tendsto_approx_grad := by
          intro i
          let μU : MeasureTheory.Measure (Vec d) := MeasureTheory.volume.restrict U
          let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
          have hφ_memTop : MeasureTheory.MemLp φ (⊤ : ENNReal) μU :=
            (hφ.continuous.memLp_of_hasCompactSupport hφ_compact).restrict U
          have hdφ_cont : Continuous dφ := by
            simpa [dφ] using
              (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
          have hdφ_compact : HasCompactSupport dφ := by
            simpa [dφ] using hφ_compact.fderiv_apply (𝕜 := ℝ) (basisVec i)
          have hdφ_memTop : MeasureTheory.MemLp dφ (⊤ : ENNReal) μU :=
            (hdφ_cont.memLp_of_hasCompactSupport hdφ_compact).restrict U
          have hfirst_tendsto :
              Filter.Tendsto
                (fun n =>
                  MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                    MeasureTheory.eLpNorm
                      (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - u'.grad x i) 2 μU)
                Filter.atTop
                (nhds (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0)) :=
            ENNReal.Tendsto.const_mul (hψ_grad_tendsto i)
              (Or.inr hφ_memTop.eLpNorm_lt_top.ne)
          have hsecond_tendsto :
              Filter.Tendsto
                (fun n =>
                  MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
                    MeasureTheory.eLpNorm (fun x => ψ n x - u' x) 2 μU)
                Filter.atTop
                (nhds (MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU * 0)) :=
            ENNReal.Tendsto.const_mul hψ_tendsto
              (Or.inr hdφ_memTop.eLpNorm_lt_top.ne)
          have hsum_tendsto :
              Filter.Tendsto
                (fun n =>
                  MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                      MeasureTheory.eLpNorm
                        (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - u'.grad x i) 2 μU +
                    MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
                      MeasureTheory.eLpNorm (fun x => ψ n x - u' x) 2 μU)
                Filter.atTop
                (nhds
                  (MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU * 0 +
                    MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU * 0)) :=
            hfirst_tendsto.add hsecond_tendsto
          have hupper :
              ∀ n,
                MeasureTheory.eLpNorm
                    (fun x =>
                      (fderiv ℝ (fun y => φ y * ψ n y) x) (basisVec i) - uφ.grad x i)
                    2 μU ≤
                  MeasureTheory.eLpNorm φ (⊤ : ENNReal) μU *
                      MeasureTheory.eLpNorm
                        (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - u'.grad x i) 2 μU +
                    MeasureTheory.eLpNorm dφ (⊤ : ENNReal) μU *
                      MeasureTheory.eLpNorm (fun x => ψ n x - u' x) 2 μU := by
            intro n
            let A : Vec d → ℝ := fun x => φ x *
              ((fderiv ℝ (ψ n) x) (basisVec i) - u'.grad x i)
            let B : Vec d → ℝ := fun x => dφ x * (ψ n x - u' x)
            have hbase_grad_mem :
                MeasureTheory.MemLp
                  (fun x => (fderiv ℝ (ψ n) x) (basisVec i) - u'.grad x i) 2 μU := by
              exact (hψ_grad_memL2 n i).sub (u'.gradMemL2 i)
            have hbase_mem :
                MeasureTheory.MemLp (fun x => ψ n x - u' x) 2 μU := by
              exact (hψ_memL2 n).sub u'.memL2
            have hA_mem : MeasureTheory.MemLp A 2 μU := by
              simpa [A, μU, mul_comm] using hbase_grad_mem.fun_mul (r := 2) hφ_memTop
            have hB_mem : MeasureTheory.MemLp B 2 μU := by
              simpa [B, dφ, μU, mul_comm] using hbase_mem.fun_mul (r := 2) hdφ_memTop
            have hEq :
                (fun x =>
                  (fderiv ℝ (fun y => φ y * ψ n y) x) (basisVec i) - uφ.grad x i) =
                  fun x => A x + B x := by
              funext x
              have hφ_diff : DifferentiableAt ℝ φ x :=
                (hφ.contDiffAt).differentiableAt (by simp)
              have hψ_diff : DifferentiableAt ℝ (ψ n) x :=
                ((hψ_smooth n).contDiffAt).differentiableAt (by simp)
              rw [show (fun y => φ y * ψ n y) = φ * ψ n by rfl, fderiv_mul hφ_diff hψ_diff]
              simp [A, B, dφ, uφ, H1Function.mulContDiffHasCompactSupport_grad, smul_eq_mul]
              ring
            rw [hEq]
            refine (MeasureTheory.eLpNorm_add_le (by norm_num)).trans ?_
            refine add_le_add ?_ ?_
            · simpa [A, mul_comm, mul_left_comm, mul_assoc] using!
                (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μU)
                  (φ := φ) (f := fun x => (fderiv ℝ (ψ n) x) (basisVec i) - u'.grad x i)
                  2 (by norm_num))
            · simpa [B, dφ, mul_comm, mul_left_comm, mul_assoc] using!
                (MeasureTheory.eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm_of_pos (μ := μU)
                  (φ := dφ) (f := fun x => ψ n x - u' x) 2 (by norm_num))
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le
            tendsto_const_nhds ?_ (fun n => zero_le) hupper
          simpa [zero_add] using hsum_tendsto
      }, rfl⟩


end Homogenization
