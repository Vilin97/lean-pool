/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubePoisson
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeReflection
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.Definitions

/-! # Weak Equation Helpers -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section


/-- Extend an inhomogeneous weak equation from smooth compactly supported tests
to arbitrary `H¹₀` tests on an open domain. The proof uses exactly the
approximation data bundled in `H10Function`: the gradient side is continuous by
`L² × L² → L¹`, and the forcing side is the same scalar argument. -/
theorem h10WeakEquationOn_of_contDiff_tests
    {d : ℕ} {U : Set (Vec d)} {G : Vec d → Vec d} {f : Vec d → ℝ}
    (hU : IsOpen U) (hG : MemVectorL2 U G) (hf : MemScalarL2 U f)
    (htest :
      ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ U →
          ∫ x in U, vecDot (G x) (euclideanGradient ψ x)
              ∂MeasureTheory.volume =
            ∫ x in U, f x * ψ x ∂MeasureTheory.volume) :
    ∀ φ : H10Function U,
      ∫ x in U, vecDot (G x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, f x * φ.toH1Function x ∂MeasureTheory.volume := by
  intro φ
  let μ := volumeMeasureOn U
  let D : ℕ → Vec d → Vec d :=
    fun n x i => (fderiv ℝ (φ.approx n) x) (basisVec i)
  have hD_coord : ∀ n i, MemScalarL2 U (fun x => D n x i) := by
    intro n i
    let ψ : H10Function U :=
      H10Function.ofContDiff hU (φ.approx_smooth n)
        (φ.approx_hasCompactSupport n) (φ.approx_support_subset n)
    simpa [D, ψ, H10Function.ofContDiff, H1Function.ofContDiff] using
      ψ.toH1Function.gradMemL2 i
  have hψ_mem : ∀ n, MemScalarL2 U (φ.approx n) := by
    intro n
    let ψ : H10Function U :=
      H10Function.ofContDiff hU (φ.approx_smooth n)
        (φ.approx_hasCompactSupport n) (φ.approx_support_subset n)
    simpa [ψ, H10Function.ofContDiff, H1Function.ofContDiff] using
      ψ.toH1Function.memL2
  have htest_approx :
      ∀ n,
        ∫ x in U, vecDot (G x) (D n x) ∂MeasureTheory.volume =
          ∫ x in U, f x * φ.approx n x ∂MeasureTheory.volume := by
    intro n
    simpa [D, euclideanGradient, euclideanCoordDeriv] using!
      htest (φ.approx n) (φ.approx_smooth n)
        (φ.approx_hasCompactSupport n) (φ.approx_support_subset n)
  have hcoord_tendsto :
      ∀ i : Fin d,
        Filter.Tendsto
          (fun n => ∫ x in U, G x i * D n x i ∂MeasureTheory.volume)
          Filter.atTop
          (nhds (∫ x in U, G x i * φ.toH1Function.grad x i
            ∂MeasureTheory.volume)) := by
    intro i
    let gi : Vec d → ℝ := fun x => G x i
    let diff : ℕ → Vec d → ℝ :=
      fun n x => D n x i - φ.toH1Function.grad x i
    let Fn : ℕ → Vec d → ℝ := fun n x => gi x * D n x i
    let fLim : Vec d → ℝ := fun x => gi x * φ.toH1Function.grad x i
    have hgi_mem : MemScalarL2 U gi :=
      memScalarL2_coord_of_memVectorL2 hG i
    have hdiff_mem : ∀ n, MemScalarL2 U (diff n) := by
      intro n
      exact (hD_coord n i).sub (φ.toH1Function.gradMemL2 i)
    have hFn_int :
        ∀ᶠ n in Filter.atTop, MeasureTheory.Integrable (Fn n) μ := by
      refine Filter.Eventually.of_forall ?_
      intro n
      simpa [Fn, gi, D, μ, MeasureTheory.IntegrableOn] using!
        (hgi_mem.integrable_mul (hD_coord n i))
    have hfLim_int : MeasureTheory.Integrable fLim μ := by
      simpa [fLim, gi, μ, MeasureTheory.IntegrableOn] using!
        (hgi_mem.integrable_mul (φ.toH1Function.gradMemL2 i))
    have hL1_bound :
        ∀ n,
          MeasureTheory.eLpNorm (fun x => gi x * diff n x) 1 μ ≤
            MeasureTheory.eLpNorm gi 2 μ *
              MeasureTheory.eLpNorm (diff n) 2 μ := by
      intro n
      have hgi_meas :
          MeasureTheory.AEStronglyMeasurable gi μ := hgi_mem.aestronglyMeasurable
      have hdiff_meas :
          MeasureTheory.AEStronglyMeasurable (diff n) μ :=
        (hdiff_mem n).aestronglyMeasurable
      simpa [gi, diff] using
        (MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
          (μ := μ) (p := (2 : ENNReal)) (q := (2 : ENNReal))
          (r := (1 : ENNReal)) (fun a b : ℝ => a * b) 1 (by fun_prop) hgi_meas hdiff_meas
          (Filter.Eventually.of_forall fun x => by simp))
    have hconst_ne_top : MeasureTheory.eLpNorm gi 2 μ ≠ ⊤ :=
      hgi_mem.eLpNorm_lt_top.ne
    have hL1 :
        Filter.Tendsto
          (fun n => MeasureTheory.eLpNorm (fun x => gi x * diff n x) 1 μ)
          Filter.atTop (nhds 0) := by
      have hscaled :
          Filter.Tendsto
            (fun n =>
              MeasureTheory.eLpNorm gi 2 μ *
                MeasureTheory.eLpNorm (diff n) 2 μ)
            Filter.atTop (nhds (MeasureTheory.eLpNorm gi 2 μ * 0)) := by
        exact ENNReal.Tendsto.const_mul (φ.tendsto_approx_grad i)
          (Or.inr hconst_ne_top)
      have hscaled0 :
          Filter.Tendsto
            (fun n =>
              MeasureTheory.eLpNorm gi 2 μ *
                MeasureTheory.eLpNorm (diff n) 2 μ)
            Filter.atTop (nhds 0) := by
        simpa [mul_zero] using hscaled
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hscaled0 (fun _ => zero_le) hL1_bound
    have hL1_diff :
        Filter.Tendsto
          (fun n => MeasureTheory.eLpNorm (fun x => Fn n x - fLim x) 1 μ)
          Filter.atTop (nhds 0) := by
      have hEq :
          (fun n => MeasureTheory.eLpNorm (fun x => Fn n x - fLim x) 1 μ) =
            fun n => MeasureTheory.eLpNorm (fun x => gi x * diff n x) 1 μ := by
        funext n
        congr 1
        funext x
        simp [Fn, fLim, gi, diff]
        ring
      rw [hEq]
      exact hL1
    exact MeasureTheory.tendsto_integral_of_L1'
      (μ := μ) (f := fLim) hFn_int hL1_diff
  have hleft_tendsto :
      Filter.Tendsto
        (fun n => ∫ x in U, vecDot (G x) (D n x) ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∫ x in U, vecDot (G x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume)) := by
    have hEq :
        (fun n => ∫ x in U, vecDot (G x) (D n x) ∂MeasureTheory.volume) =
          fun n => ∑ i, ∫ x in U, G x i * D n x i
            ∂MeasureTheory.volume := by
      funext n
      rw [show (fun x => vecDot (G x) (D n x)) =
            fun x => ∑ i, G x i * D n x i by
            funext x
            simp [vecDot, D]]
      rw [MeasureTheory.integral_finsetSum]
      intro i _hi
      exact ((memScalarL2_coord_of_memVectorL2 hG i).integrable_mul
        (hD_coord n i))
    have hEq_limit :
        ∫ x in U, vecDot (G x) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume =
          ∑ i, ∫ x in U, G x i * φ.toH1Function.grad x i
            ∂MeasureTheory.volume := by
      rw [show (fun x => vecDot (G x) (φ.toH1Function.grad x)) =
            fun x => ∑ i, G x i * φ.toH1Function.grad x i by
            funext x
            simp [vecDot]]
      rw [MeasureTheory.integral_finsetSum]
      intro i _hi
      exact ((memScalarL2_coord_of_memVectorL2 hG i).integrable_mul
        (φ.toH1Function.gradMemL2 i))
    rw [hEq]
    have hsum :
        Filter.Tendsto
          (fun n => ∑ i, ∫ x in U, G x i * D n x i
            ∂MeasureTheory.volume)
          Filter.atTop
          (nhds (∑ i, ∫ x in U, G x i * φ.toH1Function.grad x i
            ∂MeasureTheory.volume)) := by
      simpa using
        tendsto_finsetSum Finset.univ (fun i _ => hcoord_tendsto i)
    rw [hEq_limit]
    exact hsum
  have hright_tendsto :
      Filter.Tendsto
        (fun n => ∫ x in U, f x * φ.approx n x ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∫ x in U, f x * φ.toH1Function x
          ∂MeasureTheory.volume)) := by
    let diff : ℕ → Vec d → ℝ := fun n x => φ.approx n x - φ.toH1Function x
    let Fn : ℕ → Vec d → ℝ := fun n x => f x * φ.approx n x
    let fLim : Vec d → ℝ := fun x => f x * φ.toH1Function x
    have hdiff_mem : ∀ n, MemScalarL2 U (diff n) := by
      intro n
      exact (hψ_mem n).sub φ.toH1Function.memL2
    have hFn_int :
        ∀ᶠ n in Filter.atTop, MeasureTheory.Integrable (Fn n) μ := by
      refine Filter.Eventually.of_forall ?_
      intro n
      simpa [Fn, μ, MeasureTheory.IntegrableOn] using!
        (hf.integrable_mul (hψ_mem n))
    have hfLim_int : MeasureTheory.Integrable fLim μ := by
      simpa [fLim, μ, MeasureTheory.IntegrableOn] using!
        (hf.integrable_mul φ.toH1Function.memL2)
    have hL1_bound :
        ∀ n,
          MeasureTheory.eLpNorm (fun x => f x * diff n x) 1 μ ≤
            MeasureTheory.eLpNorm f 2 μ *
              MeasureTheory.eLpNorm (diff n) 2 μ := by
      intro n
      have hf_meas :
          MeasureTheory.AEStronglyMeasurable f μ := hf.aestronglyMeasurable
      have hdiff_meas :
          MeasureTheory.AEStronglyMeasurable (diff n) μ :=
        (hdiff_mem n).aestronglyMeasurable
      simpa [diff] using
        (MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
          (μ := μ) (p := (2 : ENNReal)) (q := (2 : ENNReal))
          (r := (1 : ENNReal)) (fun a b : ℝ => a * b) 1 (by fun_prop) hf_meas hdiff_meas
          (Filter.Eventually.of_forall fun x => by simp))
    have hconst_ne_top : MeasureTheory.eLpNorm f 2 μ ≠ ⊤ :=
      hf.eLpNorm_lt_top.ne
    have hL1 :
        Filter.Tendsto
          (fun n => MeasureTheory.eLpNorm (fun x => f x * diff n x) 1 μ)
          Filter.atTop (nhds 0) := by
      have hscaled :
          Filter.Tendsto
            (fun n =>
              MeasureTheory.eLpNorm f 2 μ *
                MeasureTheory.eLpNorm (diff n) 2 μ)
            Filter.atTop (nhds (MeasureTheory.eLpNorm f 2 μ * 0)) := by
        exact ENNReal.Tendsto.const_mul φ.tendsto_approx
          (Or.inr hconst_ne_top)
      have hscaled0 :
          Filter.Tendsto
            (fun n =>
              MeasureTheory.eLpNorm f 2 μ *
                MeasureTheory.eLpNorm (diff n) 2 μ)
            Filter.atTop (nhds 0) := by
        simpa [mul_zero] using hscaled
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hscaled0 (fun _ => zero_le) hL1_bound
    have hL1_diff :
        Filter.Tendsto
          (fun n => MeasureTheory.eLpNorm (fun x => Fn n x - fLim x) 1 μ)
          Filter.atTop (nhds 0) := by
      have hEq :
          (fun n => MeasureTheory.eLpNorm (fun x => Fn n x - fLim x) 1 μ) =
            fun n => MeasureTheory.eLpNorm (fun x => f x * diff n x) 1 μ := by
        funext n
        congr 1
        funext x
        simp [Fn, fLim, diff]
        ring
      rw [hEq]
      exact hL1
    exact MeasureTheory.tendsto_integral_of_L1'
      (μ := μ) (f := fLim) hFn_int hL1_diff
  have hright_to_left :
      Filter.Tendsto
        (fun n => ∫ x in U, f x * φ.approx n x ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∫ x in U, vecDot (G x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume)) := by
    have hEq :
        (fun n => ∫ x in U, vecDot (G x) (D n x)
          ∂MeasureTheory.volume) =
          fun n => ∫ x in U, f x * φ.approx n x ∂MeasureTheory.volume := by
      funext n
      exact htest_approx n
    simpa [hEq] using hleft_tendsto
  exact tendsto_nhds_unique hright_to_left hright_tendsto

namespace IsPotentialOn

/-- The H¹-potential predicate is insensitive to changing the vector-field
representative a.e. on the domain. -/
theorem congr_ae {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hfg : f =ᵐ[MeasureTheory.volume.restrict U] g)
    (hf : IsPotentialOn U f) :
    IsPotentialOn U g := by
  rcases hf with ⟨u, hgrad⟩
  let v : H1Function U :=
    { toFun := u.toFun
      grad := g
      memL2 := u.memL2
      gradMemL2 := by
        intro i
        have hcoord :
            (fun x => u.grad x i) =ᵐ[MeasureTheory.volume.restrict U]
              fun x => g x i := by
          filter_upwards [hfg] with x hx
          simpa [hgrad] using congrArg (fun y : Vec d => y i) hx
        exact (u.gradMemL2 i).ae_eq hcoord
      hasWeakGradient := by
        intro i ψ hψ_smooth hψ_compact hψ_sub
        have hweak := u.hasWeakGradient i ψ hψ_smooth hψ_compact hψ_sub
        have hcoord :
            (fun x => u.grad x i) =ᵐ[MeasureTheory.volume.restrict U]
              fun x => g x i := by
          filter_upwards [hfg] with x hx
          simpa [hgrad] using congrArg (fun y : Vec d => y i) hx
        have hright :
            ∫ x in U, g x i * ψ x ∂MeasureTheory.volume =
              ∫ x in U, u.grad x i * ψ x ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hcoord] with x hx
          rw [← hx]
        calc
          ∫ x in U, u.toFun x * (fderiv ℝ ψ x) (basisVec i)
              ∂MeasureTheory.volume =
            -∫ x in U, u.grad x i * ψ x ∂MeasureTheory.volume := hweak
          _ = -∫ x in U, g x i * ψ x ∂MeasureTheory.volume := by rw [hright] }
  exact ⟨v, rfl⟩

end IsPotentialOn

/-- On a reflection cell, the cell indicator of a function is locally the
function itself. -/
theorem eventuallyEq_indicator_cubeFaceReflectionCell_of_mem
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    (φ : Vec d → ℝ) {x : Vec d}
    (hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    Set.indicator (openCubeSet (cubeFaceReflectionCellCube Q choice)) φ
      =ᶠ[nhds x] φ := by
  filter_upwards
    [(isOpen_openCubeSet (cubeFaceReflectionCellCube Q choice)).mem_nhds hx]
    with y hy
  simp [Set.indicator_of_mem hy]

/-- Away from a reflection cell, the cell indicator of a test supported in the
reflection block is locally zero. If the base point lies in another cell, this
is disjointness of the open cells; if it lies outside the block, it is the
support hypothesis. -/
theorem eventuallyEq_indicator_cubeFaceReflectionCell_of_notMem
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {φ : Vec d → ℝ}
    (hφ_sub : tsupport φ ⊆ cubeFaceReflectionBlockSet Q)
    {x : Vec d}
    (hx : x ∉ openCubeSet (cubeFaceReflectionCellCube Q choice)) :
    Set.indicator (openCubeSet (cubeFaceReflectionCellCube Q choice)) φ
      =ᶠ[nhds x] 0 := by
  by_cases hxBlock : x ∈ cubeFaceReflectionBlockSet Q
  · have hxUnion :
        x ∈ ⋃ choice' : Fin d → Fin 3,
          openCubeSet (cubeFaceReflectionCellCube Q choice') := by
      simpa [cubeFaceReflectionBlockSet_eq_iUnion_cellCube Q] using hxBlock
    rw [Set.mem_iUnion] at hxUnion
    rcases hxUnion with ⟨choice', hx'⟩
    by_cases hchoice : choice' = choice
    · subst choice'
      exact (hx hx').elim
    · exact
        Filter.Eventually.mono
          ((isOpen_openCubeSet (cubeFaceReflectionCellCube Q choice')).mem_nhds hx')
          fun y hy => by
            have hy_not :
                y ∉ openCubeSet (cubeFaceReflectionCellCube Q choice) := by
              exact
                (Set.disjoint_left.mp
                  (disjoint_openCubeSet_cubeFaceReflectionCellCube_of_ne
                    Q hchoice)
                  hy)
            simp [Set.indicator_of_notMem hy_not]
  · have hx_support : x ∉ tsupport φ := fun hxt => hxBlock (hφ_sub hxt)
    exact
      ((notMem_tsupport_iff_eventuallyEq.mp hx_support).mono
        fun y hy => by simp [Set.indicator, hy])

/-- The zero extension of a smooth compactly supported reflection-block test
to one reflection cell remains smooth. -/
theorem contDiff_indicator_cubeFaceReflectionCell_of_tsupport_subset_block
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_sub : tsupport φ ⊆ cubeFaceReflectionBlockSet Q) :
    ContDiff ℝ (⊤ : ℕ∞)
      (Set.indicator (openCubeSet (cubeFaceReflectionCellCube Q choice)) φ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)
  · exact hφ.contDiffAt.congr_of_eventuallyEq
      (eventuallyEq_indicator_cubeFaceReflectionCell_of_mem Q choice φ hx)
  · simpa using
      (contDiffAt_const (c := (0 : ℝ)) :
        ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Vec d => (0 : ℝ)) x).congr_of_eventuallyEq
        (eventuallyEq_indicator_cubeFaceReflectionCell_of_notMem
          Q choice hφ_sub hx)

/-- The cell indicator of a compactly supported test is compactly supported. -/
theorem hasCompactSupport_indicator_cubeFaceReflectionCell
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {φ : Vec d → ℝ} (hφs : HasCompactSupport φ) :
    HasCompactSupport
      (Set.indicator (openCubeSet (cubeFaceReflectionCellCube Q choice)) φ) := by
  refine HasCompactSupport.of_support_subset_isCompact hφs ?_
  intro x hx
  have hxφ : φ x ≠ 0 := by
    by_contra hzero
    have hind :
        Set.indicator (openCubeSet (cubeFaceReflectionCellCube Q choice)) φ x = 0 := by
      by_cases hcell : x ∈ openCubeSet (cubeFaceReflectionCellCube Q choice)
      · simp [Set.indicator_of_mem hcell, hzero]
      · simp [Set.indicator_of_notMem hcell]
    exact hx hind
  exact subset_tsupport φ hxφ

/-- If a smooth test is supported in the reflection block, then its cell
indicator has topological support inside that cell. -/
theorem tsupport_indicator_cubeFaceReflectionCell_subset
    {d : ℕ} (Q : TriadicCube d) (choice : Fin d → Fin 3)
    {φ : Vec d → ℝ}
    (hφ_sub : tsupport φ ⊆ cubeFaceReflectionBlockSet Q) :
    tsupport (Set.indicator (openCubeSet (cubeFaceReflectionCellCube Q choice)) φ)
      ⊆ openCubeSet (cubeFaceReflectionCellCube Q choice) := by
  intro x hx_support
  by_contra hxcell
  have hzero :
      Set.indicator (openCubeSet (cubeFaceReflectionCellCube Q choice)) φ
        =ᶠ[nhds x] 0 :=
    eventuallyEq_indicator_cubeFaceReflectionCell_of_notMem
      Q choice hφ_sub hxcell
  exact (notMem_tsupport_iff_eventuallyEq.mpr hzero) hx_support
end

end Homogenization
