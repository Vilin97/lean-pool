/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Besov.Duality.ProjectedPairing.Integrability

/-! # Averages -/

namespace Homogenization

open MeasureTheory.Measure
open scoped BigOperators ENNReal
theorem cubeAverage_cubeProjectionResidual_eq_zero_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (f : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hf : MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hp : 1 ≤ p) :
    cubeAverage R (cubeProjectionResidual Q j f) = 0 := by
  have hres0 : MeasureTheory.MemLp (cubeProjectionResidual R 0 f) p (normalizedCubeMeasure R) :=
    cubeProjectionResidual_memLp_of_mem_descendantsAtDepth
      (Q := R) (R := R) (j := 0) (p := p) (u := f) (by simp) hf
  have hzero0 :
      cubeAverage R (cubeProjectionResidual R 0 f) = 0 :=
    cubeAverage_cubeProjectionResidual_depth_zero_eq_zero_of_memLp
      (Q := R) (p := p) (f := f) hres0 hp
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  calc
    ∫ x, cubeProjectionResidual Q j f x ∂ normalizedCubeMeasure R
        = ∫ x, cubeProjectionResidual R 0 f x ∂ normalizedCubeMeasure R := by
            refine MeasureTheory.integral_congr_ae ?_
            exact cubeProjectionResidual_ae_eq_cubeProjectionResidual_depth_zero_of_mem_descendantsAtDepth
              (Q := Q) (R := R) (j := j) f hR
    _ = 0 := by
          simpa [cubeAverage_eq_integral_normalizedCubeMeasure] using hzero0

theorem cubeAverage_mul_cubeProjection_cubeProjectionResidual_eq_zero_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (f g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hf : MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hp : 1 ≤ p) :
    cubeAverage R (fun x => cubeProjection Q j g x * cubeProjectionResidual Q j f x) = 0 := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  calc
    ∫ x, cubeProjection Q j g x * cubeProjectionResidual Q j f x ∂ normalizedCubeMeasure R
        = ∫ x, cubeAverage R g * cubeProjectionResidual Q j f x ∂ normalizedCubeMeasure R := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards
              [cubeProjection_ae_eq_cubeAverage_of_mem_descendantsAtDepth
                (Q := Q) (R := R) (j := j) g hR] with x hx
            simp [hx]
    _ = cubeAverage R g *
          ∫ x, cubeProjectionResidual Q j f x ∂ normalizedCubeMeasure R := by
            rw [MeasureTheory.integral_const_mul]
    _ = cubeAverage R g * 0 := by
          have hzero :
              ∫ x, cubeProjectionResidual Q j f x ∂ normalizedCubeMeasure R = 0 := by
            simpa [cubeAverage_eq_integral_normalizedCubeMeasure] using
              cubeAverage_cubeProjectionResidual_eq_zero_of_mem_descendantsAtDepth
                (Q := Q) (R := R) (j := j) (p := p) (f := f) hR hf hp
          rw [hzero]
    _ = 0 := by ring

theorem cubeAverage_cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeAverage R (cubeProjection Q j g) = cubeAverage R g := by
  have hcongr :
      cubeAverage R (cubeProjection Q j g) =
        cubeAverage R (fun _ => cubeAverage R g) := by
    apply cubeAverage_congr_on_cubeSet
    intro x hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) g hR hx]
  rw [hcongr, cubeAverage_const]

theorem integrableOn_cubeProjection_succ_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    MeasureTheory.IntegrableOn (cubeProjection Q (j + 1) g) (cubeSet R)
      MeasureTheory.volume := by
  have hproj_local :
      ∀ S ∈ descendantsAtDepth R 1,
        MeasureTheory.IntegrableOn (cubeProjection Q (j + 1) g) (cubeSet S)
          MeasureTheory.volume := by
    intro S hS
    have hSQ : S ∈ descendantsAtDepth Q (j + 1) := by
      rw [descendantsAtDepth_succ]
      exact Finset.mem_biUnion.mpr ⟨R, hR, by simpa [descendantsAtDepth_one] using hS⟩
    have hvol_ne_top : MeasureTheory.volume (cubeSet S) ≠ ∞ := by
      intro htop
      have hreal : (MeasureTheory.volume (cubeSet S)).toReal = cubeVolume S :=
        volume_cubeSet_toReal S
      rw [htop] at hreal
      simp at hreal
      exact (cubeVolume_pos S).ne' hreal.symm
    have hconst_int :
        MeasureTheory.IntegrableOn (fun _ : Vec d => cubeAverage S g) (cubeSet S)
          MeasureTheory.volume := by
      exact MeasureTheory.integrableOn_const
        (μ := MeasureTheory.volume) (s := cubeSet S) (C := cubeAverage S g) hvol_ne_top
    refine hconst_int.congr_fun ?_ (measurableSet_cubeSet S)
    intro x hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := S) (j := j + 1) g hSQ hx]
  rw [cubeSet_eq_iUnion_descendantsAtDepth R 1]
  exact (MeasureTheory.integrableOn_finset_iUnion
    (f := cubeProjection Q (j + 1) g) (μ := MeasureTheory.volume)
    (s := descendantsAtDepth R 1) (t := cubeSet)).2 hproj_local

theorem cubeAverage_cubeProjection_succ_eq_cubeAverage_of_mem_descendantsAtDepth_of_integrableOn
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hg : MeasureTheory.IntegrableOn g (cubeSet R) MeasureTheory.volume) :
    cubeAverage R (cubeProjection Q (j + 1) g) = cubeAverage R g := by
  have hproj_int :
      MeasureTheory.IntegrableOn (cubeProjection Q (j + 1) g) (cubeSet R)
        MeasureTheory.volume :=
    integrableOn_cubeProjection_succ_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (g := g) hR
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (Q := R) (j := 1) (f := cubeProjection Q (j + 1) g) hproj_int]
  have hchild :
      ∀ S ∈ descendantsAtDepth R 1,
        cubeAverage S (cubeProjection Q (j + 1) g) = cubeAverage S g := by
    intro S hS
    have hSQ : S ∈ descendantsAtDepth Q (j + 1) := by
      rw [descendantsAtDepth_succ]
      exact Finset.mem_biUnion.mpr ⟨R, hR, by simpa [descendantsAtDepth_one] using hS⟩
    exact cubeAverage_cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := S) (j := j + 1) (g := g) hSQ
  calc
    descendantsAverage R 1 (fun S => cubeAverage S (cubeProjection Q (j + 1) g))
        = descendantsAverage R 1 (fun S => cubeAverage S g) := by
            unfold descendantsAverage
            refine congrArg (fun t : ℝ => ((descendantsAtDepth R 1).card : ℝ)⁻¹ * t) ?_
            refine Finset.sum_congr rfl ?_
            intro S hS
            rw [hchild S hS]
    _ = cubeAverage R g := by
          simpa using
            (cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
              (Q := R) (j := 1) (f := g) hg).symm

theorem cubeAverage_mul_projection_projection_succ_eq_mul_projection_projection_of_mem_descendantsAtDepth_of_integrableOn
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (f g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hg : MeasureTheory.IntegrableOn g (cubeSet R) MeasureTheory.volume) :
    cubeAverage R (fun x => cubeProjection Q j f x * cubeProjection Q (j + 1) g x) =
      cubeAverage R (fun x => cubeProjection Q j f x * cubeProjection Q j g x) := by
  have hleft :
      cubeAverage R (fun x => cubeProjection Q j f x * cubeProjection Q (j + 1) g x) =
        cubeAverage R (fun x => cubeAverage R f * cubeProjection Q (j + 1) g x) := by
    apply cubeAverage_congr_on_cubeSet
    intro x hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) f hR hx]
  have hright :
      cubeAverage R (fun x => cubeProjection Q j f x * cubeProjection Q j g x) =
        cubeAverage R (fun x => cubeAverage R f * cubeProjection Q j g x) := by
    apply cubeAverage_congr_on_cubeSet
    intro x hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) f hR hx]
  have hconst_succ :
      cubeAverage R (fun x => cubeAverage R f * cubeProjection Q (j + 1) g x) =
        cubeAverage R f * cubeAverage R (cubeProjection Q (j + 1) g) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, MeasureTheory.integral_const_mul,
      ← cubeAverage_eq_integral_normalizedCubeMeasure]
  have hconst :
      cubeAverage R (fun x => cubeAverage R f * cubeProjection Q j g x) =
        cubeAverage R f * cubeAverage R (cubeProjection Q j g) := by
    rw [cubeAverage_eq_integral_normalizedCubeMeasure, MeasureTheory.integral_const_mul,
      ← cubeAverage_eq_integral_normalizedCubeMeasure]
  rw [hleft, hright]
  calc
    cubeAverage R (fun x => cubeAverage R f * cubeProjection Q (j + 1) g x)
        = cubeAverage R f * cubeAverage R (cubeProjection Q (j + 1) g) := hconst_succ
    _ = cubeAverage R f * cubeAverage R (cubeProjection Q j g) := by
          rw [cubeAverage_cubeProjection_succ_eq_cubeAverage_of_mem_descendantsAtDepth_of_integrableOn
            (Q := Q) (R := R) (j := j) (g := g) hR hg,
            cubeAverage_cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
              (Q := Q) (R := R) (j := j) (g := g) hR]
    _ = cubeAverage R (fun x => cubeAverage R f * cubeProjection Q j g x) := hconst.symm

theorem cubeAverage_mul_projection_eq_mul_projection_projection_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (f g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hf : MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hp : 1 ≤ p) :
    cubeAverage R (fun x => f x * cubeProjection Q j g x) =
      cubeAverage R (fun x => cubeProjection Q j f x * cubeProjection Q j g x) := by
  let q : ℝ≥0∞ := cubeBesovConjExponent p
  let : ENNReal.HolderConjugate p q :=
    by simpa [q, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  have hres :
      MeasureTheory.MemLp (cubeProjectionResidual Q j f) p (normalizedCubeMeasure R) :=
    cubeProjectionResidual_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := p) (u := f) hR hf
  have hprojf :
      MeasureTheory.MemLp (cubeProjection Q j f) p (normalizedCubeMeasure R) :=
    cubeProjection_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := p) (f := f) hR
  have hprojg :
      MeasureTheory.MemLp (cubeProjection Q j g) q (normalizedCubeMeasure R) :=
    cubeProjection_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := q) (f := g) hR
  have hfirst_int :
      MeasureTheory.Integrable
        (fun x => cubeProjection Q j f x * cubeProjection Q j g x)
        (normalizedCubeMeasure R) := by
    simpa [mul_comm] using! hprojg.integrable_mul hprojf
  have hsecond_int_raw :
      MeasureTheory.Integrable
        (fun x => cubeProjection Q j g x * cubeProjectionResidual Q j f x)
        (normalizedCubeMeasure R) := by
    simpa using! hprojg.integrable_mul hres
  have hsecond_int :
      MeasureTheory.Integrable
        (fun x => cubeProjectionResidual Q j f x * cubeProjection Q j g x)
        (normalizedCubeMeasure R) := by
    refine hsecond_int_raw.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [mul_comm]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  calc
    ∫ x, f x * cubeProjection Q j g x ∂ normalizedCubeMeasure R
        =
          ∫ x,
            cubeProjection Q j f x * cubeProjection Q j g x +
              cubeProjectionResidual Q j f x * cubeProjection Q j g x
            ∂ normalizedCubeMeasure R := by
              refine MeasureTheory.integral_congr_ae ?_
              refine Filter.Eventually.of_forall ?_
              intro x
              calc
                f x * cubeProjection Q j g x
                    = (cubeProjection Q j f x + cubeProjectionResidual Q j f x) *
                        cubeProjection Q j g x := by
                          simp [cubeProjectionResidual]
                _ = cubeProjection Q j f x * cubeProjection Q j g x +
                      cubeProjectionResidual Q j f x * cubeProjection Q j g x := by
                        rw [add_mul]
    _ =
          ∫ x, cubeProjection Q j f x * cubeProjection Q j g x ∂ normalizedCubeMeasure R +
            ∫ x, cubeProjectionResidual Q j f x * cubeProjection Q j g x
              ∂ normalizedCubeMeasure R := by
                rw [MeasureTheory.integral_add hfirst_int hsecond_int]
    _ =
          cubeAverage R (fun x => cubeProjection Q j f x * cubeProjection Q j g x) +
            cubeAverage R (fun x => cubeProjectionResidual Q j f x * cubeProjection Q j g x) := by
                congr 2 <;> rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
    _ = cubeAverage R (fun x => cubeProjection Q j f x * cubeProjection Q j g x) + 0 := by
          rw [show
            cubeAverage R (fun x => cubeProjectionResidual Q j f x * cubeProjection Q j g x) =
              cubeAverage R (fun x => cubeProjection Q j g x * cubeProjectionResidual Q j f x) by
                congr 1
                funext x
                rw [mul_comm],
            cubeAverage_mul_cubeProjection_cubeProjectionResidual_eq_zero_of_mem_descendantsAtDepth
              (Q := Q) (R := R) (j := j) (p := p) (f := f) (g := g) hR hf hp]
    _ = cubeAverage R (fun x => cubeProjection Q j f x * cubeProjection Q j g x) := by ring

theorem cubeAverage_mul_projection_succ_eq_add_cubeAverage_mul_projection_add_projectionResidual_of_mem_descendantsAtDepth_of_integrableOn
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ} (p : ℝ≥0∞) (f g : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hgInt : MeasureTheory.IntegrableOn g (cubeSet R) MeasureTheory.volume)
    (hf : MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hg : MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
      (cubeBesovConjExponent p) (normalizedCubeMeasure R))
    (hp : 1 ≤ p) :
    cubeAverage R (fun x => f x * cubeProjection Q (j + 1) g x) =
      cubeAverage R (fun x => f x * cubeProjection Q j g x) +
        cubeAverage R (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x) := by
  let q : ℝ≥0∞ := cubeBesovConjExponent p
  let : ENNReal.HolderConjugate p q :=
    by simpa [q, cubeBesovConjExponent] using ENNReal.HolderConjugate.conjExponent hp
  have hg' : MeasureTheory.MemLp (cubeProjection Q (j + 1) g) q (normalizedCubeMeasure R) := by
    simpa [q] using hg
  have hres :
      MeasureTheory.MemLp (cubeProjectionResidual Q j f) p (normalizedCubeMeasure R) :=
    cubeProjectionResidual_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := p) (u := f) hR hf
  have hprojf :
      MeasureTheory.MemLp (cubeProjection Q j f) p (normalizedCubeMeasure R) :=
    cubeProjection_memLp_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (p := p) (f := f) hR
  have hfirst_int :
      MeasureTheory.Integrable
        (fun x => cubeProjection Q j f x * cubeProjection Q (j + 1) g x)
        (normalizedCubeMeasure R) := by
    simpa [q, mul_comm] using! hg'.integrable_mul hprojf
  have hsecond_int_raw :
      MeasureTheory.Integrable
        (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)
        (normalizedCubeMeasure R) := by
    simpa [q] using! hg'.integrable_mul hres
  have hsecond_int :
      MeasureTheory.Integrable
        (fun x => cubeProjectionResidual Q j f x * cubeProjection Q (j + 1) g x)
        (normalizedCubeMeasure R) := by
    refine hsecond_int_raw.congr ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    simp [mul_comm]
  rw [cubeAverage_eq_integral_normalizedCubeMeasure]
  calc
    ∫ x, f x * cubeProjection Q (j + 1) g x ∂ normalizedCubeMeasure R
        =
          ∫ x,
            cubeProjection Q j f x * cubeProjection Q (j + 1) g x +
              cubeProjectionResidual Q j f x * cubeProjection Q (j + 1) g x
            ∂ normalizedCubeMeasure R := by
              refine MeasureTheory.integral_congr_ae ?_
              refine Filter.Eventually.of_forall ?_
              intro x
              calc
                f x * cubeProjection Q (j + 1) g x
                    = (cubeProjection Q j f x + cubeProjectionResidual Q j f x) *
                        cubeProjection Q (j + 1) g x := by
                          simp [cubeProjectionResidual]
                _ = cubeProjection Q j f x * cubeProjection Q (j + 1) g x +
                      cubeProjectionResidual Q j f x * cubeProjection Q (j + 1) g x := by
                        rw [add_mul]
    _ =
          ∫ x, cubeProjection Q j f x * cubeProjection Q (j + 1) g x
              ∂ normalizedCubeMeasure R +
            ∫ x, cubeProjectionResidual Q j f x * cubeProjection Q (j + 1) g x
              ∂ normalizedCubeMeasure R := by
                rw [MeasureTheory.integral_add hfirst_int hsecond_int]
    _ =
          cubeAverage R (fun x => cubeProjection Q j f x * cubeProjection Q (j + 1) g x) +
            cubeAverage R (fun x => cubeProjectionResidual Q j f x * cubeProjection Q (j + 1) g x) := by
                congr 2 <;> rw [← cubeAverage_eq_integral_normalizedCubeMeasure]
    _ =
          cubeAverage R (fun x => f x * cubeProjection Q j g x) +
            cubeAverage R (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x) := by
              rw [cubeAverage_mul_projection_projection_succ_eq_mul_projection_projection_of_mem_descendantsAtDepth_of_integrableOn
                (Q := Q) (R := R) (j := j) (f := f) (g := g) hR hgInt,
                ← cubeAverage_mul_projection_eq_mul_projection_projection_of_mem_descendantsAtDepth
                  (Q := Q) (R := R) (j := j) (p := p) (f := f) (g := g) hR hf hp,
                show
                  cubeAverage R (fun x => cubeProjectionResidual Q j f x * cubeProjection Q (j + 1) g x) =
                    cubeAverage R (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x) by
                      congr 1
                      funext x
                      rw [mul_comm]]

theorem cubeBesovPairing_projection_zero_eq_cubeAverage_mul_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (f g : Vec d → ℝ) :
    cubeBesovPairing Q f (cubeProjection Q 0 g) = cubeAverage Q f * cubeAverage Q g := by
  unfold cubeBesovPairing
  have hcongr :
      cubeAverage Q (fun x => f x * cubeProjection Q 0 g x) =
        cubeAverage Q (fun x => f x * cubeAverage Q g) := by
    apply cubeAverage_congr_on_cubeSet
    intro x hx
    rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
      (Q := Q) (R := Q) (j := 0) g (by simp) hx]
  rw [hcongr, cubeAverage_eq_integral_normalizedCubeMeasure, MeasureTheory.integral_mul_const,
    ← cubeAverage_eq_integral_normalizedCubeMeasure]

theorem cubeBesovPairing_projection_succ_eq_add_cubeBesovPairing_projection_add_projectionResidual
    {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) (f g : Vec d → ℝ) (j : ℕ)
    (hgInt : MeasureTheory.IntegrableOn g (cubeSet Q) MeasureTheory.volume)
    (hf : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hg : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure R))
    (hp : 1 ≤ p) :
    cubeBesovPairing Q f (cubeProjection Q (j + 1) g) =
      cubeBesovPairing Q f (cubeProjection Q j g) +
        cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x) := by
  let hsucc : Vec d → ℝ := fun x => f x * cubeProjection Q (j + 1) g x
  let hcur : Vec d → ℝ := fun x => f x * cubeProjection Q j g x
  let hres : Vec d → ℝ := fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x
  have hsucc_local :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn hsucc (cubeSet R) MeasureTheory.volume := by
    intro R hR
    simpa [hsucc] using
      integrableOn_mul_projection_succ_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) (p := p) (f := f) (g := g)
        hR (hf R hR) (hg R hR) hp
  have hcur_local :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn hcur (cubeSet R) MeasureTheory.volume := by
    intro R hR
    simpa [hcur] using
      integrableOn_mul_projection_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) (p := p) (f := f) (g := g)
        hR (hf R hR) hp
  have hres_local :
      ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.IntegrableOn hres (cubeSet R) MeasureTheory.volume := by
    intro R hR
    simpa [hres] using
      integrableOn_mul_projectionResidual_projection_succ_of_mem_descendantsAtDepth
        (Q := Q) (R := R) (j := j) (p := p) (f := f) (g := g)
        hR (hf R hR) (hg R hR) hp
  have hsucc_int :
      MeasureTheory.IntegrableOn hsucc (cubeSet Q) MeasureTheory.volume := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    exact (MeasureTheory.integrableOn_finset_iUnion
      (f := hsucc) (μ := MeasureTheory.volume) (s := descendantsAtDepth Q j) (t := cubeSet)).2
      hsucc_local
  have hcur_int :
      MeasureTheory.IntegrableOn hcur (cubeSet Q) MeasureTheory.volume := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    exact (MeasureTheory.integrableOn_finset_iUnion
      (f := hcur) (μ := MeasureTheory.volume) (s := descendantsAtDepth Q j) (t := cubeSet)).2
      hcur_local
  have hres_int :
      MeasureTheory.IntegrableOn hres (cubeSet Q) MeasureTheory.volume := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    exact (MeasureTheory.integrableOn_finset_iUnion
      (f := hres) (μ := MeasureTheory.volume) (s := descendantsAtDepth Q j) (t := cubeSet)).2
      hres_local
  have hlocal :
      ∀ R ∈ descendantsAtDepth Q j,
        cubeAverage R hsucc = cubeAverage R hcur + cubeAverage R hres := by
    intro R hR
    have hgIntR : MeasureTheory.IntegrableOn g (cubeSet R) MeasureTheory.volume :=
      hgInt.mono_set (cubeSet_subset_of_mem_descendantsAtDepth hR)
    simpa [hsucc, hcur, hres] using
      cubeAverage_mul_projection_succ_eq_add_cubeAverage_mul_projection_add_projectionResidual_of_mem_descendantsAtDepth_of_integrableOn
        (Q := Q) (R := R) (j := j) (p := p) (f := f) (g := g)
        hR hgIntR (hf R hR) (hg R hR) hp
  unfold cubeBesovPairing
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      (Q := Q) (j := j) (f := hsucc) hsucc_int,
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      (Q := Q) (j := j) (f := hcur) hcur_int,
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
      (Q := Q) (j := j) (f := hres) hres_int]
  calc
    descendantsAverage Q j (fun R => cubeAverage R hsucc)
        = descendantsAverage Q j (fun R => cubeAverage R hcur + cubeAverage R hres) := by
            unfold descendantsAverage
            refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
            refine Finset.sum_congr rfl ?_
            intro R hR
            exact hlocal R hR
    _ = descendantsAverage Q j (fun R => cubeAverage R hcur) +
          descendantsAverage Q j (fun R => cubeAverage R hres) := by
            let D : Finset (TriadicCube d) := descendantsAtDepth Q j
            change ((D.card : ℝ)⁻¹ * ∑ R ∈ D, (cubeAverage R hcur + cubeAverage R hres)) =
              ((D.card : ℝ)⁻¹ * ∑ R ∈ D, cubeAverage R hcur) +
                ((D.card : ℝ)⁻¹ * ∑ R ∈ D, cubeAverage R hres)
            rw [Finset.sum_add_distrib]
            ring

theorem cubeBesovPairing_projection_eq_cubeAverage_mul_cubeAverage_add_sum
    {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) (f g : Vec d → ℝ) (N : ℕ)
    (hgInt : MeasureTheory.IntegrableOn g (cubeSet Q) MeasureTheory.volume)
    (hf : ∀ j < N, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hg : ∀ j < N, ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure R))
    (hp : 1 ≤ p) :
    cubeBesovPairing Q f (cubeProjection Q N g) =
      cubeAverage Q f * cubeAverage Q g +
        Finset.sum (Finset.range N) (fun j =>
          cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)) := by
  let T : ℕ → ℝ := fun j =>
    cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)
  induction N with
  | zero =>
      simp [cubeBesovPairing_projection_zero_eq_cubeAverage_mul_cubeAverage]
  | succ N ih =>
      have hf' :
          ∀ j < N, ∀ R ∈ descendantsAtDepth Q j,
            MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R) := by
        intro j hj R hR
        exact hf j (Nat.lt_trans hj (Nat.lt_succ_self N)) R hR
      have hg' :
          ∀ j < N, ∀ R ∈ descendantsAtDepth Q j,
            MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
              (cubeBesovConjExponent p) (normalizedCubeMeasure R) := by
        intro j hj R hR
        exact hg j (Nat.lt_trans hj (Nat.lt_succ_self N)) R hR
      calc
        cubeBesovPairing Q f (cubeProjection Q (N + 1) g)
            = cubeBesovPairing Q f (cubeProjection Q N g) + T N := by
                simpa [T] using
                  cubeBesovPairing_projection_succ_eq_add_cubeBesovPairing_projection_add_projectionResidual
                    (Q := Q) (p := p) (f := f) (g := g) (j := N)
                    hgInt
                    (fun R hR => hf N (Nat.lt_succ_self N) R hR)
                    (fun R hR => hg N (Nat.lt_succ_self N) R hR)
                    hp
        _ = (cubeAverage Q f * cubeAverage Q g + Finset.sum (Finset.range N) T) + T N := by
              rw [ih hf' hg']
        _ = cubeAverage Q f * cubeAverage Q g + Finset.sum (Finset.range (N + 1)) T := by
              rw [Finset.sum_range_succ]
              ring

theorem cubeBesovDepthWeight_mul_cubeBesovCircDepthWeight_succ {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (j : ℕ) :
    cubeBesovDepthWeight Q s j * cubeBesovCircDepthWeight Q s (j + 1) = (3 : ℝ) ^ (-s) := by
  have hQ : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hpow_pos : 0 < (3 : ℝ) ^ j := by positivity
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ j := le_of_lt hpow_pos
  have hA_pos : 0 < cubeScaleFactor Q / (3 : ℝ) ^ j := div_pos hQ hpow_pos
  have hA_nonneg : 0 ≤ cubeScaleFactor Q / (3 : ℝ) ^ j := le_of_lt hA_pos
  have hdiv :
      cubeScaleFactor Q / (3 : ℝ) ^ (j + 1) =
        (cubeScaleFactor Q / (3 : ℝ) ^ j) / 3 := by
    rw [pow_succ', div_eq_mul_inv, div_eq_mul_inv]
    ring
  unfold cubeBesovDepthWeight cubeBesovCircDepthWeight
  rw [hdiv, Real.div_rpow hA_nonneg (by positivity)]
  calc
    (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-s) *
        ((cubeScaleFactor Q / (3 : ℝ) ^ j) ^ s / (3 : ℝ) ^ s)
        = ((cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-s) *
            (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ s) / (3 : ℝ) ^ s := by
              ring
    _ = (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ ((-s) + s) / (3 : ℝ) ^ s := by
          rw [← Real.rpow_add hA_pos]
    _ = 1 / (3 : ℝ) ^ s := by
          rw [show -s + s = 0 by ring, Real.rpow_zero]
    _ = (3 : ℝ) ^ (-s) := by
          rw [one_div, Real.rpow_neg (by positivity)]

theorem cubeBesovCircDepthSeminorm_depth_zero_eq_scaleWeight_neg_mul_norm_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovCircDepthSeminorm Q s p u 0 =
      cubeBesovScaleWeight (-s) Q * ‖cubeAverage Q u‖ := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hnorm_nonneg : 0 ≤ ‖cubeAverage Q u‖ := norm_nonneg _
  unfold cubeBesovCircDepthSeminorm
  rw [cubeBesovCircDepthWeight_depth_zero, cubeBesovCircDepthAverage_depth_zero]
  congr 1
  calc
    (‖cubeAverage Q u‖ ^ p.toReal) ^ (1 / p.toReal)
        = ‖cubeAverage Q u‖ ^ (p.toReal * (1 / p.toReal)) := by
            rw [← Real.rpow_mul hnorm_nonneg]
    _ = ‖cubeAverage Q u‖ ^ (1 : ℝ) := by
          field_simp [hp_pos.ne']
    _ = ‖cubeAverage Q u‖ := by
          rw [Real.rpow_one]

theorem cubeBesovCircDepthSeminorm_zero_le_cubeBesovCircPartialNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ)
    (hq0 : q ≠ 0) (hqTop : q ≠ ∞) :
    cubeBesovCircDepthSeminorm Q s p u 0 ≤ cubeBesovCircPartialNorm Q s p q N u := by
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqTop
  have hsingle :
      (cubeBesovCircDepthSeminorm Q s p u 0) ^ q.toReal ≤
        Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovCircDepthSeminorm Q s p u j) ^ q.toReal) := by
    simpa using Finset.single_le_sum
      (fun j _ => Real.rpow_nonneg (cubeBesovCircDepthSeminorm_nonneg Q s p u j) _)
      (by simp)
  calc
    cubeBesovCircDepthSeminorm Q s p u 0
        = ((cubeBesovCircDepthSeminorm Q s p u 0) ^ q.toReal) ^ (1 / q.toReal) := by
            symm
            rw [← Real.rpow_mul (cubeBesovCircDepthSeminorm_nonneg Q s p u 0)]
            field_simp [hq_pos.ne']
            rw [Real.rpow_one]
    _ ≤ (Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovCircDepthSeminorm Q s p u j) ^ q.toReal)) ^ (1 / q.toReal) := by
            exact Real.rpow_le_rpow
              (Real.rpow_nonneg (cubeBesovCircDepthSeminorm_nonneg Q s p u 0) _)
              hsingle
              (show 0 ≤ 1 / q.toReal by positivity)
    _ = cubeBesovCircPartialNorm Q s p q N u := by
          rfl

theorem shifted_cubeBesovCircPartialSeminorm_le_cubeBesovCircPartialNorm {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p q : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ)
    (_hq0 : q ≠ 0) (_hqTop : q ≠ ∞) :
    (Finset.sum (Finset.range (N + 1))
      (fun j => (cubeBesovCircDepthSeminorm Q s p u (j + 1)) ^ q.toReal)) ^ (1 / q.toReal) ≤
      cubeBesovCircPartialNorm Q s p q (N + 1) u := by
  have hshift :
      Finset.sum (Finset.range (N + 1))
        (fun j => (cubeBesovCircDepthSeminorm Q s p u (j + 1)) ^ q.toReal) ≤
        Finset.sum (Finset.range (N + 2))
          (fun j => (cubeBesovCircDepthSeminorm Q s p u j) ^ q.toReal) := by
    calc
      Finset.sum (Finset.range (N + 1))
          (fun j => (cubeBesovCircDepthSeminorm Q s p u (j + 1)) ^ q.toReal)
          ≤ (cubeBesovCircDepthSeminorm Q s p u 0) ^ q.toReal +
              Finset.sum (Finset.range (N + 1))
                (fun j => (cubeBesovCircDepthSeminorm Q s p u (j + 1)) ^ q.toReal) := by
                  exact le_add_of_nonneg_left
                    (Real.rpow_nonneg (cubeBesovCircDepthSeminorm_nonneg Q s p u 0) _)
      _ = Finset.sum (Finset.range (N + 2))
            (fun j => (cubeBesovCircDepthSeminorm Q s p u j) ^ q.toReal) := by
              symm
              simpa [add_comm, add_left_comm, add_assoc] using
                (Finset.sum_range_succ'
                  (f := fun j => (cubeBesovCircDepthSeminorm Q s p u j) ^ q.toReal)
                  (n := N + 1))
  exact (Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (cubeBesovCircDepthSeminorm_nonneg Q s p u (j + 1)) _)
    hshift
    (show 0 ≤ 1 / q.toReal by positivity)).trans_eq (by rfl)

theorem abs_cubeAverage_mul_projection_succ_projectionResidual_le_mul_cubeBesovDepthSeminorm
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (f g : Vec d → ℝ) (j : ℕ)
    (hp : 1 ≤ p) (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (hpConjTop : cubeBesovConjExponent p ≠ ∞)
    (hf : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeFluctuation R f) p (normalizedCubeMeasure R))
    (hg : ∀ R ∈ descendantsAtDepth Q j,
      MeasureTheory.MemLp (cubeProjection Q (j + 1) g)
        (cubeBesovConjExponent p) (normalizedCubeMeasure R)) :
    |cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)| ≤
      (3 : ℝ) ^ s *
        cubeBesovDepthSeminorm Q s p f j *
        cubeBesovCircDepthSeminorm Q s (cubeBesovConjExponent p) g (j + 1) := by
  let q : ℝ≥0∞ := cubeBesovConjExponent p
  have hraw :=
    abs_cubeAverage_mul_projection_succ_projectionResidual_le_mul_cubeBesovCircDepthAverage
      (Q := Q) (p := p) (f := f) (g := g) (j := j)
      hp hp0 hpTop hpConjTop hf hg
  have hweight :
      (3 : ℝ) ^ s * cubeBesovDepthWeight Q s j * cubeBesovCircDepthWeight Q s (j + 1) = 1 := by
    have hthree_pos : 0 < (3 : ℝ) := by norm_num
    calc
      (3 : ℝ) ^ s * cubeBesovDepthWeight Q s j * cubeBesovCircDepthWeight Q s (j + 1)
          = (3 : ℝ) ^ s *
              (cubeBesovDepthWeight Q s j * cubeBesovCircDepthWeight Q s (j + 1)) := by
                ring
      _ = (3 : ℝ) ^ s * (3 : ℝ) ^ (-s) := by
            rw [cubeBesovDepthWeight_mul_cubeBesovCircDepthWeight_succ]
      _ = (3 : ℝ) ^ (s + -s) := by
            rw [← Real.rpow_add hthree_pos]
      _ = 1 := by
            rw [show s + -s = 0 by ring, Real.rpow_zero]
  calc
    |cubeAverage Q (fun x => cubeProjection Q (j + 1) g x * cubeProjectionResidual Q j f x)|
        ≤ (cubeBesovCircDepthAverage Q q g (j + 1)) ^ (1 / q.toReal) *
            (cubeBesovDepthAverage Q p f j) ^ (1 / p.toReal) := hraw
    _ = ((3 : ℝ) ^ s * cubeBesovDepthWeight Q s j * cubeBesovCircDepthWeight Q s (j + 1)) *
          ((cubeBesovCircDepthAverage Q q g (j + 1)) ^ (1 / q.toReal) *
            (cubeBesovDepthAverage Q p f j) ^ (1 / p.toReal)) := by
              rw [hweight, one_mul]
    _ = (3 : ℝ) ^ s *
          cubeBesovDepthSeminorm Q s p f j *
          cubeBesovCircDepthSeminorm Q s q g (j + 1) := by
            unfold cubeBesovDepthSeminorm cubeBesovCircDepthSeminorm
            ring

end Homogenization
