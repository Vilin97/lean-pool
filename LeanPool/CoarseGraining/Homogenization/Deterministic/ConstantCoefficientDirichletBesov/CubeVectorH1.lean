/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.PositiveNorm

/-! # Cube Vector H1 -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-- Weak zero-trace formulation of `-Δw = div h` on a cube. -/
def CubeDirichletDivergenceProblem {d : ℕ}
    (Q : TriadicCube d) (w : H10Function (openCubeSet Q))
    (h : Vec d → Vec d) : Prop :=
  ∀ φ : H10Function (openCubeSet Q),
    ∫ x in openCubeSet Q,
        vecDot (w.toH1Function.grad x) (φ.toH1Function.grad x) ∂volume =
      -∫ x in openCubeSet Q,
        vecDot (h x) (φ.toH1Function.grad x) ∂volume

/-- Abstract placeholder for the cube vector K-functional Besov norm. The
formal proof will later replace this model by the actual K-functional
definition; keeping it as a parameter lets the Dirichlet proof consume only the
properties it needs. -/
abbrev CubeKBesovNormModel (d : ℕ) : Type :=
  TriadicCube d → ℝ → (Vec d → Vec d) → ℝ

/-- Coordinatewise `H¹` vector-field competitors on a cube for the
K-functional. -/
structure CubeVectorH1Function {d : ℕ} (Q : TriadicCube d) where
  coord : Fin d → H1Function (openCubeSet Q)

namespace CubeVectorH1Function

instance {d : ℕ} {Q : TriadicCube d} : Inhabited (CubeVectorH1Function Q) :=
  ⟨{ coord := fun _ => 0 }⟩

/-- The vector field represented by a coordinatewise `H¹` competitor. -/
noncomputable def toField {d : ℕ} {Q : TriadicCube d}
    (G : CubeVectorH1Function Q) : Vec d → Vec d :=
  fun x i => G.coord i x

/-- Restrict one coordinate of a parent-cube `H¹` vector competitor to an
admitted open overlap cube. -/
noncomputable def restrictCoordToOpenOverlap {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (G : CubeVectorH1Function Q) (hS : S ∈ overlapCentersAtDepth Q j)
    (i : Fin d) : H1Function (openOverlapCubeSet S) :=
  (G.coord i).restrict (isOpen_openOverlapCubeSet S)
    (openOverlapCubeSet_subset_openCubeSet_of_mem_overlapCentersAtDepth hS)

@[simp] theorem restrictCoordToOpenOverlap_apply {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ}
    (G : CubeVectorH1Function Q) (hS : S ∈ overlapCentersAtDepth Q j)
    (i : Fin d) (x : Vec d) :
    (G.restrictCoordToOpenOverlap hS i) x = G.coord i x :=
  rfl

@[simp] theorem restrictCoordToOpenOverlap_grad {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ}
    (G : CubeVectorH1Function Q) (hS : S ∈ overlapCentersAtDepth Q j)
    (i : Fin d) (x : Vec d) :
    (G.restrictCoordToOpenOverlap hS i).grad x = (G.coord i).grad x :=
  rfl

/-- Coordinatewise `H¹` competitors are `L²` vector fields for the normalized
cube measure. -/
theorem memLp_toField_normalizedCubeMeasure {d : ℕ} {Q : TriadicCube d}
    (G : CubeVectorH1Function Q) :
    MeasureTheory.MemLp G.toField (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  apply MeasureTheory.MemLp.of_eval
  intro i
  simpa [CubeVectorH1Function.toField] using
    H1Function.memL2_normalizedCubeMeasure (G.coord i)

/-- Coordinatewise `H¹` competitors are vector `L²` fields on the open cube. -/
theorem memVectorL2_toField_openCubeSet {d : ℕ} {Q : TriadicCube d}
    (G : CubeVectorH1Function Q) :
    MemVectorL2 (openCubeSet Q) G.toField := by
  simpa [MemVectorL2, volumeMeasureOn, CubeVectorH1Function.toField] using!
    (MeasureTheory.MemLp.of_eval
      (fun i : Fin d => (G.coord i).memL2))

/-- If the datum is `L²`, then its residual against an `H¹` competitor is also
`L²`. This is the integrability input needed by the residual energy estimate. -/
theorem memLp_sub_toField_normalizedCubeMeasure {d : ℕ} {Q : TriadicCube d}
    {h : Vec d → Vec d}
    (hh : MeasureTheory.MemLp h (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (G : CubeVectorH1Function Q) :
    MeasureTheory.MemLp (fun x => h x - G.toField x) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
  simpa [Pi.sub_apply] using! hh.sub G.memLp_toField_normalizedCubeMeasure

/-- Coordinate-summed `H¹` gradient size for a vector-field competitor. -/
noncomputable def gradientCoordL2NormSum {d : ℕ} {Q : TriadicCube d}
    (G : CubeVectorH1Function Q) : ℝ :=
  ∑ i : Fin d, (G.coord i).gradientCoordL2NormSum

theorem gradientCoordL2NormSum_nonneg {d : ℕ} {Q : TriadicCube d}
    (G : CubeVectorH1Function Q) :
    0 ≤ G.gradientCoordL2NormSum := by
  unfold gradientCoordL2NormSum
  exact Finset.sum_nonneg fun i _ =>
    (G.coord i).gradientCoordL2NormSum_nonneg

/-- Parent-normalized coordinate-summed `H¹` gradient size.

The local overlapping Besov oscillations use normalized `L²` norms.  Converting
the raw `L²(openCubeSet Q)` gradient size to that normalization costs the
scale factor `side(Q) / volume(Q)^{1/2}`. -/
noncomputable def relativeGradientCoordL2NormSum {d : ℕ} {Q : TriadicCube d}
    (G : CubeVectorH1Function Q) : ℝ :=
  (cubeScaleFactor Q / Real.sqrt (cubeVolume Q)) * G.gradientCoordL2NormSum

theorem relativeGradientCoordL2NormSum_nonneg {d : ℕ} {Q : TriadicCube d}
    (G : CubeVectorH1Function Q) :
    0 ≤ G.relativeGradientCoordL2NormSum := by
  unfold relativeGradientCoordL2NormSum
  have hscale_nonneg : 0 ≤ cubeScaleFactor Q := by
    exact le_of_lt <| by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  exact mul_nonneg
    (div_nonneg hscale_nonneg (Real.sqrt_nonneg _))
    G.gradientCoordL2NormSum_nonneg

theorem relativeGradientCoordL2NormSum_le_mul_of_gradientCoordL2NormSum_le
    {d : ℕ} {Q : TriadicCube d} {C : ℝ}
    {V G : CubeVectorH1Function Q}
    (hGrad : V.gradientCoordL2NormSum ≤ C * G.gradientCoordL2NormSum) :
    V.relativeGradientCoordL2NormSum ≤ C * G.relativeGradientCoordL2NormSum := by
  let α : ℝ := cubeScaleFactor Q / Real.sqrt (cubeVolume Q)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    have hscale_nonneg : 0 ≤ cubeScaleFactor Q := by
      exact le_of_lt <| by
        simpa [cubeScaleFactor] using
          (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    exact div_nonneg hscale_nonneg (Real.sqrt_nonneg _)
  calc
    V.relativeGradientCoordL2NormSum
        = α * V.gradientCoordL2NormSum := by rfl
    _ ≤ α * (C * G.gradientCoordL2NormSum) :=
        mul_le_mul_of_nonneg_left hGrad hα_nonneg
    _ = C * (α * G.gradientCoordL2NormSum) := by ring
    _ = C * G.relativeGradientCoordL2NormSum := by rfl

/-- Distributional divergence of a coordinatewise `H¹` vector competitor. -/
noncomputable def divergence {d : ℕ} {Q : TriadicCube d}
    (G : CubeVectorH1Function Q) : Vec d → ℝ :=
  fun x => ∑ i : Fin d, (G.coord i).grad x i

theorem divergence_memLp_normalizedCubeMeasure {d : ℕ} {Q : TriadicCube d}
    (G : CubeVectorH1Function Q) :
    MeasureTheory.MemLp G.divergence (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
  have hsum :=
    MeasureTheory.memLp_finsetSum
      (μ := normalizedCubeMeasure Q) (p := (2 : ℝ≥0∞))
      (s := Finset.univ)
      (f := fun i : Fin d => fun x : Vec d => (G.coord i).grad x i)
      (fun i _hi => H1Function.grad_memL2_normalizedCubeMeasure (G.coord i) i)
  simpa [CubeVectorH1Function.divergence] using! hsum

theorem divergence_memScalarL2_openCubeSet {d : ℕ} {Q : TriadicCube d}
    (G : CubeVectorH1Function Q) :
    MemScalarL2 (openCubeSet Q) G.divergence := by
  have hsum :=
    MeasureTheory.memLp_finsetSum
      (μ := volumeMeasureOn (openCubeSet Q)) (p := (2 : ℝ≥0∞))
      (s := Finset.univ)
      (f := fun i : Fin d => fun x : Vec d => (G.coord i).grad x i)
      (fun i _hi => by
        simpa [MemScalarL2, volumeMeasureOn] using (G.coord i).grad_memL2 i)
  simpa [CubeVectorH1Function.divergence, MemScalarL2, volumeMeasureOn] using! hsum

theorem norm_toScalarL2_divergence_le_gradientCoordL2NormSum {d : ℕ}
    {Q : TriadicCube d} (G : CubeVectorH1Function Q)
    (hdiv : MemScalarL2 (openCubeSet Q) G.divergence) :
    ‖toScalarL2 hdiv‖ ≤ G.gradientCoordL2NormSum := by
  let μ : MeasureTheory.Measure (Vec d) := volumeMeasureOn (openCubeSet Q)
  have hcoord_mem :
      ∀ i : Fin d,
        MeasureTheory.MemLp (fun x => (G.coord i).grad x i)
          (2 : ℝ≥0∞) μ := by
    intro i
    simpa [μ, MemScalarL2, volumeMeasureOn] using (G.coord i).grad_memL2 i
  have hsum_eLp :
      MeasureTheory.eLpNorm G.divergence (2 : ℝ≥0∞) μ ≤
        ∑ i : Fin d,
          MeasureTheory.eLpNorm (fun x => (G.coord i).grad x i)
            (2 : ℝ≥0∞) μ := by
    have hdiv_eq_sum :
        G.divergence =ᵐ[μ]
          (∑ i : Fin d, fun x : Vec d => (G.coord i).grad x i) := by
      exact Filter.Eventually.of_forall fun x => by
        simp [CubeVectorH1Function.divergence]
    calc
      MeasureTheory.eLpNorm G.divergence (2 : ℝ≥0∞) μ
          =
            MeasureTheory.eLpNorm
              (∑ i : Fin d, fun x : Vec d => (G.coord i).grad x i)
              (2 : ℝ≥0∞) μ := MeasureTheory.eLpNorm_congr_ae hdiv_eq_sum
      _ ≤ ∑ i : Fin d,
            MeasureTheory.eLpNorm (fun x => (G.coord i).grad x i)
              (2 : ℝ≥0∞) μ :=
          MeasureTheory.eLpNorm_sum_le
            (μ := μ) (p := (2 : ℝ≥0∞)) (s := Finset.univ)
            (f := fun i : Fin d => fun x : Vec d => (G.coord i).grad x i)
            (fun i _hi => (hcoord_mem i).1)
            (by norm_num : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞))
  have hsum_toReal :
      ENNReal.toReal
          (∑ i : Fin d,
            MeasureTheory.eLpNorm (fun x => (G.coord i).grad x i)
              (2 : ℝ≥0∞) μ) =
        ∑ i : Fin d, ‖(G.coord i).gradCoordToScalarL2 i‖ := by
    rw [ENNReal.toReal_sum (fun i _hi => (hcoord_mem i).2.ne)]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [H1Function.gradCoordToScalarL2, Homogenization.toScalarL2,
      MeasureTheory.Lp.norm_toLp, μ]
  calc
    ‖toScalarL2 hdiv‖
        = ENNReal.toReal (MeasureTheory.eLpNorm G.divergence (2 : ℝ≥0∞) μ) := by
          simp [Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp, μ]
    _ ≤ ENNReal.toReal
          (∑ i : Fin d,
            MeasureTheory.eLpNorm (fun x => (G.coord i).grad x i)
              (2 : ℝ≥0∞) μ) := by
          refine ENNReal.toReal_mono ?_ hsum_eLp
          exact ENNReal.sum_ne_top.2 fun i _hi => (hcoord_mem i).2.ne
    _ = ∑ i : Fin d, ‖(G.coord i).gradCoordToScalarL2 i‖ := hsum_toReal
    _ ≤ ∑ i : Fin d, (G.coord i).gradientCoordL2NormSum := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          unfold H1Function.gradientCoordL2NormSum
          exact Finset.single_le_sum
            (fun j _hj => norm_nonneg ((G.coord i).gradCoordToScalarL2 j))
            (Finset.mem_univ i)
    _ = G.gradientCoordL2NormSum := rfl

/-- Integration by parts for the distributional divergence of a coordinatewise
`H¹` vector field tested against an `H¹₀` function. -/
theorem integral_divergence_mul_zeroTrace_eq_neg_integral_vecDot
    {d : ℕ} {Q : TriadicCube d} (G : CubeVectorH1Function Q)
    (φ : H10Function (openCubeSet Q)) :
    ∫ x in openCubeSet Q,
        G.divergence x * φ.toH1Function x ∂MeasureTheory.volume =
      -∫ x in openCubeSet Q,
        vecDot (G.toField x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
  classical
  let U : Set (Vec d) := openCubeSet Q
  have hgrad_mul_int :
      ∀ i : Fin d,
        MeasureTheory.Integrable
          (fun x : Vec d => (G.coord i).grad x i * φ.toH1Function x)
          (MeasureTheory.volume.restrict U) := by
    intro i
    simpa [U, MeasureTheory.IntegrableOn] using!
      ((G.coord i).gradMemL2 i).integrable_mul φ.toH1Function.memL2
  have hfield_mul_int :
      ∀ i : Fin d,
        MeasureTheory.Integrable
          (fun x : Vec d => (G.coord i) x * φ.toH1Function.grad x i)
          (MeasureTheory.volume.restrict U) := by
    intro i
    simpa [U, MeasureTheory.IntegrableOn] using!
      (G.coord i).memL2.integrable_mul (φ.toH1Function.gradMemL2 i)
  have hleft_sum :
      ∫ x in openCubeSet Q,
          G.divergence x * φ.toH1Function x ∂MeasureTheory.volume =
        ∑ i : Fin d,
          ∫ x in openCubeSet Q,
            (G.coord i).grad x i * φ.toH1Function x
              ∂MeasureTheory.volume := by
    unfold divergence
    simp_rw [Finset.sum_mul]
    change
      ∫ x, (∑ i : Fin d, (G.coord i).grad x i * φ.toH1Function x)
          ∂MeasureTheory.volume.restrict U =
        ∑ i : Fin d,
          ∫ x, (G.coord i).grad x i * φ.toH1Function x
            ∂MeasureTheory.volume.restrict U
    simpa using
      (MeasureTheory.integral_finsetSum
        (μ := MeasureTheory.volume.restrict U) (s := Finset.univ)
        (f := fun i : Fin d =>
          fun x : Vec d => (G.coord i).grad x i * φ.toH1Function x)
        (fun i _hi => hgrad_mul_int i))
  have hright_sum :
      ∫ x in openCubeSet Q,
          vecDot (G.toField x) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume =
        ∑ i : Fin d,
          ∫ x in openCubeSet Q,
            (G.coord i) x * φ.toH1Function.grad x i
              ∂MeasureTheory.volume := by
    unfold Homogenization.vecDot toField
    change
      ∫ x, (∑ i : Fin d, (G.coord i) x * φ.toH1Function.grad x i)
          ∂MeasureTheory.volume.restrict U =
        ∑ i : Fin d,
          ∫ x, (G.coord i) x * φ.toH1Function.grad x i
            ∂MeasureTheory.volume.restrict U
    simpa using
      (MeasureTheory.integral_finsetSum
        (μ := MeasureTheory.volume.restrict U) (s := Finset.univ)
        (f := fun i : Fin d =>
          fun x : Vec d => (G.coord i) x * φ.toH1Function.grad x i)
        (fun i _hi => hfield_mul_int i))
  have hcoord :
      ∀ i : Fin d,
        ∫ x in openCubeSet Q,
            (G.coord i).grad x i * φ.toH1Function x
              ∂MeasureTheory.volume =
          -∫ x in openCubeSet Q,
            (G.coord i) x * φ.toH1Function.grad x i
              ∂MeasureTheory.volume := by
    intro i
    have h :=
      (G.coord i).integral_mul_zeroTrace_gradCoord_eq_neg_integral_gradCoord_mul
        φ i
    calc
      ∫ x in openCubeSet Q,
          (G.coord i).grad x i * φ.toH1Function x
            ∂MeasureTheory.volume
          = -(-∫ x in openCubeSet Q,
            (G.coord i).grad x i * φ.toH1Function x
              ∂MeasureTheory.volume) := by ring
      _ = -∫ x in openCubeSet Q,
            (G.coord i) x * φ.toH1Function.grad x i
              ∂MeasureTheory.volume := by
            rw [← h]
  calc
    ∫ x in openCubeSet Q,
        G.divergence x * φ.toH1Function x ∂MeasureTheory.volume
        =
          ∑ i : Fin d,
            ∫ x in openCubeSet Q,
              (G.coord i).grad x i * φ.toH1Function x
                ∂MeasureTheory.volume := hleft_sum
    _ =
          ∑ i : Fin d,
            -∫ x in openCubeSet Q,
              (G.coord i) x * φ.toH1Function.grad x i
                ∂MeasureTheory.volume := by
          exact Finset.sum_congr rfl fun i _hi => hcoord i
    _ =
          -∑ i : Fin d,
            ∫ x in openCubeSet Q,
              (G.coord i) x * φ.toH1Function.grad x i
                ∂MeasureTheory.volume := by
          rw [Finset.sum_neg_distrib]
    _ =
          -∫ x in openCubeSet Q,
            vecDot (G.toField x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume := by
          rw [hright_sum]

/-- The coordinate-gradient vector field associated to a weak Hessian witness,
packaged as a coordinatewise `H¹` competitor. -/
noncomputable def ofWeakHessianGradient {d : ℕ} {Q : TriadicCube d}
    {v : H10Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v.toH1Function) :
    CubeVectorH1Function Q where
  coord := fun i => H.gradCoordH1Function i

@[simp] theorem ofWeakHessianGradient_toField {d : ℕ} {Q : TriadicCube d}
    {v : H10Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v.toH1Function) :
    (ofWeakHessianGradient H).toField =
      fun x => v.toH1Function.grad x := by
  funext x i
  rfl

theorem gradientCoordL2NormSum_ofWeakHessianGradient {d : ℕ}
    {Q : TriadicCube d} {v : H10Function (openCubeSet Q)}
    (H : HasWeakHessianOn (openCubeSet Q) v.toH1Function) :
    (ofWeakHessianGradient H).gradientCoordL2NormSum =
      H.hessianCoordL2NormSum := by
  calc
    (ofWeakHessianGradient H).gradientCoordL2NormSum
        = ∑ i : Fin d, (H.gradCoordH1Function i).gradientCoordL2NormSum := rfl
    _ = ∑ i : Fin d, ∑ j : Fin d, ‖H.hessCoordToScalarL2 i j‖ := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          exact H.gradCoordH1Function_gradientCoordL2NormSum_eq i
    _ = H.hessianCoordL2NormSum := rfl

end CubeVectorH1Function

/-- Smooth relative partition of unity subordinate to the retained overlap
cubes at one depth.

The structure is intentionally an implementation interface: the downstream
quasi-interpolant only needs smooth weights, partition of unity, support,
derivative, and bounded-overlap facts.  The explicit normalized cutoff
construction will provide a value of this structure. -/
structure SmoothOverlapPartition {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) where
  weight : TriadicCube d → Vec d → ℝ
  contDiff_weight : ∀ S : TriadicCube d, ContDiff ℝ 1 (weight S)
  nonneg :
    ∀ {S : TriadicCube d} {x : Vec d},
      S ∈ overlapCentersAtDepth Q j → x ∈ openCubeSet Q → 0 ≤ weight S x
  zero_of_not_mem :
    ∀ {S : TriadicCube d}, S ∉ overlapCentersAtDepth Q j →
      ∀ x : Vec d, weight S x = 0
  support_subset :
    ∀ {S : TriadicCube d} {x : Vec d},
      S ∈ overlapCentersAtDepth Q j → x ∈ openCubeSet Q →
        weight S x ≠ 0 → x ∈ openOverlapCubeSet S
  sum_eq_one :
    ∀ {x : Vec d}, x ∈ openCubeSet Q →
      (overlapCentersAtDepth Q j).sum (fun S => weight S x) = 1
  coordDeriv_sum_eq_zero :
    ∀ {x : Vec d}, x ∈ openCubeSet Q → ∀ i : Fin d,
      (overlapCentersAtDepth Q j).sum
        (fun S => euclideanCoordDeriv i (weight S) x) = 0
  coordDeriv_zero_of_not_mem_overlap :
    ∀ {S : TriadicCube d} {x : Vec d} (i : Fin d),
      S ∈ overlapCentersAtDepth Q j → x ∈ openCubeSet Q →
        x ∉ overlapCubeSet S → euclideanCoordDeriv i (weight S) x = 0
  coordDerivConstant : ℝ
  coordDerivConstant_nonneg : 0 ≤ coordDerivConstant
  coordDeriv_bound :
    ∀ {S : TriadicCube d} {x : Vec d} (i : Fin d),
      S ∈ overlapCentersAtDepth Q j → x ∈ openCubeSet Q →
        |euclideanCoordDeriv i (weight S) x| ≤
          coordDerivConstant / (cubeScaleFactor Q / (3 : ℝ) ^ j)
  activeCardBound : ℕ
  active_card_bound :
    ∀ {x : Vec d}, x ∈ openCubeSet Q →
      ((overlapCentersAtDepth Q j).filter
        (fun S => weight S x ≠ 0)).card ≤ activeCardBound

noncomputable def concreteSmoothOverlapPartition {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) : SmoothOverlapPartition Q j where
  weight := overlapPartitionWeight Q j
  contDiff_weight := fun S =>
    (contDiff_overlapPartitionWeight Q S j).of_le (by norm_num)
  nonneg := fun _hS hxQ =>
    overlapPartitionWeight_nonneg_of_mem_openCubeSet hxQ
  zero_of_not_mem := fun hS x =>
    overlapPartitionWeight_zero_of_not_mem hS x
  support_subset := fun hS hxQ hne =>
    overlapPartitionWeight_support_subset hS hxQ hne
  sum_eq_one := fun hxQ =>
    overlapPartitionWeight_sum_eq_one hxQ
  coordDeriv_sum_eq_zero := fun hxQ i =>
    overlapPartitionWeight_coordDeriv_sum_eq_zero hxQ i
  coordDeriv_zero_of_not_mem_overlap := fun i hS hxQ hxS =>
    overlapPartitionWeight_coordDeriv_zero_of_not_mem_overlap i hS hxQ hxS
  coordDerivConstant := smoothOverlapPartitionDerivativeConstant d
  coordDerivConstant_nonneg := smoothOverlapPartitionDerivativeConstant_nonneg d
  coordDeriv_bound := fun i hS hxQ =>
    abs_overlapPartitionWeight_coordDeriv_le_depthScale i hS hxQ
  activeCardBound := 3 ^ d
  active_card_bound := fun {x} hxQ =>
    overlapPartitionWeight_active_card_bound hxQ


end

end Homogenization
