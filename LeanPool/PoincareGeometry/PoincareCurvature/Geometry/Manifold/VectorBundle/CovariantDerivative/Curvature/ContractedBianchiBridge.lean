/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RaisedRicci
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.DowngradeNormFree
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TensorDivergence

/-!
# Contraction of the actual connection curvature derivative

This bridge uses the corrected curvature derivative of a connection. The cyclic second Bianchi
equation follows from torsion-freeness. The proof derives both derivative skew symmetries and
pair interchange from the connection and its metric compatibility. It then performs the double
contraction. Identifying the resulting sums separately with differentials of the Ricci/scalar
fields, or with the divergence of an Einstein tensor field, is outside this file's scope.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff BigOperators

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 2) M] [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I (minSmoothness ℝ 4) M]
  [IsManifold I ((2 : ℕ∞) + 1) M] [IsManifold I ((3 : ℕ∞) + 1) M]

private theorem curvatureAux_contMDiff_one
    {Y Z W : Π x : M, TangentSpace I x}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% (cov.curvatureAux Y Z W)) := by
  have hY₁ := hY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hZ₁ := hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hZW := cov.contMDiff_along (n := 2) hZ hW
  have hYW := cov.contMDiff_along (n := 2) hY hW
  have hYZW := cov.contMDiff_along (n := 1) hY₁ hZW
  have hZYW := cov.contMDiff_along (n := 1) hZ₁ hYW
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (T% (VectorField.mlieBracket I Y Z)) := by
    simpa using (ContDiff.mlieBracket_vectorField (I := I)
      (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) hY hZ (by norm_num))
  have hbrW := cov.contMDiff_along (n := 1) hbr hW₂
  exact (hYZW.sub_section hZYW).sub_section hbrW

/-- Local `C¹` regularity of the raw curvature commutator for a `C²` tangent connection. -/
theorem curvatureAux_contMDiffOn_one
    {Y Z W : Π x : M, TangentSpace I x} {u : Set M} (hu : IsOpen u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% Y) u)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% Z) u)
    (hW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% W) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1 (T% (cov.curvatureAux Y Z W)) u := by
  have hcov₂ : ContMDiffCovariantDerivativeOn E 2 cov.toFun u :=
    TangentFrame.contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two hu
  have hcov₁ : ContMDiffCovariantDerivativeOn E 1 cov.toFun u :=
    TangentFrame.contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one hu
  have hY₁ := hY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hZ₁ := hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hZW₂ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.along Z W)) u := by
    simpa [CovariantDerivative.along] using (hcov₂.contMDiff hW).clm_bundle_apply hZ
  have hYW₂ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.along Y W)) u := by
    simpa [CovariantDerivative.along] using (hcov₂.contMDiff hW).clm_bundle_apply hY
  have hYZW₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (T% (cov.along Y (cov.along Z W))) u := by
    simpa [CovariantDerivative.along] using (hcov₁.contMDiff hZW₂).clm_bundle_apply hY₁
  have hZYW₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (T% (cov.along Z (cov.along Y W))) u := by
    simpa [CovariantDerivative.along] using (hcov₁.contMDiff hYW₂).clm_bundle_apply hZ₁
  have hbrWithin : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (T% (VectorField.mlieBracketWithin I Y Z u)) u := by
    simpa using hY.mlieBracketWithin_vectorField (I := I) (m := (1 : ℕ∞)) hZ
      hu.uniqueMDiffOn (by norm_num)
  have hbr : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (T% (VectorField.mlieBracket I Y Z)) u := by
    refine ContMDiffOn.congr hbrWithin ?_
    intro y hy
    have hYy : MDiffAt (T% Y) y :=
      (((hY y hy).contMDiffAt (hu.mem_nhds hy)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
    have hZy : MDiffAt (T% Z) y :=
      (((hZ y hy).contMDiffAt (hu.mem_nhds hy)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
    congr 1
    simpa using
      (VectorField.mlieBracketWithin_eq_mlieBracket (I := I) (s := u) (x := y)
        (hu.uniqueMDiffWithinAt hy) hYy hZy).symm
  have hbrW₁ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (T% (cov.along (VectorField.mlieBracket I Y Z) W)) u := by
    simpa [CovariantDerivative.along] using (hcov₁.contMDiff hW₂).clm_bundle_apply hbr
  have hcomb := (hYZW₁.sub_section hZYW₁).sub_section hbrW₁
  simpa only [CovariantDerivative.curvatureAux] using hcomb

private theorem curvatureAux_mdifferentiableAt
    {Y Z W : Π x : M, TangentSpace I x} (x : M)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W)) :
    MDiffAt (T% (cov.curvatureAux Y Z W)) x :=
  ((curvatureAux_contMDiff_one cov hY hZ hW) x).mdifferentiableAt one_ne_zero

private theorem secondBianchiAux_swap_curvature_slots
    {X Y Z W : Π x : M, TangentSpace I x} (x : M)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W)) :
    cov.secondBianchiAux X Y Z W x = -cov.secondBianchiAux X Z Y W x := by
  have hcurv := curvatureAux_mdifferentiableAt cov x hZ hY hW
  have hn : cov.along X (-cov.curvatureAux Z Y W) x =
      -cov.along X (cov.curvatureAux Z Y W) x := by
    have heq : (fun _ : M ↦ (-1 : ℝ)) • cov.curvatureAux Z Y W =
        -cov.curvatureAux Z Y W := by
      ext y
      change (-1 : ℝ) • cov.curvatureAux Z Y W y = -cov.curvatureAux Z Y W y
      exact neg_one_smul ℝ _
    have hh := cov.along_smul_right_apply (x := x) (f := fun _ : M ↦ (-1 : ℝ))
      (X := X) (σ := cov.curvatureAux Z Y W) mdifferentiableAt_const hcurv
    rw [heq] at hh
    simpa [mvfderiv] using hh
  have h0 := cov.curvatureAux_swap Y Z W
  have h1 := congrFun (cov.curvatureAux_swap (cov.along X Y) Z W) x
  have h2 := congrFun (cov.curvatureAux_swap Y (cov.along X Z) W) x
  have h3 := congrFun (cov.curvatureAux_swap Y Z (cov.along X W)) x
  simp only [Pi.neg_apply] at h1 h2 h3
  simp only [secondBianchiAux_apply]
  rw [h0, hn, h1, h2, h3]
  abel

/-- The first curvature-slot skew symmetry of the actual curvature derivative follows from
curvature skew symmetry and linearity of the covariant derivative on smooth sections. -/
theorem curvatureCovariantDerivativeInner_firstPairSkew
    (x : M) (p a b c d : TangentSpace I x) :
    curvatureCovariantDerivativeInner cov x p a b c d =
      -curvatureCovariantDerivativeInner cov x p b a c d := by
  have h := secondBianchiAux_swap_curvature_slots cov x
    (X := smoothExtend (I := I) (F := E) (V := TangentSpace I) x p)
    (smoothExtend_contMDiff_two (I := I) (F := E) (V := TangentSpace I) x a)
    (smoothExtend_contMDiff_two (I := I) (F := E) (V := TangentSpace I) x b)
    (smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x c)
  simpa only [curvatureCovariantDerivativeInner, curvatureCovariantDerivative,
    inner_neg_left] using congrArg (fun z : TangentSpace I x ↦ inner ℝ z d) h

private theorem secondBianchiAux_inner_skew
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (hmetric : cov.IsMetricCompatibleTangent)
    {X Y Z W V : Π x : M, TangentSpace I x} (x : M)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% V)) :
    inner ℝ (cov.secondBianchiAux X Y Z W x) (V x) +
      inner ℝ (W x) (cov.secondBianchiAux X Y Z V x) = 0 := by
  have hY₂ := hY.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hZ₂ := hZ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hV₂ := hV.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hY₁ := hY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hZ₁ := hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)
  have hWmd := (hW x).mdifferentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hVmd := (hV x).mdifferentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hA := curvatureAux_mdifferentiableAt cov x hY₂ hZ₂ hW
  have hB := curvatureAux_mdifferentiableAt cov x hY₂ hZ₂ hV
  have hAV : MDiffAt (fun y ↦ inner ℝ (cov.curvatureAux Y Z W y) (V y)) x := by
    have hc : ContMDiff I 𝓘(ℝ) 1
        (fun y ↦ inner ℝ (cov.curvatureAux Y Z W y) (V y)) :=
      ContMDiff.inner_bundle (IM := I) (IB := I) (F := E) (E := TangentSpace I)
        (curvatureAux_contMDiff_one cov hY₂ hZ₂ hW)
        (hV.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3))
    exact (hc x).mdifferentiableAt one_ne_zero
  have hWB : MDiffAt (fun y ↦ inner ℝ (W y) (cov.curvatureAux Y Z V y)) x := by
    have hc : ContMDiff I 𝓘(ℝ) 1
        (fun y ↦ inner ℝ (W y) (cov.curvatureAux Y Z V y)) :=
      ContMDiff.inner_bundle (IM := I) (IB := I) (F := E) (E := TangentSpace I)
        (hW.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3))
        (curvatureAux_contMDiff_one cov hY₂ hZ₂ hV)
    exact (hc x).mdifferentiableAt one_ne_zero
  have hz : (fun y ↦ inner ℝ (cov.curvatureAux Y Z W y) (V y)) +
      (fun y ↦ inner ℝ (W y) (cov.curvatureAux Y Z V y)) = (0 : M → ℝ) := by
    funext y
    exact cov.curvatureAux_inner_add_eq_zero_of_metricCompatible
      hmetric hY₁ hZ₁ hW₂ hV₂
  have hd := congrArg (fun f : M → ℝ ↦ mvfderiv (I := I) f x (X x)) hz
  rw [mvfderiv_add hAV hWB] at hd
  simp only [add_apply] at hd
  rw [hmetric hA hVmd, hmetric hWmd hB] at hd
  rw [mvfderiv_zero, zero_apply] at hd
  have hd' :
      inner ℝ (cov.along X (cov.curvatureAux Y Z W) x) (V x) +
      inner ℝ (cov.curvatureAux Y Z W x) (cov.along X V x) +
      (inner ℝ (cov.along X W x) (cov.curvatureAux Y Z V x) +
      inner ℝ (W x) (cov.along X (cov.curvatureAux Y Z V) x)) = 0 := by
    simpa only [CovariantDerivative.along] using hd
  have hXY := cov.contMDiff_along (n := 2) hX hY
  have hXZ := cov.contMDiff_along (n := 2) hX hZ
  have hXW := cov.contMDiff_along (n := 2) hX hW
  have hXV := cov.contMDiff_along (n := 2) hX hV
  have hc1 := cov.curvatureAux_inner_add_eq_zero_of_metricCompatible
    (x := x) hmetric (hXY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) hZ₁ hW₂ hV₂
  have hc2 := cov.curvatureAux_inner_add_eq_zero_of_metricCompatible
    (x := x) hmetric hY₁ (hXZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) hW₂ hV₂
  have hc3 := cov.curvatureAux_inner_add_eq_zero_of_metricCompatible
    (x := x) hmetric hY₁ hZ₁ hXW hV₂
  have hc4 := cov.curvatureAux_inner_add_eq_zero_of_metricCompatible
    (x := x) hmetric hY₁ hZ₁ hW₂ hXV
  simp only [secondBianchiAux_apply, inner_sub_left, inner_sub_right]
  linarith

/-- Metric compatibility implies the last-pair skew symmetry of the actual curvature derivative.
The proof differentiates the curvature skew-adjointness equation and cancels all connection
correction terms, using the metric Leibniz rule. -/
theorem curvatureCovariantDerivativeInner_lastPairSkew
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (p a b c d : TangentSpace I x) :
    curvatureCovariantDerivativeInner cov x p a b c d =
      -curvatureCovariantDerivativeInner cov x p a b d c := by
  have h := secondBianchiAux_inner_skew cov hmetric x
    (smoothExtend_contMDiff_two (I := I) (F := E) (V := TangentSpace I) x p)
    (smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x a)
    (smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x b)
    (smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x c)
    (smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x d)
  simp only [smoothExtend_apply] at h
  change inner ℝ (curvatureCovariantDerivative cov x p a b c) d +
    inner ℝ c (curvatureCovariantDerivative cov x p a b d) = 0 at h
  change inner ℝ _ d = -inner ℝ _ c
  have hc : inner ℝ c (curvatureCovariantDerivative cov x p a b d) =
      inner ℝ (curvatureCovariantDerivative cov x p a b d) c := real_inner_comm _ _
  linarith

private theorem secondBianchiAux_firstBianchi_inner
    (hT : cov.torsion = 0)
    {X Y Z W : Π x : M, TangentSpace I x} (x : M) (d : TangentSpace I x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W)) :
    inner ℝ (cov.secondBianchiAux X Y Z W x) d +
      inner ℝ (cov.secondBianchiAux X Z W Y x) d +
      inner ℝ (cov.secondBianchiAux X W Y Z x) d = 0 := by
  have hY₂ := hY.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hZ₂ := hZ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hA := curvatureAux_mdifferentiableAt cov x hY₂ hZ₂ hW
  have hB := curvatureAux_mdifferentiableAt cov x hZ₂ hW₂ hY
  have hC := curvatureAux_mdifferentiableAt cov x hW₂ hY₂ hZ
  have hz : cov.curvatureAux Y Z W + cov.curvatureAux Z W Y +
      cov.curvatureAux W Y Z = 0 := by
    funext y
    exact cov.firstBianchiAux_apply_of_torsion_eq_zero hT hY₂ hZ₂ hW₂
  have hd := congrArg (fun s ↦ cov.along X s x) hz
  rw [cov.along_add_right_apply (mdifferentiableAt_add_section hA hB) hC,
    cov.along_add_right_apply hA hB] at hd
  have hzero : cov.along X 0 x = 0 := by
    simp only [CovariantDerivative.along, cov.isCovariantDerivativeOn.zero,
      zero_apply]
  rw [hzero] at hd
  have hc1 := cov.firstBianchiAux_apply_of_torsion_eq_zero (x := x) hT
    (cov.contMDiff_along (n := 2) hX hY) hZ₂ hW₂
  have hc2 := cov.firstBianchiAux_apply_of_torsion_eq_zero (x := x) hT
    hY₂ (cov.contMDiff_along (n := 2) hX hZ) hW₂
  have hc3 := cov.firstBianchiAux_apply_of_torsion_eq_zero (x := x) hT
    hY₂ hZ₂ (cov.contMDiff_along (n := 2) hX hW)
  have hi0 := congrArg (fun z ↦ inner ℝ z d) hd
  have hi1 := congrArg (fun z ↦ inner ℝ z d) hc1
  have hi2 := congrArg (fun z ↦ inner ℝ z d) hc2
  have hi3 := congrArg (fun z ↦ inner ℝ z d) hc3
  simp only [inner_add_left, inner_zero_left] at hi0 hi1 hi2 hi3
  simp only [secondBianchiAux_apply, inner_sub_left]
  linarith

/-- Differentiating the first Bianchi identity preserves its cyclic curvature-slot equation. -/
theorem curvatureCovariantDerivativeInner_firstBianchi
    (hT : cov.torsion = 0) (x : M) (p a b c d : TangentSpace I x) :
    curvatureCovariantDerivativeInner cov x p a b c d +
      curvatureCovariantDerivativeInner cov x p b c a d +
      curvatureCovariantDerivativeInner cov x p c a b d = 0 := by
  exact secondBianchiAux_firstBianchi_inner cov hT x d
    (smoothExtend_contMDiff_two (I := I) (F := E) (V := TangentSpace I) x p)
    (smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x a)
    (smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x b)
    (smoothExtend_contMDiff_three (I := I) (E := E) (M := M) x c)

/-- Pair interchange follows from the two skew symmetries and the differentiated first Bianchi
identity.  In particular it is derived from the torsion-free metric-compatible connection. -/
theorem curvatureCovariantDerivativeInner_pairInterchange
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (x : M) (p a b c d : TangentSpace I x) :
    curvatureCovariantDerivativeInner cov x p a b c d =
      curvatureCovariantDerivativeInner cov x p c d a b := by
  have hf := curvatureCovariantDerivativeInner_firstPairSkew cov x p
  have hl := curvatureCovariantDerivativeInner_lastPairSkew cov hmetric x p
  have hb := curvatureCovariantDerivativeInner_firstBianchi cov hT x p
  linarith only [hb a b c d, hb a b d c, hb a c d b, hb b c d a,
    hf c a b d, hl a b d c, hf d a b c, hl a c d b,
    hf d a c b, hl a d c b, hl b c d a, hl c d b a,
    hf d b c a, hl b d c a]

/-- Double contraction of the connection's actual curvature derivative.  The cyclic Bianchi
identity and derivative pair symmetries are derived from torsion-freeness and metric compatibility.

The finite family need not be orthonormal for this algebraic identity.  Its interpretation as
metric traces requires an orthonormal basis and a separate trace/differentiation bridge. -/
theorem curvatureCovariantDerivativeInner_doubleContraction
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (x : M) (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    {ι : Type*} [Fintype ι] (e : ι → TangentSpace I x) (w : TangentSpace I x) :
    (∑ i, ∑ k, curvatureCovariantDerivativeInner cov x w (e k) (e i) (e i) (e k)) =
      2 * ∑ i, ∑ k,
        curvatureCovariantDerivativeInner cov x (e i) (e k) (e i) w (e k) := by
  let D := curvatureCovariantDerivativeInner cov x
  have hfirst := curvatureCovariantDerivativeInner_firstPairSkew cov x
  have hlast := curvatureCovariantDerivativeInner_lastPairSkew cov hmetric x
  have hpair := curvatureCovariantDerivativeInner_pairInterchange cov hT hmetric x
  change (∑ i, ∑ k, D w (e k) (e i) (e i) (e k)) =
    2 * ∑ i, ∑ k, D (e i) (e k) (e i) w (e k)
  have hsum :
      (∑ i, ∑ k, D w (e k) (e i) (e i) (e k)) +
      (∑ i, ∑ k, D (e k) (e i) w (e i) (e k)) +
      (∑ i, ∑ k, D (e i) w (e k) (e i) (e k)) = 0 := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro k _
    exact curvatureCovariantDerivativeInner_secondBianchi cov x hT w (e k) (e i) (e i) (e k)
  have hsecond : (∑ i, ∑ k, D (e k) (e i) w (e i) (e k)) =
      -(∑ i, ∑ k, D (e i) (e k) (e i) w (e k)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    change D (e i) (e k) w (e k) (e i) = -D (e i) (e k) (e i) w (e k)
    exact (hfirst (e i) (e k) w (e k) (e i)).trans
      (congrArg Neg.neg (hpair (e i) w (e k) (e k) (e i)))
  have hthird : (∑ i, ∑ k, D (e i) w (e k) (e i) (e k)) =
      -(∑ i, ∑ k, D (e i) (e k) (e i) w (e k)) := by
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    have h : D (e i) (e k) (e i) w (e k) = -D (e i) w (e k) (e i) (e k) :=
      (hpair (e i) (e k) (e i) w (e k)).trans (hlast (e i) w (e k) (e k) (e i))
    linarith
  linarith

/-! ### Canonical metric traces -/

/-- The full metric trace of the covariant derivative of curvature in its
four curvature slots, leaving the derivative direction free.  This is the
contraction which becomes `dR` once differentiation is proved to commute with
the metric trace. -/
noncomputable def curvatureCovariantDerivativeScalarTrace
    (x : M) (w : TangentSpace I x) : ℝ := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  exact ∑ i, ∑ k,
    curvatureCovariantDerivativeInner cov x w (b k) (b i) (b i) (b k)

/-- The metric trace of the covariant derivative of curvature which becomes
the divergence of Ricci after the Ricci trace/differentiation bridge. -/
noncomputable def curvatureCovariantDerivativeRicciDivergenceTrace
    (x : M) (w : TangentSpace I x) : ℝ := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  exact ∑ i, ∑ k,
    curvatureCovariantDerivativeInner cov x (b i) (b k) (b i) w (b k)

/-- The canonical metric contractions of the actual differentiated curvature
tensor satisfy the numerical core of the contracted second Bianchi identity.
No coordinate components or assumed differential identity occur here. -/
theorem curvatureCovariantDerivativeScalarTrace_eq_two_mul_ricciDivergenceTrace
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (x : M) (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (w : TangentSpace I x) :
    curvatureCovariantDerivativeScalarTrace cov x w =
      2 * curvatureCovariantDerivativeRicciDivergenceTrace cov x w := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  exact curvatureCovariantDerivativeInner_doubleContraction cov x hT hmetric
    (stdOrthonormalBasis ℝ (TangentSpace I x)) w

/-- The scalar trace/differentiation bridge follows from the general theorem
that trace commutes with the induced endomorphism connection, once the
covariant derivative of raised Ricci is identified with the corresponding
double contraction of the differentiated curvature tensor. -/
theorem scalarDifferential_scalarCurvature_eq_curvatureTrace_of_raisedRicciTrace
    [IsManifold I 1 M]
    (x : M) (hRicci : raisedRicciEndomorphismMDiffAt cov x)
    (hRaisedTrace : ∀ w : TangentSpace I x,
      raisedRicciTraceCovariantDerivative cov x w =
        curvatureCovariantDerivativeScalarTrace cov x w)
    (w : TangentSpace I x) :
    scalarDifferential (I := I) (scalarCurvature (cov := cov)) x w =
      curvatureCovariantDerivativeScalarTrace cov x w := by
  rw [scalarDifferential_scalarCurvature_eq_raisedRicciTrace cov x hRicci w]
  exact hRaisedTrace w

/-- Once differentiation is identified with the two canonical curvature
traces, the numerical double contraction above is exactly the contracted
second Bianchi identity `div Ric = (1/2) dR`.  The remaining hypotheses name
only those two trace/differentiation commutation bridges. -/
theorem ricciDivergence_eq_half_scalarDifferential_of_trace_bridges
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (x : M) (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (hScalarTrace : ∀ w : TangentSpace I x,
      scalarDifferential (I := I) (scalarCurvature (cov := cov)) x w =
        curvatureCovariantDerivativeScalarTrace cov x w)
    (hRicciTrace : ∀ w : TangentSpace I x,
      ricciDivergence cov x w =
        curvatureCovariantDerivativeRicciDivergenceTrace cov x w) :
    ricciDivergence cov x =
      (1 / 2 : ℝ) • scalarDifferential (I := I)
        (scalarCurvature (cov := cov)) x := by
  ext w
  have hcore :=
    curvatureCovariantDerivativeScalarTrace_eq_two_mul_ricciDivergenceTrace
      cov x hT hmetric w
  rw [← hScalarTrace w, ← hRicciTrace w] at hcore
  simp only [smul_apply]
  change ricciDivergence cov x w =
    (1 / 2 : ℝ) * scalarDifferential (I := I)
      (scalarCurvature (cov := cov)) x w
  linarith

/-- Contracted Bianchi with the scalar differential no longer postulated as
a primitive trace bridge.  Its scalar side is discharged by the proved
trace/connection theorem; the two remaining hypotheses are the explicit
curvature-to-Ricci covariant-derivative contractions. -/
theorem ricciDivergence_eq_half_scalarDifferential_of_curvature_contractions
    [IsManifold I 1 M]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (x : M) (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangent)
    (hRicci : raisedRicciEndomorphismMDiffAt cov x)
    (hRaisedTrace : ∀ w : TangentSpace I x,
      raisedRicciTraceCovariantDerivative cov x w =
        curvatureCovariantDerivativeScalarTrace cov x w)
    (hRicciTrace : ∀ w : TangentSpace I x,
      ricciDivergence cov x w =
        curvatureCovariantDerivativeRicciDivergenceTrace cov x w) :
    ricciDivergence cov x =
      (1 / 2 : ℝ) • scalarDifferential (I := I)
        (scalarCurvature (cov := cov)) x := by
  exact ricciDivergence_eq_half_scalarDifferential_of_trace_bridges cov x hT hmetric
    (scalarDifferential_scalarCurvature_eq_curvatureTrace_of_raisedRicciTrace
      cov x hRicci hRaisedTrace) hRicciTrace

end CovariantDerivative
