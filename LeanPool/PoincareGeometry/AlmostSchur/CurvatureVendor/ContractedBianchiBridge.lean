/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

/- Adapted from Arthur Freitas Ramos's committed contracted-bianchi formalization.
Source commit: 12cebb809524d0cd185c6cd7bcb5b73d3562bce1
Source blob: 968ea4c969894783e152ee9c28629f629296d645
Source path: contracted-bianchi/PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/ContractedBianchiBridge.lean
See PROVENANCE.json for the exact extraction and local changes. -/

public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureVendor.ContractedBianchi

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
    ContMDiff I (I.prod 𝓘(ℝ, E)) 1 (T% (cov.curvatureAuxAlmostSchur Y Z W)) := by
  have hY₁ := hY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hZ₁ := hZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hZW := cov.contMDiff_alongAlmostSchur (n := 2) hZ hW
  have hYW := cov.contMDiff_alongAlmostSchur (n := 2) hY hW
  have hYZW := cov.contMDiff_alongAlmostSchur (n := 1) hY₁ hZW
  have hZYW := cov.contMDiff_alongAlmostSchur (n := 1) hZ₁ hYW
  have hbr : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (T% (VectorField.mlieBracket I Y Z)) := by
    simpa using (ContDiff.mlieBracket_vectorField (I := I)
      (m := (1 : ℕ∞)) (n := (2 : ℕ∞)) hY hZ (by norm_num))
  have hbrW := cov.contMDiff_alongAlmostSchur (n := 1) hbr hW₂
  exact (hYZW.sub_section hZYW).sub_section hbrW

private theorem curvatureAux_mdifferentiableAt
    {Y Z W : Π x : M, TangentSpace I x} (x : M)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W)) :
    MDiffAt (T% (cov.curvatureAuxAlmostSchur Y Z W)) x :=
  ((curvatureAux_contMDiff_one cov hY hZ hW) x).mdifferentiableAt one_ne_zero

private theorem secondBianchiAux_swap_curvature_slots
    {X Y Z W : Π x : M, TangentSpace I x} (x : M)
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W)) :
    cov.secondBianchiAuxAlmostSchur X Y Z W x = -cov.secondBianchiAuxAlmostSchur X Z Y W x := by
  have hcurv := curvatureAux_mdifferentiableAt cov x hZ hY hW
  have hn : cov.alongAlmostSchur X (-cov.curvatureAuxAlmostSchur Z Y W) x =
      -cov.alongAlmostSchur X (cov.curvatureAuxAlmostSchur Z Y W) x := by
    have heq : (fun _ : M ↦ (-1 : ℝ)) • cov.curvatureAuxAlmostSchur Z Y W =
        -cov.curvatureAuxAlmostSchur Z Y W := by
      ext y
      change (-1 : ℝ) • cov.curvatureAuxAlmostSchur Z Y W y = -cov.curvatureAuxAlmostSchur Z Y W y
      exact neg_one_smul ℝ _
    have hh := cov.along_smul_right_applyAlmostSchur (x := x) (f := fun _ : M ↦ (-1 : ℝ))
      (X := X) (σ := cov.curvatureAuxAlmostSchur Z Y W) mdifferentiableAt_const hcurv
    rw [heq] at hh
    simpa [mvfderiv] using hh
  have h0 := cov.curvatureAux_swapAlmostSchur Y Z W
  have h1 := congrFun (cov.curvatureAux_swapAlmostSchur (cov.alongAlmostSchur X Y) Z W) x
  have h2 := congrFun (cov.curvatureAux_swapAlmostSchur Y (cov.alongAlmostSchur X Z) W) x
  have h3 := congrFun (cov.curvatureAux_swapAlmostSchur Y Z (cov.alongAlmostSchur X W)) x
  simp only [Pi.neg_apply] at h1 h2 h3
  simp only [secondBianchiAux_applyAlmostSchur]
  rw [h0, hn, h1, h2, h3]
  abel

/-- The first curvature-slot skew symmetry of the actual curvature derivative follows from
curvature skew symmetry and linearity of the covariant derivative on smooth sections. -/
theorem curvatureCovariantDerivativeInner_firstPairSkewAlmostSchur
    (x : M) (p a b c d : TangentSpace I x) :
    curvatureCovariantDerivativeInnerAlmostSchur cov x p a b c d =
      -curvatureCovariantDerivativeInnerAlmostSchur cov x p b a c d := by
  have h := secondBianchiAux_swap_curvature_slots cov x
    (X := smoothExtendAlmostSchur (I := I) (F := E) (V := TangentSpace I) x p)
    (smoothExtend_contMDiff_twoAlmostSchur (I := I) (F := E) (V := TangentSpace I) x a)
    (smoothExtend_contMDiff_twoAlmostSchur (I := I) (F := E) (V := TangentSpace I) x b)
    (smoothExtend_contMDiff_threeAlmostSchur (I := I) (E := E) (M := M) x c)
  simpa only [curvatureCovariantDerivativeInnerAlmostSchur, curvatureCovariantDerivativeAlmostSchur,
    inner_neg_left] using congrArg (fun z : TangentSpace I x ↦ inner ℝ z d) h

private theorem secondBianchiAux_inner_skew
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (hmetric : cov.IsMetricCompatibleTangentAlmostSchur)
    {X Y Z W V : Π x : M, TangentSpace I x} (x : M)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W))
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% V)) :
    inner ℝ (cov.secondBianchiAuxAlmostSchur X Y Z W x) (V x) +
      inner ℝ (W x) (cov.secondBianchiAuxAlmostSchur X Y Z V x) = 0 := by
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
  have hAV : MDiffAt (fun y ↦ inner ℝ (cov.curvatureAuxAlmostSchur Y Z W y) (V y)) x := by
    have hc : ContMDiff I 𝓘(ℝ) 1
        (fun y ↦ inner ℝ (cov.curvatureAuxAlmostSchur Y Z W y) (V y)) :=
      ContMDiff.inner_bundle (IM := I) (IB := I) (F := E) (E := TangentSpace I)
        (curvatureAux_contMDiff_one cov hY₂ hZ₂ hW)
        (hV.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3))
    exact (hc x).mdifferentiableAt one_ne_zero
  have hWB : MDiffAt (fun y ↦ inner ℝ (W y) (cov.curvatureAuxAlmostSchur Y Z V y)) x := by
    have hc : ContMDiff I 𝓘(ℝ) 1
        (fun y ↦ inner ℝ (W y) (cov.curvatureAuxAlmostSchur Y Z V y)) :=
      ContMDiff.inner_bundle (IM := I) (IB := I) (F := E) (E := TangentSpace I)
        (hW.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3))
        (curvatureAux_contMDiff_one cov hY₂ hZ₂ hV)
    exact (hc x).mdifferentiableAt one_ne_zero
  have hz : (fun y ↦ inner ℝ (cov.curvatureAuxAlmostSchur Y Z W y) (V y)) +
      (fun y ↦ inner ℝ (W y) (cov.curvatureAuxAlmostSchur Y Z V y)) = (0 : M → ℝ) := by
    funext y
    exact cov.curvatureAux_inner_add_eq_zero_of_metricCompatibleAlmostSchur
      hmetric hY₁ hZ₁ hW₂ hV₂
  have hd := congrArg (fun f : M → ℝ ↦ mvfderiv (I := I) f x (X x)) hz
  rw [mvfderiv_add hAV hWB] at hd
  simp only [add_apply] at hd
  rw [hmetric hA hVmd, hmetric hWmd hB] at hd
  rw [mvfderiv_zero, zero_apply] at hd
  have hd' :
      inner ℝ (cov.alongAlmostSchur X (cov.curvatureAuxAlmostSchur Y Z W) x) (V x) +
      inner ℝ (cov.curvatureAuxAlmostSchur Y Z W x) (cov.alongAlmostSchur X V x) +
      (inner ℝ (cov.alongAlmostSchur X W x) (cov.curvatureAuxAlmostSchur Y Z V x) +
      inner ℝ (W x) (cov.alongAlmostSchur X (cov.curvatureAuxAlmostSchur Y Z V) x)) = 0 := by
    simpa only [CovariantDerivative.alongAlmostSchur] using hd
  have hXY := cov.contMDiff_alongAlmostSchur (n := 2) hX hY
  have hXZ := cov.contMDiff_alongAlmostSchur (n := 2) hX hZ
  have hXW := cov.contMDiff_alongAlmostSchur (n := 2) hX hW
  have hXV := cov.contMDiff_alongAlmostSchur (n := 2) hX hV
  have hc1 := cov.curvatureAux_inner_add_eq_zero_of_metricCompatibleAlmostSchur
    (x := x) hmetric (hXY.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) hZ₁ hW₂ hV₂
  have hc2 := cov.curvatureAux_inner_add_eq_zero_of_metricCompatibleAlmostSchur
    (x := x) hmetric hY₁ (hXZ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)) hW₂ hV₂
  have hc3 := cov.curvatureAux_inner_add_eq_zero_of_metricCompatibleAlmostSchur
    (x := x) hmetric hY₁ hZ₁ hXW hV₂
  have hc4 := cov.curvatureAux_inner_add_eq_zero_of_metricCompatibleAlmostSchur
    (x := x) hmetric hY₁ hZ₁ hW₂ hXV
  simp only [secondBianchiAux_applyAlmostSchur, inner_sub_left, inner_sub_right]
  linarith

/-- Metric compatibility implies the last-pair skew symmetry of the actual curvature derivative.
The proof differentiates the curvature skew-adjointness equation and cancels all connection
correction terms, using the metric Leibniz rule. -/
theorem curvatureCovariantDerivativeInner_lastPairSkewAlmostSchur
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (hmetric : cov.IsMetricCompatibleTangentAlmostSchur)
    (x : M) (p a b c d : TangentSpace I x) :
    curvatureCovariantDerivativeInnerAlmostSchur cov x p a b c d =
      -curvatureCovariantDerivativeInnerAlmostSchur cov x p a b d c := by
  have h := secondBianchiAux_inner_skew cov hmetric x
    (smoothExtend_contMDiff_twoAlmostSchur (I := I) (F := E) (V := TangentSpace I) x p)
    (smoothExtend_contMDiff_threeAlmostSchur (I := I) (E := E) (M := M) x a)
    (smoothExtend_contMDiff_threeAlmostSchur (I := I) (E := E) (M := M) x b)
    (smoothExtend_contMDiff_threeAlmostSchur (I := I) (E := E) (M := M) x c)
    (smoothExtend_contMDiff_threeAlmostSchur (I := I) (E := E) (M := M) x d)
  simp only [smoothExtend_applyAlmostSchur] at h
  change inner ℝ (curvatureCovariantDerivativeAlmostSchur cov x p a b c) d +
    inner ℝ c (curvatureCovariantDerivativeAlmostSchur cov x p a b d) = 0 at h
  change inner ℝ _ d = -inner ℝ _ c
  have hc : inner ℝ c (curvatureCovariantDerivativeAlmostSchur cov x p a b d) =
      inner ℝ (curvatureCovariantDerivativeAlmostSchur cov x p a b d) c := real_inner_comm _ _
  linarith

private theorem secondBianchiAux_firstBianchi_inner
    (hT : cov.torsion = 0)
    {X Y Z W : Π x : M, TangentSpace I x} (x : M) (d : TangentSpace I x)
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% X))
    (hY : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% Z))
    (hW : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% W)) :
    inner ℝ (cov.secondBianchiAuxAlmostSchur X Y Z W x) d +
      inner ℝ (cov.secondBianchiAuxAlmostSchur X Z W Y x) d +
      inner ℝ (cov.secondBianchiAuxAlmostSchur X W Y Z x) d = 0 := by
  have hY₂ := hY.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hZ₂ := hZ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hW₂ := hW.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hA := curvatureAux_mdifferentiableAt cov x hY₂ hZ₂ hW
  have hB := curvatureAux_mdifferentiableAt cov x hZ₂ hW₂ hY
  have hC := curvatureAux_mdifferentiableAt cov x hW₂ hY₂ hZ
  have hz : cov.curvatureAuxAlmostSchur Y Z W + cov.curvatureAuxAlmostSchur Z W Y +
      cov.curvatureAuxAlmostSchur W Y Z = 0 := by
    funext y
    exact cov.firstBianchiAux_apply_of_torsion_eq_zeroAlmostSchur hT hY₂ hZ₂ hW₂
  have hd := congrArg (fun s ↦ cov.alongAlmostSchur X s x) hz
  rw [cov.along_add_right_applyAlmostSchur (mdifferentiableAt_add_section hA hB) hC,
    cov.along_add_right_applyAlmostSchur hA hB] at hd
  have hzero : cov.alongAlmostSchur X 0 x = 0 := by
    simp only [CovariantDerivative.alongAlmostSchur, cov.isCovariantDerivativeOn.zero,
      zero_apply]
  rw [hzero] at hd
  have hc1 := cov.firstBianchiAux_apply_of_torsion_eq_zeroAlmostSchur (x := x) hT
    (cov.contMDiff_alongAlmostSchur (n := 2) hX hY) hZ₂ hW₂
  have hc2 := cov.firstBianchiAux_apply_of_torsion_eq_zeroAlmostSchur (x := x) hT
    hY₂ (cov.contMDiff_alongAlmostSchur (n := 2) hX hZ) hW₂
  have hc3 := cov.firstBianchiAux_apply_of_torsion_eq_zeroAlmostSchur (x := x) hT
    hY₂ hZ₂ (cov.contMDiff_alongAlmostSchur (n := 2) hX hW)
  have hi0 := congrArg (fun z ↦ inner ℝ z d) hd
  have hi1 := congrArg (fun z ↦ inner ℝ z d) hc1
  have hi2 := congrArg (fun z ↦ inner ℝ z d) hc2
  have hi3 := congrArg (fun z ↦ inner ℝ z d) hc3
  simp only [inner_add_left, inner_zero_left] at hi0 hi1 hi2 hi3
  simp only [secondBianchiAux_applyAlmostSchur, inner_sub_left]
  linarith

/-- Differentiating the first Bianchi identity preserves its cyclic curvature-slot equation. -/
theorem curvatureCovariantDerivativeInner_firstBianchiAlmostSchur
    (hT : cov.torsion = 0) (x : M) (p a b c d : TangentSpace I x) :
    curvatureCovariantDerivativeInnerAlmostSchur cov x p a b c d +
      curvatureCovariantDerivativeInnerAlmostSchur cov x p b c a d +
      curvatureCovariantDerivativeInnerAlmostSchur cov x p c a b d = 0 := by
  exact secondBianchiAux_firstBianchi_inner cov hT x d
    (smoothExtend_contMDiff_twoAlmostSchur (I := I) (F := E) (V := TangentSpace I) x p)
    (smoothExtend_contMDiff_threeAlmostSchur (I := I) (E := E) (M := M) x a)
    (smoothExtend_contMDiff_threeAlmostSchur (I := I) (E := E) (M := M) x b)
    (smoothExtend_contMDiff_threeAlmostSchur (I := I) (E := E) (M := M) x c)

/-- Pair interchange follows from the two skew symmetries and the differentiated first Bianchi
identity.  In particular it is derived from the torsion-free metric-compatible connection. -/
theorem curvatureCovariantDerivativeInner_pairInterchangeAlmostSchur
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangentAlmostSchur)
    (x : M) (p a b c d : TangentSpace I x) :
    curvatureCovariantDerivativeInnerAlmostSchur cov x p a b c d =
      curvatureCovariantDerivativeInnerAlmostSchur cov x p c d a b := by
  have hf := curvatureCovariantDerivativeInner_firstPairSkewAlmostSchur cov x p
  have hl := curvatureCovariantDerivativeInner_lastPairSkewAlmostSchur cov hmetric x p
  have hb := curvatureCovariantDerivativeInner_firstBianchiAlmostSchur cov hT x p
  linarith only [hb a b c d, hb a b d c, hb a c d b, hb b c d a,
    hf c a b d, hl a b d c, hf d a b c, hl a c d b,
    hf d a c b, hl a d c b, hl b c d a, hl c d b a,
    hf d b c a, hl b d c a]

/-- Double contraction of the connection's actual curvature derivative.  The cyclic Bianchi
identity and derivative pair symmetries are derived from torsion-freeness and metric compatibility.

The finite family need not be orthonormal for this algebraic identity.  Its interpretation as
metric traces requires an orthonormal basis and a separate trace/differentiation bridge. -/
theorem curvatureCovariantDerivativeInner_doubleContractionAlmostSchur
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (x : M) (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangentAlmostSchur)
    {ι : Type*} [Fintype ι] (e : ι → TangentSpace I x) (w : TangentSpace I x) :
    (∑ i, ∑ k, curvatureCovariantDerivativeInnerAlmostSchur cov x w (e k) (e i) (e i) (e k)) =
      2 * ∑ i, ∑ k,
        curvatureCovariantDerivativeInnerAlmostSchur cov x (e i) (e k) (e i) w (e k) := by
  let D := curvatureCovariantDerivativeInnerAlmostSchur cov x
  have hfirst := curvatureCovariantDerivativeInner_firstPairSkewAlmostSchur cov x
  have hlast := curvatureCovariantDerivativeInner_lastPairSkewAlmostSchur cov hmetric x
  have hpair := curvatureCovariantDerivativeInner_pairInterchangeAlmostSchur cov hT hmetric x
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
    exact curvatureCovariantDerivativeInner_secondBianchiAlmostSchur cov x hT w (e k) (e i) (e i) (e k)
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

/-! A source-facing version of the contraction theorem.  Unlike the pointwise wrapper above,
this theorem takes the smooth vector fields used in the corrected derivative explicitly.  That
form is useful to keep a Palomar Challenge independent of candidate-local helper modules while
retaining the same connection-derived proof. -/
theorem curvatureCovariantDerivativeInner_doubleContraction_sectionsAlmostSchur
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (x : M) (hT : cov.torsion = 0) (hmetric : cov.IsMetricCompatibleTangentAlmostSchur)
    {ι : Type*} [Fintype ι]
    (e : ι → Π y : M, TangentSpace I y)
    (w : Π y : M, TangentSpace I y)
    (he : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (e i)))
    (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% w)) :
    (∑ i, ∑ k, inner ℝ
      (cov.secondBianchiAuxAlmostSchur w (e k) (e i) (e i) x) (e k x)) =
      2 * ∑ i, ∑ k, inner ℝ
        (cov.secondBianchiAuxAlmostSchur (e i) (e k) (e i) w x) (e k x) := by
  let SmoothSection := {X : Π y : M, TangentSpace I y //
    ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% X)}
  let ef : ι → SmoothSection := fun i ↦ ⟨e i, he i⟩
  let wf : SmoothSection := ⟨w, hw⟩
  let D : SmoothSection → SmoothSection → SmoothSection → SmoothSection →
      SmoothSection → ℝ := fun p a b c d ↦
    inner ℝ (cov.secondBianchiAuxAlmostSchur p.1 a.1 b.1 c.1 x) (d.1 x)
  have hfirst (p a b c d : SmoothSection) :
      D p a b c d = -D p b a c d := by
    have h := secondBianchiAux_swap_curvature_slots cov x
      (X := p.1) (Y := a.1) (Z := b.1) (W := c.1)
      (a.2.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      (b.2.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) c.2
    have h' := congrArg (fun z : TangentSpace I x ↦ inner ℝ z (d.1 x)) h
    change inner ℝ (cov.secondBianchiAuxAlmostSchur p.1 a.1 b.1 c.1 x) (d.1 x) =
      -inner ℝ (cov.secondBianchiAuxAlmostSchur p.1 b.1 a.1 c.1 x) (d.1 x)
    simpa only [inner_neg_left] using h'
  have hlast (p a b c d : SmoothSection) :
      D p a b c d = -D p a b d c := by
    have h := secondBianchiAux_inner_skew cov hmetric x
      (p.2.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      a.2 b.2 c.2 d.2
    have hc : inner ℝ (c.1 x)
        (cov.secondBianchiAuxAlmostSchur p.1 a.1 b.1 d.1 x) =
        inner ℝ (cov.secondBianchiAuxAlmostSchur p.1 a.1 b.1 d.1 x) (c.1 x) :=
      real_inner_comm _ _
    change inner ℝ (cov.secondBianchiAuxAlmostSchur p.1 a.1 b.1 c.1 x) (d.1 x) =
      -inner ℝ (cov.secondBianchiAuxAlmostSchur p.1 a.1 b.1 d.1 x) (c.1 x)
    linarith [h, hc]
  have hcyclic (p a b c d : SmoothSection) :
      D p a b c d + D p b c a d + D p c a b d = 0 := by
    have h := secondBianchiAux_firstBianchi_inner cov hT x (d.1 x)
      (p.2.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) a.2 b.2 c.2
    simpa only [D] using h
  have hpair (p a b c d : SmoothSection) :
      D p a b c d = D p c d a b := by
    have hf := hfirst p
    have hl := hlast p
    have hb := hcyclic p
    linarith only [hb a b c d, hb a b d c, hb a c d b, hb b c d a,
      hf c a b d, hl a b d c, hf d a b c, hl a c d b,
      hf d a c b, hl a d c b, hl b c d a, hl c d b a,
      hf d b c a, hl b d c a]
  have hsum :
      (∑ i, ∑ k, D wf (ef k) (ef i) (ef i) (ef k)) +
      (∑ i, ∑ k, D (ef k) (ef i) wf (ef i) (ef k)) +
      (∑ i, ∑ k, D (ef i) wf (ef k) (ef i) (ef k)) = 0 := by
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro k _
    have h := cov.secondBianchiAux_apply_of_torsion_eq_zeroAlmostSchur
      (hT := hT) (x := x)
      (X := wf.1) (Y := (ef k).1) (Z := (ef i).1) (W := (ef i).1)
      (wf.2.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      ((ef k).2.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      ((ef i).2.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
      (ef i).2
    have h' := congrArg (fun z : TangentSpace I x ↦ inner ℝ z ((ef k).1 x)) h
    simpa only [D, inner_add_left, inner_zero_left] using h'
  have hsecond :
      (∑ i, ∑ k, D (ef k) (ef i) wf (ef i) (ef k)) =
      -(∑ i, ∑ k, D (ef i) (ef k) (ef i) wf (ef k)) := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    change D (ef i) (ef k) wf (ef k) (ef i) =
      -D (ef i) (ef k) (ef i) wf (ef k)
    exact (hfirst (ef i) (ef k) wf (ef k) (ef i)).trans
      (congrArg Neg.neg (hpair (ef i) wf (ef k) (ef k) (ef i)))
  have hthird :
      (∑ i, ∑ k, D (ef i) wf (ef k) (ef i) (ef k)) =
      -(∑ i, ∑ k, D (ef i) (ef k) (ef i) wf (ef k)) := by
    simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    have h : D (ef i) (ef k) (ef i) wf (ef k) =
        -D (ef i) wf (ef k) (ef i) (ef k) :=
      (hpair (ef i) (ef k) (ef i) wf (ef k)).trans
        (hlast (ef i) wf (ef k) (ef k) (ef i))
    linarith
  have hmain :
      (∑ i, ∑ k, D wf (ef k) (ef i) (ef i) (ef k)) =
      2 * ∑ i, ∑ k, D (ef i) (ef k) (ef i) wf (ef k) := by
    linarith
  simpa [D, ef, wf] using hmain

end CovariantDerivative
