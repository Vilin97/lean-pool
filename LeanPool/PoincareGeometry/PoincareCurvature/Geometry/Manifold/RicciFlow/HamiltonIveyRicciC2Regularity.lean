/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckCorrectionRegularity

/-!
# C² regularity of intrinsic Ricci from the actual connection

This file raises the local-frame regularity argument for the intrinsic Ricci tensor by one
derivative.  It derives regularity from the connection commutator and the genuine curvature tensor;
no Ricci regularity or curvature-derivative identity is assumed.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₂" => (fun x : M => TM x →L[ℝ] TM x →L[ℝ] ℝ)

/-- A globally `C³` connection on a tangent bundle restricts to a `C³` connection on each open
set.  The proof localizes a `C⁴` section with a smooth bump, applies the global regularity class,
and transfers the result back where the bump is one. -/
theorem contMDiffCovariantDerivativeOn_three_of_contMDiffCovariantDerivative_three
    [ContMDiffVectorBundle 4 E TM I]
    {cov : CovariantDerivative I E TM} [cov.ContMDiffCovariantDerivative 3]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E 3 cov.toFun u := by
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  have hux : u ∈ nhds x := hu.mem_nhds hx
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hux).mem_iff.mp hux
  have hψ : ContMDiff I 𝓘(ℝ) 4 ψ :=
    ψ.contMDiff.of_le (show (4 : WithTop ℕ∞) ≤ ∞ by decide)
  let τ : Π y : M, TM y := fun y ↦ ψ y • σ y
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 4 (T% τ) := by
    simpa [τ] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := TM) (u := u) (n := (4 : WithTop ℕ∞)) (ψ := ψ)
        hψ.contMDiffOn hu hψtsupp hσ)
  have hcovτ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 3
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := fun z : M ↦ TM z →L[ℝ] TM z)
        y (cov τ y)) := by
    have hτOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 4 (T% τ) Set.univ := by
      simpa [contMDiffOn_univ] using hτ
    simpa [contMDiffOn_univ] using
      ((inferInstance : ContMDiffCovariantDerivative cov 3).contMDiff.contMDiff hτOn)
  have hψeq1 : {y : M | ψ y = 1} ∈ nhds x := by
    filter_upwards [ψ.eventuallyEq_one] with y hy
    simpa using hy
  rcases mem_nhds_iff.mp hψeq1 with ⟨w, hwsub, hwopen, hxw⟩
  have hwu : w ⊆ u := by
    intro y hy
    have hy1 : ψ y = 1 := hwsub hy
    have hysupp : y ∈ Function.support ψ := by
      simpa [Function.support] using show ψ y ≠ 0 by rw [hy1]; norm_num
    exact hψsupp hysupp
  have hEq : ∀ y ∈ w, cov σ y = cov τ y := by
    intro y hy
    have hyu : y ∈ u := hwu hy
    have hσy : MDiffAt (T% σ) y :=
      (((hσ y hyu).contMDiffAt (hu.mem_nhds hyu)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 4)).mdifferentiableAt one_ne_zero
    have hτy : MDiffAt (T% τ) y :=
      (hτ.contMDiffAt.of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 4)).mdifferentiableAt one_ne_zero
    exact (cov.isCovariantDerivativeOn (s := w)).congr_of_eqOn hσy hτy
      (hwopen.mem_nhds hy) (fun z hz ↦ by
        have hz1 : ψ z = 1 := hwsub hz
        calc
          σ z = 1 • σ z := by simpa using (one_smul ℝ (σ z)).symm
          _ = ψ z • σ z := by simpa [hz1])
  have hcovσw : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 3
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := fun z : M ↦ TM z →L[ℝ] TM z)
        y (cov σ y)) w := by
    refine ContMDiffOn.congr hcovτ.contMDiffOn ?_
    intro y hy
    exact congrArg (fun A ↦ TotalSpace.mk' (E := fun z : M ↦ TM z →L[ℝ] TM z)
      (E →L[ℝ] E) y A) (hEq y hy)
  refine ⟨w, hwopen, hxw, ?_⟩
  simpa [Set.inter_eq_right.mpr hwu] using hcovσw

/-- The raw curvature commutator of a `C³` tangent connection is `C²` on an open set when
evaluated on `C³`, `C³`, and `C⁴` vector fields. -/
theorem curvatureAux_contMDiffOn_two
    [ContMDiffVectorBundle 4 E TM I]
    [RiemannianBundle TM]
    {cov : CovariantDerivative I E TM}
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    [cov.ContMDiffCovariantDerivative 3]
    {Y Z W : Π x : M, TM x} {u : Set M} (hu : IsOpen u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% Y) u)
    (hZ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% Z) u)
    (hW : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 4 (T% W) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.curvatureAux Y Z W)) u := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I ((2 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by exact_mod_cast le_top)
  haveI : IsManifold I ((3 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by exact_mod_cast le_top)
  have hcov₃ : ContMDiffCovariantDerivativeOn E 3 cov.toFun u :=
    contMDiffCovariantDerivativeOn_three_of_contMDiffCovariantDerivative_three hu
  have hcov₂ : ContMDiffCovariantDerivativeOn E 2 cov.toFun u :=
    TangentFrame.contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two hu
  have hY₂ := hY.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hZ₂ := hZ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hW₃ := hW.of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4)
  have hZW₃ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% (cov.along Z W)) u := by
    simpa [CovariantDerivative.along] using (hcov₃.contMDiff hW).clm_bundle_apply hZ
  have hYW₃ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% (cov.along Y W)) u := by
    simpa [CovariantDerivative.along] using (hcov₃.contMDiff hW).clm_bundle_apply hY
  have hYZW₂ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (T% (cov.along Y (cov.along Z W))) u := by
    simpa [CovariantDerivative.along] using (hcov₂.contMDiff hZW₃).clm_bundle_apply hY₂
  have hZYW₂ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (T% (cov.along Z (cov.along Y W))) u := by
    simpa [CovariantDerivative.along] using (hcov₂.contMDiff hYW₃).clm_bundle_apply hZ₂
  have hbrWithin : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (T% (VectorField.mlieBracketWithin I Y Z u)) u := by
    simpa using hY.mlieBracketWithin_vectorField (I := I) (m := (2 : ℕ∞)) hZ
      hu.uniqueMDiffOn (by norm_num)
  have hbr : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (T% (VectorField.mlieBracket I Y Z)) u := by
    refine ContMDiffOn.congr hbrWithin ?_
    intro y hy
    have hYy : MDiffAt (T% Y) y :=
      (((hY y hy).contMDiffAt (hu.mem_nhds hy)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero
    have hZy : MDiffAt (T% Z) y :=
      (((hZ y hy).contMDiffAt (hu.mem_nhds hy)).of_le
        (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero
    congr 1
    simpa using
      (VectorField.mlieBracketWithin_eq_mlieBracket (I := I) (s := u) (x := y)
        (hu.uniqueMDiffWithinAt hy) hYy hZy).symm
  have hbrW₂ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (T% (cov.along (VectorField.mlieBracket I Y Z) W)) u := by
    simpa [CovariantDerivative.along] using
      (hcov₂.contMDiff hW₃).clm_bundle_apply hbr
  have hcomb := (hYZW₂.sub_section hZYW₂).sub_section hbrW₂
  simpa only [CovariantDerivative.curvatureAux] using hcomb

/-- The bundled curvature tensor evaluated on local vector fields is `C²` for a `C³` connection.
The comparison with the raw commutator is pointwise tensoriality; the differentiability estimate
comes from the actual connection commutator above. -/
theorem curvatureTensor_contMDiffOn_frame_two
    [ContMDiffVectorBundle 4 E TM I]
    [SigmaCompactSpace M]
    [_root_.Bundle.RiemannianBundle TM]
    {cov : CovariantDerivative I E TM}
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    [cov.ContMDiffCovariantDerivative 3]
    {ea eb ec : Π x : M, TM x} {u : Set M} (hu : IsOpen u)
    (hea : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% ea) u)
    (heb : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% eb) u)
    (hec : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 4 (T% ec) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun z ↦ TotalSpace.mk' E z
        (CovariantDerivative.curvatureTensor (cov := cov) z (ea z) (eb z) (ec z))) u := by
  haveI : IsManifold I (minSmoothness ℝ 4) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  haveI : IsManifold I ((3 : ℕ∞) + 1) M :=
    IsManifold.of_le (n := (∞ : WithTop ℕ∞)) (by exact_mod_cast le_top)
  have hcurv := curvatureAux_contMDiffOn_two (cov := cov) hu hea heb hec
  refine hcurv.congr ?_
  intro z hz
  exact congrArg (TotalSpace.mk' E z)
    (RicciFlow.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
      (cov := cov) hu hz
      (hea.of_le (by norm_num)) (heb.of_le (by norm_num))
      (hec.of_le (by norm_num))).symm

/-- C² frame coefficients determine C² regularity of an intrinsic covariant two-tensor section. -/
theorem contMDiffAt_two_covariantTwoTensor_of_localFrame
    [RiemannianBundle TM] [ContMDiffVectorBundle 2 E TM I]
    (s : ∀ x : M, T₂ x) (x : M)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (hcomp : ∀ i j, ContMDiffAt I 𝓘(ℝ) 2
      (fun y ↦ s y
        ((trivializationAt E TM x).localFrame b i y)
        ((trivializationAt E TM x).localFrame b j y)) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) y (s y)) x := by
  classical
  rw [Bundle.contMDiffAt_section
    (IB := I) (F := E →L[ℝ] E →L[ℝ] ℝ) (E := T₂) (s := s) x]
  let e := trivializationAt E TM x
  let BilF := E →L[ℝ] E →L[ℝ] ℝ
  let coord : M → BilF := fun y ↦
    (trivializationAt BilF T₂ x (TotalSpace.mk' BilF y (s y))).2
  change ContMDiffAt I 𝓘(ℝ, BilF) 2 coord x
  apply contMDiffAt_clm_of_forall_apply_basis b
  intro i
  apply contMDiffAt_clm_of_forall_apply_basis b
  intro j
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x
  have hev : (fun y ↦ coord y (b i) (b j)) =ᶠ[nhds x]
      (fun y ↦ s y (e.localFrame b i y) (e.localFrame b j y)) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    rw [show coord y =
      (trivializationAt BilF T₂ x (TotalSpace.mk' BilF y (s y))).2 by rfl]
    rw [trivializationAt_bilinearFormBundle_apply_eq
      (F := E) (W := TM) x y hy (s y) (b i) (b j)]
    have hli : ∀ k, ((e.continuousLinearEquivAt ℝ y hy).symm (b k)) =
        e.localFrame b k y := by
      intro k
      rw [e.localFrame_apply_of_mem_baseSet b hy]
      rfl
    rw [hli i, hli j]
  exact (hcomp i j).congr_of_eventuallyEq hev

/-- A `C³` tangent connection has a genuinely `C²` intrinsic Ricci tensor section.
This is derived from the actual curvature tensor in a local frame and its finite-dimensional trace. -/
theorem ricciBilinearFormSection_contMDiff_two
    [ContMDiffVectorBundle 4 E TM I] [SigmaCompactSpace M]
    [_root_.Bundle.RiemannianBundle TM]
    (cov : CovariantDerivative I E TM)
    [cov.ContMDiffCovariantDerivative 1] [cov.ContMDiffCovariantDerivative 2]
    [cov.ContMDiffCovariantDerivative 3]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := T₂) x
        (RicciFlow.ricciBilinearFormSection (I := I) (M := M) cov x)) := by
  classical
  intro x0
  refine contMDiffAt_two_covariantTwoTensor_of_localFrame
    (RicciFlow.ricciBilinearFormSection (I := I) (M := M) cov) x0 b ?_
  intro i j
  let e := trivializationAt E TM x0
  have hbase : IsOpen e.baseSet := e.open_baseSet
  have hx0 : x0 ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E TM x0
  have hframe4 : ∀ m : ι, ContMDiffOn I (I.prod 𝓘(ℝ, E)) 4
      (fun x ↦ TotalSpace.mk' E x (e.localFrame b m x)) e.baseSet :=
    fun m ↦ e.contMDiffOn_localFrame_baseSet (I := I) (n := 4) b m
  let term : ι → M → ℝ := fun k x ↦
    e.localFrameCoeff I b k x
      (CovariantDerivative.curvatureTensor (cov := cov) x
        (e.localFrame b k x) (e.localFrame b i x) (e.localFrame b j x))
  have hterm : ∀ k, ContMDiffOn I 𝓘(ℝ) 2 (term k) e.baseSet := by
    intro k
    have hcurv := curvatureTensor_contMDiffOn_frame_two (cov := cov) hbase
      ((hframe4 k).of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4))
      ((hframe4 i).of_le (by norm_num : (3 : WithTop ℕ∞) ≤ 4)) (hframe4 j)
    simpa [term] using
      (contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b)
        (k := (2 : WithTop ℕ∞)) hbase (subset_refl _) hcurv k)
  have hsum : ∀ s : Finset ι,
      ContMDiffOn I 𝓘(ℝ) 2 (fun x ↦ s.sum (fun k ↦ term k x)) e.baseSet := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using
        (contMDiffOn_const : ContMDiffOn I 𝓘(ℝ) 2 (fun _ : M ↦ (0 : ℝ)) e.baseSet)
    | @insert k s hk hs =>
        convert (hterm k).add hs using 1 <;> ext x <;>
          simp only [Finset.sum_insert, hk, not_false_eq_true, Pi.add_apply]
  have hreg := (hsum Finset.univ).contMDiffAt (hbase.mem_nhds hx0)
  refine hreg.congr_of_eventuallyEq ?_
  filter_upwards [hbase.mem_nhds hx0] with x hx
  change RicciFlow.ricciBilinearFormSection (I := I) (M := M) cov x
      (e.localFrame b i x) (e.localFrame b j x) = (∑ k, term k x)
  rw [RicciFlow.ricciBilinearFormSection_apply,
    RicciFlow.ricciCurvature_eq_sum_localFrameCoeff b x0 hx]

end CovariantDerivative

end
