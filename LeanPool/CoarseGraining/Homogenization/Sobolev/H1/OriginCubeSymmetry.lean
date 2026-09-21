/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Probability.OriginCubeSymmetry
import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Module.Equiv

/-! # Origin Cube Symmetry -/

namespace Homogenization

open scoped Topology

noncomputable section

/-- File-level typeclass cache for `Module ℝ (Vec d)`. -/
private instance instModuleVecOCS (d : ℕ) : Module ℝ (Vec d) := inferInstance

/--
Coordinate sign-flip on `Vec d` as a continuous linear equivalence.
-/
noncomputable def signFlipVecContinuousLinearEquiv {d : ℕ} (i : Fin d) :
    Vec d ≃L[ℝ] Vec d :=
  ContinuousLinearEquiv.piCongrRight fun j : Fin d =>
    if h : j = i then
      by
        subst h
        exact ContinuousLinearEquiv.neg ℝ
    else
      ContinuousLinearEquiv.refl ℝ ℝ

/--
Coordinate swap on `Vec d` as a continuous linear equivalence.
-/
noncomputable def swapVecContinuousLinearEquiv {d : ℕ} (i j : Fin d) :
    Vec d ≃L[ℝ] Vec d :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin d => ℝ) (Equiv.swap i j)

@[simp] theorem signFlipVecContinuousLinearEquiv_apply {d : ℕ} (i : Fin d) (x : Vec d) :
    signFlipVecContinuousLinearEquiv i x = matVecMul (signFlipMatrix i) x := by
  ext j
  by_cases h : j = i
  · subst h
    simp [signFlipVecContinuousLinearEquiv, matVecMul_signFlipMatrix_apply]
  · simp [signFlipVecContinuousLinearEquiv, matVecMul_signFlipMatrix_apply, h]

@[simp] theorem signFlipVecContinuousLinearEquiv_symm_apply {d : ℕ} (i : Fin d) (x : Vec d) :
    (signFlipVecContinuousLinearEquiv i).symm x = matVecMul (signFlipMatrix i) x := by
  have hs : (signFlipVecContinuousLinearEquiv i).symm = signFlipVecContinuousLinearEquiv i := by
    ext y j
    by_cases h : j = i
    · subst h
      simp [signFlipVecContinuousLinearEquiv]
    · simp [signFlipVecContinuousLinearEquiv, h]
  rw [hs]
  exact signFlipVecContinuousLinearEquiv_apply i x

@[simp] theorem swapVecContinuousLinearEquiv_apply {d : ℕ} (i j : Fin d) (x : Vec d) :
    swapVecContinuousLinearEquiv i j x = matVecMul (Matrix.swap ℝ i j) x := by
  ext k
  have h :=
    Homeomorph.piCongrLeft_apply_apply (Y := fun _ : Fin d => ℝ) (Equiv.swap i j) x
      (Equiv.swap i j k)
  simpa [swapVecContinuousLinearEquiv, matVecMul_swap_eq_comp] using! h

@[simp] theorem swapVecContinuousLinearEquiv_symm_apply {d : ℕ} (i j : Fin d) (x : Vec d) :
    (swapVecContinuousLinearEquiv i j).symm x = matVecMul (Matrix.swap ℝ i j) x := by
  ext k
  have hfun :
      ⇑(Homeomorph.piCongrLeft (Y := fun _ : Fin d => ℝ) (Equiv.swap i j)).symm =
        fun y z => y ((Equiv.swap i j) z) :=
    Homeomorph.piCongrLeft_symm_apply (Y := fun _ : Fin d => ℝ) (Equiv.swap i j)
  have h :
      (swapVecContinuousLinearEquiv i j).symm x k = x ((Equiv.swap i j) k) := by
    change (Homeomorph.piCongrLeft (Y := fun _ : Fin d => ℝ) (Equiv.swap i j)).symm x k = _
    exact congrFun (congrFun hfun x) k
  simp [h, matVecMul_swap_eq_comp]

@[simp] theorem signFlipVecContinuousLinearEquiv_self_apply {d : ℕ} (i : Fin d) (x : Vec d) :
    signFlipVecContinuousLinearEquiv i (signFlipVecContinuousLinearEquiv i x) = x := by
  have hs : (signFlipVecContinuousLinearEquiv i).symm = signFlipVecContinuousLinearEquiv i := by
    ext y j
    by_cases h : j = i
    · subst h
      simp [signFlipVecContinuousLinearEquiv]
    · simp [signFlipVecContinuousLinearEquiv, h]
  simpa [hs] using (signFlipVecContinuousLinearEquiv i).apply_symm_apply x

@[simp] theorem swapVecContinuousLinearEquiv_self_apply {d : ℕ} (i j : Fin d) (x : Vec d) :
    swapVecContinuousLinearEquiv i j (swapVecContinuousLinearEquiv i j x) = x := by
  simpa [swapVecContinuousLinearEquiv_symm_apply] using
    (swapVecContinuousLinearEquiv i j).apply_symm_apply x

@[simp] theorem signFlipVecContinuousLinearEquiv_basisVec {d : ℕ} (i k : Fin d) :
    signFlipVecContinuousLinearEquiv i (basisVec k) =
      (if k = i then (-1 : ℝ) else 1) • basisVec k := by
  by_cases hki : k = i
  · subst hki
    ext j
    by_cases hjk : j = k
    · subst hjk
      simp [basisVec_apply, signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply]
    · simp [basisVec_apply, signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply,
        hjk]
  · ext j
    by_cases hjk : j = k
    · subst hjk
      simp [basisVec_apply, signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply,
        hki]
    · simp [basisVec_apply, signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply,
        hki, hjk]

@[simp] theorem swapVecContinuousLinearEquiv_basisVec {d : ℕ} (i j k : Fin d) :
    swapVecContinuousLinearEquiv i j (basisVec k) = basisVec (Equiv.swap i j k) := by
  ext l
  by_cases h : (Equiv.swap i j l) = k
  · have h' : l = Equiv.swap i j k := by
      simpa using congrArg (Equiv.swap i j) h
    simp [basisVec_apply, swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp, h']
  · have h' : l ≠ Equiv.swap i j k := by
      intro hl
      apply h
      simp [hl]
    simp [basisVec_apply, swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp, h, h']

private theorem measurePreserving_signFlipVecContinuousLinearEquiv {d : ℕ} (i : Fin d) :
    MeasureTheory.MeasurePreserving (signFlipVecContinuousLinearEquiv i) MeasureTheory.volume
      MeasureTheory.volume := by
  classical
  simpa [signFlipVecContinuousLinearEquiv_apply] using!
    (MeasureTheory.volume_preserving_pi fun j : Fin d =>
      by
        by_cases h : j = i
        · subst h
          simpa using!
            (MeasureTheory.Measure.measurePreserving_neg
              (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        · simpa [h] using
            (MeasureTheory.MeasurePreserving.id
              (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ))))

private theorem measurePreserving_swapVecContinuousLinearEquiv {d : ℕ} (i j : Fin d) :
    MeasureTheory.MeasurePreserving (swapVecContinuousLinearEquiv i j) MeasureTheory.volume
      MeasureTheory.volume := by
  simpa [swapVecContinuousLinearEquiv] using!
    (MeasureTheory.volume_measurePreserving_piCongrLeft
      (fun _ : Fin d => ℝ) (Equiv.swap i j))

private theorem measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube
    {d : ℕ} (i : Fin d) (n : ℤ) :
    MeasureTheory.MeasurePreserving (signFlipVecContinuousLinearEquiv i)
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n)))
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n))) := by
  let U := openCubeSet (originCube d n)
  have hpre : (signFlipVecContinuousLinearEquiv i) ⁻¹' U = U := by
    ext x
    simpa [U] using (mem_openCubeSet_originCube_signFlipMatrix_iff (m := n) (i := i) (x := x))
  simpa [U, hpre] using
    (measurePreserving_signFlipVecContinuousLinearEquiv i).restrict_preimage_emb
      (signFlipVecContinuousLinearEquiv i).toHomeomorph.measurableEmbedding U

private theorem measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube
    {d : ℕ} (i j : Fin d) (n : ℤ) :
    MeasureTheory.MeasurePreserving (swapVecContinuousLinearEquiv i j)
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n)))
      (MeasureTheory.volume.restrict (openCubeSet (originCube d n))) := by
  let U := openCubeSet (originCube d n)
  have hpre : (swapVecContinuousLinearEquiv i j) ⁻¹' U = U := by
    ext x
    simpa [U] using (mem_openCubeSet_originCube_swap_iff (m := n) (i := i) (j := j) (x := x))
  simpa [U, hpre] using
    (measurePreserving_swapVecContinuousLinearEquiv i j).restrict_preimage_emb
      (swapVecContinuousLinearEquiv i j).toHomeomorph.measurableEmbedding U

theorem setIntegral_comp_signFlipVecContinuousLinearEquiv_openCubeSet_originCube
    {d : ℕ} (i : Fin d) (n : ℤ) (f : Vec d → ℝ) :
    ∫ x in openCubeSet (originCube d n), f (signFlipVecContinuousLinearEquiv i x)
      ∂MeasureTheory.volume =
      ∫ x in openCubeSet (originCube d n), f x ∂MeasureTheory.volume := by
  let U := openCubeSet (originCube d n)
  let hμ := measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i n
  simpa [U] using
    (hμ.integral_comp (signFlipVecContinuousLinearEquiv i).toHomeomorph.measurableEmbedding f)

theorem setIntegral_comp_swapVecContinuousLinearEquiv_openCubeSet_originCube
    {d : ℕ} (i j : Fin d) (n : ℤ) (f : Vec d → ℝ) :
    ∫ x in openCubeSet (originCube d n), f (swapVecContinuousLinearEquiv i j x)
      ∂MeasureTheory.volume =
      ∫ x in openCubeSet (originCube d n), f x ∂MeasureTheory.volume := by
  let U := openCubeSet (originCube d n)
  let hμ := measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube i j n
  simpa [U] using
    (hμ.integral_comp (swapVecContinuousLinearEquiv i j).toHomeomorph.measurableEmbedding f)

private theorem fderiv_comp_signFlipVecContinuousLinearEquiv_apply_basisVec {d : ℕ}
    (i k : Fin d) {φ : Vec d → ℝ} {x : Vec d}
    (hφ : DifferentiableAt ℝ φ (signFlipVecContinuousLinearEquiv i x)) :
    (fderiv ℝ (fun y => φ (signFlipVecContinuousLinearEquiv i y)) x) (basisVec k) =
      (if k = i then (-1 : ℝ) else 1) *
        (fderiv ℝ φ (signFlipVecContinuousLinearEquiv i x)) (basisVec k) := by
  let T : Vec d → Vec d := signFlipVecContinuousLinearEquiv i
  have hcomp :
      fderiv ℝ (fun y => φ (T y)) x =
        (fderiv ℝ φ (T x)).comp (fderiv ℝ T x) := by
    simpa [T] using
      (fderiv_fun_comp (f := T) (g := φ) x hφ (signFlipVecContinuousLinearEquiv i).differentiableAt)
  have hlin : fderiv ℝ T x = (signFlipVecContinuousLinearEquiv i).toContinuousLinearMap := by
    simpa [T] using ((signFlipVecContinuousLinearEquiv i).toContinuousLinearMap.fderiv (x := x))
  have hb :
      (signFlipVecContinuousLinearEquiv i).toContinuousLinearMap (basisVec k) =
        (if k = i then (-1 : ℝ) else 1) • basisVec k := by
    simpa using (signFlipVecContinuousLinearEquiv_basisVec (i := i) (k := k))
  calc
    (fderiv ℝ (fun y => φ (signFlipVecContinuousLinearEquiv i y)) x) (basisVec k)
      = ((fderiv ℝ φ (T x)).comp (fderiv ℝ T x)) (basisVec k) := by
          simpa [T] using congrArg (fun L => L (basisVec k)) hcomp
    _ = ((fderiv ℝ φ (T x)).comp (signFlipVecContinuousLinearEquiv i).toContinuousLinearMap)
          (basisVec k) := by rw [hlin]
    _ = (fderiv ℝ φ (T x))
          ((signFlipVecContinuousLinearEquiv i).toContinuousLinearMap (basisVec k)) := by
            rw [ContinuousLinearMap.comp_apply]
    _ = (fderiv ℝ φ (T x)) (((if k = i then (-1 : ℝ) else 1) • basisVec k)) := by rw [hb]
    _ = (if k = i then (-1 : ℝ) else 1) * (fderiv ℝ φ (T x)) (basisVec k) := by
          by_cases hki : k = i <;> simp [hki]
    _ = (if k = i then (-1 : ℝ) else 1) *
        (fderiv ℝ φ (signFlipVecContinuousLinearEquiv i x)) (basisVec k) := by
          simp [T]

private theorem fderiv_comp_swapVecContinuousLinearEquiv_apply_basisVec {d : ℕ}
    (i j k : Fin d) {φ : Vec d → ℝ} {x : Vec d}
    (hφ : DifferentiableAt ℝ φ (swapVecContinuousLinearEquiv i j x)) :
    (fderiv ℝ (fun y => φ (swapVecContinuousLinearEquiv i j y)) x) (basisVec (Equiv.swap i j k)) =
      (fderiv ℝ φ (swapVecContinuousLinearEquiv i j x)) (basisVec k) := by
  let T : Vec d → Vec d := swapVecContinuousLinearEquiv i j
  have hcomp :
      fderiv ℝ (fun y => φ (T y)) x =
        (fderiv ℝ φ (T x)).comp (fderiv ℝ T x) := by
    simpa [T] using
      (fderiv_fun_comp (f := T) (g := φ) x hφ (swapVecContinuousLinearEquiv i j).differentiableAt)
  have hlin : fderiv ℝ T x = (swapVecContinuousLinearEquiv i j).toContinuousLinearMap := by
    simpa [T] using ((swapVecContinuousLinearEquiv i j).toContinuousLinearMap.fderiv (x := x))
  have hb :
      (swapVecContinuousLinearEquiv i j).toContinuousLinearMap (basisVec (Equiv.swap i j k)) =
        basisVec k := by
    simpa using
      (swapVecContinuousLinearEquiv_basisVec (i := i) (j := j) (k := Equiv.swap i j k))
  calc
    (fderiv ℝ (fun y => φ (swapVecContinuousLinearEquiv i j y)) x) (basisVec (Equiv.swap i j k))
      = ((fderiv ℝ φ (T x)).comp (fderiv ℝ T x)) (basisVec (Equiv.swap i j k)) := by
          simpa [T] using congrArg (fun L => L (basisVec (Equiv.swap i j k))) hcomp
    _ = ((fderiv ℝ φ (T x)).comp (swapVecContinuousLinearEquiv i j).toContinuousLinearMap)
          (basisVec (Equiv.swap i j k)) := by rw [hlin]
    _ = (fderiv ℝ φ (T x))
          ((swapVecContinuousLinearEquiv i j).toContinuousLinearMap
            (basisVec (Equiv.swap i j k))) := by
            rw [ContinuousLinearMap.comp_apply]
    _ = (fderiv ℝ φ (T x)) (basisVec k) := by rw [hb]
    _ = (fderiv ℝ φ (swapVecContinuousLinearEquiv i j x)) (basisVec k) := by
          simp [T]

private theorem tsupport_comp_homeomorph_eq_preimage {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {f : β → ℝ} (e : α ≃ₜ β) :
    tsupport (fun x => f (e x)) = e ⁻¹' tsupport f := by
  rw [tsupport, tsupport, e.preimage_closure]
  ext x
  simp [Function.support]

private theorem tsupport_comp_signFlip_subset_openCubeSet_originCube {d : ℕ}
    {f : Vec d → ℝ} (i : Fin d) (n : ℤ)
    (hsub : tsupport f ⊆ openCubeSet (originCube d n)) :
    tsupport (fun x => f (signFlipVecContinuousLinearEquiv i x)) ⊆
      openCubeSet (originCube d n) := by
  let U := openCubeSet (originCube d n)
  intro x hx
  have htsupp :
      tsupport (fun y => f (signFlipVecContinuousLinearEquiv i y)) =
        (signFlipVecContinuousLinearEquiv i) ⁻¹' tsupport f :=
    tsupport_comp_homeomorph_eq_preimage (signFlipVecContinuousLinearEquiv i).toHomeomorph
  have hx' : signFlipVecContinuousLinearEquiv i x ∈ tsupport f := by
    rw [htsupp] at hx
    exact hx
  have hTx : signFlipVecContinuousLinearEquiv i x ∈ U := hsub hx'
  have hTx' : matVecMul (signFlipMatrix i) x ∈ U := by
    simpa [signFlipVecContinuousLinearEquiv_apply] using hTx
  simpa [U] using
    (mem_openCubeSet_originCube_signFlipMatrix_iff (m := n) (i := i) (x := x)).1 hTx'

private theorem tsupport_comp_swap_subset_openCubeSet_originCube {d : ℕ}
    {f : Vec d → ℝ} (i j : Fin d) (n : ℤ)
    (hsub : tsupport f ⊆ openCubeSet (originCube d n)) :
    tsupport (fun x => f (swapVecContinuousLinearEquiv i j x)) ⊆
      openCubeSet (originCube d n) := by
  let U := openCubeSet (originCube d n)
  intro x hx
  have htsupp :
      tsupport (fun y => f (swapVecContinuousLinearEquiv i j y)) =
        (swapVecContinuousLinearEquiv i j) ⁻¹' tsupport f :=
    tsupport_comp_homeomorph_eq_preimage (swapVecContinuousLinearEquiv i j).toHomeomorph
  have hx' : swapVecContinuousLinearEquiv i j x ∈ tsupport f := by
    rw [htsupp] at hx
    exact hx
  have hTx : swapVecContinuousLinearEquiv i j x ∈ U := hsub hx'
  have hTx' : matVecMul (Matrix.swap ℝ i j) x ∈ U := by
    simpa [swapVecContinuousLinearEquiv_apply] using hTx
  simpa [U] using
    (mem_openCubeSet_originCube_swap_iff (m := n) (i := i) (j := j) (x := x)).1 hTx'

namespace H1Function

/--
Precompose an `H¹` witness on the open centered cube with a coordinate sign
flip, transporting the weak gradient by the same sign flip.
-/
noncomputable def signFlipOnOpenCubeSetOriginCube {d : ℕ} {n : ℤ}
    (u : H1Function (openCubeSet (originCube d n))) (i : Fin d) :
    H1Function (openCubeSet (originCube d n)) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let T : Vec d → Vec d := signFlipVecContinuousLinearEquiv i
  let hμ := measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i n
  refine
    { toFun := fun x => u (T x)
      grad := fun x => signFlipVecContinuousLinearEquiv i (u.grad (T x))
      memL2 := by
        show MemL2On U (u.toFun ∘ signFlipVecContinuousLinearEquiv i)
        simpa [MemL2On, U, Function.comp] using u.memL2.comp_measurePreserving hμ
      gradMemL2 := by
        intro k
        have hcomp :
            MemL2On U ((fun x => u.grad x k) ∘ signFlipVecContinuousLinearEquiv i) := by
          simpa [MemL2On, U, Function.comp] using
            (u.gradMemL2 k).comp_measurePreserving hμ
        by_cases hki : k = i
        · simpa [U, T, signFlipVecContinuousLinearEquiv_apply,
            matVecMul_signFlipMatrix_apply, hki] using hcomp.const_mul (-1 : ℝ)
        · simpa [U, T, signFlipVecContinuousLinearEquiv_apply,
            matVecMul_signFlipMatrix_apply, hki] using hcomp.const_mul (1 : ℝ)
      hasWeakGradient := ?_ }
  intro k φ hφ hφ_supp hφ_sub
  let ψ : Vec d → ℝ := fun x => φ (T x)
  let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec k)
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    show ContDiff ℝ (⊤ : ℕ∞) (φ ∘ signFlipVecContinuousLinearEquiv i)
    simpa [ψ, T, Function.comp] using
      (ContDiff.comp_continuousLinearMap
        (g := (signFlipVecContinuousLinearEquiv i).toContinuousLinearMap) hφ)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (φ ∘ signFlipVecContinuousLinearEquiv i)
    simpa [ψ, T, Function.comp] using
      hφ_supp.comp_homeomorph (signFlipVecContinuousLinearEquiv i).toHomeomorph
  have hψ_sub : tsupport ψ ⊆ U := by
    simpa [U, ψ, T] using
      tsupport_comp_signFlip_subset_openCubeSet_originCube (f := φ) i n hφ_sub
  have hweak := u.hasWeakGradient k ψ hψ_smooth hψ_supp hψ_sub
  have hleft :
      ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec k) ∂MeasureTheory.volume =
        (if k = i then (-1 : ℝ) else 1) *
          ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume := by
    have hfun :
        (fun x => u x * (fderiv ℝ ψ x) (basisVec k)) =
          fun x => (if k = i then (-1 : ℝ) else 1) * (u x * dφ (T x)) := by
      funext x
      have hx : DifferentiableAt ℝ φ (T x) := (hφ.differentiable (by simp)) (T x)
      rw [show ψ = fun y => φ (signFlipVecContinuousLinearEquiv i y) by
        funext y
        simp [ψ, T]]
      rw [fderiv_comp_signFlipVecContinuousLinearEquiv_apply_basisVec (i := i) (k := k) (x := x) hx]
      simp [dφ, T]
    rw [hfun, MeasureTheory.integral_const_mul]
  have hchange_left :
      ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume =
        ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume := by
    let f : Vec d → ℝ := fun y => u (T y) * dφ y
    show ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume =
      ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume
    simpa only [U, T, dφ, f, signFlipVecContinuousLinearEquiv_self_apply] using
      setIntegral_comp_signFlipVecContinuousLinearEquiv_openCubeSet_originCube i n f
  have hchange_right :
      ∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume =
        ∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by
    let f : Vec d → ℝ := fun y => u.grad (T y) k * φ y
    show ∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume =
      ∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume
    simpa only [U, T, f, signFlipVecContinuousLinearEquiv_self_apply] using
      setIntegral_comp_signFlipVecContinuousLinearEquiv_openCubeSet_originCube i n f
  have hmain :
      (if k = i then (-1 : ℝ) else 1) *
          ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume =
        -∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by
    calc
      (if k = i then (-1 : ℝ) else 1) *
          ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume
        = (if k = i then (-1 : ℝ) else 1) *
            ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume := by rw [hchange_left]
      _ = ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec k) ∂MeasureTheory.volume := by
            symm
            exact hleft
      _ = -∫ x in U, u.grad x k * ψ x ∂MeasureTheory.volume := hweak
      _ = -∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume := by rfl
      _ = -∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by rw [hchange_right]
  by_cases hki : k = i
  · simp [U, T, dφ, signFlipVecContinuousLinearEquiv_apply,
      matVecMul_signFlipMatrix_apply, hki, MeasureTheory.integral_neg] at hmain ⊢
    exact hmain
  · simp [U, T, dφ, signFlipVecContinuousLinearEquiv_apply,
      matVecMul_signFlipMatrix_apply, hki] at hmain ⊢
    exact hmain

/--
Precompose an `H¹` witness on the open centered cube with a coordinate swap,
transporting the weak gradient by the same swap.
-/
noncomputable def swapOnOpenCubeSetOriginCube {d : ℕ} {n : ℤ}
    (u : H1Function (openCubeSet (originCube d n))) (i j : Fin d) :
    H1Function (openCubeSet (originCube d n)) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let T : Vec d → Vec d := swapVecContinuousLinearEquiv i j
  let hμ := measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube i j n
  refine
    { toFun := fun x => u (matVecMul (Matrix.swap ℝ i j) x)
      grad := fun x => matVecMul (Matrix.swap ℝ i j) (u.grad (matVecMul (Matrix.swap ℝ i j) x))
      memL2 := by
        show MeasureTheory.MemLp
          (fun x => u.toFun (matVecMul (Matrix.swap ℝ i j) x)) 2
          (MeasureTheory.volume.restrict U)
        convert (u.memL2.comp_measurePreserving hμ) using 1
        ext x
        simp [Function.comp, swapVecContinuousLinearEquiv_apply]
      gradMemL2 := by
        intro l
        let k : Fin d := Equiv.swap i j l
        show MeasureTheory.MemLp
          (fun x => matVecMul (Matrix.swap ℝ i j) (u.grad (matVecMul (Matrix.swap ℝ i j) x)) l) 2
          (MeasureTheory.volume.restrict U)
        convert ((u.gradMemL2 k).comp_measurePreserving hμ) using 1
        ext x
        simp [k, Function.comp, swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp]
      hasWeakGradient := ?_ }
  intro l φ hφ hφ_supp hφ_sub
  let T : Vec d → Vec d := swapVecContinuousLinearEquiv i j
  let ψ : Vec d → ℝ := fun x => φ (T x)
  let k : Fin d := Equiv.swap i j l
  let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec l)
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    show ContDiff ℝ (⊤ : ℕ∞) (φ ∘ swapVecContinuousLinearEquiv i j)
    simpa [ψ, T, Function.comp] using
      (ContDiff.comp_continuousLinearMap
        (g := (swapVecContinuousLinearEquiv i j).toContinuousLinearMap) hφ)
  have hψ_supp : HasCompactSupport ψ := by
    show HasCompactSupport (φ ∘ swapVecContinuousLinearEquiv i j)
    simpa [ψ, T, Function.comp] using
      hφ_supp.comp_homeomorph (swapVecContinuousLinearEquiv i j).toHomeomorph
  have hψ_sub : tsupport ψ ⊆ U := by
    simpa [U, ψ, T] using
      tsupport_comp_swap_subset_openCubeSet_originCube (f := φ) i j n hφ_sub
  have hweak := u.hasWeakGradient k ψ hψ_smooth hψ_supp hψ_sub
  have hleft :
      ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec k) ∂MeasureTheory.volume =
        ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume := by
    have hfun :
        (fun x => u x * (fderiv ℝ ψ x) (basisVec k)) =
          fun x => u x * dφ (T x) := by
      funext x
      have hx : DifferentiableAt ℝ φ (T x) := (hφ.differentiable (by simp)) (T x)
      have hderiv :=
        fderiv_comp_swapVecContinuousLinearEquiv_apply_basisVec
          (i := i) (j := j) (k := l) (x := x) hx
      simpa [ψ, T, dφ, k] using congrArg (fun r => u x * r) hderiv
    rw [hfun]
  have hchange_left :
      ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume =
        ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume := by
    let f : Vec d → ℝ := fun y => u (T y) * dφ y
    show ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume =
      ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume
    simpa only [U, T, dφ, f, swapVecContinuousLinearEquiv_self_apply] using
      setIntegral_comp_swapVecContinuousLinearEquiv_openCubeSet_originCube i j n f
  have hchange_right :
      ∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume =
        ∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by
    let f : Vec d → ℝ := fun y => u.grad (T y) k * φ y
    show ∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume =
      ∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume
    simpa only [U, T, k, f, swapVecContinuousLinearEquiv_self_apply] using
      setIntegral_comp_swapVecContinuousLinearEquiv_openCubeSet_originCube i j n f
  have hmain :
      ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume =
        -∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by
    calc
      ∫ x in U, u (T x) * dφ x ∂MeasureTheory.volume
        = ∫ x in U, u x * dφ (T x) ∂MeasureTheory.volume := by rw [hchange_left]
      _ = ∫ x in U, u x * (fderiv ℝ ψ x) (basisVec k) ∂MeasureTheory.volume := by
            symm
            exact hleft
      _ = -∫ x in U, u.grad x k * ψ x ∂MeasureTheory.volume := hweak
      _ = -∫ x in U, u.grad x k * φ (T x) ∂MeasureTheory.volume := by rfl
      _ = -∫ x in U, u.grad (T x) k * φ x ∂MeasureTheory.volume := by rw [hchange_right]
  simpa [U, T, dφ, k, swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp] using hmain

end H1Function

namespace H10Function

/--
Precompose an `H¹₀` witness on the open centered cube with a coordinate sign
flip.
-/
noncomputable def signFlipOnOpenCubeSetOriginCube {d : ℕ} {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) (i : Fin d) :
    H10Function (openCubeSet (originCube d n)) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let T : Vec d → Vec d := signFlipVecContinuousLinearEquiv i
  let hμ := measurePreserving_signFlipVecContinuousLinearEquiv_restrict_openCubeSet_originCube i n
  refine
    { toH1Function := u.toH1Function.signFlipOnOpenCubeSetOriginCube i
      approx := fun m x => u.approx m (T x)
      approx_smooth := by
        intro m
        show ContDiff ℝ (⊤ : ℕ∞) (u.approx m ∘ signFlipVecContinuousLinearEquiv i)
        simpa [T, Function.comp] using
          (ContDiff.comp_continuousLinearMap
            (g := (signFlipVecContinuousLinearEquiv i).toContinuousLinearMap)
            (u.approx_smooth m))
      approx_hasCompactSupport := by
        intro m
        show HasCompactSupport (u.approx m ∘ signFlipVecContinuousLinearEquiv i)
        simpa [T, Function.comp] using
          (u.approx_hasCompactSupport m).comp_homeomorph
            (signFlipVecContinuousLinearEquiv i).toHomeomorph
      approx_support_subset := by
        intro m
        simpa [U, T] using
          tsupport_comp_signFlip_subset_openCubeSet_originCube
            (f := u.approx m) i n (u.approx_support_subset m)
      tendsto_approx := by
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x =>
                  u.approx m (T x) -
                    (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).toFun x)
                2 (MeasureTheory.volume.restrict U)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x => u.approx m x - u.toH1Function.toFun x)
                  2 (MeasureTheory.volume.restrict U)) := by
          funext m
          let g : Vec d → ℝ := fun x => u.approx m x - u.toH1Function.toFun x
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict U) := by
            exact (u.approx_smooth m).continuous.aestronglyMeasurable.sub
              u.toH1Function.memL2.aestronglyMeasurable
          have hfun :
              (fun x =>
                u.approx m (T x) -
                  (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).toFun x) =
                g ∘ T := by
            funext x
            simp [g, T, Function.comp, H1Function.signFlipOnOpenCubeSetOriginCube,
              signFlipVecContinuousLinearEquiv_apply]
          rw [hfun]
          simpa [g, T, Function.comp] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := (2 : ENNReal)) hg hμ)
        rw [hEq]
        exact u.tendsto_approx
      tendsto_approx_grad := by
        intro k
        by_cases hki : k = i
        · have hEq :
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x =>
                    (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                      (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).grad x k)
                  2 (MeasureTheory.volume.restrict U)) =
                (fun m =>
                  MeasureTheory.eLpNorm
                    (fun x =>
                      -((fderiv ℝ (u.approx m) x) (basisVec k) -
                        u.toH1Function.grad x k))
                    2 (MeasureTheory.volume.restrict U)) := by
            funext m
            let g : Vec d → ℝ := fun x =>
              -((fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)
            have hg :
                MeasureTheory.AEStronglyMeasurable g
                  (MeasureTheory.volume.restrict U) := by
              exact ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
                continuous_const |>.aestronglyMeasurable.sub
                  (u.toH1Function.gradMemL2 k).aestronglyMeasurable |>.neg
            have hfun :
                (fun x =>
                  (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                    (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).grad x k) =
                g ∘ T := by
              funext x
              have hx : DifferentiableAt ℝ (u.approx m) (T x) :=
                (u.approx_smooth m).differentiable (by simp) (T x)
              rw [fderiv_comp_signFlipVecContinuousLinearEquiv_apply_basisVec
                (i := i) (k := k) (x := x) hx]
              simp [g, T, hki, H1Function.signFlipOnOpenCubeSetOriginCube,
                signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply]
              ring
            rw [hfun]
            simpa [g, T, Function.comp] using
              (MeasureTheory.eLpNorm_comp_measurePreserving
                (g := g) (p := (2 : ENNReal)) hg hμ)
          rw [hEq]
          have hEqNeg :
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x =>
                    -((fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k))
                  2 (MeasureTheory.volume.restrict U)) =
                (fun m =>
                  MeasureTheory.eLpNorm
                    (fun x =>
                      (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)
                    2 (MeasureTheory.volume.restrict U)) := by
            funext m
            have hfun :
                (fun x =>
                  -((fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)) =
                (-1 : ℝ) •
                  (fun x =>
                    (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k) := by
              funext x
              simp
            rw [hfun, MeasureTheory.eLpNorm_const_smul]
            norm_num
          rw [hEqNeg]
          exact u.tendsto_approx_grad k
        · have hEq :
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x =>
                    (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                      (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).grad x k)
                  2 (MeasureTheory.volume.restrict U)) =
                (fun m =>
                  MeasureTheory.eLpNorm
                    (fun x =>
                      (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)
                    2 (MeasureTheory.volume.restrict U)) := by
            funext m
            let g : Vec d → ℝ := fun x =>
              (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k
            have hg :
                MeasureTheory.AEStronglyMeasurable g
                  (MeasureTheory.volume.restrict U) := by
              exact ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
                continuous_const |>.aestronglyMeasurable.sub
                  (u.toH1Function.gradMemL2 k).aestronglyMeasurable
            have hfun :
                (fun x =>
                  (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec k) -
                    (u.toH1Function.signFlipOnOpenCubeSetOriginCube i).grad x k) =
                g ∘ T := by
              funext x
              have hx : DifferentiableAt ℝ (u.approx m) (T x) :=
                (u.approx_smooth m).differentiable (by simp) (T x)
              rw [fderiv_comp_signFlipVecContinuousLinearEquiv_apply_basisVec
                (i := i) (k := k) (x := x) hx]
              simp [g, T, hki, H1Function.signFlipOnOpenCubeSetOriginCube,
                signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply]
            rw [hfun]
            simpa [g, T, Function.comp] using
              (MeasureTheory.eLpNorm_comp_measurePreserving
                (g := g) (p := (2 : ENNReal)) hg hμ)
          rw [hEq]
          exact u.tendsto_approx_grad k }

@[simp] theorem signFlipOnOpenCubeSetOriginCube_toH1Function {d : ℕ} {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) (i : Fin d) :
    (u.signFlipOnOpenCubeSetOriginCube i).toH1Function =
      u.toH1Function.signFlipOnOpenCubeSetOriginCube i :=
  rfl

/--
Precompose an `H¹₀` witness on the open centered cube with a coordinate swap.
-/
noncomputable def swapOnOpenCubeSetOriginCube {d : ℕ} {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) (i j : Fin d) :
    H10Function (openCubeSet (originCube d n)) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let T : Vec d → Vec d := swapVecContinuousLinearEquiv i j
  let hμ := measurePreserving_swapVecContinuousLinearEquiv_restrict_openCubeSet_originCube i j n
  refine
    { toH1Function := u.toH1Function.swapOnOpenCubeSetOriginCube i j
      approx := fun m x => u.approx m (T x)
      approx_smooth := by
        intro m
        show ContDiff ℝ (⊤ : ℕ∞) (u.approx m ∘ swapVecContinuousLinearEquiv i j)
        simpa [T, Function.comp] using
          (ContDiff.comp_continuousLinearMap
            (g := (swapVecContinuousLinearEquiv i j).toContinuousLinearMap)
            (u.approx_smooth m))
      approx_hasCompactSupport := by
        intro m
        show HasCompactSupport (u.approx m ∘ swapVecContinuousLinearEquiv i j)
        simpa [T, Function.comp] using
          (u.approx_hasCompactSupport m).comp_homeomorph
            (swapVecContinuousLinearEquiv i j).toHomeomorph
      approx_support_subset := by
        intro m
        simpa [U, T] using
          tsupport_comp_swap_subset_openCubeSet_originCube
            (f := u.approx m) i j n (u.approx_support_subset m)
      tendsto_approx := by
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x =>
                  u.approx m (T x) -
                    (u.toH1Function.swapOnOpenCubeSetOriginCube i j).toFun x)
                2 (MeasureTheory.volume.restrict U)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x => u.approx m x - u.toH1Function.toFun x)
                  2 (MeasureTheory.volume.restrict U)) := by
          funext m
          let g : Vec d → ℝ := fun x => u.approx m x - u.toH1Function.toFun x
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict U) := by
            exact (u.approx_smooth m).continuous.aestronglyMeasurable.sub
              u.toH1Function.memL2.aestronglyMeasurable
          have hfun :
              (fun x =>
                u.approx m (T x) -
                  (u.toH1Function.swapOnOpenCubeSetOriginCube i j).toFun x) =
                g ∘ T := by
            funext x
            simp [g, T, Function.comp, H1Function.swapOnOpenCubeSetOriginCube,
              swapVecContinuousLinearEquiv_apply]
          rw [hfun]
          simpa [g, T, Function.comp] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := (2 : ENNReal)) hg hμ)
        rw [hEq]
        exact u.tendsto_approx
      tendsto_approx_grad := by
        intro l
        let k : Fin d := Equiv.swap i j l
        have hEq :
            (fun m =>
              MeasureTheory.eLpNorm
                (fun x =>
                  (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec l) -
                    (u.toH1Function.swapOnOpenCubeSetOriginCube i j).grad x l)
                2 (MeasureTheory.volume.restrict U)) =
              (fun m =>
                MeasureTheory.eLpNorm
                  (fun x =>
                    (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k)
                  2 (MeasureTheory.volume.restrict U)) := by
          funext m
          let g : Vec d → ℝ := fun x =>
            (fderiv ℝ (u.approx m) x) (basisVec k) - u.toH1Function.grad x k
          have hg :
              MeasureTheory.AEStronglyMeasurable g
                (MeasureTheory.volume.restrict U) := by
            exact ((u.approx_smooth m).continuous_fderiv (by simp)).clm_apply
              continuous_const |>.aestronglyMeasurable.sub
                (u.toH1Function.gradMemL2 k).aestronglyMeasurable
          have hfun :
              (fun x =>
                (fderiv ℝ (fun y => u.approx m (T y)) x) (basisVec l) -
                  (u.toH1Function.swapOnOpenCubeSetOriginCube i j).grad x l) =
              g ∘ T := by
            funext x
            have hx : DifferentiableAt ℝ (u.approx m) (T x) :=
              (u.approx_smooth m).differentiable (by simp) (T x)
            rw [show basisVec l = basisVec (Equiv.swap i j k) by
              simp [k]]
            rw [fderiv_comp_swapVecContinuousLinearEquiv_apply_basisVec
              (i := i) (j := j) (k := k) (x := x) hx]
            simp [g, T, k, H1Function.swapOnOpenCubeSetOriginCube,
              swapVecContinuousLinearEquiv_apply, matVecMul_swap_eq_comp]
          rw [hfun]
          simpa [g, T, Function.comp] using
            (MeasureTheory.eLpNorm_comp_measurePreserving
              (g := g) (p := (2 : ENNReal)) hg hμ)
        rw [hEq]
        simpa [k] using u.tendsto_approx_grad k }

@[simp] theorem swapOnOpenCubeSetOriginCube_toH1Function {d : ℕ} {n : ℤ}
    (u : H10Function (openCubeSet (originCube d n))) (i j : Fin d) :
    (u.swapOnOpenCubeSetOriginCube i j).toH1Function =
      u.toH1Function.swapOnOpenCubeSetOriginCube i j :=
  rfl

end H10Function

end

end Homogenization
