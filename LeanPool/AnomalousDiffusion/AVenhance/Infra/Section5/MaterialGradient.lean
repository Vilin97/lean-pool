/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TransportCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Material differentiation of the spatial gradient of a smooth scalar field. -/

@[expose] public section

open Homogenization Filter Topology
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance

/-- The material derivative represented by the spacetime Fréchet derivative. -/
def materialDerivative (T : ℝ → Vec 2 → ℝ) (b : ℝ → Vec 2 → Vec 2) :
    ℝ → Vec 2 → ℝ := fun t x =>
  fderiv ℝ (Function.uncurry T) (t, x) (1, b t x)

/-- Restricting a spacetime Fréchet derivative to a spatial direction agrees
with differentiating the fixed-time slice. -/
theorem fderiv_uncurry_scalar_spatial
    {T : ℝ → Vec 2 → ℝ} {t : ℝ} {x v : Vec 2}
    (hT : DifferentiableAt ℝ (Function.uncurry T) (t, x)) :
    fderiv ℝ (Function.uncurry T) (t, x) (0, v) =
      fderiv ℝ (T t) x v := by
  let J : Vec 2 →L[ℝ] ℝ × Vec 2 := ContinuousLinearMap.inr ℝ ℝ (Vec 2)
  have hspace : HasFDerivAt (T t)
      ((fderiv ℝ (Function.uncurry T) (t, x)).comp J) x := by
    have h := hT.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    simpa [Function.uncurry, Function.comp_def, J] using h
  rw [hspace.fderiv]
  simp [J, ContinuousLinearMap.comp_apply]

/-- Vector-valued version of `fderiv_uncurry_scalar_spatial`. -/
theorem fderiv_uncurry_vector_spatial
    {B : ℝ → Vec 2 → Vec 2} {t : ℝ} {x v : Vec 2}
    (hB : DifferentiableAt ℝ (Function.uncurry B) (t, x)) :
    fderiv ℝ (Function.uncurry B) (t, x) (0, v) =
      fderiv ℝ (B t) x v := by
  let J : Vec 2 →L[ℝ] ℝ × Vec 2 := ContinuousLinearMap.inr ℝ ℝ (Vec 2)
  have hspace : HasFDerivAt (B t)
      ((fderiv ℝ (Function.uncurry B) (t, x)).comp J) x := by
    have h := hB.hasFDerivAt.comp x (hasFDerivAt_prodMk_right t x)
    simpa [Function.uncurry, Function.comp_def, J] using h
  rw [hspace.fderiv]
  simp [J, ContinuousLinearMap.comp_apply]

/-- The spacetime Fréchet representation is the ordinary material derivative
when the scalar field is differentiable. -/
theorem materialDerivative_eq_advective_of_hasFDerivAt
    {T : ℝ → Vec 2 → ℝ} {b : ℝ → Vec 2 → Vec 2}
    {t : ℝ} {x : Vec 2} {L : (ℝ × Vec 2) →L[ℝ] ℝ}
    (hF : HasFDerivAt (Function.uncurry T) L (t, x)) :
    materialDerivative T b t x =
      deriv (fun r => T r x) t +
        vecDot (b t x) (spaceGrad (T t) x) := by
  let J : Vec 2 →L[ℝ] ℝ × Vec 2 := ContinuousLinearMap.inr ℝ ℝ (Vec 2)
  have hspace : HasFDerivAt (T t) (L.comp J) x := by
    have h := hF.comp x (hasFDerivAt_prodMk_right t x)
    simpa [Function.uncurry, Function.comp_def, J] using h
  have htime : deriv (fun r => T r x) t = L (1, (0 : Vec 2)) := by
    let γ : ℝ → ℝ × Vec 2 := fun r => (r, x)
    have hγ : HasDerivAt γ (1, (0 : Vec 2)) t := by
      exact (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    simpa [γ, Function.uncurry, Function.comp_def] using
      deriv_uncurry_comp hF hγ
  have hspacegrad (j : Fin 2) :
      spaceGrad (T t) x j = L (0, basisVec j) := by
    change fderiv ℝ (T t) x (basisVec j) = _
    rw [hspace.fderiv]
    simp [J]
  have hdot : vecDot (b t x) (spaceGrad (T t) x) = L (0, b t x) := by
    have hbasis : b t x = ∑ j : Fin 2, (b t x j) • basisVec j := by
      funext j
      fin_cases j <;> simp [basisVec, Fin.sum_univ_two]
    rw [vecDot, Fin.sum_univ_two]
    have hpair : ((0 : ℝ), b t x) =
        ∑ j : Fin 2, (b t x j) • (0, basisVec j) := by
      have h := congrArg (fun v : Vec 2 => ((0 : ℝ), v)) hbasis
      simpa [Prod.smul_mk, Finset.sum_smul] using h
    rw [hpair, map_sum]
    rw [Fin.sum_univ_two]
    rw [L.map_smul, L.map_smul]
    simp only [hspacegrad]
    ring
  calc
    materialDerivative T b t x = L (1, b t x) := by
      rw [materialDerivative, hF.fderiv]
    _ = L (1, (0 : Vec 2)) + L (0, b t x) := by
      rw [← L.map_add]
      simp
    _ = deriv (fun r => T r x) t +
        vecDot (b t x) (spaceGrad (T t) x) := by rw [htime, hdot]

/-- The forward-flow form of transport calculus: differentiating a scalar
field along a characteristic gives its material derivative. -/
theorem deriv_comp_flow_eq_materialDerivative
    {T : ℝ → Vec 2 → ℝ} {b : ℝ → Vec 2 → Vec 2}
    {X : ℝ → Vec 2 → ℝ → Vec 2}
    {t s : ℝ} {y : Vec 2}
    (hX : IsFlow b X)
    (hF : HasFDerivAt (Function.uncurry T)
      (fderiv ℝ (Function.uncurry T) (t, X t y s)) (t, X t y s)) :
    deriv (fun r => T r (X r y s)) t =
      materialDerivative T b t (X t y s) := by
  rw [materialDerivative]
  exact deriv_comp_flow hF hX

/-- Along a flow characteristic, the spatial gradient differentiates by the
gradient of the material derivative and the usual velocity-gradient
correction. The eventual equality `hgrad` is the local identification of a
spatial slice derivative with the corresponding spacetime derivative. -/
theorem gradient_material_deriv_along_flow
    {T : ℝ → Vec 2 → ℝ} {b : ℝ → Vec 2 → Vec 2}
    {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : IsFlow b X) {t s : ℝ} {y : Vec 2} (i : Fin 2)
    (hT : ContDiffAt ℝ 2 (Function.uncurry T) (t, X t y s))
    (hb : ContDiffAt ℝ 1 (Function.uncurry b) (t, X t y s))
    (hgrad : (fun r => spaceGrad (T r) (X r y s) i) =ᶠ[𝓝 t]
      fun r => fderiv ℝ (Function.uncurry T) (r, X r y s) (0, basisVec i)) :
    HasDerivAt (fun r => spaceGrad (T r) (X r y s) i)
      (spaceGrad (materialDerivative T b t) (X t y s) i -
        fderiv ℝ (Function.uncurry T) (t, X t y s)
          (0, fderiv ℝ (Function.uncurry b) (t, X t y s) (0, basisVec i))) t := by
  let p : ℝ × Vec 2 := (t, X t y s)
  let F : (ℝ × Vec 2) → ℝ := Function.uncurry T
  let B : (ℝ × Vec 2) → Vec 2 := Function.uncurry b
  let V : (ℝ × Vec 2) → ℝ × Vec 2 := fun q => (1, B q)
  let LV : (ℝ × Vec 2) →L[ℝ] (ℝ × Vec 2) :=
    (0 : (ℝ × Vec 2) →L[ℝ] ℝ).prod (fderiv ℝ B p)
  let D2 : (ℝ × Vec 2) →L[ℝ] (ℝ × Vec 2 →L[ℝ] ℝ) :=
    fderiv ℝ (fderiv ℝ F) p
  have hDFcont : ContDiffAt ℝ 1 (fderiv ℝ F) p :=
    hT.fderiv_right (m := 1) (by norm_num)
  have hDF : HasFDerivAt (fderiv ℝ F) D2 p := by
    exact (hDFcont.differentiableAt (by norm_num)).hasFDerivAt
  have hBderiv : HasFDerivAt B (fderiv ℝ B p) p := by
    exact (hb.differentiableAt (by norm_num)).hasFDerivAt
  have hV : HasFDerivAt V LV p := by
    change HasFDerivAt (fun q => (1, B q)) LV p
    simpa [LV] using (hasFDerivAt_const (1 : ℝ) p).prodMk hBderiv
  let Q : (ℝ × Vec 2) → ℝ := fun q => (fderiv ℝ F q) (V q)
  have hQ : HasFDerivAt Q
      ((fderiv ℝ F p).comp LV + D2.flip (V p)) p := by
    simpa [Q] using hDF.clm_apply hV
  have hQslice : HasFDerivAt (materialDerivative T b t)
      (((fderiv ℝ F p).comp LV + D2.flip (V p)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2)))
      (X t y s) := by
    change HasFDerivAt (fun x => Q (t, x)) _ (X t y s)
    have h := hQ.comp (X t y s)
      (hasFDerivAt_prodMk_right t (X t y s))
    simpa [Q, Function.comp_def] using h
  have hQgrad : spaceGrad (materialDerivative T b t) (X t y s) i =
      ((fderiv ℝ F p).comp LV + D2.flip (V p))
        (0, basisVec i) := by
    change fderiv ℝ (materialDerivative T b t) (X t y s) (basisVec i) = _
    rw [hQslice.fderiv]
    simp
  let G : ℝ → Vec 2 → ℝ := fun r x =>
    fderiv ℝ F (r, x) (0, basisVec i)
  have hG : HasFDerivAt (Function.uncurry G) (D2.flip (0, basisVec i)) p := by
    change HasFDerivAt (fun q => (fderiv ℝ F q) (0, basisVec i)) _ p
    simpa [D2] using hDF.clm_apply (hasFDerivAt_const (0, basisVec i) p)
  have hcurve : HasDerivAt (fun r => G r (X r y s))
      (D2.flip (0, basisVec i) (1, b t (X t y s))) t := by
    let γ : ℝ → ℝ × Vec 2 := fun r => (r, X r y s)
    have hγ : HasDerivAt γ (1, b t (X t y s)) t := by
      exact (hasDerivAt_id t).prodMk (hX.2 y s t)
    have hcomp := hG.comp t hγ.hasFDerivAt
    simpa [γ, Function.uncurry, Function.comp_def] using hcomp.hasDerivAt
  have hgrad' : HasDerivAt
      (fun r => spaceGrad (T r) (X r y s) i)
      (D2.flip (0, basisVec i) (1, b t (X t y s))) t :=
    hcurve.congr_of_eventuallyEq hgrad
  have hsymm := hT.isSymmSndFDerivAt (by norm_num)
  have hderiv_formula :
      D2.flip (0, basisVec i) (1, b t (X t y s)) =
        D2 (0, basisVec i) (1, b t (X t y s)) := by
    simpa [D2, F, p] using hsymm (1, b t (X t y s)) (0, basisVec i)
  have hq_formula :
      ((fderiv ℝ F p).comp LV + D2.flip (V p))
          (0, basisVec i) =
        fderiv ℝ F p (LV (0, basisVec i)) +
          D2 (0, basisVec i) (1, b t (X t y s)) := by
    simp [D2, V, B, LV, p, Function.uncurry, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
  have hrate : D2.flip (0, basisVec i) (1, b t (X t y s)) =
      spaceGrad (materialDerivative T b t) (X t y s) i -
        fderiv ℝ F p (0, fderiv ℝ B p (0, basisVec i)) := by
    rw [hQgrad, hq_formula, hderiv_formula]
    simp [p, LV, sub_eq_add_neg]
  exact hgrad'.congr_deriv hrate

end AVenhance.Infra.Section5

end
