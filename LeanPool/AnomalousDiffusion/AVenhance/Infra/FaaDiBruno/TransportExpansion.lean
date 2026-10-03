/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.Definitions
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.GradientEstimates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.GradientMatrix
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportSolution.Characteristics
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.DirectionalProduct
public import Mathlib.Data.List.OfFn

/-! # Transport Expansion

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open scoped ContDiff

noncomputable section

namespace AVenhance.FaaDiBruno
open Homogenization

/-- All finite spatial jets of a smooth joint field remain jointly smooth. -/
theorem transportSpatialJet_contDiff (I : List (Vec 2))
    (F : ℝ × Vec 2 → Vec 2) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (transportSpatialJet I F) := by
  induction I with
  | nil => simpa [transportSpatialJet] using hF
  | cons v I ih =>
      change ContDiff ℝ ∞ (fun p =>
        fderiv ℝ (transportSpatialJet I F) p (0, v))
      have hderiv : ContDiff ℝ ∞ (fun p : ℝ × Vec 2 =>
          fderiv ℝ (transportSpatialJet I F) p) := ih.fderiv_right (by simp)
      exact hderiv.clm_apply (contDiff_const :
        ContDiff ℝ ∞ (fun _ : ℝ × Vec 2 => ((0 : ℝ), v)))

/-- Evaluating a joint space derivative in a spatial direction is the
ordinary derivative of the corresponding time slice. -/
theorem jointSpatialDirectionalDerivative_eq_slice
    (F : ℝ → Vec 2 → Vec 2) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (t : ℝ) (x v : Vec 2) :
    fderiv ℝ (Function.uncurry F) (t, x) (0, v) =
      fderiv ℝ (F t) x v := by
  have hslice := spatialDerivativeCLM_eq_slice
    (hF.of_le (by norm_num : (1 : ℕ) ≤ ∞)) t x
  have h := congrArg (fun A : Vec 2 →L[ℝ] Vec 2 => A v) hslice
  simpa [spatialDerivativeCLM] using h

/-- The recursively defined joint transport jet agrees with the ordinary
ordered derivative of the fixed-time slice. -/
theorem transportSpatialJet_eq_directionalJet_slice
    (I : List (Vec 2)) (F : ℝ → Vec 2 → Vec 2)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (t : ℝ) :
    (fun x => transportSpatialJet I (Function.uncurry F) (t, x)) =
      directionalJet I (F t) := by
  induction I with
  | nil => rfl
  | cons v I ih =>
      funext x
      change fderiv ℝ (transportSpatialJet I (Function.uncurry F))
        (t, x) (0, v) = _
      have hjet : ContDiff ℝ ∞
          (transportSpatialJet I (Function.uncurry F)) :=
        transportSpatialJet_contDiff I (Function.uncurry F) hF
      let J : ℝ → Vec 2 → Vec 2 := fun s y =>
        transportSpatialJet I (Function.uncurry F) (s, y)
      have hJ : ContDiff ℝ ∞ (Function.uncurry J) := by
        have hJ' : Function.uncurry J = transportSpatialJet I (Function.uncurry F) := by
          funext p
          exact congrArg (transportSpatialJet I (Function.uncurry F)) (Prod.eta p)
        rw [hJ']
        exact hjet
      calc
        _ = fderiv ℝ (J t) x v :=
          jointSpatialDirectionalDerivative_eq_slice J hJ t x v
        _ = fderiv ℝ (directionalJet I (F t)) x v := by
          change fderiv ℝ
            (fun y => transportSpatialJet I (Function.uncurry F) (t, y)) x v = _
          rw [ih]
        _ = directionalJet (v :: I) (F t) x := rfl

theorem TransportExpansion.directionalJet_clm_apply {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (I : List E) (c : E → E →L[ℝ] F) (hc : ContDiff ℝ ∞ c) (v : E) :
    directionalJet I (fun x => c x v) = fun x => directionalJet I c x v := by
  induction I with
  | nil => rfl
  | cons w I ih =>
      funext x
      change fderiv ℝ (directionalJet I (fun x => c x v)) x w = _
      rw [ih]
      have hsmooth := directionalJet_contDiff I c hc
      have hdiff : DifferentiableAt ℝ (directionalJet I c) x :=
        (hsmooth.of_le (by norm_num : (1 : ℕ) ≤ ∞)).differentiable_one x
      have hconst : DifferentiableAt ℝ (fun _ : E => v) x := differentiableAt_const v
      have h := fderiv_clm_apply hdiff hconst
      have happly := congrArg (fun A : E →L[ℝ] F => A w) h
      change fderiv ℝ (fun x => (directionalJet I c x) v) x w =
        fderiv ℝ (directionalJet I c) x w v
      simpa [fderiv_const_apply] using happly

theorem TransportExpansion.iteratedFDeriv_apply_directionalJet {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (F : Type)
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F)
    (hf : ContDiff ℝ ∞ f) (x : E) (I : Fin n → E) :
    iteratedFDeriv ℝ n f x I = directionalJet (List.ofFn I) f x := by
  induction n generalizing F f with
  | zero => simp [directionalJet]
  | succ n ih =>
      let J : Fin n → E := fun i => I i.castSucc
      let v : E := I (Fin.last n)
      have hfderiv : ContDiff ℝ ∞ (fun y => fderiv ℝ f y) :=
        hf.fderiv_right (m := ∞) (by simp)
      have hIH := ih (E →L[ℝ] F) (fun y => fderiv ℝ f y) hfderiv J
      have hEval := TransportExpansion.directionalJet_clm_apply (List.ofFn J)
        (fun y => fderiv ℝ f y) hfderiv v
      have hlist : List.ofFn I = List.ofFn J ++ [v] := by
        rw [List.ofFn_succ']
        simp [J, v, List.concat_eq_append]
      calc
        iteratedFDeriv ℝ (n + 1) f x I =
            iteratedFDeriv ℝ n (fun y => fderiv ℝ f y) x J v := by
              rw [iteratedFDeriv_succ_apply_right]
              rfl
        _ = directionalJet (List.ofFn J) (fun y => fderiv ℝ f y) x v := by
              rw [hIH]
        _ = directionalJet (List.ofFn J) (fun y => fderiv ℝ f y v) x := by
              symm
              exact congrFun hEval x
        _ = directionalJet (List.ofFn J ++ [v]) f x := by
              rw [directionalJet_append]
              rfl
        _ = directionalJet (List.ofFn I) f x := by rw [hlist]

theorem TransportExpansion.directionalJet_comp_linear {E F G : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (I : List E) (f : F → G) (hf : ContDiff ℝ ∞ f)
    (L : E →L[ℝ] F) (x : E) :
    directionalJet I (f ∘ L) x =
      directionalJet (I.map L) f (L x) := by
  induction I generalizing x with
  | nil => rfl
  | cons v I ih =>
      have hjet : ContDiff ℝ ∞ (directionalJet (I.map L) f) :=
        directionalJet_contDiff (I.map L) f hf
      have hcomp := (hjet.differentiable (by simp) (L x)).hasFDerivAt.comp x
        L.hasFDerivAt
      have hfun : directionalJet I (f ∘ L) =
          fun z => directionalJet (I.map L) f (L z) := by
        funext z
        exact ih z
      change fderiv ℝ (directionalJet I (f ∘ L)) x v =
        fderiv ℝ (directionalJet (I.map L) f) (L x) (L v)
      rw [hfun]
      change fderiv ℝ (directionalJet (I.map L) f ∘ L) x v = _
      rw [hcomp.fderiv]
      rfl

/-- The paper's ordered coordinate partial is the ordinary directional jet
along the corresponding coordinate vectors on `Vec d`. -/
theorem orderedPartial_eq_directionalJet {d n : ℕ} {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec d → F) (hf : ContDiff ℝ ∞ f) (x : Vec d)
    (I : Fin n → Fin d) :
    orderedPartial n f x I =
      directionalJet (List.ofFn (fun j => coordinateVector d (I j))) f x := by
  let L : VecOne d →L[ℝ] Vec d := (vecOneEquiv d).toContinuousLinearMap
  let z : VecOne d := WithLp.toLp 1 x
  have hlift : ContDiff ℝ ∞ (liftVecOne f) := by
    dsimp [liftVecOne]
    exact hf.comp_continuousLinearMap
      (g := (vecOneEquiv d).toContinuousLinearMap)
  have hpartial := TransportExpansion.iteratedFDeriv_apply_directionalJet n F
    (liftVecOne f) hlift z (fun j => coordinateVectorOne d (I j))
  have hdirections : (List.ofFn (fun j => coordinateVectorOne d (I j))).map L =
      List.ofFn (fun j => coordinateVector d (I j)) := by
    rw [← List.ofFn_comp']
    apply congrArg List.ofFn
    funext j
    change vecOneEquiv d (coordinateVectorOne d (I j)) =
      coordinateVector d (I j)
    ext k
    by_cases hkj : k = I j <;> simp [vecOneEquiv, coordinateVectorOne,
      coordinateVector, hkj]
  have hpoint : vecOneEquiv d z = x := by
    simp [z, vecOneEquiv, PiLp.coe_continuousLinearEquiv]
  have hpointL : L z = x := hpoint
  have hjet := TransportExpansion.directionalJet_comp_linear
    (List.ofFn (fun j => coordinateVectorOne d (I j))) f hf L z
  rw [hdirections, hpointL] at hjet
  rw [orderedPartial, hpartial]
  simpa [liftVecOne, L] using hjet

end AVenhance.FaaDiBruno

end
