/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Flow.IsFlow
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Chain rules for the transport identities in Section 5.1. -/

@[expose] public section

open Homogenization

namespace AVenhance.Infra.Section5

/-- Differentiate a smooth scalar field along a spacetime curve. -/
theorem deriv_uncurry_comp {F : ℝ → Vec 2 → ℝ} {γ : ℝ → ℝ × Vec 2}
    {t : ℝ} {v : ℝ × Vec 2}
    {L : (ℝ × Vec 2) →L[ℝ] ℝ}
    (hF : HasFDerivAt (Function.uncurry F) L (γ t))
    (hγ : HasDerivAt γ v t) :
    deriv (fun s => Function.uncurry F (γ s)) t =
      L v := by
  have hcomp := hF.comp_hasDerivAt t hγ
  exact hcomp.deriv

/-- The derivative of `F` pulled back by a forward flow, in spacetime
Fréchet-derivative form. -/
theorem deriv_comp_flow {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    {F : ℝ → Vec 2 → ℝ} {t s : ℝ} {x : Vec 2}
    {v : (ℝ × Vec 2) →L[ℝ] ℝ}
    (hF : HasFDerivAt (Function.uncurry F)
      v (t, X t x s))
    (hX : IsFlow b X) :
    deriv (fun r => F r (X r x s)) t =
      v (1, b t (X t x s)) := by
  let γ : ℝ → ℝ × Vec 2 := fun r => (r, X r x s)
  have hγ : HasDerivAt γ (1, b t (X t x s)) t := by
    exact (hasDerivAt_id t).prodMk (hX.2 x s t)
  have hcomp := hF.comp_hasDerivAt t hγ
  simpa [γ, Function.uncurry, Function.comp_def] using hcomp.deriv

/-- Transport calculus for composition with a time-dependent inverse map. The
inverse transport equation is the single cancellation hypothesis
`∂ₜZ + DₓZ b = 0`; all composition and product rules are proved here. -/
theorem inverse_transport_comp
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    {Z : ℝ → Vec 2 → Vec 2}
    {t : ℝ} {x z : Vec 2} {v : Vec 2}
    {L : (ℝ × Vec 2) →L[ℝ] ℝ} {A : Vec 2 →L[ℝ] Vec 2}
    (hF : HasFDerivAt (Function.uncurry F) L (t, z))
    (hZtime : HasDerivAt (fun s => Z s x) v t)
    (hZspace : HasFDerivAt (Z t) A x)
    (hz : Z t x = z)
    (htransport : v + A (b t x) = 0) :
    deriv (fun s => F s (Z s x)) t +
        fderiv ℝ (fun y => F t (Z t y)) x (b t x) =
      L (1, (0 : Vec 2)) := by
  let γ : ℝ → ℝ × Vec 2 := fun s => (s, Z s x)
  have hγ : HasDerivAt γ (1, v) t := by
    exact (hasDerivAt_id t).prodMk hZtime
  have hpoint : (t, z) = γ t := by simp [γ, hz]
  have hcurve : HasDerivAt (fun s => Function.uncurry F (γ s))
      (L (1, v)) t := by
    simpa [γ, Function.uncurry, Function.comp_def] using
      hF.comp_hasDerivAt_of_eq t hγ hpoint
  have htime : deriv (fun s => F s (Z s x)) t = L (1, v) := by
    simpa [Function.uncurry] using hcurve.deriv
  let J : Vec 2 →L[ℝ] ℝ × Vec 2 :=
    (0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))
  have hinj : HasFDerivAt (fun y : Vec 2 => (t, y)) J z := by
    exact (hasFDerivAt_const t z).prodMk (hasFDerivAt_id z)
  have hinj' : HasFDerivAt (fun y : Vec 2 => (t, y)) J (Z t x) := by
    simpa [hz] using hinj
  have hZcomp : HasFDerivAt (fun y : Vec 2 => (t, Z t y)) (J.comp A) x := by
    simpa [J, Function.comp_def] using hinj'.comp x hZspace
  have hF' : HasFDerivAt (Function.uncurry F) L (t, Z t x) := by
    simpa [hz] using hF
  have hFcomp : HasFDerivAt (fun y : Vec 2 => F t (Z t y))
      (L.comp (J.comp A)) x := by
    simpa [Function.uncurry, Function.comp_def] using hF'.comp x hZcomp
  have hspace :
      fderiv ℝ (fun y => F t (Z t y)) x (b t x) = L (0, A (b t x)) := by
    calc
      fderiv ℝ (fun y => F t (Z t y)) x (b t x) =
          (L.comp (J.comp A)) (b t x) := by rw [hFcomp.fderiv]
      _ = L (0, A (b t x)) := by simp [J]
  calc
    deriv (fun s => F s (Z s x)) t +
        fderiv ℝ (fun y => F t (Z t y)) x (b t x) =
      L (1, v) + L (0, A (b t x)) := by rw [htime, hspace]
    _ = L ((1, v) + (0, A (b t x))) := by rw [← L.map_add]
    _ = L (1, (0 : Vec 2)) := by simp [htransport]

/-- The inverse-flow transport formula, derived from the forward ODE and the
two inverse identities. Smoothness of the inverse map is stated as a Fréchet
derivative hypothesis so this bridge can be instantiated independently of a
particular flow regularity theorem. -/
theorem inverse_flow_transport_comp
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    {Z : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    {s t : ℝ} {x : Vec 2}
    {L : (ℝ × Vec 2) →L[ℝ] ℝ}
    {M : (ℝ × Vec 2) →L[ℝ] Vec 2}
    (hF : HasFDerivAt (Function.uncurry F) L (t, Z t x))
    (hZ : HasFDerivAt (Function.uncurry Z) M (t, x))
    (hX : IsFlow b X)
    (hleft : ∀ r y, Z r (X r y s) = y)
    (hright : ∀ r y, X r (Z r y) s = y) :
    deriv (fun r => F r (Z r x)) t +
        fderiv ℝ (fun y => F t (Z t y)) x (b t x) =
      L (1, (0 : Vec 2)) := by
  let J : Vec 2 →L[ℝ] ℝ × Vec 2 :=
    (0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2))
  let v : Vec 2 := M (1, (0 : Vec 2))
  let A : Vec 2 →L[ℝ] Vec 2 := M.comp J
  have htime : HasDerivAt (fun r => Z r x) v t := by
    let γ : ℝ → ℝ × Vec 2 := fun r => (r, x)
    have hγ : HasDerivAt γ (1, (0 : Vec 2)) t := by
      exact (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    have h := hZ.comp_hasDerivAt t hγ
    simpa [γ, v, Function.uncurry, Function.comp_def] using h
  have hspace : HasFDerivAt (fun y => Z t y) A x := by
    have hpair : HasFDerivAt (fun y : Vec 2 => (t, y)) J x := by
      exact (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
    have h := hZ.comp x hpair
    simpa [A, J, Function.uncurry, Function.comp_def] using h
  let y : Vec 2 := Z t x
  have hx : X t y s = x := by
    simpa [y] using hright t x
  have hcurve : HasDerivAt (fun r => X r y s) (b t x) t := by
    simpa [hx] using hX.2 y s t
  have hγ : HasDerivAt (fun r : ℝ => (r, X r y s)) (1, b t x) t := by
    exact (hasDerivAt_id t).prodMk hcurve
  have hZat : HasFDerivAt (Function.uncurry Z) M
      (t, X t y s) := by
    simpa [hx] using hZ
  have hconstDeriv :
      deriv (fun r => Z r (X r y s)) t = M (1, b t x) := by
    have h := hZat.comp_hasDerivAt t hγ
    simpa [Function.uncurry, Function.comp_def] using h.deriv
  have hconstant : (fun r => Z r (X r y s)) = fun _ => y := by
    funext r
    exact hleft r y
  have hMzero : M (1, b t x) = 0 := by
    rw [hconstant] at hconstDeriv
    simpa using hconstDeriv.symm
  have htransport : v + A (b t x) = 0 := by
    have hpair : ((1 : ℝ), b t x) = (1, (0 : Vec 2)) + (0, b t x) := by
      ext <;> simp
    have hsplit : M (1, b t x) = v + A (b t x) := by
      calc
        M (1, b t x) = M ((1, (0 : Vec 2)) + (0, b t x)) := by
          exact congrArg M hpair
        _ = M (1, (0 : Vec 2)) + M (0, b t x) := map_add M _ _
        _ = v + A (b t x) := by simp [v, A, J]
    rw [hsplit] at hMzero
    exact hMzero
  exact inverse_transport_comp hF htime hspace (rfl) htransport

/-- Coordinate form of the inverse-flow transport formula for a vector field.
This is the form used for the pulled gradient in `e.tbm1.two`. -/
theorem inverse_flow_transport_comp_apply
    {b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2}
    {Z : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → Vec 2}
    {s t : ℝ} {x : Vec 2}
    {L : (ℝ × Vec 2) →L[ℝ] Vec 2}
    {M : (ℝ × Vec 2) →L[ℝ] Vec 2}
    (hF : HasFDerivAt (Function.uncurry F) L (t, Z t x))
    (hZ : HasFDerivAt (Function.uncurry Z) M (t, x))
    (hX : IsFlow b X)
    (hleft : ∀ r y, Z r (X r y s) = y)
    (hright : ∀ r y, X r (Z r y) s = y)
    (i : Fin 2) :
    deriv (fun r => F r (Z r x) i) t +
        fderiv ℝ (fun y => F t (Z t y) i) x (b t x) =
      L (1, (0 : Vec 2)) i := by
  let P : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hproj : HasFDerivAt (fun y : Vec 2 => y i)
      P (F t (Z t x)) := by
    change HasFDerivAt (fun y => P y) P (F t (Z t x))
    exact P.hasFDerivAt
  have hFi : HasFDerivAt
      (Function.uncurry fun r y => F r y i)
      (P.comp L) (t, Z t x) := by
    convert hproj.comp (t, Z t x) hF using 1; rfl
  have hcoord := inverse_flow_transport_comp (b := b) (X := X)
    (Z := Z) (F := fun r y => F r y i) (s := s) (t := t) (x := x)
    hFi hZ hX hleft hright
  simpa [Function.uncurry, Function.comp_def, P] using hcoord

end AVenhance.Infra.Section5
