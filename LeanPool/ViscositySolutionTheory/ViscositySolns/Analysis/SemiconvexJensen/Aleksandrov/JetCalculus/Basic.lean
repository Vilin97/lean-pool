/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.Basic.Core

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Basic second-order jet calculus
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped ENNReal

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}

/--
The superjet part of a second-order jet belongs to the closed superjet.
-/
theorem HasSecondOrderJet.closedSuperjet
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (h : HasSecondOrderJet f x p X) :
    ({ gradient := p, hessian := X } : Jet n) ∈ ClosedSuperjet Set.univ f x :=
  superjet_subset_closedSuperjet (C := Set.univ) (x := x) trivial h.1

/--
The subjet part of a second-order jet belongs to the closed subjet.
-/
theorem HasSecondOrderJet.closedSubjet
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (h : HasSecondOrderJet f x p X) :
    ({ gradient := p, hessian := X } : Jet n) ∈ ClosedSubjet Set.univ f x :=
  subjet_subset_closedSubjet (C := Set.univ) (x := x) trivial h.2

/--
A linear function has its expected second-order expansion at every point.

In quantified mathematical form, for every `q : R^n`, the function
`x ↦ q · x` has gradient `q` and Hessian `0` at every point.
-/
theorem hasSecondOrderExpansionWithin_linear
    {C : Set (Point n)} (q : Point n) (x : Point n) :
    HasSecondOrderExpansionWithin C (fun y : Point n => dotProduct q y) x
      ({ gradient := q, hessian := 0 } : Jet n) := by
  have h :=
    hasSecondOrderExpansionWithin_quadraticModel_recenter
      (C := C) (x0 := 0) (r := 0) (p := q) (X := (0 : Hessian n)) x
  simpa [quadraticModel, quadraticModelJetAt] using h

/--
If `f + q · x` has a second-order jet at `x`, then subtracting the linear jet
gives a second-order jet of `f` at `x`.
-/
theorem HasSecondOrderJet.of_linearPerturbation
    {f : Point n -> Real} {x p q : Point n} {X : Hessian n}
    (h : HasSecondOrderJet (linearPerturbation f q) x p X) :
    HasSecondOrderJet f x (p - q) X := by
  have hjet :
      ({ gradient := p, hessian := X } : Jet n) -
          ({ gradient := q, hessian := 0 } : Jet n) =
        ({ gradient := p - q, hessian := X } : Jet n) := by
    apply (Jet.equivProd n).injective
    simp [Jet.equivProd]
  constructor
  · have hsuper :=
      superjet_sub_of_add_hasSecondOrderExpansionWithin
        (C := Set.univ) (u := f) (φ := fun y : Point n => dotProduct q y)
        (x := x) (J := ({ gradient := p, hessian := X } : Jet n))
        h.1 (hasSecondOrderExpansionWithin_linear (C := Set.univ) q x)
    simpa [linearPerturbation, hjet] using hsuper
  · have hsub :=
      subjet_sub_of_add_hasSecondOrderExpansionWithin
        (C := Set.univ) (u := f) (φ := fun y : Point n => dotProduct q y)
        (x := x) (J := ({ gradient := p, hessian := X } : Jet n))
        h.2 (hasSecondOrderExpansionWithin_linear (C := Set.univ) q x)
    simpa [linearPerturbation, hjet] using hsub

/--
If `f` has a second-order jet at `x`, then `f + q · x` has the corresponding
second-order jet with gradient shifted by `q`.
-/
theorem HasSecondOrderJet.linearPerturbation
    {f : Point n -> Real} {x p q : Point n} {X : Hessian n}
    (h : HasSecondOrderJet f x p X) :
    HasSecondOrderJet (linearPerturbation f q) x (p + q) X := by
  have hjet :
      ({ gradient := p, hessian := X } : Jet n) +
          ({ gradient := q, hessian := 0 } : Jet n) =
        ({ gradient := p + q, hessian := X } : Jet n) := by
    apply (Jet.equivProd n).injective
    simp [Jet.equivProd]
  constructor
  · have hsuper :=
      superjet_add_hasSecondOrderExpansionWithin
        (C := Set.univ) (u := f) (φ := fun y : Point n => dotProduct q y)
        (x := x) (J := ({ gradient := p, hessian := X } : Jet n))
        h.1 (hasSecondOrderExpansionWithin_linear (C := Set.univ) q x)
    unfold ViscositySolns.linearPerturbation
    simpa [hjet] using hsuper
  · have hsub :=
      subjet_add_hasSecondOrderExpansionWithin
        (C := Set.univ) (u := f) (φ := fun y : Point n => dotProduct q y)
        (x := x) (J := ({ gradient := p, hessian := X } : Jet n))
        h.2 (hasSecondOrderExpansionWithin_linear (C := Set.univ) q x)
    unfold ViscositySolns.linearPerturbation
    simpa [hjet] using hsub

/--
Subtracting the quadratic function used for semiconvex convexification
converts a two-sided jet of the convexified function into a two-sided jet of
the original function.

In quantified mathematical form, if
`g(x) = f(x) + (lambda / 2) * ∑ i, x_i^2` and `(p, X)` is an ordinary
two-sided second-order jet of `g` at `x`, then subtracting the first and
second derivatives of `(lambda / 2) * ∑ i, x_i^2` at `x` gives an ordinary
two-sided second-order jet of `f` at `x`.
-/
theorem HasSecondOrderJet.of_semiconvexConvexification
    {lambda : Real} {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (h : HasSecondOrderJet (semiconvexConvexification lambda f) x p X) :
    HasSecondOrderJet f x
      (({ gradient := p, hessian := X } : Jet n) -
        quadraticModelJetAt 0 0 (lambda • (1 : Hessian n)) x).gradient
      (({ gradient := p, hessian := X } : Jet n) -
        quadraticModelJetAt 0 0 (lambda • (1 : Hessian n)) x).hessian := by
  let Q : Point n -> Real :=
    fun y => quadraticModel 0 0 0 (lambda • (1 : Hessian n)) y
  let A : Jet n := quadraticModelJetAt 0 0 (lambda • (1 : Hessian n)) x
  constructor
  · have hsuper :
        ({ gradient := p, hessian := X } : Jet n) - A ∈ Superjet Set.univ f x :=
      superjet_sub_of_add_hasSecondOrderExpansionWithin
        (C := Set.univ) (u := f) (φ := Q) (x := x)
        (J := ({ gradient := p, hessian := X } : Jet n))
        (A := A)
        h.1
        (by
          simpa [Q, A] using
            hasSecondOrderExpansionWithin_quadraticModel_recenter
              (C := Set.univ) (x0 := 0) (r := 0) (p := 0)
              (X := lambda • (1 : Hessian n)) x)
    exact hsuper
  · have hsub :
        ({ gradient := p, hessian := X } : Jet n) - A ∈ Subjet Set.univ f x :=
      subjet_sub_of_add_hasSecondOrderExpansionWithin
        (C := Set.univ) (u := f) (φ := Q) (x := x)
        (J := ({ gradient := p, hessian := X } : Jet n))
        (A := A)
        h.2
        (by
          simpa [Q, A] using
            hasSecondOrderExpansionWithin_quadraticModel_recenter
              (C := Set.univ) (x0 := 0) (r := 0) (p := 0)
              (X := lambda • (1 : Hessian n)) x)
    exact hsub

/--
Existential form of the semiconvex-to-convex reduction for two-sided jets.

This is the jet-level version of the source proof's reduction from a
semiconvex function to its convexification by adding a quadratic.
-/
theorem HasSomeSecondOrderJet.of_semiconvexConvexification
    {lambda : Real} {f : Point n -> Real} {x : Point n}
    (h : HasSomeSecondOrderJet (semiconvexConvexification lambda f) x) :
    HasSomeSecondOrderJet f x := by
  rcases h with ⟨p, X, hHerm, hJet⟩
  let QJet : Jet n := quadraticModelJetAt 0 0 (lambda • (1 : Hessian n)) x
  refine
    ⟨(({ gradient := p, hessian := X } : Jet n) - QJet).gradient,
      (({ gradient := p, hessian := X } : Jet n) - QJet).hessian, ?_, ?_⟩
  · have hlambdaI : (lambda • (1 : Hessian n)).IsHermitian :=
      Matrix.isHermitian_one.smul (IsSelfAdjoint.all lambda)
    simpa [QJet, quadraticModelJetAt] using hHerm.sub hlambdaI
  · simpa [QJet] using hJet.of_semiconvexConvexification (lambda := lambda)

/--
If `(p, X)` belongs both to the ordinary superjet and to the ordinary subjet
of `f` at `x`, then `f` has the corresponding second-order expansion at `x`.

In quantified mathematical form, there exists a function `ρ` such that
`ρ(y) = o(|y - x|^2)` as `y -> x` and, for all `y` sufficiently close to
`x`,

`f y = f x + p · (y - x) + (1 / 2) * ⟪X (y - x), y - x⟫ + ρ y`.
-/
theorem HasSecondOrderJet.hasSecondOrderExpansionWithin
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (h : HasSecondOrderJet f x p X) :
    HasSecondOrderExpansionWithin Set.univ f x
      ({ gradient := p, hessian := X } : Jet n) := by
  rcases h.1 with ⟨rhoSuper, hrhoSuper, hsuper⟩
  rcases h.2 with ⟨rhoSub, hrhoSub, hsub⟩
  let R : Point n -> Real := fun y =>
    f y - quadraticModel x (f x) p X y
  refine ⟨R, ?_, ?_⟩
  · refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
    have hsuperBound := hrhoSuper.bound hc
    have hsubBound := hrhoSub.bound hc
    filter_upwards [hsuper, hsub, hsuperBound, hsubBound] with
      y hsuperY hsubY hsuperB hsubB
    have hsuperBsq : ‖rhoSuper y‖ <= c * ‖y - x‖ ^ 2 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖y - x‖))] using hsuperB
    have hsubBsq : ‖rhoSub y‖ <= c * ‖y - x‖ ^ 2 := by
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖y - x‖))] using hsubB
    have hR_le : R y <= rhoSuper y := by
      dsimp [R] at hsuperY ⊢
      linarith
    have hrhoSub_le_R : rhoSub y <= R y := by
      dsimp [R] at hsubY ⊢
      linarith
    have hR_upper : R y <= c * ‖y - x‖ ^ 2 := by
      have hρ : rhoSuper y <= ‖rhoSuper y‖ := by
        simpa [Real.norm_eq_abs] using le_abs_self (rhoSuper y)
      linarith
    have hR_lower : - (c * ‖y - x‖ ^ 2) <= R y := by
      have hρ : - (‖rhoSub y‖) <= rhoSub y := by
        simpa [Real.norm_eq_abs] using neg_abs_le (rhoSub y)
      linarith
    have habs : |R y| <= c * ‖y - x‖ ^ 2 := abs_le.mpr ⟨hR_lower, hR_upper⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖y - x‖))] using habs
  · filter_upwards with y
    dsimp [R]
    ring

/--
The restriction of a quadratic model to a line through its base point.

In quantified mathematical form, for every `t : R` and every vector `v`,

`quadraticModel x r p X (x + t v)
 = r + t * p · v + (t^2 / 2) * ⟪X v, v⟫`.
-/
theorem quadraticModel_line (x : Point n) (r t : Real) (p v : Point n) (X : Hessian n) :
    quadraticModel x r p X (x + t • v) =
      r + t * dotProduct p v + (1 / 2 : Real) * t ^ 2 * dotProduct (Matrix.mulVec X v) v := by
  have hdx : x + t • v - x = t • v := by
    ext i
    simp
  simp [quadraticModel, hdx, dotProduct_smul, Matrix.mulVec_smul, smul_dotProduct]
  ring

/--
The quadratic part of a fixed Hessian is bounded by a constant multiple of
`|y - x|^2` near `x`.

In quantified mathematical form, for every matrix `X`, the function
`y ↦ (1 / 2) * ⟪X (y - x), y - x⟫` is `O(|y - x|^2)` as `y -> x`.
-/
theorem quadraticModel_zero_zero_isBigO_norm_sq (x : Point n) (X : Hessian n) :
    (fun y : Point n => quadraticModel x 0 0 X y) =O[𝓝 x]
      (fun y : Point n => ‖y - x‖ ^ 2) := by
  let eta : Real := ∑ i : Fin n, ∑ j : Fin n, |X i j|
  have heta_nonneg : 0 <= eta := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg (X i j)
  have hentry : ∀ i j : Fin n, |X i j| <= eta := by
    intro i j
    calc
      |X i j| <= ∑ j : Fin n, |X i j| := by
        exact Finset.single_le_sum (fun k _ => abs_nonneg (X i k)) (Finset.mem_univ j)
      _ <= eta := by
        exact Finset.single_le_sum
          (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg (X k l))
          (Finset.mem_univ i)
  refine Asymptotics.IsBigO.of_bound ((1 / 2 : Real) * eta * (n : Real) * (n : Real)) ?_
  filter_upwards with y
  have h := abs_quadraticModel_zero_zero_le_of_entrywise_abs_le x y heta_nonneg hentry
  simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖y - x‖))] using h

/--
The quadratic part of a fixed Hessian is first-order negligible at its base
point.

In quantified mathematical form, for every matrix `X`,

`(1 / 2) * ⟪X (y - x), y - x⟫ = o(|y - x|)`

as `y -> x`.
-/
theorem quadraticModel_zero_zero_isLittleO_sub (x : Point n) (X : Hessian n) :
    (fun y : Point n => quadraticModel x 0 0 X y) =o[𝓝 x]
      (fun y : Point n => y - x) := by
  have hquad := quadraticModel_zero_zero_isBigO_norm_sq (n := n) x X
  have hsquare : (fun y : Point n => ‖y - x‖ ^ 2) =o[𝓝 x]
      (fun y : Point n => y - x) := by
    have h0 : (fun h : Point n => ‖h‖ ^ 2) =o[𝓝 0] (fun h : Point n => h) :=
      Asymptotics.isLittleO_norm_pow_id (E' := Point n) (n := 2) (by norm_num : 1 < 2)
    have htend : Filter.Tendsto (fun y : Point n => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (continuous_sub_right x).tendsto x
    exact h0.comp_tendsto htend
  exact hquad.trans_isLittleO hsquare

/--
A second-order expansion gives the corresponding first Fréchet derivative.

In quantified mathematical form, if

`f y = f x + p · (y - x) + (1 / 2) * ⟪X (y - x), y - x⟫ + o(|y - x|^2)`

as `y -> x`, then the Fréchet derivative of `f` at `x` is the linear map
`h ↦ p · h`.
-/
theorem HasSecondOrderExpansionWithin.hasFDerivAt
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (h : HasSecondOrderExpansionWithin Set.univ f x
      ({ gradient := p, hessian := X } : Jet n)) :
    HasFDerivAt f (gradientLinearMap p) x := by
  rcases h with ⟨rho, hrho, heq⟩
  rw [hasFDerivAt_iff_isLittleO]
  have hquad : (fun y : Point n => quadraticModel x 0 0 X y) =o[𝓝 x]
      (fun y : Point n => y - x) :=
    quadraticModel_zero_zero_isLittleO_sub x X
  have hsquare : (fun y : Point n => ‖y - x‖ ^ 2) =o[𝓝 x]
      (fun y : Point n => y - x) := by
    have h0 : (fun h : Point n => ‖h‖ ^ 2) =o[𝓝 0] (fun h : Point n => h) :=
      Asymptotics.isLittleO_norm_pow_id (E' := Point n) (n := 2) (by norm_num : 1 < 2)
    have htend : Filter.Tendsto (fun y : Point n => y - x) (𝓝 x) (𝓝 0) := by
      simpa using (continuous_sub_right x).tendsto x
    exact h0.comp_tendsto htend
  have hrho_nhds : rho =o[𝓝 x] (fun y : Point n => ‖y - x‖ ^ 2) := by
    simpa [SemijetRemainder, nhdsWithin_univ] using hrho
  have hrho_first : rho =o[𝓝 x] (fun y : Point n => y - x) :=
    hrho_nhds.trans hsquare
  have hsum : (fun y : Point n => quadraticModel x 0 0 X y + rho y) =o[𝓝 x]
      (fun y : Point n => y - x) :=
    hquad.add hrho_first
  have hevent : (fun y : Point n => f y - f x - gradientLinearMap p (y - x)) =ᶠ[𝓝 x]
      (fun y : Point n => quadraticModel x 0 0 X y + rho y) := by
    have heq_nhds : ∀ᶠ y in 𝓝 x,
        f y = quadraticModel x (f x) p X y + rho y := by
      simpa [nhdsWithin_univ] using heq
    filter_upwards [heq_nhds] with y hy
    rw [hy]
    simp [quadraticModel, gradientLinearMap_apply]
    ring
  exact hevent.trans_isLittleO hsum

/--
At a local maximum point, the gradient component of a two-sided ordinary jet
is zero.

In quantified mathematical form, if `f` has a local maximum at `x` and
`(p, X)` belongs both to the ordinary superjet and the ordinary subjet of `f`
at `x`, then `p = 0`.
-/
theorem HasSecondOrderJet.gradient_eq_zero_of_isLocalMax
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (hmax : IsLocalMax f x) (h : HasSecondOrderJet f x p X) :
    p = 0 := by
  have hfderiv : HasFDerivAt f (gradientLinearMap p) x :=
    h.hasSecondOrderExpansionWithin.hasFDerivAt
  have hzero : gradientLinearMap p = 0 :=
    hmax.hasFDerivAt_eq_zero hfderiv
  have hgrad := congrArg linearMapGradient hzero
  rw [linearMapGradient_gradientLinearMap] at hgrad
  rw [hgrad]
  ext i
  simp

/--
At a local maximum point, the quadratic form determined by the Hessian
component of a two-sided ordinary jet is nonpositive in every direction.

In quantified mathematical form, if `f` has a local maximum at `x` and
`(p, X)` belongs both to the ordinary superjet and to the ordinary subjet of
`f` at `x`, then for every `v : R^n`,
`⟪X v, v⟫ ≤ 0`.
-/
theorem HasSecondOrderJet.quadraticForm_nonpos_of_isLocalMax
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (hmax : IsLocalMax f x) (h : HasSecondOrderJet f x p X) (v : Point n) :
    dotProduct (Matrix.mulVec X v) v <= 0 := by
  by_cases hv : v = 0
  · simp [hv]
  by_contra hnot
  have hQpos : 0 < dotProduct (Matrix.mulVec X v) v := lt_of_not_ge hnot
  let Q : Real := dotProduct (Matrix.mulVec X v) v
  have hQpos' : 0 < Q := hQpos
  have hp : p = 0 := h.gradient_eq_zero_of_isLocalMax hmax
  rcases h.hasSecondOrderExpansionWithin with ⟨rho, hrho, heq⟩
  let line : Real -> Point n := fun t => x + t • v
  have hline_nhds : Filter.Tendsto line (𝓝 (0 : Real)) (𝓝 x) := by
    have hcont :
        ContinuousAt (fun t : Real => x + t • v) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    simpa [line, ContinuousAt] using hcont
  have hline_right : Filter.Tendsto line (𝓝[>] (0 : Real)) (𝓝 x) :=
    hline_nhds.mono_left nhdsWithin_le_nhds
  have hline_event :
      ∀ᶠ t in 𝓝[>] (0 : Real), f (line t) =
        quadraticModel x (f x) p X (line t) + rho (line t) := by
    have heq_nhds :
        ∀ᶠ y in 𝓝 x, f y = quadraticModel x (f x) p X y + rho y := by
      simpa [nhdsWithin_univ] using heq
    exact hline_right.eventually heq_nhds
  have hmax_line :
      ∀ᶠ t in 𝓝[>] (0 : Real), f (line t) <= f x :=
    hline_right.eventually hmax
  have hnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hnorm_sq_pos : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hnorm_pos
  let c : Real := Q / (4 * ‖v‖ ^ 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hrho_bound :
      ∀ᶠ t in 𝓝[>] (0 : Real),
        ‖rho (line t)‖ <= c * ‖line t - x‖ ^ 2 := by
    have hrho_nhds :
        ∀ᶠ y in 𝓝 x, ‖rho y‖ <= c * ‖y - x‖ ^ 2 := by
      simpa [SemijetRemainder, nhdsWithin_univ] using hrho.bound hc
    exact hline_right.eventually hrho_nhds
  have hcontra_event : ∀ᶠ t in 𝓝[>] (0 : Real), False := by
    filter_upwards [self_mem_nhdsWithin, hline_event, hmax_line, hrho_bound] with
      t htpos hlineEq hlineMax hrhoB
    have hline_def : line t = x + t • v := rfl
    have hnorm_line : ‖line t - x‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
      have hsub : line t - x = t • v := by
        ext i
        simp [line]
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      ring
    have hquad_line :
        quadraticModel x (f x) p X (line t) =
          f x + (1 / 2 : Real) * t ^ 2 * Q := by
      calc
        quadraticModel x (f x) p X (line t)
            = quadraticModel x (f x) p X (x + t • v) := rfl
        _ = f x + t * dotProduct p v + (1 / 2 : Real) * t ^ 2 * Q := by
          simpa [Q] using quadraticModel_line x (f x) t p v X
        _ = f x + (1 / 2 : Real) * t ^ 2 * Q := by
          simp [hp]
    have hrho_lower : - ((1 / 4 : Real) * t ^ 2 * Q) <= rho (line t) := by
      have habs_lower : - ‖rho (line t)‖ <= rho (line t) := by
        simpa [Real.norm_eq_abs] using neg_abs_le (rho (line t))
      have hboundQ :
          c * ‖line t - x‖ ^ 2 = (1 / 4 : Real) * t ^ 2 * Q := by
        rw [hnorm_line]
        dsimp [c]
        field_simp [ne_of_gt hnorm_sq_pos]
      linarith
    have hpositive :
        0 < (1 / 4 : Real) * t ^ 2 * Q := by
      have ht_sq_pos : 0 < t ^ 2 := sq_pos_of_pos htpos
      positivity
    have hvalue_lower :
        f x + (1 / 4 : Real) * t ^ 2 * Q <= f (line t) := by
      rw [hlineEq, hquad_line]
      linarith
    linarith
  rcases Filter.Eventually.exists hcontra_event with ⟨_, hfalse⟩
  exact hfalse

/--
If `f` has a strict local maximum at `x0`, then `f` has a local maximum at
`x0`.

In quantified mathematical form, this says: if there is a neighborhood `U` of
`x0` such that every `x ∈ U` with `x ≠ x0` satisfies `f x < f x0`, then there
is a neighborhood `V` of `x0` such that every `x ∈ V` satisfies
`f x ≤ f x0`.
-/
theorem StrictLocalMax.isLocalMax
    {f : Point n -> Real} {x0 : Point n} (h : StrictLocalMax f x0) :
    IsLocalMax f x0 := by
  rcases h with ⟨U, hU, hstrict⟩
  filter_upwards [hU] with x hxU
  by_cases hx : x = x0
  · simp [hx]
  · exact le_of_lt (hstrict x hxU hx)

/--
A strict local maximum is strict on a sufficiently small closed ball.

In quantified mathematical form, if `x0` is a strict local maximum point of
`f` and `R > 0`, then there exists `r` with `0 < r ≤ R` such that, for every
`x ∈ closedBall x0 r`, if `x ≠ x0`, then `f x < f x0`.
-/
theorem StrictLocalMax.exists_closedBall_strict
    {f : Point n -> Real} {x0 : Point n} (h : StrictLocalMax f x0)
    {R : Real} (hR : 0 < R) :
    ∃ r : Real, 0 < r ∧ r <= R ∧
      ∀ x : Point n, x ∈ Metric.closedBall x0 r -> x ≠ x0 -> f x < f x0 := by
  rcases h with ⟨U, hU, hstrict⟩
  rcases Metric.nhds_basis_closedBall.mem_iff.1 hU with ⟨r0, hr0, hr0U⟩
  let r : Real := min r0 R
  have hr_pos : 0 < r := lt_min hr0 hR
  have hr_le_r0 : r <= r0 := min_le_left r0 R
  have hr_le_R : r <= R := min_le_right r0 R
  refine ⟨r, hr_pos, hr_le_R, ?_⟩
  intro x hx hxne
  exact hstrict x (hr0U (Metric.closedBall_subset_closedBall hr_le_r0 hx)) hxne

/--
At a local maximum point, the zero jet is a superjet.

In quantified mathematical form, if there is a neighborhood `U` of `x` such
that `f y ≤ f x` for every `y ∈ U`, then `(0, 0)` belongs to
`J^{2,+}_{R^n} f(x)`.
-/
theorem superjet_zero_of_isLocalMax
    {f : Point n -> Real} {x : Point n} (hmax : IsLocalMax f x) :
    ({ gradient := 0, hessian := 0 } : Jet n) ∈ Superjet Set.univ f x := by
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact Asymptotics.isLittleO_zero (fun y : Point n => ‖y - x‖ ^ 2)
      (nhdsWithin x Set.univ)
  · rw [nhdsWithin_univ]
    filter_upwards [hmax] with y hy
    simpa [quadraticModel] using hy

/--
At a local maximum point, the zero jet belongs to the closed superjet.

In quantified mathematical form, if there is a neighborhood `U` of `x` such
that `f y ≤ f x` for every `y ∈ U`, then `(0, 0)` belongs to
`\overline J^{2,+}_{R^n} f(x)`.
-/
theorem closedSuperjet_zero_of_isLocalMax
    {f : Point n -> Real} {x : Point n} (hmax : IsLocalMax f x) :
    ({ gradient := 0, hessian := 0 } : Jet n) ∈ ClosedSuperjet Set.univ f x :=
  superjet_subset_closedSuperjet (C := Set.univ) (x := x) trivial
    (superjet_zero_of_isLocalMax hmax)

/--
The second-order calculus theorem needed after applying Jensen's lemma.

In quantified mathematical form, `LocalMaxSecondOrderJetCalculusTheorem n`
means: for every function `f : R^n -> R`, every point `x`, every vector `p`,
and every Hermitian matrix `X`, if `f` has a local maximum at `x` and
`(p, X)` belongs both to the ordinary superjet and to the ordinary subjet of
`f` at `x`, then `p = 0` and `X ≤ 0`.
-/
def LocalMaxSecondOrderJetCalculusTheorem (n : Nat) : Prop :=
  ∀ f : Point n -> Real, ∀ x p : Point n, ∀ X : Hessian n,
    X.IsHermitian -> IsLocalMax f x -> HasSecondOrderJet f x p X -> p = 0 ∧ X <= 0

/--
At a local maximum point, the Hermitian Hessian component of a two-sided
ordinary jet is nonpositive in the Loewner order.
-/
theorem HasSecondOrderJet.hessian_le_zero_of_isLocalMax
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (hX : X.IsHermitian) (hmax : IsLocalMax f x) (h : HasSecondOrderJet f x p X) :
    X <= 0 := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa using hX.neg
  · intro v
    have hquad := h.quadraticForm_nonpos_of_isLocalMax hmax v
    have hneg :
        dotProduct v (Matrix.mulVec (-X) v) =
          - dotProduct (Matrix.mulVec X v) v := by
      rw [Matrix.neg_mulVec, dotProduct_neg, dotProduct_comm]
    rw [show 0 - X = -X by simp]
    simpa [hneg] using neg_nonneg.mpr hquad

/--
The local-maximum second-order calculus theorem for Hermitian Hessian
components.
-/
theorem localMaxSecondOrderJetCalculusTheorem :
    LocalMaxSecondOrderJetCalculusTheorem n := by
  intro f x p X hX hmax hjet
  exact ⟨hjet.gradient_eq_zero_of_isLocalMax hmax,
    hjet.hessian_le_zero_of_isLocalMax hX hmax⟩

/--
The local-maximum second-order calculus theorem applies after adding a linear
perturbation.

In quantified mathematical form, assume the theorem
`LocalMaxSecondOrderJetCalculusTheorem n`. If `f` has second-order jet
`(a, X)` at `x`, the matrix `X` is Hermitian, and the function
`y ↦ f y + q · y` has a local maximum at `x`, then `a + q = 0` and `X ≤ 0`.
-/
theorem LocalMaxSecondOrderJetCalculusTheorem.apply_linearPerturbation
    (hcalc : LocalMaxSecondOrderJetCalculusTheorem n)
    {f : Point n -> Real} {x a q : Point n} {X : Hessian n}
    (hX : X.IsHermitian)
    (hmax : IsLocalMax (linearPerturbation f q) x)
    (hjet : HasSecondOrderJet f x a X) :
    a + q = 0 ∧ X <= 0 :=
  hcalc (linearPerturbation f q) x (a + q) X hX hmax
    (HasSecondOrderJet.linearPerturbation hjet)

end ViscositySolns
