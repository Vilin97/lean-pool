/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Semijets.Definitions

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Semijet calculus (QuadraticControl)

Part of the calculus lemmas for second-order superjets and subjets.
Split from `Calculus.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
If `rho(t) = o(t^2)`, then `rho(t) / t -> 0` along any filter approaching
`0` through nonzero points.
-/
theorem tendsto_div_self_of_isLittleO_sq
    {rho : Real -> Real}
    (hrho : Asymptotics.IsLittleO (nhds (0 : Real)) rho (fun t : Real => t ^ 2))
    (l : Filter Real) (hl : l ≤ nhdsWithin (0 : Real) {t : Real | t ≠ 0})
    (hl_nhds : l ≤ nhds (0 : Real)) :
    Tendsto (fun t : Real => rho t / t) l (nhds 0) := by
  have hrho_l : Asymptotics.IsLittleO l rho (fun t : Real => t ^ 2) :=
    hrho.mono hl_nhds
  have hratio :
      Tendsto (fun t : Real => rho t / t ^ 2) l (nhds 0) := by
    rw [Asymptotics.isLittleO_iff_tendsto'] at hrho_l
    · simpa [div_eq_mul_inv] using hrho_l
    · filter_upwards [show ∀ᶠ t in l, t ≠ 0 from hl self_mem_nhdsWithin] with t htne htzero
      exact False.elim (htne (sq_eq_zero_iff.mp htzero))
  have ht : Tendsto (fun t : Real => t) l (nhds 0) := tendsto_id.mono_left hl_nhds
  have hmul := hratio.mul ht
  have hmul' : Tendsto (fun t : Real => rho t / t ^ 2 * t) l (nhds 0) := by
    simpa using hmul
  exact Filter.Tendsto.congr' (by
    filter_upwards [show ∀ᶠ t in l, t ≠ 0 from hl self_mem_nhdsWithin] with t htne
    field_simp [htne]) hmul'

/--
First-order scalar coefficient extraction from a two-sided neighborhood.

If `rho(t) = o(t^2)` and
`0 <= a t + b t^2 + rho(t)` for all `t` sufficiently close to `0`, then
`a = 0`. The proof divides by `t` on the right and left one-sided
neighborhoods and compares the two limits.
-/
theorem eq_zero_of_eventually_nonneg_linear_add_sq_add_isLittleO_sq
    {a b : Real} {rho : Real -> Real}
    (hrho : Asymptotics.IsLittleO (nhds (0 : Real)) rho (fun t : Real => t ^ 2))
    (hineq : ∀ᶠ t in nhds (0 : Real), 0 <= a * t + b * t ^ 2 + rho t) :
    a = 0 := by
  let q : Real -> Real := fun t => (a * t + b * t ^ 2 + rho t) / t
  have hq_tendsto_right : Tendsto q (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds a) := by
    have hρ : Tendsto (fun t : Real => rho t / t)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) :=
      tendsto_div_self_of_isLittleO_sq hrho _
        (nhdsWithin_mono (0 : Real) (fun t ht => ne_of_gt ht))
        nhdsWithin_le_nhds
    have ht : Tendsto (fun t : Real => t) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hb : Tendsto (fun t : Real => b * t) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) :=
      by simpa using tendsto_const_nhds.mul ht
    have hsum : Tendsto (fun t : Real => a + b * t + rho t / t)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds (a + 0 + 0)) :=
      (tendsto_const_nhds.add hb).add hρ
    have hsum' : Tendsto (fun t : Real => a + b * t + rho t / t)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds a) := by
      simpa using hsum
    exact Filter.Tendsto.congr' (by
      filter_upwards [self_mem_nhdsWithin] with t htpos
      have htne : t ≠ 0 := ne_of_gt htpos
      dsimp [q]
      field_simp [htne]) hsum'
  have hq_tendsto_left : Tendsto q (nhdsWithin (0 : Real) (Set.Iio 0)) (nhds a) := by
    have hρ : Tendsto (fun t : Real => rho t / t)
        (nhdsWithin (0 : Real) (Set.Iio 0)) (nhds 0) :=
      tendsto_div_self_of_isLittleO_sq hrho _
        (nhdsWithin_mono (0 : Real) (fun t ht => ne_of_lt ht))
        nhdsWithin_le_nhds
    have ht : Tendsto (fun t : Real => t) (nhdsWithin (0 : Real) (Set.Iio 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hb : Tendsto (fun t : Real => b * t) (nhdsWithin (0 : Real) (Set.Iio 0)) (nhds 0) :=
      by simpa using tendsto_const_nhds.mul ht
    have hsum : Tendsto (fun t : Real => a + b * t + rho t / t)
        (nhdsWithin (0 : Real) (Set.Iio 0)) (nhds (a + 0 + 0)) :=
      (tendsto_const_nhds.add hb).add hρ
    have hsum' : Tendsto (fun t : Real => a + b * t + rho t / t)
        (nhdsWithin (0 : Real) (Set.Iio 0)) (nhds a) := by
      simpa using hsum
    exact Filter.Tendsto.congr' (by
      filter_upwards [self_mem_nhdsWithin] with t htneg
      have htne : t ≠ 0 := ne_of_lt htneg
      dsimp [q]
      field_simp [htne]) hsum'
  have hright_eventual : ∀ᶠ t in nhdsWithin (0 : Real) (Set.Ioi 0), 0 <= q t := by
    filter_upwards [hineq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htpos
    have htpos' : 0 < t := htpos
    dsimp [q]
    exact div_nonneg ht htpos'.le
  have hleft_eventual : ∀ᶠ t in nhdsWithin (0 : Real) (Set.Iio 0), q t <= 0 := by
    filter_upwards [hineq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with t ht htneg
    have htneg' : t < 0 := htneg
    dsimp [q]
    exact div_nonpos_of_nonneg_of_nonpos ht htneg'.le
  have hright_ne : NeBot (nhdsWithin (0 : Real) (Set.Ioi 0)) := by infer_instance
  have hleft_ne : NeBot (nhdsWithin (0 : Real) (Set.Iio 0)) := by infer_instance
  have ha_nonneg : 0 <= a :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hq_tendsto_right hright_eventual
  have ha_nonpos : a <= 0 :=
    le_of_tendsto_of_tendsto hq_tendsto_left tendsto_const_nhds hleft_eventual
  exact le_antisymm ha_nonpos ha_nonneg

/--
A scalar `o(t^2)` comparison lemma for extracting second-order coefficients.

In standard mathematical terms, if `f(t) = o(t^2)` as `t -> 0` and
`c t^2 <= f(t)` for all `t` sufficiently close to `0`, then `c <= 0`.
The proof works on the punctured neighborhood of `0`, divides by `t^2`, and
passes to the limit.
-/
theorem nonpos_of_eventually_mul_sq_le_isLittleO_sq
    {c : Real} {f : Real -> Real}
    (hf : Asymptotics.IsLittleO (nhds (0 : Real)) f (fun t : Real => t ^ 2))
    (hle : ∀ᶠ t in nhds (0 : Real), c * t ^ 2 <= f t) :
    c <= 0 := by
  have hle_ne : ∀ᶠ t in nhdsWithin (0 : Real) {t : Real | t ≠ 0},
      c <= f t / t ^ 2 := by
    filter_upwards [hle.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with t ht htne
    have ht2pos : 0 < t ^ 2 := sq_pos_of_ne_zero htne
    have hdiv : c * t ^ 2 / t ^ 2 <= f t / t ^ 2 :=
      div_le_div_of_nonneg_right ht ht2pos.le
    have hcancel : c * t ^ 2 / t ^ 2 = c := by
      field_simp [ne_of_gt ht2pos]
    simpa [hcancel] using hdiv
  have htendsto :
      Tendsto (fun t : Real => f t / t ^ 2)
        (nhdsWithin (0 : Real) {t : Real | t ≠ 0}) (nhds 0) := by
    have hf_ne : Asymptotics.IsLittleO (nhdsWithin (0 : Real) {t : Real | t ≠ 0})
        f (fun t : Real => t ^ 2) :=
      hf.mono nhdsWithin_le_nhds
    rw [Asymptotics.isLittleO_iff_tendsto'] at hf_ne
    · simpa [div_eq_mul_inv] using hf_ne
    · filter_upwards [self_mem_nhdsWithin] with t htne htzero
      exact (htne (sq_eq_zero_iff.mp htzero)).elim
  have : NeBot (nhdsWithin (0 : Real) {t : Real | t ≠ 0}) :=
    NormedField.nhdsNE_neBot (0 : Real)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds htendsto hle_ne

/--
A full-neighborhood superjet of the zero function has zero gradient.

The proof restricts the superjet inequality to every affine line through the
base point and applies the scalar first-order extraction lemma.
-/
theorem superjet_zero_univ_gradient_eq_zero
    {x : Point n} {J : Jet n}
    (hJ : J ∈ Superjet Set.univ (fun _ : Point n => (0 : Real)) x) :
    J.gradient = 0 := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  have hdot_zero : ∀ v : Point n, dotProduct J.gradient v = 0 := by
    intro v
    have hline : Tendsto (fun t : Real => x + t • v) (nhds (0 : Real))
        (nhdsWithin x (Set.univ : Set (Point n))) := by
      have hcont : ContinuousAt (fun t : Real => x + t • v) 0 :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      simpa [ContinuousAt, nhdsWithin_univ] using hcont
    have hineq_line : ∀ᶠ t in nhds (0 : Real),
        0 <= quadraticModel x 0 J.gradient J.hessian (x + t • v) +
          rho (x + t • v) :=
      hline hineq
    let a : Real := dotProduct J.gradient v
    let b : Real := (1 / 2 : Real) * dotProduct (Matrix.mulVec J.hessian v) v
    have hscalar : ∀ᶠ t in nhds (0 : Real),
        0 <= a * t + b * t ^ 2 + rho (x + t • v) := by
      filter_upwards [hineq_line] with t ht
      have hquad :
          quadraticModel x 0 J.gradient J.hessian (x + t • v) =
            a * t + b * t ^ 2 := by
        have hdx : x + t • v - x = t • v := by
          ext i
          simp
        simp [quadraticModel, a, b, hdx, Matrix.mulVec_smul, smul_dotProduct,
          dotProduct_smul]
        ring
      rw [hquad] at ht
      simpa [add_assoc] using ht
    have hlittle :
        Asymptotics.IsLittleO (nhds (0 : Real)) (fun t : Real => rho (x + t • v))
          (fun t : Real => t ^ 2) :=
      semijetRemainder_along_affine_isLittleO_sq (n := n) (z := x) (a := v) hrho
    exact eq_zero_of_eventually_nonneg_linear_add_sq_add_isLittleO_sq
      (a := a) (b := b) hlittle hscalar
  ext i
  have hi := hdot_zero (fun j : Fin n => if j = i then (1 : Real) else 0)
  simpa [dotProduct, Finset.sum_ite_eq, Finset.mem_univ] using hi

/--
The Hessian quadratic form of a zero-function superjet is nonnegative once the
gradient part is known to vanish.

This is the line-restriction step needed to control quadratic bumps. Applied
to a superjet of a quadratic model after subtracting the recentered quadratic
expansion, it gives the quadratic-form inequalities that imply Loewner order
under the necessary Hermitian hypothesis.
-/
theorem superjet_zero_univ_quadraticForm_nonneg_of_gradient_eq_zero
    {x : Point n} {J : Jet n}
    (hJ : J ∈ Superjet Set.univ (fun _ : Point n => (0 : Real)) x)
    (hgrad : J.gradient = 0) (v : Point n) :
    0 <= dotProduct (Matrix.mulVec J.hessian v) v := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  have hline : Tendsto (fun t : Real => x + t • v) (nhds (0 : Real))
      (nhdsWithin x (Set.univ : Set (Point n))) := by
    have hcont : ContinuousAt (fun t : Real => x + t • v) 0 :=
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
    simpa [ContinuousAt, nhdsWithin_univ] using hcont
  have hineq_line : ∀ᶠ t in nhds (0 : Real),
      0 <= quadraticModel x 0 J.gradient J.hessian (x + t • v) +
        rho (x + t • v) :=
    hline hineq
  have hle : ∀ᶠ t in nhds (0 : Real),
      (-(1 / 2 * dotProduct (Matrix.mulVec J.hessian v) v)) * t ^ 2 <=
        rho (x + t • v) := by
    filter_upwards [hineq_line] with t ht
    have hquad :
        quadraticModel x 0 J.gradient J.hessian (x + t • v) =
          (1 / 2 * dotProduct (Matrix.mulVec J.hessian v) v) * t ^ 2 := by
      have hdx : x + t • v - x = t • v := by
        ext i
        simp
      simp [quadraticModel, hgrad, hdx, Matrix.mulVec_smul, smul_dotProduct,
        dotProduct_smul]
      ring
    rw [hquad] at ht
    nlinarith
  have hlittle :
      Asymptotics.IsLittleO (nhds (0 : Real)) (fun t : Real => rho (x + t • v))
        (fun t : Real => t ^ 2) :=
    semijetRemainder_along_affine_isLittleO_sq (n := n) (z := x) (a := v) hrho
  have hnonpos :=
    nonpos_of_eventually_mul_sq_le_isLittleO_sq hlittle hle
  linarith

/--
A zero-function superjet with zero gradient has nonnegative Hessian, provided
the Hessian is Hermitian.

The Hermitian hypothesis is the unavoidable bridge from scalar quadratic-form
inequalities to mathlib's Loewner order on real matrices.
-/
theorem superjet_zero_univ_hessian_nonneg_of_gradient_eq_zero
    {x : Point n} {J : Jet n}
    (hJ : J ∈ Superjet Set.univ (fun _ : Point n => (0 : Real)) x)
    (hgrad : J.gradient = 0) (hHerm : J.hessian.IsHermitian) :
    0 <= J.hessian := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa using hHerm
  · intro v
    have hnonneg :=
      superjet_zero_univ_quadraticForm_nonneg_of_gradient_eq_zero hJ hgrad v
    simpa [dotProduct_comm] using hnonneg

/--
Hessian control for a full-neighborhood superjet of a quadratic model, after
the first-order part has been identified.

Subtracting the exact recentered quadratic expansion turns the superjet into a
zero-function superjet. The preceding zero-function lemma then gives
nonnegative Hessian difference, hence the desired Loewner inequality.
-/
theorem quadraticModel_superjet_hessian_le_of_gradient_eq_of_isHermitian_sub
    {x x0 : Point n} {r : Real} {p : Point n} {X : Hessian n} {J : Jet n}
    (hJ : J ∈ Superjet Set.univ (fun y => quadraticModel x0 r p X y) x)
    (hgrad : J.gradient = (quadraticModelJetAt x0 p X x).gradient)
    (hHerm :
      (J.hessian - (quadraticModelJetAt x0 p X x).hessian).IsHermitian) :
    (quadraticModelJetAt x0 p X x).hessian <= J.hessian := by
  let q : Point n -> Real := fun y => quadraticModel x0 r p X y
  let A : Jet n := quadraticModelJetAt x0 p X x
  have hAexp : HasSecondOrderExpansionWithin Set.univ q x A :=
    hasSecondOrderExpansionWithin_quadraticModel_recenter x0 r p X x
  have hzero : J - A ∈ Superjet Set.univ (fun _ : Point n => (0 : Real)) x := by
    rcases hJ with ⟨rho, hrho, hineq⟩
    rcases hAexp with ⟨sigma, hsigma, hq⟩
    refine ⟨fun y => rho y - sigma y, semijetRemainder_sub hrho hsigma, ?_⟩
    filter_upwards [hineq, hq] with y hy hqy
    calc
      (0 : Real) = q y - q y := by ring
      _ <= (quadraticModel x (q x) J.gradient J.hessian y + rho y) - q y := by
        linarith
      _ = (quadraticModel x (q x) J.gradient J.hessian y + rho y) -
          (quadraticModel x (q x) A.gradient A.hessian y + sigma y) := by
        rw [hqy]
      _ = quadraticModel x 0 (J - A).gradient (J - A).hessian y +
          (rho y - sigma y) := by
        have hqsub :
            quadraticModel x 0 (J.gradient - A.gradient) (J.hessian - A.hessian) y =
              quadraticModel x (q x) J.gradient J.hessian y -
                quadraticModel x (q x) A.gradient A.hessian y := by
          have h := quadraticModel_sub x (q x) (q x) J.gradient A.gradient
            J.hessian A.hessian y
          simpa using h
        simp only [Jet.sub_gradient, Jet.sub_hessian]
        rw [hqsub]
        ring
  have hKgrad : (J - A).gradient = 0 := by
    ext i
    simp [A, hgrad]
  have hKHerm : ((J - A).hessian).IsHermitian := by
    simpa [A] using hHerm
  have hnonneg :
      0 <= (J - A).hessian :=
    superjet_zero_univ_hessian_nonneg_of_gradient_eq_zero hzero hKgrad hKHerm
  rw [Matrix.le_iff] at hnonneg ⊢
  simpa [A, Jet.sub_hessian] using hnonneg

/--
Full-neighborhood superjet control for a quadratic model, up to the necessary
Hermitian hypothesis on the Hessian difference.

The gradient equality is forced by subtracting the exact quadratic expansion
and applying `superjet_zero_univ_gradient_eq_zero`; the Hessian inequality is
then the preceding Loewner-control lemma.
-/
theorem quadraticModel_superjet_control_of_isHermitian_sub
    {x x0 : Point n} {r : Real} {p : Point n} {X : Hessian n} {J : Jet n}
    (hJ : J ∈ Superjet Set.univ (fun y => quadraticModel x0 r p X y) x)
    (hHerm :
      (J.hessian - (quadraticModelJetAt x0 p X x).hessian).IsHermitian) :
    J.gradient = (quadraticModelJetAt x0 p X x).gradient ∧
      (quadraticModelJetAt x0 p X x).hessian <= J.hessian := by
  let q : Point n -> Real := fun y => quadraticModel x0 r p X y
  let A : Jet n := quadraticModelJetAt x0 p X x
  have hAexp : HasSecondOrderExpansionWithin Set.univ q x A :=
    hasSecondOrderExpansionWithin_quadraticModel_recenter x0 r p X x
  have hzero : J - A ∈ Superjet Set.univ (fun _ : Point n => (0 : Real)) x := by
    rcases hJ with ⟨rho, hrho, hineq⟩
    rcases hAexp with ⟨sigma, hsigma, hq⟩
    refine ⟨fun y => rho y - sigma y, semijetRemainder_sub hrho hsigma, ?_⟩
    filter_upwards [hineq, hq] with y hy hqy
    calc
      (0 : Real) = q y - q y := by ring
      _ <= (quadraticModel x (q x) J.gradient J.hessian y + rho y) - q y := by
        linarith
      _ = (quadraticModel x (q x) J.gradient J.hessian y + rho y) -
          (quadraticModel x (q x) A.gradient A.hessian y + sigma y) := by
        rw [hqy]
      _ = quadraticModel x 0 (J - A).gradient (J - A).hessian y +
          (rho y - sigma y) := by
        have hqsub :
            quadraticModel x 0 (J.gradient - A.gradient) (J.hessian - A.hessian) y =
              quadraticModel x (q x) J.gradient J.hessian y -
                quadraticModel x (q x) A.gradient A.hessian y := by
          have h := quadraticModel_sub x (q x) (q x) J.gradient A.gradient
            J.hessian A.hessian y
          simpa using h
        simp only [Jet.sub_gradient, Jet.sub_hessian]
        rw [hqsub]
        ring
  have hKgrad : (J - A).gradient = 0 :=
    superjet_zero_univ_gradient_eq_zero hzero
  have hgrad : J.gradient = A.gradient := by
    ext i
    have hi := congrFun hKgrad i
    simp [A] at hi
    linarith
  refine ⟨by simpa [A] using hgrad, ?_⟩
  exact quadraticModel_superjet_hessian_le_of_gradient_eq_of_isHermitian_sub
    hJ (by simpa [A] using hgrad) hHerm

/--
At an interior point of the domain, ordinary superjets over the domain are the
same as full-neighborhood superjets.
-/
theorem superjet_eq_univ_of_mem_interior
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n}
    (hx : x ∈ interior C) :
    Superjet C u x = Superjet Set.univ u x := by
  apply superjet_congr_nhdsWithin
  have hC : nhdsWithin x C = nhds x :=
    nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hx)
  simpa [nhdsWithin_univ] using hC

/--
Interior-domain superjet control for a quadratic model.

This is the local version used by smooth Perron bumps: once the base point is
interior to the PDE domain, superjets relative to the domain can be read as
full-neighborhood superjets and controlled by the canonical recentered
quadratic jet.
-/
theorem quadraticModel_superjet_control_of_mem_interior_of_isHermitian_sub
    {C : Set (Point n)} {x x0 : Point n} {r : Real}
    {p : Point n} {X : Hessian n} {J : Jet n}
    (hx : x ∈ interior C)
    (hJ : J ∈ Superjet C (fun y => quadraticModel x0 r p X y) x)
    (hHerm :
      (J.hessian - (quadraticModelJetAt x0 p X x).hessian).IsHermitian) :
    J.gradient = (quadraticModelJetAt x0 p X x).gradient ∧
      (quadraticModelJetAt x0 p X x).hessian <= J.hessian := by
  have hJ_univ : J ∈ Superjet Set.univ (fun y => quadraticModel x0 r p X y) x := by
    simpa [superjet_eq_univ_of_mem_interior
      (C := C) (u := fun y => quadraticModel x0 r p X y) hx] using hJ
  exact quadraticModel_superjet_control_of_isHermitian_sub hJ_univ hHerm

/--
Symmetrizing the Hessian component of a superjet preserves superjet membership.

The defining quadratic model only sees the symmetric part of the Hessian.
-/
theorem superjet_symHessian
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hJ : J ∈ Superjet C u x) :
    ({ gradient := J.gradient, hessian := symHessian J.hessian } : Jet n) ∈
      Superjet C u x := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [hineq] with y hy
  rwa [quadraticModel_symHessian]

/--
Symmetrizing the Hessian component of a subjet preserves subjet membership.
-/
theorem subjet_symHessian
    {C : Set (Point n)} {u : Point n -> Real} {x : Point n} {J : Jet n}
    (hJ : J ∈ Subjet C u x) :
    ({ gradient := J.gradient, hessian := symHessian J.hessian } : Jet n) ∈
      Subjet C u x := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [hineq] with y hy
  rwa [quadraticModel_symHessian]

/--
Interior-domain superjet control for a quadratic model after symmetrizing the
tested Hessian.

This avoids asking every raw superjet Hessian difference to be Hermitian.
Instead, the quadratic's own Hessian is Hermitian and the arbitrary tested
Hessian is replaced by its symmetric part, which defines the same quadratic
touching polynomial.
-/
theorem quadraticModel_superjet_control_symHessian_of_mem_interior
    {C : Set (Point n)} {x x0 : Point n} {r : Real}
    {p : Point n} {X : Hessian n} {J : Jet n}
    (hx : x ∈ interior C) (hX : X.IsHermitian)
    (hJ : J ∈ Superjet C (fun y => quadraticModel x0 r p X y) x) :
    J.gradient = (quadraticModelJetAt x0 p X x).gradient ∧
      (quadraticModelJetAt x0 p X x).hessian <= symHessian J.hessian := by
  let Js : Jet n := { gradient := J.gradient, hessian := symHessian J.hessian }
  have hJs : Js ∈ Superjet C (fun y => quadraticModel x0 r p X y) x := by
    simpa [Js] using superjet_symHessian hJ
  have hHerm :
      (Js.hessian - (quadraticModelJetAt x0 p X x).hessian).IsHermitian := by
    have hA : ((quadraticModelJetAt x0 p X x).hessian).IsHermitian := by
      simpa [quadraticModelJetAt] using hX
    exact (symHessian_isHermitian J.hessian).sub hA
  simpa [Js] using
    quadraticModel_superjet_control_of_mem_interior_of_isHermitian_sub hx hJs hHerm

/--
Recover Loewner order from quadratic-form inequalities, once the Hessian
difference is known to be Hermitian.

The Hermitian hypothesis is essential in the current jet setup: quadratic
models only see the symmetric part of a matrix, while mathlib's Loewner order
is an order on Hermitian differences.
-/
theorem hessian_le_of_forall_quadraticForm_le_of_isHermitian_sub
    {X Y : Hessian n} (hHerm : (Y - X).IsHermitian)
    (hquad : ∀ v : Point n,
      dotProduct (Matrix.mulVec X v) v <= dotProduct (Matrix.mulVec Y v) v) :
    X <= Y := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hHerm ?_
  intro v
  have hv : dotProduct (Matrix.mulVec X v) v <= dotProduct (Matrix.mulVec Y v) v :=
    hquad v
  have hrewrite :
      dotProduct v (Matrix.mulVec (Y - X) v) =
        dotProduct (Matrix.mulVec Y v) v - dotProduct (Matrix.mulVec X v) v := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    rw [dotProduct_comm v (Matrix.mulVec Y v),
      dotProduct_comm v (Matrix.mulVec X v)]
  have hnonneg : 0 <= dotProduct v (Matrix.mulVec (Y - X) v) := by
    linarith
  simpa using hnonneg

/--
If `J` is a superjet of `u` and `K` is a superjet of `v`, then `J + K` is a
superjet of `u + v`. This is the formal version of CIL Remark 2.6(ii)'s
inclusion `J^{2,+}(u+v) ⊇ J^{2,+}u + J^{2,+}v`.
-/
theorem superjet_add {C : Set (Point n)} {u v : Point n -> Real}
    {x : Point n} {J K : Jet n}
    (hJ : J ∈ Superjet C u x) (hK : K ∈ Superjet C v x) :
    J + K ∈ Superjet C (fun y => u y + v y) x := by
  rcases hJ with ⟨rho, hrho, hu⟩
  rcases hK with ⟨sigma, hsigma, hv⟩
  refine ⟨fun y => rho y + sigma y, semijetRemainder_add hrho hsigma, ?_⟩
  filter_upwards [hu, hv] with y huy hvy
  rw [Jet.add_gradient, Jet.add_hessian, quadraticModel_add]
  linarith

/--
If `J` is a subjet of `u` and `K` is a subjet of `v`, then `J + K` is a subjet
of `u + v`.
-/
theorem subjet_add {C : Set (Point n)} {u v : Point n -> Real}
    {x : Point n} {J K : Jet n}
    (hJ : J ∈ Subjet C u x) (hK : K ∈ Subjet C v x) :
    J + K ∈ Subjet C (fun y => u y + v y) x := by
  rcases hJ with ⟨rho, hrho, hu⟩
  rcases hK with ⟨sigma, hsigma, hv⟩
  refine ⟨fun y => rho y + sigma y, semijetRemainder_add hrho hsigma, ?_⟩
  filter_upwards [hu, hv] with y huy hvy
  rw [Jet.add_gradient, Jet.add_hessian, quadraticModel_add]
  linarith

/--
A superjet of `max u v` at a point where `u` is an active branch is a superjet
of `u`.
-/
theorem superjet_max_of_left {C : Set (Point n)} {u v : Point n -> Real}
    {x : Point n} {J : Jet n}
    (hJ : J ∈ Superjet C (fun y => max (u y) (v y)) x)
    (hactive : max (u x) (v x) = u x) :
    J ∈ Superjet C u x := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [hineq] with y hy
  calc
    u y <= max (u y) (v y) := le_max_left _ _
    _ <= quadraticModel x ((fun y => max (u y) (v y)) x)
        J.gradient J.hessian y + rho y := hy
    _ = quadraticModel x (u x) J.gradient J.hessian y + rho y := by
      simp [hactive]

/--
A superjet of `max u v` at a point where `v` is an active branch is a superjet
of `v`.
-/
theorem superjet_max_of_right {C : Set (Point n)} {u v : Point n -> Real}
    {x : Point n} {J : Jet n}
    (hJ : J ∈ Superjet C (fun y => max (u y) (v y)) x)
    (hactive : max (u x) (v x) = v x) :
    J ∈ Superjet C v x := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [hineq] with y hy
  calc
    v y <= max (u y) (v y) := le_max_right _ _
    _ <= quadraticModel x ((fun y => max (u y) (v y)) x)
        J.gradient J.hessian y + rho y := hy
    _ = quadraticModel x (v x) J.gradient J.hessian y + rho y := by
      simp [hactive]

/--
A subjet of `min u v` at a point where `u` is an active branch is a subjet of
`u`.
-/
theorem subjet_min_of_left {C : Set (Point n)} {u v : Point n -> Real}
    {x : Point n} {J : Jet n}
    (hJ : J ∈ Subjet C (fun y => min (u y) (v y)) x)
    (hactive : min (u x) (v x) = u x) :
    J ∈ Subjet C u x := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [hineq] with y hy
  calc
    quadraticModel x (u x) J.gradient J.hessian y + rho y =
        quadraticModel x ((fun y => min (u y) (v y)) x) J.gradient J.hessian y +
          rho y := by
      simp [hactive]
    _ <= min (u y) (v y) := hy
    _ <= u y := min_le_left _ _

/--
A subjet of `min u v` at a point where `v` is an active branch is a subjet of
`v`.
-/
theorem subjet_min_of_right {C : Set (Point n)} {u v : Point n -> Real}
    {x : Point n} {J : Jet n}
    (hJ : J ∈ Subjet C (fun y => min (u y) (v y)) x)
    (hactive : min (u x) (v x) = v x) :
    J ∈ Subjet C v x := by
  rcases hJ with ⟨rho, hrho, hineq⟩
  refine ⟨rho, hrho, ?_⟩
  filter_upwards [hineq] with y hy
  calc
    quadraticModel x (v x) J.gradient J.hessian y + rho y =
        quadraticModel x ((fun y => min (u y) (v y)) x) J.gradient J.hessian y +
          rho y := by
      simp [hactive]
    _ <= min (u y) (v y) := hy
    _ <= v y := min_le_right _ _

/--
Superjet fibers depend only on the values of the function on the domain `C`.
-/
theorem superjet_congr_eqOn {C : Set (Point n)} {u v : Point n -> Real}
    {x : Point n} (h : Set.EqOn u v C) (hx : x ∈ C) :
    Superjet C u x = Superjet C v x := by
  ext J
  constructor
  · intro hJ
    rcases hJ with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, h.eventuallyEq_nhdsWithin] with y hy hyuv
    simpa [h hx, hyuv] using hy
  · intro hJ
    rcases hJ with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, h.symm.eventuallyEq_nhdsWithin] with y hy hyvu
    simpa [h hx, hyvu.symm] using hy

/--
Subjet fibers depend only on the values of the function on the domain `C`.
-/
theorem subjet_congr_eqOn {C : Set (Point n)} {u v : Point n -> Real}
    {x : Point n} (h : Set.EqOn u v C) (hx : x ∈ C) :
    Subjet C u x = Subjet C v x := by
  ext J
  constructor
  · intro hJ
    rcases hJ with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, h.eventuallyEq_nhdsWithin] with y hy hyuv
    simpa [h hx, hyuv] using hy
  · intro hJ
    rcases hJ with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, h.symm.eventuallyEq_nhdsWithin] with y hy hyvu
    simpa [h hx, hyvu.symm] using hy

/--
Subtracting a constant from a function does not change its superjet fibers.

In quantified mathematical form, for every real number `δ`,
`J ∈ J^{2,+}_C (u - δ)(x)` if and only if `J ∈ J^{2,+}_C u(x)`.
-/
theorem superjet_sub_const_iff {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} {J : Jet n} {δ : Real} :
    J ∈ Superjet C (fun y => u y - δ) x ↔ J ∈ Superjet C u x := by
  constructor
  · rintro ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq] with y hy
    simp [quadraticModel] at hy ⊢
    linarith
  · rintro ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq] with y hy
    simp [quadraticModel] at hy ⊢
    linarith

/--
Subtracting a constant from a function does not change its subjet fibers.

In quantified mathematical form, for every real number `δ`,
`J ∈ J^{2,-}_C (u - δ)(x)` if and only if `J ∈ J^{2,-}_C u(x)`.
-/
theorem subjet_sub_const_iff {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} {J : Jet n} {δ : Real} :
    J ∈ Subjet C (fun y => u y - δ) x ↔ J ∈ Subjet C u x := by
  constructor
  · rintro ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq] with y hy
    simp [quadraticModel] at hy ⊢
    linarith
  · rintro ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq] with y hy
    simp [quadraticModel] at hy ⊢
    linarith

/--
Convex combinations of superjets remain superjets. This is the concrete form of
convexity of the fiber `J^{2,+}_C u(x)`.
-/
theorem superjet_convexCombination {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} {J K : Jet n} {a b : Real}
    (hJ : J ∈ Superjet C u x) (hK : K ∈ Superjet C u x)
    (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
    a • J + b • K ∈ Superjet C u x := by
  rcases hJ with ⟨rho, hrho, hu⟩
  rcases hK with ⟨sigma, hsigma, hv⟩
  refine ⟨fun y => a * rho y + b * sigma y,
    semijetRemainder_add (semijetRemainder_const_mul a hrho)
      (semijetRemainder_const_mul b hsigma), ?_⟩
  filter_upwards [hu, hv] with y huy hvy
  simp only [Jet.add_gradient, Jet.add_hessian, Jet.smul_gradient, Jet.smul_hessian]
  rw [quadraticModel_convexCombination x (u x) a b J.gradient K.gradient
    J.hessian K.hessian y hab]
  have hJmul : a * u y <=
      a * (quadraticModel x (u x) J.gradient J.hessian y + rho y) :=
    mul_le_mul_of_nonneg_left huy ha
  have hKmul : b * u y <=
      b * (quadraticModel x (u x) K.gradient K.hessian y + sigma y) :=
    mul_le_mul_of_nonneg_left hvy hb
  calc
    u y = a * u y + b * u y := by
      nlinarith [congrArg (fun t => u y * t) hab]
    _ <= a * (quadraticModel x (u x) J.gradient J.hessian y + rho y) +
        b * (quadraticModel x (u x) K.gradient K.hessian y + sigma y) :=
      add_le_add hJmul hKmul
    _ = a * quadraticModel x (u x) J.gradient J.hessian y +
        b * quadraticModel x (u x) K.gradient K.hessian y +
          (a * rho y + b * sigma y) := by ring

/--
Convex combinations of subjets remain subjets. This is the concrete form of
convexity of the fiber `J^{2,-}_C u(x)`.
-/
theorem subjet_convexCombination {C : Set (Point n)} {u : Point n -> Real}
    {x : Point n} {J K : Jet n} {a b : Real}
    (hJ : J ∈ Subjet C u x) (hK : K ∈ Subjet C u x)
    (ha : 0 <= a) (hb : 0 <= b) (hab : a + b = 1) :
    a • J + b • K ∈ Subjet C u x := by
  rcases hJ with ⟨rho, hrho, hu⟩
  rcases hK with ⟨sigma, hsigma, hv⟩
  refine ⟨fun y => a * rho y + b * sigma y,
    semijetRemainder_add (semijetRemainder_const_mul a hrho)
      (semijetRemainder_const_mul b hsigma), ?_⟩
  filter_upwards [hu, hv] with y huy hvy
  simp only [Jet.add_gradient, Jet.add_hessian, Jet.smul_gradient, Jet.smul_hessian]
  rw [quadraticModel_convexCombination x (u x) a b J.gradient K.gradient
    J.hessian K.hessian y hab]
  have hJmul :
      a * (quadraticModel x (u x) J.gradient J.hessian y + rho y) <= a * u y :=
    mul_le_mul_of_nonneg_left huy ha
  have hKmul :
      b * (quadraticModel x (u x) K.gradient K.hessian y + sigma y) <= b * u y :=
    mul_le_mul_of_nonneg_left hvy hb
  calc
    a * quadraticModel x (u x) J.gradient J.hessian y +
        b * quadraticModel x (u x) K.gradient K.hessian y +
          (a * rho y + b * sigma y) =
        a * (quadraticModel x (u x) J.gradient J.hessian y + rho y) +
          b * (quadraticModel x (u x) K.gradient K.hessian y + sigma y) := by ring
    _ <= a * u y + b * u y := add_le_add hJmul hKmul
    _ = u y := by
      nlinarith [congrArg (fun t => u y * t) hab]

/-- Ordinary superjet fibers are convex. -/
theorem convex_superjet (C : Set (Point n)) (u : Point n -> Real) (x : Point n) :
    Convex Real (Superjet C u x) := by
  rw [convex_iff_add_mem]
  intro J hJ K hK a b ha hb hab
  exact superjet_convexCombination hJ hK ha hb hab

/-- Ordinary subjet fibers are convex. -/
theorem convex_subjet (C : Set (Point n)) (u : Point n -> Real) (x : Point n) :
    Convex Real (Subjet C u x) := by
  rw [convex_iff_add_mem]
  intro J hJ K hK a b ha hb hab
  exact subjet_convexCombination hJ hK ha hb hab

end ViscositySolns
