/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Basic
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Stability.Max
public import LeanPool.ViscositySolutionTheory.ViscositySolns.TestFunctions.Smooth

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Perron quadratic bump certification

Quadratic and max-patching lemmas used at the beginning of the Perron bump construction.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Strict operator negativity for a quadratic model persists in a neighborhood of
the base point.

This is the continuity ingredient used in the Perron bump construction after a
failed lower-envelope subjet inequality has produced a strict negative value
of `F` at the contact jet.
-/
theorem OperatorContinuous.eventually_quadraticModelJetAt_lt_of_lt
    {F : Operator n} (hF : OperatorContinuous F)
    {x x0 : Point n} {r : Real} {p : Point n} {X : Hessian n}
    (hneg :
      F x (quadraticModel x0 r p X x)
          (quadraticModelJetAt x0 p X x).gradient
          (quadraticModelJetAt x0 p X x).hessian < 0) :
    ∀ᶠ z in nhds x,
      F z (quadraticModel x0 r p X z)
          (quadraticModelJetAt x0 p X z).gradient
          (quadraticModelJetAt x0 p X z).hessian < 0 := by
  have hpath : Continuous fun z : Point n =>
      ((z, quadraticModel x0 r p X z), quadraticModelJetAt x0 p X z) := by
    exact Continuous.prodMk
      (Continuous.prodMk continuous_id (continuous_quadraticModel x0 r p X))
      (continuous_quadraticModelJetAt x0 p X)
  have hcont : Continuous fun z : Point n =>
      F z (quadraticModel x0 r p X z)
          (quadraticModelJetAt x0 p X z).gradient
          (quadraticModelJetAt x0 p X z).hessian := by
    exact hF.continuous.comp hpath
  exact hcont.continuousAt (isOpen_Iio.mem_nhds hneg)

/--
Strict operator negativity for a quadratic model persists after a sufficiently
small positive vertical lift of the model, and then in a neighborhood of the
base point.

The lift parameter is the height of the Perron bump. Continuity of `F` first
chooses a positive height that keeps the contact inequality strict; the
preceding theorem then spreads that strict inequality to nearby points.
-/
theorem OperatorContinuous.exists_pos_eventually_quadraticModelJetAt_lift_lt_of_lt
    {F : Operator n} (hF : OperatorContinuous F)
    {x x0 : Point n} {r : Real} {p : Point n} {X : Hessian n}
    (hneg :
      F x (quadraticModel x0 r p X x)
          (quadraticModelJetAt x0 p X x).gradient
          (quadraticModelJetAt x0 p X x).hessian < 0) :
    ∃ κ : Real, 0 < κ ∧
      ∀ᶠ z in nhds x,
        F z (quadraticModel x0 (r + κ) p X z)
            (quadraticModelJetAt x0 p X z).gradient
            (quadraticModelJetAt x0 p X z).hessian < 0 := by
  let A : Jet n := quadraticModelJetAt x0 p X x
  have hval : Continuous fun κ : Real => quadraticModel x0 (r + κ) p X x := by
    have hlin : Continuous fun κ : Real =>
        κ + (r + dotProduct p (x - x0) +
          (1 / 2 : Real) * dotProduct (Matrix.mulVec X (x - x0)) (x - x0)) :=
      continuous_id.add continuous_const
    simpa [quadraticModel, add_comm, add_left_comm, add_assoc] using hlin
  have hpath : Continuous fun κ : Real =>
      ((x, quadraticModel x0 (r + κ) p X x), A) := by
    exact Continuous.prodMk (Continuous.prodMk continuous_const hval) continuous_const
  have hcontκ : Continuous fun κ : Real =>
      F x (quadraticModel x0 (r + κ) p X x) A.gradient A.hessian := by
    exact hF.continuous.comp hpath
  have hnearκ : ∀ᶠ κ in nhds (0 : Real),
      F x (quadraticModel x0 (r + κ) p X x) A.gradient A.hessian < 0 := by
    have hzero :
        F x (quadraticModel x0 (r + 0) p X x) A.gradient A.hessian < 0 := by
      simpa [A] using hneg
    exact hcontκ.continuousAt (isOpen_Iio.mem_nhds hzero)
  have : NeBot (nhdsWithin (0 : Real) (Set.Ioi 0)) := by infer_instance
  have hnearκWithin : ∀ᶠ κ in nhdsWithin (0 : Real) (Set.Ioi 0),
      F x (quadraticModel x0 (r + κ) p X x) A.gradient A.hessian < 0 :=
    hnearκ.filter_mono nhdsWithin_le_nhds
  have hposWithin : ∀ᶠ κ in nhdsWithin (0 : Real) (Set.Ioi 0),
      κ ∈ Set.Ioi (0 : Real) :=
    self_mem_nhdsWithin
  rcases (hnearκWithin.and hposWithin).exists with
    ⟨κ, hκneg, hκpos⟩
  refine ⟨κ, hκpos, ?_⟩
  exact hF.eventually_quadraticModelJetAt_lt_of_lt
    (x0 := x0) (r := r + κ) (p := p) (X := X) hκneg

/--
A viscosity subsolution quadratic satisfies the operator inequality at its
canonical recentered quadratic jet.
-/
theorem ViscositySubsolution.quadraticModelJetAt_le
    {C : Set (Point n)} {F : Operator n}
    {x0 : Point n} {r : Real} {p : Point n} {X : Hessian n}
    (hsub : ViscositySubsolution C F (fun y => quadraticModel x0 r p X y))
    {x : Point n} (hx : x ∈ C) :
    F x (quadraticModel x0 r p X x)
        (quadraticModelJetAt x0 p X x).gradient
        (quadraticModelJetAt x0 p X x).hessian <= 0 :=
  hsub.2 x hx (quadraticModelJetAt x0 p X x)
    (quadraticModelJetAt_mem_superjet x0 r p X x)

/--
A viscosity supersolution quadratic satisfies the operator inequality at its
canonical recentered quadratic jet.
-/
theorem ViscositySupersolution.quadraticModelJetAt_nonneg
    {C : Set (Point n)} {F : Operator n}
    {x0 : Point n} {r : Real} {p : Point n} {X : Hessian n}
    (hsuper : ViscositySupersolution C F (fun y => quadraticModel x0 r p X y))
    {x : Point n} (hx : x ∈ C) :
    0 <= F x (quadraticModel x0 r p X x)
        (quadraticModelJetAt x0 p X x).gradient
        (quadraticModelJetAt x0 p X x).hessian :=
  hsuper.2 x hx (quadraticModelJetAt x0 p X x)
    (quadraticModelJetAt_mem_subjet x0 r p X x)

/--
Subsolution certification from a controlled jet field.

If every superjet of `u` has the same gradient as a chosen jet field `A` and a
larger Hessian, then degenerate ellipticity reduces the viscosity subsolution
check to the operator inequality on `A`.
-/
theorem ViscositySubsolution.of_superjetControl
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (husc : UpperSemicontinuousOn u C) (hFell : DegenerateElliptic F)
    (A : Point n -> Jet n)
    (hcontrol : ∀ x : Point n, x ∈ C -> ∀ J : Jet n, J ∈ Superjet C u x ->
      J.gradient = (A x).gradient ∧ (A x).hessian <= J.hessian)
    (hineq : ∀ x : Point n, x ∈ C ->
      F x (u x) (A x).gradient (A x).hessian <= 0) :
    ViscositySubsolution C F u := by
  refine ⟨husc, ?_⟩
  intro x hx J hJ
  rcases hcontrol x hx J hJ with ⟨hgrad, hhess⟩
  have hell :
      F x (u x) (A x).gradient J.hessian <=
        F x (u x) (A x).gradient (A x).hessian :=
    hFell x (u x) (A x).gradient J.hessian (A x).hessian hhess
  have hmove :
      F x (u x) J.gradient J.hessian <=
        F x (u x) (A x).gradient (A x).hessian := by
    simpa [hgrad] using hell
  exact hmove.trans (hineq x hx)

/--
Supersolution certification from a controlled jet field.

For subjets the Hessian inequality is reversed: a controlled subjet has the
same gradient as `A` and a smaller Hessian. Degenerate ellipticity then moves
the operator inequality from `A` to the tested subjet.
-/
theorem ViscositySupersolution.of_subjetControl
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hlsc : LowerSemicontinuousOn u C) (hFell : DegenerateElliptic F)
    (A : Point n -> Jet n)
    (hcontrol : ∀ x : Point n, x ∈ C -> ∀ J : Jet n, J ∈ Subjet C u x ->
      J.gradient = (A x).gradient ∧ J.hessian <= (A x).hessian)
    (hineq : ∀ x : Point n, x ∈ C ->
      0 <= F x (u x) (A x).gradient (A x).hessian) :
    ViscositySupersolution C F u := by
  refine ⟨hlsc, ?_⟩
  intro x hx J hJ
  rcases hcontrol x hx J hJ with ⟨hgrad, hhess⟩
  have hell :
      F x (u x) (A x).gradient (A x).hessian <=
        F x (u x) (A x).gradient J.hessian :=
    hFell x (u x) (A x).gradient (A x).hessian J.hessian hhess
  have hmove :
      F x (u x) (A x).gradient (A x).hessian <=
        F x (u x) J.gradient J.hessian := by
    simpa [hgrad] using hell
  exact (hineq x hx).trans hmove

/--
Quadratic subsolution certification from superjet control.

This is the bump-facing specialization of
`ViscositySubsolution.of_superjetControl`: once the remaining analytic work
identifies superjets of a quadratic bump with larger-Hessian perturbations of
the recentered quadratic jet, checking the PDE on the recentered jet proves
that the bump is a viscosity subsolution.
-/
theorem ViscositySubsolution.quadraticModel_of_superjetControl
    {C : Set (Point n)} {F : Operator n}
    {x0 : Point n} {r : Real} {p : Point n} {X : Hessian n}
    (hFell : DegenerateElliptic F)
    (hcontrol : ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
      J ∈ Superjet C (fun y => quadraticModel x0 r p X y) x ->
        J.gradient = (quadraticModelJetAt x0 p X x).gradient ∧
          (quadraticModelJetAt x0 p X x).hessian <= J.hessian)
    (hineq : ∀ x : Point n, x ∈ C ->
      F x (quadraticModel x0 r p X x)
          (quadraticModelJetAt x0 p X x).gradient
          (quadraticModelJetAt x0 p X x).hessian <= 0) :
    ViscositySubsolution C F (fun y => quadraticModel x0 r p X y) := by
  refine ViscositySubsolution.of_superjetControl
    ((continuous_quadraticModel x0 r p X).continuousOn.upperSemicontinuousOn)
    hFell (fun x => quadraticModelJetAt x0 p X x) ?_ hineq
  intro x hx J hJ
  exact hcontrol x hx J hJ

/--
Quadratic subsolution certification on an interior domain.

This is the bump-facing version of the shared semijet control theorem:
interior points let us replace relative superjets by full-neighborhood
superjets, and the Hermitian hypothesis converts scalar quadratic-form control
into the Loewner order needed for degenerate ellipticity.
-/
theorem ViscositySubsolution.quadraticModel_of_mem_interior_of_isHermitian_sub
    {C : Set (Point n)} {F : Operator n}
    {x0 : Point n} {r : Real} {p : Point n} {X : Hessian n}
    (hFell : DegenerateElliptic F)
    (hinterior : ∀ x : Point n, x ∈ C -> x ∈ interior C)
    (hHerm : ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
      J ∈ Superjet C (fun y => quadraticModel x0 r p X y) x ->
        (J.hessian - (quadraticModelJetAt x0 p X x).hessian).IsHermitian)
    (hineq : ∀ x : Point n, x ∈ C ->
      F x (quadraticModel x0 r p X x)
          (quadraticModelJetAt x0 p X x).gradient
          (quadraticModelJetAt x0 p X x).hessian <= 0) :
    ViscositySubsolution C F (fun y => quadraticModel x0 r p X y) := by
  refine ViscositySubsolution.quadraticModel_of_superjetControl hFell ?_ hineq
  intro x hx J hJ
  exact quadraticModel_superjet_control_of_mem_interior_of_isHermitian_sub
    (hinterior x hx) hJ (hHerm x hx J hJ)

/--
Quadratic subsolution certification on an interior domain, using symmetric
Hessians.

If the quadratic Hessian is Hermitian and the operator ignores skew Hessian
parts, then arbitrary superjet Hessians can be symmetrized before applying
degenerate ellipticity. This is closer to the classical Perron bump argument,
where second derivatives are symmetric matrices.
-/
theorem ViscositySubsolution.quadraticModel_of_mem_interior_of_hessianSymmetricInvariant
    {C : Set (Point n)} {F : Operator n}
    {x0 : Point n} {r : Real} {p : Point n} {X : Hessian n}
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hX : X.IsHermitian)
    (hinterior : ∀ x : Point n, x ∈ C -> x ∈ interior C)
    (hineq : ∀ x : Point n, x ∈ C ->
      F x (quadraticModel x0 r p X x)
          (quadraticModelJetAt x0 p X x).gradient
          (quadraticModelJetAt x0 p X x).hessian <= 0) :
    ViscositySubsolution C F (fun y => quadraticModel x0 r p X y) := by
  refine ⟨(continuous_quadraticModel x0 r p X).continuousOn.upperSemicontinuousOn, ?_⟩
  intro x hx J hJ
  rcases quadraticModel_superjet_control_symHessian_of_mem_interior
      (hinterior x hx) hX hJ with ⟨hgrad, hhess⟩
  have hell :
      F x (quadraticModel x0 r p X x)
          (quadraticModelJetAt x0 p X x).gradient (symHessian J.hessian) <=
        F x (quadraticModel x0 r p X x)
          (quadraticModelJetAt x0 p X x).gradient
          (quadraticModelJetAt x0 p X x).hessian :=
    hFell x (quadraticModel x0 r p X x)
      (quadraticModelJetAt x0 p X x).gradient
      (symHessian J.hessian) (quadraticModelJetAt x0 p X x).hessian hhess
  calc
    F x (quadraticModel x0 r p X x) J.gradient J.hessian =
        F x (quadraticModel x0 r p X x) J.gradient (symHessian J.hessian) := by
      exact hFinv x (quadraticModel x0 r p X x) J.gradient J.hessian
    _ = F x (quadraticModel x0 r p X x)
        (quadraticModelJetAt x0 p X x).gradient (symHessian J.hessian) := by
      rw [hgrad]
    _ <= F x (quadraticModel x0 r p X x)
        (quadraticModelJetAt x0 p X x).gradient
        (quadraticModelJetAt x0 p X x).hessian := hell
    _ <= 0 := hineq x hx

/--
Quadratic supersolution certification from subjet control.
-/
theorem ViscositySupersolution.quadraticModel_of_subjetControl
    {C : Set (Point n)} {F : Operator n}
    {x0 : Point n} {r : Real} {p : Point n} {X : Hessian n}
    (hFell : DegenerateElliptic F)
    (hcontrol : ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
      J ∈ Subjet C (fun y => quadraticModel x0 r p X y) x ->
        J.gradient = (quadraticModelJetAt x0 p X x).gradient ∧
          J.hessian <= (quadraticModelJetAt x0 p X x).hessian)
    (hineq : ∀ x : Point n, x ∈ C ->
      0 <= F x (quadraticModel x0 r p X x)
          (quadraticModelJetAt x0 p X x).gradient
          (quadraticModelJetAt x0 p X x).hessian) :
    ViscositySupersolution C F (fun y => quadraticModel x0 r p X y) := by
  refine ViscositySupersolution.of_subjetControl
    ((continuous_quadraticModel x0 r p X).continuousOn.lowerSemicontinuousOn)
    hFell (fun x => quadraticModelJetAt x0 p X x) ?_ hineq
  intro x hx J hJ
  exact hcontrol x hx J hJ

/--
Superjet fibers depend only on the germ of the function at the base point,
together with the value at the base point.
-/
theorem superjet_congr_eventuallyEq
    {C : Set (Point n)} {u v : Point n -> Real} {x : Point n}
    (hx : u x = v x) (h : u =ᶠ[nhdsWithin x C] v) :
    Superjet C u x = Superjet C v x := by
  ext J
  constructor
  · intro hJ
    rcases hJ with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, h] with y hy hyuv
    simpa [hx, hyuv] using hy
  · intro hJ
    rcases hJ with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, h.symm] with y hy hyvu
    simpa [hx, hyvu.symm] using hy

/--
Subjet fibers depend only on the germ of the function at the base point,
together with the value at the base point.
-/
theorem subjet_congr_eventuallyEq
    {C : Set (Point n)} {u v : Point n -> Real} {x : Point n}
    (hx : u x = v x) (h : u =ᶠ[nhdsWithin x C] v) :
    Subjet C u x = Subjet C v x := by
  ext J
  constructor
  · intro hJ
    rcases hJ with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, h] with y hy hyuv
    simpa [hx, hyuv] using hy
  · intro hJ
    rcases hJ with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, h.symm] with y hy hyvu
    simpa [hx, hyvu.symm] using hy

/--
A viscosity subsolution can be checked locally in the germ of the function at
each point of the PDE domain.
-/
theorem ViscositySubsolution.of_locally_eventuallyEq
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hlocal : ∀ x : Point n, x ∈ C ->
      ∃ v : Point n -> Real,
        ViscositySubsolution C F v ∧
          u x = v x ∧
            u =ᶠ[nhdsWithin x C] v) :
    ViscositySubsolution C F u := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hlocal x hx with ⟨v, hv, hxuv, huv⟩
    exact UpperSemicontinuousWithinAt.congr_of_eventuallyEq
      (hv.1 x hx) hx huv.symm
  · intro x hx J hJ
    rcases hlocal x hx with ⟨v, hv, hxuv, huv⟩
    have hJv : J ∈ Superjet C v x := by
      simpa [superjet_congr_eventuallyEq hxuv huv] using hJ
    simpa [hxuv] using hv.2 x hx J hJv

/--
A viscosity subsolution can be checked from genuinely local domain germs.

This is the locality form needed for Perron patching: near each point of the
PDE domain `C`, the candidate only has to agree with a subsolution on a
relative neighborhood `D` of that point. The semijet domain-germ lemma then
transfers the local subsolution inequality back to `C`.
-/
theorem ViscositySubsolution.of_locally_eventuallyEqOn
    {C : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hlocal : ∀ x : Point n, x ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin x C ∧
            ViscositySubsolution D F v ∧
              u x = v x ∧
                u =ᶠ[nhdsWithin x C] v) :
    ViscositySubsolution C F u := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases hlocal x hx with ⟨D, v, hDC, hDnhds, hv, hxuv, huv⟩
    have hxD : x ∈ D := mem_of_mem_nhdsWithin hx hDnhds
    have hnhds : nhdsWithin x D = nhdsWithin x C :=
      nhdsWithin_eq_of_subset_of_mem_nhdsWithin hDC hDnhds
    have hvC : UpperSemicontinuousWithinAt v C x := by
      intro y hy
      have hnear := hv.1 x hxD y hy
      rwa [← hnhds]
    exact UpperSemicontinuousWithinAt.congr_of_eventuallyEq hvC hx huv.symm
  · intro x hx J hJ
    rcases hlocal x hx with ⟨D, v, hDC, hDnhds, hv, hxuv, huv⟩
    have hxD : x ∈ D := mem_of_mem_nhdsWithin hx hDnhds
    have hnhds : nhdsWithin x D = nhdsWithin x C :=
      nhdsWithin_eq_of_subset_of_mem_nhdsWithin hDC hDnhds
    have hJuC : J ∈ Superjet C v x := by
      simpa [superjet_congr_eventuallyEq hxuv huv] using hJ
    have hJvD : J ∈ Superjet D v x := by
      simpa [superjet_congr_nhdsWithin hnhds.symm] using hJuC
    simpa [hxuv] using hv.2 x hxD J hJvD

/--
A viscosity subsolution restricts to a relatively open subdomain.

This local restriction form is useful in the Perron patch: an old Perron
branch is known to be a subsolution on `C`, while the quadratic bump is only
certified on a smaller relative neighborhood `D`.
-/
theorem ViscositySubsolution.restrict_of_subset_of_mem_nhdsWithin
    {C D : Set (Point n)} {F : Operator n} {u : Point n -> Real}
    (hu : ViscositySubsolution C F u) (hDC : D ⊆ C)
    (hDnhds : ∀ x : Point n, x ∈ D -> D ∈ nhdsWithin x C) :
    ViscositySubsolution D F u := by
  refine ⟨?_, ?_⟩
  · intro x hxD
    have hnhds : nhdsWithin x D = nhdsWithin x C :=
      nhdsWithin_eq_of_subset_of_mem_nhdsWithin hDC (hDnhds x hxD)
    intro y hy
    have hnear := hu.1 x (hDC hxD) y hy
    rwa [hnhds]
  · intro x hxD J hJ
    have hnhds : nhdsWithin x D = nhdsWithin x C :=
      nhdsWithin_eq_of_subset_of_mem_nhdsWithin hDC (hDnhds x hxD)
    have hJC : J ∈ Superjet C u x := by
      simpa [superjet_congr_nhdsWithin hnhds] using hJ
    exact hu.2 x (hDC hxD) J hJC

/--
A Dirichlet subsolution can be assembled from local viscosity-subsolution
germs and a separately supplied boundary inequality.
-/
theorem DirichletSubsolutionOn.of_locally_eventuallyEq
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hlocal : ∀ x : Point n, x ∈ C ->
      ∃ v : Point n -> Real,
        ViscositySubsolution C F v ∧
          u x = v x ∧
            u =ᶠ[nhdsWithin x C] v)
    (hboundary : BoundarySubsolutionOn boundary g u) :
    -- Semicontinuity across the boundary is independent of the PDE germs.
    -- Callers assembling a genuine Dirichlet function must provide it.
    UpperSemicontinuousOn u (C ∪ boundary) ->
    DirichletSubsolutionOn C boundary F g u :=
  fun husc => ⟨ViscositySubsolution.of_locally_eventuallyEq hlocal, hboundary, husc⟩

/--
A Dirichlet subsolution can be assembled from local-domain
viscosity-subsolution germs and a separately supplied boundary inequality.
-/
theorem DirichletSubsolutionOn.of_locally_eventuallyEqOn
    {C boundary : Set (Point n)} {F : Operator n} {g u : Point n -> Real}
    (hlocal : ∀ x : Point n, x ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin x C ∧
            ViscositySubsolution D F v ∧
              u x = v x ∧
                u =ᶠ[nhdsWithin x C] v)
    (hboundary : BoundarySubsolutionOn boundary g u) :
    UpperSemicontinuousOn u (C ∪ boundary) ->
    DirichletSubsolutionOn C boundary F g u :=
  fun husc => ⟨ViscositySubsolution.of_locally_eventuallyEqOn hlocal, hboundary, husc⟩

/--
Union semicontinuity for a patch whose changes are confined to a compact
subset of an open domain. Interior points use the assembled subsolution's
USC; boundary points have a neighborhood disjoint from the compact support
and inherit USC from the original Dirichlet function.
-/
theorem UpperSemicontinuousOn.of_eqOn_compl_closed_patch
    {C boundary K : Set (Point n)} {u v : Point n -> Real}
    (hCopen : IsOpen C) (hKclosed : IsClosed K)
    (hbase : UpperSemicontinuousOn u (C ∪ boundary))
    (hpatchUSC : UpperSemicontinuousOn v C)
    (hEq : Set.EqOn v u Kᶜ)
    (hboundaryAvoid : ∀ x : Point n, x ∈ boundary -> x ∉ K) :
    UpperSemicontinuousOn v (C ∪ boundary) := by
  intro x hx
  rcases hx with hxC | hxB
  · have hCnhds : C ∈ nhds x := hCopen.mem_nhds hxC
    have hCwithin : C ∈ nhdsWithin x (C ∪ boundary) :=
      mem_nhdsWithin_of_mem_nhds hCnhds
    have heq : nhdsWithin x C = nhdsWithin x (C ∪ boundary) :=
      nhdsWithin_eq_of_subset_of_mem_nhdsWithin (by
        intro y hy
        exact Or.inl hy) hCwithin
    apply upperSemicontinuousWithinAt_iff.mpr
    intro t ht
    have h := (upperSemicontinuousWithinAt_iff.mp (hpatchUSC x hxC)) t ht
    rw [heq] at h
    exact h
  · by_cases hxC : x ∈ C
    · have hCnhds : C ∈ nhds x := hCopen.mem_nhds hxC
      have hCwithin : C ∈ nhdsWithin x (C ∪ boundary) :=
        mem_nhdsWithin_of_mem_nhds hCnhds
      have heq : nhdsWithin x C = nhdsWithin x (C ∪ boundary) :=
        nhdsWithin_eq_of_subset_of_mem_nhdsWithin (by
          intro y hy
          exact Or.inl hy) hCwithin
      apply upperSemicontinuousWithinAt_iff.mpr
      intro t ht
      have h := (upperSemicontinuousWithinAt_iff.mp (hpatchUSC x hxC)) t ht
      rw [heq] at h
      exact h
    · have hKavoid : Kᶜ ∈ nhds x := hKclosed.isOpen_compl.mem_nhds
        (hboundaryAvoid x hxB)
      have hevent : ∀ᶠ y in nhdsWithin x (C ∪ boundary), v y = u y := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds hKavoid] with y hy
        exact hEq hy
      exact UpperSemicontinuousWithinAt.congr_of_eventuallyEq
        (hbase x (Or.inr hxB)) (Or.inr hxB)
        (hevent.mono (by intro y hy; exact hy.symm))

/-- Interior USC and boundary USC assemble on an open domain and its boundary. -/
theorem UpperSemicontinuousOn.union_of_isOpen_domain
    {C boundary : Set (Point n)} {u : Point n -> Real}
    (hC : IsOpen C) (hu : UpperSemicontinuousOn u C)
    (hb : ∀ x ∈ boundary, UpperSemicontinuousWithinAt u (C ∪ boundary) x) :
    UpperSemicontinuousOn u (C ∪ boundary) := by
  intro x hx
  rcases hx with hx | hx
  · have hfilter : nhdsWithin x C = nhdsWithin x (C ∪ boundary) :=
      nhdsWithin_eq_of_subset_of_mem_nhdsWithin Set.subset_union_left
        (mem_nhdsWithin_of_mem_nhds (hC.mem_nhds hx))
    intro t ht
    have h := hu x hx t ht
    rwa [hfilter] at h
  · exact hb x hx

open Classical in
/-- A piecewise maximum preserves boundary USC if its support stays away
from the boundary point or its continuous branch lies below the base there. -/
theorem UpperSemicontinuousOn.piecewise_max_boundary
    {S P : Set (Point n)} {u q : Point n -> Real} {x : Point n}
    (hu : UpperSemicontinuousOn u S) (hq : Continuous q) (hx : x ∈ S)
    (hboundary : x ∉ closure P ∨ q x <= u x) :
    UpperSemicontinuousWithinAt
      (fun y => if y ∈ P then max (u y) (q y) else u y) S x := by
  classical
  rcases hboundary with haway | hle
  · have hout : Pᶜ ∈ nhds x :=
      Filter.mem_of_superset (isClosed_closure.isOpen_compl.mem_nhds haway)
        (fun _ hy hP => hy (subset_closure hP))
    have heq : u =ᶠ[nhdsWithin x S]
        (fun y => if y ∈ P then max (u y) (q y) else u y) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hout] with y hy
      have hnotP : y ∉ P := hy
      simp [hnotP]
    exact UpperSemicontinuousWithinAt.congr_of_eventuallyEq (hu x hx) hx heq
  · intro t ht
    have hvalue : (if x ∈ P then max (u x) (q x) else u x) = u x := by
      by_cases hP : x ∈ P
      · simp [hP, max_eq_left hle]
      · simp [hP]
    change (if x ∈ P then max (u x) (q x) else u x) < t at ht
    rw [hvalue] at ht
    have hmax := (hu.sup hq.continuousOn.upperSemicontinuousOn) x hx t
      (show max (u x) (q x) < t by rw [max_eq_left hle]; exact ht)
    filter_upwards [hmax] with y hy
    split_ifs
    · exact hy
    · exact (le_max_left (u y) (q y)).trans_lt hy

/-- The maximum of two Dirichlet subsolutions is a Dirichlet subsolution. -/
theorem DirichletSubsolutionOn.max
    {C boundary : Set (Point n)} {F : Operator n} {g u v : Point n -> Real}
    (hu : DirichletSubsolutionOn C boundary F g u)
    (hv : DirichletSubsolutionOn C boundary F g v) :
    DirichletSubsolutionOn C boundary F g (fun x => Max.max (u x) (v x)) := by
  refine ⟨hu.viscosity.max hv.viscosity, ?_, ?_⟩
  · intro x hx
    exact max_le (hu.boundary_le hx) (hv.boundary_le hx)
  · intro x hx t hmax
    have hleft : u x < t := (max_lt_iff.mp hmax).1
    have hright : v x < t := (max_lt_iff.mp hmax).2
    filter_upwards [hu.upperSemicontinuousOn x hx t hleft,
      hv.upperSemicontinuousOn x hx t hright] with y hy₁ hy₂
    exact (max_lt_iff.mpr ⟨hy₁, hy₂⟩)

/-- Membership in the Perron class is closed under pointwise maximum. -/
theorem PerronClass.max
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper u v : Point n -> Real}
    (hu : PerronClass C boundary F g lower upper u)
    (hv : PerronClass C boundary F g lower upper v) :
    PerronClass C boundary F g lower upper (fun x => Max.max (u x) (v x)) := by
  refine ⟨hu.dirichletSubsolution.max hv.dirichletSubsolution, ?_, ?_⟩
  · intro x hx
    exact le_max_of_le_left (hu.lower_le hx)
  · intro x hx
    exact max_le (hu.le_upper hx) (hv.le_upper hx)

/--
If a new local candidate is itself an admissible Perron-class member, max
patching with an old Perron-class member remains admissible. This is the
algebraic part of the localized bump construction; the analytic work is to
produce such a candidate and prove it agrees with the old function near the
patch boundary.
-/
theorem PerronClass.max_patch
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper old bump : Point n -> Real}
    (hold : PerronClass C boundary F g lower upper old)
    (hbump : PerronClass C boundary F g lower upper bump) :
    PerronClass C boundary F g lower upper
      (fun x => Max.max (old x) (bump x)) :=
  hold.max hbump

/-- Every Perron-class member lies below the pointwise Perron envelope. -/
theorem PerronClass.le_perronEnvelope
    {C boundary : Set (Point n)} {F : Operator n}
    {g lower upper w : Point n -> Real}
    (hw : PerronClass C boundary F g lower upper w) {x : Point n}
    (hbdd : BddAbove {r : Real | ∃ v : Point n -> Real,
      PerronClass C boundary F g lower upper v ∧ r = v x}) :
    w x <= perronEnvelope C boundary F g lower upper x := by
  exact le_csSup hbdd ⟨w, hw, rfl⟩

/--
The upper barrier supplies the boundedness needed to compare a Perron-class
member with the pointwise Perron envelope.
-/
theorem DirichletBarrierPair.perronClass_le_perronEnvelope
    {C boundary : Set (Point n)} {F : Operator n} {g w : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hw : PerronClass C boundary F g B.lower B.upper w) {x : Point n}
    (hx : x ∈ C ∪ boundary) :
    w x <= perronEnvelope C boundary F g B.lower B.upper x := by
  refine hw.le_perronEnvelope ?_
  refine ⟨B.upper x, ?_⟩
  intro r hr
  rcases hr with ⟨v, hv, rfl⟩
  exact hv.le_upper hx

/--
It is impossible for a Perron-class member to exceed the Perron envelope at a
Dirichlet-domain point.
-/
theorem DirichletBarrierPair.not_perronEnvelope_lt_perronClass
    {C boundary : Set (Point n)} {F : Operator n} {g w : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g)
    (hw : PerronClass C boundary F g B.lower B.upper w) {x : Point n}
    (hx : x ∈ C ∪ boundary) :
    ¬ perronEnvelope C boundary F g B.lower B.upper x < w x :=
  not_lt_of_ge (B.perronClass_le_perronEnvelope hw hx)

/--
Approximate the Perron envelope from below by a member of the Perron class at
a fixed point.
-/
theorem DirichletBarrierPair.exists_perronClass_gt_of_lt_perronEnvelope
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    (B : DirichletBarrierPair C boundary F g) {x : Point n} (hx : x ∈ C ∪ boundary)
    {a : Real} (ha : a < perronEnvelope C boundary F g B.lower B.upper x) :
    ∃ w : Point n -> Real,
      PerronClass C boundary F g B.lower B.upper w ∧ a < w x := by
  let S : Set Real := {r : Real | ∃ w : Point n -> Real,
    PerronClass C boundary F g B.lower B.upper w ∧ r = w x}
  have hbdd : BddAbove S := by
    refine ⟨B.upper x, ?_⟩
    intro r hr
    rcases hr with ⟨w, hw, rfl⟩
    exact hw.le_upper hx
  have hne : S.Nonempty :=
    ⟨B.lower x, B.lower, B.lower_mem_perronClass, rfl⟩
  have haS : a < sSup S := by
    simpa [perronEnvelope, S] using ha
  rcases (lt_csSup_iff hbdd hne).1 haS with ⟨r, hrS, har⟩
  rcases hrS with ⟨w, hw, rfl⟩
  exact ⟨w, hw, har⟩

end ViscositySolns
