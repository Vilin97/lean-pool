/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.QuadraticGluing.CertifiedPatches

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Quadratic gluing data for the Perron bump step (OpenBumpMaxPatches)

Part of the quadratic-gluing development connecting the lifted quadratic
supplied by operator continuity to the strict local max-patch formulation.
Split from `QuadraticGluing.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Bent open lifted-quadratic data plus bent open-active lower-barrier exterior
data gives the bent max-patch datum.
-/
theorem PerronLowerEnvelopeBentQuadraticOpenBumpAt.bentQuadraticMaxPatchAt_of_openBarrierExteriorAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeBentQuadraticOpenBumpAt C boundary F g B x J)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticOpenBarrierExteriorPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeBentQuadraticMaxPatchAt C boundary F g B x J := by
  rcases hquad with
    ⟨δ, γ, V, hδpos, hγpos, hVopen, hV, hWltq, hqCont, hneg⟩
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  rcases hpatch δ γ V hδpos hγpos hVopen hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hboundaryAway, hKnhds, hlower⟩
  have hlocalOld : ∀ z : Point n, z ∈ K ->
      ∃ w : PerronFamily C boundary F g B.lower B.upper,
        ∀ᶠ y in nhdsWithin z K, q y <= w.fun y := by
    intro z hz
    exact ⟨⟨B.lower, B.lower_mem_perronClass⟩, hlower z hz⟩
  rcases B.exists_perronClass_eventually_dominate_on_isCompact
      hKcompact hKnhds hlocalOld with
    ⟨old, hold, hOld⟩
  let patched : Point n -> Real := fun y => Max.max (old y) (q y)
  have hlocal : ∀ z : Point n, z ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin z C ∧
            ViscositySubsolution D F v ∧
              patched z = v z ∧ patched =ᶠ[nhdsWithin z C] v := by
    intro z hz
    by_cases hzV : z ∈ V
    · rcases exists_activeDomain_inter_of_isOpen
        (C := C) (V := V) hCopen hVopen hz hzV with
        ⟨D, hDC, hDnhds, hDopen, hDinterior, hDV⟩
      have hqSubSym :
          ViscositySubsolution D F
            (fun y =>
              quadraticModel x
                (lowerEnvelope C
                    (perronEnvelope C boundary F g B.lower B.upper) x + δ)
                J.gradient (symHessian Xb) y) := by
        refine
          ViscositySubsolution.quadraticModel_of_mem_interior_of_hessianSymmetricInvariant
            (C := D) (F := F) (x0 := x)
            (r := lowerEnvelope C
              (perronEnvelope C boundary F g B.lower B.upper) x + δ)
            (p := J.gradient) (X := symHessian Xb)
            hFell hFinv (symHessian_isHermitian Xb) hDinterior ?_
        intro y hy
        have hnegOrig : F y (q y)
            (quadraticModelJetAt x J.gradient Xb y).gradient
            (quadraticModelJetAt x J.gradient Xb y).hessian < 0 :=
          hneg y (hDV y hy) (hDC hy)
        have hnegSym :
            F y
                (quadraticModel x
                  (lowerEnvelope C
                      (perronEnvelope C boundary F g B.lower B.upper) x + δ)
                  J.gradient (symHessian Xb) y)
                (quadraticModelJetAt x J.gradient (symHessian Xb) y).gradient
                (quadraticModelJetAt x J.gradient (symHessian Xb) y).hessian < 0 := by
          calc
            F y
                (quadraticModel x
                  (lowerEnvelope C
                      (perronEnvelope C boundary F g B.lower B.upper) x + δ)
                  J.gradient (symHessian Xb) y)
                (quadraticModelJetAt x J.gradient (symHessian Xb) y).gradient
                (quadraticModelJetAt x J.gradient (symHessian Xb) y).hessian
                = F y (q y)
                    (quadraticModelJetAt x J.gradient Xb y).gradient
                    (symHessian Xb) := by
                  rw [quadraticModel_symHessian,
                    quadraticModelJetAt_gradient_symHessian]
                  simp [q, quadraticModelJetAt]
            _ = F y (q y)
                    (quadraticModelJetAt x J.gradient Xb y).gradient
                    (quadraticModelJetAt x J.gradient Xb y).hessian := by
                  rw [← hFinv y (q y)
                    (quadraticModelJetAt x J.gradient Xb y).gradient Xb]
                  simp [quadraticModelJetAt]
            _ < 0 := hnegOrig
        exact le_of_lt hnegSym
      have hqSub : ViscositySubsolution D F q := by
        simpa [q, quadraticModel_symHessian] using hqSubSym
      have holdD : ViscositySubsolution D F old :=
        hold.dirichletSubsolution.viscosity.restrict_of_subset_of_mem_nhdsWithin hDC hDopen
      refine ⟨D, patched, hDC, hDnhds, ?_, rfl, EventuallyEq.rfl⟩
      exact holdD.max hqSub
    · have hzK : z ∈ K := hcover z (Or.inl hz) hzV
      rcases hOld z hzK with ⟨hzle, hnear⟩
      refine ⟨C, old, subset_rfl, self_mem_nhdsWithin,
        hold.dirichletSubsolution.viscosity, ?_, ?_⟩
      · exact max_eq_left hzle
      · filter_upwards [hnear] with y hy
        exact max_eq_left hy
  have hboundary : BoundarySubsolutionOn boundary g patched := by
    intro y hy
    have hyK : y ∈ K := hcover y (Or.inr hy) (hboundaryAway y hy)
    rcases hOld y hyK with ⟨hyle, _hnear⟩
    have hpatched_y : patched y = old y := max_eq_left hyle
    rw [hpatched_y]
    exact hold.dirichletSubsolution.boundary_le hy
  have hsc : UpperSemicontinuousOn patched (C ∪ boundary) :=
    hold.dirichletSubsolution.upperSemicontinuousOn.sup
      (continuous_quadraticModel _ _ _ _).continuousOn.upperSemicontinuousOn
  have hdirichlet : DirichletSubsolutionOn C boundary F g patched :=
    DirichletSubsolutionOn.of_locally_eventuallyEqOn hlocal hboundary hsc
  have hlower : ∀ z : Point n, z ∈ C ∪ boundary -> B.lower z <= patched z := by
    intro z hz
    exact (hold.lower_le hz).trans (le_max_left (old z) (q z))
  have hupper : ∀ z : Point n, z ∈ C ∪ boundary -> patched z <= B.upper z :=
    hcomparison hdirichlet B.upper_dirichlet
  have hpatched : PerronClass C boundary F g B.lower B.upper patched :=
    ⟨hdirichlet, hlower, hupper⟩
  refine ⟨δ, γ, V, old, hδpos, hγpos, hV, ?_, ?_, hold, ?_⟩
  · simpa [q, Xb] using hWltq
  · simpa [q, Xb] using hqCont
  · simpa [patched, q, Xb] using hpatched

/--
Global bent open lifted-quadratic data plus bent open-active lower-barrier
exterior data gives the global bent max-patch datum.
-/
theorem PerronLowerEnvelopeBentQuadraticOpenBump.bentQuadraticMaxPatch_of_openBarrierExterior
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeBentQuadraticOpenBump C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticOpenBarrierExteriorPatch C boundary F g B) :
    PerronLowerEnvelopeBentQuadraticMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hquad x hx J hJ hneg).bentQuadraticMaxPatchAt_of_openBarrierExteriorAt
    hcomparison hFell hFinv hCopen (hpatch x hx J hJ hneg)

/--
Operator continuity reduces the bent strict-local patch step to the
source-shaped bent exterior annulus data.
-/
theorem OperatorContinuous.perronLowerEnvelope_strictLocalPatch_of_bentOpenBarrierExterior
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticOpenBarrierExteriorPatch C boundary F g B) :
    PerronLowerEnvelopeStrictLocalPatch C boundary F g B :=
  (hF.perronLowerEnvelope_bentQuadraticOpenBump
    |>.bentQuadraticMaxPatch_of_openBarrierExterior
      hcomparison hFell hFinv hCopen hpatch).strictLocalPatch

/--
Open lifted-quadratic data plus open-active lower-barrier exterior data gives
the local quadratic max-patch datum.

The active domain required by the patch proof is generated from the open sets
`C` and `V`, while the inactive compact is handled by finite Perron selection
using the lower barrier as the local old branch.
-/
theorem PerronLowerEnvelopeLocalQuadraticOpenBumpAt.maxPatchAt_of_openBarrierExteriorAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeLocalQuadraticOpenBumpAt C boundary F g B x J)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticOpenBarrierExteriorPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticMaxPatchAt C boundary F g B x J := by
  rcases hquad with ⟨κ, V, hκpos, hVopen, hV, hWltq, hqCont, hneg⟩
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
      J.gradient J.hessian z
  rcases hpatch κ V hκpos hVopen hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hboundaryAway, hKnhds, hlower⟩
  have hlocalOld : ∀ z : Point n, z ∈ K ->
      ∃ w : PerronFamily C boundary F g B.lower B.upper,
        ∀ᶠ y in nhdsWithin z K, q y <= w.fun y := by
    intro z hz
    exact ⟨⟨B.lower, B.lower_mem_perronClass⟩, hlower z hz⟩
  rcases B.exists_perronClass_eventually_dominate_on_isCompact
      hKcompact hKnhds hlocalOld with
    ⟨old, hold, hOld⟩
  let patched : Point n -> Real := fun y => Max.max (old y) (q y)
  have hlocal : ∀ z : Point n, z ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin z C ∧
            ViscositySubsolution D F v ∧
              patched z = v z ∧ patched =ᶠ[nhdsWithin z C] v := by
    intro z hz
    by_cases hzV : z ∈ V
    · rcases exists_activeDomain_inter_of_isOpen
        (C := C) (V := V) hCopen hVopen hz hzV with
        ⟨D, hDC, hDnhds, hDopen, hDinterior, hDV⟩
      have hqSubSym :
          ViscositySubsolution D F
            (fun y =>
              quadraticModel x
                (lowerEnvelope C
                    (perronEnvelope C boundary F g B.lower B.upper) x + κ)
                J.gradient (symHessian J.hessian) y) := by
        refine
          ViscositySubsolution.quadraticModel_of_mem_interior_of_hessianSymmetricInvariant
            (C := D) (F := F) (x0 := x)
            (r := lowerEnvelope C
              (perronEnvelope C boundary F g B.lower B.upper) x + κ)
            (p := J.gradient) (X := symHessian J.hessian)
            hFell hFinv (symHessian_isHermitian J.hessian) hDinterior ?_
        intro y hy
        have hnegOrig : F y (q y)
            (quadraticModelJetAt x J.gradient J.hessian y).gradient
            (quadraticModelJetAt x J.gradient J.hessian y).hessian < 0 :=
          hneg y (hDV y hy) (hDC hy)
        have hnegSym :
            F y
                (quadraticModel x
                  (lowerEnvelope C
                      (perronEnvelope C boundary F g B.lower B.upper) x + κ)
                  J.gradient (symHessian J.hessian) y)
                (quadraticModelJetAt x J.gradient (symHessian J.hessian) y).gradient
                (quadraticModelJetAt x J.gradient (symHessian J.hessian) y).hessian < 0 := by
          calc
            F y
                (quadraticModel x
                  (lowerEnvelope C
                      (perronEnvelope C boundary F g B.lower B.upper) x + κ)
                  J.gradient (symHessian J.hessian) y)
                (quadraticModelJetAt x J.gradient (symHessian J.hessian) y).gradient
                (quadraticModelJetAt x J.gradient (symHessian J.hessian) y).hessian
                = F y (q y)
                    (quadraticModelJetAt x J.gradient J.hessian y).gradient
                    (symHessian J.hessian) := by
                  rw [quadraticModel_symHessian,
                    quadraticModelJetAt_gradient_symHessian]
                  simp [q, quadraticModelJetAt]
            _ = F y (q y)
                    (quadraticModelJetAt x J.gradient J.hessian y).gradient
                    (quadraticModelJetAt x J.gradient J.hessian y).hessian := by
                  rw [← hFinv y (q y)
                    (quadraticModelJetAt x J.gradient J.hessian y).gradient
                    J.hessian]
                  simp [quadraticModelJetAt]
            _ < 0 := hnegOrig
        exact le_of_lt hnegSym
      have hqSub : ViscositySubsolution D F q := by
        simpa [q, quadraticModel_symHessian] using hqSubSym
      have holdD : ViscositySubsolution D F old :=
        hold.dirichletSubsolution.viscosity.restrict_of_subset_of_mem_nhdsWithin hDC hDopen
      refine ⟨D, patched, hDC, hDnhds, ?_, rfl, EventuallyEq.rfl⟩
      exact holdD.max hqSub
    · have hzK : z ∈ K := hcover z (Or.inl hz) hzV
      rcases hOld z hzK with ⟨hzle, hnear⟩
      refine ⟨C, old, subset_rfl, self_mem_nhdsWithin,
        hold.dirichletSubsolution.viscosity, ?_, ?_⟩
      · exact max_eq_left hzle
      · filter_upwards [hnear] with y hy
        exact max_eq_left hy
  have hboundary : BoundarySubsolutionOn boundary g patched := by
    intro y hy
    have hyK : y ∈ K := hcover y (Or.inr hy) (hboundaryAway y hy)
    rcases hOld y hyK with ⟨hyle, _hnear⟩
    have hpatched_y : patched y = old y := max_eq_left hyle
    rw [hpatched_y]
    exact hold.dirichletSubsolution.boundary_le hy
  have hsc : UpperSemicontinuousOn patched (C ∪ boundary) :=
    hold.dirichletSubsolution.upperSemicontinuousOn.sup
      (continuous_quadraticModel _ _ _ _).continuousOn.upperSemicontinuousOn
  have hdirichlet : DirichletSubsolutionOn C boundary F g patched :=
    DirichletSubsolutionOn.of_locally_eventuallyEqOn hlocal hboundary hsc
  have hlower : ∀ z : Point n, z ∈ C ∪ boundary -> B.lower z <= patched z := by
    intro z hz
    exact (hold.lower_le hz).trans (le_max_left (old z) (q z))
  have hupper : ∀ z : Point n, z ∈ C ∪ boundary -> patched z <= B.upper z :=
    hcomparison hdirichlet B.upper_dirichlet
  have hpatched : PerronClass C boundary F g B.lower B.upper patched :=
    ⟨hdirichlet, hlower, hupper⟩
  refine ⟨κ, V, old, hκpos, hV, hWltq, hqCont, hneg, hold, ?_⟩
  simpa [patched, q] using hpatched

/--
Global open lifted-quadratic data plus open-active lower-barrier exterior data
gives the global local quadratic max-patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticOpenBump.localQuadraticMaxPatch_of_openBarrierExterior
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeLocalQuadraticOpenBump C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticOpenBarrierExteriorPatch C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hquad x hx J hJ hneg).maxPatchAt_of_openBarrierExteriorAt
    hcomparison hFell hFinv hCopen (hpatch x hx J hJ hneg)

/--
Operator continuity reduces the local quadratic max-patch step to
open-active lower-barrier exterior data.
-/
theorem OperatorContinuous.perronLowerEnvelope_localQuadraticMaxPatch_of_openBarrierExterior
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticOpenBarrierExteriorPatch C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B :=
  hF.perronLowerEnvelope_localQuadraticOpenBump.localQuadraticMaxPatch_of_openBarrierExterior
    hcomparison hFell hFinv hCopen hpatch

/--
The local-germ quadratic gluing datum supplies the max-patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticGluingAt.localQuadraticMaxPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hglue :
      PerronLowerEnvelopeLocalQuadraticGluingAt C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticMaxPatchAt C boundary F g B x J := by
  rcases hglue with
    ⟨κ, V, old, hκpos, hV, hWltq, hqCont, hneg, hold,
      hlocal, hboundary, hupper⟩
  refine ⟨κ, V, old, hκpos, hV, hWltq, hqCont, hneg, hold, ?_⟩
  exact PerronClass.max_patch_of_locally_eventuallyEq
    hold hlocal hboundary
    (hold.dirichletSubsolution.upperSemicontinuousOn.sup
      (continuous_quadraticModel _ _ _ _).continuousOn.upperSemicontinuousOn) hupper

/--
The global local-germ quadratic gluing datum supplies the global max-patch
datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticGluing.localQuadraticMaxPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hglue : PerronLowerEnvelopeLocalQuadraticGluing C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hglue x hx J hJ hneg).localQuadraticMaxPatchAt

/--
The quadratic max-patch datum gives the existing strict local-patch interface.

The only proof work here is turning pointwise strict improvement at `x` into a
relative neighborhood where the lifted quadratic is above an intermediate
level; this is exactly where continuity of the lifted quadratic is used.
-/
theorem PerronLowerEnvelopeLocalQuadraticMaxPatchAt.strictLocalPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticMaxPatchAt C boundary F g B x J) :
    PerronLowerEnvelopeStrictLocalPatchAt C boundary F g B x := by
  rcases hpatch with
    ⟨κ, V, old, _hκpos, hV, hWltq, hqCont, _hneg, hold, hmax⟩
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
      J.gradient J.hessian z
  rcases exists_between hWltq with ⟨a, hWlta, haqx⟩
  have hqAbove : {y : Point n | a < q y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp hqCont.lowerSemicontinuousWithinAt a haqx
  refine ⟨a, V ∩ {y : Point n | a < q y}, old, q,
    Filter.inter_mem hV hqAbove, ?_, hWlta, hold, ?_⟩
  · intro y hy
    exact hy.2
  · simpa [q] using hmax

/--
The global quadratic max-patch datum gives the existing global strict
local-patch interface.
-/
theorem PerronLowerEnvelopeLocalQuadraticMaxPatch.strictLocalPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch : PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B) :
    PerronLowerEnvelopeStrictLocalPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).strictLocalPatchAt

end ViscositySolns
