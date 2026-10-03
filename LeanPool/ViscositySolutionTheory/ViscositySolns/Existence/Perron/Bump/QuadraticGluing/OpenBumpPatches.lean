/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OuterSemijetPatches

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Quadratic gluing data for the Perron bump step (OpenBumpPatches)

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
Bent open lifted-quadratic data plus a localized lower-barrier piecewise patch
gives the strict patch needed for Perron's contradiction.
-/
theorem PerronLowerEnvelopeBentQuadraticOpenBumpAt.strictPatchAt_of_localizedLowerPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeBentQuadraticOpenBumpAt C boundary F g B x J)
    (hx : x ∈ C)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticLocalizedLowerPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeStrictPatchAt C boundary F g B x := by
  rcases hquad with
    ⟨δ, γ, V, hδpos, hγpos, hVopen, hV, hWltq, hqCont, hneg⟩
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  rcases hpatch δ γ V hδpos hγpos hVopen hV hWltq hqCont hneg with
    ⟨patched, hlocalMax, hlocalLower, hboundaryEq, hboundarySC, hlower⟩
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
      have hlowerD : ViscositySubsolution D F B.lower :=
        B.lower_dirichlet.viscosity.restrict_of_subset_of_mem_nhdsWithin hDC hDopen
      have hpatchedLocal :
          patched =ᶠ[nhdsWithin z C] (fun y => Max.max (B.lower y) (q y)) :=
        hlocalMax z hz hzV
      have hpatched_z :
          patched z = Max.max (B.lower z) (q z) :=
        hpatchedLocal.self_of_nhdsWithin hz
      refine ⟨D, (fun y => Max.max (B.lower y) (q y)), hDC, hDnhds,
        ?_, hpatched_z, hpatchedLocal⟩
      exact hlowerD.max hqSub
    · have hpatchedLocal : patched =ᶠ[nhdsWithin z C] B.lower :=
        hlocalLower z hz hzV
      have hpatched_z : patched z = B.lower z :=
        hpatchedLocal.self_of_nhdsWithin hz
      exact ⟨C, B.lower, subset_rfl, self_mem_nhdsWithin,
        B.lower_dirichlet.viscosity, hpatched_z, hpatchedLocal⟩
  have hboundary : BoundarySubsolutionOn boundary g patched := by
    intro y hy
    rw [hboundaryEq y hy]
    exact B.lower_dirichlet.boundary_le hy
  have hdirichlet : DirichletSubsolutionOn C boundary F g patched :=
    DirichletSubsolutionOn.of_locally_eventuallyEqOn hlocal hboundary
      (UpperSemicontinuousOn.union_of_isOpen_domain
        hCopen (ViscositySubsolution.of_locally_eventuallyEqOn hlocal).1 hboundarySC)
  have hupper : ∀ z : Point n, z ∈ C ∪ boundary -> patched z <= B.upper z :=
    hcomparison hdirichlet B.upper_dirichlet
  have hpatched : PerronClass C boundary F g B.lower B.upper patched :=
    ⟨hdirichlet, hlower, hupper⟩
  have hxV : x ∈ V := mem_of_mem_nhdsWithin hx hV
  have hpatchedLocalAtX :
      patched =ᶠ[nhdsWithin x C] (fun y => Max.max (B.lower y) (q y)) :=
    hlocalMax x hx hxV
  rcases exists_between hWltq with ⟨a, hWlta, haqx⟩
  have hqAbove : {y : Point n | a < q y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp hqCont.lowerSemicontinuousWithinAt a haqx
  refine ⟨a,
    {y : Point n | patched y = Max.max (B.lower y) (q y) ∧ a < q y},
    patched, ?_, ?_, hWlta, hpatched⟩
  · filter_upwards [hpatchedLocalAtX, hqAbove] with y hyEq hyAbove
    exact ⟨hyEq, hyAbove⟩
  · intro y hy
    rw [hy.1]
    exact hy.2.trans_le (le_max_right (B.lower y) (q y))

/--
Global bent open lifted-quadratic data plus localized lower-barrier piecewise
patches gives the global strict patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticOpenBump.strictPatch_of_localizedLowerPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeBentQuadraticOpenBump C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticLocalizedLowerPatch C boundary F g B) :
    PerronLowerEnvelopeStrictPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hquad x hx J hJ hneg).strictPatchAt_of_localizedLowerPatchAt
    hx hcomparison hFell hFinv hCopen (hpatch x hx J hJ hneg)

/--
Operator continuity reduces the strict patch step to localized bent
lower-barrier piecewise patch data.
-/
theorem OperatorContinuous.perronLowerEnvelope_strictPatch_of_bentLocalizedLowerPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticLocalizedLowerPatch C boundary F g B) :
    PerronLowerEnvelopeStrictPatch C boundary F g B :=
  hF.perronLowerEnvelope_bentQuadraticOpenBump
    |>.strictPatch_of_localizedLowerPatch
      hcomparison hFell hFinv hCopen hpatch

/--
Bent open lifted-quadratic data plus a shrinkable localized lower-barrier
piecewise patch gives the strict patch needed for Perron's contradiction.
-/
theorem PerronLowerEnvelopeBentQuadraticOpenBumpAt.strictPatchAt_of_shrinkingLocalizedLowerPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeBentQuadraticOpenBumpAt C boundary F g B x J)
    (hx : x ∈ C)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticShrinkingLocalizedLowerPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeStrictPatchAt C boundary F g B x := by
  rcases hquad with
    ⟨δ, γ, V, hδpos, hγpos, hVopen, hV, hWltq, hqCont, hneg⟩
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  rcases hpatch δ γ V hδpos hγpos hVopen hV hWltq hqCont hneg with
    ⟨P, patched, hPopen, hP, hPV, hlocalMax, hlocalLower, hboundaryEq, hboundarySC, hlower⟩
  have hlocal : ∀ z : Point n, z ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin z C ∧
            ViscositySubsolution D F v ∧
              patched z = v z ∧ patched =ᶠ[nhdsWithin z C] v := by
    intro z hz
    by_cases hzP : z ∈ P
    · rcases exists_activeDomain_inter_of_isOpen
        (C := C) (V := P) hCopen hPopen hz hzP with
        ⟨D, hDC, hDnhds, hDopen, hDinterior, hDP⟩
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
          hneg y (hPV y (hDP y hy)) (hDC hy)
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
      have hlowerD : ViscositySubsolution D F B.lower :=
        B.lower_dirichlet.viscosity.restrict_of_subset_of_mem_nhdsWithin hDC hDopen
      have hpatchedLocal :
          patched =ᶠ[nhdsWithin z C] (fun y => Max.max (B.lower y) (q y)) :=
        hlocalMax z hz hzP
      have hpatched_z :
          patched z = Max.max (B.lower z) (q z) :=
        hpatchedLocal.self_of_nhdsWithin hz
      refine ⟨D, (fun y => Max.max (B.lower y) (q y)), hDC, hDnhds,
        ?_, hpatched_z, hpatchedLocal⟩
      exact hlowerD.max hqSub
    · have hpatchedLocal : patched =ᶠ[nhdsWithin z C] B.lower :=
        hlocalLower z hz hzP
      have hpatched_z : patched z = B.lower z :=
        hpatchedLocal.self_of_nhdsWithin hz
      exact ⟨C, B.lower, subset_rfl, self_mem_nhdsWithin,
        B.lower_dirichlet.viscosity, hpatched_z, hpatchedLocal⟩
  have hboundary : BoundarySubsolutionOn boundary g patched := by
    intro y hy
    rw [hboundaryEq y hy]
    exact B.lower_dirichlet.boundary_le hy
  have hdirichlet : DirichletSubsolutionOn C boundary F g patched :=
    DirichletSubsolutionOn.of_locally_eventuallyEqOn hlocal hboundary
      (UpperSemicontinuousOn.union_of_isOpen_domain
        hCopen (ViscositySubsolution.of_locally_eventuallyEqOn hlocal).1 hboundarySC)
  have hupper : ∀ z : Point n, z ∈ C ∪ boundary -> patched z <= B.upper z :=
    hcomparison hdirichlet B.upper_dirichlet
  have hpatched : PerronClass C boundary F g B.lower B.upper patched :=
    ⟨hdirichlet, hlower, hupper⟩
  have hxP : x ∈ P := mem_of_mem_nhdsWithin hx hP
  have hpatchedLocalAtX :
      patched =ᶠ[nhdsWithin x C] (fun y => Max.max (B.lower y) (q y)) :=
    hlocalMax x hx hxP
  rcases exists_between hWltq with ⟨a, hWlta, haqx⟩
  have hqAbove : {y : Point n | a < q y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp hqCont.lowerSemicontinuousWithinAt a haqx
  refine ⟨a,
    {y : Point n | patched y = Max.max (B.lower y) (q y) ∧ a < q y},
    patched, ?_, ?_, hWlta, hpatched⟩
  · filter_upwards [hpatchedLocalAtX, hqAbove] with y hyEq hyAbove
    exact ⟨hyEq, hyAbove⟩
  · intro y hy
    rw [hy.1]
    exact hy.2.trans_le (le_max_right (B.lower y) (q y))

/--
Global bent open lifted-quadratic data plus shrinkable localized
lower-barrier patches gives the global strict patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticOpenBump.strictPatch_of_shrinkingLocalizedLowerPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeBentQuadraticOpenBump C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticShrinkingLocalizedLowerPatch C boundary F g B) :
    PerronLowerEnvelopeStrictPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hquad x hx J hJ hneg).strictPatchAt_of_shrinkingLocalizedLowerPatchAt
    hx hcomparison hFell hFinv hCopen (hpatch x hx J hJ hneg)

/--
Operator continuity reduces the strict patch step to shrinkable localized bent
lower-barrier piecewise patch data.
-/
theorem OperatorContinuous.perronLowerEnvelope_strictPatch_of_bentShrinkingLocalizedLowerPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hpatch :
      PerronLowerEnvelopeBentQuadraticShrinkingLocalizedLowerPatch C boundary F g B) :
    PerronLowerEnvelopeStrictPatch C boundary F g B :=
  hF.perronLowerEnvelope_bentQuadraticOpenBump
    |>.strictPatch_of_shrinkingLocalizedLowerPatch
      hcomparison hFell hFinv hCopen hpatch

/--
A chosen bent localized lower-barrier patch gives the strict patch needed for
Perron's contradiction.
-/
theorem PerronLowerEnvelopeBentQuadraticChosenLocalizedLowerPatchAt.strictPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hchosen :
      PerronLowerEnvelopeBentQuadraticChosenLocalizedLowerPatchAt
        C boundary F g B x J)
    (hx : x ∈ C)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C) :
    PerronLowerEnvelopeStrictPatchAt C boundary F g B x := by
  rcases hchosen with
    ⟨δ, γ, V, P, patched, hδpos, hγpos, hVopen, hV, hWltq,
      hqCont, hneg, hPopen, hP, hPV, hlocalMax, hlocalLower,
      hboundaryEq, hboundarySC, hlower⟩
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  have hlocal : ∀ z : Point n, z ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin z C ∧
            ViscositySubsolution D F v ∧
              patched z = v z ∧ patched =ᶠ[nhdsWithin z C] v := by
    intro z hz
    by_cases hzP : z ∈ P
    · rcases exists_activeDomain_inter_of_isOpen
        (C := C) (V := P) hCopen hPopen hz hzP with
        ⟨D, hDC, hDnhds, hDopen, hDinterior, hDP⟩
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
          hneg y (hPV y (hDP y hy)) (hDC hy)
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
      have hlowerD : ViscositySubsolution D F B.lower :=
        B.lower_dirichlet.viscosity.restrict_of_subset_of_mem_nhdsWithin hDC hDopen
      have hpatchedLocal :
          patched =ᶠ[nhdsWithin z C] (fun y => Max.max (B.lower y) (q y)) :=
        hlocalMax z hz hzP
      have hpatched_z :
          patched z = Max.max (B.lower z) (q z) :=
        hpatchedLocal.self_of_nhdsWithin hz
      refine ⟨D, (fun y => Max.max (B.lower y) (q y)), hDC, hDnhds,
        ?_, hpatched_z, hpatchedLocal⟩
      exact hlowerD.max hqSub
    · have hpatchedLocal : patched =ᶠ[nhdsWithin z C] B.lower :=
        hlocalLower z hz hzP
      have hpatched_z : patched z = B.lower z :=
        hpatchedLocal.self_of_nhdsWithin hz
      exact ⟨C, B.lower, subset_rfl, self_mem_nhdsWithin,
        B.lower_dirichlet.viscosity, hpatched_z, hpatchedLocal⟩
  have hboundary : BoundarySubsolutionOn boundary g patched := by
    intro y hy
    rw [hboundaryEq y hy]
    exact B.lower_dirichlet.boundary_le hy
  have hdirichlet : DirichletSubsolutionOn C boundary F g patched :=
    DirichletSubsolutionOn.of_locally_eventuallyEqOn hlocal hboundary
      (UpperSemicontinuousOn.union_of_isOpen_domain
        hCopen (ViscositySubsolution.of_locally_eventuallyEqOn hlocal).1 hboundarySC)
  have hupper : ∀ z : Point n, z ∈ C ∪ boundary -> patched z <= B.upper z :=
    hcomparison hdirichlet B.upper_dirichlet
  have hpatched : PerronClass C boundary F g B.lower B.upper patched :=
    ⟨hdirichlet, hlower, hupper⟩
  have hxP : x ∈ P := mem_of_mem_nhdsWithin hx hP
  have hpatchedLocalAtX :
      patched =ᶠ[nhdsWithin x C] (fun y => Max.max (B.lower y) (q y)) :=
    hlocalMax x hx hxP
  rcases exists_between hWltq with ⟨a, hWlta, haqx⟩
  have hqAbove : {y : Point n | a < q y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp hqCont.lowerSemicontinuousWithinAt a haqx
  refine ⟨a,
    {y : Point n | patched y = Max.max (B.lower y) (q y) ∧ a < q y},
    patched, ?_, ?_, hWlta, hpatched⟩
  · filter_upwards [hpatchedLocalAtX, hqAbove] with y hyEq hyAbove
    exact ⟨hyEq, hyAbove⟩
  · intro y hy
    rw [hy.1]
    exact hy.2.trans_le (le_max_right (B.lower y) (q y))

/--
Global chosen bent localized lower-barrier patches give the global strict
patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticChosenLocalizedLowerPatch.strictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hchosen :
      PerronLowerEnvelopeBentQuadraticChosenLocalizedLowerPatch C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C) :
    PerronLowerEnvelopeStrictPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hchosen x hx J hJ hneg).strictPatchAt
    hx hcomparison hFell hFinv hCopen

/--
Source-radius closed-ball annulus data gives the global strict patch
interface.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatch.strictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceClosedBallAnnulusPatch
        C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C) :
    PerronLowerEnvelopeStrictPatch C boundary F g B :=
  hpatch.chosenPatch.strictPatch hcomparison hFell hFinv hCopen

/--
Source-radius compact-inactive data gives the strict patch by finite Perron
selection on the inactive compact set.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceCompactInactivePatchAt.strictPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceCompactInactivePatchAt
        C boundary F g B x J)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C) :
    PerronLowerEnvelopeStrictPatchAt C boundary F g B x := by
  rcases hpatch with
    ⟨γ, r, V, K, hγpos, hrpos, hVopen, hV, hballV, hWltq,
      hqCont, hneg, hKcompact, hcoverC, hcoverBoundary, hKnhds,
      hlocalOld⟩
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let P : Set (Point n) := Metric.ball x r
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
    by_cases hzP : z ∈ P
    · rcases exists_activeDomain_inter_of_isOpen
        (C := C) (V := P) hCopen Metric.isOpen_ball hz hzP with
        ⟨D, hDC, hDnhds, hDopen, hDinterior, hDP⟩
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
        have hyP : y ∈ P := hDP y hy
        have hnegOrig : F y (q y)
            (quadraticModelJetAt x J.gradient Xb y).gradient
            (quadraticModelJetAt x J.gradient Xb y).hessian < 0 :=
          hneg y (hballV y (by simpa [P] using hyP)) (hDC hy)
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
        hold.dirichletSubsolution.viscosity.restrict_of_subset_of_mem_nhdsWithin
          hDC hDopen
      refine ⟨D, patched, hDC, hDnhds, ?_, rfl, EventuallyEq.rfl⟩
      exact holdD.max hqSub
    · have hzK : z ∈ K := hcoverC z hz (by simpa [P] using hzP)
      rcases hOld z hzK with ⟨hzle, hnear⟩
      refine ⟨C, old, subset_rfl, self_mem_nhdsWithin,
        hold.dirichletSubsolution.viscosity, ?_, ?_⟩
      · exact max_eq_left hzle
      · filter_upwards [hnear] with y hy
        exact max_eq_left hy
  have hboundary : BoundarySubsolutionOn boundary g patched := by
    intro y hy
    have hyK : y ∈ K := hcoverBoundary y hy
    rcases hOld y hyK with ⟨hyle, _hnear⟩
    have hpatched_y : patched y = old y := max_eq_left hyle
    rw [hpatched_y]
    exact hold.dirichletSubsolution.boundary_le hy
  have hdirichlet : DirichletSubsolutionOn C boundary F g patched :=
    DirichletSubsolutionOn.of_locally_eventuallyEqOn hlocal hboundary
      (hold.dirichletSubsolution.upperSemicontinuousOn.sup
        (continuous_quadraticModel _ _ _ _).continuousOn.upperSemicontinuousOn)
  have hlower : ∀ z : Point n, z ∈ C ∪ boundary -> B.lower z <= patched z := by
    intro z hz
    exact (hold.lower_le hz).trans (le_max_left (old z) (q z))
  have hupper : ∀ z : Point n, z ∈ C ∪ boundary -> patched z <= B.upper z :=
    hcomparison hdirichlet B.upper_dirichlet
  have hpatched : PerronClass C boundary F g B.lower B.upper patched :=
    ⟨hdirichlet, hlower, hupper⟩
  have hxP : x ∈ P := by
    simpa [P, Metric.mem_ball, dist_self] using hrpos
  have hPnhds : P ∈ nhdsWithin x C :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hrpos)
  rcases exists_between hWltq with ⟨a, hWlta, haqx⟩
  have hqAbove : {y : Point n | a < q y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp hqCont.lowerSemicontinuousWithinAt a haqx
  refine ⟨a, P ∩ {y : Point n | a < q y}, patched, ?_, ?_, hWlta, hpatched⟩
  · exact Filter.inter_mem hPnhds hqAbove
  · intro y hy
    exact hy.2.trans_le (le_max_right (old y) (q y))

/--
Global source-radius compact-inactive data gives the global strict patch
interface.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceCompactInactivePatch.strictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceCompactInactivePatch
        C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C) :
    PerronLowerEnvelopeStrictPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).strictPatchAt
    hcomparison hFell hFinv hCopen

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt

/--
Source outer-annulus lower-envelope data gives a strict patch by patching
directly over an already admissible old function that agrees with the Perron
envelope on the domain.

This is the direct source-proof variant of the annulus construction: on the
transition annulus the source estimate gives `q < W_*`, local boundedness gives
`W_* <= W`, and the supplied identity gives `W = old`. No Perron-family branch
selection or branch lower-semicontinuity is used.
-/
theorem strictPatchAt_of_old_eq_perronEnvelope
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt
        C boundary F g B x J)
    (old : Point n -> Real)
    (hold : PerronClass C boundary F g B.lower B.upper old)
    (hOldEq : Set.EqOn old
      (perronEnvelope C boundary F g B.lower B.upper) C)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerBddBelow : ∀ z : Point n, z ∈ C ∪ boundary ->
      (nhdsWithin z C).IsBoundedUnder (· >= ·) B.lower) :
    PerronLowerEnvelopeStrictPatchAt C boundary F g B x := by
  rcases hpatch with
    ⟨γ, r, V, hγpos, hrpos, hVopen, hV, hballV, hclosedBallC,
      hboundaryOutside, hWltq, hqCont, hneg, hlowerAnnulus⟩
  classical
  let W : Point n -> Real := perronEnvelope C boundary F g B.lower B.upper
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let P : Set (Point n) := Metric.ball x r
  let K : Set (Point n) := {z : Point n | 3 * r / 4 <= dist z x ∧ dist z x <= r}
  have hOldK : ∀ y : Point n, y ∈ K -> q y <= old y := by
    intro y hyK
    have hyClosed : y ∈ Metric.closedBall x r := by
      simpa [K, Metric.mem_closedBall] using hyK.2
    have hyC : y ∈ C := hclosedBallC y hyClosed
    have hle :
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) y <=
          perronEnvelope C boundary F g B.lower B.upper y :=
      lowerEnvelope_le hyC
        (B.perronEnvelope_isBoundedUnder_ge (hlowerBddBelow y (Or.inl hyC)))
    have hqW : q y < W y := by
      exact lt_of_lt_of_le (by simpa [q, K] using hlowerAnnulus y hyK) hle
    have hOld : old y = W y := by
      simpa [W] using hOldEq hyC
    exact le_of_lt (by
      rw [hOld]
      exact hqW)
  have htransition : ∀ z : Point n, z ∈ C -> z ∉ P ->
      ∀ᶠ y in nhdsWithin z C, y ∉ P ∨ y ∈ K := by
    intro z _hzC hzNotBall
    simpa only [P, K, Set.mem_ofPred_eq] using
      eventually_not_mem_ball_or_mem_outerAnnulus (C := C) hrpos hzNotBall
  have hboundaryAway : ∀ z : Point n, z ∈ boundary -> z ∉ P := by
    intro z hzBoundary hzP
    exact hboundaryOutside z hzBoundary
      (hclosedBallC z (Metric.ball_subset_closedBall (by simpa [P] using hzP)))
  let patched : Point n -> Real := fun y =>
    if y ∈ P then Max.max (old y) (q y) else old y
  have hlocal : ∀ z : Point n, z ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin z C ∧
            ViscositySubsolution D F v ∧
              patched z = v z ∧ patched =ᶠ[nhdsWithin z C] v := by
    intro z hz
    by_cases hzP : z ∈ P
    · rcases exists_activeDomain_inter_of_isOpen
        (C := C) (V := P) hCopen Metric.isOpen_ball hz hzP with
        ⟨D, hDC, hDnhds, hDopen, hDinterior, hDP⟩
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
        have hyP : y ∈ P := hDP y hy
        have hnegOrig : F y (q y)
            (quadraticModelJetAt x J.gradient Xb y).gradient
            (quadraticModelJetAt x J.gradient Xb y).hessian < 0 :=
          hneg y (hballV y (by simpa [P] using hyP)) (hDC hy)
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
        hold.dirichletSubsolution.viscosity.restrict_of_subset_of_mem_nhdsWithin
          hDC hDopen
      have hpatchedLocal :
          patched =ᶠ[nhdsWithin z C] (fun y => Max.max (old y) (q y)) := by
        have hPnhds : P ∈ nhds z :=
          Metric.isOpen_ball.mem_nhds (by simpa [P] using hzP)
        filter_upwards [mem_nhdsWithin_of_mem_nhds hPnhds] with y hyP
        simp [patched, hyP]
      have hpatched_z : patched z = Max.max (old z) (q z) :=
        hpatchedLocal.self_of_nhdsWithin hz
      refine ⟨D, (fun y => Max.max (old y) (q y)), hDC, hDnhds,
        ?_, hpatched_z, hpatchedLocal⟩
      exact holdD.max hqSub
    · have hpatchedLocal : patched =ᶠ[nhdsWithin z C] old := by
        filter_upwards [htransition z hz (by simpa [P] using hzP)] with y hy
        rcases hy with hyP | hyK
        · have hyP' : y ∉ P := by
            simpa [P] using hyP
          simp [patched, hyP']
        · have hyq : q y <= old y := hOldK y hyK
          by_cases hyP' : y ∈ P
          · simp [patched, hyP', max_eq_left hyq]
          · simp [patched, hyP']
      have hpatched_z : patched z = old z := by
        simp [patched, hzP]
      exact ⟨C, old, subset_rfl, self_mem_nhdsWithin,
        hold.dirichletSubsolution.viscosity, hpatched_z, hpatchedLocal⟩
  have hboundary : BoundarySubsolutionOn boundary g patched := by
    intro y hy
    have hyP : y ∉ P := hboundaryAway y hy
    change (if y ∈ P then Max.max (old y) (q y) else old y) <= g y
    rw [ite_eq_right hyP]
    exact hold.dirichletSubsolution.boundary_le hy
  have hboundarySC : ∀ y ∈ boundary,
      UpperSemicontinuousWithinAt patched (C ∪ boundary) y := by
    intro y hy
    apply UpperSemicontinuousOn.piecewise_max_boundary
      hold.dirichletSubsolution.upperSemicontinuousOn
      (continuous_quadraticModel _ _ _ _)
      (Set.mem_union_right C hy)
    apply Or.inl
    intro hyClosure
    have hyClosed : y ∈ Metric.closedBall x r :=
      Metric.closure_ball_subset_closedBall hyClosure
    exact hboundaryOutside y hy (hclosedBallC y hyClosed)
  have hdirichlet : DirichletSubsolutionOn C boundary F g patched :=
    DirichletSubsolutionOn.of_locally_eventuallyEqOn hlocal hboundary
      (UpperSemicontinuousOn.union_of_isOpen_domain hCopen
        (ViscositySubsolution.of_locally_eventuallyEqOn hlocal).1 hboundarySC)
  have hlower : ∀ z : Point n, z ∈ C ∪ boundary -> B.lower z <= patched z := by
    intro z hz
    by_cases hzP : z ∈ P
    · change B.lower z <= (if z ∈ P then Max.max (old z) (q z) else old z)
      rw [ite_eq_left hzP]
      exact (hold.lower_le hz).trans (le_max_left (old z) (q z))
    · change B.lower z <= (if z ∈ P then Max.max (old z) (q z) else old z)
      rw [ite_eq_right hzP]
      exact hold.lower_le hz
  have hupper : ∀ z : Point n, z ∈ C ∪ boundary -> patched z <= B.upper z :=
    hcomparison hdirichlet B.upper_dirichlet
  have hpatched : PerronClass C boundary F g B.lower B.upper patched :=
    ⟨hdirichlet, hlower, hupper⟩
  have hPnhds : P ∈ nhdsWithin x C :=
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hrpos)
  rcases exists_between hWltq with ⟨a, hWlta, haqx⟩
  have hqAbove : {y : Point n | a < q y} ∈ nhdsWithin x C :=
    lowerSemicontinuousWithinAt_iff.mp hqCont.lowerSemicontinuousWithinAt a haqx
  refine ⟨a, P ∩ {y : Point n | a < q y}, patched, ?_, ?_, hWlta, hpatched⟩
  · exact Filter.inter_mem hPnhds hqAbove
  · intro y hy
    have hyP : y ∈ P := hy.1
    have hpatched_y : patched y = Max.max (old y) (q y) := by
      simp [patched, hyP]
    rw [hpatched_y]
    exact hy.2.trans_le (le_max_right (old y) (q y))

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatchAt

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch

/--
Global source outer-annulus lower-envelope data gives strict patches by
patching directly over an already admissible old function that agrees with the
Perron envelope on the domain.
-/
theorem strictPatch_of_old_eq_perronEnvelope
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch
        C boundary F g B)
    (old : Point n -> Real)
    (hold : PerronClass C boundary F g B.lower B.upper old)
    (hOldEq : Set.EqOn old
      (perronEnvelope C boundary F g B.lower B.upper) C)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerBddBelow : ∀ z : Point n, z ∈ C ∪ boundary ->
      (nhdsWithin z C).IsBoundedUnder (· >= ·) B.lower) :
    PerronLowerEnvelopeStrictPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).strictPatchAt_of_old_eq_perronEnvelope
    old hold hOldEq hcomparison hFell hFinv hCopen hlowerBddBelow

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopePatch

namespace PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch

/--
Legacy outer-annulus data gives the direct strict patch after forgetting its
unused branch lower-semicontinuity field.
-/
theorem strictPatch_of_old_eq_perronEnvelope
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch
        C boundary F g B)
    (old : Point n -> Real)
    (hold : PerronClass C boundary F g B.lower B.upper old)
    (hOldEq : Set.EqOn old
      (perronEnvelope C boundary F g B.lower B.upper) C)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C)
    (hlowerBddBelow : ∀ z : Point n, z ∈ C ∪ boundary ->
      (nhdsWithin z C).IsBoundedUnder (· >= ·) B.lower) :
    PerronLowerEnvelopeStrictPatch C boundary F g B :=
  hpatch.lowerEnvelopePatch.strictPatch_of_old_eq_perronEnvelope
    old hold hOldEq hcomparison hFell hFinv hCopen hlowerBddBelow

end PerronLowerEnvelopeBentQuadraticSourceOuterClosedBallLowerEnvelopeLscSelectionPatch

end ViscositySolns
