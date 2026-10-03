/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Bump.QuadraticGluing.OuterSemijetPatches

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Quadratic gluing data for the Perron bump step (CertifiedPatches)

This module connects lifted quadratics to strict local max patches.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
Source-radius transition-annulus selection data gives the strict patch by
selecting one old Perron branch on the compact transition set and patching
piecewise across the ball.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatchAt.strictPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatchAt
        C boundary F g B x J)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C) :
    PerronLowerEnvelopeStrictPatchAt C boundary F g B x := by
  rcases hpatch with
    ⟨γ, r, V, K, hγpos, hrpos, hVopen, hV, hballV, hWltq,
      hqCont, hneg, hKcompact, _hKself, hlocalOld, htransition,
      hboundaryAway⟩
  classical
  let δ : Real := γ * r ^ 2 / 8
  let Xb : Hessian n := J.hessian - γ • (1 : Hessian n)
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + δ)
      J.gradient Xb z
  let P : Set (Point n) := Metric.ball x r
  rcases B.exists_perronClass_dominate_on_isCompact hKcompact hlocalOld with
    ⟨old, hold, hOldK⟩
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
    have hyP : y ∉ P := fun h =>
      hboundaryAway y hy (Metric.ball_subset_closedBall h)
    change (if y ∈ P then Max.max (old y) (q y) else old y) <= g y
    rw [ite_eq_right hyP]
    exact hold.dirichletSubsolution.boundary_le hy
  have hsc : UpperSemicontinuousOn patched (C ∪ boundary) := by
    refine UpperSemicontinuousOn.of_eqOn_compl_closed_patch
      (K := Metric.closedBall x r) hCopen Metric.isClosed_closedBall
      hold.dirichletSubsolution.upperSemicontinuousOn
      (ViscositySubsolution.of_locally_eventuallyEqOn hlocal).1 ?_ hboundaryAway
    intro y hy
    have hyP : y ∉ P := fun h => hy (Metric.ball_subset_closedBall h)
    simp [patched, hyP]
  have hdirichlet : DirichletSubsolutionOn C boundary F g patched :=
    DirichletSubsolutionOn.of_locally_eventuallyEqOn hlocal hboundary hsc
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
    have hyP : y ∈ P := hy.1
    have hpatched_y : patched y = Max.max (old y) (q y) := by
      simp [patched, hyP]
    rw [hpatched_y]
    exact hy.2.trans_le (le_max_right (old y) (q y))

/--
Global source-radius transition-annulus selection data gives the global strict
patch interface.
-/
theorem PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch.strictPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeBentQuadraticSourceAnnulusSelectionPatch
        C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hCopen : IsOpen C) :
    PerronLowerEnvelopeStrictPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).strictPatchAt hcomparison hFell hFinv hCopen

/--
Lower-barrier exterior data supplies exterior compact-inactive data.
-/
theorem PerronLowerEnvelopeLocalQuadraticBarrierExteriorPatchAt.exteriorPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticBarrierExteriorPatchAt C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatchAt
      C boundary F g B x J := by
  intro κ V q hκpos hV hWltq hqCont hneg
  rcases hpatch κ V hκpos hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hboundaryAway, hKnhds, hlower, hactive⟩
  refine ⟨K, hKcompact, hcover, hboundaryAway, hKnhds, ?_, hactive⟩
  intro z hz
  exact ⟨⟨B.lower, B.lower_mem_perronClass⟩, hlower z hz⟩

/--
Global lower-barrier exterior data supplies global exterior compact-inactive
data.
-/
theorem PerronLowerEnvelopeLocalQuadraticBarrierExteriorPatch.exteriorPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticBarrierExteriorPatch C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveExteriorPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).exteriorPatchAt

/--
Boundary-safe compact-inactive data supplies the symmetrized certified datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticCompactInactiveBoundaryPatchAt.symCertifiedPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveBoundaryPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatchAt
      C boundary F g B x J := by
  intro κ V q hκpos hV hWltq hqCont hneg
  rcases hpatch κ V hκpos hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hKnhds, hlocalOld, hactive, hqBoundary⟩
  refine ⟨K, hKcompact, hcover, hKnhds, hlocalOld, hactive, ?_⟩
  intro old hold y hy
  exact max_le (hold.dirichletSubsolution.boundary_le hy) (hqBoundary y hy)

/--
Global boundary-safe compact-inactive data supplies the global symmetrized
certified datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticCompactInactiveBoundaryPatch.symCertifiedPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveBoundaryPatch C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatch
      C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).symCertifiedPatchAt

/--
Certified active-domain compact-inactive data supplies the quadratic-active
patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticCompactInactiveCertifiedPatchAt.quadraticPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hcert :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveCertifiedPatchAt
        C boundary F g B x J)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatchAt
      C boundary F g B x J := by
  rcases hcert with ⟨hJHerm, hcert⟩
  intro κ V q hκpos hV hWltq hqCont hneg
  rcases hcert κ V hκpos hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hKnhds, hlocalOld, hactive, hboundary⟩
  refine ⟨K, hKcompact, hcover, hKnhds, hlocalOld, ?_, hboundary⟩
  intro z hz hzV
  rcases hactive z hz hzV with ⟨D, hDC, hDnhds, hDopen, hDinterior, hDV⟩
  have hqSub : ViscositySubsolution D F q := by
    simpa [q] using
      (ViscositySubsolution.quadraticModel_of_mem_interior_of_hessianSymmetricInvariant
        (C := D) (F := F) (x0 := x)
        (r := lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        (p := J.gradient) (X := J.hessian)
        hFell hFinv hJHerm hDinterior
        (by
          intro y hy
          exact le_of_lt (hneg y (hDV y hy) (hDC hy))))
  exact ⟨D, hDC, hDnhds, hDopen, hDV, hqSub⟩

/--
Global certified active-domain data supplies the global quadratic-active
patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticCompactInactiveCertifiedPatch.quadraticPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hcert :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveCertifiedPatch C boundary F g B)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hcert x hx J hJ hneg).quadraticPatchAt hFell hFinv

/--
Symmetrized certified active-domain compact-inactive data supplies the
quadratic-active patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatchAt.quadraticPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hcert :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatchAt
        C boundary F g B x J)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatchAt
      C boundary F g B x J := by
  intro κ V q hκpos hV hWltq hqCont hneg
  rcases hcert κ V hκpos hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hKnhds, hlocalOld, hactive, hboundary⟩
  refine ⟨K, hKcompact, hcover, hKnhds, hlocalOld, ?_, hboundary⟩
  intro z hz hzV
  rcases hactive z hz hzV with ⟨D, hDC, hDnhds, hDopen, hDinterior, hDV⟩
  have hqSubSym :
      ViscositySubsolution D F
        (fun y =>
          quadraticModel x
            (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
            J.gradient (symHessian J.hessian) y) := by
    refine
      ViscositySubsolution.quadraticModel_of_mem_interior_of_hessianSymmetricInvariant
        (C := D) (F := F) (x0 := x)
        (r := lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
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
              (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
              J.gradient (symHessian J.hessian) y)
            (quadraticModelJetAt x J.gradient (symHessian J.hessian) y).gradient
            (quadraticModelJetAt x J.gradient (symHessian J.hessian) y).hessian < 0 := by
      calc
        F y
            (quadraticModel x
              (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
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
  exact ⟨D, hDC, hDnhds, hDopen, hDV, hqSub⟩

/--
Global symmetrized certified active-domain data supplies the global
quadratic-active patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatch.quadraticPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hcert :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSymCertifiedPatch C boundary F g B)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hcert x hx J hJ hneg).quadraticPatchAt hFell hFinv

/--
The quadratic-active compact-inactive datum supplies the local
subsolution-patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatchAt.subsolutionPatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatchAt
        C boundary F g B x J) :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatchAt
      C boundary F g B x J := by
  intro κ V q hκpos hV hWltq hqCont hneg
  rcases hpatch κ V hκpos hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hKnhds, hlocalOld, hqLocal, hboundary⟩
  refine ⟨K, hKcompact, hcover, hKnhds, hlocalOld, ?_⟩
  intro old hold hOld
  refine ⟨?_, hboundary old hold⟩
  intro z hz hzV
  rcases hqLocal z hz hzV with ⟨D, hDC, hDnhds, hDopen, _hDV, hqSub⟩
  have holdD : ViscositySubsolution D F old :=
    hold.dirichletSubsolution.viscosity.restrict_of_subset_of_mem_nhdsWithin hDC hDopen
  refine ⟨D, fun y => Max.max (old y) (q y), hDC, hDnhds, holdD.max hqSub, rfl, ?_⟩
  exact EventuallyEq.rfl

/--
Global quadratic-active compact-inactive data supplies the global
subsolution-patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatch.subsolutionPatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveQuadraticPatch C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hpatch x hx J hJ hneg).subsolutionPatchAt

/--
Local lifted-quadratic data plus compact-inactive selection gives the
local-germ quadratic gluing datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticBumpAt.localQuadraticGluingAt_of_compactInactiveSelectionAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeLocalQuadraticBumpAt C boundary F g B x J)
    (hselect :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSelectionAt C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticGluingAt C boundary F g B x J := by
  rcases hquad with ⟨κ, V, hκpos, hV, hWltq, hqCont, hneg⟩
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
      J.gradient J.hessian z
  rcases hselect κ V hκpos hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hKnhds, hlocalOld, hqLocal, hbounds⟩
  rcases B.exists_perronClass_eventually_dominate_on_isCompact
      hKcompact hKnhds hlocalOld with
    ⟨old, hold, hOld⟩
  rcases hbounds old hold hOld with ⟨hboundary, hupper⟩
  refine ⟨κ, V, old, hκpos, hV, hWltq, hqCont, hneg, hold, ?_,
    hboundary, hupper⟩
  intro z hz
  by_cases hzV : z ∈ V
  · rcases hqLocal z hz hzV with ⟨v, hv, hqz, hqv⟩
    refine ⟨fun y => Max.max (old y) (v y), hold.dirichletSubsolution.viscosity.max hv,
      ?_, ?_⟩
    · simp [hqz]
    · filter_upwards [hqv] with y hy
      simp [hy]
  · have hzK : z ∈ K := hcover z hz hzV
    rcases hOld z hzK with ⟨hzle, hnear⟩
    refine ⟨old, hold.dirichletSubsolution.viscosity, max_eq_left hzle, ?_⟩
    filter_upwards [hnear] with y hyle
    exact max_eq_left hyle

/--
Global local lifted-quadratic data plus compact-inactive selection gives the
global local-germ quadratic gluing datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticBump.localQuadraticGluing_of_compactInactiveSelection
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeLocalQuadraticBump C boundary F g B)
    (hselect :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSelection C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticGluing C boundary F g B := by
  intro x hx J hJ hneg
  exact (hquad x hx J hJ hneg).localQuadraticGluingAt_of_compactInactiveSelectionAt
    (hselect x hx J hJ hneg)

/--
Operator continuity reduces local-germ Perron bump gluing to the
compact-inactive selection problem.
-/
theorem OperatorContinuous.perronLowerEnvelope_localQuadraticGluing_of_compactInactiveSelection
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    (hselect :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSelection C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticGluing C boundary F g B :=
  hF.perronLowerEnvelope_localQuadraticBump.localQuadraticGluing_of_compactInactiveSelection
    hselect

/--
The explicit lifted-quadratic data plus patch selection gives branch-local
quadratic gluing at a failed contact.
-/
theorem PerronLowerEnvelopeLocalQuadraticBumpAt.branchGluingAt_of_patchSelectionAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeLocalQuadraticBumpAt C boundary F g B x J)
    (hselect :
      PerronLowerEnvelopeLocalQuadraticPatchSelectionAt C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticBranchGluingAt C boundary F g B x J := by
  rcases hquad with ⟨κ, V, hκpos, hV, hWltq, hqCont, hneg⟩
  rcases hselect κ V hκpos hV hWltq hqCont hneg with
    ⟨old, hold, hqLocal, hbranches, hboundary, hupper⟩
  exact ⟨κ, V, old, hκpos, hV, hWltq, hqCont, hneg, hold, hqLocal,
    hbranches, hboundary, hupper⟩

/--
Local lifted-quadratic data plus patch selection gives global branch-local
quadratic gluing.
-/
theorem PerronLowerEnvelopeLocalQuadraticBump.branchGluing_of_patchSelection
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeLocalQuadraticBump C boundary F g B)
    (hselect : PerronLowerEnvelopeLocalQuadraticPatchSelection C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticBranchGluing C boundary F g B := by
  intro x hx J hJ hneg
  exact (hquad x hx J hJ hneg).branchGluingAt_of_patchSelectionAt
    (hselect x hx J hJ hneg)

/--
Operator continuity reduces the branch-local Perron bump step to the explicit
patch-selection problem.
-/
theorem OperatorContinuous.perronLowerEnvelope_branchGluing_of_patchSelection
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    (hselect : PerronLowerEnvelopeLocalQuadraticPatchSelection C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticBranchGluing C boundary F g B :=
  hF.perronLowerEnvelope_localQuadraticBump.branchGluing_of_patchSelection hselect

/--
Branch-local quadratic gluing supplies the local-germ quadratic gluing datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticBranchGluingAt.localQuadraticGluingAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hbranch :
      PerronLowerEnvelopeLocalQuadraticBranchGluingAt C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticGluingAt C boundary F g B x J := by
  rcases hbranch with
    ⟨κ, V, old, hκpos, hV, hWltq, hqCont, hneg, hold, hqLocal,
      hbranches, hboundary, hupper⟩
  refine ⟨κ, V, old, hκpos, hV, hWltq, hqCont, hneg, hold, ?_,
    hboundary, hupper⟩
  intro z hz
  rcases hbranches z hz with hOld | hQ
  · rcases hOld with ⟨hzle, hnear⟩
    refine ⟨old, hold.dirichletSubsolution.viscosity, max_eq_left hzle, ?_⟩
    filter_upwards [hnear] with y hyle
    exact max_eq_left hyle
  · rcases hQ with ⟨hzV, hzle, hnear⟩
    rcases hqLocal z hz hzV with ⟨v, hvSub, hqzv, hqv⟩
    refine ⟨v, hvSub, ?_, ?_⟩
    · exact (max_eq_right hzle).trans hqzv
    · filter_upwards [hnear, hqv] with y hyle hqyv
      exact (max_eq_right hyle).trans hqyv

/--
The global branch-local quadratic gluing datum supplies the global local-germ
quadratic gluing datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticBranchGluing.localQuadraticGluing
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hbranch : PerronLowerEnvelopeLocalQuadraticBranchGluing C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticGluing C boundary F g B := by
  intro x hx J hJ hneg
  exact (hbranch x hx J hJ hneg).localQuadraticGluingAt

/--
Active-branch quadratic gluing supplies the local-germ quadratic gluing datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticActiveGluingAt.localQuadraticGluingAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hactive :
      PerronLowerEnvelopeLocalQuadraticActiveGluingAt C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticGluingAt C boundary F g B x J := by
  rcases hactive with
    ⟨κ, V, old, hκpos, hV, hWltq, hqCont, hneg, hold, hqSub,
      hbranches, hboundary, hupper⟩
  refine ⟨κ, V, old, hκpos, hV, hWltq, hqCont, hneg, hold, ?_,
    hboundary, hupper⟩
  intro z hz
  rcases hbranches z hz with hOld | hQ
  · rcases hOld with ⟨hzle, hnear⟩
    refine ⟨old, hold.dirichletSubsolution.viscosity, max_eq_left hzle, ?_⟩
    filter_upwards [hnear] with y hyle
    exact max_eq_left hyle
  · rcases hQ with ⟨hzle, hnear⟩
    let q : Point n -> Real := fun y =>
      quadraticModel x
        (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
        J.gradient J.hessian y
    refine ⟨q, hqSub, max_eq_right hzle, ?_⟩
    filter_upwards [hnear] with y hyle
    exact max_eq_right hyle

/--
The global active-branch quadratic gluing datum supplies the global local-germ
quadratic gluing datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticActiveGluing.localQuadraticGluing
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hactive : PerronLowerEnvelopeLocalQuadraticActiveGluing C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticGluing C boundary F g B := by
  intro x hx J hJ hneg
  exact (hactive x hx J hJ hneg).localQuadraticGluingAt

/--
Source-shaped local quadratic max-patch data at a failed lower-envelope
contact.

This records the remaining gluing output after the lifted quadratic has been
chosen: an old Perron-class member can be maxed with the lifted quadratic, and
the result is still Perron-admissible. The local negativity and continuity
fields keep the datum tied to the quadratic produced by the failed subjet
inequality.
-/
def PerronLowerEnvelopeLocalQuadraticMaxPatchAt
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) (x : Point n) (J : Jet n) :
    Prop :=
  ∃ κ : Real, ∃ V : Set (Point n), ∃ old : Point n -> Real,
    0 < κ ∧
      V ∈ nhdsWithin x C ∧
        lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x <
          quadraticModel x
            (lowerEnvelope C
              (perronEnvelope C boundary F g B.lower B.upper) x + κ)
            J.gradient J.hessian x ∧
          ContinuousWithinAt
            (fun z => quadraticModel x
              (lowerEnvelope C
                (perronEnvelope C boundary F g B.lower B.upper) x + κ)
              J.gradient J.hessian z)
            C x ∧
            (∀ z : Point n, z ∈ V -> z ∈ C ->
              F z
                  (quadraticModel x
                    (lowerEnvelope C
                      (perronEnvelope C boundary F g B.lower B.upper) x + κ)
                    J.gradient J.hessian z)
                  (quadraticModelJetAt x J.gradient J.hessian z).gradient
                  (quadraticModelJetAt x J.gradient J.hessian z).hessian < 0) ∧
              PerronClass C boundary F g B.lower B.upper old ∧
                PerronClass C boundary F g B.lower B.upper
                  (fun z => Max.max (old z)
                    (quadraticModel x
                      (lowerEnvelope C
                        (perronEnvelope C boundary F g B.lower B.upper) x + κ)
                      J.gradient J.hessian z))

/--
Local quadratic max-patch data at every failed lower-envelope subjet
inequality.
-/
def PerronLowerEnvelopeLocalQuadraticMaxPatch
    (C boundary : Set (Point n)) (F : Operator n) (g : Point n -> Real)
    (B : DirichletBarrierPair C boundary F g) : Prop :=
  ∀ x : Point n, x ∈ C -> ∀ J : Jet n,
    J ∈ Subjet C (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper)) x ->
      F x
          (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x)
          J.gradient J.hessian < 0 ->
        PerronLowerEnvelopeLocalQuadraticMaxPatchAt C boundary F g B x J

/--
Local lifted-quadratic data plus compact-inactive local patch data gives the
source-shaped local quadratic max-patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticBumpAt.localQuadraticMaxPatchAt_of_compactInactivePatchAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeLocalQuadraticBumpAt C boundary F g B x J)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactivePatchAt C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticMaxPatchAt C boundary F g B x J := by
  rcases hquad with ⟨κ, V, hκpos, hV, hWltq, hqCont, hneg⟩
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
      J.gradient J.hessian z
  rcases hpatch κ V hκpos hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hKnhds, hlocalOld, hpatchOld⟩
  rcases B.exists_perronClass_eventually_dominate_on_isCompact
      hKcompact hKnhds hlocalOld with
    ⟨old, hold, hOld⟩
  rcases hpatchOld old hold hOld with ⟨hactive, hboundary, hupper⟩
  refine ⟨κ, V, old, hκpos, hV, hWltq, hqCont, hneg, hold, ?_⟩
  refine PerronClass.max_patch_of_locally_eventuallyEqOn hold ?_ hboundary
    (hold.dirichletSubsolution.upperSemicontinuousOn.sup
      (continuous_quadraticModel _ _ _ _).continuousOn.upperSemicontinuousOn) hupper
  intro z hz
  by_cases hzV : z ∈ V
  · exact hactive z hz hzV
  · have hzK : z ∈ K := hcover z hz hzV
    rcases hOld z hzK with ⟨hzle, hnear⟩
    refine ⟨C, old, subset_rfl, self_mem_nhdsWithin,
      hold.dirichletSubsolution.viscosity, max_eq_left hzle, ?_⟩
    filter_upwards [hnear] with y hy
    exact max_eq_left hy

/--
Global local lifted-quadratic data plus compact-inactive local patch data gives
the global source-shaped local quadratic max-patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticBump.localQuadraticMaxPatch_of_compactInactivePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeLocalQuadraticBump C boundary F g B)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactivePatch C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hquad x hx J hJ hneg).localQuadraticMaxPatchAt_of_compactInactivePatchAt
    (hpatch x hx J hJ hneg)

/--
Operator continuity reduces the local quadratic max-patch step to
compact-inactive local patch data.
-/
theorem OperatorContinuous.perronLowerEnvelope_localQuadraticMaxPatch_of_compactInactivePatch
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactivePatch C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B :=
  hF.perronLowerEnvelope_localQuadraticBump.localQuadraticMaxPatch_of_compactInactivePatch
    hpatch

/--
Local lifted-quadratic data plus compact-inactive local subsolution-patch data
and comparison gives the source-shaped local quadratic max-patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticBumpAt.maxPatchAt_of_compactInactiveSubsolutionAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeLocalQuadraticBumpAt C boundary F g B x J)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticMaxPatchAt C boundary F g B x J := by
  rcases hquad with ⟨κ, V, hκpos, hV, hWltq, hqCont, hneg⟩
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
      J.gradient J.hessian z
  rcases hpatch κ V hκpos hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcover, hKnhds, hlocalOld, hpatchOld⟩
  rcases B.exists_perronClass_eventually_dominate_on_isCompact
      hKcompact hKnhds hlocalOld with
    ⟨old, hold, hOld⟩
  rcases hpatchOld old hold hOld with ⟨hactive, hboundary⟩
  let patched : Point n -> Real := fun y => Max.max (old y) (q y)
  have hlocal : ∀ z : Point n, z ∈ C ->
      ∃ D : Set (Point n), ∃ v : Point n -> Real,
        D ⊆ C ∧
          D ∈ nhdsWithin z C ∧
            ViscositySubsolution D F v ∧
              patched z = v z ∧ patched =ᶠ[nhdsWithin z C] v := by
    intro z hz
    by_cases hzV : z ∈ V
    · exact hactive z hz hzV
    · have hzK : z ∈ K := hcover z hz hzV
      rcases hOld z hzK with ⟨hzle, hnear⟩
      refine ⟨C, old, subset_rfl, self_mem_nhdsWithin,
        hold.dirichletSubsolution.viscosity, ?_, ?_⟩
      · exact max_eq_left hzle
      · filter_upwards [hnear] with y hy
        exact max_eq_left hy
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
Global local lifted-quadratic data plus compact-inactive local
subsolution-patch data and comparison gives the global source-shaped local
quadratic max-patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticBump.localQuadraticMaxPatch_of_compactInactiveSubsolution
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeLocalQuadraticBump C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatch
        C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact
    (hquad x hx J hJ hneg).maxPatchAt_of_compactInactiveSubsolutionAt
    hcomparison (hpatch x hx J hJ hneg)

/--
Operator continuity reduces the local quadratic max-patch step to
compact-inactive local subsolution-patch data plus comparison.
-/
theorem OperatorContinuous.perronLowerEnvelope_localQuadraticMaxPatch_of_compactInactiveSubsolution
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveSubsolutionPatch
        C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B :=
  hF.perronLowerEnvelope_localQuadraticBump.localQuadraticMaxPatch_of_compactInactiveSubsolution
    hcomparison hpatch

/--
Local lifted-quadratic data plus boundary-covered compact-inactive data gives
the source-shaped local quadratic max-patch datum.

The inactive compact covers both the inactive portion of `C` and the
Dirichlet boundary. After finite Perron selection, the selected old branch
dominates the lifted quadratic on the boundary, so the patched function agrees
with the old branch there.
-/
theorem PerronLowerEnvelopeLocalQuadraticBumpAt.maxPatchAt_of_compactInactiveCoveredAt
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} {x : Point n} {J : Jet n}
    (hquad : PerronLowerEnvelopeLocalQuadraticBumpAt C boundary F g B x J)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveCoveredPatchAt
        C boundary F g B x J) :
    PerronLowerEnvelopeLocalQuadraticMaxPatchAt C boundary F g B x J := by
  rcases hquad with ⟨κ, V, hκpos, hV, hWltq, hqCont, hneg⟩
  let q : Point n -> Real := fun z =>
    quadraticModel x
      (lowerEnvelope C (perronEnvelope C boundary F g B.lower B.upper) x + κ)
      J.gradient J.hessian z
  rcases hpatch κ V hκpos hV hWltq hqCont hneg with
    ⟨K, hKcompact, hcoverC, hcoverBoundary, hKnhds, hlocalOld, hactive⟩
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
    · rcases hactive z hz hzV with ⟨D, hDC, hDnhds, hDopen, hDinterior, hDV⟩
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
    · have hzK : z ∈ K := hcoverC z hz hzV
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
Global local lifted-quadratic data plus boundary-covered compact-inactive data
gives the global source-shaped local quadratic max-patch datum.
-/
theorem PerronLowerEnvelopeLocalQuadraticBump.localQuadraticMaxPatch_of_compactInactiveCovered
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g}
    (hquad : PerronLowerEnvelopeLocalQuadraticBump C boundary F g B)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveCoveredPatch C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B := by
  intro x hx J hJ hneg
  exact (hquad x hx J hJ hneg).maxPatchAt_of_compactInactiveCoveredAt
    hcomparison hFell hFinv (hpatch x hx J hJ hneg)

/-- Operator continuity reduces the local quadratic max-patch step to
boundary-covered compact-inactive data. -/
theorem OperatorContinuous.perronLowerEnvelope_localQuadraticMaxPatch_of_compactInactiveCovered
    {C boundary : Set (Point n)} {F : Operator n} {g : Point n -> Real}
    {B : DirichletBarrierPair C boundary F g} (hF : OperatorContinuous F)
    (hcomparison : DirichletComparisonPrinciple C boundary F g)
    (hFell : DegenerateElliptic F) (hFinv : HessianSymmetricInvariant F)
    (hpatch :
      PerronLowerEnvelopeLocalQuadraticCompactInactiveCoveredPatch C boundary F g B) :
    PerronLowerEnvelopeLocalQuadraticMaxPatch C boundary F g B :=
  hF.perronLowerEnvelope_localQuadraticBump.localQuadraticMaxPatch_of_compactInactiveCovered
    hcomparison hFell hFinv hpatch

end ViscositySolns
