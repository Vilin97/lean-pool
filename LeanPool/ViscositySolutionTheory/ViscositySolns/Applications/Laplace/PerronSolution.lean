/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Applications.Laplace.Comparison
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Existence.Perron.Method.StrictBoundary.EnvelopeAssembly

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# The Perron solution of the Laplace Dirichlet problem

On a bounded open set `C ⊆ Point n` with `0 < n`, a Dirichlet barrier pair for
`-Δ` whose barriers are continuous on `closure C` and attain the data `g` as
boundary traces produces, through the CIL Perron theorem
`PerronMethodExistenceTheorem.strictBoundary` and the Laplace comparison
principle, a viscosity solution `w` of `-Δw = 0` on `C` that is continuous on
`closure C`, equals `g` on `frontier C`, and lies between the barriers.
-/

@[expose] public noncomputable section

open Filter Topology

namespace ViscositySolns

variable {n : Nat}

/-- The limsup along `𝓝[C] x` of a function continuous on `closure C` is its value. -/
theorem upperEnvelope_eq_of_continuousOn_closure {C : Set (Point n)} {f : Point n -> Real}
    (hf : ContinuousOn f (closure C)) {x : Point n} (hx : x ∈ closure C) :
    upperEnvelope C f x = f x := by
  have : (nhdsWithin x C).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  exact ((hf x hx).mono subset_closure).tendsto.limsup_eq

/-- The liminf along `𝓝[C] x` of a function continuous on `closure C` is its value. -/
theorem lowerEnvelope_eq_of_continuousOn_closure {C : Set (Point n)} {f : Point n -> Real}
    (hf : ContinuousOn f (closure C)) {x : Point n} (hx : x ∈ closure C) :
    lowerEnvelope C f x = f x := by
  have : (nhdsWithin x C).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  exact ((hf x hx).mono subset_closure).tendsto.liminf_eq

theorem isBoundedUnder_le_of_continuousOn_closure {C : Set (Point n)}
    (hC : Bornology.IsBounded C) {f : Point n -> Real} (hf : ContinuousOn f (closure C))
    (x : Point n) : (nhdsWithin x C).IsBoundedUnder (· <= ·) f := by
  obtain ⟨M, hM⟩ := (hC.isCompact_closure.image_of_continuousOn hf).isBounded.bddAbove
  exact isBoundedUnder_of_eventually_le (a := M)
    (eventually_nhdsWithin_of_forall fun y hy => hM ⟨y, subset_closure hy, rfl⟩)

theorem isBoundedUnder_ge_of_continuousOn_closure {C : Set (Point n)}
    (hC : Bornology.IsBounded C) {f : Point n -> Real} (hf : ContinuousOn f (closure C))
    (x : Point n) : (nhdsWithin x C).IsBoundedUnder (· >= ·) f := by
  obtain ⟨M, hM⟩ := (hC.isCompact_closure.image_of_continuousOn hf).isBounded.bddBelow
  exact isBoundedUnder_of_eventually_ge (a := M)
    (eventually_nhdsWithin_of_forall fun y hy => hM ⟨y, subset_closure hy, rfl⟩)

/--
Perron existence for the Laplace Dirichlet problem from continuous barriers.
The solution is continuous up to the boundary, attains `g` on `frontier C`,
and is squeezed between the barriers on `closure C`.
-/
theorem exists_laplace_dirichlet_of_barrierPair (hn : 0 < n)
    {C : Set (Point n)} (hCopen : IsOpen C) (hCbdd : Bornology.IsBounded C)
    {g : Point n -> Real}
    (B : DirichletBarrierPair C (frontier C) laplaceOperator g)
    (hlower : ContinuousOn B.lower (closure C)) (hupper : ContinuousOn B.upper (closure C))
    (hlowerTrace : BoundaryLowerTraceOn C (frontier C) g B.lower)
    (hupperTrace : BoundaryUpperTraceOn C (frontier C) g B.upper) :
    ∃ w : Point n -> Real, ViscositySolution C laplaceOperator w ∧
      ContinuousOn w (closure C) ∧ (∀ x ∈ frontier C, w x = g x) ∧
      ∀ x ∈ closure C, B.lower x <= w x ∧ w x <= B.upper x := by
  have : LocallyCompactSpace C := hCopen.locallyCompactSpace
  have hunion : C ∪ frontier C = closure C := (closure_eq_self_union_frontier C).symm
  have hne : ∀ x : Point n, x ∈ C ∪ frontier C -> (nhdsWithin x C).NeBot := fun x hx =>
    mem_closure_iff_nhdsWithin_neBot.mp (hunion ▸ hx)
  have hsol := PerronMethodExistenceTheorem.strictBoundary B
    { comparison := dirichletComparisonPrinciple_laplaceOperator hn hCbdd.isCompact_closure g
      operator_continuous := operatorContinuous_laplaceOperator
      degenerate_elliptic := degenerateElliptic_laplaceOperator
      hessian_symmetric_invariant := by
        intro x r p X
        simp only [laplaceOperator_apply, symHessian, Matrix.trace_smul, Matrix.trace_add,
          Matrix.trace_transpose, smul_eq_mul]
        ring
      domain_open := hCopen
      boundary_outside_domain := fun z hz hzC =>
        (Set.eq_empty_iff_forall_notMem.mp hCopen.inter_frontier_eq) z ⟨hzC, hz⟩
      lower_trace := hlowerTrace
      upper_trace := hupperTrace
      nontrivial_nhds := hne
      upper_locally_bounded := fun x _ =>
        isBoundedUnder_le_of_continuousOn_closure hCbdd hupper x
      lower_locally_bounded := fun x _ =>
        isBoundedUnder_ge_of_continuousOn_closure hCbdd hlower x }
  set P := perronEnvelope C (frontier C) laplaceOperator g B.lower B.upper with hPdef
  set w := upperEnvelope C P with hwdef
  have hPle : ∀ x, (nhdsWithin x C).IsBoundedUnder (· <= ·) P := fun x =>
    B.perronEnvelope_isBoundedUnder_le (isBoundedUnder_le_of_continuousOn_closure hCbdd hupper x)
  have hPge : ∀ x, (nhdsWithin x C).IsBoundedUnder (· >= ·) P := fun x =>
    B.perronEnvelope_isBoundedUnder_ge (isBoundedUnder_ge_of_continuousOn_closure hCbdd hlower x)
  -- Values of the barriers on the boundary.
  have hlowerBd : ∀ x ∈ frontier C, B.lower x = g x := fun x hx => by
    rw [← hlowerTrace x hx,
      lowerEnvelope_eq_of_continuousOn_closure hlower (frontier_subset_closure hx)]
  have hupperBd : ∀ x ∈ frontier C, B.upper x = g x := fun x hx => by
    rw [← hupperTrace x hx,
      upperEnvelope_eq_of_continuousOn_closure hupper (frontier_subset_closure hx)]
  have hwbd : ∀ x ∈ frontier C, w x = g x := fun x hx => hsol.boundary_eq hx
  -- The squeeze between the barriers.
  have hsqueeze : ∀ x ∈ closure C, B.lower x <= w x ∧ w x <= B.upper x := by
    intro x hx
    rw [← hunion] at hx
    rcases hx with hxC | hxB
    · have : (nhdsWithin x C).NeBot := hne x (Or.inl hxC)
      constructor
      · calc B.lower x <= P x := B.lower_le_perronEnvelope (Or.inl hxC)
          _ <= w x := le_upperEnvelope hxC (hPle x)
      · calc w x <= upperEnvelope C B.upper x :=
              B.perronEnvelope_upperEnvelope_le_upperEnvelope (hPge x).isCoboundedUnder_le
                (isBoundedUnder_le_of_continuousOn_closure hCbdd hupper x)
          _ = B.upper x :=
              upperEnvelope_eq_of_continuousOn_closure hupper (subset_closure hxC)
    · rw [hwbd x hxB, hlowerBd x hxB, hupperBd x hxB]
      exact ⟨le_rfl, le_rfl⟩
  refine ⟨w, hsol.viscosity, ?_, hwbd, hsqueeze⟩
  -- Continuity on the closure.
  intro x hx
  rcases (hunion ▸ hx : x ∈ C ∪ frontier C) with hxC | hxB
  · have hcont : ContinuousWithinAt w C x :=
      continuousWithinAt_iff_lower_upperSemicontinuousWithinAt.mpr
        ⟨hsol.viscosity.2.1 x hxC, hsol.viscosity.1.1 x hxC⟩
    exact (hcont.continuousAt (hCopen.mem_nhds hxC)).continuousWithinAt
  · have hlx := hlowerBd x hxB
    have hux := hupperBd x hxB
    have hwx := hwbd x hxB
    have hlt : Tendsto B.lower (nhdsWithin x (closure C)) (𝓝 (w x)) := by
      rw [hwx, ← hlx]
      exact hlower x hx
    have hut : Tendsto B.upper (nhdsWithin x (closure C)) (𝓝 (w x)) := by
      rw [hwx, ← hux]
      exact hupper x hx
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlt hut
      (eventually_nhdsWithin_of_forall fun y hy => (hsqueeze y hy).1)
      (eventually_nhdsWithin_of_forall fun y hy => (hsqueeze y hy).2)

end ViscositySolns
