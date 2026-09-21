/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.BoundedConvexDomain
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H10Graph

/-!
# Exact potential and solenoidal spaces

This module implements the literal Hilbert-space constructions underlying the
Chapter 1 potential/solenoidal quartet.  The raw submodules are mathematically
well-defined for an arbitrary set `U`, so this reusable construction is kept
generic here.  It is not the manuscript-facing API: `Book.Ch01.FieldSpaces`
exposes the quartet only with `IsOpenBoundedConvexDomain U` and `U.Nonempty`.
Any consequence needing those domain hypotheses states them explicitly below.

The two potential spaces are literal ranges of the typed Hilbert `L²` gradient
maps.  They are deliberately not closed: closedness is a separate analytic
theorem, not part of these definitions.
-/

namespace Homogenization

namespace PotentialSolenoidalExact

variable {d : ℕ} {U : Set (Vec d)}

/-- The generic literal range of `H¹(U)` gradients in the Euclidean
Hilbert-vector `L²(U)` ambient space.  The nonempty bounded open convex
Chapter 1 facade is `Book.Ch01.PotentialHilbertL2`. -/
noncomputable def potential (U : Set (Vec d)) : Submodule ℝ (HilbertVectorL2 U) where
  carrier := {g | ∃ u : H1Function U, u.gradToHilbertVectorL2 = g}
  zero_mem' := by
    refine ⟨0, ?_⟩
    exact H1Function.gradToHilbertVectorL2_zero
  add_mem' := by
    intro g h hg hh
    rcases hg with ⟨u, hu⟩
    rcases hh with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    calc
      (u + v).gradToHilbertVectorL2 =
          u.gradToHilbertVectorL2 + v.gradToHilbertVectorL2 :=
        H1Function.gradToHilbertVectorL2_add u v
      _ = g + h := by rw [hu, hv]
  smul_mem' := by
    intro c g hg
    rcases hg with ⟨u, hu⟩
    refine ⟨c • u, ?_⟩
    calc
      (c • u).gradToHilbertVectorL2 = c • u.gradToHilbertVectorL2 :=
        H1Function.gradToHilbertVectorL2_smul c u
      _ = c • g := by rw [hu]

/-- The generic literal range of `H¹₀(U)` gradients in the Euclidean
Hilbert-vector `L²(U)` ambient space.  The nonempty bounded open convex
Chapter 1 facade is `Book.Ch01.PotentialZeroTraceHilbertL2`. -/
noncomputable def potentialZeroTrace (U : Set (Vec d)) : Submodule ℝ (HilbertVectorL2 U) where
  carrier := {g | ∃ u : H10Function U, u.toH1Function.gradToHilbertVectorL2 = g}
  zero_mem' := by
    refine ⟨0, ?_⟩
    change (0 : H1Function U).gradToHilbertVectorL2 = 0
    exact H1Function.gradToHilbertVectorL2_zero
  add_mem' := by
    intro g h hg hh
    rcases hg with ⟨u, hu⟩
    rcases hh with ⟨v, hv⟩
    refine ⟨u + v, ?_⟩
    calc
      (u + v).toH1Function.gradToHilbertVectorL2 =
          (u.toH1Function + v.toH1Function).gradToHilbertVectorL2 := rfl
      _ = u.toH1Function.gradToHilbertVectorL2 +
          v.toH1Function.gradToHilbertVectorL2 :=
        H1Function.gradToHilbertVectorL2_add u.toH1Function v.toH1Function
      _ = g + h := by rw [hu, hv]
  smul_mem' := by
    intro c g hg
    rcases hg with ⟨u, hu⟩
    refine ⟨c • u, ?_⟩
    calc
      (c • u).toH1Function.gradToHilbertVectorL2 =
          (c • u.toH1Function).gradToHilbertVectorL2 := rfl
      _ = c • u.toH1Function.gradToHilbertVectorL2 :=
        H1Function.gradToHilbertVectorL2_smul c u.toH1Function
      _ = c • g := by rw [hu]

/-- The generic orthogonal complement of all zero-trace potential fields.
The Chapter 1 source-facing facade is
`Book.Ch01.SolenoidalHilbertL2`. -/
noncomputable def solenoidal (U : Set (Vec d)) : Submodule ℝ (HilbertVectorL2 U) :=
  (potentialZeroTrace U)ᗮ

/-- The generic orthogonal complement of all potential fields, i.e. fields
with zero normal trace in the Chapter 1 terminology.  The source-facing facade
is `Book.Ch01.SolenoidalZeroNormalTraceHilbertL2`. -/
noncomputable def solenoidalZeroNormalTrace (U : Set (Vec d)) :
    Submodule ℝ (HilbertVectorL2 U) :=
  (potential U)ᗮ

/-- The generic literal doubled space `L_pot(U) × L_sol(U)`.  The Chapter 1
source-facing facade is `Book.Ch01.PotentialSolenoidalHilbertL2`. -/
noncomputable def blockPotentialSolenoidal (U : Set (Vec d)) :
    Submodule ℝ (HilbertVectorL2 U × HilbertVectorL2 U) :=
  (potential U).prod (solenoidal U)

/-- The generic literal doubled space `L_pot,0(U) × L_sol,0(U)`.  The Chapter
1 source-facing facade is
`Book.Ch01.PotentialZeroTraceSolenoidalZeroNormalTraceHilbertL2`. -/
noncomputable def blockPotentialZeroTraceSolenoidalZeroNormalTrace (U : Set (Vec d)) :
    Submodule ℝ (HilbertVectorL2 U × HilbertVectorL2 U) :=
  (potentialZeroTrace U).prod (solenoidalZeroNormalTrace U)

theorem mem_potential_iff (g : HilbertVectorL2 U) :
    g ∈ potential U ↔ ∃ u : H1Function U, u.gradToHilbertVectorL2 = g :=
  Iff.rfl

theorem mem_potentialZeroTrace_iff (g : HilbertVectorL2 U) :
    g ∈ potentialZeroTrace U ↔
      ∃ u : H10Function U, u.toH1Function.gradToHilbertVectorL2 = g :=
  Iff.rfl

theorem mem_solenoidal_iff (g : HilbertVectorL2 U) :
    g ∈ solenoidal U ↔
      ∀ u : H10Function U, inner ℝ g u.toH1Function.gradToHilbertVectorL2 = 0 := by
  constructor
  · intro hg u
    exact (Submodule.mem_orthogonal' _ _).1 hg _ ⟨u, rfl⟩
  · intro hg
    rw [solenoidal, Submodule.mem_orthogonal']
    intro v hv
    rcases (mem_potentialZeroTrace_iff v).1 hv with ⟨u, hu⟩
    rw [← hu]
    exact hg u

theorem mem_solenoidalZeroNormalTrace_iff (g : HilbertVectorL2 U) :
    g ∈ solenoidalZeroNormalTrace U ↔
      ∀ u : H1Function U, inner ℝ g u.gradToHilbertVectorL2 = 0 := by
  constructor
  · intro hg u
    exact (Submodule.mem_orthogonal' _ _).1 hg _ ⟨u, rfl⟩
  · intro hg
    rw [solenoidalZeroNormalTrace, Submodule.mem_orthogonal']
    intro v hv
    rcases (mem_potential_iff v).1 hv with ⟨u, hu⟩
    rw [← hu]
    exact hg u

theorem potentialZeroTrace_le_potential : potentialZeroTrace U ≤ potential U := by
  intro g hg
  rcases (mem_potentialZeroTrace_iff g).1 hg with ⟨u, hu⟩
  exact (mem_potential_iff g).2 ⟨u.toH1Function, hu⟩

theorem solenoidalZeroNormalTrace_le_solenoidal :
    solenoidalZeroNormalTrace U ≤ solenoidal U := by
  intro g hg
  rw [mem_solenoidal_iff]
  intro u
  exact (mem_solenoidalZeroNormalTrace_iff g).1 hg u.toH1Function

theorem mem_blockPotentialSolenoidal_iff (g : HilbertVectorL2 U × HilbertVectorL2 U) :
    g ∈ blockPotentialSolenoidal U ↔ g.1 ∈ potential U ∧ g.2 ∈ solenoidal U :=
  Submodule.mem_prod

theorem mem_blockPotentialZeroTraceSolenoidalZeroNormalTrace_iff
    (g : HilbertVectorL2 U × HilbertVectorL2 U) :
    g ∈ blockPotentialZeroTraceSolenoidalZeroNormalTrace U ↔
      g.1 ∈ potentialZeroTrace U ∧ g.2 ∈ solenoidalZeroNormalTrace U :=
  Submodule.mem_prod

/-- A zero-normal-trace solenoidal field has zero (restricted-volume) integral.
The proof tests against affine `H¹` functions with arbitrary constant gradient. -/
theorem integral_eq_zero_of_mem_solenoidalZeroNormalTrace {d : ℕ} [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (g : HilbertVectorL2 U) (hg : g ∈ solenoidalZeroNormalTrace U) :
    ∫ x, g x ∂volumeMeasureOn U = 0 := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isFiniteMeasure_restrict_volume
  apply integral_eq_zero_of_forall_integral_inner_eq_zero ℝ g
    ((MeasureTheory.Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2))
  intro c
  let p : Vec d := c.toVec
  let u : H1Function U :=
    H1Function.affineOnIsSobolevRegularDomain hU.isSobolevRegularDomain p
  have horth : inner ℝ g u.gradToHilbertVectorL2 = 0 :=
    (mem_solenoidalZeroNormalTrace_iff g).1 hg u
  have hpair :
      ∫ x, inner ℝ (g x) (HilbertVec.ofVec p) ∂volumeMeasureOn U = 0 := by
    calc
      ∫ x, inner ℝ (g x) (HilbertVec.ofVec p) ∂volumeMeasureOn U =
          ∫ x, inner ℝ (g x) (u.gradToHilbertVectorL2 x) ∂volumeMeasureOn U := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [u.coeFn_gradToHilbertVectorL2] with x hx
            have hu_grad : u.grad x = p := by
              exact H1Function.affineOnIsSobolevRegularDomain_grad
                hU.isSobolevRegularDomain p x
            rw [hx]
            change inner ℝ (g x) (HilbertVec.ofVec p) =
              inner ℝ (g x) (HilbertVec.ofVec (u.grad x))
            rw [hu_grad]
      _ = inner ℝ g u.gradToHilbertVectorL2 := (MeasureTheory.L2.inner_def g _).symm
      _ = 0 := horth
  change ∫ x, inner ℝ c (g x) ∂volumeMeasureOn U = 0
  rw [← HilbertVec.ofVec_toVec c]
  simpa only [real_inner_comm] using hpair

/-- The normalized-domain average of a zero-normal-trace solenoidal field
vanishes. -/
theorem average_eq_zero_of_mem_solenoidalZeroNormalTrace {d : ℕ} [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) (hne : U.Nonempty)
    (g : HilbertVectorL2 U) (hg : g ∈ solenoidalZeroNormalTrace U) :
    (hU.toBoundedMeasurableDomain hne).average g (by
      change MeasureTheory.Integrable g (volumeMeasureOn U)
      let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
        hU.isFiniteMeasure_restrict_volume
      exact (MeasureTheory.Lp.memLp g).integrable (by norm_num : (1 : ENNReal) ≤ 2)) = 0 := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) :=
    hU.isFiniteMeasure_restrict_volume
  rw [BoundedMeasurableDomain.average, BoundedMeasurableDomain.normalizedVolume,
    MeasureTheory.integral_smul_measure]
  have hzero : ∫ x, g x ∂(hU.toBoundedMeasurableDomain hne).restrictedVolume = 0 := by
    change ∫ x, g x ∂volumeMeasureOn U = 0
    exact integral_eq_zero_of_mem_solenoidalZeroNormalTrace hU g hg
  rw [hzero]
  simp

end PotentialSolenoidalExact

end Homogenization
