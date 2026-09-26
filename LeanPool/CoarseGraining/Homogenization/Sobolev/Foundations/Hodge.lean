/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.H1.BasicLemmas
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareMeanZero
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph
public import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidal
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2

/-! # Hodge -/

@[expose] public section

namespace Homogenization

/-!
This file isolates the foundational theorem surface for Hodge-style converse
statements and basic restriction lemmas.

The restriction theorem is proved directly from the current `H1` witness API.
The converse theorem is now proved axiom-free from the coercive mean-zero `H¹`
Hilbert layer: solve the weak gradient problem on the closed graph, kill the
orthogonal residual in `L²`, and replace the weak gradient by the original
field. The `HasHodgeConverse` class remains as packaged theorem data for
downstream consumers that prefer typeclass style.
-/

/--
Explicit data for the Hodge-style converse on a domain `U`.

This keeps the theorem surface available for upstream consumers without hiding a
missing proof behind a placeholder. A future analytic sublayer should provide
canonical instances by proving the required orthogonal-complement statement.
-/
class HasHodgeConverse {d : ℕ} (U : Set (Vec d))
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] : Prop where
  isPotentialOn_of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2 :
    ∀ {f : Vec d → Vec d}, MemVectorL2 U f →
      (∀ {g : Vec d → Vec d}, MemVectorL2 U g →
        IsSolenoidalZeroNormalTraceOn U g →
          ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume = 0) →
        IsPotentialOn U f

/--
Explicit orthogonality criterion underlying the Hodge-style converse on `U`.

This theorem-shaped predicate is the direct non-typeclass entry point for the
current development. `HasHodgeConverse` packages the same statement as an
instance when downstream APIs prefer typeclass style.
-/
def HodgeConverseCriterion {d : ℕ} (U : Set (Vec d))
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] : Prop :=
  ∀ {f : Vec d → Vec d}, MemVectorL2 U f →
    (∀ {g : Vec d → Vec d}, MemVectorL2 U g ->
      IsSolenoidalZeroNormalTraceOn U g ->
        ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume = 0) ->
      IsPotentialOn U f

theorem HasHodgeConverse.hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U] :
    HodgeConverseCriterion U :=
  HasHodgeConverse.isPotentialOn_of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2

/--
Package an explicit orthogonality criterion as `HasHodgeConverse` data.

This is the canonical constructor surface for future analytic work that proves
the converse theorem from closed-range or orthogonal-complement arguments.
-/
theorem hasHodgeConverse_of_orthogonal_criterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (h : HodgeConverseCriterion U) :
    HasHodgeConverse U where
  isPotentialOn_of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2 := by
    intro f hf horth
    exact h hf horth

/--
The Hodge-style converse follows from the coercive mean-zero `H¹` layer.

This is the first axiom-free theorem surface for the converse inside the
repository: solve the weak gradient problem on the coercive Hilbert graph,
show the residual is solenoidal with zero normal trace, use the orthogonality
hypothesis to kill that residual in `L²`, and then replace the weak gradient by
the original field `f`.
-/
theorem hodgeConverseCriterion_of_h1CoerciveEstimate
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hC : H1CoerciveEstimate U) :
    HodgeConverseCriterion U := by
  intro f hf horth
  let u : H1MeanZeroFunction U := H1MeanZeroFunction.gradientProblemSolution (U := U) hf hC
  let r : Vec d → Vec d := fun x => f x - u.toH1Function.grad x
  let hzeroMem : MemVectorL2 U (0 : Vec d → Vec d) := MeasureTheory.MemLp.zero
  have hr : MemVectorL2 U r := hf.sub u.toH1Function.grad_memVectorL2
  have hr_sol : IsSolenoidalZeroNormalTraceOn U r := by
    intro φ
    have hfirst :=
      H1Function.gradientProblemSolution_firstVariation_eq_integral
        (d := d) (U := U) hf hC φ
    have hf_int :
        MeasureTheory.IntegrableOn (fun x => vecDot (f x) (φ.grad x)) U :=
      integrableOn_vecDot_of_memVectorL2 hf φ.grad_memVectorL2
    have hu_int :
        MeasureTheory.IntegrableOn (fun x => vecDot (u.toH1Function.grad x) (φ.grad x)) U :=
      integrableOn_vecDot_of_memVectorL2 u.toH1Function.grad_memVectorL2 φ.grad_memVectorL2
    have hsub :
        (fun x => vecDot (r x) (φ.grad x)) =
          fun x => vecDot (f x) (φ.grad x) - vecDot (u.toH1Function.grad x) (φ.grad x) := by
      funext x
      simp [r, sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
    calc
      ∫ x in U, vecDot (r x) (φ.grad x) ∂MeasureTheory.volume
          = ∫ x in U,
              (vecDot (f x) (φ.grad x) - vecDot (u.toH1Function.grad x) (φ.grad x))
                ∂MeasureTheory.volume := by
                  rw [hsub]
      _ = ∫ x in U, vecDot (f x) (φ.grad x) ∂MeasureTheory.volume -
            ∫ x in U, vecDot (u.toH1Function.grad x) (φ.grad x) ∂MeasureTheory.volume := by
              rw [MeasureTheory.integral_sub hf_int hu_int]
      _ = 0 := by
            rw [hfirst]
            ring
  have hru_zero :
      ∫ x in U, vecDot (r x) (u.toH1Function.grad x) ∂MeasureTheory.volume = 0 :=
    hr_sol u.toH1Function
  have hrr_int :
      MeasureTheory.IntegrableOn (fun x => vecDot (r x) (r x)) U :=
    integrableOn_vecDot_of_memVectorL2 hr hr
  have hru_int :
      MeasureTheory.IntegrableOn (fun x => vecDot (r x) (u.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hr u.toH1Function.grad_memVectorL2
  have hrf_expand :
      ∫ x in U, vecDot (r x) (f x) ∂MeasureTheory.volume =
        ∫ x in U, vecDot (r x) (r x) ∂MeasureTheory.volume +
          ∫ x in U, vecDot (r x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
    calc
      ∫ x in U, vecDot (r x) (f x) ∂MeasureTheory.volume
          = ∫ x in U, vecDot (r x) (r x + u.toH1Function.grad x) ∂MeasureTheory.volume := by
              congr 1
              funext x
              have hfx : f x = r x + u.toH1Function.grad x := by
                simp [r, sub_eq_add_neg, add_left_comm, add_comm]
              rw [hfx]
      _ = ∫ x in U, (vecDot (r x) (r x) + vecDot (r x) (u.toH1Function.grad x))
            ∂MeasureTheory.volume := by
              congr 1
              funext x
              simp [vecDot_add_right]
      _ = ∫ x in U, vecDot (r x) (r x) ∂MeasureTheory.volume +
            ∫ x in U, vecDot (r x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
              rw [MeasureTheory.integral_add hrr_int.integrable hru_int.integrable]
  have hsum_zero :
      ∫ x in U, vecDot (r x) (r x) ∂MeasureTheory.volume +
          ∫ x in U, vecDot (r x) (u.toH1Function.grad x) ∂MeasureTheory.volume = 0 := by
    calc
      ∫ x in U, vecDot (r x) (r x) ∂MeasureTheory.volume +
          ∫ x in U, vecDot (r x) (u.toH1Function.grad x) ∂MeasureTheory.volume
          = ∫ x in U, vecDot (r x) (f x) ∂MeasureTheory.volume := by
              symm
              exact hrf_expand
      _ = 0 := horth hr hr_sol
  have hrr_zero :
      ∫ x in U, vecDot (r x) (r x) ∂MeasureTheory.volume = 0 := by
    rw [hru_zero, add_zero] at hsum_zero
    exact hsum_zero
  have hzero_hilbert : Homogenization.toHilbertVectorL2OfVecField hr = 0 := by
    have hinner_zero :
        inner ℝ (Homogenization.toHilbertVectorL2OfVecField hr)
          (Homogenization.toHilbertVectorL2OfVecField hr) = 0 := by
      calc
        inner ℝ (Homogenization.toHilbertVectorL2OfVecField hr)
            (Homogenization.toHilbertVectorL2OfVecField hr)
            = ∫ x in U, vecDot (r x) (r x) ∂MeasureTheory.volume := by
                exact Homogenization.inner_toHilbertVectorL2OfVecField_eq_integral (U := U) hr hr
        _ = 0 := hrr_zero
    have hnorm_sq :
        ‖Homogenization.toHilbertVectorL2OfVecField hr‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hinner_zero
    have hnorm_zero : ‖Homogenization.toHilbertVectorL2OfVecField hr‖ = 0 := by
      nlinarith [sq_nonneg ‖Homogenization.toHilbertVectorL2OfVecField hr‖, hnorm_sq]
    exact norm_eq_zero.mp hnorm_zero
  have hzero_vector : Homogenization.toVectorL2 hr = 0 := by
    have htransport :=
      congrArg (Homogenization.hilbertVectorL2ToVectorL2 (U := U)) hzero_hilbert
    simpa [Homogenization.hilbertVectorL2ToVectorL2_toHilbertVectorL2 (U := U) (f := r) hr] using
      htransport
  have hzero_vector' :
      Homogenization.toVectorL2 hr =
        Homogenization.toVectorL2 (U := U) (f := (0 : Vec d → Vec d)) hzeroMem := by
    rw [show Homogenization.toVectorL2 (U := U) (f := (0 : Vec d → Vec d)) hzeroMem = 0 by
      simp [Homogenization.toVectorL2]]
    exact hzero_vector
  have hr_ae_zero : r =ᵐ[volumeMeasureOn U] (0 : Vec d → Vec d) :=
    (Homogenization.toVectorL2_eq_toVectorL2_iff
      (U := U) (f := r) (g := 0) hr hzeroMem).mp hzero_vector'
  have hgrad_ae : f =ᵐ[volumeMeasureOn U] u.toH1Function.grad := by
    filter_upwards [hr_ae_zero] with x hx
    exact sub_eq_zero.mp (by simpa [r] using hx)
  refine ⟨
    { toFun := u.toH1Function.toFun
      grad := f
      memL2 := u.toH1Function.memL2
      gradMemL2 := by
        intro i
        let π : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
        simpa [MemL2On, MemVectorL2, volumeMeasureOn] using! π.comp_memLp' hf
      hasWeakGradient := by
        intro i ψ hψ_smooth hψ_compact hψ_sub
        have hweak := u.toH1Function.hasWeakGradient i ψ hψ_smooth hψ_compact hψ_sub
        have hcoord :
            ∫ x in U, u.toH1Function.grad x i * ψ x ∂MeasureTheory.volume =
              ∫ x in U, f x i * ψ x ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards [hgrad_ae] with x hx
          rw [hx]
        calc
          ∫ x in U, u.toH1Function x * (fderiv ℝ ψ x) (basisVec i) ∂MeasureTheory.volume
              = -∫ x in U, u.toH1Function.grad x i * ψ x ∂MeasureTheory.volume := hweak
          _ = -∫ x in U, f x i * ψ x ∂MeasureTheory.volume := by rw [hcoord] }, rfl⟩

/-- Package the coercive-Hilbert proof of the Hodge converse as
`HasHodgeConverse` data. -/
theorem hasHodgeConverse_of_h1CoerciveEstimate
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hC : H1CoerciveEstimate U) :
    HasHodgeConverse U :=
  hasHodgeConverse_of_orthogonal_criterion
    (hodgeConverseCriterion_of_h1CoerciveEstimate (U := U) hC)

/-- A bounded open convex domain satisfies the Hodge converse once the direct
mean-zero `L²` Poincare theorem is available on the `H¹` layer. -/
theorem hodgeConverseCriterion_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) :
    HodgeConverseCriterion U :=
  hodgeConverseCriterion_of_h1CoerciveEstimate
    (h1CoerciveEstimate_of_isOpenBoundedConvexDomain (U := U) hU)

/-- Packaged version of
`hodgeConverseCriterion_of_isOpenBoundedConvexDomain`. -/
theorem hasHodgeConverse_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsOpenBoundedConvexDomain U) :
    HasHodgeConverse U :=
  hasHodgeConverse_of_orthogonal_criterion
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hU)

namespace IsPotentialOn

theorem of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (h : HodgeConverseCriterion U)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f)
    (horth :
      ∀ {g : Vec d → Vec d}, MemVectorL2 U g →
        IsSolenoidalZeroNormalTraceOn U g →
          ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume = 0) :
    IsPotentialOn U f :=
  h hf horth

theorem of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    [HasHodgeConverse U]
    {f : Vec d → Vec d} (hf : MemVectorL2 U f)
    (horth :
      ∀ {g : Vec d → Vec d}, MemVectorL2 U g →
        IsSolenoidalZeroNormalTraceOn U g →
          ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume = 0) :
    IsPotentialOn U f :=
  of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
    (HasHodgeConverse.hodgeConverseCriterion (U := U)) hf horth

theorem of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_h1CoerciveEstimate
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hC : H1CoerciveEstimate U)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f)
    (horth :
      ∀ {g : Vec d → Vec d}, MemVectorL2 U g →
        IsSolenoidalZeroNormalTraceOn U g →
          ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume = 0) :
    IsPotentialOn U f :=
  of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
    (hodgeConverseCriterion_of_h1CoerciveEstimate (U := U) hC) hf horth

theorem restrict_of_isOpen_of_memVectorL2
    {d : ℕ} {U V : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {f : Vec d → Vec d} (hf : IsPotentialOn U f) (_hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (hfV : MemVectorL2 V f) :
    IsPotentialOn V f := by
  rcases hf with ⟨u, rfl⟩
  exact ⟨u.restrict hV hVU, rfl⟩

end IsPotentialOn

end Homogenization
