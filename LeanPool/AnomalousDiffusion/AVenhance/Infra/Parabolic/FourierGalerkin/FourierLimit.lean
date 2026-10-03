/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.Basis
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Exhaustion limits for the symmetric torus Fourier cutoffs

The finite frequency boxes exhaust the full integer lattice.  This file records the unconditional
sum convergence needed to turn the landed torus Fourier basis expansion into cutoff convergence.
-/

@[expose] public section

namespace AVenhance.Infra.Parabolic.FourierGalerkin

open Filter Topology
open MeasureTheory
open scoped Topology

noncomputable section

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance fourierLimitMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance fourierLimitMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance fourierLimitProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance two_le_fact : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

/-- Complex-valued scalar `L²` on the unit torus. -/
abbrev ComplexScalarTorusL2 := Lp ℂ 2 (volume : Measure Torus)

/-- Pair-frequency indexing is equivalent to the two-coordinate integer lattice. -/
def pairFrequencyEquiv : ℤ × ℤ ≃ (Fin 2 → ℤ) where
  toFun := pairFrequency
  invFun := fun k => (k 0, k 1)
  left_inv p := by
    rcases p with ⟨p₁, p₂⟩
    simp [pairFrequency]
  right_inv k := by
    funext i
    fin_cases i <;> simp [pairFrequency]

/-- The symmetric frequency boxes tend to the at-top filter on finite frequency sets. -/
theorem tendsto_symmetricFrequencyBox_atTop :
    Tendsto symmetricFrequencyBox atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro s
  let B : ℕ := s.sup (fun p => max p.1.natAbs p.2.natAbs)
  filter_upwards [eventually_ge_atTop B] with N hBN
  intro p hp
  have hsup : max p.1.natAbs p.2.natAbs ≤ B :=
    Finset.le_sup (f := fun q => max q.1.natAbs q.2.natAbs) hp
  have hp₁ : p.1.natAbs ≤ N := (Nat.le_max_left _ _).trans (hsup.trans hBN)
  have hp₂ : p.2.natAbs ≤ N := (Nat.le_max_right _ _).trans (hsup.trans hBN)
  have hp₁abs : |p.1| ≤ (N : ℤ) := by
    have hcast : (p.1.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hp₁
    simpa [Int.natCast_natAbs] using hcast
  have hp₂abs : |p.2| ≤ (N : ℤ) := by
    have hcast : (p.2.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hp₂
    simpa [Int.natCast_natAbs] using hcast
  rcases abs_le.mp hp₁abs with ⟨hp₁lo, hp₁hi⟩
  rcases abs_le.mp hp₂abs with ⟨hp₂lo, hp₂hi⟩
  simp only [symmetricFrequencyBox, Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨hp₁lo, hp₁hi⟩, ⟨hp₂lo, hp₂hi⟩⟩

/-- Unconditional Fourier series sums over the symmetric frequency boxes converge to the full sum.
-/
theorem tendsto_pairBox_sum_of_hasSum
    {F : Type*} [AddCommMonoid F] [TopologicalSpace F]
    {f : (Fin 2 → ℤ) → F} {z : F} (hsum : HasSum f z) :
    Tendsto (fun N => ∑ p ∈ symmetricFrequencyBox N, f (pairFrequency p)) atTop
      (𝓝 z) := by
  have hpair : HasSum (fun p : ℤ × ℤ => f (pairFrequency p)) z :=
    (Equiv.hasSum_iff pairFrequencyEquiv).2 hsum
  change Tendsto
    (fun s : Finset (ℤ × ℤ) => ∑ p ∈ s, f (pairFrequency p)) atTop (𝓝 z) at hpair
  exact hpair.comp tendsto_symmetricFrequencyBox_atTop

/-- The finite complex Fourier partial sum as an `L²` class. -/
@[irreducible]
def complexFourierPartialSumLp (N : ℕ) (f : ComplexScalarTorusL2) :
    ComplexScalarTorusL2 :=
  ∑ p ∈ symmetricFrequencyBox N,
    UnitAddTorus.mFourierCoeff f (pairFrequency p) •
      UnitAddTorus.mFourierLp 2 (pairFrequency p)

/-- Pointwise complex Fourier partial sum for an arbitrary complex-valued function. -/
def complexFourierPartialSumFunction (N : ℕ) (f : Torus → ℂ) (x : Torus) : ℂ :=
  ∑ p ∈ symmetricFrequencyBox N,
    UnitAddTorus.mFourierCoeff f (pairFrequency p) *
      UnitAddTorus.mFourier (pairFrequency p) x

/-- The `L²` Fourier partial sum has the expected pointwise representative a.e. -/
theorem complexFourierPartialSumLp_coeFn (N : ℕ) (f : ComplexScalarTorusL2) :
    (fun x => complexFourierPartialSumLp N f x) =ᵐ[volume]
      complexFourierPartialSumFunction N (fun x => f x) := by
  let box := symmetricFrequencyBox N
  have hsum := Lp.coeFn_finsetSum box
    (fun p => UnitAddTorus.mFourierCoeff f (pairFrequency p) •
      UnitAddTorus.mFourierLp 2 (pairFrequency p))
  have hterms : ∀ᵐ x ∂volume, ∀ p : {p : ℤ × ℤ // p ∈ box},
      (UnitAddTorus.mFourierCoeff f (pairFrequency p) •
        UnitAddTorus.mFourierLp 2 (pairFrequency p)) x =
      UnitAddTorus.mFourierCoeff f (pairFrequency p) *
        UnitAddTorus.mFourier (pairFrequency p) x := by
    apply ae_all_iff.2
    intro p
    filter_upwards [Lp.coeFn_smul
      (UnitAddTorus.mFourierCoeff f (pairFrequency p))
      (UnitAddTorus.mFourierLp 2 (pairFrequency p)),
      UnitAddTorus.coeFn_mFourierLp 2 (pairFrequency p)] with x hsmul hmode
    have hmode' : (UnitAddTorus.mFourierLp 2 (pairFrequency p)) x =
        UnitAddTorus.mFourier (pairFrequency p) x := by
      simpa [UnitAddTorus.mFourierLp, ContinuousMap.coe_coe] using hmode
    calc
      _ = (fun y => UnitAddTorus.mFourierCoeff f (pairFrequency p) •
        (UnitAddTorus.mFourierLp 2 (pairFrequency p)) y) x := hsmul
      _ = UnitAddTorus.mFourierCoeff f (pairFrequency p) *
          (UnitAddTorus.mFourierLp 2 (pairFrequency p)) x := by simp
      _ = UnitAddTorus.mFourierCoeff f (pairFrequency p) *
          UnitAddTorus.mFourier (pairFrequency p) x := by rw [hmode']
  filter_upwards [hsum, hterms] with x hsum hterms
  rw [complexFourierPartialSumLp]
  rw [hsum]
  simp only [Finset.sum_apply]
  rw [complexFourierPartialSumFunction]
  apply Finset.sum_congr rfl
  intro p hp
  exact hterms ⟨p, hp⟩

/-- Complex Fourier partial sums over the positive symmetric cutoff converge in `L²`. -/
theorem tendsto_complexFourierPartialSumLp (f : ComplexScalarTorusL2) :
    Tendsto (fun N => complexFourierPartialSumLp N f) atTop (𝓝 f) := by
  have hseries : HasSum
      (fun k : Fin 2 → ℤ => UnitAddTorus.mFourierCoeff f k •
        UnitAddTorus.mFourierLp 2 k) f :=
    UnitAddTorus.hasSum_mFourier_series_L2 f
  simpa only [complexFourierPartialSumLp] using
    (tendsto_pairBox_sum_of_hasSum hseries)

/-- Taking real parts preserves the Fourier cutoff convergence. -/
theorem tendsto_realPartFourierPartialSumLp (f : ComplexScalarTorusL2) :
    Tendsto (fun N => Complex.reCLM.compLp (complexFourierPartialSumLp N f)) atTop
      (𝓝 (Complex.reCLM.compLp f)) := by
  exact (Complex.reCLM.compLpL 2 volume).continuous.continuousAt.tendsto.comp
    (tendsto_complexFourierPartialSumLp f)

end

end AVenhance.Infra.Parabolic.FourierGalerkin
