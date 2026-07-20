/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.SpectralPositivity.Operator.JentzschProof
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Kernel Positivity-Improving Criterion

An integral operator Tf(x) = ∫ K(x,y) f(y) dμ(y) on L²(Ω, μ) is
positivity-improving if and only if K(x,y) > 0 for μ ⊗ μ-a.e. (x,y).

## Proof strategy

Forward direction (K > 0 a.e. → T positivity-improving):
If f ≥ 0, f ≠ 0, then f > 0 on a set S of positive measure.
Tf(x) = ∫ K(x,y) f(y) dμ(y) ≥ ∫_S K(x,y) f(y) dμ(y) > 0
for a.e. x, since K(x,·) > 0 a.e. and f > 0 on S.

Reverse direction (T positivity-improving → K > 0 a.e.):
For any measurable sets A, B of positive measure,
⟨1_A, T(1_B)⟩ = ∫∫_{A×B} K(x,y) dμ(x)dμ(y) > 0
(since T(1_B) > 0 a.e., in particular on A).
This forces K > 0 a.e. on A × B for all such A, B.

## References

- Reed–Simon IV, Theorem XIII.44
- Simon, *Functional Integration and Quantum Physics*, Prop. I.12
-/

open MeasureTheory Measure Filter

noncomputable section

variable {Ω : Type*} [MeasureSpace Ω]

/-- An integral operator on L² defined by a kernel K : Ω × Ω → ℝ.
Tf(x) = ∫ K(x,y) f(y) dμ(y). -/
structure IntegralOperator (Ω : Type*) [MeasureSpace Ω] where
  /-- The integral kernel `K : Ω → Ω → ℝ` of the operator. -/
  kernel : Ω → Ω → ℝ
  /-- The kernel, viewed as a function on `Ω × Ω`, is measurable. -/
  kernel_measurable : Measurable (Function.uncurry kernel)

/-- A kernel is a.e. positive if K(x,y) > 0 for (volume ⊗ volume)-a.e. (x,y). -/
def IntegralOperator.IsAEPositive (T : IntegralOperator Ω) : Prop :=
  ∀ᵐ p ∂(volume.prod volume : Measure (Ω × Ω)),
    0 < T.kernel p.1 p.2

/-- Forward direction: if K(x,y) > 0 a.e. and f ≥ 0, f ≠ 0, then
Tf(x) = ∫ K(x,y) f(y) dμ(y) > 0 for a.e. x. -/
theorem IntegralOperator.ae_pos_integral_of_ae_pos_kernel
    [SFinite (volume : Measure Ω)]
    (T : IntegralOperator Ω)
    (hK : T.IsAEPositive)
    (f : Ω → ℝ)
    (_hf_meas : Measurable f)
    (hf_nonneg : ∀ᵐ x ∂(volume : Measure Ω), 0 ≤ f x)
    (hf_ne : ¬ f =ᵐ[volume] 0)
    (hf_int : ∀ᵐ x ∂(volume : Measure Ω),
      Integrable (fun y => T.kernel x y * f y) volume) :
    ∀ᵐ x ∂(volume : Measure Ω), 0 < ∫ y, T.kernel x y * f y ∂volume := by
  -- Step 1: From K > 0 a.e. on product, extract: for a.e. x, K(x,·) > 0 a.e.
  have hK_ae : ∀ᵐ x ∂(volume : Measure Ω), ∀ᵐ y ∂(volume : Measure Ω),
      0 < T.kernel x y :=
    ae_ae_of_ae_prod hK
  -- Step 2: f ≥ 0 a.e. and f ≠ 0 a.e. implies support of f has positive measure
  have hf_support : 0 < volume (Function.support f) := by
    rw [pos_iff_ne_zero]
    intro h_zero
    refine hf_ne (ae_iff.mpr ?_)
    simp only [Pi.zero_apply]
    rwa [show {a | ¬f a = 0} = Function.support f from rfl]
  -- Step 3: For a.e. x, the integrand K(x,·) * f(·) is nonneg a.e. and has positive support
  filter_upwards [hK_ae, hf_nonneg, hf_int] with x hKx hfx hintx
  -- Goal: 0 < ∫ y, K(x,y) * f(y) dy
  -- hKx : ∀ᵐ y, 0 < K(x,y)
  -- hfx : 0 ≤ f x  (not directly useful for integral over y)
  -- hintx : Integrable (fun y => K(x,y) * f(y))
  -- We use integral_pos_iff_support_of_nonneg_ae
  have h_nn : ∀ᵐ y ∂(volume : Measure Ω), 0 ≤ T.kernel x y * f y := by
    filter_upwards [hKx, hf_nonneg] with y hKy hfy
    exact mul_nonneg (le_of_lt hKy) hfy
  rw [integral_pos_iff_support_of_nonneg_ae h_nn hintx]
  -- Need: 0 < volume (support (fun y => K(x,y) * f(y)))
  -- support (K(x,·) * f) ⊇ support f ∩ {y | K(x,y) > 0}
  -- Both support f and {y | K(x,y) > 0} have positive/full measure
  rw [pos_iff_ne_zero]
  intro h_zero
  -- If support of K(x,·)*f is null, then K(x,·)*f = 0 a.e.
  -- But K(x,y) > 0 for a.e. y, so f(y) = 0 for a.e. y, contradicting hf_ne
  have h_ae_zero : (fun y => T.kernel x y * f y) =ᵐ[volume] 0 := by
    rw [Filter.EventuallyEq, ae_iff]
    simp only [Pi.zero_apply]
    rwa [show {a | ¬T.kernel x a * f a = 0} =
      Function.support (fun y => T.kernel x y * f y) from rfl]
  -- K(x,y) * f(y) = 0 a.e. and K(x,y) > 0 a.e. implies f(y) = 0 a.e.
  have hf_ae_zero : f =ᵐ[volume] 0 := by
    filter_upwards [h_ae_zero, hKx] with y hy hKy
    simp only [Pi.zero_apply] at hy
    exact (mul_eq_zero.mp hy).resolve_left (ne_of_gt hKy)
  exact hf_ne hf_ae_zero

/-- Auxiliary lemma: under the positivity-improving hypothesis, for any fixed
measurable B with positive measure, the inner integral ∫_B K(x,y) dy > 0
for a.e. x. -/
private theorem IntegralOperator.ae_pos_inner_integral
    [SFinite (volume : Measure Ω)]
    (T : IntegralOperator Ω)
    (hT : ∀ (A B : Set Ω), MeasurableSet A → MeasurableSet B →
      0 < volume A → 0 < volume B →
      0 < ∫ x in A, ∫ y in B, T.kernel x y ∂volume ∂volume)
    {B : Set Ω} (hB_meas : MeasurableSet B) (hB_pos : 0 < volume B) :
    ∀ᵐ x ∂(volume : Measure Ω),
      0 < ∫ y in B, T.kernel x y ∂volume := by
  -- By contradiction: if A = {x | ∫_B K(x,y) dy ≤ 0} has positive measure,
  -- then ∫_A ∫_B K ≤ 0, contradicting hT.
  by_contra h_not
  rw [Filter.not_eventually] at h_not
  -- h_not : ∃ᶠ x, ¬ (0 < ∫_B K(x,y) dy), i.e., ∫_B K(x,y) dy ≤ 0 frequently
  -- This means {x | ∫_B K(x,y) dy ≤ 0} has positive measure
  -- Define A = {x | ∫_B K(x,y) dy ≤ 0}
  set g : Ω → ℝ := fun x => ∫ y in B, T.kernel x y ∂volume with hg_def
  have h_A_pos : 0 < volume {x | ¬ 0 < g x} := by
    by_contra h_le
    push Not at h_le
    rw [nonpos_iff_eq_zero] at h_le
    apply h_not
    suffices ∀ᵐ x ∂(volume : Measure Ω), 0 < g x by
      filter_upwards [this] with x hx
      exact fun h => absurd hx (not_lt.mpr (not_lt.mp h))
    rw [ae_iff]
    convert h_le using 2
    ext x; simp [not_lt]
  have h_A_meas : MeasurableSet {x | ¬ 0 < g x} := by
    -- {x | ¬ 0 < g x} = {x | g x ≤ 0}, measurable since g is measurable.
    have hg_sm : StronglyMeasurable g := by
      change StronglyMeasurable (fun x => ∫ y, T.kernel x y ∂(volume.restrict B))
      exact T.kernel_measurable.stronglyMeasurable.integral_prod_right
    have : {x | ¬ 0 < g x} = {x | g x ≤ 0} := by ext x; simp [not_lt]
    rw [this]
    exact measurableSet_le hg_sm.measurable measurable_const
  -- On A, g(x) ≤ 0, so ∫_A g ≤ 0
  have h_nonpos : ∫ x in {x | ¬ 0 < g x}, g x ∂volume ≤ 0 := by
    apply setIntegral_nonpos h_A_meas
    intro x hx
    simp only [Set.mem_setOf_eq, not_lt] at hx
    exact hx
  -- But hT says ∫_A ∫_B K > 0
  have h_pos := hT _ B h_A_meas hB_meas h_A_pos hB_pos
  linarith

/-- Key measure-theoretic lemma: if ∫_B f > 0 for every measurable B with
positive measure, then f > 0 a.e.

This is a consequence of the fact that if f ≤ 0 on a set B of positive
measure, then ∫_B f ≤ 0 (by setIntegral_nonpos). -/
private theorem ae_pos_of_setIntegral_pos
    (f : Ω → ℝ) (hf_meas : Measurable f)
    (hpos : ∀ (B : Set Ω), MeasurableSet B → 0 < volume B →
      0 < ∫ y in B, f y ∂volume) :
    ∀ᵐ y ∂(volume : Measure Ω), 0 < f y := by
  rw [ae_iff]
  -- Need: volume {y | ¬ 0 < f y} = 0
  -- Equivalently: volume {y | f y ≤ 0} = 0
  by_contra h_pos
  push Not at h_pos
  -- h_pos : volume {a | f a ≤ 0} ≠ 0
  set B := {y | f y ≤ 0} with hB_def
  have hB_meas : MeasurableSet B :=
    measurableSet_le hf_meas measurable_const
  have hB_pos : 0 < volume B := pos_iff_ne_zero.mpr h_pos
  -- On B, f(y) ≤ 0
  have h_nonpos : ∫ y in B, f y ∂volume ≤ 0 := by
    apply setIntegral_nonpos hB_meas
    intro y hy
    exact hy
  -- But hpos says ∫_B f > 0
  have h_strict_pos := hpos B hB_meas hB_pos
  linarith

/-- Reverse direction in the purely atomic case: if singletons are measurable with positive
finite measure and every positive-measure pair `(A, B)` has strictly positive double integral,
then `K(x, y) > 0` for every pair `(x, y)`, hence in particular for a.e. `(x, y)`. -/
theorem IntegralOperator.ae_pos_kernel_of_positivity_improving
    [SFinite (volume : Measure Ω)]
    [MeasurableSingletonClass Ω]
    (T : IntegralOperator Ω)
    (h_atom_pos : ∀ x : Ω, 0 < volume ({x} : Set Ω))
    (h_atom_fin : ∀ x : Ω, volume ({x} : Set Ω) ≠ ⊤)
    -- For all measurable A, B with positive measure, ∫∫_{A×B} K > 0
    (hT : ∀ (A B : Set Ω), MeasurableSet A → MeasurableSet B →
      0 < volume A → 0 < volume B →
      0 < ∫ x in A, ∫ y in B, T.kernel x y ∂volume ∂volume) :
    T.IsAEPositive := by
  rw [IntegralOperator.IsAEPositive]
  refine Filter.Eventually.of_forall ?_
  intro p
  have hp1_real : 0 < (volume : Measure Ω).real ({p.1} : Set Ω) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (ne_of_gt (h_atom_pos p.1)) (h_atom_fin p.1)
  have hp2_real : 0 < (volume : Measure Ω).real ({p.2} : Set Ω) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (ne_of_gt (h_atom_pos p.2)) (h_atom_fin p.2)
  have hsing :=
    hT ({p.1} : Set Ω) ({p.2} : Set Ω)
      (measurableSet_singleton p.1) (measurableSet_singleton p.2)
      (h_atom_pos p.1) (h_atom_pos p.2)
  -- After simplifying the double singleton integral, we get:
  -- 0 < μ.real({p.1}) • (μ.real({p.2}) • K(p.1, p.2))
  simp only [integral_singleton, smul_eq_mul] at hsing
  -- hsing : 0 < μ.real({p.1}) * (μ.real({p.2}) * K(p.1, p.2))
  exact pos_of_mul_pos_right (pos_of_mul_pos_right hsing hp1_real.le) hp2_real.le

end
