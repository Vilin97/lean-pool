/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module


public import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.ShiftedBeamRealization
public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.IntervalSecondPrimitiveCompact
public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.IntervalSecondPrimitiveDeriv
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Tactic

/-! # Beam Form Space -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# The concrete free-beam form space on `L²(0,1]`

This file finally *inhabits* the abstract form method of
`ShiftedBeamRealization`.  The form space is the closed subspace of
`WithLp 2 (L² × L²)` of pairs `(u, w)` in which `w` is the weak second derivative of `u`,
tested against the polynomial bump family of `IntervalWeakSecondDeriv`.  Its inner product is
exactly the shifted bending form `∫ u conj(v) + ∫ u'' conj(v)''`, so the represented form operator is the
identity and coercivity is trivial.

The three genuinely analytic inputs are all imported:

* the representation theorem (`eq_affine_add_secondPrimitive_of_forall_integral_bumpD2`)
  identifies the first component up to affine functions, giving injectivity of the embedding,
  the finite-rank part of Rellich compactness, and the affine kernel;
* compactness of the second-primitive operator (`isCompactOperator_secondPrimitiveCLM`)
  gives the rest of Rellich compactness with no weak-topology argument;
* Weierstrass density (through the bump-family integration by parts for polynomial pairs)
  gives density of the embedded domain.

The output is `beamShiftedFormData : ShiftedBeamFormData`, whose `beamOperator` is the
self-adjoint nonnegative free-beam realization used by the Section 9 spectral analysis.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model


noncomputable section

/-- The ambient Hilbert space of the free-beam model: `L²` of the unit interval. -/
abbrev BeamL2 : Type := Lp ℂ 2 unitIocMeasure

/-- The product space carrying candidate (function, second derivative) pairs. -/
abbrev BeamPairSpace : Type := WithLp 2 (BeamL2 × BeamL2)

/-- First coordinate of a pair, as a continuous linear map. -/
def pairFst : BeamPairSpace →L[ℂ] BeamL2 :=
  (ContinuousLinearMap.fst ℂ BeamL2 BeamL2).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2 : BeamPairSpace →L[ℂ] BeamL2 × BeamL2)

/-- Second coordinate of a pair, as a continuous linear map. -/
def pairSnd : BeamPairSpace →L[ℂ] BeamL2 :=
  (ContinuousLinearMap.snd ℂ BeamL2 BeamL2).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2 : BeamPairSpace →L[ℂ] BeamL2 × BeamL2)

/-- Evaluating the first pair coordinate. -/
@[simp] theorem pairFst_apply (p : BeamPairSpace) :
    pairFst p = (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2 p).1 := rfl

/-- Evaluating the second pair coordinate. -/
@[simp] theorem pairSnd_apply (p : BeamPairSpace) :
    pairSnd p = (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2 p).2 := rfl

/-! ## Pairing functionals and the constraint subspace -/

/-- A sup bound for a continuous weight on the unit interval. -/
def pairingBound (g : ℝ → ℂ) (hg : Continuous g) : ℝ :=
  ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hg.continuousOn).choose

/-- The defining bound of the bump pairing functional. -/
theorem pairingBound_spec (g : ℝ → ℂ) (hg : Continuous g) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖g x‖ ≤ pairingBound g hg :=
  ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
    hg.continuousOn).choose_spec

/-- The bump pairing bound is nonnegative. -/
theorem pairingBound_nonneg (g : ℝ → ℂ) (hg : Continuous g) : 0 ≤ pairingBound g hg :=
  le_trans (norm_nonneg (g 0)) (pairingBound_spec g hg 0 (by norm_num))

/-- Integration against a continuous weight, as a continuous linear functional on `L²`. -/
def pairingCLM (g : ℝ → ℂ) (hg : Continuous g) : BeamL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun W => ∫ t, (W : ℝ → ℂ) t * g t ∂unitIocMeasure
      map_add' := by
        intro W V
        rw [← integral_add (integrable_mul_of_continuous (integrable_coeFn W) hg)
          (integrable_mul_of_continuous (integrable_coeFn V) hg)]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_add W V] with t ht
        rw [ht]
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro c W
        rw [RingHom.id_apply, smul_eq_mul, ← MeasureTheory.integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_smul c W] with t ht
        rw [ht]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring }
    (pairingBound g hg)
    (fun W => by
      have key : ‖∫ t, (W : ℝ → ℂ) t * g t ∂unitIocMeasure‖
          ≤ pairingBound g hg * ‖W‖ := by
        calc ‖∫ t, (W : ℝ → ℂ) t * g t ∂unitIocMeasure‖
            ≤ ∫ t, ‖(W : ℝ → ℂ) t * g t‖ ∂unitIocMeasure :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ ≤ ∫ t, pairingBound g hg * ‖(W : ℝ → ℂ) t‖ ∂unitIocMeasure := by
              refine integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun t => norm_nonneg _)
                ((integrable_coeFn W).norm.const_mul _) ?_
              filter_upwards [ae_mem_unitIocMeasure] with t ht
              rw [norm_mul, mul_comm]
              exact mul_le_mul_of_nonneg_right
                (pairingBound_spec g hg t ⟨ht.1.le, ht.2⟩) (norm_nonneg _)
          _ = pairingBound g hg * ∫ t, ‖(W : ℝ → ℂ) t‖ ∂unitIocMeasure :=
              MeasureTheory.integral_const_mul _ _
          _ ≤ pairingBound g hg * ‖W‖ :=
              mul_le_mul_of_nonneg_left (integral_norm_coeFn_le W)
                (pairingBound_nonneg g hg)
      exact key)

/-- Evaluating the bump pairing functional. -/
@[simp] theorem pairingCLM_apply (g : ℝ → ℂ) (hg : Continuous g) (W : BeamL2) :
    pairingCLM g hg W = ∫ t, (W : ℝ → ℂ) t * g t ∂unitIocMeasure := rfl

/-- The complexified second bump derivative. -/
def bumpD2C (k : ℕ) (t : ℝ) : ℂ := (intervalBumpD2 k t : ℂ)

/-- The complexified bump. -/
def bumpC (k : ℕ) (t : ℝ) : ℂ := (intervalBump k t : ℂ)

/-- The second derivative of the interval bump is continuous. -/
theorem continuous_bumpD2C (k : ℕ) : Continuous (bumpD2C k) :=
  Complex.continuous_ofReal.comp (continuous_intervalBumpD2 k)

/-- The interval bump is continuous. -/
theorem continuous_bumpC (k : ℕ) : Continuous (bumpC k) :=
  Complex.continuous_ofReal.comp (continuous_intervalBump k)

/-- The `k`-th weak-second-derivative constraint. -/
def constraintCLM (k : ℕ) : BeamPairSpace →L[ℂ] ℂ :=
  (pairingCLM (bumpD2C k) (continuous_bumpD2C k)).comp pairFst
    - (pairingCLM (bumpC k) (continuous_bumpC k)).comp pairSnd

/-- The free-beam form subspace: pairs in which the second coordinate is the weak second
derivative of the first, tested against the bump family. -/
def beamFormSubmodule : Submodule ℂ BeamPairSpace :=
  ⨅ k : ℕ, LinearMap.ker (constraintCLM k : BeamPairSpace →ₗ[ℂ] ℂ)

/-- Membership in the form subspace is the family of weak-derivative identities. -/
theorem mem_beamFormSubmodule_iff (p : BeamPairSpace) :
    p ∈ beamFormSubmodule ↔ ∀ k : ℕ,
      ∫ t, (pairFst p : ℝ → ℂ) t * bumpD2C k t ∂unitIocMeasure
        = ∫ t, (pairSnd p : ℝ → ℂ) t * bumpC k t ∂unitIocMeasure := by
  rw [beamFormSubmodule, Submodule.mem_iInf]
  refine forall_congr' fun k => ?_
  rw [LinearMap.mem_ker]
  simp only [ContinuousLinearMap.coe_coe, constraintCLM, sub_apply,
    ContinuousLinearMap.comp_apply, pairingCLM_apply]
  rw [sub_eq_zero]

/-- The form subspace is closed. -/
theorem isClosed_beamFormSubmodule :
    IsClosed (beamFormSubmodule : Set BeamPairSpace) := by
  have : (beamFormSubmodule : Set BeamPairSpace)
      = ⋂ k : ℕ,
        (LinearMap.ker (constraintCLM k : BeamPairSpace →ₗ[ℂ] ℂ) : Set BeamPairSpace) := by
    rw [beamFormSubmodule]
    exact Submodule.coe_iInf _
  rw [this]
  exact isClosed_iInter fun k => (constraintCLM k).isClosed_ker

/-- The free-beam form space. -/
abbrev BeamV : Type := ↥beamFormSubmodule

/-- The form domain is closed in the pair space, hence complete. -/
instance : CompleteSpace BeamV := isClosed_beamFormSubmodule.completeSpace_coe

/-- The form-space embedding into the ambient `L²`. -/
def beamEmbed : BeamV →L[ℂ] BeamL2 := pairFst.comp beamFormSubmodule.subtypeL

/-- The bending-slot projection of the form space. -/
def beamSnd : BeamV →L[ℂ] BeamL2 := pairSnd.comp beamFormSubmodule.subtypeL

/-- Evaluating the form-domain inclusion. -/
@[simp] theorem beamEmbed_apply (p : BeamV) : beamEmbed p = pairFst (p : BeamPairSpace) := rfl

/-- Evaluating the form-domain second-derivative map. -/
@[simp] theorem beamSnd_apply (p : BeamV) : beamSnd p = pairSnd (p : BeamPairSpace) := rfl

/-- The weak-derivative identities, in the form the representation theorem consumes. -/
theorem beamV_weak (p : BeamV) (k : ℕ) :
    ∫ t, (beamEmbed p : ℝ → ℂ) t * (intervalBumpD2 k t : ℂ) ∂unitIocMeasure
      = ∫ t, (beamSnd p : ℝ → ℂ) t * (intervalBump k t : ℂ) ∂unitIocMeasure :=
  (mem_beamFormSubmodule_iff (p : BeamPairSpace)).mp p.property k

/-- **The representation of form-space elements**: the first component is an affine function
plus the second primitive of the second component. -/
theorem beamV_repr (p : BeamV) :
    ∃ a b : ℂ, (beamEmbed p : ℝ → ℂ) =ᵐ[unitIocMeasure]
      fun t => a + b * (t : ℂ) + secondPrimitive ((beamSnd p : ℝ → ℂ)) t :=
  eq_affine_add_secondPrimitive_of_forall_integral_bumpD2
    (Lp.memLp _) (Lp.memLp _) (beamV_weak p)

/-! ## Injectivity of the embedding -/

/-- If the first component vanishes, so does the second: the bump family, being
`t²(1-t)²`-weighted monomials, is total against the second slot. -/
theorem beamEmbed_injective : Function.Injective beamEmbed := by
  have hker : ∀ p : BeamV, beamEmbed p = 0 → p = 0 := by
    intro p hp
    -- the second component is orthogonal to every bump
    have hw : ∀ k : ℕ,
        ∫ t, (beamSnd p : ℝ → ℂ) t * (intervalBump k t : ℂ) ∂unitIocMeasure = 0 := by
      intro k
      rw [← beamV_weak p k, hp]
      have hz : ((0 : BeamL2) : ℝ → ℂ) =ᵐ[unitIocMeasure] 0 :=
        Lp.coeFn_zero ℂ 2 unitIocMeasure
      rw [show ∫ t, ((0 : BeamL2) : ℝ → ℂ) t * (intervalBumpD2 k t : ℂ) ∂unitIocMeasure
          = ∫ t, (0 : ℂ) ∂unitIocMeasure from integral_congr_ae (by
        filter_upwards [hz] with t ht
        rw [ht]
        simp)]
      simp
    -- so the weighted function has all monomial moments zero
    have hmom : ∀ m : ℕ,
        ∫ t, ((beamSnd p : ℝ → ℂ) t * ((t : ℂ) ^ 2 * (1 - (t : ℂ)) ^ 2)) * (t : ℂ) ^ m
          ∂unitIocMeasure = 0 := by
      intro m
      have hfun : ∀ t : ℝ,
          ((beamSnd p : ℝ → ℂ) t * ((t : ℂ) ^ 2 * (1 - (t : ℂ)) ^ 2)) * (t : ℂ) ^ m
            = (beamSnd p : ℝ → ℂ) t * (intervalBump m t : ℂ) := by
        intro t
        have hb : (intervalBump m t : ℂ) = (t : ℂ) ^ (m + 2) * (1 - (t : ℂ)) ^ 2 := by
          rw [show intervalBump m t = t ^ (m + 2) * (1 - t) ^ 2 from rfl]
          push_cast
          ring
        rw [hb]
        ring
      calc ∫ t, ((beamSnd p : ℝ → ℂ) t * ((t : ℂ) ^ 2 * (1 - (t : ℂ)) ^ 2)) * (t : ℂ) ^ m
              ∂unitIocMeasure
          = ∫ t, (beamSnd p : ℝ → ℂ) t * (intervalBump m t : ℂ) ∂unitIocMeasure :=
            integral_congr_ae (Filter.Eventually.of_forall hfun)
        _ = 0 := hw m
    have hmem : MemLp (fun t : ℝ =>
        (beamSnd p : ℝ → ℂ) t * ((t : ℂ) ^ 2 * (1 - (t : ℂ)) ^ 2)) 2 unitIocMeasure := by
      refine MemLp.of_le (Lp.memLp (beamSnd p)) ?_ ?_
      · exact (Lp.aestronglyMeasurable _).mul
          (by fun_prop : Continuous fun t : ℝ =>
            (t : ℂ) ^ 2 * (1 - (t : ℂ)) ^ 2).aestronglyMeasurable
      · filter_upwards [ae_mem_unitIocMeasure] with t ht
        rw [norm_mul]
        have hb : ‖(t : ℂ) ^ 2 * (1 - (t : ℂ)) ^ 2‖ ≤ 1 := by
          rw [norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs]
          have h1 : |t| ≤ 1 := by
            rw [abs_of_pos ht.1]
            exact ht.2
          have h2 : ‖(1 : ℂ) - (t : ℂ)‖ ≤ 1 := by
            rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2])]
            linarith [ht.1]
          calc |t| ^ 2 * ‖(1 : ℂ) - (t : ℂ)‖ ^ 2
              ≤ 1 ^ 2 * 1 ^ 2 := by
                refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg t) h1 2)
                  (pow_le_pow_left₀ (norm_nonneg _) h2 2) (by positivity) (by norm_num)
            _ = 1 := by norm_num
        calc ‖(beamSnd p : ℝ → ℂ) t‖ * ‖(t : ℂ) ^ 2 * (1 - (t : ℂ)) ^ 2‖
            ≤ ‖(beamSnd p : ℝ → ℂ) t‖ * 1 :=
              mul_le_mul_of_nonneg_left hb (norm_nonneg _)
          _ = ‖(beamSnd p : ℝ → ℂ) t‖ := mul_one _
    have hzero := ae_eq_zero_of_forall_integral_pow_eq_zero hmem hmom
    -- divide out the weight, nonvanishing off a null set
    have hsnd : (beamSnd p : ℝ → ℂ) =ᵐ[unitIocMeasure] 0 := by
      filter_upwards [hzero, ae_mem_unitIocMeasure,
        (ae_iff.mpr (by simpa using unitIocMeasure_singleton 1) :
          ∀ᵐ t ∂unitIocMeasure, t ≠ 1)] with t ht htIoc htne
      have hne : (t : ℂ) ^ 2 * (1 - (t : ℂ)) ^ 2 ≠ 0 := by
        have h0 : (t : ℂ) ≠ 0 := by
          exact_mod_cast ne_of_gt htIoc.1
        have h1 : (1 : ℂ) - (t : ℂ) ≠ 0 := by
          intro hcon
          apply htne
          have : (t : ℂ) = 1 := by linear_combination -hcon
          exact_mod_cast this
        exact mul_ne_zero (pow_ne_zero 2 h0) (pow_ne_zero 2 h1)
      have := ht
      simp only [Pi.zero_apply] at this ⊢
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h hne
    -- both components vanish
    have hfst : (beamEmbed p : ℝ → ℂ) =ᵐ[unitIocMeasure] 0 := by
      rw [hp]
      exact Lp.coeFn_zero ℂ 2 unitIocMeasure
    have h1 : beamEmbed p = 0 := hp
    have h2 : beamSnd p = 0 := by
      refine Lp.ext ?_
      exact hsnd.trans (Lp.coeFn_zero ℂ 2 unitIocMeasure).symm
    -- conclude in the product
    have : (p : BeamPairSpace) = 0 := by
      have hcoords := WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2
      have hfst' : pairFst (p : BeamPairSpace) = 0 := h1
      have hsnd' : pairSnd (p : BeamPairSpace) = 0 := h2
      have : (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2) (p : BeamPairSpace)
          = 0 := Prod.ext hfst' hsnd'
      have := congrArg (WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm this
      simpa using this
    exact Subtype.ext this
  intro p q hpq
  have : beamEmbed (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have := hker _ this
  have := sub_eq_zero.mp (by simpa using this)
  exact this

/-! ## Density of the embedded domain -/

/-- A continuous function as an `L²` element of the unit interval. -/
def contToLp (g : ℝ → ℂ) (hg : Continuous g) : BeamL2 :=
  (MemLp.of_bound hg.aestronglyMeasurable (pairingBound g hg) (by
    filter_upwards [ae_mem_unitIocMeasure] with t ht
    exact pairingBound_spec g hg t ⟨ht.1.le, ht.2⟩)).toLp g

/-- A continuous function represents itself almost everywhere. -/
theorem coeFn_contToLp (g : ℝ → ℂ) (hg : Continuous g) :
    (contToLp g hg : ℝ → ℂ) =ᵐ[unitIocMeasure] g :=
  MemLp.coeFn_toLp _

/-- Two integrations by parts against the bump family, for a twice-differentiable real
function with no boundary conditions: every boundary term is killed by the bump's own
second-order vanishing at both endpoints. -/
theorem integral_mul_intervalBumpD2_eq_of_hasDerivAt {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ x, HasDerivAt f (f1 x) x) (hd1 : ∀ x, HasDerivAt f1 (f2 x) x) (k : ℕ) :
    ∫ t in (0 : ℝ)..1, f t * intervalBumpD2 k t
      = ∫ t in (0 : ℝ)..1, f2 t * intervalBump k t := by
  have step1 : ∫ t in (0 : ℝ)..1, f t * intervalBumpD2 k t
      = f 1 * intervalBumpD1 k 1 - f 0 * intervalBumpD1 k 0
        - ∫ t in (0 : ℝ)..1, f1 t * intervalBumpD1 k t :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hf.continuousOn (continuous_intervalBumpD1 k).continuousOn
      (fun x _ => hd x) (fun x _ => hasDerivAt_intervalBumpD1 k x)
      (hf1.intervalIntegrable 0 1)
      ((continuous_intervalBumpD2 k).intervalIntegrable 0 1)
  have step2 : ∫ t in (0 : ℝ)..1, f1 t * intervalBumpD1 k t
      = f1 1 * intervalBump k 1 - f1 0 * intervalBump k 0
        - ∫ t in (0 : ℝ)..1, f2 t * intervalBump k t :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hf1.continuousOn (continuous_intervalBump k).continuousOn
      (fun x _ => hd1 x) (fun x _ => hasDerivAt_intervalBump k x)
      (hf2.intervalIntegrable 0 1)
      ((continuous_intervalBumpD1 k).intervalIntegrable 0 1)
  rw [step1, step2]
  simp

/-- The pair of a real `C²` function and its second derivative lies in the form
subspace. -/
theorem contPair_mem {f f1 f2 : ℝ → ℝ}
    (hf : Continuous f) (hf1 : Continuous f1) (hf2 : Continuous f2)
    (hd : ∀ x, HasDerivAt f (f1 x) x) (hd1 : ∀ x, HasDerivAt f1 (f2 x) x) :
    ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
        (contToLp (fun t => (f t : ℂ)) (by fun_prop),
          contToLp (fun t => (f2 t : ℂ)) (by fun_prop)))
      ∈ beamFormSubmodule := by
  rw [mem_beamFormSubmodule_iff]
  intro k
  have hfst : pairFst ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
      (contToLp (fun t => (f t : ℂ)) (by fun_prop),
        contToLp (fun t => (f2 t : ℂ)) (by fun_prop)))
      = contToLp (fun t => (f t : ℂ)) (by fun_prop) := by
    rw [pairFst_apply]
    simp
  have hsnd : pairSnd ((WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
      (contToLp (fun t => (f t : ℂ)) (by fun_prop),
        contToLp (fun t => (f2 t : ℂ)) (by fun_prop)))
      = contToLp (fun t => (f2 t : ℂ)) (by fun_prop) := by
    rw [pairSnd_apply]
    simp
  rw [hfst, hsnd]
  have h1 : ∫ t, (contToLp (fun t => (f t : ℂ)) (by fun_prop) : ℝ → ℂ) t * bumpD2C k t
      ∂unitIocMeasure = ((∫ t in (0 : ℝ)..1, f t * intervalBumpD2 k t : ℝ) : ℂ) := by
    rw [← integral_unitIocMeasure_eq_intervalIntegral, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_contToLp (fun t => (f t : ℂ)) (by fun_prop)] with t ht
    rw [ht, bumpD2C]
    push_cast
    ring
  have h2 : ∫ t, (contToLp (fun t => (f2 t : ℂ)) (by fun_prop) : ℝ → ℂ) t * bumpC k t
      ∂unitIocMeasure = ((∫ t in (0 : ℝ)..1, f2 t * intervalBump k t : ℝ) : ℂ) := by
    rw [← integral_unitIocMeasure_eq_intervalIntegral, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_contToLp (fun t => (f2 t : ℂ)) (by fun_prop)] with t ht
    rw [ht, bumpC]
    push_cast
    ring
  rw [h1, h2, integral_mul_intervalBumpD2_eq_of_hasDerivAt hf hf1 hf2 hd hd1 k]

/-- The `L²` element of a real polynomial lies in the range of the embedding. -/
theorem contToLp_polynomial_mem_range (q : Polynomial ℝ) :
    contToLp (fun t => ((q.eval t : ℝ) : ℂ)) (by fun_prop)
      ∈ LinearMap.range (beamEmbed : BeamV →ₗ[ℂ] BeamL2) := by
  refine ⟨⟨(WithLp.prodContinuousLinearEquiv 2 ℂ BeamL2 BeamL2).symm
    (contToLp (fun t => ((q.eval t : ℝ) : ℂ)) (by fun_prop),
      contToLp (fun t => (((q.derivative.derivative).eval t : ℝ) : ℂ)) (by fun_prop)),
    contPair_mem (by fun_prop) (by fun_prop) (by fun_prop)
      (fun x => q.hasDerivAt x) (fun x => q.derivative.hasDerivAt x)⟩, ?_⟩
  rw [show (beamEmbed : BeamV →ₗ[ℂ] BeamL2) = beamEmbed.toLinearMap from rfl]
  change beamEmbed _ = _
  rw [beamEmbed_apply, pairFst_apply]
  simp

/-- **The embedded domain is dense.**  Real polynomial pairs lie in the range; Weierstrass
approximation and the density of bounded continuous functions in `L²` finish. -/
theorem denseRange_beamEmbed : DenseRange beamEmbed := by
  have hrange : ∀ x ∈ (Lp.boundedContinuousFunction ℂ 2 unitIocMeasure :
      Set BeamL2), x ∈ closure (Set.range beamEmbed) := by
    intro G hG
    obtain ⟨g, hg⟩ := Lp.mem_boundedContinuousFunction_iff.mp hG
    have hGae : ⇑G =ᵐ[unitIocMeasure] ⇑g := by
      have h1 := ContinuousMap.coeFn_toAEEqFun unitIocMeasure g.toContinuousMap
      rw [hg] at h1
      exact h1
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hδ : (0 : ℝ) < ε / 4 := by linarith
    obtain ⟨pre, hpre⟩ := exists_polynomial_near_of_continuousOn 0 1
      (fun t => (g t).re) (Complex.continuous_re.comp g.continuous).continuousOn _ hδ
    obtain ⟨pim, hpim⟩ := exists_polynomial_near_of_continuousOn 0 1
      (fun t => (g t).im) (Complex.continuous_im.comp g.continuous).continuousOn _ hδ
    obtain ⟨vre, hvre⟩ := contToLp_polynomial_mem_range pre
    obtain ⟨vim, hvim⟩ := contToLp_polynomial_mem_range pim
    refine ⟨beamEmbed (vre + Complex.I • vim), ⟨_, rfl⟩, ?_⟩
    have hy : beamEmbed (vre + Complex.I • vim)
        = contToLp (fun t => ((pre.eval t : ℝ) : ℂ)) (by fun_prop)
          + Complex.I • contToLp (fun t => ((pim.eval t : ℝ) : ℂ)) (by fun_prop) := by
      rw [map_add, map_smul]
      have h1 : beamEmbed vre = contToLp (fun t => ((pre.eval t : ℝ) : ℂ)) (by fun_prop) :=
        hvre
      have h2 : beamEmbed vim = contToLp (fun t => ((pim.eval t : ℝ) : ℂ)) (by fun_prop) :=
        hvim
      rw [h1, h2]
    rw [hy, dist_eq_norm]
    have hbound : ∀ᵐ t ∂unitIocMeasure,
        ‖(⇑(G - (contToLp (fun t => ((pre.eval t : ℝ) : ℂ)) (by fun_prop)
          + Complex.I • contToLp (fun t => ((pim.eval t : ℝ) : ℂ)) (by fun_prop)))) t‖
          ≤ 2 * (ε / 4) := by
      filter_upwards [ae_mem_unitIocMeasure, hGae,
        Lp.coeFn_sub G (contToLp (fun t => ((pre.eval t : ℝ) : ℂ)) (by fun_prop)
          + Complex.I • contToLp (fun t => ((pim.eval t : ℝ) : ℂ)) (by fun_prop)),
        Lp.coeFn_add (contToLp (fun t => ((pre.eval t : ℝ) : ℂ)) (by fun_prop))
          (Complex.I • contToLp (fun t => ((pim.eval t : ℝ) : ℂ)) (by fun_prop)),
        Lp.coeFn_smul Complex.I
          (contToLp (fun t => ((pim.eval t : ℝ) : ℂ)) (by fun_prop)),
        coeFn_contToLp (fun t => ((pre.eval t : ℝ) : ℂ)) (by fun_prop),
        coeFn_contToLp (fun t => ((pim.eval t : ℝ) : ℂ)) (by fun_prop)]
        with t htI hGt hsub hadd hsmul hcre hcim
      rw [hsub, Pi.sub_apply, hGt, hadd, Pi.add_apply, hsmul, Pi.smul_apply, hcre, hcim,
        smul_eq_mul]
      have hre := hpre t ⟨htI.1.le, htI.2⟩
      have him := hpim t ⟨htI.1.le, htI.2⟩
      calc ‖g t - (((pre.eval t : ℝ) : ℂ) + Complex.I * ((pim.eval t : ℝ) : ℂ))‖
          ≤ |(g t - (((pre.eval t : ℝ) : ℂ)
              + Complex.I * ((pim.eval t : ℝ) : ℂ))).re|
            + |(g t - (((pre.eval t : ℝ) : ℂ)
              + Complex.I * ((pim.eval t : ℝ) : ℂ))).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ = |(g t).re - pre.eval t| + |(g t).im - pim.eval t| := by simp
        _ ≤ ε / 4 + ε / 4 := by
            refine add_le_add ?_ ?_
            · rw [abs_sub_comm]
              exact hre.le
            · rw [abs_sub_comm]
              exact him.le
        _ = 2 * (ε / 4) := by ring
    have hb := eLpNorm_le_of_ae_bound (p := 2) (Lp.aestronglyMeasurable _) hbound
    rw [measure_univ, ENNReal.one_rpow, one_mul] at hb
    rw [Lp.norm_def]
    calc (eLpNorm (⇑(G - _)) 2 unitIocMeasure).toReal
        ≤ (ENNReal.ofReal (2 * (ε / 4))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
      _ = 2 * (ε / 4) := ENNReal.toReal_ofReal (by linarith)
      _ < ε := by linarith
  -- bounded continuous functions are dense, and their closure passes through the range
  intro x
  have hdense := Lp.boundedContinuousFunction_dense ℂ unitIocMeasure
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hx : x ∈ closure (Lp.boundedContinuousFunction ℂ 2 unitIocMeasure :
      Set BeamL2) := hdense x
  have hsubset : closure (Lp.boundedContinuousFunction ℂ 2 unitIocMeasure :
      Set BeamL2) ⊆ closure (Set.range beamEmbed) :=
    closure_minimal hrange isClosed_closure
  exact hsubset hx

/-! ## The coercive form data and its compact embedding -/

/-- Injectivity of the embedding's adjoint, from density of the range. -/
theorem beamEmbed_adjoint_injective :
    Function.Injective (ContinuousLinearMap.adjoint beamEmbed) := by
  have hker : ∀ x : BeamL2, ContinuousLinearMap.adjoint beamEmbed x = 0 → x = 0 := by
    intro x hx
    have horth : ∀ v : BeamV, ⟪beamEmbed v, x⟫_ℂ = 0 := by
      intro v
      rw [← ContinuousLinearMap.adjoint_inner_right beamEmbed v x, hx, inner_zero_right]
    have hclosed : IsClosed {y : BeamL2 | ⟪y, x⟫_ℂ = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hall : ∀ y : BeamL2, ⟪y, x⟫_ℂ = 0 := by
      intro y
      have hy : y ∈ closure (Set.range beamEmbed) := denseRange_beamEmbed y
      have hsub : Set.range beamEmbed ⊆ {y : BeamL2 | ⟪y, x⟫_ℂ = 0} := by
        rintro _ ⟨v, rfl⟩
        exact horth v
      exact (hclosed.closure_subset_iff.mpr hsub) hy
    have := hall x
    exact inner_self_eq_zero.mp this
  intro x y hxy
  have : ContinuousLinearMap.adjoint beamEmbed (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have := hker _ this
  exact sub_eq_zero.mp this

/-- The concrete coercive form data of the free beam: the form space carries the shifted
bending form as its own inner product, so the represented operator is the identity. -/
def beamCoerciveFormData : Abstract.CoerciveFormData (𝕜 := ℂ) (H := BeamL2) (V := BeamV) where
  embed := beamEmbed
  embed_injective := beamEmbed_injective
  embed_dense := denseRange_beamEmbed
  embed_adjoint_injective := beamEmbed_adjoint_injective
  formOperator := 1
  form_selfAdjoint := star_one _
  coercivityConstant := 1
  coercivity_pos := one_pos
  coercive := fun u => le_of_eq (by
    rw [show (1 : BeamV →L[ℂ] BeamV) u = u from rfl, one_mul,
      ← inner_self_eq_norm_sq (𝕜 := ℂ)])

/-- The pair coordinates of a form-space element decompose its squared norm. -/
theorem beamV_re_inner_self (u : BeamV) :
    RCLike.re ⟪u, u⟫_ℂ = ‖beamEmbed u‖ ^ 2 + ‖beamSnd u‖ ^ 2 := by
  have hcoe : ⟪u, u⟫_ℂ = ⟪(u : BeamPairSpace), (u : BeamPairSpace)⟫_ℂ := rfl
  rw [hcoe, WithLp.prod_inner_apply]
  rw [map_add]
  have h1 : RCLike.re ⟪(WithLp.ofLp (u : BeamPairSpace)).1,
      (WithLp.ofLp (u : BeamPairSpace)).1⟫_ℂ = ‖beamEmbed u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
    rfl
  have h2 : RCLike.re ⟪(WithLp.ofLp (u : BeamPairSpace)).2,
      (WithLp.ofLp (u : BeamPairSpace)).2⟫_ℂ = ‖beamSnd u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
    rfl
  rw [h1, h2]

/-- The concrete shifted beam form data: bending energy is the squared norm of the second
slot. -/
def beamShiftedFormData :
    Analytic.ShiftedBeamFormData (𝕜 := ℂ) (H := BeamL2) (V := BeamV) where
  toCoerciveFormData := beamCoerciveFormData
  bendingEnergy := fun u => ‖beamSnd u‖ ^ 2
  bending_nonnegative := fun u => sq_nonneg _
  form_energy_decomposition := fun u => by
    have h1 : RCLike.re ⟪beamCoerciveFormData.formOperator u, u⟫_ℂ
        = RCLike.re ⟪u, u⟫_ℂ := by
      rw [show beamCoerciveFormData.formOperator u = u from rfl]
    rw [h1, beamV_re_inner_self]
    rfl

/-- **The free-beam operator**: the self-adjoint nonnegative realization of the fourth
derivative with free boundary conditions on `L²(0,1]`. -/
def beamOperator : BeamL2 →ₗ.[ℂ] BeamL2 :=
  beamShiftedFormData.beamOperator

/-- The beam operator is self-adjoint. -/
theorem beamOperator_isSelfAdjoint : IsSelfAdjoint beamOperator :=
  beamShiftedFormData.beamOperator_isSelfAdjoint

/-- The beam operator is nonnegative. -/
theorem beamOperator_nonneg (x : beamOperator.domain) :
    0 ≤ RCLike.re ⟪beamOperator x, (x : BeamL2)⟫_ℂ :=
  beamShiftedFormData.beam_nonnegative x

/-! ## Compactness of the embedding -/

/-- The constant-one element of the beam `L²` space. -/
def beamOneLp : BeamL2 := contToLp (fun _ => (1 : ℂ)) continuous_const

/-- The coordinate element of the beam `L²` space. -/
def beamIdLp : BeamL2 := contToLp (fun t => (t : ℂ)) (by fun_prop)

/-- `beamOneLp` is the constant `1` almost everywhere. -/
theorem coeFn_beamOneLp : (beamOneLp : ℝ → ℂ) =ᵐ[unitIocMeasure] fun _ => (1 : ℂ) :=
  coeFn_contToLp _ _

/-- `beamIdLp` is `t ↦ t` almost everywhere. -/
theorem coeFn_beamIdLp : (beamIdLp : ℝ → ℂ) =ᵐ[unitIocMeasure] fun t => (t : ℂ) :=
  coeFn_contToLp _ _

/-- The affine defect of the embedding is a rank-two map into the affine span. -/
theorem exists_affine_of_beamEmbed_sub (p : BeamV) :
    ∃ a b : ℂ, beamEmbed p - secondPrimitiveCLM (beamSnd p)
      = a • beamOneLp + b • beamIdLp := by
  obtain ⟨a, b, hab⟩ := beamV_repr p
  refine ⟨a, b, ?_⟩
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (beamEmbed p) (secondPrimitiveCLM (beamSnd p)), hab,
    coeFn_secondPrimitiveCLM (beamSnd p), Lp.coeFn_add (a • beamOneLp) (b • beamIdLp),
    Lp.coeFn_smul a beamOneLp, Lp.coeFn_smul b beamIdLp, coeFn_beamOneLp,
    coeFn_beamIdLp] with t hsub habt hKt hadd hsa hsb h1 hT
  rw [hsub, Pi.sub_apply, habt, hKt, hadd]
  simp only [Pi.add_apply, hsa, hsb, Pi.smul_apply, smul_eq_mul, h1, hT]
  ring

/-- **Rellich compactness of the form-space embedding**, with no weak-topology argument:
the embedding is a rank-two affine part plus the compact second-primitive operator. -/
theorem isCompactOperator_beamEmbed : IsCompactOperator beamEmbed := by
  classical
  have hArange : ∀ p : BeamV,
      ∃ a b : ℂ, (beamEmbed - secondPrimitiveCLM.comp beamSnd) p
        = a • beamOneLp + b • beamIdLp := by
    intro p
    obtain ⟨a, b, hab⟩ := exists_affine_of_beamEmbed_sub p
    exact ⟨a, b, hab⟩
  have hAcompact : IsCompactOperator (beamEmbed - secondPrimitiveCLM.comp beamSnd) := by
    have hle : LinearMap.range
        ((beamEmbed - secondPrimitiveCLM.comp beamSnd : BeamV →L[ℂ] BeamL2)
          : BeamV →ₗ[ℂ] BeamL2)
        ≤ Submodule.span ℂ {beamOneLp, beamIdLp} := by
      rintro _ ⟨p, rfl⟩
      obtain ⟨a, b, hab⟩ := hArange p
      rw [show ((beamEmbed - secondPrimitiveCLM.comp beamSnd : BeamV →L[ℂ] BeamL2)
          : BeamV →ₗ[ℂ] BeamL2) p
          = (beamEmbed - secondPrimitiveCLM.comp beamSnd) p from rfl, hab]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
        (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    have : FiniteDimensional ℂ
        (Submodule.span ℂ ({beamOneLp, beamIdLp} : Set BeamL2)) := by
      apply FiniteDimensional.span_of_finite
      exact Set.toFinite _
    have : FiniteDimensional ℂ (LinearMap.range
        ((beamEmbed - secondPrimitiveCLM.comp beamSnd : BeamV →L[ℂ] BeamL2)
          : BeamV →ₗ[ℂ] BeamL2)) :=
      Submodule.finiteDimensional_of_le hle
    exact ContinuousLinearMap.isCompactOperator_of_finiteDimensional_range _
  have hKcompact : IsCompactOperator (secondPrimitiveCLM.comp beamSnd) :=
    IsCompactOperator.comp_clm (f := secondPrimitiveCLM)
      isCompactOperator_secondPrimitiveCLM beamSnd
  have hsum := hAcompact.add hKcompact
  have hfun : ⇑beamEmbed
      = ⇑(beamEmbed - secondPrimitiveCLM.comp beamSnd)
        + ⇑(secondPrimitiveCLM.comp beamSnd) := by
    funext p
    have hAp : (beamEmbed - secondPrimitiveCLM.comp beamSnd) p
        = beamEmbed p - secondPrimitiveCLM.comp beamSnd p := rfl
    simp only [Pi.add_apply, hAp]
    abel
  rw [show (⇑beamEmbed : BeamV → BeamL2) = _ from hfun]
  exact hsum

end

end Model
end FreeBeam
end DavisKahan
end TauCeti
