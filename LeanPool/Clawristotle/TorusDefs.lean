/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Torus Type Definitions and Differential Operators

Defines the 3-torus T^3 = (R/Z)^3, the projection `torusMk`, the periodic lift,
and differential operators (`torusGradX`, `torusDivX`, `torusCurlX`) via the
periodic lift. The `FlatTorus3` instance is assembled in `TorusInstance.lean`.
-/

open MeasureTheory Matrix Finset BigOperators Real Filter

noncomputable section

-- ============================================================================
-- The concrete 3-torus
-- ============================================================================

/-- The 3-torus: product of three circles with period 1. -/
abbrev Torus3 := Fin 3 → AddCircle (1 : ℝ)

-- Period 1 > 0, needed for AddCircle.measureSpace
instance : Fact (0 < (1 : ℝ)) := ⟨one_pos⟩

-- All measure/topology instances come for free:
instance : CompactSpace Torus3 := inferInstance
instance : T2Space Torus3 := inferInstance
instance : IsFiniteMeasure (volume : Measure Torus3) := inferInstance
instance : SigmaFinite (volume : Measure Torus3) := inferInstance

-- ============================================================================
-- The projection (covering map) ℝ³ → T³
-- ============================================================================

/-- The quotient map ℝ³ → T³, sending each coordinate to its equivalence class. -/
def torusMk (x : Fin 3 → ℝ) : Torus3 := fun i => QuotientAddGroup.mk (x i)

-- torusMk is surjective (every point in T³ has a preimage)
lemma torusMk_surjective : Function.Surjective torusMk := by
  intro x
  -- For each coordinate, QuotientAddGroup.mk is surjective
  choose f hf using fun i => Quotient.exists_rep (x i)
  exact ⟨f, funext hf⟩

-- ============================================================================
-- Periodic lift: for f : T³ → ℝ, the composition f ∘ torusMk : ℝ³ → ℝ
-- ============================================================================

/-- The periodic lift of a function on the torus to ℝ³. -/
def periodicLift (f : Torus3 → ℝ) : (Fin 3 → ℝ) → ℝ := f ∘ torusMk

-- The lift IS periodic (by construction):
lemma periodicLift_periodic (f : Torus3 → ℝ) (x : Fin 3 → ℝ) (i : Fin 3) :
    periodicLift f (x + Pi.single i 1) = periodicLift f x := by
  simp only [periodicLift, Function.comp_apply]
  congr 1
  ext j
  simp only [torusMk, Pi.add_apply]
  by_cases h : j = i
  · subst h; simp only [Pi.single_eq_same]
    rw [QuotientAddGroup.eq]
    exact ⟨-1, by simp⟩
  · simp [Pi.single_eq_of_ne h]

-- ============================================================================
-- The key lemma: fderiv of the periodic lift is well-defined
-- (independent of the choice of lift point)
-- ============================================================================

/-- The periodic lift at shifted argument equals the original when the shift
    maps to the same torus point. -/
lemma periodicLift_shift (f : Torus3 → ℝ) (x y : Fin 3 → ℝ)
    (h : torusMk x = torusMk y) (z : Fin 3 → ℝ) :
    periodicLift f (z + (x - y)) = periodicLift f z := by
  simp only [periodicLift, Function.comp_apply]
  congr 1; ext i
  simp only [torusMk, Pi.add_apply, Pi.sub_apply]
  -- x i - y i is an integer, so adding it doesn't change the equivalence class
  have hi : (fun i => QuotientAddGroup.mk (x i) : Torus3) i =
            (fun i => QuotientAddGroup.mk (y i) : Torus3) i :=
    congr_fun h i
  simp only at hi
  rw [QuotientAddGroup.eq] at hi ⊢
  obtain ⟨n, hn⟩ := hi
  refine ⟨n, ?_⟩
  simp at hn ⊢
  linarith

/-- fderiv of the lift at two points that map to the same torus point are equal.
    This follows because f(x) = f(x + n) for integer n, so the 1-jets agree. -/
lemma periodicLift_fderiv_eq (f : Torus3 → ℝ) (x y : Fin 3 → ℝ)
    (h : torusMk x = torusMk y) :
    fderiv ℝ (periodicLift f) x = fderiv ℝ (periodicLift f) y := by
  -- periodicLift f ∘ (· + (x - y)) = periodicLift f
  have hshift : (fun z => periodicLift f (z + (x - y))) = periodicLift f := by
    ext z; exact periodicLift_shift f x y h z
  -- By fderiv_comp_add_right:
  -- fderiv (fun z => f(z + (x-y))) y = fderiv f (y + (x-y)) = fderiv f x
  have h1 : fderiv ℝ (fun z => periodicLift f (z + (x - y))) y =
             fderiv ℝ (periodicLift f) (y + (x - y)) := fderiv_comp_add_right (x - y)
  -- y + (x - y) = x
  have h2 : y + (x - y) = x := by ext i; simp [Pi.add_apply, Pi.sub_apply]
  rw [h2] at h1
  -- But also fderiv (fun z => f(z + (x-y))) = fderiv f (by hshift)
  rw [hshift] at h1
  exact h1.symm

-- ============================================================================
-- Differential operators on T³ via the periodic lift
-- ============================================================================

/-- Spatial gradient on T³.
    For f : T³ → ℝ, we lift to ℝ³, compute fderiv, and read off components.
    This is well-defined by periodicLift_fderiv_eq. -/
def torusGradX (f : Torus3 → ℝ) (x : Torus3) : Fin 3 → ℝ :=
  -- Choose any preimage of x
  let x₀ := (torusMk_surjective x).choose
  fun i => fderiv ℝ (periodicLift f) x₀ (Pi.single i 1)

/-- Spatial divergence on T³. -/
def torusDivX (F : Torus3 → (Fin 3 → ℝ)) (x : Torus3) : ℝ :=
  let x₀ := (torusMk_surjective x).choose
  ∑ i : Fin 3, fderiv ℝ (fun y => periodicLift (fun z => F z i) y) x₀ (Pi.single i 1)

/-- Spatial curl on T³. -/
def torusCurlX (F : Torus3 → (Fin 3 → ℝ)) (x : Torus3) : Fin 3 → ℝ :=
  let x₀ := (torusMk_surjective x).choose
  let d := fun i j => fderiv ℝ (fun y => periodicLift (fun z => F z j) y) x₀ (Pi.single i 1)
  ![d 1 2 - d 2 1, d 2 0 - d 0 2, d 0 1 - d 1 0]

-- ============================================================================
-- Key intermediate: periodicLift of torusGradX equals fderiv of periodicLift
-- ============================================================================

/-- The periodic lift of the gradient component equals the fderiv of the lift.
    This resolves the `choose` ambiguity: at each point, the gradient uses a
    chosen preimage, but by periodicLift_fderiv_eq, the fderiv is the same
    for any preimage of the same torus point. -/
lemma periodicLift_torusGradX (φ : Torus3 → ℝ) (i : Fin 3)
    (y : Fin 3 → ℝ) :
    periodicLift (fun z => torusGradX φ z i) y =
    fderiv ℝ (periodicLift φ) y (Pi.single i 1) := by
  simp only [periodicLift, Function.comp_apply, torusGradX]
  have h := periodicLift_fderiv_eq φ ((torusMk_surjective (torusMk y)).choose) y
    (torusMk_surjective (torusMk y)).choose_spec
  exact congr_fun (congr_arg DFunLike.coe h) (Pi.single i 1)

-- ============================================================================
-- Helper lemmas: fderiv for const_mul and exp without differentiability
-- ============================================================================

/-- fderiv(c * g) = c • fderiv(g) unconditionally.
    When g is differentiable: by fderiv_const_smul.
    When g is not differentiable and c ≠ 0: c * g is also not differentiable,
    so both sides are the zero map.
    When c = 0: both sides are 0. -/
lemma fderiv_const_mul_always {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (g : E → ℝ) (x : E) :
    fderiv ℝ (fun y => c * g y) x = c • fderiv ℝ g x := by
  by_cases hc : c = 0
  · have : (fun y => c * g y) = fun _ => (0 : ℝ) := by ext y; simp [hc]
    rw [this]; simp [hc]
  by_cases hg : DifferentiableAt ℝ g x
  · exact fderiv_const_smul hg c
  · have hcg : ¬ DifferentiableAt ℝ (fun y => c * g y) x := by
      intro h; apply hg
      exact (show (fun y => c⁻¹ * (c * g y)) = g from by ext y; field_simp) ▸ h.const_mul c⁻¹
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt hcg]
    simp

/-- fderiv(exp ∘ g) x = exp(g x) • fderiv g x unconditionally.
    When g is differentiable: by fderiv_exp.
    When g is not differentiable: exp ∘ g is also not differentiable
    (since g = log ∘ exp ∘ g and log is smooth on (0,∞)), so both sides are 0. -/
lemma fderiv_exp_comp_always {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : E → ℝ) (x : E) :
    fderiv ℝ (fun y => Real.exp (g y)) x = Real.exp (g x) • fderiv ℝ g x := by
  by_cases hg : DifferentiableAt ℝ g x
  · exact fderiv_exp hg
  · have heg : ¬ DifferentiableAt ℝ (fun y => Real.exp (g y)) x := by
      intro h; apply hg
      have hlog : DifferentiableAt ℝ Real.log (Real.exp (g x)) :=
        Real.differentiableAt_log (ne_of_gt (Real.exp_pos (g x)))
      have h2 := hlog.comp x h
      have : (Real.log ∘ fun y => Real.exp (g y)) = g := by ext y; simp [Real.log_exp]
      rwa [this] at h2
    rw [fderiv_zero_of_not_differentiableAt hg, fderiv_zero_of_not_differentiableAt heg]
    simp

-- ============================================================================
-- Clairaut's theorem (symmetry of mixed partial derivatives)
-- ============================================================================

/-- Clairaut's theorem via fderiv: ∂²f/∂xᵢ∂xⱼ = ∂²f/∂xⱼ∂xᵢ for C² functions. -/
theorem clairaut_fderiv {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (i j : Fin n) (hg : ContDiff ℝ 2 g) :
    fderiv ℝ (fun y => fderiv ℝ g y (Pi.single j 1)) x (Pi.single i 1) =
    fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single j 1) := by
  have hsymm := (hg.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num [minSmoothness])
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.contDiffAt (x := x)).fderiv_right (le_refl _)).differentiableAt one_ne_zero
  have key : ∀ v w, fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fderiv ℝ g) x w v := by
    intro v w
    have h1 := fderiv_clm_apply hd (differentiableAt_const v)
    simp only [show fderiv ℝ (fun _ : Fin n → ℝ => v) x = 0 from by
      exact congr_fun (fderiv_const (𝕜 := ℝ) (E := Fin n → ℝ) v) x,
      ContinuousLinearMap.comp_zero, zero_add] at h1
    exact congr_fun (congr_arg DFunLike.coe h1) w
  rw [key, key]; exact hsymm.eq (Pi.single i 1) (Pi.single j 1)

-- ============================================================================
-- Basic FlatTorus3 axiom proofs
-- ============================================================================

/-- hGradConst: gradient of constant function vanishes. -/
theorem torus_hGradConst (φ : Torus3 → ℝ) (hconst : ∀ x y, φ x = φ y) :
    ∀ x, torusGradX φ x = 0 := by
  intro x
  ext i
  simp only [torusGradX, Pi.zero_apply]
  have : periodicLift φ = fun _ => φ x :=
    funext (fun y => by simp only [periodicLift, Function.comp_apply]; exact hconst _ _)
  rw [this, hasFDerivAt_const (φ x) _ |>.fderiv]
  rfl

/-- hGradAdd: gradient additivity for C¹ functions. -/
theorem torus_hGradAdd' (f g : Torus3 → ℝ)
    (hf : ContDiff ℝ 1 (periodicLift f)) (hg : ContDiff ℝ 1 (periodicLift g)) :
    ∀ x, torusGradX (fun y => f y + g y) x =
      torusGradX f x + torusGradX g x := by
  intro x
  ext i
  simp only [torusGradX, Pi.add_apply]
  have hlift : periodicLift (fun y => f y + g y) = periodicLift f + periodicLift g := by
    ext y; simp [periodicLift]
  rw [hlift, fderiv_add (hf.differentiable one_ne_zero).differentiableAt
    (hg.differentiable one_ne_zero).differentiableAt]
  rfl

-- ============================================================================
-- Integration axioms (from Haar measure properties)
-- ============================================================================

/-- hSpatialVelocityFubini: swap spatial and velocity integrals.
    Uses SigmaFinite (from CompactSpace + IsFiniteMeasure). -/
theorem torus_hSpatialVelocityFubini (F : Torus3 → (Fin 3 → ℝ) → ℝ)
    (hF_joint : Integrable (Function.uncurry F) (volume.prod volume)) :
    (∫ x, ∫ v, F x v) = ∫ v, ∫ x, F x v :=
  integral_integral_swap hF_joint

-- ============================================================================
-- Compact manifold axioms
-- ============================================================================

/-- hSpatialPos: positive function has positive integral. -/
theorem torus_hSpatialPos (g : Torus3 → ℝ) (hg_pos : ∀ x, 0 < g x)
    (hg_cont : Continuous g) :
    0 < ∫ x, g x := by
  have h1 : Integrable g :=
    hg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)
  exact integral_pos_of_integrable_nonneg_nonzero hg_cont h1
    (fun x => le_of_lt (hg_pos x)) (ne_of_gt (hg_pos default))

/-- hSpatialNonnegZero: nonneg function with zero integral is zero. -/
theorem torus_hSpatialNonnegZero (g : Torus3 → ℝ)
    (hg_nn : ∀ x, 0 ≤ g x) (hg_int : (∫ x, g x) = 0)
    (hg_cont : Continuous g) :
    ∀ x, g x = 0 :=
  fun x => congr_fun
    ((Continuous.ae_eq_iff_eq (volume : Measure Torus3) hg_cont continuous_const).mp
      ((integral_eq_zero_iff_of_nonneg hg_nn
        (hg_cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))).mp
        hg_int))
    x

-- ============================================================================
-- Helper lemmas for torus IBP
-- ============================================================================

/-- torusMk is an open quotient map (product of open quotient maps). -/
lemma isOpenQuotientMap_torusMk : IsOpenQuotientMap torusMk := by
  have : torusMk = Pi.map (fun (_ : Fin 3) =>
    (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ))) := by ext x j; rfl
  exact this ▸ IsOpenQuotientMap.piMap (fun _ =>
    IsOpenQuotientMap.of_isOpenMap_isQuotientMap
      QuotientAddGroup.isOpenMap_coe
      (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))))

/-- torusGradX is continuous (uses quotient map property). -/
lemma continuous_torusGradX (f : Torus3 → ℝ) (i : Fin 3)
    (hf : ContDiff ℝ 1 (periodicLift f)) :
    Continuous (fun x => torusGradX f x i) := by
  rw [isOpenQuotientMap_torusMk.isQuotientMap.continuous_iff,
      show (fun x => torusGradX f x i) ∘ torusMk =
        fun y => fderiv ℝ (periodicLift f) y (Pi.single i 1)
        from funext (periodicLift_torusGradX f i)]
  exact (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

end
