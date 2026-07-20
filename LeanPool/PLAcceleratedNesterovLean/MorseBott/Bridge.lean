/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.MorseBott.TubularProjection
import LeanPool.PLAcceleratedNesterovLean.MorseBott.NormalHessianBound
import LeanPool.PLAcceleratedNesterovLean.MorseBott.BridgeDefs
import LeanPool.PLAcceleratedNesterovLean.MorseBott.PLImpliesMB
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# PLMBBridge — Adapter/Bridge Lemmas for PLAcceleratedNesterovLeans Integration

## Overview

This file provides adapter/bridge lemmas connecting PLMB's generic
Morse–Bott and tubular-neighborhood theory (over an arbitrary
finite-dimensional real inner-product space `E`) to the concrete
setting used by PLAcceleratedNesterovLeans (where `E d := EuclideanSpace ℝ (Fin d)`).

## Bridge classification table

| Bridge                                     | Difficulty        | Mechanism                     |
|--------------------------------------------|-------------------|-------------------------------|
| `IsTubNeighSub.toIsTubularNeighborhood`    | Trivial           | Field-for-field               |
| `IsTubNeighSub.shrink`                     | Short proof       | Restriction to open subset    |
| `IsTubNeighSub.radius`                     | Short proof       | Per-point ball from openness  |
| `tubularProj` @ `Ed d`                    | Trivial           | Type specialization           |
| `tubular_neighborhood_projection` @ `Ed d` | Trivial           | Type specialization           |
| `‖Ext.gradient f x‖ = ‖fderiv ℝ f x‖`    | One-liner         | `LinearIsometryEquiv.norm_map`|
| `Ext.PL → MuPL`                           | Already in Thm3   | `ExternalThm3.pl_to_muPL`    |
| `hessian f x ξ ξ = Ext.hessianQuadForm`   | Already in Thm3   | `hessianQuadForm_eq_hessian`  |
| `Ext.PL + argmin → IsMuMB`                | Composition       | Pipeline of above bridges     |
| `muPL_implies_muMB` @ `Ed d`              | Trivial           | Type specialization           |

## References

- Rebjock & Boumal, "Fast convergence to non-isolated minima: four
  equivalent conditions for C² functions"
- PLAcceleratedNesterovLeans: `PLAcceleratedNesterovLean/Core/Defs.lean`,
  `PLAcceleratedNesterovLean/Convergence/LocalGeometry/Main.lean`
-/

open Filter Topology Metric Submodule InnerProductSpace Set

noncomputable section

namespace PLAcceleratedNesterovLean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ════════════════════════════════════════════════════════════════════════════
-- § 1. Instance verification
-- ════════════════════════════════════════════════════════════════════════════
--
-- `Ed d` (= `EuclideanSpace ℝ (Fin d)`) carries all type-class assumptions
-- that PLMB requires; everything is provided by Mathlib.

section InstanceVerification

variable (d : ℕ)

example : NormedAddCommGroup (Ed d)  := inferInstance
example : InnerProductSpace ℝ (Ed d) := inferInstance
example : FiniteDimensional ℝ (Ed d) := inferInstance

end InstanceVerification

-- ════════════════════════════════════════════════════════════════════════════
-- § 2. IsTubularNeighborhoodOfSubmanifold — derived properties
-- ════════════════════════════════════════════════════════════════════════════

namespace IsTubularNeighborhoodOfSubmanifold
variable {S U : Set E}

omit [FiniteDimensional ℝ E] in
lemma toIsTubularNeighborhood (h : IsTubularNeighborhoodOfSubmanifold S U) :
    IsTubularNeighborhood S U where
  isOpen := h.isOpen
  subset := h.subset
  uniqueProj := h.uniqueProj

omit [FiniteDimensional ℝ E] in
lemma shrink (h : IsTubularNeighborhoodOfSubmanifold S U)
    {U' : Set E} (hU'_open : IsOpen U') (hSU' : S ⊆ U') (hU'U : U' ⊆ U) :
    IsTubularNeighborhoodOfSubmanifold S U' where
  isOpen := hU'_open
  subset := hSU'
  uniqueProj := fun x hx => h.uniqueProj x (hU'U hx)
  submanifold_chart := by
    intro m hm
    obtain ⟨V, φ, δ, hδ, hφ_smooth, hφ0, hDφ0, hchart⟩ := h.submanifold_chart m hm
    exact ⟨V, φ, δ, hδ, hφ_smooth, hφ0, hDφ0, hchart⟩

omit [FiniteDimensional ℝ E] in
lemma radius (h : IsTubularNeighborhoodOfSubmanifold S U) :
    ∀ m ∈ S, ∃ r > 0, Metric.ball m r ⊆ U :=
  fun m hm => Metric.isOpen_iff.mp h.isOpen m (h.subset hm)

end IsTubularNeighborhoodOfSubmanifold

-- ════════════════════════════════════════════════════════════════════════════
-- § 3. tubularProj specialization to Ed d
-- ════════════════════════════════════════════════════════════════════════════

section TubularProjConcrete
variable {d : ℕ} {S U : Set (Ed d)}

/-- Nearest-point projection specialized to the Euclidean ambient space `Ed d`. -/
abbrev tubularProjEd (hTN : IsTubularNeighborhoodOfSubmanifold S U)
    (hne : S.Nonempty) : Ed d → Ed d :=
  tubularProj hTN hne

theorem tubular_neighborhood_projection_Ed
    (hTN : IsTubularNeighborhoodOfSubmanifold S U)
    (hne : S.Nonempty) :
    ∃ π : Ed d → Ed d,
      (∀ x ∈ U, π x ∈ S ∧ ‖x - π x‖ = Metric.infDist x S) ∧
      (∀ x ∈ S, π x = x) ∧
      (∀ x, π x ∈ S) ∧
      (∀ m ∈ S, ∀ x ∈ U, ‖x - π x‖ ≤ ‖x - m‖) ∧
      (∀ m ∈ S, ∃ δ > 0, ∀ x ∈ U, x ∈ Metric.ball m δ →
        ∀ t ∈ Icc (0 : ℝ) 1, (1 - t) • π x + t • x ∈ U) ∧
      (∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
        let y := (1 - t) • π x + t • x
        ‖y - π x‖ = Metric.infDist y S) ∧
      (∀ x ∈ U, fderiv ℝ π (π x) (x - π x) = 0) ∧
      (∀ m ∈ S, DifferentiableAt ℝ π m) ∧
      (∀ m ∈ S, ∀ u v : Ed d,
        @inner ℝ (Ed d) _ (fderiv ℝ π m u) v =
          @inner ℝ (Ed d) _ u (fderiv ℝ π m v)) ∧
      (∀ m ∈ S, ContDiffAt ℝ 1 π m) :=
  tubular_neighborhood_projection hTN hne

end TubularProjConcrete

-- ════════════════════════════════════════════════════════════════════════════
-- § 4. Norm bridge: ‖gradient f x‖ = ‖fderiv ℝ f x‖
-- ════════════════════════════════════════════════════════════════════════════
--
-- PLAcceleratedNesterovLeans' PL condition uses `‖gradient f x‖` (Mathlib's Riesz gradient).
-- PLMB's uses `‖fderiv ℝ f x‖` (operator norm of the Fréchet derivative).
-- These coincide because `toDual ℝ E` is a `LinearIsometryEquiv`.

section NormBridge

/-- The norm of the gradient equals the operator norm of the Fréchet derivative.
    This follows from `toDual ℝ E` being a linear isometry. -/
lemma norm_gradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
    ‖ExternalThm3.gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (toDual ℝ E).symm.norm_map (fderiv ℝ f x)

/-- Variant with `Ext.gradient` (BridgeDefs.lean). -/
lemma norm_extGradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
    ‖Ext.gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (toDual ℝ E).symm.norm_map (fderiv ℝ f x)

/-- Squared norms version. -/
lemma norm_sq_gradient_eq (f : E → ℝ) (x : E) :
    ‖ExternalThm3.gradient f x‖ ^ 2 = ‖fderiv ℝ f x‖ ^ 2 := by
  rw [norm_gradient_eq_norm_fderiv]

/-- Connection to Mathlib's `gradient` (from `Analysis.Calculus.Gradient.Basic`).

    Mathlib defines `gradient 𝕜 f x := (toDual 𝕜 E).symm (fderiv 𝕜 f x)`.
    Our `ExternalThm3.gradient` has the same definition (specialized to `ℝ`).
    They are definitionally equal. -/
lemma externalThm3_gradient_eq_gradient (f : E → ℝ) (x : E) :
    ExternalThm3.gradient f x = gradient f x :=
  rfl

/-- Connection between `Ext.gradient` and Mathlib's `gradient`. -/
lemma ext_gradient_eq_gradient (f : E → ℝ) (x : E) :
    Ext.gradient f x = gradient f x :=
  rfl

/-- Norm bridge for Mathlib's `gradient`. -/
lemma norm_mathlibGradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  (toDual ℝ E).symm.norm_map (fderiv ℝ f x)

end NormBridge

-- ════════════════════════════════════════════════════════════════════════════
-- § 5. PL condition bridges
-- ════════════════════════════════════════════════════════════════════════════
--
-- Three PL conditions coexist:
--
--  (a) PLMB's  `MuPL f μ x₀`  (LOCAL, ∀ᶠ near x₀, uses fderiv, relative to f(x₀))
--  (b) PLMB's  `ExternalThm3.PolyakLojasiewicz f μ U`
--      (GLOBAL on U, uses fderiv, relative to f⋆)
--  (c) PLAcceleratedNesterovLeans' `PolyakLojasiewicz f μ U`
--      (GLOBAL on U, uses gradient, relative to f⋆)
--
-- Bridge (b) → (a): `ExternalThm3.pl_to_muPL`
-- Bridge (c) ↔ (b): via the norm bridge (§4), `‖gradient f x‖ = ‖fderiv ℝ f x‖`

section PLBridge

variable {f : E → ℝ} {μ : ℝ} {U : Set E}

end PLBridge

-- ════════════════════════════════════════════════════════════════════════════
-- § 6. Hessian bridge
-- ════════════════════════════════════════════════════════════════════════════
--   `ExternalThm3.hessianQuadForm_eq_hessian`  : hessianQuadForm = hessian applied twice
--   `ExternalThm3.hessian_coercive_globalMin_PL`: Hessian coercive under PL (our language)
--   `ExternalThm3.hessianQuadForm_bound`        : same in hessianQuadForm language
--   `ExternalThm3.hessianQuadForm_bound_forall` : quantified version

-- ════════════════════════════════════════════════════════════════════════════
-- § 7. Main theorem specializations at Ed d
-- ════════════════════════════════════════════════════════════════════════════
--
-- PLMB's main theorems are generic over E.  Concrete versions at `Ed d`
-- for direct use in PLAcceleratedNesterovLeans.

section MainTheorems

variable {d : ℕ}

/-- **Corollary 2.17** at `Ed d`: μ-PŁ ⟹ μ-Morse–Bott. -/
theorem muPL_implies_muMB_Ed (f : Ed d → ℝ) (μ : ℝ) (x₀ : Ed d)
    (hμ : 0 < μ) (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀)
    (hPL : MuPL f μ x₀) :
    IsMuMB f μ x₀ :=
  muPL_implies_muMB f μ x₀ hμ hf hmin hPL

/-- **Theorem 2.16** at `Ed d`: μ-PŁ ⟹ local-min set is a C¹ submanifold. -/
theorem MuPL.implies_submanifold_Ed (f : Ed d → ℝ) (μ : ℝ) (x₀ : Ed d)
    (hμ : 0 < μ) (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀)
    (hPL : MuPL f μ x₀) :
    IsLocalSubmanifoldAt (localMinSet f x₀) x₀ (hessianKer f x₀) :=
  MuPL.implies_submanifold f μ x₀ hμ hf hmin hPL

/-- **Hessian coercivity** at `Ed d`: PŁ ⟹ `D²f(x₀) ≥ μ` on ker(Hess)⊥. -/
theorem hessian_coercive_Ed (f : Ed d → ℝ) (μ : ℝ) (x₀ : Ed d)
    (hμ : 0 < μ) (hf : ContDiffAt ℝ 2 f x₀) (hmin : IsLocalMin f x₀)
    (hPL : MuPL f μ x₀) :
    ∀ v ∈ (hessianKer f x₀).orthogonal,
      hessian f x₀ v v ≥ μ * ‖v‖ ^ 2 :=
  hessian_coercive_on_orthogonal_of_MuPL_impl f μ x₀ hμ hf hmin hPL

end MainTheorems

-- ════════════════════════════════════════════════════════════════════════════
-- § 8. Full pipeline:  ExternalThm3.PL + argmin → IsMuMB  at Ed d
-- ════════════════════════════════════════════════════════════════════════════
--
-- Combines the PL bridge (ExternalThm3.pl_to_muPL) with the main theorem
-- (muPL_implies_muMB) to go from PLAcceleratedNesterovLeans' global PL condition directly to
-- the Morse–Bott property.
--
-- Difficulty: COMPOSITION of previously established bridges.

section Pipeline

variable {d : ℕ}

/-- **Full pipeline at `Ed d`**: global PL + global minimizer ⟹ μ-MB.

    Given:
    - `f : Ed d → ℝ` is C²
    - `f` satisfies the Polyak–Łojasiewicz condition on `U` with constant `μ`
    - `x₀` is a global minimizer (i.e. `x₀ ∈ ExternalThm3.argminSet f`)
    - `U ∈ 𝓝 x₀` (x₀ is in the interior of U)

    Conclude: `f` satisfies μ-Morse–Bott at `x₀`.

    This is the bridge lemma that PLAcceleratedNesterovLeans' `local_fiberwise_geometry` can
    use to invoke PLMB's structural results. -/
theorem globalPL_implies_muMB_Ed
    (f : Ed d → ℝ) (μ : ℝ) (U : Set (Ed d)) (x₀ : Ed d)
    (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 2 f x₀)
    (hPL : ExternalThm3.PolyakLojasiewicz f μ U)
    (hU : U ∈ 𝓝 x₀)
    (hmin : x₀ ∈ ExternalThm3.argminSet f) :
    IsMuMB f μ x₀ := by
  have hmuPL : MuPL f μ x₀ := ExternalThm3.pl_to_muPL f μ U x₀ hmin hU hPL
  have hmin_loc : IsLocalMin f x₀ := ExternalThm3.argminSet_isLocalMin f x₀ hmin
  exact muPL_implies_muMB f μ x₀ hμ hf hmin_loc hmuPL

/-- **Submanifold conclusion** via global PL + tubular neighborhood.
    Under the same hypotheses, `localMinSet f x₀` is a C¹ submanifold
    with tangent space `hessianKer f x₀`. -/
theorem globalPL_implies_submanifold_Ed
    (f : Ed d → ℝ) (μ : ℝ) (U : Set (Ed d)) (x₀ : Ed d)
    (hμ : 0 < μ)
    (hf : ContDiffAt ℝ 2 f x₀)
    (hPL : ExternalThm3.PolyakLojasiewicz f μ U)
    (hU : U ∈ 𝓝 x₀)
    (hmin : x₀ ∈ ExternalThm3.argminSet f) :
    IsLocalSubmanifoldAt (localMinSet f x₀) x₀ (hessianKer f x₀) :=
  MuPL.implies_submanifold f μ x₀ hμ hf
    (ExternalThm3.argminSet_isLocalMin f x₀ hmin)
    (ExternalThm3.pl_to_muPL f μ U x₀ hmin hU hPL)

end Pipeline

-- ════════════════════════════════════════════════════════════════════════════
-- § 9. Namespace unification:  Ext.* ≡ ExternalThm3.* ≡ PLAcceleratedNesterovLean.*
-- ════════════════════════════════════════════════════════════════════════════
--
-- PLMB has two copies of PLAcceleratedNesterovLeans-compatible definitions:
--   • `Ext.*`           (BridgeDefs.lean) — used by ExternalThm1
--   • `ExternalThm3.*`  (ExternalThm3.lean) — used by ExternalThm3
--
-- PLAcceleratedNesterovLeans defines the "originals" at root level:
--   • `argminSet`, `fStar`, `PolyakLojasiewicz`, `hessianQuadForm`
--
-- All three families are definitionally identical (same body, different names).
-- We document the equalities here.  When PLAcceleratedNesterovLeans imports PLMB, these
-- become trivial `rfl` rewrites.

section NamespaceUnification

variable (f : E → ℝ) (μ : ℝ) (U : Set E) (x ξ : E)

-- argminSet
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma ext_argminSet_eq : Ext.argminSet f = ExternalThm3.argminSet f := rfl

-- fStar
omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma ext_fStar_eq : Ext.fStar f = ExternalThm3.fStar f := rfl

-- gradient
lemma ext_gradient_eq_externalThm3 :
    Ext.gradient f x = ExternalThm3.gradient f x := rfl

-- hessianQuadForm
lemma ext_hessianQuadForm_eq_externalThm3 :
    Ext.hessianQuadForm f x ξ = ExternalThm3.hessianQuadForm f x ξ := rfl

end NamespaceUnification

end PLAcceleratedNesterovLean
