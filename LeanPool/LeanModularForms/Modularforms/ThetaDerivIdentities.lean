/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.JacobiTheta
public import LeanPool.LeanModularForms.Modularforms.Derivative
public import LeanPool.LeanModularForms.Modularforms.DimensionFormulas
public import LeanPool.LeanModularForms.Modularforms.AtImInfty
public import LeanPool.LeanModularForms.Modularforms.EisensteinAsymptotics

/-! # ThetaDerivIdentities -/


@[expose] public section

/-!
# Theta Derivative Identities

This file proves the Serre derivative identities for Jacobi theta functions
(Blueprint Proposition 6.52, equations (32)–(34)):

* `serre_D_H₂` : serreD 2 H₂ = (1/6) * (H₂² + 2*H₂*H₄)
* `serre_D_H₃` : serreD 2 H₃ = (1/6) * (H₂² - H₄²)
* `serre_D_H₄` : serreD 2 H₄ = -(1/6) * (2*H₂*H₄ + H₄²)

## Contents

### Error Terms (Phases 1-5)
* Error terms `f₂`, `f₃`, `f₄` definitions
* MDifferentiable proofs for error terms
* Relation `f₂ + f₄ = f₃` (from `jacobi_identity` in JacobiTheta.lean)
* S/T transformation rules: `f₂_S_action`, `f₂_T_action`, `f₄_S_action`, `f₄_T_action`

### Level-1 Invariants (Phase 6)
* Level-1 invariant `thetaG` (weight 6): g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄
* Level-1 invariant `thetaH` (weight 8): h = f₂² + f₂f₄ + f₄²
* S/T invariance: `theta_g_S_action`, `theta_g_T_action`, `theta_h_S_action`, `theta_h_T_action`

### Cusp Form Arguments (Phase 7)
* Tendsto lemmas for f₂, f₄, thetaG, thetaH at infinity
* Cusp form construction for thetaG and thetaH

### Dimension Vanishing (Phase 8)
* thetaG = 0 and thetaH = 0 by weight < 12 cusp form vanishing

### Main Deduction (Phase 9)
* f₂ = f₃ = f₄ = 0

### Main Theorems (Phase 10)
* serre_D_H₂, serre_D_H₃, serre_D_H₄

## Strategy

We define error terms f₂, f₃, f₄ = (LHS - RHS) and prove their transformation rules under
the S and T generators of SL(2,ℤ). The key results are:
- f₂|S = -f₄, f₂|T = -f₂
- f₄|S = -f₂, f₄|T = f₃

Using these transformation rules, we construct g and h such that g|S = g, g|T = g, h|S = h, h|T = h.
This makes g and h into level-1 (SL(2,ℤ)-invariant) modular forms.

We then show g and h vanish at infinity (Phase 7), hence are cusp forms. By dimension
vanishing (Phase 8), all level-1 cusp forms of weight < 12 are zero. This gives g = h = 0,
from which we deduce f₂ = f₃ = f₄ = 0 (Phase 9), yielding the main theorems (Phase 10).
-/

open UpperHalfPlane hiding I
open Complex Real Asymptotics Filter Topology Manifold SlashInvariantForm Matrix ModularGroup
  ModularForm SlashAction MatrixGroups CongruenceSubgroup

local notation "Γ " n:100 => Gamma n


/-!
## Phase 1: Error Term Definitions
-/

/-- Error term for the ∂₂H₂ identity: f₂ = ∂₂H₂ - (1/6)(H₂² + 2H₂H₄) -/
noncomputable def f₂ : ℍ → ℂ :=
  serreD 2 H₂ - (1/6 : ℂ) • (H₂ * (H₂ + (2 : ℂ) • H₄))

/-- Error term for the ∂₂H₃ identity: f₃ = ∂₂H₃ - (1/6)(H₂² - H₄²) -/
noncomputable def f₃ : ℍ → ℂ :=
  serreD 2 H₃ - (1/6 : ℂ) • (H₂ ^ 2 - H₄ ^ 2)

/-- Error term for the ∂₂H₄ identity: f₄ = ∂₂H₄ + (1/6)(2H₂H₄ + H₄²) -/
noncomputable def f₄ : ℍ → ℂ :=
  serreD 2 H₄ + (1/6 : ℂ) • (H₄ * ((2 : ℂ) • H₂ + H₄))

/-- f₂ decomposes as serreD 2 H₂ + (-1/6) • (H₂ * (H₂ + 2*H₄)) -/
lemma f₂_decompose :
    f₂ = serreD (2 : ℤ) H₂ + ((-1/6 : ℂ) • (H₂ * (H₂ + (2 : ℂ) • H₄))) := by
  ext z; simp [f₂, sub_eq_add_neg]; ring

/-- f₄ decomposes as serreD 2 H₄ + (1/6) • (H₄ * (2*H₂ + H₄)) -/
lemma f₄_decompose :
    f₄ = serreD (2 : ℤ) H₄ + ((1/6 : ℂ) • (H₄ * ((2 : ℂ) • H₂ + H₄))) := by rfl

/-!
## Phase 2: MDifferentiable for Error Terms
-/

/-- f₂ is MDifferentiable -/
lemma f₂_MDifferentiable : MDiff f₂ := by unfold f₂; fun_prop

/-- f₃ is MDifferentiable -/
lemma f₃_MDifferentiable : MDiff f₃ := by unfold f₃; fun_prop

/-- f₄ is MDifferentiable -/
lemma f₄_MDifferentiable : MDiff f₄ := by unfold f₄; fun_prop

/-!
## Phase 3-4: Relation f₂ + f₄ = f₃
-/

/-- The error terms satisfy f₂ + f₄ = f₃ (from Jacobi identity) -/
lemma f₂_add_f₄_eq_f₃ : f₂ + f₄ = f₃ := by
  ext z; simp only [Pi.add_apply, f₂, f₃, f₄]
  -- Key relation: serreD 2 H₂ z + serreD 2 H₄ z = serreD 2 H₃ z (via Jacobi identity)
  have h_serre : serreD 2 H₂ z + serreD 2 H₄ z = serreD 2 H₃ z := by
    have h := congrFun (serre_D_add (2 : ℤ) H₂ H₄ H₂_SIF_MDifferentiable H₄_SIF_MDifferentiable) z
    simp only [Pi.add_apply, Int.cast_ofNat] at h
    rw [← h]
    congr 1
    exact jacobi_identity
  calc serreD 2 H₂ z - 1/6 * (H₂ z * (H₂ z + 2 * H₄ z)) +
       (serreD 2 H₄ z + 1/6 * (H₄ z * (2 * H₂ z + H₄ z)))
      = (serreD 2 H₂ z + serreD 2 H₄ z) +
        (1/6 * (H₄ z * (2 * H₂ z + H₄ z)) - 1/6 * (H₂ z * (H₂ z + 2 * H₄ z))) := by ring
    _ = serreD 2 H₃ z +
        (1/6 * (H₄ z * (2 * H₂ z + H₄ z)) - 1/6 * (H₂ z * (H₂ z + 2 * H₄ z))) := by rw [h_serre]
    _ = serreD 2 H₃ z - 1/6 * (H₂ z ^ 2 - H₄ z ^ 2) := by ring

/-!
## Phase 5: S/T Transformation Rules for f₂, f₄

These transformations depend on `serre_D_slash_equivariant` (which has a sorry in Derivative.lean).
The proofs use:
- serre_D_slash_equivariant: (serreD k F)|[k+2]γ = serreD k (F|[k]γ)
- H₂_S_action: H₂|[2]S = -H₄
- H₄_S_action: H₄|[2]S = -H₂
- H₂_T_action: H₂|[2]T = -H₂
- H₃_T_action: H₃|[2]T = H₄
- H₄_T_action: H₄|[2]T = H₃

From these, we get:
- (serreD 2 H₂)|[4]S = serreD 2 (H₂|[2]S) = serreD 2 (-H₄) = -serreD 2 H₄
- Products transform multiplicatively: (H₂·G)|[4]S = (H₂|[2]S)·(G|[2]S)
-/

/-- f₂ transforms under S as f₂|S = -f₄.

Proof outline using serre_D_slash_equivariant:
1. (serreD 2 H₂)|[4]S = serreD 2 (H₂|[2]S) = serreD 2 (-H₄) = -serreD 2 H₄
2. (H₂(H₂ + 2H₄))|[4]S = (-H₄)((-H₄) + 2(-H₂)) = H₄(H₄ + 2H₂)
3. f₂|[4]S = -serreD 2 H₄ - (1/6)H₄(H₄ + 2H₂) = -f₄

Key lemmas used:
- serre_D_slash_equivariant: (serreD k F)|[k+2]γ = serreD k (F|[k]γ)
- serre_D_smul: serreD k (c • F) = c • serreD k F (used for negation)
- mul_slash_SL2: (f * g)|[k1+k2]A = (f|[k1]A) * (g|[k2]A)
- add_slash, SL_smul_slash for linearity -/
lemma f₂_S_action : (f₂ ∣[(4 : ℤ)] S) = -f₄ := by
  -- Step 1: (serreD 2 H₂)|[4]S = -serreD 2 H₄ (via equivariance)
  have h_serre_term : (serreD (2 : ℤ) H₂ ∣[(4 : ℤ)] S) = -serreD (2 : ℤ) H₄ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable S, H₂_S_action]
    simpa using serre_D_smul 2 (-1) H₄ H₄_SIF_MDifferentiable
  -- Step 2: (H₂ + 2•H₄)|[2]S = -(H₄ + 2•H₂)
  have h_lin_comb : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) = -(H₄ + (2 : ℂ) • H₂) := by
    rw [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Step 3: Product (H₂ * (H₂ + 2•H₄))|[4]S = H₄ * (H₄ + 2•H₂)
  have h_prod : ((H₂ * (H₂ + (2 : ℂ) • H₄)) ∣[(4 : ℤ)] S) = H₄ * (H₄ + (2 : ℂ) • H₂) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl, mul_slash_SL2 2 2 S _ _, H₂_S_action, h_lin_comb]
    ext z; simp [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply]; ring
  -- Combine: f₂|[4]S = -serreD 2 H₄ - (1/6) * H₄ * (2*H₂ + H₄) = -f₄
  rw [f₂_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]; unfold f₄
  ext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]; ring_nf

/-- f₂ transforms under T as f₂|T = -f₂.

Proof outline:
1. (serreD 2 H₂)|[4]T = serreD 2 (H₂|[2]T) = serreD 2 (-H₂) = -serreD 2 H₂
2. (H₂(H₂ + 2H₄))|[4]T = (-H₂)((-H₂) + 2H₃)
   Using Jacobi H₃ = H₂ + H₄: -H₂ + 2H₃ = -H₂ + 2(H₂ + H₄) = H₂ + 2H₄
   So: (H₂(H₂ + 2H₄))|[4]T = (-H₂)(H₂ + 2H₄)
3. f₂|[4]T = -serreD 2 H₂ - (1/6)(-H₂)(H₂ + 2H₄)
           = -serreD 2 H₂ + (1/6)H₂(H₂ + 2H₄)
           = -(serreD 2 H₂ - (1/6)H₂(H₂ + 2H₄)) = -f₂ -/
lemma f₂_T_action : (f₂ ∣[(4 : ℤ)] T) = -f₂ := by
  -- Step 1: (serreD 2 H₂)|[4]T = -serreD 2 H₂ (via equivariance)
  have h_serre_term : (serreD (2 : ℤ) H₂ ∣[(4 : ℤ)] T) = -serreD (2 : ℤ) H₂ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₂ H₂_SIF_MDifferentiable T, H₂_T_action]
    simpa using serre_D_smul 2 (-1) H₂ H₂_SIF_MDifferentiable
  -- Step 2: (H₂ + 2•H₄)|[2]T = H₂ + 2•H₄ using Jacobi: H₃ = H₂ + H₄
  -- -H₂ + 2H₃ = -H₂ + 2(H₂ + H₄) = H₂ + 2H₄
  have h_lin_comb : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] T) = H₂ + (2 : ℂ) • H₄ := by
    rw [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
    ext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    simp only [show H₃ z = H₂ z + H₄ z by rw [← Pi.add_apply, (congrFun jacobi_identity z).symm]]
    ring
  -- Step 3: Product (H₂ * (H₂ + 2•H₄))|[4]T = (-H₂) * (H₂ + 2•H₄)
  have h_prod : ((H₂ * (H₂ + (2 : ℂ) • H₄)) ∣[(4 : ℤ)] T) = -H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl, mul_slash_SL2 2 2 T _ _, H₂_T_action, h_lin_comb]
  -- Combine: f₂|[4]T = -serreD 2 H₂ - (1/6)(-H₂)(H₂ + 2H₄) = -f₂
  rw [f₂_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]
  ext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]; ring

/-- f₄ transforms under S as f₄|S = -f₂.

Proof outline (symmetric to f₂_S_action):
1. (serreD 2 H₄)|[4]S = serreD 2 (H₄|[2]S) = serreD 2 (-H₂) = -serreD 2 H₂
2. (H₄(2H₂ + H₄))|[4]S = (-H₂)(2(-H₄) + (-H₂)) = H₂(H₂ + 2H₄)
3. f₄|[4]S = -serreD 2 H₂ + (1/6)H₂(H₂ + 2H₄) = -f₂ -/
lemma f₄_S_action : (f₄ ∣[(4 : ℤ)] S) = -f₂ := by
  -- Step 1: (serreD 2 H₄)|[4]S = -serreD 2 H₂ (via equivariance)
  have h_serre_term : (serreD (2 : ℤ) H₄ ∣[(4 : ℤ)] S) = -serreD (2 : ℤ) H₂ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₄ H₄_SIF_MDifferentiable S, H₄_S_action]
    simpa using serre_D_smul 2 (-1) H₂ H₂_SIF_MDifferentiable
  -- Step 2: (2•H₂ + H₄)|[2]S = -(2•H₄ + H₂)
  have h_lin_comb : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] S) = -((2 : ℂ) • H₄ + H₂) := by
    rw [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Step 3: Product (H₄ * (2•H₂ + H₄))|[4]S = H₂ * (H₂ + 2•H₄)
  have h_prod : ((H₄ * ((2 : ℂ) • H₂ + H₄)) ∣[(4 : ℤ)] S) = H₂ * (H₂ + (2 : ℂ) • H₄) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl, mul_slash_SL2 2 2 S _ _, H₄_S_action, h_lin_comb]
    ext z; simp [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply]; ring
  -- Combine: f₄|[4]S = -serreD 2 H₂ + (1/6) * H₂ * (H₂ + 2H₄) = -f₂
  rw [f₄_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]; unfold f₂
  ext z
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.mul_apply, smul_eq_mul]
  ring_nf

/-- f₄ transforms under T as f₄|T = f₃.

Proof outline:
1. (serreD 2 H₄)|[4]T = serreD 2 (H₄|[2]T) = serreD 2 H₃
2. (H₄(2H₂ + H₄))|[4]T = H₃(2(-H₂) + H₃) = H₃(H₃ - 2H₂)
   Using Jacobi H₃ = H₂ + H₄: H₃ - 2H₂ = H₄ - H₂
3. f₄|[4]T = serreD 2 H₃ + (1/6)H₃(H₃ - 2H₂)
   But H₂² - H₄² = (H₂ - H₄)(H₂ + H₄) = (H₂ - H₄)H₃
   So (1/6)(H₂² - H₄²) = -(1/6)H₃(H₄ - H₂) = -(1/6)H₃(H₃ - 2H₂)
   Thus f₃ = serreD 2 H₃ - (1/6)(H₂² - H₄²) = f₄|[4]T -/
lemma f₄_T_action : (f₄ ∣[(4 : ℤ)] T) = f₃ := by
  -- Step 1: (serreD 2 H₄)|[4]T = serreD 2 H₃ (via equivariance)
  have h_serre_term : (serreD (2 : ℤ) H₄ ∣[(4 : ℤ)] T) = serreD (2 : ℤ) H₃ := by
    rw [show (4 : ℤ) = 2 + 2 from rfl,
        serre_D_slash_equivariant (2 : ℤ) H₄ H₄_SIF_MDifferentiable T, H₄_T_action]
  -- Step 2: (2•H₂ + H₄)|[2]T = H₄ - H₂ using Jacobi: H₃ = H₂ + H₄
  -- -2H₂ + H₃ = -2H₂ + (H₂ + H₄) = H₄ - H₂
  have h_lin_comb : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) = H₄ - H₂ := by
    rw [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
    ext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, smul_eq_mul]
    simp only [show H₃ z = H₂ z + H₄ z by rw [← Pi.add_apply, (congrFun jacobi_identity z).symm]]
    ring
  -- Step 3: Product (H₄ * (2•H₂ + H₄))|[4]T = H₃ * (H₄ - H₂)
  have h_prod : ((H₄ * ((2 : ℂ) • H₂ + H₄)) ∣[(4 : ℤ)] T) = H₃ * (H₄ - H₂) := by
    rw [show (4 : ℤ) = 2 + 2 from rfl, mul_slash_SL2 2 2 T _ _, H₄_T_action, h_lin_comb]
  -- Combine: f₄|[4]T = serreD 2 H₃ + (1/6) * H₃ * (H₄ - H₂) = f₃
  rw [f₄_decompose, add_slash, SL_smul_slash, h_serre_term, h_prod]; unfold f₃
  ext z
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul]
  rw [show H₃ z = H₂ z + H₄ z by rw [← Pi.add_apply, (congrFun jacobi_identity z).symm]]
  ring_nf

/-!
## Phase 6: Level-1 Invariants g, h
-/

/-- Level-1 invariant of weight 6: g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄ -/
noncomputable def thetaG : ℍ → ℂ :=
  ((2 : ℂ) • H₂ + H₄) * f₂ + (H₂ + (2 : ℂ) • H₄) * f₄

/-- Level-1 invariant of weight 8: h = f₂² + f₂f₄ + f₄² -/
noncomputable def thetaH : ℍ → ℂ := f₂ ^ 2 + f₂ * f₄ + f₄ ^ 2

/-- g is invariant under S.

Proof: g = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄
Under S: H₂ ↦ -H₄, H₄ ↦ -H₂, f₂ ↦ -f₄, f₄ ↦ -f₂
g|S = (2(-H₄) + (-H₂))(-f₄) + ((-H₄) + 2(-H₂))(-f₂)
    = (2H₄ + H₂)f₄ + (H₄ + 2H₂)f₂
    = g -/
lemma theta_g_S_action : (thetaG ∣[(6 : ℤ)] S) = thetaG := by
  -- Linear combination transforms: (2•H₂ + H₄)|S = -(2•H₄ + H₂), (H₂ + 2•H₄)|S = -(H₄ + 2•H₂)
  have h_2H₂_H₄ : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] S) = -((2 : ℂ) • H₄ + H₂) := by
    simp only [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  have h_H₂_2H₄ : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] S) = -(H₄ + (2 : ℂ) • H₂) := by
    simp only [add_slash, SL_smul_slash, H₂_S_action, H₄_S_action]
    ext z; simp [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]; ring
  -- Product transforms using mul_slash_SL2
  have h_term1 : ((((2 : ℂ) • H₂ + H₄) * f₂) ∣[(6 : ℤ)] S) = ((2 : ℂ) • H₄ + H₂) * f₄ := by
    have hmul := mul_slash_SL2 2 4 S ((2 : ℂ) • H₂ + H₄) f₂
    simp only [h_2H₂_H₄, f₂_S_action] at hmul
    convert hmul using 1
    all_goals first
      | (ext z; simp only [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]; ring)
      | norm_num
  have h_term2 : (((H₂ + (2 : ℂ) • H₄) * f₄) ∣[(6 : ℤ)] S) = (H₄ + (2 : ℂ) • H₂) * f₂ := by
    have hmul := mul_slash_SL2 2 4 S (H₂ + (2 : ℂ) • H₄) f₄
    simp only [h_H₂_2H₄, f₄_S_action] at hmul
    convert hmul using 1
    all_goals first
      | (ext z; simp only [Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul]; ring)
      | norm_num
  -- g|S = (2H₄ + H₂)f₄ + (H₄ + 2H₂)f₂ = g
  simp only [thetaG, add_slash, h_term1, h_term2]
  ext z; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply]; ring

/-- g is invariant under T.

Proof: Under T: H₂ ↦ -H₂, H₄ ↦ H₃, f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
g|T = (2(-H₂) + H₃)(-f₂) + ((-H₂) + 2H₃)(f₂ + f₄)
Using Jacobi: H₃ = H₂ + H₄, simplifies to g. -/
lemma theta_g_T_action : (thetaG ∣[(6 : ℤ)] T) = thetaG := by
  -- Under T: H₂ → -H₂, H₄ → H₃, f₂ → -f₂, f₄ → f₃
  -- Linear combination transforms: (2•H₂ + H₄)|T = -2•H₂ + H₃, (H₂ + 2•H₄)|T = -H₂ + 2•H₃
  have h_2H₂_H₄ : (((2 : ℂ) • H₂ + H₄) ∣[(2 : ℤ)] T) = -(2 : ℂ) • H₂ + H₃ := by
    simp only [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action, smul_neg]
    ext z; simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]; ring
  have h_H₂_2H₄ : ((H₂ + (2 : ℂ) • H₄) ∣[(2 : ℤ)] T) = -H₂ + (2 : ℂ) • H₃ := by
    simp only [add_slash, SL_smul_slash, H₂_T_action, H₄_T_action]
  -- Product transforms
  have h_term1 : ((((2 : ℂ) • H₂ + H₄) * f₂) ∣[(6 : ℤ)] T) = (-(2 : ℂ) • H₂ + H₃) * (-f₂) := by
    have hmul := mul_slash_SL2 2 4 T ((2 : ℂ) • H₂ + H₄) f₂
    simp only [h_2H₂_H₄, f₂_T_action] at hmul; exact hmul
  have h_term2 : (((H₂ + (2 : ℂ) • H₄) * f₄) ∣[(6 : ℤ)] T) = (-H₂ + (2 : ℂ) • H₃) * f₃ := by
    have hmul := mul_slash_SL2 2 4 T (H₂ + (2 : ℂ) • H₄) f₄
    simp only [h_H₂_2H₄, f₄_T_action] at hmul; exact hmul
  -- Combine and simplify using Jacobi: H₃ = H₂ + H₄, f₃ = f₂ + f₄
  simp only [thetaG, add_slash, h_term1, h_term2]
  ext z; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  rw [(congrFun jacobi_identity z).symm, (congrFun f₂_add_f₄_eq_f₃ z).symm]
  simp only [Pi.add_apply]; ring

/-- h is invariant under S.

Proof: h = f₂² + f₂f₄ + f₄²
Under S: f₂|[4]S = -f₄, f₄|[4]S = -f₂
Using mul_slash_SL2: (f₂²)|[8]S = (f₂|[4]S)² = (-f₄)² = f₄²
                     (f₂f₄)|[8]S = (f₂|[4]S)(f₄|[4]S) = (-f₄)(-f₂) = f₂f₄
                     (f₄²)|[8]S = (f₄|[4]S)² = (-f₂)² = f₂²
So h|[8]S = f₄² + f₂f₄ + f₂² = f₂² + f₂f₄ + f₄² = h -/
lemma theta_h_S_action : (thetaH ∣[(8 : ℤ)] S) = thetaH := by
  -- Under S: f₂ ↦ -f₄, f₄ ↦ -f₂
  -- (f₂²)|S = f₄², (f₄²)|S = f₂², (f₂f₄)|S = f₂f₄
  have h_f₂_sq : ((f₂ ^ 2) ∣[(8 : ℤ)] S) = f₄ ^ 2 := by
    have hmul := mul_slash_SL2 4 4 S f₂ f₂
    simp only [f₂_S_action] at hmul
    convert hmul using 1 <;> ext <;> simp [sq]
  have h_f₄_sq : ((f₄ ^ 2) ∣[(8 : ℤ)] S) = f₂ ^ 2 := by
    have hmul := mul_slash_SL2 4 4 S f₄ f₄
    simp only [f₄_S_action] at hmul
    convert hmul using 1 <;> ext <;> simp [sq]
  have h_f₂f₄ : ((f₂ * f₄) ∣[(8 : ℤ)] S) = f₂ * f₄ := by
    have hmul := mul_slash_SL2 4 4 S f₂ f₄
    simp only [f₂_S_action, f₄_S_action] at hmul
    convert hmul using 1 <;> ext z <;>
      simp [Pi.mul_apply, Pi.neg_apply, mul_comm]
  -- h|S = f₄² + f₂f₄ + f₂² = h
  simp only [thetaH, add_slash, h_f₂_sq, h_f₂f₄, h_f₄_sq]
  ext z; simp only [Pi.add_apply, Pi.mul_apply, sq]; ring

/-- h is invariant under T.

Proof: Under T: f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
h|T = (-f₂)² + (-f₂)(f₂ + f₄) + (f₂ + f₄)²
    = f₂² - f₂² - f₂f₄ + f₂² + 2f₂f₄ + f₄²
    = f₂² + f₂f₄ + f₄² = h -/
lemma theta_h_T_action : (thetaH ∣[(8 : ℤ)] T) = thetaH := by
  -- Under T: f₂ ↦ -f₂, f₄ ↦ f₃ = f₂ + f₄
  -- (f₂²)|T = f₂², (f₄²)|T = (f₂+f₄)², (f₂f₄)|T = (-f₂)(f₂+f₄)
  have h_f₂_sq : ((f₂ ^ 2) ∣[(8 : ℤ)] T) = f₂ ^ 2 := by
    have hmul := mul_slash_SL2 4 4 T f₂ f₂
    simp only [f₂_T_action] at hmul
    convert hmul using 1 <;> ext <;> simp [sq]
  have h_f₄_sq : ((f₄ ^ 2) ∣[(8 : ℤ)] T) = (f₂ + f₄) ^ 2 := by
    have hmul := mul_slash_SL2 4 4 T f₄ f₄
    simp only [f₄_T_action] at hmul
    convert hmul using 1
    · ext; simp [sq]
    · ext z; simp only [Pi.pow_apply, Pi.mul_apply, sq]
      rw [(congrFun f₂_add_f₄_eq_f₃ z).symm, Pi.add_apply]
  have h_f₂f₄ : ((f₂ * f₄) ∣[(8 : ℤ)] T) = (-f₂) * (f₂ + f₄) := by
    have hmul := mul_slash_SL2 4 4 T f₂ f₄
    simp only [f₂_T_action, f₄_T_action] at hmul
    convert hmul using 1
    all_goals first
      | (ext z
         simp only [Pi.mul_apply, Pi.neg_apply]
         rw [(congrFun f₂_add_f₄_eq_f₃ z).symm, Pi.add_apply])
      | norm_num
  -- h|T = f₂² + (-f₂)(f₂+f₄) + (f₂+f₄)² = h
  simp only [thetaH, add_slash, h_f₂_sq, h_f₂f₄, h_f₄_sq]
  ext z; simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, sq]; ring

/-!
## Phase 7: Cusp Form Arguments

We need to show g and h vanish at infinity.
The tendsto lemmas for H₂, H₃, H₄ are already in AtImInfty.lean:
- H₂_tendsto_atImInfty : Tendsto H₂ atImInfty (𝓝 0)
- H₃_tendsto_atImInfty : Tendsto H₃ atImInfty (𝓝 1)
- H₄_tendsto_atImInfty : Tendsto H₄ atImInfty (𝓝 1)
-/

/-- thetaG is MDifferentiable (from MDifferentiable of f₂, f₄, H₂, H₄) -/
lemma theta_g_MDifferentiable : MDiff thetaG :=
  ((mdifferentiable_const.mul H₂_SIF_MDifferentiable).add H₄_SIF_MDifferentiable).mul
    f₂_MDifferentiable |>.add <|
  (H₂_SIF_MDifferentiable.add (mdifferentiable_const.mul H₄_SIF_MDifferentiable)).mul
    f₄_MDifferentiable

/-- thetaH is MDifferentiable (from MDifferentiable of f₂, f₄) -/
lemma theta_h_MDifferentiable : MDiff thetaH := by
  unfold thetaH
  exact ((f₂_MDifferentiable.pow 2).add (f₂_MDifferentiable.mul f₄_MDifferentiable)).add
    (f₄_MDifferentiable.pow 2)

/-- thetaG is slash-invariant under Γ(1) in GL₂(ℝ) form -/
lemma theta_g_slash_invariant_GL :
    ∀ γ ∈ Subgroup.map (SpecialLinearGroup.mapGL ℝ) (Γ 1),
    thetaG ∣[(6 : ℤ)] γ = thetaG :=
  slashaction_generators_GL2R thetaG 6 theta_g_S_action theta_g_T_action

/-- thetaH is slash-invariant under Γ(1) in GL₂(ℝ) form -/
lemma theta_h_slash_invariant_GL :
    ∀ γ ∈ Subgroup.map (SpecialLinearGroup.mapGL ℝ) (Γ 1),
    thetaH ∣[(8 : ℤ)] γ = thetaH :=
  slashaction_generators_GL2R thetaH 8 theta_h_S_action theta_h_T_action

/-- thetaG as a SlashInvariantForm of level 1 -/
noncomputable def thetaGSIF : SlashInvariantForm (Γ 1) 6 where
  toFun := thetaG
  slash_action_eq' := theta_g_slash_invariant_GL

/-- thetaH as a SlashInvariantForm of level 1 -/
noncomputable def thetaHSIF : SlashInvariantForm (Γ 1) 8 where
  toFun := thetaH
  slash_action_eq' := theta_h_slash_invariant_GL

/-- f₂ tends to 0 at infinity.
Proof: f₂ = serreD 2 H₂ - (1/6)H₂(H₂ + 2H₄)
Since H₂ → 0 and serreD 2 H₂ = D H₂ - (1/6)E₂ H₂ → 0,
we get f₂ → 0 - 0 = 0. -/
lemma f₂_tendsto_atImInfty : Tendsto f₂ atImInfty (𝓝 0) := by
  have h_serre_H₂ : Tendsto (serreD 2 H₂) atImInfty (𝓝 0) := by
    have hD := D_tendsto_zero_of_isBoundedAtImInfty H₂_SIF_MDifferentiable isBoundedAtImInfty_H₂
    have hE₂H₂ : Tendsto (fun z => E₂ z * H₂ z) atImInfty (𝓝 0) := by
      simpa using E₂_tendsto_one_atImInfty.mul H₂_tendsto_atImInfty
    convert hD.sub (hE₂H₂.const_mul ((2 : ℂ) / 12)) using 2 <;> simp [serreD]; ring
  have h_prod : Tendsto (H₂ * (H₂ + 2 * H₄)) atImInfty (𝓝 0) := by
    have h := H₂_tendsto_atImInfty.mul
      (H₂_tendsto_atImInfty.add (H₄_tendsto_atImInfty.const_mul 2))
    simp only [zero_mul] at h
    exact h
  have hf := h_serre_H₂.sub (h_prod.const_mul (1/6 : ℂ))
  rw [show (0 : ℂ) - 1 / 6 * 0 = 0 from by ring] at hf
  simp only [f₂]; exact hf

/-- f₄ tends to 0 at infinity.
Proof: f₄ = serreD 2 H₄ + (1/6)H₄(2H₂ + H₄)
serreD 2 H₄ = D H₄ - (1/6)E₂ H₄ → 0 - (1/6)*1*1 = -1/6 (since H₄ → 1, E₂ → 1)
H₄(2H₂ + H₄) → 1*(0 + 1) = 1
So f₄ → -1/6 + (1/6)*1 = 0. -/
lemma f₄_tendsto_atImInfty : Tendsto f₄ atImInfty (𝓝 0) := by
  have h_serre_H₄ : Tendsto (serreD 2 H₄) atImInfty (𝓝 (-(1/6 : ℂ))) := by
    convert serre_D_tendsto_neg_k_div_12 2 H₄ H₄_SIF_MDifferentiable isBoundedAtImInfty_H₄
      H₄_tendsto_atImInfty using 2
    · rw [show ((2 : ℤ) : ℂ) = 2 from by norm_num]
    · norm_num
  have h_sum : Tendsto (2 * H₂ + H₄) atImInfty (𝓝 1) := by
    have h := (H₂_tendsto_atImInfty.const_mul 2).add H₄_tendsto_atImInfty
    norm_num at h; exact h
  have h_prod : Tendsto (H₄ * (2 * H₂ + H₄)) atImInfty (𝓝 1) := by
    have h := H₄_tendsto_atImInfty.mul h_sum
    norm_num at h; exact h
  have h_scaled : Tendsto (fun z => (1/6 : ℂ) * (H₄ z * (2 * H₂ z + H₄ z)))
      atImInfty (𝓝 (1/6 : ℂ)) := by
    have h := h_prod.const_mul (1/6 : ℂ)
    norm_num at h; exact h
  have hf := h_serre_H₄.add h_scaled
  rw [show -(1 / 6 : ℂ) + 1 / 6 = 0 from by ring] at hf
  simp only [f₄]; exact hf

/-- thetaG tends to 0 at infinity.
thetaG = (2H₂ + H₄)f₂ + (H₂ + 2H₄)f₄.
Since 2H₂ + H₄ → 1, H₂ + 2H₄ → 2, and f₂, f₄ → 0, we get thetaG → 0. -/
lemma theta_g_tendsto_atImInfty : Tendsto thetaG atImInfty (𝓝 0) := by
  have h_coef1 : Tendsto (2 * H₂ + H₄) atImInfty (𝓝 1) := by
    have h := (H₂_tendsto_atImInfty.const_mul 2).add H₄_tendsto_atImInfty
    norm_num at h; exact h
  have h_coef2 : Tendsto (H₂ + 2 * H₄) atImInfty (𝓝 2) := by
    have h := H₂_tendsto_atImInfty.add (H₄_tendsto_atImInfty.const_mul 2)
    norm_num at h; exact h
  have hf := (h_coef1.mul f₂_tendsto_atImInfty).add (h_coef2.mul f₄_tendsto_atImInfty)
  norm_num at hf
  simp only [thetaG]; exact hf

/-- thetaH tends to 0 at infinity.
thetaH = f₂² + f₂f₄ + f₄² → 0 + 0 + 0 = 0 as f₂, f₄ → 0. -/
lemma theta_h_tendsto_atImInfty : Tendsto thetaH atImInfty (𝓝 0) := by
  have hf := ((f₂_tendsto_atImInfty.pow 2).add
      (f₂_tendsto_atImInfty.mul f₄_tendsto_atImInfty)).add
      (f₄_tendsto_atImInfty.pow 2)
  norm_num at hf; simp only [thetaH]; exact hf

private noncomputable def theta_g_CF : CuspForm (Γ 1) 6 :=
  cuspFormOfSIFTendstoZero thetaGSIF theta_g_MDifferentiable theta_g_tendsto_atImInfty

private noncomputable def theta_h_CF : CuspForm (Γ 1) 8 :=
  cuspFormOfSIFTendstoZero thetaHSIF theta_h_MDifferentiable theta_h_tendsto_atImInfty

/-!
## Phase 8: Apply Dimension Vanishing
-/

/-- g = 0 by dimension argument: weight-6 cusp forms vanish. -/
lemma theta_g_eq_zero : thetaG = 0 :=
  congr_arg (·.toFun)
    (rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 6 (by norm_num)) theta_g_CF)

/-- h = 0 by dimension argument: weight-8 cusp forms vanish. -/
lemma theta_h_eq_zero : thetaH = 0 :=
  congr_arg (·.toFun)
    (rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero 8 (by norm_num)) theta_h_CF)

/-!
## HSumSq: H₂² + H₂H₄ + H₄²
-/

/-- H₂² + H₂H₄ + H₄² -/
noncomputable def HSumSq : ℍ → ℂ := fun z => H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2

/-- HSumSq is MDifferentiable -/
lemma H_sum_sq_MDifferentiable : MDiff HSumSq := by
  unfold HSumSq
  exact ((H₂_SIF_MDifferentiable.pow 2).add (H₂_SIF_MDifferentiable.mul H₄_SIF_MDifferentiable)).add
    (H₄_SIF_MDifferentiable.pow 2)

/-- HSumSq → 1 at infinity -/
lemma H_sum_sq_tendsto : Tendsto HSumSq atImInfty (𝓝 1) := by
  unfold HSumSq
  simpa [sq] using
    ((H₂_tendsto_atImInfty.mul H₂_tendsto_atImInfty).add
      (H₂_tendsto_atImInfty.mul H₄_tendsto_atImInfty)).add
      (H₄_tendsto_atImInfty.mul H₄_tendsto_atImInfty)

/-- HSumSq ≠ 0 (since it tends to 1 ≠ 0) -/
lemma H_sum_sq_ne_zero : HSumSq ≠ 0 := fun h =>
  one_ne_zero (tendsto_nhds_unique tendsto_const_nhds (h ▸ H_sum_sq_tendsto)).symm

/-- 3 * HSumSq ≠ 0 -/
lemma three_H_sum_sq_ne_zero : (fun z => 3 * HSumSq z) ≠ 0 :=
  fun h => H_sum_sq_ne_zero
    (funext fun z => (mul_eq_zero.mp (congrFun h z)).resolve_left (by norm_num))

/-- 3 * HSumSq is MDifferentiable -/
lemma three_H_sum_sq_MDifferentiable : MDiff (fun z => 3 * HSumSq z) :=
  mdifferentiable_const.mul H_sum_sq_MDifferentiable

/-!
## E₄ = HSumSq (dimension argument)

E₄ and HSumSq are both weight-4 level-1 modular forms tending to 1 at ∞.
Their difference is a weight-4 cusp form, hence zero by dimension vanishing.
-/

/-- S-action on HSumSq: invariant since H₂|S = -H₄ and H₄|S = -H₂ -/
private lemma H_sum_sq_S_action : (HSumSq ∣[(4 : ℤ)] S) = HSumSq := by
  have h_eq : HSumSq = H₂ * H₂ + H₂ * H₄ + H₄ * H₄ := by ext z; simp [HSumSq, sq]
  simp only [h_eq, show (4 : ℤ) = 2 + 2 from by norm_num,
    SlashAction.add_slash, mul_slash_SL2 2 2 S _ _, H₂_S_action, H₄_S_action]
  ext z; simp [Pi.mul_apply, Pi.add_apply]; ring

/-- T-action on HSumSq: invariant since H₂|T = -H₂ and H₄|T = H₃ = H₂+H₄ -/
private lemma H_sum_sq_T_action : (HSumSq ∣[(4 : ℤ)] T) = HSumSq := by
  have h_eq : HSumSq = H₂ * H₂ + H₂ * H₄ + H₄ * H₄ := by ext z; simp [HSumSq, sq]
  simp only [h_eq, show (4 : ℤ) = 2 + 2 from by norm_num,
    SlashAction.add_slash, mul_slash_SL2 2 2 T _ _, H₂_T_action, H₄_T_action, ← jacobi_identity]
  ext z; simp [Pi.mul_apply, Pi.add_apply]; ring

private lemma H_sum_sq_SL2Z_invariant :
    ∀ γ : SL(2, ℤ), HSumSq ∣[(4 : ℤ)] γ = HSumSq :=
  slashaction_generators_SL2Z HSumSq 4 H_sum_sq_S_action H_sum_sq_T_action

private lemma isBoundedAtImInfty_H_sum_sq : IsBoundedAtImInfty HSumSq := by
  have : HSumSq = H₂ * H₂ + H₂ * H₄ + H₄ * H₄ := by ext z; simp [HSumSq, sq]
  rw [this]; exact ((isBoundedAtImInfty_H₂.mul isBoundedAtImInfty_H₂).add
    (isBoundedAtImInfty_H₂.mul isBoundedAtImInfty_H₄)).add
    (isBoundedAtImInfty_H₄.mul isBoundedAtImInfty_H₄)

private noncomputable def H_sum_sq_SIF : SlashInvariantForm (Γ 1) 4 where
  toFun := HSumSq
  slash_action_eq' := slashaction_generators_GL2R HSumSq 4 H_sum_sq_S_action H_sum_sq_T_action

private noncomputable def H_sum_sq_MF : ModularForm (Γ 1) 4 := {
  H_sum_sq_SIF with
  holo' := H_sum_sq_MDifferentiable
  bdd_at_cusps' := fun hc => bounded_at_cusps_of_bounded_at_infty hc fun A ⟨A', hA⟩ => by
    rw [← hA]; simpa [SL_slash] using H_sum_sq_SL2Z_invariant A' ▸ isBoundedAtImInfty_H_sum_sq
}

/-- E₄.toFun = H₂² + H₂H₄ + H₄². Both are weight-4 level-1 modular forms tending to 1
at ∞, so their difference is a weight-4 cusp form, hence zero. -/
theorem E₄_eq_H_sum_sq : _root_.E₄.toFun = HSumSq := by
  have h_toFun : (_root_.E₄ - H_sum_sq_MF).toFun = _root_.E₄.toFun - HSumSq := by
    ext z; simp [H_sum_sq_MF, H_sum_sq_SIF]; rfl
  have h_diff_tendsto : Tendsto (_root_.E₄ - H_sum_sq_MF).toFun atImInfty (nhds 0) := by
    rw [h_toFun]
    have h := E₄_tendsto_one_atImInfty.sub H_sum_sq_tendsto
    rw [show (1 : ℂ) - 1 = 0 from by ring] at h
    exact h
  have h_cusp : IsCuspForm (Γ 1) 4 (_root_.E₄ - H_sum_sq_MF) := by
    rw [IsCuspForm_iff_coeffZero_eq_zero,
      UpperHalfPlane.qExpansion_coeff]; simp only [Nat.factorial_zero, Nat.cast_one, inv_one,
        ModularForm.coe_sub, iteratedDeriv_zero, one_mul]
    exact IsZeroAtImInfty.cuspFunction_apply_zero h_diff_tendsto (by norm_num : (0 : ℝ) < 1)
  have h_zero := IsCuspForm_weight_lt_eq_zero 4 (by norm_num) (_root_.E₄ - H_sum_sq_MF) h_cusp
  funext z
  have hz := DFunLike.congr_fun h_zero z
  have h2 : (_root_.E₄ - H_sum_sq_MF) z = _root_.E₄.toFun z - HSumSq z := congrFun h_toFun z
  rw [h2, ModularForm.zero_apply, sub_eq_zero] at hz
  exact hz

/-!
## Phase 9: Deduce f₂ = f₃ = f₄ = 0
-/

/-- Key algebraic identity for proving f₂ = f₄ = 0.
Given Af₂ + Bf₄ = 0, we have f₄² * (A² - AB + B²) = A² * (f₂² + f₂f₄ + f₄²). -/
lemma f₄_sq_mul_eq (z : ℍ) (hg_z : thetaG z = 0) :
    f₄ z ^ 2 * (3 * HSumSq z) = (2 * H₂ z + H₄ z) ^ 2 * thetaH z := by
  unfold HSumSq
  -- Define A = 2H₂ + H₄, B = H₂ + 2H₄
  set A := 2 * H₂ z + H₄ z with hA
  set B := H₂ z + 2 * H₄ z with hB
  -- From thetaG = 0: A * f₂ + B * f₄ = 0
  have h_Af₂_eq : A * f₂ z + B * f₄ z = 0 := by
    simp only [thetaG, hA, hB, smul_eq_mul, Pi.smul_apply, Pi.mul_apply, Pi.add_apply] at hg_z ⊢
    linear_combination hg_z
  -- Af₂ = -Bf₄
  have hAf₂ : A * f₂ z = -(B * f₄ z) := by linear_combination h_Af₂_eq
  -- A²f₂² = B²f₄²
  have h1 : A ^ 2 * f₂ z ^ 2 = B ^ 2 * f₄ z ^ 2 := by
    have h_sq : (A * f₂ z) ^ 2 = (B * f₄ z) ^ 2 := by rw [hAf₂]; ring
    calc A ^ 2 * f₂ z ^ 2 = (A * f₂ z) ^ 2 := by ring
      _ = (B * f₄ z) ^ 2 := h_sq
      _ = B ^ 2 * f₄ z ^ 2 := by ring
  -- A²f₂f₄ = -ABf₄²
  have h2 : A ^ 2 * (f₂ z * f₄ z) = -(A * B * f₄ z ^ 2) := by
    calc A ^ 2 * (f₂ z * f₄ z) = (A * f₂ z) * (A * f₄ z) := by ring
      _ = (-(B * f₄ z)) * (A * f₄ z) := by rw [hAf₂]
      _ = -(A * B * f₄ z ^ 2) := by ring
  -- A² - AB + B² = 3(H₂² + H₂H₄ + H₄²)
  have h_sum : A ^ 2 - A * B + B ^ 2 = 3 * (H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2) := by
    simp only [hA, hB]; ring
  -- Now compute A²θₕ
  unfold thetaH
  calc f₄ z ^ 2 * (3 * (H₂ z ^ 2 + H₂ z * H₄ z + H₄ z ^ 2))
      = f₄ z ^ 2 * (A ^ 2 - A * B + B ^ 2) := by rw [h_sum]
    _ = B ^ 2 * f₄ z ^ 2 + (-(A * B * f₄ z ^ 2)) + A ^ 2 * f₄ z ^ 2 := by ring
    _ = A ^ 2 * f₂ z ^ 2 + A ^ 2 * (f₂ z * f₄ z) + A ^ 2 * f₄ z ^ 2 := by rw [h1, h2]
    _ = A ^ 2 * (f₂ z ^ 2 + f₂ z * f₄ z + f₄ z ^ 2) := by ring

/-- From g = 0 and h = 0, deduce f₂ = 0.

Proof: From g = 0 we get a relation between f₂ and f₄. Combined with h = 0,
we show f₄² · (3 · HSumSq) = 0. Since HSumSq → 1 ≠ 0, we get f₄ = 0,
then f₂ = 0 follows from h = f₂² = 0. -/
lemma f₂_eq_zero : f₂ = 0 := by
  have hg := theta_g_eq_zero
  have hh := theta_h_eq_zero
  -- Show f₄ = 0 first, then f₂ = 0 follows from thetaH = f₂² = 0
  suffices hf₄ : f₄ = 0 by
    funext z
    have hz := congrFun hh z
    unfold thetaH at hz
    simp only [Pi.add_apply, Pi.pow_apply, Pi.mul_apply, Pi.zero_apply, hf₄] at hz
    simpa [sq_eq_zero_iff] using hz
  -- From f₄_sq_mul_eq and thetaH = 0: f₄² * (3 * HSumSq) = 0
  have h_f₄_sq_3H : f₄ ^ 2 * (fun z => 3 * HSumSq z) = 0 := by
    ext z
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.zero_apply]
    have hh_z : thetaH z = 0 := congrFun hh z
    calc f₄ z ^ 2 * (3 * HSumSq z)
        = (2 * H₂ z + H₄ z) ^ 2 * thetaH z := f₄_sq_mul_eq z (congrFun hg z)
      _ = _ := by rw [hh_z, mul_zero]
  -- f₄² is MDifferentiable
  have f₄_sq_MDiff : MDiff (f₄ ^ 2) := f₄_MDifferentiable.pow 2
  -- By mul_eq_zero_iff: f₄² = 0 (since 3 * HSumSq ≠ 0)
  have h_f₄_sq_zero : f₄ ^ 2 = 0 :=
    ((UpperHalfPlane.mul_eq_zero_iff f₄_sq_MDiff three_H_sum_sq_MDifferentiable).mp h_f₄_sq_3H
      ).resolve_right three_H_sum_sq_ne_zero
  -- From f₄² = f₄ * f₄ = 0: f₄ = 0
  exact (UpperHalfPlane.mul_eq_zero_iff f₄_MDifferentiable f₄_MDifferentiable).mp
    (pow_two f₄ ▸ h_f₄_sq_zero) |>.elim id id

/-- From f₂ = 0 and h = 0, deduce f₄ = 0 -/
lemma f₄_eq_zero : f₄ = 0 := by
  funext z; simpa [thetaH, sq_eq_zero_iff, f₂_eq_zero] using congrFun theta_h_eq_zero z

/-- From f₂ + f₄ = f₃ and both = 0, f₃ = 0 -/
lemma f₃_eq_zero : f₃ = 0 := by
  rw [← f₂_add_f₄_eq_f₃]
  simp [f₂_eq_zero, f₄_eq_zero]

/-!
## Phase 10: Main Theorems
-/

/-- Serre derivative of H₂: ∂₂H₂ = (1/6)(H₂² + 2H₂H₄) -/
theorem serre_D_H₂ :
    serreD 2 H₂ = fun z => (1/6 : ℂ) * (H₂ z ^ 2 + 2 * H₂ z * H₄ z) := by
  funext z; have := congrFun f₂_eq_zero z
  simp only [f₂, Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_eq_mul,
    Pi.zero_apply, sub_eq_zero] at this
  convert this using 1; ring

/-- Serre derivative of H₃: ∂₂H₃ = (1/6)(H₂² - H₄²) -/
theorem serre_D_H₃ : serreD 2 H₃ = fun z => (1/6 : ℂ) * (H₂ z ^ 2 - H₄ z ^ 2) := by
  funext z; have := congrFun f₃_eq_zero z
  simp only [f₃, Pi.sub_apply, Pi.smul_apply, Pi.pow_apply, smul_eq_mul, Pi.zero_apply,
    sub_eq_zero] at this
  exact this

/-- Serre derivative of H₄: ∂₂H₄ = -(1/6)(2H₂H₄ + H₄²) -/
theorem serre_D_H₄ :
    serreD 2 H₄ = fun z => -(1/6 : ℂ) * (2 * H₂ z * H₄ z + H₄ z ^ 2) := by
  funext z; have := congrFun f₄_eq_zero z
  simp only [f₄, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, Pi.zero_apply,
    add_eq_zero_iff_eq_neg] at this
  convert this using 1; ring

/-- Ordinary derivative of `H₂` in terms of `H₂`, `H₄`, and `E₂`. -/
theorem D_H₂ :
    D H₂ = (1 / 6 : ℂ) • (H₂ ^ 2 + (2 : ℂ) • (H₂ * H₄)) + (1 / 6 : ℂ) • (E₂ * H₂) := by
  ext z
  have h : D H₂ z = serreD 2 H₂ z + 2 * 12⁻¹ * E₂ z * H₂ z := by
    simp only [serre_D_apply]; ring
  rw [h, congrFun serre_D_H₂]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]; ring

/-- Ordinary derivative of `H₃` in terms of `H₂`, `H₄`, and `E₂`. -/
theorem D_H₃ :
    D H₃ = (1 / 6 : ℂ) • (H₂ ^ 2 - H₄ ^ 2) + (1 / 6 : ℂ) • (E₂ * H₃) := by
  ext z
  have h : D H₃ z = serreD 2 H₃ z + 2 * 12⁻¹ * E₂ z * H₃ z := by
    simp only [serre_D_apply]; ring
  rw [h, congrFun serre_D_H₃]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Ordinary derivative of `H₄` in terms of `H₂`, `H₄`, and `E₂`. -/
theorem D_H₄ :
    D H₄ = (-(1 / 6 : ℂ)) • ((2 : ℂ) • (H₂ * H₄) + H₄ ^ 2) +
      (1 / 6 : ℂ) • (E₂ * H₄) := by
  ext z
  have h : D H₄ z = serreD 2 H₄ z + 2 * 12⁻¹ * E₂ z * H₄ z := by
    simp only [serre_D_apply]; ring
  rw [h, congrFun serre_D_H₄]
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, smul_eq_mul]; ring
