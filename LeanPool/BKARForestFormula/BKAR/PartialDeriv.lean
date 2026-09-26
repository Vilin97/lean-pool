/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import LeanPool.BKARForestFormula.BKAR.Interpolation

/-! # Coordinate partial derivatives on the edge-coupling space

First-order calculus for functions `ρ : (Edge V → ℝ) → ℝ` of the
edge-coupling variables.  Defines the coordinate update `updateCoord`, the
coordinate basis directions `edgeBasis`, the single-coordinate partial
derivative `partialDeriv`, iterated mixed partials along a list of edges
(`mixedPartialList`), and the unordered forest mixed partial `mixedPartial`
appearing in the integrand of the BKAR forest interpolation formula (see
`BKAR.Formula`).
-/

@[expose] public section

namespace BKAR

variable {V : Type*} [DecidableEq V]

/-- Replace one BKAR edge coordinate in a parameter vector. -/
def updateCoord (x : Edge V → ℝ) (e : Edge V) (t : ℝ) : Edge V → ℝ :=
  Function.update x e t

@[simp]
theorem updateCoord_self (x : Edge V → ℝ) (e : Edge V) (t : ℝ) :
    updateCoord x e t e = t := by
  rw [updateCoord]
  exact Function.update_self e t x

theorem updateCoord_of_ne (x : Edge V → ℝ) {e e' : Edge V} (t : ℝ)
    (hne : e' ≠ e) :
    updateCoord x e t e' = x e' := by
  rw [updateCoord]
  exact Function.update_of_ne hne t x

@[simp]
theorem updateCoord_same_value (x : Edge V → ℝ) (e : Edge V) :
    updateCoord x e (x e) = x := by
  rw [updateCoord]
  exact Function.update_eq_self e x

@[simp]
theorem updateCoord_update_same (x : Edge V → ℝ) (e : Edge V)
    (s t : ℝ) :
    updateCoord (updateCoord x e s) e t = updateCoord x e t := by
  rw [updateCoord, updateCoord]
  exact Function.update_idem s t x

/-- The coordinate basis vector for an edge. -/
def edgeBasis (e : Edge V) : Edge V → ℝ :=
  Pi.single e (1 : ℝ)

@[simp]
theorem edgeBasis_self (e : Edge V) :
    edgeBasis e e = 1 := by
  simp [edgeBasis]

theorem edgeBasis_of_ne {e e' : Edge V} (hne : e' ≠ e) :
    edgeBasis e e' = 0 := by
  simpa [edgeBasis] using
    Pi.single_eq_of_ne (M := fun _ : Edge V => ℝ) hne (1 : ℝ)

/-- Partial derivative of `ρ` along one edge coordinate. -/
noncomputable def partialDeriv (e : Edge V)
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) : ℝ :=
  deriv (fun t : ℝ => ρ (updateCoord x e t)) (x e)

theorem partialDeriv_eq_deriv (e : Edge V)
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) :
    partialDeriv e ρ x =
      deriv (fun t : ℝ => ρ (updateCoord x e t)) (x e) :=
  rfl

theorem partialDeriv_updateCoord_self (e : Edge V)
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) (s : ℝ) :
    partialDeriv e ρ (updateCoord x e s) =
      deriv (fun t : ℝ => ρ (updateCoord x e t)) s := by
  rw [partialDeriv, updateCoord_self]
  apply congrArg (fun f : ℝ → ℝ => deriv f s)
  funext t
  rw [updateCoord_update_same]

theorem partialDeriv_of_hasFDerivAt [Finite V] (e : Edge V)
    {ρ : (Edge V → ℝ) → ℝ} {x : Edge V → ℝ}
    {ρ' : (Edge V → ℝ) →L[ℝ] ℝ}
    (hρ : HasFDerivAt ρ ρ' x) :
    partialDeriv e ρ x = ρ' (edgeBasis e) := by
  classical
  let := Fintype.ofFinite V
  have hupdate :
      HasDerivAt (updateCoord x e) (edgeBasis e) (x e) := by
    simpa [updateCoord] using! hasDerivAt_update (𝕜 := ℝ) x e (x e)
  have hcomp :
      HasDerivAt (ρ ∘ updateCoord x e)
        (ρ' (edgeBasis e)) (x e) :=
    hρ.comp_hasDerivAt_of_eq (x e) hupdate
      (updateCoord_same_value x e).symm
  rw [partialDeriv]
  exact hcomp.deriv

/-- Iterated mixed partial derivative along a list of edge coordinates. -/
noncomputable def mixedPartialList :
    List (Edge V) → ((Edge V → ℝ) → ℝ) → (Edge V → ℝ) → ℝ
  | [], ρ => ρ
  | e :: es, ρ => partialDeriv e (mixedPartialList es ρ)

@[simp]
theorem mixedPartialList_nil (ρ : (Edge V → ℝ) → ℝ) :
    mixedPartialList ([] : List (Edge V)) ρ = ρ :=
  rfl

@[simp]
theorem mixedPartialList_nil_apply (ρ : (Edge V → ℝ) → ℝ)
    (x : Edge V → ℝ) :
    mixedPartialList ([] : List (Edge V)) ρ x = ρ x :=
  rfl

@[simp]
theorem mixedPartialList_cons (e : Edge V) (es : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    mixedPartialList (e :: es) ρ = partialDeriv e (mixedPartialList es ρ) :=
  rfl

@[simp]
theorem mixedPartialList_cons_apply (e : Edge V) (es : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) :
    mixedPartialList (e :: es) ρ x =
      partialDeriv e (mixedPartialList es ρ) x :=
  rfl

theorem mixedPartialList_append (es₁ es₂ : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    mixedPartialList (es₁ ++ es₂) ρ =
      mixedPartialList es₁ (mixedPartialList es₂ ρ) := by
  induction es₁ with
  | nil =>
      rfl
  | cons e es ih =>
      change partialDeriv e (mixedPartialList (es ++ es₂) ρ) =
        partialDeriv e (mixedPartialList es (mixedPartialList es₂ ρ))
      rw [ih]

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (F : Forest V)

/-- The mixed partial derivative indexed by the edge set of a forest. -/
noncomputable def mixedPartial (ρ : (Edge V → ℝ) → ℝ) :
    (Edge V → ℝ) → ℝ :=
  mixedPartialList F.edges.toList ρ

theorem mixedPartial_def (ρ : (Edge V → ℝ) → ℝ) :
    F.mixedPartial ρ = mixedPartialList F.edges.toList ρ :=
  rfl

theorem mixedPartial_empty_edges (hF : F.edges = ∅)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.mixedPartial ρ = ρ := by
  rw [mixedPartial, hF]
  rw [Finset.toList_empty]
  rfl

theorem mixedPartial_empty_edges_apply (hF : F.edges = ∅)
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) :
    F.mixedPartial ρ x = ρ x := by
  rw [F.mixedPartial_empty_edges hF ρ]

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
