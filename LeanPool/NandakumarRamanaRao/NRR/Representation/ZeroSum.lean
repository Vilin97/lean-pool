/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Tactic
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# `NRR.Representation.ZeroSum` — zero-sum real-valued target type (public API)

The zero-sum real-valued target type used by the perimeter test map. A value of
`ZeroSum n` is a function `Fin n → ℝ` whose coordinates sum to zero. It carries the
subtype topology inherited from `Fin n → ℝ`, a `CoeFun` to the underlying function, an
extensionality lemma, and a `Zero` instance (needed so that later theorems can state that
the test map vanishes, e.g. `TestMap.perimeter ... s = 0`).

This module keeps `ZeroSum` minimal: it does *not* introduce representation spheres,
obstruction theory, or quotient spaces, and it does not make `AddCommGroup`/`Module`
structure mandatory.
-/

@[expose] public section

namespace NRR

variable {n : ℕ}

/-- **Zero-sum real-valued target type.** A function `Fin n → ℝ` whose coordinates sum to
zero. -/
def ZeroSum (n : ℕ) : Type :=
  {v : Fin n → ℝ // ∑ i, v i = 0}

/-- The subtype topology inherited from `Fin n → ℝ`. -/
instance : TopologicalSpace (ZeroSum n) :=
  instTopologicalSpaceSubtype

/-- The inherited topology is Hausdorff. -/
instance : T2Space (ZeroSum n) :=
  inferInstanceAs (T2Space {v : Fin n → ℝ // ∑ i, v i = 0})

/-- Coercion of a zero-sum vector to its underlying function `Fin n → ℝ`. -/
instance : CoeFun (ZeroSum n) (fun _ => Fin n → ℝ) where
  coe v := v.val

@[simp] theorem ZeroSum.sum_coe (v : ZeroSum n) :
    ∑ i, v i = 0 :=
  v.property

theorem ZeroSum.ext {v w : ZeroSum n} (h : ∀ i, v i = w i) : v = w :=
  Subtype.ext (funext h)

/-- The zero vector of `ZeroSum n`. -/
instance : Zero (ZeroSum n) :=
  ⟨⟨0, by simp⟩⟩

@[simp] theorem ZeroSum.zero_apply (i : Fin n) :
    (0 : ZeroSum n) i = 0 :=
  rfl

/-- Constructor for `ZeroSum n` from a function and a proof its coordinates sum to zero. -/
def ZeroSum.mk' (v : Fin n → ℝ) (hv : ∑ i, v i = 0) : ZeroSum n :=
  ⟨v, hv⟩

/-- **Relabelling of a zero-sum vector.** For a permutation `σ : Equiv.Perm (Fin n)` and a
zero-sum vector `v : ZeroSum n`, the relabelled vector `ZeroSum.relabel σ v` is obtained by
precomposing the underlying function with `σ.symm`, i.e.
`(ZeroSum.relabel σ v) i = v (σ.symm i)`. This `σ.symm` convention matches `Config.relabel`. -/
def ZeroSum.relabel (σ : Equiv.Perm (Fin n)) (v : ZeroSum n) : ZeroSum n :=
  { val := fun i => v (σ.symm i)
    property := by
      simpa using σ.symm.sum_comp (fun i => v i) }

@[simp] theorem ZeroSum.relabel_apply (σ : Equiv.Perm (Fin n)) (v : ZeroSum n) (i : Fin n) :
    ZeroSum.relabel σ v i = v (σ.symm i) := rfl

@[simp] theorem ZeroSum.relabel_one (v : ZeroSum n) :
    ZeroSum.relabel 1 v = v := by
  apply ZeroSum.ext
  intro i
  rfl

theorem ZeroSum.relabel_mul (σ τ : Equiv.Perm (Fin n)) (v : ZeroSum n) :
    ZeroSum.relabel (σ * τ) v =
      ZeroSum.relabel σ (ZeroSum.relabel τ v) := by
  apply ZeroSum.ext
  intro i
  simp [ZeroSum.relabel_apply]
  rfl

/-- The `Sₙ`-action `σ • v := ZeroSum.relabel σ v` on the zero-sum target type, by relabelling
via precomposition with `σ.symm` (matching the `Config` action convention). -/
instance : MulAction (Equiv.Perm (Fin n)) (ZeroSum n) where
  smul σ v := ZeroSum.relabel σ v
  one_smul v := ZeroSum.relabel_one v
  mul_smul σ τ v := ZeroSum.relabel_mul σ τ v

@[simp] theorem ZeroSum.smul_def (σ : Equiv.Perm (Fin n)) (v : ZeroSum n) :
    σ • v = ZeroSum.relabel σ v := rfl

/-- Relabelling is continuous for the subtype topology on `ZeroSum n`. -/
theorem ZeroSum.continuous_relabel (σ : Equiv.Perm (Fin n)) :
    Continuous fun v : ZeroSum n => ZeroSum.relabel σ v := by
  refine continuous_induced_rng.2 ?_
  refine continuous_pi fun i => ?_
  exact (continuous_apply (σ.symm i)).comp continuous_induced_dom

end NRR
