/-
Copyright (c) 2026 Aditya Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aditya Rao
-/

module
public import LeanPool.KrohnRhodes.Foundations.WreathProduct
public import Mathlib.GroupTheory.RegularWreathProduct

/-! # Monoid wreath bridge

Bridges Mathlib's group-theoretic `RegularWreathProduct D Q` to the semigroup-theoretic
`WreathProduct A B X` of `WreathProduct.lean`.

Mathlib's regular wreath product uses the multiplication
`(a * b).left x = a.left x * b.left (a.right⁻¹ * x)`,
while `WreathProduct` uses
`(p * q).func x = p.func (q.base • x) * q.func x`.

When `Q` acts on itself by left multiplication (`Monoid.toMulAction`),
these two conventions are conjugate via the substitution `f ↦ (x ↦ f (q * x))`,
so we obtain an injective monoid homomorphism `D ≀ᵣ Q →* WreathProduct D Q Q`.

## Main results

- `regularWreathToMonoidWreath` : the bridge, a monoid homomorphism.
- `regularWreathToMonoidWreath_injective` : injectivity of the bridge.
-/

public section

namespace LeanPool.KrohnRhodes

universe u

variable (D Q : Type u) [Group D] [Group Q]

/-- The bridge function on underlying data: send `(a, q) ∈ D ≀ᵣ Q` to the
`WreathProduct` element with decoration `x ↦ a (q * x)` and base `q`.

This change of variable is needed because Mathlib's regular wreath uses
`b.left (a.right⁻¹ * x)` in multiplication while `WreathProduct` uses
`p.func (q.base • x)`; they match precisely after this substitution. -/
def regularWreathToMonoidWreathFun (a : D ≀ᵣ Q) :
    WreathProduct D Q Q :=
  ⟨fun x => a.left (a.right * x), a.right⟩

/-- Bridge: a group regular wreath product `D ≀ᵣ Q` embeds as a monoid into
`WreathProduct D Q Q`, where `Q` acts on itself by left
multiplication. -/
def regularWreathToMonoidWreath :
    (D ≀ᵣ Q) →* WreathProduct D Q Q where
  toFun := regularWreathToMonoidWreathFun D Q
  map_one' := by
    -- φ(1) has decoration `x ↦ 1.left (1.right * x) = 1` and base `1.right = 1`.
    ext x
    · simp [regularWreathToMonoidWreathFun]
    · simp [regularWreathToMonoidWreathFun]
  map_mul' a b := by
    -- We have to verify
    --   φ(a*b).func x = (φ a * φ b).func x
    --   φ(a*b).base   = (φ a * φ b).base
    -- LHS func: (a*b).left ((a*b).right * x)
    --         = a.left ((a*b).right * x) * b.left (a.right⁻¹ * (a*b).right * x)
    --         = a.left (a.right * b.right * x) * b.left (b.right * x)
    -- RHS func: φ(a).func (φ(b).base • x) * φ(b).func x
    --         = a.left (a.right * (b.right * x)) * b.left (b.right * x)
    -- These agree by associativity.
    ext x
    · -- decoration component
      change (a * b).left ((a * b).right * x)
        = a.left (a.right * (b.right * x)) * b.left (b.right * x)
      simp [RegularWreathProduct.mul_def, mul_assoc]
    · -- base component
      change (a * b).right = a.right * b.right
      rfl

/-- The bridge is injective. -/
theorem regularWreathToMonoidWreath_injective :
    Function.Injective (regularWreathToMonoidWreath D Q) := by
  intro a b hab
  -- From `φ a = φ b` we read off `a.right = b.right` and
  -- `∀ x, a.left (a.right * x) = b.left (b.right * x)`.
  have hbase : a.right = b.right :=
    congrArg WreathProduct.base hab
  have hfunc : ∀ x, a.left (a.right * x) = b.left (b.right * x) := by
    intro x
    have := congrArg (fun w : WreathProduct D Q Q => w.func x) hab
    simpa [regularWreathToMonoidWreath, regularWreathToMonoidWreathFun] using this
  -- Recover equality of `a.left` and `b.left` by substituting `x = a.right⁻¹ * y`.
  have hleft : a.left = b.left := by
    funext y
    have h := hfunc (a.right⁻¹ * y)
    have hcancel : a.right * (a.right⁻¹ * y) = y := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    rw [hcancel] at h
    have hb : b.right * (a.right⁻¹ * y) = y := by
      rw [hbase, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [hb] at h
    exact h
  -- Conclude with the structure extensionality lemma.
  exact RegularWreathProduct.ext hleft hbase

end LeanPool.KrohnRhodes
