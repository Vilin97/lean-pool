/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license.
Authors: Bryan Ehrlich
-/
import LeanPool.EuclideanJordan.EuclideanJordan.Pattern


/-!
# Unbundled Jordan algebras: the multiplication as a bilinear map

The rest of this library runs on the **typeclasses** `[NonUnitalNonAssocCommRing J]
[IsCommJordan J] [Module ℝ J]`. A caller who instead holds the Jordan product as a **bundled
bilinear map** `m : J →ₗ[ℝ] J →ₗ[ℝ] J` over `[NormedAddCommGroup J] [Module ℝ J]` cannot simply
assume both: that gives two different `AddCommGroup J` instances, `Module ℝ J` then fails to
synthesise at the use site, and the result is a textbook Mathlib diamond.

**This file dodges it.** `ringOfBilinear` builds the multiplicative structure *on the ambient
additive group* — `{ (inferInstance : AddCommGroup J) with mul := fun x y => m x y, … }` — so
only one `AddCommGroup` is ever in play. Nothing is assumed twice.

## What that buys

Two sample transfers are given, both stated with `m` alone:

* `peirce_poly_bilinear` — the Peirce polynomial identity `2 c(c(c y)) + c y = 3 c(c y)` for an
  idempotent `c`;
* `opCommute_scalarOn_bilinear` — the Jordan multiplication operators `L_a` and `L_b` commute,
  for `a` scalar on `range c` and `b` in the `1`-eigenspace of `L_c`. This is the load-bearing
  Faraut–Korányi operator-commutation hypothesis.

`EuclideanJordan/Spectral.lean` and `EuclideanJordan/Order.lean` use the same device at scale:
`spectral_resolution_bilinear` and `orderUnitSpaceOfBilinear` are stated over `m` and proved by
installing `ringOfBilinear` locally.

★ **The device has a hard limit.** Only results whose *statements* are expressible with `m`
alone cross over; anything whose statement needs the ring instance — `jpow`, and so Albert's
power-associativity theorem — cannot be bridged this way, because the instance would have to
exist before the statement elaborates.
-/
namespace EuclideanJordan

section Bridge

variable {J : Type*} [NormedAddCommGroup J] [Module ℝ J]

/-- Build the multiplicative structure ON the ambient additive group, from a bilinear map. -/
@[instance_reducible]
def ringOfBilinear (m : J →ₗ[ℝ] J →ₗ[ℝ] J) (hcomm : ∀ x y, m x y = m y x) :
    NonUnitalNonAssocCommRing J :=
  { (inferInstance : AddCommGroup J) with
    mul := fun x y => m x y
    left_distrib := fun a b c => (m a).map_add b c
    right_distrib := fun a b c => by
      show m (a + b) c = m a c + m b c
      rw [map_add]; rfl
    zero_mul := fun a => by
      show m 0 a = 0
      rw [map_zero]; rfl
    mul_zero := fun a => (m a).map_zero
    mul_comm := hcomm }


variable (m : J →ₗ[ℝ] J →ₗ[ℝ] J)

/-- `m` is linear in its first argument — the scalar-tower law for the constructed ring. -/
theorem smul_bilinear (r : ℝ) (a b : J) : m (r • a) b = r • m a b := by
  rw [map_smul]; rfl

/-- **The Peirce polynomial identity, in bilinear-map vocabulary.** -/
theorem peirce_poly_bilinear (hcomm : ∀ x y : J, m x y = m y x)
    (hjordan : ∀ a b : J, m (m a b) (m a a) = m a (m b (m a a)))
    {c : J} (hc : m c c = c) (y : J) :
    (2 : ℕ) • m c (m c (m c y)) + m c y = (3 : ℕ) • m c (m c y) := by
  letI : NonUnitalNonAssocCommRing J := ringOfBilinear m hcomm
  letI : IsCommJordan J := ⟨hjordan⟩
  exact peirce_poly hc y

/-- **Operator commutation in bilinear-map vocabulary**: `L_a` and `L_b` commute at `w`, for
`a` scalar on `range c` and `b` in the `1`-eigenspace of `L_c`. -/
theorem opCommute_scalarOn_bilinear (hcomm : ∀ x y : J, m x y = m y x)
    (hjordan : ∀ a b : J, m (m a b) (m a a) = m a (m b (m a a)))
    {c a a₀ b : J} {mu : ℝ} (hc : m c c = c) (ha : a = mu • c + a₀)
    (ha₀ : m c a₀ = 0) (hb : m c b = b) (w : J) :
    m a (m b w) = m b (m a w) := by
  letI : NonUnitalNonAssocCommRing J := ringOfBilinear m hcomm
  letI : IsCommJordan J := ⟨hjordan⟩
  letI : IsScalarTower ℝ J J := ⟨fun r x y => smul_bilinear m r x y⟩
  exact opCommute_scalarOn hc ha ha₀ hb w

end Bridge

end EuclideanJordan
