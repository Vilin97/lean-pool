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
import LeanPool.EuclideanJordan.EuclideanJordan.Peirce


/-!
# The Peirce multiplication rules

`EuclideanJordan/Peirce.lean` decomposes `J = J₁(c) ⊕ J_{1/2}(c) ⊕ J₀(c)` for an idempotent `c`. This
file proves how the three components multiply — the Faraut–Korányi relations:

| | `J₁` | `J_{1/2}` | `J₀` |
| --- | --- | --- | --- |
| **`J₁`** | `⊆ J₁` | `⊆ J_{1/2}` | `= 0` |
| **`J_{1/2}`** | `⊆ J_{1/2}` | `⊆ J₁ ⊕ J₀` | `⊆ J_{1/2}` |
| **`J₀`** | `= 0` | `⊆ J_{1/2}` | `⊆ J₀` |

As in `EuclideanJordan/Peirce.lean`, the hypotheses are the Jordan identity and the invertibility of the
integers used (`2` for the commuting rules, `4` for the half-half rule): no spectral theorem,
no formal reality, no finite dimension, no unit.
## The two ingredients

`EuclideanJordan/Peirce.lean` needed only the *once*-linearised Jordan identity `two_lin1_raw`. Five of
the six rules follow from a single consequence of it — **`L_x` commutes with `L_c` whenever
`x` lies in `J₁(c)` or `J₀(c)`** (`mul_comm_of_eigen_one`, `mul_comm_of_eigen_zero`) — after
which each rule is one rewrite.

The sixth, `J_{1/2} ∘ J_{1/2} ⊆ J₁ ⊕ J₀`, is genuinely deeper and needs the *fully*
linearised identity `four_lin2_raw`, obtained here by polarising `two_lin1_raw` a second
time. Evaluated at the right point it collapses to `L_c² = L_c` on the product, which is
exactly "the `1/2`-component vanishes".

## Why `opCommute_eigen_one_zero` is the one to look at

The Faraut–Korányi simultaneous-diagonalisation fact — *an element scalar on `range q` and an
element of `J₂(q)` operator-commute* — is the load-bearing hypothesis in the coalescence
arguments that run over a Jordan frame. Its single-idempotent case is
`opCommute_eigen_one_zero` below, and it is three lines from `four_lin2_raw`.

★ **That is a case, not the frame-level statement.** The frame-level version quantifies over a
rank-two `q = pᵢ + pⱼ` drawn from a Jordan frame, and this file has no frame.
`EuclideanJordan/Frame.lean` puts it in frame shape (`opCommute_scalarOn_frame`) once
orthogonal idempotent families are available, and `EuclideanJordan/Block.lean` supplies the
projection commutation (`peirceOne_comm_peirceOne` and siblings) and the exact
characterisation of the rank-two block.

## References

* Faraut and Korányi, *Analysis on Symmetric Cones*, Prop. IV.1.1 and Lemma IV.1.3.
* McCrimmon, *A Taste of Jordan Algebras*, §II.8.
-/

namespace EuclideanJordan

local notation "L" => AddMonoid.End.mulLeft

/-! Applying an `AddMonoid.End` expression to an element is definitional in every constructor
we use, but Mathlib's corresponding lemmas are phrased for the `AddMonoidHom` coercion and do not
match the `AddMonoid.End` one.  Lean 4.28's simp set bridged this on its own; 4.30's does not, so
the four `rfl`s are stated here and passed to `simpa` explicitly. -/

private theorem L_apply {J : Type*} [NonUnitalNonAssocSemiring J] (a w : J) :
    (AddMonoid.End.mulLeft a) w = a * w := rfl

private theorem End_add_apply {J : Type*} [NonUnitalNonAssocCommRing J]
    (f g : AddMonoid.End J) (w : J) : (f + g) w = f w + g w := rfl

private theorem End_mul_apply {J : Type*} [NonUnitalNonAssocCommRing J]
    (f g : AddMonoid.End J) (w : J) : (f * g) w = f (g w) := rfl

private theorem End_neg_apply {J : Type*} [NonUnitalNonAssocCommRing J]
    (f : AddMonoid.End J) (w : J) : (-f) w = -(f w) := rfl

section Lin2

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J]

/-- **Four times the fully linearised Jordan identity.** Polarising `two_lin1_raw` a second
time, in `a := p + q`, and subtracting the two pure terms leaves the cyclic sum

  `⁅L_b, L_{pq}⁆ + ⁅L_p, L_{qb}⁆ + ⁅L_q, L_{pb}⁆ = 0`,

which is the identity every Peirce multiplication rule beyond the commuting ones needs.
The factor `4` is carried rather than cancelled so that this holds with no torsion
hypothesis. -/
theorem four_lin2_raw (p q b : J) :
    (4 : ℕ) • (⁅L b, L (p * q)⁆ + ⁅L p, L (q * b)⁆ + ⁅L q, L (p * b)⁆) = 0 := by
  -- Same instance gap as in `two_lin1_raw`: `LieRing.ofAssociativeRing` is a `local instance`
  -- of its own Mathlib file, so a ring's commutator carries `Ring.instBracket` but no `LieRing`,
  -- and `lie_add`/`add_lie` cannot fire on `AddMonoid.End J`.  Reinstating it inside the proof —
  -- never at section scope, which would elaborate this theorem's own `⁅·,·⁆` against a different
  -- instance — is what makes the `simp only` below distribute the bracket.
  let _ : LieRing (AddMonoid.End J) := LieRing.ofAssociativeRing
  have h1 := two_lin1_raw (p + q) b
  have hp := two_lin1_raw p b
  have hq := two_lin1_raw q b
  simp only [add_mul, mul_add, map_add, lie_add, add_lie, mul_comm q p] at h1
  have hpq : (2 : ℕ) • ⁅L b, L (p * p)⁆ + (4 : ℕ) • ⁅L p, L (p * b)⁆
      + ((2 : ℕ) • ⁅L b, L (q * q)⁆ + (4 : ℕ) • ⁅L q, L (q * b)⁆) = 0 := by
    rw [hp, hq, add_zero]
  have h := sub_eq_zero_of_eq (h1.trans hpq.symm)
  rw [← h]
  abel

/-- `four_lin2_raw` evaluated at an element. -/
theorem four_lin2_apply (p q b w : J) :
    (4 : ℕ) • (b * (p * q * w) - p * q * (b * w)
      + (p * (q * b * w) - q * b * (p * w))
      + (q * (p * b * w) - p * b * (q * w))) = 0 := by
  have h := congrArg (fun f : AddMonoid.End J => f w) (four_lin2_raw p q b)
  simpa [Ring.lie_def, sub_eq_add_neg, L_apply, End_add_apply, End_mul_apply,
    End_neg_apply] using h

end Lin2

section Commuting

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]

omit [IsCommJordan J] in
/-- Cancel a nonzero natural multiple in a real vector space. -/
theorem nsmul_eq_zero_iff' {n : ℕ} (hn : n ≠ 0) {x : J} (h : n • x = 0) : x = 0 := by
  have h2 : (n : ℝ) • x = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact h
  rcases smul_eq_zero.mp h2 with h' | h'
  · exact absurd (Nat.cast_eq_zero.mp h') hn
  · exact h'

/-- **`L_x` commutes with `L_c` when `c ∘ x = x`.** The `1`-eigenvectors of `L_c` are
operator-compatible with `c`. Five of the six multiplication rules come from this and its
`0`-eigenvalue twin. -/
theorem mul_comm_of_eigen_one {c x : J} (hc : c * c = c) (hx : c * x = x) (w : J) :
    c * (x * w) = x * (c * w) := by
  have h := two_lin1_apply c x w
  simp only [hc, hx] at h
  refine sub_eq_zero.mp (nsmul_eq_zero_iff' (n := 2) (by norm_num) ?_)
  rw [← h]
  abel

/-- **`L_x` commutes with `L_c` when `c ∘ x = 0`.** -/
theorem mul_comm_of_eigen_zero {c x : J} (hc : c * c = c) (hx : c * x = 0) (w : J) :
    c * (x * w) = x * (c * w) := by
  have h := two_lin1_apply c x w
  simp only [hc, hx, zero_mul, mul_zero, sub_self] at h
  refine (sub_eq_zero.mp (nsmul_eq_zero_iff' (n := 2) (by norm_num) ?_)).symm
  rw [← h]
  abel

/-- **`J₁(c) ∘ J₁(c) ⊆ J₁(c)`.** -/
theorem eigen_one_mul_one {c x y : J} (hc : c * c = c) (hx : c * x = x) (hy : c * y = y) :
    c * (x * y) = x * y := by
  rw [mul_comm_of_eigen_one hc hx y, hy]

/-- **`J₀(c) ∘ J₀(c) ⊆ J₀(c)`.** -/
theorem eigen_zero_mul_zero {c x y : J} (hc : c * c = c) (hx : c * x = 0) (hy : c * y = 0) :
    c * (x * y) = 0 := by
  rw [mul_comm_of_eigen_zero hc hx y, hy, mul_zero]

/-- **`J₁(c) ∘ J₀(c) = 0`** — the two extreme Peirce components annihilate each other, and
not merely land in a common component.

The proof reads the same product twice: `L_c` fixes it because `x ∈ J₁`, and `L_c` kills it
because `y ∈ J₀`. -/
theorem eigen_one_mul_zero {c x y : J} (hc : c * c = c) (hx : c * x = x) (hy : c * y = 0) :
    x * y = 0 := by
  have h1 : c * (x * y) = 0 := by rw [mul_comm_of_eigen_one hc hx y, hy, mul_zero]
  have h2 : c * (x * y) = x * y := by
    rw [mul_comm x y, mul_comm_of_eigen_zero hc hy x, hx, mul_comm]
  rw [← h2, h1]

/-- **The single-idempotent case of Faraut–Korányi simultaneous diagonalisation.**

An element of `J₁(c)` and an element of `J₀(c)` **operator**-commute: `L_x L_y = L_y L_x`,
which is strictly more than the product `x ∘ y` vanishing. It falls straight out of the
cyclic identity, because two of its three brackets vanish.

★ This is the *case* `q = c`, not the field: the field ranges over a rank-two `q = pᵢ + pⱼ`
inside a Jordan frame, and there is no frame in this file. -/
theorem opCommute_eigen_one_zero {c x y : J} (hc : c * c = c) (hx : c * x = x)
    (hy : c * y = 0) (w : J) : x * (y * w) = y * (x * w) := by
  have hxy : x * y = 0 := eigen_one_mul_zero hc hx hy
  have h := four_lin2_apply x y c w
  rw [hxy] at h
  simp only [mul_comm y c, mul_comm x c, hx, hy, zero_mul, mul_zero,
    sub_self, zero_add, add_zero] at h
  refine (sub_eq_zero.mp (nsmul_eq_zero_iff' (n := 4) (by norm_num) ?_)).symm
  rw [← h]

end Commuting

section HalfRules

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J]

/-- **`J₁(c) ∘ J_{1/2}(c) ⊆ J_{1/2}(c)`.** -/
theorem eigen_one_mul_half {c x y : J} (hc : c * c = c) (hx : c * x = x)
    (hy : c * y = (2 : ℝ)⁻¹ • y) : c * (x * y) = (2 : ℝ)⁻¹ • (x * y) := by
  rw [mul_comm_of_eigen_one hc hx y, hy, mul_smul_comm']

/-- **`J₀(c) ∘ J_{1/2}(c) ⊆ J_{1/2}(c)`.** -/
theorem eigen_zero_mul_half {c x y : J} (hc : c * c = c) (hx : c * x = 0)
    (hy : c * y = (2 : ℝ)⁻¹ • y) : c * (x * y) = (2 : ℝ)⁻¹ • (x * y) := by
  rw [mul_comm_of_eigen_zero hc hx y, hy, mul_smul_comm']

/-- **`J_{1/2}(c) ∘ J_{1/2}(c) ⊆ J₁(c) ⊕ J₀(c)`**, stated as the polynomial relation
`L_c² = L_c` on the product — which is exactly "no `1/2`-component", since
`peirceHalf c z = 4•(c ∘ z) − 4•(c ∘ (c ∘ z))` collapses to `0` under it (`peirceHalf_mul_half_eq_zero`).
★ An earlier draft attributed this to the eigenvalue trichotomy. It does not use the
trichotomy — it is the projection formula directly.

This is the one rule that needs the fully linearised identity: evaluating `four_lin2_raw`
at `(c, y, x)` and argument `c`, the four `1/4`-terms cancel in pairs and what survives is
`L_c²(xy) − L_c(xy) = 0`. -/
theorem eigen_half_mul_half {c x y : J} (hc : c * c = c) (hx : c * x = (2 : ℝ)⁻¹ • x)
    (hy : c * y = (2 : ℝ)⁻¹ • y) : c * (c * (x * y)) = c * (x * y) := by
  have h := four_lin2_apply c y x c
  simp only [hc, hx, hy, smul_mul_assoc, mul_smul_comm', smul_smul,
    mul_comm y c, mul_comm x c, mul_comm (x * y) c, mul_comm y x] at h
  refine sub_eq_zero.mp (nsmul_eq_zero_iff' (n := 4) (by norm_num) ?_)
  rw [← h]
  abel

/-- The `1/2`-component of a product of two `1/2`-elements vanishes — `eigen_half_mul_half`
read through the projection of `EuclideanJordan/Peirce.lean`. -/
theorem peirceHalf_mul_half_eq_zero {c x y : J} (hc : c * c = c)
    (hx : c * x = (2 : ℝ)⁻¹ • x) (hy : c * y = (2 : ℝ)⁻¹ • y) :
    peirceHalf c (x * y) = 0 := by
  rw [peirceHalf_apply, eigen_half_mul_half hc hx hy, sub_self]

end HalfRules

end EuclideanJordan
