/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ParabolicHolder
public import Mathlib.Analysis.MeanInequalities

/-!
# Parabolic Hölder AM–GM (Young) interpolation (roadmap point 4, Item 3)

`AnalyticPDE/ParabolicHolder.lean` proves the multiplicative interpolation inequality
`parabolicHolderWith_interpolation`:

  `[u]_{α θ} ≤ (2 · sup)^{1 − θ} · [u]_α^θ`.

This module refines that multiplicative bound into the **additive (Young / weighted arithmetic–
geometric mean) form** that parabolic Schauder estimates use to *absorb lower-order terms*.  Applying
the weighted AM–GM inequality `p₁^{w₁} · p₂^{w₂} ≤ w₁ p₁ + w₂ p₂` (with weights `w₁ = 1 − θ`,
`w₂ = θ`) to the two interpolation factors turns the product into a convex combination:

  `[u]_{α θ} ≤ (1 − θ) · (2 · sup) + θ · [u]_α`,

and — genuinely load-bearing for the fixed point — with a free scaling parameter `κ > 0`, the
*absorbing* form

  `[u]_{α θ} ≤ (1 − θ) · κ^{−θ/(1−θ)} · (2 · sup) + θ κ · [u]_α`,

whose coefficient `θ κ` on the top seminorm `[u]_α` can be made arbitrarily small at the cost of a
large multiple of the sup norm — exactly the mechanism that lets an intermediate parabolic Hölder
seminorm be swallowed by a small fraction of the leading seminorm plus a controlled `C^0` remainder.

This is a leaf module (nothing in the project imports it yet): the only heavy dependency is
`Mathlib.Analysis.MeanInequalities`, kept out of the widely-imported `ParabolicHolder` file so that
adding it does not trigger a rebuild of the downstream parabolic function-space tower.

* `parabolicHolderWith_interpolation_add` / `_le` — the additive and uniform (`≤ 2·sup + [u]_α`)
  interpolation constants at the `ParabolicHolderWith` level.
* `parabolicHolderSeminorm_interpolation_add_le` — the additive interpolation at the seminorm-
  functional level.
* `parabolicHolderWith_interpolation_absorb` / `parabolicHolderSeminorm_interpolation_absorb_le` —
  the `κ`-scaled *absorbing* form and its seminorm functional.

All proofs are pure norm/rpow/AM–GM algebra; no Schauder or heat-kernel content.  Axiom-clean
(`propext` / `Classical.choice` / `Quot.sound`).
-/

@[expose] public section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE
variable {X E : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E]

/-- **Scalar weighted-AM–GM absorbing inequality.**  For nonnegative `a, b`, weight `0 ≤ θ < 1`, and
a free scaling parameter `κ > 0`,
`a^{1−θ} · b^θ ≤ (1 − θ) · κ^{−θ/(1−θ)} · a + θ · κ · b`.
Obtained from the weighted AM–GM inequality applied to the rescaled values
`p₁ = κ^{−θ/(1−θ)} · a` and `p₂ = κ · b` (weights `1 − θ`, `θ`), whose weighted geometric mean is
exactly `a^{1−θ} b^θ`.  The `θ κ` coefficient on `b` is the tunable one. -/
theorem rpow_mul_rpow_le_absorb {a b θ κ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hκ : 0 < κ) :
    a ^ (1 - θ) * b ^ θ ≤ (1 - θ) * (κ ^ (-(θ / (1 - θ))) * a) + θ * (κ * b) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hp1nn : 0 ≤ κ ^ (-(θ / (1 - θ))) * a := mul_nonneg (Real.rpow_nonneg hκ.le _) ha
  have hp2nn : 0 ≤ κ * b := mul_nonneg hκ.le hb
  have hkey : (κ ^ (-(θ / (1 - θ))) * a) ^ (1 - θ) * (κ * b) ^ θ = a ^ (1 - θ) * b ^ θ := by
    rw [Real.mul_rpow (Real.rpow_nonneg hκ.le _) ha, Real.mul_rpow hκ.le hb,
      ← Real.rpow_mul hκ.le]
    have he : (-(θ / (1 - θ))) * (1 - θ) = -θ := by
      field_simp
    rw [he,
      show κ ^ (-θ) * a ^ (1 - θ) * (κ ^ θ * b ^ θ)
          = κ ^ (-θ) * κ ^ θ * (a ^ (1 - θ) * b ^ θ) by ring,
      ← Real.rpow_add hκ, show (-θ) + θ = (0 : ℝ) by ring, Real.rpow_zero, one_mul]
  have hAMGM := Real.geom_mean_le_arith_mean2_weighted (by linarith : (0 : ℝ) ≤ 1 - θ)
    hθ0 hp1nn hp2nn (by ring : (1 - θ) + θ = 1)
  rw [hkey] at hAMGM
  exact hAMGM

/-- **Parabolic Hölder interpolation, additive (Young) form.**  A parabolically bounded (`B`) and
`α`-Hölder (`H`) function is, for every weight `0 ≤ θ ≤ 1`, parabolic Hölder with the intermediate
exponent `α · θ` and the *convex-combination* constant `(1 − θ) · (2 · B) + θ · H`.  The additive
form of `parabolicHolderWith_interpolation`, obtained by dominating the multiplicative constant
`(2B)^{1−θ} H^θ` through the weighted AM–GM inequality. -/
theorem parabolicHolderWith_interpolation_add
    {B H α θ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hB0 : 0 ≤ B) (hH0 : 0 ≤ H) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hbdd : ParabolicBoundedWith B u s)
    (hhol : ParabolicHolderWith H α u s) :
    ParabolicHolderWith ((1 - θ) * (2 * B) + θ * H) (α * θ) u s := by
  have hamgm : (2 * B) ^ (1 - θ) * H ^ θ ≤ (1 - θ) * (2 * B) + θ * H :=
    Real.geom_mean_le_arith_mean2_weighted (by linarith) hθ0 (by linarith) hH0 (by ring)
  exact (parabolicHolderWith_interpolation hB0 hH0 hθ0 hθ1 hbdd hhol).mono_const hamgm

/-- **Uniform interpolation constant.**  The convex-combination constant of
`parabolicHolderWith_interpolation_add` is bounded by the uniform value `2 · B + H`. -/
theorem parabolicHolderWith_interpolation_add_le
    {B H α θ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hB0 : 0 ≤ B) (hH0 : 0 ≤ H) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hbdd : ParabolicBoundedWith B u s)
    (hhol : ParabolicHolderWith H α u s) :
    ParabolicHolderWith (2 * B + H) (α * θ) u s := by
  refine (parabolicHolderWith_interpolation_add hB0 hH0 hθ0 hθ1 hbdd hhol).mono_const ?_
  have h1 : (1 - θ) * (2 * B) ≤ 2 * B := by nlinarith
  have h2 : θ * H ≤ H := by nlinarith
  linarith

/-- **Parabolic Hölder interpolation, absorbing form.**  For a parabolically bounded (`B`) and
`α`-Hölder (`H`) function, every weight `0 ≤ θ < 1`, and every scaling parameter `κ > 0`, the
intermediate `α · θ`-Hölder control holds with the *absorbing* constant
`(1 − θ) · κ^{−θ/(1−θ)} · (2 · B) + θ κ · H`, whose `θ κ` coefficient on `H` is tunable to any
target. -/
theorem parabolicHolderWith_interpolation_absorb
    {B H α θ κ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hB0 : 0 ≤ B) (hH0 : 0 ≤ H) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hκ : 0 < κ)
    (hbdd : ParabolicBoundedWith B u s)
    (hhol : ParabolicHolderWith H α u s) :
    ParabolicHolderWith
      ((1 - θ) * (κ ^ (-(θ / (1 - θ))) * (2 * B)) + θ * (κ * H)) (α * θ) u s := by
  refine (parabolicHolderWith_interpolation hB0 hH0 hθ0 (le_of_lt hθ1) hbdd hhol).mono_const ?_
  exact rpow_mul_rpow_le_absorb (by linarith) hH0 hθ0 hθ1 hκ

/-- **Additive interpolation at the seminorm level.**  For a function in the parabolic `C^{0,α}`
class and every weight `0 ≤ θ ≤ 1`,
`[u]_{α θ} ≤ (1 − θ) · (2 · ‖u‖_{C^0}) + θ · [u]_α`. -/
theorem parabolicHolderSeminorm_interpolation_add_le
    {α θ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : ParabolicC0AlphaOn α u s) :
    parabolicHolderSeminorm (α * θ) u s
      ≤ (1 - θ) * (2 * parabolicSupNorm u s) + θ * parabolicHolderSeminorm α u s := by
  obtain ⟨hbdd, hhol⟩ :=
    parabolicC0AlphaWith_parabolicSupNorm_parabolicHolderSeminorm hu
  refine parabolicHolderSeminorm_le ?_ ?_
  · exact add_nonneg
      (mul_nonneg (by linarith)
        (by have := parabolicSupNorm_nonneg u s; linarith))
      (mul_nonneg hθ0 (parabolicHolderSeminorm_nonneg α u s))
  · exact parabolicHolderWith_interpolation_add (parabolicSupNorm_nonneg u s)
      (parabolicHolderSeminorm_nonneg α u s) hθ0 hθ1 hbdd hhol

/-- **Absorbing interpolation at the seminorm level.**  For a function in the parabolic `C^{0,α}`
class, every weight `0 ≤ θ < 1`, and every `κ > 0`,
`[u]_{α θ} ≤ (1 − θ) · κ^{−θ/(1−θ)} · (2 · ‖u‖_{C^0}) + θ κ · [u]_α`.  The functional form of the
absorbing interpolation. -/
theorem parabolicHolderSeminorm_interpolation_absorb_le
    {α θ κ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hκ : 0 < κ)
    (hu : ParabolicC0AlphaOn α u s) :
    parabolicHolderSeminorm (α * θ) u s
      ≤ (1 - θ) * (κ ^ (-(θ / (1 - θ))) * (2 * parabolicSupNorm u s))
        + θ * (κ * parabolicHolderSeminorm α u s) := by
  obtain ⟨hbdd, hhol⟩ :=
    parabolicC0AlphaWith_parabolicSupNorm_parabolicHolderSeminorm hu
  refine parabolicHolderSeminorm_le ?_ ?_
  · exact add_nonneg
      (mul_nonneg (by linarith)
        (mul_nonneg (Real.rpow_nonneg hκ.le _)
          (by have := parabolicSupNorm_nonneg u s; linarith)))
      (mul_nonneg hθ0 (mul_nonneg hκ.le (parabolicHolderSeminorm_nonneg α u s)))
  · exact parabolicHolderWith_interpolation_absorb (parabolicSupNorm_nonneg u s)
      (parabolicHolderSeminorm_nonneg α u s) hθ0 hθ1 hκ hbdd hhol

/-- **Short-time smallness of the intermediate Hölder seminorm.**  If `u` is parabolic `α`-Hölder on
`s`, every time-coordinate of `s` lies within `T` of the initial time `t₀`, `s` is closed under
dropping to the initial-time slice, and `u` vanishes on that slice, then for every weight
`0 ≤ θ ≤ 1` the intermediate `α · θ`-Hölder seminorm is a *small* multiple of the leading
`α`-seminorm:

  `[u]_{α θ} ≤ 2^{1−θ} · (√T)^{α (1−θ)} · [u]_α`.

Since `(√T)^{α (1−θ)} = T^{α (1−θ)/2} → 0` as the slab thickness `T → 0`, the intermediate seminorm
is dominated by an arbitrarily small fraction of the top seminorm on a thin time-slab — the
mechanism by which the Ricci–DeTurck solution map contracts in the *intermediate* seminorms too, not
merely the sup norm.  Obtained by feeding the initial-vanishing sup bound
`parabolicSupNorm ≤ [u]_α · (√T)^α` into the multiplicative interpolation
`parabolicHolderSeminorm_interpolation_le`. -/
theorem parabolicHolderSeminorm_interpolation_short_time_le
    {α θ T t₀ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hα : 0 ≤ α) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : ParabolicHolderOn α u s)
    (hslab : ∀ p ∈ s, |p.1 - t₀| ≤ T)
    (hcyl : ∀ p ∈ s, (t₀, p.2) ∈ s)
    (hu0 : ∀ x : X, (t₀, x) ∈ s → u (t₀, x) = 0) :
    parabolicHolderSeminorm (α * θ) u s
      ≤ 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)) * parabolicHolderSeminorm α u s := by
  have hH0 : 0 ≤ parabolicHolderSeminorm α u s := parabolicHolderSeminorm_nonneg α u s
  have hsqrt0 : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
  have hrpow0 : 0 ≤ Real.sqrt T ^ α := Real.rpow_nonneg hsqrt0 α
  have hne : (1 - θ) + θ ≠ 0 := by rw [show (1 - θ) + θ = 1 by ring]; norm_num
  have hhol : ParabolicHolderWith (parabolicHolderSeminorm α u s) α u s :=
    parabolicHolderWith_parabolicHolderSeminorm hu
  have hbdd : ParabolicBoundedWith (parabolicHolderSeminorm α u s * Real.sqrt T ^ α) u s := by
    rintro ⟨t, x⟩ hp
    have hp0 : (t₀, x) ∈ s := hcyl (t, x) hp
    exact norm_le_of_parabolicHolderWith_of_initial_zero hH0 hα hhol hp hp0
      (hu0 x hp0) (hslab (t, x) hp)
  have hCOA : ParabolicC0AlphaOn α u s :=
    ⟨parabolicHolderSeminorm α u s * Real.sqrt T ^ α, mul_nonneg hH0 hrpow0,
      parabolicHolderSeminorm α u s, hH0, hbdd, hhol⟩
  have hst : parabolicSupNorm u s ≤ parabolicHolderSeminorm α u s * Real.sqrt T ^ α :=
    parabolicSupNorm_le_holderSeminorm_mul_of_initial_zero hα hu hslab hcyl hu0
  have hinterp := parabolicHolderSeminorm_interpolation_le hθ0 hθ1 hCOA
  refine hinterp.trans ?_
  have e1 : (2 * (parabolicHolderSeminorm α u s * Real.sqrt T ^ α)) ^ (1 - θ)
      = 2 ^ (1 - θ) * parabolicHolderSeminorm α u s ^ (1 - θ)
        * Real.sqrt T ^ (α * (1 - θ)) := by
    rw [Real.mul_rpow (by norm_num) (mul_nonneg hH0 hrpow0), Real.mul_rpow hH0 hrpow0,
        ← Real.rpow_mul hsqrt0]
    ring
  have e2 : parabolicHolderSeminorm α u s ^ (1 - θ) * parabolicHolderSeminorm α u s ^ θ
      = parabolicHolderSeminorm α u s := by
    rw [← Real.rpow_add' hH0 hne, show (1 - θ) + θ = 1 by ring, Real.rpow_one]
  calc (2 * parabolicSupNorm u s) ^ (1 - θ) * parabolicHolderSeminorm α u s ^ θ
      ≤ (2 * (parabolicHolderSeminorm α u s * Real.sqrt T ^ α)) ^ (1 - θ)
          * parabolicHolderSeminorm α u s ^ θ := by
        apply mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (by have := parabolicSupNorm_nonneg u s; linarith)
            (by linarith [hst]) (by linarith)) (Real.rpow_nonneg hH0 θ)
    _ = 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ))
          * (parabolicHolderSeminorm α u s ^ (1 - θ) * parabolicHolderSeminorm α u s ^ θ) := by
        rw [e1]; ring
    _ = 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)) * parabolicHolderSeminorm α u s := by rw [e2]

/-- **Short-time smallness of the full intermediate `C^{0,α θ}` norm.**  For an initial-vanishing,
`α`-Hölder function on a thin time-slab, the *full* intermediate parabolic `C^{0,α θ}` norm is
controlled by a short-time-small multiple of the leading `α`-seminorm:

  `‖u‖_{C^{0,α θ}} ≤ ((√T)^α + 2^{1−θ} (√T)^{α (1−θ)}) · [u]_α`.

Both terms of the factor carry a positive power of the slab thickness `T`, so the whole intermediate
norm `→ 0` as `T → 0`.  Sum of the initial-vanishing sup bound and the intermediate-seminorm bound
`parabolicHolderSeminorm_interpolation_short_time_le`. -/
theorem parabolicC0AlphaNorm_interpolation_short_time_le
    {α θ T t₀ : ℝ} {u : ℝ × X → E} {s : Set (ℝ × X)}
    (hα : 0 ≤ α) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hu : ParabolicHolderOn α u s)
    (hslab : ∀ p ∈ s, |p.1 - t₀| ≤ T)
    (hcyl : ∀ p ∈ s, (t₀, p.2) ∈ s)
    (hu0 : ∀ x : X, (t₀, x) ∈ s → u (t₀, x) = 0) :
    parabolicC0AlphaNorm (α * θ) u s
      ≤ (Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)))
        * parabolicHolderSeminorm α u s := by
  have hsup : parabolicSupNorm u s ≤ parabolicHolderSeminorm α u s * Real.sqrt T ^ α :=
    parabolicSupNorm_le_holderSeminorm_mul_of_initial_zero hα hu hslab hcyl hu0
  have hsemi : parabolicHolderSeminorm (α * θ) u s
      ≤ 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)) * parabolicHolderSeminorm α u s :=
    parabolicHolderSeminorm_interpolation_short_time_le hα hθ0 hθ1 hu hslab hcyl hu0
  unfold parabolicC0AlphaNorm
  calc parabolicSupNorm u s + parabolicHolderSeminorm (α * θ) u s
      ≤ parabolicHolderSeminorm α u s * Real.sqrt T ^ α
        + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)) * parabolicHolderSeminorm α u s :=
        add_le_add hsup hsemi
    _ = (Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)))
        * parabolicHolderSeminorm α u s := by ring

/-- **Short-time intermediate `C^{0,α θ}` contraction for a difference (initial-agreement form).**
The form the Ricci–DeTurck fixed point consumes: if `u` and `v` agree on the initial-time slice and
their difference is `α`-Hölder on a thin slab, then the intermediate `C^{0,α θ}` norm of the
difference is short-time small relative to its own leading `α`-seminorm:

  `‖u − v‖_{C^{0,α θ}} ≤ ((√T)^α + 2^{1−θ} (√T)^{α (1−θ)}) · [u − v]_α`.

Immediate from `parabolicC0AlphaNorm_interpolation_short_time_le` applied to `u − v`, which vanishes
on the initial slice by agreement.  As `T → 0` the factor `→ 0`, so on a sufficiently thin time-slab
the map `u ↦ (solution)` is a contraction in the intermediate norm. -/
theorem parabolicC0AlphaNorm_sub_interpolation_short_time_le
    {α θ T t₀ : ℝ} {u v : ℝ × X → E} {s : Set (ℝ × X)}
    (hα : 0 ≤ α) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (huv : ParabolicHolderOn α (fun z => u z - v z) s)
    (hslab : ∀ p ∈ s, |p.1 - t₀| ≤ T)
    (hcyl : ∀ p ∈ s, (t₀, p.2) ∈ s)
    (hagree : ∀ x : X, (t₀, x) ∈ s → u (t₀, x) = v (t₀, x)) :
    parabolicC0AlphaNorm (α * θ) (fun z => u z - v z) s
      ≤ (Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)))
        * parabolicHolderSeminorm α (fun z => u z - v z) s := by
  refine parabolicC0AlphaNorm_interpolation_short_time_le hα hθ0 hθ1 huv hslab hcyl ?_
  intro x hx
  exact sub_eq_zero.mpr (hagree x hx)

/-- **Quantitative short-time smallness of the interpolation factor.**  For `0 < α`, `θ < 1`, and any
target ratio `q > 0`, there is a slab thickness `T₀ > 0` such that for every `0 ≤ T ≤ T₀` the
short-time interpolation contraction factor is at most `q`:

  `(√T)^α + 2^{1−θ} · (√T)^{α (1−θ)} ≤ q`.

Both exponents `α` and `α (1 − θ)` are strictly positive (as `α > 0`, `1 − θ > 0`), so the factor is
continuous in `T` at `0` with value `0 < q`; hence it stays below `q` on a whole neighbourhood of `0`,
and in particular on `[0, T₀]` for `T₀` half the neighbourhood radius.  This is the honest
*quantitative* form of "the factor `→ 0` as `T → 0`" that the Ricci–DeTurck fixed point consumes:
choosing the slab thin enough drives the intermediate-norm contraction ratio below any prescribed
`q < 1`. -/
theorem exists_thickness_shortTimeInterpFactor_le
    {α θ q : ℝ} (hα : 0 < α) (hθ1 : θ < 1) (hq : 0 < q) :
    ∃ T₀ > 0, ∀ T : ℝ, 0 ≤ T → T ≤ T₀ →
      Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)) ≤ q := by
  have hαθ : 0 < α * (1 - θ) := mul_pos hα (by linarith)
  have hgc : ContinuousAt
      (fun T : ℝ => Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ))) 0 :=
    (Real.continuous_sqrt.continuousAt.rpow_const (Or.inr hα.le)).add
      (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.rpow_const (Or.inr hαθ.le)))
  have hlt : Real.sqrt (0 : ℝ) ^ α + 2 ^ (1 - θ) * Real.sqrt 0 ^ (α * (1 - θ)) < q := by
    rw [Real.sqrt_zero, Real.zero_rpow (ne_of_gt hα), Real.zero_rpow (ne_of_gt hαθ),
      mul_zero, add_zero]
    exact hq
  have hev := Filter.Tendsto.eventually_lt_const hlt hgc
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨ε / 2, by positivity, fun T hT0 hTle => ?_⟩
  have hdist : dist T 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hT0]; linarith
  exact le_of_lt (hball hdist)

/-- **Short-time intermediate `C^{0,α θ}` contraction (quantitative form).**  For `0 < α`,
`0 ≤ θ < 1`, and any prescribed contraction ratio `q > 0`, there is a slab thickness `T₀ > 0` such
that on *every* time-slab of thickness `T ≤ T₀` (closed under dropping to the initial slice), any two
functions `u`, `v` agreeing on the initial slice with `α`-Hölder difference satisfy the genuine
`q`-contraction estimate in the intermediate parabolic norm:

  `‖u − v‖_{C^{0,α θ}} ≤ q · [u − v]_α`.

This is the load-bearing capstone the Ricci–DeTurck short-time fixed point consumes: it upgrades the
qualitative short-time smallness `parabolicC0AlphaNorm_sub_interpolation_short_time_le` (whose factor
merely `→ 0`) to the quantitative "thin enough slab ⇒ contraction ratio `< 1`" statement, by choosing
`T₀` so small (`exists_thickness_shortTimeInterpFactor_le`) that the interpolation factor is below the
target ratio `q`.  Taking `q < 1` exhibits the solution map as a strict contraction in the
intermediate `C^{0,α θ}` norm on a sufficiently thin time-slab. -/
theorem exists_thickness_parabolicC0AlphaNorm_sub_interpolation_contraction
    {α θ q : ℝ} (hα : 0 < α) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hq : 0 < q) :
    ∃ T₀ > 0, ∀ {T t₀ : ℝ} {u v : ℝ × X → E} {s : Set (ℝ × X)},
      0 ≤ T → T ≤ T₀ →
      ParabolicHolderOn α (fun z => u z - v z) s →
      (∀ p ∈ s, |p.1 - t₀| ≤ T) →
      (∀ p ∈ s, (t₀, p.2) ∈ s) →
      (∀ x : X, (t₀, x) ∈ s → u (t₀, x) = v (t₀, x)) →
      parabolicC0AlphaNorm (α * θ) (fun z => u z - v z) s
        ≤ q * parabolicHolderSeminorm α (fun z => u z - v z) s := by
  obtain ⟨T₀, hT₀, hfac⟩ := exists_thickness_shortTimeInterpFactor_le hα hθ1 hq
  refine ⟨T₀, hT₀, ?_⟩
  intro T t₀ u v s hT0 hTle huv hslab hcyl hagree
  refine (parabolicC0AlphaNorm_sub_interpolation_short_time_le hα.le hθ0 hθ1.le
    huv hslab hcyl hagree).trans ?_
  exact mul_le_mul_of_nonneg_right (hfac T hT0 hTle)
    (parabolicHolderSeminorm_nonneg α (fun z => u z - v z) s)

/-- **Short-time existence reduces to the parabolic Schauder gain (contraction form).**  Suppose a
solution map produces, from candidate perturbations `w₁`, `w₂`, outputs `Sw₁`, `Sw₂` that
* agree on the initial-time slice (the solution map preserves the prescribed initial data), and
* whose difference is `α`-Hölder on the slab and satisfies the **parabolic Schauder gain**
  `[Sw₁ − Sw₂]_α ≤ C · ‖w₁ − w₂‖_{C^{0,α θ}}`
  (gain of regularity from the intermediate `C^{0,α θ}` input norm to the top `α`-Hölder seminorm of
  the output — the heat-kernel content, taken here as a hypothesis).

Then for `0 < α`, `0 ≤ θ < 1`, gain constant `C ≥ 0` and any target ratio `q > 0`, there is a slab
thickness `T₀ > 0` such that on every slab of thickness `T ≤ T₀` the solution map is a genuine
`q`-contraction **in the intermediate `C^{0,α θ}` norm** (the same exponent on both sides):

  `‖Sw₁ − Sw₂‖_{C^{0,α θ}} ≤ q · ‖w₁ − w₂‖_{C^{0,α θ}}`.

Composing the short-time interpolation smallness `‖Sw₁ − Sw₂‖_{α θ} ≤ factor(T) · [Sw₁ − Sw₂]_α`
(`parabolicC0AlphaNorm_sub_interpolation_short_time_le`, whose factor `→ 0`) with the gain and choosing
`T₀` so that `factor(T) · C ≤ q` (`exists_thickness_shortTimeInterpFactor_le` with target
`q / (C + 1)`).  Taking `q < 1` exhibits the solution map as a strict contraction on the complete
parabolic `C^{0,α θ}` space — the exact input to `exists_parabolicC0AlphaOn_fixedPt_of_contraction` —
reducing Ricci–DeTurck short-time existence to the single Schauder gain estimate. -/
theorem exists_thickness_solutionMap_contraction_of_schauder_gain
    {α θ C q : ℝ} (hα : 0 < α) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C) (hq : 0 < q) :
    ∃ T₀ > 0, ∀ {T t₀ : ℝ} {w₁ w₂ Sw₁ Sw₂ : ℝ × X → E} {s : Set (ℝ × X)},
      0 ≤ T → T ≤ T₀ →
      ParabolicHolderOn α (fun z => Sw₁ z - Sw₂ z) s →
      (∀ p ∈ s, |p.1 - t₀| ≤ T) →
      (∀ p ∈ s, (t₀, p.2) ∈ s) →
      (∀ x : X, (t₀, x) ∈ s → Sw₁ (t₀, x) = Sw₂ (t₀, x)) →
      parabolicHolderSeminorm α (fun z => Sw₁ z - Sw₂ z) s
        ≤ C * parabolicC0AlphaNorm (α * θ) (fun z => w₁ z - w₂ z) s →
      parabolicC0AlphaNorm (α * θ) (fun z => Sw₁ z - Sw₂ z) s
        ≤ q * parabolicC0AlphaNorm (α * θ) (fun z => w₁ z - w₂ z) s := by
  have hCp : (0 : ℝ) < C + 1 := by linarith
  have hCne : (C : ℝ) + 1 ≠ 0 := ne_of_gt hCp
  obtain ⟨T₀, hT₀, hfac⟩ :=
    exists_thickness_shortTimeInterpFactor_le hα hθ1 (div_pos hq hCp)
  refine ⟨T₀, hT₀, ?_⟩
  intro T t₀ w₁ w₂ Sw₁ Sw₂ s hT0 hTle hdiff hslab hcyl hagree hgain
  have hfac_nonneg :
      (0 : ℝ) ≤ Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)) :=
    add_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg T) α)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Real.rpow_nonneg (Real.sqrt_nonneg T) _))
  have hfacC :
      (Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ))) * C ≤ q := by
    have h1 := mul_le_mul_of_nonneg_right (hfac T hT0 hTle) hC
    have h2 : q / (C + 1) * C ≤ q := by
      have hq1 : (0 : ℝ) ≤ q / (C + 1) := by positivity
      calc q / (C + 1) * C ≤ q / (C + 1) * (C + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) hq1
        _ = q := by field_simp
    exact h1.trans h2
  calc parabolicC0AlphaNorm (α * θ) (fun z => Sw₁ z - Sw₂ z) s
      ≤ (Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)))
          * parabolicHolderSeminorm α (fun z => Sw₁ z - Sw₂ z) s :=
        parabolicC0AlphaNorm_sub_interpolation_short_time_le hα.le hθ0 hθ1.le
          hdiff hslab hcyl hagree
    _ ≤ (Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ)))
          * (C * parabolicC0AlphaNorm (α * θ) (fun z => w₁ z - w₂ z) s) :=
        mul_le_mul_of_nonneg_left hgain hfac_nonneg
    _ = ((Real.sqrt T ^ α + 2 ^ (1 - θ) * Real.sqrt T ^ (α * (1 - θ))) * C)
          * parabolicC0AlphaNorm (α * θ) (fun z => w₁ z - w₂ z) s := by ring
    _ ≤ q * parabolicC0AlphaNorm (α * θ) (fun z => w₁ z - w₂ z) s :=
        mul_le_mul_of_nonneg_right hfacC
          (parabolicC0AlphaNorm_nonneg (α * θ) (fun z => w₁ z - w₂ z) s)

/-- **Ricci–DeTurck short-time existence & uniqueness, reduced to the parabolic Schauder gain.**
Suppose a solution map `S` on the parabolic `C^{0,α θ}` class over a slab `s` (anchored at initial time
`t₀`, closed under dropping to the initial slice) has:
* a starting iterate `u₀` in the class (`hu₀`);
* the self-mapping property `hSmaps` (`S` preserves the `C^{0,α θ}` class);
* `α`-Hölder output differences `hSholder`;
* initial-data preservation `hSinit` (`S w₁` and `S w₂` agree on the initial slice — both equal the
  prescribed initial datum);
* the **parabolic Schauder gain** `hSgain`:
  `[S w₁ − S w₂]_α ≤ C · ‖w₁ − w₂‖_{C^{0,α θ}}` (the sole remaining heat-kernel content).

Then there is a slab thickness `T₀ > 0` such that on *every* thin enough slab (`T ≤ T₀`) the solution
map has a **unique** fixed point `g` in the parabolic `C^{0,α θ}` class:

  `S g = g on s`, and any other `C^{0,α θ}` fixed point of `S` on `s` coincides with `g`.

This is the abstract Ricci–DeTurck short-time well-posedness: on a sufficiently thin time-slab the
interpolation smallness turns the Schauder gain into a strict `½`-contraction
(`exists_thickness_solutionMap_contraction_of_schauder_gain` with `q = ½`), and the parabolic Banach
fixed point (`exists_parabolicC0AlphaOn_fixedPt_of_contraction`) supplies the unique solution.  Every
hypothesis except the Schauder gain is a structural property of the DeTurck solution operator, so this
reduces the analytic core of Item 3 to that one estimate. -/
theorem exists_shortTime_fixedPoint_of_schauder_gain [CompleteSpace E]
    {α θ C : ℝ} (hα : 0 < α) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C) :
    ∃ T₀ > 0, ∀ {T t₀ : ℝ} {s : Set (ℝ × X)}
        {S : (ℝ × X → E) → (ℝ × X → E)} {u₀ : ℝ × X → E},
      0 ≤ T → T ≤ T₀ →
      (∀ p ∈ s, |p.1 - t₀| ≤ T) →
      (∀ p ∈ s, (t₀, p.2) ∈ s) →
      ParabolicC0AlphaOn (α * θ) u₀ s →
      (∀ u, ParabolicC0AlphaOn (α * θ) u s → ParabolicC0AlphaOn (α * θ) (S u) s) →
      (∀ w₁ w₂, ParabolicC0AlphaOn (α * θ) w₁ s → ParabolicC0AlphaOn (α * θ) w₂ s →
        ParabolicHolderOn α (fun z => S w₁ z - S w₂ z) s) →
      (∀ w₁ w₂, ∀ x : X, (t₀, x) ∈ s → S w₁ (t₀, x) = S w₂ (t₀, x)) →
      (∀ w₁ w₂, ParabolicC0AlphaOn (α * θ) w₁ s → ParabolicC0AlphaOn (α * θ) w₂ s →
        parabolicHolderSeminorm α (fun z => S w₁ z - S w₂ z) s
          ≤ C * parabolicC0AlphaNorm (α * θ) (fun z => w₁ z - w₂ z) s) →
      ∃ g, ParabolicC0AlphaOn (α * θ) g s ∧ Set.EqOn (S g) g s ∧
        ∀ w, ParabolicC0AlphaOn (α * θ) w s → Set.EqOn (S w) w s → Set.EqOn w g s := by
  obtain ⟨T₀, hT₀, hcontr⟩ :=
    exists_thickness_solutionMap_contraction_of_schauder_gain (X := X) (E := E)
      (q := (1 : ℝ) / 2) hα hθ0 hθ1 hC (by norm_num)
  refine ⟨T₀, hT₀, ?_⟩
  intro T t₀ s S u₀ hT0 hTle hslab hcyl hu₀ hSmaps hSholder hSinit hSgain
  refine exists_parabolicC0AlphaOn_fixedPt_of_contraction (α := α * θ) (q := (1 : ℝ) / 2)
    (by norm_num) (by norm_num) hu₀ hSmaps (fun w₁ w₂ hw₁ hw₂ => ?_)
  exact hcontr hT0 hTle (hSholder w₁ w₂ hw₁ hw₂) hslab hcyl
    (fun x hx => hSinit w₁ w₂ x hx) (hSgain w₁ w₂ hw₁ hw₂)

/-- **Ricci–DeTurck short-time existence with an a-priori solution bound, reduced to the Schauder
gain.**  The quantitative refinement of `exists_shortTime_fixedPoint_of_schauder_gain`: under the same
hypotheses (self-mapping, initial-data preservation, `α`-Hölder output differences, and the parabolic
Schauder gain `[S w₁ − S w₂]_α ≤ C · ‖w₁ − w₂‖_{C^{0,α θ}}`), on a thin enough slab the unique
`C^{0,α θ}` fixed point `g = S g` additionally satisfies the a-priori bound

  `‖g − u₀‖_{C^{0,α θ}} ≤ 2 · ‖S u₀ − u₀‖_{C^{0,α θ}}`

controlling the solution by (twice) the initial residual `‖S u₀ − u₀‖_{C^{0,α θ}}` of any starting
guess `u₀` — the estimate that keeps the DeTurck solution inside the ball on which the coefficient
data / Schauder gain remain valid.  The `½`-contraction (constant `(1 − ½)⁻¹ = 2`) fed into the
ball-form parabolic Banach fixed point `exists_parabolicC0AlphaOn_fixedPt_ball_of_contraction`. -/
theorem exists_shortTime_fixedPoint_ball_of_schauder_gain [CompleteSpace E]
    {α θ C : ℝ} (hα : 0 < α) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C) :
    ∃ T₀ > 0, ∀ {T t₀ : ℝ} {s : Set (ℝ × X)}
        {S : (ℝ × X → E) → (ℝ × X → E)} {u₀ : ℝ × X → E},
      0 ≤ T → T ≤ T₀ →
      (∀ p ∈ s, |p.1 - t₀| ≤ T) →
      (∀ p ∈ s, (t₀, p.2) ∈ s) →
      ParabolicC0AlphaOn (α * θ) u₀ s →
      (∀ u, ParabolicC0AlphaOn (α * θ) u s → ParabolicC0AlphaOn (α * θ) (S u) s) →
      (∀ w₁ w₂, ParabolicC0AlphaOn (α * θ) w₁ s → ParabolicC0AlphaOn (α * θ) w₂ s →
        ParabolicHolderOn α (fun z => S w₁ z - S w₂ z) s) →
      (∀ w₁ w₂, ∀ x : X, (t₀, x) ∈ s → S w₁ (t₀, x) = S w₂ (t₀, x)) →
      (∀ w₁ w₂, ParabolicC0AlphaOn (α * θ) w₁ s → ParabolicC0AlphaOn (α * θ) w₂ s →
        parabolicHolderSeminorm α (fun z => S w₁ z - S w₂ z) s
          ≤ C * parabolicC0AlphaNorm (α * θ) (fun z => w₁ z - w₂ z) s) →
      ∃ g, ParabolicC0AlphaOn (α * θ) g s ∧ Set.EqOn (S g) g s ∧
        (∀ w, ParabolicC0AlphaOn (α * θ) w s → Set.EqOn (S w) w s → Set.EqOn w g s) ∧
        parabolicC0AlphaNorm (α * θ) (fun z => g z - u₀ z) s
          ≤ 2 * parabolicC0AlphaNorm (α * θ) (fun z => S u₀ z - u₀ z) s := by
  obtain ⟨T₀, hT₀, hcontr⟩ :=
    exists_thickness_solutionMap_contraction_of_schauder_gain (X := X) (E := E)
      (q := (1 : ℝ) / 2) hα hθ0 hθ1 hC (by norm_num)
  refine ⟨T₀, hT₀, ?_⟩
  intro T t₀ s S u₀ hT0 hTle hslab hcyl hu₀ hSmaps hSholder hSinit hSgain
  obtain ⟨g, hg, hfix, huniq, hbound⟩ :=
    exists_parabolicC0AlphaOn_fixedPt_ball_of_contraction (α := α * θ) (q := (1 : ℝ) / 2)
      (by norm_num) (by norm_num) hu₀ hSmaps (fun w₁ w₂ hw₁ hw₂ =>
        hcontr hT0 hTle (hSholder w₁ w₂ hw₁ hw₂) hslab hcyl
          (fun x hx => hSinit w₁ w₂ x hx) (hSgain w₁ w₂ hw₁ hw₂))
  exact ⟨g, hg, hfix, huniq, hbound.trans_eq (by norm_num)⟩

/-- **Ricci–DeTurck short-time continuous dependence, reduced to the parabolic Schauder gain.**
The stability companion of `exists_shortTime_fixedPoint_of_schauder_gain` and
`exists_shortTime_fixedPoint_ball_of_schauder_gain`, completing the abstract well-posedness family
(existence, uniqueness, a-priori bound, *stability*) on the reduced-to-Schauder-gain route.

Given two solution maps `S₁`, `S₂` on the parabolic `C^{0,α θ}` class over a slab `s` anchored at the
initial time `t₀` (closed under dropping to the initial slice), where `S₁` self-maps (`hS₁maps`),
preserves initial data (`hS₁init`), has `α`-Hölder output differences (`hS₁holder`) and satisfies the
parabolic Schauder gain (`hS₁gain`) — so that on a thin enough slab it is a `½`-contraction — and `S₂`
self-maps (`hS₂maps`), the respective fixed points `g₁ = S₁ g₁`, `g₂ = S₂ g₂` obey the
continuous-dependence bound

  `‖g₁ − g₂‖_{C^{0,α θ}} ≤ 2 · ‖S₁ g₂ − S₂ g₂‖_{C^{0,α θ}}`

on every slab of thickness `T ≤ T₀`.  Two solution operators agreeing at their common fixed locus
have identical short-time solutions (recovering uniqueness), and nearby operators have nearby
solutions — the Hadamard continuous-dependence leg for the Ricci–DeTurck short-time flow, obtained by
feeding the thin-slab `½`-contraction of `S₁`
(`exists_thickness_solutionMap_contraction_of_schauder_gain`, `q = ½`) into the two-map fixed-point
stability bound `parabolicC0AlphaNorm_fixedPt_sub_fixedPt_le_of_contraction`
(constant `(1 − ½)⁻¹ = 2`). -/
theorem exists_shortTime_fixedPoint_stability_of_schauder_gain [CompleteSpace E]
    {α θ C : ℝ} (hα : 0 < α) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (hC : 0 ≤ C) :
    ∃ T₀ > 0, ∀ {T t₀ : ℝ} {s : Set (ℝ × X)}
        {S₁ S₂ : (ℝ × X → E) → (ℝ × X → E)} {g₁ g₂ : ℝ × X → E},
      0 ≤ T → T ≤ T₀ →
      (∀ p ∈ s, |p.1 - t₀| ≤ T) →
      (∀ p ∈ s, (t₀, p.2) ∈ s) →
      (∀ u, ParabolicC0AlphaOn (α * θ) u s → ParabolicC0AlphaOn (α * θ) (S₁ u) s) →
      (∀ u, ParabolicC0AlphaOn (α * θ) u s → ParabolicC0AlphaOn (α * θ) (S₂ u) s) →
      (∀ w₁ w₂, ParabolicC0AlphaOn (α * θ) w₁ s → ParabolicC0AlphaOn (α * θ) w₂ s →
        ParabolicHolderOn α (fun z => S₁ w₁ z - S₁ w₂ z) s) →
      (∀ w₁ w₂, ∀ x : X, (t₀, x) ∈ s → S₁ w₁ (t₀, x) = S₁ w₂ (t₀, x)) →
      (∀ w₁ w₂, ParabolicC0AlphaOn (α * θ) w₁ s → ParabolicC0AlphaOn (α * θ) w₂ s →
        parabolicHolderSeminorm α (fun z => S₁ w₁ z - S₁ w₂ z) s
          ≤ C * parabolicC0AlphaNorm (α * θ) (fun z => w₁ z - w₂ z) s) →
      ParabolicC0AlphaOn (α * θ) g₁ s → ParabolicC0AlphaOn (α * θ) g₂ s →
      Set.EqOn (S₁ g₁) g₁ s → Set.EqOn (S₂ g₂) g₂ s →
      parabolicC0AlphaNorm (α * θ) (fun z => g₁ z - g₂ z) s
        ≤ 2 * parabolicC0AlphaNorm (α * θ) (fun z => S₁ g₂ z - S₂ g₂ z) s := by
  obtain ⟨T₀, hT₀, hcontr⟩ :=
    exists_thickness_solutionMap_contraction_of_schauder_gain (X := X) (E := E)
      (q := (1 : ℝ) / 2) hα hθ0 hθ1 hC (by norm_num)
  refine ⟨T₀, hT₀, ?_⟩
  intro T t₀ s S₁ S₂ g₁ g₂ hT0 hTle hslab hcyl hS₁maps hS₂maps hS₁holder hS₁init hS₁gain
    hg₁ hg₂ hg₁fix hg₂fix
  have hbound := parabolicC0AlphaNorm_fixedPt_sub_fixedPt_le_of_contraction
    (q := (1 : ℝ) / 2) (by norm_num) hg₁ hg₂ hg₁fix hg₂fix hS₁maps hS₂maps
    (fun u v hu hv => hcontr hT0 hTle (hS₁holder u v hu hv) hslab hcyl
      (fun x hx => hS₁init u v x hx) (hS₁gain u v hu hv))
  exact hbound.trans_eq (by norm_num)

end AnalyticPDE
end RicciFlow
