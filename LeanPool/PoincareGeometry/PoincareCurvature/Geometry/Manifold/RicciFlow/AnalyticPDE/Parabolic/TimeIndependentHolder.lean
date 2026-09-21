/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.BanachSpace

/-!
# Time-independent spatial fields in parabolic Hölder spaces

A bounded spatially Lipschitz field, regarded as a function on time-space,
is parabolic `C^{0,α}` for every `0 < α ≤ 1`.  The large-distance part of
the estimate is supplied by the uniform bound.  This file packages that
elementary interpolation with explicit constants, including the Banach-space
representative used for globalized coordinate coefficients.
-/

@[expose] public noncomputable section
open Set

namespace RicciFlow
namespace AnalyticPDE

variable {X V : Type*} [PseudoMetricSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A bounded field with a Lipschitz estimate is Hölder of every exponent in
`(0,1]`.  At distances at most one, `d ≤ d^α`; at larger distances the
uniform bound controls the oscillation. -/
theorem parabolicHolderWith_of_bounded_of_lipschitz
    {B L α : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1)
    {u : ℝ × X → V} {s : Set (ℝ × X)}
    (hb : ParabolicBoundedWith B u s)
    (hlip : ∀ ⦃p : ℝ × X⦄, p ∈ s → ∀ ⦃q : ℝ × X⦄, q ∈ s →
      ‖u p - u q‖ ≤ L * parabolicDistance p q) :
    ParabolicHolderWith (2 * B + L) α u s := by
  intro p hp q hq
  let d := parabolicDistance p q
  have hd0 : 0 ≤ d := parabolicDistance.nonneg p q
  by_cases hd1 : d ≤ 1
  · have hpow : d ≤ d ^ α := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' hd0 hd1 hα.le hα1
    exact (hlip hp hq).trans <|
      calc
        L * d ≤ L * d ^ α := mul_le_mul_of_nonneg_left hpow hL
        _ ≤ (2 * B + L) * d ^ α := by
          exact mul_le_mul_of_nonneg_right (by linarith)
            (Real.rpow_nonneg hd0 α)
  · have hd1' : 1 ≤ d := le_of_not_ge hd1
    have hpow : 1 ≤ d ^ α := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow zero_le_one hd1' hα.le
    calc
      ‖u p - u q‖ ≤ ‖u p‖ + ‖u q‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hb hp) (hb hq)
      _ = 2 * B := by ring
      _ ≤ (2 * B + L) * d ^ α := by
        nlinarith [Real.rpow_nonneg hd0 α]

/-- A bounded spatially Lipschitz field, lifted without time dependence, has
explicit parabolic `C^{0,α}` control on every time-space set. -/
theorem parabolicC0AlphaWith_snd_of_bounded_of_lipschitz
    {B L α : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1)
    {f : X → V} {s : Set (ℝ × X)}
    (hb : ∀ x ∈ Prod.snd '' s, ‖f x‖ ≤ B)
    (hlip : ∀ x ∈ Prod.snd '' s, ∀ y ∈ Prod.snd '' s,
      ‖f x - f y‖ ≤ L * dist x y) :
    ParabolicC0AlphaWith B (2 * B + L) α (fun z : ℝ × X => f z.2) s := by
  refine ⟨ParabolicBoundedWith.of_snd hb, ?_⟩
  apply parabolicHolderWith_of_bounded_of_lipschitz hB hL hα hα1
    (ParabolicBoundedWith.of_snd hb)
  intro p hp q hq
  have hpim : p.2 ∈ Prod.snd '' s := ⟨p, hp, rfl⟩
  have hqim : q.2 ∈ Prod.snd '' s := ⟨q, hq, rfl⟩
  exact (hlip p.2 hpim q.2 hqim).trans
    (mul_le_mul_of_nonneg_left (parabolicDistance.space_dist_le p q) hL)

/-- The time-independent lift of a bounded spatially Lipschitz field as a
member of the parabolic Hölder function space. -/
def ParabolicC0AlphaSpace.ofSpatialBoundedLipschitz
    {B L α : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : X → V) (s : Set (ℝ × X))
    (hb : ∀ x ∈ Prod.snd '' s, ‖f x‖ ≤ B)
    (hlip : ∀ x ∈ Prod.snd '' s, ∀ y ∈ Prod.snd '' s,
      ‖f x - f y‖ ≤ L * dist x y) :
    ParabolicC0AlphaSpace X V α s :=
  ParabolicC0AlphaSpace.ofSubmodule ⟨(fun z => f z.2),
    ⟨B, hB, 2 * B + L, by positivity,
      parabolicC0AlphaWith_snd_of_bounded_of_lipschitz
        hB hL hα hα1 hb hlip⟩⟩

@[simp] theorem ParabolicC0AlphaSpace.toFun_ofSpatialBoundedLipschitz
    {B L α : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : X → V) (s : Set (ℝ × X))
    (hb : ∀ x ∈ Prod.snd '' s, ‖f x‖ ≤ B)
    (hlip : ∀ x ∈ Prod.snd '' s, ∀ y ∈ Prod.snd '' s,
      ‖f x - f y‖ ≤ L * dist x y) (z : ℝ × X) :
    ParabolicC0AlphaSpace.toFun
        (ParabolicC0AlphaSpace.ofSpatialBoundedLipschitz
          hB hL hα hα1 f s hb hlip) z = f z.2 :=
  rfl

/-- Explicit norm bound for a time-independent bounded spatially Lipschitz
field. -/
theorem ParabolicC0AlphaSpace.norm_ofSpatialBoundedLipschitz_le
    {B L α : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L) (hα : 0 < α) (hα1 : α ≤ 1)
    (f : X → V) (s : Set (ℝ × X))
    (hb : ∀ x ∈ Prod.snd '' s, ‖f x‖ ≤ B)
    (hlip : ∀ x ∈ Prod.snd '' s, ∀ y ∈ Prod.snd '' s,
      ‖f x - f y‖ ≤ L * dist x y) :
    ‖ParabolicC0AlphaSpace.ofSpatialBoundedLipschitz
        hB hL hα hα1 f s hb hlip‖ ≤ 3 * B + L := by
  rw [ParabolicC0AlphaSpace.norm_def]
  change parabolicC0AlphaNorm α (fun z : ℝ × X => f z.2) s ≤ 3 * B + L
  calc
    parabolicC0AlphaNorm α (fun z : ℝ × X => f z.2) s
        ≤ B + (2 * B + L) := parabolicC0AlphaNorm_le hB (by positivity)
          (parabolicC0AlphaWith_snd_of_bounded_of_lipschitz
            hB hL hα hα1 hb hlip)
    _ = 3 * B + L := by ring

end AnalyticPDE
end RicciFlow
