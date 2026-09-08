/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.OctagonalDescent
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Both rare-distance assertions for coordinates in Q(sqrt(2))

See the project entry module for the exact coordinate restrictions and source roles.
Integer coefficient clearing is an actual complex similarity. The resulting
rare classes are counted in the original complete unordered distance graph.
-/

namespace LeanPool.RareDistanceFields.OctagonalRational

open OctagonalNorm
noncomputable section

variable {V : Type*} [Fintype V]

open Classical in
/-- The complete simple distance graph on distinct configuration labels. -/
def graph (x : V → ℂ) (d : ℝ) : SimpleGraph V :=
  OrderedColors.colorGraph (fun a b => dist (x a) (x b))
    (fun _ _ => dist_comm _ _) d

open Classical in
/-- Occurring distances whose unordered multiplicities are at most the label count. -/
def rareDistances (x : V → ℂ) : Finset ℝ :=
  (OrderedColors.palette (fun a b => dist (x a) (x b))).filter
    fun d => (graph x d).edgeFinset.card ≤ Fintype.card V

open Classical in
/-- Both real coordinates of each point have the form a + b*sqrt(2) with rational a, b. -/
def QuadraticCoordinates (x : V → ℂ) : Prop :=
  ∀ i, ∃ a b c d : ℚ, (x i).re = (a : ℝ) + (b : ℝ) * Real.sqrt 2 ∧
    (x i).im = (c : ℝ) + (d : ℝ) * Real.sqrt 2

omit [Fintype V] in
open Classical in
theorem clear_coordinates [Finite V] (x : V → ℂ) (h : QuadraticCoordinates x) :
    ∃ B : ℤ, B ≠ 0 ∧ ∃ y : V → Point, ∀ i, embed (y i) = (B : ℂ) * x i := by
  let := Fintype.ofFinite V
  choose a b c d hre him using h
  let f : V × Fin 4 → ℚ := fun p => ![a p.1, b p.1 + d p.1, c p.1, d p.1 - b p.1] p.2
  obtain ⟨B, hB⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) f
  choose coeff hcoeff using hB
  refine ⟨B, nonZeroDivisors.ne_zero B.property,
    (fun i => ((coeff (i, 0), coeff (i, 1)), (coeff (i, 2), coeff (i, 3)))), ?_⟩
  intro i
  have h0 : (coeff (i, 0) : ℚ) = (B : ℤ) * a i := by simpa [f, zsmul_eq_mul] using hcoeff (i, 0)
  have h1 : (coeff (i, 1) : ℚ) = (B : ℤ) * (b i + d i) := by
    simpa [f, zsmul_eq_mul, mul_add] using hcoeff (i, 1)
  have h2 : (coeff (i, 2) : ℚ) = (B : ℤ) * c i := by simpa [f, zsmul_eq_mul] using hcoeff (i, 2)
  have h3 : (coeff (i, 3) : ℚ) = (B : ℤ) * (d i - b i) := by
    simpa [f, zsmul_eq_mul] using hcoeff (i, 3)
  have h0R : (coeff (i, 0) : ℝ) = (B : ℤ) * (a i : ℝ) := by exact_mod_cast h0
  have h1R : (coeff (i, 1) : ℝ) = (B : ℤ) * ((b i : ℝ) + (d i : ℝ)) := by exact_mod_cast h1
  have h2R : (coeff (i, 2) : ℝ) = (B : ℤ) * (c i : ℝ) := by exact_mod_cast h2
  have h3R : (coeff (i, 3) : ℝ) = (B : ℤ) * ((d i : ℝ) - (b i : ℝ)) := by exact_mod_cast h3
  apply Complex.ext
  · change (coeff (i, 0) : ℝ) + (coeff (i, 1) - coeff (i, 3) : ℤ) * Real.sqrt 2 / 2 =
      ((B : ℂ) * x i).re
    simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, zero_mul, sub_zero]
    push_cast
    rw [h0R, h1R, h3R, hre i]
    ring
  · change (coeff (i, 2) : ℝ) + (coeff (i, 1) + coeff (i, 3) : ℤ) * Real.sqrt 2 / 2 =
      ((B : ℂ) * x i).im
    simp only [Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero]
    push_cast
    rw [h2R, h1R, h3R, him i]
    ring

open Classical in
theorem card_le_pow_of_scaled_integer (x : V → ℂ) (hx : Function.Injective x)
    (B : ℤ) (hB : B ≠ 0) (y : V → Point) (hy : ∀ i, embed (y i) = (B : ℂ) * x i) :
    Fintype.card V ≤ 2 ^ (rareDistances x).card := by
  have hB' : (B : ℂ) ≠ 0 := by exact_mod_cast hB
  have hnorm : ‖(B : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hB'
  have hyinj : Function.Injective y := by
    intro a b he
    apply hx
    apply mul_left_cancel₀ hB'
    rw [←hy a, ←hy b, he]
  have hscale (a b : V) : dist (embed (y a)) (embed (y b)) = ‖(B : ℂ)‖ * dist (x a) (x b) := by
    rw [hy a, hy b, Complex.dist_eq, ←mul_sub, Complex.norm_mul, ←Complex.dist_eq]
  let f : ℝ → ℝ := fun d => d / ‖(B : ℂ)‖
  have hf : Function.Injective f := by
    intro a b he
    exact (div_left_inj' hnorm).mp he
  have heq (a b : V) (d : ℝ) : dist (embed (y a)) (embed (y b)) = d ↔ dist (x a) (x b) = f d := by
    dsimp [f]
    rw [hscale, eq_div_iff hnorm, mul_comm]
  have hg (d : ℝ) : BinaryPalette.graph OctagonalDescent.model y d = graph x (f d) := by
    ext a b
    simp only [BinaryPalette.graph, graph, OrderedColors.colorGraph,
      BinaryDescent.Model.distance, OctagonalDescent.model, heq]
  have hsub : (OctagonalDescent.rareDistances y).image f ⊆ rareDistances x := by
    intro d hd
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨_, ⟨a, b, hab, he⟩, hc⟩ := (OctagonalDescent.rareDistances_spec y hyinj r).mp hr
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨(a, b), by simp [hab], (heq a b r).mp he⟩, hg r ▸ hc⟩
  have hc : (OctagonalDescent.rareDistances y).card ≤ (rareDistances x).card := by
    have hh := Finset.card_le_card hsub
    rwa [Finset.card_image_of_injective _ hf] at hh
  exact (OctagonalDescent.card_le_pow_rareDistances y hyinj).trans
    (Nat.pow_le_pow_right (by decide) hc)

open Classical in
theorem card_le_pow_rareDistances (x : V → ℂ) (hx : Function.Injective x)
    (h : QuadraticCoordinates x) : Fintype.card V ≤ 2 ^ (rareDistances x).card := by
  obtain ⟨B, hB, y, hy⟩ := clear_coordinates x h
  exact card_le_pow_of_scaled_integer x hx B hB y hy

open Classical in
theorem two_rare_classes (x : V → ℂ) (hx : Function.Injective x)
    (h : QuadraticCoordinates x) (hn : 3 ≤ Fintype.card V) : 2 ≤ (rareDistances x).card := by
  have hb := card_le_pow_rareDistances x hx h
  by_contra hc
  have he : (rareDistances x).card = 0 ∨ (rareDistances x).card = 1 := by omega
  rcases he with he|he <;> simp [he] at hb <;> omega

open Classical in
theorem uniform_divergence (k : ℕ) : ∃ N : ℕ, ∀ {V : Type*} [Fintype V]
    (x : V → ℂ), Function.Injective x → QuadraticCoordinates x → N ≤ Fintype.card V →
      k ≤ (rareDistances x).card := by
  refine ⟨2 ^ k, ?_⟩
  intro V inst x hx h hn
  have hb := card_le_pow_rareDistances x hx h
  by_contra hc
  have hp : 2 ^ (rareDistances x).card < 2 ^ k := Nat.pow_lt_pow_right (by decide) (by omega)
  omega

open Classical in
theorem rareDistances_spec (x : V → ℂ) (hx : Function.Injective x) (d : ℝ) :
    d ∈ rareDistances x ↔ 0 < d ∧ (∃ a b, a ≠ b ∧ dist (x a) (x b) = d) ∧
      (graph x d).edgeFinset.card ≤ Fintype.card V := by
  constructor
  · intro h
    obtain ⟨hp, hc⟩ := Finset.mem_filter.mp h
    obtain ⟨⟨a, b⟩, hab, he⟩ := Finset.mem_image.mp hp
    have hn := (Finset.mem_offDiag.mp hab).2.2
    exact ⟨he ▸ dist_pos.mpr (hx.ne hn), ⟨a, b, hn, he⟩, hc⟩
  · rintro ⟨_, ⟨a, b, hab, he⟩, hc⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(a, b), by simp [hab], he⟩, hc⟩

end
end LeanPool.RareDistanceFields.OctagonalRational
