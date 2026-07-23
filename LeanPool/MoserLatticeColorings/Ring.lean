/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/

import LeanPool.MoserLatticeColorings.Basic

/-!
# Extension to the Moser ring

Dúcz observes that both geometric four-colorings of the Moser lattice extend
to its multiplicative closure, the Moser ring. This file constructs the ring
as localization-by-three representatives modulo equal Euclidean embeddings,
proves that both colorings descend, and proves their properness and
geometricity on the quotient.

As a search consequence, every unit-distance graph realized entirely in the
Moser ring is four-colorable. This rules out Moser-ring-only searches for a
six-chromatic witness, but it does not determine the chromatic number of the
plane.
-/

namespace LeanPool.MoserLatticeColorings

/-- A representative `x / 3^k` of a point in the Moser ring, with `x` in
the integer-coordinate presentation of the Moser lattice. -/
structure RingRep where
  /-- The lattice numerator. -/
  coeff : Coeff
  /-- The exponent `k` in the denominator `3^k`. -/
  denomPow : ℕ
deriving DecidableEq

namespace RingRep

/-- The Euclidean embedding of a Moser-ring representative. -/
noncomputable def toR2 (p : RingRep) : R2 :=
  ((3 : ℝ) ^ p.denomPow)⁻¹ • p.coeff.toR2

/-- The first parity color of a representative. -/
def color (p : RingRep) : ZMod 2 × ZMod 2 := p.coeff.color

/-- The second parity color of a representative. -/
def colorTwo (p : RingRep) : ZMod 2 × ZMod 2 := p.coeff.colorTwo

/-- Common-denominator numerator of `p - q`. -/
def crossDiff (p q : RingRep) : Coeff :=
  (Coeff.scale ((3 : ℤ) ^ q.denomPow) p.coeff).sub
    (Coeff.scale ((3 : ℤ) ^ p.denomPow) q.coeff)

lemma crossDiff_color_eq_zero_iff (p q : RingRep) :
    (p.crossDiff q).color = 0 ↔ p.color = q.color := by
  unfold crossDiff
  rw [Coeff.color_sub_eq_zero_iff, Coeff.color_scale_three_pow,
    Coeff.color_scale_three_pow]
  rfl

lemma crossDiff_colorTwo_eq_zero_iff (p q : RingRep) :
    Coeff.colorTwo (p.crossDiff q) = 0 ↔ p.colorTwo = q.colorTwo := by
  unfold crossDiff
  rw [Coeff.colorTwo_sub_eq_zero_iff, Coeff.colorTwo_scale_three_pow,
    Coeff.colorTwo_scale_three_pow]
  rfl

lemma crossDiff_toR2 (p q : RingRep) :
    (p.crossDiff q).toR2 =
      ((3 : ℝ) ^ (p.denomPow + q.denomPow)) • (p.toR2 - q.toR2) := by
  rw [crossDiff, Coeff.toR2_sub, Coeff.toR2_scale, Coeff.toR2_scale]
  ext i
  simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, toR2]
  have hp : (3 : ℝ) ^ p.denomPow ≠ 0 := pow_ne_zero _ (by norm_num)
  have hq : (3 : ℝ) ^ q.denomPow ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [Int.cast_pow, Int.cast_ofNat]
  field_simp
  ring_nf

lemma crossDiff_dist_zero (p q : RingRep) :
    dist (p.crossDiff q).toR2 0 =
      (3 : ℝ) ^ (p.denomPow + q.denomPow) * dist p.toR2 q.toR2 := by
  rw [crossDiff_toR2]
  calc
    dist (((3 : ℝ) ^ (p.denomPow + q.denomPow)) • (p.toR2 - q.toR2)) 0 =
        dist (((3 : ℝ) ^ (p.denomPow + q.denomPow)) • (p.toR2 - q.toR2))
          (((3 : ℝ) ^ (p.denomPow + q.denomPow)) • 0) := by simp
    _ = ‖(3 : ℝ) ^ (p.denomPow + q.denomPow)‖ *
          dist (p.toR2 - q.toR2) 0 := dist_smul₀ _ _ _
    _ = (3 : ℝ) ^ (p.denomPow + q.denomPow) * dist p.toR2 q.toR2 := by
      rw [Real.norm_of_nonneg (by positivity)]
      simp [dist_eq_norm]

lemma scaled_norm_coordinates_eq_of_dist_eq
    {p q r s : RingRep} (h : dist p.toR2 q.toR2 = dist r.toR2 s.toR2) :
    (3 : ℤ) ^ (2 * (r.denomPow + s.denomPow)) *
          (p.crossDiff q).normRational =
        (3 : ℤ) ^ (2 * (p.denomPow + q.denomPow)) *
          (r.crossDiff s).normRational ∧
      (3 : ℤ) ^ (2 * (r.denomPow + s.denomPow)) *
          (p.crossDiff q).normRadical =
        (3 : ℤ) ^ (2 * (p.denomPow + q.denomPow)) *
          (r.crossDiff s).normRadical := by
  have hpdist := crossDiff_dist_zero p q
  have hrdist := crossDiff_dist_zero r s
  have hpsq := Coeff.dist_sq (p.crossDiff q) Coeff.zero
  have hrsq := Coeff.dist_sq (r.crossDiff s) Coeff.zero
  rw [Coeff.toR2_zero_coeff, Coeff.sub_zero] at hpsq hrsq
  have hscaled :
      ((3 : ℝ) ^ (r.denomPow + s.denomPow)) ^ 2 *
          (((p.crossDiff q).normRational : ℝ) / 6 +
            ((p.crossDiff q).normRadical : ℝ) * Real.sqrt 33 / 6) =
        ((3 : ℝ) ^ (p.denomPow + q.denomPow)) ^ 2 *
          (((r.crossDiff s).normRational : ℝ) / 6 +
            ((r.crossDiff s).normRadical : ℝ) * Real.sqrt 33 / 6) := by
    rw [← hpsq, ← hrsq, hpdist, hrdist, h]
    ring
  have hradical :
      (((3 : ℤ) ^ (2 * (r.denomPow + s.denomPow)) *
          (p.crossDiff q).normRational : ℤ) : ℝ) +
        (((3 : ℤ) ^ (2 * (r.denomPow + s.denomPow)) *
          (p.crossDiff q).normRadical : ℤ) : ℝ) * Real.sqrt 33 =
      (((3 : ℤ) ^ (2 * (p.denomPow + q.denomPow)) *
          (r.crossDiff s).normRational : ℤ) : ℝ) +
        (((3 : ℤ) ^ (2 * (p.denomPow + q.denomPow)) *
          (r.crossDiff s).normRadical : ℤ) : ℝ) * Real.sqrt 33 := by
    push_cast
    rw [show ((3 : ℝ) ^ (r.denomPow + s.denomPow)) ^ 2 =
        3 ^ (2 * (r.denomPow + s.denomPow)) by rw [← pow_mul, Nat.mul_comm],
      show ((3 : ℝ) ^ (p.denomPow + q.denomPow)) ^ 2 =
        3 ^ (2 * (p.denomPow + q.denomPow)) by rw [← pow_mul, Nat.mul_comm]] at hscaled
    nlinarith
  exact Coeff.radical_coordinates_unique hradical

lemma dvd_four_iff_of_scaled_eq {x y : ℤ} {m n : ℕ}
    (h : (3 : ℤ) ^ (2 * m) * x = (3 : ℤ) ^ (2 * n) * y) :
    (4 : ℤ) ∣ x ↔ (4 : ℤ) ∣ y := by
  have hcast := congrArg (fun z : ℤ => (z : ZMod 4)) h
  push_cast at hcast
  have hm : (3 : ZMod 4) ^ (2 * m) = 1 := by
    rw [pow_mul, show (3 : ZMod 4) ^ 2 = 1 by decide]
    simp
  have hn : (3 : ZMod 4) ^ (2 * n) = 1 := by
    rw [pow_mul, show (3 : ZMod 4) ^ 2 = 1 by decide]
    simp
  have hxy : (x : ZMod 4) = (y : ZMod 4) := by
    simpa [hm, hn] using hcast
  constructor
  · intro hx
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd y 4).mp
    rw [← hxy]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 4).mpr hx
  · intro hy
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd x 4).mp
    rw [hxy]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd y 4).mpr hy

/-- Geometricity for a coloring on Moser-ring representatives. -/
def IsGeometricColoring {κ : Type*} (f : RingRep → κ) : Prop :=
  ∀ p q r s : RingRep,
    dist p.toR2 q.toR2 = dist r.toR2 s.toR2 →
      (f p = f q ↔ f r = f s)

theorem color_isGeometric : IsGeometricColoring color := by
  intro p q r s hdist
  have hcoords := scaled_norm_coordinates_eq_of_dist_eq hdist
  have hsum :
      (3 : ℤ) ^ (2 * (r.denomPow + s.denomPow)) *
          ((p.crossDiff q).normRational + (p.crossDiff q).normRadical) =
        (3 : ℤ) ^ (2 * (p.denomPow + q.denomPow)) *
          ((r.crossDiff s).normRational + (r.crossDiff s).normRadical) := by
    linear_combination hcoords.1 + hcoords.2
  rw [← crossDiff_color_eq_zero_iff p q, ← crossDiff_color_eq_zero_iff r s,
    Coeff.color_eq_zero_iff_norm_sum_dvd_four,
    Coeff.color_eq_zero_iff_norm_sum_dvd_four]
  exact dvd_four_iff_of_scaled_eq hsum

theorem colorTwo_isGeometric : IsGeometricColoring colorTwo := by
  intro p q r s hdist
  have hcoords := scaled_norm_coordinates_eq_of_dist_eq hdist
  have hdiff :
      (3 : ℤ) ^ (2 * (r.denomPow + s.denomPow)) *
          ((p.crossDiff q).normRational - (p.crossDiff q).normRadical) =
        (3 : ℤ) ^ (2 * (p.denomPow + q.denomPow)) *
          ((r.crossDiff s).normRational - (r.crossDiff s).normRadical) := by
    linear_combination hcoords.1 - hcoords.2
  rw [← crossDiff_colorTwo_eq_zero_iff p q,
    ← crossDiff_colorTwo_eq_zero_iff r s,
    Coeff.colorTwo_eq_zero_iff_norm_diff_dvd_four,
    Coeff.colorTwo_eq_zero_iff_norm_diff_dvd_four]
  exact dvd_four_iff_of_scaled_eq hdiff

lemma sqNorm_coefficients_of_int {p : Coeff} {t : ℤ}
    (h : ((p.normRational : ℝ) + (p.normRadical : ℝ) * Real.sqrt 33) / 6 = t) :
    p.normRational = 6 * t ∧ p.normRadical = 0 := by
  have hcoords := Coeff.radical_coordinates_unique
    (a := p.normRational) (b := p.normRadical) (c := 6 * t) (d := 0) (by
      push_cast
      linarith)
  simpa using hcoords

lemma crossDiff_norm_coefficients_of_dist_eq_one {p q : RingRep}
    (h : dist p.toR2 q.toR2 = 1) :
    (p.crossDiff q).normRational =
        6 * (3 : ℤ) ^ (2 * (p.denomPow + q.denomPow)) ∧
      (p.crossDiff q).normRadical = 0 := by
  have hdist := crossDiff_dist_zero p q
  rw [h] at hdist
  simp only [mul_one] at hdist
  have hsq := Coeff.dist_sq (p.crossDiff q) Coeff.zero
  rw [Coeff.toR2_zero_coeff, Coeff.sub_zero] at hsq
  have hvalue : (((p.crossDiff q).normRational : ℝ) +
      ((p.crossDiff q).normRadical : ℝ) * Real.sqrt 33) / 6 =
        ((3 : ℤ) ^ (2 * (p.denomPow + q.denomPow)) : ℤ) := by
    have hpow : ((3 : ℝ) ^ (p.denomPow + q.denomPow)) ^ 2 =
        ((3 : ℤ) ^ (2 * (p.denomPow + q.denomPow)) : ℤ) := by
      push_cast
      ring
    rw [hdist] at hsq
    rw [hpow] at hsq
    linarith
  exact sqNorm_coefficients_of_int hvalue

lemma color_ne_of_dist_eq_one {p q : RingRep} (h : dist p.toR2 q.toR2 = 1) :
    p.color ≠ q.color := by
  intro heq
  have hzero := (crossDiff_color_eq_zero_iff p q).2 heq
  have hdiv := (Coeff.color_eq_zero_iff_norm_sum_dvd_four _).1 hzero
  have hcoeff := crossDiff_norm_coefficients_of_dist_eq_one h
  rw [hcoeff.1, hcoeff.2] at hdiv
  have hzmod := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 hdiv
  have hnine : (9 : ZMod 4) = 1 := by decide
  have hsix : (6 : ZMod 4) ≠ 0 := by decide
  apply hsix
  simpa [pow_mul, hnine] using hzmod

lemma colorTwo_ne_of_dist_eq_one {p q : RingRep} (h : dist p.toR2 q.toR2 = 1) :
    p.colorTwo ≠ q.colorTwo := by
  intro heq
  have hzero := (crossDiff_colorTwo_eq_zero_iff p q).2 heq
  have hdiv := (Coeff.colorTwo_eq_zero_iff_norm_diff_dvd_four _).1 hzero
  have hcoeff := crossDiff_norm_coefficients_of_dist_eq_one h
  rw [hcoeff.1, hcoeff.2] at hdiv
  have hzmod := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).2 hdiv
  have hnine : (9 : ZMod 4) = 1 := by decide
  have hsix : (6 : ZMod 4) ≠ 0 := by decide
  apply hsix
  simpa [pow_mul, hnine] using hzmod

lemma norm_coefficients_of_toR2_eq {p q : RingRep} (h : p.toR2 = q.toR2) :
    (p.crossDiff q).normRational = 0 ∧ (p.crossDiff q).normRadical = 0 := by
  have hdist : dist p.toR2 q.toR2 = 0 := by rw [h]; simp
  have hcross := crossDiff_dist_zero p q
  rw [hdist, mul_zero] at hcross
  have hsq := Coeff.dist_sq (p.crossDiff q) Coeff.zero
  rw [Coeff.toR2_zero_coeff, Coeff.sub_zero, hcross] at hsq
  norm_num at hsq
  exact sqNorm_coefficients_of_int (t := 0) (by
    nlinarith)

lemma color_eq_of_toR2_eq {p q : RingRep} (h : p.toR2 = q.toR2) :
    p.color = q.color := by
  have hcoeff := norm_coefficients_of_toR2_eq h
  apply (crossDiff_color_eq_zero_iff p q).1
  apply (Coeff.color_eq_zero_iff_norm_sum_dvd_four _).2
  rw [hcoeff.1, hcoeff.2]
  norm_num

lemma colorTwo_eq_of_toR2_eq {p q : RingRep} (h : p.toR2 = q.toR2) :
    p.colorTwo = q.colorTwo := by
  have hcoeff := norm_coefficients_of_toR2_eq h
  apply (crossDiff_colorTwo_eq_zero_iff p q).1
  apply (Coeff.colorTwo_eq_zero_iff_norm_diff_dvd_four _).2
  rw [hcoeff.1, hcoeff.2]
  norm_num

end RingRep

/-- Representatives are identified precisely when they embed as the same
point of the Euclidean plane. -/
def moserRingSetoid : Setoid RingRep where
  r p q := p.toR2 = q.toR2
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- The Moser ring
`{(a + bω₁ + cω₃ + dω₁ω₃) / 3^k : a, b, c, d ∈ ℤ, k ∈ ℕ}`,
quotiented by equality of Euclidean embeddings. -/
def MoserRing := Quotient moserRingSetoid

namespace MoserRing

/-- The well-defined Euclidean embedding of the Moser ring. -/
noncomputable def toR2 : MoserRing → R2 :=
  Quotient.lift RingRep.toR2 fun _ _ h => h

/-- Dúcz's first parity color, descended to the Moser ring. -/
def color : MoserRing → ZMod 2 × ZMod 2 :=
  Quotient.lift RingRep.color fun _ _ h => RingRep.color_eq_of_toR2_eq h

/-- Dúcz's second parity color, descended to the Moser ring. -/
def colorTwo : MoserRing → ZMod 2 × ZMod 2 :=
  Quotient.lift RingRep.colorTwo fun _ _ h => RingRep.colorTwo_eq_of_toR2_eq h

theorem toR2_injective : Function.Injective toR2 := by
  intro p q
  refine Quotient.inductionOn₂ p q ?_
  intro p q h
  exact Quotient.sound h

@[simp] lemma out_toR2 (p : MoserRing) :
    (Quotient.out p : RingRep).toR2 = p.toR2 := by
  change toR2 ⟦Quotient.out p⟧ = toR2 p
  exact congrArg toR2 (Quotient.out_eq p)

@[simp] lemma out_color (p : MoserRing) :
    (Quotient.out p : RingRep).color = p.color := by
  change color ⟦Quotient.out p⟧ = color p
  exact congrArg color (Quotient.out_eq p)

/-- A coloring of the Moser ring is geometric when pairwise color equality
depends only on Euclidean distance. -/
def IsGeometricColoring {κ : Type*} (f : MoserRing → κ) : Prop :=
  ∀ p q r s : MoserRing,
    dist p.toR2 q.toR2 = dist r.toR2 s.toR2 →
      (f p = f q ↔ f r = f s)

theorem color_isGeometric : IsGeometricColoring color := by
  intro p q r s
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  refine Quotient.inductionOn r ?_
  intro r
  refine Quotient.inductionOn s ?_
  intro s h
  exact RingRep.color_isGeometric p q r s h

theorem colorTwo_isGeometric : IsGeometricColoring colorTwo := by
  intro p q r s
  refine Quotient.inductionOn p ?_
  intro p
  refine Quotient.inductionOn q ?_
  intro q
  refine Quotient.inductionOn r ?_
  intro r
  refine Quotient.inductionOn s ?_
  intro s h
  exact RingRep.colorTwo_isGeometric p q r s h

/-- Unit-distance graph induced by the entire Moser ring. -/
def unitDistanceGraph : SimpleGraph MoserRing :=
  SimpleGraph.fromRel fun p q => dist p.toR2 q.toR2 = 1

/-- The first parity map as a proper four-coloring of the Moser ring. -/
noncomputable def coloring : unitDistanceGraph.Coloring (ZMod 2 × ZMod 2) :=
  SimpleGraph.Coloring.mk color fun {p q} h => by
    unfold unitDistanceGraph at h
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with hpq | hqp
    · revert hpq
      refine Quotient.inductionOn₂ p q ?_
      intro p q hpq
      exact RingRep.color_ne_of_dist_eq_one hpq
    · revert hqp
      refine Quotient.inductionOn₂ p q ?_
      intro p q hqp
      exact RingRep.color_ne_of_dist_eq_one (dist_comm q.toR2 p.toR2 ▸ hqp)

/-- The second parity map as a proper four-coloring of the Moser ring. -/
noncomputable def coloringTwo : unitDistanceGraph.Coloring (ZMod 2 × ZMod 2) :=
  SimpleGraph.Coloring.mk colorTwo fun {p q} h => by
    unfold unitDistanceGraph at h
    rw [SimpleGraph.fromRel_adj] at h
    rcases h.2 with hpq | hqp
    · revert hpq
      refine Quotient.inductionOn₂ p q ?_
      intro p q hpq
      exact RingRep.colorTwo_ne_of_dist_eq_one hpq
    · revert hqp
      refine Quotient.inductionOn₂ p q ?_
      intro p q hqp
      exact RingRep.colorTwo_ne_of_dist_eq_one (dist_comm q.toR2 p.toR2 ▸ hqp)

theorem colorable_four : unitDistanceGraph.Colorable 4 := by
  simpa using coloring.colorable

/-- Both explicit proper four-colorings of the Moser ring are geometric. -/
theorem both_colorings_are_geometric :
    IsGeometricColoring coloring ∧ IsGeometricColoring coloringTwo := by
  constructor
  · change IsGeometricColoring color
    exact color_isGeometric
  · change IsGeometricColoring colorTwo
    exact colorTwo_isGeometric

/-- Every graph whose vertices are realized in the Moser ring and whose edges
have Euclidean length one is four-colorable. -/
theorem graph_colorable_four_of_moserRing_realization
    {V : Type*} (G : SimpleGraph V) (f : V → MoserRing)
    (hedge : ∀ {v w : V}, G.Adj v w → dist (f v).toR2 (f w).toR2 = 1) :
    G.Colorable 4 := by
  let C : G.Coloring (ZMod 2 × ZMod 2) :=
    SimpleGraph.Coloring.mk (fun v => color (f v)) fun {v w} h => by
      simpa only [out_color] using
        RingRep.color_ne_of_dist_eq_one (p := Quotient.out (f v))
        (q := Quotient.out (f w)) (by
          simpa only [out_toR2] using hedge h)
  simpa using C.colorable

end MoserRing

end LeanPool.MoserLatticeColorings
