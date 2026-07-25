/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.Erdos132N14.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The three classified thirteen-point templates

The regular tridecagon is constructed from the canonical primitive thirteenth
root of unity. Its centroid, second harmonic, isotropy, chord classes, and
distance moments are derived from those coordinates. The centered dodecagon
and centered regular hexagram are also given by explicit complex coordinates;
their high-multiplicity classes are checked inside Lean.
-/

namespace LeanPool.Erdos132N14

open scoped BigOperators ComplexConjugate

noncomputable section

/-- The canonical primitive thirteenth root of unity. -/
def regularThirteenRoot : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 13)

theorem regularThirteenRoot_isPrimitive :
    IsPrimitiveRoot regularThirteenRoot 13 := by
  exact Complex.isPrimitiveRoot_exp 13 (by norm_num)

theorem norm_regularThirteenRoot : ‖regularThirteenRoot‖ = 1 := by
  rw [regularThirteenRoot, Complex.norm_exp]
  norm_num

/-- Unit-circumradius regular-tridecagon coordinates. -/
def regularTridecagonPoint (i : Fin 13) : ℂ :=
  regularThirteenRoot ^ i.val

theorem regularTridecagonPoint_injective :
    Function.Injective regularTridecagonPoint := by
  intro i j hij
  apply Fin.ext
  exact regularThirteenRoot_isPrimitive.pow_inj i.isLt j.isLt hij

/-- The regular tridecagon as a labelled planar configuration. -/
def regularTridecagon : Configuration (Fin 13) where
  point := regularTridecagonPoint
  injective := regularTridecagonPoint_injective

theorem norm_regularTridecagonPoint (i : Fin 13) :
    ‖regularTridecagonPoint i‖ = 1 := by
  simp [regularTridecagonPoint, norm_regularThirteenRoot]

theorem normSq_regularTridecagonPoint (i : Fin 13) :
    Complex.normSq (regularTridecagonPoint i) = 1 := by
  rw [← Complex.sq_norm, norm_regularTridecagonPoint]
  norm_num

/-- The regular tridecagon is centered at the origin. -/
theorem sum_regularTridecagonPoint :
    ∑ i : Fin 13, regularTridecagonPoint i = 0 := by
  rw [show (∑ i : Fin 13, regularTridecagonPoint i) =
      ∑ i ∈ Finset.range 13, regularThirteenRoot ^ i by
    simpa [regularTridecagonPoint] using
      (Fin.sum_univ_eq_sum_range (fun i ↦ regularThirteenRoot ^ i) 13)]
  exact regularThirteenRoot_isPrimitive.geom_sum_eq_zero (by norm_num)

/-- Its second complex harmonic also vanishes. -/
theorem sum_regularTridecagonPoint_sq :
    ∑ i : Fin 13, regularTridecagonPoint i ^ 2 = 0 := by
  have hprimitiveSquare :=
    regularThirteenRoot_isPrimitive.pow_of_coprime 2 (by decide)
  rw [show (∑ i : Fin 13, regularTridecagonPoint i ^ 2) =
      ∑ i : Fin 13, (regularThirteenRoot ^ 2) ^ i.val by
    apply Finset.sum_congr rfl
    intro i _
    simp only [regularTridecagonPoint]
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega]
  rw [Fin.sum_univ_eq_sum_range]
  exact hprimitiveSquare.geom_sum_eq_zero (by norm_num)

/-- The real Euclidean scalar product on complex coordinates. -/
def planeDot (x y : ℂ) : ℝ :=
  x.re * y.re + x.im * y.im

theorem normSq_sub (x y : ℂ) :
    Complex.normSq (x - y) =
      Complex.normSq x + Complex.normSq y - 2 * planeDot x y := by
  simp [Complex.normSq_apply, planeDot]
  ring

/-- The regular tridecagon is a unit tight frame with frame constant `13 / 2`. -/
theorem regularTridecagon_isotropy (v : ℂ) :
    ∑ i : Fin 13, planeDot v (regularTridecagonPoint i) ^ 2 =
      (13 / 2 : ℝ) * Complex.normSq v := by
  have hunit :
      ∑ i : Fin 13,
          ((regularTridecagonPoint i).re ^ 2 +
            (regularTridecagonPoint i).im ^ 2) = 13 := by
    calc
      ∑ i : Fin 13,
          ((regularTridecagonPoint i).re ^ 2 +
            (regularTridecagonPoint i).im ^ 2) =
          ∑ _i : Fin 13, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa [Complex.normSq_apply, pow_two] using normSq_regularTridecagonPoint i
      _ = 13 := by norm_num
  have hsquareRe :
      ∑ i : Fin 13,
          ((regularTridecagonPoint i).re ^ 2 -
            (regularTridecagonPoint i).im ^ 2) = 0 := by
    have h := congrArg Complex.re sum_regularTridecagonPoint_sq
    simpa [map_sum, Complex.mul_re, pow_two] using h
  have hsquareIm :
      ∑ i : Fin 13,
          2 * (regularTridecagonPoint i).re *
            (regularTridecagonPoint i).im = 0 := by
    have h : ∑ i : Fin 13, (regularTridecagonPoint i ^ 2).im = 0 := by
      simpa [map_sum] using congrArg Complex.im sum_regularTridecagonPoint_sq
    calc
      ∑ i : Fin 13,
          2 * (regularTridecagonPoint i).re *
            (regularTridecagonPoint i).im =
          ∑ i : Fin 13, (regularTridecagonPoint i ^ 2).im := by
        apply Finset.sum_congr rfl
        intro i _
        simp [Complex.mul_im, pow_two]
        ring
      _ = 0 := h
  have hreSq :
      ∑ i : Fin 13, (regularTridecagonPoint i).re ^ 2 = (13 / 2 : ℝ) := by
    rw [Finset.sum_sub_distrib] at hsquareRe
    rw [Finset.sum_add_distrib] at hunit
    linarith
  have himSq :
      ∑ i : Fin 13, (regularTridecagonPoint i).im ^ 2 = (13 / 2 : ℝ) := by
    rw [Finset.sum_sub_distrib] at hsquareRe
    rw [Finset.sum_add_distrib] at hunit
    linarith
  have hreIm :
      ∑ i : Fin 13,
          (regularTridecagonPoint i).re * (regularTridecagonPoint i).im = 0 := by
    have htwo :
        2 * ∑ i : Fin 13,
          (regularTridecagonPoint i).re * (regularTridecagonPoint i).im = 0 := by
      rw [Finset.mul_sum]
      simpa [mul_assoc] using hsquareIm
    linarith
  calc
    ∑ i : Fin 13, planeDot v (regularTridecagonPoint i) ^ 2 =
        v.re ^ 2 * ∑ i : Fin 13, (regularTridecagonPoint i).re ^ 2 +
        2 * v.re * v.im *
          ∑ i : Fin 13,
            (regularTridecagonPoint i).re * (regularTridecagonPoint i).im +
        v.im ^ 2 * ∑ i : Fin 13, (regularTridecagonPoint i).im ^ 2 := by
      calc
        ∑ i : Fin 13, planeDot v (regularTridecagonPoint i) ^ 2 =
            ∑ i : Fin 13,
              (v.re ^ 2 * (regularTridecagonPoint i).re ^ 2 +
                2 * v.re * v.im *
                  ((regularTridecagonPoint i).re *
                    (regularTridecagonPoint i).im) +
                v.im ^ 2 * (regularTridecagonPoint i).im ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [planeDot]
          ring
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = (13 / 2 : ℝ) * Complex.normSq v := by
      rw [hreSq, himSq, hreIm]
      simp [Complex.normSq_apply]
      ring

/-- Sum of squared distances from an arbitrary point to the unit tridecagon. -/
theorem regularTridecagon_second_moment (v : ℂ) :
    ∑ i : Fin 13, Complex.normSq (v - regularTridecagonPoint i) =
      13 * (Complex.normSq v + 1) := by
  have hdot : ∑ i : Fin 13, planeDot v (regularTridecagonPoint i) = 0 := by
    calc
      ∑ i : Fin 13, planeDot v (regularTridecagonPoint i) =
          planeDot v (∑ i : Fin 13, regularTridecagonPoint i) := by
        simp [planeDot, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 0 := by rw [sum_regularTridecagonPoint]; simp [planeDot]
  calc
    ∑ i : Fin 13, Complex.normSq (v - regularTridecagonPoint i) =
        ∑ i : Fin 13, (Complex.normSq v + 1 -
          2 * planeDot v (regularTridecagonPoint i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [normSq_sub, normSq_regularTridecagonPoint]
    _ = 13 * (Complex.normSq v + 1) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum, hdot]
      ring

/-- Sum of fourth powers of distances from an arbitrary point to the tridecagon. -/
theorem regularTridecagon_fourth_moment (v : ℂ) :
    ∑ i : Fin 13, Complex.normSq (v - regularTridecagonPoint i) ^ 2 =
      13 * (Complex.normSq v ^ 2 + 4 * Complex.normSq v + 1) := by
  have hdot : ∑ i : Fin 13, planeDot v (regularTridecagonPoint i) = 0 := by
    calc
      ∑ i : Fin 13, planeDot v (regularTridecagonPoint i) =
          planeDot v (∑ i : Fin 13, regularTridecagonPoint i) := by
        simp [planeDot, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = 0 := by rw [sum_regularTridecagonPoint]; simp [planeDot]
  calc
    ∑ i : Fin 13, Complex.normSq (v - regularTridecagonPoint i) ^ 2 =
        ∑ i : Fin 13,
          ((Complex.normSq v + 1) ^ 2 -
            4 * (Complex.normSq v + 1) *
              planeDot v (regularTridecagonPoint i) +
            4 * planeDot v (regularTridecagonPoint i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [normSq_sub, normSq_regularTridecagonPoint]
      ring
    _ = 13 * (Complex.normSq v ^ 2 + 4 * Complex.normSq v + 1) := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← Finset.mul_sum, hdot, regularTridecagon_isotropy]
      ring

theorem normSq_regularThirteenRoot_pow (n : ℕ) :
    Complex.normSq (regularThirteenRoot ^ n) = 1 := by
  rw [← Complex.sq_norm, norm_pow, norm_regularThirteenRoot]
  simp

/-- The six chord lengths, indexed by cyclic gaps `1, ..., 6`. -/
def regularTridecagonChord (k : Fin 6) : ℝ :=
  dist 1 (regularThirteenRoot ^ (k.val + 1))

private theorem dist_one_root_pow_sq (n : ℕ) :
    dist 1 (regularThirteenRoot ^ n) ^ 2 =
      2 - 2 * (regularThirteenRoot ^ n).re := by
  rw [Complex.dist_eq, Complex.sq_norm]
  have hunit := normSq_regularThirteenRoot_pow n
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im]
  rw [Complex.normSq_apply] at hunit
  nlinarith

private theorem regularChord_pow_eq_or_product_eq_one
    {a b : ℕ}
    (hdistance : dist 1 (regularThirteenRoot ^ a) =
      dist 1 (regularThirteenRoot ^ b)) :
    regularThirteenRoot ^ a = regularThirteenRoot ^ b ∨
      regularThirteenRoot ^ a * regularThirteenRoot ^ b = 1 := by
  let x := regularThirteenRoot ^ a
  let y := regularThirteenRoot ^ b
  have hreal : x.re = y.re := by
    have hsquare := congrArg (· ^ 2) hdistance
    rw [dist_one_root_pow_sq, dist_one_root_pow_sq] at hsquare
    nlinarith
  have himSquare : x.im ^ 2 = y.im ^ 2 := by
    have hx := normSq_regularThirteenRoot_pow a
    have hy := normSq_regularThirteenRoot_pow b
    simp only [Complex.normSq_apply] at hx hy
    change x.re * x.re + x.im * x.im = 1 at hx
    change y.re * y.re + y.im * y.im = 1 at hy
    simp only [pow_two]
    rw [hreal] at hx
    nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp himSquare with him | him
  · left
    exact Complex.ext hreal him
  · right
    have hxy : x = conj y := by
      exact Complex.ext (by simpa using hreal) (by simpa using him)
    change x * y = 1
    rw [hxy, mul_comm]
    have hyunit : Complex.normSq y = 1 := by
      exact normSq_regularThirteenRoot_pow b
    simpa [hyunit] using Complex.mul_conj y

theorem regularTridecagonChord_injective :
    Function.Injective regularTridecagonChord := by
  intro k l hkl
  rcases regularChord_pow_eq_or_product_eq_one hkl with hpowers | hproduct
  · apply Fin.ext
    have hexponents := regularThirteenRoot_isPrimitive.pow_inj
      (show k.val + 1 < 13 by omega) (show l.val + 1 < 13 by omega) hpowers
    omega
  · have hone : regularThirteenRoot ^ (k.val + 1 + (l.val + 1)) = 1 := by
      rw [pow_add]
      exact hproduct
    have hdivides :=
      (regularThirteenRoot_isPrimitive.pow_eq_one_iff_dvd _).mp hone
    omega

private theorem regularTridecagon_pairDistance_eq_gap
    {i j : Fin 13} (hij : i < j) :
    regularTridecagon.pairDistance (i, j) =
      dist 1 (regularThirteenRoot ^ (j.val - i.val)) := by
  rw [Configuration.pairDistance, Complex.dist_eq, Complex.dist_eq]
  let gap := j.val - i.val
  change ‖regularThirteenRoot ^ i.val - regularThirteenRoot ^ j.val‖ =
    ‖1 - regularThirteenRoot ^ gap‖
  have hj : j.val = i.val + gap := by
    dsimp [gap]
    omega
  have hfactor :
      regularThirteenRoot ^ i.val - regularThirteenRoot ^ j.val =
        regularThirteenRoot ^ i.val *
          (1 - regularThirteenRoot ^ gap) := by
    rw [hj, pow_add]
    ring
  rw [hfactor, norm_mul]
  simp [norm_pow, norm_regularThirteenRoot]

private theorem dist_one_root_pow_eq_of_sum_eq_thirteen
    {a b : ℕ} (hsum : a + b = 13) :
    dist 1 (regularThirteenRoot ^ a) =
      dist 1 (regularThirteenRoot ^ b) := by
  have hproduct : regularThirteenRoot ^ a * regularThirteenRoot ^ b = 1 := by
    rw [← pow_add, hsum]
    exact regularThirteenRoot_isPrimitive.pow_eq_one
  have halgebra :
      regularThirteenRoot ^ b * (1 - regularThirteenRoot ^ a) =
        -(1 - regularThirteenRoot ^ b) := by
    calc
      regularThirteenRoot ^ b * (1 - regularThirteenRoot ^ a) =
          regularThirteenRoot ^ b -
            regularThirteenRoot ^ b * regularThirteenRoot ^ a := by ring
      _ = regularThirteenRoot ^ b - 1 := by rw [mul_comm, hproduct]
      _ = -(1 - regularThirteenRoot ^ b) := by ring
  rw [Complex.dist_eq, Complex.dist_eq]
  calc
    ‖1 - regularThirteenRoot ^ a‖ =
        ‖regularThirteenRoot ^ b‖ * ‖1 - regularThirteenRoot ^ a‖ := by
      simp [norm_pow, norm_regularThirteenRoot]
    _ = ‖regularThirteenRoot ^ b * (1 - regularThirteenRoot ^ a)‖ := by
      rw [norm_mul]
    _ = ‖-(1 - regularThirteenRoot ^ b)‖ := by
      rw [halgebra]
    _ = ‖1 - regularThirteenRoot ^ b‖ := norm_neg _

theorem normSq_one_root_pow_eq_of_sum_eq_thirteen
    {a b : ℕ} (hsum : a + b = 13) :
    Complex.normSq (1 - regularThirteenRoot ^ a) =
      Complex.normSq (1 - regularThirteenRoot ^ b) := by
  have h := congrArg (fun x : ℝ ↦ x ^ 2)
    (dist_one_root_pow_eq_of_sum_eq_thirteen hsum)
  rw [Complex.dist_eq, Complex.dist_eq, Complex.sq_norm, Complex.sq_norm] at h
  exact h

/-- Twice the sum of the six squared chord lengths. -/
theorem regularTridecagon_chord_second_sum :
    2 * (∑ k : Fin 6, regularTridecagonChord k ^ 2) = 26 := by
  have h12 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 12) (b := 1) (by omega)
  have h11 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 11) (b := 2) (by omega)
  have h10 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 10) (b := 3) (by omega)
  have h9 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 9) (b := 4) (by omega)
  have h8 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 8) (b := 5) (by omega)
  have h7 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 7) (b := 6) (by omega)
  have h := regularTridecagon_second_moment 1
  norm_num at h
  change (∑ i : Fin 13,
    Complex.normSq (1 - regularThirteenRoot ^ i.val)) = 26 at h
  rw [show (∑ i : Fin 13,
      Complex.normSq (1 - regularThirteenRoot ^ i.val)) =
      ∑ i ∈ Finset.range 13,
        Complex.normSq (1 - regularThirteenRoot ^ i) by
    simpa using Fin.sum_univ_eq_sum_range
      (fun i ↦ Complex.normSq (1 - regularThirteenRoot ^ i)) 13] at h
  norm_num [Finset.sum_range_succ] at h
  rw [show (∑ k : Fin 6, regularTridecagonChord k ^ 2) =
      ∑ k ∈ Finset.range 6,
        dist 1 (regularThirteenRoot ^ (k + 1)) ^ 2 by
    simpa [regularTridecagonChord] using Fin.sum_univ_eq_sum_range
      (fun k ↦ dist 1 (regularThirteenRoot ^ (k + 1)) ^ 2) 6]
  norm_num [Finset.sum_range_succ, regularTridecagonChord,
    Complex.dist_eq, Complex.sq_norm]
  rw [h7, h8, h9, h10, h11, h12] at h
  ring_nf at h ⊢
  exact h

/-- Twice the sum of the squares of the six squared chord lengths. -/
theorem regularTridecagon_chord_fourth_sum :
    2 * (∑ k : Fin 6, (regularTridecagonChord k ^ 2) ^ 2) = 78 := by
  have h12 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 12) (b := 1) (by omega)
  have h11 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 11) (b := 2) (by omega)
  have h10 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 10) (b := 3) (by omega)
  have h9 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 9) (b := 4) (by omega)
  have h8 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 8) (b := 5) (by omega)
  have h7 := normSq_one_root_pow_eq_of_sum_eq_thirteen
    (a := 7) (b := 6) (by omega)
  have h := regularTridecagon_fourth_moment 1
  norm_num at h
  change (∑ i : Fin 13,
    Complex.normSq (1 - regularThirteenRoot ^ i.val) ^ 2) = 78 at h
  rw [show (∑ i : Fin 13,
      Complex.normSq (1 - regularThirteenRoot ^ i.val) ^ 2) =
      ∑ i ∈ Finset.range 13,
        Complex.normSq (1 - regularThirteenRoot ^ i) ^ 2 by
    simpa using Fin.sum_univ_eq_sum_range
      (fun i ↦ Complex.normSq (1 - regularThirteenRoot ^ i) ^ 2) 13] at h
  norm_num [Finset.sum_range_succ] at h
  rw [show (∑ k : Fin 6, (regularTridecagonChord k ^ 2) ^ 2) =
      ∑ k ∈ Finset.range 6,
        (dist 1 (regularThirteenRoot ^ (k + 1)) ^ 2) ^ 2 by
    simpa [regularTridecagonChord] using Fin.sum_univ_eq_sum_range
      (fun k ↦ (dist 1 (regularThirteenRoot ^ (k + 1)) ^ 2) ^ 2) 6]
  norm_num [Finset.sum_range_succ, regularTridecagonChord,
    Complex.dist_eq, Complex.sq_norm]
  rw [h7, h8, h9, h10, h11, h12] at h
  ring_nf at h ⊢
  exact h

private theorem regularTridecagon_pairDistance_eq_chord_iff
    {i j : Fin 13} (hij : i < j) (k : Fin 6) :
    regularTridecagon.pairDistance (i, j) = regularTridecagonChord k ↔
      j.val - i.val = k.val + 1 ∨
        j.val - i.val = 13 - (k.val + 1) := by
  have hgapPos : 0 < j.val - i.val := by omega
  have hgapLt : j.val - i.val < 13 := by omega
  constructor
  · intro hdistance
    have hgapDistance :
        dist 1 (regularThirteenRoot ^ (j.val - i.val)) =
          dist 1 (regularThirteenRoot ^ (k.val + 1)) := by
      rw [← regularTridecagon_pairDistance_eq_gap hij]
      exact hdistance
    rcases regularChord_pow_eq_or_product_eq_one hgapDistance with hpowers | hproduct
    · left
      exact regularThirteenRoot_isPrimitive.pow_inj hgapLt
        (show k.val + 1 < 13 by omega) hpowers
    · right
      have hone : regularThirteenRoot ^ (j.val - i.val + (k.val + 1)) = 1 := by
        rw [pow_add]
        exact hproduct
      have hdivides :=
        (regularThirteenRoot_isPrimitive.pow_eq_one_iff_dvd _).mp hone
      omega
  · rintro (hgap | hgap)
    · rw [regularTridecagon_pairDistance_eq_gap hij, regularTridecagonChord, hgap]
    · rw [regularTridecagon_pairDistance_eq_gap hij, regularTridecagonChord]
      apply dist_one_root_pow_eq_of_sum_eq_thirteen
      omega

/-- Every one of the six regular-tridecagon chord lengths occurs on exactly
thirteen unordered vertex pairs. -/
theorem regularTridecagon_chord_multiplicity (k : Fin 6) :
    regularTridecagon.distanceMultiplicity Finset.univ
      (regularTridecagonChord k) = 13 := by
  rw [Configuration.distanceMultiplicity]
  have hfilter :
      (pairs (Finset.univ : Finset (Fin 13))).filter
          (fun e ↦ regularTridecagon.pairDistance e = regularTridecagonChord k) =
        (pairs (Finset.univ : Finset (Fin 13))).filter
          (fun e ↦ e.2.val - e.1.val = k.val + 1 ∨
            e.2.val - e.1.val = 13 - (k.val + 1)) := by
    apply Finset.filter_congr
    intro e he
    exact regularTridecagon_pairDistance_eq_chord_iff
      (Finset.mem_filter.mp he).2 k
  rw [hfilter]
  fin_cases k <;> decide

/-- Explicit coordinates for the regular dodecagon and its center. -/
def dodecagonWithCenterPoint (i : Fin 13) : ℂ :=
  match i.val with
  | 0 => ⟨0, 0⟩
  | 1 => ⟨1, 0⟩
  | 2 => ⟨Real.sqrt 3 / 2, 1 / 2⟩
  | 3 => ⟨1 / 2, Real.sqrt 3 / 2⟩
  | 4 => ⟨0, 1⟩
  | 5 => ⟨-1 / 2, Real.sqrt 3 / 2⟩
  | 6 => ⟨-Real.sqrt 3 / 2, 1 / 2⟩
  | 7 => ⟨-1, 0⟩
  | 8 => ⟨-Real.sqrt 3 / 2, -1 / 2⟩
  | 9 => ⟨-1 / 2, -Real.sqrt 3 / 2⟩
  | 10 => ⟨0, -1⟩
  | 11 => ⟨1 / 2, -Real.sqrt 3 / 2⟩
  | _ => ⟨Real.sqrt 3 / 2, -1 / 2⟩

theorem dodecagonWithCenterPoint_injective :
    Function.Injective dodecagonWithCenterPoint := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [dodecagonWithCenterPoint, Complex.ext_iff] at hij ⊢ <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)]

/-- The centered regular dodecagon template in the published classification. -/
def dodecagonWithCenter : Configuration (Fin 13) where
  point := dodecagonWithCenterPoint
  injective := dodecagonWithCenterPoint_injective

/-- Explicit coordinates for the twelve vertices of a regular hexagram and
its center. The outer radius is `√3` and the inner radius is `1`. -/
def hexagramWithCenterPoint (i : Fin 13) : ℂ :=
  match i.val with
  | 0 => ⟨0, 0⟩
  | 1 => ⟨Real.sqrt 3, 0⟩
  | 2 => ⟨Real.sqrt 3 / 2, 3 / 2⟩
  | 3 => ⟨-Real.sqrt 3 / 2, 3 / 2⟩
  | 4 => ⟨-Real.sqrt 3, 0⟩
  | 5 => ⟨-Real.sqrt 3 / 2, -3 / 2⟩
  | 6 => ⟨Real.sqrt 3 / 2, -3 / 2⟩
  | 7 => ⟨Real.sqrt 3 / 2, 1 / 2⟩
  | 8 => ⟨0, 1⟩
  | 9 => ⟨-Real.sqrt 3 / 2, 1 / 2⟩
  | 10 => ⟨-Real.sqrt 3 / 2, -1 / 2⟩
  | 11 => ⟨0, -1⟩
  | _ => ⟨Real.sqrt 3 / 2, -1 / 2⟩

theorem hexagramWithCenterPoint_injective :
    Function.Injective hexagramWithCenterPoint := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [hexagramWithCenterPoint, Complex.ext_iff] at hij ⊢ <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)]

/-- The centered regular-hexagram template in the published classification. -/
def hexagramWithCenter : Configuration (Fin 13) where
  point := hexagramWithCenterPoint
  injective := hexagramWithCenterPoint_injective

/-- The centered dodecagon has exactly twenty-four unit-distance pairs. -/
theorem dodecagonWithCenter_unit_distance_multiplicity :
    dodecagonWithCenter.distanceMultiplicity Finset.univ 1 = 24 := by
  rw [Configuration.distanceMultiplicity]
  have hfilter :
      (pairs (Finset.univ : Finset (Fin 13))).filter
          (fun e ↦ dodecagonWithCenter.pairDistance e = 1) =
        (pairs (Finset.univ : Finset (Fin 13))).filter
          (fun e ↦ e.1.val = 0 ∨ e.2.val - e.1.val = 2 ∨
            e.2.val - e.1.val = 10) := by
    apply Finset.filter_congr
    rintro ⟨i, j⟩ he
    fin_cases i <;> fin_cases j <;>
      simp [pairs, Configuration.pairDistance, dodecagonWithCenter,
        dodecagonWithCenterPoint, Complex.dist_eq, Complex.norm_def,
        Complex.normSq_apply] at he ⊢ <;>
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)]
  rw [hfilter]
  decide

/-- Enumeration of twenty-four unit pairs in the centered hexagram. -/
def hexagramUnitPair (k : Fin 24) : Fin 13 × Fin 13 :=
  match k.val with
  | 0 => (0, 7)
  | 1 => (0, 8)
  | 2 => (0, 9)
  | 3 => (0, 10)
  | 4 => (0, 11)
  | 5 => (0, 12)
  | 6 => (1, 7)
  | 7 => (1, 12)
  | 8 => (2, 7)
  | 9 => (2, 8)
  | 10 => (3, 8)
  | 11 => (3, 9)
  | 12 => (4, 9)
  | 13 => (4, 10)
  | 14 => (5, 10)
  | 15 => (5, 11)
  | 16 => (6, 11)
  | 17 => (6, 12)
  | 18 => (7, 8)
  | 19 => (7, 12)
  | 20 => (8, 9)
  | 21 => (9, 10)
  | 22 => (10, 11)
  | _ => (11, 12)

theorem hexagramUnitPair_injective : Function.Injective hexagramUnitPair := by
  decide

theorem hexagramUnitPair_mem_pairs (k : Fin 24) :
    hexagramUnitPair k ∈ pairs (Finset.univ : Finset (Fin 13)) := by
  fin_cases k <;> decide

theorem hexagramUnitPair_distance (k : Fin 24) :
    hexagramWithCenter.pairDistance (hexagramUnitPair k) = 1 := by
  fin_cases k <;>
    norm_num [Configuration.pairDistance, hexagramWithCenter,
      hexagramWithCenterPoint, hexagramUnitPair, Complex.dist_eq,
      Complex.norm_def, Complex.normSq_apply] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 3)]

/-- The centered hexagram has at least twenty-four unit-distance pairs. -/
theorem hexagramWithCenter_unit_distance_multiplicity :
    24 ≤ hexagramWithCenter.distanceMultiplicity Finset.univ 1 := by
  rw [Configuration.distanceMultiplicity]
  calc
    24 = ((Finset.univ : Finset (Fin 24)).image hexagramUnitPair).card := by
      rw [Finset.card_image_of_injective _ hexagramUnitPair_injective]
      simp
    _ ≤ ((pairs (Finset.univ : Finset (Fin 13))).filter
        (fun e ↦ hexagramWithCenter.pairDistance e = 1)).card := by
      apply Finset.card_le_card
      intro e he
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_filter.mpr
        ⟨hexagramUnitPair_mem_pairs k, hexagramUnitPair_distance k⟩

end

end LeanPool.Erdos132N14
