/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.DiskSquare
import LeanPool.ClassificationOfSurfaces.SphereCarrierGeometry
import LeanPool.ClassificationOfSurfaces.WeightedCircle

/-!
# The one-sided-degenerate P2 disk model

The ordinary P2 model glues two polygons along a marked side, with at least one old side on
each child.  Cancellation in the Gallier--Xu normalization also uses the limiting case in which
one child is a monogon.  This file supplies a concrete model for that case.

The local target is a polynomial teardrop.  The map

`z ↦ (1 - z) ^ 2`

is injective on the closed unit disk: translating by `1` puts the disk in a closed half-plane,
on which squaring has no nontrivial antipodal pair.  Its image is star-shaped at the cusp.  A
scaled copy receives the monogon, while the other child fills the collar between that copy and
the full teardrop.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace P2DegenerateDisk

/-- Every polygon cell has the closed-unit-disk norm bound. -/
theorem norm_le_one {n : ℕ} (z : PolygonCell n) :
    ‖z.val‖ ≤ 1 := by
  simpa [Metric.mem_closedBall, dist_zero_right] using z.property

/-- The polynomial disk used as the target of the degenerate two-child gluing. -/
def teardropMap {n : ℕ} (z : PolygonCell n) : ℂ :=
  (1 - z.val) ^ 2

theorem continuous_teardropMap {n : ℕ} :
    Continuous (teardropMap : PolygonCell n → ℂ) := by
  unfold teardropMap
  fun_prop

/-- A point of the closed unit disk with real part `1` is the cusp point `1`. -/
theorem eq_one_of_re_eq_one {n : ℕ} (z : PolygonCell n)
    (hre : z.val.re = 1) :
    z.val = 1 := by
  have hnorm : Complex.normSq z.val ≤ 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  apply Complex.ext
  · simpa using hre
  · simp only [Complex.one_im]
    rw [Complex.normSq_apply] at hnorm
    nlinarith

/-- Squaring after translation by `1` is injective on the closed unit disk. -/
theorem teardropMap_injective {n m : ℕ}
    {z : PolygonCell n} {w : PolygonCell m}
    (h : teardropMap z = teardropMap w) :
    z.val = w.val := by
  let u : ℂ := 1 - z.val
  let v : ℂ := 1 - w.val
  have hprod : (u - v) * (u + v) = 0 := by
    calc
      (u - v) * (u + v) = u ^ 2 - v ^ 2 := by ring
      _ = 0 := by
        dsimp [u, v, teardropMap] at h ⊢
        rw [h]
        ring
  rcases mul_eq_zero.mp hprod with huv | huv
  · dsimp [u, v] at huv
    linear_combination -huv
  · have hsum : z.val + w.val = 2 := by
      dsimp [u, v] at huv
      calc
        z.val + w.val =
            2 - ((1 - z.val) + (1 - w.val)) := by ring
        _ = 2 := by rw [huv, sub_zero]
    have hzre : z.val.re ≤ 1 :=
      (Complex.re_le_norm z.val).trans (norm_le_one z)
    have hwre : w.val.re ≤ 1 :=
      (Complex.re_le_norm w.val).trans (norm_le_one w)
    have hsumre := congrArg Complex.re hsum
    change z.val.re + w.val.re = 2 at hsumre
    have hzre_eq : z.val.re = 1 := by linarith
    have hwre_eq : w.val.re = 1 := by linarith
    rw [eq_one_of_re_eq_one z hzre_eq,
      eq_one_of_re_eq_one w hwre_eq]

/-- The teardrop image, equipped with the subspace topology inherited from the plane. -/
abbrev Teardrop :=
  Set.range (teardropMap : PolygonCell 1 → ℂ)

/-- The polynomial map as a map into its exact range. -/
def toTeardrop (z : PolygonCell 1) : Teardrop :=
  ⟨teardropMap z, ⟨z, rfl⟩⟩

theorem continuous_toTeardrop :
    Continuous toTeardrop := by
  exact continuous_induced_rng.2 continuous_teardropMap

theorem toTeardrop_bijective :
    Function.Bijective toTeardrop := by
  constructor
  · intro z w h
    apply PolygonCell.ext
    exact teardropMap_injective (congrArg Subtype.val h)
  · rintro ⟨x, z, rfl⟩
    exact ⟨z, rfl⟩

/-- The closed disk is homeomorphic to its polynomial teardrop image. -/
noncomputable def teardropHomeomorph :
    PolygonCell 1 ≃ₜ Teardrop :=
  IsHomeomorph.homeomorph toTeardrop
    ((isHomeomorph_iff_continuous_bijective).2
      ⟨continuous_toTeardrop, toTeardrop_bijective⟩)

@[simp]
theorem teardropHomeomorph_apply_val (z : PolygonCell 1) :
    (teardropHomeomorph z).val = teardropMap z :=
  by
    simp [teardropHomeomorph, toTeardrop]

/-- Contracting the translated disk toward its cusp stays in the translated disk. -/
theorem one_sub_smul_mem_closedBall
    (z : PolygonCell 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖(1 : ℂ) - s * (1 - z.val)‖ ≤ 1 := by
  have hconvex :
      (1 : ℂ) - s * (1 - z.val) =
        (1 - (s : ℂ)) * (1 : ℂ) + (s : ℂ) * z.val := by
    ring
  rw [hconvex]
  calc
    ‖(1 - (s : ℂ)) * (1 : ℂ) + (s : ℂ) * z.val‖ ≤
        ‖(1 - (s : ℂ)) * (1 : ℂ)‖ +
          ‖(s : ℂ) * z.val‖ :=
      norm_add_le _ _
    _ = (1 - s) + s * ‖z.val‖ := by
      rw [norm_mul, norm_mul, norm_one, mul_one]
      have hsub :
          (1 : ℂ) - (s : ℂ) = ((1 - s : ℝ) : ℂ) := by
        norm_num
      rw [hsub, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hs0, abs_of_nonneg (sub_nonneg.mpr hs1)]
    _ ≤ 1 := by
      have hz := norm_le_one z
      nlinarith

/-- Every radial contraction of a teardrop point is again a teardrop point. -/
theorem smul_teardropMap_mem_range
    (z : PolygonCell 1) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (s : ℂ) * teardropMap z ∈
      Set.range (teardropMap : PolygonCell 1 → ℂ) := by
  let r : ℝ := Real.sqrt s
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 := by
    simpa [r] using hs1
  let w : PolygonCell 1 :=
    ⟨(1 : ℂ) - r * (1 - z.val), by
      simpa [Metric.mem_closedBall, dist_zero_right] using
        one_sub_smul_mem_closedBall z hr0 hr1⟩
  refine ⟨w, ?_⟩
  unfold teardropMap
  dsimp [w, r]
  have hsqrt : (Real.sqrt s) ^ 2 = s :=
    Real.sq_sqrt hs0
  have hsqrtC : (Real.sqrt s : ℂ) ^ 2 = (s : ℂ) := by
    exact_mod_cast hsqrt
  rw [show (1 : ℂ) -
      ((1 : ℂ) - (Real.sqrt s : ℂ) * (1 - z.val)) =
        (Real.sqrt s : ℂ) * (1 - z.val) by ring]
  rw [mul_pow, hsqrtC]

/-! ## The monogon and collar maps -/

/-- The monogon occupies the inner radial half of the teardrop. -/
noncomputable def monogonMap (z : PolygonCell 1) : ℂ :=
  (((2 : ℝ)⁻¹ : ℝ) : ℂ) * teardropMap z

theorem continuous_monogonMap :
    Continuous monogonMap := by
  unfold monogonMap
  exact continuous_const.mul continuous_teardropMap

/-- Half of a teardrop point is still in the full teardrop. -/
theorem monogonMap_mem_teardrop (z : PolygonCell 1) :
    monogonMap z ∈ Set.range
      (teardropMap : PolygonCell 1 → ℂ) := by
  unfold monogonMap
  exact smul_teardropMap_mem_range
    (s := (2 : ℝ)⁻¹) z (by norm_num) (by norm_num)

/-- The nonnegative height of the upper circular boundary above a fixed real coordinate. -/
noncomputable def chordHeight (z : PolygonCell 2) : ℝ :=
  Real.sqrt (1 - z.val.re ^ 2)

theorem re_sq_le_one (z : PolygonCell 2) :
    z.val.re ^ 2 ≤ 1 := by
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  nlinarith [sq_nonneg z.val.im]

theorem chordHeight_nonneg (z : PolygonCell 2) :
    0 ≤ chordHeight z :=
  Real.sqrt_nonneg _

theorem chordHeight_sq (z : PolygonCell 2) :
    chordHeight z ^ 2 = 1 - z.val.re ^ 2 := by
  exact Real.sq_sqrt (sub_nonneg.mpr (re_sq_le_one z))

theorem neg_chordHeight_le_im (z : PolygonCell 2) :
    -chordHeight z ≤ z.val.im := by
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  have hs := chordHeight_sq z
  have hs0 := chordHeight_nonneg z
  nlinarith [sq_nonneg (z.val.im + chordHeight z)]

theorem im_le_chordHeight (z : PolygonCell 2) :
    z.val.im ≤ chordHeight z := by
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  have hs := chordHeight_sq z
  have hs0 := chordHeight_nonneg z
  nlinarith [sq_nonneg (z.val.im - chordHeight z)]

/-- The lower unit-circle point on the vertical chord through a digon point, squared so that the
two chord endpoints sweep the teardrop boundary once. -/
noncomputable def collarCircleValue (z : PolygonCell 2) : ℂ :=
  ((z.val.re : ℂ) - (chordHeight z : ℂ) * Complex.I) ^ 2

theorem collarCircleValue_norm (z : PolygonCell 2) :
    ‖collarCircleValue z‖ = 1 := by
  let a : ℂ :=
    (z.val.re : ℂ) - (chordHeight z : ℂ) * Complex.I
  have haSq : Complex.normSq a = 1 := by
    rw [Complex.normSq_apply]
    simp only [a, Complex.sub_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, sub_zero, Complex.sub_im,
      Complex.mul_im, Complex.I_im, mul_one, add_zero,
      zero_sub]
    nlinarith [chordHeight_sq z]
  have haNorm : ‖a‖ = 1 := by
    have hnorm0 := norm_nonneg a
    rw [Complex.normSq_eq_norm_sq] at haSq
    nlinarith
  change ‖a ^ 2‖ = 1
  rw [norm_pow, haNorm]
  norm_num

/-- The collar's boundary-direction point, bundled as a point of the unit disk. -/
noncomputable def collarCirclePoint (z : PolygonCell 2) :
    PolygonCell 1 :=
  ⟨collarCircleValue z, by
    simp [Metric.mem_closedBall, dist_zero_right,
      collarCircleValue_norm z]⟩

theorem continuous_chordHeight :
    Continuous chordHeight := by
  unfold chordHeight
  fun_prop

theorem continuous_collarCircleValue :
    Continuous collarCircleValue := by
  unfold collarCircleValue
  apply Continuous.pow
  apply Continuous.sub
  · exact Complex.continuous_ofReal.comp
      (Complex.continuous_re.comp PolygonCell.continuous_val)
  · exact
      (Complex.continuous_ofReal.comp continuous_chordHeight).mul
        continuous_const

theorem continuous_collarCirclePoint :
    Continuous collarCirclePoint :=
  continuous_induced_rng.2 continuous_collarCircleValue

/-- The teardrop boundary value of the collar direction has an exact quadratic factor. -/
theorem teardropMap_collarCirclePoint
    (z : PolygonCell 2) :
    teardropMap (collarCirclePoint z) =
      (-4 : ℂ) * (chordHeight z : ℂ) ^ 2 *
        collarCircleValue z := by
  let x : ℝ := z.val.re
  let s : ℝ := chordHeight z
  let a : ℂ := (x : ℂ) - (s : ℂ) * Complex.I
  have hcircleR : x ^ 2 + s ^ 2 = 1 := by
    dsimp [x, s]
    nlinarith [chordHeight_sq z]
  have hcircleC : (x : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by
    exact_mod_cast hcircleR
  have hone : (1 : ℂ) - a ^ 2 =
      2 * Complex.I * (s : ℂ) * a := by
    apply Complex.ext
    · simp [a, pow_two]
      nlinarith [hcircleR]
    · simp [a, pow_two]
      ring
  have hI : (2 * Complex.I : ℂ) ^ 2 = -4 := by
    calc
      (2 * Complex.I : ℂ) ^ 2 =
          4 * (Complex.I * Complex.I) := by ring
      _ = -4 := by rw [Complex.I_mul_I]; ring
  change (1 - a ^ 2) ^ 2 =
    (-4 : ℂ) * (s : ℂ) ^ 2 * a ^ 2
  rw [hone]
  calc
    (2 * Complex.I * (s : ℂ) * a) ^ 2 =
        (2 * Complex.I) ^ 2 * (s : ℂ) ^ 2 * a ^ 2 := by ring
    _ = (-4 : ℂ) * (s : ℂ) ^ 2 * a ^ 2 := by rw [hI]

/-- The digon fills the radial collar between the half-size and full teardrop boundaries. -/
noncomputable def collarMap (z : PolygonCell 2) : ℂ :=
  let s := chordHeight z
  collarCircleValue z *
    ((s * z.val.im - 3 * s ^ 2 : ℝ) : ℂ)

theorem continuous_collarMap :
    Continuous collarMap := by
  unfold collarMap
  apply continuous_collarCircleValue.mul
  apply Complex.continuous_ofReal.comp
  exact
    (continuous_chordHeight.mul
      (Complex.continuous_im.comp PolygonCell.continuous_val)).sub
        (continuous_const.mul (continuous_chordHeight.pow 2))

/-- Away from the two chord tips, the collar map is a radial teardrop value with scale in
`[1/2, 1]`. -/
theorem collarMap_eq_smul_teardropMap
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    collarMap z =
      (((3 * chordHeight z ^ 2 -
          chordHeight z * z.val.im) /
            (4 * chordHeight z ^ 2) : ℝ) : ℂ) *
        teardropMap (collarCirclePoint z) := by
  let s : ℝ := chordHeight z
  let y : ℝ := z.val.im
  have hscalar :
      s * y - 3 * s ^ 2 =
        ((3 * s ^ 2 - s * y) / (4 * s ^ 2)) *
          (-4) * s ^ 2 := by
    have hs' : s ≠ 0 := by simpa [s] using hs
    field_simp [hs']
    ring
  have hscalarC :
      ((s * y - 3 * s ^ 2 : ℝ) : ℂ) =
        (((3 * s ^ 2 - s * y) / (4 * s ^ 2) : ℝ) : ℂ) *
          (-4 : ℂ) * (s : ℂ) ^ 2 := by
    exact_mod_cast hscalar
  rw [teardropMap_collarCirclePoint]
  unfold collarMap
  change
    collarCircleValue z *
        ((s * y - 3 * s ^ 2 : ℝ) : ℂ) =
      (((3 * s ^ 2 - s * y) / (4 * s ^ 2) : ℝ) : ℂ) *
        ((-4 : ℂ) * (s : ℂ) ^ 2 * collarCircleValue z)
  rw [hscalarC]
  ring

theorem collarScale_nonneg
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    0 ≤ (3 * chordHeight z ^ 2 -
        chordHeight z * z.val.im) /
          (4 * chordHeight z ^ 2) := by
  have hspos : 0 < chordHeight z :=
    (chordHeight_nonneg z).lt_of_ne' hs
  have hy := im_le_chordHeight z
  apply div_nonneg
  · nlinarith
  · positivity

theorem collarScale_le_one
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    (3 * chordHeight z ^ 2 -
        chordHeight z * z.val.im) /
          (4 * chordHeight z ^ 2) ≤ 1 := by
  have hspos : 0 < chordHeight z :=
    (chordHeight_nonneg z).lt_of_ne' hs
  have hy := neg_chordHeight_le_im z
  rw [div_le_one (by positivity)]
  nlinarith

theorem collarMap_mem_teardrop (z : PolygonCell 2) :
    collarMap z ∈ Set.range
      (teardropMap : PolygonCell 1 → ℂ) := by
  by_cases hs : chordHeight z = 0
  · refine ⟨⟨1, by simp [Metric.mem_closedBall]⟩, ?_⟩
    simp [collarMap, hs, teardropMap]
  · rw [collarMap_eq_smul_teardropMap z hs]
    exact smul_teardropMap_mem_range
      (collarCirclePoint z)
      (collarScale_nonneg z hs)
      (collarScale_le_one z hs)

/-! ## Exact compatibility on the fresh seam -/

/-- On the upper circular boundary of the digon, the collar meets the half-size teardrop
occupied by the monogon. -/
theorem collarMap_eq_monogonMap_collarCirclePoint_of_im_eq
    (z : PolygonCell 2) (hy : z.val.im = chordHeight z) :
    collarMap z = monogonMap (collarCirclePoint z) := by
  unfold collarMap monogonMap
  rw [teardropMap_collarCirclePoint]
  rw [hy]
  norm_num
  ring

/-- Side zero of the digon is the upper semicircle with its usual angle parameter. -/
theorem side_zero_digon_val (t : unitInterval) :
    (PolygonCell.side (0 : Fin 2) t : PolygonCell 2).val =
      (Circle.exp (Real.pi * (t : ℝ)) : ℂ) := by
  change
    (Circle.exp
        (PolygonCell.sideAngle (0 : Fin 2) t) : ℂ) =
      (Circle.exp (Real.pi * (t : ℝ)) : ℂ)
  congr 2
  unfold PolygonCell.sideAngle
  norm_num
  ring

/-- The imaginary coordinate on side zero of the digon. -/
theorem side_zero_digon_im (t : unitInterval) :
    (PolygonCell.side (0 : Fin 2) t : PolygonCell 2).val.im =
      Real.sin (Real.pi * (t : ℝ)) := by
  rw [side_zero_digon_val]
  exact Complex.exp_ofReal_mul_I_im _

/-- The chord height agrees with the imaginary coordinate on the upper digon side. -/
theorem chordHeight_side_zero_digon (t : unitInterval) :
    chordHeight (PolygonCell.side (0 : Fin 2) t) =
      Real.sin (Real.pi * (t : ℝ)) := by
  let z : PolygonCell 2 := PolygonCell.side (0 : Fin 2) t
  let θ : ℝ := Real.pi * (t : ℝ)
  have hθ0 : 0 ≤ θ := mul_nonneg Real.pi_pos.le t.property.1
  have hθπ : θ ≤ Real.pi := by
    dsimp [θ]
    nlinarith [Real.pi_pos, t.property.2]
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  have hre : z.val.re = Real.cos θ := by
    dsimp [z, θ]
    rw [side_zero_digon_val]
    exact Complex.exp_ofReal_mul_I_re _
  have him : z.val.im = Real.sin θ := by
    simpa [z, θ] using side_zero_digon_im t
  have hs := chordHeight_sq z
  have htrig := Real.sin_sq_add_cos_sq θ
  rw [hre] at hs
  have hheight0 := chordHeight_nonneg z
  change chordHeight z = Real.sin θ
  nlinarith

/-- Squaring the lower endpoint of an upper digon chord gives the corresponding monogon
boundary point. -/
theorem collarCirclePoint_side_zero_digon_symm (t : unitInterval) :
    collarCirclePoint
        (PolygonCell.side (0 : Fin 2) (unitInterval.symm t)) =
      PolygonCell.side (0 : Fin 1) t := by
  apply PolygonCell.ext
  let u : unitInterval := unitInterval.symm t
  let θ : ℝ := Real.pi * (u : ℝ)
  have hheight :
      chordHeight (PolygonCell.side (0 : Fin 2) u) =
        Real.sin θ := by
    simpa [θ] using chordHeight_side_zero_digon u
  have hre :
      (PolygonCell.side (0 : Fin 2) u : PolygonCell 2).val.re =
        Real.cos θ := by
    rw [side_zero_digon_val]
    exact Complex.exp_ofReal_mul_I_re _
  have ha :
      ((Real.cos θ : ℂ) -
          (Real.sin θ : ℂ) * Complex.I) =
        (Circle.exp (-θ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
        zero_mul, sub_zero, Circle.coe_exp,
        Complex.exp_ofReal_mul_I_re, Real.cos_neg]
    · simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul,
        mul_one, add_zero, zero_sub, Circle.coe_exp,
        Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  change collarCircleValue
      (PolygonCell.side (0 : Fin 2) u) =
    (PolygonCell.side (0 : Fin 1) t : PolygonCell 1).val
  unfold collarCircleValue
  rw [hheight, hre, ha]
  change ((Circle.exp (-θ) : ℂ) ^ 2) =
    (Circle.exp (PolygonCell.sideAngle (0 : Fin 1) t) : ℂ)
  rw [pow_two, ← Circle.coe_mul, ← Circle.exp_add]
  apply congrArg (fun z : Circle ↦ (z : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨-1, ?_⟩
  dsimp [θ, u]
  simp only [PolygonCell.sideAngle, Fin.val_zero, Nat.cast_one,
    div_one, Int.cast_neg, Int.cast_one,
    neg_mul, one_mul]
  ring

/-- The analytic child map respects the exact reversed fresh-side parameter used by P2. -/
theorem monogonMap_fresh_seam (t : unitInterval) :
    monogonMap (PolygonCell.side (0 : Fin 1) t) =
      collarMap
        (PolygonCell.side (0 : Fin 2) (unitInterval.symm t)) := by
  symm
  rw [collarMap_eq_monogonMap_collarCirclePoint_of_im_eq,
    collarCirclePoint_side_zero_digon_symm]
  rw [side_zero_digon_im]
  exact (chordHeight_side_zero_digon (unitInterval.symm t)).symm

/-! ## Descending the base child pair to the teardrop -/

/-- The base one-sided-degenerate child pair: a monogon and a digon. -/
abbrev BaseChildPair :=
  DiskSquare.ChildPair 0 1

/-- Map both children into their complementary regions of the teardrop. -/
noncomputable def baseChildPairMap : BaseChildPair → Teardrop
  | .inl z => ⟨monogonMap z, monogonMap_mem_teardrop z⟩
  | .inr z => ⟨collarMap z, collarMap_mem_teardrop z⟩

theorem continuous_baseChildPairMap :
    Continuous baseChildPairMap := by
  apply continuous_induced_rng.2
  convert continuous_monogonMap.sumElim continuous_collarMap using 1
  funext x
  cases x <;> rfl

@[simp]
theorem baseChildPairMap_inl (z : PolygonCell 1) :
    (baseChildPairMap (.inl z)).val = monogonMap z :=
  rfl

@[simp]
theorem baseChildPairMap_inr (z : PolygonCell 2) :
    (baseChildPairMap (.inr z)).val = collarMap z :=
  rfl

/-- The child-pair map is constant on the generating fresh seam. -/
theorem baseChildPairMap_eq_of_generator
    {x y : BaseChildPair}
    (hxy : DiskSquare.ParamChildSeamGenerator 0 1 x y) :
    baseChildPairMap x = baseChildPairMap y := by
  cases hxy with
  | glue t =>
      apply Subtype.ext
      exact monogonMap_fresh_seam t

/-- The child-pair map is constant on the equivalence relation generated by the fresh seam. -/
theorem baseChildPairMap_respects
    {x y : BaseChildPair}
    (hxy :
      Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 1) x y) :
    baseChildPairMap x = baseChildPairMap y := by
  induction hxy with
  | rel _ _ h => exact baseChildPairMap_eq_of_generator h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The continuous analytic map induced on the one-sided-degenerate child quotient. -/
noncomputable def baseChildGluingMap :
    C(DiskSquare.ParamChildGluing 0 1, Teardrop) where
  toFun :=
    Quotient.lift baseChildPairMap fun _ _ hxy ↦
      baseChildPairMap_respects hxy
  continuous_toFun :=
    continuous_baseChildPairMap.quotient_lift fun _ _ hxy ↦
      baseChildPairMap_respects hxy

@[simp]
theorem baseChildGluingMap_mk (x : BaseChildPair) :
    baseChildGluingMap
        (@Quotient.mk'' BaseChildPair
          (DiskSquare.paramChildSeamSetoid 0 1) x) =
      baseChildPairMap x :=
  rfl

/-! ## The collar has no hidden interior identifications -/

/-- The nonnegative radial magnitude used by the collar map. -/
noncomputable def collarRadius (z : PolygonCell 2) : ℝ :=
  3 * chordHeight z ^ 2 - chordHeight z * z.val.im

theorem two_mul_chordHeight_sq_le_collarRadius
    (z : PolygonCell 2) :
    2 * chordHeight z ^ 2 ≤ collarRadius z := by
  have hs0 := chordHeight_nonneg z
  have hy := im_le_chordHeight z
  unfold collarRadius
  nlinarith

theorem collarRadius_nonneg (z : PolygonCell 2) :
    0 ≤ collarRadius z :=
  (mul_nonneg (by norm_num) (sq_nonneg _)).trans
    (two_mul_chordHeight_sq_le_collarRadius z)

theorem collarRadius_pos (z : PolygonCell 2)
    (hs : chordHeight z ≠ 0) :
    0 < collarRadius z := by
  have hsSq : 0 < chordHeight z ^ 2 :=
    sq_pos_of_ne_zero hs
  exact (mul_pos (by norm_num) hsSq).trans_le
    (two_mul_chordHeight_sq_le_collarRadius z)

theorem collarMap_eq_neg_radius_mul (z : PolygonCell 2) :
    collarMap z =
      (-(collarRadius z) : ℂ) * collarCircleValue z := by
  unfold collarMap collarRadius
  push_cast
  ring

theorem norm_collarMap (z : PolygonCell 2) :
    ‖collarMap z‖ = collarRadius z := by
  rw [collarMap_eq_neg_radius_mul, norm_mul,
    collarCircleValue_norm]
  rw [mul_one, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (collarRadius_nonneg z)]

/-- Equal non-tip collar values have the same boundary direction. -/
theorem collarCircleValue_eq_of_collarMap_eq
    (z w : PolygonCell 2)
    (hz : chordHeight z ≠ 0)
    (hzw : collarMap z = collarMap w) :
    collarCircleValue z = collarCircleValue w := by
  have hradius :
      collarRadius z = collarRadius w := by
    rw [← norm_collarMap z, ← norm_collarMap w, hzw]
  have hradius_ne : collarRadius z ≠ 0 :=
    (collarRadius_pos z hz).ne'
  have hradius_ne_w : collarRadius w ≠ 0 := by
    rwa [← hradius]
  rw [collarMap_eq_neg_radius_mul,
    collarMap_eq_neg_radius_mul, hradius] at hzw
  exact mul_left_cancel₀
    (show (-(collarRadius w) : ℂ) ≠ 0 by
      exact_mod_cast neg_ne_zero.mpr hradius_ne_w)
    hzw

/-- The lower unit-circle representatives used by the squaring map. -/
noncomputable def lowerChordValue (z : PolygonCell 2) : ℂ :=
  (z.val.re : ℂ) - (chordHeight z : ℂ) * Complex.I

theorem collarCircleValue_eq_lowerChordValue_sq
    (z : PolygonCell 2) :
    collarCircleValue z = lowerChordValue z ^ 2 :=
  rfl

theorem lowerChordValue_im (z : PolygonCell 2) :
    (lowerChordValue z).im = -chordHeight z := by
  simp [lowerChordValue]

theorem lowerChordValue_re (z : PolygonCell 2) :
    (lowerChordValue z).re = z.val.re := by
  simp [lowerChordValue]

/-- Squaring is injective on the open lower semicircle used by non-tip collar chords. -/
theorem lowerChordValue_eq_of_collarCircleValue_eq
    (z w : PolygonCell 2)
    (hz : chordHeight z ≠ 0)
    (hzw : collarCircleValue z = collarCircleValue w) :
    lowerChordValue z = lowerChordValue w := by
  rw [collarCircleValue_eq_lowerChordValue_sq,
    collarCircleValue_eq_lowerChordValue_sq] at hzw
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hzw with heq | hneg
  · exact heq
  · exfalso
    have him := congrArg Complex.im hneg
    rw [lowerChordValue_im, Complex.neg_im,
      lowerChordValue_im] at him
    have hzpos : 0 < chordHeight z :=
      (chordHeight_nonneg z).lt_of_ne' hz
    have hw0 := chordHeight_nonneg w
    linarith

/-- The collar is injective away from its two pinched tips. -/
theorem collarMap_injective_of_chordHeight_ne_zero
    (z w : PolygonCell 2)
    (hz : chordHeight z ≠ 0)
    (hzw : collarMap z = collarMap w) :
    z = w := by
  have hcircle :=
    collarCircleValue_eq_of_collarMap_eq z w hz hzw
  have hlower :=
    lowerChordValue_eq_of_collarCircleValue_eq z w hz hcircle
  have hre : z.val.re = w.val.re := by
    simpa only [lowerChordValue_re] using
      congrArg Complex.re hlower
  have hs : chordHeight z = chordHeight w := by
    have him := congrArg Complex.im hlower
    rw [lowerChordValue_im, lowerChordValue_im] at him
    linarith
  have hradius :
      collarRadius z = collarRadius w := by
    rw [← norm_collarMap z, ← norm_collarMap w, hzw]
  have him : z.val.im = w.val.im := by
    have hzpos : 0 < chordHeight z :=
      (chordHeight_nonneg z).lt_of_ne' hz
    unfold collarRadius at hradius
    rw [hs] at hradius
    nlinarith
  apply PolygonCell.ext
  exact Complex.ext hre him

theorem chordHeight_eq_zero_of_collarRadius_eq_zero
    (z : PolygonCell 2) (hradius : collarRadius z = 0) :
    chordHeight z = 0 := by
  have hle := two_mul_chordHeight_sq_le_collarRadius z
  rw [hradius] at hle
  have hs0 := chordHeight_nonneg z
  nlinarith [sq_nonneg (chordHeight z)]

/-- The only zero-height digon points are the two endpoints of its upper side. -/
theorem eq_side_zero_or_side_one_of_chordHeight_eq_zero
    (z : PolygonCell 2) (hs : chordHeight z = 0) :
    z = PolygonCell.side (0 : Fin 2) 0 ∨
      z = PolygonCell.side (0 : Fin 2) 1 := by
  have hsSq := chordHeight_sq z
  rw [hs] at hsSq
  have hreSq : z.val.re ^ 2 = 1 := by
    nlinarith
  have hnormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  rw [Complex.normSq_apply] at hnormSq
  have him : z.val.im = 0 := by
    nlinarith [sq_nonneg z.val.im]
  rcases sq_eq_one_iff.mp hreSq with hre | hre
  · left
    apply PolygonCell.ext
    rw [side_zero_digon_val]
    apply Complex.ext
    · simpa using hre
    · simpa using him
  · right
    apply PolygonCell.ext
    rw [side_zero_digon_val]
    apply Complex.ext
    · simpa [Circle.coe_exp] using hre
    · simpa [Circle.coe_exp] using him

/-- Either collar tip is identified with the monogon basepoint by the generated seam relation. -/
theorem inr_tip_eqv_inl_monogon_basepoint
    (z : PolygonCell 2) (hs : chordHeight z = 0) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 1)
        (.inr z : BaseChildPair)
        (.inl (PolygonCell.side (0 : Fin 1) 0)) := by
  rcases eq_side_zero_or_side_one_of_chordHeight_eq_zero z hs with hz | hz
  · subst z
    have hgen :=
      Relation.EqvGen.rel _ _
        (DiskSquare.ParamChildSeamGenerator.glue
          (l := 0) (r := 1) (1 : unitInterval))
    exact Relation.EqvGen.symm _ _ (by
      simpa [PolygonCell.side_zero_eq_side_one_monogon] using hgen)
  · subst z
    have hgen :=
      Relation.EqvGen.rel _ _
        (DiskSquare.ParamChildSeamGenerator.glue
          (l := 0) (r := 1) (0 : unitInterval))
    exact Relation.EqvGen.symm _ _ (by simpa using hgen)

/-- Equality inside the collar is exactly equality modulo the two endpoint seam identifications. -/
theorem baseChildPair_eqvGen_inr_inr_of_map_eq
    (z w : PolygonCell 2) (hzw : collarMap z = collarMap w) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 1)
        (.inr z : BaseChildPair) (.inr w) := by
  by_cases hz : chordHeight z = 0
  · have hzmap : collarMap z = 0 := by
      simp [collarMap, hz]
    have hwmap : collarMap w = 0 := hzmap ▸ hzw.symm
    have hradius : collarRadius w = 0 := by
      rw [← norm_collarMap w, hwmap, norm_zero]
    have hw := chordHeight_eq_zero_of_collarRadius_eq_zero w hradius
    exact Relation.EqvGen.trans _ _ _
      (inr_tip_eqv_inl_monogon_basepoint z hz)
      (Relation.EqvGen.symm _ _
        (inr_tip_eqv_inl_monogon_basepoint w hw))
  · have heq :=
      collarMap_injective_of_chordHeight_ne_zero z w hz hzw
    subst w
    exact Relation.EqvGen.refl _

/-- Every point on the upper circular boundary of the digon has a side-zero parameter. -/
theorem exists_side_zero_digon_eq_of_im_eq_chordHeight
    (z : PolygonCell 2) (hy : z.val.im = chordHeight z) :
    ∃ t : unitInterval, PolygonCell.side (0 : Fin 2) t = z := by
  have hcircleSq :
      z.val.re ^ 2 + z.val.im ^ 2 = 1 := by
    rw [hy, chordHeight_sq]
    ring
  have hnorm : ‖z.val‖ = 1 := by
    have hnormSq : ‖z.val‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply]
      simpa [pow_two] using hcircleSq
    nlinarith [norm_nonneg z.val]
  let q : Circle :=
    ⟨z.val, mem_sphere_zero_iff_norm.mpr hnorm⟩
  have harg0 : 0 ≤ q.val.arg := by
    rw [Complex.arg_nonneg_iff]
    exact hy.trans_ge (chordHeight_nonneg z)
  have hargPi : q.val.arg ≤ Real.pi :=
    Complex.arg_le_pi _
  let t : unitInterval :=
    ⟨q.val.arg / Real.pi,
      div_nonneg harg0 Real.pi_pos.le,
      (div_le_one Real.pi_pos).2 hargPi⟩
  refine ⟨t, ?_⟩
  apply PolygonCell.ext
  rw [side_zero_digon_val]
  have hangle :
      Real.pi * (t : ℝ) = q.val.arg := by
    dsimp [t]
    field_simp [Real.pi_ne_zero]
  rw [hangle]
  exact congrArg Subtype.val (Circle.exp_arg q)

/-- A disk point cannot lie radially beyond a non-cusp boundary point of the teardrop. -/
theorem teardrop_radial_scale_le_one
    (z q : PolygonCell 1) (hqnorm : ‖q.val‖ = 1)
    (hqcusp : q.val ≠ 1) {μ : ℝ} (hμ : 1 ≤ μ)
    (hscale :
      teardropMap z = (μ : ℂ) * teardropMap q) :
    μ ≤ 1 := by
  let u : ℂ := 1 - z.val
  let v : ℂ := 1 - q.val
  let r : ℝ := Real.sqrt μ
  have hμ0 : 0 ≤ μ := le_trans (by norm_num) hμ
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = μ := by
    exact Real.sq_sqrt hμ0
  have hr1 : 1 ≤ r := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hμ
  have hsq :
      u ^ 2 = ((r : ℂ) * v) ^ 2 := by
    dsimp [u, v, r, teardropMap] at hscale ⊢
    rw [mul_pow]
    have hrSqC : (Real.sqrt μ : ℂ) ^ 2 = (μ : ℂ) := by
      exact_mod_cast hrSq
    rw [hrSqC]
    exact hscale
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hplus | hminus
  · have hzval :
        z.val = 1 - (r : ℂ) * (1 - q.val) := by
      dsimp [u, v] at hplus
      linear_combination -hplus
    have hqre : q.val.re < 1 := by
      have hle :
          q.val.re ≤ 1 :=
        (Complex.re_le_norm q.val).trans_eq hqnorm
      exact lt_of_le_of_ne hle fun heq ↦
        hqcusp (eq_one_of_re_eq_one q heq)
    have hqSq : q.val.re ^ 2 + q.val.im ^ 2 = 1 := by
      have h := congrArg (fun x : ℝ ↦ x ^ 2) hqnorm
      rw [← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply] at h
      simpa [pow_two] using h
    have hformula :
        Complex.normSq
            (1 - (r : ℂ) * (1 - q.val)) =
          1 + 2 * r * (r - 1) * (1 - q.val.re) := by
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re,
        Complex.re_ofReal_mul, Complex.sub_im,
        Complex.one_im, Complex.im_ofReal_mul, zero_sub]
      linear_combination r ^ 2 * hqSq
    have hnormz : Complex.normSq z.val ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_le_one z, norm_nonneg z.val]
    rw [hzval, hformula] at hnormz
    have hrle : r ≤ 1 := by
      by_contra hr
      have hrlt : 1 < r := lt_of_not_ge hr
      have hprod :
          0 < 2 * r * (r - 1) * (1 - q.val.re) := by
        positivity
      linarith
    nlinarith [hrSq]
  · have hzval :
        z.val = 1 + (r : ℂ) * (1 - q.val) := by
      dsimp [u, v] at hminus
      linear_combination -hminus
    have hqre : q.val.re < 1 := by
      have hle :
          q.val.re ≤ 1 :=
        (Complex.re_le_norm q.val).trans_eq hqnorm
      exact lt_of_le_of_ne hle fun heq ↦
        hqcusp (eq_one_of_re_eq_one q heq)
    have hqSq : q.val.re ^ 2 + q.val.im ^ 2 = 1 := by
      have h := congrArg (fun x : ℝ ↦ x ^ 2) hqnorm
      rw [← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply] at h
      simpa [pow_two] using h
    have hformula :
        Complex.normSq
            (1 + (r : ℂ) * (1 - q.val)) =
          1 + 2 * r * (r + 1) * (1 - q.val.re) := by
      rw [Complex.normSq_apply]
      simp only [Complex.add_re, Complex.one_re,
        Complex.re_ofReal_mul, Complex.sub_re,
        Complex.add_im, Complex.one_im,
        Complex.im_ofReal_mul, Complex.sub_im, zero_sub]
      linear_combination r ^ 2 * hqSq
    have hnormz : Complex.normSq z.val ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_le_one z, norm_nonneg z.val]
    rw [hzval, hformula] at hnormz
    have hprod :
        0 < 2 * r * (r + 1) * (1 - q.val.re) := by
      have hrpos : 0 < r := lt_of_lt_of_le (by norm_num) hr1
      positivity
    linarith

theorem collarScale_half_le
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    (2 : ℝ)⁻¹ ≤
      (3 * chordHeight z ^ 2 -
          chordHeight z * z.val.im) /
        (4 * chordHeight z ^ 2) := by
  have hspos : 0 < chordHeight z :=
    (chordHeight_nonneg z).lt_of_ne' hs
  have hy := im_le_chordHeight z
  rw [le_div_iff₀ (by positivity)]
  norm_num
  nlinarith

theorem norm_collarCirclePoint (z : PolygonCell 2) :
    ‖(collarCirclePoint z).val‖ = 1 :=
  collarCircleValue_norm z

theorem collarCirclePoint_ne_cusp
    (z : PolygonCell 2) (hs : chordHeight z ≠ 0) :
    (collarCirclePoint z).val ≠ 1 := by
  intro hcusp
  have htd := teardropMap_collarCirclePoint z
  have hleftzero :
      teardropMap (collarCirclePoint z) = 0 := by
    unfold teardropMap
    rw [hcusp]
    ring
  have hzero' :
      (-4 : ℂ) * (chordHeight z : ℂ) ^ 2 *
          collarCircleValue z = 0 :=
    htd.symm.trans hleftzero
  have hzero :
      (-4 : ℂ) * (chordHeight z : ℂ) ^ 2 = 0 := by
    rw [show collarCircleValue z = 1 from hcusp,
      mul_one] at hzero'
    exact hzero'
  rcases mul_eq_zero.mp hzero with hfour | hsSq
  · norm_num at hfour
  · exact hs (by
      exact_mod_cast (sq_eq_zero_iff.mp hsSq))

/-- The half-size teardrop map reaches the cusp only at the monogon basepoint. -/
theorem eq_monogon_basepoint_of_monogonMap_eq_zero
    (z : PolygonCell 1) (hz : monogonMap z = 0) :
    z = PolygonCell.side (0 : Fin 1) 0 := by
  have htd : teardropMap z = 0 := by
    unfold monogonMap at hz
    have hhalf :
        ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hz).resolve_left hhalf
  apply PolygonCell.ext
  apply teardropMap_injective
  rw [htd]
  change 0 =
    (1 -
      (Circle.exp
        (PolygonCell.sideAngle (0 : Fin 1) 0) : ℂ)) ^ 2
  simp [PolygonCell.sideAngle]

/-- A monogon point and a collar point have the same image exactly along the declared seam. -/
theorem baseChildPair_eqvGen_inl_inr_of_map_eq
    (z : PolygonCell 1) (w : PolygonCell 2)
    (hzw : monogonMap z = collarMap w) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 1)
        (.inl z : BaseChildPair) (.inr w) := by
  by_cases hs : chordHeight w = 0
  · have hwmap : collarMap w = 0 := by
      simp [collarMap, hs]
    have hzmap : monogonMap z = 0 := hzw.trans hwmap
    have hz := eq_monogon_basepoint_of_monogonMap_eq_zero z hzmap
    subst z
    exact Relation.EqvGen.symm _ _
      (inr_tip_eqv_inl_monogon_basepoint w hs)
  · let scale : ℝ :=
      (3 * chordHeight w ^ 2 -
          chordHeight w * w.val.im) /
        (4 * chordHeight w ^ 2)
    have hcollar :
        collarMap w =
          (scale : ℂ) * teardropMap (collarCirclePoint w) := by
      simpa [scale] using collarMap_eq_smul_teardropMap w hs
    have hscale :
        teardropMap z =
          ((2 * scale : ℝ) : ℂ) *
            teardropMap (collarCirclePoint w) := by
      unfold monogonMap at hzw
      rw [hcollar] at hzw
      calc
        teardropMap z =
            (2 : ℂ) *
              (((((2 : ℝ)⁻¹ : ℝ) : ℂ)) *
                teardropMap z) := by
                  norm_num
                  ring
        _ = (2 : ℂ) *
              ((scale : ℂ) *
                teardropMap (collarCirclePoint w)) := by
              rw [hzw]
        _ = ((2 * scale : ℝ) : ℂ) *
              teardropMap (collarCirclePoint w) := by
              push_cast
              ring
    have hμone :
        2 * scale ≤ 1 :=
      teardrop_radial_scale_le_one z (collarCirclePoint w)
        (norm_collarCirclePoint w)
        (collarCirclePoint_ne_cusp w hs)
        (by
          dsimp [scale]
          nlinarith [collarScale_half_le w hs])
        hscale
    have hscaleHalf : scale = (2 : ℝ)⁻¹ := by
      have hhalf := collarScale_half_le w hs
      dsimp [scale] at hhalf ⊢
      nlinarith
    have hy : w.val.im = chordHeight w := by
      have hden : 4 * chordHeight w ^ 2 ≠ 0 := by
        positivity
      dsimp [scale] at hscaleHalf
      rw [div_eq_iff hden] at hscaleHalf
      norm_num at hscaleHalf
      have hspos : 0 < chordHeight w :=
        (chordHeight_nonneg w).lt_of_ne' hs
      nlinarith
    have htd :
        teardropMap z =
          teardropMap (collarCirclePoint w) := by
      have hμeq : 2 * scale = 1 := by
        rw [hscaleHalf]
        norm_num
      simpa [hμeq] using hscale
    have hzcircle : z = collarCirclePoint w := by
      apply PolygonCell.ext
      exact teardropMap_injective htd
    obtain ⟨u, hu⟩ :=
      exists_side_zero_digon_eq_of_im_eq_chordHeight w hy
    have hgen :=
      Relation.EqvGen.rel _ _
        (DiskSquare.ParamChildSeamGenerator.glue
          (l := 0) (r := 1) (unitInterval.symm u))
    rw [← hu] at hzcircle ⊢
    have hc :=
      collarCirclePoint_side_zero_digon_symm
        (unitInterval.symm u)
    simp only [unitInterval.symm_symm] at hc hgen
    rw [hzcircle, hc]
    exact hgen

theorem monogonMap_injective :
    Function.Injective monogonMap := by
  intro z w hzw
  unfold monogonMap at hzw
  have hhalf :
      ((((2 : ℝ)⁻¹ : ℝ) : ℂ)) ≠ 0 := by norm_num
  have htd :
      teardropMap z = teardropMap w :=
    mul_left_cancel₀ hhalf hzw
  apply PolygonCell.ext
  exact teardropMap_injective htd

/-- Equality under the analytic child-pair map is exactly the generated seam relation. -/
theorem baseChildPairMap_eqvGen_of_eq
    {x y : BaseChildPair}
    (hxy : baseChildPairMap x = baseChildPairMap y) :
    Relation.EqvGen
      (DiskSquare.ParamChildSeamGenerator 0 1) x y := by
  cases x with
  | inl z =>
      cases y with
      | inl w =>
          have hzw : monogonMap z = monogonMap w :=
            congrArg Subtype.val hxy
          have heq := monogonMap_injective hzw
          subst w
          exact Relation.EqvGen.refl _
      | inr w =>
          exact baseChildPair_eqvGen_inl_inr_of_map_eq z w
            (congrArg Subtype.val hxy)
  | inr z =>
      cases y with
      | inl w =>
          exact Relation.EqvGen.symm _ _
            (baseChildPair_eqvGen_inl_inr_of_map_eq w z
              (congrArg Subtype.val hxy).symm)
      | inr w =>
          exact baseChildPair_eqvGen_inr_inr_of_map_eq z w
            (congrArg Subtype.val hxy)

theorem baseChildGluingMap_injective :
    Function.Injective baseChildGluingMap := by
  intro q r hqr
  induction q using Quotient.inductionOn' with
  | _ x =>
      induction r using Quotient.inductionOn' with
      | _ y =>
          apply Quotient.sound
          apply baseChildPairMap_eqvGen_of_eq
          simpa only [baseChildGluingMap_mk] using hqr

/-! ## Surjectivity onto the teardrop -/

theorem collarCirclePoint_eq_cusp_of_chordHeight_eq_zero
    (z : PolygonCell 2) (hs : chordHeight z = 0) :
    (collarCirclePoint z).val = 1 := by
  change collarCircleValue z = 1
  unfold collarCircleValue
  rw [hs]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  have hsSq := chordHeight_sq z
  rw [hs] at hsSq
  exact_mod_cast (by nlinarith [hsSq] :
    z.val.re ^ 2 = (1 : ℝ))

/-- Every radial scale between one half and one is realized by a unique vertical chord in the
digon collar, for any non-cusp teardrop boundary direction. -/
theorem exists_collarMap_eq_smul_teardropMap
    (q : PolygonCell 1) (hqnorm : ‖q.val‖ = 1)
    (hqcusp : q.val ≠ 1) {a : ℝ}
    (haHalf : (2 : ℝ)⁻¹ ≤ a) (haOne : a ≤ 1) :
    ∃ w : PolygonCell 2,
      collarMap w = (a : ℂ) * teardropMap q := by
  have hqSphere :
      q.val ∈ Metric.sphere (0 : ℂ) 1 := by
    exact mem_sphere_zero_iff_norm.mpr hqnorm
  obtain ⟨i, t, hit⟩ :=
    PolygonCell.exists_side_eq_of_mem_sphere
      (n := 1) (by omega) q hqSphere
  have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
  subst i
  let upper : PolygonCell 2 :=
    PolygonCell.side (0 : Fin 2) (unitInterval.symm t)
  have hcircle :
      collarCirclePoint upper = q := by
    rw [collarCirclePoint_side_zero_digon_symm]
    exact hit
  have hheight : chordHeight upper ≠ 0 := by
    intro hs
    apply hqcusp
    rw [← hcircle]
    exact collarCirclePoint_eq_cusp_of_chordHeight_eq_zero
      upper hs
  let s : ℝ := chordHeight upper
  let y : ℝ := s * (3 - 4 * a)
  have hs0 : 0 ≤ s := chordHeight_nonneg upper
  have hspos : 0 < s := hs0.lt_of_ne' (by
    simpa [s] using hheight)
  have hfactorLower : -1 ≤ 3 - 4 * a := by
    nlinarith
  have hfactorUpper : 3 - 4 * a ≤ 1 := by
    nlinarith
  have hyBounds : -s ≤ y ∧ y ≤ s := by
    dsimp [y]
    constructor <;> nlinarith
  have hySq : y ^ 2 ≤ s ^ 2 := by
    exact sq_le_sq' hyBounds.1 hyBounds.2
  let w : PolygonCell 2 :=
    ⟨Complex.mk upper.val.re y, by
      rw [Metric.mem_closedBall, dist_zero_right]
      have hupperSq := chordHeight_sq upper
      have hnormSq :
          Complex.normSq (Complex.mk upper.val.re y) ≤ 1 := by
        rw [Complex.normSq_apply]
        change
          upper.val.re * upper.val.re + y * y ≤ 1
        nlinarith
      rw [Complex.normSq_eq_norm_sq] at hnormSq
      nlinarith [norm_nonneg (Complex.mk upper.val.re y)]⟩
  have hwHeight : chordHeight w = s := by
    have hwSq := chordHeight_sq w
    have hupperSq := chordHeight_sq upper
    have hwre : w.val.re = upper.val.re := by rfl
    rw [hwre] at hwSq
    have hw0 := chordHeight_nonneg w
    nlinarith
  have hwCircle : collarCirclePoint w = q := by
    rw [← hcircle]
    apply PolygonCell.ext
    unfold collarCirclePoint collarCircleValue
    dsimp only [w]
    rw [hwHeight]
  refine ⟨w, ?_⟩
  have hwHeightNe : chordHeight w ≠ 0 := by
    rw [hwHeight]
    exact hspos.ne'
  rw [collarMap_eq_smul_teardropMap w hwHeightNe,
    hwCircle]
  congr 2
  rw [hwHeight]
  change
    (3 * s ^ 2 - s * y) / (4 * s ^ 2) = a
  dsimp [y]
  field_simp [hspos.ne']
  ring

/-- Every non-cusp teardrop point lies on a unique radial segment from a non-cusp boundary
direction, at a scale in `(0, 1]`. -/
theorem exists_teardrop_boundary_scale
    (z : PolygonCell 1) (hz : z.val ≠ 1) :
    ∃ q : PolygonCell 1, ∃ a : ℝ,
      ‖q.val‖ = 1 ∧ q.val ≠ 1 ∧
        0 < a ∧ a ≤ 1 ∧
          teardropMap z = (a : ℂ) * teardropMap q := by
  let u : ℂ := 1 - z.val
  have hu : u ≠ 0 := by
    intro hu0
    apply hz
    dsimp [u] at hu0
    linear_combination -hu0
  have huSqPos : 0 < Complex.normSq u :=
    Complex.normSq_pos.mpr hu
  have hzNormSq : Complex.normSq z.val ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_le_one z, norm_nonneg z.val]
  have huSqLe : Complex.normSq u ≤ 2 * u.re := by
    rw [Complex.normSq_apply] at hzNormSq
    rw [Complex.normSq_apply]
    dsimp [u]
    simp only [zero_sub]
    nlinarith
  have hurePos : 0 < u.re := by
    nlinarith
  let r : ℝ := 2 * u.re / Complex.normSq u
  have hrPos : 0 < r := by
    dsimp [r]
    positivity
  have hrOne : 1 ≤ r := by
    dsimp [r]
    rw [le_div_iff₀ huSqPos]
    simpa using huSqLe
  let qval : ℂ := 1 - (r : ℂ) * u
  have hqNormSq : Complex.normSq qval = 1 := by
    rw [Complex.normSq_apply]
    simp only [qval, Complex.sub_re, Complex.one_re,
      Complex.re_ofReal_mul, Complex.sub_im, Complex.one_im,
      Complex.im_ofReal_mul, zero_sub]
    have huApply := Complex.normSq_apply u
    dsimp [r]
    field_simp [huSqPos.ne']
    nlinarith
  have hqNorm : ‖qval‖ = 1 := by
    rw [Complex.normSq_eq_norm_sq] at hqNormSq
    nlinarith [norm_nonneg qval]
  let q : PolygonCell 1 :=
    ⟨qval, by
      simp [Metric.mem_closedBall, dist_zero_right,
        hqNorm]⟩
  have hqne : q.val ≠ 1 := by
    intro hq
    have hmul : (r : ℂ) * u = 0 := by
      dsimp [q, qval] at hq
      linear_combination -hq
    rcases mul_eq_zero.mp hmul with hr | hu0
    · have hrCast : (r : ℂ) ≠ 0 := by
        exact_mod_cast hrPos.ne'
      exact hrCast hr
    · exact hu hu0
  let a : ℝ := (r ^ 2)⁻¹
  have haPos : 0 < a := by
    dsimp [a]
    positivity
  have haOne : a ≤ 1 := by
    dsimp [a]
    rw [inv_le_one₀ (by positivity)]
    nlinarith [sq_nonneg r]
  have hscale :
      teardropMap z = (a : ℂ) * teardropMap q := by
    unfold teardropMap
    change u ^ 2 =
      (a : ℂ) * (1 - q.val) ^ 2
    have hqdiff : (1 : ℂ) - q.val = (r : ℂ) * u := by
      dsimp [q, qval]
      ring
    rw [hqdiff, mul_pow]
    dsimp [a]
    have hrne : r ≠ 0 := hrPos.ne'
    push_cast
    field_simp [hrne]
  exact ⟨q, a, by simpa [q] using hqNorm,
    hqne, haPos, haOne, hscale⟩

theorem baseChildGluingMap_surjective :
    Function.Surjective baseChildGluingMap := by
  rintro ⟨x, z, rfl⟩
  by_cases hz : z.val = 1
  · let p : PolygonCell 1 :=
      PolygonCell.side (0 : Fin 1) 0
    refine ⟨@Quotient.mk'' BaseChildPair
      (DiskSquare.paramChildSeamSetoid 0 1) (.inl p), ?_⟩
    apply Subtype.ext
    change monogonMap p = teardropMap z
    have hp : p.val = 1 := by
      dsimp [p]
      change
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin 1) 0) : ℂ) = 1
      simp [PolygonCell.sideAngle]
    unfold monogonMap teardropMap
    rw [hz, hp]
    ring
  · obtain ⟨q, a, hqnorm, hqne, haPos, haOne, hscale⟩ :=
      exists_teardrop_boundary_scale z hz
    by_cases haHalf : a ≤ (2 : ℝ)⁻¹
    · have hb0 : 0 ≤ 2 * a := by positivity
      have hb1 : 2 * a ≤ 1 := by
        norm_num at haHalf ⊢
        linarith
      obtain ⟨v, hv⟩ :=
        smul_teardropMap_mem_range q hb0 hb1
      refine ⟨@Quotient.mk'' BaseChildPair
        (DiskSquare.paramChildSeamSetoid 0 1) (.inl v), ?_⟩
      apply Subtype.ext
      change monogonMap v = teardropMap z
      unfold monogonMap
      rw [hv, hscale]
      push_cast
      norm_num
      ring
    · have haHalf' : (2 : ℝ)⁻¹ ≤ a :=
        le_of_not_ge haHalf
      obtain ⟨w, hw⟩ :=
        exists_collarMap_eq_smul_teardropMap
          q hqnorm hqne haHalf' haOne
      refine ⟨@Quotient.mk'' BaseChildPair
        (DiskSquare.paramChildSeamSetoid 0 1) (.inr w), ?_⟩
      apply Subtype.ext
      change collarMap w = teardropMap z
      rw [hw, hscale]

/-- A monogon glued along its entire side to one side of a digon is a closed disk. -/
noncomputable def baseChildGluingHomeomorph :
    DiskSquare.ParamChildGluing 0 1 ≃ₜ Teardrop := by
  let e : DiskSquare.ParamChildGluing 0 1 ≃ Teardrop :=
    Equiv.ofBijective baseChildGluingMap
      ⟨baseChildGluingMap_injective,
        baseChildGluingMap_surjective⟩
  exact Continuous.homeoOfEquivCompactToT2
    (f := e) baseChildGluingMap.continuous

@[simp]
theorem baseChildGluingHomeomorph_apply
    (q : DiskSquare.ParamChildGluing 0 1) :
    baseChildGluingHomeomorph q = baseChildGluingMap q :=
  rfl

/-- The complete base equivalence from the unsplit monogon to the one-sided-degenerate child
quotient. -/
noncomputable def baseSourceChildGluingHomeomorph :
    PolygonCell 1 ≃ₜ DiskSquare.ParamChildGluing 0 1 :=
  teardropHomeomorph.trans baseChildGluingHomeomorph.symm

/-! ## Exact compatibility with the surviving digon side -/

theorem side_one_digon_val (t : unitInterval) :
    (PolygonCell.side (1 : Fin 2) t : PolygonCell 2).val =
      (Circle.exp (Real.pi * (1 + (t : ℝ))) : ℂ) := by
  change
    (Circle.exp
        (PolygonCell.sideAngle (1 : Fin 2) t) : ℂ) =
      (Circle.exp (Real.pi * (1 + (t : ℝ))) : ℂ)
  congr 2
  unfold PolygonCell.sideAngle
  norm_num
  ring

theorem side_one_digon_im (t : unitInterval) :
    (PolygonCell.side (1 : Fin 2) t : PolygonCell 2).val.im =
      -Real.sin (Real.pi * (t : ℝ)) := by
  rw [side_one_digon_val]
  simp only [Circle.coe_exp,
    Complex.exp_ofReal_mul_I_im]
  have hangle :
      Real.pi * (1 + (t : ℝ)) =
        Real.pi * (t : ℝ) + Real.pi := by ring
  rw [hangle, Real.sin_add_pi]

theorem chordHeight_side_one_digon (t : unitInterval) :
    chordHeight (PolygonCell.side (1 : Fin 2) t) =
      Real.sin (Real.pi * (t : ℝ)) := by
  let z : PolygonCell 2 := PolygonCell.side (1 : Fin 2) t
  let θ : ℝ := Real.pi * (t : ℝ)
  have hθ0 : 0 ≤ θ := mul_nonneg Real.pi_pos.le t.property.1
  have hθπ : θ ≤ Real.pi := by
    dsimp [θ]
    nlinarith [Real.pi_pos, t.property.2]
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 hθπ
  have him : z.val.im = -Real.sin θ := by
    simpa [z, θ] using side_one_digon_im t
  have hnormSq : Complex.normSq z.val = 1 := by
    have hmem :=
      PolygonCell.side_mem_sphere (1 : Fin 2) t
    rw [Metric.mem_sphere, Complex.dist_eq,
      sub_zero] at hmem
    rw [Complex.normSq_eq_norm_sq, hmem]
    norm_num
  rw [Complex.normSq_apply] at hnormSq
  have hsSq := chordHeight_sq z
  have hs0 := chordHeight_nonneg z
  change chordHeight z = Real.sin θ
  rw [him] at hnormSq
  nlinarith

theorem collarCirclePoint_side_one_digon (t : unitInterval) :
    collarCirclePoint (PolygonCell.side (1 : Fin 2) t) =
      PolygonCell.side (0 : Fin 1) t := by
  apply PolygonCell.ext
  let z : PolygonCell 2 := PolygonCell.side (1 : Fin 2) t
  have hheight :
      chordHeight z = Real.sin (Real.pi * (t : ℝ)) := by
    simpa [z] using chordHeight_side_one_digon t
  have him :
      z.val.im = -Real.sin (Real.pi * (t : ℝ)) := by
    simpa [z] using side_one_digon_im t
  have hlower :
      ((z.val.re : ℂ) -
          (chordHeight z : ℂ) * Complex.I) = z.val := by
    apply Complex.ext
    · simp
    · simp only [Complex.sub_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, zero_mul, mul_one, add_zero]
      rw [hheight, him]
      ring
  change collarCircleValue z =
    (PolygonCell.side (0 : Fin 1) t : PolygonCell 1).val
  unfold collarCircleValue
  rw [hlower]
  rw [side_one_digon_val]
  change
    ((Circle.exp (Real.pi * (1 + (t : ℝ))) : ℂ) ^ 2) =
      (Circle.exp
        (PolygonCell.sideAngle (0 : Fin 1) t) : ℂ)
  rw [pow_two, ← Circle.coe_mul, ← Circle.exp_add]
  apply congrArg (fun q : Circle ↦ (q : ℂ))
  apply Circle.exp_eq_exp.mpr
  refine ⟨1, ?_⟩
  simp only [PolygonCell.sideAngle, Fin.val_zero,
    Nat.cast_one, div_one, Int.cast_one, one_mul]
  ring

theorem collarMap_eq_teardropMap_collarCirclePoint_of_im_eq_neg
    (z : PolygonCell 2)
    (hy : z.val.im = -chordHeight z) :
    collarMap z = teardropMap (collarCirclePoint z) := by
  unfold collarMap
  rw [hy, teardropMap_collarCirclePoint]
  push_cast
  ring

theorem collarMap_old_side (t : unitInterval) :
    collarMap (PolygonCell.side (1 : Fin 2) t) =
      teardropMap (PolygonCell.side (0 : Fin 1) t) := by
  rw [collarMap_eq_teardropMap_collarCirclePoint_of_im_eq_neg,
    collarCirclePoint_side_one_digon]
  rw [side_one_digon_im, chordHeight_side_one_digon]

/-- In the base one-sided-degenerate P2 equivalence, the source side is exactly the surviving
digon side. -/
theorem baseSourceChildGluingHomeomorph_side
    (t : unitInterval) :
    baseSourceChildGluingHomeomorph
        (PolygonCell.side (0 : Fin 1) t) =
      @Quotient.mk'' BaseChildPair
        (DiskSquare.paramChildSeamSetoid 0 1)
        (.inr (PolygonCell.side (1 : Fin 2) t)) := by
  apply baseChildGluingHomeomorph.injective
  rw [baseSourceChildGluingHomeomorph,
    Homeomorph.trans_apply, Homeomorph.apply_symm_apply,
    baseChildGluingHomeomorph_apply,
    baseChildGluingMap_mk]
  apply Subtype.ext
  rw [teardropHomeomorph_apply_val,
    baseChildPairMap_inr]
  exact (collarMap_old_side t).symm

/-! ## Transport to an arbitrary positive surviving side count -/

/-- Boundary weights which make side zero fill one digon semicircle and divide the other
semicircle equally among the `r` old sides. -/
def rightDegenerateWeights (r : ℕ) : List ℕ :=
  r :: List.replicate r 1

@[simp]
theorem rightDegenerateWeights_length (r : ℕ) :
    (rightDegenerateWeights r).length = r + 1 := by
  simp [rightDegenerateWeights]

@[simp]
theorem rightDegenerateWeights_sum (r : ℕ) :
    (rightDegenerateWeights r).sum = 2 * r := by
  simp [rightDegenerateWeights]
  omega

theorem rightDegenerateWeights_positive
    {r : ℕ} (hr : 0 < r) :
    WeightedCircle.Positive (rightDegenerateWeights r) := by
  intro w hw
  simp only [rightDegenerateWeights, List.mem_cons,
    List.mem_replicate] at hw
  rcases hw with rfl | ⟨_, rfl⟩
  · exact hr
  · norm_num

theorem rightDegenerateWeights_ne_nil (r : ℕ) :
    rightDegenerateWeights r ≠ [] := by
  simp [rightDegenerateWeights]

theorem rightDegenerateWeights_get_zero (r : ℕ) :
    (rightDegenerateWeights r).get
        ⟨0, by simp⟩ = r := by
  simp [rightDegenerateWeights]

theorem rightDegenerateWeights_take_succ
    (r : ℕ) (i : Fin r) :
    (rightDegenerateWeights r).take (i.val + 1) =
      r :: List.replicate i.val 1 := by
  simp [rightDegenerateWeights, List.take_succ_cons]

theorem rightDegenerateWeights_get_succ
    (r : ℕ) (i : Fin r) :
    (rightDegenerateWeights r).get
        ⟨i.val + 1, by
          simp only [rightDegenerateWeights_length]
          omega⟩ = 1 := by
  simp [rightDegenerateWeights]

/-- The common parameter occupied by old side `i` inside the surviving digon semicircle. -/
noncomputable def oldSideParameter
    {r : ℕ} (hr : 0 < r) (i : Fin r)
    (t : unitInterval) : unitInterval :=
  ⟨((i.val : ℝ) + (t : ℝ)) / r,
    div_nonneg (add_nonneg (Nat.cast_nonneg _) t.property.1)
      (Nat.cast_nonneg _),
    by
      rw [div_le_one (by positivity)]
      have hi : (i.val : ℝ) + 1 ≤ r := by
        exact_mod_cast i.isLt
      linarith [t.property.2]⟩

/-- Reparameterize the `(r+1)`-gon boundary as a digon boundary, assigning the entire first
semicircle to the fresh side. -/
noncomputable def rightBoundaryHomeomorph
    (r : ℕ) (hr : 0 < r) : Circle ≃ₜ Circle :=
  WeightedCircle.circleHomeomorph
    (rightDegenerateWeights r)
    (rightDegenerateWeights_positive hr)
    (rightDegenerateWeights_ne_nil r)

/-- Radially extend the weighted boundary map from the surviving child to a digon. -/
noncomputable def rightCellHomeomorph
    (r : ℕ) (hr : 0 < r) :
    PolygonCell (r + 1) ≃ₜ PolygonCell 2 :=
  PolygonCell.radialHomeomorph
    (rightBoundaryHomeomorph r hr)

/-- Forget the side subdivision on the unsplit source disk. -/
noncomputable def sourceCellHomeomorph
    (r : ℕ) : PolygonCell r ≃ₜ PolygonCell 1 :=
  PolygonCell.radialHomeomorph (Homeomorph.refl Circle)

theorem rightBoundaryHomeomorph_fresh
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    rightBoundaryHomeomorph r hr
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin (r + 1)) t)) =
      Circle.exp
        (PolygonCell.sideAngle (0 : Fin 2) t) := by
  have h :=
    WeightedCircle.circleHomeomorph_exp_index_add'
      (rightDegenerateWeights r)
      (rightDegenerateWeights_positive hr)
      (rightDegenerateWeights_ne_nil r)
      ⟨0, by simp⟩ t
  rw [show PolygonCell.sideAngle (0 : Fin (r + 1)) t =
      2 * Real.pi / (rightDegenerateWeights r).length *
        ((0 : ℝ) + (t : ℝ)) by
    unfold PolygonCell.sideAngle
    simp only [rightDegenerateWeights_length,
      Fin.val_zero, Nat.cast_zero, zero_add]
    ring]
  unfold rightBoundaryHomeomorph
  have h' := h
  simp only [Nat.cast_zero, zero_add] at h'
  simp only [zero_add]
  rw [h']
  apply Circle.exp_eq_exp.mpr
  refine ⟨0, ?_⟩
  simp only [rightDegenerateWeights_sum,
    List.take_zero, List.sum_nil,
    rightDegenerateWeights_get_zero,
    Nat.cast_zero, zero_add, Int.cast_zero,
    zero_mul, add_zero]
  unfold PolygonCell.sideAngle
  simp only [Fin.val_zero, Nat.cast_zero, zero_add]
  have hrReal : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp [hrReal]

theorem rightBoundaryHomeomorph_old
    (r : ℕ) (hr : 0 < r) (i : Fin r)
    (t : unitInterval) :
    rightBoundaryHomeomorph r hr
        (Circle.exp
          (PolygonCell.sideAngle (i.addNat 1) t)) =
      Circle.exp
        (PolygonCell.sideAngle (1 : Fin 2)
          (oldSideParameter hr i t)) := by
  let j : Fin (rightDegenerateWeights r).length :=
    ⟨i.val + 1, by
      simp only [rightDegenerateWeights_length]
      omega⟩
  have h :=
    WeightedCircle.circleHomeomorph_exp_index_add'
      (rightDegenerateWeights r)
      (rightDegenerateWeights_positive hr)
      (rightDegenerateWeights_ne_nil r) j t
  rw [show PolygonCell.sideAngle (i.addNat 1) t =
      2 * Real.pi / (rightDegenerateWeights r).length *
        ((j : ℝ) + (t : ℝ)) by
    unfold PolygonCell.sideAngle
    simp only [rightDegenerateWeights_length, j,
      Fin.val_addNat]
    ring]
  unfold rightBoundaryHomeomorph
  rw [h]
  apply Circle.exp_eq_exp.mpr
  refine ⟨0, ?_⟩
  have hget :
      (rightDegenerateWeights r).get j = 1 := by
    dsimp [j]
    exact rightDegenerateWeights_get_succ r i
  rw [hget]
  rw [rightDegenerateWeights_take_succ]
  simp only [rightDegenerateWeights_sum,
    List.sum_cons, List.sum_replicate,
    nsmul_eq_mul, mul_one, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat,
    Int.cast_zero, zero_mul, add_zero]
  unfold PolygonCell.sideAngle oldSideParameter
  simp only [Fin.val_one, Nat.cast_one]
  have hrReal : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  push_cast
  field_simp [hrReal]
  ring

theorem rightCellHomeomorph_fresh
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    rightCellHomeomorph r hr
        (PolygonCell.side (0 : Fin (r + 1)) t) =
      PolygonCell.side (0 : Fin 2) t := by
  unfold rightCellHomeomorph
  change
    PolygonCell.radialHomeomorph
        (rightBoundaryHomeomorph r hr)
        (PolygonCell.ofCircle (r + 1)
          (Circle.exp
            (PolygonCell.sideAngle (0 : Fin (r + 1)) t))) =
      PolygonCell.ofCircle 2
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin 2) t))
  rw [PolygonCell.radialHomeomorph_ofCircle,
    rightBoundaryHomeomorph_fresh]

theorem rightCellHomeomorph_old
    (r : ℕ) (hr : 0 < r) (i : Fin r)
    (t : unitInterval) :
    rightCellHomeomorph r hr
        (PolygonCell.side (i.addNat 1) t) =
      PolygonCell.side (1 : Fin 2)
        (oldSideParameter hr i t) := by
  unfold rightCellHomeomorph
  change
    PolygonCell.radialHomeomorph
        (rightBoundaryHomeomorph r hr)
        (PolygonCell.ofCircle (r + 1)
          (Circle.exp
            (PolygonCell.sideAngle (i.addNat 1) t))) =
      PolygonCell.ofCircle 2
        (Circle.exp
          (PolygonCell.sideAngle (1 : Fin 2)
            (oldSideParameter hr i t)))
  rw [PolygonCell.radialHomeomorph_ofCircle,
    rightBoundaryHomeomorph_old]

theorem sourceCellHomeomorph_side
    (r : ℕ) (hr : 0 < r) (i : Fin r)
    (t : unitInterval) :
    sourceCellHomeomorph r
        (PolygonCell.side i t) =
      PolygonCell.side (0 : Fin 1)
        (oldSideParameter hr i t) := by
  unfold sourceCellHomeomorph
  change
    PolygonCell.radialHomeomorph
        (Homeomorph.refl Circle)
        (PolygonCell.ofCircle r
          (Circle.exp (PolygonCell.sideAngle i t))) =
      PolygonCell.ofCircle 1
        (Circle.exp
          (PolygonCell.sideAngle (0 : Fin 1)
            (oldSideParameter hr i t)))
  rw [PolygonCell.radialHomeomorph_ofCircle]
  apply congrArg (PolygonCell.ofCircle 1)
  apply Circle.exp_eq_exp.mpr
  refine ⟨0, ?_⟩
  unfold PolygonCell.sideAngle oldSideParameter
  simp only [Fin.val_zero, Nat.cast_zero,
    Nat.cast_one, zero_add, div_one,
    Int.cast_zero, zero_mul, add_zero]
  ring

/-- Simultaneously straighten a one-sided-degenerate child pair to the base monogon--digon
pair. -/
noncomputable def childPairBaseHomeomorph
    (r : ℕ) (hr : 0 < r) :
    DiskSquare.ChildPair 0 r ≃ₜ BaseChildPair :=
  Homeomorph.sumCongr
    (Homeomorph.refl (PolygonCell 1))
    (rightCellHomeomorph r hr)

@[simp]
theorem childPairBaseHomeomorph_inl
    (r : ℕ) (hr : 0 < r) (z : PolygonCell 1) :
    childPairBaseHomeomorph r hr (.inl z) = .inl z :=
  rfl

@[simp]
theorem childPairBaseHomeomorph_inr
    (r : ℕ) (hr : 0 < r)
    (z : PolygonCell (r + 1)) :
    childPairBaseHomeomorph r hr (.inr z) =
      .inr (rightCellHomeomorph r hr z) :=
  rfl

theorem rightCellHomeomorph_symm_fresh
    (r : ℕ) (hr : 0 < r) (t : unitInterval) :
    (rightCellHomeomorph r hr).symm
        (PolygonCell.side (0 : Fin 2) t) =
      PolygonCell.side (0 : Fin (r + 1)) t := by
  apply (rightCellHomeomorph r hr).injective
  rw [Homeomorph.apply_symm_apply,
    rightCellHomeomorph_fresh]

theorem childPairBase_generator_map
    (r : ℕ) (hr : 0 < r)
    {x y : DiskSquare.ChildPair 0 r}
    (hxy : DiskSquare.ParamChildSeamGenerator 0 r x y) :
    DiskSquare.ParamChildSeamGenerator 0 1
      (childPairBaseHomeomorph r hr x)
      (childPairBaseHomeomorph r hr y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator 0 1
          (.inl (PolygonCell.side (0 : Fin 1) t))
          (.inr
            (rightCellHomeomorph r hr
              (PolygonCell.side (0 : Fin (r + 1))
                (unitInterval.symm t))))
      rw [rightCellHomeomorph_fresh]
      exact DiskSquare.ParamChildSeamGenerator.glue t

theorem childPairBase_generator_comap
    (r : ℕ) (hr : 0 < r)
    {x y : BaseChildPair}
    (hxy : DiskSquare.ParamChildSeamGenerator 0 1 x y) :
    DiskSquare.ParamChildSeamGenerator 0 r
      ((childPairBaseHomeomorph r hr).symm x)
      ((childPairBaseHomeomorph r hr).symm y) := by
  cases hxy with
  | glue t =>
      change
        DiskSquare.ParamChildSeamGenerator 0 r
          (.inl (PolygonCell.side (0 : Fin 1) t))
          (.inr
            ((rightCellHomeomorph r hr).symm
              (PolygonCell.side (0 : Fin 2)
                (unitInterval.symm t))))
      rw [rightCellHomeomorph_symm_fresh]
      exact DiskSquare.ParamChildSeamGenerator.glue t

/-- The weighted child straightening identifies exactly the two generated seam relations. -/
theorem childPairBase_eqvGen_iff
    (r : ℕ) (hr : 0 < r)
    (x y : DiskSquare.ChildPair 0 r) :
    Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 r) x y ↔
      Relation.EqvGen
        (DiskSquare.ParamChildSeamGenerator 0 1)
        (childPairBaseHomeomorph r hr x)
        (childPairBaseHomeomorph r hr y) := by
  constructor
  · intro hxy
    induction hxy with
    | rel _ _ h =>
        exact Relation.EqvGen.rel _ _
          (childPairBase_generator_map r hr h)
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ =>
        exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  · intro hxy
    let e := childPairBaseHomeomorph r hr
    have hcomap :
        ∀ {u v : BaseChildPair},
          Relation.EqvGen
              (DiskSquare.ParamChildSeamGenerator 0 1)
              u v →
            Relation.EqvGen
              (DiskSquare.ParamChildSeamGenerator 0 r)
              (e.symm u) (e.symm v) := by
      intro u v huv
      induction huv with
      | rel _ _ h =>
          exact Relation.EqvGen.rel _ _
            (childPairBase_generator_comap r hr h)
      | refl => exact Relation.EqvGen.refl _
      | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
      | trans _ _ _ _ _ ih₁ ih₂ =>
          exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
    simpa only [e, Homeomorph.symm_apply_apply] using
      hcomap hxy

/-- The arbitrary one-sided-degenerate child quotient is identified with the base
monogon--digon quotient. -/
noncomputable def childGluingBaseHomeomorph
    (r : ℕ) (hr : 0 < r) :
    DiskSquare.ParamChildGluing 0 r ≃ₜ
      DiskSquare.ParamChildGluing 0 1 :=
  Homeomorph.Quotient.congr
    (childPairBaseHomeomorph r hr)
    (childPairBase_eqvGen_iff r hr)

@[simp]
theorem childGluingBaseHomeomorph_mk
    (r : ℕ) (hr : 0 < r)
    (x : DiskSquare.ChildPair 0 r) :
    childGluingBaseHomeomorph r hr
        (@Quotient.mk'' (DiskSquare.ChildPair 0 r)
          (DiskSquare.paramChildSeamSetoid 0 r) x) =
      @Quotient.mk'' BaseChildPair
        (DiskSquare.paramChildSeamSetoid 0 1)
        (childPairBaseHomeomorph r hr x) :=
  rfl

/-- The local source-to-children equivalence for any ordinary-valid right one-sided-degenerate
P2 cut. -/
noncomputable def sourceChildGluingHomeomorph
    (r : ℕ) (hr : 0 < r) :
    PolygonCell r ≃ₜ DiskSquare.ParamChildGluing 0 r :=
  (sourceCellHomeomorph r).trans
    (baseSourceChildGluingHomeomorph.trans
      (childGluingBaseHomeomorph r hr).symm)

/-- Every old source side is carried to the corresponding surviving-child side with its exact
original parameter. -/
theorem sourceChildGluingHomeomorph_side
    (r : ℕ) (hr : 0 < r) (i : Fin r)
    (t : unitInterval) :
    sourceChildGluingHomeomorph r hr
        (PolygonCell.side i t) =
      @Quotient.mk'' (DiskSquare.ChildPair 0 r)
        (DiskSquare.paramChildSeamSetoid 0 r)
        (.inr (PolygonCell.side (i.addNat 1) t)) := by
  apply (childGluingBaseHomeomorph r hr).injective
  rw [sourceChildGluingHomeomorph,
    Homeomorph.trans_apply, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply,
    childGluingBaseHomeomorph_mk,
    childPairBaseHomeomorph_inr,
    sourceCellHomeomorph_side,
    rightCellHomeomorph_old]
  exact baseSourceChildGluingHomeomorph_side
    (oldSideParameter hr i t)

end P2DegenerateDisk

end LeanEval.Topology.ClassificationOfSurfaces
