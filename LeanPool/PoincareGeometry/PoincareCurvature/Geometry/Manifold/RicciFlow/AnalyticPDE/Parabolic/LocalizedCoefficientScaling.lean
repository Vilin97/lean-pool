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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.Parabolic.TimeIndependentHolder
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compactly localized coefficient fields under spatial scaling

For a spatial coefficient `F`, center `c`, scale `r`, and fixed normalized
cutoff `χ`, the centered field

`y ↦ χ y • (F (c + r • y) - F c)`

has parabolic `C^{0,α}` norm of order `|r|`.  Compact support is used
quantitatively through a support radius.  This is what makes freezing a
principal coefficient on the all-space finite cylinder legitimate: affine
pullback alone would preserve its global oscillation.
-/

@[expose] public noncomputable section
open Set

namespace RicciFlow
namespace AnalyticPDE

variable {X V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## Quantitative data from a smooth compactly supported cutoff -/

/-- A `C¹`, compactly supported map on a real normed space has a global
nonnegative Lipschitz constant.  Compact support of the derivative supplies
the uniform derivative bound used by the mean-value theorem. -/
theorem exists_nonneg_lipschitz_bound_of_contDiff_one_hasCompactSupport
    {f : X → V} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    ∃ K ≥ 0, ∀ x y, ‖f x - f y‖ ≤ K * dist x y := by
  have hDfcont : Continuous (fderiv ℝ f) :=
    hf.continuous_fderiv one_ne_zero
  obtain ⟨K, hK⟩ := hDfcont.bounded_above_of_compact_support (hfc.fderiv ℝ)
  have hK0 : 0 ≤ K :=
    (norm_nonneg (fderiv ℝ f 0)).trans (hK 0)
  let Knn : NNReal := ⟨K, hK0⟩
  have hbound : ∀ x, nnnorm (fderiv ℝ f x) ≤ Knn := by
    intro x
    rw [← NNReal.coe_le_coe]
    exact hK x
  have hlip : LipschitzWith Knn f :=
    lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable one_ne_zero) hbound
  refine ⟨K, hK0, ?_⟩
  intro x y
  have hKcoe : (Knn : ℝ) = K := rfl
  rw [← hKcoe]
  simpa [dist_eq_norm] using hlip.dist_le_mul x y

/-- The support of a compactly supported function lies in a closed norm
ball of some positive radius. -/
theorem exists_pos_support_radius_of_hasCompactSupport
    {f : X → V} (hfc : HasCompactSupport f) :
    ∃ R > 0, ∀ x, f x ≠ 0 → ‖x‖ ≤ R := by
  obtain ⟨R, hR, hbound⟩ := hfc.isCompact.isBounded.exists_pos_norm_le
  refine ⟨R, hR, ?_⟩
  intro x hx
  apply hbound x
  exact subset_closure (by simpa [Function.mem_support] using hx)

/-- A fixed normalized cutoff times the oscillation of a coefficient about
the frozen center. -/
def localizedCenteredRescale
    (χ : X → ℝ) (F : X → V) (c : X) (r : ℝ) (y : X) : V :=
  χ y • (F (c + r • y) - F c)

/-- The coefficient oscillation at a point in the cutoff support is bounded
by the scaling factor times the support radius. -/
theorem norm_affine_coefficient_sub_center_le
    {F : X → V} {c y : X} {r KF R : ℝ}
    (hKF : 0 ≤ KF) (hradius : ‖y‖ ≤ R)
    (hF : ∀ x x', ‖F x - F x'‖ ≤ KF * dist x x') :
    ‖F (c + r • y) - F c‖ ≤ KF * |r| * R := by
  calc
    ‖F (c + r • y) - F c‖ ≤ KF * dist (c + r • y) c := hF _ _
    _ = KF * (|r| * ‖y‖) := by
      rw [dist_eq_norm]
      simp [norm_smul, Real.norm_eq_abs]
    _ ≤ KF * (|r| * R) := by gcongr
    _ = KF * |r| * R := by ring

/-- Uniform order-`|r|` bound for the localized centered coefficient. -/
theorem norm_localizedCenteredRescale_le
    {χ : X → ℝ} {F : X → V} {c y : X} {r Bχ KF R : ℝ}
    (hBχ : 0 ≤ Bχ) (hKF : 0 ≤ KF) (hR : 0 ≤ R)
    (hχ : ∀ x, |χ x| ≤ Bχ)
    (hχsupp : ∀ x, χ x ≠ 0 → ‖x‖ ≤ R)
    (hF : ∀ x x', ‖F x - F x'‖ ≤ KF * dist x x') :
    ‖localizedCenteredRescale χ F c r y‖ ≤ Bχ * KF * |r| * R := by
  by_cases hy : χ y = 0
  · simp [localizedCenteredRescale, hy,
      mul_nonneg (mul_nonneg (mul_nonneg hBχ hKF) (abs_nonneg r)) hR]
  · rw [localizedCenteredRescale, norm_smul, Real.norm_eq_abs]
    calc
      |χ y| * ‖F (c + r • y) - F c‖
          ≤ Bχ * (KF * |r| * R) :=
        mul_le_mul (hχ y)
          (norm_affine_coefficient_sub_center_le hKF (hχsupp y hy) hF)
          (norm_nonneg _) hBχ
      _ = Bχ * KF * |r| * R := by ring

/-- Explicit spatial Lipschitz estimate for the localized centered
coefficient.  Every term contains `|r|`; the cutoff does not destroy the
smallness because its support has bounded radius. -/
theorem norm_localizedCenteredRescale_sub_le
    {χ : X → ℝ} {F : X → V} {c x y : X}
    {r Bχ Kχ KF R : ℝ}
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hKF : 0 ≤ KF) (hR : 0 ≤ R)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hχsupp : ∀ z, χ z ≠ 0 → ‖z‖ ≤ R)
    (hF : ∀ z z', ‖F z - F z'‖ ≤ KF * dist z z') :
    ‖localizedCenteredRescale χ F c r x -
        localizedCenteredRescale χ F c r y‖ ≤
      (Bχ * KF * |r| + Kχ * KF * |r| * R) * dist x y := by
  by_cases hy : χ y = 0
  · by_cases hx : χ x = 0
    · simp [localizedCenteredRescale, hx, hy,
        mul_nonneg
          (add_nonneg
            (mul_nonneg (mul_nonneg hBχ hKF) (abs_nonneg r))
            (mul_nonneg
              (mul_nonneg (mul_nonneg hKχ hKF) (abs_nonneg r)) hR))
          dist_nonneg]
    · simp only [localizedCenteredRescale, hy, zero_smul, sub_zero,
        norm_smul, Real.norm_eq_abs]
      have hχx : |χ x| ≤ Kχ * dist x y := by
        simpa [hy] using hχlip x y
      have hFx := norm_affine_coefficient_sub_center_le
        (c := c) (y := x) (r := r) hKF (hχsupp x hx) hF
      calc
        |χ x| * ‖F (c + r • x) - F c‖
            ≤ (Kχ * dist x y) * (KF * |r| * R) :=
          mul_le_mul hχx hFx (norm_nonneg _)
            (mul_nonneg hKχ dist_nonneg)
        _ = (Kχ * KF * |r| * R) * dist x y := by ring
        _ ≤ (Bχ * KF * |r| + Kχ * KF * |r| * R) * dist x y := by
          apply mul_le_mul_of_nonneg_right _ dist_nonneg
          exact le_add_of_nonneg_left
            (mul_nonneg (mul_nonneg hBχ hKF) (abs_nonneg r))
  · have hFy := norm_affine_coefficient_sub_center_le
      (c := c) (y := y) (r := r) hKF (hχsupp y hy) hF
    have hFxy :
        ‖(F (c + r • x) - F c) - (F (c + r • y) - F c)‖ ≤
          KF * |r| * dist x y := by
      calc
        ‖(F (c + r • x) - F c) - (F (c + r • y) - F c)‖
            = ‖F (c + r • x) - F (c + r • y)‖ := by congr 1 <;> abel
        _ ≤ KF * dist (c + r • x) (c + r • y) := hF _ _
        _ = KF * (|r| * dist x y) := by
          rw [dist_add_left, dist_smul₀, Real.norm_eq_abs]
        _ = KF * |r| * dist x y := by ring
    have hdecomp :
        localizedCenteredRescale χ F c r x -
            localizedCenteredRescale χ F c r y =
          χ x • ((F (c + r • x) - F c) - (F (c + r • y) - F c)) +
            (χ x - χ y) • (F (c + r • y) - F c) := by
      simp only [localizedCenteredRescale]
      module
    rw [hdecomp]
    calc
      ‖χ x • ((F (c + r • x) - F c) - (F (c + r • y) - F c)) +
          (χ x - χ y) • (F (c + r • y) - F c)‖
          ≤ ‖χ x • ((F (c + r • x) - F c) - (F (c + r • y) - F c))‖ +
              ‖(χ x - χ y) • (F (c + r • y) - F c)‖ := norm_add_le _ _
      _ = |χ x| * ‖(F (c + r • x) - F c) - (F (c + r • y) - F c)‖ +
            |χ x - χ y| * ‖F (c + r • y) - F c‖ := by
          simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ Bχ * (KF * |r| * dist x y) +
            (Kχ * dist x y) * (KF * |r| * R) := by
          gcongr
          exact hχ x
          exact hχlip x y
      _ = (Bχ * KF * |r| + Kχ * KF * |r| * R) * dist x y := by ring

/-- The localized centered coefficient as a genuine parabolic Hölder-space
element on an arbitrary time-space domain. -/
def ParabolicC0AlphaSpace.localizedCenteredRescale
    {α Bχ Kχ KF R : ℝ}
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hKF : 0 ≤ KF) (hR : 0 ≤ R)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (F : X → V) (c : X) (r : ℝ)
    (s : Set (ℝ × X))
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hχsupp : ∀ z, χ z ≠ 0 → ‖z‖ ≤ R)
    (hF : ∀ z z', ‖F z - F z'‖ ≤ KF * dist z z') :
    ParabolicC0AlphaSpace X V α s :=
  ParabolicC0AlphaSpace.ofSpatialBoundedLipschitz
    (mul_nonneg (mul_nonneg (mul_nonneg hBχ hKF) (abs_nonneg r)) hR)
    (add_nonneg
      (mul_nonneg (mul_nonneg hBχ hKF) (abs_nonneg r))
      (mul_nonneg (mul_nonneg (mul_nonneg hKχ hKF) (abs_nonneg r)) hR))
    hα hα1 (AnalyticPDE.localizedCenteredRescale χ F c r) s
    (fun y _ => AnalyticPDE.norm_localizedCenteredRescale_le
      hBχ hKF hR hχ hχsupp hF)
    (fun x _ y _ => AnalyticPDE.norm_localizedCenteredRescale_sub_le
      hBχ hKχ hKF hR hχ hχlip hχsupp hF)

@[simp] theorem ParabolicC0AlphaSpace.toFun_localizedCenteredRescale
    {α Bχ Kχ KF R : ℝ}
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hKF : 0 ≤ KF) (hR : 0 ≤ R)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (F : X → V) (c : X) (r : ℝ)
    (s : Set (ℝ × X))
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hχsupp : ∀ z, χ z ≠ 0 → ‖z‖ ≤ R)
    (hF : ∀ z z', ‖F z - F z'‖ ≤ KF * dist z z')
    (z : ℝ × X) :
    ParabolicC0AlphaSpace.toFun
        (ParabolicC0AlphaSpace.localizedCenteredRescale
          hBχ hKχ hKF hR hα hα1 χ F c r s hχ hχlip hχsupp hF) z =
      AnalyticPDE.localizedCenteredRescale χ F c r z.2 :=
  rfl

/-- Quantitative order-`|r|` parabolic Hölder norm estimate. -/
theorem ParabolicC0AlphaSpace.norm_localizedCenteredRescale_le
    {α Bχ Kχ KF R : ℝ}
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hKF : 0 ≤ KF) (hR : 0 ≤ R)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (F : X → V) (c : X) (r : ℝ)
    (s : Set (ℝ × X))
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hχsupp : ∀ z, χ z ≠ 0 → ‖z‖ ≤ R)
    (hF : ∀ z z', ‖F z - F z'‖ ≤ KF * dist z z') :
    ‖ParabolicC0AlphaSpace.localizedCenteredRescale
        hBχ hKχ hKF hR hα hα1 χ F c r s hχ hχlip hχsupp hF‖ ≤
      |r| * (3 * Bχ * KF * R + Bχ * KF + Kχ * KF * R) := by
  refine (ParabolicC0AlphaSpace.norm_ofSpatialBoundedLipschitz_le
    (mul_nonneg (mul_nonneg (mul_nonneg hBχ hKF) (abs_nonneg r)) hR)
    (add_nonneg
      (mul_nonneg (mul_nonneg hBχ hKF) (abs_nonneg r))
      (mul_nonneg (mul_nonneg (mul_nonneg hKχ hKF) (abs_nonneg r)) hR))
    hα hα1 (AnalyticPDE.localizedCenteredRescale χ F c r) s
    (fun y _ => AnalyticPDE.norm_localizedCenteredRescale_le
      hBχ hKF hR hχ hχsupp hF)
    (fun x _ y _ => AnalyticPDE.norm_localizedCenteredRescale_sub_le
      hBχ hKχ hKF hR hχ hχlip hχsupp hF)).trans_eq ?_
  ring

/-! ## Non-centered lower-order fields -/

/-- A fixed normalized cutoff times a coefficient sampled at scale `r`. -/
def localizedRescale
    (χ : X → ℝ) (F : X → V) (c : X) (r : ℝ) (y : X) : V :=
  χ y • F (c + r • y)

/-- Uniform bound for a cutoff coefficient sampled at scale `r`. -/
theorem norm_localizedRescale_le
    {χ : X → ℝ} {F : X → V} {c y : X} {r Bχ BF : ℝ}
    (hBχ : 0 ≤ Bχ) (hBF : 0 ≤ BF)
    (hχ : ∀ x, |χ x| ≤ Bχ) (hF : ∀ x, ‖F x‖ ≤ BF) :
    ‖localizedRescale χ F c r y‖ ≤ Bχ * BF := by
  rw [localizedRescale, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul (hχ y) (hF _) (norm_nonneg _) hBχ

/-- Spatial Lipschitz bound for a cutoff coefficient sampled at scale `r`. -/
theorem norm_localizedRescale_sub_le
    {χ : X → ℝ} {F : X → V} {c x y : X}
    {r Bχ Kχ BF KF : ℝ}
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hBF : 0 ≤ BF) (hKF : 0 ≤ KF)
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hFb : ∀ z, ‖F z‖ ≤ BF)
    (hFlip : ∀ z z', ‖F z - F z'‖ ≤ KF * dist z z') :
    ‖localizedRescale χ F c r x - localizedRescale χ F c r y‖ ≤
      (Bχ * KF * |r| + Kχ * BF) * dist x y := by
  have hFxy : ‖F (c + r • x) - F (c + r • y)‖ ≤
      KF * |r| * dist x y := by
    calc
      ‖F (c + r • x) - F (c + r • y)‖
          ≤ KF * dist (c + r • x) (c + r • y) := hFlip _ _
      _ = KF * (|r| * dist x y) := by
        rw [dist_add_left, dist_smul₀, Real.norm_eq_abs]
      _ = KF * |r| * dist x y := by ring
  have hdecomp :
      localizedRescale χ F c r x - localizedRescale χ F c r y =
        χ x • (F (c + r • x) - F (c + r • y)) +
          (χ x - χ y) • F (c + r • y) := by
    simp only [localizedRescale]
    module
  rw [hdecomp]
  calc
    ‖χ x • (F (c + r • x) - F (c + r • y)) +
        (χ x - χ y) • F (c + r • y)‖
        ≤ ‖χ x • (F (c + r • x) - F (c + r • y))‖ +
            ‖(χ x - χ y) • F (c + r • y)‖ := norm_add_le _ _
    _ = |χ x| * ‖F (c + r • x) - F (c + r • y)‖ +
          |χ x - χ y| * ‖F (c + r • y)‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ Bχ * (KF * |r| * dist x y) +
          (Kχ * dist x y) * BF := by
        gcongr
        exact hχ x
        exact hχlip x y
        exact hFb _
    _ = (Bχ * KF * |r| + Kχ * BF) * dist x y := by ring

/-- A cutoff coefficient sampled at scale `r`, as a parabolic Hölder-space
element on an arbitrary time-space domain. -/
def ParabolicC0AlphaSpace.localizedRescale
    {α Bχ Kχ BF KF : ℝ}
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hBF : 0 ≤ BF) (hKF : 0 ≤ KF)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (F : X → V) (c : X) (r : ℝ)
    (s : Set (ℝ × X))
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hFb : ∀ z, ‖F z‖ ≤ BF)
    (hFlip : ∀ z z', ‖F z - F z'‖ ≤ KF * dist z z') :
    ParabolicC0AlphaSpace X V α s :=
  ParabolicC0AlphaSpace.ofSpatialBoundedLipschitz
    (mul_nonneg hBχ hBF)
    (add_nonneg
      (mul_nonneg (mul_nonneg hBχ hKF) (abs_nonneg r))
      (mul_nonneg hKχ hBF))
    hα hα1 (AnalyticPDE.localizedRescale χ F c r) s
    (fun y _ => AnalyticPDE.norm_localizedRescale_le hBχ hBF hχ hFb)
    (fun x _ y _ => AnalyticPDE.norm_localizedRescale_sub_le
      hBχ hKχ hBF hKF hχ hχlip hFb hFlip)

@[simp] theorem ParabolicC0AlphaSpace.toFun_localizedRescale
    {α Bχ Kχ BF KF : ℝ}
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hBF : 0 ≤ BF) (hKF : 0 ≤ KF)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (F : X → V) (c : X) (r : ℝ)
    (s : Set (ℝ × X))
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hFb : ∀ z, ‖F z‖ ≤ BF)
    (hFlip : ∀ z z', ‖F z - F z'‖ ≤ KF * dist z z')
    (z : ℝ × X) :
    ParabolicC0AlphaSpace.toFun
        (ParabolicC0AlphaSpace.localizedRescale
          hBχ hKχ hBF hKF hα hα1 χ F c r s hχ hχlip hFb hFlip) z =
      AnalyticPDE.localizedRescale χ F c r z.2 :=
  rfl

/-- Uniform parabolic Hölder norm estimate for a cutoff sampled field. -/
theorem ParabolicC0AlphaSpace.norm_localizedRescale_le
    {α Bχ Kχ BF KF : ℝ}
    (hBχ : 0 ≤ Bχ) (hKχ : 0 ≤ Kχ) (hBF : 0 ≤ BF) (hKF : 0 ≤ KF)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (χ : X → ℝ) (F : X → V) (c : X) (r : ℝ)
    (s : Set (ℝ × X))
    (hχ : ∀ z, |χ z| ≤ Bχ)
    (hχlip : ∀ z z', |χ z - χ z'| ≤ Kχ * dist z z')
    (hFb : ∀ z, ‖F z‖ ≤ BF)
    (hFlip : ∀ z z', ‖F z - F z'‖ ≤ KF * dist z z') :
    ‖ParabolicC0AlphaSpace.localizedRescale
        hBχ hKχ hBF hKF hα hα1 χ F c r s hχ hχlip hFb hFlip‖ ≤
      3 * Bχ * BF + Bχ * KF * |r| + Kχ * BF := by
  refine (ParabolicC0AlphaSpace.norm_ofSpatialBoundedLipschitz_le
    (mul_nonneg hBχ hBF)
    (add_nonneg
      (mul_nonneg (mul_nonneg hBχ hKF) (abs_nonneg r))
      (mul_nonneg hKχ hBF))
    hα hα1 (AnalyticPDE.localizedRescale χ F c r) s
    (fun y _ => AnalyticPDE.norm_localizedRescale_le hBχ hBF hχ hFb)
    (fun x _ y _ => AnalyticPDE.norm_localizedRescale_sub_le
      hBχ hKχ hBF hKF hχ hχlip hFb hFlip)).trans_eq ?_
  ring

end AnalyticPDE
end RicciFlow
