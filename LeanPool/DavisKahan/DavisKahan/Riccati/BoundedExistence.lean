/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedSharpEstimates
public import Mathlib.Topology.MetricSpace.Contracting

/-! # Bounded Existence -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Local bounded Riccati existence by contraction

This leaf module constructs the locally selected bounded Riccati solution under
an interval/exterior spectral gap and the conservative threshold
`2 * ‖B01‖ < d`.

The construction centers the two diagonal operators at the midpoint of the
interval.  The centered exterior block has a bounded two-sided inverse, while
the centered interval block has norm at most the interval radius.  These data
define a nonlinear self-map of the closed operator-norm unit ball.  The gap
threshold makes that map strictly contractive and keeps its image in the open
unit ball.  Banach's fixed-point theorem then supplies a contractive Riccati
solution.  The algebraic smaller-root estimate is applied afterwards.
-/

namespace TauCeti
namespace DavisKahanExt

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- Nonlinear map used in the local Riccati fixed-point construction. -/
noncomputable def riccatiIterationMap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (J : E1 →L[ℂ] E1) (B0 : E0 →L[ℂ] E0)
    (X : E0 →L[ℂ] E1) : E0 →L[ℂ] E1 :=
  J ∘L (X ∘L H.B01 ∘L X - H.B10 + X ∘L B0)

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Difference identity for the local Riccati iteration map. -/
theorem riccatiIterationMap_sub
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (J : E1 →L[ℂ] E1) (B0 : E0 →L[ℂ] E0)
    (X Y : E0 →L[ℂ] E1) :
    riccatiIterationMap H J B0 X - riccatiIterationMap H J B0 Y =
      J ∘L
        ((X - Y) ∘L H.B01 ∘L X +
          Y ∘L H.B01 ∘L (X - Y) +
          (X - Y) ∘L B0) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [riccatiIterationMap, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sub]
  abel

/-- The iteration map sends the closed unit ball into its open interior. -/
theorem norm_riccatiIterationMap_lt_one
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (J : E1 →L[ℂ] E1) (B0 : E0 →L[ℂ] E0)
    {r d : ℝ} (hr : 0 ≤ r) (hd : 0 < d)
    (hJ : ‖J‖ ≤ (r + d)⁻¹) (hB0 : ‖B0‖ ≤ r)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X : E0 →L[ℂ] E1} (hX : ‖X‖ ≤ 1) :
    ‖riccatiIterationMap H J B0 X‖ < 1 := by
  have hrd : 0 < r + d := by linarith
  have hX0 : 0 ≤ ‖X‖ := norm_nonneg X
  have hXsq : ‖X‖ ^ 2 ≤ 1 := by nlinarith
  have hmain : ‖riccatiIterationMap H J B0 X‖ ≤
      (r + d)⁻¹ *
        (‖H.B01‖ * (1 + ‖X‖ ^ 2) + ‖X‖ * r) := by
    calc
      ‖riccatiIterationMap H J B0 X‖ =
          ‖J ∘L (X ∘L H.B01 ∘L X - H.B10 + X ∘L B0)‖ := rfl
      _ ≤ ‖J‖ * ‖X ∘L H.B01 ∘L X - H.B10 + X ∘L B0‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖J‖ *
          (‖X ∘L H.B01 ∘L X - H.B10‖ + ‖X ∘L B0‖) := by
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg J)
      _ ≤ ‖J‖ *
          (‖H.B01‖ * (1 + ‖X‖ ^ 2) + ‖X‖ * ‖B0‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg J)
        exact add_le_add (norm_riccati_sylvester_rhs_le H X)
          (ContinuousLinearMap.opNorm_comp_le X B0)
      _ ≤ (r + d)⁻¹ *
          (‖H.B01‖ * (1 + ‖X‖ ^ 2) + ‖X‖ * r) := by
        refine mul_le_mul hJ ?_ (by positivity) (inv_nonneg.mpr hrd.le)
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left hB0 hX0)
  have hinside :
      (r + d)⁻¹ *
          (‖H.B01‖ * (1 + ‖X‖ ^ 2) + ‖X‖ * r) ≤
        (r + d)⁻¹ * (2 * ‖H.B01‖ + r) := by
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hrd.le)
    have hB0' : 0 ≤ ‖H.B01‖ := norm_nonneg H.B01
    have hquad : ‖H.B01‖ * (1 + ‖X‖ ^ 2) ≤ 2 * ‖H.B01‖ := by
      nlinarith
    have hlin : ‖X‖ * r ≤ r := by
      nlinarith
    linarith
  have hratio : (r + d)⁻¹ * (2 * ‖H.B01‖ + r) < 1 := by
    rw [← div_eq_inv_mul]
    exact (div_lt_one hrd).2 (by linarith)
  exact lt_of_le_of_lt (hmain.trans hinside) hratio

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Lipschitz estimate for the iteration map on the closed unit ball. -/
theorem norm_riccatiIterationMap_sub_le
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (J : E1 →L[ℂ] E1) (B0 : E0 →L[ℂ] E0)
    {r d : ℝ} (hr : 0 ≤ r) (hd : 0 < d)
    (hJ : ‖J‖ ≤ (r + d)⁻¹) (hB0 : ‖B0‖ ≤ r)
    {X Y : E0 →L[ℂ] E1} (hX : ‖X‖ ≤ 1) (hY : ‖Y‖ ≤ 1) :
    ‖riccatiIterationMap H J B0 X -
        riccatiIterationMap H J B0 Y‖ ≤
      ((r + 2 * ‖H.B01‖) / (r + d)) * ‖X - Y‖ := by
  have hrd : 0 < r + d := by linarith
  have hD0 : 0 ≤ ‖X - Y‖ := norm_nonneg (X - Y)
  have hsum : ‖X‖ + ‖Y‖ ≤ 2 := by linarith
  rw [riccatiIterationMap_sub]
  calc
    ‖J ∘L
        ((X - Y) ∘L H.B01 ∘L X +
          Y ∘L H.B01 ∘L (X - Y) +
          (X - Y) ∘L B0)‖ ≤
        ‖J‖ *
          ‖(X - Y) ∘L H.B01 ∘L X +
            Y ∘L H.B01 ∘L (X - Y) +
            (X - Y) ∘L B0‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖J‖ *
        (‖(X - Y) ∘L H.B01 ∘L X +
            Y ∘L H.B01 ∘L (X - Y)‖ +
          ‖(X - Y) ∘L B0‖) := by
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg J)
    _ ≤ ‖J‖ *
        (‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖X - Y‖ +
          ‖X - Y‖ * ‖B0‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg J)
      exact add_le_add (norm_riccati_solution_sub_rhs_le H X Y)
        (ContinuousLinearMap.opNorm_comp_le (X - Y) B0)
    _ ≤ (r + d)⁻¹ *
        (‖H.B01‖ * 2 * ‖X - Y‖ + ‖X - Y‖ * r) := by
      refine mul_le_mul hJ ?_ (by positivity) (inv_nonneg.mpr hrd.le)
      refine add_le_add ?_ ?_
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsum (norm_nonneg H.B01)) hD0
      · exact mul_le_mul_of_nonneg_left hB0 hD0
    _ = ((r + 2 * ‖H.B01‖) / (r + d)) * ‖X - Y‖ := by
      rw [div_eq_inv_mul]
      ring

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A fixed point of the shifted iteration map solves the original Riccati
equation. -/
theorem solvesRiccati_of_fixedPoint_riccatiIterationMap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (J : E1 →L[ℂ] E1) (B0 : E0 →L[ℂ] E0)
    (A1c : E1 →L[ℂ] E1) (c : ℝ)
    (hA1c : A1c = H.A1 - algebraMap ℝ (E1 →L[ℂ] E1) c)
    (hB0 : B0 = H.A0 - algebraMap ℝ (E0 →L[ℂ] E0) c)
    (hAJ : A1c ∘L J = ContinuousLinearMap.id ℂ E1)
    {X : E0 →L[ℂ] E1}
    (hfix : Function.IsFixedPt (riccatiIterationMap H J B0) X) :
    SolvesRiccati H X := by
  have hcentered :
      A1c ∘L X - X ∘L B0 = X ∘L H.B01 ∘L X - H.B10 := by
    have hAX : A1c ∘L X =
        X ∘L H.B01 ∘L X - H.B10 + X ∘L B0 := by
      calc
        A1c ∘L X = A1c ∘L riccatiIterationMap H J B0 X := by
          rw [hfix]
        _ = (A1c ∘L J) ∘L
            (X ∘L H.B01 ∘L X - H.B10 + X ∘L B0) := by
          rw [riccatiIterationMap, ← ContinuousLinearMap.comp_assoc]
        _ = X ∘L H.B01 ∘L X - H.B10 + X ∘L B0 := by
          rw [hAJ, ContinuousLinearMap.id_comp]
    rw [hAX]
    abel
  have hscalar :
      algebraMap ℝ (E1 →L[ℂ] E1) c ∘L X =
        X ∘L algebraMap ℝ (E0 →L[ℂ] E0) c := by
    apply ContinuousLinearMap.ext
    intro u
    simp [Algebra.algebraMap_eq_smul_one]
  have horiginal :
      H.A1 ∘L X - X ∘L H.A0 =
        X ∘L H.B01 ∘L X - H.B10 := by
    calc
      H.A1 ∘L X - X ∘L H.A0 = A1c ∘L X - X ∘L B0 := by
        rw [hA1c, hB0, ContinuousLinearMap.sub_comp,
          ContinuousLinearMap.comp_sub]
        rw [hscalar]
        abel
      _ = X ∘L H.B01 ∘L X - H.B10 := hcentered
  unfold SolvesRiccati riccatiDefect
  rw [show H.A1 ∘L X - X ∘L H.A0 =
      X ∘L H.B01 ∘L X - H.B10 from horiginal]
  abel
/-- Under a genuine interval/exterior spectral gap and
`2 * ‖B01‖ < d`, the bounded Riccati equation has a contractive solution.
The selected solution also obeys the exact smaller-root majorant. -/
theorem exists_contractive_riccati_solution_of_spectrum_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d) :
    ∃ X : E0 →L[ℂ] E1,
      SolvesRiccati H X ∧ ‖X‖ < 1 ∧
      ‖X‖ ≤
        2 * ‖H.B01‖ /
          (d + Real.sqrt (d ^ 2 - 4 * ‖H.B01‖ ^ 2)) := by
  set c : ℝ := (left + right) / 2 with hc
  set r : ℝ := (right - left) / 2 with hrdef
  have hr0 : 0 ≤ r := by rw [hrdef]; linarith
  have hrd : 0 < r + d := by linarith
  set A1c : E1 →L[ℂ] E1 :=
    H.A1 - algebraMap ℝ (E1 →L[ℂ] E1) c with hA1c
  set B0c : E0 →L[ℂ] E0 :=
    H.A0 - algebraMap ℝ (E0 →L[ℂ] E0) c with hB0c
  have hA1sa : IsSelfAdjoint H.A1 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint1
  have hA0sa : IsSelfAdjoint H.A0 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint0
  have hA1csa : IsSelfAdjoint A1c := by
    rw [hA1c]
    exact hA1sa.sub
      (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
  have hB0csa : IsSelfAdjoint B0c := by
    rw [hB0c]
    exact hA0sa.sub
      (IsSelfAdjoint.algebraMap _ (IsSelfAdjoint.all c))
  have hA1cspec : ∀ x ∈ spectrum ℝ A1c, r + d ≤ |x| := by
    intro x hx
    rw [hA1c, ← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_sub.mp hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    rw [← hyz]
    rcases hA1spec y hy with hleft | hright
    · have hle : y - c ≤ -(r + d) := by
        rw [hc, hrdef]
        linarith
      calc
        r + d ≤ -(y - c) := by linarith
        _ ≤ |y - c| := neg_le_abs _
    · have hge : r + d ≤ y - c := by
        rw [hc, hrdef]
        linarith
      exact hge.trans (le_abs_self _)
  have hB0cspec : spectrum ℝ B0c ⊆ Set.Icc (-r) r := by
    intro x hx
    rw [hB0c, ← spectrum.sub_singleton_eq] at hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Set.mem_sub.mp hx
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hmem := hA0spec hy
    rw [Set.mem_Icc] at hmem
    rw [← hyz, Set.mem_Icc]
    constructor
    · rw [hc, hrdef]
      linarith [hmem.1]
    · rw [hc, hrdef]
      linarith [hmem.2]
  have hB0cnorm : ‖B0c‖ ≤ r :=
    (TauCeti.IsSelfAdjoint.norm_le_iff_spectrum_subset_Icc hB0csa hr0).mpr hB0cspec
  have hA1cunit : IsUnit A1c :=
    TauCeti.isUnit_of_forall_le_abs (A := E1 →L[ℂ] E1) hrd hA1cspec
  set J : E1 →L[ℂ] E1 := Ring.inverse A1c
  have hAJmul : A1c * J = 1 := Ring.mul_inverse_cancel _ hA1cunit
  have hJnorm : ‖J‖ ≤ (r + d)⁻¹ :=
    TauCeti.IsSelfAdjoint.norm_ringInverse_le (A := E1 →L[ℂ] E1) hA1csa hrd hA1cspec
  have hAJ : A1c ∘L J = ContinuousLinearMap.id ℂ E1 := by
    rw [← ContinuousLinearMap.mul_def, hAJmul,
      ContinuousLinearMap.one_def]
  let phi : (E0 →L[ℂ] E1) → (E0 →L[ℂ] E1) :=
    riccatiIterationMap H J B0c
  let s : Set (E0 →L[ℂ] E1) := Metric.closedBall 0 1
  have hsComplete : IsComplete s := Metric.isClosed_closedBall.isComplete
  have hsMap : Set.MapsTo phi s s := by
    intro X hXs
    have hXnorm : ‖X‖ ≤ 1 := by
      simpa [s, Metric.mem_closedBall, dist_eq_norm] using hXs
    have hlt : ‖phi X‖ < 1 := by
      exact norm_riccatiIterationMap_lt_one H J B0c hr0 hd hJnorm
        hB0cnorm hsmall hXnorm
    simpa [s, Metric.mem_closedBall, dist_eq_norm] using le_of_lt hlt
  let qR : ℝ := (r + 2 * ‖H.B01‖) / (r + d)
  have hqR0 : 0 ≤ qR := by
    dsimp [qR]
    exact div_nonneg (by nlinarith [norm_nonneg H.B01]) hrd.le
  let q : NNReal := ⟨qR, hqR0⟩
  have hqLt : q < 1 := by
    change qR < 1
    dsimp [qR]
    exact (div_lt_one hrd).2 (by linarith)
  have hcontract :
      ContractingWith q (Set.MapsTo.restrict phi s s hsMap) := by
    refine ⟨hqLt, (lipschitzWith_iff_dist_le_mul).2 ?_⟩
    intro X Y
    change dist (phi (X : E0 →L[ℂ] E1))
        (phi (Y : E0 →L[ℂ] E1)) ≤
      (q : ℝ) * dist (X : E0 →L[ℂ] E1) (Y : E0 →L[ℂ] E1)
    rw [dist_eq_norm, dist_eq_norm]
    change ‖phi (X : E0 →L[ℂ] E1) - phi (Y : E0 →L[ℂ] E1)‖ ≤
      qR * ‖(X : E0 →L[ℂ] E1) - (Y : E0 →L[ℂ] E1)‖
    have hXball :
        (X : E0 →L[ℂ] E1) ∈
          Metric.closedBall (0 : E0 →L[ℂ] E1) 1 := by
      change (X : E0 →L[ℂ] E1) ∈ s
      exact X.2
    have hYball :
        (Y : E0 →L[ℂ] E1) ∈
          Metric.closedBall (0 : E0 →L[ℂ] E1) 1 := by
      change (Y : E0 →L[ℂ] E1) ∈ s
      exact Y.2
    have hXdist : dist (X : E0 →L[ℂ] E1) 0 ≤ 1 :=
      Metric.mem_closedBall.mp hXball
    have hYdist : dist (Y : E0 →L[ℂ] E1) 0 ≤ 1 :=
      Metric.mem_closedBall.mp hYball
    have hXnorm : ‖(X : E0 →L[ℂ] E1)‖ ≤ 1 := by
      simpa [dist_eq_norm] using hXdist
    have hYnorm : ‖(Y : E0 →L[ℂ] E1)‖ ≤ 1 := by
      simpa [dist_eq_norm] using hYdist
    exact norm_riccatiIterationMap_sub_le H J B0c hr0 hd hJnorm
      hB0cnorm hXnorm hYnorm
  have hzero : (0 : E0 →L[ℂ] E1) ∈ s := by
    simp [s]
  obtain ⟨X, hXs, hfix, _hconv, _hrate⟩ :=
    hcontract.exists_fixedPoint' hsComplete hsMap hzero
      (edist_ne_top (0 : E0 →L[ℂ] E1) (phi 0))
  have hXnorm : ‖X‖ ≤ 1 := by
    simpa [s, Metric.mem_closedBall, dist_eq_norm] using hXs
  have hXlt : ‖X‖ < 1 := by
    rw [← hfix]
    exact norm_riccatiIterationMap_lt_one H J B0c hr0 hd hJnorm
      hB0cnorm hsmall hXnorm
  have hXRiccati : SolvesRiccati H X :=
    solvesRiccati_of_fixedPoint_riccatiIterationMap H J B0c A1c c
      hA1c hB0c hAJ hfix
  refine ⟨X, hXRiccati, hXlt, ?_⟩
  exact norm_riccati_solution_le_small_root_of_contractive_spectrum_gap
    H hd hlr hA0spec hA1spec hsmall hXRiccati hXlt

end DavisKahanExt
end TauCeti
