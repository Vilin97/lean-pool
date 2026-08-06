/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# `RellichKondrachov.Geometry.Manifold.Riemannian.ChartLocalLipschitzForward`

Local Lipschitz control for the (forward) extended chart on a Riemannian manifold, measured using
`riemannianEDist`.

## Main result

- `RellichKondrachov.Geometry.Manifold.Riemannian.lipschitzOnWith_extChartAt_ofRiemannianMetric`
-/

namespace RellichKondrachov
namespace Geometry
namespace Manifold
namespace Riemannian

open Set Filter MeasureTheory
open _root_.Manifold _root_.Bundle
open scoped NNReal ENNReal Topology Manifold

local notation "n∞" => (⊤ : WithTop ℕ∞)

section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I n∞ M] [IsManifold I (1 : WithTop ℕ∞) M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-!
`mfderiv`/`mfderivWithin` takes values in spaces of continuous linear maps between tangent spaces.
For the model space `E` (viewed as a manifold), we locally activate the `NormedAddCommGroup` and
`NormedSpace` instances on its tangent spaces so that operator norms are available (following
Mathlib’s approach in `Mathlib.Geometry.Manifold.Riemannian.Basic`).
-/

@[reducible]
private noncomputable def normedAddCommGroupTangentSpaceVectorSpace (x : E) :
    NormedAddCommGroup (TangentSpace (𝓘(ℝ, E)) x) :=
  inferInstanceAs (NormedAddCommGroup E)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace

@[reducible]
private noncomputable def normedSpaceTangentSpaceVectorSpace (x : E) :
    NormedSpace ℝ (TangentSpace (𝓘(ℝ, E)) x) :=
  inferInstanceAs (NormedSpace ℝ E)

attribute [local instance] normedSpaceTangentSpaceVectorSpace

omit [FiniteDimensional ℝ E] [IsManifold I n∞ M] in
/-- Around any point `x`, the (forward) extended chart is Lipschitz on a small Riemannian ball
centered at `x`, with respect to the Riemannian distance. -/
theorem lipschitzOnWith_extChartAt_ofRiemannianMetric
    [EMetricSpace M] [IsRiemannianManifold I M] [RegularSpace M] (x : M) :
    ∃ (C : ℝ≥0), 0 < C ∧ ∃ (r : ℝ≥0), 0 < r ∧
      LipschitzOnWith C (extChartAt I x) {y : M | riemannianEDist I x y < (r : ℝ≥0∞)} := by
  classical
  -- Prefer the `ContinuousLinearMap`-native `SeminormedAddCommGroup` structure on `→L` spaces to
  -- avoid definitional mismatches between `‖_‖ₑ` occurrences.
  letI (y : M) :
      SeminormedAddCommGroup (TangentSpace I y →L[ℝ] TangentSpace (𝓘(ℝ, E)) (extChartAt I x y)) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  -- Start from a local bound on the derivative of `extChartAt I x`.
  rcases eventually_enorm_mfderiv_extChartAt_lt (I := I) x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  let P : Set M := {y | ‖mfderiv I (𝓘(ℝ, E)) (extChartAt I x) y‖ₑ < C}
  have hP : P ∈ 𝓝 x := by
    change (∀ᶠ y in 𝓝 x, y ∈ P)
    filter_upwards [hC] with y hy
    exact hy
  have hx_source : (chartAt H x).source ∈ 𝓝 x := chart_source_mem_nhds H x
  have hU : P ∩ (chartAt H x).source ∈ 𝓝 x := inter_mem hP hx_source
  -- Convert this neighborhood information into a concrete Riemannian ball.
  rcases setOf_riemannianEDist_lt_subset_nhds (I := I) (x := x)
      (s := P ∩ (chartAt H x).source) hU with ⟨c, c_pos, hc⟩
  -- Work on the smaller ball of radius `c/4`, so that short paths between points in the ball stay
  -- inside `{y | riemannianEDist I x y < c}` where the derivative bound holds.
  let r : ℝ≥0 := c / 4
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  refine ⟨r, hr_pos, ?_⟩
  intro y₁ hy₁ y₂ hy₂
  -- Work with `edist` for triangle/commutativity, rewriting back to `riemannianEDist` at the end.
  have hy₁_edist : edist x y₁ < (r : ℝ≥0∞) := by
    have : riemannianEDist I x y₁ < (r : ℝ≥0∞) := by simpa [r] using hy₁
    simpa [IsRiemannianManifold.out (I := I) (M := M)] using this
  have hy₂_edist : edist x y₂ < (r : ℝ≥0∞) := by
    have : riemannianEDist I x y₂ < (r : ℝ≥0∞) := by simpa [r] using hy₂
    simpa [IsRiemannianManifold.out (I := I) (M := M)] using this
  have hy₁x_edist : edist y₁ x < (r : ℝ≥0∞) := by simpa [edist_comm] using hy₁_edist
  have hdist_edist_lt : edist y₁ y₂ < (r : ℝ≥0∞) + (r : ℝ≥0∞) := by
    have htri : edist y₁ y₂ ≤ edist y₁ x + edist x y₂ := edist_triangle _ _ _
    have hsum : edist y₁ x + edist x y₂ < (r : ℝ≥0∞) + (r : ℝ≥0∞) :=
      ENNReal.add_lt_add hy₁x_edist hy₂_edist
    exact lt_of_le_of_lt htri hsum
  have hdist_lt : riemannianEDist I y₁ y₂ < (r : ℝ≥0∞) + (r : ℝ≥0∞) := by
    -- rewrite `edist` as `riemannianEDist`
    simpa [IsRiemannianManifold.out (I := I) (M := M)] using hdist_edist_lt
  have hb_fin : ((C : ℝ≥0∞) * riemannianEDist I y₁ y₂) < ∞ := by
    refine ENNReal.mul_lt_top (by simp) ?_
    have : riemannianEDist I y₁ y₂ < (⊤ : ℝ≥0∞) :=
      lt_of_lt_of_le hdist_lt (by simp)
    exact this
  -- `ε`-approximation and `ENNReal.le_of_forall_pos_le_add` to avoid unfolding `riemannianEDist`.
  have hmain :
      edist (extChartAt I x y₁) (extChartAt I x y₂) ≤ (C : ℝ≥0∞) * riemannianEDist I y₁ y₂ := by
    refine ENNReal.le_of_forall_pos_le_add (a := edist (extChartAt I x y₁) (extChartAt I x y₂))
      (b := (C : ℝ≥0∞) * riemannianEDist I y₁ y₂) ?_
    intro ε ε_pos _hb
    have C_ne : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast (ne_of_gt C_pos)
    let δ : ℝ≥0∞ := min ((ε : ℝ≥0∞) / (C : ℝ≥0∞)) (r : ℝ≥0∞)
    have δ_pos : 0 < δ := by
      have hε : (ε : ℝ≥0∞) ≠ 0 := by exact_mod_cast ε_pos.ne'
      have hεC : 0 < (ε : ℝ≥0∞) / (C : ℝ≥0∞) := ENNReal.div_pos hε (by simp)
      have hc4 : 0 < (r : ℝ≥0∞) := by
        exact_mod_cast hr_pos
      exact lt_min_iff.2 ⟨hεC, hc4⟩
    have hdist_ne_top : riemannianEDist I y₁ y₂ ≠ (⊤ : ℝ≥0∞) :=
      ne_of_lt (lt_of_lt_of_le hdist_lt le_top)
    have hdist_lt' : riemannianEDist I y₁ y₂ < riemannianEDist I y₁ y₂ + δ :=
      ENNReal.lt_add_right hdist_ne_top (ne_of_gt δ_pos)
    rcases exists_lt_of_riemannianEDist_lt (I := I) (x := y₁) (y := y₂)
        (r := riemannianEDist I y₁ y₂ + δ) hdist_lt' with
      ⟨γ, hγ0, hγ1, γ_smooth, hlen⟩
    have hlen_lt_c : pathELength I γ 0 1 < (c : ℝ≥0∞) := by
      have hδ_le : δ ≤ (r : ℝ≥0∞) := min_le_right _ _
      have hδ_ne_top : δ ≠ (⊤ : ℝ≥0∞) := ne_of_lt (lt_of_le_of_lt hδ_le (by simp))
      have hsum_lt : riemannianEDist I y₁ y₂ + δ < ((r : ℝ≥0∞) + (r : ℝ≥0∞)) + (r : ℝ≥0∞) := by
        -- `dist + δ < (r + r) + r`
        simpa [add_assoc] using (ENNReal.add_lt_add_of_lt_of_le hδ_ne_top hdist_lt hδ_le)
      have hc3r : ((r : ℝ≥0∞) + (r : ℝ≥0∞)) + (r : ℝ≥0∞) < (c : ℝ≥0∞) := by
        -- `r = c/4`, so `3r = 3c/4 < c`.
        have : (r + r + r : ℝ≥0) < c := by
          -- cast to ℝ and finish with `nlinarith`
          dsimp [r]
          exact_mod_cast (by nlinarith [show (0 : ℝ) < c by exact_mod_cast c_pos] :
            (c : ℝ) / 4 + (c : ℝ) / 4 + (c : ℝ) / 4 < (c : ℝ))
        -- coerce to `ℝ≥0∞`
        simpa [add_assoc, add_left_comm, add_comm] using
          (by exact_mod_cast this : (r + r + r : ℝ≥0∞) < (c : ℝ≥0∞))
      have hsum_lt_c : riemannianEDist I y₁ y₂ + δ < (c : ℝ≥0∞) := hsum_lt.trans hc3r
      exact hlen.trans hsum_lt_c
    -- Points along `γ` stay in the `c`-ball around `x`, hence in `P ∩ source`.
    have hδ_le : δ ≤ (r : ℝ≥0∞) := min_le_right _ _
    have hlen_lt_c34 :
        pathELength I γ 0 1 < ((r : ℝ≥0∞) + (r : ℝ≥0∞)) + (r : ℝ≥0∞) := by
        have hδ_ne_top : δ ≠ (⊤ : ℝ≥0∞) := ne_of_lt (lt_of_le_of_lt hδ_le (by simp))
        simpa [add_assoc] using hlen.trans (ENNReal.add_lt_add_of_lt_of_le hδ_ne_top hdist_lt hδ_le)
    have hγ_mem : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ P ∩ (chartAt H x).source := by
      intro t ht
      -- Control `edist y₁ (γ t)` by the length of the path segment.
      have hdist_y₁ :
          riemannianEDist I y₁ (γ t) ≤ pathELength I γ 0 t := by
        apply riemannianEDist_le_pathELength (I := I) (γ := γ) (a := 0) (b := t) (hab := ht.1)
        · exact γ_smooth.mono (Icc_subset_Icc_right ht.2)
        · simp [hγ0]
        · rfl
      have hlen_mono : pathELength I γ 0 t ≤ pathELength I γ 0 1 := by
        simpa using pathELength_mono (I := I) (γ := γ) (a' := (0 : ℝ)) (a := 0) (b := t) (b' := 1)
          (le_rfl) ht.2
      have hy₁γt_edist : edist y₁ (γ t) < ((r : ℝ≥0∞) + (r : ℝ≥0∞)) + (r : ℝ≥0∞) := by
        have : edist y₁ (γ t) ≤ pathELength I γ 0 t := by
          -- rewrite `edist` as `riemannianEDist`
          simpa [IsRiemannianManifold.out (I := I) (M := M)] using hdist_y₁
        refine lt_of_le_of_lt (this.trans hlen_mono) hlen_lt_c34
      have hxγt : riemannianEDist I x (γ t) < (c : ℝ≥0∞) := by
        have hsum :
            edist x y₁ + edist y₁ (γ t) < (r : ℝ≥0∞) + (((r : ℝ≥0∞) + (r : ℝ≥0∞)) + (r : ℝ≥0∞)) :=
          ENNReal.add_lt_add hy₁_edist hy₁γt_edist
        have htri : edist x (γ t) ≤ edist x y₁ + edist y₁ (γ t) := edist_triangle _ _ _
        have hxγt_edist : edist x (γ t) < (c : ℝ≥0∞) := by
          have : (r : ℝ≥0∞) + (((r : ℝ≥0∞) + (r : ℝ≥0∞)) + (r : ℝ≥0∞)) = (c : ℝ≥0∞) := by
            -- `c = 4r`.
            have : (r + (r + r + r) : ℝ≥0) = c := by
              dsimp [r]
              exact_mod_cast (by nlinarith :
                (c : ℝ) / 4 + ((c : ℝ) / 4 + (c : ℝ) / 4 + (c : ℝ) / 4) = (c : ℝ))
            simpa [add_assoc, add_left_comm, add_comm] using
              (by exact_mod_cast this :
                (r + (r + r + r) : ℝ≥0∞) = (c : ℝ≥0∞))
          exact (lt_of_le_of_lt htri (hsum.trans_eq this))
        simpa [IsRiemannianManifold.out (I := I) (M := M)] using hxγt_edist
      exact hc hxγt
    have hchart_le :
        edist (extChartAt I x y₁) (extChartAt I x y₂) ≤ (C : ℝ≥0∞) * pathELength I γ 0 1 := by
      let γ' : ℝ → E := extChartAt I x ∘ γ
      have hC' : ContMDiffOn 𝓘(ℝ) (𝓘(ℝ, E)) 1 γ' (Icc (0 : ℝ) 1) := by
        refine ContMDiffOn.comp (I' := I) (t := (chartAt H x).source) (contMDiffOn_extChartAt (I :=
          I) (x := x) (n := 1))
          γ_smooth ?_
        intro t ht
        exact (hγ_mem t ht).2
      have hγ' : ContDiffOn ℝ 1 γ' (Icc (0 : ℝ) 1) :=
        contMDiffOn_iff_contDiffOn.mp hC'
      have hsub :
          ‖γ' 1 - γ' 0‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖derivWithin γ' (Icc (0 : ℝ) 1) t‖ₑ :=
        enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hγ' zero_le_one
      have hsub' :
          edist (γ' 0) (γ' 1) ≤ ∫⁻ t in Icc (0 : ℝ) 1,
            ‖mfderivWithin 𝓘(ℝ) (𝓘(ℝ, E)) γ' (Icc (0 : ℝ) 1) t 1‖ₑ := by
        -- Rewrite the left-hand side and convert `derivWithin` to `mfderivWithin`.
        have : edist (γ' 0) (γ' 1) = ‖γ' 1 - γ' 0‖ₑ := by
          -- `edist_eq_enorm_sub` gives `‖γ' 0 - γ' 1‖ₑ`; rewrite it using symmetry of `enorm`.
          have hsymm : ‖γ' 0 - γ' 1‖ₑ = ‖γ' 1 - γ' 0‖ₑ := by
            simpa using (enorm_sub_rev (γ' 0) (γ' 1))
          simp [edist_eq_enorm_sub, hsymm]
        -- `simp_rw` matches the pattern used in Mathlib’s proof of
        -- `setOf_riemannianEDist_lt_subset_nhds`.
        refine (le_trans (le_of_eq this) ?_)
        refine hsub.trans_eq ?_
        simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
        rfl
      -- Bound the integrand using the `mfderiv` bound along the path.
      have hI :
          (∫⁻ t in Icc (0 : ℝ) 1, ‖mfderivWithin 𝓘(ℝ) (𝓘(ℝ, E)) γ' (Icc (0 : ℝ) 1) t 1‖ₑ)
            ≤ ∫⁻ t in Icc (0 : ℝ) 1, (C : ℝ≥0∞) * ‖mfderivWithin 𝓘(ℝ) I γ (Icc (0 : ℝ) 1) t 1‖ₑ :=
              by
        apply setLIntegral_mono' measurableSet_Icc (fun t ht => ?_)
        have hcomp :
            mfderivWithin 𝓘(ℝ) (𝓘(ℝ, E)) γ' (Icc (0 : ℝ) 1) t =
              (mfderiv I (𝓘(ℝ, E)) (extChartAt I x) (γ t)) ∘L
                (mfderivWithin 𝓘(ℝ) I γ (Icc (0 : ℝ) 1) t) := by
          apply mfderiv_comp_mfderivWithin
          · exact mdifferentiableAt_extChartAt (I := I) (x := x) (hγ_mem t ht).2
          · exact ContMDiffWithinAt.mdifferentiableWithinAt (γ_smooth t ht) (by simp)
          · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
            exact uniqueDiffOn_Icc zero_lt_one t ht
        have hcomp1 :
            mfderivWithin 𝓘(ℝ) (𝓘(ℝ, E)) γ' (Icc (0 : ℝ) 1) t 1 =
              (mfderiv I (𝓘(ℝ, E)) (extChartAt I x) (γ t))
                (mfderivWithin 𝓘(ℝ) I γ (Icc (0 : ℝ) 1) t 1) := congr($hcomp 1)
        rw [hcomp1]
        apply (ContinuousLinearMap.le_opENorm _ _).trans
        gcongr
        · have hlt : ‖mfderiv I (𝓘(ℝ, E)) (extChartAt I x) (γ t)‖ₑ < (C : ℝ≥0∞) := by
            have : γ t ∈ P := (hγ_mem t ht).1
            simpa [P] using this
          exact hlt.le
      have hI' :
          edist (γ' 0) (γ' 1) ≤ (C : ℝ≥0∞) * pathELength I γ 0 1 := by
        refine (hsub'.trans ?_)
        refine (hI.trans ?_)
        -- Pull out the constant and identify the remaining integral with `pathELength`.
        simp [pathELength_eq_lintegral_mfderivWithin_Icc, lintegral_const_mul', ENNReal.coe_ne_top]
      -- Unfold `γ'` at the endpoints.
      simpa [γ', Function.comp, hγ0, hγ1] using hI'
    have hδ_mul : (C : ℝ≥0∞) * δ ≤ (ε : ℝ≥0∞) := by
      have hδ : δ ≤ (ε : ℝ≥0∞) / (C : ℝ≥0∞) := min_le_left _ _
      have : (C : ℝ≥0∞) * δ ≤ (C : ℝ≥0∞) * ((ε : ℝ≥0∞) / (C : ℝ≥0∞)) :=
        mul_le_mul_right hδ _
      -- cancel `C` (finite and nonzero)
      simpa [ENNReal.mul_div_cancel C_ne (by simp)] using this
    have hfinal :
        edist (extChartAt I x y₁) (extChartAt I x y₂) ≤
          (C : ℝ≥0∞) * riemannianEDist I y₁ y₂ + (ε : ℝ≥0∞) := by
      calc
        edist (extChartAt I x y₁) (extChartAt I x y₂)
            ≤ (C : ℝ≥0∞) * pathELength I γ 0 1 := hchart_le
        _ ≤ (C : ℝ≥0∞) * (riemannianEDist I y₁ y₂ + δ) := by
              exact mul_le_mul_right (le_of_lt hlen) _
        _ = (C : ℝ≥0∞) * riemannianEDist I y₁ y₂ + (C : ℝ≥0∞) * δ := by
              simp [mul_add]
        _ ≤ (C : ℝ≥0∞) * riemannianEDist I y₁ y₂ + (ε : ℝ≥0∞) := by
              -- `add_le_add_left` produces the inequality with potentially swapped summands;
              -- normalize.
              simpa [add_assoc, add_left_comm, add_comm] using
                (add_le_add_left hδ_mul ((C : ℝ≥0∞) * riemannianEDist I y₁ y₂))
    exact hfinal
  -- Conclude in terms of `edist` on `M`.
  simpa [IsRiemannianManifold.out (I := I) (M := M)] using hmain

end

end Riemannian
end Manifold
end Geometry
end RellichKondrachov
