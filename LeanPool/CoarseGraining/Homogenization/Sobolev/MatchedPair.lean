/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.MatchedPair.Core
public import LeanPool.CoarseGraining.Homogenization.Sobolev.CubeEmbedding

/-! # Matched Pair -/

@[expose] public section

namespace Homogenization

open MeasureTheory Homogenization
open scoped ENNReal NNReal BigOperators

/-!
# The matched-pair Sobolev inequality

This module re-exports the scaled Poincaré inequalities, the zero-set lower
bound, and the matched-pair Poincaré inequality from the `MatchedPair`
submodules, and proves the top-level matched-pair Sobolev inequality (the
high-moment paper's Lemma 3.2, `l.doubled.sobolev` / `e.doubled.sobolev`,
Armstrong–Kuusi–Loher, to appear):

For `f, g ∈ H¹(axisCube z L)` sharing a boundary trace (`f − g ∈ H¹₀`) whose
value sets together cover at most `|U|`,
`‖f‖_{L^{2*}} + ‖g‖_{L^{2*}} ≤ C_d (∑ᵢ‖∂ᵢf‖_{L²} + ∑ᵢ‖∂ᵢg‖_{L²})`,
in the split `eLpNorm` spelling aligned with `cube_sobolev_embedding`.

The proof combines the cube Sobolev embedding for `f` and `g` with the
matched-pair Poincaré inequality to absorb the lower-order `L⁻¹‖·‖_{L²}` terms.
-/

noncomputable section

variable {d : ℕ}

/-- **Matched-pair Sobolev inequality (the high-moment paper's Lemma 3.2, split `eLpNorm` form).**

For `d ≥ 3` there is an absolute constant `C = C(d) ≥ 0` such that for every axis
cube `U = axisCube z L` of side `L > 0` and every pair `f, g ∈ H¹(U)` with
`f − g ∈ H¹₀(U)` and `|{f ≠ 0}| + |{g ≠ 0}| ≤ |U|` (measurable representatives),
`‖f‖_{L^{2*}(U)} + ‖g‖_{L^{2*}(U)} ≤ C (∑ᵢ‖∂ᵢf‖_{L²(U)} + ∑ᵢ‖∂ᵢg‖_{L²(U)})`. -/
theorem matchedPair_sobolev (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z : Homogenization.Vec d) (L : ℝ), 0 < L →
        ∀ (f g : H1Function (axisCube z L)),
          Measurable f.toFun → Measurable g.toFun →
          MemH10 (axisCube z L) (fun x => f.toFun x - g.toFun x) →
          MeasureTheory.volume {x | x ∈ axisCube z L ∧ f.toFun x ≠ 0}
            + MeasureTheory.volume {x | x ∈ axisCube z L ∧ g.toFun x ≠ 0}
            ≤ MeasureTheory.volume (axisCube z L) →
          (eLpNorm f.toFun (twoStar d) (volumeMeasureOn (axisCube z L))).toReal
            + (eLpNorm g.toFun (twoStar d) (volumeMeasureOn (axisCube z L))).toReal
          ≤ C *
              ((∑ i : Fin d,
                  (eLpNorm (fun x => f.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal)
                + ∑ i : Fin d,
                  (eLpNorm (fun x => g.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal) := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨CE, hCEpos, hE⟩ := cube_sobolev_embedding hd
  have hmpp_nn : 0 ≤ matchedPairPoincareConst d := matchedPairPoincareConst_nonneg d
  refine ⟨(CE : ℝ) * (1 + matchedPairPoincareConst d), by positivity, ?_⟩
  intro z L hL f g hfm hgm hfg hzero
  -- Real-valued form of E1 for a single `H¹` function on this cube.
  have e1real : ∀ u : H1Function (axisCube z L),
      (eLpNorm u.toFun (twoStar d) (volumeMeasureOn (axisCube z L))).toReal ≤
        (CE : ℝ) *
          ((∑ i : Fin d,
              (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal)
            + L⁻¹ * (eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L))).toReal) := by
    intro u
    have hEu := hE z L hL u
    -- Finiteness of the pieces of the right-hand side.
    have hgrad_ne : ∀ i : Fin d,
        eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L)) ≠ ⊤ :=
      fun i => (u.gradMemL2 i).eLpNorm_lt_top.ne
    have hval_ne : eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L)) ≠ ⊤ :=
      u.memL2.eLpNorm_lt_top.ne
    have hB1_ne :
        (∑ i : Fin d, eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))) ≠ ⊤ :=
      (ENNReal.sum_lt_top.2 fun i _ => (hgrad_ne i).lt_top).ne
    have hB2_ne :
        ENNReal.ofReal L⁻¹ * eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hval_ne
    have hCE_ne : ((CE : ℝ≥0∞)) ≠ ⊤ := ENNReal.coe_ne_top
    have hRHS_ne :
        (CE : ℝ≥0∞) *
          ((∑ i : Fin d, eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L)))
            + ENNReal.ofReal L⁻¹ * eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L))) ≠ ⊤ :=
      ENNReal.mul_ne_top hCE_ne (ENNReal.add_ne_top.2 ⟨hB1_ne, hB2_ne⟩)
    calc (eLpNorm u.toFun (twoStar d) (volumeMeasureOn (axisCube z L))).toReal
        ≤ ((CE : ℝ≥0∞) *
            ((∑ i : Fin d, eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L)))
              + ENNReal.ofReal L⁻¹ * eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L)))).toReal :=
          ENNReal.toReal_mono hRHS_ne hEu
      _ = (CE : ℝ) *
            ((∑ i : Fin d,
                (eLpNorm (fun x => u.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal)
              + L⁻¹ * (eLpNorm u.toFun 2 (volumeMeasureOn (axisCube z L))).toReal) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_add hB1_ne hB2_ne,
            ENNReal.toReal_sum (fun i _ => hgrad_ne i), ENNReal.toReal_mul,
            ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal]
  -- E1 for `f` and `g`.
  have hEf := e1real f
  have hEg := e1real g
  -- F3 in real / `eLpNorm` form.
  have hF3 := matchedPair_poincare z hL f g hfm hgm hfg hzero
  rw [norm_toScalarL2_eq, norm_toScalarL2_eq,
    gradientCoordL2NormSum_eq_sum_eLpNorm f,
    gradientCoordL2NormSum_eq_sum_eLpNorm g] at hF3
  -- Abbreviations.
  set Gf := ∑ i : Fin d,
    (eLpNorm (fun x => f.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal with hGf
  set Gg := ∑ i : Fin d,
    (eLpNorm (fun x => g.grad x i) 2 (volumeMeasureOn (axisCube z L))).toReal with hGg
  set nff := (eLpNorm f.toFun 2 (volumeMeasureOn (axisCube z L))).toReal with hnff
  set nfg := (eLpNorm g.toFun 2 (volumeMeasureOn (axisCube z L))).toReal with hnfg
  -- Absorb the lower-order term via F3.
  have hLinv_nn : (0 : ℝ) ≤ L⁻¹ := by positivity
  have hstep : L⁻¹ * (nff + nfg) ≤ matchedPairPoincareConst d * (Gf + Gg) := by
    have h1 := mul_le_mul_of_nonneg_left hF3 hLinv_nn
    have h2 : L⁻¹ * (matchedPairPoincareConst d * L * (Gf + Gg)) =
        matchedPairPoincareConst d * (Gf + Gg) := by
      rw [show matchedPairPoincareConst d * L * (Gf + Gg)
            = L * (matchedPairPoincareConst d * (Gf + Gg)) by ring,
        ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
    linarith [h1, h2]
  -- Assemble.
  calc (eLpNorm f.toFun (twoStar d) (volumeMeasureOn (axisCube z L))).toReal
        + (eLpNorm g.toFun (twoStar d) (volumeMeasureOn (axisCube z L))).toReal
      ≤ (CE : ℝ) * (Gf + L⁻¹ * nff) + (CE : ℝ) * (Gg + L⁻¹ * nfg) := add_le_add hEf hEg
    _ = (CE : ℝ) * ((Gf + Gg) + L⁻¹ * (nff + nfg)) := by ring
    _ ≤ (CE : ℝ) * ((Gf + Gg) + matchedPairPoincareConst d * (Gf + Gg)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith [hstep]
    _ = (CE : ℝ) * (1 + matchedPairPoincareConst d) * (Gf + Gg) := by ring

end

end Homogenization
