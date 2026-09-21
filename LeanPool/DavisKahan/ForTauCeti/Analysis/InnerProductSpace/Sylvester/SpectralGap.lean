/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Sylvester.BlockEstimate
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BlockLowerBound
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralGrid
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.RealLowerBound
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.StoneUniqueness
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralProjectionGroup
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralGapInverse

/-!
# The Sylvester spectral gap

Separated spectra force a lower bound on the Sylvester operator, hence a spectral
gap at **every** vector of the Hilbert–Schmidt space.

The argument cuts the line into cells of width `ε`, estimates `𝒮` on each
two-sided spectral block, and reassembles.  All of the pieces are proved
elsewhere; this module is the chain:

`grid → blocks → per-block estimate → global lower bound → resolvent point → gap`

## The one place a case split is needed

A block whose left or right projection is **zero** is itself zero, and the
estimate holds trivially.  A block whose projections are both nonzero has cells
meeting both spectra (`exists_mem_spectrum_of_specProjection_ne_zero`), and the
separation hypothesis then applies to actual spectral points — which is what
bounds the *representatives* `kε` and `lε` apart, up to the cell radius.

## Provenance

*New.*  The donor proves the same statement in the tensor model, through joint
projection-valued measures and a product-measure identity whose closure is
~20,000 lines of Born-rule machinery.  Nothing of that appears here.

Moved from
`ForTauCeti/Analysis/InnerProductSpace/SylvesterSpectralGap.lean` to
`ForTauCeti/Analysis/InnerProductSpace/Sylvester/SpectralGap.lean`.  The `Sylvester/`
directory already held `Basic`, `Interval`, `SpectralDistance` and `Internal/`, while
six siblings of the same family used a flat `Sylvester*` prefix in the directory above;
one family now has one convention.  Path change and import repoint only — no statement,
signature, proof, attribute, declaration name or namespace changed.
-/

public section

open scoped InnerProductSpace ENNReal
open TauCeti.OneParameterUnitaryGroup (generator)

namespace TauCeti
namespace HilbertSchmidt

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A block with a zero factor is the zero block. -/
theorem blockFun_eq_zero_left (b : HilbertBasis ι ℂ F) (Q : F →L[ℂ] F)
    (f : lp (fun _ : ι => E) 2) : blockFun b (0 : E →L[ℂ] E) Q f = 0 := by
  refine ofLp_injective b ?_
  rw [ofLp_blockFun, ofLp_zero]
  ext x
  simp

/-- A block with a zero right factor vanishes. -/
theorem blockFun_eq_zero_right (b : HilbertBasis ι ℂ F) (P : E →L[ℂ] E)
    (f : lp (fun _ : ι => E) 2) : blockFun b P (0 : F →L[ℂ] F) f = 0 := by
  refine ofLp_injective b ?_
  rw [ofLp_blockFun, ofLp_zero]
  ext x
  simp

section Gap

variable {A : E →ₗ.[ℂ] E} {Bop : F →ₗ.[ℂ] F}

/-- The spectral projection of the `k`-th grid cell. -/
noncomputable def gridProj (hA : IsSelfAdjoint A) (ε : ℝ) (k : ℤ) : E →L[ℂ] E :=
  TauCeti.LinearPMap.specProjection hA (TauCeti.LinearPMap.gridCell ε k)
    (TauCeti.LinearPMap.measurableSet_gridCell ε k)

/-- The grid projections commute with the group they were built from. -/
private theorem gridProj_comm (hA : IsSelfAdjoint A) (ε : ℝ) (k : ℤ) (t : ℝ) (y : E) :
    gridProj hA ε k ((TauCeti.LinearPMap.genToGroup hA).U t y)
      = (TauCeti.LinearPMap.genToGroup hA).U t (gridProj hA ε k y) :=
  TauCeti.LinearPMap.specProjection_expLimit_apply hA _ _ t y

/-- **The per-block bound, with the shift.**  On a block whose two projections
are both nonzero the separation hypothesis applies to genuine spectral points,
and the block estimate turns it into a bound on `𝒮 - s`.  A block with a zero
projection is zero, where the bound is vacuous.

The group is a parameter rather than `genToGroup hA` so that no `set` has to
rewrite inside the type of `z`. -/
theorem norm_block_ge (U : TauCeti.OneParameterUnitaryGroup E)
    (V : TauCeti.OneParameterUnitaryGroup F)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint Bop)
    (hUA : generator U = A) (hVB : generator V = Bop)
    (b : HilbertBasis ι ℂ F) {δ ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ lam : ℝ, (lam : ℂ) ∈ TauCeti.LinearPMap.spectrum A →
      ∀ alp : ℝ, (alp : ℂ) ∈ TauCeti.LinearPMap.spectrum Bop → δ ≤ |lam - alp|)
    (s : ℝ) (k l : ℤ)
    (hUcomm : ∀ (t : ℝ) (y : E), gridProj hA ε k (U.U t y) = U.U t (gridProj hA ε k y))
    (hVcomm : ∀ (t : ℝ) (y : F), gridProj hB ε l (V.U t y) = V.U t (gridProj hB ε l y))
    (z : (generator (sylvesterGroup U V b)).domain) :
    (δ - |s| - 4 * ε)
        * ‖blockCLM b (gridProj hA ε k) (gridProj hB ε l) (z : lp (fun _ : ι => E) 2)‖
      ≤ ‖blockCLM b (gridProj hA ε k) (gridProj hB ε l)
          (generator (sylvesterGroup U V b) z - (s : ℂ) • (z : lp (fun _ : ι => E) 2))‖ := by
  have hT : ∀ (t : ℝ) (y : lp (fun _ : ι => E) 2),
      blockCLM b (gridProj hA ε k) (gridProj hB ε l) ((sylvesterGroup U V b).U t y)
        = (sylvesterGroup U V b).U t (blockCLM b (gridProj hA ε k) (gridProj hB ε l) y) := by
    intro t y
    simpa using blockCLM_comm_sylvesterGroup U V b (gridProj hA ε k) (gridProj hB ε l)
      hUcomm hVcomm t y
  obtain ⟨hmemW, hcommW⟩ := TauCeti.OneParameterUnitaryGroup.generator_commute
    (sylvesterGroup U V b) (blockCLM b (gridProj hA ε k) (gridProj hB ε l)) hT z
  set W := blockCLM b (gridProj hA ε k) (gridProj hB ε l) (z : lp (fun _ : ι => E) 2) with hW
  have hrewrite : blockCLM b (gridProj hA ε k) (gridProj hB ε l)
      (generator (sylvesterGroup U V b) z - (s : ℂ) • (z : lp (fun _ : ι => E) 2))
      = generator (sylvesterGroup U V b) ⟨W, hmemW⟩ - (s : ℂ) • W := by
    rw [map_sub, map_smul, hcommW]
  rw [hrewrite]
  by_cases hPz : gridProj hA ε k = 0
  · have hz0 : W = 0 := by rw [hW, blockCLM_apply, hPz]; exact blockFun_eq_zero_left b _ _
    have hn : ‖W‖ = 0 := by rw [hz0]; simp
    rw [hn, mul_zero]
    exact norm_nonneg _
  by_cases hQz : gridProj hB ε l = 0
  · have hz0 : W = 0 := by rw [hW, blockCLM_apply, hQz]; exact blockFun_eq_zero_right b _ _
    have hn : ‖W‖ = 0 := by rw [hz0]; simp
    rw [hn, mul_zero]
    exact norm_nonneg _
  obtain ⟨lam, hlamCell, hlamSpec⟩ :=
    TauCeti.LinearPMap.exists_mem_spectrum_of_specProjection_ne_zero hA _ _ hPz
  obtain ⟨alp, halpCell, halpSpec⟩ :=
    TauCeti.LinearPMap.exists_mem_spectrum_of_specProjection_ne_zero hB _ _ hQz
  have hsep : δ ≤ |lam - alp| := hgap lam hlamSpec alp halpSpec
  have hlamNear : |lam - (k : ℝ) * ε| ≤ ε :=
    TauCeti.LinearPMap.abs_sub_le_of_mem_gridCell hε k hlamCell
  have halpNear : |alp - (l : ℝ) * ε| ≤ ε :=
    TauCeti.LinearPMap.abs_sub_le_of_mem_gridCell hε l halpCell
  have hrep : δ - 2 * ε ≤ |(k : ℝ) * ε - (l : ℝ) * ε| := by
    have h1 := abs_sub_abs_le_abs_sub (lam - alp) (((k : ℝ) * ε) - ((l : ℝ) * ε))
    have h2 : |(lam - alp) - (((k : ℝ) * ε) - ((l : ℝ) * ε))| ≤ 2 * ε := by
      have heq : (lam - alp) - (((k : ℝ) * ε) - ((l : ℝ) * ε))
          = (lam - (k : ℝ) * ε) - (alp - (l : ℝ) * ε) := by ring
      rw [heq]
      exact (abs_sub _ _).trans (by linarith)
    linarith
  have hest := norm_sylvester_block_sub_smul_le U V b hA hB hUA hVB
    (TauCeti.LinearPMap.measurableSet_gridCell ε k)
    (TauCeti.LinearPMap.measurableSet_gridCell ε l)
    (fun t ht => TauCeti.LinearPMap.abs_le_of_mem_gridCell hε k ht) hε.le
    (fun t ht => TauCeti.LinearPMap.abs_sub_le_of_mem_gridCell hε k ht)
    (fun t ht => TauCeti.LinearPMap.abs_le_of_mem_gridCell hε l ht) hε.le
    (fun t ht => TauCeti.LinearPMap.abs_sub_le_of_mem_gridCell hε l ht)
    ⟨W, hmemW⟩
    (by
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change (TauCeti.LinearPMap.specProjection hA (TauCeti.LinearPMap.gridCell ε k)
        (TauCeti.LinearPMap.measurableSet_gridCell ε k)).comp (ofLp b W) = ofLp b W
      rw [hW, blockCLM_apply]
      exact comp_ofLp_blockFun_left b
        (TauCeti.LinearPMap.specProjection_comp_self hA _ _) _ _)
    (by
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      change (ofLp b W).comp (TauCeti.LinearPMap.specProjection hB
        (TauCeti.LinearPMap.gridCell ε l) (TauCeti.LinearPMap.measurableSet_gridCell ε l))
        = ofLp b W
      rw [hW, blockCLM_apply]
      exact comp_ofLp_blockFun_right b _
        (TauCeti.LinearPMap.specProjection_comp_self hB _ _) _)
  have hcast : ((((k : ℝ) * ε : ℝ) : ℂ) - (((l : ℝ) * ε : ℝ) : ℂ) - (s : ℂ))
      = (((k : ℝ) * ε - (l : ℝ) * ε - s : ℝ) : ℂ) := by push_cast; ring
  have hscal : ‖((((k : ℝ) * ε : ℝ) : ℂ) - (((l : ℝ) * ε : ℝ) : ℂ) - (s : ℂ)) • W‖
      = |(k : ℝ) * ε - (l : ℝ) * ε - s| * ‖W‖ := by
    rw [hcast, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hlow : δ - |s| - 2 * ε ≤ |(k : ℝ) * ε - (l : ℝ) * ε - s| := by
    have h := abs_sub_abs_le_abs_sub ((k : ℝ) * ε - (l : ℝ) * ε) s
    have hs' : |(k : ℝ) * ε - (l : ℝ) * ε| - |s| ≤ |(k : ℝ) * ε - (l : ℝ) * ε - s| := by
      simpa using h
    linarith
  have htri : |(k : ℝ) * ε - (l : ℝ) * ε - s| * ‖W‖
      ≤ ‖generator (sylvesterGroup U V b) ⟨W, hmemW⟩ - (s : ℂ) • W‖
        + ‖generator (sylvesterGroup U V b) ⟨W, hmemW⟩
            - ((((k : ℝ) * ε : ℝ) : ℂ) - (((l : ℝ) * ε : ℝ) : ℂ)) • W‖ := by
    rw [← hscal]
    have hid : ((((k : ℝ) * ε : ℝ) : ℂ) - (((l : ℝ) * ε : ℝ) : ℂ) - (s : ℂ)) • W
        = (generator (sylvesterGroup U V b) ⟨W, hmemW⟩ - (s : ℂ) • W)
          - (generator (sylvesterGroup U V b) ⟨W, hmemW⟩
              - ((((k : ℝ) * ε : ℝ) : ℂ) - (((l : ℝ) * ε : ℝ) : ℂ)) • W) := by
      module
    rw [hid]
    exact norm_sub_le _ _
  have hmul : (δ - |s| - 2 * ε) * ‖W‖ ≤ |(k : ℝ) * ε - (l : ℝ) * ε - s| * ‖W‖ :=
    mul_le_mul_of_nonneg_right hlow (norm_nonneg W)
  linarith [hest, htri, hmul]

private theorem enorm_eq_ofReal_norm {X : Type*} [NormedAddCommGroup X] (x : X) :
    ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm]

/-- **The global lower bound at a fixed grid width.**  The block bounds sum. -/
theorem norm_sub_smul_ge_of_grid (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint Bop)
    (b : HilbertBasis ι ℂ F) {δ ε : ℝ} (hε : 0 < ε)
    (hgap : ∀ lam : ℝ, (lam : ℂ) ∈ TauCeti.LinearPMap.spectrum A →
      ∀ alp : ℝ, (alp : ℂ) ∈ TauCeti.LinearPMap.spectrum Bop → δ ≤ |lam - alp|)
    (s : ℝ)
    (z : (generator (sylvesterGroup (TauCeti.LinearPMap.genToGroup hA)
      (TauCeti.LinearPMap.genToGroup hB) b)).domain) :
    (δ - |s| - 4 * ε) * ‖(z : lp (fun _ : ι => E) 2)‖
      ≤ ‖generator (sylvesterGroup (TauCeti.LinearPMap.genToGroup hA)
          (TauCeti.LinearPMap.genToGroup hB) b) z
          - (s : ℂ) • (z : lp (fun _ : ι => E) 2)‖ := by
  obtain ⟨w, c, -⟩ := exists_hilbertBasis ℂ E
  set y := generator (sylvesterGroup (TauCeti.LinearPMap.genToGroup hA)
    (TauCeti.LinearPMap.genToGroup hB) b) z
    - (s : ℂ) • (z : lp (fun _ : ι => E) 2) with hy
  -- the block family splits norms
  have hsplit : ∀ g : lp (fun _ : ι => E) 2,
      ∑' p : ℤ × ℤ, ‖blockCLM b (gridProj hA ε p.1) (gridProj hB ε p.2) g‖ₑ ^ 2 = ‖g‖ₑ ^ 2 := by
    intro g
    simpa using tsum_enorm_sq_blockFun b c (gridProj hA ε) (gridProj hB ε)
      (TauCeti.LinearPMap.tsum_enorm_sq_specProjection_gridCell hA hε)
      (TauCeti.LinearPMap.tsum_enorm_sq_adjoint_specProjection_gridCell hB hε) g
  -- the block bounds, in `ℝ≥0∞`
  have hblock : ∀ p : ℤ × ℤ,
      ENNReal.ofReal (δ - |s| - 4 * ε)
          * ‖blockCLM b (gridProj hA ε p.1) (gridProj hB ε p.2) (z : lp (fun _ : ι => E) 2)‖ₑ
        ≤ ‖blockCLM b (gridProj hA ε p.1) (gridProj hB ε p.2) y‖ₑ := by
    intro p
    have hreal := norm_block_ge (TauCeti.LinearPMap.genToGroup hA)
      (TauCeti.LinearPMap.genToGroup hB) hA hB
      (TauCeti.LinearPMap.generator_genToGroup hA) (TauCeti.LinearPMap.generator_genToGroup hB)
      b hε hgap s p.1 p.2 (gridProj_comm hA ε p.1) (gridProj_comm hB ε p.2) z
    rw [hy]
    rcases le_or_gt 0 (δ - |s| - 4 * ε) with hc | hc
    · rw [enorm_eq_ofReal_norm, enorm_eq_ofReal_norm, ← ENNReal.ofReal_mul hc]
      exact ENNReal.ofReal_le_ofReal hreal
    · rw [ENNReal.ofReal_eq_zero.mpr hc.le, zero_mul]
      simp
  have hgoal := TauCeti.enorm_ge_of_blocks
    (fun p : ℤ × ℤ => blockCLM b (gridProj hA ε p.1) (gridProj hB ε p.2)) hsplit hblock
  -- back to `ℝ`
  rcases le_or_gt 0 (δ - |s| - 4 * ε) with hc | hc
  · rw [enorm_eq_ofReal_norm, enorm_eq_ofReal_norm, ← ENNReal.ofReal_mul hc,
      ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] at hgoal
    exact hgoal
  · exact le_trans (by nlinarith [norm_nonneg ((z : lp (fun _ : ι => E) 2))]) (norm_nonneg y)

/-- **The Sylvester spectral gap.**  Separated spectra give a gap at every
vector. -/
theorem hasVectorSpectralGap_sylvesterGroup (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint Bop)
    (b : HilbertBasis ι ℂ F) {δ : ℝ}
    (hgap : ∀ lam : ℝ, (lam : ℂ) ∈ TauCeti.LinearPMap.spectrum A →
      ∀ alp : ℝ, (alp : ℂ) ∈ TauCeti.LinearPMap.spectrum Bop → δ ≤ |lam - alp|)
    (f : lp (fun _ : ι => E) 2) :
    TauCeti.LinearPMap.HasVectorSpectralGap
      (isSelfAdjoint_generator_sylvesterGroup (TauCeti.LinearPMap.genToGroup hA)
        (TauCeti.LinearPMap.genToGroup hB) b) δ f := by
  set hS := isSelfAdjoint_generator_sylvesterGroup (TauCeti.LinearPMap.genToGroup hA)
    (TauCeti.LinearPMap.genToGroup hB) b with hSdef
  -- every real point inside the gap is a resolvent point
  have hres : ∀ s ∈ Set.Ioo (-δ) δ, (s : ℂ) ∈ TauCeti.LinearPMap.resolventSet
      (generator (sylvesterGroup (TauCeti.LinearPMap.genToGroup hA)
        (TauCeti.LinearPMap.genToGroup hB) b)) := by
    intro s hs
    have hsabs : |s| < δ := abs_lt.mpr ⟨hs.1, hs.2⟩
    refine (TauCeti.LinearPMap.mem_resolventSet_and_norm_le_of_lower_bound (c := δ - |s|) hS
      (by linarith) ?_).1
    intro x
    -- let the grid width go to zero
    refine le_of_forall_pos_le_add fun η hη => ?_
    set ε := η / (4 * (‖(x : lp (fun _ : ι => E) 2)‖ + 1)) with hεdef
    have hεpos : 0 < ε := by
      rw [hεdef]; positivity
    have hb := norm_sub_smul_ge_of_grid hA hB b hεpos hgap s x
    have hxn : (0 : ℝ) ≤ ‖(x : lp (fun _ : ι => E) 2)‖ := norm_nonneg _
    have hden : (0 : ℝ) < 4 * (‖(x : lp (fun _ : ι => E) 2)‖ + 1) := by positivity
    have hkey : 4 * ε * ‖(x : lp (fun _ : ι => E) 2)‖ ≤ η := by
      set nx := ‖(x : lp (fun _ : ι => E) 2)‖ with hnx
      have hrw : 4 * ε * nx = η * (4 * nx) / (4 * (nx + 1)) := by
        rw [hεdef]; field_simp
      rw [hrw, div_le_iff₀ hden]
      nlinarith [hη.le, hxn, mul_nonneg hη.le (show (0:ℝ) ≤ 4 by norm_num)]
    -- `linarith` cannot finish here: the two `≤` sides carry different (defeq) `ℝ` order
    -- instances, so its atoms do not match.  Combine the two bounds directly instead.
    exact le_trans (le_of_eq (by ring)) (add_le_add hb hkey)
  have := TauCeti.LinearPMap.diag_eq_zero_of_subset_resolventSet hS
    (Set.Ioo (-δ) δ) measurableSet_Ioo hres f
  exact this


end Gap


end HilbertSchmidt
end TauCeti
