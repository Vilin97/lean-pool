/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.SNumbers.SNumbers.Gelfand
public import LeanPool.SNumbers.SNumbers.Hilbert
public import LeanPool.SNumbers.SNumbers.MaxDifference
public import LeanPool.SNumbers.BasicResults.LittleGrothendieck
public import LeanPool.SNumbers.BasicResults.SVD
public import LeanPool.SNumbers.AddOns.Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences

/-!
# The identity `ℓ₁ → ℓ_∞` and order-optimality of the maximal difference theorem

The maximal difference theorem `aₙ ≤ e·(n+1)·hₙ` (see `SNumbers.MaxDifference`)
has an order-optimal linear factor `n+1`, witnessed by the natural inclusion
`I : ℓ₁ → ℓ_∞`. This file proves the two Gelfand bounds

  `½ ≤ cₙ(I) ≤ 1`

and the exact value of the Hilbert numbers

  `hₙ(I) = 1/(n+1)`,

whence `((n+1)/2)·hₙ(I) ≤ cₙ(I)` (`mul_hilbertNumber_le_gelfandNumber`): the factor
cannot grow slower than linearly.

The lower bound `hₙ(I) ≥ 1/(n+1)` comes from the factorization
`id_{ℓ₂ⁿ⁺¹} = proj∞ ∘ I ∘ emb1` and the ideal property of the Hilbert numbers.
For the upper bound, write `I = J₂ ∘ J₁` with the norm-one inclusions
`J₁ : ℓ₁ → ℓ₂` and `J₂ : ℓ₂ → ℓ_∞`, so that `B I A = T₂ ∘ T₁` with `T₁ = J₁A` and
`T₂ = BJ₂` acting on `ℓ₂`. Sign averaging (`BasicResults.LittleGrothendieck`)
bounds the two Hilbert–Schmidt norms, `∑ⱼ‖Beⱼ‖² ≤ ‖B‖²` and `∑ⱼ‖rowⱼ(A)‖² ≤ ‖A‖²`,
and the singular values of the product then satisfy
`(n+1)·σₙ ≤ ∑_{k≤n} σₖ ≤ ‖T₁‖_HS·‖T₂‖_HS`. The last step is carried out directly
from the Schmidt decomposition (Bessel and Cauchy–Schwarz), so no Schatten-class
theory is needed; truncating `A` to finite rank supplies the compactness that the
Schmidt decomposition requires, and the truncation is removed by subadditivity of
the approximation numbers.

Here `ℓ₁ = lp (fun _ : ℕ => 𝕜) 1` and `ℓ_∞ = lp (fun _ : ℕ => 𝕜) ∞`, and `𝕜` is `RCLike`.
-/

@[expose] public section

open scoped ENNReal

namespace SNumbers.L1Linf

variable {𝕜 : Type*} [RCLike 𝕜]

-- The `Fact (1 ≤ p)` instances needed for the `lp` norms are Mathlib's
-- `fact_one_le_one_ennreal`, `fact_one_le_two_ennreal`, `fact_one_le_top_ennreal`.

/-- `ℓ₁(ℕ; 𝕜)`, the space of absolutely summable scalar sequences. -/
abbrev L1 (𝕜 : Type*) [RCLike 𝕜] : Type _ := lp (fun _ : ℕ => 𝕜) 1

/-- `ℓ_∞(ℕ; 𝕜)`, the space of bounded scalar sequences. -/
abbrev Linf (𝕜 : Type*) [RCLike 𝕜] : Type _ := lp (fun _ : ℕ => 𝕜) ∞

/-- `‖x‖_∞ ≤ ‖x‖_p`: each coordinate is bounded by the `ℓ^p` norm. Used for
`p = 1` (the inclusion `I` below) and for `p = 2` (the inclusion `J₂`). -/
lemma norm_coe_linf_le_norm {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0)
    (f : lp (fun _ : ℕ => 𝕜) p) :
    ‖(lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) le_top f : Linf 𝕜)‖ ≤ ‖f‖ := by
  refine lp.norm_le_of_forall_le (norm_nonneg f) (fun i => ?_)
  rw [lp.coe_linearMapOfLE_apply]
  exact lp.norm_apply_le_norm hp f i

/-- The natural inclusion `I : ℓ₁ → ℓ_∞`, a contraction. -/
noncomputable def incl : L1 𝕜 →L[𝕜] Linf 𝕜 :=
  LinearMap.mkContinuous (lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) le_top) 1 (fun f => by
    rw [one_mul]; exact norm_coe_linf_le_norm (by norm_num) f)

@[simp] lemma incl_apply (f : L1 𝕜) (i : ℕ) :
    ((incl : L1 𝕜 →L[𝕜] Linf 𝕜) f) i = f i := rfl

lemma norm_incl_le : ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-! ## Basis vectors of `ℓ₁` -/

/-- The `i`-th standard basis vector `eᵢ = δᵢ` of `ℓ₁`. -/
noncomputable def e (i : ℕ) : L1 𝕜 := lp.single 1 i (1 : 𝕜)

@[simp] lemma e_apply_self (i : ℕ) : (e i : L1 𝕜) i = 1 :=
  lp.single_apply_self (E := fun _ : ℕ => 𝕜) 1 i (1 : 𝕜)

lemma e_apply_ne {i j : ℕ} (h : j ≠ i) : (e i : L1 𝕜) j = 0 :=
  lp.single_apply_ne (E := fun _ : ℕ => 𝕜) 1 i (1 : 𝕜) h

/-- `‖eᵢ‖₁ = 1`. -/
lemma norm_e (i : ℕ) : ‖(e i : L1 𝕜)‖ = 1 := by
  unfold e; rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_one]

/-! ## `cₙ(I) ≤ 1` -/

lemma gelfand_le_one (n : ℕ) :
    gelfandNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n ≤ 1 :=
  (gelfandNumber_le_norm _ _).trans norm_incl_le

/-! ## `cₙ(I) ≥ ½`

For any closed subspace `N ⊆ ℓ₁` of codimension `≤ n`, the quotient `ℓ₁ ⧸ N` is finite
dimensional, so the bounded family `([eᵢ])ᵢ` of basis-vector classes has two members
arbitrarily close (Bolzano–Weierstrass). Lifting their difference back gives `x ∈ N` close to
`eᵢ − eᵢ'`, with `‖x‖₁ ≈ 2` but `‖I x‖_∞ ≈ 1`, forcing `‖I|_N‖ ≥ ½`. -/

lemma half_le_gelfandNumber (n : ℕ) :
    (1 : ℝ) / 2 ≤ gelfandNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n := by
  refine le_gelfandNumber (fun N hN_closed hN_rank => ?_)
  have : FiniteDimensional 𝕜 (L1 𝕜 ⧸ N) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hN_rank (Cardinal.natCast_lt_aleph0))
  have : ProperSpace (L1 𝕜 ⧸ N) := FiniteDimensional.proper 𝕜 _
  set D : ℝ := deviationFromRestriction (incl : L1 𝕜 →L[𝕜] Linf 𝕜) N with hD
  have hD_nn : 0 ≤ D := deviationFromRestriction_nonneg _ _
  -- Operator-norm bound on the restriction: `‖I x‖ ≤ D · ‖x‖` for `x ∈ N`.
  have hopbound : ∀ x : L1 𝕜, x ∈ N →
      ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ ≤ D * ‖x‖ := by
    intro x hx
    have h := ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp N.subtypeL).le_opNorm (⟨x, hx⟩ : N)
    rwa [ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] at h
  -- Key ratio estimate for every `ε' > 0`.
  have key : ∀ ε' : ℝ, 0 < ε' → 1 - 2 * ε' ≤ D * (2 + 2 * ε') := by
    intro ε' hε'
    set g : ℕ → L1 𝕜 ⧸ N := fun i => Submodule.Quotient.mk (e i) with hg
    have hg_bdd : ∀ i, g i ∈ Metric.closedBall (0 : L1 𝕜 ⧸ N) 1 := by
      intro i
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖g i‖ ≤ ‖(e i : L1 𝕜)‖ := Submodule.Quotient.norm_mk_le N (e i)
        _ = 1 := norm_e i
    obtain ⟨a, -, φ, hφ_mono, hφ_tendsto⟩ :=
      tendsto_subseq_of_bounded Metric.isBounded_closedBall hg_bdd
    rw [Metric.tendsto_atTop] at hφ_tendsto
    obtain ⟨K, hK⟩ := hφ_tendsto (ε' / 2) (by positivity)
    have hi_ne : φ K ≠ φ (K + 1) := (hφ_mono (Nat.lt_succ_self K)).ne
    have hclose : dist (g (φ K)) (g (φ (K + 1))) < ε' := by
      calc dist (g (φ K)) (g (φ (K + 1)))
          ≤ dist (g (φ K)) a + dist a (g (φ (K + 1))) := dist_triangle _ _ _
        _ = dist (g (φ K)) a + dist (g (φ (K + 1))) a := by rw [dist_comm a]
        _ < ε' / 2 + ε' / 2 := add_lt_add (hK K (le_refl _)) (hK (K + 1) (Nat.le_succ _))
        _ = ε' := by ring
    set d : L1 𝕜 := e (φ K) - e (φ (K + 1)) with hd_def
    have hmk_small : ‖(Submodule.Quotient.mk d : L1 𝕜 ⧸ N)‖ < ε' := by
      have hmk_eq : (Submodule.Quotient.mk d : L1 𝕜 ⧸ N) = g (φ K) - g (φ (K + 1)) := by
        rw [hg, hd_def, Submodule.Quotient.mk_sub]
      rw [hmk_eq, ← dist_eq_norm]; exact hclose
    obtain ⟨y, hy_mk, hy_lt⟩ :=
      Submodule.Quotient.norm_mk_lt (Submodule.Quotient.mk d : L1 𝕜 ⧸ N) hε'
    set x : L1 𝕜 := d - y with hx_def
    have hx_mem : x ∈ N := by
      rw [← Submodule.Quotient.mk_eq_zero, hx_def, Submodule.Quotient.mk_sub, hy_mk, sub_self]
    have hy_2 : ‖y‖ < 2 * ε' := by linarith [hy_lt, hmk_small]
    have hx_l1 : ‖x‖ ≤ 2 + 2 * ε' := by
      calc ‖x‖ = ‖d - y‖ := by rw [hx_def]
        _ ≤ ‖d‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ (‖(e (φ K) : L1 𝕜)‖ + ‖(e (φ (K + 1)) : L1 𝕜)‖) + ‖y‖ := by
            gcongr; rw [hd_def]; exact norm_sub_le _ _
        _ ≤ (1 + 1) + 2 * ε' := by rw [norm_e, norm_e]; linarith [hy_2]
        _ = 2 + 2 * ε' := by ring
    have hx_linf : 1 - 2 * ε' ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ := by
      have hcoord : ((incl : L1 𝕜 →L[𝕜] Linf 𝕜) d) (φ K) = (1 : 𝕜) := by
        rw [incl_apply, hd_def]
        simp only [lp.coeFn_sub, Pi.sub_apply, e_apply_self, e_apply_ne hi_ne, sub_zero]
      have h_incl_d : (1 : ℝ) ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) d‖ := by
        have hb := lp.norm_apply_le_norm (show (∞ : ℝ≥0∞) ≠ 0 by simp)
          ((incl : L1 𝕜 →L[𝕜] Linf 𝕜) d) (φ K)
        rwa [hcoord, norm_one] at hb
      have h_incl_y : ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) y‖ ≤ ‖y‖ :=
        ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).le_opNorm y).trans
          (mul_le_of_le_one_left (norm_nonneg y) norm_incl_le)
      have hxeq : (incl : L1 𝕜 →L[𝕜] Linf 𝕜) x
          = (incl : L1 𝕜 →L[𝕜] Linf 𝕜) d - (incl : L1 𝕜 →L[𝕜] Linf 𝕜) y := by
        rw [hx_def, map_sub]
      calc 1 - 2 * ε'
          ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) d‖ - ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) y‖ := by
            linarith [h_incl_d, h_incl_y, hy_2]
        _ ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) d - (incl : L1 𝕜 →L[𝕜] Linf 𝕜) y‖ :=
            norm_sub_norm_le _ _
        _ = ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ := by rw [hxeq]
    calc 1 - 2 * ε'
        ≤ ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜) x‖ := hx_linf
      _ ≤ D * ‖x‖ := hopbound x hx_mem
      _ ≤ D * (2 + 2 * ε') := mul_le_mul_of_nonneg_left hx_l1 hD_nn
  -- Let `ε' → 0`.
  change (1 : ℝ) / 2 ≤ D
  have h2D : (1 : ℝ) ≤ 2 * D := by
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have h1D : (0 : ℝ) < 1 + D := by linarith
    set ε' : ℝ := δ / (2 * (1 + D)) with hε'_def
    have hε'_pos : 0 < ε' := by positivity
    have hk := key ε' hε'_pos
    have hδeq : 2 * ε' * (1 + D) = δ := by
      rw [hε'_def]; field_simp
    nlinarith [hk, hδeq]
  linarith

/-! ## Auxiliary norm bounds on `ℓ₂ᵐ`

Cauchy–Schwarz bounds relating the `ℓ₁`/`ℓ₂` and `ℓ₂`/`ℓ_∞` norms of a finite
vector, both with the factor `√m`. -/

open scoped Finset in
/-- `∑ᵢ ‖vᵢ‖ ≤ √m · ‖v‖₂` on `ℓ₂ᵐ`: the `EuclideanSpace` reading of
`SNumbers.sum_le_sqrt_card_mul_sqrt_sum_sq`. -/
lemma sum_norm_le_sqrt_mul_norm {m : ℕ} (v : EuclideanSpace 𝕜 (Fin m)) :
    ∑ i, ‖v i‖ ≤ Real.sqrt m * ‖v‖ := by
  refine (SNumbers.sum_le_sqrt_card_mul_sqrt_sum_sq fun i => ‖v i‖).trans ?_
  rw [EuclideanSpace.norm_eq, Fintype.card_fin]

/-! ### The factorization `id_{ℓ₂ᵐ} = proj∞ ∘ I ∘ emb1`

`hₙ(I) ≥ 1/(n+1)` follows from `1 ≤ hₙ(id_{ℓ₂ᵐ})` (`one_le_hilbertNumber_id`) and the
factorization `id_{ℓ₂ᵐ} = proj∞ ∘ I ∘ emb1` through `√m`-bounded maps
`emb1 : ℓ₂ᵐ → ℓ₁` and `proj∞ : ℓ_∞ → ℓ₂ᵐ`, via the Hilbert-number ideal property
`hilbertNumber_comp_comp_le`. -/

/-- `emb1 v = ∑_{i<m} single 1 i (vᵢ)`, the finite-support embedding `ℓ₂ᵐ → ℓ₁`. -/
noncomputable def emb1 (m : ℕ) : EuclideanSpace 𝕜 (Fin m) →L[𝕜] L1 𝕜 :=
  ∑ i : Fin m,
    (lp.singleContinuousLinearMap 𝕜 (fun _ : ℕ => 𝕜) 1 (i : ℕ)).comp (EuclideanSpace.proj i)

lemma emb1_apply (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) :
    emb1 m v = ∑ i : Fin m, lp.single 1 (i : ℕ) (v i) := by
  simp only [emb1, sum_apply, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply, EuclideanSpace.coe_proj]

lemma norm_emb1_apply_le (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) :
    ‖emb1 m v‖ ≤ Real.sqrt m * ‖v‖ := by
  have key : ‖(∑ i : Fin m, lp.single 1 (i : ℕ) (v i) : L1 𝕜)‖ ≤ Real.sqrt m * ‖v‖ := by
    refine (norm_sum_le _ _).trans ?_
    have hsum : ∑ i : Fin m, ‖(lp.single 1 (i : ℕ) (v i) : L1 𝕜)‖ = ∑ i : Fin m, ‖v i‖ :=
      Finset.sum_congr rfl fun i _ =>
        lp.norm_single (E := fun _ : ℕ => 𝕜) (show (0 : ℝ≥0∞) < 1 by norm_num) (i : ℕ) (v i)
    rw [hsum]
    exact sum_norm_le_sqrt_mul_norm v
  exact (congrArg Norm.norm (emb1_apply m v)).trans_le key

lemma norm_emb1_le (m : ℕ) : ‖(emb1 m : EuclideanSpace 𝕜 (Fin m) →L[𝕜] L1 𝕜)‖ ≤ Real.sqrt m :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (norm_emb1_apply_le m)

/-- `proj∞ y = ∑_{i<m} yᵢ • eᵢ`, the finite coordinate projection `ℓ_∞ → ℓ₂ᵐ`. -/
noncomputable def projinf (m : ℕ) : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m) :=
  ∑ i : Fin m,
    (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) ∞ (i : ℕ)).smulRight (EuclideanSpace.single i (1 : 𝕜))

lemma projinf_apply (m : ℕ) (y : Linf 𝕜) :
    (projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y
      = ∑ i : Fin m, (y (i : ℕ)) • EuclideanSpace.single i (1 : 𝕜) := by
  simp only [projinf, sum_apply, ContinuousLinearMap.smulRight_apply,
    lp.evalCLM, LinearMap.mkContinuous_apply, lp.evalₗ_apply]

/-- Coordinate of `proj∞ y`: the `j`-th entry is `y j`. -/
lemma projinf_coord (m : ℕ) (y : Linf 𝕜) (j : Fin m) :
    (projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y j = y (j : ℕ) := by
  have h := congrArg (fun x : EuclideanSpace 𝕜 (Fin m) => x j) (projinf_apply m y)
  refine h.trans ?_
  simp [Pi.single_apply, Finset.sum_ite_eq]

lemma norm_projinf_apply_le (m : ℕ) (y : Linf 𝕜) :
    ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ≤ Real.sqrt m * ‖y‖ := by
  have hnn : (0 : ℝ) ≤ ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ := norm_nonneg _
  have hsq : ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ^ 2
      = ∑ j : Fin m, ‖y (j : ℕ)‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
    exact Finset.sum_congr rfl fun j _ => by rw [projinf_coord]
  have hle : ∑ j : Fin m, ‖y (j : ℕ)‖ ^ 2 ≤ (m : ℝ) * ‖y‖ ^ 2 := by
    calc ∑ j : Fin m, ‖y (j : ℕ)‖ ^ 2
        ≤ ∑ _j : Fin m, ‖y‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => by gcongr; exact lp.norm_apply_le_norm (by simp) y (j : ℕ)
      _ = (m : ℝ) * ‖y‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have key : ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y‖ ^ 2
      ≤ (Real.sqrt m * ‖y‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (m : ℝ)), hsq]; exact hle
  exact le_of_sq_le_sq key (by positivity)

lemma norm_projinf_le (m : ℕ) :
    ‖(projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m))‖ ≤ Real.sqrt m :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (norm_projinf_apply_le m)

/-- Coordinate of `emb1 v` at `j < m`: the `j`-th entry is `vⱼ`. -/
lemma emb1_coord (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) (j : Fin m) :
    (emb1 m v) (j : ℕ) = v j := by
  have h := congrArg (fun x : L1 𝕜 => x (j : ℕ)) (emb1_apply m v)
  refine h.trans ?_
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp [lp.single_apply, Pi.single_apply, Finset.sum_ite_eq, Fin.val_inj]

/-- The factorization `id_{ℓ₂ᵐ} = proj∞ ∘ I ∘ emb1`. -/
lemma projinf_comp_incl_comp_emb1 (m : ℕ) :
    (projinf m : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)).comp
        ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (emb1 m))
      = ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin m)) := by
  ext v j
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
  rw [projinf_coord, incl_apply, emb1_coord]

/-! ## `hₙ(I) ≥ 1/(n+1)` -/

/-- The Hilbert numbers of `I : ℓ₁ → ℓ_∞` are bounded below by `1/(n+1)`. Combined with
`cₙ(I) ≥ ½`, this shows the factor `n+1` in the maximal difference theorem is order-optimal. -/
theorem one_div_le_hilbertNumber (n : ℕ) :
    (1 : ℝ) / (n + 1) ≤ hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n := by
  set hI := hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n with hI_def
  have hmnn : (0 : ℝ) ≤ hI := hilbertNumber_nonneg _ _
  have hid := one_le_hilbertNumber_id (𝕜 := 𝕜) n
  have hideal := hilbertNumber_comp_comp_le (emb1 (n + 1))
    (incl : L1 𝕜 →L[𝕜] Linf 𝕜) (projinf (n + 1)) n
  rw [projinf_comp_incl_comp_emb1 (n + 1), ← hI_def] at hideal
  -- `1 ≤ hₙ(id) ≤ ‖proj∞‖ · hI · ‖emb1‖`.
  have h1 : (1 : ℝ)
      ≤ ‖(projinf (n + 1) : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖ * hI
        * ‖(emb1 (n + 1) : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] L1 𝕜)‖ := hid.trans hideal
  -- `‖proj∞‖ · hI · ‖emb1‖ ≤ √(n+1) · hI · √(n+1) = (n+1) · hI`.
  have hbound : ‖(projinf (n + 1) : Linf 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)))‖ * hI
      * ‖(emb1 (n + 1) : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] L1 𝕜)‖
      ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) * hI * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    gcongr
    · exact norm_projinf_le (𝕜 := 𝕜) (n + 1)
    · exact norm_emb1_le (𝕜 := 𝕜) (n + 1)
  have hsqrt : Real.sqrt ((n + 1 : ℕ) : ℝ) * hI * Real.sqrt ((n + 1 : ℕ) : ℝ)
      = ((n : ℝ) + 1) * hI := by
    rw [mul_right_comm, Real.mul_self_sqrt (by positivity)]; push_cast; ring
  have h3 : (1 : ℝ) ≤ ((n : ℝ) + 1) * hI := by
    calc (1 : ℝ) ≤ _ := h1
      _ ≤ _ := hbound
      _ = ((n : ℝ) + 1) * hI := hsqrt
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  linarith [h3]

/-- Coordinates of `emb1 v` beyond its support vanish. -/
lemma emb1_coord_of_le (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) {j : ℕ} (hj : m ≤ j) :
    (emb1 m v) j = 0 := by
  have h := congrArg (fun x : L1 𝕜 => x j) (emb1_apply m v)
  refine h.trans ?_
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hij : j ≠ (i : ℕ) := by have := i.isLt; omega
  simp [lp.single_apply, hij]

/-- The finite coordinate projection `ℓ₁ → ℓ₂ᵐ` onto the first `m` coordinates.
Since `I` preserves coordinates, it is `proj∞` precomposed with `I`. -/
noncomputable def proj1 (m : ℕ) : L1 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m) :=
  (projinf m).comp (incl : L1 𝕜 →L[𝕜] Linf 𝕜)

/-- Coordinate of `proj1 y`: the `j`-th entry is `y j`. -/
lemma proj1_coord (m : ℕ) (y : L1 𝕜) (j : Fin m) :
    (proj1 m : L1 𝕜 →L[𝕜] EuclideanSpace 𝕜 (Fin m)) y j = y (j : ℕ) := by
  rw [proj1, ContinuousLinearMap.comp_apply, projinf_coord, incl_apply]

/-! ## The factorization `I = J₂ ∘ J₁` through `ℓ₂`

The upper bound `hₙ(I) ≤ 1/(n+1)` rests on splitting the inclusion into the two
norm-one inclusions `J₁ : ℓ₁ → ℓ₂` and `J₂ : ℓ₂ → ℓ_∞`. For bounded operators
`A : ℓ₂ → ℓ₁` and `B : ℓ_∞ → ℓ₂` this writes `B I A` as a product `T₂ T₁` of two
Hilbert–Schmidt operators on `ℓ₂`, with `‖T₁‖_HS ≤ ‖A‖` and `‖T₂‖_HS ≤ ‖B‖`. -/

/-- `‖x‖₂ ≤ ‖x‖₁`, since the cross terms in `(∑ᵢ |xᵢ|)²` are nonnegative:
`∑ᵢ |xᵢ|² ≤ (∑ᵢ |xᵢ|)²`. -/
lemma norm_coe_l2_le_norm_l1 (f : L1 𝕜) :
    ‖(lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) (by norm_num : (1 : ℝ≥0∞) ≤ 2) f : L2 𝕜)‖ ≤ ‖f‖ := by
  set g := (lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) (by norm_num : (1 : ℝ≥0∞) ≤ 2) f : L2 𝕜)
    with hg
  have hcoord : ∀ i : ℕ, (g : ℕ → 𝕜) i = f i := by
    intro i
    rw [hg]
    exact congrFun (lp.coe_linearMapOfLE_apply _ _) i
  have hsq : ‖g‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
    rw [norm_sq_eq_tsum_norm_sq]
    exact tsum_congr fun i => by rw [hcoord]
  have hle : ∑' i, ‖f i‖ ^ 2 ≤ ‖f‖ ^ 2 :=
    Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun n =>
      calc ∑ i ∈ Finset.range n, ‖f i‖ ^ 2
          ≤ (∑ i ∈ Finset.range n, ‖f i‖) ^ 2 :=
            Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _
        _ ≤ ‖f‖ ^ 2 :=
            pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => norm_nonneg _)
              (sum_norm_apply_le_norm_l1 f (Finset.range n)) 2
  nlinarith [norm_nonneg g, norm_nonneg f, hsq, hle]

/-- The norm-one inclusion `J₁ : ℓ₁ → ℓ₂`. -/
noncomputable def inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜 :=
  LinearMap.mkContinuous (lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)) 1 (fun f => by
    rw [one_mul]; exact norm_coe_l2_le_norm_l1 f)

@[simp] lemma inclL1L2_apply (f : L1 𝕜) (i : ℕ) :
    ((inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜) f) i = f i := rfl

lemma norm_inclL1L2_le : ‖(inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- The norm-one inclusion `J₂ : ℓ₂ → ℓ_∞`. -/
noncomputable def inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜 :=
  LinearMap.mkContinuous (lp.linearMapOfLE 𝕜 (fun _ : ℕ => 𝕜) le_top) 1 (fun f => by
    rw [one_mul]; exact norm_coe_linf_le_norm (by norm_num) f)

@[simp] lemma inclL2Linf_apply (f : L2 𝕜) (i : ℕ) :
    ((inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜) f) i = f i := rfl

lemma norm_inclL2Linf_le : ‖(inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜)‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `I = J₂ ∘ J₁`: all three inclusions act as the identity on coordinates. -/
lemma incl_eq_comp :
    (incl : L1 𝕜 →L[𝕜] Linf 𝕜)
      = (inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜).comp (inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜) :=
  ContinuousLinearMap.ext fun _ => lp.ext (funext fun _ => rfl)

/-- `J₂` maps the `j`-th unit vector of `ℓ₂` to the `j`-th unit vector of `ℓ_∞`. -/
@[simp] lemma inclL2Linf_single (j : ℕ) :
    (inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜) (lp.single 2 j (1 : 𝕜)) = lp.single ∞ j (1 : 𝕜) :=
  lp.ext (funext fun _ => rfl)

/-! ## The two Hilbert–Schmidt factors and their rows and columns -/

section Factors

variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)

/-- The left factor `T₁ = J₁ A : ℓ₂ → ℓ₂`. -/
noncomputable def T1 : L2 𝕜 →L[𝕜] L2 𝕜 := (inclL1L2 : L1 𝕜 →L[𝕜] L2 𝕜).comp A

/-- The right factor `T₂ = B J₂ : ℓ₂ → ℓ₂`. -/
noncomputable def T2 : L2 𝕜 →L[𝕜] L2 𝕜 := B.comp (inclL2Linf : L2 𝕜 →L[𝕜] Linf 𝕜)

/-- The `j`-th **row** of `A`: the vector of `ℓ₂` representing the bounded
functional `x ↦ (A x) j`, realised as the adjoint of `T₁` applied to the `j`-th
unit vector. -/
noncomputable def row (j : ℕ) : L2 𝕜 :=
  ContinuousLinearMap.adjoint (T1 A) (lp.single 2 j (1 : 𝕜))

/-- The `j`-th **column** of `B`: the image of the `j`-th unit vector of `ℓ_∞`. -/
noncomputable def col (j : ℕ) : L2 𝕜 := B (lp.single ∞ j (1 : 𝕜))

/-- The defining property of the rows: `⟪rowⱼ, x⟫ = (A x) j`. -/
lemma inner_row (j : ℕ) (x : L2 𝕜) : (inner 𝕜 (row A j) x : 𝕜) = A x j := by
  rw [row, ContinuousLinearMap.adjoint_inner_left, lp.inner_single_left]
  simp [T1]

/-- Hilbert–Schmidt bound for the left factor, via its rows:
`∑ⱼ ‖rowⱼ‖² ≤ ‖A‖²`. -/
lemma sum_norm_sq_row_le_norm_sq (J : Finset ℕ) : ∑ j ∈ J, ‖row A j‖ ^ 2 ≤ ‖A‖ ^ 2 :=
  sum_norm_sq_row_le A (inner_row A) J

lemma summable_norm_sq_row' : Summable fun j => ‖row A j‖ ^ 2 :=
  summable_norm_sq_row A (inner_row A)

/-- Hilbert–Schmidt bound for the right factor, via its columns:
`∑ⱼ ‖colⱼ‖² ≤ ‖B‖²`. -/
lemma sum_norm_sq_col_le_norm_sq (J : Finset ℕ) : ∑ j ∈ J, ‖col B j‖ ^ 2 ≤ ‖B‖ ^ 2 := by
  simpa [col] using sum_norm_sq_apply_single_le B J

/-- `‖T₁ x‖² = ∑ⱼ |⟪rowⱼ, x⟫|²`. -/
lemma norm_T1_apply_sq (x : L2 𝕜) :
    ‖T1 A x‖ ^ 2 = ∑' j, ‖(inner 𝕜 (row A j) x : 𝕜)‖ ^ 2 := by
  rw [norm_sq_eq_tsum_norm_sq]
  exact tsum_congr fun j => by rw [inner_row]; rfl

/-- Coordinates of the adjoint of the right factor: `(T₂* y)ⱼ = ⟪colⱼ, y⟫`. -/
lemma adjoint_T2_coord (y : L2 𝕜) (j : ℕ) :
    (ContinuousLinearMap.adjoint (T2 B) y) j = (inner 𝕜 (col B j) y : 𝕜) := by
  have h := ContinuousLinearMap.adjoint_inner_right (T2 B) (lp.single 2 j (1 : 𝕜)) y
  rw [lp.inner_single_left] at h
  simpa [T2, col] using h

/-- `‖T₂* y‖² = ∑ⱼ |⟪colⱼ, y⟫|²`. -/
lemma norm_adjoint_T2_apply_sq (y : L2 𝕜) :
    ‖ContinuousLinearMap.adjoint (T2 B) y‖ ^ 2 = ∑' j, ‖(inner 𝕜 (col B j) y : 𝕜)‖ ^ 2 := by
  rw [norm_sq_eq_tsum_norm_sq]
  exact tsum_congr fun j => by rw [adjoint_T2_coord]

/-! ### From rows to Hilbert–Schmidt bounds along an orthonormal family

Both bounds are instances of `SVD.sum_norm_sq_apply_le_of_rows` (Bessel plus a
row bound), applied to the rows of `A` and to the columns of `B`. -/

/-- Hilbert–Schmidt bound for the left factor along an orthonormal-or-zero
family: `∑ₖ ‖T₁ uₖ‖² ≤ ‖A‖²`. -/
lemma sum_norm_sq_T1_le {u : ℕ → L2 𝕜} (hu : SVD.OrthonormalOrZero 𝕜 u) (s : Finset ℕ) :
    ∑ k ∈ s, ‖T1 A (u k)‖ ^ 2 ≤ ‖A‖ ^ 2 :=
  SVD.sum_norm_sq_apply_le_of_rows (norm_T1_apply_sq A)
    (sum_norm_sq_row_le_norm_sq A) hu s

/-- Hilbert–Schmidt bound for the adjoint of the right factor along an
orthonormal-or-zero family: `∑ₖ ‖T₂* vₖ‖² ≤ ‖B‖²`. -/
lemma sum_norm_sq_adjoint_T2_le {v : ℕ → L2 𝕜} (hv : SVD.OrthonormalOrZero 𝕜 v)
    (s : Finset ℕ) :
    ∑ k ∈ s, ‖ContinuousLinearMap.adjoint (T2 B) (v k)‖ ^ 2 ≤ ‖B‖ ^ 2 :=
  SVD.sum_norm_sq_apply_le_of_rows (norm_adjoint_T2_apply_sq B)
    (sum_norm_sq_col_le_norm_sq B) hv s

/-! ### The estimate for operators of finite rank -/

/-- `B I A` has at most the rank of `A`. -/
lemma rank_comp_incl_comp_le :
    (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)).rank ≤ A.rank := by
  have h : B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)
      = (B.comp (incl : L1 𝕜 →L[𝕜] Linf 𝕜)).comp
          (A.comp (ContinuousLinearMap.id 𝕜 (L2 𝕜))) := by
    simp only [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_id]
  rw [h]
  exact ContinuousLinearMap.rank_comp_comp_le _ _ _

/-- If `A` has finite rank, so has `B I A`, and it is therefore compact. -/
lemma isCompactOperator_comp_incl_comp {m : ℕ} (hrank : A.rank ≤ (m : Cardinal)) :
    IsCompactOperator (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) :=
  SVD.isCompactOperator_of_rank_le ((rank_comp_incl_comp_le A B).trans hrank)

/-- `B I A` factors through `ℓ₂` as the product of the two Hilbert–Schmidt
factors `T₂ = B J₂` and `T₁ = J₁ A`. -/
lemma comp_incl_comp_eq : B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A) = (T2 B).comp (T1 A) :=
  ContinuousLinearMap.ext fun _ =>
    congrArg (fun y : Linf 𝕜 => B y) (lp.ext (funext fun _ => rfl))

/-- **The key estimate, for `A` of finite rank.** If `A` has rank at most `m`,
then `aₙ(B I A) ≤ ‖A‖ ‖B‖ / (n+1)` for every `n`.

`T := B I A` has finite rank, hence is compact, and factors as `T = T₂T₁` through
`ℓ₂`; the two Hilbert–Schmidt bounds above then feed the general singular value
estimate `SVD.mul_approximationNumber_le_of_factorization`. -/
theorem approximationNumber_comp_incl_comp_le_of_rank {m : ℕ}
    (hrank : A.rank ≤ (m : Cardinal)) (n : ℕ) :
    approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) n
      ≤ ‖A‖ * ‖B‖ / (n + 1) := by
  have key := SVD.mul_approximationNumber_le_of_factorization
    (isCompactOperator_comp_incl_comp A B hrank) (comp_incl_comp_eq A B)
    (fun u hu s => sum_norm_sq_T1_le A hu s)
    (fun v hv s => sum_norm_sq_adjoint_T2_le B hv s)
    (norm_nonneg A) (norm_nonneg B) n
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  linarith [key]

/-! ### The finite-rank truncations of `A`

Truncating `A` to its first `m` coordinates gives a finite-rank operator `Aₘ`
with `‖Aₘ‖ ≤ ‖A‖`, so the estimate above applies to it. The truncation error is
controlled by the rows: `‖I (A - Aₘ)‖ ≤ sup_{j ≥ m} ‖rowⱼ‖`, which tends to `0`
because `∑ⱼ ‖rowⱼ‖² < ∞`. -/

/-- The `m`-th coordinate truncation `Aₘ = emb1 ∘ proj1 ∘ A` of `A`; it factors
through `ℓ₂ᵐ` and therefore has rank at most `m`. -/
noncomputable def trunc (m : ℕ) : L2 𝕜 →L[𝕜] L1 𝕜 :=
  (emb1 m).comp ((proj1 m).comp A)

/-- Below the truncation index the coordinates of `Aₘ` agree with those of `A`. -/
lemma trunc_coord_of_lt (m : ℕ) (x : L2 𝕜) {j : ℕ} (hj : j < m) :
    (trunc A m x) j = A x j := by
  have h1 := emb1_coord m ((proj1 m) (A x)) ⟨j, hj⟩
  have h2 := proj1_coord m (A x) ⟨j, hj⟩
  simpa [trunc, h2] using h1

/-- From the truncation index on, the coordinates of `Aₘ` vanish. -/
lemma trunc_coord_of_le (m : ℕ) (x : L2 𝕜) {j : ℕ} (hj : m ≤ j) :
    (trunc A m x) j = 0 := by
  simpa [trunc] using emb1_coord_of_le m ((proj1 m) (A x)) hj

/-- The truncation has rank at most `m`, since it factors through `ℓ₂ᵐ`. -/
lemma rank_trunc_le (m : ℕ) : (trunc A m).rank ≤ (m : Cardinal) := by
  have h : trunc A m = (emb1 m).comp ((proj1 m).comp A) := by simp only [trunc]
  rw [h]
  exact rank_comp_le_of_euclidean _ _

/-- Truncating does not increase the norm: `‖Aₘ x‖₁ ≤ ‖A x‖₁`, since the
coordinates of `Aₘ x` are those of `A x` or zero. -/
lemma norm_trunc_apply_le (m : ℕ) (x : L2 𝕜) : ‖trunc A m x‖ ≤ ‖A x‖ := by
  refine lp.norm_le_of_forall_sum_le (by norm_num) (norm_nonneg _) fun s => ?_
  have hone : ((1 : ℝ≥0∞)).toReal = (1 : ℝ) := by norm_num
  simp only [hone, Real.rpow_one]
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => i < m)]
  have hlow : ∑ i ∈ s.filter (fun i => i < m), ‖(trunc A m x) i‖
      = ∑ i ∈ s.filter (fun i => i < m), ‖A x i‖ :=
    Finset.sum_congr rfl fun i hi => by
      rw [trunc_coord_of_lt A m x (Finset.mem_filter.mp hi).2]
  have hhigh : ∑ i ∈ s.filter (fun i => ¬ i < m), ‖(trunc A m x) i‖ = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [trunc_coord_of_le A m x (not_lt.mp (Finset.mem_filter.mp hi).2), norm_zero]
  rw [hlow, hhigh, add_zero]
  exact sum_norm_apply_le_norm_l1 (A x) _

lemma norm_trunc_le (m : ℕ) : ‖trunc A m‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x =>
    (norm_trunc_apply_le A m x).trans (A.le_opNorm x)

/-- The key estimate for the truncations: `aₙ(B I Aₘ) ≤ ‖A‖ ‖B‖ / (n+1)`. -/
theorem approximationNumber_comp_incl_comp_trunc_le (m n : ℕ) :
    approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (trunc A m))) n
      ≤ ‖A‖ * ‖B‖ / (n + 1) := by
  refine (approximationNumber_comp_incl_comp_le_of_rank (trunc A m) B
    (rank_trunc_le A m) n).trans ?_
  gcongr
  exact norm_trunc_le A m

/-- **The key estimate.** `aₙ(B I A) ≤ ‖A‖ ‖B‖ / (n+1)` for *all* bounded
`A : ℓ₂ → ℓ₁` and `B : ℓ_∞ → ℓ₂`.

The truncation error is handled with the subadditivity of the approximation
numbers: `aₙ(T) ≤ aₙ(Tₘ) + ‖T - Tₘ‖`, where `‖T - Tₘ‖ ≤ ‖B‖ δ` as soon as
`‖rowⱼ‖ ≤ δ` for all `j ≥ m` — which holds eventually since `∑ⱼ ‖rowⱼ‖² < ∞`. -/
theorem approximationNumber_comp_incl_comp_le (n : ℕ) :
    approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) n
      ≤ ‖A‖ * ‖B‖ / (n + 1) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- Choose a truncation index beyond which all rows are small.
  set δ := ε / (‖B‖ + 1) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; positivity
  obtain ⟨m, hm⟩ : ∃ m, ∀ j, m ≤ j → ‖row A j‖ ≤ δ := by
    have h := (summable_norm_sq_row' A).tendsto_atTop_zero
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp
      (h.eventually_lt_const (show (0 : ℝ) < δ ^ 2 by positivity))
    refine ⟨m, fun j hj => ?_⟩
    nlinarith [hm j hj, norm_nonneg (row A j), hδpos]
  -- The truncation error is at most `‖B‖ δ ≤ ε`.
  have hres : ‖(incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m)‖ ≤ δ := by
    refine ContinuousLinearMap.opNorm_le_bound _ hδpos.le fun x => ?_
    refine lp.norm_le_of_forall_le (mul_nonneg hδpos.le (norm_nonneg x)) fun j => ?_
    have hcoord : ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m) x) j
        = if j < m then 0 else (inner 𝕜 (row A j) x : 𝕜) := by
      have h : ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m) x) j
          = A x j - (trunc A m x) j := by
        simp [ContinuousLinearMap.comp_apply]
      rw [h]
      by_cases hj : j < m
      · rw [ite_eq_left hj, trunc_coord_of_lt A m x hj, sub_self]
      · rw [ite_eq_right hj, trunc_coord_of_le A m x (not_lt.mp hj), sub_zero, inner_row]
    rw [hcoord]
    by_cases hj : j < m
    · rw [ite_eq_left hj, norm_zero]
      exact mul_nonneg hδpos.le (norm_nonneg x)
    · rw [ite_eq_right hj]
      calc ‖(inner 𝕜 (row A j) x : 𝕜)‖ ≤ ‖row A j‖ * ‖x‖ := norm_inner_le_norm _ _
        _ ≤ δ * ‖x‖ :=
            mul_le_mul_of_nonneg_right (hm j (not_lt.mp hj)) (norm_nonneg x)
  -- Subadditivity of the approximation numbers.
  have hsplit : B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)
      = B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (trunc A m))
        + B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m)) := by
    ext x
    simp [ContinuousLinearMap.comp_apply, sub_eq_add_neg]
  have hnorm : ‖B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m))‖ ≤ ‖B‖ * δ :=
    (B.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left hres (norm_nonneg B))
  have hδB : ‖B‖ * δ ≤ ε :=
    calc ‖B‖ * δ ≤ (‖B‖ + 1) * δ :=
          mul_le_mul_of_nonneg_right (by linarith) hδpos.le
      _ = ε := by rw [hδ]; field_simp
  calc approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) n
      ≤ approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (trunc A m))) n
          + ‖B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp (A - trunc A m))‖ := by
        rw [hsplit]; exact approximationNumber_add_le _ _ n
    _ ≤ ‖A‖ * ‖B‖ / (n + 1) + ε := by
        gcongr
        · exact approximationNumber_comp_incl_comp_trunc_le A B m n
        · exact hnorm.trans hδB

end Factors

/-! ## `hₙ(I) ≤ 1/(n+1)`, and order-optimality of the factor `n+1` -/

/-- The Hilbert numbers of `I : ℓ₁ → ℓ_∞` are bounded above by `1/(n+1)`: every
admissible ratio `aₙ(B I A)/(‖B‖‖A‖)` is, by the key estimate. -/
theorem hilbertNumber_le_one_div (n : ℕ) :
    hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n ≤ (1 : ℝ) / (n + 1) := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (by positivity)
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  have h := approximationNumber_comp_incl_comp_le A B n
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at h
  rw [div_le_div_iff₀ hpos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
  linarith [h]

/-- **The Hilbert numbers of the inclusion `I : ℓ₁ → ℓ_∞`:** `hₙ(I) = 1/(n+1)`. -/
theorem hilbertNumber_eq_one_div (n : ℕ) :
    hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n = (1 : ℝ) / (n + 1) :=
  le_antisymm (hilbertNumber_le_one_div n) (one_div_le_hilbertNumber n)

/-- **Order-optimality of the factor `n+1`** in the maximal difference theorem:
for the inclusion `I : ℓ₁ → ℓ_∞` one has `((n+1)/2) · hₙ(I) ≤ cₙ(I)`, whereas the
maximal difference theorem bounds `cₙ ≤ aₙ ≤ e·(n+1)·hₙ` from above. So the linear
growth of the factor cannot be improved. -/
theorem mul_hilbertNumber_le_gelfandNumber (n : ℕ) :
    ((n : ℝ) + 1) / 2 * hilbertNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n
      ≤ gelfandNumber (incl : L1 𝕜 →L[𝕜] Linf 𝕜) n := by
  rw [hilbertNumber_eq_one_div,
    show ((n : ℝ) + 1) / 2 * ((1 : ℝ) / (n + 1)) = 1 / 2 by
      field_simp]
  exact half_le_gelfandNumber n

end SNumbers.L1Linf

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
