/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/

import Mathlib.Analysis.Complex.Tietze
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Invariance of domain

This file contains the completed invariance-of-domain portion of Kai Lam's development in
[mathlib4 PR #36770](https://github.com/leanprover-community/mathlib4/pull/36770), adapted from
commit `230d75acb32d80e7d7c4f4cd028b139f3dc28be7`. It proves invariance of domain for
finite-dimensional real inner product spaces, conditional on Brouwer's fixed-point theorem for the
closed unit ball.

The chart-independence layer is adapted from Steven Sivek's
[`TopologicalManifolds`](https://github.com/stevensivek/TopologicalManifolds) development at commit
`05f80330d5a41b05376ae90eb8aa32c0166721db`. It packages invariance of domain as a reusable
topological typeclass and applies it to the interior and boundary strata of charted spaces.

The proof follows Terry Tao's exposition, using the Tietze extension theorem,
Stone-Weierstrass approximation, and a measure-theoretic perturbation argument.

## Main declarations

* `BrouwerFixedPoint`: the required fixed-point principle for the closed unit ball.
* `differentiable_approx_of_continuous`: differentiable approximation on compact sets.
* `stability_of_zero`: stability of a zero under a bounded perturbation.
* `invariance_of_domain_interior`: the closed-ball form of invariance of domain.
* `invariance_of_domain_open_map`: the open-set form of invariance of domain.
* `invariance_of_domain_partial_equiv`: the neighbourhood form for partial equivalences.
* `HasInvarianceOfDomain`: a reusable topological form of invariance of domain.
* `isInteriorPoint_iff_any_chart`: chart independence of interior points.
* `isBoundaryPoint_iff_any_chart`: chart independence of boundary points.

## Reference

* Terry Tao, "Brouwer's fixed point and invariance of domain theorems, and Hilbert's fifth
  problem", 2011.
-/


namespace LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain

open MeasureTheory Metric Set ContinuousLinearMap LinearMap _root_.Topology Polynomial

variable {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (E) in
/-- `BrouwerFixedPoint E` is a typeclass asserting that the Brouwer fixed point theorem holds for
  the closed unit ball in the inner product space `E`.  That is: for every continuous map
  `f : closedBall 0 1 → closedBall 0 1`, there exists `x` such that `f x = x`.
  This is assumed and used to prove invariance of domain. -/
class BrouwerFixedPoint : Prop where
  brouwer_fixed_point (f : (closedBall (0 : E) 1) → (closedBall 0 1))
    (hf : Continuous f) : ∃ x, f x = x

/-- On a compact set, any continuous map can be uniformly approximated by a differentiable map. -/
theorem differentiable_approx_of_continuous {δ : ℝ} (hδ : 0 < δ) {U : Set E}
    (hUcompact : IsCompact U) (G : E → E) (hG_cont : Continuous G) [Nontrivial E] :
    ∃ (P : C(E, E)), Differentiable ℝ P ∧ ∀ y ∈ U, ‖P y - G y‖ < δ := by
  let basis := stdOrthonormalBasis ℝ E
  let n := Module.finrank ℝ E
  -- We construct the subalgebra of polynomials from `ℝ^n` to `ℝ` and show they are differentiable
  -- Projecting onto one of the axes is continuous and differentiable
  let coord (i : Fin n) : C(E, ℝ) :=
    { toFun := fun x => basis.toBasis.equivFunL x i
      continuous_toFun := by fun_prop}
  have hcoord_diff (i : Fin n) : Differentiable ℝ (coord i) :=
    ((ContinuousLinearMap.proj i).comp
    (basis.toBasis.equivFunL : E →L[ℝ] (Fin n → ℝ))).differentiable
  -- This gives us the subalgebra of polynomials.
  let generator : Set C(E, ℝ) := Set.range coord
  have hgen_diff : ∀ f ∈ generator, Differentiable ℝ f := by
    rintro _ ⟨i, rfl⟩
    exact hcoord_diff i
  let A : Subalgebra ℝ C(E, ℝ) := Algebra.adjoin ℝ generator
  have hA_diff : ∀ f ∈ A, Differentiable ℝ f := by
    let D : Subalgebra ℝ C(E, ℝ) :=
      { carrier := {f | Differentiable ℝ f}
        zero_mem' := differentiable_const 0
        one_mem' := differentiable_const 1
        add_mem' := fun hf hg => hf.add hg
        mul_mem' := fun hf hg => hf.mul hg
        algebraMap_mem' := fun r => differentiable_const r }
    have hA_sub : A ≤ D := Algebra.adjoin_le hgen_diff
    exact fun f hf => hA_sub hf
  -- This subalgebra of polynomials separates points.
  have hAsep : A.SeparatesPoints := by
    intro x y hxy
    have hequiv: basis.toBasis.equivFunL x ≠ basis.toBasis.equivFunL y := by simpa
    obtain ⟨i, hi⟩ : ∃ i : (Fin n), basis.toBasis.equivFunL x i ≠ basis.toBasis.equivFunL y i := by
      contrapose! hequiv
      ext i
      exact (hequiv i)
    have hf_mem : coord i ∈ A := Algebra.subset_adjoin (Set.mem_range_self i)
    exact ⟨coord i, Set.mem_image_of_mem (fun f ↦ f.1) hf_mem, hi⟩
  let G_i (i : Fin n) : C(E, ℝ) :=
    {toFun := fun y => basis.toBasis.equivFunL (G y) i, continuous_toFun := by fun_prop}
  let coordEquiv := basis.toBasis.equivFunL
  have hpos_symm : 0 < ‖(coordEquiv.symm : ((Fin n) → ℝ) →L[ℝ] E)‖ := by
    refine lt_of_le_of_ne (norm_nonneg _) fun h_eq => ?_
    let w : Fin n → ℝ := fun _ => 1
    have hw : w ≠ 0 := by
      have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp Module.finrank_pos
      obtain ⟨i⟩ := (inferInstance : Nonempty (Fin n))
      intro h
      have : w i = 0 := congr_fun h i
      linarith
    have hw0 : (coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E) w = 0 := by
      rw [norm_eq_zero.1 h_eq.symm]
      rfl
    have hfalse : coordEquiv (coordEquiv.symm w) = coordEquiv 0 := congrArg coordEquiv hw0
    rw [coordEquiv.apply_symm_apply w, map_zero] at hfalse
    exact hw hfalse
  -- Define `C` as the operator norm for l.symm
  let C := ‖(coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E)‖
  let ε' := δ / (2 * C)
  have hε' : 0 < ε' := div_pos (hδ) (mul_pos zero_lt_two hpos_symm)
  -- Using the Stone-Weierstrass theorem, pick each `P_i` to be `ε'-close` to each `G_i`.
  have approx (i : Fin n) :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_isCompact_of_separatesPoints
    hAsep (G_i i) hUcompact hε'
  choose p_i hp_i using approx
  -- Construct `P` as a function from `ℝ^n` to `ℝ^n` using the component functions `P_i`.
  let P : C(E, E) :=
    { toFun := fun y => basis.toBasis.equivFunL.symm (fun i => (p_i i : C(E, ℝ)) y),
      continuous_toFun := by fun_prop}
  -- The difference between `P` and `G` on `Σ` is bounded by `δ`
  have hP_bound : ∀ y ∈ U , ‖P y - G y‖ < δ := by
    intro y hy
    let v : Fin n → ℝ := fun i => (p_i i : C(E, ℝ)) y - (basis.toBasis.equivFunL (G y)) i
    have hv i : |v i| < ε' := by
      grind only [ContinuousMap.coe_mk, Real.norm_eq_abs, (hp_i i).2 y hy]
    have hnorm_v : ‖v‖ < ε' := by rw [pi_norm_lt_iff hε']; exact fun i => hv i
    have hP_eq : P y - G y = coordEquiv.symm v := by
      apply coordEquiv.injective
      rw [map_sub, coordEquiv.apply_symm_apply]
      ext i
      change
        (coordEquiv (coordEquiv.symm (fun j => (p_i j : C(E, ℝ)) y)) - coordEquiv (G y)) i =
          (fun j => (p_i j : C(E, ℝ)) y - coordEquiv (G y) j) i
      rw [coordEquiv.apply_symm_apply]
      rfl
    rw [hP_eq]
    calc
      ‖coordEquiv.symm v‖
      ≤ C * ‖v‖ := le_opNorm (coordEquiv.symm : (Fin n → ℝ) →L[ℝ] E) v
    _ < C * ε' := mul_lt_mul_of_pos_left hnorm_v hpos_symm
    _ = δ / 2 := by
        unfold ε'
        field_simp [ne_of_gt hpos_symm]
        exact div_self (ne_of_gt hpos_symm)
    _ < δ := half_lt_self hδ
  have hp_i_diff (i : Fin n) : Differentiable ℝ (p_i i) := hA_diff (p_i i) (hp_i i).1
  have hP_diff : Differentiable ℝ P :=
    (basis.toBasis.equivFunL.symm : (Fin n → ℝ) →L[ℝ] E).differentiable.comp
    (differentiable_pi.mpr hp_i_diff)
  use P

variable [BrouwerFixedPoint E]
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Stability of zero (Lemma 6). If `G` is a left inverse of `f` on the closed ball,
    and `Gtilde` is a continuous function on `f(Bⁿ)` with `‖G - Gtilde‖ ≤ 1` pointwise,
    then `Gtilde` has a zero in `f(Bⁿ)`. -/
lemma stability_of_zero (f : E → E) (hf_cont : ContinuousOn f (closedBall 0 1))
    (G : C(E, E)) (hG_left_inv : ∀ x ∈ closedBall 0 1, G (f x) = x)
    (Gtilde : E → E) (hGtilde_cont : ContinuousOn Gtilde (f '' closedBall 0 1))
    (hbound : ∀ y ∈ f '' closedBall 0 1, ‖G y - Gtilde y‖ ≤ 1) :
    ∃ y ∈ f '' closedBall 0 1, Gtilde y = 0 := by
  -- Define the function whose fixed point gives the zero of `Gtilde`
  let diff_fun : E → E := fun x => x - Gtilde (f x)
  -- `B^n` contains the image of itself under diff_fun.
  have hMapsTo : Set.MapsTo diff_fun (closedBall 0 1) (closedBall 0 1) :=
    fun x hx => by grind [mem_closedBall_zero_iff]
  -- `diff_fun` is continuous on `B^n`
  have diff_fun_cont_on : ContinuousOn diff_fun (closedBall 0 1) :=
    (continuousOn_id' _).sub (hGtilde_cont.comp hf_cont (mapsTo_image f _))
  obtain ⟨x, hx⟩ := BrouwerFixedPoint.brouwer_fixed_point
    (Set.MapsTo.restrict diff_fun (closedBall 0 1) (closedBall 0 1) hMapsTo)
    (ContinuousOn.mapsToRestrict diff_fun_cont_on hMapsTo)
  have hx_eq : diff_fun (x : E) = (x : E) := congr_arg Subtype.val hx
  grind

omit [FiniteDimensional ℝ E] [BrouwerFixedPoint E] in
private theorem radialProjection_mem_sep_union_sphere (c : E) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) {s : Set E} (hc : c ∉ s) {y : E} (hy : y ∈ s) :
    c + max (epsilon / ‖y - c‖) (1 : ℝ) • (y - c) ∈
      {z ∈ s | ‖z - c‖ ≥ epsilon} ∪ sphere c epsilon := by
  by_cases h : epsilon < ‖y - c‖
  · have hyc : 0 < ‖y - c‖ := hepsilon.trans h
    grind [max_eq_right_of_lt, one_smul, add_sub_cancel, div_lt_one hyc]
  · right
    simp only [not_lt] at h
    have hy_neq_c : c ≠ y := fun hcy ↦ hc (hcy ▸ hy)
    have hleft : 1 ≤ epsilon / ‖y - c‖ :=
      (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr hy_neq_c.symm))).mpr h
    rw [max_eq_left hleft]
    simp [norm_smul, sub_ne_zero_of_ne hy_neq_c.symm, hepsilon.le]

/-- Let `B^n` be the closed unit ball (closedBall 0 1).
Let `f : B^n → ℝ^n` be an continuous injective map.
Then `f(0)` lies in the interior of `f(B^n)`. -/
theorem invariance_of_domain_interior (f : E → E)
    (hf_cont : ContinuousOn f (closedBall 0 1)) (hf_inj : Set.InjOn f (closedBall 0 1))
    : f 0 ∈ interior (f ''(closedBall 0 1)) := by
  -- In the case where `n = 0`, `ℝ^0` has only a single point.
  cases subsingleton_or_nontrivial E
  · have himage : f '' closedBall 0 1 = Set.univ := by
      ext y
      simp only [Set.mem_image, Set.mem_univ, iff_true]
      exact ⟨0, by simp, Subsingleton.elim _ _⟩
    rw [himage, interior_univ]; exact Set.mem_univ _
  -- The equivalence between `B^n` and `f(B^n)`.
  let FEquiv := Equiv.Set.imageOfInjOn f (closedBall 0 1) hf_inj
  -- The inverse map of `f` is continuous.
  let FInvCmap : C(f '' closedBall 0 1, (closedBall (0 : E) 1)) :=
  ⟨FEquiv.symm,  Continuous.continuous_symm_of_equiv_compact_to_t2 (continuous_induced_rng.mpr <|
    ContinuousOn.domRestrict hf_cont)⟩
  -- `f(B^n)` is closed.
  have hballimageclosed : IsClosed (f '' closedBall 0 1) :=
    ((isCompact_closedBall 0 1).image_of_continuousOn hf_cont).isClosed
  -- The Tietze extension theorem, finding a continuous function `G` that extends `f⁻¹`.
  obtain ⟨G, hG⟩ := ContinuousMap.exists_restrict_eq hballimageclosed FInvCmap
  -- `G` has a zero at `f 0`.
  have hG0 : G (f 0) = (0 : E) := by
    let fzero' : (f '' closedBall 0 1) := ⟨f 0, ⟨0, by simp, rfl⟩⟩
    have := congr($hG fzero')
    conv_lhs at this => simp [fzero']
    have H : (⟨f 0, ⟨0, by simp, rfl⟩⟩ : f '' closedBall 0 1) = FEquiv ⟨0, by simp⟩ :=
      Subtype.ext rfl
    simp [this, FInvCmap, fzero', H]
  let G' : C(E, E) := ⟨fun x => (G x : E), continuous_subtype_val.comp (ContinuousMap.continuous G)⟩
  -- Prove that `G` restricted to the image equals `FInvCmap`
  have hG_eq : ∀ y (hy : y ∈ f '' closedBall 0 1), G y = FInvCmap ⟨y, hy⟩ := by
    grind [ContinuousMap.restrict_apply]
  -- Now prove the left‑inverse property for `G'`
  have hG'_left_inv : ∀ x ∈ closedBall 0 1, G' (f x) = x := fun x hx =>
    (congr_arg Subtype.val (hG_eq (f x) (mem_image_of_mem f hx))).trans
    (congr_arg Subtype.val (FEquiv.symm_apply_apply ⟨x, hx⟩))
  -- Let `Gtilde : f(B^n) → ℝ^n` be a continuous function such that
  -- `‖G(y) - Gtilde(y)‖ ≤ 1 ∀ y ∈ f(B^n)`. Then `∃ y ∈ f (B^n)` such that `Gtilde(y)=0`.
  have hStability_of_zero (Gtilde : E → E) (hGtilde : ContinuousOn Gtilde (f '' closedBall 0 1))
      (hy : ∀ y ∈ (f '' closedBall 0 1), ‖G y - Gtilde y‖ ≤ 1) :
      ∃ y ∈ f '' closedBall 0 1, Gtilde y = 0 :=
    stability_of_zero f hf_cont G' hG'_left_inv Gtilde hGtilde hy
  -- By way of contradiction, we assume that `f(0)` is not an interior point of `f(B^n)` .
  -- From this, we construct a `Gtilde` as in the above lemma to derive a contradiction.
  by_contra hnotinterior
  -- `G` is continuous at `f(0)`.
  have hG_cont_at_f0 : ContinuousAt (fun x => (G x : E)) (f 0) := Continuous.continuousAt
    (continuous_subtype_val.comp (ContinuousMap.continuous G))
  rw [continuousAt_iff] at hG_cont_at_f0
  -- `G` is continuous on the whole space, so by picking `ε > 0` small enough,
  -- we can ensure `‖G(y)‖ ≤ 0.1` whenever `y ∈ ℝ^n` and `‖y - f(0)‖ ≤ 2ε`.
  obtain ⟨twoε, h2εpos, h2ε1⟩ := hG_cont_at_f0 0.1 (by norm_num)
  let ε : ℝ := twoε /2
  have hε1 : ε > 0 := half_pos h2εpos
  have h2εeq : twoε = 2 * ε := by ring
  -- As `f(0)` is not an interior point of `f(B^n)`, there exists a point `c ∈ ℝ^n` with
  -- `‖c - f(0)‖ < ε` not in `f(B^n)`.
  obtain ⟨c, hc1, hc2⟩ : ∃ c, dist c (f 0) < ε ∧ c ∉ f '' closedBall 0 1 := by
    rw [mem_interior] at hnotinterior
    push Not at hnotinterior
    specialize hnotinterior (ball (f 0) ε)
    simp only [isOpen_ball, mem_ball, dist_self, forall_const, imp_not_comm] at hnotinterior
    have hnotball := hnotinterior hε1
    rw [Set.not_subset] at hnotball
    obtain ⟨c, hc⟩ := hnotball
    exact ⟨c, ⟨mem_ball.mp hc.1, (Set.mem_compl_iff (f '' closedBall 0 1) c).mp hc.2⟩⟩
  -- `‖G(y)‖ ≤ 0.1` whenever `‖y - c‖ ≤ ε`.
  have hG_small (y : E) (h : ‖y - c‖ ≤ ε) : ‖(G y : E)‖ ≤ 0.1 := by
    rw [dist_eq_norm] at hc1
    have hdist : ‖y - f 0‖ < 2 * ε := by
      have hineq := norm_add_le (y - c) (c - f 0)
      simp only [sub_add_sub_cancel] at hineq; linarith
    grind [dist_zero_right, dist_eq_norm]
  -- Let `Σ₁ := {y ∈ f(B^n): ‖y - c‖ ≥ ε}`.
  let sigma1 : Set (E) := {y ∈ f '' closedBall 0 1 | ‖y - c‖ ≥ ε}
  -- Let `Σ₂ := {y ∈ ℝ^n : ‖y - c‖ = ε}`.
  let sigma2 : Set (E) := sphere c ε
  -- Let `Σ := Σ₁ ∪ Σ₂`.
  let sigma := sigma1 ∪ sigma2
  -- By construction, `Σ` is compact.
  -- `Σ₁` is compact.
  have hsigma1compact : IsCompact sigma1 := by
    rw [isCompact_iff_isClosed_bounded]
    -- `Σ₁` is the complement of the open ball, so it is closed.
    have hcompl : {y | ‖y - c‖ ≥ ε }ᶜ = ball c ε := by
      ext y; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, mem_ball_iff_norm]
    have hopen : IsOpen {y | ‖y - c‖ ≥ ε }ᶜ := hcompl ▸ isOpen_ball
    -- `f(B^n)` is compact as it is the image of a compact set under a continuous function
    -- As compact sets are bounded and `Σ₁` is contained in this, `Σ₁` is bounded.
    have himgcompact := IsCompact.image_of_continuousOn (isCompact_closedBall 0 1) hf_cont
    exact ⟨(IsClosed.and hballimageclosed ({isOpen_compl := (hopen) })), Bornology.IsBounded.subset
    (IsCompact.isBounded himgcompact) (Set.sep_subset (f '' closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)⟩
  -- It remains to be shown that `Σ₂` is compact, which follows from it being a sphere.
  have hsigmacompact : IsCompact sigma := IsCompact.union hsigma1compact (isCompact_sphere c ε)
  -- Let `Φ` be the function `Φ(y) := max(ε / ‖y - c‖, 1)) * (y - c)`.
  let Phi : (E) → (E) := fun y => c + (max (ε / ‖y - c‖) (1 : ℝ)) • (y - c)
  -- The image of `f(B^n)` under `Φ` is `Σ`.
  have hPhiimg (y : E) (hy : y ∈ f '' closedBall 0 1) : Phi y ∈ sigma := by
    simpa only [Phi, sigma, sigma1, sigma2] using
      radialProjection_mem_sep_union_sphere c hε1 hc2 hy
  -- `Φ` is continuous.
  have hPhicont : ContinuousOn Phi (f '' closedBall 0 1) := by
    refine ContinuousOn.add continuousOn_const (ContinuousOn.smul ?_
    (ContinuousOn.sub (continuousOn_id' (f '' closedBall 0 1)) continuousOn_const))
    rw [continuousOn_iff_continuous_domRestrict]
    exact Continuous.max ((Continuous.div continuous_const (Continuous.norm
    (Continuous.sub continuous_subtype_val continuous_const)))
    (fun y ↦ by
      change ‖(y : E) - c‖ ≠ 0
      rw [norm_ne_zero_iff, sub_ne_zero]
      intro hyc
      exact hc2 (hyc ▸ y.property)))
      continuous_const
  -- By construction, `G` is non-zero on `Σ₁`
  have hGavoids : ∀ y ∈ sigma1, G y ≠ (0 : (E)) := by
    intro y hy
    by_contra hGeq
    have hG_inj_on_image : Set.InjOn G (f '' closedBall 0 1) := by
      intro x hx y hy h
      have hx_eq : G x = FInvCmap ⟨x, hx⟩ := by grind
      have hy_eq : G y = FInvCmap ⟨y, hy⟩ := by grind
      rw [hx_eq, hy_eq] at h
      exact congr_arg Subtype.val (FEquiv.symm.injective h)
    have hyeq : y = f 0 := by
      have hf0_image : f 0 ∈ f '' closedBall 0 1 := ⟨0, by simp, rfl⟩
      have heq : G y = G (f 0) := SetCoe.ext (Eq.trans hGeq hG0.symm)
      exact hG_inj_on_image hy.1 hf0_image heq
    rw [Set.mem_sep_iff, hyeq] at hy
    rw [dist_eq_norm, ← norm_neg, neg_sub] at hc1; linarith
  -- The norm of `G` is continuous on `Σ₁`
  let normG : E → ℝ := fun y => ‖(G y : E)‖
  have hGconton : ContinuousOn G (f '' closedBall 0 1) := (ContinuousMap.continuous G).continuousOn
  have hgnormconton1 : ContinuousOn normG sigma1 :=
    ContinuousOn.norm (continuous_subtype_val.comp_continuousOn
    (ContinuousOn.mono hGconton (Set.sep_subset (f '' closedBall 0 1) fun x ↦ ‖x - c‖ ≥ ε)))
  -- As `Σ₁` is compact, `G` is bounded below on `Σ₁` by some `δ > 0`.
  -- We can shrink `δ` to assume `δ < 0.1`.
  obtain ⟨δ, hδ1, hδ2, hδ3⟩ : ∃ (δ : ℝ), 0 < δ ∧ δ < 0.1 ∧ ∀ y ∈ sigma1, δ ≤ ‖(G y : E)‖ := by
    by_cases hP : sigma1.Nonempty
    · obtain ⟨z, hz, hmin⟩ := IsCompact.exists_isMinOn hsigma1compact hP hgnormconton1
      let δ := min (normG z) (0.05)
      have hδ_pos : 0 < δ := lt_min_iff.mpr ⟨norm_pos_iff.mpr (hGavoids z hz), by norm_num⟩
      have hδ_lt_0_1 : δ < 0.1 := (min_le_right _ 0.05).trans_lt (by norm_num)
      have hδ_lower : ∀ y ∈ sigma1, normG y ≥ δ := fun y hy => (min_le_left _ _).trans (hmin hy)
      exact ⟨δ, hδ_pos, hδ_lt_0_1, hδ_lower⟩
    · exact ⟨0.05, by norm_num, by norm_num, fun y hy ↦ False.elim (hP ⟨y, hy⟩)⟩
  obtain ⟨P, hP_diff, hP_bound⟩ :=
    differentiable_approx_of_continuous hδ1 hsigmacompact (fun (y : E) => (G y : E)) (by fun_prop)
  have h0_notin_image : (0 : E) ∉ P '' sigma1 := by
    rintro ⟨y, hy, h⟩
    have hG : ‖(G y : E)‖ ≥ δ := hδ3 y hy
    have hP : ‖P y - G y‖ < δ := hP_bound y (Set.subset_union_left hy)
    simp only [h, _root_.zero_sub, norm_neg] at hP
    linarith
  -- It is possible that `P` vanishes on `Σ₂`, so we construct a perturbation `P'` that does not.
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  -- `Σ₂` has measure `0`; `P` is differentiable. The image of `Σ₂` under P also has measure `0`.
  have hP_image_null : volume (P '' (sphere c ε)) = 0 :=
    MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    hP_diff.differentiableOn
    (MeasureTheory.Measure.addHaar_sphere_of_ne_zero volume c (ne_of_gt hε1))
  -- As the image of `Σ₂` under P also has measure `0`, we can find a point v in the ball of radius
  -- δ that is neither in `Σ₁` nor `Σ₂`
  obtain ⟨v, hvnorm, hv1, hv2⟩ : ∃ (v : E), ‖v‖ < δ ∧ ¬ v ∈ P '' sigma1 ∧ ¬ v ∈ P '' sigma2 := by
    obtain hsigma1empty | hsigma1nonempty := sigma1.eq_empty_or_nonempty
    · have hball_pos := measure_ball_pos volume (0 : E) hδ1
      have hnot_subset2 : ¬ (ball 0 δ ⊆ P '' sigma2) := by
        intro hsub
        have : volume (ball (0 : E) δ) ≤ volume (P '' sigma2) := measure_mono hsub
        rw [show volume (P '' sigma2) = 0 by simpa [sigma2] using hP_image_null] at this
        exact (not_lt_of_ge this) (measure_ball_pos volume (0 : E) hδ1)
      rcases Set.not_subset.1 hnot_subset2 with ⟨v, hv_in_ball, hv_notin_sigma2⟩
      exact ⟨v, mem_ball_zero_iff.mp hv_in_ball, by simp [hsigma1empty], hv_notin_sigma2⟩
    have hP_cont : ContinuousOn (fun v => ‖P v‖) sigma1 := by fun_prop
    -- Let `d` be a point of `Σ₁` such that `‖P(d)‖` takes its minimum value.
    let ⟨d, _, hd⟩ := IsCompact.exists_isMinOn hsigma1compact hsigma1nonempty hP_cont
    -- Let `k` be the minimum of these two, to ensure both properties.
    let k := min ‖P d‖ δ
    obtain ⟨v, hvnorm, hv1⟩ : ∃ a ∈ ball 0 k, a ∉ P '' sphere c ε := by
      rw [← Set.not_subset]
      intro hsub
      have : volume (ball (0 : E) k) ≤ 0 := by rw [← hP_image_null]; exact measure_mono hsub
      exact LT.lt.false (lt_of_lt_of_le (measure_ball_pos volume (0 : E)
        (lt_min_iff.mpr ⟨by simp only [norm_pos_iff, ne_eq]; grind, hδ1⟩)) this)
    refine ⟨v, ⟨by linarith [mem_ball_zero_iff.mp hvnorm, min_le_right ‖P d‖ δ],
      ⟨fun hin1 => ?_, fun hin2 ↦ hv1 hin2⟩⟩⟩
    rcases hin1 with ⟨x, hx, rfl⟩
    linarith [(isMinOn_iff.mp hd) x hx, mem_ball_zero_iff.mp hvnorm, min_le_left ‖P d‖ δ]
  -- Let `P'` be the perturbation of `P` such that `P'(y) = P(y) - v`.
  let P' : C(E, E) := {toFun := fun y => P y - v, continuous_toFun:= by fun_prop}
  -- `v` is not in `Σ`.
  have hv_notin_sigma : v ∉ P '' sigma := by grind
  -- Define `Gtilde : f(B^n) → ℝ^n` as `Gtilde(y) = P'(Φ(y))`.
  let Gtilde : E → E := fun y => P' (Phi y)
  -- `Gtilde` is continuous.
  have hGtilde_cont : ContinuousOn Gtilde (f '' closedBall 0 1) :=
    (ContinuousMap.continuous P').comp_continuousOn hPhicont
  -- `P'` is never `0` on `Σ`. `Gtilde` is never `0`.
  have hGtilde_nonzero : ∀ y ∈ f '' closedBall 0 1, (P' ∘ Phi) y ≠ 0 :=
    fun y hy h_eq => (hv_notin_sigma) ⟨Phi y, hPhiimg y hy, sub_eq_zero.mp h_eq⟩
  -- We bound the difference between `G` and `Gtilde` by `1`.
  have hpeturb_bound : ∀ y ∈ f '' (closedBall (0 : E) 1), ‖G y - Gtilde y‖ ≤ 1 := by
    intro y hy
    -- There are two possible cases for the norm of `y - c`.
    by_cases hP : ε < ‖y - c‖
    · -- If `ε < ‖y - c‖`, then `Φ(y) = y`
      -- Thus `Gtilde(y) = G(Φ(y))`
      have hPhi : Phi y = y := by
        have hright : ε / ‖y - c‖ < 1 := by
          have hyc : 0 < ‖y - c‖ := by linarith
          rwa [div_lt_one hyc]
        simp [Phi, max_eq_right_of_lt hright]
      simp only [hPhi, Gtilde]
      -- We are using `P' = P - v`, `∀ y ∈ Σ, ‖P y - ↑(G y)‖ < δ` and `‖v‖ < δ`
      calc
        ‖G y - P' y‖ = ‖G y - (P y - v)‖ := rfl
        _ ≤ _ := by grw [sub_sub_eq_add_sub, add_sub_right_comm, norm_add_le, norm_sub_rev,
          hP_bound y (Or.inl ⟨hy, le_of_lt hP⟩), add_comm, hvnorm]
        _ ≤ _ := by linarith
    · -- If `‖y - c‖ ≤ ε`, then `Φ y ∈ Σ₂`.
      simp only [not_lt] at hP
      have hy_neq_c : c ≠ y := by grind
      have hleft : 1 ≤ ε / ‖y - c‖ :=
        (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hy_neq_c)))).mpr hP
      have hPhi : Phi y = c + (ε / ‖y - c‖) • (y - c) := by grind [max_eq_left]
      have hyimg : Phi y ∈ sphere c ε := by
        simp [hPhi, mem_sphere_iff_norm, add_sub_cancel_left, norm_smul,
          (sub_ne_zero_of_ne (Ne.symm hy_neq_c)), hε1.le]
      have hP_approx_le : ‖P (Phi y)‖ ≤ ‖(G (Phi y) : E)‖ + δ := by
        linarith [norm_sub_rev (P (Phi y)) (G (Phi y) : E), hP_bound (Phi y) (Or.inr hyimg),
        norm_le_norm_add_norm_sub' (P (Phi y)) (G (Phi y))]
      have hG_phi_small : ‖(G (Phi y) : E)‖ ≤ 0.1 := by
        rw [dist_eq_norm] at hc1
        have hdist : ‖Phi y - f 0‖ < 2 * ε := calc
          ‖Phi y - f 0‖  ≤ ‖Phi y - c‖ + ‖c - f 0‖ := by grw [← sub_add_sub_cancel,norm_add_le]
          _ = ε + ‖c - f 0‖ := by rw [mem_sphere_iff_norm.mp hyimg]
          _ < ε + ε := add_lt_add_right hc1 ε
          _ = 2 * ε := by ring
        rw [← h2εeq, ← dist_eq_norm] at hdist
        grind [h2ε1 hdist, dist_zero_right]
      specialize hG_small y hP
      calc
        ‖G y - P' (Phi y)‖
          = ‖G y - (P (Phi y) - v)‖ := rfl
        _ ≤ ‖(G y : E)‖ + ‖P (Phi y)‖ + ‖v‖ := by grw [sub_sub_eq_add_sub, add_sub_right_comm,
          norm_add_le, norm_sub_le]
        _ ≤ _ := by linarith
  -- We derive a contradiction using the lemma for the stability of zero.
  obtain ⟨y, hy1, hy2⟩ := (((hStability_of_zero)) Gtilde hGtilde_cont) hpeturb_bound
  exact hGtilde_nonzero y hy1 hy2

/-- The invariance of domain theorem: if `U ⊆ E` is open,
  `f : E → E` is continuous on `U` and injective on `U`, then the image `f '' U` is open in `E`. -/
theorem invariance_of_domain_open_map (f : E → E) (U : Set E) (hU : IsOpen U)
    (hf_cont : ContinuousOn f U) (hf_inj : Set.InjOn f U) : IsOpen (f '' U) := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨x, hxU, hfx⟩
  rw [isOpen_iff] at hU
  have hclosedball: ∀ x' ∈ U, ∃ ε' > 0, closedBall x' ε' ⊆ U := by
    intro x' hx'
    obtain ⟨ε, hε, hball⟩ := hU x' hx'
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (div_two_lt_of_pos hε)).trans hball⟩
  obtain ⟨ε, hε , hclosedball⟩ := hclosedball x hxU
  -- Define `g` as a scaling and translating function.
  let g := fun (v : E) => ε • v + x
  have hg_inj : Function.Injective g := by simp [Function.Injective, g, hε.ne']
  have h_g_eq : g '' closedBall 0 1 = closedBall x ε := by
    rw [← Set.image_image (fun v ↦ v + x) (fun v ↦ ε • v) (closedBall 0 1), Set.image_smul,
      smul_unitClosedBall]
    simp only [Real.norm_eq_abs, Set.image_add_right, preimage_add_right_closedBall,
      sub_neg_eq_add, zero_add]
    rw [abs_of_pos hε]
  let e := f ∘ g
  have he_cont : ContinuousOn e (closedBall 0 1):=
    ContinuousOn.image_comp_continuous (h_g_eq ▸ hf_cont.mono hclosedball) (by fun_prop)
  have he_inj : Set.InjOn e (closedBall 0 1) := by
    rw [Set.InjOn.comp_iff hg_inj.injOn, h_g_eq]
    exact Set.InjOn.mono hclosedball hf_inj
  -- `e(0)` is in the interior using the prior version.
  have h_interior : e 0 ∈ interior (e '' closedBall 0 1) :=
    invariance_of_domain_interior e he_cont he_inj
  refine ⟨interior (f '' U), ⟨interior_subset, isOpen_interior, ?_⟩⟩
  unfold e g at h_interior
  rw [Set.image_comp, h_g_eq] at h_interior
  simp only [Function.comp_apply, smul_zero, zero_add] at h_interior
  grw [hfx, hclosedball] at h_interior
  exact h_interior

/-- If `f` is a partial equivalence continuous on its source, then it maps
    neighbourhoods of `x` (contained in the source) to neighbourhoods of `f(x)`. -/
theorem invariance_of_domain_partial_equiv {x : E} {s : Set E} {f : PartialEquiv E E}
    (hCont : ContinuousOn f f.source) : s ∈ nhds x → s ⊆ f.source →
    f '' s ∈ nhds (f x) := by
  intro hsin hsubset
  obtain ⟨a, ha1, ha2, ha3⟩ := _root_.mem_nhds_iff.mp hsin
  exact _root_.mem_nhds_iff.mpr ⟨f '' a, Set.image_mono ha1, invariance_of_domain_open_map (↑f) a
  ha2 (ContinuousOn.mono hCont (ha1.trans hsubset)) (Set.InjOn.mono (ha1.trans hsubset)
  (PartialEquiv.injOn f)), Set.mem_image_of_mem (↑f) ha3⟩

open Function ModelWithCorners TopologicalSpace

/-- A topological space has invariance of domain if each continuous partial equivalence maps
neighbourhoods contained in its source to neighbourhoods of the corresponding image point. -/
class HasInvarianceOfDomain (X : Type*) [TopologicalSpace X] : Prop where
  invariance_of_domain {x : X} {s : Set X} {f : PartialEquiv X X}
      (hCont : ContinuousOn f f.source) :
    s ∈ nhds x → s ⊆ f.source → f '' s ∈ nhds (f x)

/-- Apply a `HasInvarianceOfDomain` instance to a continuous partial equivalence. -/
theorem maps_nhds_to_nhds (X : Type*) [TopologicalSpace X]
    [instID : HasInvarianceOfDomain X] {x : X} {s : Set X} {f : PartialEquiv X X}
    (hCont : ContinuousOn f f.source) :
    s ∈ nhds x → s ⊆ f.source → f '' s ∈ nhds (f x) :=
  instID.invariance_of_domain hCont

/-- Brouwer's fixed-point theorem supplies invariance of domain in a finite-dimensional real
inner product space. -/
instance instHasInvarianceOfDomainOfBrouwerFixedPoint : HasInvarianceOfDomain E where
  invariance_of_domain := invariance_of_domain_partial_equiv

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

omit [ChartedSpace H M] in
variable (I) (M) in
/-- If some `OpenPartialHomeomorph M H` sends a point to the interior of `range I`, then
so does any other `OpenPartialHomeomorph M H`. -/
theorem independence_of_interior [HasInvarianceOfDomain E] {x : M}
    {f g : OpenPartialHomeomorph M H} (hfSource : x ∈ f.source) (hgSource : x ∈ g.source) :
    I (f x) ∈ interior (range I) → I (g x) ∈ interior (range I) := by
  intro hfInterior
  apply mem_interior_iff_mem_nhds.mp at hfInterior
  apply mem_interior_iff_mem_nhds.mpr
  let f' : PartialEquiv M E := f.toPartialEquiv.trans I.toPartialEquiv
  have hf'symmCont : ContinuousOn f'.symm f'.target := by
    apply ContinuousOn.comp (OpenPartialHomeomorph.continuousOn f.symm) ?_ ?_
    · simp only [PartialEquiv.restr_coe_symm, toPartialEquiv_coe_symm]
      exact continuousOn_symm I
    · simp only [PartialEquiv.symm_source, PartialEquiv.restr_coe_symm,
        toPartialEquiv_coe_symm, OpenPartialHomeomorph.symm_toPartialEquiv]
      simp only [f', PartialEquiv.trans_target, target_eq, toPartialEquiv_coe_symm]
      exact fun _ hy ↦ mem_preimage.mp <| mem_of_mem_inter_right hy
  let U₀ : Set M := f.source ∩ g.source
  have hU₀nhds : U₀ ∈ nhds x := by
    apply IsOpen.mem_nhds (IsOpen.inter f.open_source g.open_source) ⟨hfSource, hgSource⟩
  let U : Set E := (f') '' U₀
  have hUf'target : U ⊆ f'.target := by
    rw [← f'.image_source_eq_target]
    apply image_mono
    simpa only [f', PartialEquiv.trans_source, source_eq, preimage_univ, inter_univ] using
      (inter_subset_left : U₀ ⊆ f.source)
  have hf'MapsToU : MapsTo f'.symm U U₀ := by
    intro _ ⟨_, _, hzy⟩
    subst hzy
    simp_all [f', U₀]
  let g' : PartialEquiv M E := g.toPartialEquiv.trans I.toPartialEquiv
  have hg'Cont : ContinuousOn g' U₀ := by
    apply ContinuousOn.mono ?_ <| show U₀ ⊆ g.source by exact inter_subset_right
    apply ContinuousOn.comp ?_ g.continuousOn g.mapsTo
    apply ContinuousOn.mono ?_ (fun _ _ ↦ trivial)
    exact continuousOn_univ.mpr <| I.continuous
  let φ : PartialEquiv E E := f'.symm.trans g'
  have hφCont : ContinuousOn φ U := by
    simp only [PartialEquiv.coe_trans, φ]
    apply ContinuousOn.comp (g := g') hg'Cont ?_ hf'MapsToU
    exact ContinuousOn.mono hf'symmCont hUf'target
  rw [← show φ (I (f x)) = I (g x)
      by simp [φ, f', g', OpenPartialHomeomorph.left_inv f hfSource]]
  have hUφsource : U ⊆ φ.source := by
    rw [PartialEquiv.trans_source]
    simp only [PartialEquiv.symm_source, subset_inter_iff]
    simp_all only [PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      toPartialEquiv_coe_symm, PartialEquiv.trans_target, target_eq, Filter.inter_mem_iff,
      PartialEquiv.coe_trans, toPartialEquiv_coe, OpenPartialHomeomorph.toFun_eq_coe, comp_apply,
      subset_inter_iff, image_subset_iff, mapsTo_inter, mapsTo_image_iff, and_self,
      PartialEquiv.trans_source, source_eq, preimage_univ, inter_univ, true_and, f', U₀, U, g', φ]
    exact hf'MapsToU.2
  have hUNhds : U ∈ nhds (I (f x)) := by
    apply nhds_of_nhdsWithin_of_nhds hfInterior
    rw [show U = I '' (f '' U₀) by rw [← image_comp I f U₀]; rfl]
    apply image_mem_nhdsWithin I
    exact OpenPartialHomeomorph.image_mem_nhds f hfSource hU₀nhds
  let φ' : PartialEquiv E E := φ.restr U
  have hφCont'U : ContinuousOn φ' U := by
    simpa only [φ', PartialEquiv.restr_coe] using hφCont
  have hφ'Cont : ContinuousOn φ' φ'.source := by
    rw [PartialEquiv.restr_source φ U]
    exact ContinuousOn.mono hφCont'U inter_subset_right
  have : U ⊆ φ'.source := by
    rw [PartialEquiv.restr_source]
    exact subset_inter hUφsource fun _ a ↦ a
  obtain hMapsNhds := maps_nhds_to_nhds E hφ'Cont hUNhds this
  have : (φ') '' U ⊆ range I := by
    rintro _ ⟨z, _, hzy⟩
    rw [← hzy]
    exact mem_range_self (g (f'.symm z))
  exact Filter.mem_of_superset hMapsNhds this

variable (I) in
/-- A point lies in the interior of M iff *any* `OpenPartialHomeomorph M H`
sends it to the interior of `range I`. -/
theorem isInteriorPoint_iff_any_chart {x : M} [HasInvarianceOfDomain E]
    {f : OpenPartialHomeomorph M H} (hfSource : x ∈ f.source) :
    I.IsInteriorPoint x ↔ I (f x) ∈ interior (range I) := by
  constructor <;> intro hx
  · apply isInteriorPoint_iff.mp at hx
    exact (independence_of_interior I M (ChartedSpace.mem_chart_source x) hfSource)
          (by exact (interior_mono <| extChartAt_target_subset_range x) hx)
  · apply isInteriorPoint_iff.mpr
    apply (chartAt H x).mem_interior_extend_target
          ((chartAt H x).map_source <| ChartedSpace.mem_chart_source x)
    exact independence_of_interior I M hfSource (ChartedSpace.mem_chart_source x) hx

variable (I) in
/-- A point lies on the boundary of M iff *any* `OpenPartialHomeomorph M H`
sends it to the frontier of `range I`. -/
theorem isBoundaryPoint_iff_any_chart {x : M} [HasInvarianceOfDomain E]
    {f : OpenPartialHomeomorph M H} (hfSource : x ∈ f.source) :
    (I.IsBoundaryPoint x ↔ I (f x) ∈ frontier (range I)) := by
  apply not_iff_not.mp
  apply Iff.trans <| Iff.symm <| I.isInteriorPoint_iff_not_isBoundaryPoint x
  obtain hInt := isInteriorPoint_iff_any_chart I hfSource
  rw [← self_sdiff_frontier] at hInt
  constructor <;> intro hx
  · exact notMem_of_mem_sdiff <| hInt.mp hx
  · exact hInt.mpr <| mem_sdiff_of_mem (mem_range_self (f x)) hx

/-- An embedded open part of the model vector space has open image in a manifold modeled on
`I`.  This is the manifold-with-boundary form of invariance of domain needed at an interior
edge of an embedded finite triangle complex.

The use of the *extended* target chart is important: if the image point were on the manifold
boundary, invariance of domain would produce an ambient vector-space neighborhood contained in
`range I`, which is impossible there. -/
theorem isOpen_range_of_isOpen_of_continuous_injective
    (I : ModelWithCorners 𝕜 E H) [HasInvarianceOfDomain E]
    {U : Set E} (hU : IsOpen U) (f : U → M)
    (hfcont : Continuous f) (hfinj : Function.Injective f) :
    IsOpen (Set.range f) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨u, rfl⟩
  let c : PartialEquiv M E := extChartAt I (f u)
  let f₀ : E → M :=
    Function.extend ((↑) : U → E) f (fun _ ↦ f u)
  have hf₀_eq (x : U) : f₀ x.1 = f x := by
    exact Function.Injective.extend_apply Subtype.val_injective f
      (fun _ ↦ f u) x
  have hf₀_cont : ContinuousOn f₀ U := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hfcont using 1
    funext x
    exact hf₀_eq x
  let W : Set E := U ∩ f₀ ⁻¹' c.source
  have hWopen : IsOpen W :=
    hf₀_cont.isOpen_inter_preimage hU (isOpen_extChartAt_source (I := I) (f u))
  have huW : u.1 ∈ W := by
    refine ⟨u.2, ?_⟩
    change f₀ u.1 ∈ c.source
    rw [hf₀_eq u]
    exact mem_extChartAt_source (I := I) (f u)
  let g : E → E := fun x ↦ c (f₀ x)
  have hg_cont : ContinuousOn g W := by
    apply (continuousOn_extChartAt (I := I) (f u)).comp
      (hf₀_cont.mono inter_subset_left)
    exact fun x hx ↦ hx.2
  have hg_inj : Set.InjOn g W := by
    intro x hx y hy hxy
    have hf₀xy : f₀ x = f₀ y :=
      c.injOn hx.2 hy.2 hxy
    have hfx :
        f (⟨x, hx.1⟩ : U) = f (⟨y, hy.1⟩ : U) := by
      rw [← hf₀_eq ⟨x, hx.1⟩, ← hf₀_eq ⟨y, hy.1⟩]
      exact hf₀xy
    exact congrArg Subtype.val (hfinj hfx)
  let φ : PartialEquiv E E :=
    hg_inj.toPartialEquiv g W
  have hφ_cont : ContinuousOn φ φ.source := by
    change ContinuousOn g W
    exact hg_cont
  have hWnhds : W ∈ nhds u.1 :=
    hWopen.mem_nhds huW
  have himage :
      g '' W ∈ nhds (g u.1) := by
    have h :=
      maps_nhds_to_nhds E hφ_cont hWnhds
        (show W ⊆ φ.source by
          change W ⊆ W
          exact subset_rfl)
    change g '' W ∈ nhds (g u.1) at h
    exact h
  obtain ⟨O, hOsub, hOopen, hguO⟩ :=
    _root_.mem_nhds_iff.mp himage
  let Z : Set M := c.source ∩ c ⁻¹' O
  have hZopen : IsOpen Z :=
    (continuousOn_extChartAt (I := I) (f u)).isOpen_inter_preimage
      (isOpen_extChartAt_source (I := I) (f u)) hOopen
  have hfuZ : f u ∈ Z := by
    refine ⟨mem_extChartAt_source (I := I) (f u), ?_⟩
    change c (f u) ∈ O
    rw [← hf₀_eq u]
    exact hguO
  have hZrange : Z ⊆ Set.range f := by
    intro y hy
    have hcyO : c y ∈ O := hy.2
    obtain ⟨x, hxW, hxcoord⟩ := hOsub hcyO
    have hcy :
        c y = c (f₀ x) := by
      exact hxcoord.symm
    have hyf₀ : y = f₀ x :=
      c.injOn hy.1 hxW.2 hcy
    refine ⟨⟨x, hxW.1⟩, ?_⟩
    rw [← hf₀_eq ⟨x, hxW.1⟩]
    exact hyf₀.symm
  exact Filter.mem_of_superset (hZopen.mem_nhds hfuZ) hZrange

/-- Embedding-form wrapper for
`isOpen_range_of_isOpen_of_continuous_injective`. -/
theorem isOpen_range_of_isOpen_of_isEmbedding
    (I : ModelWithCorners 𝕜 E H) [HasInvarianceOfDomain E]
    {U : Set E} (hU : IsOpen U) (f : U → M)
    (hf : _root_.Topology.IsEmbedding f) :
    IsOpen (Set.range f) :=
  isOpen_range_of_isOpen_of_continuous_injective I hU f
    hf.continuous hf.injective

/-- At an interior point of the ambient manifold, re-embedding a fixed source cannot turn the
corresponding local sheet into a boundary point of the new image.

This is deliberately an interior-point statement.  It is false at a manifold-boundary point:
an embedding of a half-plane may bend its boundary into the ambient interior. -/
theorem mem_interior_range_of_eq_of_mem_interior_range_of_isInteriorPoint
    (I : ModelWithCorners 𝕜 E H) [HasInvarianceOfDomain E]
    {X : Type*} [TopologicalSpace X]
    {f g : X → M} (hf : _root_.Topology.IsEmbedding f)
    (hg : _root_.Topology.IsEmbedding g) {x : X}
    (hx : f x ∈ interior (Set.range f))
    (hxi : I.IsInteriorPoint (f x)) :
    g x ∈ interior (Set.range g) := by
  let z : M := f x
  let c : PartialEquiv M E := extChartAt I z
  let W : Set E :=
    interior c.target ∩ c.symm ⁻¹' interior (Set.range f)
  have hWopen : IsOpen W := by
    apply
      ((continuousOn_extChartAt_symm (I := I) z).mono interior_subset
        ).isOpen_inter_preimage isOpen_interior isOpen_interior
  have hzTarget : c z ∈ interior c.target := by
    exact I.isInteriorPoint_iff.mp hxi
  have hcz : c.symm (c z) = z :=
    c.left_inv (mem_extChartAt_source (I := I) z)
  have hczW : c z ∈ W := by
    refine ⟨hzTarget, ?_⟩
    change c.symm (c z) ∈ interior (Set.range f)
    rw [hcz]
    exact hx
  have hcSymm : Continuous (fun w : W ↦ c.symm w.1) := by
    apply ContinuousOn.domRestrict
    exact (continuousOn_extChartAt_symm (I := I) z).mono fun w hw ↦
      interior_subset hw.1
  let toOldRange : W → Set.range f :=
    fun w ↦ ⟨c.symm w.1, interior_subset w.2.2⟩
  have htoOldRange : Continuous toOldRange :=
    Continuous.subtype_mk hcSymm _
  let source : W → X :=
    fun w ↦ hf.toHomeomorph.symm (toOldRange w)
  have hsourceCont : Continuous source :=
    hf.toHomeomorph.symm.continuous.comp htoOldRange
  have hsourceInj : Function.Injective source := by
    intro u v huv
    have huvRange : toOldRange u = toOldRange v :=
      hf.toHomeomorph.symm.injective huv
    have huvSurface : c.symm u.1 = c.symm v.1 :=
      congrArg Subtype.val huvRange
    apply Subtype.ext
    exact c.symm.injOn (interior_subset u.2.1) (interior_subset v.2.1)
      huvSurface
  let localMap : W → M := fun w ↦ g (source w)
  have hlocalCont : Continuous localMap :=
    hg.continuous.comp hsourceCont
  have hlocalInj : Function.Injective localMap :=
    hg.injective.comp hsourceInj
  have hlocalOpen : IsOpen (Set.range localMap) :=
    isOpen_range_of_isOpen_of_continuous_injective I hWopen localMap
      hlocalCont hlocalInj
  let w₀ : W := ⟨c z, hczW⟩
  have hsourceW₀ : source w₀ = x := by
    apply hf.injective
    change (hf.toHomeomorph (source w₀)).1 = f x
    rw [hf.toHomeomorph.apply_symm_apply]
    change c.symm (c z) = f x
    exact hcz
  have hlocalAt : localMap w₀ = g x := by
    rw [show localMap w₀ = g (source w₀) by rfl, hsourceW₀]
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset
    (hlocalOpen.mem_nhds ⟨w₀, hlocalAt⟩)
  rintro y ⟨w, rfl⟩
  exact Set.mem_range_self (source w)

end LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain
