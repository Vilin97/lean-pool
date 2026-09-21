/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Module.Span
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Auxiliary lemmas for John's ellipsoid theorem

General-purpose results needed by the proof of the John decomposition of identity
(`BasicResults/John.lean`), none of which are specific to convex bodies. Each is a
candidate for upstreaming to Mathlib:

* `Real.exp_sub_two_mul_sq_le` and `one_sub_two_mul_sum_sq_le_prod_one_add` — a
  quantitative Weierstrass-type product bound: if `∑ aᵢ = 0` and `|aᵢ| ≤ 1/2`, then
  `∏ (1 + aᵢ) ≥ 1 - 2 ∑ aᵢ²`. This is why a trace-zero perturbation `1 + tH` of the
  identity loses determinant only to *second* order in `t`.
* `IsCompact.convexHull` — in a finite-dimensional real normed space, the convex hull
  of a compact set is compact. Mathlib's `TotallyBounded.convexHull` yields total
  boundedness of the hull, hence compactness only of its *closure*; the work here
  is that in finite dimension the hull is already closed.
* `Seminorm.exists_inner_le_of_apply` — the supporting-vector form of Hahn–Banach
  dominated by a *seminorm* on an inner product space over `RCLike 𝕜`: every point
  admits a supporting functional `x ↦ re ⟪x, v⟫` of the seminorm attaining its value
  at the point. The extension itself is Mathlib's
  `Module.Dual.exists_extension_of_le_seminorm`; what is added is the representing
  vector `v`.
* `ContinuousLinearMap.exists_trace_repr` — trace duality: every linear functional on
  the endomorphisms of a finite-dimensional inner product space is `A ↦ tr (A ∘ G)`
  for some endomorphism `G`.
-/

open scoped InnerProductSpace ComplexConjugate

/-! ## A quantitative Weierstrass product inequality -/

/-- Pointwise exponential bound: `exp (a - 2a²) ≤ 1 + a` for `a ≥ -1/2`.

This is the elementary inequality behind the second-order determinant bound: it
follows from `1 + x ≤ exp x` applied to `x = 2a² - a`, since
`(1 + 2a² - a) * (1 + a) = 1 + a² (1 + 2a) ≥ 1` when `1 + 2a ≥ 0`. -/
lemma Real.exp_sub_two_mul_sq_le {a : ℝ} (ha : -(1 / 2) ≤ a) :
    Real.exp (a - 2 * a ^ 2) ≤ 1 + a := by
  have h₂ : Real.exp (a - 2 * a ^ 2) = (Real.exp (2 * a ^ 2 - a))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  have hexp := Real.add_one_le_exp (2 * a ^ 2 - a)
  rw [h₂, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  nlinarith [mul_nonneg (sq_nonneg a) (by linarith : (0 : ℝ) ≤ 1 + 2 * a),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a)
      (by linarith : (0 : ℝ) ≤ Real.exp (2 * a ^ 2 - a) - 1 - (2 * a ^ 2 - a))]

/-- **Weierstrass-type product lower bound.** If `∑ aᵢ = 0` and every `|aᵢ| ≤ 1/2`,
then `∏ (1 + aᵢ) ≥ 1 - 2 ∑ aᵢ²`.

Mathematically: a multiplicative perturbation with vanishing first-order term loses
volume only to second order. Proof: `∏ (1 + aᵢ) ≥ ∏ exp (aᵢ - 2aᵢ²)
= exp (∑ aᵢ - 2 ∑ aᵢ²) = exp (-2 ∑ aᵢ²) ≥ 1 - 2 ∑ aᵢ²`, using
`Real.exp_sub_two_mul_sq_le` and `Real.add_one_le_exp`. -/
lemma one_sub_two_mul_sum_sq_le_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, |a i| ≤ 1 / 2) (hsum : ∑ i ∈ s, a i = 0) :
    1 - 2 * ∑ i ∈ s, a i ^ 2 ≤ ∏ i ∈ s, (1 + a i) := by
  have key : Real.exp (∑ i ∈ s, (a i - 2 * a i ^ 2)) ≤ ∏ i ∈ s, (1 + a i) := by
    rw [Real.exp_sum]
    exact Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
      fun i hi => Real.exp_sub_two_mul_sq_le (abs_le.mp (ha i hi)).1
  have hs : ∑ i ∈ s, (a i - 2 * a i ^ 2) = -(2 * ∑ i ∈ s, a i ^ 2) := by
    rw [Finset.sum_sub_distrib, hsum, Finset.mul_sum]
    simp
  calc 1 - 2 * ∑ i ∈ s, a i ^ 2 = -(2 * ∑ i ∈ s, a i ^ 2) + 1 := by ring
    _ ≤ Real.exp (-(2 * ∑ i ∈ s, a i ^ 2)) := Real.add_one_le_exp _
    _ = Real.exp (∑ i ∈ s, (a i - 2 * a i ^ 2)) := by rw [hs]
    _ ≤ ∏ i ∈ s, (1 + a i) := key

/-! ## The convex hull of a compact set is compact (finite dimensions) -/

section CompactConvexHull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The convex hull of a compact set is compact**, in a finite-dimensional real normed
space. Mathlib has the finite-set case (`Set.Finite.isCompact_convexHull`) and
`TotallyBounded.convexHull`, which gives total boundedness of the hull and so
compactness only of its *closure*; the point here is that in finite dimension the
hull is already closed.

By Carathéodory's theorem every point of the hull is a convex combination of at most
`finrank ℝ E + 1` affinely independent points of `s`, so the hull is the image of the
compact set `stdSimplex × s^(finrank+1)` under the continuous map `(w, z) ↦ ∑ᵢ wᵢ • zᵢ`. -/
theorem IsCompact.convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  rcases Set.eq_empty_or_nonempty s with rfl | ⟨x₀, hx₀⟩
  · simp only [convexHull_empty]; exact isCompact_empty
  have hK : IsCompact ((stdSimplex ℝ (Fin (Module.finrank ℝ E + 1))) ×ˢ
      Set.univ.pi fun _ : Fin (Module.finrank ℝ E + 1) => s) :=
    IsCompact.prod (isCompact_stdSimplex ℝ (Fin (Module.finrank ℝ E + 1)))
      (isCompact_univ_pi fun _ => hs)
  have himg : _root_.convexHull ℝ s =
      (fun p : (Fin (Module.finrank ℝ E + 1) → ℝ) × (Fin (Module.finrank ℝ E + 1) → E) =>
          ∑ i, p.1 i • p.2 i) ''
        ((stdSimplex ℝ (Fin (Module.finrank ℝ E + 1))) ×ˢ
          Set.univ.pi fun _ : Fin (Module.finrank ℝ E + 1) => s) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ι, hfin, z, w, hzs, hai, hw0, hw1, hxeq⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      let : Fintype ι := hfin
      -- Carathéodory: affinely independent families have at most `finrank + 1` members.
      have hcard : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
        le_trans hai.card_le_finrank_succ (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      -- embed the index type into `Fin (finrank + 1)`
      set f : ι → Fin (Module.finrank ℝ E + 1) :=
        fun j => Fin.castLE hcard ((Fintype.equivFin ι) j) with hf
      have hfinj : Function.Injective f := by
        intro a b hab
        have h2 := congrArg Fin.val hab
        simp only [hf, Fin.val_castLE] at h2
        exact (Fintype.equivFin ι).injective (Fin.ext h2)
      -- pad the family by weight-0 copies of a fixed point of `s`
      set w' : Fin (Module.finrank ℝ E + 1) → ℝ :=
        fun i => if h : ∃ j, f j = i then w h.choose else 0 with hw'
      set z' : Fin (Module.finrank ℝ E + 1) → E :=
        fun i => if h : ∃ j, f j = i then z h.choose else x₀ with hz'
      have hchoose : ∀ (j : ι) (h : ∃ j', f j' = f j), h.choose = j :=
        fun j h => hfinj h.choose_spec
      have hw'f : ∀ j, w' (f j) = w j := fun j => by
        simp only [hw']
        rw [dif_pos ⟨j, rfl⟩, hchoose j ⟨j, rfl⟩]
      have hz'f : ∀ j, z' (f j) = z j := fun j => by
        simp only [hz']
        rw [dif_pos ⟨j, rfl⟩, hchoose j ⟨j, rfl⟩]
      have hw'zero : ∀ i, i ∉ Finset.univ.image f → w' i = 0 := fun i hi => by
        simp only [hw']
        exact dif_neg fun h =>
          hi (Finset.mem_image.mpr ⟨h.choose, Finset.mem_univ _, h.choose_spec⟩)
      have hw'sum : ∑ i, w' i = 1 := by
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))
          fun i _ hi => hw'zero i hi]
        rw [Finset.sum_image fun a _ b _ hab => hfinj hab]
        rw [Finset.sum_congr rfl fun j _ => hw'f j]
        exact hw1
      have hsum : ∑ i, w' i • z' i = x := by
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f))
          fun i _ hi => by rw [hw'zero i hi, zero_smul]]
        rw [Finset.sum_image fun a _ b _ hab => hfinj hab]
        rw [Finset.sum_congr rfl fun j _ => by rw [hw'f j, hz'f j]]
        exact hxeq
      refine ⟨(w', z'), ⟨⟨fun i => ?_, hw'sum⟩, Set.mem_univ_pi.mpr fun i => ?_⟩, hsum⟩
      · simp only [hw']
        by_cases h : ∃ j, f j = i
        · rw [dif_pos h]; exact (hw0 _).le
        · rw [dif_neg h]
      · simp only [hz']
        by_cases h : ∃ j, f j = i
        · rw [dif_pos h]; exact hzs (Set.mem_range_self _)
        · rw [dif_neg h]; exact hx₀
    · rintro x ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
      exact mem_convexHull_of_exists_fintype w z hw.1 hw.2
        (fun i => hz i (Set.mem_univ i)) rfl
  rw [himg]
  refine hK.image (continuous_finsetSum _ fun i _ => ?_)
  exact ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)

end CompactConvexHull

/-! ## Hahn–Banach dominated by a seminorm, inner-product form -/

section SeminormHahnBanach

open RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E]

/-- **Hahn–Banach dominated by a seminorm**, inner-product form. For every continuous
seminorm `q` on a finite-dimensional inner product space over `RCLike 𝕜` and every point
`u`, there is a vector `v` whose associated real functional `x ↦ re ⟪x, v⟫` is dominated
by `q` everywhere and attains the value `q u` at `u`.

Mathematically: the convex body `{q ≤ 1}` has a supporting hyperplane at each boundary
point. On the `𝕜`-span of `u` the functional `c • u ↦ c · q u` satisfies `‖f z‖ = q z`
outright, so Mathlib's seminorm Hahn–Banach
(`Module.Dual.exists_extension_of_le_seminorm`) extends it to all of `E` keeping that
bound; the Riesz isomorphism (`InnerProductSpace.toDual`) then represents the extension
by a vector. -/
theorem Seminorm.exists_inner_le_of_apply (q : Seminorm 𝕜 E) (u : E) :
    ∃ v : E, (∀ x, re ⟪x, v⟫_𝕜 ≤ q x) ∧ re ⟪u, v⟫_𝕜 = q u := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, fun x => by simp, by simp⟩
  -- `f : c • u ↦ c * q u` on the span of `u`; at `z = c • u` both sides are `‖c‖ * q u`
  set f : Module.Dual 𝕜 (𝕜 ∙ u) :=
    (q u : 𝕜) • (ContinuousLinearEquiv.coord 𝕜 u hu).toLinearMap with hf
  have hcoord : ∀ z : (𝕜 ∙ u), (ContinuousLinearEquiv.coord 𝕜 u hu z) • u = (z : E) :=
    fun z => LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul 𝕜 E u hu z
  have hdom : ∀ z : (𝕜 ∙ u), ‖f z‖ ≤ q z := by
    intro z
    have hq : q (z : E) = ‖ContinuousLinearEquiv.coord 𝕜 u hu z‖ * q u := by
      rw [← hcoord z, map_smul_eq_mul]
    rw [hf]
    simp only [LinearMap.smul_apply, smul_eq_mul, norm_mul, RCLike.norm_ofReal,
      abs_of_nonneg (apply_nonneg q u), hq]
    exact le_of_eq (mul_comm _ _)
  -- extend to all of `E`, still dominated by `q`
  obtain ⟨g, hg_eq, hg_le⟩ := Module.Dual.exists_extension_of_le_seminorm (𝕜 ∙ u) f hdom
  have hgu : g u = (q u : 𝕜) := by
    rw [hg_eq ⟨u, Submodule.mem_span_singleton_self u⟩, hf]
    simp [RCLike.real_smul_eq_coe_mul]
  -- represent the extension by a vector via Riesz
  set v : E := (InnerProductSpace.toDual 𝕜 E).symm (LinearMap.toContinuousLinearMap g) with hv
  have hre : ∀ x, re ⟪x, v⟫_𝕜 = re (g x) := fun x => by
    rw [← inner_conj_symm x v, RCLike.conj_re, hv, InnerProductSpace.toDual_symm_apply]
    rfl
  exact ⟨v, fun x => (hre x).le.trans ((re_le_norm (g x)).trans (hg_le x)),
    by rw [hre u, hgu, RCLike.ofReal_re]⟩

end SeminormHahnBanach

/-! ## Trace duality for endomorphisms of a finite-dimensional inner product space -/

section TraceDuality

open ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [FiniteDimensional 𝕜 E] [CompleteSpace E]

/-- The trace of the adjoint is the conjugate of the trace:
`tr G* = conj (tr G)`. (Compute both traces in an orthonormal basis.) -/
lemma ContinuousLinearMap.trace_adjoint (G : E →L[𝕜] E) :
    LinearMap.trace 𝕜 E ((ContinuousLinearMap.adjoint G : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = starRingEnd 𝕜 (LinearMap.trace 𝕜 E (G : E →ₗ[𝕜] E)) := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis 𝕜 E),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis 𝕜 E), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

/-- **Trace duality.** Every `𝕜`-linear functional `f` on the continuous endomorphisms of
a finite-dimensional inner product space is of the form `A ↦ tr (A ∘ G)` for some
endomorphism `G`.

The pairing `(G, A) ↦ tr (A ∘ G)` is nondegenerate — testing against `A = G*` gives
`tr (G* ∘ G) = ∑ᵢ ‖G eᵢ‖² ` — so `G ↦ tr (· ∘ G)` is an injective linear map into the
dual, hence surjective by equality of dimensions. -/
theorem ContinuousLinearMap.exists_trace_repr (f : (E →L[𝕜] E) →ₗ[𝕜] 𝕜) :
    ∃ G : E →L[𝕜] E, ∀ A : E →L[𝕜] E,
      f A = LinearMap.trace 𝕜 E ((A : E →ₗ[𝕜] E) ∘ₗ (G : E →ₗ[𝕜] E)) := by
  classical
  have : FiniteDimensional 𝕜 (E →L[𝕜] E) :=
    Module.Finite.equiv
      (LinearMap.toContinuousLinearMap : (E →ₗ[𝕜] E) ≃ₗ[𝕜] (E →L[𝕜] E))
  -- the pairing `G ↦ (A ↦ tr (A ∘ G))`, as a linear map into the dual
  set J : (E →L[𝕜] E) →ₗ[𝕜] Module.Dual 𝕜 (E →L[𝕜] E) :=
    { toFun := fun G =>
        { toFun := fun A => LinearMap.trace 𝕜 E ((A : E →ₗ[𝕜] E) ∘ₗ (G : E →ₗ[𝕜] E))
          map_add' := fun A B => by
            simp only [ContinuousLinearMap.toLinearMap_add, LinearMap.add_comp, map_add]
          map_smul' := fun c A => by
            simp only [ContinuousLinearMap.toLinearMap_smul, LinearMap.smul_comp, map_smul,
              RingHom.id_apply] }
      map_add' := fun G₁ G₂ => by
        ext A
        simp only [ContinuousLinearMap.toLinearMap_add, LinearMap.comp_add, map_add,
          LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
      map_smul' := fun c G => by
        ext A
        simp only [ContinuousLinearMap.toLinearMap_smul, LinearMap.comp_smul, map_smul,
          LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply] } with hJ
  -- injectivity: test against the adjoint
  have hJinj : Function.Injective J := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro G hG
    have h0 : LinearMap.trace 𝕜 E
        (((ContinuousLinearMap.adjoint G : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ (G : E →ₗ[𝕜] E))
          = 0 := by
      have h := DFunLike.congr_fun hG (ContinuousLinearMap.adjoint G)
      simpa [hJ] using h
    rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis 𝕜 E)] at h0
    have hterm : ∀ i, ⟪stdOrthonormalBasis 𝕜 E i,
        ((((ContinuousLinearMap.adjoint G : E →L[𝕜] E) : E →ₗ[𝕜] E)
          ∘ₗ (G : E →ₗ[𝕜] E)) (stdOrthonormalBasis 𝕜 E i))⟫_𝕜
        = ((‖G (stdOrthonormalBasis 𝕜 E i)‖ : 𝕜) ^ 2) := fun i => by
      rw [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
    rw [Finset.sum_congr rfl fun i _ => hterm i] at h0
    -- a sum of squares of norms vanishes, so `G` kills an orthonormal basis
    have hreal : ∑ i, ‖G (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 = 0 := by
      have h1 : ((∑ i, ‖G (stdOrthonormalBasis 𝕜 E i)‖ ^ 2 : ℝ) : 𝕜) = 0 := by
        push_cast
        exact h0
      exact_mod_cast h1
    have hzero : ∀ i, G (stdOrthonormalBasis 𝕜 E i) = 0 := by
      intro i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp hreal i
        (Finset.mem_univ i)
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hi)
    apply ContinuousLinearMap.coe_injective
    apply Module.Basis.ext (stdOrthonormalBasis 𝕜 E).toBasis
    intro i
    simp [hzero i]
  -- surjectivity by dimension count
  have hJsurj : Function.Surjective J := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [LinearMap.finrank_range_of_inj hJinj, Subspace.dual_finrank_eq]
  obtain ⟨G, hG⟩ := hJsurj f
  exact ⟨G, fun A => (DFunLike.congr_fun hG A).symm⟩

end TraceDuality

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
