/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.SNumbers.BasicResults.Determinant
public import LeanPool.SNumbers.BasicResults.JohnAux
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact

/-!
# John's ellipsoid — the maximal-volume position

This is the first step towards the Kadets–Snobar and Garling–Gordon projection
theorems (`BasicResults/KadetsSnobar.lean`, `BasicResults/GarlingGordon.lean`),
whose sharp `‖P‖ ≤ √n` bounds rest on John's ellipsoid theorem (absent from
Mathlib). Everything is done over an arbitrary `RCLike` field `𝕜` (so both the
real and complex cases are covered at once).

We model an ellipsoid inside a symmetric convex body as the image `T (B₂)` of the
Euclidean unit ball under a continuous linear map `T : 𝕜^k →L 𝕜^k`; its volume is
proportional to `‖det T‖`. The body is described by a norm, given here as a
`Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))` `p` that is equivalent to the Euclidean
norm (`c‖x‖ ≤ p x ≤ C‖x‖`, `c > 0`). The ellipsoid `T (B₂)` lies in the body
`{p ≤ 1}` exactly when `T` is *feasible*: `p (T u) ≤ ‖u‖` for all `u`.

## Main results

* `John.exists_maxVolume` — among the feasible operators there is one, `T₀`, of
  maximal `‖det‖`; it is invertible (`det ≠ 0`). This is the maximal-volume
  inscribed ellipsoid.
* `John.exists_johnPosition` — the John position along any continuous linear
  equivalence `L : 𝕜^k ≃L W`: an equivalence `M` and a body seminorm `q` with
  `q u ≤ ‖u‖`, `‖det S‖ ≤ 1` for every feasible `S`, and `‖M z‖ = q z`. The
  common core of both projection theorems below.
* `John.john_decomposition` — the **decomposition of identity** in John position,
  `∑ᵢ cᵢ uᵢ⊗uᵢ = id` over contact points with `∑ᵢ cᵢ = dim`. By the classical
  variational argument: Hahn–Banach separation of `k⁻¹ • id` from the
  compact convex hull of the contact projections, trace duality to produce a
  self-adjoint trace-zero improving direction, the first-order perturbation
  `(1-ρ)⁻¹ • (id + tH)` to contradict maximality, and Carathéodory to extract the
  finite combination. The general-purpose ingredients (compactness of convex hulls,
  seminorm Hahn–Banach, trace duality, the product bound `∏(1+aᵢ) ≥ 1-2∑aᵢ²`) live
  in `BasicResults/JohnAux.lean`.
* `John.exists_projection` — **Kadets–Snobar**: every finite-dimensional subspace
  of a normed `𝕜`-space is the range of a projection `P` with `‖P‖ ≤ √(dim)`. Its
  analytic core is the weighted Cauchy–Schwarz bound `John.norm_sum_weight_smul_le`.
* `John.exists_projection_ker` — **Garling–Gordon** (ε-form), dual to
  Kadets–Snobar: every closed subspace `M` with finite-dimensional quotient is the
  kernel of a projection `P` with `‖P‖ ≤ √(codim M) + ε`, for every `ε > 0`. Built
  on the dual `(X ⧸ M)*`, representing contact points via `Φ.flip` (avoiding the
  topological double dual).
-/

@[expose] public section

universe u

open scoped InnerProductSpace ComplexConjugate

open RCLike (re)

namespace John

variable {𝕜 : Type u} [RCLike 𝕜] {k : ℕ}

/-- An operator `T : 𝕜^k →L 𝕜^k` is *feasible* for the body seminorm `p` when the
image `T (B₂)` of the Euclidean unit ball lies in `{p ≤ 1}`, i.e. `p (T u) ≤ ‖u‖`
for every `u`. -/
def Feasible (p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))) :
    Set (EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :=
  {T | ∀ u, p (T u) ≤ ‖u‖}

/-- The feasible set is closed: for each `u`, `T ↦ p (T u)` is continuous. -/
lemma isClosed_feasible (p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    (hp : Continuous p) : IsClosed (Feasible p) := by
  rw [Feasible, Set.ofPred_forall]
  refine isClosed_iInter fun u => isClosed_le ?_ continuous_const
  exact hp.comp (continuous_id.clm_apply continuous_const)

/-- The feasible set is bounded: `c‖x‖ ≤ p x` forces `‖T‖ ≤ 1/c`. -/
lemma feasible_subset_closedBall (p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    {c : ℝ} (hc : 0 < c) (hlo : ∀ x, c * ‖x‖ ≤ p x) :
    Feasible p ⊆ Metric.closedBall 0 (1 / c) := by
  intro T hT
  simp only [Metric.mem_closedBall, dist_zero_right]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  have h1 : c * ‖T u‖ ≤ ‖u‖ := le_trans (hlo (T u)) (hT u)
  have h2 : ‖T u‖ ≤ ‖u‖ / c := by rw [le_div_iff₀ hc]; linarith
  exact h2.trans_eq (by rw [one_div, inv_mul_eq_div])

/-- **Maximal-volume inscribed ellipsoid.** For a body seminorm `p` equivalent to
the Euclidean norm (`c‖x‖ ≤ p x ≤ C‖x‖`, `c > 0`), among the feasible operators
there is one of maximal `‖det‖`, and it is invertible. -/
theorem exists_maxVolume (p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    (hp : Continuous p) {c : ℝ} (hc : 0 < c) (hlo : ∀ x, c * ‖x‖ ≤ p x)
    {C : ℝ} (hup : ∀ x, p x ≤ C * ‖x‖) :
    ∃ T ∈ Feasible p, T.det ≠ 0 ∧ ∀ S ∈ Feasible p, ‖S.det‖ ≤ ‖T.det‖ := by
  classical
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hup' : ∀ x, p x ≤ C' * ‖x‖ := fun x =>
    (hup x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  -- A small multiple of the identity is feasible: gives nonemptiness.
  set δ : ℝ := 1 / (C' + 1) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ * C' ≤ 1 := by
    rw [hδ, div_mul_eq_mul_div, div_le_one (by positivity)]; linarith
  set T₀ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    (δ : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)) with hT₀
  have hT₀feas : T₀ ∈ Feasible p := by
    intro u
    have hpu : p (T₀ u) = δ * p u := by
      rw [hT₀]
      simp only [smul_apply, ContinuousLinearMap.id_apply,
        map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos hδpos]
    rw [hpu]
    calc δ * p u ≤ δ * (C' * ‖u‖) :=
          mul_le_mul_of_nonneg_left (hup' u) hδpos.le
      _ = (δ * C') * ‖u‖ := by ring
      _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hδ1 (norm_nonneg _)
      _ = ‖u‖ := one_mul _
  -- The determinant is continuous and the feasible set is compact.
  have : ProperSpace (EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :=
    FiniteDimensional.proper_rclike 𝕜 _
  have hcompact : IsCompact (Feasible p) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_feasible p hp)
      (Metric.isBounded_closedBall.subset (feasible_subset_closedBall p hc hlo))
  obtain ⟨T, hTfeas, hTmax⟩ :=
    hcompact.exists_isMaxOn ⟨T₀, hT₀feas⟩
      (continuous_norm.comp ContinuousLinearMap.continuous_det).continuousOn
  refine ⟨T, hTfeas, ?_, fun S hS => hTmax hS⟩
  -- `det T₀ = δ ^ (finrank) ≠ 0`, and `‖det T‖ ≥ ‖det T₀‖ > 0`, so `det T ≠ 0`.
  have hcoe : (T₀ : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))
      = (δ : 𝕜) • LinearMap.id := by rw [hT₀]; ext x; simp
  have hval : T₀.det = (δ : 𝕜) ^ Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) := by
    simp only [ContinuousLinearMap.det, hcoe, LinearMap.det_smul, LinearMap.det_id, mul_one]
  have hdet₀ne : T₀.det ≠ 0 := by
    rw [hval]; exact pow_ne_zero _ (by exact_mod_cast ne_of_gt hδpos)
  have hpos : 0 < ‖T.det‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hdet₀ne) (hTmax hT₀feas)
  exact fun h => by simp [h] at hpos

/-- **John position along an equivalence.** Given a continuous linear equivalence
`L : 𝕜^k ≃L W` onto a normed space `W` (with `0 < k`), there are an equivalence
`M : 𝕜^k ≃L W` and a body seminorm `q` in *John position*: `q` is continuous, the
identity is feasible for `q` (`q u ≤ ‖u‖`), every feasible operator has `‖det‖ ≤ 1`,
and `q` is the pullback of the norm of `W` along `M` (`‖M z‖ = q z`).

Mathematically: pull the norm of `W` back to a body seminorm `p = ‖L ·‖` on `𝕜^k`
(equivalent to the Euclidean norm since `L` is an equivalence and `k > 0`), take a
maximal-volume feasible operator `T₀` (`exists_maxVolume`), and set `q = p ∘ T₀`,
`M = L ∘ T₀`. This is the common core of the Kadets–Snobar and Garling–Gordon
projection theorems below. -/
theorem exists_johnPosition {W : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
    (hk : 0 < k) (L : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] W) :
    ∃ (M : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] W)
      (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))),
      Continuous q ∧ (∀ u, q u ≤ ‖u‖) ∧ (∀ S ∈ Feasible q, ‖S.det‖ ≤ 1) ∧
      ∀ z, ‖M z‖ = q z := by
  classical
  -- the body seminorm `p x = ‖L x‖`, equivalent to the Euclidean norm
  set p : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)) :=
    (normSeminorm 𝕜 W).comp (L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] W).toLinearMap with hpdef
  have hp_apply : ∀ x, p x = ‖L x‖ := fun x => by
    simp only [hpdef, Seminorm.comp_apply, coe_normSeminorm, ContinuousLinearMap.coe_coe,
      ContinuousLinearEquiv.coe_coe]
  have hpc : Continuous p := by
    refine (continuous_norm.comp L.continuous).congr fun x => ?_
    exact (hp_apply x).symm
  -- upper bound `p x ≤ ‖L‖ ‖x‖`
  have hup : ∀ x, p x ≤ ‖(L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] W)‖ * ‖x‖ := fun x => by
    rw [hp_apply]
    exact (L : EuclideanSpace 𝕜 (Fin k) →L[𝕜] W).le_opNorm x
  -- lower bound `‖L.symm‖⁻¹ ‖x‖ ≤ p x`; the constant is positive since `0 < k`
  set D : ℝ := ‖(L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k))‖ with hD
  have hDpos : 0 < D := by
    have hne : (L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k)) ≠ 0 := by
      intro hzero
      have he1 : ‖(EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : 𝕜))‖ = 1 := by
        rw [PiLp.norm_single, norm_one]
      have hcontra : (EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : 𝕜)) = 0 := by
        have h2 : (L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k))
            (L (EuclideanSpace.single (⟨0, hk⟩ : Fin k) (1 : 𝕜))) = 0 := by
          rw [hzero]; rfl
        rwa [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply] at h2
      rw [hcontra, norm_zero] at he1
      exact one_ne_zero he1.symm
    rw [hD]
    rcases eq_or_lt_of_le (norm_nonneg (L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k))) with h | h
    · exact absurd ((ContinuousLinearMap.opNorm_zero_iff _).mp h.symm) hne
    · exact h
  have hlo : ∀ x, D⁻¹ * ‖x‖ ≤ p x := fun x => by
    have hbound : ‖x‖ ≤ D * p x := by
      rw [hp_apply]
      have e : ‖x‖ = ‖(L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (L x)‖ := by
        rw [ContinuousLinearEquiv.coe_coe, L.symm_apply_apply]
      rw [e]
      exact (L.symm : W →L[𝕜] EuclideanSpace 𝕜 (Fin k)).le_opNorm (L x)
    have h2 := mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.mpr hDpos))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hDpos), one_mul] at h2
  -- the maximal-volume ellipsoid `T₀` and the John-position seminorm `q = p ∘ T₀`
  obtain ⟨T₀, hT₀feas, hT₀det, hT₀max⟩ :=
    exists_maxVolume p hpc (inv_pos.mpr hDpos) hlo hup
  set q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)) := p.comp T₀.toLinearMap with hqdef
  have hq1 : ∀ u, q u ≤ ‖u‖ := fun u => by
    rw [hqdef, Seminorm.comp_apply]; exact hT₀feas u
  have hqc : Continuous q := by
    rw [hqdef]; exact hpc.comp T₀.continuous
  have hqmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1 := fun S hS => by
    have hTS : T₀.comp S ∈ Feasible p := fun u => by
      have h := hS u
      rw [hqdef, Seminorm.comp_apply, ContinuousLinearMap.coe_coe] at h
      simpa [ContinuousLinearMap.comp_apply] using h
    have hdc : (T₀.comp S).det = T₀.det * S.det := by
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
    have hle := hT₀max (T₀.comp S) hTS
    rw [hdc, norm_mul] at hle
    exact (mul_le_iff_le_one_right (norm_pos_iff.mpr hT₀det)).mp hle
  -- the composite equivalence `M = L ∘ T₀`
  refine ⟨(T₀.toContinuousLinearEquivOfDetNeZero hT₀det).trans L, q, hqc, hq1, hqmax,
    fun z => ?_⟩
  rw [ContinuousLinearEquiv.trans_apply,
    ContinuousLinearMap.toContinuousLinearEquivOfDetNeZero_apply, hqdef,
    Seminorm.comp_apply, ContinuousLinearMap.coe_coe, hp_apply]

/-- The **contact set** of a body seminorm `q`: unit vectors `u` whose associated
linear functional `x ↦ re ⟪x, u⟫` is dominated by `q`. These are the points where
the Euclidean unit sphere touches the boundary `{q = 1}` with a shared supporting
hyperplane; the John decomposition of identity is supported on this set. -/
def Contact (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))) :
    Set (EuclideanSpace 𝕜 (Fin k)) :=
  {u | ‖u‖ = 1 ∧ ∀ x, re ⟪x, u⟫_𝕜 ≤ q x}

/-- The contact set is compact: it is a closed subset of the (compact) unit
sphere. -/
lemma isCompact_contact (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))) :
    IsCompact (Contact q) := by
  have hsub : Contact q ⊆ Metric.sphere 0 1 := fun u hu => by
    simpa using hu.1
  have hcl : IsClosed (Contact q) := by
    have heq : Contact q =
        {u : EuclideanSpace 𝕜 (Fin k) | ‖u‖ = 1} ∩ ⋂ x, {u | re ⟪x, u⟫_𝕜 ≤ q x} := by
      ext u
      simp only [Contact, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [heq]
    refine (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_iInter fun x => isClosed_le ?_ continuous_const)
    exact RCLike.continuous_re.comp (continuous_const.inner continuous_id)
  exact (isCompact_sphere 0 1).of_isClosed_subset hcl hsub

/-- The self-adjoint **rank-one operator** `u ⊗ u : x ↦ ⟪u, x⟫ • u`. The John
decomposition of identity expresses `id` as a positive combination of these over
contact points. -/
noncomputable def rankOneSA (u : EuclideanSpace 𝕜 (Fin k)) :
    EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
  (innerSL 𝕜 u).smulRight u

@[simp] lemma rankOneSA_apply (u x : EuclideanSpace 𝕜 (Fin k)) :
    rankOneSA u x = ⟪u, x⟫_𝕜 • u := rfl

/-- **Contact support.** A contact point `u` has `‖⟪x, u⟫‖ ≤ q x` for all `x`:
choosing a unit phase `a` with `re ⟪a • x, u⟫ = ‖⟪x, u⟫‖`, the contact bound and
`𝕜`-homogeneity of `q` give the claim. -/
lemma norm_inner_le_of_contact {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    {u : EuclideanSpace 𝕜 (Fin k)} (hu : u ∈ Contact q) (x : EuclideanSpace 𝕜 (Fin k)) :
    ‖⟪x, u⟫_𝕜‖ ≤ q x := by
  rcases eq_or_ne (⟪x, u⟫_𝕜) 0 with h | h
  · rw [h, norm_zero]; exact apply_nonneg q x
  · set c := ⟪x, u⟫_𝕜 with hcdef
    have hcnorm : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr h
    have hkey : re ⟪(c / (‖c‖ : 𝕜)) • x, u⟫_𝕜 = ‖c‖ := by
      rw [inner_smul_left, map_div₀, RCLike.conj_ofReal, div_mul_eq_mul_div,
        RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_div, RCLike.ofReal_re,
        pow_two, mul_div_assoc, div_self hcnorm, mul_one]
    have hle := hu.2 ((c / (‖c‖ : 𝕜)) • x)
    rw [hkey, map_smul_eq_mul, norm_div, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg c), div_self hcnorm, one_mul] at hle
    exact hle

/-- **Quadratic form of a decomposition of identity.** If
`∑ᵢ ((cᵢ:𝕜) · ⟪uᵢ, x⟫) • uᵢ = x` for all `x`, then `∑ᵢ cᵢ · ‖⟪uᵢ, z⟫‖² = ‖z‖²`. -/
lemma sum_weight_inner_sq {N : ℕ} (c : Fin N → ℝ) (u : Fin N → EuclideanSpace 𝕜 (Fin k))
    (hdec : ∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x) (z : EuclideanSpace 𝕜 (Fin k)) :
    ∑ i, c i * ‖⟪u i, z⟫_𝕜‖ ^ 2 = ‖z‖ ^ 2 := by
  have h : re ⟪(∑ i, ((c i : 𝕜) * ⟪u i, z⟫_𝕜) • u i), z⟫_𝕜 = re ⟪z, z⟫_𝕜 := by
    rw [hdec z]
  rw [sum_inner, map_sum, inner_self_eq_norm_sq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc, RCLike.conj_mul,
    ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, RCLike.ofReal_re]

/-- **Weighted Cauchy–Schwarz.** For nonnegative weights `cᵢ`,
`∑ᵢ cᵢ tᵢ ≤ √(∑ᵢ cᵢ) · √(∑ᵢ cᵢ tᵢ²)`.

Cauchy–Schwarz applied to the vectors `(√cᵢ)` and `(√cᵢ · tᵢ)`. Paired with a
decomposition of identity (where `∑ᵢ cᵢ` is the dimension) this is what turns a
quadratic bound into the linear bound needed for a projection norm. -/
lemma sum_weight_mul_le_sqrt {N : ℕ} (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i) (t : Fin N → ℝ) :
    ∑ i, c i * t i ≤ Real.sqrt (∑ i, c i) * Real.sqrt (∑ i, c i * t i ^ 2) := by
  have hcsum : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  have hquad : 0 ≤ ∑ i, c i * t i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  -- Cauchy–Schwarz for the two vectors `√cᵢ` and `√cᵢ · tᵢ`.
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (c i)) (fun i => Real.sqrt (c i) * t i)
  have e1 : ∀ i, Real.sqrt (c i) * (Real.sqrt (c i) * t i) = c i * t i := fun i => by
    rw [← mul_assoc, Real.mul_self_sqrt (hc i)]
  have e2 : ∀ i, (Real.sqrt (c i)) ^ 2 = c i := fun i => Real.sq_sqrt (hc i)
  have e3 : ∀ i, (Real.sqrt (c i) * t i) ^ 2 = c i * t i ^ 2 := fun i => by
    rw [mul_pow, Real.sq_sqrt (hc i)]
  simp only [e1, e2, e3] at h
  -- `(∑ cᵢtᵢ)² ≤ (∑ cᵢ)(∑ cᵢtᵢ²)`, so the claim follows by taking square roots.
  calc ∑ i, c i * t i ≤ |∑ i, c i * t i| := le_abs_self _
    _ = Real.sqrt ((∑ i, c i * t i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, c i) * ∑ i, c i * t i ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt (∑ i, c i) * Real.sqrt (∑ i, c i * t i ^ 2) := Real.sqrt_mul hcsum _

/-! ### Ingredients for the John decomposition of identity

The proof of `john_decomposition` below is the classical variational argument
(F. John; K. Ball, *An elementary introduction to modern convex geometry*):

1. `mem_contact_of_apply_eq_one` — every unit vector where the body touches the
   Euclidean sphere is a contact point (Hahn–Banach for the seminorm `q`).
2. `exists_selfAdjoint_of_not_mem_convexHull` — if `k⁻¹ • id` did *not* lie in the
   convex hull of the contact projections `uᵢ ⊗ uᵢ`, geometric Hahn–Banach separation
   plus trace duality would produce a self-adjoint, trace-zero `H` with
   `re ⟪u, H u⟫ ≤ -δ < 0` at every contact point.
3. `no_neg_direction_of_maxVolume` — no such `H` exists: for small `t > 0` the operator
   `(1 - ρ)⁻¹ • (id + t H)` would be feasible with `‖det‖ > 1`, because the feasibility
   slack grows linearly in `t` while (trace being zero) the determinant only loses
   `O(t²)` — contradicting the John-position maximality. Its four ingredients are the
   compactness gap `exists_gap_of_lt_one_on_compact`, the norm estimate
   `norm_add_smul_le_of_inner_le`, the rescaling step
   `smul_mem_feasible_of_le_on_sphere`, and the determinant bound
   `one_sub_le_norm_det_one_add_smul`.
4. Carathéodory (`mem_convexHull_iff_exists_fintype`) turns hull membership into the
   finite positive combination.
-/

/-- **Every touching point is a contact point.** If `q ≤ ‖·‖` and `u` is a unit vector
with `q u = 1`, then `u ∈ Contact q`. The supporting functional of `{q ≤ 1}` at `u`
produced by seminorm-Hahn–Banach (`Seminorm.exists_inner_le_of_apply`) is represented by
a vector `v` with `re ⟪u, v⟫ = 1` and `‖v‖ ≤ 1`; equality in Cauchy–Schwarz forces
`v = u`, so `u` itself supports the body. -/
lemma mem_contact_of_apply_eq_one {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    (hq1 : ∀ x, q x ≤ ‖x‖) {u : EuclideanSpace 𝕜 (Fin k)} (hu : ‖u‖ = 1) (hqu : q u = 1) :
    u ∈ Contact q := by
  obtain ⟨v, hvle, hvu⟩ := q.exists_inner_le_of_apply u
  rw [hqu] at hvu
  have hv1 : ‖v‖ ≤ 1 := by
    have h := (hvle v).trans (hq1 v)
    rw [inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1)]
  have hveq : v = u := by
    have hsub : ‖u - v‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq (𝕜 := 𝕜), hu, hvu]
      nlinarith [hv1, norm_nonneg v]
    have h0 : ‖u - v‖ = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hsub (sq_nonneg _))
    exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm
  refine ⟨hu, fun x => ?_⟩
  have h := hvle x
  rwa [hveq] at h

/-- The map `u ↦ u ⊗ u` sending a vector to its rank-one projection is continuous. -/
lemma continuous_rankOneSA :
    Continuous fun u : EuclideanSpace 𝕜 (Fin k) => rankOneSA (𝕜 := 𝕜) u := by
  change Continuous fun u : EuclideanSpace 𝕜 (Fin k) => (innerSL 𝕜 u).smulRight u
  have h : Continuous fun u : EuclideanSpace 𝕜 (Fin k) =>
      ContinuousLinearMap.smulRightL 𝕜 (EuclideanSpace 𝕜 (Fin k))
        (EuclideanSpace 𝕜 (Fin k)) (innerSL 𝕜 u) :=
    (ContinuousLinearMap.smulRightL 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (EuclideanSpace 𝕜 (Fin k))).continuous.comp (innerSL 𝕜).continuous
  simpa using h.clm_apply continuous_id

/-- The trace of `(u ⊗ u) ∘ G` is the quadratic-form value `⟪u, G u⟫`. -/
lemma trace_rankOneSA_comp (u : EuclideanSpace 𝕜 (Fin k))
    (G : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :
    LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      ((rankOneSA u : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) ∘ₗ
        (G : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))) = ⟪u, G u⟫_𝕜 := by
  have hcomp : (rankOneSA u : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) ∘ₗ
      (G : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))
      = LinearMap.smulRight
          (((innerSL 𝕜 u).comp G : EuclideanSpace 𝕜 (Fin k) →L[𝕜] 𝕜) :
            EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] 𝕜) u := by
    ext x
    simp [rankOneSA_apply]
  rw [hcomp, LinearMap.trace_smulRight]
  simp

/-- **The separation step of John's theorem.** If, in John position, `k⁻¹ • id` is not a
convex combination of contact projections `u ⊗ u`, then some self-adjoint trace-zero
direction `H` improves all contact points at once: `re ⟪u, H u⟫ ≤ -δ < 0` on `Contact q`.

Proof: the contact set is compact, so the set of its rank-one projections is compact and
(in finite dimensions) its convex hull is compact, hence closed; geometric Hahn–Banach
(`RCLike.geometric_hahn_banach_closed_point`) separates `k⁻¹ • id` from it. Trace duality
(`ContinuousLinearMap.exists_trace_repr`) writes the separating functional as
`A ↦ tr (A ∘ G)`; on rank-one projections this evaluates to `re ⟪u, G u⟫`
(`trace_rankOneSA_comp`). Passing to the self-adjoint part of `G` and subtracting the
right multiple of the identity makes the trace zero without changing the inequality. -/
lemma exists_selfAdjoint_of_not_mem_convexHull (hk : 0 < k)
    {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    (hmem : ((k : ℝ)⁻¹ • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))
      ∉ convexHull ℝ (rankOneSA '' Contact q)) :
    ∃ (H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) (δ : ℝ), 0 < δ ∧
      IsSelfAdjoint H ∧
      LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
        (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0 ∧
      ∀ u ∈ Contact q, re ⟪u, H u⟫_𝕜 ≤ -δ := by
  classical
  have : FiniteDimensional ℝ
      (EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)) :=
    Module.Finite.trans 𝕜 (EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k))
  -- the convex hull of the contact projections is compact, hence closed
  have hcompact : IsCompact (convexHull ℝ (rankOneSA '' Contact q)) :=
    ((isCompact_contact q).image continuous_rankOneSA).convexHull
  -- separate the point from the closed convex hull
  obtain ⟨f, β, hfs, hfx⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
    (convex_convexHull ℝ _) hcompact.isClosed hmem
  -- represent the separating functional by trace duality
  obtain ⟨G, hG⟩ := ContinuousLinearMap.exists_trace_repr (𝕜 := 𝕜) f.toLinearMap
  have hfu : ∀ u : EuclideanSpace 𝕜 (Fin k), f (rankOneSA u) = ⟪u, G u⟫_𝕜 := fun u => by
    have h := hG (rankOneSA u)
    rwa [trace_rankOneSA_comp] at h
  have hfid : f (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))
      = LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
          (G : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) := by
    have h := hG (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    rwa [ContinuousLinearMap.coe_id, LinearMap.id_comp] at h
  -- the self-adjoint part of `G`, normalized to trace zero
  set H₀ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    ((((1 : ℝ) / 2 : ℝ)) : 𝕜) • (G + ContinuousLinearMap.adjoint G) with hH₀
  set τ : ℝ := re (LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
    (G : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))) / k with hτ
  set H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    H₀ - ((τ : ℝ) : 𝕜) • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)) with hH
  -- pointwise form of `H`
  have hHapp : ∀ w, H w = ((((1 : ℝ) / 2 : ℝ)) : 𝕜) • (G w + ContinuousLinearMap.adjoint G w)
      - ((τ : ℝ) : 𝕜) • w := fun w => by
    simp only [hH, hH₀, sub_apply, smul_apply,
      add_apply, ContinuousLinearMap.id_apply]
  -- `H` is self-adjoint: its quadratic form is symmetric
  have hHsa : IsSelfAdjoint H := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    change ⟪H x, y⟫_𝕜 = ⟪x, H y⟫_𝕜
    rw [hHapp x, hHapp y]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_add_left, inner_add_right, RCLike.conj_ofReal,
      ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
    ring
  -- traces
  have htrH₀ : LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (H₀ : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))
      = ((re (LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
          (G : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))) : ℝ) : 𝕜) := by
    rw [hH₀, ContinuousLinearMap.toLinearMap_smul, ContinuousLinearMap.toLinearMap_add,
      map_smul, map_add, ContinuousLinearMap.trace_adjoint, RCLike.add_conj, smul_eq_mul]
    push_cast
    ring
  have htrH : LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0 := by
    have hkK : ((k : ℕ) : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    rw [hH, ContinuousLinearMap.toLinearMap_sub, map_sub, htrH₀,
        ContinuousLinearMap.toLinearMap_smul,
      map_smul, ContinuousLinearMap.coe_id, LinearMap.trace_id, finrank_euclideanSpace_fin,
      hτ, smul_eq_mul]
    push_cast
    field_simp
    ring
  -- the gap
  set δ : ℝ := re (f ((k : ℝ)⁻¹ • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))) - β
    with hδdef
  have hδpos : 0 < δ := sub_pos.mpr hfx
  -- the quadratic form of the self-adjoint part is that of `G`
  have hquad : ∀ w : EuclideanSpace 𝕜 (Fin k),
      re ⟪w, ((((1 : ℝ) / 2 : ℝ)) : 𝕜) • (G w + ContinuousLinearMap.adjoint G w)⟫_𝕜
        = re ⟪w, G w⟫_𝕜 := fun w => by
    have h2 : re ⟪w, ContinuousLinearMap.adjoint G w⟫_𝕜 = re ⟪w, G w⟫_𝕜 := by
      rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm w (G w), RCLike.conj_re]
    rw [inner_smul_right, RCLike.re_ofReal_mul, inner_add_right, map_add, h2]
    ring
  have hτre : re (f ((k : ℝ)⁻¹ • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))) = τ := by
    rw [ContinuousLinearMap.map_smul_of_tower, RCLike.smul_re, hfid, hτ]
    ring
  refine ⟨H, δ, hδpos, hHsa, htrH, fun u hu => ?_⟩
  -- the contact bound
  have h1 : re (f (rankOneSA u)) < β :=
    hfs _ (subset_convexHull ℝ _ (Set.mem_image_of_mem _ hu))
  rw [hfu u] at h1
  have h2 : re ⟪u, H u⟫_𝕜 = re ⟪u, G u⟫_𝕜 - τ := by
    rw [hHapp u, inner_sub_right, map_sub, hquad u, inner_smul_right,
      RCLike.re_ofReal_mul, inner_self_eq_norm_sq, hu.1]
    ring
  rw [h2, hδdef, hτre]
  linarith

/-- **Uniform gap on a compact set.** If a continuous seminorm satisfies `q < 1` on a
compact set `C`, it stays below `1 - η` on `C` for a uniform `0 < η ≤ 1` (extreme value
theorem; `η ≤ 1` because `q ≥ 0`). -/
lemma exists_gap_of_lt_one_on_compact {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    (hqc : Continuous q) {C : Set (EuclideanSpace 𝕜 (Fin k))} (hC : IsCompact C)
    (hlt : ∀ u ∈ C, q u < 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ u ∈ C, q u ≤ 1 - η := by
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · exact ⟨1 / 2, by norm_num, by norm_num,
      fun u hu => absurd (hCe ▸ hu) (Set.notMem_empty u)⟩
  · obtain ⟨u₀, hu₀C, hu₀max⟩ := hC.exists_isMaxOn hCne hqc.continuousOn
    refine ⟨1 - q u₀, by linarith [hlt u₀ hu₀C], by linarith [apply_nonneg q u₀], ?_⟩
    intro u hu
    linarith [(isMaxOn_iff.mp hu₀max) u hu]

/-- **Rescaling to feasibility.** If `q (T u) ≤ s` for every unit vector `u` (with
`s > 0`), then `s⁻¹ • T` is feasible for `q`: by homogeneity, `q (T x) ≤ s ‖x‖` for
every `x`. Part of the John's-ellipsoid perturbation argument. -/
lemma smul_mem_feasible_of_le_on_sphere {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))}
    {T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)} {s : ℝ} (hs : 0 < s)
    (hT : ∀ u, ‖u‖ = 1 → q (T u) ≤ s) : ((s⁻¹ : ℝ) : 𝕜) • T ∈ Feasible q := by
  intro x
  rw [smul_apply, map_smul_eq_mul, RCLike.norm_ofReal,
    abs_of_pos (inv_pos.mpr hs)]
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    set u : EuclideanSpace 𝕜 (Fin k) := ((‖x‖⁻¹ : ℝ) : 𝕜) • x with hudef
    have hun : ‖u‖ = 1 := by
      rw [hudef, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hxn),
        inv_mul_cancel₀ hxn.ne']
    have hxu : x = ((‖x‖ : ℝ) : 𝕜) • u := by
      rw [hudef, smul_smul, ← RCLike.ofReal_mul, mul_inv_cancel₀ hxn.ne',
        RCLike.ofReal_one, one_smul]
    have hTx : q (T x) = ‖x‖ * q (T u) := by
      conv_lhs => rw [hxu]
      rw [map_smul, map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos hxn]
    rw [hTx]
    calc s⁻¹ * (‖x‖ * q (T u)) ≤ s⁻¹ * (‖x‖ * s) := by
          have h3 : ‖x‖ * q (T u) ≤ ‖x‖ * s :=
            mul_le_mul_of_nonneg_left (hT u hun) hxn.le
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = s⁻¹ * s * ‖x‖ := by ring
      _ = ‖x‖ := by rw [inv_mul_cancel₀ hs.ne', one_mul]

/-- **Linear norm shrinking near the touching set.** If `re ⟪u, H u⟫ ≤ -(δ/2)` at a
unit vector `u`, then `‖u + t • H u‖ ≤ 1 - tδ/4` for `0 < t` with `t‖H‖² ≤ δ/2` and
`tδ ≤ 4`: expanding the square,
`‖u + tHu‖² ≤ 1 - tδ + t²‖H‖² ≤ 1 - tδ/2 ≤ (1 - tδ/4)²`.
This is the first-order feasibility gain of the John perturbation. -/
lemma norm_add_smul_le_of_inner_le
    {H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    {u : EuclideanSpace 𝕜 (Fin k)} (hu : ‖u‖ = 1) {t δ : ℝ} (ht0 : 0 < t)
    (h1 : t * ‖H‖ ^ 2 ≤ δ / 2) (h2 : t * δ ≤ 4)
    (hA : re ⟪u, H u⟫_𝕜 ≤ -(δ / 2)) :
    ‖u + ((t : ℝ) : 𝕜) • H u‖ ≤ 1 - t * δ / 4 := by
  have hHu : ‖H u‖ ≤ ‖H‖ := by simpa [hu] using H.le_opNorm u
  have hnorm : ‖u + ((t : ℝ) : 𝕜) • H u‖ ^ 2 ≤ 1 - t * δ / 2 := by
    rw [norm_add_sq (𝕜 := 𝕜), hu, inner_smul_right, norm_smul,
      RCLike.re_ofReal_mul, RCLike.norm_ofReal, abs_of_pos ht0]
    have e1 : t * re ⟪u, H u⟫_𝕜 ≤ t * (-(δ / 2)) := mul_le_mul_of_nonneg_left hA ht0.le
    have e2 : (t * ‖H u‖) ^ 2 ≤ (t * ‖H‖) ^ 2 := by
      have h3 : t * ‖H u‖ ≤ t * ‖H‖ := mul_le_mul_of_nonneg_left hHu ht0.le
      exact pow_le_pow_left₀ (by positivity) h3 2
    have e3 : (t * ‖H‖) ^ 2 ≤ t * (δ / 2) := by
      have h4 : (t * ‖H‖) ^ 2 = t * (t * ‖H‖ ^ 2) := by ring
      rw [h4]
      exact mul_le_mul_of_nonneg_left h1 ht0.le
    nlinarith [e1, e2, e3]
  have h3 : (0 : ℝ) ≤ 1 - t * δ / 4 := by linarith
  have h4 : ‖u + ((t : ℝ) : 𝕜) • H u‖ ^ 2 ≤ (1 - t * δ / 4) ^ 2 := by
    nlinarith [hnorm, sq_nonneg (t * δ)]
  exact le_of_sq_le_sq h4 h3

/-- **Second-order determinant bound for a trace-zero perturbation.** For a
self-adjoint `H` with `tr H = 0` and `0 < t` with `t‖H‖ ≤ 1/2`,
`‖det (id + t • H)‖ ≥ 1 - 2t²·(k·‖H‖²)`.

In an orthonormal eigenbasis (spectral theorem for symmetric operators),
`det (id + tH) = ∏ᵢ (1 + tλᵢ)` with real eigenvalues `λᵢ` satisfying
`∑ᵢ λᵢ = tr H = 0` and `|λᵢ| ≤ ‖H‖`; the Weierstrass-type bound
`one_sub_two_mul_sum_sq_le_prod_one_add` then gives
`∏(1+tλᵢ) ≥ 1 - 2t²∑λᵢ² ≥ 1 - 2t²k‖H‖²`. The trace-zero hypothesis is what makes
the determinant loss second order in `t`. -/
lemma one_sub_le_norm_det_one_add_smul
    {H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hHsa : IsSelfAdjoint H)
    (htr : LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0)
    {t : ℝ} (ht0 : 0 < t) (htH : t * ‖H‖ ≤ 1 / 2) :
    1 - 2 * (t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2))
      ≤ ‖(ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k))
          + ((t : ℝ) : 𝕜) • H).det‖ := by
  classical
  set T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)) + ((t : ℝ) : 𝕜) • H with hT
  -- eigenvalues of `H`
  have hsym : (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hHsa
  have hn : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = k := finrank_euclideanSpace_fin
  set lam : Fin k → ℝ := hsym.eigenvalues hn with hlam
  set b : OrthonormalBasis (Fin k) 𝕜 (EuclideanSpace 𝕜 (Fin k)) :=
    hsym.eigenvectorBasis hn with hb
  have hbnorm : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hbeig : ∀ i, H (b i) = ((lam i : ℝ) : 𝕜) • b i := fun i => by
    have h := hsym.apply_eigenvectorBasis hn i
    rw [hlam, hb]
    exact h
  have hsum0 : ∑ i, lam i = 0 := by
    have h := hsym.trace_eq_sum_eigenvalues hn
    rw [htr] at h
    exact_mod_cast h.symm
  have hlam_le : ∀ i, |lam i| ≤ ‖H‖ := fun i => by
    have h1 : ‖H (b i)‖ = |lam i| := by
      rw [hbeig i, norm_smul, RCLike.norm_ofReal, hbnorm i, mul_one]
    calc |lam i| = ‖H (b i)‖ := h1.symm
      _ ≤ ‖H‖ * ‖b i‖ := H.le_opNorm _
      _ = ‖H‖ := by rw [hbnorm i, mul_one]
  have hlam_half : ∀ i, |t * lam i| ≤ 1 / 2 := fun i => by
    rw [abs_mul, abs_of_pos ht0]
    calc t * |lam i| ≤ t * ‖H‖ := mul_le_mul_of_nonneg_left (hlam_le i) ht0.le
      _ ≤ 1 / 2 := htH
  have hfac_pos : ∀ i, 0 < 1 + t * lam i := fun i => by
    have h := abs_le.mp (hlam_half i)
    linarith [h.1]
  -- `det (id + tH) = ∏ (1 + tλᵢ)` in the eigenbasis
  have hTeig : ∀ i, T (b i) = ((1 + t * lam i : ℝ) : 𝕜) • b i := fun i => by
    rw [hT, add_apply, smul_apply,
      ContinuousLinearMap.id_apply, hbeig i, smul_smul, RCLike.ofReal_add,
      RCLike.ofReal_one, RCLike.ofReal_mul, add_smul, one_smul]
  have hdetT : T.det = ∏ i, ((1 + t * lam i : ℝ) : 𝕜) := by
    have h := LinearMap.det_eq_prod_of_apply_eq_smul b.toBasis
      (T : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k))
      (fun i => ((1 + t * lam i : ℝ) : 𝕜))
      (fun i => by simpa [OrthonormalBasis.coe_toBasis] using hTeig i)
    simpa [ContinuousLinearMap.det] using h
  -- the product bound, with `∑λᵢ² ≤ k‖H‖²`
  have hprod : 1 - 2 * (t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2)) ≤ ∏ i, (1 + t * lam i) := by
    have h := one_sub_two_mul_sum_sq_le_prod_one_add Finset.univ (fun i => t * lam i)
      (fun i _ => hlam_half i) (by rw [← Finset.mul_sum, hsum0, mul_zero])
    have hΛle : ∑ i, (t * lam i) ^ 2 ≤ t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2) := by
      calc ∑ i, (t * lam i) ^ 2 ≤ ∑ _i : Fin k, t ^ 2 * ‖H‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h2 : lam i ^ 2 ≤ ‖H‖ ^ 2 := by
              rw [← sq_abs (lam i)]
              exact pow_le_pow_left₀ (abs_nonneg _) (hlam_le i) 2
            nlinarith [sq_nonneg t]
        _ = t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            ring
    linarith [h]
  rw [hdetT, norm_prod]
  calc 1 - 2 * (t ^ 2 * ((k : ℝ) * ‖H‖ ^ 2)) ≤ ∏ i, (1 + t * lam i) := hprod
    _ = ∏ i, ‖((1 + t * lam i : ℝ) : 𝕜)‖ := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [RCLike.norm_ofReal, abs_of_pos (hfac_pos i)]

private lemma scaled_perturbation_det_gain {k : ℕ} (hk : 0 < k)
    {CH t δ ρ D : ℝ} (ht0 : 0 < t) (_hδ : 0 < δ) (hρ : ρ = t * δ / 4)
    (hρ0 : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (hbound4 : t * (20 * ((k : ℝ) * CH ^ 2 + 1)) ≤ δ)
    (hdetT : 1 - 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2)) ≤ D) :
    1 < (1 - ρ)⁻¹ ^ k * D := by
  have h1ρ : 0 < 1 - ρ := by linarith
  -- arithmetic: the first-order gain beats the second-order loss
  have hcge : 1 + ρ ≤ (1 - ρ)⁻¹ := by
    have h2 : (1 + ρ) * (1 - ρ) ≤ 1 := by nlinarith [sq_nonneg ρ]
    calc 1 + ρ = (1 + ρ) * (1 - ρ) * (1 - ρ)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ h1ρ.ne', mul_one]
      _ ≤ 1 * (1 - ρ)⁻¹ := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = (1 - ρ)⁻¹ := one_mul _
  have hc1 : 1 ≤ (1 - ρ)⁻¹ := by linarith
  have hck : 1 + ρ ≤ (1 - ρ)⁻¹ ^ k := le_trans hcge (le_self_pow₀ hc1 hk.ne')
  have hsmall : 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2)) * (1 + ρ) < ρ := by
    have hρ32 : 1 + ρ ≤ 3 / 2 := by linarith
    have h1 : t * ((k : ℝ) * CH ^ 2 + 1) ≤ δ / 20 := by nlinarith [hbound4]
    have h2 : t * ((k : ℝ) * CH ^ 2) ≤ δ / 20 := by nlinarith [ht0]
    have h3 : 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2)) * (1 + ρ)
        ≤ 3 * (t * (t * ((k : ℝ) * CH ^ 2))) := by
      nlinarith [mul_nonneg (mul_nonneg ht0.le ht0.le)
        (by positivity : (0 : ℝ) ≤ (k : ℝ) * CH ^ 2), hρ32, hρ0]
    have h4 : t * (t * ((k : ℝ) * CH ^ 2)) ≤ t * (δ / 20) :=
      mul_le_mul_of_nonneg_left h2 ht0.le
    have h5 : 3 * (t * (δ / 20)) < ρ := by
      rw [hρ]
      nlinarith [mul_pos ht0 _hδ]
    linarith [h3, h4, h5]
  have hprod0 : 0 ≤ 1 - 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2)) := by
    nlinarith [hsmall, hρ0, hρhalf, mul_nonneg (mul_nonneg (sq_nonneg t)
      (by positivity : (0 : ℝ) ≤ (k : ℝ) * CH ^ 2)) hρ0.le]
  calc (1 : ℝ) < (1 + ρ) * (1 - 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2))) := by
        nlinarith [hsmall]
    _ ≤ (1 - ρ)⁻¹ ^ k * (1 - 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2))) :=
        mul_le_mul_of_nonneg_right hck hprod0
    _ ≤ (1 - ρ)⁻¹ ^ k * D := mul_le_mul_of_nonneg_left hdetT (by positivity)

/-- **First-order optimality in John position.** If the identity has maximal `‖det‖`
among feasible operators for `q` (with `q ≤ ‖·‖`), then no self-adjoint trace-zero `H`
can satisfy `re ⟪u, H u⟫ ≤ -δ < 0` at every unit vector `u` touching the body
(`q u = 1`).

Otherwise `S = (1 - ρ)⁻¹ • (id + t H)` with `ρ = tδ/4` would be feasible for small
`t > 0`: near the touching set the Euclidean norm of `(id + t H) u` shrinks linearly in
`t` (`norm_add_smul_le_of_inner_le` — this is where `re ⟪u, H u⟫ ≤ -δ` enters), and
away from it `q` is uniformly below `1` by compactness
(`exists_gap_of_lt_one_on_compact`), so `S` is feasible by rescaling
(`smul_mem_feasible_of_le_on_sphere`). Meanwhile the trace-zero determinant bound
`one_sub_le_norm_det_one_add_smul` shows the perturbation loses only `O(t²)` of
determinant — beaten by the first-order gain `(1 - ρ)⁻¹ ≥ 1 + tδ/4`. So `‖det S‖ > 1`,
contradicting maximality. -/
lemma no_neg_direction_of_maxVolume (hk : 0 < k)
    {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))} (hqc : Continuous q)
    (hq1 : ∀ x, q x ≤ ‖x‖) (hmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1)
    {H : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k)}
    (hHsa : IsSelfAdjoint H)
    (htr : LinearMap.trace 𝕜 (EuclideanSpace 𝕜 (Fin k))
      (H : EuclideanSpace 𝕜 (Fin k) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin k)) = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hneg : ∀ u, ‖u‖ = 1 → q u = 1 → re ⟪u, H u⟫_𝕜 ≤ -δ) : False := by
  classical
  set CH : ℝ := ‖H‖ with hCH
  -- the set `B` of unit vectors where `H` does not improve, and its `q`-gap `η`
  set B : Set (EuclideanSpace 𝕜 (Fin k)) :=
    {u | ‖u‖ = 1 ∧ -(δ / 2) ≤ re ⟪u, H u⟫_𝕜} with hB
  have hBclosed : IsClosed B := by
    rw [hB, Set.ofPred_and]
    exact (isClosed_eq continuous_norm continuous_const).inter
      (isClosed_le continuous_const
        (RCLike.continuous_re.comp (Continuous.inner continuous_id H.continuous)))
  have hBcompact : IsCompact B := by
    have hsub : B ⊆ Metric.sphere 0 1 := fun u hu => by simpa using hu.1
    exact (isCompact_sphere 0 1).of_isClosed_subset hBclosed hsub
  have hBlt : ∀ u ∈ B, q u < 1 := by
    intro u hu
    have hle : q u ≤ 1 := (hq1 u).trans_eq hu.1
    rcases hle.lt_or_eq with h | h
    · exact h
    · exact absurd (hneg u hu.1 h) (not_le.mpr (by linarith [hu.2]))
  obtain ⟨η, hη0, hη1, hηB⟩ := exists_gap_of_lt_one_on_compact hqc hBcompact hBlt
  -- a perturbation size `t` small enough for all four estimates below
  obtain ⟨t, ht0, hta, htb, htc, htd⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ δ / (2 * CH ^ 2 + 1) ∧
      t ≤ η / (2 * CH + 1) ∧ t ≤ 2 * η / δ ∧ t ≤ δ / (20 * ((k : ℝ) * CH ^ 2 + 1)) :=
    ⟨min (min (δ / (2 * CH ^ 2 + 1)) (η / (2 * CH + 1)))
        (min (2 * η / δ) (δ / (20 * ((k : ℝ) * CH ^ 2 + 1)))),
      by refine lt_min (lt_min ?_ ?_) (lt_min ?_ ?_) <;> positivity,
      le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _),
      le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (min_le_right _ _)⟩
  have hbound1 : t * CH ^ 2 ≤ δ / 2 := by
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * CH ^ 2 + 1)).mp hta
    nlinarith [ht0]
  have hbound2 : t * CH ≤ η / 2 := by
    have h2 := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * CH + 1)).mp htb
    nlinarith [ht0]
  have hbound3 : t * δ ≤ 2 * η := by
    have h2 : t * δ ≤ 2 * η / δ * δ := mul_le_mul_of_nonneg_right htc hδ.le
    rwa [div_mul_cancel₀ _ hδ.ne'] at h2
  have hbound4 : t * (20 * ((k : ℝ) * CH ^ 2 + 1)) ≤ δ :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 20 * ((k : ℝ) * CH ^ 2 + 1))).mp htd
  have htCH : t * CH ≤ 1 / 2 := by linarith
  have htδ4 : t * δ ≤ 4 := by linarith
  -- the perturbed operator and the uniform feasibility slack `ρ = tδ/4`
  set T : EuclideanSpace 𝕜 (Fin k) →L[𝕜] EuclideanSpace 𝕜 (Fin k) :=
    ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)) + ((t : ℝ) : 𝕜) • H with hT
  have hTapp : ∀ x, T x = x + ((t : ℝ) : 𝕜) • H x := fun x => by
    rw [hT, add_apply, smul_apply,
      ContinuousLinearMap.id_apply]
  set ρ : ℝ := t * δ / 4 with hρ
  have hρη : ρ ≤ η / 2 := by rw [hρ]; linarith
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρhalf : ρ ≤ 1 / 2 := by linarith
  have hslack : ∀ u, ‖u‖ = 1 → q (T u) ≤ 1 - ρ := by
    intro u hu
    rcases le_or_gt (re ⟪u, H u⟫_𝕜) (-(δ / 2)) with hA | hAB
    · -- near the touching set: the Euclidean norm itself shrinks
      calc q (T u) ≤ ‖T u‖ := hq1 _
        _ ≤ 1 - t * δ / 4 := by
            rw [hTapp u]
            exact norm_add_smul_le_of_inner_le hu ht0 hbound1 htδ4 hA
        _ = 1 - ρ := by rw [hρ]
    · -- away from the touching set: `q` has a uniform gap `η`
      have huB : u ∈ B := by
        rw [hB]
        exact ⟨hu, hAB.le⟩
      have hHu : ‖H u‖ ≤ CH := by simpa [hu] using H.le_opNorm u
      have h1 : q (T u) ≤ q u + t * q (H u) := by
        rw [hTapp u]
        refine le_trans (map_add_le_add q _ _) ?_
        rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos ht0]
      calc q (T u) ≤ q u + t * q (H u) := h1
        _ ≤ 1 - η + t * CH := add_le_add (hηB u huB)
            (mul_le_mul_of_nonneg_left (le_trans (hq1 _) hHu) ht0.le)
        _ ≤ 1 - η + η / 2 := by linarith [hbound2]
        _ = 1 - η / 2 := by ring
        _ ≤ 1 - ρ := by linarith
  -- the scaled perturbation is feasible, and its determinant exceeds 1
  have h1ρ : 0 < 1 - ρ := by linarith
  have hcpos : 0 < (1 - ρ)⁻¹ := inv_pos.mpr h1ρ
  have hSfeas : (((1 - ρ)⁻¹ : ℝ) : 𝕜) • T ∈ Feasible q :=
    smul_mem_feasible_of_le_on_sphere h1ρ hslack
  have hn : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = k := finrank_euclideanSpace_fin
  have hdetS : ‖((((1 - ρ)⁻¹ : ℝ) : 𝕜) • T).det‖ = (1 - ρ)⁻¹ ^ k * ‖T.det‖ := by
    have hsm : ((((1 - ρ)⁻¹ : ℝ) : 𝕜) • T).det = (((1 - ρ)⁻¹ : ℝ) : 𝕜) ^ k * T.det := by
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
        LinearMap.det_smul, hn]
    rw [hsm, norm_mul, norm_pow, RCLike.norm_ofReal, abs_of_pos hcpos]
  have hdetT : 1 - 2 * (t ^ 2 * ((k : ℝ) * CH ^ 2)) ≤ ‖T.det‖ := by
    have h := one_sub_le_norm_det_one_add_smul hHsa htr ht0
      (by rw [← hCH]; exact htCH)
    rw [hT, hCH]
    exact h
  have hgt : 1 < ‖((((1 - ρ)⁻¹ : ℝ) : 𝕜) • T).det‖ := by
    rw [hdetS]
    exact scaled_perturbation_det_gain hk ht0 hδ hρ hρ0 hρhalf hbound4 hdetT
  exact absurd (hmax _ hSfeas) (not_le.mpr hgt)

/-- **John decomposition of identity** — the classical core of John's ellipsoid
theorem.

In John position — the identity is a maximal-volume feasible operator for the body
seminorm `q` (`q u ≤ ‖u‖`, and `‖det S‖ ≤ 1` for every feasible `S`) — the
identity is a positive combination of the rank-one projections onto contact
points, with weights summing to the dimension `k`:
`∑ᵢ ((cᵢ:𝕜) · ⟪uᵢ, x⟫) • uᵢ = x`, with `uᵢ ∈ Contact q`, `cᵢ ≥ 0`, `∑ᵢ cᵢ = k`.

Proof: `k⁻¹ • id` lies in the convex hull of `{u ⊗ u : u ∈ Contact q}` — otherwise
`exists_selfAdjoint_of_not_mem_convexHull` would produce a self-adjoint trace-zero
improving direction, which `no_neg_direction_of_maxVolume` forbids (all unit vectors
with `q u = 1` are contact points by `mem_contact_of_apply_eq_one`). Carathéodory
(`mem_convexHull_iff_exists_fintype`) turns hull membership into a finite convex
combination `∑ᵢ wᵢ (uᵢ ⊗ uᵢ) = k⁻¹ • id`; multiplying by `k` and evaluating at `x`
gives the decomposition with `cᵢ = k wᵢ`. -/
theorem john_decomposition (q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k)))
    (hq : Continuous q) (hq1 : ∀ u, q u ≤ ‖u‖)
    (hmax : ∀ S ∈ Feasible q, ‖S.det‖ ≤ 1) :
    ∃ (N : ℕ) (u : Fin N → EuclideanSpace 𝕜 (Fin k)) (c : Fin N → ℝ),
      (∀ i, u i ∈ Contact q) ∧ (∀ i, 0 ≤ c i) ∧ (∑ i, c i = (k : ℝ)) ∧
      (∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x) := by
  classical
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- the space is trivial: the empty decomposition works
    subst hk0
    refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      by simp, fun x => ?_⟩
    have hx : x = 0 := by
      ext i
      exact i.elim0
    simp [hx]
  -- `k⁻¹ • id` is a convex combination of contact projections
  have hmem : ((k : ℝ)⁻¹ • ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin k)))
      ∈ convexHull ℝ (rankOneSA '' Contact q) := by
    by_contra hmem
    obtain ⟨H, δ, hδ, hHsa, htr, hneg⟩ := exists_selfAdjoint_of_not_mem_convexHull hk hmem
    exact no_neg_direction_of_maxVolume hk hq hq1 hmax hHsa htr hδ
      fun u hu hqu => hneg u (mem_contact_of_apply_eq_one hq1 hu hqu)
  obtain ⟨ι, hfin, w, z, hw0, hw1, hz, hsum⟩ := mem_convexHull_iff_exists_fintype.mp hmem
  let : Fintype ι := hfin
  choose v hv hvz using fun i => hz i
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm with he
  have hkR : ((k : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  refine ⟨Fintype.card ι, fun j => v (e j), fun j => (k : ℝ) * w (e j),
    fun j => hv (e j), fun j => mul_nonneg (Nat.cast_nonneg k) (hw0 (e j)), ?_, ?_⟩
  · -- the weights sum to `k`
    rw [Equiv.sum_comp e (fun i => (k : ℝ) * w i), ← Finset.mul_sum, hw1, mul_one]
  · -- the decomposition of identity, evaluated at `x`
    intro x
    have hx := DFunLike.congr_fun hsum x
    simp only [sum_apply, smul_apply,
      ContinuousLinearMap.id_apply] at hx
    have hzi : ∀ i, z i x = ⟪v i, x⟫_𝕜 • v i := fun i => by
      rw [← hvz i, rankOneSA_apply]
    have hx2 : ∑ i, ((((k : ℝ) * w i : ℝ) : 𝕜) * ⟪v i, x⟫_𝕜) • v i = x := by
      have h3 : ∑ i, (k : ℝ) • w i • z i x = x := by
        have h4 : (k : ℝ) • ∑ i, w i • z i x = (k : ℝ) • ((k : ℝ)⁻¹ • x) := by rw [hx]
        rwa [smul_smul, mul_inv_cancel₀ hkR, one_smul, Finset.smul_sum] at h4
      calc ∑ i, ((((k : ℝ) * w i : ℝ) : 𝕜) * ⟪v i, x⟫_𝕜) • v i
          = ∑ i, (k : ℝ) • w i • z i x := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hzi i, smul_smul, RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul]
        _ = x := h3
    calc ∑ j, ((((k : ℝ) * w (e j) : ℝ) : 𝕜) * ⟪v (e j), x⟫_𝕜) • v (e j)
        = ∑ i, ((((k : ℝ) * w i : ℝ) : 𝕜) * ⟪v i, x⟫_𝕜) • v i :=
          Equiv.sum_comp e (fun i => ((((k : ℝ) * w i : ℝ) : 𝕜) * ⟪v i, x⟫_𝕜) • v i)
      _ = x := hx2

/-- **Weighted Cauchy–Schwarz for a decomposition of identity** (the analytic
heart of the Kadets–Snobar estimate). If `∑ᵢ ((cᵢ:𝕜)·⟪uᵢ,x⟫)•uᵢ = x` and
`cᵢ ≥ 0`, then for any scalars `aᵢ`, `‖∑ᵢ ((cᵢ:𝕜)·aᵢ)•uᵢ‖ ≤ √(∑ᵢ cᵢ·‖aᵢ‖²)`. -/
lemma norm_sum_weight_smul_le {N : ℕ} (c : Fin N → ℝ)
    (u : Fin N → EuclideanSpace 𝕜 (Fin k))
    (hdec : ∀ x, ∑ i, ((c i : 𝕜) * ⟪u i, x⟫_𝕜) • u i = x)
    (hc : ∀ i, 0 ≤ c i) (a : Fin N → 𝕜) :
    ‖∑ i, ((c i : 𝕜) * a i) • u i‖ ≤ Real.sqrt (∑ i, c i * ‖a i‖ ^ 2) := by
  set w := ∑ i, ((c i : 𝕜) * a i) • u i with hw
  have hB : 0 ≤ ∑ i, c i * ‖a i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (sq_nonneg _)
  -- `‖w‖² = re ⟪w, w⟫ ≤ ∑ᵢ cᵢ ‖aᵢ‖ ‖⟪uᵢ, w⟫‖`.
  have hww : ‖w‖ ^ 2 ≤ ∑ i, c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖) := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) w]
    nth_rewrite 1 [hw]
    rw [sum_inner, map_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [inner_smul_left, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc,
      RCLike.re_ofReal_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hc i)
    calc re (conj (a i) * ⟪u i, w⟫_𝕜) ≤ ‖conj (a i) * ⟪u i, w⟫_𝕜‖ := RCLike.re_le_norm _
      _ = ‖a i‖ * ‖⟪u i, w⟫_𝕜‖ := by rw [norm_mul, RCLike.norm_conj]
  -- Weighted Cauchy–Schwarz on the reals, then `∑ᵢ cᵢ ‖⟪uᵢ,w⟫‖² = ‖w‖²`.
  have hCS : (∑ i, c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖)) ^ 2
      ≤ (∑ i, c i * ‖a i‖ ^ 2) * (∑ i, c i * ‖⟪u i, w⟫_𝕜‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => Real.sqrt (c i) * ‖a i‖) (fun i => Real.sqrt (c i) * ‖⟪u i, w⟫_𝕜‖)
    have e1 : ∀ i, Real.sqrt (c i) * ‖a i‖ * (Real.sqrt (c i) * ‖⟪u i, w⟫_𝕜‖)
        = c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖) := fun i => by
      rw [mul_mul_mul_comm, Real.mul_self_sqrt (hc i)]
    have e2 : ∀ i, (Real.sqrt (c i) * ‖a i‖) ^ 2 = c i * ‖a i‖ ^ 2 := fun i => by
      rw [mul_pow, Real.sq_sqrt (hc i)]
    have e3 : ∀ i, (Real.sqrt (c i) * ‖⟪u i, w⟫_𝕜‖) ^ 2 = c i * ‖⟪u i, w⟫_𝕜‖ ^ 2 := fun i => by
      rw [mul_pow, Real.sq_sqrt (hc i)]
    simpa only [e1, e2, e3] using h
  rw [sum_weight_inner_sq c u hdec w] at hCS
  rcases eq_or_lt_of_le (norm_nonneg w) with h0 | hpos
  · rw [← h0]; exact Real.sqrt_nonneg _
  · have ht : (0 : ℝ) < ‖w‖ ^ 2 := by positivity
    have hle : ‖w‖ ^ 2 ≤ ∑ i, c i * ‖a i‖ ^ 2 := by
      refine le_of_mul_le_mul_right ?_ ht
      calc ‖w‖ ^ 2 * ‖w‖ ^ 2 = (‖w‖ ^ 2) ^ 2 := (pow_two _).symm
        _ ≤ (∑ i, c i * (‖a i‖ * ‖⟪u i, w⟫_𝕜‖)) ^ 2 := by
            apply pow_le_pow_left₀ (by positivity) hww
        _ ≤ (∑ i, c i * ‖a i‖ ^ 2) * ‖w‖ ^ 2 := hCS
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ ≤ Real.sqrt (∑ i, c i * ‖a i‖ ^ 2) := Real.sqrt_le_sqrt hle

/-- **Kadets–Snobar.** Every finite-dimensional subspace `V` of a normed
`𝕜`-space `Y` is the range of a bounded projection `P : Y →L[𝕜] Y` with
`‖P‖ ≤ √(dim V)`.

The proof puts `V` in John position: transport the Euclidean structure of
`𝕜^{dim V}` to `V` through the maximal-volume ellipsoid `M` (built from the John
decomposition of identity `∑ᵢ cᵢ uᵢ⊗uᵢ = id`). The contact points `uᵢ` give unit
vectors `vᵢ = M uᵢ ∈ V` and functionals `φᵢ = ⟪uᵢ, M⁻¹ ·⟫ ∈ V*` of norm `≤ 1`,
which Hahn–Banach (`exists_extension_norm_eq`) extends to `gᵢ ∈ Y*` without
increasing the norm. Then `P = ∑ᵢ cᵢ · gᵢ ⊗ vᵢ` is the identity on `V` (so it is
a projection onto `V`), and the weighted Cauchy–Schwarz estimate
`norm_sum_weight_smul_le` together with `∑ᵢ cᵢ = dim V` yields `‖P‖ ≤ √(dim V)`. -/
theorem exists_projection {Y : Type u} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (V : Submodule 𝕜 Y) [FiniteDimensional 𝕜 V] :
    ∃ P : Y →L[𝕜] Y, P.comp P = P ∧
      LinearMap.range (P : Y →ₗ[𝕜] Y) = V ∧ ‖P‖ ≤ Real.sqrt (Module.finrank 𝕜 V) := by
  classical
  set k := Module.finrank 𝕜 V with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `V = ⊥`: the zero map works.
    refine ⟨0, by simp, ?_, ?_⟩
    · have hV : V = ⊥ := Submodule.finrank_eq_zero.mp (hk.symm.trans hk0)
      rw [hV]; simp
    · rw [hk0]; simp
  -- From now on `0 < k`.
  -- A continuous linear equivalence `𝕜^k ≃L V` (both have dimension `k`), and the
  -- John position along it: `M = L ∘ T₀` with `‖M z‖ = q z`.
  have hEfin : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = k := finrank_euclideanSpace_fin
  obtain ⟨M, q, hqc, hq1, hqmax, hqM₀⟩ :=
    exists_johnPosition hkpos (ContinuousLinearEquiv.ofFinrankEq (hEfin.trans hk) :
      EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] V)
  have hqM : ∀ z, ‖(M z : Y)‖ = q z := fun z => by
    rw [Submodule.norm_coe]; exact hqM₀ z
  -- The John decomposition of identity in John position.
  obtain ⟨N, u, c, hcontact, hcnn, hcsum, hdec⟩ := john_decomposition q hqc hq1 hqmax
  -- Functionals `φ i = ⟪u i, M.symm ·⟫` on `V`, of norm `≤ 1`.
  set φ : Fin N → (V →L[𝕜] 𝕜) :=
    fun i => (innerSL 𝕜 (u i)).comp (M.symm : V →L[𝕜] EuclideanSpace 𝕜 (Fin k)) with hφ
  have hφapply : ∀ i (w : V), φ i w = ⟪u i, M.symm w⟫_𝕜 := fun i w => by
    simp only [hφ, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      innerSL_apply_apply]
  have hφnorm : ∀ i, ‖φ i‖ ≤ 1 := fun i => by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
    rw [one_mul, hφapply]
    calc ‖⟪u i, M.symm w⟫_𝕜‖ = ‖⟪M.symm w, u i⟫_𝕜‖ := by
          rw [← inner_conj_symm (M.symm w) (u i), RCLike.norm_conj]
      _ ≤ q (M.symm w) := norm_inner_le_of_contact (hcontact i) (M.symm w)
      _ = ‖(M (M.symm w) : Y)‖ := (hqM (M.symm w)).symm
      _ = ‖w‖ := by rw [M.apply_symm_apply, Submodule.norm_coe]
  -- Hahn–Banach: extend each `φ i` to `g i ∈ Y*` without increasing the norm.
  choose g hg_ext hg_norm using fun i => exists_extension_norm_eq V (φ i)
  have hgnorm1 : ∀ i, ‖g i‖ ≤ 1 := fun i => (hg_norm i).trans_le (hφnorm i)
  -- The projection `P = ∑ᵢ cᵢ · g i ⊗ (M (u i))`.
  set P : Y →L[𝕜] Y := ∑ i, (c i : 𝕜) • ((g i).smulRight ((M (u i) : V) : Y)) with hP
  have hPapply : ∀ y, P y = ∑ i, ((c i : 𝕜) * g i y) • ((M (u i) : Y)) := fun y => by
    rw [hP]
    simp only [sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_smul]
  have hPmem : ∀ y, P y ∈ V := fun y => by
    rw [hPapply]
    exact V.sum_mem fun i _ => V.smul_mem _ (M (u i)).2
  -- `P` is the identity on `V`.
  have hPV : ∀ w : V, P (w : Y) = (w : Y) := fun w => by
    rw [hPapply]
    have hgi : ∀ i, g i (w : Y) = ⟪u i, M.symm w⟫_𝕜 := fun i => by rw [hg_ext i w, hφapply i w]
    simp only [hgi]
    have hpull : ((M (∑ i, ((c i : 𝕜) * ⟪u i, M.symm w⟫_𝕜) • u i) : V) : Y)
        = ∑ i, ((c i : 𝕜) * ⟪u i, M.symm w⟫_𝕜) • ((M (u i) : V) : Y) := by
      rw [map_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Submodule.coe_smul]
    rw [← hpull, hdec (M.symm w), M.apply_symm_apply]
  refine ⟨P, ?_, ?_, ?_⟩
  · -- `P ∘ P = P`, since `P` fixes its range `⊆ V`.
    ext y
    simpa [ContinuousLinearMap.comp_apply] using hPV ⟨P y, hPmem y⟩
  · -- `range P = V`.
    apply le_antisymm
    · rintro x hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨y, rfl⟩ := hx
      exact hPmem y
    · intro w hw
      rw [LinearMap.mem_range]
      exact ⟨w, by simpa using hPV ⟨w, hw⟩⟩
  · -- `‖P‖ ≤ √k`.
    refine ContinuousLinearMap.opNorm_le_bound P (Real.sqrt_nonneg _) fun y => ?_
    have hpull : ((M (∑ i, ((c i : 𝕜) * g i y) • u i) : V) : Y)
        = ∑ i, ((c i : 𝕜) * g i y) • ((M (u i) : V) : Y) := by
      rw [map_sum, Submodule.coe_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, Submodule.coe_smul]
    have hPyeq : P y = ((M (∑ i, ((c i : 𝕜) * g i y) • u i) : V) : Y) := by rw [hPapply, hpull]
    have hb : ∑ i, c i * ‖g i y‖ ^ 2 ≤ (k : ℝ) * ‖y‖ ^ 2 := by
      have hstep : ∀ i, c i * ‖g i y‖ ^ 2 ≤ c i * ‖y‖ ^ 2 := fun i => by
        apply mul_le_mul_of_nonneg_left _ (hcnn i)
        calc ‖g i y‖ ^ 2 ≤ (‖g i‖ * ‖y‖) ^ 2 := by
              apply pow_le_pow_left₀ (norm_nonneg _) ((g i).le_opNorm y)
          _ ≤ (1 * ‖y‖) ^ 2 := by
              apply pow_le_pow_left₀ (by positivity)
              exact mul_le_mul_of_nonneg_right (hgnorm1 i) (norm_nonneg _)
          _ = ‖y‖ ^ 2 := by rw [one_mul]
      calc ∑ i, c i * ‖g i y‖ ^ 2 ≤ ∑ i, c i * ‖y‖ ^ 2 := Finset.sum_le_sum fun i _ => hstep i
        _ = (∑ i, c i) * ‖y‖ ^ 2 := (Finset.sum_mul _ _ _).symm
        _ = (k : ℝ) * ‖y‖ ^ 2 := by rw [hcsum]
    calc ‖P y‖ = q (∑ i, ((c i : 𝕜) * g i y) • u i) := by rw [hPyeq, hqM]
      _ ≤ ‖∑ i, ((c i : 𝕜) * g i y) • u i‖ := hq1 _
      _ ≤ Real.sqrt (∑ i, c i * ‖g i y‖ ^ 2) :=
          norm_sum_weight_smul_le c u hdec hcnn (fun i => g i y)
      _ ≤ Real.sqrt ((k : ℝ) * ‖y‖ ^ 2) := Real.sqrt_le_sqrt hb
      _ = Real.sqrt (k : ℝ) * ‖y‖ := by
          rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq (norm_nonneg _)]

/-! ### Ingredients for the dual (Garling–Gordon) projection

`exists_projection_ker` below runs the Kadets–Snobar argument in the
finite-dimensional dual `D = (X ⧸ M)*`, where the John-position map is a
contraction `Φ : 𝕜^k ≃L D`. Three steps of that argument are independent of the
quotient and are recorded here for a `W` in place of `X ⧸ M`. -/

section DualProjection

variable {W : Type u} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- **Riesz representation of evaluation.** If `Φ : 𝕜^k ≃L W*` is a contraction,
then for every `v : W` the functional `z ↦ (Φ z) v` on `𝕜^k` is an inner product
`⟪r, ·⟫` against a vector `r` with `‖r‖ ≤ ‖v‖`.

This is how a vector of `W` is turned into a Euclidean vector, so that the
decomposition of identity (which lives on `𝕜^k`) can be applied to it. -/
private lemma exists_riesz_repr (Φ : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] StrongDual 𝕜 W)
    (hΦ : ∀ z, ‖Φ z‖ ≤ ‖z‖) (v : W) :
    ∃ r : EuclideanSpace 𝕜 (Fin k), (∀ z, ⟪r, z⟫_𝕜 = (Φ z) v) ∧ ‖r‖ ≤ ‖v‖ := by
  set ℓ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] 𝕜 :=
    ((NormedSpace.inclusionInDoubleDual 𝕜 W) v).comp
      (Φ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] StrongDual 𝕜 W) with hℓ
  have hℓapply : ∀ z, ℓ z = (Φ z) v := fun z => rfl
  have hℓnorm : ‖ℓ‖ ≤ ‖v‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun z => ?_
    rw [hℓapply z]
    calc ‖(Φ z) v‖ ≤ ‖Φ z‖ * ‖v‖ := (Φ z).le_opNorm v
      _ ≤ ‖z‖ * ‖v‖ := mul_le_mul_of_nonneg_right (hΦ z) (norm_nonneg v)
      _ = ‖v‖ * ‖z‖ := mul_comm _ _
  refine ⟨(InnerProductSpace.toDual 𝕜 (EuclideanSpace 𝕜 (Fin k))).symm ℓ, fun z => ?_, ?_⟩
  · rw [InnerProductSpace.toDual_symm_apply]
    exact hℓapply z
  · rw [LinearIsometryEquiv.norm_map]
    exact hℓnorm

/-- **A contact point of the dual body is represented by a vector of `W`.**
For a contact point `u₀` of the body seminorm `q` (so `‖⟪z, u₀⟫‖ ≤ q z`), there is
`w : W` with `‖w‖ ≤ 1` representing `u₀` in the sense that
`g w = ⟪u₀, Φ.symm g⟫` for every `g : W*`.

The point of the statement is that it avoids the *topological double dual*: the
flip `Φ.flip : W → (𝕜^k)*` is injective (a nonzero `v` is separated by some
functional) between spaces of equal finite dimension `k`, hence surjective, so
the Riesz vector of `u₀` is hit by some `w`. The norm bound is then the contact
inequality read through `‖Φ z‖ = q z`. -/
private lemma exists_witness_of_contact
    (hkW : Module.finrank 𝕜 W = k)
    (Φ : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] StrongDual 𝕜 W)
    {q : Seminorm 𝕜 (EuclideanSpace 𝕜 (Fin k))} (hqΦ : ∀ z, ‖Φ z‖ = q z)
    (u₀ : EuclideanSpace 𝕜 (Fin k)) (hu₀ : ∀ z, ‖⟪z, u₀⟫_𝕜‖ ≤ q z) :
    ∃ w : W, (∀ g : StrongDual 𝕜 W, g w = ⟪u₀, Φ.symm g⟫_𝕜) ∧ ‖w‖ ≤ 1 := by
  classical
  set T : W →L[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k)) :=
    (Φ : EuclideanSpace 𝕜 (Fin k) →L[𝕜] StrongDual 𝕜 W).flip with hT
  have hTapply : ∀ (v : W) (z : EuclideanSpace 𝕜 (Fin k)), T v z = Φ z v :=
    fun v z => ContinuousLinearMap.flip_apply _ z v
  have : FiniteDimensional 𝕜 (StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) :=
    Module.Finite.equiv
      (LinearMap.toContinuousLinearMap :
        ((EuclideanSpace 𝕜 (Fin k)) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] ((EuclideanSpace 𝕜 (Fin k)) →L[𝕜] 𝕜))
  have hkSD : Module.finrank 𝕜 (StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) = k := by
    rw [← (LinearMap.toContinuousLinearMap :
          ((EuclideanSpace 𝕜 (Fin k)) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜]
            ((EuclideanSpace 𝕜 (Fin k)) →L[𝕜] 𝕜)).finrank_eq,
        Subspace.dual_finrank_eq, finrank_euclideanSpace_fin]
  have hTinj : Function.Injective
      (T : W →ₗ[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    refine norm_le_zero_iff.mp (NormedSpace.norm_le_dual_bound 𝕜 v le_rfl fun g => ?_)
    have hgv : g v = 0 := by
      have h2 := hTapply v (Φ.symm g)
      rw [Φ.apply_symm_apply] at h2
      rw [← h2, show T v = 0 from hv]; rfl
    simp [hgv]
  have hTsurj : Function.Surjective
      (T : W →ₗ[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) := by
    have hrank : Module.finrank 𝕜 (LinearMap.range
        (T : W →ₗ[𝕜] StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))))
        = Module.finrank 𝕜 (StrongDual 𝕜 (EuclideanSpace 𝕜 (Fin k))) := by
      rw [LinearMap.finrank_range_of_inj hTinj, hkSD, hkW]
    rw [← LinearMap.range_eq_top]
    exact Submodule.eq_top_of_finrank_eq hrank
  obtain ⟨w, hw⟩ := hTsurj (InnerProductSpace.toDual 𝕜 (EuclideanSpace 𝕜 (Fin k)) u₀)
  have hweval : ∀ g : StrongDual 𝕜 W, g w = ⟪u₀, Φ.symm g⟫_𝕜 := fun g => by
    have h1 : T w (Φ.symm g) = ⟪u₀, Φ.symm g⟫_𝕜 := by
      rw [show T w = InnerProductSpace.toDual 𝕜 (EuclideanSpace 𝕜 (Fin k)) u₀ from hw,
        InnerProductSpace.toDual_apply_apply]
    rwa [hTapply w (Φ.symm g), Φ.apply_symm_apply] at h1
  refine ⟨w, hweval, ?_⟩
  refine NormedSpace.norm_le_dual_bound 𝕜 w zero_le_one fun g => ?_
  rw [one_mul, hweval g]
  calc ‖⟪u₀, Φ.symm g⟫_𝕜‖ = ‖⟪Φ.symm g, u₀⟫_𝕜‖ := by
        rw [← inner_conj_symm (Φ.symm g) u₀, RCLike.norm_conj]
    _ ≤ q (Φ.symm g) := hu₀ (Φ.symm g)
    _ = ‖Φ (Φ.symm g)‖ := (hqΦ (Φ.symm g)).symm
    _ = ‖g‖ := by rw [Φ.apply_symm_apply]

/-- **The witnesses reproduce every vector.** With `w i` representing the contact
point `u i` (as in `exists_witness_of_contact`) and `cᵢ, uᵢ` a decomposition of
identity, every `v : W` is recovered as `∑ᵢ (cᵢ · (Φ uᵢ) v) • wᵢ`.

This is the identity that makes the operator built from the `wᵢ` a *projection*:
pairing with an arbitrary `g : W*` turns the claim into the decomposition of
identity applied to the Riesz vector of `v`. -/
private lemma sum_weight_smul_witness_eq
    (Φ : EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] StrongDual 𝕜 W) (hΦ : ∀ z, ‖Φ z‖ ≤ ‖z‖)
    {N : ℕ} (c : Fin N → ℝ) (u : Fin N → EuclideanSpace 𝕜 (Fin k)) (w : Fin N → W)
    (hdec : ∀ z, ∑ i, ((c i : 𝕜) * ⟪u i, z⟫_𝕜) • u i = z)
    (hweval : ∀ i (g : StrongDual 𝕜 W), g (w i) = ⟪u i, Φ.symm g⟫_𝕜) (v : W) :
    (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) = v := by
  obtain ⟨r, hr, -⟩ := exists_riesz_repr Φ hΦ v
  apply (NormedSpace.inclusionInDoubleDualLi (E := W) 𝕜).injective
  apply ContinuousLinearMap.ext
  intro g
  have hLHS : (NormedSpace.inclusionInDoubleDualLi (E := W) 𝕜)
      (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) g
      = ∑ i, ((c i : 𝕜) * (Φ (u i)) v) * g (w i) := by
    change g (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
  have hRHS : (NormedSpace.inclusionInDoubleDualLi (E := W) 𝕜) v g = g v := rfl
  rw [hLHS, hRHS]
  -- Rewrite through the Riesz vector and the decomposition of identity.
  set z := Φ.symm g with hz
  have hgz : g = Φ z := by rw [hz, Φ.apply_symm_apply]
  calc ∑ i, ((c i : 𝕜) * (Φ (u i)) v) * g (w i)
      = ∑ i, (c i : 𝕜) * ⟪u i, z⟫_𝕜 * ⟪r, u i⟫_𝕜 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hweval i g, ← hz, hr (u i)]; ring
    _ = ⟪r, ∑ i, ((c i : 𝕜) * ⟪u i, z⟫_𝕜) • u i⟫_𝕜 := by
        rw [inner_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [inner_smul_right]
    _ = ⟪r, z⟫_𝕜 := by rw [hdec z]
    _ = (Φ z) v := hr z
    _ = g v := by rw [← hgz]

end DualProjection

/-- **Garling–Gordon, ε-form.** Every closed subspace `M` of a normed `𝕜`-space
`X` with finite-dimensional quotient is the kernel of a bounded projection
`P : X →L[𝕜] X` with `‖P‖ ≤ √(codim M) + ε`, for every `ε > 0`.

This is the dual of `exists_projection`, run in the finite-dimensional dual
`D = (X ⧸ M)*` (so no dual of `X` is needed). John position of the unit ball of
`D` gives contact points `uᵢ` and weights `cᵢ` with `∑ᵢ cᵢ = codim M`; the
`uᵢ` become unit functionals `fᵢ = Φ uᵢ ∈ D` on the quotient, and the contact
supports become norm-`≤ 1` functionals on `D`, i.e. — since `X ⧸ M` is
finite-dimensional, hence isometrically reflexive
(`NormedSpace.inclusionInDoubleDualLi`) — vectors `wᵢ ∈ X ⧸ M` with `‖wᵢ‖ ≤ 1`.
Lifting each `wᵢ` to a representative `xᵢ ∈ X` with `‖xᵢ‖ < 1 + ε'`
(`Submodule.Quotient.norm_mk_lt` — the quotient norm is an infimum; this is the
sole source of the `ε`), the operator `P y = ∑ᵢ cᵢ · fᵢ(π y) · xᵢ` satisfies
`π ∘ P = π` (via the decomposition of identity and the Riesz representation on
the Euclidean model), hence is a projection with kernel `M`; Cauchy–Schwarz and
the quadratic identity `sum_weight_inner_sq` give `‖P‖ ≤ (1 + ε')·√(codim M)`. -/
theorem exists_projection_ker {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (M : Submodule 𝕜 X) [IsClosed (M : Set X)] [FiniteDimensional 𝕜 (X ⧸ M)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : X →L[𝕜] X, P.comp P = P ∧ LinearMap.ker (P : X →ₗ[𝕜] X) = M ∧
      ‖P‖ ≤ Real.sqrt (Module.finrank 𝕜 (X ⧸ M)) + ε := by
  classical
  set k := Module.finrank 𝕜 (X ⧸ M) with hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `codim M = 0`: the quotient is trivial, `M = ⊤`, and `P = 0` works.
    have hsub : Subsingleton (X ⧸ M) :=
      Module.finrank_zero_iff.mp (hk.symm.trans hk0)
    have hM : M = ⊤ := by
      ext x0
      simp only [Submodule.mem_top, iff_true]
      have := Subsingleton.elim (Submodule.Quotient.mk x0 : X ⧸ M) 0
      exact (Submodule.Quotient.mk_eq_zero M).mp this
    refine ⟨0, by simp, ?_, ?_⟩
    · rw [hM]; simp [LinearMap.ker_zero]
    · simp only [norm_zero]; positivity
  -- From now on `0 < k`. The finite-dimensional dual `D := (X ⧸ M)*`.
  have hEfin : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin k)) = k := finrank_euclideanSpace_fin
  have hDfin : FiniteDimensional 𝕜 (StrongDual 𝕜 (X ⧸ M)) :=
    Module.Finite.equiv
      (LinearMap.toContinuousLinearMap : ((X ⧸ M) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] ((X ⧸ M) →L[𝕜] 𝕜))
  have hkD : Module.finrank 𝕜 (StrongDual 𝕜 (X ⧸ M)) = k := by
    rw [← (LinearMap.toContinuousLinearMap :
          ((X ⧸ M) →ₗ[𝕜] 𝕜) ≃ₗ[𝕜] ((X ⧸ M) →L[𝕜] 𝕜)).finrank_eq]
    exact (Subspace.dual_finrank_eq (K := 𝕜) (V := X ⧸ M)).trans hk.symm
  -- A continuous linear equivalence `𝕜^k ≃L D`, and the John position along it:
  -- `Φ = L ∘ T₀` with `‖Φ z‖ = q z`.
  obtain ⟨Φ, q, hqc, hq1, hqmax, hqΦ⟩ :=
    exists_johnPosition hkpos (ContinuousLinearEquiv.ofFinrankEq (hEfin.trans hkD.symm) :
      EuclideanSpace 𝕜 (Fin k) ≃L[𝕜] StrongDual 𝕜 (X ⧸ M))
  -- The John decomposition of identity in John position.
  obtain ⟨N, u, c, hcontact, hcnn, hcsum, hdec⟩ := john_decomposition q hqc hq1 hqmax
  -- The John-position map is a contraction, so evaluation at `v ∈ X ⧸ M` pulls
  -- back through `Φ` to an inner product against a vector of norm `≤ ‖v‖`.
  have hΦle : ∀ z, ‖Φ z‖ ≤ ‖z‖ := fun z => (hqΦ z).trans_le (hq1 z)
  have hRiesz : ∀ v : X ⧸ M, ∃ r : EuclideanSpace 𝕜 (Fin k),
      (∀ z, ⟪r, z⟫_𝕜 = (Φ z) v) ∧ ‖r‖ ≤ ‖v‖ := fun v => exists_riesz_repr Φ hΦle v
  -- Represent each contact point `u i` by a vector `w i ∈ X ⧸ M` of norm `≤ 1`
  -- (`exists_witness_of_contact`, via the single dual `Φ.flip`).
  choose w hweval hwnorm using fun i =>
    exists_witness_of_contact hk.symm Φ hqΦ (u i) (norm_inner_le_of_contact (hcontact i))
  -- Lift each `w i` to a representative `x i ∈ X` with `‖x i‖ < 1 + ε'` — the
  -- sole source of the `ε`.
  set ε' : ℝ := ε / Real.sqrt k with hε'def
  have hsqrtk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hkpos)
  have hε' : 0 < ε' := div_pos hε hsqrtk
  choose x hxmk hxnorm using fun i => Submodule.Quotient.norm_mk_lt (w i) hε'
  have hxbound : ∀ i, ‖x i‖ ≤ 1 + ε' := fun i => by
    linarith [hxnorm i, hwnorm i]
  -- The projection `P = ∑ᵢ cᵢ · (Φ uᵢ)(π ·) · xᵢ`.
  set π : X →L[𝕜] X ⧸ M := M.mkQL with hπdef
  have hπmk : ∀ y : X, π y = Submodule.Quotient.mk y := fun y => by
    rw [hπdef, Submodule.mkQL_apply, Submodule.mkQ_apply]
  have hπx : ∀ i, π (x i) = w i := fun i => by rw [hπmk]; exact hxmk i
  have hπle : ∀ y : X, ‖π y‖ ≤ ‖y‖ := fun y => by
    rw [hπmk]; exact Submodule.Quotient.norm_mk_le M y
  set P : X →L[𝕜] X := ∑ i, (c i : 𝕜) • (((Φ (u i)).comp π).smulRight (x i)) with hP
  have hPapply : ∀ y, P y = ∑ i, ((c i : 𝕜) * (Φ (u i)) (π y)) • x i := fun y => by
    rw [hP]
    simp only [sum_apply, smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, smul_smul]
  -- Key identity: the weighted combination of the `w i` reproduces every `v`.
  have hkey : ∀ v : X ⧸ M, (∑ i, ((c i : 𝕜) * (Φ (u i)) v) • w i) = v :=
    fun v => sum_weight_smul_witness_eq Φ hΦle c u w hdec hweval v
  have hπP : ∀ y, π (P y) = π y := fun y => by
    have hsum : π (P y) = ∑ i, ((c i : 𝕜) * (Φ (u i)) (π y)) • w i := by
      rw [hPapply, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hπx i]
    rw [hsum, hkey (π y)]
  refine ⟨P, ?_, ?_, ?_⟩
  · -- `P ∘ P = P`, since `π ∘ P = π`.
    ext y
    change P (P y) = P y
    rw [hPapply (P y), hπP y, ← hPapply y]
  · -- `ker P = M`.
    ext x0
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    constructor
    · intro hPx
      have h0 : π x0 = 0 := by rw [← hπP x0, hPx, map_zero]
      rw [hπmk] at h0
      exact (Submodule.Quotient.mk_eq_zero M).mp h0
    · intro hx0
      have h0 : π x0 = 0 := by rw [hπmk]; exact (Submodule.Quotient.mk_eq_zero M).mpr hx0
      rw [hPapply, h0]
      simp
  · -- `‖P‖ ≤ √k + ε`.
    have hbnd : (0 : ℝ) ≤ Real.sqrt k + ε := by positivity
    refine ContinuousLinearMap.opNorm_le_bound P hbnd fun y => ?_
    obtain ⟨r, hr, hrnorm⟩ := hRiesz (π y)
    -- `∑ᵢ cᵢ ‖fᵢ(πy)‖² = ‖r‖² ≤ ‖y‖²` via the quadratic identity.
    have hquad : ∑ i, c i * ‖(Φ (u i)) (π y)‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      have h1 : ∀ i, ‖(Φ (u i)) (π y)‖ = ‖⟪u i, r⟫_𝕜‖ := fun i => by
        rw [← hr (u i), ← inner_conj_symm r (u i), RCLike.norm_conj]
      calc ∑ i, c i * ‖(Φ (u i)) (π y)‖ ^ 2
          = ∑ i, c i * ‖⟪u i, r⟫_𝕜‖ ^ 2 := by
            exact Finset.sum_congr rfl fun i _ => by rw [h1 i]
        _ = ‖r‖ ^ 2 := sum_weight_inner_sq c u hdec r
        _ ≤ ‖π y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg r) hrnorm 2
        _ ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hπle y) 2
    -- Cauchy–Schwarz: `∑ᵢ cᵢ ‖fᵢ(πy)‖ ≤ √k · ‖y‖`.
    have hCS : ∑ i, c i * ‖(Φ (u i)) (π y)‖ ≤ Real.sqrt k * ‖y‖ := by
      calc ∑ i, c i * ‖(Φ (u i)) (π y)‖
          ≤ Real.sqrt (∑ i, c i) * Real.sqrt (∑ i, c i * ‖(Φ (u i)) (π y)‖ ^ 2) :=
            sum_weight_mul_le_sqrt c hcnn _
        _ ≤ Real.sqrt k * Real.sqrt (‖y‖ ^ 2) := by
            rw [hcsum]
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hquad) (Real.sqrt_nonneg _)
        _ = Real.sqrt k * ‖y‖ := by rw [Real.sqrt_sq (norm_nonneg _)]
    -- Assemble.
    calc ‖P y‖ ≤ ∑ i, ‖((c i : 𝕜) * (Φ (u i)) (π y)) • x i‖ := by
          rw [hPapply]; exact norm_sum_le _ _
      _ = ∑ i, c i * ‖(Φ (u i)) (π y)‖ * ‖x i‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_smul, norm_mul, RCLike.norm_ofReal, abs_of_nonneg (hcnn i)]
      _ ≤ ∑ i, c i * ‖(Φ (u i)) (π y)‖ * (1 + ε') := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul_of_nonneg_left (hxbound i)
            (mul_nonneg (hcnn i) (norm_nonneg _))
      _ = (1 + ε') * ∑ i, c i * ‖(Φ (u i)) (π y)‖ := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ (1 + ε') * (Real.sqrt k * ‖y‖) :=
          mul_le_mul_of_nonneg_left hCS (by positivity)
      _ = (Real.sqrt k + ε) * ‖y‖ := by
          rw [← mul_assoc, show (1 + ε') * Real.sqrt k = Real.sqrt k + ε from by
            rw [hε'def, add_mul, one_mul, div_mul_cancel₀ ε (ne_of_gt hsqrtk)]]

end John

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
