/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Gap geometry for orthogonally complemented subspaces

The symmetric and directed projection gaps over arbitrary `RCLike` scalars.
-/

@[expose] public section


open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Submodule

/-- Operator-norm gap between two orthogonal projections. -/
noncomputable def projectionGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  ‖U.starProjection - V.starProjection‖

/-- Directed gap from `U` to `V`. -/
noncomputable def directedProjectionGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  ‖Vᗮ.starProjection ∘L U.starProjection‖

/-- The projection gap is symmetric. -/
theorem projectionGap_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.projectionGap V = V.projectionGap U := by
  unfold projectionGap
  rw [show V.starProjection - U.starProjection =
      -(U.starProjection - V.starProjection) by abel, norm_neg]

/-- The directed gap is bounded by the symmetric projection gap. -/
theorem directedProjectionGap_le_projectionGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.directedProjectionGap V ≤ U.projectionGap V := by
  have hcomp : Vᗮ.starProjection ∘L U.starProjection =
      (U.starProjection - V.starProjection) ∘L U.starProjection := by
    ext x
    simp only [ContinuousLinearMap.comp_apply, sub_apply]
    rw [Submodule.starProjection_orthogonal_apply V (U.starProjection x)]
    rw [show U.starProjection (U.starProjection x) = U.starProjection x by
      exact Submodule.starProjection_eq_self_iff.mpr
        (U.starProjection_apply_mem x)]
  have hP : ‖U.starProjection‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simpa using U.norm_starProjection_apply_le x
  unfold directedProjectionGap projectionGap
  rw [hcomp]
  calc
    ‖(U.starProjection - V.starProjection) ∘L U.starProjection‖
        ≤ ‖U.starProjection - V.starProjection‖ * ‖U.starProjection‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖U.starProjection - V.starProjection‖ * 1 :=
      mul_le_mul_of_nonneg_left hP (norm_nonneg _)
    _ = ‖U.starProjection - V.starProjection‖ := mul_one _

/-- The directed gap never exceeds one: it is the norm of a composition of two
orthogonal projections, each a contraction. -/
theorem directedProjectionGap_le_one (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.directedProjectionGap V ≤ 1 := by
  change ‖Vᗮ.starProjection ∘L U.starProjection‖ ≤ 1
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, ContinuousLinearMap.comp_apply]
  exact (Vᗮ.norm_starProjection_apply_le _).trans (U.norm_starProjection_apply_le x)

/-- A subspace has no directed gap towards a subspace containing it. -/
theorem directedProjectionGap_eq_zero_of_le {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ≤ V) :
    U.directedProjectionGap V = 0 := by
  have hzero : Vᗮ.starProjection ∘L U.starProjection = 0 := by
    ext x
    change Vᗮ.starProjection (U.starProjection x) = 0
    rw [Submodule.starProjection_apply_eq_zero_iff Vᗮ]
    exact Submodule.le_orthogonal_orthogonal V (h (U.starProjection_apply_mem x))
  change ‖Vᗮ.starProjection ∘L U.starProjection‖ = 0
  rw [hzero, norm_zero]

/-- **A nonzero crossed intersection pins the directed gap at one.**

A vector of `U ⊓ Vᗮ` is fixed by `P_U` and by `P_{Vᗮ}`, hence by their
composite, so the directed gap attains its maximum.  This is the "defect
block contributes the singular value `1`" half of the Halmos picture, and it
needs no decomposition to state or to prove. -/
theorem directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : U ⊓ Vᗮ ≠ ⊥) :
    U.directedProjectionGap V = 1 := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  obtain ⟨hxU, hxV⟩ := Submodule.mem_inf.mp hx
  refine le_antisymm (directedProjectionGap_le_one U V) ?_
  have happ : (Vᗮ.starProjection ∘L U.starProjection) x = x := by
    rw [ContinuousLinearMap.comp_apply, Submodule.starProjection_eq_self_iff.mpr hxU,
      Submodule.starProjection_eq_self_iff.mpr hxV]
  have hle : ‖x‖ ≤ U.directedProjectionGap V * ‖x‖ := by
    have hop := ContinuousLinearMap.le_opNorm
      (Vᗮ.starProjection ∘L U.starProjection) x
    rwa [happ] at hop
  exact le_of_mul_le_mul_right (by linarith) (norm_pos_iff.mpr hx0)

end Submodule

variable [CompleteSpace E]

/-! ### The sharp projector-difference norm identity

`‖P − Q‖ = max(‖(1−Q)P‖, ‖(1−P)Q‖)` for orthogonal projections, via the block
decomposition `(P−Q)² = P(1−Q)P + (1−P)Q(1−P)` and the C\*-norm identities.  This
is the two-projection fact that upgrades two one-sided `sin Θ` estimates to the
*sharp* (factor-one) projector-difference bound, without any equal-rank
hypothesis.  The proof uses the `RCLike` Hilbert-space star structure and is scalar-generic.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `df036cd`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/


namespace ContinuousLinearMap

/-- **A block-diagonal sum has the max of the two norms.**  If `P` is an
orthogonal projection, `A` lives on its range on both sides (`A P = P A = A`) and
`B` is annihilated by it on both sides (`B P = P B = 0`), then `A` and `B` act on
orthogonal blocks and `‖A + B‖ = max ‖A‖ ‖B‖`. -/
theorem norm_add_eq_max_of_block {P A B : E →L[𝕜] E}
    (hPsa : IsSelfAdjoint P) (hPid : IsIdempotentElem P)
    (hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖) (hcompnorm : ∀ x, ‖(1 - P) x‖ ≤ ‖x‖)
    (hAP : A * P = A) (hPA : P * A = A) (hBP : B * P = 0) (hPB : P * B = 0) :
    ‖A + B‖ = max ‖A‖ ‖B‖ := by
  have hPsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hPsa
  have hPsymC : ∀ x y, ⟪P x, y⟫_𝕜 = ⟪x, P y⟫_𝕜 := fun x y => hPsym x y
  have app : ∀ (f g : E →L[𝕜] E) (x : E), (f * g) x = f (g x) := fun _ _ _ => rfl
  have hAppx : ∀ x, A (P x) = A x := fun x => by
    rw [← app]; exact congrFun (congrArg DFunLike.coe hAP) x
  have hPArange : ∀ x, P (A x) = A x := fun x => by
    rw [← app]; exact congrFun (congrArg DFunLike.coe hPA) x
  have hPBker : ∀ x, P (B x) = 0 := fun x => by
    rw [← app]; have h := congrFun (congrArg DFunLike.coe hPB) x; simpa using h
  have hBPx : ∀ x, B (P x) = 0 := fun x => by
    rw [← app]; have h := congrFun (congrArg DFunLike.coe hBP) x; simpa using h
  have hBcpx : ∀ x, B ((1 - P) x) = B x := fun x => by
    have hb : B * (1 - P) = B := by rw [mul_sub, mul_one, hBP, sub_zero]
    rw [← app]; exact congrFun (congrArg DFunLike.coe hb) x
  have hPcx : ∀ x, P ((1 - P) x) = 0 := fun x => by
    have h0 : P * (1 - P) = 0 := by rw [mul_sub, mul_one, hPid, sub_self]
    rw [← app]; have h := congrFun (congrArg DFunLike.coe h0) x; simpa using h
  have hApx : ∀ x, A ((1 - P) x) = 0 := fun x => by
    have h0 : A * (1 - P) = 0 := by rw [mul_sub, mul_one, hAP, sub_self]
    rw [← app]; have h := congrFun (congrArg DFunLike.coe h0) x; simpa using h
  have hpyth : ∀ x, ‖P x‖ ^ 2 + ‖(1 - P) x‖ ^ 2 = ‖x‖ ^ 2 := fun x => by
    have horth : ⟪P x, (1 - P) x⟫_𝕜 = 0 := by rw [hPsymC x ((1 - P) x), hPcx, inner_zero_right]
    have h := norm_add_sq (𝕜 := 𝕜) (P x) ((1 - P) x)
    rw [show P x + (1 - P) x = x by
      rw [sub_apply, one_apply_eq_self]; abel] at h
    simp only [horth, map_zero, mul_zero, add_zero] at h
    linarith
  refine le_antisymm ?_ ?_
  · refine ContinuousLinearMap.opNorm_le_bound _ (le_max_of_le_left (norm_nonneg _)) fun x => ?_
    have horthAB : ⟪A x, B x⟫_𝕜 = 0 := by
      rw [← hPArange x, hPsymC (A x) (B x), hPBker, inner_zero_right]
    have hnormsq : ‖(A + B) x‖ ^ 2 = ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := by
      have h := norm_add_sq (𝕜 := 𝕜) (A x) (B x)
      simp only [horthAB, map_zero, mul_zero, add_zero] at h
      simp only [add_apply]; linarith
    have hAxle : ‖A x‖ ≤ max ‖A‖ ‖B‖ * ‖P x‖ := by
      rw [← hAppx x]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact le_max_left _ _)
    have hBxle : ‖B x‖ ≤ max ‖A‖ ‖B‖ * ‖(1 - P) x‖ := by
      rw [← hBcpx x]
      exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact le_max_right _ _)
    have hM : (0:ℝ) ≤ max ‖A‖ ‖B‖ := le_max_of_le_left (norm_nonneg _)
    have hkey : ‖(A + B) x‖ ^ 2 ≤ (max ‖A‖ ‖B‖ * ‖x‖) ^ 2 := by
      have e : (max ‖A‖ ‖B‖ * ‖x‖) ^ 2
          = (max ‖A‖ ‖B‖)^2 * ‖P x‖^2 + (max ‖A‖ ‖B‖)^2 * ‖(1 - P) x‖^2 := by
        rw [mul_pow, ← hpyth x]; ring
      rw [hnormsq, e]
      gcongr
      · simpa only [mul_pow] using
          (sq_le_sq₀ (norm_nonneg (A x))
            (mul_nonneg hM (norm_nonneg (P x)))).2 hAxle
      · simpa only [mul_pow] using
          (sq_le_sq₀ (norm_nonneg (B x))
            (mul_nonneg hM (norm_nonneg ((1 - P) x)))).2 hBxle
    have hnn : (0:ℝ) ≤ max ‖A‖ ‖B‖ * ‖x‖ := mul_nonneg hM (norm_nonneg x)
    calc ‖(A + B) x‖ = Real.sqrt (‖(A + B) x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((max ‖A‖ ‖B‖ * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hkey
      _ = max ‖A‖ ‖B‖ * ‖x‖ := Real.sqrt_sq hnn
  · refine max_le ?_ ?_
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      have hval : A x = (A + B) (P x) := by
        rw [add_apply, hBPx, add_zero, hAppx]
      rw [hval]; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hPnorm x)
    · refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
      have hval : B x = (A + B) ((1 - P) x) := by
        rw [add_apply, hApx, zero_add, hBcpx]
      rw [hval]; exact (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hcompnorm x)


end ContinuousLinearMap

namespace Submodule

/-- **The gap between two subspaces is the max of the two one-sided defects.**
`‖P_U - P_V‖` equals the larger of `‖(1 - P_V) P_U‖` and `‖(1 - P_U) P_V‖` — the
norms of the parts of each subspace that the other does not see.  This is the
identity behind the two-sided form of the sin-Θ theorem. -/
theorem norm_starProjection_sub_eq_max (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖(U.starProjection - V.starProjection : E →L[𝕜] E)‖ =
      max ‖(1 - V.starProjection) ∘L U.starProjection‖
          ‖(1 - U.starProjection) ∘L V.starProjection‖ := by
  set P := U.starProjection with hPdef
  set Q := V.starProjection with hQdef
  have hPsa : IsSelfAdjoint P := isSelfAdjoint_starProjection U
  have hQsa : IsSelfAdjoint Q := isSelfAdjoint_starProjection V
  have hPid : P * P = P := U.isIdempotentElem_starProjection
  have hQid : Q * Q = Q := V.isIdempotentElem_starProjection
  have hPnorm : ∀ x, ‖P x‖ ≤ ‖x‖ := U.norm_starProjection_apply_le
  have hcompeq : (1 - P : E →L[𝕜] E) = Uᗮ.starProjection := by
    rw [hPdef]; exact (Submodule.starProjection_orthogonal' U).symm
  have hcompnorm : ∀ x, ‖(1 - P) x‖ ≤ ‖x‖ := fun x => by
    rw [hcompeq]; exact Uᗮ.norm_starProjection_apply_le x
  set X : E →L[𝕜] E := (1 - Q) * P with hXdef
  set Y : E →L[𝕜] E := (1 - P) * Q with hYdef
  set A : E →L[𝕜] E := P * (1 - Q) * P with hAdef
  set B : E →L[𝕜] E := (1 - P) * Q * (1 - P) with hBdef
  have hQ1id : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [mul_sub, mul_one, sub_mul, one_mul, hQid]; abel
  have hstarX : star X = P * (1 - Q) := by
    rw [hXdef, star_mul, hPsa.star_eq, star_sub, star_one, hQsa.star_eq]
  have hstarY : star Y = Q * (1 - P) := by
    rw [hYdef, star_mul, hQsa.star_eq, star_sub, star_one, hPsa.star_eq]
  have hnormA : ‖A‖ = ‖X‖ ^ 2 := by
    have h : star X * X = A := by
      rw [hstarX, hXdef, hAdef,
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        show (P * (1 - Q)) * ((1 - Q) * P) = P * ((1 - Q) * (1 - Q)) * P by noncomm_ring, hQ1id]
    calc
      ‖A‖ = ‖star X * X‖ := congrArg (fun T : E →L[𝕜] E => ‖T‖) h.symm
      _ = ‖X‖ * ‖X‖ := CStarRing.norm_star_mul_self
      _ = ‖X‖ ^ 2 := by rw [pow_two]
  have hnormB : ‖B‖ = ‖Y‖ ^ 2 := by
    have hQP : Q * Q = Q := hQid
    have h : Y * star Y = B := by
      rw [hstarY, hYdef, hBdef,
        -- states the goal with the definition unfolded, in the shape the next step needs;
        -- there is no `_apply` lemma to rewrite with here.
        show ((1 - P) * Q) * (Q * (1 - P)) = (1 - P) * (Q * Q) * (1 - P) by noncomm_ring, hQP]
    calc
      ‖B‖ = ‖Y * star Y‖ := congrArg (fun T : E →L[𝕜] E => ‖T‖) h.symm
      _ = ‖Y‖ * ‖Y‖ := CStarRing.norm_self_mul_star
      _ = ‖Y‖ ^ 2 := by rw [pow_two]
  have hAP : A * P = A := by rw [hAdef, mul_assoc, hPid]
  have hPA : P * A = A := by rw [hAdef, ← mul_assoc, ← mul_assoc, hPid]
  have hBP : B * P = 0 := by
    rw [hBdef, mul_assoc, show (1 - P) * P = 0 by rw [sub_mul, one_mul, hPid, sub_self], mul_zero]
  have hPB : P * B = 0 := by
    simp only [hBdef, ← mul_assoc,
      show P * (1 - P) = 0 by rw [mul_sub, mul_one, hPid, sub_self], zero_mul]
  have hA' : A = P - P * Q * P := by rw [hAdef, mul_sub, mul_one, sub_mul, hPid]
  have hB' : B = Q - Q * P - P * Q + P * Q * P := by
    simp only [hBdef, sub_mul, one_mul, mul_sub, mul_one]; abel
  have hPQsq : (P - Q) * (P - Q) = A + B := by
    have lhs : (P - Q) * (P - Q) = P + Q - P * Q - Q * P := by
      rw [sub_mul, mul_sub, mul_sub, hPid, hQid]; abel
    rw [lhs, hA', hB']; abel
  have hnormPQ : ‖(P - Q) * (P - Q)‖ = ‖P - Q‖ ^ 2 := by
    exact (hPsa.sub hQsa).norm_mul_self
  have hblock : ‖A + B‖ = max ‖A‖ ‖B‖ :=
    ContinuousLinearMap.norm_add_eq_max_of_block hPsa hPid hPnorm hcompnorm hAP hPA hBP hPB
  have hsq : ‖(P - Q : E →L[𝕜] E)‖ ^ 2 = (max ‖X‖ ‖Y‖) ^ 2 := by
    rw [← hnormPQ, hPQsq, hblock, hnormA, hnormB]
    rcases le_total ‖X‖ ‖Y‖ with h | h
    · rw [max_eq_right h, max_eq_right (by gcongr)]
    · rw [max_eq_left h, max_eq_left (by gcongr)]
  have hfin : ‖(P - Q : E →L[𝕜] E)‖ = max ‖X‖ ‖Y‖ := by
    have h2 : (0 : ℝ) ≤ max ‖X‖ ‖Y‖ := le_max_of_le_left (norm_nonneg _)
    exact (sq_eq_sq₀ (norm_nonneg (P - Q : E →L[𝕜] E)) h2).mp hsq
  rw [hfin]
  rfl

/-- **The projection gap is the larger of the two directed gaps.**

The gap-level reading of `norm_starProjection_sub_eq_max`: `projectionGap` is symmetric in
its arguments, so it cannot see which of the two subspaces carries the defect, and this
identity says the symmetric quantity is exactly the worse of the two directed ones.

Stated here rather than derived at each use site.  It had been unfolded inline three times
-- twice in the Davis--Kahan sine theory and once in `AngleGeometry` -- at six lines each,
which is what a missing lemma looks like. -/
theorem projectionGap_eq_max_directedProjectionGap (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.projectionGap V = max (U.directedProjectionGap V) (V.directedProjectionGap U) := by
  change ‖U.starProjection - V.starProjection‖ =
    max ‖Vᗮ.starProjection ∘L U.starProjection‖
      ‖Uᗮ.starProjection ∘L V.starProjection‖
  rw [Submodule.norm_starProjection_sub_eq_max,
    Submodule.starProjection_orthogonal' V,
    Submodule.starProjection_orthogonal' U]

/-! ### When the two directed gaps agree

The directed gap is genuinely asymmetric: `U = ⊤`, `V` a proper subspace has
`U.directedProjectionGap V = 1` and `V.directedProjectionGap U = 0`.  The three
results below isolate exactly what removes the asymmetry, and it is the pair of
*crossed intersections* `U ⊓ Vᗮ` and `Uᗮ ⊓ V` — Davis--Kahan 1970's Section 3
standing assumption (3.5) in its qualitative form.

The engine is `directedProjectionGap_le_of_inf_orthogonal_eq_bot`, and its proof
is two lines of Cauchy--Schwarz plus one density argument, with no Halmos
decomposition and no spectral theory:

* writing `c` for `√(1 - ‖P_{Vᗮ} P_U‖²)`, Pythagoras turns the directed bound
  into `c ‖u‖ ≤ ‖P_V u‖` for every `u ∈ U`;
* for `u ∈ U` and `a = P_V u`, `⟪P_U a, u⟫ = ⟪a, a⟫`, so Cauchy--Schwarz gives
  `‖a‖² ≤ ‖P_U a‖ ‖u‖`, and dividing by `‖u‖` propagates the same constant to
  `a`: `c ‖a‖ ≤ ‖P_U a‖`;
* `P_V '' U` is dense in `V` when `Uᗮ ⊓ V = ⊥`, and `c ‖x‖ ≤ ‖P_U x‖` is a
  closed condition, so the bound holds on all of `V`, which is the reverse
  directed estimate.

Only one crossed intersection is used per direction, and only through
`Uᗮ ⊓ V = ⊥`; that asymmetry is what makes the combined hypothesis an
if-and-only-if rather than a conjunction. -/

/-- **One vanishing crossed intersection reverses the directed gap estimate.**

If `Uᗮ ⊓ V = ⊥` then `‖P_{Uᗮ} P_V‖ ≤ ‖P_{Vᗮ} P_U‖`.  Geometrically: with no
part of `V` orthogonal to `U`, the image `P_V '' U` is dense in `V`, and the
worst tilt of `V` away from `U` is already witnessed by the tilt of `U` away
from `V`. -/
theorem directedProjectionGap_le_of_inf_orthogonal_eq_bot (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (h : Uᗮ ⊓ V = ⊥) :
    V.directedProjectionGap U ≤ U.directedProjectionGap V := by
  set t := U.directedProjectionGap V with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht1 : t ≤ 1 := U.directedProjectionGap_le_one V
  have hk0 : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
  set c := Real.sqrt (1 - t ^ 2) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hcsq : c ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hk0
  -- Pythagoras turns the directed bound into a lower bound for `P_V` on `U`.
  have hstep1 : ∀ u ∈ U, c * ‖u‖ ≤ ‖V.starProjection u‖ := by
    intro u hu
    have hperp : ‖Vᗮ.starProjection u‖ ≤ t * ‖u‖ := by
      have hop := ContinuousLinearMap.le_opNorm
        (Vᗮ.starProjection ∘L U.starProjection) u
      rwa [ContinuousLinearMap.comp_apply,
        Submodule.starProjection_eq_self_iff.mpr hu] at hop
    have hpy : ‖u‖ ^ 2 = ‖V.starProjection u‖ ^ 2 + ‖Vᗮ.starProjection u‖ ^ 2 :=
      V.norm_sq_eq_add_norm_sq_starProjection u
    have hsq : (c * ‖u‖) ^ 2 ≤ ‖V.starProjection u‖ ^ 2 := by
      have hsqperp : ‖Vᗮ.starProjection u‖ ^ 2 ≤ (t * ‖u‖) ^ 2 := by
        nlinarith [norm_nonneg (Vᗮ.starProjection u),
          mul_nonneg ht0 (norm_nonneg u)]
      have hexpand : (c * ‖u‖) ^ 2 = ‖u‖ ^ 2 - (t * ‖u‖) ^ 2 := by
        rw [mul_pow, mul_pow, hcsq]; ring
      rw [hexpand]
      linarith
    calc c * ‖u‖ = Real.sqrt ((c * ‖u‖) ^ 2) :=
          (Real.sqrt_sq (mul_nonneg hc0 (norm_nonneg u))).symm
      _ ≤ Real.sqrt (‖V.starProjection u‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖V.starProjection u‖ := Real.sqrt_sq (norm_nonneg _)
  -- The same constant propagates to the image `P_V '' U` by Cauchy--Schwarz.
  set S : Submodule 𝕜 E := U.map (V.starProjection : E →ₗ[𝕜] E) with hS
  set T : Set E := {x : E | c * ‖x‖ ≤ ‖U.starProjection x‖} with hT
  have hTclosed : IsClosed T :=
    isClosed_le (continuous_const.mul continuous_norm)
      (continuous_norm.comp U.starProjection.continuous)
  have hST : (S : Set E) ⊆ T := by
    rintro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    change c * ‖V.starProjection u‖ ≤ ‖U.starProjection (V.starProjection u)‖
    rcases eq_or_ne (V.starProjection u) 0 with h0 | h0
    · rw [h0]; simp
    have hunorm : 0 < ‖u‖ := by
      refine norm_pos_iff.mpr fun huz => h0 ?_
      rw [huz, map_zero]
    have hzero : ⟪V.starProjection u, u - V.starProjection u⟫_𝕜 = 0 :=
      inner_eq_zero_symm.mp
        (V.starProjection_inner_eq_zero u _ (V.starProjection_apply_mem u))
    have hself : ⟪V.starProjection u, u⟫_𝕜
        = ⟪V.starProjection u, V.starProjection u⟫_𝕜 := by
      have hsub := inner_sub_right (𝕜 := 𝕜) (V.starProjection u) u (V.starProjection u)
      rw [hzero] at hsub
      exact sub_eq_zero.mp hsub.symm
    have hmove : ⟪U.starProjection (V.starProjection u), u⟫_𝕜
        = ⟪V.starProjection u, V.starProjection u⟫_𝕜 := by
      rw [Submodule.inner_starProjection_left_eq_right U,
        Submodule.starProjection_eq_self_iff.mpr hu, hself]
    have hcs : ‖V.starProjection u‖ * ‖V.starProjection u‖
        ≤ ‖U.starProjection (V.starProjection u)‖ * ‖u‖ := by
      have hbound := norm_inner_le_norm (𝕜 := 𝕜)
        (U.starProjection (V.starProjection u)) u
      have hnormself : ‖⟪V.starProjection u, V.starProjection u⟫_𝕜‖
          = ‖V.starProjection u‖ * ‖V.starProjection u‖ := by
        rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
          abs_of_nonneg (norm_nonneg _), sq]
      rwa [hmove, hnormself] at hbound
    have hlow : c * ‖u‖ * ‖V.starProjection u‖
        ≤ ‖V.starProjection u‖ * ‖V.starProjection u‖ :=
      mul_le_mul_of_nonneg_right (hstep1 u hu) (norm_nonneg _)
    nlinarith [hcs, hlow, hunorm, norm_pos_iff.mpr h0]
  -- `P_V '' U` is dense in `V` precisely because `Uᗮ ⊓ V = ⊥`.
  have hVle : V ≤ Sᗮᗮ := by
    intro v hv
    rw [Submodule.mem_orthogonal]
    intro y hy
    have hy' := (Submodule.mem_orthogonal S y).mp hy
    have hyV : V.starProjection y = 0 := by
      have hmem : V.starProjection y ∈ Uᗮ ⊓ V := by
        refine Submodule.mem_inf.mpr ⟨?_, V.starProjection_apply_mem y⟩
        rw [Submodule.mem_orthogonal]
        intro u hu
        have hzu : ⟪V.starProjection u, y⟫_𝕜 = 0 :=
          hy' (V.starProjection u) (Submodule.mem_map_of_mem hu)
        rwa [Submodule.inner_starProjection_left_eq_right] at hzu
      rw [h] at hmem
      simpa using hmem
    have hyperp : y ∈ Vᗮ := (Submodule.starProjection_apply_eq_zero_iff V).mp hyV
    exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal V y).mp hyperp v hv)
  have hstep3 : ∀ v ∈ V, c * ‖v‖ ≤ ‖U.starProjection v‖ := by
    intro v hv
    have hmem : v ∈ closure (S : Set E) := by
      have hvv := hVle hv
      rwa [Submodule.orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe,
        Submodule.topologicalClosure_coe] at hvv
    exact hTclosed.closure_subset_iff.mpr hST hmem
  -- Reversing Pythagoras on `V` is the reverse directed estimate.
  change ‖Uᗮ.starProjection ∘L V.starProjection‖ ≤ t
  refine ContinuousLinearMap.opNorm_le_bound _ ht0 fun x => ?_
  rw [ContinuousLinearMap.comp_apply]
  have hv : V.starProjection x ∈ V := V.starProjection_apply_mem x
  have hpy : ‖V.starProjection x‖ ^ 2
      = ‖U.starProjection (V.starProjection x)‖ ^ 2
        + ‖Uᗮ.starProjection (V.starProjection x)‖ ^ 2 :=
    U.norm_sq_eq_add_norm_sq_starProjection _
  have hlow := hstep3 _ hv
  have hvx : ‖V.starProjection x‖ ≤ ‖x‖ := V.norm_starProjection_apply_le x
  have hsq : ‖Uᗮ.starProjection (V.starProjection x)‖ ^ 2 ≤ (t * ‖x‖) ^ 2 := by
    have hc2 : (c * ‖V.starProjection x‖) ^ 2
        ≤ ‖U.starProjection (V.starProjection x)‖ ^ 2 := by
      nlinarith [norm_nonneg (U.starProjection (V.starProjection x)),
        mul_nonneg hc0 (norm_nonneg (V.starProjection x))]
    have hexpand : (c * ‖V.starProjection x‖) ^ 2
        = ‖V.starProjection x‖ ^ 2 - (t * ‖V.starProjection x‖) ^ 2 := by
      rw [mul_pow, mul_pow, hcsq]; ring
    have hmono : (t * ‖V.starProjection x‖) ^ 2 ≤ (t * ‖x‖) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hvx ht0
      nlinarith [mul_nonneg ht0 (norm_nonneg (V.starProjection x))]
    rw [hexpand] at hc2
    linarith
  calc ‖Uᗮ.starProjection (V.starProjection x)‖
      = Real.sqrt (‖Uᗮ.starProjection (V.starProjection x)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((t * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = t * ‖x‖ := Real.sqrt_sq (mul_nonneg ht0 (norm_nonneg x))

/-- **The two directed gaps agree exactly when the crossed intersections vanish
together.**

The hypothesis is the qualitative content of Davis--Kahan 1970's standing
assumption (3.5): *one* crossed defect is trivial if and only if the other is.
It is strictly weaker than assuming both vanish, and strictly weaker than an
equality of dimensions; it is what the norm statement actually consumes.

Both branches are elementary.  When both crossed intersections vanish, the two
applications of `directedProjectionGap_le_of_inf_orthogonal_eq_bot` are the two
inequalities.  When neither vanishes, both directed gaps are pinned at `1` by
`directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot`. -/
theorem directedProjectionGap_comm_of_inf_orthogonal_eq_bot_iff (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U ⊓ Vᗮ = ⊥ ↔ Uᗮ ⊓ V = ⊥) :
    U.directedProjectionGap V = V.directedProjectionGap U := by
  by_cases hb : U ⊓ Vᗮ = ⊥
  · have hb' : Uᗮ ⊓ V = ⊥ := h.mp hb
    refine le_antisymm
      (V.directedProjectionGap_le_of_inf_orthogonal_eq_bot U (by rwa [inf_comm] at hb)) ?_
    exact U.directedProjectionGap_le_of_inf_orthogonal_eq_bot V hb'
  · have hb' : Uᗮ ⊓ V ≠ ⊥ := fun hc => hb (h.mpr hc)
    rw [U.directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot V hb,
      V.directedProjectionGap_eq_one_of_inf_orthogonal_ne_bot U
        (by rwa [inf_comm] at hb')]

/-- **The symmetric gap is the directed gap under the crossed-defect
hypothesis.**

`projectionGap` is the maximum of the two directed gaps, so once they agree it
is either one of them.  This is the identification Davis--Kahan use to read a
directed `sin Θ` estimate as a statement about `‖P_U - P_V‖`, and it is the
place their Section 3 standing assumption enters. -/
theorem projectionGap_eq_directedProjectionGap_of_inf_orthogonal_eq_bot_iff
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : U ⊓ Vᗮ = ⊥ ↔ Uᗮ ⊓ V = ⊥) :
    U.projectionGap V = U.directedProjectionGap V := by
  rw [U.projectionGap_eq_max_directedProjectionGap V,
    ← U.directedProjectionGap_comm_of_inf_orthogonal_eq_bot_iff V h, max_self]


end Submodule
