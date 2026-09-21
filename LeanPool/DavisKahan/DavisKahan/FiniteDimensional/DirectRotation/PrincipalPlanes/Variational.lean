/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DirectRotation.PrincipalPlanes.Spectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CourantFischer
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm

/-!
# Davis's variational theorem for the restricted displacement

Davis 1958, Theorem 7.2 (= Davis--Kahan 1970, Proposition 4.1): among all
unitaries `W` carrying `U` onto `V`, the direct rotation minimizes every
singular value of the restricted displacement `(I - W) P_U` — pointwise, over
any `RCLike` field, and with no largest-angle threshold.  (`IsAcute` is
standing throughout: it is the hypothesis under which the direct rotation
exists, not a restriction on the conclusion.)  The main results are

* `principalPlaneChord_le_singularValues_restrictedDisplacement` (lower bound),
* `singularValues_restrictedDisplacement_directRotation` (closed form for `R`),
* `singularValues_restrictedDisplacement_le` (pointwise minimality),
* `kyFanSum_restrictedDisplacement_le` and `uiNorm_restrictedDisplacement_le`
  (Davis--Kahan Corollary 4.1).
-/

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ## Davis's variational theorem for the restricted displacement

Davis 1958, Theorem 7.2 (= Davis--Kahan 1970, Proposition 4.1): among all
unitaries `W` carrying `U` onto `V`, the direct rotation minimizes every
singular value of the restricted displacement `(I - W) P_U` — pointwise, over
any `RCLike` field, and with no largest-angle threshold.  The proof is the minimax
argument: for a unit vector `x ∈ U`, the image `W x` is a *unit* vector of
`V`, so `‖x - W x‖² ≥ 2 - 2 ‖P_V x‖`, and on the span of the top source
vectors the cosine bound `‖P_V x‖ ≤ c_j` is uniform. -/

omit [FiniteDimensional 𝕜 E] in
/-- Squared norms of orthonormal combinations. -/
private theorem norm_sq_sum_smul_orthonormal
    {ι : Type*} [Fintype ι] {w : ι → E} (hw : Orthonormal 𝕜 w) (β : ι → 𝕜) :
    ‖∑ a, β a • w a‖ ^ 2 = ∑ a, ‖β a‖ ^ 2 := by
  classical
  have hinner : ⟪∑ a, β a • w a, ∑ a, β a • w a⟫_𝕜 =
      ((∑ a, ‖β a‖ ^ 2 : ℝ) : 𝕜) := by
    rw [sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_smul_left, inner_sum]
    rw [Finset.sum_eq_single a]
    · rw [inner_smul_right, orthonormal_iff_ite.mp hw a a, ite_eq_left rfl, mul_one,
        RCLike.conj_mul]
    · intro c _ hca
      rw [inner_smul_right, orthonormal_iff_ite.mp hw a c,
        ite_eq_right (fun h => hca h.symm), mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  have := congrArg RCLike.re hinner
  rwa [← norm_sq_eq_re_inner, RCLike.ofReal_re] at this

/-- **Davis 1958 Theorem 7.2 / Davis--Kahan Proposition 4.1** (lower bound):
for every unitary `W` carrying `U` onto `V`, the `i`-th singular value of the
restricted displacement `(I - W) ∘ P_U` is at least the `i`-th principal
chord. -/
theorem principalPlaneChord_le_singularValues_restrictedDisplacement
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V)
    (i : Fin (nontrivialAngleCount U V)) :
    principalPlaneChord U V i ≤
      ((LinearMap.id - W.toLinearMap) ∘ₗ projection U).singularValues (i : ℕ) := by
  classical
  set AW := (LinearMap.id - W.toLinearMap) ∘ₗ projection U with hAW
  have hiE : (i : ℕ) < finrank 𝕜 E :=
    lt_of_lt_of_le i.isLt (nontrivialAngleCount_le_finrank U V)
  -- The span of the top `i+1` source vectors.
  set u' : Fin ((i : ℕ) + 1) → E := fun a =>
    principalSourceVector U V (Fin.castLE (by omega) a) with hu'
  have hu'on : Orthonormal 𝕜 u' :=
    (orthonormal_principalSourceVector U V).comp _
      (Fin.castLE_injective (by omega))
  set L : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range u') with hL
  have hLdim : finrank 𝕜 L = (i : ℕ) + 1 := by
    rw [hL, finrank_span_eq_card hu'on.linearIndependent, Fintype.card_fin]
  have hLU : L ≤ U := by
    rw [hL, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact principalSourceVector_mem U V hacute _
  -- Courant–Fischer gives a unit test vector in `L`.
  obtain ⟨x, hxL, hxnorm, hxbound⟩ :=
    LinearMap.IsSymmetric.exists_unit_vector_re_inner_le_eigenvalue
      AW.isSymmetric_adjoint_comp_self rfl ⟨(i : ℕ), hiE⟩ L hLdim
  -- The quadratic form at `x` is the squared displacement of `x`.
  have hform : RCLike.re ⟪(AW.adjoint ∘ₗ AW) x, x⟫_𝕜 = ‖x - W x‖ ^ 2 := by
    have hxU : x ∈ U := hLU hxL
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    rw [← norm_sq_eq_re_inner]
    congr 2
    rw [hAW, LinearMap.comp_apply, projection_apply_of_mem hxU,
      LinearMap.sub_apply, LinearMap.id_apply]
    rfl
  -- Lower bound for the displacement on `L`.
  have hdisp : principalPlaneChord U V i ^ 2 ≤ ‖x - W x‖ ^ 2 := by
    have hxU : x ∈ U := hLU hxL
    -- Coefficients of `x` in the orthonormal family.
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hxL
    -- Norm of `x`.
    have hxnorm2 : ∑ a, ‖β a‖ ^ 2 = 1 := by
      have := norm_sq_sum_smul_orthonormal hu'on β
      rw [hβ, hxnorm] at this
      simpa using this.symm
    -- `P_V x` in the rotated orthonormal family.
    have hPV : projection V x = ∑ a,
        (β a * (principalPlaneCosine U V (Fin.castLE (by omega) a) : 𝕜)) •
          directRotation U V hacute (u' a) := by
      rw [← hβ, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, hu',
        projection_apply_principalSourceVector U V hacute _, smul_smul]
    have hRon : Orthonormal 𝕜 (fun a => directRotation U V hacute (u' a)) := by
      rw [orthonormal_iff_ite]
      intro a c
      rw [(directRotation U V hacute).inner_map_map]
      exact orthonormal_iff_ite.mp hu'on a c
    have hPVnorm : ‖projection V x‖ ^ 2 = ∑ a,
        ‖β a * (principalPlaneCosine U V (Fin.castLE (by omega) a) : 𝕜)‖ ^ 2 := by
      rw [hPV]
      exact norm_sq_sum_smul_orthonormal hRon _
    -- Uniform cosine bound on the span.
    have hcos : ‖projection V x‖ ^ 2 ≤ principalPlaneCosine U V i ^ 2 := by
      rw [hPVnorm]
      calc ∑ a, ‖β a * (principalPlaneCosine U V (Fin.castLE (by omega) a) : 𝕜)‖ ^ 2
          ≤ ∑ a, principalPlaneCosine U V i ^ 2 * ‖β a‖ ^ 2 := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [norm_mul, mul_pow, RCLike.norm_ofReal]
            have hmono : principalPlaneCosine U V (Fin.castLE (by omega) a) ≤
                principalPlaneCosine U V i := by
              apply principalPlaneCosine_monotone
              simp only [Fin.le_def, Fin.val_castLE]
              omega
            have h0 : 0 ≤ principalPlaneCosine U V (Fin.castLE (by omega) a) :=
              Real.sqrt_nonneg _
            calc ‖β a‖ ^ 2 * |principalPlaneCosine U V (Fin.castLE (by omega) a)| ^ 2
                = |principalPlaneCosine U V (Fin.castLE (by omega) a)| ^ 2 * ‖β a‖ ^ 2 := by
                  ring
              _ ≤ principalPlaneCosine U V i ^ 2 * ‖β a‖ ^ 2 := by
                  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
                  rw [abs_of_nonneg h0]
                  exact pow_le_pow_left₀ h0 hmono 2
        _ = principalPlaneCosine U V i ^ 2 := by
            rw [← Finset.mul_sum, hxnorm2, mul_one]
    have hPVle : ‖projection V x‖ ≤ principalPlaneCosine U V i := by
      have h0 : 0 ≤ principalPlaneCosine U V i := Real.sqrt_nonneg _
      nlinarith [norm_nonneg (projection V x)]
    -- `W x` is a unit vector of `V`.
    have hWxV : W x ∈ V := by
      rw [← hmap]
      exact ⟨x, hxU, rfl⟩
    have hWxnorm : ‖W x‖ = 1 := by rw [W.norm_map, hxnorm]
    -- Expand the squared displacement.
    have hre : RCLike.re ⟪x, W x⟫_𝕜 ≤ principalPlaneCosine U V i := by
      have h1 : ⟪x, W x⟫_𝕜 = ⟪projection V x, W x⟫_𝕜 := by
        rw [projection_inner_left_eq_right, projection_apply_of_mem hWxV]
      calc RCLike.re ⟪x, W x⟫_𝕜 = RCLike.re ⟪projection V x, W x⟫_𝕜 := by rw [h1]
        _ ≤ ‖⟪projection V x, W x⟫_𝕜‖ := RCLike.re_le_norm _
        _ ≤ ‖projection V x‖ * ‖W x‖ := norm_inner_le_norm _ _
        _ = ‖projection V x‖ := by rw [hWxnorm, mul_one]
        _ ≤ principalPlaneCosine U V i := hPVle
    have hexpand : ‖x - W x‖ ^ 2 = 2 - 2 * RCLike.re ⟪x, W x⟫_𝕜 := by
      rw [@norm_sub_sq 𝕜, hxnorm, hWxnorm]
      norm_num
      ring
    rw [hexpand, principalPlaneChord_sq]
    linarith
  -- Assemble.
  have hσ := AW.singularValues_of_lt rfl hiE
  rw [hσ]
  have hbound : principalPlaneChord U V i ^ 2 ≤
      AW.isSymmetric_adjoint_comp_self.eigenvalues rfl ⟨(i : ℕ), hiE⟩ := by
    calc principalPlaneChord U V i ^ 2 ≤ ‖x - W x‖ ^ 2 := hdisp
      _ = RCLike.re ⟪(AW.adjoint ∘ₗ AW) x, x⟫_𝕜 := hform.symm
      _ ≤ _ := hxbound
  calc principalPlaneChord U V i
      = Real.sqrt (principalPlaneChord U V i ^ 2) :=
        (Real.sqrt_sq (principalPlaneChord_nonneg U V i)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hbound

/-- Closed form for the singular values of the restricted direct displacement:
the principal chords, then zeros. -/
theorem singularValues_restrictedDisplacement_directRotation
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V) (n : ℕ) :
    ((LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
        projection U).singularValues n =
      if hn : n < nontrivialAngleCount U V then
        principalPlaneChord U V ⟨n, hn⟩ else 0 := by
  classical
  set m := nontrivialAngleCount U V with hm
  set AR := (LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
    projection U with hAR
  have hmE : m ≤ finrank 𝕜 E := nontrivialAngleCount_le_finrank U V
  -- Eigenvector family: the source vectors, then an orthonormal completion.
  set v : Fin (finrank 𝕜 E) → E := fun k =>
    if hk : (k : ℕ) < m then principalSourceVector U V ⟨(k : ℕ), hk⟩ else 0
    with hv
  set s : Set (Fin (finrank 𝕜 E)) := {k | (k : ℕ) < m} with hs
  have hres : Orthonormal 𝕜 (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : (a : ℕ) < m := ha
    have hb' : (b : ℕ) < m := hb
    simp only [Set.domRestrict_apply, hv, dite_eq_left ha', dite_eq_left hb']
    rw [orthonormal_iff_ite.mp (orthonormal_principalSourceVector U V)
      ⟨(a : ℕ), ha'⟩ ⟨(b : ℕ), hb'⟩]
    congr 1
    simp only [Fin.mk.injEq, Subtype.mk.injEq, eq_iff_iff]
    constructor
    · intro h; exact Fin.ext h
    · intro h; exact_mod_cast congrArg Fin.val h
  obtain ⟨b, hb⟩ := hres.exists_orthonormalBasis_extension_of_card_eq
    (by simp) (v := v)
  set μ : Fin (finrank 𝕜 E) → ℝ := fun k =>
    if hk : (k : ℕ) < m then principalPlaneChord U V ⟨(k : ℕ), hk⟩ ^ 2 else 0
    with hμ
  have hμanti : Antitone μ := by
    intro a c hac
    rw [hμ]
    simp only
    split_ifs with h1 h2 h2
    · have hchord := principalPlaneChord_antitone U V
        (show (⟨(a : ℕ), h2⟩ : Fin m) ≤ ⟨(c : ℕ), h1⟩ from hac)
      have h0a := principalPlaneChord_nonneg U V ⟨(a : ℕ), h2⟩
      have h0c := principalPlaneChord_nonneg U V ⟨(c : ℕ), h1⟩
      nlinarith
    -- `a ≤ c < 2m` makes this branch vacuous; the next one is the genuine
    -- nonnegativity of a squared chord
    · omega
    · positivity
    · exact le_rfl
  -- The Gram operator of the restricted displacement.
  have hgramfull := adjoint_comp_displacement_directRotation U V hacute
  have hgram : AR.adjoint ∘ₗ AR =
      projection U ∘ₗ ((2 : 𝕜) • (LinearMap.id -
        TauCeti.operatorAbs (canonicalIntertwiner U V))) ∘ₗ projection U := by
    rw [hAR, LinearMap.adjoint_comp, projection_adjoint, ← hgramfull]
    ext x
    simp only [LinearMap.comp_apply]
  have hdiag : ∀ k, (AR.adjoint ∘ₗ AR) (b k) = ((μ k : ℝ) : 𝕜) • b k := by
    intro k
    by_cases hk : (k : ℕ) < m
    · have hbk : b k = v k := hb k hk
      have hsrc : b k = principalSourceVector U V ⟨(k : ℕ), hk⟩ := by
        rw [hbk, hv]; simp [dite_eq_left hk]
      rw [hgram, hsrc]
      have hu := principalSourceVector_mem U V hacute ⟨(k : ℕ), hk⟩
      simp only [LinearMap.comp_apply, LinearMap.comp_apply,
        projection_apply_of_mem hu, LinearMap.smul_apply, LinearMap.sub_apply,
        LinearMap.id_apply,
        abs_canonicalIntertwiner_apply_principalSourceVector U V hacute
          ⟨(k : ℕ), hk⟩]
      rw [smul_sub, map_sub]
      -- push the projector through every scalar before using its fixed point
      simp only [map_smul, projection_apply_of_mem hu]
      rw [hμ]
      simp only [dite_eq_left hk]
      rw [principalPlaneChord_sq]
      match_scalars
      ring
    · -- `b k` is orthogonal to the sources; `P_U (b k)` is fixed by `|S|`.
      have hperp_u : ∀ i, ⟪principalSourceVector U V i, b k⟫_𝕜 = 0 := by
        intro i
        have hval : ((⟨(i : ℕ), lt_of_lt_of_le i.isLt hmE⟩ :
            Fin (finrank 𝕜 E)) : ℕ) < m := i.isLt
        have hbu : b ⟨(i : ℕ), lt_of_lt_of_le i.isLt hmE⟩ =
            principalSourceVector U V i := by
          rw [hb _ hval, hv]
          simp only [dite_eq_left hval]
        have hne : (⟨(i : ℕ), lt_of_lt_of_le i.isLt hmE⟩ :
            Fin (finrank 𝕜 E)) ≠ k := by
          intro h
          rw [← h] at hk
          exact hk hval
        rw [← hbu]
        exact b.orthonormal.inner_eq_zero hne
      have hPmem : projection U (b k) ∈ U := U.starProjection_apply_mem _
      have hPperp : ∀ i, ⟪principalSourceVector U V i, projection U (b k)⟫_𝕜 = 0 := by
        intro i
        have := projection_inner_left_eq_right U (principalSourceVector U V i) (b k)
        rw [projection_apply_of_mem (principalSourceVector_mem U V hacute i)] at this
        rw [← this, hperp_u i]
      have habs := abs_canonicalIntertwiner_apply_eq_self_of_orthogonal_sources
        U V hPmem hPperp
      simp only [hgram, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply, habs,
        sub_self, smul_zero, map_zero, hμ]
      simp [dite_eq_right hk]
  have heig := LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis AR.isSymmetric_adjoint_comp_self rfl b
    hμanti hdiag
  rcases lt_or_ge n (finrank 𝕜 E) with hnE | hnE
  · rw [AR.singularValues_of_lt rfl hnE, heig]
    rw [hμ]
    simp only
    split_ifs with hn
    · exact Real.sqrt_sq (principalPlaneChord_nonneg U V _)
    · exact Real.sqrt_zero
  · rw [AR.singularValues_of_finrank_le hnE, dite_eq_right (by omega)]

/-- **Pointwise singular-value minimality of the restricted displacement**
(Davis--Kahan Proposition 4.1): every singular value of `(I - R) P_U` is
dominated by the corresponding singular value of `(I - W) P_U` for any
unitary `W` carrying `U` onto `V`. -/
theorem singularValues_restrictedDisplacement_le
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) (n : ℕ) :
    ((LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
        projection U).singularValues n ≤
      ((LinearMap.id - W.toLinearMap) ∘ₗ projection U).singularValues n := by
  rw [singularValues_restrictedDisplacement_directRotation U V hacute n]
  split_ifs with hn
  · exact principalPlaneChord_le_singularValues_restrictedDisplacement
      U V hacute W hmap ⟨n, hn⟩
  · exact LinearMap.singularValues_nonneg _ n

/-- **Ky Fan minimality of the restricted displacement** (Davis--Kahan
Corollary 4.1, Ky Fan form). -/
theorem kyFanSum_restrictedDisplacement_le
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) (k : ℕ) :
    kyFanSum k ((LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
        projection U) ≤
      kyFanSum k ((LinearMap.id - W.toLinearMap) ∘ₗ projection U) :=
  kyFanSum_le_of_singularValues_le
    (singularValues_restrictedDisplacement_le U V hacute W hmap) k

/-- **Unitarily-invariant-norm minimality of the restricted displacement**
(Davis--Kahan Corollary 4.1): the direct rotation minimizes `N ((I - W) P_U)`
for every UI norm `N`, over any `RCLike` field, with no largest-angle
threshold.  `IsAcute` is required, but only because `directRotation` is
defined from it. -/
theorem uiNorm_restrictedDisplacement_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hacute : IsAcute U V)
    (W : E ≃ₗᵢ[𝕜] E) (hmap : U.map W.toLinearMap = V) :
    N ((LinearMap.id - (directRotation U V hacute).toLinearMap) ∘ₗ
        projection U) ≤
      N ((LinearMap.id - W.toLinearMap) ∘ₗ projection U) :=
  N.apply_le_of_kyFanSum_le
    (kyFanSum_restrictedDisplacement_le U V hacute W hmap)
end DavisKahan.FiniteDimensional
end TauCeti
