/-
Copyright (c) 2026 M1ngXU. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Obreiter, Tobias Steinbrecher, Robert Foerster
-/

import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.Step1
import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.Step2
import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.HessianBound
import LeanPool.PLAcceleratedNesterovLean.Convergence.LocalGeometry.SegmentEstimate
import LeanPool.PLAcceleratedNesterovLean.MorseBott.Bridge
import Mathlib.Analysis.Calculus.FDeriv.Symmetric


/-!
# Local Fiberwise Geometry from PL near M

Given a base point m⋆ ∈ M and any μ' ∈ (0, μ), there exists a fiber-saturated open
neighborhood U₊ of m⋆ with U₊ ⊂⊂ U, and ε > 0 with ε ≤ √(μ'/η), such that:

(a) Normal Hessian lower bound: ξᵀ D²f(x)ξ ≥ μ'‖ξ‖² for x ∈ U₊, ξ ∈ N_{π(x)}M
(b) Quadratic growth: f(x) - f⋆ ≥ (μ'/2) dist(x, M)²
(c) Strong aiming: ⟨∇f(x), x - π(x)⟩ ≥ f(x) - f⋆ + (μ'/2)‖x - π(x)‖²
(d) Hessian lower bound: D²f(x) ≽ -εI
-/

noncomputable section

namespace PLAcceleratedNesterovLean

open scoped Topology NNReal
open Manifold


/-- Fiber-path second derivative lower bound.

Given f C² on an open set V containing the segment {m + t·e | t ∈ ℝ},
the fiber path φ(t) = f(m + t·e) satisfies φ''(t) ≥ μ' * ‖e‖² for t ∈ [0,1],
where e = x − π(x) is a normal direction.
This is used for both quadratic growth and strong aiming. -/
private abbrev fiber_path_hessian_lower_bound
    {d : ℕ} (f : E d → ℝ) (μ' : ℝ)
    (m e : E d)
    {V : Set (E d)} (hV : IsOpen V) (hf_C2 : ContDiffOn ℝ 2 f V)
    (hseg : ∀ t : ℝ, t ∈ Set.Icc 0 1 → m + t • e ∈ V)
    (hbound : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → hessianQuadForm f (m + t • e) e ≥ μ' * ‖e‖ ^ 2) :
    let φ : ℝ → ℝ := fun t => f (m + t • e)
    ∀ t, 0 ≤ t → t ≤ 1 →
      deriv (deriv φ) t ≥ μ' * ‖e‖ ^ 2 := by
  intro φ t ht0 ht1
  have hf_at : ContDiffAt ℝ 2 f (m + t • e) :=
    hf_C2.contDiffAt (hV.mem_nhds (hseg t ⟨ht0, ht1⟩))
  rw [fiber_path_second_deriv f m e t hf_at]
  exact hbound t ht0 ht1

/-- **Local fiberwise geometry from PL near M.**

Fix m⋆ ∈ M and any μ' ∈ (0, μ). There exists a fiber-saturated open neighborhood U₊
of m⋆ with U₊ ⊂⊂ U, and ε > 0 with ε ≤ √(μ'/η), satisfying:
  (a) normal Hessian bound ≥ μ' in normal directions,
  (b) quadratic growth of f above f⋆,
  (c) strong aiming inequality,
  (d) global Hessian bound ≥ -ε.
-/
private abbrev localFiberwiseGeometryProof
    -- Dimensions
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Smoothness parameters
    (L : ℝ≥0) (_hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ)
    -- Slack parameter μ' ∈ (0, μ), used to leave room for local perturbations.
    (μ' : ℝ) (hμ' : 0 < μ') (hμ'_lt : μ' < μ)
    -- Step size
    (η : ℝ) (_hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    -- The minimizer set S = argmin f
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Tubular neighborhood U ⊃ S (open set with unique projection + C² submanifold structure)
    (U : Set (E d))
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U)
    -- PL condition on U
    (hPL : PolyakLojasiewicz f μ U)
    -- f is C² on U
    (hf_C2 : ContDiffOn ℝ 2 f U)
    -- Nearest-point projection on U
    (π : E d → E d)
    (hπ_proj : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    -- Gradient vanishes on S
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    -- Base point on M
    (m_star : E d) (hm_star : m_star ∈ S) :
    -- Conclusion: ∃ neighborhood U₊ and ε with all four properties for μ'
    ∃ (U_plus : Set (E d)) (ε : ℝ),
      -- U₊ is open, contains m⋆, and U₊ ⊂⊂ U (compact closure inside U)
      IsOpen U_plus ∧ m_star ∈ U_plus ∧
      IsCompact (closure U_plus) ∧ closure U_plus ⊆ U ∧
      Convex ℝ U_plus ∧
      -- ε > 0 with ε ≤ √(μ/(4η))
      0 < ε ∧ ε ≤ Real.sqrt (μ' / η) ∧
      -- (a) Normal Hessian lower bound: for ξ in ker(Dπ(π x))
      (∀ x ∈ U_plus, ∀ ξ : E d,
        fderiv ℝ π (π x) ξ = 0 →
        hessianQuadForm f x ξ ≥ μ' * ‖ξ‖ ^ 2) ∧
      -- (b) Quadratic growth
      (∀ x ∈ U_plus,
        f x - fStar f ≥ μ' / 2 * (Metric.infDist x S) ^ 2) ∧
      -- (c) Strong aiming
      (∀ x ∈ U_plus,
        @inner ℝ _ _ (gradient f x) (x - π x) ≥
          f x - fStar f + μ' / 2 * ‖x - π x‖ ^ 2) ∧
      -- (d) Hessian lower bound D²f(x) ≽ -εI
      (∀ x ∈ U_plus, ∀ ξ : E d,
        hessianQuadForm f x ξ ≥ -ε * ‖ξ‖ ^ 2) ∧
      -- (e) Normal Hessian ≥ μ at m_star (full μ bound at the base point)
      (∀ ξ : E d,
        fderiv ℝ π m_star ξ = 0 →
        hessianQuadForm f m_star ξ ≥ μ * ‖ξ‖ ^ 2) ∧
      -- (f) Fiber segments from U₊ stay in U
      (∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        π x + t • (x - π x) ∈ U) := by
  /-
    PROOF OUTLINE (`local_fiberwise_geometry`):
    1. PL ⟹ Morse-Bott: on M, normal Hessian ξᵀD²f(m)ξ ≥ μ‖ξ‖².
    2. By continuity of D²f and local compactness near m⋆, extend to ≥ μ' on a
       neighborhood V₁ (using the gap μ - μ' > 0).
    3. D²f(m) ≽ 0 at minimizers + continuity ⟹ D²f(x) ≽ -ε₀I on V₂.
    4. Construct fiber-saturated U₊ ⊂⊂ V₁ ∩ V₂ ∩ U.
    5. Quadratic growth and strong aiming by integrating φ(t) = f(m+te)
       along fibers (Step2 helpers).
  -/
  have hU_is_open : IsOpen U := hTub_sub.isOpen
  -- ================================================================
  -- Step 1: Hessian bounds on M (from PL + Morse-Bott structure)
  -- ================================================================
  -- PL ⟹ Morse-Bott: normal Hessian ξᵀD²f(m)ξ ≥ μ‖ξ‖² on M
  have h_normal_hess_M : ∀ m ∈ S, ∀ ξ : E d,
      fderiv ℝ π m ξ = 0 →
      hessianQuadForm f m ξ ≥ μ * ‖ξ‖ ^ 2 := by
    intro m hmS ξ hξ_normal
    -- ══════════════════════════════════════════════════════════════════
    -- Goal: hessianQuadForm f m ξ ≥ μ * ‖ξ‖ ^ 2
    -- Proof: Rayleigh quotient minimizer on the unit sphere of ker(H)⊥,
    -- combined with PL ⟹ μ·⟨Hv,v⟩ ≤ ‖Hv‖² (Rebjock & Boumal, Cor 2.17).
    -- ══════════════════════════════════════════════════════════════════
    -- ═══ BASIC SETUP ═══
    have hmin : ∀ y, f m ≤ f y := by rw [hM_argmin] at hmS; exact hmS
    have hmin_local : IsLocalMin f m := Filter.Eventually.of_forall hmin
    have hmU : m ∈ U := hTub_sub.subset hmS
    have hf_C2_at_m : ContDiffAt ℝ 2 f m :=
      hf_C2.contDiffAt (hU_is_open.mem_nhds hmU)
    -- DifferentiableAt ℝ f m and DifferentiableAt ℝ (gradient f) m from local C²
    have hf_da_m : DifferentiableAt ℝ f m :=
      hf_C2_at_m.differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
    have hfderiv_da_m : DifferentiableAt ℝ (fderiv ℝ f) m :=
      (hf_C2_at_m.fderiv_right le_rfl).differentiableAt one_ne_zero
    have hgrad_da_m : DifferentiableAt ℝ (gradient f) m := by
      exact ((InnerProductSpace.toDual ℝ (E d)).symm
        |>.toContinuousLinearEquiv
        |>.differentiable |>.differentiableAt
        |>.comp m hfderiv_da_m)
    -- The gradient-Hessian operator H := D(∇f)(m) : E d →L[ℝ] E d
    set H := fderiv ℝ (gradient f) m with hH_def
    set K : Submodule ℝ (E d) := LinearMap.ker H.toLinearMap with hK_def
    -- ═══ BRIDGE 1: projection condition → ξ ∈ K⊥ ═══
    have hξ_orth : ξ ∈ K.orthogonal := by
      rw [K.mem_orthogonal]
      intro w hw
      -- w ∈ K = ker(H), need: ⟪w, ξ⟫ = 0
      -- Morse-Bott: K ⊆ range(Dπ(m)). Under PL + C², S is a smooth minimizer
      -- manifold with T_mS = ker(H), so every w ∈ ker(H) is tangent to S,
      -- hence w = Dπ(m)(u) for some u.
      have hMB : w ∈ LinearMap.range (fderiv ℝ π m).toLinearMap := by
        -- ── Step 1: Connect π with π' from tubular_neighborhood_projection ──
        obtain ⟨π', hπ'_proj, hπ'_fix, _, _, _, _, _, hπ'_diff, _, _⟩ :=
          tubular_neighborhood_projection_Ed hTub_sub ⟨m_star, hm_star⟩
        have hmU : m ∈ U := hTub_sub.subset hmS
        have hπ_eq' : ∀ x ∈ U, π x = π' x := by
          intro x hxU
          obtain ⟨p, hp, huniq⟩ := hTub_sub.uniqueProj x hxU
          exact (huniq (π x) (hπ_proj x hxU)).trans
            (huniq (π' x) ⟨(hπ'_proj x hxU).1,
              by rw [dist_eq_norm]; exact (hπ'_proj x hxU).2⟩).symm
        have hπ_ev : π =ᶠ[𝓝 m] π' :=
          Filter.eventually_of_mem (hTub_sub.isOpen.mem_nhds hmU) hπ_eq'
        have hfderiv_eq : fderiv ℝ π m = fderiv ℝ π' m := hπ_ev.fderiv_eq
        -- Suffices to show fderiv ℝ π' m w = w
        suffices hPw : fderiv ℝ π' m w = w by
          exact LinearMap.mem_range.mpr
            ⟨w, by rw [ContinuousLinearMap.coe_coe, hfderiv_eq, hPw]⟩
        -- ── Step 2: Convert PL → MuPL → submanifold ──
        have hPL_ext : ExternalThm3.PolyakLojasiewicz f μ U :=
          ⟨hμ, fun x hxU => by
            have := hPL.2.2 x hxU
            rw [norm_mathlibGradient_eq_norm_fderiv] at this; exact this⟩
        have hMuPL : MuPL f μ m :=
          ExternalThm3.pl_to_muPL f μ U m
            (by rw [hM_argmin] at hmS; exact hmS)
            (hTub_sub.isOpen.mem_nhds hmU) hPL_ext
        have hsub' : IsLocalSubmanifoldAt (localMinSet f m) m (hessianKer f m) := by
          exact MuPL.implies_submanifold f μ m hμ hf_C2_at_m hmin_local hMuPL
        -- ── Step 3: localMinSet f m = S ──
        have hS_eq : S = localMinSet f m := by
          ext x; constructor
          · intro hxS; rw [hM_argmin] at hxS
            exact ⟨Filter.Eventually.of_forall hxS, le_antisymm (hxS m) (hmin x)⟩
          · intro ⟨_, hfx⟩; rw [hM_argmin]
            intro z; linarith [hmin z]
        -- ── Step 4: w ∈ hessianKer f m ──
        have hw' : fderiv ℝ (gradient f) m w = 0 := by
          have := LinearMap.mem_ker.mp hw; rwa [ContinuousLinearMap.coe_coe] at this
        have hw_hess : w ∈ hessianKer f m := by
          rw [hessianKer, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
          have hbridge : ∀ u', (fderiv ℝ (fderiv ℝ f) m) w u' = 0 := by
            intro u'
            have h1 : fderiv ℝ (fun z => @inner ℝ (E d) _ (gradient f z) u') m w =
                @inner ℝ (E d) _ (fderiv ℝ (gradient f) m w) u' := by
              rw [fderiv_inner_apply (𝕜 := ℝ) (hgrad_da_m) (differentiableAt_const u')]
              simp only [fderiv_fun_const, Pi.zero_apply,
                zero_apply,
                inner_zero_right, zero_add]
            have hDf_diff' : DifferentiableAt ℝ (fderiv ℝ f) m := hfderiv_da_m
            have hcomp : HasFDerivAt (fun y => (fderiv ℝ f y) u')
                ((ContinuousLinearMap.apply ℝ ℝ u').comp (fderiv ℝ (fderiv ℝ f) m)) m :=
              ((ContinuousLinearMap.apply ℝ ℝ u').hasFDerivAt).comp m hDf_diff'.hasFDerivAt
            have h2 : fderiv ℝ (fun z => @inner ℝ (E d) _ (gradient f z) u') m w =
                (fderiv ℝ (fderiv ℝ f) m) w u' := by
              have heq : (fun z => @inner ℝ (E d) _ (gradient f z) u') =ᶠ[𝓝 m]
                  (fun y => (fderiv ℝ f y) u') := by
                filter_upwards [hU_is_open.mem_nhds hmU] with z hz
                exact inner_gradient_left (𝕜 := ℝ) (f := f) (x := z) (y := u')
              rw [heq.fderiv_eq, hcomp.fderiv]
              rfl
            rw [← h2, h1, hw', inner_zero_left]
          have : (fderiv ℝ (fderiv ℝ f) m) w = 0 :=
            ContinuousLinearMap.ext fun u' => hbridge u'
          exact this
        -- ── Step 5: Construct curve γ in S through m with γ'(0) = w ──
        set T := hessianKer f m with hT_def
        obtain ⟨U_chart, hU_chart_nhds, ψ, hψ_C1, hψ0, hDψ0, hgraph⟩ := hsub'.2
        rw [← hS_eq] at hgraph
        set w_T : ↥T := ⟨w, hw_hess⟩
        set γ : ℝ → E d :=
          fun t => m + t • w + (↑(ψ (t • w_T)) : E d)
        -- HasDerivAt γ w 0
        have hψ_diff : DifferentiableAt ℝ ψ 0 :=
          hψ_C1.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
        have hβ : HasDerivAt (fun t : ℝ => t • w_T) w_T 0 := by
          simpa using (hasDerivAt_id (0 : ℝ)).smul_const w_T
        have hψβ : HasDerivAt (fun t : ℝ => ψ (t • w_T)) 0 0 := by
          have h := hψ_diff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hβ (zero_smul ℝ w_T).symm
          rwa [hDψ0, zero_apply] at h
        have hγ_deriv : HasDerivAt γ w 0 := by
          have h1 : HasDerivAt (fun t : ℝ => m + t • w) w 0 := by
            simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add m
          have h2 : HasDerivAt
              (fun t : ℝ => (↑(ψ (t • w_T)) : E d)) (0 : E d) 0 := by
            have h := (ContinuousLinearMap.hasFDerivAt
              T.orthogonal.subtypeL).comp_hasDerivAt (0 : ℝ) hψβ
            simp only [map_zero] at h
            exact h
          have h3 := h1.add h2
          rwa [add_zero] at h3
        -- ── Step 6: γ(t) ∈ S for small t ──
        have hγ0 : γ 0 = m := by
          change m + (0 : ℝ) • w + (↑(ψ ((0 : ℝ) • w_T)) : E d) = m
          rw [zero_smul, zero_smul, hψ0]; simp only [add_zero, ZeroMemClass.coe_zero]
        have hγ_cont := hγ_deriv.continuousAt
        have hpre : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U_chart := by
          exact hγ_cont.preimage_mem_nhds (by rw [hγ0]; exact hU_chart_nhds)
        have hγ_in_S : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ S := by
          filter_upwards [hpre] with t ht
          have hgr := (hgraph (γ t) ht).mpr
          apply hgr
          -- γ(t) - m = t•(w_T : E d) + ↑(ψ(t•w_T))
          have hγ_sub : γ t - m = t • (w_T : E d) + (↑(ψ (t • w_T)) : E d) := by
            simp only [γ]; abel
          have hψ_proj : T.orthogonalProjectionOnto (ψ (t • w_T) : E d) = 0 :=
            Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr (ψ (t • w_T)).property
          have hw_perp_proj : Tᗮ.orthogonalProjectionOnto (w_T : E d) = 0 :=
            Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
              (Submodule.le_orthogonal_orthogonal T w_T.property)
          rw [hγ_sub, map_add, map_smul, map_add, map_smul]
          rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self w_T,
            hψ_proj,
            add_zero,
            hw_perp_proj,
            smul_zero, zero_add,
            Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (ψ (t • w_T))]
        -- ── Step 7: Differentiate π' ∘ γ = γ to get fderiv ℝ π' m w = w ──
        -- π' fixes S, so π' ∘ γ =ᶠ[𝓝 0] γ
        have hπγ_eq : (π' ∘ γ) =ᶠ[𝓝 (0 : ℝ)] γ := by
          filter_upwards [hγ_in_S] with t ht
          exact hπ'_fix (γ t) ht
        -- From EventuallyEq + HasDerivAt γ w 0: HasDerivAt (π' ∘ γ) w 0
        have hπγ_deriv1 : HasDerivAt (π' ∘ γ) w 0 :=
          hπγ_eq.hasDerivAt_iff.mpr hγ_deriv
        -- From chain rule: HasDerivAt (π' ∘ γ) ((fderiv ℝ π' m) w) 0
        have hπ_diff_m : DifferentiableAt ℝ π' m := hπ'_diff m hmS
        have hπγ_deriv2 : HasDerivAt (π' ∘ γ) ((fderiv ℝ π' m) w) 0 :=
          hπ_diff_m.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ_deriv hγ0.symm
        -- By uniqueness of derivatives
        exact hπγ_deriv2.unique hπγ_deriv1
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hMB
      simp only [ContinuousLinearMap.coe_coe] at hu
      -- Self-adjointness of Dπ(m): for the nearest-point projection onto a smooth
      -- submanifold, the derivative at a point on the manifold is an orthogonal
      -- projector, hence self-adjoint: ⟪Dπ(m) u, v⟫ = ⟪u, Dπ(m) v⟫.
      have hπ_sa : @inner ℝ (E d) _ (fderiv ℝ π m u) ξ =
          @inner ℝ (E d) _ u (fderiv ℝ π m ξ) := by
        -- Get canonical projection π' with self-adjointness from tubular neighborhood
        obtain ⟨π', hπ'_proj, _, _, _, _, _, _, _, hπ'_sa, _⟩ :=
          tubular_neighborhood_projection_Ed hTub_sub ⟨m_star, hm_star⟩
        have hmU : m ∈ U := hTub_sub.subset hmS
        -- π and π' agree on U by uniqueness of nearest-point projection
        have hπ_eq : ∀ x ∈ U, π x = π' x := by
          intro x hxU
          obtain ⟨p, hp, huniq⟩ := hTub_sub.uniqueProj x hxU
          have h1 : π x ∈ S ∧ dist x (π x) = Metric.infDist x S := hπ_proj x hxU
          have h2' := hπ'_proj x hxU
          have h2 : π' x ∈ S ∧ dist x (π' x) = Metric.infDist x S :=
            ⟨h2'.1, by rw [dist_eq_norm]; exact h2'.2⟩
          exact (huniq (π x) h1).trans (huniq (π' x) h2).symm
        -- π =ᶠ[𝓝 m] π' since they agree on the open set U containing m
        have hπ_eq_nhds : π =ᶠ[𝓝 m] π' :=
          Filter.eventually_of_mem (hTub_sub.isOpen.mem_nhds hmU) hπ_eq
        rw [hπ_eq_nhds.fderiv_eq]
        exact hπ'_sa m hmS u ξ
      rw [← hu, hπ_sa, hξ_normal, inner_zero_right]
    have hξ_hess_orth : ξ ∈ (hessianKer f m).orthogonal := by
      rw [(hessianKer f m).mem_orthogonal]
      intro w hw
      have hwK : w ∈ K := by
        rw [hK_def, LinearMap.mem_ker]
        have hw_hess_zero : (fderiv ℝ (fderiv ℝ f) m) w = 0 := by
          exact LinearMap.mem_ker.mp hw
        apply ext_inner_right ℝ
        intro u'
        have hbridge : @inner ℝ (E d) _ (H w) u' =
            (fderiv ℝ (fderiv ℝ f) m) w u' := by
          set G : E d → ℝ := fun y => (fderiv ℝ f y) u'
          have hG_inner_nhds : G =ᶠ[𝓝 m]
              fun z => @inner ℝ (E d) _ (gradient f z) u' := by
            filter_upwards [hU_is_open.mem_nhds hmU] with z hz
            exact (inner_gradient_left (𝕜 := ℝ) (f := f) (x := z) (y := u')).symm
          have hleft : fderiv ℝ G m w = @inner ℝ (E d) _ (H w) u' := by
            rw [hG_inner_nhds.fderiv_eq]
            rw [fderiv_inner_apply (𝕜 := ℝ) hgrad_da_m (differentiableAt_const u')]
            simp only [fderiv_fun_const, Pi.zero_apply,
              zero_apply, inner_zero_right, ← hH_def, zero_add]
          have hright : fderiv ℝ G m w = (fderiv ℝ (fderiv ℝ f) m) w u' := by
            have hcomp : HasFDerivAt G
                ((ContinuousLinearMap.apply ℝ ℝ u').comp
                  (fderiv ℝ (fderiv ℝ f) m)) m :=
              ((ContinuousLinearMap.apply ℝ ℝ u').hasFDerivAt).comp
                m hfderiv_da_m.hasFDerivAt
            rw [hcomp.fderiv]
            rfl
          linarith
        change @inner ℝ (E d) _ (H w) u' = @inner ℝ (E d) _ (0 : E d) u'
        calc
          @inner ℝ (E d) _ (H w) u'
              = (fderiv ℝ (fderiv ℝ f) m) w u' := hbridge
          _ = 0 := by rw [hw_hess_zero, zero_apply]
          _ = @inner ℝ (E d) _ (0 : E d) u' := by rw [inner_zero_left]
      have hξK := hξ_orth
      rw [K.mem_orthogonal] at hξK
      exact hξK w hwK
    have hPL_ext : ExternalThm3.PolyakLojasiewicz f μ U :=
      ⟨hμ, fun x hxU => by
        have := hPL.2.2 x hxU
        rw [norm_mathlibGradient_eq_norm_fderiv] at this
        exact this⟩
    have hm_ext : m ∈ ExternalThm3.argminSet f := by
      rw [hM_argmin] at hmS
      exact hmS
    have hbound := ExternalThm3.hessianQuadForm_bound f μ U m ξ
      hf_C2_at_m hPL_ext hm_ext (hU_is_open.mem_nhds hmU) hξ_hess_orth
    have hgrad_fun : ExternalThm3.gradient f = gradient f := by
      funext x
      exact externalThm3_gradient_eq_gradient f x
    simpa [ExternalThm3.hessianQuadForm, hessianQuadForm, hgrad_fun] using hbound
  -- D²f(m) ≽ 0 at global minimizers (PSD, by hessian_psd_at_minimizer)
  have h_hess_psd_M : ∀ m ∈ S, ∀ ξ : E d,
      hessianQuadForm f m ξ ≥ 0 := by
    intro m hmS ξ
    have hmin : ∀ y, f m ≤ f y := by rw [hM_argmin] at hmS; exact hmS
    have hmU : m ∈ U := hTub_sub.subset hmS
    have hf_m_C2 : ContDiffAt ℝ 2 f m :=
      hf_C2.contDiffAt (hU_is_open.mem_nhds hmU)
    exact hessian_psd_at_minimizer f m hmin hf_m_C2 ξ
  -- ================================================================
  -- Step 2: Extend bounds to neighborhoods by continuity + compactness
  -- ================================================================
  -- The gap μ - μ' > 0 provides room to relax constants
  have hgap : 0 < μ - μ' := by linarith
  -- V₁: neighborhood of S where normal Hessian ≥ μ'‖ξ‖²
  -- (continuous_lower_bound_neighborhood applied to the normal Hessian map)
  obtain ⟨V₁, hV₁_open, hm_V₁, h_normal_V₁⟩ :
      ∃ V₁ : Set (E d), IsOpen V₁ ∧ m_star ∈ V₁ ∧
        ∀ x ∈ V₁, ∀ ξ : E d,
          fderiv ℝ π (π x) ξ = 0 →
          hessianQuadForm f x ξ ≥ μ' * ‖ξ‖ ^ 2 := by
    -- ── Setup: hessianQuadForm ContinuousOn from C² ──
    set g : E d × E d → ℝ := fun p => hessianQuadForm f p.1 p.2 with hg_def
    have hg_contOn : ContinuousOn g (U ×ˢ Set.univ) := by
      have hfderiv_C1 : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
        hf_C2.fderiv_of_isOpen hU_is_open (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
      have hgrad_C1 : ContDiffOn ℝ 1 (gradient f) U :=
        ((InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv.contDiff.of_le
          le_top).comp_contDiffOn hfderiv_C1
      have hDgrad_cont : ContinuousOn (fderiv ℝ (gradient f)) U :=
        (hgrad_C1.fderiv_of_isOpen hU_is_open
          (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn
      simp only [hg_def, hessianQuadForm]
      exact ((hDgrad_cont.comp continuousOn_fst (fun p hp => hp.1)).clm_apply
        continuousOn_snd).inner continuousOn_snd
    -- ── Local compactness: S ∩ closedBall(m⋆, r_loc) is compact ──
    haveI : ProperSpace (E d) := FiniteDimensional.proper ℝ (E d)
    have hm_star_U := hTub_sub.subset hm_star
    obtain ⟨r_U, hr_U_pos, hr_U_sub⟩ := Metric.isOpen_iff.mp hTub_sub.isOpen m_star hm_star_U
    set r_loc := min 1 (r_U / 2) with hr_loc_def
    have hr_loc_pos : 0 < r_loc := lt_min one_pos (half_pos hr_U_pos)
    have hr_loc_le1 : r_loc ≤ 1 := min_le_left _ _
    have hcball_sub_U : Metric.closedBall m_star r_loc ⊆ U := by
      intro x hx
      exact hr_U_sub (Metric.closedBall_subset_ball
        (lt_of_le_of_lt (min_le_right 1 (r_U / 2)) (half_lt_self hr_U_pos)) hx)
    set S_loc := S ∩ Metric.closedBall m_star r_loc
    have hS_loc_compact : IsCompact S_loc :=
      hTub_sub.isCompact_inter_closedBall hcball_sub_U
    have hSphere_compact' : IsCompact (Metric.sphere (0 : E d) 1) := isCompact_sphere 0 1
    have hSlxS_compact := hS_loc_compact.prod hSphere_compact'
    have hSlxS_closed := hSlxS_compact.isClosed
    have hSlxS_sub : S_loc ×ˢ Metric.sphere (0 : E d) 1 ⊆ U ×ˢ Set.univ :=
      Set.prod_mono (Set.inter_subset_left.trans hTub_sub.subset) (Set.subset_univ _)
    -- ── Define N = {(m,ξ) ∈ S_loc × sphere | hessianQuadForm f m ξ ≥ μ} ──
    -- N is compact: closed subset of compact S_loc × sphere
    set N : Set (E d × E d) :=
      (S_loc ×ˢ Metric.sphere (0 : E d) 1) ∩ g ⁻¹' Set.Ici μ with hN_def
    have hN_compact : IsCompact N :=
      hSlxS_compact.of_isClosed_subset
        ((hg_contOn.mono hSlxS_sub).preimage_isClosed_of_isClosed hSlxS_closed isClosed_Ici)
        Set.inter_subset_left
    -- ── V_nbhd = (U ×ˢ univ) ∩ {(x,ξ) | hessianQuadForm f x ξ > μ'} is open ──
    set V_nbhd : Set (E d × E d) :=
      (U ×ˢ Set.univ) ∩ g ⁻¹' Set.Ioi μ' with hV_def
    have hV_open : IsOpen V_nbhd :=
      hg_contOn.isOpen_inter_preimage (hU_is_open.prod isOpen_univ) isOpen_Ioi
    -- ── N ⊆ V_nbhd (since S_loc ⊆ S, hessianQuadForm ≥ μ > μ' on N) ──
    have hN_sub : N ⊆ V_nbhd := by
      intro ⟨x, ξ⟩ ⟨hmem, hge⟩
      exact ⟨hSlxS_sub hmem, by
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Ici] at hge ⊢; linarith⟩
    -- ── Thickening: ∃ δ > 0, thickening δ N ⊆ V_nbhd ──
    obtain ⟨δ, hδ_pos, hthick⟩ := hN_compact.exists_thickening_subset_open hV_open hN_sub
    -- ── V₁ = U ∩ ball(m⋆, min(δ, r_loc/2)): local neighborhood ──
    set δ' := min δ (r_loc / 2) with hδ'_def
    have hδ'_pos : 0 < δ' := lt_min hδ_pos (half_pos hr_loc_pos)
    refine ⟨U ∩ Metric.ball m_star δ',
            hTub_sub.isOpen.inter Metric.isOpen_ball,
            ⟨hTub_sub.subset hm_star, Metric.mem_ball_self hδ'_pos⟩,
            fun x ⟨hxU, hx_near⟩ ξ hξ_normal => ?_⟩
    -- Main bound
    · by_cases hξ : ξ = 0
      · subst hξ; simp only [hessianQuadForm, map_zero, inner_self_eq_norm_sq_to_K, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, ge_iff_le, le_refl]
      · have hξ_norm_pos : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
        set c := ‖ξ‖ with hc_def
        set ξ₀ := c⁻¹ • ξ with hξ₀_def
        have hξ₀_norm : ‖ξ₀‖ = 1 := by
          rw [hξ₀_def, norm_smul, norm_inv, norm_norm,
            inv_mul_cancel₀ (ne_of_gt hξ_norm_pos)]
        have hξ₀_sphere : ξ₀ ∈ Metric.sphere (0 : E d) 1 := by
          rw [Metric.mem_sphere, dist_zero_right]; exact hξ₀_norm
        -- fderiv ℝ π (π x) ξ₀ = 0 (linearity)
        have hξ₀_normal : fderiv ℝ π (π x) ξ₀ = 0 := by
          rw [hξ₀_def, map_smul, hξ_normal, smul_zero]
        -- π(x) ∈ S
        have hπ_in_S : π x ∈ S := (hπ_proj x hxU).1
        -- Derive: dist(x, m_star) < δ' ≤ r_loc/2, so π(x) ∈ S_loc
        have hx_dist : dist x m_star < δ' := Metric.mem_ball.mp hx_near
        have hinfDist_le : Metric.infDist x S ≤ dist x m_star :=
          Metric.infDist_le_dist_of_mem hm_star
        have hπ_in_S_loc : π x ∈ S_loc := by
          refine ⟨hπ_in_S, Metric.mem_closedBall.mpr ?_⟩
          have h1 := dist_triangle (π x) x m_star
          rw [dist_comm (π x) x] at h1
          have h2 : dist x (π x) = Metric.infDist x S := (hπ_proj x hxU).2
          linarith [min_le_right δ (r_loc / 2)]
        -- hessianQuadForm f (π x) ξ₀ ≥ μ (by h_normal_hess_M)
        have hge_mu : hessianQuadForm f (π x) ξ₀ ≥ μ := by
          have := h_normal_hess_M (π x) hπ_in_S ξ₀ hξ₀_normal
          rw [hξ₀_norm, one_pow, mul_one] at this; exact this
        -- (π(x), ξ₀) ∈ N
        have hπξ_in_N : (π x, ξ₀) ∈ N := by
          refine ⟨Set.mk_mem_prod hπ_in_S_loc hξ₀_sphere, ?_⟩
          simp only [Set.mem_preimage, Set.mem_Ici]; exact hge_mu
        -- dist((x, ξ₀), (π(x), ξ₀)) = dist(x, π(x)) < δ
        have hdist_pair : dist (x, ξ₀) (π x, ξ₀) = dist x (π x) := by
          simp only [Prod.dist_eq, dist_self, dist_nonneg, sup_of_le_left]
        have hx_near_π : dist x (π x) = Metric.infDist x S := (hπ_proj x hxU).2
        -- (x, ξ₀) ∈ thickening δ N
        have h_in_thick : (x, ξ₀) ∈ Metric.thickening δ N := by
          rw [Metric.mem_thickening_iff]
          exact ⟨(π x, ξ₀), hπξ_in_N, by
            rw [hdist_pair, hx_near_π]; linarith [min_le_left δ (r_loc / 2)]⟩
        -- hessianQuadForm f x ξ₀ > μ/4
        have hbound₀ : hessianQuadForm f x ξ₀ ≥ μ' := by
          have hmem := (hthick h_in_thick).2
          simp only [Set.mem_preimage, Set.mem_Ioi] at hmem
          linarith
        -- ξ = c • ξ₀
        have hξ_eq : ξ = c • ξ₀ := by
          rw [hξ₀_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hξ_norm_pos), one_smul]
        -- Homogeneity: hessianQuadForm f x ξ = c² * hessianQuadForm f x ξ₀
        have hhomog : hessianQuadForm f x ξ = c ^ 2 * hessianQuadForm f x ξ₀ := by
          conv_lhs => rw [hξ_eq]
          simp only [hessianQuadForm, map_smul, real_inner_smul_left, real_inner_smul_right]
          ring
        rw [hhomog]
        have hc_sq_nonneg : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
        nlinarith [hbound₀, hc_sq_nonneg]
  -- Choose ε₀ = min 1 (√(μ/(4η))), which satisfies 0 < ε₀ ≤ √(μ/(4η))
  let ε₀ : ℝ := min 1 (Real.sqrt (μ' / η))
  have hε₀_pos : 0 < ε₀ := by
    exact lt_min one_pos (Real.sqrt_pos_of_pos (div_pos hμ' hη_pos))
  have hε₀_le : ε₀ ≤ Real.sqrt (μ' / η) := min_le_right _ _
  -- V₂: neighborhood of S where D²f(x) ≽ -ε₀·I
  -- (D²f(m) ≽ 0 on M extends to ≽ -ε₀ by continuity)
  obtain ⟨V₂, hV₂_open, hm_V₂, h_hess_V₂⟩ :
      ∃ V₂ : Set (E d), IsOpen V₂ ∧ m_star ∈ V₂ ∧
        ∀ x ∈ V₂, ∀ ξ : E d,
          hessianQuadForm f x ξ ≥ -ε₀ * ‖ξ‖ ^ 2 := by
    -- Strategy: hessianQuadForm ≥ 0 on compact S (PSD at minimizers).
    -- Apply continuous_lower_bound_neighborhood on E d × E d with
    -- K = S ×ˢ sphere to get ≥ -ε₀ on unit vectors near S.
    -- Use generalized_tube_lemma to separate variables.
    -- Extend to all ξ by quadratic homogeneity.
    -- Step 1-2: hessianQuadForm ContinuousOn from C²
    set g₂ : E d × E d → ℝ := fun p => hessianQuadForm f p.1 p.2 with hg₂_def
    have hg₂_contOn : ContinuousOn g₂ (U ×ˢ Set.univ) := by
      have hfderiv_C1 : ContDiffOn ℝ 1 (fderiv ℝ f) U :=
        hf_C2.fderiv_of_isOpen hU_is_open (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
      have hgrad_C1 : ContDiffOn ℝ 1 (gradient f) U :=
        ((InnerProductSpace.toDual ℝ (E d)).symm.toContinuousLinearEquiv.contDiff.of_le
          le_top).comp_contDiffOn hfderiv_C1
      have hDgrad_cont : ContinuousOn (fderiv ℝ (gradient f)) U :=
        (hgrad_C1.fderiv_of_isOpen hU_is_open
          (show (0 : WithTop ℕ∞) + 1 ≤ 1 by norm_num)).continuousOn
      simp only [hg₂_def, hessianQuadForm]
      exact ((hDgrad_cont.comp continuousOn_fst (fun p hp => hp.1)).clm_apply
        continuousOn_snd).inner continuousOn_snd
    -- Step 3: S_loc₂ = S ∩ closedBall(m⋆, r_loc₂) is compact (local compactness)
    haveI : ProperSpace (E d) := FiniteDimensional.proper ℝ (E d)
    have hm_star_U₂ := hTub_sub.subset hm_star
    obtain ⟨r_U₂, hr_U₂_pos, hr_U₂_sub⟩ := Metric.isOpen_iff.mp hTub_sub.isOpen m_star hm_star_U₂
    set r_loc₂ := min 1 (r_U₂ / 2) with hr_loc₂_def
    have hr_loc₂_pos : 0 < r_loc₂ := lt_min one_pos (half_pos hr_U₂_pos)
    have hcball₂_sub_U : Metric.closedBall m_star r_loc₂ ⊆ U := by
      intro x hx
      exact hr_U₂_sub (Metric.closedBall_subset_ball
        (lt_of_le_of_lt (min_le_right 1 (r_U₂ / 2)) (half_lt_self hr_U₂_pos)) hx)
    set S_loc₂ := S ∩ Metric.closedBall m_star r_loc₂
    have hS_loc₂_compact : IsCompact S_loc₂ :=
      hTub_sub.isCompact_inter_closedBall hcball₂_sub_U
    -- Step 4: Unit sphere is compact (E d is finite-dimensional, hence proper)
    have hSphere_compact : IsCompact (Metric.sphere (0 : E d) 1) := isCompact_sphere 0 1
    -- Step 5: hessianQuadForm ≥ 0 on S × sphere (PSD at minimizers)
    have hg_K : ∀ p ∈ S ×ˢ Metric.sphere (0 : E d) 1,
        (0 : ℝ) ≤ g₂ p := by
      rintro ⟨x, ξ⟩ ⟨hx, -⟩
      exact h_hess_psd_M x hx ξ
    -- Step 6: V_prod = (U ×ˢ univ) ∩ {p | g₂ p > -ε₀} is open, contains K = S × sphere
    set V_prod : Set (E d × E d) :=
      (U ×ˢ Set.univ) ∩ g₂ ⁻¹' Set.Ioi (-ε₀) with hVp_def
    have hV_prod_open : IsOpen V_prod :=
      hg₂_contOn.isOpen_inter_preimage (hU_is_open.prod isOpen_univ) isOpen_Ioi
    have hK_V_prod : S ×ˢ Metric.sphere (0 : E d) 1 ⊆ V_prod := by
      intro ⟨x, ξ⟩ ⟨hx, hξ⟩
      exact ⟨⟨hTub_sub.subset hx, Set.mem_univ _⟩,
        by simp only [Set.mem_preimage, Set.mem_Ioi]; linarith [hg_K (x, ξ) ⟨hx, hξ⟩]⟩
    -- S_loc₂ ×ˢ sphere ⊆ V_prod (since S_loc₂ ⊆ S)
    have hK_V_prod_loc : S_loc₂ ×ˢ Metric.sphere (0 : E d) 1 ⊆ V_prod :=
      (Set.prod_mono Set.inter_subset_left (le_refl _)).trans hK_V_prod
    have hg_bound : ∀ p ∈ V_prod, (0 : ℝ) - ε₀ ≤ g₂ p := by
      intro p ⟨_, hmem⟩
      simp only [Set.mem_preimage, Set.mem_Ioi] at hmem; linarith
    -- Step 7: Apply generalized_tube_lemma with S_loc₂ (local compactness)
    obtain ⟨V₂, W, hV₂_open, _, hSloc_V₂, hSphere_W, hVW⟩ :=
      generalized_tube_lemma hS_loc₂_compact hSphere_compact hV_prod_open hK_V_prod_loc
    have hm_V₂ : m_star ∈ V₂ :=
      hSloc_V₂ ⟨hm_star, Metric.mem_closedBall_self (le_of_lt hr_loc₂_pos)⟩
    refine ⟨V₂, hV₂_open, hm_V₂, fun x hx ξ => ?_⟩
    -- Case ξ = 0: hessianQuadForm f x 0 = 0 ≥ 0 = -ε₀ * 0
    by_cases hξ : ξ = 0
    · subst hξ; simp only [hessianQuadForm, map_zero, inner_self_eq_norm_sq_to_K, norm_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, ge_iff_le, le_refl]
    · -- Case ξ ≠ 0: normalize to unit vector, apply bound, scale by ‖ξ‖²
      have hξ_norm_pos : (0 : ℝ) < ‖ξ‖ := norm_pos_iff.mpr hξ
      set c := ‖ξ‖ with hc_def
      set ξ₀ := c⁻¹ • ξ with hξ₀_def
      -- ‖ξ₀‖ = 1
      have hξ₀_norm : ‖ξ₀‖ = 1 := by
        rw [hξ₀_def, norm_smul, norm_inv, norm_norm,
          inv_mul_cancel₀ (ne_of_gt hξ_norm_pos)]
      -- ξ₀ ∈ unit sphere
      have hξ₀_sphere : ξ₀ ∈ Metric.sphere (0 : E d) 1 := by
        rw [Metric.mem_sphere, dist_zero_right]; exact hξ₀_norm
      -- (x, ξ₀) ∈ V₂ ×ˢ W ⊆ V_prod, so hessianQuadForm f x ξ₀ ≥ -ε₀
      have hbound₀ : hessianQuadForm f x ξ₀ ≥ -ε₀ := by
        have := hg_bound (x, ξ₀) (hVW (Set.mk_mem_prod hx (hSphere_W hξ₀_sphere)))
        linarith
      -- ξ = c • ξ₀
      have hξ_eq : ξ = c • ξ₀ := by
        rw [hξ₀_def, smul_smul, mul_inv_cancel₀ (ne_of_gt hξ_norm_pos), one_smul]
      -- Homogeneity: hessianQuadForm f x ξ = c² * hessianQuadForm f x ξ₀
      have hhomog : hessianQuadForm f x ξ = c ^ 2 * hessianQuadForm f x ξ₀ := by
        conv_lhs => rw [hξ_eq]
        simp only [hessianQuadForm, map_smul, real_inner_smul_left, real_inner_smul_right]
        ring
      -- c² * hessianQuadForm f x ξ₀ ≥ c² * (-ε₀) = -ε₀ * ‖ξ‖²
      rw [hhomog]
      have hc_sq_nonneg : (0 : ℝ) ≤ c ^ 2 := sq_nonneg c
      nlinarith [hbound₀, hc_sq_nonneg]
  -- ================================================================
  -- Step 3: Construct fiber-saturated U₊ ⊂⊂ V₁ ∩ V₂ ∩ U
  -- ================================================================
  -- V₁ ∩ V₂ ∩ U is an open neighborhood of m_star (since m_star ∈ S ⊆ each).
  -- By the tubular neighborhood structure, we extract a fiber-saturated
  -- open set U₊ with compact closure inside V₁ ∩ V₂ ∩ U.
  obtain ⟨U_plus, hU_open, hm_in, hU_compact, hU_cl_U, hU_convex,
          hU_V₁, hU_V₂, hU_fiber_V₁, hU_fiber_U⟩ :
      ∃ U_plus : Set (E d), IsOpen U_plus ∧ m_star ∈ U_plus ∧
        IsCompact (closure U_plus) ∧ closure U_plus ⊆ U ∧
        Convex ℝ U_plus ∧
        U_plus ⊆ V₁ ∧ U_plus ⊆ V₂ ∧
        (∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          π x + t • (x - π x) ∈ V₁) ∧
        (∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          π x + t • (x - π x) ∈ U) := by
    -- V₁ ∩ V₂ ∩ U is open and contains m⋆
    have hW_open : IsOpen (V₁ ∩ V₂ ∩ U) := (hV₁_open.inter hV₂_open).inter hTub_sub.isOpen
    have hm_in_W : m_star ∈ V₁ ∩ V₂ ∩ U :=
      ⟨⟨hm_V₁, hm_V₂⟩, hTub_sub.subset hm_star⟩
    obtain ⟨r, hr_pos, hball_sub⟩ := Metric.isOpen_iff.mp hW_open m_star hm_in_W
    -- Take U₊ = B(m⋆, r/2)
    refine ⟨Metric.ball m_star (r / 2), Metric.isOpen_ball,
            Metric.mem_ball_self (by linarith), ?_, ?_, convex_ball _ _, ?_, ?_, ?_, ?_⟩
    -- (1) IsCompact (closure (ball m⋆ (r/2))): bounded in proper space
    · exact Metric.isBounded_ball.isCompact_closure
    -- (2) closure (ball m⋆ (r/2)) ⊆ U
    · intro y hy
      have h_in_cl : y ∈ Metric.closedBall m_star (r / 2) :=
        closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hy
      have : dist y m_star < r :=
        lt_of_le_of_lt (Metric.mem_closedBall.mp h_in_cl) (by linarith)
      exact (hball_sub (Metric.mem_ball.mpr this)).2
    -- (3) ball m⋆ (r/2) ⊆ V₁
    · exact fun x hx =>
        (hball_sub (Metric.ball_subset_ball (by linarith : r / 2 ≤ r) hx)).1.1
    -- (4) ball m⋆ (r/2) ⊆ V₂
    · exact fun x hx =>
        (hball_sub (Metric.ball_subset_ball (by linarith : r / 2 ≤ r) hx)).1.2
    -- (5) fiber segments from ball(m_star, r/2) stay in V₁
    · intro x hx t ht0 ht1
      have hx_ball_r : x ∈ Metric.ball m_star r :=
        Metric.ball_subset_ball (by linarith : r / 2 ≤ r) hx
      have hxU : x ∈ U := (hball_sub hx_ball_r).2
      obtain ⟨hπx_S, hπx_dist⟩ := hπ_proj x hxU
      have hπx_ball : π x ∈ Metric.ball m_star r := by
        rw [Metric.mem_ball]
        have h1 : dist x (π x) < r / 2 := by
          calc dist x (π x) = Metric.infDist x S := hπx_dist
            _ ≤ dist x m_star := Metric.infDist_le_dist_of_mem hm_star
            _ < r / 2 := Metric.mem_ball.mp hx
        have h2 : dist x m_star < r / 2 := Metric.mem_ball.mp hx
        linarith [dist_triangle (π x) x m_star, dist_comm (π x) x]
      suffices π x + t • (x - π x) ∈ Metric.ball m_star r from
        (hball_sub this).1.1
      have hy_eq : π x + t • (x - π x) = (1 - t) • π x + t • x := by
        simp only [smul_sub, sub_smul, one_smul]; abel
      rw [hy_eq]
      exact convex_ball m_star r hπx_ball hx_ball_r (by linarith) ht0 (by linarith)
    -- (6) fiber segments from ball(m_star, r/2) stay in U
    · intro x hx t ht0 ht1
      have hx_ball_r : x ∈ Metric.ball m_star r :=
        Metric.ball_subset_ball (by linarith : r / 2 ≤ r) hx
      have hxU : x ∈ U := (hball_sub hx_ball_r).2
      obtain ⟨hπx_S, hπx_dist⟩ := hπ_proj x hxU
      have hπx_ball : π x ∈ Metric.ball m_star r := by
        rw [Metric.mem_ball]
        have h1 : dist x (π x) < r / 2 := by
          calc dist x (π x) = Metric.infDist x S := hπx_dist
            _ ≤ dist x m_star := Metric.infDist_le_dist_of_mem hm_star
            _ < r / 2 := Metric.mem_ball.mp hx
        have h2 : dist x m_star < r / 2 := Metric.mem_ball.mp hx
        linarith [dist_triangle (π x) x m_star, dist_comm (π x) x]
      suffices π x + t • (x - π x) ∈ Metric.ball m_star r from
        (hball_sub this).2
      have hy_eq : π x + t • (x - π x) = (1 - t) • π x + t • x := by
        simp only [smul_sub, sub_smul, one_smul]; abel
      rw [hy_eq]
      exact convex_ball m_star r hπx_ball hx_ball_r (by linarith) ht0 (by linarith)
  obtain ⟨π', hπ'_proj, _, _, _, _, hπ'_fiber_dist, hπ'_normal, _, _, _⟩ :=
    tubular_neighborhood_projection_Ed hTub_sub ⟨m_star, hm_star⟩
  have hπ_eq_U : ∀ x ∈ U, π x = π' x := by
    intro x hxU
    obtain ⟨p, hp, huniq⟩ := hTub_sub.uniqueProj x hxU
    exact (huniq (π x) (hπ_proj x hxU)).trans
      (huniq (π' x) ⟨(hπ'_proj x hxU).1,
        by rw [dist_eq_norm]; exact (hπ'_proj x hxU).2⟩).symm
  have hfderiv_normal : ∀ x ∈ U_plus, fderiv ℝ π (π x) (x - π x) = 0 := by
    intro x hx
    have hxU : x ∈ U := hU_cl_U (subset_closure hx)
    have hm_S := (hπ_proj x hxU).1
    have hmU : π x ∈ U := hTub_sub.subset hm_S
    have hπ_eq_nhds : π =ᶠ[𝓝 (π x)] π' :=
      Filter.eventually_of_mem (hTub_sub.isOpen.mem_nhds hmU) hπ_eq_U
    rw [hπ_eq_nhds.fderiv_eq, hπ_eq_U x hxU]
    exact hπ'_normal x hxU
  have hπ_fiber_const : ∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      π (π x + t • (x - π x)) = π x := by
    intro x hx t ht0 ht1
    have hxU : x ∈ U := hU_cl_U (subset_closure hx)
    have hm_S := (hπ_proj x hxU).1
    set y := π x + t • (x - π x) with hy_def
    -- Local fiber-in-U proof: convexity of ball ensures y ∈ U
    have hyU : y ∈ U := hU_fiber_U x hx t ht0 ht1
    have hy_conv : y = (1 - t) • π' x + t • x := by
      rw [hy_def, hπ_eq_U x hxU]; simp only [smul_sub, sub_smul, one_smul]; abel
    have h_realizes : ‖y - π x‖ = Metric.infDist y S := by
      rw [hy_conv, hπ_eq_U x hxU]; exact hπ'_fiber_dist x hxU t ⟨ht0, ht1⟩
    obtain ⟨p, hp, huniq⟩ := hTub_sub.uniqueProj y hyU
    exact (huniq (π y) (hπ_proj y hyU)).trans
      (huniq (π x) ⟨hm_S, by rw [dist_eq_norm]; exact h_realizes⟩).symm
  -- ================================================================
  -- Step 4: Assemble the conclusion
  -- ================================================================
  refine ⟨U_plus, ε₀, hU_open, hm_in, hU_compact, hU_cl_U, hU_convex,
          hε₀_pos, hε₀_le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- ----------------------------------------------------------------
  -- (a) Normal Hessian lower bound: inherited from V₁
  -- ----------------------------------------------------------------
  · exact fun x hx ξ hξ => h_normal_V₁ x (hU_V₁ hx) ξ hξ
  -- ----------------------------------------------------------------
  -- (b) Quadratic growth: f(x) - f⋆ ≥ (μ/8)·dist(x,S)²
  -- ----------------------------------------------------------------
  · intro x hx
    -- Define the fiber path φ(t) = f(π(x) + t·(x − π(x)))
    set m := π x with hm_def
    set e := x - m with he_def
    set φ : ℝ → ℝ := fun t => f (m + t • e) with hφ_def
    -- φ(0) = f(π(x)) = f⋆ since π(x) ∈ S = argmin f
    have hφ0 : φ 0 = fStar f := by
      simp only [hφ_def, zero_smul, add_zero]
      have hxU : x ∈ U := hU_cl_U (subset_closure hx)
      have hm_min : ∀ y, f m ≤ f y := by
        have := (hπ_proj x hxU).1; rw [hM_argmin] at this; exact this
      unfold fStar
      exact le_antisymm (le_ciInf hm_min)
        (ciInf_le ⟨f m, fun _ ⟨y, hy⟩ => hy ▸ hm_min y⟩ m)
    -- φ(1) = f(m + 1·e) = f(m + (x − m)) = f(x)
    have hφ1 : φ 1 = f x := by
      simp only [hφ_def, one_smul, he_def]; congr 1; abel
    -- φ'(0) = ⟨∇f(m), e⟩ = 0, since ∇f vanishes on S
    have hxU : x ∈ U := hU_cl_U (subset_closure hx)
    have hm_S : m ∈ S := (hπ_proj x hxU).1
    have hm_U : m ∈ U := hTub_sub.subset hm_S
    have hf_diff_on : DifferentiableOn ℝ f U :=
      hf_C2.differentiableOn two_ne_zero
    have hf_da : DifferentiableAt ℝ f m :=
      hf_diff_on.differentiableAt (hTub_sub.isOpen.mem_nhds hm_U)
    have hφ'0 : deriv φ 0 = 0 := by
      have hg : HasDerivAt (fun t : ℝ => m + t • e) e 0 := by
        simpa [one_smul, zero_add] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add m
      have hf_da' : DifferentiableAt ℝ f (m + (0 : ℝ) • e) := by
        simp only [zero_smul, add_zero]; exact hf_da
      have key := hf_da'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
      simp only [Function.comp_def] at key
      rw [key.deriv, show m + (0 : ℝ) • e = m from by simp only [zero_smul, add_zero],
          ← inner_gradient_left (𝕜 := ℝ) (f := f) (x := m) (y := e),
          hgrad_zero m hm_S, inner_zero_left]
    -- φ is C² at each point of [0,1] (fiber_path_C2at_on_segment)
    have hseg_U : ∀ t : ℝ, t ∈ Set.Icc 0 1 → m + t • e ∈ U := by
      intro t ⟨ht0, ht1⟩
      have : m + t • e = π x + t • (x - π x) := by simp only [hm_def, he_def]
      rw [this]
      exact hU_fiber_U x hx t ht0 ht1
    have hφ_C2at := fiber_path_C2at_on_segment f m e hU_is_open hf_C2 hseg_U
    -- Derive local regularity from pointwise ContDiffAt ℝ 2
    have hφ_cont : ContinuousOn φ (Set.Icc 0 1) :=
      fun t ht => (hφ_C2at t ht).continuousAt.continuousWithinAt
    have hφ_diffon : DifferentiableOn ℝ φ (Set.Ioo 0 1) :=
      fun t ht => ((hφ_C2at t (Set.Ioo_subset_Icc_self ht)).differentiableAt
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableWithinAt
    have hφ'_cont : ContinuousOn (deriv φ) (Set.Icc 0 1) := by
      intro t ht
      have hfda := (hφ_C2at t ht).fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
      have h_eq : deriv φ = fun s => fderiv ℝ φ s 1 := by
        ext s; exact fderiv_apply_one_eq_deriv.symm
      rw [h_eq]; exact (hfda.continuousAt.clm_apply continuousAt_const).continuousWithinAt
    have hφ'_diffon : DifferentiableOn ℝ (deriv φ) (Set.Ioo 0 1) := by
      intro t ht
      have hfda := (hφ_C2at t (Set.Ioo_subset_Icc_self ht)).fderiv_right
        (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
      have hfda_diff := hfda.differentiableAt (show (1 : WithTop ℕ∞) ≠ 0 by norm_num)
      have h_eq : deriv φ = fun s => fderiv ℝ φ s 1 := by
        ext s; exact fderiv_apply_one_eq_deriv.symm
      rw [h_eq]; exact (hfda_diff.clm_apply (differentiableAt_const _)).differentiableWithinAt
    -- φ''(t) = eᵀ D²f(m+te) e ≥ (μ/4)‖e‖² (by normal Hessian bound on U₊,
    -- since e = x − π(x) is a normal direction and m+te ∈ U₊ by fiber saturation)
    have hφ''_lb : ∀ t, 0 ≤ t → t ≤ 1 →
        deriv (deriv φ) t ≥ μ' * ‖e‖ ^ 2 :=
      fiber_path_hessian_lower_bound f μ' m e hU_is_open hf_C2 hseg_U
        (fun t ht0 ht1 => by
          exact h_normal_V₁ _ (hU_fiber_V₁ x hx t ht0 ht1) e (by
            rw [hπ_fiber_const x hx t ht0 ht1]
            exact hfderiv_normal x hx))
    -- By quadratic_growth_from_hessian: φ(1) − φ(0) ≥ ((μ/4)·‖e‖²)/2
    have hgrowth := quadratic_growth_from_hessian φ (μ' * ‖e‖ ^ 2)
      hφ_cont hφ_diffon hφ'_cont hφ'_diffon hφ'0 hφ''_lb
    rw [hφ1, hφ0] at hgrowth
    -- dist(x, S) = ‖x − π(x)‖ = ‖e‖ by the projection property
    have hdist : Metric.infDist x S = ‖e‖ := by
      have hxU : x ∈ U := hU_cl_U (subset_closure hx)
      rw [← (hπ_proj x hxU).2, dist_eq_norm]
    rw [hdist]
    have : μ' * ‖e‖ ^ 2 / 2 = μ' / 2 * ‖e‖ ^ 2 := by ring
    linarith
  -- ----------------------------------------------------------------
  -- (c) Strong aiming: ⟨∇f(x), x−π(x)⟩ ≥ f(x)−f⋆ + (μ/8)‖x−π(x)‖²
  -- ----------------------------------------------------------------
  · intro x hx
    -- Same fiber path as in (b)
    set m := π x with hm_def
    set e := x - m with he_def
    set φ : ℝ → ℝ := fun t => f (m + t • e) with hφ_def
    have hφ0 : φ 0 = fStar f := by
      simp only [hφ_def, zero_smul, add_zero]
      have hxU : x ∈ U := hU_cl_U (subset_closure hx)
      have hm_min : ∀ y, f m ≤ f y := by
        have := (hπ_proj x hxU).1; rw [hM_argmin] at this; exact this
      unfold fStar
      exact le_antisymm (le_ciInf hm_min)
        (ciInf_le ⟨f m, fun _ ⟨y, hy⟩ => hy ▸ hm_min y⟩ m)
    have hφ1 : φ 1 = f x := by
      simp only [hφ_def, one_smul, he_def]; congr 1; abel
    have hxU : x ∈ U := hU_cl_U (subset_closure hx)
    have hm_S : m ∈ S := (hπ_proj x hxU).1
    have hm_U : m ∈ U := hTub_sub.subset hm_S
    have hf_diff_on : DifferentiableOn ℝ f U :=
      hf_C2.differentiableOn two_ne_zero
    have hf_da_m : DifferentiableAt ℝ f m :=
      hf_diff_on.differentiableAt (hTub_sub.isOpen.mem_nhds hm_U)
    have hf_da_x : DifferentiableAt ℝ f x :=
      hf_diff_on.differentiableAt (hTub_sub.isOpen.mem_nhds hxU)
    have hφ'0 : deriv φ 0 = 0 := by
      have hg : HasDerivAt (fun t : ℝ => m + t • e) e 0 := by
        simpa [one_smul, zero_add] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add m
      have hf_da' : DifferentiableAt ℝ f (m + (0 : ℝ) • e) := by
        simp only [zero_smul, add_zero]; exact hf_da_m
      have key := hf_da'.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hg
      simp only [Function.comp_def] at key
      rw [key.deriv, show m + (0 : ℝ) • e = m from by simp only [zero_smul, add_zero],
          ← inner_gradient_left (𝕜 := ℝ) (f := f) (x := m) (y := e),
          hgrad_zero m hm_S, inner_zero_left]
    have hseg_U : ∀ t : ℝ, t ∈ Set.Icc 0 1 → m + t • e ∈ U := by
      intro t ⟨ht0, ht1⟩
      have : m + t • e = π x + t • (x - π x) := by simp only [hm_def, he_def]
      rw [this]
      exact hU_fiber_U x hx t ht0 ht1
    have hφ_C2at := fiber_path_C2at_on_segment f m e hU_is_open hf_C2 hseg_U
    have hφ_cont : ContinuousOn φ (Set.Icc 0 1) :=
      fun t ht => (hφ_C2at t ht).continuousAt.continuousWithinAt
    have hφ_diffon : DifferentiableOn ℝ φ (Set.Ioo 0 1) :=
      fun t ht => ((hφ_C2at t (Set.Ioo_subset_Icc_self ht)).differentiableAt
        (by norm_num : (2 : WithTop ℕ∞) ≠ 0)).differentiableWithinAt
    have hφ'_cont : ContinuousOn (deriv φ) (Set.Icc 0 1) := by
      intro t ht
      have hfda := (hφ_C2at t ht).fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
      have h_eq : deriv φ = fun s => fderiv ℝ φ s 1 := by
        ext s; exact fderiv_apply_one_eq_deriv.symm
      rw [h_eq]; exact (hfda.continuousAt.clm_apply continuousAt_const).continuousWithinAt
    have hφ'_diffon : DifferentiableOn ℝ (deriv φ) (Set.Ioo 0 1) := by
      intro t ht
      have hfda := (hφ_C2at t (Set.Ioo_subset_Icc_self ht)).fderiv_right
        (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
      have hfda_diff := hfda.differentiableAt (show (1 : WithTop ℕ∞) ≠ 0 by norm_num)
      have h_eq : deriv φ = fun s => fderiv ℝ φ s 1 := by
        ext s; exact fderiv_apply_one_eq_deriv.symm
      rw [h_eq]; exact (hfda_diff.clm_apply (differentiableAt_const _)).differentiableWithinAt
    have hφ''_lb : ∀ t, 0 ≤ t → t ≤ 1 →
        deriv (deriv φ) t ≥ μ' * ‖e‖ ^ 2 :=
      fiber_path_hessian_lower_bound f μ' m e hU_is_open hf_C2 hseg_U
        (fun t ht0 ht1 => by
          exact h_normal_V₁ _ (hU_fiber_V₁ x hx t ht0 ht1) e (by
            rw [hπ_fiber_const x hx t ht0 ht1]
            exact hfderiv_normal x hx))
    -- By strong_aiming_from_hessian: φ'(1) ≥ (φ(1)−φ(0)) + ((μ/4)·‖e‖²)/2
    have hsa := strong_aiming_from_hessian φ (μ' * ‖e‖ ^ 2)
      hφ_cont hφ_diffon hφ'_cont hφ'_diffon hφ'0 hφ''_lb
    -- φ'(1) = ⟨∇f(x), e⟩ by fiber_deriv
    have hφ'1 : deriv φ 1 = @inner ℝ _ _ (gradient f x) e := by
      have hg : HasDerivAt (fun t : ℝ => m + t • e) e 1 := by
        simpa [one_smul] using ((hasDerivAt_id (1 : ℝ)).smul_const e).const_add m
      have hme1 : m + (1 : ℝ) • e = x := by simp only [he_def, one_smul, add_sub_cancel]
      have hf_da' : DifferentiableAt ℝ f (m + (1 : ℝ) • e) := by rw [hme1]; exact hf_da_x
      have key := hf_da'.hasFDerivAt.comp_hasDerivAt (1 : ℝ) hg
      simp only [Function.comp_def] at key
      rw [key.deriv, hme1]
      exact (inner_gradient_left (𝕜 := ℝ) (f := f) (x := x) (y := e)).symm
    rw [hφ1, hφ0, hφ'1] at hsa
    -- e = x − π(x), so the inner products match; convert (c/2) form
    have : μ' * ‖e‖ ^ 2 / 2 = μ' / 2 * ‖e‖ ^ 2 := by ring
    linarith
  -- ----------------------------------------------------------------
  -- (d) Hessian lower bound D²f(x) ≽ −ε₀·I: inherited from V₂
  -- ----------------------------------------------------------------
  · exact fun x hx ξ => h_hess_V₂ x (hU_V₂ hx) ξ
  -- ----------------------------------------------------------------
  -- (e) Normal Hessian ≥ μ at m_star (from Step 1)
  -- ----------------------------------------------------------------
  · exact h_normal_hess_M m_star hm_star
  -- ----------------------------------------------------------------
  -- (f) Fiber segments from U₊ stay in U
  -- ----------------------------------------------------------------
  · exact hU_fiber_U


/-- Public theorem wrapper for `localFiberwiseGeometryProof`. -/
theorem local_fiberwise_geometry
    -- Dimensions
    {d : ℕ} (_hd : 0 < d)
    -- The objective function
    (f : E d → ℝ)
    -- Smoothness parameters
    (L : ℝ≥0) (_hL : 0 < (L : ℝ))
    (μ : ℝ) (hμ : 0 < μ)
    -- Slack parameter μ' ∈ (0, μ), used to leave room for local perturbations.
    (μ' : ℝ) (hμ' : 0 < μ') (hμ'_lt : μ' < μ)
    -- Step size
    (η : ℝ) (_hη : η = 1 / (L : ℝ)) (hη_pos : 0 < η)
    -- The minimizer set S = argmin f
    (S : Set (E d))
    (hM_argmin : S = argminSet f)
    -- Tubular neighborhood U ⊃ S (open set with unique projection + C² submanifold structure)
    (U : Set (E d))
    (hTub_sub : IsTubularNeighborhoodOfSubmanifold S U)
    -- PL condition on U
    (hPL : PolyakLojasiewicz f μ U)
    -- f is C² on U
    (hf_C2 : ContDiffOn ℝ 2 f U)
    -- Nearest-point projection on U
    (π : E d → E d)
    (hπ_proj : ∀ x ∈ U, π x ∈ S ∧ dist x (π x) = Metric.infDist x S)
    -- Gradient vanishes on S
    (hgrad_zero : ∀ x ∈ S, gradient f x = 0)
    -- Base point on M
    (m_star : E d) (hm_star : m_star ∈ S) :
    -- Conclusion: ∃ neighborhood U₊ and ε with all four properties for μ'
    ∃ (U_plus : Set (E d)) (ε : ℝ),
      -- U₊ is open, contains m⋆, and U₊ ⊂⊂ U (compact closure inside U)
      IsOpen U_plus ∧ m_star ∈ U_plus ∧
      IsCompact (closure U_plus) ∧ closure U_plus ⊆ U ∧
      Convex ℝ U_plus ∧
      -- ε > 0 with ε ≤ √(μ/(4η))
      0 < ε ∧ ε ≤ Real.sqrt (μ' / η) ∧
      -- (a) Normal Hessian lower bound: for ξ in ker(Dπ(π x))
      (∀ x ∈ U_plus, ∀ ξ : E d,
        fderiv ℝ π (π x) ξ = 0 →
        hessianQuadForm f x ξ ≥ μ' * ‖ξ‖ ^ 2) ∧
      -- (b) Quadratic growth
      (∀ x ∈ U_plus,
        f x - fStar f ≥ μ' / 2 * (Metric.infDist x S) ^ 2) ∧
      -- (c) Strong aiming
      (∀ x ∈ U_plus,
        @inner ℝ _ _ (gradient f x) (x - π x) ≥
          f x - fStar f + μ' / 2 * ‖x - π x‖ ^ 2) ∧
      -- (d) Hessian lower bound D²f(x) ≽ -εI
      (∀ x ∈ U_plus, ∀ ξ : E d,
        hessianQuadForm f x ξ ≥ -ε * ‖ξ‖ ^ 2) ∧
      -- (e) Normal Hessian ≥ μ at m_star (full μ bound at the base point)
      (∀ ξ : E d,
        fderiv ℝ π m_star ξ = 0 →
        hessianQuadForm f m_star ξ ≥ μ * ‖ξ‖ ^ 2) ∧
      -- (f) Fiber segments from U₊ stay in U
      (∀ x ∈ U_plus, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        π x + t • (x - π x) ∈ U) := by
  exact localFiberwiseGeometryProof (d := d) (_hd := _hd) (f := f) (L := L) (_hL := _hL) (μ := μ)
    (hμ := hμ) (μ' := μ') (hμ' := hμ') (hμ'_lt := hμ'_lt) (η := η) (_hη := _hη) (hη_pos := hη_pos)
    (S := S) (hM_argmin := hM_argmin) (U := U) (hTub_sub := hTub_sub) (hPL := hPL) (hf_C2 := hf_C2)
    (π := π) (hπ_proj := hπ_proj) (hgrad_zero := hgrad_zero) (m_star := m_star) (hm_star := hm_star)

end PLAcceleratedNesterovLean
