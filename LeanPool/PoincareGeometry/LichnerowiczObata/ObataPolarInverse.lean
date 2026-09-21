/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataRegularRoundComparison
public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarInverseDifferentiability
public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothObataPolar
public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothPolarInverse
public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarComparisonMetric

/-! # Smoothness of the constructed regular Obata coordinates -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur TopologicalSpace
open scoped Manifold ContDiff Topology

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {n : ℕ} [hDimension : Fact (Module.finrank ℝ E = n + 1)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [PreconnectedSpace M]
  [CompactSpace M] [T2Space M] [Nonempty M]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)

local instance tangentFinrank (p : M) : Fact (Module.finrank ℝ (TM p) = n + 1) :=
  ⟨show Module.finrank ℝ E = n + 1 from Fact.out⟩

/-- The Obata Hessian equation yields a single regular polar chart whose
inverse is smooth on the entire regular region. The coordinate
homeomorphism in the conclusion is the one used to construct the chart. -/
theorem exists_obata_differentiable_polar_inverse
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    ∃ Φ : TM p × ℝ → M,
      HasRadialPoleModel I Φ p ∧
      ∃ Q : Metric.sphere (0 : TM p) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
      ∃ e : OpenPartialHomeomorph (Metric.sphere (0 : TM p) 1 × ℝ) M,
        e.source = {q | q.2 ∈ Ioo 0 (Real.pi / Real.sqrt K)} ∧
        e.target = {x | -a < f x ∧ f x < a} ∧
        (∀ q, (Q q : M) = Φ (q.1, q.2)) ∧
        (∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          obataRadial K a f (Φ (u, r)) = r) ∧
        (∀ u : Metric.sphere (0 : TM p) 1,
          IsMIntegralCurveOn (fun r => Φ (u, r)) (gradient (I := I) (obataRadial K a f))
            (Ioo 0 (Real.pi / Real.sqrt K))) ∧
        (∀ q ∈ e.source, e q = Φ (q.1, q.2)) ∧
        (∀ y : {x : M // -a < f x ∧ f x < a},
          e.symm (y : M) = ((Q.symm y).1, ((Q.symm y).2 : ℝ))) ∧
        (∀ y, -a < f y ∧ f y < a →
          ContMDiffAt I ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞ e.symm y) ∧
        ∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          MDifferentiableAt 𝓘(ℝ, TM p × ℝ) I Φ (u, r) ∧
          Set.InjOn (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r))
            {q : TM p × ℝ | inner ℝ (u : TM p) q.1 = 0} ∧
          ∀ w v : TM p, inner ℝ (u : TM p) w = 0 → inner ℝ (u : TM p) v = 0 →
            ∀ s t : ℝ,
              inner ℝ (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r) (w, s))
                (mfderiv 𝓘(ℝ, TM p × ℝ) I Φ (u, r) (v, t)) =
              inner ℝ (fderiv ℝ (fun q : TM p × ℝ => roundPolarCurve (1 / Real.sqrt K)
                  roundNorth (roundAngularInclusion q.1) q.2) (u, r) (w, s))
                (fderiv ℝ (fun q : TM p × ℝ => roundPolarCurve (1 / Real.sqrt K)
                  roundNorth (roundAngularInclusion q.1) q.2) (u, r) (v, t)) := by
  obtain ⟨Φ, hpole, Q, F, G, hG, hQ, hradial, hcurves, hF, hjet⟩ :=
    exists_obata_regular_round_comparison hf hnon hK ha hH c hz hcrit hmax
  let p := (extChartAt I c).symm z
  let J : Opens ℝ := ⟨Ioo 0 (Real.pi / Real.sqrt K), isOpen_Ioo⟩
  let U : Opens M := ⟨{x | -a < f x ∧ f x < a},
    (isOpen_lt continuous_const hf.continuous).inter
      (isOpen_lt hf.continuous continuous_const)⟩
  have hDim : Module.finrank ℝ E = n + 1 := Fact.out
  let : Nontrivial (TM p) := Module.nontrivial_of_finrank_eq_succ (R := ℝ) hDim
  obtain ⟨u, hu⟩ := NormedSpace.sphere_nonempty (E := TM p) |>.mpr (show (0 : ℝ) ≤ 1 by norm_num)
  have hL : 0 < Real.pi / Real.sqrt K := div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)
  let r : J := ⟨(Real.pi / Real.sqrt K) / 2, by change 0 < _ ∧ _ < _; constructor <;> linarith⟩
  have hSmooth : ∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ J,
      ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : Metric.sphere (0 : TM p) 1 × ℝ => Φ (q.1, q.2)) (u, r) := by
    intro u r hr
    apply hpole.contMDiffAt_obata_polar hf hnon hK ha hH hcrit
      ((hmax _).mpr rfl) ?_ hradial hcurves u hr
    intro v s hs
    have he := hQ (v, ⟨s, hs⟩)
    rw [← he]
    exact (Q (v, ⟨s, hs⟩)).property
  obtain ⟨e, hs, ht, he, hi, hd⟩ := exists_smooth_polar_inverse_on_target
    (I := I) (n := n) J U Q (⟨u, hu⟩, r) Φ hQ hDim hSmooth
    (fun u r hr => ⟨(hjet u r hr).1, (hjet u r hr).2.1⟩)
  exact ⟨Φ, hpole, Q, e, hs, ht, hQ, hradial, hcurves, he, hi, hd, hjet⟩

include hDimension in
/-- A single regular comparison to the punctured round sphere has a smooth
forward ambient extension and a differentiable inverse extension. Its forward
derivative preserves the Riemannian inner product on every regular tangent
space. The same comparison retains its differentiable north-pole inverse
extension and its north-pole tangent metric; no south-pole assertion is made here. -/
theorem exists_obata_regular_forward_differentiable
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c : M) {z : E} (hz : z ∈ (extChartAt I c).target)
    (hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z) :
    let p := (extChartAt I c).symm z
    ∃ F : {x : M // -a < f x ∧ f x < a} ≃ₜ
        RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
      HasRoundNorthInverseExtension I K F p ∧
      ∃ T : M → RoundAmbient (TM p),
        (∀ y : {x : M // -a < f x ∧ f x < a},
          T (y : M) = ((F y).1 : RoundAmbient (TM p)) ∧
          ContMDiffAt I 𝓘(ℝ, RoundAmbient (TM p)) ∞ T (y : M) ∧
          ∀ v w : TM (y : M),
            inner ℝ (mfderiv I 𝓘(ℝ, RoundAmbient (TM p)) T (y : M) v)
              (mfderiv I 𝓘(ℝ, RoundAmbient (TM p)) T (y : M) w) = inner ℝ v w) ∧
        (∀ y : {x : M // -a < f x ∧ f x < a},
          obataRadial K a f (y : M) =
            (intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
              ((F y).1 : RoundAmbient (TM p))).2) ∧
        ∃ G : RoundAmbient (TM p) → M,
          ∀ x : RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient (TM p)),
            G (x.1 : RoundAmbient (TM p)) = (F.symm x : M) ∧
            MDifferentiableAt 𝓘(ℝ, RoundAmbient (TM p)) I G (x.1 : RoundAmbient (TM p)) := by
  obtain ⟨Φ, hpole, Q, e, hs, ht, hQ, hradial, hcurves, he, hi, hd, hjet⟩ :=
    exists_obata_differentiable_polar_inverse (n := n) hf hnon hK ha hH c hz hcrit hmax
  let p := (extChartAt I c).symm z
  let Ψ := fun q : TM p × ℝ => roundPolarCurve (1 / Real.sqrt K)
    roundNorth (roundAngularInclusion q.1) q.2
  let Ψₛ := fun q : Metric.sphere (0 : TM p) 1 × ℝ => Ψ (q.1, q.2)
  let F := Q.symm.trans (curvatureRoundPolarHomeomorph hK)
  let T := Ψₛ ∘ e.symm
  let : FiniteDimensional ℝ (TM p) := inferInstanceAs (FiniteDimensional ℝ E)
  let : CompleteSpace (TM p) := FiniteDimensional.complete ℝ _
  refine ⟨F, hpole.round_north_inverse_extension hK Q hQ, T, ?_, ?_, ?_⟩
  · intro y
    refine ⟨?_, ?_⟩
    · change Ψₛ (e.symm (y : M)) = _
      rw [hi y]
      exact (curvatureRoundPolarHomeomorph_apply hK (Q.symm y)).symm
    · have hΨ : ContMDiffAt 𝓘(ℝ, TM p × ℝ) 𝓘(ℝ, RoundAmbient (TM p)) ∞
          Ψ ((e.symm (y : M)).1, (e.symm (y : M)).2) := by
        apply contMDiffAt_iff_contDiffAt.mpr
        dsimp only [Ψ, roundPolarCurve]
        fun_prop
      have hΨₛ : ContMDiffAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, RoundAmbient (TM p)) ∞
          Ψₛ (e.symm (y : M)) := by
        have hc : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TM p × ℝ) ∞
            (fun q : Metric.sphere (0 : TM p) 1 × ℝ => ((q.1 : TM p), q.2)) := by
          have hcoe : ContMDiff (𝓡 n) 𝓘(ℝ, TM p) ∞
              (Subtype.val : Metric.sphere (0 : TM p) 1 → TM p) := contMDiff_coe_sphere
          have hfst : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, TM p) ∞
              (fun q : Metric.sphere (0 : TM p) 1 × ℝ => (q.1 : TM p)) :=
            hcoe.comp contMDiff_fst
          exact hfst.prodMk_space (contMDiff_snd : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
            (Prod.snd : Metric.sphere (0 : TM p) 1 × ℝ → ℝ))
        exact hΨ.comp (f := fun q : Metric.sphere (0 : TM p) 1 × ℝ => ((q.1 : TM p), q.2))
          (e.symm (y : M)) (hc _)
      have hTy := hΨₛ.comp (y : M) (hd y y.property)
      refine ⟨hTy, ?_⟩
      let q := Q.symm y
      have hqy : Φ ((q.1 : TM p), (q.2 : ℝ)) = (y : M) := by
        rw [← hQ q]
        exact congrArg (fun x : {x : M // -a < f x ∧ f x < a} => (x : M))
          (Q.apply_symm_apply y)
      have hTq : MDifferentiableAt I 𝓘(ℝ, RoundAmbient (TM p)) T
          (Φ ((q.1 : TM p), (q.2 : ℝ))) := by
        rw [hqy]
        exact hTy.mdifferentiableAt (by norm_num)
      have hΨq : MDifferentiableAt 𝓘(ℝ, TM p × ℝ) 𝓘(ℝ, RoundAmbient (TM p))
          Ψ ((q.1 : TM p), (q.2 : ℝ)) := by
        apply mdifferentiableAt_iff_differentiableAt.mpr
        dsimp only [Ψ, roundPolarCurve]
        fun_prop
      have hsource : (q.1, (q.2 : ℝ)) ∈ e.source := by rw [hs]; exact q.2.property
      have hlocal : (fun b : Metric.sphere (0 : TM p) 1 × ℝ => T (Φ (b.1, b.2)))
          =ᶠ[𝓝 (q.1, (q.2 : ℝ))] Ψₛ := by
        filter_upwards [e.open_source.mem_nhds hsource] with b hb
        change Ψₛ (e.symm (Φ (b.1, b.2))) = Ψₛ b
        rw [← he b hb, e.left_inv hb]
      have hmetricq := polar_comparison_derivative_inner q.1 (q.2 : ℝ)
        (show Module.finrank ℝ E = n + 1 from Fact.out)
        (hjet q.1 q.2 q.2.property).1 hΨq hTq (hjet q.1 q.2 q.2.property).2.1
        (by
          intro w v hw hv s t
          rw [mfderiv_eq_fderiv]
          exact (hjet q.1 q.2 q.2.property).2.2 w v hw hv s t) hlocal
      change ∀ v w : TM (Φ ((q.1 : TM p), (q.2 : ℝ))),
        inner ℝ (mfderiv I 𝓘(ℝ, RoundAmbient (TM p)) T (Φ ((q.1 : TM p), (q.2 : ℝ))) v)
          (mfderiv I 𝓘(ℝ, RoundAmbient (TM p)) T (Φ ((q.1 : TM p), (q.2 : ℝ))) w) =
          inner ℝ v w at hmetricq
      rw [hqy] at hmetricq
      exact hmetricq
  · intro y
    change obataRadial K a f (y : M) =
      (intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
        (((curvatureRoundPolarHomeomorph hK) (Q.symm y)).1 : RoundAmbient (TM p))).2
    rw [intrinsicRoundInverseCoordinates_apply hK]
    have hρ := hradial (Q.symm y).1 (Q.symm y).2 (Q.symm y).2.property
    rw [← hQ (Q.symm y), Q.apply_symm_apply] at hρ
    exact hρ
  · let G := Φ ∘ intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
    refine ⟨G, ?_⟩
    intro x
    let q := (curvatureRoundPolarHomeomorph hK).symm x
    have hcoord := intrinsicRoundInverseCoordinates_eq_inverse hK x
    have hΦ : MDifferentiableAt 𝓘(ℝ, TM p × ℝ) I Φ
        (intrinsicRoundInverseCoordinates (1 / Real.sqrt K) (x.1 : RoundAmbient (TM p))) := by
      rw [hcoord]
      exact (hjet q.1 q.2 q.2.property).1
    have hD := (contDiffAt_intrinsicRoundInverseCoordinates hK x).differentiableAt (by norm_num)
    refine ⟨?_, hΦ.comp (x.1 : RoundAmbient (TM p))
      (mdifferentiableAt_iff_differentiableAt.mpr hD)⟩
    change Φ (intrinsicRoundInverseCoordinates (1 / Real.sqrt K)
      (x.1 : RoundAmbient (TM p))) = (Q q : M)
    rw [hcoord]
    exact (hQ q).symm

end LichnerowiczObata
