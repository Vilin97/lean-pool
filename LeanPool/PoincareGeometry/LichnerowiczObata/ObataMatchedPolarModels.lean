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

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataSouthPolarModel
public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarInverseDifferentiability
public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarMetricNondegeneracy

/-! # Matched north and south polar models constructed from one Obata function -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
/-- The full unit-angular polar metric, including differentiability of
the ambient parameter map. This packages the existing metric identity. -/
def HasUnitPolarMetric {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    (K : ℝ) (Φ : P × ℝ → M) : Prop :=
  ∀ u : Metric.sphere (0 : P) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
    MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ (u, r) ∧
    ∀ w v : P, inner ℝ (u : P) w = 0 → inner ℝ (u : P) v = 0 → ∀ s t : ℝ,
      inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I Φ (u, r) (w, s))
        (mfderiv 𝓘(ℝ, P × ℝ) I Φ (u, r) (v, t)) =
          (Real.sin (Real.sqrt K * r) ^ 2 / K) * inner ℝ w v + s * t

/-- The metric identity supplies nondegeneracy, so a polar coordinate
homeomorphism has a differentiable inverse without an extra jet hypothesis. -/
theorem HasUnitPolarMetric.exists_differentiable_inverse
    {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {K : ℝ} {Φ : P × ℝ → M} (hm : HasUnitPolarMetric I K Φ) (hK : 0 < K)
    (U : TopologicalSpace.Opens M)
    (Q : Metric.sphere (0 : P) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ U)
    (q₀ : Metric.sphere (0 : P) 1 × Ioo 0 (Real.pi / Real.sqrt K))
    (hQ : ∀ q, (Q q : M) = Φ (q.1, q.2))
    (hDim : Module.finrank ℝ E = n + 1) :
    ∃ e : OpenPartialHomeomorph (Metric.sphere (0 : P) 1 × ℝ) M,
      e.source = {q | q.2 ∈ Ioo 0 (Real.pi / Real.sqrt K)} ∧ e.target = U ∧
      (∀ q ∈ e.source, e q = Φ (q.1, q.2)) ∧
      (∀ y : U, e.symm (y : M) = ((Q.symm y).1, ((Q.symm y).2 : ℝ))) ∧
      ∀ y ∈ U, MDifferentiableAt I ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm y := by
  apply exists_differentiable_polar_inverse_on_target
    ⟨Ioo 0 (Real.pi / Real.sqrt K), isOpen_Ioo⟩ U Q q₀ Φ hQ hDim
  intro u r hr
  refine ⟨(hm u r hr).1, polar_derivative_injOn _ (obata_polar_coefficient_pos hK hr) ?_⟩
  intro v hv t
  exact (hm u r hr).2 v v hv hv t t

/-- Angular matching on any regular latitude is differentiable: it is the
angular component of the inverse polar coordinates of the other model. -/
theorem mdifferentiable_polar_angular_matching
    {P V : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]
    [Fact (Module.finrank ℝ V = n + 1)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {K : ℝ} {Φ : P × ℝ → M} {Ψ : V × ℝ → M}
    (hΦ : HasUnitPolarMetric I K Φ) (hΨ : HasUnitPolarMetric I K Ψ) (hK : 0 < K)
    (U : TopologicalSpace.Opens M)
    (Q : Metric.sphere (0 : V) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ U)
    (hQ : ∀ q, (Q q : M) = Ψ (q.1, q.2))
    (hDim : Module.finrank ℝ E = n + 1)
    (A : Metric.sphere (0 : P) 1 → Metric.sphere (0 : V) 1)
    {r s : ℝ} (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K))
    (hs : s ∈ Ioo 0 (Real.pi / Real.sqrt K))
    (hmatch : ∀ u : Metric.sphere (0 : P) 1, Φ (u, s) = Ψ (A u, r)) :
    MDifferentiable (𝓡 n) (𝓡 n) A := by
  intro u
  obtain ⟨e, heS, heT, he, heinv, hed⟩ := hΨ.exists_differentiable_inverse hK U Q
    (A u, ⟨r, hr⟩) hQ hDim
  have hid (v : Metric.sphere (0 : P) 1) : e.symm (Φ (v, s)) = (A v, r) := by
    have hh := heinv (Q (A v, ⟨r, hr⟩))
    simpa only [hQ, Q.symm_apply_apply, hmatch] using hh
  have hmem : Φ (u, s) ∈ U := by
    rw [hmatch, ← hQ (A u, ⟨r, hr⟩)]
    exact (Q (A u, ⟨r, hr⟩)).property
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, P)
      (Subtype.val : Metric.sphere (0 : P) 1 → P) u :=
    (contMDiff_coe_sphere u).mdifferentiableAt one_ne_zero
  have hp : MDifferentiableAt (𝓡 n) I
      (fun v : Metric.sphere (0 : P) 1 => Φ (v, s)) u :=
    (hΦ u s hs).1.comp u (hc.prodMk_space mdifferentiableAt_const)
  have hi := (hed _ hmem).comp u hp
  have hf : MDifferentiableAt (𝓡 n) (𝓡 n)
      (fun v : Metric.sphere (0 : P) 1 => (e.symm (Φ (v, s))).1) u :=
    mdifferentiableAt_fst.comp u hi
  simpa only [hid] using hf

section AngularMetric
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- Restricting the polar metric to a fixed latitude gives the angular
metric scaled by the squared polar warping coefficient. -/
theorem HasUnitPolarMetric.latitude_inner {K : ℝ} {Φ : P × ℝ → M}
    (hm : HasUnitPolarMetric I K Φ) (u : Metric.sphere (0 : P) 1)
    {r : ℝ} (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K))
    (v w : TangentSpace (𝓡 n) u) :
    inner ℝ (mfderiv (𝓡 n) I (fun a : Metric.sphere (0 : P) 1 => Φ (a, r)) u v)
      (mfderiv (𝓡 n) I (fun a : Metric.sphere (0 : P) 1 => Φ (a, r)) u w) =
      (Real.sin (Real.sqrt K * r) ^ 2 / K) *
        inner ℝ (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : P) 1 → P) u v)
          (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : P) 1 → P) u w) := by
  let j := fun a : Metric.sphere (0 : P) 1 => ((a : P), r)
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, P)
      (Subtype.val : Metric.sphere (0 : P) 1 → P) u :=
    (contMDiff_coe_sphere u).mdifferentiableAt one_ne_zero
  have hj : MDifferentiableAt (𝓡 n) 𝓘(ℝ, P × ℝ) j u :=
    hc.prodMk_space mdifferentiableAt_const
  have hd := mfderiv_comp (f := j) (g := Φ) u (hm u r hr).1 hj
  have hjd : ∀ z : TangentSpace (𝓡 n) u,
      mfderiv (𝓡 n) 𝓘(ℝ, P × ℝ) j u z =
        (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : P) 1 → P) u z, 0) := by
    intro z
    have hconst : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
        (fun _ : Metric.sphere (0 : P) 1 => r) u := mdifferentiableAt_const
    have hh := mfderiv_prodMk hc hconst
    rw [mfderiv_const] at hh
    convert congrArg (fun D => D z) hh using 1 <;>
      simp [j, mvfderiv, mfderiv, hc, hc.prodMk_space hconst, hc.prodMk hconst] <;> rfl
  change inner ℝ (mfderiv (𝓡 n) I (Φ ∘ j) u v)
    (mfderiv (𝓡 n) I (Φ ∘ j) u w) = _
  rw [hd]
  change inner ℝ (mfderiv 𝓘(ℝ, P × ℝ) I Φ (u, r) (mfderiv (𝓡 n) 𝓘(ℝ, P × ℝ) j u v))
    (mfderiv 𝓘(ℝ, P × ℝ) I Φ (u, r) (mfderiv (𝓡 n) 𝓘(ℝ, P × ℝ) j u w)) = _
  rw [hjd, hjd]
  have hv := spherePolarTangentInclusion_orthogonal (n := n) u (v, 0)
  have hw := spherePolarTangentInclusion_orthogonal (n := n) u (w, 0)
  simpa [spherePolarTangentInclusion] using (hm u r hr).2 _ _ hv hw 0 0

/-- Preservation of the intrinsic unit-sphere metric, expressed through the
differential of its Euclidean inclusion. -/
def PreservesSphereTangentMetric
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = n + 1)]
    (A : Metric.sphere (0 : P) 1 → Metric.sphere (0 : V) 1) : Prop :=
  ∀ (u : Metric.sphere (0 : P) 1) (v w : TangentSpace (𝓡 n) u),
    inner ℝ
      (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) (A u)
        (mfderiv (𝓡 n) (𝓡 n) A u v))
      (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) (A u)
        (mfderiv (𝓡 n) (𝓡 n) A u w)) =
    inner ℝ (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : P) 1 → P) u v)
      (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : P) 1 → P) u w)

/-- Matching latitude maps with the same positive polar coefficient forces
the angular differential to preserve the induced sphere inner product. -/
theorem polar_angular_matching_inner
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = n + 1)]
    {K : ℝ} {Φ : P × ℝ → M} {Ψ : V × ℝ → M}
    (hΦ : HasUnitPolarMetric I K Φ) (hΨ : HasUnitPolarMetric I K Ψ) (hK : 0 < K)
    (A : Metric.sphere (0 : P) 1 → Metric.sphere (0 : V) 1)
    (hA : MDifferentiable (𝓡 n) (𝓡 n) A)
    {r : ℝ} (hr : r ∈ Ioo 0 (Real.pi / Real.sqrt K))
    (hmatch : ∀ u : Metric.sphere (0 : P) 1, Φ (u, r) = Ψ (A u, r))
    (u : Metric.sphere (0 : P) 1) (v w : TangentSpace (𝓡 n) u) :
    inner ℝ
      (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) (A u)
        (mfderiv (𝓡 n) (𝓡 n) A u v))
      (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) (A u)
        (mfderiv (𝓡 n) (𝓡 n) A u w)) =
    inner ℝ (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : P) 1 → P) u v)
      (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : P) 1 → P) u w) := by
  let L := fun a : Metric.sphere (0 : V) 1 => Ψ (a, r)
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, V)
      (Subtype.val : Metric.sphere (0 : V) 1 → V) (A u) :=
    (contMDiff_coe_sphere (A u)).mdifferentiableAt one_ne_zero
  have hL : MDifferentiableAt (𝓡 n) I L (A u) :=
    (hΨ (A u) r hr).1.comp (A u) (hc.prodMk_space mdifferentiableAt_const)
  have heq : (fun a : Metric.sphere (0 : P) 1 => Φ (a, r)) = L ∘ A := funext hmatch
  have hh := hΦ.latitude_inner u hr v w
  rw [heq, mfderiv_comp u hL (hA u)] at hh
  rw [hmatch u] at hh
  have hs := hΨ.latitude_inner (A u) hr
    (mfderiv (𝓡 n) (𝓡 n) A u v) (mfderiv (𝓡 n) (𝓡 n) A u w)
  have hh' : (Real.sin (Real.sqrt K * r) ^ 2 / K) *
      inner ℝ
        (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) (A u)
          (mfderiv (𝓡 n) (𝓡 n) A u v))
        (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : V) 1 → V) (A u)
          (mfderiv (𝓡 n) (𝓡 n) A u w)) = _ := hs.symm.trans hh
  exact mul_left_cancel₀ (ne_of_gt (obata_polar_coefficient_pos hK hr)) hh'

end AngularMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
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

local instance matchedPolarTangentFinrank {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)] (p : M) :
    Fact (Module.finrank ℝ (TM p) = n + 1) :=
  ⟨show Module.finrank ℝ E = n + 1 from Fact.out⟩

/-- Both metric polar models, their isometric pole derivatives, and their
angular matching are constructed together from the Obata equation and the
two unique extrema. No matching homeomorphism is assumed. -/
theorem exists_obata_matched_polar_models
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) (hb : ∀ x, -a ≤ f x ∧ f x ≤ a)
    (hH : ∀ (y : M) (v w : TM y),
      hessian (leviCivitaConnection (I := I)) f y v w = -K * f y * inner ℝ v w)
    (c d : M) {z z' : E} (hz : z ∈ (extChartAt I c).target) (hz' : z' ∈ (extChartAt I d).target)
    (hmax : ∀ x, f x = a ↔ x = (extChartAt I c).symm z)
    (hmin : ∀ x, f x = -a ↔ x = (extChartAt I d).symm z') :
    let p := (extChartAt I c).symm z
    let q := (extChartAt I d).symm z'
    ∃ Φ : TM p × ℝ → M, ∃ Ψ : TM q × ℝ → M,
      HasRadialPoleModel I Φ p ∧ HasRadialPoleModel I Ψ q ∧
      HasUnitPolarMetric I K Φ ∧ HasUnitPolarMetric I K Ψ ∧
      ∃ N : Metric.sphere (0 : TM p) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
      ∃ S : Metric.sphere (0 : TM q) 1 × Ioo 0 (Real.pi / Real.sqrt K) ≃ₜ
          {x : M // -a < f x ∧ f x < a},
        (∀ u, (N u : M) = Φ (u.1, u.2)) ∧
        (∀ u, (S u : M) = Ψ (u.1, u.2)) ∧
        (∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          obataRadial K a f (Φ (u, r)) = r) ∧
        (∀ u : Metric.sphere (0 : TM q) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
          obataRadial K a f (Ψ (u, r)) = Real.pi / Real.sqrt K - r) ∧
        (∀ u : Metric.sphere (0 : TM p) 1,
          IsMIntegralCurveOn (fun r => Φ (u, r)) (gradient (I := I) (obataRadial K a f))
            (Ioo 0 (Real.pi / Real.sqrt K))) ∧
        ∃ A : Metric.sphere (0 : TM p) 1 ≃ₜ Metric.sphere (0 : TM q) 1,
          (∀ u : Metric.sphere (0 : TM p) 1, ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
            Φ (u, Real.pi / Real.sqrt K - r) = Ψ (A u, r)) ∧
          ∀ (n : ℕ) (hdim : Module.finrank ℝ E = n + 1),
            letI : Fact (Module.finrank ℝ E = n + 1) := ⟨hdim⟩
            MDifferentiable (𝓡 n) (𝓡 n) A ∧ MDifferentiable (𝓡 n) (𝓡 n) A.symm ∧
              PreservesSphereTangentMetric (n := n) A ∧
              PreservesSphereTangentMetric (n := n) A.symm := by
  have hf2 : ContMDiff I 𝓘(ℝ, ℝ) 2 f :=
    hf.of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hpm : IsMaxOn f univ ((extChartAt I c).symm z) := by
    intro x _
    change f x ≤ f ((extChartAt I c).symm z)
    rw [(hmax _).mpr rfl]
    exact (hb x).2
  have hcrit : gradient (I := I) f ((extChartAt I c).symm z) = 0 :=
    gradient_eq_zero_of_local_extremum ((hf2 _).mdifferentiableAt (by norm_num))
      (Or.inr (hpm.isLocalMax (by simp)))
  obtain ⟨Φ, hpole, N, hN, hρN, hcN, hmN⟩ :=
    exists_obata_unit_spherical_product hf hnon hK ha hH c hz hcrit hmax
  obtain ⟨Ψ, hspole, S, hS, hρS, hcS, hmS⟩ :=
    exists_obata_south_polar_model hf hnon hK ha hb hH d hz' hmin
  obtain ⟨A, hA⟩ := obata_polar_coordinates_match hf2 hK ha N S
    (fun u : Metric.sphere (0 : TM ((extChartAt I c).symm z)) 1 × ℝ => Φ (u.1, u.2))
    (fun u : Metric.sphere (0 : TM ((extChartAt I d).symm z')) 1 × ℝ => Ψ (u.1, u.2))
    hN hS hρN hρS hcN hcS
  refine ⟨Φ, Ψ, hpole, hspole, hmN, hmS, N, S, hN, hS, hρN, hρS, hcN, A, hA, ?_⟩
  intro n hdim
  let : Fact (Module.finrank ℝ E = n + 1) := ⟨hdim⟩
  let U : TopologicalSpace.Opens M :=
    ⟨{x | -a < f x ∧ f x < a},
      (isOpen_lt continuous_const hf.continuous).inter
        (isOpen_lt hf.continuous continuous_const)⟩
  let m := (Real.pi / Real.sqrt K) / 2
  have hm : m ∈ Ioo 0 (Real.pi / Real.sqrt K) := by
    have hp := div_pos Real.pi_pos (Real.sqrt_pos.mpr hK)
    dsimp [m]
    constructor <;> linarith
  have heq : Real.pi / Real.sqrt K - m = m := by dsimp [m]; ring
  have hforward : MDifferentiable (𝓡 n) (𝓡 n) A := by
    apply mdifferentiable_polar_angular_matching (n := n) hmN hmS hK U S hS hdim A hm hm
    intro u
    simpa only [heq] using hA u m hm
  have hbackward : MDifferentiable (𝓡 n) (𝓡 n) A.symm := by
    apply mdifferentiable_polar_angular_matching (n := n) hmS hmN hK U N hN hdim A.symm hm hm
    intro v
    simpa only [heq, A.apply_symm_apply] using (hA (A.symm v) m hm).symm
  refine ⟨hforward, hbackward, ?_, ?_⟩
  · intro u v w
    apply polar_angular_matching_inner hmN hmS hK A hforward hm _ u v w
    intro a
    simpa only [heq] using hA a m hm
  · intro u v w
    apply polar_angular_matching_inner hmS hmN hK A.symm hbackward hm _ u v w
    intro a
    simpa only [heq, A.apply_symm_apply] using (hA (A.symm a) m hm).symm

end LichnerowiczObata
