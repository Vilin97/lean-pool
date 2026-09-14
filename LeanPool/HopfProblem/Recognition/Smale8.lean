/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus2
import all LeanPool.HopfProblem.Recognition.Smale1
import all LeanPool.HopfProblem.Recognition.Smale2
import all LeanPool.HopfProblem.Recognition.Smale3
import all LeanPool.HopfProblem.Recognition.Smale4
import all LeanPool.HopfProblem.Recognition.Smale5
import all LeanPool.HopfProblem.Recognition.Degree1
import all LeanPool.HopfProblem.Recognition.Smale6
import all LeanPool.HopfProblem.Recognition.Smale7
import all LeanPool.HopfProblem.Pi1.ThreefoldOverlapMappingTorus2

/-!
# Hopf problem: recognition · smale 8

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem
    Smale.ChartMapPerturbation.fderiv_cutoff_mul_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ψ ρ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hρ : ContDiff ℝ ∞ ρ) {x v : E}
    (hx : ρ x = 0) (hv : fderiv ℝ ρ x v = 0) : fderiv ℝ (fun y => ψ y * ρ y) x v = 0 := by
  rw [fderiv_fun_mul (hψ.differentiable (by simp) x) (hρ.differentiable (by simp) x)]
  simp only [add_apply, smul_apply, smul_eq_mul, hx, hv, MulZeroClass.mul_zero,
    MulZeroClass.zero_mul, add_zero]

private theorem Smale.ChartMapPerturbation.common_kernel_preserved_on_zero_set {E G F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
    [TopologicalSpace N] [ChartedSpace H N] (c : PartialDiffeomorph J 𝓘(ℝ, F) N F ∞) {f : E → N}
    {ψ ρ : E → ℝ} (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hψ : ContDiff ℝ ∞ ψ) (hρ : ContDiff ℝ ∞ ρ)
    (hsupport : tsupport (fun y => ψ y * ρ y) ⊆ f ⁻¹' c.source) {a : F}
    (ha : Valid c f (fun y => ψ y * ρ y) a)
    (hcommon : ∀ x, ρ x = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f x v = 0 → fderiv ℝ ρ x v = 0 → v = 0) :
    ∀ x,
      ρ x = 0 →
        ∀ v,
          mfderiv 𝓘(ℝ, E) J (perturb c f (fun y => ψ y * ρ y) a) x v = 0 →
            fderiv ℝ ρ x v = 0 → v = 0 := by
  intro x hx v hzero hv
  have hweight := fderiv_cutoff_mul_eq_zero hψ hρ hx hv
  have hold :=
    (derivative_eq_zero_iff_of_weight_derivative_eq_zero c hf (hψ.mul hρ) hsupport ha hweight).mp
      hzero
  exact hcommon x hx v hold hv

private theorem
    Smale.ManifoldImmersion.exists_boundary_derivative_repair_step {B E G H H' X N : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [LindelofSpace (X × E)]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N)) (i : ι)
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ j, (p j).Compatible f)
    {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G) {K L : Set E}
    (hK : IsCompact K) (hinj : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f y))
    (hLsub : L ⊆ (p i).plateau) (hLrange : L ⊆ Set.range b)
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ j, (p j).Compatible g) ∧
          f.HomotopicRel g {y | ρ y = 0} ∧
            (∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) ∧
              ∀ y ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  let β : E → ℝ := fun y => (p i).cutoff y * ρ y
  have hβ : ContDiff ℝ ∞ β := (p i).smooth.contDiff.mul hρ
  have hcompact : HasCompactSupport β := (p i).compact.mul_right
  have hsupport : tsupport β ⊆ f ⁻¹' (p i).chart.source :=
    tsupport_mul_subset_left.trans ((p i).inner_compatible (hcompatible i))
  have hkeep :
    ∀ᶠ a in 𝓝 (0 : G),
      ∀ j, (p j).Compatible (Smale.ChartMapPerturbation.perturb (p i).chart f β a) := by
    apply Filter.eventually_all.mpr
    intro j
    exact
      Smale.ChartMapPerturbation.eventually_maps_compact_into_open (p i).chart hf hβ.contMDiff
        hsupport (p j).outer_compact.isCompact (p j).chart.open_source (hcompatible j)
  have hold :=
    Smale.ChartMapPerturbation.eventually_perturb_injective_derivative (p i).chart hf hβ.contMDiff
      hcompact hsupport hK hinj
  let Common (g : E → N) : Prop :=
    ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 → fderiv ℝ ρ y v = 0 → v = 0
  have hretain :
    ∀ᶠ a in 𝓝 (0 : G), Common (Smale.ChartMapPerturbation.perturb (p i).chart f β a) := by
    filter_upwards [Smale.ChartMapPerturbation.eventually_valid (p i).chart hf hβ.contMDiff
        hcompact hsupport] with
      a ha
    exact
      Smale.ChartMapPerturbation.common_kernel_preserved_on_zero_set (p i).chart hf
        (p i).smooth.contDiff hρ hsupport ha hcommon
  let Q : (E → N) → Prop := fun g =>
    (∀ j, (p j).Compatible g) ∧ (∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J g y)) ∧ Common g
  have hQ : ∀ᶠ a in 𝓝 (0 : G), Q (Smale.ChartMapPerturbation.perturb (p i).chart f β a) :=
    hkeep.and (hold.and hretain)
  have houter : (p i).plateau ⊆ interior {y | (p i).outer y = 1} := by
    apply isOpen_interior.subset_interior_iff.mpr
    intro y hy
    apply (p i).nested y
    apply subset_tsupport (p i).cutoff
    change (p i).cutoff y ≠ 0
    rw [interior_subset (s := {y | (p i).cutoff y = 1}) hy]
    exact one_ne_zero
  have hplateau : ∀ x ∈ b ⁻¹' L, b x ∈ interior {y | (p i).outer y = 1} := fun _ hx =>
    houter (hLsub hx)
  have hcommonβ :
    ∀ x ∈ b ⁻¹' L, ∀ v, mfderiv 𝓘(ℝ, E) J f (b x) v = 0 → fderiv ℝ β (b x) v = 0 → v = 0 := by
    intro x hx v hfv hβv
    have heq : β =ᶠ[𝓝 (b x)] ρ := by
      filter_upwards [(p i).plateau_eventually_one (hLsub hx)] with y hy
      simp only [β, hy, one_mul]
    apply hcommon (b x) (hzero x) v hfv
    rw [← heq.fderiv_eq]
    exact hβv
  obtain ⟨g, hg, ⟨hc, hinjg, hcommong⟩, ⟨Hrel⟩, hnew⟩ :=
    exists_weighted_immersive_patch_with_property (p i).chart f hf hb hβ
      (p i).outer_smooth.contDiff hcompact hsupport (hcompatible i) hplateau hcommonβ hdim Q hQ
  refine ⟨g, hg, hc, ?_, hcommong, ?_⟩
  · refine ⟨{ Hrel.toHomotopy with prop' := ?_ }⟩
    intro t y hy
    apply Hrel.eq_fst t
    change (p i).cutoff y * ρ y = 0
    rw [hy, MulZeroClass.mul_zero]
  · intro y hy
    rcases hy with hy | hy
    · exact hinjg y hy
    · obtain ⟨x, rfl⟩ := hLrange hy
      exact hnew x hy

private theorem
    Smale.ManifoldImmersion.exists_finite_boundary_derivative_repair {B E G H H' X N : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [LindelofSpace (X × E)]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] {ι : Type*} [Finite ι]
    (p : ι → Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N))
    (L : ι → Set E) (hL : ∀ i, IsCompact (L i)) (hLsub : ∀ i, L i ⊆ (p i).plateau) (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) (hcompatible : ∀ i, (p i).Compatible f) {b : X → E}
    (hb : ContMDiff I 𝓘(ℝ, E) ∞ b) (hLrange : ∀ i, L i ⊆ Set.range b) {ρ : E → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G) {K : Set E}
    (hK : IsCompact K) (hinj : ∀ y ∈ K, Function.Injective (mfderiv 𝓘(ℝ, E) J f y))
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ ρ y v = 0 → v = 0)
    (s : Finset ι) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        (∀ i, (p i).Compatible g) ∧
          f.HomotopicRel g {y | ρ y = 0} ∧
            (∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J g y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) ∧
              ∀ y ∈ K ∪ ⋃ i ∈ s, L i, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  classical
    induction s using Finset.induction_on with
  | empty =>
    refine ⟨f, hf, hcompatible, ContinuousMap.HomotopicRel.refl f, hcommon, ?_⟩
    simpa only [Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty, Set.union_empty] using
      hinj
  | @insert i s _ ih =>
    obtain ⟨g₁, hg₁, hc₁, hhom₁, hcommon₁, hinj₁⟩ := ih
    have hKold : IsCompact (K ∪ ⋃ j ∈ s, L j) := hK.union (s.isCompact_biUnion (fun j _ => hL j))
    obtain ⟨g₂, hg₂, hc₂, hhom₂, hcommon₂, hinj₂⟩ :=
      exists_boundary_derivative_repair_step p i g₁ hg₁ hc₁ hb hρ hzero hdim hKold hinj₁ (hLsub i)
        (hLrange i) hcommon₁
    refine ⟨g₂, hg₂, hc₂, hhom₁.trans hhom₂, hcommon₂, ?_⟩
    intro y hy
    apply hinj₂ y
    rcases hy with hy | hy
    · exact Or.inl (Or.inl hy)
    · obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.mp hy
      rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact Or.inr hyj
      · exact Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨j, hjs, hyj⟩))

public
theorem Smale.ManifoldImmersion.exists_compact_boundary_derivative_repair {B E G H H' X N : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
    [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X] [CompactSpace X]
    [LindelofSpace (X × E)] [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    (f : C(E, N)) (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b)
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G)
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 → fderiv ℝ ρ y v = 0 → v = 0) :
    ∃ g : C(E, N),
      ContMDiff 𝓘(ℝ, E) J ∞ g ∧
        f.HomotopicRel g {y | ρ y = 0} ∧
          ∀ y ∈ Set.range b, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  classical
  have hboundary : IsCompact (Set.range b) := isCompact_range hb.continuous
  have hp (x : Set.range b) :
    ∃ p : Smale.ManifoldSmoothing.MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N),
      ∃ D : Set E, p.Compatible f ∧ IsCompact D ∧ D ∈ 𝓝 x.1 ∧ D ⊆ p.plateau := by
    obtain ⟨p, hcompatible, hplateau⟩ :=
      Smale.ManifoldSmoothing.exists_smoothing_patch_at (I := 𝓘(ℝ, E)) (J := J) f x.1
    obtain ⟨D, hDx, hDsub, hD⟩ := local_compact_nhds (isOpen_interior.mem_nhds hplateau)
    exact ⟨p, D, hcompatible, hD, hDx, hDsub⟩
  choose p D hcompatible hD hn hsub using hp
  have hcover : Set.range b ⊆ ⋃ x : Set.range b, interior (D x) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ :=
    hboundary.elim_finite_subcover (fun x : Set.range b => interior (D x))
      (fun _ => isOpen_interior) hcover
  let L (i : s) := Set.range b ∩ D i.1
  have hL (i : s) : IsCompact (L i) := hboundary.inter_right (hD i.1).isClosed
  have hLsub (i : s) : L i ⊆ (p i.1).plateau := fun _ hx => hsub i.1 hx.2
  have hLrange (i : s) : L i ⊆ Set.range b := Set.inter_subset_left
  obtain ⟨g, hg, -, hhom, -, hinj⟩ :=
    exists_finite_boundary_derivative_repair (fun i : s => p i.1) L hL hLsub f hf
      (fun i => hcompatible i.1) hb hLrange hρ hzero hdim isCompact_empty
      (fun _ hx => False.elim hx) hcommon Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro y hy
  obtain ⟨i, hi, hyD⟩ := Set.mem_iUnion₂.mp (hs hy)
  apply hinj y
  exact Or.inr (Set.mem_iUnion₂.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hy, interior_subset hyD⟩)

private def Smale.CurveImmersion.endpointFunction (t : ℝ) : ℝ :=
  t * (1 - t)

private theorem Smale.CurveImmersion.contDiff_endpointFunction : ContDiff ℝ ∞ endpointFunction := by
  unfold endpointFunction
  fun_prop

private theorem Smale.CurveImmersion.endpointFunction_eq_zero_iff (t : ℝ) :
    endpointFunction t = 0 ↔ t = 0 ∨ t = 1 := by
  rw [endpointFunction, mul_eq_zero, sub_eq_zero]
  exact or_congr Iff.rfl eq_comm

private theorem Smale.CurveImmersion.fderiv_endpointFunction (t v : ℝ) :
    fderiv ℝ endpointFunction t v = v * (1 - 2 * t) := by
  have hd : HasDerivAt endpointFunction (1 * (1 - t) + t * (0 - 1)) t :=
    (hasDerivAt_id t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  have heq : 1 * (1 - t) + t * (0 - 1) = 1 - 2 * t := by ring
  rw [heq] at hd
  rw [hd.hasFDerivAt.fderiv]
  rfl

private theorem Smale.CurveImmersion.injective_endpointFunction_derivative {t : ℝ}
    (ht : endpointFunction t = 0) {v : ℝ} (hv : fderiv ℝ endpointFunction t v = 0) : v = 0 := by
  rw [fderiv_endpointFunction] at hv
  rcases (endpointFunction_eq_zero_iff t).mp ht with rfl | rfl
  · simpa using hv
  · norm_num at hv
    exact hv

private theorem Smale.ManifoldImmersion.exists_curve_endpoint_derivative_repair {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] (f : C(ℝ, N)) (hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f)
    (hdim : 2 ≤ Module.finrank ℝ G) :
    ∃ g : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ g ∧
        f.HomotopicRel g ({0, 1} : Set ℝ) ∧
          ∀ t ∈ ({0, 1} : Set ℝ), Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t) := by
  let X := ({0, 1} : Set ℝ)
  let : Fintype X := ((Set.finite_singleton (1 : ℝ)).insert 0).fintype
  let Z := EuclideanSpace ℝ (Fin 0)
  let : ChartedSpace Z X := ChartedSpace.ofDiscreteTopology
  let : IsManifold 𝓘(ℝ, Z) ∞ X := IsManifold.of_discreteTopology _
  let b : X → ℝ := Subtype.val
  have hb : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, ℝ) ∞ b := contMDiff_of_discreteTopology
  have hrange : Set.range b = ({0, 1} : Set ℝ) := by ext t; simp [b, X]
  have hzero : ∀ x, Smale.CurveImmersion.endpointFunction (b x) = 0 := by
    intro x
    apply (Smale.CurveImmersion.endpointFunction_eq_zero_iff _).mpr
    exact x.property
  have hzset : {t | Smale.CurveImmersion.endpointFunction t = 0} = ({0, 1} : Set ℝ) := by
    ext t
    simp only [Set.mem_ofPred_eq, Smale.CurveImmersion.endpointFunction_eq_zero_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  have hd : Module.finrank ℝ Z + Module.finrank ℝ ℝ < Module.finrank ℝ G := by
    simp only [Z, finrank_euclideanSpace_fin, Module.finrank_self]
    omega
  obtain ⟨g, hg, hrel, hi⟩ :=
    exists_compact_boundary_derivative_repair f hf hb
      Smale.CurveImmersion.contDiff_endpointFunction hzero hd
      (fun _ ht _ _ hv => Smale.CurveImmersion.injective_endpointFunction_derivative ht hv)
  refine ⟨g, hg, ?_, ?_⟩
  · simpa only [hzset] using hrel
  · simpa only [hrange] using hi

private theorem
    Smale.exists_short_embedded_arc {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N] {U : Set N}
    (hU : IsOpen U) {x : N} (hx : x ∈ U) (hdim : 2 ≤ Module.finrank ℝ G) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        f 0 = x ∧
          f 1 ≠ x ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ∈ U := by
  let c : C(ℝ, N) := ContinuousMap.const ℝ x
  obtain ⟨g, hg, hrel, hi⟩ :=
    ManifoldImmersion.exists_curve_endpoint_derivative_repair (J := J) c contMDiff_const hdim
  have hg0 : g 0 = x := (hrel.fst_eq_snd (by simp)).symm
  have hi0 : Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g 0) := hi 0 (by simp)
  obtain ⟨V, hV, h0V, hinj⟩ :=
    ManifoldImmersion.exists_open_injOn_of_injective_nativeDerivative hg hi0
  let W := V ∩ ({t : ℝ | Function.Injective (mfderiv 𝓘(ℝ, ℝ) J g t)} ∩ g ⁻¹' U)
  have hW : IsOpen W :=
    hV.inter ((ManifoldImmersion.isOpen_injective_derivative hg).inter (hU.preimage g.continuous))
  have h0W : (0 : ℝ) ∈ W := ⟨h0V, hi0, (show g 0 ∈ U from hg0.symm ▸ hx)⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0W)
  let L : ℝ →L[ℝ] ℝ := (r / 2) • ContinuousLinearMap.id ℝ ℝ
  have hLs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ L := L.contDiff.contMDiff
  have hL (t : ℝ) : L t = (r / 2) * t := rfl
  have hscale : 0 < r / 2 := by positivity
  have hLinj : Function.Injective L := by
    intro s t hst
    exact mul_left_cancel₀ hscale.ne' hst
  have hLW : ∀ t ∈ Set.Icc (0 : ℝ) 1, L t ∈ W := by
    intro t ht
    apply hball
    change Dist.dist (L t) 0 < r
    rw [dist_zero_right, Real.norm_eq_abs, hL, abs_of_nonneg (mul_nonneg hscale.le ht.1)]
    have hbound := mul_le_mul_of_nonneg_left ht.2 hscale.le
    linarith
  let f : C(ℝ, N) := ⟨g ∘ L, g.continuous.comp L.continuous⟩
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f := hg.comp hLs
  have hfinj : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact hLinj (hinj (hLW s hs).1 (hLW t ht).1 hst)
  have hf0 : f 0 = x := by
    change g (L 0) = x
    rw [map_zero, hg0]
  have hemb : Topology.IsClosedEmbedding (fun t : unitInterval => f t) := by
    apply (f.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro s t hst
    exact Subtype.ext (hfinj s.property t.property hst)
  refine ⟨f, hf, hf0, ?_, hemb, ?_, ?_⟩
  · intro hfx
    have h10 : (1 : ℝ) = 0 := hfinj (by simp) (by simp) (hfx.trans hf0.symm)
    exact one_ne_zero h10
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (g ∘ L) t)
    rw [mfderiv_comp t (hg.mdifferentiableAt (by simp)) (hLs.mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv, L.fderiv]
    exact (hLW t ht).2.1.comp hLinj
  · intro t ht
    exact (hLW t ht).2.2

private theorem Smale.exists_embedded_connecting_arc_avoiding_finite_dim_two {G H N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace H]
    {J : ModelWithCorners ℝ G H} [J.Boundaryless] [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold J ∞ N] [T2Space N] {x y : N} (γ : Path x y) (hxy : x ≠ y)
    (hdim : 2 ≤ Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
        f 0 = x ∧
          f 1 = y ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
                ∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S := by
  have hSx : (S \ { x }).Finite := hS.subset Set.sdiff_subset
  obtain ⟨g, hg, hg0, hg1, hemb, hi, havoid⟩ :=
    exists_short_embedded_arc (J := J) hSx.isClosed.isOpen_compl
      (show x ∈ (S \ { x })ᶜ from by simp) hdim
  have hginj : Set.InjOn g (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨s, hs⟩) (a₂ := ⟨t, ht⟩) hst)
  have hg1S : g 1 ∉ S := by
    intro hs
    exact havoid 1 (by simp) ⟨hs, hg1⟩
  let C : Set N := (Insert.insert x S) \ { y }
  have hC : C.Finite := (hS.insert x).subset Set.sdiff_subset
  have hxC : x ∈ C := ⟨Set.mem_insert x S, hxy⟩
  have hg1C : g 1 ∉ C := by
    rintro ⟨hr, _⟩
    rcases hr with hr | hr
    · exact hg1 hr
    · exact hg1S hr
  have hyC : y ∉ C := fun hy => hy.2 rfl
  let α : Path x (g 1) :=
    { toFun := fun t => g t
      continuous_toFun := g.continuous.comp continuous_subtype_val
      source' := hg0
      target' := rfl }
  obtain ⟨d, hd, hfix⟩ :=
    exists_pointMoving_fixing_finite (J := J) (α.symm.trans γ) hdim hC hg1C hyC
  let f : C(ℝ, N) := ⟨d ∘ g, d.continuous.comp g.continuous⟩
  have hf : ContMDiff 𝓘(ℝ, ℝ) J ∞ f := d.contMDiff.comp hg
  refine ⟨f, hf, ?_, hd, ?_, ?_, ?_⟩
  · change d (g 0) = x
    rw [hg0]
    exact hfix x hxC
  · apply (f.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro s t hst
    exact hemb.injective (d.injective hst)
  · intro t ht
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ) J (d ∘ g) t)
    rw [mfderiv_comp t (d.contMDiff.mdifferentiableAt (by simp)) (hg.mdifferentiableAt (by simp))]
    exact
      (PartialChart.bijective_mfderiv d.toPartialDiffeomorph (Set.mem_univ (g t))).1.comp
        (hi t ht)
  · intro t ht hftS
    have htI : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    by_cases hfty : f t = y
    · have hgt : g t = g 1 := d.injective (hfty.trans hd.symm)
      exact ht.2.ne (hginj htI (by simp) hgt)
    · have hftC : f t ∈ C := ⟨Or.inr hftS, hfty⟩
      have hgt : g t = f t := d.injective (hfix (f t) hftC).symm
      have hgtS : g t ∈ S := hgt.symm ▸ hftS
      have hgtx : g t ≠ x := by
        intro he
        exact ht.1.ne' (hginj htI (by simp) (he.trans hg0.symm))
      exact havoid t htI ⟨hgtS, hgtx⟩

private theorem Smale.exists_tubular_connecting_arc_avoiding_finite_with_global_zero {G N : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] [CompactSpace N] {x y : N}
    (γ : Path x y) (hxy : x ≠ y) (hdim : 2 ≤ Module.finrank ℝ G) (n : ℕ)
    (hcodim : 1 + n = Module.finrank ℝ G) {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N),
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, G) ∞ f ∧
        f 0 = x ∧
          f 1 = y ∧
            Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
              (∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, G) f t)) ∧
                (∀ t ∈ Set.Ioo (0 : ℝ) 1, f t ∉ S) ∧
                  ∃ ε : ℝ,
                    0 < ε ∧
                      ∃ Φ :
                        PartialDiffeomorph 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, G)
                          (ℝ × EuclideanSpace ℝ (Fin n)) N ∞,
                        Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 ε ⊆ Φ.source ∧
                          (∀ t, Φ (t, 0) = f t) ∧ Φ.target ⊆ (S \ { x, y })ᶜ := by
  obtain ⟨f, hf, hf0, hf1, hemb, hi, havoid⟩ :=
    exists_embedded_connecting_arc_avoiding_finite_dim_two (J := 𝓘(ℝ, G)) γ hxy hdim hS
  have hinj : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro t ht s hs hts
    exact congrArg Subtype.val (hemb.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) hts)
  have hO : IsOpen (S \ { x, y })ᶜ := (hS.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hfO : Set.MapsTo f (Set.Icc (0 : ℝ) 1) (S \ { x, y })ᶜ := by
    intro t ht
    change f t ∉ S \ { x, y }
    by_cases ht0 : t = 0
    · rw [ht0, hf0]
      exact fun hx => hx.2 (by simp)
    by_cases ht1 : t = 1
    · rw [ht1, hf1]
      exact fun hy => hy.2 (by simp)
    have hti : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact fun hs => havoid t hti hs.1
  have hstar : StarConvex ℝ (0 : ℝ) (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  obtain ⟨ε, hε, Φ, hsource, hzero, htarget⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      CompactIccSpace.isCompact_Icc (by simp) hstar hinj hi n
      (by simpa only [Module.finrank_self] using hcodim) hO hfO
  exact ⟨f, hf, hf0, hf1, hemb, hi, havoid, ε, hε, Φ, hsource, hzero, htarget⟩

private theorem
    Smale.exists_clean_corner_of_tubular_arcs {E M D Z N P A B : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    [TopologicalSpace N] [ChartedSpace D N] [TopologicalSpace P] [ChartedSpace Z P] {F : N → M}
    {G : P → M} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ × A) 𝓘(ℝ, D) (ℝ × A) N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞) {f : ℝ → N} {g : ℝ → P}
    (hc : ∀ t, c (t, 0) = f t) (hd : ∀ t, d (t, 0) = g t) {t₀ : ℝ}
    (htc : (t₀, (0 : A)) ∈ c.source) (htd : (t₀, (0 : B)) ∈ d.source) (hxy : G (g t₀) = F (f t₀))
    (hdim : Module.finrank ℝ (ℝ × A) + Module.finrank ℝ (ℝ × B) = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f t₀)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g t₀))))
    {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) {O : Set M} (hO : IsOpen O) (hxO : F (f t₀) ∈ O) :
    ∃ W : Set (ℝ × ℝ),
      IsOpen W ∧
        (0 : ℝ × ℝ) ∈ W ∧
          ∃ k : (ℝ × ℝ) → M,
            ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
              Set.InjOn k W ∧
                Set.MapsTo k W O ∧
                  k 0 = F (f t₀) ∧
                    (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                      (∀ p ∈ W, (k p ∈ Set.range F ↔ p.2 = 0) ∧ (k p ∈ Set.range G ↔ p.1 = 0)) ∧
                        (∀ s, (s, 0) ∈ W → k (s, 0) = F (f (t₀ + s * σ))) ∧
                          (∀ t, (0, t) ∈ W → k (0, t) = G (g (t₀ + t * τ))) := by
  let c' := (NativeParametrization.translation (t₀, (0 : A))).toPartialDiffeomorph.trans c
  let d' := (NativeParametrization.translation (t₀, (0 : B))).toPartialDiffeomorph.trans d
  have hc0 : (0 : ℝ × A) ∈ c'.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change 0 + (t₀, (0 : A)) ∈ c.source
    rw [zero_add]
    exact htc
  have hd0 : (0 : ℝ × B) ∈ d'.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change 0 + (t₀, (0 : B)) ∈ d.source
    rw [zero_add]
    exact htd
  have hcx : c' 0 = f t₀ := by
    change c (0 + (t₀, (0 : A))) = f t₀
    rw [zero_add, hc]
  have hdy : d' 0 = g t₀ := by
    change d (0 + (t₀, (0 : B))) = g t₀
    rw [zero_add, hd]
  have hxy' : G (d' 0) = F (c' 0) := by rw [hcx, hdy]; exact hxy
  have ht' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (c' 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d' 0))) := by
    rw [hcx, hdy]
    exact ht
  have hxO' : F (c' 0) ∈ O := by rw [hcx]; exact hxO
  have hu : (σ, (0 : A)) ≠ 0 := fun he => hσ (congrArg Prod.fst he)
  have hv : (τ, (0 : B)) ≠ 0 := fun he => hτ (congrArg Prod.fst he)
  obtain ⟨W, hW, h0W, k, hk, hinj, hWO, hcenter, hi, hclean, hlo, hhi⟩ :=
    exists_native_clean_corner_of_parametrizations hF hG hembF hembG c' d' hc0 hd0 hxy' hdim ht'
      hu hv hO hxO'
  refine ⟨W, hW, h0W, k, hk, hinj, hWO, hcenter.trans (congrArg F hcx), hi, hclean, ?_, ?_⟩
  · intro s hs
    rw [hlo s hs]
    apply congrArg F
    change c (s • (σ, (0 : A)) + (t₀, 0)) = f (t₀ + s * σ)
    have he : s • (σ, (0 : A)) + (t₀, 0) = (t₀ + s * σ, 0) := by simp [smul_eq_mul, add_comm]
    rw [he, hc]
  · intro t ht
    rw [hhi t ht]
    apply congrArg G
    change d (t • (τ, (0 : B)) + (t₀, 0)) = g (t₀ + t * τ)
    have he : t • (τ, (0 : B)) + (t₀, 0) = (t₀ + t * τ, 0) := by simp [smul_eq_mul, add_comm]
    rw [he, hd]

private theorem Smale.nonempty_cleanCornerPatch_of_tubular_arcs {E M D Z N P A B : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace N] [ChartedSpace D N]
    [TopologicalSpace P] [ChartedSpace Z P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hembF : Topology.IsEmbedding F) (hembG : Topology.IsEmbedding G)
    (c : PartialDiffeomorph 𝓘(ℝ, ℝ × A) 𝓘(ℝ, D) (ℝ × A) N ∞)
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞) {f : ℝ → N} {g : ℝ → P}
    (hc : ∀ t, c (t, 0) = f t) (hd : ∀ t, d (t, 0) = g t) {t₀ : ℝ}
    (htc : (t₀, (0 : A)) ∈ c.source) (htd : (t₀, (0 : B)) ∈ d.source) (hxy : G (g t₀) = F (f t₀))
    (hdim : Module.finrank ℝ (ℝ × A) + Module.finrank ℝ (ℝ × B) = Module.finrank ℝ E)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f t₀)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g t₀))))
    {σ τ : ℝ} (hσ : σ ≠ 0) (hτ : τ ≠ 0) :
    Nonempty
      (CleanCornerPatch (E := E) (Set.range F) (Set.range G) (fun s => F (f (t₀ + s * σ)))
        (fun t => G (g (t₀ + t * τ)))) := by
  obtain ⟨W, hW, h0W, k, hk, hinj, _, _, hi, hsheets, hlo, hhi⟩ :=
    exists_clean_corner_of_tubular_arcs hF hG hembF hembG c d hc hd htc htd hxy hdim ht hσ hτ
      isOpen_univ (Set.mem_univ _)
  exact
    ⟨{ domain := W, open_domain := hW, contains_zero := h0W, map := k, smooth := hk,
        injective := hinj, derivative_injective := hi, sheets := hsheets, axis_first := hlo,
        axis_second := hhi }⟩

private theorem Smale.exists_clean_ambient_chart_along_embedded_arc {E M G N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [TopologicalSpace N]
    [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N] [T2Space N] [CompactSpace N] {F : N → M}
    {f : ℝ → N} (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F) (hembF : Topology.IsEmbedding F)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, G) ∞ f) (hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, G) f t)) (n m : ℕ)
    (hsheet : 1 + n = Module.finrank ℝ G) (hcodim : Module.finrank ℝ G + m = Module.finrank ℝ E)
    {O : Set M} (hO : IsOpen O) (hfO : Set.MapsTo (F ∘ f) (Set.Icc (0 : ℝ) 1) O) :
    ∃ Φ :
      PartialDiffeomorph
        𝓘(ℝ, StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) 𝓘(ℝ, E)
        (StripCoordinates.Space (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) M ∞,
      Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) Φ.source ∧
        Φ.target ⊆ O ∧
          (∀ t, StripCoordinates.center t ∈ Φ.source → Φ (StripCoordinates.center t) = F (f t)) ∧
            (∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) := by
  have hstar : StarConvex ℝ (0 : ℝ) (Set.Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  obtain ⟨a, ha, c, hprod, hzero, _⟩ :=
    exists_normed_tubularNeighborhood_in_open_of_embedded_starConvex_with_global_zero hf
      CompactIccSpace.isCompact_Icc (by simp) hstar hinjf hif n
      (by simpa only [Module.finrank_self] using hsheet) isOpen_univ (fun _ _ => Set.mem_univ _)
  let K := Set.Icc (0 : ℝ) 1 ×ˢ {(0 : EuclideanSpace ℝ (Fin n))}
  have hK : IsCompact K := CompactIccSpace.isCompact_Icc.prod isCompact_singleton
  have h0K : (0 : ℝ × EuclideanSpace ℝ (Fin n)) ∈ K := by simp [K]
  have hstarK : StarConvex ℝ (0 : ℝ × EuclideanSpace ℝ (Fin n)) K :=
    hstar.prod (starConvex_singleton _)
  have hKc : K ⊆ c.source := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact hprod ⟨ht, Metric.mem_closedBall_self ha.le⟩
  have hFO : Set.MapsTo (F ∘ c) K O := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have hz0 : z = 0 := hz
    subst z
    change F (c (t, 0)) ∈ O
    rw [hzero]
    exact hfO ht
  have hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin n)) + m = Module.finrank ℝ E := by
    simpa only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin,
      hsheet] using hcodim
  obtain ⟨b, hb, Φ, hΦprod, _, htarget, hΦzero, hclean⟩ :=
    exists_clean_embedded_sheet_neighborhood hF hembF c hK h0K hstarK hKc (fun x _ => hiF (c x)) m
      hdim hO hFO
  refine ⟨Φ, ?_, htarget, ?_, hclean⟩
  · intro t ht
    exact hΦprod ⟨⟨ht, rfl⟩, Metric.mem_closedBall_self hb.le⟩
  · intro t ht
    exact (hΦzero (t, 0) ht).trans (congrArg F (hzero t))

private theorem Smale.TransverseCoordinates.bijective_normalDerivative_transverse_sheet
    {D B E M A Z N P : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace A N] [TopologicalSpace P] [ChartedSpace Z P]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0) {x : N} {y : P} (hx : F x ∈ Φ.target)
    (hxy : G y = F x)
    (ht :
      Function.Surjective ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) :
    Function.Bijective (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, B) (normalCoordinate Φ ∘ G) y) := by
  let Q : E →L[ℝ] B := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, B) (normalCoordinate Φ) (F x)
  let DF : A →L[ℝ] E := mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x
  let DG : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y
  have hQ : Function.Surjective Q := surjective_mfderiv_normalCoordinate Φ hx
  have hQA : Q.comp DF = 0 := normalDerivative_comp_sheet_eq_zero Φ hF hclean hx
  have hb : Function.Bijective (Q.comp DG) := bijective_normal_comp Q DF DG hQ ht hQA hdim
  have hy : G y ∈ Φ.target := hxy.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have hderiv : mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, B) (normalCoordinate Φ ∘ G) y = Q.comp DG := by
    rw [mfderiv_comp y (hnormal.mdifferentiableAt (by simp)) (hG.mdifferentiableAt (by simp)),
      hxy]
    rfl
  rw [hderiv]
  exact hb

private theorem Smale.TransverseCoordinates.bijective_normalDerivative_transverse_parametrization
    {D B E M A Z N P : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N]
    [ChartedSpace A N] [TopologicalSpace P] [ChartedSpace Z P]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {Z' : Type*} [NormedAddCommGroup Z']
    [NormedSpace ℝ Z'] {F : N → M} {G : P → M} (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G) (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0)
    (c : PartialDiffeomorph 𝓘(ℝ, Z') 𝓘(ℝ, Z) Z' P ∞) {z : Z'} (hz : z ∈ c.source) {x : N}
    (hx : F x ∈ Φ.target) (hxy : G (c z) = F x)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c z))))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) :
    Function.Bijective (fderiv ℝ ((normalCoordinate Φ ∘ G) ∘ c) z) := by
  have hb := bijective_normalDerivative_transverse_sheet Φ hF hG hclean hx hxy ht hdim
  have hy : G (c z) ∈ Φ.target := hxy.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have hg : ContMDiffAt 𝓘(ℝ, Z) 𝓘(ℝ, B) ∞ (normalCoordinate Φ ∘ G) (c z) :=
    hnormal.comp (c z) hG.contMDiffAt
  rw [← mfderiv_eq_fderiv,
    mfderiv_comp z (hg.mdifferentiableAt (by simp)) (c.mdifferentiableAt (by simp) hz)]
  exact hb.comp (Smale.PartialChart.bijective_mfderiv c hz)

private def Smale.NativeParametrization.line {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (u : D) : ℝ →L[ℝ] D :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight u

private theorem Smale.NativeParametrization.line_apply {D : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] (u : D) (t : ℝ) : line u t = t • u :=
  rfl

private theorem Smale.TransverseCoordinates.vertical_derivative_of_axis_germ {Z B : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup B] [NormedSpace ℝ B]
    {H : (ℝ × ℝ) → B} {a : Z → B} (v : Z) (hH : DifferentiableAt ℝ H 0)
    (ha : DifferentiableAt ℝ a 0) (heq : (fun t : ℝ => H (0, t)) =ᶠ[𝓝 0] (fun t => a (t • v))) :
    fderiv ℝ H (0, 0) (0, 1) = fderiv ℝ a 0 v := by
  let S : ℝ →L[ℝ] (ℝ × ℝ) := ContinuousLinearMap.inr ℝ ℝ ℝ
  let L : ℝ →L[ℝ] Z := Smale.NativeParametrization.line v
  have hHS : fderiv ℝ (H ∘ S) 0 = (fderiv ℝ H 0).comp S := by
    rw [fderiv_comp 0 (by simpa only [map_zero] using hH) S.differentiableAt, map_zero, S.fderiv]
  have haL : fderiv ℝ (a ∘ L) 0 = (fderiv ℝ a 0).comp L := by
    rw [fderiv_comp 0 (by simpa only [map_zero] using ha) L.differentiableAt, map_zero, L.fderiv]
  have heq' : (H ∘ S) =ᶠ[𝓝 (0 : ℝ)] (a ∘ L) := heq
  have hd : fderiv ℝ (H ∘ S) 0 = fderiv ℝ (a ∘ L) 0 := heq'.fderiv_eq
  rw [hHS, haL] at hd
  have hval := congrArg (fun T : ℝ →L[ℝ] B => T 1) hd
  change fderiv ℝ H (0 : ℝ × ℝ) (0, 1) = fderiv ℝ a 0 v
  simpa only [ContinuousLinearMap.comp_apply, S, L, Smale.NativeParametrization.line_apply,
    one_smul, ContinuousLinearMap.inr_apply] using hval

private theorem Smale.TransverseCoordinates.eventually_vertical_derivative_ne_zero {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B] {H : (ℝ × ℝ) → B} {p : ℝ × ℝ}
    (hH : ContDiffAt ℝ ∞ H p) (hn : fderiv ℝ H p (0, 1) ≠ 0) :
    ∀ᶠ q in 𝓝 p, fderiv ℝ H q (0, 1) ≠ 0 := by
  have hd : ContinuousAt (fderiv ℝ H) p := hH.continuousAt_fderiv (by simp)
  have hv : ContinuousAt (fun q => fderiv ℝ H q (0, 1)) p := hd.clm_apply continuousAt_const
  exact hv.preimage_mem_nhds (isClosed_singleton.isOpen_compl.mem_nhds hn)

private theorem
    Smale.TransverseCoordinates.corner_normalDerivative_ne_zero {D B E M A Z Z' N P : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup Z'] [NormedSpace ℝ Z']
    [TopologicalSpace N] [ChartedSpace A N] [TopologicalSpace P] [ChartedSpace Z P]
    (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ Set.range F ↔ q.2 = 0)
    (c : PartialDiffeomorph 𝓘(ℝ, Z') 𝓘(ℝ, Z) Z' P ∞) (hc : (0 : Z') ∈ c.source) {x : N}
    (hx : F x ∈ Φ.target) (hxy : G (c 0) = F x)
    (ht :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, A) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c 0))))
    (hdim : Module.finrank ℝ Z = Module.finrank ℝ B) {k : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W) (hW : IsOpen W) (h0W : (0 : ℝ × ℝ) ∈ W) {v : Z'}
    (hv : v ≠ 0) (haxis : ∀ t, (0, t) ∈ W → k (0, t) = G (c (t • v))) :
    fderiv ℝ (normalCoordinate Φ ∘ k) (0, 0) (0, 1) ≠ 0 ∧
      ∀ᶠ q in 𝓝 (0 : ℝ × ℝ), fderiv ℝ (normalCoordinate Φ ∘ k) q (0, 1) ≠ 0 := by
  let H := normalCoordinate Φ ∘ k
  let a := (normalCoordinate Φ ∘ G) ∘ c
  have hk0 : k (0 : ℝ × ℝ) = F x := by
    have h := haxis 0 h0W
    rw [zero_smul] at h
    exact h.trans hxy
  have hkΦ : k (0 : ℝ × ℝ) ∈ Φ.target := hk0.symm ▸ hx
  have hnormal := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hkΦ)
  have hH : ContDiffAt ℝ ∞ H 0 := (hnormal.comp 0 (hk.contMDiffAt (hW.mem_nhds h0W))).contDiffAt
  have hy : G (c 0) ∈ Φ.target := hxy.symm ▸ hx
  have hnormalG := (contMDiffOn_normalCoordinate Φ).contMDiffAt (Φ.open_target.mem_nhds hy)
  have ha : ContDiffAt ℝ ∞ a 0 :=
    ((hnormalG.comp (c 0) hG.contMDiffAt).comp 0
        (c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hc))).contDiffAt
  have haxisW : ∀ᶠ t : ℝ in 𝓝 0, (0, t) ∈ W :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hW.mem_nhds h0W)
  have heq : (fun t : ℝ => H (0, t)) =ᶠ[𝓝 0] (fun t => a (t • v)) := by
    filter_upwards [haxisW] with t htW
    exact congrArg (normalCoordinate Φ) (haxis t htW)
  have hderiv :=
    vertical_derivative_of_axis_germ v (hH.differentiableAt (by simp))
      (ha.differentiableAt (by simp)) heq
  have hbij : Function.Bijective (fderiv ℝ a 0) :=
    bijective_normalDerivative_transverse_parametrization Φ hF hG hclean c hc hx hxy ht hdim
  have hn : fderiv ℝ H (0, 0) (0, 1) ≠ 0 := by
    rw [hderiv]
    intro hz
    exact hv (hbij.1 (hz.trans (map_zero (fderiv ℝ a 0)).symm))
  exact ⟨hn, eventually_vertical_derivative_ne_zero hH hn⟩

private theorem Smale.StripCoordinates.exists_smooth_strip_matching_germs {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {v : ℝ → B}
    {F₀ F₁ : (ℝ × ℝ) → Space A B} (hv : ContDiff ℝ ∞ v) (hF₀ : ContDiff ℝ ∞ F₀)
    (hF₁ : ContDiff ℝ ∞ F₁) (hc₀ : (fun t : ℝ => F₀ (t, 0)) =ᶠ[𝓝 0] Smale.StripCoordinates.center)
    (hc₁ : (fun t : ℝ => F₁ (t, 0)) =ᶠ[𝓝 1] Smale.StripCoordinates.center)
    (hn₀ : normalDerivative F₀ =ᶠ[𝓝 (0 : ℝ)] v) (hn₁ : normalDerivative F₁ =ᶠ[𝓝 (1 : ℝ)] v) :
    ∃ F : (ℝ × ℝ) → Space A B,
      ContDiff ℝ ∞ F ∧
        (∀ t, F (t, 0) = Smale.StripCoordinates.center t) ∧
          (∀ t, normalDerivative F t = v t) ∧ (F =ᶠ[𝓝 (0, 0)] F₀) ∧ (F =ᶠ[𝓝 (1, 0)] F₁) := by
  have hgood₀ :
    {t : ℝ |
        F₀ (t, 0) = Smale.StripCoordinates.center t ∧ normalDerivative F₀ t = v t ∧ t < 1 / 3} ∈
      𝓝 (0 : ℝ) := by
    filter_upwards [hc₀, hn₀, Iio_mem_nhds (show (0 : ℝ) < 1 / 3 by norm_num)] with t hc hn ht
    exact ⟨hc, hn, ht⟩
  have hgood₁ :
    {t : ℝ |
        F₁ (t, 0) = Smale.StripCoordinates.center t ∧ normalDerivative F₁ t = v t ∧ 2 / 3 < t} ∈
      𝓝 (1 : ℝ) := by
    filter_upwards [hc₁, hn₁, Ioi_mem_nhds (show (2 / 3 : ℝ) < 1 by norm_num)] with t hc hn ht
    exact ⟨hc, hn, ht⟩
  obtain ⟨β₀, _, hβ₀⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℝ)) (0 : ℝ)).mem_iff.mp hgood₀
  obtain ⟨β₁, _, hβ₁⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, ℝ)) (1 : ℝ)).mem_iff.mp hgood₁
  have hcβ₀ (t : ℝ) (ht : β₀ t ≠ 0) : F₀ (t, 0) = Smale.StripCoordinates.center t :=
    (hβ₀ (subset_tsupport β₀ ht)).1
  have hcβ₁ (t : ℝ) (ht : β₁ t ≠ 0) : F₁ (t, 0) = Smale.StripCoordinates.center t :=
    (hβ₁ (subset_tsupport β₁ ht)).1
  have hnβ₀ (t : ℝ) (ht : β₀ t ≠ 0) : normalDerivative F₀ t = v t :=
    (hβ₀ (subset_tsupport β₀ ht)).2.1
  have hnβ₁ (t : ℝ) (ht : β₁ t ≠ 0) : normalDerivative F₁ t = v t :=
    (hβ₁ (subset_tsupport β₁ ht)).2.1
  have hβ₀zero : (β₀ : ℝ → ℝ) =ᶠ[𝓝 (1 : ℝ)] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro ht
    have hbad : (1 : ℝ) < 1 / 3 := (hβ₀ ht).2.2
    norm_num at hbad
  have hβ₁zero : (β₁ : ℝ → ℝ) =ᶠ[𝓝 (0 : ℝ)] 0 := by
    apply notMem_tsupport_iff_eventuallyEq.mp
    intro ht
    have hbad : (2 / 3 : ℝ) < 0 := (hβ₁ ht).2.2
    norm_num at hbad
  let F := blend v F₀ F₁ β₀ β₁
  have hF : ContDiff ℝ ∞ F :=
    contDiff_blend hv hF₀ hF₁ β₀.contMDiff.contDiff β₁.contMDiff.contDiff
  refine
    ⟨F, hF, blend_zero hcβ₀ hcβ₁,
      normalDerivative_blend hv hF₀ hF₁ β₀.contMDiff.contDiff β₁.contMDiff.contDiff hnβ₀ hnβ₁, ?_,
      ?_⟩
  · have hp : Filter.Tendsto (Prod.fst : ℝ × ℝ → ℝ) (𝓝 (0, 0)) (𝓝 0) :=
      continuous_fst.continuousAt.tendsto
    filter_upwards [hp β₀.eventuallyEq_one, hp hβ₁zero] with p hp₀ hp₁
    exact blend_eq_left hp₀ hp₁
  · have hp : Filter.Tendsto (Prod.fst : ℝ × ℝ → ℝ) (𝓝 (1, 0)) (𝓝 1) :=
      continuous_fst.continuousAt.tendsto
    filter_upwards [hp hβ₀zero, hp β₁.eventuallyEq_one] with p hp₀ hp₁
    exact blend_eq_right hp₀ hp₁

private theorem Smale.StripCoordinates.exists_clean_strip_neighborhood {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hc : ∀ t, F (t, 0) = Smale.StripCoordinates.center t) (hD : ∀ t, normalDerivative F t = v t)
    (hn : ∀ t ∈ Set.Icc (0 : ℝ) 1, v t ≠ 0) {O : Set (Space A B)} (hO : IsOpen O)
    (hcenterO : Set.MapsTo Smale.StripCoordinates.center (Set.Icc (0 : ℝ) 1) O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ W : Set (ℝ × ℝ),
          IsOpen W ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
              Set.InjOn F W ∧
                Set.MapsTo F W O ∧
                  (∀ p ∈ W, Function.Injective (fderiv ℝ F p)) ∧
                    (∀ p ∈ W, (F p).2 = 0 ↔ p.2 = 0) ∧
                      Topology.IsClosedEmbedding
                        (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => F p) := by
  let K := Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := CompactIccSpace.isCompact_Icc.prod isCompact_singleton
  have hFK : Set.InjOn F K := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨u, r⟩ ⟨hu, hr⟩ heq
    have hs0 : s = 0 := hs
    have hr0 : r = 0 := hr
    subst s
    subst r
    have htu : t = u := by
      simpa only [hc, Smale.StripCoordinates.center] using
        congrArg (fun q : Space A B => q.1.1) heq
    exact Prod.ext htu rfl
  have hiF : ∀ p ∈ K, Function.Injective (fderiv ℝ F p) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    apply injective_fderiv_at_center (hF.contDiffAt.differentiableAt (by simp)) hc
    rw [hD t]
    exact hn t ht
  have hiFM : ∀ p ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, Space A B) F p) := by
    intro p hp
    rw [mfderiv_eq_fderiv]
    exact hiF p hp
  obtain ⟨V, hV, hKV, hinjV⟩ :=
    Smale.ManifoldImmersion.exists_open_injOn_near_compact hF.contMDiff hK hFK hiFM
  let Q := detector v F
  have hQ : ContDiff ℝ ∞ Q := contDiff_detector hv hF
  have hQK : Set.InjOn Q K := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩ ⟨u, r⟩ ⟨hu, hr⟩ heq
    have hs0 : s = 0 := hs
    have hr0 : r = 0 := hr
    subst s
    subst r
    have htu : t = u := congrArg Prod.fst heq
    exact Prod.ext htu rfl
  have hiQ : ∀ p ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) Q p) := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    rw [mfderiv_eq_fderiv]
    exact injective_fderiv_detector_at_center hv hF hc hD (hn t ht)
  obtain ⟨T, hT, hKT, hinjT⟩ :=
    Smale.ManifoldImmersion.exists_open_injOn_near_compact hQ.contMDiff hK hQK hiQ
  let I := {p : ℝ × ℝ | Function.Injective (fderiv ℝ F p)}
  have hI : IsOpen I :=
    ContinuousLinearMap.isOpen_injective.preimage (hF.continuous_fderiv (by simp))
  let W := ((V ∩ T) ∩ I) ∩ (F ⁻¹' O ∩ (fun p : ℝ × ℝ => (p.1, 0)) ⁻¹' T)
  have hW : IsOpen W :=
    ((hV.inter hT).inter hI).inter
      ((hO.preimage hF.continuous).inter (hT.preimage (continuous_fst.prodMk continuous_const)))
  have hKW : K ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    have hpK : (t, (0 : ℝ)) ∈ K := ⟨ht, rfl⟩
    refine ⟨⟨⟨hKV hpK, hKT hpK⟩, hiF _ hpK⟩, ⟨?_, hKT hpK⟩⟩
    change F (t, 0) ∈ O
    rw [hc]
    exact hcenterO ht
  obtain ⟨ε, hε, hprod⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hW hKW
  have hrect : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hprod
    refine ⟨ht, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  have hinjW : Set.InjOn F W := hinjV.mono (fun _ hp => hp.1.1.1)
  refine ⟨ε, hε, W, hW, hrect, hinjW, fun _ hp => hp.2.1, fun _ hp => hp.1.2, ?_, ?_⟩
  · rintro ⟨t, s⟩ hp
    constructor
    · intro hz
      have heq : Q (t, s) = Q (t, 0) := by
        change detector v F (t, s) = detector v F (t, 0)
        rw [detector_zero hc]
        change (t, ⟪v t, (F (t, s)).2⟫_ℝ) = (t, 0)
        rw [hz, inner_zero_right]
      exact congrArg Prod.snd (hinjT hp.1.1.2 hp.2.2 heq)
    · intro hs
      change s = 0 at hs
      subst s
      rw [hc]
      rfl
  · let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
    let : CompactSpace R :=
      isCompact_iff_compactSpace.mp
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
    apply (hF.continuous.comp continuous_subtype_val).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjW (hrect p.property) (hrect q.property) hpq)

private theorem
    Smale.StripCoordinates.contDiff_normalDerivative {A B : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] {F : (ℝ × ℝ) → Space A B}
    (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (normalDerivative F) :=
  ((hF.snd.fderiv_right (by simp)).clm_apply contDiff_const).comp
    (contDiff_id.prodMk contDiff_const)

private theorem
    Smale.StripCoordinates.normalDerivative_congr_germ {A B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] {F G : (ℝ × ℝ) → Space A B} {t : ℝ} (heq : F =ᶠ[𝓝 (t, 0)] G) :
    normalDerivative F t = normalDerivative G t := by
  have heq' : (fun p => (F p).2) =ᶠ[𝓝 (t, (0 : ℝ))] (fun p => (G p).2) := by
    filter_upwards [heq] with p hp
    exact congrArg Prod.snd hp
  have hd : fderiv ℝ (fun p => (F p).2) (t, 0) = fderiv ℝ (fun p => (G p).2) (t, 0) :=
    heq'.fderiv_eq
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] B => L (0, 1)) hd

private theorem Smale.StripCoordinates.exists_clean_strip_matching_local_germs {A B : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B]
    [InnerProductSpace ℝ B] [FiniteDimensional ℝ B] {F₀ F₁ : (ℝ × ℝ) → Space A B}
    {U₀ U₁ : Set (ℝ × ℝ)} (hF₀ : ContDiffOn ℝ ∞ F₀ U₀) (hF₁ : ContDiffOn ℝ ∞ F₁ U₁)
    (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁) (h0U₀ : (0, 0) ∈ U₀) (h1U₁ : (1, 0) ∈ U₁)
    (hc₀ : (fun t : ℝ => F₀ (t, 0)) =ᶠ[𝓝 0] Smale.StripCoordinates.center)
    (hc₁ : (fun t : ℝ => F₁ (t, 0)) =ᶠ[𝓝 1] Smale.StripCoordinates.center)
    (hn₀ : normalDerivative F₀ 0 ≠ 0) (hn₁ : normalDerivative F₁ 1 ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) {O : Set (Space A B)} (hO : IsOpen O)
    (hcenterO : Set.MapsTo Smale.StripCoordinates.center (Set.Icc (0 : ℝ) 1) O) :
    ∃ F : (ℝ × ℝ) → Space A B,
      ContDiff ℝ ∞ F ∧
        (∀ t, F (t, 0) = Smale.StripCoordinates.center t) ∧
          (F =ᶠ[𝓝 (0, 0)] F₀) ∧
            (F =ᶠ[𝓝 (1, 0)] F₁) ∧
              ∃ ε : ℝ,
                0 < ε ∧
                  ∃ W : Set (ℝ × ℝ),
                    IsOpen W ∧
                      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
                        Set.InjOn F W ∧
                          Set.MapsTo F W O ∧
                            (∀ p ∈ W, Function.Injective (fderiv ℝ F p)) ∧
                              (∀ p ∈ W, (F p).2 = 0 ↔ p.2 = 0) ∧
                                Topology.IsClosedEmbedding
                                    (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => F p) ∧
                                  (∀ t, normalDerivative F t ≠ 0) := by
  obtain ⟨G₀, hG₀, heq₀⟩ := Smale.exists_smooth_extension_near_point hF₀.contMDiffOn hU₀ h0U₀
  obtain ⟨G₁, hG₁, heq₁⟩ := Smale.exists_smooth_extension_near_point hF₁.contMDiffOn hU₁ h1U₁
  have hnG₀ : normalDerivative G₀ 0 ≠ 0 := by rwa [normalDerivative_congr_germ heq₀]
  have hnG₁ : normalDerivative G₁ 1 ≠ 0 := by rwa [normalDerivative_congr_germ heq₁]
  obtain ⟨v, hv, hvne, hv₀, hv₁⟩ :=
    Smale.DiskFraming.exists_nonzero_smooth_curve_with_endpoint_germs
      (contDiff_normalDerivative hG₀.contDiff).contDiffOn
      (contDiff_normalDerivative hG₁.contDiff).contDiffOn isOpen_univ isOpen_univ (Set.mem_univ _)
      (Set.mem_univ _) hnG₀ hnG₁ hdim
  have hcG₀ : (fun t : ℝ => G₀ (t, 0)) =ᶠ[𝓝 0] Smale.StripCoordinates.center := by
    have hi : Filter.Tendsto (fun t : ℝ => (t, (0 : ℝ))) (𝓝 0) (𝓝 (0, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    exact (heq₀.comp_tendsto hi).trans hc₀
  have hcG₁ : (fun t : ℝ => G₁ (t, 0)) =ᶠ[𝓝 1] Smale.StripCoordinates.center := by
    have hi : Filter.Tendsto (fun t : ℝ => (t, (0 : ℝ))) (𝓝 1) (𝓝 (1, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    exact (heq₁.comp_tendsto hi).trans hc₁
  obtain ⟨F, hF, hc, hD, hFG₀, hFG₁⟩ :=
    exists_smooth_strip_matching_germs hv hG₀.contDiff hG₁.contDiff hcG₀ hcG₁ hv₀.symm hv₁.symm
  obtain ⟨ε, hε, W, hW, hrect, hinj, hmap, hi, hclean, hemb⟩ :=
    exists_clean_strip_neighborhood hv hF hc hD (fun t _ => hvne t) hO hcenterO
  exact
    ⟨F, hF, hc, hFG₀.trans heq₀, hFG₁.trans heq₁, ε, hε, W, hW, hrect, hinj, hmap, hi, hclean,
      hemb, fun t => by rw [hD t]; exact hvne t⟩

private theorem
    Smale.exists_native_clean_strip_matching_germs {A B E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [FiniteDimensional ℝ A] [NormedAddCommGroup B] [InnerProductSpace ℝ B]
    [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [T2Space M]
    (Φ :
      PartialDiffeomorph 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) (StripCoordinates.Space A B) M
        ∞)
    (hline : Set.MapsTo StripCoordinates.center (Set.Icc (0 : ℝ) 1) Φ.source) {S : Set M}
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ S ↔ q.2 = 0) {k₀ k₁ : (ℝ × ℝ) → M} {U₀ U₁ : Set (ℝ × ℝ)}
    (hk₀ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₀ U₀)
    (hk₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0U₀ : (0, 0) ∈ U₀) (h1U₁ : (1, 0) ∈ U₁)
    (hc₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] fun t => Φ (StripCoordinates.center t))
    (hc₁ : (fun t : ℝ => k₁ (t, 0)) =ᶠ[𝓝 1] fun t => Φ (StripCoordinates.center t))
    (hn₀ : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₀) (0, 0) (0, 1) ≠ 0)
    (hn₁ : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁) (1, 0) (0, 1) ≠ 0)
    (hdim : 2 ≤ Module.finrank ℝ B) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ W : Set (ℝ × ℝ),
          IsOpen W ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
              ∃ k : (ℝ × ℝ) → M,
                ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
                  Set.InjOn k W ∧
                    Set.MapsTo k W Φ.target ∧
                      Topology.IsClosedEmbedding
                          (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) ∧
                        (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                          (∀ p ∈ W, k p ∈ S ↔ p.2 = 0) ∧
                            (∀ t, k (t, 0) = Φ (StripCoordinates.center t)) ∧
                              (k =ᶠ[𝓝 (0, 0)] k₀) ∧
                                (k =ᶠ[𝓝 (1, 0)] k₁) ∧
                                  (∀ t ∈ Set.Icc (0 : ℝ) 1,
                                    fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k) (t, 0)
                                        (0, 1) ≠
                                      0) := by
  let C₀ := U₀ ∩ k₀ ⁻¹' Φ.target
  let C₁ := U₁ ∩ k₁ ⁻¹' Φ.target
  have hC₀ : IsOpen C₀ := hk₀.continuousOn.isOpen_inter_preimage hU₀ Φ.open_target
  have hC₁ : IsOpen C₁ := hk₁.continuousOn.isOpen_inter_preimage hU₁ Φ.open_target
  have hline₀ : StripCoordinates.center (0 : ℝ) ∈ Φ.source := hline (by simp)
  have hline₁ : StripCoordinates.center (1 : ℝ) ∈ Φ.source := hline (by simp)
  have h0C₀ : (0, 0) ∈ C₀ := by
    refine ⟨h0U₀, ?_⟩
    change k₀ (0, 0) ∈ Φ.target
    rw [hc₀.eq_of_nhds]
    exact Φ.map_source' hline₀
  have h1C₁ : (1, 0) ∈ C₁ := by
    refine ⟨h1U₁, ?_⟩
    change k₁ (1, 0) ∈ Φ.target
    rw [hc₁.eq_of_nhds]
    exact Φ.map_source' hline₁
  let G₀ : (ℝ × ℝ) → StripCoordinates.Space A B := Φ.invFun ∘ k₀
  let G₁ : (ℝ × ℝ) → StripCoordinates.Space A B := Φ.invFun ∘ k₁
  have hG₀ : ContDiffOn ℝ ∞ G₀ C₀ :=
    (Φ.contMDiffOn_invFun.comp (hk₀.mono Set.inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hG₁ : ContDiffOn ℝ ∞ G₁ C₁ :=
    (Φ.contMDiffOn_invFun.comp (hk₁.mono Set.inter_subset_left) (fun _ hp => hp.2)).contDiffOn
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hcG₀ : (fun t : ℝ => G₀ (t, 0)) =ᶠ[𝓝 0] StripCoordinates.center := by
    have hsource := hc.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₀)
    filter_upwards [hc₀, hsource] with t hkt ht
    change Φ.invFun (k₀ (t, 0)) = StripCoordinates.center t
    rw [hkt]
    exact Φ.left_inv' ht
  have hcG₁ : (fun t : ℝ => G₁ (t, 0)) =ᶠ[𝓝 1] StripCoordinates.center := by
    have hsource := hc.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₁)
    filter_upwards [hc₁, hsource] with t hkt ht
    change Φ.invFun (k₁ (t, 0)) = StripCoordinates.center t
    rw [hkt]
    exact Φ.left_inv' ht
  obtain
    ⟨F, hF, hFc, hFG₀, hFG₁, ε, hε, W, hW, hrect, hinjF, hsource, hiF, hcleanF, _, hnormalF⟩ :=
    StripCoordinates.exists_clean_strip_matching_local_germs hG₀ hG₁ hC₀ hC₁ h0C₀ h1C₁ hcG₀ hcG₁
      hn₀ hn₁ hdim Φ.open_source hline
  let k := Φ ∘ F
  have hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W :=
    Φ.contMDiffOn_toFun.comp hF.contMDiff.contMDiffOn hsource
  have hinjk : Set.InjOn k W := by
    intro p hp q hq heq
    exact hinjF hp hq (Φ.toPartialEquiv.injOn (hsource hp) (hsource hq) heq)
  have hemb : Topology.IsClosedEmbedding (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) := by
    let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
    let : CompactSpace R :=
      isCompact_iff_compactSpace.mp
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
    apply
      (continuousOn_iff_continuous_domRestrict.mp (hk.continuousOn.mono hrect)).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjk (hrect p.property) (hrect q.property) hpq)
  refine
    ⟨ε, hε, W, hW, hrect, k, hk, hinjk, fun _ hp => Φ.map_source' (hsource hp), hemb, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
  · intro p hp
    have hiFM : Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, StripCoordinates.Space A B) F p) := by
      rw [mfderiv_eq_fderiv]
      exact hiF p hp
    change Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (Φ ∘ F) p)
    rw [mfderiv_comp p (Φ.mdifferentiableAt (by simp) (hsource hp))
        (hF.contMDiff.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv Φ (hsource hp)).1.comp hiFM
  · intro p hp
    exact (hclean (F p) (hsource hp)).trans (hcleanF p hp)
  · intro t
    exact congrArg Φ (hFc t)
  · filter_upwards [hFG₀, hC₀.mem_nhds h0C₀] with p hFp hp
    change Φ (F p) = k₀ p
    rw [hFp]
    exact Φ.right_inv' hp.2
  · filter_upwards [hFG₁, hC₁.mem_nhds h1C₁] with p hFp hp
    change Φ (F p) = k₁ p
    rw [hFp]
    exact Φ.right_inv' hp.2
  · intro t ht
    have hp : (t, (0 : ℝ)) ∈ W := hrect ⟨ht, ⟨neg_nonpos.mpr hε.le, hε.le⟩⟩
    have heq : (TransverseCoordinates.normalCoordinate Φ ∘ k) =ᶠ[𝓝 (t, 0)] (fun p => (F p).2) := by
      filter_upwards [hW.mem_nhds hp] with p hpW
      change (Φ.invFun (Φ (F p))).2 = (F p).2
      rw [Φ.left_inv' (hsource hpW)]
    rw [heq.fderiv_eq]
    exact hnormalF t

private theorem Smale.exists_strip_neighborhood_with_exact_endpoint_contacts {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {k : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hk : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ k W) (hW : IsOpen W)
    (hKW : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ W) {B : Set M} (hB : IsClosed B)
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, k (t, 0) ∉ B)
    (hc₀ : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), k p ∈ B ↔ p.1 = 0)
    (hc₁ : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), k p ∈ B ↔ p.1 = 1) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ U : Set (ℝ × ℝ),
          IsOpen U ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ U ∧
              U ⊆ W ∧ ∀ p ∈ U, k p ∈ B ↔ p.1 = 0 ∨ p.1 = 1 := by
  obtain ⟨V₀, hV₀sub, hV₀, h0V₀⟩ := _root_.mem_nhds_iff.mp hc₀
  obtain ⟨V₁, hV₁sub, hV₁, h1V₁⟩ := _root_.mem_nhds_iff.mp hc₁
  let L := V₀ ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Iio (1 / 3)
  let R := V₁ ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ioi (2 / 3)
  let C := (W ∩ k ⁻¹' Bᶜ) ∩ (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Ioo 0 1
  have hL : IsOpen L := hV₀.inter (isOpen_Iio.preimage continuous_fst)
  have hR : IsOpen R := hV₁.inter (isOpen_Ioi.preimage continuous_fst)
  have hC : IsOpen C :=
    (hk.continuousOn.isOpen_inter_preimage hW hB.isOpen_compl).inter
      (isOpen_Ioo.preimage continuous_fst)
  let U := W ∩ ((L ∪ R) ∪ C)
  have hU : IsOpen U := hW.inter ((hL.union hR).union hC)
  have hKU : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ U := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    have htW := hKW ⟨ht, rfl⟩
    refine ⟨htW, ?_⟩
    by_cases ht0 : t = 0
    · subst t
      exact Or.inl (Or.inl ⟨h0V₀, by change (0 : ℝ) < 1 / 3; norm_num⟩)
    by_cases ht1 : t = 1
    · subst t
      exact Or.inl (Or.inr ⟨h1V₁, by change (2 / 3 : ℝ) < 1; norm_num⟩)
    have hti : t ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    exact Or.inr ⟨⟨htW, havoid t hti⟩, hti⟩
  obtain ⟨ε, hε, hprod⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hU hKU
  refine ⟨ε, hε, U, hU, ?_, Set.inter_subset_left, ?_⟩
  · rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply hprod
    refine ⟨ht, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  · intro p hp
    rcases hp.2 with (hpL | hpR) | hpC
    · have hcontact : k p ∈ B ↔ p.1 = 0 := hV₀sub hpL.1
      have hlt : p.1 < 1 / 3 := hpL.2
      constructor
      · exact fun h => Or.inl (hcontact.mp h)
      · intro h
        rcases h with h0 | h1
        · exact hcontact.mpr h0
        · rw [h1] at hlt
          norm_num at hlt
    · have hcontact : k p ∈ B ↔ p.1 = 1 := hV₁sub hpR.1
      have hgt : 2 / 3 < p.1 := hpR.2
      constructor
      · exact fun h => Or.inr (hcontact.mp h)
      · intro h
        rcases h with h0 | h1
        · rw [h0] at hgt
          norm_num at hgt
        · exact hcontact.mpr h1
    · have hnot : k p ∉ B := hpC.1.2
      have hti : p.1 ∈ Set.Ioo (0 : ℝ) 1 := hpC.2
      constructor
      · exact fun h => (hnot h).elim
      · intro h
        rcases h with h0 | h1
        · exact (hti.1.ne' h0).elim
        · exact (hti.2.ne h1).elim

private theorem
    Smale.exists_strip_along_arc_matching_parametrized_corners {E M D Z Z₀ Z₁ N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup Z₀] [NormedSpace ℝ Z₀]
    [NormedAddCommGroup Z₁] [NormedSpace ℝ Z₁] [TopologicalSpace N] [ChartedSpace D N]
    [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P] [ChartedSpace Z P] [T2Space N] [CompactSpace N]
    [CompactSpace P] {F : N → M} {G : P → M} {f : ℝ → N} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G) (hembF : Topology.IsEmbedding F)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f) (hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t))
    (c₀ : PartialDiffeomorph 𝓘(ℝ, Z₀) 𝓘(ℝ, Z) Z₀ P ∞)
    (c₁ : PartialDiffeomorph 𝓘(ℝ, Z₁) 𝓘(ℝ, Z) Z₁ P ∞) (hc₀ : (0 : Z₀) ∈ c₀.source)
    (hc₁ : (0 : Z₁) ∈ c₁.source) (hcross₀ : G (c₀ 0) = F (f 0)) (hcross₁ : G (c₁ 0) = F (f 1))
    (ht₀ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c₀ 0))))
    (ht₁ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (c₁ 0))))
    (n : ℕ) (hsheet : 1 + n = Module.finrank ℝ D)
    (hcodim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (hdimZ : 2 ≤ Module.finrank ℝ Z) {v₀ : Z₀} {v₁ : Z₁} (hv₀ : v₀ ≠ 0) (hv₁ : v₁ ≠ 0)
    (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F (f t) ∉ Set.range G) {k₀ k₁ : (ℝ × ℝ) → M}
    {U₀ U₁ : Set (ℝ × ℝ)} (hk₀ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₀ U₀)
    (hk₁ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁ U₁) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (h0U₀ : (0 : ℝ × ℝ) ∈ U₀) (h0U₁ : (0 : ℝ × ℝ) ∈ U₁)
    (hl₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] (F ∘ f))
    (hl₁ : (fun t : ℝ => k₁ (t, 0)) =ᶠ[𝓝 0] fun t => F (f (1 - t)))
    (hr₀ : ∀ s, (0, s) ∈ U₀ → k₀ (0, s) = G (c₀ (s • v₀)))
    (hr₁ : ∀ s, (0, s) ∈ U₁ → k₁ (0, s) = G (c₁ (s • v₁)))
    (hcG₀ : ∀ p ∈ U₀, k₀ p ∈ Set.range G ↔ p.1 = 0)
    (hcG₁ : ∀ p ∈ U₁, k₁ p ∈ Set.range G ↔ p.1 = 0) {O : Set M} (hO : IsOpen O)
    (hfO : Set.MapsTo (F ∘ f) (Set.Icc (0 : ℝ) 1) O) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ W : Set (ℝ × ℝ),
          IsOpen W ∧
            Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ W ∧
              ∃ k : (ℝ × ℝ) → M,
                ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k W ∧
                  Set.InjOn k W ∧
                    Set.MapsTo k W O ∧
                      Topology.IsClosedEmbedding
                          (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) ∧
                        (∀ p ∈ W, Function.Injective (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k p)) ∧
                          (∀ p ∈ W, k p ∈ Set.range F ↔ p.2 = 0) ∧
                            (∀ p ∈ W, k p ∈ Set.range G ↔ p.1 = 0 ∨ p.1 = 1) ∧
                              (∀ t ∈ Set.Icc (0 : ℝ) 1, k (t, 0) = F (f t)) ∧
                                (k =ᶠ[𝓝 (0, 0)] k₀) ∧
                                  (k =ᶠ[𝓝 (1, 0)] k₁ ∘ StripCoordinates.reverse) ∧
                                    Nonempty
                                      (StripNormalData (EuclideanSpace ℝ (Fin n))
                                        (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z))) (E := E)
                                        (Set.range F) k) := by
  obtain ⟨Φ, hline, htarget, hzero, hclean⟩ :=
    exists_clean_ambient_chart_along_embedded_arc hF hembF hiF hf hinjf hif n (Module.finrank ℝ Z)
      hsheet hcodim hO hfO
  have hline₀ := hline (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
  have hline₁ := hline (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
  have hx₀ : F (f 0) ∈ Φ.target := by
    have h := Φ.map_source' hline₀
    rwa [hzero 0 hline₀] at h
  have hx₁ : F (f 1) ∈ Φ.target := by
    have h := Φ.map_source' hline₁
    rwa [hzero 1 hline₁] at h
  have hdim :
    Module.finrank ℝ Z = Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z))) :=
    finrank_euclideanSpace_fin.symm
  have hn₀ :=
    (TransverseCoordinates.corner_normalDerivative_ne_zero Φ hF hG hclean c₀ hc₀ hx₀ hcross₀ ht₀
        hdim hk₀ hU₀ h0U₀ hv₀ hr₀).1
  have hn₁ :=
    (TransverseCoordinates.corner_normalDerivative_ne_zero Φ hF hG hclean c₁ hc₁ hx₁ hcross₁ ht₁
        hdim hk₁ hU₁ h0U₁ hv₁ hr₁).1
  let k₁' := k₁ ∘ StripCoordinates.reverse
  let U₁' := StripCoordinates.reverse ⁻¹' U₁
  have hU₁' : IsOpen U₁' := hU₁.preimage StripCoordinates.contDiff_reverse.continuous
  have h1U₁' : (1, 0) ∈ U₁' := by
    change StripCoordinates.reverse (1, 0) ∈ U₁
    rw [StripCoordinates.reverse_one_zero]
    exact h0U₁
  have hk₁' : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k₁' U₁' :=
    hk₁.comp StripCoordinates.contDiff_reverse.contMDiff.contMDiffOn (fun _ hp => hp)
  have hk₁zero : k₁ (0, 0) = F (f 1) := by simpa only [sub_zero] using hl₁.eq_of_nhds
  have hk₁Phi : k₁ (0, 0) ∈ Φ.target := hk₁zero.symm ▸ hx₁
  have hnormal :=
    (TransverseCoordinates.contMDiffOn_normalCoordinate Φ).contMDiffAt
      (Φ.open_target.mem_nhds hk₁Phi)
  have hH₁ : DifferentiableAt ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁) (0, 0) :=
    (hnormal.comp (0, 0) (hk₁.contMDiffAt (hU₁.mem_nhds h0U₁))).contDiffAt.differentiableAt
      (by simp)
  have hn₁' : fderiv ℝ (TransverseCoordinates.normalCoordinate Φ ∘ k₁') (1, 0) (0, 1) ≠ 0 := by
    change
      fderiv ℝ ((TransverseCoordinates.normalCoordinate Φ ∘ k₁) ∘ StripCoordinates.reverse) (1, 0)
          (0, 1) ≠
        0
    rw [StripCoordinates.vertical_derivative_reverse hH₁]
    exact hn₁
  have hcenter :
    Continuous
      (StripCoordinates.center :
        ℝ →
          StripCoordinates.Space (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z)))) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  have hmatch₀ : (fun t : ℝ => k₀ (t, 0)) =ᶠ[𝓝 0] fun t => Φ (StripCoordinates.center t) := by
    have hsource := hcenter.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₀)
    filter_upwards [hsource, hl₀] with t hs heq
    exact heq.trans (hzero t hs).symm
  have hrev : Filter.Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 0) := by
    have he : Filter.Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) :=
      (show Continuous (fun t : ℝ => 1 - t) by fun_prop).continuousAt
    simpa only [sub_self] using he
  have hmatch₁ : (fun t : ℝ => k₁' (t, 0)) =ᶠ[𝓝 1] fun t => Φ (StripCoordinates.center t) := by
    have hsource := hcenter.continuousAt.preimage_mem_nhds (Φ.open_source.mem_nhds hline₁)
    have hleft := hl₁.comp_tendsto hrev
    filter_upwards [hsource, hleft] with t hs heq
    change k₁ (1 - t, 0) = Φ (StripCoordinates.center t)
    change k₁ (1 - t, 0) = F (f (1 - (1 - t))) at heq
    rw [heq, hzero t hs]
    congr 2
    ring
  obtain ⟨a, ha, V, hV, hrectV, k, hk, hinjk, hmap, _, hik, hcF, hkc, hkk₀, hkk₁, hnormal⟩ :=
    exists_native_clean_strip_matching_germs Φ hline hclean hk₀ hk₁' hU₀ hU₁' h0U₀ h1U₁' hmatch₀
      hmatch₁ hn₀ hn₁' (by simpa only [finrank_euclideanSpace_fin] using hdimZ)
  have hkc' : ∀ t ∈ Set.Icc (0 : ℝ) 1, k (t, 0) = F (f t) := by
    intro t ht
    exact (hkc t).trans (hzero t (hline ht))
  have hKV : Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)} ⊆ V := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact hrectV ⟨ht, ⟨neg_nonpos.mpr ha.le, ha.le⟩⟩
  have havoidk : ∀ t ∈ Set.Ioo (0 : ℝ) 1, k (t, 0) ∉ Set.range G := by
    intro t ht
    rw [hkc' t ⟨ht.1.le, ht.2.le⟩]
    exact havoid t ht
  have hcontact₀ : ∀ᶠ p in 𝓝 ((0 : ℝ), (0 : ℝ)), k p ∈ Set.range G ↔ p.1 = 0 := by
    filter_upwards [hkk₀, hU₀.mem_nhds h0U₀] with p heq hp
    rw [heq]
    exact hcG₀ p hp
  have hcontact₁ : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), k p ∈ Set.range G ↔ p.1 = 1 := by
    filter_upwards [hkk₁, hU₁'.mem_nhds h1U₁'] with p heq hp
    have h : k p ∈ Set.range G ↔ (StripCoordinates.reverse p).1 = 0 := by
      rw [heq]
      exact hcG₁ (StripCoordinates.reverse p) hp
    change (k p ∈ Set.range G ↔ 1 - p.1 = 0) at h
    rw [sub_eq_zero] at h
    exact h.trans eq_comm
  obtain ⟨ε, hε, W, hW, hrectW, hWV, hcG⟩ :=
    exists_strip_neighborhood_with_exact_endpoint_contacts hk hV hKV
      (isCompact_range hG.continuous).isClosed havoidk hcontact₀ hcontact₁
  have hemb : Topology.IsClosedEmbedding (fun p : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε => k p) := by
    let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
    let : CompactSpace R :=
      isCompact_iff_compactSpace.mp
        (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
    apply
      (continuousOn_iff_continuous_domRestrict.mp
          (hk.continuousOn.mono (hrectW.trans hWV))).isClosedEmbedding
    intro p q hpq
    exact Subtype.ext (hinjk (hWV (hrectW p.property)) (hWV (hrectW q.property)) hpq)
  exact
    ⟨ε, hε, W, hW, hrectW, k, hk.mono hWV, hinjk.mono hWV, fun _ hp => htarget (hmap (hWV hp)),
      hemb, fun p hp => hik p (hWV hp), fun p hp => hcF p (hWV hp), hcG, hkc', hkk₀, hkk₁,
      ⟨{  chart := Φ
          line := hline
          sheet := hclean
          center := hkc
          normal_nonzero := hnormal }⟩⟩

private theorem Smale.exists_cleanStripPatch_of_tubular_arc_corners {E M D Z B N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [TopologicalSpace N] [ChartedSpace D N] [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P]
    [ChartedSpace Z P] [T2Space N] [CompactSpace N] [CompactSpace P] {F : N → M} {G : P → M}
    {f : ℝ → N} {g : ℝ → P} (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F)
    (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G) (hembF : Topology.IsEmbedding F)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f) (hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1))
    (hif : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t))
    (d : PartialDiffeomorph 𝓘(ℝ, ℝ × B) 𝓘(ℝ, Z) (ℝ × B) P ∞) (hd : ∀ t, d (t, 0) = g t)
    (hd₀ : ((0 : ℝ), (0 : B)) ∈ d.source) (hd₁ : ((1 : ℝ), (0 : B)) ∈ d.source)
    (hcross₀ : G (g 0) = F (f 0)) (hcross₁ : G (g 1) = F (f 1))
    (ht₀ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 0))))
    (ht₁ :
      Function.Surjective
        ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 1))))
    (n : ℕ) (hsheet : 1 + n = Module.finrank ℝ D)
    (hcodim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (hdimZ : 2 ≤ Module.finrank ℝ Z) (havoid : ∀ t ∈ Set.Ioo (0 : ℝ) 1, F (f t) ∉ Set.range G)
    (c₀ : CleanCornerPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) (G ∘ g))
    (c₁ :
      CleanCornerPatch (E := E) (Set.range F) (Set.range G) (fun t => F (f (1 - t)))
        (fun t => G (g (1 - t))))
    {O : Set M} (hO : IsOpen O) (hfO : Set.MapsTo (F ∘ f) (Set.Icc (0 : ℝ) 1) O) :
    ∃ k : CleanStripPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) c₀.map c₁.map,
      Nonempty
          (StripNormalData (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z))) (E := E) (Set.range F) k.map) ∧
        Set.MapsTo k.map k.domain O := by
  let d' := (NativeParametrization.translation ((1 : ℝ), (0 : B))).toPartialDiffeomorph.trans d
  have hd'₀ : (0 : ℝ × B) ∈ d'.source := by
    refine ⟨Set.mem_univ _, ?_⟩
    change 0 + ((1 : ℝ), (0 : B)) ∈ d.source
    rw [zero_add]
    exact hd₁
  have hd0 : d (0 : ℝ × B) = g 0 := hd 0
  have hd1 : d' (0 : ℝ × B) = g 1 := by
    change d (0 + ((1 : ℝ), (0 : B))) = g 1
    rw [zero_add, hd]
  have hcross₀' : G (d 0) = F (f 0) := by rw [hd0]; exact hcross₀
  have hcross₁' : G (d' 0) = F (f 1) := by rw [hd1]; exact hcross₁
  have ht₀' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d 0))) := by
    rw [hd0]; exact ht₀
  have ht₁' :
    Function.Surjective
      ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (d' 0))) := by
    rw [hd1]; exact ht₁
  have hv₀ : ((1 : ℝ), (0 : B)) ≠ 0 := fun he => one_ne_zero (congrArg Prod.fst he)
  have hv₁ : ((-1 : ℝ), (0 : B)) ≠ 0 := by
    intro he
    have he' : (-1 : ℝ) = 0 := congrArg Prod.fst he
    norm_num at he'
  have hleft₀ : (fun t : ℝ => c₀.map (t, 0)) =ᶠ[𝓝 0] (F ∘ f) := by
    have haxis :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (c₀.open_domain.mem_nhds c₀.contains_zero)
    filter_upwards [haxis] with t ht
    exact c₀.axis_first t ht
  have hleft₁ : (fun t : ℝ => c₁.map (t, 0)) =ᶠ[𝓝 0] fun t => F (f (1 - t)) := by
    have haxis :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
        (c₁.open_domain.mem_nhds c₁.contains_zero)
    filter_upwards [haxis] with t ht
    exact c₁.axis_first t ht
  have hcurve₀ (s : ℝ) : d (s • ((1 : ℝ), (0 : B))) = g s := by
    simpa only [Prod.smul_mk, smul_eq_mul, mul_one, smul_zero] using hd s
  have hcurve₁ (s : ℝ) : d' (s • ((-1 : ℝ), (0 : B))) = g (1 - s) := by
    change d (s • ((-1 : ℝ), (0 : B)) + (1, 0)) = g (1 - s)
    have he : s • ((-1 : ℝ), (0 : B)) + (1, 0) = (1 - s, 0) := by
      simp [smul_eq_mul, sub_eq_add_neg, add_comm]
    rw [he, hd]
  obtain
    ⟨ε, hε, W, hW, hrect, k, hk, hinj, hmap, hemb, hi, hfirst, hsecond, hcenter, hleft, hright,
      hnormal⟩ :=
    exists_strip_along_arc_matching_parametrized_corners hF hG hembF hiF hf hinjf hif d d' hd₀
      hd'₀ hcross₀' hcross₁' ht₀' ht₁' n hsheet hcodim hdimZ hv₀ hv₁ havoid c₀.smooth c₁.smooth
      c₀.open_domain c₁.open_domain c₀.contains_zero c₁.contains_zero hleft₀ hleft₁
      (fun s hs => (c₀.axis_second s hs).trans (congrArg G (hcurve₀ s).symm))
      (fun s hs => (c₁.axis_second s hs).trans (congrArg G (hcurve₁ s).symm))
      (fun p hp => (c₀.sheets p hp).2) (fun p hp => (c₁.sheets p hp).2) hO hfO
  let strip : CleanStripPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) c₀.map c₁.map :=
    { width := ε, width_pos := hε, domain := W, open_domain := hW, contains_strip := hrect,
      map := k, smooth := hk, injective := hinj, closed_embedding := hemb,
      derivative_injective := hi, first_sheet := hfirst, second_sheet := hsecond,
      center := hcenter, left_germ := hleft, right_germ := hright }
  exact ⟨strip, hnormal, hmap⟩

private theorem
    Smale.exists_open_neighborhoods_with_coincidences_in {X Y M : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace M] [T2Space M] {K : Set X} {L : Set Y}
    (hK : IsCompact K) (hL : IsCompact L) {f : X → M} {g : Y → M} (hf : ∀ x ∈ K, ContinuousAt f x)
    (hg : ∀ y ∈ L, ContinuousAt g y) {O : Set (X × Y)} (hO : IsOpen O)
    (hcoinc : ∀ x ∈ K, ∀ y ∈ L, f x = g y → (x, y) ∈ O) :
    ∃ U : Set X,
      ∃ V : Set Y,
        IsOpen U ∧ IsOpen V ∧ K ⊆ U ∧ L ⊆ V ∧ ∀ x ∈ U, ∀ y ∈ V, f x = g y → (x, y) ∈ O := by
  let R : Set (X × Y) := {p | f p.1 ≠ g p.2} ∪ O
  have hKR : K ×ˢ L ⊆ interior R := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    apply mem_interior_iff_mem_nhds.mpr
    by_cases hxy : f x = g y
    · exact Filter.mem_of_superset (hO.mem_nhds (hcoinc x hx y hy hxy)) (fun _ hp => Or.inr hp)
    · have hfc : ContinuousAt (fun p : X × Y => f p.1) (x, y) := (hf x hx).comp continuousAt_fst
      have hgc : ContinuousAt (fun p : X × Y => g p.2) (x, y) := (hg y hy).comp continuousAt_snd
      have hne : ∀ᶠ p : X × Y in 𝓝 (x, y), f p.1 ≠ g p.2 := (hfc.ne_iff_eventually_ne hgc).mp hxy
      exact Filter.mem_of_superset hne (fun _ hp => Or.inl hp)
  obtain ⟨U, V, hU, hV, hKU, hLV, hUV⟩ := generalized_tube_lemma hK hL isOpen_interior hKR
  refine ⟨U, V, hU, hV, hKU, hLV, ?_⟩
  intro x hx y hy hxy
  exact (interior_subset (hUV ⟨hx, hy⟩)).resolve_left (fun hne => hne hxy)

private theorem Smale.exists_open_corner_overlap {X Y D M : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace D] {k : X → M} {l : Y → M} {c : D → M} {a : X → D}
    {b : Y → D} {x₀ : X} {y₀ : Y} {W : Set D} (hW : IsOpen W) (hc : Set.InjOn c W)
    (ha : ContinuousAt a x₀) (hb : ContinuousAt b y₀) (haW : a x₀ ∈ W) (hbW : b y₀ ∈ W)
    (hk : k =ᶠ[𝓝 x₀] c ∘ a) (hl : l =ᶠ[𝓝 y₀] c ∘ b) :
    ∃ U : Set X,
      ∃ V : Set Y,
        IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ y₀ ∈ V ∧ ∀ x ∈ U, ∀ y ∈ V, k x = l y ↔ a x = b y := by
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp (hk.and (ha.preimage_mem_nhds (hW.mem_nhds haW)))
  obtain ⟨V, hVsub, hV, hyV⟩ := mem_nhds_iff.mp (hl.and (hb.preimage_mem_nhds (hW.mem_nhds hbW)))
  refine ⟨U, V, hU, hV, hxU, hyV, ?_⟩
  intro x hx y hy
  obtain ⟨hkx, hax⟩ := hUsub hx
  obtain ⟨hly, hby⟩ := hVsub hy
  rw [hkx, hly]
  exact ⟨hc hax hby, congrArg c⟩

private theorem Smale.exists_clean_strip_pair_neighborhoods {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {S T : Set M}
    {a b a₀ b₀ a₁ b₁ : ℝ → M} (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁) (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map)
    (hcoinc :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ∀ s ∈ Set.Icc (0 : ℝ) 1, a t = b s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∃ δ : ℝ,
          0 < δ ∧
            ∃ U : Set (ℝ × ℝ),
              ∃ V : Set (ℝ × ℝ),
                IsOpen U ∧
                  IsOpen V ∧
                    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ U ∧
                      Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-δ) δ ⊆ V ∧
                        U ⊆ k.domain ∧
                          V ⊆ l.domain ∧
                            ∀ p ∈ U,
                              ∀ q ∈ V,
                                k.map p = l.map q →
                                  p = q.swap ∨
                                    StripCoordinates.reverse p =
                                      (StripCoordinates.reverse q).swap := by
  have hswap : Continuous (Prod.swap : (ℝ × ℝ) → ℝ × ℝ) := by fun_prop
  have hrev := StripCoordinates.contDiff_reverse.continuous
  obtain ⟨U₀, V₀, hU₀, hV₀, h0U₀, h0V₀, hover₀⟩ :=
    exists_open_corner_overlap c₀.open_domain c₀.injective
      (continuousAt_id : ContinuousAt (id : (ℝ × ℝ) → ℝ × ℝ) (0, 0))
      (hswap.continuousAt (x := (0, 0))) c₀.contains_zero c₀.contains_zero k.left_germ l.left_germ
  obtain ⟨U₁, V₁, hU₁, hV₁, h1U₁, h1V₁, hover₁⟩ :=
    exists_open_corner_overlap c₁.open_domain c₁.injective (hrev.continuousAt (x := (1, 0)))
      ((hswap.comp hrev).continuousAt (x := (1, 0)))
      (by rw [StripCoordinates.reverse_one_zero]; exact c₁.contains_zero)
      (by
        change (StripCoordinates.reverse (1, 0)).swap ∈ c₁.domain
        rw [StripCoordinates.reverse_one_zero]; exact c₁.contains_zero)
      k.right_germ l.right_germ
  let K : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ {(0 : ℝ)}
  have hK : IsCompact K := CompactIccSpace.isCompact_Icc.prod isCompact_singleton
  have hKk : K ⊆ k.domain := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have hKl : K ⊆ l.domain := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    have hs0 : s = 0 := hs
    subst s
    exact l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  have hk : ∀ p ∈ K, ContinuousAt k.map p := fun p hp =>
    k.smooth.continuousOn.continuousAt (k.open_domain.mem_nhds (hKk hp))
  have hl : ∀ p ∈ K, ContinuousAt l.map p := fun p hp =>
    l.smooth.continuousOn.continuousAt (l.open_domain.mem_nhds (hKl hp))
  let O := (U₀ ×ˢ V₀) ∪ (U₁ ×ˢ V₁)
  have hO : IsOpen O := (hU₀.prod hV₀).union (hU₁.prod hV₁)
  have hcenter : ∀ p ∈ K, ∀ q ∈ K, k.map p = l.map q → (p, q) ∈ O := by
    rintro ⟨t, r⟩ ⟨ht, hr⟩ ⟨s, v⟩ ⟨hs, hv⟩ heq
    have hr0 : r = 0 := hr
    have hv0 : v = 0 := hv
    subst r
    subst v
    rw [k.center t ht, l.center s hs] at heq
    rcases hcoinc t ht s hs heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨h0U₀, h0V₀⟩
    · exact Or.inr ⟨h1U₁, h1V₁⟩
  obtain ⟨U', V', hU', hV', hKU', hKV', hcoinc'⟩ :=
    exists_open_neighborhoods_with_coincidences_in hK hK hk hl hO hcenter
  let U := U' ∩ k.domain
  let V := V' ∩ l.domain
  have hU : IsOpen U := hU'.inter k.open_domain
  have hV : IsOpen V := hV'.inter l.open_domain
  have hKU : K ⊆ U := fun p hp => ⟨hKU' hp, hKk hp⟩
  have hKV : K ⊆ V := fun p hp => ⟨hKV' hp, hKl hp⟩
  obtain ⟨ε, hε, hεU⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hU hKU
  obtain ⟨δ, hδ, hδV⟩ :=
    DiskFraming.exists_pos_prod_closedBall_subset CompactIccSpace.isCompact_Icc hV hKV
  have hrect {r : ℝ} {W : Set (ℝ × ℝ)} (h : Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall 0 r ⊆ W) :
    Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-r) r ⊆ W := by
    rintro ⟨t, s⟩ ⟨ht, hs⟩
    apply h
    refine ⟨ht, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] using abs_le.mpr hs
  refine
    ⟨ε, hε, δ, hδ, U, V, hU, hV, hrect hεU, hrect hδV, Set.inter_subset_right,
      Set.inter_subset_right, ?_⟩
  intro p hp q hq heq
  rcases hcoinc' p hp.1 q hq.1 heq with hleft | hright
  · exact Or.inl ((hover₀ p hleft.1 q hleft.2).mp heq)
  · exact Or.inr ((hover₁ p hright.1 q hright.2).mp heq)

private def Smale.CleanStripPatch.restrict {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [T2Space M] {S T : Set M} {a : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} (k : Smale.CleanStripPatch (E := E) S T a k₀ k₁) {ε : ℝ} (hε : 0 < ε)
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hrect : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε ⊆ U)
    (hUk : U ⊆ k.domain) : Smale.CleanStripPatch (E := E) S T a k₀ k₁ := by
  refine
    { width := ε
      width_pos := hε
      domain := U
      open_domain := hU
      contains_strip := hrect
      map := k.map
      smooth := k.smooth.mono hUk
      injective := k.injective.mono hUk
      closed_embedding := ?_
      derivative_injective := fun p hp => k.derivative_injective p (hUk hp)
      first_sheet := fun p hp => k.first_sheet p (hUk hp)
      second_sheet := fun p hp => k.second_sheet p (hUk hp)
      center := k.center
      left_germ := k.left_germ
      right_germ := k.right_germ }
  let R := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-ε) ε
  let : CompactSpace R :=
    isCompact_iff_compactSpace.mp
      (CompactIccSpace.isCompact_Icc.prod CompactIccSpace.isCompact_Icc)
  have hc : Continuous (fun p : R => k.map p) :=
    continuousOn_iff_continuous_domRestrict.mp (k.smooth.continuousOn.mono (hrect.trans hUk))
  apply hc.isClosedEmbedding
  intro p q hpq
  exact Subtype.ext (k.injective (hUk (hrect p.property)) (hUk (hrect q.property)) hpq)

private theorem Smale.exists_native_shared_corner_strip_pair_dim_two {E M D Z N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace D N]
    [IsManifold 𝓘(ℝ, D) ∞ N] [TopologicalSpace P] [ChartedSpace Z P] [IsManifold 𝓘(ℝ, Z) ∞ P]
    [T2Space N] [CompactSpace N] [T2Space P] [CompactSpace P] {F : N → M} {G : P → M}
    (hF : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ F) (hG : ContMDiff 𝓘(ℝ, Z) 𝓘(ℝ, E) ∞ G)
    (hinjF : Function.Injective F) (hinjG : Function.Injective G)
    (hiF : ∀ x, Function.Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x))
    (hiG : ∀ y, Function.Injective (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)) (hdimD : 2 ≤ Module.finrank ℝ D)
    (hdimZ : 2 ≤ Module.finrank ℝ Z)
    (hcodim : Module.finrank ℝ D + Module.finrank ℝ Z = Module.finrank ℝ E)
    (ht :
      ∀ x y,
        G y = F x →
          Function.Surjective
            ((mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F x).coprod (mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G y)))
    {x₀ x₁ : N} {y₀ y₁ : P} (hcross₀ : G y₀ = F x₀) (hcross₁ : G y₁ = F x₁) (hxy : x₀ ≠ x₁)
    (γ : Path x₀ x₁) (η : Path y₀ y₁) :
    ∃ f : C(ℝ, N),
      ∃ g : C(ℝ, P),
        ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, D) ∞ f ∧
          ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) ∞ g ∧
            f 0 = x₀ ∧
              f 1 = x₁ ∧
                g 0 = y₀ ∧
                  g 1 = y₁ ∧
                    Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
                      Topology.IsClosedEmbedding (fun t : unitInterval => g t) ∧
                        (∀ t ∈ Set.Icc (0 : ℝ) 1,
                            Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, D) f t)) ∧
                          (∀ t ∈ Set.Icc (0 : ℝ) 1,
                              Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Z) g t)) ∧
                            (∀ t ∈ Set.Ioo (0 : ℝ) 1, F (f t) ∉ Set.range G) ∧
                              (∀ t ∈ Set.Ioo (0 : ℝ) 1, G (g t) ∉ Set.range F) ∧
                                Set.range (fun t : unitInterval => F (f t)) ∩
                                      Set.range (fun t : unitInterval => G (g t)) =
                                    {F x₀, F x₁} ∧
                                  ∃ c₀ :
                                    CleanCornerPatch (E := E) (Set.range F) (Set.range G) (F ∘ f)
                                      (G ∘ g),
                                    ∃ c₁ :
                                      CleanCornerPatch (E := E) (Set.range F) (Set.range G)
                                        (fun t => F (f (1 - t))) (fun t => G (g (1 - t))),
                                      ∃ k :
                                        CleanStripPatch (E := E) (Set.range F) (Set.range G)
                                          (F ∘ f) c₀.map c₁.map,
                                        ∃ l :
                                          CleanStripPatch (E := E) (Set.range G) (Set.range F)
                                            (G ∘ g) c₀.swap.map c₁.swap.map,
                                          Nonempty
                                              (StripNormalData
                                                (EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1)))
                                                (EuclideanSpace ℝ (Fin (Module.finrank ℝ Z)))
                                                (E := E) (Set.range F) k.map) ∧
                                            Nonempty
                                                (StripNormalData
                                                  (EuclideanSpace ℝ
                                                    (Fin (Module.finrank ℝ Z - 1)))
                                                  (EuclideanSpace ℝ (Fin (Module.finrank ℝ D)))
                                                  (E := E) (Set.range G) l.map) ∧
                                              (∀ p ∈ k.domain,
                                                  ∀ q ∈ l.domain,
                                                    k.map p = l.map q →
                                                      p = q.swap ∨
                                                        StripCoordinates.reverse p =
                                                          (StripCoordinates.reverse q).swap) ∧
                                                ∀ h : ℝ,
                                                  0 < h →
                                                    Nonempty
                                                      (CleanBigonBoundary (E := E) (Set.range F)
                                                        (Set.range G) (F ∘ f) (G ∘ g) k.map l.map
                                                        h) := by
  have hfinite : (Set.range F ∩ Set.range G).Finite :=
    finite_transverse_intersections hF hG hinjF hinjG hcodim ht
  have hSF : (F ⁻¹' Set.range G).Finite := by
    have hpre : F ⁻¹' (Set.range F ∩ Set.range G) = F ⁻¹' Set.range G := by
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff]
      exact and_iff_right (Set.mem_range_self z)
    rw [← hpre]
    exact hfinite.preimage hinjF.injOn
  have hSG : (G ⁻¹' Set.range F).Finite := by
    have hpre : G ⁻¹' (Set.range F ∩ Set.range G) = G ⁻¹' Set.range F := by
      ext z
      simp only [Set.mem_preimage, Set.mem_inter_iff]
      exact and_iff_left (Set.mem_range_self z)
    rw [← hpre]
    exact hfinite.preimage hinjG.injOn
  have hy : y₀ ≠ y₁ := by
    intro heq
    apply hxy
    exact hinjF (hcross₀.symm.trans ((congrArg G heq).trans hcross₁))
  obtain ⟨f, hf, hf0, hf1, hembf, hif, havoidf, ρ, hρ, c, hsourceC, hzeroC, _⟩ :=
    exists_tubular_connecting_arc_avoiding_finite_with_global_zero γ hxy hdimD
      (Module.finrank ℝ D - 1) (by omega) hSF
  obtain ⟨g, hg, hg0, hg1, hembg, hig, havoidg, σ, hσ, d, hsourceD, hzeroD, _⟩ :=
    exists_tubular_connecting_arc_avoiding_finite_with_global_zero η hy hdimZ
      (Module.finrank ℝ Z - 1) (by omega) hSG
  have hinjf : Set.InjOn f (Set.Icc (0 : ℝ) 1) := by
    intro t ht s hs heq
    exact congrArg Subtype.val (hembf.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) heq)
  have hinjg : Set.InjOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht s hs heq
    exact congrArg Subtype.val (hembg.injective (a₁ := ⟨t, ht⟩) (a₂ := ⟨s, hs⟩) heq)
  have hinter :
    Set.range (fun t : unitInterval => F (f t)) ∩ Set.range (fun t : unitInterval => G (g t)) =
      {F x₀, F x₁} := by
    ext w
    constructor
    · rintro ⟨⟨t, rfl⟩, ⟨s, hs⟩⟩
      by_cases ht0 : (t : ℝ) = 0
      · simp only [ht0, hf0]
        exact Set.mem_insert _ _
      by_cases ht1 : (t : ℝ) = 1
      · simp only [ht1, hf1]
        exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
      have hti : (t : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0), lt_of_le_of_ne t.property.2 ht1⟩
      exact (havoidf t hti ⟨g s, hs⟩).elim
    · intro hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact ⟨⟨0, congrArg F hf0⟩, ⟨0, (congrArg G hg0).trans hcross₀⟩⟩
      · exact ⟨⟨1, congrArg F hf1⟩, ⟨1, (congrArg G hg1).trans hcross₁⟩⟩
  have hembF := (hF.continuous.isClosedEmbedding hinjF).isEmbedding
  have hembG := (hG.continuous.isClosedEmbedding hinjG).isEmbedding
  have hc₀ : ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1)))) ∈ c.source :=
    hsourceC ⟨by simp, Metric.mem_closedBall_self hρ.le⟩
  have hc₁ : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1)))) ∈ c.source :=
    hsourceC ⟨by simp, Metric.mem_closedBall_self hρ.le⟩
  have hd₀ : ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ Z - 1)))) ∈ d.source :=
    hsourceD ⟨by simp, Metric.mem_closedBall_self hσ.le⟩
  have hd₁ : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ Z - 1)))) ∈ d.source :=
    hsourceD ⟨by simp, Metric.mem_closedBall_self hσ.le⟩
  have hcross₀' : G (g 0) = F (f 0) := by rw [hf0, hg0]; exact hcross₀
  have hcross₁' : G (g 1) = F (f 1) := by rw [hf1, hg1]; exact hcross₁
  have ht₀ := ht (f 0) (g 0) hcross₀'
  have ht₁ := ht (f 1) (g 1) hcross₁'
  have hcoord :
    Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ D - 1))) +
        Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin (Module.finrank ℝ Z - 1))) =
      Module.finrank ℝ E := by
    simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
    omega
  have hcorner₀ :
    Nonempty (CleanCornerPatch (E := E) (Set.range F) (Set.range G) (F ∘ f) (G ∘ g)) := by
    simpa only [zero_add, mul_one, Function.comp_def] using
      nonempty_cleanCornerPatch_of_tubular_arcs hF hG hembF hembG c d hzeroC hzeroD hc₀ hd₀
        hcross₀' hcoord ht₀ (σ := 1) (τ := 1) one_ne_zero one_ne_zero
  have hcorner₁ :
    Nonempty
      (CleanCornerPatch (E := E) (Set.range F) (Set.range G) (fun t => F (f (1 - t)))
        (fun t => G (g (1 - t)))) := by
    simpa only [mul_neg_one, ← sub_eq_add_neg] using
      nonempty_cleanCornerPatch_of_tubular_arcs hF hG hembF hembG c d hzeroC hzeroD hc₁ hd₁
        hcross₁' hcoord ht₁ (σ := -1) (τ := -1) (by norm_num) (by norm_num)
  obtain ⟨c₀⟩ := hcorner₀
  obtain ⟨c₁⟩ := hcorner₁
  obtain ⟨stripF, hnormalF, _⟩ :=
    exists_cleanStripPatch_of_tubular_arc_corners hF hG hembF hiF hf hinjf hif d hzeroD hd₀ hd₁
      hcross₀' hcross₁' ht₀ ht₁ (Module.finrank ℝ D - 1) (by omega) hcodim hdimZ havoidf c₀ c₁
      isOpen_univ (fun _ _ => Set.mem_univ _)
  let DF₀ : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 0)
  let DF₁ : D →L[ℝ] E := mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) F (f 1)
  let DG₀ : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 0)
  let DG₁ : Z →L[ℝ] E := mfderiv 𝓘(ℝ, Z) 𝓘(ℝ, E) G (g 1)
  have ht₀' : Function.Surjective (DG₀.coprod DF₀) :=
    TransverseCoordinates.surjective_coprod_swap DF₀ DG₀ ht₀
  have ht₁' : Function.Surjective (DG₁.coprod DF₁) :=
    TransverseCoordinates.surjective_coprod_swap DF₁ DG₁ ht₁
  have hcodim' : Module.finrank ℝ Z + Module.finrank ℝ D = Module.finrank ℝ E := by omega
  obtain ⟨stripG, hnormalG, _⟩ :=
    exists_cleanStripPatch_of_tubular_arc_corners hG hF hembG hiG hg hinjg hig c hzeroC hc₀ hc₁
      hcross₀'.symm hcross₁'.symm ht₀' ht₁' (Module.finrank ℝ Z - 1) (by omega) hcodim' hdimD
      havoidg c₀.swap c₁.swap isOpen_univ (fun _ _ => Set.mem_univ _)
  have hcoinc :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ s ∈ Set.Icc (0 : ℝ) 1, (F ∘ f) t = (G ∘ g) s → (t = 0 ∧ s = 0) ∨ (t = 1 ∧ s = 1) := by
    intro t ht s hs heq
    have hmem : F (f t) ∈ ({F x₀, F x₁} : Set M) := by
      rw [← hinter]
      exact ⟨⟨⟨t, ht⟩, rfl⟩, ⟨⟨s, hs⟩, heq.symm⟩⟩
    change F (f t) = F x₀ ∨ F (f t) = F x₁ at hmem
    have h0 : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
    have h1 : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨zero_le_one, le_rfl⟩
    rcases hmem with hleft | hright
    · left
      constructor
      · exact hinjf ht h0 (hinjF (hleft.trans (congrArg F hf0).symm))
      · apply hinjg hs h0
        apply hinjG
        exact heq.symm.trans (hleft.trans ((congrArg G hg0).trans hcross₀).symm)
    · right
      constructor
      · exact hinjf ht h1 (hinjF (hright.trans (congrArg F hf1).symm))
      · apply hinjg hs h1
        apply hinjG
        exact heq.symm.trans (hright.trans ((congrArg G hg1).trans hcross₁).symm)
  obtain ⟨ε', hε', δ', hδ', U', V', hU', hV', hrectU', hrectV', hU'sub, hV'sub, hoverlap⟩ :=
    exists_clean_strip_pair_neighborhoods c₀ c₁ stripF stripG hcoinc
  let k' := stripF.restrict hε' hU' hrectU' hU'sub
  let l' := stripG.restrict hδ' hV' hrectV' hV'sub
  have hoverlap' :
    ∀ p ∈ k'.domain,
      ∀ q ∈ l'.domain,
        k'.map p = l'.map q →
          p = q.swap ∨ StripCoordinates.reverse p = (StripCoordinates.reverse q).swap :=
    hoverlap
  refine
    ⟨f, g, hf, hg, hf0, hf1, hg0, hg1, hembf, hembg, hif, hig, havoidf, havoidg, hinter, c₀, c₁,
      k', l', hnormalF, hnormalG, hoverlap', ?_⟩
  intro h hh
  exact nonempty_cleanBigonBoundary hh c₀ c₁ k' l' hoverlap'

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.nonempty_belt_tubularBigon {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ g : C(Smale.Hemisphere.Sphere 1, d.LowerLevel),
        ∃ q, g.Homotopic (ContinuousMap.const _ q))
    (g : C(Smale.Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) {a b : ℝ → d.UpperLevel}
      {k l : (ℝ × ℝ) → d.UpperLevel} {h : ℝ},
      Smale.CleanBigonBoundary (E := Smale.RegularLevel.Model E) (Set.range g)
          (Set.range d.surgery.beltSphere) a b k l h →
        Nonempty
          (Smale.TubularBigon (E := Smale.RegularLevel.Model E) (Set.range g)
            (Set.range d.surgery.beltSphere) a b k l h 3) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ := Smale.RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro hg a b k l h B
  have hT : IsClosed (Set.range d.surgery.beltSphere) := d.belt_isClosedEmbedding.isClosed_range
  have hnullbelt :=
    d.chart.surgery_beltComplement_circle_nullhomotopies hf d.radius d.radius_pos d.block
      d.lower_regular d.surgery d.oldPiece_eq hindex (by omega) hnull
  exact
    B.nonempty_tubularBigon_of_complement_contractions g hg hT hnullbelt
      (by simp [Smale.RegularLevel.Model, hdim]) (by simp [Smale.RegularLevel.Model, hdim]) 3
      (by simp [Smale.RegularLevel.Model, hdim])

attribute [local instance 100] Classical.propDecidable in
private theorem Smale.ManifoldMorse.MorseSurgeryData.exists_belt_tubular_strip_pair {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (d : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ g : C(Smale.Hemisphere.Sphere 1, d.LowerLevel),
        ∃ q, g.Homotopic (ContinuousMap.const _ q))
    (g : C(Smale.Hemisphere.Sphere 2, d.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf d.upper_regular
    letI : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := d.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          d.surgery.beltSphere y = g x →
            Function.Surjective
              ((mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g x).coprod
                (mfderiv (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) d.surgery.beltSphere y)))
      (x₀ x₁ : Smale.Hemisphere.Sphere 2)
      (y₀ y₁ : Smale.PuncturedHandle.UnitSphere d.chart.PositiveCoordinates),
      d.surgery.beltSphere y₀ = g x₀ →
        d.surgery.beltSphere y₁ = g x₁ →
          x₀ ≠ x₁ →
            ∃ a b : ℝ → d.UpperLevel,
              a 0 = g x₀ ∧
                a 1 = g x₁ ∧
                  b 0 = g x₀ ∧
                    b 1 = g x₁ ∧
                      ∃ k₀ k₁ l₀ l₁ : (ℝ × ℝ) → d.UpperLevel,
                        ∃ k :
                          Smale.CleanStripPatch (E := Smale.RegularLevel.Model E) (Set.range g)
                            (Set.range d.surgery.beltSphere) a k₀ k₁,
                          ∃ l :
                            Smale.CleanStripPatch (E := Smale.RegularLevel.Model E)
                              (Set.range d.surgery.beltSphere) (Set.range g) b l₀ l₁,
                            Nonempty
                                (Smale.StripNormalData (EuclideanSpace ℝ (Fin 1))
                                  (EuclideanSpace ℝ (Fin 3)) (E := Smale.RegularLevel.Model E)
                                  (Set.range g) k.map) ∧
                              Nonempty
                                  (Smale.StripNormalData (EuclideanSpace ℝ (Fin 2))
                                    (EuclideanSpace ℝ (Fin 2)) (E := Smale.RegularLevel.Model E)
                                    (Set.range d.surgery.beltSphere) l.map) ∧
                                ∀ h : ℝ,
                                  0 < h →
                                    Nonempty
                                      (Smale.TubularBigon (E := Smale.RegularLevel.Model E)
                                        (Set.range g) (Set.range d.surgery.beltSphere) a b k.map
                                        l.map h 3) := by
  let _ := Smale.RegularLevel.chartedSpace hf d.upper_regular
  let _ := Smale.RegularLevel.isManifold hf d.upper_regular
  let _ : CompactSpace d.UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  have hpos : Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1 := by
    have hh := d.chart.finrank_negative_add_positive
    omega
  let _ : Fact (Module.finrank ℝ d.chart.PositiveCoordinates = 3 + 1) := ⟨hpos⟩
  intro hg hinj hi ht x₀ x₁ y₀ y₁ hcross₀ hcross₁ hxy
  have hpath₂ : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isPathConnected_sphere (by simp [← Module.finrank_eq_rank]) 0 (by norm_num)
  have hpath₃ : IsPathConnected (Metric.sphere (0 : d.chart.PositiveCoordinates) 1) :=
    isPathConnected_sphere (by rw [← Module.finrank_eq_rank, hpos]; norm_num) 0 (by norm_num)
  let γ : Path x₀ x₁ := (hpath₂.joinedIn x₀ x₀.property x₁ x₁.property).joined_subtype.somePath
  let η : Path y₀ y₁ := (hpath₃.joinedIn y₀ y₀.property y₁ y₁.property).joined_subtype.somePath
  have hG := d.belt_smooth hf 3
  have hiG := d.belt_derivative_injective hf 3
  obtain
    ⟨α, β, -, -, hα₀, hα₁, hβ₀, hβ₁, -, -, -, -, -, -, -, c₀, c₁, k, l, hnK, hnL, -, hboundary⟩ :=
    Smale.exists_native_shared_corner_strip_pair_dim_two hg hG hinj
      d.belt_isClosedEmbedding.injective hi hiG (by simp) (by simp)
      (by simp [Smale.RegularLevel.Model, hdim]) ht hcross₀ hcross₁ hxy γ η
  refine
    ⟨g ∘ α, d.surgery.beltSphere ∘ β, ?_, ?_, ?_, ?_, c₀.map, c₁.map, c₀.swap.map, c₁.swap.map, k,
      l, ?_, ?_, ?_⟩
  · change g (α 0) = g x₀
    rw [hα₀]
  · change g (α 1) = g x₁
    rw [hα₁]
  · change d.surgery.beltSphere (β 0) = g x₀
    rw [hβ₀, hcross₀]
  · change d.surgery.beltSphere (β 1) = g x₁
    rw [hβ₁, hcross₁]
  · have transport (m n : ℕ) (hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) - 1 = m)
      (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = n) :
      Nonempty
        (Smale.StripNormalData (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)) (E :=
          Smale.RegularLevel.Model E) (Set.range g) k.map) := by
      subst m
      subst n
      exact hnK
    exact transport 1 3 (by simp) (by simp)
  · have transport (m n : ℕ) (hm : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1 = m)
      (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = n) :
      Nonempty
        (Smale.StripNormalData (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)) (E :=
          Smale.RegularLevel.Model E) (Set.range d.surgery.beltSphere) l.map) := by
      subst m
      subst n
      exact hnL
    exact transport 2 2 (by simp) (by simp)
  · intro h hh
    obtain ⟨B⟩ := hboundary h hh
    exact d.nonempty_belt_tubularBigon hf hdim hindex hnull g hg B

private def Smale.FiberRestriction.embed {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : U →L[ℝ] V) : (X × U) →L[ℝ] (X × V) :=
  (ContinuousLinearMap.id ℝ X).prodMap i

private def Smale.FiberRestriction.project {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (r : V →L[ℝ] U) : (X × V) →L[ℝ] (X × U) :=
  (ContinuousLinearMap.id ℝ X).prodMap r

private theorem Smale.FiberRestriction.project_embed {X U V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i)
    (z : X × U) : project r (embed i z) = z :=
  Prod.ext rfl (hi z.2)

private theorem
    Smale.FiberRestriction.embed_project_of_normal {X U V : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
    [NormedSpace ℝ V] (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i) {z : X × V}
    {w : X × U} (hz : z.2 = i w.2) : embed i (project r z) = z := by
  apply Prod.ext
  · rfl
  · change i (r z.2) = z.2
    rw [hz, hi]

private def Smale.FiberRestriction.restrict {X U V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : U →L[ℝ] V) (r : V →L[ℝ] U) (hi : Function.LeftInverse r i)
    (d : Diffeomorph 𝓘(ℝ, X × V) 𝓘(ℝ, X × V) (X × V) (X × V) ∞) (hnormal : ∀ z, (d z).2 = z.2) :
    Diffeomorph 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) (X × U) (X × U) ∞
    where
  toEquiv :=
    { toFun := fun z => project r (d (embed i z))
      invFun := fun z => project r (d.symm (embed i z))
      left_inv := by
        intro z
        have hfix := embed_project_of_normal i r hi (w := z) (hnormal (embed i z))
        change project r (d.symm (embed i (project r (d (embed i z))))) = z
        rw [hfix, d.symm_apply_apply, project_embed i r hi]
      right_inv := by
        intro z
        have hnormalInv : (d.symm (embed i z)).2 = i z.2 := by
          have he := hnormal (d.symm (embed i z))
          rw [d.apply_symm_apply] at he
          exact he.symm
        have hfix := embed_project_of_normal i r hi (w := z) hnormalInv
        change project r (d (embed i (project r (d.symm (embed i z))))) = z
        rw [hfix, d.apply_symm_apply, project_embed i r hi] }
  contMDiff_toFun := by
    change ContMDiff 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) ∞ (fun z => project r (d (embed i z)))
    exact (project r).contDiff.contMDiff.comp (d.contMDiff.comp (embed i).contDiff.contMDiff)
  contMDiff_invFun := by
    change ContMDiff 𝓘(ℝ, X × U) 𝓘(ℝ, X × U) ∞ (fun z => project r (d.symm (embed i z)))
    exact (project r).contDiff.contMDiff.comp (d.symm.contMDiff.comp (embed i).contDiff.contMDiff)

private theorem Smale.SmallPerturbation.lipschitzWith_slice {E : Type*} [NormedAddCommGroup E]
    {β : ℝ × E → ℝ} {k : ℝ≥0} (hβ : LipschitzWith k β) (t : ℝ) :
    LipschitzWith k (fun x : E => β (t, x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    Dist.dist (β (t, x)) (β (t, y)) ≤ (k : ℝ) * Dist.dist (t, x) (t, y) := hβ.dist_le_mul _ _
    _ = (k : ℝ) * Dist.dist x y := by
      rw [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg : 0 ≤ Dist.dist x y)]

private theorem Smale.SmallPerturbation.exists_uniform_radius_bumpTranslation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {β : ℝ × E → ℝ}
    (hs : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ t : ℝ,
          ∀ a : E,
            ‖a‖ < ε →
              ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞,
                (∀ x, d x = x + β (t, x) • a) ∧ ∀ x ∉ tsupport (fun y : E => β (t, y)), d x = x :=
  by
  obtain ⟨k, hk⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcompact hs (by simp)
  have hkpos : 0 < (k : ℝ) + 1 := by positivity
  refine ⟨((k : ℝ) + 1)⁻¹, inv_pos.mpr hkpos, ?_⟩
  intro t a ha
  have hmul : ((k : ℝ) + 1) * ‖a‖ < 1 := by
    calc
      ((k : ℝ) + 1) * ‖a‖ < ((k : ℝ) + 1) * ((k : ℝ) + 1)⁻¹ := mul_lt_mul_of_pos_left ha hkpos
      _ = 1 := mul_inv_cancel₀ hkpos.ne'
  have hsmall : k * ‖a‖₊ < 1 := by
    have hr : (k : ℝ) * ‖a‖ < 1 := by nlinarith [norm_nonneg a]
    exact hr
  have hslice : ContDiff ℝ ∞ (fun x : E => β (t, x)) :=
    hs.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨bumpTranslation hslice (lipschitzWith_slice hk t) a hsmall, fun _ => rfl, ?_⟩
  intro x hx
  apply bumpTranslation_eq_of_zero
  by_contra hne
  exact hx (subset_tsupport (fun y : E => β (t, y)) hne)

private def Smale.SmallPerturbation.composeFamily {E : Type*} (B : ℕ → ℝ × E → E) : ℕ → ℝ × E → E
  | 0, p => p.2
  | n + 1, p => B n (p.1, composeFamily B n p)

private theorem Smale.SmallPerturbation.contDiff_composeFamily {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {B : ℕ → ℝ × E → E} (hB : ∀ i, ContDiff ℝ ∞ (B i)) (n : ℕ) :
    ContDiff ℝ ∞ (composeFamily B n) := by
  induction n with
  | zero => exact contDiff_snd
  | succ n ih => exact (hB n).comp (contDiff_fst.prodMk ih)

private theorem Smale.SmallPerturbation.composeFamily_zero {E : Type*} {B : ℕ → ℝ × E → E}
    (hB : ∀ i x, B i (0, x) = x) (n : ℕ) (x : E) : composeFamily B n (0, x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hB n _).trans ih

private theorem
    Smale.SmallPerturbation.composeFamily_fixed {E : Type*} {B : ℕ → ℝ × E → E} {C : Set E}
    (hB : ∀ i t x, x ∉ C → B i (t, x) = x) (n : ℕ) (t : ℝ) {x : E} (hx : x ∉ C) :
    composeFamily B n (t, x) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change B n (t, composeFamily B n (t, x)) = x
    rw [ih]
    exact hB n t x hx

private theorem Smale.SmallPerturbation.composeFamily_preserves {E : Type*} {F : Type*}
    {B : ℕ → ℝ × E → E} {f : E → F} (hB : ∀ i t x, f (B i (t, x)) = f x) (n : ℕ) (t : ℝ) (x : E) :
    f (composeFamily B n (t, x)) = f x := by
  induction n with
  | zero => rfl
  | succ n ih => exact (hB n t _).trans ih

private theorem Smale.SmallPerturbation.exists_diffeomorph_composeFamily {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {B : ℕ → ℝ × E → E}
    (hB : ∀ i t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = B i (t, x)) (n : ℕ) (t : ℝ) :
    ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞, ∀ x, d x = composeFamily B n (t, x) := by
  induction n with
  | zero => exact ⟨Diffeomorph.refl 𝓘(ℝ, E) E ∞, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨d, hd⟩ := ih
    obtain ⟨e, he⟩ := hB n t
    refine ⟨d.trans e, ?_⟩
    intro x
    change e (d x) = B n (t, composeFamily B n (t, x))
    rw [he, hd]

private def Smale.WhitneyPairModel.scaledBigonEmbedding (r : ℝ) (p : ℝ × ℝ) : Space :=
  bigonEmbedding (r * p.1, r ^ 2 * p.2)

private theorem Smale.WhitneyPairModel.scaledBigonEmbedding_one (p : ℝ × ℝ) :
    scaledBigonEmbedding 1 p = bigonEmbedding p := by
  simp only [scaledBigonEmbedding, one_mul, one_pow, Prod.eta]

private theorem Smale.WhitneyPairModel.continuous_scaledBigonEmbedding :
    Continuous (fun z : ℝ × (ℝ × ℝ) => scaledBigonEmbedding z.1 z.2) := by
  unfold scaledBigonEmbedding bigonEmbedding
  fun_prop

private theorem
    Smale.WhitneyPairModel.exists_scaled_bigon_in_open {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : Set.MapsTo bigonEmbedding (bigon h) U) :
    ∃ r : ℝ, 1 < r ∧ Set.MapsTo (scaledBigonEmbedding r) (bigon h) U := by
  have hnear : ∀ᶠ r in 𝓝 (1 : ℝ), ∀ p ∈ bigon h, scaledBigonEmbedding r p ∈ U := by
    apply (isCompact_bigon hh).eventually_forall_of_forall_eventually
    intro p hp
    apply (continuous_scaledBigonEmbedding.continuousAt (x := (1, p))).preimage_mem_nhds
    apply hU.mem_nhds
    simpa only [scaledBigonEmbedding_one] using hKU hp
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  have hrball : (1 + ε / 2 : ℝ) ∈ Metric.ball 1 ε := by
    change Dist.dist (1 + ε / 2) 1 < ε
    rw [Real.dist_eq]
    have heq : 1 + ε / 2 - 1 = ε / 2 := by ring
    rw [heq, abs_of_pos (half_pos hε)]
    exact half_lt_self hε
  exact ⟨1 + ε / 2, by linarith, fun p hp => hball hrball p hp⟩

private theorem
    Smale.WhitneyPairModel.enlarged_cap_parametrization {h r : ℝ} (hr : 0 < r) {p : ℝ × ℝ}
    (hp : 0 ≤ p.2 ∧ h * p.1 ^ 2 + p.2 ≤ h * r ^ 2) :
    ∃ q ∈ bigon h, scaledBigonEmbedding r q = bigonEmbedding p := by
  let q : ℝ × ℝ := (p.1 / r, p.2 / r ^ 2)
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hcalc : h * (p.1 / r) ^ 2 + p.2 / r ^ 2 = (h * p.1 ^ 2 + p.2) / r ^ 2 := by field_simp
  have hq : q ∈ bigon h := by
    refine ⟨div_nonneg hp.1 hr2.le, ?_⟩
    change h * (p.1 / r) ^ 2 + p.2 / r ^ 2 ≤ h
    rw [hcalc]
    exact (div_le_iff₀ hr2).mpr hp.2
  refine ⟨q, hq, ?_⟩
  apply congrArg bigonEmbedding
  apply Prod.ext
  · change r * (p.1 / r) = p.1
    field_simp
  · change r ^ 2 * (p.2 / r ^ 2) = p.2
    field_simp

private def Smale.WhitneyPairModel.verticalGraph (B : ℝ → ℝ) (t s : ℝ) : Space :=
  ((s, t * B s), 0)

private theorem
    Smale.WhitneyPairModel.exists_supported_graph_height {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : Set.MapsTo bigonEmbedding (bigon h) U) :
    ∃ B : ℝ → ℝ,
      ContDiff ℝ ∞ B ∧
        HasCompactSupport B ∧
          (∀ s, 0 ≤ B s) ∧
            (∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < B s) ∧
              ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ tsupport B, verticalGraph B t s ∈ U := by
  obtain ⟨r, hr, hscaled⟩ := exists_scaled_bigon_in_open hh hU hKU
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  let α : ContDiffBump (0 : ℝ) :=
    { rIn := 1
      rOut := r
      rIn_pos := zero_lt_one
      rIn_lt_rOut := hr }
  let B : ℝ → ℝ := fun s => α s * (h * (r ^ 2 - s ^ 2))
  have hB : ContDiff ℝ ∞ B := α.contDiff.mul (by fun_prop)
  have hcompact : HasCompactSupport B := α.hasCompactSupport.mul_right
  have hsupp : tsupport B ⊆ tsupport (α : ℝ → ℝ) := by
    apply closure_mono
    intro s hs hα
    apply hs
    change α s * (h * (r ^ 2 - s ^ 2)) = 0
    rw [hα, MulZeroClass.zero_mul]
  have hbound : ∀ s ∈ tsupport B, |s| ≤ r := by
    intro s hs
    have hx := hsupp hs
    rw [α.tsupport_eq] at hx
    change Dist.dist s 0 ≤ r at hx
    simpa only [Real.dist_eq, sub_zero] using hx
  have hheight {s : ℝ} (hs : |s| ≤ r) : 0 ≤ h * (r ^ 2 - s ^ 2) := by
    have hsq : s ^ 2 ≤ r ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg s) hrpos.le).mpr hs
    exact mul_nonneg hh.le (sub_nonneg.mpr hsq)
  have hnonneg : ∀ s, 0 ≤ B s := by
    intro s
    by_cases hs : α s = 0
    · simp only [B, hs, MulZeroClass.zero_mul, le_refl]
    have hmem : s ∈ Function.support α := hs
    rw [α.support_eq] at hmem
    have hsr : |s| ≤ r := by
      have hl : |s| < r := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hmem
      exact hl.le
    exact mul_nonneg α.nonneg (hheight hsr)
  refine ⟨B, hB, hcompact, hnonneg, ?_, ?_⟩
  · intro s hs
    have hα : α s = 1 :=
      α.one_of_mem_closedBall
        (by
          change Dist.dist s 0 ≤ 1
          simpa only [Real.dist_eq, sub_zero] using hs)
    change h * (1 - s ^ 2) < α s * (h * (r ^ 2 - s ^ 2))
    rw [hα, one_mul]
    have hgap : 0 < h * (r ^ 2 - 1) := mul_pos hh (by nlinarith [sq_nonneg (r - 1)])
    nlinarith
  · intro t ht s hs
    have hts : t * α s ≤ 1 := by
      calc
        t * α s ≤ 1 * α s := mul_le_mul_of_nonneg_right ht.2 α.nonneg
        _ ≤ 1 := by simpa only [one_mul] using (α.le_one (x := s))
    have hy : t * B s ≤ h * (r ^ 2 - s ^ 2) := by
      calc
        t * B s = (t * α s) * (h * (r ^ 2 - s ^ 2)) := by dsimp [B]; ring
        _ ≤ h * (r ^ 2 - s ^ 2) := mul_le_of_le_one_left (hheight (hbound s hs)) hts
    have hcap : 0 ≤ t * B s ∧ h * s ^ 2 + t * B s ≤ h * r ^ 2 :=
      ⟨mul_nonneg ht.1 (hnonneg s), by nlinarith⟩
    obtain ⟨q, hq, heq⟩ := enlarged_cap_parametrization (h := h) (p := (s, t * B s)) hrpos hcap
    have hmem := hscaled hq
    rw [heq] at hmem
    exact hmem

private def Smale.WhitneyPairModel.graphTrace (B : ℝ → ℝ) : Set (ℝ × Space) :=
  (fun p : ℝ × ℝ => (p.1, verticalGraph B p.1 p.2)) '' (Set.Icc (0 : ℝ) 1 ×ˢ tsupport B)

private theorem Smale.WhitneyPairModel.isCompact_graphTrace {B : ℝ → ℝ} (hB : Continuous B)
    (hcompact : HasCompactSupport B) : IsCompact (graphTrace B) := by
  apply (CompactIccSpace.isCompact_Icc.prod hcompact.isCompact).image
  unfold verticalGraph
  fun_prop

private theorem Smale.WhitneyPairModel.exists_graph_motion_cutoff {B : ℝ → ℝ} (hB : ContDiff ℝ ∞ B)
    (hcompact : HasCompactSupport B) (hnonneg : ∀ s, 0 ≤ B s) {U : Set Space} (hU : IsOpen U)
    (htrace : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ tsupport B, verticalGraph B t s ∈ U) :
    ∃ β : ℝ × Space → ℝ,
      ContDiff ℝ ∞ β ∧
        HasCompactSupport β ∧
          tsupport β ⊆ Prod.snd ⁻¹' U ∧
            (∀ p, 0 ≤ β p) ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s : ℝ, β (t, verticalGraph B t s) = B s :=
  by
  have hCU : graphTrace B ⊆ Prod.snd ⁻¹' U := by
    rintro _ ⟨p, hp, rfl⟩
    exact htrace p.1 hp.1 p.2 hp.2
  obtain ⟨η, hη, hηcompact, hηsupport, hηone, hηrange⟩ :=
    Smale.exists_compact_smooth_cutoff (isCompact_graphTrace hB.continuous hcompact)
      (hU.preimage continuous_snd) hCU
  let β : ℝ × Space → ℝ := fun p => η p * B p.2.1.1
  have hβ : ContDiff ℝ ∞ β := hη.mul (hB.comp (by fun_prop))
  have hβcompact : HasCompactSupport β := hηcompact.mul_right
  have hsupp : tsupport β ⊆ tsupport η := by
    apply closure_mono
    intro p hp hηp
    apply hp
    change η p * B p.2.1.1 = 0
    rw [hηp, MulZeroClass.zero_mul]
  refine
    ⟨β, hβ, hβcompact, hsupp.trans hηsupport, fun p => mul_nonneg (hηrange p).1 (hnonneg _), ?_⟩
  intro t ht s
  by_cases hs : B s = 0
  · change η (t, verticalGraph B t s) * B s = B s
    rw [hs, MulZeroClass.mul_zero]
  have hpoint : (t, verticalGraph B t s) ∈ graphTrace B :=
    ⟨(t, s), ⟨ht, subset_tsupport B hs⟩, rfl⟩
  have hηpoint : η (t, verticalGraph B t s) = 1 := hηone.self_of_nhdsSet _ hpoint
  change η (t, verticalGraph B t s) * B s = B s
  rw [hηpoint, one_mul]

private structure Smale.WhitneyPairModel.GraphMotionData (h : ℝ) (U : Set Space) where
  height : ℝ → ℝ
  smooth_height : ContDiff ℝ ∞ height
  compact_height : HasCompactSupport height
  nonneg_height : ∀ s, 0 ≤ height s
  above : ∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < height s
  trace_source : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s ∈ tsupport height, verticalGraph height t s ∈ U
  cutoff : ℝ × Space → ℝ
  smooth_cutoff : ContDiff ℝ ∞ cutoff
  compact_cutoff : HasCompactSupport cutoff
  support_cutoff : tsupport cutoff ⊆ Prod.snd ⁻¹' U
  nonneg_cutoff : ∀ p, 0 ≤ cutoff p
  tracking : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ s, cutoff (t, verticalGraph height t s) = height s

private theorem Smale.WhitneyPairModel.nonempty_graphMotionData {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : Set.MapsTo bigonEmbedding (bigon h) U) :
    Nonempty (GraphMotionData h U) := by
  obtain ⟨B, hB, hcompact, hnonneg, habove, htrace⟩ := exists_supported_graph_height hh hU hKU
  obtain ⟨β, hβ, hβcompact, hβsupport, hβnonneg, hβtrack⟩ :=
    exists_graph_motion_cutoff hB hcompact hnonneg hU htrace
  exact
    ⟨{  height := B
        smooth_height := hB
        compact_height := hcompact
        nonneg_height := hnonneg
        above := habove
        trace_source := htrace
        cutoff := β
        smooth_cutoff := hβ
        compact_cutoff := hβcompact
        support_cutoff := hβsupport
        nonneg_cutoff := hβnonneg
        tracking := hβtrack }⟩

private def Smale.WhitneyPairModel.verticalVector (δ : ℝ) : Space :=
  ((0, δ), 0)

private theorem Smale.WhitneyPairModel.norm_verticalVector {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖verticalVector δ‖ = δ := by
  simp [verticalVector, Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hδ, hδ]

private def Smale.WhitneyPairModel.graphStep (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (p : ℝ × Space) :
    Space :=
  p.2 + β ((i : ℝ) * δ, p.2) • (Real.smoothTransition p.1 • verticalVector δ)

private theorem Smale.WhitneyPairModel.contDiff_graphStep {β : ℝ × Space → ℝ} (hβ : ContDiff ℝ ∞ β)
    (δ : ℝ) (i : ℕ) : ContDiff ℝ ∞ (graphStep β δ i) := by
  have hθ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact
    contDiff_snd.add
      ((hβ.comp (contDiff_const.prodMk contDiff_snd)).smul
        ((hθ.comp contDiff_fst).smul contDiff_const))

private theorem
    Smale.WhitneyPairModel.graphStep_zero (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (z : Space) :
    graphStep β δ i (0, z) = z := by
  simp only [graphStep, Real.smoothTransition.zero, zero_smul, smul_zero, add_zero]

private theorem
    Smale.WhitneyPairModel.graphStep_horizontal (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ)
    (z : Space) : (graphStep β δ i (t, z)).1.1 = z.1.1 := by simp [graphStep, verticalVector]

private theorem Smale.WhitneyPairModel.graphStep_normal (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ)
    (z : Space) : (graphStep β δ i (t, z)).2 = z.2 := by simp [graphStep, verticalVector]

private theorem Smale.WhitneyPairModel.graphStep_fixed (β : ℝ × Space → ℝ) (δ : ℝ) (i : ℕ) (t : ℝ)
    {z : Space} (hz : z ∉ Prod.snd '' tsupport β) : graphStep β δ i (t, z) = z := by
  have hzero : β ((i : ℝ) * δ, z) = 0 := by
    by_contra hne
    exact hz ⟨((i : ℝ) * δ, z), subset_tsupport β hne, rfl⟩
  simp only [graphStep, hzero, zero_smul, add_zero]

private theorem
    Smale.WhitneyPairModel.exists_radius_graphStep {β : ℝ × Space → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hcompact : HasCompactSupport β) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ δ : ℝ,
          0 ≤ δ →
            δ < ε →
              ∀ i : ℕ,
                ∀ t : ℝ,
                  ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞,
                    ∀ z, d z = graphStep β δ i (t, z) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    Smale.SmallPerturbation.exists_uniform_radius_bumpTranslation hβ hcompact
  refine ⟨ε, hε, ?_⟩
  intro δ hδ hδε i t
  have hnorm : ‖Real.smoothTransition t • verticalVector δ‖ ≤ δ := by
    rw [norm_smul, norm_verticalVector hδ, Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg t)]
    exact mul_le_of_le_one_left hδ (Real.smoothTransition.le_one t)
  obtain ⟨d, hd, _⟩ :=
    hsmall ((i : ℝ) * δ) (Real.smoothTransition t • verticalVector δ) (hnorm.trans_lt hδε)
  exact ⟨d, hd⟩

private theorem Smale.WhitneyPairModel.graphStep_tracking {h : ℝ} {U : Set Space}
    (g : GraphMotionData h U) {δ : ℝ} {i : ℕ} (hi : (i : ℝ) * δ ∈ Set.Icc (0 : ℝ) 1) (s : ℝ) :
    graphStep g.cutoff δ i (1, verticalGraph g.height ((i : ℝ) * δ) s) =
      verticalGraph g.height (((i : ℝ) + 1) * δ) s := by
  rw [graphStep, g.tracking _ hi, Real.smoothTransition.one, one_smul]
  ext <;> simp [verticalGraph, verticalVector, smul_eq_mul]
  ring

private structure Smale.WhitneyPairModel.GraphMotion {h : ℝ} {U : Set Space}
    (g : GraphMotionData h U) where
  support : Set Space
  compact_support : IsCompact support
  support_subset : support ⊆ U
  family : ℝ × Space → Space
  smooth : ContDiff ℝ ∞ family
  initial : ∀ z, family (0, z) = z
  diffeomorph :
    ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞, ∀ z, d z = family (t, z)
  fixed : ∀ t z, z ∉ support → family (t, z) = z
  horizontal : ∀ t z, (family (t, z)).1.1 = z.1.1
  normal : ∀ t z, (family (t, z)).2 = z.2
  tracking : ∀ s, family (1, firstSheet (s, 0)) = verticalGraph g.height 1 s

private theorem Smale.WhitneyPairModel.GraphMotionData.nonempty_graphMotion {h : ℝ}
    {U : Set Smale.WhitneyPairModel.Space} (g : Smale.WhitneyPairModel.GraphMotionData h U) :
    Nonempty (Smale.WhitneyPairModel.GraphMotion g) := by
  obtain ⟨ε, hε, hsmall⟩ :=
    Smale.WhitneyPairModel.exists_radius_graphStep g.smooth_cutoff g.compact_cutoff
  obtain ⟨N, hN, hNsmall⟩ := Real.exists_nat_pos_inv_lt hε
  let δ : ℝ := (N : ℝ)⁻¹
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hδ : 0 ≤ δ := (inv_pos.mpr hNreal).le
  have htotal : (N : ℝ) * δ = 1 := mul_inv_cancel₀ hNreal.ne'
  let B : ℕ → ℝ × Smale.WhitneyPairModel.Space → Smale.WhitneyPairModel.Space :=
    Smale.WhitneyPairModel.graphStep g.cutoff δ
  let A : ℝ × Smale.WhitneyPairModel.Space → Smale.WhitneyPairModel.Space :=
    Smale.SmallPerturbation.composeFamily B N
  have htrack :
    ∀ j ≤ N,
      ∀ s,
        Smale.SmallPerturbation.composeFamily B j (1, Smale.WhitneyPairModel.firstSheet (s, 0)) =
          Smale.WhitneyPairModel.verticalGraph g.height ((j : ℝ) * δ) s := by
    intro j
    induction j with
    | zero =>
      intro _ s
      simp [Smale.SmallPerturbation.composeFamily, Smale.WhitneyPairModel.firstSheet,
        Smale.WhitneyPairModel.verticalGraph]
    | succ j ih =>
      intro hj s
      have hjN : j ≤ N := Nat.le_of_succ_le hj
      have htime : (j : ℝ) * δ ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨mul_nonneg (Nat.cast_nonneg j) hδ, ?_⟩
        calc
          (j : ℝ) * δ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjN) hδ
          _ = 1 := htotal
      change
        Smale.WhitneyPairModel.graphStep g.cutoff δ j
            (1,
              Smale.SmallPerturbation.composeFamily B j
                (1, Smale.WhitneyPairModel.firstSheet (s, 0))) =
          _
      rw [ih hjN s, Smale.WhitneyPairModel.graphStep_tracking g htime s, Nat.cast_add,
        Nat.cast_one]
  refine
    ⟨{  support := Prod.snd '' tsupport g.cutoff
        compact_support := g.compact_cutoff.isCompact.image continuous_snd
        support_subset := ?_
        family := A
        smooth :=
          Smale.SmallPerturbation.contDiff_composeFamily
            (fun i => Smale.WhitneyPairModel.contDiff_graphStep g.smooth_cutoff δ i) N
        initial :=
          Smale.SmallPerturbation.composeFamily_zero
            (Smale.WhitneyPairModel.graphStep_zero g.cutoff δ) N
        diffeomorph :=
          Smale.SmallPerturbation.exists_diffeomorph_composeFamily (hsmall δ hδ hNsmall) N
        fixed := fun t z hz =>
          Smale.SmallPerturbation.composeFamily_fixed
            (fun i t _ hz => Smale.WhitneyPairModel.graphStep_fixed g.cutoff δ i t hz) N t hz
        horizontal := fun t z =>
          Smale.SmallPerturbation.composeFamily_preserves (B := B) (f :=
            fun z : Smale.WhitneyPairModel.Space => z.1.1)
            (Smale.WhitneyPairModel.graphStep_horizontal g.cutoff δ) N t z
        normal := fun t z =>
          Smale.SmallPerturbation.composeFamily_preserves (B := B) (f :=
            fun z : Smale.WhitneyPairModel.Space => z.2)
            (Smale.WhitneyPairModel.graphStep_normal g.cutoff δ) N t z
        tracking := ?_ }⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact g.support_cutoff hp
  · intro s
    change
      Smale.SmallPerturbation.composeFamily B N (1, Smale.WhitneyPairModel.firstSheet (s, 0)) = _
    rw [htrack N le_rfl s, htotal]


private abbrev Smale.RankThreeWhitneyModel.Lower :=
  EuclideanSpace ℝ (Fin 1)

private abbrev Smale.RankThreeWhitneyModel.Upper :=
  EuclideanSpace ℝ (Fin 2)

private abbrev Smale.RankThreeWhitneyModel.Space :=
  (ℝ × ℝ) × (Lower × Upper)

private abbrev Smale.RankThreeWhitneyModel.LowerSheet :=
  ℝ × Lower

private abbrev Smale.RankThreeWhitneyModel.UpperSheet :=
  ℝ × Upper

private def Smale.RankThreeWhitneyModel.firstSheet (p : LowerSheet) : Space :=
  ((p.1, 0), (p.2, 0))

private def Smale.RankThreeWhitneyModel.secondSheet (h : ℝ) (p : UpperSheet) : Space :=
  ((p.1, h * (1 - p.1 ^ 2)), (0, p.2))

private theorem Smale.RankThreeWhitneyModel.contDiff_firstSheet : ContDiff ℝ ∞ firstSheet := by
  unfold firstSheet
  fun_prop

private theorem
    Smale.RankThreeWhitneyModel.contDiff_secondSheet (h : ℝ) : ContDiff ℝ ∞ (secondSheet h) :=
  by
  unfold secondSheet
  fun_prop

private def Smale.RankThreeWhitneyModel.firstSheetDerivative : LowerSheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Lower).prod 0).prod ((ContinuousLinearMap.snd ℝ ℝ Lower).prod 0)

private def Smale.RankThreeWhitneyModel.secondSheetDerivative (h s : ℝ) : UpperSheet →L[ℝ] Space :=
  ((ContinuousLinearMap.fst ℝ ℝ Upper).prod
        ((-2 * h * s) • ContinuousLinearMap.fst ℝ ℝ Upper)).prod
    ((0 : UpperSheet →L[ℝ] Lower).prod (ContinuousLinearMap.snd ℝ ℝ Upper))

private theorem Smale.RankThreeWhitneyModel.firstSheetDerivative_apply (p : LowerSheet) :
    firstSheetDerivative p = ((p.1, 0), (p.2, 0)) :=
  rfl

private theorem Smale.RankThreeWhitneyModel.secondSheetDerivative_apply (h s : ℝ) (p : UpperSheet) :
    secondSheetDerivative h s p = ((p.1, (-2 * h * s) * p.1), (0, p.2)) :=
  rfl

private theorem Smale.RankThreeWhitneyModel.hasFDerivAt_firstSheet (p : LowerSheet) :
    HasFDerivAt firstSheet firstSheetDerivative p :=
  firstSheetDerivative.hasFDerivAt

private theorem Smale.RankThreeWhitneyModel.hasFDerivAt_secondSheet (h : ℝ) (p : UpperSheet) :
    HasFDerivAt (secondSheet h) (secondSheetDerivative h p.1) p := by
  have hs := (ContinuousLinearMap.fst ℝ ℝ Upper).hasFDerivAt (x := p)
  have hu := (ContinuousLinearMap.snd ℝ ℝ Upper).hasFDerivAt (x := p)
  have ht := ((hasFDerivAt_const (1 : ℝ) p).sub (hs.pow 2)).const_mul h
  have hd := (hs.prodMk ht).prodMk ((hasFDerivAt_const (0 : Lower) p).prodMk hu)
  apply hd.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [secondSheetDerivative, ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', zero_apply, sub_apply, smul_apply, smul_eq_mul]
  congr 2
  norm_num [two_smul]
  ring

private def
    Smale.RankThreeWhitneyModel.lowerSplit : (Lower × ℝ) ≃L[ℝ] Smale.WhitneyPairModel.Plane :=
  ContinuousLinearEquiv.ofFinrankEq
    (by simp [Lower, Smale.WhitneyPairModel.Plane, Module.finrank_prod])

private def Smale.RankThreeWhitneyModel.lowerInclude : Lower →L[ℝ] Smale.WhitneyPairModel.Plane :=
  lowerSplit.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ Lower ℝ)

private def Smale.RankThreeWhitneyModel.lowerProject : Smale.WhitneyPairModel.Plane →L[ℝ] Lower :=
  (ContinuousLinearMap.fst ℝ Lower ℝ).comp lowerSplit.symm.toContinuousLinearMap

private theorem Smale.RankThreeWhitneyModel.lowerProject_include (u : Lower) :
    lowerProject (lowerInclude u) = u := by
  change (lowerSplit.symm (lowerSplit (u, 0))).1 = u
  rw [lowerSplit.symm_apply_apply]

private def Smale.RankThreeWhitneyModel.normalInclude :
    (Lower × Upper) →L[ℝ] (Smale.WhitneyPairModel.Plane × Smale.WhitneyPairModel.Plane) :=
  lowerInclude.prodMap (ContinuousLinearMap.id ℝ Upper)

private def Smale.RankThreeWhitneyModel.normalProject :
    (Smale.WhitneyPairModel.Plane × Smale.WhitneyPairModel.Plane) →L[ℝ] (Lower × Upper) :=
  lowerProject.prodMap (ContinuousLinearMap.id ℝ Upper)

private theorem Smale.RankThreeWhitneyModel.normalProject_include :
    Function.LeftInverse normalProject normalInclude := fun z =>
  Prod.ext (lowerProject_include z.1) rfl

private def Smale.RankThreeWhitneyModel.expand : Space →L[ℝ] Smale.WhitneyPairModel.Space :=
  Smale.FiberRestriction.embed normalInclude

private def Smale.RankThreeWhitneyModel.collapse : Smale.WhitneyPairModel.Space →L[ℝ] Space :=
  Smale.FiberRestriction.project normalProject

private theorem Smale.RankThreeWhitneyModel.collapse_expand (z : Space) : collapse (expand z) = z :=
  Smale.FiberRestriction.project_embed normalInclude normalProject normalProject_include z

private theorem Smale.RankThreeWhitneyModel.expand_zero (p : ℝ × ℝ) : expand (p, 0) = (p, 0) :=
  Prod.ext rfl normalInclude.map_zero

private theorem Smale.RankThreeWhitneyModel.collapse_zero (p : ℝ × ℝ) : collapse (p, 0) = (p, 0) :=
  Prod.ext rfl normalProject.map_zero

private def Smale.RankThreeWhitneyModel.verticalGraph (B : ℝ → ℝ) (t s : ℝ) : Space :=
  ((s, t * B s), 0)

private theorem Smale.RankThreeWhitneyModel.collapse_verticalGraph (B : ℝ → ℝ) (t s : ℝ) :
    collapse (Smale.WhitneyPairModel.verticalGraph B t s) = verticalGraph B t s :=
  collapse_zero _

private structure Smale.RankThreeWhitneyModel.GraphMotion (h : ℝ) (U : Set Space) where
  height : ℝ → ℝ
  nonneg_height : ∀ s, 0 ≤ height s
  above : ∀ s, |s| ≤ 1 → h * (1 - s ^ 2) < height s
  support : Set Space
  compact_support : IsCompact support
  support_subset : support ⊆ U
  family : ℝ × Space → Space
  smooth : ContDiff ℝ ∞ family
  initial : ∀ z, family (0, z) = z
  diffeomorph :
    ∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Space) 𝓘(ℝ, Space) Space Space ∞, ∀ z, d z = family (t, z)
  fixed : ∀ t z, z ∉ support → family (t, z) = z
  horizontal : ∀ t z, (family (t, z)).1.1 = z.1.1
  normal : ∀ t z, (family (t, z)).2 = z.2
  tracking : ∀ s, family (1, firstSheet (s, 0)) = verticalGraph height 1 s

private theorem
    Smale.RankThreeWhitneyModel.nonempty_graphMotion {h : ℝ} (hh : 0 < h) {U : Set Space}
    (hU : IsOpen U) (hKU : ∀ p ∈ Smale.WhitneyPairModel.bigon h, (p, (0 : Lower × Upper)) ∈ U) :
    Nonempty (GraphMotion h U) := by
  let V : Set Smale.WhitneyPairModel.Space := collapse ⁻¹' U
  have hV : IsOpen V := hU.preimage collapse.continuous
  have hKV :
    Set.MapsTo Smale.WhitneyPairModel.bigonEmbedding (Smale.WhitneyPairModel.bigon h) V := by
    intro p hp
    change collapse (p, 0) ∈ U
    rw [collapse_zero]
    exact hKU p hp
  obtain ⟨g⟩ := Smale.WhitneyPairModel.nonempty_graphMotionData hh hV hKV
  obtain ⟨a⟩ := g.nonempty_graphMotion
  let A : ℝ × Space → Space := fun p => collapse (a.family (p.1, expand p.2))
  have hA : ContDiff ℝ ∞ A :=
    collapse.contDiff.comp
      (a.smooth.comp (contDiff_fst.prodMk (expand.contDiff.comp contDiff_snd)))
  refine
    ⟨{  height := g.height
        nonneg_height := g.nonneg_height
        above := g.above
        support := collapse '' a.support
        compact_support := a.compact_support.image collapse.continuous
        support_subset := ?_
        family := A
        smooth := hA
        initial := ?_
        diffeomorph := ?_
        fixed := ?_
        horizontal := ?_
        normal := ?_
        tracking := ?_ }⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact a.support_subset hz
  · intro z
    change collapse (a.family (0, expand z)) = z
    rw [a.initial, collapse_expand]
  · intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hn : ∀ z, (d z).2 = z.2 := by
      intro z
      rw [hd]
      exact a.normal t z
    refine
      ⟨Smale.FiberRestriction.restrict normalInclude normalProject normalProject_include d hn, ?_⟩
    intro z
    change collapse (d (expand z)) = collapse (a.family (t, expand z))
    rw [hd]
  · intro t z hz
    have hz' : expand z ∉ a.support := fun hs => hz ⟨expand z, hs, collapse_expand z⟩
    change collapse (a.family (t, expand z)) = z
    rw [a.fixed t _ hz', collapse_expand]
  · intro t z
    change (a.family (t, expand z)).1.1 = z.1.1
    rw [a.horizontal]
    rfl
  · intro t z
    change normalProject (a.family (t, expand z)).2 = z.2
    rw [a.normal]
    exact normalProject_include z.2
  · intro s
    have he : expand (firstSheet (s, 0)) = Smale.WhitneyPairModel.firstSheet (s, 0) :=
      expand_zero (s, 0)
    change collapse (a.family (1, expand (firstSheet (s, 0)))) = verticalGraph g.height 1 s
    rw [he, a.tracking, collapse_verticalGraph]

private theorem Smale.RankThreeWhitneyModel.GraphMotion.firstSheet_ne_secondSheet {h : ℝ}
    {U : Set Smale.RankThreeWhitneyModel.Space} (a : Smale.RankThreeWhitneyModel.GraphMotion h U)
    (hh : 0 < h) (p : Smale.RankThreeWhitneyModel.LowerSheet)
    (q : Smale.RankThreeWhitneyModel.UpperSheet) :
    a.family (1, Smale.RankThreeWhitneyModel.firstSheet p) ≠
      Smale.RankThreeWhitneyModel.secondSheet h q := by
  intro heq
  have hst : p.1 = q.1 := by
    have he := congrArg (fun z : Smale.RankThreeWhitneyModel.Space => z.1.1) heq
    rw [a.horizontal] at he
    exact he
  have hu : p.2 = 0 := by
    have he := congrArg (fun z : Smale.RankThreeWhitneyModel.Space => z.2) heq
    rw [a.normal] at he
    exact congrArg Prod.fst he
  have hp : p = (q.1, 0) := Prod.ext hst hu
  rw [hp, a.tracking] at heq
  have ht : a.height q.1 = h * (1 - q.1 ^ 2) := by
    simpa only [Smale.RankThreeWhitneyModel.verticalGraph,
      Smale.RankThreeWhitneyModel.secondSheet, one_mul] using
      congrArg (fun z : Smale.RankThreeWhitneyModel.Space => z.1.2) heq
  have hheight : 0 ≤ h * (1 - q.1 ^ 2) := ht ▸ a.nonneg_height q.1
  have hlevel : 0 ≤ 1 - q.1 ^ 2 := nonneg_of_mul_nonneg_right hheight hh
  have habs : |q.1| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (q.1 + 1)], by nlinarith [sq_nonneg (q.1 - 1)]⟩
  exact (a.above q.1 habs).ne ht.symm

private structure
    Smale.TubularBigon.RankThreeTangentAdaptedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map) where
  base : (ℝ × ℝ) → ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] (ℝ × ℝ))
  normal :
    (ℝ × ℝ) →
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3))
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  contains : Smale.WhitneyPairModel.bigon h ⊆ domain
  smooth_base : ContDiffOn ℝ ∞ base domain
  smooth_normal : ContDiffOn ℝ ∞ normal domain
  normal_invertible : ∀ p ∈ domain, (normal p).IsInvertible
  lower_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : EuclideanSpace ℝ (Fin 1),
        Smale.FrameField.shearedBlock (base (2 * t - 1, 0)) (normal (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u)
  upper_transverse :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : EuclideanSpace ℝ (Fin 2),
        Smale.FrameField.shearedBlock (base (Smale.WhitneyPairModel.upperBoundaryArc h t))
            (normal (Smale.WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v)
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, Smale.RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      Smale.RankThreeWhitneyModel.Space M ∞
  source_contains : Smale.WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  coordinates : ∀ p, chart p = tube.chart (Smale.FrameField.shearedMap base normal p)
  target_subset : chart.target ⊆ tube.chart.target
  transition_derivative :
    ∀ p ∈ Smale.WhitneyPairModel.bigon h,
      HasFDerivAt (tube.chart.symm ∘ chart) (Smale.FrameField.shearedBlock (base p) (normal p))
        (p, 0)

private theorem Smale.TubularBigon.nonempty_rankThreeTangentAdaptedChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 3)) (E := E) S
        k.map)
    (e :
      Smale.StripNormalData (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (E := E) T
        l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeTangentAdaptedChart tube d e) := by
  obtain ⟨W, hW, hlo, O, hO, hKO, C, hC, hhi, hframe⟩ :=
    tube.exists_rankThree_adapted_frame_of_opposite_corner_signs d e hsign
  obtain ⟨Dlo, hDlo, hIDlo, hBlo⟩ :=
    d.exists_open_sheetBaseFrame_domain tube.chart
      (fun t ht => tube.lower_chart_center_mem_target d ht)
  obtain ⟨Dhi, hDhi, hIDhi, hBhi⟩ :=
    e.exists_open_sheetBaseFrame_domain tube.chart
      (fun t ht => tube.upper_chart_center_mem_target e ht)
  have htime (t y : ℝ) : Smale.WhitneyPairModel.arcTime (2 * t - 1, y) = t := by
    dsimp [Smale.WhitneyPairModel.arcTime]; ring
  have htq (t : ℝ) :
    Smale.WhitneyPairModel.arcTime (Smale.WhitneyPairModel.upperBoundaryArc h t) = t := htime t _
  have htimeK :
    Set.MapsTo Smale.WhitneyPairModel.arcTime (Smale.WhitneyPairModel.bigon h)
      (Set.Icc (0 : ℝ) 1) := by
    intro p hp
    have hpr := Smale.WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  let U := O ∩ Smale.WhitneyPairModel.arcTime ⁻¹' (Dlo ∩ Dhi)
  have hU : IsOpen U :=
    hO.inter ((hDlo.inter hDhi).preimage Smale.WhitneyPairModel.contDiff_arcTime.continuous)
  have hKU : Smale.WhitneyPairModel.bigon h ⊆ U := fun p hp =>
    ⟨hKO hp, hIDlo (htimeK hp), hIDhi (htimeK hp)⟩
  let A : (ℝ × ℝ) → ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] (ℝ × ℝ)) :=
    fun p =>
    (d.sheetBaseFrame tube.chart (Smale.WhitneyPairModel.arcTime p)).coprod
      (e.sheetBaseFrame tube.chart (Smale.WhitneyPairModel.arcTime p))
  let N :
    (ℝ × ℝ) →
      ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 2)) →L[ℝ] EuclideanSpace ℝ (Fin 3)) :=
    fun p => (W p).coprod (C p)
  have hA : ContDiffOn ℝ ∞ A U :=
    Smale.FrameField.contDiffOn_coprod
      (hBlo.comp Smale.WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.1))
      (hBhi.comp Smale.WhitneyPairModel.contDiff_arcTime.contDiffOn (fun _ hp => hp.2.2))
  have hN : ContDiffOn ℝ ∞ N U :=
    Smale.FrameField.contDiffOn_coprod hW.contDiffOn (hC.mono Set.inter_subset_left)
  have hiN : ∀ p ∈ U, (N p).IsInvertible := fun p hp =>
    Smale.FrameField.isInvertible_coprod_of_bijective _ _ (hframe p hp.1)
  have hlow :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ u : EuclideanSpace ℝ (Fin 1),
        Smale.FrameField.shearedBlock (A (2 * t - 1, 0)) (N (2 * t - 1, 0)) (0, (u, 0)) =
          d.sheetDifferential tube.chart t (0, u) := by
    intro t ht u
    have hWt : W (2 * t - 1, 0) = d.normalFrame tube.chart t := by
      have hg := (hlo t ht).eq_of_nhds
      dsimp only [Function.comp_apply] at hg
      rwa [htime] at hg
    rw [d.sheetDifferential_transverse_eq tube.chart ht (tube.lower_chart_center_mem_target d ht),
      Smale.FrameField.shearedBlock_apply]
    simp only [A, N, ContinuousLinearMap.coprod_apply, map_zero, add_zero, zero_add, htime, hWt]
  have hupp :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ v : EuclideanSpace ℝ (Fin 2),
        Smale.FrameField.shearedBlock (A (Smale.WhitneyPairModel.upperBoundaryArc h t))
            (N (Smale.WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v)) =
          e.sheetDifferential tube.chart t (0, v) := by
    intro t ht v
    rw [e.sheetDifferential_transverse_eq tube.chart ht (tube.upper_chart_center_mem_target e ht),
      Smale.FrameField.shearedBlock_apply]
    simp only [A, N, ContinuousLinearMap.coprod_apply, map_zero, zero_add, htq, hhi t ht]
  have hz :
    Smale.WhitneyPairModel.bigon h ×ˢ {(0 : EuclideanSpace ℝ (Fin 3))} ⊆ tube.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, Φ, hsource, hformula, htarget, -, hderiv⟩ :=
    Smale.FrameField.exists_sheared_tubular_chart tube.chart
      (Smale.WhitneyPairModel.isCompact_bigon tube.height_pos) hU hKU hz hA hN
      (fun p hp => hiN p (hKU hp))
  refine
    ⟨{  base := A
        normal := N
        domain := U
        open_domain := hU
        contains := hKU
        smooth_base := hA
        smooth_normal := hN
        normal_invertible := hiN
        lower_transverse := hlow
        upper_transverse := hupp
        radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := ?_
        coordinates := hformula
        target_subset := htarget
        transition_derivative := hderiv }⟩
  intro p
  rw [hformula, Smale.FrameField.shearedMap_zero, tube.zero_section]


private def Smale.WhitneyPairModel.halfTimeDerivative {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : (ℝ × A) →L[ℝ] (ℝ × A) :=
  (((1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ A)).prod (ContinuousLinearMap.snd ℝ ℝ A)

private theorem Smale.WhitneyPairModel.halfTimeDerivative_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (v : (ℝ × A)) : halfTimeDerivative v = (v.1 / 2, v.2) := by
  apply Prod.ext
  · change (1 / 2 : ℝ) * v.1 = v.1 / 2
    ring
  · rfl

private def Smale.WhitneyPairModel.sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : (ℝ × A) :=
  halfTimeDerivative p + ((1 / 2 : ℝ), 0)

private theorem Smale.WhitneyPairModel.sheetTimeCoordinates_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : sheetTimeCoordinates p = ((p.1 + 1) / 2, p.2) := by
  rw [sheetTimeCoordinates, halfTimeDerivative_apply]
  apply Prod.ext
  · change p.1 / 2 + 1 / 2 = (p.1 + 1) / 2
    ring
  · exact add_zero _

private theorem
    Smale.WhitneyPairModel.sheetTimeCoordinates_center {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (t : ℝ) : sheetTimeCoordinates (2 * t - 1, (0 : A)) = (t, 0) := by
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · dsimp
    ring
  · rfl

private theorem
    Smale.WhitneyPairModel.contDiff_sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : ContDiff ℝ ∞ (sheetTimeCoordinates (A := A)) :=
  (halfTimeDerivative (A := A)).contDiff.add contDiff_const

private theorem
    Smale.WhitneyPairModel.hasFDerivAt_sheetTimeCoordinates {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : (ℝ × A)) : HasFDerivAt sheetTimeCoordinates halfTimeDerivative p :=
  halfTimeDerivative.hasFDerivAt.add_const ((1 / 2 : ℝ), (0 : A))

private def Smale.StripNormalData.sheetTransitionDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) : Set (ℝ × A) :=
  (ContinuousLinearMap.inl ℝ (ℝ × A) B) ⁻¹' (d.chart.source ∩ d.chart ⁻¹' Ψ.target)

private theorem Smale.StripNormalData.isOpen_sheetTransitionDomain {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    IsOpen (d.sheetTransitionDomain Ψ) := by
  have hO : IsOpen (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    d.chart.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage d.chart.open_source Ψ.open_target
  exact hO.preimage (ContinuousLinearMap.inl ℝ (ℝ × A) B).continuous

private theorem Smale.StripNormalData.contDiffOn_sheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.sheetTransition Ψ) (d.sheetTransitionDomain Ψ) := by
  have hfull : ContDiffOn ℝ ∞ (Ψ.symm ∘ d.chart) (d.chart.source ∩ d.chart ⁻¹' Ψ.target) :=
    (Ψ.contMDiffOn_invFun.comp (d.chart.contMDiffOn_toFun.mono Set.inter_subset_left)
        (fun _ hp => hp.2)).contDiffOn
  exact hfull.comp (ContinuousLinearMap.inl ℝ (ℝ × A) B).contDiff.contDiffOn (fun _ hp => hp)

private def Smale.StripNormalData.retimedSheetTransition {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    (ℝ × A) → ((ℝ × ℝ) × Z) :=
  d.sheetTransition Ψ ∘ Smale.WhitneyPairModel.sheetTimeCoordinates

private def Smale.StripNormalData.retimedDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) : Set (ℝ × A) :=
  Smale.WhitneyPairModel.sheetTimeCoordinates ⁻¹' d.sheetTransitionDomain Ψ

private theorem
    Smale.StripNormalData.isOpen_retimedDomain {A B Z E M : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M} (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    IsOpen (d.retimedDomain Ψ) :=
  (d.isOpen_sheetTransitionDomain Ψ).preimage
    Smale.WhitneyPairModel.contDiff_sheetTimeCoordinates.continuous

private theorem Smale.StripNormalData.contDiffOn_retimedSheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) :
    ContDiffOn ℝ ∞ (d.retimedSheetTransition Ψ) (d.retimedDomain Ψ) :=
  (d.contDiffOn_sheetTransition Ψ).comp
    Smale.WhitneyPairModel.contDiff_sheetTimeCoordinates.contDiffOn (fun _ hp => hp)

private theorem Smale.StripNormalData.retimedDomain_contains_center {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    (2 * t - 1, (0 : A)) ∈ d.retimedDomain Ψ := by
  change Smale.WhitneyPairModel.sheetTimeCoordinates (2 * t - 1, 0) ∈ d.sheetTransitionDomain Ψ
  rw [Smale.WhitneyPairModel.sheetTimeCoordinates_center]
  exact ⟨d.line ht, htarget⟩

private theorem Smale.StripNormalData.hasFDerivAt_retimedSheetTransition {A B Z E M : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] {S : Set M} {k : (ℝ × ℝ) → M}
    (d : Smale.StripNormalData A B (E := E) S k)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, (ℝ × ℝ) × Z) 𝓘(ℝ, E) ((ℝ × ℝ) × Z) M ∞) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (htarget : d.chart (Smale.StripCoordinates.center t) ∈ Ψ.target) :
    HasFDerivAt (d.retimedSheetTransition Ψ)
      ((d.sheetDifferential Ψ t).comp Smale.WhitneyPairModel.halfTimeDerivative) (2 * t - 1, 0) :=
  by
  have hd :
    HasFDerivAt (d.sheetTransition Ψ) (d.sheetDifferential Ψ t)
      (Smale.WhitneyPairModel.sheetTimeCoordinates (2 * t - 1, 0)) := by
    rw [Smale.WhitneyPairModel.sheetTimeCoordinates_center]
    exact ((d.contDiffAt_sheetTransition Ψ ht htarget).differentiableAt (by simp)).hasFDerivAt
  exact hd.comp (2 * t - 1, (0 : A)) (Smale.WhitneyPairModel.hasFDerivAt_sheetTimeCoordinates _)

private theorem Smale.TubularBigon.RankThreeTangentAdaptedChart.lower_model_tangent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (Smale.FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))).comp
        Smale.RankThreeWhitneyModel.firstSheetDerivative =
      (d.sheetDifferential tube.chart t).comp Smale.WhitneyPairModel.halfTimeDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  have harc : d.sheetDifferential tube.chart t (v.1 / 2, 0) = ((v.1, 0), 0) := by
    rw [Smale.IntersectionCoordinates.map_first_axis _ (v.1 / 2),
      tube.lower_sheetDifferential_arc d ht]
    ext <;> simp [smul_eq_mul]
  change
    Smale.FrameField.shearedBlock _ _ (Smale.RankThreeWhitneyModel.firstSheetDerivative v) =
      d.sheetDifferential tube.chart t (Smale.WhitneyPairModel.halfTimeDerivative v)
  rw [Smale.WhitneyPairModel.halfTimeDerivative_apply]
  calc
    Smale.FrameField.shearedBlock _ _ (Smale.RankThreeWhitneyModel.firstSheetDerivative v) =
        Smale.FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))
            ((v.1, 0), 0) +
          Smale.FrameField.shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))
            (0, (v.2, 0)) := by
      rw [← map_add]
      congr 1
      simp only [Smale.RankThreeWhitneyModel.firstSheetDerivative_apply, Prod.mk_add_mk, add_zero,
        zero_add]
    _ =
        d.sheetDifferential tube.chart t (v.1 / 2, 0) +
          d.sheetDifferential tube.chart t (0, v.2) := by
      rw [Smale.FrameField.shearedBlock_horizontal, c.lower_transverse t ht, harc]
    _ = d.sheetDifferential tube.chart t (v.1 / 2, v.2) := by
      rw [← map_add]
      congr 1
      simp

private theorem Smale.TubularBigon.RankThreeTangentAdaptedChart.upper_model_tangent {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (Smale.FrameField.shearedBlock (c.base (Smale.WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (Smale.WhitneyPairModel.upperBoundaryArc h t))).comp
        (Smale.RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1)) =
      (e.sheetDifferential tube.chart t).comp Smale.WhitneyPairModel.halfTimeDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  have harc :
    e.sheetDifferential tube.chart t (v.1 / 2, 0) = ((v.1, (-2 * h * (2 * t - 1)) * v.1), 0) := by
    rw [Smale.IntersectionCoordinates.map_first_axis _ (v.1 / 2),
      tube.upper_sheetDifferential_arc e ht]
    ext <;> simp [smul_eq_mul]
    ring
  change
    Smale.FrameField.shearedBlock _ _
        (Smale.RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1) v) =
      e.sheetDifferential tube.chart t (Smale.WhitneyPairModel.halfTimeDerivative v)
  rw [Smale.WhitneyPairModel.halfTimeDerivative_apply]
  calc
    Smale.FrameField.shearedBlock _ _
          (Smale.RankThreeWhitneyModel.secondSheetDerivative h (2 * t - 1) v) =
        Smale.FrameField.shearedBlock (c.base (Smale.WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (Smale.WhitneyPairModel.upperBoundaryArc h t))
            ((v.1, (-2 * h * (2 * t - 1)) * v.1), 0) +
          Smale.FrameField.shearedBlock (c.base (Smale.WhitneyPairModel.upperBoundaryArc h t))
            (c.normal (Smale.WhitneyPairModel.upperBoundaryArc h t)) (0, (0, v.2)) := by
      rw [← map_add]
      congr 1
      simp only [Smale.RankThreeWhitneyModel.secondSheetDerivative_apply, Prod.mk_add_mk,
        add_zero, zero_add]
    _ =
        e.sheetDifferential tube.chart t (v.1 / 2, 0) +
          e.sheetDifferential tube.chart t (0, v.2) := by
      rw [Smale.FrameField.shearedBlock_horizontal, c.upper_transverse t ht, harc]
    _ = e.sheetDifferential tube.chart t (v.1 / 2, v.2) := by
      rw [← map_add]
      congr 1
      simp

private def
    Smale.SheetCorrection.centerProjection {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] :
    (ℝ × A) →L[ℝ] (ℝ × A) :=
  (ContinuousLinearMap.fst ℝ ℝ A).prod (0 : (ℝ × A) →L[ℝ] A)

private theorem Smale.SheetCorrection.centerProjection_apply {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (p : ℝ × A) : centerProjection p = (p.1, 0) :=
  rfl

private def Smale.SheetCorrection.centeredCorrection {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] (R G : (ℝ × A) → F) (p : ℝ × A) : F :=
  (R p - G p) - (R (centerProjection p) - G (centerProjection p))

private theorem Smale.SheetCorrection.centeredCorrection_zero {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] (R G : (ℝ × A) → F) (s : ℝ) :
    centeredCorrection R G (s, 0) = 0 := by
  simp only [centeredCorrection, centerProjection_apply, sub_self]

private theorem Smale.SheetCorrection.centeredCorrection_eq_sub {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] {R G : (ℝ × A) → F} {p : ℝ × A}
    (hcenter : R (p.1, 0) = G (p.1, 0)) : centeredCorrection R G p = R p - G p := by
  simp only [centeredCorrection, centerProjection_apply, hcenter, sub_self, sub_zero]

private theorem
    Smale.SheetCorrection.contDiffOn_centeredCorrection {A F : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F] {R G : (ℝ × A) → F}
    {D : Set (ℝ × A)} (hR : ContDiffOn ℝ ∞ R D) (hG : ContDiffOn ℝ ∞ G D) :
    ContDiffOn ℝ ∞ (centeredCorrection R G) (D ∩ centerProjection ⁻¹' D) :=
  ((hR.sub hG).mono Set.inter_subset_left).sub
    ((hR.sub hG).comp (centerProjection (A := A)).contDiff.contDiffOn (fun _ hp => hp.2))

private theorem Smale.SheetCorrection.hasFDerivAt_centeredCorrection_zero {A F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {R G : (ℝ × A) → F} {L : (ℝ × A) →L[ℝ] F} {s : ℝ} (hR : HasFDerivAt R L (s, 0))
    (hG : HasFDerivAt G L (s, 0)) :
    HasFDerivAt (centeredCorrection R G) (0 : (ℝ × A) →L[ℝ] F) (s, 0) := by
  have hdiff : HasFDerivAt (fun p => R p - G p) (0 : (ℝ × A) →L[ℝ] F) (s, (0 : A)) := by
    convert hR.sub hG using 1 <;>
      first
      | rfl
      | simp only [sub_self]
  have hcenter := hdiff.comp (s, (0 : A)) (centerProjection (A := A)).hasFDerivAt
  convert hdiff.sub hcenter using 1 <;>
    first
    | rfl
    | simp only [ContinuousLinearMap.zero_comp, sub_self]

private def Smale.RankThreeWhitneyModel.lowerSheetCoordinates : Space →L[ℝ] LowerSheet :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Lower × Upper))).prod
    ((ContinuousLinearMap.fst ℝ Lower Upper).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Lower × Upper)))

private def Smale.RankThreeWhitneyModel.upperSheetCoordinates : Space →L[ℝ] UpperSheet :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) (Lower × Upper))).prod
    ((ContinuousLinearMap.snd ℝ Lower Upper).comp
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Lower × Upper)))

private def Smale.RankThreeWhitneyModel.correctedSheetMap {F : Type*} [NormedAddCommGroup F]
    (G : Space → F) (Rlo : LowerSheet → F) (Rhi : UpperSheet → F) (h : ℝ) (p : Space) : F :=
  G p + Smale.SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) (lowerSheetCoordinates p) +
    Smale.SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) (upperSheetCoordinates p)

private theorem
    Smale.RankThreeWhitneyModel.correctedSheetMap_zero {F : Type*} [NormedAddCommGroup F]
    (G : Space → F) (Rlo : LowerSheet → F) (Rhi : UpperSheet → F) (h : ℝ) (p : ℝ × ℝ) :
    correctedSheetMap G Rlo Rhi h (p, 0) = G (p, 0) := by
  change
    G (p, 0) + Smale.SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) (p.1, 0) +
        Smale.SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) (p.1, 0) =
      G (p, 0)
  rw [Smale.SheetCorrection.centeredCorrection_zero,
    Smale.SheetCorrection.centeredCorrection_zero, add_zero, add_zero]

private theorem
    Smale.RankThreeWhitneyModel.correctedSheetMap_lower {F : Type*} [NormedAddCommGroup F]
    {G : Space → F} {Rlo : LowerSheet → F} {Rhi : UpperSheet → F} {h : ℝ} (q : LowerSheet)
    (hcenter : Rlo (q.1, 0) = G (firstSheet (q.1, 0))) :
    correctedSheetMap G Rlo Rhi h (firstSheet q) = Rlo q := by
  have hlo : lowerSheetCoordinates (firstSheet q) = q := rfl
  have hhi : upperSheetCoordinates (firstSheet q) = (q.1, 0) := rfl
  rw [correctedSheetMap, hlo, hhi, Smale.SheetCorrection.centeredCorrection_zero, add_zero,
    Smale.SheetCorrection.centeredCorrection_eq_sub hcenter]
  dsimp only [Function.comp_apply]
  abel

private theorem
    Smale.RankThreeWhitneyModel.correctedSheetMap_upper {F : Type*} [NormedAddCommGroup F]
    {G : Space → F} {Rlo : LowerSheet → F} {Rhi : UpperSheet → F} {h : ℝ} (q : UpperSheet)
    (hcenter : Rhi (q.1, 0) = G (secondSheet h (q.1, 0))) :
    correctedSheetMap G Rlo Rhi h (secondSheet h q) = Rhi q := by
  have hlo : lowerSheetCoordinates (secondSheet h q) = (q.1, 0) := rfl
  have hhi : upperSheetCoordinates (secondSheet h q) = q := rfl
  rw [correctedSheetMap, hlo, hhi, Smale.SheetCorrection.centeredCorrection_zero, add_zero,
    Smale.SheetCorrection.centeredCorrection_eq_sub hcenter]
  dsimp only [Function.comp_apply]
  abel

private def Smale.RankThreeWhitneyModel.correctionDomain (U : Set Space) (Dlo : Set LowerSheet)
    (Dhi : Set UpperSheet) : Set Space :=
  U ∩
    (lowerSheetCoordinates ⁻¹' (Dlo ∩ Smale.SheetCorrection.centerProjection ⁻¹' Dlo) ∩
      upperSheetCoordinates ⁻¹' (Dhi ∩ Smale.SheetCorrection.centerProjection ⁻¹' Dhi))

private theorem
    Smale.RankThreeWhitneyModel.isOpen_correctionDomain {U : Set Space} {Dlo : Set LowerSheet}
    {Dhi : Set UpperSheet} (hU : IsOpen U) (hDlo : IsOpen Dlo) (hDhi : IsOpen Dhi) :
    IsOpen (correctionDomain U Dlo Dhi) :=
  hU.inter
    (((hDlo.inter (hDlo.preimage Smale.SheetCorrection.centerProjection.continuous)).preimage
          lowerSheetCoordinates.continuous).inter
      ((hDhi.inter (hDhi.preimage Smale.SheetCorrection.centerProjection.continuous)).preimage
        upperSheetCoordinates.continuous))

private theorem Smale.RankThreeWhitneyModel.contDiffOn_correctedSheetMap {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Space → F} {Rlo : LowerSheet → F}
    {Rhi : UpperSheet → F} {h : ℝ} {U : Set Space} {Dlo : Set LowerSheet} {Dhi : Set UpperSheet}
    (hG : ContDiffOn ℝ ∞ G U) (hRlo : ContDiffOn ℝ ∞ Rlo Dlo)
    (hGlo : ContDiffOn ℝ ∞ (G ∘ firstSheet) Dlo) (hRhi : ContDiffOn ℝ ∞ Rhi Dhi)
    (hGhi : ContDiffOn ℝ ∞ (G ∘ secondSheet h) Dhi) :
    ContDiffOn ℝ ∞ (correctedSheetMap G Rlo Rhi h) (correctionDomain U Dlo Dhi) :=
  ((hG.mono Set.inter_subset_left).add
        ((Smale.SheetCorrection.contDiffOn_centeredCorrection hRlo hGlo).comp
          lowerSheetCoordinates.contDiff.contDiffOn (fun _ hp => hp.2.1))).add
    ((Smale.SheetCorrection.contDiffOn_centeredCorrection hRhi hGhi).comp
      upperSheetCoordinates.contDiff.contDiffOn (fun _ hp => hp.2.2))

private theorem Smale.RankThreeWhitneyModel.hasFDerivAt_correctedSheetMap_zero {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Space → F} {Rlo : LowerSheet → F}
    {Rhi : UpperSheet → F} {h : ℝ} {p : ℝ × ℝ} {L : Space →L[ℝ] F} {Llo : LowerSheet →L[ℝ] F}
    {Lhi : UpperSheet →L[ℝ] F} (hG : HasFDerivAt G L (p, 0)) (hRlo : HasFDerivAt Rlo Llo (p.1, 0))
    (hGlo : HasFDerivAt (G ∘ firstSheet) Llo (p.1, 0)) (hRhi : HasFDerivAt Rhi Lhi (p.1, 0))
    (hGhi : HasFDerivAt (G ∘ secondSheet h) Lhi (p.1, 0)) :
    HasFDerivAt (correctedSheetMap G Rlo Rhi h) L (p, 0) := by
  have hlo :
    HasFDerivAt
      (Smale.SheetCorrection.centeredCorrection Rlo (G ∘ firstSheet) ∘ lowerSheetCoordinates)
      (0 : Space →L[ℝ] F) (p, 0) := by
    simpa only [ContinuousLinearMap.zero_comp] using
      (Smale.SheetCorrection.hasFDerivAt_centeredCorrection_zero hRlo hGlo).comp
        (p, (0 : Lower × Upper)) lowerSheetCoordinates.hasFDerivAt
  have hhi :
    HasFDerivAt
      (Smale.SheetCorrection.centeredCorrection Rhi (G ∘ secondSheet h) ∘ upperSheetCoordinates)
      (0 : Space →L[ℝ] F) (p, 0) := by
    simpa only [ContinuousLinearMap.zero_comp] using
      (Smale.SheetCorrection.hasFDerivAt_centeredCorrection_zero hRhi hGhi).comp
        (p, (0 : Lower × Upper)) upperSheetCoordinates.hasFDerivAt
  convert (hG.add hlo).add hhi using 1 <;>
    first
    | rfl
    | simp only [add_zero]

private def Smale.TubularBigon.RankThreeTangentAdaptedChart.shearedCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Smale.RankThreeWhitneyModel.Space → ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  Smale.FrameField.shearedMap c.base c.normal

private def Smale.TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Smale.RankThreeWhitneyModel.Space → ((ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) :=
  Smale.RankThreeWhitneyModel.correctedSheetMap c.shearedCoordinates
    (d.retimedSheetTransition tube.chart) (e.retimedSheetTransition tube.chart) h

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_zero {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) (p : ℝ × ℝ) :
    c.correctedCoordinates (p, 0) = (p, 0) := by
  rw [correctedCoordinates, Smale.RankThreeWhitneyModel.correctedSheetMap_zero]
  exact Smale.FrameField.shearedMap_zero c.base c.normal p

private theorem Smale.TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_shearedCoordinates_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ Smale.WhitneyPairModel.bigon h) :
    HasFDerivAt c.shearedCoordinates (Smale.FrameField.shearedBlock (c.base p) (c.normal p))
      (p, 0) :=
  Smale.FrameField.hasFDerivAt_shearedMap_zero
    ((c.smooth_base.contDiffAt (c.open_domain.mem_nhds (c.contains hp))).differentiableAt
      (by simp))
    ((c.smooth_normal.contDiffAt (c.open_domain.mem_nhds (c.contains hp))).differentiableAt
      (by simp))

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_sheared_lower {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasFDerivAt (c.shearedCoordinates ∘ Smale.RankThreeWhitneyModel.firstSheet)
      ((d.sheetDifferential tube.chart t).comp Smale.WhitneyPairModel.halfTimeDerivative)
      (2 * t - 1, 0) := by
  have hd :=
    (c.hasFDerivAt_shearedCoordinates_zero (tube.lowerBoundaryArc_mem_bigon ht)).comp
      (2 * t - 1, (0 : Smale.RankThreeWhitneyModel.Lower))
      (Smale.RankThreeWhitneyModel.hasFDerivAt_firstSheet (2 * t - 1, 0))
  rwa [Smale.WhitneyPairModel.lowerBoundaryArc, c.lower_model_tangent ht] at hd

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_sheared_upper {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasFDerivAt (c.shearedCoordinates ∘ Smale.RankThreeWhitneyModel.secondSheet h)
      ((e.sheetDifferential tube.chart t).comp Smale.WhitneyPairModel.halfTimeDerivative)
      (2 * t - 1, 0) := by
  have hd :=
    (c.hasFDerivAt_shearedCoordinates_zero (tube.upperBoundaryArc_mem_bigon ht)).comp
      (2 * t - 1, (0 : Smale.RankThreeWhitneyModel.Upper))
      (Smale.RankThreeWhitneyModel.hasFDerivAt_secondSheet h (2 * t - 1, 0))
  rwa [c.upper_model_tangent ht] at hd

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.hasFDerivAt_correctedCoordinates_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ Smale.WhitneyPairModel.bigon h) :
    HasFDerivAt c.correctedCoordinates (Smale.FrameField.shearedBlock (c.base p) (c.normal p))
      (p, 0) := by
  have hpr := Smale.WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
  have ht : Smale.WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have htime : 2 * Smale.WhitneyPairModel.arcTime p - 1 = p.1 := by
    dsimp [Smale.WhitneyPairModel.arcTime]; ring
  have hRlo :=
    d.hasFDerivAt_retimedSheetTransition tube.chart ht (tube.lower_chart_center_mem_target d ht)
  have hRhi :=
    e.hasFDerivAt_retimedSheetTransition tube.chart ht (tube.upper_chart_center_mem_target e ht)
  have hGlo := c.hasFDerivAt_sheared_lower ht
  have hGhi := c.hasFDerivAt_sheared_upper ht
  rw [htime] at hRlo hRhi hGlo hGhi
  exact
    Smale.RankThreeWhitneyModel.hasFDerivAt_correctedSheetMap_zero
      (c.hasFDerivAt_shearedCoordinates_zero hp) hRlo hGlo hRhi hGhi

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.retimed_lower_center_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.retimedSheetTransition tube.chart (s, 0)) =ᶠ[𝓝 (2 * t - 1)]
      (fun s => c.shearedCoordinates (Smale.RankThreeWhitneyModel.firstSheet (s, 0))) := by
  have hct : ContinuousAt (fun s : ℝ => (s + 1) / 2) (2 * t - 1) := by fun_prop
  have heq : (2 * t - 1 + 1) / 2 = t := by ring
  have htime : Filter.Tendsto (fun s : ℝ => (s + 1) / 2) (𝓝 (2 * t - 1)) (𝓝 t) := by
    simpa only [heq] using hct.tendsto
  filter_upwards [(tube.lower_sheetTransition_center_germ d ht).comp_tendsto htime] with s hs
  change
    d.sheetTransition tube.chart (Smale.WhitneyPairModel.sheetTimeCoordinates (s, 0)) =
      Smale.FrameField.shearedMap c.base c.normal ((s, 0), 0)
  rw [Smale.WhitneyPairModel.sheetTimeCoordinates_apply, Smale.FrameField.shearedMap_zero]
  dsimp only [Function.comp_apply] at hs
  rw [hs]
  have hlin : 2 * ((s + 1) / 2) - 1 = s := by ring
  simp only [Smale.WhitneyPairModel.lowerBoundaryArc, hlin]

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.retimed_upper_center_germ {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (fun s : ℝ => e.retimedSheetTransition tube.chart (s, 0)) =ᶠ[𝓝 (2 * t - 1)]
      (fun s => c.shearedCoordinates (Smale.RankThreeWhitneyModel.secondSheet h (s, 0))) := by
  have hct : ContinuousAt (fun s : ℝ => (s + 1) / 2) (2 * t - 1) := by fun_prop
  have heq : (2 * t - 1 + 1) / 2 = t := by ring
  have htime : Filter.Tendsto (fun s : ℝ => (s + 1) / 2) (𝓝 (2 * t - 1)) (𝓝 t) := by
    simpa only [heq] using hct.tendsto
  filter_upwards [(tube.upper_sheetTransition_center_germ e ht).comp_tendsto htime] with s hs
  change
    e.sheetTransition tube.chart (Smale.WhitneyPairModel.sheetTimeCoordinates (s, 0)) =
      Smale.FrameField.shearedMap c.base c.normal ((s, h * (1 - s ^ 2)), 0)
  rw [Smale.WhitneyPairModel.sheetTimeCoordinates_apply, Smale.FrameField.shearedMap_zero]
  dsimp only [Function.comp_apply] at hs
  rw [hs]
  have hlin : 2 * ((s + 1) / 2) - 1 = s := by ring
  simp only [Smale.WhitneyPairModel.upperBoundaryArc, hlin]

private def Smale.TubularBigon.RankThreeTangentAdaptedChart.shearedDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set Smale.RankThreeWhitneyModel.Space :=
  Prod.fst ⁻¹' c.domain

private def Smale.TubularBigon.RankThreeTangentAdaptedChart.lowerCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set Smale.RankThreeWhitneyModel.LowerSheet :=
  d.retimedDomain tube.chart ∩ Smale.RankThreeWhitneyModel.firstSheet ⁻¹' c.shearedDomain

private def Smale.TubularBigon.RankThreeTangentAdaptedChart.upperCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set Smale.RankThreeWhitneyModel.UpperSheet :=
  e.retimedDomain tube.chart ∩ Smale.RankThreeWhitneyModel.secondSheet h ⁻¹' c.shearedDomain

private def Smale.TubularBigon.RankThreeTangentAdaptedChart.centerMatchingTimes {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) : Set ℝ :=
  interior
    {s |
      d.retimedSheetTransition tube.chart (s, 0) =
          c.shearedCoordinates (Smale.RankThreeWhitneyModel.firstSheet (s, 0)) ∧
        e.retimedSheetTransition tube.chart (s, 0) =
          c.shearedCoordinates (Smale.RankThreeWhitneyModel.secondSheet h (s, 0))}

private def Smale.TubularBigon.RankThreeTangentAdaptedChart.nonlinearDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Set Smale.RankThreeWhitneyModel.Space :=
  Smale.RankThreeWhitneyModel.correctionDomain c.shearedDomain c.lowerCorrectionDomain
      c.upperCorrectionDomain ∩
    (fun p : Smale.RankThreeWhitneyModel.Space => p.1.1) ⁻¹' c.centerMatchingTimes

private theorem Smale.TubularBigon.RankThreeTangentAdaptedChart.isOpen_shearedDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) : IsOpen c.shearedDomain :=
  c.open_domain.preimage continuous_fst

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.isOpen_lowerCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    IsOpen c.lowerCorrectionDomain :=
  (d.isOpen_retimedDomain tube.chart).inter
    (c.isOpen_shearedDomain.preimage Smale.RankThreeWhitneyModel.contDiff_firstSheet.continuous)

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.isOpen_upperCorrectionDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    IsOpen c.upperCorrectionDomain :=
  (e.isOpen_retimedDomain tube.chart).inter
    (c.isOpen_shearedDomain.preimage
      (Smale.RankThreeWhitneyModel.contDiff_secondSheet h).continuous)

private theorem Smale.TubularBigon.RankThreeTangentAdaptedChart.isOpen_nonlinearDomain {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) : IsOpen c.nonlinearDomain :=
  (Smale.RankThreeWhitneyModel.isOpen_correctionDomain c.isOpen_shearedDomain
        c.isOpen_lowerCorrectionDomain c.isOpen_upperCorrectionDomain).inter
    (isOpen_interior.preimage (by fun_prop))

private theorem Smale.TubularBigon.RankThreeTangentAdaptedChart.contDiffOn_correctedCoordinates
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    ContDiffOn ℝ ∞ c.correctedCoordinates c.nonlinearDomain := by
  have hG : ContDiffOn ℝ ∞ c.shearedCoordinates c.shearedDomain :=
    Smale.FrameField.contDiffOn_shearedMap c.smooth_base c.smooth_normal
  exact
    (Smale.RankThreeWhitneyModel.contDiffOn_correctedSheetMap hG
          ((d.contDiffOn_retimedSheetTransition tube.chart).mono Set.inter_subset_left)
          (hG.comp Smale.RankThreeWhitneyModel.contDiff_firstSheet.contDiffOn (fun _ hp => hp.2))
          ((e.contDiffOn_retimedSheetTransition tube.chart).mono Set.inter_subset_left)
          (hG.comp (Smale.RankThreeWhitneyModel.contDiff_secondSheet h).contDiffOn
            (fun _ hp => hp.2))).mono
      Set.inter_subset_left

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.centerMatchingTimes_contains {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : 2 * t - 1 ∈ c.centerMatchingTimes :=
  mem_interior_iff_mem_nhds.mpr
    ((c.retimed_lower_center_germ ht).and (c.retimed_upper_center_germ ht))

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.lowerCorrectionDomain_contains_center
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (2 * t - 1, (0 : Smale.RankThreeWhitneyModel.Lower)) ∈ c.lowerCorrectionDomain := by
  refine
    ⟨d.retimedDomain_contains_center tube.chart ht (tube.lower_chart_center_mem_target d ht), ?_⟩
  exact c.contains (tube.lowerBoundaryArc_mem_bigon ht)

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.upperCorrectionDomain_contains_center
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (2 * t - 1, (0 : Smale.RankThreeWhitneyModel.Upper)) ∈ c.upperCorrectionDomain := by
  refine
    ⟨e.retimedDomain_contains_center tube.chart ht (tube.upper_chart_center_mem_target e ht), ?_⟩
  exact c.contains (tube.upperBoundaryArc_mem_bigon ht)

private theorem Smale.TubularBigon.RankThreeTangentAdaptedChart.nonlinearDomain_contains_zero
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) {p : ℝ × ℝ}
    (hp : p ∈ Smale.WhitneyPairModel.bigon h) :
    (p, (0 : Smale.RankThreeWhitneyModel.Lower × Smale.RankThreeWhitneyModel.Upper)) ∈
      c.nonlinearDomain := by
  have hpr := Smale.WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
  have ht : Smale.WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
    change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
    constructor <;> linarith [hpr.1.1, hpr.1.2]
  have htime : 2 * Smale.WhitneyPairModel.arcTime p - 1 = p.1 := by
    dsimp [Smale.WhitneyPairModel.arcTime]; ring
  have hlo := c.lowerCorrectionDomain_contains_center ht
  have hhi := c.upperCorrectionDomain_contains_center ht
  have hmatch := c.centerMatchingTimes_contains ht
  rw [htime] at hlo hhi hmatch
  exact ⟨⟨c.contains hp, ⟨hlo, hlo⟩, ⟨hhi, hhi⟩⟩, hmatch⟩

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.lower_native_parameters {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : Smale.RankThreeWhitneyModel.LowerSheet}
    (hq : Smale.RankThreeWhitneyModel.firstSheet q ∈ c.nonlinearDomain) :
    (Smale.WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
        d.chart.source ∧
      d.chart (Smale.WhitneyPairModel.sheetTimeCoordinates q, 0) ∈ tube.chart.target :=
  hq.1.2.1.1.1

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.upper_native_parameters {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : Smale.RankThreeWhitneyModel.UpperSheet}
    (hq : Smale.RankThreeWhitneyModel.secondSheet h q ∈ c.nonlinearDomain) :
    (Smale.WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 2))) ∈
        e.chart.source ∧
      e.chart (Smale.WhitneyPairModel.sheetTimeCoordinates q, 0) ∈ tube.chart.target :=
  hq.1.2.2.1.1

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_lower_of_mem_domain
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : Smale.RankThreeWhitneyModel.LowerSheet}
    (hq : Smale.RankThreeWhitneyModel.firstSheet q ∈ c.nonlinearDomain) :
    c.correctedCoordinates (Smale.RankThreeWhitneyModel.firstSheet q) =
      d.retimedSheetTransition tube.chart q := by
  have hJ : q.1 ∈ c.centerMatchingTimes := hq.2
  have hm :=
    (show
        c.centerMatchingTimes ⊆
          {s : ℝ |
            d.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (Smale.RankThreeWhitneyModel.firstSheet (s, 0)) ∧
              e.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (Smale.RankThreeWhitneyModel.secondSheet h (s, 0))}
        from interior_subset)
      hJ
  exact Smale.RankThreeWhitneyModel.correctedSheetMap_lower q hm.1

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.correctedCoordinates_upper_of_mem_domain
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e)
    {q : Smale.RankThreeWhitneyModel.UpperSheet}
    (hq : Smale.RankThreeWhitneyModel.secondSheet h q ∈ c.nonlinearDomain) :
    c.correctedCoordinates (Smale.RankThreeWhitneyModel.secondSheet h q) =
      e.retimedSheetTransition tube.chart q := by
  have hJ : q.1 ∈ c.centerMatchingTimes := hq.2
  have hm :=
    (show
        c.centerMatchingTimes ⊆
          {s : ℝ |
            d.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (Smale.RankThreeWhitneyModel.firstSheet (s, 0)) ∧
              e.retimedSheetTransition tube.chart (s, 0) =
                c.shearedCoordinates (Smale.RankThreeWhitneyModel.secondSheet h (s, 0))}
        from interior_subset)
      hJ
  exact Smale.RankThreeWhitneyModel.correctedSheetMap_upper q hm.2

private structure
    Smale.TubularBigon.RankThreeSheetParametrizedChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, Smale.RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      Smale.RankThreeWhitneyModel.Space M ∞
  source_contains : Smale.WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  lower_source :
    ∀ q : Smale.RankThreeWhitneyModel.LowerSheet,
      Smale.RankThreeWhitneyModel.firstSheet q ∈ chart.source →
        (Smale.WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 3))) ∈
          d.chart.source
  upper_source :
    ∀ q : Smale.RankThreeWhitneyModel.UpperSheet,
      Smale.RankThreeWhitneyModel.secondSheet h q ∈ chart.source →
        (Smale.WhitneyPairModel.sheetTimeCoordinates q, (0 : EuclideanSpace ℝ (Fin 2))) ∈
          e.chart.source
  lower :
    ∀ q : Smale.RankThreeWhitneyModel.LowerSheet,
      Smale.RankThreeWhitneyModel.firstSheet q ∈ chart.source →
        chart (Smale.RankThreeWhitneyModel.firstSheet q) =
          d.chart (Smale.WhitneyPairModel.sheetTimeCoordinates q, 0)
  upper :
    ∀ q : Smale.RankThreeWhitneyModel.UpperSheet,
      Smale.RankThreeWhitneyModel.secondSheet h q ∈ chart.source →
        chart (Smale.RankThreeWhitneyModel.secondSheet h q) =
          e.chart (Smale.WhitneyPairModel.sheetTimeCoordinates q, 0)

private theorem
    Smale.TubularBigon.RankThreeTangentAdaptedChart.nonempty_rankThreeSheetParametrizedChart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeTangentAdaptedChart tube d e) :
    Nonempty (Smale.TubularBigon.RankThreeSheetParametrizedChart tube d e) := by
  have hinj :
    Set.InjOn c.correctedCoordinates
      (Smale.WhitneyPairModel.bigon h ×ˢ
        {(0 : Smale.RankThreeWhitneyModel.Lower × Smale.RankThreeWhitneyModel.Upper)}) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩ ⟨q, w⟩ ⟨hq, hw⟩ heq
    have hz0 : z = 0 := hz
    have hw0 : w = 0 := hw
    subst z
    subst w
    rw [c.correctedCoordinates_zero, c.correctedCoordinates_zero] at heq
    exact Prod.ext (congrArg (fun v : (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3) => v.1) heq) rfl
  have hlocal :
    ∀
      p ∈
        Smale.WhitneyPairModel.bigon h ×ˢ
          {(0 : Smale.RankThreeWhitneyModel.Lower × Smale.RankThreeWhitneyModel.Upper)},
      IsLocalDiffeomorphAt 𝓘(ℝ, Smale.RankThreeWhitneyModel.Space)
        𝓘(ℝ, (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) ∞ c.correctedCoordinates p := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    apply
      Smale.isLocalDiffeomorphAt_of_contMDiffOn (D := Smale.RankThreeWhitneyModel.Space) (E :=
        (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3)) (M := (ℝ × ℝ) × EuclideanSpace ℝ (Fin 3))
        c.isOpen_nonlinearDomain (c.nonlinearDomain_contains_zero hp)
        c.contDiffOn_correctedCoordinates.contMDiffOn
    rw [mfderiv_eq_fderiv, (c.hasFDerivAt_correctedCoordinates_zero hp).fderiv]
    exact
      Smale.FrameField.isInvertible_shearedBlock (c.base p) (c.normal p)
        (c.normal_invertible p (c.contains hp))
  have hzeroDomain :
    Smale.WhitneyPairModel.bigon h ×ˢ
        {(0 : Smale.RankThreeWhitneyModel.Lower × Smale.RankThreeWhitneyModel.Upper)} ⊆
      c.nonlinearDomain := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.nonlinearDomain_contains_zero hp
  obtain ⟨χ, hzeroχ, hχD, hχ⟩ :=
    Smale.exists_partialDiffeomorph_near_compact
      ((Smale.WhitneyPairModel.isCompact_bigon tube.height_pos).prod isCompact_singleton) hinj
      hlocal c.isOpen_nonlinearDomain hzeroDomain
  let Φ := χ.trans tube.chart
  have hzeroΦ :
    Smale.WhitneyPairModel.bigon h ×ˢ
        {(0 : Smale.RankThreeWhitneyModel.Lower × Smale.RankThreeWhitneyModel.Upper)} ⊆
      Φ.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    refine ⟨hzeroχ ⟨hp, rfl⟩, ?_⟩
    change χ (p, 0) ∈ tube.chart.source
    rw [hχ, c.correctedCoordinates_zero]
    exact tube.source_contains ⟨hp, Metric.mem_closedBall_self tube.radius_pos.le⟩
  obtain ⟨ε, hε, hsource⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset
      (Smale.WhitneyPairModel.isCompact_bigon tube.height_pos) Φ.open_source hzeroΦ
  have hformula (p : Smale.RankThreeWhitneyModel.Space) :
    Φ p = tube.chart (c.correctedCoordinates p) := by
    change tube.chart (χ p) = tube.chart (c.correctedCoordinates p)
    rw [hχ]
  refine
    ⟨{  radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := ?_
        target_subset := fun _ hy => hy.1
        lower_source := fun q hq => (c.lower_native_parameters (hχD hq.1)).1
        upper_source := fun q hq => (c.upper_native_parameters (hχD hq.1)).1
        lower := ?_
        upper := ?_ }⟩
  · intro p
    rw [hformula, c.correctedCoordinates_zero, tube.zero_section]
  · intro q hq
    rw [hformula, c.correctedCoordinates_lower_of_mem_domain (hχD hq.1)]
    exact tube.chart.right_inv' (c.lower_native_parameters (hχD hq.1)).2
  · intro q hq
    rw [hformula, c.correctedCoordinates_upper_of_mem_domain (hχD hq.1)]
    exact tube.chart.right_inv' (c.upper_native_parameters (hχD hq.1)).2

private theorem Smale.TubularBigon.nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeSheetParametrizedChart tube d e) := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeTangentAdaptedChart_of_opposite_corner_signs d e hsign
  exact c.nonempty_rankThreeSheetParametrizedChart

private theorem Smale.TubularBigon.RankThreeSheetParametrizedChart.lower_mem_sheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : Smale.RankThreeWhitneyModel.LowerSheet}
    (hq : Smale.RankThreeWhitneyModel.firstSheet q ∈ c.chart.source) :
    c.chart (Smale.RankThreeWhitneyModel.firstSheet q) ∈ S := by
  rw [c.lower q hq]
  exact (d.sheet _ (c.lower_source q hq)).mpr rfl

private theorem Smale.TubularBigon.RankThreeSheetParametrizedChart.upper_mem_sheet {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : Smale.RankThreeWhitneyModel.UpperSheet}
    (hq : Smale.RankThreeWhitneyModel.secondSheet h q ∈ c.chart.source) :
    c.chart (Smale.RankThreeWhitneyModel.secondSheet h q) ∈ T := by
  rw [c.upper q hq]
  exact (e.sheet _ (c.upper_source q hq)).mpr rfl

private theorem
    Smale.SheetRecognition.eventually_mem_sheet_iff {W D B E M : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞)
    (ψ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞) {S : Set M}
    (hsheet : ∀ q ∈ ψ.source, ψ q ∈ S ↔ q.2 = 0) {ι : D → W} (hι : Continuous ι) {σ τ : D → D}
    (hτ : Continuous τ) (hτσ : Function.LeftInverse τ σ) (hστ : Function.RightInverse τ σ)
    (hparam : ∀ q : D, ι q ∈ Φ.source → (σ q, (0 : B)) ∈ ψ.source ∧ Φ (ι q) = ψ (σ q, 0)) {q₀ : D}
    (hq₀ : ι q₀ ∈ Φ.source) : ∀ᶠ z in 𝓝 (ι q₀), z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ Set.range ι) := by
  let recover : W → W := fun z => ι (τ ((ψ.symm (Φ z)).1))
  have htarget : Φ (ι q₀) ∈ ψ.target := by
    rw [(hparam q₀ hq₀).2]
    exact ψ.map_source' (hparam q₀ hq₀).1
  have hΦ : ContinuousAt Φ (ι q₀) :=
    (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds hq₀)).continuousAt
  have hψ : ContinuousAt ψ.symm (Φ (ι q₀)) :=
    (ψ.contMDiffOn_invFun.contMDiffAt (ψ.open_target.mem_nhds htarget)).continuousAt
  have hrec : ContinuousAt recover (ι q₀) :=
    hι.continuousAt.comp (hτ.continuousAt.comp (continuousAt_fst.comp (hψ.comp hΦ)))
  have hreczero : recover (ι q₀) = ι q₀ := by
    have hcoord : ψ.symm (Φ (ι q₀)) = (σ q₀, (0 : B)) := by
      rw [(hparam q₀ hq₀).2]
      exact ψ.left_inv' (hparam q₀ hq₀).1
    change ι (τ ((ψ.symm (Φ (ι q₀))).1)) = ι q₀
    rw [hcoord]
    exact congrArg ι (hτσ q₀)
  have hrecSource : ∀ᶠ z in 𝓝 (ι q₀), recover z ∈ Φ.source :=
    hrec.preimage_mem_nhds (by rw [hreczero]; exact Φ.open_source.mem_nhds hq₀)
  have htargetNear : ∀ᶠ z in 𝓝 (ι q₀), Φ z ∈ ψ.target :=
    hΦ.preimage_mem_nhds (ψ.open_target.mem_nhds htarget)
  filter_upwards [Φ.open_source.mem_nhds hq₀, htargetNear, hrecSource] with z hz hzψ hzrec
  refine ⟨hz, ?_⟩
  constructor
  · intro hzS
    let q := ψ.symm (Φ z)
    have hq : q ∈ ψ.source := ψ.map_target' hzψ
    have hqzero : q.2 = 0 :=
      (hsheet q hq).mp
        (by
          change ψ (ψ.symm (Φ z)) ∈ S
          have he : ψ (ψ.symm (Φ z)) = Φ z := ψ.right_inv' hzψ
          rw [he]
          exact hzS)
    have heq : Φ (recover z) = Φ z := by
      change Φ (ι (τ q.1)) = Φ z
      rw [(hparam (τ q.1) hzrec).2, hστ q.1]
      have hqeq : (q.1, (0 : B)) = q := by
        apply Prod.ext
        · rfl
        · exact hqzero.symm
      rw [hqeq]
      exact ψ.right_inv' hzψ
    exact ⟨τ q.1, Φ.toPartialEquiv.injOn hzrec hz heq⟩
  · rintro ⟨q, hqz⟩
    have hq : ι q ∈ Φ.source := hqz.symm ▸ hz
    rw [← hqz, (hparam q hq).2]
    exact (hsheet _ (hparam q hq).1).mpr rfl

private def Smale.WhitneyPairModel.sheetTimeInverse {A : Type*} (q : (ℝ × A)) : (ℝ × A) :=
  (2 * q.1 - 1, q.2)

private theorem Smale.WhitneyPairModel.contDiff_sheetTimeInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : ContDiff ℝ ∞ (sheetTimeInverse (A := A)) := by
  unfold sheetTimeInverse
  fun_prop

private theorem
    Smale.WhitneyPairModel.sheetTimeInverse_leftInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : Function.LeftInverse (sheetTimeInverse (A := A)) sheetTimeCoordinates := by
  intro q
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · change 2 * ((q.1 + 1) / 2) - 1 = q.1
    ring
  · rfl

private theorem
    Smale.WhitneyPairModel.sheetTimeInverse_rightInverse {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] : Function.RightInverse (sheetTimeInverse (A := A)) sheetTimeCoordinates := by
  intro q
  rw [sheetTimeCoordinates_apply]
  apply Prod.ext
  · change (2 * q.1 - 1 + 1) / 2 = q.1
    ring
  · rfl

private theorem
    Smale.TubularBigon.RankThreeSheetParametrizedChart.eventually_lower_mem_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : Smale.RankThreeWhitneyModel.LowerSheet}
    (hq : Smale.RankThreeWhitneyModel.firstSheet q ∈ c.chart.source) :
    ∀ᶠ z in 𝓝 (Smale.RankThreeWhitneyModel.firstSheet q),
      z ∈ c.chart.source ∧
        (c.chart z ∈ S ↔ z ∈ Set.range Smale.RankThreeWhitneyModel.firstSheet) :=
  Smale.SheetRecognition.eventually_mem_sheet_iff c.chart d.chart d.sheet
    Smale.RankThreeWhitneyModel.contDiff_firstSheet.continuous
    Smale.WhitneyPairModel.contDiff_sheetTimeInverse.continuous
    Smale.WhitneyPairModel.sheetTimeInverse_leftInverse
    Smale.WhitneyPairModel.sheetTimeInverse_rightInverse
    (fun q hq => ⟨c.lower_source q hq, c.lower q hq⟩) hq

private theorem
    Smale.TubularBigon.RankThreeSheetParametrizedChart.eventually_upper_mem_iff {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeSheetParametrizedChart tube d e)
    {q : Smale.RankThreeWhitneyModel.UpperSheet}
    (hq : Smale.RankThreeWhitneyModel.secondSheet h q ∈ c.chart.source) :
    ∀ᶠ z in 𝓝 (Smale.RankThreeWhitneyModel.secondSheet h q),
      z ∈ c.chart.source ∧
        (c.chart z ∈ T ↔ z ∈ Set.range (Smale.RankThreeWhitneyModel.secondSheet h)) :=
  Smale.SheetRecognition.eventually_mem_sheet_iff c.chart e.chart e.sheet
    (Smale.RankThreeWhitneyModel.contDiff_secondSheet h).continuous
    Smale.WhitneyPairModel.contDiff_sheetTimeInverse.continuous
    Smale.WhitneyPairModel.sheetTimeInverse_leftInverse
    Smale.WhitneyPairModel.sheetTimeInverse_rightInverse
    (fun q hq => ⟨c.upper_source q hq, c.upper q hq⟩) hq


private theorem Smale.TubularBigon.lower_center_mem_sheet {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : tube.map (2 * t - 1, 0) ∈ S := by
  rw [tube.lower t ht, ← k.center t ht]
  exact
    (k.first_sheet (t, 0)
          (k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩)).mpr
      rfl

private theorem Smale.TubularBigon.upper_center_mem_sheet {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h n) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : tube.map (Smale.WhitneyPairModel.upperBoundaryArc h t) ∈ T := by
  change tube.map (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ T
  rw [tube.upper t ht, ← l.center t ht]
  exact
    (l.first_sheet (t, 0)
          (l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩)).mpr
      rfl

private theorem Smale.TubularBigon.map_mem_first_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h n) {p : ℝ × ℝ}
    (hp : p ∈ Smale.WhitneyPairModel.bigon h) : tube.map p ∈ S ↔ p.2 = 0 := by
  constructor
  · intro hpS
    have hfront : p ∈ frontier (Smale.WhitneyPairModel.bigon h) := by
      rw [frontier, (Smale.WhitneyPairModel.isClosed_bigon h).closure_eq]
      exact ⟨hp, fun hi => tube.interior_avoids p hi (Or.inl hpS)⟩
    obtain ⟨t, ht, rfl | rfl⟩ :=
      (Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos p).mp hfront
    · rfl
    · have hlt : (t, (0 : ℝ)) ∈ l.domain :=
        l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
      rw [tube.upper t ht, ← l.center t ht] at hpS
      rcases (l.second_sheet (t, 0) hlt).mp hpS with ht0 | ht1
      · change t = 0 at ht0
        rw [ht0]
        norm_num
      · change t = 1 at ht1
        rw [ht1]
        norm_num
  · intro hpzero
    have hpr := Smale.WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    have ht : Smale.WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
      change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * Smale.WhitneyPairModel.arcTime p - 1 := by
      dsimp [Smale.WhitneyPairModel.arcTime]; ring
    have heq : p = (2 * Smale.WhitneyPairModel.arcTime p - 1, 0) := Prod.ext hbase hpzero
    rw [heq]
    exact tube.lower_center_mem_sheet ht

private theorem Smale.TubularBigon.map_mem_second_iff {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁} {n : ℕ}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h n) {p : ℝ × ℝ}
    (hp : p ∈ Smale.WhitneyPairModel.bigon h) : tube.map p ∈ T ↔ p.2 = h * (1 - p.1 ^ 2) := by
  constructor
  · intro hpT
    have hfront : p ∈ frontier (Smale.WhitneyPairModel.bigon h) := by
      rw [frontier, (Smale.WhitneyPairModel.isClosed_bigon h).closure_eq]
      exact ⟨hp, fun hi => tube.interior_avoids p hi (Or.inr hpT)⟩
    obtain ⟨t, ht, rfl | rfl⟩ :=
      (Smale.WhitneyPairModel.mem_frontier_bigon_iff_exists_time tube.height_pos p).mp hfront
    · have hkt : (t, (0 : ℝ)) ∈ k.domain :=
        k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
      rw [tube.lower t ht, ← k.center t ht] at hpT
      rcases (k.second_sheet (t, 0) hkt).mp hpT with ht0 | ht1
      · change t = 0 at ht0
        rw [ht0]
        norm_num
      · change t = 1 at ht1
        rw [ht1]
        norm_num
    · rfl
  · intro hpupper
    have hpr := Smale.WhitneyPairModel.bigon_subset_rectangle tube.height_pos hp
    have ht : Smale.WhitneyPairModel.arcTime p ∈ Set.Icc (0 : ℝ) 1 := by
      change 0 ≤ (p.1 + 1) / 2 ∧ (p.1 + 1) / 2 ≤ 1
      constructor <;> linarith [hpr.1.1, hpr.1.2]
    have hbase : p.1 = 2 * Smale.WhitneyPairModel.arcTime p - 1 := by
      dsimp [Smale.WhitneyPairModel.arcTime]; ring
    have heq : p = Smale.WhitneyPairModel.upperBoundaryArc h (Smale.WhitneyPairModel.arcTime p) :=
      by
      apply Prod.ext hbase
      change p.2 = h * (1 - (2 * Smale.WhitneyPairModel.arcTime p - 1) ^ 2)
      rw [← hbase]
      exact hpupper
    rw [heq]
    exact tube.upper_center_mem_sheet ht

private theorem Smale.SheetRecognition.exists_open_recognition_domain {W E M : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] (Φ : PartialDiffeomorph 𝓘(ℝ, W) 𝓘(ℝ, E) W M ∞)
    {S : Set M} {A K : Set W} (hS : IsClosed S) (hK : K ⊆ Φ.source)
    (hforward : ∀ z ∈ Φ.source, z ∈ A → Φ z ∈ S)
    (hlocal : ∀ z ∈ Φ.source, z ∈ A → ∀ᶠ w in 𝓝 z, w ∈ Φ.source ∧ (Φ w ∈ S ↔ w ∈ A))
    (hcontact : ∀ z ∈ K, Φ z ∈ S ↔ z ∈ A) :
    ∃ U : Set W, IsOpen U ∧ K ⊆ U ∧ U ⊆ Φ.source ∧ ∀ z ∈ U, Φ z ∈ S ↔ z ∈ A := by
  have hnear : ∀ z ∈ K, ∀ᶠ w in 𝓝 z, w ∈ Φ.source ∧ (Φ w ∈ S ↔ w ∈ A) := by
    intro z hz
    by_cases hzA : z ∈ A
    · exact hlocal z (hK hz) hzA
    have hzS : Φ z ∉ S := fun hs => hzA ((hcontact z hz).mp hs)
    have hΦ : ContinuousAt Φ z :=
      (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds (hK hz))).continuousAt
    have havoid : ∀ᶠ w in 𝓝 z, Φ w ∉ S := hΦ.preimage_mem_nhds (hS.isOpen_compl.mem_nhds hzS)
    filter_upwards [Φ.open_source.mem_nhds (hK hz), havoid] with w hw hwS
    exact ⟨hw, ⟨fun hs => (hwS hs).elim, fun ha => (hwS (hforward w hw ha)).elim⟩⟩
  let U := interior {z : W | z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ A)}
  have hsub : U ⊆ {z : W | z ∈ Φ.source ∧ (Φ z ∈ S ↔ z ∈ A)} := interior_subset
  exact
    ⟨U, isOpen_interior, fun z hz => mem_interior_iff_mem_nhds.mpr (hnear z hz), fun _ hz =>
      (hsub hz).1, fun _ hz => (hsub hz).2⟩

private theorem Smale.RankThreeWhitneyModel.zero_mem_firstSheet_iff (p : ℝ × ℝ) :
    (p, (0 : Lower × Upper)) ∈ Set.range firstSheet ↔ p.2 = 0 := by
  constructor
  · rintro ⟨q, hq⟩
    exact (congrArg (fun z : Space => z.1.2) hq).symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

private theorem Smale.RankThreeWhitneyModel.zero_mem_secondSheet_iff (h : ℝ) (p : ℝ × ℝ) :
    (p, (0 : Lower × Upper)) ∈ Set.range (secondSheet h) ↔ p.2 = h * (1 - p.1 ^ 2) := by
  constructor
  · rintro ⟨q, hq⟩
    have hs : q.1 = p.1 := congrArg (fun z : Space => z.1.1) hq
    have ht : h * (1 - q.1 ^ 2) = p.2 := congrArg (fun z : Space => z.1.2) hq
    rw [hs] at ht
    exact ht.symm
  · intro hp
    refine ⟨(p.1, 0), ?_⟩
    exact Prod.ext (Prod.ext rfl hp.symm) rfl

private theorem
    Smale.TubularBigon.RankThreeSheetParametrizedChart.exists_open_full_sheet_neighborhood
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeSheetParametrizedChart tube d e) (hS : IsClosed S)
    (hT : IsClosed T) :
    ∃ U : Set Smale.RankThreeWhitneyModel.Space,
      IsOpen U ∧
        Smale.WhitneyPairModel.bigon h ×ˢ
              {(0 : Smale.RankThreeWhitneyModel.Lower × Smale.RankThreeWhitneyModel.Upper)} ⊆
            U ∧
          U ⊆ c.chart.source ∧
            (∀ z ∈ U, c.chart z ∈ S ↔ z ∈ Set.range Smale.RankThreeWhitneyModel.firstSheet) ∧
              ∀ z ∈ U,
                c.chart z ∈ T ↔ z ∈ Set.range (Smale.RankThreeWhitneyModel.secondSheet h) := by
  have hzero :
    Smale.WhitneyPairModel.bigon h ×ˢ
        {(0 : Smale.RankThreeWhitneyModel.Lower × Smale.RankThreeWhitneyModel.Upper)} ⊆
      c.chart.source := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    exact c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩
  have hfirst :
    ∀
      z ∈
        Smale.WhitneyPairModel.bigon h ×ˢ
          {(0 : Smale.RankThreeWhitneyModel.Lower × Smale.RankThreeWhitneyModel.Upper)},
      c.chart z ∈ S ↔ z ∈ Set.range Smale.RankThreeWhitneyModel.firstSheet := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact
      (tube.map_mem_first_iff hp).trans
        (Smale.RankThreeWhitneyModel.zero_mem_firstSheet_iff p).symm
  have hsecond :
    ∀
      z ∈
        Smale.WhitneyPairModel.bigon h ×ˢ
          {(0 : Smale.RankThreeWhitneyModel.Lower × Smale.RankThreeWhitneyModel.Upper)},
      c.chart z ∈ T ↔ z ∈ Set.range (Smale.RankThreeWhitneyModel.secondSheet h) := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    have hz0 : z = 0 := hz
    subst z
    rw [c.zero_section]
    exact
      (tube.map_mem_second_iff hp).trans
        (Smale.RankThreeWhitneyModel.zero_mem_secondSheet_iff h p).symm
  obtain ⟨U, hU, hKU, hUsource, hUS⟩ :=
    Smale.SheetRecognition.exists_open_recognition_domain c.chart (A :=
      Set.range Smale.RankThreeWhitneyModel.firstSheet) hS hzero
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.lower_mem_sheet hz)
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.eventually_lower_mem_iff hz)
      hfirst
  obtain ⟨V, hV, hKV, -, hVT⟩ :=
    Smale.SheetRecognition.exists_open_recognition_domain c.chart (A :=
      Set.range (Smale.RankThreeWhitneyModel.secondSheet h)) hT hzero
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.upper_mem_sheet hz)
      (fun z hz ⟨q, hq⟩ => by
        rw [← hq] at hz ⊢
        exact c.eventually_upper_mem_iff hz)
      hsecond
  exact
    ⟨U ∩ V, hU.inter hV, fun z hz => ⟨hKU hz, hKV hz⟩, fun _ hz => hUsource hz.1, fun z hz =>
      hUS z hz.1, fun z hz => hVT z hz.2⟩

private def Smale.RankThreeWhitneyModel.nativeFirstSheet {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) : Set M :=
  Φ '' (Set.range firstSheet ∩ Φ.source)

private def Smale.RankThreeWhitneyModel.nativeSecondSheet {F H M : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H} [TopologicalSpace M]
    [ChartedSpace H M] (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) (h : ℝ) : Set M :=
  Φ '' (Set.range (secondSheet h) ∩ Φ.source)

private structure Smale.TubularBigon.RankThreeCompatibleChart {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M} {a b : ℝ → M}
    {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ} {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3) where
  radius : ℝ
  radius_pos : 0 < radius
  chart :
    PartialDiffeomorph 𝓘(ℝ, Smale.RankThreeWhitneyModel.Space) 𝓘(ℝ, E)
      Smale.RankThreeWhitneyModel.Space M ∞
  source_contains : Smale.WhitneyPairModel.bigon h ×ˢ Metric.closedBall 0 radius ⊆ chart.source
  zero_section : ∀ p, chart (p, 0) = tube.map p
  target_subset : chart.target ⊆ tube.chart.target
  first_sheet :
    ∀ z ∈ chart.source, chart z ∈ S ↔ z ∈ Set.range Smale.RankThreeWhitneyModel.firstSheet
  second_sheet :
    ∀ z ∈ chart.source, chart z ∈ T ↔ z ∈ Set.range (Smale.RankThreeWhitneyModel.secondSheet h)

private theorem Smale.TubularBigon.RankThreeSheetParametrizedChart.nonempty_rankThreeCompatibleChart
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    {d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map}
    {e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map}
    (c : Smale.TubularBigon.RankThreeSheetParametrizedChart tube d e) (hS : IsClosed S)
    (hT : IsClosed T) : Nonempty (Smale.TubularBigon.RankThreeCompatibleChart tube) := by
  obtain ⟨U, hU, hKU, hUsource, hfirst, hsecond⟩ := c.exists_open_full_sheet_neighborhood hS hT
  have hlocal :
    IsLocalDiffeomorphOn 𝓘(ℝ, Smale.RankThreeWhitneyModel.Space) 𝓘(ℝ, E) ∞ c.chart U := fun z =>
    ⟨c.chart, hUsource z.property, fun _ _ => rfl⟩
  let Φ :=
    Smale.partialDiffeomorphOfInjectiveLocal hU (c.chart.toPartialEquiv.injOn.mono hUsource)
      hlocal
  have hzero :
    Smale.WhitneyPairModel.bigon h ×ˢ
        {(0 : Smale.RankThreeWhitneyModel.Lower × Smale.RankThreeWhitneyModel.Upper)} ⊆
      Φ.source :=
    hKU
  obtain ⟨ε, hε, hsource⟩ :=
    Smale.DiskFraming.exists_pos_prod_closedBall_subset
      (Smale.WhitneyPairModel.isCompact_bigon tube.height_pos) Φ.open_source hzero
  refine
    ⟨{  radius := ε
        radius_pos := hε
        chart := Φ
        source_contains := hsource
        zero_section := c.zero_section
        target_subset := ?_
        first_sheet := hfirst
        second_sheet := hsecond }⟩
  intro y hy
  change y ∈ c.chart '' U at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact c.target_subset (c.chart.map_source' (hUsource hz))

private theorem Smale.TubularBigon.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    Nonempty (RankThreeCompatibleChart tube) := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeSheetParametrizedChart_of_opposite_corner_signs d e hsign
  exact c.nonempty_rankThreeCompatibleChart hS hT

private theorem Smale.TubularBigon.RankThreeCompatibleChart.nativeFirstSheet_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : Smale.TubularBigon.RankThreeCompatibleChart tube) :
    Smale.RankThreeWhitneyModel.nativeFirstSheet c.chart = S ∩ c.chart.target := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzModel, hzSource⟩, rfl⟩
    exact ⟨(c.first_sheet z hzSource).mpr hzModel, c.chart.map_source' hzSource⟩
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    refine ⟨c.chart.symm y, ⟨?_, hz⟩, hzy⟩
    apply (c.first_sheet _ hz).mp
    change c.chart (c.chart.symm y) ∈ S
    rw [hzy]
    exact hy.1

private theorem Smale.TubularBigon.RankThreeCompatibleChart.nativeSecondSheet_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : Smale.TubularBigon.RankThreeCompatibleChart tube) :
    Smale.RankThreeWhitneyModel.nativeSecondSheet c.chart h = T ∩ c.chart.target := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzModel, hzSource⟩, rfl⟩
    exact ⟨(c.second_sheet z hzSource).mpr hzModel, c.chart.map_source' hzSource⟩
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    refine ⟨c.chart.symm y, ⟨?_, hz⟩, hzy⟩
    apply (c.second_sheet _ hz).mp
    change c.chart (c.chart.symm y) ∈ T
    rw [hzy]
    exact hy.1

private theorem Smale.RankThreeWhitneyModel.GraphMotion.exists_native_cancellation {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (Φ :
      PartialDiffeomorph 𝓘(ℝ, Smale.RankThreeWhitneyModel.Space) J
        Smale.RankThreeWhitneyModel.Space M ∞)
    {h : ℝ} (a : Smale.RankThreeWhitneyModel.GraphMotion h Φ.source) (hh : 0 < h) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    Disjoint
                      ((fun y => A (1, y)) '' Smale.RankThreeWhitneyModel.nativeFirstSheet Φ)
                      (Smale.RankThreeWhitneyModel.nativeSecondSheet Φ h) := by
  have hsource : ∀ t, Set.MapsTo (fun z => a.family (t, z)) Φ.source Φ.source := by
    intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hdfix : ∀ z ∉ a.support, d z = z := fun z hz => (hd z).trans (a.fixed t z hz)
    intro z hz
    change a.family (t, z) ∈ Φ.source
    rw [← hd z]
    exact Smale.SupportedDiffeomorph.mapsTo_source Φ d.toEquiv a.support_subset hdfix hz
  let A : ℝ × M → M := fun p =>
    Smale.SupportedDiffeomorph.extendMap Φ (fun z => a.family (p.1, z)) p.2
  have hcompact : IsCompact (Φ '' a.support) :=
    a.compact_support.image_of_continuousOn
      (Φ.contMDiffOn_toFun.continuousOn.mono a.support_subset)
  have htarget : Φ '' a.support ⊆ Φ.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact Φ.map_source' (a.support_subset hz)
  have hfamily :
    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Smale.RankThreeWhitneyModel.Space))
      𝓘(ℝ, Smale.RankThreeWhitneyModel.Space) ∞ a.family := by
    exact a.smooth.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  refine
    ⟨Φ '' a.support, hcompact, htarget, A,
      Smale.SupportedDiffeomorph.contMDiff_extendFamily Φ hfamily a.compact_support
        a.support_subset a.fixed hsource,
      ?_, ?_, ?_, ?_⟩
  · intro y
    have hzero : (fun z => a.family (0, z)) = id := funext a.initial
    change Smale.SupportedDiffeomorph.extendMap Φ (fun z => a.family (0, z)) y = y
    rw [hzero]
    exact Smale.SupportedDiffeomorph.extendMap_id Φ y
  · intro t
    obtain ⟨d, hd⟩ := a.diffeomorph t
    have hdfix : ∀ z ∉ a.support, d z = z := fun z hz => (hd z).trans (a.fixed t z hz)
    refine ⟨Smale.SupportedDiffeomorph.extension Φ d a.compact_support a.support_subset hdfix, ?_⟩
    intro y
    change
      Smale.SupportedDiffeomorph.extendMap Φ (fun z => a.family (t, z)) y =
        Smale.SupportedDiffeomorph.extendMap Φ d y
    exact
      congrArg
        (fun f : Smale.RankThreeWhitneyModel.Space → Smale.RankThreeWhitneyModel.Space =>
          Smale.SupportedDiffeomorph.extendMap Φ f y)
        (funext (fun z => (hd z).symm))
  · intro t y hy
    exact Smale.SupportedDiffeomorph.extendMap_eq_of_notMem_image Φ (a.fixed t) hy
  · rw [Set.disjoint_left]
    intro y hy₁ hy₂
    obtain ⟨x, hx, hxy⟩ := hy₁
    obtain ⟨z, ⟨⟨p, hp⟩, hz⟩, hzx⟩ := hx
    obtain ⟨w, ⟨⟨q, hq⟩, hw⟩, hwy⟩ := hy₂
    have hleft : A (1, Φ z) = y := by rw [hzx]; exact hxy
    have hcomm : A (1, Φ z) = Φ (a.family (1, z)) :=
      Smale.SupportedDiffeomorph.extendMap_chart Φ (fun v => a.family (1, v)) hz
    have heq : a.family (1, z) = w :=
      Φ.toPartialEquiv.injOn (hsource 1 hz) hw (hcomm.symm.trans (hleft.trans hwy.symm))
    apply a.firstSheet_ne_secondSheet hh p q
    rw [hp, hq]
    exact heq

private theorem
    Smale.RankThreeWhitneyModel.exists_supported_native_bigon_cancellation {F H M : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
    (Φ : PartialDiffeomorph 𝓘(ℝ, Space) J Space M ∞) {h : ℝ} (hh : 0 < h)
    (hsource : ∀ p ∈ Smale.WhitneyPairModel.bigon h, (p, (0 : Lower × Upper)) ∈ Φ.source) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ Φ.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    Disjoint ((fun y => A (1, y)) '' nativeFirstSheet Φ)
                      (nativeSecondSheet Φ h) := by
  obtain ⟨a⟩ := nonempty_graphMotion hh Φ.open_source hsource
  exact a.exists_native_cancellation Φ hh

private theorem
    Smale.SupportedDiffeomorph.image_inter_eq_diff {X : Type*} (d : X ≃ X) {S T U : Set X}
    (hfix : ∀ x ∉ U, d x = x) (hdisjoint : Disjoint (d '' (S ∩ U)) (T ∩ U)) :
    (d '' S) ∩ T = (S ∩ T) \ U := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hyT⟩
    have hyU : y ∉ U := by
      intro hy
      have hxU : x ∈ U := by
        by_contra hnot
        have he : x = y := (hfix x hnot).symm.trans hxy
        exact hnot (he.symm ▸ hy)
      exact Set.disjoint_left.mp hdisjoint ⟨x, ⟨hx, hxU⟩, hxy⟩ ⟨hyT, hy⟩
    have he : x = y := d.injective (hxy.trans (hfix y hyU).symm)
    exact ⟨⟨he ▸ hx, hyT⟩, hyU⟩
  · rintro ⟨⟨hyS, hyT⟩, hyU⟩
    exact ⟨⟨y, hyS, hfix y hyU⟩, hyT⟩

private theorem Smale.SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal {X Y : Type*}
    (d : X ≃ X) (F : Y → X) {T R : Set X} (hfix : ∀ y ∈ (Set.range F ∩ T) \ R, d y = y)
    (himage : (d '' Set.range F) ∩ T = (Set.range F ∩ T) \ R) :
    (d ∘ F) ⁻¹' T = (F ⁻¹' T) \ (F ⁻¹' R) := by
  ext x
  constructor
  · intro hx
    have hy : d (F x) ∈ (d '' Set.range F) ∩ T := ⟨⟨F x, ⟨x, rfl⟩, rfl⟩, hx⟩
    rw [himage] at hy
    have heq : F x = d (F x) := d.injective (hfix _ hy).symm
    change F x ∈ T ∧ F x ∉ R
    rw [heq]
    exact ⟨hy.1.2, hy.2⟩
  · intro hx
    have hy : F x ∈ (Set.range F ∩ T) \ R := ⟨⟨⟨x, rfl⟩, hx.1⟩, hx.2⟩
    change d (F x) ∈ T
    rw [hfix _ hy]
    exact hx.1

private theorem Smale.SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {d : X → X} {F : Y → X} {K : Set X}
    (hK : IsClosed K) (hfix : ∀ y ∉ K, d y = y) (hF : Continuous F) {x : Y} (hx : F x ∉ K) :
    (d ∘ F) =ᶠ[𝓝 x] F := by
  filter_upwards [hF.continuousAt.preimage_mem_nhds (hK.isOpen_compl.mem_nhds hx)] with y hy
  exact hfix _ hy

private theorem Smale.RankThreeWhitneyModel.firstSheet_eq_secondSheet_iff {h : ℝ} (hh : 0 < h)
    (p : LowerSheet) (q : UpperSheet) :
    firstSheet p = secondSheet h q ↔ p.1 = q.1 ∧ p.2 = 0 ∧ q.2 = 0 ∧ (q.1 = -1 ∨ q.1 = 1) := by
  rcases p with ⟨s, u⟩
  rcases q with ⟨t, v⟩
  constructor
  · intro heq
    have hst : s = t := congrArg (fun z : Space => z.1.1) heq
    have ht : 0 = h * (1 - t ^ 2) := congrArg (fun z : Space => z.1.2) heq
    have hu : u = 0 := congrArg (fun z : Space => z.2.1) heq
    have hv : v = 0 := (congrArg (fun z : Space => z.2.2) heq).symm
    have hsq : t ^ 2 = 1 := by
      have hz := (mul_eq_zero.mp ht.symm).resolve_left hh.ne'
      linarith
    have hprod : (t + 1) * (t - 1) = 0 := by nlinarith
    refine ⟨hst, hu, hv, ?_⟩
    rcases mul_eq_zero.mp hprod with hm | hp
    · left
      linarith
    · right
      linarith
  · rintro ⟨hst, hu, hv, ht⟩
    change s = t at hst
    change u = 0 at hu
    change v = 0 at hv
    subst s
    subst u
    subst v
    rcases ht with ht | ht
    · change t = -1 at ht
      subst t
      simp [firstSheet, secondSheet]
    · change t = 1 at ht
      subst t
      simp [firstSheet, secondSheet]

private theorem Smale.TubularBigon.RankThreeCompatibleChart.intersection_in_target_eq {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : Smale.TubularBigon.RankThreeCompatibleChart tube) :
    (S ∩ T) ∩ c.chart.target = {a 0, a 1} := by
  have hc0 : c.chart (Smale.RankThreeWhitneyModel.firstSheet (-1, 0)) = a 0 := by
    calc
      c.chart (Smale.RankThreeWhitneyModel.firstSheet (-1, 0)) = tube.map (-1, 0) :=
        c.zero_section (-1, 0)
      _ = a 0 := by simpa using tube.lower 0 (by simp)
  have hc1 : c.chart (Smale.RankThreeWhitneyModel.firstSheet (1, 0)) = a 1 := by
    calc
      c.chart (Smale.RankThreeWhitneyModel.firstSheet (1, 0)) = tube.map (1, 0) :=
        c.zero_section (1, 0)
      _ = a 1 := by
        have he := tube.lower 1 (by simp)
        norm_num at he
        exact he
  have hcorner :
    ∀ s : ℝ,
      s = -1 ∨ s = 1 →
        c.chart (Smale.RankThreeWhitneyModel.firstSheet (s, 0)) ∈ (S ∩ T) ∩ c.chart.target := by
    intro s hs
    have hb : (s, (0 : ℝ)) ∈ Smale.WhitneyPairModel.bigon h := by
      rcases hs with rfl | rfl <;> simp [Smale.WhitneyPairModel.bigon]
    have hsource : Smale.RankThreeWhitneyModel.firstSheet (s, 0) ∈ c.chart.source :=
      c.source_contains ⟨hb, Metric.mem_closedBall_self c.radius_pos.le⟩
    refine
      ⟨⟨(c.first_sheet _ hsource).mpr ⟨(s, 0), rfl⟩, (c.second_sheet _ hsource).mpr ?_⟩,
        c.chart.map_source' hsource⟩
    refine ⟨(s, 0), ?_⟩
    rcases hs with rfl | rfl <;>
      simp [Smale.RankThreeWhitneyModel.firstSheet, Smale.RankThreeWhitneyModel.secondSheet]
  ext y
  change y ∈ (S ∩ T) ∩ c.chart.target ↔ y = a 0 ∨ y = a 1
  constructor
  · intro hy
    have hz := c.chart.map_target' hy.2
    have hzy : c.chart (c.chart.symm y) = y := c.chart.right_inv' hy.2
    have hlo : c.chart.symm y ∈ Set.range Smale.RankThreeWhitneyModel.firstSheet := by
      apply (c.first_sheet _ hz).mp
      change c.chart (c.chart.symm y) ∈ S
      rw [hzy]
      exact hy.1.1
    have hhi : c.chart.symm y ∈ Set.range (Smale.RankThreeWhitneyModel.secondSheet h) := by
      apply (c.second_sheet _ hz).mp
      change c.chart (c.chart.symm y) ∈ T
      rw [hzy]
      exact hy.1.2
    obtain ⟨p, hp⟩ := hlo
    obtain ⟨q, hq⟩ := hhi
    obtain ⟨hst, hu, _, hends⟩ :=
      (Smale.RankThreeWhitneyModel.firstSheet_eq_secondSheet_iff tube.height_pos p q).mp
        (hp.trans hq.symm)
    have hpq : p = (q.1, 0) := Prod.ext hst hu
    rw [hpq] at hp
    have hycorner : y = c.chart (Smale.RankThreeWhitneyModel.firstSheet (q.1, 0)) :=
      hzy.symm.trans (congrArg c.chart hp.symm)
    rcases hends with hm | hp
    · left
      rw [hm] at hycorner
      exact hycorner.trans hc0
    · right
      rw [hp] at hycorner
      exact hycorner.trans hc1
  · rintro (rfl | rfl)
    · rw [← hc0]
      exact hcorner (-1) (Or.inl rfl)
    · rw [← hc1]
      exact hcorner 1 (Or.inr rfl)

private theorem Smale.TubularBigon.RankThreeCompatibleChart.exists_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {S T : Set M}
    {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : Smale.TubularBigon.RankThreeCompatibleChart tube) [T2Space M] :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ c.chart.target ∧
          ∃ A : ℝ × M → M,
            ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
              (∀ y, A (0, y) = y) ∧
                (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
                  (∀ t y, y ∉ K → A (t, y) = y) ∧
                    ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨K, hK, hKsource, A, hA, hzero, hdiff, hfix, hdisjoint⟩ :=
    Smale.RankThreeWhitneyModel.exists_supported_native_bigon_cancellation c.chart tube.height_pos
      (fun _ hp => c.source_contains ⟨hp, Metric.mem_closedBall_self c.radius_pos.le⟩)
  rw [c.nativeFirstSheet_eq, c.nativeSecondSheet_eq] at hdisjoint
  obtain ⟨d, hd⟩ := hdiff 1
  have hdfix : ∀ y ∉ c.chart.target, d y = y := by
    intro y hy
    exact (hd y).symm.trans (hfix 1 y (fun h => hy (hKsource h)))
  have hdeq : (fun y => A (1, y)) = d := funext hd
  have hdisjoint' : Disjoint (d '' (S ∩ c.chart.target)) (T ∩ c.chart.target) := by
    rw [← hdeq]
    exact hdisjoint
  have hinter : (d '' S) ∩ T = (S ∩ T) \ c.chart.target :=
    Smale.SupportedDiffeomorph.image_inter_eq_diff d.toEquiv hdfix hdisjoint'
  refine ⟨K, hK, hKsource, A, hA, hzero, hdiff, hfix, ?_⟩
  rw [hdeq, hinter, ← c.intersection_in_target_eq]
  ext y
  simp only [Set.mem_sdiff, Set.mem_inter_iff]
  tauto

private theorem
    Smale.TubularBigon.RankThreeCompatibleChart.exists_relative_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    {tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3}
    (c : Smale.TubularBigon.RankThreeCompatibleChart tube) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ c.chart.target ∧
          Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = d y) ∧
                    (∀ t y, y ∉ K → A (t, y) = y) ∧
                      ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨K, hK, hKt, A, hA⟩ := c.exists_cancellation
  refine ⟨K, hK, hKt, ?_, A, hA⟩
  apply Set.disjoint_left.mpr
  intro y hyK hy
  have hc : y ∈ (S ∩ T) ∩ c.chart.target := ⟨hy.1, hKt hyK⟩
  rw [c.intersection_in_target_eq] at hc
  exact hy.2 hc

private theorem Smale.TubularBigon.exists_rankThree_relative_cancellation {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
    {k : Smale.CleanStripPatch (E := E) S T a k₀ k₁}
    {l : Smale.CleanStripPatch (E := E) T S b l₀ l₁}
    (tube : Smale.TubularBigon (E := E) S T a b k.map l.map h 3)
    (d :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Lower (EuclideanSpace ℝ (Fin 3)) (E := E)
        S k.map)
    (e :
      Smale.StripNormalData Smale.RankThreeWhitneyModel.Upper (EuclideanSpace ℝ (Fin 2)) (E := E)
        T l.map)
    (hS : IsClosed S) (hT : IsClosed T)
    (hsign : tube.rankThreeSheetPairDet d e 0 * tube.rankThreeSheetPairDet d e 1 < 0) :
    ∃ K : Set M,
      IsCompact K ∧
        K ⊆ tube.chart.target ∧
          Disjoint K ((S ∩ T) \ {a 0, a 1}) ∧
            ∃ A : ℝ × M → M,
              ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A ∧
                (∀ y, A (0, y) = y) ∧
                  (∀ t, ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, A (t, y) = D y) ∧
                    (∀ t y, y ∉ K → A (t, y) = y) ∧
                      ((fun y => A (1, y)) '' S) ∩ T = (S ∩ T) \ {a 0, a 1} := by
  obtain ⟨c⟩ := tube.nonempty_rankThreeCompatibleChart_of_opposite_corner_signs d e hS hT hsign
  obtain ⟨K, hK, hKt, hd, A, hA⟩ := c.exists_relative_cancellation
  exact ⟨K, hK, hKt.trans c.target_subset, hd, A, hA⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.exists_belt_whitney_cancellation_of_opposite_signs
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
    {f : M → ℝ} {p : M} (D : Smale.ManifoldMorse.MorseSurgeryData E f p)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Smale.Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            D.surgery.beltSphere x y)
      (x₀ x₁ : Smale.Hemisphere.Sphere 2),
      x₀ ∈ D.beltIntersectionPoints 2 g →
        x₁ ∈ D.beltIntersectionPoints 2 g →
          D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1 →
            ∃ K : Set D.UpperLevel,
              IsCompact K ∧
                Disjoint K ((Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁}) ∧
                  ∃ A : ℝ × D.UpperLevel → D.UpperLevel,
                    ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Smale.RegularLevel.Model E))
                        𝓘(ℝ, Smale.RegularLevel.Model E) ∞ A ∧
                      (∀ y, A (0, y) = y) ∧
                        (∀ t,
                            ∃ e :
                              Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E)
                                𝓘(ℝ, Smale.RegularLevel.Model E) D.UpperLevel D.UpperLevel ∞,
                              ∀ y, A (t, y) = e y) ∧
                          (∀ t y, y ∉ K → A (t, y) = y) ∧
                            ((fun y => A (1, y)) '' Set.range g) ∩
                                Set.range D.surgery.beltSphere =
                              (Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁} := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  intro hg hinj hi ht x₀ x₁ hx₀ hx₁ hsign
  obtain ⟨y₀, hy₀⟩ := hx₀
  obtain ⟨y₁, hy₁⟩ := hx₁
  have hne : x₀ ≠ x₁ := by
    intro heq
    rw [heq] at hsign
    have hs : ∀ s : SignType, s * s ≠ -1 := by decide
    exact hs _ hsign
  obtain ⟨a, b, ha₀, ha₁, _, _, k₀, k₁, l₀, l₁, k, l, ⟨d⟩, ⟨e⟩, htube⟩ :=
    D.exists_belt_tubular_strip_pair hf hdim hindex hnull g hg hinj hi (fun x y hxy => ht x y hxy)
      x₀ x₁ y₀ y₁ hy₀ hy₁ hne
  obtain ⟨tube⟩ := htube 1 (by norm_num)
  have hcenter₀ : g x₀ = d.chart (Smale.StripCoordinates.center 0) :=
    ha₀.symm.trans ((k.center 0 (by simp)).symm.trans (d.center 0))
  have hcenter₁ : g x₁ = d.chart (Smale.StripCoordinates.center 1) :=
    ha₁.symm.trans ((k.center 1 (by simp)).symm.trans (d.center 1))
  have hcorner :=
    (D.opposite_beltIntersectionSigns_iff_Whitney_corners hf hdim hindex r g hg hinj hi ht tube d
          e x₀ x₁ hcenter₀ hcenter₁).mp
      hsign
  obtain ⟨K, hK, _, hdisjoint, A, hA, hA₀, hAt, hfix, hcancel⟩ :=
    tube.exists_rankThree_relative_cancellation d e (isCompact_range g.continuous).isClosed
      D.belt_isClosedEmbedding.isClosed_range hcorner
  rw [ha₀, ha₁] at hcancel hdisjoint
  exact ⟨K, hK, hdisjoint, A, hA, hA₀, hAt, hfix, hcancel⟩

attribute [local instance 100] Classical.propDecidable in
private theorem
    Smale.ManifoldMorse.MorseSurgeryData.exists_signed_belt_cancellation_step {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (hnull :
      ∀ γ : C(Smale.Hemisphere.Sphere 1, D.LowerLevel),
        ∃ q, γ.Homotopic (ContinuousMap.const _ q))
    (r : (ℝ × D.chart.NegativeCoordinates) ≃L[ℝ] Smale.Hemisphere.Ambient 3)
    (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel)) :
    letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
    letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
      ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
    ∀ (_hg : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g) (_hinj : Function.Injective g)
      (_hi : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g x))
      (_ht :
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            D.surgery.beltSphere x y)
      (x₀ x₁ : Smale.Hemisphere.Sphere 2),
      x₀ ∈ D.beltIntersectionPoints 2 g →
        x₁ ∈ D.beltIntersectionPoints 2 g →
          D.beltIntersectionSign 2 r g x₀ * D.beltIntersectionSign 2 r g x₁ = -1 →
            ∃ e :
              Diffeomorph 𝓘(ℝ, Smale.RegularLevel.Model E) 𝓘(ℝ, Smale.RegularLevel.Model E)
                D.UpperLevel D.UpperLevel ∞,
              ∃ g' : C(Smale.Hemisphere.Sphere 2, D.UpperLevel),
                Smale.SupportedDiffeomorph.IsotopicToIdentity e ∧
                  (∀ x, g' x = e (g x)) ∧
                    ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g' ∧
                      Function.Injective g' ∧
                        (∀ x,
                            Function.Injective
                              (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g' x)) ∧
                          (∀ x y,
                              Smale.NativeTransversality.At (𝓡 2) (𝓡 3)
                                𝓘(ℝ, Smale.RegularLevel.Model E) g' D.surgery.beltSphere x y) ∧
                            D.beltIntersectionPoints 2 g' =
                                D.beltIntersectionPoints 2 g \ { x₀, x₁ } ∧
                              (∀ x ∈ D.beltIntersectionPoints 2 g',
                                  (g' : Smale.Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g) ∧
                                ∀ x ∈ D.beltIntersectionPoints 2 g',
                                  D.beltIntersectionSign 2 r g' x =
                                    D.beltIntersectionSign 2 r g x := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  let _ : Fact (Module.finrank ℝ (Smale.Hemisphere.Ambient 3) = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  intro hg hinj hi ht x₀ x₁ hx₀ hx₁ hsign
  obtain ⟨K, hK, hdis, A, hA, hA₀, hAt, hfix, hcancel⟩ :=
    D.exists_belt_whitney_cancellation_of_opposite_signs hf hdim hindex hnull r g hg hinj hi ht x₀
      x₁ hx₀ hx₁ hsign
  obtain ⟨e, he⟩ := hAt 1
  have hisotopy : Smale.SupportedDiffeomorph.IsotopicToIdentity e := ⟨A, hA, hA₀, he, hAt⟩
  have hfixe : ∀ y ∉ K, e y = y := fun y hy => (he y).symm.trans (hfix 1 y hy)
  have hfun : (fun y => A (1, y)) = e := funext he
  rw [hfun] at hcancel
  let g' : C(Smale.Hemisphere.Sphere 2, D.UpperLevel) := ⟨e ∘ g, e.continuous.comp g.continuous⟩
  have hg' : ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g' := e.contMDiff.comp hg
  have hinj' : Function.Injective g' := e.injective.comp hinj
  have hi' : ∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g' x) := by
    intro x
    change Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) (e ∘ g) x)
    rw [mfderiv_comp x (e.mdifferentiable (by simp) _) (hg.mdifferentiableAt (by simp))]
    exact
      ((e.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective (by trivial)).comp
        (hi x)
  have hfixR : ∀ y ∈ (Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁}, e y = y := by
    intro y hy
    exact hfixe y (fun hyK => Set.disjoint_left.mp hdis hyK hy)
  have hpre :=
    Smale.SupportedDiffeomorph.preimage_target_eq_diff_of_relative_removal e.toEquiv
      (g : Smale.Hemisphere.Sphere 2 → D.UpperLevel) hfixR hcancel
  have hp : (g : Smale.Hemisphere.Sphere 2 → D.UpperLevel) ⁻¹' {g x₀, g x₁} = { x₀, x₁ } := by
    ext x
    change (g x = g x₀ ∨ g x = g x₁) ↔ (x = x₀ ∨ x = x₁)
    exact or_congr hinj.eq_iff hinj.eq_iff
  have hpoints : D.beltIntersectionPoints 2 g' = D.beltIntersectionPoints 2 g \ { x₀, x₁ } :=
    hpre.trans
      (congrArg (fun s : Set (Smale.Hemisphere.Sphere 2) => D.beltIntersectionPoints 2 g \ s) hp)
  have hgerm :
    ∀ x ∈ D.beltIntersectionPoints 2 g',
      (g' : Smale.Hemisphere.Sphere 2 → D.UpperLevel) =ᶠ[𝓝 x] g := by
    intro x hx
    have hxold : x ∈ D.beltIntersectionPoints 2 g \ { x₀, x₁ } := hpoints ▸ hx
    have hy : g x ∈ (Set.range g ∩ Set.range D.surgery.beltSphere) \ {g x₀, g x₁} := by
      refine ⟨⟨⟨x, rfl⟩, hxold.1⟩, ?_⟩
      change x ∉ (g : Smale.Hemisphere.Sphere 2 → D.UpperLevel) ⁻¹' {g x₀, g x₁}
      rw [hp]
      exact hxold.2
    exact
      Smale.SupportedDiffeomorph.eventuallyEq_comp_of_fixed_off_closed hK.isClosed hfixe
        g.continuous (fun hyK => Set.disjoint_left.mp hdis hyK hy)
  have ht' :
    ∀ x y,
      Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) g'
        D.surgery.beltSphere x y := by
    intro x y hxy
    have hx : x ∈ D.beltIntersectionPoints 2 g' := ⟨y, hxy⟩
    have hnear := hgerm x hx
    have hpoint : g' x = g x := hnear.eq_of_nhds
    have hder :
      (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g' x :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] Smale.RegularLevel.Model E) =
        mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g x :=
      hnear.mfderiv_eq
    change
      Function.Surjective
        ((mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g' x :
              EuclideanSpace ℝ (Fin 2) →L[ℝ] Smale.RegularLevel.Model E).coprod
          (mfderiv (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) D.surgery.beltSphere y :
            EuclideanSpace ℝ (Fin 3) →L[ℝ] Smale.RegularLevel.Model E))
    rw [hder]
    exact ht x y (hxy.trans hpoint)
  refine ⟨e, g', hisotopy, fun _ => rfl, hg', hinj', hi', ht', hpoints, hgerm, ?_⟩
  intro x hx
  have hnormal : (D.beltNormal ∘ g') =ᶠ[𝓝 x] (D.beltNormal ∘ g) := by
    filter_upwards [hgerm x hx] with z hz
    exact congrArg D.beltNormal hz
  have hder :
    (mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g') x :
        EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates) =
      mfderiv (𝓡 2) 𝓘(ℝ, D.chart.NegativeCoordinates) (D.beltNormal ∘ g) x :=
    hnormal.mfderiv_eq
  have hjac : D.beltIntersectionJacobian 2 r g' x = D.beltIntersectionJacobian 2 r g x :=
    congrArg
      (fun L : EuclideanSpace ℝ (Fin 2) →L[ℝ] D.chart.NegativeCoordinates =>
        Smale.SphereNormalCoordinates.normalJacobian r x L)
      hder
  exact congrArg SignType.sign hjac

private def Smale.ManifoldMorse.MorseSurgeryData.IsTransverseBeltSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    (g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel)) : Prop :=
  letI := Smale.RegularLevel.chartedSpace hf D.upper_regular
  letI : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  ContMDiff (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) ∞ g ∧
    Function.Injective g ∧
      (∀ x, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, Smale.RegularLevel.Model E) g x)) ∧
        ∀ x y,
          Smale.NativeTransversality.At (𝓡 2) (𝓡 3) 𝓘(ℝ, Smale.RegularLevel.Model E) g
            D.surgery.beltSphere x y

private theorem
    Smale.ManifoldMorse.MorseSurgeryData.finite_points_of_isTransverseBeltSphere {E M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
    (D : Smale.ManifoldMorse.MorseSurgeryData E f p) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    [T2Space M] [CompactSpace M] (hdim : Module.finrank ℝ E = 6)
    (hindex : Module.finrank ℝ D.chart.NegativeCoordinates = 2)
    {g : C(Smale.Hemisphere.Sphere 2, D.UpperLevel)}
    (hg : D.IsTransverseBeltSphere hf hdim hindex g) : (D.beltIntersectionPoints 2 g).Finite := by
  let _ := Smale.RegularLevel.chartedSpace hf D.upper_regular
  let _ : Fact (Module.finrank ℝ D.chart.PositiveCoordinates = 3 + 1) :=
    ⟨by have hh := D.chart.finrank_negative_add_positive; omega⟩
  obtain ⟨hs, hinj, _, ht⟩ := hg
  exact D.finite_beltIntersectionPoints hf 3 2 hindex g hs hinj ht

private def
    MorseCancel.nativeMorseCount (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (k : ℕ) : ℕ :=
  {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}.ncard

private theorem
    MorseCancel.indexed_criticalPoints_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) (k : ℕ) :
    {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E g ∧ nativeMorseIndex E g z = k} =
      {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k} \
        { p, q } := by
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hzg, hindex⟩
    obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hzg
    rw [nativeMorseIndex_congr_germ (hkeep z hzg)] at hindex
    exact ⟨⟨hzf, hindex⟩, hzp, hzq⟩
  · rintro ⟨⟨hzf, hindex⟩, hzp, hzq⟩
    have hzg := (hcrit z).mpr ⟨hzf, hzp, hzq⟩
    exact ⟨hzg, (nativeMorseIndex_congr_germ (hkeep z hzg)).trans hindex⟩

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.nativeMorseCount_after_pair_removal {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) (k : ℕ) :
    nativeMorseCount E g k + (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) =
      nativeMorseCount E f k := by
  let K := {z : M | z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ nativeMorseIndex E f z = k}
  have hK : K.Finite := hfinite.subset (fun _ hz => hz.1)
  have hdiff : K \ (K ∩ { p, q }) = K \ { p, q } := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_inter_iff]
    tauto
  have hrem :
    (K ∩ { p, q }).ncard =
      (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) := by
    by_cases hip : nativeMorseIndex E f p = k
    · have hpK : p ∈ K := ⟨hp, hip⟩
      rw [Set.inter_insert_of_mem hpK, ite_eq_left hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), ite_eq_left hiq,
          Set.ncard_pair hpq]
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), ite_eq_right hiq]
        simp
    · have hpK : p ∉ K := fun h => hip h.2
      rw [Set.inter_insert_of_notMem hpK, ite_eq_right hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [Set.inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), ite_eq_left hiq]
        simp
      · rw [Set.inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), ite_eq_right hiq]
        simp
  have hc := Set.ncard_sdiff_add_ncard_of_subset (Set.inter_subset_left : K ∩ { p, q } ⊆ K) hK
  rw [hdiff, hrem] at hc
  unfold nativeMorseCount
  rw [indexed_criticalPoints_after_pair_removal hcrit hkeep k]
  exact (Nat.add_assoc _ _ _).trans hc

attribute [local instance 100] Classical.propDecidable in
private theorem MorseCancel.nativeMorseCount_adjacent_pair {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}
    (hfinite : (Smale.ManifoldMorse.criticalPoints E f).Finite)
    (hp : p ∈ Smale.ManifoldMorse.criticalPoints E f)
    (hq : q ∈ Smale.ManifoldMorse.criticalPoints E f) (hpq : p ≠ q)
    (hcrit :
      ∀ z,
        z ∈ Smale.ManifoldMorse.criticalPoints E g ↔
          z ∈ Smale.ManifoldMorse.criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ Smale.ManifoldMorse.criticalPoints E g, g =ᶠ[𝓝 z] f) {k : ℕ}
    (hip : nativeMorseIndex E f p = k) (hiq : nativeMorseIndex E f q = k + 1) :
    nativeMorseCount E g k + 1 = nativeMorseCount E f k ∧
      nativeMorseCount E g (k + 1) + 1 = nativeMorseCount E f (k + 1) ∧
        ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  have hc := nativeMorseCount_after_pair_removal hfinite hp hq hpq hcrit hkeep
  refine ⟨?_, ?_, ?_⟩
  · simpa [hip, hiq] using hc k
  · simpa [hip, hiq, show k ≠ k + 1 by omega] using hc (k + 1)
  · intro j hj hj'
    simpa only [hip, hiq, ite_eq_right (Ne.symm hj), ite_eq_right (Ne.symm hj'),
      Nat.add_zero] using hc j

private def
    Smale.RadialCoreShrink.shrink {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (a : ℝ)
    (y : E) : E :=
  (Max.max (‖y‖ - Max.max a 0) 0 / ‖y‖) • y

@[simp]
private theorem
    Smale.RadialCoreShrink.shrink_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) : shrink a (0 : E) = 0 := by simp [shrink]

private theorem
    Smale.RadialCoreShrink.norm_shrink {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (y : E) : ‖shrink a y‖ = Max.max (‖y‖ - Max.max a 0) 0 := by
  by_cases hy : y = 0
  · subst y
    rw [shrink_zero, norm_zero]
    exact (max_eq_right (by linarith [le_max_right a 0])).symm
  rw [shrink, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (le_max_right _ _) (norm_nonneg y)),
    div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy)]

private theorem
    Smale.RadialCoreShrink.norm_shrink_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (y : E) : ‖shrink a y‖ ≤ ‖y‖ := by
  rw [norm_shrink]
  exact max_le (sub_le_self _ (le_max_right a 0)) (norm_nonneg y)

@[simp]
private theorem Smale.RadialCoreShrink.shrink_zero_parameter {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (y : E) : shrink 0 y = y := by
  by_cases hy : y = 0
  · subst y
    exact shrink_zero 0
  rw [shrink, max_self, sub_zero, max_eq_left (norm_nonneg y), div_self (norm_ne_zero_iff.mpr hy),
    one_smul]

private theorem
    Smale.RadialCoreShrink.shrink_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : ℝ} {y : E} (hy : ‖y‖ ≤ a) : shrink a y = 0 := by
  rw [shrink, max_eq_right (sub_nonpos.mpr (hy.trans (le_max_left a 0))), zero_div, zero_smul]

private theorem Smale.RadialCoreShrink.continuous_shrink {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Continuous (fun z : ℝ × E => shrink z.1 z.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨a, y⟩
  by_cases hy : y = 0
  · subst y
    change Filter.Tendsto (fun z : ℝ × E => shrink z.1 z.2) (𝓝 (a, 0)) (𝓝 (shrink a 0))
    rw [shrink_zero]
    apply squeeze_zero_norm (fun z => norm_shrink_le z.1 z.2)
    simpa only [ContinuousAt, norm_zero] using
      (continuous_snd.norm.continuousAt : ContinuousAt (fun z : ℝ × E => ‖z.2‖) (a, 0))
  exact
    (((continuous_snd.norm.sub (continuous_fst.max continuous_const)).max
              continuous_const).continuousAt.div
          continuous_snd.norm.continuousAt (norm_ne_zero_iff.mpr hy)).smul
      continuous_snd.continuousAt

private def Smale.HandleCoreDeformation.denominator {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :
    ℝ :=
  Max.max ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)

private theorem Smale.HandleCoreDeformation.denominator_pos {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :
    0 < denominator z := by
  have hy : ‖(z.2 : P)‖ ≤ 1 := mem_closedBall_zero_iff.mp z.2.property
  have h := le_max_right ‖(z.1 : N)‖ (1 - ‖(z.2 : P)‖ / 2)
  dsimp [denominator]
  linarith

private theorem
    Smale.HandleCoreDeformation.continuous_denominator {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] : Continuous (denominator (N := N) (P := P)) :=
  (continuous_subtype_val.comp continuous_fst).norm.max
    (continuous_const.sub ((continuous_subtype_val.comp continuous_snd).norm.div_const 2))

private def
    Smale.HandleCoreDeformation.negative {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :
    Smale.MorseHandle.UnitDisk N :=
  ⟨(denominator z)⁻¹ • (z.1 : N),
    by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (denominator_pos z))]
    calc
      _ ≤ (denominator z)⁻¹ * denominator z :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (inv_pos.mpr (denominator_pos z)).le
      _ = 1 := inv_mul_cancel₀ (denominator_pos z).ne'⟩

private def Smale.HandleCoreDeformation.positive {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :
    Smale.MorseHandle.UnitDisk P :=
  ⟨Smale.RadialCoreShrink.shrink (2 * (1 - ‖(z.1 : N)‖)) (z.2 : P),
    mem_closedBall_zero_iff.mpr
      ((Smale.RadialCoreShrink.norm_shrink_le _ _).trans
        (mem_closedBall_zero_iff.mp z.2.property))⟩

private theorem Smale.HandleCoreDeformation.continuous_negative {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] : Continuous (negative (N := N) (P := P)) :=
  ((continuous_denominator.inv₀ (fun z => (denominator_pos z).ne')).smul
        (continuous_subtype_val.comp continuous_fst)).subtype_mk
    _

private theorem Smale.HandleCoreDeformation.continuous_positive {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] : Continuous (positive (N := N) (P := P)) :=
  (Smale.RadialCoreShrink.continuous_shrink.comp
        ((continuous_const.mul
              (continuous_const.sub (continuous_subtype_val.comp continuous_fst).norm)).prodMk
          (continuous_subtype_val.comp continuous_snd))).subtype_mk
    _

private def
    Smale.HandleCoreDeformation.collapse {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] :
    C(Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P,
      Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :=
  ⟨fun z => (negative z, positive z), continuous_negative.prodMk continuous_positive⟩

private def Smale.HandleCoreDeformation.faceCore {N P : Type*} [NormedAddCommGroup N]
    [NormedAddCommGroup P] : Set (Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) :=
  {z | ‖(z.1 : N)‖ = 1 ∨ (z.2 : P) = 0}

private theorem Smale.HandleCoreDeformation.collapse_mem {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) : collapse z ∈ faceCore := by
  rcases le_total (1 - ‖(z.2 : P)‖ / 2) ‖(z.1 : N)‖ with h | h
  · left
    have hx : 0 < ‖(z.1 : N)‖ := by
      have hpos := denominator_pos z
      rwa [denominator, max_eq_left h] at hpos
    change ‖(denominator z)⁻¹ • (z.1 : N)‖ = 1
    rw [denominator, max_eq_left h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx),
      inv_mul_cancel₀ hx.ne']
  · right
    apply Smale.RadialCoreShrink.shrink_eq_zero
    linarith

private theorem Smale.HandleCoreDeformation.collapse_face {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) (hz : ‖(z.1 : N)‖ = 1) :
    collapse z = z := by
  have hd : denominator z = 1 := by
    rw [denominator, hz, max_eq_left]
    linarith [norm_nonneg (z.2 : P)]
  apply Prod.ext
  · apply Subtype.ext
    change (denominator z)⁻¹ • (z.1 : N) = (z.1 : N)
    rw [hd, inv_one, one_smul]
  · apply Subtype.ext
    change Smale.RadialCoreShrink.shrink (2 * (1 - ‖(z.1 : N)‖)) (z.2 : P) = (z.2 : P)
    rw [hz, sub_self, MulZeroClass.mul_zero, Smale.RadialCoreShrink.shrink_zero_parameter]

private theorem Smale.HandleCoreDeformation.collapse_core {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) (hz : (z.2 : P) = 0) :
    collapse z = z := by
  have hd : denominator z = 1 := by
    rw [denominator, hz, norm_zero, zero_div, sub_zero]
    exact max_eq_right (mem_closedBall_zero_iff.mp z.1.property)
  apply Prod.ext
  · apply Subtype.ext
    change (denominator z)⁻¹ • (z.1 : N) = (z.1 : N)
    rw [hd, inv_one, one_smul]
  · apply Subtype.ext
    change Smale.RadialCoreShrink.shrink (2 * (1 - ‖(z.1 : N)‖)) (z.2 : P) = (z.2 : P)
    rw [hz, Smale.RadialCoreShrink.shrink_zero]

private theorem Smale.HandleCoreDeformation.collapse_fixed {N P : Type*} [NormedAddCommGroup N]
    [NormedSpace ℝ N] [NormedAddCommGroup P] [NormedSpace ℝ P]
    (z : Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P) (hz : z ∈ faceCore) :
    collapse z = z :=
  hz.elim (collapse_face z) (collapse_core z)

private def
    Smale.HandleCoreDeformation.diskBlend {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (t : (unitInterval)) (x y : Smale.MorseHandle.UnitDisk V) : Smale.MorseHandle.UnitDisk V :=
  ⟨(1 - (t : ℝ)) • (x : V) + (t : ℝ) • (y : V),
    (convex_closedBall (0 : V) 1) x.property y.property (sub_nonneg.mpr t.property.2) t.property.1
      (sub_add_cancel 1 (t : ℝ))⟩

private theorem Smale.HandleCoreDeformation.continuous_diskBlend {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] :
    Continuous
      (fun q : (unitInterval) × (Smale.MorseHandle.UnitDisk V × Smale.MorseHandle.UnitDisk V) =>
        diskBlend q.1 q.2.1 q.2.2) :=
  (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
            (continuous_subtype_val.comp continuous_snd.fst)).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp continuous_snd.snd))).subtype_mk
    _

@[simp]
private theorem Smale.HandleCoreDeformation.diskBlend_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x y : Smale.MorseHandle.UnitDisk V) : diskBlend 0 x y = x := by
  apply Subtype.ext
  simp [diskBlend]

@[simp]
private theorem Smale.HandleCoreDeformation.diskBlend_one {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (x y : Smale.MorseHandle.UnitDisk V) : diskBlend 1 x y = y := by
  apply Subtype.ext
  simp [diskBlend]

@[simp]
private theorem Smale.HandleCoreDeformation.diskBlend_self {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (t : (unitInterval)) (x : Smale.MorseHandle.UnitDisk V) :
    diskBlend t x x = x := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • (x : V) + (t : ℝ) • (x : V) = (x : V)
  rw [← add_smul, sub_add_cancel, one_smul]

private def
    Smale.HandleCoreDeformation.deformation {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (ContinuousMap.id (Smale.MorseHandle.UnitDisk N × Smale.MorseHandle.UnitDisk P)).HomotopyRel
      collapse faceCore
    where
  toFun q := (diskBlend q.1 q.2.1 (collapse q.2).1, diskBlend q.1 q.2.2 (collapse q.2).2)
  continuous_toFun :=
    (continuous_diskBlend.comp
          (continuous_fst.prodMk
            (continuous_snd.fst.prodMk (collapse.continuous.comp continuous_snd).fst))).prodMk
      (continuous_diskBlend.comp
        (continuous_fst.prodMk
          (continuous_snd.snd.prodMk (collapse.continuous.comp continuous_snd).snd)))
  map_zero_left z := by simp
  map_one_left z := by simp
  prop' t z
    hz := by
    change (diskBlend t z.1 (collapse z).1, diskBlend t z.2 (collapse z).2) = z
    rw [collapse_fixed z hz]
    simp

private def Smale.ClosedCover.mapOfClosedPieces {R P X Y : Type*} [TopologicalSpace R]
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y] (r : R → X) (p : P → X)
    (hr : Topology.IsClosedEmbedding r) (hp : Topology.IsClosedEmbedding p)
    (hcover : Set.range r ∪ Set.range p = Set.univ) (f : C(R, Y)) (g : C(P, Y))
    (hagree : ∀ a b, r a = p b → f a = g b) : C(X, Y) := by
  let a := hr.isEmbedding.toHomeomorph
  let b := hp.isEmbedding.toHomeomorph
  refine ⟨glue hcover (fun x => f (a.symm x)) (fun x => g (b.symm x)), ?_⟩
  apply
    continuous_glue hcover hr.isClosed_range hp.isClosed_range _ _
      (f.continuous.comp a.symm.continuous) (g.continuous.comp b.symm.continuous)
  intro x y hxy
  apply hagree
  exact
    (congrArg Subtype.val (a.apply_symm_apply x)).trans
      (hxy.trans (congrArg Subtype.val (b.apply_symm_apply y)).symm)

private theorem Smale.ClosedCover.mapOfClosedPieces_left {R P X Y : Type*} [TopologicalSpace R]
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y] (r : R → X) (p : P → X)
    (hr : Topology.IsClosedEmbedding r) (hp : Topology.IsClosedEmbedding p)
    (hcover : Set.range r ∪ Set.range p = Set.univ) (f : C(R, Y)) (g : C(P, Y))
    (hagree : ∀ a b, r a = p b → f a = g b) (x : R) :
    mapOfClosedPieces r p hr hp hcover f g hagree (r x) = f x := by
  let a := hr.isEmbedding.toHomeomorph
  let b := hp.isEmbedding.toHomeomorph
  change glue hcover (fun z => f (a.symm z)) (fun z => g (b.symm z)) (r x) = f x
  exact
    (glue_left hcover _ _ ⟨r x, Set.mem_range_self x⟩).trans (congrArg f (a.symm_apply_apply x))

private theorem Smale.ClosedCover.mapOfClosedPieces_right {R P X Y : Type*} [TopologicalSpace R]
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y] (r : R → X) (p : P → X)
    (hr : Topology.IsClosedEmbedding r) (hp : Topology.IsClosedEmbedding p)
    (hcover : Set.range r ∪ Set.range p = Set.univ) (f : C(R, Y)) (g : C(P, Y))
    (hagree : ∀ a b, r a = p b → f a = g b) (x : P) :
    mapOfClosedPieces r p hr hp hcover f g hagree (p x) = g x := by
  let a := hr.isEmbedding.toHomeomorph
  let b := hp.isEmbedding.toHomeomorph
  have hagree' :
    ∀ u : Set.range r, ∀ v : Set.range p, (u : X) = v → f (a.symm u) = g (b.symm v) := by
    intro u v huv
    apply hagree
    exact
      (congrArg Subtype.val (a.apply_symm_apply u)).trans
        (huv.trans (congrArg Subtype.val (b.apply_symm_apply v)).symm)
  change glue hcover (fun z => f (a.symm z)) (fun z => g (b.symm z)) (p x) = g x
  exact
    (glue_right hcover _ _ hagree' ⟨p x, Set.mem_range_self x⟩).trans
      (congrArg g (b.symm_apply_apply x))

end Mathoverflow1973

end
