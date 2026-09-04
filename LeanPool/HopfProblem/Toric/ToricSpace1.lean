/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen1

/-!
# Hopf problem: toric · toric space 1

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

private abbrev ToricCharts.CoordinateSpace (d : ℕ) :=
  Fin d → ℂ

private def ToricCharts.torus {d : ℕ} : Set (CoordinateSpace d) :=
  {z | ∀ j, z j ≠ 0}

private theorem ToricCharts.torus_open {d : ℕ} : IsOpen (torus : Set (CoordinateSpace d)) := by
  unfold torus
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_ne_fun (continuous_apply j) continuous_const

private theorem ToricCharts.torus_dense {d : ℕ} : Dense (torus : Set (CoordinateSpace d)) := by
  simpa [torus, Set.pi] using
    (dense_pi (Set.univ : Set (Fin d)) fun _ _ => dense_compl_singleton (0 : ℂ))

private def ToricCharts.monomial {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (z : CoordinateSpace d) :
    CoordinateSpace d := fun i => ∏ j, z j ^ A i j

private def ToricCharts.domain {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : Set (CoordinateSpace d) :=
  {z | ∀ i j, A i j < 0 → z j ≠ 0}

private theorem
    ToricCharts.domain_open {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : IsOpen (domain A) := by
  unfold domain
  simp only [Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases h : A i j < 0
  · simpa [h] using isOpen_ne_fun (continuous_apply j) continuous_const
  · simp [h]

private theorem ToricCharts.torus_subset_domain {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) :
    torus ⊆ domain A := fun _ hz _ j _ => hz j

private theorem ToricCharts.monomial_mapsTo_torus {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) :
    Set.MapsTo (monomial A) torus torus := by
  intro z hz i
  exact Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hz j)

private theorem ToricCharts.monomial_contDiffOn {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) (n : ℕ∞ω) :
    ContDiffOn ℂ n (monomial A) (domain A) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_prod
  intro j _
  cases h : A i j with
  | ofNat k =>
    simpa only [h, Int.ofNat_eq_natCast, zpow_natCast] using
      (contDiff_apply ℂ ℂ j).contDiffOn.pow k
  | negSucc k =>
    have hn : A i j < 0 := by omega
    intro z hz
    simpa only [h, zpow_negSucc] using
      ((contDiff_apply ℂ ℂ j).contDiffWithinAt.pow (k + 1)).fun_inv (pow_ne_zero _ (hz i j hn))

private theorem ToricCharts.prod_zpow_eq_mo1973_9082 {d : ℕ} (a : ℂ) (ha : a ≠ 0)
    (s : Finset (Fin d)) (k : Fin d → ℤ) : (∏ i ∈ s, a ^ k i) = a ^ ∑ i ∈ s, k i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, zpow_add₀ ha]

private theorem ToricCharts.monomial_mul_on_torus {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ)
    {z : CoordinateSpace d} (hz : z ∈ torus) : monomial A (monomial B z) = monomial (A * B) z := by
  funext i
  simp only [monomial, Matrix.mul_apply]
  calc
    (∏ k, (∏ j, z j ^ B k j) ^ A i k) = ∏ k, ∏ j, z j ^ (A i k * B k j) := by
      apply Finset.prod_congr rfl
      intro k _
      rw [← Finset.prod_zpow]
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_mul, mul_comm]
    _ = ∏ j, ∏ k, z j ^ (A i k * B k j) := Finset.prod_comm
    _ = ∏ j, z j ^ ∑ k, A i k * B k j := by
      apply Finset.prod_congr rfl
      intro j _
      exact prod_zpow_eq_mo1973_9082 (z j) (hz j) _ _

@[simp]
private theorem ToricCharts.monomial_one {d : ℕ} (z : CoordinateSpace d) : monomial 1 z = z := by
  funext i
  simp [monomial, Matrix.one_apply]

private theorem ToricCharts.monomial_mul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ)
    (z w : CoordinateSpace d) : monomial A (z * w) = monomial A z * monomial A w := by
  funext i
  simp [monomial, mul_zpow, Finset.prod_mul_distrib]

@[simp]
private theorem
    ToricCharts.monomial_ones {d : ℕ} (A : Matrix (Fin d) (Fin d) ℤ) : monomial A 1 = 1 := by
  funext i
  simp [monomial]

private def
    ToricCharts.overlap {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) : Set (CoordinateSpace d) :=
  domain A ∩ monomial A ⁻¹' domain B

private theorem ToricCharts.overlap_open {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) :
    IsOpen (overlap A B) :=
  (monomial_contDiffOn A 0).continuousOn.isOpen_inter_preimage (domain_open A) (domain_open B)

private theorem ToricCharts.torus_subset_overlap {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) :
    torus ⊆ overlap A B := fun _ hz =>
  ⟨torus_subset_domain A hz, torus_subset_domain B (monomial_mapsTo_torus A hz)⟩

private theorem ToricCharts.monomial_inverse_on_overlap {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ)
    (hBA : B * A = 1) : Set.EqOn (monomial B ∘ monomial A) id (overlap A B) := by
  have h : Set.EqOn (monomial B ∘ monomial A) id (overlap A B ∩ torus) := by
    intro z hz
    simpa [hBA] using monomial_mul_on_torus B A hz.2
  refine
    h.of_subset_closure ?_ continuousOn_id Set.inter_subset_left
      (torus_dense.open_subset_closure_inter (overlap_open A B))
  exact
    (monomial_contDiffOn B 0).continuousOn.comp
      ((monomial_contDiffOn A 0).continuousOn.mono Set.inter_subset_left) (fun _ hz => hz.2)

private def
    ToricCharts.changeOfCoordinates {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (hAB : A * B = 1)
    (hBA : B * A = 1) : OpenPartialHomeomorph (CoordinateSpace d) (CoordinateSpace d)
    where
  toFun := monomial A
  invFun := monomial B
  source := overlap A B
  target := overlap B A
  map_source' z
    hz :=
    ⟨hz.2, by
      change (monomial B ∘ monomial A) z ∈ domain A
      rw [monomial_inverse_on_overlap A B hBA hz]
      exact hz.1⟩
  map_target' z
    hz :=
    ⟨hz.2, by
      change (monomial A ∘ monomial B) z ∈ domain B
      rw [monomial_inverse_on_overlap B A hAB hz]
      exact hz.1⟩
  left_inv' := monomial_inverse_on_overlap A B hBA
  right_inv' := monomial_inverse_on_overlap B A hAB
  open_source := overlap_open A B
  open_target := overlap_open B A
  continuousOn_toFun := (monomial_contDiffOn A 0).continuousOn.mono Set.inter_subset_left
  continuousOn_invFun := (monomial_contDiffOn B 0).continuousOn.mono Set.inter_subset_left

private theorem ToricCharts.changeOfCoordinates_holomorphic {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ)
    (hAB : A * B = 1) (hBA : B * A = 1) :
    ContDiffOn ℂ ω (changeOfCoordinates A B hAB hBA) (changeOfCoordinates A B hAB hBA).source :=
  (monomial_contDiffOn A ω).mono Set.inter_subset_left


private def ToricCharts.HeightOne (A : Matrix (Fin 3) (Fin 3) ℤ) : Prop :=
  ∀ j, ∑ i, A i j = 1

private theorem ToricCharts.column_single_of_zero {A : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A)
    {z : CoordinateSpace 3} (hz : z ∈ domain A) {j : Fin 3} (hj : z j = 0) :
    ∃ k : Fin 3, ∀ i, A i j = if i = k then 1 else 0 := by
  have hn (i : Fin 3) : 0 ≤ A i j := by
    by_contra h
    exact hz i j (lt_of_not_ge h) hj
  have hsum := hA j
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.sum_univ_zero,
    add_zero] at hsum
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have hcases : A 0 j = 1 ∨ A 1 j = 1 ∨ A 2 j = 1 := by omega
  rcases hcases with h | h | h
  · refine ⟨0, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
  · refine ⟨1, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega
  · refine ⟨2, ?_⟩
    intro i
    fin_cases i <;> simp <;> omega

private theorem ToricCharts.monomial_zero_of_column_single {A : Matrix (Fin 3) (Fin 3) ℤ}
    {z : CoordinateSpace 3} {j k : Fin 3} (hj : z j = 0)
    (hc : ∀ i, A i j = if i = k then 1 else 0) : monomial A z k = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hj, hc]

private theorem
    ToricCharts.inverse_mapsTo_domain {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A)
    (hBA : B * A = 1) : Set.MapsTo (monomial A) (domain A) (domain B) := by
  intro z hz i k hB hzero
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hzero
  have hzj : z j = 0 := eq_zero_of_zpow_eq_zero hj
  have hAj : A k j ≠ 0 := by
    intro he
    simp [he] at hj
  obtain ⟨l, hl⟩ := column_single_of_zero hA hz hzj
  have hkl : k = l := by
    by_contra h
    exact hAj (by simp [hl, h])
  subst l
  have hentry := congrFun (congrFun hBA i) j
  have hnonneg : 0 ≤ B i k := by
    have he : B i k = (1 : Matrix (Fin 3) (Fin 3) ℤ) i j := by
      simpa [Matrix.mul_apply, hl] using hentry
    rw [he, Matrix.one_apply]
    split_ifs <;> norm_num
  exact (not_lt_of_ge hnonneg) hB

private theorem ToricCharts.overlap_eq_domain {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A)
    (hBA : B * A = 1) : overlap A B = domain A := by
  exact Set.inter_eq_left.mpr (inverse_mapsTo_domain hA hBA)

private theorem ToricCharts.domain_composition {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A) :
    overlap A B ⊆ domain (B * A) := by
  intro z hz i j hC hzj
  obtain ⟨k, hk⟩ := column_single_of_zero hA hz.1 hzj
  have hzAk : monomial A z k = 0 := monomial_zero_of_column_single hzj hk
  have hBk : B i k < 0 := by simpa [Matrix.mul_apply, hk] using hC
  exact hz.2 i k hBk hzAk

private theorem
    ToricCharts.monomial_mul_on_overlap {A B : Matrix (Fin 3) (Fin 3) ℤ} (hA : HeightOne A) :
    Set.EqOn (monomial B ∘ monomial A) (monomial (B * A)) (overlap A B) := by
  have h : Set.EqOn (monomial B ∘ monomial A) (monomial (B * A)) (overlap A B ∩ torus) :=
    fun _ hz => monomial_mul_on_torus B A hz.2
  refine
    h.of_subset_closure ?_ ?_ Set.inter_subset_left
      (torus_dense.open_subset_closure_inter (overlap_open A B))
  · exact
      (monomial_contDiffOn B 0).continuousOn.comp
        ((monomial_contDiffOn A 0).continuousOn.mono Set.inter_subset_left) (fun _ hz => hz.2)
  · exact (monomial_contDiffOn (B * A) 0).continuousOn.mono (domain_composition hA)

@[ext]
private structure ToricFan.Triangle where
  a : ℤ
  b : ℤ
  upper : Bool
  deriving DecidableEq

private instance ToricFan.instLocal1 : Countable Triangle := by
  apply Function.Injective.countable (f := fun s : Triangle => (s.a, s.b, s.upper))
  intro s t h
  simpa only [Prod.mk.injEq, Triangle.ext_iff, and_assoc] using h

private def ToricFan.Triangle.rays (s : ToricFan.Triangle) : Matrix (Fin 3) (Fin 3) ℤ :=
  if s.upper then !![s.a + 1, s.a, s.a + 1; s.b, s.b + 1, s.b + 1; 1, 1, 1]
  else !![s.a, s.a + 1, s.a; s.b, s.b, s.b + 1; 1, 1, 1]

private def ToricFan.Triangle.dual (s : ToricFan.Triangle) : Matrix (Fin 3) (Fin 3) ℤ :=
  if s.upper then !![0, -1, s.b + 1; -1, 0, s.a + 1; 1, 1, -1 - s.a - s.b]
  else !![-1, -1, 1 + s.a + s.b; 1, 0, -s.a; 0, 1, -s.b]

private theorem ToricFan.Triangle.dual_rays (s : ToricFan.Triangle) : s.dual * s.rays = 1 := by
  ext i j
  cases h : s.upper <;> fin_cases i <;> fin_cases j <;>
      simp [dual, rays, h, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem ToricFan.Triangle.rays_dual (s : ToricFan.Triangle) : s.rays * s.dual = 1 := by
  ext i j
  cases h : s.upper <;> fin_cases i <;> fin_cases j <;>
      simp [dual, rays, h, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring


@[simp]
private theorem
    ToricFan.Triangle.rays_height (s : ToricFan.Triangle) (j : Fin 3) : s.rays 2 j = 1 := by
  cases h : s.upper <;> fin_cases j <;> simp [rays, h]

private def ToricFan.Triangle.transition (s t : ToricFan.Triangle) : Matrix (Fin 3) (Fin 3) ℤ :=
  t.dual * s.rays

@[simp]
private theorem ToricFan.Triangle.transition_self (s : ToricFan.Triangle) : transition s s = 1 :=
  s.dual_rays

private theorem ToricFan.Triangle.transition_mul (r s t : ToricFan.Triangle) :
    transition s t * transition r s = transition r t := by
  unfold transition
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc s.rays, rays_dual, Matrix.one_mul]

private theorem ToricFan.Triangle.transition_covariance (s t : ToricFan.Triangle) :
    t.rays * transition s t = s.rays := by
  rw [transition, ← Matrix.mul_assoc, rays_dual, Matrix.one_mul]

private theorem ToricFan.Triangle.transition_heightOne (s t : ToricFan.Triangle) :
    ToricCharts.HeightOne (transition s t) := by
  intro j
  have h := congrFun (congrFun (transition_covariance s t) 2) j
  simpa [Matrix.mul_apply] using h

private def ToricFan.Triangle.chartChange (s t : ToricFan.Triangle) :
    OpenPartialHomeomorph (ToricCharts.CoordinateSpace 3) (ToricCharts.CoordinateSpace 3) :=
  ToricCharts.changeOfCoordinates (transition s t) (transition t s)
    (by rw [transition_mul, transition_self]) (by rw [transition_mul, transition_self])

@[simp]
private theorem ToricFan.Triangle.chartChange_source (s t : ToricFan.Triangle) :
    (chartChange s t).source = ToricCharts.domain (transition s t) :=
  ToricCharts.overlap_eq_domain (transition_heightOne s t)
    (by rw [transition_mul, transition_self])

private theorem ToricFan.Triangle.chartChange_self_source (s : ToricFan.Triangle) :
    (chartChange s s).source = Set.univ := by
  rw [chartChange_source, transition_self]
  ext z
  simp only [ToricCharts.domain, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  intro i j h
  simp only [Matrix.one_apply] at h
  split_ifs at h <;> omega

@[simp]
private theorem ToricFan.Triangle.chartChange_self_apply (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) : chartChange s s z = z := by
  change ToricCharts.monomial (transition s s) z = z
  rw [transition_self, ToricCharts.monomial_one]

private theorem ToricFan.Triangle.chartChange_cocycle (r s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ (chartChange r s).source)
    (hsz : chartChange r s z ∈ (chartChange s t).source) :
    z ∈ (chartChange r t).source ∧ chartChange s t (chartChange r s z) = chartChange r t z := by
  rw [chartChange_source] at hz hsz ⊢
  have hm : z ∈ ToricCharts.overlap (transition r s) (transition s t) := ⟨hz, hsz⟩
  constructor
  · simpa only [transition_mul] using ToricCharts.domain_composition (transition_heightOne r s) hm
  · change
      ToricCharts.monomial (transition s t) (ToricCharts.monomial (transition r s) z) =
        ToricCharts.monomial (transition r t) z
    simpa only [Function.comp_apply, transition_mul] using
      ToricCharts.monomial_mul_on_overlap (transition_heightOne r s) hm

private theorem ToricFan.Triangle.chartChange_inter (r s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hs : z ∈ (chartChange r s).source)
    (ht : z ∈ (chartChange r t).source) : chartChange r s z ∈ (chartChange s t).source := by
  have hi : chartChange r s z ∈ (chartChange s r).source := (chartChange r s).map_source hs
  have hinv : chartChange s r (chartChange r s z) = z := (chartChange r s).left_inv hs
  exact (chartChange_cocycle s r t hi (by rwa [hinv])).1

private theorem ToricFan.Triangle.chartChange_holomorphic (s t : ToricFan.Triangle) :
    ContDiffOn ℂ ω (chartChange s t) (chartChange s t).source :=
  ToricCharts.changeOfCoordinates_holomorphic _ _ _ _

private def ToricFan.Triangle.time (z : ToricCharts.CoordinateSpace 3) : ℂ :=
  z 0 * z 1 * z 2

private theorem ToricFan.Triangle.time_holomorphic : ContDiff ℂ ω time := by
  exact ((contDiff_apply ℂ ℂ 0).mul (contDiff_apply ℂ ℂ 1)).mul (contDiff_apply ℂ ℂ 2)

private theorem ToricFan.Triangle.monomial_rays_height (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) : ToricCharts.monomial s.rays z 2 = time z := by
  simp [ToricCharts.monomial, rays_height, Fin.prod_univ_succ, time, mul_assoc]

private theorem ToricFan.Triangle.chartChange_preserves_time (s t : ToricFan.Triangle) :
    Set.EqOn (time ∘ chartChange s t) time (chartChange s t).source := by
  have h :
    Set.EqOn (time ∘ chartChange s t) time ((chartChange s t).source ∩ ToricCharts.torus) := by
    intro z hz
    change time (ToricCharts.monomial (transition s t) z) = time z
    have he := congrFun (ToricCharts.monomial_mul_on_torus t.rays (transition s t) hz.2) 2
    simpa only [transition_covariance, monomial_rays_height] using he
  refine
    h.of_subset_closure ?_ time_holomorphic.continuous.continuousOn Set.inter_subset_left
      (ToricCharts.torus_dense.open_subset_closure_inter (chartChange s t).open_source)
  exact time_holomorphic.continuous.comp_continuousOn (chartChange s t).continuousOn

private theorem ToricFan.Triangle.central_fibre (z : ToricCharts.CoordinateSpace 3) :
    time z = 0 ↔ z 0 = 0 ∨ z 1 = 0 ∨ z 2 = 0 := by simp [time, mul_eq_zero, or_assoc]

private abbrev ToricSpace.gluingCore : TopCat.GlueData.MkCore
    where
  J := ToricFan.Triangle
  U := fun _ => TopCat.of (ToricCharts.CoordinateSpace 3)
  V s
    t :=
    ⟨(ToricFan.Triangle.chartChange s t).source, (ToricFan.Triangle.chartChange s t).open_source⟩
  t s
    t :=
    TopCat.ofHom
      { toFun := fun z =>
          ⟨ToricFan.Triangle.chartChange s t z,
            (ToricFan.Triangle.chartChange s t).map_source z.2⟩
        continuous_toFun :=
          (ToricFan.Triangle.chartChange s t).continuousOn.domRestrict.subtype_mk _ }
  V_id
    s := by
    apply TopologicalSpace.Opens.ext
    exact ToricFan.Triangle.chartChange_self_source s
  t_id
    s := by
    funext z
    exact Subtype.ext (ToricFan.Triangle.chartChange_self_apply s z.1)
  t_inter := by
    intro r s t z hz
    exact ToricFan.Triangle.chartChange_inter r s t z.2 hz
  cocycle r s t z
    hz :=
    (ToricFan.Triangle.chartChange_cocycle r s t z.2
        (ToricFan.Triangle.chartChange_inter r s t z.2 hz)).2

private abbrev ToricSpace.gluing : TopCat.GlueData :=
  TopCat.GlueData.mk' gluingCore

private abbrev ToricSpace.Space :=
  gluing.toGlueData.glued

private def ToricSpace.inclusion (s : ToricFan.Triangle) : ToricCharts.CoordinateSpace 3 → Space :=
  gluing.toGlueData.ι s

private theorem ToricSpace.inclusion_openEmbedding (s : ToricFan.Triangle) :
    Topology.IsOpenEmbedding (ToricSpace.inclusion s) :=
  gluing.ι_isOpenEmbedding s

private theorem ToricSpace.inclusion_jointly_surjective (x : Space) :
    ∃ s z, ToricSpace.inclusion s z = x :=
  gluing.ι_jointly_surjective x

private theorem ToricSpace.inclusion_eq_iff (s t : ToricFan.Triangle)
    (z w : ToricCharts.CoordinateSpace 3) :
    ToricSpace.inclusion s z = ToricSpace.inclusion t w ↔
      z ∈ (ToricFan.Triangle.chartChange s t).source ∧ ToricFan.Triangle.chartChange s t z = w := by
  refine (gluing.ι_eq_iff_rel s t z w).trans ?_
  constructor
  · rintro ⟨⟨v, hv⟩, h1, h2⟩
    change v = z at h1
    change ToricFan.Triangle.chartChange s t v = w at h2
    subst v
    exact ⟨hv, h2⟩
  · rintro ⟨hz, he⟩
    exact ⟨⟨z, hz⟩, rfl, he⟩

private def ToricSpace.parametrization (s : ToricFan.Triangle) :
    OpenPartialHomeomorph (ToricCharts.CoordinateSpace 3) Space :=
  (inclusion_openEmbedding s).toOpenPartialHomeomorph (ToricSpace.inclusion s)

@[simp]
private theorem ToricSpace.parametrization_target (s : ToricFan.Triangle) :
    (parametrization s).target = Set.range (ToricSpace.inclusion s) := by simp [parametrization]

private theorem ToricSpace.parametrization_transition (s t : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3}
    (hz : ToricSpace.inclusion s z ∈ Set.range (ToricSpace.inclusion t)) :
    z ∈ (ToricFan.Triangle.chartChange s t).source ∧
      (parametrization t).symm (ToricSpace.inclusion s z) = ToricFan.Triangle.chartChange s t z :=
  by
  obtain ⟨w, hw⟩ := hz
  have he := (inclusion_eq_iff s t z w).mp hw.symm
  refine ⟨he.1, ?_⟩
  rw [← hw]
  exact ((inclusion_openEmbedding t).toOpenPartialHomeomorph_left_inv).trans he.2.symm

private def ToricSpace.preferredTriangle (x : Space) : ToricFan.Triangle :=
  (inclusion_jointly_surjective x).choose

private theorem ToricSpace.preferred_mem (x : Space) :
    x ∈ Set.range (ToricSpace.inclusion (preferredTriangle x)) :=
  (inclusion_jointly_surjective x).choose_spec

private instance ToricSpace.chartedSpace : ChartedSpace (ToricCharts.CoordinateSpace 3) Space
    where
  atlas := Set.range (fun s : ToricFan.Triangle => (parametrization s).symm)
  chartAt x := (parametrization (preferredTriangle x)).symm
  mem_chart_source
    x := by
    change x ∈ (parametrization (preferredTriangle x)).target
    rw [parametrization_target]
    exact preferred_mem x
  chart_mem_atlas x := Set.mem_range_self _

private theorem ToricSpace.transition_holomorphic (s t : ToricFan.Triangle) :
    ContDiffOn ℂ ω ((parametrization s).trans (parametrization t).symm)
      ((parametrization s).trans (parametrization t).symm).source := by
  have hparam (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    parametrization s z = ToricSpace.inclusion s z := rfl
  have h :
    ∀ z ∈ ((parametrization s).trans (parametrization t).symm).source,
      z ∈ (ToricFan.Triangle.chartChange s t).source ∧
        ((parametrization s).trans (parametrization t).symm) z =
          ToricFan.Triangle.chartChange s t z := by
    intro z hz
    exact parametrization_transition s t (by simpa [hparam] using hz.2)
  exact
    ((ToricFan.Triangle.chartChange_holomorphic s t).mono (fun z hz => (h z hz).1)).congr
      (fun z hz => (h z hz).2)

private instance ToricSpace.isManifold :
    IsManifold (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω Space := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨s, rfl⟩ := he
  obtain ⟨t, rfl⟩ := he'
  simpa using transition_holomorphic s t

private instance ToricSpace.secondCountableTopology : SecondCountableTopology Space := by
  let U : ToricFan.Triangle → Set Space := fun s => Set.range (ToricSpace.inclusion s)
  let (s : ToricFan.Triangle) : SecondCountableTopology (U s) :=
    (inclusion_openEmbedding s).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply
    TopologicalSpace.secondCountableTopology_of_countable_cover (U := U)
      (fun s => (inclusion_openEmbedding s).isOpen_range)
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  exact Set.mem_iUnion.mpr ⟨s, Set.mem_range_self z⟩

private def ToricSpace.time (x : Space) : ℂ :=
  ToricFan.Triangle.time ((parametrization (preferredTriangle x)).symm x)

@[simp]
private theorem
    ToricSpace.time_inclusion (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    time (ToricSpace.inclusion s z) = ToricFan.Triangle.time z := by
  change
    ToricFan.Triangle.time
        ((parametrization (preferredTriangle (ToricSpace.inclusion s z))).symm
          (ToricSpace.inclusion s z)) =
      ToricFan.Triangle.time z
  have h :=
    parametrization_transition s (preferredTriangle (ToricSpace.inclusion s z))
      (preferred_mem (ToricSpace.inclusion s z))
  rw [h.2]
  exact ToricFan.Triangle.chartChange_preserves_time _ _ h.1

private theorem ToricSpace.time_comp_parametrization (s : ToricFan.Triangle) :
    time ∘ parametrization s = ToricFan.Triangle.time := by
  funext z
  exact time_inclusion s z

private theorem ToricSpace.time_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) (modelWithCornersSelf ℂ ℂ)
      ω time := by
  intro x
  rw [contMDiffAt_iff_source]
  have hchart :
    chartAt (ToricCharts.CoordinateSpace 3) x = (parametrization (preferredTriangle x)).symm :=
    rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, time_comp_parametrization] using
    ToricFan.Triangle.time_holomorphic.contMDiff.contMDiffAt.contMDiffWithinAt (s := Set.univ)
      (x := (parametrization (preferredTriangle x)).symm x)

private def ToricSpace.referenceTriangle : ToricFan.Triangle :=
  ⟨0, 0, Bool.false⟩

private def ToricSpace.openTorus : Set Space :=
  ToricSpace.inclusion referenceTriangle '' ToricCharts.torus

private theorem ToricSpace.inclusion_torus_subset (s : ToricFan.Triangle) :
    ToricSpace.inclusion s '' ToricCharts.torus ⊆ openTorus := by
  rintro _ ⟨z, hz, rfl⟩
  refine
    ⟨ToricFan.Triangle.chartChange s referenceTriangle z, ToricCharts.monomial_mapsTo_torus _ hz,
      ?_⟩
  exact
    ((inclusion_eq_iff s referenceTriangle z _).mpr
        ⟨ToricCharts.torus_subset_overlap _ _ hz, rfl⟩).symm

private theorem ToricSpace.mem_openTorus_iff (x : Space) : x ∈ openTorus ↔ time x ≠ 0 := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [time_inclusion]
    exact mul_ne_zero (mul_ne_zero (hz 0) (hz 1)) (hz 2)
  · intro hx
    obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
    have hz : z ∈ ToricCharts.torus := by
      have h : (z 0 ≠ 0 ∧ z 1 ≠ 0) ∧ z 2 ≠ 0 := by
        simpa only [time_inclusion, ToricFan.Triangle.time, mul_ne_zero_iff] using hx
      intro i
      fin_cases i
      · exact h.1.1
      · exact h.1.2
      · exact h.2
    exact inclusion_torus_subset s ⟨z, hz, rfl⟩

private theorem ToricSpace.openTorus_isOpen : IsOpen openTorus := by
  have he : openTorus = {x | time x ≠ 0} := Set.ext mem_openTorus_iff
  rw [he]
  exact isOpen_ne_fun time_holomorphic.continuous continuous_const

private theorem ToricSpace.openTorus_dense : Dense openTorus := by
  intro x
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  apply closure_mono (inclusion_torus_subset s)
  exact
    mem_closure_image (inclusion_openEmbedding s).continuous.continuousAt
      (ToricCharts.torus_dense z)

private theorem ToricSpace.inclusion_holomorphic (s : ToricFan.Triangle) :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (ToricSpace.inclusion s) := by
  have he :
    (parametrization s).symm ∈
      IsManifold.maximalAtlas (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω Space :=
    IsManifold.subset_maximalAtlas (Set.mem_range_self s)
  have h := contMDiffOn_symm_of_mem_maximalAtlas he
  change
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (ToricSpace.inclusion s)
      Set.univ at h
  exact contMDiffOn_univ.mp h

private def
    ToricSpace.descend {Y : Type*} (f : ToricFan.Triangle → ToricCharts.CoordinateSpace 3 → Y)
    (x : Space) : Y :=
  f (preferredTriangle x) ((parametrization (preferredTriangle x)).symm x)

private theorem ToricSpace.descend_inclusion {Y : Type*}
    (f : ToricFan.Triangle → ToricCharts.CoordinateSpace 3 → Y)
    (h :
      ∀ s t z,
        z ∈ (ToricFan.Triangle.chartChange s t).source →
          f t (ToricFan.Triangle.chartChange s t z) = f s z)
    (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    descend f (ToricSpace.inclusion s z) = f s z := by
  change
    f (preferredTriangle (ToricSpace.inclusion s z))
        ((parametrization (preferredTriangle (ToricSpace.inclusion s z))).symm
          (ToricSpace.inclusion s z)) =
      f s z
  have he :=
    parametrization_transition s (preferredTriangle (ToricSpace.inclusion s z))
      (preferred_mem (ToricSpace.inclusion s z))
  rw [he.2]
  exact h _ _ _ he.1

private theorem
    ToricSpace.descend_holomorphic {F H Y : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y] (I : ModelWithCorners ℂ F H)
    (f : ToricFan.Triangle → ToricCharts.CoordinateSpace 3 → Y)
    (h :
      ∀ s t z,
        z ∈ (ToricFan.Triangle.chartChange s t).source →
          f t (ToricFan.Triangle.chartChange s t z) = f s z)
    (hf : ∀ s, ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) I ω (f s)) :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) I ω (descend f) := by
  have hcomp (s : ToricFan.Triangle) : descend f ∘ parametrization s = f s := by
    funext z
    exact descend_inclusion f h s z
  intro x
  rw [contMDiffAt_iff_source]
  have hchart :
    chartAt (ToricCharts.CoordinateSpace 3) x = (parametrization (preferredTriangle x)).symm :=
    rfl
  simpa [extChartAt, OpenPartialHomeomorph.extend, hchart, hcomp] using
    (hf (preferredTriangle x)).contMDiffAt.contMDiffWithinAt (s := Set.univ) (x :=
      (parametrization (preferredTriangle x)).symm x)

private theorem ToricSpace.contMDiffOn_of_comp_inclusion {F H Y : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] [TopologicalSpace H] [TopologicalSpace Y] [ChartedSpace H Y]
    (I : ModelWithCorners ℂ F H) (f : Space → Y) {U : Set Space} (hU : IsOpen U)
    (hf :
      ∀ s,
        ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) I ω
          (f ∘ ToricSpace.inclusion s) (ToricSpace.inclusion s ⁻¹' U)) :
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) I ω f U := by
  have hparam (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    parametrization s z = ToricSpace.inclusion s z := rfl
  intro x hx
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff_source]
  have he :
    ToricSpace.inclusion (preferredTriangle x) ((parametrization (preferredTriangle x)).symm x) =
      x :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv
      (ToricSpace.inclusion (preferredTriangle x)) (inclusion_openEmbedding _) (preferred_mem x)
  have hm :
    (parametrization (preferredTriangle x)).symm x ∈
      ToricSpace.inclusion (preferredTriangle x) ⁻¹' U := by
    change ToricSpace.inclusion _ _ ∈ U
    rwa [he]
  have hlocal :=
    (hf (preferredTriangle x)).contMDiffAt
      ((hU.preimage (inclusion_openEmbedding _).continuous).mem_nhds hm)
  have hchart :
    chartAt (ToricCharts.CoordinateSpace 3) x = (parametrization (preferredTriangle x)).symm :=
    rfl
  simpa [hparam, extChartAt, OpenPartialHomeomorph.extend, hchart, Function.comp_def] using
    hlocal.contMDiffWithinAt (s := Set.univ)

private def ToricSeparation.stripIndex (s : ToricFan.Triangle) : Fin 3 → ℤ :=
  ![s.a, s.b, s.a + s.b + if s.upper then 1 else 0]

private def ToricSeparation.pencil (k : Fin 3) (x : Fin 3 → ℤ) : ℤ :=
  ![x 0, x 1, x 0 + x 1] k

private def ToricSeparation.sign (a b : ℤ) : ℤ :=
  if a < b then -1 else if b < a then 1 else 0

private def ToricSeparation.stripValue (a b x : ℤ) : ℤ :=
  sign a b * (2 * x - a - b - 1)

private theorem ToricSeparation.sign_swap (a b : ℤ) : sign b a = -sign a b := by
  unfold sign
  split_ifs <;> omega

private theorem ToricSeparation.stripValue_nonneg {a b x : ℤ} (hx : a ≤ x ∧ x ≤ a + 1) :
    0 ≤ stripValue a b x := by
  unfold stripValue sign
  split_ifs <;> omega

private theorem ToricSeparation.stripValue_zero_bounds {a b x : ℤ} (hx : a ≤ x ∧ x ≤ a + 1)
    (hzero : stripValue a b x = 0) : b ≤ x ∧ x ≤ b + 1 := by
  unfold stripValue sign at hzero
  split_ifs at hzero <;> omega

private theorem ToricSeparation.ray_strip_bounds (s : ToricFan.Triangle) (j k : Fin 3) :
    stripIndex s k ≤ pencil k (fun i => s.rays i j) ∧
      pencil k (fun i => s.rays i j) ≤ stripIndex s k + 1 := by
  cases h : s.upper <;> fin_cases j <;> fin_cases k <;>
      simp [stripIndex, pencil, ToricFan.Triangle.rays, h] <;>
    omega

private theorem ToricSeparation.transition_nonneg_of_bounds (s t : ToricFan.Triangle) (j : Fin 3)
    (h :
      ∀ k,
        stripIndex t k ≤ pencil k (fun i => s.rays i j) ∧
          pencil k (fun i => s.rays i j) ≤ stripIndex t k + 1) :
    ∀ i, 0 ≤ ToricFan.Triangle.transition s t i j := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  intro i
  cases ht : t.upper <;> fin_cases i <;>
        simp [ToricFan.Triangle.transition, ToricFan.Triangle.dual, ht, Matrix.mul_apply,
          Fin.sum_univ_succ] <;>
      simp [stripIndex, pencil, ht] at h0 h1 h2 <;>
    omega

private def ToricSeparation.character (s t : ToricFan.Triangle) : Fin 3 → ℤ :=
  let e : Fin 3 → ℤ := fun k => sign (stripIndex s k) (stripIndex t k)
  ![2 * (e 0 + e 2), 2 * (e 1 + e 2),
    -(e 0 * (stripIndex s 0 + stripIndex t 0 + 1) + e 1 * (stripIndex s 1 + stripIndex t 1 + 1) +
        e 2 * (stripIndex s 2 + stripIndex t 2 + 1))]

private theorem ToricSeparation.character_swap (s t : ToricFan.Triangle) :
    character t s = -character s t := by
  have he (k : Fin 3) :
    sign (stripIndex t k) (stripIndex s k) = -sign (stripIndex s k) (stripIndex t k) :=
    sign_swap _ _
  unfold character
  simp only [he]
  ext i
  fin_cases i <;> dsimp <;> ring

private def ToricSeparation.exponents (s t : ToricFan.Triangle) : Fin 3 → ℤ :=
  character s t ᵥ* s.rays

private theorem ToricSeparation.exponents_eq_sum (s t : ToricFan.Triangle) (j : Fin 3) :
    exponents s t j =
      ∑ k, stripValue (stripIndex s k) (stripIndex t k) (pencil k (fun i => s.rays i j)) := by
  simp [exponents, character, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, stripValue, pencil]
  ring

private theorem ToricSeparation.exponents_nonneg (s t : ToricFan.Triangle) (j : Fin 3) :
    0 ≤ exponents s t j := by
  rw [exponents_eq_sum]
  exact Finset.sum_nonneg fun k _ => stripValue_nonneg (ray_strip_bounds s j k)

private theorem
    ToricSeparation.transition_nonneg_of_exponent_zero (s t : ToricFan.Triangle) (j : Fin 3)
    (hzero : exponents s t j = 0) : ∀ i, 0 ≤ ToricFan.Triangle.transition s t i j := by
  apply transition_nonneg_of_bounds s t j
  intro k
  apply stripValue_zero_bounds (ray_strip_bounds s j k)
  rw [exponents_eq_sum] at hzero
  exact
    (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => stripValue_nonneg (ray_strip_bounds s j k))).mp
      hzero k (Finset.mem_univ k)

private theorem
    ToricSeparation.exponents_pos_of_transition_neg (s t : ToricFan.Triangle) (i j : Fin 3)
    (hneg : ToricFan.Triangle.transition s t i j < 0) : 0 < exponents s t j := by
  have hn := exponents_nonneg s t j
  by_contra h
  have hz : exponents s t j = 0 := by omega
  exact (not_lt_of_ge (transition_nonneg_of_exponent_zero s t j hz i)) hneg

private theorem ToricSeparation.exponents_transition (s t : ToricFan.Triangle) :
    exponents t s ᵥ* ToricFan.Triangle.transition s t = -exponents s t := by
  rw [exponents, character_swap, Matrix.vecMul_vecMul, ToricFan.Triangle.transition_covariance]
  simp [exponents, Matrix.neg_vecMul]

private theorem ToricSeparation.exponents_cancel (s t : ToricFan.Triangle) (j : Fin 3) :
    exponents s t j + ∑ i, exponents t s i * ToricFan.Triangle.transition s t i j = 0 := by
  have h := congrFun (exponents_transition s t) j
  change (∑ i, exponents t s i * ToricFan.Triangle.transition s t i j) = -exponents s t j at h
  omega

private def ToricCharts.character (a : Fin 3 → ℤ) (z : CoordinateSpace 3) : ℂ :=
  ∏ j, z j ^ a j

private theorem ToricCharts.character_contDiff (a : Fin 3 → ℤ) (ha : ∀ j, 0 ≤ a j) (n : ℕ∞ω) :
    ContDiff ℂ n (character a) := by
  apply contDiff_prod
  intro j _
  have he :
    (fun z : CoordinateSpace 3 => z j ^ a j) = (fun z : CoordinateSpace 3 => z j ^ (a j).toNat) :=
    by
    funext z
    conv_lhs => rw [← Int.toNat_of_nonneg (ha j), zpow_natCast]
  rw [he]
  exact (contDiff_apply ℂ ℂ j).pow _

private theorem ToricCharts.characters_mul_on_torus (A : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℤ)
    (h : ∀ j, a j + ∑ i, b i * A i j = 0) {z : CoordinateSpace 3} (hz : z ∈ torus) :
    character a z * character b (monomial A z) = 1 := by
  have he := congrFun (monomial_mul_on_torus (fun _ j : Fin 3 => b j) A hz) 0
  change character b (monomial A z) = ∏ j, z j ^ ∑ i, b i * A i j at he
  rw [he]
  unfold character
  rw [← Finset.prod_mul_distrib]
  calc
    (∏ j, z j ^ a j * z j ^ ∑ i, b i * A i j) = ∏ _j : Fin 3, (1 : ℂ) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← zpow_add₀ (hz j), h j, zpow_zero]
    _ = 1 := by simp

private theorem
    ToricCharts.characters_mul_on_domain (A : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℤ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (h : ∀ j, a j + ∑ i, b i * A i j = 0) :
    Set.EqOn (fun z => character a z * character b (monomial A z)) (fun _ => 1) (domain A) := by
  have he :
    Set.EqOn (fun z => character a z * character b (monomial A z)) (fun _ => 1)
      (domain A ∩ torus) :=
    fun _ hz => characters_mul_on_torus A a b h hz.2
  refine
    he.of_subset_closure ?_ continuousOn_const Set.inter_subset_left
      (torus_dense.open_subset_closure_inter (domain_open A))
  exact
    (character_contDiff a ha 0).continuous.continuousOn.mul
      ((character_contDiff b hb 0).continuous.comp_continuousOn
        (monomial_contDiffOn A 0).continuousOn)

private def ToricCharts.overlapGraph (A : Matrix (Fin 3) (Fin 3) ℤ) :
    Set (CoordinateSpace 3 × CoordinateSpace 3) :=
  {p | p.1 ∈ domain A ∧ monomial A p.1 = p.2}

private theorem ToricCharts.overlapGraph_closed (A : Matrix (Fin 3) (Fin 3) ℤ) (a b : Fin 3 → ℤ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (hcancel : ∀ j, a j + ∑ i, b i * A i j = 0)
    (hpos : ∀ i j, A i j < 0 → 0 < a j) : IsClosed (overlapGraph A) := by
  let P : CoordinateSpace 3 × CoordinateSpace 3 → ℂ := fun p => character a p.1 * character b p.2
  have hP : Continuous P :=
    ((character_contDiff a ha 0).continuous.comp continuous_fst).mul
      ((character_contDiff b hb 0).continuous.comp continuous_snd)
  have hsubset : overlapGraph A ⊆ {p | P p = 1} := by
    intro p hp
    change character a p.1 * character b p.2 = 1
    rw [← hp.2]
    exact characters_mul_on_domain A a b ha hb hcancel hp.1
  apply isClosed_of_closure_subset
  intro p hp
  have hPeq : P p = 1 := closure_minimal hsubset (isClosed_eq hP continuous_const) hp
  have hD : p.1 ∈ domain A := by
    intro i j hij hz
    have hchar : character a p.1 = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hz, zero_zpow _ (ne_of_gt (hpos i j hij))]
    change character a p.1 * character b p.2 = 1 at hPeq
    simp [hchar] at hPeq
  refine ⟨hD, ?_⟩
  let : (𝓝[overlapGraph A] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hp
  have hf : ContinuousAt (fun q : CoordinateSpace 3 × CoordinateSpace 3 => monomial A q.1) p :=
    ((monomial_contDiffOn A 0).continuousOn.continuousAt ((domain_open A).mem_nhds hD)).comp
      continuous_fst.continuousAt
  have he :
    (fun q : CoordinateSpace 3 × CoordinateSpace 3 => monomial A q.1) =ᶠ[𝓝[overlapGraph A] p]
      Prod.snd := by
    filter_upwards [self_mem_nhdsWithin (s := overlapGraph A) (a := p)] with q hq
    exact hq.2
  exact
    tendsto_nhds_unique hf.continuousWithinAt
      (continuous_snd.continuousAt.continuousWithinAt.congr' he.symm)

private theorem ToricSpace.chart_overlap_graph_closed (s t : ToricFan.Triangle) :
    IsClosed (ToricCharts.overlapGraph (ToricFan.Triangle.transition s t)) :=
  ToricCharts.overlapGraph_closed (ToricFan.Triangle.transition s t)
    (ToricSeparation.exponents s t) (ToricSeparation.exponents t s)
    (ToricSeparation.exponents_nonneg s t) (ToricSeparation.exponents_nonneg t s)
    (ToricSeparation.exponents_cancel s t) (ToricSeparation.exponents_pos_of_transition_neg s t)

private instance ToricSpace.t2Space : T2Space Space := by
  constructor
  intro x y hxy
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨t, w, rfl⟩ := inclusion_jointly_surjective y
  have hn : (z, w) ∈ (ToricCharts.overlapGraph (ToricFan.Triangle.transition s t))ᶜ := by
    intro h
    apply hxy
    exact (inclusion_eq_iff s t z w).mpr ⟨by simpa using h.1, h.2⟩
  obtain ⟨U, V, hU, hV, hz, hw, hUV⟩ :=
    isOpen_prod_iff.mp (chart_overlap_graph_closed s t).isOpen_compl z w hn
  refine
    ⟨ToricSpace.inclusion s '' U, ToricSpace.inclusion t '' V,
      (inclusion_openEmbedding s).isOpenMap _ hU, (inclusion_openEmbedding t).isOpenMap _ hV,
      Set.mem_image_of_mem _ hz, Set.mem_image_of_mem _ hw, ?_⟩
  apply Set.disjoint_left.mpr
  rintro q ⟨u, hu, hsu⟩ ⟨v, hv, htv⟩
  have he := (inclusion_eq_iff s t u v).mp (hsu.trans htv.symm)
  exact hUV (show (u, v) ∈ U ×ˢ V from ⟨hu, hv⟩) ⟨by simpa using he.1, he.2⟩

private def ToricFan.Triangle.shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ) : ToricFan.Triangle :=
  ⟨s.a + v 0, s.b + v 1, s.upper⟩

@[simp]
private theorem ToricFan.Triangle.shift_zero (s : ToricFan.Triangle) : s.shift 0 = s := by
  ext <;> simp [shift]

private theorem ToricFan.Triangle.shift_add (s : ToricFan.Triangle) (v w : Fin 2 → ℤ) :
    (s.shift v).shift w = s.shift (v + w) := by ext <;> simp [shift, add_assoc]

private def ToricFan.Triangle.shear (v : Fin 2 → ℤ) : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 0, v 0; 0, 1, v 1; 0, 0, 1]

@[simp]
private theorem ToricFan.Triangle.shear_zero : shear 0 = 1 := by decide

private theorem
    ToricFan.Triangle.shear_add (v w : Fin 2 → ℤ) : shear v * shear w = shear (v + w) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem ToricFan.Triangle.rays_shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    (s.shift v).rays = shear v * s.rays := by
  ext i j
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
      simp [rays, shift, shear, hs, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem ToricFan.Triangle.dual_shift (s : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    (s.shift v).dual = s.dual * shear (-v) := by
  ext i j
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
      simp [dual, shift, shear, hs, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    ring

private theorem ToricFan.Triangle.transition_shift (s t : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    transition (s.shift v) (t.shift v) = transition s t := by
  rw [transition, dual_shift, rays_shift, Matrix.mul_assoc, ← Matrix.mul_assoc (shear (-v)),
    shear_add]
  simp [transition]

private theorem
    ToricFan.Triangle.chartChange_shift_source (s t : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    (chartChange (s.shift v) (t.shift v)).source = (chartChange s t).source := by
  simp [transition_shift]

private theorem ToricFan.Triangle.chartChange_shift_apply (s t : ToricFan.Triangle) (v : Fin 2 → ℤ)
    (z : ToricCharts.CoordinateSpace 3) :
    chartChange (s.shift v) (t.shift v) z = chartChange s t z := by
  change
    ToricCharts.monomial (transition (s.shift v) (t.shift v)) z =
      ToricCharts.monomial (transition s t) z
  rw [transition_shift]

private theorem ToricSpace.translation_compatible (v : Fin 2 → ℤ) (s t : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) (hz : z ∈ (ToricFan.Triangle.chartChange s t).source) :
    ToricSpace.inclusion (t.shift v) (ToricFan.Triangle.chartChange s t z) =
      ToricSpace.inclusion (s.shift v) z := by
  apply ((inclusion_eq_iff (s.shift v) (t.shift v) z _).mpr ?_).symm
  exact
    ⟨by simpa only [ToricFan.Triangle.chartChange_shift_source] using hz,
      ToricFan.Triangle.chartChange_shift_apply s t v z⟩

private def ToricSpace.translate (v : Fin 2 → ℤ) : Space → Space :=
  descend (fun s z => ToricSpace.inclusion (s.shift v) z)

@[simp]
private theorem ToricSpace.translate_inclusion (v : Fin 2 → ℤ) (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricSpace.translate v (ToricSpace.inclusion s z) = ToricSpace.inclusion (s.shift v) z :=
  descend_inclusion _ (translation_compatible v) s z

private theorem ToricSpace.translate_holomorphic (v : Fin 2 → ℤ) :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (ToricSpace.translate v) :=
  descend_holomorphic _ _ (translation_compatible v) (fun s => inclusion_holomorphic (s.shift v))

@[simp]
private theorem ToricSpace.translate_zero (x : Space) : ToricSpace.translate 0 x = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp

private theorem ToricSpace.translate_add (v w : Fin 2 → ℤ) (x : Space) :
    ToricSpace.translate v (ToricSpace.translate w x) = ToricSpace.translate (v + w) x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [ToricFan.Triangle.shift_add, add_comm v w]

private def ToricSpace.translationHomeomorph (v : Fin 2 → ℤ) : Space ≃ₜ Space
    where
  toFun := ToricSpace.translate v
  invFun := ToricSpace.translate (-v)
  left_inv x := by rw [ToricSpace.translate_add]; simp
  right_inv x := by rw [ToricSpace.translate_add]; simp
  continuous_toFun := (translate_holomorphic v).continuous
  continuous_invFun := (translate_holomorphic (-v)).continuous

@[simp]
private theorem ToricSpace.time_translate (v : Fin 2 → ℤ) (x : Space) :
    time (ToricSpace.translate v x) = time x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp

private abbrev ToricSpace.ActingTorus :=
  Fin 3 → ℂˣ

private def ToricSpace.factors (s : ToricFan.Triangle) (u : ActingTorus) :
    ToricCharts.CoordinateSpace 3 :=
  ToricCharts.monomial s.dual (fun j => (u j : ℂ))

private theorem ToricSpace.factors_nonzero (s : ToricFan.Triangle) (u : ActingTorus) (j : Fin 3) :
    factors s u j ≠ 0 :=
  ToricCharts.monomial_mapsTo_torus _ (fun i => (u i).ne_zero) j

private def ToricSpace.scale (s : ToricFan.Triangle) (u : ActingTorus)
    (z : ToricCharts.CoordinateSpace 3) : ToricCharts.CoordinateSpace 3 :=
  factors s u * z

private theorem ToricSpace.scale_holomorphic (s : ToricFan.Triangle) (u : ActingTorus) :
    ContDiff ℂ ω (scale s u) := by
  apply contDiff_pi.mpr
  intro j
  exact contDiff_const.mul (contDiff_apply ℂ ℂ j)

private theorem ToricSpace.scale_mem_source (s t : ToricFan.Triangle) (u : ActingTorus)
    (z : ToricCharts.CoordinateSpace 3) :
    scale s u z ∈ (ToricFan.Triangle.chartChange s t).source ↔
      z ∈ (ToricFan.Triangle.chartChange s t).source := by
  simp [ToricFan.Triangle.chartChange_source, ToricCharts.domain, scale, factors_nonzero]

private theorem ToricSpace.transition_factors (s t : ToricFan.Triangle) (u : ActingTorus) :
    ToricCharts.monomial (ToricFan.Triangle.transition s t) (factors s u) = factors t u := by
  have he : ToricFan.Triangle.transition s t * s.dual = t.dual := by
    rw [ToricFan.Triangle.transition, Matrix.mul_assoc, ToricFan.Triangle.rays_dual,
      Matrix.mul_one]
  change
    ToricCharts.monomial (ToricFan.Triangle.transition s t)
        (ToricCharts.monomial s.dual (fun j => (u j : ℂ))) =
      _
  rw [ToricCharts.monomial_mul_on_torus _ _ (fun j => (u j).ne_zero), he]
  rfl

private theorem ToricSpace.scale_transition (s t : ToricFan.Triangle) (u : ActingTorus)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricFan.Triangle.chartChange s t (scale s u z) =
      scale t u (ToricFan.Triangle.chartChange s t z) := by
  change
    ToricCharts.monomial (ToricFan.Triangle.transition s t) (factors s u * z) =
      factors t u * ToricCharts.monomial (ToricFan.Triangle.transition s t) z
  rw [ToricCharts.monomial_mul, transition_factors]

private theorem ToricSpace.action_compatible (u : ActingTorus) (s t : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) (hz : z ∈ (ToricFan.Triangle.chartChange s t).source) :
    ToricSpace.inclusion t (scale t u (ToricFan.Triangle.chartChange s t z)) =
      ToricSpace.inclusion s (scale s u z) := by
  exact
    ((inclusion_eq_iff s t _ _).mpr
        ⟨(scale_mem_source s t u z).mpr hz, scale_transition s t u z⟩).symm

private def ToricSpace.torusAction (u : ActingTorus) : Space → Space :=
  descend (fun s z => ToricSpace.inclusion s (scale s u z))

@[simp]
private theorem ToricSpace.torusAction_inclusion (u : ActingTorus) (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    torusAction u (ToricSpace.inclusion s z) = ToricSpace.inclusion s (scale s u z) :=
  descend_inclusion _ (action_compatible u) s z

private theorem ToricSpace.torusAction_holomorphic (u : ActingTorus) :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (torusAction u) :=
  descend_holomorphic _ _ (action_compatible u)
    (fun s => (inclusion_holomorphic s).comp (scale_holomorphic s u).contMDiff)

@[simp]
private theorem ToricSpace.factors_one (s : ToricFan.Triangle) : factors s 1 = 1 := by
  change ToricCharts.monomial s.dual 1 = 1
  exact ToricCharts.monomial_ones _

private theorem ToricSpace.factors_mul (s : ToricFan.Triangle) (u v : ActingTorus) :
    factors s (u * v) = factors s u * factors s v := by
  change ToricCharts.monomial s.dual ((fun j => (u j : ℂ)) * (fun j => (v j : ℂ))) = _
  exact ToricCharts.monomial_mul _ _ _

@[simp]
private theorem ToricSpace.scale_one (s : ToricFan.Triangle) (z : ToricCharts.CoordinateSpace 3) :
    scale s 1 z = z := by simp [scale]

private theorem ToricSpace.scale_mul (s : ToricFan.Triangle) (u v : ActingTorus)
    (z : ToricCharts.CoordinateSpace 3) : scale s u (scale s v z) = scale s (u * v) z := by
  simp [scale, factors_mul, mul_assoc]

@[simp]
private theorem ToricSpace.torusAction_one (x : Space) : torusAction 1 x = x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp

private theorem ToricSpace.torusAction_mul (u v : ActingTorus) (x : Space) :
    torusAction u (torusAction v x) = torusAction (u * v) x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [scale_mul]

private def ToricSpace.torusHomeomorph (u : ActingTorus) : Space ≃ₜ Space
    where
  toFun := torusAction u
  invFun := torusAction u⁻¹
  left_inv x := by rw [torusAction_mul]; simp
  right_inv x := by rw [torusAction_mul]; simp
  continuous_toFun := (torusAction_holomorphic u).continuous
  continuous_invFun := (torusAction_holomorphic u⁻¹).continuous

private theorem ToricSpace.time_factors (s : ToricFan.Triangle) (u : ActingTorus) :
    ToricFan.Triangle.time (factors s u) = u 2 := by
  have he := congrFun (ToricCharts.monomial_mul_on_torus s.rays s.dual (fun j => (u j).ne_zero)) 2
  simpa only [factors, ToricFan.Triangle.rays_dual, ToricCharts.monomial_one,
    ToricFan.Triangle.monomial_rays_height] using he

private theorem ToricSpace.time_scale (s : ToricFan.Triangle) (u : ActingTorus)
    (z : ToricCharts.CoordinateSpace 3) :
    ToricFan.Triangle.time (scale s u z) = (u 2 : ℂ) * ToricFan.Triangle.time z := by
  rw [← time_factors s u]
  simp [ToricFan.Triangle.time, scale]
  ring

private theorem ToricSpace.time_torusAction (u : ActingTorus) (x : Space) :
    time (torusAction u x) = (u 2 : ℂ) * time x := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [time_scale]

private def ToricSpace.fibreMultiplier (u : Fin 2 → ℂˣ) : ActingTorus :=
  ![u 0, u 1, 1]

@[simp]
private theorem ToricSpace.time_fibreMultiplier (u : Fin 2 → ℂˣ) (x : Space) :
    time (torusAction (fibreMultiplier u) x) = time x := by
  simp [time_torusAction, fibreMultiplier]

private theorem ToricSpace.shear_fibreMultiplier (v : Fin 2 → ℤ) (u : Fin 2 → ℂˣ) :
    ToricCharts.monomial (ToricFan.Triangle.shear v) (fun j => (fibreMultiplier u j : ℂ)) =
      (fun j => (fibreMultiplier u j : ℂ)) := by
  ext i
  fin_cases i <;>
    simp [ToricCharts.monomial, ToricFan.Triangle.shear, fibreMultiplier, Fin.prod_univ_succ]

private theorem ToricSpace.factors_shift_fibreMultiplier (s : ToricFan.Triangle) (v : Fin 2 → ℤ)
    (u : Fin 2 → ℂˣ) : factors (s.shift v) (fibreMultiplier u) = factors s (fibreMultiplier u) := by
  unfold factors
  rw [ToricFan.Triangle.dual_shift, ←
    ToricCharts.monomial_mul_on_torus s.dual (ToricFan.Triangle.shear (-v))
      (fun j => (fibreMultiplier u j).ne_zero),
    shear_fibreMultiplier]

private theorem ToricSpace.fibreMultiplier_translate (v : Fin 2 → ℤ) (u : Fin 2 → ℂˣ) (x : Space) :
    torusAction (fibreMultiplier u) (ToricSpace.translate v x) =
      ToricSpace.translate v (torusAction (fibreMultiplier u) x) := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  simp [scale, factors_shift_fibreMultiplier]

@[simp]
private theorem ToricSpace.fibreMultiplier_one : fibreMultiplier 1 = 1 := by
  ext i
  fin_cases i <;> simp [fibreMultiplier]

private theorem ToricSpace.fibreMultiplier_mul (u v : Fin 2 → ℂˣ) :
    fibreMultiplier (u * v) = fibreMultiplier u * fibreMultiplier v := by
  ext i
  fin_cases i <;> simp [fibreMultiplier]

private def ToricSpace.variableMultiplier (u : ℂ → Fin 2 → ℂˣ) (x : Space) : Space :=
  torusAction (fibreMultiplier (u (time x))) x

@[simp]
private theorem ToricSpace.variableMultiplier_inclusion (u : ℂ → Fin 2 → ℂˣ) (s : ToricFan.Triangle)
    (z : ToricCharts.CoordinateSpace 3) :
    variableMultiplier u (ToricSpace.inclusion s z) =
      ToricSpace.inclusion s (scale s (fibreMultiplier (u (ToricFan.Triangle.time z))) z) := by
  simp [variableMultiplier]

@[simp]
private theorem ToricSpace.time_variableMultiplier (u : ℂ → Fin 2 → ℂˣ) (x : Space) :
    time (variableMultiplier u x) = time x := by simp [variableMultiplier]

@[simp]
private theorem
    ToricSpace.variableMultiplier_one (x : Space) : variableMultiplier (fun _ => 1) x = x := by
  simp [variableMultiplier]

private theorem ToricSpace.variableMultiplier_mul (u v : ℂ → Fin 2 → ℂˣ) (x : Space) :
    variableMultiplier u (variableMultiplier v x) = variableMultiplier (fun t => u t * v t) x := by
  simp only [variableMultiplier, time_fibreMultiplier, torusAction_mul, fibreMultiplier_mul]

private theorem
    ToricSpace.variableMultiplier_translate (u : ℂ → Fin 2 → ℂˣ) (v : Fin 2 → ℤ) (x : Space) :
    variableMultiplier u (ToricSpace.translate v x) =
      ToricSpace.translate v (variableMultiplier u x) := by
  simp [variableMultiplier, fibreMultiplier_translate]

private theorem ToricSpace.varying_scale_holomorphic (s : ToricFan.Triangle) (u : ℂ → Fin 2 → ℂˣ)
    {D : Set ℂ} (hu : ∀ j, ContDiffOn ℂ ω (fun t => (u t j : ℂ)) D) :
    ContDiffOn ℂ ω (fun z => scale s (fibreMultiplier (u (ToricFan.Triangle.time z))) z)
      (ToricFan.Triangle.time ⁻¹' D) := by
  have hval :
    ContDiffOn ℂ ω
      (fun z : ToricCharts.CoordinateSpace 3 => fun j =>
        (fibreMultiplier (u (ToricFan.Triangle.time z)) j : ℂ))
      (ToricFan.Triangle.time ⁻¹' D) := by
    apply contDiffOn_pi.mpr
    intro j
    fin_cases j
    · exact (hu 0).comp ToricFan.Triangle.time_holomorphic.contDiffOn (fun _ hz => hz)
    · exact (hu 1).comp ToricFan.Triangle.time_holomorphic.contDiffOn (fun _ hz => hz)
    · exact contDiffOn_const
  have hfactors :
    ContDiffOn ℂ ω
      (fun z : ToricCharts.CoordinateSpace 3 =>
        factors s (fibreMultiplier (u (ToricFan.Triangle.time z))))
      (ToricFan.Triangle.time ⁻¹' D) :=
    (ToricCharts.monomial_contDiffOn s.dual ω).comp hval
      (fun z _ =>
        ToricCharts.torus_subset_domain _
          (fun j => (fibreMultiplier (u (ToricFan.Triangle.time z)) j).ne_zero))
  exact hfactors.mul contDiffOn_id

private theorem
    ToricSpace.variableMultiplier_holomorphic (u : ℂ → Fin 2 → ℂˣ) {D : Set ℂ} (hD : IsOpen D)
    (hu : ∀ j, ContDiffOn ℂ ω (fun t => (u t j : ℂ)) D) :
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (variableMultiplier u)
      (time ⁻¹' D) := by
  apply contMDiffOn_of_comp_inclusion _ _ (hD.preimage time_holomorphic.continuous)
  intro s
  have he :
    (variableMultiplier u ∘ ToricSpace.inclusion s) =
      (ToricSpace.inclusion s ∘ fun z =>
        scale s (fibreMultiplier (u (ToricFan.Triangle.time z))) z) := by
    funext z
    exact variableMultiplier_inclusion u s z
  rw [he]
  have hpre : ToricSpace.inclusion s ⁻¹' (time ⁻¹' D) = ToricFan.Triangle.time ⁻¹' D := by
    ext z
    simp
  rw [hpre]
  exact (inclusion_holomorphic s).comp_contMDiffOn (varying_scale_holomorphic s u hu).contMDiffOn

private def ToricSpace.cuspVector (v : Fin 2 → ℤ) : Fin 2 → ℤ :=
  ![v 1, -v 0]

@[simp]
private theorem ToricSpace.cuspVector_zero : cuspVector 0 = 0 := by ext i; fin_cases i <;> rfl

private theorem ToricSpace.cuspVector_add (v w : Fin 2 → ℤ) :
    cuspVector (v + w) = cuspVector v + cuspVector w := by
  ext i
  fin_cases i <;> simp [cuspVector, add_comm]

/-- The multiplicative torus factor obtained by exponentiating a period matrix. -/
public
def ToricSpace.exponentialMultiplier (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (t : ℂ) :
    Fin 2 → ℂˣ := fun j =>
  Units.mk0 (Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => (v i : ℂ))) j))
    (Complex.exp_ne_zero _)

@[simp]
private theorem ToricSpace.exponentialMultiplier_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    exponentialMultiplier C 0 t = 1 := by
  ext j
  simp [exponentialMultiplier, Matrix.mulVec, dotProduct]

private theorem
    ToricSpace.exponentialMultiplier_add (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 2 → ℤ)
    (t : ℂ) :
    exponentialMultiplier C (v + w) t =
      exponentialMultiplier C v t * exponentialMultiplier C w t := by
  have he : (fun i => ((v + w) i : ℂ)) = (fun i => (v i : ℂ)) + (fun i => (w i : ℂ)) := by
    ext i
    simp
  ext j
  change
    Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => ((v + w) i : ℂ))) j) =
      Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => (v i : ℂ))) j) *
        Complex.exp (2 * Real.pi * Complex.I * ((C t) *ᵥ (fun i => (w i : ℂ))) j)
  rw [he, Matrix.mulVec_add]
  simp only [Pi.add_apply, mul_add, Complex.exp_add]

private theorem ToricSpace.exponentialMultiplier_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {D : Set ℂ} (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) D) (j : Fin 2) :
    ContDiffOn ℂ ω (fun t => (exponentialMultiplier C v t j : ℂ)) D := by
  apply ContDiffOn.cexp
  apply contDiffOn_const.mul
  change ContDiffOn ℂ ω (fun t => ∑ i, C t j i * (v i : ℂ)) D
  apply ContDiffOn.sum
  intro i _
  exact (hC j i).mul contDiffOn_const

private def
    ToricSpace.twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ) (x : Space) :
    Space :=
  variableMultiplier (exponentialMultiplier C v) (ToricSpace.translate (cuspVector v) x)

@[simp]
private theorem ToricSpace.time_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    (x : Space) : time (twistedTranslate C v x) = time x := by simp [twistedTranslate]

@[simp]
private theorem ToricSpace.twistedTranslate_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (x : Space) :
    twistedTranslate C 0 x = x := by
  have he : exponentialMultiplier C 0 = (fun _ => 1) := funext (exponentialMultiplier_zero C)
  simp [twistedTranslate, he]

private theorem ToricSpace.twistedTranslate_add (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 2 → ℤ)
    (x : Space) : twistedTranslate C v (twistedTranslate C w x) = twistedTranslate C (v + w) x := by
  simp only [twistedTranslate]
  rw [← variableMultiplier_translate, ToricSpace.translate_add, variableMultiplier_mul]
  have he :
    (fun t => exponentialMultiplier C v t * exponentialMultiplier C w t) =
      exponentialMultiplier C (v + w) :=
    funext fun t => (exponentialMultiplier_add C v w t).symm
  rw [he, cuspVector_add]

private theorem
    ToricSpace.twistedTranslate_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    {D : Set ℂ} (hD : IsOpen D) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) D) :
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (twistedTranslate C v)
      (time ⁻¹' D) := by
  exact
    (variableMultiplier_holomorphic _ hD (exponentialMultiplier_holomorphic C v hC)).comp
      (translate_holomorphic (cuspVector v)).contMDiffOn (fun x hx => by simpa using hx)

private def ToricSpace.tubeOpen (D : TopologicalSpace.Opens ℂ) : TopologicalSpace.Opens Space :=
  ⟨time ⁻¹' (D : Set ℂ), D.isOpen.preimage time_holomorphic.continuous⟩

private abbrev ToricSpace.Tube (D : TopologicalSpace.Opens ℂ) :=
  tubeOpen D

private def
    ToricSpace.tubeTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (D : TopologicalSpace.Opens ℂ)
    (v : Fin 2 → ℤ) (x : Tube D) : Tube D :=
  ⟨twistedTranslate C v x, by
    change time (twistedTranslate C v x) ∈ D
    rw [time_twistedTranslate]
    exact x.2⟩

@[instance_reducible]
private def
    ToricSpace.tubeAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (D : TopologicalSpace.Opens ℂ) :
    MulAction (Multiplicative (Fin 2 → ℤ)) (Tube D)
    where
  smul v x := tubeTranslate C D v.toAdd x
  one_smul x := Subtype.ext (twistedTranslate_zero C x)
  mul_smul v w x := Subtype.ext (twistedTranslate_add C v.toAdd w.toAdd x).symm

private theorem ToricSpace.tubeTranslate_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (D : TopologicalSpace.Opens ℂ) (v : Fin 2 → ℤ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (D : Set ℂ)) :
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (tubeTranslate C D v) := by
  intro x
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
        (fun y : Tube D => (tubeTranslate C D v y : Space)) x ↔
      ContMDiffAt (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
        (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (tubeTranslate C D v) x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  change
    ContMDiffAt (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (fun y : Tube D => twistedTranslate C v (y : Space)) x
  apply (contMDiffAt_subtype_iff (U := tubeOpen D) (f := twistedTranslate C v)).mpr
  exact
    (twistedTranslate_holomorphic C v D.isOpen hC).contMDiffAt ((tubeOpen D).isOpen.mem_nhds x.2)

private def ToricSpace.torusCoordinates (x : Space) : ToricCharts.CoordinateSpace 3 :=
  ToricCharts.monomial (preferredTriangle x).rays ((parametrization (preferredTriangle x)).symm x)

private theorem ToricSpace.torusCoordinates_inclusion (s : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ ToricCharts.torus) :
    torusCoordinates (ToricSpace.inclusion s z) = ToricCharts.monomial s.rays z := by
  have he :=
    parametrization_transition s (preferredTriangle (ToricSpace.inclusion s z))
      (preferred_mem (ToricSpace.inclusion s z))
  unfold torusCoordinates
  rw [he.2]
  change
    ToricCharts.monomial (preferredTriangle (ToricSpace.inclusion s z)).rays
        (ToricCharts.monomial
          (ToricFan.Triangle.transition s (preferredTriangle (ToricSpace.inclusion s z))) z) =
      _
  rw [ToricCharts.monomial_mul_on_torus _ _ hz, ToricFan.Triangle.transition_covariance]

@[simp]
private theorem ToricSpace.torusCoordinates_time (x : Space) : torusCoordinates x 2 = time x :=
  ToricFan.Triangle.monomial_rays_height _ _

private theorem ToricSpace.torusCoordinates_nonzero {x : Space} (hx : x ∈ openTorus) (i : Fin 3) :
    torusCoordinates x i ≠ 0 := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [torusCoordinates_inclusion _ hz]
  exact ToricCharts.monomial_mapsTo_torus _ hz i

private theorem ToricSpace.inclusion_preimage_openTorus (s : ToricFan.Triangle) :
    ToricSpace.inclusion s ⁻¹' openTorus = ToricCharts.torus := by
  ext z
  simp [mem_openTorus_iff, ToricFan.Triangle.time, ToricCharts.torus, Fin.forall_fin_succ,
    and_assoc]

private theorem ToricSpace.torusCoordinates_holomorphic :
    ContMDiffOn (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω torusCoordinates openTorus := by
  apply contMDiffOn_of_comp_inclusion _ _ openTorus_isOpen
  intro s
  rw [inclusion_preimage_openTorus]
  exact
    ((ToricCharts.monomial_contDiffOn s.rays ω).mono
          (ToricCharts.torus_subset_domain _)).contMDiffOn.congr
      (fun z hz => torusCoordinates_inclusion s hz)

private theorem
    ToricSpace.torusCoordinates_translate (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (ToricSpace.translate v x) =
      ToricCharts.monomial (ToricFan.Triangle.shear v) (torusCoordinates x) := by
  obtain ⟨z, hz, rfl⟩ := hx
  rw [translate_inclusion, torusCoordinates_inclusion _ hz, torusCoordinates_inclusion _ hz,
    ToricFan.Triangle.rays_shift]
  exact (ToricCharts.monomial_mul_on_torus _ _ hz).symm

private theorem ToricSpace.monomial_rays_factors (s : ToricFan.Triangle) (u : ActingTorus) :
    ToricCharts.monomial s.rays (factors s u) = (fun j => (u j : ℂ)) := by
  rw [factors, ToricCharts.monomial_mul_on_torus _ _ (fun j => (u j).ne_zero),
    ToricFan.Triangle.rays_dual, ToricCharts.monomial_one]

private theorem
    ToricSpace.torusCoordinates_action (u : ActingTorus) {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (torusAction u x) = (fun j => (u j : ℂ)) * torusCoordinates x := by
  obtain ⟨z, hz, rfl⟩ := hx
  have hs : scale referenceTriangle u z ∈ ToricCharts.torus := fun j =>
    mul_ne_zero (factors_nonzero _ _ j) (hz j)
  rw [torusAction_inclusion, torusCoordinates_inclusion _ hs, torusCoordinates_inclusion _ hz]
  rw [scale, ToricCharts.monomial_mul, monomial_rays_factors]

private theorem ToricSpace.torusCoordinates_variableMultiplier (u : ℂ → Fin 2 → ℂˣ) {x : Space}
    (hx : x ∈ openTorus) :
    torusCoordinates (variableMultiplier u x) =
      (fun j => (fibreMultiplier (u (time x)) j : ℂ)) * torusCoordinates x :=
  torusCoordinates_action _ hx

private theorem ToricSpace.torusCoordinates_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) :
    torusCoordinates (twistedTranslate C v x) =
      (fun j => (fibreMultiplier (exponentialMultiplier C v (time x)) j : ℂ)) *
        ToricCharts.monomial (ToricFan.Triangle.shear (cuspVector v)) (torusCoordinates x) := by
  have ht : ToricSpace.translate (cuspVector v) x ∈ openTorus := by
    simpa only [mem_openTorus_iff, time_translate] using hx
  rw [twistedTranslate, torusCoordinates_variableMultiplier _ ht, time_translate,
    torusCoordinates_translate _ hx]

private theorem
    ToricSpace.torusCoordinates_twistedTranslate_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (i : Fin 2) :
    torusCoordinates (twistedTranslate C v x) i.castSucc =
      (exponentialMultiplier C v (time x) i : ℂ) * (time x) ^ cuspVector v i *
        torusCoordinates x i.castSucc := by
  rw [torusCoordinates_twistedTranslate C v hx]
  fin_cases i <;>
    simp [ToricCharts.monomial, ToricFan.Triangle.shear, fibreMultiplier, Fin.prod_univ_succ,
      mul_comm, mul_left_comm, mul_assoc]

private def
    ToricSpace.logNorm (z : ToricCharts.CoordinateSpace 3) : Fin 3 → ℝ := fun i => Real.log ‖z i‖

private theorem ToricSpace.logNorm_monomial (A : Matrix (Fin 3) (Fin 3) ℤ)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ ToricCharts.torus) :
    logNorm (ToricCharts.monomial A z) = A.map (Int.castRingHom ℝ) *ᵥ logNorm z := by
  ext i
  change Real.log ‖∏ j, z j ^ A i j‖ = ∑ j, (A i j : ℝ) * Real.log ‖z j‖
  rw [norm_prod, Real.log_prod (fun j _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hz j)))]
  simp [norm_zpow, Real.log_zpow]

private def ToricSpace.logCoordinates (x : Space) : Fin 3 → ℝ :=
  logNorm (torusCoordinates x)

private theorem ToricSpace.logCoordinates_inclusion (s : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ ToricCharts.torus) :
    logCoordinates (ToricSpace.inclusion s z) = s.rays.map (Int.castRingHom ℝ) *ᵥ logNorm z := by
  rw [logCoordinates, torusCoordinates_inclusion s hz, logNorm_monomial _ hz]

@[simp]
private theorem
    ToricSpace.logCoordinates_time (x : Space) : logCoordinates x 2 = Real.log ‖time x‖ := by
  simp [logCoordinates, logNorm]

private theorem ToricSpace.logNorm_sum (s : ToricFan.Triangle) {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) : ∑ j, logNorm z j = Real.log ‖ToricFan.Triangle.time z‖ := by
  have he := congrFun (logCoordinates_inclusion s hz) 2
  simpa [Matrix.mulVec, dotProduct, logCoordinates_time] using he.symm

/-- The real drift matrix determined by imaginary parts of the period correction. -/
public
def ToricSpace.driftMatrix (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => -2 * Real.pi * (C t i j).im

private theorem ToricSpace.exponentialMultiplier_log_norm (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) (t : ℂ) (i : Fin 2) :
    Real.log ‖(exponentialMultiplier C v t i : ℂ)‖ =
      (driftMatrix C t *ᵥ (fun j => (v j : ℝ))) i := by
  simp [exponentialMultiplier, Complex.norm_exp, driftMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, Complex.mul_re, Complex.mul_im]
  ring

private theorem ToricSpace.logCoordinates_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (i : Fin 2) :
    logCoordinates (twistedTranslate C v x) i.castSucc =
      logCoordinates x i.castSucc + Real.log ‖time x‖ * (cuspVector v i : ℝ) +
        (driftMatrix C (time x) *ᵥ (fun j => (v j : ℝ))) i := by
  have ht : time x ≠ 0 := (mem_openTorus_iff x).mp hx
  have hu : ‖(exponentialMultiplier C v (time x) i : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (exponentialMultiplier C v (time x) i).ne_zero
  have hp : ‖(time x) ^ cuspVector v i‖ ≠ 0 := norm_ne_zero_iff.mpr (zpow_ne_zero _ ht)
  have hz : ‖torusCoordinates x i.castSucc‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (torusCoordinates_nonzero hx _)
  simp only [logCoordinates, logNorm, torusCoordinates_twistedTranslate_apply C v hx, norm_mul]
  rw [Real.log_mul (mul_ne_zero hu hp) hz, Real.log_mul hu hp, exponentialMultiplier_log_norm,
    norm_zpow, Real.log_zpow]
  ring

private def ToricSpace.position (x : Space) : Fin 2 → ℝ := fun i =>
  logCoordinates x i.castSucc / Real.log ‖time x‖

private theorem
    ToricSpace.position_twistedTranslate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ ≠ 0) (i : Fin 2) :
    position (twistedTranslate C v x) i =
      position x i + (cuspVector v i : ℝ) +
        (driftMatrix C (time x) *ᵥ (fun j => (v j : ℝ))) i / Real.log ‖time x‖ := by
  simp only [position, time_twistedTranslate, logCoordinates_twistedTranslate C v hx]
  field_simp

private def ToricSpace.latticeReal (v : Fin 2 → ℤ) : Fin 2 → ℝ := fun i => (v i : ℝ)

private theorem ToricSpace.norm_latticeReal (v : Fin 2 → ℤ) : ‖latticeReal v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact (Int.norm_cast_real (v i)).le.trans (norm_le_pi_norm v i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    rw [← Int.norm_cast_real (v i)]
    exact norm_le_pi_norm (latticeReal v) i

private theorem ToricSpace.lattice_bounded_finite (R : ℝ) :
    {v : Fin 2 → ℤ | ‖latticeReal v‖ ≤ R}.Finite := by
  have he : {v : Fin 2 → ℤ | ‖latticeReal v‖ ≤ R} = Metric.closedBall 0 R := by
    ext v
    simp [norm_latticeReal, Metric.mem_closedBall, dist_zero_right]
  rw [he]
  exact (ProperSpace.isCompact_closedBall _ _).finite_of_discrete

/-- The sup norm of the entries of a real two-by-two matrix. -/
public
def ToricSpace.entryNorm (A : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  ‖fun i : Fin 2 => fun j : Fin 2 => A i j‖

private theorem ToricSpace.entryNorm_nonneg (A : Matrix (Fin 2) (Fin 2) ℝ) : 0 ≤ entryNorm A :=
  norm_nonneg _

private theorem ToricSpace.norm_cuspVector (v : Fin 2 → ℤ) :
    ‖latticeReal (cuspVector v)‖ = ‖latticeReal v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm (latticeReal v) 1
    · simpa [latticeReal, cuspVector] using norm_le_pi_norm (latticeReal v) 0
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simpa [latticeReal, cuspVector] using norm_le_pi_norm (latticeReal (cuspVector v)) 1
    · exact norm_le_pi_norm (latticeReal (cuspVector v)) 0

private theorem ToricSpace.norm_matrix_mulVec_le (A : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → ℝ) :
    ‖A *ᵥ v‖ ≤ 2 * entryNorm A * ‖v‖ := by
  have hA := entryNorm_nonneg A
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  calc
    ‖(A *ᵥ v) i‖ ≤ ∑ j, ‖A i j * v j‖ := by
      change ‖∑ j, A i j * v j‖ ≤ _
      exact norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, entryNorm A * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact
        mul_le_mul
          ((norm_le_pi_norm (A i) j).trans
            (norm_le_pi_norm (fun k : Fin 2 => fun l : Fin 2 => A k l) i))
          (norm_le_pi_norm v j) (norm_nonneg _) (norm_nonneg _)
    _ = 2 * entryNorm A * ‖v‖ := by simp; ring

private theorem ToricSpace.position_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ ≠ 0) :
    position (twistedTranslate C v x) - position x =
      latticeReal (cuspVector v) +
        (Real.log ‖time x‖)⁻¹ • (driftMatrix C (time x) *ᵥ latticeReal v) := by
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [position_twistedTranslate C v hx ht]
  simp only [latticeReal, div_eq_mul_inv, Matrix.mulVec, dotProduct]
  ring

private theorem
    ToricSpace.lattice_bound_of_small_drift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℤ)
    {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ < 0)
    (hR : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    ‖latticeReal v‖ ≤ 2 * ‖position (twistedTranslate C v x) - position x‖ := by
  let e := (Real.log ‖time x‖)⁻¹ • (driftMatrix C (time x) *ᵥ latticeReal v)
  have hneg : 0 < -Real.log ‖time x‖ := neg_pos.mpr ht
  have he : ‖e‖ ≤ ‖latticeReal v‖ / 2 := by
    calc
      ‖e‖ = (-Real.log ‖time x‖)⁻¹ * ‖driftMatrix C (time x) *ᵥ latticeReal v‖ := by
        simp only [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_neg ht]
      _ ≤ (-Real.log ‖time x‖)⁻¹ * (2 * entryNorm (driftMatrix C (time x)) * ‖latticeReal v‖) :=
        (mul_le_mul_of_nonneg_left (norm_matrix_mulVec_le _ _) (by positivity))
      _ ≤ (-Real.log ‖time x‖)⁻¹ * (2 * (-Real.log ‖time x‖ / 4) * ‖latticeReal v‖) := by gcongr
      _ = ‖latticeReal v‖ / 2 := by field_simp [ht.ne]; ring
  have htriangle := norm_add_le (latticeReal (cuspVector v) + e) (-e)
  have hnorm :
    ‖latticeReal (cuspVector v) + e‖ = ‖position (twistedTranslate C v x) - position x‖ := by
    rw [position_displacement C v hx ht.ne]
  simp only [add_neg_cancel_right, norm_neg, norm_cuspVector] at htriangle
  rw [hnorm] at htriangle
  linarith

private def ToricSpace.barycentric (z : ToricCharts.CoordinateSpace 3) : Fin 3 → ℝ := fun j =>
  logNorm z j / Real.log ‖ToricFan.Triangle.time z‖

private theorem
    ToricSpace.barycentric_sum (s : ToricFan.Triangle) {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) (ht : Real.log ‖ToricFan.Triangle.time z‖ ≠ 0) :
    ∑ j, barycentric z j = 1 := by
  simp only [barycentric, ← Finset.sum_div, logNorm_sum s hz, div_self ht]

private theorem
    ToricSpace.position_inclusion (s : ToricFan.Triangle) {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) (i : Fin 2) :
    position (ToricSpace.inclusion s z) i = ∑ j, (s.rays i.castSucc j : ℝ) * barycentric z j := by
  simp only [position, time_inclusion, logCoordinates_inclusion s hz, Matrix.mulVec, dotProduct,
    barycentric, Finset.sum_div, mul_div_assoc]
  rfl

private def ToricSpace.chartSize (s : ToricFan.Triangle) : ℝ :=
  ‖(s.a : ℝ)‖ + ‖(s.b : ℝ)‖ + 1

private theorem ToricSpace.chartSize_pos (s : ToricFan.Triangle) : 0 < chartSize s := by
  unfold chartSize
  positivity

private theorem ToricSpace.ray_norm_le_chartSize (s : ToricFan.Triangle) (i : Fin 2) (j : Fin 3) :
    ‖(s.rays i.castSucc j : ℝ)‖ ≤ chartSize s := by
  have ha : ‖(s.a : ℝ)‖ ≤ chartSize s := by unfold chartSize; linarith [norm_nonneg (s.b : ℝ)]
  have hb : ‖(s.b : ℝ)‖ ≤ chartSize s := by unfold chartSize; linarith [norm_nonneg (s.a : ℝ)]
  have ha' : ‖(s.a : ℝ) + 1‖ ≤ chartSize s := (norm_add_le _ _).trans (by simp [chartSize])
  have hb' : ‖(s.b : ℝ) + 1‖ ≤ chartSize s := (norm_add_le _ _).trans (by simp [chartSize])
  cases hs : s.upper <;> fin_cases i <;> fin_cases j <;>
    first
    | simpa [ToricFan.Triangle.rays, hs] using ha
    | simpa [ToricFan.Triangle.rays, hs] using hb
    | simpa [ToricFan.Triangle.rays, hs] using ha'
    | simpa [ToricFan.Triangle.rays, hs] using hb'

private theorem ToricSpace.barycentric_lower_bound {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε < 1)
    (ht : ‖ToricFan.Triangle.time z‖ < ε) (hzS : ∀ j, ‖z j‖ ≤ S) (j : Fin 3) :
    -(Real.log S / (-Real.log ε)) ≤ barycentric z j := by
  have hn : ToricFan.Triangle.time z ≠ 0 := mul_ne_zero (mul_ne_zero (hz 0) (hz 1)) (hz 2)
  have hlogε : Real.log ε < 0 := Real.log_neg hε hε1
  have hlogt : Real.log ‖ToricFan.Triangle.time z‖ < Real.log ε :=
    Real.log_lt_log (norm_pos_iff.mpr hn) ht
  have hη : 0 ≤ Real.log S / (-Real.log ε) :=
    div_nonneg (Real.log_nonneg hS) (neg_nonneg.mpr hlogε.le)
  have hlogz : Real.log ‖z j‖ ≤ Real.log S := Real.log_le_log (norm_pos_iff.mpr (hz j)) (hzS j)
  have hmul := mul_le_mul_of_nonpos_left hlogt.le (neg_nonpos.mpr hη)
  have he : -(Real.log S / (-Real.log ε)) * Real.log ε = Real.log S := by field_simp [hlogε.ne]
  rw [he] at hmul
  exact (le_div_iff_of_neg (hlogt.trans hlogε)).mpr (hlogz.trans hmul)

private theorem ToricSpace.barycentric_norm_bound {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε < 1)
    (ht : ‖ToricFan.Triangle.time z‖ < ε) (hzS : ∀ j, ‖z j‖ ≤ S) (j : Fin 3) :
    ‖barycentric z j‖ ≤ 1 + 2 * (Real.log S / (-Real.log ε)) := by
  let η := Real.log S / (-Real.log ε)
  have hη : 0 ≤ η := div_nonneg (Real.log_nonneg hS) (neg_nonneg.mpr (Real.log_neg hε hε1).le)
  have hlow (k : Fin 3) : -η ≤ barycentric z k := barycentric_lower_bound hz hS hε hε1 ht hzS k
  have hn : ToricFan.Triangle.time z ≠ 0 := mul_ne_zero (mul_ne_zero (hz 0) (hz 1)) (hz 2)
  have hs :=
    barycentric_sum referenceTriangle hz (Real.log_neg (norm_pos_iff.mpr hn) (ht.trans hε1)).ne
  have hsum : ∑ k : Fin 3, (barycentric z k + η) = 1 + 3 * η := by
    rw [Finset.sum_add_distrib, hs]
    simp
  have hu :=
    Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin 3 => barycentric z k + η)
      (fun k _ => by linarith [hlow k]) (Finset.mem_univ j)
  rw [hsum] at hu
  change ‖barycentric z j‖ ≤ 1 + 2 * η
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hlow j]

private def ToricSpace.positionBound (s : ToricFan.Triangle) (S ε : ℝ) : ℝ :=
  3 * chartSize s * (1 + 2 * (Real.log S / (-Real.log ε)))

private theorem
    ToricSpace.position_norm_bound (s : ToricFan.Triangle) {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) {S ε : ℝ} (hS : 1 ≤ S) (hε : 0 < ε) (hε1 : ε < 1)
    (ht : ‖ToricFan.Triangle.time z‖ < ε) (hzS : ∀ j, ‖z j‖ ≤ S) :
    ‖position (ToricSpace.inclusion s z)‖ ≤ positionBound s S ε := by
  have hη : 0 ≤ Real.log S / (-Real.log ε) :=
    div_nonneg (Real.log_nonneg hS) (neg_nonneg.mpr (Real.log_neg hε hε1).le)
  have hsize := chartSize_pos s
  apply (pi_norm_le_iff_of_nonneg (by unfold positionBound; positivity)).mpr
  intro i
  rw [position_inclusion s hz]
  calc
    ‖∑ j, (s.rays i.castSucc j : ℝ) * barycentric z j‖ ≤
        ∑ j, ‖(s.rays i.castSucc j : ℝ) * barycentric z j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin 3, chartSize s * (1 + 2 * (Real.log S / (-Real.log ε))) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact
        mul_le_mul (ray_norm_le_chartSize s i j) (barycentric_norm_bound hz hS hε hε1 ht hzS j)
          (norm_nonneg _) (chartSize_pos s).le
    _ = positionBound s S ε := by simp [positionBound]; ring

/-- The logarithmic bound required of a period correction near the cusp. -/
public
def ToricSpace.SmallDrift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) : Prop :=
  ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ε → entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4

private def ToricSpace.chartNeighbourhood (s : ToricFan.Triangle) (n : ℕ) (ε : ℝ) : Set Space :=
  ToricSpace.inclusion s ''
    {z : ToricCharts.CoordinateSpace 3 |
      (∀ j, ‖z j‖ < (n : ℝ) + 2) ∧ ‖ToricFan.Triangle.time z‖ < ε}

private theorem ToricSpace.chartNeighbourhood_open (s : ToricFan.Triangle) (n : ℕ) (ε : ℝ) :
    IsOpen (chartNeighbourhood s n ε) := by
  apply (inclusion_openEmbedding s).isOpenMap
  have hc : IsOpen {z : ToricCharts.CoordinateSpace 3 | ∀ j, ‖z j‖ < (n : ℝ) + 2} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (continuous_apply j).norm continuous_const
  exact hc.inter (isOpen_lt ToricFan.Triangle.time_holomorphic.continuous.norm continuous_const)

private theorem
    ToricSpace.chartNeighbourhood_time {s : ToricFan.Triangle} {n : ℕ} {ε : ℝ} {x : Space}
    (hx : x ∈ chartNeighbourhood s n ε) : ‖time x‖ < ε := by
  obtain ⟨z, hz, rfl⟩ := hx
  simpa only [time_inclusion] using hz.2

private theorem ToricSpace.chartNeighbourhood_cover {ε : ℝ} {x : Space} (hx : ‖time x‖ < ε) :
    ∃ s n, x ∈ chartNeighbourhood s n ε := by
  obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨n, hn⟩ := exists_nat_gt ‖z‖
  refine ⟨s, n, z, ⟨?_, by simpa using hx⟩, rfl⟩
  intro j
  have h := norm_le_pi_norm z j
  linarith

private def ToricSpace.chartTranslates (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s t : ToricFan.Triangle) (n m : ℕ) : Set (Fin 2 → ℤ) :=
  {v | (chartNeighbourhood s n ε ∩ twistedTranslate C v ⁻¹' chartNeighbourhood t m ε).Nonempty}

private theorem
    ToricSpace.chartTranslates_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) (s t : ToricFan.Triangle) (n m : ℕ) :
    (chartTranslates C ε s t n m).Finite := by
  apply
    (lattice_bounded_finite
        (2 * (positionBound s ((n : ℝ) + 2) ε + positionBound t ((m : ℝ) + 2) ε))).subset
  intro v hv
  have hcont : ContinuousOn (twistedTranslate C v) (chartNeighbourhood s n ε) :=
    (twistedTranslate_holomorphic C v Metric.isOpen_ball hC).continuousOn.mono
      (by
        intro x hx
        simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using
          chartNeighbourhood_time hx)
  have hV :=
    hcont.isOpen_inter_preimage (chartNeighbourhood_open s n ε) (chartNeighbourhood_open t m ε)
  obtain ⟨p, hpT, hpV⟩ := openTorus_dense.exists_mem_open hV hv
  obtain ⟨z, hz, rfl⟩ := hpV.1
  have hzT : z ∈ ToricCharts.torus := by
    rw [← inclusion_preimage_openTorus s]
    exact hpT
  obtain ⟨w, hw, hew⟩ := hpV.2
  have hwT : w ∈ ToricCharts.torus := by
    rw [← inclusion_preimage_openTorus t]
    change ToricSpace.inclusion t w ∈ openTorus
    rw [hew, mem_openTorus_iff, time_twistedTranslate]
    exact (mem_openTorus_iff _).mp hpT
  have ht : 0 < ‖time (ToricSpace.inclusion s z)‖ :=
    norm_pos_iff.mpr ((mem_openTorus_iff _).mp hpT)
  have htime : ‖time (ToricSpace.inclusion s z)‖ < ε := by simpa only [time_inclusion] using hz.2
  have hvbound :=
    lattice_bound_of_small_drift C v hpT (Real.log_neg ht (htime.trans hε1)) (hR _ ht htime)
  have hpbound :=
    position_norm_bound s hzT
      (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith : (1 : ℝ) ≤ n + 2) hε hε1 hz.2
      (fun j => (hz.1 j).le)
  have hqbound :=
    position_norm_bound t hwT
      (by have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m; linarith : (1 : ℝ) ≤ m + 2) hε hε1 hw.2
      (fun j => (hw.1 j).le)
  rw [hew] at hqbound
  have hd :=
    norm_sub_le (position (twistedTranslate C v (ToricSpace.inclusion s z)))
      (position (ToricSpace.inclusion s z))
  change ‖latticeReal v‖ ≤ _
  linarith

private theorem ToricSpace.compact_translates_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) {K : Set Space} (hK : IsCompact K) (hKt : ∀ x ∈ K, ‖time x‖ < ε) :
    {v : Fin 2 → ℤ | (twistedTranslate C v '' K ∩ K).Nonempty}.Finite := by
  let U : ToricFan.Triangle × ℕ → Set Space := fun i => chartNeighbourhood i.1 i.2 ε
  have hcover : K ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨s, n, hn⟩ := chartNeighbourhood_cover (hKt x hx)
    exact Set.mem_iUnion.mpr ⟨(s, n), hn⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover U (fun i => chartNeighbourhood_open _ _ _) hcover
  have hfinite : (⋃ i ∈ I, ⋃ j ∈ I, chartTranslates C ε i.1 j.1 i.2 j.2).Finite :=
    I.finite_toSet.biUnion fun i _ =>
      I.finite_toSet.biUnion fun j _ => chartTranslates_finite C hε hε1 hC hR i.1 j.1 i.2 j.2
  apply hfinite.subset
  rintro v ⟨q, ⟨p, hp, hpq⟩, hq⟩
  obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp (hI hp)
  obtain ⟨j, hj, hqj⟩ := Set.mem_iUnion₂.mp (hI hq)
  apply Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
  apply Set.mem_iUnion₂.mpr ⟨j, hj, ?_⟩
  exact ⟨p, hpi, by simpa only [Set.mem_preimage, hpq] using hqj⟩

private theorem ToricSpace.SmallDrift.mono {C : ℂ → Matrix (Fin 2) (Fin 2) ℂ} {ε δ : ℝ}
    (h : ToricSpace.SmallDrift C ε) (hδε : δ ≤ ε) : ToricSpace.SmallDrift C δ := fun t ht hδ =>
  h t ht (hδ.trans_le hδε)

private theorem ToricSpace.exists_smallDrift_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (hC : ∀ i j, ContinuousAt (fun t => C t i j) 0) : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ SmallDrift C ε := by
  have hentries :
    ContinuousAt (fun t : ℂ => fun i : Fin 2 => fun j : Fin 2 => driftMatrix C t i j) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact continuousAt_const.mul (Complex.continuous_im.continuousAt.comp (hC i j))
  have hnorm : ContinuousAt (fun t => entryNorm (driftMatrix C t)) 0 := hentries.norm
  let M := entryNorm (driftMatrix C 0) + 1
  have hM : entryNorm (driftMatrix C 0) < M := by dsimp [M]; linarith
  have hevent : ∀ᶠ t in 𝓝 (0 : ℂ), entryNorm (driftMatrix C t) < M := hnorm (gt_mem_nhds hM)
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp hevent
  let ε := Min.min δ (Min.min (1 / 2) (Real.exp (-4 * M)))
  have hε : 0 < ε := lt_min hδ (lt_min (by norm_num) (Real.exp_pos _))
  refine ⟨ε, hε, lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num), ?_⟩
  intro t ht htε
  have htδ : Dist.dist t 0 < δ := by
    simpa only [dist_zero_right] using htε.trans_le (min_le_left _ _)
  have hbound := hδbound htδ
  have hlog : Real.log ‖t‖ ≤ -4 * M := by
    have hsmall : ‖t‖ ≤ Real.exp (-4 * M) :=
      htε.le.trans ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [Real.log_exp] using Real.log_le_log ht hsmall
  linarith

private abbrev CuspQuotient.LatticeGroup :=
  Multiplicative (Fin 2 → ℤ)

private def CuspQuotient.disc (ε : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 ε, Metric.isOpen_ball⟩

private instance CuspQuotient.tube_locallyCompactSpace (ε : ℝ) :
    LocallyCompactSpace (ToricSpace.Tube (disc ε)) :=
  ChartedSpace.locallyCompactSpace (ToricCharts.CoordinateSpace 3) (ToricSpace.Tube (disc ε))

private theorem CuspQuotient.continuous_action (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    letI := ToricSpace.tubeAction C (disc ε)
    ContinuousConstSMul LatticeGroup (ToricSpace.Tube (disc ε)) := by
  let := ToricSpace.tubeAction C (disc ε)
  exact ⟨fun v => (ToricSpace.tubeTranslate_holomorphic C (disc ε) v.toAdd hC).continuous⟩

private theorem CuspQuotient.proper_action (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := ToricSpace.tubeAction C (disc ε)
    ProperlyDiscontinuousSMul LatticeGroup (ToricSpace.Tube (disc ε)) := by
  let := ToricSpace.tubeAction C (disc ε)
  constructor
  intro K L hK hL
  let K' : Set ToricSpace.Space := Subtype.val '' (K ∪ L)
  have hK' : IsCompact K' := (hK.union hL).image continuous_subtype_val
  have hKt : ∀ x ∈ K', ‖ToricSpace.time x‖ < ε := by
    rintro _ ⟨x, _, rfl⟩
    have hx : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  have hfinite := ToricSpace.compact_translates_finite C hε hε1 hC hR hK' hKt
  have hinj : Function.Injective (fun g : LatticeGroup => g.toAdd) := fun _ _ h =>
    congrArg Multiplicative.ofAdd h
  apply (hfinite.preimage hinj.injOn).subset
  rintro g ⟨q, ⟨p, hp, hpq⟩, hq⟩
  refine
    ⟨(q : ToricSpace.Space), ⟨(p : ToricSpace.Space), ⟨p, Or.inl hp, rfl⟩, ?_⟩,
      ⟨q, Or.inr hq, rfl⟩⟩
  exact congrArg Subtype.val hpq

private theorem CuspQuotient.free_action (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := ToricSpace.tubeAction C (disc ε)
    IsCancelSMul LatticeGroup (ToricSpace.Tube (disc ε)) := by
  let := ToricSpace.tubeAction C (disc ε)
  let := proper_action C ε hε hε1 hC hR
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g x hg
  let H := MulAction.stabilizer LatticeGroup x
  let : Finite H := ProperlyDiscontinuousSMul.finite_stabilizer x
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_of_finite (⟨g, hg⟩ : H)).exists_pow_eq_one
  have he : g ^ n = 1 := congrArg Subtype.val hpow
  exact (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, he⟩).eq_one'

private def CuspQuotient.relation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Setoid (ToricSpace.Tube (disc ε)) :=
  letI := ToricSpace.tubeAction C (disc ε)
  MulAction.orbitRel LatticeGroup (ToricSpace.Tube (disc ε))

private abbrev CuspQuotient.QuotientSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  Quotient (relation C ε)

private def CuspQuotient.quotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    ToricSpace.Tube (disc ε) → QuotientSpace C ε :=
  Quotient.mk (relation C ε)

private theorem CuspQuotient.quotientMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (quotientMap C ε) :=
  continuous_quotient_mk'

@[simp]
private theorem CuspQuotient.quotientMap_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (v : Fin 2 → ℤ) (x : ToricSpace.Tube (disc ε)) :
    quotientMap C ε (ToricSpace.tubeTranslate C (disc ε) v x) = quotientMap C ε x := by
  let := ToricSpace.tubeAction C (disc ε)
  exact MulAction.orbitRel.Quotient.quotient_smul_eq (g := Multiplicative.ofAdd v) (a := x)

private def
    CuspQuotient.projection (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) : QuotientSpace C ε → ℂ :=
  Quotient.lift (fun x : ToricSpace.Tube (disc ε) => ToricSpace.time (x : ToricSpace.Space))
    (by
      let := ToricSpace.tubeAction C (disc ε)
      intro x y h
      change x ∈ MulAction.orbit LatticeGroup y at h
      obtain ⟨g, rfl⟩ := h
      exact ToricSpace.time_twistedTranslate C g.toAdd y)

@[simp]
private theorem CuspQuotient.projection_quotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (x : ToricSpace.Tube (disc ε)) :
    projection C ε (quotientMap C ε x) = ToricSpace.time (x : ToricSpace.Space) :=
  rfl

private theorem CuspQuotient.projection_mem_disc (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (x : QuotientSpace C ε) : projection C ε x ∈ disc ε := by
  induction x using Quotient.inductionOn with
  | h x => exact x.2

private def
    CuspQuotient.baseMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (x : QuotientSpace C ε) :
    disc ε :=
  ⟨projection C ε x, projection_mem_disc C ε x⟩

private theorem CuspQuotient.projection_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (projection C ε) :=
  (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val).quotient_lift _

private theorem CuspQuotient.baseMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Continuous (baseMap C ε) :=
  (projection_continuous C ε).subtype_mk _

private theorem
    CuspQuotient.quotientMap_covering (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := ToricSpace.tubeAction C (disc ε)
    IsQuotientCoveringMap (quotientMap C ε) LatticeGroup := by
  let := ToricSpace.tubeAction C (disc ε)
  let := continuous_action C ε hC
  let := proper_action C ε hε hε1 hC hR
  let := free_action C ε hε hε1 hC hR
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

private theorem
    CuspQuotient.quotient_t2Space (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : T2Space (QuotientSpace C ε) := by
  let := ToricSpace.tubeAction C (disc ε)
  let := continuous_action C ε hC
  let := proper_action C ε hε hε1 hC hR
  change T2Space (Quotient (MulAction.orbitRel LatticeGroup (ToricSpace.Tube (disc ε))))
  infer_instance

@[instance_reducible]
private def CuspQuotient.chartedSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    ChartedSpace (ToricCharts.CoordinateSpace 3) (QuotientSpace C ε) :=
  letI := ToricSpace.tubeAction C (disc ε)
  CoveringQuotient.chartedSpace (E := ToricCharts.CoordinateSpace 3)
    (quotientMap_covering C ε hε hε1 hC hR)

private theorem CuspQuotient.isManifold (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    IsManifold (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (QuotientSpace C ε) := by
  let := ToricSpace.tubeAction C (disc ε)
  exact
    CoveringQuotient.isManifold (E := ToricCharts.CoordinateSpace 3)
      (quotientMap_covering C ε hε hε1 hC hR) ω
      (fun v => ToricSpace.tubeTranslate_holomorphic C (disc ε) v.toAdd hC)

private theorem CuspQuotient.quotientMap_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (quotientMap C ε) := by
  let := ToricSpace.tubeAction C (disc ε)
  exact
    CoveringQuotient.contMDiff_project (E := ToricCharts.CoordinateSpace 3)
      (quotientMap_covering C ε hε hε1 hC hR) ω
      (fun v => ToricSpace.tubeTranslate_holomorphic C (disc ε) v.toAdd hC)

private theorem CuspQuotient.exists_admissible_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {r : ℝ}
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < r ∧
          ε < 1 ∧
            ToricSpace.SmallDrift C ε ∧
              ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε) := by
  have hC0 : ∀ i j, ContinuousAt (fun z => C z i j) 0 := by
    intro i j
    exact (hC i j).continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (by simpa using hr))
  obtain ⟨δ, hδ, hδ1, hR⟩ := ToricSpace.exists_smallDrift_radius C hC0
  refine
    ⟨Min.min δ (r / 2), lt_min hδ (half_pos hr), (min_le_right _ _).trans_lt (half_lt_self hr),
      (min_le_left _ _).trans_lt hδ1, hR.mono (min_le_left _ _), ?_⟩
  intro i j
  exact (hC i j).mono (Metric.ball_subset_ball ((min_le_right _ _).trans (half_le_self hr.le)))

private abbrev ToricFan.Triangle.RealCoordinates :=
  Fin 3 → ℝ

private def ToricFan.Triangle.coordinates (s : ToricFan.Triangle) :
    RealCoordinates →ₗ[ℝ] RealCoordinates :=
  (s.dual.map (Int.castRingHom ℝ)).mulVecLin

private def
    ToricFan.Triangle.generate (s : ToricFan.Triangle) : RealCoordinates →ₗ[ℝ] RealCoordinates :=
  (s.rays.map (Int.castRingHom ℝ)).mulVecLin

private theorem ToricFan.Triangle.coordinates_lower (a b : ℤ) (x : RealCoordinates) :
    coordinates ⟨a, b, Bool.false⟩ x =
      ![(1 + (a : ℝ) + b) * x 2 - x 0 - x 1, x 0 - a * x 2, x 1 - b * x 2] := by
  ext i
  fin_cases i <;> simp [coordinates, dual, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem ToricFan.Triangle.coordinates_upper (a b : ℤ) (x : RealCoordinates) :
    coordinates ⟨a, b, Bool.true⟩ x =
      ![((b : ℝ) + 1) * x 2 - x 1, ((a : ℝ) + 1) * x 2 - x 0,
        x 0 + x 1 - (1 + (a : ℝ) + b) * x 2] := by
  ext i
  fin_cases i <;> simp [coordinates, dual, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring

private theorem
    ToricFan.Triangle.coordinates_generate (s : ToricFan.Triangle) (x : RealCoordinates) :
    s.coordinates (s.generate x) = x := by
  change (s.dual.map (Int.castRingHom ℝ)) *ᵥ ((s.rays.map (Int.castRingHom ℝ)) *ᵥ x) = x
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, dual_rays]
  simp

private def ToricFan.Triangle.cone (s : ToricFan.Triangle) : ConvexCone ℝ RealCoordinates
    where
  carrier := {x | ∀ i, 0 ≤ s.coordinates x i}
  smul_mem' := by
    intro c hc x hx i
    simpa using mul_nonneg hc.le (hx i)
  add_mem' := by
    intro x hx y hy i
    simpa using add_nonneg (hx i) (hy i)

@[simp]
private theorem ToricFan.Triangle.mem_cone (s : ToricFan.Triangle) (x : RealCoordinates) :
    x ∈ s.cone ↔ ∀ i, 0 ≤ s.coordinates x i :=
  Iff.rfl

private def ToricSpace.realCuspVector : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ)
    where
  toFun v := ![v 1, -v 0]
  map_add' v w := by ext i; fin_cases i <;> simp [add_comm]
  map_smul' a v := by ext i; fin_cases i <;> simp

private theorem ToricSpace.realCuspVector_latticeReal (v : Fin 2 → ℤ) :
    realCuspVector (latticeReal v) = latticeReal (cuspVector v) := by
  ext i
  fin_cases i <;> simp [realCuspVector, latticeReal, cuspVector]

private theorem ToricSpace.realCuspVector_norm (v : Fin 2 → ℝ) : ‖realCuspVector v‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 1
    · simpa [realCuspVector] using norm_le_pi_norm v 0
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simpa [realCuspVector] using norm_le_pi_norm (realCuspVector v) 1
    · exact norm_le_pi_norm (realCuspVector v) 0

private def ToricSpace.displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
  realCuspVector + (Real.log ‖t‖)⁻¹ • (driftMatrix C t).mulVecLin

private theorem ToricSpace.displacement_error_bound (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (v : Fin 2 → ℝ) : ‖displacement C t v - realCuspVector v‖ ≤ ‖v‖ / 2 := by
  have hneg : 0 < -Real.log ‖t‖ := neg_pos.mpr ht
  have he : displacement C t v - realCuspVector v = (Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ v) := by
    simp [displacement]
  rw [he]
  calc
    ‖(Real.log ‖t‖)⁻¹ • (driftMatrix C t *ᵥ v)‖ = (-Real.log ‖t‖)⁻¹ * ‖driftMatrix C t *ᵥ v‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_neg ht]
    _ ≤ (-Real.log ‖t‖)⁻¹ * (2 * entryNorm (driftMatrix C t) * ‖v‖) :=
      (mul_le_mul_of_nonneg_left (norm_matrix_mulVec_le _ _) (by positivity))
    _ ≤ (-Real.log ‖t‖)⁻¹ * (2 * (-Real.log ‖t‖ / 4) * ‖v‖) := by gcongr
    _ = ‖v‖ / 2 := by field_simp [ht.ne]; ring

private theorem ToricSpace.displacement_lower_bound (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (v : Fin 2 → ℝ) : ‖v‖ ≤ 2 * ‖displacement C t v‖ := by
  have he := displacement_error_bound C ht hR v
  have htri := norm_sub_le (displacement C t v) (displacement C t v - realCuspVector v)
  rw [sub_sub_cancel, realCuspVector_norm] at htri
  linarith

private theorem ToricSpace.displacement_upper_bound (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4)
    (v : Fin 2 → ℝ) : ‖displacement C t v‖ ≤ 3 / 2 * ‖v‖ := by
  have he := displacement_error_bound C ht hR v
  have htri := norm_add_le (realCuspVector v) (displacement C t v - realCuspVector v)
  rw [add_sub_cancel, realCuspVector_norm] at htri
  linarith

private theorem ToricSpace.displacement_bijective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {t : ℂ}
    (ht : Real.log ‖t‖ < 0) (hR : entryNorm (driftMatrix C t) ≤ -Real.log ‖t‖ / 4) :
    Function.Bijective (displacement C t) := by
  have hinj : Function.Injective (displacement C t) := by
    apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    have hb := displacement_lower_bound C ht hR v
    rw [hv, norm_zero, MulZeroClass.mul_zero] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  exact ⟨hinj, LinearMap.surjective_of_injective hinj⟩

private theorem ToricSpace.exists_integer_rounding (u : Fin 2 → ℝ) :
    ∃ v : Fin 2 → ℤ, ‖u + latticeReal v‖ ≤ 1 := by
  refine ⟨fun i => -⌊u i⌋, ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  simp only [Pi.add_apply, latticeReal, Int.cast_neg, Real.norm_eq_abs]
  rw [abs_le]
  constructor <;> linarith [Int.floor_le (u i), Int.lt_floor_add_one (u i)]

private theorem ToricSpace.position_twistedTranslate_displacement (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (v : Fin 2 → ℤ) {x : Space} (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ ≠ 0) :
    position (twistedTranslate C v x) = position x + displacement C (time x) (latticeReal v) := by
  have he := position_displacement C v hx ht
  rw [← realCuspVector_latticeReal] at he
  change
    position (twistedTranslate C v x) - position x = displacement C (time x) (latticeReal v) at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

private theorem ToricSpace.exists_bounded_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {x : Space}
    (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ < 0)
    (hR : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    ∃ v : Fin 2 → ℤ, ‖position (twistedTranslate C v x)‖ ≤ 2 := by
  obtain ⟨u, hu⟩ := (displacement_bijective C ht hR).surjective (position x)
  obtain ⟨v, hv⟩ := exists_integer_rounding u
  refine ⟨v, ?_⟩
  rw [position_twistedTranslate_displacement C v hx ht.ne, ← hu, ← map_add]
  exact (displacement_upper_bound C ht hR _).trans (by nlinarith)

private theorem
    ToricSpace.exists_torus_chart (s : ToricFan.Triangle) {x : Space} (hx : x ∈ openTorus) :
    ∃ z ∈ ToricCharts.torus, ToricSpace.inclusion s z = x := by
  obtain ⟨z, hz, rfl⟩ := hx
  refine
    ⟨ToricFan.Triangle.chartChange referenceTriangle s z, ToricCharts.monomial_mapsTo_torus _ hz,
      ?_⟩
  exact
    ((inclusion_eq_iff referenceTriangle s z _).mpr
        ⟨ToricCharts.torus_subset_overlap _ _ hz, rfl⟩).symm

private def ToricSpace.positionPoint (y : Fin 2 → ℝ) : ToricFan.Triangle.RealCoordinates :=
  ![y 0, y 1, 1]

private theorem ToricSpace.generate_barycentric (s : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ ToricCharts.torus)
    (ht : Real.log ‖ToricFan.Triangle.time z‖ ≠ 0) :
    s.generate (barycentric z) = positionPoint (position (ToricSpace.inclusion s z)) := by
  ext i
  fin_cases i
  · exact (position_inclusion s hz 0).symm
  · exact (position_inclusion s hz 1).symm
  · simpa [ToricFan.Triangle.generate, Matrix.mulVec, dotProduct, positionPoint] using
      barycentric_sum s hz ht

private theorem ToricSpace.unit_chart_of_position_mem_cone (s : ToricFan.Triangle)
    {z : ToricCharts.CoordinateSpace 3} (hz : z ∈ ToricCharts.torus)
    (ht : Real.log ‖ToricFan.Triangle.time z‖ < 0)
    (hp : positionPoint (position (ToricSpace.inclusion s z)) ∈ s.cone) : ‖z‖ ≤ 1 := by
  rw [← generate_barycentric s hz ht.ne, ToricFan.Triangle.mem_cone,
    ToricFan.Triangle.coordinates_generate] at hp
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro j
  apply (Real.log_nonpos_iff (norm_nonneg _)).mp
  have hj := (le_div_iff_of_neg ht).mp (hp j)
  simpa [barycentric, logNorm] using hj

private def ToricSpace.boundedTriangles : Set ToricFan.Triangle :=
  {s | (-3 ≤ s.a ∧ s.a ≤ 3) ∧ (-3 ≤ s.b ∧ s.b ≤ 3)}

private theorem ToricSpace.boundedTriangles_finite : boundedTriangles.Finite := by
  have hf :=
    (Set.finite_Icc (-3 : ℤ) 3).prod
      ((Set.finite_Icc (-3 : ℤ) 3).prod (Set.finite_univ (α := Bool)))
  have hi : Function.Injective (fun s : ToricFan.Triangle => (s.a, s.b, s.upper)) := by
    intro s t h
    simpa only [Prod.mk.injEq, ToricFan.Triangle.ext_iff, and_assoc] using h
  apply (hf.preimage hi.injOn).subset
  intro s hs
  exact ⟨hs.1, hs.2, Set.mem_univ _⟩

private theorem ToricSpace.exists_bounded_cone (y : Fin 2 → ℝ) (hy : ‖y‖ ≤ 2) :
    ∃ s ∈ boundedTriangles, positionPoint y ∈ s.cone := by
  let a := ⌊y 0⌋
  let b := ⌊y 1⌋
  have ha : (a : ℝ) ≤ y 0 := Int.floor_le _
  have hb : (b : ℝ) ≤ y 1 := Int.floor_le _
  have ha' : y 0 < (a : ℝ) + 1 := Int.lt_floor_add_one _
  have hb' : y 1 < (b : ℝ) + 1 := Int.lt_floor_add_one _
  have hy0 : -(2 : ℝ) ≤ y 0 ∧ y 0 ≤ 2 :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y 0).trans hy)
  have hy1 : -(2 : ℝ) ≤ y 1 ∧ y 1 ≤ 2 :=
    abs_le.mp (by simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y 1).trans hy)
  have haI : (-3 : ℤ) ≤ a ∧ a ≤ 3 := by
    constructor
    · exact_mod_cast (show (-3 : ℝ) ≤ (a : ℝ) by linarith)
    · exact_mod_cast (show (a : ℝ) ≤ 3 by linarith)
  have hbI : (-3 : ℤ) ≤ b ∧ b ≤ 3 := by
    constructor
    · exact_mod_cast (show (-3 : ℝ) ≤ (b : ℝ) by linarith)
    · exact_mod_cast (show (b : ℝ) ≤ 3 by linarith)
  by_cases hsum : y 0 + y 1 ≤ 1 + (a : ℝ) + b
  · refine ⟨⟨a, b, Bool.false⟩, ⟨haI, hbI⟩, ?_⟩
    rw [ToricFan.Triangle.mem_cone, ToricFan.Triangle.coordinates_lower]
    intro i
    fin_cases i <;> dsimp [positionPoint] <;> linarith
  · refine ⟨⟨a, b, Bool.true⟩, ⟨haI, hbI⟩, ?_⟩
    rw [ToricFan.Triangle.mem_cone, ToricFan.Triangle.coordinates_upper]
    intro i
    fin_cases i <;> dsimp [positionPoint] <;> linarith

private theorem ToricSpace.exists_unit_chart_of_bounded_position {x : Space} (hx : x ∈ openTorus)
    (ht : Real.log ‖time x‖ < 0) (hp : ‖position x‖ ≤ 2) :
    ∃ s ∈ boundedTriangles,
      ∃ z ∈ Metric.closedBall (0 : ToricCharts.CoordinateSpace 3) 1,
        ToricSpace.inclusion s z = x := by
  obtain ⟨s, hs, hp⟩ := exists_bounded_cone (position x) hp
  obtain ⟨z, hz, rfl⟩ := exists_torus_chart s hx
  refine ⟨s, hs, z, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact unit_chart_of_position_mem_cone s hz (by simpa using ht) hp

private theorem
    ToricSpace.exists_bounded_chart_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) {x : Space}
    (hx : x ∈ openTorus) (ht : Real.log ‖time x‖ < 0)
    (hR : entryNorm (driftMatrix C (time x)) ≤ -Real.log ‖time x‖ / 4) :
    ∃ v : Fin 2 → ℤ,
      ∃ s ∈ boundedTriangles,
        ∃ z ∈ Metric.closedBall (0 : ToricCharts.CoordinateSpace 3) 1,
          ToricSpace.inclusion s z = twistedTranslate C v x := by
  obtain ⟨v, hv⟩ := exists_bounded_translate C hx ht hR
  refine ⟨v, ?_⟩
  apply exists_unit_chart_of_bounded_position _ (by simpa using ht) hv
  simpa only [mem_openTorus_iff, time_twistedTranslate] using hx

private def CuspQuotient.compactRepresentatives (η : ℝ) : Set ToricSpace.Space :=
  ⋃ s ∈ ToricSpace.boundedTriangles,
    ToricSpace.inclusion s ''
      (Metric.closedBall (0 : ToricCharts.CoordinateSpace 3) 1 ∩
        ToricFan.Triangle.time ⁻¹' Metric.closedBall 0 η)

private theorem CuspQuotient.compactRepresentatives_compact (η : ℝ) :
    IsCompact (compactRepresentatives η) := by
  apply ToricSpace.boundedTriangles_finite.isCompact_biUnion
  intro s _
  exact
    ((ProperSpace.isCompact_closedBall _ _).inter_right
          (Metric.isClosed_closedBall.preimage
            ToricFan.Triangle.time_holomorphic.continuous)).image
      (ToricSpace.inclusion_openEmbedding s).continuous

private theorem CuspQuotient.compactRepresentatives_time {η : ℝ} {x : ToricSpace.Space}
    (hx : x ∈ compactRepresentatives η) : ‖ToricSpace.time x‖ ≤ η := by
  obtain ⟨s, _, z, hz, rfl⟩ := Set.mem_iUnion₂.mp hx
  simpa only [ToricSpace.time_inclusion, Set.mem_preimage, Metric.mem_closedBall,
    dist_zero_right] using hz.2

private def CuspQuotient.tubeRepresentatives (ε η : ℝ) : Set (ToricSpace.Tube (disc ε)) :=
  Subtype.val ⁻¹' compactRepresentatives η

private theorem CuspQuotient.tubeRepresentatives_compact {ε η : ℝ} (hηε : η < ε) :
    IsCompact (tubeRepresentatives ε η) := by
  apply
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (compactRepresentatives_compact η)
  intro x hx
  have hxt : x ∈ ToricSpace.tubeOpen (disc ε) := by
    change ToricSpace.time x ∈ Metric.ball 0 ε
    simpa only [Metric.mem_ball, dist_zero_right] using
      (compactRepresentatives_time hx).trans_lt hηε
  exact ⟨⟨x, hxt⟩, rfl⟩

private def
    CuspQuotient.quotientRepresentatives (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (η : ℝ) :
    Set (QuotientSpace C ε) :=
  quotientMap C ε '' tubeRepresentatives ε η

private theorem
    CuspQuotient.quotientRepresentatives_compact (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    {η : ℝ} (hηε : η < ε) : IsCompact (quotientRepresentatives C ε η) :=
  (tubeRepresentatives_compact hηε).image (quotientMap_continuous C ε)

private theorem
    CuspQuotient.torus_mem_quotientRepresentatives (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε1 : ε < 1) (hR : ToricSpace.SmallDrift C ε) {η : ℝ} {x : ToricSpace.Tube (disc ε)}
    (hx : (x : ToricSpace.Space) ∈ ToricSpace.openTorus)
    (hxη : ‖ToricSpace.time (x : ToricSpace.Space)‖ ≤ η) :
    quotientMap C ε x ∈ quotientRepresentatives C ε η := by
  have hxt : ‖ToricSpace.time (x : ToricSpace.Space)‖ < ε := by
    have hxε : ToricSpace.time (x : ToricSpace.Space) ∈ Metric.ball 0 ε := x.2
    simpa only [Metric.mem_ball, dist_zero_right] using hxε
  have ht : 0 < ‖ToricSpace.time (x : ToricSpace.Space)‖ :=
    norm_pos_iff.mpr ((ToricSpace.mem_openTorus_iff _).mp hx)
  obtain ⟨v, s, hs, z, hz, he⟩ :=
    ToricSpace.exists_bounded_chart_translate C hx (Real.log_neg ht (hxt.trans hε1)) (hR _ ht hxt)
  refine ⟨ToricSpace.tubeTranslate C (disc ε) v x, ?_, quotientMap_translate C ε v x⟩
  change ToricSpace.twistedTranslate C v (x : ToricSpace.Space) ∈ compactRepresentatives η
  refine Set.mem_iUnion₂.mpr ⟨s, hs, z, ⟨hz, ?_⟩, he⟩
  change ToricFan.Triangle.time z ∈ Metric.closedBall 0 η
  rw [← ToricSpace.time_inclusion s z, he, ToricSpace.time_twistedTranslate,
    Metric.mem_closedBall, dist_zero_right]
  exact hxη

private theorem CuspQuotient.tube_torus_dense (ε : ℝ) :
    Dense
      ((Subtype.val : ToricSpace.Tube (disc ε) → ToricSpace.Space) ⁻¹' ToricSpace.openTorus) :=
  ToricSpace.openTorus_dense.preimage
    (ToricSpace.tubeOpen (disc ε)).isOpen.isOpenEmbedding_subtypeVal.isOpenMap

private theorem CuspQuotient.mem_quotientRepresentatives (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {η : ℝ} (hη : 0 < η) (hηε : η < ε)
    {x : ToricSpace.Tube (disc ε)} (hxη : ‖ToricSpace.time (x : ToricSpace.Space)‖ ≤ η) :
    quotientMap C ε x ∈ quotientRepresentatives C ε η := by
  let := quotient_t2Space C ε hε hε1 hC hR
  by_cases hx : (x : ToricSpace.Space) ∈ ToricSpace.openTorus
  · exact torus_mem_quotientRepresentatives C ε hε1 hR hx hxη
  have hzero : ToricSpace.time (x : ToricSpace.Space) = 0 := by
    simpa only [ToricSpace.mem_openTorus_iff, Classical.not_not] using hx
  let A := quotientMap C ε ⁻¹' quotientRepresentatives C ε η
  have hA : IsClosed A :=
    (quotientRepresentatives_compact C ε hηε).isClosed.preimage (quotientMap_continuous C ε)
  let U : Set (ToricSpace.Tube (disc ε)) := {p | ‖ToricSpace.time (p : ToricSpace.Space)‖ < η}
  have hU : IsOpen U :=
    isOpen_lt (ToricSpace.time_holomorphic.continuous.comp continuous_subtype_val).norm
      continuous_const
  by_contra hn
  have hxU : x ∈ U := by simpa [U, hzero] using hη
  obtain ⟨p, hp, hpU, hpA⟩ :=
    (tube_torus_dense ε).exists_mem_open (hU.inter hA.isOpen_compl) ⟨x, hxU, hn⟩
  exact hpA (torus_mem_quotientRepresentatives C ε hε1 hR hp hpU.le)

private theorem CuspQuotient.closedDisc_preimage_compact (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) {η : ℝ} (hη : 0 < η) (hηε : η < ε) :
    IsCompact (projection C ε ⁻¹' Metric.closedBall 0 η) := by
  have he : projection C ε ⁻¹' Metric.closedBall 0 η = quotientRepresentatives C ε η := by
    ext q
    constructor
    · induction q using Quotient.inductionOn with
      | h x =>
        intro hx
        exact
          mem_quotientRepresentatives C ε hε hε1 hC hR hη hηε
            (by
              simpa only [Set.mem_preimage, projection, Quotient.lift_mk, Metric.mem_closedBall,
                dist_zero_right] using hx)
    · rintro ⟨x, hx, rfl⟩
      simpa only [Set.mem_preimage, projection_quotientMap, Metric.mem_closedBall,
        dist_zero_right] using compactRepresentatives_time hx
  rw [he]
  exact quotientRepresentatives_compact C ε hηε

private theorem CuspQuotient.baseMap_proper (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsProperMap (baseMap C ε) := by
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨baseMap_continuous C ε, ?_⟩
  intro K hK
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨t, ht, hmax⟩ := hK.exists_isMaxOn hne continuous_subtype_val.norm.continuousOn
  have htε : ‖(t : ℂ)‖ < ε := by
    have htball : (t : ℂ) ∈ Metric.ball 0 ε := t.2
    simpa only [Metric.mem_ball, dist_zero_right] using htball
  obtain ⟨η, htη, hηε⟩ := exists_between htε
  have hη : 0 < η := (norm_nonneg _).trans_lt htη
  apply
    (closedDisc_preimage_compact C ε hε hε1 hC hR hη hηε).of_isClosed_subset
      (hK.isClosed.preimage (baseMap_continuous C ε))
  intro q hq
  have hb : ‖projection C ε q‖ ≤ ‖(t : ℂ)‖ := hmax hq
  simpa only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right] using hb.trans htη.le

private def CuspQuotient.affineTube (ε : ℝ) : Set (ToricCharts.CoordinateSpace 3) :=
  {z | ‖ToricFan.Triangle.time z‖ < ε}

private theorem CuspQuotient.affineTube_starConvex (ε : ℝ) : StarConvex ℝ 0 (affineTube ε) := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  simp only [smul_zero, zero_add]
  change ‖ToricFan.Triangle.time (b • z)‖ < ε
  have he : ‖ToricFan.Triangle.time (b • z)‖ = b ^ 3 * ‖ToricFan.Triangle.time z‖ := by
    simp only [ToricFan.Triangle.time, Pi.smul_apply, norm_mul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hb]
    ring
  rw [he]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hb hb1)).trans_lt hz

private theorem
    CuspQuotient.affineTube_connected {ε : ℝ} (hε : 0 < ε) : IsConnected (affineTube ε) :=
  ((affineTube_starConvex ε).isPathConnected
      (by simpa [affineTube, ToricFan.Triangle.time] using hε)).isConnected

private theorem CuspQuotient.tube_eq_union (ε : ℝ) :
    (ToricSpace.tubeOpen (disc ε) : Set ToricSpace.Space) =
      ⋃ s : ToricFan.Triangle, ToricSpace.inclusion s '' affineTube ε := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, z, rfl⟩ := ToricSpace.inclusion_jointly_surjective x
    refine Set.mem_iUnion.mpr ⟨s, z, ?_, rfl⟩
    have he : ToricSpace.time (ToricSpace.inclusion s z) ∈ Metric.ball 0 ε := hx
    simpa only [affineTube, Set.mem_ofPred_eq, ToricSpace.time_inclusion, Metric.mem_ball,
      dist_zero_right] using he
  · intro hx
    obtain ⟨s, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
    change ToricSpace.time (ToricSpace.inclusion s z) ∈ Metric.ball 0 ε
    simpa only [affineTube, Set.mem_ofPred_eq, ToricSpace.time_inclusion, Metric.mem_ball,
      dist_zero_right] using hz

private theorem CuspQuotient.tube_charts_common_point {ε : ℝ} (hε : 0 < ε) :
    (⋂ s : ToricFan.Triangle, ToricSpace.inclusion s '' affineTube ε).Nonempty := by
  let x := ToricSpace.inclusion ToricSpace.referenceTriangle ![((ε / 2 : ℝ) : ℂ), 1, 1]
  have hxT : x ∈ ToricSpace.openTorus := by
    apply ToricSpace.inclusion_torus_subset ToricSpace.referenceTriangle
    refine ⟨_, ?_, rfl⟩
    intro i
    fin_cases i
    · change ((ε / 2 : ℝ) : ℂ) ≠ 0
      exact_mod_cast (half_pos hε).ne'
    · exact one_ne_zero
    · exact one_ne_zero
  have hxt : ‖ToricSpace.time x‖ < ε := by
    simpa [x, ToricFan.Triangle.time, abs_of_pos hε] using half_lt_self hε
  refine ⟨x, Set.mem_iInter.mpr fun s => ?_⟩
  obtain ⟨z, _, he⟩ := ToricSpace.exists_torus_chart s hxT
  refine ⟨z, ?_, he⟩
  change ‖ToricFan.Triangle.time z‖ < ε
  rw [← ToricSpace.time_inclusion s z, he]
  exact hxt

private theorem CuspQuotient.tube_connected {ε : ℝ} (hε : 0 < ε) :
    ConnectedSpace (ToricSpace.Tube (disc ε)) := by
  apply isConnected_iff_connectedSpace.mp
  have hpre : IsPreconnected (⋃ s : ToricFan.Triangle, ToricSpace.inclusion s '' affineTube ε) :=
    isPreconnected_iUnion (tube_charts_common_point hε)
      (fun s =>
        (affineTube_connected hε).isPreconnected.image _
          (ToricSpace.inclusion_openEmbedding s).continuous.continuousOn)
  rw [← tube_eq_union] at hpre
  refine ⟨⟨ToricSpace.inclusion ToricSpace.referenceTriangle 0, ?_⟩, hpre⟩
  change ToricSpace.time (ToricSpace.inclusion ToricSpace.referenceTriangle 0) ∈ Metric.ball 0 ε
  simpa [ToricFan.Triangle.time] using hε

private theorem
    CuspQuotient.quotient_connected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    ConnectedSpace (QuotientSpace C ε) := by
  let := tube_connected hε
  infer_instance

private theorem CuspQuotient.quotient_secondCountable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : SecondCountableTopology (QuotientSpace C ε) := by
  let := ToricSpace.tubeAction C (disc ε)
  have hq := quotientMap_covering C ε hε hε1 hC hR
  exact hq.toIsQuotientMap.secondCountableTopology hq.isCoveringMap.isOpenMap

private def CuspQuotient.centralAffine : Set (ToricCharts.CoordinateSpace 3) :=
  {z | ToricFan.Triangle.time z = 0}

private def CuspQuotient.centralOrigin : centralAffine :=
  ⟨0, by simp [centralAffine, ToricFan.Triangle.time]⟩

private theorem CuspQuotient.centralAffine_starConvex : StarConvex ℝ 0 centralAffine := by
  intro z hz a b _ _ _
  simp only [smul_zero, zero_add]
  change ToricFan.Triangle.time (b • z) = 0
  obtain h | h | h := (ToricFan.Triangle.central_fibre z).mp hz
  all_goals simp [ToricFan.Triangle.time, Pi.smul_apply, h]

private instance CuspQuotient.centralAffine_connected : ConnectedSpace centralAffine :=
  isConnected_iff_connectedSpace.mp
    ((centralAffine_starConvex.isPathConnected centralOrigin.2).isConnected)

private def
    CuspQuotient.centralLift (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle) (z : centralAffine) :
    ToricSpace.Tube (disc ε) :=
  ⟨ToricSpace.inclusion s z,
    by
    change ToricSpace.time (ToricSpace.inclusion s z) ∈ Metric.ball 0 ε
    rw [ToricSpace.time_inclusion, z.2]
    simpa using hε⟩

private theorem CuspQuotient.centralLift_continuous (ε : ℝ) (hε : 0 < ε) (s : ToricFan.Triangle) :
    Continuous (centralLift ε hε s) :=
  ((ToricSpace.inclusion_openEmbedding s).continuous.comp continuous_subtype_val).subtype_mk _

private def CuspQuotient.centralChartMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (s : ToricFan.Triangle) : centralAffine → QuotientSpace C ε :=
  quotientMap C ε ∘ centralLift ε hε s

private theorem CuspQuotient.centralChartMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s : ToricFan.Triangle) : Continuous (centralChartMap C ε hε s) :=
  (quotientMap_continuous C ε).comp (centralLift_continuous ε hε s)

private theorem
    CuspQuotient.centralChartMap_range_connected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s : ToricFan.Triangle) : IsConnected (Set.range (centralChartMap C ε hε s)) :=
  isConnected_range (centralChartMap_continuous C ε hε s)

@[simp]
private theorem CuspQuotient.projection_centralChartMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s : ToricFan.Triangle) (z : centralAffine) :
    projection C ε (centralChartMap C ε hε s z) = 0 := by
  change ToricSpace.time (ToricSpace.inclusion s z) = 0
  rw [ToricSpace.time_inclusion, z.2]

private theorem CuspQuotient.centralChartMap_origin_shift (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s : ToricFan.Triangle) (v : Fin 2 → ℤ) :
    centralChartMap C ε hε (s.shift (ToricSpace.cuspVector v)) centralOrigin =
      centralChartMap C ε hε s centralOrigin := by
  have he :
    ToricSpace.tubeTranslate C (disc ε) v (centralLift ε hε s centralOrigin) =
      centralLift ε hε (s.shift (ToricSpace.cuspVector v)) centralOrigin := by
    apply Subtype.ext
    simp [ToricSpace.tubeTranslate, centralLift, centralOrigin, ToricSpace.twistedTranslate,
      ToricSpace.variableMultiplier, ToricSpace.translate_inclusion,
      ToricSpace.torusAction_inclusion, ToricSpace.scale]
  exact
    (congrArg (quotientMap C ε) he).symm.trans
      (quotientMap_translate C ε v (centralLift ε hε s centralOrigin))

private theorem
    CuspQuotient.centralChartMap_origin_reference (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (s : ToricFan.Triangle) :
    centralChartMap C ε hε s centralOrigin =
      centralChartMap C ε hε ⟨0, 0, s.upper⟩ centralOrigin := by
  let v : Fin 2 → ℤ := ![-s.b, s.a]
  have he : (⟨0, 0, s.upper⟩ : ToricFan.Triangle).shift (ToricSpace.cuspVector v) = s := by
    ext <;> simp [ToricFan.Triangle.shift, ToricSpace.cuspVector, v]
  simpa only [he] using centralChartMap_origin_shift C ε hε ⟨0, 0, s.upper⟩ v

private theorem CuspQuotient.reference_central_overlap :
    ToricSpace.inclusion (⟨0, 0, Bool.false⟩ : ToricFan.Triangle) ![1, 0, 0] =
      ToricSpace.inclusion (⟨0, 0, Bool.true⟩ : ToricFan.Triangle) ![0, 0, 1] := by
  have hA :
    ToricFan.Triangle.transition ⟨0, 0, Bool.false⟩ ⟨0, 0, Bool.true⟩ =
      !![1, 1, 0; 1, 0, 1; -1, 0, 0] := by decide
  apply (ToricSpace.inclusion_eq_iff _ _ _ _).mpr
  constructor
  · rw [ToricFan.Triangle.chartChange_source]
    intro i j hij
    rw [hA] at hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    norm_num
  · change ToricCharts.monomial (ToricFan.Triangle.transition _ _) _ = _
    rw [hA]
    ext i
    fin_cases i <;> norm_num [ToricCharts.monomial, Fin.prod_univ_succ]

private theorem
    CuspQuotient.reference_centralChartMap_overlap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    (Set.range (centralChartMap C ε hε ⟨0, 0, Bool.false⟩) ∩
        Set.range (centralChartMap C ε hε ⟨0, 0, Bool.true⟩)).Nonempty := by
  let z : centralAffine := ⟨![1, 0, 0], by simp [centralAffine, ToricFan.Triangle.time]⟩
  let w : centralAffine := ⟨![0, 0, 1], by simp [centralAffine, ToricFan.Triangle.time]⟩
  refine ⟨centralChartMap C ε hε ⟨0, 0, Bool.false⟩ z, Set.mem_range_self z, w, ?_⟩
  apply congrArg (quotientMap C ε)
  exact Subtype.ext reference_central_overlap.symm

private theorem CuspQuotient.central_fibre_eq_union (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    projection C ε ⁻¹' {0} = ⋃ s : ToricFan.Triangle, Set.range (centralChartMap C ε hε s) := by
  ext q
  constructor
  · induction q using Quotient.inductionOn with
    | h x =>
      intro hx
      have hx0 : ToricSpace.time (x : ToricSpace.Space) = 0 := hx
      obtain ⟨s, z, he⟩ := ToricSpace.inclusion_jointly_surjective (x : ToricSpace.Space)
      have hz : z ∈ centralAffine := by
        change ToricFan.Triangle.time z = 0
        rw [← ToricSpace.time_inclusion s z, he, hx0]
      refine Set.mem_iUnion.mpr ⟨s, ⟨z, hz⟩, ?_⟩
      apply congrArg (quotientMap C ε)
      exact Subtype.ext he
  · intro hq
    obtain ⟨s, z, rfl⟩ := Set.mem_iUnion.mp hq
    exact projection_centralChartMap C ε hε s z

private theorem CuspQuotient.central_fibre_connected (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : IsConnected (projection C ε ⁻¹' {0}) := by
  let U := fun s : ToricFan.Triangle => Set.range (centralChartMap C ε hε s)
  let R := U ⟨0, 0, Bool.false⟩ ∪ U ⟨0, 0, Bool.true⟩
  have hU (s : ToricFan.Triangle) : IsPreconnected (U s) :=
    (centralChartMap_range_connected C ε hε s).isPreconnected
  have hR : IsPreconnected R :=
    IsPreconnected.union' (reference_centralChartMap_overlap C ε hε) (hU _) (hU _)
  have horigin (s : ToricFan.Triangle) : centralChartMap C ε hε s centralOrigin ∈ R := by
    rw [centralChartMap_origin_reference]
    cases hs : s.upper
    · exact Or.inl (Set.mem_range_self _)
    · exact Or.inr (Set.mem_range_self _)
  have hcommon : (⋂ s : ToricFan.Triangle, R ∪ U s).Nonempty := by
    refine
      ⟨centralChartMap C ε hε ⟨0, 0, Bool.false⟩ centralOrigin, Set.mem_iInter.mpr fun s => ?_⟩
    exact Or.inl (Or.inl (Set.mem_range_self _))
  have hpre : IsPreconnected (⋃ s : ToricFan.Triangle, R ∪ U s) :=
    isPreconnected_iUnion hcommon
      (fun s =>
        IsPreconnected.union'
          ⟨centralChartMap C ε hε s centralOrigin, horigin s, Set.mem_range_self _⟩ hR (hU s))
  have he : (⋃ s : ToricFan.Triangle, R ∪ U s) = ⋃ s : ToricFan.Triangle, U s := by
    apply subset_antisymm
    · intro q hq
      obtain ⟨s, hq⟩ := Set.mem_iUnion.mp hq
      rcases hq with (hq | hq) | hq
      · exact Set.mem_iUnion.mpr ⟨⟨0, 0, Bool.false⟩, hq⟩
      · exact Set.mem_iUnion.mpr ⟨⟨0, 0, Bool.true⟩, hq⟩
      · exact Set.mem_iUnion.mpr ⟨s, hq⟩
    · intro q hq
      obtain ⟨s, hq⟩ := Set.mem_iUnion.mp hq
      exact Set.mem_iUnion.mpr ⟨s, Or.inr hq⟩
  rw [he] at hpre
  rw [central_fibre_eq_union C ε hε]
  exact
    ⟨⟨centralChartMap C ε hε ⟨0, 0, Bool.false⟩ centralOrigin,
        Set.mem_iUnion.mpr ⟨⟨0, 0, Bool.false⟩, Set.mem_range_self _⟩⟩,
      hpre⟩

private def CuspHoneycombHexagon.CommonFibres.descend {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) (x : X) : Y :=
  g (hf x).choose

private theorem
    CuspHoneycombHexagon.CommonFibres.descend_apply {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) (hfg : ∀ a b, f a = f b → g a = g b) (a : A) :
    descend f g hf (f a) = g a :=
  hfg _ a (hf (f a)).choose_spec

private theorem CuspHoneycombHexagon.CommonFibres.descend_surjective {A X Y : Type*} (f : A → X)
    (g : A → Y) (hf : Function.Surjective f) (hfg : ∀ a b, f a = f b → g a = g b)
    (hg : Function.Surjective g) : Function.Surjective (descend f g hf) := by
  intro y
  obtain ⟨a, rfl⟩ := hg y
  exact ⟨f a, descend_apply f g hf hfg a⟩

private theorem CuspHoneycombHexagon.CommonFibres.descend_injective {A X Y : Type*} (f : A → X)
    (g : A → Y) (hf : Function.Surjective f) (hgf : ∀ a b, g a = g b → f a = f b) :
    Function.Injective (descend f g hf) := by
  intro x y h
  have he := hgf (hf x).choose (hf y).choose h
  exact (hf x).choose_spec.symm.trans (he.trans (hf y).choose_spec)

private theorem CuspHoneycombHexagon.CommonFibres.descend_continuous {A X Y : Type*} (f : A → X)
    (g : A → Y) (hf : Function.Surjective f) [TopologicalSpace A] [TopologicalSpace X]
    [TopologicalSpace Y] (hq : Topology.IsQuotientMap f) (hg : Continuous g)
    (hfg : ∀ a b, f a = f b → g a = g b) : Continuous (descend f g hf) := by
  apply hq.continuous_iff.mpr
  have he : descend f g hf ∘ f = g := funext (descend_apply f g hf hfg)
  rwa [he]

private def CuspHoneycombHexagon.CommonFibres.homeomorph {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace A] [T2Space X] [T2Space Y] (hfc : Continuous f) (hgc : Continuous g)
    (hg : Function.Surjective g) (hfg : ∀ a b, f a = f b ↔ g a = g b) : X ≃ₜ Y := by
  have hX : IsCompact (Set.univ : Set X) := by
    rw [← Set.range_eq_univ.mpr hf]
    exact isCompact_range hfc
  letI : CompactSpace X := ⟨hX⟩
  have hd : Continuous (descend f g hf) :=
    descend_continuous f g hf (hfc.isClosedMap.isQuotientMap hfc hf) hgc (fun a b => (hfg a b).mp)
  let e : X ≃ Y :=
    Equiv.ofBijective (descend f g hf)
      ⟨descend_injective f g hf (fun a b => (hfg a b).mpr),
        descend_surjective f g hf (fun a b => (hfg a b).mp) hg⟩
  exact Equiv.toHomeomorphOfContinuousClosed e hd hd.isClosedMap

@[simp]
private theorem
    CuspHoneycombHexagon.CommonFibres.homeomorph_apply {A X Y : Type*} (f : A → X) (g : A → Y)
    (hf : Function.Surjective f) [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace A] [T2Space X] [T2Space Y] (hfc : Continuous f) (hgc : Continuous g)
    (hg : Function.Surjective g) (hfg : ∀ a b, f a = f b ↔ g a = g b) (a : A) :
    homeomorph f g hf hfc hgc hg hfg (f a) = g a :=
  descend_apply f g hf (fun a b => (hfg a b).mp) a

end Mathoverflow1973

end
