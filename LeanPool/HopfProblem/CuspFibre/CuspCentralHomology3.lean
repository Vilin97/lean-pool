/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
public import LeanPool.HopfProblem.CuspFibre.CuspCentralHomology1
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology4
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.Toric.ToricSpace2
import all LeanPool.HopfProblem.CuspFibre.CuspPositiveRetraction
import all LeanPool.HopfProblem.HomologyTheory.FirstHurewicz3
import all LeanPool.HopfProblem.Toric.CuspHoneycombHexagon
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology7
import all LeanPool.HopfProblem.CuspFibre.CuspCentralHomology1

/-!
# Hopf problem: cusp fibre · cusp central homology 3

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
    CuspCentralHomology.central_pathConnectedSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) : PathConnectedSpace (CuspRetraction.QuotientCentralFibre C r) := by
  exact
    (CuspHoneycomb.honeycombCollapseMap_surjective C r hr).pathConnectedSpace
      (CuspHoneycomb.honeycombCollapseMap_continuous C r hr)

private def
    CuspCentralHomology.centralBasePoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) :
    CuspRetraction.QuotientCentralFibre C r :=
  CuspHoneycomb.honeycombCollapseMap C r hr (1, 0)

private def CuspCentralHomology.centralSingularH0Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 0 ≃ₗ[ℤ] ℤ := by
  let := central_pathConnectedSpace C r hr
  exact
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv (CuspRetraction.QuotientCentralFibre C r)

private theorem
    CuspCentralHomology.centralSingularH0Equiv_natural (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (r : ℝ) (hr : 0 < r) {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (f : C(X, CuspRetraction.QuotientCentralFibre C r))
    (a : SingularMayerVietoris.SingularHomology X 0) :
    centralSingularH0Equiv C r hr (SingularMayerVietoris.singularHomologyMap f 0 a) =
      PeriodTorusHigherHomology.connectedHomologyZeroEquiv X a := by
  let := central_pathConnectedSpace C r hr
  exact PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural f a

private structure CuspCentralHomology.SmallCentralModel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < r
  radius_lt_one : radius < 1
  smallDrift : ToricSpace.SmallDrift C radius
  equivalence : CuspRetraction.QuotientCentralFibre C r ≃ₕ CuspQuotient.QuotientSpace C radius
  inclusion_eq :
    equivalence.toFun = centralIntoSmallerQuotient C r radius radius_pos radius_lt.le hC

private theorem
    CuspCentralHomology.exists_smallCentralModel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Nonempty (SmallCentralModel C r hC) := by
  obtain ⟨δ₀, hδ₀, hδ₀r, _hδ₀1, he⟩ := exists_centralHomotopyEquiv C r hr hC
  have hCδ₀ : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ₀) := fun i j =>
    (hC i j).mono (Metric.ball_subset_ball hδ₀r.le)
  obtain ⟨δ, hδ, hδδ₀, hδ1, hR, _hCδ⟩ := CuspQuotient.exists_admissible_radius C hδ₀ hCδ₀
  have hδr := hδδ₀.trans hδ₀r
  obtain ⟨e, he⟩ := he δ hδ hδδ₀.le hδr.le
  exact ⟨⟨δ, hδ, hδr, hδ1, hR, e, he⟩⟩

private def
    CuspCentralHomology.smallCentralModel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SmallCentralModel C r hC :=
  Classical.choice (exists_smallCentralModel C r hr hC)

private theorem CuspCentralHomology.SmallCentralModel.holomorphic {C : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    {r : ℝ} {hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)}
    (M : CuspCentralHomology.SmallCentralModel C r hC) :
    ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 M.radius) := fun i j =>
  (hC i j).mono (Metric.ball_subset_ball M.radius_lt.le)

private def CuspCentralHomology.SmallCentralModel.singularH1Equiv {C : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    {r : ℝ} {hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)}
    (M : CuspCentralHomology.SmallCentralModel C r hC)
    (q : CuspRetraction.QuotientCentralFibre C r) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1 ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv M.equivalence 1).trans
    (CuspQuotient.singularH1Equiv C M.radius M.radius_pos M.radius_lt_one M.holomorphic
      M.smallDrift (M.equivalence q))

private def CuspCentralHomology.centralSingularH1Equiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1 ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  (smallCentralModel C r hr hC).singularH1Equiv (centralBasePoint C r hr)

private theorem
    CuspCentralHomology.centralSingularH1_free (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Free ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1) :=
  Module.Free.of_equiv (centralSingularH1Equiv C r hr hC).symm

private theorem
    CuspCentralHomology.centralSingularH1_finite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.Finite ℤ
      (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1) :=
  Module.Finite.of_surjective (centralSingularH1Equiv C r hr hC).symm.toLinearMap
    (centralSingularH1Equiv C r hr hC).symm.surjective

private theorem
    CuspCentralHomology.centralSingularH1_finrank (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)
    (hr : 0 < r) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Module.finrank ℤ
        (SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C r) 1) =
      2 := by
  rw [(centralSingularH1Equiv C r hr hC).finrank_eq]
  simp

private def
    CuspCentralHomology.edgeCharacter (n : Fin 2 → ℤ) : ToricSpace.CompactFibreTorus →* Circle
    where
  toFun u := u 0 ^ (-n 1) * u 1 ^ n 0
  map_one' := by simp
  map_mul' u
    v := by
    simp only [Pi.mul_apply, mul_zpow]
    ac_rfl

private theorem CuspCentralHomology.edgeCharacter_continuous (n : Fin 2 → ℤ) :
    Continuous (edgeCharacter n) :=
  ((continuous_apply 0).zpow (-n 1)).mul ((continuous_apply 1).zpow (n 0))

private theorem CuspCentralHomology.edgeCharacter_edgeCompactPhase (n m : Fin 2 → ℤ) (a : Circle) :
    edgeCharacter n (ToricSpace.edgeCompactPhase m a) = a ^ (n 0 * m 1 - n 1 * m 0) := by
  change (a ^ m 0) ^ (-n 1) * (a ^ m 1) ^ n 0 = _
  rw [← zpow_mul, ← zpow_mul, ← zpow_add]
  congr 1
  ring

@[simp]
private theorem CuspCentralHomology.edgeCharacter_own_phase (n : Fin 2 → ℤ) (a : Circle) :
    edgeCharacter n (ToricSpace.edgeCompactPhase n a) = 1 := by
  rw [edgeCharacter_edgeCompactPhase]
  simp [mul_comm]

private abbrev CuspCentralHomology.hexagonCharacter (k : Fin 6) :
    ToricSpace.CompactFibreTorus →* Circle :=
  edgeCharacter (ToricComponent.hexagonRay k)

private def CuspCentralHomology.hexagonCharacterSection (k : Fin 6) :
    Circle →* ToricSpace.CompactFibreTorus :=
  ToricSpace.edgeCompactPhase (ToricComponent.hexagonRay (k + 1))

private theorem CuspCentralHomology.hexagonCharacterSection_continuous (k : Fin 6) :
    Continuous (hexagonCharacterSection k) :=
  ToricSpace.edgeCompactPhase_continuous _

@[simp]
private theorem CuspCentralHomology.hexagonCharacter_section (k : Fin 6) (a : Circle) :
    hexagonCharacter k (hexagonCharacterSection k a) = a := by
  rw [hexagonCharacterSection, edgeCharacter_edgeCompactPhase]
  have hd :
    ToricComponent.hexagonRay k 0 * ToricComponent.hexagonRay (k + 1) 1 -
        ToricComponent.hexagonRay k 1 * ToricComponent.hexagonRay (k + 1) 0 =
      1 := by fin_cases k <;> decide
  rw [hd, zpow_one]

private theorem CuspCentralHomology.hexagonCharacter_decomposition (k : Fin 6)
    (u : ToricSpace.CompactFibreTorus) :
    ToricSpace.edgeCompactPhase (ToricComponent.hexagonRay k) ((hexagonCharacter (k + 1) u)⁻¹) *
        hexagonCharacterSection k (hexagonCharacter k u) =
      u := by
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [hexagonCharacter, edgeCharacter, hexagonCharacterSection, ToricSpace.edgeCompactPhase,
      ToricComponent.hexagonRay]

private theorem CuspCentralHomology.ker_hexagonCharacter (k : Fin 6) :
    (hexagonCharacter k).ker = ToricSpace.edgeCircle (ToricComponent.hexagonRay k) := by
  ext u
  constructor
  · intro hu
    change hexagonCharacter k u = 1 at hu
    change ∃ a : Circle, ToricSpace.edgeCompactPhase (ToricComponent.hexagonRay k) a = u
    refine ⟨(hexagonCharacter (k + 1) u)⁻¹, ?_⟩
    simpa only [hu, map_one, mul_one] using hexagonCharacter_decomposition k u
  · rintro ⟨a, rfl⟩
    exact edgeCharacter_own_phase (ToricComponent.hexagonRay k) a

private theorem CuspCentralHomology.hexagonCharacter_eq_iff (k : Fin 6)
    (u v : ToricSpace.CompactFibreTorus) :
    hexagonCharacter k u = hexagonCharacter k v ↔
      u⁻¹ * v ∈ ToricSpace.edgeCircle (ToricComponent.hexagonRay k) := by
  rw [← ker_hexagonCharacter, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]

private theorem CuspCentralHomology.chartPoint_stabilizer_fst_zero (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) (hz0 : z 0 = 0) (hz1 : z 1 ≠ 0) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) =
      ToricSpace.edgeCircle (ToricComponent.hexagonRay i) := by
  have hne : ToricComponent.zeroCoordinate i ≠ CuspHoneycombHexagon.firstCoordinate i := by
    intro h
    have hv := congrArg (ToricComponent.zeroTriangle i).vertex h
    rw [ToricComponent.zeroTriangle_vertex, CuspHoneycombHexagon.firstCoordinate_vertex] at hv
    exact ToricComponent.hexagonRay_ne_zero i hv.symm
  have hrest (j : Fin 3) (hj0 : j ≠ ToricComponent.zeroCoordinate i)
    (hj1 : j ≠ CuspHoneycombHexagon.firstCoordinate i) :
    CuspHoneycombHexagon.liftCoordinates i z j ≠ 0 := by
    rcases CuspHoneycombHexagon.coordinates_exhaustive i j with h | h | h
    · exact (hj0 h).elim
    · exact (hj1 h).elim
    · subst j
      simpa only [CuspHoneycombHexagon.liftCoordinates_second] using hz1
  rw [CuspHoneycombHexagon.chartPoint_coe]
  have h :=
    ToricSpace.compactFibre_stabilizer_eq_edgeCircle_of_two_zero (ToricComponent.zeroTriangle i)
      (CuspHoneycombHexagon.liftCoordinates i z) (ToricComponent.zeroCoordinate i)
      (CuspHoneycombHexagon.firstCoordinate i) hne (CuspHoneycombHexagon.liftCoordinates_zero i z)
      (by simpa only [CuspHoneycombHexagon.liftCoordinates_first] using hz0) hrest
  simpa only [CuspHoneycombHexagon.firstCoordinate_vertex, ToricComponent.zeroTriangle_vertex,
    sub_zero] using h

private theorem CuspCentralHomology.chartPoint_stabilizer_snd_zero (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) (hz0 : z 0 ≠ 0) (hz1 : z 1 = 0) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) =
      ToricSpace.edgeCircle (ToricComponent.hexagonRay (i + 1)) := by
  have hne : ToricComponent.zeroCoordinate i ≠ CuspHoneycombHexagon.secondCoordinate i := by
    intro h
    have hv := congrArg (ToricComponent.zeroTriangle i).vertex h
    rw [ToricComponent.zeroTriangle_vertex, CuspHoneycombHexagon.secondCoordinate_vertex] at hv
    exact ToricComponent.hexagonRay_ne_zero (i + 1) hv.symm
  have hrest (j : Fin 3) (hj0 : j ≠ ToricComponent.zeroCoordinate i)
    (hj1 : j ≠ CuspHoneycombHexagon.secondCoordinate i) :
    CuspHoneycombHexagon.liftCoordinates i z j ≠ 0 := by
    rcases CuspHoneycombHexagon.coordinates_exhaustive i j with h | h | h
    · exact (hj0 h).elim
    · subst j
      simpa only [CuspHoneycombHexagon.liftCoordinates_first] using hz0
    · exact (hj1 h).elim
  rw [CuspHoneycombHexagon.chartPoint_coe]
  have h :=
    ToricSpace.compactFibre_stabilizer_eq_edgeCircle_of_two_zero (ToricComponent.zeroTriangle i)
      (CuspHoneycombHexagon.liftCoordinates i z) (ToricComponent.zeroCoordinate i)
      (CuspHoneycombHexagon.secondCoordinate i) hne
      (CuspHoneycombHexagon.liftCoordinates_zero i z)
      (by simpa only [CuspHoneycombHexagon.liftCoordinates_second] using hz1) hrest
  simpa only [CuspHoneycombHexagon.secondCoordinate_vertex, ToricComponent.zeroTriangle_vertex,
    sub_zero] using h

private theorem CuspCentralHomology.positiveBoundary_stabilizer_eq_edgeCircle (k : Fin 6)
    (q : CuspHoneycombHexagon.positiveBoundary k)
    (hprev : q.1 ≠ CuspHoneycombHexagon.squarePoint (k - 1) CuspHoneycombHexagon.cornerZero)
    (hcurr : q.1 ≠ CuspHoneycombHexagon.squarePoint k CuspHoneycombHexagon.cornerZero) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus (q.1.1 : ToricSpace.Space) =
      ToricSpace.edgeCircle (ToricComponent.hexagonRay k) := by
  obtain ⟨i, z, he⟩ := CuspHoneycombHexagon.chartPoint_jointly_surjective q.1.1
  have hqzero (hz0 : z 0 = 0) (hz1 : z 1 = 0) :
    q.1 = CuspHoneycombHexagon.squarePoint i CuspHoneycombHexagon.cornerZero := by
    apply Subtype.ext
    change
      q.1.1 =
        CuspHoneycombHexagon.chartPoint i (fun j => (CuspHoneycombHexagon.cornerZero.1 j : ℂ))
    rw [← he]
    apply congrArg (CuspHoneycombHexagon.chartPoint i)
    funext j
    fin_cases j
    · change z 0 = 0
      exact hz0
    · change z 1 = 0
      exact hz1
  have hb :
    (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) ∈
      ToricSpace.rayDivisor (ToricComponent.hexagonRay k) := by
    rw [he]
    exact q.property
  rcases (CuspHoneycombHexagon.chartPoint_mem_rayDivisor_iff i k z).mp hb with ⟨rfl, hz0⟩ |
    ⟨rfl, hz1⟩
  · have hz1 : z 1 ≠ 0 := fun hz1 => hcurr (hqzero hz0 hz1)
    rw [← he]
    exact chartPoint_stabilizer_fst_zero k z hz0 hz1
  · have hz0 : z 0 ≠ 0 := by
      intro hz0
      apply hprev
      simpa only [add_sub_cancel_right] using hqzero hz0 hz1
    rw [← he]
    exact chartPoint_stabilizer_snd_zero i z hz0 hz1

private theorem CuspCentralHomology.compatibleBoundaryArc_stabilizer (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1 : ToricSpace.Space) =
      ToricSpace.edgeCircle (ToricComponent.hexagonRay k) := by
  apply
    positiveBoundary_stabilizer_eq_edgeCircle k
      (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t)
  · intro h
    apply ht0
    apply (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).injective
    apply Subtype.ext
    exact h.trans (CuspHoneycombHexagon.compatibleBoundaryArc_zero_point C₀ k).symm
  · intro h
    apply ht1
    apply (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).injective
    apply Subtype.ext
    exact h.trans (CuspHoneycombHexagon.compatibleBoundaryArc_one_point C₀ k).symm

private def CuspCollapse.centralPhaseOrbit (q : CuspPositiveRetraction.PositiveCentralFibre)
    (u : ToricSpace.CompactFibreTorus) : CuspRetraction.CentralFibre :=
  centralPolarMap (u, q)

@[simp]
private theorem
    CuspCollapse.centralPhaseOrbit_apply (q : CuspPositiveRetraction.PositiveCentralFibre)
    (u : ToricSpace.CompactFibreTorus) : centralPhaseOrbit q u = centralPolarMap (u, q) :=
  rfl

private abbrev CuspCollapse.CentralModulusFibre (q : CuspPositiveRetraction.PositiveCentralFibre) :=
  { x : CuspRetraction.CentralFibre // centralModulus x = q }

private def CuspCollapse.centralPhaseOrbitToFibre (q : CuspPositiveRetraction.PositiveCentralFibre)
    (u : ToricSpace.CompactFibreTorus) : CentralModulusFibre q :=
  ⟨centralPhaseOrbit q u, centralModulus_centralPolarMap (u, q)⟩

private theorem CuspCentralHomology.centralPhaseOrbit_eq_iff_character (k : Fin 6)
    (q : CuspPositiveRetraction.PositiveCentralFibre)
    (hq :
      MulAction.stabilizer ToricSpace.CompactFibreTorus (q.1 : ToricSpace.Space) =
        ToricSpace.edgeCircle (ToricComponent.hexagonRay k))
    (u v : ToricSpace.CompactFibreTorus) :
    CuspCollapse.centralPhaseOrbit q u = CuspCollapse.centralPhaseOrbit q v ↔
      hexagonCharacter k u = hexagonCharacter k v := by
  rw [CuspCollapse.centralPhaseOrbit_apply, CuspCollapse.centralPhaseOrbit_apply,
    CuspCollapse.centralPolarMap_eq_iff]
  simp only [true_and, hq]
  exact (hexagonCharacter_eq_iff k u v).symm

private def CuspCentralHomology.characterCircleOrbit (k : Fin 6)
    (q : CuspPositiveRetraction.PositiveCentralFibre) (a : Circle) :
    CuspCollapse.CentralModulusFibre q :=
  CuspCollapse.centralPhaseOrbitToFibre q (hexagonCharacterSection k a)

private theorem CuspCentralHomology.characterCircleOrbit_character (k : Fin 6)
    (q : CuspPositiveRetraction.PositiveCentralFibre)
    (hq :
      MulAction.stabilizer ToricSpace.CompactFibreTorus (q.1 : ToricSpace.Space) =
        ToricSpace.edgeCircle (ToricComponent.hexagonRay k))
    (u : ToricSpace.CompactFibreTorus) :
    characterCircleOrbit k q (hexagonCharacter k u) = CuspCollapse.centralPhaseOrbitToFibre q u :=
  by
  apply Subtype.ext
  apply (centralPhaseOrbit_eq_iff_character k q hq _ _).mpr
  exact hexagonCharacter_section k _

private theorem CuspCentralHomology.characterCircleOrbit_injective (k : Fin 6)
    (q : CuspPositiveRetraction.PositiveCentralFibre)
    (hq :
      MulAction.stabilizer ToricSpace.CompactFibreTorus (q.1 : ToricSpace.Space) =
        ToricSpace.edgeCircle (ToricComponent.hexagonRay k)) :
    Function.Injective (characterCircleOrbit k q) := by
  intro a b hab
  have he := (centralPhaseOrbit_eq_iff_character k q hq _ _).mp (congrArg Subtype.val hab)
  simpa only [hexagonCharacter_section] using he

private def CuspCentralHomology.edgeArcPositive (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) : CuspPositiveRetraction.PositiveCentralFibre :=
  ⟨⟨(CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1,
      (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.2⟩,
    ToricSpace.time_eq_zero_of_mem_rayDivisor
      (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1.2⟩

@[simp]
private theorem CuspCentralHomology.edgeArcPositive_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) :
    (edgeArcPositive C₀ k t).1.1 =
      ((CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1 : ToricSpace.Space) :=
  rfl

private theorem CuspCentralHomology.edgeArcPositive_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : Continuous (edgeArcPositive C₀ k) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact
    continuous_subtype_val.comp
      (continuous_subtype_val.comp
        (continuous_subtype_val.comp
          (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).continuous))

private theorem CuspCentralHomology.edgeArcPositive_injective (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : Function.Injective (edgeArcPositive C₀ k) := by
  intro s t h
  apply (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).injective
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : CuspPositiveRetraction.PositiveCentralFibre => q.1.1) h

private theorem
    CuspCentralHomology.edgeArcPositive_stabilizer (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    MulAction.stabilizer ToricSpace.CompactFibreTorus
        ((edgeArcPositive C₀ k t).1 : ToricSpace.Space) =
      ToricSpace.edgeCircle (ToricComponent.hexagonRay k) :=
  compatibleBoundaryArc_stabilizer C₀ k t ht0 ht1

private def CuspCentralHomology.edgeCylinder (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (p : unitInterval × Circle) : CuspRetraction.CentralFibre :=
  CuspCollapse.centralPolarMap (hexagonCharacterSection k p.2, edgeArcPositive C₀ k p.1)

@[simp]
private theorem CuspCentralHomology.edgeCylinder_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (p : unitInterval × Circle) :
    (edgeCylinder C₀ k p : ToricSpace.Space) =
      ToricSpace.compactFibreAction (hexagonCharacterSection k p.2)
        ((CuspHoneycombHexagon.compatibleBoundaryArc C₀ k p.1).1.1 : ToricSpace.Space) :=
  rfl

private theorem
    CuspCentralHomology.edgeCylinder_continuous (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    Continuous (edgeCylinder C₀ k) :=
  CuspCollapse.centralPolarMap_continuous.comp
    (((hexagonCharacterSection_continuous k).comp continuous_snd).prodMk
      ((edgeArcPositive_continuous C₀ k).comp continuous_fst))

@[simp]
private theorem CuspCentralHomology.edgeCylinder_modulus (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (p : unitInterval × Circle) :
    CuspCollapse.centralModulus (edgeCylinder C₀ k p) = edgeArcPositive C₀ k p.1 :=
  CuspCollapse.centralModulus_centralPolarMap _

private theorem
    CuspCentralHomology.edgeCylinder_character (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (u : ToricSpace.CompactFibreTorus) :
    edgeCylinder C₀ k (t, hexagonCharacter k u) =
      CuspCollapse.centralPolarMap (u, edgeArcPositive C₀ k t) :=
  congrArg Subtype.val
    (characterCircleOrbit_character k (edgeArcPositive C₀ k t)
      (edgeArcPositive_stabilizer C₀ k t ht0 ht1) u)

private theorem CuspCentralHomology.edgeCylinder_eq_iff_of_interior (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (s t : unitInterval) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (a b : Circle) :
    edgeCylinder C₀ k (s, a) = edgeCylinder C₀ k (t, b) ↔ s = t ∧ a = b := by
  constructor
  · intro h
    have hst : s = t :=
      edgeArcPositive_injective C₀ k
        (by simpa only [edgeCylinder_modulus] using congrArg CuspCollapse.centralModulus h)
    subst t
    refine ⟨rfl, ?_⟩
    apply
      characterCircleOrbit_injective k (edgeArcPositive C₀ k s)
        (edgeArcPositive_stabilizer C₀ k s hs0 hs1)
    exact Subtype.ext h
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem
    CuspCentralHomology.edgeCylinder_zero_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (a : Circle) :
    (edgeCylinder C₀ k (0, a) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle (k - 1)) 0 := by
  rw [edgeCylinder_coe, CuspHoneycombHexagon.compatibleBoundaryArc_zero,
    CuspHoneycombHexagon.positiveBoundaryArc_zero_coe,
    ToricSpace.compactFibreAction_inclusion_zero]

private theorem CuspCentralHomology.edgeCylinder_one_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (a : Circle) :
    (edgeCylinder C₀ k (1, a) : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0 := by
  rw [edgeCylinder_coe, CuspHoneycombHexagon.compatibleBoundaryArc_one,
    CuspHoneycombHexagon.positiveBoundaryArc_one_coe,
    ToricSpace.compactFibreAction_inclusion_zero]

private theorem
    CuspCentralHomology.edgeCylinder_character_all (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) (u : ToricSpace.CompactFibreTorus) :
    edgeCylinder C₀ k (t, hexagonCharacter k u) =
      CuspCollapse.centralPolarMap (u, edgeArcPositive C₀ k t) := by
  by_cases ht0 : t = 0
  · subst t
    apply Subtype.ext
    rw [edgeCylinder_zero_coe, CuspCollapse.centralPolarMap_coe, edgeArcPositive_coe,
      CuspHoneycombHexagon.compatibleBoundaryArc_zero,
      CuspHoneycombHexagon.positiveBoundaryArc_zero_coe,
      ToricSpace.compactFibreAction_inclusion_zero]
  by_cases ht1 : t = 1
  · subst t
    apply Subtype.ext
    rw [edgeCylinder_one_coe, CuspCollapse.centralPolarMap_coe, edgeArcPositive_coe,
      CuspHoneycombHexagon.compatibleBoundaryArc_one,
      CuspHoneycombHexagon.positiveBoundaryArc_one_coe,
      ToricSpace.compactFibreAction_inclusion_zero]
  exact edgeCylinder_character C₀ k t ht0 ht1 u

private def CuspCentralHomology.cornerOrigin (k : Fin 6) : CuspRetraction.CentralFibre :=
  ⟨ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0, by simp [ToricFan.Triangle.time]⟩

@[simp]
private theorem CuspCentralHomology.cornerOrigin_coe (k : Fin 6) :
    (cornerOrigin k : ToricSpace.Space) =
      ToricSpace.inclusion (ToricComponent.zeroTriangle k) 0 :=
  rfl

private theorem CuspCentralHomology.zeroTriangle_upper_eq_iff_parity (k l : Fin 6) :
    (ToricComponent.zeroTriangle k).upper = (ToricComponent.zeroTriangle l).upper ↔
      k.val % 2 = l.val % 2 := by
  have h :
    ∀ k l : Fin 6,
      (ToricComponent.zeroTriangle k).upper = (ToricComponent.zeroTriangle l).upper ↔
        k.val % 2 = l.val % 2 := by decide
  exact h k l

private def CuspCentralHomology.cornerPoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (k : Fin 6) : CuspRetraction.QuotientCentralFibre C ε :=
  CuspCollapse.centralProject C ε hε (cornerOrigin k)

@[simp]
private theorem CuspCentralHomology.cornerPoint_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k : Fin 6) :
    (cornerPoint C ε hε k : CuspQuotient.QuotientSpace C ε) =
      CuspQuotient.centralChartMap C ε hε (ToricComponent.zeroTriangle k)
        CuspQuotient.centralOrigin :=
  rfl

private theorem
    CuspCentralHomology.cornerPoint_eq_iff_parity (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k l : Fin 6) :
    cornerPoint C ε hε k = cornerPoint C ε hε l ↔ k.val % 2 = l.val % 2 := by
  rw [Subtype.ext_iff, cornerPoint_coe, cornerPoint_coe,
    CuspQuotient.centralChartMap_origin_eq_iff, zeroTriangle_upper_eq_iff_parity]

private def CuspCentralHomology.evenPole (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CuspRetraction.QuotientCentralFibre C ε :=
  cornerPoint C ε hε 0

private def CuspCentralHomology.oddPole (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CuspRetraction.QuotientCentralFibre C ε :=
  cornerPoint C ε hε 1

private theorem
    CuspCentralHomology.cornerPoint_eq_evenPole_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k : Fin 6) : cornerPoint C ε hε k = evenPole C ε hε ↔ k.val % 2 = 0 := by
  simpa only [evenPole, Fin.val_zero, Nat.zero_mod] using cornerPoint_eq_iff_parity C ε hε k 0

private theorem
    CuspCentralHomology.cornerPoint_eq_oddPole_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k : Fin 6) : cornerPoint C ε hε k = oddPole C ε hε ↔ k.val % 2 = 1 := by
  simpa [oddPole] using cornerPoint_eq_iff_parity C ε hε k 1

private theorem
    CuspCentralHomology.pole_ne (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    evenPole C ε hε ≠ oddPole C ε hε := by
  intro h
  have hp := (cornerPoint_eq_iff_parity C ε hε 0 1).mp h
  norm_num at hp

private abbrev CuspCentralHomology.ThreeCircles :=
  _root_.Circle ⊕ (_root_.Circle ⊕ _root_.Circle)

private def CuspCentralHomology.unitCircleHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology _root_.Circle 0 ≃ₗ[ℤ] ℤ :=
  PeriodTorusHigherHomology.connectedHomologyZeroEquiv _root_.Circle

private def CuspCentralHomology.unitCircleHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology _root_.Circle 1 ≃ₗ[ℤ] ℤ :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm 1).trans
    PeriodTorusHigherHomology.circleHomologyOneEquiv

private theorem CuspCentralHomology.unitCircle_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology _root_.Circle (n + 2)) := by
  let := PeriodTorusHigherHomology.circle_homology_subsingleton n
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm
        (n + 2)).injective.subsingleton

private def CuspCentralHomology.threeCirclesHomologySplit (n : ℕ) :
    SingularMayerVietoris.SingularHomology ThreeCircles n ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology _root_.Circle n ×
        (SingularMayerVietoris.SingularHomology _root_.Circle n ×
          SingularMayerVietoris.SingularHomology _root_.Circle n)) :=
  ((PeriodTorusHigherHomology.sumHomologyEquiv _root_.Circle (_root_.Circle ⊕ _root_.Circle)
          n).toAddEquiv.trans
      ((AddEquiv.refl _).prodCongr
        (PeriodTorusHigherHomology.sumHomologyEquiv _root_.Circle _root_.Circle
            n).toAddEquiv)).toIntLinearEquiv

private def CuspCentralHomology.integerTripleEquiv : (ℤ × (ℤ × ℤ)) ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ({    toFun a := ![a.1, a.2.1, a.2.2]
        invFun a := (a 0, (a 1, a 2))
        left_inv _ := rfl
        right_inv a := by ext i; fin_cases i <;> rfl
        map_add' a b := by ext i; fin_cases i <;> rfl } :
      (ℤ × (ℤ × ℤ)) ≃+ (Fin 3 → ℤ)).toIntLinearEquiv

private def CuspCentralHomology.threeCirclesHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology ThreeCircles 0 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ((threeCirclesHomologySplit 0).toAddEquiv.trans
      ((unitCircleHomologyZeroEquiv.toAddEquiv.prodCongr
            (unitCircleHomologyZeroEquiv.toAddEquiv.prodCongr
              unitCircleHomologyZeroEquiv.toAddEquiv)).trans
        integerTripleEquiv.toAddEquiv)).toIntLinearEquiv

private def CuspCentralHomology.threeCirclesHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology ThreeCircles 1 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ((threeCirclesHomologySplit 1).toAddEquiv.trans
      ((unitCircleHomologyOneEquiv.toAddEquiv.prodCongr
            (unitCircleHomologyOneEquiv.toAddEquiv.prodCongr
              unitCircleHomologyOneEquiv.toAddEquiv)).trans
        integerTripleEquiv.toAddEquiv)).toIntLinearEquiv

private theorem CuspCentralHomology.threeCircles_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology ThreeCircles (n + 2)) := by
  let := unitCircle_homology_subsingleton n
  exact (threeCirclesHomologySplit (n + 2)).injective.subsingleton

private def CuspCentralHomology.sumCoordinates : (Fin 3 → ℤ) →ₗ[ℤ] ℤ
    where
  toFun a := ∑ i, a i
  map_add' a b := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' r a := by simp only [RingHom.id_apply, Pi.smul_apply, Finset.smul_sum]

@[simp]
private theorem CuspCentralHomology.sumCoordinates_apply (a : Fin 3 → ℤ) :
    sumCoordinates a = a 0 + a 1 + a 2 := by
  simp only [sumCoordinates, LinearMap.coe_mk, AddHom.coe_mk, Fin.sum_univ_three]

private theorem CuspCentralHomology.sumHomology_map_mo1973_12039 {X Y Z : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (f : C(X ⊕ Y, Z)) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (X ⊕ Y) n) :
    SingularMayerVietoris.singularHomologyMap f n a =
      SingularMayerVietoris.singularHomologyMap (f.comp (PeriodTorusHigherHomology.sumInlMap X Y))
          n (PeriodTorusHigherHomology.sumHomologyEquiv X Y n a).1 +
        SingularMayerVietoris.singularHomologyMap
          (f.comp (PeriodTorusHigherHomology.sumInrMap X Y)) n
          (PeriodTorusHigherHomology.sumHomologyEquiv X Y n a).2 := by
  have hf :
    f =
      PeriodTorusHigherHomology.sumElimMap (f.comp (PeriodTorusHigherHomology.sumInlMap X Y))
        (f.comp (PeriodTorusHigherHomology.sumInrMap X Y)) := by
    ext x
    cases x <;> rfl
  conv_lhs => rw [hf]
  exact PeriodTorusHigherHomology.sumHomologyEquiv_sumElim _ _ n a

private theorem
    CuspCentralHomology.threeCirclesHomologyZeroEquiv_map {Y : Type} [TopologicalSpace Y]
    [PathConnectedSpace Y] (f : C(ThreeCircles, Y))
    (a : SingularMayerVietoris.SingularHomology ThreeCircles 0) :
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y
        (SingularMayerVietoris.singularHomologyMap f 0 a) =
      sumCoordinates (threeCirclesHomologyZeroEquiv a) := by
  rw [sumHomology_map_mo1973_12039 f, map_add]
  rw [sumHomology_map_mo1973_12039
      (f.comp
        (PeriodTorusHigherHomology.sumInrMap _root_.Circle (_root_.Circle ⊕ _root_.Circle))),
    map_add]
  rw [PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural,
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural,
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural, sumCoordinates_apply]
  exact (add_assoc _ _ _).symm

private theorem CuspCentralHomology.threeCirclesHomologyZeroEquiv_map_homotopyEquiv {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ ThreeCircles)
    (f : C(X, Y)) (a : SingularMayerVietoris.SingularHomology X 0) :
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y
        (SingularMayerVietoris.singularHomologyMap f 0 a) =
      sumCoordinates
        (threeCirclesHomologyZeroEquiv
          (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 0 a)) := by
  obtain ⟨b, rfl⟩ := (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 0).symm.surjective a
  rw [LinearEquiv.apply_symm_apply,
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_symm_apply]
  change
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y
        (((SingularMayerVietoris.singularHomologyMap f 0).comp
            (SingularMayerVietoris.singularHomologyMap e.invFun 0))
          b) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact threeCirclesHomologyZeroEquiv_map (f.comp e.invFun) b

private def CuspCentralHomology.sumCoordinatesKernelEquiv :
    LinearMap.ker sumCoordinates ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ({    toFun a := ![a.1 1, a.1 2]
        invFun
          a :=
          ⟨![-a 0 - a 1, a 0, a 1],
            by
            change sumCoordinates ![-a 0 - a 1, a 0, a 1] = 0
            rw [sumCoordinates_apply]
            change -a 0 - a 1 + a 0 + a 1 = 0
            ring⟩
        left_inv
          a := by
          apply Subtype.ext
          have ha : a.1 0 + a.1 1 + a.1 2 = 0 := by
            simpa only [LinearMap.mem_ker, sumCoordinates_apply] using a.2
          ext i
          fin_cases i
          · change -a.1 1 - a.1 2 = a.1 0
            omega
          · rfl
          · rfl
        right_inv a := by ext i; fin_cases i <;> rfl
        map_add' a b := by ext i; fin_cases i <;> rfl } :
      LinearMap.ker sumCoordinates ≃+ (Fin 2 → ℤ)).toIntLinearEquiv

@[simp]
private theorem
    CuspCentralHomology.centralProject_edgeCylinder_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (a : Circle) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k (0, a)) =
      cornerPoint C ε hε (k - 1) :=
  congrArg (CuspCollapse.centralProject C ε hε) (Subtype.ext (edgeCylinder_zero_coe (C 0) k a))

@[simp]
private theorem
    CuspCentralHomology.centralProject_edgeCylinder_one (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (a : Circle) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k (1, a)) = cornerPoint C ε hε k :=
  congrArg (CuspCollapse.centralProject C ε hε) (Subtype.ext (edgeCylinder_one_coe (C 0) k a))

private def
    CuspCentralHomology.doubleCylinder (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (p : unitInterval × ThreeCircles) : CuspRetraction.QuotientCentralFibre C ε :=
  match p.2 with
  | Sum.inl a => CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 0 (p.1, a))
  | Sum.inr (Sum.inl a) =>
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 1 (unitInterval.symm p.1, a))
  | Sum.inr (Sum.inr a) => CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 2 (p.1, a))

@[simp]
private theorem CuspCentralHomology.doubleCylinder_first (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (t : unitInterval) (a : Circle) :
    doubleCylinder C ε hε (t, Sum.inl a) =
      CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 0 (t, a)) :=
  rfl

@[simp]
private theorem CuspCentralHomology.doubleCylinder_middle (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (t : unitInterval) (a : Circle) :
    doubleCylinder C ε hε (t, Sum.inr (Sum.inl a)) =
      CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 1 (unitInterval.symm t, a)) :=
  rfl

@[simp]
private theorem CuspCentralHomology.doubleCylinder_last (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (t : unitInterval) (a : Circle) :
    doubleCylinder C ε hε (t, Sum.inr (Sum.inr a)) =
      CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 2 (t, a)) :=
  rfl

private theorem
    CuspCentralHomology.doubleCylinder_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (doubleCylinder C ε hε) := by
  have h0 :
    Continuous
      (fun p : unitInterval × Circle =>
        CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 0 p)) :=
    (CuspCollapse.centralProject_continuous C ε hε).comp (edgeCylinder_continuous (C 0) 0)
  have h1 :
    Continuous
      (fun p : unitInterval × Circle =>
        CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 1 (unitInterval.symm p.1, p.2))) :=
    (CuspCollapse.centralProject_continuous C ε hε).comp
      ((edgeCylinder_continuous (C 0) 1).comp
        ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd))
  have h2 :
    Continuous
      (fun p : unitInterval × Circle =>
        CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) 2 p)) :=
    (CuspCollapse.centralProject_continuous C ε hε).comp (edgeCylinder_continuous (C 0) 2)
  let e0 :
    unitInterval × ThreeCircles ≃ₜ (unitInterval × Circle) ⊕ (unitInterval × (Circle ⊕ Circle)) :=
    Homeomorph.prodSumDistrib
  let e1 :
    unitInterval × (Circle ⊕ Circle) ≃ₜ (unitInterval × Circle) ⊕ (unitInterval × Circle) :=
    Homeomorph.prodSumDistrib
  have h := (h0.sumElim ((h1.sumElim h2).comp e1.continuous)).comp e0.continuous
  apply h.congr
  rintro ⟨t, a⟩
  rcases a with a | a | a <;> rfl

@[simp]
private theorem CuspCentralHomology.doubleCylinder_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ThreeCircles) : doubleCylinder C ε hε (0, a) = oddPole C ε hε := by
  rcases a with a | a | a <;>
    simp only [doubleCylinder_first, doubleCylinder_middle, doubleCylinder_last,
      unitInterval.symm_zero, centralProject_edgeCylinder_zero, centralProject_edgeCylinder_one]
  all_goals exact (cornerPoint_eq_oddPole_iff C ε hε _).mpr (by decide)

@[simp]
private theorem CuspCentralHomology.doubleCylinder_one (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ThreeCircles) : doubleCylinder C ε hε (1, a) = evenPole C ε hε := by
  rcases a with a | a | a <;>
    simp only [doubleCylinder_first, doubleCylinder_middle, doubleCylinder_last,
      unitInterval.symm_one, centralProject_edgeCylinder_zero, centralProject_edgeCylinder_one]
  all_goals exact (cornerPoint_eq_evenPole_iff C ε hε _).mpr (by decide)

private theorem
    CuspCentralHomology.doubleCylinder_respects (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p q : unitInterval × ThreeCircles) (h : (suspensionSetoid ThreeCircles).r p q) :
    doubleCylinder C ε hε p = doubleCylinder C ε hε q := by
  rcases p with ⟨s, a⟩
  rcases q with ⟨t, b⟩
  change s = t ∧ (s = 0 ∨ s = 1 ∨ a = b) at h
  rcases h with ⟨hst, hs⟩
  cases hst
  rcases hs with rfl | rfl | rfl <;> simp only [doubleCylinder_zero, doubleCylinder_one]

private def CuspCentralHomology.doubleSuspensionMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Suspension ThreeCircles → CuspRetraction.QuotientCentralFibre C ε :=
  Quotient.lift (doubleCylinder C ε hε) (doubleCylinder_respects C ε hε)

@[simp]
private theorem
    CuspCentralHomology.doubleSuspensionMap_mk (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (t : unitInterval) (a : ThreeCircles) :
    doubleSuspensionMap C ε hε (Suspension.mk t a) = doubleCylinder C ε hε (t, a) :=
  rfl

private theorem
    CuspCentralHomology.doubleSuspensionMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Continuous (doubleSuspensionMap C ε hε) :=
  (Suspension.isQuotientMap_mk (X := ThreeCircles)).continuous_iff.mpr
    (doubleCylinder_continuous C ε hε)

private theorem CuspCentralHomology.chartPoint_branchVertices_fst_zero (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) (hz0 : z 0 = 0) (hz1 : z 1 ≠ 0) :
    ToricSpace.branchVertices (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) =
      {0, ToricComponent.hexagonRay i} := by
  rw [CuspHoneycombHexagon.chartPoint_coe, ToricSpace.branchVertices_inclusion]
  ext v
  change
    (∃ j,
        CuspHoneycombHexagon.liftCoordinates i z j = 0 ∧
          (ToricComponent.zeroTriangle i).vertex j = v) ↔
      v = 0 ∨ v = ToricComponent.hexagonRay i
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases CuspHoneycombHexagon.coordinates_exhaustive i j with rfl | rfl | rfl
    · exact Or.inl (ToricComponent.zeroTriangle_vertex i)
    · exact Or.inr (CuspHoneycombHexagon.firstCoordinate_vertex i)
    · exact (hz1 (by simpa only [CuspHoneycombHexagon.liftCoordinates_second] using hj)).elim
  · rintro (rfl | rfl)
    · exact
        ⟨ToricComponent.zeroCoordinate i, CuspHoneycombHexagon.liftCoordinates_zero i z,
          ToricComponent.zeroTriangle_vertex i⟩
    · exact
        ⟨CuspHoneycombHexagon.firstCoordinate i,
          (CuspHoneycombHexagon.liftCoordinates_first i z).trans hz0,
          CuspHoneycombHexagon.firstCoordinate_vertex i⟩

private theorem CuspCentralHomology.chartPoint_branchVertices_snd_zero (i : Fin 6)
    (z : ToricCharts.CoordinateSpace 2) (hz0 : z 0 ≠ 0) (hz1 : z 1 = 0) :
    ToricSpace.branchVertices (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) =
      {0, ToricComponent.hexagonRay (i + 1)} := by
  rw [CuspHoneycombHexagon.chartPoint_coe, ToricSpace.branchVertices_inclusion]
  ext v
  change
    (∃ j,
        CuspHoneycombHexagon.liftCoordinates i z j = 0 ∧
          (ToricComponent.zeroTriangle i).vertex j = v) ↔
      v = 0 ∨ v = ToricComponent.hexagonRay (i + 1)
  constructor
  · rintro ⟨j, hj, rfl⟩
    rcases CuspHoneycombHexagon.coordinates_exhaustive i j with rfl | rfl | rfl
    · exact Or.inl (ToricComponent.zeroTriangle_vertex i)
    · exact (hz0 (by simpa only [CuspHoneycombHexagon.liftCoordinates_first] using hj)).elim
    · exact Or.inr (CuspHoneycombHexagon.secondCoordinate_vertex i)
  · rintro (rfl | rfl)
    · exact
        ⟨ToricComponent.zeroCoordinate i, CuspHoneycombHexagon.liftCoordinates_zero i z,
          ToricComponent.zeroTriangle_vertex i⟩
    · exact
        ⟨CuspHoneycombHexagon.secondCoordinate i,
          (CuspHoneycombHexagon.liftCoordinates_second i z).trans hz1,
          CuspHoneycombHexagon.secondCoordinate_vertex i⟩

private theorem CuspCentralHomology.positiveBoundary_branchVertices (k : Fin 6)
    (q : CuspHoneycombHexagon.positiveBoundary k)
    (hprev : q.1 ≠ CuspHoneycombHexagon.squarePoint (k - 1) CuspHoneycombHexagon.cornerZero)
    (hcurr : q.1 ≠ CuspHoneycombHexagon.squarePoint k CuspHoneycombHexagon.cornerZero) :
    ToricSpace.branchVertices (q.1.1 : ToricSpace.Space) = {0, ToricComponent.hexagonRay k} := by
  obtain ⟨i, z, he⟩ := CuspHoneycombHexagon.chartPoint_jointly_surjective q.1.1
  have hqzero (hz0 : z 0 = 0) (hz1 : z 1 = 0) :
    q.1 = CuspHoneycombHexagon.squarePoint i CuspHoneycombHexagon.cornerZero := by
    apply Subtype.ext
    change
      q.1.1 =
        CuspHoneycombHexagon.chartPoint i (fun j => (CuspHoneycombHexagon.cornerZero.1 j : ℂ))
    rw [← he]
    apply congrArg (CuspHoneycombHexagon.chartPoint i)
    funext j
    fin_cases j
    · change z 0 = 0
      exact hz0
    · change z 1 = 0
      exact hz1
  have hb :
    (CuspHoneycombHexagon.chartPoint i z : ToricSpace.Space) ∈
      ToricSpace.rayDivisor (ToricComponent.hexagonRay k) := by
    rw [he]
    exact q.property
  rcases (CuspHoneycombHexagon.chartPoint_mem_rayDivisor_iff i k z).mp hb with ⟨rfl, hz0⟩ |
    ⟨rfl, hz1⟩
  · have hz1 : z 1 ≠ 0 := fun hz1 => hcurr (hqzero hz0 hz1)
    rw [← he]
    exact chartPoint_branchVertices_fst_zero k z hz0 hz1
  · have hz0 : z 0 ≠ 0 := by
      intro hz0
      apply hprev
      simpa only [add_sub_cancel_right] using hqzero hz0 hz1
    rw [← he]
    exact chartPoint_branchVertices_snd_zero i z hz0 hz1

private theorem
    CuspCentralHomology.compatibleBoundaryArc_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ToricSpace.branchVertices
        ((CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1 : ToricSpace.Space) =
      {0, ToricComponent.hexagonRay k} := by
  apply positiveBoundary_branchVertices k (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t)
  · intro h
    apply ht0
    apply (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).injective
    apply Subtype.ext
    exact h.trans (CuspHoneycombHexagon.compatibleBoundaryArc_zero_point C₀ k).symm
  · intro h
    apply ht1
    apply (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).injective
    apply Subtype.ext
    exact h.trans (CuspHoneycombHexagon.compatibleBoundaryArc_one_point C₀ k).symm

private theorem CuspCentralHomology.edgeArcPositive_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ToricSpace.branchVertices ((edgeArcPositive C₀ k t).1 : ToricSpace.Space) =
      {0, ToricComponent.hexagonRay k} :=
  compatibleBoundaryArc_branchVertices C₀ k t ht0 ht1

private theorem
    CuspCentralHomology.branchVertices_compactFibreAction (u : ToricSpace.CompactFibreTorus)
    (x : ToricSpace.Space) :
    ToricSpace.branchVertices (ToricSpace.compactFibreAction u x) = ToricSpace.branchVertices x :=
  ToricSpace.branchVertices_torusAction _ x

private theorem CuspCentralHomology.edgeCylinder_branchVertices (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (p : unitInterval × Circle) (ht0 : p.1 ≠ 0) (ht1 : p.1 ≠ 1) :
    ToricSpace.branchVertices (edgeCylinder C₀ k p : ToricSpace.Space) =
      {0, ToricComponent.hexagonRay k} := by
  rw [edgeCylinder_coe, branchVertices_compactFibreAction]
  exact compatibleBoundaryArc_branchVertices C₀ k p.1 ht0 ht1

private theorem CuspCentralHomology.edgeArcPositive_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    ToricSpace.branchCount ((edgeArcPositive C₀ k t).1 : ToricSpace.Space) = 2 := by
  rw [← ToricSpace.branchVertices_ncard, edgeArcPositive_branchVertices C₀ k t ht0 ht1]
  exact Set.ncard_pair (ToricComponent.hexagonRay_ne_zero k).symm

private theorem
    CuspCentralHomology.edgeCylinder_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (p : unitInterval × Circle) (ht0 : p.1 ≠ 0) (ht1 : p.1 ≠ 1) :
    ToricSpace.branchCount (edgeCylinder C₀ k p : ToricSpace.Space) = 2 := by
  rw [← ToricSpace.branchVertices_ncard, edgeCylinder_branchVertices C₀ k p ht0 ht1]
  exact Set.ncard_pair (ToricComponent.hexagonRay_ne_zero k).symm

private theorem CuspCentralHomology.edgeArcPositive_zero_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : ToricSpace.branchCount ((edgeArcPositive C₀ k 0).1 : ToricSpace.Space) = 3 := by
  rw [edgeArcPositive_coe, CuspHoneycombHexagon.compatibleBoundaryArc_zero_point,
    CuspHoneycombHexagon.squarePoint_cornerZero_coe, ToricSpace.branchCount_inclusion,
    ToricCharts.zeroCount_zero]

private theorem CuspCentralHomology.edgeArcPositive_one_branchCount (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) : ToricSpace.branchCount ((edgeArcPositive C₀ k 1).1 : ToricSpace.Space) = 3 := by
  rw [edgeArcPositive_coe, CuspHoneycombHexagon.compatibleBoundaryArc_one_point,
    CuspHoneycombHexagon.squarePoint_cornerZero_coe, ToricSpace.branchCount_inclusion,
    ToricCharts.zeroCount_zero]

private theorem CuspCentralHomology.hexagonRay_first_half_ne_neg (k l : Fin 6) (hk : k.val < 3)
    (hl : l.val < 3) : ToricComponent.hexagonRay k ≠ -ToricComponent.hexagonRay l := by
  have h :
    ∀ k l : Fin 6,
      k.val < 3 → l.val < 3 → ToricComponent.hexagonRay k ≠ -ToricComponent.hexagonRay l := by
    decide
  exact h k l hk hl

private theorem CuspCentralHomology.hexagonPair_image_add_eq (k l : Fin 6) (hk : k.val < 3)
    (hl : l.val < 3) (d : Fin 2 → ℤ)
    (h :
      ({0, ToricComponent.hexagonRay k} : Set (Fin 2 → ℤ)) =
        (fun w => w + d) '' {0, ToricComponent.hexagonRay l}) :
    k = l ∧ d = 0 := by
  simp only [Set.image_insert_eq, Set.image_singleton, zero_add, Set.pair_eq_pair_iff] at h
  rcases h with ⟨hd, hn⟩ | ⟨hd, hn⟩
  · subst d
    exact ⟨ToricComponent.hexagonRay_injective (by simpa only [add_zero] using hn), rfl⟩
  · have hneg : ToricComponent.hexagonRay k = -ToricComponent.hexagonRay l := by
      funext i
      have hd' := congrFun hd i
      have hn' := congrFun hn i
      change (0 : ℤ) = ToricComponent.hexagonRay l i + d i at hd'
      change ToricComponent.hexagonRay k i = d i at hn'
      change ToricComponent.hexagonRay k i = -ToricComponent.hexagonRay l i
      omega
    exact (hexagonRay_first_half_ne_neg k l hk hl hneg).elim

private def CuspCentralHomology.projectedEdgeCylinder (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k : Fin 6) (p : unitInterval × Circle) :
    CuspRetraction.QuotientCentralFibre C ε :=
  CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k p)

private theorem CuspCentralHomology.centralProject_branchCount_eq (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) {x y : CuspRetraction.CentralFibre}
    (h : CuspCollapse.centralProject C ε hε x = CuspCollapse.centralProject C ε hε y) :
    ToricSpace.branchCount (x : ToricSpace.Space) =
      ToricSpace.branchCount (y : ToricSpace.Space) := by
  obtain ⟨v, hv⟩ := (CuspCollapse.centralProject_eq_iff C ε hε x y).mp h
  rw [← hv, ToricSpace.branchCount_twistedTranslate]

private theorem CuspCentralHomology.projectedEdgeCylinder_eq_iff_of_interior
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k l : Fin 6) (hk : k.val < 3)
    (hl : l.val < 3) (s t : unitInterval) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0) (ht1 : t ≠ 1)
    (a b : Circle) :
    projectedEdgeCylinder C ε hε k (s, a) = projectedEdgeCylinder C ε hε l (t, b) ↔
      k = l ∧ s = t ∧ a = b := by
  constructor
  · intro he
    obtain ⟨v, hv⟩ := (CuspCollapse.centralProject_eq_iff C ε hε _ _).mp he
    have hb := congrArg ToricSpace.branchVertices hv
    rw [ToricSpace.branchVertices_twistedTranslate,
      edgeCylinder_branchVertices (C 0) l (t, b) ht0 ht1,
      edgeCylinder_branchVertices (C 0) k (s, a) hs0 hs1] at hb
    obtain ⟨hkl, hv0⟩ := hexagonPair_image_add_eq k l hk hl (ToricSpace.cuspVector v) hb.symm
    have hzero : v = 0 :=
      ToricSpace.cuspVector_injective (hv0.trans ToricSpace.cuspVector_zero.symm)
    subst v
    subst l
    rw [ToricSpace.twistedTranslate_zero] at hv
    exact
      ⟨rfl, (edgeCylinder_eq_iff_of_interior (C 0) k s t hs0 hs1 a b).mp (Subtype.ext hv.symm)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

private theorem CuspCentralHomology.projectedEdgeCylinder_interior_ne_corner
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a : Circle) (j : Fin 6) :
    projectedEdgeCylinder C ε hε k (t, a) ≠ cornerPoint C ε hε j := by
  intro he
  have hb := centralProject_branchCount_eq C ε hε he
  rw [edgeCylinder_branchCount (C 0) k (t, a) ht0 ht1, cornerOrigin_coe,
    ToricSpace.branchCount_inclusion, ToricCharts.zeroCount_zero] at hb
  omega

private def CuspCentralHomology.cylinderEdgeData_mo1973_12083 (t : unitInterval)
    (a : ThreeCircles) : Fin 6 × (unitInterval × Circle) :=
  match a with
  | Sum.inl a => (0, t, a)
  | Sum.inr (Sum.inl a) => (1, unitInterval.symm t, a)
  | Sum.inr (Sum.inr a) => (2, t, a)

private theorem CuspCentralHomology.cylinderEdgeData_index_lt_mo1973_12084 (t : unitInterval)
    (a : ThreeCircles) : (cylinderEdgeData_mo1973_12083 t a).1.val < 3 := by
  rcases a with a | a | a <;> norm_num [cylinderEdgeData_mo1973_12083]

private theorem CuspCentralHomology.cylinderEdgeData_time_ne_zero_mo1973_12085 (t : unitInterval)
    (a : ThreeCircles) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (cylinderEdgeData_mo1973_12083 t a).2.1 ≠ 0 := by
  rcases a with a | a | a
  · exact ht0
  · exact fun h => ht1 (unitInterval.symm_eq_zero.mp h)
  · exact ht0

private theorem CuspCentralHomology.cylinderEdgeData_time_ne_one_mo1973_12086 (t : unitInterval)
    (a : ThreeCircles) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    (cylinderEdgeData_mo1973_12083 t a).2.1 ≠ 1 := by
  rcases a with a | a | a
  · exact ht1
  · exact fun h => ht0 (unitInterval.symm_eq_one.mp h)
  · exact ht1

private theorem CuspCentralHomology.cylinderEdgeData_eq_iff_mo1973_12087 (s t : unitInterval)
    (a b : ThreeCircles) :
    ((cylinderEdgeData_mo1973_12083 s a).1 = (cylinderEdgeData_mo1973_12083 t b).1 ∧
        (cylinderEdgeData_mo1973_12083 s a).2.1 = (cylinderEdgeData_mo1973_12083 t b).2.1 ∧
          (cylinderEdgeData_mo1973_12083 s a).2.2 = (cylinderEdgeData_mo1973_12083 t b).2.2) ↔
      s = t ∧ a = b := by
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    simp [cylinderEdgeData_mo1973_12083, unitInterval.symm_inj]

private theorem CuspCentralHomology.doubleCylinder_eq_projected_mo1973_12088
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (t : unitInterval)
    (a : ThreeCircles) :
    doubleCylinder C ε hε (t, a) =
      projectedEdgeCylinder C ε hε (cylinderEdgeData_mo1973_12083 t a).1
        (cylinderEdgeData_mo1973_12083 t a).2 := by rcases a with a | a | a <;> rfl

private theorem
    CuspCentralHomology.doubleCylinder_eq_iff_of_interior (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (s t : unitInterval) (hs0 : s ≠ 0) (hs1 : s ≠ 1) (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (a b : ThreeCircles) :
    doubleCylinder C ε hε (s, a) = doubleCylinder C ε hε (t, b) ↔ s = t ∧ a = b := by
  simp only [doubleCylinder_eq_projected_mo1973_12088]
  exact
    (projectedEdgeCylinder_eq_iff_of_interior C ε hε _ _
          (cylinderEdgeData_index_lt_mo1973_12084 s a)
          (cylinderEdgeData_index_lt_mo1973_12084 t b) _ _
          (cylinderEdgeData_time_ne_zero_mo1973_12085 s a hs0 hs1)
          (cylinderEdgeData_time_ne_one_mo1973_12086 s a hs0 hs1)
          (cylinderEdgeData_time_ne_zero_mo1973_12085 t b ht0 ht1)
          (cylinderEdgeData_time_ne_one_mo1973_12086 t b ht0 ht1) _ _).trans
      (cylinderEdgeData_eq_iff_mo1973_12087 s t a b)

private theorem
    CuspCentralHomology.doubleCylinder_interior_ne_corner (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (t : unitInterval) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (a : ThreeCircles)
    (j : Fin 6) : doubleCylinder C ε hε (t, a) ≠ cornerPoint C ε hε j := by
  rw [doubleCylinder_eq_projected_mo1973_12088]
  exact
    projectedEdgeCylinder_interior_ne_corner C ε hε _ _
      (cylinderEdgeData_time_ne_zero_mo1973_12085 t a ht0 ht1)
      (cylinderEdgeData_time_ne_one_mo1973_12086 t a ht0 ht1) _ j

private theorem CuspCentralHomology.doubleCylinder_eq_oddPole_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (t : unitInterval) (a : ThreeCircles) :
    doubleCylinder C ε hε (t, a) = oddPole C ε hε ↔ t = 0 := by
  constructor
  · intro h
    by_contra ht0
    by_cases ht1 : t = 1
    · subst t
      exact pole_ne C ε hε (by simpa only [doubleCylinder_one] using h)
    · exact doubleCylinder_interior_ne_corner C ε hε t ht0 ht1 a 1 h
  · rintro rfl
    exact doubleCylinder_zero C ε hε a

private theorem
    CuspCentralHomology.doubleCylinder_eq_evenPole_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (t : unitInterval) (a : ThreeCircles) :
    doubleCylinder C ε hε (t, a) = evenPole C ε hε ↔ t = 1 := by
  constructor
  · intro h
    by_contra ht1
    by_cases ht0 : t = 0
    · subst t
      apply pole_ne C ε hε
      simpa only [doubleCylinder_zero] using h.symm
    · exact doubleCylinder_interior_ne_corner C ε hε t ht0 ht1 a 0 h
  · rintro rfl
    exact doubleCylinder_one C ε hε a

private theorem CuspCentralHomology.doubleCylinder_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p q : unitInterval × ThreeCircles) :
    doubleCylinder C ε hε p = doubleCylinder C ε hε q ↔ (suspensionSetoid ThreeCircles).r p q := by
  rcases p with ⟨s, a⟩
  rcases q with ⟨t, b⟩
  constructor
  · intro h
    change s = t ∧ (s = 0 ∨ s = 1 ∨ a = b)
    by_cases hs0 : s = 0
    · subst s
      have ht0 : t = 0 :=
        (doubleCylinder_eq_oddPole_iff C ε hε t b).mp
          (h.symm.trans (doubleCylinder_zero C ε hε a))
      exact ⟨ht0.symm, Or.inl rfl⟩
    by_cases hs1 : s = 1
    · subst s
      have ht1 : t = 1 :=
        (doubleCylinder_eq_evenPole_iff C ε hε t b).mp
          (h.symm.trans (doubleCylinder_one C ε hε a))
      exact ⟨ht1.symm, Or.inr (Or.inl rfl)⟩
    have ht0 : t ≠ 0 := by
      intro ht0
      subst t
      exact
        doubleCylinder_interior_ne_corner C ε hε s hs0 hs1 a 1
          (h.trans (doubleCylinder_zero C ε hε b))
    have ht1 : t ≠ 1 := by
      intro ht1
      subst t
      exact
        doubleCylinder_interior_ne_corner C ε hε s hs0 hs1 a 0
          (h.trans (doubleCylinder_one C ε hε b))
    obtain ⟨hst, hab⟩ := (doubleCylinder_eq_iff_of_interior C ε hε s t hs0 hs1 ht0 ht1 a b).mp h
    exact ⟨hst, Or.inr (Or.inr hab)⟩
  · exact doubleCylinder_respects C ε hε _ _

private theorem CuspCentralHomology.doubleSuspensionMap_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Function.Injective (doubleSuspensionMap C ε hε) := by
  intro x y h
  obtain ⟨⟨s, a⟩, rfl⟩ := Suspension.mk_surjective x
  obtain ⟨⟨t, b⟩, rfl⟩ := Suspension.mk_surjective y
  exact Quotient.sound ((doubleCylinder_eq_iff C ε hε (s, a) (t, b)).mp h)

private theorem
    CuspCentralHomology.edgeArcPositive_opposite (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) :
    edgeArcPositive C₀ (k + 3) (unitInterval.symm t) =
      CuspCollapse.positiveCentralTranslate C₀
        (ToricSpace.cuspVector (ToricComponent.hexagonRay k)) (edgeArcPositive C₀ k t) := by
  apply Subtype.ext
  apply Subtype.ext
  exact CuspHoneycombHexagon.compatibleBoundaryArc_opposite_coe C₀ k t

private theorem
    CuspCentralHomology.centralCollapseMap_phaseDeckMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (v : Fin 2 → ℤ) (p : CuspCollapse.PhasePositiveSpace) :
    CuspCollapse.centralCollapseMap C ε hε (CuspCollapse.phaseDeckMap (C 0) v p) =
      CuspCollapse.centralCollapseMap C ε hε p := by
  apply (CuspCollapse.centralProject_eq_iff C ε hε _ _).mpr
  exact ⟨v, (CuspCollapse.centralPolarMap_phaseDeckMap C v p).symm⟩

private theorem
    CuspCentralHomology.centralCollapseMap_opposite (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (k : Fin 6) (t : unitInterval) (u : ToricSpace.CompactFibreTorus) :
    CuspCollapse.centralCollapseMap C ε hε
        (u, edgeArcPositive (C 0) (k + 3) (unitInterval.symm t)) =
      CuspCollapse.centralCollapseMap C ε hε
        ((CuspCollapse.deckFibrePhase (C 0)
                (ToricSpace.cuspVector (ToricComponent.hexagonRay k)))⁻¹ *
            u,
          edgeArcPositive (C 0) k t) := by
  have h :=
    centralCollapseMap_phaseDeckMap C ε hε (ToricSpace.cuspVector (ToricComponent.hexagonRay k))
      ((CuspCollapse.deckFibrePhase (C 0)
              (ToricSpace.cuspVector (ToricComponent.hexagonRay k)))⁻¹ *
          u,
        edgeArcPositive (C 0) k t)
  simpa only [CuspCollapse.phaseDeckMap, mul_inv_cancel_left, ← edgeArcPositive_opposite] using h

private theorem CuspCentralHomology.centralProject_edgeCylinder_opposite
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (a : Circle) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (k + 3) (unitInterval.symm t, a)) =
      CuspCollapse.centralProject C ε hε
        (edgeCylinder (C 0) k
          (t,
            hexagonCharacter k
              ((CuspCollapse.deckFibrePhase (C 0)
                    (ToricSpace.cuspVector (ToricComponent.hexagonRay k)))⁻¹ *
                hexagonCharacterSection (k + 3) a))) := by
  change
    CuspCollapse.centralCollapseMap C ε hε
        (hexagonCharacterSection (k + 3) a, edgeArcPositive (C 0) (k + 3) (unitInterval.symm t)) =
      _
  rw [centralCollapseMap_opposite]
  exact
    (congrArg (CuspCollapse.centralProject C ε hε)
        (edgeCylinder_character_all (C 0) k t
          ((CuspCollapse.deckFibrePhase (C 0)
                (ToricSpace.cuspVector (ToricComponent.hexagonRay k)))⁻¹ *
            hexagonCharacterSection (k + 3) a))).symm

private theorem CuspCentralHomology.centralProject_edgeCylinder_opposite_exists
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (a : Circle) :
    ∃ b : Circle,
      CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (k + 3) (unitInterval.symm t, a)) =
        CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k (t, b)) :=
  ⟨_, centralProject_edgeCylinder_opposite C ε hε k t a⟩

private theorem CuspCentralHomology.edgeCylinder_mem_range_doubleCylinder
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (a : Circle) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k (t, a)) ∈
      Set.range (doubleCylinder C ε hε) := by
  fin_cases k
  · exact ⟨(t, Sum.inl a), rfl⟩
  · change CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (1 : Fin 6) (t, a)) ∈ _
    refine ⟨(unitInterval.symm t, Sum.inr (Sum.inl a)), ?_⟩
    rw [doubleCylinder_middle, unitInterval.symm_symm]
  · exact ⟨(t, Sum.inr (Sum.inr a)), rfl⟩
  · change CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (3 : Fin 6) (t, a)) ∈ _
    obtain ⟨b, hb⟩ := centralProject_edgeCylinder_opposite_exists C ε hε 0 (unitInterval.symm t) a
    refine ⟨(unitInterval.symm t, Sum.inl b), ?_⟩
    simpa only [show (0 + 3 : Fin 6) = 3 from by decide, doubleCylinder_first,
      unitInterval.symm_symm] using hb.symm
  · change CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (4 : Fin 6) (t, a)) ∈ _
    obtain ⟨b, hb⟩ := centralProject_edgeCylinder_opposite_exists C ε hε 1 (unitInterval.symm t) a
    refine ⟨(t, Sum.inr (Sum.inl b)), ?_⟩
    simpa only [show (1 + 3 : Fin 6) = 4 from by decide, doubleCylinder_middle,
      unitInterval.symm_symm] using hb.symm
  · change CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) (5 : Fin 6) (t, a)) ∈ _
    obtain ⟨b, hb⟩ := centralProject_edgeCylinder_opposite_exists C ε hε 2 (unitInterval.symm t) a
    refine ⟨(unitInterval.symm t, Sum.inr (Sum.inr b)), ?_⟩
    simpa only [show (2 + 3 : Fin 6) = 5 from by decide, doubleCylinder_last,
      unitInterval.symm_symm] using hb.symm

private theorem CuspCentralHomology.centralCollapseMap_edgeArc_mem_range_doubleCylinder
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (u : ToricSpace.CompactFibreTorus) :
    CuspCollapse.centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) ∈
      Set.range (doubleCylinder C ε hε) := by
  have h := edgeCylinder_mem_range_doubleCylinder C ε hε k t (hexagonCharacter k u)
  change
    CuspCollapse.centralProject C ε hε
        (CuspCollapse.centralPolarMap (u, edgeArcPositive (C 0) k t)) ∈
      _
  rwa [edgeCylinder_character_all] at h

private theorem
    CuspCentralHomology.range_doubleSuspensionMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Set.range (doubleSuspensionMap C ε hε) = Set.range (doubleCylinder C ε hε) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨⟨t, z⟩, rfl⟩ := Suspension.mk_surjective p
    exact ⟨(t, z), rfl⟩
  · rintro ⟨⟨t, z⟩, rfl⟩
    exact ⟨Suspension.mk t z, rfl⟩

private abbrev CuspCentralHomology.FundamentalCell :=
  ToricSpace.CompactFibreTorus × CuspHoneycombTiling.baseCell

private instance
    CuspCentralHomology.fundamentalCell_compactSpace : CompactSpace FundamentalCell := by
  let : CompactSpace CuspHoneycombTiling.baseCell :=
    isCompact_iff_compactSpace.mp CuspHoneycombTiling.baseCell_isCompact
  infer_instance

private def CuspCentralHomology.fundamentalCellInclusion (p : FundamentalCell) :
    CuspHoneycomb.PhasePlane :=
  (p.1, (p.2 : (CuspHoneycombTiling.Plane)))

private theorem CuspCentralHomology.fundamentalCellInclusion_continuous :
    Continuous fundamentalCellInclusion :=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)

private def CuspCentralHomology.fundamentalCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : FundamentalCell → CuspRetraction.QuotientCentralFibre C ε :=
  CuspHoneycomb.honeycombCollapseMap C ε hε ∘ fundamentalCellInclusion

private theorem CuspCentralHomology.fundamentalCellMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Continuous (fundamentalCellMap C ε hε) :=
  (CuspHoneycomb.honeycombCollapseMap_continuous C ε hε).comp fundamentalCellInclusion_continuous

private theorem
    CuspCentralHomology.honeycombCollapseMap_deck_invariant (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (v : (CuspHoneycombTiling.Lattice)) (p : CuspHoneycomb.PhasePlane) :
    CuspHoneycomb.honeycombCollapseMap C ε hε (CuspHoneycomb.honeycombDeckMap (C 0) v p) =
      CuspHoneycomb.honeycombCollapseMap C ε hε p := by
  apply (CuspHoneycomb.honeycombCollapseMap_eq_iff C ε hε _ _).mpr
  refine ⟨v, rfl, ?_⟩
  simp [CuspHoneycomb.honeycombDeckMap]

private theorem CuspCentralHomology.fundamentalCellMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Function.Surjective (fundamentalCellMap C ε hε) := by
  intro q
  obtain ⟨p, hp⟩ := CuspHoneycomb.honeycombCollapseMap_surjective C ε hε q
  obtain ⟨v, hv⟩ := CuspHoneycombTiling.exists_mem_cell p.2
  let y : CuspHoneycombTiling.baseCell := ⟨p.2 - CuspHoneycombTiling.latticePoint v, hv⟩
  refine ⟨(CuspCollapse.deckFibrePhase (C 0) (ToricSpace.cuspVector v) * p.1, y), ?_⟩
  change
    CuspHoneycomb.honeycombCollapseMap C ε hε
        (CuspCollapse.deckFibrePhase (C 0) (ToricSpace.cuspVector v) * p.1,
          p.2 - CuspHoneycombTiling.latticePoint v) =
      q
  simpa only [CuspHoneycomb.honeycombDeckMap, ToricSpace.cuspVector_cuspVector,
    CuspHoneycombTiling.latticePoint_neg, sub_eq_add_neg] using
    (honeycombCollapseMap_deck_invariant C ε hε (ToricSpace.cuspVector v) p).trans hp

private theorem
    CuspCentralHomology.fundamentalCellMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p q : FundamentalCell) :
    fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q ↔
      ∃ v : (CuspHoneycombTiling.Lattice),
        (p.2 : (CuspHoneycombTiling.Plane)) =
            (q.2 : (CuspHoneycombTiling.Plane)) +
              CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) ∧
          p.1⁻¹ * (CuspCollapse.deckFibrePhase (C 0) v * q.1) ∈
            MulAction.stabilizer ToricSpace.CompactFibreTorus
              ((CuspHoneycomb.honeycombHomeomorph (C 0) (p.2 : (CuspHoneycombTiling.Plane))).1 :
                ToricSpace.Space) :=
  CuspHoneycomb.honeycombCollapseMap_eq_iff C ε hε (fundamentalCellInclusion p)
    (fundamentalCellInclusion q)

private theorem
    CuspCentralHomology.fundamentalCellMap_isProperMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsProperMap (fundamentalCellMap C ε hε) := by
  let := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  exact (fundamentalCellMap_continuous C ε hε).isProperMap

private theorem
    CuspCentralHomology.fundamentalCellMap_isClosedMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsClosedMap (fundamentalCellMap C ε hε) :=
  (fundamentalCellMap_isProperMap C ε hε hε1 hC hR).isClosedMap

private theorem
    CuspCentralHomology.fundamentalCellMap_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : Topology.IsQuotientMap (fundamentalCellMap C ε hε) :=
  (fundamentalCellMap_isClosedMap C ε hε hε1 hC hR).isQuotientMap
    (fundamentalCellMap_continuous C ε hε) (fundamentalCellMap_surjective C ε hε)

private theorem
    CuspCentralHomology.fundamentalCellMap_eq_of_interior (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p q : FundamentalCell)
    (hp : (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) : p = q := by
  obtain ⟨u, hb, hphase⟩ := (fundamentalCellMap_eq_iff C ε hε p q).mp h
  have hpcell :
    (p.2 : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell (ToricSpace.cuspVector u) := by
    rw [hb, CuspHoneycombTiling.mem_cell, add_sub_cancel_right]
    exact q.2.2
  have hpinterior : (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior (CuspHoneycombTiling.cell 0) :=
    by simpa only [CuspHoneycombTiling.cell_zero] using hp
  have hcells :=
    (CuspHoneycombTiling.containingCells_eq_singleton_iff (p.2 : (CuspHoneycombTiling.Plane))
          0).mpr
      hpinterior
  have hcu : ToricSpace.cuspVector u = 0 := by
    have hu :
      ToricSpace.cuspVector u ∈
        {v : (CuspHoneycombTiling.Lattice) |
          (p.2 : (CuspHoneycombTiling.Plane)) ∈ CuspHoneycombTiling.cell v} :=
      hpcell
    simpa only [hcells, Set.mem_singleton_iff] using hu
  have hu : u = 0 := ToricSpace.cuspVector_injective (hcu.trans ToricSpace.cuspVector_zero.symm)
  subst u
  have hb' : (p.2 : (CuspHoneycombTiling.Plane)) = (q.2 : (CuspHoneycombTiling.Plane)) := by
    simpa only [ToricSpace.cuspVector_zero, CuspHoneycombTiling.latticePoint_zero, add_zero] using
      hb
  have hstab :=
    CuspHoneycomb.honeycombHomeomorph_stabilizer_eq_bot_of_mem_interior (C 0)
      (p.2 : (CuspHoneycombTiling.Plane)) 0 hpinterior
  have hphase' : p.1 = q.1 := by
    simpa only [hstab, Subgroup.mem_bot, CuspCollapse.deckFibrePhase_zero, one_mul,
      inv_mul_eq_one] using hphase
  exact Prod.ext hphase' (Subtype.ext hb')

private theorem CuspCentralHomology.fundamentalCellMap_interior_iff_of_eq
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell ↔
      (q.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
  constructor
  · intro hp
    have hpq := fundamentalCellMap_eq_of_interior C ε hε p q hp h
    simpa only [← hpq] using hp
  · intro hq
    have hqp := fundamentalCellMap_eq_of_interior C ε hε q p hq h.symm
    simpa only [← hqp] using hq

private theorem
    CuspCentralHomology.fundamentalCellMap_eq_or_frontier (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    p = q ∨
      ((p.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell ∧
        (q.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell) := by
  by_cases hp : (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell
  · exact Or.inl (fundamentalCellMap_eq_of_interior C ε hε p q hp h)
  · right
    rw [CuspHoneycombTiling.baseCell_isClosed.frontier_eq]
    refine ⟨⟨p.2.2, hp⟩, q.2.2, ?_⟩
    intro hq
    exact hp ((fundamentalCellMap_interior_iff_of_eq C ε hε p q h).mpr hq)

private theorem CuspCentralHomology.fundamentalCellMap_eq_base_or_frontier
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    (p.2 : (CuspHoneycombTiling.Plane)) = (q.2 : (CuspHoneycombTiling.Plane)) ∨
      ((p.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell ∧
        (q.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell) := by
  rcases fundamentalCellMap_eq_or_frontier C ε hε p q h with hpq | hfrontier
  · exact Or.inl (congrArg (fun r : FundamentalCell => (r.2 : (CuspHoneycombTiling.Plane))) hpq)
  · exact Or.inr hfrontier

private def CuspCentralHomology.Radial.cellGauge (x : CuspHoneycombTiling.Plane) : ℝ :=
  Max.max |2 * x 0 + x 1| (Max.max |x 0 - x 1| |x 0 + 2 * x 1|)

private theorem CuspCentralHomology.Radial.cellGauge_continuous : Continuous cellGauge :=
  (((continuous_const.mul (continuous_apply 0)).add (continuous_apply 1)).abs).max
    (((continuous_apply 0).sub (continuous_apply 1)).abs.max
      ((continuous_apply 0).add (continuous_const.mul (continuous_apply 1))).abs)

private theorem CuspCentralHomology.Radial.cellGauge_nonneg (x : CuspHoneycombTiling.Plane) :
    0 ≤ cellGauge x :=
  (abs_nonneg _).trans (le_max_left _ _)

@[simp]
private theorem CuspCentralHomology.Radial.cellGauge_zero :
    cellGauge (0 : CuspHoneycombTiling.Plane) = 0 := by simp [cellGauge]

private theorem CuspCentralHomology.Radial.cellGauge_smul (c : ℝ) (x : CuspHoneycombTiling.Plane) :
    cellGauge (c • x) = |c| * cellGauge x := by
  have h0 : 2 * (c * x 0) + c * x 1 = c * (2 * x 0 + x 1) := by ring
  have h1 : c * x 0 - c * x 1 = c * (x 0 - x 1) := by ring
  have h2 : c * x 0 + 2 * (c * x 1) = c * (x 0 + 2 * x 1) := by ring
  simp only [cellGauge, Pi.smul_apply, smul_eq_mul, h0, h1, h2, abs_mul,
    mul_max_of_nonneg _ _ (abs_nonneg c)]

private theorem CuspCentralHomology.Radial.cellGauge_smul_of_nonneg (c : ℝ) (hc : 0 ≤ c)
    (x : CuspHoneycombTiling.Plane) : cellGauge (c • x) = c * cellGauge x := by
  rw [cellGauge_smul, abs_of_nonneg hc]

@[simp]
private theorem CuspCentralHomology.Radial.cellGauge_eq_zero_iff (x : CuspHoneycombTiling.Plane) :
    cellGauge x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have h0 : |2 * x 0 + x 1| ≤ 0 := (le_max_left _ _).trans (le_of_eq hx)
    have h1 : |x 0 - x 1| ≤ 0 := (le_max_left _ _).trans ((le_max_right _ _).trans (le_of_eq hx))
    have h0' : 2 * x 0 + x 1 = 0 := abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _))
    have h1' : x 0 - x 1 = 0 := abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    funext i
    fin_cases i
    · change x 0 = 0
      linarith
    · change x 1 = 0
      linarith
  · rintro rfl
    exact cellGauge_zero

private theorem CuspCentralHomology.Radial.cellGauge_pos_iff (x : CuspHoneycombTiling.Plane) :
    0 < cellGauge x ↔ x ≠ 0 := by
  constructor
  · intro hx hzero
    simp only [hzero, cellGauge_zero, lt_self_iff_false] at hx
  · intro hx
    apply lt_of_le_of_ne (cellGauge_nonneg x)
    intro h
    exact hx ((cellGauge_eq_zero_iff x).mp h.symm)

private theorem CuspCentralHomology.Radial.mem_baseCell_iff (x : CuspHoneycombTiling.Plane) :
    x ∈ CuspHoneycombTiling.baseCell ↔ cellGauge x ≤ 1 := by
  simp only [CuspHoneycombTiling.mem_baseCell, cellGauge, max_le_iff]

private theorem
    CuspCentralHomology.Radial.mem_interior_baseCell_iff (x : CuspHoneycombTiling.Plane) :
    x ∈ interior CuspHoneycombTiling.baseCell ↔ cellGauge x < 1 := by
  constructor
  · intro hx
    have hle := (mem_baseCell_iff x).mp (interior_subset hx)
    apply lt_of_le_of_ne hle
    intro heq
    have hopen : IsOpen ((fun a : ℝ => a • x) ⁻¹' interior CuspHoneycombTiling.baseCell) :=
      isOpen_interior.preimage (continuous_id.smul continuous_const)
    have hone : (1 : ℝ) ∈ (fun a : ℝ => a • x) ⁻¹' interior CuspHoneycombTiling.baseCell := by
      simpa only [Set.mem_preimage, one_smul] using hx
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 1 hone
    have ha : (1 + δ / 2) • x ∈ interior CuspHoneycombTiling.baseCell :=
      hball
        (by
          change Dist.dist (1 + δ / 2) (1 : ℝ) < δ
          rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
          exact half_lt_self hδ)
    have hb := (mem_baseCell_iff _).mp (interior_subset ha)
    rw [cellGauge_smul_of_nonneg _ (by linarith), heq, mul_one] at hb
    linarith
  · intro hx
    have hopen : IsOpen {y : CuspHoneycombTiling.Plane | cellGauge y < 1} :=
      isOpen_lt cellGauge_continuous continuous_const
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (hopen.mem_nhds hx)
    intro y hy
    exact (mem_baseCell_iff y).mpr hy.le

private theorem
    CuspCentralHomology.Radial.mem_frontier_baseCell_iff (x : CuspHoneycombTiling.Plane) :
    x ∈ frontier CuspHoneycombTiling.baseCell ↔ cellGauge x = 1 := by
  rw [frontier, CuspHoneycombTiling.baseCell_isClosed.closure_eq, Set.mem_sdiff, mem_baseCell_iff,
    mem_interior_baseCell_iff, not_lt]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

private def CuspCentralHomology.fundamentalRadius (p : FundamentalCell) : ℝ :=
  Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane))

private theorem CuspCentralHomology.fundamentalRadius_continuous : Continuous fundamentalRadius :=
  Radial.cellGauge_continuous.comp (continuous_subtype_val.comp continuous_snd)

private theorem
    CuspCentralHomology.fundamentalRadius_eq_of_map_eq (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p q : FundamentalCell)
    (h : fundamentalCellMap C ε hε p = fundamentalCellMap C ε hε q) :
    fundamentalRadius p = fundamentalRadius q := by
  change
    Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) =
      Radial.cellGauge (q.2 : (CuspHoneycombTiling.Plane))
  rcases fundamentalCellMap_eq_base_or_frontier C ε hε p q h with he | ⟨hp, hq⟩
  · exact congrArg Radial.cellGauge he
  · rw [(Radial.mem_frontier_baseCell_iff _).mp hp, (Radial.mem_frontier_baseCell_iff _).mp hq]

private def
    CuspCentralHomology.centralRadius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    CuspRetraction.QuotientCentralFibre C ε → ℝ :=
  CuspHoneycombHexagon.CommonFibres.descend (fundamentalCellMap C ε hε) fundamentalRadius
    (fundamentalCellMap_surjective C ε hε)

@[simp]
private theorem
    CuspCentralHomology.centralRadius_fundamentalCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p : FundamentalCell) :
    centralRadius C ε hε (fundamentalCellMap C ε hε p) =
      Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (fundamentalCellMap C ε hε) fundamentalRadius
    (fundamentalCellMap_surjective C ε hε) (fundamentalRadius_eq_of_map_eq C ε hε) p

private def
    CuspCentralHomology.centralBoundary (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set (CuspRetraction.QuotientCentralFibre C ε) :=
  {q | centralRadius C ε hε q = 1}

private def CuspCentralHomology.outerRegion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) : Set (CuspRetraction.QuotientCentralFibre C ε) :=
  {q | a < centralRadius C ε hε q}

private def
    CuspCentralHomology.innerRegion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set (CuspRetraction.QuotientCentralFibre C ε) :=
  {q | centralRadius C ε hε q < 1}

private theorem CuspCentralHomology.fundamentalCellMap_mem_centralBoundary_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ centralBoundary C ε hε ↔
      (p.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell := by
  change centralRadius C ε hε (fundamentalCellMap C ε hε p) = 1 ↔ _
  rw [centralRadius_fundamentalCellMap]
  exact (Radial.mem_frontier_baseCell_iff _).symm

private theorem CuspCentralHomology.fundamentalCellMap_mem_innerRegion_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ innerRegion C ε hε ↔
      (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
  change centralRadius C ε hε (fundamentalCellMap C ε hε p) < 1 ↔ _
  rw [centralRadius_fundamentalCellMap]
  exact (Radial.mem_interior_baseCell_iff _).symm

private theorem
    CuspCentralHomology.centralBoundary_eq_image (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    centralBoundary C ε hε =
      CuspHoneycomb.honeycombCollapseMap C ε hε ''
        ((Set.univ : Set ToricSpace.CompactFibreTorus) ×ˢ
          frontier CuspHoneycombTiling.baseCell) := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε q
    exact
      ⟨(p.1, (p.2 : (CuspHoneycombTiling.Plane))),
        ⟨Set.mem_univ _, (fundamentalCellMap_mem_centralBoundary_iff C ε hε p).mp hq⟩, rfl⟩
  · rintro ⟨⟨φ, x⟩, ⟨_, hx⟩, rfl⟩
    let p : FundamentalCell := (φ, ⟨x, CuspHoneycombTiling.baseCell_isClosed.frontier_subset hx⟩)
    exact (fundamentalCellMap_mem_centralBoundary_iff C ε hε p).mpr hx

private theorem
    CuspCentralHomology.centralBoundary_subset_outerRegion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : a < 1) : centralBoundary C ε hε ⊆ outerRegion C ε hε a := by
  intro q hq
  change a < centralRadius C ε hε q
  change centralRadius C ε hε q = 1 at hq
  rwa [hq]

private theorem CuspCentralHomology.outerRegion_union_innerRegion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : a < 1) :
    outerRegion C ε hε a ∪ innerRegion C ε hε = Set.univ := by
  apply Set.eq_univ_of_forall
  intro q
  by_cases hq : centralRadius C ε hε q < 1
  · exact Or.inr hq
  · exact Or.inl (ha.trans_le (le_of_not_gt hq))

private theorem
    CuspCentralHomology.centralRadius_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : Continuous (centralRadius C ε hε) :=
  CuspHoneycombHexagon.CommonFibres.descend_continuous (fundamentalCellMap C ε hε)
    fundamentalRadius (fundamentalCellMap_surjective C ε hε)
    (fundamentalCellMap_isQuotientMap C ε hε hε1 hC hR) fundamentalRadius_continuous
    (fundamentalRadius_eq_of_map_eq C ε hε)

private theorem CuspCentralHomology.outerRegion_isOpen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) : IsOpen (outerRegion C ε hε a) :=
  isOpen_lt continuous_const (centralRadius_continuous C ε hε hε1 hC hR)

private theorem CuspCentralHomology.innerRegion_isOpen (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsOpen (innerRegion C ε hε) :=
  isOpen_lt (centralRadius_continuous C ε hε hε1 hC hR) continuous_const

private theorem CuspCentralHomology.honeycombHomeomorph_baseCell_coe (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (x : CuspHoneycombTiling.baseCell) :
    ((CuspHoneycomb.honeycombHomeomorph C₀ (x : (CuspHoneycombTiling.Plane))).1 :
        ToricSpace.Space) =
      ((CuspHoneycombHexagon.compatibleCellHomeomorph C₀ x).1 : ToricSpace.Space) := by
  let y : CuspHoneycombTiling.cell 0 := CuspHoneycombTiling.cellTranslationHomeomorph 0 x
  have hy : (y : (CuspHoneycombTiling.Plane)) = (x : (CuspHoneycombTiling.Plane)) := by
    change
      (x : (CuspHoneycombTiling.Plane)) + CuspHoneycombTiling.latticePoint 0 =
        (x : (CuspHoneycombTiling.Plane))
    rw [CuspHoneycombTiling.latticePoint_zero, add_zero]
  have hnorm : (CuspHoneycombTiling.cellTranslationHomeomorph 0).symm y = x :=
    (CuspHoneycombTiling.cellTranslationHomeomorph 0).symm_apply_apply x
  have h := CuspHoneycomb.honeycombHomeomorph_cell_coe C₀ 0 y
  rw [hy, hnorm, ToricSpace.cuspVector_zero, neg_zero, ToricSpace.twistedTranslate_zero] at h
  exact h

private def CuspCentralHomology.edgeArcBase (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) : CuspHoneycombTiling.baseCell :=
  (CuspHoneycombHexagon.compatibleCellHomeomorph C₀).symm
    (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1

@[simp]
private theorem
    CuspCentralHomology.compatibleCellHomeomorph_edgeArcBase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    CuspHoneycombHexagon.compatibleCellHomeomorph C₀ (edgeArcBase C₀ k t) =
      (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1 :=
  (CuspHoneycombHexagon.compatibleCellHomeomorph C₀).apply_symm_apply _

private theorem
    CuspCentralHomology.edgeArcBase_mem_frontier (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6)
    (t : unitInterval) :
    (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell := by
  rw [CuspHoneycombTiling.frontier_baseCell, Set.mem_iUnion]
  refine ⟨k, (edgeArcBase C₀ k t).2, ?_⟩
  apply
    (CuspHoneycombHexagon.compatibleCellHomeomorph_mem_boundary_iff C₀ (edgeArcBase C₀ k t) k).mp
  rw [compatibleCellHomeomorph_edgeArcBase]
  exact (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).2

@[simp]
private theorem CuspCentralHomology.honeycombHomeomorph_edgeArcBase (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    CuspHoneycomb.honeycombHomeomorph C₀ (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane)) =
      edgeArcPositive C₀ k t := by
  apply Subtype.ext
  apply Subtype.ext
  change
    ((CuspHoneycomb.honeycombHomeomorph C₀ (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane))).1 :
        ToricSpace.Space) =
      ((CuspHoneycombHexagon.compatibleBoundaryArc C₀ k t).1.1 : ToricSpace.Space)
  rw [honeycombHomeomorph_baseCell_coe, compatibleCellHomeomorph_edgeArcBase]

private theorem
    CuspCentralHomology.exists_edgeArcBase_of_mem_frontier (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (x : (CuspHoneycombTiling.Plane)) (hx : x ∈ frontier CuspHoneycombTiling.baseCell) :
    ∃ k : Fin 6, ∃ t : unitInterval, (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane)) = x := by
  obtain ⟨k, hbase, hside⟩ :=
    Set.mem_iUnion.mp ((congrArg (x ∈ ·) CuspHoneycombTiling.frontier_baseCell).mp hx)
  let a : CuspHoneycombTiling.baseCell := ⟨x, hbase⟩
  have ha :
    CuspHoneycombHexagon.compatibleCellHomeomorph C₀ a ∈
      CuspHoneycombHexagon.positiveBoundary k :=
    (CuspHoneycombHexagon.compatibleCellHomeomorph_mem_boundary_iff C₀ a k).mpr hside
  obtain ⟨t, ht⟩ :=
    (CuspHoneycombHexagon.compatibleBoundaryArc C₀ k).surjective
      ⟨CuspHoneycombHexagon.compatibleCellHomeomorph C₀ a, ha⟩
  refine ⟨k, t, ?_⟩
  have hcell : edgeArcBase C₀ k t = a := by
    apply (CuspHoneycombHexagon.compatibleCellHomeomorph C₀).injective
    rw [compatibleCellHomeomorph_edgeArcBase]
    exact congrArg Subtype.val ht
  exact congrArg Subtype.val hcell

private theorem
    CuspCentralHomology.honeycombHomeomorph_mem_edgeArcs_iff (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (x : (CuspHoneycombTiling.Plane)) :
    (∃ k : Fin 6,
        ∃ t : unitInterval, CuspHoneycomb.honeycombHomeomorph C₀ x = edgeArcPositive C₀ k t) ↔
      x ∈ frontier CuspHoneycombTiling.baseCell := by
  constructor
  · rintro ⟨k, t, h⟩
    have hx : x = (edgeArcBase C₀ k t : (CuspHoneycombTiling.Plane)) :=
      (CuspHoneycomb.honeycombHomeomorph C₀).injective
        (h.trans (honeycombHomeomorph_edgeArcBase C₀ k t).symm)
    rw [hx]
    exact edgeArcBase_mem_frontier C₀ k t
  · intro hx
    obtain ⟨k, t, ht⟩ := exists_edgeArcBase_of_mem_frontier C₀ x hx
    refine ⟨k, t, ?_⟩
    rw [← ht, honeycombHomeomorph_edgeArcBase]

private theorem
    CuspCentralHomology.mem_centralBoundary_iff_edgeArc (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (q : CuspRetraction.QuotientCentralFibre C ε) :
    q ∈ centralBoundary C ε hε ↔
      ∃ k : Fin 6,
        ∃ t : unitInterval,
          ∃ u : ToricSpace.CompactFibreTorus,
            CuspCollapse.centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) = q := by
  rw [centralBoundary_eq_image]
  constructor
  · rintro ⟨⟨u, x⟩, ⟨_, hx⟩, hq⟩
    obtain ⟨k, t, ht⟩ := (honeycombHomeomorph_mem_edgeArcs_iff (C 0) x).mpr hx
    refine ⟨k, t, u, ?_⟩
    change
      CuspCollapse.centralCollapseMap C ε hε (u, CuspHoneycomb.honeycombHomeomorph (C 0) x) =
        q at hq
    rw [ht] at hq
    exact hq
  · rintro ⟨k, t, u, hq⟩
    refine
      ⟨(u, (edgeArcBase (C 0) k t : (CuspHoneycombTiling.Plane))),
        ⟨Set.mem_univ _, edgeArcBase_mem_frontier (C 0) k t⟩, ?_⟩
    change
      CuspCollapse.centralCollapseMap C ε hε
          (u,
            CuspHoneycomb.honeycombHomeomorph (C 0)
              (edgeArcBase (C 0) k t : (CuspHoneycombTiling.Plane))) =
        q
    rw [honeycombHomeomorph_edgeArcBase]
    exact hq

private theorem CuspCentralHomology.centralCollapseMap_edgeArc_mem_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6) (t : unitInterval)
    (u : ToricSpace.CompactFibreTorus) :
    CuspCollapse.centralCollapseMap C ε hε (u, edgeArcPositive (C 0) k t) ∈
      centralBoundary C ε hε :=
  (mem_centralBoundary_iff_edgeArc C ε hε _).mpr ⟨k, t, u, rfl⟩

private theorem CuspCentralHomology.centralProject_edgeCylinder_mem_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (k : Fin 6)
    (p : unitInterval × Circle) :
    CuspCollapse.centralProject C ε hε (edgeCylinder (C 0) k p) ∈ centralBoundary C ε hε :=
  centralCollapseMap_edgeArc_mem_centralBoundary C ε hε k p.1 (hexagonCharacterSection k p.2)

private def
    CuspCentralHomology.threeCirclesIntersectionHomologyZeroEquiv {X : Type} [TopologicalSpace X]
    (U V : Set X) (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) :
    SingularMayerVietoris.SingularHomology (U ∩ V : Set X) 0 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 0).toAddEquiv.trans
      threeCirclesHomologyZeroEquiv.toAddEquiv).toIntLinearEquiv

private theorem CuspCentralHomology.threeCirclesIntersectionHomologyZeroEquiv_map {X : Type}
    [TopologicalSpace X] (U V : Set X) {Y : Type} [TopologicalSpace Y] [PathConnectedSpace Y]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) (f : C((U ∩ V : Set X), Y))
    (a : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) 0) :
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv Y
        (SingularMayerVietoris.singularHomologyMap f 0 a) =
      sumCoordinates (threeCirclesIntersectionHomologyZeroEquiv U V e a) :=
  threeCirclesHomologyZeroEquiv_map_homotopyEquiv e f a

private theorem CuspCentralHomology.threeCirclesIntersectionLeftMap_zero_iff {X : Type}
    [TopologicalSpace X] (U V : Set X) [PathConnectedSpace U] [PathConnectedSpace V]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles)
    (a : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) 0) :
    SingularMayerVietoris.leftHomologyMap U V 0 a = 0 ↔
      sumCoordinates (threeCirclesIntersectionHomologyZeroEquiv U V e a) = 0 := by
  constructor
  · intro ha
    have hleft :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) 0 a =
        0 := by
      rw [SingularMayerVietoris.leftHomologyMap_apply] at ha
      exact congrArg Prod.fst ha
    have hsum :=
      threeCirclesIntersectionHomologyZeroEquiv_map U V e
        (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) a
    rw [hleft, map_zero] at hsum
    exact hsum.symm
  · intro ha
    have hleft :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_left : U ∩ V ⊆ U)) 0 a =
        0 := by
      apply (PeriodTorusHigherHomology.connectedHomologyZeroEquiv U).injective
      rw [map_zero, threeCirclesIntersectionHomologyZeroEquiv_map U V e]
      exact ha
    have hright :
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.inclusion (Set.inter_subset_right : U ∩ V ⊆ V)) 0 a =
        0 := by
      apply (PeriodTorusHigherHomology.connectedHomologyZeroEquiv V).injective
      rw [map_zero, threeCirclesIntersectionHomologyZeroEquiv_map U V e]
      exact ha
    rw [SingularMayerVietoris.leftHomologyMap_apply, hleft, hright, neg_zero]
    rfl

private theorem
    CuspCentralHomology.threeCirclesIntersection_mem_ker_iff {X : Type} [TopologicalSpace X]
    (U V : Set X) [PathConnectedSpace U] [PathConnectedSpace V]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles)
    (a : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) 0) :
    a ∈ LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) ↔
      threeCirclesIntersectionHomologyZeroEquiv U V e a ∈ LinearMap.ker sumCoordinates :=
  threeCirclesIntersectionLeftMap_zero_iff U V e a

private def
    CuspCentralHomology.threeCirclesIntersectionKernelToSumEquiv {X : Type} [TopologicalSpace X]
    (U V : Set X) [PathConnectedSpace U] [PathConnectedSpace V]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) :
    LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) ≃ₗ[ℤ]
      LinearMap.ker sumCoordinates :=
  ({    toFun
          a :=
          ⟨threeCirclesIntersectionHomologyZeroEquiv U V e a,
            (threeCirclesIntersection_mem_ker_iff U V e a).mp a.property⟩
        invFun
          b :=
          ⟨(threeCirclesIntersectionHomologyZeroEquiv U V e).symm b,
            by
            apply (threeCirclesIntersection_mem_ker_iff U V e _).mpr
            simpa only [LinearEquiv.apply_symm_apply] using b.property⟩
        left_inv
          a := Subtype.ext ((threeCirclesIntersectionHomologyZeroEquiv U V e).symm_apply_apply a)
        right_inv
          b := Subtype.ext ((threeCirclesIntersectionHomologyZeroEquiv U V e).apply_symm_apply b)
        map_add' a
          b := Subtype.ext ((threeCirclesIntersectionHomologyZeroEquiv U V e).map_add a b) } :
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) ≃+
        LinearMap.ker sumCoordinates).toIntLinearEquiv

private def CuspCentralHomology.threeCirclesIntersectionKernelEquiv {X : Type} [TopologicalSpace X]
    (U V : Set X) [PathConnectedSpace U] [PathConnectedSpace V]
    (e : (U ∩ V : Set X) ≃ₕ ThreeCircles) :
    LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((threeCirclesIntersectionKernelToSumEquiv U V e).toAddEquiv.trans
      sumCoordinatesKernelEquiv.toAddEquiv).toIntLinearEquiv

private abbrev CuspCentralHomology.ThreeCircleSuspension :=
  Suspension ThreeCircles

private def CuspCentralHomology.threeCircleSuspensionHomologyZeroEquiv :
    SingularMayerVietoris.SingularHomology ThreeCircleSuspension 0 ≃ₗ[ℤ] ℤ :=
  PeriodTorusHigherHomology.connectedHomologyZeroEquiv ThreeCircleSuspension

private def CuspCentralHomology.threeCircleSuspensionHomologyOneEquiv :
    SingularMayerVietoris.SingularHomology ThreeCircleSuspension 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (contractibleCoverHomologyOneEquivKernel
        ((CuspCentralHomology.Suspension.northOpen :
          Set CuspCentralHomology.ThreeCircleSuspension))
        ((CuspCentralHomology.Suspension.southOpen :
          Set CuspCentralHomology.ThreeCircleSuspension))
        Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover).trans
    (threeCirclesIntersectionKernelEquiv
      ((CuspCentralHomology.Suspension.northOpen : Set CuspCentralHomology.ThreeCircleSuspension))
      ((CuspCentralHomology.Suspension.southOpen : Set CuspCentralHomology.ThreeCircleSuspension))
      (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)))

private def CuspCentralHomology.threeCircleSuspensionHomologyTwoEquiv :
    SingularMayerVietoris.SingularHomology ThreeCircleSuspension 2 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (contractibleCoverHomologyHigherEquiv
        ((CuspCentralHomology.Suspension.northOpen :
          Set CuspCentralHomology.ThreeCircleSuspension))
        ((CuspCentralHomology.Suspension.southOpen :
          Set CuspCentralHomology.ThreeCircleSuspension))
        Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover 0).trans
    ((PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)) 1).trans
      threeCirclesHomologyOneEquiv)

private theorem CuspCentralHomology.threeCircleSuspension_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology ThreeCircleSuspension (n + 3)) := by
  let := threeCircles_homology_subsingleton n
  exact
    ((contractibleCoverHomologyHigherEquiv
            ((CuspCentralHomology.Suspension.northOpen :
              Set CuspCentralHomology.ThreeCircleSuspension))
            ((CuspCentralHomology.Suspension.southOpen :
              Set CuspCentralHomology.ThreeCircleSuspension))
            Suspension.northOpen_isOpen Suspension.southOpen_isOpen Suspension.open_cover
            (n + 1)).trans
        (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
          (Suspension.middleBandHomotopyEquiv (X := ThreeCircles))
          (n + 2))).injective.subsingleton

private def CuspCentralHomology.threeCircleSuspensionBetti : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | _ => 0

private def CuspCentralHomology.threeCircleSuspensionHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology ThreeCircleSuspension n ≃ₗ[ℤ]
      (Fin (threeCircleSuspensionBetti n) → ℤ) := by
  cases n with
  | zero =>
    exact threeCircleSuspensionHomologyZeroEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | succ n =>
    cases n with
    | zero => exact threeCircleSuspensionHomologyOneEquiv
    | succ n =>
      cases n with
      | zero => exact threeCircleSuspensionHomologyTwoEquiv
      | succ
        n =>
        change
          SingularMayerVietoris.SingularHomology ThreeCircleSuspension (n + 3) ≃ₗ[ℤ] (Fin 0 → ℤ)
        letI := threeCircleSuspension_homology_subsingleton n
        exact LinearEquiv.ofSubsingleton _ _

private theorem
    CuspCentralHomology.doubleCylinder_mem_centralBoundary (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p : unitInterval × ThreeCircles) :
    doubleCylinder C ε hε p ∈ centralBoundary C ε hε := by
  rcases p with ⟨t, a | (a | a)⟩
  · exact centralProject_edgeCylinder_mem_centralBoundary C ε hε 0 (t, a)
  · exact centralProject_edgeCylinder_mem_centralBoundary C ε hε 1 (unitInterval.symm t, a)
  · exact centralProject_edgeCylinder_mem_centralBoundary C ε hε 2 (t, a)

private theorem CuspCentralHomology.range_doubleCylinder_eq_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set.range (doubleCylinder C ε hε) = centralBoundary C ε hε := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    exact doubleCylinder_mem_centralBoundary C ε hε p
  · intro hq
    obtain ⟨k, t, u, hu⟩ := (mem_centralBoundary_iff_edgeArc C ε hε q).mp hq
    rw [← hu]
    exact centralCollapseMap_edgeArc_mem_range_doubleCylinder C ε hε k t u

private theorem CuspCentralHomology.range_doubleSuspensionMap_eq_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set.range (doubleSuspensionMap C ε hε) = centralBoundary C ε hε := by
  rw [range_doubleSuspensionMap, range_doubleCylinder_eq_centralBoundary]

private theorem CuspCentralHomology.doubleSuspensionMap_mem_centralBoundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : ThreeCircleSuspension) :
    doubleSuspensionMap C ε hε p ∈ centralBoundary C ε hε := by
  rw [← range_doubleSuspensionMap_eq_centralBoundary]
  exact Set.mem_range_self p

private def
    CuspCentralHomology.doubleSuspensionBoundaryMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : ThreeCircleSuspension) : centralBoundary C ε hε :=
  ⟨doubleSuspensionMap C ε hε p, doubleSuspensionMap_mem_centralBoundary C ε hε p⟩

private theorem CuspCentralHomology.doubleSuspensionBoundaryMap_continuous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Continuous (doubleSuspensionBoundaryMap C ε hε) :=
  (doubleSuspensionMap_continuous C ε hε).subtype_mk _

private theorem CuspCentralHomology.doubleSuspensionBoundaryMap_bijective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Function.Bijective (doubleSuspensionBoundaryMap C ε hε) := by
  constructor
  · intro p q h
    exact doubleSuspensionMap_injective C ε hε (congrArg Subtype.val h)
  · rintro ⟨q, hq⟩
    rw [← range_doubleSuspensionMap_eq_centralBoundary] at hq
    obtain ⟨p, hp⟩ := hq
    exact ⟨p, Subtype.ext hp⟩

private def
    CuspCentralHomology.doubleSuspensionBoundaryEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : ThreeCircleSuspension ≃ centralBoundary C ε hε :=
  Equiv.ofBijective (doubleSuspensionBoundaryMap C ε hε)
    (doubleSuspensionBoundaryMap_bijective C ε hε)

private def
    CuspCentralHomology.doubleSuspensionBoundaryHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : ThreeCircleSuspension ≃ₜ centralBoundary C ε hε := by
  letI := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  exact
    (doubleSuspensionBoundaryEquiv C ε hε).toHomeomorphOfContinuousClosed
      (doubleSuspensionBoundaryMap_continuous C ε hε)
      (doubleSuspensionBoundaryMap_continuous C ε hε).isClosedMap

private def
    CuspCentralHomology.centralBoundarySuspensionHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : centralBoundary C ε hε ≃ₜ ThreeCircleSuspension :=
  (doubleSuspensionBoundaryHomeomorph C ε hε hε1 hC hR).symm

@[simp]
private theorem CuspCentralHomology.centralBoundarySuspensionHomeomorph_symm_coe
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : ThreeCircleSuspension) :
    ((centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm p :
        CuspRetraction.QuotientCentralFibre C ε) =
      doubleSuspensionMap C ε hε p :=
  rfl


private def
    CuspCentralHomology.centralBoundaryHomologyOneEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    SingularMayerVietoris.SingularHomology (centralBoundary C ε hε) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv
        (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR) 1).trans
    threeCircleSuspensionHomologyOneEquiv

private abbrev CuspCentralHomology.InteriorPhaseCell :=
  ToricSpace.CompactFibreTorus × (interior CuspHoneycombTiling.baseCell)

private def CuspCentralHomology.interiorCellInclusion (p : InteriorPhaseCell) : FundamentalCell :=
  (p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), interior_subset p.2.2⟩)

@[simp]
private theorem CuspCentralHomology.interiorCellInclusion_snd_coe (p : InteriorPhaseCell) :
    ((interiorCellInclusion p).2 : (CuspHoneycombTiling.Plane)) =
      (p.2 : (CuspHoneycombTiling.Plane)) :=
  rfl

private theorem
    CuspCentralHomology.interiorCellInclusion_continuous : Continuous interiorCellInclusion :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

private theorem CuspCentralHomology.interiorCellInclusion_injective :
    Function.Injective interiorCellInclusion := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun r : FundamentalCell => r.1) hpq
  · apply Subtype.ext
    exact congrArg (fun r : FundamentalCell => (r.2 : (CuspHoneycombTiling.Plane))) hpq

private def
    CuspCentralHomology.interiorCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    InteriorPhaseCell → CuspRetraction.QuotientCentralFibre C ε :=
  fundamentalCellMap C ε hε ∘ interiorCellInclusion

private theorem CuspCentralHomology.interiorCellMap_eq_fundamentalCellMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : InteriorPhaseCell) :
    interiorCellMap C ε hε p = fundamentalCellMap C ε hε (interiorCellInclusion p) :=
  rfl

@[simp]
private theorem CuspCentralHomology.interiorCellMap_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : InteriorPhaseCell) :
    interiorCellMap C ε hε p =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) :=
  rfl

private theorem
    CuspCentralHomology.interiorCellMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Continuous (interiorCellMap C ε hε) :=
  (fundamentalCellMap_continuous C ε hε).comp interiorCellInclusion_continuous

private theorem
    CuspCentralHomology.interiorCellMap_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : Function.Injective (interiorCellMap C ε hε) := by
  intro p q hpq
  apply interiorCellInclusion_injective
  exact
    fundamentalCellMap_eq_of_interior C ε hε (interiorCellInclusion p) (interiorCellInclusion q)
      p.2.2 hpq

private def
    CuspCentralHomology.interiorImage (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    Set (CuspRetraction.QuotientCentralFibre C ε) :=
  Set.range (interiorCellMap C ε hε)

private theorem CuspCentralHomology.fundamentalCellMap_mem_interiorImage_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ interiorImage C ε hε ↔
      (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell := by
  constructor
  · rintro ⟨q, hq⟩
    have he := fundamentalCellMap_eq_of_interior C ε hε (interiorCellInclusion q) p q.2.2 hq
    rw [← he]
    exact q.2.2
  · intro hp
    exact ⟨(p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), hp⟩), rfl⟩

private def CuspCentralHomology.interiorCellMapToImage (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : InteriorPhaseCell) : interiorImage C ε hε :=
  ⟨interiorCellMap C ε hε p, Set.mem_range_self p⟩

private theorem
    CuspCentralHomology.interiorCellMapToImage_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Continuous (interiorCellMapToImage C ε hε) :=
  (interiorCellMap_continuous C ε hε).subtype_mk _

private theorem
    CuspCentralHomology.interiorCellMapToImage_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Function.Surjective (interiorCellMapToImage C ε hε) := by
  rintro ⟨y, p, hp⟩
  exact ⟨p, Subtype.ext hp⟩

private theorem
    CuspCentralHomology.interiorCellMapToImage_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : Function.Injective (interiorCellMapToImage C ε hε) := by
  intro p q hpq
  exact interiorCellMap_injective C ε hε (congrArg Subtype.val hpq)

private def
    CuspCentralHomology.interiorPreimageHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : InteriorPhaseCell ≃ₜ (fundamentalCellMap C ε hε ⁻¹' interiorImage C ε hε)
    where
  toFun
    p := ⟨interiorCellInclusion p, (fundamentalCellMap_mem_interiorImage_iff C ε hε _).mpr p.2.2⟩
  invFun
    p :=
    (p.1.1,
      ⟨(p.1.2 : (CuspHoneycombTiling.Plane)),
        (fundamentalCellMap_mem_interiorImage_iff C ε hε p.1).mp p.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := interiorCellInclusion_continuous.subtype_mk _
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)

private theorem
    CuspCentralHomology.interiorCellMapToImage_isProperMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsProperMap (interiorCellMapToImage C ε hε) := by
  have hf :=
    (fundamentalCellMap_isProperMap C ε hε hε1 hC hR).restrictPreimage (interiorImage C ε hε)
  have hg := (interiorPreimageHomeomorph C ε hε).isProperMap
  have hc := hf.comp hg
  have he :
    (interiorImage C ε hε).restrictPreimage (fundamentalCellMap C ε hε) ∘
        interiorPreimageHomeomorph C ε hε =
      interiorCellMapToImage C ε hε := by
    funext p
    apply Subtype.ext
    rfl
  rw [he] at hc
  exact hc

private theorem
    CuspCentralHomology.interiorCellMapToImage_isClosedMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsClosedMap (interiorCellMapToImage C ε hε) :=
  (interiorCellMapToImage_isProperMap C ε hε hε1 hC hR).isClosedMap

private def CuspCentralHomology.interiorCellHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : InteriorPhaseCell ≃ₜ interiorImage C ε hε :=
  Equiv.toHomeomorphOfContinuousClosed
    (Equiv.ofBijective (interiorCellMapToImage C ε hε)
      ⟨interiorCellMapToImage_injective C ε hε, interiorCellMapToImage_surjective C ε hε⟩)
    (interiorCellMapToImage_continuous C ε hε)
    (interiorCellMapToImage_isClosedMap C ε hε hε1 hC hR)

@[simp]
private theorem
    CuspCentralHomology.interiorCellHomeomorph_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : InteriorPhaseCell) :
    (interiorCellHomeomorph C ε hε hε1 hC hR p : CuspRetraction.QuotientCentralFibre C ε) =
      interiorCellMap C ε hε p :=
  rfl

private theorem CuspCentralHomology.innerRegion_eq_interiorImage (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : innerRegion C ε hε = interiorImage C ε hε := by
  ext q
  obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε q
  exact
    (fundamentalCellMap_mem_innerRegion_iff C ε hε p).trans
      (fundamentalCellMap_mem_interiorImage_iff C ε hε p).symm

private def CuspCentralHomology.innerRegionHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : InteriorPhaseCell ≃ₜ innerRegion C ε hε :=
  (interiorCellHomeomorph C ε hε hε1 hC hR).trans
    (Homeomorph.setCongr (innerRegion_eq_interiorImage C ε hε).symm)

@[simp]
private theorem
    CuspCentralHomology.innerRegionHomeomorph_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : InteriorPhaseCell) :
    (innerRegionHomeomorph C ε hε hε1 hC hR p : CuspRetraction.QuotientCentralFibre C ε) =
      interiorCellMap C ε hε p :=
  interiorCellHomeomorph_coe C ε hε hε1 hC hR p

private theorem
    CuspCentralHomology.innerRegionHomeomorph_honeycomb (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : InteriorPhaseCell) :
    (innerRegionHomeomorph C ε hε hε1 hC hR p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) := by
  rw [innerRegionHomeomorph_coe, interiorCellMap_apply]

private theorem CuspCentralHomology.innerRegionHomeomorph_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : InteriorPhaseCell) :
    centralRadius C ε hε
        (innerRegionHomeomorph C ε hε hε1 hC hR p : CuspRetraction.QuotientCentralFibre C ε) =
      Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) := by
  rw [innerRegionHomeomorph_coe, interiorCellMap_eq_fundamentalCellMap,
    centralRadius_fundamentalCellMap, interiorCellInclusion_snd_coe]

private abbrev CuspCentralHomology.Radial.InteriorCell :=
  interior CuspHoneycombTiling.baseCell

private def CuspCentralHomology.Radial.interiorCellZero : InteriorCell :=
  ⟨0, (mem_interior_baseCell_iff 0).mpr (by rw [cellGauge_zero]; norm_num)⟩

private def CuspCentralHomology.Radial.interiorCellContract (s : unitInterval) (x : InteriorCell) :
    InteriorCell :=
  ⟨(1 - (s : ℝ)) • (x : CuspHoneycombTiling.Plane),
    by
    apply (mem_interior_baseCell_iff _).mpr
    rw [cellGauge_smul_of_nonneg _ (sub_nonneg.mpr s.2.2)]
    calc
      (1 - (s : ℝ)) * cellGauge x ≤ 1 * cellGauge x :=
        mul_le_mul_of_nonneg_right (sub_le_self 1 s.2.1) (cellGauge_nonneg x)
      _ = cellGauge x := (one_mul _)
      _ < 1 := (mem_interior_baseCell_iff x).mp x.2⟩

private theorem CuspCentralHomology.Radial.interiorCellContract_continuous :
    Continuous (fun p : unitInterval × InteriorCell => interiorCellContract p.1 p.2) :=
  ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)).subtype_mk
    _

@[simp]
private theorem CuspCentralHomology.Radial.interiorCellContract_zero (x : InteriorCell) :
    interiorCellContract 0 x = x := by
  apply Subtype.ext
  simp [interiorCellContract]

@[simp]
private theorem CuspCentralHomology.Radial.interiorCellContract_one (x : InteriorCell) :
    interiorCellContract 1 x = interiorCellZero := by
  apply Subtype.ext
  simp [interiorCellContract, interiorCellZero]

@[simp]
private theorem CuspCentralHomology.Radial.interiorCellContract_fixed_zero (s : unitInterval) :
    interiorCellContract s interiorCellZero = interiorCellZero := by
  apply Subtype.ext
  simp [interiorCellContract, interiorCellZero]

private def CuspCentralHomology.Radial.interiorCellContraction :
    (ContinuousMap.id InteriorCell).HomotopyRel
      (ContinuousMap.const InteriorCell interiorCellZero) { interiorCellZero }
    where
  toFun p := interiorCellContract p.1 p.2
  continuous_toFun := interiorCellContract_continuous
  map_zero_left := interiorCellContract_zero
  map_one_left := interiorCellContract_one
  prop' s x
    hx := by
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact interiorCellContract_fixed_zero s

private def CuspCentralHomology.Radial.interiorCellPointHomotopyEquiv : InteriorCell ≃ₕ Unit
    where
  toFun := ContinuousMap.const _ ()
  invFun := ContinuousMap.const _ interiorCellZero
  left_inv := ⟨interiorCellContraction.toHomotopy.symm⟩
  right_inv := by
    convert ContinuousMap.Homotopic.refl (ContinuousMap.id Unit) using 1
    ext u

private def
    CuspCentralHomology.Radial.interiorCellProductHomotopyEquiv (X : Type*) [TopologicalSpace X] :
    (X × InteriorCell) ≃ₕ X :=
  ((ContinuousMap.HomotopyEquiv.refl X).prodCongr interiorCellPointHomotopyEquiv).trans
    (Homeomorph.prodUnique X Unit).toHomotopyEquiv

private abbrev CuspCentralHomology.Radial.CellFrontier :=
  frontier CuspHoneycombTiling.baseCell

private abbrev CuspCentralHomology.Radial.Annulus (a : ℝ) :=
  { x : (CuspHoneycombTiling.Plane) // a < cellGauge x ∧ cellGauge x < 1 }

private noncomputable def CuspCentralHomology.Radial.normalize (x : (CuspHoneycombTiling.Plane)) :
    (CuspHoneycombTiling.Plane) :=
  (cellGauge x)⁻¹ • x

private theorem CuspCentralHomology.Radial.normalize_gauge (x : (CuspHoneycombTiling.Plane))
    (hx : x ≠ 0) : cellGauge (CuspCentralHomology.Radial.normalize x) = 1 := by
  rw [CuspCentralHomology.Radial.normalize,
    cellGauge_smul_of_nonneg _ (inv_nonneg.mpr (cellGauge_nonneg x))]
  exact inv_mul_cancel₀ ((cellGauge_pos_iff x).mpr hx).ne'

private theorem CuspCentralHomology.Radial.normalize_continuousOn :
    ContinuousOn CuspCentralHomology.Radial.normalize {x : (CuspHoneycombTiling.Plane) | x ≠ 0} :=
  (cellGauge_continuous.continuousOn.inv₀ (fun x hx => ((cellGauge_pos_iff x).mpr hx).ne')).smul
    continuous_id.continuousOn

private noncomputable def CuspCentralHomology.Radial.direction
    (x : { x : (CuspHoneycombTiling.Plane) // x ≠ 0 }) : CellFrontier :=
  ⟨CuspCentralHomology.Radial.normalize x,
    (mem_frontier_baseCell_iff _).mpr (normalize_gauge x x.2)⟩

private theorem CuspCentralHomology.Radial.direction_continuous : Continuous direction :=
  normalize_continuousOn.domRestrict.subtype_mk _

private theorem CuspCentralHomology.Radial.cellGauge_smul_frontier (c : ℝ) (hc : 0 ≤ c)
    (u : CellFrontier) : cellGauge (c • (u : (CuspHoneycombTiling.Plane))) = c := by
  rw [cellGauge_smul_of_nonneg c hc, (mem_frontier_baseCell_iff _).mp u.2, mul_one]

private noncomputable def CuspCentralHomology.Radial.radialRangeHomeomorph (R : Set ℝ)
    (hR : ∀ r ∈ R, 0 < r) :
    { x : (CuspHoneycombTiling.Plane) // cellGauge x ∈ R } ≃ₜ CellFrontier × R
    where
  toFun x := (direction ⟨x, (cellGauge_pos_iff x).mp (hR _ x.2)⟩, ⟨cellGauge x, x.2⟩)
  invFun
    p :=
    ⟨(p.2 : ℝ) • (p.1 : (CuspHoneycombTiling.Plane)),
      by
      rw [cellGauge_smul_frontier _ (hR _ p.2.2).le]
      exact p.2.2⟩
  left_inv
    x := by
    apply Subtype.ext
    change
      cellGauge x • ((cellGauge x)⁻¹ • (x : (CuspHoneycombTiling.Plane))) =
        (x : (CuspHoneycombTiling.Plane))
    rw [smul_smul, mul_inv_cancel₀ (hR _ x.2).ne', one_smul]
  right_inv
    p := by
    apply Prod.ext
    · apply Subtype.ext
      change
        CuspCentralHomology.Radial.normalize ((p.2 : ℝ) • (p.1 : (CuspHoneycombTiling.Plane))) =
          (p.1 : (CuspHoneycombTiling.Plane))
      rw [CuspCentralHomology.Radial.normalize, cellGauge_smul_frontier _ (hR _ p.2.2).le,
        smul_smul, inv_mul_cancel₀ (hR _ p.2.2).ne', one_smul]
    · apply Subtype.ext
      exact cellGauge_smul_frontier _ (hR _ p.2.2).le p.1
  continuous_toFun :=
    (direction_continuous.comp (continuous_subtype_val.subtype_mk _)).prodMk
      ((cellGauge_continuous.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_snd).smul
          (continuous_subtype_val.comp continuous_fst)).subtype_mk
      _

private noncomputable def CuspCentralHomology.Radial.annulusHomeomorph (a : ℝ) (ha : 0 ≤ a) :
    Annulus a ≃ₜ CellFrontier × Set.Ioo a 1 :=
  radialRangeHomeomorph (Set.Ioo a 1) (fun _ hr => ha.trans_lt hr.1)

private abbrev CuspCentralHomology.Radial.RadialDomain (R : Set ℝ) :=
  { x : (CuspHoneycombTiling.Plane) // cellGauge x ∈ R }

private def CuspCentralHomology.Radial.radiusProjection (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) :
    C(RadialDomain R, CellFrontier) :=
  ⟨fun x => (radialRangeHomeomorph R hR x).1,
    continuous_fst.comp (radialRangeHomeomorph R hR).continuous⟩

private def CuspCentralHomology.Radial.radiusSection (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (c : ℝ)
    (hc : c ∈ R) : C(CellFrontier, RadialDomain R) :=
  ⟨fun u => (radialRangeHomeomorph R hR).symm (u, ⟨c, hc⟩),
    (radialRangeHomeomorph R hR).symm.continuous.comp (continuous_id.prodMk continuous_const)⟩

private theorem CuspCentralHomology.Radial.radiusProjection_coe (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (x : RadialDomain R) :
    (radiusProjection R hR x : (CuspHoneycombTiling.Plane)) =
      CuspCentralHomology.Radial.normalize x :=
  rfl

private theorem
    CuspCentralHomology.Radial.radiusSection_coe (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r) (c : ℝ)
    (hc : c ∈ R) (u : CellFrontier) :
    (radiusSection R hR c hc u : (CuspHoneycombTiling.Plane)) =
      c • (u : (CuspHoneycombTiling.Plane)) :=
  rfl

private theorem
    CuspCentralHomology.Radial.radiusProjection_comp_section (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (c : ℝ) (hc : c ∈ R) :
    (radiusProjection R hR).comp (radiusSection R hR c hc) = ContinuousMap.id CellFrontier := by
  apply ContinuousMap.ext
  intro u
  change ((radialRangeHomeomorph R hR) ((radialRangeHomeomorph R hR).symm (u, ⟨c, hc⟩))).1 = u
  rw [Homeomorph.apply_symm_apply]

private def CuspCentralHomology.Radial.radiusBlend (c : ℝ) (s : unitInterval) (r : ℝ) : ℝ :=
  (1 - (s : ℝ)) * r + (s : ℝ) * c

private theorem CuspCentralHomology.Radial.radiusBlend_mem {R : Set ℝ} (hconv : Convex ℝ R) (c : ℝ)
    (hc : c ∈ R) (s : unitInterval) (r : ℝ) (hr : r ∈ R) : radiusBlend c s r ∈ R :=
  hconv hr hc (sub_nonneg.mpr s.2.2) s.2.1 (sub_add_cancel 1 (s : ℝ))

private def CuspCentralHomology.Radial.radiusHomotopyMap (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) : C(unitInterval × RadialDomain R, RadialDomain R)
    where
  toFun
    p :=
    (radialRangeHomeomorph R hR).symm
      ((radialRangeHomeomorph R hR p.2).1,
        ⟨radiusBlend c p.1 (cellGauge p.2), radiusBlend_mem hconv c hc p.1 _ p.2.2⟩)
  continuous_toFun :=
    (radialRangeHomeomorph R hR).symm.continuous.comp
      ((continuous_fst.comp ((radialRangeHomeomorph R hR).continuous.comp continuous_snd)).prodMk
        ((((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
                  (cellGauge_continuous.comp (continuous_subtype_val.comp continuous_snd))).add
              ((continuous_subtype_val.comp continuous_fst).mul continuous_const)).subtype_mk
          _))

private theorem CuspCentralHomology.Radial.radiusHomotopyMap_coe (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (s : unitInterval) (x : RadialDomain R) :
    (radiusHomotopyMap R hR hconv c hc (s, x) : (CuspHoneycombTiling.Plane)) =
      radiusBlend c s (cellGauge x) • CuspCentralHomology.Radial.normalize x :=
  rfl

private theorem CuspCentralHomology.Radial.radiusHomotopyMap_gauge (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (s : unitInterval) (x : RadialDomain R) :
    cellGauge (radiusHomotopyMap R hR hconv c hc (s, x)) = radiusBlend c s (cellGauge x) :=
  cellGauge_smul_frontier _ (hR _ (radiusBlend_mem hconv c hc s _ x.2)).le
    (radialRangeHomeomorph R hR x).1

private theorem CuspCentralHomology.Radial.radiusHomotopyMap_zero (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (x : RadialDomain R) :
    radiusHomotopyMap R hR hconv c hc (0, x) = x := by
  apply Subtype.ext
  rw [radiusHomotopyMap_coe]
  change
    ((1 - (0 : ℝ)) * cellGauge x + 0 * c) • CuspCentralHomology.Radial.normalize x =
      (x : (CuspHoneycombTiling.Plane))
  rw [sub_zero, one_mul, MulZeroClass.zero_mul, add_zero, CuspCentralHomology.Radial.normalize,
    smul_smul, mul_inv_cancel₀ (hR _ x.2).ne', one_smul]

private theorem CuspCentralHomology.Radial.radiusHomotopyMap_one (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (x : RadialDomain R) :
    radiusHomotopyMap R hR hconv c hc (1, x) =
      radiusSection R hR c hc (radiusProjection R hR x) := by
  apply Subtype.ext
  rw [radiusHomotopyMap_coe, radiusSection_coe, radiusProjection_coe]
  change
    ((1 - (1 : ℝ)) * cellGauge x + 1 * c) • CuspCentralHomology.Radial.normalize x =
      c • CuspCentralHomology.Radial.normalize x
  rw [sub_self, MulZeroClass.zero_mul, one_mul, zero_add]

private theorem CuspCentralHomology.Radial.radiusHomotopyMap_fixed (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) (s : unitInterval) (x : RadialDomain R)
    (hx : cellGauge x = c) : radiusHomotopyMap R hR hconv c hc (s, x) = x := by
  have hblend : radiusBlend c s (cellGauge x) = cellGauge x := by
    rw [radiusBlend, hx]
    ring
  apply Subtype.ext
  rw [radiusHomotopyMap_coe, hblend, CuspCentralHomology.Radial.normalize, smul_smul,
    mul_inv_cancel₀ (hR _ x.2).ne', one_smul]

private def CuspCentralHomology.Radial.radiusHomotopy (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) :
    (ContinuousMap.id (RadialDomain R)).Homotopy
      ((radiusSection R hR c hc).comp (radiusProjection R hR))
    where
  toContinuousMap := radiusHomotopyMap R hR hconv c hc
  map_zero_left := radiusHomotopyMap_zero R hR hconv c hc
  map_one_left := radiusHomotopyMap_one R hR hconv c hc

private def CuspCentralHomology.Radial.radialHomotopyEquiv (R : Set ℝ) (hR : ∀ r ∈ R, 0 < r)
    (hconv : Convex ℝ R) (c : ℝ) (hc : c ∈ R) : RadialDomain R ≃ₕ CellFrontier
    where
  toFun := radiusProjection R hR
  invFun := radiusSection R hR c hc
  left_inv := ⟨(radiusHomotopy R hR hconv c hc).symm⟩
  right_inv := by rw [radiusProjection_comp_section]

private def
    CuspCentralHomology.Radial.annulusFrontierHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Annulus a ≃ₕ CellFrontier :=
  radialHomotopyEquiv (Set.Ioo a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioo a 1) ((a + 1) / 2)
    ⟨by linarith, by linarith⟩

private abbrev CuspCentralHomology.Radial.OpenCollar (a : ℝ) :=
  { x : (CuspHoneycombTiling.Plane) // a < cellGauge x ∧ cellGauge x ≤ 1 }

private def CuspCentralHomology.Radial.frontierIntoOpenCollar (a : ℝ) (ha1 : a < 1) :
    C(CellFrontier, OpenCollar a) :=
  ⟨fun u =>
    ⟨u, by
      rw [(mem_frontier_baseCell_iff _).mp u.2]
      exact ⟨ha1, le_rfl⟩⟩,
    continuous_subtype_val.subtype_mk _⟩

private def CuspCentralHomology.Radial.openCollarRetraction (a : ℝ) (ha : 0 ≤ a) :
    C(OpenCollar a, CellFrontier) :=
  radiusProjection (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1)

private def
    CuspCentralHomology.Radial.outwardOpenCollarHomotopy (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (ContinuousMap.id (OpenCollar a)).HomotopyRel
      ((frontierIntoOpenCollar a ha1).comp (openCollarRetraction a ha))
      {x : OpenCollar a | cellGauge x = 1}
    where
  toContinuousMap :=
    radiusHomotopyMap (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1
      ⟨ha1, le_rfl⟩
  map_zero_left :=
    radiusHomotopyMap_zero (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1
      ⟨ha1, le_rfl⟩
  map_one_left
    x := by
    apply Subtype.ext
    change
      ((1 - (1 : ℝ)) * cellGauge x + 1 * 1) • CuspCentralHomology.Radial.normalize x =
        CuspCentralHomology.Radial.normalize x
    rw [sub_self, MulZeroClass.zero_mul, one_mul, zero_add, one_smul]
  prop' s x
    hx :=
    radiusHomotopyMap_fixed (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1
      ⟨ha1, le_rfl⟩ s x hx

private theorem CuspCentralHomology.Radial.outwardOpenCollarHomotopy_coe (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (x : OpenCollar a) :
    (outwardOpenCollarHomotopy a ha ha1 (s, x) : (CuspHoneycombTiling.Plane)) =
      ((1 - (s : ℝ)) + (s : ℝ) / cellGauge x) • (x : (CuspHoneycombTiling.Plane)) := by
  change radiusBlend 1 s (cellGauge x) • CuspCentralHomology.Radial.normalize x = _
  rw [CuspCentralHomology.Radial.normalize, smul_smul]
  congr 1
  rw [radiusBlend, mul_one, add_mul, mul_assoc, mul_inv_cancel₀ (ha.trans_lt x.2.1).ne', mul_one,
    div_eq_mul_inv]

private theorem CuspCentralHomology.Radial.outwardOpenCollarHomotopy_gauge (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (x : OpenCollar a) :
    cellGauge (outwardOpenCollarHomotopy a ha ha1 (s, x)) =
      (1 - (s : ℝ)) * cellGauge x + (s : ℝ) := by
  change
    cellGauge
        (radiusHomotopyMap (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1
          ⟨ha1, le_rfl⟩ (s, x)) =
      _
  simpa only [radiusBlend, mul_one] using
    radiusHomotopyMap_gauge (Set.Ioc a 1) (fun _ hr => ha.trans_lt hr.1) (convex_Ioc a 1) 1
      ⟨ha1, le_rfl⟩ s x

private theorem CuspCentralHomology.Radial.outwardOpenCollarHomotopy_fixed (a : ℝ) (ha : 0 ≤ a)
    (ha1 : a < 1) (s : unitInterval) (x : OpenCollar a)
    (hx : (x : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell) :
    outwardOpenCollarHomotopy a ha ha1 (s, x) = x :=
  (outwardOpenCollarHomotopy a ha ha1).eq_fst s ((mem_frontier_baseCell_iff _).mp hx)

private def CuspCentralHomology.Radial.circlePlaneComplexEquiv : CuspHoneycombTiling.Plane ≃L[ℝ] ℂ
    where
  toFun x := ⟨x 0, x 1⟩
  invFun z := ![z.re, z.im]
  left_inv
    x := by
    funext i
    fin_cases i <;> rfl
  right_inv
    z := by
    cases z
    rfl
  map_add' _ _ := rfl
  map_smul' c x := by apply Complex.ext <;> simp
  continuous_toFun := by
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

private theorem CuspCentralHomology.Radial.circleFrontier_ne_zero
    (x : frontier CuspHoneycombTiling.baseCell) : (x : CuspHoneycombTiling.Plane) ≠ 0 := by
  intro hx
  have hg := (mem_frontier_baseCell_iff (x : CuspHoneycombTiling.Plane)).mp x.property
  exact zero_ne_one (by simpa only [hx, cellGauge_zero] using hg)

private theorem CuspCentralHomology.Radial.circleFrontierComplex_ne_zero
    (x : frontier CuspHoneycombTiling.baseCell) :
    circlePlaneComplexEquiv (x : CuspHoneycombTiling.Plane) ≠ 0 := by
  intro hx
  exact circleFrontier_ne_zero x (circlePlaneComplexEquiv.map_eq_zero_iff.mp hx)

private def
    CuspCentralHomology.Radial.frontierCircleForward (x : frontier CuspHoneycombTiling.baseCell) :
    Circle :=
  ⟨NormedSpace.normalize (circlePlaneComplexEquiv (x : CuspHoneycombTiling.Plane)),
    mem_sphere_zero_iff_norm.mpr (NormedSpace.norm_normalize (circleFrontierComplex_ne_zero x))⟩

@[simp]
private theorem CuspCentralHomology.Radial.frontierCircleForward_coe
    (x : frontier CuspHoneycombTiling.baseCell) :
    (frontierCircleForward x : ℂ) =
      ‖circlePlaneComplexEquiv (x : CuspHoneycombTiling.Plane)‖⁻¹ •
        circlePlaneComplexEquiv (x : CuspHoneycombTiling.Plane) :=
  rfl

private theorem CuspCentralHomology.Radial.frontierCircleForward_continuous :
    Continuous frontierCircleForward := by
  apply Continuous.subtype_mk
  have h :
    Continuous
      (fun x : frontier CuspHoneycombTiling.baseCell =>
        circlePlaneComplexEquiv (x : CuspHoneycombTiling.Plane)) :=
    circlePlaneComplexEquiv.continuous.comp continuous_subtype_val
  exact (h.norm.inv₀ fun x => norm_ne_zero_iff.mpr (circleFrontierComplex_ne_zero x)).smul h

private theorem CuspCentralHomology.Radial.circleComplexPlane_ne_zero (z : Circle) :
    circlePlaneComplexEquiv.symm (z : ℂ) ≠ 0 := by
  intro hz
  exact z.coe_ne_zero (circlePlaneComplexEquiv.symm.map_eq_zero_iff.mp hz)

private theorem CuspCentralHomology.Radial.circleComplexPlaneGauge_pos (z : Circle) :
    0 < cellGauge (circlePlaneComplexEquiv.symm (z : ℂ)) :=
  (cellGauge_pos_iff _).mpr (circleComplexPlane_ne_zero z)

private def CuspCentralHomology.Radial.frontierCircleInverse (z : Circle) :
    frontier CuspHoneycombTiling.baseCell :=
  ⟨(cellGauge (circlePlaneComplexEquiv.symm (z : ℂ)))⁻¹ • circlePlaneComplexEquiv.symm (z : ℂ),
    (mem_frontier_baseCell_iff _).mpr
      (by
        rw [cellGauge_smul_of_nonneg _ (inv_nonneg.mpr (cellGauge_nonneg _)),
          inv_mul_cancel₀ (ne_of_gt (circleComplexPlaneGauge_pos z))])⟩

@[simp]
private theorem CuspCentralHomology.Radial.frontierCircleInverse_coe (z : Circle) :
    (frontierCircleInverse z : CuspHoneycombTiling.Plane) =
      (cellGauge (circlePlaneComplexEquiv.symm (z : ℂ)))⁻¹ •
        circlePlaneComplexEquiv.symm (z : ℂ) :=
  rfl

private theorem CuspCentralHomology.Radial.frontierCircleInverse_continuous :
    Continuous frontierCircleInverse := by
  apply Continuous.subtype_mk
  have h : Continuous (fun z : Circle => circlePlaneComplexEquiv.symm (z : ℂ)) :=
    circlePlaneComplexEquiv.symm.continuous.comp continuous_subtype_val
  exact
    ((cellGauge_continuous.comp h).inv₀ fun z => ne_of_gt (circleComplexPlaneGauge_pos z)).smul h

@[simp]
private theorem CuspCentralHomology.Radial.frontierCircleInverse_forward
    (x : frontier CuspHoneycombTiling.baseCell) :
    frontierCircleInverse (frontierCircleForward x) = x := by
  apply Subtype.ext
  change
    (cellGauge (circlePlaneComplexEquiv.symm (frontierCircleForward x : ℂ)))⁻¹ •
        circlePlaneComplexEquiv.symm (frontierCircleForward x : ℂ) =
      (x : CuspHoneycombTiling.Plane)
  rw [frontierCircleForward_coe, map_smul, circlePlaneComplexEquiv.symm_apply_apply,
    cellGauge_smul_of_nonneg _ (inv_nonneg.mpr (norm_nonneg _)),
    (mem_frontier_baseCell_iff _).mp x.property, mul_one, inv_inv, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (circleFrontierComplex_ne_zero x)), one_smul]

@[simp]
private theorem CuspCentralHomology.Radial.frontierCircleForward_inverse (z : Circle) :
    frontierCircleForward (frontierCircleInverse z) = z := by
  apply Circle.ext
  change
    NormedSpace.normalize
        (circlePlaneComplexEquiv (frontierCircleInverse z : CuspHoneycombTiling.Plane)) =
      (z : ℂ)
  rw [frontierCircleInverse_coe, map_smul, circlePlaneComplexEquiv.apply_symm_apply,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr (circleComplexPlaneGauge_pos z))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one z.norm_coe

private def CuspCentralHomology.Radial.frontierCellCircleHomeomorph :
    frontier CuspHoneycombTiling.baseCell ≃ₜ Circle
    where
  toFun := frontierCircleForward
  invFun := frontierCircleInverse
  left_inv := frontierCircleInverse_forward
  right_inv := frontierCircleForward_inverse
  continuous_toFun := frontierCircleForward_continuous
  continuous_invFun := frontierCircleInverse_continuous

@[simp]
private theorem CuspCentralHomology.Radial.frontierCellCircleHomeomorph_symm_coe (z : Circle) :
    (frontierCellCircleHomeomorph.symm z : CuspHoneycombTiling.Plane) =
      (cellGauge ![(z : ℂ).re, (z : ℂ).im])⁻¹ • ![(z : ℂ).re, (z : ℂ).im] :=
  rfl

private def
    CuspCentralHomology.Radial.annulusCircleHomotopyEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Annulus a ≃ₕ Circle :=
  (annulusFrontierHomotopyEquiv a ha ha1).trans frontierCellCircleHomeomorph.toHomotopyEquiv

private def
    CuspCentralHomology.Radial.phaseAnnulusHomotopyEquiv (X : Type*) [TopologicalSpace X] (a : ℝ)
    (ha : 0 ≤ a) (ha1 : a < 1) : (X × Annulus a) ≃ₕ X × Circle :=
  (ContinuousMap.HomotopyEquiv.refl X).prodCongr (annulusCircleHomotopyEquiv a ha ha1)

private abbrev CuspCentralHomology.OverlapPhaseCell (a : ℝ) :=
  ToricSpace.CompactFibreTorus × Radial.Annulus a

private def CuspCentralHomology.annulusCellInclusion (a : ℝ) (p : OverlapPhaseCell a) :
    InteriorPhaseCell :=
  (p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), (Radial.mem_interior_baseCell_iff _).mpr p.2.2.2⟩)

@[simp]
private theorem CuspCentralHomology.annulusCellInclusion_snd_coe (a : ℝ) (p : OverlapPhaseCell a) :
    ((annulusCellInclusion a p).2 : (CuspHoneycombTiling.Plane)) =
      (p.2 : (CuspHoneycombTiling.Plane)) :=
  rfl

private theorem CuspCentralHomology.annulusCellInclusion_continuous (a : ℝ) :
    Continuous (annulusCellInclusion a) :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

private theorem CuspCentralHomology.annulusCellInclusion_injective (a : ℝ) :
    Function.Injective (annulusCellInclusion a) := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun r : InteriorPhaseCell => r.1) hpq
  · apply Subtype.ext
    exact congrArg (fun r : InteriorPhaseCell => (r.2 : (CuspHoneycombTiling.Plane))) hpq

private def
    CuspCentralHomology.overlapRegion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) : Set (CuspRetraction.QuotientCentralFibre C ε) :=
  outerRegion C ε hε a ∩ innerRegion C ε hε

private def
    CuspCentralHomology.overlapIntoInner (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) : C(overlapRegion C ε hε a, innerRegion C ε hε) :=
  ⟨fun q => ⟨(q : CuspRetraction.QuotientCentralFibre C ε), q.2.2⟩,
    continuous_subtype_val.subtype_mk _⟩

private def
    CuspCentralHomology.overlapCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (p : OverlapPhaseCell a) : overlapRegion C ε hε a :=
  ⟨(innerRegionHomeomorph C ε hε hε1 hC hR (annulusCellInclusion a p) :
      CuspRetraction.QuotientCentralFibre C ε),
    by
    constructor
    · change a < centralRadius C ε hε _
      rw [innerRegionHomeomorph_radius, annulusCellInclusion_snd_coe]
      exact p.2.2.1
    · exact (innerRegionHomeomorph C ε hε hε1 hC hR (annulusCellInclusion a p)).2⟩

@[simp]
private theorem CuspCentralHomology.overlapCellMap_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (p : OverlapPhaseCell a) :
    (overlapCellMap C ε hε hε1 hC hR a p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) :=
  innerRegionHomeomorph_honeycomb C ε hε hε1 hC hR (annulusCellInclusion a p)

private theorem
    CuspCentralHomology.overlapCellMap_intoInner (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (p : OverlapPhaseCell a) :
    overlapIntoInner C ε hε a (overlapCellMap C ε hε hε1 hC hR a p) =
      innerRegionHomeomorph C ε hε hε1 hC hR (annulusCellInclusion a p) :=
  rfl

private theorem
    CuspCentralHomology.overlapCellMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) : Continuous (overlapCellMap C ε hε hε1 hC hR a) :=
  (continuous_subtype_val.comp
        ((innerRegionHomeomorph C ε hε hε1 hC hR).continuous.comp
          (annulusCellInclusion_continuous a))).subtype_mk
    _

private def
    CuspCentralHomology.overlapCellInverse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (q : overlapRegion C ε hε a) : OverlapPhaseCell a :=
  let p := (innerRegionHomeomorph C ε hε hε1 hC hR).symm (overlapIntoInner C ε hε a q)
  (p.1,
    ⟨(p.2 : (CuspHoneycombTiling.Plane)), by
      constructor
      · rw [← innerRegionHomeomorph_radius C ε hε hε1 hC hR p]
        dsimp only [p]
        rw [Homeomorph.apply_symm_apply]
        exact q.2.1
      · exact (Radial.mem_interior_baseCell_iff _).mp p.2.2⟩)

private theorem
    CuspCentralHomology.overlapCellInverse_interior (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (q : overlapRegion C ε hε a) :
    annulusCellInclusion a (overlapCellInverse C ε hε hε1 hC hR a q) =
      (innerRegionHomeomorph C ε hε hε1 hC hR).symm (overlapIntoInner C ε hε a q) :=
  rfl

private theorem CuspCentralHomology.overlapCellInverse_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) :
    Continuous (overlapCellInverse C ε hε hε1 hC hR a) := by
  have hp :=
    (innerRegionHomeomorph C ε hε hε1 hC hR).symm.continuous.comp
      (overlapIntoInner C ε hε a).continuous
  exact
    (continuous_fst.comp hp).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp hp)).subtype_mk _)

private def CuspCentralHomology.overlapPhaseHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) : OverlapPhaseCell a ≃ₜ overlapRegion C ε hε a
    where
  toFun := overlapCellMap C ε hε hε1 hC hR a
  invFun := overlapCellInverse C ε hε hε1 hC hR a
  left_inv
    p := by
    apply annulusCellInclusion_injective a
    rw [overlapCellInverse_interior, overlapCellMap_intoInner, Homeomorph.symm_apply_apply]
  right_inv
    q := by
    apply Subtype.ext
    change
      (innerRegionHomeomorph C ε hε hε1 hC hR
            (annulusCellInclusion a (overlapCellInverse C ε hε hε1 hC hR a q)) :
          CuspRetraction.QuotientCentralFibre C ε) =
        (q : CuspRetraction.QuotientCentralFibre C ε)
    rw [overlapCellInverse_interior, Homeomorph.apply_symm_apply]
    rfl
  continuous_toFun := overlapCellMap_continuous C ε hε hε1 hC hR a
  continuous_invFun := overlapCellInverse_continuous C ε hε hε1 hC hR a

@[simp]
private theorem
    CuspCentralHomology.overlapPhaseHomeomorph_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (p : OverlapPhaseCell a) :
    (overlapPhaseHomeomorph C ε hε hε1 hC hR a p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) :=
  overlapCellMap_coe C ε hε hε1 hC hR a p

private def
    CuspCentralHomology.overlapHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) :
    overlapRegion C ε hε a ≃ₜ ToricSpace.CompactFibreTorus × Radial.CellFrontier × Set.Ioo a 1 :=
  (overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm.trans
    ((Homeomorph.refl ToricSpace.CompactFibreTorus).prodCongr (Radial.annulusHomeomorph a ha))

private def CuspCentralHomology.innerRegionHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : innerRegion C ε hε ≃ₕ ToricSpace.CompactFibreTorus :=
  (innerRegionHomeomorph C ε hε hε1 hC hR).symm.toHomotopyEquiv.trans
    (Radial.interiorCellProductHomotopyEquiv ToricSpace.CompactFibreTorus)

private def
    CuspCentralHomology.overlapCircleHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    overlapRegion C ε hε a ≃ₕ ToricSpace.CompactFibreTorus × Circle :=
  (overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm.toHomotopyEquiv.trans
    (Radial.phaseAnnulusHomotopyEquiv ToricSpace.CompactFibreTorus a ha ha1)

private theorem
    CuspCentralHomology.overlapIntoInner_phase_map (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (innerRegionHomotopyEquiv C ε hε hε1 hC hR).toFun.comp (overlapIntoInner C ε hε a) =
      (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus)).comp
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun := by
  ext q
  rfl

private abbrev CuspCentralHomology.CollarPhaseCell (a : ℝ) :=
  ToricSpace.CompactFibreTorus × Radial.OpenCollar a

private def
    CuspCentralHomology.collarCellInclusion (a : ℝ) (p : CollarPhaseCell a) : FundamentalCell :=
  (p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), (Radial.mem_baseCell_iff _).mpr p.2.2.2⟩)

private theorem CuspCentralHomology.collarCellInclusion_continuous (a : ℝ) :
    Continuous (collarCellInclusion a) :=
  continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)

private theorem CuspCentralHomology.collarCellInclusion_injective (a : ℝ) :
    Function.Injective (collarCellInclusion a) := by
  intro p q hpq
  apply Prod.ext
  · exact congrArg (fun r : FundamentalCell => r.1) hpq
  · apply Subtype.ext
    exact congrArg (fun r : FundamentalCell => (r.2 : (CuspHoneycombTiling.Plane))) hpq

private theorem CuspCentralHomology.fundamentalCellMap_mem_outerRegion_iff
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (p : FundamentalCell) :
    fundamentalCellMap C ε hε p ∈ outerRegion C ε hε a ↔
      a < Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) := by
  change a < centralRadius C ε hε (fundamentalCellMap C ε hε p) ↔ _
  rw [centralRadius_fundamentalCellMap]

private def
    CuspCentralHomology.collarCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) (p : CollarPhaseCell a) : outerRegion C ε hε a :=
  ⟨fundamentalCellMap C ε hε (collarCellInclusion a p),
    (fundamentalCellMap_mem_outerRegion_iff C ε hε a _).mpr p.2.2.1⟩

@[simp]
private theorem CuspCentralHomology.collarCellMap_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (p : CollarPhaseCell a) :
    (collarCellMap C ε hε a p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) :=
  rfl

private theorem
    CuspCentralHomology.centralRadius_collarCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (p : CollarPhaseCell a) :
    centralRadius C ε hε (collarCellMap C ε hε a p) =
      Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) :=
  centralRadius_fundamentalCellMap C ε hε (collarCellInclusion a p)

private theorem
    CuspCentralHomology.collarCellMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) : Continuous (collarCellMap C ε hε a) :=
  ((fundamentalCellMap_continuous C ε hε).comp (collarCellInclusion_continuous a)).subtype_mk _

private theorem
    CuspCentralHomology.collarCellMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) : Function.Surjective (collarCellMap C ε hε a) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, hp⟩ := fundamentalCellMap_surjective C ε hε q
  have hg : a < Radial.cellGauge (p.2 : (CuspHoneycombTiling.Plane)) := by
    apply (fundamentalCellMap_mem_outerRegion_iff C ε hε a p).mp
    rwa [hp]
  refine
    ⟨(p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), hg, (Radial.mem_baseCell_iff _).mp p.2.2⟩), ?_⟩
  apply Subtype.ext
  exact hp

private def CuspCentralHomology.collarPreimageHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) :
    CollarPhaseCell a ≃ₜ (fundamentalCellMap C ε hε ⁻¹' outerRegion C ε hε a)
    where
  toFun
    p :=
    ⟨collarCellInclusion a p, (fundamentalCellMap_mem_outerRegion_iff C ε hε a _).mpr p.2.2.1⟩
  invFun
    p :=
    (p.1.1,
      ⟨(p.1.2 : (CuspHoneycombTiling.Plane)),
        (fundamentalCellMap_mem_outerRegion_iff C ε hε a p.1).mp p.2,
        (Radial.mem_baseCell_iff _).mp p.1.2.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (collarCellInclusion_continuous a).subtype_mk _
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)

private theorem
    CuspCentralHomology.collarCellMap_isProperMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsProperMap (collarCellMap C ε hε a) := by
  have hf :=
    (fundamentalCellMap_isProperMap C ε hε hε1 hC hR).restrictPreimage (outerRegion C ε hε a)
  have hc := hf.comp (collarPreimageHomeomorph C ε hε a).isProperMap
  have he :
    (outerRegion C ε hε a).restrictPreimage (fundamentalCellMap C ε hε) ∘
        collarPreimageHomeomorph C ε hε a =
      collarCellMap C ε hε a := by
    funext p
    apply Subtype.ext
    rfl
  rw [he] at hc
  exact hc

private theorem
    CuspCentralHomology.collarCellMap_isClosedMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsClosedMap (collarCellMap C ε hε a) :=
  (collarCellMap_isProperMap C ε hε a hε1 hC hR).isClosedMap

private theorem
    CuspCentralHomology.collarCellMap_isQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : Topology.IsQuotientMap (collarCellMap C ε hε a) :=
  (collarCellMap_isClosedMap C ε hε a hε1 hC hR).isQuotientMap (collarCellMap_continuous C ε hε a)
    (collarCellMap_surjective C ε hε a)

private def CuspCentralHomology.collarCellHomotopy (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    C(unitInterval × CollarPhaseCell a, CollarPhaseCell a)
    where
  toFun p := (p.2.1, Radial.outwardOpenCollarHomotopy a ha ha1 (p.1, p.2.2))
  continuous_toFun :=
    (continuous_fst.comp continuous_snd).prodMk
      ((Radial.outwardOpenCollarHomotopy a ha ha1).continuous.comp
        (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))

@[simp]
private theorem CuspCentralHomology.collarCellHomotopy_zero (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (p : CollarPhaseCell a) : collarCellHomotopy a ha ha1 (0, p) = p := by
  apply Prod.ext
  · rfl
  · exact (Radial.outwardOpenCollarHomotopy a ha ha1).apply_zero p.2

private theorem CuspCentralHomology.collarCellHomotopy_fixed (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (p : CollarPhaseCell a)
    (hp : (p.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell) :
    collarCellHomotopy a ha ha1 (s, p) = p := by
  apply Prod.ext
  · rfl
  · exact Radial.outwardOpenCollarHomotopy_fixed a ha ha1 s p.2 hp

private theorem CuspCentralHomology.collarCellHomotopy_compatible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval)
    (p q : CollarPhaseCell a) (h : collarCellMap C ε hε a p = collarCellMap C ε hε a q) :
    collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)) =
      collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, q)) := by
  have he :
    fundamentalCellMap C ε hε (collarCellInclusion a p) =
      fundamentalCellMap C ε hε (collarCellInclusion a q) :=
    congrArg Subtype.val h
  rcases
    fundamentalCellMap_eq_or_frontier C ε hε (collarCellInclusion a p) (collarCellInclusion a q)
      he with
    hpq | ⟨hp, hq⟩
  · rw [collarCellInclusion_injective a hpq]
  · rw [collarCellHomotopy_fixed a ha ha1 s p hp, collarCellHomotopy_fixed a ha ha1 s q hq]
    exact h

private def
    CuspCentralHomology.outerRegionBoundaryInclusion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha1 : a < 1) : C(centralBoundary C ε hε, outerRegion C ε hε a)
    where
  toFun x := ⟨x, centralBoundary_subset_outerRegion C ε hε a ha1 x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

private def CuspCentralHomology.outerRegionDeformation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval)
    (x : outerRegion C ε hε a) : outerRegion C ε hε a :=
  CuspHoneycombHexagon.CommonFibres.descend (collarCellMap C ε hε a)
    (fun p => collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective C ε hε a) x

@[simp]
private theorem CuspCentralHomology.outerRegionDeformation_collarCellMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (p : CollarPhaseCell a) :
    outerRegionDeformation C ε hε a ha ha1 s (collarCellMap C ε hε a p) =
      collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)) :=
  CuspHoneycombHexagon.CommonFibres.descend_apply (collarCellMap C ε hε a)
    (fun p => collarCellMap C ε hε a (collarCellHomotopy a ha ha1 (s, p)))
    (collarCellMap_surjective C ε hε a) (collarCellHomotopy_compatible C ε hε a ha ha1 s) p

private theorem CuspCentralHomology.outerRegionDeformation_collarCellMap_coe
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (s : unitInterval) (p : CollarPhaseCell a) :
    (outerRegionDeformation C ε hε a ha ha1 s (collarCellMap C ε hε a p) :
        CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (p.1,
          ((1 - (s : ℝ)) + (s : ℝ) / Radial.cellGauge p.2) •
            (p.2 : (CuspHoneycombTiling.Plane))) := by
  rw [outerRegionDeformation_collarCellMap, collarCellMap_coe]
  change
    CuspHoneycomb.honeycombCollapseMap C ε hε
        (p.1,
          (Radial.outwardOpenCollarHomotopy a ha ha1 (s, p.2) : (CuspHoneycombTiling.Plane))) =
      _
  rw [Radial.outwardOpenCollarHomotopy_coe]

@[simp]
private theorem
    CuspCentralHomology.outerRegionDeformation_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (x : outerRegion C ε hε a) :
    outerRegionDeformation C ε hε a ha ha1 0 x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective C ε hε a x
  rw [outerRegionDeformation_collarCellMap, collarCellHomotopy_zero]

private theorem CuspCentralHomology.outerRegionDeformation_radius (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval)
    (x : outerRegion C ε hε a) :
    centralRadius C ε hε (outerRegionDeformation C ε hε a ha ha1 s x) =
      (1 - (s : ℝ)) * centralRadius C ε hε x + (s : ℝ) := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective C ε hε a x
  rw [outerRegionDeformation_collarCellMap, centralRadius_collarCellMap,
    centralRadius_collarCellMap]
  exact Radial.outwardOpenCollarHomotopy_gauge a ha ha1 s p.2

private theorem CuspCentralHomology.outerRegionDeformation_one_mem_boundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (x : outerRegion C ε hε a) :
    (outerRegionDeformation C ε hε a ha ha1 1 x : CuspRetraction.QuotientCentralFibre C ε) ∈
      centralBoundary C ε hε := by
  change centralRadius C ε hε (outerRegionDeformation C ε hε a ha ha1 1 x) = 1
  rw [outerRegionDeformation_radius]
  simp

private theorem CuspCentralHomology.outerRegionDeformation_fixed (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (s : unitInterval)
    (x : outerRegion C ε hε a)
    (hx : (x : CuspRetraction.QuotientCentralFibre C ε) ∈ centralBoundary C ε hε) :
    outerRegionDeformation C ε hε a ha ha1 s x = x := by
  obtain ⟨p, rfl⟩ := collarCellMap_surjective C ε hε a x
  have hp : (p.2 : (CuspHoneycombTiling.Plane)) ∈ frontier CuspHoneycombTiling.baseCell := by
    apply (Radial.mem_frontier_baseCell_iff _).mpr
    change centralRadius C ε hε (collarCellMap C ε hε a p) = 1 at hx
    rwa [centralRadius_collarCellMap] at hx
  rw [outerRegionDeformation_collarCellMap, collarCellHomotopy_fixed a ha ha1 s p hp]

private theorem
    CuspCentralHomology.outerRegionDeformation_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Continuous
      (fun p : unitInterval × outerRegion C ε hε a =>
        outerRegionDeformation C ε hε a ha ha1 p.1 p.2) := by
  apply (collarCellMap_isQuotientMap C ε hε a hε1 hC hR).continuous_lift_prod_right
  have hc := (collarCellMap_continuous C ε hε a).comp (collarCellHomotopy a ha ha1).continuous
  simpa only [outerRegionDeformation_collarCellMap, Function.comp_def, Prod.eta] using hc

private def CuspCentralHomology.outerRegionRetraction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : C(outerRegion C ε hε a, centralBoundary C ε hε)
    where
  toFun
    x :=
    ⟨outerRegionDeformation C ε hε a ha ha1 1 x,
      outerRegionDeformation_one_mem_boundary C ε hε a ha ha1 x⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          ((outerRegionDeformation_continuous C ε hε a ha ha1 hε1 hC hR).comp
            (continuous_const.prodMk continuous_id))).subtype_mk
      _

@[simp]
private theorem
    CuspCentralHomology.outerRegionRetraction_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (x : outerRegion C ε hε a) :
    (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR x :
        CuspRetraction.QuotientCentralFibre C ε) =
      outerRegionDeformation C ε hε a ha ha1 1 x :=
  rfl

private theorem
    CuspCentralHomology.outerRegionRetraction_collarCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : CollarPhaseCell a) :
    (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR (collarCellMap C ε hε a p) :
        CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (p.1, (Radial.cellGauge p.2)⁻¹ • (p.2 : (CuspHoneycombTiling.Plane))) := by
  rw [outerRegionRetraction_coe, outerRegionDeformation_collarCellMap_coe]
  simp

@[simp]
private theorem CuspCentralHomology.outerRegionRetraction_comp_inclusion
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR).comp
        (outerRegionBoundaryInclusion C ε hε a ha1) =
      ContinuousMap.id (centralBoundary C ε hε) := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change
    (outerRegionDeformation C ε hε a ha ha1 1 (outerRegionBoundaryInclusion C ε hε a ha1 x) :
        CuspRetraction.QuotientCentralFibre C ε) =
      x
  exact
    congrArg Subtype.val
      (outerRegionDeformation_fixed C ε hε a ha ha1 1
        (outerRegionBoundaryInclusion C ε hε a ha1 x) x.2)

private def CuspCentralHomology.outerRegionHomotopyRel (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    (ContinuousMap.id (outerRegion C ε hε a)).HomotopyRel
      ((outerRegionBoundaryInclusion C ε hε a ha1).comp
        (outerRegionRetraction C ε hε a ha ha1 hε1 hC hR))
      {x : outerRegion C ε hε a |
        (x : CuspRetraction.QuotientCentralFibre C ε) ∈ centralBoundary C ε hε}
    where
  toFun p := outerRegionDeformation C ε hε a ha ha1 p.1 p.2
  continuous_toFun := outerRegionDeformation_continuous C ε hε a ha ha1 hε1 hC hR
  map_zero_left := outerRegionDeformation_zero C ε hε a ha ha1
  map_one_left _ := rfl
  prop' := outerRegionDeformation_fixed C ε hε a ha ha1

private def CuspCentralHomology.outerRegionBoundaryHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : outerRegion C ε hε a ≃ₕ centralBoundary C ε hε
    where
  toFun := outerRegionRetraction C ε hε a ha ha1 hε1 hC hR
  invFun := outerRegionBoundaryInclusion C ε hε a ha1
  left_inv := ⟨(outerRegionHomotopyRel C ε hε a ha ha1 hε1 hC hR).toHomotopy.symm⟩
  right_inv := by
    refine ⟨?_⟩
    rw [outerRegionRetraction_comp_inclusion]
    exact ContinuousMap.Homotopy.refl _

@[simp]
private theorem CuspCentralHomology.outerRegionBoundaryHomotopyEquiv_apply
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (x : outerRegion C ε hε a) :
    outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR x =
      outerRegionRetraction C ε hε a ha ha1 hε1 hC hR x :=
  rfl

private abbrev CuspCentralHomology.BoundaryPhaseCell :=
  ToricSpace.CompactFibreTorus × Radial.CellFrontier

private theorem CuspCentralHomology.honeycombCollapseMap_frontier_mem_boundary
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (p : BoundaryPhaseCell) :
    CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) ∈
      centralBoundary C ε hε := by
  rw [centralBoundary_eq_image]
  exact ⟨(p.1, (p.2 : (CuspHoneycombTiling.Plane))), ⟨Set.mem_univ _, p.2.2⟩, rfl⟩

private def
    CuspCentralHomology.boundaryCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(BoundaryPhaseCell, centralBoundary C ε hε)
    where
  toFun
    p :=
    ⟨CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))),
      honeycombCollapseMap_frontier_mem_boundary C ε hε p⟩
  continuous_toFun := by
    have hi :
      Continuous (fun p : BoundaryPhaseCell => (p.1, (p.2 : (CuspHoneycombTiling.Plane)))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    exact ((CuspHoneycomb.honeycombCollapseMap_continuous C ε hε).comp hi).subtype_mk _

@[simp]
private theorem CuspCentralHomology.boundaryCellMap_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : BoundaryPhaseCell) :
    (boundaryCellMap C ε hε p : CuspRetraction.QuotientCentralFibre C ε) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (p.1, (p.2 : (CuspHoneycombTiling.Plane))) :=
  rfl

private def CuspCentralHomology.circleBoundaryCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : C(ToricSpace.CompactFibreTorus × Circle, centralBoundary C ε hε) :=
  (boundaryCellMap C ε hε).comp
    ⟨fun p => (p.1, Radial.frontierCellCircleHomeomorph.symm p.2),
      continuous_fst.prodMk
        (Radial.frontierCellCircleHomeomorph.symm.continuous.comp continuous_snd)⟩

@[simp]
private theorem
    CuspCentralHomology.circleBoundaryCellMap_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (p : ToricSpace.CompactFibreTorus × Circle) :
    circleBoundaryCellMap C ε hε p =
      boundaryCellMap C ε hε (p.1, Radial.frontierCellCircleHomeomorph.symm p.2) :=
  rfl

private def
    CuspCentralHomology.overlapIntoOuter (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (a : ℝ) : C(overlapRegion C ε hε a, outerRegion C ε hε a) :=
  ⟨fun q => ⟨(q : CuspRetraction.QuotientCentralFibre C ε), q.2.1⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp]
private theorem CuspCentralHomology.overlapIntoOuter_coe (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (a : ℝ) (q : overlapRegion C ε hε a) :
    (overlapIntoOuter C ε hε a q : CuspRetraction.QuotientCentralFibre C ε) =
      (q : CuspRetraction.QuotientCentralFibre C ε) :=
  rfl

private def
    CuspCentralHomology.annulusIntoCollar (a : ℝ) (p : OverlapPhaseCell a) : CollarPhaseCell a :=
  (p.1, ⟨(p.2 : (CuspHoneycombTiling.Plane)), p.2.2.1, p.2.2.2.le⟩)

private theorem
    CuspCentralHomology.overlapIntoOuter_phaseHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (p : OverlapPhaseCell a) :
    overlapIntoOuter C ε hε a (overlapPhaseHomeomorph C ε hε hε1 hC hR a p) =
      collarCellMap C ε hε a (annulusIntoCollar a p) := by
  apply Subtype.ext
  rw [overlapIntoOuter_coe, overlapPhaseHomeomorph_coe, collarCellMap_coe]
  rfl

private theorem CuspCentralHomology.outerRegionRetraction_overlapPhaseHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (p : OverlapPhaseCell a) :
    outerRegionRetraction C ε hε a ha ha1 hε1 hC hR
        (overlapIntoOuter C ε hε a (overlapPhaseHomeomorph C ε hε hε1 hC hR a p)) =
      boundaryCellMap C ε hε (p.1, (Radial.annulusHomeomorph a ha p.2).1) := by
  apply Subtype.ext
  rw [overlapIntoOuter_phaseHomeomorph, outerRegionRetraction_collarCellMap, boundaryCellMap_coe]
  rfl

private theorem CuspCentralHomology.overlapCircleHomotopyEquiv_phaseHomeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (p : OverlapPhaseCell a) :
    overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1
        (overlapPhaseHomeomorph C ε hε hε1 hC hR a p) =
      (p.1, Radial.annulusCircleHomotopyEquiv a ha ha1 p.2) := by
  change
    Radial.phaseAnnulusHomotopyEquiv ToricSpace.CompactFibreTorus a ha ha1
        ((overlapPhaseHomeomorph C ε hε hε1 hC hR a).symm
          (overlapPhaseHomeomorph C ε hε hε1 hC hR a p)) =
      _
  rw [Homeomorph.symm_apply_apply]
  rfl

private theorem
    CuspCentralHomology.overlapIntoOuter_boundary (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)
    (q : overlapRegion C ε hε a) :
    outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR (overlapIntoOuter C ε hε a q) =
      circleBoundaryCellMap C ε hε (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1 q) := by
  obtain ⟨p, rfl⟩ := (overlapPhaseHomeomorph C ε hε hε1 hC hR a).surjective q
  rw [outerRegionBoundaryHomotopyEquiv_apply, outerRegionRetraction_overlapPhaseHomeomorph,
    overlapCircleHomotopyEquiv_phaseHomeomorph, circleBoundaryCellMap_apply]
  congr 1
  apply Prod.ext
  · rfl
  · change
      (Radial.annulusHomeomorph a ha p.2).1 =
        Radial.frontierCellCircleHomeomorph.symm
          (Radial.frontierCellCircleHomeomorph (Radial.annulusHomeomorph a ha p.2).1)
    exact (Radial.frontierCellCircleHomeomorph.symm_apply_apply _).symm

private theorem CuspCentralHomology.overlapIntoOuter_boundary_map (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    (outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR).toFun.comp
        (overlapIntoOuter C ε hε a) =
      (circleBoundaryCellMap C ε hε).comp
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1).toFun := by
  apply ContinuousMap.ext
  intro q
  exact overlapIntoOuter_boundary C ε hε hε1 hC hR a ha ha1 q

private def CuspCentralHomology.phaseOrbitVertex : Radial.CellFrontier :=
  ⟨![(1 / 3 : ℝ), 1 / 3],
    (Radial.mem_frontier_baseCell_iff _).mpr (by norm_num [Radial.cellGauge])⟩

@[simp]
private theorem CuspCentralHomology.phaseOrbitVertex_coe :
    (phaseOrbitVertex : (CuspHoneycombTiling.Plane)) = ![(1 / 3 : ℝ), 1 / 3] :=
  rfl

private theorem CuspCentralHomology.phaseOrbitVertex_eq_triangleBarycenter :
    (phaseOrbitVertex : (CuspHoneycombTiling.Plane)) =
      CuspHoneycombTiling.triangleBarycenter (ToricComponent.zeroTriangle 0) := by
  rw [CuspHoneycombTiling.triangleBarycenter_zeroTriangle]
  funext i
  fin_cases i <;> norm_num [phaseOrbitVertex, ToricComponent.hexagonRay]

private theorem CuspCentralHomology.honeycombCollapseMap_phaseOrbitVertex
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (φ : ToricSpace.CompactFibreTorus) :
    CuspHoneycomb.honeycombCollapseMap C ε hε
        (φ, (phaseOrbitVertex : (CuspHoneycombTiling.Plane))) =
      CuspHoneycomb.honeycombCollapseMap C ε hε
        (1, (phaseOrbitVertex : (CuspHoneycombTiling.Plane))) := by
  apply (CuspHoneycomb.honeycombCollapseMap_eq_iff C ε hε _ _).mpr
  refine ⟨0, by simp, ?_⟩
  rw [phaseOrbitVertex_eq_triangleBarycenter,
    CuspHoneycomb.honeycombHomeomorph_stabilizer_triangleBarycenter]
  trivial

private theorem CuspCentralHomology.phaseOrbitAnchor_coe :
    (Radial.frontierCellCircleHomeomorph.symm 1 : (CuspHoneycombTiling.Plane)) =
      ![(1 / 2 : ℝ), 0] := by
  rw [Radial.frontierCellCircleHomeomorph_symm_coe]
  ext i
  fin_cases i <;> norm_num [Radial.cellGauge, Pi.smul_apply, smul_eq_mul]

private theorem CuspCentralHomology.phaseOrbitSegment_coordinates (s : unitInterval) :
    (1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : (CuspHoneycombTiling.Plane)) +
        (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : (CuspHoneycombTiling.Plane)) =
      ![(1 / 2 : ℝ) - (s : ℝ) / 6, (s : ℝ) / 3] := by
  ext i
  fin_cases i <;> simp [Pi.add_apply, smul_eq_mul] <;> ring

private theorem CuspCentralHomology.phaseOrbitSegment_mem_frontier (s : unitInterval) :
    (1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : (CuspHoneycombTiling.Plane)) +
        (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : (CuspHoneycombTiling.Plane)) ∈
      frontier CuspHoneycombTiling.baseCell := by
  apply (Radial.mem_frontier_baseCell_iff _).mpr
  rw [phaseOrbitSegment_coordinates]
  simp only [Radial.cellGauge, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : 2 * ((1 / 2 : ℝ) - (s : ℝ) / 6) + (s : ℝ) / 3 = 1 := by ring
  rw [h0, abs_one]
  apply max_eq_left
  apply max_le
  · apply abs_le.mpr
    constructor <;> linarith [s.2.1, s.2.2]
  · apply abs_le.mpr
    constructor <;> linarith [s.2.1, s.2.2]

private def CuspCentralHomology.phaseOrbitSegment : C(unitInterval, Radial.CellFrontier)
    where
  toFun
    s :=
    ⟨(1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : (CuspHoneycombTiling.Plane)) +
        (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : (CuspHoneycombTiling.Plane)),
      phaseOrbitSegment_mem_frontier s⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact
      ((continuous_const.sub continuous_subtype_val).smul continuous_const).add
        (continuous_subtype_val.smul continuous_const)

@[simp]
private theorem CuspCentralHomology.phaseOrbitSegment_coe (s : unitInterval) :
    (phaseOrbitSegment s : (CuspHoneycombTiling.Plane)) =
      (1 - (s : ℝ)) • (![(1 / 2 : ℝ), 0] : (CuspHoneycombTiling.Plane)) +
        (s : ℝ) • (![(1 / 3 : ℝ), 1 / 3] : (CuspHoneycombTiling.Plane)) :=
  rfl

@[simp]
private theorem CuspCentralHomology.phaseOrbitSegment_zero :
    phaseOrbitSegment 0 = Radial.frontierCellCircleHomeomorph.symm 1 := by
  apply Subtype.ext
  rw [phaseOrbitSegment_coe, phaseOrbitAnchor_coe]
  simp

@[simp]
private theorem
    CuspCentralHomology.phaseOrbitSegment_one : phaseOrbitSegment 1 = phaseOrbitVertex := by
  apply Subtype.ext
  rw [phaseOrbitSegment_coe, phaseOrbitVertex_coe]
  simp

private theorem
    CuspCentralHomology.boundaryCellMap_phaseOrbitVertex (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (φ : ToricSpace.CompactFibreTorus) :
    boundaryCellMap C ε hε (φ, phaseOrbitVertex) = boundaryCellMap C ε hε (1, phaseOrbitVertex) :=
  Subtype.ext (honeycombCollapseMap_phaseOrbitVertex C ε hε φ)

private def CuspCentralHomology.boundaryPhaseOrbit (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : C(ToricSpace.CompactFibreTorus, centralBoundary C ε hε) :=
  (circleBoundaryCellMap C ε hε).comp ⟨fun φ => (φ, 1), continuous_id.prodMk continuous_const⟩

private def
    CuspCentralHomology.boundaryPhaseOrbitHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    (boundaryPhaseOrbit C ε hε).Homotopy
      (ContinuousMap.const ToricSpace.CompactFibreTorus
        (boundaryCellMap C ε hε (1, phaseOrbitVertex)))
    where
  toFun p := boundaryCellMap C ε hε (p.2, phaseOrbitSegment p.1)
  continuous_toFun :=
    (boundaryCellMap C ε hε).continuous.comp
      (continuous_snd.prodMk (phaseOrbitSegment.continuous.comp continuous_fst))
  map_zero_left
    φ := by
    change boundaryCellMap C ε hε (φ, phaseOrbitSegment 0) = circleBoundaryCellMap C ε hε (φ, 1)
    rw [phaseOrbitSegment_zero, circleBoundaryCellMap_apply]
  map_one_left
    φ := by
    change boundaryCellMap C ε hε (φ, phaseOrbitSegment 1) = _
    rw [phaseOrbitSegment_one]
    exact boundaryCellMap_phaseOrbitVertex C ε hε φ

private theorem
    CuspCentralHomology.boundaryPhaseOrbit_nullhomotopic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : (boundaryPhaseOrbit C ε hε).Nullhomotopic :=
  ⟨boundaryCellMap C ε hε (1, phaseOrbitVertex), ⟨boundaryPhaseOrbitHomotopy C ε hε⟩⟩

private def CuspCentralHomology.innerRegionInclusion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : C(innerRegion C ε hε, CuspRetraction.QuotientCentralFibre C ε) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def
    CuspCentralHomology.innerRegionInclusionHomotopy (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    (innerRegionInclusion C ε hε).Homotopy
      (ContinuousMap.const (innerRegion C ε hε)
        (CuspHoneycomb.honeycombCollapseMap C ε hε
          (1, (phaseOrbitVertex : (CuspHoneycombTiling.Plane)))))
    where
  toFun
    p :=
    let x := (innerRegionHomeomorph C ε hε hε1 hC hR).symm p.2
    CuspHoneycomb.honeycombCollapseMap C ε hε
      (x.1,
        (1 - (p.1 : ℝ)) • (x.2 : (CuspHoneycombTiling.Plane)) +
          (p.1 : ℝ) • (phaseOrbitVertex : (CuspHoneycombTiling.Plane)))
  continuous_toFun := by
    have hx :=
      (innerRegionHomeomorph C ε hε hε1 hC hR).symm.continuous.comp
        (continuous_snd : Continuous (Prod.snd : unitInterval × innerRegion C ε hε → _))
    have hs : Continuous (fun p : unitInterval × innerRegion C ε hε => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact
      (CuspHoneycomb.honeycombCollapseMap_continuous C ε hε).comp
        ((continuous_fst.comp hx).prodMk
          (((continuous_const.sub hs).smul
                (continuous_subtype_val.comp (continuous_snd.comp hx))).add
            (hs.smul continuous_const)))
  map_zero_left
    q := by
    change
      CuspHoneycomb.honeycombCollapseMap C ε hε
          (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).1,
            (1 - (0 : ℝ)) •
                (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).2 :
                  (CuspHoneycombTiling.Plane)) +
              (0 : ℝ) • (phaseOrbitVertex : (CuspHoneycombTiling.Plane))) =
        (q : CuspRetraction.QuotientCentralFibre C ε)
    rw [sub_zero, one_smul, zero_smul, add_zero]
    simpa only [Homeomorph.apply_symm_apply] using
      (innerRegionHomeomorph_honeycomb C ε hε hε1 hC hR
          ((innerRegionHomeomorph C ε hε hε1 hC hR).symm q)).symm
  map_one_left
    q := by
    change
      CuspHoneycomb.honeycombCollapseMap C ε hε
          (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).1,
            (1 - (1 : ℝ)) •
                (((innerRegionHomeomorph C ε hε hε1 hC hR).symm q).2 :
                  (CuspHoneycombTiling.Plane)) +
              (1 : ℝ) • (phaseOrbitVertex : (CuspHoneycombTiling.Plane))) =
        _
    rw [sub_self, zero_smul, one_smul, zero_add]
    exact honeycombCollapseMap_phaseOrbitVertex C ε hε _

private theorem
    CuspCentralHomology.innerRegionInclusion_nullhomotopic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : (innerRegionInclusion C ε hε).Nullhomotopic :=
  ⟨CuspHoneycomb.honeycombCollapseMap C ε hε
      (1, (phaseOrbitVertex : (CuspHoneycombTiling.Plane))),
    ⟨innerRegionInclusionHomotopy C ε hε hε1 hC hR⟩⟩

private def
    CuspCentralHomology.boundaryLoop (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    C(Circle, centralBoundary C ε hε) :=
  (circleBoundaryCellMap C ε hε).comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩

@[simp]
private theorem CuspCentralHomology.boundaryLoop_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (z : Circle) : boundaryLoop C ε hε z = circleBoundaryCellMap C ε hε (1, z) :=
  rfl

private def CuspCentralHomology.centralBoundaryInclusion (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : C(centralBoundary C ε hε, CuspRetraction.QuotientCentralFibre C ε) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def CuspCentralHomology.boundaryLoopInCentral (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) : C(Circle, CuspRetraction.QuotientCentralFibre C ε) :=
  (centralBoundaryInclusion C ε hε).comp (boundaryLoop C ε hε)

private def CuspCentralHomology.boundaryLoopContraction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) :
    (boundaryLoopInCentral C ε hε).Homotopy
      (ContinuousMap.const Circle (CuspHoneycomb.honeycombCollapseMap C ε hε (1, 0)))
    where
  toFun
    p :=
    CuspHoneycomb.honeycombCollapseMap C ε hε
      (1,
        (1 - (p.1 : ℝ)) •
          (Radial.frontierCellCircleHomeomorph.symm p.2 : (CuspHoneycombTiling.Plane)))
  continuous_toFun :=
    (CuspHoneycomb.honeycombCollapseMap_continuous C ε hε).comp
      (continuous_const.prodMk
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
          (continuous_subtype_val.comp
            (Radial.frontierCellCircleHomeomorph.symm.continuous.comp continuous_snd))))
  map_zero_left
    z := by
    change
      CuspHoneycomb.honeycombCollapseMap C ε hε
          (1,
            (1 - (0 : ℝ)) •
              (Radial.frontierCellCircleHomeomorph.symm z : (CuspHoneycombTiling.Plane))) =
        CuspHoneycomb.honeycombCollapseMap C ε hε
          (1, (Radial.frontierCellCircleHomeomorph.symm z : (CuspHoneycombTiling.Plane)))
    simp only [sub_zero, one_smul]
  map_one_left
    z := by
    change
      CuspHoneycomb.honeycombCollapseMap C ε hε
          (1,
            (1 - (1 : ℝ)) •
              (Radial.frontierCellCircleHomeomorph.symm z : (CuspHoneycombTiling.Plane))) =
        CuspHoneycomb.honeycombCollapseMap C ε hε (1, 0)
    simp only [sub_self, zero_smul]

private theorem
    CuspCentralHomology.boundaryLoopInCentral_nullhomotopic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) : (boundaryLoopInCentral C ε hε).Nullhomotopic :=
  ⟨CuspHoneycomb.honeycombCollapseMap C ε hε (1, 0), ⟨boundaryLoopContraction C ε hε⟩⟩

private theorem CuspCentralHomology.centralBoundaryInclusion_comp_boundaryLoop_nullhomotopic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) :
    ((centralBoundaryInclusion C ε hε).comp (boundaryLoop C ε hε)).Nullhomotopic :=
  boundaryLoopInCentral_nullhomotopic C ε hε

private theorem
    CuspCentralHomology.centralBoundary_pathConnectedSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : PathConnectedSpace (centralBoundary C ε hε) :=
  (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm.surjective.pathConnectedSpace
    (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).symm.continuous

private theorem
    CuspCentralHomology.overlapRegion_pathConnectedSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    PathConnectedSpace (overlapRegion C ε hε a) := by
  let : PathConnectedSpace Radial.CellFrontier :=
    Radial.frontierCellCircleHomeomorph.symm.surjective.pathConnectedSpace
      Radial.frontierCellCircleHomeomorph.symm.continuous
  let : PathConnectedSpace (Set.Ioo a 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo a 1).isPathConnected (Set.nonempty_Ioo.mpr ha1))
  exact
    (overlapHomeomorph C ε hε hε1 hC hR a ha).symm.surjective.pathConnectedSpace
      (overlapHomeomorph C ε hε hε1 hC hR a ha).symm.continuous

private theorem
    CuspCentralHomology.halfCoverLeftHomologyZero_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Injective
      (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
        0) := by
  let := centralBoundary_pathConnectedSpace C ε hε hε1 hC hR
  let := overlapRegion_pathConnectedSpace C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num)
  let e := outerRegionBoundaryHomotopyEquiv C ε hε (1 / 2) (by norm_num) (by norm_num) hε1 hC hR
  let i : C((overlapRegion C ε hε (1 / 2)), (outerRegion C ε hε (1 / 2))) :=
    ContinuousMap.inclusion
      (Set.inter_subset_left :
        (outerRegion C ε hε (1 / 2)) ∩ (innerRegion C ε hε) ⊆ (outerRegion C ε hε (1 / 2)))
  let g : C((overlapRegion C ε hε (1 / 2)), (centralBoundary C ε hε)) := e.toFun.comp i
  intro a b hab
  have hi :
    SingularMayerVietoris.singularHomologyMap i 0 a =
      SingularMayerVietoris.singularHomologyMap i 0 b := by
    have h := congrArg Prod.fst hab
    simp only [SingularMayerVietoris.leftHomologyMap_apply] at h
    change
      SingularMayerVietoris.singularHomologyMap i 0 a =
        SingularMayerVietoris.singularHomologyMap i 0 b at h
    exact h
  have hg :
    SingularMayerVietoris.singularHomologyMap g 0 a =
      SingularMayerVietoris.singularHomologyMap g 0 b := by
    dsimp [g]
    rw [PeriodTorusHigherHomology.singularHomologyMap_comp]
    exact congrArg (SingularMayerVietoris.singularHomologyMap e.toFun 0) hi
  apply
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv
        (overlapRegion C ε hε (1 / 2))).injective
  have hn :=
    congrArg (PeriodTorusHigherHomology.connectedHomologyZeroEquiv (centralBoundary C ε hε)) hg
  exact
    (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural g a).symm.trans
      (hn.trans (PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural g b))

private theorem CuspCentralHomology.halfCoverRightHomologyOne_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective
      (SingularMayerVietoris.rightHomologyMap (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
        1) := by
  let hU := outerRegion_isOpen C ε hε hε1 hC hR (1 / 2)
  let hV := innerRegion_isOpen C ε hε hε1 hC hR
  let hc := outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)
  intro a
  have hz :
    SingularMayerVietoris.connectingHomomorphism (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
        hU hV hc 0 a =
      0 := by
    apply halfCoverLeftHomologyZero_injective C ε hε hε1 hC hR
    have h :=
      LinearMap.congr_fun
        (SingularMayerVietoris.connectingHomomorphism_comp_left (outerRegion C ε hε (1 / 2))
          (innerRegion C ε hε) hU hV hc 0)
        a
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using h
  have hm :
    a ∈
      LinearMap.ker
        (SingularMayerVietoris.connectingHomomorphism (outerRegion C ε hε (1 / 2))
          (innerRegion C ε hε) hU hV hc 0) :=
    hz
  rw [←
    SingularMayerVietoris.exact_at_ambient (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε) hU hV
      hc 0] at hm
  exact hm

private theorem CuspCentralHomology.innerRegionInclusion_homology_eq_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (innerRegionInclusion C ε hε) (n + 1) = 0 :=
  singularHomologyMap_eq_zero_of_nullhomotopic _
    (innerRegionInclusion_nullhomotopic C ε hε hε1 hC hR) (n + 1) (Nat.succ_ne_zero n)

private theorem CuspCentralHomology.centralBoundaryInclusion_homology_one_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 1) := by
  let e := outerRegionBoundaryHomotopyEquiv C ε hε (1 / 2) (by norm_num) (by norm_num) hε1 hC hR
  let E := PeriodTorusHigherHomology.homotopyEquivHomologyEquiv e 1
  have he :
    (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε (1 / 2))).comp e.symm.toFun =
      centralBoundaryInclusion C ε hε := by
    apply ContinuousMap.ext
    intro q
    rfl
  intro a
  obtain ⟨⟨x, y⟩, hxy⟩ := halfCoverRightHomologyOne_surjective C ε hε hε1 hC hR a
  refine ⟨E x, ?_⟩
  rw [← he, PeriodTorusHigherHomology.singularHomologyMap_comp]
  change
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε (1 / 2))) 1 (E.symm (E x)) =
      a
  rw [E.symm_apply_apply]
  have hv :
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion (innerRegion C ε hε)) 1 =
      0 :=
    innerRegionInclusion_homology_eq_zero C ε hε hε1 hC hR 0
  simpa only [SingularMayerVietoris.rightHomologyMap_apply, hv, LinearMap.zero_apply,
    add_zero] using hxy

private theorem CuspCentralHomology.centralBoundaryInclusion_homology_one_injective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 1) := by
  let := centralSingularH1_finite C ε hε hC
  let i :=
    (centralBoundaryHomologyOneEquiv C ε hε hε1 hC hR).trans
      (centralSingularH1Equiv C ε hε hC).symm
  exact
    IsNoetherian.injective_of_surjective_of_injective i.toLinearMap
      (SingularMayerVietoris.singularHomologyMap (centralBoundaryInclusion C ε hε) 1) i.injective
      (centralBoundaryInclusion_homology_one_surjective C ε hε hε1 hC hR)

private theorem
    CuspCentralHomology.boundaryLoop_homology_one_eq_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    SingularMayerVietoris.singularHomologyMap (boundaryLoop C ε hε) 1 = 0 := by
  have hzero :=
    singularHomologyMap_eq_zero_of_nullhomotopic _
      (centralBoundaryInclusion_comp_boundaryLoop_nullhomotopic C ε hε) 1 (by decide)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp] at hzero
  apply LinearMap.ext
  intro a
  apply centralBoundaryInclusion_homology_one_injective C ε hε hε1 hC hR
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply, map_zero] using
    LinearMap.congr_fun hzero a

@[simp]
private theorem
    CuspCentralHomology.centralCollapseMap_branchCount (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p : CuspCollapse.PhasePositiveSpace) :
    CuspQuotient.branchCount C ε (CuspCollapse.centralCollapseMap C ε hε p).1 =
      ToricSpace.branchCount (p.2.1 : ToricSpace.Space) := by
  change ToricSpace.branchCount (ToricSpace.compactFibreAction p.1 (p.2.1 : ToricSpace.Space)) = _
  exact ToricSpace.branchCount_torusAction _ _

@[simp]
private theorem
    CuspCentralHomology.fundamentalCellMap_branchCount (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (p : FundamentalCell) :
    CuspQuotient.branchCount C ε (fundamentalCellMap C ε hε p).1 =
      ToricSpace.branchCount
        ((CuspHoneycomb.honeycombHomeomorph (C 0) (p.2 : (CuspHoneycombTiling.Plane))).1 :
          ToricSpace.Space) :=
  centralCollapseMap_branchCount C ε hε
    (p.1, CuspHoneycomb.honeycombHomeomorph (C 0) (p.2 : (CuspHoneycombTiling.Plane)))

private theorem
    CuspCentralHomology.edgeArcPositive_branchCount_ge_two (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (k : Fin 6) (t : unitInterval) :
    2 ≤ ToricSpace.branchCount ((edgeArcPositive C₀ k t).1 : ToricSpace.Space) := by
  by_cases ht0 : t = 0
  · subst t
    rw [edgeArcPositive_zero_branchCount]
    decide
  by_cases ht1 : t = 1
  · subst t
    rw [edgeArcPositive_one_branchCount]
    decide
  rw [edgeArcPositive_branchCount C₀ k t ht0 ht1]

private theorem
    CuspCentralHomology.mem_centralBoundary_iff_branchCount (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (q : CuspRetraction.QuotientCentralFibre C ε) :
    q ∈ centralBoundary C ε hε ↔ 2 ≤ CuspQuotient.branchCount C ε q.1 := by
  constructor
  · intro hq
    obtain ⟨k, t, u, rfl⟩ := (mem_centralBoundary_iff_edgeArc C ε hε q).mp hq
    rw [centralCollapseMap_branchCount]
    exact edgeArcPositive_branchCount_ge_two (C 0) k t
  · intro hq
    obtain ⟨p, rfl⟩ := fundamentalCellMap_surjective C ε hε q
    apply (fundamentalCellMap_mem_centralBoundary_iff C ε hε p).mpr
    by_contra hp
    have hi : (p.2 : (CuspHoneycombTiling.Plane)) ∈ interior CuspHoneycombTiling.baseCell :=
      (mem_interior_iff_notMem_frontier p.2.2).mpr hp
    have hb :
      ToricSpace.branchCount
          ((CuspHoneycomb.honeycombHomeomorph (C 0) (p.2 : (CuspHoneycombTiling.Plane))).1 :
            ToricSpace.Space) =
        1 :=
      (CuspHoneycomb.honeycombHomeomorph_branchCount_eq_one_iff (C 0)
            (p.2 : (CuspHoneycombTiling.Plane))).mpr
        ⟨0, by simpa only [CuspHoneycombTiling.cell_zero] using hi⟩
    rw [fundamentalCellMap_branchCount, hb] at hq
    exact (by decide : ¬2 ≤ (1 : ℕ)) hq

private def CuspCentralHomology.phaseMultiply (u : ToricSpace.CompactFibreTorus)
    (p : CuspCollapse.PhasePositiveSpace) : CuspCollapse.PhasePositiveSpace :=
  (u * p.1, p.2)

private theorem
    CuspCentralHomology.centralCollapseRelation_phaseMultiply (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : ToricSpace.CompactFibreTorus) (p q : CuspCollapse.PhasePositiveSpace)
    (h : CuspCollapse.centralCollapseRelation C₀ p q) :
    CuspCollapse.centralCollapseRelation C₀ (phaseMultiply u p) (phaseMultiply u q) := by
  obtain ⟨v, hv, hu⟩ := h
  refine ⟨v, hv, ?_⟩
  change
    (u * p.1)⁻¹ * (CuspCollapse.deckFibrePhase C₀ v * (u * q.1)) ∈
      MulAction.stabilizer ToricSpace.CompactFibreTorus (p.2.1 : ToricSpace.Space)
  have he :
    (u * p.1)⁻¹ * (CuspCollapse.deckFibrePhase C₀ v * (u * q.1)) =
      p.1⁻¹ * (CuspCollapse.deckFibrePhase C₀ v * q.1) := by
    calc
      _ = p.1⁻¹ * ((u⁻¹ * u) * (CuspCollapse.deckFibrePhase C₀ v * q.1)) := by
        simp only [mul_inv_rev]
        ac_rfl
      _ = p.1⁻¹ * (CuspCollapse.deckFibrePhase C₀ v * q.1) := by rw [inv_mul_cancel, one_mul]
  rw [he]
  exact hu

private def CuspCentralHomology.phaseMultiplyModel (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (u : ToricSpace.CompactFibreTorus) :
    CuspCollapse.CentralCollapseModel C₀ → CuspCollapse.CentralCollapseModel C₀ :=
  Quotient.map' (phaseMultiply u) (centralCollapseRelation_phaseMultiply C₀ u)

private def
    CuspCentralHomology.centralPhaseAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (u : ToricSpace.CompactFibreTorus) (x : CuspRetraction.QuotientCentralFibre C ε) :
    CuspRetraction.QuotientCentralFibre C ε :=
  CuspCollapse.centralCollapseModelMap C ε hε
    (phaseMultiplyModel (C 0) u ((CuspCollapse.centralCollapseEquiv C ε hε).symm x))

@[simp]
private theorem
    CuspCentralHomology.centralPhaseAction_collapse (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (p : CuspCollapse.PhasePositiveSpace) :
    centralPhaseAction C ε hε u (CuspCollapse.centralCollapseMap C ε hε p) =
      CuspCollapse.centralCollapseMap C ε hε (u * p.1, p.2) := by
  unfold centralPhaseAction
  rw [CuspCollapse.centralCollapseEquiv_symm_map]
  rfl

@[simp]
private theorem
    CuspCentralHomology.centralPhaseAction_branchCount (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (x : CuspRetraction.QuotientCentralFibre C ε) :
    CuspQuotient.branchCount C ε (centralPhaseAction C ε hε u x).1 =
      CuspQuotient.branchCount C ε x.1 := by
  obtain ⟨p, rfl⟩ := CuspCollapse.centralCollapseMap_surjective C ε hε x
  rw [centralPhaseAction_collapse, centralCollapseMap_branchCount, centralCollapseMap_branchCount]

private theorem
    CuspCentralHomology.centralPhaseAction_mem_boundary_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (x : CuspRetraction.QuotientCentralFibre C ε) :
    centralPhaseAction C ε hε u x ∈ centralBoundary C ε hε ↔ x ∈ centralBoundary C ε hε := by
  rw [mem_centralBoundary_iff_branchCount, centralPhaseAction_branchCount,
    mem_centralBoundary_iff_branchCount]

private def CuspCentralHomology.boundaryPhaseAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (x : centralBoundary C ε hε) :
    centralBoundary C ε hε :=
  ⟨centralPhaseAction C ε hε u x.1, (centralPhaseAction_mem_boundary_iff C ε hε u x.1).mpr x.2⟩

private theorem CuspCentralHomology.centralPhaseAction_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    Continuous
      (fun p : ToricSpace.CompactFibreTorus × CuspRetraction.QuotientCentralFibre C ε =>
        centralPhaseAction C ε hε p.1 p.2) := by
  apply (CuspCollapse.centralCollapseMap_isQuotientMap C ε hε hC).continuous_lift_prod_right
  have hm :
    Continuous
      (fun p : ToricSpace.CompactFibreTorus × CuspCollapse.PhasePositiveSpace =>
        (p.1 * p.2.1, p.2.2)) :=
    (continuous_fst.mul continuous_snd.fst).prodMk continuous_snd.snd
  exact
    ((CuspCollapse.centralCollapseMap_continuous C ε hε).comp hm).congr
      (fun p => (centralPhaseAction_collapse C ε hε p.1 p.2).symm)

private theorem
    CuspCentralHomology.boundaryPhaseAction_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    Continuous
      (fun p : ToricSpace.CompactFibreTorus × centralBoundary C ε hε =>
        boundaryPhaseAction C ε hε p.1 p.2) :=
  ((centralPhaseAction_continuous C ε hε hC).comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk
    _

private def CuspCentralHomology.boundaryPhaseActionMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    C(ToricSpace.CompactFibreTorus × centralBoundary C ε hε, centralBoundary C ε hε) :=
  ⟨fun p => boundaryPhaseAction C ε hε p.1 p.2, boundaryPhaseAction_continuous C ε hε hC⟩

@[simp]
private theorem CuspCentralHomology.centralPhaseAction_honeycombCollapseMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (p : CuspHoneycomb.PhasePlane) :
    centralPhaseAction C ε hε u (CuspHoneycomb.honeycombCollapseMap C ε hε p) =
      CuspHoneycomb.honeycombCollapseMap C ε hε (u * p.1, p.2) :=
  centralPhaseAction_collapse C ε hε u (p.1, CuspHoneycomb.honeycombHomeomorph (C 0) p.2)

@[simp]
private theorem
    CuspCentralHomology.boundaryPhaseAction_boundaryCellMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (p : BoundaryPhaseCell) :
    boundaryPhaseAction C ε hε u (boundaryCellMap C ε hε p) =
      boundaryCellMap C ε hε (u * p.1, p.2) := by
  apply Subtype.ext
  exact centralPhaseAction_honeycombCollapseMap C ε hε u (p.1, p.2)

private theorem CuspCentralHomology.boundaryPhaseAction_circleBoundaryCellMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus)
    (p : ToricSpace.CompactFibreTorus × Circle) :
    boundaryPhaseAction C ε hε u (circleBoundaryCellMap C ε hε p) =
      circleBoundaryCellMap C ε hε (u * p.1, p.2) := by
  rw [circleBoundaryCellMap_apply, boundaryPhaseAction_boundaryCellMap,
    circleBoundaryCellMap_apply]

private theorem
    CuspCentralHomology.circleBoundaryCellMap_phaseAction (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (u : ToricSpace.CompactFibreTorus) (z : Circle) :
    circleBoundaryCellMap C ε hε (u, z) = boundaryPhaseAction C ε hε u (boundaryLoop C ε hε z) := by
  rw [boundaryLoop_apply, boundaryPhaseAction_circleBoundaryCellMap, mul_one]

private theorem CuspCentralHomology.circleBoundaryCellMap_eq_phaseAction
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun t => C t i j) (Metric.ball 0 ε)) :
    circleBoundaryCellMap C ε hε =
      (boundaryPhaseActionMap C ε hε hC).comp
        ((ContinuousMap.id ToricSpace.CompactFibreTorus).prodMap (boundaryLoop C ε hε)) := by
  apply ContinuousMap.ext
  intro p
  exact circleBoundaryCellMap_phaseAction C ε hε p.1 p.2

private def CuspCentralHomology.circleCoordinateHomeomorph : Circle ≃ₜ AddCircle (1 : ℝ) :=
  (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm

@[simp]
private theorem CuspCentralHomology.circleCoordinateHomeomorph_symm_apply (x : AddCircle (1 : ℝ)) :
    circleCoordinateHomeomorph.symm x = AddCircle.toCircle x :=
  AddCircle.homeomorphCircle_apply one_ne_zero x

private theorem CuspCentralHomology.circleCoordinateHomeomorph_mul (u v : Circle) :
    circleCoordinateHomeomorph (u * v) =
      circleCoordinateHomeomorph u + circleCoordinateHomeomorph v := by
  apply circleCoordinateHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply, circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_add,
    ← circleCoordinateHomeomorph_symm_apply, ← circleCoordinateHomeomorph_symm_apply,
    Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]

private theorem CuspCentralHomology.circleCoordinateHomeomorph_zpow (u : Circle) (n : ℤ) :
    circleCoordinateHomeomorph (u ^ n) = n • circleCoordinateHomeomorph u := by
  apply circleCoordinateHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply, circleCoordinateHomeomorph_symm_apply,
    AddCircle.toCircle_zsmul, ← circleCoordinateHomeomorph_symm_apply,
    Homeomorph.symm_apply_apply]

private theorem CuspCentralHomology.circleCoordinateHomeomorph_exp (x : ℝ) :
    circleCoordinateHomeomorph (Circle.exp (2 * Real.pi * x)) = (x : AddCircle (1 : ℝ)) := by
  apply circleCoordinateHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply, circleCoordinateHomeomorph_symm_apply,
    AddCircle.toCircle_apply_mk, div_one]

private def CuspCentralHomology.compactFibreTorusHomeomorph :
    ToricSpace.CompactFibreTorus ≃ₜ PeriodTorusHigherHomology.ProductTorus 2 :=
  Homeomorph.piCongrRight (fun _ : Fin 2 => circleCoordinateHomeomorph)

private theorem
    CuspCentralHomology.compactFibreTorusHomeomorph_mul (u v : ToricSpace.CompactFibreTorus) :
    compactFibreTorusHomeomorph (u * v) =
      compactFibreTorusHomeomorph u + compactFibreTorusHomeomorph v := by
  funext i
  exact circleCoordinateHomeomorph_mul (u i) (v i)

private theorem CuspCentralHomology.compactFibreTorusHomeomorph_exp (x : Fin 2 → ℝ) :
    compactFibreTorusHomeomorph (fun i => Circle.exp (2 * Real.pi * x i)) =
      PeriodTorusHigherHomology.coordinateProjection 2 x := by
  funext i
  exact circleCoordinateHomeomorph_exp (x i)

private def CuspCentralHomology.productTorusLastHomeomorph (n : ℕ) :
    PeriodTorusHigherHomology.ProductTorus (n + 1) ≃ₜ
      PeriodTorusHigherHomology.ProductTorus n × AddCircle (1 : ℝ)
    where
  toFun x := (fun i => x i.castSucc, x (Fin.last n))
  invFun p := Fin.snoc p.1 p.2
  left_inv x := Fin.snoc_init_self x
  right_inv p := by simp only [Fin.snoc_castSucc, Fin.snoc_last]
  continuous_toFun :=
    (continuous_pi (fun i => continuous_apply i.castSucc)).prodMk (continuous_apply (Fin.last n))
  continuous_invFun := by
    apply continuous_pi
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using
        (continuous_snd :
          Continuous
            (fun p : PeriodTorusHigherHomology.ProductTorus n × AddCircle (1 : ℝ) => p.2))
    · simpa only [Fin.snoc_castSucc, Function.comp_def] using
        ((continuous_apply j).comp continuous_fst :
          Continuous
            (fun p : PeriodTorusHigherHomology.ProductTorus n × AddCircle (1 : ℝ) => p.1 j))

private def CuspCentralHomology.fibreTorusCircleHomeomorph :
    (ToricSpace.CompactFibreTorus × Circle) ≃ₜ PeriodTorusHigherHomology.ProductTorus 3 :=
  (compactFibreTorusHomeomorph.prodCongr circleCoordinateHomeomorph).trans
    (productTorusLastHomeomorph 2).symm

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.circleParametrizedMap {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (a : C(X × D, D)) (α : C(_root_.Circle, D)) : C(X × _root_.Circle, D) :=
  a.comp ((ContinuousMap.id X).prodMap α)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.circleParametrizedOrbit {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (a : C(X × D, D)) (α : C(_root_.Circle, D)) : C(X, D) :=
  a.comp ((ContinuousMap.id X).prodMk (ContinuousMap.const X (α 1)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.circleParametrizedSourceHomeomorph (X : Type) [TopologicalSpace X] :
    (AddCircle (1 : ℝ) × X) ≃ₜ (X × _root_.Circle) :=
  (circleCoordinateHomeomorph.symm.prodCongr (Homeomorph.refl X)).trans
    (Homeomorph.prodComm _root_.Circle X)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.additiveCircleParametrizedMap {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (a : C(X × D, D)) (β : C(AddCircle (1 : ℝ), D)) :
    C(AddCircle (1 : ℝ) × X, D) :=
  (a.comp (Homeomorph.prodComm D X : C(D × X, X × D))).comp (β.prodMap (ContinuousMap.id X))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    CuspCentralHomology.circleParametrizedMap_comp_source {X D : Type} [TopologicalSpace X]
    [TopologicalSpace D] (a : C(X × D, D)) (α : C(_root_.Circle, D)) :
    (circleParametrizedMap a α).comp
        (circleParametrizedSourceHomeomorph X : C(AddCircle (1 : ℝ) × X, X × _root_.Circle)) =
      additiveCircleParametrizedMap a
        (α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.parameterMap_positiveCircleCross_eq_zero {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (β : C(AddCircle (1 : ℝ), D))
    (hβ : SingularMayerVietoris.singularHomologyMap β 1 = 0) (n : ℕ)
    (b : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross X n b) =
      0 := by
  have h :=
    PeriodTorusHigherHomology.crossProductHomology_natural β (ContinuousMap.id X) n
      (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop) b
  change
    SingularMayerVietoris.singularHomologyMap (β.prodMap (ContinuousMap.id X)) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross X n b) =
      PeriodTorusHigherHomology.crossProductHomology D X n
        (SingularMayerVietoris.singularHomologyMap β 1
          (FirstHurewicz.loopHomologyClass PeriodTorusHigherHomology.CirclePaths.positiveLoop))
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.id X) n b) at h
  rw [hβ, LinearMap.zero_apply, map_zero, LinearMap.zero_apply] at h
  exact h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.additiveCircleParametrizedHomologyMap_eq_zero {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (a : C(X × D, D)) (β : C(AddCircle (1 : ℝ), D))
    (hβ : SingularMayerVietoris.singularHomologyMap β 1 = 0) (n : ℕ)
    (hsection :
      SingularMayerVietoris.singularHomologyMap
          ((additiveCircleParametrizedMap a β).comp
            (PeriodTorusHigherHomology.CircleTopology.productSection X))
          (n + 1) =
        0) :
    SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1) = 0 := by
  have hs (c : SingularMayerVietoris.SingularHomology X (n + 1)) :
    SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1)
        (PeriodTorusHigherHomology.circleSectionHomology X (n + 1) c) =
      0 := by
    change
      ((SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β)
                (n + 1)).comp
            (SingularMayerVietoris.singularHomologyMap
              (PeriodTorusHigherHomology.CircleTopology.productSection X) (n + 1)))
          c =
        0
    rw [← PeriodTorusHigherHomology.singularHomologyMap_comp, hsection, LinearMap.zero_apply]
  have hc (c : SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1)
        (PeriodTorusHigherHomology.positiveCircleCross X n c) =
      0 := by
    rw [additiveCircleParametrizedMap, PeriodTorusHigherHomology.singularHomologyMap_comp,
      LinearMap.comp_apply, parameterMap_positiveCircleCross_eq_zero β hβ, map_zero]
  apply LinearMap.ext
  intro c
  change
    SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1) c = 0
  obtain ⟨p, rfl⟩ := (PeriodTorusHigherHomology.circleProductHomologyEquiv X n).symm.surjective c
  rw [PeriodTorusHigherHomology.circleProductHomologyEquiv_symm_eq_section_add_cross, map_add, hs,
    hc, add_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.circleParametrizedHomologyMap_eq_zero {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (a : C(X × D, D)) (α : C(_root_.Circle, D))
    (hα : SingularMayerVietoris.singularHomologyMap α 1 = 0) (n : ℕ)
    (horbit :
      SingularMayerVietoris.singularHomologyMap (circleParametrizedOrbit a α) (n + 1) = 0) :
    SingularMayerVietoris.singularHomologyMap (circleParametrizedMap a α) (n + 1) = 0 := by
  let β : C(AddCircle (1 : ℝ), D) :=
    α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))
  have hβ : SingularMayerVietoris.singularHomologyMap β 1 = 0 := by
    rw [show β = α.comp (circleCoordinateHomeomorph.symm : C(AddCircle (1 : ℝ), _root_.Circle))
        from rfl,
      PeriodTorusHigherHomology.singularHomologyMap_comp, hα, LinearMap.zero_comp]
  have hsectionMap :
    (additiveCircleParametrizedMap a β).comp
        (PeriodTorusHigherHomology.CircleTopology.productSection X) =
      circleParametrizedOrbit a α := by
    apply ContinuousMap.ext
    intro x
    change a (x, α (circleCoordinateHomeomorph.symm 0)) = a (x, α 1)
    rw [circleCoordinateHomeomorph_symm_apply, AddCircle.toCircle_zero]
  have hzero :
    SingularMayerVietoris.singularHomologyMap (additiveCircleParametrizedMap a β) (n + 1) = 0 :=
    additiveCircleParametrizedHomologyMap_eq_zero a β hβ n (by rw [hsectionMap]; exact horbit)
  have hcomp :
    (SingularMayerVietoris.singularHomologyMap (circleParametrizedMap a α) (n + 1)).comp
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X)
            (n + 1)).toLinearMap =
      0 := by
    rw [PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap, ←
      PeriodTorusHigherHomology.singularHomologyMap_comp, circleParametrizedMap_comp_source]
    exact hzero
  apply LinearMap.ext
  intro c
  obtain ⟨d, rfl⟩ :=
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X)
          (n + 1)).surjective
      c
  exact LinearMap.congr_fun hcomp d

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    CuspCentralHomology.circleParametrizedHomologyMap_eq_zero_of_nullhomotopic {X D : Type}
    [TopologicalSpace X] [TopologicalSpace D] (a : C(X × D, D)) (α : C(_root_.Circle, D))
    (hα : SingularMayerVietoris.singularHomologyMap α 1 = 0) (n : ℕ)
    (horbit : (circleParametrizedOrbit a α).Nullhomotopic) :
    SingularMayerVietoris.singularHomologyMap (circleParametrizedMap a α) (n + 1) = 0 :=
  circleParametrizedHomologyMap_eq_zero a α hα n
    (singularHomologyMap_eq_zero_of_nullhomotopic _ horbit (n + 1) (Nat.succ_ne_zero n))

private theorem CuspCentralHomology.boundaryPhaseAction_parametrizedOrbit
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε)) :
    circleParametrizedOrbit (boundaryPhaseActionMap C ε hε hC) (boundaryLoop C ε hε) =
      boundaryPhaseOrbit C ε hε := by
  apply ContinuousMap.ext
  intro u
  exact (circleBoundaryCellMap_phaseAction C ε hε u 1).symm

private theorem CuspCentralHomology.circleBoundaryCellMap_homology_eq_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (circleBoundaryCellMap C ε hε) (n + 1) = 0 := by
  rw [circleBoundaryCellMap_eq_phaseAction C ε hε hC]
  change
    SingularMayerVietoris.singularHomologyMap
        (circleParametrizedMap (boundaryPhaseActionMap C ε hε hC) (boundaryLoop C ε hε)) (n + 1) =
      0
  apply circleParametrizedHomologyMap_eq_zero_of_nullhomotopic
  · exact boundaryLoop_homology_one_eq_zero C ε hε hε1 hC hR
  · rw [boundaryPhaseAction_parametrizedOrbit]
    exact boundaryPhaseOrbit_nullhomotopic C ε hε

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def CuspCentralHomology.rightCircleSection (X : Type) [TopologicalSpace X] :
    C(X, X × _root_.Circle) :=
  (ContinuousMap.id X).prodMk (ContinuousMap.const X 1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.rightCircleProjection_section (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
            n).comp
        (SingularMayerVietoris.singularHomologyMap (rightCircleSection X) n) =
      LinearMap.id := by
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact PeriodTorusHigherHomology.singularHomologyMap_id X n

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.rightCircleProjection_surjective_allDegrees (X : Type)
    [TopologicalSpace X] (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
        n) := by
  intro a
  exact
    ⟨SingularMayerVietoris.singularHomologyMap (rightCircleSection X) n a,
      LinearMap.congr_fun (rightCircleProjection_section X n) a⟩

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem CuspCentralHomology.rightCircleProjection_surjective (X : Type) [TopologicalSpace X]
    (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
        (n + 1)) :=
  rightCircleProjection_surjective_allDegrees X (n + 1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    CuspCentralHomology.rightCircleProductHomologyEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    SingularMayerVietoris.SingularHomology (X × _root_.Circle) (n + 1) ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv (circleParametrizedSourceHomeomorph X).symm
        (n + 1)).trans
    (PeriodTorusHigherHomology.circleProductHomologyEquiv X n)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    CuspCentralHomology.rightCircleProductHomologyEquiv_fst (X : Type) [TopologicalSpace X]
    (n : ℕ) (a : SingularMayerVietoris.SingularHomology (X × _root_.Circle) (n + 1)) :
    (rightCircleProductHomologyEquiv X n a).1 =
      SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
        (n + 1) a := by
  change
    PeriodTorusHigherHomology.circleProjectionHomology X (n + 1)
        (SingularMayerVietoris.singularHomologyMap
          ((circleParametrizedSourceHomeomorph X).symm :
            C(X × _root_.Circle, AddCircle (1 : ℝ) × X))
          (n + 1) a) =
      _
  rw [← LinearMap.comp_apply, ← PeriodTorusHigherHomology.singularHomologyMap_comp]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem CuspCentralHomology.rightCircleProductHomologyEquiv_symm_projection (X : Type)
    [TopologicalSpace X] (n : ℕ)
    (a :
      SingularMayerVietoris.SingularHomology X (n + 1) ×
        SingularMayerVietoris.SingularHomology X n) :
    SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
        (n + 1) ((rightCircleProductHomologyEquiv X n).symm a) =
      a.1 := by rw [← rightCircleProductHomologyEquiv_fst, LinearEquiv.apply_symm_apply]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    CuspCentralHomology.rightCircleProjectionKernelEquiv (X : Type) [TopologicalSpace X] (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
          (n + 1)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology X n :=
  ({    toFun a := (rightCircleProductHomologyEquiv X n a).2
        invFun
          b :=
          ⟨(rightCircleProductHomologyEquiv X n).symm (0, b), by
            rw [LinearMap.mem_ker, rightCircleProductHomologyEquiv_symm_projection]⟩
        left_inv
          a := by
          apply Subtype.ext
          apply (rightCircleProductHomologyEquiv X n).injective
          rw [LinearEquiv.apply_symm_apply]
          apply Prod.ext
          · rw [rightCircleProductHomologyEquiv_fst]
            exact a.property.symm
          · rfl
        right_inv
          b := by
          change
            ((rightCircleProductHomologyEquiv X n)
                  ((rightCircleProductHomologyEquiv X n).symm (0, b))).2 =
              b
          rw [LinearEquiv.apply_symm_apply]
        map_add' a
          b := by
          change (rightCircleProductHomologyEquiv X n ((a : _) + b)).2 = _
          rw [map_add]
          rfl } :
      LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap (ContinuousMap.fst : C(X × _root_.Circle, X))
            (n + 1)) ≃+
        SingularMayerVietoris.SingularHomology X n).toIntLinearEquiv

private def CuspCentralHomology.compactFibreTorusHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n ≃ₗ[ℤ]
      PeriodTorusHigherHomology.binomialModule 2 n :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv compactFibreTorusHomeomorph n).trans
    (PeriodTorusHigherHomology.productTorusHomologyEquiv 2 n)

private def CuspCentralHomology.fibreTorusCircleHomologyEquiv (n : ℕ) :
    SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) n ≃ₗ[ℤ]
      PeriodTorusHigherHomology.binomialModule 3 n :=
  (PeriodTorusHigherHomology.homeomorphHomologyEquiv fibreTorusCircleHomeomorph n).trans
    (PeriodTorusHigherHomology.productTorusHomologyEquiv 3 n)

private def CuspCentralHomology.fibreTorusCircleHomologyThreeEquiv :
    SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) 3 ≃ₗ[ℤ] ℤ :=
  (fibreTorusCircleHomologyEquiv 3).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)

private theorem
    CuspCentralHomology.compactFibreTorus_homology_subsingleton_of_lt {n : ℕ} (hn : 2 < n) :
    Subsingleton (SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt hn
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv compactFibreTorusHomeomorph
        n).injective.subsingleton

private theorem CuspCentralHomology.compactFibreTorus_homology_subsingleton (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus (n + 3)) :=
  compactFibreTorus_homology_subsingleton_of_lt (by omega)

private theorem
    CuspCentralHomology.fibreTorusCircle_homology_subsingleton_of_lt {n : ℕ} (hn : 3 < n) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) n) := by
  let := PeriodTorusHigherHomology.productTorus_homology_subsingleton_of_lt hn
  exact
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv fibreTorusCircleHomeomorph
        n).injective.subsingleton

private theorem CuspCentralHomology.fibreTorusCircle_homology_subsingleton (n : ℕ) :
    Subsingleton
      (SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) (n + 4)) :=
  fibreTorusCircle_homology_subsingleton_of_lt (by omega)

private def
    CuspCentralHomology.outerRegionSuspensionHomotopyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    outerRegion C ε hε a ≃ₕ ThreeCircleSuspension :=
  (outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR).trans
    (centralBoundarySuspensionHomeomorph C ε hε hε1 hC hR).toHomotopyEquiv


private def
    CuspCentralHomology.overlapRegionHomologyThreeEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) 3 ≃ₗ[ℤ] ℤ :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) 3).trans
    fibreTorusCircleHomologyThreeEquiv

private theorem
    CuspCentralHomology.outerRegion_homology_subsingleton (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology (outerRegion C ε hε a) (n + 3)) := by
  let := threeCircleSuspension_homology_subsingleton n
  exact
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (outerRegionSuspensionHomotopyEquiv C ε hε hε1 hC hR a ha ha1)
        (n + 3)).injective.subsingleton

private theorem
    CuspCentralHomology.innerRegion_homology_subsingleton (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology (innerRegion C ε hε) (n + 3)) := by
  let := compactFibreTorus_homology_subsingleton n
  exact
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (innerRegionHomotopyEquiv C ε hε hε1 hC hR) (n + 3)).injective.subsingleton

private theorem
    CuspCentralHomology.overlapRegion_homology_subsingleton (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    Subsingleton (SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) (n + 4)) := by
  let := fibreTorusCircle_homology_subsingleton n
  exact
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) (n + 4)).injective.subsingleton

private def CuspCentralHomology.middleInnerHomologyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (innerRegion C ε hε) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv (innerRegionHomotopyEquiv C ε hε hε1 hC hR)
    n

private def
    CuspCentralHomology.middleOverlapHomologyEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) n ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (ToricSpace.CompactFibreTorus × Circle) n :=
  PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
    (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) n

private theorem
    CuspCentralHomology.overlapIntoOuter_homology_eq_zero (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    SingularMayerVietoris.singularHomologyMap (overlapIntoOuter C ε hε a) (n + 1) = 0 := by
  have hm :=
    congrArg
      (fun f : C((overlapRegion C ε hε a), centralBoundary C ε hε) =>
        SingularMayerVietoris.singularHomologyMap f (n + 1))
      (overlapIntoOuter_boundary_map C ε hε hε1 hC hR a ha ha1)
  rw [PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    circleBoundaryCellMap_homology_eq_zero C ε hε hε1 hC hR n] at hm
  apply LinearMap.ext
  intro z
  apply
    (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR) (n + 1)).injective
  simpa only [PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, map_zero] using LinearMap.congr_fun hm z

private theorem CuspCentralHomology.middleInnerProjection_natural (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    (middleInnerHomologyEquiv C ε hε hε1 hC hR n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) n) =
      (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.fst :
              C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
            n).comp
        (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 n).toLinearMap := by
  have hm :=
    congrArg
      (fun f : C((overlapRegion C ε hε a), ToricSpace.CompactFibreTorus) =>
        SingularMayerVietoris.singularHomologyMap f n)
      (overlapIntoInner_phase_map C ε hε hε1 hC hR a ha ha1)
  simpa only [PeriodTorusHigherHomology.singularHomologyMap_comp, middleInnerHomologyEquiv,
    middleOverlapHomologyEquiv,
    PeriodTorusHigherHomology.homotopyEquivHomologyEquiv_toLinearMap] using hm

private theorem
    CuspCentralHomology.middleInnerProjection_zero_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (z : SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) n) :
    SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) n z = 0 ↔
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          n (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 n z) =
        0 := by
  have hm := LinearMap.congr_fun (middleInnerProjection_natural C ε hε hε1 hC hR a ha ha1 n) z
  change
    middleInnerHomologyEquiv C ε hε hε1 hC hR n
        (SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) n z) =
      _ at hm
  constructor
  · intro hz
    rw [hz, map_zero] at hm
    exact hm.symm
  · intro hz
    apply (middleInnerHomologyEquiv C ε hε hε1 hC hR n).injective
    simpa only [map_zero] using hm.trans hz

private theorem CuspCentralHomology.overlapIntoInner_homology_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    Function.Surjective
      (SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) (n + 1)) := by
  intro z
  obtain ⟨w, hw⟩ :=
    rightCircleProjection_surjective ToricSpace.CompactFibreTorus n
      (middleInnerHomologyEquiv C ε hε hε1 hC hR (n + 1) z)
  refine ⟨(middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)).symm w, ?_⟩
  apply (middleInnerHomologyEquiv C ε hε hε1 hC hR (n + 1)).injective
  have hm :=
    LinearMap.congr_fun (middleInnerProjection_natural C ε hε hε1 hC hR a ha ha1 (n + 1))
      ((middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)).symm w)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, hw] using
    hm

private theorem
    CuspCentralHomology.middleLeftHomologyMap_apply (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (z : SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) (n + 1)) :
    SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) (n + 1) z =
      (0, -SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) (n + 1) z) := by
  calc
    SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) (n + 1) z =
        (SingularMayerVietoris.singularHomologyMap (overlapIntoOuter C ε hε a) (n + 1) z,
          -SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) (n + 1) z) :=
      SingularMayerVietoris.leftHomologyMap_apply (outerRegion C ε hε a) (innerRegion C ε hε)
        (n + 1) z
    _ = _ := by
      rw [overlapIntoOuter_homology_eq_zero C ε hε hε1 hC hR a ha ha1 n, LinearMap.zero_apply]

private theorem
    CuspCentralHomology.middleLeftHomology_mem_ker_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ)
    (z : SingularMayerVietoris.SingularHomology (overlapRegion C ε hε a) (n + 1)) :
    z ∈
        LinearMap.ker
          (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε)
            (n + 1)) ↔
      SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1) (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1) z) =
        0 := by
  change
    SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) (n + 1) z =
        0 ↔
      _
  rw [middleLeftHomologyMap_apply C ε hε hε1 hC hR a ha ha1 n z]
  constructor
  · intro hz
    have hi :
      -SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) (n + 1) z = 0 :=
      congrArg Prod.snd hz
    exact
      (middleInnerProjection_zero_iff C ε hε hε1 hC hR a ha ha1 (n + 1) z).mp (neg_eq_zero.mp hi)
  · intro hz
    rw [(middleInnerProjection_zero_iff C ε hε hε1 hC hR a ha ha1 (n + 1) z).mpr hz, neg_zero]
    rfl

private def CuspCentralHomology.middleLeftKernelToProjectionEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε)
          (n + 1)) ≃ₗ[ℤ]
      LinearMap.ker
        (SingularMayerVietoris.singularHomologyMap
          (ContinuousMap.fst :
            C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
          (n + 1)) :=
  ({    toFun
          z :=
          ⟨middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1) z.1,
            (middleLeftHomology_mem_ker_iff C ε hε hε1 hC hR a ha ha1 n z.1).mp z.2⟩
        invFun
          z :=
          ⟨(middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)).symm z.1,
            (middleLeftHomology_mem_ker_iff C ε hε hε1 hC hR a ha ha1 n _).mpr
              (by
                rw [LinearEquiv.apply_symm_apply]
                exact z.2)⟩
        left_inv z := Subtype.ext (LinearEquiv.symm_apply_apply _ z.1)
        right_inv z := Subtype.ext (LinearEquiv.apply_symm_apply _ z.1)
        map_add' z
          w := by
          apply Subtype.ext
          exact map_add (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)) z.1 w.1 } :
      LinearMap.ker
          (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε)
            (n + 1)) ≃+
        LinearMap.ker
          (SingularMayerVietoris.singularHomologyMap
            (ContinuousMap.fst :
              C(ToricSpace.CompactFibreTorus × Circle, ToricSpace.CompactFibreTorus))
            (n + 1))).toIntLinearEquiv

private def CuspCentralHomology.middleLeftKernelEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (n : ℕ) :
    LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε)
          (n + 1)) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology ToricSpace.CompactFibreTorus n :=
  ((middleLeftKernelToProjectionEquiv C ε hε hε1 hC hR a ha ha1 n).toAddEquiv.trans
      (rightCircleProjectionKernelEquiv ToricSpace.CompactFibreTorus
          n).toAddEquiv).toIntLinearEquiv

private theorem
    CuspCentralHomology.coverConnecting_injective_of_vanishing {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))] :
    Function.Injective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← SingularMayerVietoris.exact_at_ambient U V hU hV hcover n]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  rw [ha, map_zero, LinearMap.zero_apply]

private theorem CuspCentralHomology.coverConnecting_surjective_of_vanishing {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) [Subsingleton (SingularMayerVietoris.SingularHomology U n)]
    [Subsingleton (SingularMayerVietoris.SingularHomology V n)] :
    Function.Surjective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
  intro a
  have ha : a ∈ LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V n) := by
    exact Subsingleton.elim _ _
  rw [← SingularMayerVietoris.exact_at_intersection U V hU hV hcover n] at ha
  exact ha

private def CuspCentralHomology.coverConnectingEquivOfVanishing {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology U n)]
    [Subsingleton (SingularMayerVietoris.SingularHomology V n)] :
    SingularMayerVietoris.SingularHomology X (n + 1) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (U ∩ V : Set X) n :=
  LinearEquiv.ofBijective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n)
    ⟨coverConnecting_injective_of_vanishing U V hU hV hcover n,
      coverConnecting_surjective_of_vanishing U V hU hV hcover n⟩

public
theorem CuspCentralHomology.coverHomology_subsingleton_of_vanishing {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology (U ∩ V : Set X) n)] :
    Subsingleton (SingularMayerVietoris.SingularHomology X (n + 1)) :=
  (coverConnecting_injective_of_vanishing U V hU hV hcover n).subsingleton

private def
    CuspCentralHomology.coverConnectingToKernel {X : Type} [TopologicalSpace X] (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    SingularMayerVietoris.SingularHomology X (n + 1) →ₗ[ℤ]
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V n) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    ((SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n).codRestrict
        (LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V n))
        (by
          intro a
          rw [← SingularMayerVietoris.exact_at_intersection U V hU hV hcover n]
          exact ⟨a, rfl⟩)).toAddMonoidHom

private theorem
    CuspCentralHomology.coverConnectingToKernel_surjective {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    Function.Surjective (coverConnectingToKernel U V hU hV hcover n) := by
  intro a
  have ha :
    (a : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) n) ∈
      LinearMap.range (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) :=
    (SingularMayerVietoris.exact_at_intersection U V hU hV hcover n).symm.le a.property
  obtain ⟨b, hb⟩ := ha
  exact ⟨b, Subtype.ext hb⟩

@[simp]
private theorem
    CuspCentralHomology.coverConnectingToKernel_eq_zero_iff {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology X (n + 1)) :
    coverConnectingToKernel U V hU hV hcover n a = 0 ↔
      SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n a = 0 := by
  constructor
  · exact fun ha => congrArg Subtype.val ha
  · exact fun ha => Subtype.ext ha

private theorem CuspCentralHomology.coverConnectingToKernel_ker {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.ker (coverConnectingToKernel U V hU hV hcover n) =
      LinearMap.ker (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
  ext a
  exact coverConnectingToKernel_eq_zero_iff U V hU hV hcover n a

private theorem CuspCentralHomology.coverConnectingToKernel_exact {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    LinearMap.range (SingularMayerVietoris.rightHomologyMap U V (n + 1)) =
      LinearMap.ker (coverConnectingToKernel U V hU hV hcover n) := by
  rw [coverConnectingToKernel_ker]
  exact SingularMayerVietoris.exact_at_ambient U V hU hV hcover n

private theorem CuspCentralHomology.coverConnectingToKernel_injective_of_vanishing {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (n : ℕ) [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))] :
    Function.Injective (coverConnectingToKernel U V hU hV hcover n) := by
  intro a b hab
  apply coverConnecting_injective_of_vanishing U V hU hV hcover n
  exact congrArg Subtype.val hab

private def
    CuspCentralHomology.coverConnectingKernelEquivOfVanishing {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    [Subsingleton (SingularMayerVietoris.SingularHomology U (n + 1))]
    [Subsingleton (SingularMayerVietoris.SingularHomology V (n + 1))] :
    SingularMayerVietoris.SingularHomology X (n + 1) ≃ₗ[ℤ]
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V n) :=
  LinearEquiv.ofBijective (coverConnectingToKernel U V hU hV hcover n)
    ⟨coverConnectingToKernel_injective_of_vanishing U V hU hV hcover n,
      coverConnectingToKernel_surjective U V hU hV hcover n⟩

private def CuspCentralHomology.integerExtensionLift {B : Type*} [AddCommGroup B] [Module ℤ B]
    (d : B →ₗ[ℤ] ℤ) (hd : Function.Surjective d) : B :=
  Classical.choose (hd 1)

@[simp]
private theorem
    CuspCentralHomology.integerExtensionLift_spec {B : Type*} [AddCommGroup B] [Module ℤ B]
    (d : B →ₗ[ℤ] ℤ) (hd : Function.Surjective d) : d (integerExtensionLift d hd) = 1 :=
  Classical.choose_spec (hd 1)

private def
    CuspCentralHomology.integerExtensionAssembly {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (b : B) : (A × ℤ) →ₗ[ℤ] B :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun az := i az.1 + az.2 • b
      map_zero' := by simp only [Prod.fst_zero, Prod.snd_zero, map_zero, zero_smul, add_zero]
      map_add' az
        aw := by
        change i (az.1 + aw.1) + (az.2 + aw.2) • b = (i az.1 + az.2 • b) + (i aw.1 + aw.2 • b)
        rw [map_add, add_zsmul]
        exact add_add_add_comm _ _ _ _ }

@[simp]
private theorem CuspCentralHomology.integerExtensionAssembly_apply {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (b : B) (az : A × ℤ) :
    integerExtensionAssembly i b az = i az.1 + az.2 • b :=
  rfl

private theorem
    CuspCentralHomology.integerExtension_boundary_inclusion {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (a : A) : d (i a) = 0 := by
  have ha : i a ∈ LinearMap.range i := ⟨a, rfl⟩
  rw [hexact] at ha
  exact ha

private theorem CuspCentralHomology.integerExtensionAssembly_boundary {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (b : B) (hb : d b = 1) (az : A × ℤ) :
    d (integerExtensionAssembly i b az) = az.2 := by
  rw [integerExtensionAssembly_apply, map_add, map_zsmul,
    integerExtension_boundary_inclusion i d hexact, hb, zero_add]
  simp

private theorem
    CuspCentralHomology.integerExtensionAssembly_injective {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker d) (b : B)
    (hb : d b = 1) : Function.Injective (integerExtensionAssembly i b) := by
  intro az aw h
  have hsnd : az.2 = aw.2 := by
    have hd := congrArg d h
    simpa only [integerExtensionAssembly_boundary i d hexact b hb] using hd
  apply Prod.ext _ hsnd
  apply hi
  apply add_right_cancel (b := aw.2 • b)
  simpa only [integerExtensionAssembly_apply, hsnd] using h

private theorem
    CuspCentralHomology.integerExtensionAssembly_surjective {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hexact : LinearMap.range i = LinearMap.ker d) (b : B) (hb : d b = 1) :
    Function.Surjective (integerExtensionAssembly i b) := by
  intro y
  have hk : y - d y • b ∈ LinearMap.ker d := by
    change d (y - d y • b) = 0
    rw [map_sub, map_zsmul, hb]
    simp
  rw [← hexact] at hk
  obtain ⟨a, ha⟩ := hk
  refine ⟨(a, d y), ?_⟩
  change i a + d y • b = y
  rw [ha, sub_add_cancel]

private def
    CuspCentralHomology.splitIntegerExtensionEquiv {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ) (hi : Function.Injective i)
    (hd : Function.Surjective d) (hexact : LinearMap.range i = LinearMap.ker d) :
    B ≃ₗ[ℤ] (A × ℤ) :=
  (LinearEquiv.ofBijective (integerExtensionAssembly i (integerExtensionLift d hd))
      ⟨integerExtensionAssembly_injective i d hi hexact (integerExtensionLift d hd)
          (integerExtensionLift_spec d hd),
        integerExtensionAssembly_surjective i d hexact (integerExtensionLift d hd)
          (integerExtensionLift_spec d hd)⟩).symm

@[simp]
private theorem
    CuspCentralHomology.splitIntegerExtensionEquiv_symm_apply {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (az : A × ℤ) :
    (splitIntegerExtensionEquiv i d hi hd hexact).symm az =
      i az.1 + az.2 • integerExtensionLift d hd :=
  rfl

@[simp]
private theorem CuspCentralHomology.splitIntegerExtensionEquiv_snd {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module ℤ A] [Module ℤ B] (i : A →ₗ[ℤ] B) (d : B →ₗ[ℤ] ℤ)
    (hi : Function.Injective i) (hd : Function.Surjective d)
    (hexact : LinearMap.range i = LinearMap.ker d) (b : B) :
    (splitIntegerExtensionEquiv i d hi hd hexact b).2 = d b := by
  have h :=
    integerExtensionAssembly_boundary i d hexact (integerExtensionLift d hd)
      (integerExtensionLift_spec d hd) (splitIntegerExtensionEquiv i d hi hd hexact b)
  change
    d
        ((splitIntegerExtensionEquiv i d hi hd hexact).symm
          (splitIntegerExtensionEquiv i d hi hd hexact b)) =
      _ at h
  rw [LinearEquiv.symm_apply_apply] at h
  exact h.symm

private def CuspCentralHomology.signedRightMap {C E : Type*} [AddCommGroup C] [AddCommGroup E]
    [Module ℤ C] [Module ℤ E] (A : Type*) [AddCommGroup A] (p : E →ₗ[ℤ] C) :
    E →ₗ[ℤ] (A × C) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun e := (0, -p e)
      map_zero' := by simp only [map_zero, neg_zero, Prod.mk_zero_zero]
      map_add' e
        f := by
        apply Prod.ext
        · exact (add_zero 0).symm
        · exact (congrArg Neg.neg (p.map_add e f)).trans (neg_add (p e) (p f)) }

@[simp]
private theorem
    CuspCentralHomology.signedRightMap_apply {A C E : Type*} [AddCommGroup A] [AddCommGroup C]
    [AddCommGroup E] [Module ℤ C] [Module ℤ E] (p : E →ₗ[ℤ] C) (e : E) :
    signedRightMap A p e = (0, -p e) :=
  rfl

private def CuspCentralHomology.firstSummandMap {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module ℤ A] [Module ℤ B] (r : (A × C) →ₗ[ℤ] B) : A →ₗ[ℤ] B :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    { toFun a := r (a, 0)
      map_zero' := r.map_zero
      map_add' a b := by simpa only [Prod.mk_add_mk, add_zero] using r.map_add (a, 0) (b, 0) }

@[simp]
private theorem CuspCentralHomology.firstSummandMap_apply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] (r : (A × C) →ₗ[ℤ] B) (a : A) :
    firstSummandMap r a = r (a, 0) :=
  rfl

private theorem CuspCentralHomology.firstSummandMap_injective {A B C E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    [Module ℤ E] (p : E →ₗ[ℤ] C) (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) :
    Function.Injective (firstSummandMap r) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro a ha
  have hmem : (a, 0) ∈ LinearMap.ker r := ha
  rw [hker] at hmem
  obtain ⟨e, he⟩ := hmem
  change a = 0
  exact (congrArg Prod.fst he).symm

private theorem CuspCentralHomology.secondSummand_eq_zero {A B C E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ B] [Module ℤ C]
    [Module ℤ E] (p : E →ₗ[ℤ] C) (hp : Function.Surjective p) (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) (c : C) : r (0, c) = 0 := by
  have hmem : (0, c) ∈ LinearMap.range (signedRightMap A p) := by
    obtain ⟨e, he⟩ := hp (-c)
    refine ⟨e, ?_⟩
    simp only [signedRightMap_apply, he, neg_neg]
  rw [← hker] at hmem
  exact hmem

private theorem CuspCentralHomology.firstSummandMap_apply_fst {A B C E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    [Module ℤ E] (p : E →ₗ[ℤ] C) (hp : Function.Surjective p) (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) (ac : A × C) :
    firstSummandMap r ac.1 = r ac := by
  have h := r.map_add (ac.1, 0) (0, ac.2)
  simpa only [firstSummandMap_apply, Prod.mk_add_mk, add_zero, zero_add,
    secondSummand_eq_zero p hp r hker] using h.symm

private theorem CuspCentralHomology.firstSummandMap_range {A B C E : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    [Module ℤ E] (p : E →ₗ[ℤ] C) (hp : Function.Surjective p) (r : (A × C) →ₗ[ℤ] B)
    (hker : LinearMap.ker r = LinearMap.range (signedRightMap A p)) :
    LinearMap.range (firstSummandMap r) = LinearMap.range r := by
  ext b
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(a, 0), ha⟩
  · rintro ⟨ac, hac⟩
    exact ⟨ac.1, (firstSummandMap_apply_fst p hp r hker ac).trans hac⟩

private theorem CuspCentralHomology.eq_signedRightMap_of_apply {A C E : Type*} [AddCommGroup A]
    [AddCommGroup C] [AddCommGroup E] [Module ℤ C] [Module ℤ E]
    (left : E →ₗ[ℤ] (A × C)) (p : E →ₗ[ℤ] C) (hl : ∀ e, left e = (0, -p e)) :
    left = signedRightMap A p := by
  apply LinearMap.ext
  intro e
  exact hl e

private theorem CuspCentralHomology.firstSummandMap_injective_of_signed_formula {A B C E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ E] (left : E →ₗ[ℤ] (A × C)) (p : E →ₗ[ℤ] C) (r : (A × C) →ₗ[ℤ] B)
    (hl : ∀ e, left e = (0, -p e)) (hexact : LinearMap.range left = LinearMap.ker r) :
    Function.Injective (firstSummandMap r) := by
  apply firstSummandMap_injective p r
  rw [← eq_signedRightMap_of_apply left p hl]
  exact hexact.symm

private theorem CuspCentralHomology.firstSummandMap_range_of_signed_formula {A B C E : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup E] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ E] (left : E →ₗ[ℤ] (A × C)) (p : E →ₗ[ℤ] C)
    (hp : Function.Surjective p) (r : (A × C) →ₗ[ℤ] B) (hl : ∀ e, left e = (0, -p e))
    (hexact : LinearMap.range left = LinearMap.ker r) :
    LinearMap.range (firstSummandMap r) = LinearMap.range r := by
  apply firstSummandMap_range p hp r
  rw [← eq_signedRightMap_of_apply left p hl]
  exact hexact.symm

private def
    CuspCentralHomology.middleConnectingKernelEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    LinearMap.ker
        (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε)
          1) ≃ₗ[ℤ]
      ℤ :=
  (middleLeftKernelEquiv C ε hε hε1 hC hR a ha ha1 0).trans
    ((compactFibreTorusHomologyEquiv 0).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ))

private def
    CuspCentralHomology.middleQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 2 →ₗ[ℤ] ℤ :=
  (middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1).toLinearMap.comp
    (coverConnectingToKernel (outerRegion C ε hε a) (innerRegion C ε hε)
      (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε a ha1) 1)

private theorem CuspCentralHomology.middleQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Function.Surjective (middleQuotientMap C ε hε hε1 hC hR a ha ha1) :=
  (middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1).surjective.comp
    (coverConnectingToKernel_surjective (outerRegion C ε hε a) (innerRegion C ε hε)
      (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε a ha1) 1)

private theorem CuspCentralHomology.middleQuotientMap_ker (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    LinearMap.ker (middleQuotientMap C ε hε hε1 hC hR a ha ha1) =
      LinearMap.ker
        (coverConnectingToKernel (outerRegion C ε hε a) (innerRegion C ε hε)
          (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
          (outerRegion_union_innerRegion C ε hε a ha1) 1) := by
  ext x
  change
    middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1
          (coverConnectingToKernel (outerRegion C ε hε a) (innerRegion C ε hε) _ _ _ 1 x) =
        0 ↔
      _
  constructor
  · intro hx
    apply (middleConnectingKernelEquiv C ε hε hε1 hC hR a ha ha1).injective
    simpa only [map_zero] using hx
  · intro hx
    change coverConnectingToKernel (outerRegion C ε hε a) (innerRegion C ε hε) _ _ _ 1 x = 0 at hx
    rw [hx, map_zero]

private theorem CuspCentralHomology.middleOuterInclusion_eq_firstSummand
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (a : ℝ) :
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2 =
      firstSummandMap
        (SingularMayerVietoris.rightHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2) := by
  apply LinearMap.ext
  intro x
  change
    SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2 x =
      SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2 x +
        SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (innerRegion C ε hε)) 2 0
  rw [map_zero, add_zero]

private theorem
    CuspCentralHomology.middleOuterInclusion_injective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    Function.Injective
      (SingularMayerVietoris.singularHomologyMap
        (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2) := by
  rw [middleOuterInclusion_eq_firstSummand C ε hε a]
  exact
    firstSummandMap_injective_of_signed_formula
      (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2)
      (SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) 2)
      (SingularMayerVietoris.rightHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2)
      (middleLeftHomologyMap_apply C ε hε hε1 hC hR a ha ha1 1)
      (SingularMayerVietoris.exact_at_pair (outerRegion C ε hε a) (innerRegion C ε hε)
        (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
        (outerRegion_union_innerRegion C ε hε a ha1) 2)

private theorem
    CuspCentralHomology.middleOuterInclusion_range (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2) =
      LinearMap.range
        (SingularMayerVietoris.rightHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2) := by
  rw [middleOuterInclusion_eq_firstSummand C ε hε a]
  exact
    firstSummandMap_range_of_signed_formula
      (SingularMayerVietoris.leftHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2)
      (SingularMayerVietoris.singularHomologyMap (overlapIntoInner C ε hε a) 2)
      (overlapIntoInner_homology_surjective C ε hε hε1 hC hR a ha ha1 1)
      (SingularMayerVietoris.rightHomologyMap (outerRegion C ε hε a) (innerRegion C ε hε) 2)
      (middleLeftHomologyMap_apply C ε hε hε1 hC hR a ha ha1 1)
      (SingularMayerVietoris.exact_at_pair (outerRegion C ε hε a) (innerRegion C ε hε)
        (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
        (outerRegion_union_innerRegion C ε hε a ha1) 2)

private theorem
    CuspCentralHomology.middleSecondHomology_exact (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    LinearMap.range
        (SingularMayerVietoris.singularHomologyMap
          (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2) =
      LinearMap.ker (middleQuotientMap C ε hε hε1 hC hR a ha ha1) := by
  rw [middleOuterInclusion_range C ε hε hε1 hC hR a ha ha1, middleQuotientMap_ker]
  exact
    coverConnectingToKernel_exact (outerRegion C ε hε a) (innerRegion C ε hε)
      (outerRegion_isOpen C ε hε hε1 hC hR a) (innerRegion_isOpen C ε hε hε1 hC hR)
      (outerRegion_union_innerRegion C ε hε a ha1) 1

private def CuspCentralHomology.middleSecondHomologySplit (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 2 ≃ₗ[ℤ]
      (SingularMayerVietoris.SingularHomology (outerRegion C ε hε a) 2 × ℤ) :=
  splitIntegerExtensionEquiv
    (SingularMayerVietoris.singularHomologyMap
      (SingularMayerVietoris.subtypeInclusion (outerRegion C ε hε a)) 2)
    (middleQuotientMap C ε hε hε1 hC hR a ha ha1)
    (middleOuterInclusion_injective C ε hε hε1 hC hR a ha ha1)
    (middleQuotientMap_surjective C ε hε hε1 hC hR a ha ha1)
    (middleSecondHomology_exact C ε hε hε1 hC hR a ha ha1)

private def CuspCentralHomology.middleIntegerFourEquiv : ((Fin 3 → ℤ) × ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ({    toFun p := ![p.1 0, p.1 1, p.1 2, p.2]
        invFun v := (![v 0, v 1, v 2], v 3)
        left_inv
          p := by
          apply Prod.ext
          · funext i
            fin_cases i <;> rfl
          · rfl
        right_inv
          v := by
          funext i
          fin_cases i <;> rfl
        map_add' p
          q := by
          funext i
          fin_cases i <;> rfl } :
      ((Fin 3 → ℤ) × ℤ) ≃+ (Fin 4 → ℤ)).toIntLinearEquiv

private def
    CuspCentralHomology.middleOuterHomologyTwoEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    SingularMayerVietoris.SingularHomology (outerRegion C ε hε a) 2 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (PeriodTorusHigherHomology.homotopyEquivHomologyEquiv
        (outerRegionSuspensionHomotopyEquiv C ε hε hε1 hC hR a ha ha1) 2).trans
    threeCircleSuspensionHomologyTwoEquiv

private def
    CuspCentralHomology.centralSingularH3Equiv_of_admissible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 3 ≃ₗ[ℤ]
      (Fin 2 → ℤ) := by
  letI := outerRegion_homology_subsingleton C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) 0
  letI := innerRegion_homology_subsingleton C ε hε hε1 hC hR 0
  exact
    ((coverConnectingKernelEquivOfVanishing (outerRegion C ε hε (1 / 2)) (innerRegion C ε hε)
              (outerRegion_isOpen C ε hε hε1 hC hR (1 / 2)) (innerRegion_isOpen C ε hε hε1 hC hR)
              (outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)) 2).trans
          (middleLeftKernelEquiv C ε hε hε1 hC hR (1 / 2) (by norm_num) (by norm_num) 1)).trans
      (compactFibreTorusHomologyEquiv 1)

private def
    CuspCentralHomology.centralSingularH2Equiv_of_admissible (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    SingularMayerVietoris.SingularHomology (CuspRetraction.QuotientCentralFibre C ε) 2 ≃ₗ[ℤ]
      (Fin 4 → ℤ) :=
  (((middleSecondHomologySplit C ε hε hε1 hC hR (1 / 2) (by norm_num)
              (by norm_num)).toAddEquiv.trans
          (AddEquiv.prodCongr
            (middleOuterHomologyTwoEquiv C ε hε hε1 hC hR (1 / 2) (by norm_num)
                (by norm_num)).toAddEquiv
            (AddEquiv.refl ℤ))).trans
      middleIntegerFourEquiv.toAddEquiv).toIntLinearEquiv

private def CuspControlledRetraction.normalizedPosition (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (x : ToricSpace.Space) : (Fin 2 → ℝ) :=
  ToricSpace.realCuspVector
    (ToricSpace.inverseDisplacement (CuspPositive.positiveTwist C₀) (ToricSpace.time x)
      (ToricSpace.position x))

private theorem CuspControlledRetraction.inverseDisplacement_positiveTwist_norm
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (t : ℂ) :
    ToricSpace.inverseDisplacement (CuspPositive.positiveTwist C₀) (‖t‖ : ℂ) =
      ToricSpace.inverseDisplacement (CuspPositive.positiveTwist C₀) t := by
  unfold ToricSpace.inverseDisplacement
  congr 1
  simp only [ToricSpace.displacementMatrix, CuspPositive.driftMatrix_positiveTwist,
    Complex.norm_of_nonneg (norm_nonneg t)]

private theorem CuspControlledRetraction.realCuspVector_continuous :
    Continuous ToricSpace.realCuspVector := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_apply 1
  · exact (continuous_apply 0).neg

private theorem
    CuspControlledRetraction.normalizedPosition_continuousAt (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    {ε : ℝ} (hε1 : ε < 1) (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε)
    {x : ToricSpace.Space} (hx : ToricSpace.time x ≠ 0) (ht : ‖ToricSpace.time x‖ < ε) :
    ContinuousAt (normalizedPosition C₀) x := by
  have htpos : 0 < ‖ToricSpace.time x‖ := norm_pos_iff.mpr hx
  have hlog : Real.log ‖ToricSpace.time x‖ < 0 := Real.log_neg htpos (ht.trans hε1)
  have hinv :=
    ToricSpace.inverseDisplacement_continuousAt (CuspPositive.positiveTwist C₀)
      (fun _ _ => continuousAt_const) hlog (hR _ htpos ht) (ToricSpace.position x)
  have hp :
    ContinuousAt (fun y : ToricSpace.Space => (ToricSpace.time y, ToricSpace.position y)) x :=
    ToricSpace.time_holomorphic.continuous.continuousAt.prodMk
      (ToricSpace.position_continuousAt hx hlog.ne)
  exact
    realCuspVector_continuous.continuousAt.comp
      (ContinuousAt.comp (f := fun y : ToricSpace.Space =>
        (ToricSpace.time y, ToricSpace.position y)) (g := fun p : ℂ × (Fin 2 → ℝ) =>
        ToricSpace.inverseDisplacement (CuspPositive.positiveTwist C₀) p.1 p.2) hinv hp)

private theorem CuspControlledRetraction.normalizedPosition_twistedTranslate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (v : Fin 2 → ℤ)
    {x : ToricSpace.Space} (hx : ToricSpace.time x ≠ 0) (ht : ‖ToricSpace.time x‖ < ε) :
    normalizedPosition C₀ (ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v x) =
      normalizedPosition C₀ x + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) := by
  have htpos : 0 < ‖ToricSpace.time x‖ := norm_pos_iff.mpr hx
  have hlog : Real.log ‖ToricSpace.time x‖ < 0 := Real.log_neg htpos (ht.trans hε1)
  unfold normalizedPosition
  rw [ToricSpace.time_twistedTranslate,
    ToricSpace.position_twistedTranslate_displacement (CuspPositive.positiveTwist C₀) v
      ((ToricSpace.mem_openTorus_iff x).mpr hx) hlog.ne,
    ToricSpace.inverseDisplacement_add,
    ToricSpace.inverseDisplacement_displacement (CuspPositive.positiveTwist C₀) hlog
      (hR _ htpos ht),
    map_add, ToricSpace.realCuspVector_latticeReal]
  rfl

private theorem CuspControlledRetraction.normalizedPosition_closedPositive_continuousAt
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε)
    {q : ToricSpace.ClosedPositiveTube η} (hq : ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0) :
    ContinuousAt
      (fun r : ToricSpace.ClosedPositiveTube η => normalizedPosition C₀ (r.1 : ToricSpace.Space))
      q :=
  ContinuousAt.comp (f := fun r : ToricSpace.ClosedPositiveTube η => (r.1 : ToricSpace.Space))
    (g := normalizedPosition C₀) (normalizedPosition_continuousAt C₀ hε1 hR hq (q.2.trans_lt hηε))
    (continuous_subtype_val.comp continuous_subtype_val).continuousAt

private theorem CuspControlledRetraction.normalizedPosition_closedPositive_continuousOn
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) :
    ContinuousOn
      (fun q : ToricSpace.ClosedPositiveTube η => normalizedPosition C₀ (q.1 : ToricSpace.Space))
      {q | ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0} := by
  intro q hq
  exact (normalizedPosition_closedPositive_continuousAt C₀ hε1 hR hηε hq).continuousWithinAt

private theorem CuspControlledRetraction.normalizedPosition_closedPositive_twistedTranslate
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε η : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (v : Fin 2 → ℤ)
    {q : ToricSpace.ClosedPositiveTube η} (hq : ToricSpace.time (q.1 : ToricSpace.Space) ≠ 0) :
    normalizedPosition C₀ ((CuspPositive.closedPositiveTranslate C₀ η v q).1 : ToricSpace.Space) =
      normalizedPosition C₀ (q.1 : ToricSpace.Space) +
        CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) :=
  normalizedPosition_twistedTranslate C₀ hε1 hR v hq (q.2.trans_lt hηε)

private noncomputable def CuspControlledRetraction.Interpolation.tentWeight (ρ r : ℝ) : ℝ :=
  Max.max 0 (1 - |r - ρ| / (ρ / 2))

private theorem CuspControlledRetraction.Interpolation.tentWeight_continuous (ρ : ℝ) :
    Continuous (tentWeight ρ) :=
  continuous_const.max
    (continuous_const.sub ((continuous_id.sub continuous_const).abs.div_const (ρ / 2)))

private theorem
    CuspControlledRetraction.Interpolation.tentWeight_self (ρ : ℝ) : tentWeight ρ ρ = 1 := by
  simp [tentWeight]

private theorem CuspControlledRetraction.Interpolation.tentWeight_eq_zero_of_half_le_abs {ρ : ℝ}
    (hρ : 0 < ρ) (r : ℝ) (hr : ρ / 2 ≤ |r - ρ|) : tentWeight ρ r = 0 := by
  apply max_eq_left
  have hdiv : 1 ≤ |r - ρ| / (ρ / 2) :=
    (le_div_iff₀ (half_pos hρ)).mpr (by simpa only [one_mul] using hr)
  linarith

private theorem
    CuspControlledRetraction.Interpolation.tentWeight_eq_zero_of_le_half {ρ : ℝ} (hρ : 0 < ρ)
    (r : ℝ) (hr : r ≤ ρ / 2) : tentWeight ρ r = 0 := by
  apply tentWeight_eq_zero_of_half_le_abs hρ r
  linarith [neg_le_abs (r - ρ)]

private noncomputable def CuspControlledRetraction.Interpolation.interpolate {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E)
    (p : unitInterval × X) : E :=
  a p.2 + ((p.1 : ℝ) * tentWeight ρ (h p.2)) • (b p.2 - a p.2)

private theorem CuspControlledRetraction.Interpolation.interpolate_zero {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E) (x : X) :
    interpolate ρ h a b (0, x) = a x := by simp [interpolate]

private theorem
    CuspControlledRetraction.Interpolation.interpolate_eq_left_of_height_le_half {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E) (hρ : 0 < ρ)
    (s : unitInterval) (x : X) (hx : h x ≤ ρ / 2) : interpolate ρ h a b (s, x) = a x := by
  simp only [interpolate, tentWeight_eq_zero_of_le_half hρ (h x) hx, MulZeroClass.mul_zero,
    zero_smul, add_zero]

private theorem
    CuspControlledRetraction.Interpolation.interpolate_fixed_of_height_zero {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E) (hρ : 0 < ρ)
    (s : unitInterval) (x : X) (hx : h x = 0) : interpolate ρ h a b (s, x) = a x :=
  interpolate_eq_left_of_height_le_half ρ h a b hρ s x (by rw [hx]; exact (half_pos hρ).le)

private theorem CuspControlledRetraction.Interpolation.interpolate_one_of_height_eq {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E) (x : X)
    (hx : h x = ρ) : interpolate ρ h a b (1, x) = b x := by
  simp [interpolate, hx, tentWeight_self]

private theorem CuspControlledRetraction.Interpolation.interpolate_translate {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : ℝ) (h : X → ℝ) (a b : X → E) (hρ : 0 < ρ)
    (T : X → X) (d : E) (hT : ∀ x, h (T x) = h x) (ha : ∀ x, a (T x) = a x + d)
    (hb : ∀ x, h x ≠ 0 → b (T x) = b x + d) (s : unitInterval) (x : X) :
    interpolate ρ h a b (s, T x) = interpolate ρ h a b (s, x) + d := by
  by_cases hx : h x = 0
  · rw [interpolate_fixed_of_height_zero ρ h a b hρ s (T x) ((hT x).trans hx),
      interpolate_fixed_of_height_zero ρ h a b hρ s x hx, ha x]
  · simp only [interpolate, hT x, ha x, hb x hx, add_sub_add_right_eq_sub]
    exact add_right_comm _ _ _

private theorem CuspControlledRetraction.Interpolation.interpolate_continuous {X E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X] (ρ : ℝ) (h : X → ℝ)
    (a b : X → E) (hρ : 0 < ρ) (hh : Continuous h) (ha : Continuous a)
    (hb : ContinuousOn b {x : X | h x ≠ 0}) : Continuous (interpolate ρ h a b) := by
  have hw : Continuous (fun p : unitInterval × X => (p.1 : ℝ) * tentWeight ρ (h p.2)) :=
    (continuous_subtype_val.comp continuous_fst).mul
      ((tentWeight_continuous ρ).comp (hh.comp continuous_snd))
  have hu : ContinuousOn (interpolate ρ h a b) {p : unitInterval × X | h p.2 ≠ 0} :=
    (ha.comp continuous_snd).continuousOn.add
      (hw.continuousOn.smul
        ((hb.comp continuous_snd.continuousOn (fun _ hp => hp)).sub
          (ha.comp continuous_snd).continuousOn))
  have hv : ContinuousOn (interpolate ρ h a b) {p : unitInterval × X | h p.2 < ρ / 2} :=
    (ha.comp continuous_snd).continuousOn.congr fun p hp =>
      interpolate_eq_left_of_height_le_half ρ h a b hρ p.1 p.2 hp.le
  have hcover :
    {p : unitInterval × X | h p.2 ≠ 0} ∪ {p : unitInterval × X | h p.2 < ρ / 2} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    by_cases hp : h p.2 = 0
    · right
      change h p.2 < ρ / 2
      rw [hp]
      exact half_pos hρ
    · exact Or.inl hp
  rw [← continuousOn_univ, ← hcover]
  exact
    hu.union_of_isOpen hv (isOpen_ne_fun (hh.comp continuous_snd) continuous_const)
      (isOpen_Iio.preimage (hh.comp continuous_snd))

private def
    CuspControlledRetraction.positiveHeight {η : ℝ} (q : ToricSpace.ClosedPositiveTube η) : ℝ :=
  ‖ToricSpace.time (q.1 : ToricSpace.Space)‖

private theorem CuspControlledRetraction.positiveHeight_continuous {η : ℝ} :
    Continuous (positiveHeight : ToricSpace.ClosedPositiveTube η → ℝ) :=
  (ToricSpace.time_holomorphic.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)).norm

private theorem
    CuspControlledRetraction.positiveHeight_translate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η) :
    positiveHeight (CuspPositive.closedPositiveTranslate C₀ η v q) = positiveHeight q := by
  change
    ‖ToricSpace.time
          (ToricSpace.twistedTranslate (CuspPositive.positiveTwist C₀) v
            (q.1 : ToricSpace.Space))‖ =
      _
  rw [ToricSpace.time_twistedTranslate]
  rfl

private def CuspControlledRetraction.positiveEndpoint {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0) :
    C(ToricSpace.ClosedPositiveTube η, CuspPositiveRetraction.PositiveCentralFibre)
    where
  toFun q := ⟨(P (1, q)).1, hone q⟩
  continuous_toFun :=
    (continuous_subtype_val.comp
          (P.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk
      _

private def CuspControlledRetraction.endpointPosition {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) :
    C(ToricSpace.ClosedPositiveTube η, CuspHoneycombTiling.Plane)
    where
  toFun q := (CuspHoneycomb.honeycombHomeomorph C₀).symm (positiveEndpoint P hone q)
  continuous_toFun :=
    (CuspHoneycomb.honeycombHomeomorph C₀).symm.continuous.comp
      (positiveEndpoint P hone).continuous

private theorem CuspControlledRetraction.positiveEndpoint_equivariant {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (hequiv :
      ∀ s v q,
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η) :
    positiveEndpoint P hone (CuspPositive.closedPositiveTranslate C₀ η v q) =
      CuspCollapse.positiveCentralTranslate C₀ v (positiveEndpoint P hone q) := by
  apply Subtype.ext
  exact congrArg (fun x : ToricSpace.ClosedPositiveTube η => x.1) (hequiv 1 v q)

private theorem CuspControlledRetraction.endpointPosition_equivariant {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ)
    (hequiv :
      ∀ s v q,
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η) :
    endpointPosition P hone C₀ (CuspPositive.closedPositiveTranslate C₀ η v q) =
      endpointPosition P hone C₀ q + CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v) :=
  by
  change
    (CuspHoneycomb.honeycombHomeomorph C₀).symm
        (positiveEndpoint P hone (CuspPositive.closedPositiveTranslate C₀ η v q)) =
      _
  rw [positiveEndpoint_equivariant P hone C₀ hequiv,
    CuspHoneycomb.honeycombHomeomorph_symm_equivariant]
  rfl

private theorem CuspControlledRetraction.normalizedPosition_height_continuousOn_mo1973_13101
    {η : ℝ} (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) :
    ContinuousOn
      (fun q : ToricSpace.ClosedPositiveTube η => normalizedPosition C₀ (q.1 : ToricSpace.Space))
      {q | positiveHeight q ≠ 0} := by
  simpa only [positiveHeight, ne_eq, norm_eq_zero] using
    normalizedPosition_closedPositive_continuousOn C₀ hε1 hR hηε

private def CuspControlledRetraction.centralInterpolation {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) :
    C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η)
    where
  toFun
    p :=
    CuspPositiveRetraction.positiveCentralInclusion η hη
      (CuspHoneycomb.honeycombHomeomorph C₀
        (Interpolation.interpolate ρ positiveHeight (endpointPosition P hone C₀)
          (fun q => normalizedPosition C₀ (q.1 : ToricSpace.Space)) p))
  continuous_toFun :=
    (CuspPositiveRetraction.positiveCentralInclusion η hη).continuous.comp
      ((CuspHoneycomb.honeycombHomeomorph C₀).continuous.comp
        (Interpolation.interpolate_continuous ρ positiveHeight (endpointPosition P hone C₀)
          (fun q => normalizedPosition C₀ (q.1 : ToricSpace.Space)) hρ positiveHeight_continuous
          (endpointPosition P hone C₀).continuous
          (normalizedPosition_height_continuousOn_mo1973_13101 C₀ hε1 hR hηε)))

private theorem CuspControlledRetraction.centralInterpolation_apply {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q) =
      CuspPositiveRetraction.positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀
          (Interpolation.interpolate ρ positiveHeight (endpointPosition P hone C₀)
            (fun r => normalizedPosition C₀ (r.1 : ToricSpace.Space)) (s, q))) :=
  rfl

private theorem CuspControlledRetraction.centralInterpolation_zero {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (q : ToricSpace.ClosedPositiveTube η) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (0, q) = P (1, q) := by
  rw [centralInterpolation_apply, Interpolation.interpolate_zero]
  change
    CuspPositiveRetraction.positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀
          ((CuspHoneycomb.honeycombHomeomorph C₀).symm (positiveEndpoint P hone q))) =
      _
  rw [Homeomorph.apply_symm_apply]
  rfl

private theorem CuspControlledRetraction.centralInterpolation_central {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η) :
    ToricSpace.time
        ((centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)).1 : ToricSpace.Space) =
      0 :=
  (CuspHoneycomb.honeycombHomeomorph C₀
      (Interpolation.interpolate ρ positiveHeight (endpointPosition P hone C₀)
        (fun r => normalizedPosition C₀ (r.1 : ToricSpace.Space)) (s, q))).2

private theorem CuspControlledRetraction.centralInterpolation_eq_endpoint_of_height_le_half {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η)
    (hq : positiveHeight q ≤ ρ / 2) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q) = P (1, q) := by
  rw [centralInterpolation_apply,
    Interpolation.interpolate_eq_left_of_height_le_half _ _ _ _ hρ s q hq]
  change
    CuspPositiveRetraction.positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀
          ((CuspHoneycomb.honeycombHomeomorph C₀).symm (positiveEndpoint P hone q))) =
      _
  rw [Homeomorph.apply_symm_apply]
  rfl

private theorem CuspControlledRetraction.centralInterpolation_fixed {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hfix : ∀ s q, ToricSpace.time (q.1 : ToricSpace.Space) = 0 → P (s, q) = q)
    (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η)
    (hq : ToricSpace.time (q.1 : ToricSpace.Space) = 0) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q) = q := by
  rw [centralInterpolation_eq_endpoint_of_height_le_half P hone C₀ hε1 hR hηε hη ρ hρ s q
      (by simpa only [positiveHeight, hq, norm_zero] using (half_pos hρ).le)]
  exact hfix 1 q hq

private theorem CuspControlledRetraction.centralInterpolation_equivariant {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hequiv :
      ∀ s v q,
        P (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
          CuspPositive.closedPositiveTranslate C₀ η v (P (s, q)))
    (s : unitInterval) (v : Fin 2 → ℤ) (q : ToricSpace.ClosedPositiveTube η) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ
        (s, CuspPositive.closedPositiveTranslate C₀ η v q) =
      CuspPositive.closedPositiveTranslate C₀ η v
        (centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)) := by
  have he :=
    Interpolation.interpolate_translate ρ positiveHeight (endpointPosition P hone C₀)
      (fun q => normalizedPosition C₀ (q.1 : ToricSpace.Space)) hρ
      (CuspPositive.closedPositiveTranslate C₀ η v)
      (CuspHoneycombTiling.latticePoint (ToricSpace.cuspVector v))
      (positiveHeight_translate C₀ η v) (endpointPosition_equivariant P hone C₀ hequiv v)
      (fun q hq =>
        normalizedPosition_closedPositive_twistedTranslate C₀ hε1 hR hηε v
          (norm_ne_zero_iff.mp hq))
      s q
  rw [centralInterpolation_apply, he, CuspHoneycomb.honeycombHomeomorph_equivariant]
  rfl

private theorem CuspControlledRetraction.centralInterpolation_nonincreasing {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (s : unitInterval) (q : ToricSpace.ClosedPositiveTube η) :
    positiveHeight (centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)) ≤
      positiveHeight q := by
  change
    ‖ToricSpace.time
          ((centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)).1 : ToricSpace.Space)‖ ≤
      _
  rw [centralInterpolation_central, norm_zero]
  exact norm_nonneg _

private theorem CuspControlledRetraction.centralInterpolation_one_of_height_eq {η : ℝ}
    (P : C(unitInterval × ToricSpace.ClosedPositiveTube η, ToricSpace.ClosedPositiveTube η))
    (hone :
      ∀ q : ToricSpace.ClosedPositiveTube η,
        ToricSpace.time ((P (1, q)).1 : ToricSpace.Space) = 0)
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) {ε : ℝ} (hε1 : ε < 1)
    (hR : ToricSpace.SmallDrift (CuspPositive.positiveTwist C₀) ε) (hηε : η < ε) (hη : 0 ≤ η)
    (ρ : ℝ) (hρ : 0 < ρ) (q : ToricSpace.ClosedPositiveTube η) (hq : positiveHeight q = ρ) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (1, q) =
      CuspPositiveRetraction.positiveCentralInclusion η hη
        (CuspHoneycomb.honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : ToricSpace.Space))) :=
  by rw [centralInterpolation_apply, Interpolation.interpolate_one_of_height_eq _ _ _ _ q hq]

private def CuspControlledRetraction.Concatenation.slice {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P : C(unitInterval × X, Y)) (s : unitInterval) : C(X, Y) :=
  ⟨fun x => P (s, x), P.continuous.comp (continuous_const.prodMk continuous_id)⟩

private def CuspControlledRetraction.Concatenation.asHomotopy {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (P : C(unitInterval × X, Y)) : (slice P 0).Homotopy (slice P 1)
    where
  toContinuousMap := P
  map_zero_left _ := rfl
  map_one_left _ := rfl

end Mathoverflow1973

end
